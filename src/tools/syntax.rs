// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

// In the informal grammar comments in this file, Comma<T> is shorthand for:
//      (<T> ",")* <T>?
// Note that this allows an optional trailing comma.

use move_command_line_common::files::FileHash;
use move_compiler::{
    diag,
    diagnostics::{Diagnostic, Diagnostics},
    editions::Edition,
    parser::{ast::*, lexer::*},
    shared::*,
    MatchedFileCommentMap,
};
use move_ir_types::location::*;
use move_ir_types::sp;
use move_symbol_pool::Symbol;

struct Context<'env, 'lexer, 'input> {
    env: &'env mut CompilationEnv,
    tokens: &'lexer mut Lexer<'input>,
}

impl<'env, 'lexer, 'input> Context<'env, 'lexer, 'input> {
    fn new(env: &'env mut CompilationEnv, tokens: &'lexer mut Lexer<'input>) -> Self {
        Self { env, tokens }
    }
}

//**************************************************************************************************
// Error Handling
//**************************************************************************************************

fn current_token_error_string(tokens: &Lexer) -> String {
    if tokens.peek() == Tok::EOF {
        "end-of-file".to_string()
    } else {
        format!("'{}'", tokens.content())
    }
}

fn unexpected_token_error(tokens: &Lexer, expected: &str) -> Box<Diagnostic> {
    unexpected_token_error_(tokens, tokens.start_loc(), expected)
}

fn unexpected_token_error_(
    tokens: &Lexer,
    expected_start_loc: usize,
    expected: &str,
) -> Box<Diagnostic> {
    let unexpected_loc = current_token_loc(tokens);
    let unexpected = current_token_error_string(tokens);
    let expected_loc = if expected_start_loc < tokens.start_loc() {
        make_loc(
            tokens.file_hash(),
            expected_start_loc,
            tokens.previous_end_loc(),
        )
    } else {
        unexpected_loc
    };
    Box::new(diag!(
        Syntax::UnexpectedToken,
        (unexpected_loc, format!("Unexpected {}", unexpected)),
        (expected_loc, format!("Expected {}", expected)),
    ))
}

fn add_type_args_ambiguity_label(loc: Loc, mut diag: Box<Diagnostic>) -> Box<Diagnostic> {
    const MSG: &str = "Perhaps you need a blank space before this '<' operator?";
    diag.add_secondary_label((loc, MSG));
    diag
}

//**************************************************************************************************
// Miscellaneous Utilities
//**************************************************************************************************

pub fn make_loc(file_hash: FileHash, start: usize, end: usize) -> Loc {
    Loc::new(file_hash, start as u32, end as u32)
}

fn current_token_loc(tokens: &Lexer) -> Loc {
    let start_loc = tokens.start_loc();
    make_loc(
        tokens.file_hash(),
        start_loc,
        start_loc + tokens.content().len(),
    )
}

fn spanned<T>(file_hash: FileHash, start: usize, end: usize, value: T) -> Spanned<T> {
    Spanned {
        loc: make_loc(file_hash, start, end),
        value,
    }
}

// Check for the specified token and consume it if it matches.
// Returns true if the token matches.
fn match_token(tokens: &mut Lexer, tok: Tok) -> Result<bool, Box<Diagnostic>> {
    if tokens.peek() == tok {
        tokens.advance()?;
        Ok(true)
    } else {
        Ok(false)
    }
}

// Check for the specified token and return an error if it does not match.
fn consume_token(tokens: &mut Lexer, tok: Tok) -> Result<(), Box<Diagnostic>> {
    consume_token_(tokens, tok, tokens.start_loc(), "")
}

fn consume_token_(
    tokens: &mut Lexer,
    tok: Tok,
    expected_start_loc: usize,
    expected_case: &str,
) -> Result<(), Box<Diagnostic>> {
    if tokens.peek() == tok {
        tokens.advance()?;
        Ok(())
    } else {
        let expected = format!("'{}'{}", tok, expected_case);
        Err(unexpected_token_error_(
            tokens,
            expected_start_loc,
            &expected,
        ))
    }
}

// let unexp_loc = current_token_loc(tokens);
// let unexp_msg = format!("Unexpected {}", current_token_error_string(tokens));

// let end_loc = tokens.previous_end_loc();
// let addr_loc = make_loc(tokens.file_hash(), start_loc, end_loc);
// let exp_msg = format!("Expected '::' {}", case);
// Err(vec![(unexp_loc, unexp_msg), (addr_loc, exp_msg)])

// Check for the identifier token with specified value and return an error if it does not match.
fn consume_identifier(tokens: &mut Lexer, value: &str) -> Result<(), Box<Diagnostic>> {
    if tokens.peek() == Tok::Identifier && tokens.content() == value {
        tokens.advance()
    } else {
        let expected = format!("'{}'", value);
        Err(unexpected_token_error(tokens, &expected))
    }
}

// If the next token is the specified kind, consume it and return
// its source location.
fn consume_optional_token_with_loc(
    tokens: &mut Lexer,
    tok: Tok,
) -> Result<Option<Loc>, Box<Diagnostic>> {
    if tokens.peek() == tok {
        let start_loc = tokens.start_loc();
        tokens.advance()?;
        let end_loc = tokens.previous_end_loc();
        Ok(Some(make_loc(tokens.file_hash(), start_loc, end_loc)))
    } else {
        Ok(None)
    }
}

// While parsing a list and expecting a ">" token to mark the end, replace
// a ">>" token with the expected ">". This handles the situation where there
// are nested type parameters that result in two adjacent ">" tokens, e.g.,
// "A<B<C>>".
fn adjust_token(tokens: &mut Lexer, end_token: Tok) {
    if tokens.peek() == Tok::GreaterGreater && end_token == Tok::Greater {
        tokens.replace_token(Tok::Greater, 1);
    }
}

// Parse a comma-separated list of items, including the specified starting and
// ending tokens.
fn parse_comma_list<F, R>(
    context: &mut Context,
    start_token: Tok,
    end_token: Tok,
    parse_list_item: F,
    item_description: &str,
) -> Result<Vec<R>, Box<Diagnostic>>
where
    F: Fn(&mut Context) -> Result<R, Box<Diagnostic>>,
{
    let start_loc = context.tokens.start_loc();
    consume_token(context.tokens, start_token)?;
    parse_comma_list_after_start(
        context,
        start_loc,
        start_token,
        end_token,
        parse_list_item,
        item_description,
    )
}

// Parse a comma-separated list of items, including the specified ending token, but
// assuming that the starting token has already been consumed.
fn parse_comma_list_after_start<F, R>(
    context: &mut Context,
    start_loc: usize,
    start_token: Tok,
    end_token: Tok,
    parse_list_item: F,
    item_description: &str,
) -> Result<Vec<R>, Box<Diagnostic>>
where
    F: Fn(&mut Context) -> Result<R, Box<Diagnostic>>,
{
    adjust_token(context.tokens, end_token);
    if match_token(context.tokens, end_token)? {
        return Ok(vec![]);
    }
    let mut v = vec![];
    loop {
        if context.tokens.peek() == Tok::Comma {
            let current_loc = context.tokens.start_loc();
            let loc = make_loc(context.tokens.file_hash(), current_loc, current_loc);
            return Err(Box::new(diag!(
                Syntax::UnexpectedToken,
                (loc, format!("Expected {}", item_description))
            )));
        }
        v.push(parse_list_item(context)?);
        adjust_token(context.tokens, end_token);
        if match_token(context.tokens, end_token)? {
            break Ok(v);
        }
        if !match_token(context.tokens, Tok::Comma)? {
            let current_loc = context.tokens.start_loc();
            let loc = make_loc(context.tokens.file_hash(), current_loc, current_loc);
            let loc2 = make_loc(context.tokens.file_hash(), start_loc, start_loc);
            return Err(Box::new(diag!(
                Syntax::UnexpectedToken,
                (loc, format!("Expected '{}'", end_token)),
                (loc2, format!("To match this '{}'", start_token)),
            )));
        }
        adjust_token(context.tokens, end_token);
        if match_token(context.tokens, end_token)? {
            break Ok(v);
        }
    }
}

// Parse a list of items, without specified start and end tokens, and the separator determined by
// the passed function `parse_list_continue`.
fn parse_list<C, F, R>(
    context: &mut Context,
    mut parse_list_continue: C,
    parse_list_item: F,
) -> Result<Vec<R>, Box<Diagnostic>>
where
    C: FnMut(&mut Context) -> Result<bool, Box<Diagnostic>>,
    F: Fn(&mut Context) -> Result<R, Box<Diagnostic>>,
{
    let mut v = vec![];
    loop {
        v.push(parse_list_item(context)?);
        if !parse_list_continue(context)? {
            break Ok(v);
        }
    }
}

//**************************************************************************************************
// Identifiers, Addresses, and Names
//**************************************************************************************************

// Parse an identifier:
//      Identifier = <IdentifierValue>
fn parse_identifier(context: &mut Context) -> Result<Name, Box<Diagnostic>> {
    if context.tokens.peek() != Tok::Identifier {
        return Err(unexpected_token_error(context.tokens, "an identifier"));
    }
    let start_loc = context.tokens.start_loc();
    let id = context.tokens.content().into();
    context.tokens.advance()?;
    let end_loc = context.tokens.previous_end_loc();
    Ok(spanned(context.tokens.file_hash(), start_loc, end_loc, id))
}

// Parse a numerical address value
//     NumericalAddress = <Number>
fn parse_address_bytes(
    context: &mut Context,
) -> Result<Spanned<NumericalAddress>, Box<Diagnostic>> {
    let loc = current_token_loc(context.tokens);
    let addr_res = NumericalAddress::parse_str(context.tokens.content());
    consume_token(context.tokens, Tok::NumValue)?;
    let addr_ = match addr_res {
        Ok(addr_) => addr_,
        Err(msg) => {
            context
                .env
                .add_diag(diag!(Syntax::InvalidAddress, (loc, msg)));
            NumericalAddress::DEFAULT_ERROR_ADDRESS
        }
    };
    Ok(sp(loc, addr_))
}

// Parse the beginning of an access, either an address or an identifier:
//      LeadingNameAccess = <NumericalAddress> | <Identifier>
fn parse_leading_name_access(
    context: &mut Context,
    allow_wildcard: bool,
) -> Result<LeadingNameAccess, Box<Diagnostic>> {
    parse_leading_name_access_(context, allow_wildcard, || "an address or an identifier")
}

// Parse the beginning of an access, either an address or an identifier with a specific description
fn parse_leading_name_access_<'a, F: FnOnce() -> &'a str>(
    context: &mut Context,
    allow_wildcard: bool,
    item_description: F,
) -> Result<LeadingNameAccess, Box<Diagnostic>> {
    match context.tokens.peek() {
        Tok::Identifier => {
            let loc = current_token_loc(context.tokens);
            let n = parse_identifier(context)?;
            Ok(sp(loc, LeadingNameAccess_::Name(n)))
        }
        Tok::Star if allow_wildcard => {
            let name = advance_wildcard_name(context)?;
            Ok(sp(name.loc, LeadingNameAccess_::Name(name)))
        }
        Tok::NumValue => {
            let sp!(loc, addr) = parse_address_bytes(context)?;
            Ok(sp(loc, LeadingNameAccess_::AnonymousAddress(addr)))
        }
        _ => Err(unexpected_token_error(context.tokens, item_description())),
    }
}

fn advance_wildcard_name(context: &mut Context) -> Result<Name, Box<Diagnostic>> {
    let loc = current_token_loc(context.tokens);
    context.tokens.advance()?;
    Ok(Name::new(loc, Symbol::from("*")))
}

// Parse a variable name:
//      Var = <Identifier>
fn parse_var(context: &mut Context) -> Result<Var, Box<Diagnostic>> {
    Ok(Var(parse_identifier(context)?))
}

// Parse a field name:
//      Field = <Identifier>
fn parse_field(context: &mut Context) -> Result<Field, Box<Diagnostic>> {
    Ok(Field(parse_identifier(context)?))
}

// Parse a module name:
//      ModuleName = <Identifier>
fn parse_module_name(context: &mut Context) -> Result<ModuleName, Box<Diagnostic>> {
    Ok(ModuleName(parse_identifier(context)?))
}

// Parse a module identifier:
//      ModuleIdent = <LeadingNameAccess> "::" <ModuleName>
fn parse_module_ident(context: &mut Context) -> Result<ModuleIdent, Box<Diagnostic>> {
    let start_loc = context.tokens.start_loc();
    let address = parse_leading_name_access(context, false)?;

    consume_token_(
        context.tokens,
        Tok::ColonColon,
        start_loc,
        " after an address in a module identifier",
    )?;
    let module = parse_module_name(context)?;
    let end_loc = context.tokens.previous_end_loc();
    let loc = make_loc(context.tokens.file_hash(), start_loc, end_loc);
    Ok(sp(loc, ModuleIdent_ { address, module }))
}

// Parse a module access (a variable, struct type, or function):
//      NameAccessChain = <LeadingNameAccess> ( "::" <Identifier> ( "::" <Identifier> )? )?
// If `allow_wildcard` is true, `*` will be accepted as an identifier.
fn parse_name_access_chain<'a, F: FnOnce() -> &'a str>(
    context: &mut Context,
    allow_wildcard: bool,
    item_description: F,
) -> Result<NameAccessChain, Box<Diagnostic>> {
    let start_loc = context.tokens.start_loc();
    let access = parse_name_access_chain_(context, allow_wildcard, item_description)?;
    let end_loc = context.tokens.previous_end_loc();
    Ok(spanned(
        context.tokens.file_hash(),
        start_loc,
        end_loc,
        access,
    ))
}

// Parse a module access with a specific description. If `allow_wildcard` is true, allows
// wildcards (`*`) for identifiers.
fn parse_name_access_chain_<'a, F: FnOnce() -> &'a str>(
    context: &mut Context,
    allow_wildcard: bool,
    item_description: F,
) -> Result<NameAccessChain_, Box<Diagnostic>> {
    let start_loc = context.tokens.start_loc();
    let ln = parse_leading_name_access_(context, allow_wildcard, item_description)?;
    let mut path = NamePath {
        root: RootPathEntry {
            name: ln,
            tyargs: None,
            is_macro: None,
        },
        entries: Vec::new(),
    };

    loop {
        if matches!(
            path.root.name,
            sp!(
                _,
                LeadingNameAccess_::AnonymousAddress(_) | LeadingNameAccess_::GlobalAddress(_)
            )
        ) {
            consume_token_(
                context.tokens,
                Tok::ColonColon,
                start_loc,
                " after an address in a module access chain",
            )?;
        } else if !match_token(context.tokens, Tok::ColonColon)? {
            break;
        }
        let name = parse_identifier_or_possibly_wildcard(context, allow_wildcard)?;
        path.entries.push(PathEntry {
            name,
            tyargs: None,
            is_macro: None,
        });
    }
    Ok(NameAccessChain_::Path(path))
}

fn parse_identifier_or_possibly_wildcard(
    context: &mut Context,
    allow_wildcard: bool,
) -> Result<Name, Box<Diagnostic>> {
    match context.tokens.peek() {
        Tok::Identifier => parse_identifier(context),
        Tok::Star if allow_wildcard => advance_wildcard_name(context),
        _ => Err(unexpected_token_error(
            context.tokens,
            if allow_wildcard {
                "an identifier or wildcard"
            } else {
                "an identifier"
            },
        )),
    }
}

//**************************************************************************************************
// Modifiers
//**************************************************************************************************

struct Modifiers {
    visibility: Option<Visibility>,
    entry: Option<Loc>,
    native: Option<Loc>,
}

impl Modifiers {
    fn empty() -> Self {
        Self {
            visibility: None,
            entry: None,
            native: None,
        }
    }
}

// Parse module member modifiers: visiblility and native.
// The modifiers are also used for script-functions
//      ModuleMemberModifiers = <ModuleMemberModifier>*
//      ModuleMemberModifier = <Visibility> | "native"
// ModuleMemberModifiers checks for uniqueness, meaning each individual ModuleMemberModifier can
// appear only once
fn parse_module_member_modifiers(context: &mut Context) -> Result<Modifiers, Box<Diagnostic>> {
    let mut mods = Modifiers::empty();
    loop {
        match context.tokens.peek() {
            Tok::Public => {
                let vis = parse_visibility(context)?;
                if let Some(prev_vis) = mods.visibility {
                    let msg = "Duplicate visibility modifier".to_string();
                    let prev_msg = "Visibility modifier previously given here".to_string();
                    context.env.add_diag(diag!(
                        Declarations::DuplicateItem,
                        (vis.loc().unwrap(), msg),
                        (prev_vis.loc().unwrap(), prev_msg),
                    ));
                }
                mods.visibility = Some(vis)
            }
            Tok::Native => {
                let loc = current_token_loc(context.tokens);
                context.tokens.advance()?;
                if let Some(prev_loc) = mods.native {
                    let msg = "Duplicate 'native' modifier".to_string();
                    let prev_msg = "'native' modifier previously given here".to_string();
                    context.env.add_diag(diag!(
                        Declarations::DuplicateItem,
                        (loc, msg),
                        (prev_loc, prev_msg)
                    ))
                }
                mods.native = Some(loc)
            }
            Tok::Identifier if context.tokens.content() == ENTRY_MODIFIER => {
                let loc = current_token_loc(context.tokens);
                context.tokens.advance()?;
                if let Some(prev_loc) = mods.entry {
                    let msg = format!("Duplicate '{}' modifier", ENTRY_MODIFIER);
                    let prev_msg = format!("'{}' modifier previously given here", ENTRY_MODIFIER);
                    context.env.add_diag(diag!(
                        Declarations::DuplicateItem,
                        (loc, msg),
                        (prev_loc, prev_msg)
                    ))
                }
                mods.entry = Some(loc)
            }
            _ => break,
        }
    }
    Ok(mods)
}

// Parse a function visibility modifier:
//      Visibility = "public" ( "(" "package" ")" )?
fn parse_visibility(context: &mut Context) -> Result<Visibility, Box<Diagnostic>> {
    let start_loc = context.tokens.start_loc();
    consume_token(context.tokens, Tok::Public)?;
    let sub_public_vis = if match_token(context.tokens, Tok::LParen)? {
        let sub_token = context.tokens.peek();
        let content = context.tokens.content();
        context.tokens.advance()?;
        if sub_token != Tok::RParen {
            consume_token(context.tokens, Tok::RParen)?;
        }
        Some(content)
    } else {
        None
    };
    let end_loc = context.tokens.previous_end_loc();
    // this loc will cover the span of 'public' or 'public(...)' in entirety
    let loc = make_loc(context.tokens.file_hash(), start_loc, end_loc);
    Ok(match sub_public_vis {
        None => Visibility::Public(loc),
        Some("package") => Visibility::Package(loc),
        _ => {
            let msg = format!(
                "Invalid visibility modifier. Consider removing it or using '{}' or '{}'",
                Visibility::PUBLIC,
                Visibility::PACKAGE
            );
            return Err(Box::new(diag!(Syntax::UnexpectedToken, (loc, msg))));
        }
    })
}
// Parse an attribute value. Either a value literal or a module access
//      AttributeValue =
//          <Value>
//          | <NameAccessChain>
fn parse_attribute_value(context: &mut Context) -> Result<AttributeValue, Box<Diagnostic>> {
    if let Some(v) = maybe_parse_value(context)? {
        return Ok(sp(v.loc, AttributeValue_::Value(v)));
    }

    let ma = parse_name_access_chain(context, false, || "attribute name value")?;
    Ok(sp(ma.loc, AttributeValue_::ModuleAccess(ma)))
}

// Parse a single attribute
//      Attribute =
//          <Identifier>
//          | <Identifier> "=" <AttributeValue>
//          | <Identifier> "(" Comma<Attribute> ")"
fn parse_attribute(context: &mut Context) -> Result<Attribute, Box<Diagnostic>> {
    let start_loc = context.tokens.start_loc();
    let n = parse_identifier(context)?;
    let attr_ = match context.tokens.peek() {
        Tok::Equal => {
            context.tokens.advance()?;
            Attribute_::Assigned(n, Box::new(parse_attribute_value(context)?))
        }
        Tok::LParen => {
            let args_ = parse_comma_list(
                context,
                Tok::LParen,
                Tok::RParen,
                parse_attribute,
                "attribute",
            )?;
            let end_loc = context.tokens.previous_end_loc();
            Attribute_::Parameterized(
                n,
                spanned(context.tokens.file_hash(), start_loc, end_loc, args_),
            )
        }
        _ => Attribute_::Name(n),
    };
    let end_loc = context.tokens.previous_end_loc();
    Ok(spanned(
        context.tokens.file_hash(),
        start_loc,
        end_loc,
        attr_,
    ))
}

// Parse attributes. Used to annotate a variety of AST nodes
//      Attributes = ("#" "[" Comma<Attribute> "]")*
fn parse_attributes(context: &mut Context) -> Result<Vec<Attributes>, Box<Diagnostic>> {
    let mut attributes_vec = vec![];
    while let Tok::NumSign = context.tokens.peek() {
        let start_loc = context.tokens.start_loc();
        context.tokens.advance()?;
        let attributes_ = parse_comma_list(
            context,
            Tok::LBracket,
            Tok::RBracket,
            parse_attribute,
            "attribute",
        )?;
        let end_loc = context.tokens.previous_end_loc();
        attributes_vec.push(spanned(
            context.tokens.file_hash(),
            start_loc,
            end_loc,
            attributes_,
        ))
    }
    Ok(attributes_vec)
}

//**************************************************************************************************
// Fields and Bindings
//**************************************************************************************************

// Parse a field name optionally followed by a colon and an expression argument:
//      ExpField = <Mutability>? <Field> <":" <Exp>>?
fn parse_exp_field(context: &mut Context) -> Result<(Mutability, Field, Exp), Box<Diagnostic>> {
    let mutability = consume_optional_token_with_loc(context.tokens, Tok::Mut)?;
    let f = parse_field(context)?;
    let arg = if match_token(context.tokens, Tok::Colon)? {
        parse_exp(context)?
    } else {
        sp(
            f.loc(),
            Exp_::Name(sp(
                f.loc(),
                NameAccessChain_::Single(PathEntry {
                    name: f.0,
                    tyargs: None,
                    is_macro: None,
                }),
            )),
        )
    };
    Ok((mutability, f, arg))
}

// Parse a field name optionally followed by a colon and a binding:
//      BindField = <Mutability>? <Field> <":" <Bind>>? | ".."
//
// If the binding is not specified, the default is to use a variable
// with the same name as the field.
fn parse_bind_field(context: &mut Context) -> Result<Ellipsis<(Field, Bind)>, Box<Diagnostic>> {
    if let Some(loc) = consume_optional_token_with_loc(context.tokens, Tok::PeriodPeriod)? {
        return Ok(Ellipsis::Ellipsis(loc));
    }
    let mutability = consume_optional_token_with_loc(context.tokens, Tok::Mut)?;
    let f = parse_field(context)?;
    let arg = if match_token(context.tokens, Tok::Colon)? {
        parse_bind(context)?
    } else {
        let v = Var(f.0);
        sp(v.loc(), Bind_::Var(mutability, v))
    };
    Ok(Ellipsis::Binder((f, arg)))
}

// Parse a binding or an ellipsis:
//      BindField = <Bind> | ".."
fn parse_bind_positional(context: &mut Context) -> Result<Ellipsis<Bind>, Box<Diagnostic>> {
    if let Some(loc) = consume_optional_token_with_loc(context.tokens, Tok::PeriodPeriod)? {
        return Ok(Ellipsis::Ellipsis(loc));
    }
    Ok(Ellipsis::Binder(parse_bind(context)?))
}

// Parse a binding:
//      Bind =
//          <Var>
//          | <NameAccessChain> <OptionalTypeArgs> "{" Comma<BindField> "}"
fn parse_bind(context: &mut Context) -> Result<Bind, Box<Diagnostic>> {
    let mutability = consume_optional_token_with_loc(context.tokens, Tok::Mut)?;
    let start_loc = context.tokens.start_loc();
    if context.tokens.peek() == Tok::Identifier {
        let next_tok = context.tokens.lookahead()?;
        if next_tok != Tok::LBrace && next_tok != Tok::Less && next_tok != Tok::ColonColon {
            let v = Bind_::Var(mutability, parse_var(context)?);
            let end_loc = context.tokens.previous_end_loc();
            return Ok(spanned(context.tokens.file_hash(), start_loc, end_loc, v));
        }
    }
    // The item description specified here should include the special case above for
    // variable names, because if the current context cannot be parsed as a struct name
    // it is possible that the user intention was to use a variable name.
    let ty = parse_name_access_chain(context, false, || "a variable or struct name")?;
    let _ty_args = parse_optional_type_args(context)?;
    Ok(if match_token(context.tokens, Tok::LParen)? {
        let args = parse_comma_list(
            context,
            Tok::LParen,
            Tok::RParen,
            parse_bind_positional,
            "a positional binding",
        )?;
        let end_loc = context.tokens.previous_end_loc();
        let unpack = Bind_::Unpack(Box::new(ty), FieldBindings::Positional(args));
        spanned(context.tokens.file_hash(), start_loc, end_loc, unpack)
    } else {
        let args = parse_comma_list(
            context,
            Tok::LBrace,
            Tok::RBrace,
            parse_bind_field,
            "a field binding",
        )?;
        let end_loc = context.tokens.previous_end_loc();
        let unpack = Bind_::Unpack(Box::new(ty), FieldBindings::Named(args));
        spanned(context.tokens.file_hash(), start_loc, end_loc, unpack)
    })
}

// Parse a list of bindings, which can be zero, one, or more bindings:
//      BindList =
//          <Bind>
//          | "(" Comma<Bind> ")"
//
// The list is enclosed in parenthesis, except that the parenthesis are
// optional if there is a single Bind.
fn parse_bind_list(context: &mut Context) -> Result<BindList, Box<Diagnostic>> {
    let start_loc = context.tokens.start_loc();
    let b = if context.tokens.peek() != Tok::LParen {
        vec![parse_bind(context)?]
    } else {
        parse_comma_list(
            context,
            Tok::LParen,
            Tok::RParen,
            parse_bind,
            "a variable or structure binding",
        )?
    };
    let end_loc = context.tokens.previous_end_loc();
    Ok(spanned(context.tokens.file_hash(), start_loc, end_loc, b))
}

// Parse a list of bindings, which can be zero, one, or more bindings:
//      BindList =
//          <Bind>
//          | "(" Comma<Bind> ")"
//
// The list is enclosed in parenthesis, except that the parenthesis are
// optional if there is a single Bind.
fn parse_typed_bind_list(
    context: &mut Context,
) -> Result<(BindList, Option<Type>), Box<Diagnostic>> {
    let start_loc = context.tokens.start_loc();
    let b = if context.tokens.peek() != Tok::LParen {
        vec![parse_bind(context)?]
    } else {
        parse_comma_list(
            context,
            Tok::LParen,
            Tok::RParen,
            parse_bind,
            "a variable or structure binding",
        )?
    };
    let end_loc = context.tokens.previous_end_loc();
    Ok((
        spanned(context.tokens.file_hash(), start_loc, end_loc, b),
        parse_type_qualifier(context)?,
    ))
}

// Parse a list of bindings for lambda.
//      LambdaBindList =
//          "|" Comma<Bind> "|"
fn parse_lambda_bind_list(context: &mut Context) -> Result<LambdaBindings, Box<Diagnostic>> {
    let start_loc = context.tokens.start_loc();
    let b = parse_comma_list(
        context,
        Tok::Pipe,
        Tok::Pipe,
        parse_typed_bind_list,
        "a variable or structure binding",
    )?;
    let end_loc = context.tokens.previous_end_loc();
    Ok(spanned(context.tokens.file_hash(), start_loc, end_loc, b))
}

//**************************************************************************************************
// Values
//**************************************************************************************************

// Parse a byte string:
//      ByteString = <ByteStringValue>
fn parse_byte_string(context: &mut Context) -> Result<Value_, Box<Diagnostic>> {
    if context.tokens.peek() != Tok::ByteStringValue {
        return Err(unexpected_token_error(
            context.tokens,
            "a byte string value",
        ));
    }
    let s = context.tokens.content();
    let text = Symbol::from(&s[2..s.len() - 1]);
    let value_ = if s.starts_with("x\"") {
        Value_::HexString(text)
    } else {
        assert!(s.starts_with("b\""));
        Value_::ByteString(text)
    };
    context.tokens.advance()?;
    Ok(value_)
}

// Parse a value:
//      Value =
//          "@" <LeadingAccessName>
//          | "true"
//          | "false"
//          | <Number>
//          | <NumberTyped>
//          | <ByteString>
fn maybe_parse_value(context: &mut Context) -> Result<Option<Value>, Box<Diagnostic>> {
    let start_loc = context.tokens.start_loc();
    let val = match context.tokens.peek() {
        Tok::AtSign => {
            context.tokens.advance()?;
            let addr = parse_leading_name_access(context, false)?;
            Value_::Address(addr)
        }
        Tok::True => {
            context.tokens.advance()?;
            Value_::Bool(true)
        }
        Tok::False => {
            context.tokens.advance()?;
            Value_::Bool(false)
        }
        Tok::NumValue => {
            //  If the number is followed by "::", parse it as the beginning of an address access
            if let Ok(Tok::ColonColon) = context.tokens.lookahead() {
                return Ok(None);
            }
            let num = context.tokens.content().into();
            context.tokens.advance()?;
            Value_::Num(num)
        }
        Tok::NumTypedValue => {
            let num = context.tokens.content().into();
            context.tokens.advance()?;
            Value_::Num(num)
        }

        Tok::ByteStringValue => parse_byte_string(context)?,
        _ => return Ok(None),
    };
    let end_loc = context.tokens.previous_end_loc();
    Ok(Some(spanned(
        context.tokens.file_hash(),
        start_loc,
        end_loc,
        val,
    )))
}

fn parse_value(context: &mut Context) -> Result<Value, Box<Diagnostic>> {
    Ok(maybe_parse_value(context)?.expect("parse_value called with invalid token"))
}

//**************************************************************************************************
// Sequences
//**************************************************************************************************

// Parse a sequence item:
//      SequenceItem =
//          <Exp>
//          | "let" <BindList> (":" <Type>)? ("=" <Exp>)?
fn parse_sequence_item(context: &mut Context) -> Result<SequenceItem, Box<Diagnostic>> {
    let start_loc = context.tokens.start_loc();
    let item = if match_token(context.tokens, Tok::Let)? {
        let b = parse_bind_list(context)?;
        let ty_opt = if match_token(context.tokens, Tok::Colon)? {
            Some(parse_type(context)?)
        } else {
            None
        };
        if match_token(context.tokens, Tok::Equal)? {
            let e = parse_exp(context)?;
            SequenceItem_::Bind(b, ty_opt, Box::new(e))
        } else {
            SequenceItem_::Declare(b, ty_opt)
        }
    } else {
        let e = parse_exp(context)?;
        SequenceItem_::Seq(Box::new(e))
    };
    let end_loc = context.tokens.previous_end_loc();
    Ok(spanned(
        context.tokens.file_hash(),
        start_loc,
        end_loc,
        item,
    ))
}

// Parse a sequence:
//      Sequence = <UseDecl>* (<SequenceItem> ";")* <Exp>? "}"
//
// Note that this does not include the opening brace of a block but it
// does consume the closing right brace.
fn parse_sequence(context: &mut Context) -> Result<Sequence, Box<Diagnostic>> {
    let mut uses = vec![];
    while context.tokens.peek() == Tok::Use {
        uses.push(parse_use_decl(vec![], context)?);
    }

    let mut seq: Vec<SequenceItem> = vec![];
    let mut last_semicolon_loc = None;
    let mut eopt = None;
    while context.tokens.peek() != Tok::RBrace {
        let item = parse_sequence_item(context)?;
        if context.tokens.peek() == Tok::RBrace {
            // If the sequence ends with an expression that is not
            // followed by a semicolon, split out that expression
            // from the rest of the SequenceItems.
            match item.value {
                SequenceItem_::Seq(e) => {
                    eopt = Some(Spanned {
                        loc: item.loc,
                        value: e.value,
                    });
                }
                _ => return Err(unexpected_token_error(context.tokens, "';'")),
            }
            break;
        }
        seq.push(item);
        last_semicolon_loc = Some(current_token_loc(context.tokens));
        consume_token(context.tokens, Tok::Semicolon)?;
    }
    context.tokens.advance()?; // consume the RBrace
    Ok((uses, seq, last_semicolon_loc, Box::new(eopt)))
}

//**************************************************************************************************
// Expressions
//**************************************************************************************************

// Parse an expression term:
//      Term =
//          "break <Label>? <Exp>?"
//          | "continue <Label>?"
//          | "vector" ('<' Comma<Type> ">")? "[" Comma<Exp> "]"
//          | <Value>
//          | "(" Comma<Exp> ")"
//          | "(" <Exp> ":" <Type> ")"
//          | "(" <Exp> "as" <Type> ")"
//          | "{" <Sequence>
//          | "if" "(" <Exp> ")" <Exp> "else" "{" <Exp> "}"
//          | "if" "(" <Exp> ")" "{" <Exp> "}"
//          | "if" "(" <Exp> ")" <Exp> ("else" <Exp>)?
//          | "<Label>? while" "(" <Exp> ")" "{" <Exp> "}"
//          | "<Label>? while" "(" <Exp> ")" <Exp> (SpecBlock)?
//          | "<Label>? loop" <Exp>
//          | "<Label>? loop" "{" <Exp> "}"
//          | "return" "{" <Exp> "}"
//          | "return" <Exp>?
//          | "abort" "{" <Exp> "}"
//          | "abort" <Exp>
fn parse_term(context: &mut Context) -> Result<Exp, Box<Diagnostic>> {
    const VECTOR_IDENT: &str = "vector";

    let start_loc = context.tokens.start_loc();
    let term = match context.tokens.peek() {
        tok if is_control_exp(tok) => {
            let (control_exp, ends_in_block) = parse_control_exp(context)?;
            if !ends_in_block || at_end_of_exp(context) {
                return Ok(control_exp);
            }

            return parse_binop_exp(context, control_exp, /* min_prec */ 1);
        }
        Tok::Break => {
            context.tokens.advance()?;
            let label = (context.tokens.peek() == Tok::BlockLabel)
                .then(|| parse_identifier(context))
                .transpose()?
                .map(BlockLabel);
            let exp = at_start_of_exp(context)
                .then(|| parse_exp(context))
                .transpose()?
                .map(Box::new);
            Exp_::Break(label, exp)
        }

        Tok::Continue => {
            context.tokens.advance()?;
            let label = (context.tokens.peek() == Tok::BlockLabel)
                .then(|| parse_identifier(context))
                .transpose()?
                .map(BlockLabel);
            Exp_::Continue(label)
        }

        Tok::Identifier
            if context.tokens.content() == VECTOR_IDENT
                && matches!(context.tokens.lookahead(), Ok(Tok::Less | Tok::LBracket)) =>
        {
            consume_identifier(context.tokens, VECTOR_IDENT)?;
            let vec_end_loc = context.tokens.previous_end_loc();
            let vec_loc = make_loc(context.tokens.file_hash(), start_loc, vec_end_loc);
            let targs_start_loc = context.tokens.start_loc();
            let tys_opt = parse_optional_type_args(context).map_err(|diag| {
                let targ_loc =
                    make_loc(context.tokens.file_hash(), targs_start_loc, targs_start_loc);
                add_type_args_ambiguity_label(targ_loc, diag)
            })?;
            let args_start_loc = context.tokens.start_loc();
            let args_ = parse_comma_list(
                context,
                Tok::LBracket,
                Tok::RBracket,
                parse_exp,
                "a vector argument expression",
            )?;
            let args_end_loc = context.tokens.previous_end_loc();
            let args = spanned(
                context.tokens.file_hash(),
                args_start_loc,
                args_end_loc,
                args_,
            );
            Exp_::Vector(vec_loc, tys_opt, args)
        }

        Tok::Identifier => parse_name_exp(context)?,

        Tok::NumValue => {
            // Check if this is a ModuleIdent (in a ModuleAccess).
            if context.tokens.lookahead()? == Tok::ColonColon {
                parse_name_exp(context)?
            } else {
                Exp_::Value(parse_value(context)?)
            }
        }

        Tok::AtSign | Tok::True | Tok::False | Tok::NumTypedValue | Tok::ByteStringValue => {
            Exp_::Value(parse_value(context)?)
        }

        // "(" Comma<Exp> ")"
        // "(" <Exp> ":" <Type> ")"
        // "(" <Exp> "as" <Type> ")"
        Tok::LParen => {
            let list_loc = context.tokens.start_loc();
            context.tokens.advance()?; // consume the LParen
            if match_token(context.tokens, Tok::RParen)? {
                Exp_::Unit
            } else {
                // If there is a single expression inside the parens,
                // then it may be followed by a colon and a type annotation.
                let e = parse_exp(context)?;
                if match_token(context.tokens, Tok::Colon)? {
                    let ty = parse_type(context)?;
                    consume_token(context.tokens, Tok::RParen)?;
                    Exp_::Annotate(Box::new(e), ty)
                } else if match_token(context.tokens, Tok::As)? {
                    let ty = parse_type(context)?;
                    consume_token(context.tokens, Tok::RParen)?;
                    Exp_::Cast(Box::new(e), ty)
                } else {
                    if context.tokens.peek() != Tok::RParen {
                        consume_token(context.tokens, Tok::Comma)?;
                    }
                    let mut es = parse_comma_list_after_start(
                        context,
                        list_loc,
                        Tok::LParen,
                        Tok::RParen,
                        parse_exp,
                        "an expression",
                    )?;
                    if es.is_empty() {
                        e.value
                    } else {
                        es.insert(0, e);
                        Exp_::ExpList(es)
                    }
                }
            }
        }

        // "{" <Sequence>
        Tok::LBrace => {
            context.tokens.advance()?; // consume the LBrace
            Exp_::Block(parse_sequence(context)?)
        }

        _ => {
            return Err(unexpected_token_error(context.tokens, "an expression term"));
        }
    };
    let end_loc = context.tokens.previous_end_loc();
    Ok(spanned(
        context.tokens.file_hash(),
        start_loc,
        end_loc,
        term,
    ))
}

fn is_control_exp(tok: Tok) -> bool {
    matches!(
        tok,
        Tok::If | Tok::While | Tok::Loop | Tok::Return | Tok::Abort
    )
}

// if there is a block, only parse the block, not any subsequent tokens
// e.g.           if (cond) e1 else { e2 } + 1
// should be,    (if (cond) e1 else { e2 }) + 1
// AND NOT,       if (cond) e1 else ({ e2 } + 1)
// But otherwise, if (cond) e1 else e2 + 1
// should be,     if (cond) e1 else (e2 + 1)
fn parse_control_exp(context: &mut Context) -> Result<(Exp, bool), Box<Diagnostic>> {
    fn parse_exp_or_sequence(context: &mut Context) -> Result<(Exp, bool), Box<Diagnostic>> {
        match context.tokens.peek() {
            Tok::LBrace => {
                let block_start_loc = context.tokens.start_loc();
                context.tokens.advance()?; // consume the LBrace
                let block_ = Exp_::Block(parse_sequence(context)?);
                let block_end_loc = context.tokens.previous_end_loc();
                let exp = spanned(
                    context.tokens.file_hash(),
                    block_start_loc,
                    block_end_loc,
                    block_,
                );
                Ok((exp, true))
            }
            _ => Ok((parse_exp(context)?, false)),
        }
    }
    let start_loc = context.tokens.start_loc();
    match_token(context.tokens, Tok::BlockLabel)?;
    let (exp_, ends_in_block) = match context.tokens.peek() {
        Tok::If => {
            context.tokens.advance()?;
            consume_token(context.tokens, Tok::LParen)?;
            let eb = Box::new(parse_exp(context)?);
            consume_token(context.tokens, Tok::RParen)?;
            let (et, ends_in_block) = parse_exp_or_sequence(context)?;
            let (ef, ends_in_block) = if match_token(context.tokens, Tok::Else)? {
                let (ef, ends_in_block) = parse_exp_or_sequence(context)?;
                (Some(Box::new(ef)), ends_in_block)
            } else {
                (None, ends_in_block)
            };
            (Exp_::IfElse(eb, Box::new(et), ef), ends_in_block)
        }
        Tok::While => {
            context.tokens.advance()?;
            consume_token(context.tokens, Tok::LParen)?;
            let econd = parse_exp(context)?;
            consume_token(context.tokens, Tok::RParen)?;
            let (eloop, ends_in_block) = parse_exp_or_sequence(context)?;
            (Exp_::While(Box::new(econd), Box::new(eloop)), ends_in_block)
        }
        Tok::Loop => {
            context.tokens.advance()?;
            let (eloop, ends_in_block) = parse_exp_or_sequence(context)?;
            (Exp_::Loop(Box::new(eloop)), ends_in_block)
        }
        Tok::Return => {
            context.tokens.advance()?;
            let label = (context.tokens.peek() == Tok::BlockLabel)
                .then(|| parse_identifier(context))
                .transpose()?
                .map(BlockLabel);
            let (e, ends_in_block) = if !at_start_of_exp(context) {
                (None, false)
            } else {
                let (e, ends_in_block) = parse_exp_or_sequence(context)?;
                (Some(Box::new(e)), ends_in_block)
            };
            (Exp_::Return(label, e), ends_in_block)
        }
        Tok::Abort => {
            context.tokens.advance()?;
            let (e, ends_in_block) = parse_exp_or_sequence(context)?;
            (Exp_::Abort(Box::new(e)), ends_in_block)
        }
        _ => unreachable!(),
    };
    let end_loc = context.tokens.previous_end_loc();
    let exp = spanned(context.tokens.file_hash(), start_loc, end_loc, exp_);
    Ok((exp, ends_in_block))
}

// Parse a pack, call, or other reference to a name:
//      NameExp =
//          <NameAccessChain> <OptionalTypeArgs> "{" Comma<ExpField> "}"
//          | <NameAccessChain> <OptionalTypeArgs> "(" Comma<Exp> ")"
//          | <NameAccessChain> "!" "(" Comma<Exp> ")"
//          | <NameAccessChain> <OptionalTypeArgs>
fn parse_name_exp(context: &mut Context) -> Result<Exp_, Box<Diagnostic>> {
    let n = parse_name_access_chain(context, false, || {
        panic!("parse_name_exp with something other than a ModuleAccess")
    })?;

    // There's an ambiguity if the name is followed by a '<'. If there is no whitespace
    // after the name, treat it as the start of a list of type arguments. Otherwise
    // assume that the '<' is a boolean operator.
    let start_loc = context.tokens.start_loc();
    if context.tokens.peek() == Tok::Exclaim {
        context.tokens.advance()?;
        let rhs = parse_call_args(context)?;
        return Ok(Exp_::Call(n, rhs));
    }

    if context.tokens.peek() == Tok::Less && n.loc.end() as usize == start_loc {
        let loc = make_loc(context.tokens.file_hash(), start_loc, start_loc);
        parse_optional_type_args(context)
            .map_err(|diag| add_type_args_ambiguity_label(loc, diag))?;
    }

    match context.tokens.peek() {
        // Pack: "{" Comma<ExpField> "}"
        Tok::LBrace => {
            let fs = parse_comma_list(
                context,
                Tok::LBrace,
                Tok::RBrace,
                parse_exp_field,
                "a field expression",
            )?
            .into_iter()
            .map(|(_, f, e)| (f, e))
            .collect();
            Ok(Exp_::Pack(n, fs))
        }

        // Call: "(" Comma<Exp> ")"
        Tok::Exclaim | Tok::LParen => {
            let rhs = parse_call_args(context)?;
            Ok(Exp_::Call(n, rhs))
        }

        // Other name reference...
        _ => Ok(Exp_::Name(n)),
    }
}

// Parse the arguments to a call: "(" Comma<Exp> ")"
fn parse_call_args(context: &mut Context) -> Result<Spanned<Vec<Exp>>, Box<Diagnostic>> {
    let start_loc = context.tokens.start_loc();
    let args = parse_comma_list(
        context,
        Tok::LParen,
        Tok::RParen,
        parse_exp,
        "a call argument expression",
    )?;
    let end_loc = context.tokens.previous_end_loc();
    Ok(spanned(
        context.tokens.file_hash(),
        start_loc,
        end_loc,
        args,
    ))
}

// Return true if the current token is one that might occur after an Exp.
// This is needed, for example, to check for the optional Exp argument to
// a return (where "return" is itself an Exp).
fn at_end_of_exp(context: &mut Context) -> bool {
    matches!(
        context.tokens.peek(),
        // These are the tokens that can occur after an Exp. If the grammar
        // changes, we need to make sure that these are kept up to date and that
        // none of these tokens can occur at the beginning of an Exp.
        Tok::Else | Tok::RBrace | Tok::RParen | Tok::Comma | Tok::Colon | Tok::Semicolon
    )
}

fn at_start_of_exp(context: &mut Context) -> bool {
    matches!(
        context.tokens.peek(),
        // value
        Tok::NumValue
            | Tok::NumTypedValue
            | Tok::ByteStringValue
            | Tok::Identifier
            | Tok::AtSign
            | Tok::Copy
            | Tok::Move
            | Tok::False
            | Tok::True
            | Tok::Amp
            | Tok::AmpMut
            | Tok::Star
            | Tok::Exclaim
            | Tok::LParen
            | Tok::LBrace
            | Tok::Abort
            | Tok::Break
            | Tok::Continue
            | Tok::If
            | Tok::Loop
            | Tok::Return
            | Tok::While
    )
}

// Parse an expression:
//      Exp =
//            <LambdaBindList> <Exp>        spec only
//          | <Quantifier>                  spec only
//          | <BinOpExp>
//          | <UnaryExp> "=" <Exp>
fn parse_exp(context: &mut Context) -> Result<Exp, Box<Diagnostic>> {
    let start_loc = context.tokens.start_loc();
    let exp = match context.tokens.peek() {
        Tok::Pipe => {
            let bindings = parse_lambda_bind_list(context)?;
            let return_type = match_token(context.tokens, Tok::MinusGreater)?
                .then(|| parse_type(context))
                .transpose()?;
            let body = Box::new(parse_exp(context)?);
            Exp_::Lambda(bindings, return_type, body)
        }
        _ => {
            // This could be either an assignment or a binary operator
            // expression.
            let lhs = parse_unary_exp(context)?;
            if context.tokens.peek() != Tok::Equal {
                return parse_binop_exp(context, lhs, /* min_prec */ 1);
            }
            context.tokens.advance()?; // consume the "="
            let rhs = Box::new(parse_exp(context)?);
            Exp_::Assign(Box::new(lhs), rhs)
        }
    };
    let end_loc = context.tokens.previous_end_loc();
    Ok(spanned(context.tokens.file_hash(), start_loc, end_loc, exp))
}

// Get the precedence of a binary operator. The minimum precedence value
// is 1, and larger values have higher precedence. For tokens that are not
// binary operators, this returns a value of zero so that they will be
// below the minimum value and will mark the end of the binary expression
// for the code in parse_binop_exp.
fn get_precedence(token: Tok) -> u32 {
    match token {
        // Reserved minimum precedence value is 1
        Tok::EqualEqualGreater => 2,
        Tok::LessEqualEqualGreater => 2,
        Tok::PipePipe => 3,
        Tok::AmpAmp => 4,
        Tok::EqualEqual => 5,
        Tok::ExclaimEqual => 5,
        Tok::Less => 5,
        Tok::Greater => 5,
        Tok::LessEqual => 5,
        Tok::GreaterEqual => 5,
        Tok::PeriodPeriod => 6,
        Tok::Pipe => 7,
        Tok::Caret => 8,
        Tok::Amp => 9,
        Tok::LessLess => 10,
        Tok::GreaterGreater => 10,
        Tok::Plus => 11,
        Tok::Minus => 11,
        Tok::Star => 12,
        Tok::Slash => 12,
        Tok::Percent => 12,
        _ => 0, // anything else is not a binary operator
    }
}

// Parse a binary operator expression:
//      BinOpExp =
//          <BinOpExp> <BinOp> <BinOpExp>
//          | <UnaryExp>
//      BinOp = (listed from lowest to highest precedence)
//          "==>"                                       spec only
//          | "||"
//          | "&&"
//          | "==" | "!=" | '<' | ">" | "<=" | ">="
//          | ".."                                      spec only
//          | "|"
//          | "^"
//          | "&"
//          | "<<" | ">>"
//          | "+" | "-"
//          | "*" | "/" | "%"
//
// This function takes the LHS of the expression as an argument, and it
// continues parsing binary expressions as long as they have at least the
// specified "min_prec" minimum precedence.
fn parse_binop_exp(context: &mut Context, lhs: Exp, min_prec: u32) -> Result<Exp, Box<Diagnostic>> {
    let mut result = lhs;
    let mut next_tok_prec = get_precedence(context.tokens.peek());

    while next_tok_prec >= min_prec {
        // Parse the operator.
        let op_start_loc = context.tokens.start_loc();
        let op_token = context.tokens.peek();
        context.tokens.advance()?;
        let op_end_loc = context.tokens.previous_end_loc();

        let mut rhs = parse_unary_exp(context)?;

        // If the next token is another binary operator with a higher
        // precedence, then recursively parse that expression as the RHS.
        let this_prec = next_tok_prec;
        next_tok_prec = get_precedence(context.tokens.peek());
        if this_prec < next_tok_prec {
            rhs = parse_binop_exp(context, rhs, this_prec + 1)?;
            next_tok_prec = get_precedence(context.tokens.peek());
        }

        let op = match op_token {
            Tok::EqualEqual => BinOp_::Eq,
            Tok::ExclaimEqual => BinOp_::Neq,
            Tok::Less => BinOp_::Lt,
            Tok::Greater => BinOp_::Gt,
            Tok::LessEqual => BinOp_::Le,
            Tok::GreaterEqual => BinOp_::Ge,
            Tok::PipePipe => BinOp_::Or,
            Tok::AmpAmp => BinOp_::And,
            Tok::Caret => BinOp_::Xor,
            Tok::Pipe => BinOp_::BitOr,
            Tok::Amp => BinOp_::BitAnd,
            Tok::LessLess => BinOp_::Shl,
            Tok::GreaterGreater => BinOp_::Shr,
            Tok::Plus => BinOp_::Add,
            Tok::Minus => BinOp_::Sub,
            Tok::Star => BinOp_::Mul,
            Tok::Slash => BinOp_::Div,
            Tok::Percent => BinOp_::Mod,
            Tok::PeriodPeriod => BinOp_::Range,
            Tok::EqualEqualGreater => BinOp_::Implies,
            Tok::LessEqualEqualGreater => BinOp_::Iff,
            _ => panic!("Unexpected token that is not a binary operator"),
        };
        let sp_op = spanned(context.tokens.file_hash(), op_start_loc, op_end_loc, op);

        let start_loc = result.loc.start() as usize;
        let end_loc = context.tokens.previous_end_loc();
        let e = Exp_::BinopExp(Box::new(result), sp_op, Box::new(rhs));
        result = spanned(context.tokens.file_hash(), start_loc, end_loc, e);
    }

    Ok(result)
}

// Parse a unary expression:
//      UnaryExp =
//          "!" <UnaryExp>
//          | "&mut" <UnaryExp>
//          | "&" <UnaryExp>
//          | "*" <UnaryExp>
//          | "move" <Var>
//          | "copy" <Var>
//          | <DotOrIndexChain>
fn parse_unary_exp(context: &mut Context) -> Result<Exp, Box<Diagnostic>> {
    let start_loc = context.tokens.start_loc();
    let exp = match context.tokens.peek() {
        Tok::Exclaim => {
            context.tokens.advance()?;
            let op_end_loc = context.tokens.previous_end_loc();
            let op = spanned(
                context.tokens.file_hash(),
                start_loc,
                op_end_loc,
                UnaryOp_::Not,
            );
            let e = parse_unary_exp(context)?;
            Exp_::UnaryExp(op, Box::new(e))
        }
        Tok::AmpMut => {
            context.tokens.advance()?;
            let e = parse_unary_exp(context)?;
            Exp_::Borrow(true, Box::new(e))
        }
        Tok::Amp => {
            context.tokens.advance()?;
            let e = parse_unary_exp(context)?;
            Exp_::Borrow(false, Box::new(e))
        }
        Tok::Star => {
            context.tokens.advance()?;
            let e = parse_unary_exp(context)?;
            Exp_::Dereference(Box::new(e))
        }
        Tok::Move => {
            context.tokens.advance()?;
            let end_loc = context.tokens.previous_end_loc();
            Exp_::Move(
                make_loc(context.tokens.file_hash(), start_loc, end_loc),
                Box::new(parse_exp(context)?),
            )
        }
        Tok::Copy => {
            context.tokens.advance()?;
            let end_loc = context.tokens.previous_end_loc();
            Exp_::Copy(
                make_loc(context.tokens.file_hash(), start_loc, end_loc),
                Box::new(parse_exp(context)?),
            )
        }
        _ => {
            return parse_dot_or_index_chain(context);
        }
    };
    let end_loc = context.tokens.previous_end_loc();
    Ok(spanned(context.tokens.file_hash(), start_loc, end_loc, exp))
}

// Parse an expression term optionally followed by a chain of dot or index accesses:
//      DotOrIndexChain =
//          <DotOrIndexChain> "." <Identifier>
//          | <DotOrIndexChain> "[" <Exp> "]"                      spec only
//          | <Term>
fn parse_dot_or_index_chain(context: &mut Context) -> Result<Exp, Box<Diagnostic>> {
    let start_loc = context.tokens.start_loc();
    let mut lhs = parse_term(context)?;
    loop {
        let exp = match context.tokens.peek() {
            Tok::Period => {
                context.tokens.advance()?;
                let n = parse_identifier(context)?;
                Exp_::Dot(Box::new(lhs), n)
            }
            Tok::LBracket => {
                context.tokens.advance()?;
                let start_loc = context.tokens.start_loc();
                let index = parse_exp(context)?;
                let end_loc = context.tokens.previous_end_loc();
                let exp = Exp_::Index(
                    Box::new(lhs),
                    spanned(context.tokens.file_hash(), start_loc, end_loc, vec![index]),
                );
                consume_token(context.tokens, Tok::RBracket)?;
                exp
            }
            _ => break,
        };
        let end_loc = context.tokens.previous_end_loc();
        lhs = spanned(context.tokens.file_hash(), start_loc, end_loc, exp);
    }
    Ok(lhs)
}

//**************************************************************************************************
// Types
//**************************************************************************************************

// Parse a Type:
//      Type =
//          <NameAccessChain> ('<' Comma<Type> ">")?
//          | "&" <Type>
//          | "&mut" <Type>
//          | "|" Comma<Type> "|" Type   (spec only)
//          | "(" Comma<Type> ")"
fn parse_type(context: &mut Context) -> Result<Type, Box<Diagnostic>> {
    let start_loc = context.tokens.start_loc();
    let t = match context.tokens.peek() {
        Tok::LParen => {
            let mut ts = parse_comma_list(context, Tok::LParen, Tok::RParen, parse_type, "a type")?;
            match ts.len() {
                0 => Type_::Unit,
                1 => ts.pop().unwrap().value,
                _ => Type_::Multiple(ts),
            }
        }
        Tok::Amp => {
            context.tokens.advance()?;
            let t = parse_type(context)?;
            Type_::Ref(false, Box::new(t))
        }
        Tok::AmpMut => {
            context.tokens.advance()?;
            let t = parse_type(context)?;
            Type_::Ref(true, Box::new(t))
        }
        Tok::Pipe => {
            let args = parse_comma_list(context, Tok::Pipe, Tok::Pipe, parse_type, "a type")?;
            let result = if is_start_of_type(context) {
                parse_type(context)?
            } else {
                spanned(
                    context.tokens.file_hash(),
                    start_loc,
                    context.tokens.start_loc(),
                    Type_::Unit,
                )
            };
            return Ok(spanned(
                context.tokens.file_hash(),
                start_loc,
                context.tokens.previous_end_loc(),
                Type_::Fun(args, Box::new(result)),
            ));
        }
        _ => {
            let tn = parse_name_access_chain(context, false, || "a type name")?;
            if context.tokens.peek() == Tok::Less {
                parse_comma_list(context, Tok::Less, Tok::Greater, parse_type, "a type")?;
            }
            Type_::Apply(Box::new(tn))
        }
    };
    let end_loc = context.tokens.previous_end_loc();
    Ok(spanned(context.tokens.file_hash(), start_loc, end_loc, t))
}

fn parse_type_qualifier(context: &mut Context) -> Result<Option<Type>, Box<Diagnostic>> {
    match_token(context.tokens, Tok::Colon)?
        .then(|| parse_type(context))
        .transpose()
}

/// Checks whether the next tokens looks like the start of a type. NOTE: must be aligned
/// with `parse_type`.
fn is_start_of_type(context: &mut Context) -> bool {
    matches!(
        context.tokens.peek(),
        Tok::LParen | Tok::Amp | Tok::AmpMut | Tok::Pipe | Tok::Identifier
    )
}

// Parse an optional list of type arguments.
//    OptionalTypeArgs = '<' Comma<Type> ">" | <empty>
fn parse_optional_type_args(context: &mut Context) -> Result<Option<Vec<Type>>, Box<Diagnostic>> {
    if context.tokens.peek() == Tok::Less {
        Ok(Some(parse_comma_list(
            context,
            Tok::Less,
            Tok::Greater,
            parse_type,
            "a type",
        )?))
    } else {
        Ok(None)
    }
}

pub fn token_to_ability(token: Tok, content: &str) -> Option<Ability_> {
    match (token, content) {
        (Tok::Copy, _) => Some(Ability_::Copy),
        (Tok::Identifier, Ability_::DROP) => Some(Ability_::Drop),
        (Tok::Identifier, Ability_::STORE) => Some(Ability_::Store),
        (Tok::Identifier, Ability_::KEY) => Some(Ability_::Key),
        _ => None,
    }
}

// Parse a type ability
//      Ability =
//          <Copy>
//          | "drop"
//          | "store"
//          | "key"
fn parse_ability(context: &mut Context) -> Result<Ability, Box<Diagnostic>> {
    let loc = current_token_loc(context.tokens);
    match token_to_ability(context.tokens.peek(), context.tokens.content()) {
        Some(ability) => {
            context.tokens.advance()?;
            Ok(sp(loc, ability))
        }
        None => {
            let msg = format!(
                "Unexpected {}. Expected a type ability, one of: 'copy', 'drop', 'store', or 'key'",
                current_token_error_string(context.tokens)
            );
            Err(Box::new(diag!(Syntax::UnexpectedToken, (loc, msg))))
        }
    }
}

// Parse a type parameter:
//      TypeParameter =
//          <Identifier> <Constraint>?
//      Constraint =
//          ":" <Ability> (+ <Ability>)*
fn parse_type_parameter(context: &mut Context) -> Result<(Name, Vec<Ability>), Box<Diagnostic>> {
    let n = parse_identifier(context)?;

    let ability_constraints = if match_token(context.tokens, Tok::Colon)? {
        parse_list(
            context,
            |context| match context.tokens.peek() {
                Tok::Plus => {
                    context.tokens.advance()?;
                    Ok(true)
                }
                Tok::Greater | Tok::Comma => Ok(false),
                _ => Err(unexpected_token_error(
                    context.tokens,
                    &format!(
                        "one of: '{}', '{}', or '{}'",
                        Tok::Plus,
                        Tok::Greater,
                        Tok::Comma
                    ),
                )),
            },
            parse_ability,
        )?
    } else {
        vec![]
    };
    Ok((n, ability_constraints))
}

// Parse type parameter with optional phantom declaration:
//   TypeParameterWithPhantomDecl = "phantom"? <TypeParameter>
fn parse_type_parameter_with_phantom_decl(
    context: &mut Context,
) -> Result<DatatypeTypeParameter, Box<Diagnostic>> {
    let is_phantom =
        if context.tokens.peek() == Tok::Identifier && context.tokens.content() == "phantom" {
            context.tokens.advance()?;
            true
        } else {
            false
        };
    let (name, constraints) = parse_type_parameter(context)?;
    Ok(DatatypeTypeParameter {
        is_phantom,
        name,
        constraints,
    })
}

// Parse optional type parameter list.
//    OptionalTypeParameters = '<' Comma<TypeParameter> ">" | <empty>
fn parse_optional_type_parameters(
    context: &mut Context,
) -> Result<Vec<(Name, Vec<Ability>)>, Box<Diagnostic>> {
    if context.tokens.peek() == Tok::Less {
        parse_comma_list(
            context,
            Tok::Less,
            Tok::Greater,
            parse_type_parameter,
            "a type parameter",
        )
    } else {
        Ok(vec![])
    }
}

// Parse optional struct type parameters:
//    StructTypeParameter = '<' Comma<TypeParameterWithPhantomDecl> ">" | <empty>
fn parse_struct_type_parameters(
    context: &mut Context,
) -> Result<Vec<DatatypeTypeParameter>, Box<Diagnostic>> {
    if context.tokens.peek() == Tok::Less {
        parse_comma_list(
            context,
            Tok::Less,
            Tok::Greater,
            parse_type_parameter_with_phantom_decl,
            "a type parameter",
        )
    } else {
        Ok(vec![])
    }
}

//**************************************************************************************************
// Functions
//**************************************************************************************************

// Parse a function declaration:
//      FunctionDecl =
//          [ "inline" ] "fun"
//          <FunctionDefName> "(" Comma<Parameter> ")"
//          (":" <Type>)?
//          ("acquires" <NameAccessChain> ("," <NameAccessChain>)*)?
//          ("{" <Sequence> "}" | ";")
//
fn parse_function_decl(
    attributes: Vec<Attributes>,
    start_loc: usize,
    modifiers: Modifiers,
    context: &mut Context,
) -> Result<Function, Box<Diagnostic>> {
    let Modifiers {
        visibility,
        entry,
        native,
    } = modifiers;

    consume_token(context.tokens, Tok::Fun)?;
    let name = FunctionName(parse_identifier(context)?);
    let type_parameters = parse_optional_type_parameters(context)?;

    // "(" Comma<Parameter> ")"
    let parameters = parse_comma_list(
        context,
        Tok::LParen,
        Tok::RParen,
        parse_parameter,
        "a function parameter",
    )?;

    // (":" <Type>)?
    let return_type = if match_token(context.tokens, Tok::Colon)? {
        parse_type(context)?
    } else {
        sp(name.loc(), Type_::Unit)
    };

    let body = match native {
        Some(loc) => {
            consume_token(context.tokens, Tok::Semicolon)?;
            sp(loc, FunctionBody_::Native)
        }
        _ => {
            let start_loc = context.tokens.start_loc();
            consume_token(context.tokens, Tok::LBrace)?;
            let seq = parse_sequence(context)?;
            let end_loc = context.tokens.previous_end_loc();
            sp(
                make_loc(context.tokens.file_hash(), start_loc, end_loc),
                FunctionBody_::Defined(seq),
            )
        }
    };

    let signature = FunctionSignature {
        type_parameters,
        parameters,
        return_type,
    };

    let loc = make_loc(
        context.tokens.file_hash(),
        start_loc,
        context.tokens.previous_end_loc(),
    );
    Ok(Function {
        attributes,
        loc,
        visibility: visibility.unwrap_or(Visibility::Internal),
        entry,
        signature,
        name,
        body,
        macro_: None,
    })
}

// Parse a function parameter:
//      Parameter = <Mutability>? <Var> ":" <Type>
fn parse_parameter(context: &mut Context) -> Result<(Mutability, Var, Type), Box<Diagnostic>> {
    let mutability = consume_optional_token_with_loc(context.tokens, Tok::Mut)?;
    let v = parse_var(context)?;
    consume_token(context.tokens, Tok::Colon)?;
    let t = parse_type(context)?;
    Ok((mutability, v, t))
}

//**************************************************************************************************
// Structs
//**************************************************************************************************

// Parse a struct definition:
//      StructDecl =
//          "struct" <StructDefName> ("has" <Ability> (, <Ability>)+)?
//          ("{" Comma<FieldAnnot> "}" | <"(" Comma<Type> ")"> | ";")
//      StructDefName =
//          <Identifier> <OptionalTypeParameters>
fn parse_struct_decl(
    attributes: Vec<Attributes>,
    start_loc: usize,
    modifiers: Modifiers,
    context: &mut Context,
) -> Result<StructDefinition, Box<Diagnostic>> {
    let Modifiers {
        visibility,
        entry,
        native,
    } = modifiers;
    if let Some(vis) = visibility {
        let msg = format!(
            "Invalid struct declaration. Structs cannot have visibility modifiers as they are \
             always '{}'",
            Visibility::PUBLIC
        );
        context
            .env
            .add_diag(diag!(Syntax::InvalidModifier, (vis.loc().unwrap(), msg)));
    }
    if let Some(loc) = entry {
        let msg = format!(
            "Invalid struct declaration. '{}' is used only on functions",
            ENTRY_MODIFIER
        );
        context
            .env
            .add_diag(diag!(Syntax::InvalidModifier, (loc, msg)));
    }

    consume_token(context.tokens, Tok::Struct)?;

    // <StructDefName>
    let name = DatatypeName(parse_identifier(context)?);
    let type_parameters = parse_struct_type_parameters(context)?;

    let abilities = if context.tokens.peek() == Tok::Identifier && context.tokens.content() == "has"
    {
        context.tokens.advance()?;
        parse_list(
            context,
            |context| match context.tokens.peek() {
                Tok::Comma => {
                    context.tokens.advance()?;
                    Ok(true)
                }
                Tok::LBrace | Tok::Semicolon => Ok(false),
                _ => Err(unexpected_token_error(
                    context.tokens,
                    &format!(
                        "one of: '{}', '{}', or '{}'",
                        Tok::Comma,
                        Tok::LBrace,
                        Tok::Semicolon
                    ),
                )),
            },
            parse_ability,
        )?
    } else {
        Vec::new()
    };

    let fields = match native {
        Some(loc) => {
            consume_token(context.tokens, Tok::Semicolon)?;
            StructFields::Native(loc)
        }
        _ => {
            if context.tokens.peek() == Tok::LParen {
                StructFields::Positional(parse_comma_list(
                    context,
                    Tok::LParen,
                    Tok::RParen,
                    parse_type,
                    "a type",
                )?)
            } else {
                StructFields::Named(parse_comma_list(
                    context,
                    Tok::LBrace,
                    Tok::RBrace,
                    parse_field_annot,
                    "a field",
                )?)
            }
        }
    };

    let loc = make_loc(
        context.tokens.file_hash(),
        start_loc,
        context.tokens.previous_end_loc(),
    );
    Ok(StructDefinition {
        attributes,
        loc,
        abilities,
        name,
        type_parameters,
        fields,
    })
}

// Parse a field annotated with a type:
//      FieldAnnot = <DocComments> <Field> ":" <Type>
fn parse_field_annot(context: &mut Context) -> Result<(Field, Type), Box<Diagnostic>> {
    context.tokens.match_doc_comments();
    let f = parse_field(context)?;
    consume_token(context.tokens, Tok::Colon)?;
    let st = parse_type(context)?;
    Ok((f, st))
}

//**************************************************************************************************
// Enums
//**************************************************************************************************

// Parse an enum definition:
//      EnumDecl =
//          "enum" <EnumDefName> ("has" <Ability> (, <Ability>)+)?
//          ("{" Comma<VariantDef> "}" | ";")
//      EnumDefName =
//          <Identifier> <OptionalTypeParameters>
fn parse_enum_decl(
    attributes: Vec<Attributes>,
    start_loc: usize,
    modifiers: Modifiers,
    context: &mut Context,
) -> Result<EnumDefinition, Box<Diagnostic>> {
    let Modifiers {
        visibility, entry, ..
    } = modifiers;
    if let Some(vis) = visibility {
        let msg = format!(
            "Invalid enum declaration. Enums cannot have visibility modifiers as they are \
             always '{}'",
            Visibility::PUBLIC
        );
        context
            .env
            .add_diag(diag!(Syntax::InvalidModifier, (vis.loc().unwrap(), msg)));
    }
    if let Some(loc) = entry {
        let msg = format!(
            "Invalid enum declaration. '{}' is used only on functions",
            ENTRY_MODIFIER
        );
        context
            .env
            .add_diag(diag!(Syntax::InvalidModifier, (loc, msg)));
    }

    consume_token(context.tokens, Tok::Enum)?;

    // <EnumDefName>
    let name = DatatypeName(parse_identifier(context)?);
    let type_parameters = parse_struct_type_parameters(context)?;

    let abilities = if context.tokens.peek() == Tok::Identifier && context.tokens.content() == "has"
    {
        context.tokens.advance()?;
        parse_list(
            context,
            |context| match context.tokens.peek() {
                Tok::Comma => {
                    context.tokens.advance()?;
                    Ok(true)
                }
                Tok::LBrace | Tok::Semicolon => Ok(false),
                _ => Err(unexpected_token_error(
                    context.tokens,
                    &format!(
                        "one of: '{}', '{}', or '{}'",
                        Tok::Comma,
                        Tok::LBrace,
                        Tok::Semicolon
                    ),
                )),
            },
            parse_ability,
        )?
    } else {
        Vec::new()
    };

    let variants = parse_comma_list(
        context,
        Tok::LBrace,
        Tok::RBrace,
        parse_variant_def,
        "an enum variant",
    )?;

    let loc = make_loc(
        context.tokens.file_hash(),
        start_loc,
        context.tokens.previous_end_loc(),
    );
    Ok(EnumDefinition {
        attributes,
        loc,
        abilities,
        name,
        type_parameters,
        variants,
    })
}

// Parse an enum variant:
//      VariantDef = <DocComments> <VariantName> ("{" Comma<FieldAnnot> "}" | "(" Comma<Type> ")")?
fn parse_variant_def(context: &mut Context) -> Result<VariantDefinition, Box<Diagnostic>> {
    context.tokens.match_doc_comments();
    let start_loc = context.tokens.start_loc();
    let name = VariantName(parse_identifier(context)?);
    let fields = if context.tokens.peek() == Tok::LParen {
        VariantFields::Positional(parse_comma_list(
            context,
            Tok::LParen,
            Tok::RParen,
            parse_type,
            "a type",
        )?)
    } else {
        VariantFields::Named(parse_comma_list(
            context,
            Tok::LBrace,
            Tok::RBrace,
            parse_field_annot,
            "a field",
        )?)
    };
    let end_loc = context.tokens.previous_end_loc();
    Ok(VariantDefinition {
        loc: make_loc(context.tokens.file_hash(), start_loc, end_loc),
        name,
        fields,
    })
}

//**************************************************************************************************
// Constants
//**************************************************************************************************

// Parse a constant:
//      ConstantDecl = "const" <Identifier> ":" <Type> "=" <Exp> ";"
fn parse_constant_decl(
    attributes: Vec<Attributes>,
    start_loc: usize,
    modifiers: Modifiers,
    context: &mut Context,
) -> Result<Constant, Box<Diagnostic>> {
    let Modifiers {
        visibility,
        entry,
        native,
    } = modifiers;
    if let Some(vis) = visibility {
        let msg = "Invalid constant declaration. Constants cannot have visibility modifiers as \
                   they are always internal";
        context
            .env
            .add_diag(diag!(Syntax::InvalidModifier, (vis.loc().unwrap(), msg)));
    }
    if let Some(loc) = entry {
        let msg = format!(
            "Invalid constant declaration. '{}' is used only on functions",
            ENTRY_MODIFIER
        );
        context
            .env
            .add_diag(diag!(Syntax::InvalidModifier, (loc, msg)));
    }
    if let Some(loc) = native {
        let msg = "Invalid constant declaration. 'native' constants are not supported";
        context
            .env
            .add_diag(diag!(Syntax::InvalidModifier, (loc, msg)));
    }
    consume_token(context.tokens, Tok::Const)?;
    let name = ConstantName(parse_identifier(context)?);
    consume_token(context.tokens, Tok::Colon)?;
    let signature = parse_type(context)?;
    consume_token(context.tokens, Tok::Equal)?;
    let value = parse_exp(context)?;
    consume_token(context.tokens, Tok::Semicolon)?;
    let loc = make_loc(
        context.tokens.file_hash(),
        start_loc,
        context.tokens.previous_end_loc(),
    );
    Ok(Constant {
        attributes,
        loc,
        signature,
        name,
        value,
    })
}

//**************************************************************************************************
// AddressBlock
//**************************************************************************************************

// Parse an address block:
//      AddressBlock =
//          "address" <LeadingNameAccess> "{" (<Attributes> <Module>)* "}"
//
// Note that "address" is not a token.
fn parse_address_block(
    attributes: Vec<Attributes>,
    context: &mut Context,
) -> Result<AddressDefinition, Box<Diagnostic>> {
    const UNEXPECTED_TOKEN: &str = "Invalid code unit. Expected 'address', 'module', or 'script'";
    if context.tokens.peek() != Tok::Identifier {
        let start = context.tokens.start_loc();
        let end = start + context.tokens.content().len();
        let loc = make_loc(context.tokens.file_hash(), start, end);
        let msg = format!(
            "{}. Got {}",
            UNEXPECTED_TOKEN,
            current_token_error_string(context.tokens)
        );
        return Err(Box::new(diag!(Syntax::UnexpectedToken, (loc, msg))));
    }
    let addr_name = parse_identifier(context)?;
    if addr_name.value.as_str() != "address" {
        let msg = format!("{}. Got '{}'", UNEXPECTED_TOKEN, addr_name.value);
        return Err(Box::new(diag!(
            Syntax::UnexpectedToken,
            (addr_name.loc, msg)
        )));
    }
    let start_loc = context.tokens.start_loc();
    let addr = parse_leading_name_access(context, false)?;
    let end_loc = context.tokens.previous_end_loc();
    let loc = make_loc(context.tokens.file_hash(), start_loc, end_loc);

    let modules = match context.tokens.peek() {
        Tok::LBrace => {
            context.tokens.advance()?;
            let mut modules = vec![];
            while context.tokens.peek() != Tok::RBrace {
                let attributes = parse_attributes(context)?;
                modules.push(parse_module(attributes, context)?);
            }
            consume_token(context.tokens, Tok::RBrace)?;
            modules
        }
        _ => return Err(unexpected_token_error(context.tokens, "'{'")),
    };

    Ok(AddressDefinition {
        attributes,
        loc,
        addr,
        modules,
    })
}

//**************************************************************************************************
// Modules
//**************************************************************************************************

// Parse a use declaration:
//      UseDecl =
//          "use" <ModuleIdent> <UseAlias> ";" |
//          "use" <ModuleIdent> :: <UseMember> ";" |
//          "use" <ModuleIdent> :: "{" Comma<UseMember> "}" ";"
fn parse_use_decl(
    attributes: Vec<Attributes>,
    context: &mut Context,
) -> Result<UseDecl, Box<Diagnostic>> {
    let start_loc = context.tokens.start_loc();
    consume_token(context.tokens, Tok::Use)?;
    let ident = parse_module_ident(context)?;
    let alias_opt = parse_use_alias(context)?;
    let use_ = match (&alias_opt, context.tokens.peek()) {
        (None, Tok::ColonColon) => {
            consume_token(context.tokens, Tok::ColonColon)?;
            let sub_uses = match context.tokens.peek() {
                Tok::LBrace => parse_comma_list(
                    context,
                    Tok::LBrace,
                    Tok::RBrace,
                    parse_use_member,
                    "a module member alias",
                )?,
                _ => vec![parse_use_member(context)?],
            };
            Use::ModuleUse(ident, ModuleUse::Members(sub_uses))
        }
        _ => Use::ModuleUse(ident, ModuleUse::Module(alias_opt.map(ModuleName))),
    };
    consume_token(context.tokens, Tok::Semicolon)?;
    let loc = make_loc(
        context.tokens.file_hash(),
        start_loc,
        context.tokens.previous_end_loc(),
    );
    Ok(UseDecl {
        loc,
        attributes,
        use_,
    })
}

// Parse an alias for a module member:
//      UseMember = <Identifier> <UseAlias>
fn parse_use_member(context: &mut Context) -> Result<(Name, Option<Name>), Box<Diagnostic>> {
    let member = parse_identifier(context)?;
    let alias_opt = parse_use_alias(context)?;
    Ok((member, alias_opt))
}

// Parse an 'as' use alias:
//      UseAlias = ("as" <Identifier>)?
fn parse_use_alias(context: &mut Context) -> Result<Option<Name>, Box<Diagnostic>> {
    Ok(if context.tokens.peek() == Tok::As {
        context.tokens.advance()?;
        Some(parse_identifier(context)?)
    } else {
        None
    })
}

// Parse a module:
//      Module =
//          <DocComments> ( "spec" | "module") (<LeadingNameAccess>::)?<ModuleName> "{"
//              ( <Attributes>
//                  ( <UseDecl> | <FriendDecl> | <SpecBlock> |
//                    <DocComments> <ModuleMemberModifiers>
//                        (<ConstantDecl> | <StructDecl> | <FunctionDecl>) )
//                  )
//              )*
//          "}"
fn parse_module(
    attributes: Vec<Attributes>,
    context: &mut Context,
) -> Result<ModuleDefinition, Box<Diagnostic>> {
    context.tokens.match_doc_comments();
    let start_loc = context.tokens.start_loc();

    let is_spec_module = if context.tokens.peek() == Tok::Spec {
        context.tokens.advance()?;
        true
    } else {
        consume_token(context.tokens, Tok::Module)?;
        false
    };
    let sp!(n1_loc, n1_) = parse_leading_name_access(context, false)?;
    let (address, name) = match (n1_, context.tokens.peek()) {
        (addr_ @ LeadingNameAccess_::AnonymousAddress(_), _)
        | (addr_ @ LeadingNameAccess_::GlobalAddress(_), _)
        | (addr_ @ LeadingNameAccess_::Name(_), Tok::ColonColon) => {
            let addr = sp(n1_loc, addr_);
            consume_token(context.tokens, Tok::ColonColon)?;
            let name = parse_module_name(context)?;
            (Some(addr), name)
        }
        (LeadingNameAccess_::Name(name), _) => (None, ModuleName(name)),
    };
    consume_token(context.tokens, Tok::LBrace)?;

    let mut members = vec![];
    while context.tokens.peek() != Tok::RBrace {
        members.push({
            let attributes = parse_attributes(context)?;
            match context.tokens.peek() {
                // Regular move constructs
                Tok::Use => ModuleMember::Use(parse_use_decl(attributes, context)?),
                _ => {
                    context.tokens.match_doc_comments();
                    let start_loc = context.tokens.start_loc();
                    let modifiers = parse_module_member_modifiers(context)?;
                    match context.tokens.peek() {
                        Tok::Const => ModuleMember::Constant(parse_constant_decl(
                            attributes, start_loc, modifiers, context,
                        )?),
                        Tok::Fun => ModuleMember::Function(parse_function_decl(
                            attributes, start_loc, modifiers, context,
                        )?),
                        Tok::Struct => ModuleMember::Struct(parse_struct_decl(
                            attributes, start_loc, modifiers, context,
                        )?),
                        Tok::Enum => ModuleMember::Enum(parse_enum_decl(
                            attributes, start_loc, modifiers, context,
                        )?),
                        _ => {
                            return Err(unexpected_token_error(
                                context.tokens,
                                &format!(
                                    "a module member: '{}', '{}', '{}', '{}', or '{}'",
                                    Tok::Use,
                                    Tok::Const,
                                    Tok::Fun,
                                    Tok::Struct,
                                    Tok::Enum
                                ),
                            ))
                        }
                    }
                }
            }
        })
    }
    consume_token(context.tokens, Tok::RBrace)?;
    let loc = make_loc(
        context.tokens.file_hash(),
        start_loc,
        context.tokens.previous_end_loc(),
    );
    let def = ModuleDefinition {
        attributes,
        loc,
        address,
        name,
        is_spec_module,
        members,
    };

    Ok(def)
}

//**************************************************************************************************
// File
//**************************************************************************************************

// Parse a file:
//      File =
//          (<Attributes> (<AddressBlock> | <Module> | <Script>))*
fn parse_file(context: &mut Context) -> Result<Vec<Definition>, Box<Diagnostic>> {
    let mut defs = vec![];
    while context.tokens.peek() != Tok::EOF {
        let attributes = parse_attributes(context)?;
        defs.push(match context.tokens.peek() {
            Tok::Spec | Tok::Module => Definition::Module(parse_module(attributes, context)?),
            _ => Definition::Address(parse_address_block(attributes, context)?),
        })
    }
    Ok(defs)
}

/// Parse the `input` string as a file of Move source code and return the
/// result as either a pair of FileDefinition and doc comments or some Diagnostics. The `file` name
/// is used to identify source locations in error messages.
pub fn parse_file_string(
    env: &mut CompilationEnv,
    file_hash: FileHash,
    input: &str,
) -> Result<(Vec<Definition>, MatchedFileCommentMap), Diagnostics> {
    let mut tokens = Lexer::new(input, file_hash, Edition::E2024_BETA);
    match tokens.advance() {
        Err(err) => Err(Diagnostics::from(vec![*err])),
        Ok(..) => Ok(()),
    }?;
    match parse_file(&mut Context::new(env, &mut tokens)) {
        Err(err) => Err(Diagnostics::from(vec![*err])),
        Ok(def) => Ok((def, tokens.check_and_get_doc_comments(env))),
    }
}
