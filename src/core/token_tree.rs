// Copyright 2024 IOTA Stiftung
// SPDX-License-Identifier: Apache-2.0

// Copyright © Aptos Foundation
// Copyright (c) The BitsLab.MoveBit Contributors
// SPDX-License-Identifier: Apache-2.0

use core::panic;
use std::{cmp::Ordering, collections::HashSet};

use move_compiler::{
    parser::{
        ast::{Definition, *},
        lexer::{Lexer, Tok},
    },
    shared::Identifier,
};

#[derive(Clone, Copy, PartialEq, Eq, Debug, serde::Serialize)]
pub enum NestKind {
    /// ()
    ParentTheses,
    /// []  
    Bracket,
    /// {}
    Brace,
    /// type parameter like  A<B>
    Type,
    /// lambda like |a , b|
    Lambda,
}

#[derive(Clone, Copy, serde::Serialize, Debug)]
pub struct NestData {
    pub kind: NestKind,
    pub start_pos: u32,
    pub end_pos: u32,
}

impl NestData {
    pub fn start_token_tree(&self) -> TokenTree {
        TokenTree::Simple(SimpleToken {
            content: self.kind.start_tok().to_string(),
            pos: self.start_pos,
            tok: self.kind.start_tok(),
            note: None,
        })
    }

    pub fn end_token_tree(&self) -> TokenTree {
        TokenTree::Simple(SimpleToken {
            content: self.kind.end_tok().to_string(),
            pos: self.end_pos,
            tok: self.kind.end_tok(),
            note: None,
        })
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Delimiter {
    Semicolon,
    Comma,
}

impl Delimiter {
    pub fn to_static_str(self) -> &'static str {
        match self {
            Delimiter::Semicolon => ";",
            Delimiter::Comma => ",",
        }
    }
}
impl NestKind {
    pub fn is_nest_start(tok: Tok) -> Option<NestKind> {
        match tok {
            Tok::LParen => Some(Self::ParentTheses),
            Tok::LBracket => Some(Self::Bracket),
            Tok::LBrace => Some(Self::Brace),
            Tok::Less => Some(Self::Type),
            Tok::Pipe => Some(Self::Lambda),
            _ => None,
        }
    }

    pub const fn start_tok(self) -> Tok {
        match self {
            NestKind::ParentTheses => Tok::LParen,
            NestKind::Bracket => Tok::LBracket,
            NestKind::Brace => Tok::LBrace,
            NestKind::Type => Tok::Less,
            NestKind::Lambda => Tok::Pipe,
        }
    }

    pub fn end_tok(self) -> Tok {
        match self {
            NestKind::ParentTheses => Tok::RParen,
            NestKind::Bracket => Tok::RBracket,
            NestKind::Brace => Tok::RBrace,
            NestKind::Type => Tok::Greater,
            NestKind::Lambda => Tok::Pipe,
        }
    }
}

#[derive(Clone, serde::Serialize)]
pub enum TokenTree {
    Simple(SimpleToken),
    Nested(NestedToken),
}

#[derive(Clone, serde::Serialize)]
pub struct SimpleToken {
    pub content: String,
    #[serde(skip_serializing)]
    pub pos: u32, // start offset in file buffer.
    #[serde(skip_serializing)]
    pub tok: Tok,
    #[serde(skip_serializing)]
    pub note: Option<Note>,
}

#[derive(Clone, serde::Serialize)]
pub struct NestedToken {
    pub elements: Vec<TokenTree>,
    pub data: NestData,
    #[serde(skip_serializing)]
    pub note: Option<Note>,
}

#[derive(Clone, Copy, PartialEq, Eq, Default)]
pub enum Note {
    /// binary op like `+` , `*`
    BinaryOP,
    /// This is a struct definition.
    StructDefinition,
    /// This is an enum definition.
    EnumDefinition,
    /// This is a function body.
    FunBody,
    /// This is a name in an `apply` statement.
    ApplyName,
    /// This is a address that contains modules.
    ModuleAddress,
    /// default
    #[default]
    Unknown,
}

impl Default for TokenTree {
    fn default() -> Self {
        Self::Simple(Default::default())
    }
}

impl Default for SimpleToken {
    fn default() -> Self {
        SimpleToken {
            content: Default::default(),
            pos: 0,
            tok: Tok::EOF,
            note: None,
        }
    }
}

pub trait TokenTreeInfo {
    fn note(&self) -> Option<Note>;

    fn start_token(&self) -> Tok;

    fn end_token(&self) -> Tok;

    fn end_pos(&self) -> u32;

    fn is_pound(&self) -> bool {
        self.token() == Some(Tok::NumSign)
    }

    fn token(&self) -> Option<Tok> {
        None
    }

    fn content(&self) -> Option<&str> {
        None
    }

    fn as_simple(&self) -> Option<&SimpleToken> {
        None
    }

    fn as_nested(&self) -> Option<&NestedToken> {
        None
    }
}

impl TokenTreeInfo for SimpleToken {
    fn note(&self) -> Option<Note> {
        self.note
    }

    fn start_token(&self) -> Tok {
        self.tok
    }

    fn end_token(&self) -> Tok {
        self.tok
    }

    fn end_pos(&self) -> u32 {
        self.pos + self.content.len() as u32
    }

    fn token(&self) -> Option<Tok> {
        Some(self.tok)
    }

    fn content(&self) -> Option<&str> {
        Some(&self.content)
    }

    fn as_simple(&self) -> Option<&SimpleToken> {
        Some(self)
    }
}

impl TokenTreeInfo for NestedToken {
    fn note(&self) -> Option<Note> {
        self.note
    }

    fn start_token(&self) -> Tok {
        self.data.kind.start_tok()
    }

    fn end_token(&self) -> Tok {
        self.data.kind.end_tok()
    }

    fn end_pos(&self) -> u32 {
        self.data.end_pos
    }

    fn as_nested(&self) -> Option<&NestedToken> {
        Some(self)
    }
}

impl TokenTreeInfo for TokenTree {
    fn note(&self) -> Option<Note> {
        match self {
            TokenTree::Simple(t) => t.note(),
            TokenTree::Nested(t) => t.note(),
        }
    }

    fn start_token(&self) -> Tok {
        match self {
            TokenTree::Simple(t) => t.start_token(),
            TokenTree::Nested(t) => t.start_token(),
        }
    }

    fn end_token(&self) -> Tok {
        match self {
            TokenTree::Simple(t) => t.end_token(),
            TokenTree::Nested(t) => t.end_token(),
        }
    }

    fn end_pos(&self) -> u32 {
        match self {
            TokenTree::Simple(t) => t.end_pos(),
            TokenTree::Nested(t) => t.end_pos(),
        }
    }

    fn token(&self) -> Option<Tok> {
        match self {
            TokenTree::Simple(t) => t.token(),
            TokenTree::Nested(t) => t.token(),
        }
    }

    fn content(&self) -> Option<&str> {
        match self {
            TokenTree::Simple(t) => t.content(),
            TokenTree::Nested(t) => t.content(),
        }
    }

    fn as_simple(&self) -> Option<&SimpleToken> {
        if let Self::Simple(t) = self { Some(t) } else { None }
    }

    fn as_nested(&self) -> Option<&NestedToken> {
        if let Self::Nested(t) = self { Some(t) } else { None }
    }
}

pub struct Parser<'a> {
    lexer: Lexer<'a>,
    defs: &'a Vec<Definition>,
    type_lambda_pair: Vec<(u32, u32)>,
    type_lambda_pair_index: usize,
    struct_definitions: Vec<(u32, u32)>,
    enum_definitions: Vec<(u32, u32)>,
    bin_op: HashSet<u32>,
    fun_body: HashSet<u32>, // start pos.
    apple_name: HashSet<u32>,
    address_module: Vec<(u32, u32)>,
    match_body: HashSet<u32>,
    match_arms: HashSet<u32>,
    patterns: HashSet<u32>,
    pattern_or: HashSet<u32>,
}

impl<'a> Parser<'a> {
    pub fn new(lexer: Lexer<'a>, defs: &'a Vec<Definition>) -> Self {
        let mut x = Self {
            lexer,
            defs,
            type_lambda_pair: Default::default(),
            type_lambda_pair_index: 0,
            struct_definitions: Vec::new(),
            enum_definitions: Vec::new(),
            bin_op: Default::default(),
            fun_body: Default::default(),
            apple_name: Default::default(),
            address_module: Vec::new(),
            match_arms: Default::default(),
            match_body: Default::default(),
            patterns: Default::default(),
            pattern_or: Default::default(),
        };
        x.collect_various_information();
        x
    }
}

impl<'a> Parser<'a> {
    fn add_simple_note(&self, pos: u32) -> Option<Note> {
        if self.bin_op.contains(&pos) {
            return Some(Note::BinaryOP);
        }
        if self.apple_name.contains(&pos) {
            return Some(Note::ApplyName);
        }
        None
    }

    pub fn parse_tokens(mut self) -> Vec<TokenTree> {
        let mut ret = Vec::new();
        self.lexer.advance().unwrap();
        while self.lexer.peek() != Tok::EOF {
            if let Some(kind) = self.is_nest_start() {
                ret.push(self.parse_nested(kind));
                continue;
            }
            ret.push(TokenTree::Simple(SimpleToken {
                content: self.lexer.content().to_string(),
                pos: self.lexer.start_loc() as u32,
                tok: self.lexer.peek(),
                note: self.add_simple_note(self.lexer.start_loc() as u32),
            }));

            self.lexer.advance().unwrap();
        }
        ret
    }

    fn is_nest_start(&mut self) -> Option<NestKind> {
        let Some(nest_kind) = NestKind::is_nest_start(self.lexer.peek()) else {
            return None;
        };
        match nest_kind {
            NestKind::Type | NestKind::Lambda => {
                let pos = self.lexer.start_loc() as u32;
                // try drop
                for (_, end) in &self.type_lambda_pair[self.type_lambda_pair_index..] {
                    if end < &pos {
                        self.type_lambda_pair_index += 1;
                    } else {
                        break;
                    }
                }

                if let Some((start, end)) = self.type_lambda_pair[self.type_lambda_pair_index..].iter().next() {
                    if &pos >= start && &pos <= end {
                        return Some(nest_kind);
                    } else {
                        return None;
                    }
                }
                None
            }
            _ => Some(nest_kind),
        }
    }

    fn parse_nested(&mut self, kind: NestKind) -> TokenTree {
        debug_assert!(self.lexer.peek() == kind.start_tok());
        let start = self.lexer.start_loc() as u32;
        self.lexer.advance().unwrap();
        let mut ret = Vec::new();
        let note = if self.struct_definitions.iter().any(|x| x.0 <= start && x.1 >= start) && kind == NestKind::Brace {
            Some(Note::StructDefinition)
        } else if self.enum_definitions.iter().any(|x| x.0 <= start && x.1 >= start) && kind == NestKind::Brace {
            Some(Note::EnumDefinition)
        } else if self.fun_body.contains(&start) {
            Some(Note::FunBody)
        } else if self
            .address_module
            .iter()
            .any(|(addr, modname)| *addr < start && start < *modname)
        {
            Some(Note::ModuleAddress)
        } else {
            None
        };

        while self.lexer.peek() != Tok::EOF {
            if self.lexer.peek() == kind.end_tok() {
                break;
            }
            if let Some(kind) = self.is_nest_start() {
                ret.push(self.parse_nested(kind));
                continue;
            }
            if kind == NestKind::Type && self.lexer.peek() == Tok::GreaterGreater {
                self.adjust_token(Tok::Greater);
                break;
            }
            ret.push(TokenTree::Simple(SimpleToken {
                content: self.lexer.content().to_owned(),
                pos: self.lexer.start_loc() as u32,
                tok: self.lexer.peek(),
                note: self.add_simple_note(self.lexer.start_loc() as u32),
            }));
            self.lexer.advance().unwrap();
        }
        debug_assert_eq!(self.lexer.peek(), kind.end_tok());
        let end = self.lexer.start_loc() as u32;
        self.lexer.advance().unwrap();
        TokenTree::Nested(NestedToken {
            elements: ret,
            data: NestData {
                kind,
                start_pos: start,
                end_pos: end,
            },
            note,
        })
    }
}

impl<'a> Parser<'a> {
    // While parsing a list and expecting a ">" token to mark the end, replace
    // a ">>" token with the expected ">". This handles the situation where there
    // are nested type parameters that result in two adjacent ">" tokens, e.g.,
    // "A<B<C>>".
    fn adjust_token(&mut self, end_token: Tok) {
        if self.lexer.peek() == Tok::GreaterGreater && end_token == Tok::Greater {
            self.lexer.replace_token(Tok::Greater, 1);
        }
    }
}

impl<'a> Parser<'a> {
    fn collect_various_information(&mut self) {
        for d in self.defs.iter() {
            collect_definition(self, d);
        }
        self.type_lambda_pair.iter().for_each(|x| debug_assert!(x.0 <= x.1));

        self.type_lambda_pair.sort_by(|x, y| {
            debug_assert!(x.0.cmp(&y.0) != Ordering::Equal, "{:?}?{:?}", x, y);
            if x.0.cmp(&y.0) == Ordering::Greater {
                Ordering::Greater
            } else {
                x.1.cmp(&y.1)
            }
        });

        fn collect_definition(p: &mut Parser, d: &Definition) {
            match d {
                Definition::Module(x) => collect_module(p, x),
                Definition::Address(addr) => {
                    for x in addr.modules.iter() {
                        p.address_module.push((addr.loc.start(), x.loc.start()));
                        collect_module(p, x);
                    }
                }
            }
        }

        fn collect_module(p: &mut Parser, d: &ModuleDefinition) {
            for m in d.members.iter() {
                match &m {
                    ModuleMember::Function(x) => collect_function(p, x),
                    ModuleMember::Struct(x) => collect_struct(p, x),
                    ModuleMember::Enum(e) => collect_enum(p, e),
                    ModuleMember::Use(_) => {}
                    ModuleMember::Friend(_) => {}
                    ModuleMember::Constant(x) => {
                        collect_const(p, x);
                    }
                    ModuleMember::Spec(_) => {}
                }
            }
        }

        fn collect_struct(p: &mut Parser, s: &StructDefinition) {
            p.type_lambda_pair.push((s.loc.start(), s.loc.end()));
            p.struct_definitions.push((s.loc.start(), s.loc.end()));
        }

        fn collect_enum(p: &mut Parser, e: &EnumDefinition) {
            p.type_lambda_pair.push((e.loc.start(), e.loc.end()));
            p.enum_definitions.push((e.loc.start(), e.loc.end()));
        }

        fn collect_seq_item(p: &mut Parser, s: &SequenceItem) {
            match &s.value {
                SequenceItem_::Seq(e) => collect_expr(p, e),
                SequenceItem_::Declare(_, ty) => {
                    if let Some(ty) = ty {
                        collect_ty(p, ty);
                    }
                }
                SequenceItem_::Bind(_, ty, e) => {
                    if let Some(ty) = ty {
                        collect_ty(p, ty);
                    }
                    collect_expr(p, e);
                }
            }
        }
        fn collect_seq(p: &mut Parser, s: &Sequence) {
            for s in s.1.iter() {
                collect_seq_item(p, s);
            }
            if let Some(t) = s.3.as_ref() {
                collect_expr(p, t);
            }
        }

        fn collect_expr(p: &mut Parser, e: &Exp) {
            match &e.value {
                Exp_::Value(_) => {}
                Exp_::Move(_, _) => {}
                Exp_::Copy(_, _) => {}
                Exp_::Name(name) => {
                    p.type_lambda_pair.push((name.loc.end(), e.loc.end()));
                }
                Exp_::Call(name, es) => {
                    p.type_lambda_pair.push((name.loc.end(), es.loc.start()));
                    es.value.iter().for_each(|e| collect_expr(p, e));
                }
                Exp_::DotCall(e, name, _, _, es) => {
                    collect_expr(p, e);
                    p.type_lambda_pair.push((name.loc.end(), es.loc.start()));
                    es.value.iter().for_each(|e| collect_expr(p, e));
                }
                Exp_::Pack(name, es) => {
                    if let Some(e) = es.first() {
                        p.type_lambda_pair.push((name.loc.end(), e.0.loc().start()));
                    }
                    es.iter().for_each(|e| collect_expr(p, &e.1));
                }
                Exp_::Vector(name_loc, _, es) => {
                    p.type_lambda_pair.push((name_loc.end(), es.loc.start()));
                    es.value.iter().for_each(|e| collect_expr(p, e));
                }
                Exp_::IfElse(condition, then_, else_) => {
                    collect_expr(p, condition);
                    collect_expr(p, then_);
                    if let Some(else_) = else_ {
                        collect_expr(p, else_);
                    }
                }
                Exp_::While(e, then_) => {
                    collect_expr(p, e);
                    collect_expr(p, then_);
                }
                Exp_::Loop(b) => {
                    collect_expr(p, b);
                }
                Exp_::Match(e, arms) => {
                    collect_expr(p, e);
                    p.match_body.insert(arms.loc.start());
                    for arm in &arms.value {
                        p.match_arms.insert(arm.loc.start());
                        if let Some(guard) = &arm.value.guard {
                            collect_expr(p, guard);
                        }
                        collect_match_pattern(p, &arm.value.pattern);
                        collect_expr(p, &arm.value.rhs);
                    }
                }
                Exp_::Block(b) => collect_seq(p, b),

                Exp_::Lambda(b, _, e) => {
                    p.type_lambda_pair.push((b.loc.start(), b.loc.end()));
                    collect_expr(p, e);
                }
                Exp_::Quant(_, _, es, e1, e2) => {
                    es.iter().for_each(|e| {
                        for e in e.iter() {
                            collect_expr(p, e)
                        }
                    });
                    if let Some(t) = e1 {
                        collect_expr(p, t);
                    }
                    collect_expr(p, e2);
                }
                Exp_::ExpList(es) => {
                    es.iter().for_each(|e| collect_expr(p, e));
                }
                Exp_::Unit => {}
                Exp_::Parens(e) => {
                    collect_expr(p, e);
                }
                Exp_::Assign(l, r) => {
                    collect_expr(p, l);
                    collect_expr(p, r);
                }
                Exp_::Return(_, e) => {
                    if let Some(t) = e {
                        collect_expr(p, t);
                    }
                }
                Exp_::Abort(e) => {
                    collect_expr(p, e);
                }
                Exp_::Break(_, e) => {
                    if let Some(t) = e {
                        collect_expr(p, t);
                    }
                }
                Exp_::Continue(_) => {}
                Exp_::Labeled(_, e) => {
                    collect_expr(p, e);
                }
                Exp_::Dereference(e) => {
                    collect_expr(p, e);
                }
                Exp_::UnaryExp(_, e) => {
                    collect_expr(p, e);
                }
                Exp_::BinopExp(l, op, r) => {
                    p.bin_op.insert(op.loc.start());
                    collect_expr(p, l);
                    collect_expr(p, r);
                }
                Exp_::Borrow(_, e) => {
                    collect_expr(p, e);
                }
                Exp_::Dot(e, _) => {
                    collect_expr(p, e);
                }
                Exp_::Index(e, i) => {
                    collect_expr(p, e);
                    for e in &i.value {
                        collect_expr(p, e);
                    }
                }
                Exp_::Cast(e, ty) => {
                    collect_expr(p, e);
                    collect_ty(p, ty);
                }
                Exp_::Annotate(e, ty) => {
                    collect_expr(p, e);
                    collect_ty(p, ty);
                }
                Exp_::Spec(_) => {}
                Exp_::UnresolvedError => {
                    unreachable!()
                }
            }
        }

        fn collect_match_pattern(p: &mut Parser, m: &MatchPattern) {
            p.patterns.insert(m.loc.start());
            match &m.value {
                MatchPattern_::PositionalConstructor(_, patterns) => {
                    for e in &patterns.value {
                        match e {
                            Ellipsis::Binder(m) => collect_match_pattern(p, m),
                            Ellipsis::Ellipsis(_) => (),
                        }
                    }
                }
                MatchPattern_::FieldConstructor(_, patterns) => {
                    for e in &patterns.value {
                        match e {
                            Ellipsis::Binder((_, m)) => collect_match_pattern(p, m),
                            Ellipsis::Ellipsis(_) => (),
                        }
                    }
                }
                MatchPattern_::Name(_, _) => (),
                MatchPattern_::Literal(_) => (),
                MatchPattern_::Or(m1, m2) => {
                    p.pattern_or.insert(m1.loc.end());
                    collect_match_pattern(p, m1);
                    collect_match_pattern(p, m2);
                }
                MatchPattern_::At(_, m) => {
                    collect_match_pattern(p, m);
                }
            }
        }

        fn collect_const(p: &mut Parser, c: &Constant) {
            collect_ty(p, &c.signature);
            collect_expr(p, &c.value);
        }

        fn collect_function(p: &mut Parser, d: &Function) {
            p.type_lambda_pair.push((
                d.name.0.loc.start(),
                match &d.body.value {
                    FunctionBody_::Defined(_x) => d.body.loc.start(),
                    FunctionBody_::Native => d.loc.end(),
                },
            ));

            match &d.body.value {
                FunctionBody_::Defined(s) => {
                    p.fun_body.insert(d.body.loc.start());
                    collect_seq(p, s);
                }
                FunctionBody_::Native => {}
            }
        }

        fn collect_ty(p: &mut Parser, ty: &Type) {
            p.type_lambda_pair.push((ty.loc.start(), ty.loc.end()))
        }
    }
}

fn analyzer_token_tree_length_(ret: &mut usize, token_tree: &TokenTree, max: usize) {
    match token_tree {
        TokenTree::Simple(SimpleToken { content, .. }) => {
            *ret += content.len();
        }
        TokenTree::Nested(NestedToken { elements, .. }) => {
            for t in elements.iter() {
                analyzer_token_tree_length_(ret, t, max);
                if *ret > max {
                    return;
                }
            }
            *ret += 2; // for delimiter.
        }
    }
}

/// analyzer How long is list of token_tree
pub(crate) fn analyze_token_tree_length(token_tree: &[TokenTree], max: usize) -> usize {
    let mut ret = usize::default();
    for t in token_tree.iter() {
        analyzer_token_tree_length_(&mut ret, t, max);
        if ret > max {
            return ret;
        }
    }
    ret
}

// ===================================================================================================
#[derive(Default, Debug)]
pub struct CommentExtractor {
    pub comments: Vec<Comment>,
}

#[derive(Debug)]
pub struct Comment {
    pub start_offset: u32,
    pub content: String,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum CommentKind {
    /// "//"
    InlineComment,
    /// "///"
    DocComment,
    /// "/**/"
    BlockComment,
}

/// A comment extractor to extract all comment from move file
/// include the start and end tokens `//`,`*/`,etc.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CommentExtractorErr {
    NewLineInQuote,
    NotTerminalState(ExtractorCommentState),
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ExtractorCommentState {
    /// init state
    Init,
    /// `/` has been seen,maybe a comment.
    OneSlash,
    /// `///` has been seen,inline comment.
    InlineComment,
    /// `/*` has been seen,block comment.
    BlockComment,
    /// in state `BlockComment`,`*` has been seen,maybe exit the `BlockComment`.
    OneStar,
    /// `"` has been seen.
    Quote,
}

impl CommentExtractor {
    pub fn new(content: &str) -> Result<Self, CommentExtractorErr> {
        if content.len() <= 1 {
            return Ok(Self::default());
        }
        let content = content.as_bytes();

        let mut state = ExtractorCommentState::Init;
        const NEW_LINE: u8 = 10;
        const SLASH: u8 = 47;
        const STAR: u8 = 42;
        const BLACK_SLASH: u8 = 92;
        const QUOTE: u8 = 34;
        let mut depth = 0;
        let mut comments = Vec::new();
        let mut comment = Vec::new();
        let last_index = content.len() - 1;
        let mut index = 0;

        macro_rules! make_comment {
            () => {
                comments.push(Comment {
                    start_offset: (index as u32) + 1 - (comment.len() as u32),
                    content: String::from_utf8(comment.clone()).unwrap(),
                });
                comment.clear();

                if state == ExtractorCommentState::InlineComment {
                    if depth == 0 {
                        state = ExtractorCommentState::Init;
                    } else {
                        state = ExtractorCommentState::BlockComment;
                    }
                } else {
                    if depth <= 1 {
                        depth = 0;
                        state = ExtractorCommentState::Init;
                    } else {
                        depth -= 1;
                        state = ExtractorCommentState::BlockComment;
                    }
                }
            };
        }
        // tracing::info!("xxxx:{}", content.len());
        while index <= last_index {
            let c = content.get(index).unwrap();
            // tracing::info!(
            //     "index:{} state:{:?} c:{:?} last:{}",
            //     index, state, *c as char, last_index
            // );
            match state {
                ExtractorCommentState::Init => match *c {
                    SLASH => {
                        state = ExtractorCommentState::OneSlash;
                    }
                    QUOTE => {
                        state = ExtractorCommentState::Quote;
                    }
                    _ => {}
                },
                ExtractorCommentState::OneSlash => {
                    if *c == SLASH {
                        comment.push(SLASH);
                        comment.push(SLASH);
                        if depth == 0 {
                            state = ExtractorCommentState::InlineComment;
                        } else {
                            state = ExtractorCommentState::BlockComment;
                        }
                    } else if *c == STAR {
                        comment.push(SLASH);
                        comment.push(STAR);
                        depth += 1;
                        state = ExtractorCommentState::BlockComment;
                    } else if depth == 0 {
                        state = ExtractorCommentState::Init;
                    } else {
                        state = ExtractorCommentState::BlockComment;
                    }
                }
                ExtractorCommentState::BlockComment => {
                    if *c == STAR {
                        state = ExtractorCommentState::OneStar;
                    } else if *c == SLASH {
                        state = ExtractorCommentState::OneSlash;
                    } else {
                        comment.push(*c);
                    }
                }
                ExtractorCommentState::OneStar => {
                    if *c == SLASH {
                        comment.push(STAR);
                        comment.push(SLASH);
                        make_comment!();
                    } else if *c == STAR {
                        comment.push(STAR);
                    } else {
                        comment.push(STAR);
                        comment.push(*c);
                        state = ExtractorCommentState::BlockComment;
                    }
                }
                ExtractorCommentState::InlineComment => {
                    if *c == NEW_LINE || index == last_index {
                        if *c != NEW_LINE {
                            comment.push(*c);
                        }
                        make_comment!();
                    } else {
                        comment.push(*c);
                    }
                }
                ExtractorCommentState::Quote => {
                    // handle \" or handle \\
                    if *c == BLACK_SLASH
                        && content
                            .get(index + 1)
                            .map(|x| *x == QUOTE || *x == BLACK_SLASH)
                            .unwrap_or(false)
                    {
                        index += 2;
                        continue;
                    } else if *c == QUOTE {
                        state = ExtractorCommentState::Init;
                    } else if *c == NEW_LINE {
                        // return Err(CommentExtractorErr::NewLineInQuote);
                        panic!("1")
                    }
                }
            };
            index += 1;
        }
        if state != ExtractorCommentState::Init {
            return Err(CommentExtractorErr::NotTerminalState(state));
        }
        Ok(Self { comments })
    }
}

#[cfg(test)]
mod comment_test {
    use std::collections::BTreeMap;

    use move_command_line_common::files::FileHash;
    use move_compiler::{editions::Edition, shared::CompilationEnv, Flags};

    use super::*;
    use crate::tools::syntax::parse_file_string;
    #[test]
    fn token_tree_to_json() {
        let content = r#"module 0x1::xxx{
            public entry fun object_vec(msg: String, objs: vector<Object<ModuleData>>) acquires ModuleData {
                vector::for_each(objs,|o| {  });
            }
          }"#;
        let filehash = FileHash::empty();
        let attrs = BTreeMap::new();
        let mut env = CompilationEnv::new(Flags::testing(), Vec::new(), attrs, None);
        let (defs, _) = parse_file_string(&mut env, filehash, content).unwrap();
        let lexer = Lexer::new(content, filehash, Edition::DEVELOPMENT);
        let parse = Parser::new(lexer, &defs);
        let token_tree = parse.parse_tokens();
        let s = serde_json::to_string(&token_tree).unwrap();
        // check this using some online json tool.
        tracing::info!("json:{}", s);
    }

    #[test]
    fn test_comment_extrator_ok() {
        let x = CommentExtractor::new(
            r#"
        // 111
    // 222
    fdfdf
    // bb
    /* ***** '" 1121 **/
    " \" // iii "
    "// fff"
    /// ggg
    b"\\"
        "#,
        )
        .unwrap();
        let v = ["// 111", "// 222", "// bb", "/* ***** '\" 1121 **/", "/// ggg"];
        for (c1, c2) in v.iter().zip(x.comments.iter()) {
            assert_eq!(*c1, c2.content.as_str());
        }
        assert_eq!(v.len(), x.comments.len());
    }
    #[test]
    fn test_comment_extrator_ok2() {
        let _x = CommentExtractor::new(r#"/* /* 1 */ */"#).unwrap();
    }

    #[test]
    fn test_comment_extractor_err() {
        let v = [
            (
                r#" \" "#,
                CommentExtractorErr::NotTerminalState(ExtractorCommentState::Quote),
            ),
            (
                r#" \" 
                "#,
                CommentExtractorErr::NewLineInQuote,
            ),
            (
                r#" /*  "#,
                CommentExtractorErr::NotTerminalState(ExtractorCommentState::BlockComment),
            ),
        ];

        for (c, err) in v.iter() {
            match CommentExtractor::new(c) {
                Ok(_) => unreachable!(),
                Err(x) => assert_eq!(x, *err),
            }
        }
    }
}
