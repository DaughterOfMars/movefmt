use move_compiler::parser::lexer::Tok;
use crate::core::token_tree::{Note, TokenTree, NestKind_};

pub enum TokType {
    /// abc like token,
    Alphabet,
    /// + - ...
    MathSign,
    ///
    Sign,
    // specials no need space at all.
    NoNeedSpace,
    /// numbers 0x1 ...
    Number,
    /// b"hello world"
    String,
    /// &
    Amp,
    /// *
    Star,
    /// &mut
    AmpMut,
    ///
    Semicolon,
    ///:
    Colon,
    /// @
    AtSign,
    /// <
    Less,
}

impl From<Tok> for TokType {
    fn from(value: Tok) -> Self {
        match value {
            Tok::EOF => unreachable!(), // EOF not in `TokenTree`.
            Tok::NumValue => TokType::Number,
            Tok::NumTypedValue => TokType::Number,
            Tok::ByteStringValue => TokType::String,
            Tok::Exclaim => TokType::Sign,
            Tok::ExclaimEqual => TokType::MathSign,
            Tok::Percent => TokType::MathSign,
            Tok::Amp => TokType::Amp,
            Tok::AmpAmp => TokType::MathSign,
            Tok::LParen => TokType::Sign,
            Tok::RParen => TokType::Sign,
            Tok::LBracket => TokType::Sign,
            Tok::RBracket => TokType::Sign,
            Tok::Star => TokType::Star,
            Tok::Plus => TokType::MathSign,
            Tok::Comma => TokType::Sign,
            Tok::Minus => TokType::MathSign,
            Tok::Period => TokType::NoNeedSpace,
            Tok::PeriodPeriod => TokType::NoNeedSpace,
            Tok::Slash => TokType::Sign,
            Tok::Colon => TokType::Colon,
            Tok::ColonColon => TokType::NoNeedSpace,
            Tok::Semicolon => TokType::Semicolon,
            Tok::Less => TokType::Less,
            Tok::LessEqual => TokType::MathSign,
            Tok::LessLess => TokType::MathSign,
            Tok::Equal => TokType::MathSign,
            Tok::EqualEqual => TokType::MathSign,
            Tok::EqualEqualGreater => TokType::MathSign,
            Tok::LessEqualEqualGreater => TokType::MathSign,
            Tok::Greater => TokType::MathSign,
            Tok::GreaterEqual => TokType::MathSign,
            Tok::GreaterGreater => TokType::MathSign,
            Tok::LBrace => TokType::Sign,
            Tok::Pipe => TokType::Sign,
            Tok::PipePipe => TokType::MathSign,
            Tok::RBrace => TokType::Sign,
            Tok::NumSign => TokType::Sign,
            Tok::AtSign => TokType::AtSign,
            Tok::AmpMut => TokType::Amp,
            _ => TokType::Alphabet,
        }
    }
}

fn get_start_tok(t: &TokenTree) -> Tok {
    match t {
        TokenTree::SimpleToken {
            content: _,
            pos: _,
            tok,
            note: _,
        } => tok.clone(),
        TokenTree::Nested {
            elements: _,
            kind,
            note: _,
        } => kind.kind.start_tok(),
    }
}


fn get_end_tok(t: &TokenTree) -> Tok {
    match t {
        TokenTree::SimpleToken {
            content: _,
            pos: _,
            tok,
            note: _,
        } => tok.clone(),
        TokenTree::Nested {
            elements: _,
            kind,
            note: _,
        } => kind.kind.end_tok(),
    }
}

fn is_to_or_except(token: &Option<&TokenTree>) -> bool {  
    match token {  
        None => false,  
        Some(TokenTree::SimpleToken { content: con, .. }) => con.as_str() == "to" || con.as_str() == "except",  
        _ => false,  
    }  
}

pub(crate) fn need_space(current: &TokenTree, next: Option<&TokenTree>) -> bool {
    if next.is_none() {
        return false;
    }

    // if let Tok::Identifier = get_start_tok(current) {
        if let TokenTree::SimpleToken{content, ..} = current {
            // eprintln!("need_space: content = {:?}", content);
            if content.contains("acquires") {
                eprintln!("need_space: content--acquires = {:?}, get_start_tok(current) = {:?}", content, get_start_tok(current));
            }
            if content.contains("reads") {
                eprintln!("need_space: content--reads = {:?}, get_start_tok(current) = {:?}", content, get_start_tok(current));
            }
            if content.contains("writes") {
                eprintln!("need_space: content--writes = {:?}, get_start_tok(current) = {:?}", content, get_start_tok(current));
            }
        }
    // }

    let _is_bin_current = current
        .get_note()
        .map(|x| x == Note::BinaryOP)
        .unwrap_or_default();

    let is_bin_next = match next {
        None => false,
        Some(next_) => next_
            .get_note()
            .map(|x| x == Note::BinaryOP)
            .unwrap_or_default(),
    };
    let is_apply_current = current
        .get_note()
        .map(|x| x == Note::ApplyName)
        .unwrap_or_default();

    let is_apply_next = match next {
        None => false,
        Some(next_) => next_
            .get_note()
            .map(|x| x == Note::ApplyName)
            .unwrap_or_default(),
    };

    let is_to_execpt = is_to_or_except(&Some(current)) || is_to_or_except(&next);

    return match (
        TokType::from(get_start_tok(current)),
        TokType::from(next.map(|x| get_start_tok(x)).unwrap()),
    ) {
        (TokType::Alphabet, TokType::Alphabet) => true,
        (TokType::MathSign, _) => true,
        (TokType::Sign, TokType::Alphabet) => {
            !(Tok::Exclaim == get_end_tok(current))
        },
        (TokType::Sign, TokType::Number) => true,
        (TokType::Sign, TokType::String | TokType::AtSign) => {
            let mut result = false;
            let mut next_tok = Tok::EOF;
            next.map(|x| {
                match x {
                    TokenTree::Nested {
                        elements: _,
                        kind,
                        note: _,
                    } => {
                        next_tok = kind.kind.start_tok();
                        // if kind.kind.start_tok() == Tok::LBrace {
                        //     result = true;
                        // }
                    },
                    TokenTree::SimpleToken {
                        content,
                        pos: _,
                        tok,
                        note: _,
                    } => {
                        next_tok = *tok;
                        println!("content = {:?}", content);                    
                        if Tok::ByteStringValue == *tok {
                            result = true;
                        }
                    }
                }
            });

            if Tok::Comma == get_start_tok(current) {
                if Tok::AtSign == next_tok {
                    result = true;
                }
                println!("after Comma, result = {}, next_tok = {:?}", result, next_tok);
            }
            result
        },
        (_, TokType::MathSign) => true,
        (TokType::Alphabet, TokType::String) => true,
        (TokType::Number, TokType::Alphabet) => true,
        (_, TokType::AmpMut) => true,
        (TokType::Colon, _) => true,
        (TokType::Alphabet, TokType::Number) => true,

        (_, TokType::Less) => {
            if is_bin_next {
                true
            } else {
                false
            }
        }
        (TokType::Less, TokType::Alphabet) => true,
        (TokType::Less, _) => false,

        (_, TokType::Amp) => {
            if is_bin_next {
                true
            } else {
                false
            }
        }

        (_, TokType::Star) => {
            let result = if is_bin_next || is_apply_next {
                if is_to_execpt {
                    true
                } else {
                    false
                }
            } else {
                false
            };
            result || 
            Tok::NumValue == get_start_tok(current) 
                   || Tok::NumTypedValue == get_start_tok(current)
                   || Tok::Acquires == get_start_tok(current)
                   || Tok::Identifier == get_start_tok(current)
                   || Tok::RParen == get_end_tok(current)
        }

        (TokType::Star, _) => {
            if is_bin_next {
                return true;
            }
            match next {
                None => {},
                Some(next_) => {
                    if let TokenTree::Nested{elements, ..} = next_ {
                        // if elements.len() > 0 {
                        //     elements[0]
                        //     .get_note()
                        //     .map(|x| x == Note::BinaryOP)
                        //     .unwrap_or_default()
                        // } else {
                        //     false
                        // }
                        if Tok::LParen == get_start_tok(next_) {
                            return elements.len() > 2    
                        }
                    }
                }
            }

            if is_apply_current {
                if is_to_execpt {
                    true
                } else {
                    false
                }
            } else {
                let mut result = false;
                let mut next_tok = Tok::EOF;
                next.map(|x| {
                    match x {
                        TokenTree::Nested {
                            elements: _,
                            kind,
                            note: _,
                        } => {
                            next_tok = kind.kind.start_tok();
                            if kind.kind == NestKind_::Brace {
                                result = true;
                            }
                        },
                        TokenTree::SimpleToken {
                            content,
                            pos: _,
                            tok,
                            note: _,
                        } => {
                            next_tok = *tok;
                            println!("content = {:?}", content);
                            if Tok::NumValue == *tok 
                            || Tok::NumTypedValue == *tok 
                            || Tok::Identifier == *tok
                            || Tok::LParen == *tok {
                                result = true;
                            }
                        }
                    }
                });
                result
            }
        }

        (TokType::AtSign, TokType::Alphabet) => false,
        (TokType::Alphabet | TokType::Number | TokType::Sign, TokType::Sign) => {
            let mut result = false;
            let mut next_tok = Tok::EOF;
            next.map(|x| {
                match x {
                    TokenTree::Nested {
                        elements: _,
                        kind,
                        note: _,
                    } => {
                        next_tok = kind.kind.start_tok();
                        if kind.kind.start_tok() == Tok::LBrace {
                            result = true;
                        }
                    },
                    TokenTree::SimpleToken {
                        content,
                        pos: _,
                        tok,
                        note: _,
                    } => {
                        next_tok = *tok;
                        println!("content = {:?}", content);
                        if Tok::Slash == *tok || Tok::LBrace == *tok {
                            result = true;
                        }
                    }
                }
            });
            if Tok::Let == get_start_tok(current) || 
               Tok::Slash == get_start_tok(current) || 
               Tok::If == get_start_tok(current) || 
               Tok::Else == get_start_tok(current) ||
               Tok::While == get_start_tok(current) {
                result = true;
            }

            if Tok::RParen == get_end_tok(current) && next_tok == Tok::Exclaim {
                result = true;
            }

            println!("result = {}, next_tok = {:?}", result, next_tok);
            result
        },
        _ => false,
    };
}
