// Copyright © Aptos Foundation
// Copyright (c) The BitsLab.MoveBit Contributors
// SPDX-License-Identifier: Apache-2.0

use std::{collections::BTreeMap, result::Result::*};

use commentfmt::{Config, Verbosity};
use move_command_line_common::files::FileHash;
use move_compiler::{
    diagnostics::Diagnostics,
    editions::Edition,
    parser::lexer::{Lexer, Tok as Token},
    shared::CompilationEnv,
    Flags,
};

use super::token_tree::{NestedToken, SimpleToken, TokenTreeInfo};
use crate::{
    core::token_tree::{
        analyze_token_tree_length, Comment, CommentExtractor, CommentKind, Delimiter, NestData, NestKind, Note,
        TokenTree,
    },
    syntax_fmt::{
        big_block_fmt,
        branch_fmt::{self, BranchExtractor, BranchKind},
        expr_fmt, fun_fmt,
        fun_fmt::FunExtractor,
        match_fmt::MatchExtractor,
    },
    tools::{
        syntax::{self, parse_file_string},
        utils::{FileLineMappingOneFile, Timer},
    },
};

pub enum FormatEnv {
    FormatModule,
    FormatUse,
    FormatStruct,
    FormatEnum,
    FormatExp,
    FormatTuple,
    FormatList,
    FormatLambda,
    FormatFun,
    FormatDefault,
}
pub struct FormatContext {
    pub content: String,
    pub env: FormatEnv,
    pub cur_module_name: String,
    pub current_token: Token,
}

impl FormatContext {
    pub(crate) fn new(content: String, env: FormatEnv) -> Self {
        FormatContext {
            content,
            env,
            cur_module_name: "".to_string(),
            current_token: Token::Module,
        }
    }

    pub fn set_env(&mut self, env: FormatEnv) {
        self.env = env;
    }
}

pub struct SyntaxExtractor {
    pub branch_extractor: BranchExtractor,
    pub match_extractor: MatchExtractor,
    pub fun_extractor: FunExtractor,
}

pub struct Format {
    pub local_cfg: FormatConfig,
    pub global_cfg: Config,
    pub depth: usize,
    pub line_mapping: FileLineMappingOneFile,
    pub comments_index: usize,
    pub ret: String,
    pub cur_line: u32,
    pub format_context: FormatContext,
    pub syntax_extractor: SyntaxExtractor,
}

#[derive(Clone, Default)]
pub struct FormatConfig {
    pub max_with: usize,
    pub indent_size: usize,
}

impl Format {
    pub(crate) fn new(global_cfg: Config, content: &str, format_context: FormatContext) -> Self {
        let mut line_mapping = FileLineMappingOneFile::default();
        line_mapping.update(content);
        let syntax_extractor = SyntaxExtractor {
            branch_extractor: BranchExtractor::new(content, BranchKind::ComIfElse),
            match_extractor: MatchExtractor::new(content),
            fun_extractor: FunExtractor::new(content),
        };
        Self {
            comments_index: Default::default(),
            local_cfg: FormatConfig {
                max_with: global_cfg.max_width(),
                indent_size: global_cfg.indent_size(),
            },
            global_cfg,
            depth: Default::default(),
            line_mapping,
            ret: Default::default(),
            cur_line: Default::default(),
            format_context,
            syntax_extractor,
        }
    }

    pub(crate) fn generate_token_tree(&mut self, content: &str) -> Result<Vec<TokenTree>, Diagnostics> {
        let mut env = CompilationEnv::new(Flags::testing(), Vec::new(), BTreeMap::new(), None);
        let (defs, _) = parse_file_string(&mut env, FileHash::empty(), content)?;
        let lexer = Lexer::new(content, FileHash::empty(), Edition::DEVELOPMENT);
        let parse = crate::core::token_tree::Parser::new(lexer, &defs);
        let token_tree = parse.parse_tokens();
        self.syntax_extractor.branch_extractor.preprocess(&defs);
        self.syntax_extractor.match_extractor.preprocess(&defs);
        Ok(token_tree)
    }

    fn post_process(&mut self) {
        tracing::debug!("post_process >> meet Brace");
        self.remove_trailing_whitespaces();
        tracing::debug!("post_process -- fmt_fun");
        self.ret = fun_fmt::fmt_fun(&self.ret, &self.global_cfg);
        tracing::debug!("post_process -- split_if_else_in_let_block");
        self.ret = branch_fmt::split_if_else_in_let_block(&self.ret, &self.global_cfg);

        tracing::debug!("post_process -- fmt_big_block");
        self.ret = big_block_fmt::fmt_big_block(&self.ret);
        self.remove_trailing_whitespaces();
        tracing::debug!("post_process << done !!!");
    }

    pub fn format_token_trees(mut self, token_tree: &[TokenTree], comments: &[Comment]) -> String {
        let mut pound_sign = None;
        for (index, tree) in token_tree.iter().enumerate() {
            if tree.is_pound() {
                pound_sign = Some(index);
            }
            let new_line = pound_sign.map(|x| (x + 1) == index).unwrap_or_default();
            self.format_token_trees_internal(tree, token_tree.get(index + 1), new_line, comments);
            if new_line {
                self.new_line(Some(tree.end_pos()), comments);
                pound_sign = None;
            }
            // top level
            if let TokenTree::Nested(NestedToken { data: kind, .. }) = tree {
                if kind.kind == NestKind::Brace {
                    self.new_line(Some(tree.end_pos()), comments);
                    self.post_process();
                }
            }
        }
        self.add_comments(comments, u32::MAX, "end_of_move_file".to_string());
        self.process_last_empty_line();
        self.ret
    }

    fn need_new_line(
        kind: NestKind,
        delimiter: Option<Delimiter>,
        _has_colon: bool,
        current: &TokenTree,
        next: Option<&TokenTree>,
    ) -> bool {
        if next.and_then(|x| x.content()) == delimiter.map(|x| x.to_static_str()) {
            return false;
        }

        let b_judge_next_token = if let Some((next_tok, next_content)) = next.map(|x| match x {
            TokenTree::Simple(SimpleToken { content, tok, .. }) => (*tok, content.clone()),
            TokenTree::Nested(NestedToken { data, .. }) => (data.kind.start_tok(), data.kind.start_tok().to_string()),
        }) {
            match next_tok {
                Token::Friend
                | Token::Const
                | Token::Fun
                | Token::While
                | Token::Use
                | Token::Struct
                | Token::Enum
                | Token::Spec
                | Token::Return
                | Token::Public
                | Token::Native
                | Token::Move
                | Token::Module
                | Token::Loop
                | Token::Let
                | Token::Invariant
                | Token::If
                | Token::Match
                | Token::Continue
                | Token::Break
                | Token::NumSign
                | Token::Abort => true,
                Token::Identifier => next_content.as_str() == "entry",
                _ => false,
            }
        } else {
            true
        };

        // special case for `}}`
        if match current {
            TokenTree::Simple(_) => false,
            TokenTree::Nested(NestedToken { data, .. }) => data.kind == NestKind::Brace,
        } && kind == NestKind::Brace
            && b_judge_next_token
        {
            return true;
        }
        false
    }

    fn need_new_line_for_each_token_in_nested(
        token: &NestedToken,
        delimiter: Option<Delimiter>,
        has_colon: bool,
        index: usize,
        new_line_mode: bool,
    ) -> bool {
        let NestedToken { elements, data, .. } = token;
        let t = elements.get(index).unwrap();
        let next_t = elements.get(index + 1);
        let d = delimiter.map(|x| x.to_static_str());
        let t_str = t.content();

        let mut new_line = if new_line_mode {
            Self::need_new_line(data.kind, delimiter, has_colon, t, next_t) || (d == t_str && d.is_some())
        } else {
            false
        };

        // comma in fun resource access specifier not change new line
        if d == t_str && d.is_some() {
            if let Some(deli_str) = d {
                if deli_str.contains(',') {
                    let mut idx = index;
                    while idx != 0 {
                        let ele = &elements[idx];
                        idx -= 1;
                        if let Some(key) = ele.content() {
                            if key.contains("fun") {
                                break;
                            }
                        }
                        if ele.content().is_none() {
                            continue;
                        }
                        if matches!(ele.content().unwrap(), "acquires" | "reads" | "writes" | "pure") {
                            new_line = false;
                            break;
                        }
                    }
                }
            }
        }

        if let Some((next_tok, next_content)) = next_t.map(|x| match x {
            TokenTree::Simple(SimpleToken { content, tok, .. }) => (*tok, content.clone()),
            TokenTree::Nested(NestedToken { data, .. }) => (data.kind.start_tok(), data.kind.start_tok().to_string()),
        }) {
            // ablility not change new line
            if syntax::token_to_ability(next_tok, &next_content).is_some() {
                new_line = false;
            }
        }
        new_line
    }

    fn process_fn_header_before_before_fn_nested(&mut self) {
        let cur_ret = self.ret.clone();
        // tracing::debug!("fun_header = {:?}", &self.format_context.content[(kind.start_pos as usize)..(kind.end_pos as
        // usize)]);
        if let Some(last_fun_idx) = cur_ret.rfind("fun") {
            let fun_header: &str = &cur_ret[last_fun_idx..];
            if let Some(specifier_idx) = fun_header.rfind("fun") {
                let indent_str = " ".to_string().repeat((self.depth + 1) * self.local_cfg.indent_size);
                let fun_specifier_fmted_str =
                    fun_fmt::fun_header_specifier_fmt(&fun_header[specifier_idx + 1..], &indent_str);

                self.ret = [
                    &self.ret[0..last_fun_idx + specifier_idx + 1],
                    fun_specifier_fmted_str.as_str(),
                ]
                .concat();
            }
        }
        if self.ret.contains("writes") {
            tracing::debug!("self.last_line = {:?}", self.last_line());
        }
    }

    fn get_new_line_mode_begin_nested(
        &mut self,
        nest_data: &NestData,
        elements: &Vec<TokenTree>,
        note: &Option<Note>,
        delimiter: Option<Delimiter>,
    ) -> (bool, Option<bool>) {
        let struct_def = note.map(|x| x == Note::StructDefinition).unwrap_or_default();
        let enum_def = note.map(|x| x == Note::EnumDefinition).unwrap_or_default();
        let fun_body = note.map(|x| x == Note::FunBody).unwrap_or_default();

        // 20240328 optimize
        // if it's branch with block, and block had more than one token, need new line
        if nest_data.kind == NestKind::Brace
            && elements.len() > 1
            && (self
                .syntax_extractor
                .branch_extractor
                .com_if_else
                .then_loc_vec
                .iter()
                .any(|&x| x.start() == nest_data.start_pos)
                || self
                    .syntax_extractor
                    .branch_extractor
                    .com_if_else
                    .else_loc_vec
                    .iter()
                    .any(|&x| x.start() == nest_data.start_pos)
                || self
                    .syntax_extractor
                    .match_extractor
                    .match_block
                    .match_loc_vec
                    .iter()
                    .any(|&x| x.start() == nest_data.start_pos)
                || self
                    .syntax_extractor
                    .match_extractor
                    .match_block
                    .arm_rhs_loc_vec
                    .iter()
                    .any(|&x| x.start() == nest_data.start_pos))
        {
            return (true, None);
        }

        let max_len_when_no_add_line: usize = self.global_cfg.max_width() / 3;
        let nested_token_len = analyze_token_tree_length(elements, self.global_cfg.max_width());

        if fun_body {
            self.process_fn_header_before_before_fn_nested();
        }

        // 20240329 updated
        // fun body brace always change new line;
        // if ParentTheses is empty, not change new line;
        let mut new_line_mode = {
            delimiter.map(|x| x == Delimiter::Semicolon).unwrap_or_default()
                || (struct_def && !elements.is_empty())
                || (enum_def && !elements.is_empty())
                || fun_body
                || (self.get_cur_line_len() + nested_token_len > self.global_cfg.max_width() && !elements.is_empty())
        };
        if new_line_mode && nest_data.kind != NestKind::Type {
            return (true, None);
        }

        match nest_data.kind {
            NestKind::Type => {
                // added in 20240112: if type in fun header, not change new line
                if self
                    .syntax_extractor
                    .fun_extractor
                    .is_generic_ty_in_fun_header(nest_data)
                {
                    return (false, None);
                }
                new_line_mode = nested_token_len > max_len_when_no_add_line;
            }
            NestKind::ParentTheses => {
                if self.format_context.current_token == Token::If {
                    new_line_mode = false;
                } else {
                    new_line_mode = !expr_fmt::judge_simple_paren_expr(nest_data, elements, &self.global_cfg);
                    return (new_line_mode, Some(new_line_mode));
                }
            }
            NestKind::Bracket => {
                new_line_mode = nested_token_len > max_len_when_no_add_line;
            }
            NestKind::Lambda => {
                if delimiter.is_none() && nested_token_len <= max_len_when_no_add_line {
                    new_line_mode = false;
                }
            }
            NestKind::Brace => {
                new_line_mode = self.last_line().contains("module") || nested_token_len > max_len_when_no_add_line;
            }
        }
        (new_line_mode, None)
    }

    fn add_new_line_after_nested_begin(
        &mut self,
        kind: &NestData,
        elements: &[TokenTree],
        b_new_line_mode: bool,
        comments: &[Comment],
    ) {
        if !b_new_line_mode {
            if let NestKind::Brace = kind.kind {
                if elements.len() == 1 {
                    self.ret.push(' ');
                }
            }
            return;
        }

        if !elements.is_empty() {
            let next_token = elements.first().unwrap();
            let mut next_token_start_pos: u32 = 0;
            self.analyzer_token_tree_start_pos_(&mut next_token_start_pos, next_token);
            if self.translate_line(next_token_start_pos) > self.translate_line(kind.start_pos) {
                // let source = self.format_context.content.clone();
                // let start_pos: usize = next_token_start_pos as usize;
                // let (_, next_str) = source.split_at(start_pos);
                // tracing::debug!("after format_token_trees_internal<TokenTree::Nested-start_token_tree> return,
                // next_token = {:?}",     next_str);
                // process line tail comment
                self.process_same_line_comment(kind.start_pos, true, comments);
            } else {
                self.new_line(Some(kind.start_pos), comments);
            }
        } else {
            self.new_line(Some(kind.start_pos), comments);
        }
    }

    fn format_single_token(
        &mut self,
        nested_token: &NestedToken,
        index: usize,
        pound_sign_new_line: bool,
        new_line: bool,
        pound_sign: &mut Option<usize>,
        comments: &[Comment],
    ) {
        let NestedToken { elements, data, .. } = nested_token;
        let token = &elements[index];
        let next_token = elements.get(index + 1);

        if !new_line && token.content().is_some() {
            if let NestKind::Brace = data.kind {
                if elements.len() == 1 {
                    self.ret.push(' ');
                }
            }
        }
        self.format_token_trees_internal(token, next_token, pound_sign_new_line || new_line, comments);
        if pound_sign_new_line {
            tracing::debug!("in loop<TokenTree::Nested> pound_sign_new_line = true");
            self.new_line(Some(token.end_pos()), comments);
            *pound_sign = None;
            return;
        }

        if new_line {
            let process_tail_comment_of_line = match next_token {
                Some(next_token) => {
                    let mut next_token_start_pos: u32 = 0;
                    self.analyzer_token_tree_start_pos_(&mut next_token_start_pos, next_token);
                    self.translate_line(next_token_start_pos) > self.translate_line(token.end_pos())
                }
                None => true,
            };
            self.process_same_line_comment(token.end_pos(), process_tail_comment_of_line, comments);
        } else if let NestKind::Brace = data.kind {
            if elements.len() == 1 {
                self.ret.push(' ');
            }
        }
    }

    fn format_each_token_in_nested_elements(
        &mut self,
        token: &NestedToken,
        delimiter: Option<Delimiter>,
        has_colon: bool,
        b_new_line_mode: bool,
        comments: &[Comment],
    ) {
        let NestedToken { elements, .. } = token;
        let mut pound_sign = None;
        let len = elements.len();
        let mut internal_token_idx = 0;
        while internal_token_idx < len {
            let pound_sign_new_line = pound_sign.map(|x| (x + 1) == internal_token_idx).unwrap_or_default();

            let new_line = Self::need_new_line_for_each_token_in_nested(
                token,
                delimiter,
                has_colon,
                internal_token_idx,
                b_new_line_mode,
            );

            if elements.get(internal_token_idx).unwrap().is_pound() {
                pound_sign = Some(internal_token_idx)
            }

            if Token::Period == self.format_context.current_token {
                let (continue_dot_cnt, index) = expr_fmt::process_link_access(&elements, internal_token_idx + 1);
                if continue_dot_cnt > 3 && index > internal_token_idx {
                    self.inc_depth(1);
                    let mut is_dot_new_line = true;
                    while internal_token_idx <= index + 1 {
                        self.format_single_token(
                            token,
                            internal_token_idx,
                            false,
                            is_dot_new_line,
                            &mut pound_sign,
                            comments,
                        );
                        internal_token_idx += 1;
                        is_dot_new_line = !is_dot_new_line;
                    }
                    // tracing::debug!("after processed link access, ret = {}", self.ret.clone().into_inner());
                    // tracing::debug!("after processed link access, internal_token_idx = {}, len = {}",
                    // internal_token_idx, len);
                    self.dec_depth(1);
                    continue;
                }
            }

            self.format_single_token(
                token,
                internal_token_idx,
                pound_sign_new_line,
                new_line,
                &mut pound_sign,
                comments,
            );
            internal_token_idx += 1;
        }
    }

    fn format_nested_token(&mut self, token: &NestedToken, next_token: Option<&TokenTree>, comments: &[Comment]) {
        let NestedToken { elements, data, note } = token;
        let (delimiter, has_colon) = Self::analyze_token_tree_delimiter(elements);
        let (b_new_line_mode, opt_mode) = self.get_new_line_mode_begin_nested(data, elements, note, delimiter);
        let b_add_indent = !note.map(|x| x == Note::ModuleAddress).unwrap_or_default();
        let nested_token_head = self.format_context.current_token;

        if b_new_line_mode {
            tracing::debug!("nested_token_head = [{:?}], add a new line", nested_token_head);
        }

        if nested_token_head == Token::NumSign {
            self.ret
                .push_str(&fun_fmt::process_fun_annotation(*data, elements.to_vec()));
            return;
        }

        // step1 -- format start_token
        self.format_token_trees_internal(&data.start_token_tree(), None, b_new_line_mode, comments);

        // step2 -- paired effect with step6
        if b_add_indent {
            self.inc_depth(1);
        }

        // step3
        if b_new_line_mode {
            self.add_new_line_after_nested_begin(data, elements, b_new_line_mode, comments);
        }

        // step4 -- format elements
        let need_change_line_for_each_item_in_paren = if NestKind::ParentTheses == data.kind {
            if opt_mode.is_none() {
                !expr_fmt::judge_simple_paren_expr(data, elements, &self.global_cfg)
            } else {
                opt_mode.unwrap_or_default()
            }
        } else {
            b_new_line_mode
        };
        self.format_each_token_in_nested_elements(
            token,
            delimiter,
            has_colon,
            need_change_line_for_each_item_in_paren,
            comments,
        );

        // step5 -- add_comments which before kind.end_pos
        self.add_comments(
            comments,
            data.end_pos,
            data.end_token_tree().content().unwrap_or_default().to_string(),
        );
        let ret_lines = self.ret.lines().count();
        let ends_with_whitespace = self.ret.ends_with(' ');
        // may be already add_a_new_line in step5 by add_comments(doc_comment in tail of line)
        self.ret = self.ret.trim_end().to_owned();
        if ends_with_whitespace {
            self.ret.push(' ');
        }
        let had_rm_added_new_line = self.ret.lines().count() < ret_lines;

        // step6 -- paired effect with step2
        if b_add_indent {
            self.dec_depth(1);
        }

        // step7
        if b_new_line_mode || had_rm_added_new_line {
            tracing::debug!("end_of_nested_block, b_new_line_mode = {b_new_line_mode}");
            if nested_token_head != Token::If {
                self.new_line(Some(data.end_pos), comments);
            }
        }

        // step8 -- format end_token
        self.format_token_trees_internal(&data.end_token_tree(), None, false, comments);
        if let TokenTree::Simple(_) = data.end_token_tree() {
            if nested_token_head == Token::EqualGreater && data.kind == NestKind::Brace {
                self.new_line(None, comments);
            } else if expr_fmt::need_space(token, next_token) {
                self.ret.push(' ');
            }
        }
    }

    fn format_simple_token(
        &mut self,
        token: &SimpleToken,
        next_token: Option<&TokenTree>,
        new_line_after: bool,
        comments: &[Comment],
    ) {
        let SimpleToken {
            content,
            pos,
            tok,
            note,
        } = token;

        // added in 20240115
        // updated in 20240124
        if *tok != Token::LBrace
            && self.syntax_extractor.branch_extractor.need_new_line_after_branch(
                &self.last_line(),
                *pos,
                &self.global_cfg,
            )
        {
            tracing::debug!("need_new_line_after_branch[{:?}], add a new line", content);
            self.inc_depth(1);
            self.new_line(None, comments);
        }

        // process `else if`
        if *tok == Token::Else
            && next_token.is_some_and(|tree| {
                tree.token() == Some(Token::If)
                    || self
                        .syntax_extractor
                        .branch_extractor
                        .is_nested_within_an_outer_else(*pos)
            })
        {
            self.new_line(None, comments);
        }

        // add blank row between module
        // this step must before add_comments. because there maybe some comments before new module
        // https://github.com/movebit/movefmt/issues/1
        self.maybe_meet_new_module_in_same_file(*tok, next_token, *pos, comments);

        // add comment(xxx) before current simple_token
        self.add_comments(comments, *pos, content.clone());
        // simple1:
        // self.translate_line(*pos) = 6
        // after processed xxx, self.cur_line = 5;
        // self.translate_line(*pos) - self.cur_line == 1
        // """
        // line5: // comment xxx
        // line6: simple_token
        // """
        if (self.translate_line(*pos) - self.cur_line) > 1 {
            // There are multiple blank lines between the cur_line and the current code simple_token
            tracing::debug!(
                "self.translate_line(*pos) = {}, self.cur_line = {}",
                self.translate_line(*pos),
                self.cur_line
            );
            tracing::debug!("SimpleToken[{:?}], add a new line", content);
            self.new_line(None, comments);
        }

        // added in 20240115
        // updated in 20240124
        // updated in 20240222: remove condition `if Tok::RBrace != *tok `
        if self.depth > 0 {
            let tok_end_pos = *pos + content.len() as u32;
            let nested_branch_depth = self
                .syntax_extractor
                .branch_extractor
                .added_new_line_after_branch(tok_end_pos);

            if nested_branch_depth > 0 {
                tracing::debug!("nested_branch_depth[{:?}] = [{:?}]", content, nested_branch_depth);
                self.dec_depth(nested_branch_depth);
            }
        }

        if matches!(tok, Token::If | Token::Match) {
            self.format_context.set_env(FormatEnv::FormatExp);
        }
        self.format_context.current_token = *tok;

        let mut split_line_after_content = false;
        if self.judge_change_new_line_when_over_limits(*tok, *note, next_token) {
            tracing::debug!("last_line = {:?}", self.last_line());
            tracing::debug!(
                "SimpleToken{:?} too long, add a new line because of split line",
                content
            );

            if matches!(
                *tok,
                Token::Equal | Token::EqualEqual | Token::EqualEqualGreater | Token::LessEqualEqualGreater
            ) {
                self.ret.push_str(content.as_str());
                split_line_after_content = true;
            }
            self.inc_depth(1);
            self.new_line(None, comments);
            self.dec_depth(1);
        }

        if !split_line_after_content {
            self.ret.push_str(content.as_str());
        }

        self.cur_line = self.translate_line(*pos);
        if new_line_after {
            return;
        }
        if self.judge_change_new_line_when_over_limits(*tok, *note, next_token) {
            tracing::debug!("last_line = {:?}", self.last_line());
            tracing::debug!("SimpleToken{:?}, add a new line because of split line", content);
            self.inc_depth(1);
            self.new_line(None, comments);
            self.dec_depth(1);
            return;
        }
        if expr_fmt::need_space(token, next_token) {
            self.ret.push(' ');
        }
    }

    fn format_token_trees_internal(
        &mut self,
        token: &TokenTree,
        next_token: Option<&TokenTree>,
        new_line_after: bool,
        comments: &[Comment],
    ) {
        match token {
            TokenTree::Nested(nested) => self.format_nested_token(nested, next_token, comments),
            TokenTree::Simple(simple) => self.format_simple_token(simple, next_token, new_line_after, comments),
        }
    }

    fn add_comments(&mut self, comments: &[Comment], pos: u32, content: String) {
        let mut comment_nums_before_cur_simple_token = 0;
        let mut last_cmt_is_block_cmt = false;
        let mut last_cmt_start_pos = 0;
        for c in &comments[self.comments_index..] {
            if c.start_offset > pos {
                break;
            }

            if (self.translate_line(c.start_offset) - self.cur_line) > 1 {
                tracing::debug!("the pos of this comment > current line");
                // 20240318: process case as follows
                //
                /*
                #[test(econia = @econia, integrator = @user)]

                // comment
                fun func() {}
                */
                if self.format_context.current_token != Token::NumSign {
                    self.new_line(None, comments);
                }
            }

            if (self.translate_line(c.start_offset) - self.cur_line) == 1 {
                // if located after nestedToken start, maybe already chanedLine
                self.ret = self.ret.trim_end().to_owned();
                self.new_line(None, comments);
            }

            // tracing::debug!("-- add_comments: line(c.start_offset) - cur_line = {:?}",
            //     self.translate_line(c.start_offset) - self.cur_line);
            // tracing::debug!("c.content.as_str() = {:?}\n", c.content.as_str());
            if self.no_space_or_new_line_for_comment() {
                self.ret.push(' ');
            }

            self.ret.push_str(&c.format_comment(
                c.comment_kind(),
                self.depth * self.local_cfg.indent_size,
                0,
                &self.global_cfg,
            ));

            match c.comment_kind() {
                CommentKind::DocComment => {
                    // let buffer = self.ret.clone();
                    // let len: usize = c.content.len();
                    // let x: usize = buffer.len();
                    // if len + 2 < x {
                    //     if let Some(ch) = buffer.clone().chars().nth(x - len - 2) {
                    //         if !ch.is_ascii_whitespace() {
                    //             // insert black space after '//'
                    //             self.ret.insert(x - len - 1, ' ');
                    //         }
                    //     }
                    // }
                    self.new_line(None, comments);
                    last_cmt_is_block_cmt = false;
                }
                _ => {
                    let end = c.start_offset + (c.content.len() as u32);
                    let line_start = self.translate_line(c.start_offset);
                    let line_end = self.translate_line(end);

                    if !content.contains(')')
                        && !content.contains(',')
                        && !content.contains(';')
                        && !content.contains('.')
                    {
                        self.ret.push(' ');
                    }
                    if line_start != line_end {
                        self.new_line(None, comments);
                    }
                    last_cmt_is_block_cmt = true;
                }
            }
            self.comments_index += 1;
            self.cur_line = self.translate_line(c.start_offset + (c.content.len() as u32) - 1);
            comment_nums_before_cur_simple_token += 1;
            last_cmt_start_pos = c.start_offset;
            // tracing::debug!("in add_comments for loop: self.cur_line = {:?}\n", self.cur_line);
        }
        if comment_nums_before_cur_simple_token > 0 {
            if last_cmt_is_block_cmt && self.translate_line(pos) - self.translate_line(last_cmt_start_pos) == 1 {
                // process this case:
                // line[i]: /*comment1*/ /*comment2*/
                // line[i+1]: code // located in `pos`
                self.new_line(None, comments);
            }
            tracing::debug!(
                "add_comments[{:?}] before pos[{:?}] = {:?} return <<<<<<<<<\n",
                comment_nums_before_cur_simple_token,
                pos,
                content
            );
        }
    }
}

impl Format {
    fn inc_depth(&mut self, amount: usize) {
        self.depth += amount;
    }
    fn dec_depth(&mut self, amount: usize) {
        self.depth = self.depth.saturating_sub(amount)
    }

    fn no_space_or_new_line_for_comment(&self) -> bool {
        self.ret
            .chars()
            .last()
            .is_some_and(|c| c == '\n' || c == ' ' || c == '(')
    }

    fn indent(&mut self) {
        self.ret
            .push_str(" ".repeat(self.depth * self.local_cfg.indent_size).as_str());
    }

    fn translate_line(&self, pos: u32) -> u32 {
        self.line_mapping.translate(pos, pos).unwrap().start.line
    }

    /// analyzer a `Nested` token tree.
    fn analyze_token_tree_delimiter(
        token_tree: &[TokenTree],
    ) -> (
        Option<Delimiter>, // if this is a `Delimiter::Semicolon` we can know this is a function body or etc.
        bool,              // has a `:`
    ) {
        let mut d = None;
        let mut has_colon = false;
        for t in token_tree.iter() {
            match t {
                TokenTree::Simple(SimpleToken { content, .. }) => match content.as_str() {
                    ";" => {
                        d = Some(Delimiter::Semicolon);
                    }
                    "," => {
                        if d.is_none() {
                            // Somehow `;` has high priority.
                            d = Some(Delimiter::Comma);
                        }
                    }
                    ":" => {
                        has_colon = true;
                    }
                    _ => {}
                },
                TokenTree::Nested { .. } => {}
            }
        }
        (d, has_colon)
    }

    fn analyzer_token_tree_start_pos_(&self, ret: &mut u32, token_tree: &TokenTree) {
        match token_tree {
            TokenTree::Simple(SimpleToken { pos, .. }) => {
                *ret = *pos;
            }
            TokenTree::Nested(NestedToken { data, .. }) => {
                *ret = data.start_pos;
            }
        }
    }

    fn process_same_line_comment(
        &mut self,
        add_line_comment_pos: u32,
        process_tail_comment_of_line: bool,
        comments: &[Comment],
    ) {
        let cur_line = self.cur_line;
        let mut call_new_line = false;
        for c in &comments[self.comments_index..] {
            if !process_tail_comment_of_line && c.start_offset > add_line_comment_pos {
                break;
            }

            if self.translate_line(add_line_comment_pos) != self.translate_line(c.start_offset) {
                break;
            }
            // tracing::debug!("self.translate_line(c.start_offset) = {}, self.cur_line = {}", self.translate_line(c.start_offset), self.cur_line);
            // tracing::debug!("add a new line[{:?}], meet comment", c.content);
            // if (self.translate_line(c.start_offset) - self.cur_line) > 1 {
            //     tracing::debug!("add a black line");
            //     self.new_line(None);
            // }
            // self.ret.push_str(c.content.as_str());
            let kind = c.comment_kind();
            let fmted_cmt_str = c.format_comment(kind, self.depth * self.local_cfg.indent_size, 0, &self.global_cfg);
            // tracing::debug!("fmted_cmt_str in same_line = \n{}", fmted_cmt_str);
            /*
            let buffer = self.ret.clone();
            if !buffer.clone().chars().last().unwrap_or(' ').is_ascii_whitespace()
            && !buffer.clone().chars().last().unwrap_or(' ').eq(&'('){
                self.ret.push_str(" ");
                // insert 2 black space before '//'
                // if let Some(_) = fmted_cmt_str.find("//") {
                //     self.ret.push_str(" ");
                // }
            }
            */
            if self.no_space_or_new_line_for_comment() {
                self.ret.push(' ');
            }

            self.ret.push_str(&fmted_cmt_str);
            match kind {
                CommentKind::BlockComment => {
                    let end = c.start_offset + (c.content.len() as u32);
                    let line_start = self.translate_line(c.start_offset);
                    let line_end = self.translate_line(end);
                    if line_start != line_end {
                        tracing::debug!("in new_line, add CommentKind::BlockComment");
                        self.new_line(None, comments);
                        call_new_line = true;
                    }
                }
                _ => {
                    // tracing::debug!("-- process_same_line_comment, add CommentKind::_({})", c.content);
                    self.new_line(None, comments);
                    call_new_line = true;
                }
            }
            self.comments_index += 1;
            self.cur_line = self.translate_line(c.start_offset + (c.content.len() as u32) - 1);
        }
        if cur_line != self.cur_line || call_new_line {
            tracing::debug!("success new line, return <<<<<<<<<<<<<<<<< \n");
            return;
        }
        self.ret.push('\n');
        self.indent();
    }

    fn new_line(&mut self, add_line_comment_option: Option<u32>, comments: &[Comment]) {
        let (add_line_comment, b_add_comment) = match add_line_comment_option {
            Some(add_line_comment) => (add_line_comment, true),
            _ => (0, false),
        };
        if !b_add_comment {
            self.ret.push('\n');
            self.indent();
            return;
        }
        self.process_same_line_comment(add_line_comment, false, comments);
    }

    fn maybe_meet_new_module_in_same_file(
        &mut self,
        tok: Token,
        next_token: Option<&TokenTree>,
        pos: u32,
        comments: &[Comment],
    ) {
        if Token::Module == tok {
            // tracing::debug!("SimpleToken[{:?}], cur_module_name = {:?}", content,
            // self.format_context.cur_module_name);
            if !self.format_context.cur_module_name.is_empty() && (self.translate_line(pos) - self.cur_line) >= 1 {
                // tracing::debug!("SimpleToken[{:?}], add blank row between module", content);
                self.new_line(None, comments);
            }
            self.format_context.set_env(FormatEnv::FormatModule);
            self.format_context.cur_module_name = next_token.unwrap().content().unwrap_or_default().to_string();
            // Note: You can get the token tree of the entire format_context.env here
        }
    }
}

impl Format {
    fn last_line(&self) -> String {
        self.ret.lines().last().map(|x| x.to_string()).unwrap_or_default()
    }

    fn tok_suitable_for_new_line(tok: Token, note: Option<Note>, next: Option<&TokenTree>) -> bool {
        // special case
        if next.is_some_and(|x| matches!(x, TokenTree::Nested(NestedToken { data, .. }) if data.kind == NestKind::Type))
        {
            // tracing::debug!("tok_suitable_for_new_line ret false");
            return false;
        }
        let is_bin = note.map(|x| x == Note::BinaryOP).unwrap_or_default();
        let ret = match tok {
            Token::Less | Token::Amp | Token::Star | Token::Greater if is_bin => true,
            Token::ExclaimEqual
            | Token::Percent
            | Token::AmpAmp
            | Token::Plus
            | Token::Minus
            | Token::Period
            | Token::Slash
            | Token::LessEqual
            | Token::LessLess
            | Token::Equal
            | Token::EqualEqual
            | Token::EqualEqualGreater
            | Token::LessEqualEqualGreater
            | Token::GreaterEqual
            | Token::GreaterGreater
            | Token::NumValue => true,
            _ => false,
        };
        tracing::debug!("tok_suitable_for_new_line ret = {}", ret);
        ret
    }

    fn get_cur_line_len(&self) -> usize {
        let last_ret = self.last_line();
        let mut tokens_len = 0;
        let mut special_key = false;
        let mut lexer = Lexer::new(&last_ret, FileHash::empty(), Edition::DEVELOPMENT);
        lexer.advance().unwrap();
        while lexer.peek() != Token::EOF {
            tokens_len += lexer.content().len();
            if !special_key {
                special_key = matches!(
                    lexer.peek(),
                    Token::If
                        | Token::Match
                        | Token::LBrace
                        | Token::Module
                        | Token::Struct
                        | Token::Enum
                        | Token::Fun
                        | Token::Public
                        | Token::Colon
                        | Token::Spec
                );
            }
            lexer.advance().unwrap();
        }

        if special_key { tokens_len } else { last_ret.len() }
    }

    fn judge_change_new_line_when_over_limits(&self, tok: Token, note: Option<Note>, next: Option<&TokenTree>) -> bool {
        self.get_cur_line_len() + tok.to_string().len() > self.global_cfg.max_width()
            && Self::tok_suitable_for_new_line(tok, note, next)
    }

    fn remove_trailing_whitespaces(&mut self) {
        self.ret = self
            .ret
            .lines()
            .map(|line| line.trim_end_matches(|c| c == ' '))
            .collect::<Vec<_>>()
            .join("\n");
    }

    fn process_last_empty_line(&mut self) {
        let mut lines = self.ret.lines().collect::<Vec<&str>>();
        let last_line = lines.last().unwrap_or(&"");

        if last_line.is_empty() {
            while lines.len() > 1 && lines[lines.len() - 2].is_empty() {
                lines.pop();
            }
        } else {
            lines.push("");
        }

        self.ret = lines.join("\n");
    }
}

pub fn format_entry(content: &str, config: &Config) -> Result<String, Diagnostics> {
    let mut timer = Timer::start();
    {
        // https://github.com/movebit/movefmt/issues/2
        let mut env = CompilationEnv::new(Flags::testing(), Vec::new(), BTreeMap::new(), None);
        let _ = parse_file_string(&mut env, FileHash::empty(), content)?;
    }

    let mut full_fmt = Format::new(
        config.clone(),
        content,
        FormatContext::new(content.to_string(), FormatEnv::FormatDefault),
    );
    let ce = CommentExtractor::new(content).unwrap();

    let token_tree = full_fmt.generate_token_tree(content)?;
    timer = timer.done_parsing();

    let result = full_fmt.format_token_trees(&token_tree, &ce.comments);
    timer = timer.done_formatting();
    if config.verbose() == Verbosity::Verbose {
        println!(
            "Spent {0:.3} secs in the parsing phase, and {1:.3} secs in the formatting phase",
            timer.get_parse_time(),
            timer.get_format_time(),
        );
    }
    Ok(result)
}
