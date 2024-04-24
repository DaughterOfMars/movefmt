// Copyright 2024 IOTA Stiftung
// SPDX-License-Identifier: Apache-2.0

use core::cell::RefCell;
use std::collections::HashMap;

use move_compiler::parser::ast::*;
use move_ir_types::location::{ByteIndex, Loc};

use crate::tools::utils::FileLineMappingOneFile;

#[derive(Default, Debug)]
pub struct MatchBlock {
    pub match_block_loc_vec: Vec<Loc>,
    pub arm_loc_vec: Vec<Loc>,
}

#[derive(Debug)]
pub struct MatchExtractor {
    pub match_block: MatchBlock,
    pub source: String,
    pub line_mapping: FileLineMappingOneFile,
    pub added_new_line_branch: RefCell<HashMap<ByteIndex, usize>>,
}

impl MatchExtractor {
    pub fn new(fmt_buffer: &str) -> Self {
        let mut extractor = Self {
            match_block: Default::default(),
            source: fmt_buffer.to_owned(),
            line_mapping: FileLineMappingOneFile::default(),
            added_new_line_branch: HashMap::default().into(),
        };

        extractor.line_mapping.update(fmt_buffer);
        extractor
    }

    fn collect_expr(&mut self, e: &Exp) {
        if let Exp_::Match(_, arms) = &e.value {
            self.match_block.match_block_loc_vec.push(arms.loc);
            for arm in &arms.value {
                self.match_block.arm_loc_vec.push(arm.loc);
                self.collect_expr(&arm.value.rhs);
            }
        }
        if let Exp_::Block(b) = &e.value {
            self.collect_seq(b);
        }
    }

    fn collect_seq_item(&mut self, s: &SequenceItem) {
        if let SequenceItem_::Bind(_, _, e) = &s.value {
            self.collect_expr(e);
        }
    }

    fn collect_seq(&mut self, s: &Sequence) {
        for s in s.1.iter() {
            self.collect_seq_item(s);
        }
        if let Some(t) = s.3.as_ref() {
            self.collect_expr(t);
        }
    }

    fn collect_function(&mut self, d: &Function) {
        match &d.body.value {
            FunctionBody_::Defined(s) => {
                self.collect_seq(s);
            }
            FunctionBody_::Native => {}
        }
    }

    fn collect_module(&mut self, d: &ModuleDefinition) {
        for m in d.members.iter() {
            if let ModuleMember::Function(x) = &m {
                self.collect_function(x)
            }
        }
    }

    fn collect_definition(&mut self, d: &Definition) {
        match d {
            Definition::Module(x) => self.collect_module(x),
            Definition::Address(x) => {
                for x in x.modules.iter() {
                    self.collect_module(x);
                }
            }
        }
    }

    fn need_new_line_after_arm(&self, arm_start_pos: ByteIndex) -> bool {
        for arm_loc in &self.match_block.arm_loc_vec {
            if arm_loc.start() == arm_start_pos {
                let new_line_cnt = if self.added_new_line_branch.borrow().contains_key(&arm_loc.start()) {
                    self.added_new_line_branch.borrow_mut()[&arm_loc.start()]
                } else {
                    0
                };
                self.added_new_line_branch
                    .borrow_mut()
                    .insert(arm_loc.start(), new_line_cnt + 1);
                return true;
            }
        }
        false
    }

    fn added_new_line_after_arm(&self, arm_end_pos: ByteIndex) -> usize {
        for arm_loc in &self.match_block.arm_loc_vec {
            if arm_loc.end() == arm_end_pos && self.added_new_line_branch.borrow().contains_key(&arm_loc.end()) {
                return self.added_new_line_branch.borrow_mut()[&arm_loc.end()];
            }
        }
        0
    }

    pub fn preprocess(&mut self, module_defs: &[Definition]) {
        for d in module_defs.iter() {
            self.collect_definition(d);
        }
    }
}
