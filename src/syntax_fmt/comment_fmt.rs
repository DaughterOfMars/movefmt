use crate::core::token_tree::{
    Comment, CommentExtrator, CommentKind, Delimiter, NestKind_, Note, TokenTree,
};
use commentfmt::{shape::*, comment::*, config::*};

impl Comment {
    /// format comment
    /// exampls `//   this is a comment` to `// this is a comment`,etc.
    pub fn format(
        &self,
        _convert_line: impl Fn(
            u32, // offset
        ) -> u32, // line number
    ) -> String {
        unimplemented!()
    }

    pub fn comment_kind(&self) -> CommentKind {
        if self.content.starts_with("//") {
            CommentKind::DocComment
        } else {
            CommentKind::BlockComment
        }
    }

    pub fn format_doc_comment_with_multi_star(
        &self,
        block_indent: usize, 
        alignment: usize
    ) -> String {
        let mut result = self.content.to_string();
        let block_style = false;
        let indent = Indent::new(block_indent, alignment);
        let shape = Shape {
            width: 100,
            indent,
            offset: 0,
        };

        let config = &Config::default();
        let mut cmt_str = String::from("");
        cmt_str.push_str(result.as_str());
        if let Some(comment) = rewrite_comment(&cmt_str, block_style, shape, config) {
            result = comment;
        }
        result
    }

    pub fn format_comment(
        &self,
        kind: CommentKind,
        block_indent: usize, 
        alignment: usize
    ) -> String {
        if CommentKind::DocComment == kind {
            self.content.to_string()
        } else {
            self.format_doc_comment_with_multi_star(block_indent, alignment)
        }
    }


    fn add_spaces(s: &str) -> String {
        let start = s.find("comment").unwrap();  
        let end = start + "comment".len();  
        format!("{}{}{}", &s[0..start], " comment ", &s[end..])  
    }
}


#[test]
fn test_rewrite_comment_1() {
    // let orig = "/* This is a multi-line\n * comment */\n\n// This is a single-line comment";
    let orig = "\n/**  \n         * This function demonstrates various examples using tuples.  \n         * It includes assignments to tuple variables and reassignments using conditional statements.  \n*/";
    // let orig = "
    // //      this is a comment
    // ";
    
    let block_style = true;
    // let style = CommentStyle::SingleBullet;
    let indent = Indent::new(4, 0);
    let shape = Shape {
        width: 100,
        indent,
        offset: 0,
    };

    let config = &Config::default();
    if let Some(comment) = rewrite_comment(orig, block_style, shape, config) {
        println!("{}", comment);
    }
}
