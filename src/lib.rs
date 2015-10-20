#![feature(plugin_registrar)]
#![feature(quote)]
#![feature(rustc_private)]

#![warn(unused_qualifications)]

extern crate syntax;
extern crate rustc;

#[macro_use] extern crate log;

use syntax::{ast, codemap, diagnostic, parse};
use syntax::ext::base;
use syntax::ext::build::AstBuilder;
use syntax::ptr::P;
use syntax::util::small_vector::SmallVector;

pub mod rt {
    pub use ::grammar::Symbol;
    pub trait Parser {
        type Token;
        type Output;
        type Error;
        fn parse<T>(lexer: T) -> Result<Self::Output, Self::Error>
            where T: Iterator<Item = Self::Token>;
    }
}

mod codegen;
#[macro_use]
mod grammar;
mod ll;

trait Generator: grammar::EBNFExpander {
    fn run(ast: grammar::Grammar, cx: &mut base::ExtCtxt) -> Vec<P<ast::Item>>;
}

struct Result {
    handler: diagnostic::SpanHandler,
    span: codemap::Span,
    item: P<ast::Item>
}

impl base::MacResult for Result {
    fn make_items(self: Box<Result>) -> Option<SmallVector<P<ast::Item>>> {
        Some(SmallVector::one(self.item))
    }

    fn make_expr(self: Box<Result>) -> Option<P<ast::Expr>> {
        panic!(self.handler.span_fatal(self.span,
            "macro invoked on expression context"));
    }
}

fn run_generator<'a, T: Generator>(
        cx: &'a mut base::ExtCtxt, sp: codemap::Span,
        id: ast::Ident, args: Vec<ast::TokenTree>
    ) -> Box<base::MacResult + 'a> {
    let ast = grammar::parse::<T>(args, cx);
    let items = <T as Generator>::run(ast, cx);

    Box::new(Result {
        handler: diagnostic::SpanHandler::new(
            diagnostic::Handler::new(diagnostic::Auto, None, true),
            codemap::CodeMap::new()
        ),
        span: sp,
        item: quote_item!(cx, mod $id {
            // add a glob use
            #[allow(unused_imports)] use super::*;
            $items
        }).unwrap()
    }) as Box<base::MacResult>
}

macro_rules! register(
    ($reg:ident, $gen:ident) => (
        $reg.register_syntax_extension(
            { let name = stringify!($gen);
              parse::token::intern(&format!("{}_parser", name)[..]) },
            base::IdentTT(Box::new(run_generator::<$gen>), None, false)
        );
    )
);

#[plugin_registrar]
pub fn plugin_registrar(reg: &mut ::rustc::plugin::Registry) {
    use ll::LL;
    register!(reg, LL)
}
