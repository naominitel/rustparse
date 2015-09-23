#![feature(rustc_private)]
#![feature(plugin)]
#![plugin(rustparse)]

#[macro_use] extern crate log;

LL_parser! my_parser(
    token Op;
    token Cl;
    token Bang;
    token Inter;
    token String;

    Session ::=
        Facts Question,
        Op Session Cl Session
    ;

    Facts ::=
        empty,
        Fact Facts
    ;

    Fact ::= Bang String ;

    Question ::= Inter String ;
);

fn main() {
    use my_parser::Token::*;

    let tokens = vec![
        Op(()), Op(()), Bang(()), String(()), Bang(()), String(()), Inter(()), String(()), Cl(()), Inter(()), String(()), Cl(()),
        Bang(()), String(()), Inter(()), String(()),
    ];

    match my_parser::parse(tokens.iter()) {
        Ok(()) => (),
        Err(e) => println!("{}", e)
    };
}
