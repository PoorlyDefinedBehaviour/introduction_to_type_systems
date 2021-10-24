mod ast;
mod grammar;
mod typechecker;

use ast::Term;

fn parse(input: &str) -> Term {
  grammar::TermParser::new().parse(input).unwrap()
}

fn main() {
  let code = "λx: Int. x + 2";

  let term = parse(code);

  match typechecker::type_of(&term) {
    Err(error) => println!("{:?}", error),
    Ok(typ) => println!("{}: {}", code, typ),
  }
}
