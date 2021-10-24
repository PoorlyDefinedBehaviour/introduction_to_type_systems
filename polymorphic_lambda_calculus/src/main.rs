mod ast;
mod grammar;
mod typechecker;

use ast::Term;

fn parse(input: &str) -> Term {
  grammar::TermParser::new().parse(input).unwrap()
}

fn main() {
  // let code = "λx: Int. x + 2";
  // let code = "(ΛX. λx: X. ΛX. λy: X. y) ";

  // let code = "ΛX. λx: X. x";

  // let code = "ΛZ. λz: Z. z";

  // ΛX. λx: X. ΛY. λy: Y. x: (∀X.1 -> (∀Y.0 -> 1))
  let code = "ΛX. λx: X. ΛY. λy: Y. x";

  let term = parse(code);

  match typechecker::type_of(term) {
    Err(error) => println!("{:?}", error),
    Ok(typ) => println!("{}: {}", code, typ),
  }
}
