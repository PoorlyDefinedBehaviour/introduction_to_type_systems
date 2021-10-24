// The simply typed lambda calculus has two different
// sorts of types:
//
// Function types
//
// We write the type of a function that accepts a parameter
// of type τ and returns a value of type τ' as τ -> τ'.
//
// The identity function on booleans, for example, accepts a
// parameter of type Bool and returns a value of of the same type.
//
// Its type is written as Bool -> Bool.
//
// The function arrow is right-associative:
// τ -> τ' -> τ'' is the same as τ -> (τ' -> τ'').
//
// Simple types
//
// Simple types are the types of constant values: Bool, Int, etc.

// τ ::=
//  | τ -> τ'   (function type)
//  | Bool      (boolean type)
//  | Int       (integer type)
#[derive(Debug, PartialEq, Clone)]
pub enum Type {
  Arrow(Box<Type>, Box<Type>),
  Bool,
  Int,
}

impl std::fmt::Display for Type {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Type::Int => write!(f, "Int"),
      Type::Bool => write!(f, "Bool"),
      Type::Arrow(param_type, return_type) => write!(f, "{} -> {}", param_type, return_type),
    }
  }
}
// Terms
// There are five sorts of terms in the simply typed lambda calculus.
//
// Variables
// These are are names for values, we usually use strings for this
// but could also use integers(NOTE: is he talking about De Bruijn?)
//
// Lambda abstractions
// Lambda abstractions are functions that accept one parameter
// and return a value the identity function would look like this:
//
// \λx: τ. x
//
// Applications
// Also known as function calls, it looks like this:
//
// Here we are applying f to x, in rust it would be f(x).
//
// f x
//
// Constant values
// These are values like integer literals, boolean literals, etc.
//
// Computation constructs
// There are terms like if expressions

// term ::=
//  | False                             (false)
//  | True                              (true)
//  | integer                           (integer)
//  | variable                          (variable)
//  | λx: term. term                    (lambda abstraction)
//  | term term'                        (application)
//  | term + term'                      (addition)
//  | if term then term' else term''    (if-then-else)
#[derive(Debug)]
pub enum Term {
  True,
  False,
  Int(i32),
  Var(String),
  Abs {
    param: String,
    param_type: Type,
    body: Box<Term>,
  },
  App {
    function: Box<Term>,
    arg: Box<Term>,
  },
  Add(Box<Term>, Box<Term>),
  If {
    condition: Box<Term>,
    consequence: Box<Term>,
    alternative: Box<Term>,
  },
}
