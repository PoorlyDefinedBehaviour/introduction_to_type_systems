// The polymorphic lambda calculus,
// also called System F, is an extension of the
// simply typed lambda calculus with polymorphism.
//
// In the simply typed lambda calculus we can write
// functions with types like these:
//
// λx: Bool. x
// λx: Bool -> Int. x
//
// These functions have different types even though they
// are the same function, the identity function.
// In the simply typed lambda calculus we would need
// to define the identity function for every type
// that we care about, which is really annoying(looking at you Go).
//
// The polymorphic lambda calculus allows us to define the
// identity function only once using parametric polymorphism,
// the result of adding parametric polymorphism to the
// simply typed lambda calculus is called polymorphic
// lambda calculus or System F.
//
// Syntax
//
// To incorporate polymorphism in the simply typed lambda calculus,
// we need to add two new sorts of types:
//
// Type variables
// These are just like term-level variables, but instead of ranging
// over values, they range over types. They are written with capital letters.
//
// Polymorphic types
// These are written like this: ∀X.τ, where X is a type variable
// and τ a type.(∀ means for all)
//
// Here's how the identity function type looks like in the
// polymorphic lambda calculus:
//
// ∀X. X -> X
//
// This type means the identity function accepts a value of any
// type, and returns a value of the same type.
//
// The syntax for types is:
//
// τ ::=
//  | X       (type variable)
//  | ∀X.τ    (polymorphic type)
//  | τ -> τ' (function type)
//  | Bool    (boolean type)
//  | Int     (integer type)
#[derive(Debug, PartialEq, Clone)]
pub enum Type {
  // Differences from the symply typed lambda calculus types:
  //
  // We have the same types as the simply typed lambda calculus
  // but we also add a TypeVariable
  TypeVariable(String),
  DeBruijn(usize),
  // We also added for all
  // ∀X. X -> X
  Forall(String, Box<Type>),
  Arrow(Box<Type>, Box<Type>),
  Bool,
  Int,
}

impl std::fmt::Display for Type {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Type::Int => write!(f, "Int"),
      Type::Bool => write!(f, "Bool"),
      Type::DeBruijn(i) => write!(f, "{}", i),
      Type::TypeVariable(x) => write!(f, "{}", x),
      Type::Arrow(param_type, return_type) => match (&**param_type, &**return_type) {
        (Type::Arrow(_, _), Type::Arrow(_, _)) => {
          write!(f, "({}) -> ({})", param_type, return_type)
        }
        (_, Type::Arrow(_, _)) => {
          write!(f, "{} -> ({})", param_type, return_type)
        }
        (Type::Arrow(_, _), _) => {
          write!(f, "({}) -> {}", param_type, return_type)
        }
        (_, _) => {
          write!(f, "{} -> {}", param_type, return_type)
        }
      },
      Type::Forall(type_var, typ) => write!(f, "(∀{}.{})", type_var, typ),
    }
  }
}

// We also have new terms:
//
// Type abstractions
// Type abstractions are just like normal abstractions,
// but instead of introducing a variable that ranges over values,
// it introduces a type variable that ranges over types.
//
// Type abstractions are written with an uppercase lambda.
// Here's how the identity function looks like:
//
// id = ΛX. λx: X. x
//
// It means that for any type X, x has type X.
//
// Type applications
// Type applications are used to instantiate a term with
// a specific type.
// If we want to use the identity function on an integer,
// we need to indicate that the type variable X in the definition
// of id should be replaced by Int.
//
// The syntax for a type application for instantiating the
// identity function with the Int type is:
//
// id Int
//
// term ::=
//  | False                             (false)
//  | True                              (true)
//  | integer                           (integer)
//  | variable                          (variable)
//  | λx: term. term                    (lambda abstraction)
//  | term term'                        (application)
//  | term + term'                      (addition)
//  | if term then term' else term''    (if-then-else)
//  | ΛX. t                             (type abstraction)
//  | t τ                               (type application)
#[derive(Debug, Clone)]
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
  // NEW
  // id = ΛX. λx: X. x
  TypeAbs(String, Box<Term>),
  // id Int
  // id Bool
  TypeApp(Box<Term>, Type),
}

impl std::fmt::Display for Term {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Term::True => write!(f, "true"),
      Term::False => write!(f, "false"),
      Term::Int(x) => write!(f, "{}", x),
      Term::Var(x) => write!(f, "{}", x),
      Term::Abs {
        param,
        param_type,
        body,
      } => write!(f, "λ{}: {}. {}", param, param_type, body),
      Term::App { function, arg } => write!(f, "{} {}", function, arg),
      Term::Add(left, right) => write!(f, "{} + {}", left, right),
      Term::If {
        condition,
        consequence,
        alternative,
      } => write!(
        f,
        "if {} then {} else {}",
        condition, consequence, alternative
      ),
      Term::TypeAbs(type_var, typ) => write!(f, "Λ{}. {}", type_var, typ),
      Term::TypeApp(type_abs, typ) => write!(f, "{} {}", type_abs, typ),
    }
  }
}
