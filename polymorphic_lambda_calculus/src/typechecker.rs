// To express that a term has a certain type, we use
// typing judgement. The judgment will look something like
// this in mathmetical notation Γ ⊢ t: τ.
//
// Read Γ ⊢ t: τ as the context Γ entails that t has type τ.
//
// Ø represents the empty context
// Γ, t: τ represents the context Γ extended with t and its type τ
//
// Typing rules for booleans
//
// Ø Γ true: Bool (T-True)
// Ø Γ false: Bool (T-False)
//
// Typing rules for integers
//
// Ø Γ n: Int (T-Int)
//
// Typing rules for variables
//
// x: τ ε Γ (T-Var)
// --------
// Γ ⊢ x : τ
//
// Typing rules for lambda abstractions
//
// Γ, x: τ ⊢ t: τ'
// -------------- (T-Abs)
// Γ ⊢ λx: τ. t: τ -> τ'
//
// Typing rules for applications
//
// Γ ⊢ t: τ -> τ'
// Γ ⊢ t': τ
// --------- (T-App)
// Γ ⊢ t t': τ'
//
// Typing rules for addition
//
// Γ ⊢ t: Int
// Γ ⊢ t': Int
// ----------- (T-Add)
// Γ ⊢ t + t': Int
//
// Typying rules for if-then-else
//
// Γ ⊢ t1: Bool
// Γ ⊢ t2: τ
// Γ ⊢ τ3: τ
// --------- (T-If)
// Γ ⊢ if t1 then t2 else t3: τ
//
// Typing rules for type abstractions
//
// Γ ⊢ t: τ
// -------- (T-TyAbs)
// Γ ⊢ ΛX. t: ∀X. τ
//
// The rule means if t has type τ, then ΛX. t has type τ
// for all types.
//
// Typing rules for type applications
//
// Γ ⊢ t: ∀X. τ
// ------------
// Γ ⊢ t τ': τ[X := τ']
//
// It substitues X with the type that the type abstraction
// is being applied to.
//
// Examples:
//
// id = ΛX. λx: X. x
// id Int
// id = λx: Int. x
//
// X[X := Int] -> Int
// (X -> X)[X := Bool] -> (Bool -> Bool)
// (X -> Y)[X := Int -> Bool] -> ((Int -> Bool) -> Y)
// (X -> (∀X.X))[X := Y] -> (Y -> (∀X.X))
use crate::ast::{Term, Type};
use std::collections::{HashMap, LinkedList};

#[derive(Debug, PartialEq)]
pub enum TypecheckerError {
  UndefinedVariable(String),
  TypeMismatch { expected: Type, got: Type },
  UnexpectedType(Type),
  ExpectedPolymorphicType(Type),
}

// https://www.cs.cornell.edu/courses/cs4110/2018fa/lectures/lecture15.pdf
//
// de Bruijn Notation
//
// One way to avoid the tricky interaction between free
// and bound names during substitution is to represent
// the variables in a way where their name does not matter.
//
// We can think of a bound variable as a pointer to the
// λ that binds it.
//
// For example in λx.λy.y x, the y points to the first λ
// and the x points to the second λ (counting from the last term).
//
// de Bruijn notation uses this idea as representation for λ
// expressions.
//
// An expression is defined as:
//
// e ::= n | λ.e | e e
//
// Variables are represented by integers n
// the refer to the index of the λ
// that binds the variable.
//
// Lambda abstractions have the form λ.e
// NOTE: the variable bound by the abstraction is not named
//
// Examples:
//
// Without de Bruijn       | With de Bruijn
// λx.x                    | λ.0
// λz.z                    | λ.0
// λx.λy.x                 | λ.λ.1
// λx.λy.λs.λz.x s (y s z) | λ.λ.λ.λ.3 1 (2 1 0)
// (λx.x x) (λx. x x)      | (λ.0 0) (λ 0 0)
// (λx.λx.x) (λy.y)        | (λ.λ.0) (λ.0)
fn type_to_debruijn(
  context: &mut LinkedList<String>,
  typ: &Type,
) -> Result<Type, TypecheckerError> {
  match typ {
    // We get the type variable index from the context,
    // and transform the type variable into
    // a de bruijn index.
    //
    // ∀X.λx: X. x ==> ∀.λx: 0. x
    Type::TypeVariable(x) => match context.iter().position(|type_var| type_var == x) {
      None => Err(TypecheckerError::UndefinedVariable(x.clone())),
      Some(i) => Ok(Type::DeBruijn(i)),
    },
    // If we reached a ∀X.λx: X. x for example,
    // we add X to the context.
    Type::Forall(type_var, typ) => {
      context.push_front(type_var.clone());

      Ok(Type::Forall(
        type_var.clone(),
        Box::new(type_to_debruijn(context, typ)?),
      ))
    }
    Type::Arrow(param_type, body_type) => Ok(Type::Arrow(
      Box::new(type_to_debruijn(context, param_type)?),
      Box::new(type_to_debruijn(context, body_type)?),
    )),
    Type::Bool => Ok(Type::Bool),
    Type::Int => Ok(Type::Int),
    Type::DeBruijn(_) => panic!("unexpected type {:?}", typ),
  }
}

fn named_to_debruijn_term(
  context: &mut LinkedList<String>,
  term: Term,
) -> Result<Term, TypecheckerError> {
  match term {
    Term::True => Ok(Term::True),
    Term::False => Ok(Term::False),
    Term::Int(x) => Ok(Term::Int(x)),
    Term::Var(x) => Ok(Term::Var(x)),
    Term::TypeAbs(type_var, term) => {
      context.push_front(type_var.clone());

      Ok(Term::TypeAbs(
        type_var,
        Box::new(named_to_debruijn_term(context, *term)?),
      ))
    }
    Term::TypeApp(type_abs, typ) => {
      let type_abs = named_to_debruijn_term(context, *type_abs)?;

      Ok(Term::TypeApp(
        Box::new(type_abs),
        type_to_debruijn(context, &typ)?,
      ))
    }
    Term::Abs {
      param,
      param_type,
      body,
    } => {
      let body = named_to_debruijn_term(context, *body)?;

      Ok(Term::Abs {
        param,
        param_type: type_to_debruijn(context, &param_type)?,
        body: Box::new(body),
      })
    }
    Term::App { function, arg } => Ok(Term::App {
      function: Box::new(named_to_debruijn_term(context, *function)?),
      arg: Box::new(named_to_debruijn_term(context, *arg)?),
    }),
    Term::Add(left, right) => Ok(Term::Add(
      Box::new(named_to_debruijn_term(context, *left)?),
      Box::new(named_to_debruijn_term(context, *right)?),
    )),
    Term::If {
      condition,
      consequence,
      alternative,
    } => Ok(Term::If {
      condition: Box::new(named_to_debruijn_term(context, *condition)?),
      consequence: Box::new(named_to_debruijn_term(context, *consequence)?),
      alternative: Box::new(named_to_debruijn_term(context, *alternative)?),
    }),
  }
}

fn debruijn_to_named_term(context: &LinkedList<String>, typ: Type) -> Type {
  match typ {
    Type::DeBruijn(i) => Type::TypeVariable(context.iter().nth(i).cloned().unwrap()),
    Type::Arrow(param_type, body_type) => Type::Arrow(
      Box::new(debruijn_to_named_term(context, *param_type)),
      Box::new(debruijn_to_named_term(context, *body_type)),
    ),
    Type::Forall(type_var, typ) => {
      Type::Forall(type_var, Box::new(debruijn_to_named_term(context, *typ)))
    }
    Type::Bool => Type::Bool,
    Type::Int => Type::Int,
    Type::TypeVariable(_) => panic!("unexpected type {:?}", typ),
  }
}

// Performs type substitution
//
// τ[X := τ']
//
// Examples:
//
// X[X := Int] -> Int
// (X -> X)[X := Bool] -> (Bool -> Bool)
// (X -> Y)[X := Int -> Bool] -> ((Int -> Bool) -> Y)
// (X -> (∀X.X))[X := Y] -> (Y -> (∀X.X))
fn subst(type_var_bruijn_index: usize, current_type: Type, new_type: Type) -> Type {
  match current_type {
    Type::Bool => Type::Bool,
    Type::Int => Type::Int,
    Type::Arrow(param_type, return_type) => Type::Arrow(
      Box::new(subst(type_var_bruijn_index, *param_type, new_type.clone())),
      Box::new(subst(type_var_bruijn_index, *return_type, new_type)),
    ),
    Type::DeBruijn(i) => {
      if i == type_var_bruijn_index {
        new_type
      } else {
        Type::DeBruijn(i)
      }
    }
    // ∀ binds a type variable.
    //
    // Given the following term:
    //
    // ∀X.∀Y.λx: X. λy: Y. x
    //
    //                  ∀X.∀Y.λx: X. λy: Y. x
    // When we are here ^
    //
    // The de bruijn index that represents X is 0.
    //
    // It looks like this:
    //
    // ∀X.∀Y.λx: 0. λy: Y. x
    //
    // But when we reach the second type variable
    //
    // ∀X.∀Y.λx: X. λy: Y. x
    //    ^ here
    //
    // The de bruijn index that represents Y is also 0.
    //
    // It looks like this:
    //
    // ∀X.∀Y.λx: 0. λy: 0. x
    //
    // Because of that we have two type variables
    // being referred by the same de bruijn index.
    //
    // To solve this:
    //
    // Y will be represented by 0 because it is the current
    // level.
    //
    // And type variables that came before Y, will have their
    // index increased by 1.
    //
    // After that we will have:
    //
    // ∀X.∀Y.λx: 1. λy: 0. x
    Type::Forall(x, typ) => {
      let new_type_with_de_bruijn_indices_increased = shift(0, 1, new_type);

      Type::Forall(
        x,
        Box::new(subst(
          type_var_bruijn_index + 1,
          *typ,
          new_type_with_de_bruijn_indices_increased,
        )),
      )
    }
    Type::TypeVariable(_) => unreachable!(),
  }
}

fn shift(cutoff: usize, de_bruijn_index: i32, typ: Type) -> Type {
  match typ {
    Type::Bool => Type::Bool,
    Type::Int => Type::Int,
    Type::Arrow(param_type, body_type) => Type::Arrow(
      Box::new(shift(cutoff, de_bruijn_index, *param_type)),
      Box::new(shift(cutoff, de_bruijn_index, *body_type)),
    ),
    // When we see ∀, we will increase the cutoff.
    //
    // ∀X.∀Y.λx: X. λy: Y. x
    // 1  1
    Type::Forall(type_var, typ) => {
      Type::Forall(type_var, Box::new(shift(cutoff + 1, de_bruijn_index, *typ)))
    }
    Type::DeBruijn(i) => {
      if i < cutoff {
        Type::DeBruijn(i)
      } else {
        Type::DeBruijn(if de_bruijn_index < 0 {
          i - 1
        } else {
          i + de_bruijn_index as usize
        })
      }
    }
    Type::TypeVariable(_) => unreachable!(),
  }
}

fn infer(context: &mut HashMap<String, Type>, term: &Term) -> Result<Type, TypecheckerError> {
  match term {
    Term::True | Term::False => Ok(Type::Bool),
    Term::Int(_) => Ok(Type::Int),
    Term::Var(x) => match context.get(x) {
      None => Err(TypecheckerError::UndefinedVariable(x.clone())),
      Some(typ) => Ok(typ.clone()),
    },
    Term::Abs {
      param,
      param_type,
      body,
    } => {
      context.insert(param.clone(), param_type.clone());
      let body_type = infer(context, body)?;
      Ok(Type::Arrow(
        Box::new(param_type.clone()),
        Box::new(body_type),
      ))
    }
    Term::App { function, arg } => {
      let function_type = infer(context, function)?;
      dbg!(&function_type);
      let arg_type = infer(context, arg)?;

      match function_type {
        Type::Arrow(from, to) => {
          if *from == arg_type {
            Ok(*to)
          } else {
            Err(TypecheckerError::TypeMismatch {
              expected: *from,
              got: arg_type,
            })
          }
        }
        typ => Err(TypecheckerError::UnexpectedType(typ)),
      }
    }
    Term::Add(a, b) => {
      let a_type = infer(context, a)?;
      let b_type = infer(context, b)?;

      match (a_type, b_type) {
        (Type::Int, Type::Int) => Ok(Type::Int),
        (a_type, b_type) => Err(TypecheckerError::TypeMismatch {
          expected: Type::Int,
          got: if a_type != Type::Int { a_type } else { b_type },
        }),
      }
    }
    Term::If {
      condition,
      consequence,
      alternative,
    } => {
      let condition_type = infer(context, condition)?;

      match &condition_type {
        Type::Bool => {
          let consequence_type = infer(context, consequence)?;
          let alternative_type = infer(context, alternative)?;

          if consequence_type != alternative_type {
            Err(TypecheckerError::TypeMismatch {
              expected: consequence_type,
              got: alternative_type,
            })
          } else {
            Ok(consequence_type)
          }
        }
        _ => Err(TypecheckerError::TypeMismatch {
          expected: Type::Bool,
          got: condition_type,
        }),
      }
    }
    Term::TypeAbs(type_var, abs) => Ok(Type::Forall(
      type_var.clone(),
      Box::new(infer(context, abs)?),
    )),
    Term::TypeApp(term, typ) => match infer(context, term)? {
      Type::Forall(_, forall_typ) => Ok(shift(
        0,
        -1,
        subst(0, *forall_typ, shift(0, 1, typ.clone())),
      )),
      typ => Err(TypecheckerError::ExpectedPolymorphicType(typ)),
    },
  }
}

pub fn type_of(term: Term) -> Result<Type, TypecheckerError> {
  let mut context = LinkedList::new();

  let de_bruijn_term = named_to_debruijn_term(&mut context, term.clone())?;

  dbg!(&de_bruijn_term);

  println!("de_bruijn({}) ==> {}", term, &de_bruijn_term,);

  let typ = infer(&mut HashMap::new(), &de_bruijn_term)?;

  dbg!(&typ);

  Ok(typ)

  // Ok(debruijn_to_named_term(&context, typ))
}
