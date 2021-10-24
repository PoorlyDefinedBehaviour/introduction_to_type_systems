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
use crate::ast::{Term, Type};
use std::collections::HashMap;

#[derive(Debug, PartialEq)]
pub enum TypecheckerError {
  UndefinedVariable(String),
  TypeMismatch { expected: Type, got: Type },
  UnexpectedType(Type),
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
        _ => Err(TypecheckerError::UnexpectedType(function_type)),
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
        Type::Arrow(_, _) | Type::Int => Err(TypecheckerError::TypeMismatch {
          expected: Type::Bool,
          got: condition_type,
        }),
      }
    }
  }
}

pub fn type_of(term: &Term) -> Result<Type, TypecheckerError> {
  infer(&mut HashMap::new(), term)
}
