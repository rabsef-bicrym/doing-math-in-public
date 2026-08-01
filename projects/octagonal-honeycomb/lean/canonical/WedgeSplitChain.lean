import Mathlib

/-!
# Iterating a local tangent-wedge split

The geometric fan refinement inserts several octagonal sector normals into one
large normal gap.  This module isolates the finite induction: whenever every
intermediate point satisfies the three-point split inequality, the sum of all
refined wedge contributions is at most the original endpoint wedge.
-/

namespace WedgeSplitChain

variable {α : Type*}

/-- Endpoint of a path whose first vertex is supplied separately. -/
def endpoint (first : α) : List α → α
  | [] => first
  | x :: xs => endpoint x xs

/-- Sum of pair costs along a finite path. -/
def pathCost (w : α → α → ℝ) (first : α) : List α → ℝ
  | [] => 0
  | x :: xs => w first x + pathCost w x xs

@[simp] lemma endpoint_nil (a : α) : endpoint a [] = a := rfl
@[simp] lemma endpoint_cons (a b : α) (xs : List α) :
    endpoint a (b :: xs) = endpoint b xs := rfl
@[simp] lemma pathCost_nil (w : α → α → ℝ) (a : α) : pathCost w a [] = 0 := rfl
@[simp] lemma pathCost_cons (w : α → α → ℝ) (a b : α) (xs : List α) :
    pathCost w a (b :: xs) = w a b + pathCost w b xs := rfl

/-- Abstract transitive split inequality along a path. -/
theorem pathCost_le_direct
    (w : α → α → ℝ)
    (hsplit : ∀ a b c, w a b + w b c ≤ w a c)
    (a b : α) (xs : List α) :
    pathCost w a (b :: xs) ≤ w a (endpoint b xs) := by
  induction xs generalizing a b with
  | nil => simp
  | cons c cs ih =>
      calc
        pathCost w a (b :: c :: cs) =
            w a b + pathCost w b (c :: cs) := by rfl
        _ ≤ w a b + w b (endpoint c cs) := by
          gcongr
          exact ih b c
        _ ≤ w a (endpoint c cs) := hsplit a b (endpoint c cs)
        _ = w a (endpoint b (c :: cs)) := rfl

/-- Reversing the previous inequality gives the area statement in its usual
form: the original wedge dominates the sum of all refined wedges. -/
theorem direct_ge_pathCost
    (w : α → α → ℝ)
    (hsplit : ∀ a b c, w a b + w b c ≤ w a c)
    (a b : α) (xs : List α) :
    pathCost w a (b :: xs) ≤ w a (endpoint b xs) :=
  pathCost_le_direct w hsplit a b xs

end WedgeSplitChain
