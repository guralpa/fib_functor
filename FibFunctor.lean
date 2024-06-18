-- This module serves as the root of the `FibFunctor` library.
-- Import modules here that should be built as part of the library.
import «FibFunctor».Basic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Algebra.Group.Nat
import Mathlib.Data.Nat.Fib.Basic

universe u

namespace CategoryTheory

instance : Category.{0} ℕ where
  Hom A B := ULift (PLift (A ∣ B))
  id A := ⟨⟨dvd_refl A⟩⟩
  comp X Y := ⟨⟨dvd_trans X.down.down Y.down.down⟩⟩

def fib_functor : ℕ ⥤ ℕ where
  obj := Nat.fib
  map := by
    intro X Y h
    exact ⟨⟨Nat.fib_dvd X Y h.down.down⟩⟩
    -- TODO: prove fib_dvd yourself
  map_id := by
    intro a
    dsimp
    apply congrArg
    apply congrArg
    rfl
  map_comp := by
    intro a b c h h'
    dsimp
    apply congrArg
    apply congrArg
    rfl

def fib_entry (n k : ℕ) : ℕ :=
  if (Nat.fib k) % n = 0 then k
  else
  (fib_entry n (k + 1))
  decreasing_by {sorry}

lemma fib_entry_dvd (a : ℕ) : a ∣ fib_functor.obj (fib_entry a 1) := by
  sorry

instance : Limits.HasLimitsOfSize.{0, 0, 0, 0} ℕ where
  has_limits_of_shape := by
    intro J h
    exact {has_limit := fun F ↦ {exists_limit := ⟨by sorry, by sorry⟩}}

instance : Limits.PreservesLimitsOfSize fib_functor where
  preservesLimitsOfShape := by
    sorry

lemma nat_is_simple (A B : Nat) (f g : A ⟶ B) : f = g := by
  have h := f.down.down
  have h' := g.down.down
  have h'' : h = h' := rfl
  sorry

lemma fib_solset : SolutionSetCondition.{0} fib_functor := by
  rw [SolutionSetCondition]
  intro a
  use ℕ
  use fun i ↦ (fib_entry a 1)
  use fun i ↦ ⟨⟨fib_entry_dvd a⟩⟩
  intro X h
  use 1
  have h' : (fib_entry a 1) ∣ X := by
    sorry
  use ⟨⟨h'⟩⟩
  apply nat_is_simple a (fib_functor.obj X)

set_option pp.all true

theorem fib_has_left_adjoint : Functor.IsRightAdjoint.{0, 0} fib_functor :=
  isRightAdjoint_of_preservesLimits_of_solutionSetCondition fib_functor fib_solset
