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
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.Pairing
import Mathlib.Algebra.Periodic
import Mathlib.Data.Finset.Card
import Init.Core

universe u

namespace CategoryTheory

-- Defining the category structure directly:

instance : Category.{0} ℕ where
  Hom A B := ULift (PLift (A ∣ B))
  id A := ⟨⟨dvd_refl A⟩⟩
  comp X Y := ⟨⟨dvd_trans X.down.down Y.down.down⟩⟩

-- Using the category structure of a preorder

instance : Preorder ℕ where
  le := fun n m => n ∣ m
  lt := fun n m => n ∣ m ∧ n ≠ m
  le_refl := fun n => dvd_rfl
  le_trans := fun n m k => dvd_trans
  lt_iff_le_not_le := by
    intro n m
    constructor
    · simp
      intro h
      contrapose!
      intro h'
      have h' := h' h
      exact (dvd_antisymm h h')
    · simp
      intro h
      contrapose!
      intro h'
      have h' := h' h
      rw [h']

instance : Category.{0} ℕ := Preorder.smallCategory ℕ

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

lemma fib_dvd_mul (n m : ℕ) : (Nat.fib n) ∣ (Nat.fib (n * m)) := by
  induction' m with k ih
  · simp
  · rw [mul_add, mul_one]
    by_cases h' : 1 ≤ n
    · have h : n * k + n = n * k + (n - 1) + 1 := by
        rw [add_assoc, Nat.sub_add_cancel]
        exact h'
      rw [h]
      rw [Nat.fib_add]
      apply dvd_add
      · apply dvd_mul_of_dvd_left ih
      · have p : n = n - 1 + 1 := by
          rw [Nat.sub_add_cancel]
          apply h'
        rw [← p]
        apply dvd_mul_left n.fib
    · push_neg at h'
      have p : n = 0 := (Nat.lt_one_iff.1 h')
      rw [p]
      simp

lemma fib_prime_entry_exists (p : ℕ) (pp : Nat.Prime p) :  ∃k, p ∣ (Nat.fib k) := by
  sorry

def fib_prime_entry (n: ℕ) (pn : Nat.Prime n) : ℕ :=
  Nat.find (fib_prime_entry_exists n pn)

theorem fib_entry_exists (n : ℕ) : ∃k, n ∣ (Nat.fib k) := by
  by_cases h : n = 0
  · rw [h]
    simp
  · have h : n ≠ 0 := by simp [h]
    let pf := Nat.factors n
    have h' : n ∣ pf.prod := by
      dsimp [pf]
      rw [Nat.prod_factors h]
    -- need to figure out membership proof as part of map
    let pe := pf.map fun n => (fib_prime_entry n _)
    sorry


def fib_entry (n: ℕ) : ℕ :=
  Nat.find (fib_entry_exists n)

lemma fib_entry_dvd (n : ℕ) : n ∣ (Nat.fib (fib_entry n)) := by
  rw [fib_entry]
  apply (Nat.find_spec (fib_entry_exists n))

instance : Limits.HasLimitsOfSize.{0, 0, 0, 0} ℕ where
  has_limits_of_shape := by
    intro J h
    exact {has_limit :=
      fun F ↦ {exists_limit :=
        ⟨by sorry, by sorry⟩}}

lemma nat_is_simple (A B : Nat) (f g : A ⟶ B) : f = g := by
  apply Subsingleton.elim (α := ULift (PLift (A ∣ B)))

instance : Limits.PreservesLimitsOfSize fib_functor where
  preservesLimitsOfShape := by
    intro J inst
    constructor
    intro K
    constructor
    intro c h
    constructor
    · intro s j
      apply nat_is_simple
    · intro s m j
      apply nat_is_simple
    · intro s
      simp
      have h : s.pt ∣ fib_functor.obj c.pt := by
        dsimp [fib_functor]
        sorry
      exact ⟨⟨h⟩⟩

lemma fib_solset : SolutionSetCondition.{0} fib_functor := by
  rw [SolutionSetCondition]
  intro a
  use ℕ
  use fun i ↦ (fib_entry a)
  use fun i ↦ ⟨⟨dvd_fib_fib_entry a⟩⟩
  intro X h
  use 1
  have h' := h.down.down
  have h'' : (fib_entry a) ∣ X := by
    have h'' := fib_entry_dvd a (Nat.fib X) h'
    by_cases xeq : X = 0
    · rw [xeq]
      simp
    · by_cases xeq' : X = 1
      · rw [xeq'] at h'
        have h' := Nat.dvd_one.1 h'
        rw [h']
        rw [fib_entry_one]
        simp
      · have xge : 2 ≤ X := by sorry
        have H : fib_entry X.fib = X := by
          norm_num [fib_entry, xeq]
          have ⟨k, ⟨kne, fe_ex⟩⟩ := (fib_nonzero_entry_exists X xeq)
          sorry
        rw [H] at h''
        exact h''
  use ⟨⟨h''⟩⟩
  apply nat_is_simple a (fib_functor.obj X)

set_option pp.all true

theorem fib_has_left_adjoint : Functor.IsRightAdjoint.{0, 0} fib_functor :=
  isRightAdjoint_of_preservesLimits_of_solutionSetCondition fib_functor fib_solset

def fib_entry_functor : ℕ ⥤ ℕ where
  obj := fib_entry
  map := by
    intro X Y h
    exact ⟨⟨fib_entry_dvd X Y h.down.down⟩⟩
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

-- Eventually eventually: Show adjunction between these two
instance : Adjunction fib_entry_functor fib_functor where
  homEquiv := by sorry
  unit := by sorry
  counit := by sorry
