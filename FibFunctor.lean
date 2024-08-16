-- This module serves as the root of the `FibFunctor` library.
-- Import modules here that should be built as part of the library.
import «FibFunctor».Basic
-- import «FibFunctor».GenFib
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
import Mathlib.Data.Finite.Card
import Mathlib.Order.Monotone.Basic
import Init.Core

universe u


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

def fib_mod (m : ℕ) : ℕ → Fin (m + 1) := fun n => Fin.ofNat (Nat.fib n)

lemma fib_mod_add_two (m : ℕ) {n : ℕ}: (fib_mod m) (n + 2) = ((fib_mod m) n) + ((fib_mod m) (n + 1)) := by
  dsimp [fib_mod, Fin.ofNat]
  rw [Fin.add_def]
  simp [Sigma.mk.inj_iff, Nat.fib_add]

lemma mod_sub_mod_mod (m n k : ℕ) (h : n ≤ k) : (k - (n % m)) % m = (k - n) % m := by
  sorry

-- set_option pp.analyze true

lemma fib_mod_add_one (m : ℕ) (n : ℕ) (h : n ≠ 0): (fib_mod m) (n - 1) = ((fib_mod m) (n + 1)) - ((fib_mod m) (n)) := by
  dsimp [fib_mod, Fin.ofNat]
  rw [Fin.sub_def]
  simp [Sigma.mk.inj_iff]
  rw [← Nat.add_sub_assoc, Nat.add_comm ((n + 1).fib), Nat.add_sub_assoc]
  simp
  have : (n - 1).fib = (n + 1).fib - n.fib := by simp [Nat.fib_add_one h]
  simp [this]
  rw [mod_sub_mod_mod]
  apply Monotone.imp Nat.fib_mono (Nat.le_succ n)
  apply Nat.le_trans _ (Monotone.imp Nat.fib_mono (Nat.le_succ n))
  simp [Nat.mod_le]
  have h' : m + 1 > 0 := by norm_num
  apply Nat.le_of_lt (Nat.mod_lt (Nat.fib n) h')

def fib_mod_pair (m : ℕ) : ℕ → (Fin (m + 1)) × (Fin (m + 1)) := fun n => ((fib_mod m) n, (fib_mod m) (n + 1))

theorem fib_mod_m_periodic (m : ℕ) : ∃p, p ≠ 0 ∧ (fib_mod m).Periodic p := by
  dsimp
  let pairs_mod_m := (Fin (m + 1)) × (Fin (m + 1))
  have ⟨k, l, hne, heq⟩ : ∃x, ∃y, x ≠ y ∧ (fib_mod_pair m) x = (fib_mod_pair m) y := Finite.exists_ne_map_eq_of_infinite (fib_mod_pair m)
  dsimp [fib_mod_pair] at heq
  let ⟨hkl, hkl'⟩ := (Prod.mk.inj_iff.1 heq)
  by_cases kle : k ≤ l
  · use l - k
    constructor
    · contrapose! hne
      rw [← Nat.zero_add k, eq_comm]
      apply Nat.eq_add_of_sub_eq kle hne
    intro x
    by_cases xle : x ≤ k
    · have ⟨n, xeqn, nle⟩ : ∃n, x = k - n ∧ n ≤ k := by
        have ⟨n, keq⟩ := Nat.exists_eq_add_of_le xle
        use n
        norm_num [keq]
      rw [xeqn, ← Nat.add_sub_assoc _, ← Nat.sub_add_comm _, Nat.add_comm k l, Nat.sub_add_comm]
      simp
      induction' n using Nat.twoStepInduction with a h1 h2
      · simp [hkl]
      · have h : (fib_mod m) (l - 1) = (fib_mod m ) (l + 1) - ((fib_mod m ) l) := by
          apply fib_mod_add_one m l
          linarith
        have h' : (fib_mod m) (k - 1) = (fib_mod m ) (k + 1) - ((fib_mod m ) k) := by
          apply fib_mod_add_one m k
          linarith
        simp [h, h']
        rw [hkl, hkl']
      · simp [Nat.succ]
        simp [Nat.sub_add_eq]
        sorry
      · apply Nat.le_trans nle kle
      · apply nle
      · apply kle
    · sorry
  · sorry

theorem fib_nonzero_entry_exists (n : ℕ) (hn : n ≠ 0): ∃k ≠ 0, n ∣ (Nat.fib k) := by
  have hp : ∀m, ∃k ≠ 0, (fib_mod (n - 1)) m = (fib_mod (n - 1)) (m + k) := by
    intro m
    have ⟨p, ⟨pne, pp⟩⟩ := (fib_mod_m_periodic (n - 1))
    use p
    dsimp at pp
    simp [fib_mod_m_periodic (n - 1), pne, pp]
  have ⟨k, hk1, hk2⟩ : ∃k ≠ 0, (fib_mod (n - 1)) k = (Fin.ofNat 0) := by
    have ⟨k, hk1, hk2⟩ := (hp 0)
    simp! at hk1
    dsimp[fib_mod] at hk2
    norm_num at hk2
    dsimp[fib_mod]
    rw[eq_comm] at hk2
    use k
  use k;
  dsimp[fib_mod] at hk2
  use hk1
  apply Nat.dvd_of_mod_eq_zero
  dsimp [Fin.ofNat] at hk2
  have : n - 1 + 1 = n := by
    apply Nat.sub_add_cancel
    simp [Nat.one_le_iff_ne_zero, hn]
  simp [this] at hk2
  apply Fin.val_eq_of_eq hk2

def fib_entry (n: ℕ) : ℕ :=
  if h : n ≠ 0 then Nat.find (fib_nonzero_entry_exists n h)
  else 0

lemma dvd_fib_fib_entry (n : ℕ) : n ∣ (Nat.fib (fib_entry n)) := by
  rw [fib_entry]
  by_cases h : n ≠ 0
  · simp[h]
    apply (Nat.find_spec (fib_nonzero_entry_exists n h)).2
  · simp[h]

lemma fib_entry_exists' (n : ℕ) : ∃k, n ∣ Nat.fib k := by
  use fib_entry n
  apply dvd_fib_fib_entry n

#eval List.map (fib_mod 2) (List.iota 15)

lemma fib_mod_zero_of_dvd_fib (m n : ℕ) : m ≠ 0 → (m ∣ Nat.fib n ↔ (fib_mod (m - 1)) n = 0) := by
  intro h
  have : m - 1 + 1 = m := by
      apply Nat.sub_add_cancel
      simp [Nat.one_le_iff_ne_zero, h]
  constructor
  · intro h'
    dsimp [fib_mod, Fin.ofNat]
    simp [this, Nat.mod_eq_zero_of_dvd h']
  · intro h'
    dsimp [fib_mod, Fin.ofNat] at h'
    simp [this] at h'
    apply Nat.dvd_of_mod_eq_zero
    apply Fin.val_eq_of_eq h'

lemma fib_mod_zero_add (m n k : ℕ) (h : fib_mod m n = 0) (h' : fib_mod m k = 0) : fib_mod m (n + k) = 0 := by
  sorry

lemma fib_entry_dvd_of_fib_mod_zero (m n : ℕ) (mne : m ≠ 0) (h : fib_mod (m - 1) n = 0) : fib_entry m ∣ n := by
  sorry

lemma fib_entry_dvd_iff_dvd_fib (m n : ℕ) : ((fib_entry m) ∣ n) ↔ m ∣ (Nat.fib n) := by
  constructor
  · intro h
    have : Nat.fib (fib_entry m) ∣ Nat.fib n := Nat.fib_dvd (fib_entry m) n h
    apply Nat.dvd_trans (dvd_fib_fib_entry m) this
  · intro h
    by_cases meq : m = 0
    · dsimp [fib_entry]
      simp [meq]
      rw [meq] at h
      apply Nat.fib_eq_zero.1
      apply Nat.eq_zero_of_zero_dvd h
    · have := (fib_mod_zero_of_dvd_fib m n meq).1 h
      apply fib_entry_dvd_of_fib_mod_zero
      push_neg at meq; exact meq; exact this

theorem fib_entry_dvd (m n : ℕ) (h : m ∣ n) : fib_entry m ∣ fib_entry n := by
  apply (fib_entry_dvd_iff_dvd_fib m (fib_entry n)).2
  apply Nat.dvd_trans h (dvd_fib_fib_entry n)

lemma fib_entry_one : fib_entry 1 = 1 := by
  native_decide

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

lemma nat_is_simple (A B : Nat) (f g : A ⟶ B) : f = g := by
  apply Subsingleton.elim (α := ULift (PLift (A ∣ B)))

instance : Limits.HasLimitsOfSize.{0, 0, 0, 0} ℕ where
  has_limits_of_shape := by
    intro J h
    constructor
    intro F
    constructor
    constructor
    constructor
    · constructor
      · intro s j
        apply nat_is_simple
      · intro s m j
        apply nat_is_simple
      · intro s
        constructor
        have nt := s.π
        have C := ?has_limit.exists_limit.val.cone
        sorry
    · constructor
      constructor
      · intro X Y f
        apply nat_is_simple
      · intro X
        sorry
      · sorry

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
    apply (fib_entry_dvd_iff_dvd_fib a X).2 h'
  use ⟨⟨h''⟩⟩
  apply nat_is_simple a (fib_functor.obj X)

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
