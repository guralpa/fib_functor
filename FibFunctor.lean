-- This module serves as the root of the `FibFunctor` library.
-- Import modules here that should be built as part of the library.
import «FibFunctor».Basic
import «FibFunctor».GenFib
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

/-
lemma fib_pair_repeats_mod_m (m : ℕ) (mne : m ≠ 0): ∃ n, ∃ k ≠ 0, (fib_mod_m m) n = (fib_mod_m m ) n + k ∧ (fib_mod_m m) n + 1 = (fib_mod_m m ) n + 1 + k := by
  let fib_pairs := (List.map (fun n => (Nat.pair (Nat.fib n) (Nat.fib (n+ 1)))) (List.iota (m^2 - 1)))
  sorry -/
/-
lemma prime_mul_dvd_fib_mul (pf : List ℕ) (hp : ∀ p, p ∈ pf → Prime p) : ∃ N, (pf.prod) ∣ (Nat.fib N) :=
  match pf with
  |  [] => by
    use 1
    rw [List.prod_nil]
    simp
  |  p::r =>
      let h := (List.mem_cons_self p r)
      let ih := (prime_mul_dvd_fib_mul r fun rp hr => (hp rp (List.mem_cons_of_mem p hr))) -/

/-
def prime_of_pf (pf : List ℕ) (hp : p ∈ pf → Prime p) : (List Prime ℕ) :=
  match pf with
  |  [] => []
  |  p::r =>
      let h := (List.mem_cons_self p r)
      (hp h)::(prime_of_pf r fun hr => (hp (List.mem_cons_of_mem hr))) -/

/-
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
    sorry -/

def fib_mod (m : ℕ) : ℕ → Fin (m + 1) := fun n => Fin.ofNat (Nat.fib n)

lemma fib_mod_add_two (m : ℕ) {n : ℕ}: (fib_mod m) (n + 2) = ((fib_mod m) n) + ((fib_mod m) (n + 1)) := by
  dsimp [fib_mod, Fin.ofNat]
  rw [Fin.add_def]
  simp [Sigma.mk.inj_iff, Nat.fib_add]

lemma fib_mod_add_one (m : ℕ) {n : ℕ} (h : n ≠ 0): (fib_mod m) (n - 1) = ((fib_mod m) (n + 1)) - ((fib_mod m) (n)) := by
  dsimp [fib_mod, Fin.ofNat]
  rw [Fin.sub_def]
  simp [Sigma.mk.inj_iff]
  rw [← Nat.add_sub_assoc, Nat.add_comm ((n + 1).fib), Nat.add_sub_assoc]
  simp
  have : (n - 1).fib = (n + 1).fib - n.fib := by simp [Nat.fib_add_one h]
  simp [this]
  sorry

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
    have ⟨n, xeqn⟩ : ∃n, x = k - n := by
      have ⟨n, keq⟩ := Nat.exists_eq_add_of_le xle
      use n
      norm_num [keq]
    rw [xeqn, ← Nat.add_sub_assoc _, ← Nat.sub_add_comm _, Nat.add_comm k l, Nat.sub_add_comm]
    simp
    induction' n using Nat.twoStepInduction with a h1 h2
    · simp [hkl]
    · have h : (fib_mod m) (l - 1) = (fib_mod m ) (l + 1) - ((fib_mod m ) l) := by
        have h' : (fib_mod m) (l - 1) ≤ (fib_mod m) l := by sorry
        rw [Eq.comm]
        sorry
      have h' : (fib_mod m) (k - 1) = (fib_mod m ) (k + 1) - ((fib_mod m ) k) := by
        have h' : (fib_mod m) (k - 1) ≤ (fib_mod m) k := by sorry
        rw [Eq.comm]
        sorry
      simp [h, h']
      rw [hkl, hkl']
    · simp [Nat.succ]
      sorry
    sorry
  · sorry


#check Fintype.exists_ne_map_eq_of_card_lt
-- try one of the type-y versions
-- set_option pp.analyze true
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

namespace Nat

lemma fib_entry_gcd (n m : ℕ) : fib_entry (Nat.gcd m n) = Nat.gcd (fib_entry m) (fib_entry n) := by
  induction' m, n using Nat.gcd.induction with a m n h h'
  · dsimp [fib_entry]
    simp
  · dsimp [fib_entry]
    rw [← Nat.gcd_rec m n] at h'
    have mne : m ≠ 0 := by intro h''; rw [Eq.comm] at h''; apply Nat.ne_of_lt h h''
    simp [mne]
    have h'' : m.gcd n ≠ 0 := Nat.gcd_ne_zero_left mne
    simp [h'']
    conv_rhs => simp [mne]
    -- conv_rhs => rw [← Nat.mod_add_div' n m]
    by_cases neq : n = 0
    · simp [neq]
    · simp [neq]
      sorry


lemma fib_entry_dvd (n m : ℕ) (h : n ∣ m) : fib_entry n ∣ fib_entry m := by
  sorry

#eval fib_entry 1 -- how to use? rfl won't work
lemma fib_entry_one : fib_entry 1 = 1 := by
  native_decide

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
