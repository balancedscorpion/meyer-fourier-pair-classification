module

public import MeyerGeneralProblem.Carrier.TwoSided
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Set.Card

@[expose] public section

/-!
# Open-window counts from eventual consecutive-gap bounds

An increasing natural sequence escaping to positive infinity has finite bounded
window preimages. Once its consecutive gaps are bounded by `ell`, every open
window to the right of the initial tail node contains at least its length divided
by `ell`, less the necessary endpoint loss of one. No positivity assumption on
the nodes and no density or counting assumption is imposed.
-/

open Filter Set

namespace MeyerGeneralProblem

/-- A strictly increasing natural sequence escaping to positive infinity has
only finitely many indices in any bounded open real interval. -/
theorem finite_indices_in_Ioo_of_strictMono_tendsto {z : ℕ → ℝ}
    (hzmono : StrictMono z) (hztop : Tendsto z atTop atTop) (a b : ℝ) :
    {n : ℕ | a < z n ∧ z n < b}.Finite := by
  obtain ⟨hi, hhi⟩ := (hztop.eventually (eventually_ge_atTop b)).exists
  apply (Set.finite_Iio hi).subset
  intro n hn
  change n < hi
  by_contra h
  have hle := hzmono.monotone (le_of_not_gt h)
  exact (not_lt_of_ge (hhi.trans hle)) hn.2

/-- The full preimage of an open window beyond an eventual bounded-gap tail
satisfies the sharp finite endpoint-loss estimate. Empty interiors and endpoints
that are nodes require no additional assumptions. -/
theorem openInterval_count_ge_of_eventual_gap {z : ℕ → ℝ}
    (hzmono : StrictMono z) (hztop : Tendsto z atTop atTop)
    {ell : ℝ} (hell : 0 < ell) (N₀ : ℕ)
    (hgap : ∀ n ≥ N₀, z (n + 1) - z n ≤ ell)
    {a b : ℝ} (ha : z N₀ ≤ a) (hab : a < b) :
    b - a ≤ ell * (({n : ℕ | a < z n ∧ z n < b}.ncard : ℝ) + 1) := by
  classical
  have hright : ∃ n : ℕ, a < z n :=
    (hztop.eventually (eventually_gt_atTop a)).exists
  let k : ℕ := Nat.find hright
  have hk : a < z k := Nat.find_spec hright
  have hNk : N₀ < k := hzmono.lt_iff_lt.mp (ha.trans_lt hk)
  let p : ℕ := k - 1
  have hpk : p + 1 = k := by dsimp [p]; omega
  have hNp : N₀ ≤ p := by dsimp [p]; omega
  have hp : z p ≤ a := by
    exact le_of_not_gt (Nat.find_min hright (show p < Nat.find hright by
      change p < k
      omega))
  have hpnext : a < z (p + 1) := by simpa only [hpk] using hk
  have hupper : ∃ n : ℕ, b ≤ z n :=
    (hztop.eventually (eventually_ge_atTop b)).exists
  let q : ℕ := Nat.find hupper
  have hq : b ≤ z q := Nat.find_spec hupper
  have hqmin (n : ℕ) (hn : n < q) : z n < b :=
    lt_of_not_ge (Nat.find_min hupper hn)
  have hpq : p < q := hzmono.lt_iff_lt.mp (hp.trans_lt (hab.trans_le hq))
  have hindices : {n : ℕ | a < z n ∧ z n < b} = (Finset.Ioo p q : Set ℕ) := by
    ext n
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_Ioo]
    constructor
    · intro hn
      exact ⟨hzmono.lt_iff_lt.mp (hp.trans_lt hn.1),
        hzmono.lt_iff_lt.mp (hn.2.trans_le hq)⟩
    · intro hn
      exact ⟨hpnext.trans_le (hzmono.monotone (by omega)), hqmin n hn.2⟩
  have hsum : z q - z p ≤ (q - p : ℕ) * ell := by
    calc
      z q - z p = ∑ n ∈ Finset.Ico p q, (z (n + 1) - z n) :=
        (Finset.sum_Ico_sub z hpq.le).symm
      _ ≤ ∑ _n ∈ Finset.Ico p q, ell := by
        apply Finset.sum_le_sum
        intro n hn
        exact hgap n (hNp.trans (Finset.mem_Ico.mp hn).1)
      _ = (q - p : ℕ) * ell := by simp
  have hcard : (q - p : ℕ) = (Finset.Ioo p q).card + 1 := by
    rw [Nat.card_Ioo]
    omega
  calc
    b - a ≤ z q - z p := sub_le_sub hq hp
    _ ≤ (q - p : ℕ) * ell := hsum
    _ ≤ ell * (({n : ℕ | a < z n ∧ z n < b}.ncard : ℝ) + 1) := by
      rw [mul_comm ell]
      apply mul_le_mul_of_nonneg_right _ hell.le
      rw [hindices, Set.ncard_coe_finset, hcard, Nat.cast_add, Nat.cast_one]

end MeyerGeneralProblem
