module

public import MeyerGeneralProblem.Carrier.FiniteModificationDensity
public import Mathlib.Algebra.Order.Floor.Ring

@[expose] public section

/-!
# Uniform upper density from strict separation

A globally `d`-separated locally finite carrier has upper uniform density at
most `1 / d`.  The formulation below retains a strict margin when `1 < d`;
this is the counting bridge needed by the signed-square subcritical regime.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set

namespace LocallyFiniteCarrier

/-- A `d`-separated carrier has at most `floor (L / d) + 1` points in any
positive half-open window of length `L`. -/
theorem windowCount_le_natFloor_div_add_one_of_separated
    (S : LocallyFiniteCarrier) {d : ℝ} (hd : 0 < d)
    (hsep : ∀ x ∈ S.carrier, ∀ y ∈ S.carrier, x ≠ y → d ≤ |x - y|)
    {a L : ℝ} (_hL : 0 ≤ L) :
    windowCount S a L ≤ ⌊L / d⌋₊ + 1 := by
  unfold windowCount
  let source : Set ℝ := S.carrier ∩ Set.Ico a (a + L)
  let target : Set ℕ := (Finset.range (⌊L / d⌋₊ + 1) : Set ℕ)
  let bin : ℝ → ℕ := fun x ↦ ⌊(x - a) / d⌋₊
  have hmap : ∀ x ∈ source, bin x ∈ target := by
    intro x hx
    have hx0 : 0 ≤ (x - a) / d := div_nonneg (sub_nonneg.mpr hx.2.1) hd.le
    have hxL : (x - a) / d ≤ L / d := by
      apply div_le_div_of_nonneg_right _ hd.le
      linarith [hx.2.2]
    simp only [bin, target, Finset.mem_coe, Finset.mem_range]
    exact Nat.lt_succ_of_le (Nat.floor_mono hxL)
  have hinj : Set.InjOn bin source := by
    intro x hx y hy hbin
    by_contra hxy
    have hx0 : 0 ≤ (x - a) / d := div_nonneg (sub_nonneg.mpr hx.2.1) hd.le
    have hy0 : 0 ≤ (y - a) / d := div_nonneg (sub_nonneg.mpr hy.2.1) hd.le
    have hfloor : ⌊(x - a) / d⌋ = ⌊(y - a) / d⌋ := by
      rw [← Int.natCast_floor_eq_floor hx0,
        ← Int.natCast_floor_eq_floor hy0]
      exact_mod_cast hbin
    have hclose := Int.abs_sub_lt_one_of_floor_eq_floor hfloor
    have hclose' : |x - y| < d := by
      rw [show (x - a) / d - (y - a) / d = (x - y) / d by ring,
        abs_div, abs_of_pos hd, div_lt_one hd] at hclose
      exact hclose
    exact (not_lt_of_ge (hsep x hx.1 y hy.1 hxy)) hclose'
  have hcard := Set.ncard_le_ncard_of_injOn bin hmap hinj
    (show target.Finite by simp [target])
  simpa only [source, target, Set.ncard_coe_finset, Finset.card_range] using hcard

/-- A carrier separated by a distance strictly larger than one has strict
upper uniform density below one. -/
theorem uniformUpperDensityLT_one_of_separated
    (S : LocallyFiniteCarrier) {d : ℝ} (hd : 1 < d)
    (hsep : ∀ x ∈ S.carrier, ∀ y ∈ S.carrier, x ≠ y → d ≤ |x - y|) :
    UniformUpperDensityLT S 1 := by
  have hd0 : 0 < d := zero_lt_one.trans hd
  let ε : ℝ := (1 - 1 / d) / 2
  have hε : 0 < ε := by
    dsimp [ε]
    have : 1 / d < 1 := (div_lt_one hd0).2 hd
    linarith
  refine ⟨ε, hε, max 1 (1 / ε), zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro L hL a
  have hL0 : 0 ≤ L := (zero_lt_one.trans_le ((le_max_left _ _).trans hL)).le
  have hcountNat := S.windowCount_le_natFloor_div_add_one_of_separated
    hd0 hsep (a := a) hL0
  have hfloor : (⌊L / d⌋₊ : ℝ) ≤ L / d :=
    Nat.floor_le (div_nonneg hL0 hd0.le)
  have hcount : (windowCount S a L : ℝ) ≤ L / d + 1 := by
    have hcountCast :
        (windowCount S a L : ℝ) ≤ (⌊L / d⌋₊ : ℝ) + 1 := by
      exact_mod_cast hcountNat
    linarith
  have hlarge : 1 / ε ≤ L := (le_max_right _ _).trans hL
  have hone : 1 ≤ ε * L := by
    calc
      1 = ε * (1 / ε) := by field_simp
      _ ≤ ε * L := mul_le_mul_of_nonneg_left hlarge hε.le
  calc
    (windowCount S a L : ℝ) ≤ L / d + 1 := hcount
    _ = (1 / d) * L + 1 := by ring
    _ ≤ (1 / d) * L + ε * L := by linarith
    _ = (1 - ε) * L := by
      dsimp [ε]
      ring

end LocallyFiniteCarrier

end

end MeyerGeneralProblem
