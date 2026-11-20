module

public import MeyerGeneralProblem.Distribution.FiniteCombConvolutionSupport
public import MeyerGeneralProblem.Distribution.IntegerComb
public import MeyerGeneralProblem.Distribution.OriginalWeightedSchwartzC0
public import MeyerGeneralProblem.Distribution.SchwartzSeries
public import Mathlib.Data.Nat.Pairing
public import Mathlib.Analysis.Normed.Ring.InfiniteSum

@[expose] public section

/-!
# Boundedly weighted affine quadrants on the real line

Two positive steps projected in the same direction give a locally finite
point set. The distribution uses the absolutely convergent sum over the
original quadrant indices, adding any coincident atoms automatically.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set SchwartzMap
open scoped SchwartzMap

/-- The real position of a quadrant index, before translating the origin. -/
def quadrantNode (d a b : ℝ) (p : ℕ × ℕ) : ℝ :=
  d * (a * (p.1 : ℝ) + b * (p.2 : ℝ))

private theorem abs_quadrantNode (d a b : ℝ) (hd : |d| = 1) (ha : 0 < a) (hb : 0 < b)
    (p : ℕ × ℕ) :
    |quadrantNode d a b p| = a * (p.1 : ℝ) + b * (p.2 : ℝ) := by
  rw [quadrantNode, abs_mul, hd, one_mul, abs_of_nonneg (by positivity)]

/-- The full image of one quadrant is locally finite, even if some
indices coincide at a real atom. -/
def quadrantCarrier (d a b : ℝ) (hd : |d| = 1) (ha : 0 < a) (hb : 0 < b) :
    LocallyFiniteCarrier where
  carrier := Set.range (quadrantNode d a b)
  finite_inter_Icc l r := by
    let c := min a b
    let M := ⌈(|l| + |r|) / c⌉₊
    have hc : 0 < c := lt_min ha hb
    apply (((Set.finite_Iic M).prod (Set.finite_Iic M)).image (quadrantNode d a b)).subset
    rintro x ⟨⟨p, rfl⟩, hx⟩
    have hsize : |quadrantNode d a b p| ≤ |l| + |r| := by
      apply abs_le.mpr
      constructor
      · linarith [hx.1, neg_abs_le l, abs_nonneg r]
      · linarith [hx.2, le_abs_self r, abs_nonneg l]
    rw [abs_quadrantNode d a b hd ha hb] at hsize
    have h₁ : c * (p.1 : ℝ) ≤ |l| + |r| := by
      have h := mul_le_mul_of_nonneg_right (min_le_left a b) (Nat.cast_nonneg p.1)
      linarith [mul_nonneg hb.le (Nat.cast_nonneg p.2)]
    have h₂ : c * (p.2 : ℝ) ≤ |l| + |r| := by
      have h := mul_le_mul_of_nonneg_right (min_le_right a b) (Nat.cast_nonneg p.2)
      linarith [mul_nonneg ha.le (Nat.cast_nonneg p.1)]
    have hM : (|l| + |r|) / c ≤ (M : ℝ) := Nat.le_ceil _
    refine ⟨p, ⟨?_, ?_⟩, rfl⟩
    · exact Nat.cast_le.mp (((le_div_iff₀ hc).mpr (by simpa only [mul_comm] using h₁)).trans hM)
    · exact Nat.cast_le.mp (((le_div_iff₀ hc).mpr (by simpa only [mul_comm] using h₂)).trans hM)

def quadrantDecay (a b : ℝ) (p : ℕ × ℕ) : ℝ :=
  ((1 + a * (p.1 : ℝ) + b * (p.2 : ℝ)) ^ 4)⁻¹

theorem summable_quadrantDecay (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Summable (quadrantDecay a b) := by
  let c := min 1 (min a b)
  have hc : 0 < c := lt_min zero_lt_one (lt_min ha hb)
  let z (n : ℕ) := integerCombDecay (n : ℤ)
  have hz : Summable z := summable_integerCombDecay.comp_injective Int.ofNat_injective
  have hz₀ (n : ℕ) : 0 ≤ z n := sq_nonneg _
  have hs := (hz.mul_of_nonneg hz hz₀ hz₀).mul_left (c⁻¹ ^ 4)
  refine hs.of_nonneg_of_le (fun p => by unfold quadrantDecay; positivity) ?_
  intro p
  let n : ℝ := p.1
  let m : ℝ := p.2
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hm : 0 ≤ m := Nat.cast_nonneg _
  have hc₁ : c ≤ 1 := min_le_left _ _
  have hca : c ≤ a := (min_le_right _ _).trans (min_le_left _ _)
  have hcb : c ≤ b := (min_le_right _ _).trans (min_le_right _ _)
  have hlinear : c * (1 + n + m) ≤ 1 + a * n + b * m := by
    linarith [mul_le_mul_of_nonneg_right hca hn, mul_le_mul_of_nonneg_right hcb hm]
  have hcross : (1 + n) * (1 + m) ≤ (1 + n + m) ^ 2 := by
    nlinarith [mul_nonneg hn hm]
  have hpow : c ^ 4 * ((1 + n) ^ 2 * (1 + m) ^ 2) ≤ (1 + a * n + b * m) ^ 4 := by
    calc
      _ = (c ^ 2 * ((1 + n) * (1 + m))) ^ 2 := by ring
      _ ≤ (c ^ 2 * (1 + n + m) ^ 2) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hcross (sq_nonneg c)) 2
      _ = (c * (1 + n + m)) ^ 4 := by ring
      _ ≤ _ := pow_le_pow_left₀ (by positivity) hlinear 4
  calc
    quadrantDecay a b p ≤ (c ^ 4 * ((1 + n) ^ 2 * (1 + m) ^ 2))⁻¹ :=
      inv_anti₀ (by positivity) hpow
    _ = c⁻¹ ^ 4 * (z p.1 * z p.2) := by
      simp only [z, integerCombDecay, Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _)]
      rw [mul_inv, mul_inv, ← inv_pow, ← inv_pow, ← inv_pow]

def quadrantSeminorm : Seminorm ℂ (SchwartzMap ℝ ℂ) :=
  (Finset.Iic (4, 0)).sup (schwartzSeminormFamily ℂ ℝ ℂ)

theorem continuous_quadrantSeminorm : Continuous quadrantSeminorm :=
  Seminorm.continuous_finsetSup (fun i _ => (schwartz_withSeminorms ℂ ℝ ℂ).continuous_seminorm i)

private theorem norm_weightedQuadrant_sample_le (d a b : ℝ) (hd : |d| = 1)
    (ha : 0 < a) (hb : 0 < b) (u : ℕ × ℕ → ℂ) (M : ℝ)
    (hM : 0 ≤ M) (hu : ∀ p, ‖u p‖ ≤ M) (f : SchwartzMap ℝ ℂ) (p : ℕ × ℕ) :
    ‖u p * f (quadrantNode d a b p)‖ ≤ (M * 2 ^ 4 * quadrantDecay a b p) * quadrantSeminorm f := by
  have h := originalWeightedSchwartzValue_le_seminorm 4 f (quadrantNode d a b p)
  rw [abs_quadrantNode d a b hd ha hb] at h
  have hsample : ‖f (quadrantNode d a b p)‖ ≤
      2 ^ 4 * quadrantSeminorm f * quadrantDecay a b p := by
    rw [quadrantDecay, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    simpa only [quadrantSeminorm, mul_comm (‖f (quadrantNode d a b p)‖)]
      using (by simpa only [← add_assoc] using h)
  rw [norm_mul]
  exact (mul_le_mul (hu p) hsample (norm_nonneg _) hM).trans_eq (by ring)

theorem summable_weightedQuadrant_samples (d a b : ℝ) (hd : |d| = 1)
    (ha : 0 < a) (hb : 0 < b) (u : ℕ × ℕ → ℂ) (M : ℝ)
    (hM : 0 ≤ M) (hu : ∀ p, ‖u p‖ ≤ M) (f : SchwartzMap ℝ ℂ) :
    Summable (fun p : ℕ × ℕ => u p * f (quadrantNode d a b p)) :=
  Summable.of_norm_bounded
    (((summable_quadrantDecay a b ha hb).mul_left (M * 2 ^ 4)).mul_right (quadrantSeminorm f))
    (norm_weightedQuadrant_sample_le d a b hd ha hb u M hM hu f)

/-- The genuine tempered quadratic sampling functional, with no
absolute-convergence premise supplied by the caller. -/
def weightedQuadrant (d a b : ℝ) (hd : |d| = 1) (ha : 0 < a) (hb : 0 < b)
    (u : ℕ × ℕ → ℂ) (M : ℝ) (hM : 0 ≤ M) (hu : ∀ p, ‖u p‖ ≤ M) :
    TemperedDistribution ℝ ℂ := by
  let bound (p : ℕ × ℕ) := M * 2 ^ 4 * quadrantDecay a b p
  have hs : Summable bound := (summable_quadrantDecay a b ha hb).mul_left (M * 2 ^ 4)
  let e := Nat.pairEquiv.symm
  exact schwartzSeries
    (fun n => u (e n) • TemperedDistribution.delta (quadrantNode d a b (e n)))
    quadrantSeminorm continuous_quadrantSeminorm (bound ∘ e)
    (hs.comp_injective e.injective)
    (fun _ => by simp only [Function.comp_apply, bound]; unfold quadrantDecay; positivity)
    (fun n f => by
      simpa only [smul_apply, smul_eq_mul, TemperedDistribution.delta_apply, Function.comp_apply, bound] using
        norm_weightedQuadrant_sample_le d a b hd ha hb u M hM hu f (e n))

theorem weightedQuadrant_apply (d a b : ℝ) (hd : |d| = 1) (ha : 0 < a) (hb : 0 < b)
    (u : ℕ × ℕ → ℂ) (M : ℝ) (hM : 0 ≤ M) (hu : ∀ p, ‖u p‖ ≤ M)
    (f : SchwartzMap ℝ ℂ) :
    weightedQuadrant d a b hd ha hb u M hM hu f =
      ∑' p : ℕ × ℕ, u p * f (quadrantNode d a b p) := by
  simp only [weightedQuadrant, schwartzSeries_apply, smul_apply, smul_eq_mul,
    TemperedDistribution.delta_apply]
  exact Nat.pairEquiv.symm.tsum_eq (fun p => u p * f (quadrantNode d a b p))

theorem weightedQuadrant_atomicOnCarrier (d a b : ℝ) (hd : |d| = 1)
    (ha : 0 < a) (hb : 0 < b) (u : ℕ × ℕ → ℂ) (M : ℝ)
    (hM : 0 ≤ M) (hu : ∀ p, ‖u p‖ ≤ M) :
    AtomicOnCarrier (quadrantCarrier d a b hd ha hb) (weightedQuadrant d a b hd ha hb u M hM hu) := by
  intro f hf
  rw [weightedQuadrant_apply]
  have hzero (p : ℕ × ℕ) : f (quadrantNode d a b p) = 0 := hf _ ⟨p, rfl⟩
  simp only [hzero, mul_zero, tsum_zero]

end
end MeyerGeneralProblem
