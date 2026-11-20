module

public import MeyerGeneralProblem.Distribution.BroadCauchySupportJets
public import MeyerGeneralProblem.Distribution.SymmetricCarrierCanonicalProduct
public import Mathlib.Analysis.Complex.RemovableSingularity

@[expose] public section

/-!
# The entire canonical-product multiple of the original Cauchy pairing

The canonical product removes every pole of the exact finite local
expansions. The analytic functions on the resulting disks agree by
continuity on their dense off-real subsets.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter Metric Set
open scoped Topology

private theorem dense_im_ne_zero : Dense {z : ℂ | z.im ≠ 0} := by
  refine Metric.dense_iff.mpr fun z r hr => ?_
  by_cases hz : z.im ≠ 0
  · exact ⟨z, mem_ball_self hr, hz⟩
  · have hz' := not_ne_iff.mp hz
    refine ⟨z + (↑(r / 2 : ℝ) : ℂ) * Complex.I, ?_, ?_⟩
    · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I,
        mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hr)]
      exact half_lt_self hr
    · simpa only [mem_ofPred_eq, Complex.add_im, Complex.mul_im, hz', Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add]
        using (half_pos hr).ne'

private theorem analyticOnNhd_neg_dslope {Q : ℂ → ℂ} (hQ : AnalyticOnNhd ℂ Q univ) (a : ℂ) :
    AnalyticOnNhd ℂ (fun z => -dslope Q a z) univ :=
  (((Complex.differentiableOn_dslope (show (univ : Set ℂ) ∈ 𝓝 a from univ_mem)).mpr
    hQ.differentiableOn).analyticOnNhd isOpen_univ).neg

private theorem pow_mul_broadCauchyKernel_eq_of_zero (Q : ℂ → ℂ) (a : ℝ) (hQa : Q a = 0)
    (p n : ℕ) (hn : n ≤ p) (z : ℂ) (hz : z.im ≠ 0) :
    Q z ^ p * broadCauchyKernel n z a = Q z ^ (p - n) * (-dslope Q (a : ℂ) z) ^ n := by
  have hne : (a : ℂ) - z ≠ 0 := fun he =>
    hz (by simpa only [Complex.ofReal_im] using (congrArg Complex.im (sub_eq_zero.mp he)).symm)
  have he : Q z * ((a : ℂ) - z)⁻¹ = -dslope Q (a : ℂ) z := by
    have hd := sub_smul_dslope_of_zero hQa z
    rw [smul_eq_mul] at hd
    apply (mul_inv_eq_iff_eq_mul₀ hne).mpr
    rw [← hd]
    ring
  have hp : Q z ^ p = Q z ^ (p - n) * Q z ^ n := by rw [← pow_add, Nat.sub_add_cancel hn]
  calc
    _ = Q z ^ (p - n) * (Q z * ((a : ℂ) - z)⁻¹) ^ n := by
      rw [hp, broadCauchyKernel, mul_pow, mul_assoc]
    _ = _ := by rw [he]

private theorem exists_analytic_broadCauchyProductOnBall (S : LocallyFiniteCarrier)
    (hsum : Summable (fun x : NonzeroCarrierPoint S => (|x.val| ^ 2)⁻¹))
    (T : TemperedDistribution ℝ ℂ) (q m : ℕ) (hT : Adaptive.DistributionSupportedOn S.carrier T)
    (horder : HasSchwartzOrderBound T q) (hm : q < m) (R : ℝ) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F (ball 0 R) ∧
      ∀ z ∈ ball (0 : ℂ) R, ∀ hz : z.im ≠ 0,
        F z = symmetricCarrierCanonicalProduct S z ^ (m + q) * broadCauchyPairing T q m horder hm z hz := by
  obtain ⟨H, E, c, hH, he⟩ := exists_broadCauchyPairing_finite_pole_expansion S T q m hT horder hm R
  let Q := symmetricCarrierCanonicalProduct S
  let p := m + q
  let U := ball (0 : ℂ) R
  have hQ : AnalyticOnNhd ℂ Q univ := symmetricCarrierCanonicalProduct_entire S hsum
  let G (a : S.subtype) (j i : ℕ) (z : ℂ) : ℂ :=
    c a j i * (Q z ^ (p - (m + (j - i))) * (-dslope Q (a : ℂ) z) ^ (m + (j - i)))
  have hG (a : S.subtype) (j i : ℕ) : DifferentiableOn ℂ (G a j i) U :=
    ((analyticOnNhd_const (v := c a j i)).mul
      (((hQ.pow _).mul ((analyticOnNhd_neg_dslope hQ (a : ℂ)).pow _)).mono (subset_univ U))).differentiableOn
  let F (z : ℂ) := Q z ^ p * H z +
    ∑ a ∈ E, ∑ j ∈ Finset.range (q + 1), ∑ i ∈ Finset.range (j + 1), G a j i z
  have hF : DifferentiableOn ℂ F U := by
    apply (((hQ.pow _).mono (subset_univ U)).mul hH).differentiableOn.fun_add
    exact DifferentiableOn.fun_sum fun a _ => DifferentiableOn.fun_sum fun j _ =>
      DifferentiableOn.fun_sum fun i _ => hG a j i
  refine ⟨F, hF.analyticOnNhd isOpen_ball, fun z hz him => ?_⟩
  rw [he z hz him, mul_add]
  change Q z ^ p * H z + _ = Q z ^ p * H z + _
  congr 1
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j hj =>
    Finset.sum_congr rfl fun i _ => ?_
  have hj' : j ≤ q := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hle : m + (j - i) ≤ p := Nat.add_le_add_left ((Nat.sub_le j i).trans hj') m
  have hzero : Q (a : ℂ) = 0 := symmetricCarrierCanonicalProduct_eq_zero_of_mem S a a.property
  dsimp only [G]
  rw [← pow_mul_broadCauchyKernel_eq_of_zero Q a hzero p _ hle z him]
  ring

/-- The actual canonical-product multiple extends to an entire function
at the exact exponent m + q. -/
theorem exists_entire_broadCauchyCanonicalProduct (S : LocallyFiniteCarrier)
    (hsum : Summable (fun x : NonzeroCarrierPoint S => (|x.val| ^ 2)⁻¹))
    (T : TemperedDistribution ℝ ℂ) (q m : ℕ) (hT : Adaptive.DistributionSupportedOn S.carrier T)
    (horder : HasSchwartzOrderBound T q) (hm : q < m) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F univ ∧ ∀ (z : ℂ) (hz : z.im ≠ 0),
      F z = symmetricCarrierCanonicalProduct S z ^ (m + q) * broadCauchyPairing T q m horder hm z hz := by
  choose G hG hE using fun R : ℝ => exists_analytic_broadCauchyProductOnBall S hsum T q m hT horder hm R
  let F (z : ℂ) := G (‖z‖ + 1) z
  have hmemb (z : ℂ) : z ∈ ball (0 : ℂ) (‖z‖ + 1) := by
    rw [mem_ball, dist_zero_right]
    exact lt_add_of_pos_right _ zero_lt_one
  have hEq (R : ℝ) : EqOn F (G R) (ball 0 R) := by
    intro z hz
    let X := ball (0 : ℂ) (‖z‖ + 1) ∩ ball 0 R
    have hX : ∀ᶠ w in 𝓝 z, w ∈ X :=
      (isOpen_ball.inter isOpen_ball).mem_nhds ⟨hmemb z, hz⟩
    have hf : ∃ᶠ w in 𝓝 z, w.im ≠ 0 := mem_closure_iff_frequently.mp (dense_im_ne_zero z)
    refine tendsto_nhds_unique_of_frequently_eq
      ((hG (‖z‖ + 1) z (hmemb z)).continuousAt.tendsto)
      ((hG R z hz).continuousAt.tendsto) ((hf.and_eventually hX).mono fun w hw => ?_)
    exact (hE _ w hw.2.1 hw.1).trans (hE _ w hw.2.2 hw.1).symm
  refine ⟨F, fun z _ => ?_, fun z hz => hE _ z (hmemb z) hz⟩
  have hnear : ∀ᶠ w in 𝓝 z, w ∈ ball (0 : ℂ) (‖z‖ + 1) :=
    isOpen_ball.mem_nhds (hmemb z)
  exact (hG _ z (hmemb z)).congr (hnear.mono (hEq (‖z‖ + 1)).symm)

end

end MeyerGeneralProblem
