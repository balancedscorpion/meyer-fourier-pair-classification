module

public import MeyerGeneralProblem.Carrier.ClusterDecomposition
public import Mathlib.Analysis.Complex.JensenFormula

@[expose] public section

/-!
# A uniform count of real zeros from Jensen's inequality

A lower bound along one horizontal line and an upper bound in a fixed
strip give a common unit-window zero count. The count includes every
zero's analytic multiplicity, so it also bounds distinct real sites.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set Metric MeromorphicOn

theorem entire_analyticOrderAt_ne_top_of_exists_ne_zero (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f univ)
    (h : ∃ c, f c ≠ 0) (z : ℂ) : analyticOrderAt f z ≠ ⊤ := by
  obtain ⟨c, hc⟩ := h
  have h0 := (hf c (mem_univ c)).analyticOrderAt_eq_zero.mpr hc
  apply hf.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (mem_univ c) (mem_univ z)
  rw [h0]
  exact WithTop.zero_ne_top

private theorem analyticDivisor_eq_orderNat (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f univ)
    (h : ∃ c, f c ≠ 0) (U : Set ℂ) {z : ℂ} (hz : z ∈ U) :
    divisor f U z = (analyticOrderNatAt f z : ℤ) := by
  have htop := entire_analyticOrderAt_ne_top_of_exists_ne_zero f hf h z
  rw [(hf.mono (subset_univ U)).divisor_apply hz]
  lift analyticOrderAt f z to ℕ using htop with n hn
  simp [analyticOrderNatAt, ← hn]

private theorem analyticDivisor_pos_of_zero (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f univ)
    (h : ∃ c, f c ≠ 0) (U : Set ℂ) {z : ℂ} (hz : z ∈ U) (hzero : f z = 0) :
    0 < divisor f U z := by
  rw [analyticDivisor_eq_orderNat f hf h U hz]
  exact_mod_cast ENat.toNat_pos ((hf z (mem_univ z)).analyticOrderAt_ne_zero.mpr hzero)
    (entire_analyticOrderAt_ne_top_of_exists_ne_zero f hf h z)

/-- The literal real zero carrier of a nonzero entire function is locally finite. -/
def entireRealZeroCarrier (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f univ)
    (h : ∃ c, f c ≠ 0) : LocallyFiniteCarrier where
  carrier := {x : ℝ | f (x : ℂ) = 0}
  finite_inter_Icc a b := by
    let r := max |a| |b|
    let U := closedBall (0 : ℂ) r
    have hd : (Function.support (divisor f U)).Finite :=
      (divisor f U).finiteSupport (isCompact_closedBall _ _)
    apply (hd.preimage Complex.ofReal_injective.injOn).subset
    rintro x ⟨hzero, hax, hxb⟩
    have hx : (x : ℂ) ∈ U := by
      rw [show U = closedBall (0 : ℂ) r by rfl, mem_closedBall, dist_zero_right,
        Complex.norm_real, Real.norm_eq_abs, abs_le]
      exact ⟨(neg_le_neg (le_max_left |a| |b|)).trans ((neg_abs_le a).trans hax),
        hxb.trans ((le_abs_self b).trans (le_max_right |a| |b|))⟩
    exact (analyticDivisor_pos_of_zero f hf h U hx hzero).ne'

/-- A horizontal strip estimate and a nonvanishing test line bound every
real unit window, counted with analytic multiplicity. -/
theorem exists_entireRealZeroCarrier_multiplicity_bound
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f univ) (h : ∃ c, f c ≠ 0)
    (Y M κ : ℝ) (hY : 1 ≤ Y) (hM : 1 ≤ M) (hκ : 0 < κ)
    (hupper : ∀ z : ℂ, |z.im| ≤ 5 * Y → ‖f z‖ ≤ M)
    (hlower : ∀ x : ℝ, κ ≤ ‖f ((x : ℂ) + (Y : ℂ) * Complex.I)‖) :
    let S := entireRealZeroCarrier f hf h
    ∃ K : ℕ, ∀ a : ℝ,
      ∑ x ∈ (S.finite_window a 1).toFinset, analyticOrderNatAt f (x : ℂ) ≤ K := by
  classical
  let S := entireRealZeroCarrier f hf h
  let C := Real.log (M / κ) / Real.log 2
  obtain ⟨K, hK⟩ := exists_nat_ge C
  refine ⟨K, fun a => ?_⟩
  let c : ℂ := ((a + 1 / 2 : ℝ) : ℂ) + (Y : ℂ) * Complex.I
  let U := closedBall c |2 * Y|
  let d := divisor f U
  let E := (S.finite_window a 1).toFinset
  let e : ℝ ↪ ℂ := ⟨fun x => (x : ℂ), Complex.ofReal_injective⟩
  have hreal (x : ℝ) (hx : x ∈ E) : (x : ℂ) ∈ U := by
    have hw := (S.finite_window a 1).mem_toFinset.mp hx
    have hdist : |x - (a + 1 / 2)| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [hw.2.1], by linarith [hw.2.2]⟩
    change dist (x : ℂ) c ≤ |2 * Y|
    rw [dist_eq_norm, abs_of_nonneg (by positivity : 0 ≤ 2 * Y)]
    have heq : (x : ℂ) - c = ((x - (a + 1 / 2) : ℝ) : ℂ) - (Y : ℂ) * Complex.I := by
      dsimp [c]
      push_cast
      ring
    rw [heq]
    refine (norm_sub_le _ _).trans ?_
    simp only [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, mul_one,
      abs_of_nonneg (show 0 ≤ Y by linarith)]
    linarith
  have hd : (Function.support d).Finite := d.finiteSupport (isCompact_closedBall _ _)
  have hsub : E.map e ⊆ hd.toFinset := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hz
    apply hd.mem_toFinset.mpr
    exact (analyticDivisor_pos_of_zero f hf h U (hreal x hx)
      ((S.finite_window a 1).mem_toFinset.mp hx).1).ne'
  have hsum : (∑ x ∈ E, analyticOrderNatAt f (x : ℂ) : ℤ) ≤ ∑ᶠ z, d z := by
    calc
      _ = ∑ z ∈ E.map e, d z := by
        rw [Finset.sum_map]
        apply Finset.sum_congr rfl
        intro x hx
        exact (analyticDivisor_eq_orderNat f hf h U (hreal x hx)).symm
      _ ≤ ∑ z ∈ hd.toFinset, d z := Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun z _ _ => (hf.mono (subset_univ U)).divisor_nonneg z)
      _ = _ := by
        symm
        apply finsum_eq_sum_of_support_subset
        intro z hz
        exact hd.mem_toFinset.mpr hz
  have hcenter : κ ≤ ‖f c‖ := hlower (a + 1 / 2)
  have hcenter' : f c ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (hκ.trans_le hcenter))
  have hbound (z : ℂ) (hz : z ∈ sphere c |4 * Y|) : ‖f z‖ ≤ M := by
    apply hupper
    have hdiff : ‖z - c‖ = 4 * Y := by
      rw [mem_sphere, dist_eq_norm, abs_of_nonneg (by positivity : 0 ≤ 4 * Y)] at hz
      exact hz
    have hcim : c.im = Y := by simp [c, Complex.mul_im]
    calc
      |z.im| = |(z - c).im + Y| := by rw [Complex.sub_im, hcim, sub_add_cancel]
      _ ≤ |(z - c).im| + |Y| := abs_add_le _ _
      _ ≤ 5 * Y := by
        rw [abs_of_nonneg (show 0 ≤ Y by linarith)]
        linarith [Complex.abs_im_le_norm (z - c)]
  have hJ := (hf.mono (subset_univ (closedBall c |4 * Y|))).sum_divisor_le
    (c := c) (r := 2 * Y) (R := 4 * Y) (M := M)
    (by rw [abs_of_pos (by positivity : 0 < 2 * Y)]; positivity)
    (by rw [abs_of_nonneg (by positivity : 0 ≤ 2 * Y), abs_of_nonneg (by positivity : 0 ≤ 4 * Y)]; linarith)
    hM hcenter' hbound
  have hlog : Real.log (M / ‖f c‖) ≤ Real.log (M / κ) := by
    apply Real.log_le_log (by positivity)
    exact div_le_div_of_nonneg_left (by linarith) hκ hcenter
  have hdenom : (4 * Y) / (2 * Y) = 2 := by field_simp; ring
  rw [hdenom] at hJ
  have hcomp : ((∑ x ∈ E, analyticOrderNatAt f (x : ℂ) : ℕ) : ℝ) ≤ (∑ᶠ z, d z : ℤ) := by
    exact_mod_cast hsum
  exact_mod_cast hcomp.trans (hJ.trans ((div_le_div_of_nonneg_right hlog
    (Real.log_nonneg (by norm_num))).trans hK))

end

end MeyerGeneralProblem
