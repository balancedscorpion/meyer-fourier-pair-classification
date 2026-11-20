module

public import MeyerGeneralProblem.Distribution.BroadCauchySupportJets

@[expose] public section

/-!
# Recovering a supported distribution from its Cauchy pairing

At a site of the original carrier the top Laurent pole recovers
the top jet. Removing that pole successively recovers every jet.
-/

namespace MeyerGeneralProblem

noncomputable section

open Adaptive Filter Metric Set
open scoped Topology

private theorem highestPoleCoefficient_eq_zero (m q : ℕ) (hm : 0 < m)
    (c : ℕ → ℂ) (H : ℝ → ℂ) (hH : ContinuousAt H 0)
    (he : ∀ᶠ t in 𝓝[>] (0 : ℝ), H t +
      ∑ j ∈ Finset.range (q + 1), c j * ((-Complex.I * (t : ℂ))⁻¹) ^ (m + j) = 0) :
    c q = 0 := by
  let w (t : ℝ) : ℂ := -Complex.I * (t : ℂ)
  let F (t : ℝ) := w t ^ (m + q) * H t +
    ∑ j ∈ Finset.range (q + 1), c j * w t ^ (q - j)
  have hw : Tendsto w (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc : Continuous w := continuous_const.mul Complex.continuous_ofReal
    simpa only [w, Complex.ofReal_zero, mul_zero] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have ht : Tendsto F (𝓝[>] (0 : ℝ))
      (𝓝 ((0 : ℂ) ^ (m + q) * H 0 + ∑ j ∈ Finset.range (q + 1), c j * (0 : ℂ) ^ (q-j))) := by
    apply Tendsto.add
    · exact (hw.pow _).mul (hH.tendsto.mono_left nhdsWithin_le_nhds)
    · exact tendsto_finsetSum (Finset.range (q + 1)) (fun j _ => (hw.pow (q - j)).const_mul (c j))
  have hv : (0 : ℂ) ^ (m + q) * H 0 + ∑ j ∈ Finset.range (q + 1), c j * (0 : ℂ) ^ (q-j) = c q := by
    rw [zero_pow (by omega : m + q ≠ 0), zero_mul, zero_add, Finset.sum_eq_single q]
    · simp
    · intro j hj hne
      have hj' : j ≤ q := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      rw [zero_pow (by omega : q - j ≠ 0), mul_zero]
    · intro h; exact (h (Finset.mem_range.mpr (Nat.lt_succ_self q))).elim
  rw [hv] at ht
  refine tendsto_nhds_unique ht (tendsto_const_nhds.congr' ?_)
  filter_upwards [he, self_mem_nhdsWithin] with t ht hpos
  have hpos' : 0 < t := hpos
  have hwt : w t ≠ 0 := mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (by exact_mod_cast hpos'.ne')
  symm
  calc
    F t = w t ^ (m + q) *
      (H t + ∑ j ∈ Finset.range (q + 1), c j * ((w t)⁻¹) ^ (m + j)) := by
        dsimp only [F]
        rw [mul_add, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        have hj' : j ≤ q := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
        have hsplit : w t ^ (m + q) = w t ^ (q-j) * w t ^ (m+j) := by
          rw [← pow_add, show q - j + (m + j) = m + q by omega]
        rw [hsplit, inv_pow]
        calc
          _ = (c j * w t ^ (q-j)) * ((w t ^ (m+j)) * (w t ^ (m+j))⁻¹) := by
            rw [mul_inv_cancel₀ (pow_ne_zero _ hwt), mul_one]
          _ = _ := by ring
    _ = _ := by rw [show H t + ∑ j ∈ Finset.range (q + 1), c j * ((w t)⁻¹) ^ (m + j) = 0 from ht, mul_zero]

private theorem poleCoefficients_eq_zero (m q : ℕ) (hm : 0 < m)
    (c : ℕ → ℂ) (H : ℝ → ℂ) (hH : ContinuousAt H 0)
    (he : ∀ᶠ t in 𝓝[>] (0 : ℝ), H t +
      ∑ j ∈ Finset.range (q + 1), c j * ((-Complex.I * (t : ℂ))⁻¹) ^ (m + j) = 0) :
    ∀ j ≤ q, c j = 0 := by
  induction q with
  | zero =>
    intro j hj
    rw [Nat.eq_zero_of_le_zero hj]
    exact highestPoleCoefficient_eq_zero m 0 hm c H hH he
  | succ q ih =>
    have hq := highestPoleCoefficient_eq_zero m (q + 1) hm c H hH he
    intro j hj
    by_cases hj' : j = q + 1
    · rwa [hj']
    · refine ih ?_ j (by omega)
      filter_upwards [he] with t ht
      simpa only [Finset.sum_range_succ, hq, zero_mul, add_zero] using ht

/-- A higher-order original Cauchy pairing separates tempered
distributions supported on a locally finite real carrier. -/
theorem eq_zero_of_broadCauchyPairing_eq_zero (S : LocallyFiniteCarrier)
    (T : TemperedDistribution ℝ ℂ) (q m : ℕ) (hT : DistributionSupportedOn S.carrier T)
    (horder : HasSchwartzOrderBound T q) (hm : q < m)
    (hzero : ∀ (z : ℂ) (hz : z.im ≠ 0), broadCauchyPairing T q m horder hm z hz = 0) :
    T = 0 := by
  classical
  have hm₀ : 0 < m := by omega
  obtain ⟨c, hc⟩ := supportedOn_compact_jet_formula_of_schwartzOrder S T q hT horder
  have hcZero (a : S.subtype) (j : ℕ) (hj : j ≤ q) : c a j = 0 := by
    let R := |(a : ℝ)| + 1
    obtain ⟨N, hN⟩ := exists_nat_gt (2 * R)
    have hNR : 2 * R ≤ (N : ℝ) + 1 := by linarith
    obtain ⟨H, hH, hAnnular⟩ := exists_analytic_broadCauchyAnnularTail T q m horder hm R N hNR
    let χ := scaledCompactSchwartzCutoff N
    have hχ : HasCompactSupport (χ : ℝ → ℂ) := scaledCompactSchwartzCutoff_hasCompactSupport N
    obtain ⟨E₀, hE₀⟩ := exists_finite_neighborhood_support S χ hχ
    let E := insert a E₀
    have haE : a ∈ E := Finset.mem_insert_self _ _
    have hE (b : S.subtype) (hb : b ∉ E) :
        (χ : ℝ → ℂ) =ᶠ[𝓝 (b : ℝ)] 0 :=
      hE₀ b (fun h => hb (Finset.mem_insert_of_mem h))
    have haN : |(a : ℝ)| < (N : ℝ) + 1 := by dsimp only [R] at hNR; linarith [abs_nonneg (a : ℝ)]
    have hχone : (χ : ℝ → ℂ) =ᶠ[𝓝 (a : ℝ)] (fun _ => 1) := by
      filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds haN] with x hx
      exact scaledCompactSchwartzCutoff_eq_one N (show |x| < (N : ℝ) + 1 from hx).le
    let z (t : ℝ) : ℂ := ((a : ℝ) : ℂ) + (t : ℂ) * Complex.I
    have hz : Continuous z := continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    have hz₀ : z 0 = ((a : ℝ) : ℂ) := by simp only [z, Complex.ofReal_zero, zero_mul, add_zero]
    have hzim (t : ℝ) : (z t).im = t := by
      simp only [z, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add]
    have haR : ((a : ℝ) : ℂ) ∈ ball (0 : ℂ) R := by
      rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
      exact lt_add_of_pos_right _ zero_lt_one
    have hzR : ∀ᶠ t in 𝓝[>] (0 : ℝ), z t ∈ ball (0 : ℂ) R := by
      exact ((hz.tendsto 0).mono_left nhdsWithin_le_nhds).eventually
        (isOpen_ball.mem_nhds (hz₀.symm ▸ haR))
    let D (b : S.subtype) (j i : ℕ) :=
      cauchyCutoffJetCoefficient m N j i b (c b j)
    let K (b : S.subtype) (t : ℝ) :=
      ∑ j ∈ Finset.range (q + 1), ∑ i ∈ Finset.range (j + 1),
        D b j i * broadCauchyKernel (m + (j - i)) (z t) b
    let W (t : ℝ) := H (z t) + ∑ b ∈ E.erase a, K b t
    have hW : ContinuousAt W 0 := by
      apply ContinuousAt.add
      · have hHz : ContinuousAt H (z 0) := by
          rw [hz₀]
          exact (hH _ haR).continuousAt
        exact hHz.comp hz.continuousAt
      · apply tendsto_finsetSum
        intro b hb
        have hba : (b : ℝ) ≠ (a : ℝ) := fun h => (Finset.mem_erase.mp hb).1 (Subtype.ext h)
        apply tendsto_finsetSum
        intro r _
        apply tendsto_finsetSum
        intro i _
        have hh : ((b : ℝ) : ℂ) - z 0 ≠ 0 := by
          rw [hz₀, sub_ne_zero]
          exact fun h => hba (Complex.ofReal_injective h)
        have hK := (((continuousAt_const.sub hz.continuousAt).inv₀ hh).pow (m + (r - i))).const_mul (D b r i)
        exact hK
    let b (r : ℕ) := c a r * (-1 : ℂ) ^ r * (m.ascFactorial r : ℂ)
    have hD₀ (r : ℕ) : D a r 0 = b r := by
      have ho := hχone.iteratedDeriv_eq 0
      dsimp only [D, cauchyCutoffJetCoefficient, b]
      rw [ho, iteratedDeriv_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, mul_one, Nat.sub_zero]
      ring
    have hD₁ (r i : ℕ) (hi : i ≠ 0) : D a r i = 0 := by
      dsimp only [D, cauchyCutoffJetCoefficient]
      rw [hχone.iteratedDeriv_eq i]
      simp only [iteratedDeriv_const, ite_eq_right hi, mul_zero, zero_mul]
    have hKa (t : ℝ) : K a t =
        ∑ r ∈ Finset.range (q + 1), b r * ((-Complex.I * (t : ℂ))⁻¹) ^ (m + r) := by
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Finset.sum_eq_single 0]
      · rw [hD₀, Nat.sub_zero, broadCauchyKernel,
          show ((a : ℝ) : ℂ) - z t = -Complex.I * (t : ℂ) by dsimp only [z]; ring]
      · intro i _ hi
        rw [hD₁ r i hi, zero_mul]
      · intro hi
        exact (hi (Finset.mem_range.mpr (Nat.succ_pos r))).elim
    have hvanish : ∀ᶠ t in 𝓝[>] (0 : ℝ), W t +
        ∑ r ∈ Finset.range (q + 1), b r * ((-Complex.I * (t : ℂ))⁻¹) ^ (m + r) = 0 := by
      filter_upwards [hzR, self_mem_nhdsWithin] with t ht hpos
      have ht₀ : 0 < t := hpos
      have hpos' : (z t).im ≠ 0 := (hzim t).trans_ne ht₀.ne'
      have he := hAnnular (z t) ht hpos'
      rw [action_broadCauchySchwartzCut_eq_finite_jets S T q m c hc N E hE] at he
      rw [← hKa t]
      change H (z t) + (∑ b ∈ E.erase a, K b t) + K a t = 0
      rw [add_assoc, Finset.sum_erase_add E (fun b => K b t) haE, ← he]
      exact hzero (z t) hpos'
    have hbj := poleCoefficients_eq_zero m q hm₀ b W hW hvanish j hj
    have hmj : 0 < m.ascFactorial j := by
      obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm₀.ne'
      exact Nat.ascFactorial_pos r j
    have hfactor : (m.ascFactorial j : ℂ) ≠ 0 := by exact_mod_cast hmj.ne'
    have hp : (-1 : ℂ) ^ j ≠ 0 := pow_ne_zero _ (by norm_num)
    exact (mul_eq_zero.mp ((mul_eq_zero.mp hbj).resolve_right hfactor)).resolve_right hp
  apply distributions_eq_of_compact_test_eq
  intro f hf
  obtain ⟨E, hE⟩ := exists_finite_neighborhood_support S f hf
  rw [hc f hf E hE]
  change (∑ a ∈ E, ∑ j ∈ Finset.range (q + 1), c a j * iteratedDeriv j (f : ℝ → ℂ) a) = 0
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun j hj => ?_
  rw [hcZero a j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)), zero_mul]

end

end MeyerGeneralProblem
