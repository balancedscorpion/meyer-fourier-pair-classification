module

public import MeyerGeneralProblem.Distribution.BroadCauchyEntireProduct
public import MeyerGeneralProblem.Distribution.CanonicalProductDensity
public import Mathlib.Analysis.Complex.AbsMax

@[expose] public section

/-!
# A bound across the real axis at the original exponential type

On a circle of radius two centered in the unit strip, the product of
the distances to the two real intersections is four times the distance
to the real line. Multiplying by the corresponding polynomial lets the
maximum modulus principle absorb the apparent real-axis singularity.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter Metric Set
open scoped ComplexConjugate Topology

private theorem exists_realIntersectionPolynomial (z : ℂ) (hz : |z.im| ≤ 1) :
    ∃ P : ℂ → ℂ, Differentiable ℂ P ∧ ‖P z‖ = 4 ∧
      ∀ w ∈ sphere z 2, ‖P w‖ = 4 * |w.im| := by
  let y := z.im
  have hy : y ^ 2 ≤ 1 := by
    rw [← sq_abs y]
    simpa only [one_pow] using pow_le_pow_left₀ (abs_nonneg y) hz 2
  let a := Real.sqrt (4 - y ^ 2)
  have ha : a ^ 2 = 4 - y ^ 2 := Real.sq_sqrt (by linarith)
  let uPlus : ℂ := (a : ℂ) - (y : ℂ) * Complex.I
  let uMinus : ℂ := -(a : ℂ) - (y : ℂ) * Complex.I
  let P (w : ℂ) := (w - z - uPlus) * (w - z - uMinus)
  have hnormPlus : ‖uPlus‖ = 2 := by
    apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num)).mp
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [uPlus, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, sub_zero, add_zero]
    nlinarith
  have hnormMinus : ‖uMinus‖ = 2 := by
    apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num)).mp
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [uMinus, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, neg_zero, mul_zero, mul_one, sub_zero, add_zero]
    nlinarith
  have hsum : uPlus + uMinus = -(2 * (y : ℂ) * Complex.I) := by dsimp [uPlus, uMinus]; ring
  have hprod : uPlus * uMinus = -4 := by
    have ha' : (a : ℂ) ^ 2 = 4 - (y : ℂ) ^ 2 := by exact_mod_cast ha
    calc
      _ = -(a : ℂ) ^ 2 + (y : ℂ) ^ 2 * Complex.I ^ 2 := by dsimp [uPlus, uMinus]; ring
      _ = _ := by rw [ha', Complex.I_sq]; ring
  refine ⟨P, by dsimp only [P]; fun_prop, by
    simp only [P, sub_self, zero_sub, norm_mul, norm_neg, hnormPlus, hnormMinus]
    norm_num, fun w hw => ?_⟩
  let u := w - z
  have hu : ‖u‖ = 2 := by simpa only [mem_sphere, dist_eq_norm, u] using hw
  have hconj : u * conj u = (4 : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hu]
    norm_num
  have him : u.im + y = w.im := by simp only [u, y, Complex.sub_im, sub_add_cancel]
  have hP : P w = u * ((2 * w.im : ℝ) * Complex.I) := by
    change (u - uPlus) * (u - uMinus) = _
    calc
      _ = u * u - u * (uPlus + uMinus) + uPlus * uMinus := by ring
      _ = u * (u - conj u + 2 * (y : ℂ) * Complex.I) := by
        rw [hsum, hprod, ← hconj]
        ring
      _ = _ := by
        rw [Complex.sub_conj, ← him]
        push_cast
        ring
  rw [hP, norm_mul, norm_mul, hu, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))]
  ring

/-- An apparent off-real pole bound can be removed from a fixed disk,
with a constant independent of the center in the unit strip. -/
theorem norm_entire_le_of_offReal_sphere_bound {F : ℂ → ℂ}
    (hF : Differentiable ℂ F) (z : ℂ) (hz : |z.im| ≤ 1) (p : ℕ) (hp : 0 < p) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ w ∈ sphere z 2, w.im ≠ 0 → ‖F w‖ ≤ B * (1 + (|w.im|)⁻¹ ^ p)) :
    ‖F z‖ ≤ B * (3 ^ p + 1) := by
  obtain ⟨P, hP, hPz, hPw⟩ := exists_realIntersectionPolynomial z hz
  let G (w : ℂ) := P w ^ p * F w
  have hG : Differentiable ℂ G := (hP.pow p).mul hF
  have hbound (w : ℂ) (hw : w ∈ frontier (ball z 2)) :
      ‖G w‖ ≤ (4 : ℝ) ^ p * (B * (3 ^ p + 1)) := by
    have hsphere := frontier_ball_subset_sphere hw
    have him : |w.im| ≤ 3 := by
      have hd : |w.im - z.im| ≤ 2 := by
        have h := Complex.abs_im_le_norm (w - z)
        rw [Complex.sub_im, ← dist_eq_norm, mem_sphere.mp hsphere] at h
        exact h
      calc
        _ = |(w.im - z.im) + z.im| := by rw [sub_add_cancel]
        _ ≤ |w.im - z.im| + |z.im| := abs_add_le _ _
        _ ≤ _ := by linarith
    have hpow := pow_le_pow_left₀ (abs_nonneg w.im) him p
    change ‖P w ^ p * F w‖ ≤ _
    rw [norm_mul, norm_pow, hPw w hsphere]
    by_cases h : w.im = 0
    · rw [h, abs_zero, mul_zero, zero_pow hp.ne', zero_mul]
      positivity
    · calc
        _ ≤ (4 * |w.im|) ^ p * (B * (1 + (|w.im|)⁻¹ ^ p)) :=
          mul_le_mul_of_nonneg_left (hb w hsphere h) (by positivity)
        _ = (4 : ℝ) ^ p * (B * (|w.im| ^ p + 1)) := by
          have he : |w.im| ^ p * (|w.im|)⁻¹ ^ p = 1 := by
            rw [← mul_pow, mul_inv_cancel₀ (abs_ne_zero.mpr h), one_pow]
          rw [mul_pow]
          linear_combination (4 : ℝ) ^ p * B * he
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (add_le_add_left hpow 1) hB) (by positivity)
  have hh := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hG.diffContOnCl hbound
    (subset_closure (mem_ball_self (by norm_num : (0 : ℝ) < 2)))
  change ‖P z ^ p * F z‖ ≤ _ at hh
  rw [norm_mul, norm_pow, hPz] at hh
  exact le_of_mul_le_mul_left hh (by positivity)

/-- An eventual bound on the literal centered count ratio gives
inverse-square summability on the original nonzero sites. -/
theorem summable_inverseSq_of_eventual_centered_ratio_bound
    (S : LocallyFiniteCarrier)
    (hb : (atTop : Filter ℝ).IsBoundedUnder (· ≤ ·)
      (fun t => ((S.carrier ∩ Icc (-t) t).ncard : ℝ) / (2 * t))) :
    Summable (fun a : NonzeroCarrierPoint S => (|a.val| ^ 2)⁻¹) := by
  obtain ⟨B, hB⟩ := hb.eventually_le
  obtain ⟨T, hT⟩ := eventually_atTop.mp hB
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 T)
  let n₀ := (S.carrier ∩ Icc (-(N : ℝ)) N).ncard
  obtain ⟨C, hC⟩ := exists_nat_gt (max (2 * B) (n₀ : ℝ))
  have hC₀ : n₀ ≤ C := by exact_mod_cast (le_max_right (2 * B) (n₀ : ℝ)).trans hC.le
  apply summable_inverseSq_of_linear_centered_carrier_count S C
  intro n
  by_cases hn : N ≤ n
  · have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
    have hnpos : (0 : ℝ) < n := by linarith [le_max_left (1 : ℝ) T]
    have hTn : T ≤ n := ((le_max_right (1 : ℝ) T).trans hN.le).trans hn'
    have hcnt := (div_le_iff₀ (show 0 < 2 * (n : ℝ) by positivity)).mp (hT n hTn)
    have hC' := (le_max_left (2 * B) (n₀ : ℝ)).trans hC.le
    have hh := mul_le_mul_of_nonneg_right hC' hnpos.le
    exact_mod_cast (show ((S.carrier ∩ Icc (-(n : ℝ)) n).ncard : ℝ) ≤
      (C : ℝ) * ((n : ℝ) + 1) by linarith [show (0 : ℝ) ≤ C from Nat.cast_nonneg C])
  · have hn' : (n : ℝ) ≤ N := by exact_mod_cast (le_of_not_ge hn)
    have hsub : S.carrier ∩ Icc (-(n : ℝ)) n ⊆ S.carrier ∩ Icc (-(N : ℝ)) N :=
      inter_subset_inter_right _ (Icc_subset_Icc (neg_le_neg hn') hn')
    exact (ncard_le_ncard hsub (S.finite_inter_Icc _ _)).trans
      (hC₀.trans (Nat.le_mul_of_pos_right C (Nat.succ_pos n)))

/-- The canonical-product multiple of the actual Cauchy pairing is entire
with radial exponential type at most 2π(m+q)D, recorded by a global
bound with a polynomial factor and every positive density slack. -/
theorem exists_entire_broadCauchyCanonicalProduct_with_growth
    (S : LocallyFiniteCarrier)
    (hb : (atTop : Filter ℝ).IsBoundedUnder (· ≤ ·)
      (fun t => ((S.carrier ∩ Icc (-t) t).ncard : ℝ) / (2 * t)))
    (T : TemperedDistribution ℝ ℂ) (q m : ℕ) (hT : Adaptive.DistributionSupportedOn S.carrier T)
    (horder : HasSchwartzOrderBound T q) (hm : q < m) :
    let D := limsup (fun t : ℝ => ((S.carrier ∩ Icc (-t) t).ncard : ℝ) / (2 * t)) atTop
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F univ ∧
      (∀ z : ℂ, ∀ hz : z.im ≠ 0, F z =
        symmetricCarrierCanonicalProduct S z ^ (m + q) * broadCauchyPairing T q m horder hm z hz) ∧
      ∀ ε > 0, ∃ A L : ℝ, 0 ≤ A ∧ 0 ≤ L ∧ ∀ z : ℂ,
        ‖F z‖ ≤ A * (3 + ‖z‖) ^ q *
          Real.exp (2 * Real.pi * (D + ε) * (m + q : ℕ) * (‖z‖ + 2) + L * Real.log (4 + ‖z‖)) := by
  let u (t : ℝ) := ((S.carrier ∩ Icc (-t) t).ncard : ℝ) / (2 * t)
  let D := limsup u atTop
  let p := m + q
  have hp : 0 < p := by dsimp [p]; omega
  have hD : 0 ≤ D := le_limsup_of_frequently_le
    ((eventually_gt_atTop (0 : ℝ)).mono (fun t ht => by dsimp [u]; positivity)).frequently hb
  obtain ⟨F, hF, hE⟩ := exists_entire_broadCauchyCanonicalProduct S
    (summable_inverseSq_of_eventual_centered_ratio_bound S hb) T q m hT horder hm
  obtain ⟨K, hK, hAction⟩ := norm_broadCauchyPairing_le T q m horder hm
  refine ⟨F, hF, hE, fun ε hε => ?_⟩
  obtain ⟨L₀, hL₀, hQ⟩ := norm_symmetricCarrierCanonicalProduct_le_of_centered_upper_density S hb ε hε
  let σ := 2 * Real.pi * (D + ε) * p
  let L := L₀ * p
  have hσ : 0 ≤ σ := by dsimp [σ]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  let b (r : ℝ) := K * (1 + r) ^ q * Real.exp (σ * r + L * Real.log (2 + r))
  have hb₀ (r : ℝ) (hr : 0 ≤ r) : 0 ≤ b r := by dsimp [b]; positivity
  have hbmono (r s : ℝ) (hr : 0 ≤ r) (hrs : r ≤ s) : b r ≤ b s := by
    have hlog := Real.log_le_log (show 0 < 2 + r by positivity)
      (add_le_add_right hrs (2 : ℝ))
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) (add_le_add_right hrs (1 : ℝ)) q) hK
    · exact Real.exp_le_exp.mpr (add_le_add
        (mul_le_mul_of_nonneg_left hrs hσ) (mul_le_mul_of_nonneg_left hlog hL))
    · positivity
    · exact mul_nonneg hK (pow_nonneg (by linarith : 0 ≤ 1 + s) _)
  have hoff (z : ℂ) (hz : z.im ≠ 0) : ‖F z‖ ≤ b ‖z‖ * (1 + (|z.im|)⁻¹ ^ p) := by
    rw [hE z hz, norm_mul, norm_pow]
    have hpow := pow_le_pow_left₀ (norm_nonneg _) (hQ z) p
    refine (mul_le_mul hpow (hAction z hz) (norm_nonneg _) (by positivity)).trans_eq ?_
    rw [← Real.exp_nat_mul]
    have hexp : (p : ℝ) * (2 * Real.pi * (D + ε) * ‖z‖ + L₀ * Real.log (2 + ‖z‖)) =
        σ * ‖z‖ + L * Real.log (2 + ‖z‖) := by dsimp only [σ, L]; ring
    change Real.exp ((p : ℝ) * (2 * Real.pi * (D + ε) * ‖z‖ + L₀ * Real.log (2 + ‖z‖))) *
      (K * (1 + ‖z‖) ^ q * (1 + (|z.im|)⁻¹ ^ p)) = _
    rw [hexp]
    dsimp only [b]
    ring
  refine ⟨K * (3 ^ p + 1), L, by positivity, hL, fun z => ?_⟩
  have he : b (‖z‖ + 2) * (3 ^ p + 1) =
      K * (3 ^ p + 1) * (3 + ‖z‖) ^ q *
        Real.exp (σ * (‖z‖ + 2) + L * Real.log (4 + ‖z‖)) := by
    have h1 : 1 + (‖z‖ + 2) = 3 + ‖z‖ := by ring
    have h2 : 2 + (‖z‖ + 2) = 4 + ‖z‖ := by ring
    dsimp only [b]
    rw [h1, h2]
    ring
  change ‖F z‖ ≤ _
  rw [← he]
  by_cases hz : |z.im| ≤ 1
  · refine norm_entire_le_of_offReal_sphere_bound
      (differentiableOn_univ.mp hF.differentiableOn) z hz p hp (b (‖z‖ + 2)) (hb₀ _ (by positivity)) ?_
    intro w hw him
    have hn : ‖w‖ ≤ ‖z‖ + 2 := by
      calc
        ‖w‖ = ‖(w - z) + z‖ := by rw [sub_add_cancel]
        _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
        _ = _ := by rw [← dist_eq_norm, mem_sphere.mp hw, add_comm]
    exact (hoff w him).trans (mul_le_mul_of_nonneg_right (hbmono _ _ (norm_nonneg w) hn) (by positivity))
  · have hz' : 1 < |z.im| := lt_of_not_ge hz
    have him : z.im ≠ 0 := abs_pos.mp (zero_lt_one.trans hz')
    have hpow : (|z.im|)⁻¹ ^ p ≤ (3 : ℝ) ^ p :=
      pow_le_pow_left₀ (inv_nonneg.mpr (abs_nonneg _))
        ((inv_le_one_of_one_le₀ hz'.le).trans (by norm_num)) _
    exact (hoff z him).trans (mul_le_mul
      (hbmono _ _ (norm_nonneg z) (by linarith)) (by linarith)
      (by positivity) (hb₀ _ (by positivity)))

end

end MeyerGeneralProblem
