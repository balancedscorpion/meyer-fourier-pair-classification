module

public import MeyerGeneralProblem.Distribution.FourierGapKernelEstimates
public import MeyerGeneralProblem.Distribution.BroadCauchyPairing
public import MeyerGeneralProblem.Distribution.ShiftedIntegerComb
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.UniformSpace.UniformApproximation

@[expose] public section

/-!
# Pairing the original tempered source with cutoff kernels

Finite Schwartz order gives convergence of the cutoff kernel pairings
to a continuous function with a uniform polynomial growth bound.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter MeasureTheory Metric Set
open scoped ContDiff FourierTransform Topology

/-- Frequency cutoffs approximate the inverse Fourier transform of any
tempered frequency distribution on each original Schwartz test. -/
theorem tendsto_inverseFourier_cutoff_tempered_apply
    (U : TemperedDistribution ℝ ℂ) (φ : SchwartzMap ℝ ℂ) :
    Tendsto (fun N : ℕ =>
      (𝓕⁻ (TemperedDistribution.smulLeftCLM ℂ (⇑(scaledCompactSchwartzCutoff N)) U) :
        TemperedDistribution ℝ ℂ) φ) atTop (𝓝 ((𝓕⁻ U : TemperedDistribution ℝ ℂ) φ)) := by
  let g : SchwartzMap ℝ ℂ := 𝓕⁻ φ
  change Tendsto (fun N => U (compactSchwartzApproximation N g)) atTop (𝓝 (U g))
  exact (U.continuous.tendsto g).comp (compactSchwartzApproximation_tendsto g)

/-- Pair the tempered source with the kernel evaluated at x minus the test variable. -/
def fourierPrimitiveKernelPairing (T : TemperedDistribution ℝ ℂ) (g : SchwartzMap ℝ ℂ)
    (x : ℝ) : ℂ := T (schwartzReflectionCLM (combSchwartzTranslation x g))

private theorem abs_pow_le_shifted_weight (x t : ℝ) {k q : ℕ} (hk : k ≤ q) :
    |t| ^ k ≤ ((1 + |x|) * (1 + |x - t|)) ^ q := by
  have ht : |t| ≤ (1 + |x|) * (1 + |x - t|) := by
    calc
      |t| = |x - (x - t)| := by rw [sub_sub_cancel]
      _ ≤ |x| + |x - t| := abs_sub _ _
      _ ≤ _ := by nlinarith [mul_nonneg (abs_nonneg x) (abs_nonneg (x - t))]
  have hbase : 1 ≤ (1 + |x|) * (1 + |x - t|) :=
    one_le_mul_of_one_le_of_one_le (le_add_of_nonneg_right (abs_nonneg _))
      (le_add_of_nonneg_right (abs_nonneg _))
  exact (pow_le_pow_left₀ (abs_nonneg t) ht k).trans (pow_le_pow_right₀ hbase hk)

private theorem norm_fourierPrimitiveKernelPairing_le
    (T : TemperedDistribution ℝ ℂ) (q : ℕ) (D : ℝ) (hD : 0 ≤ D)
    (hT : ∀ f : SchwartzMap ℝ ℂ,
      ‖T f‖ ≤ D * ((Finset.Iic (q, q)).sup (schwartzSeminormFamily ℂ ℝ ℂ)) f)
    (g : SchwartzMap ℝ ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hg : ∀ j ≤ q, ∀ z : ℝ, (1 + |z|) ^ q * ‖iteratedDeriv j g z‖ ≤ B) (x : ℝ) :
    ‖fourierPrimitiveKernelPairing T g x‖ ≤ D * B * (1 + |x|) ^ q := by
  let G := schwartzReflectionCLM (combSchwartzTranslation x g)
  have he : (G : ℝ → ℂ) = fun t => g (x - t) := by
    funext t
    simp only [G, schwartzReflectionCLM_apply, combSchwartzTranslation_apply, sub_eq_add_neg]
  have hG : ((Finset.Iic (q, q)).sup (schwartzSeminormFamily ℂ ℝ ℂ)) G ≤ B * (1 + |x|) ^ q := by
    apply Seminorm.finset_sup_apply_le (by positivity)
    rintro ⟨k, j⟩ hkj
    have hk : k ≤ q := (Finset.mem_Iic.mp hkj).1
    have hj : j ≤ q := (Finset.mem_Iic.mp hkj).2
    apply SchwartzMap.seminorm_le_bound' ℂ k j G (by positivity)
    intro t
    rw [he, iteratedDeriv_comp_const_sub, norm_smul]
    simp only [norm_pow, norm_neg, norm_one, one_pow, one_mul]
    have hpow := abs_pow_le_shifted_weight x t hk
    calc
      _ ≤ ((1 + |x|) * (1 + |x - t|)) ^ q * ‖iteratedDeriv j g (x - t)‖ :=
        mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
      _ = ((1 + |x - t|) ^ q * ‖iteratedDeriv j g (x - t)‖) * (1 + |x|) ^ q := by
        rw [mul_pow]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hg j hj (x - t)) (by positivity)
  exact (hT G).trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hG hD)

/-- For a fixed Schwartz kernel the tempered pairing varies continuously
with the translated point. -/
theorem continuous_fourierPrimitiveKernelPairing
    (T : TemperedDistribution ℝ ℂ) (g : SchwartzMap ℝ ℂ) :
    Continuous (fourierPrimitiveKernelPairing T g) := by
  obtain ⟨q, _, D, hD, hT⟩ := exists_hasSchwartzOrderBound T
  let S := (2 : ℝ) ^ q * ((Finset.Iic (q, q + 1)).sup (schwartzSeminormFamily ℂ ℝ ℂ)) g
  have hS : 0 ≤ S := mul_nonneg (by positivity) (apply_nonneg _ _)
  rw [continuous_iff_continuousAt]
  intro x₀
  let R := |x₀| + 1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hx₀ : x₀ ∈ Ioo (-R) R := abs_lt.mp (by dsimp [R]; linarith)
  let B := S * (1 + R) ^ q
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hLip : LipschitzOnWith ⟨D * B, mul_nonneg hD hB⟩ (fourierPrimitiveKernelPairing T g) (Icc (-R) R) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [dist_eq_norm, Real.dist_eq]
    let G := schwartzReflectionCLM (combSchwartzTranslation x g - combSchwartzTranslation y g)
    have he : (G : ℝ → ℂ) = (fun t => g (x - t)) - (fun t => g (y - t)) := by
      funext t
      simp [G, combSchwartzTranslation_apply, sub_eq_add_neg]
    have hBound : ((Finset.Iic (q, q)).sup (schwartzSeminormFamily ℂ ℝ ℂ)) G ≤ B * |x - y| := by
      apply Seminorm.finset_sup_apply_le (by positivity)
      rintro ⟨k, j⟩ hkj
      have hk : k ≤ q := (Finset.mem_Iic.mp hkj).1
      have hj : j ≤ q := (Finset.mem_Iic.mp hkj).2
      apply SchwartzMap.seminorm_le_bound' ℂ k j G (by positivity)
      intro t
      have hCD (v : ℝ) : ContDiff ℝ j (fun a : ℝ => g (v - a)) :=
        ((g.smooth j).comp (contDiff_const.sub contDiff_id))
      rw [he, iteratedDeriv_sub (hCD x).contDiffAt (hCD y).contDiffAt,
        iteratedDeriv_comp_const_sub, iteratedDeriv_comp_const_sub]
      simp only [← smul_sub, norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      let H (v : ℝ) := |t| ^ k • iteratedDeriv j g (v - t)
      have hDeriv (v : ℝ) : HasDerivAt H (|t| ^ k • iteratedDeriv (j + 1) g (v - t)) v := by
        have hDiff : Differentiable ℝ (iteratedDeriv j g) :=
          (g.smooth (j + 1)).differentiable_iteratedDeriv j (by exact_mod_cast Nat.lt_succ_self j)
        have hv := (hDiff (v - t)).hasDerivAt
        rw [← iteratedDeriv_succ] at hv
        have hShift : HasDerivAt (fun u : ℝ => u - t) 1 v := (hasDerivAt_id v).sub_const t
        change HasDerivAt (|t| ^ k • fun u : ℝ => iteratedDeriv j g (u - t)) _ v
        simpa only [Function.comp_def, one_smul] using
          (hv.scomp v hShift).const_smul (|t| ^ k)
      rw [← norm_smul_of_nonneg (pow_nonneg (abs_nonneg t) k), smul_sub]
      change ‖H x - H y‖ ≤ B * |x - y|
      have hDB (v : ℝ) (hv : v ∈ Icc (-R) R) : ‖deriv H v‖ ≤ B := by
        rw [(hDeriv v).deriv, norm_smul, Real.norm_eq_abs, abs_pow, abs_abs]
        have hv' : |v| ≤ R := abs_le.mpr hv
        have hW := abs_pow_le_shifted_weight v t hk
        calc
          _ ≤ ((1 + |v|) * (1 + |v - t|)) ^ q * ‖iteratedDeriv (j + 1) g (v - t)‖ :=
            mul_le_mul_of_nonneg_right hW (norm_nonneg _)
          _ = ((1 + |v - t|) ^ q * ‖iteratedDeriv (j + 1) g (v - t)‖) * (1 + |v|) ^ q := by
            rw [mul_pow]
            ring
          _ ≤ B := by
            have hSbound : (1 + |v - t|) ^ q * ‖iteratedDeriv (j + 1) g (v - t)‖ ≤ S := by
              change _ ≤ (2 : ℝ) ^ q * ((Finset.Iic (q, q + 1)).sup
                (fun i => SchwartzMap.seminorm ℂ i.1 i.2)) g
              simpa only [Nat.succ_eq_add_one, Real.norm_eq_abs,
                norm_iteratedFDeriv_eq_norm_iteratedDeriv] using
                SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (q, q + 1)) (k := q)
                  le_rfl (Nat.succ_le_succ hj) g (v - t)
            exact mul_le_mul hSbound (pow_le_pow_left₀ (by positivity) (by linarith) q)
              (by positivity) hS
      simpa only [Real.norm_eq_abs] using
        (convex_Icc (-R) R).norm_image_sub_le_of_norm_deriv_le
          (fun v _ => (hDeriv v).differentiableAt) hDB hy hx
    have hEq : fourierPrimitiveKernelPairing T g x - fourierPrimitiveKernelPairing T g y = T G := by
      simp [G, fourierPrimitiveKernelPairing]
    rw [hEq]
    change ‖T G‖ ≤ D * B * |x - y|
    exact (hT G).trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hBound hD)
  exact hLip.continuousOn.continuousAt (Icc_mem_nhds hx₀.1 hx₀.2)

private theorem one_add_abs_pow_mul_le_of_two_bounds
    (q : ℕ) (t u B : ℝ) (hu : 0 ≤ u) (h₀ : u ≤ B) (hq : |t| ^ q * u ≤ B) :
    (1 + |t|) ^ q * u ≤ 2 ^ q * B := by
  by_cases ht : |t| ≤ 1
  · calc
      _ ≤ 2 ^ q * u := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) (by linarith) q) hu
      _ ≤ _ := mul_le_mul_of_nonneg_left h₀ (by positivity)
  · have hAbs : 1 ≤ |t| := (lt_of_not_ge ht).le
    calc
      _ ≤ (2 * |t|) ^ q * u := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) (by linarith) q) hu
      _ = 2 ^ q * (|t| ^ q * u) := by rw [mul_pow, mul_assoc]
      _ ≤ _ := mul_le_mul_of_nonneg_left hq (by positivity)

/-- The original tempered source applied to the cutoff kernels converges
on the whole line with one fixed polynomial weight. The limit has that
same polynomial growth bound. -/
theorem exists_polynomialGrowth_limit_fourierPrimitiveKernelPairing
    (T : TemperedDistribution ℝ ℂ) (a : ℝ → ℂ) (ha : a.HasTemperateGrowth) (r : ℝ)
    (hRecip : ∀ x : ℝ, r ≤ |x| →
      a x = ((2 * (Real.pi : ℂ) * Complex.I) * (x : ℂ))⁻¹) :
    ∃ q : ℕ, ∀ m : ℕ, q + 2 ≤ m →
      ∃ f : ℝ → ℂ, Continuous f ∧ (∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, ‖f x‖ ≤ C * (1 + |x|) ^ q) ∧
        ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x : ℝ,
          ‖fourierPrimitiveKernelPairing T (fourierPrimitiveSchwartzApproximation a m N) x - f x‖ ≤
            ε * (1 + |x|) ^ q := by
  obtain ⟨q, _, D, hD, hT⟩ := exists_hasSchwartzOrderBound T
  refine ⟨q, fun m hm => ?_⟩
  let g := fourierPrimitiveSchwartzApproximation a m
  let F (N : ℕ) (x : ℝ) := fourierPrimitiveKernelPairing T (g N) x
  let K : ℝ → ℂ := 𝓕⁻ (a ^ m)
  let L := D * (2 : ℝ) ^ q
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hCauchy (ε : ℝ) (hε : 0 < ε) : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ M ≥ N₀,
      ∀ x : ℝ, ‖F N x - F M x‖ ≤ ε * (1 + |x|) ^ q := by
    let δ := ε / (2 * (L + 1))
    have hDenom : 0 < 2 * (L + 1) := by positivity
    have hδ : 0 < δ := div_pos hε hDenom
    have hCoeff : L * (2 * δ) ≤ ε := by
      have hh : 2 * (L + 1) * δ = ε := by
        dsimp only [δ]
        rw [mul_comm, div_mul_cancel₀ ε hDenom.ne']
      nlinarith only [hh, hδ.le]
    have hEvt : ∀ᶠ N : ℕ in atTop, ∀ j ∈ Finset.range (q + 1), ∀ x : ℝ,
        ‖iteratedDeriv j (g N) x - iteratedDeriv j K x‖ < δ ∧
          |x| ^ q * ‖iteratedDeriv j (g N) x - iteratedDeriv j K x‖ < δ := by
      apply (eventually_all_finset _).mpr
      intro j hj
      have hjm : j + 2 ≤ m := by
        have h := Finset.mem_range.mp hj
        omega
      have h0 := eventually_weighted_deriv_fourierPrimitiveSchwartzApproximation a ha r hRecip
        j m hjm 0 δ hδ
      have hq := eventually_weighted_deriv_fourierPrimitiveSchwartzApproximation a ha r hRecip
        j m hjm q δ hδ
      filter_upwards [h0, hq] with N h0N hqN
      intro x
      exact ⟨by simpa only [pow_zero, one_mul] using h0N x, hqN x⟩
    obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hEvt
    refine ⟨N₀, fun N hN M hM x => ?_⟩
    have hG (j : ℕ) (hj : j ≤ q) (t : ℝ) :
        (1 + |t|) ^ q * ‖iteratedDeriv j (g N - g M : SchwartzMap ℝ ℂ) t‖ ≤ 2 ^ q * (2 * δ) := by
      have hj' : j ∈ Finset.range (q + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hj)
      have hN' := hN₀ N hN j hj' t
      have hM' := hN₀ M hM j hj' t
      have he : iteratedDeriv j (g N - g M : SchwartzMap ℝ ℂ) t =
          iteratedDeriv j (g N) t - iteratedDeriv j (g M) t :=
        iteratedDeriv_sub ((g N).smooth j).contDiffAt ((g M).smooth j).contDiffAt
      rw [he]
      have hTri : ‖iteratedDeriv j (g N) t - iteratedDeriv j (g M) t‖ ≤
          ‖iteratedDeriv j (g N) t - iteratedDeriv j K t‖ +
            ‖iteratedDeriv j (g M) t - iteratedDeriv j K t‖ := by
        calc
          _ = ‖(iteratedDeriv j (g N) t - iteratedDeriv j K t) -
              (iteratedDeriv j (g M) t - iteratedDeriv j K t)‖ := by congr 1; abel
          _ ≤ _ := norm_sub_le _ _
      apply one_add_abs_pow_mul_le_of_two_bounds q _ _ _ (norm_nonneg _)
      · exact hTri.trans (by linarith [hN'.1, hM'.1])
      · refine (mul_le_mul_of_nonneg_left hTri (by positivity)).trans ?_
        rw [mul_add]
        linarith [hN'.2, hM'.2]
    have hDiff : F N x - F M x = fourierPrimitiveKernelPairing T (g N - g M) x := by
      simp [F, fourierPrimitiveKernelPairing, map_sub]
    rw [hDiff]
    refine (norm_fourierPrimitiveKernelPairing_le T q D hD hT _ _ (by positivity) hG x).trans ?_
    rw [show D * (2 ^ q * (2 * δ)) = L * (2 * δ) by dsimp [L]; ring]
    exact mul_le_mul_of_nonneg_right hCoeff (by positivity)
  have hPoint (x : ℝ) : ∃ y : ℂ, Tendsto (fun N => F N x) atTop (𝓝 y) := by
    apply cauchySeq_tendsto_of_complete
    refine Metric.cauchySeq_iff.mpr fun ε hε => ?_
    let w := (1 + |x|) ^ q
    have hw : 0 < w := by dsimp [w]; positivity
    obtain ⟨N₀, hN₀⟩ := hCauchy (ε / (2 * w)) (div_pos hε (by positivity))
    refine ⟨N₀, fun N hN M hM => ?_⟩
    rw [dist_eq_norm]
    have hhalf : ε / (2 * w) * w = ε / 2 := by field_simp [hw.ne']
    exact (hN₀ N hN M hM x).trans_lt (by change ε / (2 * w) * w < ε; rw [hhalf]; linarith)
  choose f hf using hPoint
  have hConverges (ε : ℝ) (hε : 0 < ε) : ∀ᶠ N : ℕ in atTop, ∀ x : ℝ,
      ‖F N x - f x‖ ≤ ε * (1 + |x|) ^ q := by
    obtain ⟨N₀, hN₀⟩ := hCauchy ε hε
    filter_upwards [eventually_ge_atTop N₀] with N hN
    intro x
    apply le_of_tendsto ((tendsto_const_nhds.sub (hf x)).norm)
    filter_upwards [eventually_ge_atTop N₀] with M hM
    exact hN₀ N hN M hM x
  have hLocal : TendstoLocallyUniformly F f atTop := Metric.tendstoLocallyUniformly_iff.mpr <| by
    intro ε hε x
    let R := |x| + 1
    have hx : x ∈ Ioo (-R) R := abs_lt.mp (by dsimp [R]; linarith)
    let W := (1 + R) ^ q
    have hW : 0 < W := by dsimp [W, R]; positivity
    refine ⟨Icc (-R) R, Icc_mem_nhds hx.1 hx.2, ?_⟩
    have hScale : 0 < ε / (2 * W) := div_pos hε (by positivity)
    filter_upwards [hConverges (ε / (2 * W)) hScale] with N hN
    intro y hy
    have hAbs : |y| ≤ R := abs_le.mpr hy
    have hBound : (1 + |y|) ^ q ≤ W := pow_le_pow_left₀ (by positivity) (by linarith) q
    rw [dist_comm, dist_eq_norm]
    calc
      _ ≤ ε / (2 * W) * (1 + |y|) ^ q := hN y
      _ ≤ ε / (2 * W) * W := mul_le_mul_of_nonneg_left hBound hScale.le
      _ = ε / 2 := by field_simp [hW.ne']
      _ < ε := half_lt_self hε
  have hContinuous : Continuous f :=
    hLocal.continuous (Eventually.of_forall fun N => continuous_fourierPrimitiveKernelPairing T (g N)).frequently
  obtain ⟨N₁, hN₁⟩ := (hConverges 1 zero_lt_one).exists
  let B := (2 : ℝ) ^ q * ((Finset.Iic (q, q)).sup (schwartzSeminormFamily ℂ ℝ ℂ)) (g N₁)
  have hB : 0 ≤ B := mul_nonneg (by positivity) (apply_nonneg _ _)
  have hF (x : ℝ) : ‖F N₁ x‖ ≤ D * B * (1 + |x|) ^ q := by
    apply norm_fourierPrimitiveKernelPairing_le T q D hD hT (g N₁) B hB _ x
    intro j hj t
    change _ ≤ (2 : ℝ) ^ q * ((Finset.Iic (q, q)).sup
      (fun i => SchwartzMap.seminorm ℂ i.1 i.2)) (g N₁)
    simpa only [Real.norm_eq_abs, norm_iteratedFDeriv_eq_norm_iteratedDeriv] using
      SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (q, q)) (k := q) le_rfl hj (g N₁) t
  refine ⟨f, hContinuous, ⟨D * B + 1, by positivity, fun x => ?_⟩, hConverges⟩
  calc
    ‖f x‖ = ‖F N₁ x + (f x - F N₁ x)‖ := by congr 1; abel
    _ ≤ ‖F N₁ x‖ + ‖f x - F N₁ x‖ := norm_add_le _ _
    _ = ‖F N₁ x‖ + ‖F N₁ x - f x‖ := by rw [norm_sub_rev]
    _ ≤ _ := by have hh := add_le_add (hF x) (hN₁ x); rw [one_mul] at hh; simpa [add_mul] using hh

end
end MeyerGeneralProblem
