module

public import MeyerGeneralProblem.Distribution.OriginalAtomicTorusLocalization
public import MeyerGeneralProblem.Distribution.OriginalGroupedNewtonMoments
public import MeyerGeneralProblem.Distribution.DiscreteSupportPoisson

@[expose] public section

/-!
# Translated Schwartz estimates for original grouped atomic records

Compact tests are paired through the original Newton moments and the
corresponding divided differences. A unit-window count bounds the sum of
inverse-quadratic weights at the cluster anchors. Compact Schwartz
approximation then gives the same estimate for every Schwartz test.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter MeasureTheory Set
open scoped ContDiff ENNReal FourierTransform SchwartzMap Topology

private theorem summable_grouped_unitCell_weight :
    Summable (fun n : ℤ => (1 + (n : ℝ) ^ 2)⁻¹) := by
  have hs : Summable (fun n : ℤ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_int_pow.mpr (by norm_num)
  apply hs.of_norm_bounded_eventually
  filter_upwards [eventually_cofinite_ne (0 : ℤ)] with n hn
  have hn₀ : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [Real.norm_of_nonneg (by positivity), ← one_div]
  exact one_div_le_one_div_of_le (sq_pos_of_ne_zero hn₀) (by linarith)

/-- A uniform half-open unit-window cap controls the inverse-quadratic
mass of every finite subset, uniformly over translations. -/
theorem exists_sum_inverseQuadratic_le_of_unit_window_bound (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : LocallyFiniteCarrier), (∀ t, windowCount A t 1 ≤ K) →
      ∀ {ι : Type*} (a : ι → ℝ), Function.Injective a →
      (∀ i, a i ∈ A.carrier) → ∀ (E : Finset ι) (t : ℝ),
        (∑ i ∈ E, (1 + (a i - t) ^ 2)⁻¹) ≤ C := by
  classical
  let w (n : ℤ) := (1 + (n : ℝ) ^ 2)⁻¹
  have hw (n : ℤ) : 0 ≤ w n := by dsimp [w]; positivity
  let C := (3 * (K : ℝ)) * ∑' n, w n
  have hC : 0 ≤ C := mul_nonneg (by positivity) (tsum_nonneg hw)
  refine ⟨C, hC, ?_⟩
  intro A hA ι a hInj hMem E t
  let g (i : ι) := ⌊a i - t⌋
  let L (n : ℤ) := E.filter (fun i => g i = n)
  let p (i : ι) := (1 + (a i - t) ^ 2)⁻¹
  have hMaps (i : ι) (hi : i ∈ E) : g i ∈ E.image g := Finset.mem_image_of_mem _ hi
  have hCell (i : ι) (n : ℤ) (hi : i ∈ L n) : a i ∈ Ico (t + n) (t + n + 1) := by
    have h : g i = n := (Finset.mem_filter.mp hi).2
    have h0 := Int.floor_le (a i - t)
    have h1 := Int.lt_floor_add_one (a i - t)
    change (g i : ℝ) ≤ _ at h0
    change _ < (g i : ℝ) + 1 at h1
    rw [h] at h0 h1
    exact ⟨by linarith, by linarith⟩
  have hP (n : ℤ) (i : ι) (hi : i ∈ L n) : p i ≤ 3 * w n := by
    have h := hCell i n hi
    have he : 0 ≤ a i - t - n := by linarith [h.1]
    have he' : a i - t - n ≤ 1 := by linarith [h.2]
    have hs := pow_le_pow_left₀ he he' 2
    have hGeom : 1 + (n : ℝ) ^ 2 ≤ 3 * (1 + (a i - t) ^ 2) := by
      nlinarith [hs, sq_nonneg ((a i - t) + (a i - t - n))]
    have hDiv : 1 / (1 + (a i - t) ^ 2) ≤ 3 / (1 + (n : ℝ) ^ 2) :=
      (div_le_div_iff₀ (by positivity) (by positivity)).mpr (by simpa only [one_mul] using hGeom)
    simpa only [p, w, div_eq_mul_inv, one_mul] using hDiv
  have hCount (n : ℤ) : (L n).card ≤ K := by
    have hs : ((L n).image a : Set ℝ) ⊆ A.carrier ∩ Ico (t + n) (t + n + 1) := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact ⟨hMem i, hCell i n hi⟩
    have hh := Set.ncard_le_ncard hs (A.finite_window (t + n) 1)
    rw [Set.ncard_coe_finset, Finset.card_image_of_injective _ hInj] at hh
    exact hh.trans (hA _)
  have hSum (n : ℤ) : (∑ i ∈ L n, p i) ≤ (3 * (K : ℝ)) * w n := by
    calc
      _ ≤ ∑ i ∈ L n, 3 * w n := Finset.sum_le_sum (fun i hi => hP n i hi)
      _ = (L n).card * (3 * w n) := by simp
      _ ≤ (K : ℝ) * (3 * w n) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hCount n) (by positivity)
      _ = _ := by ring
  change (∑ i ∈ E, p i) ≤ C
  rw [← Finset.sum_fiberwise_of_maps_to hMaps p]
  calc
    _ ≤ ∑ n ∈ E.image g, (3 * (K : ℝ)) * w n := Finset.sum_le_sum (fun n _ => hSum n)
    _ = (3 * (K : ℝ)) * ∑ n ∈ E.image g, w n := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (summable_grouped_unitCell_weight.sum_le_tsum _ (fun n _ => hw n)) (by positivity)

namespace BoundedClusterOrder

variable {A : LocallyFiniteCarrier} {d : ℝ} {q : ℕ} (ho : BoundedClusterOrder A d q)

/-- Every compact test is evaluated by an exact finite sum of complete
canonical cluster Newton moments and its initial divided differences. -/
theorem exists_compact_original_grouped_expansion
    (T : TemperedDistribution ℝ ℂ) (hAt : AtomicOnCarrier A T)
    (f : SchwartzMap ℝ ℂ) (hfc : HasCompactSupport (f : ℝ → ℂ)) :
    ∃ E : Finset (CanonicalClusterIndex A d),
      T f = ∑ C ∈ E, ∑ j : Fin (ho.clusterSize C),
        ho.originalClusterNewtonMoment T C j * ho.canonicalPrefixData f C j := by
  classical
  obtain ⟨F, hF⟩ := A.exists_finite_nonzero_values_of_hasCompactSupport f hfc
  let E := F.image (fun x => (ho.canonicalNodeEquiv.symm x).1)
  let H := (E.sigma (fun C => (Finset.univ : Finset (Fin (ho.clusterSize C))))).map
    ho.canonicalNodeEquiv.toEmbedding
  have hOff (x : A.subtype) (hx : x ∉ H) : f x = 0 := by
    by_contra h
    have hF' : x ∈ F := not_imp_comm.mp (hF x) h
    apply hx
    apply Finset.mem_map.mpr
    refine ⟨ho.canonicalNodeEquiv.symm x, Finset.mem_sigma.mpr ?_, ho.canonicalNodeEquiv.apply_symm_apply x⟩
    exact ⟨Finset.mem_image_of_mem _ hF', Finset.mem_univ _⟩
  refine ⟨E, ?_⟩
  rw [atomicOnCarrier_apply_eq_sum_of_compact_of_zero_off_finset A T hAt f hfc H hOff]
  have hSumH :
      (∑ x ∈ H, T (A.isolationSchwartz x) * f x) =
      ∑ C ∈ E, ∑ i : Fin (ho.clusterSize C), T (A.isolationSchwartz (ho.orderedClusterNode C i)) *
        f (ho.orderedClusterNode C i) := by
    unfold H
    rw [Finset.sum_map]
    exact (Finset.sum_sigma' E (fun _ => Finset.univ) (fun C i =>
      T (A.isolationSchwartz (ho.orderedClusterNode C i)) * f (ho.orderedClusterNode C i))).symm
  rw [hSumH]
  apply Finset.sum_congr rfl
  intro C _
  have hEval (i : Fin (ho.clusterSize C)) :
      f (ho.orderedClusterNode C i) =
        ∑ j : Fin (ho.clusterSize C), ho.canonicalPrefixData f C j *
          (ho.clusterNewtonPolynomial C j).eval (ho.realClusterNode C i : ℂ) := by
    change f (ho.realClusterNode C i) = _
    rw [values_eq_newtonInterpolant_of_initialData (ho.realClusterNode C)
      ((ho.realClusterNode_strictMono C).injective) (f : ℝ → ℂ) _ (fun _ => rfl) i,
      newtonInterpolant_eq_sum, Polynomial.eval_finsetSum]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, clusterNewtonPolynomial, canonicalPrefixData]
  change (∑ i : Fin (ho.clusterSize C), T (A.isolationSchwartz (ho.orderedClusterNode C i)) *
    f (ho.orderedClusterNode C i)) = _
  simp_rw [hEval, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [originalClusterNewtonMoment, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring


/-- Uniformly bounded original Newton moments give the exact weight-two
Schwartz bound on every translate, through the last derivative of a cluster. -/
theorem exists_uniform_translated_schwartz_bound_factor_of_newtonMoments
    (K q : ℕ) {d : ℝ} (hd : 0 < d) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (A : LocallyFiniteCarrier) (ho : BoundedClusterOrder A d q),
      (∀ t, windowCount A t 1 ≤ K) →
      ∀ (T : TemperedDistribution ℝ ℂ), AtomicOnCarrier A T → ∀ M : ℝ, 0 ≤ M →
      (∀ (C : CanonicalClusterIndex A d) (j : Fin (ho.clusterSize C)),
        ‖ho.originalClusterNewtonMoment T C j‖ ≤ M) →
      ∀ (t : ℝ) (f : SchwartzMap ℝ ℂ),
        ‖combDistributionTranslation (-t) T f‖ ≤
          D * M * ((Finset.Iic (2, q - 1)).sup (schwartzSeminormFamily ℂ ℝ ℂ)) f := by
  classical
  obtain ⟨S, hS, hSum⟩ := exists_sum_inverseQuadratic_le_of_unit_window_bound K
  let Δ := (q : ℝ) * d
  let Cder := 4 * (1 + Δ ^ 2)
  let D := (q : ℝ) * Cder * S
  have hD : 0 ≤ D := by dsimp [D, Cder]; positivity
  refine ⟨D, hD, ?_⟩
  intro A ho hCount T hAt M hM hMom
  let C := D * M
  let P := (Finset.Iic (2, q - 1)).sup (schwartzSeminormFamily ℂ ℝ ℂ)
  let a (C : CanonicalClusterIndex A d) := ho.clusterLower C
  have hMem (C : CanonicalClusterIndex A d) : a C ∈ A.carrier :=
    ho.realClusterNode_mem _ _
  have hAinj : Function.Injective a := by
    intro C D he
    by_contra hne
    have h := ho.realClusterNode_separated hne ⟨0, ho.clusterSize_pos C⟩ ⟨0, ho.clusterSize_pos D⟩
    change d ≤ |a C - a D| at h
    rw [he, sub_self, abs_zero] at h
    exact (not_le_of_gt hd) h
  have hCompact (t : ℝ) (f : SchwartzMap ℝ ℂ) (hfc : HasCompactSupport (f : ℝ → ℂ)) :
      ‖combDistributionTranslation (-t) T f‖ ≤ C * P f := by
    let V := combSchwartzTranslation (-t) f
    have hVFun : (V : ℝ → ℂ) = (fun x => f ((-t) + x)) := rfl
    have hVc : HasCompactSupport (V : ℝ → ℂ) := hfc.comp_homeomorph (Homeomorph.addLeft (-t))
    obtain ⟨E, hE⟩ := ho.exists_compact_original_grouped_expansion T hAt V hVc
    have hDeriv (j : ℕ) (x : ℝ) :
        iteratedDeriv j (V : ℝ → ℂ) x = iteratedDeriv j (f : ℝ → ℂ) (x - t) := by
      rw [hVFun, iteratedDeriv_comp_const_add]
      simp only [neg_add_eq_sub]
    let w (B : CanonicalClusterIndex A d) := (1 + (a B - t) ^ 2)⁻¹
    have hw (B : CanonicalClusterIndex A d) : 0 ≤ w B := by dsimp [w]; positivity
    have hPf : 0 ≤ P f := apply_nonneg _ _
    have hDD (B : CanonicalClusterIndex A d) (j : Fin (ho.clusterSize B)) :
        ‖ho.canonicalPrefixData (V : ℝ → ℂ) B j‖ ≤ Cder * P f * w B := by
      have hj : (j : ℕ) ≤ q - 1 := by
        have h := ho.clusterSize_le B
        have hlt := j.isLt
        omega
      have hNodes (i : ℕ) (hi : i ≤ j) :
          finiteNodeSequence (ho.realClusterNode B) i ∈ Icc (a B) (a B + Δ) := by
        have hi' : i < ho.clusterSize B := hi.trans_lt j.isLt
        rw [finiteNodeSequence, dite_eq_left hi']
        have h := ho.realClusterNode_diameter hd B ⟨i, hi'⟩ ⟨0, ho.clusterSize_pos B⟩
        have hu : |ho.realClusterNode B ⟨i, hi'⟩ - a B| ≤ Δ := by
          simpa only [Real.dist_eq, a, BoundedClusterOrder.clusterLower, Δ] using h
        exact ⟨(ho.realClusterNode_mem_hull B ⟨i, hi'⟩).1, by linarith [(abs_le.mp hu).2]⟩
      have hSup (x : ℝ) (hx : x ∈ Icc (a B) (a B + Δ)) :
          ‖iteratedDeriv (j : ℕ) (V : ℝ → ℂ) x‖ ≤ Cder * P f * w B := by
        rw [hDeriv]
        have h0 := SchwartzMap.le_seminorm ℂ 0 (j : ℕ) f (x - t)
        have h2 := SchwartzMap.le_seminorm ℂ 2 (j : ℕ) f (x - t)
        rw [pow_zero, one_mul, norm_iteratedFDeriv_eq_norm_iteratedDeriv] at h0
        rw [Real.norm_eq_abs, sq_abs, norm_iteratedFDeriv_eq_norm_iteratedDeriv] at h2
        have hP0 : SchwartzMap.seminorm ℂ 0 (j : ℕ) f ≤ P f :=
          Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℂ ℝ ℂ) (i := (0, (j : ℕ)))
            (Finset.mem_Iic.mpr ⟨by omega, hj⟩)
        have hP2 : SchwartzMap.seminorm ℂ 2 (j : ℕ) f ≤ P f :=
          Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℂ ℝ ℂ) (i := (2, (j : ℕ)))
            (Finset.mem_Iic.mpr ⟨by omega, hj⟩)
        have hProd : (1 + (x - t) ^ 2) * ‖iteratedDeriv (j : ℕ) (f : ℝ → ℂ) (x - t)‖ ≤ 2 * P f := by
          rw [add_mul, one_mul, two_mul]
          exact add_le_add (h0.trans hP0) (h2.trans hP2)
        have hxSquare : (x - a B) ^ 2 ≤ Δ ^ 2 :=
          pow_le_pow_left₀ (sub_nonneg.mpr hx.1) (by linarith [hx.2]) 2
        have hGeom : 1 + (a B - t) ^ 2 ≤ 2 * (1 + Δ ^ 2) * (1 + (x - t) ^ 2) := by
          nlinarith [hxSquare, sq_nonneg ((x - t) + (x - a B)),
            mul_nonneg (sq_nonneg Δ) (sq_nonneg (x - t))]
        change ‖iteratedDeriv (j : ℕ) (f : ℝ → ℂ) (x - t)‖ ≤
          Cder * P f * (1 + (a B - t) ^ 2)⁻¹
        rw [← div_eq_mul_inv]
        apply (le_div_iff₀ (by positivity)).mpr
        calc
          _ = (1 + (a B - t) ^ 2) * ‖iteratedDeriv (j : ℕ) (f : ℝ → ℂ) (x - t)‖ := mul_comm _ _
          _ ≤ (2 * (1 + Δ ^ 2) * (1 + (x - t) ^ 2)) *
              ‖iteratedDeriv (j : ℕ) (f : ℝ → ℂ) (x - t)‖ :=
            mul_le_mul_of_nonneg_right hGeom (norm_nonneg _)
          _ = (2 * (1 + Δ ^ 2)) * ((1 + (x - t) ^ 2) *
              ‖iteratedDeriv (j : ℕ) (f : ℝ → ℂ) (x - t)‖) := by ring
          _ ≤ (2 * (1 + Δ ^ 2)) * (2 * P f) := mul_le_mul_of_nonneg_left hProd (by positivity)
          _ = _ := by change _ = 4 * (1 + Δ ^ 2) * P f; ring
      have hH := norm_analyticDividedDifference_le_of_contDiff (finiteNodeSequence (ho.realClusterNode B))
        (j : ℕ) (V.smooth _) hNodes hSup
      have hFac : (1 : ℝ) ≤ ((j : ℕ).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
      exact hH.trans (div_le_self (by positivity) hFac)
    have hGroup (B : CanonicalClusterIndex A d) :
        ‖∑ j : Fin (ho.clusterSize B),
            ho.originalClusterNewtonMoment T B j * ho.canonicalPrefixData (V : ℝ → ℂ) B j‖ ≤
          ((q : ℝ) * M * Cder * P f) * w B := by
      calc
        _ ≤ ∑ j : Fin (ho.clusterSize B),
          ‖ho.originalClusterNewtonMoment T B j * ho.canonicalPrefixData (V : ℝ → ℂ) B j‖ :=
            norm_sum_le _ _
        _ ≤ ∑ _j : Fin (ho.clusterSize B), M * (Cder * P f * w B) := by
          apply Finset.sum_le_sum
          intro j _
          rw [norm_mul]
          exact mul_le_mul (hMom B j) (hDD B j) (norm_nonneg _) hM
        _ = (ho.clusterSize B : ℝ) * (M * (Cder * P f * w B)) := by simp
        _ ≤ (q : ℝ) * (M * (Cder * P f * w B)) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast ho.clusterSize_le B) (by positivity)
        _ = _ := by ring
    change ‖T V‖ ≤ _
    rw [hE]
    calc
      _ ≤ ∑ B ∈ E, ‖∑ j : Fin (ho.clusterSize B),
          ho.originalClusterNewtonMoment T B j * ho.canonicalPrefixData (V : ℝ → ℂ) B j‖ := norm_sum_le _ _
      _ ≤ ∑ B ∈ E, ((q : ℝ) * M * Cder * P f) * w B :=
        Finset.sum_le_sum (fun B _ => hGroup B)
      _ = ((q : ℝ) * M * Cder * P f) * ∑ B ∈ E, w B := (Finset.mul_sum _ _ _).symm
      _ ≤ ((q : ℝ) * M * Cder * P f) * S :=
        mul_le_mul_of_nonneg_left (hSum A hCount a hAinj hMem E t) (by positivity)
      _ = _ := by dsimp [C, D]; ring
  intro t f
  let L := (combDistributionTranslation (-t) T : TemperedDistribution ℝ ℂ)
  have hP : Continuous P := Seminorm.continuous_finsetSup (fun i _ =>
    (schwartz_withSeminorms ℂ ℝ ℂ).continuous_seminorm i)
  have hL := compactSchwartzApproximation_tendsto f
  exact le_of_tendsto_of_tendsto ((L.continuous.tendsto _).comp hL).norm
    ((((hP.tendsto _).comp hL).const_mul C)) (Eventually.of_forall (fun N =>
      hCompact t _ (compactSchwartzApproximation_hasCompactSupport N f)))

end BoundedClusterOrder

/-- One fixed compact Fourier window gives a uniformly bounded family of
translates of the original clustered value-only measure. -/
theorem exists_uniform_translated_schwartz_bound_of_broad_pair_of_density
    (A B : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ)
    (hA : AtomicOnCarrier A T) (hB : AtomicOnCarrier B (𝓕 T))
    (K : ℕ) (hCount : ∀ t, windowCount A t 1 ≤ K)
    (R : ℝ) (hR : 0 < R)
    (hρ : upperUniformBeurlingDensity A < ENNReal.ofReal (2 * R)) :
    ∃ q : ℕ, 0 < q ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ (t : ℝ) (f : SchwartzMap ℝ ℂ),
        ‖combDistributionTranslation (-t) T f‖ ≤
          C * ((Finset.Iic (2, q - 1)).sup (schwartzSeminormFamily ℂ ℝ ℂ)) f := by
  obtain ⟨d, hd, q, hq, ho⟩ :=
    finiteUpperDensity_exists_boundedClusterOrder A (hρ.trans ENNReal.ofReal_lt_top)
  obtain ⟨M, hM, hm⟩ := ho.exists_uniform_originalClusterNewtonMoment_bound B T hA hB hd hR hρ
  obtain ⟨D, hD, hEstimate⟩ :=
    BoundedClusterOrder.exists_uniform_translated_schwartz_bound_factor_of_newtonMoments K q hd
  exact ⟨q, hq, D * M, mul_nonneg hD hM, hEstimate A ho hCount T hA M hM hm⟩

/-- A relatively separated physical record has uniform translated Schwartz
order with a weight of two, using only local atomicity of the Fourier record. -/
theorem exists_uniform_translated_schwartz_bound_of_broad_pair
    (A B : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ)
    (hA : AtomicOnCarrier A T) (hB : AtomicOnCarrier B (𝓕 T))
    (K : ℕ) (hCount : ∀ t, windowCount A t 1 ≤ K) :
    ∃ q : ℕ, 0 < q ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ (t : ℝ) (f : SchwartzMap ℝ ℂ),
        ‖combDistributionTranslation (-t) T f‖ ≤
          C * ((Finset.Iic (2, q - 1)).sup (schwartzSeminormFamily ℂ ℝ ℂ)) f := by
  obtain ⟨R, hR, hρ⟩ := exists_strict_upperDensity_radius_of_unit_window_bound A K hCount
  exact exists_uniform_translated_schwartz_bound_of_broad_pair_of_density
    A B T hA hB K hCount R hR hρ

/-- The original rectangular localization produces a finite annihilator for a
broad pair with one relatively separated record and a weighted opposite record. -/
theorem exists_originalModule_finite_annihilator_of_weighted_spectral_record
    {d : Type*} [Fintype d] [DecidableEq d]
    (A B : LocallyFiniteCarrier) (β : d → ℝ) (L : (d → ℤ) →+ ℝ)
    (hL : Function.Injective L) (hLfreq : ∀ n, L n = torusDirectionalFrequency β n)
    (label : B.subtype → d → ℤ) (hLabel : ∀ x : B.subtype, L (label x) = (x : ℝ))
    (N : ℕ) (μ : TemperedDistribution ℝ ℂ)
    (hν : 𝓕 μ ∈ stronglyTemperedAtomicAtExponent B N)
    (hA : AtomicOnCarrier A μ) (hB : AtomicOnCarrier B (𝓕 μ))
    (hActual : ∀ x : A.subtype, μ (A.isolationSchwartz x) ≠ 0)
    {K : ℕ} (hCount : ∀ x, windowCount A x 1 ≤ K) :
    ∃ p : (d → ℤ) →₀ ℂ, p ≠ 0 ∧
      (∃ y : ℝ, annihilatorExponentialSymbol L p y ≠ 0) ∧
      (∀ x ∈ A.carrier, annihilatorExponentialSymbol L p x = 0) ∧
      finiteExponentialMultiplication (fun i : p.support => L i.1)
        (fun i : p.support => p i.1) μ = 0 := by
  obtain ⟨q, hq, D, hD, hUniform⟩ :=
    exists_uniform_translated_schwartz_bound_of_broad_pair A B μ hA hB K hCount
  exact exists_originalModule_finite_annihilator_of_translated_schwartz_bound
    A B β L hL hLfreq label hLabel N μ hν hA hB hActual hCount q hq D hD hUniform

/-- For a common cap on the physical supports, one common compact Fourier
window controls the translated Schwartz estimates by its actual mass. -/
theorem exists_uniform_translated_schwartz_bound_factor_of_unit_window_cap
    (K : ℕ) (hK : 0 < K) :
    ∃ (W D : ℝ) (q : ℕ), 0 < W ∧ 0 ≤ D ∧ 0 < q ∧
      ∀ (A B : LocallyFiniteCarrier), (∀ t, windowCount A t 1 ≤ K) →
        ∀ T : TemperedDistribution ℝ ℂ,
          AtomicOnCarrier A T → AtomicOnCarrier B (𝓕 T) →
          ∀ (t : ℝ) (f : SchwartzMap ℝ ℂ),
            ‖combDistributionTranslation (-t) T f‖ ≤
              D * originalClosedWindowMass B (𝓕 T) W *
                ((Finset.Iic (2, q - 1)).sup (schwartzSeminormFamily ℂ ℝ ℂ)) f := by
  let d : ℝ := 1 / (2 * (K : ℝ))
  let q := 4 * K - 1
  have hd : 0 < d := by dsimp [d]; positivity
  obtain ⟨W, M, hW, hM, hMoment⟩ :=
    BoundedClusterOrder.exists_uniform_originalClusterNewtonMoment_factor_of_unit_window_cap K q hd
  obtain ⟨D, hD, hBound⟩ :=
    BoundedClusterOrder.exists_uniform_translated_schwartz_bound_factor_of_newtonMoments K q hd
  refine ⟨W, D * M, q, hW, mul_nonneg hD hM, by dsimp [q]; omega, ?_⟩
  intro A B hCount T hA hB t f
  have ho : BoundedClusterOrder A d q := boundedClusterOrder_of_unitCellBound hK
    (fun n => hCount n)
  have hMass := originalClosedWindowMass_nonneg B (𝓕 T) W
  have h := hBound A ho hCount T hA (originalClosedWindowMass B (𝓕 T) W * M)
    (mul_nonneg hMass hM) (hMoment A ho hCount B T hA hB) t f
  convert h using 1
  ring

end
end MeyerGeneralProblem
