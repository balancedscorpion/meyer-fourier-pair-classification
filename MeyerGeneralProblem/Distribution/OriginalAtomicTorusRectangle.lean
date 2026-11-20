module

public import MeyerGeneralProblem.Distribution.OriginalAtomicTorusSpectralEquations
public import MeyerGeneralProblem.Distribution.TorusPoissonCayleyCutoffCovariance
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

@[expose] public section

/-!
# Finite rectangular localization of the original spectral equations

Both directional band cutoffs are part of the same bounded operator.
Cube truncation of a full kernel vector leaves residual rows only in
its finite propagation shell. Orthogonal projection onto the column
span gives a rank lower bound using a single nonzero diagonal entry.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter Set
open scoped ENNReal InnerProductSpace Topology

local notation "SeqL2(" G ")" => lp (fun _ : G => ℂ) 2

section

variable {G : Type*} [AddCommGroup G]

/-- The finite set of original frequencies which can couple the closed
input band to the open output band. -/
def originalConvolutionWindow (L : G →+ ℝ) (u : G → ℂ) (hu : FrequencyLocallyFinite L u)
    (W a b : ℝ) : Finset G :=
  (hu (a - W) b).toFinset

/-- The literal rectangular operator with both horizontal band cutoffs. -/
def originalBandConvolution (L : G →+ ℝ) (u : G → ℂ) (hu : FrequencyLocallyFinite L u)
    (W a b : ℝ) : SeqL2(G) →L[ℂ] SeqL2(G) :=
  lpCoordinateProjection {k | L k ∈ Ioo a b} ∘L
    (∑ m ∈ originalConvolutionWindow L u hu W a b,
      u m • (lpFrequencyShift m).toLinearIsometry.toContinuousLinearMap) ∘L
    lpCoordinateProjection {k | L k ∈ Icc 0 W}

theorem originalBandConvolution_apply (L : G →+ ℝ) (u : G → ℂ) (hu : FrequencyLocallyFinite L u)
    (W a b : ℝ) (f : SeqL2(G)) (k : G) :
    originalBandConvolution L u hu W a b f k =
      if L k ∈ Ioo a b then
        ∑ m ∈ originalConvolutionWindow L u hu W a b,
          if L (k - m) ∈ Icc 0 W then u m * f (k - m) else 0
      else 0 := by
  classical
  unfold originalBandConvolution
  simp only [ContinuousLinearMap.comp_apply, lpCoordinateProjection_apply,
    Set.indicator_apply, Set.mem_ofPred_eq]
  split
  · rw [sum_apply]
    change (∑ m ∈ originalConvolutionWindow L u hu W a b,
      u m • lpFrequencyShift m (lpCoordinateProjection {k | L k ∈ Icc 0 W} f)) k = _
    rw [lp.coeFn_sum]
    simp only [Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
      lpFrequencyShift_apply, lpCoordinateProjection_apply, Set.indicator_apply, Set.mem_ofPred_eq,
      mul_ite, mul_zero]
  · rfl

/-- On the output band the rectangle reads the full original row
when the input sequence is supported in the input band. -/
theorem originalBandConvolution_apply_eq_tsum_of_mem_output
    (L : G →+ ℝ) (u : G → ℂ) (hu : FrequencyLocallyFinite L u) (W a b : ℝ)
    (f : SeqL2(G)) (hBand : ∀ j : G, f j ≠ 0 → L j ∈ Icc 0 W)
    (k : G) (hk : L k ∈ Ioo a b) :
    originalBandConvolution L u hu W a b f k = ∑' j, f j * u (k - j) := by
  classical
  rw [originalBandConvolution_apply, ite_eq_left hk]
  have hterm (m : G) :
      (if L (k - m) ∈ Icc 0 W then u m * f (k - m) else 0) = u m * f (k - m) := by
    split
    · rfl
    · next hm => rw [show f (k - m) = 0 from by by_contra h; exact hm (hBand _ h), mul_zero]
  simp_rw [hterm]
  have hOutside (m : G) (hm : m ∉ originalConvolutionWindow L u hu W a b) :
      u m * f (k - m) = 0 := by
    by_contra hne
    have hn := mul_ne_zero_iff.mp hne
    have hFreq := hBand (k - m) hn.2
    apply hm
    apply (hu (a - W) b).mem_toFinset.mpr
    refine ⟨hn.1, ?_⟩
    rw [map_sub] at hFreq
    exact ⟨by linarith [hk.1, hFreq.2], by linarith [hk.2, hFreq.1]⟩
  calc
    _ = ∑' m : G, u m * f (k - m) := (tsum_eq_sum hOutside).symm
    _ = ∑' j : G, f j * u (k - j) := by
      have h := (Equiv.subLeft k).tsum_eq (fun j => f j * u (k - j))
      change (∑' m : G, f (k - m) * u (k - (k - m))) = _ at h
      simpa only [sub_sub_cancel, mul_comm] using h

theorem originalBandConvolution_eq_zero_of_global_rows (L : G →+ ℝ) (u : G → ℂ)
    (hu : FrequencyLocallyFinite L u) (W a b : ℝ) (f : SeqL2(G))
    (hBand : ∀ j : G, f j ≠ 0 → L j ∈ Icc 0 W)
    (hRows : ∀ k, (∑' j, f j * u (k - j)) = 0) :
    originalBandConvolution L u hu W a b f = 0 := by
  classical
  ext k
  change originalBandConvolution L u hu W a b f k = (0 : ℂ)
  by_cases hk : L k ∈ Ioo a b
  · rw [originalBandConvolution_apply_eq_tsum_of_mem_output L u hu W a b f hBand k hk, hRows]
  · rw [originalBandConvolution_apply, ite_eq_right hk]

/-- A band shift staying within the input band remains in the kernel
of the same rectangle, including every row of the open output window. -/
theorem originalBandConvolution_frequencyShift_eq_zero (L : G →+ ℝ) (u : G → ℂ)
    (hu : FrequencyLocallyFinite L u) (W₀ W a b : ℝ) (f : SeqL2(G))
    (hBand : ∀ j : G, f j ≠ 0 → L j ∈ Icc 0 W₀)
    (hRows : ∀ k, (∑' j, f j * u (k - j)) = 0)
    (γ : G) (hγ : L γ ∈ Icc 0 (W - W₀)) :
    originalBandConvolution L u hu W a b (lpFrequencyShift γ f) = 0 := by
  apply originalBandConvolution_eq_zero_of_global_rows
  · intro j hj
    rw [lpFrequencyShift_apply] at hj
    have hb := hBand (j - γ) hj
    rw [map_sub] at hb
    exact ⟨by linarith [hb.1, hγ.1], by linarith [hb.2, hγ.2]⟩
  · intro k
    simp only [lpFrequencyShift_apply]
    have h := (Equiv.addRight γ).tsum_eq (fun j => f (j - γ) * u (k - j))
    change (∑' j, f (j + γ - γ) * u (k - (j + γ))) = _ at h
    calc
      _ = ∑' j, f (j + γ - γ) * u (k - (j + γ)) := h.symm
      _ = ∑' j, f j * u ((k - γ) - j) := by
        apply tsum_congr
        intro j
        rw [add_sub_cancel_right, show k - (j + γ) = (k - γ) - j by abel]
      _ = _ := hRows (k - γ)

/-- The two coordinate cutoffs commute at every row whose active
inputs have the same cube membership as that output row. -/
theorem originalBandConvolution_coordinateProjection_apply_eq
    (L : G →+ ℝ) (u : G → ℂ) (hu : FrequencyLocallyFinite L u) (W a b : ℝ)
    (s : Set G) (f : SeqL2(G)) (k : G)
    (hLocal : ∀ m ∈ originalConvolutionWindow L u hu W a b, k - m ∈ s ↔ k ∈ s) :
    originalBandConvolution L u hu W a b (lpCoordinateProjection s f) k =
      lpCoordinateProjection s (originalBandConvolution L u hu W a b f) k := by
  classical
  by_cases hOut : L k ∈ Ioo a b
  · rw [originalBandConvolution_apply, ite_eq_left hOut, lpCoordinateProjection_apply, Set.indicator_apply]
    by_cases hk : k ∈ s
    · rw [ite_eq_left hk, originalBandConvolution_apply, ite_eq_left hOut]
      apply Finset.sum_congr rfl
      intro m hm
      rw [lpCoordinateProjection_apply, Set.indicator_apply, ite_eq_left ((hLocal m hm).mpr hk)]
    · rw [ite_eq_right hk]
      apply Finset.sum_eq_zero
      intro m hm
      have hNot : k - m ∉ s := fun h => hk ((hLocal m hm).mp h)
      rw [lpCoordinateProjection_apply, Set.indicator_apply, ite_eq_right hNot, mul_zero, ite_self]
  · simp [originalBandConvolution_apply, lpCoordinateProjection_apply, Set.indicator_apply, hOut]

end

/-- The coordinate cube uses the exact sup-norm cutoff on integral labels. -/
def integerCoordinateCube {d : Type*} (N : ℤ) : Set (d → ℤ) :=
  {n | ∀ i, |n i| ≤ N}

theorem integerCoordinateCube_sub_mem_iff_of_outside_shell {d : Type*}
    (N R : ℤ) (hR : 0 ≤ R) (k m : d → ℤ) (hm : m ∈ integerCoordinateCube R)
    (hk : k ∉ integerCoordinateCube (N + R) \ integerCoordinateCube (N - R - 1)) :
    k - m ∈ integerCoordinateCube N ↔ k ∈ integerCoordinateCube N := by
  by_cases hInner : k ∈ integerCoordinateCube (N - R - 1)
  · have hOutput : k ∈ integerCoordinateCube N := fun i => (hInner i).trans (by linarith)
    have hInput : k - m ∈ integerCoordinateCube N := by
      intro i
      change |k i - m i| ≤ N
      have hTri : |k i - m i| ≤ |k i| + |m i| := by
        simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le (k i) 0 (m i)
      linarith [hInner i, hm i]
    exact iff_of_true hInput hOutput
  · have hOuter : k ∉ integerCoordinateCube (N + R) := fun h => hk ⟨h, hInner⟩
    have hOutput : k ∉ integerCoordinateCube N := fun h => hOuter (fun i => (h i).trans (by linarith))
    have hInput : k - m ∉ integerCoordinateCube N := by
      intro h
      apply hOuter
      intro i
      have hTri := abs_add_le (k i - m i) (m i)
      rw [sub_add_cancel] at hTri
      have hBound : |k i - m i| ≤ N := h i
      linarith [hm i]
    exact iff_of_false hInput hOutput

/-- The only possible nonzero residual rows after cube truncation are
inside the open output band and the finite propagation shell. -/
theorem support_originalBandConvolution_coordinateProjection_cube_subset
    {d : Type*}
    (L : (d → ℤ) →+ ℝ) (u : (d → ℤ) → ℂ) (hu : FrequencyLocallyFinite L u)
    (W a b : ℝ) (N R : ℤ) (hR : 0 ≤ R)
    (hWindow : ∀ m ∈ originalConvolutionWindow L u hu W a b, m ∈ integerCoordinateCube R)
    (f : SeqL2(d → ℤ)) (hKernel : originalBandConvolution L u hu W a b f = 0) :
    Function.support (⇑(originalBandConvolution L u hu W a b
      (lpCoordinateProjection (integerCoordinateCube N) f)) : (d → ℤ) → ℂ) ⊆
      {k | L k ∈ Ioo a b} ∩ (integerCoordinateCube (N + R) \ integerCoordinateCube (N - R - 1)) := by
  classical
  intro k hk
  have hk' : originalBandConvolution L u hu W a b
      (lpCoordinateProjection (integerCoordinateCube N) f) k ≠ 0 := hk
  refine ⟨?_, ?_⟩
  · by_contra h
    change L k ∉ Ioo a b at h
    exact hk' (by rw [originalBandConvolution_apply, ite_eq_right h])
  · by_contra h
    apply hk'
    have hLoc (m : d → ℤ) (hm : m ∈ originalConvolutionWindow L u hu W a b) :
        k - m ∈ integerCoordinateCube N ↔ k ∈ integerCoordinateCube N :=
      integerCoordinateCube_sub_mem_iff_of_outside_shell N R hR k m (hWindow m hm) h
    rw [originalBandConvolution_coordinateProjection_apply_eq L u hu W a b
      (integerCoordinateCube N) f k hLoc, hKernel, map_zero]
    rfl

/-- A common diagonal entry and uniform column norm bound force a
quantitative lower bound on the dimension of the column span. -/
theorem card_mul_sq_norm_diagonal_le_finrank_span_columns {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (b : OrthonormalBasis ι ℂ E) (v : ι → E) (a : ℂ) (C : ℝ)
    (hDiag : ∀ i, ⟪b i, v i⟫_ℂ = a) (hCol : ∀ i, ‖v i‖ ^ 2 ≤ C) :
    (Fintype.card ι : ℝ) * ‖a‖ ^ 2 ≤
      (Module.finrank ℂ (Submodule.span ℂ (Set.range v)) : ℝ) * C := by
  classical
  let K := Submodule.span ℂ (Set.range v)
  let e := stdOrthonormalBasis ℂ K
  have hMem (i) : v i ∈ K := Submodule.subset_span ⟨i, rfl⟩
  have hProj (i : ι) : ‖K.orthogonalProjectionOnto (b i)‖ ^ 2 =
      ∑ j, ‖⟪(e j : E), b i⟫_ℂ‖ ^ 2 := by
    rw [← e.sum_sq_norm_inner_right (K.orthogonalProjectionOnto (b i))]
    simp_rw [K.inner_orthogonalProjectionOnto_eq_of_mem_left]
  have hTrace : (∑ i, ‖K.orthogonalProjectionOnto (b i)‖ ^ 2) = (Module.finrank ℂ K : ℝ) := by
    simp_rw [hProj]
    rw [Finset.sum_comm]
    trans ∑ j : Fin (Module.finrank ℂ K), (1 : ℝ)
    · apply Finset.sum_congr rfl
      intro j _
      rw [b.sum_sq_norm_inner_left]
      change ‖e j‖ ^ 2 = 1
      rw [e.orthonormal.norm_eq_one, one_pow]
    · simp
  have hEach (i : ι) : ‖a‖ ^ 2 ≤ ‖K.orthogonalProjectionOnto (b i)‖ ^ 2 * C := by
    have hi : ⟪K.starProjection (b i), v i⟫_ℂ = a := by
      rw [K.inner_starProjection_left_eq_right, K.starProjection_eq_self_iff.mpr (hMem i), hDiag]
    calc
      ‖a‖ ^ 2 = ‖⟪K.starProjection (b i), v i⟫_ℂ‖ ^ 2 := by rw [hi]
      _ ≤ (‖K.starProjection (b i)‖ * ‖v i‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm _ _) 2
      _ = ‖K.orthogonalProjectionOnto (b i)‖ ^ 2 * ‖v i‖ ^ 2 := by
        rw [mul_pow, K.starProjection_apply, Submodule.coe_norm]
      _ ≤ ‖K.orthogonalProjectionOnto (b i)‖ ^ 2 * C :=
        mul_le_mul_of_nonneg_left (hCol i) (sq_nonneg _)
  calc
    _ = ∑ _ : ι, ‖a‖ ^ 2 := by simp
    _ ≤ ∑ i, ‖K.orthogonalProjectionOnto (b i)‖ ^ 2 * C :=
      Finset.sum_le_sum fun i _ => hEach i
    _ = (Module.finrank ℂ K : ℝ) * C := by rw [← Finset.sum_mul, hTrace]


/-- The truncated shift columns retain a uniform positive fraction of
their input dimension whenever their common diagonal lies inside the cube. -/
theorem card_mul_sq_norm_le_finrank_span_cut_shift_columns
    {d ι : Type*} [Fintype ι] (N : ℤ) (r : SeqL2(d → ℤ)) (n₀ : d → ℤ)
    (γ : ι ↪ (d → ℤ)) (hCenter : ∀ i, n₀ + γ i ∈ integerCoordinateCube N) :
    let v (i : ι) := lpCoordinateProjection (integerCoordinateCube N) (lpFrequencyShift (γ i) r)
    (Fintype.card ι : ℝ) * ‖r n₀‖ ^ 2 ≤
      (Module.finrank ℂ (Submodule.span ℂ (Set.range v)) : ℝ) * ‖r‖ ^ 2 := by
  classical
  intro v
  let S := Submodule.span ℂ (Set.range v)
  let E : SeqL2(d → ℤ) →ₗ[ℂ] EuclideanSpace ℂ ι :=
    (WithLp.linearEquiv 2 ℂ (ι → ℂ)).symm.toLinearMap ∘ₗ
      LinearMap.pi fun i => (lp.evalCLM ℂ (fun _ : d → ℤ => ℂ) 2 (n₀ + γ i)).toLinearMap
  let w := E ∘ v
  have hEval (i j : ι) : w i j = r (n₀ + γ j - γ i) := by
    change v i (n₀ + γ j) = _
    simp only [v, lpCoordinateProjection_apply, Set.indicator_of_mem (hCenter j), lpFrequencyShift_apply]
  let b := EuclideanSpace.basisFun ι ℂ
  have hDiag (i : ι) : ⟪b i, w i⟫_ℂ = r n₀ := by
    rw [show b i = EuclideanSpace.single i 1 from EuclideanSpace.basisFun_apply ι ℂ i,
      EuclideanSpace.inner_single_left]
    simp only [map_one, one_mul, hEval, add_sub_cancel_right]
  have hSum : HasSum (fun n : d → ℤ => ‖r n‖ ^ (2 : ℕ)) (‖r‖ ^ (2 : ℕ)) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      lp.hasSum_norm (by norm_num : 0 < (2 : ℝ≥0∞).toReal) r
  have hCol (i : ι) : ‖w i‖ ^ 2 ≤ ‖r‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [hEval]
    let a (j : ι) := n₀ + γ j - γ i
    have ha : Function.Injective a := by
      intro j k h
      apply γ.injective
      exact add_left_cancel (sub_left_inj.mp h)
    calc
      _ = ∑ n ∈ (Finset.univ : Finset ι).image a, ‖r n‖ ^ 2 :=
        (Finset.sum_image (f := fun n => ‖r n‖ ^ 2) (fun _ _ _ _ h => ha h)).symm
      _ ≤ _ := by
        rw [← hSum.tsum_eq]
        exact hSum.summable.sum_le_tsum _ (fun _ _ => sq_nonneg _)
  have h := card_mul_sq_norm_diagonal_le_finrank_span_columns b w (r n₀) (‖r‖ ^ 2) hDiag hCol
  have hMap : Submodule.span ℂ (Set.range w) = S.map E := by
    dsimp only [S]
    rw [Submodule.map_span, ← Set.range_comp]
  have : FiniteDimensional ℂ S := FiniteDimensional.span_of_finite ℂ (Set.finite_range v)
  have hDim : Module.finrank ℂ (Submodule.span ℂ (Set.range w)) ≤ Module.finrank ℂ S := by
    rw [hMap]
    exact Submodule.finrank_map_le E S
  exact h.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hDim) (sq_nonneg _))

theorem integerCoordinateCube_finite {d : Type*} [Finite d] (N : ℤ) :
    (integerCoordinateCube (d := d) N).Finite := by
  let : Fintype d := Fintype.ofFinite d
  simpa only [integerCoordinateCube, abs_le, mem_Icc] using
    (Set.Finite.pi' fun (_ : d) => (finite_Icc (-N) N))

/-- Once the number of shifts dominates the size of the propagation shell,
a nonzero finite multiplier annihilates every row in the open output band. -/
theorem exists_finite_band_convolution_solution_of_card_shell_lt
    {d ι : Type*} [Finite d] [Fintype ι]
    (L : (d → ℤ) →+ ℝ) (u : (d → ℤ) → ℂ) (hu : FrequencyLocallyFinite L u)
    (W₀ W a b : ℝ) (r : SeqL2(d → ℤ))
    (hBand : ∀ j : d → ℤ, r j ≠ 0 → L j ∈ Icc 0 W₀)
    (hRows : ∀ k : d → ℤ, (∑' j : d → ℤ, r j * u (k - j)) = 0)
    (N R : ℤ) (hR : 0 ≤ R)
    (hWindow : ∀ m ∈ originalConvolutionWindow L u hu W a b, m ∈ integerCoordinateCube R)
    (n₀ : d → ℤ) (γ : ι ↪ (d → ℤ))
    (hCenter : ∀ i, n₀ + γ i ∈ integerCoordinateCube N)
    (hγ : ∀ i, L (γ i) ∈ Icc 0 (W - W₀))
    (hSize : (({k | L k ∈ Ioo a b} ∩
      (integerCoordinateCube (N + R) \ integerCoordinateCube (N - R - 1))).ncard : ℝ) * ‖r‖ ^ 2 <
      (Fintype.card ι : ℝ) * ‖r n₀‖ ^ 2) :
    ∃ p : (d → ℤ) →₀ ℂ, p ≠ 0 ∧
      (∀ j ∈ p.support, L j ∈ Icc 0 W) ∧
      ∀ k : d → ℤ, L k ∈ Ioo a b → annihilatorArrayConvolution p u k = 0 := by
  classical
  let v (i : ι) := lpCoordinateProjection (integerCoordinateCube N) (lpFrequencyShift (γ i) r)
  let S := Submodule.span ℂ (Set.range v)
  have : FiniteDimensional ℂ S := FiniteDimensional.span_of_finite ℂ (Set.finite_range v)
  let A := originalBandConvolution L u hu W a b
  let J := {k | L k ∈ Ioo a b} ∩ (integerCoordinateCube (N + R) \ integerCoordinateCube (N - R - 1))
  have hFinite : J.Finite := (integerCoordinateCube_finite (N + R)).subset fun k hk => hk.2.1
  let : Fintype J := hFinite.fintype
  have hShiftBand (i : ι) (j : d → ℤ) (hj : (lpFrequencyShift (γ i) r) j ≠ 0) :
      L j ∈ Icc 0 W := by
    rw [lpFrequencyShift_apply] at hj
    have hb := hBand (j - γ i) hj
    rw [map_sub] at hb
    exact ⟨by linarith [hb.1, (hγ i).1], by linarith [hb.2, (hγ i).2]⟩
  have hResidual (i : ι) : Function.support (⇑(A (v i)) : (d → ℤ) → ℂ) ⊆ J :=
    support_originalBandConvolution_coordinateProjection_cube_subset
      L u hu W a b N R hR hWindow (lpFrequencyShift (γ i) r)
      (originalBandConvolution_frequencyShift_eq_zero L u hu W₀ W a b r hBand hRows (γ i) (hγ i))
  have hDim : Module.finrank ℂ (J → ℂ) < Module.finrank ℂ S := by
    have hRank := card_mul_sq_norm_le_finrank_span_cut_shift_columns N r n₀ γ hCenter
    change _ < (Fintype.card ι : ℝ) * ‖r n₀‖ ^ 2 at hSize
    change (J.ncard : ℝ) * ‖r‖ ^ 2 < _ at hSize
    have h := lt_of_mul_lt_mul_right (hSize.trans_le hRank) (sq_nonneg _)
    rw [Module.finrank_fintype_fun_eq_card, Set.fintypeCard_eq_ncard]
    exact_mod_cast h
  let Y : S →ₗ[ℂ] (J → ℂ) := LinearMap.pi fun k =>
    (lp.evalCLM ℂ (fun _ : d → ℤ => ℂ) 2 k.1).toLinearMap ∘ₗ A.toLinearMap ∘ₗ S.subtype
  have hY : LinearMap.ker Y ≠ ⊥ := by
    intro h
    exact (not_le_of_gt hDim) (LinearMap.finrank_le_finrank_of_injective (LinearMap.ker_eq_bot.mp h))
  obtain ⟨x, hx, hx0⟩ := (LinearMap.ker Y).ne_bot_iff.mp hY
  let y : SeqL2(d → ℤ) := x
  have hA0 : A y = 0 := by
    ext k
    change A y k = 0
    by_cases hk : k ∈ J
    · exact congrFun (LinearMap.mem_ker.mp hx) ⟨k, hk⟩
    · let φ := (lp.evalCLM ℂ (fun _ : d → ℤ => ℂ) 2 k).toLinearMap ∘ₗ A.toLinearMap
      have hc : S ≤ LinearMap.ker φ := Submodule.span_le.mpr (by
        rintro _ ⟨i, rfl⟩
        exact LinearMap.mem_ker.mpr (by
          by_contra h
          exact hk (hResidual i h)))
      exact LinearMap.mem_ker.mp (hc x.property)
  have hCut (k : d → ℤ) (hk : k ∉ integerCoordinateCube N ∨ L k ∉ Icc 0 W) : y k = 0 := by
    let φ := (lp.evalCLM ℂ (fun _ : d → ℤ => ℂ) 2 k).toLinearMap
    have hc : S ≤ LinearMap.ker φ := Submodule.span_le.mpr (by
      rintro _ ⟨i, rfl⟩
      apply LinearMap.mem_ker.mpr
      change v i k = 0
      rw [lpCoordinateProjection_apply, Set.indicator_apply]
      rcases hk with h | h
      · rw [ite_eq_right h]
      · by_cases hC : k ∈ integerCoordinateCube N
        · rw [ite_eq_left hC]
          by_contra hne
          exact h (hShiftBand i k hne)
        · rw [ite_eq_right hC])
    exact LinearMap.mem_ker.mp (hc x.property)
  let p := Finsupp.onFinset (integerCoordinateCube_finite (d := d) N).toFinset (⇑y)
    (fun j hj => (integerCoordinateCube_finite (d := d) N).mem_toFinset.mpr
      (by by_contra hc; exact hj (hCut j (Or.inl hc))))
  have hp (j : d → ℤ) : p j = y j := Finsupp.onFinset_apply
  refine ⟨p, ?_, fun j hj => ?_, fun k hk => ?_⟩
  · intro h
    apply hx0
    apply Subtype.ext
    ext j
    have hpj := hp j
    rw [h, Finsupp.zero_apply] at hpj
    exact hpj.symm
  · by_contra h
    exact (Finsupp.mem_support_iff.mp hj) ((hp j).trans (hCut j (Or.inr h)))
  · have hBandY (j : d → ℤ) (hj : y j ≠ 0) : L j ∈ Icc 0 W := by
      by_contra h
      exact hj (hCut j (Or.inr h))
    have hRow := originalBandConvolution_apply_eq_tsum_of_mem_output L u hu W a b y hBandY k hk
    change A y k = _ at hRow
    rw [hA0] at hRow
    unfold annihilatorArrayConvolution
    have hFinite : (∑' j : d → ℤ, p j * u (k - j)) = ∑ j ∈ p.support, p j * u (k - j) :=
      tsum_eq_sum fun j hj => by rw [Finsupp.notMem_support_iff.mp hj, zero_mul]
    calc
      _ = ∑' j : d → ℤ, p j * u (k - j) := hFinite.symm
      _ = ∑' j : d → ℤ, y j * u (k - j) := tsum_congr (fun j => by rw [hp])
      _ = 0 := hRow.symm

end
end MeyerGeneralProblem
