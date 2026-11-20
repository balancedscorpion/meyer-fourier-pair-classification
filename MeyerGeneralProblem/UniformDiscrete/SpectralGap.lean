module

public import MeyerGeneralProblem.Sampling.BeurlingSmoothing
public import MeyerGeneralProblem.Sampling.BeurlingWindow
public import MeyerGeneralProblem.UniformDiscrete.SpectralWindow
public import MeyerGeneralProblem.Cardinal.AtomicCoefficientBound

@[expose] public section

/-!
Bounded global Fourier-window extension, following the existing finite-span
Hahn–Banach proof. All-index interpolation is constructed here; it is not an
input record. The fixed-bump growth component remains separately retained.
-/
namespace MeyerGeneralProblem
open MeasureTheory ComplexConjugate
open scoped SchwartzMap ContDiff
noncomputable section

theorem exists_global_biorthogonal_of_lowerBound
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ι : Type*} [DecidableEq ι] (v : ι → H) {A : ℝ} (hA : 0 < A)
    (hlower : ∀ c : ι →₀ ℂ,
      A * (c.sum fun _ z => ‖z‖ ^ 2) ≤ ‖Finsupp.linearCombination ℂ v c‖ ^ 2) :
    ∃ y : ι → H, (∀ i j, inner ℂ (y i) (v j) = if i = j then 1 else 0) ∧
      ∀ i, ‖y i‖ ≤ (Real.sqrt A)⁻¹ := by
  classical
  let S : (ι →₀ ℂ) →ₗ[ℂ] H := Finsupp.linearCombination ℂ v
  have hsqrt : 0 < Real.sqrt A := Real.sqrt_pos.2 hA
  have hcoordinate (c : ι →₀ ℂ) (k : ι) :
      ‖c k‖ ≤ (Real.sqrt A)⁻¹ * ‖S c‖ := by
    have hsum : ‖c k‖ ^ 2 ≤ c.sum (fun _ z => ‖z‖ ^ 2) := by
      by_cases hk : k ∈ c.support
      · exact Finset.single_le_sum (fun i hi => sq_nonneg ‖c i‖) hk
      · rw [Finsupp.notMem_support_iff.mp hk]
        simpa [Finsupp.sum] using Finset.sum_nonneg (s := c.support) (fun i _ => sq_nonneg ‖c i‖)
    have hsq : (Real.sqrt A * ‖c k‖) ^ 2 ≤ ‖S c‖ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hA.le]
      exact (mul_le_mul_of_nonneg_left hsum hA.le).trans (hlower c)
    have h := (sq_le_sq₀ (by positivity) (norm_nonneg (S c))).1 hsq
    calc
      ‖c k‖ ≤ ‖S c‖ / Real.sqrt A :=
        (le_div_iff₀ hsqrt).2 (by simpa only [mul_comm] using h)
      _ = (Real.sqrt A)⁻¹ * ‖S c‖ := by ring
  have hinj : Function.Injective S := by
    intro c e hce
    have hzero : S (c - e) = 0 := by rw [map_sub, hce, sub_self]
    ext i
    have hi := hcoordinate (c - e) i
    rw [hzero, norm_zero, mul_zero] at hi
    exact sub_eq_zero.1 (norm_eq_zero.1 (le_antisymm hi (norm_nonneg _)))
  let R : (ι →₀ ℂ) ≃ₗ[ℂ] S.range := LinearEquiv.ofInjective S hinj
  have hex (i : ι) : ∃ y : H,
      (∀ j, inner ℂ y (v j) = if i = j then 1 else 0) ∧
        ‖y‖ ≤ (Real.sqrt A)⁻¹ := by
    let coord : S.range →ₗ[ℂ] ℂ := (Finsupp.lapply i).comp R.symm.toLinearMap
    have hc (z : S.range) : ‖coord z‖ ≤ (Real.sqrt A)⁻¹ * ‖z‖ := by
      have h := hcoordinate (R.symm z) i
      have hz : S (R.symm z) = (z : H) := congrArg Subtype.val (R.apply_symm_apply z)
      simpa only [coord, LinearMap.comp_apply, Finsupp.lapply_apply,
        LinearEquiv.coe_coe, hz, Submodule.norm_coe] using h
    let fc : S.range →L[ℂ] ℂ := coord.mkContinuous (Real.sqrt A)⁻¹ hc
    obtain ⟨g, hg, hgnorm⟩ := exists_extension_norm_eq S.range fc
    refine ⟨(InnerProductSpace.toDual ℂ H).symm g, fun j => ?_, ?_⟩
    · rw [InnerProductSpace.toDual_symm_apply]
      have hSj : S (Finsupp.single j 1) = v j := by simp [S]
      have hj := hg (R (Finsupp.single j 1))
      change g (S (Finsupp.single j 1)) = coord (R (Finsupp.single j 1)) at hj
      rw [hSj] at hj
      rw [hj]
      simp [coord, Finsupp.single_apply, eq_comm]
    · rw [(InnerProductSpace.toDual ℂ H).symm.norm_map, hgnorm]
      exact fc.opNorm_le_bound (inv_nonneg.2 hsqrt.le) hc
  choose y hy hnorm using hex
  exact ⟨y, hy, hnorm⟩


/-- The actual window lower bound controls every finitely supported vector,
with the same constant and no restriction on the ambient index type. -/
theorem HasFourierWindowLowerBound.finsupp_window_lowerBound
    {ι : Type*} {s : ι → ℝ} {a A : ℝ}
    (h : HasFourierWindowLowerBound s a A) (c : ι →₀ ℂ) :
    A * (c.sum fun _ z => ‖z‖ ^ 2) ≤
      ‖Finsupp.linearCombination ℂ (fun i => fourierWindowVector a (s i)) c‖ ^ 2 := by
  classical
  let σ := {i : ι // i ∈ c.support}
  let f : σ ≃ Fin (Fintype.card σ) := Fintype.equivFin σ
  have hfin := h _ (fun j => (f.symm j).val)
    (Subtype.val_injective.comp f.symm.injective) (fun j => c (f.symm j))
  rw [← fourierWindowVector_sum_norm_sq] at hfin
  have henergy : (∑ i : Fin (Fintype.card σ), ‖c (f.symm i)‖ ^ 2) =
      c.sum (fun _ z => ‖z‖ ^ 2) := by
    rw [f.symm.sum_comp (fun i : σ => ‖c i‖ ^ 2)]
    exact (Finset.sum_subtype c.support (fun _ => Iff.rfl) (fun i => ‖c i‖ ^ 2)).symm
  have hsynthesis : (∑ i : Fin (Fintype.card σ),
      c (f.symm i) • fourierWindowVector a (s (f.symm i))) =
      Finsupp.linearCombination ℂ (fun i => fourierWindowVector a (s i)) c := by
    rw [f.symm.sum_comp (fun i : σ => c i • fourierWindowVector a (s i))]
    exact (Finset.sum_subtype c.support (fun _ => Iff.rfl)
      (fun i => c i • fourierWindowVector a (s i))).symm
  simpa only [Function.comp_def, henergy, hsynthesis] using hfin

/-- Genuine global compact-frequency interpolation from positive separation.
The Kronecker values hold at every index simultaneously. -/
theorem exists_global_supported_fourier_interpolation
    {ι : Type*} [DecidableEq ι] (s : ι → ℝ) {a d : ℝ} (ha : 0 < a) (had : 1 < 2 * a * d)
    (hsep : ∀ i j, i ≠ j → d ≤ |s i - s j|) :
    ∃ ρ : ι → ℝ → ℂ,
      (∀ i, Integrable (ρ i)) ∧
      (∀ i, Function.support (ρ i) ⊆ Set.Icc (-a) a) ∧
      (∀ i j, FourierTransform.fourier (ρ i) (s j) = if i = j then 1 else 0) := by
  classical
  have hwindow := hasFourierWindowLowerBound_of_cosineIngham s ha had hsep
  obtain ⟨y, hy, _⟩ := exists_global_biorthogonal_of_lowerBound
    (fun i => fourierWindowVector a (s i))
    (cosineInghamFloorFactor_pos ha had) hwindow.finsupp_window_lowerBound
  refine ⟨fun i => fourierWindowKernel a (y i),
    fun i => integrable_fourierWindowKernel a (y i),
    fun i => support_fourierWindowKernel_subset a (y i), ?_⟩
  intro i j
  rw [fourier_fourierWindowKernel, ← inner_conj_symm, hy]
  split_ifs <;> simp

/-- Smoothing the global kernels preserves all their carrier values while
producing actual compactly supported Schwartz tests. No limit of finite
interpolants or unproved Schwartz convergence is used. -/
theorem exists_global_schwartz_fourier_interpolation
    {ι : Type*} [DecidableEq ι] (s : ι → ℝ) {a d r : ℝ}
    (ha : 0 < a) (had : 1 < 2 * a * d) (hr : 0 < r)
    (hsep : ∀ i j, i ≠ j → d ≤ |s i - s j|) :
    ∃ v : ι → SchwartzMap ℝ ℂ,
      (∀ i, Function.support (v i) ⊆ Set.Icc (-(a + r)) (a + r)) ∧
      (∀ i j, FourierTransform.fourier (v i : ℝ → ℂ) (s j) =
        if i = j then 1 else 0) := by
  classical
  obtain ⟨ρ, hρint, hρs, hρfourier⟩ :=
    exists_global_supported_fourier_interpolation s ha had hsep
  obtain ⟨G, hGs, hGzero, _⟩ := exists_compact_positive_fourier_smoothing hr
  choose g hg hgs using fun i => exists_schwartz_modulation G hGs (s i)
  have hgf (i : ι) (w : ℝ) :
      FourierTransform.fourier (g i : ℝ → ℂ) w =
        FourierTransform.fourier (G : ℝ → ℂ) (w - s i) := by
    have heq : (g i : ℝ → ℂ) = fun t => G t * gramPhase (s i) t := funext (hg i)
    rw [heq, fourier_mul_gramPhase]
  choose v hv hvs using fun i => exists_schwartz_fourierKernelConvolution
    (hρint i) (hρs i) (hgs i) ((g i).smooth (⊤ : ℕ∞))
  refine ⟨v, hvs, ?_⟩
  intro i j
  rw [hv i, fourier_fourierKernelConvolution (hρint i) (g i).integrable, hρfourier]
  by_cases hij : i = j
  · subst j
    simp only [ite_true, one_mul, hgf, sub_self, hGzero]
  · simp only [hij, ite_false, zero_mul]

namespace UniformDiscrete

/-- Positive physical separation supplies the actual distributional gap
input at a window fixed before the tempered distribution is chosen. -/
theorem spectralGapUniqueness_of_positive_separation
    (S : LocallyFiniteCarrier) (d : ℝ) (hd : 0 < d)
    (hsep : ∀ x ∈ S.carrier, ∀ y ∈ S.carrier, x ≠ y → d ≤ |x - y|) :
    SpectralGapUniqueness S (d⁻¹ + 2) := by
  classical
  have ha : 0 < d⁻¹ := inv_pos.mpr hd
  have had : 1 < 2 * d⁻¹ * d := by rw [mul_assoc, inv_mul_cancel₀ hd.ne']; norm_num
  obtain ⟨v, hvs, hvf⟩ := exists_global_schwartz_fourier_interpolation
    (fun x : S.subtype => (x : ℝ)) ha had (by norm_num : (0 : ℝ) < 1)
    (fun x y hxy => hsep x x.property y y.property (Subtype.val_injective.ne hxy))
  intro T hT hgap
  have hTa := hasLocallyAtomicAction_atomicOnCarrier S T hT
  apply atomicOnCarrier_eq_zero_of_isolationAction_eq_zero S T hTa
  intro x
  have hcompact : HasCompactSupport (v x) :=
    HasCompactSupport.intro isCompact_Icc (fun y hy => not_not.mp (fun h => hy (hvs x h)))
  have hts : tsupport (v x) ⊆ Set.Icc (-(d⁻¹ + 1)) (d⁻¹ + 1) :=
    closure_minimal (hvs x) isClosed_Icc
  have hinside : tsupport (v x) ⊆ Set.Ioo (-(d⁻¹ + 2)) (d⁻¹ + 2) := by
    intro y hy
    obtain ⟨hlo, hhi⟩ := hts hy
    constructor <;> linarith
  have hvan := hgap (v x) hcompact hinside
  rw [TemperedDistribution.fourier_apply] at hvan
  have heq : T (S.isolationSchwartz x) = T (FourierTransform.fourier (v x)) := by
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply hTa
    intro y hy
    let j : S.subtype := ⟨y, hy⟩
    have hf := hvf x j
    change (FourierTransform.fourier (v x)) y = _ at hf
    simp only [sub_apply]
    rw [hf]
    by_cases hj : x = j
    · subst x
      simp only [ite_true]
      change S.isolationSchwartz j (j : ℝ) - 1 = 0
      rw [S.isolationSchwartz_self, sub_self]
    · have hyx : y ≠ (x : ℝ) := by
        intro he
        exact hj (Subtype.ext he.symm)
      simp only [hj, ite_false, S.isolationSchwartz_of_mem_of_ne x hy hyx, sub_self]
  exact heq.trans hvan

/-- The whole actual Meyer space has a finite injective Fourier coordinate
window from physical separation alone, with no supplied gap theorem. -/
theorem spectralWindowMap_injective_of_positive_separation
    (S : LocallyFiniteCarrier) (d : ℝ) (hd : 0 < d)
    (hsep : ∀ x ∈ S.carrier, ∀ y ∈ S.carrier, x ≠ y → d ≤ |x - y|) :
    Function.Injective (spectralWindowMap S (d⁻¹ + 2)) :=
  spectralWindowMap_injective_of_gap S _
    (spectralGapUniqueness_of_positive_separation S d hd hsep)

/-- Finite dimension applies to the whole distributional space at once,
without a fixed Hermite-order or coefficient-growth bound. -/
theorem finiteDimensional_of_positive_separation
    (S : LocallyFiniteCarrier) (d : ℝ) (hd : 0 < d)
    (hsep : ∀ x ∈ S.carrier, ∀ y ∈ S.carrier, x ≠ y → d ≤ |x - y|) :
    FiniteDimensional ℂ (DistributionalMeyerSpace S) :=
  finiteDimensional_of_gap S _
    (spectralGapUniqueness_of_positive_separation S d hd hsep)

/-- A concrete finite rank bound counts only the actual carrier's window
points, with no prescribed ambient lattice. -/
theorem finrank_le_spectralWindow_card_of_positive_separation
    (S : LocallyFiniteCarrier) (d : ℝ) (hd : 0 < d)
    (hsep : ∀ x ∈ S.carrier, ∀ y ∈ S.carrier, x ≠ y → d ≤ |x - y|) :
    Module.finrank ℂ (DistributionalMeyerSpace S) ≤
      Fintype.card (spectralWindow S (d⁻¹ + 2)) :=
  finrank_le_spectralWindow_card_of_gap S _
    (spectralGapUniqueness_of_positive_separation S d hd hsep)

end UniformDiscrete

#print axioms exists_global_biorthogonal_of_lowerBound
#print axioms HasFourierWindowLowerBound.finsupp_window_lowerBound
#print axioms exists_global_supported_fourier_interpolation
#print axioms exists_global_schwartz_fourier_interpolation
#print axioms UniformDiscrete.spectralGapUniqueness_of_positive_separation
#print axioms UniformDiscrete.spectralWindowMap_injective_of_positive_separation
#print axioms UniformDiscrete.finiteDimensional_of_positive_separation
#print axioms UniformDiscrete.finrank_le_spectralWindow_card_of_positive_separation

end
end MeyerGeneralProblem
