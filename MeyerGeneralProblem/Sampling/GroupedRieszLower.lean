module

public import MeyerGeneralProblem.Sampling.GroupedBiorthogonal
public import MeyerGeneralProblem.Sampling.FiniteWindowDuality

@[expose] public section

/-!
# Actual grouped finite-window duality

Supported Schwartz Fourier interpolation kernels pair exactly with positive
grouped exponentials in the window Hilbert space. Their genuine synthesis
Bessel inequality yields the reciprocal lower inequality for the original
grouped system. Distinct nodes are used only for exact finite Newton algebra,
not an estimate involving their internal gaps.
-/

namespace MeyerGeneralProblem

open MeasureTheory ComplexConjugate
open scoped SchwartzMap

noncomputable section

/-- Finite Hilbert duality is invariant under arbitrary finite reindexing. -/
theorem fintype_lowerBound_of_biorthogonal_bessel
    {ι H : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (v y : ι → H) {B : ℝ} (hB : 0 < B)
    (hbio : ∀ i j, inner ℂ (y i) (v j) = if i = j then 1 else 0)
    (hupper : ∀ c : ι → ℂ, ‖∑ i, c i • y i‖ ^ 2 ≤ B * ∑ i, ‖c i‖ ^ 2)
    (c : ι → ℂ) :
    B⁻¹ * ∑ i, ‖c i‖ ^ 2 ≤ ‖∑ i, c i • v i‖ ^ 2 := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hc := e.sum_comp (fun i => ‖c i‖ ^ 2)
  have hv := e.sum_comp (fun i => c i • v i)
  have h := finite_lowerBound_of_biorthogonal_bessel (fun i => v (e i))
    (fun i => y (e i)) hB (fun i j => by simpa using hbio (e i) (e j))
    (by
      intro d
      have hsum := e.sum_comp (fun i => d (e.symm i) • y i)
      have hsq := e.sum_comp (fun i => ‖d (e.symm i)‖ ^ 2)
      simpa only [← hsum, ← hsq, e.symm_apply_apply] using hupper (fun i => d (e.symm i)))
    (fun i => c (e i))
  simpa only [hc, hv] using h

/-- Restriction of an actual Schwartz function to the window Hilbert space. -/
def schwartzFourierWindowVector (a : ℝ) (v : SchwartzMap ℝ ℂ) : FourierWindowSpace a :=
  continuousFourierWindowVector a v v.continuous

/-- The scalar Fourier pairing keeps the exact negative Fourier convention. -/
theorem inner_fourierWindowVector_schwartz
    (a : ℝ) (v : SchwartzMap ℝ ℂ)
    (hsupp : Function.support v ⊆ Set.Icc (-a) a) (ω : ℝ) :
    inner ℂ (fourierWindowVector a ω) (schwartzFourierWindowVector a v) =
      FourierTransform.fourier (v : ℝ → ℂ) ω := by
  rw [L2.inner_def, fourier_eq_integral_gramPhase]
  calc
    _ = ∫ t : ℝ in Set.Icc (-a) a, gramPhase (-ω) t * v t := by
      apply integral_congr_ae
      filter_upwards [fourierWindowVector_coeFn a ω,
        continuousFourierWindowVector_coeFn a v v.continuous] with t ht hv
      change inner ℂ ((fourierWindowVector a ω : ℝ → ℂ) t)
        ((continuousFourierWindowVector a v v.continuous : ℝ → ℂ) t) = _
      rw [ht, hv]
      simp only [RCLike.inner_apply, gramPhase_neg_left, mul_comm]
    _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun t ht => by
      have hz : v t = 0 := not_not.mp (fun h => ht (hsupp h))
      rw [hz, mul_zero])

/-- Actual analytic initial-prefix Fourier data is exactly the Hilbert pairing
against the genuine positive grouped exponential on the same window. -/
theorem analyticDividedDifference_fourier_schwartz_eq_inner
    {k : ℕ} (a : ℝ) (ω : Fin k → ℝ) (hω : Function.Injective ω)
    (v : SchwartzMap ℝ ℂ) (hsupp : Function.support v ⊆ Set.Icc (-a) a)
    (j : Fin k) :
    analyticDividedDifference (finiteNodeSequence ω) j
      (FourierTransform.fourier (v : ℝ → ℂ)) =
        inner ℂ (groupedFourierWindowVector a ω j) (schwartzFourierWindowVector a v) := by
  rw [analyticDividedDifference_eq_dividedDifferences ω hω,
    dividedDifferences_eq_groupedNewtonWeights, groupedFourierWindowVector_eq_sum a ω hω,
    sum_inner]
  apply Finset.sum_congr rfl
  intro i hi
  rw [inner_smul_left, conj_groupedNewtonWeight_real,
    inner_fourierWindowVector_schwartz a v hsupp]

/-- Compact window support makes the Hilbert energy of a finite Schwartz
synthesis equal to its actual whole-line integral. -/
theorem schwartzFourierWindowVector_sum_norm_sq
    {ι : Type*} [Fintype ι] (a : ℝ) (v : ι → SchwartzMap ℝ ℂ)
    (hsupp : ∀ i, Function.support (v i) ⊆ Set.Icc (-a) a) (c : ι → ℂ) :
    ‖∑ i, c i • schwartzFourierWindowVector a (v i)‖ ^ 2 =
      ∫ t : ℝ, ‖(∑ i, c i • v i : SchwartzMap ℝ ℂ) t‖ ^ 2 := by
  simp only [schwartzFourierWindowVector]
  rw [continuousFourierWindowVector_sum_norm_sq]
  simp only [sum_apply, smul_apply, smul_eq_mul]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro t ht
  have hz (i : ι) : v i t = 0 := not_not.mp (fun h => ht (hsupp i h))
  simp only [hz, mul_zero, Finset.sum_const_zero, norm_zero, zero_pow (by norm_num : 2 ≠ 0)]

/-- Exact target and off-target Newton data combine into a Kronecker family
on the actual dependent coordinate index, without padding empty clusters. -/
theorem grouped_initialData_kronecker
    {N : ℕ} (size : Fin N → ℕ) (nodes : (g : Fin N) → Fin (size g) → ℝ)
    (v : (g : Fin N) → Fin (size g) → ℝ → ℂ)
    (htarget : ∀ g (i j : Fin (size g)),
      analyticDividedDifference (finiteNodeSequence (nodes g)) j
        (FourierTransform.fourier (v g i)) = if i = j then 1 else 0)
    (hoff : ∀ g h, g ≠ h → ∀ (i : Fin (size g)) (j : Fin (size h)),
      analyticDividedDifference (finiteNodeSequence (nodes h)) j
        (FourierTransform.fourier (v g i)) = 0)
    (x y : Σ g, Fin (size g)) :
    analyticDividedDifference (finiteNodeSequence (nodes y.1)) y.2
      (FourierTransform.fourier (v x.1 x.2)) = if x = y then 1 else 0 := by
  classical
  rcases x with ⟨g, i⟩
  rcases y with ⟨h, j⟩
  by_cases hgh : g = h
  · subst h
    simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using htarget g i j
  · have hxy : (⟨g, i⟩ : Σ g, Fin (size g)) ≠ ⟨h, j⟩ :=
      fun h => hgh (congrArg Sigma.fst h)
    simpa only [ite_eq_right hxy] using hoff g h hgh i j

/-- Genuine supported Schwartz grouped interpolation kernels with a proved
Bessel inequality imply the actual grouped exponential lower bound `1/B`.
No cluster-count or inverse-internal-gap factor is introduced by duality. -/
theorem finite_groupedWindow_lowerBound_of_schwartz_bessel
    {N : ℕ} (size : Fin N → ℕ) (nodes : (g : Fin N) → Fin (size g) → ℝ)
    (hnodes : ∀ g, Function.Injective (nodes g)) {a B : ℝ} (hB : 0 < B)
    (v : (g : Fin N) → Fin (size g) → SchwartzMap ℝ ℂ)
    (hsupp : ∀ g i, Function.support (v g i) ⊆ Set.Icc (-a) a)
    (htarget : ∀ g (i j : Fin (size g)),
      analyticDividedDifference (finiteNodeSequence (nodes g)) j
        (FourierTransform.fourier (v g i : ℝ → ℂ)) = if i = j then 1 else 0)
    (hoff : ∀ g h, g ≠ h → ∀ (i : Fin (size g)) (j : Fin (size h)),
      analyticDividedDifference (finiteNodeSequence (nodes h)) j
        (FourierTransform.fourier (v g i : ℝ → ℂ)) = 0)
    (hupper : ∀ c : (g : Fin N) → Fin (size g) → ℂ,
      (∫ t : ℝ, ‖(∑ g, ∑ j, c g j • v g j : SchwartzMap ℝ ℂ) t‖ ^ 2) ≤
        B * ∑ g, ∑ j, ‖c g j‖ ^ 2)
    (c : (g : Fin N) → Fin (size g) → ℂ) :
    B⁻¹ * (∑ g, ∑ j, ‖c g j‖ ^ 2) ≤
      ∫ t : ℝ in Set.Icc (-a) a,
        ‖∑ g, ∑ j, c g j * groupedExponentialInitial (nodes g) j t‖ ^ 2 := by
  classical
  let V (x : Σ g, Fin (size g)) : FourierWindowSpace a :=
    groupedFourierWindowVector a (nodes x.1) x.2
  let Y (x : Σ g, Fin (size g)) : FourierWindowSpace a :=
    schwartzFourierWindowVector a (v x.1 x.2)
  have hbio (x y : Σ g, Fin (size g)) : inner ℂ (Y x) (V y) =
      if x = y then 1 else 0 := by
    rw [← inner_conj_symm]
    change conj (inner ℂ (groupedFourierWindowVector a (nodes y.1) y.2)
      (schwartzFourierWindowVector a (v x.1 x.2))) = _
    rw [← analyticDividedDifference_fourier_schwartz_eq_inner a _ (hnodes y.1) _ (hsupp x.1 x.2),
      grouped_initialData_kronecker size nodes (fun g i => (v g i : ℝ → ℂ)) htarget hoff]
    split_ifs <;> simp
  have hupper' (d : (Σ g, Fin (size g)) → ℂ) :
      ‖∑ x, d x • Y x‖ ^ 2 ≤ B * ∑ x, ‖d x‖ ^ 2 := by
    change ‖∑ x, d x • schwartzFourierWindowVector a (v x.1 x.2)‖ ^ 2 ≤ _
    rw [schwartzFourierWindowVector_sum_norm_sq a (fun x : Σ g, Fin (size g) => v x.1 x.2)
      (fun x => hsupp x.1 x.2)]
    simpa only [Fintype.sum_sigma] using hupper (fun g j => d ⟨g, j⟩)
  have h := fintype_lowerBound_of_biorthogonal_bessel V Y hB hbio hupper'
    (fun x => c x.1 x.2)
  have he := continuousFourierWindowVector_sum_norm_sq a
    (fun x : Σ g, Fin (size g) => groupedExponentialInitial (nodes x.1) x.2)
    (fun x => continuous_groupedExponentialInitial _ _) (fun x => c x.1 x.2)
  change ‖∑ x, c x.1 x.2 • V x‖ ^ 2 = _ at he
  rw [he] at h
  simpa only [Fintype.sum_sigma] using h

end

end MeyerGeneralProblem
