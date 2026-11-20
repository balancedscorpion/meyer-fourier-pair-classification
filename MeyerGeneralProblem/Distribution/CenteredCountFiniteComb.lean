module

public import MeyerGeneralProblem.Distribution.FiniteLatticeSpectrumComb
public import MeyerGeneralProblem.Distribution.ReflectionSupportRecovery

@[expose] public section

/-!
# Finite combs from asymmetric centered counts

The Fourier transform of each original modulated comb is computed with its
phase and reciprocal spacing. Applying the finite-lattice-spectrum theorem
in the exchanged orientation then recovers both original records.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter Set
open scoped BigOperators FourierTransform SchwartzMap

/-- The distribution is a finite sum of actual modulated Dirac combs. -/
def IsFiniteModulatedDiracCombSum (T : TemperedDistribution ℝ ℂ) : Prop :=
  ∃ (ι : Type) (inst : Fintype ι), letI := inst
    ∃ (q : ι → AffineCombTerm) (w : ι → ℝ) (hw : ∀ i, 0 < w i),
      T = ∑ i, (q i).distribution (w i) (hw i)

theorem IsFiniteSpectralClassCombSum.isFiniteModulatedDiracCombSum
    {classes : List (ℝ × List ℝ)} {T : TemperedDistribution ℝ ℂ}
    (h : IsFiniteSpectralClassCombSum classes T) : IsFiniteModulatedDiracCombSum T := by
  obtain ⟨ι, inst, q, w, hw, heq, _⟩ := h
  exact ⟨ι, inst, q, w, hw, heq⟩

private theorem dualCombCharacter (w y s : ℝ) (n : ℤ) :
    fourier n ((-(y / w) : ℝ) : UnitAddCircle) =
      combModulationCharacter y s *
        combModulationCharacter (-y) (s + (n : ℝ) * w⁻¹) := by
  rw [fourier_coe_apply, combModulationCharacter_eq_exp, combModulationCharacter_eq_exp,
    ← Complex.exp_add]
  congr 1
  push_cast
  simp only [div_eq_mul_inv]
  ring

/-- The exact Fourier image of a term, including its scalar phase. -/
def AffineCombTerm.fourierTerm (q : AffineCombTerm) (w : ℝ) : AffineCombTerm :=
  ⟨-q.origin, q.frequency,
    q.coefficient * ((w⁻¹ : ℝ) : ℂ) * combModulationCharacter q.origin q.frequency⟩

theorem fourier_affineCombTerm (q : AffineCombTerm) (w : ℝ) (hw : 0 < w) :
    𝓕 (q.distribution w hw) = (q.fourierTerm w).distribution w⁻¹ (inv_pos.mpr hw) := by
  ext f
  have hright : (q.fourierTerm w).distribution w⁻¹ (inv_pos.mpr hw) f =
      (q.coefficient * ((w⁻¹ : ℝ) : ℂ) * combModulationCharacter q.origin q.frequency) *
        ∑' n : ℤ, combModulationCharacter (-q.origin) (q.frequency + (n : ℝ) * w⁻¹) *
          f (q.frequency + (n : ℝ) * w⁻¹) := by
    simp only [AffineCombTerm.distribution, smul_apply, modulatedAffineDiracComb_apply,
      AffineCombTerm.fourierTerm, smul_eq_mul]
  rw [hright]
  simp only [AffineCombTerm.distribution, FourierTransform.fourier_smul,
    modulatedAffineDiracComb, fourier_combDistributionModulation, affineDiracComb,
    fourier_combDistributionDilation, fourier_shiftedIntegerComb, map_smul, smul_apply,
    combDistributionTranslation_apply, combDistributionDilation_apply, modulatedIntegerComb_apply,
    combSchwartzDilation_apply, combSchwartzTranslation_apply, abs_of_pos hw, smul_eq_mul]
  rw [← mul_assoc]
  simp only [← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [dualCombCharacter w q.origin q.frequency n, mul_comm w⁻¹ (n : ℝ)]
  simp only [mul_assoc]

theorem IsFiniteModulatedDiracCombSum.fourier {T : TemperedDistribution ℝ ℂ}
    (h : IsFiniteModulatedDiracCombSum T) : IsFiniteModulatedDiracCombSum (𝓕 T) := by
  obtain ⟨ι, inst, q, w, hw, heq⟩ := h
  let _ := inst
  refine ⟨ι, inst, fun i => (q i).fourierTerm (w i), fun i => (w i)⁻¹,
    fun i => inv_pos.mpr (hw i), ?_⟩
  rw [heq, ← temperedFourierLinearMap_apply, map_sum]
  simp only [temperedFourierLinearMap_apply, fourier_affineCombTerm]

theorem IsFiniteModulatedDiracCombSum.of_fourier {T : TemperedDistribution ℝ ℂ}
    (h : IsFiniteModulatedDiracCombSum (𝓕 T)) : IsFiniteModulatedDiracCombSum T := by
  have h' := h.fourier.fourier.fourier
  rw [fourier_fourier_eq_originalDistributionReflection (𝓕 (𝓕 T)),
    fourier_fourier_eq_originalDistributionReflection T,
    originalDistributionReflection_involutive] at h'
  exact h'

/-- Bounded unit cells and vanishing opposite quadratic lower count give
finite modulated combs for every admitted pair on the two carriers. -/
theorem finiteModulatedDiracCombSum_pair_of_unitCellBound
    (A B : LocallyFiniteCarrier) (K : ℕ) (hK : UnitCellBound A K)
    (T : TemperedDistribution ℝ ℂ) (hT : AtomicOnCarrier A T)
    (hFT : AtomicOnCarrier B (𝓕 T))
    (hcount : ∀ c : ℝ, 0 < c → ∃ᶠ R : ℝ in atTop,
      ((B.carrier ∩ Icc (-R) R).ncard : ℝ) < c * R ^ 2) :
    IsFiniteModulatedDiracCombSum T ∧ IsFiniteModulatedDiracCombSum (𝓕 T) := by
  classical
  obtain ⟨E, hE, A₀, hA₀, heq⟩ :=
    exists_originalPairSpace_lattice_intersection_of_unitCellBound A B K hK hcount
  have hpair := (mem_distributionalMeyerPairSpace_iff A B T).mpr ⟨hT, hFT⟩
  rw [heq] at hpair
  have hT₀ := ((mem_distributionalMeyerPairSpace_iff A₀ B T).mp hpair).1
  have hFFT : AtomicOnCarrier A₀.reflect (𝓕 (𝓕 T)) := by
    rw [fourier_fourier_eq_originalDistributionReflection]
    exact atomicOnCarrier_originalDistributionReflection A₀ T hT₀
  let reflect (p : ℝ × ℝ) := (-p.1, p.2)
  let F := E.toFinset.image reflect
  have hpos : ∀ p ∈ F, 0 < p.2 := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    exact hE q (List.mem_toFinset.mp hq)
  have hsub : A₀.reflect.carrier ⊆ (affineLatticeUnionCarrier F).carrier := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hA₀] at hx
    obtain ⟨p, hp, k, hk⟩ := hx.2
    refine (mem_affineLatticeUnionCarrier F (-x)).mpr
      ⟨reflect p, Finset.mem_image.mpr ⟨p, List.mem_toFinset.mpr hp, rfl⟩, -k, ?_⟩
    simp [reflect, hk, add_comm]
  obtain ⟨classes, h⟩ := exists_finite_spectralClassCombSum_of_finite_lattice_spectral_cover
    B A₀.reflect (𝓕 T) hFT hFFT F hpos hsub hcount
  exact ⟨h.isFiniteModulatedDiracCombSum.of_fourier, h.isFiniteModulatedDiracCombSum⟩

/-- An actual finite exponential annihilator and vanishing opposite
quadratic lower count give finite combs on the original records. -/
theorem finiteModulatedDiracCombSum_pair_of_annihilator
    (A B : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier A T) (hFT : AtomicOnCarrier B (𝓕 T))
    (hactual : ∀ x : A.subtype, T (A.isolationSchwartz x) ≠ 0)
    {ι : Type*} [Fintype ι] (a : ι → ℝ) (c : ι → ℂ) (ha : Function.Injective a)
    (hval : ∃ x : ℝ, ∑ i, c i * combModulationCharacter (a i) x ≠ 0)
    (hzero : finiteExponentialMultiplication a c T = 0)
    (hcount : ∀ e : ℝ, 0 < e → ∃ᶠ R : ℝ in atTop,
      ((B.carrier ∩ Icc (-R) R).ncard : ℝ) < e * R ^ 2) :
    IsFiniteModulatedDiracCombSum T ∧ IsFiniteModulatedDiracCombSum (𝓕 T) := by
  obtain ⟨K, hK⟩ :=
    exists_unitCellBound_of_finiteExponentialAnnihilator A T hT hactual a c ha hval hzero
  exact finiteModulatedDiracCombSum_pair_of_unitCellBound A B K hK T hT hFT hcount

/-- One centered upper linear count and vanishing opposite quadratic lower
count force both original records to be finite modulated comb sums. -/
theorem finiteModulatedDiracCombSum_pair_of_centered_count
    (A B : LocallyFiniteCarrier)
    (hb : (atTop : Filter ℝ).IsBoundedUnder (· ≤ ·)
      (fun t => ((A.carrier ∩ Icc (-t) t).ncard : ℝ) / (2 * t)))
    (T : TemperedDistribution ℝ ℂ) (hT : AtomicOnCarrier A T)
    (hFT : AtomicOnCarrier B (𝓕 T))
    (hactual : ∀ x : A.subtype, T (A.isolationSchwartz x) ≠ 0)
    (hcount : ∀ c : ℝ, 0 < c → ∃ᶠ R : ℝ in atTop,
      ((B.carrier ∩ Icc (-R) R).ncard : ℝ) < c * R ^ 2) :
    IsFiniteModulatedDiracCombSum T ∧ IsFiniteModulatedDiracCombSum (𝓕 T) := by
  obtain ⟨K, hK⟩ := exists_unitCellBound_of_centered_count_of_atomic_pair
    A B hb T hT hFT hactual
  exact finiteModulatedDiracCombSum_pair_of_unitCellBound A B K hK T hT hFT hcount

/-- Reflecting the carrier preserves its centered closed-window count. -/
theorem centeredCount_reflect (A : LocallyFiniteCarrier) (R : ℝ) :
    (A.reflect.carrier ∩ Icc (-R) R).ncard = (A.carrier ∩ Icc (-R) R).ncard := by
  change (((fun x : ℝ => -x) '' A.carrier) ∩ Icc (-R) R).ncard = _
  have hset : ((fun x : ℝ => -x) '' A.carrier) ∩ Icc (-R) R =
      (fun x : ℝ => -x) '' (A.carrier ∩ Icc (-R) R) := by
    ext y
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hl, hr⟩
      exact ⟨x, ⟨hx, by linarith, by linarith⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hl, hr⟩, rfl⟩
      exact ⟨⟨x, hx, rfl⟩, by linarith, by linarith⟩
  rw [hset, ncard_image_of_injective _ neg_injective]

/-- The same count criterion in the opposite Fourier orientation. -/
theorem finiteModulatedDiracCombSum_pair_of_centered_count_fourier
    (A B : LocallyFiniteCarrier)
    (hb : (atTop : Filter ℝ).IsBoundedUnder (· ≤ ·)
      (fun t => ((B.carrier ∩ Icc (-t) t).ncard : ℝ) / (2 * t)))
    (T : TemperedDistribution ℝ ℂ) (hT : AtomicOnCarrier A T)
    (hFT : AtomicOnCarrier B (𝓕 T))
    (hactual : ∀ x : B.subtype, (𝓕 T) (B.isolationSchwartz x) ≠ 0)
    (hcount : ∀ c : ℝ, 0 < c → ∃ᶠ R : ℝ in atTop,
      ((A.carrier ∩ Icc (-R) R).ncard : ℝ) < c * R ^ 2) :
    IsFiniteModulatedDiracCombSum T ∧ IsFiniteModulatedDiracCombSum (𝓕 T) := by
  have hFFT : AtomicOnCarrier A.reflect (𝓕 (𝓕 T)) := by
    rw [fourier_fourier_eq_originalDistributionReflection]
    exact atomicOnCarrier_originalDistributionReflection A T hT
  have h := finiteModulatedDiracCombSum_pair_of_centered_count B A.reflect hb (𝓕 T)
    hFT hFFT hactual (by simpa only [centeredCount_reflect] using hcount)
  exact ⟨h.1.of_fourier, h.1⟩

end
end MeyerGeneralProblem
