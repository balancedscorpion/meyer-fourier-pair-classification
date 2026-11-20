module

public import MeyerGeneralProblem.Distribution.QuasiperiodicAtomicComb

@[expose] public section

/-!
# A finite set of translation phases at one period

The kernel of a product of distinct translation factors on physical
value-only records is a finite sum of combs in the prescribed phases.
The proof solves each known phase by division by the difference of
eigenvalues. Only the physical record needs to be value-only.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set
open scoped SchwartzMap FourierTransform

/-- One summand in the finite affine comb expansion. -/
structure AffineCombTerm where
  /-- The frequency of the modulating character. -/
  frequency : ℝ
  /-- The translate of the physical lattice. -/
  origin : ℝ
  /-- The scalar amplitude multiplying the modulated comb. -/
  coefficient : ℂ

/-- The original tempered distribution defined by one comb summand. -/
abbrev AffineCombTerm.distribution (q : AffineCombTerm) (w : ℝ) (hw : 0 < w) :
    TemperedDistribution ℝ ℂ :=
  q.coefficient • modulatedAffineDiracComb w hw q.origin q.frequency

/-- The distributional sum of the given modulated comb terms. -/
def affineCombTermSum (w : ℝ) (hw : 0 < w) (terms : List AffineCombTerm) :
    TemperedDistribution ℝ ℂ :=
  (terms.map fun q => q.distribution w hw).sum

/-- A finite union of the full physical lattices of the summands. -/
def affineCombTermSumCarrier (w : ℝ) (hw : 0 < w) : List AffineCombTerm → LocallyFiniteCarrier
  | [] => ⟨∅, by simp⟩
  | q :: qs => (affineDiracCombCarrier w hw q.origin).union (affineCombTermSumCarrier w hw qs)

theorem atomicOnCarrier_affineCombTermSum (w : ℝ) (hw : 0 < w)
    (terms : List AffineCombTerm) :
    AtomicOnCarrier (affineCombTermSumCarrier w hw terms) (affineCombTermSum w hw terms) := by
  induction terms with
  | nil => intro f _; simp [affineCombTermSum]
  | cons q qs ih =>
      intro f hf
      rw [affineCombTermSum, List.map_cons, List.sum_cons]
      simp only [add_apply, AffineCombTerm.distribution, smul_apply]
      have hq := atomicOnCarrier_combDistributionModulation _ _
        (affineDiracComb_atomicOnCarrier w hw q.origin) q.frequency
      change q.coefficient • combDistributionModulation q.frequency (affineDiracComb w hw q.origin) f +
        affineCombTermSum w hw qs f = 0
      rw [hq f (fun x hx => hf x (Or.inl hx)), ih f (fun x hx => hf x (Or.inr hx))]
      simp

/-- The physical pushforward minus the eigenvalue belonging to a spectral
coset of reciprocal spacing. -/
def combTranslationFactor (w s : ℝ) : Module.End ℂ (TemperedDistribution ℝ ℂ) :=
  (combDistributionTranslation w).toLinearMap -
    combModulationCharacter (-w) s • LinearMap.id

theorem combTranslationFactor_apply (w s : ℝ) (T : TemperedDistribution ℝ ℂ) :
    combTranslationFactor w s T =
      combDistributionTranslation w T - combModulationCharacter (-w) s • T := rfl

/-- Finite translation factors acting in list order. -/
def combTranslationFactors (w : ℝ) :
    List ℝ → Module.End ℂ (TemperedDistribution ℝ ℂ)
  | [] => LinearMap.id
  | s :: modes => (combTranslationFactors w modes).comp (combTranslationFactor w s)

theorem atomicOnCarrier_combTranslationFactor (A : LocallyFiniteCarrier)
    (T : TemperedDistribution ℝ ℂ) (hT : AtomicOnCarrier A T) (w s : ℝ) :
    AtomicOnCarrier ((A.translate w).union A) (combTranslationFactor w s T) := by
  intro f hf
  rw [combTranslationFactor_apply]
  simp only [sub_apply, smul_apply]
  rw [atomicOnCarrier_combDistributionTranslation A T hT w f (fun x hx => hf x (Or.inl hx)),
    hT f (fun x hx => hf x (Or.inr hx))]
  simp

private theorem combTranslationFactor_combTerm (w : ℝ) (hw : 0 < w)
    (s : ℝ) (q : AffineCombTerm) :
    combTranslationFactor w s (q.distribution w hw) =
      (⟨q.frequency, q.origin, (combModulationCharacter (-w) q.frequency -
        combModulationCharacter (-w) s) * q.coefficient⟩ : AffineCombTerm).distribution w hw := by
  have hq := combDistributionTranslation_eigen_of_spectral_coset _
    (modulatedAffineDiracComb w hw q.origin q.frequency)
    (fourier_modulatedAffineDiracComb_atomicOnCarrier w hw q.origin q.frequency)
    w hw q.frequency subset_rfl
  change combTranslationFactor w s (q.coefficient •
    modulatedAffineDiracComb w hw q.origin q.frequency) =
      ((combModulationCharacter (-w) q.frequency - combModulationCharacter (-w) s) *
        q.coefficient) • modulatedAffineDiracComb w hw q.origin q.frequency
  have hsub := sub_smul (combModulationCharacter (-w) q.frequency)
    (combModulationCharacter (-w) s) (modulatedAffineDiracComb w hw q.origin q.frequency)
  rw [map_smul, combTranslationFactor_apply, hq, ← hsub, smul_smul, mul_comm q.coefficient]

/-- Exact kernel of a finite product of distinct translation factors. The
characters in the conclusion correspond to the prescribed spectral cosets. -/
theorem exists_affineCombTermSum_of_combTranslationFactors_eq_zero (w : ℝ) (hw : 0 < w)
    (modes : List ℝ)
    (hdistinct : modes.Pairwise
      (fun s t => combModulationCharacter (-w) s ≠ combModulationCharacter (-w) t))
    (A : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ) (hT : AtomicOnCarrier A T)
    (hzero : combTranslationFactors w modes T = 0) :
    ∃ terms : List AffineCombTerm, T = affineCombTermSum w hw terms ∧
      ∀ q ∈ terms, q.frequency ∈ modes := by
  classical
  induction modes generalizing A T with
  | nil =>
      exact ⟨[], by simpa [combTranslationFactors, affineCombTermSum] using hzero,
        by simp⟩
  | cons s modes ih =>
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hdistinct
      let D := combTranslationFactor w s
      obtain ⟨terms, hterms, hmodes⟩ := ih htail _ _ (atomicOnCarrier_combTranslationFactor A T hT w s)
        (by simpa only [combTranslationFactors, LinearMap.comp_apply] using hzero)
      let lift (q : AffineCombTerm) : AffineCombTerm := {q with coefficient :=
        q.coefficient / (combModulationCharacter (-w) q.frequency - combModulationCharacter (-w) s)}
      let Q := affineCombTermSum w hw (terms.map lift)
      have hDQ : D Q = D T := by
        rw [hterms]
        simp only [Q, affineCombTermSum, List.map_map, map_list_sum]
        congr 1
        apply List.map_congr_left
        intro q hq
        have hne := sub_ne_zero.mpr (hhead _ (hmodes q hq)).symm
        change combTranslationFactor w s ((lift q).distribution w hw) = q.distribution w hw
        rw [combTranslationFactor_combTerm]
        simp only [lift, AffineCombTerm.distribution]
        congr 1
        field_simp
      let C := A.union (affineCombTermSumCarrier w hw (terms.map lift))
      have hC : AtomicOnCarrier C (T - Q) := by
        intro f hf
        simp only [sub_apply]
        rw [hT f (fun x hx => hf x (Or.inl hx)),
          atomicOnCarrier_affineCombTermSum w hw (terms.map lift) f (fun x hx => hf x (Or.inr hx)),
          sub_self]
      have hkernel : D (T - Q) = 0 := by rw [map_sub, hDQ, sub_self]
      obtain ⟨E, _, hE⟩ := exists_modulatedAffineDiracComb_sum_of_translation_eigen C
        (T - Q) hC w hw s (sub_eq_zero.mp hkernel)
      let initial (y : ℝ) : AffineCombTerm :=
        ⟨s, y, extendedAtomicCoefficient C (combDistributionModulation (-s) (T - Q)) y⟩
      have hfirst : T - Q = affineCombTermSum w hw (E.toList.map initial) := by
        rw [hE]
        simp only [affineCombTermSum, List.map_map]
        let source (y : ℝ) := (initial y).distribution w hw
        change (E.val.map source).sum = (E.val.toList.map source).sum
        have he := congrArg (fun m : Multiset ℝ => (m.map source).sum)
          (Multiset.coe_toList E.val)
        simpa only [Multiset.map_coe, Multiset.sum_coe] using he.symm
      refine ⟨E.toList.map initial ++ terms.map lift, ?_, ?_⟩
      · simp only [affineCombTermSum, List.map_append, List.sum_append]
        change T = affineCombTermSum w hw (E.toList.map initial) + Q
        rw [← hfirst, sub_add_cancel]
      · intro q hq
        rcases List.mem_append.mp hq with hq | hq
        · obtain ⟨y, _, rfl⟩ := List.mem_map.mp hq
          exact List.mem_cons_self
        · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
          exact List.mem_cons_of_mem _ (hmodes p hp)

/-- A translation factor kills the covered spectral sites and retains the
original Fourier record at all other sites. -/
theorem atomicOnCarrier_fourier_combTranslationFactor (B : LocallyFiniteCarrier)
    (T : TemperedDistribution ℝ ℂ) (hFT : AtomicOnCarrier B (𝓕 T)) (w s : ℝ) :
    AtomicOnCarrier (B.restrict
      {x ∈ B.carrier | combModulationCharacter (-w) x ≠ combModulationCharacter (-w) s}
      (fun _ hx => hx.1)) (𝓕 (combTranslationFactor w s T)) := by
  intro f hf
  rw [combTranslationFactor_apply, ← temperedFourierLinearMap_apply, map_sub]
  simp only [temperedFourierLinearMap_apply, FourierTransform.fourier_smul,
    fourier_combDistributionTranslation]
  simp only [sub_apply, smul_apply, combDistributionModulation_apply, ← map_smul, ← map_sub]
  apply hFT
  intro x hx
  by_cases hphase : combModulationCharacter (-w) x = combModulationCharacter (-w) s
  · rw [_root_.sub_apply, combSchwartzModulation_apply, _root_.smul_apply, smul_eq_mul,
      hphase, sub_self]
  · have hz := hf x ⟨hx, hphase⟩
    rw [_root_.sub_apply, combSchwartzModulation_apply, _root_.smul_apply, smul_eq_mul,
      hz, mul_zero, mul_zero, sub_self]

/-- The spectral carrier left after deleting the sites with any prescribed phase. -/
def combTranslationFactorsSpectralCarrier (B : LocallyFiniteCarrier) (w : ℝ)
    (modes : List ℝ) : LocallyFiniteCarrier :=
  B.restrict {x ∈ B.carrier | ∀ s ∈ modes,
    combModulationCharacter (-w) x ≠ combModulationCharacter (-w) s} (fun _ hx => hx.1)

theorem atomicOnCarrier_fourier_combTranslationFactors (B : LocallyFiniteCarrier) (w : ℝ)
    (modes : List ℝ) (T : TemperedDistribution ℝ ℂ) (hFT : AtomicOnCarrier B (𝓕 T)) :
    AtomicOnCarrier (combTranslationFactorsSpectralCarrier B w modes)
      (𝓕 (combTranslationFactors w modes T)) := by
  induction modes generalizing B T with
  | nil =>
      exact AtomicOnCarrier.mono (T := combTranslationFactorsSpectralCarrier B w [])
        (fun x hx => ⟨hx, by simp⟩) hFT
  | cons s modes ih =>
      have h := ih _ _ (atomicOnCarrier_fourier_combTranslationFactor B T hFT w s)
      refine AtomicOnCarrier.mono (T := combTranslationFactorsSpectralCarrier B w (s :: modes))
        ?_ h
      intro x hx
      refine ⟨hx.1.1, ?_⟩
      intro t ht
      rcases List.mem_cons.mp ht with he | ht
      · subst t
        exact hx.1.2
      · exact hx.2 t ht

/-- The translation factors annihilate the actual original pair whenever
the true spectral carrier is covered by their reciprocal cosets. -/
theorem combTranslationFactors_eq_zero_of_spectral_cosets (w : ℝ) (hw : 0 < w)
    (modes : List ℝ) (B : LocallyFiniteCarrier)
    (T : TemperedDistribution ℝ ℂ) (hFT : AtomicOnCarrier B (𝓕 T))
    (hB : ∀ x ∈ B.carrier, ∃ s ∈ modes,
      x ∈ (affineDiracCombCarrier w⁻¹ (inv_pos.mpr hw) s).carrier) :
    combTranslationFactors w modes T = 0 := by
  apply (FourierTransform.fourierEquiv ℂ (TemperedDistribution ℝ ℂ)).injective
  change 𝓕 (combTranslationFactors w modes T) = 𝓕 (0 : TemperedDistribution ℝ ℂ)
  rw [FourierTransform.fourier_zero]
  ext f
  apply atomicOnCarrier_fourier_combTranslationFactors B w modes T hFT
  intro x hx
  obtain ⟨s, hs, hxs⟩ := hB x hx.1
  obtain ⟨k, hshift⟩ := (mem_affineDiracCombCarrier w⁻¹ (inv_pos.mpr hw) s x).mp hxs
  exact (hx.2 s hs (hshift ▸ combModulationCharacter_eq_on_reciprocal_coset w s hw k)).elim

/-- Complete reconstruction for one commensurable spectral class, with the
individual phases retained. The period and coset list are in normalized form. -/
theorem exists_affineCombTermSum_of_spectral_cosets (A B : LocallyFiniteCarrier)
    (T : TemperedDistribution ℝ ℂ) (hT : AtomicOnCarrier A T) (hFT : AtomicOnCarrier B (𝓕 T))
    (w : ℝ) (hw : 0 < w) (modes : List ℝ)
    (hdistinct : modes.Pairwise
      (fun s t => combModulationCharacter (-w) s ≠ combModulationCharacter (-w) t))
    (hB : ∀ x ∈ B.carrier, ∃ s ∈ modes,
      x ∈ (affineDiracCombCarrier w⁻¹ (inv_pos.mpr hw) s).carrier) :
    ∃ terms : List AffineCombTerm, T = affineCombTermSum w hw terms ∧
      ∀ q ∈ terms, q.frequency ∈ modes :=
  exists_affineCombTermSum_of_combTranslationFactors_eq_zero w hw modes hdistinct A T hT
    (combTranslationFactors_eq_zero_of_spectral_cosets w hw modes B T hFT hB)

end
end MeyerGeneralProblem
