module

public import MeyerGeneralProblem.Distribution.ClassCombFromLineSupport
public import MeyerGeneralProblem.Distribution.QuadrantGlobalLineCover

@[expose] public section

/-!
# The vanishing quadratic count theorem for normalized spectral classes

Remove the first class by its exact translation factors. The induction
hypothesis applies on the remaining actual spectral carrier. The
mixed-period line cover and bilateral recurrence then recover the
original record as a finite class-comb sum.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set Filter
open scoped BigOperators SchwartzMap FourierTransform

/-- Two steps spanning different rational directions have injective
integer coordinates. -/
theorem integerPlaneMap_injective_of_not_parallel (a w : ℝ) (hw : w ≠ 0)
    (ha : a ∉ rationalLineDirection w) :
    Function.Injective (integerPlaneMap a w) := by
  intro p q he
  let d := p - q
  have hd : integerPlaneMap a w d = 0 := by
    dsimp only [d]
    rw [map_sub,he,sub_self]
  rw [integerPlaneMap_real_apply] at hd
  have h₁ : d.1 = 0 := by
    by_contra hn
    have hr : (d.1 : ℝ) ≠ 0 := by exact_mod_cast hn
    apply ha
    apply Submodule.mem_span_singleton.mpr
    refine ⟨-(d.2 : ℚ) / (d.1 : ℚ), ?_⟩
    rw [Rat.smul_def]
    push_cast
    field_simp
    linarith only [hd]
  have h₂ : d.2 = 0 := by
    rw [h₁,Int.cast_zero,zero_mul,zero_add] at hd
    exact_mod_cast (mul_eq_zero.mp hd).resolve_right hw
  exact sub_eq_zero.mp (Prod.ext h₁ h₂)

/-- For normalized reciprocal lattice classes, vanishing quadratic
lower count on the original physical support forces an exact finite
class-comb decomposition of the complete original distribution. -/
theorem isFiniteSpectralClassCombSum_of_normalized_lattice_spectrum
    (classes : List (ℝ × List ℝ))
    (hpos : ∀ p ∈ classes, 0 < p.1)
    (hNonempty : ∀ p ∈ classes, p.2 ≠ [])
    (hModes : ∀ p ∈ classes, p.2.Pairwise
      (fun s t => combModulationCharacter (-p.1) s ≠ combModulationCharacter (-p.1) t))
    (hsep : classes.Pairwise (fun p q => p.1 ∉ rationalLineDirection q.1))
    (A B : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier A T) (hFT : AtomicOnCarrier B (𝓕 T))
    (hcover : ∀ x ∈ B.carrier, ∃ p ∈ classes, ∃ s ∈ p.2, ∃ k : ℤ,
      x = s + (k : ℝ) * p.1⁻¹)
    (hcount : ∀ e : ℝ, 0 < e → ∃ᶠ R : ℝ in atTop,
      ((A.carrier ∩ Icc (-R) R).ncard : ℝ) < e * R ^ 2) :
    IsFiniteSpectralClassCombSum classes T := by
  induction classes generalizing A B T with
  | nil =>
      have hzero := combTranslationFactorsByClass_eq_zero_of_phase_cover [] B T hFT
        (fun x hx => by simpa using hcover x hx)
      change T = 0 at hzero
      exact ⟨Fin 0,inferInstance,Fin.elim0,Fin.elim0,(fun i => Fin.elim0 i),
        by simp [hzero],fun i => Fin.elim0 i⟩
  | cons c classes ih =>
      obtain ⟨w,modes⟩ := c
      obtain ⟨hHead,hTail⟩ := List.pairwise_cons.mp hsep
      have hw : 0 < w := hpos (w,modes) List.mem_cons_self
      let V := combTranslationFactors w modes T
      let A₁ := combTranslationFactorsPhysicalCarrier w modes A
      let B₁ := combTranslationFactorsSpectralCarrier B w modes
      have hcover₁ (x : ℝ) (hx : x ∈ B₁.carrier) : ∃ p ∈ classes, ∃ s ∈ p.2,
          ∃ k : ℤ, x = s + (k : ℝ) * p.1⁻¹ := by
        obtain ⟨p,hp,s,hs,k,he⟩ := hcover x hx.1
        rcases List.mem_cons.mp hp with hp | hp
        · subst p
          exact (hx.2 s hs (he ▸ combModulationCharacter_eq_on_reciprocal_coset w s hw k)).elim
        · exact ⟨p,hp,s,hs,k,he⟩
      obtain ⟨ι,inst,q,a,ha,hV,hclasses⟩ := ih
        (fun p hp => hpos p (List.mem_cons_of_mem _ hp))
        (fun p hp => hNonempty p (List.mem_cons_of_mem _ hp))
        (fun p hp => hModes p (List.mem_cons_of_mem _ hp)) hTail A₁ B₁ V
        (atomicOnCarrier_combTranslationFactors w modes A T hT)
        (atomicOnCarrier_fourier_combTranslationFactors B w modes T hFT)
        hcover₁ (vanishingQuadraticLowerCount_combTranslationFactorsPhysicalCarrier w modes A hcount)
      let _ := inst
      have hindep (i : ι) : Function.Injective (integerPlaneMap (a i) w) := by
        apply integerPlaneMap_injective_of_not_parallel (a i) w hw.ne'
        intro he
        obtain ⟨p,hp,hpi,_⟩ := hclasses i
        have hOut := hHead p hp
        change w ∉ rationalLineDirection p.1 at hOut
        rw [hpi,rationalLineDirection_eq_of_mem_ne_zero (a i) w (ha i).ne' he] at hOut
        exact hOut (Submodule.mem_span_singleton_self w)
      obtain ⟨E,_,hLine⟩ := exists_atomicOnCarrier_affineLatticeUnion_of_combTranslationFactors
        q a ha A T hT w hw modes (hNonempty (w,modes) List.mem_cons_self)
        (hModes (w,modes) List.mem_cons_self) hV hindep (⊤ : AddSubgroup ℝ)
        (fun _ => by simp) (by simp) hcount
      exact isFiniteSpectralClassCombSum_of_recurrence_and_affine_lattice_cover
        ((w,modes) :: classes) hpos hModes hsep A T hT E hLine
        (translationDifferenceProduct_extendedAtomicCoefficient_eq_zero_of_spectral_cover
          ((w,modes) :: classes) hpos A B T hT hFT hcover)

end
end MeyerGeneralProblem
