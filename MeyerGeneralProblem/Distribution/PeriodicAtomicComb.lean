module

public import MeyerGeneralProblem.Cardinal.Strong.OriginalDilationCoefficients
public import MeyerGeneralProblem.Distribution.CarrierUnion

@[expose] public section

/-!
# Periodic value-only atomic records

A periodic tempered atomic distribution is a finite sum of full affine
Dirac combs, with the original masses from a half-open fundamental interval.
The allowed carrier may have unused sites and need not itself be periodic.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set
open scoped SchwartzMap

/-- Translation transports the intrinsic local masses, including all zero
coefficients outside the translated carrier. -/
theorem extendedAtomicCoefficient_translation (A : LocallyFiniteCarrier)
    (T : TemperedDistribution ℝ ℂ) (hT : AtomicOnCarrier A T) (a x : ℝ) :
    extendedAtomicCoefficient (A.translate a) (combDistributionTranslation a T) (a + x) =
      extendedAtomicCoefficient A T x := by
  classical
  have hmem : a + x ∈ (A.translate a).carrier ↔ x ∈ A.carrier := by
    rw [LocallyFiniteCarrier.mem_translate]
    constructor
    · rintro ⟨y, hy, he⟩
      rwa [add_left_cancel he] at hy
    · exact fun hx => ⟨x, hx, rfl⟩
  by_cases hx : x ∈ A.carrier
  · rw [extendedAtomicCoefficient, dite_eq_left (hmem.mpr hx), combDistributionTranslation_apply]
    rw [atomic_action_singleton_values A T hT _ x]
    · rw [combSchwartzTranslation_apply, LocallyFiniteCarrier.isolationSchwartz_self, mul_one]
    · intro y hy hne
      rw [combSchwartzTranslation_apply]
      exact (A.translate a).isolationSchwartz_of_mem_of_ne ⟨a + x, hmem.mpr hx⟩
        ⟨y, hy, rfl⟩ (fun he => hne (add_left_cancel he))
  · have hnot : a + x ∉ (A.translate a).carrier := fun h => hx (hmem.mp h)
    simp only [extendedAtomicCoefficient, dite_eq_right hx, dite_eq_right hnot]

/-- Periodicity of the distribution implies periodicity of its original
coefficient function, including the zero extension at unused sites. -/
theorem periodic_extendedAtomicCoefficient_of_translation (A : LocallyFiniteCarrier)
    (T : TemperedDistribution ℝ ℂ) (hT : AtomicOnCarrier A T) (a : ℝ)
    (hperiod : combDistributionTranslation a T = T) :
    Function.Periodic (extendedAtomicCoefficient A T) a := by
  intro x
  have htranslated := atomicOnCarrier_combDistributionTranslation A T hT a
  rw [hperiod] at htranslated
  let U := (A.translate a).union A
  rw [add_comm x a,
    ← extendedAtomicCoefficient_on_larger_carrier A U subset_union_right T hT,
    extendedAtomicCoefficient_on_larger_carrier (A.translate a) U subset_union_left T htranslated]
  exact (congrArg (fun V => extendedAtomicCoefficient (A.translate a) V (a + x))
    hperiod).symm.trans (extendedAtomicCoefficient_translation A T hT a x)

/-- The full Dirac comb at the points `y + k * w`, with mass one at each. -/
def affineDiracComb (w : ℝ) (hw : 0 < w) (y : ℝ) : TemperedDistribution ℝ ℂ :=
  combDistributionDilation w hw.ne' (shiftedIntegerComb (y / w))

theorem affineDiracComb_apply (w : ℝ) (hw : 0 < w) (y : ℝ) (f : SchwartzMap ℝ ℂ) :
    affineDiracComb w hw y f = ∑' k : ℤ, f (y + (k : ℝ) * w) := by
  simp only [affineDiracComb, combDistributionDilation_apply, shiftedIntegerComb_apply,
    combSchwartzDilation_apply]
  apply tsum_congr
  intro k
  congr 1
  field_simp

/-- The actual affine lattice carrying the comb. -/
def affineDiracCombCarrier (w : ℝ) (hw : 0 < w) (y : ℝ) : LocallyFiniteCarrier :=
  (shiftedIntegerCombCarrier (y / w)).dilate w hw

theorem mem_affineDiracCombCarrier (w : ℝ) (hw : 0 < w) (y x : ℝ) :
    x ∈ (affineDiracCombCarrier w hw y).carrier ↔ ∃ k : ℤ, x = y + (k : ℝ) * w := by
  change (∃ z ∈ Set.range (fun n : ℤ => y / w + (n : ℝ)), w * z = x) ↔ _
  have he (k : ℤ) : w * (y / w + (k : ℝ)) = y + (k : ℝ) * w := by
    field_simp
  constructor
  · rintro ⟨z, ⟨k, rfl⟩, rfl⟩
    exact ⟨k, he k⟩
  · rintro ⟨k, rfl⟩
    exact ⟨_, ⟨k, rfl⟩, he k⟩

theorem affineDiracComb_atomicOnCarrier (w : ℝ) (hw : 0 < w) (y : ℝ) :
    AtomicOnCarrier (affineDiracCombCarrier w hw y) (affineDiracComb w hw y) :=
  atomicOnCarrier_combDistributionDilation _ w hw _ (shiftedIntegerComb_atomicOnCarrier _)

private theorem affineDiracComb_floor (w : ℝ) (hw : 0 < w) {y : ℝ}
    (hy : y ∈ Ico 0 w) (k : ℤ) :
    ⌊(y + (k : ℝ) * w) / w⌋ = k := by
  rw [Int.floor_eq_iff, le_div_iff₀ hw, div_lt_iff₀ hw]
  constructor <;> nlinarith [hy.1, hy.2]

/-- The exact reconstruction on the complete Schwartz space. Its finitely
many origins are all allowed sites in a single half-open fundamental
interval, and their coefficients are the original isolation masses. -/
theorem exists_affineDiracComb_sum_of_periodic_coefficients (A : LocallyFiniteCarrier)
    (T : TemperedDistribution ℝ ℂ) (hT : AtomicOnCarrier A T)
    (w : ℝ) (hw : 0 < w) (hperiod : Function.Periodic (extendedAtomicCoefficient A T) w) :
    ∃ E : Finset ℝ, (∀ y, y ∈ E ↔ y ∈ A.carrier ∩ Ico 0 w) ∧
      T = ∑ y ∈ E, extendedAtomicCoefficient A T y • affineDiracComb w hw y := by
  classical
  let E := (A.finite_inter_Icc 0 w).toFinset.filter (· < w)
  have hE (y : ℝ) : y ∈ E ↔ y ∈ A.carrier ∩ Ico 0 w := by
    simp only [E, Finset.mem_filter, Set.Finite.mem_toFinset, mem_inter_iff, mem_Icc, mem_Ico]
    exact ⟨fun h => ⟨h.1.1, h.1.2.1, h.2⟩, fun h => ⟨⟨h.1, h.2.1, h.2.2.le⟩, h.2.2⟩⟩
  let c := extendedAtomicCoefficient A T
  have horbit (y : ℝ) (k : ℤ) : c (y + (k : ℝ) * w) = c y := by
    simpa only [zsmul_eq_mul] using (hperiod.int_mul k) y
  have hsupport {y : ℝ} (hcy : c y ≠ 0) :
      (affineDiracCombCarrier w hw y).carrier ⊆ A.carrier := by
    intro x hx
    obtain ⟨k, rfl⟩ := (mem_affineDiracCombCarrier w hw y x).mp hx
    by_contra hn
    apply hcy
    rw [← horbit y k]
    simp only [c, extendedAtomicCoefficient, dite_eq_right hn]
  refine ⟨E, hE, ?_⟩
  change T = ∑ y ∈ E, c y • affineDiracComb w hw y
  apply atomic_eq_of_coefficients A _ _ hT
  · intro f hf
    simp only [_root_.sum_apply, smul_apply, smul_eq_mul]
    apply Finset.sum_eq_zero
    intro y _
    by_cases hc : c y = 0
    · rw [hc, zero_mul]
    · rw [((affineDiracComb_atomicOnCarrier w hw y).mono (hsupport hc)) f hf, mul_zero]
  · intro x
    let k := ⌊(x : ℝ) / w⌋
    let r := (x : ℝ) - (k : ℝ) * w
    have hx : (x : ℝ) = r + (k : ℝ) * w := by simp [r]
    have hr : r ∈ Ico 0 w := by
      constructor
      · have hlo := (le_div_iff₀ hw).mp (Int.floor_le ((x : ℝ) / w))
        dsimp [r, k]
        linarith
      · have hhi := (div_lt_iff₀ hw).mp (Int.lt_floor_add_one ((x : ℝ) / w))
        dsimp [r, k]
        linarith only [hhi]
    have hcr : T (A.isolationSchwartz x) = c r := by
      calc
        T (A.isolationSchwartz x) = c (x : ℝ) := by
          change T (A.isolationSchwartz x) = extendedAtomicCoefficient A T (x : ℝ)
          have hmem : (x : ℝ) ∈ A.carrier := x.property
          rw [extendedAtomicCoefficient, dite_eq_left hmem]
        _ = c r := by rw [hx, horbit]
    have hterm (y : ℝ) (hy : y ∈ E) :
        c y * affineDiracComb w hw y (A.isolationSchwartz x) =
          if y = r then c r else 0 := by
      by_cases he : y = r
      · subst y
        rw [ite_eq_left rfl]
        by_cases hc : c r = 0
        · rw [hc, zero_mul]
        · rw [affineDiracComb_apply, tsum_eq_single k, ← hx,
            LocallyFiniteCarrier.isolationSchwartz_self, mul_one]
          intro l hne
          apply A.isolationSchwartz_of_mem_of_ne x
            (hsupport hc ((mem_affineDiracCombCarrier w hw r _).mpr ⟨l, rfl⟩))
          intro hl
          apply hne
          simpa only [k, ← hl] using (affineDiracComb_floor w hw hr l).symm
      · rw [ite_eq_right he]
        by_cases hc : c y = 0
        · rw [hc, zero_mul]
        · rw [affineDiracComb_apply]
          have hzero (l : ℤ) : A.isolationSchwartz x (y + (l : ℝ) * w) = 0 := by
            apply A.isolationSchwartz_of_mem_of_ne x
              (hsupport hc ((mem_affineDiracCombCarrier w hw y _).mpr ⟨l, rfl⟩))
            intro hl
            have hk : k = l := by
              simpa only [k, hl] using affineDiracComb_floor w hw ((hE y).mp hy).2 l
            apply he
            rw [← hk] at hl
            linarith only [hl, hx]
          simp only [hzero, tsum_zero, mul_zero]
    simp only [_root_.sum_apply, smul_apply, smul_eq_mul]
    rw [hcr, Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
    by_cases hm : r ∈ E
    · rw [ite_eq_left hm]
    · have hnot : r ∉ A.carrier := fun h => hm ((hE r).mpr ⟨h, hr⟩)
      simp only [ite_eq_right hm, c, extendedAtomicCoefficient, dite_eq_right hnot]

/-- Every actual periodic value-only atomic tempered distribution is a
finite complex linear combination of its full affine Dirac combs. -/
theorem exists_affineDiracComb_sum_of_translation (A : LocallyFiniteCarrier)
    (T : TemperedDistribution ℝ ℂ) (hT : AtomicOnCarrier A T)
    (w : ℝ) (hw : 0 < w) (hperiod : combDistributionTranslation w T = T) :
    ∃ E : Finset ℝ, (∀ y, y ∈ E ↔ y ∈ A.carrier ∩ Ico 0 w) ∧
      T = ∑ y ∈ E, extendedAtomicCoefficient A T y • affineDiracComb w hw y :=
  exists_affineDiracComb_sum_of_periodic_coefficients A T hT w hw
    (periodic_extendedAtomicCoefficient_of_translation A T hT w hperiod)

end
end MeyerGeneralProblem
