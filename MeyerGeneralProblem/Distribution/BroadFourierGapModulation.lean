module

public import MeyerGeneralProblem.Cardinal.Adaptive.PeriodicDescent
public import MeyerGeneralProblem.Distribution.BroadCenteredFourierGap
public import MeyerGeneralProblem.Distribution.FiniteModulationMenu
public import MeyerGeneralProblem.Distribution.OriginalStrongFourierSquare
public import MeyerGeneralProblem.Distribution.RealRootedCosetPhysicalJets

@[expose] public section

/-!
# The broad Fourier gap theorem and its modulation consequences

An arbitrary gap of the required width detects the original distribution.
The same interval works for every finite exponential multiplication of
that distribution, with its original carrier count and Schwartz order.
-/

namespace MeyerGeneralProblem

noncomputable section

open Adaptive Filter Set
open scoped FourierTransform Topology

private theorem schwartzSeminorms_combModulation_le (a : ℝ) (q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : SchwartzMap ℝ ℂ,
      ((Finset.Iic (q, q)).sup (schwartzSeminormFamily ℂ ℝ ℂ)) (combSchwartzModulation a f) ≤
        C * ((Finset.Iic (q, q)).sup (schwartzSeminormFamily ℂ ℝ ℂ)) f := by
  let I := Finset.Iic (q, q)
  let P := I.sup (schwartzSeminormFamily ℂ ℝ ℂ)
  let b := ‖2 * (Real.pi : ℂ) * Complex.I * (a : ℂ)‖
  let B (j : ℕ) := ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * b ^ i
  let C := ∑ j ∈ Finset.range (q + 1), B j
  have hB (j : ℕ) : 0 ≤ B j := Finset.sum_nonneg fun i _ => by dsimp [b]; positivity
  have hC : 0 ≤ C := Finset.sum_nonneg fun j _ => hB j
  refine ⟨C, hC, fun f => ?_⟩
  change P (combSchwartzModulation a f) ≤ C * P f
  refine Seminorm.finset_sup_apply_le (mul_nonneg hC (apply_nonneg P f)) ?_
  rintro ⟨k, j⟩ hjk
  have hkj : k ≤ q ∧ j ≤ q := Finset.mem_Iic.mp hjk
  change SchwartzMap.seminorm ℂ k j (combSchwartzModulation a f) ≤ C * P f
  refine (SchwartzMap.seminorm_le_bound' ℂ k j _ (mul_nonneg (hB j) (apply_nonneg P f)) ?_).trans
    (mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun n _ => hB n)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hkj.2))) (apply_nonneg P f))
  intro x
  have he : (combSchwartzModulation a f : ℝ → ℂ) = combModulationCharacter a * (f : ℝ → ℂ) :=
    funext (combSchwartzModulation_apply a f)
  change |x| ^ k * ‖iteratedDeriv j (combSchwartzModulation a f : ℝ → ℂ) x‖ ≤ B j * P f
  rw [he, iteratedDeriv_mul (contDiff_combModulationCharacter a j).contDiffAt
    (f.smooth j).contDiffAt]
  refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)).trans ?_
  rw [Finset.mul_sum, show B j = ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * b ^ i from rfl,
    Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  have hi : (k, j - i) ∈ I := Finset.mem_Iic.mpr ⟨hkj.1, (Nat.sub_le j i).trans hkj.2⟩
  have hbound : |x| ^ k * ‖iteratedDeriv (j - i) (f : ℝ → ℂ) x‖ ≤ P f :=
    (SchwartzMap.le_seminorm' ℂ k (j - i) f x).trans
      ((Finset.le_sup (f := schwartzSeminormFamily ℂ ℝ ℂ) hi) f)
  have hchar : ‖iteratedDeriv i (combModulationCharacter a) x‖ = b ^ i := by
    rw [iteratedDeriv_combModulationCharacter, norm_mul, norm_pow, norm_combModulationCharacter,
      mul_one]
  simp only [norm_mul, norm_natCast, hchar]
  calc
    _ = ((j.choose i : ℝ) * b ^ i) *
        (|x| ^ k * ‖iteratedDeriv (j - i) (f : ℝ → ℂ) x‖) := by ring
    _ ≤ ((j.choose i : ℝ) * b ^ i) * P f :=
      mul_le_mul_of_nonneg_left hbound (by dsimp [b]; positivity)

/-- Modulation changes the Schwartz bound constant while preserving its order. -/
theorem HasSchwartzOrderBound.combDistributionModulation {U : TemperedDistribution ℝ ℂ}
    {q : ℕ} (hU : HasSchwartzOrderBound U q) (a : ℝ) :
    HasSchwartzOrderBound (combDistributionModulation a U) q := by
  obtain ⟨D, hD, hDf⟩ := schwartzSeminorms_combModulation_le a q
  obtain ⟨C, hC, hCf⟩ := hU
  refine ⟨C * D, mul_nonneg hC hD, fun f => ?_⟩
  rw [combDistributionModulation_apply, mul_assoc]
  exact (hCf _).trans (mul_le_mul_of_nonneg_left (hDf f) hC)

/-- A finite sum of physical modulations acts at the same original order. -/
theorem HasSchwartzOrderBound.finiteExponentialMultiplication {U : TemperedDistribution ℝ ℂ}
    {q : ℕ} (hU : HasSchwartzOrderBound U q) {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (c : ι → ℂ) :
    HasSchwartzOrderBound (finiteExponentialMultiplication a c U) q := by
  have h := fun i => hU.combDistributionModulation (a i)
  choose C hC hCf using h
  refine ⟨∑ i, ‖c i‖ * C i, Finset.sum_nonneg (fun i _ => mul_nonneg (norm_nonneg _) (hC i)),
    fun f => ?_⟩
  simp only [MeyerGeneralProblem.finiteExponentialMultiplication, _root_.sum_apply, _root_.smul_apply,
    smul_eq_mul]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hCf i f) (norm_nonneg _)

/-- A single physical modulation preserves ordinary distributional support. -/
theorem distributionSupportedOn_combDistributionModulation {S : Set ℝ}
    {U : TemperedDistribution ℝ ℂ} (hU : DistributionSupportedOn S U) (a : ℝ) :
    DistributionSupportedOn S (combDistributionModulation a U) := by
  intro f hf hvan
  rw [combDistributionModulation_apply]
  have he : (combSchwartzModulation a f : ℝ → ℂ) = combModulationCharacter a * (f : ℝ → ℂ) :=
    funext (combSchwartzModulation_apply a f)
  apply hU
  · rw [he]
    exact hf.mul_left
  · rw [he]
    intro x hx
    filter_upwards [hvan x hx] with y hy
    simp [hy]

/-- The broad gap theorem for a bounded open interval of arbitrary center. -/
theorem eq_zero_of_centered_count_and_fourier_gap
    (S : LocallyFiniteCarrier)
    (hb : (atTop : Filter ℝ).IsBoundedUnder (· ≤ ·)
      (fun t => ((S.carrier ∩ Icc (-t) t).ncard : ℝ) / (2 * t)))
    (U : TemperedDistribution ℝ ℂ) (q : ℕ) (hS : DistributionSupportedOn S.carrier U)
    (hU : HasSchwartzOrderBound U q) (l r : ℝ)
    (hwidth : 2 * (((q + 2 + q : ℕ) : ℝ) *
      limsup (fun t : ℝ => ((S.carrier ∩ Icc (-t) t).ncard : ℝ) / (2 * t)) atTop) < r - l)
    (hgap : DistributionVanishesOn (Ioo l r) (𝓕 U)) : U = 0 := by
  let w := (r - l) / 2
  let a := (l + r) / 2
  have hw : ((q + 2 + q : ℕ) : ℝ) *
      limsup (fun t : ℝ => ((S.carrier ∩ Icc (-t) t).ncard : ℝ) / (2 * t)) atTop < w := by
    dsimp [w]
    linarith
  have hz : combDistributionModulation (-a) U = 0 := by
    apply eq_zero_of_centered_count_and_centered_fourier_gap S hb _ q
      (distributionSupportedOn_combDistributionModulation hS (-a))
      (hU.combDistributionModulation (-a)) w hw
    intro f hf hs
    rw [fourier_combDistributionModulation, combDistributionTranslation_apply]
    apply hgap
    · exact hf.comp_homeomorph (Homeomorph.addLeft (-a))
    · have he : (combSchwartzTranslation (-a) f : ℝ → ℂ) =
          (f : ℝ → ℂ) ∘ Homeomorph.addLeft (-a) := rfl
      rw [he, tsupport_comp_eq_preimage]
      intro x hx
      have h := hs hx
      change -w < -a + x ∧ -a + x < w at h
      dsimp [w, a] at h
      exact ⟨by linarith [h.1], by linarith [h.2]⟩
  rw [← combDistributionModulation_neg_apply a U, hz, map_zero]

/-- One interval detects every member of the finite-modulation module at
the original order and count threshold. -/
theorem finiteExponentialMultiplication_eq_zero_of_centered_count_and_fourier_gap
    (S : LocallyFiniteCarrier)
    (hb : (atTop : Filter ℝ).IsBoundedUnder (· ≤ ·)
      (fun t => ((S.carrier ∩ Icc (-t) t).ncard : ℝ) / (2 * t)))
    (U : TemperedDistribution ℝ ℂ) (q : ℕ) (hS : DistributionSupportedOn S.carrier U)
    (hU : HasSchwartzOrderBound U q) (l r : ℝ)
    (hwidth : 2 * (((q + 2 + q : ℕ) : ℝ) *
      limsup (fun t : ℝ => ((S.carrier ∩ Icc (-t) t).ncard : ℝ) / (2 * t)) atTop) < r - l)
    {ι : Type*} [Fintype ι] (a : ι → ℝ) (c : ι → ℂ)
    (hgap : DistributionVanishesOn (Ioo l r) (𝓕 (finiteExponentialMultiplication a c U))) :
    finiteExponentialMultiplication a c U = 0 := by
  apply eq_zero_of_centered_count_and_fourier_gap S hb _ q ?_
    (hU.finiteExponentialMultiplication a c) l r hwidth hgap
  intro f hf hvan
  simp only [finiteExponentialMultiplication, _root_.sum_apply, _root_.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro i _
  rw [distributionSupportedOn_combDistributionModulation hS (a i) f hf hvan, mul_zero]

/-- An upper linear centered count and a value-only Fourier record suffice
for whole-source annihilation. The matrix uses only the original atoms in
one compact spectral prefix. -/
theorem exists_finiteExponentialAnnihilator_of_centered_count_and_order
    (A B : LocallyFiniteCarrier)
    (hb : (atTop : Filter ℝ).IsBoundedUnder (· ≤ ·)
      (fun t => ((A.carrier ∩ Icc (-t) t).ncard : ℝ) / (2 * t)))
    (U : TemperedDistribution ℝ ℂ) (q : ℕ) (hA : DistributionSupportedOn A.carrier U)
    (hU : HasSchwartzOrderBound U q) (hB : AtomicOnCarrier B (𝓕 U)) :
    ∃ (ι : Type) (f : Fintype ι), letI := f
      ∃ (a : ι → ℝ) (c : ι → ℂ), Function.Injective a ∧
        (∃ x : ℝ, ∑ i, c i * combModulationCharacter (a i) x ≠ 0) ∧
        finiteExponentialMultiplication a c U = 0 := by
  let d := ((q + 2 + q : ℕ) : ℝ) *
    limsup (fun t : ℝ => ((A.carrier ∩ Icc (-t) t).ncard : ℝ) / (2 * t)) atTop
  let R := d + 1
  obtain ⟨ι, f, a, c, ha, hsym, hgap⟩ :=
    exists_finiteExponentialMultiplication_fourierGap B U hB R
  let _ := f
  have hw : 2 * d < R - (-R) := by dsimp [R]; linarith
  exact ⟨ι, f, a, c, ha, hsym,
    finiteExponentialMultiplication_eq_zero_of_centered_count_and_fourier_gap
      A hb U q hA hU (-R) R hw a c hgap⟩

/-- Upper linear centered counts on one record of an original broad
value-only pair produce a nonzero finite exponential annihilator. -/
theorem exists_finiteExponentialAnnihilator_of_centered_count
    (A B : LocallyFiniteCarrier)
    (hb : (atTop : Filter ℝ).IsBoundedUnder (· ≤ ·)
      (fun t => ((A.carrier ∩ Icc (-t) t).ncard : ℝ) / (2 * t)))
    (U : TemperedDistribution ℝ ℂ) (hA : AtomicOnCarrier A U)
    (hB : AtomicOnCarrier B (𝓕 U)) :
    ∃ (ι : Type) (f : Fintype ι), letI := f
      ∃ (a : ι → ℝ) (c : ι → ℂ), Function.Injective a ∧
        (∃ x : ℝ, ∑ i, c i * combModulationCharacter (a i) x ≠ 0) ∧
        finiteExponentialMultiplication a c U = 0 := by
  obtain ⟨q, _, hq⟩ := exists_hasSchwartzOrderBound U
  apply exists_finiteExponentialAnnihilator_of_centered_count_and_order A B hb U q ?_ hq hB
  intro f _ hf
  exact hA f fun x hx => (hf x hx).eq_of_nhds

/-- A linear centered count on the Fourier record gives the whole-source
annihilator in the exchanged orientation. -/
theorem exists_finiteExponentialAnnihilator_of_fourier_centered_count
    (A B : LocallyFiniteCarrier)
    (hb : (atTop : Filter ℝ).IsBoundedUnder (· ≤ ·)
      (fun t => ((B.carrier ∩ Icc (-t) t).ncard : ℝ) / (2 * t)))
    (U : TemperedDistribution ℝ ℂ) (hA : AtomicOnCarrier A U)
    (hB : AtomicOnCarrier B (𝓕 U)) :
    ∃ (ι : Type) (f : Fintype ι), letI := f
      ∃ (a : ι → ℝ) (c : ι → ℂ), Function.Injective a ∧
        (∃ x : ℝ, ∑ i, c i * combModulationCharacter (a i) x ≠ 0) ∧
        finiteExponentialMultiplication a c (𝓕 U) = 0 := by
  apply exists_finiteExponentialAnnihilator_of_centered_count B A.reflect hb _ hB
  rw [fourier_fourier_eq_originalDistributionReflection]
  exact atomicOnCarrier_originalDistributionReflection A U hA

end

end MeyerGeneralProblem
