module

public import MeyerGeneralProblem.Distribution.OriginalGroupedNewtonMoments
public import MeyerGeneralProblem.Distribution.FiniteExponentialMean
public import MeyerGeneralProblem.Distribution.BroadFourierGapModulation

@[expose] public section

/-!
# Original Fourier coefficients from translated Schwartz estimates

A single translated compact spectral test gives a finite exponential sum.
Long averages isolate its center coefficient, while the modulation estimate
controls the test seminorm by the derivative order of the translated bound.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set
open scoped ContDiff FourierTransform SchwartzMap

/-- The rectangular Schwartz seminorm changes by a polynomial of degree
given by its derivative order under modulation. -/
theorem exists_rectangular_schwartzSeminorm_combModulation_bound (k q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : ℝ) (f : SchwartzMap ℝ ℂ),
      ((Finset.Iic (k, q)).sup (schwartzSeminormFamily ℂ ℝ ℂ)) (combSchwartzModulation a f) ≤
        C * (1 + |a|) ^ q * ((Finset.Iic (k, q)).sup (schwartzSeminormFamily ℂ ℝ ℂ)) f := by
  let I := Finset.Iic (k, q)
  let P := I.sup (schwartzSeminormFamily ℂ ℝ ℂ)
  let D₀ : ℝ := ‖2 * (Real.pi : ℂ) * Complex.I‖
  refine ⟨(1 + D₀) ^ q, by positivity, fun a f => ?_⟩
  let b := ‖2 * (Real.pi : ℂ) * Complex.I * (a : ℂ)‖
  have hb : b = D₀ * |a| := by simp [b, D₀, Real.norm_eq_abs]
  have hbase : 1 + b ≤ (1 + D₀) * (1 + |a|) := by
    rw [hb]
    nlinarith [norm_nonneg (2 * (Real.pi : ℂ) * Complex.I), abs_nonneg a]
  change P (combSchwartzModulation a f) ≤ _ * P f
  refine Seminorm.finset_sup_apply_le (mul_nonneg (by positivity) (apply_nonneg P f)) ?_
  rintro ⟨m, j⟩ hmj
  have hmj' : m ≤ k ∧ j ≤ q := Finset.mem_Iic.mp hmj
  let S := (1 + b) ^ j
  have hS : S ≤ (1 + D₀) ^ q * (1 + |a|) ^ q := by
    calc
      S ≤ (1 + b) ^ q := pow_le_pow_right₀ (by linarith [show 0 ≤ b from norm_nonneg _]) hmj'.2
      _ ≤ ((1 + D₀) * (1 + |a|)) ^ q := pow_le_pow_left₀ (by dsimp [b]; positivity) hbase _
      _ = _ := mul_pow _ _ _
  change SchwartzMap.seminorm ℂ m j (combSchwartzModulation a f) ≤ _ * P f
  refine (SchwartzMap.seminorm_le_bound' ℂ m j _
    (mul_nonneg (by dsimp [S, b]; positivity) (apply_nonneg P f)) ?_).trans
    (mul_le_mul_of_nonneg_right hS (apply_nonneg P f))
  intro x
  have he : (combSchwartzModulation a f : ℝ → ℂ) = combModulationCharacter a * (f : ℝ → ℂ) :=
    funext (combSchwartzModulation_apply a f)
  change |x| ^ m * ‖iteratedDeriv j (combSchwartzModulation a f : ℝ → ℂ) x‖ ≤ S * P f
  rw [he, iteratedDeriv_mul (contDiff_combModulationCharacter a j).contDiffAt
    (f.smooth j).contDiffAt]
  refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)).trans ?_
  have hsum : S = ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * b ^ i := by
    dsimp [S]
    rw [add_comm, add_pow]
    simp only [one_pow, mul_one, mul_comm]
  rw [Finset.mul_sum, hsum, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  have hi : (m, j - i) ∈ I := Finset.mem_Iic.mpr ⟨hmj'.1, (Nat.sub_le j i).trans hmj'.2⟩
  have hbound : |x| ^ m * ‖iteratedDeriv (j - i) (f : ℝ → ℂ) x‖ ≤ P f :=
    (SchwartzMap.le_seminorm' ℂ m (j - i) f x).trans
      ((Finset.le_sup (f := schwartzSeminormFamily ℂ ℝ ℂ) hi) f)
  have hchar : ‖iteratedDeriv i (combModulationCharacter a) x‖ = b ^ i := by
    rw [iteratedDeriv_combModulationCharacter, norm_mul, norm_pow, norm_combModulationCharacter,
      mul_one]
  simp only [norm_mul, norm_natCast, hchar]
  calc
    _ = ((j.choose i : ℝ) * b ^ i) *
        (|x| ^ m * ‖iteratedDeriv (j - i) (f : ℝ → ℂ) x‖) := by ring
    _ ≤ ((j.choose i : ℝ) * b ^ i) * P f :=
      mul_le_mul_of_nonneg_left hbound (by dsimp [b]; positivity)

/-- A translation-uniform Schwartz bound bounds each original Fourier atom
by a polynomial in its frequency, independently of the other atoms. -/
theorem exists_original_fourier_coefficient_bound_of_uniform_translates (k q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (B : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ),
        AtomicOnCarrier B (𝓕 T) → ∀ D : ℝ, 0 ≤ D →
        (∀ (t : ℝ) (f : SchwartzMap ℝ ℂ),
          ‖combDistributionTranslation (-t) T f‖ ≤
            D * ((Finset.Iic (k, q)).sup (schwartzSeminormFamily ℂ ℝ ℂ)) f) →
        ∀ b : B.subtype, ‖(𝓕 T) (B.isolationSchwartz b)‖ ≤ D * C * (1 + |(b : ℝ)|) ^ q := by
  classical
  let P := (Finset.Iic (k, q)).sup (schwartzSeminormFamily ℂ ℝ ℂ)
  obtain ⟨M, hM, hm⟩ := exists_rectangular_schwartzSeminorm_combModulation_bound k q
  let C := M * P (𝓕 compactSchwartzCutoff)
  refine ⟨C, mul_nonneg hM (apply_nonneg _ _), ?_⟩
  intro B T hB D hD hUniform b
  let ψ := combSchwartzTranslation (-(b : ℝ)) compactSchwartzCutoff
  have hψ : HasCompactSupport (ψ : ℝ → ℂ) :=
    compactSchwartzCutoff_hasCompactSupport.comp_homeomorph (Homeomorph.addLeft (-(b : ℝ)))
  have hψb : ψ b = 1 := by
    change compactSchwartzCutoff (-(b : ℝ) + b) = 1
    rw [neg_add_cancel]
    exact compactSchwartzCutoff_eq_one (by norm_num)
  obtain ⟨F, hF⟩ := B.exists_finite_nonzero_values_of_hasCompactSupport ψ hψ
  let E := insert b F
  have hoff (x : B.subtype) (hx : x ∉ E) : ψ x = 0 :=
    hF x (fun hf => hx (Finset.mem_insert_of_mem hf))
  let a (x : B.subtype) : ℝ := x
  let c (x : B.subtype) := (𝓕 T) (B.isolationSchwartz x) * ψ x
  have hfinite (t : ℝ) : (𝓕 T) (combSchwartzModulation t ψ) =
      ∑ x ∈ E, c x * combModulationCharacter (a x) t := by
    have hmSupport : HasCompactSupport (combSchwartzModulation t ψ : ℝ → ℂ) := by
      apply HasCompactSupport.of_support_subset_isCompact hψ.isCompact
      intro x hx
      apply subset_closure
      intro hz
      exact hx (by simp [combSchwartzModulation_apply, hz])
    rw [atomicOnCarrier_apply_eq_sum_of_compact_of_zero_off_finset B _ hB _ hmSupport E
      (fun x hx => by rw [combSchwartzModulation_apply, hoff x hx, mul_zero])]
    apply Finset.sum_congr rfl
    intro x _
    rw [combSchwartzModulation_apply]
    have he : combModulationCharacter t (x : ℝ) = combModulationCharacter (a x) t := by
      simp [combModulationCharacter, a, mul_comm]
    rw [he]
    dsimp [c]
    ring
  have hψF : (𝓕 ψ) = combSchwartzModulation (-(b : ℝ)) (𝓕 compactSchwartzCutoff) := by
    ext x
    rw [combSchwartzModulation_apply]
    exact fourier_combSchwartzTranslation _ _ _
  have hbound (t : ℝ) :
      ‖∑ x ∈ E, c x * combModulationCharacter (a x) t‖ ≤ D * C * (1 + |(b : ℝ)|) ^ q := by
    rw [← hfinite, TemperedDistribution.fourier_apply, ← neg_neg t, fourier_combSchwartzModulation_neg,
      ← combDistributionTranslation_apply]
    change ‖combDistributionTranslation (-t) T (𝓕 ψ)‖ ≤ _
    calc
      _ ≤ D * P (𝓕 ψ) := hUniform t _
      _ ≤ D * (M * (1 + |(b : ℝ)|) ^ q * P (𝓕 compactSchwartzCutoff)) := by
        rw [hψF]
        apply mul_le_mul_of_nonneg_left _ hD
        simpa only [abs_neg] using hm (-(b : ℝ)) (𝓕 compactSchwartzCutoff)
      _ = _ := by dsimp [C]; ring
  have hc := norm_coefficient_le_of_finiteExponentialSum_bound E a c
    Subtype.val_injective.injOn _ hbound b (Finset.mem_insert_self _ _)
  simpa only [c, hψb, mul_one] using hc

end
end MeyerGeneralProblem
