module

public import MeyerGeneralProblem.Carrier.SeparatedColouring
public import MeyerGeneralProblem.Distribution.ModulationModuleDescent
public import MeyerGeneralProblem.Sampling.WindowIsolation
public import MeyerGeneralProblem.UniformDiscrete.SpectralGap

@[expose] public section

/-!
# Spectral gap uniqueness from bounded local counts

Use a finite colouring with separation one within each colour. To
interpolate at a target, temporarily remove points of every colour
within distance one of the target. Convolving the resulting tests
enforces all far zeros, and a finite differential operator inserts
the remaining nearby zeros without spending bandwidth.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter Set SchwartzMap
open scoped FourierTransform ContDiff

private theorem exists_windowTest_product {ι : Type*}
    (s : Finset ι) (f : ι → SchwartzMap ℝ ℂ) (W x : ℝ)
    (hs : ∀ i, Function.support (f i) ⊆ Icc (-W) W)
    (hx : ∀ i, (𝓕 (f i)) x = 1) :
    ∃ g : SchwartzMap ℝ ℂ,
      Function.support g ⊆ Icc (-((s.card : ℝ) * W + 1)) ((s.card : ℝ) * W + 1) ∧
      (𝓕 g) x = 1 ∧ ∀ y, (∃ i ∈ s, (𝓕 (f i)) y = 0) → (𝓕 g) y = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨G, hGs, hG0, _⟩ := exists_compact_positive_fourier_smoothing (r := 1) (by norm_num)
    obtain ⟨g, hgv, hgs⟩ := exists_schwartz_modulation G hGs x
    refine ⟨g, by simpa using hgs, ?_, by simp⟩
    rw [SchwartzMap.fourier_coe, funext hgv, fourier_mul_gramPhase, sub_self, hG0]
  | insert i s hi ih =>
    obtain ⟨g, hgs, hgx, hgz⟩ := ih
    obtain ⟨v, hv, hvs⟩ := exists_schwartz_fourierKernelConvolution
      g.integrable hgs (hs i) ((f i).smooth (⊤ : ℕ∞))
    have hBudget : (s.card : ℝ) * W + 1 + W = ((insert i s).card : ℝ) * W + 1 := by
      rw [Finset.card_insert_of_notMem hi, Nat.cast_succ]
      ring
    have hfourier (y : ℝ) : (𝓕 v) y = (𝓕 g) y * (𝓕 (f i)) y := by
      simp only [SchwartzMap.fourier_coe]
      rw [hv, fourier_fourierKernelConvolution g.integrable (f i).integrable]
    refine ⟨v, by simpa only [hBudget] using hvs, by simp [hfourier, hgx, hx], ?_⟩
    rintro y ⟨j, hj, hzero⟩
    rw [hfourier]
    rcases Finset.mem_insert.mp hj with rfl | hj
    · rw [hzero, mul_zero]
    · rw [hgz y ⟨j, hj, hzero⟩, zero_mul]

/-- One fixed window isolates each actual carrier point, even for gaps that
collapse arbitrarily within a unit cell. -/
theorem exists_windowSchwartz_isolation_of_unitCellBound
    (S : LocallyFiniteCarrier) (K : ℕ) (hK : UnitCellBound S K) :
    ∃ R : ℝ, 0 < R ∧ ∀ x : S.subtype, ∃ f : SchwartzMap ℝ ℂ,
      Function.support f ⊆ Icc (-R) R ∧
      ∀ y : S.subtype, (𝓕 f) y = if x = y then 1 else 0 := by
  classical
  obtain ⟨colour, hc⟩ := hK.exists_separatedColouring
  let C := Fin 2 × Fin K
  let R : ℝ := (Fintype.card C : ℝ) * 2 + 1
  refine ⟨R, by dsimp [R]; positivity, ?_⟩
  intro x
  let Far (i : C) := {y : S.subtype // y = x ∨ (colour y = i ∧ 1 ≤ |(y : ℝ) - x|)}
  have hsep (i : C) (u v : Far i) (hne : u ≠ v) :
      1 ≤ |((u.1 : S.subtype) : ℝ) - (v.1 : ℝ)| := by
    have huv : u.1 ≠ v.1 := fun h => hne (Subtype.ext h)
    rcases u.property with hu | ⟨huc, hu⟩ <;> rcases v.property with hv | ⟨hvc, hv⟩
    · exact (huv (hu.trans hv.symm)).elim
    · rw [hu, abs_sub_comm]
      exact hv
    · rw [hv]
      exact hu
    · exact hc _ _ huv (huc.trans hvc.symm)
  have htests (i : C) : ∃ f : SchwartzMap ℝ ℂ, Function.support f ⊆ Icc (-2 : ℝ) 2 ∧
      (𝓕 f) x = 1 ∧ ∀ y : S.subtype, colour y = i → 1 ≤ |(y : ℝ) - x| →
        (𝓕 f) y = 0 := by
    obtain ⟨g, hgs, hgv⟩ := exists_global_schwartz_fourier_interpolation
      (fun u : Far i => (u.1 : ℝ)) (a := 1) (d := 1) (r := 1)
      (by norm_num) (by norm_num) (by norm_num) (hsep i)
    let ix : Far i := ⟨x, Or.inl rfl⟩
    refine ⟨g ix, by norm_num at hgs ⊢; exact hgs ix, ?_, ?_⟩
    · simpa [← SchwartzMap.fourier_coe] using hgv ix ix
    · intro y hy hfar
      let iy : Far i := ⟨y, Or.inr ⟨hy, hfar⟩⟩
      have hne : ix ≠ iy := by
        intro he
        have hxy : x = y := congrArg Subtype.val he
        rw [← hxy, sub_self, abs_zero] at hfar
        norm_num at hfar
      simpa only [← SchwartzMap.fourier_coe, ite_eq_right hne] using hgv ix iy
  choose fs hfs hfx hfz using htests
  obtain ⟨g, hgs, hgx, hgz⟩ := exists_windowTest_product (Finset.univ : Finset C) fs
    2 x hfs hfx
  let Z := (S.finite_inter_Icc ((x : ℝ) - 1) ((x : ℝ) + 1)).toFinset.erase (x : ℝ)
  obtain ⟨h, hhs, hhx, hhz⟩ := exists_schwartz_fourier_kill_finite g Z x
    (by simp [Z]) (by rw [hgx]; exact one_ne_zero) isClosed_Icc
    (by simpa only [Finset.card_univ, R] using hgs)
  refine ⟨((𝓕 h) x)⁻¹ • h, ?_, ?_⟩
  · intro t ht
    apply hhs
    intro he
    exact ht (by simp [smul_apply, he])
  · intro y
    rw [FourierTransform.fourier_smul, smul_apply, smul_eq_mul]
    split_ifs with hxy
    · subst y
      exact inv_mul_cancel₀ hhx
    · have hz : (𝓕 h) y = 0 := by
        apply hhz
        by_cases hfar : 1 ≤ |(y : ℝ) - x|
        · exact Or.inr (hgz y ⟨colour y, Finset.mem_univ _, hfz (colour y) y rfl hfar⟩)
        · apply Or.inl
          have habs := abs_lt.mp (lt_of_not_ge hfar)
          have hne : (y : ℝ) ≠ (x : ℝ) := fun he => hxy (Subtype.ext he.symm)
          simp only [Z, Finset.mem_erase, Set.Finite.mem_toFinset, mem_inter_iff, mem_Icc]
          exact ⟨hne, y.property, by linarith [habs.1], by linarith [habs.2]⟩
      rw [hz, mul_zero]

namespace UniformDiscrete

/-- Bounded local counts give a fixed spectral gap detector on the whole
broad value-only class, without a mass-growth or minimum-gap assumption. -/
theorem exists_spectralGapUniqueness_of_unitCellBound (S : LocallyFiniteCarrier) (K : ℕ)
    (hK : UnitCellBound S K) : ∃ R : ℝ, 0 < R ∧ SpectralGapUniqueness S R := by
  obtain ⟨R, hR, htests⟩ := exists_windowSchwartz_isolation_of_unitCellBound S K hK
  refine ⟨R + 1, by linarith, ?_⟩
  intro U hU hgap
  have hUA := hasLocallyAtomicAction_atomicOnCarrier S U hU
  apply atomicOnCarrier_eq_zero_of_isolationAction_eq_zero S U hUA
  intro x
  obtain ⟨f, hfs, hfv⟩ := htests x
  have hc : HasCompactSupport f :=
    HasCompactSupport.intro isCompact_Icc (fun t ht => not_not.mp (fun h => ht (hfs h)))
  have ht : tsupport f ⊆ Ioo (-(R + 1)) (R + 1) := by
    intro t ht
    obtain ⟨hlo, hhi⟩ := closure_minimal hfs isClosed_Icc ht
    exact ⟨by linarith, by linarith⟩
  have hz := hgap f hc ht
  rw [TemperedDistribution.fourier_apply] at hz
  suffices he : U (S.isolationSchwartz x) = U (𝓕 f) by rwa [he]
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply hUA
  intro y hy
  let j : S.subtype := ⟨y, hy⟩
  have hj := hfv j
  change (𝓕 f) y = _ at hj
  change S.isolationSchwartz x y - (𝓕 f) y = 0
  rw [hj]
  by_cases hxy : x = j
  · have hyx : y = (x : ℝ) := (congrArg (fun s : S.subtype => (s : ℝ)) hxy).symm
    rw [ite_eq_left hxy, hyx, S.isolationSchwartz_self, sub_self]
  · rw [ite_eq_right hxy, S.isolationSchwartz_of_mem_of_ne x hy (fun h => hxy (Subtype.ext h.symm)),
      sub_zero]

/-- Original broad pairs with one bounded-count carrier have a genuine
nonzero finite exponential annihilator in the spectral module. The
opposite carrier needs only local finiteness. -/
theorem exists_finiteExponentialAnnihilator_in_module_of_unitCellBound
    (A B : LocallyFiniteCarrier) (K : ℕ) (hK : UnitCellBound A K)
    (H : AddSubgroup ℝ) (hH : B.carrier ⊆ H) (U : TemperedDistribution ℝ ℂ)
    (hA : AtomicOnCarrier A U) (hB : AtomicOnCarrier B (𝓕 U)) :
    ∃ (ι : Type) (f : Fintype ι), letI := f
      ∃ (a : ι → ℝ) (c : ι → ℂ), Function.Injective a ∧ (∀ i, a i ∈ H) ∧
        (∃ x : ℝ, ∑ i, c i * combModulationCharacter (a i) x ≠ 0) ∧
        finiteExponentialMultiplication a c U = 0 := by
  obtain ⟨R, _, hgap⟩ := exists_spectralGapUniqueness_of_unitCellBound A K hK
  obtain ⟨ι, f, a, c, ha, hval, hz⟩ :=
    exists_finiteExponentialAnnihilator_of_spectralGapUniqueness A B U hA hB R hgap
  let _ := f
  have hc : c ≠ 0 := by
    intro he
    obtain ⟨x, hx⟩ := hval
    exact hx (by simp [he])
  obtain ⟨κ, g, b, d, hb, hfreq, hd, hzero⟩ :=
    exists_finiteExponentialAnnihilator_in_module_of_annihilated B H hH U hB a c ha hc hz
  let _ := g
  exact ⟨κ, g, b, d, hb, hfreq,
    exists_eval_ne_zero_of_finiteModulation_coefficients_ne_zero b hb d hd, hzero⟩

end UniformDiscrete
end

end MeyerGeneralProblem
