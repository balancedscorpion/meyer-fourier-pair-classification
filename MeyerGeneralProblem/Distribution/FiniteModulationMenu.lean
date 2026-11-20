module

public import MeyerGeneralProblem.Distribution.FiniteModulationGap
public import Mathlib.Analysis.SpecificLimits.Normed

@[expose] public section

/-!
# A finite modulation menu with fewer local spectral rows than columns

Use fractional parts of bounded nonnegative integer combinations of the
contributing spectral prefix. Their number grows at most polynomially.
At some successive pair of boxes it therefore grows by a factor less
than two. Integer translates then produce the row deficit in a fixed
window, without any assumptions on the spectral module.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter Set
open scoped Topology FourierTransform
open UniformDiscrete

private def residueBox {ι : Type*} [Fintype ι] (b : ι → ℝ) (N : ℕ) : Finset ℝ := by
  classical
  exact Finset.univ.image fun e : ι → Fin (N + 1) =>
    Int.fract (∑ i, (e i : ℕ) • b i)

private theorem residueBox_mem_Ico {ι : Type*} [Fintype ι] (b : ι → ℝ)
    (N : ℕ) {u : ℝ} (hu : u ∈ residueBox b N) : u ∈ Ico (0 : ℝ) 1 := by
  classical
  obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hu
  exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

private theorem residueBox_succ_mem {ι : Type*} [Fintype ι] (b : ι → ℝ)
    (N : ℕ) {u : ℝ} (hu : u ∈ residueBox b N) (j : ι) :
    Int.fract (b j + u) ∈ residueBox b (N + 1) := by
  classical
  obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hu
  let e' (i : ι) : Fin (N + 1 + 1) :=
    ⟨(e i : ℕ) + if i = j then 1 else 0, by split <;> have := (e i).isLt <;> omega⟩
  apply Finset.mem_image.mpr
  refine ⟨e', Finset.mem_univ _, ?_⟩
  have hsum : (∑ i, (e' i : ℕ) • b i) = (∑ i, (e i : ℕ) • b i) + b j := by
    simp only [e', add_nsmul, Finset.sum_add_distrib]
    congr 1
    calc
      (∑ i, (if i = j then 1 else 0 : ℕ) • b i) =
          ∑ i, if i = j then b i else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        split_ifs <;> simp
      _ = b j := by simp
  rw [hsum, add_comm (∑ i, (e i : ℕ) • b i) (b j)]
  let x : ℝ := ∑ i, (e i : ℕ) • b i
  change Int.fract (b j + x) = Int.fract (b j + (x - (⌊x⌋ : ℝ)))
  rw [← add_sub_assoc, Int.fract_sub_intCast]

private theorem exists_residueBox_slow_step {ι : Type*} [Fintype ι] (b : ι → ℝ) :
    ∃ N, (residueBox b (N + 1)).card < 2 * (residueBox b N).card := by
  classical
  have hupper (n : ℕ) : (residueBox b n).card ≤ (n + 1) ^ Fintype.card ι :=
    Finset.card_image_le.trans_eq (by simp)
  have hbase : 1 ≤ (residueBox b 0).card := by
    apply Finset.Nonempty.card_pos
    refine ⟨0, Finset.mem_image.mpr ⟨fun _ => 0, Finset.mem_univ _, ?_⟩⟩
    simp
  by_contra h
  push Not at h
  have hlower (n : ℕ) : 2 ^ n ≤ (residueBox b n).card := by
    induction n with
    | zero => simpa using hbase
    | succ n ih =>
      simpa only [pow_succ, mul_comm _ 2] using (Nat.mul_le_mul_left 2 ih).trans (h n)
  have hlim := tendsto_pow_const_div_const_pow_of_one_lt (Fintype.card ι)
    (r := 2) (by norm_num)
  obtain ⟨n, hn, hsmall⟩ := ((eventually_gt_atTop (0 : ℕ)).and
    (hlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num)))).exists
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hle : (2 : ℝ) ^ n ≤ ((n : ℝ) + 1) ^ Fintype.card ι := by
    exact_mod_cast (hlower n).trans (hupper n)
  have hpos : 0 < (2 : ℝ) ^ n.succ := by positivity
  have hh := (div_lt_iff₀ hpos).mp hsmall
  rw [Nat.cast_succ, pow_succ] at hh
  linarith

private def residueMenu {ι : Type*} [Fintype ι] (b : ι → ℝ)
    (N K : ℕ) (p : residueBox b N × Fin (2 * K + 1)) : ℝ :=
  (p.1 : ℝ) + (((p.2 : ℕ) : ℤ) - (K : ℤ) : ℤ)

private theorem residueMenu_injective {ι : Type*} [Fintype ι] (b : ι → ℝ)
    (N K : ℕ) : Function.Injective (residueMenu b N K) := by
  intro p q h
  have hp := Int.fract_eq_self.mpr (residueBox_mem_Ico b N p.1.property)
  have hq := Int.fract_eq_self.mpr (residueBox_mem_Ico b N q.1.property)
  have hf := congrArg Int.fract h
  simp only [residueMenu, Int.fract_add_intCast, hp, hq] at hf
  apply Prod.ext (Subtype.ext hf)
  apply Fin.ext
  simp only [residueMenu, Int.cast_sub, Int.cast_natCast] at h
  exact_mod_cast (show ((p.2 : ℕ) : ℝ) = ((q.2 : ℕ) : ℝ) by linarith)

private theorem residueMenu_abs_le {ι : Type*} [Fintype ι] (b : ι → ℝ)
    (N K : ℕ) (p : residueBox b N × Fin (2 * K + 1)) :
    |residueMenu b N K p| ≤ (K : ℝ) + 1 := by
  have h := residueBox_mem_Ico b N p.1.property
  have hp : ((p.2 : ℕ) : ℝ) ≤ 2 * (K : ℝ) := by
    exact_mod_cast (show (p.2 : ℕ) ≤ 2 * K by have := p.2.isLt; omega)
  have hnonneg : (0 : ℝ) ≤ (p.2 : ℕ) := by positivity
  rw [abs_le]
  simp only [residueMenu, Int.cast_sub, Int.cast_natCast]
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- Every locally finite spectral carrier admits distinct finite shift columns
with strictly fewer shifted carrier sites in the fixed window. -/
theorem exists_finiteModulationMenu_card_lt (B : LocallyFiniteCarrier) (R : ℝ) :
    ∃ (ι : Type) (f : Fintype ι) (a : ι → ℝ), Function.Injective a ∧
      Fintype.card (spectralWindow (@finiteCombConvolutionCarrier ι f B a) R) < @Fintype.card ι f := by
  classical
  obtain ⟨M, hM⟩ := exists_nat_ge (R + 1)
  let K := 2 * M + 1
  let b (i : spectralWindow B (R + K + 1)) : ℝ := i
  obtain ⟨N, hN⟩ := exists_residueBox_slow_step b
  let a := residueMenu b N K
  have hres (x : spectralWindow (finiteCombConvolutionCarrier B a) R) :
      Int.fract (x : ℝ) ∈ residueBox b (N + 1) := by
    obtain ⟨i, t, ht, htx⟩ := mem_iUnion.mp x.property.1
    have habs : |t| ≤ R + (K : ℝ) + 1 := by
      have hi := residueMenu_abs_le b N K i
      have hx : |(x : ℝ)| ≤ R := abs_le.mpr x.property.2
      rw [show t = (x : ℝ) - a i by linarith]
      calc
        _ ≤ |(x : ℝ)| + |a i| := abs_sub _ _
        _ ≤ R + (K : ℝ) + 1 := by linarith
    let j : spectralWindow B (R + K + 1) := ⟨t, ht, abs_le.mp habs⟩
    have hf : Int.fract (x : ℝ) = Int.fract (b j + (i.1 : ℝ)) := by
      rw [← htx]
      change Int.fract ((i.1 : ℝ) + (((i.2 : ℕ) : ℤ) - ↑K : ℤ) + t) = _
      rw [add_right_comm, Int.fract_add_intCast, add_comm]
    rw [hf]
    exact residueBox_succ_mem b N i.1.property j
  have hfloor (x : spectralWindow (finiteCombConvolutionCarrier B a) R) :
      -(M : ℤ) ≤ ⌊(x : ℝ)⌋ := by
    apply Int.le_floor.mpr
    push_cast
    linarith [x.property.2.1]
  let rowIndex (x : spectralWindow (finiteCombConvolutionCarrier B a) R) :
      residueBox b (N + 1) × Fin (2 * M + 1) :=
    (⟨Int.fract x, hres x⟩, ⟨(⌊(x : ℝ)⌋ + (M : ℤ)).toNat, by
      have hlo := hfloor x
      have hhi : ⌊(x : ℝ)⌋ ≤ (M : ℤ) := by
        exact_mod_cast (show (⌊(x : ℝ)⌋ : ℝ) ≤ (M : ℝ) by
          linarith [Int.floor_le (x : ℝ), x.property.2.2])
      omega⟩)
  have hinj : Function.Injective rowIndex := by
    intro x y h
    have hfrac : Int.fract (x : ℝ) = Int.fract (y : ℝ) :=
      congrArg (fun p => (p.1 : ℝ)) h
    have hidx : (⌊(x : ℝ)⌋ + (M : ℤ)).toNat = (⌊(y : ℝ)⌋ + (M : ℤ)).toNat :=
      congrArg (fun p => (p.2 : ℕ)) h
    have hx := hfloor x
    have hy := hfloor y
    have hf : ⌊(x : ℝ)⌋ = ⌊(y : ℝ)⌋ := by omega
    apply Subtype.ext
    rw [← Int.fract_add_floor (x : ℝ), ← Int.fract_add_floor (y : ℝ), hfrac, hf]
  have hrow := Fintype.card_le_of_injective rowIndex hinj
  simp only [Fintype.card_prod, Fintype.card_coe, Fintype.card_fin] at hrow
  refine ⟨_, inferInstance, a, residueMenu_injective b N K, ?_⟩
  simpa only [Fintype.card_prod, Fintype.card_coe, Fintype.card_fin] using
    calc
      _ ≤ (residueBox b (N + 1)).card * (2 * M + 1) := hrow
      _ < 2 * (residueBox b N).card * (2 * M + 1) :=
        Nat.mul_lt_mul_of_pos_right hN (by omega)
      _ ≤ (residueBox b N).card * (2 * K + 1) := by
        rw [mul_comm 2, mul_assoc]
        exact Nat.mul_le_mul_left _ (by dsimp [K]; omega)

/-- For any fixed window, some genuine nonzero exponential polynomial makes
the Fourier transform of the modulated source vanish on that window. -/
theorem exists_finiteExponentialMultiplication_fourierGap
    (B : LocallyFiniteCarrier) (U : TemperedDistribution ℝ ℂ)
    (hB : AtomicOnCarrier B (𝓕 U)) (R : ℝ) :
    ∃ (ι : Type) (f : Fintype ι), letI := f
      ∃ (a : ι → ℝ) (c : ι → ℂ), Function.Injective a ∧
        (∃ x : ℝ, ∑ i, c i * combModulationCharacter (a i) x ≠ 0) ∧
        VanishesOnInterval (𝓕 (finiteExponentialMultiplication a c U)) R := by
  obtain ⟨ι, f, a, ha, hcard⟩ := exists_finiteModulationMenu_card_lt B R
  let _ := f
  obtain ⟨c, hc, hvan⟩ := exists_finiteModulation_fourierGap_of_card_lt B U hB a R hcard
  exact ⟨ι, f, a, c, ha, exists_eval_ne_zero_of_finiteModulation_coefficients_ne_zero a ha c hc,
    hvan⟩

/-- The whole-source annihilator follows from a fixed gap detector on the
physical carrier. The finite modulation menu and its rank deficit have
no additional hypotheses on the spectrum. -/
theorem exists_finiteExponentialAnnihilator_of_spectralGapUniqueness
    (A B : LocallyFiniteCarrier) (U : TemperedDistribution ℝ ℂ)
    (hA : AtomicOnCarrier A U) (hB : AtomicOnCarrier B (𝓕 U))
    (R : ℝ) (hgap : SpectralGapUniqueness A R) :
    ∃ (ι : Type) (f : Fintype ι), letI := f
      ∃ (a : ι → ℝ) (c : ι → ℂ), Function.Injective a ∧
        (∃ x : ℝ, ∑ i, c i * combModulationCharacter (a i) x ≠ 0) ∧
        finiteExponentialMultiplication a c U = 0 := by
  obtain ⟨ι, f, a, ha, hcard⟩ := exists_finiteModulationMenu_card_lt B R
  let _ := f
  obtain ⟨c, hc, hzero⟩ :=
    exists_finiteModulation_eq_zero_of_card_lt_of_gap A B U hA hB a R hgap hcard
  exact ⟨ι, f, a, c, ha, exists_eval_ne_zero_of_finiteModulation_coefficients_ne_zero a ha c hc,
    hzero⟩

end

end MeyerGeneralProblem
