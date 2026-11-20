module

public import MeyerGeneralProblem.Distribution.FiniteCombConvolutionSupport

@[expose] public section

/-!
# Vanishing quadratic lower count under finite translations

A common reduced radius bounds all the translated windows by the same
original window. This preserves arbitrarily small quadratic counts and
allows the actual finite convolution carrier in the spectral-class
induction.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter Set
open scoped Topology

/-- A finite union of translated records has a common centered-window
bound in terms of one original count. -/
theorem finiteCombConvolutionCarrier_count_le {ι : Type*} [Fintype ι]
    (S : LocallyFiniteCarrier) (a : ι → ℝ) (M r R : ℝ)
    (hM : ∀ i, |a i| ≤ M) (hR : r + M ≤ R) :
    ((finiteCombConvolutionCarrier S a).carrier ∩ Icc (-r) r).ncard ≤
      Fintype.card ι * (S.carrier ∩ Icc (-R) R).ncard := by
  classical
  let F := (S.finite_inter_Icc (-R) R).toFinset
  let K := Finset.univ.biUnion (fun i : ι => F.image (fun x : ℝ => a i + x))
  have hF : F.card = (S.carrier ∩ Icc (-R) R).ncard :=
    (Set.ncard_eq_toFinset_card _ (S.finite_inter_Icc (-R) R)).symm
  have hsub : (finiteCombConvolutionCarrier S a).carrier ∩ Icc (-r) r ⊆ (K : Set ℝ) := by
    intro y hy
    obtain ⟨i, x, hx, rfl⟩ := Set.mem_iUnion.mp hy.1
    have hxy : a i + x ∈ Icc (-r) r := hy.2
    have ha := abs_le.mp (hM i)
    have hxR : x ∈ Icc (-R) R := ⟨by linarith [ha.2, hxy.1], by linarith [ha.1, hxy.2]⟩
    have hxF : x ∈ F := (S.finite_inter_Icc (-R) R).mem_toFinset.mpr ⟨hx, hxR⟩
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_image.mpr ⟨x, hxF, rfl⟩⟩
  calc
    _ ≤ (K : Set ℝ).ncard := Set.ncard_le_ncard hsub K.finite_toSet
    _ = K.card := Set.ncard_coe_finset K
    _ ≤ ∑ i : ι, (F.image fun x : ℝ => a i + x).card := Finset.card_biUnion_le
    _ ≤ ∑ _i : ι, F.card := Finset.sum_le_sum fun _ _ => Finset.card_image_le
    _ = _ := by simp [hF]

/-- A finite union of translates preserves vanishing quadratic lower
count, even when a source has no finite quadratic upper count. -/
theorem vanishingQuadraticLowerCount_finiteCombConvolutionCarrier
    {ι : Type*} [Fintype ι] (S : LocallyFiniteCarrier) (a : ι → ℝ)
    (hcount : ∀ c : ℝ, 0 < c → ∃ᶠ R : ℝ in atTop,
      ((S.carrier ∩ Icc (-R) R).ncard : ℝ) < c * R ^ 2) :
    ∀ c : ℝ, 0 < c → ∃ᶠ R : ℝ in atTop,
      (((finiteCombConvolutionCarrier S a).carrier ∩ Icc (-R) R).ncard : ℝ) < c * R ^ 2 := by
  classical
  intro c hc
  let M : ℝ := ∑ i : ι, |a i|
  let N : ℝ := Fintype.card ι
  let ε := c / (4 * (N + 1))
  have hM : 0 ≤ M := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hn : 0 ≤ N := by dsimp [N]; positivity
  have hε : 0 < ε := by dsimp [ε]; positivity
  apply frequently_atTop.mpr
  intro b
  obtain ⟨R, hR, hsmall⟩ :=
    frequently_atTop.mp (hcount ε hε) (max (b + M) (2 * M + 1))
  let r := R - M
  have hbr : b ≤ r := by dsimp [r]; linarith [(le_max_left _ _).trans hR]
  have hR₀ : 0 ≤ R := by linarith [(le_max_right _ _).trans hR]
  have htwo : R ≤ 2 * r := by dsimp [r]; linarith [(le_max_right _ _).trans hR]
  have hsq : R ^ 2 ≤ 4 * r ^ 2 := by
    calc
      _ ≤ (2 * r) ^ 2 := pow_le_pow_left₀ hR₀ htwo 2
      _ = _ := by ring
  have hM' (i : ι) : |a i| ≤ M :=
    Finset.single_le_sum (fun j _ => abs_nonneg (a j)) (Finset.mem_univ i)
  have hbound : (((finiteCombConvolutionCarrier S a).carrier ∩ Icc (-r) r).ncard : ℝ) ≤
      N * ((S.carrier ∩ Icc (-R) R).ncard : ℝ) := by
    dsimp only [N]
    exact_mod_cast finiteCombConvolutionCarrier_count_le S a M r R hM' (by dsimp [r]; linarith)
  have hscaled : (N + 1) * ε = c / 4 := by
    dsimp only [ε]
    field_simp [show N + 1 ≠ 0 by positivity]
  refine ⟨r, hbr, hbound.trans_lt ?_⟩
  calc
    _ ≤ (N + 1) * ((S.carrier ∩ Icc (-R) R).ncard : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ < (N + 1) * (ε * R ^ 2) := mul_lt_mul_of_pos_left hsmall (by positivity)
    _ = (c / 4) * R ^ 2 := by rw [← mul_assoc, hscaled]
    _ ≤ (c / 4) * (4 * r ^ 2) := mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = _ := by ring

end

end MeyerGeneralProblem
