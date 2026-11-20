module

public import MeyerGeneralProblem.Sampling.PositiveSeparationDecay
public import MeyerGeneralProblem.Cross.CompactRemainder
public import MeyerGeneralProblem.Gram.SchurKernelOperator

@[expose] public section

/-!
# Separated-anchor Schur estimates with bounded finite multiplicity

All counting is performed on genuine group anchors. The finite coordinate
fibres contribute only their uniform multiplicity bound, and no intra-group
node gap enters either row bounds or uniform tails.
-/

namespace MeyerGeneralProblem

open Filter

noncomputable section

/-- A finite section of bounded-size coordinate fibres is controlled by the
corresponding finite set of group anchors, with only the multiplicity factor. -/
theorem sum_grouped_anchor_le
    {κ : Type*} [DecidableEq κ] (size : κ → ℕ) {q : ℕ} (hsize : ∀ g, size g ≤ q)
    (U : Finset (Σ g, Fin (size g))) (f : κ → ℝ) (hf : ∀ g, 0 ≤ f g) :
    (∑ i ∈ U, f i.1) ≤ (q : ℝ) * ∑ g ∈ U.image Sigma.fst, f g := by
  have hsub : U ⊆ (U.image Sigma.fst).sigma (fun g => (Finset.univ : Finset (Fin (size g)))) := by
    intro i hi
    exact Finset.mem_sigma.mpr ⟨Finset.mem_image_of_mem _ hi, Finset.mem_univ _⟩
  calc
    _ ≤ ∑ i ∈ (U.image Sigma.fst).sigma (fun g => (Finset.univ : Finset (Fin (size g)))), f i.1 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i hi hnot => hf i.1)
    _ = ∑ g ∈ U.image Sigma.fst, (size g : ℝ) * f g := by simp [Finset.sum_sigma]
    _ ≤ ∑ g ∈ U.image Sigma.fst, (q : ℝ) * f g := by
      exact Finset.sum_le_sum (fun g hg => mul_le_mul_of_nonneg_right
        (by exact_mod_cast hsize g) (hf g))
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- A bounded metric band contains uniformly finitely many grouped
coordinates, even when all coordinates of one group share its anchor. -/
theorem card_grouped_metricBand_le
    {κ : Type*} [DecidableEq κ] (size : κ → ℕ) {q : ℕ} (hsize : ∀ g, size g ≤ q)
    (s : κ → ℝ) {d : ℝ} (hd : 0 < d)
    (hsep : ∀ g h, g ≠ h → d ≤ |s g - s h|)
    (L a : ℝ) (U : Finset (Σ g, Fin (size g))) :
    (U.filter (fun i => |s i.1 - a| ≤ L)).card ≤
      q * (Finset.Icc ⌊-(positiveSeparationScale d * L)⌋
        ⌊positiveSeparationScale d * L⌋).card := by
  let V := U.filter (fun i => |s i.1 - a| ≤ L)
  have hmult : V.card ≤ q * (V.image Sigma.fst).card := by
    have h := sum_grouped_anchor_le size hsize V (fun _ => 1) (fun _ => zero_le_one)
    simpa only [Finset.sum_const, one_mul, mul_one, nsmul_eq_mul, ← Nat.cast_mul,
      Nat.cast_le] using h
  have hf : (V.image Sigma.fst).filter (fun g => |s g - a| ≤ L) = V.image Sigma.fst := by
    apply Finset.filter_eq_self.mpr
    intro g hg
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hg
    exact (Finset.mem_filter.mp hi).2
  have hband := card_metricBand_le_integerFloorBand_of_posSeparated s hd hsep L a
    (V.image Sigma.fst)
  rw [hf] at hband
  exact hmult.trans (Nat.mul_le_mul_left q hband)

/-- Uniform absolute exponential row ceiling for finite grouped sections. -/
theorem sum_grouped_exp_distance_le
    {κ : Type*} [DecidableEq κ] (size : κ → ℕ) {q : ℕ} (hsize : ∀ g, size g ≤ q)
    (s : κ → ℝ) {d c : ℝ} (hd : 0 < d) (hc : 0 < c)
    (hsep : ∀ g h, g ≠ h → d ≤ |s g - s h|)
    (a : ℝ) (U : Finset (Σ g, Fin (size g))) :
    (∑ i ∈ U, Real.exp (-c * |s i.1 - a|)) ≤
      (q : ℝ) * positiveSeparationExpRowConstant d c := by
  have hs := summable_exp_neg_abs_sub_of_finite_posSeparated s ∅ hd hc
    (fun i j _ _ hij => hsep i j hij) a
  have hb := tsum_exp_neg_abs_sub_le_of_finite_posSeparated s ∅ hd hc
    (fun i j _ _ hij => hsep i j hij) a
  simp only [Finset.card_empty, Nat.cast_zero, zero_add] at hb
  exact (sum_grouped_anchor_le size hsize U _ (fun _ => (Real.exp_pos _).le)).trans
    (mul_le_mul_of_nonneg_left ((hs.sum_le_tsum _ (fun _ _ => (Real.exp_pos _).le)).trans hb)
      (Nat.cast_nonneg q))

/-- The grouped exponential tails are uniformly small in the row center
and the finite section. The cutoff does not involve internal node gaps. -/
theorem exists_uniform_sum_grouped_exp_distance_tail
    {κ : Type*} [DecidableEq κ] (size : κ → ℕ) {q : ℕ} (hsize : ∀ g, size g ≤ q)
    (s : κ → ℝ) {d c : ℝ} (hd : 0 < d) (hc : 0 < c)
    (hsep : ∀ g h, g ≠ h → d ≤ |s g - s h|) :
    ∀ ε > 0, ∃ L ≥ 0, ∀ a : ℝ, ∀ U : Finset (Σ g, Fin (size g)),
      (∑ i ∈ U with L < |s i.1 - a|, Real.exp (-c * |s i.1 - a|)) ≤ ε := by
  intro ε hε
  obtain ⟨L, hL, htail⟩ := exists_uniform_sum_exp_neg_abs_tail_of_posSeparated s hd hc hsep
    (ε / ((q : ℝ) + 1)) (by positivity)
  refine ⟨L, hL, ?_⟩
  intro a U
  let V := U.filter (fun i => L < |s i.1 - a|)
  have hf : (V.image Sigma.fst).filter (fun g => L < |s g - a|) = V.image Sigma.fst := by
    apply Finset.filter_eq_self.mpr
    intro g hg
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hg
    exact (Finset.mem_filter.mp hi).2
  have ht := htail a (V.image Sigma.fst)
  rw [hf] at ht
  have hfrac : (q : ℝ) * (ε / ((q : ℝ) + 1)) ≤ ε := by
    have he : ((q : ℝ) + 1) * (ε / ((q : ℝ) + 1)) = ε := by field_simp
    nlinarith [div_pos hε (show (0 : ℝ) < q + 1 by positivity)]
  exact (sum_grouped_anchor_le size hsize V _ (fun _ => (Real.exp_pos _).le)).trans
    ((mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg q)).trans hfrac)

/-- Bounded anchor bands give actual finite central coordinate sets. -/
theorem finite_grouped_anchor_abs_le
    {κ : Type*} [DecidableEq κ] (size : κ → ℕ) {q : ℕ} (hsize : ∀ g, size g ≤ q)
    (s : κ → ℝ) {d : ℝ} (hd : 0 < d)
    (hsep : ∀ g h, g ≠ h → d ≤ |s g - s h|) (R : ℝ) :
    {i : Σ g, Fin (size g) | |s i.1| ≤ R}.Finite := by
  by_contra hinf
  let M := q * (Finset.Icc ⌊-(positiveSeparationScale d * R)⌋
    ⌊positiveSeparationScale d * R⌋).card
  obtain ⟨V, hV, hf, hcard⟩ := Set.Infinite.exists_subset_ncard_eq hinf (M + 1)
  have hfilter : hf.toFinset.filter (fun i => |s i.1 - 0| ≤ R) = hf.toFinset := by
    apply Finset.filter_eq_self.mpr
    intro i hi
    simpa only [sub_zero, Set.mem_ofPred_eq] using hV (Set.Finite.mem_toFinset hf |>.mp hi)
  have h := card_grouped_metricBand_le size hsize s hd hsep R 0 hf.toFinset
  rw [hfilter] at h
  have hcard' : hf.toFinset.card = M + 1 := by
    rwa [Set.ncard_eq_toFinset_card V hf] at hcard
  change hf.toFinset.card ≤ M at h
  omega

private theorem both_abs_large_of_band {u v T L : ℝ} (hL : 0 ≤ L)
    (hband : |v - u| ≤ L) (hout : ¬ (|u| ≤ T + L ∧ |v| ≤ T + L)) :
    T ≤ |u| ∧ T ≤ |v| := by
  have htri := abs_sub_abs_le_abs_sub v u
  have htri' := abs_sub_abs_le_abs_sub u v
  rw [abs_sub_comm u v] at htri'
  push Not at hout
  by_cases hu : |u| ≤ T + L
  · have hv := hout hu
    constructor <;> linarith
  · have hu' : T + L < |u| := lt_of_not_ge hu
    constructor <;> linarith

/-- Actual exponential localization and uniform near-band smallness imply
uniformly small Schur rows after removal of one finite central matrix block. -/
theorem exists_grouped_masked_row_bound
    {κ : Type*} [DecidableEq κ] (size : κ → ℕ) {q : ℕ} (hsize : ∀ g, size g ≤ q)
    (s : κ → ℝ) {d C c : ℝ} (hd : 0 < d) (hC : 0 < C) (hc : 0 < c)
    (hsep : ∀ g h, g ≠ h → d ≤ |s g - s h|)
    (K : (Σ g, Fin (size g)) → (Σ g, Fin (size g)) → ℂ)
    (hdec : ∀ i j, ‖K i j‖ ≤ C * Real.exp (-c * |s j.1 - s i.1|))
    (hnear : ∀ L ≥ 0, ∀ δ > 0, ∃ T ≥ 0, ∀ i j,
      T ≤ |s i.1| → T ≤ |s j.1| → |s j.1 - s i.1| ≤ L → ‖K i j‖ ≤ δ) :
    ∀ ε > 0, ∃ E : Finset (Σ g, Fin (size g)),
      ∀ U : Finset (Σ g, Fin (size g)), ∀ i,
        (∑ j ∈ U, ‖if i ∈ E ∧ j ∈ E then (0 : ℂ) else K i j‖) ≤ ε := by
  intro ε hε
  obtain ⟨L, hL, hfar⟩ := exists_uniform_sum_grouped_exp_distance_tail size hsize s hd hc hsep
    (ε / (2 * C)) (by positivity)
  let N := q * (Finset.Icc ⌊-(positiveSeparationScale d * L)⌋
    ⌊positiveSeparationScale d * L⌋).card
  let δ := ε / (2 * ((N : ℝ) + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨T, _hT, hsmall⟩ := hnear L hL δ hδ
  let E := (finite_grouped_anchor_abs_le size hsize s hd hsep (T + L)).toFinset
  have hE (i : Σ g, Fin (size g)) : i ∈ E ↔ |s i.1| ≤ T + L := Set.Finite.mem_toFinset _
  refine ⟨E, ?_⟩
  intro U i
  let near := U.filter (fun j => |s j.1 - s i.1| ≤ L)
  let far := U.filter (fun j => ¬ |s j.1 - s i.1| ≤ L)
  have hcard : near.card ≤ N := card_grouped_metricBand_le size hsize s hd hsep L (s i.1) U
  have hnpoint (j : Σ g, Fin (size g)) (hj : j ∈ near) :
      ‖if i ∈ E ∧ j ∈ E then (0 : ℂ) else K i j‖ ≤ δ := by
    have hband := (Finset.mem_filter.mp hj).2
    by_cases hcentral : i ∈ E ∧ j ∈ E
    · simpa only [ite_eq_left hcentral, norm_zero] using hδ.le
    · have hout : ¬ (|s i.1| ≤ T + L ∧ |s j.1| ≤ T + L) := by
        simpa only [hE] using hcentral
      obtain ⟨hiT, hjT⟩ := both_abs_large_of_band hL hband hout
      simpa only [ite_eq_right hcentral] using hsmall i j hiT hjT hband
  have hnearSum : (∑ j ∈ near, ‖if i ∈ E ∧ j ∈ E then (0 : ℂ) else K i j‖) ≤ ε / 2 := by
    have hcardR : (near.card : ℝ) ≤ N := by exact_mod_cast hcard
    have hfrac : (N : ℝ) * δ ≤ ε / 2 := by
      have he : ((N : ℝ) + 1) * δ = ε / 2 := by dsimp [δ]; field_simp
      nlinarith
    calc
      _ ≤ ∑ _j ∈ near, δ := Finset.sum_le_sum hnpoint
      _ = (near.card : ℝ) * δ := by simp
      _ ≤ (N : ℝ) * δ := mul_le_mul_of_nonneg_right hcardR hδ.le
      _ ≤ ε / 2 := hfrac
  have hfarSum : (∑ j ∈ far, ‖if i ∈ E ∧ j ∈ E then (0 : ℂ) else K i j‖) ≤ ε / 2 := by
    have hbound := hfar (s i.1) U
    have hm : C * (ε / (2 * C)) = ε / 2 := by field_simp
    calc
      _ ≤ ∑ j ∈ far, C * Real.exp (-c * |s j.1 - s i.1|) := by
        apply Finset.sum_le_sum
        intro j hj
        by_cases hcentral : i ∈ E ∧ j ∈ E
        · simp only [ite_eq_left hcentral, norm_zero]
          positivity
        · simpa only [ite_eq_right hcentral] using hdec i j
      _ = C * ∑ j ∈ far, Real.exp (-c * |s j.1 - s i.1|) := (Finset.mul_sum _ _ _).symm
      _ ≤ C * (ε / (2 * C)) := mul_le_mul_of_nonneg_left (by simpa only [far, not_le] using hbound) hC.le
      _ = ε / 2 := hm
  have heq := Finset.sum_filter_add_sum_filter_not U (fun j => |s j.1 - s i.1| ≤ L)
    (fun j => ‖if i ∈ E ∧ j ∈ E then (0 : ℂ) else K i j‖)
  change (∑ j ∈ near, _) + (∑ j ∈ far, _) = _ at heq
  rw [← heq]
  linarith

/-- A genuine self-adjoint coefficient operator with these actual entries
is compact. Finite central blocks and their norm approximation are constructed
from the separated anchors, rather than included as an assumption. -/
theorem isCompactOperator_of_grouped_exponential_and_band_smallness
    {κ : Type*} [DecidableEq κ] (size : κ → ℕ) {q : ℕ} (hsize : ∀ g, size g ≤ q)
    (s : κ → ℝ) {d C c : ℝ} (hd : 0 < d) (hC : 0 < C) (hc : 0 < c)
    (hsep : ∀ g h, g ≠ h → d ≤ |s g - s h|)
    (K : (Σ g, Fin (size g)) → (Σ g, Fin (size g)) → ℂ)
    (hdec : ∀ i j, ‖K i j‖ ≤ C * Real.exp (-c * |s j.1 - s i.1|))
    (hnear : ∀ L ≥ 0, ∀ δ > 0, ∃ T ≥ 0, ∀ i j,
      T ≤ |s i.1| → T ≤ |s j.1| → |s j.1 - s i.1| ≤ L → ‖K i j‖ ≤ δ)
    (A : CoefficientSpace (Σ g, Fin (size g)) →L[ℂ] CoefficientSpace (Σ g, Fin (size g)))
    (hA : IsSelfAdjoint A)
    (hentry : ∀ i j, inner ℂ (coefficientAtom i) (A (coefficientAtom j)) = K i j) :
    IsCompactOperator A := by
  let R : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hR : ∀ n, 0 ≤ R n := by intro n; dsimp [R]; positivity
  have hR0 : Tendsto R atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hex (n : ℕ) := exists_grouped_masked_row_bound size hsize s hd hC hc hsep K hdec hnear
    (R n) (by dsimp [R]; positivity)
  choose E hE using hex
  apply isCompactOperator_of_finite_compression_schur A hA E R hR hR0
  intro n U i hi
  have h := hE n U i
  convert h using 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [sub_apply, inner_sub_right, finiteCoordinateCompression_entry, hentry]
  split_ifs <;> simp

/-- An actual Hermitian grouped kernel with exponential localization and
near-band decay constructs a compact self-adjoint operator. Existence,
boundedness, exact entries and compactness are all conclusions. -/
theorem exists_compact_grouped_coefficientOperator
    {κ : Type*} [DecidableEq κ] (size : κ → ℕ) {q : ℕ} (hsize : ∀ g, size g ≤ q)
    (s : κ → ℝ) {d C c : ℝ} (hd : 0 < d) (hC : 0 < C) (hc : 0 < c)
    (hsep : ∀ g h, g ≠ h → d ≤ |s g - s h|)
    (K : (Σ g, Fin (size g)) → (Σ g, Fin (size g)) → ℂ)
    (hherm : ∀ i j, starRingEnd ℂ (K j i) = K i j)
    (hdec : ∀ i j, ‖K i j‖ ≤ C * Real.exp (-c * |s j.1 - s i.1|))
    (hnear : ∀ L ≥ 0, ∀ δ > 0, ∃ T ≥ 0, ∀ i j,
      T ≤ |s i.1| → T ≤ |s j.1| → |s j.1 - s i.1| ≤ L → ‖K i j‖ ≤ δ) :
    ∃ A : CoefficientSpace (Σ g, Fin (size g)) →L[ℂ] CoefficientSpace (Σ g, Fin (size g)),
      IsSelfAdjoint A ∧ IsCompactOperator A ∧
        ‖A‖ ≤ C * (q : ℝ) * positiveSeparationExpRowConstant d c ∧
        ∀ i j, inner ℂ (coefficientAtom i) (A (coefficientAtom j)) = K i j := by
  have hR : 0 ≤ C * (q : ℝ) * positiveSeparationExpRowConstant d c :=
    mul_nonneg (mul_nonneg hC.le (Nat.cast_nonneg q)) (positiveSeparationExpRowConstant_nonneg d c)
  have hrow (U : Finset (Σ g, Fin (size g))) (i : Σ g, Fin (size g)) :
      (∑ j ∈ U, ‖K i j‖) ≤ C * (q : ℝ) * positiveSeparationExpRowConstant d c := by
    calc
      _ ≤ ∑ j ∈ U, C * Real.exp (-c * |s j.1 - s i.1|) :=
        Finset.sum_le_sum (fun j hj => hdec i j)
      _ = C * ∑ j ∈ U, Real.exp (-c * |s j.1 - s i.1|) := (Finset.mul_sum _ _ _).symm
      _ ≤ C * ((q : ℝ) * positiveSeparationExpRowConstant d c) :=
        mul_le_mul_of_nonneg_left (sum_grouped_exp_distance_le size hsize s hd hc hsep (s i.1) U) hC.le
      _ = _ := by ring
  obtain ⟨A, hA, hnorm, hentry⟩ := exists_selfAdjoint_coefficientOperator_of_schur K hR hherm hrow
  exact ⟨A, hA, isCompactOperator_of_grouped_exponential_and_band_smallness
    size hsize s hd hC hc hsep K hdec hnear A hA hentry, hnorm, hentry⟩

end

end MeyerGeneralProblem
