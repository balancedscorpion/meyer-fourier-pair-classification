module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.MeasureTheory.Group.AddCircle
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

@[expose] public section

/-!
# Circle phase averages for lattice-slab counting

Geometric character sums give the Fourier moments of the empirical box
measures. Density of Fourier polynomials and the null frontier of closed
arcs give their exact limiting frequencies. The count of integers in a
closed interval is its integer length plus one such arc indicator.
-/

namespace MeyerGeneralProblem

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Classical ENNReal Topology

/-- The Fourier character average in one integer box direction has a
bound independent of the translation of that box. -/
private theorem norm_normalized_geometric_sum_le_of_unit_norm
    (z c : ℂ) (hz : ‖z‖ = 1) (hc : ‖c‖ = 1) (hne : z ≠ 1) (n : ℕ) :
    ‖(∑ k ∈ Finset.range n, c * z ^ k) / (n : ℂ)‖ ≤ (2 / ‖z - 1‖) / (n : ℝ) := by
  have hnorm : ‖z - 1‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne)
  let S := ∑ k ∈ Finset.range n, z ^ k
  have hS : S * (z - 1) = z ^ n - 1 := geom_sum_mul z n
  have hBound : ‖S‖ ≤ 2 / ‖z - 1‖ := by
    calc
      ‖S‖ = ‖S * (z - 1)‖ / ‖z - 1‖ := by rw [norm_mul, mul_div_cancel_right₀ _ hnorm]
      _ = ‖z ^ n - 1‖ / ‖z - 1‖ := by rw [hS]
      _ ≤ 2 / ‖z - 1‖ := by
        apply div_le_div_of_nonneg_right _ (norm_nonneg _)
        exact (norm_sub_le _ _).trans_eq (by rw [norm_pow, hz, one_pow, norm_one]; norm_num)
  rw [← Finset.mul_sum, norm_div, norm_mul, hc, one_mul, Complex.norm_natCast]
  exact div_le_div_of_nonneg_right hBound (Nat.cast_nonneg _)

private theorem norm_geometric_mean_le_one (z : ℂ) (hz : ‖z‖ = 1) (n : ℕ) :
    ‖(∑ f : Fin (n + 1), z ^ (f : ℕ)) / (n + 1 : ℕ)‖ ≤ 1 := by
  have hBound : ‖∑ f : Fin (n + 1), z ^ (f : ℕ)‖ ≤ (n + 1 : ℕ) := by
    refine (norm_sum_le _ _).trans_eq ?_
    simp [norm_pow, hz]
  rw [norm_div, Complex.norm_natCast, div_le_iff₀ (by positivity)]
  simpa using hBound

/-- A box average factors into one-dimensional geometric means.
One nontrivial direction therefore makes the full character average
vanish uniformly over its starting phase. -/
theorem tendsto_normalized_box_geometric_mean
    {d : Type*} [Fintype d] [DecidableEq d] (z : d → ℂ) (hz : ∀ i, ‖z i‖ = 1)
    (c : ℕ → ℂ) (hc : ∀ n, ‖c n‖ = 1) (i : d) (hne : z i ≠ 1) :
    Tendsto (fun n : ℕ =>
      (∑ f : d → Fin (n + 1), c n * ∏ j, z j ^ (f j : ℕ)) /
        (↑(n + 1 : ℕ) : ℂ) ^ Fintype.card d) atTop (𝓝 0) := by
  classical
  let g (j : d) (n : ℕ) := (∑ f : Fin (n + 1), z j ^ (f : ℕ)) / (n + 1 : ℕ)
  have hEq (n : ℕ) :
      (∑ f : d → Fin (n + 1), c n * ∏ j, z j ^ (f j : ℕ)) /
        (↑(n + 1 : ℕ) : ℂ) ^ Fintype.card d = c n * ∏ j, g j n := by
    rw [← Finset.mul_sum, ← Fintype.prod_sum (fun (j : d) (k : Fin (n + 1)) => z j ^ (k : ℕ)), mul_div_assoc]
    congr 1
    simp [g, Finset.prod_div_distrib]
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hLimit : Tendsto (fun n : ℕ => (2 / ‖z i - 1‖) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  apply squeeze_zero (fun _ => norm_nonneg _) _ hLimit
  intro n
  rw [hEq, norm_mul, hc, one_mul, norm_prod]
  have hMean : ‖g i n‖ ≤ (2 / ‖z i - 1‖) / ((n + 1 : ℕ) : ℝ) := by
    let f (m : ℕ) := z i ^ m
    change ‖(∑ j : Fin (n + 1), f (j : ℕ)) / (n + 1 : ℕ)‖ ≤ _
    rw [Fin.sum_univ_eq_sum_range]
    simpa only [one_mul] using
      norm_normalized_geometric_sum_le_of_unit_norm (z i) 1 (hz i) norm_one hne (n + 1)
  calc
    _ ≤ ∏ j, if j = i then (2 / ‖z i - 1‖) / ((n + 1 : ℕ) : ℝ) else 1 := by
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro j _
      by_cases he : j = i
      · subst j
        rw [ite_eq_left rfl]
        exact hMean
      · rw [ite_eq_right he]
        exact norm_geometric_mean_le_one (z j) (hz j) n
    _ = _ := by simp

private theorem fourier_add_arg (m : ℤ) (x y : UnitAddCircle) :
    fourier m (x + y) = fourier m x * fourier m y := by
  simp only [fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul]

private theorem fourier_nsmul_arg (m : ℤ) (x : UnitAddCircle) (n : ℕ) :
    fourier m (n • x) = (fourier m x) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, fourier_add_arg, ih, pow_succ]

private theorem fourier_sum_arg {d : Type*} (m : ℤ) (a : d → UnitAddCircle) (s : Finset d) :
    fourier m (∑ j ∈ s, a j) = ∏ j ∈ s, fourier m (a j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, fourier_add_arg, ih]

/-- Each nonzero Fourier mode that detects a box direction has zero
limiting average over the actual phases of expanding integer boxes. -/
theorem tendsto_fourier_box_phase_mean
    {d : Type*} [Fintype d] [DecidableEq d]
    (a : d → UnitAddCircle) (c : ℕ → UnitAddCircle) (m : ℤ)
    (i : d) (hi : fourier m (a i) ≠ 1) :
    Tendsto (fun n : ℕ => (∑ f : d → Fin (n + 1),
      fourier m (c n + ∑ j, (f j : ℕ) • a j)) /
        (↑(n + 1 : ℕ) : ℂ) ^ Fintype.card d) atTop (𝓝 0) := by
  have hNorm (θ : UnitAddCircle) : ‖fourier m θ‖ = 1 := Circle.norm_coe _
  simpa only [fourier_add_arg, fourier_sum_arg, fourier_nsmul_arg] using
    tendsto_normalized_box_geometric_mean (fun j => fourier m (a j)) (fun j => hNorm (a j))
      (fun n => fourier m (c n)) (fun n => hNorm (c n)) i hi

/-- The number of integers in a closed interval, including both endpoints. -/
def closedIntegerIntervalCount (a b : ℝ) : ℕ :=
  (Finset.Icc ⌈a⌉ ⌊b⌋).card

private theorem ceil_eq_add_fract_neg (a : ℝ) :
    (⌈a⌉ : ℝ) = a + Int.fract (-a) := by
  have he : ⌈a⌉ = -⌊-a⌋ := by simpa only [neg_neg] using (Int.ceil_neg (a := -a))
  rw [he, Int.cast_neg, Int.fract]
  ring

private theorem fract_le_iff_mem_closedBall_unitCircle (x r : ℝ) (hr₁ : r < 1) :
    Int.fract x ≤ r ↔ (x : UnitAddCircle) ∈ closedBall ((r / 2 : ℝ) : UnitAddCircle) (r / 2) := by
  change Int.fract x ≤ r ↔ x ∈ (fun y : ℝ => (y : UnitAddCircle)) ⁻¹'
    closedBall ((r / 2 : ℝ) : UnitAddCircle) (r / 2)
  rw [AddCircle.coe_real_preimage_closedBall_eq_iUnion 1]
  simp only [Set.mem_iUnion, Real.closedBall_eq_Icc, zsmul_eq_mul, mul_one, Set.mem_Icc]
  constructor
  · intro hx
    refine ⟨⌊x⌋, ?_, ?_⟩
    · linarith [Int.floor_le x]
    · change x - (⌊x⌋ : ℝ) ≤ r at hx
      linarith
  · rintro ⟨z, hzlo, hzhi⟩
    have hz : ⌊x⌋ = z := Int.floor_eq_iff.mpr ⟨by linarith, by linarith⟩
    rw [Int.fract, hz]
    linarith

/-- The integer count is its integer length plus the indicator of one
closed arc, whose length is the fractional part of the interval length. -/
theorem closedIntegerIntervalCount_eq_floor_add_arc (a ℓ : ℝ) (hℓ : 0 ≤ ℓ) :
    closedIntegerIntervalCount a (a + ℓ) =
      ⌊ℓ⌋.toNat + (if ((-a : ℝ) : UnitAddCircle) ∈
        closedBall (((Int.fract ℓ / 2 : ℝ) : UnitAddCircle)) (Int.fract ℓ / 2) then 1 else 0) := by
  classical
  rw [← fract_le_iff_mem_closedBall_unitCircle (-a) _ (Int.fract_lt_one ℓ)]
  have hce := ceil_eq_add_fract_neg a
  have hf₀ := Int.fract_nonneg (-a)
  have hf₁ := Int.fract_lt_one (-a)
  have hr₀ := Int.fract_nonneg ℓ
  have hr₁ := Int.fract_lt_one ℓ
  have hℓeq : ℓ = (⌊ℓ⌋ : ℝ) + Int.fract ℓ := by
    change ℓ = (⌊ℓ⌋ : ℝ) + (ℓ - (⌊ℓ⌋ : ℝ))
    ring
  have hN : 0 ≤ ⌊ℓ⌋ := Int.floor_nonneg.mpr hℓ
  rw [closedIntegerIntervalCount, Int.card_Icc]
  split_ifs with h
  · have he : ⌊a + ℓ⌋ = ⌈a⌉ + ⌊ℓ⌋ := by
      apply Int.floor_eq_iff.mpr
      push_cast
      constructor <;> linarith
    rw [he]
    omega
  · have he : ⌊a + ℓ⌋ = ⌈a⌉ + ⌊ℓ⌋ - 1 := by
      apply Int.floor_eq_iff.mpr
      push_cast
      have h' := lt_of_not_ge h
      constructor <;> linarith
    rw [he]
    omega

/-- Equal mass at every index of a finite family, retaining multiplicity
when several indices give the same point. -/
private def finiteEmpiricalProbability {ι X : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace X]
    (a : ι → X) : ProbabilityMeasure X := by
  let μ := (Fintype.card ι : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (a i)
  refine ⟨μ, ⟨?_⟩⟩
  have hcard : (Fintype.card ι : ℝ≥0∞) ≠ 0 := by simp [Fintype.card_ne_zero]
  simp [μ, Measure.smul_apply, Measure.finsetSum_apply, ENNReal.inv_mul_cancel, hcard]

private theorem integral_finiteEmpiricalProbability
    {ι X : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace X] [MeasurableSingletonClass X]
    (a : ι → X) (g : X → ℂ) :
    (∫ x, g x ∂(finiteEmpiricalProbability a : Measure X)) =
      (∑ j, g (a j)) / (Fintype.card ι : ℂ) := by
  change (∫ x, g x ∂((Fintype.card ι : ℝ≥0∞)⁻¹ • ∑ j, Measure.dirac (a j))) = _
  rw [integral_smul_measure, integral_finsetSum_measure]
  · simp [ENNReal.toReal_inv, Complex.real_smul, div_eq_mul_inv, mul_comm]
  · exact fun j _ => integrable_dirac enorm_lt_top

private theorem real_finiteEmpiricalProbability
    {ι X : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace X]
    (a : ι → X) (s : Set X) (hs : MeasurableSet s) :
    ((finiteEmpiricalProbability a : Measure X) s).toReal =
      ((Finset.univ.filter fun i => a i ∈ s).card : ℝ) / (Fintype.card ι : ℝ) := by
  classical
  change (((Fintype.card ι : ℝ≥0∞)⁻¹ • ∑ j, Measure.dirac (a j)) s).toReal = _
  have hsum : (∑ j : ι, (if a j ∈ s then (1 : ℝ≥0∞) else 0)) =
      ((Finset.univ.filter fun i => a i ∈ s).card : ℝ≥0∞) := by
    rw [Finset.card_filter, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp
  simp only [Measure.smul_apply, smul_eq_mul, Measure.finsetSum_apply, Measure.dirac_apply' _ hs, Set.indicator_apply, Pi.one_apply, hsum,
    ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, div_eq_mul_inv, mul_comm]

private theorem integral_circle_probability_le_norm (μ : ProbabilityMeasure UnitAddCircle)
    (f : C(UnitAddCircle, ℂ)) : ‖∫ x, f x ∂(μ : Measure UnitAddCircle)‖ ≤ ‖f‖ := by
  have h := norm_integral_le_of_norm_le_const (μ := (μ : Measure UnitAddCircle))
    (C := ‖f‖) (Eventually.of_forall f.norm_coe_le_norm)
  simpa using h

/-- On the unit circle, convergence of every Fourier moment implies
weak convergence of the probability measures. -/
private theorem tendsto_probabilityMeasure_of_fourier_moments
    (μ : ℕ → ProbabilityMeasure UnitAddCircle) (ν : ProbabilityMeasure UnitAddCircle)
    (h : ∀ m : ℤ, Tendsto (fun n => ∫ x, fourier m x ∂(μ n : Measure UnitAddCircle)) atTop
      (𝓝 (∫ x, fourier m x ∂(ν : Measure UnitAddCircle)))) :
    Tendsto μ atTop (𝓝 ν) := by
  have hInt (f : C(UnitAddCircle, ℂ)) (ρ : ProbabilityMeasure UnitAddCircle) :
      Integrable f (ρ : Measure UnitAddCircle) := f.continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace f)
  let U : Submodule ℂ C(UnitAddCircle, ℂ) := {
    carrier := {f | Tendsto (fun n => ∫ x, f x ∂(μ n : Measure UnitAddCircle)) atTop
      (𝓝 (∫ x, f x ∂(ν : Measure UnitAddCircle)))}
    zero_mem' := by simp
    add_mem' := by
      intro f g hf hg
      have hf' := hf
      change Tendsto _ _ _ at hf' hg
      simpa only [Set.mem_ofPred_eq, ContinuousMap.add_apply, integral_add (hInt _ _) (hInt _ _)]
        using hf'.add hg
    smul_mem' := by
      intro a f hf
      change Tendsto _ _ _ at hf
      simpa only [Set.mem_ofPred_eq, ContinuousMap.smul_apply, integral_smul] using hf.const_smul a
  }
  have hU : Submodule.span ℂ (range (@fourier 1)) ≤ U :=
    Submodule.span_le.mpr (by rintro _ ⟨m, rfl⟩; exact h m)
  let V := Submodule.span ℂ (range (@fourier 1))
  have hd : V.topologicalClosure = ⊤ := span_fourier_closure_eq_top
  apply (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mpr
  intro f
  let g : C(UnitAddCircle, ℂ) := f.toContinuousMap
  change Tendsto (fun n => ∫ x, g x ∂(μ n : Measure UnitAddCircle)) atTop
    (𝓝 (∫ x, g x ∂(ν : Measure UnitAddCircle)))
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hClos : g ∈ closure (V : Set C(UnitAddCircle, ℂ)) := by
    change g ∈ V.topologicalClosure
    rw [hd]
    exact Submodule.mem_top
  obtain ⟨p, hp, hpdist⟩ := Metric.mem_closure_iff.mp hClos (ε / 4) (by positivity)
  have hdist : ‖g - p‖ < ε / 4 := by
    simpa only [dist_eq_norm, norm_sub_rev] using hpdist
  have hpU : Tendsto (fun n => ∫ x, p x ∂(μ n : Measure UnitAddCircle)) atTop
      (𝓝 (∫ x, p x ∂(ν : Measure UnitAddCircle))) := hU hp
  have hpNear := Metric.tendsto_nhds.mp hpU (ε / 2) (by positivity)
  filter_upwards [hpNear] with n hn
  let I (ρ : ProbabilityMeasure UnitAddCircle) (u : C(UnitAddCircle, ℂ)) := ∫ x, u x ∂(ρ : Measure UnitAddCircle)
  have hDiff (ρ : ProbabilityMeasure UnitAddCircle) : dist (I ρ g) (I ρ p) ≤ ‖g - p‖ := by
    rw [dist_eq_norm]
    have hh := integral_circle_probability_le_norm ρ (g - p)
    simpa only [ContinuousMap.sub_apply, integral_sub (hInt _ _) (hInt _ _)] using hh
  have hdistn : dist (I (μ n) p) (I ν p) < ε / 2 := hn
  change dist (I (μ n) g) (I ν g) < ε
  calc
    _ ≤ dist (I (μ n) g) (I (μ n) p) +
        (dist (I (μ n) p) (I ν p) + dist (I ν p) (I ν g)) :=
      (dist_triangle _ _ _).trans (add_le_add le_rfl (dist_triangle _ _ _))
    _ < ε := by
      rw [dist_comm (I ν p) (I ν g)]
      linarith [hDiff (μ n), hDiff ν]

private def unitCircleHaarProbability : ProbabilityMeasure UnitAddCircle :=
  ⟨AddCircle.haarAddCircle, inferInstance⟩

private theorem unitCircle_volume_eq_haar :
    (volume : Measure UnitAddCircle) = AddCircle.haarAddCircle := by
  simpa only [ENNReal.ofReal_one, one_smul] using (AddCircle.volume_eq_smul_haarAddCircle (T := 1))

private theorem unitCircle_haar_fourier (m : ℤ) :
    (∫ θ, fourier m θ ∂(unitCircleHaarProbability : Measure UnitAddCircle)) =
      if m = 0 then 1 else 0 := by
  change (∫ θ : UnitAddCircle, fourier m θ ∂AddCircle.haarAddCircle) = _
  have hc := congrFun (fourierCoeff_fourier (T := 1) m) (0 : ℤ)
  simpa only [fourierCoeff, neg_zero, fourier_zero, one_smul, Pi.single_apply, eq_comm] using hc

private theorem tendsto_finiteEmpiricalProbability_box_phases
    {d : Type*} [Fintype d] [DecidableEq d]
    (a : d → UnitAddCircle) (c : ℕ → UnitAddCircle)
    (ha : ∀ m : ℤ, m ≠ 0 → ∃ i, fourier m (a i) ≠ 1) :
    Tendsto (fun n : ℕ => finiteEmpiricalProbability
      (fun f : d → Fin (n + 1) => c n + ∑ j, (f j : ℕ) • a j)) atTop (𝓝 unitCircleHaarProbability) := by
  apply tendsto_probabilityMeasure_of_fourier_moments
  intro m
  simp only [integral_finiteEmpiricalProbability, Fintype.card_fun, Fintype.card_fin,
    Nat.cast_pow, unitCircle_haar_fourier]
  by_cases hm : m = 0
  · subst m
    simp only [fourier_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_pow, mul_one]
    have hn : ∀ n : ℕ, ((↑(n + 1 : ℕ) : ℂ) ^ Fintype.card d) ≠ 0 := by
      intro n
      exact pow_ne_zero _ (by exact_mod_cast Nat.succ_ne_zero n)
    simp only [div_self (hn _)]
    exact tendsto_const_nhds
  · obtain ⟨i, hi⟩ := ha m hm
    rw [ite_eq_right hm]
    exact tendsto_fourier_box_phase_mean a c m i hi

private theorem unitCircle_haar_frontier_closedBall (x : UnitAddCircle) (r : ℝ) :
    (unitCircleHaarProbability : Measure UnitAddCircle) (frontier (closedBall x r)) = 0 := by
  change AddCircle.haarAddCircle (frontier (closedBall x r)) = 0
  rw [← unitCircle_volume_eq_haar]
  have hsub : frontier (closedBall x r) ⊆ closedBall x r \ ball x r := by
    rw [isClosed_closedBall.frontier_eq]
    exact sdiff_subset_sdiff_right (interior_maximal ball_subset_closedBall isOpen_ball)
  have heq : volume (closedBall x r) = volume (ball x r) :=
    measure_congr AddCircle.closedBall_ae_eq_ball
  have hfin : volume (ball x r) ≠ ∞ := by
    rw [unitCircle_volume_eq_haar]
    exact measure_ne_top _ _
  exact le_antisymm ((measure_mono hsub).trans_eq (by
    rw [measure_sdiff ball_subset_closedBall measurableSet_ball.nullMeasurableSet hfin, heq, tsub_self]))
    bot_le

private theorem tendsto_closedBall_frequency_of_box_phases
    {d : Type*} [Fintype d] [DecidableEq d]
    (a : d → UnitAddCircle) (c : ℕ → UnitAddCircle)
    (ha : ∀ m : ℤ, m ≠ 0 → ∃ i, fourier m (a i) ≠ 1)
    (x : UnitAddCircle) (r : ℝ) (hr : 0 ≤ r) (hr' : 2 * r ≤ 1) :
    Tendsto (fun n : ℕ =>
      ((Finset.univ.filter (fun f : d → Fin (n + 1) =>
        c n + ∑ j, (f j : ℕ) • a j ∈ closedBall x r)).card : ℝ) /
          (↑(n + 1 : ℕ) : ℝ) ^ Fintype.card d) atTop (𝓝 (2 * r)) := by
  let s := closedBall x r
  let μ n := finiteEmpiricalProbability (fun f : d → Fin (n + 1) => c n + ∑ j, (f j : ℕ) • a j)
  have hμ : Tendsto μ atTop (𝓝 unitCircleHaarProbability) :=
    tendsto_finiteEmpiricalProbability_box_phases a c ha
  have h := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hμ
    (E := s) (unitCircle_haar_frontier_closedBall x r)
  have hreal := (ENNReal.continuousAt_toReal
    (measure_ne_top (unitCircleHaarProbability : Measure UnitAddCircle) s)).tendsto.comp h
  have hval : ((unitCircleHaarProbability : Measure UnitAddCircle) s).toReal = 2 * r := by
    change (AddCircle.haarAddCircle (closedBall x r)).toReal = 2 * r
    rw [← unitCircle_volume_eq_haar, AddCircle.volume_closedBall 1, min_eq_right hr']
    exact ENNReal.toReal_ofReal (by positivity)
  rw [hval] at hreal
  change Tendsto (fun n => ((μ n : Measure UnitAddCircle) s).toReal) atTop (𝓝 (2 * r)) at hreal
  simpa only [μ, real_finiteEmpiricalProbability _ s isClosed_closedBall.measurableSet,
    Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, s] using hreal

/-- The closed integer count has its exact mean for phase boxes, with
closed endpoints included in both the count and its residual arc. -/
theorem tendsto_closedIntegerIntervalCount_box_mean
    {d : Type*} [Fintype d] [DecidableEq d]
    (a : d → UnitAddCircle) (c : ℕ → UnitAddCircle)
    (ha : ∀ m : ℤ, m ≠ 0 → ∃ i, fourier m (a i) ≠ 1)
    (v : (n : ℕ) → (d → Fin (n + 1)) → ℝ)
    (hPhase : ∀ n f, ((-v n f : ℝ) : UnitAddCircle) = c n + ∑ j, (f j : ℕ) • a j)
    (ℓ : ℝ) (hℓ : 0 ≤ ℓ) :
    Tendsto (fun n : ℕ => ((∑ f : d → Fin (n + 1),
      closedIntegerIntervalCount (v n f) (v n f + ℓ)) : ℝ) /
          (↑(n + 1 : ℕ) : ℝ) ^ Fintype.card d) atTop (𝓝 ℓ) := by
  let x : UnitAddCircle := ((Int.fract ℓ / 2 : ℝ) : UnitAddCircle)
  let r := Int.fract ℓ / 2
  have hr : 0 ≤ r := div_nonneg (Int.fract_nonneg _) (by norm_num)
  have hr' : 2 * r ≤ 1 := by dsimp [r]; linarith [Int.fract_lt_one ℓ]
  have h := tendsto_closedBall_frequency_of_box_phases a c ha x r hr hr'
  have hFloor : 0 ≤ ⌊ℓ⌋ := Int.floor_nonneg.mpr hℓ
  have hℓeq : (⌊ℓ⌋.toNat : ℝ) + 2 * r = ℓ := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hFloor]
    change (⌊ℓ⌋ : ℝ) + 2 * ((ℓ - (⌊ℓ⌋ : ℝ)) / 2) = ℓ
    ring
  have hconst : Tendsto (fun _ : ℕ => (⌊ℓ⌋.toNat : ℝ)) atTop (𝓝 (⌊ℓ⌋.toNat : ℝ)) :=
    tendsto_const_nhds
  have hlim := hconst.add h
  rw [hℓeq] at hlim
  apply hlim.congr
  intro n
  let M := n + 1
  let P (f : d → Fin M) : Prop := c n + ∑ j, (f j : ℕ) • a j ∈ closedBall x r
  have hsum :
      (∑ f : d → Fin M, closedIntegerIntervalCount (v n f) (v n f + ℓ)) =
        M ^ Fintype.card d * ⌊ℓ⌋.toNat + (Finset.univ.filter P).card := by
    have hf (f : d → Fin M) : closedIntegerIntervalCount (v n f) (v n f + ℓ) =
        ⌊ℓ⌋.toNat + (if P f then 1 else 0) := by
      rw [closedIntegerIntervalCount_eq_floor_add_arc (ℓ := ℓ) _ hℓ, hPhase]
    simp_rw [hf]
    rw [Finset.sum_add_distrib, ← Finset.card_filter P, Finset.sum_const, Finset.card_univ,
      Fintype.card_fun, Fintype.card_fin]
    rfl
  change (⌊ℓ⌋.toNat : ℝ) + ((Finset.univ.filter P).card : ℝ) / (M : ℝ) ^ Fintype.card d =
    ((∑ f : d → Fin M, closedIntegerIntervalCount (v n f) (v n f + ℓ)) : ℝ) / (M : ℝ) ^ Fintype.card d
  rw [← Nat.cast_sum, hsum]
  push_cast
  have hM : (M : ℝ) ^ Fintype.card d ≠ 0 := pow_ne_zero _ (by exact_mod_cast Nat.succ_ne_zero n)
  field_simp [hM]

end
end MeyerGeneralProblem
