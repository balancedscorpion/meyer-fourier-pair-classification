module

public import MeyerGeneralProblem.Gram.GroupedHigherMixedBounds

@[expose] public section

/-!
# Higher derivatives of the actual Hermite normalizer

The positive diagonal is differentiated through its exact Laplace moments.
Faà di Bruno for scalar powers retains the sum of partition block sizes,
and hence the full inverse signed-square power in every derivative.
Both the norm and its reciprocal are the actual same-order Dirac norms.
No differentiated asymptotic remainder is asserted.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter
open scoped Topology

/-- The exact all-order diagonal estimate's numerical factor. -/
def groupedDiagonalDerivativeConstant (m i : ℕ) : ℝ :=
  groupedHermiteDiagonalRatioConstant m * (2:ℝ)^i * (i.factorial:ℝ)

theorem groupedDiagonalDerivativeConstant_pos (m : ℕ) (hm : 1 ≤ m) (i : ℕ) :
    0 < groupedDiagonalDerivativeConstant m i := by
  unfold groupedDiagonalDerivativeConstant
  have := groupedHermiteDiagonalRatioConstant_pos m hm
  positivity

theorem grouped_orderedFinpartition_sum_partSize {i : ℕ} (c : OrderedFinpartition i) :
    ∑ r, c.partSize r = i := by
  simpa using Fintype.card_congr c.equivSigma

theorem contDiff_groupedHermiteDiagonalMoment_zero (m : ℕ) (hm : 1 ≤ m) (q : ℕ) :
    ContDiff ℝ q (groupedHermiteDiagonalMoment m 0) := by
  apply contDiff_nat_iff_iteratedDeriv.mpr
  constructor
  · intro i hi
    rw [iteratedDeriv_groupedHermiteDiagonalMoment m hm]
    exact Differentiable.continuous (fun s =>
      (hasDerivAt_groupedHermiteDiagonalMoment m hm i s).differentiableAt)
  · intro i hi
    rw [iteratedDeriv_groupedHermiteDiagonalMoment m hm]
    exact fun s => (hasDerivAt_groupedHermiteDiagonalMoment m hm i s).differentiableAt

theorem groupedHermiteDiagonalMoment_zero_pos
    (m : ℕ) (hm : 1 ≤ m) {s : ℝ} (hs : 0 ≤ s) :
    0 < groupedHermiteDiagonalMoment m 0 s := by
  rw [groupedHermiteDiagonalMoment_zero_eq_norm_sq m hm hs]
  exact sq_pos_of_pos (norm_pos_iff.mpr (hermitePointMass_ne_zero m hm _))

/-- Product constant belonging to an ordered diagonal derivative partition. -/
def groupedDiagonalPartitionConstant (m : ℕ) {i : ℕ} (c : OrderedFinpartition i) : ℝ :=
  ∏ r, groupedDiagonalDerivativeConstant m (c.partSize r)

theorem groupedDiagonalPartitionConstant_nonneg (m : ℕ) (hm : 1 ≤ m)
    {i : ℕ} (c : OrderedFinpartition i) : 0 ≤ groupedDiagonalPartitionConstant m c := by
  apply Finset.prod_nonneg
  intro r hr
  exact (groupedDiagonalDerivativeConstant_pos m hm _).le

theorem abs_prod_groupedHermiteDiagonalMoment_le
    (m : ℕ) (hm : 1 ≤ m) {i : ℕ} (c : OrderedFinpartition i) {s : ℝ} (hs : 0 < s) :
    |∏ r, groupedHermiteDiagonalMoment m (c.partSize r) s| ≤
      groupedDiagonalPartitionConstant m c *
        (groupedHermiteDiagonalMoment m 0 s)^c.length / s^i := by
  rw [Finset.abs_prod]
  calc
    _ ≤ ∏ r, (groupedDiagonalDerivativeConstant m (c.partSize r)/s^(c.partSize r))*
        groupedHermiteDiagonalMoment m 0 s := by
      apply Finset.prod_le_prod₀
      · intro r hr; exact abs_nonneg _
      · intro r hr
        exact norm_groupedHermiteDiagonalMoment_le_relative m hm _ hs
    _ = _ := by
      simp only [Finset.prod_mul_distrib, Finset.prod_div_distrib, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin, Finset.prod_pow_eq_pow_sum,
        grouped_orderedFinpartition_sum_partSize]
      unfold groupedDiagonalPartitionConstant
      ring

/-- Finite Faà di Bruno constant for a scalar power of the actual diagonal. -/
def groupedDiagonalPowerDerivativeConstant (m i : ℕ) (p : ℝ) : ℝ :=
  ∑ c : OrderedFinpartition i,
    groupedDiagonalPartitionConstant m c * |(descPochhammer ℝ c.length).eval p|

theorem groupedDiagonalPowerDerivativeConstant_nonneg
    (m : ℕ) (hm : 1 ≤ m) (i : ℕ) (p : ℝ) :
    0 ≤ groupedDiagonalPowerDerivativeConstant m i p := by
  apply Finset.sum_nonneg
  intro c hc
  exact mul_nonneg (groupedDiagonalPartitionConstant_nonneg m hm c) (abs_nonneg _)

theorem iteratedDeriv_groupedHermiteDiagonalMoment_rpow
    (m : ℕ) (hm : 1 ≤ m) (i : ℕ) (p : ℝ) {s : ℝ} (hs : 0 < s) :
    iteratedDeriv i (fun z => (groupedHermiteDiagonalMoment m 0 z)^p) s =
      ∑ c : OrderedFinpartition i,
        (∏ r, groupedHermiteDiagonalMoment m (c.partSize r) s) *
          ((descPochhammer ℝ c.length).eval p *
            (groupedHermiteDiagonalMoment m 0 s)^(p-(c.length:ℝ))) := by
  have hD := groupedHermiteDiagonalMoment_zero_pos m hm hs.le
  have h := iteratedDeriv_scomp_eq_sum_orderedFinpartition
    (Real.contDiffAt_rpow_const_of_ne (p := p) (n := i) hD.ne')
    (contDiff_groupedHermiteDiagonalMoment_zero m hm i).contDiffAt le_rfl
  simp only [Function.comp_def] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro c hc
  simp_rw [iteratedDeriv_groupedHermiteDiagonalMoment m hm, smul_eq_mul,
    iteratedDeriv_eq_iterate, Real.iter_deriv_rpow_const]

/-- Every scalar power of the positive diagonal has the full relative
inverse-power derivative bound, proved by genuine composition. -/
theorem norm_iteratedDeriv_groupedHermiteDiagonalMoment_rpow_le
    (m : ℕ) (hm : 1 ≤ m) (i : ℕ) (p : ℝ) {s : ℝ} (hs : 0 < s) :
    ‖iteratedDeriv i (fun z => (groupedHermiteDiagonalMoment m 0 z)^p) s‖ ≤
      (groupedDiagonalPowerDerivativeConstant m i p / s^i) *
        (groupedHermiteDiagonalMoment m 0 s)^p := by
  let D := groupedHermiteDiagonalMoment m 0 s
  have hD : 0 < D := groupedHermiteDiagonalMoment_zero_pos m hm hs.le
  have hpow (c : OrderedFinpartition i) : D^c.length * D^(p-(c.length:ℝ)) = D^p := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hD]
    congr 1
    ring
  rw [iteratedDeriv_groupedHermiteDiagonalMoment_rpow m hm i p hs]
  calc
    _ ≤ ∑ c : OrderedFinpartition i,
        ‖(∏ r, groupedHermiteDiagonalMoment m (c.partSize r) s) *
          ((descPochhammer ℝ c.length).eval p * D^(p-(c.length:ℝ)))‖ := norm_sum_le _ _
    _ ≤ ∑ c : OrderedFinpartition i,
        (groupedDiagonalPartitionConstant m c * |(descPochhammer ℝ c.length).eval p| / s^i) * D^p := by
      apply Finset.sum_le_sum
      intro c hc
      rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
        Real.norm_of_nonneg (Real.rpow_nonneg hD.le _)]
      calc
        _ ≤ (groupedDiagonalPartitionConstant m c * D^c.length/s^i)*
            (|(descPochhammer ℝ c.length).eval p| * D^(p-(c.length:ℝ))) :=
          mul_le_mul_of_nonneg_right (abs_prod_groupedHermiteDiagonalMoment_le m hm c hs) (by positivity)
        _ = (groupedDiagonalPartitionConstant m c * |(descPochhammer ℝ c.length).eval p| / s^i)*
            (D^c.length * D^(p-(c.length:ℝ))) := by ring
        _ = _ := by rw [hpow]
    _ = _ := by simp only [groupedDiagonalPowerDerivativeConstant, Finset.sum_div, Finset.sum_mul, D]

theorem groupedHermiteDiagonalMoment_rpow_half_eq_norm
    (m : ℕ) (hm : 1 ≤ m) {s : ℝ} (hs : 0 ≤ s) :
    (groupedHermiteDiagonalMoment m 0 s)^(1/2:ℝ) =
      ‖hermitePointMass m hm (Real.sqrt s)‖ := by
  rw [← Real.sqrt_eq_rpow, groupedHermiteDiagonalMoment_zero_eq_norm_sq m hm hs,
    Real.sqrt_sq (norm_nonneg _)]

theorem groupedHermiteDiagonalMoment_rpow_neg_half_eq_inv_norm
    (m : ℕ) (hm : 1 ≤ m) {s : ℝ} (hs : 0 ≤ s) :
    (groupedHermiteDiagonalMoment m 0 s)^(-(1/2:ℝ)) =
      ‖hermitePointMass m hm (Real.sqrt s)‖⁻¹ := by
  rw [Real.rpow_neg (groupedHermiteDiagonalMoment_zero_pos m hm hs).le,
    groupedHermiteDiagonalMoment_rpow_half_eq_norm m hm hs]

theorem norm_iteratedDeriv_norm_hermitePointMass_sqrt_le
    (m : ℕ) (hm : 1 ≤ m) (i : ℕ) {s : ℝ} (hs : 0 < s) :
    ‖iteratedDeriv i (fun z => ‖hermitePointMass m hm (Real.sqrt z)‖) s‖ ≤
      (groupedDiagonalPowerDerivativeConstant m i (1/2) / s^i) *
        ‖hermitePointMass m hm (Real.sqrt s)‖ := by
  have heq : (fun z => ‖hermitePointMass m hm (Real.sqrt z)‖) =ᶠ[𝓝 s]
      (fun z => (groupedHermiteDiagonalMoment m 0 z)^(1/2:ℝ)) := by
    filter_upwards [Ioi_mem_nhds hs] with z hz
    exact (groupedHermiteDiagonalMoment_rpow_half_eq_norm m hm hz.le).symm
  rw [heq.iteratedDeriv_eq i, ← groupedHermiteDiagonalMoment_rpow_half_eq_norm m hm hs.le]
  exact norm_iteratedDeriv_groupedHermiteDiagonalMoment_rpow_le m hm i (1/2) hs

theorem norm_iteratedDeriv_inv_norm_hermitePointMass_sqrt_le
    (m : ℕ) (hm : 1 ≤ m) (i : ℕ) {s : ℝ} (hs : 0 < s) :
    ‖iteratedDeriv i (fun z => ‖hermitePointMass m hm (Real.sqrt z)‖⁻¹) s‖ ≤
      (groupedDiagonalPowerDerivativeConstant m i (-(1/2)) / s^i) *
        ‖hermitePointMass m hm (Real.sqrt s)‖⁻¹ := by
  have heq : (fun z => ‖hermitePointMass m hm (Real.sqrt z)‖⁻¹) =ᶠ[𝓝 s]
      (fun z => (groupedHermiteDiagonalMoment m 0 z)^(-(1/2:ℝ))) := by
    filter_upwards [Ioi_mem_nhds hs] with z hz
    exact (groupedHermiteDiagonalMoment_rpow_neg_half_eq_inv_norm m hm hz.le).symm
  rw [heq.iteratedDeriv_eq i, ← groupedHermiteDiagonalMoment_rpow_neg_half_eq_inv_norm m hm hs.le]
  exact norm_iteratedDeriv_groupedHermiteDiagonalMoment_rpow_le m hm i (-(1/2)) hs

theorem contDiffAt_norm_hermitePointMass_sqrt
    (m : ℕ) (hm : 1 ≤ m) (q : ℕ) {s : ℝ} (hs : 0 < s) :
    ContDiffAt ℝ q (fun z => ‖hermitePointMass m hm (Real.sqrt z)‖) s := by
  have h := (contDiff_groupedHermiteDiagonalMoment_zero m hm q).contDiffAt.sqrt
    (groupedHermiteDiagonalMoment_zero_pos m hm hs.le).ne'
  apply h.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hs] with z hz
  rw [groupedHermiteDiagonalMoment_zero_eq_norm_sq m hm hz.le, Real.sqrt_sq (norm_nonneg _)]

theorem contDiffAt_inv_norm_hermitePointMass_sqrt
    (m : ℕ) (hm : 1 ≤ m) (q : ℕ) {s : ℝ} (hs : 0 < s) :
    ContDiffAt ℝ q (fun z => ‖hermitePointMass m hm (Real.sqrt z)‖⁻¹) s :=
  (contDiffAt_norm_hermitePointMass_sqrt m hm q hs).inv
    (norm_ne_zero_iff.mpr (hermitePointMass_ne_zero m hm _))

theorem norm_hermitePointMass_neg (m : ℕ) (hm : 1 ≤ m) (x : ℝ) :
    ‖hermitePointMass m hm (-x)‖ = ‖hermitePointMass m hm x‖ := by
  have h := norm_hermitePointMass_neg_sq m hm x
  nlinarith [norm_nonneg (hermitePointMass m hm (-x)), norm_nonneg (hermitePointMass m hm x)]

/-- The actual same-order point-mass norm along a signed-square ray. -/
def groupedHermiteRayNormalizer (m : ℕ) (hm : 1 ≤ m) (ε s : ℝ) : ℝ :=
  ‖hermitePointMass m hm (groupedSignedSquareRayPoint ε s)‖

theorem groupedHermiteRayNormalizer_pos (m : ℕ) (hm : 1 ≤ m) (ε s : ℝ) :
    0 < groupedHermiteRayNormalizer m hm ε s :=
  norm_pos_iff.mpr (hermitePointMass_ne_zero m hm _)

theorem groupedHermiteRayNormalizer_one (m : ℕ) (hm : 1 ≤ m) (s : ℝ) :
    groupedHermiteRayNormalizer m hm 1 s = ‖hermitePointMass m hm (Real.sqrt s)‖ := by
  simp [groupedHermiteRayNormalizer, groupedSignedSquareRayPoint]

theorem groupedHermiteRayNormalizer_neg_one (m : ℕ) (hm : 1 ≤ m) (s : ℝ) :
    groupedHermiteRayNormalizer m hm (-1) s = ‖hermitePointMass m hm (Real.sqrt (-s))‖ := by
  simp [groupedHermiteRayNormalizer, groupedSignedSquareRayPoint, norm_hermitePointMass_neg]

theorem groupedHermiteRayNormalizer_one_fun (m : ℕ) (hm : 1 ≤ m) :
    groupedHermiteRayNormalizer m hm 1 = fun s => ‖hermitePointMass m hm (Real.sqrt s)‖ :=
  funext (groupedHermiteRayNormalizer_one m hm)

theorem groupedHermiteRayNormalizer_neg_one_fun (m : ℕ) (hm : 1 ≤ m) :
    groupedHermiteRayNormalizer m hm (-1) = fun s => ‖hermitePointMass m hm (Real.sqrt (-s))‖ :=
  funext (groupedHermiteRayNormalizer_neg_one m hm)

/-- The actual norm's full relative inverse-power estimate on both signed-square rays. -/
theorem norm_iteratedDeriv_groupedHermiteRayNormalizer_le
    (m : ℕ) (hm : 1 ≤ m) (i : ℕ) (ε s : ℝ) (hε : ε^2=1) (hs : 0 < ε*s) :
    ‖iteratedDeriv i (groupedHermiteRayNormalizer m hm ε) s‖ ≤
      (groupedDiagonalPowerDerivativeConstant m i (1/2)/|s|^i)*
        groupedHermiteRayNormalizer m hm ε s := by
  rcases sq_eq_one_iff.mp hε with rfl | rfl
  · simp only [one_mul] at hs
    simp_rw [groupedHermiteRayNormalizer_one_fun]
    rw [abs_of_pos hs]
    exact norm_iteratedDeriv_norm_hermitePointMass_sqrt_le m hm i hs
  · have hs' : s < 0 := by linarith
    simp_rw [groupedHermiteRayNormalizer_neg_one_fun]
    rw [iteratedDeriv_comp_neg i (fun z => ‖hermitePointMass m hm (Real.sqrt z)‖),
      norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul, abs_of_neg hs']
    exact norm_iteratedDeriv_norm_hermitePointMass_sqrt_le m hm i (by linarith)

/-- The reciprocal norm's full relative inverse-power estimate on both rays. -/
theorem norm_iteratedDeriv_inv_groupedHermiteRayNormalizer_le
    (m : ℕ) (hm : 1 ≤ m) (i : ℕ) (ε s : ℝ) (hε : ε^2=1) (hs : 0 < ε*s) :
    ‖iteratedDeriv i (fun z => (groupedHermiteRayNormalizer m hm ε z)⁻¹) s‖ ≤
      (groupedDiagonalPowerDerivativeConstant m i (-(1/2))/|s|^i)*
        (groupedHermiteRayNormalizer m hm ε s)⁻¹ := by
  rcases sq_eq_one_iff.mp hε with rfl | rfl
  · simp only [one_mul] at hs
    simp_rw [groupedHermiteRayNormalizer_one]
    rw [abs_of_pos hs]
    exact norm_iteratedDeriv_inv_norm_hermitePointMass_sqrt_le m hm i hs
  · have hs' : s < 0 := by linarith
    simp_rw [groupedHermiteRayNormalizer_neg_one]
    rw [iteratedDeriv_comp_neg i (fun z => ‖hermitePointMass m hm (Real.sqrt z)‖⁻¹),
      norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul, abs_of_neg hs']
    exact norm_iteratedDeriv_inv_norm_hermitePointMass_sqrt_le m hm i (by linarith)

theorem contDiffAt_groupedHermiteRayNormalizer
    (m : ℕ) (hm : 1 ≤ m) (q : ℕ) (ε s : ℝ) (hε : ε^2=1) (hs : 0 < ε*s) :
    ContDiffAt ℝ q (groupedHermiteRayNormalizer m hm ε) s := by
  rcases sq_eq_one_iff.mp hε with rfl | rfl
  · simp only [one_mul] at hs
    simpa only [groupedHermiteRayNormalizer_one_fun] using contDiffAt_norm_hermitePointMass_sqrt m hm q hs
  · have h := (contDiffAt_norm_hermitePointMass_sqrt m hm q (s := -s) (by linarith)).comp s
      contDiffAt_id.neg
    simpa only [Function.comp_def, groupedHermiteRayNormalizer_neg_one_fun] using h

theorem contDiffAt_inv_groupedHermiteRayNormalizer
    (m : ℕ) (hm : 1 ≤ m) (q : ℕ) (ε s : ℝ) (hε : ε^2=1) (hs : 0 < ε*s) :
    ContDiffAt ℝ q (fun z => (groupedHermiteRayNormalizer m hm ε z)⁻¹) s :=
  (contDiffAt_groupedHermiteRayNormalizer m hm q ε s hε hs).inv
    (groupedHermiteRayNormalizer_pos m hm ε s).ne'

/-- One positive constant controls both the norm and reciprocal norm
through any fixed finite derivative order. -/
def groupedNormalizerDerivativeConstant (m q : ℕ) : ℝ :=
  1 + ∑ i ∈ Finset.range (q+1),
    (groupedDiagonalPowerDerivativeConstant m i (1/2) +
      groupedDiagonalPowerDerivativeConstant m i (-(1/2)))

theorem groupedNormalizerDerivativeConstant_pos (m : ℕ) (hm : 1 ≤ m) (q : ℕ) :
    0 < groupedNormalizerDerivativeConstant m q := by
  have h : 0 ≤ ∑ i ∈ Finset.range (q+1),
      (groupedDiagonalPowerDerivativeConstant m i (1/2) +
        groupedDiagonalPowerDerivativeConstant m i (-(1/2))) := by
    exact Finset.sum_nonneg (fun i hi => add_nonneg
      (groupedDiagonalPowerDerivativeConstant_nonneg m hm i _)
      (groupedDiagonalPowerDerivativeConstant_nonneg m hm i _))
  unfold groupedNormalizerDerivativeConstant
  linarith

theorem groupedDiagonalPowerDerivativeConstant_le_uniform
    (m : ℕ) (hm : 1 ≤ m) (q i : ℕ) (hi : i ≤ q) :
    groupedDiagonalPowerDerivativeConstant m i (1/2) ≤ groupedNormalizerDerivativeConstant m q ∧
    groupedDiagonalPowerDerivativeConstant m i (-(1/2)) ≤ groupedNormalizerDerivativeConstant m q := by
  have h := Finset.single_le_sum (f := fun i =>
      groupedDiagonalPowerDerivativeConstant m i (1/2) + groupedDiagonalPowerDerivativeConstant m i (-(1/2)))
    (s := Finset.range (q+1))
    (fun j hj => add_nonneg (groupedDiagonalPowerDerivativeConstant_nonneg m hm j _)
      (groupedDiagonalPowerDerivativeConstant_nonneg m hm j _))
    (Finset.mem_range.mpr (by omega : i < q+1))
  have hp := groupedDiagonalPowerDerivativeConstant_nonneg m hm i (1/2)
  have hn := groupedDiagonalPowerDerivativeConstant_nonneg m hm i (-(1/2))
  unfold groupedNormalizerDerivativeConstant
  constructor <;> linarith

/-- Simultaneous all-order bounds for the actual normalizer and its reciprocal,
with one constant for every order through `q` and both ray signs. -/
theorem groupedHermiteRayNormalizer_derivative_bounds
    (m : ℕ) (hm : 1 ≤ m) (q i : ℕ) (hi : i ≤ q)
    (ε s : ℝ) (hε : ε^2=1) (hs : 1 ≤ ε*s) :
    ‖iteratedDeriv i (groupedHermiteRayNormalizer m hm ε) s‖ ≤
        (groupedNormalizerDerivativeConstant m q / |s|^i)*groupedHermiteRayNormalizer m hm ε s ∧
    ‖iteratedDeriv i (fun z => (groupedHermiteRayNormalizer m hm ε z)⁻¹) s‖ ≤
        (groupedNormalizerDerivativeConstant m q / |s|^i)*(groupedHermiteRayNormalizer m hm ε s)⁻¹ := by
  have hC := groupedDiagonalPowerDerivativeConstant_le_uniform m hm q i hi
  have hpos := groupedHermiteRayNormalizer_pos m hm ε s
  constructor
  · refine (norm_iteratedDeriv_groupedHermiteRayNormalizer_le m hm i ε s hε (by linarith)).trans ?_
    gcongr
    exact hC.1
  · refine (norm_iteratedDeriv_inv_groupedHermiteRayNormalizer_le m hm i ε s hε (by linarith)).trans ?_
    gcongr
    exact hC.2

/-- Leibniz expansion for a real weight multiplying a complex kernel. -/
theorem grouped_iteratedDeriv_fun_smul (n : ℕ) (f : ℝ → ℝ) (g : ℝ → ℂ) (x : ℝ)
    (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g x) :
    iteratedDeriv n (fun z => f z • g z) x =
      ∑ a ∈ Finset.range (n+1), ((n.choose a:ℝ)*iteratedDeriv a f x) •
        iteratedDeriv (n-a) g x := by
  have h := iteratedDerivWithin_smul (Set.mem_univ x) uniqueDiffOn_univ
    hf.contDiffWithinAt hg.contDiffWithinAt
  change iteratedDeriv n (f • g) x = _
  simpa only [iteratedDerivWithin_univ, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul] using h

theorem contDiffAt_hermiteResolventKernel_ray_left
    (q m : ℕ) (hm : groupedHermiteDifferentiationOrder q ≤ m)
    (ε s y : ℝ) (hs : 0 < ε*s) :
    ContDiffAt ℝ q (fun z => hermiteResolventKernel m (groupedSignedSquareRayPoint ε z) y) s := by
  have h := (contDiff_groupedHermiteMixedJetKernel_left q m 0 hm (by omega) y).contDiffAt.comp s
    (contDiffAt_groupedSignedSquareRayPoint ε s q hs)
  simpa only [Function.comp_def, groupedHermiteMixedJetKernel_zero] using h

theorem contDiffAt_iteratedDeriv_hermiteResolventKernel_ray_right
    (q m i : ℕ) (hm : groupedHermiteDifferentiationOrder q ≤ m) (hi : i ≤ q)
    (ε η s t : ℝ) (hs : 0 < ε*s) (ht : 0 < η*t) :
    ContDiffAt ℝ q (fun v => iteratedDeriv i (fun u => hermiteResolventKernel m
      (groupedSignedSquareRayPoint ε u) (groupedSignedSquareRayPoint η v)) s) t := by
  have heq : (fun v => iteratedDeriv i (fun u => hermiteResolventKernel m
      (groupedSignedSquareRayPoint ε u) (groupedSignedSquareRayPoint η v)) s) =
      fun v => ∑ c : OrderedFinpartition i, groupedRayPartitionCoefficient ε s c •
        groupedHermiteMixedJetKernel m c.length 0 (groupedSignedSquareRayPoint ε s)
          (groupedSignedSquareRayPoint η v) := by
    funext v
    simp_rw [← groupedHermiteMixedJetKernel_zero]
    exact iteratedDeriv_groupedHermiteMixedJetKernel_ray_left q m i 0 hm hi (by omega) ε s _ hs
  rw [heq]
  apply ContDiffAt.sum
  intro c hc
  apply ContDiffAt.const_smul
  exact (contDiff_groupedHermiteMixedJetKernel_right q m c.length hm
    (c.length_le.trans hi) (groupedSignedSquareRayPoint ε s)).contDiffAt.comp t
      (contDiffAt_groupedSignedSquareRayPoint η t q ht)

theorem normalizedHermiteGramKernel_ray_eq_smul
    (m : ℕ) (hm : 1 ≤ m) (ε s y : ℝ) :
    normalizedHermiteGramKernel m hm (groupedSignedSquareRayPoint ε s) y =
      (groupedHermiteRayNormalizer m hm ε s)⁻¹ •
        (‖hermitePointMass m hm y‖⁻¹ • hermiteResolventKernel m (groupedSignedSquareRayPoint ε s) y) := by
  rw [normalizedHermiteGramKernel_eq_resolventKernel, smul_smul]
  rfl

theorem iteratedDeriv_normalizedHermiteGramKernel_ray_left
    (q m i : ℕ) (hm : groupedHermiteDifferentiationOrder q ≤ m) (hi : i ≤ q)
    (ε s y : ℝ) (hε : ε^2=1) (hs : 0 < ε*s) :
    iteratedDeriv i (fun u => normalizedHermiteGramKernel m
      (by have := (le_max_left _ _).trans hm; omega) (groupedSignedSquareRayPoint ε u) y) s =
      ∑ a ∈ Finset.range (i+1),
        ((i.choose a:ℝ)*iteratedDeriv a (fun u => (groupedHermiteRayNormalizer m
          (by have := (le_max_left _ _).trans hm; omega) ε u)⁻¹) s) •
          (‖hermitePointMass m (by have := (le_max_left _ _).trans hm; omega) y‖⁻¹ •
            iteratedDeriv (i-a) (fun u => hermiteResolventKernel m
              (groupedSignedSquareRayPoint ε u) y) s) := by
  have hq : q+2 ≤ m := (le_max_left _ _).trans hm
  simp_rw [normalizedHermiteGramKernel_ray_eq_smul]
  rw [grouped_iteratedDeriv_fun_smul i _ _ s
    (contDiffAt_inv_groupedHermiteRayNormalizer m (by omega) i ε s hε hs)
    (((contDiffAt_hermiteResolventKernel_ray_left q m hm ε s y hs).of_le
      (by exact_mod_cast hi)).const_smul _)]
  simp only [iteratedDeriv_fun_const_smul_field]

/-- Exact mixed Leibniz formula for the actual normalized Hermite Gram
kernel. All terms use genuine derivatives of the two actual reciprocal norms. -/
theorem iteratedDeriv_iteratedDeriv_normalizedHermiteGramKernel_signedSquareRay_eq
    (q m i j : ℕ) (hm : groupedHermiteDifferentiationOrder q ≤ m)
    (hi : i ≤ q) (hj : j ≤ q) (ε η s t : ℝ)
    (hε : ε^2=1) (hη : η^2=1) (hs : 0 < ε*s) (ht : 0 < η*t) :
    iteratedDeriv j (fun v => iteratedDeriv i (fun u => normalizedHermiteGramKernel m
      (by have := (le_max_left _ _).trans hm; omega)
      (groupedSignedSquareRayPoint ε u) (groupedSignedSquareRayPoint η v)) s) t =
      ∑ a ∈ Finset.range (i+1), ∑ b ∈ Finset.range (j+1),
        (((i.choose a:ℝ)*iteratedDeriv a (fun u => (groupedHermiteRayNormalizer m
          (by have := (le_max_left _ _).trans hm; omega) ε u)⁻¹) s) *
          ((j.choose b:ℝ)*iteratedDeriv b (fun v => (groupedHermiteRayNormalizer m
            (by have := (le_max_left _ _).trans hm; omega) η v)⁻¹) t)) •
          iteratedDeriv (j-b) (fun v => iteratedDeriv (i-a) (fun u => hermiteResolventKernel m
            (groupedSignedSquareRayPoint ε u) (groupedSignedSquareRayPoint η v)) s) t := by
  have hq : q+2 ≤ m := (le_max_left _ _).trans hm
  simp_rw [iteratedDeriv_normalizedHermiteGramKernel_ray_left q m i hm hi ε s _ hε hs]
  have hsm (a : ℕ) (_ha : a ∈ Finset.range (i+1)) : ContDiffAt ℝ j
      (fun v => ((i.choose a:ℝ)*iteratedDeriv a (fun u => (groupedHermiteRayNormalizer m
        (by omega) ε u)⁻¹) s) •
        (‖hermitePointMass m (by omega) (groupedSignedSquareRayPoint η v)‖⁻¹ •
          iteratedDeriv (i-a) (fun u => hermiteResolventKernel m
            (groupedSignedSquareRayPoint ε u) (groupedSignedSquareRayPoint η v)) s)) t := by
    apply ContDiffAt.const_smul
    exact (contDiffAt_inv_groupedHermiteRayNormalizer m (by omega) j η t hη ht).smul
      ((contDiffAt_iteratedDeriv_hermiteResolventKernel_ray_right q m (i-a) hm
        (by omega) ε η s t hs ht).of_le (by exact_mod_cast hj))
  rw [iteratedDeriv_fun_sum hsm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [iteratedDeriv_fun_const_smul_field]
  have hleib := grouped_iteratedDeriv_fun_smul j _ _ t
    (contDiffAt_inv_groupedHermiteRayNormalizer m (by omega) j η t hη ht)
    ((contDiffAt_iteratedDeriv_hermiteResolventKernel_ray_right q m (i-a) hm
      (by omega) ε η s t hs ht).of_le (by exact_mod_cast hj))
  simp only [groupedHermiteRayNormalizer] at hleib
  rw [hleib, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [smul_smul]
  rfl

theorem grouped_abs_ge_one_on_signedSquareRay (ε s : ℝ) (hε : ε^2=1) (hs : 1 ≤ ε*s) :
    1 ≤ |s| := by
  have heps : |ε|=1 := by nlinarith [sq_abs ε, abs_nonneg ε]
  have heq : |ε*s|=|s| := by rw [abs_mul, heps, one_mul]
  rw [← heq, abs_of_pos (by linarith : 0 < ε*s)]
  exact hs

theorem norm_iteratedDeriv_inv_groupedHermiteRayNormalizer_le_tail
    (m : ℕ) (hm : 1 ≤ m) (q i : ℕ) (hi : i ≤ q)
    (ε s : ℝ) (hε : ε^2=1) (hs : 1 ≤ ε*s) :
    ‖iteratedDeriv i (fun z => (groupedHermiteRayNormalizer m hm ε z)⁻¹) s‖ ≤
      groupedNormalizerDerivativeConstant m q * (groupedHermiteRayNormalizer m hm ε s)⁻¹ := by
  refine (groupedHermiteRayNormalizer_derivative_bounds m hm q i hi ε s hε hs).2.trans ?_
  apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr (groupedHermiteRayNormalizer_pos m hm ε s).le)
  exact div_le_self (groupedNormalizerDerivativeConstant_pos m hm q).le
    (one_le_pow₀ (grouped_abs_ge_one_on_signedSquareRay ε s hε hs))

/-- Actual normalized-kernel mixed derivatives are uniformly bounded on
all signed-square tail-ray pairs, with no reciprocal minimum node gap.
The sufficient cofinal cutoff is exactly the raw-kernel cutoff. This bound
does not assert convergence or a differentiated asymptotic remainder. -/
theorem exists_norm_iteratedDeriv_iteratedDeriv_normalizedHermiteGramKernel_signedSquareRay_le
    (q m i j : ℕ) (hm : groupedHermiteDifferentiationOrder q ≤ m)
    (hi : i ≤ q) (hj : j ≤ q) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε η : ℝ, ε^2=1 → η^2=1 → ∀ s t : ℝ,
      1 ≤ ε*s → 1 ≤ η*t →
      ‖iteratedDeriv j (fun v => iteratedDeriv i (fun u => normalizedHermiteGramKernel m
        (by have := (le_max_left _ _).trans hm; omega)
        (groupedSignedSquareRayPoint ε u) (groupedSignedSquareRayPoint η v)) s) t‖ ≤ C := by
  classical
  have hq : q+2 ≤ m := (le_max_left _ _).trans hm
  have hp : 1 ≤ m := by omega
  choose R hR hraw using fun a b : ℕ =>
    exists_norm_iteratedDeriv_iteratedDeriv_hermiteResolventKernel_signedSquareRay_le_weighted
      q m (i-a) (j-b) hm (by omega) (by omega)
  let N := groupedNormalizerDerivativeConstant m q
  have hN : 0 < N := groupedNormalizerDerivativeConstant_pos m hp q
  let B : ℝ := ∑ a ∈ Finset.range (i+1), ∑ b ∈ Finset.range (j+1),
    (i.choose a:ℝ)*(j.choose b:ℝ)*N^2*R a b
  have hB : 0 ≤ B := by
    apply Finset.sum_nonneg
    intro a ha
    apply Finset.sum_nonneg
    intro b hb
    exact mul_nonneg (by positivity) (hR a b).le
  refine ⟨B+1, by linarith, ?_⟩
  intro ε η hε hη s t hs ht
  let U := groupedHermiteRayNormalizer m hp ε s
  let V := groupedHermiteRayNormalizer m hp η t
  have hU : 0 < U := groupedHermiteRayNormalizer_pos m hp ε s
  have hV : 0 < V := groupedHermiteRayNormalizer_pos m hp η t
  have hterm (a b : ℕ) (ha : a ∈ Finset.range (i+1)) (hb : b ∈ Finset.range (j+1)) :
      ‖(((i.choose a:ℝ)*iteratedDeriv a (fun u => (groupedHermiteRayNormalizer m hp ε u)⁻¹) s) *
        ((j.choose b:ℝ)*iteratedDeriv b (fun v => (groupedHermiteRayNormalizer m hp η v)⁻¹) t)) •
          iteratedDeriv (j-b) (fun v => iteratedDeriv (i-a) (fun u => hermiteResolventKernel m
            (groupedSignedSquareRayPoint ε u) (groupedSignedSquareRayPoint η v)) s) t‖ ≤
        (i.choose a:ℝ)*(j.choose b:ℝ)*N^2*R a b := by
    have ha' : a ≤ q := by have := Finset.mem_range.mp ha; omega
    have hb' : b ≤ q := by have := Finset.mem_range.mp hb; omega
    have hleft := norm_iteratedDeriv_inv_groupedHermiteRayNormalizer_le_tail m hp q a ha' ε s hε hs
    have hright := norm_iteratedDeriv_inv_groupedHermiteRayNormalizer_le_tail m hp q b hb' η t hη ht
    have hK := hraw a b ε η hε hη s t hs ht
    rw [norm_smul, norm_mul, norm_mul, norm_mul,
      Real.norm_of_nonneg (Nat.cast_nonneg (i.choose a)),
      Real.norm_of_nonneg (Nat.cast_nonneg (j.choose b))]
    calc
      _ ≤ ((i.choose a:ℝ)*(N*U⁻¹))*((j.choose b:ℝ)*(N*V⁻¹))*(R a b*U*V) := by
        apply mul_le_mul
          (mul_le_mul (mul_le_mul_of_nonneg_left hleft (Nat.cast_nonneg _))
            (mul_le_mul_of_nonneg_left hright (Nat.cast_nonneg _)) (by positivity) (by positivity))
          hK (norm_nonneg _) (by positivity)
      _ = _ := by field_simp [hU.ne', hV.ne']
  rw [iteratedDeriv_iteratedDeriv_normalizedHermiteGramKernel_signedSquareRay_eq
    q m i j hm hi hj ε η s t hε hη (by linarith) (by linarith)]
  calc
    _ ≤ ∑ a ∈ Finset.range (i+1), ∑ b ∈ Finset.range (j+1),
        ‖(((i.choose a:ℝ)*iteratedDeriv a (fun u => (groupedHermiteRayNormalizer m hp ε u)⁻¹) s) *
          ((j.choose b:ℝ)*iteratedDeriv b (fun v => (groupedHermiteRayNormalizer m hp η v)⁻¹) t)) •
            iteratedDeriv (j-b) (fun v => iteratedDeriv (i-a) (fun u => hermiteResolventKernel m
              (groupedSignedSquareRayPoint ε u) (groupedSignedSquareRayPoint η v)) s) t‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro a ha
      exact norm_sum_le _ _
    _ ≤ B := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      exact hterm a b ha hb
    _ ≤ B+1 := by linarith

/-- A single constant controls every mixed derivative through `q` of the
actual normalized kernel, uniformly in the ray signs and tail nodes. -/
theorem exists_uniform_normalizedHermiteGramKernel_signedSquareRay_derivative_bound
    (q m : ℕ) (hm : groupedHermiteDifferentiationOrder q ≤ m) :
    ∃ C : ℝ, 0 < C ∧ ∀ i j : ℕ, i ≤ q → j ≤ q →
      ∀ ε η : ℝ, ε^2=1 → η^2=1 → ∀ s t : ℝ, 1 ≤ ε*s → 1 ≤ η*t →
      ‖iteratedDeriv j (fun v => iteratedDeriv i (fun u => normalizedHermiteGramKernel m
        (by have := (le_max_left _ _).trans hm; omega)
        (groupedSignedSquareRayPoint ε u) (groupedSignedSquareRayPoint η v)) s) t‖ ≤ C := by
  classical
  choose C hC hb using fun (i j : Fin (q+1)) =>
    exists_norm_iteratedDeriv_iteratedDeriv_normalizedHermiteGramKernel_signedSquareRay_le
      q m i j hm (by omega) (by omega)
  let B : ℝ := ∑ i : Fin (q+1), ∑ j : Fin (q+1), C i j
  have hB : 0 ≤ B := Finset.sum_nonneg (fun i hi =>
    Finset.sum_nonneg (fun j hj => (hC i j).le))
  refine ⟨B+1, by linarith, ?_⟩
  intro i j hi hj ε η hε hη s t hs ht
  let ii : Fin (q+1) := ⟨i, by omega⟩
  let jj : Fin (q+1) := ⟨j, by omega⟩
  have h₁ : C ii jj ≤ ∑ j : Fin (q+1), C ii j :=
    Finset.single_le_sum (fun j hj => (hC ii j).le) (Finset.mem_univ jj)
  have h₂ : (∑ j : Fin (q+1), C ii j) ≤ B :=
    Finset.single_le_sum (fun i hi => Finset.sum_nonneg (fun j hj => (hC i j).le))
      (Finset.mem_univ ii)
  exact (hb ii jj ε η hε hη s t hs ht).trans ((h₁.trans h₂).trans (by linarith))

end

end MeyerGeneralProblem
