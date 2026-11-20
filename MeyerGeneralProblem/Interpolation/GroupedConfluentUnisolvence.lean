module

public import MeyerGeneralProblem.Interpolation.UniformNewtonBounds
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section

/-!
# Multiple-group confluent Newton interpolation

The actual prefix divided differences on several disjoint groups uniquely
determine a polynomial below the total node count. Nodes within each group
may coincide, and their multiplicities are retained in the group's nodal
product. Vanishing data force divisibility by every group product; coprimality
between different groups then forces divisibility by the full product.

This is the algebraic unisolvence step for the compact grouped-matrix route.
No inverse bound, intra-group separation, or global weighted interpolant is
part of the assumptions.
-/

namespace MeyerGeneralProblem

noncomputable section

open Finset Polynomial

section Algebra

variable {K : Type*} [Field K]

/-- Nodal product with multiplicities for the first `n` entries of a node
sequence. Indexing factors retains repeated roots. -/
def confluentNodalProduct (nodes : ℕ → K) (n : ℕ) : K[X] :=
  ∏ i ∈ Finset.range n, (X - C (nodes i))

/-- Removing the first indexed factor shifts the node sequence. -/
theorem confluentNodalProduct_succ (nodes : ℕ → K) (n : ℕ) :
    confluentNodalProduct nodes (n + 1) =
      (X - C (nodes 0)) * confluentNodalProduct (fun i => nodes (i + 1)) n := by
  simp only [confluentNodalProduct, Finset.prod_range_succ', mul_comm]

/-- Every confluent nodal product is monic, even when every node coincides. -/
theorem confluentNodalProduct_monic (nodes : ℕ → K) (n : ℕ) :
    (confluentNodalProduct nodes n).Monic :=
  Polynomial.monic_prod_of_monic _ _ (fun _ _ => Polynomial.monic_X_sub_C _)

/-- The degree is the number of indexed nodes, not the number of distinct
node values. -/
@[simp]
theorem natDegree_confluentNodalProduct (nodes : ℕ → K) (n : ℕ) :
    (confluentNodalProduct nodes n).natDegree = n := by
  rw [confluentNodalProduct, Polynomial.natDegree_prod_of_monic _ _
    (fun i _ => Polynomial.monic_X_sub_C _)]
  simp

/-- Vanishing first `n` prefix divided differences force the full nodal
product, with all multiplicities, to divide the polynomial. -/
theorem confluentNodalProduct_dvd_of_zero_data (nodes : ℕ → K) (n : ℕ) (p : K[X])
    (hdata : ∀ i < n, polynomialDividedDifference nodes i p = 0) :
    confluentNodalProduct nodes n ∣ p := by
  induction n generalizing nodes p with
  | zero => simp [confluentNodalProduct]
  | succ n ih =>
      have hvalue : p.eval (nodes 0) = 0 := hdata 0 (Nat.zero_lt_succ _)
      have hfactor : (X - C (nodes 0)) * newtonQuotient (nodes 0) p = p := by
        simpa only [hvalue, C_0, sub_zero] using X_sub_C_mul_newtonQuotient (nodes 0) p
      have htail : ∀ i < n, polynomialDividedDifference (fun j => nodes (j + 1)) i
          (newtonQuotient (nodes 0) p) = 0 := by
        intro i hi
        exact hdata (i + 1) (Nat.succ_lt_succ hi)
      rw [confluentNodalProduct_succ, ← hfactor]
      exact mul_dvd_mul_left _ (ih _ _ htail)

variable {ι : Type*} [Fintype ι]

/-- Different groups share no node value. No restriction is made on
coincidences among entries of the same group. -/
def GroupedNodeDisjoint (size : ι → ℕ) (nodes : ι → ℕ → K) : Prop :=
  ∀ g h, g ≠ h → ∀ i < size g, ∀ j < size h, nodes g i ≠ nodes h j

omit [Fintype ι] in
/-- Disjoint group node ranges make their complete nodal products coprime,
even when each group contains repeated roots. -/
theorem isCoprime_confluentNodalProduct_of_groupedNodeDisjoint
    (size : ι → ℕ) (nodes : ι → ℕ → K) (hdisjoint : GroupedNodeDisjoint size nodes)
    {g h : ι} (hgh : g ≠ h) :
    IsCoprime (confluentNodalProduct (nodes g) (size g))
      (confluentNodalProduct (nodes h) (size h)) := by
  unfold confluentNodalProduct
  apply IsCoprime.prod_left
  intro i hi
  apply IsCoprime.prod_right
  intro j hj
  exact Polynomial.isCoprime_X_sub_C_of_isUnit_sub
    (sub_ne_zero.mpr (hdisjoint g h hgh i (Finset.mem_range.mp hi)
      j (Finset.mem_range.mp hj))).isUnit

/-- The full product over all groups has degree exactly the total node
count, including the internal multiplicities of every group. -/
theorem natDegree_prod_confluentNodalProduct (size : ι → ℕ) (nodes : ι → ℕ → K) :
    (∏ g, confluentNodalProduct (nodes g) (size g)).natDegree = ∑ g, size g := by
  rw [Polynomial.natDegree_prod_of_monic _ _ (fun g _ => confluentNodalProduct_monic _ _)]
  simp

/-- Actual multiple-group confluent Newton unisolvence: null prefix data
force a degree-bounded polynomial to be zero. -/
theorem groupedConfluentUnisolvence (size : ι → ℕ) (nodes : ι → ℕ → K)
    (hdisjoint : GroupedNodeDisjoint size nodes) (p : K[X])
    (hdegree : p ∈ Polynomial.degreeLT K (∑ g, size g))
    (hdata : ∀ g, ∀ i < size g, polynomialDividedDifference (nodes g) i p = 0) :
    p = 0 := by
  have hdvd : (∏ g, confluentNodalProduct (nodes g) (size g)) ∣ p :=
    Fintype.prod_dvd_of_coprime
      (fun g h hgh => isCoprime_confluentNodalProduct_of_groupedNodeDisjoint
        size nodes hdisjoint hgh)
      (fun g => confluentNodalProduct_dvd_of_zero_data (nodes g) (size g) p (hdata g))
  by_contra hp
  have hle := Polynomial.natDegree_le_of_dvd hdvd hp
  rw [natDegree_prod_confluentNodalProduct] at hle
  have hlt := (Polynomial.natDegree_lt_iff_degree_lt hp).mpr
    (Polynomial.mem_degreeLT.mp hdegree)
  omega

/-- The actual block prefix-data map on polynomials below the total number
of nodes, with one coordinate per indexed node of each group. -/
def groupedConfluentData (size : ι → ℕ) (nodes : ι → ℕ → K) :
    Polynomial.degreeLT K (∑ g, size g) →ₗ[K] ((g : ι) → Fin (size g) → K) where
  toFun p g i := polynomialDividedDifference (nodes g) i p
  map_add' p q := by
    funext g i
    exact polynomialDividedDifference_add (nodes g) i p q
  map_smul' c p := by
    funext g i
    simpa only [Submodule.coe_smul, Polynomial.smul_eq_C_mul, Pi.smul_apply,
      smul_eq_mul, RingHom.id_apply] using polynomialDividedDifference_C_mul (nodes g) i c p

/-- The block divided-difference map is injective under inter-group
disjointness alone. -/
theorem groupedConfluentData_injective (size : ι → ℕ) (nodes : ι → ℕ → K)
    (hdisjoint : GroupedNodeDisjoint size nodes) :
    Function.Injective (groupedConfluentData size nodes) := by
  intro p q hpq
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply groupedConfluentUnisolvence size nodes hdisjoint (p.1 - q.1)
    ((Polynomial.degreeLT K (∑ g, size g)).sub_mem p.property q.property)
  intro g i hi
  have hzero : groupedConfluentData size nodes (p - q) = 0 := by
    rw [map_sub, hpq, sub_self]
  exact congrFun (congrFun hzero g) ⟨i, hi⟩

/-- Grouped prefix data and degree-bounded polynomials are genuinely
linearly equivalent; the inverse is derived from unisolvence and dimensions. -/
def groupedConfluentDataEquiv (size : ι → ℕ) (nodes : ι → ℕ → K)
    (hdisjoint : GroupedNodeDisjoint size nodes) :
    Polynomial.degreeLT K (∑ g, size g) ≃ₗ[K] ((g : ι) → Fin (size g) → K) :=
  LinearEquiv.ofInjectiveOfFinrankEq (groupedConfluentData size nodes)
    (groupedConfluentData_injective size nodes hdisjoint) (by
      rw [(Polynomial.degreeLTEquiv K (∑ g, size g)).finrank_eq]
      simp only [Module.finrank_pi, Fintype.card_fin, Module.finrank_pi_fintype])

/-- The derived grouped equivalence evaluates to the actual synthetic
divided differences, not to an unrelated abstract coordinate map. -/
@[simp]
theorem groupedConfluentDataEquiv_apply (size : ι → ℕ) (nodes : ι → ℕ → K)
    (hdisjoint : GroupedNodeDisjoint size nodes)
    (p : Polynomial.degreeLT K (∑ g, size g)) (g : ι) (i : Fin (size g)) :
    groupedConfluentDataEquiv size nodes hdisjoint p g i =
      polynomialDividedDifference (nodes g) i p := rfl

/-- The actual polynomial interpolating arbitrary grouped confluent data. -/
def groupedConfluentInterpolant (size : ι → ℕ) (nodes : ι → ℕ → K)
    (hdisjoint : GroupedNodeDisjoint size nodes) (data : (g : ι) → Fin (size g) → K) :
    Polynomial.degreeLT K (∑ g, size g) :=
  (groupedConfluentDataEquiv size nodes hdisjoint).symm data

/-- The grouped interpolant satisfies every prescribed prefix divided
difference, including higher jets at repeated nodes. -/
@[simp]
theorem polynomialDividedDifference_groupedConfluentInterpolant
    (size : ι → ℕ) (nodes : ι → ℕ → K) (hdisjoint : GroupedNodeDisjoint size nodes)
    (data : (g : ι) → Fin (size g) → K) (g : ι) (i : Fin (size g)) :
    polynomialDividedDifference (nodes g) i
      (groupedConfluentInterpolant size nodes hdisjoint data) = data g i := by
  change groupedConfluentDataEquiv size nodes hdisjoint
    ((groupedConfluentDataEquiv size nodes hdisjoint).symm data) g i = data g i
  rw [LinearEquiv.apply_symm_apply]

/-- There is exactly one grouped confluent interpolant below the total
node count. This includes arbitrary multiplicities within disjoint groups. -/
theorem existsUnique_groupedConfluentInterpolant
    (size : ι → ℕ) (nodes : ι → ℕ → K) (hdisjoint : GroupedNodeDisjoint size nodes)
    (data : (g : ι) → Fin (size g) → K) :
    ∃! p : Polynomial.degreeLT K (∑ g, size g),
      ∀ g, ∀ i : Fin (size g), polynomialDividedDifference (nodes g) i p = data g i := by
  refine ⟨groupedConfluentInterpolant size nodes hdisjoint data,
    polynomialDividedDifference_groupedConfluentInterpolant size nodes hdisjoint data, ?_⟩
  intro p hp
  apply groupedConfluentData_injective size nodes hdisjoint
  funext g i
  exact (hp g i).trans
    (polynomialDividedDifference_groupedConfluentInterpolant size nodes hdisjoint data g i).symm

/-- At collapsed groups, the actual block rows are Taylor coefficients
of distinct centres, preserving every prescribed multiplicity. -/
theorem groupedConfluentData_repeated_groups (size : ι → ℕ) (centres : ι → K)
    (p : Polynomial.degreeLT K (∑ g, size g)) (g : ι) (i : Fin (size g)) :
    groupedConfluentData size (fun g _ => centres g) p g i =
      (Polynomial.taylor (centres g) p.1).coeff i :=
  polynomialDividedDifference_repeated_node (centres g) i p

omit [Field K] [Fintype ι] in
/-- Distinct centres give disjoint collapsed groups at every multiplicity. -/
theorem groupedNodeDisjoint_repeated_groups (size : ι → ℕ) (centres : ι → K)
    (hcentres : Function.Injective centres) :
    GroupedNodeDisjoint size (fun g _ => centres g) := by
  intro g h hgh i _ j _ heq
  exact hgh (hcentres heq)

end Algebra

section Analytic

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
/-- Strictly ordered group ranges are disjoint. Only inter-group ordering
is used; repeated entries inside a group are allowed. -/
theorem groupedNodeDisjoint_of_ordered_ranges [LinearOrder ι]
    (size : ι → ℕ) (nodes : ι → ℕ → ℝ)
    (horder : ∀ g h, g < h → ∀ i < size g, ∀ j < size h, nodes g i < nodes h j) :
    GroupedNodeDisjoint size nodes := by
  intro g h hgh i hi j hj
  rcases lt_or_gt_of_ne hgh with hlt | hgt
  · exact (horder g h hlt i hi j hj).ne
  · exact (horder h g hgt j hj i hi).ne'

/-- On real group nodes, the block map is exactly the genuine analytic
divided-difference map, including all confluent rows. -/
theorem groupedConfluentData_ofReal_eq_analyticDividedDifference
    (size : ι → ℕ) (nodes : ι → ℕ → ℝ)
    (p : Polynomial.degreeLT ℂ (∑ g, size g)) (g : ι) (i : Fin (size g)) :
    groupedConfluentData size (fun g j => (nodes g j : ℂ)) p g i =
      analyticDividedDifference (nodes g) i (fun x : ℝ => p.1.eval (x : ℂ)) :=
  (analyticDividedDifference_polynomial_eval (nodes g) i p).symm

/-- Actual analytic grouped data are unisolvent, with no distinctness
requirement inside a group. -/
theorem groupedAnalyticConfluentUnisolvence (size : ι → ℕ) (nodes : ι → ℕ → ℝ)
    (hdisjoint : GroupedNodeDisjoint size nodes) (p : ℂ[X])
    (hdegree : p ∈ Polynomial.degreeLT ℂ (∑ g, size g))
    (hdata : ∀ g, ∀ i < size g,
      analyticDividedDifference (nodes g) i (fun x : ℝ => p.eval (x : ℂ)) = 0) :
    p = 0 := by
  refine groupedConfluentUnisolvence size (fun g j => (nodes g j : ℂ)) ?_ p hdegree ?_
  · intro g h hgh i hi j hj heq
    exact hdisjoint g h hgh i hi j hj (Complex.ofReal_injective heq)
  · intro g i hi
    rw [← analyticDividedDifference_polynomial_eval]
    exact hdata g i hi

/-- The retained ordered-group unisolvence statement for genuine analytic
prefix divided differences, with all intra-group multiplicities permitted. -/
theorem groupedAnalyticConfluentUnisolvence_of_ordered_ranges [LinearOrder ι]
    (size : ι → ℕ) (nodes : ι → ℕ → ℝ)
    (horder : ∀ g h, g < h → ∀ i < size g, ∀ j < size h, nodes g i < nodes h j)
    (p : ℂ[X]) (hdegree : p ∈ Polynomial.degreeLT ℂ (∑ g, size g))
    (hdata : ∀ g, ∀ i < size g,
      analyticDividedDifference (nodes g) i (fun x : ℝ => p.eval (x : ℂ)) = 0) :
    p = 0 :=
  groupedAnalyticConfluentUnisolvence size nodes
    (groupedNodeDisjoint_of_ordered_ranges size nodes horder) p hdegree hdata

/-- Actual grouped data vary continuously with every finite node coordinate,
including configurations where nodes within a group collide. -/
theorem continuous_groupedConfluentData_finite_nodes (size : ι → ℕ)
    (p : Polynomial.degreeLT ℂ (∑ g, size g)) :
    Continuous (fun positions : (g : ι) → Fin (size g) → ℝ =>
      groupedConfluentData size
        (fun g j => (finiteNodeSequence (positions g) j : ℂ)) p) := by
  apply continuous_pi
  intro g
  apply continuous_pi
  intro i
  change Continuous (fun positions : (g : ι) → Fin (size g) → ℝ =>
    polynomialDividedDifference
      (fun j => (finiteNodeSequence (positions g) j : ℂ)) i p.1)
  simp_rw [polynomialDividedDifference_eq_hermiteGenocchi]
  apply continuous_hermiteGenocchiIntegral_parametric
  · intro j
    exact (continuous_finiteNodeSequence (size g) j).comp (continuous_apply g)
  · exact (((Polynomial.derivative^[i.val]) p.1).differentiable.continuous.comp
      Complex.continuous_ofReal).comp continuous_snd

omit [Fintype ι] in
/-- For finite node coordinates, inter-group disjointness refers precisely
to the actual entries and is unaffected by the zero extension of each row. -/
theorem groupedNodeDisjoint_finiteNodeSequence_iff (size : ι → ℕ)
    (positions : (g : ι) → Fin (size g) → ℝ) :
    GroupedNodeDisjoint size (fun g => finiteNodeSequence (positions g)) ↔
      ∀ g h, g ≠ h → ∀ i : Fin (size g), ∀ j : Fin (size h), positions g i ≠ positions h j := by
  constructor
  · intro hdisjoint g h hgh i j
    simpa only [finiteNodeSequence_apply] using hdisjoint g h hgh i i.isLt j j.isLt
  · intro hdisjoint g h hgh i hi j hj
    simpa only [finiteNodeSequence, dite_eq_left hi, dite_eq_left hj] using
      hdisjoint g h hgh ⟨i, hi⟩ ⟨j, hj⟩

/-- The actual grouped prefix map in ordinary monomial-coefficient
coordinates. Source and target are fixed finite-dimensional normed spaces. -/
def groupedCoefficientData (size : ι → ℕ)
    (positions : (g : ι) → Fin (size g) → ℝ) :
    (Fin (∑ g, size g) → ℂ) →ₗ[ℂ] ((g : ι) → Fin (size g) → ℂ) :=
  (groupedConfluentData size
    (fun g j => (finiteNodeSequence (positions g) j : ℂ))).comp
      (Polynomial.degreeLTEquiv ℂ (∑ g, size g)).symm.toLinearMap

/-- Coefficient-coordinate rows are the same actual confluent prefix data. -/
@[simp]
theorem groupedCoefficientData_apply (size : ι → ℕ)
    (positions : (g : ι) → Fin (size g) → ℝ)
    (coefficients : Fin (∑ g, size g) → ℂ) (g : ι) (i : Fin (size g)) :
    groupedCoefficientData size positions coefficients g i =
      polynomialDividedDifference
        (fun j => (finiteNodeSequence (positions g) j : ℂ)) i
        ((Polynomial.degreeLTEquiv ℂ (∑ g, size g)).symm coefficients) := rfl

/-- Inter-group disjointness proves injectivity of the actual matrix in
monomial-coefficient coordinates, without an assumed matrix inverse. -/
theorem groupedCoefficientData_injective (size : ι → ℕ)
    (positions : (g : ι) → Fin (size g) → ℝ)
    (hdisjoint : GroupedNodeDisjoint size (fun g => finiteNodeSequence (positions g))) :
    Function.Injective (groupedCoefficientData size positions) := by
  have hc : GroupedNodeDisjoint size
      (fun g j => (finiteNodeSequence (positions g) j : ℂ)) := by
    intro g h hgh i hi j hj heq
    exact hdisjoint g h hgh i hi j hj (Complex.ofReal_injective heq)
  exact (groupedConfluentData_injective size _ hc).comp
    (Polynomial.degreeLTEquiv ℂ (∑ g, size g)).symm.injective

/-- The actual coefficient matrix is a linear equivalence whenever the
groups have disjoint node ranges. Equal dimensions supply surjectivity. -/
def groupedCoefficientDataEquiv (size : ι → ℕ)
    (positions : (g : ι) → Fin (size g) → ℝ)
    (hdisjoint : GroupedNodeDisjoint size (fun g => finiteNodeSequence (positions g))) :
    (Fin (∑ g, size g) → ℂ) ≃ₗ[ℂ] ((g : ι) → Fin (size g) → ℂ) :=
  LinearEquiv.ofInjectiveOfFinrankEq (groupedCoefficientData size positions)
    (groupedCoefficientData_injective size positions hdisjoint) (by
      simp only [Module.finrank_pi, Fintype.card_fin, Module.finrank_pi_fintype])

/-- Actual grouped coefficient data are both injective and surjective,
with multiplicities counted and no intra-group separation requirement. -/
theorem groupedCoefficientData_bijective (size : ι → ℕ)
    (positions : (g : ι) → Fin (size g) → ℝ)
    (hdisjoint : GroupedNodeDisjoint size (fun g => finiteNodeSequence (positions g))) :
    Function.Bijective (groupedCoefficientData size positions) :=
  (groupedCoefficientDataEquiv size positions hdisjoint).bijective

/-- The bounded linear map associated to the actual finite coefficient
matrix. Its continuity follows from finite dimension, not a gap estimate. -/
def groupedCoefficientDataCLM (size : ι → ℕ)
    (positions : (g : ι) → Fin (size g) → ℝ) :
    (Fin (∑ g, size g) → ℂ) →L[ℂ] ((g : ι) → Fin (size g) → ℂ) :=
  (groupedCoefficientData size positions).toContinuousLinearMap

/-- The actual block coefficient operator is continuous in operator norm
across every intra-group collision. No disjointness is needed for continuity. -/
theorem continuous_groupedCoefficientDataCLM (size : ι → ℕ) :
    Continuous (groupedCoefficientDataCLM size) := by
  apply continuous_clm_apply.mpr
  intro coefficients
  exact continuous_groupedConfluentData_finite_nodes size
    ((Polynomial.degreeLTEquiv ℂ (∑ g, size g)).symm coefficients)

/-- Joint continuity of node positions and coefficients for the actual
grouped data map, suitable for compact-parameter coercivity arguments. -/
theorem continuous_groupedCoefficientData_joint (size : ι → ℕ) :
    Continuous (fun z : ((g : ι) → Fin (size g) → ℝ) × (Fin (∑ g, size g) → ℂ) =>
      groupedCoefficientData size z.1 z.2) :=
  ((continuous_groupedCoefficientDataCLM size).comp continuous_fst).clm_apply continuous_snd

end Analytic

end

end MeyerGeneralProblem
