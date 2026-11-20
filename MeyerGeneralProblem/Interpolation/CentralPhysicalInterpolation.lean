module

public import MeyerGeneralProblem.Interpolation.CanonicalExteriorInterpolation

@[expose] public section

/-!
# Whole-cluster central physical interpolation

The central set is the union of every signed-square cluster meeting the
actual central interval. It is finite by local finiteness and the proved
cluster bound, and includes the origin whenever the carrier does. The
interpolation polynomial is the genuine complex-linear Lagrange map on
these physical points, not a polynomial in the squared coordinate.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set MeasureTheory Polynomial
open scoped ContDiff ENNReal

attribute [local instance] Classical.propDecidable

namespace BoundedClusterOrder

variable {S : LocallyFiniteCarrier} {d : ℝ} {q : ℕ}
    (horder : BoundedClusterOrder S d q)

/-- The actual signed-coordinate points in the closed central interval. -/
def centralSeedPoints (R : ℝ) : Set S.subtype := {x | |(x : ℝ)| ≤ R}

/-- The seed points are finite even when the specified interval is empty. -/
theorem finite_centralSeedPoints (R : ℝ) : (centralSeedPoints (S := S) R).Finite := by
  have h := Set.Finite.preimage (f := fun x : S.subtype => (x : ℝ))
    Subtype.val_injective.injOn (S.finite_inter_Icc (-R) R)
  exact h.subset (fun x hx => ⟨x.property, abs_le.mp hx⟩)

/-- All canonical classes meeting the initial interval, including classes
straddling its boundary. -/
def centralClasses (R : ℝ) : Set (CanonicalClusterIndex S d) :=
  Quotient.mk (clusterSetoid S d) '' centralSeedPoints (S := S) R

/-- Only finitely many canonical classes meet a bounded central interval. -/
theorem finite_centralClasses (R : ℝ) : (centralClasses (S := S) (d := d) R).Finite :=
  (finite_centralSeedPoints (S := S) R).image _

/-- The whole-cluster closure of the central interval in signed coordinates. -/
def centralClusterPoints (R : ℝ) : Set S.subtype :=
  {x | Quotient.mk (clusterSetoid S d) x ∈ centralClasses (S := S) (d := d) R}

/-- Every seed point is kept in the whole-cluster central set. -/
theorem centralSeedPoints_subset (R : ℝ) :
    centralSeedPoints (S := S) R ⊆ centralClusterPoints (S := S) (d := d) R :=
  fun x hx => ⟨x, hx, rfl⟩

/-- Membership in the central set is constant on an entire canonical class. -/
theorem centralClusterPoints_iff_of_related (R : ℝ) {x y : S.subtype}
    (hxy : (clusterSetoid S d).r x y) :
    x ∈ centralClusterPoints (S := S) (d := d) R ↔
      y ∈ centralClusterPoints (S := S) (d := d) R := by
  change Quotient.mk (clusterSetoid S d) x ∈ centralClasses R ↔
    Quotient.mk (clusterSetoid S d) y ∈ centralClasses R
  rw [Quotient.sound hxy]

include horder in
/-- The corrected whole-cluster central set is genuinely finite. -/
theorem finite_centralClusterPoints (R : ℝ) :
    (centralClusterPoints (S := S) (d := d) R).Finite := by
  have h := (finite_centralClasses (S := S) (d := d) R).biUnion
    (fun C _ => (horder.clusterClass_finite_card_le C.out).1)
  apply h.subset
  intro x hx
  refine mem_iUnion₂.mpr ⟨Quotient.mk (clusterSetoid S d) x, hx, ?_⟩
  exact @Quotient.mk_out _ (clusterSetoid S d) x

end BoundedClusterOrder

namespace LocallyFiniteCarrier

variable (S : LocallyFiniteCarrier) {d : ℝ} {q : ℕ}
    (horder : BoundedClusterOrder S.signedSquareImage d q)

/-- Actual physical points in all signed-square classes meeting the central
interval. No global inverse-square-root convention is needed. -/
def centralPhysicalPoints (R : ℝ) : Set S.subtype :=
  S.signedSquareSubtypeEquiv ⁻¹'
    BoundedClusterOrder.centralClusterPoints (S := S.signedSquareImage) (d := d) R

include horder in
/-- Whole-cluster central physical points form a finite set. -/
theorem finite_centralPhysicalPoints (R : ℝ) :
    (S.centralPhysicalPoints (d := d) R).Finite :=
  Set.Finite.preimage S.signedSquareSubtypeEquiv.injective.injOn
    (horder.finite_centralClusterPoints R)

/-- The central physical finset contains whole clusters, not only the points
strictly on the central side of a transition. -/
def centralPhysicalFinset (R : ℝ) : Finset S.subtype :=
  (S.finite_centralPhysicalPoints horder R).toFinset

/-- Every actual physical point in the initial squared-radius interval is
retained. In particular this includes zero for a nonnegative radius. -/
theorem mem_centralPhysicalFinset_of_sq_le (R : ℝ) (x : S.subtype)
    (hx : (x : ℝ) ^ 2 ≤ R) : x ∈ S.centralPhysicalFinset horder R := by
  apply (S.finite_centralPhysicalPoints horder R).mem_toFinset.mpr
  apply BoundedClusterOrder.centralSeedPoints_subset R
  change |signedSquare (x : ℝ)| ≤ R
  simpa only [abs_signedSquare, sq_abs] using hx

/-- An active central cutoff is covered by the actual central finset at the
exact upper plateau radius. -/
theorem mem_centralPhysicalFinset_of_cutoff {B : ℝ} (hB : 0 < B)
    (start : ℕ) (x : S.subtype)
    (hx : 1 - blockTransition B start ((x : ℝ) ^ 2) ≠ 0) :
    x ∈ S.centralPhysicalFinset horder (((start : ℝ) + 1 / 8) * B) := by
  apply S.mem_centralPhysicalFinset_of_sq_le horder
  by_contra h
  exact hx (by rw [blockTransition_eq_one_of_plateau hB start (le_of_not_ge h), sub_self])

end LocallyFiniteCarrier

/-- The genuine finite physical Lagrange polynomial, complex-linear in its
finite data. Injectivity is needed for interpolation, not for linearity. -/
def finitePhysicalPolynomial {ι : Type*} [Fintype ι] (nodes : ι → ℝ) :
    (ι → ℂ) →ₗ[ℂ] ℂ[X] :=
  Lagrange.interpolate Finset.univ (fun i => (nodes i : ℂ))

/-- The finite physical polynomial takes exactly the supplied values. -/
theorem finitePhysicalPolynomial_eval {ι : Type*} [Fintype ι]
    (nodes : ι → ℝ) (hnodes : Function.Injective nodes) (data : ι → ℂ) (i : ι) :
    (finitePhysicalPolynomial nodes data).eval (nodes i : ℂ) = data i := by
  exact Lagrange.eval_interpolate_at_node data
    (Complex.ofReal_injective.comp hnodes).injOn (Finset.mem_univ i)

/-- The actual physical Lagrange polynomial has degree below the number of
nodes, including the empty-node case. -/
theorem finitePhysicalPolynomial_degree_lt {ι : Type*} [Fintype ι]
    (nodes : ι → ℝ) (hnodes : Function.Injective nodes) (data : ι → ℂ) :
    (finitePhysicalPolynomial nodes data).degree < Fintype.card ι := by
  exact (Lagrange.degree_interpolate_lt data
    (Complex.ofReal_injective.comp hnodes).injOn).trans_le (by simp)

/-- Evaluation of the actual finite physical polynomial as a function of
the physical variable, still linear in its data. -/
def finitePhysicalPolynomialFunction {ι : Type*} [Fintype ι] (nodes : ι → ℝ) :
    (ι → ℂ) →ₗ[ℂ] (ℝ → ℂ) where
  toFun data x := (finitePhysicalPolynomial nodes data).eval (x : ℂ)
  map_add' a b := by ext x; simp
  map_smul' a b := by ext x; simp

/-- Physical Lagrange interpolation is smooth on the whole line, including
the origin. -/
theorem contDiff_finitePhysicalPolynomialFunction {ι : Type*} [Fintype ι]
    (nodes : ι → ℝ) (data : ι → ℂ) :
    ContDiff ℝ ∞ (finitePhysicalPolynomialFunction nodes data) := by
  have h : ContDiff ℝ ∞ (fun z : ℂ => (finitePhysicalPolynomial nodes data).eval z) := by
    simpa using ((finitePhysicalPolynomial nodes data).contDiff_aeval (𝕜 := ℂ) ∞).restrict_scalars ℝ
  exact h.comp Complex.ofRealCLM.contDiff

/-- A smooth compactly supported physical function has both weighted value
and derivative energies integrable, at every finite order. -/
theorem integrable_physicalEnergy_of_smooth_compact (k : ℕ) (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    Integrable (fun x : ℝ => |x| ^ (2*k) * ‖f x‖ ^ 2) ∧
      Integrable (fun x : ℝ => ‖iteratedDeriv k f x‖ ^ 2) := by
  constructor
  · apply ((continuous_abs.pow (2*k)).mul (hf.continuous.norm.pow 2)).integrable_of_hasCompactSupport
    apply HasCompactSupport.intro hc
    intro x hx
    simp [image_eq_zero_of_notMem_tsupport hx]
  · apply ((((hf.of_le (by simp)).continuous_iteratedDeriv' k).norm).pow 2).integrable_of_hasCompactSupport
    apply HasCompactSupport.intro hc
    intro x hx
    have hz : iteratedDeriv k f x = 0 := by
      by_contra hn
      exact hx (tsupport_iteratedDeriv_subset_original k (subset_closure hn))
    simp [hz]

/-- For genuine integrable energies the ENNReal and real formulations agree. -/
theorem physicalInterpolationEnergy_eq_ofReal_integral (k : ℕ) (f : ℝ → ℂ)
    (hv : Integrable (fun x : ℝ => |x| ^ (2*k) * ‖f x‖ ^ 2))
    (hd : Integrable (fun x : ℝ => ‖iteratedDeriv k f x‖ ^ 2)) :
    physicalInterpolationEnergy k f = ENNReal.ofReal
      ((∫ x : ℝ, |x| ^ (2*k) * ‖f x‖ ^ 2) +
        (∫ x : ℝ, ‖iteratedDeriv k f x‖ ^ 2)) := by
  rw [ENNReal.ofReal_add (integral_nonneg (by intro x; positivity))
    (integral_nonneg (by intro x; positivity)),
    ofReal_integral_eq_lintegral_ofReal hv (Filter.Eventually.of_forall (by intro x; positivity)),
    ofReal_integral_eq_lintegral_ofReal hd (Filter.Eventually.of_forall (by intro x; positivity))]
  unfold physicalInterpolationEnergy
  congr 1
  apply lintegral_congr
  intro x
  exact (ENNReal.ofReal_mul (by positivity : 0 ≤ |x| ^ (2*k))).symm

private theorem norm_finite_smul_sq_le {ι : Type*} [Fintype ι]
    (data : ι → ℂ) (v : ι → ℂ) :
    ‖∑ i, data i • v i‖ ^ 2 ≤ (∑ i, ‖data i‖ ^ 2) * ∑ i, ‖v i‖ ^ 2 := by
  calc
    _ ≤ (∑ i, ‖data i‖ * ‖v i‖) ^ 2 := by
      apply pow_le_pow_left₀ (norm_nonneg _) _ 2
      simpa only [norm_smul] using norm_sum_le Finset.univ (fun i => data i • v i)
    _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

/-- A fixed genuine finite family of smooth functions supported in a common
compact set has a uniform squared-energy bound in its coefficient data.
The bound is derived from the integrals of the actual basis functions. -/
theorem exists_uniform_finiteCompact_energy_bound {ι : Type*} [Fintype ι]
    (k : ℕ) (basis : ι → ℝ → ℂ) (hb : ∀ i, ContDiff ℝ ∞ (basis i))
    (K : Set ℝ) (hK : IsCompact K) (hz : ∀ i x, x ∉ K → basis i x = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ data : ι → ℂ,
      let f := fun x : ℝ => ∑ i, data i • basis i x
      ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      Integrable (fun x : ℝ => |x| ^ (2*k) * ‖f x‖ ^ 2) ∧
      Integrable (fun x : ℝ => ‖iteratedDeriv k f x‖ ^ 2) ∧
      (∫ x : ℝ, |x| ^ (2*k) * ‖f x‖ ^ 2) +
        (∫ x : ℝ, ‖iteratedDeriv k f x‖ ^ 2) ≤ C * ∑ i, ‖data i‖ ^ 2 ∧
      physicalInterpolationEnergy k f ≤ ENNReal.ofReal C * ENNReal.ofReal (∑ i, ‖data i‖ ^ 2) := by
  have hint (i : ι) := integrable_physicalEnergy_of_smooth_compact k (basis i) (hb i)
    (HasCompactSupport.intro hK (hz i))
  let e (i : ι) : ℝ := (∫ x : ℝ, |x| ^ (2*k) * ‖basis i x‖ ^ 2) +
    (∫ x : ℝ, ‖iteratedDeriv k (basis i) x‖ ^ 2)
  have he (i : ι) : 0 ≤ e i := add_nonneg
    (integral_nonneg (by intro x; positivity)) (integral_nonneg (by intro x; positivity))
  have heSum : 0 ≤ ∑ i, e i := Finset.sum_nonneg (fun i _ => he i)
  refine ⟨1 + ∑ i, e i, by positivity, ?_⟩
  intro data
  let f := fun x : ℝ => ∑ i, data i • basis i x
  have hf : ContDiff ℝ ∞ f := ContDiff.sum (fun i _ => (hb i).const_smul (data i))
  have hc : HasCompactSupport f := HasCompactSupport.intro hK (by
    intro x hx
    simp only [f, hz _ _ hx, smul_zero, Finset.sum_const_zero])
  obtain ⟨hv, hd⟩ := integrable_physicalEnergy_of_smooth_compact k f hf hc
  have hderiv (x : ℝ) : iteratedDeriv k f x = ∑ i, data i • iteratedDeriv k (basis i) x := by
    rw [show f = fun x : ℝ => ∑ i, data i • basis i x from rfl,
      iteratedDeriv_fun_sum (fun i _ => ((hb i).const_smul (data i)).contDiffAt.of_le (by simp))]
    apply Finset.sum_congr rfl
    intro i _
    exact iteratedDeriv_const_smul_field (data i) (basis i)
  let D : ℝ := ∑ i, ‖data i‖ ^ 2
  have hD : 0 ≤ D := Finset.sum_nonneg (by intro i _; positivity)
  have hbound : (∫ x : ℝ, |x| ^ (2*k) * ‖f x‖ ^ 2) +
      (∫ x : ℝ, ‖iteratedDeriv k f x‖ ^ 2) ≤ D * ∑ i, e i := by
    have hsumInt : Integrable (fun x : ℝ => ∑ i,
        (|x| ^ (2*k) * ‖basis i x‖ ^ 2 + ‖iteratedDeriv k (basis i) x‖ ^ 2)) :=
      integrable_finsetSum _ (fun i _ => (hint i).1.add (hint i).2)
    have hsumEq : (∫ x : ℝ, ∑ i,
        (|x| ^ (2*k) * ‖basis i x‖ ^ 2 + ‖iteratedDeriv k (basis i) x‖ ^ 2)) = ∑ i, e i := by
      rw [integral_finsetSum (f := fun i x =>
        |x| ^ (2*k) * ‖basis i x‖ ^ 2 + ‖iteratedDeriv k (basis i) x‖ ^ 2)
        Finset.univ (fun i _ => (hint i).1.add (hint i).2)]
      exact Finset.sum_congr rfl (fun i _ => integral_add (hint i).1 (hint i).2)
    rw [← integral_add hv hd, ← hsumEq, ← integral_const_mul]
    apply integral_mono (hv.add hd) (hsumInt.const_mul D)
    intro x
    simp only [Pi.add_apply]
    have hval := norm_finite_smul_sq_le data (fun i => basis i x)
    have hder := norm_finite_smul_sq_le data (fun i => iteratedDeriv k (basis i) x)
    rw [hderiv x]
    calc
      _ ≤ |x| ^ (2*k) * (D * ∑ i, ‖basis i x‖ ^ 2) +
          D * ∑ i, ‖iteratedDeriv k (basis i) x‖ ^ 2 :=
        add_le_add (mul_le_mul_of_nonneg_left hval (by positivity)) hder
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum]; ring
  have hfinal : (∫ x : ℝ, |x| ^ (2*k) * ‖f x‖ ^ 2) +
      (∫ x : ℝ, ‖iteratedDeriv k f x‖ ^ 2) ≤ (1 + ∑ i, e i) * D :=
    hbound.trans (by nlinarith)
  refine ⟨hf, hc, hv, hd, hfinal, ?_⟩
  rw [physicalInterpolationEnergy_eq_ofReal_integral k f hv hd,
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 + ∑ i, e i)]
  exact ENNReal.ofReal_le_ofReal hfinal

/-- The central cutoff times the physical polynomial is a complex-linear
map of the finite data into actual functions on the line. -/
def centralPhysicalInterpolant {ι : Type*} [Fintype ι]
    (B : ℝ) (start : ℕ) (nodes : ι → ℝ) : (ι → ℂ) →ₗ[ℂ] (ℝ → ℂ) where
  toFun data x := (1 - blockTransition B start (x^2)) •
    finitePhysicalPolynomialFunction nodes data x
  map_add' a b := by ext x; simp
  map_smul' a b := by ext x; simp; ring

/-- The actual cutoff Lagrange basis, with no abstract interpolation-bound
certificate. -/
def centralPhysicalBasis {ι : Type*} [Fintype ι]
    (B : ℝ) (start : ℕ) (nodes : ι → ℝ) (i : ι) (x : ℝ) : ℂ :=
  (1 - blockTransition B start (x^2)) •
    (Lagrange.basis Finset.univ (fun j => (nodes j : ℂ)) i).eval (x : ℂ)

/-- The cutoff polynomial is the finite combination of its actual basis. -/
theorem centralPhysicalInterpolant_eq_sum {ι : Type*} [Fintype ι]
    (B : ℝ) (start : ℕ) (nodes : ι → ℝ) (data : ι → ℂ) (x : ℝ) :
    centralPhysicalInterpolant B start nodes data x =
      ∑ i, data i • centralPhysicalBasis B start nodes i x := by
  simp only [centralPhysicalInterpolant, LinearMap.coe_mk, AddHom.coe_mk,
    finitePhysicalPolynomialFunction, finitePhysicalPolynomial, Lagrange.interpolate_apply,
    eval_finsetSum, eval_mul, eval_C, Finset.smul_sum, centralPhysicalBasis]
  exact Finset.sum_congr rfl (fun i _ => by rw [smul_comm]; rfl)

/-- Every actual central basis function is smooth, including at zero. -/
theorem contDiff_centralPhysicalBasis {ι : Type*} [Fintype ι]
    (B : ℝ) (start : ℕ) (nodes : ι → ℝ) (i : ι) :
    ContDiff ℝ ∞ (centralPhysicalBasis B start nodes i) := by
  have hp : ContDiff ℝ ∞ (fun x : ℝ =>
      (Lagrange.basis Finset.univ (fun j => (nodes j : ℂ)) i).eval (x : ℂ)) := by
    have hc : ContDiff ℝ ∞ (fun z : ℂ =>
        (Lagrange.basis Finset.univ (fun j => (nodes j : ℂ)) i).eval z) := by
      simpa using ((Lagrange.basis Finset.univ (fun j => (nodes j : ℂ)) i).contDiff_aeval
        (𝕜 := ℂ) ∞).restrict_scalars ℝ
    exact hc.comp Complex.ofRealCLM.contDiff
  exact (contDiff_const.sub ((contDiff_blockTransition B start).comp (by fun_prop))).smul hp

/-- All central basis functions have the same explicit bounded support.
This estimate concerns the physical variable and remains valid at zero. -/
theorem centralPhysicalBasis_eq_zero_outside {ι : Type*} [Fintype ι]
    {B : ℝ} (hB : 0 < B) (start : ℕ) (nodes : ι → ℝ) (i : ι)
    (x : ℝ) (hx : x ∉ Icc (-(|((start : ℝ) + 1 / 8) * B| + 1))
      (|((start : ℝ) + 1 / 8) * B| + 1)) :
    centralPhysicalBasis B start nodes i x = 0 := by
  have hx' : |((start : ℝ) + 1 / 8) * B| + 1 < |x| :=
    lt_of_not_ge (fun h => hx (abs_le.mp h))
  have hp : ((start : ℝ) + 1 / 8) * B ≤ x^2 := by
    have ha := abs_nonneg (((start : ℝ) + 1 / 8) * B)
    have hb := le_abs_self (((start : ℝ) + 1 / 8) * B)
    nlinarith [sq_abs x]
  simp only [centralPhysicalBasis, blockTransition_eq_one_of_plateau hB start hp,
    sub_self, zero_smul]

/-- The actual central interpolation map has a bounded finite-data energy
constant chosen before the data. No minimum-gap bound is assumed: dependence
on the fixed central physical nodes is allowed, as in the retained source. -/
theorem exists_uniform_centralPhysical_energy_bound {ι : Type*} [Fintype ι]
    (k : ℕ) {B : ℝ} (hB : 0 < B) (start : ℕ) (nodes : ι → ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ data : ι → ℂ,
      let f := centralPhysicalInterpolant B start nodes data
      ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      Integrable (fun x : ℝ => |x| ^ (2*k) * ‖f x‖ ^ 2) ∧
      Integrable (fun x : ℝ => ‖iteratedDeriv k f x‖ ^ 2) ∧
      (∫ x : ℝ, |x| ^ (2*k) * ‖f x‖ ^ 2) +
        (∫ x : ℝ, ‖iteratedDeriv k f x‖ ^ 2) ≤ C * ∑ i, ‖data i‖ ^ 2 ∧
      physicalInterpolationEnergy k f ≤ ENNReal.ofReal C * ENNReal.ofReal (∑ i, ‖data i‖ ^ 2) := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_finiteCompact_energy_bound k
    (centralPhysicalBasis B start nodes) (contDiff_centralPhysicalBasis B start nodes)
    _ isCompact_Icc (centralPhysicalBasis_eq_zero_outside hB start nodes)
  refine ⟨C, hC, ?_⟩
  intro data
  have heq : centralPhysicalInterpolant B start nodes data =
      fun x => ∑ i, data i • centralPhysicalBasis B start nodes i x := by
    funext x
    exact centralPhysicalInterpolant_eq_sum B start nodes data x
  simpa only [heq] using hbound data

/-- Exact central transition-weighted interpolation at every supplied
physical node. The plateau and origin are not excluded. -/
theorem centralPhysicalInterpolant_eval {ι : Type*} [Fintype ι]
    (B : ℝ) (start : ℕ) (nodes : ι → ℝ) (hnodes : Function.Injective nodes)
    (data : ι → ℂ) (i : ι) :
    centralPhysicalInterpolant B start nodes data (nodes i) =
      (1 - blockTransition B start ((nodes i)^2)) • data i := by
  change (1 - blockTransition B start ((nodes i)^2)) •
    (finitePhysicalPolynomial nodes data).eval (nodes i : ℂ) = _
  rw [finitePhysicalPolynomial_eval nodes hnodes data i]

namespace LocallyFiniteCarrier

variable (S : LocallyFiniteCarrier) {d : ℝ} {q : ℕ}
    (horder : BoundedClusterOrder S.signedSquareImage d q)

/-- Physical coordinates of the finite central data space. -/
def centralPhysicalNode (R : ℝ) (i : S.centralPhysicalFinset horder R) : ℝ := i.val

/-- No multiplicity is introduced by the whole-cluster central selection. -/
theorem centralPhysicalNode_injective (R : ℝ) :
    Function.Injective (S.centralPhysicalNode horder R) := by
  intro i j hij
  exact Subtype.ext (Subtype.ext hij)

/-- The actual whole-cluster central polynomial is a finite-data linear map. -/
def canonicalCentralPolynomial (R : ℝ) :
    (S.centralPhysicalFinset horder R → ℂ) →ₗ[ℂ] ℂ[X] :=
  finitePhysicalPolynomial (S.centralPhysicalNode horder R)

/-- The constructed whole-cluster polynomial interpolates every retained
central point, not merely the seed points. -/
theorem canonicalCentralPolynomial_eval (R : ℝ)
    (data : S.centralPhysicalFinset horder R → ℂ) (i : S.centralPhysicalFinset horder R) :
    (S.canonicalCentralPolynomial horder R data).eval (i.val : ℂ) = data i :=
  finitePhysicalPolynomial_eval _ (S.centralPhysicalNode_injective horder R) data i

/-- Whole-cluster physical central interpolation gives the required active
central value at every carrier point; the same actual linear map has a
finite-data energy bound, with a constant independent of the input data. -/
theorem exists_canonicalCentral_interpolation_energy (k : ℕ) {B : ℝ}
    (hB : 0 < B) (start : ℕ) :
    let R := ((start : ℝ) + 1/8) * B
    ∃ C : ℝ, 0 < C ∧ ∀ g : ℝ → ℂ,
      let data := fun i : S.centralPhysicalFinset horder R => g i.val
      let p := S.canonicalCentralPolynomial horder R data
      let f := centralPhysicalInterpolant B start (S.centralPhysicalNode horder R) data
      (∀ x : S.subtype, 1 - blockTransition B start ((x : ℝ)^2) ≠ 0 →
        p.eval (x : ℂ) = g x) ∧
      ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      Integrable (fun x : ℝ => |x| ^ (2*k) * ‖f x‖ ^ 2) ∧
      Integrable (fun x : ℝ => ‖iteratedDeriv k f x‖ ^ 2) ∧
      (∫ x : ℝ, |x| ^ (2*k) * ‖f x‖ ^ 2) +
        (∫ x : ℝ, ‖iteratedDeriv k f x‖ ^ 2) ≤ C * ∑ i, ‖data i‖ ^ 2 ∧
      physicalInterpolationEnergy k f ≤ ENNReal.ofReal C * ENNReal.ofReal (∑ i, ‖data i‖ ^ 2) := by
  dsimp only
  obtain ⟨C, hC, hbound⟩ := exists_uniform_centralPhysical_energy_bound k hB start
    (S.centralPhysicalNode horder (((start : ℝ) + 1/8) * B))
  refine ⟨C, hC, ?_⟩
  intro g
  refine ⟨?_, hbound _⟩
  intro x hx
  exact S.canonicalCentralPolynomial_eval horder _ _
    ⟨x, S.mem_centralPhysicalFinset_of_cutoff horder hB start x hx⟩

end LocallyFiniteCarrier

end

end MeyerGeneralProblem
