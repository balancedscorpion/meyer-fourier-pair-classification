module

public import MeyerGeneralProblem.Gram.GroupedGramKernel
public import MeyerGeneralProblem.Cross.NormalizedRemainder

@[expose] public section

/-!
# Exact peeling of the actual grouped normalizer

The divided-difference product rule below applies to arbitrary functions at
distinct nodes. It is proved using the actual interpolating polynomials,
not postulated for a formal symbol. The resulting factors are the divided
differences of the actual Dirac norm divided by the fixed anchor norm.

Our finite lists increase in signed-square order. On the negative ray the
first point need not be the smallest-modulus anchor: the zeroth peeling
factor is therefore a ratio tending to one, not identically one. No
differentiated Mehler remainder or compactness is assumed here.
-/

namespace MeyerGeneralProblem

noncomputable section

open Finset Polynomial
open scoped Topology

/-- Exact product rule at distinct prefix nodes. No regularity is needed:
the polynomial interpolants have the same values at every tested node. -/
theorem groupedAnalyticDividedDifference_leibniz_of_distinct
    (nodes : ℕ → ℝ) (order : ℕ) (f g : ℝ → ℂ)
    (hnode : ∀ i ≤ order, ∀ j ≤ order, i ≠ j → nodes i ≠ nodes j) :
    analyticDividedDifference nodes order (fun x => f x * g x) =
      ∑ k ∈ range (order + 1), analyticDividedDifference nodes k f *
        analyticDividedDifference (fun i => nodes (i + k)) (order - k) g := by
  let z : Fin (order + 1) → ℂ := fun i => (nodes i : ℂ)
  have hz : Function.Injective z := by
    intro i j hij
    apply Fin.ext
    by_contra h
    exact hnode i (by omega) j (by omega) h (Complex.ofReal_injective hij)
  let p := newtonInterpolantFromValues z hz (fun i => f (nodes i))
  let q := newtonInterpolantFromValues z hz (fun i => g (nodes i))
  have hp (i : ℕ) (hi : i ≤ order) : p.eval (nodes i : ℂ) = f (nodes i) :=
    eval_newtonInterpolantFromValues_at_node z hz _ ⟨i, by omega⟩
  have hq (i : ℕ) (hi : i ≤ order) : q.eval (nodes i : ℂ) = g (nodes i) :=
    eval_newtonInterpolantFromValues_at_node z hz _ ⟨i, by omega⟩
  have hfg := analyticDividedDifference_congr_values_of_distinct nodes order
    (fun x => f x * g x) (fun x => (p*q).eval (x : ℂ)) hnode (by
      intro i hi
      simp only [Polynomial.eval_mul, hp i hi, hq i hi])
  rw [hfg, analyticDividedDifference_polynomial_eval, dividedDifference_leibniz]
  apply sum_congr rfl
  intro k hk
  have hk' : k ≤ order := by have := mem_range.mp hk; omega
  congr 1
  · rw [← analyticDividedDifference_polynomial_eval]
    apply analyticDividedDifference_congr_values_of_distinct
    · intro i hi j hj hij
      exact hnode i (hi.trans hk') j (hj.trans hk') hij
    · intro i hi
      exact hp i (hi.trans hk')
  · rw [← analyticDividedDifference_polynomial_eval]
    apply analyticDividedDifference_congr_values_of_distinct
    · intro i hi j hj hij
      exact hnode (i+k) (by omega) (j+k) (by omega) (by omega)
    · intro i hi
      exact hq (i+k) (by omega)

/-- A finite segment of the actual node list, with its original ordering. -/
def groupedSublistDividedDifference {n : ℕ} (nodes : Fin n → ℝ)
    (start finish : Fin n) (f : ℝ → ℂ) : ℂ :=
  analyticDividedDifference (fun i => finiteNodeSequence nodes (i + start.val))
    (finish.val - start.val) f

/-- A segment only uses the declared consecutive finite node list. -/
theorem groupedSublistDividedDifference_eq_finite {n : ℕ}
    (nodes : Fin n → ℝ) (hnodes : Function.Injective nodes)
    (start finish : Fin n) (h : start ≤ finish) (f : ℝ → ℂ) :
    groupedSublistDividedDifference nodes start finish f =
      groupedRealDividedDifference
        (fun i : Fin (finish.val-start.val+1) => nodes ⟨i.val+start.val, by omega⟩)
        (Fin.last (finish.val-start.val)) f := by
  unfold groupedSublistDividedDifference
  have hn : Function.Injective (fun i : Fin (finish.val-start.val+1) =>
      (i.val+start.val : ℕ)) := by
    intro a b hab
    apply Fin.ext
    dsimp only at hab
    omega
  rw [groupedRealDividedDifference_eq_analytic]
  · apply analyticDividedDifference_congr_nodes
    intro i hi
    simp only [finiteNodeSequence, dite_eq_left (show i+start.val<n by omega),
      dite_eq_left (show i<finish.val-start.val+1 by omega)]
  · intro a b hab
    exact hn (congrArg Fin.val (hnodes hab))

/-- Initial-segment peeling into a genuine prefix factor and a genuine
suffix divided difference, retaining the shared split node. -/
theorem groupedRealDividedDifference_leibniz {n : ℕ}
    (nodes : Fin n → ℝ) (hnodes : Function.Injective nodes) (j : Fin n)
    (f g : ℝ → ℂ) :
    groupedRealDividedDifference nodes j (fun x => f x * g x) =
      ∑ i ∈ Iic j, groupedRealDividedDifference nodes i f *
        groupedSublistDividedDifference nodes i j g := by
  rw [groupedRealDividedDifference_eq_analytic nodes hnodes]
  rw [groupedAnalyticDividedDifference_leibniz_of_distinct]
  · apply Finset.sum_bij (fun k hk => (⟨k, (show k ≤ j.val by
        have := mem_range.mp hk; omega).trans_lt j.isLt⟩ : Fin n))
    · intro k hk
      simp only [mem_Iic, Fin.le_iff_val_le_val]
      have := mem_range.mp hk
      omega
    · intro a ha b hb hab
      exact congrArg Fin.val hab
    · intro i hi
      refine ⟨i.val, mem_range.mpr (by have := mem_Iic.mp hi; omega), ?_⟩
      rfl
    · intro k hk
      simp only [groupedSublistDividedDifference,
        groupedRealDividedDifference_eq_analytic nodes hnodes]
  · intro a ha b hb hab heq
    have han : a < n := ha.trans_lt j.isLt
    have hbn : b < n := hb.trans_lt j.isLt
    simp only [finiteNodeSequence, dite_eq_left han, dite_eq_left hbn] at heq
    exact hab (congrArg Fin.val (hnodes heq))

/-- Finite sums commute with the actual barycentric prefix functional. -/
theorem groupedRealDividedDifference_sum {n : ℕ} {ι : Type*}
    (nodes : Fin n → ℝ) (j : Fin n) (s : Finset ι) (f : ι → ℝ → ℂ) :
    groupedRealDividedDifference nodes j (fun x => ∑ i ∈ s, f i x) =
      ∑ i ∈ s, groupedRealDividedDifference nodes j (f i) := by
  simp only [groupedRealDividedDifference, mul_sum]
  exact sum_comm

/-- A constant complex factor pulls through the actual prefix functional. -/
theorem groupedRealDividedDifference_const_mul {n : ℕ}
    (nodes : Fin n → ℝ) (j : Fin n) (c : ℂ) (f : ℝ → ℂ) :
    groupedRealDividedDifference nodes j (fun x => c*f x) =
      c*groupedRealDividedDifference nodes j f := by
  simp only [groupedRealDividedDifference, mul_sum]
  apply sum_congr rfl
  intro i _
  ring

/-- A constant factor also pulls through every genuine distinct-node
suffix appearing in the product rule. -/
theorem groupedSublistDividedDifference_const_mul {n : ℕ}
    (nodes : Fin n → ℝ) (hnodes : Function.Injective nodes)
    (start finish : Fin n) (h : start ≤ finish) (c : ℂ) (f : ℝ → ℂ) :
    groupedSublistDividedDifference nodes start finish (fun x => c*f x) =
      c*groupedSublistDividedDifference nodes start finish f := by
  simp only [groupedSublistDividedDifference_eq_finite nodes hnodes start finish h,
    groupedRealDividedDifference_const_mul]

/-- Exact two-variable weight peeling. The remainder function is one
function of the two independent variables, not a cluster-pair-dependent
replacement. All suffixes share the split node with their prefix. -/
theorem groupedDoubleDividedDifference_leibniz {n k : ℕ}
    (nodes : Fin n → ℝ) (other : Fin k → ℝ)
    (hnodes : Function.Injective nodes) (hother : Function.Injective other)
    (i : Fin n) (j : Fin k) (w v : ℝ → ℂ) (F : ℝ → ℝ → ℂ) :
    groupedDoubleDividedDifference nodes other i j (fun s t => w s*v t*F s t) =
      ∑ a ∈ Iic i, ∑ b ∈ Iic j,
        groupedRealDividedDifference nodes a w *
          groupedRealDividedDifference other b v *
            groupedSublistDividedDifference nodes a i (fun s =>
              groupedSublistDividedDifference other b j (F s)) := by
  unfold groupedDoubleDividedDifference
  have hin (s : ℝ) : groupedRealDividedDifference other j
      (fun t => w s*v t*F s t) =
      ∑ b ∈ Iic j, (w s*groupedRealDividedDifference other b v)*
        groupedSublistDividedDifference other b j (F s) := by
    simp only [mul_assoc]
    rw [groupedRealDividedDifference_const_mul,
      groupedRealDividedDifference_leibniz other hother, mul_sum]
  simp_rw [hin]
  rw [groupedRealDividedDifference_sum]
  have hout (b : Fin k) (hb : b ∈ Iic j) :
      groupedRealDividedDifference nodes i (fun s =>
        (w s*groupedRealDividedDifference other b v)*
          groupedSublistDividedDifference other b j (F s)) =
      ∑ a ∈ Iic i, groupedRealDividedDifference nodes a w *
        groupedRealDividedDifference other b v *
          groupedSublistDividedDifference nodes a i (fun s =>
            groupedSublistDividedDifference other b j (F s)) := by
    simp only [mul_assoc]
    rw [groupedRealDividedDifference_leibniz nodes hnodes]
    apply sum_congr rfl
    intro a ha
    rw [groupedSublistDividedDifference_const_mul nodes hnodes a i (mem_Iic.mp ha)]
  rw [sum_congr rfl hout, sum_comm]

/-- The exact coefficient arising when the fixed anchor normalization is
peeled from a prefix of magnitude nodes. -/
def groupedNormalizerPeelingCoefficient (m : ℕ) (hm : 1 ≤ m)
    {n : ℕ} (nodes : Fin n → ℝ) (j : Fin n) (anchor : ℝ) : ℂ :=
  groupedRealDividedDifference nodes j
    (fun s => (groupedNormalizerRatio m hm anchor s : ℂ))

/-- Uniform, inverse-gap-free normalizer coefficient bound for every
finite prefix. The constant depends only on the order and physical scale. -/
theorem norm_groupedNormalizerPeelingCoefficient_le
    (m : ℕ) (hm : 1 ≤ m) (q : ℕ) {n : ℕ}
    (nodes : Fin n → ℝ) (hnodes : Function.Injective nodes)
    (j : Fin n) (hj : j.val ≤ q) {a U : ℝ} (ha : 1 ≤ a)
    (hnode : ∀ i, nodes i ∈ Set.Icc a U) :
    ‖groupedNormalizerPeelingCoefficient m hm nodes j a‖ ≤
      (groupedNormalizerDerivativeConstant m q / a^j.val) / j.val.factorial := by
  apply norm_groupedRealDividedDifference_le_positive nodes hnodes j
    (fun s => (groupedNormalizerRatio m hm a s : ℂ))
  · intro x hx
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp x
      (contDiffAt_groupedNormalizerRatio m hm j.val a x hx)
  · exact ha
  · exact hnode
  · intro x hx
    have heq : iteratedDeriv j.val (fun s => (groupedNormalizerRatio m hm a s : ℂ)) x =
        ((iteratedDeriv j.val (groupedNormalizerRatio m hm a) x : ℝ) : ℂ) := by
      simp only [iteratedDeriv]
      change (iteratedFDeriv ℝ j.val (Complex.ofRealCLM ∘ groupedNormalizerRatio m hm a) x)
        (fun _ => 1) = _
      rw [Complex.ofRealCLM.iteratedFDeriv_comp_left
        (contDiffAt_groupedNormalizerRatio m hm j.val a x (by linarith [hx.1])) le_rfl]
      rfl
    rw [heq]
    simpa only [Complex.norm_real] using
      norm_iteratedDeriv_groupedNormalizerRatio_le m hm q j.val hj ha hx.1

/-- Every positive-order peeling factor tends to zero uniformly in the
whole finite node pattern; neither a node gap nor its reciprocal occurs. -/
theorem norm_groupedNormalizerPeelingCoefficient_le_inv
    (m : ℕ) (hm : 1 ≤ m) (q : ℕ) {n : ℕ}
    (nodes : Fin n → ℝ) (hnodes : Function.Injective nodes)
    (j : Fin n) (hj : j.val ≤ q) (hjpos : 0 < j.val)
    {a U : ℝ} (ha : 1 ≤ a) (hnode : ∀ i, nodes i ∈ Set.Icc a U) :
    ‖groupedNormalizerPeelingCoefficient m hm nodes j a‖ ≤
      groupedNormalizerDerivativeConstant m q / a := by
  have hC := (groupedNormalizerDerivativeConstant_pos m hm q).le
  have hfac : (1 : ℝ) ≤ j.val.factorial := by exact_mod_cast Nat.factorial_pos j.val
  have hpow : a ≤ a^j.val := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j.val ≠ 0)
    rw [hk, pow_succ]
    exact le_mul_of_one_le_left (by linarith) (one_le_pow₀ ha)
  calc
    _ ≤ (groupedNormalizerDerivativeConstant m q / a^j.val) / j.val.factorial :=
      norm_groupedNormalizerPeelingCoefficient_le m hm q nodes hnodes j hj ha hnode
    _ ≤ groupedNormalizerDerivativeConstant m q / a^j.val :=
      div_le_self (by positivity) hfac
    _ ≤ groupedNormalizerDerivativeConstant m q / a :=
      div_le_div_of_nonneg_left hC (by linarith) hpow

/-- The zeroth coefficient is the actual first-node/anchor ratio. This
does not identify the first node with the anchor on the negative ray. -/
theorem groupedNormalizerPeelingCoefficient_zero (m : ℕ) (hm : 1 ≤ m)
    {n : ℕ} (nodes : Fin (n+1) → ℝ) (hnodes : Function.Injective nodes) (a : ℝ) :
    groupedNormalizerPeelingCoefficient m hm nodes 0 a =
      (groupedNormalizerRatio m hm a (nodes 0) : ℂ) := by
  rw [groupedNormalizerPeelingCoefficient,
    groupedRealDividedDifference_eq_analytic nodes hnodes]
  simp only [Fin.val_zero, analyticDividedDifference_zero]
  simp only [finiteNodeSequence, dite_eq_left (show 0 < n+1 by omega)]
  rfl

/-- The zeroth coefficient differs from one by a uniformly small
quantity on any fixed-diameter tail group, in either node ordering. -/
theorem norm_groupedNormalizerPeelingCoefficient_zero_sub_one_le
    (m : ℕ) (hm : 1 ≤ m) {n : ℕ}
    (nodes : Fin (n+1) → ℝ) (hnodes : Function.Injective nodes)
    {a D : ℝ} (ha : 1 ≤ a) (hnode : ∀ i, nodes i ∈ Set.Icc a (a+D)) :
    ‖groupedNormalizerPeelingCoefficient m hm nodes 0 a-1‖ ≤
      (groupedNormalizerDerivativeConstant m 1/a)*D := by
  rw [groupedNormalizerPeelingCoefficient_zero m hm nodes hnodes]
  simpa only [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real] using
    norm_groupedNormalizerRatio_sub_one_le m hm ha (hnode 0).1 (hnode 0).2

/-- The actual cross resolvent at ray points, normalized at two fixed
anchors rather than separately at every evaluation point. -/
def groupedAnchorNormalizedCrossKernel (m : ℕ) (hm : 1 ≤ m)
    (ε η a b s t : ℝ) : ℂ :=
  (‖hermitePointMass m hm (Real.sqrt a)‖⁻¹ *
      ‖hermitePointMass m hm (Real.sqrt b)‖⁻¹) •
    hermiteCrossResolventKernel m (ε*Real.sqrt s) (η*Real.sqrt t)

/-- Exact restoration of point normalization in the genuine cross
kernel, with independent ray signs and independent magnitude variables. -/
theorem groupedAnchorNormalizedCrossKernel_eq_ratios
    (m : ℕ) (hm : 1 ≤ m) (ε η a b s t : ℝ) (hε : ε^2=1) (hη : η^2=1) :
    groupedAnchorNormalizedCrossKernel m hm ε η a b s t =
      (groupedNormalizerRatio m hm a s : ℂ) *
        (groupedNormalizerRatio m hm b t : ℂ) *
          normalizedHermiteCrossKernel m hm (ε*Real.sqrt s) (η*Real.sqrt t) := by
  unfold groupedAnchorNormalizedCrossKernel normalizedHermiteCrossKernel
  rw [norm_hermitePointMass_sign_sqrt m hm ε s hε,
    norm_hermitePointMass_sign_sqrt m hm η t hη]
  unfold groupedNormalizerRatio
  simp only [Complex.real_smul]
  have hs := (norm_pos_iff.mpr (hermitePointMass_ne_zero m hm (Real.sqrt s))).ne'
  have ht := (norm_pos_iff.mpr (hermitePointMass_ne_zero m hm (Real.sqrt t))).ne'
  push_cast
  field_simp [hs, ht]

/-- The exact corrected source peeling formula for actual cross kernels.
It holds for every prefix in the same physical Hermite order. -/
theorem groupedAnchorNormalizedCrossKernel_DD_peeling
    (m : ℕ) (hm : 1 ≤ m) {n k : ℕ}
    (nodes : Fin n → ℝ) (other : Fin k → ℝ)
    (hnodes : Function.Injective nodes) (hother : Function.Injective other)
    (i : Fin n) (j : Fin k) (ε η a b : ℝ) (hε : ε^2=1) (hη : η^2=1) :
    groupedDoubleDividedDifference nodes other i j
      (groupedAnchorNormalizedCrossKernel m hm ε η a b) =
      ∑ u ∈ Iic i, ∑ v ∈ Iic j,
        groupedNormalizerPeelingCoefficient m hm nodes u a *
          groupedNormalizerPeelingCoefficient m hm other v b *
            groupedSublistDividedDifference nodes u i (fun s =>
              groupedSublistDividedDifference other v j (fun t =>
                normalizedHermiteCrossKernel m hm (ε*Real.sqrt s) (η*Real.sqrt t))) := by
  rw [show groupedAnchorNormalizedCrossKernel m hm ε η a b =
    (fun s t => (groupedNormalizerRatio m hm a s : ℂ) *
      (groupedNormalizerRatio m hm b t : ℂ) *
        normalizedHermiteCrossKernel m hm (ε*Real.sqrt s) (η*Real.sqrt t)) from
    funext (fun s => funext (fun t =>
      groupedAnchorNormalizedCrossKernel_eq_ratios m hm ε η a b s t hε hη))]
  exact groupedDoubleDividedDifference_leibniz nodes other hnodes hother i j _ _ _

namespace OrderedCarrierGrouping

variable {S : LocallyFiniteCarrier} {κ : Type*} (G : OrderedCarrierGrouping S κ)

/-- The actual physical/Fourier grouped Hilbert cross entry. The
Fourier convention is the existing phase-weighted resolvent convention. -/
def crossKernel (m : ℕ) (hm : 1 ≤ m) (x y : G.Index) : ℂ :=
  inner ℂ (G.atom m hm x) (hermiteFourier (-(m:ℤ)) (G.atom m hm y))

/-- Exact finite expansion of the actual cross entry; both fixed anchor
weights are retained outside the barycentric sum. -/
theorem crossKernel_eq_weighted_sum (m : ℕ) (hm : 1 ≤ m)
    (C D : κ) (i : Fin (G.size C)) (j : Fin (G.size D)) :
    G.crossKernel m hm ⟨C,i⟩ ⟨D,j⟩ =
      ((G.weight m hm C)⁻¹ : ℂ)*((G.weight m hm D)⁻¹ : ℂ)*
        ∑ a, ∑ b, (groupedNewtonWeight (K := ℝ) (G.realNodes C) i a : ℂ)*
          (groupedNewtonWeight (K := ℝ) (G.realNodes D) j b : ℂ)*
            hermiteCrossResolventKernel m (G.point C a) (G.point D b) := by
  simp only [crossKernel, atom, rawAtom, groupedFiniteAtom, map_smul, map_sum,
    inner_smul_left, inner_smul_right, inner_sum, sum_inner,
    map_inv₀, Complex.conj_ofReal,
    inner_hermitePointMass_hermiteFourier_eq_crossResolventKernel, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  have hC := groupedNewtonWeight_ofReal (G.realNodes C) i a
  have hD := groupedNewtonWeight_ofReal (G.realNodes D) j b
  change groupedNewtonWeight (G.nodes C) i a = _ at hC
  change groupedNewtonWeight (G.nodes D) j b = _ at hD
  rw [hC, hD, Complex.conj_ofReal]
  ring

/-- The actual grouped cross entry is exactly the two-variable
magnitude DD of the anchor-normalized raw cross kernel. Negative ray
orientation contributes only the displayed signs, never a node-gap factor. -/
theorem crossKernel_eq_magnitude_DD (m : ℕ) (hm : 1 ≤ m)
    (ε η : ℝ) (hε : ε^2=1) (hη : η^2=1)
    (C D : κ) (i : Fin (G.size C)) (j : Fin (G.size D))
    (hC : ∀ a, 0 ≤ G.magnitudeNodes ε C a) (hD : ∀ b, 0 ≤ G.magnitudeNodes η D b) :
    G.crossKernel m hm ⟨C,i⟩ ⟨D,j⟩ =
      (ε^i.val*η^j.val) • groupedDoubleDividedDifference
        (G.magnitudeNodes ε C) (G.magnitudeNodes η D) i j
        (groupedAnchorNormalizedCrossKernel m hm ε η
          (G.anchorMagnitude ε C) (G.anchorMagnitude η D)) := by
  rw [G.crossKernel_eq_weighted_sum,
    G.weight_eq_norm_sqrt_anchorMagnitude m hm ε hε C (hC _),
    G.weight_eq_norm_sqrt_anchorMagnitude m hm η hη D (hD _)]
  rw [G.realNodes_eq_sign_magnitudeNodes ε hε C, G.realNodes_eq_sign_magnitudeNodes η hη D]
  simp only [groupedNewtonWeight_sign _ _ _ ε hε, groupedNewtonWeight_sign _ _ _ η hη,
    groupedDoubleDividedDifference_sum, groupedAnchorNormalizedCrossKernel, smul_sum,
    Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_inv, mul_sum]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  rw [G.point_eq_sign_sqrt_magnitudeNodes ε hε C a (hC a),
    G.point_eq_sign_sqrt_magnitudeNodes η hη D b (hD b)]
  ring

end OrderedCarrierGrouping

end

end MeyerGeneralProblem
