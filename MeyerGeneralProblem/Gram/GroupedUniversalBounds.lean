module

public import MeyerGeneralProblem.Gram.GroupedGramCompactness
public import MeyerGeneralProblem.Atomic.GramSchur

@[expose] public section

/-!+# Genuine upper bounds for grouped universal atoms

The actual universal `L²` atoms are bounded through double divided differences
of their rational-density Gram kernel. Signed nodes may cross zero; no
square-root chart or lower bound on internal gaps enters this model estimate.
-/

namespace MeyerGeneralProblem

noncomputable section

open Finset

/-- Actual universal double divided differences have a uniform exponential
envelope on arbitrary real group hulls, including the central region. -/
theorem exists_universalDoubleDividedDifference_exponential
    (q m i j : ℕ) (hm : groupedHermiteDifferentiationOrder (q+1) ≤ m)
    (hi : i ≤ q) (hj : j ≤ q) (D : ℝ) (_hD : 0 ≤ D) :
    ∃ A : ℝ, 0 < A ∧ ∃ c : ℝ, 0 < c ∧
      ∀ {n k : ℕ} (nodes : Fin n → ℝ) (other : Fin k → ℝ)
      (_hnodes : Function.Injective nodes) (_hother : Function.Injective other)
      (a : Fin n) (b : Fin k), a.val=i → b.val=j → ∀ r t : ℝ,
      (∀ x, |nodes x-r| ≤ D) → (∀ y, |other y-t| ≤ D) →
      ‖groupedDoubleDividedDifference nodes other a b (fun x y => universalGramKernel m (y-x))‖ ≤
        A*Real.exp (-c*|t-r|) := by
  have hq : q+1+2 ≤ m := (le_max_left _ _).trans hm
  obtain ⟨A,hA,c,hc,hbound⟩ := exists_norm_iteratedDeriv_universalGramKernel_le_exponential_grouped q m i j hm hi hj
  refine ⟨A*Real.exp (2*c*D),by positivity,c,hc,?_⟩
  intro n k nodes other hnodes hother a b ha hb r t hn ho
  have hn' : ∀ x, nodes x ∈ Set.Icc (r-D) (r+D) := fun x => by
    have h := abs_le.mp (hn x); exact ⟨by linarith [h.1],by linarith [h.2]⟩
  have ho' : ∀ y, other y ∈ Set.Icc (t-D) (t+D) := fun y => by
    have h := abs_le.mp (ho y); exact ⟨by linarith [h.1],by linarith [h.2]⟩
  have hM : 0 ≤ (A*Real.exp (2*c*D))*Real.exp (-c*|t-r|) := by positivity
  apply (norm_groupedDoubleDividedDifference_le nodes other hnodes hother a b
    (fun x y => universalGramKernel m (y-x))
    (fun y => (contDiff_grouped_universalGramKernel m a.val (by omega)).comp (contDiff_const.sub contDiff_id))
    (fun x => contDiff_iff_contDiffAt.mpr (fun y => by
      simpa only [one_mul] using contDiffAt_iteratedDeriv_grouped_universalMagnitude_right m b.val a.val
        (by omega) 1 x y (by norm_num))) hn' ho' ?_).trans
      (grouped_div_factorials_le _ hM _ _)
  intro x hx y hy
  have hxy : |t-r| ≤ |y-x|+2*D := by
    have htri := abs_add_three (t-y) (y-x) (x-r)
    rw [show (t-y)+(y-x)+(x-r)=t-r by ring] at htri
    have hty : |t-y| ≤ D := abs_le.mpr ⟨by linarith [hy.2],by linarith [hy.1]⟩
    have hxr : |x-r| ≤ D := abs_le.mpr ⟨by linarith [hx.1],by linarith [hx.2]⟩
    linarith
  have hjet := norm_iteratedDeriv_iteratedDeriv_grouped_universalMagnitude m a.val b.val 1 x y (by norm_num)
  simp only [one_mul] at hjet
  rw [hjet,ha,hb]
  have h := hbound 1 (by norm_num) (y-x)
  simp only [one_mul] at h
  refine h.trans ?_
  rw [mul_assoc,← Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ hA.le
  exact Real.exp_le_exp.mpr (by nlinarith)

namespace OrderedCarrierGrouping

variable {S : LocallyFiniteCarrier} {κ : Type*} (G : OrderedCarrierGrouping S κ)

/-- A uniform bound for the actual universal grouped Gram, on all real
groups and all allowed prefix orders. -/
theorem exists_universalGroupedGramKernel_exponential (q m : ℕ)
    (hm : groupedHermiteDifferentiationOrder (q+1) ≤ m) (D : ℝ) (hD : 0 ≤ D)
    (s : κ → ℝ) (hsize : ∀ C, G.size C ≤ q)
    (hdiam : ∀ C i, |G.realNodes C i-s C| ≤ D) :
    ∃ A : ℝ, 0 < A ∧ ∃ c : ℝ, 0 < c ∧ ∀ x y : G.Index,
      ‖G.universalGroupedGramKernel m (by have := (le_max_left _ _).trans hm; omega) x y‖ ≤
        A*Real.exp (-c*|s y.1-s x.1|) := by
  choose A hA c hc hbound using fun p : Fin (q+1) × Fin (q+1) =>
    exists_universalDoubleDividedDifference_exponential q m p.1.val p.2.val hm
      (by omega) (by omega) D hD
  obtain ⟨p,hp⟩ := Finite.exists_max A
  obtain ⟨r,hr⟩ := Finite.exists_min c
  refine ⟨A p,hA p,c r,hc r,?_⟩
  intro x y
  have hx := hsize x.1
  have hy := hsize y.1
  let k : Fin (q+1) × Fin (q+1) := (⟨x.2.val,by have := x.2.isLt; omega⟩,
    ⟨y.2.val,by have := y.2.isLt; omega⟩)
  rw [G.universalGroupedGramKernel_eq_DD]
  refine (hbound k _ _ (G.realNodes_injective x.1) (G.realNodes_injective y.1)
    x.2 y.2 rfl rfl (s x.1) (s y.1) (hdiam x.1) (hdiam y.1)).trans ?_
  exact mul_le_mul (hp k) (Real.exp_le_exp.mpr (by nlinarith [hr k,abs_nonneg (s y.1-s x.1)]))
    (Real.exp_pos _).le (hA p).le

/-- Genuine Bessel analysis of the universal grouped atoms, constructed from
the proved kernel localization and separated-anchor row counting. -/
def universalBesselAnalysisOfGeometry [DecidableEq κ] (q m : ℕ)
    (hm : groupedHermiteDifferentiationOrder (q+1) ≤ m) (D d : ℝ) (hD : 0 ≤ D) (hd : 0 < d)
    (s : κ → ℝ) (hsize : ∀ C, G.size C ≤ q)
    (hdiam : ∀ C i, |G.realNodes C i-s C| ≤ D)
    (hsep : ∀ C E, C ≠ E → d ≤ |s C-s E|) :
    BesselAnalysis (G.universalAtom m (by have := (le_max_left _ _).trans hm; omega)) := by
  apply Classical.choice
  obtain ⟨A,hA,c,hc,hbound⟩ := G.exists_universalGroupedGramKernel_exponential q m hm D hD s hsize hdiam
  refine ⟨?_⟩
  let R := A*(q:ℝ)*positiveSeparationExpRowConstant d c
  have hR : 0 ≤ R := mul_nonneg (mul_nonneg hA.le (Nat.cast_nonneg q))
    (positiveSeparationExpRowConstant_nonneg d c)
  apply BesselAnalysis.of_finsupp_gram_row_bound _ (R+1) (by positivity)
  intro U x _hx
  have hrow := sum_grouped_exp_distance_le G.size hsize s hd hc hsep (s x.1) U
  calc
    ∑ y ∈ U, ‖inner ℂ (G.universalAtom m _ x) (G.universalAtom m _ y)‖ ≤
        ∑ y ∈ U, A*Real.exp (-c*|s y.1-s x.1|) := sum_le_sum (fun y _ => hbound x y)
    _ = A*∑ y ∈ U, Real.exp (-c*|s y.1-s x.1|) := (mul_sum _ _ _).symm
    _ ≤ R := by dsimp [R]; nlinarith [mul_le_mul_of_nonneg_left hrow hA.le]
    _ ≤ (R+1)^2 := by nlinarith [sq_nonneg R]

end OrderedCarrierGrouping

/-- A genuine bounded difference of finite Gram entries transfers the
Bessel property from a known family to the original family. -/
def BesselAnalysis.of_gramDifference {ι H J : Type*} [DecidableEq ι]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]
    (v : ι → H) (w : ι → J) (B : BesselAnalysis w)
    (A : CoefficientSpace ι →L[ℂ] CoefficientSpace ι)
    (hentry : ∀ i j, inner ℂ (coefficientAtom i) (A (coefficientAtom j)) =
      inner ℂ (v i) (v j)-inner ℂ (w i) (w j)) : BesselAnalysis v := by
  apply BesselAnalysis.of_finsupp_synthesis_bound v (‖B.synthesis‖+‖A‖+1)
  intro c
  let e := Finsupp.linearCombination ℂ (coefficientAtom : ι → CoefficientSpace ι) c
  have he : B.synthesis e=Finsupp.linearCombination ℂ w c := by
    simp only [e,Finsupp.linearCombination_apply,Finsupp.sum,map_sum,map_smul,B.synthesis_coefficientAtom]
  have hdiff : inner ℂ e (A e) = BesselAnalysis.finsuppGramForm v c-BesselAnalysis.finsuppGramForm w c := by
    simp only [e,Finsupp.linearCombination_apply,Finsupp.sum,map_sum,map_smul]
    rw [inner_sum]
    simp only [inner_smul_right,sum_inner,inner_smul_left,hentry,
      BesselAnalysis.finsuppGramForm,Finsupp.sum,mul_sub,sum_sub_distrib]
  have hv := BesselAnalysis.norm_sq_finsupp_linearCombination_eq_gramForm_re v c
  have hw := BesselAnalysis.norm_sq_finsupp_linearCombination_eq_gramForm_re w c
  have hdiffR := congrArg Complex.re hdiff
  rw [Complex.sub_re,← hv,← hw,← he] at hdiffR
  have hinner : (inner ℂ e (A e)).re ≤ ‖A‖*‖e‖^2 := by
    calc
      _ ≤ ‖inner ℂ e (A e)‖ := Complex.re_le_norm _
      _ ≤ ‖e‖*‖A e‖ := norm_inner_le_norm _ _
      _ ≤ ‖e‖*(‖A‖*‖e‖) := mul_le_mul_of_nonneg_left (A.le_opNorm e) (norm_nonneg _)
      _ = _ := by ring
  have hB := B.synthesis.le_opNorm e
  have hB2 : ‖B.synthesis e‖^2 ≤ ‖B.synthesis‖^2*‖e‖^2 := by
    nlinarith [norm_nonneg (B.synthesis e),mul_nonneg (norm_nonneg B.synthesis) (norm_nonneg e)]
  have hcoef : ‖B.synthesis‖^2+‖A‖ ≤ (‖B.synthesis‖+‖A‖+1)^2 := by
    nlinarith [norm_nonneg B.synthesis,norm_nonneg A,sq_nonneg ‖A‖,
      mul_nonneg (norm_nonneg B.synthesis) (norm_nonneg A)]
  have hsquare : ‖Finsupp.linearCombination ℂ v c‖^2 ≤ ((‖B.synthesis‖+‖A‖+1)*‖e‖)^2 := by
    have hh := mul_le_mul_of_nonneg_right hcoef (sq_nonneg ‖e‖)
    nlinarith
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hsquare

/-- All coefficient entries determine a bounded operator uniquely. -/
theorem coefficientOperator_eq_of_entries {ι : Type*} [DecidableEq ι]
    (A B : CoefficientSpace ι →L[ℂ] CoefficientSpace ι)
    (h : ∀ i j, inner ℂ (coefficientAtom i) (A (coefficientAtom j)) =
      inner ℂ (coefficientAtom i) (B (coefficientAtom j))) : A=B := by
  apply ContinuousLinearMap.ext_on
  · exact Submodule.dense_iff_topologicalClosure_eq_top.mpr coefficientAtom_dense_span
  · rintro _ ⟨j,rfl⟩
    apply (coefficientHilbertBasis ι).repr.injective
    apply lp.ext
    funext i
    simp only [(coefficientHilbertBasis ι).repr_apply_apply]
    exact h i j

end

end MeyerGeneralProblem
