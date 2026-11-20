module

public import MeyerGeneralProblem.Sampling.GroupedBiorthogonal

@[expose] public section

/-!
# Uniform finite kernels with actual cluster Newton data

The proved cluster insertion inequality constructs supported Hilbert duals.
Finite colour convolution supplies the chosen Newton datum on one cluster
and zero data on every other cluster. Only exact point-to-Newton identities
are used; the uniform mass bound never estimates an inverse node gap.
-/

namespace MeyerGeneralProblem

open MeasureTheory

noncomputable section

/-- Actual separated exterior frequencies can be annihilated while every
initial Newton coordinate of one bounded cluster is prescribed independently.
The common mass bound precedes both finite dimensions and all node gaps. -/
theorem exists_uniform_supported_grouped_separator
    (q : ℕ) {b r L d D : ℝ} (hb : 0 < b) (hr : 0 < r)
    (hL : 0 < L) (hd : 0 < d) (hD : 0 ≤ D) (hgap : 1 < 2 * b * L) :
    ∃ C : ℝ, 0 < C ∧ ∀ n k : ℕ, k ≤ q →
      ∀ (s : Fin n → ℝ) (ω : Fin k → ℝ),
      PairwiseFrequencySeparated s L → Function.Injective ω →
      (∀ i j, dist (ω i) (ω j) ≤ D) → (∀ i j, d ≤ |s i - ω j|) →
      ∃ ψ : Fin k → ℝ → ℂ,
        (∀ i, Integrable (ψ i)) ∧ (∀ i, MemLp (ψ i) 2 volume) ∧
        (∀ i, Function.support (ψ i) ⊆ Set.Icc (-(b + q * r)) (b + q * r)) ∧
        (∀ i j, FourierTransform.fourier (ψ i) (s j) = 0) ∧
        (∀ i j : Fin k, analyticDividedDifference (finiteNodeSequence ω) j
          (FourierTransform.fourier (ψ i)) = if i = j then 1 else 0) ∧
        ∀ i, (∫ t : ℝ, ‖ψ i t‖) ^ 2 ≤ C := by
  obtain ⟨A, hA, hbound⟩ :=
    exists_uniform_finite_cosineIngham_insert_cluster q hb hr hL hd hD hgap
  refine ⟨2 * (b + q * r) / A, by positivity, ?_⟩
  intro n k hk s ω hs hω hdiam hsep
  exact exists_supported_grouped_biorthogonal_of_lowerBound (by positivity)
    s ω hω hA (hbound n k hk s ω hs hω hdiam hsep)

/-- Initial Newton data reconstruct actual point values at distinct nodes,
for an arbitrary function, without a regularity assumption. -/
theorem values_eq_newtonInterpolant_of_initialData {k : ℕ}
    (ω : Fin k → ℝ) (hω : Function.Injective ω) (f : ℝ → ℂ) (data : Fin k → ℂ)
    (hdata : ∀ j : Fin k,
      analyticDividedDifference (finiteNodeSequence ω) j f = data j) (i : Fin k) :
    f (ω i) = (newtonInterpolant (fun j => (ω j : ℂ)) data).eval (ω i : ℂ) := by
  have hcoeff : dividedDifferences (fun j => (ω j : ℂ))
      (Complex.ofReal_injective.comp hω) (fun j => f (ω j)) = data := by
    funext j
    rw [← analyticDividedDifference_eq_dividedDifferences ω hω]
    exact hdata j
  simpa only [newtonInterpolantFromValues, hcoeff] using
    (eval_newtonInterpolantFromValues_at_node (fun j => (ω j : ℂ))
      (Complex.ofReal_injective.comp hω) (fun j => f (ω j)) i).symm

/-- A single coordinate datum reconstructs precisely the corresponding
Newton basis polynomial at the original nodes. -/
theorem values_eq_newtonBasis_of_initialData {k : ℕ}
    (ω : Fin k → ℝ) (hω : Function.Injective ω) (f : ℝ → ℂ) (a : Fin k)
    (hdata : ∀ j : Fin k,
      analyticDividedDifference (finiteNodeSequence ω) j f = if a = j then 1 else 0)
    (i : Fin k) :
    f (ω i) = (newtonBasisPolynomial (fun j => (ω j : ℂ)) a).eval (ω i : ℂ) := by
  rw [values_eq_newtonInterpolant_of_initialData ω hω f _ hdata i, newtonInterpolant_eq_sum]
  simp

/-- Equal complete initial Newton data imply equal values at the cluster. -/
theorem values_eq_of_initialData_eq {k : ℕ}
    (ω : Fin k → ℝ) (hω : Function.Injective ω) (f g : ℝ → ℂ)
    (hdata : ∀ j : Fin k, analyticDividedDifference (finiteNodeSequence ω) j f =
      analyticDividedDifference (finiteNodeSequence ω) j g) (i : Fin k) :
    f (ω i) = g (ω i) := by
  rw [values_eq_newtonInterpolant_of_initialData ω hω f _ hdata i,
    values_eq_newtonInterpolant_of_initialData ω hω g _ (fun _ => rfl) i]

/-- At distinct cluster nodes, equality of values implies equality of all
initial divided differences. The finite prefix is made explicit. -/
theorem initialData_eq_of_values_eq {k : ℕ}
    (ω : Fin k → ℝ) (hω : Function.Injective ω) (f g : ℝ → ℂ)
    (hvalues : ∀ i, f (ω i) = g (ω i)) (j : Fin k) :
    analyticDividedDifference (finiteNodeSequence ω) j f =
      analyticDividedDifference (finiteNodeSequence ω) j g := by
  rw [analyticDividedDifference_eq_dividedDifferences ω hω,
    analyticDividedDifference_eq_dividedDifferences ω hω]
  congr 1
  exact funext hvalues

/-- The exact zero-function regression at every finite initial coordinate. -/
theorem initialData_zero {k : ℕ} (ω : Fin k → ℝ) (j : Fin k) :
    analyticDividedDifference (finiteNodeSequence ω) j (fun _ => (0 : ℂ)) = 0 := by
  simpa only [Polynomial.eval_zero] using
    (analyticDividedDifference_polynomial_eval (finiteNodeSequence ω) j (0 : Polynomial ℂ)).trans
      (polynomialDividedDifference_zero _ _)

/-- Convolving one prescribed-coordinate factor with constant-coordinate
factors gives genuine grouped kernels for a finite union of separated colours.
Every exterior frequency is annihilated, while all target Newton data remain
exact. The support and mass budgets depend on colours, not finite dimension. -/
theorem exists_uniform_supported_grouped_kernels_of_colours
    (m q : ℕ) {b r L d D : ℝ} (hb : 0 < b) (hr : 0 < r)
    (hL : 0 < L) (hd : 0 < d) (hD : 0 ≤ D) (hgap : 1 < 2 * b * L) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, k ≤ q → ∀ (ω : Fin k → ℝ),
      Function.Injective ω → (∀ i j, dist (ω i) (ω j) ≤ D) →
      ∀ (n : Fin (m + 1) → ℕ) (s : (a : Fin (m + 1)) → Fin (n a) → ℝ),
      (∀ a, PairwiseFrequencySeparated (s a) L) →
      (∀ a i j, d ≤ |s a i - ω j|) →
      ∃ ρ : Fin k → ℝ → ℂ,
        (∀ i, Integrable (ρ i)) ∧
        (∀ i, Function.support (ρ i) ⊆
          Set.Icc (-((m + 1 : ℕ) * (b + q * r))) ((m + 1 : ℕ) * (b + q * r))) ∧
        (∀ i a j, FourierTransform.fourier (ρ i) (s a j) = 0) ∧
        (∀ i j : Fin k, analyticDividedDifference (finiteNodeSequence ω) j
          (FourierTransform.fourier (ρ i)) = if i = j then 1 else 0) ∧
        ∀ i, (∫ t : ℝ, ‖ρ i t‖) ^ 2 ≤ C := by
  classical
  obtain ⟨C₀, hC₀, hseparator⟩ :=
    exists_uniform_supported_grouped_separator q hb hr hL hd hD hgap
  refine ⟨C₀ ^ (m + 1), pow_pos hC₀ _, ?_⟩
  intro k hk ω hω hdiam n s hs hsep
  have hone (a : Fin (m + 1)) :=
    hseparator (n a) k hk (s a) ω (hs a) hω hdiam (hsep a)
  choose ψ hint _hL2 hsupp hzero hdata hmass using hone
  let z (i : Fin k) : Fin k := ⟨0, lt_of_le_of_lt (Nat.zero_le i) i.isLt⟩
  let idx (i : Fin k) (a : Fin (m + 1)) : Fin k := if a = 0 then i else z i
  let factors (i : Fin k) (a : Fin (m + 1)) : ℝ → ℂ := ψ a (idx i a)
  let ρ (i : Fin k) : ℝ → ℂ := finiteFourierKernelConvolution m (factors i)
  have hfint (i : Fin k) (a : Fin (m + 1)) : Integrable (factors i a) := hint a _
  have htarget (i l : Fin k) :
      FourierTransform.fourier (ρ i) (ω l) = FourierTransform.fourier (ψ 0 i) (ω l) := by
    rw [fourier_finiteFourierKernelConvolution m (factors i) (hfint i)]
    have hp : (∏ a, FourierTransform.fourier (factors i a) (ω l)) =
        FourierTransform.fourier (factors i 0) (ω l) := by
      apply Finset.prod_eq_single 0
      · intro a ha ha0
        change FourierTransform.fourier (ψ a (idx i a)) (ω l) = 1
        rw [show idx i a = z i from ite_eq_right ha0]
        rw [values_eq_newtonBasis_of_initialData ω hω _ (z i) (hdata a (z i)) l]
        rw [eval_newtonBasisPolynomial]
        apply Finset.prod_eq_one
        intro j hj
        have hh := Finset.mem_Iio.mp hj
        change j.val < 0 at hh
        omega
      · simp
    simpa only [factors, idx, ite_true] using hp
  refine ⟨ρ, fun i => integrable_finiteFourierKernelConvolution m _ (hfint i),
    ?_, ?_, ?_, ?_⟩
  · intro i
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
      support_finiteFourierKernelConvolution_subset m (factors i)
        (fun _ => b + q * r) (fun a => hsupp a (idx i a))
  · intro i a j
    rw [fourier_finiteFourierKernelConvolution m (factors i) (hfint i)]
    exact Finset.prod_eq_zero (Finset.mem_univ a) (hzero a (idx i a) j)
  · intro i j
    rw [initialData_eq_of_values_eq ω hω _ _ (htarget i) j]
    exact hdata 0 i j
  · intro i
    have h := integral_norm_finiteFourierKernelConvolution_le m (factors i) (hfint i)
    calc
      _ ≤ (∏ a, ∫ t : ℝ, ‖factors i a t‖) ^ 2 :=
        (sq_le_sq₀ (integral_nonneg (fun t => norm_nonneg _))
          (Finset.prod_nonneg (fun a ha => integral_nonneg (fun t => norm_nonneg _)))).2 h
      _ = ∏ a, (∫ t : ℝ, ‖factors i a t‖) ^ 2 := (Finset.prod_pow _ _ _).symm
      _ ≤ ∏ _a : Fin (m + 1), C₀ :=
        Finset.prod_le_prod₀ (fun a ha => sq_nonneg _) (fun a ha => hmass a (idx i a))
      _ = C₀ ^ (m + 1) := by simp

/-- Finite coloured cluster families have actual supported interpolation
kernels for every initial coordinate. Every off-cluster initial datum is
zero. Only inter-cluster separation occurs in the common constants. -/
theorem exists_uniform_supported_grouped_kernels_of_finite_colouring
    (m q : ℕ) {b r L d D : ℝ} (hb : 0 < b) (hr : 0 < r)
    (hL : 0 < L) (hd : 0 < d) (hD : 0 ≤ D) (hgap : 1 < 2 * b * L) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (size : Fin N → ℕ),
      (∀ g, size g ≤ q) → ∀ (nodes : (g : Fin N) → Fin (size g) → ℝ),
      (∀ g, Function.Injective (nodes g)) →
      (∀ g i j, dist (nodes g i) (nodes g j) ≤ D) →
      (∀ g h, g ≠ h → ∀ i j, d ≤ |nodes g i - nodes h j|) →
      ∀ (colour : (Σ g, Fin (size g)) → Fin (m + 1)),
      (∀ x y : Σ g, Fin (size g), colour x = colour y → x ≠ y →
        L ≤ |nodes x.1 x.2 - nodes y.1 y.2|) →
      ∃ ρ : (g : Fin N) → Fin (size g) → ℝ → ℂ,
        (∀ g i, Integrable (ρ g i)) ∧
        (∀ g i, Function.support (ρ g i) ⊆
          Set.Icc (-((m + 1 : ℕ) * (b + q * r))) ((m + 1 : ℕ) * (b + q * r))) ∧
        (∀ g (i j : Fin (size g)), analyticDividedDifference (finiteNodeSequence (nodes g)) j
          (FourierTransform.fourier (ρ g i)) = if i = j then 1 else 0) ∧
        (∀ g h, g ≠ h → ∀ (i : Fin (size g)) (j : Fin (size h)),
          analyticDividedDifference (finiteNodeSequence (nodes h)) j
            (FourierTransform.fourier (ρ g i)) = 0) ∧
        ∀ g i, (∫ t : ℝ, ‖ρ g i t‖) ^ 2 ≤ C := by
  classical
  obtain ⟨C, hC, hcolours⟩ :=
    exists_uniform_supported_grouped_kernels_of_colours m q hb hr hL hd hD hgap
  refine ⟨C, hC, ?_⟩
  intro N size hsize nodes hnodes hdiam hsep colour hcolour
  have hone (g : Fin N) : ∃ ρ : Fin (size g) → ℝ → ℂ,
      (∀ i, Integrable (ρ i)) ∧
      (∀ i, Function.support (ρ i) ⊆
        Set.Icc (-((m + 1 : ℕ) * (b + q * r))) ((m + 1 : ℕ) * (b + q * r))) ∧
      (∀ i j : Fin (size g), analyticDividedDifference (finiteNodeSequence (nodes g)) j
        (FourierTransform.fourier (ρ i)) = if i = j then 1 else 0) ∧
      (∀ h, g ≠ h → ∀ (i : Fin (size g)) (j : Fin (size h)),
        FourierTransform.fourier (ρ i) (nodes h j) = 0) ∧
      ∀ i, (∫ t : ℝ, ‖ρ i t‖) ^ 2 ≤ C := by
    let J (a : Fin (m + 1)) := {x : Σ h, Fin (size h) // x.1 ≠ g ∧ colour x = a}
    let e (a : Fin (m + 1)) : Fin (Fintype.card (J a)) ≃ J a := (Fintype.equivFin (J a)).symm
    let s (a : Fin (m + 1)) (i : Fin (Fintype.card (J a))) : ℝ :=
      nodes (e a i).val.1 (e a i).val.2
    have hs (a : Fin (m + 1)) : PairwiseFrequencySeparated (s a) L := by
      intro i j hij
      apply hcolour (e a i).val (e a j).val
      · exact (e a i).property.2.trans (e a j).property.2.symm
      · exact fun h => hij ((e a).injective (Subtype.ext h))
    have hsg (a : Fin (m + 1)) (i : Fin (Fintype.card (J a))) (j : Fin (size g)) :
        d ≤ |s a i - nodes g j| :=
      hsep (e a i).val.1 g (e a i).property.1 (e a i).val.2 j
    obtain ⟨ρ, hi, hsupp, hzero, hdata, hmass⟩ :=
      hcolours (size g) (hsize g) (nodes g) (hnodes g) (hdiam g)
        (fun a => Fintype.card (J a)) s hs hsg
    refine ⟨ρ, hi, hsupp, hdata, ?_, hmass⟩
    intro h hgh i j
    let x : Σ h, Fin (size h) := ⟨h, j⟩
    let y : J (colour x) := ⟨x, Ne.symm hgh, rfl⟩
    have hz := hzero i (colour x) ((e (colour x)).symm y)
    change FourierTransform.fourier (ρ i)
      (nodes (e (colour x) ((e (colour x)).symm y)).val.1
        (e (colour x) ((e (colour x)).symm y)).val.2) = 0 at hz
    rw [Equiv.apply_symm_apply] at hz
    exact hz
  choose ρ hint hsupp hdata hzero hmass using hone
  refine ⟨ρ, hint, hsupp, hdata, ?_, hmass⟩
  intro g h hgh i j
  rw [initialData_eq_of_values_eq (nodes h) (hnodes h) _ (fun _ => (0 : ℂ))
    (hzero g h hgh i) j]
  exact initialData_zero (nodes h) j

end

end MeyerGeneralProblem
