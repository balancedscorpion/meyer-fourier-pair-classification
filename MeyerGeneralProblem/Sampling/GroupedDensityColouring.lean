module

public import MeyerGeneralProblem.Sampling.GroupedFiniteKernels

@[expose] public section

/-!
# Sharp-density colour and support budgets for grouped kernels

The numerical upper density supplies a half-open window count cap. Its
colours are assigned to actual carrier points, while every original cluster
is kept intact and removed in full from each exterior colour. Strict density
slack pays for all cluster insertions and reserves a positive smoothing
radius. No internal cluster gap or altered disc boundary is introduced.
-/

namespace MeyerGeneralProblem

open MeasureTheory

noncomputable section

/-- Numerical upper density leaves enough support for all colour factors,
bounded-size cluster insertion, and a strictly positive smoothing margin.
The choice uses `q + 1`, so the empty-cluster bound is included. -/
theorem exists_grouped_density_colour_budget
    (S : LocallyFiniteCarrier) (q : ℕ) {W : ℝ} (hW : 0 < W)
    (hS : upperUniformBeurlingDensity S < ENNReal.ofReal (2 * W)) :
    ∃ m : ℕ, ∃ L b r η : ℝ,
      0 < L ∧ 0 < b ∧ 0 < r ∧ 0 < η ∧ 1 < 2 * b * L ∧
      (m + 1 : ℕ) * (b + q * r) + η < W ∧
      ∀ x : ℝ, windowCount S x L ≤ m + 1 := by
  obtain ⟨N, hN, L, hL, hratio, hcap⟩ :=
    exists_uniform_windowCap_of_upperDensity_lt S (by positivity : 0 < 2 * W) hS
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  have hNr : (0 : ℝ) < (m + 1 : ℕ) := by positivity
  have hbudget : 1 / (2 * L) < W / (m + 1 : ℕ) := by
    apply (div_lt_div_iff₀ (by positivity) hNr).2
    nlinarith
  obtain ⟨b, hblo, hbhi⟩ := exists_between hbudget
  have hb : 0 < b := (by positivity : (0 : ℝ) < 1 / (2 * L)).trans hblo
  have hgap : 1 < 2 * b * L := by
    have h := (div_lt_iff₀ (by positivity : 0 < 2 * L)).1 hblo
    nlinarith
  obtain ⟨w, hbw, hwa⟩ := exists_between hbhi
  let r := (w - b) / ((q : ℝ) + 1)
  have hr : 0 < r := div_pos (sub_pos.2 hbw) (by positivity)
  have heq : ((q : ℝ) + 1) * r = w - b := by
    dsimp [r]
    field_simp
  have hsmall : b + (q : ℝ) * r < w := by nlinarith
  let R := (m + 1 : ℕ) * (b + (q : ℝ) * r)
  have hRW : R < W := by
    have hw := (lt_div_iff₀ hNr).1 hwa
    have hm := mul_lt_mul_of_pos_left hsmall hNr
    dsimp [R]
    nlinarith
  refine ⟨m, L, b, r, (W - R) / 2, hL, hb, hr, by positivity, hgap, ?_, hcap⟩
  change R + (W - R) / 2 < W
  linarith

/-- Distinct points inside each cluster and positive separation between
clusters give an injective enumeration of the union, counting each point once. -/
theorem grouped_nodes_injective_of_intercluster_separation
    {N : ℕ} (size : Fin N → ℕ) (nodes : (g : Fin N) → Fin (size g) → ℝ)
    (hnodes : ∀ g, Function.Injective (nodes g)) {d : ℝ} (hd : 0 < d)
    (hsep : ∀ g h, g ≠ h → ∀ i j, d ≤ |nodes g i - nodes h j|) :
    Function.Injective (fun x : Σ g, Fin (size g) => nodes x.1 x.2) := by
  rintro ⟨g, i⟩ ⟨h, j⟩ heq
  change nodes g i = nodes h j at heq
  have hgh : g = h := by
    by_contra hgh
    have h := hsep g h hgh i j
    rw [heq, sub_self, abs_zero] at h
    linarith
  subst h
  have hij := hnodes g heq
  subst j
  rfl

/-- A carrier window cap colours any actual finite grouped subfamily.
The original groups are not modified, merged, or split by this construction. -/
theorem exists_grouped_finite_colouring_of_uniform_windowCap
    {S : LocallyFiniteCarrier} {m : ℕ} (hm : 0 < m) {L : ℝ}
    (hcap : ∀ x : ℝ, windowCount S x L ≤ m)
    {N : ℕ} (size : Fin N → ℕ) (nodes : (g : Fin N) → Fin (size g) → ℝ)
    (hinj : Function.Injective (fun x : Σ g, Fin (size g) => nodes x.1 x.2))
    (hmem : ∀ g i, nodes g i ∈ S.carrier) :
    ∃ colour : (Σ g, Fin (size g)) → Fin m,
      ∀ x y : Σ g, Fin (size g), colour x = colour y → x ≠ y →
        L ≤ |nodes x.1 x.2 - nodes y.1 y.2| := by
  classical
  let f : (Σ g, Fin (size g)) → ℝ := fun x => nodes x.1 x.2
  let F : Finset ℝ := Finset.univ.image f
  have hF : ∀ x ∈ F, x ∈ S.carrier := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact hmem i.1 i.2
  obtain ⟨colour, hc⟩ := exists_finite_colouring_of_uniform_windowCap hm hcap F hF
  let e (x : Σ g, Fin (size g)) : F := ⟨f x, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  refine ⟨fun x => colour (e x), ?_⟩
  intro x y hxy hne
  exact hc (e x) (e y) hxy (fun h => hne (hinj (congrArg Subtype.val h)))

/-- Strict numerical upper density yields genuine finite grouped Fourier
interpolation kernels with a common mass bound and a positive smoothing
budget. Geometry uses only bounded cluster size/diameter and inter-cluster
separation; no positive lower bound on internal gaps is required. -/
theorem exists_uniform_finite_grouped_kernels_of_upperDensity_lt
    (S : LocallyFiniteCarrier) (q : ℕ) {W d D : ℝ}
    (hW : 0 < W) (hd : 0 < d) (hD : 0 ≤ D)
    (hS : upperUniformBeurlingDensity S < ENNReal.ofReal (2 * W)) :
    ∃ R η C : ℝ, 0 < R ∧ 0 < η ∧ R + η < W ∧ 0 < C ∧
      ∀ (N : ℕ) (size : Fin N → ℕ), (∀ g, size g ≤ q) →
      ∀ (nodes : (g : Fin N) → Fin (size g) → ℝ),
      (∀ g, Function.Injective (nodes g)) →
      (∀ g i, nodes g i ∈ S.carrier) →
      (∀ g i j, dist (nodes g i) (nodes g j) ≤ D) →
      (∀ g h, g ≠ h → ∀ i j, d ≤ |nodes g i - nodes h j|) →
      ∃ ρ : (g : Fin N) → Fin (size g) → ℝ → ℂ,
        (∀ g i, Integrable (ρ g i)) ∧
        (∀ g i, Function.support (ρ g i) ⊆ Set.Icc (-R) R) ∧
        (∀ g (i j : Fin (size g)), analyticDividedDifference (finiteNodeSequence (nodes g)) j
          (FourierTransform.fourier (ρ g i)) = if i = j then 1 else 0) ∧
        (∀ g h, g ≠ h → ∀ (i : Fin (size g)) (j : Fin (size h)),
          analyticDividedDifference (finiteNodeSequence (nodes h)) j
            (FourierTransform.fourier (ρ g i)) = 0) ∧
        ∀ g i, (∫ t : ℝ, ‖ρ g i t‖) ^ 2 ≤ C := by
  obtain ⟨m, L, b, r, η, hL, hb, hr, hη, hgap, hbudget, hcap⟩ :=
    exists_grouped_density_colour_budget S q hW hS
  obtain ⟨C, hC, hkernels⟩ :=
    exists_uniform_supported_grouped_kernels_of_finite_colouring m q hb hr hL hd hD hgap
  refine ⟨(m + 1 : ℕ) * (b + q * r), η, C, by positivity, hη, hbudget, hC, ?_⟩
  intro N size hsize nodes hnodes hmem hdiam hsep
  have hinj := grouped_nodes_injective_of_intercluster_separation size nodes hnodes hd hsep
  obtain ⟨colour, hcolour⟩ := exists_grouped_finite_colouring_of_uniform_windowCap
    (Nat.succ_pos m) hcap size nodes hinj hmem
  exact hkernels N size hsize nodes hnodes hdiam hsep colour hcolour

end

end MeyerGeneralProblem
