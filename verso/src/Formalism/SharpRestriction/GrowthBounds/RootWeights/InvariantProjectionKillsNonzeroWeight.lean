import Formalism.SharpRestriction.GrowthBounds.RootWeights.DegreeZeroWeightsBounded

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

/- English proof (translation)
Establish `hs` using `gl_rep_shifts_weights hE`. Establish `htop` using `sum_isotypic_top_of_weight_data D h2 E hE hs (findim_weights_bounded E) (weight_projections_integral_findim E)`. Establish `hinv` using `trivial_isotypic_invariant_holds hE`. Establish `hle : ∀ mu, isoSub E mu ≤ LinearMap.ker (Inv * E a b)`. Introduce `mu y hy`.

Rewrite using `[LinearMap.mem_ker, Module.End.mul_apply]`. Distinguish the cases in `hmu : mu = 0`. Substitute `hmu` using the available equality. Take `⟨hy0, hyr⟩` from `hinv y hy`. Establish `: E a b y = 0`.

Break down `lt_trichotomy a b with h | h | h` into its components or cases. Conclude with `hyr a b h`. Substitute `h` using the available equality. Use `(mem_weightSpace_iff_diagonal_eigen E 0 y).1 hy0 a` as an intermediate fact. Simplify using `using this`.

Conclude with `weight_zero_lowering_kills_raising hE hy0 b a (ne_of_lt h) (hyr b a h)`. Rewrite using `[this, map_zero]`. Conclude with `hInv.2 mu hmu _ (isotypic_stable_under_gl_operator E mu a b y hy)`. Establish `: (⊤ : Submodule K V) ≤ LinearMap.ker (Inv * E a b)`. Rewrite using `[← htop]`.

Conclude with `iSup_le hle`. Establish `h3` using `this (Submodule.mem_top (x := x))`. Rewrite `h3` using `[LinearMap.mem_ker, Module.End.mul_apply]`. Then use the resulting hypothesis.
-/
theorem invariant_projection_kills_operator (D : Formalism.BasicNotions.D7) (h2 : adm2 D) {K V : Type} [Field K] [CharZero K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {n : ℕ} (E : GLOps n K V) (hE : IsGLRep E)
    (Inv : Module.End K V) (hInv : IsInvProj E Inv) (a b : Fin n) (x : V) : Inv (E a b x) = 0 := by
  have hs := gl_rep_shifts_weights hE
  have htop := sum_isotypic_top_of_weight_data D h2 E hE hs (findim_weights_bounded E) (weight_projections_integral_findim E)
  have hinv := trivial_isotypic_invariant_holds hE
  have hle : ∀ mu, isoSub E mu ≤ LinearMap.ker (Inv * E a b) := by
    intro mu y hy
    rw [LinearMap.mem_ker, Module.End.mul_apply]
    by_cases hmu : mu = 0
    · subst hmu
      obtain ⟨hy0, hyr⟩ := hinv y hy
      have : E a b y = 0 := by
        rcases lt_trichotomy a b with h | h | h
        · exact hyr a b h
        · subst h
          have := (mem_weightSpace_iff_diagonal_eigen E 0 y).1 hy0 a
          simpa using this
        · exact weight_zero_lowering_kills_raising hE hy0 b a (ne_of_lt h) (hyr b a h)
      rw [this, map_zero]
    · exact hInv.2 mu hmu _ (isotypic_stable_under_gl_operator E mu a b y hy)
  have : (⊤ : Submodule K V) ≤ LinearMap.ker (Inv * E a b) := by
    rw [← htop]
    exact iSup_le hle
  have h3 := this (Submodule.mem_top (x := x))
  rwa [LinearMap.mem_ker, Module.End.mul_apply] at h3

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨a, ha⟩ : ∃ a, μ a ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `hμ (funext h)`. Establish `h1` using `(mem_weightSpace_iff_diagonal_eigen E μ x).1 hx a`.

Establish `h2' : (μ a : K) ≠ 0` using `by exact_mod_cast ha`. Establish `h3 : x = E a a (((μ a : K))⁻¹ • x)`. Rewrite using `[map_smul, h1, smul_smul, inv_mul_cancel₀ h2', one_smul]`. Rewrite using `[h3]`. Conclude with `invariant_projection_kills_operator D h2 E hE Inv hInv a a _`.
-/
theorem invariant_projection_kills_nonzero_weight (D : Formalism.BasicNotions.D7) (h2 : adm2 D) {K V : Type} [Field K] [CharZero K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {n : ℕ} (E : GLOps n K V) (hE : IsGLRep E)
    (Inv : Module.End K V) (hInv : IsInvProj E Inv) (μ : Fin n → ℤ) (hμ : μ ≠ 0) (x : V)
    (hx : x ∈ weightSp E μ) : Inv x = 0 := by
  obtain ⟨a, ha⟩ : ∃ a, μ a ≠ 0 := by
    by_contra h
    push Not at h
    exact hμ (funext h)
  have h1 := (mem_weightSpace_iff_diagonal_eigen E μ x).1 hx a
  have h2' : (μ a : K) ≠ 0 := by exact_mod_cast ha
  have h3 : x = E a a (((μ a : K))⁻¹ • x) := by
    rw [map_smul, h1, smul_smul, inv_mul_cancel₀ h2', one_smul]
  rw [h3]
  exact invariant_projection_kills_operator D h2 E hE Inv hInv a a _

/- English proof (translation)
Take `⟨m, hm⟩` from `findim_weights_bounded E`. Use `set box : Finset (Fin n → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-(m : ℤ)) m with hbox`. Establish `hb : ∀ ν, weightSp E ν ≠ ⊥ → ν ∈ box`. Introduce `ν hν`. Rewrite using `[hbox, Fintype.mem_piFinset]`.

Introduce `a`. Rewrite using `[Finset.mem_Icc]`. Conclude with `abs_le.1 (hm ν hν a)`. Establish `hsum` using `sum_weight_projections_eq_self E hE Θ hΘ box hb x`. Establish `h0 : (0 : Fin n → ℤ) ∈ box`.

Rewrite using `[hbox, Fintype.mem_piFinset]`. Introduce `a`. Rewrite using `[Finset.mem_Icc]`. Apply the tactic sequence `constructor <;> simp`. Use `conv_lhs => rw [← hsum]`.

Rewrite using `[map_sum, Finset.sum_eq_single_of_mem 0 h0]`. Introduce `μ _ hμ`. Conclude with `invariant_projection_kills_nonzero_weight D h2 E hE Inv hInv μ hμ _ (weight_projection_mem_weightSpace E hE Θ hΘ μ x)`.
-/
theorem invariant_projection_through_zero_weight (D : Formalism.BasicNotions.D7) (h2 : adm2 D) {K V : Type} [Field K] [CharZero K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {n : ℕ} (E : GLOps n K V) (hE : IsGLRep E)
    (Inv : Module.End K V) (hInv : IsInvProj E Inv) (Θ : (Fin n → ℤ) → Module.End K V)
    (hΘ : ∀ μ ν, ∀ x ∈ weightSp E ν, Θ μ x = if ν = μ then x else 0) (x : V) : Inv x = Inv (Θ 0 x) := by
  classical
  obtain ⟨m, hm⟩ := findim_weights_bounded E
  set box : Finset (Fin n → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-(m : ℤ)) m with hbox
  have hb : ∀ ν, weightSp E ν ≠ ⊥ → ν ∈ box := by
    intro ν hν
    rw [hbox, Fintype.mem_piFinset]
    intro a
    rw [Finset.mem_Icc]
    exact abs_le.1 (hm ν hν a)
  have hsum := sum_weight_projections_eq_self E hE Θ hΘ box hb x
  have h0 : (0 : Fin n → ℤ) ∈ box := by
    rw [hbox, Fintype.mem_piFinset]
    intro a
    rw [Finset.mem_Icc]
    constructor <;> simp
  conv_lhs => rw [← hsum]
  rw [map_sum, Finset.sum_eq_single_of_mem 0 h0]
  intro μ _ hμ
  exact invariant_projection_kills_nonzero_weight D h2 E hE Inv hInv μ hμ _ (weight_projection_mem_weightSpace E hE Θ hΘ μ x)

end Formalism.MainNotions.G.GLWeightTheory
