import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JumpWindow

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.BlockWindow

open Formalism.MainNotions.AdmissibleParameterJ in

/- English proof (translation)
Establish `hc : (Jp D j ρ).ncard = D.R.nV` using `(hb j h1 h2 ρ).2.2.2.2.2`. Establish `hf : (Jp D j ρ).Finite` using `Set.finite_of_ncard_pos (by omega)`. Consider the cases of `up with`. Consider the case `true => simpa [JJ] using And.intro hf hc`. Consider the case `false`.

Establish `hinj : Function.Injective (AdmissibleParameterJ.refl D)`. Introduce `a b hab`. Simplify using `only [AdmissibleParameterJ.refl] at hab`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hEq : Jm D j ρ = AdmissibleParameterJ.refl D '' Jp D j ρ`.

Use extensionality with `q`. Simplify using `only [Jm, reflS, Set.mem_setOf_eq, Set.mem_image]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `⟨_, h, by simp [AdmissibleParameterJ.refl]⟩`.

Introduce and unpack `⟨u, hu, rfl⟩`. Establish `: AdmissibleParameterJ.refl D (AdmissibleParameterJ.refl D u) = u` using `by simp [AdmissibleParameterJ.refl]`. Rewrite using `[this]` and apply the resulting hypothesis. Simplify using `only [JJ, Bool.false_eq_true, if_false]`. Rewrite using `[hEq]`.

Conclude with `⟨hf.image _, by rw [Set.ncard_image_of_injective _ hinj, hc]⟩`.
-/
theorem JJ_finite_ncard {D : D7} (L : SizeData₂ D) (hb : AdmissibleParameterJ.CloudCentreDistance L) (hn : 0 < D.R.nV) (up : Bool) (j : ℕ) (h1 : 1 ≤ j)
    (h2 : j ≤ D.R.m) (ρ : D.what₂.Tau) : (JJ D up j ρ).Finite ∧ (JJ D up j ρ).ncard = D.R.nV := by
  have hc : (Jp D j ρ).ncard = D.R.nV := (hb j h1 h2 ρ).2.2.2.2.2
  have hf : (Jp D j ρ).Finite := Set.finite_of_ncard_pos (by omega)
  cases up with
  | true => simpa [JJ] using And.intro hf hc
  | false =>
    have hinj : Function.Injective (AdmissibleParameterJ.refl D) := by
      intro a b hab
      simp only [AdmissibleParameterJ.refl] at hab
      linarith
    have hEq : Jm D j ρ = AdmissibleParameterJ.refl D '' Jp D j ρ := by
      ext q
      simp only [Jm, reflS, Set.mem_setOf_eq, Set.mem_image]
      constructor
      · intro h
        exact ⟨_, h, by simp [AdmissibleParameterJ.refl]⟩
      · rintro ⟨u, hu, rfl⟩
        have : AdmissibleParameterJ.refl D (AdmissibleParameterJ.refl D u) = u := by simp [AdmissibleParameterJ.refl]
        rwa [this]
    simp only [JJ, Bool.false_eq_true, if_false]
    rw [hEq]
    exact ⟨hf.image _, by rw [Set.ncard_image_of_injective _ hinj, hc]⟩

/- English proof (translation)
Introduce `D large₂ hJ hP`. Take `⟨⟨ep, hA⟩, hb, -, -, he, -, -⟩` from `hJ`. Establish `hn : 0 < D.R.nV`. Use `D.R.rank_add_five_le` as an intermediate fact. Unfold `Ranks.nV`.

Use linear arithmetic over natural numbers and integers. Establish `hS` using `large₂.Sc_pos`. Establish `hη` using `large₂.etaSz_pos`. Establish `hP' : large₂.Sc + large₂.etaSz + (D.R.t : ℝ) + 2 ≤ large₂.sc.b` using `hP`. Establish `ht0 : (0 : ℝ) ≤ D.R.t` using `Nat.cast_nonneg _`.

Use `⟨Nat.le_floor (by linarith), ?_⟩` and prove the remaining obligations. Introduce `i r hr π w hw CL h τ`. Take `⟨g, ρ, -, hx, -⟩` from `hA i r hr w hw ⟨CL, h⟩ τ`. Establish `hj` using `D.nd.j_range i`. Take `⟨hfin, hcard⟩` from `JJ_finite_ncard large₂ hb hn (decide (AdmissibleParameterJ.TypeU D ep g)) (D.nd.j i) hj.1 hj.2 ρ`.

Establish `hpre : ((fun a : ℤ => (a : ℚ)) ⁻¹' AdmissibleParameterJ.JJ D (decide (AdmissibleParameterJ.TypeU D ep g)) (D.nd.j i) ρ).Finite` using `hfin.preimage (Int.cast_injective.injOn)`. Use `⟨hpre.toFinset, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hcard, ← Set.ncard_eq_toFinset_card _ hpre, ← Set.ncard_image_of_injective _ (Int.cast_injective (α := ℚ))]`. Conclude with `Set.ncard_le_ncard (Set.image_preimage_subset _ _) hfin`. Introduce `u hu`.

Establish `hu' : (u : ℚ) ∈ AdmissibleParameterJ.JJ D (decide (AdmissibleParameterJ.TypeU D ep g)) (D.nd.j i) ρ`. Simplify using `using hu`. Establish `hbd` using `he.1 _ hj.1 hj.2 ρ _ _ hu'`. Establish `hc0 : ((AdmissibleParameterJ.c0 D : ℚ) : ℝ) = ((D.R.t : ℝ) - 1) / 2`. Simplify using `[AdmissibleParameterJ.c0]`.

Rewrite `hbd` using `[hc0]`. Establish `habs : ((u.natAbs : ℕ) : ℝ) = |((u : ℚ) : ℝ)|`. Simplify using `[Nat.cast_natAbs]`. Establish `hle : u.natAbs + 1 ≤ ⌊2 * large₂.sc.b⌋₊`. Apply `Nat.le_floor` to reduce the goal to its premises.

Use `push_cast`. Rewrite using `[habs]`. Combine the linear equalities and inequalities to obtain the conclusion. Use linear arithmetic over natural numbers and integers. Introduce `a ha`.

Establish `: (a : ℚ) ∈ AdmissibleParameterJ.JJ D (decide (AdmissibleParameterJ.TypeU D ep g)) (D.nd.j i) ρ` using `(hx π a).1.1 ha`. Simplify using `using this`.
-/
theorem jumpWindow_of_jumpSets : ∀ (D : D7) (large₂ : SizeData₂ D), AdmissibleParameterJ.JumpConditions large₂ → EmbeddingTypeJumps.ParametersPolynomiallyBounded large₂ → D.R.t ≤ ⌊2 * large₂.sc.b⌋₊ ∧ ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r → ∀ π : D.nd.X i, GlobalTheory.BlockWindow.JumpWindow D i r π ⌊2 * large₂.sc.b⌋₊ := by
  classical
  intro D large₂ hJ hP
  obtain ⟨⟨ep, hA⟩, hb, -, -, he, -, -⟩ := hJ
  have hn : 0 < D.R.nV := by
    have := D.R.rank_add_five_le
    unfold Ranks.nV; omega
  have hS := large₂.Sc_pos
  have hη := large₂.etaSz_pos
  have hP' : large₂.Sc + large₂.etaSz + (D.R.t : ℝ) + 2 ≤ large₂.sc.b := hP
  have ht0 : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  refine ⟨Nat.le_floor (by linarith), ?_⟩
  intro i r hr π w hw CL h τ
  obtain ⟨g, ρ, -, hx, -⟩ := hA i r hr w hw ⟨CL, h⟩ τ
  have hj := D.nd.j_range i
  obtain ⟨hfin, hcard⟩ := JJ_finite_ncard large₂ hb hn (decide (AdmissibleParameterJ.TypeU D ep g)) (D.nd.j i) hj.1 hj.2 ρ
  have hpre : ((fun a : ℤ => (a : ℚ)) ⁻¹' AdmissibleParameterJ.JJ D (decide (AdmissibleParameterJ.TypeU D ep g)) (D.nd.j i) ρ).Finite :=
    hfin.preimage (Int.cast_injective.injOn)
  refine ⟨hpre.toFinset, ?_, ?_, ?_⟩
  · rw [← hcard, ← Set.ncard_eq_toFinset_card _ hpre,
      ← Set.ncard_image_of_injective _ (Int.cast_injective (α := ℚ))]
    exact Set.ncard_le_ncard (Set.image_preimage_subset _ _) hfin
  · intro u hu
    have hu' : (u : ℚ) ∈ AdmissibleParameterJ.JJ D (decide (AdmissibleParameterJ.TypeU D ep g)) (D.nd.j i) ρ := by
      simpa using hu
    have hbd := he.1 _ hj.1 hj.2 ρ _ _ hu'
    have hc0 : ((AdmissibleParameterJ.c0 D : ℚ) : ℝ) = ((D.R.t : ℝ) - 1) / 2 := by
      simp [AdmissibleParameterJ.c0]
    rw [hc0] at hbd
    have habs : ((u.natAbs : ℕ) : ℝ) = |((u : ℚ) : ℝ)| := by
      simp [Nat.cast_natAbs]
    have hle : u.natAbs + 1 ≤ ⌊2 * large₂.sc.b⌋₊ := by
      apply Nat.le_floor
      push_cast
      rw [habs]
      linarith
    omega
  · intro a ha
    have : (a : ℚ) ∈ AdmissibleParameterJ.JJ D (decide (AdmissibleParameterJ.TypeU D ep g)) (D.nd.j i) ρ := (hx π a).1.1 ha
    simpa using this

end GlobalTheory.BlockWindow
