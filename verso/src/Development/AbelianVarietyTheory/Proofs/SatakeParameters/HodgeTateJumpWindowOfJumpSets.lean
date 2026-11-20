import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JumpWindow

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.BlockWindow

open Formalism.MainNotions.AdmissibleParameterJ in

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Split into cases according to the possible forms of the given data. Treat this case separately. Treat this case separately.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Combine the linear equalities and inequalities to obtain the conclusion. Establish an intermediate fact.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components.

Assume the hypotheses and unpack their components. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Use the resulting assumption. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Supply the required witnesses or components.
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
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions.

Use linear arithmetic over natural numbers and integers. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Move the embeddings inside the algebraic operations.

Rewrite the conclusion using the stated equalities. Combine the linear equalities and inequalities to obtain the conclusion. Use linear arithmetic over natural numbers and integers. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
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
