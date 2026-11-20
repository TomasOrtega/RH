import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.LetAct
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.InPsiOrInPsiConjugate
open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.FrameRead
open scoped Classical

set_option autoImplicit false

namespace GlobalTheory.FrameRead

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.CMTypeOrConjugate.inPsi_or_inPsi_conjugate`. Consider the case `exact _root_.GlobalTheory.CMTypeOrConjugate.inPsi_or_inPsi_conjugate`. Consider the case `(apply _root_.GlobalTheory.CMTypeOrConjugate.inPsi_or_inPsi_conjugate <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.CMTypeOrConjugate.inPsi_or_inPsi_conjugate <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.CMTypeOrConjugate.inPsi_or_inPsi_conjugate <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.CMTypeOrConjugate.inPsi_or_inPsi_conjugate ..)`.
-/
theorem inPsi_or_conjugate_unit {E : Type} [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (τ : E →+* ℂ) :
    InPsi H τ ∨ InPsi H (ComplexEmbedding.conjugate τ) := by
  first
  | exact @_root_.GlobalTheory.CMTypeOrConjugate.inPsi_or_inPsi_conjugate
  | exact _root_.GlobalTheory.CMTypeOrConjugate.inPsi_or_inPsi_conjugate
  | (apply _root_.GlobalTheory.CMTypeOrConjugate.inPsi_or_inPsi_conjugate <;> assumption)
  | (intros; apply _root_.GlobalTheory.CMTypeOrConjugate.inPsi_or_inPsi_conjugate <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CMTypeOrConjugate.inPsi_or_inPsi_conjugate <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CMTypeOrConjugate.inPsi_or_inPsi_conjugate ..)

/- English proof (translation)
Introduce `E _ _ _ H Dw n Ix _ pl hpl _ l c ga h hU`. Establish `hval : ((Matrix.nonsingInvUnit ga h : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = ga` using `rfl`. Establish `hinv : (((Matrix.nonsingInvUnit ga h : GL (Fin n) E)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = ga.conjTranspose`. Rewrite using `[Matrix.coe_units_inv, hval]`. Conclude with `Matrix.inv_eq_left_inv hU`.

Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce and unpack `⟨τ, i, b⟩`. Simplify using `only [Formalism.L2.Pj.gaStar, letAct, aeval_X, letB]`. Use `split_ifs with h1 h2`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Use `congr 2`. Establish `e : (invTrK (embGL (fun t => embF c (pl t)) (Matrix.nonsingInvUnit ga h)) h1.choose : Matrix (Fin n) (Fin n) c.F) j b = embF c (pl h1.choose) ((((Matrix.nonsingInvUnit ga h : GL (Fin n) E)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) b j)` using `rfl`. Rewrite using `[e, hinv, h1.choose_spec]`. Both sides reduce to the same expression. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Use `congr 2`. Establish `e : (((invTrK (embGL (fun t => embF c (pl t)) (Matrix.nonsingInvUnit ga h)) h2.choose)⁻¹ : GL (Fin n) c.F) : Matrix (Fin n) (Fin n) c.F) b j = embF c (pl h2.choose) (ga j b)` using `rfl`. Rewrite using `[e]`. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `τ (IsCMField.complexConj E (ga j b)) = pl h2.choose (ga j b)`.

Establish `hs` using `h2.choose_spec`. Generalize the expression as in `h2.choose = t at hs ⊢`. Substitute `hs` using the available equality. Rewrite using `[IsCMField.complexEmbedding_complexConj]`. Simplify using the standard rewrite rules.

It suffices to derive a contradiction. Break down `inPsi_or_conjugate_unit H τ with h3 | h3` into its components or cases. Conclude with `h1 ((hpl.2 τ).1 h3)`. Take `⟨t, ht⟩` from `(hpl.2 _).1 h3`. Conclude with `h2 ⟨t, by rw [ht]; ext x; simp⟩`.
-/
theorem gaStar_conj_eq_letAct : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (n : ℕ) (Ix : Type) [Fintype Ix] (pl : Ix → (E →+* ℂ)), IsEnum H pl → Dw.p + Dw.q ≤ n → ∀ (l : Level H) (c : Coeff l) (ga : Matrix (Fin n) (Fin n) E) (h : IsUnit ga.det), ga.conjTranspose * ga = 1 → gaStar (Dw := Dw) c (ga.map (IsCMField.complexConj E)) = letAct Dw pl c.F (invTrK (embGL (fun t => embF c (pl t)) (Matrix.nonsingInvUnit ga h))) := by
  intro E _ _ _ H Dw n Ix _ pl hpl _ l c ga h hU
  have hval : ((Matrix.nonsingInvUnit ga h : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = ga := rfl
  have hinv : (((Matrix.nonsingInvUnit ga h : GL (Fin n) E)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)
      = ga.conjTranspose := by
    rw [Matrix.coe_units_inv, hval]
    exact Matrix.inv_eq_left_inv hU
  apply MvPolynomial.algHom_ext
  rintro ⟨τ, i, b⟩
  simp only [Formalism.L2.Pj.gaStar, letAct, aeval_X, letB]
  split_ifs with h1 h2
  · refine Finset.sum_congr rfl fun j _ => ?_
    congr 2
    have e : (invTrK (embGL (fun t => embF c (pl t)) (Matrix.nonsingInvUnit ga h)) h1.choose :
        Matrix (Fin n) (Fin n) c.F) j b = embF c (pl h1.choose)
          ((((Matrix.nonsingInvUnit ga h : GL (Fin n) E)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) b j) := rfl
    rw [e, hinv, h1.choose_spec]
    rfl
  · refine Finset.sum_congr rfl fun j _ => ?_
    congr 2
    have e : (((invTrK (embGL (fun t => embF c (pl t)) (Matrix.nonsingInvUnit ga h)) h2.choose)⁻¹ : GL (Fin n) c.F) :
        Matrix (Fin n) (Fin n) c.F) b j = embF c (pl h2.choose) (ga j b) := rfl
    rw [e]
    apply Subtype.ext
    change τ (IsCMField.complexConj E (ga j b)) = pl h2.choose (ga j b)
    have hs := h2.choose_spec
    generalize h2.choose = t at hs ⊢
    subst hs
    rw [IsCMField.complexEmbedding_complexConj]
    simp
  · exfalso
    rcases inPsi_or_conjugate_unit H τ with h3 | h3
    · exact h1 ((hpl.2 τ).1 h3)
    · obtain ⟨t, ht⟩ := (hpl.2 _).1 h3
      exact h2 ⟨t, by rw [ht]; ext x; simp⟩

end GlobalTheory.FrameRead
