import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.LetAct
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaLetterEquivConjugate

open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.FrameRead
open scoped Classical

namespace GlobalTheory.FrameRead

open GlobalTheory.Harm Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  (Dw : Datum H) {n : ℕ} {Ix : Type} [Fintype Ix] {pl : Ix → (E →+* ℂ)}

noncomputable def IsEnum.idx (h : IsEnum H pl) (t : {τ : E →+* ℂ // InPsi H τ}) : Ix :=
  ((h.2 t.1).1 t.2).choose

omit [Fintype Ix] in

/- English proof (translation)
The claim follows from `((h.2 t.1).1 t.2).choose_spec`.
-/
theorem IsEnum.pl_idx (h : IsEnum H pl) (t : {τ : E →+* ℂ // InPsi H τ}) : pl (h.idx t) = t.1 :=
  ((h.2 t.1).1 t.2).choose_spec

/- English proof (translation)
Use `DFunLike.congr_fun (?_ : (rename (thetaLetterEquiv Dw n)).comp (letAct Dw pl K g) = (colSubst _ _).comp (rename (thetaLetterEquiv Dw n))) P` and prove the remaining obligations. Use `MvPolynomial.algHom_ext fun ⟨τ, i, b⟩ => ?_` and prove the remaining obligations. Rewrite using `[AlgHom.comp_apply, AlgHom.comp_apply, rename_X, letAct, aeval_X]`. Break down `half_cases (Ψ := InPsi H) (ComplexEmbedding.involutive_conjugate E) (not_mem_hostType_iff H) τ with hτ | ⟨τ, hτ, rfl⟩` into its components or cases. Establish `h1 : ∃ t, pl t = τ` using `(h.2 τ).1 hτ`.

Rewrite using `[dif_pos h1, thetaLetterEquiv_of_mem Dw hτ, colSubst_X_xVar, xForm_apply, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, rename_C, rename_X, thetaLetterEquiv_of_mem Dw hτ]`. Both sides reduce to the same expression. Establish `h1 : ¬ ∃ t, pl t = ComplexEmbedding.conjugate τ` using `fun h1 => ((not_mem_hostType_iff H τ).2 ((h.2 _).2 h1)) hτ`.

Establish `h2 : ∃ t, ComplexEmbedding.conjugate (pl t) = ComplexEmbedding.conjugate τ` using `⟨h.idx ⟨τ, hτ⟩, by rw [h.pl_idx]⟩`. Establish `h3 : h2.choose = h.idx ⟨τ, hτ⟩` using `h.1 (by`. Rewrite using `[h.pl_idx]`. Conclude with `(ComplexEmbedding.involutive_conjugate E).injective h2.choose_spec)`. Rewrite using `[dif_neg h1, dif_pos h2, thetaLetterEquiv_conjugate Dw hτ, colSubst_X_yVar, yForm_apply, map_sum, h3]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, rename_C, rename_X, thetaLetterEquiv_conjugate Dw hτ]`. Both sides reduce to the same expression.
-/
theorem rename_letAct (h : IsEnum H pl) {K : Type} [Field K] (g : Ix → GL (Fin n) K)
    (P : MvPolynomial (LtN Dw n) K) :
    rename (thetaLetterEquiv Dw n) (letAct Dw pl K g P) =
      colSubst (fun t => (g (h.idx t) : Matrix (Fin n) (Fin n) K)ᵀ)
        (fun t => (((g (h.idx t))⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ)
        (rename (thetaLetterEquiv Dw n) P) := by
  refine DFunLike.congr_fun (?_ : (rename (thetaLetterEquiv Dw n)).comp (letAct Dw pl K g) =
    (colSubst _ _).comp (rename (thetaLetterEquiv Dw n))) P
  refine MvPolynomial.algHom_ext fun ⟨τ, i, b⟩ => ?_
  rw [AlgHom.comp_apply, AlgHom.comp_apply, rename_X, letAct, aeval_X]
  rcases half_cases (Ψ := InPsi H) (ComplexEmbedding.involutive_conjugate E)
    (not_mem_hostType_iff H) τ with hτ | ⟨τ, hτ, rfl⟩
  · have h1 : ∃ t, pl t = τ := (h.2 τ).1 hτ
    rw [dif_pos h1, thetaLetterEquiv_of_mem Dw hτ, colSubst_X_xVar, xForm_apply, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, rename_C, rename_X, thetaLetterEquiv_of_mem Dw hτ]
    rfl
  · have h1 : ¬ ∃ t, pl t = ComplexEmbedding.conjugate τ := fun h1 =>
      ((not_mem_hostType_iff H τ).2 ((h.2 _).2 h1)) hτ
    have h2 : ∃ t, ComplexEmbedding.conjugate (pl t) = ComplexEmbedding.conjugate τ :=
      ⟨h.idx ⟨τ, hτ⟩, by rw [h.pl_idx]⟩
    have h3 : h2.choose = h.idx ⟨τ, hτ⟩ := h.1 (by
      rw [h.pl_idx]
      exact (ComplexEmbedding.involutive_conjugate E).injective h2.choose_spec)
    rw [dif_neg h1, dif_pos h2, thetaLetterEquiv_conjugate Dw hτ, colSubst_X_yVar, yForm_apply,
      map_sum, h3]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, rename_C, rename_X, thetaLetterEquiv_conjugate Dw hτ]
    rfl

/- English proof (translation)
Introduce `E _ _ _ H Dw n Ix _ pl h _ K _ _ a`. Establish `hinj` using `rename_injective (R := K) _ (thetaLetterEquiv Dw n).injective`. Use `⟨fun g g' => AlgHom.ext fun P => hinj ?_, AlgHom.ext fun P => hinj ?_, fun g P hP => ?_⟩` and prove the remaining obligations. Rewrite using `[AlgHom.comp_apply, rename_letAct Dw h, rename_letAct Dw h, rename_letAct Dw h, ← AlgHom.comp_apply (colSubst _ _) (colSubst _ _), colSubst_comp]`. Simplify using `only [Pi.mul_apply, _root_.mul_inv_rev, Units.val_mul, transpose_mul]`.

Rewrite using `[rename_letAct Dw h]`. Simplify using `only [Pi.one_apply, inv_one, Units.val_one, transpose_one, colSubst_one, AlgHom.id_apply]`. Establish `key` using `mem_HHa_iff_rename (Ψ := InPsi H) (dim := Dw.mult) (n := n) (K := K) (ComplexEmbedding.involutive_conjugate E) (not_mem_hostType_iff H) (fun _ => mult_of_mem Dw) (fun _ => mult_conjEmb_of_mem Dw) (fun τ i => a (τ, i))`. Take `⟨h₁, h₂, h₃⟩` from `(key P).1 hP`. Use `(key _).2 ?_` and prove the remaining obligations.

Establish `e` using `rename_letAct Dw h g P`. Unfold `thetaLetterEquiv at e`. Rewrite using `[e]`. Conclude with `⟨h₁.colSubst fun t => by rw [← transpose_mul, Units.inv_mul, transpose_one], fun t r => colSubst_isWeightedHomogeneous _ _ _ (h₂ t r), fun t r r' hr s => by rw [rowAdd_colSubst _ _ t hr.isLeft_eq, h₃ t r r' hr]⟩`.
-/
theorem letAct_mul_one_mem_HHa :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (n : ℕ) (Ix : Type) [Fintype Ix] (pl : Ix → (E →+* ℂ)), IsEnum H pl → Dw.p + Dw.q ≤ n → ∀ (K : Type) [Field K] [CharZero K] (a : (E →+* ℂ) × ℕ → ℕ), (∀ g g' : Ix → GL (Fin n) K, letAct Dw pl K (g * g') = (letAct Dw pl K g).comp (letAct Dw pl K g')) ∧ letAct Dw pl K (1 : Ix → GL (Fin n) K) = AlgHom.id K _ ∧ ∀ (g : Ix → GL (Fin n) K), ∀ P ∈ HHa Dw.mult n K ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), letAct Dw pl K g P ∈ HHa Dw.mult n K ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) := by
  intro E _ _ _ H Dw n Ix _ pl h _ K _ _ a
  have hinj := rename_injective (R := K) _ (thetaLetterEquiv Dw n).injective
  refine ⟨fun g g' => AlgHom.ext fun P => hinj ?_, AlgHom.ext fun P => hinj ?_, fun g P hP => ?_⟩
  · rw [AlgHom.comp_apply, rename_letAct Dw h, rename_letAct Dw h, rename_letAct Dw h,
      ← AlgHom.comp_apply (colSubst _ _) (colSubst _ _), colSubst_comp]
    simp only [Pi.mul_apply, _root_.mul_inv_rev, Units.val_mul, transpose_mul]
  · rw [rename_letAct Dw h]
    simp only [Pi.one_apply, inv_one, Units.val_one, transpose_one, colSubst_one, AlgHom.id_apply]
  · have key := mem_HHa_iff_rename (Ψ := InPsi H) (dim := Dw.mult) (n := n) (K := K)
      (ComplexEmbedding.involutive_conjugate E) (not_mem_hostType_iff H)
      (fun _ => mult_of_mem Dw) (fun _ => mult_conjEmb_of_mem Dw) (fun τ i => a (τ, i))
    obtain ⟨h₁, h₂, h₃⟩ := (key P).1 hP
    refine (key _).2 ?_
    have e := rename_letAct Dw h g P
    unfold thetaLetterEquiv at e
    rw [e]
    exact ⟨h₁.colSubst fun t => by rw [← transpose_mul, Units.inv_mul, transpose_one],
      fun t r => colSubst_isWeightedHomogeneous _ _ _ (h₂ t r),
      fun t r r' hr s => by rw [rowAdd_colSubst _ _ t hr.isLeft_eq, h₃ t r r' hr]⟩

end GlobalTheory.FrameRead
