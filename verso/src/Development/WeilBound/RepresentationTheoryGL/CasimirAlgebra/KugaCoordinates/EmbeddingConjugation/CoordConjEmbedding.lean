import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.IsStarRep

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WigAlg Formalism.REAL
open scoped Classical

namespace PositivityTheory.Rg.Cz.J

section
variable {E : Type} [Field E] [NumberField E]

omit [NumberField E] in

/- English proof (translation)
Apply the tactic sequence `unfold atEmb; split_ifs <;> simp_all`.
-/
theorem atEmb_embedding (w : InfinitePlace E) (z : ℂ) : atEmb w.embedding z = (Pi.single w z : Cinf E) := by
  unfold atEmb; split_ifs <;> simp_all

omit [NumberField E] in

/- English proof (translation)
Apply the tactic sequence `unfold coord; split_ifs <;> simp_all`.
-/
theorem coord_embedding (w : InfinitePlace E) (c : Cinf E) : coord w.embedding c = c w := by
  unfold coord; split_ifs <;> simp_all

/- English proof (translation)
Use `set τ := ComplexEmbedding.conjugate w.embedding`. Establish `hs : ∀ z : ℂ, (Pi.single w z : Cinf E) = atEmb τ (starRingEnd ℂ z)`. Introduce `z`. Rewrite using `[atEmb_conj, Complex.conj_conj, atEmb_embedding]`. Establish `h1 : coord τ (Pi.single w 1) = 1` using `by rw [hs, map_one, coord_atEmb]`.

Establish `h0 : ∀ v, v ≠ w → ∀ z : ℂ, coord τ (Pi.single v z) = 0`. Introduce `v hv z`. Establish `e0 : (Pi.single w 1 : Cinf E) * Pi.single v z = 0`. Use function extensionality and compare the values at `u`. Distinguish the cases in `hu : u = w`.

Substitute `hu` using the available equality. Simplify using `[Pi.single_eq_of_ne' hv]`. Simplify using `[Pi.single_eq_of_ne hu]`. Use `congrArg (coord τ) e0` as an intermediate fact. Rewrite `this` using `[map_mul, h1, one_mul, map_zero]`.

Conclude with `this`. Establish `hc : c = ∑ v, (Pi.single v (c v) : Cinf E)` using `(Finset.univ_sum_single c).symm`. Use `conv_lhs => rw [hc]`. Rewrite using `[map_sum, Finset.sum_eq_single w (fun v _ hv => h0 v hv _) (by simp), hs, coord_atEmb]`.
-/
theorem coord_conj_embedding [IsTotallyComplex E] (w : InfinitePlace E) (c : Cinf E) :
    coord (ComplexEmbedding.conjugate w.embedding) c = starRingEnd ℂ (c w) := by
  set τ := ComplexEmbedding.conjugate w.embedding
  have hs : ∀ z : ℂ, (Pi.single w z : Cinf E) = atEmb τ (starRingEnd ℂ z) := by
    intro z; rw [atEmb_conj, Complex.conj_conj, atEmb_embedding]
  have h1 : coord τ (Pi.single w 1) = 1 := by rw [hs, map_one, coord_atEmb]
  have h0 : ∀ v, v ≠ w → ∀ z : ℂ, coord τ (Pi.single v z) = 0 := by
    intro v hv z
    have e0 : (Pi.single w 1 : Cinf E) * Pi.single v z = 0 := by
      funext u; by_cases hu : u = w
      · subst hu; simp [Pi.single_eq_of_ne' hv]
      · simp [Pi.single_eq_of_ne hu]
    have := congrArg (coord τ) e0
    rw [map_mul, h1, one_mul, map_zero] at this
    exact this
  have hc : c = ∑ v, (Pi.single v (c v) : Cinf E) := (Finset.univ_sum_single c).symm
  conv_lhs => rw [hc]
  rw [map_sum, Finset.sum_eq_single w (fun v _ hv => h0 v hv _) (by simp), hs, coord_atEmb]

/- English proof (translation)
Rewrite using `[← Finset.sum_fiberwise Finset.univ (fun τ => InfinitePlace.mk τ) f]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Establish `hne : w.embedding ≠ ComplexEmbedding.conjugate w.embedding`. Introduce `h`. Conclude with `(InfinitePlace.isComplex_iff.1 (IsTotallyComplex.isComplex w)) (ComplexEmbedding.isReal_iff.2 h.symm)`.

Establish `hf : Finset.univ.filter (fun τ : E →+* ℂ => InfinitePlace.mk τ = w) = {w.embedding, ComplexEmbedding.conjugate w.embedding}`. Use extensionality with `τ`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Substitute `h` using the available equality. Break down `InfinitePlace.mk_eq_iff.1 (InfinitePlace.mk_embedding (InfinitePlace.mk τ)) with h | h` into its components or cases. Conclude with `Or.inl h.symm`. Conclude with `Or.inr h.symm`. Apply the tactic sequence `rintro (h | h) <;> subst h <;> simp [InfinitePlace.mk_conjugate_eq]`.

Rewrite using `[hf, Finset.sum_pair hne]`.
-/
theorem sum_emb [IsTotallyComplex E] {R : Type*} [AddCommMonoid R] (f : (E →+* ℂ) → R) :
    ∑ τ, f τ = ∑ w : InfinitePlace E, (f w.embedding + f (ComplexEmbedding.conjugate w.embedding)) := by
  rw [← Finset.sum_fiberwise Finset.univ (fun τ => InfinitePlace.mk τ) f]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hne : w.embedding ≠ ComplexEmbedding.conjugate w.embedding := by
    intro h
    exact (InfinitePlace.isComplex_iff.1 (IsTotallyComplex.isComplex w)) (ComplexEmbedding.isReal_iff.2 h.symm)
  have hf : Finset.univ.filter (fun τ : E →+* ℂ => InfinitePlace.mk τ = w) =
      {w.embedding, ComplexEmbedding.conjugate w.embedding} := by
    ext τ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro h
      subst h
      rcases InfinitePlace.mk_eq_iff.1 (InfinitePlace.mk_embedding (InfinitePlace.mk τ)) with h | h
      · exact Or.inl h.symm
      · exact Or.inr h.symm
    · rintro (h | h) <;> subst h <;> simp [InfinitePlace.mk_conjugate_eq]
  rw [hf, Finset.sum_pair hne]

end

/- English proof (translation)
Introduce `E _ _ _ a N _ _ _ _ φ X`. Set `Φ : Matrix (Fin a) (Fin a) (Cinf E) →ₗ[ℝ] N` to `{ toFun := fun A => φ (toL A) map_add' := fun A B => φ.map_add (toL A) (toL B) map_smul' := fun r A => φ.map_smul r (toL A) }`. Set `ψ : Fin a → Fin a → Cinf E →ₗ[ℝ] N` to `fun i j => Φ ∘ₗ (Matrix.singleLinearMap ℝ i j)`. Establish `hψ : ∀ i j z, ψ i j z = φ (toL (Matrix.single i j z))` using `fun _ _ _ => rfl`. Establish `hcx : ∀ τ i j, cx τ φ i j = (1 / 2 : ℂ) • (ψ i j (atEmb τ 1) - Complex.I • ψ i j (atEmb τ Complex.I))` using `fun _ _ _ => rfl`.

Establish `key : ∀ (w : InfinitePlace E) (i j : Fin a) (c : Cinf E), coord w.embedding c • cx w.embedding φ i j + coord (ComplexEmbedding.conjugate w.embedding) c • cx (ComplexEmbedding.conjugate w.embedding) φ i j = ψ i j (Pi.single w (c w))`. Introduce `w i j c`. Establish `hz : (Pi.single w (c w) : Cinf E) = (c w).re • (Pi.single w 1 : Cinf E) + (c w).im • (Pi.single w Complex.I : Cinf E)`. Rewrite using `[← atEmb_embedding, atEmb_eq, atEmb_embedding, atEmb_embedding]`. Rewrite using `[coord_embedding, coord_conj_embedding, hcx, hcx]`.

Simplify using `only [atEmb_conj, map_one, Complex.conj_I, atEmb_embedding, Pi.single_neg, map_neg]`. Rewrite using `[hz, map_add, map_smul, map_smul, ← algebraMap_smul ℂ (c w).re, ← algebraMap_smul ℂ (c w).im]`. Generalize the expression as in `ψ i j (Pi.single w 1) = P`. Generalize the expression as in `ψ i j (Pi.single w Complex.I) = Q`. Use `conv_lhs => rw [← Complex.re_add_im (c w)]`.

Simplify using `only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]`. Apply the tactic sequence `match_scalars <;> apply Complex.ext <;> simp <;> ring`. Establish `hX : φ X = ∑ i, ∑ j, ψ i j (X i j)`. Rewrite using `[show φ X = Φ (Matrix.of X) from rfl, Matrix.matrix_eq_sum_single (Matrix.of X), map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[map_sum]`. Both sides reduce to the same expression. Rewrite using `[hX]`. Use `symm`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[sum_emb (fun τ => coord τ (X i j) • cx τ φ i j), Finset.sum_congr rfl fun w _ => key w i j (X i j), ← map_sum, Finset.univ_sum_single]`.
-/
theorem cxExpand_holds : CxExpand := by
  intro E _ _ _ a N _ _ _ _ φ X
  let Φ : Matrix (Fin a) (Fin a) (Cinf E) →ₗ[ℝ] N :=
    { toFun := fun A => φ (toL A)
      map_add' := fun A B => φ.map_add (toL A) (toL B)
      map_smul' := fun r A => φ.map_smul r (toL A) }
  let ψ : Fin a → Fin a → Cinf E →ₗ[ℝ] N := fun i j => Φ ∘ₗ (Matrix.singleLinearMap ℝ i j)
  have hψ : ∀ i j z, ψ i j z = φ (toL (Matrix.single i j z)) := fun _ _ _ => rfl
  have hcx : ∀ τ i j, cx τ φ i j = (1 / 2 : ℂ) • (ψ i j (atEmb τ 1) - Complex.I • ψ i j (atEmb τ Complex.I)) :=
    fun _ _ _ => rfl
  have key : ∀ (w : InfinitePlace E) (i j : Fin a) (c : Cinf E),
      coord w.embedding c • cx w.embedding φ i j +
          coord (ComplexEmbedding.conjugate w.embedding) c • cx (ComplexEmbedding.conjugate w.embedding) φ i j =
        ψ i j (Pi.single w (c w)) := by
    intro w i j c
    have hz : (Pi.single w (c w) : Cinf E) =
        (c w).re • (Pi.single w 1 : Cinf E) + (c w).im • (Pi.single w Complex.I : Cinf E) := by
      rw [← atEmb_embedding, atEmb_eq, atEmb_embedding, atEmb_embedding]
    rw [coord_embedding, coord_conj_embedding, hcx, hcx]
    simp only [atEmb_conj, map_one, Complex.conj_I, atEmb_embedding, Pi.single_neg, map_neg]
    rw [hz, map_add, map_smul, map_smul, ← algebraMap_smul ℂ (c w).re, ← algebraMap_smul ℂ (c w).im]
    generalize ψ i j (Pi.single w 1) = P
    generalize ψ i j (Pi.single w Complex.I) = Q
    conv_lhs => rw [← Complex.re_add_im (c w)]
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    match_scalars <;> apply Complex.ext <;> simp <;> ring
  have hX : φ X = ∑ i, ∑ j, ψ i j (X i j) := by
    rw [show φ X = Φ (Matrix.of X) from rfl, Matrix.matrix_eq_sum_single (Matrix.of X), map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum]
    rfl
  rw [hX]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sum_emb (fun τ => coord τ (X i j) • cx τ φ i j), Finset.sum_congr rfl fun w _ => key w i j (X i j), ← map_sum,
    Finset.univ_sum_single]

end PositivityTheory.Rg.Cz.J

end
