import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HeckeLocalBlock
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.BlockDiagConjUnipotentLinear

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

section SlopeTestRemainingChoices

open UpperTheory.V.Af.Fin GroundTheory.Automorphic.AutomorphicForm

variable {R S : Type} [CommRing R] [CommRing S]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(1 : Matrix (Fin a) (Fin a) S) i j - s ((1 : Matrix (Fin a) (Fin a) R) i j) + s (g.val i j) - (1 : Matrix (Fin a) (Fin a) S) i j = s (g.val i j - (1 : Matrix (Fin a) (Fin a) R) i j)`. Rewrite using `[map_sub]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem corner_sub_one {a : ℕ} (s : R →ₙ+* S) (g : GL (Fin a) R) (i j : Fin a) :
    ((cornerGL a s g).val - 1) i j = s ((g.val - 1) i j) := by
  change (1 : Matrix (Fin a) (Fin a) S) i j - s ((1 : Matrix (Fin a) (Fin a) R) i j) + s (g.val i j)
    - (1 : Matrix (Fin a) (Fin a) S) i j = s (g.val i j - (1 : Matrix (Fin a) (Fin a) R) i j)
  rw [map_sub]
  ring

/- English proof (translation)
Use `Units.ext (sub_left_injective (b := (1 : Matrix (Fin n) (Fin n) S)) ?_)` and prove the remaining obligations. Use extensionality with `i j`. Use `beta_reduce`. Rewrite using `[corner_sub_one, coe_emb, coe_emb, add_sub_cancel_left, add_sub_cancel_left]`. Distinguish the cases in `hi : ∃ k, i = e k`.

Take `⟨k, rfl⟩` from `hi`. Distinguish the cases in `hj : ∃ l, j = e l`. Take `⟨l, rfl⟩` from `hj`. Rewrite using `[matrixExtendByZero_apply, matrixExtendByZero_apply, corner_sub_one]`. Use `push Not at hj`.

Rewrite using `[matrixExtendByZero_apply_of_outside_col e _ _ hj, matrixExtendByZero_apply_of_outside_col e _ _ hj, map_zero]`. Use `push Not at hi`. Rewrite using `[extendByZero_apply_eq_zero_of_row_not_mem e _ hi, extendByZero_apply_eq_zero_of_row_not_mem e _ hi, map_zero]`.
-/
private theorem corner_emb {a n : ℕ} (e : Fin a ↪ Fin n) (s : R →ₙ+* S) (g : GL (Fin a) R) :
    cornerGL n s (emb e g) = emb e (cornerGL a s g) := by
  refine Units.ext (sub_left_injective (b := (1 : Matrix (Fin n) (Fin n) S)) ?_)
  ext i j
  beta_reduce
  rw [corner_sub_one, coe_emb, coe_emb, add_sub_cancel_left, add_sub_cancel_left]
  by_cases hi : ∃ k, i = e k
  · obtain ⟨k, rfl⟩ := hi
    by_cases hj : ∃ l, j = e l
    · obtain ⟨l, rfl⟩ := hj
      rw [matrixExtendByZero_apply, matrixExtendByZero_apply, corner_sub_one]
    · push Not at hj
      rw [matrixExtendByZero_apply_of_outside_col e _ _ hj, matrixExtendByZero_apply_of_outside_col e _ _ hj, map_zero]
  · push Not at hi
    rw [extendByZero_apply_eq_zero_of_row_not_mem e _ hi, extendByZero_apply_eq_zero_of_row_not_mem e _ hi, map_zero]

/- English proof (translation)
Rewrite using `[blk, blk, map_mul, corner_emb, corner_emb]`.
-/
private theorem corner_blk {r t : ℕ} (s : R →ₙ+* S) (g : GL (Fin r) R) (h : GL (Fin t) R) :
    cornerGL (r + t) s (blk g h) = blk (cornerGL r s g) (cornerGL t s h) := by
  rw [blk, blk, map_mul, corner_emb, corner_emb]

/- English proof (translation)
Use `Units.ext (sub_left_injective (b := (1 : Matrix (Fin n) (Fin n) S)) ?_)` and prove the remaining obligations. Use extensionality with `i j`. Use `beta_reduce`. Rewrite using `[corner_sub_one]`. Apply the tactic sequence `change s ((1 + blockEntry X - 1) i j) = (1 + blockEntry (fun p => s (X p)) - 1) i j`.

Rewrite using `[add_sub_cancel_left, add_sub_cancel_left, blockEntry_apply, blockEntry_apply]`. Use `split_ifs`. Both sides reduce to the same expression. Conclude with `map_zero s`.
-/
private theorem corner_unip {n r : ℕ} (s : R →ₙ+* S) (X : UPos n r → R) :
    cornerGL n s (unipGL X) = unipGL fun p => s (X p) := by
  refine Units.ext (sub_left_injective (b := (1 : Matrix (Fin n) (Fin n) S)) ?_)
  ext i j
  beta_reduce
  rw [corner_sub_one]
  change s ((1 + blockEntry X - 1) i j) = (1 + blockEntry (fun p => s (X p)) - 1) i j
  rw [add_sub_cancel_left, add_sub_cancel_left, blockEntry_apply, blockEntry_apply]
  split_ifs
  · rfl
  · exact map_zero s

/- English proof (translation)
Take `⟨k, rfl⟩` from `hk`. Conclude with `⟨emb e k, emb_map e O.subtype k⟩`.
-/
private theorem emb_mem {L : Type} [Field L] (O : Subring L) {a n : ℕ} (e : Fin a ↪ Fin n) {k : GL (Fin a) L}
    (hk : k ∈ GLint (Fin a) O) : emb e k ∈ GLint (Fin n) O := by
  obtain ⟨k, rfl⟩ := hk
  exact ⟨emb e k, emb_map e O.subtype k⟩

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `E _ _ w r s`. Use `⟨fun b₁ b₂ => ?_, fun X => ?_, fun x y Y => ?_, fun k₁ h₁ k₂ h₂ => ?_⟩` and prove the remaining obligations. Simplify using `only [finGL, locGL, corner_blk]`. Simplify using `only [finGL, locGL, corner_unip]`. Conclude with `⟨_, rfl⟩`.

Take `⟨c, hc⟩` from `UpperTheory.blockDiag_conj_unipotent_linear (Ad E) r s x y`. Conclude with `⟨_, hc (Ad E) (RingHom.id _) Y⟩`. Conclude with `mul_mem (emb_mem _ _ h₁) (emb_mem _ _ h₂)`.
-/
theorem UpperTheory.V.Cj.S.gl2_local_to_adelic_embedding :
    UpperTheory.V.Cj.S.HeckeLocalBlock := by
  intro E _ _ w r s
  refine ⟨fun b₁ b₂ => ?_, fun X => ?_, fun x y Y => ?_, fun k₁ h₁ k₂ h₂ => ?_⟩
  · simp only [finGL, locGL, corner_blk]
  · simp only [finGL, locGL, corner_unip]
    exact ⟨_, rfl⟩
  · obtain ⟨c, hc⟩ := UpperTheory.blockDiag_conj_unipotent_linear (Ad E) r s x y
    exact ⟨_, hc (Ad E) (RingHom.id _) Y⟩
  · exact mul_mem (emb_mem _ _ h₁) (emb_mem _ _ h₂)
