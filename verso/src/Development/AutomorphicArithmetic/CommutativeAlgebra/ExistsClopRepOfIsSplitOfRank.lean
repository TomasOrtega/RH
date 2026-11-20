import Mathlib
import Development.AutomorphicArithmetic.RepresentationRank.RepOfRank
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsClopRepTrivial
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsClopRepOfDisjointOpenCover
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

/- English proof (translation)
Establish `hY : (Y₁ ⊗ Y₂).hom = pullback.fst Y₁.hom Y₂.hom ≫ Y₁.hom` using `rfl`. Rewrite using `[hY]`. Conclude with `⟨inferInstance, inferInstance⟩`.
-/
private lemma tensor_fe {S : Scheme.{0}} (Y₁ Y₂ : Over S) (h1 : IsFinite Y₁.hom) (e1 : Etale Y₁.hom)
    (h2 : IsFinite Y₂.hom) (e2 : Etale Y₂.hom) :
    IsFinite (Y₁ ⊗ Y₂).hom ∧ Etale (Y₁ ⊗ Y₂).hom := by
  have hY : (Y₁ ⊗ Y₂).hom = pullback.fst Y₁.hom Y₂.hom ≫ Y₁.hom := rfl
  rw [hY]
  exact ⟨inferInstance, inferInstance⟩

/- English proof (translation)
Use `⟨by simp, fun T V _ => ?_⟩` and prove the remaining obligations. Establish `hE : IsEmpty (T ⊗ G).left` using `⟨fun x => hG.false ((CartesianMonoidalCategory.snd T G).left x)⟩`. Establish `hV : V = ⊥`. Use extensionality with `x`. Conclude with `hE.elim x`.

Substitute `hV` using the available equality. Use `⟨Over.homMk T.hom (by simp), ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Conclude with `hE.elim x`. Introduce `y _`.

Use `ext`. Simplify using `using Over.w y`.
-/
private lemma rep_empty {S : Scheme.{0}} (G : Over S) (hG : IsEmpty G.left) :
    UpperTheory.RepresentationRank.Rep G (Over.mk (𝟙 S)) (⊥ : ((Over.mk (𝟙 S)) ⊗ G).left.Opens) := by
  refine ⟨by simp, fun T V _ => ?_⟩
  have hE : IsEmpty (T ⊗ G).left := ⟨fun x => hG.false ((CartesianMonoidalCategory.snd T G).left x)⟩
  have hV : V = ⊥ := by
    ext x
    exact hE.elim x
  subst hV
  refine ⟨Over.homMk T.hom (by simp), ?_, ?_⟩
  · ext x
    exact hE.elim x
  · intro y _
    ext
    simpa using Over.w y

/- English proof (translation)
Introduce `S G n`. Proceed by induction on `n generalizing G with`. Consider the case `zero`. Introduce `h`. Establish `hG : IsEmpty G.left` using `(GlobalTheory.FinEt.isSplitOfRank_zero_iff G.hom).1 h`.

Use `⟨Over.mk (𝟙 S), ⊥, rep_empty G hG, ?_, ?_⟩` and prove the remaining obligations. Use `show IsFinite (𝟙 S) infer_instance`. Use `show Etale (𝟙 S) infer_instance`. Consider the case `succ n ih`. Introduce `h`.

Take `⟨σ, hσ, V, hσp, hrange, hV⟩` from `h.exists_of_succ`. Take `⟨Y₁, U₁, hR₁, hf₁, he₁⟩` from `UpperTheory.exists_clopRep_trivial S`. Take `⟨Y₂, U₂, hR₂, hf₂, he₂⟩` from `ih (Over.mk (V.ι ≫ G.hom)) hV`. Take `⟨U, hU⟩` from `UpperTheory.exists_clopRep_of_disjoint_open_cover G (Over.mk (𝟙 S)) (Over.mk (V.ι ≫ G.hom)) Y₁ Y₂ (Over.homMk σ hσp) (Over.homMk V.ι rfl) U₁ U₂ hσ (show IsOpenImmersion V.ι from inferInstance) (show Set.range σ = (Set.range V.ι)ᶜ by rw [hrange, compl_compl]) hR₁ hR₂`. Conclude with `⟨Y₁ ⊗ Y₂, U, hU, tensor_fe Y₁ Y₂ hf₁ he₁ hf₂ he₂⟩`.
-/
theorem UpperTheory.exists_clopRep_of_isSplitOfRank :
    ∀ {S : Scheme.{0}} (G : Over S) (n : ℕ), GlobalTheory.FinEt.IsSplitOfRank G.hom n → ∃ (Y : Over S) (U : (Y ⊗ G).left.Opens), UpperTheory.RepresentationRank.Rep G Y U ∧ IsFinite Y.hom ∧ Etale Y.hom := by
  intro S G n
  induction n generalizing G with
  | zero =>
    intro h
    have hG : IsEmpty G.left := (GlobalTheory.FinEt.isSplitOfRank_zero_iff G.hom).1 h
    refine ⟨Over.mk (𝟙 S), ⊥, rep_empty G hG, ?_, ?_⟩
    · show IsFinite (𝟙 S)
      infer_instance
    · show Etale (𝟙 S)
      infer_instance
  | succ n ih =>
    intro h
    obtain ⟨σ, hσ, V, hσp, hrange, hV⟩ := h.exists_of_succ
    obtain ⟨Y₁, U₁, hR₁, hf₁, he₁⟩ := UpperTheory.exists_clopRep_trivial S
    obtain ⟨Y₂, U₂, hR₂, hf₂, he₂⟩ := ih (Over.mk (V.ι ≫ G.hom)) hV
    obtain ⟨U, hU⟩ := UpperTheory.exists_clopRep_of_disjoint_open_cover G (Over.mk (𝟙 S)) (Over.mk (V.ι ≫ G.hom)) Y₁ Y₂
      (Over.homMk σ hσp) (Over.homMk V.ι rfl) U₁ U₂ hσ (show IsOpenImmersion V.ι from inferInstance)
      (show Set.range σ = (Set.range V.ι)ᶜ by rw [hrange, compl_compl]) hR₁ hR₂
    exact ⟨Y₁ ⊗ Y₂, U, hU, tensor_fe Y₁ Y₂ hf₁ he₁ hf₂ he₂⟩
