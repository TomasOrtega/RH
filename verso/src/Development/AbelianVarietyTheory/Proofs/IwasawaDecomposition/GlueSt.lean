import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

namespace GlobalTheory.TorRef

/- English proof (translation)
Introduce `X X' U Y π j g hred hj hd hY hext`. Use `choose V h hxV hV using hext`. Establish `hsep : IsSeparated (terminal.from Y)` using `hY.isSeparated_terminal_from`. Establish `compat : ∀ a b, pullback.fst (V a).ι (V b).ι ≫ h a = pullback.snd (V a).ι (V b).ι ≫ h b`. Introduce `a b`.

Set `p : pullback (V a).ι (V b).ι ⟶ X'` to `pullback.fst (V a).ι (V b).ι ≫ (V a).ι`. Establish `hp : pullback.snd (V a).ι (V b).ι ≫ (V b).ι = p` using `(pullback.condition).symm`. Establish `hopen : IsOpenMap p` using `p.isOpenEmbedding.isOpenMap`. Establish `hdom : IsDominant (pullback.fst (p ≫ π) j)`. Use `⟨?_⟩` and prove the remaining obligations.

Establish `hr` using `Scheme.Pullback.range_fst (p ≫ π) j`. Establish `hden : Dense (p ⁻¹' (π ⁻¹' Set.range j))` using `hd.preimage hopen`. Establish `he : Set.range (pullback.fst (p ≫ π) j) = p ⁻¹' (π ⁻¹' Set.range j)`. Rewrite using `[hr]`. Use extensionality with `x`.

Simplify using the standard rewrite rules. Use `show Dense (Set.range (pullback.fst (p ≫ π) j))`. Rewrite using `[he]`. Conclude with `hden`. Establish `: AlgebraicGeometry.IsReduced (pullback (V a).ι (V b).ι)` using `isReduced_of_isOpenImmersion p`.

Use `ext_of_isDominant_of_isSeparated (terminal.from Y) (terminal.hom_ext _ _) (pullback.fst (p ≫ π) j) ?_` and prove the remaining obligations. Establish `hqr : pullback.fst (p ≫ π) j ≫ p ≫ π = pullback.snd (p ≫ π) j ≫ j` using `pullback.condition`. Establish `hA : pullback.fst (V a).ι (V b).ι ≫ (V a).ι ≫ π = p ≫ π` using `(Category.assoc _ _ _).symm`. Establish `hB : pullback.snd (V a).ι (V b).ι ≫ (V b).ι ≫ π = p ≫ π` using `by rw [← Category.assoc, hp]`. Establish `h₁` using `hV a _ (pullback.fst (p ≫ π) j ≫ pullback.fst (V a).ι (V b).ι) (pullback.snd (p ≫ π) j) ((Category.assoc _ _ _).trans ((congrArg (pullback.fst (p ≫ π) j ≫ ·) hA).trans hqr))`.

Establish `h₂` using `hV b _ (pullback.fst (p ≫ π) j ≫ pullback.snd (V a).ι (V b).ι) (pullback.snd (p ≫ π) j) ((Category.assoc _ _ _).trans ((congrArg (pullback.fst (p ≫ π) j ≫ ·) hB).trans hqr))`. Conclude with `(Category.assoc _ _ _).symm.trans (h₁.trans (h₂.symm.trans (Category.assoc _ _ _)))`. Establish `hcov : IsOpenCover V` using `eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxV x⟩`. Set `𝒰` to `X'.openCoverOfIsOpenCover V hcov`. Take `⟨G, hι⟩ : ∃ G : X' ⟶ Y, ∀ x, (V x).ι ≫ G = h x` from `⟨𝒰.glueMorphisms h compat, fun x => 𝒰.ι_glueMorphisms h compat x⟩`.

Use `⟨G, fun T a u hau => ?_⟩` and prove the remaining obligations. Establish `hcovT : IsOpenCover (fun x => a ⁻¹ᵁ V x)` using `eq_top_iff.2 fun t _ => TopologicalSpace.Opens.mem_iSup.2 ⟨a t, hxV (a t)⟩`. Use `(T.openCoverOfIsOpenCover _ hcovT).hom_ext _ _ fun (x : X') => ?_` and prove the remaining obligations. Use `show (a ⁻¹ᵁ V x).ι ≫ a ≫ G = (a ⁻¹ᵁ V x).ι ≫ u ≫ g`. Establish `hr : (a ∣_ V x) ≫ (V x).ι = (a ⁻¹ᵁ V x).ι ≫ a` using `morphismRestrict_ι a (V x)`.

Establish `h₃` using `hV x _ (a ∣_ V x) ((a ⁻¹ᵁ V x).ι ≫ u) (by rw [reassoc_of% hr, hau, Category.assoc])`. Rewrite using `[← reassoc_of% hr, hι x, h₃, Category.assoc]`.
-/
theorem glueSt : GlueSt := by
  intro X X' U Y π j g hred hj hd hY hext
  choose V h hxV hV using hext
  have hsep : IsSeparated (terminal.from Y) := hY.isSeparated_terminal_from
  have compat : ∀ a b, pullback.fst (V a).ι (V b).ι ≫ h a = pullback.snd (V a).ι (V b).ι ≫ h b := by
    intro a b
    let p : pullback (V a).ι (V b).ι ⟶ X' := pullback.fst (V a).ι (V b).ι ≫ (V a).ι
    have hp : pullback.snd (V a).ι (V b).ι ≫ (V b).ι = p := (pullback.condition).symm
    have hopen : IsOpenMap p := p.isOpenEmbedding.isOpenMap
    have hdom : IsDominant (pullback.fst (p ≫ π) j) := by
      refine ⟨?_⟩
      have hr := Scheme.Pullback.range_fst (p ≫ π) j
      have hden : Dense (p ⁻¹' (π ⁻¹' Set.range j)) := hd.preimage hopen
      have he : Set.range (pullback.fst (p ≫ π) j) = p ⁻¹' (π ⁻¹' Set.range j) := by
        rw [hr]
        ext x
        simp
      show Dense (Set.range (pullback.fst (p ≫ π) j))
      rw [he]
      exact hden
    have : AlgebraicGeometry.IsReduced (pullback (V a).ι (V b).ι) := isReduced_of_isOpenImmersion p
    refine ext_of_isDominant_of_isSeparated (terminal.from Y) (terminal.hom_ext _ _)
      (pullback.fst (p ≫ π) j) ?_
    have hqr : pullback.fst (p ≫ π) j ≫ p ≫ π = pullback.snd (p ≫ π) j ≫ j := pullback.condition
    have hA : pullback.fst (V a).ι (V b).ι ≫ (V a).ι ≫ π = p ≫ π := (Category.assoc _ _ _).symm
    have hB : pullback.snd (V a).ι (V b).ι ≫ (V b).ι ≫ π = p ≫ π := by rw [← Category.assoc, hp]
    have h₁ := hV a _ (pullback.fst (p ≫ π) j ≫ pullback.fst (V a).ι (V b).ι) (pullback.snd (p ≫ π) j)
      ((Category.assoc _ _ _).trans ((congrArg (pullback.fst (p ≫ π) j ≫ ·) hA).trans hqr))
    have h₂ := hV b _ (pullback.fst (p ≫ π) j ≫ pullback.snd (V a).ι (V b).ι) (pullback.snd (p ≫ π) j)
      ((Category.assoc _ _ _).trans ((congrArg (pullback.fst (p ≫ π) j ≫ ·) hB).trans hqr))
    exact (Category.assoc _ _ _).symm.trans (h₁.trans (h₂.symm.trans (Category.assoc _ _ _)))
  have hcov : IsOpenCover V :=
    eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxV x⟩
  let 𝒰 := X'.openCoverOfIsOpenCover V hcov
  obtain ⟨G, hι⟩ : ∃ G : X' ⟶ Y, ∀ x, (V x).ι ≫ G = h x :=
    ⟨𝒰.glueMorphisms h compat, fun x => 𝒰.ι_glueMorphisms h compat x⟩
  refine ⟨G, fun T a u hau => ?_⟩
  have hcovT : IsOpenCover (fun x => a ⁻¹ᵁ V x) :=
    eq_top_iff.2 fun t _ => TopologicalSpace.Opens.mem_iSup.2 ⟨a t, hxV (a t)⟩
  refine (T.openCoverOfIsOpenCover _ hcovT).hom_ext _ _ fun (x : X') => ?_
  show (a ⁻¹ᵁ V x).ι ≫ a ≫ G = (a ⁻¹ᵁ V x).ι ≫ u ≫ g
  have hr : (a ∣_ V x) ≫ (V x).ι = (a ⁻¹ᵁ V x).ι ≫ a := morphismRestrict_ι a (V x)
  have h₃ := hV x _ (a ∣_ V x) ((a ⁻¹ᵁ V x).ι ≫ u)
    (by rw [reassoc_of% hr, hau, Category.assoc])
  rw [← reassoc_of% hr, hι x, h₃, Category.assoc]

end GlobalTheory.TorRef
