import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsPullForm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechTripleRestrictCompositeInjectiveSecond
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.CechDR

/- English proof (translation)
Introduce `R _ X s J U hU`. Apply `restrict_bijective_one_of_basis s` to reduce the goal to its premises. Introduce `T`. Establish `hT : IsAffineOpen T.unop.1` using `T.unop.2`. Set `G : Set Γ(X, T.unop.1)` to `{f | ∃ j, X.basicOpen f ≤ U j}`.

Establish `hG : Ideal.span G = ⊤`. Rewrite using `[← hT.self_le_iSup_basicOpen_iff]`. Introduce `x hx`. Establish `hxU : x ∈ ⨆ i, U i` using `by rw [hU]; trivial`. Take `⟨j, hj⟩` from `TopologicalSpace.Opens.mem_iSup.1 hxU`.

Take `⟨f, hf, hxf⟩` from `hT.exists_basicOpen_le (V := U j) ⟨x, hj⟩ hx`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, ⟨j, hf⟩⟩, hxf⟩`. Take `⟨F, hFG, hF⟩` from `(Ideal.span_eq_top_iff_finite G).1 hG`. Use `⟨F.card, fun i ↦ (F.equivFin.symm i).1, ?_, ?_⟩` and prove the remaining obligations. Establish `hR : Set.range (fun i : Fin F.card ↦ (F.equivFin.symm i).1) = (F : Set Γ(X, T.unop.1))`.

Use extensionality with `f`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨i, rfl⟩`. Conclude with `(F.equivFin.symm i).2`. Introduce `hf; exact ⟨F.equivFin ⟨f, hf⟩, by simp⟩`.

Conclude with `hR ▸ hF`. Introduce `i S u hu`. Take `⟨j, hj⟩` from `hFG (F.equivFin.symm i).2`. Use `set f : Γ(X, T.unop.1) := (F.equivFin.symm i).1`. Establish `hW : IsAffineOpen (X.basicOpen f)` using `hT.basicOpen f`.

Establish `hWT : X.basicOpen f ≤ T.unop.1` using `X.basicOpen_le f`. Establish `hSW : S.unop.1 ≤ X.basicOpen f`. Establish `h1 : X.basicOpen (X.presheaf.map (homOfLE (leOfHom u.unop)).op f) = S.unop.1` using `X.basicOpen_of_isUnit hu`. Rewrite `h1` using `[Scheme.basicOpen_res]`. Rewrite using `[← h1]`.

Conclude with `inf_le_right`. Set `t : {V : X.affineOpens // ∃ i, V.1 ≤ U i}` to `⟨⟨_, hW⟩, j, hj⟩`. Use `⟨Opposite.op t, (homOfLE (show (⟨_, hW⟩ : X.affineOpens) ≤ T.unop from hWT)).op, (homOfLE (show S.unop ≤ (⟨_, hW⟩ : X.affineOpens) from hSW)).op, ?_⟩` and prove the remaining obligations. Conclude with `Quiver.Hom.unop_inj (Subsingleton.elim _ _)`. Introduce `t₁ t₂ S h₁ h₂`.

Use `⟨1, fun _ ↦ 1, ?_, fun _ S' u _ ↦ ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.span_eq_top_iff_finite]`. Conclude with `⟨{1}, by simp, by simp⟩`. Take `⟨j, hj⟩` from `t₁.unop.2`. Establish `hS'S : S'.unop ≤ S.unop` using `leOfHom u.unop`.

Establish `hS1 : S.unop ≤ t₁.unop.1` using `leOfHom h₁.unop`. Establish `hS2 : S.unop ≤ t₂.unop.1` using `leOfHom h₂.unop`. Set `t₃ : {V : X.affineOpens // ∃ i, V.1 ≤ U i}` to `⟨S'.unop, j, le_trans (hS'S.trans hS1) hj⟩`. Use `⟨Opposite.op t₃, ⟨(homOfLE (show t₃ ≤ t₁.unop from hS'S.trans hS1)).op⟩, ⟨(homOfLE (show t₃ ≤ t₂.unop from hS'S.trans hS2)).op⟩, ⟨𝟙 _⟩⟩` and prove the remaining obligations.
-/
theorem restrict_cover_affine_bijective : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (J : Type) (U : J → X.Opens), ⨆ i, U i = ⊤ → Function.Bijective (pullHyp1 (CoefMap.restrict (OAff s) (Monotone.functor (f := (Subtype.val : {V : X.affineOpens // ∃ i, V.1 ≤ U i} → X.affineOpens)) fun _ _ h ↦ h).op)) := by
  intro R _ X s J U hU
  apply restrict_bijective_one_of_basis s
  · intro T
    have hT : IsAffineOpen T.unop.1 := T.unop.2
    let G : Set Γ(X, T.unop.1) := {f | ∃ j, X.basicOpen f ≤ U j}
    have hG : Ideal.span G = ⊤ := by
      rw [← hT.self_le_iSup_basicOpen_iff]
      intro x hx
      have hxU : x ∈ ⨆ i, U i := by rw [hU]; trivial
      obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hxU
      obtain ⟨f, hf, hxf⟩ := hT.exists_basicOpen_le (V := U j) ⟨x, hj⟩ hx
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, ⟨j, hf⟩⟩, hxf⟩
    obtain ⟨F, hFG, hF⟩ := (Ideal.span_eq_top_iff_finite G).1 hG
    refine ⟨F.card, fun i ↦ (F.equivFin.symm i).1, ?_, ?_⟩
    · have hR : Set.range (fun i : Fin F.card ↦ (F.equivFin.symm i).1) = (F : Set Γ(X, T.unop.1)) := by
        ext f
        constructor
        · rintro ⟨i, rfl⟩; exact (F.equivFin.symm i).2
        · intro hf; exact ⟨F.equivFin ⟨f, hf⟩, by simp⟩
      exact hR ▸ hF
    · intro i S u hu
      obtain ⟨j, hj⟩ := hFG (F.equivFin.symm i).2
      set f : Γ(X, T.unop.1) := (F.equivFin.symm i).1
      have hW : IsAffineOpen (X.basicOpen f) := hT.basicOpen f
      have hWT : X.basicOpen f ≤ T.unop.1 := X.basicOpen_le f
      have hSW : S.unop.1 ≤ X.basicOpen f := by
        have h1 : X.basicOpen (X.presheaf.map (homOfLE (leOfHom u.unop)).op f) = S.unop.1 :=
          X.basicOpen_of_isUnit hu
        rw [Scheme.basicOpen_res] at h1
        rw [← h1]; exact inf_le_right
      let t : {V : X.affineOpens // ∃ i, V.1 ≤ U i} := ⟨⟨_, hW⟩, j, hj⟩
      refine ⟨Opposite.op t, (homOfLE (show (⟨_, hW⟩ : X.affineOpens) ≤ T.unop from hWT)).op,
        (homOfLE (show S.unop ≤ (⟨_, hW⟩ : X.affineOpens) from hSW)).op, ?_⟩
      exact Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  · intro t₁ t₂ S h₁ h₂
    refine ⟨1, fun _ ↦ 1, ?_, fun _ S' u _ ↦ ?_⟩
    · rw [Ideal.span_eq_top_iff_finite]
      exact ⟨{1}, by simp, by simp⟩
    · obtain ⟨j, hj⟩ := t₁.unop.2
      have hS'S : S'.unop ≤ S.unop := leOfHom u.unop
      have hS1 : S.unop ≤ t₁.unop.1 := leOfHom h₁.unop
      have hS2 : S.unop ≤ t₂.unop.1 := leOfHom h₂.unop
      let t₃ : {V : X.affineOpens // ∃ i, V.1 ≤ U i} := ⟨S'.unop, j, le_trans (hS'S.trans hS1) hj⟩
      refine ⟨Opposite.op t₃, ⟨(homOfLE (show t₃ ≤ t₁.unop from hS'S.trans hS1)).op⟩,
        ⟨(homOfLE (show t₃ ≤ t₂.unop from hS'S.trans hS2)).op⟩, ⟨𝟙 _⟩⟩

end GlobalTheory.CechDR
