import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR

namespace GlobalTheory.CechDR

/- English proof (translation)
Introduce `T`. Establish `hT : IsAffineOpen T.unop.1` using `T.unop.2`. Set `G : Set Γ(X', T.unop.1)` to `{f | ∃ V : X.affineOpens, X'.basicOpen f ≤ φ ⁻¹ᵁ V.1}`. Establish `hG : Ideal.span G = ⊤`. Rewrite using `[← hT.self_le_iSup_basicOpen_iff]`.

Introduce `x hx`. Take `⟨_, ⟨V, hV, rfl⟩, hxV, -⟩` from `X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (φ x)) isOpen_univ`. Take `⟨f, hf, hxf⟩` from `hT.exists_basicOpen_le (V := φ ⁻¹ᵁ V) ⟨x, hxV⟩ hx`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, ⟨⟨V, hV⟩, hf⟩⟩, hxf⟩`. Take `⟨F, hFG, hF⟩` from `(Ideal.span_eq_top_iff_finite G).1 hG`.

Use `⟨F.card, fun i ↦ (F.equivFin.symm i).1, ?_, ?_⟩` and prove the remaining obligations. Establish `hR : Set.range (fun i : Fin F.card ↦ (F.equivFin.symm i).1) = (F : Set Γ(X', T.unop.1))`. Use extensionality with `f`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨i, rfl⟩`.

Conclude with `(F.equivFin.symm i).2`. Introduce `hf; exact ⟨F.equivFin ⟨f, hf⟩, by simp⟩`. Conclude with `hR ▸ hF`. Introduce `i S u hu`. Take `⟨V, hV⟩` from `hFG (F.equivFin.symm i).2`.

Use `set f : Γ(X', T.unop.1) := (F.equivFin.symm i).1`. Establish `hW : IsAffineOpen (X'.basicOpen f)` using `hT.basicOpen f`. Establish `hWT : X'.basicOpen f ≤ T.unop.1` using `X'.basicOpen_le f`. Set `t : Pair φ` to `⟨(⟨_, hW⟩, V), hV⟩`. Establish `hSW : S.unop.1 ≤ X'.basicOpen f`.

Establish `h1 : X'.basicOpen (X'.presheaf.map (homOfLE (leOfHom u.unop)).op f) = S.unop.1` using `X'.basicOpen_of_isUnit hu`. Rewrite `h1` using `[Scheme.basicOpen_res]`. Rewrite using `[← h1]`. Conclude with `inf_le_right`. Use `⟨Opposite.op t, (homOfLE (show (⟨_, hW⟩ : X'.affineOpens) ≤ T.unop from hWT)).op, (homOfLE (show S.unop ≤ (⟨_, hW⟩ : X'.affineOpens) from hSW)).op, ?_⟩` and prove the remaining obligations.

Conclude with `Quiver.Hom.unop_inj (Subsingleton.elim _ _)`.
-/
theorem pair_cover_affine {R' : Type} [CommRing R'] {X X' : Scheme.{0}} (φ : X' ⟶ X)
    (s' : X' ⟶ Sp R') : ∀ T : AffOp X', ∃ (n : ℕ) (b : Fin n → (OAff s').obj T),
      Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : AffOp X') (u : T ⟶ S),
        IsUnit (mp (OAff s') u (b i)) →
          ∃ (t : (Pair φ)ᵒᵖ) (v : T ⟶ (pairFst φ).obj t) (w : (pairFst φ).obj t ⟶ S), v ≫ w = u := by
  intro T
  have hT : IsAffineOpen T.unop.1 := T.unop.2
  let G : Set Γ(X', T.unop.1) :=
    {f | ∃ V : X.affineOpens, X'.basicOpen f ≤ φ ⁻¹ᵁ V.1}
  have hG : Ideal.span G = ⊤ := by
    rw [← hT.self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (φ x)) isOpen_univ
    obtain ⟨f, hf, hxf⟩ := hT.exists_basicOpen_le (V := φ ⁻¹ᵁ V) ⟨x, hxV⟩ hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, ⟨⟨V, hV⟩, hf⟩⟩, hxf⟩
  obtain ⟨F, hFG, hF⟩ := (Ideal.span_eq_top_iff_finite G).1 hG
  refine ⟨F.card, fun i ↦ (F.equivFin.symm i).1, ?_, ?_⟩
  · have hR : Set.range (fun i : Fin F.card ↦ (F.equivFin.symm i).1) = (F : Set Γ(X', T.unop.1)) := by
      ext f
      constructor
      · rintro ⟨i, rfl⟩; exact (F.equivFin.symm i).2
      · intro hf; exact ⟨F.equivFin ⟨f, hf⟩, by simp⟩
    exact hR ▸ hF
  · intro i S u hu
    obtain ⟨V, hV⟩ := hFG (F.equivFin.symm i).2
    set f : Γ(X', T.unop.1) := (F.equivFin.symm i).1
    have hW : IsAffineOpen (X'.basicOpen f) := hT.basicOpen f
    have hWT : X'.basicOpen f ≤ T.unop.1 := X'.basicOpen_le f
    let t : Pair φ := ⟨(⟨_, hW⟩, V), hV⟩
    have hSW : S.unop.1 ≤ X'.basicOpen f := by
      have h1 : X'.basicOpen (X'.presheaf.map (homOfLE (leOfHom u.unop)).op f) = S.unop.1 :=
        X'.basicOpen_of_isUnit hu
      rw [Scheme.basicOpen_res] at h1
      rw [← h1]; exact inf_le_right
    refine ⟨Opposite.op t, (homOfLE (show (⟨_, hW⟩ : X'.affineOpens) ≤ T.unop from hWT)).op,
      (homOfLE (show S.unop ≤ (⟨_, hW⟩ : X'.affineOpens) from hSW)).op, ?_⟩
    exact Quiver.Hom.unop_inj (Subsingleton.elim _ _)

end GlobalTheory.CechDR
