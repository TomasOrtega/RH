import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineHomOfIsPullback
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

/- English proof (translation)
Establish `hcov : ∀ T : AffOp X, ∃ (n : ℕ) (b : Fin n → (OAff s).obj T), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : AffOp X) (u : T ⟶ S), IsUnit (mp (OAff s) u (b i)) → ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u`. Introduce `T`. Establish `hT : IsAffineOpen T.unop.1` using `T.unop.2`. Set `B : Set Γ(X, T.unop.1)` to `{f | ∃ t : C', X.basicOpen f ≤ (G.obj t).unop.1 ∧ (G.obj t).unop.1 ≤ T.unop.1}`. Establish `hB : Ideal.span B = ⊤`.

Rewrite using `[← hT.self_le_iSup_basicOpen_iff]`. Introduce `x hx`. Take `⟨t, hxt, htT⟩` from `h1 x T.unop.1 hx`. Take `⟨f, hf, hxf⟩` from `hT.exists_basicOpen_le (V := (G.obj t).unop.1) ⟨x, hxt⟩ hx`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, ⟨t, hf, htT⟩⟩, hxf⟩`.

Take `⟨F, hFB, hF⟩` from `(Ideal.span_eq_top_iff_finite B).1 hB`. Use `⟨F.card, fun i ↦ (F.equivFin.symm i).1, ?_, ?_⟩` and prove the remaining obligations. Establish `hsp : Ideal.span (Set.range fun i ↦ ((F.equivFin.symm i).1 : Γ(X, T.unop.1))) = ⊤`. Rewrite using `[eq_top_iff, ← hF]`. Conclude with `Ideal.span_mono fun x hx ↦ ⟨F.equivFin ⟨x, hx⟩, by simp⟩`.

Conclude with `hsp`. Introduce `i S u hu`. Take `⟨t, hft, htT⟩` from `hFB (F.equivFin.symm i).2`. Use `set f : Γ(X, T.unop.1) := (F.equivFin.symm i).1`. Express the relevant statement in the definitionally equal form `IsUnit (X.presheaf.map (homOfLE (show S.unop.1 ≤ T.unop.1 from leOfHom u.unop)).op f) at hu`.

Establish `hSf : S.unop.1 ≤ X.basicOpen f`. Use `Scheme.basicOpen_of_isUnit X hu` as an intermediate fact. Rewrite `this` using `[Scheme.basicOpen_res]`. Rewrite using `[← this]`. Conclude with `inf_le_right`.

Use `⟨t, (homOfLE (show (G.obj t).unop ≤ T.unop from htT)).op, (homOfLE (show S.unop ≤ (G.obj t).unop from hSf.trans hft)).op, ?_⟩` and prove the remaining obligations. Conclude with `Quiver.Hom.unop_inj (Subsingleton.elim _ _)`. Establish `hdir : ∀ (t₁ t₂ : C') (S : AffOp X), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → (OAff s).obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : AffOp X) (u : S ⟶ S'), IsUnit (mp (OAff s) u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj …`. Introduce `t₁ t₂ S a₁ a₂`. Establish `hS : IsAffineOpen S.unop.1` using `S.unop.2`.

Establish `hS₁ : S.unop.1 ≤ (G.obj t₁).unop.1` using `leOfHom a₁.unop`. Establish `hS₂ : S.unop.1 ≤ (G.obj t₂).unop.1` using `leOfHom a₂.unop`. Set `B : Set Γ(X, S.unop.1)` to `{g | ∃ t₃ : C', Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ X.basicOpen g ≤ (G.obj t₃).unop.1}`. Establish `hB : Ideal.span B = ⊤`. Rewrite using `[← hS.self_le_iSup_basicOpen_iff]`.

Introduce `x hx`. Take `⟨t₃, e₁, e₂, hxt, -⟩` from `h2 t₁ t₂ x S.unop.1 hx (hS₁ hx) (hS₂ hx)`. Take `⟨g, hg, hxg⟩` from `hS.exists_basicOpen_le (V := (G.obj t₃).unop.1) ⟨x, hxt⟩ hx`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨⟨g, ⟨t₃, e₁, e₂, hg⟩⟩, hxg⟩`. Take `⟨F, hFB, hF⟩` from `(Ideal.span_eq_top_iff_finite B).1 hB`.

Use `⟨F.card, fun i ↦ (F.equivFin.symm i).1, ?_, ?_⟩` and prove the remaining obligations. Establish `hsp : Ideal.span (Set.range fun i ↦ ((F.equivFin.symm i).1 : Γ(X, S.unop.1))) = ⊤`. Rewrite using `[eq_top_iff, ← hF]`. Conclude with `Ideal.span_mono fun x hx ↦ ⟨F.equivFin ⟨x, hx⟩, by simp⟩`. Conclude with `hsp`.

Introduce `i S' u hu`. Take `⟨t₃, e₁, e₂, hgt⟩` from `hFB (F.equivFin.symm i).2`. Use `set g : Γ(X, S.unop.1) := (F.equivFin.symm i).1`. Express the relevant statement in the definitionally equal form `IsUnit (X.presheaf.map (homOfLE (show S'.unop.1 ≤ S.unop.1 from leOfHom u.unop)).op g) at hu`. Establish `hS'g : S'.unop.1 ≤ X.basicOpen g`.

Use `Scheme.basicOpen_of_isUnit X hu` as an intermediate fact. Rewrite `this` using `[Scheme.basicOpen_res]`. Rewrite using `[← this]`. Conclude with `inf_le_right`. Conclude with `⟨t₃, e₁, e₂, ⟨(homOfLE (show S'.unop ≤ (G.obj t₃).unop from hS'g.trans hgt)).op⟩⟩`.

Establish `H` using `_root_.GlobalTheory.CechDR.hasLoc_OAff s`. Establish `hs` using `_root_.GlobalTheory.sep_of_factoring_cover (OAff s) G H hcov`. Establish `hg` using `_root_.GlobalTheory.CatCoh.Desc.glue_comma_of_basis (OAff s) G H hcov hdir`. Establish `hv` using `_root_.GlobalTheory.CatCoh.Desc.Basis.oneCocycle_vanishing_comma_of_basis (OAff s) G H hcov hdir`. Establish `hv2` using `GlobalTheory.T.twoCocycle_coboundary_of_basisFunctor (OAff s) G H hcov hdir`.

Conclude with `⟨GlobalTheory.T.comma_descent_injective _ _ hs hg hv, GlobalTheory.T.comma_descent_restriction_equiv _ _ hs hg hv hv2⟩`.
-/
theorem restrict_pull2_bijective_of_basis (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R)
    (C' : Type) [Category.{0} C'] [Quiver.IsThin C'] (G : C' ⥤ AffOp X)
    (h1 : ∀ (x : X) (U : X.Opens), x ∈ U → ∃ t : C', x ∈ (G.obj t).unop.1 ∧ (G.obj t).unop.1 ≤ U)
    (h2 : ∀ (t₁ t₂ : C') (x : X) (U : X.Opens), x ∈ U → x ∈ (G.obj t₁).unop.1 →
      x ∈ (G.obj t₂).unop.1 → ∃ t₃ : C', Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧
        x ∈ (G.obj t₃).unop.1 ∧ (G.obj t₃).unop.1 ≤ U) :
    Function.Bijective (CoefMap.restrict (OAff s) G).pull2 := by
  have hcov : ∀ T : AffOp X, ∃ (n : ℕ) (b : Fin n → (OAff s).obj T),
      Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : AffOp X) (u : T ⟶ S),
        IsUnit (mp (OAff s) u (b i)) →
          ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u := by
    intro T
    have hT : IsAffineOpen T.unop.1 := T.unop.2
    let B : Set Γ(X, T.unop.1) :=
      {f | ∃ t : C', X.basicOpen f ≤ (G.obj t).unop.1 ∧ (G.obj t).unop.1 ≤ T.unop.1}
    have hB : Ideal.span B = ⊤ := by
      rw [← hT.self_le_iSup_basicOpen_iff]
      intro x hx
      obtain ⟨t, hxt, htT⟩ := h1 x T.unop.1 hx
      obtain ⟨f, hf, hxf⟩ := hT.exists_basicOpen_le (V := (G.obj t).unop.1) ⟨x, hxt⟩ hx
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, ⟨t, hf, htT⟩⟩, hxf⟩
    obtain ⟨F, hFB, hF⟩ := (Ideal.span_eq_top_iff_finite B).1 hB
    refine ⟨F.card, fun i ↦ (F.equivFin.symm i).1, ?_, ?_⟩
    · have hsp : Ideal.span (Set.range fun i ↦ ((F.equivFin.symm i).1 : Γ(X, T.unop.1))) = ⊤ := by
        rw [eq_top_iff, ← hF]
        exact Ideal.span_mono fun x hx ↦ ⟨F.equivFin ⟨x, hx⟩, by simp⟩
      exact hsp
    · intro i S u hu
      obtain ⟨t, hft, htT⟩ := hFB (F.equivFin.symm i).2
      set f : Γ(X, T.unop.1) := (F.equivFin.symm i).1
      change IsUnit (X.presheaf.map (homOfLE (show S.unop.1 ≤ T.unop.1 from leOfHom u.unop)).op f) at hu
      have hSf : S.unop.1 ≤ X.basicOpen f := by
        have := Scheme.basicOpen_of_isUnit X hu
        rw [Scheme.basicOpen_res] at this
        rw [← this]; exact inf_le_right
      refine ⟨t, (homOfLE (show (G.obj t).unop ≤ T.unop from htT)).op,
        (homOfLE (show S.unop ≤ (G.obj t).unop from hSf.trans hft)).op, ?_⟩
      exact Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  have hdir : ∀ (t₁ t₂ : C') (S : AffOp X), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) →
      ∃ (n : ℕ) (b : Fin n → (OAff s).obj S), Ideal.span (Set.range b) = ⊤ ∧
        ∀ (i : Fin n) (S' : AffOp X) (u : S ⟶ S'), IsUnit (mp (OAff s) u (b i)) →
          ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S') := by
    intro t₁ t₂ S a₁ a₂
    have hS : IsAffineOpen S.unop.1 := S.unop.2
    have hS₁ : S.unop.1 ≤ (G.obj t₁).unop.1 := leOfHom a₁.unop
    have hS₂ : S.unop.1 ≤ (G.obj t₂).unop.1 := leOfHom a₂.unop
    let B : Set Γ(X, S.unop.1) :=
      {g | ∃ t₃ : C', Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ X.basicOpen g ≤ (G.obj t₃).unop.1}
    have hB : Ideal.span B = ⊤ := by
      rw [← hS.self_le_iSup_basicOpen_iff]
      intro x hx
      obtain ⟨t₃, e₁, e₂, hxt, -⟩ := h2 t₁ t₂ x S.unop.1 hx (hS₁ hx) (hS₂ hx)
      obtain ⟨g, hg, hxg⟩ := hS.exists_basicOpen_le (V := (G.obj t₃).unop.1) ⟨x, hxt⟩ hx
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨g, ⟨t₃, e₁, e₂, hg⟩⟩, hxg⟩
    obtain ⟨F, hFB, hF⟩ := (Ideal.span_eq_top_iff_finite B).1 hB
    refine ⟨F.card, fun i ↦ (F.equivFin.symm i).1, ?_, ?_⟩
    · have hsp : Ideal.span (Set.range fun i ↦ ((F.equivFin.symm i).1 : Γ(X, S.unop.1))) = ⊤ := by
        rw [eq_top_iff, ← hF]
        exact Ideal.span_mono fun x hx ↦ ⟨F.equivFin ⟨x, hx⟩, by simp⟩
      exact hsp
    · intro i S' u hu
      obtain ⟨t₃, e₁, e₂, hgt⟩ := hFB (F.equivFin.symm i).2
      set g : Γ(X, S.unop.1) := (F.equivFin.symm i).1
      change IsUnit (X.presheaf.map (homOfLE (show S'.unop.1 ≤ S.unop.1 from leOfHom u.unop)).op g) at hu
      have hS'g : S'.unop.1 ≤ X.basicOpen g := by
        have := Scheme.basicOpen_of_isUnit X hu
        rw [Scheme.basicOpen_res] at this
        rw [← this]; exact inf_le_right
      exact ⟨t₃, e₁, e₂, ⟨(homOfLE (show S'.unop ≤ (G.obj t₃).unop from hS'g.trans hgt)).op⟩⟩
  have H := _root_.GlobalTheory.CechDR.hasLoc_OAff s
  have hs := _root_.GlobalTheory.sep_of_factoring_cover (OAff s) G H hcov
  have hg := _root_.GlobalTheory.CatCoh.Desc.glue_comma_of_basis (OAff s) G H hcov hdir
  have hv := _root_.GlobalTheory.CatCoh.Desc.Basis.oneCocycle_vanishing_comma_of_basis (OAff s) G H hcov hdir
  have hv2 := GlobalTheory.T.twoCocycle_coboundary_of_basisFunctor (OAff s) G H hcov hdir
  exact ⟨GlobalTheory.T.comma_descent_injective _ _ hs hg hv, GlobalTheory.T.comma_descent_restriction_equiv _ _ hs hg hv hv2⟩

end GlobalTheory.AbCoh
