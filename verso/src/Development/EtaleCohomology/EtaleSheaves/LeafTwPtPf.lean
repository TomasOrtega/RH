import Development.EtaleCohomology.EtaleSheaves.LeafTwSecKillCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.E8.TwSec

/- English proof (translation)
Rewrite using `[op_comp, Functor.map_comp, Functor.map_comp]`. Both sides reduce to the same expression.
-/
theorem twF_res_comp {q : ℕ} (j : ℤ) {X Y Z : Scheme.{0}} (a : X ⟶ Y) (b : Y ⟶ Z) (x : (twF q j).obj Γ(Z, ⊤)) :
    ((twF q j).map (Scheme.Γ.map (a ≫ b).op)).hom x =
      ((twF q j).map (Scheme.Γ.map a.op)).hom (((twF q j).map (Scheme.Γ.map b.op)).hom x) := by
  rw [op_comp, Functor.map_comp, Functor.map_comp]; rfl

/- English proof (translation)
Rewrite using `[map_smul]`. Use `congr 1`. Unfold `twCls`. Express the relevant statement in the definitionally equal form `Submodule.mapQ _ _ _ (twRel_le q j f.hom) _ = _`. Rewrite using `[Submodule.mapQ_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]`.
-/
theorem twF_map_cls {q : ℕ} (j : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B) (ζ : Prim q A) (c : ZMod q) :
    ((twF q j).map f).hom (ULift.up c • twCls j ζ) = ULift.up c • twCls j (ζ.map f.hom) := by
  rw [map_smul]
  congr 1
  unfold twCls
  change Submodule.mapQ _ _ _ (twRel_le q j f.hom) _ = _
  rw [Submodule.mapQ_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

/- English proof (translation)
Use `haveI : IsEmpty (Prim q A) := ⟨fun ζ => hq ζ.2.1⟩`. Take `⟨f, rfl⟩` from `Submodule.Quotient.mk_surjective _ t`. Rewrite using `[Subsingleton.elim f 0]`. Conclude with `Submodule.Quotient.mk_zero _`.
-/
theorem twF_eq_zero_of_not_unit {q : ℕ} (j : ℤ) {A : CommRingCat.{0}} (hq : ¬ IsUnit (q : A)) (t : (twF q j).obj A) :
    t = 0 := by
  haveI : IsEmpty (Prim q A) := ⟨fun ζ => hq ζ.2.1⟩
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ t
  rw [Subsingleton.elim f 0]
  exact Submodule.Quotient.mk_zero _

/- English proof (translation)
Introduce `q _ j U u t V g v hgv ht`. Distinguish the cases in `hq : IsUnit (q : Γ(U, ⊤))`. Use `swap`. Use `⟨U, 𝟙 U, inferInstance, ⟨u, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[twF_eq_zero_of_not_unit j hq t]`.

Conclude with `map_zero _`. Take `⟨W₁, w₁, hw₁, ⟨w, hw⟩, ⟨ζ⟩⟩` from `hA q U u hq`. Use `haveI := hw₁`. Take `⟨O, c, hwO, hO⟩` from `hG q j W₁ ζ (((twF q j).map (Scheme.Γ.map w₁.op)).hom t) w`. Establish `hO' : ((twF q j).map (Scheme.Γ.map (O.ι ≫ w₁).op)).hom t = ULift.up c • twCls j (ζ.map (Scheme.Γ.map O.ι.op).hom)`.

Rewrite using `[twF_res_comp, hO]`. Conclude with `twF_map_cls j _ ζ c`. Take `⟨p, hp1, hp2⟩` from `Scheme.Pullback.exists_preimage_pullback (f := O.ι ≫ w₁) (g := g) (⟨w, hwO⟩ : O.toScheme) v (by rw [hgv]; exact hw)`. Establish `hc : c = 0`. Set `P` to `pullback (O.ι ≫ w₁) g`.

Set `φ` to `P.evaluation ⊤ p trivial`. Establish `e : ((twF q j).map (Scheme.Γ.map (pullback.fst (O.ι ≫ w₁) g ≫ O.ι ≫ w₁).op)).hom t = 0`. Rewrite using `[pullback.condition, twF_res_comp, ht, map_zero]`. Rewrite `e` using `[twF_res_comp, hO', twF_map_cls]`. Establish `key` using `twF_map_cls j φ (Prim.map (Scheme.Γ.map (pullback.fst (O.ι ≫ w₁) g).op).hom (Prim.map (Scheme.Γ.map O.ι.op).hom ζ)) c`.

Conclude with `hF q j (P.residueField p) (Field.toIsField _) _ c (key.symm.trans ((congrArg (fun x => ((twF q j).map φ).hom x) e).trans (map_zero _)))`. Use `⟨O, O.ι ≫ w₁, inferInstance, ⟨⟨w, hwO⟩, hw⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hO', hc]`. Conclude with `zero_smul (ULift (ZMod q)) _`.
-/
theorem LeafTwPt_of (hA : LeafTwAdj) (hG : LeafTwGen) (hF : LeafTwFieldZ) : LeafTwPt := by
  intro q _ j U u t V g v hgv ht
  by_cases hq : IsUnit (q : Γ(U, ⊤))
  swap
  · refine ⟨U, 𝟙 U, inferInstance, ⟨u, rfl⟩, ?_⟩
    rw [twF_eq_zero_of_not_unit j hq t]; exact map_zero _
  obtain ⟨W₁, w₁, hw₁, ⟨w, hw⟩, ⟨ζ⟩⟩ := hA q U u hq
  haveI := hw₁
  obtain ⟨O, c, hwO, hO⟩ := hG q j W₁ ζ (((twF q j).map (Scheme.Γ.map w₁.op)).hom t) w
  have hO' : ((twF q j).map (Scheme.Γ.map (O.ι ≫ w₁).op)).hom t =
      ULift.up c • twCls j (ζ.map (Scheme.Γ.map O.ι.op).hom) := by
    rw [twF_res_comp, hO]; exact twF_map_cls j _ ζ c
  obtain ⟨p, hp1, hp2⟩ := Scheme.Pullback.exists_preimage_pullback (f := O.ι ≫ w₁) (g := g)
    (⟨w, hwO⟩ : O.toScheme) v (by rw [hgv]; exact hw)
  have hc : c = 0 := by
    let P := pullback (O.ι ≫ w₁) g
    let φ := P.evaluation ⊤ p trivial
    have e : ((twF q j).map (Scheme.Γ.map (pullback.fst (O.ι ≫ w₁) g ≫ O.ι ≫ w₁).op)).hom t = 0 := by
      rw [pullback.condition, twF_res_comp, ht, map_zero]
    rw [twF_res_comp, hO', twF_map_cls] at e
    have key := twF_map_cls j φ (Prim.map (Scheme.Γ.map (pullback.fst (O.ι ≫ w₁) g).op).hom
      (Prim.map (Scheme.Γ.map O.ι.op).hom ζ)) c
    exact hF q j (P.residueField p) (Field.toIsField _) _ c
      (key.symm.trans ((congrArg (fun x => ((twF q j).map φ).hom x) e).trans (map_zero _)))
  refine ⟨O, O.ι ≫ w₁, inferInstance, ⟨⟨w, hwO⟩, hw⟩, ?_⟩
  rw [hO', hc]
  exact zero_smul (ULift (ZMod q)) _

end LateralTheory.E.E8.TwSec
