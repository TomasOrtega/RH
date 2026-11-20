import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegUnif
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.TorusInj

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Semi.LBVal

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(X.presheaf.map (homOfLE h1).op ≫ X.presheaf.map (homOfLE h2).op).hom x = _`. Rewrite using `[← Functor.map_comp]`. Apply the tactic sequence `all_goals rfl`.
-/
lemma rres {X : Scheme.{0}} {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (x : Γ(X, U)) :
    (X.presheaf.map (homOfLE h2).op).hom ((X.presheaf.map (homOfLE h1).op).hom x) =
      (X.presheaf.map (homOfLE (h2.trans h1)).op).hom x := by
  change (X.presheaf.map (homOfLE h1).op ≫ X.presheaf.map (homOfLE h2).op).hom x = _
  rw [← Functor.map_comp]
  all_goals rfl

variable {X Y Z : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K']

/- English proof (translation)
Introduce `_ hy` and use `Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k`.
-/
lemma wchart_pull_le (φ : K → (Y ⟶ X)) (h : Z ⟶ Y) (j : K → L.ι) :
    LB.wchart L (fun k => h ≫ φ k) j ≤ h ⁻¹ᵁ LB.wchart L φ j := fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k

/- English proof (translation)
Conclude with `rres (wchart_pull_le L φ h j) hW ((h.app (LB.wchart L φ j)).hom (c.s j).val)`.
-/
lemma pullGen_val (φ : K → (Y ⟶ X)) (ε : K → ℤ) (c : LB.Gen (LB.LinComb L φ ε)) (h : Z ⟶ Y)
    (j : K → L.ι) (W : Z.Opens) (hW : W ≤ LB.wchart L (fun k => h ≫ φ k) j) :
    (Z.presheaf.map (homOfLE hW).op).hom ((LB.pullGen L φ ε c h).s j).val =
      (h.appLE (LB.wchart L φ j) W (hW.trans (wchart_pull_le L φ h j))).hom (c.s j).val := by
  exact rres (wchart_pull_le L φ h j) hW ((h.app (LB.wchart L φ j)).hom (c.s j).val)

/- English proof (translation)
Establish `ha : LB.wchart L (Sum.elim φ φ') j ≤ LB.wchart L φ (j ∘ Sum.inl)` using `fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inl k)`. Establish `hb : LB.wchart L (Sum.elim φ φ') j ≤ LB.wchart L φ' (j ∘ Sum.inr)` using `fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inr k)`. Express the relevant statement in the definitionally equal form `(Y.presheaf.map (homOfLE hW).op).hom ((Y.presheaf.map (homOfLE ha).op).hom (t.s (j ∘ Sum.inl)).val * (Y.presheaf.map (homOfLE hb).op).hom (t'.s (j ∘ Sum.inr)).val) = _`. Rewrite using `[map_mul]`. Conclude with `congrArg₂ (· * ·) (rres ha hW _) (rres hb hW _)`.
-/
lemma mulGen_val (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε')) (j : K ⊕ K' → L.ι)
    (W : Y.Opens) (hW : W ≤ LB.wchart L (Sum.elim φ φ') j) :
    (Y.presheaf.map (homOfLE hW).op).hom ((LB.mulGen L φ ε φ' ε' t t').s j).val =
      (Y.presheaf.map (homOfLE (hW.trans (fun _ hy => Set.mem_iInter.2 fun k =>
          Set.mem_iInter.1 hy (Sum.inl k)))).op).hom (t.s (j ∘ Sum.inl)).val *
      (Y.presheaf.map (homOfLE (hW.trans (fun _ hy => Set.mem_iInter.2 fun k =>
          Set.mem_iInter.1 hy (Sum.inr k)))).op).hom (t'.s (j ∘ Sum.inr)).val := by
  have ha : LB.wchart L (Sum.elim φ φ') j ≤ LB.wchart L φ (j ∘ Sum.inl) :=
    fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inl k)
  have hb : LB.wchart L (Sum.elim φ φ') j ≤ LB.wchart L φ' (j ∘ Sum.inr) :=
    fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inr k)
  change (Y.presheaf.map (homOfLE hW).op).hom
      ((Y.presheaf.map (homOfLE ha).op).hom (t.s (j ∘ Sum.inl)).val *
        (Y.presheaf.map (homOfLE hb).op).hom (t'.s (j ∘ Sum.inr)).val) = _
  rw [map_mul]
  exact congrArg₂ (· * ·) (rres ha hW _) (rres hb hW _)

/- English proof (translation)
Establish `e` using `congrArg (fun u : Γ(Y, LB.wchart L φ j ⊓ LB.wchart L φ' j')ˣ => (Y.presheaf.map (homOfLE hW).op).hom u.val) (hc j j' c1 c2 c3)`. Conclude with `(rres inf_le_left hW _).symm.trans (e.trans (rres inf_le_right hW _))`.
-/
lemma corr_val (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε'))
    (hc : LB.Gen.Corr L φ ε φ' ε' t t') (j : K → L.ι) (j' : K' → L.ι) (c1 : LB.Coh L φ j)
    (c2 : LB.Coh L φ' j') (c3 : ∀ k k', φ k = φ' k' → j k = j' k') (W : Y.Opens)
    (hW : W ≤ LB.wchart L φ j ⊓ LB.wchart L φ' j') :
    (Y.presheaf.map (homOfLE (hW.trans inf_le_left)).op).hom (t.s j).val =
      (Y.presheaf.map (homOfLE (hW.trans inf_le_right)).op).hom (t'.s j').val := by
  have e := congrArg (fun u : Γ(Y, LB.wchart L φ j ⊓ LB.wchart L φ' j')ˣ =>
    (Y.presheaf.map (homOfLE hW).op).hom u.val) (hc j j' c1 c2 c3)
  exact (rres inf_le_left hW _).symm.trans (e.trans (rres inf_le_right hW _))

end ReciprocityTheory.ChartRestriction.G.Semi.LBVal

namespace ReciprocityTheory.ChartRestriction.G.Out.LBVal

open Semi

/- English proof (translation)
Establish `p : LB.wchart L (Y` using `(splitTorus S X ⊗ G).left) (K := PEmpty) PEmpty.elim j ≤ (fst (splitTorus S X) G).left ⁻¹ᵁ ⊤ := fun _ _ => trivial`. Use `(Semi.LBVal.rres p hW _).trans ?_` and prove the remaining obligations. Apply the tactic sequence `all_goals rfl`.
-/
lemma charGen_val {S : Scheme.{0}} (X : Type) [AddCommGroup X] (G : Over S) {Z : Scheme.{0}}
    (L : LB Z) (χ : X) (j : PEmpty → L.ι) (W : (splitTorus S X ⊗ G).left.Opens)
    (hW : W ≤ LB.wchart L (Y := (splitTorus S X ⊗ G).left) (K := PEmpty) PEmpty.elim j) :
    ((splitTorus S X ⊗ G).left.presheaf.map (homOfLE hW).op).hom ((charGen X G L χ).s j).val =
      ((splitTorus S X ⊗ G).left.presheaf.map (homOfLE le_top).op).hom
        (Semi.TorusInj.chiP X G χ) := by
  have p : LB.wchart L (Y := (splitTorus S X ⊗ G).left) (K := PEmpty) PEmpty.elim j ≤
      (fst (splitTorus S X) G).left ⁻¹ᵁ ⊤ := fun _ _ => trivial
  refine (Semi.LBVal.rres p hW _).trans ?_
  all_goals rfl

end ReciprocityTheory.ChartRestriction.G.Out.LBVal
