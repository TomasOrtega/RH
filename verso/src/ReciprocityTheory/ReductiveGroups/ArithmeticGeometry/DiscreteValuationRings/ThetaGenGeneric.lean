import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGenDiv
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.AppCompatGeneric

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.TG

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

def pullSec' {X Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (s : LB.Sec (LB.LinComb L φ ε)) (h : Z ⟶ Y) (φ' : K → (Z ⟶ X)) (hφ : ∀ k, φ' k = h ≫ φ k) :
    LB.Sec (LB.LinComb L φ' ε) := by
  have e : φ' = fun k => h ≫ φ k := funext hφ
  subst e
  exact pullSec L φ ε s h

/- English proof (translation)
Take `rfl : φ' = fun k => h ≫ φ k` from `funext hφ`. Both sides reduce to the same expression.
-/
lemma pullSec'_f {X Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (s : LB.Sec (LB.LinComb L φ ε)) (h : Z ⟶ Y) (φ' : K → (Z ⟶ X)) (hφ : ∀ k, φ' k = h ≫ φ k)
    (j : K → L.ι) :
    (pullSec' L φ ε s h φ' hφ).f j =
      (Z.presheaf.map (homOfLE (wchart_le_preimage L h φ φ' hφ j)).op).hom ((h.app _).hom (s.f j)) := by
  obtain rfl : φ' = fun k => h ≫ φ k := funext hφ
  rfl

/- English proof (translation)
Take `rfl : W = V` from `le_antisymm h1 h2`. Establish `e : homOfLE h1 = 𝟙 W` using `Subsingleton.elim _ _`. Rewrite `h` using `[e]`. Simplify using `using h`.
-/
lemma map_inj_of_le_ge {X : Scheme.{0}} {V W : X.Opens} (h1 : W ≤ V) (h2 : V ≤ W) {a b : Γ(X, V)}
    (h : (X.presheaf.map (homOfLE h1).op).hom a = (X.presheaf.map (homOfLE h1).op).hom b) : a = b := by
  obtain rfl : W = V := le_antisymm h1 h2
  have e : homOfLE h1 = 𝟙 W := Subsingleton.elim _ _
  rw [e] at h
  simpa using h

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

def secK (U : UnifPre I D A G) (s : H0 U.LG.L 1) : U.SecK 1 :=
  pullSec' U.LG.L _ _ s (pullback.fst G.hom (jK R)) _ (fun _ => (Category.comp_id _).symm)

/- English proof (translation)
Introduce `j₁ j₂ hc`. Establish `hj : j₁ = j₂` using `funext fun k => by`. Rewrite using `[Subsingleton.elim k 0]`. Conclude with `hc (Sum.inl 0) (Sum.inr 0) (Category.comp_id _).symm`. Substitute `hj` using the available equality.

Rewrite using `[secK, pullSec'_f]`. Establish `h1 : resTop (LB.wchart U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) j₁ ⊓ LB.wchart U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R) ≫ 𝟙 G.left) j₁) (1 : Γ(pullback G.hom (jK R), ⊤)) = 1` using `map_one _`. Rewrite using `[h1, _root_.one_mul, ← CommRingCat.comp_apply, ← Functor.map_comp]`. Both sides reduce to the same expression.
-/
lemma secK_rel (U : UnifPre I D A G) (s : H0 U.LG.L 1) :
    GeneratorPullback.SecScal U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) (fun _ => ((1 : ℕ) : ℤ)) (secK U s)
      (fun _ : Fin 1 => 𝟙 G.left) (fun _ => ((1 : ℕ) : ℤ)) s (pullback.fst G.hom (jK R)) 1 := by
  intro j₁ j₂ hc
  have hj : j₁ = j₂ := funext fun k => by
    rw [Subsingleton.elim k 0]
    exact hc (Sum.inl 0) (Sum.inr 0) (Category.comp_id _).symm
  subst hj
  rw [secK, pullSec'_f]
  have h1 : resTop (LB.wchart U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) j₁ ⊓
      LB.wchart U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R) ≫ 𝟙 G.left) j₁)
      (1 : Γ(pullback G.hom (jK R), ⊤)) = 1 := map_one _
  rw [h1, _root_.one_mul, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/- English proof (translation)
Introduce `(j : Fin 1 → U.LG.L.ι)`. Establish `hc : LB.Coh U.LG.L (Sum.elim (fun _ : Fin 1 => pullback.fst G.hom (jK R)) (fun k : Fin 1 => pullback.fst G.hom (jK R) ≫ (fun _ : Fin 1 => 𝟙 G.left) k)) (Sum.elim j j)`. Introduce `a b _`. Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b <;> exact congrArg j (Subsingleton.elim _ _)`. Establish `e1` using `h1 j j hc`.

Establish `e2` using `h2 j j hc`. Establish `h1' : resTop (LB.wchart U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) j ⊓ LB.wchart U.LG.L (fun k : Fin 1 => pullback.fst G.hom (jK R) ≫ (fun _ : Fin 1 => 𝟙 G.left) k) j) (1 : Γ(pullback G.hom (jK R), ⊤)) = 1` using `map_one _`. Rewrite `e1` using `[h1', _root_.one_mul]`. Rewrite `e2` using `[← e1]`. Establish `hle : pullback.fst G.hom (jK R) ⁻¹ᵁ LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j ≤ LB.wchart U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) j ⊓ LB.wchart U.LG.L (fun k : Fin 1 => pullback.fst G.hom (jK R) ≫ (fun _ : Fin 1 => 𝟙 G.left) k) j` using `fun x hx => ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx k, Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx k⟩`.

Apply `app_fst_jF_injective G.hom` to reduce the goal to its premises. Apply `map_inj_of_le_ge (inf_le_right.trans (wchart_comp_le _ _ j)) hle` to reduce the goal to its premises. Use `e2.trans ?_` and prove the remaining obligations. Establish `e3 : (((pullback.fst G.hom (jK R)).app (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j)).hom (toW G.hom (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j) r * (show Γ(G.left, LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j) from s.f j))) = toW (pullback.fst G.hom (jK R) ≫ G.hom) _ r …`. Rewrite using `[map_mul, app_toW]`.

Use `erw [e3, map_mul, toW_res, resTop_scal, toW_congr pullback.condition.symm]`.
-/
theorem sec_eq_of_secScal (U : UnifPre I D A G) [Flat G.hom] (s σ : H0 U.LG.L 1) (sK : U.SecK 1) (r : R)
    (h1 : GeneratorPullback.SecScal U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) (fun _ => ((1 : ℕ) : ℤ)) sK
      (fun _ : Fin 1 => 𝟙 G.left) (fun _ => ((1 : ℕ) : ℤ)) s (pullback.fst G.hom (jK R)) 1)
    (h2 : GeneratorPullback.SecScal U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) (fun _ => ((1 : ℕ) : ℤ)) sK
      (fun _ : Fin 1 => 𝟙 G.left) (fun _ => ((1 : ℕ) : ℤ)) σ (pullback.fst G.hom (jK R))
      (scal (pullback.snd G.hom (jK R) ≫ jK R) r)) :
    ∀ j, σ.f j = toW G.hom _ r * s.f j := by
  intro (j : Fin 1 → U.LG.L.ι)
  have hc : LB.Coh U.LG.L (Sum.elim (fun _ : Fin 1 => pullback.fst G.hom (jK R))
      (fun k : Fin 1 => pullback.fst G.hom (jK R) ≫ (fun _ : Fin 1 => 𝟙 G.left) k)) (Sum.elim j j) := by
    intro a b _
    rcases a with a | a <;> rcases b with b | b <;> exact congrArg j (Subsingleton.elim _ _)
  have e1 := h1 j j hc
  have e2 := h2 j j hc
  have h1' : resTop (LB.wchart U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) j ⊓
      LB.wchart U.LG.L (fun k : Fin 1 => pullback.fst G.hom (jK R) ≫ (fun _ : Fin 1 => 𝟙 G.left) k) j)
      (1 : Γ(pullback G.hom (jK R), ⊤)) = 1 := map_one _
  rw [h1', _root_.one_mul] at e1
  rw [← e1] at e2
  have hle : pullback.fst G.hom (jK R) ⁻¹ᵁ LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j ≤
      LB.wchart U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) j ⊓
        LB.wchart U.LG.L (fun k : Fin 1 => pullback.fst G.hom (jK R) ≫ (fun _ : Fin 1 => 𝟙 G.left) k) j :=
    fun x hx => ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx k, Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx k⟩
  apply app_fst_jF_injective G.hom
  apply map_inj_of_le_ge (inf_le_right.trans (wchart_comp_le _ _ j)) hle
  refine e2.trans ?_
  have e3 : (((pullback.fst G.hom (jK R)).app (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j)).hom
      (toW G.hom (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j) r *
        (show Γ(G.left, LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j) from s.f j))) =
      toW (pullback.fst G.hom (jK R) ≫ G.hom) _ r *
        ((pullback.fst G.hom (jK R)).app (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j)).hom
          (show Γ(G.left, LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j) from s.f j) := by
    rw [map_mul, app_toW]
  erw [e3, map_mul, toW_res, resTop_scal, toW_congr pullback.condition.symm]

end ReciprocityTheory.ChartRestriction.G.DVR.TG
