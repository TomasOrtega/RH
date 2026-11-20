import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerUniformisedMonomialPeriodsLatticeIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullUnif
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BetaPos
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftCompSquare
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.TraitPow

/- English proof (translation)
Introduce `g n o _ ζ F W hW T R _ _ _ hB hdvr G' _ _ hG' D' A' U' h hK hl hhK c pr hS`. Take `⟨G, _, _, D, A, U, α, α₂, ε, hG, hα, hαsq, ⟨w', hw'⟩, hτ⟩` from `GlobalTheory.Poinc.TraitPull.exists_pull_unif g n o ζ F T R hB hdvr h hK hl hhK`. Take `⟨⟨φc, φ₂, hc, hsq, ⟨w, hw⟩, -⟩, hpr, huniv, hL⟩` from `hS`. Take `⟨i, hi, hii⟩` from `grpPullback_iso hc hα`. Establish `hpt : ∀ a, (pr a).left ≫ φc = (pr a ≫ i.hom).left ≫ α` using `fun a => by`.

Rewrite using `[Over.comp_left, Category.assoc (pr a).left, hii]`. Establish `hΛ : (abelian₂ A.A A.L).IsLB` using `LB.isLB_linComb A.isLB _ _`. Establish `i₁` using `iso_linComb ((isGen_iff w).1 hw) (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)`. Establish `i₂` using `iso_linComb ((isGen_iff w').1 hw') (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1 ≫ i.hom) (pr ab.2 ≫ i.hom)).left) (fun ab => W ab.1 ab.2)`. Establish `hm : (fun ab : Fin 8 × Fin 8 => (lift (pr ab.1) (pr ab.2)).left ≫ φ₂) = fun ab => (lift (pr ab.1 ≫ i.hom) (pr ab.2 ≫ i.hom)).left ≫ α₂`.

Use function extensionality and compare the values at `fun ab => GlobalTheory.Poinc.SharpIdent.lift_comp_square hsq hαsq _ _ _ _ (hpt ab.1) (hpt ab.2)`. Rewrite `i₁` using `[hm]`. Establish `hL'` using `LBIso.trans A'.isLB (LB.isLB_linComb c.isLB _ _) (LB.isLB_linComb hΛ _ _) hL (LBIso.trans (LB.isLB_linComb c.isLB _ _) (LB.isLB_linComb F.univ.isLB _ _) (LB.isLB_linComb hΛ _ _) i₁ i₂.symm)`. Establish `hu' : ∀ (T' : Over (Sp (FractionRing R))) (y : Fin 8 → (T' ⟶ A.A)), ∃! z : T' ⟶ A'.A, ∀ a, z ≫ pr a ≫ i.hom = y a`. Introduce `T' y`.

Take `⟨z, hz, hz'⟩` from `huniv T' fun a => y a ≫ i.inv`. Use `⟨z, fun a => ?_, fun z' h' => hz' z' fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[← Category.assoc, hz a, Category.assoc, i.inv_hom_id, Category.comp_id]`. Rewrite using `[← h' a, Category.assoc z', Category.assoc (pr a), i.hom_inv_id, Category.comp_id]`. Establish `hnn : ∀ a, 0 ≤ T.β a a` using `fun a => by`.

Distinguish the cases in `ha : a = 0`. Simplify using `[ha]`. Conclude with `(GlobalTheory.Poinc.Trait.beta_pos g n o ζ F T a ha).le`. Take `⟨e, he₁, he₂⟩` from `GlobalTheory.T.eighthPower_uniformised_monomialPeriods_latticeIso R hB hdvr G hG D A U G' hG' D' A' U' W hW (fun a => pr a ≫ i.hom) (fun a => by have := hpr a; infer_instance) hu' hL' (h T.ϖ) (T.β.compl₁₂ (ε : D.toPre.X →+ T.D.toPre.X).toIntLinearMap (ε : D.toPre.X →+ T.D.toPre.X …`. Use `⟨e.trans (AddEquiv.piCongrRight fun _ => ε), he₁, ?_⟩` and prove the remaining obligations.

Introduce `a b f f₁ m hf hM hgen hE y v`. Establish `hM' : MatEnd (fun a => pr a ≫ i.hom) a b f₁`. Use `⟨hM.1, fun u => ?_⟩` and prove the remaining obligations. Rewrite using `[← Category.assoc, hM.2 u]`. Use `split_ifs`.

Both sides reduce to the same expression. Conclude with `MonObj.one_comp _`. Establish `key` using `congrArg ε (he₂ a b f f₁ m hf hM' hgen hE y v)`. Rewrite `key` using `[apply_ite ε, map_sum, map_sum, map_zero]`. Simplify using `only [map_zsmul] at key`.

Conclude with `key`.
-/
theorem exists_equiv : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (T : Trait F) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → IsDiscreteValuationRing R → ∀ (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G') (h : T.V →+* R) (hK : FractionRing T.V →+* FractionRing R), IsLocalHom h → (∀ a, hK (algebraMap T.V _ a) = algebraMap R _ (h a)) → ∀ c pr, SharpBy F W A' (spMap hK ≫ T.y) c pr → ∃ e : D'.toPre.X ≃+ (Fin 8 → T.D.toPre.X), (∀ y r, PsiCoord D'.toPre y r → 0 ≤ qW W T.β (e y) ∧ Associated r (h T.ϖ ^ (qW W T.β (e y)).toNat)) ∧ ∀ (a b : Fin 8) (f : G' ⟶ G') (f₁ : A'.A ⟶ A'.A) (m : D'.toPre.X →+ D'.toPre.X), IsMonHom f → MatEnd pr a b f₁ → (Over.pullback (jK R)).map f ≫ U'.gen.hom = U'.gen.hom ≫ f₁ → EndChar U' f m → ∀ y, MatRel W a b (e y) (e (m y)) := by
  intro g n o _ ζ F W hW T R _ _ _ hB hdvr G' _ _ hG' D' A' U' h hK hl hhK c pr hS
  obtain ⟨G, _, _, D, A, U, α, α₂, ε, hG, hα, hαsq, ⟨w', hw'⟩, hτ⟩ :=
    GlobalTheory.Poinc.TraitPull.exists_pull_unif g n o ζ F T R hB hdvr h hK hl hhK
  obtain ⟨⟨φc, φ₂, hc, hsq, ⟨w, hw⟩, -⟩, hpr, huniv, hL⟩ := hS
  obtain ⟨i, hi, hii⟩ := grpPullback_iso hc hα
  have hpt : ∀ a, (pr a).left ≫ φc = (pr a ≫ i.hom).left ≫ α := fun a => by
    rw [Over.comp_left, Category.assoc (pr a).left, hii]
  have hΛ : (abelian₂ A.A A.L).IsLB := LB.isLB_linComb A.isLB _ _
  have i₁ := iso_linComb ((isGen_iff w).1 hw) (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left)
    (fun ab => W ab.1 ab.2)
  have i₂ := iso_linComb ((isGen_iff w').1 hw') (K := Fin 8 × Fin 8)
    (fun ab => (lift (pr ab.1 ≫ i.hom) (pr ab.2 ≫ i.hom)).left) (fun ab => W ab.1 ab.2)
  have hm : (fun ab : Fin 8 × Fin 8 => (lift (pr ab.1) (pr ab.2)).left ≫ φ₂) =
      fun ab => (lift (pr ab.1 ≫ i.hom) (pr ab.2 ≫ i.hom)).left ≫ α₂ :=
    funext fun ab => GlobalTheory.Poinc.SharpIdent.lift_comp_square hsq hαsq _ _ _ _ (hpt ab.1) (hpt ab.2)
  rw [hm] at i₁
  have hL' := LBIso.trans A'.isLB (LB.isLB_linComb c.isLB _ _) (LB.isLB_linComb hΛ _ _) hL
    (LBIso.trans (LB.isLB_linComb c.isLB _ _) (LB.isLB_linComb F.univ.isLB _ _) (LB.isLB_linComb hΛ _ _) i₁ i₂.symm)
  have hu' : ∀ (T' : Over (Sp (FractionRing R))) (y : Fin 8 → (T' ⟶ A.A)),
      ∃! z : T' ⟶ A'.A, ∀ a, z ≫ pr a ≫ i.hom = y a := by
    intro T' y
    obtain ⟨z, hz, hz'⟩ := huniv T' fun a => y a ≫ i.inv
    refine ⟨z, fun a => ?_, fun z' h' => hz' z' fun a => ?_⟩
    · rw [← Category.assoc, hz a, Category.assoc, i.inv_hom_id, Category.comp_id]
    · rw [← h' a, Category.assoc z', Category.assoc (pr a), i.hom_inv_id, Category.comp_id]
  have hnn : ∀ a, 0 ≤ T.β a a := fun a => by
    by_cases ha : a = 0
    · simp [ha]
    · exact (GlobalTheory.Poinc.Trait.beta_pos g n o ζ F T a ha).le
  obtain ⟨e, he₁, he₂⟩ := GlobalTheory.T.eighthPower_uniformised_monomialPeriods_latticeIso R hB hdvr G hG D A U G' hG' D' A' U' W hW (fun a => pr a ≫ i.hom)
    (fun a => by have := hpr a; infer_instance) hu' hL' (h T.ϖ)
    (T.β.compl₁₂ (ε : D.toPre.X →+ T.D.toPre.X).toIntLinearMap (ε : D.toPre.X →+ T.D.toPre.X).toIntLinearMap)
    (fun a b => T.symm (ε a) (ε b)) (fun a => hnn (ε a)) hτ
  refine ⟨e.trans (AddEquiv.piCongrRight fun _ => ε), he₁, ?_⟩
  intro a b f f₁ m hf hM hgen hE y v
  have hM' : MatEnd (fun a => pr a ≫ i.hom) a b f₁ := by
    refine ⟨hM.1, fun u => ?_⟩
    rw [← Category.assoc, hM.2 u]
    split_ifs
    · rfl
    · exact MonObj.one_comp _
  have key := congrArg ε (he₂ a b f f₁ m hf hM' hgen hE y v)
  rw [apply_ite ε, map_sum, map_sum, map_zero] at key
  simp only [map_zsmul] at key
  exact key

end GlobalTheory.Poinc.TraitPow
