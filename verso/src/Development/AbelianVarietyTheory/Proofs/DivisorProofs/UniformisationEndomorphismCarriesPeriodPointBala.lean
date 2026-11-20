import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniformizationEndomorphismOfLinear
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndDataSymmAndOfOAct
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.UT

noncomputable section

namespace GlobalTheory.Mum.KeepsIota

variable {R : Type} [CommRing R] [IsDomain R]

/- English proof (translation)
Establish `cf : ∀ T, cP D T (k χ) = cP D T χ ≫ f` using `fun T => by`. Rewrite using `[cP, hk, ← Category.assoc]`. Both sides reduce to the same expression. Take `⟨v, hv, vv⟩` from `exists_gen D.P.isLB (φ' := Sum.elim (D.Oφ (𝟙 _) (k χ)) (D.Oφ g χ)) (ε' := Sum.elim Oε Oinvε) (fun U _ h => by`. Use `(prod_ros _ _ (cP D _ χ) (𝟙 D.P.A) h).trans (Eq.symm ?_)` and prove the remaining obligations.

Use `(prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ (GlobalTheory.UT.OLinEnd.prod_Oφ D (𝟙 _) (k χ) h) (GlobalTheory.UT.OLinEnd.prod_Oφ_inv D g χ h)).trans ?_` and prove the remaining obligations. Rewrite using `[cf, Category.id_comp]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv]`. Use the proof step `abel)`.

Use the proof step `(LB.pullGen D.P.L _ _ u (lift (cP D D.P.A χ) (𝟙 D.P.A)).left) (pullGen_isGen _ _ _ _ hu _)`. Establish `key : ∀ (T : Over (Spec (CommRingCat.of R))) (x : T ⟶ D.P.A) (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) (J), Good D.P.L z J → val v (r ≫ x.left) z J = val u (r ≫ (lift (cP D T χ) x).left) z J` using `fun T x Z r z J hJ => by`. Rewrite using `[vv Z _ z J hJ, val_pull hJ, Category.assoc, ← Over.comp_left, comp_lift, comp_cP, Category.comp_id]`. Use `⟨v, ⟨hv, corr_of_val D.P.isLB fun y J hJ => ?_⟩, key⟩` and prove the remaining obligations. Establish `C : IsCub (cubV D.cub (T` using `𝟙_ (Over (Spec (CommRingCat.of R)))) y J) := isCub_cubV D.cub hJ`.

Establish `e` using `(ros_add D.cub hG D.P.isAb _ _ u hu u₀ (T := 𝟙_ (Over (Spec (CommRingCat.of R)))) hJ 1 1 (cP D _ χ)).2`. Rewrite `e` using `[_root_.mul_one, MonObj.one_comp, C.face₃, C.face₃, _root_.mul_one, _root_.one_mul]`. Establish `e' : val₂ u (T` using `𝟙_ (Over (Spec (CommRingCat.of R)))) y J (cP D _ χ) 1 = 1 := mul_eq_left.1 e.symm`. Establish `k'` using `key (𝟙_ (Over (Spec (CommRingCat.of R)))) 1 _ (𝟙 _) y J hJ`. Establish `o : (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A).left = eSec D.P.A`.

Rewrite using `[Hom.one_def, toUnit_unit, Category.id_comp]`. Both sides reduce to the same expression. Rewrite `k'` using `[o]`. Use `(val_pull hJ _ _ _).trans (k'.trans (Eq.trans ?_ (val_one _).symm))` and prove the remaining obligations. Rewrite using `[Category.id_comp]`.

Conclude with `e'`.
-/
theorem exists_v (hG : GlobalFnsSt) (D : DegPre R) (f g : D.P.A ⟶ D.P.A) [IsMonHom f] [IsMonHom g]
    (k : D.X → D.X) (hk : ∀ χ, D.c (k χ) = D.c χ ≫ f)
    (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A f g) rosatiε)) (hu : u.IsGen)
    (u₀ : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zero2 D.P.A)) (LB.oneGen D.P.L)) (χ : D.X) :
    ∃ v : LB.Gen (LB.LinComb D.P.L (Sum.elim (D.Oφ (𝟙 _) (k χ)) (D.Oφ g χ)) (Sum.elim Oε Oinvε)),
      Normd v ∧ ∀ (T : Over (Spec (CommRingCat.of R))) (x : T ⟶ D.P.A) (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) (J),
        Good D.P.L z J → val v (r ≫ x.left) z J = val u (r ≫ (lift (cP D T χ) x).left) z J := by
  have cf : ∀ T, cP D T (k χ) = cP D T χ ≫ f := fun T => by
    rw [cP, hk, ← Category.assoc]; rfl
  obtain ⟨v, hv, vv⟩ := exists_gen D.P.isLB
    (φ' := Sum.elim (D.Oφ (𝟙 _) (k χ)) (D.Oφ g χ)) (ε' := Sum.elim Oε Oinvε)
    (fun U _ h => by
      refine (prod_ros _ _ (cP D _ χ) (𝟙 D.P.A) h).trans (Eq.symm ?_)
      refine (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ (GlobalTheory.UT.OLinEnd.prod_Oφ D (𝟙 _) (k χ) h)
        (GlobalTheory.UT.OLinEnd.prod_Oφ_inv D g χ h)).trans ?_
      rw [cf, Category.id_comp]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
    (LB.pullGen D.P.L _ _ u (lift (cP D D.P.A χ) (𝟙 D.P.A)).left) (pullGen_isGen _ _ _ _ hu _)
  have key : ∀ (T : Over (Spec (CommRingCat.of R))) (x : T ⟶ D.P.A) (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) (J),
      Good D.P.L z J → val v (r ≫ x.left) z J = val u (r ≫ (lift (cP D T χ) x).left) z J := fun T x Z r z J hJ => by
    rw [vv Z _ z J hJ, val_pull hJ, Category.assoc, ← Over.comp_left, comp_lift, comp_cP, Category.comp_id]
  refine ⟨v, ⟨hv, corr_of_val D.P.isLB fun y J hJ => ?_⟩, key⟩
  have C : IsCub (cubV D.cub (T := 𝟙_ (Over (Spec (CommRingCat.of R)))) y J) := isCub_cubV D.cub hJ
  have e := (ros_add D.cub hG D.P.isAb _ _ u hu u₀ (T := 𝟙_ (Over (Spec (CommRingCat.of R)))) hJ 1 1 (cP D _ χ)).2
  rw [_root_.mul_one, MonObj.one_comp, C.face₃, C.face₃, _root_.mul_one, _root_.one_mul] at e
  have e' : val₂ u (T := 𝟙_ (Over (Spec (CommRingCat.of R)))) y J (cP D _ χ) 1 = 1 := mul_eq_left.1 e.symm
  have k' := key (𝟙_ (Over (Spec (CommRingCat.of R)))) 1 _ (𝟙 _) y J hJ
  have o : (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A).left = eSec D.P.A := by
    rw [Hom.one_def, toUnit_unit, Category.id_comp]; rfl
  rw [o] at k'
  refine (val_pull hJ _ _ _).trans (k'.trans (Eq.trans ?_ (val_one _).symm))
  rw [Category.id_comp]
  exact e'

/- English proof (translation)
Introduce `R _ _ _ _ D A G _ _ _ U a a' h h' hd E hEa hEh F _ _ _ y g g' hg hact`. Substitute `hEa hEh` using the available equality. Establish `hG : GlobalFnsSt` using `GlobalTheory.SemiRigid.globalFns`. Establish `hs` using `(endData_symm_and_ofOAct R D.toPre).1 _ _ _ _ hd`. Take `⟨ha, ha', -, hc, hc', -⟩` from `hd`.

Take `⟨-, -, hr', -, -, hbal'⟩` from `hs`. Take `⟨u, hu, u₀⟩` from `exists_ros hG D.toPre.P.isAb D.toPre.P.isLB _ _ hr'`. Take `⟨gb, gv⟩` from `(isIota_iff _ _).1 hg`. Use `(isIota_iff _ _).2 ⟨?_, fun χ z J hJ => ?_⟩` and prove the remaining obligations. Rewrite using `[hact.1, gb, cP, cP, hc, ← Category.assoc]`.

Take `⟨v, hv, vv⟩` from `exists_v hG D.toPre a' E.aB E.h hc' u hu u₀ χ`. Establish `k1 : val (E.u χ) g.b.left z J = val u (lift (cP D.toPre _ χ) g.b).left z J`. Use `vv _ g.b _ (𝟙 _) z J hJ` as an intermediate fact. Rewrite `this` using `[Category.id_comp, Category.id_comp]`. Conclude with `(GlobalTheory.UT.SymFrame.normd_unique hG (E.u_norm χ) hv _ z J hJ).trans this`.

Rewrite using `[hact.2 χ z J hJ, gv _ z J hJ, k1, gb]`. Set `κ : TF (R` to `R) F ⟶ TK R := Over.homMk (𝟙 _ ≫ jFK (R := R) F) (by rw [Category.id_comp]; rfl)`. Establish `e` using `(val_mul hJ _ _ _).symm.trans (val_corr hJ (hbal' u hu u₀ χ y) κ.left)`. Establish `e' : val (LB.pullGen D.toPre.P.L _ _ u (D.toPre.pt2 χ y)) κ.left z J = val u (lift (cP D.toPre _ χ) (cP D.toPre _ y)).left z J`. Rewrite using `[val_pull hJ, ← comp_cP D.toPre κ, ← comp_cP D.toPre κ y, ← comp_lift]`.

Both sides reduce to the same expression. Rewrite using `[← e']`. Conclude with `(congrArg₂ (· * ·) (tau_symm (𝟙 (TF (R := R) F)) hJ _ _) rfl).trans (e.trans (tau_symm (𝟙 (TF (R := R) F)) hJ _ _))`.
-/
theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ E : EndU U.toUnifPre, E.aB = a → E.h = h' → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (y : D.toPre.X) (g g' : GtPtF D.toPre F), GtPtF.IsIota y g → E.Act g g' → GtPtF.IsIota (h y) g' := by
  intro R _ _ _ _ D A G _ _ _ U a a' h h' hd E hEa hEh F _ _ _ y g g' hg hact
  subst hEa hEh
  have hG : GlobalFnsSt := GlobalTheory.SemiRigid.globalFns
  have hs := (endData_symm_and_ofOAct R D.toPre).1 _ _ _ _ hd
  obtain ⟨ha, ha', -, hc, hc', -⟩ := hd
  obtain ⟨-, -, hr', -, -, hbal'⟩ := hs
  obtain ⟨u, hu, u₀⟩ := exists_ros hG D.toPre.P.isAb D.toPre.P.isLB _ _ hr'
  obtain ⟨gb, gv⟩ := (isIota_iff _ _).1 hg
  refine (isIota_iff _ _).2 ⟨?_, fun χ z J hJ => ?_⟩
  · rw [hact.1, gb, cP, cP, hc, ← Category.assoc]
  · obtain ⟨v, hv, vv⟩ := exists_v hG D.toPre a' E.aB E.h hc' u hu u₀ χ
    have k1 : val (E.u χ) g.b.left z J = val u (lift (cP D.toPre _ χ) g.b).left z J := by
      have := vv _ g.b _ (𝟙 _) z J hJ
      rw [Category.id_comp, Category.id_comp] at this
      exact (GlobalTheory.UT.SymFrame.normd_unique hG (E.u_norm χ) hv _ z J hJ).trans this
    rw [hact.2 χ z J hJ, gv _ z J hJ, k1, gb]
    let κ : TF (R := R) F ⟶ TK R := Over.homMk (𝟙 _ ≫ jFK (R := R) F) (by rw [Category.id_comp]; rfl)
    have e := (val_mul hJ _ _ _).symm.trans (val_corr hJ (hbal' u hu u₀ χ y) κ.left)
    have e' : val (LB.pullGen D.toPre.P.L _ _ u (D.toPre.pt2 χ y)) κ.left z J =
        val u (lift (cP D.toPre _ χ) (cP D.toPre _ y)).left z J := by
      rw [val_pull hJ, ← comp_cP D.toPre κ, ← comp_cP D.toPre κ y, ← comp_lift]; rfl
    rw [← e']
    exact (congrArg₂ (· * ·) (tau_symm (𝟙 (TF (R := R) F)) hJ _ _) rfl).trans
      (e.trans (tau_symm (𝟙 (TF (R := R) F)) hJ _ _))

end GlobalTheory.Mum.KeepsIota

end
