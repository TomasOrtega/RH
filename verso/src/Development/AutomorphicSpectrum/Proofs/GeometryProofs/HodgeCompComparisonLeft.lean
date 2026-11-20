import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CardComapMulFinsumEqFinsumFibres
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapFromSpecStalk
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackCorrespondence
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeDominantCompatStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.CoverLie

section Move

variable {S : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']

/- English proof (translation)
Set `u : Over.mk x' ⟶ Over.mk x` to `Over.homMk (Spec.map (CommRingCat.ofHom φ)) h`. Establish `e : (LieEx.zsec x' : _ ⟶ LieEx.ob x' R') ≫ LieCarrier.epsHom φ x x' h = u ≫ LieEx.zsec x`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Use `show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _`. Rewrite using `[← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]`.

Use `congr 2`. Use `RingHom.ext fun a => ?_` and prove the remaining obligations. Simplify using `[dualMap]`. Use `(LieEx.isTanAt_iff x' G _).2 ?_` and prove the remaining obligations. Rewrite using `[← Category.assoc, e, Category.assoc, (LieEx.isTanAt_iff x G _).1 hv, MonObj.comp_one]`.
-/
theorem tan_up {G : Over S} [GrpObj G] (φ : R →+* R') (x : Sp R ⟶ S) (x' : Sp R' ⟶ S)
    (h : Spec.map (CommRingCat.ofHom φ) ≫ x = x') (v : epsAt x ⟶ G) (hv : IsTanAt G x v) :
    IsTanAt G x' (LieCarrier.epsHom φ x x' h ≫ v) := by
  let u : Over.mk x' ⟶ Over.mk x := Over.homMk (Spec.map (CommRingCat.ofHom φ)) h
  have e : (LieEx.zsec x' : _ ⟶ LieEx.ob x' R') ≫ LieCarrier.epsHom φ x x' h = u ≫ LieEx.zsec x := by
    apply Over.OverMorphism.ext
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun a => ?_
    simp [dualMap]
  refine (LieEx.isTanAt_iff x' G _).2 ?_
  rw [← Category.assoc, e, Category.assoc, (LieEx.isTanAt_iff x G _).1 hv, MonObj.comp_one]

variable {X X' : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω'] {ξ : Sp Ω ⟶ X} {ξ' : Sp Ω' ⟶ X'} {f : X' ⟶ X}
  {i : Ω →+* Ω'} {G : Over X} {G' : Over X'} [GrpObj G] [GrpObj G'] {φ : G'.left ⟶ G.left}
  {V V' : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V']

/- English proof (translation)
Establish `hx : Spec.map (CommRingCat.ofHom i) ≫ ξ = ξ' ≫ f` using `hd.symm`. Set `P` to `LieMove.pushModel hG M'`. Establish `ex : ∀ e, ∃ e', P.pt e' = LieCarrier.epsHom i ξ (ξ' ≫ f) hx ≫ M.pt e` using `fun e => P.onto _ (tan_up i ξ (ξ' ≫ f) hx _ (M.tan e))`. Use `choose j hj using ex`. Use `⟨AddMonoidHom.mk' j fun a b => P.inj ?_, fun e => congrArg (fun z => z.left) (hj e)⟩` and prove the remaining obligations.

Rewrite using `[P.add, hj, hj, hj, M.add, MonObj.comp_mul]`.
-/
theorem exists_hom (hd : GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i) (hG : IsGrpPullback G' G f φ) (M : LieModel G ξ V)
    (M' : LieModel G' ξ' V') :
    ∃ j : V →+ V', ∀ e, (M'.pt (j e)).left ≫ φ = Spec.map (CommRingCat.ofHom (dualMap i)) ≫ (M.pt e).left := by
  have hx : Spec.map (CommRingCat.ofHom i) ≫ ξ = ξ' ≫ f := hd.symm
  let P := LieMove.pushModel hG M'
  have ex : ∀ e, ∃ e', P.pt e' = LieCarrier.epsHom i ξ (ξ' ≫ f) hx ≫ M.pt e :=
    fun e => P.onto _ (tan_up i ξ (ξ' ≫ f) hx _ (M.tan e))
  choose j hj using ex
  refine ⟨AddMonoidHom.mk' j fun a b => P.inj ?_, fun e => congrArg (fun z => z.left) (hj e)⟩
  rw [P.add, hj, hj, hj, M.add, MonObj.comp_mul]

/- English proof (translation)
Use `M'.inj (Over.OverMorphism.ext (hG.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm)))` and prove the remaining obligations. Rewrite using `[hj, hT e, hT' (j e), Over.comp_left, Over.comp_left, Category.assoc, hφ, ← Category.assoc, ← Category.assoc, hj]`.
-/
theorem map_diff {M : LieModel G ξ V} {M' : LieModel G' ξ' V'} {a : G ⟶ G} {a' : G' ⟶ G'}
    (hG : IsGrpPullback G' G f φ) (hφ : a'.left ≫ φ = φ ≫ a.left) {j : V →+ V'}
    (hj : ∀ e, (M'.pt (j e)).left ≫ φ = Spec.map (CommRingCat.ofHom (dualMap i)) ≫ (M.pt e).left)
    {T : V →ₗ[Ω] V} {T' : V' →ₗ[Ω'] V'} (hT : M.IsDiffOf a T) (hT' : M'.IsDiffOf a' T') (e : V) :
    j (T e) = T' (j e) := by
  refine M'.inj (Over.OverMorphism.ext (hG.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm)))
  rw [hj, hT e, hT' (j e), Over.comp_left, Over.comp_left, Category.assoc, hφ, ← Category.assoc, ← Category.assoc, hj]

end Move

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

/- English proof (translation)
Substitute `hf` using the available equality. Conclude with `sabCancel pullCubCancel E H S S' S'' t t' t'' f g m n`.
-/
theorem cancel {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S} {g : S'' ⟶ S'}
    {f' : S'' ⟶ S} (hf : f' = g ≫ f) (m : SABMap t' t f) (n : SABMap t'' t f') :
    ∃ m' : SABMap t'' t' g, n.φ = m'.φ ≫ m.φ := by
  subst hf
  exact sabCancel pullCubCancel E H S S' S'' t t' t'' f g m n

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c Y S₀ S Ω₁ Ω _ _ K₁ _ J₁ _ y₁ K _ J _ y A B i h hd hf`. Take `⟨m, hm⟩` from `cancel hf A.m B.m`. Take `⟨j, hj⟩` from `exists_hom hd m.cart A.M B.M`. Take `⟨hx, -, hl⟩` from `GlobalTheory.T.lie_lattice_dominant_compat A.X B.X Ω₁ Ω A.ξ B.ξ h i A.t.G B.t.G m.φ A.Li B.Li A.M B.M j A.tie.gen B.tie.gen hd m.cart A.t.semi.smooth hj`. Use `⟨j, hx, fun e => ?_, fun a e => ?_, hl⟩` and prove the remaining obligations.

Rewrite using `[hm, ← Category.assoc, hj, Category.assoc]`. Conclude with `map_diff m.cart (m.act a) hj (A.act a) (B.act a) e`.
-/
theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S₀ S : Finset ℕ) (Ω₁ Ω : Type) [Field Ω₁] [Field Ω] (K₁ : Type) [Fintype K₁] (J₁ : K₁ → Type) [∀ k, Fintype (J₁ k)] (y₁ : (Σ k, J₁ k) → Ω₁) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S₀ y₁) (B : HodgeCpt Y S y) (i : Ω₁ →+* Ω) (h : B.X ⟶ A.X), GlobalTheory.CompanionTheory.Ar.Dominates B.ξ A.ξ h i → B.f = h ≫ A.f → ∃ jA : A.Li →+ B.Li, IsExtOver i jA ∧ (∀ e, (B.M.pt (jA e)).left ≫ B.m.φ = spMap (dualMap i) ≫ (A.M.pt e).left ≫ A.m.φ) ∧ (∀ a e, jA (A.ρ a e) = B.ρ a (jA e)) ∧ B.M.lat = A.M.lat.pull B.ξ h jA := by
  intro E _ _ _ H D l Xo c Y S₀ S Ω₁ Ω _ _ K₁ _ J₁ _ y₁ K _ J _ y A B i h hd hf
  obtain ⟨m, hm⟩ := cancel hf A.m B.m
  obtain ⟨j, hj⟩ := exists_hom hd m.cart A.M B.M
  obtain ⟨hx, -, hl⟩ := GlobalTheory.T.lie_lattice_dominant_compat A.X B.X Ω₁ Ω A.ξ B.ξ h i A.t.G B.t.G m.φ A.Li B.Li A.M B.M j A.tie.gen B.tie.gen
    hd m.cart A.t.semi.smooth hj
  refine ⟨j, hx, fun e => ?_, fun a e => ?_, hl⟩
  · rw [hm, ← Category.assoc, hj, Category.assoc]
  · exact map_diff m.cart (m.act a) hj (A.act a) (B.act a) e

end GlobalTheory.CompanionTheory.Ar.CoverLie
