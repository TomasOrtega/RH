import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmallTorsionSetForEndomorphismStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelStructureChangeFramedGeometricPointUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrMoveTransfer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteOrderLevelMoveUniversalSemiAbelianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatCardQuotSmulTopLePowFinrankStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateIsometryTorsionEqLevelSmulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnipotentModIdealLiftLaInvStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

noncomputable section

namespace GlobalTheory.UnipFree

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c hpq hA1 I g hN hMb «γ» hU y hy`. Establish `hA : l.A.Coprime l.M` using `by rw [hA1]; exact Nat.coprime_one_left _`. Take `⟨ρ, ν, hiso, hm, hf⟩` from `GlobalTheory.LevDesc.levR_move (Xo := Xo) (c := c) hpq hA «γ» y`. Establish `hm' : IsLevMove ρ ν (liftLa «γ») LinearMap.id` using `hm`. Establish `hx : y.x ≫ ρ = y.x`.

Establish `e` using `congrArg (· ≫ pullback.fst _ _) hy`. Simplify using `only [GlobalTheory.AllWt.ptF, pullback.lift_fst] at e`. Rewrite using `[← hf.1]`. Conclude with `e`. Take `⟨hg, hnorm, hsq, hr⟩` from `hN`.

Use `set x := y.x with hxdef`. Use `set G := Xo.univ.t.G with hGdef`. Set `G0 : Over (Sp ℂ)` to `(Over.pullback x).obj G`. Set `act0 : OAct (𝓞 E) G0` to `OAct.pullback x G Xo.univ.t.act`. Establish `w : (pullback.fst G.hom x ≫ ν.φ) ≫ G.hom = pullback.snd G.hom x ≫ x`.

Rewrite using `[Category.assoc, ν.cart.1.w, ← Category.assoc, pullback.condition, Category.assoc, hx]`. Set `α : G0 ⟶ G0` to `Over.homMk (pullback.lift (pullback.fst G.hom x ≫ ν.φ) (pullback.snd G.hom x) w) (pullback.lift_snd _ _ _)`. Establish `hαf : α.left ≫ pullback.fst G.hom x = pullback.fst G.hom x ≫ ν.φ` using `pullback.lift_fst _ _ _`. Establish `pA : IsGrpPullback G0 G x (pullback.fst G.hom x)` using `isGrpPullback_pullback G x`. Establish `c₁ : IsGrpPullback G0 G x (pullback.fst G.hom x ≫ ν.φ)`.

Establish `c₀` using `IsGrpPullback.comp pA ν.cart`. Rewrite `c₀` using `[hx]`. Conclude with `c₀`. Establish `hαm : IsMonHom α` using `ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.isMonHom_of_grpPullback c₁ pA (𝟙 G) α (by simpa using hαf)`. Establish `hact0 : ∀ a, (act0.act a).left ≫ pullback.fst G.hom x = pullback.fst G.hom x ≫ (Xo.univ.t.act.act a).left` using `fun a => pullback.lift_fst _ _ _`.

Establish `hact : ∀ a, act0.act a ≫ α = α ≫ act0.act a` using `fun a => by`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Apply `pullback.hom_ext` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Establish `h1 : ∀ f : G0 ⟶ G0, f.left ≫ pullback.snd G.hom x = pullback.snd G.hom x` using `fun f => Over.w f`.

Simplify using `only [Over.comp_left, Category.assoc, h1]`. Take `⟨n, hn, hνn⟩` from `GlobalTheory.T.exists_finite_order_levelMove_universalSemiAbelian E H Dw l Xo c «γ» ρ ν hpq hA1 hiso hm'`. Establish `hαn : (fun f => f ≫ α)^[n] (𝟙 G0) = 𝟙 G0`. Establish `key : ∀ j, ((fun f => f ≫ α)^[j] (𝟙 G0)).left ≫ pullback.fst G.hom x = pullback.fst G.hom x ≫ (fun f : G.left ⟶ G.left => f ≫ ν.φ)^[j] (𝟙 _)`. Introduce `j`.

Proceed by induction on `j with`. Consider the case `zero => simp`. Consider the case `succ j ih`. Rewrite using `[Function.iterate_succ_apply', Function.iterate_succ_apply', Over.comp_left, Category.assoc, hαf, ← Category.assoc, ih, Category.assoc]`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises.

Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[key, hνn, Over.id_left, Category.id_comp, Category.comp_id]`. Establish `h1 : ∀ f : G0 ⟶ G0, f.left ≫ pullback.snd G.hom x = pullback.snd G.hom x` using `fun f => Over.w f`. Rewrite using `[h1]`. Simplify using the standard rewrite rules.

Establish `bw : ∀ u : 𝟙_ (Over (Sp ℂ)) ⟶ G0, (u.left ≫ pullback.fst G.hom x) ≫ G.hom = (Over.mk x).hom` using `fun u => by`. Rewrite using `[Category.assoc, pullback.condition, ← Category.assoc]`. Establish `e : u.left ≫ pullback.snd G.hom x = 𝟙 _` using `Over.w u`. Rewrite using `[e, Category.id_comp]`. Both sides reduce to the same expression.

Set `B : (𝟙_ (Over (Sp ℂ)) ⟶ G0) → (Over.mk x ⟶ G)` to `fun u => Over.homMk (u.left ≫ pullback.fst G.hom x) (bw u)`. Establish `B_left : ∀ u, (B u).left = u.left ≫ pullback.fst G.hom x` using `fun u => rfl`. Establish `B_inj : Function.Injective B` using `fun u v h => by`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Apply `pullback.hom_ext` to reduce the goal to its premises.

Conclude with `congrArg (fun z => z.left) h`. Conclude with `(Over.w u).trans (Over.w v).symm`. Establish `B_mul : ∀ u v, B (u * v) = B u * B v` using `fun u v => by`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Establish `e1` using `pA.2 (𝟙_ _) u v (pushPt pA.1.w u) (pushPt pA.1.w v) rfl rfl`.

Establish `e2` using `mul_left_congr (Category.id_comp x) (pushPt pA.1.w u) (pushPt pA.1.w v) (B u) (B v) rfl rfl`. Conclude with `e1.symm.trans e2`. Set `Bh : (𝟙_ (Over (Sp ℂ)) ⟶ G0) →* (Over.mk x ⟶ G)` to `MonoidHom.mk' B B_mul`. Establish `B_act : ∀ u a, B (u ≫ act0.act a) = B u ≫ Xo.univ.t.act.act a` using `fun u a => by`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises.

Rewrite using `[B_left, Over.comp_left, Over.comp_left, B_left, Category.assoc, Category.assoc, hact0]`. Establish `B_α : ∀ u, (B (u ≫ α)).left = (B u).left ≫ ν.φ` using `fun u => by`. Rewrite using `[B_left, B_left, Over.comp_left, Category.assoc, hαf, Category.assoc]`. Establish `B_one : B 1 = 1` using `map_one Bh`. Establish `tl : (toUnit (Over.mk x)).left = x` using `by simpa using Over.w (toUnit (Over.mk x))`.

Set `β : KA l →+* ℂ` to `(algebraMap c.F ℂ).comp (IntermediateField.inclusion c.le).toRingHom`. Take `⟨-, TI, -, -, hTI⟩` from `Xo.univ.geom ℂ x β y.x_over`. Set `et : Dw.La → (Over.mk x ⟶ G)` to `fun b => toUnit (Over.mk x) ≫ Xo.univ.eta b`. Establish `et_add : ∀ a b, et (a + b) = et a * et b` using `fun a b => by`. Simplify using `only [et, Xo.univ.eta_add, MonObj.comp_mul]`.

Establish `et_ker : ∀ a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La), et a = 1` using `fun a ha => by`. Simplify using `only [et, Xo.univ.eta_ker a ha, MonObj.comp_one]`. Establish `hadd : ∀ (a b : 𝓞 E) (z : Over.mk x ⟶ G), z ≫ Xo.univ.t.act.act (a + b) = (z ≫ Xo.univ.t.act.act a) * (z ≫ Xo.univ.t.act.act b)` using `fun a b z => by`. Rewrite using `[Xo.univ.t.act.add, MonObj.comp_mul]`. Establish `hone : ∀ z : Over.mk x ⟶ G, z ≫ Xo.univ.t.act.act 1 = z` using `fun z => by`.

Rewrite using `[Xo.univ.t.act.one, Category.comp_id]`. Establish `hnat : ∀ (k : ℕ) (z : Over.mk x ⟶ G), z ≫ Xo.univ.t.act.act (k : 𝓞 E) = z ^ k`. Introduce `k z`. Proceed by induction on `k with`. Consider the case `zero`.

Establish `h0` using `hadd 0 0 z`. Rewrite `h0` using `[add_zero]`. Simplify using `using h0`. Consider the case `succ k ih => rw [Nat.cast_succ, hadd, ih, hone, pow_succ]`. Take `⟨t, ht, htor⟩` from `GlobalTheory.T.tateIsometry_torsion_eq_level_smul E H Dw l ℂ (Over.mk x ⟶ G) (fun a z => z ≫ Xo.univ.t.act.act a) _ TI et I g hadd hone hnat (fun a ha => hTI a ha) hg hnorm hsq hMb`.

Establish `tor_B : ∀ u : 𝟙_ (Over (Sp ℂ)) ⟶ G0, (∀ a ∈ I, u ≫ act0.act a = 1) → ∃ c' : Dw.La, B u = et (t • c')` using `fun u hu => htor (B u) fun a ha => by rw [← B_act, hu a ha, B_one]`. Take `⟨hfin, hcard⟩` from `GlobalTheory.T.natCard_quot_smul_le_pow_finrank E Dw.La Dw.fin Dw.proj I g hg hnorm`. Use `haveI : Fintype (Dw.La ⧸ I • (⊤ : Submodule (𝓞 E) Dw.La)) := Fintype.ofFinite _`. Set `rep` to `Function.surjInv (Submodule.Quotient.mk_surjective (I • (⊤ : Submodule (𝓞 E) Dw.La)))`. Set `S' : Finset (Over.mk x ⟶ G)` to `Finset.univ.image fun q => et (t • rep q)`.

Establish `et_t : ∀ c', et (t • c') ∈ S'` using `fun c' => by`. Use `Finset.mem_image.2 ⟨Submodule.Quotient.mk c', Finset.mem_univ _, ?_⟩` and prove the remaining obligations. Establish `e : rep (Submodule.Quotient.mk c') - c' ∈ I • (⊤ : Submodule (𝓞 E) Dw.La)` using `(Submodule.Quotient.eq _).1 (Function.surjInv_eq _ _)`. Establish `e2` using `ht _ e`. Rewrite `e2` using `[smul_sub]`.

Establish `e3 : et (t • rep (Submodule.Quotient.mk c')) = et (t • rep (Submodule.Quotient.mk c') - t • c') * et (t • c')`. Rewrite using `[← et_add, sub_add_cancel]`. Rewrite using `[e3, et_ker _ e2, _root_.one_mul]`. Set `T0 : Finset (𝟙_ (Over (Sp ℂ)) ⟶ G0)` to `S'.preimage B B_inj.injOn`. Establish `hT0 : T0.card ≤ g ^ (Dw.p + Dw.q)`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.card_univ, Nat.card_eq_fintype_card]`. Use `_ ≤ g ^ (Dw.p + Dw.q) := by rw [← Dw.rank]; exact hcard`. Establish `hmemT : ∀ u : 𝟙_ (Over (Sp ℂ)) ⟶ G0, (∀ a ∈ I, u ≫ act0.act a = 1) → u ∈ T0` using `fun u hu => by`. Take `⟨c', hc'⟩` from `tor_B u hu`.

Conclude with `Finset.mem_preimage.2 (hc' ▸ et_t c')`. Take `⟨m, hmU⟩` from `GlobalTheory.T.isUnipotentModIdeal_liftLa_inv E H Dw l I «γ» hMb hU`. Establish `hδ : ∀ b, et (liftLa «γ» (liftLa «γ»⁻¹ b)) = et b` using `fun b => by`. Establish `e1` using `GlobalTheory.LevelActionLaws.liftLa_mul_sub «γ» «γ»⁻¹ b`. Establish `e2` using `GlobalTheory.LevelActionLaws.liftLa_one_sub (D := Dw) (l := l) b`.

Rewrite `e1` using `[mul_inv_cancel]`. Establish `e3 : liftLa «γ» (liftLa «γ»⁻¹ b) - b ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)`. Establish `e4` using `Submodule.sub_mem _ e2 e1`. Rewrite `e4` using `[sub_sub_sub_cancel_left]`. Then use the resulting hypothesis. Establish `e5 : et (liftLa «γ» (liftLa «γ»⁻¹ b)) = et (liftLa «γ» (liftLa «γ»⁻¹ b) - b) * et b`.

Rewrite using `[← et_add, sub_add_cancel]`. Rewrite using `[e5, et_ker _ e3, _root_.one_mul]`. Establish `B_step : ∀ u b, B u = et b → B (u ≫ α) = et (liftLa «γ»⁻¹ b)` using `fun u b hb => by`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[B_α, hb, ← hδ b]`.

Use `show (toUnit (Over.mk x) ≫ Xo.univ.eta (liftLa «γ» (liftLa «γ»⁻¹ b))).left ≫ ν.φ = (toUnit (Over.mk x) ≫ Xo.univ.eta (liftLa «γ»⁻¹ b)).left`. Rewrite using `[Over.comp_left, Over.comp_left, Category.assoc, hm'.2.1, tl, ← Category.assoc, hx]`. Set `φf : (𝟙_ (Over (Sp ℂ)) ⟶ G0) → (𝟙_ (Over (Sp ℂ)) ⟶ G0)` to `fun z => (z ≫ α) * z⁻¹`. Establish `B_iter : ∀ j u b, B u = et b → B (φf^[j] u) = et (((liftLa «γ»⁻¹ - 1) ^ j) b)`. Introduce `j`.

Proceed by induction on `j with`. Consider the case `zero => intro u b hb`. Simplify using `using hb`. Consider the case `succ j ih`. Introduce `u b hb`.

Rewrite using `[Function.iterate_succ_apply']`. Establish `h1` using `ih u b hb`. Use `set b' := ((liftLa «γ»⁻¹ - 1) ^ j) b`. Use `show Bh ((φf^[j] u ≫ α) * (φf^[j] u)⁻¹) = _`. Rewrite using `[map_mul, map_inv]`.

Use `show B (φf^[j] u ≫ α) * (B (φf^[j] u))⁻¹ = _`. Rewrite using `[B_step _ _ h1, h1, pow_succ', Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply]`. Rewrite using `[eq_comm, eq_mul_inv_iff_mul_eq, ← et_add, sub_add_cancel]`. Establish `hunip : ∀ u : 𝟙_ (Over (Sp ℂ)) ⟶ G0, (∀ a ∈ I, u ≫ act0.act a = 1) → (fun z : 𝟙_ (Over (Sp ℂ)) ⟶ G0 => (z ≫ α) * z⁻¹)^[m] u = 1` using `fun u hu => by`. Take `⟨c', hc'⟩` from `tor_B u hu`.

Apply `B_inj` to reduce the goal to its premises. Rewrite using `[B_iter m u _ hc', B_one, map_smul]`. Conclude with `et_ker _ (ht _ (hmU c'))`. Establish `hαid : α = 𝟙 G0` using `GlobalTheory.T.exists_small_torsion_set_for_endomorphism E ℂ G0 act0 α n m g (Dw.p + Dw.q) I (IsSemiAbelian.pullback x G Xo.univ.t.semi) hαm hact hn hαn hg hnorm hsq hr ⟨T0, hT0, hmemT⟩ hunip`. Establish `hαl : α.left = 𝟙 _` using `by rw [hαid]; rfl`.

Establish `fix : ∀ s : Over.mk x ⟶ G, s.left ≫ ν.φ = s.left` using `fun s => by`. Establish `hs : s.left ≫ G.hom = 𝟙 (Sp ℂ) ≫ x` using `by rw [Category.id_comp]; exact Over.w s`. Establish `e0 : pullback.lift s.left (𝟙 _) hs ≫ pullback.fst G.hom x = s.left` using `pullback.lift_fst _ _ _`. Rewrite using `[← e0, Category.assoc, ← hαf, hαl, Category.id_comp]`. Establish `heq : ∀ a, liftLa «γ» a - a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)` using `fun a => by`.

Use `GlobalTheory.LevelFree.eta_injective Xo x β y.x_over _ ?_` and prove the remaining obligations. Establish `e1 : et (liftLa «γ» a) = et a`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[← fix (et (liftLa «γ» a))]`. Use `show (toUnit (Over.mk x) ≫ Xo.univ.eta (liftLa «γ» a)).left ≫ ν.φ = (toUnit (Over.mk x) ≫ Xo.univ.eta a).left`.

Rewrite using `[Over.comp_left, Over.comp_left, Category.assoc, hm'.2.1, tl, ← Category.assoc, hx]`. Establish `e2 : et (liftLa «γ» a) = et (liftLa «γ» a - a) * et a` using `by rw [← et_add, sub_add_cancel]`. Rewrite `e2` using `[e1]`. Conclude with `mul_eq_right.1 e2.symm`. Use `LinearEquiv.ext fun q => ?_` and prove the remaining obligations.

Take `⟨a, rfl⟩` from `Submodule.Quotient.mk_surjective _ q`. Establish `e` using `liftLa_spec «γ» a`. Simplify using `only [Submodule.mkQ_apply] at e`. Express the relevant statement in the definitionally equal form `«γ» (Submodule.Quotient.mk a) = Submodule.Quotient.mk a`. Rewrite using `[← e]`.

Conclude with `(Submodule.Quotient.eq _).2 (heq a)`.
-/
theorem free : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → l.A = 1 → ∀ (I : Ideal (𝓞 E)) (g : ℕ), NeatPrime I g (Dw.p + Dw.q) → l.Mb ≤ I → ∀ «γ» : LevelAut Dw l, UnipAt I «γ» → ∀ y : FrPt Xo c ℂ, ptF (move Xo c «γ» y) = ptF y → «γ» = 1 := by
  intro E _ _ _ H Dw l Xo c hpq hA1 I g hN hMb «γ» hU y hy
  have hA : l.A.Coprime l.M := by rw [hA1]; exact Nat.coprime_one_left _
  obtain ⟨ρ, ν, hiso, hm, hf⟩ := GlobalTheory.LevDesc.levR_move (Xo := Xo) (c := c) hpq hA «γ» y
  have hm' : IsLevMove ρ ν (liftLa «γ») LinearMap.id := hm
  have hx : y.x ≫ ρ = y.x := by
    have e := congrArg (· ≫ pullback.fst _ _) hy
    simp only [GlobalTheory.AllWt.ptF, pullback.lift_fst] at e
    rw [← hf.1]; exact e
  obtain ⟨hg, hnorm, hsq, hr⟩ := hN
  set x := y.x with hxdef
  set G := Xo.univ.t.G with hGdef
  let G0 : Over (Sp ℂ) := (Over.pullback x).obj G
  let act0 : OAct (𝓞 E) G0 := OAct.pullback x G Xo.univ.t.act
  have w : (pullback.fst G.hom x ≫ ν.φ) ≫ G.hom = pullback.snd G.hom x ≫ x := by
    rw [Category.assoc, ν.cart.1.w, ← Category.assoc, pullback.condition, Category.assoc, hx]
  let α : G0 ⟶ G0 := Over.homMk (pullback.lift (pullback.fst G.hom x ≫ ν.φ) (pullback.snd G.hom x) w)
    (pullback.lift_snd _ _ _)
  have hαf : α.left ≫ pullback.fst G.hom x = pullback.fst G.hom x ≫ ν.φ := pullback.lift_fst _ _ _
  have pA : IsGrpPullback G0 G x (pullback.fst G.hom x) := isGrpPullback_pullback G x
  have c₁ : IsGrpPullback G0 G x (pullback.fst G.hom x ≫ ν.φ) := by
    have c₀ := IsGrpPullback.comp pA ν.cart
    rw [hx] at c₀
    exact c₀
  have hαm : IsMonHom α :=
    ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.isMonHom_of_grpPullback c₁ pA (𝟙 G) α (by simpa using hαf)
  have hact0 : ∀ a, (act0.act a).left ≫ pullback.fst G.hom x = pullback.fst G.hom x ≫ (Xo.univ.t.act.act a).left :=
    fun a => pullback.lift_fst _ _ _
  have hact : ∀ a, act0.act a ≫ α = α ≫ act0.act a := fun a => by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · calc (act0.act a ≫ α).left ≫ pullback.fst G.hom x
          = (act0.act a).left ≫ (α.left ≫ pullback.fst G.hom x) := by rw [Over.comp_left, Category.assoc]
        _ = ((act0.act a).left ≫ pullback.fst G.hom x) ≫ ν.φ := by rw [hαf, Category.assoc]
        _ = pullback.fst G.hom x ≫ ((Xo.univ.t.act.act a).left ≫ ν.φ) := by rw [hact0, Category.assoc]
        _ = pullback.fst G.hom x ≫ (ν.φ ≫ (Xo.univ.t.act.act a).left) :=
          congrArg (pullback.fst G.hom x ≫ ·) (ν.act a)
        _ = (α.left ≫ pullback.fst G.hom x) ≫ (Xo.univ.t.act.act a).left := by rw [hαf, Category.assoc]
        _ = α.left ≫ ((act0.act a).left ≫ pullback.fst G.hom x) := by rw [hact0, Category.assoc]
        _ = (α ≫ act0.act a).left ≫ pullback.fst G.hom x := by rw [Over.comp_left, Category.assoc]
    · have h1 : ∀ f : G0 ⟶ G0, f.left ≫ pullback.snd G.hom x = pullback.snd G.hom x := fun f => Over.w f
      simp only [Over.comp_left, Category.assoc, h1]
  obtain ⟨n, hn, hνn⟩ := GlobalTheory.T.exists_finite_order_levelMove_universalSemiAbelian E H Dw l Xo c «γ» ρ ν hpq hA1 hiso hm'
  have hαn : (fun f => f ≫ α)^[n] (𝟙 G0) = 𝟙 G0 := by
    have key : ∀ j, ((fun f => f ≫ α)^[j] (𝟙 G0)).left ≫ pullback.fst G.hom x =
        pullback.fst G.hom x ≫ (fun f : G.left ⟶ G.left => f ≫ ν.φ)^[j] (𝟙 _) := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Over.comp_left, Category.assoc, hαf,
          ← Category.assoc, ih, Category.assoc]
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · rw [key, hνn, Over.id_left, Category.id_comp, Category.comp_id]
    · have h1 : ∀ f : G0 ⟶ G0, f.left ≫ pullback.snd G.hom x = pullback.snd G.hom x := fun f => Over.w f
      rw [h1]; simp

  have bw : ∀ u : 𝟙_ (Over (Sp ℂ)) ⟶ G0, (u.left ≫ pullback.fst G.hom x) ≫ G.hom = (Over.mk x).hom := fun u => by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    have e : u.left ≫ pullback.snd G.hom x = 𝟙 _ := Over.w u
    rw [e, Category.id_comp]; rfl
  let B : (𝟙_ (Over (Sp ℂ)) ⟶ G0) → (Over.mk x ⟶ G) := fun u => Over.homMk (u.left ≫ pullback.fst G.hom x) (bw u)
  have B_left : ∀ u, (B u).left = u.left ≫ pullback.fst G.hom x := fun u => rfl
  have B_inj : Function.Injective B := fun u v h => by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · exact congrArg (fun z => z.left) h
    · exact (Over.w u).trans (Over.w v).symm
  have B_mul : ∀ u v, B (u * v) = B u * B v := fun u v => by
    apply Over.OverMorphism.ext
    have e1 := pA.2 (𝟙_ _) u v (pushPt pA.1.w u) (pushPt pA.1.w v) rfl rfl
    have e2 := mul_left_congr (Category.id_comp x) (pushPt pA.1.w u) (pushPt pA.1.w v) (B u) (B v) rfl rfl
    exact e1.symm.trans e2
  let Bh : (𝟙_ (Over (Sp ℂ)) ⟶ G0) →* (Over.mk x ⟶ G) := MonoidHom.mk' B B_mul
  have B_act : ∀ u a, B (u ≫ act0.act a) = B u ≫ Xo.univ.t.act.act a := fun u a => by
    apply Over.OverMorphism.ext
    rw [B_left, Over.comp_left, Over.comp_left, B_left, Category.assoc, Category.assoc, hact0]
  have B_α : ∀ u, (B (u ≫ α)).left = (B u).left ≫ ν.φ := fun u => by
    rw [B_left, B_left, Over.comp_left, Category.assoc, hαf, Category.assoc]
  have B_one : B 1 = 1 := map_one Bh

  have tl : (toUnit (Over.mk x)).left = x := by simpa using Over.w (toUnit (Over.mk x))
  let β : KA l →+* ℂ := (algebraMap c.F ℂ).comp (IntermediateField.inclusion c.le).toRingHom
  obtain ⟨-, TI, -, -, hTI⟩ := Xo.univ.geom ℂ x β y.x_over
  let et : Dw.La → (Over.mk x ⟶ G) := fun b => toUnit (Over.mk x) ≫ Xo.univ.eta b
  have et_add : ∀ a b, et (a + b) = et a * et b := fun a b => by
    simp only [et, Xo.univ.eta_add, MonObj.comp_mul]
  have et_ker : ∀ a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La), et a = 1 := fun a ha => by
    simp only [et, Xo.univ.eta_ker a ha, MonObj.comp_one]
  have hadd : ∀ (a b : 𝓞 E) (z : Over.mk x ⟶ G), z ≫ Xo.univ.t.act.act (a + b) =
      (z ≫ Xo.univ.t.act.act a) * (z ≫ Xo.univ.t.act.act b) := fun a b z => by
    rw [Xo.univ.t.act.add, MonObj.comp_mul]
  have hone : ∀ z : Over.mk x ⟶ G, z ≫ Xo.univ.t.act.act 1 = z := fun z => by
    rw [Xo.univ.t.act.one, Category.comp_id]
  have hnat : ∀ (k : ℕ) (z : Over.mk x ⟶ G), z ≫ Xo.univ.t.act.act (k : 𝓞 E) = z ^ k := by
    intro k z
    induction k with
    | zero =>
      have h0 := hadd 0 0 z
      rw [add_zero] at h0
      simpa using h0
    | succ k ih => rw [Nat.cast_succ, hadd, ih, hone, pow_succ]
  obtain ⟨t, ht, htor⟩ := GlobalTheory.T.tateIsometry_torsion_eq_level_smul E H Dw l ℂ (Over.mk x ⟶ G) (fun a z => z ≫ Xo.univ.t.act.act a) _ TI et I g
    hadd hone hnat (fun a ha => hTI a ha) hg hnorm hsq hMb

  have tor_B : ∀ u : 𝟙_ (Over (Sp ℂ)) ⟶ G0, (∀ a ∈ I, u ≫ act0.act a = 1) → ∃ c' : Dw.La, B u = et (t • c') :=
    fun u hu => htor (B u) fun a ha => by rw [← B_act, hu a ha, B_one]
  obtain ⟨hfin, hcard⟩ := GlobalTheory.T.natCard_quot_smul_le_pow_finrank E Dw.La Dw.fin Dw.proj I g hg hnorm
  classical
  haveI : Fintype (Dw.La ⧸ I • (⊤ : Submodule (𝓞 E) Dw.La)) := Fintype.ofFinite _
  let rep := Function.surjInv (Submodule.Quotient.mk_surjective (I • (⊤ : Submodule (𝓞 E) Dw.La)))
  let S' : Finset (Over.mk x ⟶ G) := Finset.univ.image fun q => et (t • rep q)
  have et_t : ∀ c', et (t • c') ∈ S' := fun c' => by
    refine Finset.mem_image.2 ⟨Submodule.Quotient.mk c', Finset.mem_univ _, ?_⟩
    have e : rep (Submodule.Quotient.mk c') - c' ∈ I • (⊤ : Submodule (𝓞 E) Dw.La) :=
      (Submodule.Quotient.eq _).1 (Function.surjInv_eq _ _)
    have e2 := ht _ e
    rw [smul_sub] at e2
    have e3 : et (t • rep (Submodule.Quotient.mk c')) =
        et (t • rep (Submodule.Quotient.mk c') - t • c') * et (t • c') := by
      rw [← et_add, sub_add_cancel]
    rw [e3, et_ker _ e2, _root_.one_mul]
  let T0 : Finset (𝟙_ (Over (Sp ℂ)) ⟶ G0) := S'.preimage B B_inj.injOn
  have hT0 : T0.card ≤ g ^ (Dw.p + Dw.q) := by
    calc T0.card ≤ S'.card :=
          Finset.card_le_card_of_injOn B (fun u hu => Finset.mem_preimage.1 hu) B_inj.injOn
      _ ≤ (Finset.univ : Finset (Dw.La ⧸ I • (⊤ : Submodule (𝓞 E) Dw.La))).card := Finset.card_image_le
      _ = Nat.card (Dw.La ⧸ I • (⊤ : Submodule (𝓞 E) Dw.La)) := by
          rw [Finset.card_univ, Nat.card_eq_fintype_card]
      _ ≤ g ^ (Dw.p + Dw.q) := by rw [← Dw.rank]; exact hcard
  have hmemT : ∀ u : 𝟙_ (Over (Sp ℂ)) ⟶ G0, (∀ a ∈ I, u ≫ act0.act a = 1) → u ∈ T0 := fun u hu => by
    obtain ⟨c', hc'⟩ := tor_B u hu
    exact Finset.mem_preimage.2 (hc' ▸ et_t c')

  obtain ⟨m, hmU⟩ := GlobalTheory.T.isUnipotentModIdeal_liftLa_inv E H Dw l I «γ» hMb hU
  have hδ : ∀ b, et (liftLa «γ» (liftLa «γ»⁻¹ b)) = et b := fun b => by
    have e1 := GlobalTheory.LevelActionLaws.liftLa_mul_sub «γ» «γ»⁻¹ b
    have e2 := GlobalTheory.LevelActionLaws.liftLa_one_sub (D := Dw) (l := l) b
    rw [mul_inv_cancel] at e1
    have e3 : liftLa «γ» (liftLa «γ»⁻¹ b) - b ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) := by
      have e4 := Submodule.sub_mem _ e2 e1
      rwa [sub_sub_sub_cancel_left] at e4
    have e5 : et (liftLa «γ» (liftLa «γ»⁻¹ b)) = et (liftLa «γ» (liftLa «γ»⁻¹ b) - b) * et b := by
      rw [← et_add, sub_add_cancel]
    rw [e5, et_ker _ e3, _root_.one_mul]
  have B_step : ∀ u b, B u = et b → B (u ≫ α) = et (liftLa «γ»⁻¹ b) := fun u b hb => by
    apply Over.OverMorphism.ext
    rw [B_α, hb, ← hδ b]
    show (toUnit (Over.mk x) ≫ Xo.univ.eta (liftLa «γ» (liftLa «γ»⁻¹ b))).left ≫ ν.φ =
      (toUnit (Over.mk x) ≫ Xo.univ.eta (liftLa «γ»⁻¹ b)).left
    rw [Over.comp_left, Over.comp_left, Category.assoc, hm'.2.1, tl, ← Category.assoc, hx]
  let φf : (𝟙_ (Over (Sp ℂ)) ⟶ G0) → (𝟙_ (Over (Sp ℂ)) ⟶ G0) := fun z => (z ≫ α) * z⁻¹
  have B_iter : ∀ j u b, B u = et b → B (φf^[j] u) = et (((liftLa «γ»⁻¹ - 1) ^ j) b) := by
    intro j
    induction j with
    | zero => intro u b hb; simpa using hb
    | succ j ih =>
      intro u b hb
      rw [Function.iterate_succ_apply']
      have h1 := ih u b hb
      set b' := ((liftLa «γ»⁻¹ - 1) ^ j) b
      show Bh ((φf^[j] u ≫ α) * (φf^[j] u)⁻¹) = _
      rw [map_mul, map_inv]
      show B (φf^[j] u ≫ α) * (B (φf^[j] u))⁻¹ = _
      rw [B_step _ _ h1, h1, pow_succ', Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply]
      rw [eq_comm, eq_mul_inv_iff_mul_eq, ← et_add, sub_add_cancel]
  have hunip : ∀ u : 𝟙_ (Over (Sp ℂ)) ⟶ G0, (∀ a ∈ I, u ≫ act0.act a = 1) →
      (fun z : 𝟙_ (Over (Sp ℂ)) ⟶ G0 => (z ≫ α) * z⁻¹)^[m] u = 1 := fun u hu => by
    obtain ⟨c', hc'⟩ := tor_B u hu
    apply B_inj
    rw [B_iter m u _ hc', B_one, map_smul]
    exact et_ker _ (ht _ (hmU c'))
  have hαid : α = 𝟙 G0 := GlobalTheory.T.exists_small_torsion_set_for_endomorphism E ℂ G0 act0 α n m g (Dw.p + Dw.q) I
    (IsSemiAbelian.pullback x G Xo.univ.t.semi) hαm hact hn hαn hg hnorm hsq hr ⟨T0, hT0, hmemT⟩ hunip

  have hαl : α.left = 𝟙 _ := by rw [hαid]; rfl
  have fix : ∀ s : Over.mk x ⟶ G, s.left ≫ ν.φ = s.left := fun s => by
    have hs : s.left ≫ G.hom = 𝟙 (Sp ℂ) ≫ x := by rw [Category.id_comp]; exact Over.w s
    have e0 : pullback.lift s.left (𝟙 _) hs ≫ pullback.fst G.hom x = s.left := pullback.lift_fst _ _ _
    rw [← e0, Category.assoc, ← hαf, hαl, Category.id_comp]
  have heq : ∀ a, liftLa «γ» a - a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) := fun a => by
    refine GlobalTheory.LevelFree.eta_injective Xo x β y.x_over _ ?_
    have e1 : et (liftLa «γ» a) = et a := by
      apply Over.OverMorphism.ext
      rw [← fix (et (liftLa «γ» a))]
      show (toUnit (Over.mk x) ≫ Xo.univ.eta (liftLa «γ» a)).left ≫ ν.φ =
        (toUnit (Over.mk x) ≫ Xo.univ.eta a).left
      rw [Over.comp_left, Over.comp_left, Category.assoc, hm'.2.1, tl, ← Category.assoc, hx]
    have e2 : et (liftLa «γ» a) = et (liftLa «γ» a - a) * et a := by rw [← et_add, sub_add_cancel]
    rw [e1] at e2
    exact mul_eq_right.1 e2.symm
  refine LinearEquiv.ext fun q => ?_
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  have e := liftLa_spec «γ» a
  simp only [Submodule.mkQ_apply] at e
  change «γ» (Submodule.Quotient.mk a) = Submodule.Quotient.mk a
  rw [← e]
  exact (Submodule.Quotient.eq _).2 (heq a)

end GlobalTheory.UnipFree
