import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaOK
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInclusionCyclotomicAwayRingFiniteEtale
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaObjectEighthPowerPrincipalSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionCommutatorPairingConstHolomorphicFamilyAn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilIsDiagRoot
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingDiagonalPullbackEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinProductRelationAlgebraicClauses
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinProductMkPointBasicFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieModelIsBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open GlobalTheory.CechPic GlobalTheory.AbDual

noncomputable section

namespace GlobalTheory.ZarhinWeil

/- English proof (translation)
The claim follows from `map_mul (Units.map _) u v`.
-/
theorem unitOn_mul'' {k : Type} [CommRing k] (u v : kˣ) : unitOn (u * v) = unitOn u * unitOn v := map_mul (Units.map _) u v
/- English proof (translation)
The claim follows from `map_inv (Units.map _) u`.
-/
theorem unitOn_inv'' {k : Type} [CommRing k] (u : kˣ) : unitOn u⁻¹ = (unitOn u)⁻¹ := map_inv (Units.map _) u
/- English proof (translation)
The claim follows from `map_one (Units.map _)`.
-/
theorem unitOn_one'' {k : Type} [CommRing k] : unitOn (1 : kˣ) = 1 := map_one (Units.map _)
/- English proof (translation)
The claim follows from `map_pow (Units.map _) u n`.
-/
theorem unitOn_pow'' {k : Type} [CommRing k] (u : kˣ) (n : ℕ) : unitOn (u ^ n) = unitOn u ^ n := map_pow (Units.map _) u n

/- English proof (translation)
Introduce `h M₁ Bt _ ζ S s c n T a b e he`. Establish `hG` using `GlobalTheory.globalFns_holds`. Establish `hAA : IsAbelianScheme (G2 c.A)` using `AbelianSchemeGerms.isAbelianScheme_tensor _ _ c.ab c.ab`. Establish `hcls : GlobalTheory.CechPic.cls c.P c.isLB = GlobalTheory.CechPic.pull (lift (snd c.A c.A) (fst c.A c.A)).left (GlobalTheory.CechPic.cls c.P c.isLB)`. Rewrite using `[← GlobalTheory.CechPic.cls_pull c.isLB _ (pull_isLB c.isLB _)]`.

Conclude with `(GlobalTheory.CechPic.cls_eq_iff _ _).2 c.symm`. Use `GlobalTheory.SiegelPower.weilIs_of_cls hG hAA c.isLB c.isLB (lift (snd c.A c.A) (fst c.A c.A)) hcls ?_` and prove the remaining obligations. Use `GlobalTheory.CommPairing.weilIs_symm c.isLB he` as an intermediate fact. Simplify using `using this`.
-/
theorem weilIs_axes_swap : ∀ (h M₁ : ℕ) {Bt : Type} [CommRing Bt] (ζ : Bt) (S : Scheme.{0}) (s : S ⟶ Sp Bt) (c : SiegPre h M₁ ζ s) (n : ℤ) (T : Over S) (a b : T ⟶ c.A) (e : (Γ(T.left, ⊤))ˣ), Out.WeilIs (G2 c.A) c.P n (lift a 1) (lift 1 b) e → Out.WeilIs (G2 c.A) c.P n (lift b 1) (lift 1 a) e⁻¹ := by
  intro h M₁ Bt _ ζ S s c n T a b e he
  have hG := GlobalTheory.globalFns_holds
  have hAA : IsAbelianScheme (G2 c.A) := AbelianSchemeGerms.isAbelianScheme_tensor _ _ c.ab c.ab
  have hcls : GlobalTheory.CechPic.cls c.P c.isLB =
      GlobalTheory.CechPic.pull (lift (snd c.A c.A) (fst c.A c.A)).left (GlobalTheory.CechPic.cls c.P c.isLB) := by
    rw [← GlobalTheory.CechPic.cls_pull c.isLB _ (pull_isLB c.isLB _)]
    exact (GlobalTheory.CechPic.cls_eq_iff _ _).2 c.symm
  refine GlobalTheory.SiegelPower.weilIs_of_cls hG hAA c.isLB c.isLB (lift (snd c.A c.A) (fst c.A c.A)) hcls ?_
  have := GlobalTheory.CommPairing.weilIs_symm c.isLB he
  simpa using this

/- English proof (translation)
Introduce `h M₁ Bt _ ζ S s c n T a b a' b' ha hb ha' hb' e₁ e₂ h1 h2`. Establish `hG` using `GlobalTheory.globalFns_holds`. Establish `hA` using `c.ab`. Establish `hAA : IsAbelianScheme (G2 c.A)` using `AbelianSchemeGerms.isAbelianScheme_tensor _ _ hA hA`. Establish `axis : ∀ (ψ : c.A ⟶ G2 c.A) [IsMonHom ψ], (∃ t : (c.P.pull ψ.left).Gen, t.IsGen) → ∀ u u' : T ⟶ c.A, u ^ n = 1 → u' ^ n = 1 → Out.WeilIs (G2 c.A) c.P n (u ≫ ψ) (u' ≫ ψ) 1`.

Introduce `ψ _ ht u u' hu hu'`. Establish `hL` using `pull_isLB c.isLB ψ.left`. Establish `pu : (u ≫ ψ) ^ n = 1` using `by rw [← GlobalTheory.SS.FrobTorsion.pow_comp', hu]; simp`. Establish `pu' : (u' ≫ ψ) ^ n = 1` using `by rw [← GlobalTheory.SS.FrobTorsion.pow_comp', hu']; simp`. Take `⟨f, -, hf⟩` from `GlobalTheory.HolTorsionAny.exists_weilIs_pow_eq_one hAA c.isLB pu pu'`.

Establish `hf'` using `GlobalTheory.SiegelPower.weilIs_of_cls hG hA hL c.isLB ψ (GlobalTheory.CechPic.cls_pull c.isLB _ _) hf`. Take `⟨t, ht⟩` from `ht`. Establish `one` using `GlobalTheory.DiagSqAxes.weilIs_one_of_gen hA hL t ht hu hu'`. Rewrite `hf` using `[GlobalTheory.CommutatorPairing.weilIs_unique hG hA hL hf' one]`. Then use the resulting hypothesis. Establish `e11 : Out.WeilIs (G2 c.A) c.P n (lift a 1) (lift a' 1) 1`.

Use `axis (lift (𝟙 c.A) (1 : c.A ⟶ c.A)) c.rig₂ a a' ha ha'` as an intermediate fact. Simplify `this` using `only [comp_lift, Category.comp_id, MonObj.comp_one]`. Establish `e22 : Out.WeilIs (G2 c.A) c.P n (lift 1 b) (lift 1 b') 1`. Use `axis (lift (1 : c.A ⟶ c.A) (𝟙 c.A)) c.rig₁ b b' hb hb'` as an intermediate fact. Simplify `this` using `only [comp_lift, Category.comp_id, MonObj.comp_one]`.

Establish `sA` using `GlobalTheory.DiagPairing.weilIs_mul_left hG hAA c.isLB (GlobalTheory.CommPairing.weilIs_symm c.isLB e11) (GlobalTheory.CommPairing.weilIs_symm c.isLB h1)`. Establish `sB` using `GlobalTheory.DiagPairing.weilIs_mul_left hG hAA c.isLB h2 (GlobalTheory.CommPairing.weilIs_symm c.isLB e22)`. Establish `r` using `GlobalTheory.DiagPairing.weilIs_mul_left hG hAA c.isLB (GlobalTheory.CommPairing.weilIs_symm c.isLB sA) (GlobalTheory.CommPairing.weilIs_symm c.isLB sB)`. Rewrite `r` using `[GlobalTheory.DiagSqAxes.lift_mul_lift₂, GlobalTheory.DiagSqAxes.lift_mul_lift₂]`. Simplify using `only [_root_.mul_one, _root_.one_mul, inv_one, _root_.mul_inv, inv_inv] at r`.

Conclude with `r`.
-/
theorem weilIs_decomp : ∀ (h M₁ : ℕ) {Bt : Type} [CommRing Bt] (ζ : Bt) (S : Scheme.{0}) (s : S ⟶ Sp Bt) (c : SiegPre h M₁ ζ s) (n : ℕ) (T : Over S) (a b a' b' : T ⟶ c.A), a ^ n = 1 → b ^ n = 1 → a' ^ n = 1 → b' ^ n = 1 → ∀ e₁ e₂ : (Γ(T.left, ⊤))ˣ, Out.WeilIs (G2 c.A) c.P n (lift a 1) (lift 1 b') e₁ → Out.WeilIs (G2 c.A) c.P n (lift a' 1) (lift 1 b) e₂ → Out.WeilIs (G2 c.A) c.P n (lift a b) (lift a' b') (e₁ * e₂⁻¹) := by
  intro h M₁ Bt _ ζ S s c n T a b a' b' ha hb ha' hb' e₁ e₂ h1 h2
  have hG := GlobalTheory.globalFns_holds
  have hA := c.ab
  have hAA : IsAbelianScheme (G2 c.A) := AbelianSchemeGerms.isAbelianScheme_tensor _ _ hA hA
  have axis : ∀ (ψ : c.A ⟶ G2 c.A) [IsMonHom ψ], (∃ t : (c.P.pull ψ.left).Gen, t.IsGen) →
      ∀ u u' : T ⟶ c.A, u ^ n = 1 → u' ^ n = 1 → Out.WeilIs (G2 c.A) c.P n (u ≫ ψ) (u' ≫ ψ) 1 := by
    intro ψ _ ht u u' hu hu'
    have hL := pull_isLB c.isLB ψ.left
    have pu : (u ≫ ψ) ^ n = 1 := by rw [← GlobalTheory.SS.FrobTorsion.pow_comp', hu]; simp
    have pu' : (u' ≫ ψ) ^ n = 1 := by rw [← GlobalTheory.SS.FrobTorsion.pow_comp', hu']; simp
    obtain ⟨f, -, hf⟩ := GlobalTheory.HolTorsionAny.exists_weilIs_pow_eq_one hAA c.isLB pu pu'
    have hf' := GlobalTheory.SiegelPower.weilIs_of_cls hG hA hL c.isLB ψ (GlobalTheory.CechPic.cls_pull c.isLB _ _) hf
    obtain ⟨t, ht⟩ := ht
    have one := GlobalTheory.DiagSqAxes.weilIs_one_of_gen hA hL t ht hu hu'
    rwa [GlobalTheory.CommutatorPairing.weilIs_unique hG hA hL hf' one] at hf
  have e11 : Out.WeilIs (G2 c.A) c.P n (lift a 1) (lift a' 1) 1 := by
    have := axis (lift (𝟙 c.A) (1 : c.A ⟶ c.A)) c.rig₂ a a' ha ha'
    simpa only [comp_lift, Category.comp_id, MonObj.comp_one] using this
  have e22 : Out.WeilIs (G2 c.A) c.P n (lift 1 b) (lift 1 b') 1 := by
    have := axis (lift (1 : c.A ⟶ c.A) (𝟙 c.A)) c.rig₁ b b' hb hb'
    simpa only [comp_lift, Category.comp_id, MonObj.comp_one] using this
  have sA := GlobalTheory.DiagPairing.weilIs_mul_left hG hAA c.isLB (GlobalTheory.CommPairing.weilIs_symm c.isLB e11)
    (GlobalTheory.CommPairing.weilIs_symm c.isLB h1)
  have sB := GlobalTheory.DiagPairing.weilIs_mul_left hG hAA c.isLB h2 (GlobalTheory.CommPairing.weilIs_symm c.isLB e22)
  have r := GlobalTheory.DiagPairing.weilIs_mul_left hG hAA c.isLB (GlobalTheory.CommPairing.weilIs_symm c.isLB sA)
    (GlobalTheory.CommPairing.weilIs_symm c.isLB sB)
  rw [GlobalTheory.DiagSqAxes.lift_mul_lift₂, GlobalTheory.DiagSqAxes.lift_mul_lift₂] at r
  simp only [_root_.mul_one, _root_.one_mul, inv_one, _root_.mul_inv, inv_inv] at r
  exact r

/- English proof (translation)
Use `CartesianMonoidalCategory.hom_ext _ _ ?_ ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.SS.FrobTorsion.pow_comp', lift_fst, hu]`. Simplify using the standard rewrite rules. Rewrite using `[GlobalTheory.SS.FrobTorsion.pow_comp', lift_snd, hv]`. Simplify using the standard rewrite rules.
-/
theorem lift_pow_eq_one {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] {T : Over S} (u : T ⟶ A) (v : T ⟶ B)
    (n : ℕ) (hu : u ^ n = 1) (hv : v ^ n = 1) : lift u v ^ n = 1 := by
  refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
  · rw [GlobalTheory.SS.FrobTorsion.pow_comp', lift_fst, hu]
    simp
  · rw [GlobalTheory.SS.FrobTorsion.pow_comp', lift_snd, hv]
    simp

/- English proof (translation)
Introduce `h M S t c hMo k _ _ x β z hxt hz p q`. Establish `hA` using `c.ab`. Establish `hAA : IsAbelianScheme (G2 c.A)` using `AbelianSchemeGerms.isAbelianScheme_tensor _ _ hA hA`. Establish `tA : ∀ p, (toUnit (Over.mk x) ≫ c.lev p) ^ M = 1` using `fun p => by`. Rewrite using `[← GlobalTheory.SymLiftOdd.comp_pow', c.lev_tors]`.

Simplify using the standard rewrite rules. Take `⟨E, hEM, hE⟩` from `GlobalTheory.HolTorsionAny.exists_weilIs_pow_eq_one hAA c.isLB (lift_pow_eq_one _ _ M (tA p) (one_pow M)) (lift_pow_eq_one _ _ M (one_pow M) (tA q))`. Establish `h2` using `weilIs_axes_swap h M (zetaAway M) S t c M (Over.mk x) _ _ E hE`. Establish `h3` using `weilIs_decomp h M (zetaAway M) S t c M (Over.mk x) _ _ _ _ (tA p) (tA p) (tA q) (tA q) E E⁻¹ hE h2`. Establish `hg` using `(c.geom k x β z hxt hz).2.2 p q`.

Establish `hsq` using `GlobalTheory.DiagPull.weilIs_diag_eq S c.A c.P hA c.isLB M (Over.mk x) _ _ _ _ h3 hg`. Rewrite `hsq` using `[inv_inv]`. Establish `hzM : z ^ M = 1`. Use `ext`. Rewrite using `[Units.val_pow_eq_pow_val, hz, ← map_pow, zetaAway_pow_self hMo.pos.ne', map_one, Units.val_one]`.

Take `⟨m, hm⟩` from `hMo`. Establish `root : ∀ v : (Γ((Over.mk x).left, ⊤))ˣ, v ^ M = 1 → v = (v * v) ^ (m + 1)` using `fun v hv => by`. Rewrite using `[← sq, ← pow_mul, show 2 * (m + 1) = M + 1 by omega, pow_succ, hv, _root_.one_mul]`. Establish `hu : (unitOn (z ^ omegaStd p q)) ^ M = 1`. Rewrite using `[← unitOn_pow'', ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hzM, one_zpow, unitOn_one'']`.

Establish `key : E = unitOn (z ^ omegaStd p q)`. Rewrite using `[root E hEM, root _ hu, hsq, ← unitOn_mul'', ← zpow_add, two_mul]`. Rewrite using `[← key]`. Conclude with `hE`.
-/
theorem weilIs_axes_lev : ∀ (h M : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t), Odd M →
    ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (β : cycAway M →+* k) (z : kˣ), x ≫ t = spMap β →
    (z : k) = β (zetaAway M) → ∀ p q : Fin h ⊕ Fin h → ℤ,
    Out.WeilIs (G2 c.A) c.P M (lift (toUnit (Over.mk x) ≫ c.lev p) 1) (lift 1 (toUnit (Over.mk x) ≫ c.lev q))
      (unitOn (z ^ omegaStd p q)) := by
  intro h M S t c hMo k _ _ x β z hxt hz p q
  have hA := c.ab
  have hAA : IsAbelianScheme (G2 c.A) := AbelianSchemeGerms.isAbelianScheme_tensor _ _ hA hA
  have tA : ∀ p, (toUnit (Over.mk x) ≫ c.lev p) ^ M = 1 := fun p => by
    rw [← GlobalTheory.SymLiftOdd.comp_pow', c.lev_tors]
    simp
  obtain ⟨E, hEM, hE⟩ := GlobalTheory.HolTorsionAny.exists_weilIs_pow_eq_one hAA c.isLB
    (lift_pow_eq_one _ _ M (tA p) (one_pow M)) (lift_pow_eq_one _ _ M (one_pow M) (tA q))
  have h2 := weilIs_axes_swap h M (zetaAway M) S t c M (Over.mk x) _ _ E hE
  have h3 := weilIs_decomp h M (zetaAway M) S t c M (Over.mk x) _ _ _ _ (tA p) (tA p) (tA q) (tA q) E E⁻¹ hE h2
  have hg := (c.geom k x β z hxt hz).2.2 p q
  have hsq := GlobalTheory.DiagPull.weilIs_diag_eq S c.A c.P hA c.isLB M (Over.mk x) _ _ _ _ h3 hg
  rw [inv_inv] at hsq
  have hzM : z ^ M = 1 := by
    ext
    rw [Units.val_pow_eq_pow_val, hz, ← map_pow, zetaAway_pow_self hMo.pos.ne', map_one, Units.val_one]
  obtain ⟨m, hm⟩ := hMo
  have root : ∀ v : (Γ((Over.mk x).left, ⊤))ˣ, v ^ M = 1 → v = (v * v) ^ (m + 1) := fun v hv => by
    rw [← sq, ← pow_mul, show 2 * (m + 1) = M + 1 by omega, pow_succ, hv, _root_.one_mul]
  have hu : (unitOn (z ^ omegaStd p q)) ^ M = 1 := by
    rw [← unitOn_pow'', ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hzM, one_zpow, unitOn_one'']
  have key : E = unitOn (z ^ omegaStd p q) := by
    rw [root E hEM, root _ hu, hsq, ← unitOn_mul'', ← zpow_add, two_mul]
  rw [← key]
  exact hE

/- English proof (translation)
Introduce `h M d S t c B _ _ Q la mu hZ hMo k _ _ x β z hxt hz p q p' q'`. Establish `hG` using `GlobalTheory.globalFns_holds`. Establish `hA` using `c.ab`. Establish `hB : IsAbelianScheme B` using `hZ.1`. Establish `hAA : IsAbelianScheme (G2 c.A)` using `AbelianSchemeGerms.isAbelianScheme_tensor _ _ hA hA`.

Establish `hAB : IsAbelianScheme (c.A ⊗ B)` using `AbelianSchemeGerms.isAbelianScheme_tensor _ _ hA hB`. Establish `hQ : Q.IsLB` using `hZ.2.1.isLB`. Use `haveI : IsMonHom la := hZ.2.2.2.1`. Establish `tA : ∀ p, (toUnit (Over.mk x) ≫ c.lev p) ^ M = 1` using `fun p => by`. Rewrite using `[← GlobalTheory.SymLiftOdd.comp_pow', c.lev_tors]`.

Simplify using the standard rewrite rules. Establish `tB : ∀ p, (toUnit (Over.mk x) ≫ c.lev p ≫ la) ^ M = 1` using `fun p => by`. Rewrite using `[← Category.assoc, ← GlobalTheory.SS.FrobTorsion.pow_comp', tA]`. Simplify using the standard rewrite rules. Take `⟨e, -, he⟩` from `GlobalTheory.HolTorsionAny.exists_weilIs_pow_eq_one hAB hQ (lift_pow_eq_one _ _ M (tA p) (tB q)) (lift_pow_eq_one _ _ M (tA p') (tB q'))`.

Set `ψ : G2 c.A ⟶ c.A ⊗ B` to `lift (fst c.A c.A) (snd c.A c.A ≫ la)`. Establish `hcls : GlobalTheory.CechPic.cls c.P c.isLB = GlobalTheory.CechPic.pull ψ.left (GlobalTheory.CechPic.cls Q hQ)`. Rewrite using `[← GlobalTheory.CechPic.cls_pull hQ ψ.left (pull_isLB hQ _)]`. Conclude with `(GlobalTheory.CechPic.cls_eq_iff _ _).2 hZ.2.2.2.2.2.2.2`. Establish `hψ : ∀ u v : Over.mk x ⟶ c.A, lift u v ≫ ψ = lift u (v ≫ la)` using `fun u v => by`.

Simplify using `[ψ]`. Establish `hP : Out.WeilIs (G2 c.A) c.P M (lift (toUnit (Over.mk x) ≫ c.lev p) (toUnit (Over.mk x) ≫ c.lev q)) (lift (toUnit (Over.mk x) ≫ c.lev p') (toUnit (Over.mk x) ≫ c.lev q')) e`. Use `GlobalTheory.SiegelPower.weilIs_of_cls hG hAA c.isLB hQ ψ hcls ?_` and prove the remaining obligations. Rewrite using `[hψ, hψ]`. Simplify `he` using `only [Category.assoc]`.

Establish `hv` using `weilIs_decomp h M (zetaAway M) S t c M (Over.mk x) _ _ _ _ (tA p) (tA q) (tA p') (tA q') _ _ (weilIs_axes_lev h M S t c ⟨hMo.choose, hMo.choose_spec⟩ k x β z hxt hz p q') (weilIs_axes_lev h M S t c ⟨hMo.choose, hMo.choose_spec⟩ k x β z hxt hz p' q)`. Establish `hu` using `GlobalTheory.CommutatorPairing.weilIs_unique hG hAA c.isLB hP hv`. Establish `anti : omegaStd q p' = - omegaStd p' q`. Unfold `omegaStd`. Rewrite using `[← Finset.sum_neg_distrib]`.

Conclude with `Finset.sum_congr rfl fun i _ => by ring`. Establish `hval : unitOn (z ^ (omegaStd p q' + omegaStd q p')) = unitOn (z ^ omegaStd p q') * (unitOn (z ^ omegaStd p' q))⁻¹`. Rewrite using `[anti, ← sub_eq_add_neg, zpow_sub, unitOn_mul'', unitOn_inv'']`. Rewrite using `[hval, ← hu]`. Conclude with `he`.
-/
theorem weilIs_poincare_lev : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), Odd M → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (β : cycAway M →+* k) (z : kˣ), x ≫ t = spMap β → (z : k) = β (zetaAway M) → ∀ p q p' q' : Fin h ⊕ Fin h → ℤ, Out.WeilIs (c.A ⊗ B) Q M (lift (toUnit (Over.mk x) ≫ c.lev p) (toUnit (Over.mk x) ≫ c.lev q ≫ la)) (lift (toUnit (Over.mk x) ≫ c.lev p') (toUnit (Over.mk x) ≫ c.lev q' ≫ la)) (unitOn (z ^ (omegaStd p q' + omegaStd q p'))) := by
  intro h M d S t c B _ _ Q la mu hZ hMo k _ _ x β z hxt hz p q p' q'
  have hG := GlobalTheory.globalFns_holds
  have hA := c.ab
  have hB : IsAbelianScheme B := hZ.1
  have hAA : IsAbelianScheme (G2 c.A) := AbelianSchemeGerms.isAbelianScheme_tensor _ _ hA hA
  have hAB : IsAbelianScheme (c.A ⊗ B) := AbelianSchemeGerms.isAbelianScheme_tensor _ _ hA hB
  have hQ : Q.IsLB := hZ.2.1.isLB
  haveI : IsMonHom la := hZ.2.2.2.1
  have tA : ∀ p, (toUnit (Over.mk x) ≫ c.lev p) ^ M = 1 := fun p => by
    rw [← GlobalTheory.SymLiftOdd.comp_pow', c.lev_tors]
    simp
  have tB : ∀ p, (toUnit (Over.mk x) ≫ c.lev p ≫ la) ^ M = 1 := fun p => by
    rw [← Category.assoc, ← GlobalTheory.SS.FrobTorsion.pow_comp', tA]
    simp
  obtain ⟨e, -, he⟩ := GlobalTheory.HolTorsionAny.exists_weilIs_pow_eq_one hAB hQ
    (lift_pow_eq_one _ _ M (tA p) (tB q)) (lift_pow_eq_one _ _ M (tA p') (tB q'))
  let ψ : G2 c.A ⟶ c.A ⊗ B := lift (fst c.A c.A) (snd c.A c.A ≫ la)
  have hcls : GlobalTheory.CechPic.cls c.P c.isLB = GlobalTheory.CechPic.pull ψ.left (GlobalTheory.CechPic.cls Q hQ) := by
    rw [← GlobalTheory.CechPic.cls_pull hQ ψ.left (pull_isLB hQ _)]
    exact (GlobalTheory.CechPic.cls_eq_iff _ _).2 hZ.2.2.2.2.2.2.2
  have hψ : ∀ u v : Over.mk x ⟶ c.A, lift u v ≫ ψ = lift u (v ≫ la) := fun u v => by
    simp [ψ]
  have hP : Out.WeilIs (G2 c.A) c.P M (lift (toUnit (Over.mk x) ≫ c.lev p) (toUnit (Over.mk x) ≫ c.lev q))
      (lift (toUnit (Over.mk x) ≫ c.lev p') (toUnit (Over.mk x) ≫ c.lev q')) e := by
    refine GlobalTheory.SiegelPower.weilIs_of_cls hG hAA c.isLB hQ ψ hcls ?_
    rw [hψ, hψ]
    simpa only [Category.assoc] using he
  have hv := weilIs_decomp h M (zetaAway M) S t c M (Over.mk x) _ _ _ _ (tA p) (tA q) (tA p') (tA q') _ _
    (weilIs_axes_lev h M S t c ⟨hMo.choose, hMo.choose_spec⟩ k x β z hxt hz p q')
    (weilIs_axes_lev h M S t c ⟨hMo.choose, hMo.choose_spec⟩ k x β z hxt hz p' q)
  have hu := GlobalTheory.CommutatorPairing.weilIs_unique hG hAA c.isLB hP hv
  have anti : omegaStd q p' = - omegaStd p' q := by
    unfold omegaStd
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hval : unitOn (z ^ (omegaStd p q' + omegaStd q p')) =
      unitOn (z ^ omegaStd p q') * (unitOn (z ^ omegaStd p' q))⁻¹ := by
    rw [anti, ← sub_eq_add_neg, zpow_sub, unitOn_mul'', unitOn_inv'']
  rw [hval, ← hu]
  exact he

/- English proof (translation)
Introduce `h M d S t c B _ _ Q la mu hZ hL`. Establish `hQ : Q.IsLB` using `hZ.2.1.isLB`. Establish `hP : GlobalTheory.CechPic.cls c.P c.isLB = GlobalTheory.CechPic.pull (lift (fst c.A c.A) (snd c.A c.A ≫ la)).left (GlobalTheory.CechPic.cls Q hQ)`. Rewrite using `[← GlobalTheory.CechPic.cls_pull hQ _ (pull_isLB hQ _)]`. Conclude with `(GlobalTheory.CechPic.cls_eq_iff _ _).2 hZ.2.2.2.2.2.2.2`.

Rewrite using `[GlobalTheory.CechPic.cls_pull (GlobalTheory.ZarhinFam.zarhinBundle_isLineBundle c.A B c.isLB hQ d mu) _ hL, GlobalTheory.ZarhinFam.cls_zP]`. Unfold `GlobalTheory.ZarhinFam.zCls`. Rewrite using `[hP]`. Simplify using `only [map_add, map_sum, map_zsmul, ← GlobalTheory.CechPic.pull_comp, ← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc, Category.id_comp, lift_fst, lift_snd, Category.assoc]`. Simplify using `only [mul_smul, two_smul, Finset.sum_add_distrib]`.

Normalize the expressions using the abelian group laws.
-/
theorem cls_diag_zP : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu) (hL : ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (𝟙 (GlobalTheory.ZarhinFam.Zob c.A B)) (𝟙 (GlobalTheory.ZarhinFam.Zob c.A B))).left).IsLB), GlobalTheory.CechPic.cls _ hL = (∑ i, GlobalTheory.CechPic.pull (lift (GlobalTheory.ZarhinFam.pa c.A B i) (GlobalTheory.ZarhinFam.pa c.A B i ≫ la)).left (GlobalTheory.CechPic.cls Q hZ.2.1.isLB)) + (∑ i, ∑ j, (2 * GlobalTheory.ZarhinFam.quat d j i) • GlobalTheory.CechPic.pull (lift (GlobalTheory.ZarhinFam.pa c.A B i) (GlobalTheory.ZarhinFam.pb c.A B j)).left (GlobalTheory.CechPic.cls Q hZ.2.1.isLB)) + ∑ j, GlobalTheory.CechPic.pull (lift (GlobalTheory.ZarhinFam.pb c.A B j ≫ mu) (GlobalTheory.ZarhinFam.pb c.A B j)).left (GlobalTheory.CechPic.cls Q hZ.2.1.isLB) := by
  intro h M d S t c B _ _ Q la mu hZ hL
  have hQ : Q.IsLB := hZ.2.1.isLB
  have hP : GlobalTheory.CechPic.cls c.P c.isLB =
      GlobalTheory.CechPic.pull (lift (fst c.A c.A) (snd c.A c.A ≫ la)).left (GlobalTheory.CechPic.cls Q hQ) := by
    rw [← GlobalTheory.CechPic.cls_pull hQ _ (pull_isLB hQ _)]
    exact (GlobalTheory.CechPic.cls_eq_iff _ _).2 hZ.2.2.2.2.2.2.2
  rw [GlobalTheory.CechPic.cls_pull (GlobalTheory.ZarhinFam.zarhinBundle_isLineBundle c.A B c.isLB hQ d mu) _ hL, GlobalTheory.ZarhinFam.cls_zP]
  unfold GlobalTheory.ZarhinFam.zCls
  rw [hP]
  simp only [map_add, map_sum, map_zsmul, ← GlobalTheory.CechPic.pull_comp, ← Over.comp_left, comp_lift, lift_fst_assoc,
    lift_snd_assoc, Category.id_comp, lift_fst, lift_snd, Category.assoc]
  simp only [mul_smul, two_smul, Finset.sum_add_distrib]
  abel

/- English proof (translation)
Unfold `omegaStd`. Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => by simp only [Pi.smul_apply, nsmul_eq_mul]; ring`.
-/
theorem omegaStd_nsmul_left {h : ℕ} (n : ℕ) (x y : Fin h ⊕ Fin h → ℤ) :
    omegaStd (n • x) y = n * omegaStd x y := by
  unfold omegaStd
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by simp only [Pi.smul_apply, nsmul_eq_mul]; ring

/- English proof (translation)
Unfold `omegaStd`. Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => by simp only [Pi.smul_apply, nsmul_eq_mul]; ring`.
-/
theorem omegaStd_nsmul_right {h : ℕ} (n : ℕ) (x y : Fin h ⊕ Fin h → ℤ) :
    omegaStd x (n • y) = n * omegaStd x y := by
  unfold omegaStd
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by simp only [Pi.smul_apply, nsmul_eq_mul]; ring

/- English proof (translation)
Introduce `d h a b`. Establish `hs : ∀ F : Fin 8 → ℤ, ∑ k, F k = ∑ i : Fin 4, F (Fin.castAdd 4 i) + ∑ j : Fin 4, F (Fin.natAdd 4 j)` using `fun F => Fin.sum_univ_add (a := 4) (b := 4) F`. Establish `sl : ∀ i : Fin 4, GlobalTheory.ZarhinFam.sig (Fin.castAdd 4 i) = Sum.inl i`. Apply the tactic sequence `intro i; fin_cases i <;> rfl`. Establish `sr : ∀ j : Fin 4, GlobalTheory.ZarhinFam.sig (Fin.natAdd 4 j) = Sum.inr j`.

Apply the tactic sequence `intro j; fin_cases j <;> rfl`. Unfold `GlobalTheory.ZarhinFam.formZ`. Simplify using `only [hs, sl, sr, omegaStd_nsmul_left, omegaStd_nsmul_right, GlobalTheory.ZarhinFam.form, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.smul_apply, Matrix.one_apply, Matrix.transpose_apply]`. Simplify using `[Finset.sum_add_distrib, Finset.mul_sum, mul_add]`. Establish `hc : ∑ x : Fin 4, ∑ x_1 : Fin 4, 2 * GlobalTheory.ZarhinFam.quat d x_1 x * omegaStd (a (x_1.addNat 4)) (b (Fin.castAdd 4 x)) = ∑ x : Fin 4, ∑ i : Fin 4, 2 * (GlobalTheory.ZarhinFam.quat d x i * omegaStd (a (x.addNat 4)) (b (Fin.castAdd 4 i)))`.

Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`. Rewrite using `[hc]`. Establish `h2 : ∀ x y : ℤ, 2 * x * y = 2 * (x * y)` using `fun x y => by ring`. Simplify using `only [h2, mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem two_formZ : ∀ (d h : ℕ) (a b : Fin 8 → (Fin h ⊕ Fin h → ℤ)), 2 * GlobalTheory.ZarhinFam.formZ d h a b = (∑ i : Fin 4, (omegaStd (a (Fin.castAdd 4 i)) (b (Fin.castAdd 4 i)) + omegaStd (a (Fin.castAdd 4 i)) (b (Fin.castAdd 4 i)))) + (∑ i : Fin 4, ∑ j : Fin 4, 2 * GlobalTheory.ZarhinFam.quat d j i * (omegaStd (a (Fin.castAdd 4 i)) (b (Fin.natAdd 4 j)) + omegaStd (a (Fin.natAdd 4 j)) (b (Fin.castAdd 4 i)))) + ∑ j : Fin 4, (omegaStd (d • a (Fin.natAdd 4 j)) (b (Fin.natAdd 4 j)) + omegaStd (a (Fin.natAdd 4 j)) (d • b (Fin.natAdd 4 j))) := by
  intro d h a b
  have hs : ∀ F : Fin 8 → ℤ, ∑ k, F k = ∑ i : Fin 4, F (Fin.castAdd 4 i) + ∑ j : Fin 4, F (Fin.natAdd 4 j) :=
    fun F => Fin.sum_univ_add (a := 4) (b := 4) F
  have sl : ∀ i : Fin 4, GlobalTheory.ZarhinFam.sig (Fin.castAdd 4 i) = Sum.inl i := by
    intro i; fin_cases i <;> rfl
  have sr : ∀ j : Fin 4, GlobalTheory.ZarhinFam.sig (Fin.natAdd 4 j) = Sum.inr j := by
    intro j; fin_cases j <;> rfl
  unfold GlobalTheory.ZarhinFam.formZ
  simp only [hs, sl, sr, omegaStd_nsmul_left, omegaStd_nsmul_right, GlobalTheory.ZarhinFam.form, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.smul_apply,
    Matrix.one_apply, Matrix.transpose_apply]
  simp [Finset.sum_add_distrib, Finset.mul_sum, mul_add]
  have hc : ∑ x : Fin 4, ∑ x_1 : Fin 4, 2 * GlobalTheory.ZarhinFam.quat d x_1 x *
        omegaStd (a (x_1.addNat 4)) (b (Fin.castAdd 4 x)) =
      ∑ x : Fin 4, ∑ i : Fin 4, 2 * (GlobalTheory.ZarhinFam.quat d x i * omegaStd (a (x.addNat 4)) (b (Fin.castAdd 4 i))) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [hc]
  have h2 : ∀ x y : ℤ, 2 * x * y = 2 * (x * y) := fun x y => by ring
  simp only [h2, mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Establish `e` using `c.lev_add 0 0`. Rewrite `e` using `[add_zero]`. Rewrite using `[zero_smul, pow_zero]`.

Conclude with `mul_eq_left.1 e.symm`. Consider the case `succ n ih => rw [succ_nsmul, c.lev_add, ih, pow_succ]`.
-/
theorem lev_nsmul {h M₁ : ℕ} {Bt : Type} [CommRing Bt] {ζ : Bt} {S : Scheme.{0}} {s : S ⟶ Sp Bt}
    (c : SiegPre h M₁ ζ s) (n : ℕ) (q : Fin h ⊕ Fin h → ℤ) : c.lev (n • q) = c.lev q ^ n := by
  induction n with
  | zero =>
    have e := c.lev_add 0 0
    rw [add_zero] at e
    rw [zero_smul, pow_zero]
    exact mul_eq_left.1 e.symm
  | succ n ih => rw [succ_nsmul, c.lev_add, ih, pow_succ]

/- English proof (translation)
Introduce `h M d S t c B _ _ Q la mu hZ _ _ hMo _ _ _ _ k _ _ x β z hxt hz a b`. Establish `hG` using `GlobalTheory.globalFns_holds`. Establish `hA : IsAbelianScheme c.A` using `c.ab`. Establish `hB : IsAbelianScheme B` using `hZ.1`. Establish `hZab : IsAbelianScheme (GlobalTheory.ZarhinFam.Zob c.A B)` using `AbelianSchemeGerms.isAbelianScheme_tensor _ _ (AbelianSchemeGerms.isAbelianScheme_powObj c.A hA 3) (AbelianSchemeGerms.isAbelianScheme_powObj B hB 3)`.

Establish `hQ : Q.IsLB` using `hZ.2.1.isLB`. Use `haveI : IsMonHom la := hZ.2.2.2.1`. Use `haveI : IsMonHom mu := hZ.2.2.2.2.1`. Establish `hL` using `pull_isLB (GlobalTheory.ZarhinFam.zarhinBundle_isLineBundle c.A B c.isLB hQ d mu) (lift (𝟙 (GlobalTheory.ZarhinFam.Zob c.A B)) (𝟙 (GlobalTheory.ZarhinFam.Zob c.A B))).left`. Establish `tA : ∀ p, (toUnit (Over.mk x) ≫ c.lev p) ^ M = 1` using `fun p => by`.

Rewrite using `[← GlobalTheory.SymLiftOdd.comp_pow', c.lev_tors]`. Simplify using the standard rewrite rules. Establish `tB : ∀ p, (toUnit (Over.mk x) ≫ c.lev p ≫ la) ^ M = 1` using `fun p => by`. Rewrite using `[← Category.assoc, ← GlobalTheory.SS.FrobTorsion.pow_comp', tA]`. Simplify using the standard rewrite rules.

Establish `tw : ∀ a : Fin 8 → (Fin h ⊕ Fin h → ℤ), GlobalTheory.ZarhinFam.mkZ c.A B (fun i => toUnit (Over.mk x) ≫ c.lev (a (Fin.castAdd 4 i))) (fun j => toUnit (Over.mk x) ≫ c.lev (a (Fin.natAdd 4 j)) ≫ la) ^ M = 1` using `fun a => by`. Rewrite using `[(GlobalTheory.ZarhinFam.PtFacts.mkZ_facts c.A B (𝟙 _) _ _ 1 M).2.1, (GlobalTheory.ZarhinFam.PtFacts.mkZ_facts c.A B (𝟙 _) _ _ 1 M).2.2.1]`. Conclude with `⟨fun i => tA _, fun j => tB _⟩`. Take `⟨e, -, he⟩` from `GlobalTheory.HolTorsionAny.exists_weilIs_pow_eq_one hZab hL (tw a) (tw b)`. Establish `hmu : ∀ q, toUnit (Over.mk x) ≫ c.lev q ≫ la ≫ mu = toUnit (Over.mk x) ≫ c.lev (d • q)` using `fun q => by`.

Rewrite using `[hZ.2.2.2.2.2.1, lev_nsmul, GlobalTheory.SymLiftOdd.comp_pow', Category.comp_id]`. Set `f : Fin 4 ⊕ (Fin 4 × Fin 4) ⊕ Fin 4 → (GlobalTheory.ZarhinFam.Zob c.A B ⟶ c.A ⊗ B)` to `Sum.elim (fun i => lift (GlobalTheory.ZarhinFam.pa c.A B i) (GlobalTheory.ZarhinFam.pa c.A B i ≫ la)) (Sum.elim (fun ij => lift (GlobalTheory.ZarhinFam.pa c.A B ij.1) (GlobalTheory.ZarhinFam.pb c.A B ij.2)) (fun j => lift (GlobalTheory.ZarhinFam.pb c.A B j ≫ mu) (GlobalTheory.Zar …`. Set `ε : Fin 4 ⊕ (Fin 4 × Fin 4) ⊕ Fin 4 → ℤ` to `Sum.elim (fun _ => 1) (Sum.elim (fun ij => 2 * GlobalTheory.ZarhinFam.quat d ij.2 ij.1) (fun _ => 1))`. Set `g : Fin 4 ⊕ (Fin 4 × Fin 4) ⊕ Fin 4 → ℤ` to `Sum.elim (fun i => omegaStd (a (Fin.castAdd 4 i)) (b (Fin.castAdd 4 i)) + omegaStd (a (Fin.castAdd 4 i)) (b (Fin.castAdd 4 i))) (Sum.elim (fun ij => omegaStd (a (Fin.castAdd 4 ij.1)) (b (Fin.natAdd 4 ij.2)) + omegaStd (a (Fin.natAdd 4 ij.2)) (b (Fin.castAdd 4 ij.1))) (fun j => om …`. Establish `hf : ∀ i, IsMonHom (f i)`.

Apply the tactic sequence `rintro (i | ij | j) <;> simp only [f, Sum.elim_inl, Sum.elim_inr] <;> infer_instance`. Establish `e₁ : (1 : ℤ) • GlobalTheory.CechPic.cls _ hL = ∑ i, ε i • GlobalTheory.CechPic.pull (f i).left (GlobalTheory.CechPic.cls Q hQ)`. Rewrite using `[one_smul, cls_diag_zP h M d S t c B Q la mu hZ hL]`. Simplify using `only [Fintype.sum_sum_type, Fintype.sum_prod_type, f, ε, Sum.elim_inl, Sum.elim_inr, one_smul, add_assoc]`. Establish `hd : ∀ i, Out.WeilIs (c.A ⊗ B) Q M (GlobalTheory.ZarhinFam.mkZ c.A B (fun i => toUnit (Over.mk x) ≫ c.lev (a (Fin.castAdd 4 i))) (fun j => toUnit (Over.mk x) ≫ c.lev (a (Fin.natAdd 4 j)) ≫ la) ≫ f i) (GlobalTheory.ZarhinFam.mkZ c.A B (fun i => toUnit (Over.mk x) ≫ c.lev (b (Fin.c …`.

Establish `q` using `weilIs_poincare_lev h M d S t c B Q la mu hZ hMo k x β z hxt hz`. Introduce and unpack `(i | ⟨i, j⟩ | j)`. Simplify using `only [f, g, Sum.elim_inl, comp_lift, GlobalTheory.ZarhinFam.RelAlg.mkZ_pa, GlobalTheory.ZarhinFam.RelAlg.mkZ_pb, ← Category.assoc]`. Simplify `q (a (Fin.castAdd 4 i)) (a (Fin.castAdd 4 i)) (b (Fin.castAdd 4 i)) (b (Fin.castAdd 4 i))` using `only [Category.assoc]`. Simplify using `only [f, g, Sum.elim_inl, Sum.elim_inr, comp_lift, GlobalTheory.ZarhinFam.RelAlg.mkZ_pa, GlobalTheory.ZarhinFam.RelAlg.mkZ_pb]`.

Conclude with `q (a (Fin.castAdd 4 i)) (a (Fin.natAdd 4 j)) (b (Fin.castAdd 4 i)) (b (Fin.natAdd 4 j))`. Simplify using `only [f, g, Sum.elim_inr, comp_lift, ← Category.assoc (GlobalTheory.ZarhinFam.mkZ _ _ _ _), GlobalTheory.ZarhinFam.RelAlg.mkZ_pa, GlobalTheory.ZarhinFam.RelAlg.mkZ_pb, Category.assoc, hmu]`. Conclude with `q (d • a (Fin.natAdd 4 j)) (a (Fin.natAdd 4 j)) (d • b (Fin.natAdd 4 j)) (b (Fin.natAdd 4 j))`. Establish `hp` using `GlobalTheory.SiegelPower.pow_eq_prod hG hZab hL hQ f hf ε 1 e₁ he hd`. Establish `key : ∑ i, g i * ε i = 2 * GlobalTheory.ZarhinFam.formZ d h a b`.

Rewrite using `[two_formZ d h a b]`. Simplify using `only [Fintype.sum_sum_type, Fintype.sum_prod_type, g, ε, Sum.elim_inl, Sum.elim_inr, _root_.mul_one]`. Rewrite using `[← add_assoc]`. Use `congrArg₂ (· + ·) (congrArg₂ (· + ·) rfl ?_) rfl` and prove the remaining obligations. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring`.

Establish `he' : e = unitOn (z ^ (2 * GlobalTheory.ZarhinFam.formZ d h a b))`. Rewrite using `[← zpow_one e, hp, ← key, DVR.zpow_fsum]`. Unfold `unitOn`. Rewrite using `[map_prod]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations.

Simplify using `only [zpow_mul, map_zpow]`. Rewrite using `[← he']`. Conclude with `he`.
-/
theorem weilIs_formZ : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (β : cycAway M →+* k) (z : kˣ), x ≫ t = spMap β → (z : k) = β (zetaAway M) → ∀ a b : Fin 8 → (Fin h ⊕ Fin h → ℤ), Out.WeilIs (GlobalTheory.ZarhinFam.Zob c.A B) ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (𝟙 (GlobalTheory.ZarhinFam.Zob c.A B)) (𝟙 (GlobalTheory.ZarhinFam.Zob c.A B))).left) M (GlobalTheory.ZarhinFam.mkZ c.A B (fun i => toUnit (Over.mk x) ≫ c.lev (a (Fin.castAdd 4 i))) (fun j => toUnit (Over.mk x) ≫ c.lev (a (Fin.natAdd 4 j)) ≫ la)) (GlobalTheory.ZarhinFam.mkZ c.A B (fun i => toUnit (Over.mk x) ≫ c.lev (b (Fin.castAdd 4 i))) (fun j => toUnit (Over.mk x) ≫ c.lev (b (Fin.natAdd 4 j)) ≫ la)) (unitOn (z ^ (2 * GlobalTheory.ZarhinFam.formZ d h a b))) := by
  intro h M d S t c B _ _ Q la mu hZ _ _ hMo _ _ _ _ k _ _ x β z hxt hz a b
  have hG := GlobalTheory.globalFns_holds
  have hA : IsAbelianScheme c.A := c.ab
  have hB : IsAbelianScheme B := hZ.1
  have hZab : IsAbelianScheme (GlobalTheory.ZarhinFam.Zob c.A B) :=
    AbelianSchemeGerms.isAbelianScheme_tensor _ _ (AbelianSchemeGerms.isAbelianScheme_powObj c.A hA 3)
      (AbelianSchemeGerms.isAbelianScheme_powObj B hB 3)
  have hQ : Q.IsLB := hZ.2.1.isLB
  haveI : IsMonHom la := hZ.2.2.2.1
  haveI : IsMonHom mu := hZ.2.2.2.2.1
  have hL := pull_isLB (GlobalTheory.ZarhinFam.zarhinBundle_isLineBundle c.A B c.isLB hQ d mu)
    (lift (𝟙 (GlobalTheory.ZarhinFam.Zob c.A B)) (𝟙 (GlobalTheory.ZarhinFam.Zob c.A B))).left
  have tA : ∀ p, (toUnit (Over.mk x) ≫ c.lev p) ^ M = 1 := fun p => by
    rw [← GlobalTheory.SymLiftOdd.comp_pow', c.lev_tors]
    simp
  have tB : ∀ p, (toUnit (Over.mk x) ≫ c.lev p ≫ la) ^ M = 1 := fun p => by
    rw [← Category.assoc, ← GlobalTheory.SS.FrobTorsion.pow_comp', tA]
    simp
  have tw : ∀ a : Fin 8 → (Fin h ⊕ Fin h → ℤ),
      GlobalTheory.ZarhinFam.mkZ c.A B (fun i => toUnit (Over.mk x) ≫ c.lev (a (Fin.castAdd 4 i)))
        (fun j => toUnit (Over.mk x) ≫ c.lev (a (Fin.natAdd 4 j)) ≫ la) ^ M = 1 := fun a => by
    rw [(GlobalTheory.ZarhinFam.PtFacts.mkZ_facts c.A B (𝟙 _) _ _ 1 M).2.1,
      (GlobalTheory.ZarhinFam.PtFacts.mkZ_facts c.A B (𝟙 _) _ _ 1 M).2.2.1]
    exact ⟨fun i => tA _, fun j => tB _⟩
  obtain ⟨e, -, he⟩ := GlobalTheory.HolTorsionAny.exists_weilIs_pow_eq_one hZab hL (tw a) (tw b)
  have hmu : ∀ q, toUnit (Over.mk x) ≫ c.lev q ≫ la ≫ mu = toUnit (Over.mk x) ≫ c.lev (d • q) := fun q => by
    rw [hZ.2.2.2.2.2.1, lev_nsmul, GlobalTheory.SymLiftOdd.comp_pow', Category.comp_id]
  let f : Fin 4 ⊕ (Fin 4 × Fin 4) ⊕ Fin 4 → (GlobalTheory.ZarhinFam.Zob c.A B ⟶ c.A ⊗ B) :=
    Sum.elim (fun i => lift (GlobalTheory.ZarhinFam.pa c.A B i) (GlobalTheory.ZarhinFam.pa c.A B i ≫ la))
      (Sum.elim (fun ij => lift (GlobalTheory.ZarhinFam.pa c.A B ij.1) (GlobalTheory.ZarhinFam.pb c.A B ij.2))
        (fun j => lift (GlobalTheory.ZarhinFam.pb c.A B j ≫ mu) (GlobalTheory.ZarhinFam.pb c.A B j)))
  let ε : Fin 4 ⊕ (Fin 4 × Fin 4) ⊕ Fin 4 → ℤ :=
    Sum.elim (fun _ => 1) (Sum.elim (fun ij => 2 * GlobalTheory.ZarhinFam.quat d ij.2 ij.1) (fun _ => 1))
  let g : Fin 4 ⊕ (Fin 4 × Fin 4) ⊕ Fin 4 → ℤ :=
    Sum.elim (fun i => omegaStd (a (Fin.castAdd 4 i)) (b (Fin.castAdd 4 i)) +
        omegaStd (a (Fin.castAdd 4 i)) (b (Fin.castAdd 4 i)))
      (Sum.elim (fun ij => omegaStd (a (Fin.castAdd 4 ij.1)) (b (Fin.natAdd 4 ij.2)) +
          omegaStd (a (Fin.natAdd 4 ij.2)) (b (Fin.castAdd 4 ij.1)))
        (fun j => omegaStd (d • a (Fin.natAdd 4 j)) (b (Fin.natAdd 4 j)) +
          omegaStd (a (Fin.natAdd 4 j)) (d • b (Fin.natAdd 4 j))))
  have hf : ∀ i, IsMonHom (f i) := by
    rintro (i | ij | j) <;> simp only [f, Sum.elim_inl, Sum.elim_inr] <;> infer_instance
  have e₁ : (1 : ℤ) • GlobalTheory.CechPic.cls _ hL = ∑ i, ε i • GlobalTheory.CechPic.pull (f i).left (GlobalTheory.CechPic.cls Q hQ) := by
    rw [one_smul, cls_diag_zP h M d S t c B Q la mu hZ hL]
    simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, f, ε, Sum.elim_inl, Sum.elim_inr, one_smul, add_assoc]
  have hd : ∀ i, Out.WeilIs (c.A ⊗ B) Q M
      (GlobalTheory.ZarhinFam.mkZ c.A B (fun i => toUnit (Over.mk x) ≫ c.lev (a (Fin.castAdd 4 i)))
        (fun j => toUnit (Over.mk x) ≫ c.lev (a (Fin.natAdd 4 j)) ≫ la) ≫ f i)
      (GlobalTheory.ZarhinFam.mkZ c.A B (fun i => toUnit (Over.mk x) ≫ c.lev (b (Fin.castAdd 4 i)))
        (fun j => toUnit (Over.mk x) ≫ c.lev (b (Fin.natAdd 4 j)) ≫ la) ≫ f i) (unitOn (z ^ g i)) := by
    have q := weilIs_poincare_lev h M d S t c B Q la mu hZ hMo k x β z hxt hz
    rintro (i | ⟨i, j⟩ | j)
    · simp only [f, g, Sum.elim_inl, comp_lift, GlobalTheory.ZarhinFam.RelAlg.mkZ_pa, GlobalTheory.ZarhinFam.RelAlg.mkZ_pb,
        ← Category.assoc]
      simpa only [Category.assoc] using q (a (Fin.castAdd 4 i)) (a (Fin.castAdd 4 i)) (b (Fin.castAdd 4 i))
        (b (Fin.castAdd 4 i))
    · simp only [f, g, Sum.elim_inl, Sum.elim_inr, comp_lift, GlobalTheory.ZarhinFam.RelAlg.mkZ_pa,
        GlobalTheory.ZarhinFam.RelAlg.mkZ_pb]
      exact q (a (Fin.castAdd 4 i)) (a (Fin.natAdd 4 j)) (b (Fin.castAdd 4 i)) (b (Fin.natAdd 4 j))
    · simp only [f, g, Sum.elim_inr, comp_lift, ← Category.assoc (GlobalTheory.ZarhinFam.mkZ _ _ _ _),
        GlobalTheory.ZarhinFam.RelAlg.mkZ_pa, GlobalTheory.ZarhinFam.RelAlg.mkZ_pb, Category.assoc, hmu]
      exact q (d • a (Fin.natAdd 4 j)) (a (Fin.natAdd 4 j)) (d • b (Fin.natAdd 4 j)) (b (Fin.natAdd 4 j))
  have hp := GlobalTheory.SiegelPower.pow_eq_prod hG hZab hL hQ f hf ε 1 e₁ he hd
  have key : ∑ i, g i * ε i = 2 * GlobalTheory.ZarhinFam.formZ d h a b := by
    rw [two_formZ d h a b]
    simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, g, ε, Sum.elim_inl, Sum.elim_inr, _root_.mul_one]
    rw [← add_assoc]
    refine congrArg₂ (· + ·) (congrArg₂ (· + ·) rfl ?_) rfl
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have he' : e = unitOn (z ^ (2 * GlobalTheory.ZarhinFam.formZ d h a b)) := by
    rw [← zpow_one e, hp, ← key, DVR.zpow_fsum]
    unfold unitOn
    rw [map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [zpow_mul, map_zpow]
  rw [← he']
  exact he

end GlobalTheory.ZarhinWeil
