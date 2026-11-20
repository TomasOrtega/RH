import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerZeroTangentTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupLiftTangentPhiLinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupLiftTangentPhiAdditive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionDualNumberPointEqConstantCharZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoTangentPullConstantDeformation
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EndoConstantFamilyDualNumbersEqBaseChange
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsConstKOfLocDerK
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGlobalLocDerOfIsCob
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ConstThickeningFieldStructure
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional

set_option autoImplicit false

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.InteriorKS

/- English proof (translation)
Establish `h : ∀ p : PrimeSpectrum (DualNumber K), p.asIdeal = IsLocalRing.maximalIdeal (DualNumber K)`. Introduce `p`. Use `le_antisymm (IsLocalRing.le_maximalIdeal p.isPrime.ne_top) fun x hx => ?_` and prove the remaining obligations. Establish `hn : IsNilpotent x`. Rewrite using `[TrivSqZeroExt.isNilpotent_iff_isNilpotent_fst]`.

Establish `: ¬ IsUnit x.fst` using `fun hu => hx (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 hu)`. Establish `h0 : x.fst = 0` using `by simpa using this`. Rewrite using `[h0]`. Conclude with `IsNilpotent.zero`. Take `⟨n, hn⟩` from `hn`.

Conclude with `p.isPrime.mem_of_pow_mem n (hn ▸ p.asIdeal.zero_mem)`. Conclude with `⟨fun p q => PrimeSpectrum.ext ((h p).trans (h q).symm)⟩`.
-/
theorem subsingleton_sp_dualNumber (K : Type) [Field K] : Subsingleton (Sp (DualNumber K)) := by
  have h : ∀ p : PrimeSpectrum (DualNumber K),
      p.asIdeal = IsLocalRing.maximalIdeal (DualNumber K) := by
    intro p
    refine le_antisymm (IsLocalRing.le_maximalIdeal p.isPrime.ne_top) fun x hx => ?_
    have hn : IsNilpotent x := by
      rw [TrivSqZeroExt.isNilpotent_iff_isNilpotent_fst]
      have : ¬ IsUnit x.fst := fun hu => hx (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 hu)
      have h0 : x.fst = 0 := by simpa using this
      rw [h0]; exact IsNilpotent.zero
    obtain ⟨n, hn⟩ := hn
    exact p.isPrime.mem_of_pow_mem n (hn ▸ p.asIdeal.zero_mem)
  exact ⟨fun p q => PrimeSpectrum.ext ((h p).trans (h q).symm)⟩

/- English proof (translation)
Establish `hL : Out.Laws` using `GlobalTheory.abelianSchemeLaws_all.1`. Use `haveI := subsingleton_sp_dualNumber K`. Set `c : A' ⟶ G'` to `a * b⁻¹`. Set `j' : Over.mk (j ≫ A'.hom) ⟶ A'` to `Over.homMk j rfl`. Establish `h1 : j' ≫ a = j' ≫ b` using `Over.OverMorphism.ext hab`.

Establish `h2 : j' ≫ c = 1`. Simplify using `only [c, MonObj.comp_mul, GrpObj.comp_inv, h1, mul_inv_cancel]`. Establish `h3 : η[A'] ≫ c = 1`. Simplify using `only [c, MonObj.comp_mul, GrpObj.comp_inv, hη, mul_inv_cancel]`. Take `⟨t₀⟩ : Nonempty (Sp K)` from `inferInstance`.

Set `t : Sp (DualNumber K)` to `spMap (TrivSqZeroExt.fstHom K K K).toRingHom t₀`. Establish `hc : ∀ x : A'.left, c.left x = (η[G'] : 𝟙_ (Over (Sp (DualNumber K))) ⟶ G').left t`. Introduce `x`. Take `⟨z, rfl, -⟩` from `Scheme.exists_preimage_of_isPullback hj x t₀ (Subsingleton.elim _ _)`. Establish `e : j ≫ c.left = (j' ≫ c).left` using `rfl`.

Rewrite using `[← Scheme.Hom.comp_apply, e, h2, Hom.one_def, Over.comp_left]`. Use `(Scheme.Hom.comp_apply _ _ _).trans ?_` and prove the remaining obligations. Use `congr 1`. Conclude with `Subsingleton.elim (α := Sp (DualNumber K)) _ _`. Establish `hη' : (η[A'] : 𝟙_ (Over (Sp (DualNumber K))) ⟶ A').left ≫ A'.hom = 𝟙 _` using `Over.w η[A']`.

Establish `key` using `GlobalTheory.DualRigidity.eq_comp_section_of_const A'.hom _ c.left hη' (hL.globalFns _ A' hA).2 _ hc`. Establish `key' : c = toUnit A' ≫ η[A'] ≫ c` using `Over.OverMorphism.ext key`. Rewrite `key'` using `[h3, MonObj.comp_one]`. Conclude with `mul_inv_eq_one.1 key'`.
-/
theorem rigidity_dualNumber {K : Type} [Field K] (A₀ : Over (Sp K)) (A' G' : Over (Sp (DualNumber K))) [GrpObj A']
    [GrpObj G'] (j : A₀.left ⟶ A'.left) (a b : A' ⟶ G') (hA : IsAbelianScheme A')
    (hj : IsPullback j A₀.hom A'.hom (spMap (TrivSqZeroExt.fstHom K K K).toRingHom))
    (hab : j ≫ a.left = j ≫ b.left) (hη : η[A'] ≫ a = η[A'] ≫ b) : a = b := by
  have hL : Out.Laws := GlobalTheory.abelianSchemeLaws_all.1
  haveI := subsingleton_sp_dualNumber K
  let c : A' ⟶ G' := a * b⁻¹
  let j' : Over.mk (j ≫ A'.hom) ⟶ A' := Over.homMk j rfl
  have h1 : j' ≫ a = j' ≫ b := Over.OverMorphism.ext hab
  have h2 : j' ≫ c = 1 := by
    simp only [c, MonObj.comp_mul, GrpObj.comp_inv, h1, mul_inv_cancel]
  have h3 : η[A'] ≫ c = 1 := by
    simp only [c, MonObj.comp_mul, GrpObj.comp_inv, hη, mul_inv_cancel]
  obtain ⟨t₀⟩ : Nonempty (Sp K) := inferInstance
  let t : Sp (DualNumber K) := spMap (TrivSqZeroExt.fstHom K K K).toRingHom t₀
  have hc : ∀ x : A'.left, c.left x = (η[G'] : 𝟙_ (Over (Sp (DualNumber K))) ⟶ G').left t := by
    intro x
    obtain ⟨z, rfl, -⟩ := Scheme.exists_preimage_of_isPullback hj x t₀ (Subsingleton.elim _ _)
    have e : j ≫ c.left = (j' ≫ c).left := rfl
    rw [← Scheme.Hom.comp_apply, e, h2, Hom.one_def, Over.comp_left]
    refine (Scheme.Hom.comp_apply _ _ _).trans ?_
    congr 1
    exact Subsingleton.elim (α := Sp (DualNumber K)) _ _
  have hη' : (η[A'] : 𝟙_ (Over (Sp (DualNumber K))) ⟶ A').left ≫ A'.hom = 𝟙 _ := Over.w η[A']
  have key := GlobalTheory.DualRigidity.eq_comp_section_of_const A'.hom _ c.left hη' (hL.globalFns _ A' hA).2 _ hc
  have key' : c = toUnit A' ≫ η[A'] ≫ c := Over.OverMorphism.ext key
  rw [h3, MonObj.comp_one] at key'
  exact mul_inv_eq_one.1 key'

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {K : Type} [Field K] {x₀ : Sp K ⟶ Xo.X} {x' : Sp (DualNumber K) ⟶ Xo.X}
  {A : Over (Sp K)} [GrpObj A] {A' : Over (Sp (DualNumber K))} [GrpObj A'] {π : A.left ⟶ Xo.univ.t.G.left}
  {π' : A'.left ⟶ Xo.univ.t.G.left} {i : A.left ⟶ A'.left} {q : A'.left ⟶ A.left}

/- English proof (translation)
Use `haveI := Xo.univ.t.act.hom a`. Establish `wβ : (π ≫ (Xo.univ.t.act.act a).left) ≫ Xo.univ.t.G.hom = A.hom ≫ x₀`. Rewrite using `[Category.assoc, Over.w (Xo.univ.t.act.act a), hπ.1.w]`. Set `β : A ⟶ A` to `Over.homMk (hπ.1.lift _ A.hom wβ) (hπ.1.lift_snd _ _ _)`. Establish `hβ : β.left ≫ π = π ≫ (Xo.univ.t.act.act a).left` using `hπ.1.lift_fst _ _ _`.

Use `haveI : IsMonHom β := GlobalTheory.UU.isMonHom_of_over_isMonHom hπ hπ (Xo.univ.t.act.act a) β hβ`. Establish `wα : (π' ≫ (Xo.univ.t.act.act a).left) ≫ Xo.univ.t.G.hom = A'.hom ≫ x'`. Rewrite using `[Category.assoc, Over.w (Xo.univ.t.act.act a), hπ'.1.w]`. Set `α : A' ⟶ A'` to `Over.homMk (hπ'.1.lift _ A'.hom wα) (hπ'.1.lift_snd _ _ _)`. Establish `hα : α.left ≫ π' = π' ≫ (Xo.univ.t.act.act a).left` using `hπ'.1.lift_fst _ _ _`.

Use `haveI : IsMonHom α := GlobalTheory.UU.isMonHom_of_over_isMonHom hπ' hπ' (Xo.univ.t.act.act a) α hα`. Establish `wδ : (q ≫ β.left) ≫ A.hom = A'.hom ≫ spMap (algebraMap K (DualNumber K))`. Rewrite using `[Category.assoc, Over.w β, hq.1.w]`. Set `δ : A' ⟶ A'` to `Over.homMk (hq.1.lift _ A'.hom wδ) (hq.1.lift_snd _ _ _)`. Establish `hδ : δ.left ≫ q = q ≫ β.left` using `hq.1.lift_fst _ _ _`.

Use `haveI : IsMonHom δ := GlobalTheory.UU.isMonHom_of_over_isMonHom hq hq β δ hδ`. Establish `hA'` using `PolPull.isAbelianScheme_of_isGrpPullback (ObjDim.isAbelianScheme Xo.univ) hπ'`. Establish `e1 : i ≫ α.left = β.left ≫ i`. Apply `hπ'.1.hom_ext` to reduce the goal to its premises. Simplify using `only [Category.assoc]`.

Rewrite using `[hα, reassoc_of% hiπ, hiπ, hβ]`. Simplify using `only [Category.assoc]`. Rewrite using `[Over.w α, hi.1.w, reassoc_of% (Over.w β)]`. Establish `e2 : i ≫ δ.left = β.left ≫ i`. Apply `hq.1.hom_ext` to reduce the goal to its premises.

Simplify using `only [Category.assoc]`. Rewrite using `[hδ, reassoc_of% hiq, hiq, Category.comp_id]`. Simplify using `only [Category.assoc]`. Rewrite using `[Over.w δ, hi.1.w, reassoc_of% (Over.w β)]`. Establish `hαδ : α = δ` using `rigidity_dualNumber A A' A' i α δ hA' hi.1 (e1.trans e2.symm) (by rw [IsMonHom.one_hom, IsMonHom.one_hom])`.

Establish `hga : (o.t.act.act a).left ≫ g = g ≫ α.left`. Apply `hπ'.1.hom_ext` to reduce the goal to its premises. Simplify using `only [Category.assoc]`. Rewrite using `[hα, hg, reassoc_of% hg]`. Conclude with `m.act a`.

Simplify using `only [Category.assoc]`. Rewrite using `[hgw, Over.w α, hgw, Over.w (o.t.act.act a)]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem act_const (hi : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) (hπ : IsGrpPullback A Xo.univ.t.G x₀ π)
    (hπ' : IsGrpPullback A' Xo.univ.t.G x' π') (hiπ : i ≫ π' = π) (hiq : i ≫ q = 𝟙 _)
    (hq : IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q)
    (o : Obj Dw l (baseKA l) (x' ≫ Xo.s)) (m : ObjMap o Xo.univ x') (g : o.t.G.left ⟶ A'.left)
    (hg : g ≫ π' = m.cm.F) (hgw : g ≫ A'.hom = o.t.G.hom) (a : 𝓞 E) :
    (o.t.act.act a).left ≫ (g ≫ q ≫ π) = (g ≫ q ≫ π) ≫ (Xo.univ.t.act.act a).left := by
  haveI := Xo.univ.t.act.hom a
  have wβ : (π ≫ (Xo.univ.t.act.act a).left) ≫ Xo.univ.t.G.hom = A.hom ≫ x₀ := by
    rw [Category.assoc, Over.w (Xo.univ.t.act.act a), hπ.1.w]
  let β : A ⟶ A := Over.homMk (hπ.1.lift _ A.hom wβ) (hπ.1.lift_snd _ _ _)
  have hβ : β.left ≫ π = π ≫ (Xo.univ.t.act.act a).left := hπ.1.lift_fst _ _ _
  haveI : IsMonHom β := GlobalTheory.UU.isMonHom_of_over_isMonHom hπ hπ (Xo.univ.t.act.act a) β hβ
  have wα : (π' ≫ (Xo.univ.t.act.act a).left) ≫ Xo.univ.t.G.hom = A'.hom ≫ x' := by
    rw [Category.assoc, Over.w (Xo.univ.t.act.act a), hπ'.1.w]
  let α : A' ⟶ A' := Over.homMk (hπ'.1.lift _ A'.hom wα) (hπ'.1.lift_snd _ _ _)
  have hα : α.left ≫ π' = π' ≫ (Xo.univ.t.act.act a).left := hπ'.1.lift_fst _ _ _
  haveI : IsMonHom α := GlobalTheory.UU.isMonHom_of_over_isMonHom hπ' hπ' (Xo.univ.t.act.act a) α hα
  have wδ : (q ≫ β.left) ≫ A.hom = A'.hom ≫ spMap (algebraMap K (DualNumber K)) := by
    rw [Category.assoc, Over.w β, hq.1.w]
  let δ : A' ⟶ A' := Over.homMk (hq.1.lift _ A'.hom wδ) (hq.1.lift_snd _ _ _)
  have hδ : δ.left ≫ q = q ≫ β.left := hq.1.lift_fst _ _ _
  haveI : IsMonHom δ := GlobalTheory.UU.isMonHom_of_over_isMonHom hq hq β δ hδ
  have hA' := PolPull.isAbelianScheme_of_isGrpPullback (ObjDim.isAbelianScheme Xo.univ) hπ'
  have e1 : i ≫ α.left = β.left ≫ i := by
    apply hπ'.1.hom_ext
    · simp only [Category.assoc]
      rw [hα, reassoc_of% hiπ, hiπ, hβ]
    · simp only [Category.assoc]
      rw [Over.w α, hi.1.w, reassoc_of% (Over.w β)]
  have e2 : i ≫ δ.left = β.left ≫ i := by
    apply hq.1.hom_ext
    · simp only [Category.assoc]
      rw [hδ, reassoc_of% hiq, hiq, Category.comp_id]
    · simp only [Category.assoc]
      rw [Over.w δ, hi.1.w, reassoc_of% (Over.w β)]
  have hαδ : α = δ := rigidity_dualNumber A A' A' i α δ hA' hi.1 (e1.trans e2.symm)
    (by rw [IsMonHom.one_hom, IsMonHom.one_hom])
  have hga : (o.t.act.act a).left ≫ g = g ≫ α.left := by
    apply hπ'.1.hom_ext
    · simp only [Category.assoc]
      rw [hα, hg, reassoc_of% hg]
      exact m.act a
    · simp only [Category.assoc]
      rw [hgw, Over.w α, hgw, Over.w (o.t.act.act a)]
  calc (o.t.act.act a).left ≫ (g ≫ q ≫ π) = g ≫ α.left ≫ q ≫ π := by rw [reassoc_of% hga]
    _ = g ≫ q ≫ π ≫ (Xo.univ.t.act.act a).left := by rw [hαδ, reassoc_of% hδ, hβ]
    _ = (g ≫ q ≫ π) ≫ (Xo.univ.t.act.act a).left := by simp only [Category.assoc]

/- English proof (translation)
Use `haveI : IsProper o.t.G.hom := o.proper`. Establish `hA : IsAbelianScheme o.t.G` using `AbelianSchemeGerms.isAbelianScheme_of_proper o.t.G o.t.semi`. Use `GlobalTheory.TripleModel.isPullCubical_of_lbIso GlobalTheory.SemiRigid.globalFns hA hF o.t.cub Xo.univ.t.cub ?_` and prove the remaining obligations. Take `⟨w, -, hw, -⟩` from `rigIso_congr rfl m.cm m.lin rfl rfl`. Establish `K2 : LBIso (Xo.univ.t.PP.L.pull π') (Xo.univ.t.PP.L.pull (q ≫ π))` using `GlobalTheory.TangentConstLB.lbIso_tangent_const E H Dw l Xo c K x₀ x' A A' π π' i q hi hπ hπ' hiπ hiq hq`.

Establish `hM` using `Xo.univ.t.PP.isLB`. Establish `h1 : LBIso o.t.PP.L (Xo.univ.t.PP.L.pull (g ≫ π'))` using `hg1 ▸ ⟨w, hw⟩`. Establish `h2 : LBIso ((Xo.univ.t.PP.L.pull π').pull g) (Xo.univ.t.PP.L.pull (g ≫ q ≫ π))` using `GlobalTheory.Ex.GenericFibre.lbIso_pull K2 g rfl`. Establish `h3 : LBIso ((Xo.univ.t.PP.L.pull π').pull g) (Xo.univ.t.PP.L.pull (g ≫ π'))` using `GlobalTheory.FamRep.lbIso_pull_pull hM π' g`. Conclude with `LBIso.trans o.t.PP.isLB (pull_isLB hM _) (pull_isLB hM _) h1 (LBIso.trans (pull_isLB hM _) (pull_isLB (pull_isLB hM _) _) (pull_isLB hM _) h3.symm h2)`.
-/
theorem cub_const (c : Coeff l) [Algebra c.F K] (hi : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i)
    (hπ : IsGrpPullback A Xo.univ.t.G x₀ π)
    (hπ' : IsGrpPullback A' Xo.univ.t.G x' π') (hiπ : i ≫ π' = π) (hiq : i ≫ q = 𝟙 _)
    (hq : IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q)
    (o : Obj Dw l (baseKA l) (x' ≫ Xo.s)) (m : ObjMap o Xo.univ x') (g : o.t.G.left ⟶ A'.left)
    (hg1 : g ≫ π' = m.cm.F) (hF : IsGrpPullback o.t.G Xo.univ.t.G (constPt x') (g ≫ q ≫ π)) :
    (cubeMapOf hF).IsPullCubical o.t.cub Xo.univ.t.cub := by
  haveI : IsProper o.t.G.hom := o.proper
  have hA : IsAbelianScheme o.t.G := AbelianSchemeGerms.isAbelianScheme_of_proper o.t.G o.t.semi
  refine GlobalTheory.TripleModel.isPullCubical_of_lbIso GlobalTheory.SemiRigid.globalFns hA hF o.t.cub Xo.univ.t.cub ?_
  obtain ⟨w, -, hw, -⟩ := rigIso_congr rfl m.cm m.lin rfl rfl
  have K2 : LBIso (Xo.univ.t.PP.L.pull π') (Xo.univ.t.PP.L.pull (q ≫ π)) :=
    GlobalTheory.TangentConstLB.lbIso_tangent_const E H Dw l Xo c K x₀ x' A A' π π' i q hi hπ hπ' hiπ hiq hq
  have hM := Xo.univ.t.PP.isLB
  have h1 : LBIso o.t.PP.L (Xo.univ.t.PP.L.pull (g ≫ π')) := hg1 ▸ ⟨w, hw⟩
  have h2 : LBIso ((Xo.univ.t.PP.L.pull π').pull g) (Xo.univ.t.PP.L.pull (g ≫ q ≫ π)) :=
    GlobalTheory.Ex.GenericFibre.lbIso_pull K2 g rfl
  have h3 : LBIso ((Xo.univ.t.PP.L.pull π').pull g) (Xo.univ.t.PP.L.pull (g ≫ π')) :=
    GlobalTheory.FamRep.lbIso_pull_pull hM π' g
  exact LBIso.trans o.t.PP.isLB (pull_isLB hM _) (pull_isLB hM _) h1
    (LBIso.trans (pull_isLB hM _) (pull_isLB (pull_isLB hM _) _) (pull_isLB hM _) h3.symm h2)

/- English proof (translation)
Establish `hw : m.cm.F ≫ Xo.univ.t.G.hom = o.t.G.hom ≫ x'` using `m.cart.1.w`. Set `g : o.t.G.left ⟶ A'.left` to `hπ'.1.lift m.cm.F o.t.G.hom hw`. Establish `hg : g ≫ π' = m.cm.F` using `hπ'.1.lift_fst _ _ _`. Establish `hgw : g ≫ A'.hom = o.t.G.hom` using `hπ'.1.lift_snd _ _ _`. Establish `hgc : IsGrpPullback o.t.G A' (𝟙 _) g` using `hπ'.cancel (m.cart.congr (Category.id_comp _).symm hg.symm) (by rw [hgw, Category.comp_id])`.

Establish `hred : spMap (algebraMap K (DualNumber K)) ≫ x₀ = constPt x'`. Rewrite using `[← hx]`. Both sides reduce to the same expression. Establish `hF : IsGrpPullback o.t.G Xo.univ.t.G (constPt x') (g ≫ q ≫ π)` using `(hgc.comp (hq.comp hπ)).congr (by rw [Category.id_comp, hred]) rfl`. Use `haveI : CharZero K := (RingHom.charZero_iff (algebraMap c.F K).injective).1 inferInstance`.

Establish `hgq` using `hgc.comp hq`. Establish `hcomm : ∀ (T : Over (Sp K)) (x y : T ⟶ A), x * y = y * x`. Introduce `T x y`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Apply `hπ.1.hom_ext` to reduce the goal to its premises.

Establish `e1` using `hπ.2 T x y (pushPt hπ.1.w x) (pushPt hπ.1.w y) rfl rfl`. Establish `e2` using `hπ.2 T y x (pushPt hπ.1.w y) (pushPt hπ.1.w x) rfl rfl`. Rewrite using `[← e1, ← e2, _root_.mul_comm]`. Rewrite using `[Over.w (x * y), Over.w (y * x)]`. Establish `key : ∀ (σ : 𝟙_ (Over (Sp (DualNumber K))) ⟶ o.t.G) (τ : 𝟙_ (Over Xo.X) ⟶ Xo.univ.t.G) (n : ℕ), 0 < n → σ ^ n = 1 → σ.left ≫ m.cm.F = x' ≫ τ.left → σ.left ≫ (g ≫ q ≫ π) = constPt x' ≫ τ.left`.

Introduce `σ τ n hn hσ hστ`. Set `u` to `pushHom hgq (𝟙_ (Over (Sp (DualNumber K)))) σ`. Establish `hu : u ^ n = 1` using `by rw [← map_pow, hσ, map_one]`. Establish `e` using `GlobalTheory.TorsConst.torsion_eq_const K A _ (by simp) (hcomm _) u n hn hu`. Establish `hul : u.left = σ.left ≫ g ≫ q` using `by show σ.left ≫ (g ≫ q) = _; rfl`.

Rewrite `e` using `[hul]`. Set `w` to `spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ σ.left ≫ g`. Establish `hw' : w ≫ A'.hom = 𝟙 _ ≫ GlobalTheory.DeRham.epsRed K`. Simplify using `only [w, Category.assoc, hgw, Category.id_comp]`. Rewrite using `[Over.w σ]`.

Both sides reduce to the same expression. Set `s₀` to `hi.1.lift w (𝟙 _) hw'`. Establish `hs₀ : s₀ ≫ i = w` using `hi.1.lift_fst _ _ _`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← hs₀]`.

Simplify using `only [Category.assoc]`. Rewrite using `[reassoc_of% hiq, hiπ]`. Use `_ = spMap (algebraMap K (DualNumber K)) ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ σ.left ≫ m.cm.F := by`. Rewrite using `[reassoc_of% hs₀]`. Simplify using `only [w, Category.assoc, hg]`.

Use `_ = constPt x' ≫ τ.left := by rw [hστ]; rfl`. Establish `hpow : ∀ (f : Dw.La → (𝟙_ (Over (Sp (DualNumber K))) ⟶ o.t.G)), (∀ a b, f (a + b) = f a * f b) → ∀ (n : ℕ) a, f (n • a) = f a ^ n`. Introduce `f hf n a`. Proceed by induction on `n with`. Consider the case `zero`.

Establish `h0` using `hf 0 0`. Rewrite `h0` using `[add_zero]`. Rewrite using `[zero_smul, pow_zero]`. Conclude with `mul_left_cancel (h0.symm.trans (_root_.mul_one _).symm)`. Consider the case `succ n ih => rw [succ_nsmul, hf, ih, pow_succ]`.

Establish `hM : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb`. Establish `h1 : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)`. Rewrite using `[l.prod]`. Conclude with `Ideal.mem_span_singleton_self _`. Conclude with `Ideal.mul_le_left (I := l.Mb) (J := l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) h1`.

Conclude with `⟨{ cm := cubeMapOf hF cart := hF base := rfl act := act_const hi hπ hπ' hiπ hiq hq o m g hg hgw lin := cub_const c hi hπ hπ' hiπ hiq hq o m g hg hF eta := fun a => key (o.eta a) (Xo.univ.eta a) l.M (by have := l.three_le; omega) (by rw [← hpow _ o.eta_add]; exact o.eta_ker _ (by`. Rewrite using `[← Nat.cast_smul_eq_nsmul (𝓞 E)]`. Conclude with `Submodule.smul_mem_smul hM Submodule.mem_top))`. Use the proof step `(m.eta a)`. Use `etaA := fun a => key (o.etaA a) (Xo.univ.etaA a) l.A l.A_pos (by rw [← hpow _ o.etaA_add]; exact o.etaA_ker a) (m.etaA a) }⟩`.
-/
theorem objMap_const (c : Coeff l) [Algebra c.F K] (hx : GlobalTheory.DeRham.epsRed K ≫ x' = x₀)
    (hi : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) (hπ : IsGrpPullback A Xo.univ.t.G x₀ π)
    (hπ' : IsGrpPullback A' Xo.univ.t.G x' π') (hiπ : i ≫ π' = π) (hiq : i ≫ q = 𝟙 _)
    (hq : IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q)
    (o : Obj Dw l (baseKA l) (x' ≫ Xo.s)) (m : ObjMap o Xo.univ x') : Nonempty (ObjMap o Xo.univ (constPt x')) := by
  have hw : m.cm.F ≫ Xo.univ.t.G.hom = o.t.G.hom ≫ x' := m.cart.1.w
  let g : o.t.G.left ⟶ A'.left := hπ'.1.lift m.cm.F o.t.G.hom hw
  have hg : g ≫ π' = m.cm.F := hπ'.1.lift_fst _ _ _
  have hgw : g ≫ A'.hom = o.t.G.hom := hπ'.1.lift_snd _ _ _
  have hgc : IsGrpPullback o.t.G A' (𝟙 _) g :=
    hπ'.cancel (m.cart.congr (Category.id_comp _).symm hg.symm) (by rw [hgw, Category.comp_id])
  have hred : spMap (algebraMap K (DualNumber K)) ≫ x₀ = constPt x' := by
    rw [← hx]; rfl
  have hF : IsGrpPullback o.t.G Xo.univ.t.G (constPt x') (g ≫ q ≫ π) :=
    (hgc.comp (hq.comp hπ)).congr (by rw [Category.id_comp, hred]) rfl
  haveI : CharZero K := (RingHom.charZero_iff (algebraMap c.F K).injective).1 inferInstance
  have hgq := hgc.comp hq
  have hcomm : ∀ (T : Over (Sp K)) (x y : T ⟶ A), x * y = y * x := by
    intro T x y
    apply Over.OverMorphism.ext
    apply hπ.1.hom_ext
    · have e1 := hπ.2 T x y (pushPt hπ.1.w x) (pushPt hπ.1.w y) rfl rfl
      have e2 := hπ.2 T y x (pushPt hπ.1.w y) (pushPt hπ.1.w x) rfl rfl
      rw [← e1, ← e2, _root_.mul_comm]
    · rw [Over.w (x * y), Over.w (y * x)]
  have key : ∀ (σ : 𝟙_ (Over (Sp (DualNumber K))) ⟶ o.t.G) (τ : 𝟙_ (Over Xo.X) ⟶ Xo.univ.t.G) (n : ℕ),
      0 < n → σ ^ n = 1 → σ.left ≫ m.cm.F = x' ≫ τ.left →
      σ.left ≫ (g ≫ q ≫ π) = constPt x' ≫ τ.left := by
    intro σ τ n hn hσ hστ
    let u := pushHom hgq (𝟙_ (Over (Sp (DualNumber K)))) σ
    have hu : u ^ n = 1 := by rw [← map_pow, hσ, map_one]
    have e := GlobalTheory.TorsConst.torsion_eq_const K A _ (by simp) (hcomm _) u n hn hu
    have hul : u.left = σ.left ≫ g ≫ q := by
      show σ.left ≫ (g ≫ q) = _; rfl
    rw [hul] at e
    let w := spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ σ.left ≫ g
    have hw' : w ≫ A'.hom = 𝟙 _ ≫ GlobalTheory.DeRham.epsRed K := by
      simp only [w, Category.assoc, hgw, Category.id_comp]
      rw [Over.w σ]; rfl
    let s₀ := hi.1.lift w (𝟙 _) hw'
    have hs₀ : s₀ ≫ i = w := hi.1.lift_fst _ _ _
    calc σ.left ≫ (g ≫ q ≫ π) = (σ.left ≫ g ≫ q) ≫ π := by simp only [Category.assoc]
      _ = (spMap (algebraMap K (DualNumber K)) ≫ w ≫ q) ≫ π := by rw [e]; simp only [w, Category.assoc]
      _ = spMap (algebraMap K (DualNumber K)) ≫ s₀ ≫ i ≫ π' := by
          rw [← hs₀]; simp only [Category.assoc]; rw [reassoc_of% hiq, hiπ]
      _ = spMap (algebraMap K (DualNumber K)) ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ σ.left ≫ m.cm.F := by
          rw [reassoc_of% hs₀]; simp only [w, Category.assoc, hg]
      _ = constPt x' ≫ τ.left := by rw [hστ]; rfl
  have hpow : ∀ (f : Dw.La → (𝟙_ (Over (Sp (DualNumber K))) ⟶ o.t.G)), (∀ a b, f (a + b) = f a * f b) →
      ∀ (n : ℕ) a, f (n • a) = f a ^ n := by
    intro f hf n a
    induction n with
    | zero =>
      have h0 := hf 0 0
      rw [add_zero] at h0
      rw [zero_smul, pow_zero]
      exact mul_left_cancel (h0.symm.trans (_root_.mul_one _).symm)
    | succ n ih => rw [succ_nsmul, hf, ih, pow_succ]
  have hM : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb := by
    have h1 : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [l.prod]; exact Ideal.mem_span_singleton_self _
    exact Ideal.mul_le_left (I := l.Mb) (J := l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) h1
  exact ⟨{
    cm := cubeMapOf hF
    cart := hF
    base := rfl
    act := act_const hi hπ hπ' hiπ hiq hq o m g hg hgw
    lin := cub_const c hi hπ hπ' hiπ hiq hq o m g hg hF
    eta := fun a => key (o.eta a) (Xo.univ.eta a) l.M (by have := l.three_le; omega)
      (by rw [← hpow _ o.eta_add]; exact o.eta_ker _ (by
        rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]; exact Submodule.smul_mem_smul hM Submodule.mem_top))
      (m.eta a)
    etaA := fun a => key (o.etaA a) (Xo.univ.etaA a) l.A l.A_pos
      (by rw [← hpow _ o.etaA_add]; exact o.etaA_ker a) (m.etaA a) }⟩

/- English proof (translation)
Take `⟨o, ⟨m⟩⟩` from `GlobalTheory.obj_pull E H Dw l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ Xo.s (x' ≫ Xo.s) x' rfl rfl (by rw [spMap, CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]) Xo.univ`. Conclude with `Xo.unram K x' o ⟨m⟩ (objMap_const c rfl hi (hi.comp hπ') hπ' rfl hiq hq o m)`.
-/
theorem eq_constPt (c : Coeff l) [Algebra c.F K] (hi : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i)
    (hπ' : IsGrpPullback A' Xo.univ.t.G x' π') (hiq : i ≫ q = 𝟙 _)
    (hq : IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q) : x' = constPt x' := by
  obtain ⟨o, ⟨m⟩⟩ := GlobalTheory.obj_pull E H Dw l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ Xo.s (x' ≫ Xo.s) x' rfl rfl
    (by rw [spMap, CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]) Xo.univ
  exact Xo.unram K x' o ⟨m⟩ (objMap_const c rfl hi (hi.comp hπ') hπ' rfl hiq hq o m)

end GlobalTheory.InteriorKS
