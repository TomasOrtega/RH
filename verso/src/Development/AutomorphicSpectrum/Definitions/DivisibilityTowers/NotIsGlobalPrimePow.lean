import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverOfIsIso
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabMapOfBaseEq
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.ExistsGoodLevel
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.ModuliNonemptyOfObj
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ToMatrixTrFormBaseChange
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.OneAddZeta21PowSevenAddPowFourteenEqZero
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top.GoodModel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Models GlobalTheory.Models.RankZero

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

/- English proof (translation)
Take `⟨Yl, h₁, h₆⟩` from `hP.2 E H D hD Xo`. Take `⟨Y, hd, hdom⟩` from `h₆ l c hg hA`. Conclude with `⟨Y, Yl, hg, h₁, hA, hd, hdom⟩`.
-/
theorem exists_isGlobal (hP : PartI) (hD : 1 ≤ D.p + D.q) (Xo : ∀ l : Level H, Moduli D l) (l : Level H)
    (c : Coeff l) (hg : ∀ p : ℕ, p.Prime → l.GoodAt p) (hA : l.A = 1) :
    ∃ Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F), IsGlobal Xo l c Y := by
  obtain ⟨Yl, h₁, h₆⟩ := hP.2 E H D hD Xo
  obtain ⟨Y, hd, hdom⟩ := h₆ l c hg hA
  exact ⟨Y, Yl, hg, h₁, hA, hd, hdom⟩

/- English proof (translation)
Take `⟨⟨hP, hN, -⟩, -⟩` from `hG`. Take `⟨l, hA, hg⟩` from `GlobalTheory.GlobalModelGuards.exists_good_level HostModel.host`. Take `⟨c⟩` from `GlobalTheory.ModuliProbe.coeff_nonempty l`. Set `Xo : ∀ l : Level HostModel.host, Moduli (HostModel.hypDatum HostModel.host) l` to `fun l => (hN _ _ _ l (by simp)).some`. Take `⟨Y, hY⟩` from `exists_isGlobal hP (by simp) Xo l c hg hA`.

Conclude with `⟨_, _, Xo, l, c, Y, by simp, by simp, hY⟩`.
-/
theorem isGlobal_inhabited (hG : Given) :
    ∃ (H : Host HostModel.E21) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l)
      (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)), 1 ≤ D.p ∧ 1 ≤ D.q ∧ IsGlobal Xo l c Y := by
  obtain ⟨⟨hP, hN, -⟩, -⟩ := hG
  obtain ⟨l, hA, hg⟩ := GlobalTheory.GlobalModelGuards.exists_good_level HostModel.host
  obtain ⟨c⟩ := GlobalTheory.ModuliProbe.coeff_nonempty l
  let Xo : ∀ l : Level HostModel.host, Moduli (HostModel.hypDatum HostModel.host) l :=
    fun l => (hN _ _ _ l (by simp)).some
  obtain ⟨Y, hY⟩ := exists_isGlobal hP (by simp) Xo l c hg hA
  exact ⟨_, _, Xo, l, c, Y, by simp, by simp, hY⟩

/- English proof (translation)
Introduce `⟨_, hg, _⟩` and use `GlobalTheory.GlobalModelGuards.not_goodAt_pow l p k hp hM (hg p hp)`.
-/
theorem not_isGlobal_primePow (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l)
    (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (p k : ℕ) (hp : p.Prime) (hM : l.M = p ^ k) :
    ¬ IsGlobal Xo l c Y := fun ⟨_, hg, _⟩ => GlobalTheory.GlobalModelGuards.not_goodAt_pow l p k hp hM (hg p hp)

/- English proof (translation)
Establish `h₁` using `o.j_eq`. Establish `h₂` using `T.j_pos`. Establish `h₃` using `T.j_lt`. Use linear arithmetic over natural numbers and integers.
-/
theorem signature_pos {l : Level H} {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)}
    {T : RootTower (CMType H) (D.p + D.q)} [DecidableEq (CMType H)] (o : GoodOrigin Y T) : 1 ≤ D.p ∧ 1 ≤ D.q := by
  have h₁ := o.j_eq
  have h₂ := T.j_pos
  have h₃ := T.j_lt
  omega

/- English proof (translation)
Use `⟨by rw [(o.Or B a).kA_eq, (o.refOr a).kA_eq], by rw [(o.refOr a).δ_eq, o.ref_deg, Nat.mul_one], by rw [(o.refOr a).Re_deg, o.ref_deg], ⟨(o.refOr a).g.injective, ?_⟩, fun a => (o.Fx a).pos⟩` and prove the remaining obligations. Set `_` to `(o.refOr a).g.toAlgebra`. Establish `h : Module.finrank (o.Fx a).Ωf (o.R a).Ω = 1` using `(o.refOr a).g_deg.trans (o.ref_deg a)`. Introduce `x`. Establish `hx : x ∈ (⊥ : Subalgebra (o.Fx a).Ωf (o.R a).Ω)`.

Rewrite using `[Subalgebra.bot_eq_top_iff_finrank_eq_one.2 h]`. Discharge the goal by the elementary cases of `trivial`. Conclude with `Algebra.mem_bot.1 hx`.
-/
theorem ref_facts {l : Level H} {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)}
    {T : RootTower (CMType H) (D.p + D.q)} [DecidableEq (CMType H)] (o : GoodOrigin Y T) (B : ℕ) (a : T.Comp) :
    (T.M B a).kA = (o.R a).kA ∧ (o.R a).δ = Module.finrank ℚ c.F ∧ (o.refOr a).Re.deg = 1 ∧
      Function.Bijective (o.refOr a).g ∧ (realOf o.toTowerOrigin).Pos := by
  refine ⟨by rw [(o.Or B a).kA_eq, (o.refOr a).kA_eq], by rw [(o.refOr a).δ_eq, o.ref_deg, Nat.mul_one],
    by rw [(o.refOr a).Re_deg, o.ref_deg], ⟨(o.refOr a).g.injective, ?_⟩, fun a => (o.Fx a).pos⟩
  let _ := (o.refOr a).g.toAlgebra
  have h : Module.finrank (o.Fx a).Ωf (o.R a).Ω = 1 := (o.refOr a).g_deg.trans (o.ref_deg a)
  intro x
  have hx : x ∈ (⊥ : Subalgebra (o.Fx a).Ωf (o.R a).Ω) := by
    rw [Subalgebra.bot_eq_top_iff_finrank_eq_one.2 h]; trivial
  exact Algebra.mem_bot.1 hx

/- English proof (translation)
Introduce `l Xo 𝔓 p i _ _ _ _ _ k _ _ y C _`. Take `⟨hs, hG⟩` from `isIso_moduli GlobalTheory.card_torsion_abelianVariety hD Xo`. Use `⟨y, ⟨rfl, 𝟙 _, MonoidHom.id _, Category.id_comp _, fun x => Category.comp_id _, fun _ _ => rfl, Function.surjective_id, ?_, fun n x x' c _ h => ?_, fun p' _ a => ⟨hom_unique hG _ _, hom_unique hG _ _⟩⟩, fun y'' h => (cancel_mono Xo.s).1 h.1⟩` and prove the remaining obligations. Use extensionality with `x`. Rewrite using `[hom_unique hG x 1]`.

Conclude with `⟨fun _ => C.one_mem, fun _ => (MonoidHom.id _).ker.one_mem⟩`. Establish `h₁` using `weilIs_zero hG Xo.univ.t.PP.isLB (triv_rig hG Xo.univ.t.PP) (n : ℤ) x x'`. Establish `e` using `GlobalTheory.CommutatorPairing.weilIs_unique globalFns_holds (isAbelianScheme_zero hG) Xo.univ.t.PP.isLB h h₁`. Establish `e' : unitOn (c ^ p ^ 2) = 1`. Establish `: unitOn (c ^ p ^ 2) = unitOn c ^ p ^ 2` using `map_pow _ _ _`.

Rewrite using `[this, e, one_pow]`. Rewrite using `[e']`. Conclude with `h₁`.
-/
theorem hecke_rank_zero (hD : D.p + D.q = 0) : ToroidalHeckeCompatibility (H := H) (D := D) := by
  intro l Xo 𝔓 p i _ _ _ _ _ k _ _ y C _
  obtain ⟨hs, hG⟩ := isIso_moduli GlobalTheory.card_torsion_abelianVariety hD Xo
  refine ⟨y, ⟨rfl, 𝟙 _, MonoidHom.id _, Category.id_comp _, fun x => Category.comp_id _, fun _ _ => rfl,
    Function.surjective_id, ?_, fun n x x' c _ h => ?_, fun p' _ a => ⟨hom_unique hG _ _, hom_unique hG _ _⟩⟩,
    fun y'' h => (cancel_mono Xo.s).1 h.1⟩
  · ext x
    rw [hom_unique hG x 1]
    exact ⟨fun _ => C.one_mem, fun _ => (MonoidHom.id _).ker.one_mem⟩
  · have h₁ := weilIs_zero hG Xo.univ.t.PP.isLB (triv_rig hG Xo.univ.t.PP) (n : ℤ) x x'
    have e := GlobalTheory.CommutatorPairing.weilIs_unique globalFns_holds (isAbelianScheme_zero hG) Xo.univ.t.PP.isLB h h₁
    have e' : unitOn (c ^ p ^ 2) = 1 := by
      have : unitOn (c ^ p ^ 2) = unitOn c ^ p ^ 2 := map_pow _ _ _
      rw [this, e, one_pow]
    rw [e']
    exact h₁

end GlobalTheory.CompanionTheory.Ar.Top.GoodModel
