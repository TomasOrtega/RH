import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmpPropsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspExpansionAtInfinityPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspExpansionAtInfinityCompRatAffineStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlTwoPosRatMobiusUpperHalfPlanePropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExpTwoPiIRatInFieldRootsOfUnityPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FractionFieldExtClosureInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHahnSeriesScaleTwistRingHomStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

/- English proof (translation)
Take `⟨hl, hmob⟩` from `(GlobalTheory.T.glTwoPosRatMobius_upperHalfPlane_properties).2.2.2.2.2 g hg`. Take `⟨_, hε, h0, hadd, _, _⟩` from `GlobalTheory.T.expTwoPiIRatInField_roots_of_unity_properties Ω ε`. Take `⟨Φ, hΦ⟩` from `GlobalTheory.T.exists_hahnSeries_scale_twist_ringHom Ω Ω (RingHom.id Ω) (ent g 0 0 / ent g 1 1) (fun r => eOm ε (r * (ent g 0 1 / ent g 1 1))) hl (by simpa using h0) (fun r r' => by simp only [add_mul, hadd])`. Establish `key : (T.exp.toRingHom.comp (T.sl g).toRingEquiv.toRingHom) = Φ.comp T.exp.toRingHom`. Apply `(GlobalTheory.T.fractionField_ext_closure_injective Ω ε T).1` to reduce the goal to its premises.

Introduce `a`. Take `⟨a', ha', hsl⟩` from `(GlobalTheory.T.fractionField_ext_closure_injective Ω ε T).2.1 g a`. Establish `hE : IsExp ε a' (Φ (T.exp (T.io a)))`. Use `GlobalTheory.T.isCuspExpansionAtInfinity_comp_rat_affine Ω ε a a' (ent g 0 0 / ent g 1 1) (ent g 0 1 / ent g 1 1) _ _ hl (fun z hz => ?_) (fun s => ?_) (T.exp_io a)` and prove the remaining obligations. Rewrite using `[ha', (GlobalTheory.T.cmp_mul_ofSL_and_up_cmp_eq_up_mob).2.2.2 g a z hz, hmob z]`.

Rewrite using `[hΦ, map_mul, hε]`. Both sides reduce to the same expression. Establish `hu` using `(GlobalTheory.T.isCuspExpansionAtInfinity_properties Ω ε).2.1 _ _ _ (T.exp_io a') hE`. Use `show T.exp (T.sl g (T.io a)) = Φ (T.exp (T.io a))`. Rewrite using `[hsl, hu]`.

Establish `hc` using `congrArg (fun h : HahnSeries ℚ Ω => h.coeff (r * (ent g 0 0 / ent g 1 1))) (RingHom.congr_fun key f)`. Simplify using `only [RingHom.comp_apply] at hc`. Rewrite using `[mul_div_assoc, mul_div_assoc]`. Use `(show (T.exp (T.sl g f)).coeff (r * (ent g 0 0 / ent g 1 1)) = _ from hc).trans ?_` and prove the remaining obligations. Rewrite using `[hΦ]`.

Both sides reduce to the same expression.
-/
theorem exp_sl_coeff_upper (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ)
    (T : Frac Ω ε) (g : GQ) (hg : ent g 1 0 = 0) (f : T.K) (r : ℚ) :
    (T.exp (T.sl g f)).coeff (r * ent g 0 0 / ent g 1 1) =
      eOm ε (r * ent g 0 1 / ent g 1 1) * (T.exp f).coeff r := by
  obtain ⟨hl, hmob⟩ := (GlobalTheory.T.glTwoPosRatMobius_upperHalfPlane_properties).2.2.2.2.2 g hg
  obtain ⟨_, hε, h0, hadd, _, _⟩ := GlobalTheory.T.expTwoPiIRatInField_roots_of_unity_properties Ω ε
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.exists_hahnSeries_scale_twist_ringHom Ω Ω (RingHom.id Ω) (ent g 0 0 / ent g 1 1)
    (fun r => eOm ε (r * (ent g 0 1 / ent g 1 1))) hl (by simpa using h0)
    (fun r r' => by simp only [add_mul, hadd])
  have key : (T.exp.toRingHom.comp (T.sl g).toRingEquiv.toRingHom) = Φ.comp T.exp.toRingHom := by
    apply (GlobalTheory.T.fractionField_ext_closure_injective Ω ε T).1
    intro a
    obtain ⟨a', ha', hsl⟩ := (GlobalTheory.T.fractionField_ext_closure_injective Ω ε T).2.1 g a
    have hE : IsExp ε a' (Φ (T.exp (T.io a))) := by
      refine GlobalTheory.T.isCuspExpansionAtInfinity_comp_rat_affine Ω ε a a' (ent g 0 0 / ent g 1 1) (ent g 0 1 / ent g 1 1) _ _ hl
        (fun z hz => ?_) (fun s => ?_) (T.exp_io a)
      · rw [ha', (GlobalTheory.T.cmp_mul_ofSL_and_up_cmp_eq_up_mob).2.2.2 g a z hz, hmob z]
      · rw [hΦ, map_mul, hε]
        rfl
    have hu := (GlobalTheory.T.isCuspExpansionAtInfinity_properties Ω ε).2.1 _ _ _ (T.exp_io a') hE
    show T.exp (T.sl g (T.io a)) = Φ (T.exp (T.io a))
    rw [hsl, hu]
  have hc := congrArg (fun h : HahnSeries ℚ Ω => h.coeff (r * (ent g 0 0 / ent g 1 1)))
    (RingHom.congr_fun key f)
  simp only [RingHom.comp_apply] at hc
  rw [mul_div_assoc, mul_div_assoc]
  refine (show (T.exp (T.sl g f)).coeff (r * (ent g 0 0 / ent g 1 1)) = _ from hc).trans ?_
  rw [hΦ]
  rfl

end GlobalTheory.FN
