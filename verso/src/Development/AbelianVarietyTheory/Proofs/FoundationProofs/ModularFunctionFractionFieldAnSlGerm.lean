import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmpPropsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneGermRingHomAndRestrictStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TendstoMobCodiscreteWithinStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FractionFieldExtClosureInjectiveStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

noncomputable section

namespace GlobalTheory.FN

def germCompMob (g : GQ) : Mero →+* Mero where
  toFun F := F.compTendsto (mob g) (GlobalTheory.T.tendsto_mob_codiscreteWithin_codiscreteWithin g)
  map_one' := rfl
  map_mul' F G := by
    induction F using Filter.Germ.inductionOn
    induction G using Filter.Germ.inductionOn
    rfl
  map_zero' := rfl
  map_add' F G := by
    induction F using Filter.Germ.inductionOn
    induction G using Filter.Germ.inductionOn
    rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem germCompMob_coe (g : GQ) (φ : ℂ → ℂ) :
    germCompMob g (φ : Mero) = ((fun z => φ (mob g z)) : Mero) := rfl

/- English proof (translation)
Introduce `Ω _ _ _ ε T g f φ hf`. Establish `key : T.an.comp ((T.sl g : T.K ≃ₐ[Ω] T.K) : T.K →+* T.K) = (germCompMob g).comp T.an`. Apply `(GlobalTheory.T.fractionField_ext_closure_injective Ω ε T).1 Mero` to reduce the goal to its premises. Introduce `a`. Take `⟨a', ha', hs⟩` from `(GlobalTheory.T.fractionField_ext_closure_injective Ω ε T).2.1 g a`.

Simplify using `only [RingHom.comp_apply]`. Rewrite using `[show ((T.sl g : T.K ≃ₐ[Ω] T.K) : T.K →+* T.K) (T.io a) = T.sl g (T.io a) from rfl, hs, T.an_io, T.an_io]`. Unfold `germ`. Rewrite using `[germCompMob_coe]`. Apply `(GlobalTheory.T.upperHalfPlane_germ_ringHom_and_restrict).2.2.1` to reduce the goal to its premises.

Introduce `z hz`. Rewrite using `[ha']`. Conclude with `(GlobalTheory.T.cmp_mul_ofSL_and_up_cmp_eq_up_mob).2.2.2 g a z hz`. Establish `h2` using `RingHom.congr_fun key f`. Simplify using `only [RingHom.comp_apply] at h2`.

Rewrite `h2` using `[show ((T.sl g : T.K ≃ₐ[Ω] T.K) : T.K →+* T.K) f = T.sl g f from rfl]`. Rewrite using `[h2, hf, germCompMob_coe]`.
-/
theorem an_sl_germ : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (g : GQ) (f : T.K) (φ : ℂ → ℂ), T.an f = (φ : Mero) → T.an (T.sl g f) = ((fun z => φ (mob g z)) : Mero) := by
  intro Ω _ _ _ ε T g f φ hf
  have key : T.an.comp ((T.sl g : T.K ≃ₐ[Ω] T.K) : T.K →+* T.K) = (germCompMob g).comp T.an := by
    apply (GlobalTheory.T.fractionField_ext_closure_injective Ω ε T).1 Mero
    intro a
    obtain ⟨a', ha', hs⟩ := (GlobalTheory.T.fractionField_ext_closure_injective Ω ε T).2.1 g a
    simp only [RingHom.comp_apply]
    rw [show ((T.sl g : T.K ≃ₐ[Ω] T.K) : T.K →+* T.K) (T.io a) = T.sl g (T.io a) from rfl, hs, T.an_io, T.an_io]
    unfold germ
    rw [germCompMob_coe]
    apply (GlobalTheory.T.upperHalfPlane_germ_ringHom_and_restrict).2.2.1
    intro z hz
    rw [ha']
    exact (GlobalTheory.T.cmp_mul_ofSL_and_up_cmp_eq_up_mob).2.2.2 g a z hz
  have h2 := RingHom.congr_fun key f
  simp only [RingHom.comp_apply] at h2
  rw [show ((T.sl g : T.K ≃ₐ[Ω] T.K) : T.K →+* T.K) f = T.sl g f from rfl] at h2
  rw [h2, hf, germCompMob_coe]

end GlobalTheory.FN
