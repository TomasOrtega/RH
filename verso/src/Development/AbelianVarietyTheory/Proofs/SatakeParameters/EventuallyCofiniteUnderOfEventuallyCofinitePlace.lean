import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.BaseChange
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL
namespace GlobalTheory

/- English proof (translation)
Introduce `K M _ _ _ _ _ P hP`. Rewrite `hP`, the goal using `[Filter.eventually_cofinite]`. Establish `hfib : ∀ v : HeightOneSpectrum (𝓞 K), ((fun w : HeightOneSpectrum (𝓞 M) => w.under (𝓞 K)) ⁻¹' {v}).Finite`. Introduce `v`. Use `Set.Finite.of_finite_image (f := HeightOneSpectrum.asIdeal) ((IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 M)).subset ?_) (fun a _ b _ h => HeightOneSpectrum.ext h)` and prove the remaining obligations.

Introduce and unpack `_ ⟨w, hw, rfl⟩`. Simplify using `only [Set.mem_preimage, Set.mem_singleton_iff] at hw`. Use `⟨w.isPrime, ⟨?_⟩⟩` and prove the remaining obligations. Rewrite using `[← hw]`. Both sides reduce to the same expression.

Conclude with `(hP.preimage' fun v _ => hfib v).subset fun w hw => hw`.
-/
theorem eventually_cofinite_under_of_eventually_cofinite :
    ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
      (P : HeightOneSpectrum (𝓞 K) → Prop), (∀ᶠ v in Filter.cofinite, P v) →
      ∀ᶠ w : HeightOneSpectrum (𝓞 M) in Filter.cofinite, P (w.under (𝓞 K)) := by
  intro K M _ _ _ _ _ P hP
  rw [Filter.eventually_cofinite] at hP ⊢
  have hfib : ∀ v : HeightOneSpectrum (𝓞 K),
      ((fun w : HeightOneSpectrum (𝓞 M) => w.under (𝓞 K)) ⁻¹' {v}).Finite := by
    intro v
    refine Set.Finite.of_finite_image (f := HeightOneSpectrum.asIdeal)
      ((IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 M)).subset ?_)
      (fun a _ b _ h => HeightOneSpectrum.ext h)
    rintro _ ⟨w, hw, rfl⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hw
    refine ⟨w.isPrime, ⟨?_⟩⟩
    rw [← hw]
    rfl
  exact (hP.preimage' fun v _ => hfib v).subset fun w hw => hw

end GlobalTheory
