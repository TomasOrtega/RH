import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.ScalarOnInertiaProp

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.TNZ

namespace SphericalUnramified

/- English proof (translation)
Unfold `IsSpherical IsSphericalFor at *`. Take `⟨x, hx, h0⟩` from `(Submodule.ne_bot_iff _).1 h`. Use `(Submodule.ne_bot_iff _).2 ⟨e x, ?_, ?_⟩` and prove the remaining obligations. Introduce `g`. Establish `hg` using `hx g`.

Establish `hint : e (ρ (g : GL (Fin d) k) x) = π (g : GL (Fin d) k) (e x)` using `LinearMap.congr_fun (e.isIntertwining' (g : GL (Fin d) k)) x`. Rewrite using `[← hint, hg, map_smul]`. Introduce `h1`. Apply `h0` to reduce the goal to its premises. Establish `: e x = e 0` using `by rw [h1, map_zero]`.

Conclude with `EquivLike.injective e this`.
-/
theorem isSpherical_of_equiv {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {d : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GL (Fin d) k) V} {π : Representation ℂ (GL (Fin d) k) W} (e : ρ.Equiv π)
    (h : IsSpherical ρ) : IsSpherical π := by
  unfold IsSpherical IsSphericalFor at *
  obtain ⟨x, hx, h0⟩ := (Submodule.ne_bot_iff _).1 h
  refine (Submodule.ne_bot_iff _).2 ⟨e x, ?_, ?_⟩
  · intro g
    have hg := hx g
    have hint : e (ρ (g : GL (Fin d) k) x) = π (g : GL (Fin d) k) (e x) :=
      LinearMap.congr_fun (e.isIntertwining' (g : GL (Fin d) k)) x
    rw [← hint, hg, map_smul]
  · intro h1
    apply h0
    have : e x = e 0 := by rw [h1, map_zero]
    exact EquivLike.injective e this

end SphericalUnramified

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ A w h a ha ε rc hL d X _ _ σ hs hi hsph`. Conclude with `(hL.sph (IrrGL.of σ hs hi)).1 (SphericalUnramified.isSpherical_of_equiv (IrrGL.equivOf σ hs hi) hsph)`.
-/
theorem step_sphUnr : SphericalUnramifiedProp := by
  intro E Ω _ _ _ _ _ A w h a ha ε rc hL d X _ _ σ hs hi hsph
  exact (hL.sph (IrrGL.of σ hs hi)).1 (SphericalUnramified.isSpherical_of_equiv (IrrGL.equivOf σ hs hi) hsph)

end UpperTheory.TNZ
