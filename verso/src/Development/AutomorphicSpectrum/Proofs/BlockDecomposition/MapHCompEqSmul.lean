import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.QuoDMk

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CrystallineSemistableComparison CrystallineSemistableComparison.Tw CrystallineSemistableComparison.Ls

namespace GlobalTheory.CompanionTheory.LsRho

variable {W : Type} [CommRing W]

/- English proof (translation)
Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ u`. Conclude with `congrArg Submodule.Quotient.mk (Subtype.ext (h z.1))`.
-/
theorem mapH_eq_self {K : Cx.{1} W} (φ : Cx.Hom K K (RingHom.id W)) (n : ℕ)
    (h : ∀ x, φ.f n x = x) (u : K.H n) : φ.mapH n u = u := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  exact congrArg Submodule.Quotient.mk (Subtype.ext (h z.1))

/- English proof (translation)
Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ u`. Conclude with `congrArg Submodule.Quotient.mk (Subtype.ext (h z.1))`.
-/
theorem mapH_of_comp {K L P : Cx.{1} W} (φ : Cx.Hom K L (RingHom.id W)) (ψ : Cx.Hom L P (RingHom.id W))
    (χ : Cx.Hom K P (RingHom.id W)) (n : ℕ) (h : ∀ x, χ.f n x = ψ.f n (φ.f n x)) (u : K.H n) :
    χ.mapH n u = ψ.mapH n (φ.mapH n u) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  exact congrArg Submodule.Quotient.mk (Subtype.ext (h z.1))

/- English proof (translation)
Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ u`. Conclude with `congrArg Submodule.Quotient.mk (Subtype.ext (h z.1))`.
-/
theorem mapH_comp_eq_smul {K L : Cx.{1} W} (φ : Cx.Hom K L (RingHom.id W)) (ψ : Cx.Hom L K (RingHom.id W))
    (s : W) (n : ℕ) (h : ∀ x, ψ.f n (φ.f n x) = s • x) (u : K.H n) :
    ψ.mapH n (φ.mapH n u) = s • u := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  exact congrArg Submodule.Quotient.mk (Subtype.ext (h z.1))

/- English proof (translation)
Express the relevant statement in the definitionally equal form `((l : W) ^ n) • (x : (quo l K n).H j) = 0`. Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Establish `hz : ((l : W) ^ n) • z = 0`. Use `Subtype.ext ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((l : W) ^ n) • z.1 = 0`.

Take `⟨w, hw⟩` from `Submodule.Quotient.mk_surjective _ z.1`. Rewrite using `[← hw]`. Express the relevant statement in the definitionally equal form `Submodule.Quotient.mk (((l : W) ^ n) • w) = 0`. Conclude with `(Submodule.Quotient.mk_eq_zero _).2 ⟨w, rfl⟩`. Rewrite using `[← Submodule.Quotient.mk_smul, hz]`.

Both sides reduce to the same expression.
-/
theorem kill (l : ℕ) (K : Cx.{1} W) (j n : ℕ) (x : (qsys l K j).M n) : ((l : W) ^ n) • x = 0 := by
  change ((l : W) ^ n) • (x : (quo l K n).H j) = 0
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hz : ((l : W) ^ n) • z = 0 := by
    refine Subtype.ext ?_
    change ((l : W) ^ n) • z.1 = 0
    obtain ⟨w, hw⟩ := Submodule.Quotient.mk_surjective _ z.1
    rw [← hw]
    change Submodule.Quotient.mk (((l : W) ^ n) • w) = 0
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨w, rfl⟩
  rw [← Submodule.Quotient.mk_smul, hz]
  rfl

end GlobalTheory.CompanionTheory.LsRho

end
