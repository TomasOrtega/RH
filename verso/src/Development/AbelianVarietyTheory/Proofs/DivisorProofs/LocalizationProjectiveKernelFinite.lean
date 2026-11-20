import Mathlib
open TensorProduct

namespace GlobalTheory

/- English proof (translation)
Use `set S := Submonoid.powers f`. Set `πf` to `LocalizedModule.map S π`. Establish `hsurj : Function.Surjective πf` using `LocalizedModule.map_surjective S π hπ`. Establish `: Module.Finite (Localization.Away f) (LocalizedModule S M)` using `Module.Finite.of_surjective πf hsurj`. Establish `: Module.FinitePresentation (Localization.Away f) (LocalizedModule S M)` using `Module.finitePresentation_of_projective _ _`.

Establish `hfg : (LinearMap.ker πf).FG` using `Module.FinitePresentation.fg_ker πf hsurj`. Establish `: Module.Finite (Localization.Away f) (LinearMap.ker πf)` using `Module.Finite.iff_fg.mpr hfg`. Set `ι` to `LocalizedModule.map S (LinearMap.ker π).subtype`. Establish `hinj : Function.Injective ι` using `LocalizedModule.map_injective S _ (LinearMap.ker π).injective_subtype`. Establish `hex : Function.Exact ι πf` using `LocalizedModule.map_exact S _ π (LinearMap.exact_subtype_ker_map π)`.

Establish `hr : LinearMap.range ι = LinearMap.ker πf` using `LinearMap.exact_iff.mp hex |>.symm`. Set `e : LocalizedModule S (LinearMap.ker π) ≃ₗ[Localization.Away f] LinearMap.ker πf` to `(LinearEquiv.ofInjective ι hinj).trans (LinearEquiv.ofEq _ _ hr)`. Conclude with `Module.Finite.equiv e.symm`.
-/
theorem finite_localized_ker_of_projective_away (A : Type) [CommRing A] (f : A) (M : Type) [AddCommGroup M] [Module A M]
  (hP : Module.Projective (Localization.Away f) (LocalizedModule (Submonoid.powers f) M))
  (n : ℕ) (π : (Fin n → A) →ₗ[A] M) (hπ : Function.Surjective π) :
  Module.Finite (Localization.Away f) (LocalizedModule (Submonoid.powers f) (LinearMap.ker π)) := by
  set S := Submonoid.powers f
  let πf := LocalizedModule.map S π
  have hsurj : Function.Surjective πf := LocalizedModule.map_surjective S π hπ
  have : Module.Finite (Localization.Away f) (LocalizedModule S M) := Module.Finite.of_surjective πf hsurj
  have : Module.FinitePresentation (Localization.Away f) (LocalizedModule S M) :=
    Module.finitePresentation_of_projective _ _
  have hfg : (LinearMap.ker πf).FG := Module.FinitePresentation.fg_ker πf hsurj
  have : Module.Finite (Localization.Away f) (LinearMap.ker πf) := Module.Finite.iff_fg.mpr hfg
  let ι := LocalizedModule.map S (LinearMap.ker π).subtype
  have hinj : Function.Injective ι := LocalizedModule.map_injective S _ (LinearMap.ker π).injective_subtype
  have hex : Function.Exact ι πf := LocalizedModule.map_exact S _ π (LinearMap.exact_subtype_ker_map π)
  have hr : LinearMap.range ι = LinearMap.ker πf := LinearMap.exact_iff.mp hex |>.symm
  let e : LocalizedModule S (LinearMap.ker π) ≃ₗ[Localization.Away f] LinearMap.ker πf :=
    (LinearEquiv.ofInjective ι hinj).trans (LinearEquiv.ofEq _ _ hr)
  exact Module.Finite.equiv e.symm

end GlobalTheory
