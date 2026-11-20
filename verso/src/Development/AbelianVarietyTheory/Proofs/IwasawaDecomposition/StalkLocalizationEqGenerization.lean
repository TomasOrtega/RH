import Mathlib
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace GlobalTheory

/- English proof (translation)
Introduce `X x q _`. Take `⟨_, ⟨U, hU, rfl⟩, hxU, -⟩` from `X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ`. Establish `hU : IsAffineOpen U` using `hU`. Set `xU : U` to `⟨x, hxU⟩`. Set `algX : Algebra Γ(X, U) (X.presheaf.stalk x)` to `TopCat.Presheaf.algebra_section_stalk X.presheaf xU`.

Establish `hlocX : IsLocalization.AtPrime (X.presheaf.stalk x) (hU.primeIdealOf xU).asIdeal` using `hU.isLocalization_stalk xU`. Use `set Px := hU.primeIdealOf xU with hPx`. Set `P' : PrimeSpectrum Γ(X, U)` to `⟨q.comap (algebraMap Γ(X, U) (X.presheaf.stalk x)), inferInstance⟩`. Establish `hP'x : P' ≤ Px`. Introduce `a ha`.

Assume the negation of the conclusion as `hna`. Establish `hu : IsUnit (algebraMap Γ(X, U) (X.presheaf.stalk x) a)` using `IsLocalization.map_units (X.presheaf.stalk x) (⟨a, hna⟩ : Px.asIdeal.primeCompl)`. Conclude with `(Ideal.IsPrime.ne_top inferInstance) (Ideal.eq_top_of_isUnit_mem q ha hu)`. Use `set y := hU.fromSpec P' with hy`. Establish `hyU : y ∈ U`.

Establish `: y ∈ (U : Set X)` using `by rw [← hU.range_fromSpec]; exact ⟨P', rfl⟩`. Conclude with `this`. Establish `hsp : y ⤳ x`. Establish `h1 : P' ⤳ Px` using `(PrimeSpectrum.le_iff_specializes P' Px).mp hP'x`. Establish `h2` using `h1.map hU.fromSpec.continuous`.

Rewrite `h2` using `[hU.fromSpec_primeIdealOf xU]`. Then use the resulting hypothesis. Set `yU : U` to `⟨y, hyU⟩`. Set `algY : Algebra Γ(X, U) (X.presheaf.stalk y)` to `TopCat.Presheaf.algebra_section_stalk X.presheaf yU`. Establish `hlocY : IsLocalization.AtPrime (X.presheaf.stalk y) P'.asIdeal` using `hU.isLocalization_stalk' P' hyU`. Set `T` to `Localization.AtPrime q`.

Establish `hT : IsLocalization.AtPrime T P'.asIdeal` using `IsLocalization.isLocalization_isLocalization_atPrime_isLocalization (M := Px.asIdeal.primeCompl) (S := X.presheaf.stalk x) (T := T) q`. Set `φ : X.presheaf.stalk y ≃ₐ[Γ(X, U)] T` to `IsLocalization.algEquiv P'.asIdeal.primeCompl _ _`. Use `⟨y, hsp, φ.symm.toRingEquiv, ?_⟩` and prove the remaining obligations. Introduce `s`. Establish `key : (φ.symm.toRingEquiv.toRingHom.comp (algebraMap (X.presheaf.stalk x) T)) = (X.presheaf.stalkSpecializes hsp).hom`.

Apply `IsLocalization.ringHom_ext Px.asIdeal.primeCompl` to reduce the goal to its premises. Use extensionality with `a`. Simplify using `only [RingHom.comp_apply]`. Rewrite using `[← IsScalarTower.algebraMap_apply Γ(X, U) (X.presheaf.stalk x) T]`. Establish `h1 : φ.symm.toRingEquiv.toRingHom (algebraMap Γ(X, U) T a) = algebraMap Γ(X, U) (X.presheaf.stalk y) a` using `φ.symm.commutes a`.

Rewrite using `[h1]`. Use `show X.presheaf.germ U y hyU a = (X.presheaf.stalkSpecializes hsp).hom (X.presheaf.germ U x hxU a)`. Conclude with `(TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf hxU hsp a).symm`. Conclude with `congrArg (fun f => f s) key`.
-/
theorem stalk_localization_atPrime_eq_stalk_generization :
    ∀ (X : Scheme.{0}) (x : X) (q : Ideal (X.presheaf.stalk x)) [q.IsPrime],
      ∃ (y : X) (h : y ⤳ x) (e : Localization.AtPrime q ≃+* X.presheaf.stalk y),
        ∀ s, e (algebraMap _ _ s) = (X.presheaf.stalkSpecializes h).hom s := by
  intro X x q _
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hU : IsAffineOpen U := hU
  let xU : U := ⟨x, hxU⟩
  let algX : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf xU
  have hlocX : IsLocalization.AtPrime (X.presheaf.stalk x) (hU.primeIdealOf xU).asIdeal :=
    hU.isLocalization_stalk xU
  set Px := hU.primeIdealOf xU with hPx
  let P' : PrimeSpectrum Γ(X, U) :=
    ⟨q.comap (algebraMap Γ(X, U) (X.presheaf.stalk x)), inferInstance⟩
  have hP'x : P' ≤ Px := by
    intro a ha
    by_contra hna
    have hu : IsUnit (algebraMap Γ(X, U) (X.presheaf.stalk x) a) :=
      IsLocalization.map_units (X.presheaf.stalk x) (⟨a, hna⟩ : Px.asIdeal.primeCompl)
    exact (Ideal.IsPrime.ne_top inferInstance) (Ideal.eq_top_of_isUnit_mem q ha hu)
  set y := hU.fromSpec P' with hy
  have hyU : y ∈ U := by
    have : y ∈ (U : Set X) := by rw [← hU.range_fromSpec]; exact ⟨P', rfl⟩
    exact this
  have hsp : y ⤳ x := by
    have h1 : P' ⤳ Px := (PrimeSpectrum.le_iff_specializes P' Px).mp hP'x
    have h2 := h1.map hU.fromSpec.continuous
    rwa [hU.fromSpec_primeIdealOf xU] at h2
  let yU : U := ⟨y, hyU⟩
  let algY : Algebra Γ(X, U) (X.presheaf.stalk y) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf yU
  have hlocY : IsLocalization.AtPrime (X.presheaf.stalk y) P'.asIdeal :=
    hU.isLocalization_stalk' P' hyU
  let T := Localization.AtPrime q
  have hT : IsLocalization.AtPrime T P'.asIdeal :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (M := Px.asIdeal.primeCompl) (S := X.presheaf.stalk x) (T := T) q
  let φ : X.presheaf.stalk y ≃ₐ[Γ(X, U)] T := IsLocalization.algEquiv P'.asIdeal.primeCompl _ _
  refine ⟨y, hsp, φ.symm.toRingEquiv, ?_⟩
  intro s
  have key : (φ.symm.toRingEquiv.toRingHom.comp (algebraMap (X.presheaf.stalk x) T)) =
      (X.presheaf.stalkSpecializes hsp).hom := by
    apply IsLocalization.ringHom_ext Px.asIdeal.primeCompl
    ext a
    simp only [RingHom.comp_apply]
    rw [← IsScalarTower.algebraMap_apply Γ(X, U) (X.presheaf.stalk x) T]
    have h1 : φ.symm.toRingEquiv.toRingHom (algebraMap Γ(X, U) T a) =
        algebraMap Γ(X, U) (X.presheaf.stalk y) a :=
      φ.symm.commutes a
    rw [h1]
    show X.presheaf.germ U y hyU a =
      (X.presheaf.stalkSpecializes hsp).hom (X.presheaf.germ U x hxU a)
    exact (TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf hxU hsp a).symm
  exact congrArg (fun f => f s) key

end GlobalTheory
