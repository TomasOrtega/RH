import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLifted
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LogPair

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry TopologicalSpace in

/- English proof (translation)
Introduce `R _ Y g U n t hU ht y hy`. Establish `hC : (MvPolynomial.C : R →+* MvPolynomial (Fin n) R).Flat`. Rewrite using `[← MvPolynomial.algebraMap_eq, RingHom.flat_algebraMap_iff]`. Use `infer_instance`. Establish `hE : (MvPolynomial.eval₂Hom (_root_.GlobalTheory.LogPair.cstOn g U) t).Flat`.

Establish `h : (MvPolynomial.eval₂Hom (_root_.GlobalTheory.LogPair.cstOn g U) t).Etale` using `ht`. Use `letI := (MvPolynomial.eval₂Hom (_root_.GlobalTheory.LogPair.cstOn g U) t).toAlgebra`. Establish `: Algebra.Etale (MvPolynomial (Fin n) R) Γ(Y, U)` using `h`. Use `show Module.Flat _ _`. Use `infer_instance`.

Establish `hG : (Y.presheaf.germ U y hy).hom.Flat`. Use `letI := (Y.presheaf.germ U y hy).hom.toAlgebra`. Use `hU.isLocalization_stalk ⟨y, hy⟩` as an intermediate fact. Use `show Module.Flat _ _`. Conclude with `IsLocalization.flat _ (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl`.

Rewrite using `[← MvPolynomial.eval₂Hom_comp_C (_root_.GlobalTheory.LogPair.cstOn g U) t, ← RingHom.comp_assoc]`. Conclude with `(hC.comp hE).comp hG`.
-/
theorem _root_.GlobalTheory.LogPair.flat_germ_comp_cstOn_of_isEtCoord : ∀ {R : Type} [CommRing R] {Y : Scheme.{0}}
    (g : Y ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R) (U : Y.Opens) {n : ℕ} (t : Fin n → Γ(Y, U)), IsAffineOpen U →
    _root_.GlobalTheory.LogPair.IsEtCoord g U t → ∀ (y : Y) (hy : y ∈ U),
    ((Y.presheaf.germ U y hy).hom.comp (_root_.GlobalTheory.LogPair.cstOn g U)).Flat := by
  intro R _ Y g U n t hU ht y hy
  have hC : (MvPolynomial.C : R →+* MvPolynomial (Fin n) R).Flat := by
    rw [← MvPolynomial.algebraMap_eq, RingHom.flat_algebraMap_iff]
    infer_instance
  have hE : (MvPolynomial.eval₂Hom (_root_.GlobalTheory.LogPair.cstOn g U) t).Flat := by
    have h : (MvPolynomial.eval₂Hom (_root_.GlobalTheory.LogPair.cstOn g U) t).Etale := ht
    letI := (MvPolynomial.eval₂Hom (_root_.GlobalTheory.LogPair.cstOn g U) t).toAlgebra
    have : Algebra.Etale (MvPolynomial (Fin n) R) Γ(Y, U) := h
    show Module.Flat _ _
    infer_instance
  have hG : (Y.presheaf.germ U y hy).hom.Flat := by
    letI := (Y.presheaf.germ U y hy).hom.toAlgebra
    have := hU.isLocalization_stalk ⟨y, hy⟩
    show Module.Flat _ _
    exact IsLocalization.flat _ (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl
  rw [← MvPolynomial.eval₂Hom_comp_C (_root_.GlobalTheory.LogPair.cstOn g U) t, ← RingHom.comp_assoc]
  exact (hC.comp hE).comp hG

end GlobalTheory.LogPair
