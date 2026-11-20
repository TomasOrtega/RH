import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory

/- English proof (translation)
Introduce `R _ _ X hX x hx hc`. Use `haveI := hX`. Use `haveI := isClosed_singleton_iff_isClosedImmersion.mp hc`. Establish `hf : LocallyOfFiniteType (X.left.fromSpecResidueField x ≫ X.hom)` using `inferInstance`. Establish `hpt : ∀ p : Spec (X.left.residueField x), (X.left.fromSpecResidueField x ≫ X.hom) p = closedPoint R`.

Introduce `p`. Rewrite using `[Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply, hx]`. Rewrite `hf`, `hpt`, the goal using `[← Spec.map_preimage (X.left.fromSpecResidueField x ≫ X.hom)]`. Rewrite using `[IsFinite.SpecMap_iff]`. Rewrite `hf` using `[HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]`.

Generalize the expression as in `Spec.preimage (X.left.fromSpecResidueField x ≫ X.hom) = φ at hf hpt ⊢`. Set `K` to `X.left.residueField x`. Set `p0 : PrimeSpectrum K` to `⟨⊥, Ideal.bot_prime⟩`. Establish `hker : RingHom.ker φ.hom = maximalIdeal R`. Establish `h1` using `congrArg PrimeSpectrum.asIdeal (hpt p0)`.

Establish `h2 : (Spec.map φ).base p0 = PrimeSpectrum.comap φ.hom p0` using `rfl`. Rewrite `h1` using `[show (Spec.map φ) p0 = (Spec.map φ).base p0 from rfl, h2]`. Establish `h3 : Ideal.comap φ.hom ⊥ = (closedPoint R).asIdeal` using `by simpa [p0] using h1`. Conclude with `h3`. Set `k` to `ResidueField R`.

Set `ψ : k →+* K` to `Ideal.Quotient.lift (maximalIdeal R) φ.hom (fun a ha => by`. Rewrite using `[← RingHom.mem_ker, hker]`. Conclude with `ha)`. Establish `hφ : φ.hom = ψ.comp (residue R)`. Use extensionality with `a`.

Both sides reduce to the same expression. Rewrite `hf`, the goal using `[hφ]`. Establish `hψ : ψ.FiniteType` using `RingHom.FiniteType.of_comp_finiteType hf`. Use `letI : Algebra k K := ψ.toAlgebra`. Use `haveI : Algebra.FiniteType k K := hψ`.

Establish `: Module.Finite k K` using `finite_of_finite_type_of_isJacobsonRing k K`. Establish `hψf : ψ.Finite` using `this`. Conclude with `hψf.comp (RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective)`.
-/
theorem isFinite_fromSpecResidueField_comp_of_isClosed_of_closedPoint : ∀ (R : Type) [CommRing R] [IsLocalRing R] (X : Over (Sp R)), LocallyOfFiniteType X.hom → ∀ x : X.left, X.hom x = closedPoint R → IsClosed ({x} : Set X.left) → IsFinite (X.left.fromSpecResidueField x ≫ X.hom) := by
  intro R _ _ X hX x hx hc
  haveI := hX
  haveI := isClosed_singleton_iff_isClosedImmersion.mp hc
  have hf : LocallyOfFiniteType (X.left.fromSpecResidueField x ≫ X.hom) := inferInstance
  have hpt : ∀ p : Spec (X.left.residueField x), (X.left.fromSpecResidueField x ≫ X.hom) p = closedPoint R := by
    intro p
    rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply, hx]
  rw [← Spec.map_preimage (X.left.fromSpecResidueField x ≫ X.hom)] at hf hpt ⊢
  rw [IsFinite.SpecMap_iff]
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at hf
  generalize Spec.preimage (X.left.fromSpecResidueField x ≫ X.hom) = φ at hf hpt ⊢
  let K := X.left.residueField x
  let p0 : PrimeSpectrum K := ⟨⊥, Ideal.bot_prime⟩
  have hker : RingHom.ker φ.hom = maximalIdeal R := by
    have h1 := congrArg PrimeSpectrum.asIdeal (hpt p0)
    have h2 : (Spec.map φ).base p0 = PrimeSpectrum.comap φ.hom p0 := rfl
    rw [show (Spec.map φ) p0 = (Spec.map φ).base p0 from rfl, h2] at h1
    have h3 : Ideal.comap φ.hom ⊥ = (closedPoint R).asIdeal := by simpa [p0] using h1
    exact h3
  let k := ResidueField R
  let ψ : k →+* K := Ideal.Quotient.lift (maximalIdeal R) φ.hom (fun a ha => by
    rw [← RingHom.mem_ker, hker]; exact ha)
  have hφ : φ.hom = ψ.comp (residue R) := by
    ext a; rfl
  rw [hφ] at hf ⊢
  have hψ : ψ.FiniteType := RingHom.FiniteType.of_comp_finiteType hf
  letI : Algebra k K := ψ.toAlgebra
  haveI : Algebra.FiniteType k K := hψ
  have : Module.Finite k K := finite_of_finite_type_of_isJacobsonRing k K
  have hψf : ψ.Finite := this
  exact hψf.comp (RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective)

end GlobalTheory
