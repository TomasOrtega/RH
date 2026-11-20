import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
open GlobalTheory.EtC

open TensorProduct

namespace GlobalTheory

/- English proof (translation)
Introduce `T E _ _ _ _ _ P _ _ hK`. Use `haveI : Module.Flat T (Localization.AtPrime P) := Module.Flat.trans T E (Localization.AtPrime P)`. Establish `hTEp : Function.Injective (algebraMap T (Localization.AtPrime P))`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `t ht`.

Assume the negation of the conclusion as `h0`. Establish `hreg` using `Module.Flat.isSMulRegular_of_nonZeroDivisors (M := (Localization.AtPrime P)) (mem_nonZeroDivisors_of_ne_zero h0)`. Apply `one_ne_zero (α := (Localization.AtPrime P))` to reduce the goal to its premises. Apply `hreg` to reduce the goal to its premises. Simplify using `[Algebra.smul_def, ht]`.

Establish `hTL : Function.Injective (algebraMap T (FractionRing (Localization.AtPrime P)))`. Rewrite using `[IsScalarTower.algebraMap_eq T (Localization.AtPrime P) (FractionRing (Localization.AtPrime P))]`. Conclude with `(IsFractionRing.injective (Localization.AtPrime P) (FractionRing (Localization.AtPrime P))).comp hTEp`. Use `haveI : FaithfulSMul T (FractionRing (Localization.AtPrime P)) := (faithfulSMul_iff_algebraMap_injective T (FractionRing (Localization.AtPrime P))).2 hTL`. Use `letI : Algebra (FractionRing T) (FractionRing (Localization.AtPrime P)) := FractionRing.liftAlgebra T (FractionRing (Localization.AtPrime P))`.

Use `haveI : IsScalarTower T (FractionRing T) (FractionRing (Localization.AtPrime P)) := FractionRing.isScalarTower_liftAlgebra T (FractionRing (Localization.AtPrime P))`. Use `haveI : Module.Finite (FractionRing T) ((FractionRing T) ⊗[T] E) := Algebra.FormallyUnramified.finite_of_free (FractionRing T) ((FractionRing T) ⊗[T] E)`. Set `φ : (FractionRing T) ⊗[T] E →ₐ[(FractionRing T)] (FractionRing (Localization.AtPrime P))` to `Algebra.TensorProduct.lift (Algebra.ofId (FractionRing T) (FractionRing (Localization.AtPrime P))) (IsScalarTower.toAlgHom T E (FractionRing (Localization.AtPrime P))) (fun _ _ => Commute.all _ _)`. Establish `hE : ∀ e : E, IsIntegral (FractionRing T) (algebraMap E (FractionRing (Localization.AtPrime P)) e)`. Introduce `e`.

Establish `h1 : IsIntegral (FractionRing T) ((1 : (FractionRing T)) ⊗ₜ[T] e)` using `Algebra.IsIntegral.isIntegral _`. Establish `h2` using `h1.map φ`. Simplify `h2` using `[φ]`. Establish `hEp : ∀ x : (Localization.AtPrime P), algebraMap (Localization.AtPrime P) (FractionRing (Localization.AtPrime P)) x ∈ algebraicClosure (FractionRing T) (FractionRing (Localization.AtPrime P))`. Introduce `x`.

Take `⟨⟨e, s⟩, rfl⟩` from `IsLocalization.mk'_surjective P.primeCompl x`. Establish `hs : algebraMap E (FractionRing (Localization.AtPrime P)) s ≠ 0`. Rewrite using `[IsScalarTower.algebraMap_apply E (Localization.AtPrime P) (FractionRing (Localization.AtPrime P))]`. Conclude with `(map_ne_zero_iff _ (IsFractionRing.injective (Localization.AtPrime P) (FractionRing (Localization.AtPrime P)))).2 (IsLocalization.map_units (Localization.AtPrime P) s).ne_zero`. Establish `heq : algebraMap (Localization.AtPrime P) (FractionRing (Localization.AtPrime P)) (IsLocalization.mk' (Localization.AtPrime P) e s) = algebraMap E (FractionRing (Localization.AtPrime P)) e / algebraMap E (FractionRing (Localization.AtPrime P)) s`.

Rewrite using `[eq_div_iff hs, IsScalarTower.algebraMap_apply E (Localization.AtPrime P) (FractionRing (Localization.AtPrime P)) e, IsScalarTower.algebraMap_apply E (Localization.AtPrime P) (FractionRing (Localization.AtPrime P)) (s : E), ← map_mul, IsLocalization.mk'_spec]`. Simplify using `only at heq ⊢`. Rewrite using `[heq]`. Conclude with `div_mem (mem_algebraicClosure_iff.2 (hE e).isAlgebraic) (mem_algebraicClosure_iff.2 (hE s).isAlgebraic)`. Establish `hL : (algebraMap (FractionRing T) (FractionRing (Localization.AtPrime P))).IsIntegral`.

Introduce `z`. Take `⟨x, y, -, rfl⟩` from `IsFractionRing.div_surjective (Localization.AtPrime P) z`. Conclude with `(mem_algebraicClosure_iff.1 (div_mem (hEp x) (hEp y))).isIntegral`. Use `haveI := hK`. Conclude with `IsAlgClosed.of_ringEquiv (FractionRing T) (FractionRing (Localization.AtPrime P)) (RingEquiv.ofBijective (algebraMap (FractionRing T) (FractionRing (Localization.AtPrime P))) (IsAlgClosed.ringHom_bijective_of_isIntegral _ hL))`.
-/
theorem isAlgClosed_fractionRing_atPrime_of_etale : ∀ (T E : Type) [CommRing T] [IsDomain T]
    [CommRing E] [Algebra T E] [Algebra.Etale T E] (P : Ideal E) [P.IsPrime]
    [IsDomain (Localization.AtPrime P)],
    IsAlgClosed (FractionRing T) → IsAlgClosed (FractionRing (Localization.AtPrime P)) := by
  intro T E _ _ _ _ _ P _ _ hK
  haveI : Module.Flat T (Localization.AtPrime P) := Module.Flat.trans T E (Localization.AtPrime P)
  have hTEp : Function.Injective (algebraMap T (Localization.AtPrime P)) := by
    rw [injective_iff_map_eq_zero]
    intro t ht
    by_contra h0
    have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := (Localization.AtPrime P))
      (mem_nonZeroDivisors_of_ne_zero h0)
    apply one_ne_zero (α := (Localization.AtPrime P))
    apply hreg
    simp [Algebra.smul_def, ht]
  have hTL : Function.Injective (algebraMap T (FractionRing (Localization.AtPrime P))) := by
    rw [IsScalarTower.algebraMap_eq T (Localization.AtPrime P) (FractionRing (Localization.AtPrime P))]
    exact (IsFractionRing.injective (Localization.AtPrime P) (FractionRing (Localization.AtPrime P))).comp hTEp
  haveI : FaithfulSMul T (FractionRing (Localization.AtPrime P)) := (faithfulSMul_iff_algebraMap_injective T (FractionRing (Localization.AtPrime P))).2 hTL
  letI : Algebra (FractionRing T) (FractionRing (Localization.AtPrime P)) := FractionRing.liftAlgebra T (FractionRing (Localization.AtPrime P))
  haveI : IsScalarTower T (FractionRing T) (FractionRing (Localization.AtPrime P)) := FractionRing.isScalarTower_liftAlgebra T (FractionRing (Localization.AtPrime P))
  haveI : Module.Finite (FractionRing T) ((FractionRing T) ⊗[T] E) := Algebra.FormallyUnramified.finite_of_free (FractionRing T) ((FractionRing T) ⊗[T] E)
  let φ : (FractionRing T) ⊗[T] E →ₐ[(FractionRing T)] (FractionRing (Localization.AtPrime P)) := Algebra.TensorProduct.lift (Algebra.ofId (FractionRing T) (FractionRing (Localization.AtPrime P)))
    (IsScalarTower.toAlgHom T E (FractionRing (Localization.AtPrime P))) (fun _ _ => Commute.all _ _)
  have hE : ∀ e : E, IsIntegral (FractionRing T) (algebraMap E (FractionRing (Localization.AtPrime P)) e) := by
    intro e
    have h1 : IsIntegral (FractionRing T) ((1 : (FractionRing T)) ⊗ₜ[T] e) := Algebra.IsIntegral.isIntegral _
    have h2 := h1.map φ
    simpa [φ] using h2
  have hEp : ∀ x : (Localization.AtPrime P), algebraMap (Localization.AtPrime P) (FractionRing (Localization.AtPrime P)) x ∈ algebraicClosure (FractionRing T) (FractionRing (Localization.AtPrime P)) := by
    intro x
    obtain ⟨⟨e, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl x
    have hs : algebraMap E (FractionRing (Localization.AtPrime P)) s ≠ 0 := by
      rw [IsScalarTower.algebraMap_apply E (Localization.AtPrime P) (FractionRing (Localization.AtPrime P))]
      exact (map_ne_zero_iff _ (IsFractionRing.injective (Localization.AtPrime P) (FractionRing (Localization.AtPrime P)))).2
        (IsLocalization.map_units (Localization.AtPrime P) s).ne_zero
    have heq : algebraMap (Localization.AtPrime P) (FractionRing (Localization.AtPrime P)) (IsLocalization.mk' (Localization.AtPrime P) e s) =
        algebraMap E (FractionRing (Localization.AtPrime P)) e / algebraMap E (FractionRing (Localization.AtPrime P)) s := by
      rw [eq_div_iff hs, IsScalarTower.algebraMap_apply E (Localization.AtPrime P) (FractionRing (Localization.AtPrime P)) e,
        IsScalarTower.algebraMap_apply E (Localization.AtPrime P) (FractionRing (Localization.AtPrime P)) (s : E), ← map_mul, IsLocalization.mk'_spec]
    simp only at heq ⊢
    rw [heq]
    exact div_mem (mem_algebraicClosure_iff.2 (hE e).isAlgebraic)
      (mem_algebraicClosure_iff.2 (hE s).isAlgebraic)
  have hL : (algebraMap (FractionRing T) (FractionRing (Localization.AtPrime P))).IsIntegral := by
    intro z
    obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective (Localization.AtPrime P) z
    exact (mem_algebraicClosure_iff.1 (div_mem (hEp x) (hEp y))).isIntegral
  haveI := hK
  exact IsAlgClosed.of_ringEquiv (FractionRing T) (FractionRing (Localization.AtPrime P))
    (RingEquiv.ofBijective (algebraMap (FractionRing T) (FractionRing (Localization.AtPrime P))) (IsAlgClosed.ringHom_bijective_of_isIntegral _ hL))

end GlobalTheory
