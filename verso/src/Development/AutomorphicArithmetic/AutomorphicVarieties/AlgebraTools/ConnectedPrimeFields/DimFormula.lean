import Mathlib
import ReciprocityTheory.CommutativeAlgebra.ChainConnInDim
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.IsSaturatedChain
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.Integral
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.LocDim
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.IsWeaklyRegularPairModOneLeft

open IsLocalRing UpperTheory.V.AlgebraTools.Conn

/- English proof (translation)
Introduce `R _ _ h`. Take `⟨A, _, _, i, hA, hinj, hf⟩` from `h`. Set `: Algebra A R` to `i.toAlgebra`. Establish `: Module.Finite A R` using `hf`. Establish `: IsDomain A` using `hA.dom`.

Establish `: IsIntegrallyClosed A` using `hA.normal`. Establish `: IsNoetherianRing A` using `hA.cm.1`. Establish `hinj' : Function.Injective (algebraMap A R)` using `hinj`. Establish `: FaithfulSMul A R` using `(faithfulSMul_iff_algebraMap_injective _ _).mpr hinj'`. Establish `: IsNoetherianRing R` using `Algebra.FiniteType.isNoetherianRing A R`.

Use `⟨this, fun q _ => ?_⟩` and prove the remaining obligations. Use `set p := q.comap (algebraMap A R) with hp`. Establish `: q.LiesOver p` using `⟨rfl⟩`. Establish `h1 : p.height ≤ q.height`. Rewrite using `[Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p q]`.

Conclude with `le_self_add`. Establish `h2 : q.height ≤ p.height`. Establish `e1` using `PrimeSpectrum.height_eq_orderHeight (⟨q, inferInstance⟩ : PrimeSpectrum R)`. Establish `e2` using `PrimeSpectrum.height_eq_orderHeight (⟨p, inferInstance⟩ : PrimeSpectrum A)`. Simplify using `only at e1 e2`.

Rewrite using `[e1, e2]`. Conclude with `Order.height_le_height_apply_of_strictMono (fun P : PrimeSpectrum R => (⟨P.asIdeal.comap (algebraMap A R), inferInstance⟩ : PrimeSpectrum A)) (fun P Q hPQ => Ideal.IsIntegral.comap_lt_comap (R := A) (show P.asIdeal < Q.asIdeal from hPQ)) _`. Rewrite using `[le_antisymm h2 h1, ReciprocityTheory.CA.ringKrullDim_quotient_eq_quotient_comap_of_isIntegral (A := A) q, hA.cm.height_add_ringKrullDim_quotient, ReciprocityTheory.CA.ringKrullDim_eq_of_isIntegral_of_injective hinj']`.
-/
theorem UpperTheory.V.AlgebraTools.Conn.dimFormula :
    ∀ {R : Type} [CommRing R] [IsDomain R], HasBase R → IsNoetherianRing R ∧ ReciprocityTheory.CA.DimFormula R := by
  intro R _ _ h
  obtain ⟨A, _, _, i, hA, hinj, hf⟩ := h
  let : Algebra A R := i.toAlgebra
  have : Module.Finite A R := hf
  have : IsDomain A := hA.dom
  have : IsIntegrallyClosed A := hA.normal
  have : IsNoetherianRing A := hA.cm.1
  have hinj' : Function.Injective (algebraMap A R) := hinj
  have : FaithfulSMul A R := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj'
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing A R
  refine ⟨this, fun q _ => ?_⟩
  set p := q.comap (algebraMap A R) with hp
  have : q.LiesOver p := ⟨rfl⟩
  have h1 : p.height ≤ q.height := by
    rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p q]
    exact le_self_add
  have h2 : q.height ≤ p.height := by
    have e1 := PrimeSpectrum.height_eq_orderHeight (⟨q, inferInstance⟩ : PrimeSpectrum R)
    have e2 := PrimeSpectrum.height_eq_orderHeight (⟨p, inferInstance⟩ : PrimeSpectrum A)
    simp only at e1 e2
    rw [e1, e2]
    exact Order.height_le_height_apply_of_strictMono
      (fun P : PrimeSpectrum R => (⟨P.asIdeal.comap (algebraMap A R),
        inferInstance⟩ : PrimeSpectrum A))
      (fun P Q hPQ => Ideal.IsIntegral.comap_lt_comap (R := A)
        (show P.asIdeal < Q.asIdeal from hPQ)) _
  rw [le_antisymm h2 h1,
    ReciprocityTheory.CA.ringKrullDim_quotient_eq_quotient_comap_of_isIntegral (A := A) q,
    hA.cm.height_add_ringKrullDim_quotient,
    ReciprocityTheory.CA.ringKrullDim_eq_of_isIntegral_of_injective hinj']
