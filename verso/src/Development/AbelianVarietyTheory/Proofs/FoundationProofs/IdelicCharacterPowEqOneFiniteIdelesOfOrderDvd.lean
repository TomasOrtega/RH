import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIdeleExistsLocalApprox
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharEqProdLocalComponentsApproximating
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdelesStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CharOrderFin

/- English proof (translation)
Establish `h1 : (χ.1 : _ →* ℂˣ) ^ n = 1`. Use `congrArg Subtype.val h` as an intermediate fact. Simplify using `using this`. Establish `h2 : ∀ y, χ.1 y ^ n = 1` using `fun y => by`. Use `DFunLike.congr_fun h1 y` as an intermediate fact.

Simplify `this` using `[MonoidHom.pow_apply]`. Conclude with `h2 _`.
-/
theorem locK_pow_eq_one {L : Type} [Field L] [NumberField L] {χ : HChar L} {n : ℕ}
    (h : χ.OrderDvd n) (P : HeightOneSpectrum (𝓞 L)) (k : Lˣ) : χ.locK P k ^ n = 1 := by
  have h1 : (χ.1 : _ →* ℂˣ) ^ n = 1 := by
    have := congrArg Subtype.val h
    simpa using this
  have h2 : ∀ y, χ.1 y ^ n = 1 := fun y => by
    have := DFunLike.congr_fun h1 y
    simpa [MonoidHom.pow_apply] using this
  exact h2 _

/- English proof (translation)
Introduce `D c χ hc n hn x hx`. Take `⟨ι, h1, h2, h3⟩` from `GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D`. Establish `h4` using `GlobalTheory.T.exists_finitePlaceIdempotent_baseChangeAdeles D ι h1 h2 h3`. Take `⟨N, hN, hprod⟩` from `GlobalTheory.CharLocProd.char_eq_prod_locK D ι h1 h2 h4 c χ hc`. Set `y : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ` to `⟨ι (finPart D (x : AE D)), ι (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)), by rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one], by rw [← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]⟩`.

Take `⟨S, k, hS, hS'⟩` from `GlobalTheory.finiteIdele_exists_local_approx D.host.E N hN y`. Establish `h5` using `hprod x hx S k (fun P hP => ⟨(hS P hP).1, (hS P hP).2.1⟩) hS'`. Apply `Circle.ext` to reduce the goal to its premises. Establish `h6 : ((c x ^ n : Circle) : ℂ) = ((c x : Circle) : ℂ) ^ n` using `map_pow Circle.coeHom (c x) n`. Rewrite using `[h6, h5, ← Finset.prod_pow, Circle.coe_one]`.

Use `Finset.prod_eq_one fun P _ => ?_` and prove the remaining obligations. Rewrite using `[← Units.val_pow_eq_pow_val, locK_pow_eq_one hn, Units.val_one]`.
-/
theorem char_pow_eq_one_of_orderDvd : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : HChar D.host.E),
    ChrEq c χ → ∀ n : ℕ, χ.OrderDvd n → ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → c x ^ n = 1 := by
  intro D c χ hc n hn x hx
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  have h4 := GlobalTheory.T.exists_finitePlaceIdempotent_baseChangeAdeles D ι h1 h2 h3
  obtain ⟨N, hN, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D ι h1 h2 h4 c χ hc
  let y : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ :=
    ⟨ι (finPart D (x : AE D)), ι (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)),
      by rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one],
      by rw [← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]⟩
  obtain ⟨S, k, hS, hS'⟩ := GlobalTheory.finiteIdele_exists_local_approx D.host.E N hN y
  have h5 := hprod x hx S k (fun P hP => ⟨(hS P hP).1, (hS P hP).2.1⟩) hS'
  apply Circle.ext
  have h6 : ((c x ^ n : Circle) : ℂ) = ((c x : Circle) : ℂ) ^ n :=
    map_pow Circle.coeHom (c x) n
  rw [h6, h5, ← Finset.prod_pow, Circle.coe_one]
  refine Finset.prod_eq_one fun P _ => ?_
  rw [← Units.val_pow_eq_pow_val, locK_pow_eq_one hn, Units.val_one]

end GlobalTheory.CharOrderFin
