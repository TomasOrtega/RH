import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemIdemSf
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

namespace GlobalTheory.SchurExt

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

/- English proof (translation)
The claim follows from `Prod.ext (one_mul _) (mul_zero _)`.
-/
theorem idemS_mul_sInf (S : Finset (HeightOneSpectrum (𝓞 E))) (x : Cinf E) : idemS S * sInf E x = sInf E x :=
  Prod.ext (one_mul _) (mul_zero _)

/- English proof (translation)
Rewrite using `[sub_mul, one_mul, idemS_mul_sInf, sub_self]`.
-/
theorem one_sub_idemS_mul_sInf (S : Finset (HeightOneSpectrum (𝓞 E))) (x : Cinf E) :
    (1 - idemS S) * sInf E x = 0 := by
  rw [sub_mul, one_mul, idemS_mul_sInf, sub_self]

/- English proof (translation)
Use extensionality with `i j`. Express the relevant statement in the definitionally equal form `(1 : Matrix (Fin a) (Fin a) (Ad E)) i j - idemS S * (1 : Matrix (Fin a) (Fin a) (Ad E)) i j + idemS S * ((1 : Matrix (Fin a) (Fin a) (Ad E)) i j - sInf E ((1 : Matrix (Fin a) (Fin a) (Cinf E)) i j) + sInf E (y i j)) = (1 : Matrix (Fin a) (Fin a) (Ad E)) i j - sInf E ((1 : Matrix …`. Rewrite using `[mul_add, mul_sub, idemS_mul_sInf, idemS_mul_sInf]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem prS_infGL (S : Finset (HeightOneSpectrum (𝓞 E))) (a : ℕ) (y : GL (Fin a) (Cinf E)) :
    prS S a (infGL E a y) = infGL E a y := by
  ext i j
  change (1 : Matrix (Fin a) (Fin a) (Ad E)) i j - idemS S * (1 : Matrix (Fin a) (Fin a) (Ad E)) i j +
      idemS S * ((1 : Matrix (Fin a) (Fin a) (Ad E)) i j - sInf E ((1 : Matrix (Fin a) (Fin a) (Cinf E)) i j) +
        sInf E (y i j)) =
    (1 : Matrix (Fin a) (Fin a) (Ad E)) i j - sInf E ((1 : Matrix (Fin a) (Fin a) (Cinf E)) i j) + sInf E (y i j)
  rw [mul_add, mul_sub, idemS_mul_sInf, idemS_mul_sInf]
  ring

/- English proof (translation)
Use extensionality with `i j`. Express the relevant statement in the definitionally equal form `(1 : Matrix (Fin a) (Fin a) (Ad E)) i j - (1 - idemS S) * (1 : Matrix (Fin a) (Fin a) (Ad E)) i j + (1 - idemS S) * ((1 : Matrix (Fin a) (Fin a) (Ad E)) i j - sInf E ((1 : Matrix (Fin a) (Fin a) (Cinf E)) i j) + sInf E (y i j)) = (1 : Matrix (Fin a) (Fin a) (Ad E)) i j`. Rewrite using `[mul_add, mul_sub, one_sub_idemS_mul_sInf, one_sub_idemS_mul_sInf]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem prO_infGL (S : Finset (HeightOneSpectrum (𝓞 E))) (a : ℕ) (y : GL (Fin a) (Cinf E)) :
    prO S a (infGL E a y) = 1 := by
  ext i j
  change (1 : Matrix (Fin a) (Fin a) (Ad E)) i j - (1 - idemS S) * (1 : Matrix (Fin a) (Fin a) (Ad E)) i j +
      (1 - idemS S) * ((1 : Matrix (Fin a) (Fin a) (Ad E)) i j - sInf E ((1 : Matrix (Fin a) (Fin a) (Cinf E)) i j) +
        sInf E (y i j)) =
    (1 : Matrix (Fin a) (Fin a) (Ad E)) i j
  rw [mul_add, mul_sub, one_sub_idemS_mul_sInf, one_sub_idemS_mul_sInf]
  ring

/- English proof (translation)
Introduce `E _ _ _ a S g y`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, prS_infGL]`. Rewrite using `[map_mul, prO_infGL, mul_one]`.
-/
theorem prS_prO_mul_infGL : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (g : GA E a) (y : GL (Fin a) (Cinf E)),
    prS S a (g * infGL E a y) = prS S a g * infGL E a y ∧ prO S a (g * infGL E a y) = prO S a g := by
  intro E _ _ _ a S g y
  refine ⟨?_, ?_⟩
  · rw [map_mul, prS_infGL]
  · rw [map_mul, prO_infGL, mul_one]

end GlobalTheory.SchurExt
