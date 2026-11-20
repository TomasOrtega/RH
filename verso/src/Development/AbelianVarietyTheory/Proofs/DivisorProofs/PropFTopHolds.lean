import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentMapIsIntegral
open GlobalTheory.EtC.GmStep

namespace GlobalTheory.EtC.GmStep

/- English proof (translation)
Introduce `n B _`. Establish `hap : ∀ (x : LaurentPolynomial (∀ j, B j)) k, (Pi.ringHom (fun j => laurentMap (Pi.evalRingHom B j)) : LaurentPolynomial (∀ j, B j) →+* ∀ j, LaurentPolynomial (B j)) x k = laurentMap (Pi.evalRingHom B k) x` using `fun _ _ => rfl`. Prove the components needed by the constructor for the conclusion. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `p hp`.

Establish `hc : p.coeff = 0`. Use extensionality with `m j`. Establish `h1` using `congrArg (fun r : ∀ j, LaurentPolynomial (B j) => (r j).coeff m) hp`. Simplify using `only [hap, Pi.zero_apply, laurentMap_coeff, Finsupp.mapRange_apply] at h1`. Simplify using `using h1`.

Conclude with `AddMonoidAlgebra.ext hc`. Introduce `F`. Establish `hsub : ∀ j (q : LaurentPolynomial (B j)), Pi.single j q ∈ (Pi.ringHom (fun j => laurentMap (Pi.evalRingHom B j)) : LaurentPolynomial (∀ j, B j) →+* ∀ j, LaurentPolynomial (B j)).range`. Introduce `j q`. Proceed by induction on `q using LaurentPolynomial.induction_on' with`.

Consider the case `add p r hp hr`. Rewrite using `[Pi.single_add]`. Conclude with `Subring.add_mem _ hp hr`. Consider the case `C_mul_T m a`. Use `⟨LaurentPolynomial.C (Pi.single j a) * LaurentPolynomial.T m, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `k`. Simplify using `only [hap, map_mul, laurentMap_C, laurentMap_T, Pi.evalRingHom_apply]`. Distinguish the cases in `hk : k = j`. Substitute `hk` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[Pi.single_eq_of_ne hk]`. Rewrite using `[← Finset.univ_sum_single F]`. Take `⟨p, hp⟩` from `Subring.sum_mem _ (fun j (_ : j ∈ Finset.univ) => hsub j (F j))`. Conclude with `⟨p, hp⟩`.
-/
theorem laurentPi_bijective : ∀ (n : ℕ) (B : Fin n → Type) [∀ j, CommRing (B j)], Function.Bijective (Pi.ringHom (fun j => laurentMap (Pi.evalRingHom B j)) : LaurentPolynomial (∀ j, B j) →+* ∀ j, LaurentPolynomial (B j)) := by
  intro n B _
  have hap : ∀ (x : LaurentPolynomial (∀ j, B j)) k, (Pi.ringHom (fun j => laurentMap (Pi.evalRingHom B j)) : LaurentPolynomial (∀ j, B j) →+* ∀ j, LaurentPolynomial (B j)) x k = laurentMap (Pi.evalRingHom B k) x := fun _ _ => rfl
  constructor
  · rw [injective_iff_map_eq_zero]
    intro p hp
    have hc : p.coeff = 0 := by
      ext m j
      have h1 := congrArg (fun r : ∀ j, LaurentPolynomial (B j) => (r j).coeff m) hp
      simp only [hap, Pi.zero_apply, laurentMap_coeff, Finsupp.mapRange_apply] at h1
      simpa using h1
    exact AddMonoidAlgebra.ext hc
  · intro F
    have hsub : ∀ j (q : LaurentPolynomial (B j)), Pi.single j q ∈ (Pi.ringHom (fun j => laurentMap (Pi.evalRingHom B j)) : LaurentPolynomial (∀ j, B j) →+* ∀ j, LaurentPolynomial (B j)).range := by
      intro j q
      induction q using LaurentPolynomial.induction_on' with
      | add p r hp hr =>
        rw [Pi.single_add]; exact Subring.add_mem _ hp hr
      | C_mul_T m a =>
        refine ⟨LaurentPolynomial.C (Pi.single j a) * LaurentPolynomial.T m, ?_⟩
        funext k
        simp only [hap, map_mul, laurentMap_C, laurentMap_T, Pi.evalRingHom_apply]
        by_cases hk : k = j
        · subst hk; simp
        · simp [Pi.single_eq_of_ne hk]
    rw [← Finset.univ_sum_single F]
    obtain ⟨p, hp⟩ := Subring.sum_mem _ (fun j (_ : j ∈ Finset.univ) => hsub j (F j))
    exact ⟨p, hp⟩

end GlobalTheory.EtC.GmStep
