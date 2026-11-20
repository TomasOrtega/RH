import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.FieldPair

/- English proof (translation)
Introduce `L K _ _ cL cK Q hQ S ψ F hSQ hc hF m z zs hz hu P hP`. Set `j : Q →+* S.ring` to `Q.subtype.codRestrict S.ring fun q => hSQ q q.2`. Establish `h1 : (ψ.comp j).comp (cL.codRestrict Q hQ.const_mem) = cK` using `RingHom.ext fun a => hc a`. Establish `h2 : (fun i => (ψ.comp j) (z i)) = fun i => ψ (zs i)`. Use function extensionality and compare the values at `fun i => congrArg ψ (Subtype.ext (hz i).symm)`.

Establish `h3 : (ψ.comp j) (MvPolynomial.eval₂ (cL.codRestrict Q hQ.const_mem) z P) = MvPolynomial.eval₂ cK (fun i => ψ (zs i)) P`. Rewrite using `[MvPolynomial.hom_eval₂, h1, h2]`. Take `⟨q, hq⟩` from `(hu P hP).exists_right_inv`. Establish `h4 : MvPolynomial.eval₂ cK (fun i => ψ (zs i)) P * (ψ.comp j) q = 1`. Rewrite using `[← h3, ← map_mul, hq, map_one]`.

Use `⟨left_ne_zero_of_mul_eq_one h4, ?_⟩` and prove the remaining obligations. Rewrite using `[← eq_inv_of_mul_eq_one_right h4]`. Conclude with `(hF _).2 ⟨j q, q.2, rfl⟩`.
-/
theorem eval₂_residue_ne_zero_and_inv_mem_of_isUnit :
    ∀ {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K) (Q : Subring L) (hQ : IsLocModel cL Q)
  (S : Place cL) (ψ : S.ring →+* K) (F : Place cK), S.Contains Q → (∀ a, ψ (S.const a) = cK a) →
  (∀ a : K, a ∈ F.ring ↔ ∃ q : S.ring, (q : L) ∈ Q ∧ ψ q = a) →
  ∀ (m : ℕ) (z : Fin m → Q) (zs : Fin m → S.ring), (∀ i, (zs i : L) = z i) →
  (∀ P : MvPolynomial (Fin m) ℂ, P ≠ 0 → IsUnit (MvPolynomial.eval₂ (cL.codRestrict Q hQ.const_mem) z P)) →
  ∀ P : MvPolynomial (Fin m) ℂ, P ≠ 0 → MvPolynomial.eval₂ cK (fun i => ψ (zs i)) P ≠ 0 ∧
    (MvPolynomial.eval₂ cK (fun i => ψ (zs i)) P)⁻¹ ∈ F.ring := by
  intro L K _ _ cL cK Q hQ S ψ F hSQ hc hF m z zs hz hu P hP
  let j : Q →+* S.ring := Q.subtype.codRestrict S.ring fun q => hSQ q q.2
  have h1 : (ψ.comp j).comp (cL.codRestrict Q hQ.const_mem) = cK := RingHom.ext fun a => hc a
  have h2 : (fun i => (ψ.comp j) (z i)) = fun i => ψ (zs i) :=
    funext fun i => congrArg ψ (Subtype.ext (hz i).symm)
  have h3 : (ψ.comp j) (MvPolynomial.eval₂ (cL.codRestrict Q hQ.const_mem) z P) =
      MvPolynomial.eval₂ cK (fun i => ψ (zs i)) P := by
    rw [MvPolynomial.hom_eval₂, h1, h2]
  obtain ⟨q, hq⟩ := (hu P hP).exists_right_inv
  have h4 : MvPolynomial.eval₂ cK (fun i => ψ (zs i)) P * (ψ.comp j) q = 1 := by
    rw [← h3, ← map_mul, hq, map_one]
  refine ⟨left_ne_zero_of_mul_eq_one h4, ?_⟩
  rw [← eq_inv_of_mul_eq_one_right h4]
  exact (hF _).2 ⟨j q, q.2, rfl⟩

end GlobalTheory.FieldPair
