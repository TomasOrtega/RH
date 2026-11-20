import Formalism.GradedWeylDivisibility.StatementA

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

/- English proof (translation)
Simplify using `only [dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, AlgHom.toLinearMap_apply, sub_eq_zero, mem_weightedHomogeneousSubmodule]`.
-/
theorem lsat_mem_dualWeyl {R : Type*} [CommRing R] {r n : ℕ} {ν : Fin n → ℕ}
    {f : MvPolynomial (Fin r × Fin n) R} :
    f ∈ dualWeyl R r n ν ↔ IsWeightedHomogeneous (colW r n) f ν ∧
      ∀ l j : Fin n, l < j → colAddGen R l j f = rename some f := by
  simp only [dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    AlgHom.toLinearMap_apply, sub_eq_zero, mem_weightedHomogeneousSubmodule]

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on`. Use `next a =>`. Simplify using `[colAddGen]`. Use `next p q hp hq =>`. Simplify using `only [map_add, hp, hq]`.

Use `next p v hp =>`. Simplify using `only [map_mul, hp, map_X]`. Use `congr 1`. Simplify using `only [colAddGen, aeval_X]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem lsat_map_colAddGen {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {r n : ℕ}
    (l j : Fin n) (f : MvPolynomial (Fin r × Fin n) R) :
    map φ (colAddGen R l j f) = colAddGen S l j (map φ f) := by
  induction f using MvPolynomial.induction_on
  next a =>
    simp [colAddGen]
  next p q hp hq =>
    simp only [map_add, hp, hq]
  next p v hp =>
    simp only [map_mul, hp, map_X]
    congr 1
    simp only [colAddGen, aeval_X]
    split_ifs <;> simp

/- English proof (translation)
Introduce `d hd`. Apply `hf` to reduce the goal to its premises. Introduce `h0`. Apply `hd` to reduce the goal to its premises. Rewrite using `[coeff_map, h0, map_zero]`.
-/
theorem lsat_isWH_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {σ M : Type*}
    [AddCommMonoid M] (w : σ → M) (m : M) (f : MvPolynomial σ R)
    (hf : IsWeightedHomogeneous w f m) : IsWeightedHomogeneous w (map φ f) m := by
  intro d hd
  apply hf
  intro h0
  apply hd
  rw [coeff_map, h0, map_zero]

end Formalism.GradedWeylDivisibility
