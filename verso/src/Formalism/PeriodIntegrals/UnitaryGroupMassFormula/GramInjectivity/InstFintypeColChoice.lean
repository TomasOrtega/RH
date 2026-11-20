import Mathlib
import Formalism.PeriodIntegrals.WwInjective
import Formalism.PeriodIntegrals.WwCauchyBinet
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramInjectivity.GramVanish

noncomputable section

namespace PI.WwInjectiveWork

open MvPolynomial PI.WwInjective PI.WwInjective.KM

variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N : ℕ) (nu : Lt → YoungDiagram)

noncomputable instance instFintypeColChoice : Fintype (ColChoice N nu) := by
  unfold ColChoice; infer_instance

/- English proof (translation)
Unfold `nablaX minY`. Simplify using `only [map_prod, RingHom.map_det]`. Use `Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[← Matrix.det_transpose]`. Use `congr 1`.

Use extensionality with `i j`. Simplify using `[Matrix.transpose_apply, RingHom.mapMatrix_apply, Matrix.map_apply]`.
-/
theorem eval_map_nablaX {K : Type} [CommRing K] (J : ColChoice N nu)
    (pt : Lt × ℕ × Fin N → K) :
    eval pt (map (Int.castRingHom K) (nablaX N nu J)) = minY N nu J (fun s a i => pt (s, i, a)) := by
  unfold nablaX minY
  simp only [map_prod, RingHom.map_det]
  refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => ?_
  rw [← Matrix.det_transpose]
  congr 1
  ext i j
  simp [Matrix.transpose_apply, RingHom.mapMatrix_apply, Matrix.map_apply]

/- English proof (translation)
Establish `h` using `hCB Lt K N nu y`. Establish `h' : (∑ᶠ J : ColChoice N nu, C (minY N nu J y) * map (Int.castRingHom K) (nablaX N nu J)) = ∑ J : ColChoice N nu, C (minY N nu J y) * map (Int.castRingHom K) (nablaX N nu J)` using `finsum_eq_sum_of_fintype _`. Rewrite using `[← h']`. Conclude with `h`.
-/
theorem deX_eq_sum (hCB : PI.WwCauchyBinet.WwCauchyBinet) {K : Type} [CommRing K]
    (y : Lt → Fin N → ℕ → K) :
    DeX N nu y = ∑ J : ColChoice N nu, C (minY N nu J y) *
      map (Int.castRingHom K) (nablaX N nu J) := by
  have h := hCB Lt K N nu y
  have h' : (∑ᶠ J : ColChoice N nu, C (minY N nu J y) * map (Int.castRingHom K) (nablaX N nu J)) =
      ∑ J : ColChoice N nu, C (minY N nu J y) * map (Int.castRingHom K) (nablaX N nu J) :=
    finsum_eq_sum_of_fintype _
  rw [← h']
  exact h

/- English proof (translation)
Use `haveI : Infinite ℂ_[l] := Infinite.of_injective (Nat.cast : ℕ → ℂ_[l]) Nat.cast_injective`. Apply `MvPolynomial.funext` to reduce the goal to its premises. Introduce `x`. Establish `hx` using `hph (fun s a i => x (s, i, a))`. Rewrite `hx` using `[deX_eq_sum N nu hCB, map_sum]`.

Simplify using `only [MvPolynomial.C_mul', map_smul, smul_eq_mul] at hx`. Simplify using `only [map_sum, MvPolynomial.smul_eq_C_mul, MvPolynomial.eval_mul, MvPolynomial.eval_C, eval_map_nablaX, map_zero]`. Use `Eq.trans ?_ hx` and prove the remaining obligations. Conclude with `Finset.sum_congr rfl fun J _ => mul_comm _ _`.
-/
theorem sum_smul_eq_zero (hCB : PI.WwCauchyBinet.WwCauchyBinet) (l : ℕ) [Fact l.Prime]
    (ph : Module.Dual ℂ_[l] (MvPolynomial (Lt × ℕ × Fin N) ℂ_[l]))
    (hph : ∀ y, ph (DeX N nu y) = 0) :
    ∑ J : ColChoice N nu, ph (map (Int.castRingHom ℂ_[l]) (nablaX N nu J)) •
      map (Int.castRingHom ℂ_[l]) (nablaX N nu J) = 0 := by
  haveI : Infinite ℂ_[l] := Infinite.of_injective (Nat.cast : ℕ → ℂ_[l]) Nat.cast_injective
  apply MvPolynomial.funext
  intro x
  have hx := hph (fun s a i => x (s, i, a))
  rw [deX_eq_sum N nu hCB, map_sum] at hx
  simp only [MvPolynomial.C_mul', map_smul, smul_eq_mul] at hx
  simp only [map_sum, MvPolynomial.smul_eq_C_mul, MvPolynomial.eval_mul, MvPolynomial.eval_C,
    eval_map_nablaX, map_zero]
  refine Eq.trans ?_ hx
  exact Finset.sum_congr rfl fun J _ => mul_comm _ _

/- English proof (translation)
Unfold `PI.WwInjective.WwInjective`. Introduce `Lt _ _ l _ N nu ph hph J`. Conclude with `gram_vanish (fun J => nablaX N nu J) ph (sum_smul_eq_zero N nu hCB l ph hph) J`.
-/
theorem wwInjective_of (hCB : PI.WwCauchyBinet.WwCauchyBinet) : PI.WwInjective.WwInjective := by
  unfold PI.WwInjective.WwInjective
  intro Lt _ _ l _ N nu ph hph J
  exact gram_vanish (fun J => nablaX N nu J) ph (sum_smul_eq_zero N nu hCB l ph hph) J

end PI.WwInjectiveWork
