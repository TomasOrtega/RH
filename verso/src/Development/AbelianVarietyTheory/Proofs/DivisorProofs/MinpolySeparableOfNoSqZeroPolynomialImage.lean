import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical ComplexOrder

namespace GlobalTheory.LKCx

/- English proof (translation)
Use `haveI : CharZero F := (RingHom.charZero_iff σ.injective).2 inferInstance`. Use `haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩`. Establish `hinj : Function.Injective ψ` using `ψ.injective`. Establish `hcomp : ψ.comp (algebraMap F C) = (algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ)).comp σ`. Use extensionality with `x`.

Simplify using `only [RingHom.comp_apply, hψ, Matrix.algebraMap_eq_diagonal, Matrix.scalar_apply]`. Both sides reduce to the same expression. Establish `hev : ∀ Q : Polynomial F, ψ (Polynomial.aeval c Q) = Polynomial.aeval (ψ c) (Q.map σ)`. Introduce `Q`. Rewrite using `[Polynomial.aeval_def, Polynomial.hom_eval₂, hcomp, Polynomial.aeval_def, Polynomial.eval₂_map]`.

Establish `hint : IsIntegral F c` using `IsIntegral.of_finite F c`. Establish `hm0 : minpoly F c ≠ 0` using `minpoly.ne_zero hint`. Rewrite using `[PerfectField.separable_iff_squarefree]`. Introduce `g hg`. Take `⟨h, hh⟩` from `hg`.

Establish `hQ : Polynomial.aeval c (g * h) = 0`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_zero, hev]`. Apply `hc` to reduce the goal to its premises. Rewrite using `[← hev, ← map_mul, ← map_mul]`.

Establish `: g * h * (g * h) = minpoly F c * h` using `by rw [hh]; ring`. Rewrite using `[this, map_mul, minpoly.aeval, zero_mul, map_zero]`. Establish `hdvd : minpoly F c ∣ g * h` using `minpoly.dvd F c hQ`. Establish `hgh0 : g * h ≠ 0`. Introduce `h0`.

Apply `hm0` to reduce the goal to its premises. Rewrite using `[hh, mul_assoc, h0, mul_zero]`. Rewrite `hdvd` using `[hh, mul_assoc]`. Establish `: g * (g * h) ∣ 1 * (g * h)` using `by rwa [one_mul]`. Conclude with `isUnit_of_dvd_one ((mul_dvd_mul_iff_right hgh0).1 this)`.
-/
theorem minpoly_separable_of_sq_zero_free
    (F C : Type) [Field F] [Ring C] [IsSimpleRing C] [Algebra F C] [FiniteDimensional F C]
    (n : ℕ) (σ : F →+* ℂ) (ψ : C →+* Matrix (Fin n) (Fin n) ℂ) (hn : 0 < n)
    (hψ : ∀ x : F, ψ (algebraMap F C x) = Matrix.scalar (Fin n) (σ x)) (c : C)
    (hc : ∀ P : Polynomial ℂ, Polynomial.aeval (ψ c) P * Polynomial.aeval (ψ c) P = 0 →
      Polynomial.aeval (ψ c) P = 0) :
    (minpoly F c).Separable := by
  haveI : CharZero F := (RingHom.charZero_iff σ.injective).2 inferInstance
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hinj : Function.Injective ψ := ψ.injective
  have hcomp : ψ.comp (algebraMap F C) = (algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ)).comp σ := by
    ext x
    simp only [RingHom.comp_apply, hψ, Matrix.algebraMap_eq_diagonal, Matrix.scalar_apply]
    rfl
  have hev : ∀ Q : Polynomial F, ψ (Polynomial.aeval c Q) = Polynomial.aeval (ψ c) (Q.map σ) := by
    intro Q
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂, hcomp, Polynomial.aeval_def,
      Polynomial.eval₂_map]
  have hint : IsIntegral F c := IsIntegral.of_finite F c
  have hm0 : minpoly F c ≠ 0 := minpoly.ne_zero hint
  rw [PerfectField.separable_iff_squarefree]
  intro g hg
  obtain ⟨h, hh⟩ := hg
  have hQ : Polynomial.aeval c (g * h) = 0 := by
    apply hinj
    rw [map_zero, hev]
    apply hc
    rw [← hev, ← map_mul, ← map_mul]
    have : g * h * (g * h) = minpoly F c * h := by rw [hh]; ring
    rw [this, map_mul, minpoly.aeval, zero_mul, map_zero]
  have hdvd : minpoly F c ∣ g * h := minpoly.dvd F c hQ
  have hgh0 : g * h ≠ 0 := by
    intro h0
    apply hm0
    rw [hh, mul_assoc, h0, mul_zero]
  rw [hh, mul_assoc] at hdvd
  have : g * (g * h) ∣ 1 * (g * h) := by rwa [one_mul]
  exact isUnit_of_dvd_one ((mul_dvd_mul_iff_right hgh0).1 this)

end GlobalTheory.LKCx
