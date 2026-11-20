import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace ZeroLocusDimH

/- English proof (translation)
Break down `isEmpty_or_nonempty (PrimeSpectrum A) with hA | hA` into its components or cases. Rewrite using `[ringKrullDim, Order.krullDim_eq_bot]`. Conclude with `bot_le`. Rewrite using `[ringKrullDim, Order.krullDim_eq_iSup_length]`. Rewrite using `[WithBot.coe_iSup (OrderTop.bddAbove _)]`.

Use `iSup_le fun l => ?_` and prove the remaining obligations. Take `⟨P, -, hP, hPl⟩` from `Ideal.exists_ideal_over_prime_of_isIntegral l.head.asIdeal (⊥ : Ideal R) (by rw [← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).1 h]; exact bot_le)`. Establish `: P.LiesOver l.head.asIdeal` using `⟨hPl.symm⟩`. Take `⟨L, hL, -, -⟩` from `Ideal.exists_ltSeries_of_hasGoingUp l P`. Rewrite using `[← hL]`.

Conclude with `Order.LTSeries.length_le_krullDim L`.
-/
theorem ringKrullDim_le_of_isIntegral_inj {A R : Type*} [CommRing A] [CommRing R] [Algebra A R]
    [Algebra.IsIntegral A R] (h : Function.Injective (algebraMap A R)) :
    ringKrullDim A ≤ ringKrullDim R := by
  rcases isEmpty_or_nonempty (PrimeSpectrum A) with hA | hA
  · rw [ringKrullDim, Order.krullDim_eq_bot]
    exact bot_le
  rw [ringKrullDim, Order.krullDim_eq_iSup_length]
  rw [WithBot.coe_iSup (OrderTop.bddAbove _)]
  refine iSup_le fun l => ?_
  obtain ⟨P, -, hP, hPl⟩ := Ideal.exists_ideal_over_prime_of_isIntegral l.head.asIdeal (⊥ : Ideal R)
    (by rw [← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).1 h]; exact bot_le)
  have : P.LiesOver l.head.asIdeal := ⟨hPl.symm⟩
  obtain ⟨L, hL, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P
  rw [← hL]
  exact Order.LTSeries.length_le_krullDim L

/- English proof (translation)
Establish `: Module.IsTorsionFree R A` using `Module.isTorsionFree_iff_algebraMap_injective.2 hinj`. Establish `hx : IsIntegral R x` using `Algebra.IsIntegral.isIntegral x`. Introduce `h0`. Establish `hdvd` using `minpoly.isIntegrallyClosed_dvd hx h0`. Establish `hmon` using `minpoly.monic hx`.

Establish `hne : Polynomial.derivative (minpoly R x) ≠ 0`. Introduce `hd`. Conclude with `(minpoly.natDegree_pos hx).ne' (Polynomial.derivative_eq_zero.1 hd)`. Establish `h1` using `Polynomial.degree_le_of_dvd hdvd hne`. Establish `h2` using `Polynomial.degree_derivative_lt hmon.ne_zero`.

Conclude with `absurd h1 (not_le.2 h2)`.
-/
theorem aeval_derivative_minpoly_ne_zero {R A : Type*} [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] [CharZero R] [CommRing A] [IsDomain A] [Algebra R A]
    [Algebra.IsIntegral R A] (hinj : Function.Injective (algebraMap R A)) (x : A) :
    Polynomial.aeval x (Polynomial.derivative (minpoly R x)) ≠ 0 := by
  have : Module.IsTorsionFree R A := Module.isTorsionFree_iff_algebraMap_injective.2 hinj
  have hx : IsIntegral R x := Algebra.IsIntegral.isIntegral x
  intro h0
  have hdvd := minpoly.isIntegrallyClosed_dvd hx h0
  have hmon := minpoly.monic hx
  have hne : Polynomial.derivative (minpoly R x) ≠ 0 := by
    intro hd
    exact (minpoly.natDegree_pos hx).ne' (Polynomial.derivative_eq_zero.1 hd)
  have h1 := Polynomial.degree_le_of_dvd hdvd hne
  have h2 := Polynomial.degree_derivative_lt hmon.ne_zero
  exact absurd h1 (not_le.2 h2)

/- English proof (translation)
Establish `: Nontrivial (MvPolynomial (Fin n) ℂ ⧸ p)` using `Ideal.Quotient.nontrivial_iff.2 hp.ne_top`. Take `⟨s, g, hinj, hint⟩` from `exists_integral_inj_algHom_of_fg ℂ (MvPolynomial (Fin n) ℂ ⧸ p)`. Set `_ : Algebra (MvPolynomial (Fin s) ℂ) (MvPolynomial (Fin n) ℂ ⧸ p)` to `g.toRingHom.toAlgebra`. Establish `: Algebra.IsIntegral (MvPolynomial (Fin s) ℂ) (MvPolynomial (Fin n) ℂ ⧸ p)` using `⟨hint⟩`. Establish `hdim : ringKrullDim (MvPolynomial (Fin s) ℂ) = s`.

Rewrite using `[MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]`. Simplify using the standard rewrite rules. Use `⟨s, hdim ▸ ringKrullDim_le_of_isIntegral_inj hinj, ?_⟩` and prove the remaining obligations. Use `choose π hπ using fun j : Fin s => Ideal.Quotient.mk_surjective (I := p) (g (X j))`. Establish `hcomp : (Ideal.Quotient.mk p).comp (MvPolynomial.aeval π).toRingHom = algebraMap (MvPolynomial (Fin s) ℂ) (MvPolynomial (Fin n) ℂ ⧸ p)`.

Use `MvPolynomial.ringHom_ext (fun a => ?_) (fun j => ?_)` and prove the remaining obligations. Simplify using `only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_C]`. Express the relevant statement in the definitionally equal form `_ = g (C a)`. Rewrite using `[← MvPolynomial.algebraMap_eq, g.commutes]`. Both sides reduce to the same expression.

Simplify using `only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_X]`. Conclude with `hπ j`. Establish `hkey : ∀ (Q : Polynomial (MvPolynomial (Fin s) ℂ)) (i : Fin n), Ideal.Quotient.mk p (Q.eval₂ (MvPolynomial.aeval π).toRingHom (X i)) = Polynomial.aeval (Ideal.Quotient.mk p (X i)) Q`. Introduce `Q i`. Rewrite using `[Polynomial.hom_eval₂, hcomp, Polynomial.aeval_def]`.

Establish `hx : ∀ i : Fin n, IsIntegral (MvPolynomial (Fin s) ℂ) (Ideal.Quotient.mk p (X i))` using `fun i => Algebra.IsIntegral.isIntegral _`. Use `⟨π, fun i => minpoly (MvPolynomial (Fin s) ℂ) (Ideal.Quotient.mk p (X i)), fun i => ?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, hkey, minpoly.aeval]`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, hkey]`. Conclude with `aeval_derivative_minpoly_ne_zero hinj _`.
-/
theorem exists_simple_root_data {n : ℕ} (p : Ideal (MvPolynomial (Fin n) ℂ)) [hp : p.IsPrime] :
    ∃ s : ℕ, (s : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ p) ∧
    ∃ (π : Fin s → MvPolynomial (Fin n) ℂ) (P : Fin n → Polynomial (MvPolynomial (Fin s) ℂ)),
      (∀ i, (P i).eval₂ (MvPolynomial.aeval π).toRingHom (X i) ∈ p) ∧
      (∀ i, (Polynomial.derivative (P i)).eval₂ (MvPolynomial.aeval π).toRingHom (X i) ∉ p) := by
  have : Nontrivial (MvPolynomial (Fin n) ℂ ⧸ p) := Ideal.Quotient.nontrivial_iff.2 hp.ne_top
  obtain ⟨s, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg ℂ (MvPolynomial (Fin n) ℂ ⧸ p)
  let _ : Algebra (MvPolynomial (Fin s) ℂ) (MvPolynomial (Fin n) ℂ ⧸ p) := g.toRingHom.toAlgebra
  have : Algebra.IsIntegral (MvPolynomial (Fin s) ℂ) (MvPolynomial (Fin n) ℂ ⧸ p) := ⟨hint⟩
  have hdim : ringKrullDim (MvPolynomial (Fin s) ℂ) = s := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  refine ⟨s, hdim ▸ ringKrullDim_le_of_isIntegral_inj hinj, ?_⟩
  choose π hπ using fun j : Fin s => Ideal.Quotient.mk_surjective (I := p) (g (X j))
  have hcomp : (Ideal.Quotient.mk p).comp (MvPolynomial.aeval π).toRingHom =
      algebraMap (MvPolynomial (Fin s) ℂ) (MvPolynomial (Fin n) ℂ ⧸ p) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun j => ?_)
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        MvPolynomial.aeval_C]
      change _ = g (C a)
      rw [← MvPolynomial.algebraMap_eq, g.commutes]
      rfl
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        MvPolynomial.aeval_X]
      exact hπ j
  have hkey : ∀ (Q : Polynomial (MvPolynomial (Fin s) ℂ)) (i : Fin n),
      Ideal.Quotient.mk p (Q.eval₂ (MvPolynomial.aeval π).toRingHom (X i)) =
        Polynomial.aeval (Ideal.Quotient.mk p (X i)) Q := by
    intro Q i
    rw [Polynomial.hom_eval₂, hcomp, Polynomial.aeval_def]
  have hx : ∀ i : Fin n, IsIntegral (MvPolynomial (Fin s) ℂ) (Ideal.Quotient.mk p (X i)) :=
    fun i => Algebra.IsIntegral.isIntegral _
  refine ⟨π, fun i => minpoly (MvPolynomial (Fin s) ℂ) (Ideal.Quotient.mk p (X i)), fun i => ?_,
    fun i => ?_⟩
  · rw [← Ideal.Quotient.eq_zero_iff_mem, hkey, minpoly.aeval]
  · rw [← Ideal.Quotient.eq_zero_iff_mem, hkey]
    exact aeval_derivative_minpoly_ne_zero hinj _

end ZeroLocusDimH

end

end GroundTheory.Heights₂.Heights
