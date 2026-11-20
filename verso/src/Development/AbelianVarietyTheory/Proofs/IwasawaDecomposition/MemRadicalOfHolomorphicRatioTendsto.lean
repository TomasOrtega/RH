import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicArcSmoothAlgebraNonvanishingStatement
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo

open GlobalTheory.ShFam.BdArc Filter Topology

namespace GlobalTheory.ShFam.BdArc

/- English proof (translation)
Establish `: IsJacobsonRing A` using `isJacobsonRing_of_finiteType (A := F)`. Establish `hj : P.jacobson = P` using `IsJacobsonRing.out inferInstance hP.isRadical`. Rewrite `hs` using `[← hj, Ideal.jacobson, Ideal.mem_sInf]`. Use `push Not at hs`. Take `⟨M, ⟨hle, hM⟩, hsM⟩` from `hs`.

Set `_ : Field (A ⧸ M)` to `Ideal.Quotient.field M`. Establish `: Module.Finite F (A ⧸ M)` using `finite_of_finite_type_of_isJacobsonRing F (A ⧸ M)`. Set `_ : Algebra F ℂ` to `σ.toAlgebra`. Set `κ : (A ⧸ M) →ₐ[F] ℂ` to `IsAlgClosed.lift`. Use `⟨(κ.comp (Ideal.Quotient.mkₐ F M)).toRingHom, ?_, fun x hx => ?_, ?_⟩` and prove the remaining obligations.

Use extensionality with `x`. Conclude with `(κ.comp (Ideal.Quotient.mkₐ F M)).commutes x`. Use `show κ (Ideal.Quotient.mk M x) = 0`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem.2 (hle hx), map_zero]`. Use `show κ (Ideal.Quotient.mk M s) ≠ 0`.

Rewrite using `[map_ne_zero, Ne, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hsM`.
-/
theorem exists_complexPoint_of_notMem {F A : Type} [Field F] [CommRing A] [Algebra F A] [Algebra.FiniteType F A]
    (σ : F →+* ℂ) (P : Ideal A) [hP : P.IsPrime] {s : A} (hs : s ∉ P) :
    ∃ ψ : A →+* ℂ, ψ.comp (algebraMap F A) = σ ∧ (∀ x ∈ P, ψ x = 0) ∧ ψ s ≠ 0 := by
  have : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := F)
  have hj : P.jacobson = P := IsJacobsonRing.out inferInstance hP.isRadical
  rw [← hj, Ideal.jacobson, Ideal.mem_sInf] at hs
  push Not at hs
  obtain ⟨M, ⟨hle, hM⟩, hsM⟩ := hs
  let _ : Field (A ⧸ M) := Ideal.Quotient.field M
  have : Module.Finite F (A ⧸ M) := finite_of_finite_type_of_isJacobsonRing F (A ⧸ M)
  let _ : Algebra F ℂ := σ.toAlgebra
  let κ : (A ⧸ M) →ₐ[F] ℂ := IsAlgClosed.lift
  refine ⟨(κ.comp (Ideal.Quotient.mkₐ F M)).toRingHom, ?_, fun x hx => ?_, ?_⟩
  · ext x
    exact (κ.comp (Ideal.Quotient.mkₐ F M)).commutes x
  · show κ (Ideal.Quotient.mk M x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.2 (hle hx), map_zero]
  · show κ (Ideal.Quotient.mk M s) ≠ 0
    rw [map_ne_zero, Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact hsM

/- English proof (translation)
Use `GlobalTheory.isDiscreteValuationRing_of_height_eq_one P hP (Localization.AtPrime P)` as an intermediate fact. Establish `key : ∀ x y : A, algebraMap A (Localization.AtPrime P) x ∣ algebraMap A _ y → ∃ s, s ∉ P ∧ x ∣ s * y`. Introduce and unpack `x y ⟨c, hc⟩`. Take `⟨⟨n, d⟩, hnd⟩` from `IsLocalization.surj P.primeCompl c`. Use `⟨d, d.2, n, ?_⟩` and prove the remaining obligations.

Apply `IsLocalization.injective (Localization.AtPrime P) P.primeCompl_le_nonZeroDivisors` to reduce the goal to its premises. Simplify using `only at hnd`. Rewrite using `[map_mul, map_mul, hc, ← hnd]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `(ValuationRing.dvd_total (algebraMap A (Localization.AtPrime P) a) (algebraMap A _ b)).imp (key a b) (key b a)`.
-/
theorem dvd_or_dvd_of_height_eq_one {A : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (P : Ideal A) [P.IsPrime] (hP : P.height = 1) (a b : A) :
    (∃ s, s ∉ P ∧ a ∣ s * b) ∨ ∃ s, s ∉ P ∧ b ∣ s * a := by
  have := GlobalTheory.isDiscreteValuationRing_of_height_eq_one P hP (Localization.AtPrime P)
  have key : ∀ x y : A, algebraMap A (Localization.AtPrime P) x ∣ algebraMap A _ y → ∃ s, s ∉ P ∧ x ∣ s * y := by
    rintro x y ⟨c, hc⟩
    obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.surj P.primeCompl c
    refine ⟨d, d.2, n, ?_⟩
    apply IsLocalization.injective (Localization.AtPrime P) P.primeCompl_le_nonZeroDivisors
    simp only at hnd
    rw [map_mul, map_mul, hc, ← hnd]
    ring
  exact (ValuationRing.dvd_total (algebraMap A (Localization.AtPrime P) a) (algebraMap A _ b)).imp (key a b) (key b a)

/- English proof (translation)
Introduce `F A _ _ _ _ hsm σ p a m hp h`. Establish `: IsNoetherianRing A` using `Algebra.FiniteType.isNoetherianRing F A`. Establish `: IsIntegrallyClosed A` using `GlobalTheory.isIntegrallyClosed_of_smooth F A`. Establish `key : ∀ (P : Ideal A) [P.IsPrime], p ∈ P → ∀ s, s ∉ P → ¬ a ∣ s * p ^ m`. Introduce and unpack `P _ hpP s hs ⟨t, ht⟩`.

Take `⟨ψ₀, hσ, hP0, hs0⟩` from `exists_complexPoint_of_notMem σ P hs`. Take `⟨ψ, r, hhol, h0, hσ', hne⟩` from `GlobalTheory.T.exists_holomorphic_arc_smooth_algebra_nonvanishing F A hsm ψ₀ p hp`. Establish `hlim` using `h ψ r hhol (fun u hu => (hσ' u hu).trans hσ) (by rw [h0]; exact hP0 p hpP) hne`. Establish `hball : Metric.ball (0 : ℂ) r ∈ 𝓝 (0 : ℂ)` using `Metric.ball_mem_nhds _ hhol.1`. Establish `hc : ∀ x, Tendsto (fun u => ψ u x) (𝓝[≠] 0) (𝓝 (ψ₀ x))` using `fun x => by`.

Rewrite using `[← h0]`. Conclude with `(((hhol.2 x).differentiableAt hball).continuousAt.tendsto).mono_left nhdsWithin_le_nhds`. Establish `h1` using `hlim.mul (hc t)`. Rewrite `h1` using `[zero_mul]`. Establish `h2 : Tendsto (fun u => ψ u s) (𝓝[≠] 0) (𝓝 0)`.

Use `h1.congr' ?_` and prove the remaining obligations. Use `filter_upwards [mem_nhdsWithin_of_mem_nhds hball, self_mem_nhdsWithin] with u hu hu0`. Establish `hpu : ψ u (p ^ m) ≠ 0`. Rewrite using `[map_pow]`. Conclude with `pow_ne_zero _ (hne u hu hu0)`.

Rewrite using `[div_mul_eq_mul_div, ← map_mul, ← ht, map_mul, mul_div_cancel_right₀ _ hpu]`. Conclude with `hs0 (tendsto_nhds_unique (hc s) h2)`. Choose the witnesses or unpack the hypotheses as in `⟨b, hb⟩ : p ^ m ∣ a := by`. Use `GlobalTheory.dvd_of_forall_height_eq_one (pow_ne_zero m hp) fun P hP h1 hpm => ?_` and prove the remaining obligations. Use `(dvd_or_dvd_of_height_eq_one P h1 (p ^ m) a).resolve_right ?_` and prove the remaining obligations.

Introduce and unpack `⟨s, hs, hd⟩`. Conclude with `key P (hP.mem_of_pow_mem m hpm) s hs hd`. Use `⟨b, by rw [hb, mul_comm], ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.radical_eq_sInf, Ideal.mem_sInf]`. Introduce and unpack `P ⟨hle, hP⟩`.

Assume the negation of the conclusion as `hbP`. Conclude with `key P (hle (Ideal.mem_span_singleton_self p)) b hbP ⟨1, by rw [hb]; ring⟩`.
-/
theorem exists_eq_mul_pow_of_tendsto_zero : ∀ (F A : Type) [Field F] [CommRing A] [IsDomain A] [Algebra F A], Algebra.Smooth F A → ∀ (σ : F →+* ℂ) (p a : A) (m : ℕ), p ≠ 0 → (∀ (ψ : ℂ → (A →+* ℂ)) (r : ℝ), IsHolPts ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, (ψ u).comp (algebraMap F A) = σ) → ψ 0 p = 0 → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → ψ u p ≠ 0) → Tendsto (fun u => ψ u a / ψ u (p ^ m)) (𝓝[≠] 0) (𝓝 0)) → ∃ b : A, a = b * p ^ m ∧ b ∈ (Ideal.span {p}).radical := by
  intro F A _ _ _ _ hsm σ p a m hp h
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing F A
  have : IsIntegrallyClosed A := GlobalTheory.isIntegrallyClosed_of_smooth F A
  have key : ∀ (P : Ideal A) [P.IsPrime], p ∈ P → ∀ s, s ∉ P → ¬ a ∣ s * p ^ m := by
    rintro P _ hpP s hs ⟨t, ht⟩
    obtain ⟨ψ₀, hσ, hP0, hs0⟩ := exists_complexPoint_of_notMem σ P hs
    obtain ⟨ψ, r, hhol, h0, hσ', hne⟩ := GlobalTheory.T.exists_holomorphic_arc_smooth_algebra_nonvanishing F A hsm ψ₀ p hp
    have hlim := h ψ r hhol (fun u hu => (hσ' u hu).trans hσ) (by rw [h0]; exact hP0 p hpP) hne
    have hball : Metric.ball (0 : ℂ) r ∈ 𝓝 (0 : ℂ) := Metric.ball_mem_nhds _ hhol.1
    have hc : ∀ x, Tendsto (fun u => ψ u x) (𝓝[≠] 0) (𝓝 (ψ₀ x)) := fun x => by
      rw [← h0]
      exact (((hhol.2 x).differentiableAt hball).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
    have h1 := hlim.mul (hc t)
    rw [zero_mul] at h1
    have h2 : Tendsto (fun u => ψ u s) (𝓝[≠] 0) (𝓝 0) := by
      refine h1.congr' ?_
      filter_upwards [mem_nhdsWithin_of_mem_nhds hball, self_mem_nhdsWithin] with u hu hu0
      have hpu : ψ u (p ^ m) ≠ 0 := by
        rw [map_pow]
        exact pow_ne_zero _ (hne u hu hu0)
      rw [div_mul_eq_mul_div, ← map_mul, ← ht, map_mul, mul_div_cancel_right₀ _ hpu]
    exact hs0 (tendsto_nhds_unique (hc s) h2)
  obtain ⟨b, hb⟩ : p ^ m ∣ a := by
    refine GlobalTheory.dvd_of_forall_height_eq_one (pow_ne_zero m hp) fun P hP h1 hpm => ?_
    refine (dvd_or_dvd_of_height_eq_one P h1 (p ^ m) a).resolve_right ?_
    rintro ⟨s, hs, hd⟩
    exact key P (hP.mem_of_pow_mem m hpm) s hs hd
  refine ⟨b, by rw [hb, mul_comm], ?_⟩
  rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
  rintro P ⟨hle, hP⟩
  by_contra hbP
  exact key P (hle (Ideal.mem_span_singleton_self p)) b hbP ⟨1, by rw [hb]; ring⟩

end GlobalTheory.ShFam.BdArc
