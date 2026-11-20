import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingHomExtDense
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism GlobalTheory.CrysEval
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.CrysEval

/- English proof (translation)
Rewrite using `[← map_natCast (C : R →+* R⟦X⟧) n, coeff_C_mul]`.
-/
theorem coeff_natCast_mul_ps {R : Type} [CommRing R] (n i : ℕ) (f : R⟦X⟧) :
    coeff i ((n : R⟦X⟧) * f) = n * coeff i f := by
  rw [← map_natCast (C : R →+* R⟦X⟧) n, coeff_C_mul]

/- English proof (translation)
Introduce `l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t ϖ g b F hF n hn hnF`. Take `⟨w, -, hw⟩` from `hF`. Use `charZero_K (l := l) (K := K)` as an intermediate fact. Establish `key : ∀ i k, ((i.factorial * (k / e).factorial : ℕ) : Wq l a) * (b.coeff i).coeff k = n * w (i, k)`. Introduce `i k`.

Apply `embK_injective (K := K) t 0` to reduce the goal to its premises. Establish `h1` using `congrArg (fun G => coeff k (coeff i (G 0))) hnF`. Simplify using `only [Pi.mul_apply, Pi.natCast_apply] at h1`. Rewrite `h1` using `[coeff_natCast_mul_ps, coeff_natCast_mul_ps, coeff_iotaP]`. Establish `h2` using `hw 0 i k`.

Express the relevant statement in the definitionally equal form `_ = embK K t 0 (w (i, k)) at h2`. Rewrite using `[map_mul, map_mul, map_natCast, map_natCast]`. Move the coercions through the operations in `at h2 ⊢`. Take the linear combination `(-((i.factorial : K) * ((k / e).factorial : K))) * h1 + (n : K) * h2`. Establish `hμ` using `ϖ.theta_mu (ϖ.gal_pi a g)`.

Use `set T := ainfToAcris l ϖ.teich with hTdef`. Establish `term : ∀ i k, ainfToAcris l (wA l a ((b.coeff i).coeff k)) * T ^ k * ainfToAcris l (ϖ.mu (g : GQ l) * ϖ.teich) ^ i ∈ Ideal.span {(n : Per.Acris l)}`. Introduce `i k`. Take `⟨D, hD⟩` from `ϖ.exists_dpow_teich (k / e)`. Establish `hm` using `factorial_mul_dpow (ϖ.mu (g : GQ l)) hμ i`.

Establish `hk` using `congrArg (fun x => ainfToAcris l (wA l a x)) (key i k)`. Simplify using `only [map_mul, map_natCast] at hk`. Move the coercions through the operations in `at hk`. Rewrite using `[Ideal.mem_span_singleton']`. Use `⟨ainfToAcris l (wA l a (w (i, k))) * D * dpow (ϖ.mu (g : GQ l)) hμ i * T ^ (k % e) * T ^ i, ?_⟩` and prove the remaining obligations.

Establish `hT : T ^ k = T ^ (k % e) * T ^ (e * (k / e))` using `by rw [← pow_add, Nat.mod_add_div]`. Rewrite using `[hT, ← hD, map_mul, mul_pow, ← hm]`. Take the linear combination `(-(D * dpow (ϖ.mu (g : GQ l)) hμ i * T ^ (k % e) * T ^ i)) * hk`. Establish `hmem : fP a ϖ (g : GQ l) b ∈ Ideal.span {(n : Per.Acris l)}`. Rewrite using `[fP, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_eq_sum, Polynomial.sum_def]`.

Use `Ideal.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Establish `hev : evC a ϖ (b.coeff i) = (b.coeff i).sum fun k c => ainfToAcris l (wA l a c) * T ^ k`. Rewrite using `[evC, RingHom.comp_apply, RingHom.comp_apply, Polynomial.coeToPowerSeries.ringHom_apply, ev_coe, Polynomial.eval₂_eq_sum, Polynomial.sum_def, Polynomial.sum_def]`. Express the relevant statement in the definitionally equal form `ainfToAcris l _ = _`. Rewrite using `[map_sum]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_pow]`. Both sides reduce to the same expression. Rewrite using `[hev, Polynomial.sum_def, Finset.sum_mul]`. Conclude with `Ideal.sum_mem _ fun k _ => term i k`.

Take `⟨y, hy⟩` from `Ideal.mem_span_singleton'.1 hmem`. Conclude with `⟨y, by rw [mul_comm]; exact hy⟩`.
-/
theorem dvd_fP_of_mem_PPSet : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ (ϖ : PiSys l e) (g : ↥(GK (ϖ.field a))) (b : Bp l a) (F : ZMod a → K⟦X⟧⟦X⟧), F ∈ PPSet t K e → ∀ n : ℕ, n ≠ 0 → (n : ZMod a → K⟦X⟧⟦X⟧) * F = iotaP K t b → ∃ y : Per.Acris l, (n : Per.Acris l) * y = fP a ϖ (g : GQ l) b := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t ϖ g b F hF n hn hnF
  obtain ⟨w, -, hw⟩ := hF
  have := charZero_K (l := l) (K := K)
  have key : ∀ i k, ((i.factorial * (k / e).factorial : ℕ) : Wq l a) * (b.coeff i).coeff k = n * w (i, k) := by
    intro i k
    apply embK_injective (K := K) t 0
    have h1 := congrArg (fun G => coeff k (coeff i (G 0))) hnF
    simp only [Pi.mul_apply, Pi.natCast_apply] at h1
    rw [coeff_natCast_mul_ps, coeff_natCast_mul_ps, coeff_iotaP] at h1
    have h2 := hw 0 i k
    change _ = embK K t 0 (w (i, k)) at h2
    rw [map_mul, map_mul, map_natCast, map_natCast]
    push_cast at h2 ⊢
    linear_combination (-((i.factorial : K) * ((k / e).factorial : K))) * h1 + (n : K) * h2
  have hμ := ϖ.theta_mu (ϖ.gal_pi a g)
  set T := ainfToAcris l ϖ.teich with hTdef
  have term : ∀ i k, ainfToAcris l (wA l a ((b.coeff i).coeff k)) * T ^ k *
      ainfToAcris l (ϖ.mu (g : GQ l) * ϖ.teich) ^ i ∈ Ideal.span {(n : Per.Acris l)} := by
    intro i k
    obtain ⟨D, hD⟩ := ϖ.exists_dpow_teich (k / e)
    have hm := factorial_mul_dpow (ϖ.mu (g : GQ l)) hμ i
    have hk := congrArg (fun x => ainfToAcris l (wA l a x)) (key i k)
    simp only [map_mul, map_natCast] at hk
    push_cast at hk
    rw [Ideal.mem_span_singleton']
    refine ⟨ainfToAcris l (wA l a (w (i, k))) * D * dpow (ϖ.mu (g : GQ l)) hμ i * T ^ (k % e) * T ^ i, ?_⟩
    have hT : T ^ k = T ^ (k % e) * T ^ (e * (k / e)) := by rw [← pow_add, Nat.mod_add_div]
    rw [hT, ← hD, map_mul, mul_pow, ← hm]
    linear_combination (-(D * dpow (ϖ.mu (g : GQ l)) hμ i * T ^ (k % e) * T ^ i)) * hk
  have hmem : fP a ϖ (g : GQ l) b ∈ Ideal.span {(n : Per.Acris l)} := by
    rw [fP, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
    refine Ideal.sum_mem _ fun i _ => ?_
    have hev : evC a ϖ (b.coeff i) = (b.coeff i).sum fun k c => ainfToAcris l (wA l a c) * T ^ k := by
      rw [evC, RingHom.comp_apply, RingHom.comp_apply, Polynomial.coeToPowerSeries.ringHom_apply, ev_coe,
        Polynomial.eval₂_eq_sum, Polynomial.sum_def, Polynomial.sum_def]
      change ainfToAcris l _ = _
      rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, map_pow]
      rfl
    rw [hev, Polynomial.sum_def, Finset.sum_mul]
    exact Ideal.sum_mem _ fun k _ => term i k
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hmem
  exact ⟨y, by rw [mul_comm]; exact hy⟩

end GlobalTheory.CrysEval
