import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeOfSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqTopOfSpanImage

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct

namespace GlobalTheory.IdemVanish

/- English proof (translation)
Set `f : O →ₐ[O] k` to `Algebra.ofId O k`. Establish `hf : Function.Surjective f` using `hs`. Establish `hker : RingHom.ker f = Ideal.span {lam}`. Use extensionality with `a`. Rewrite using `[RingHom.mem_ker, Ideal.mem_span_singleton]`.

Conclude with `hk a`. Set `e : (O ⧸ RingHom.ker f) ≃ₐ[O] k` to `Ideal.quotientKerAlgEquivOfSurjective hf`. Set `φ : k ⊗[O] R ≃ₗ[O] R ⧸ (RingHom.ker f • (⊤ : Submodule O R))` to `(TensorProduct.congr e.symm.toLinearEquiv (LinearEquiv.refl O R)).trans (TensorProduct.quotTensorEquivQuotSMul R (RingHom.ker f))`. Establish `he : e.symm (1 : k) = Ideal.Quotient.mk (RingHom.ker f) 1` using `by simp`. Establish `h1 : φ ((1 : k) ⊗ₜ[O] x) = Submodule.Quotient.mk x`.

Simplify using `only [φ, LinearEquiv.trans_apply, TensorProduct.congr_tmul, AlgEquiv.toLinearEquiv_apply, LinearEquiv.refl_apply, he, TensorProduct.quotTensorEquivQuotSMul_mk_tmul, one_smul]`. Establish `h2 : x ∈ RingHom.ker f • (⊤ : Submodule O R)`. Rewrite using `[← Submodule.Quotient.mk_eq_zero, ← h1, hx, map_zero]`. Rewrite `h2` using `[hker, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]`. Take `⟨y, -, hy⟩` from `h2`.

Conclude with `⟨y, by rw [← hy, Algebra.smul_def]⟩`.
-/
theorem dvd_of_one_tmul_eq_zero {O k R : Type} [CommRing O] [CommRing k] [CommRing R]
    [Algebra O k] [Algebra O R] (lam : O) (hs : Function.Surjective (algebraMap O k))
    (hk : ∀ x, algebraMap O k x = 0 ↔ lam ∣ x) (x : R)
    (hx : ((1 : k) ⊗ₜ[O] x : k ⊗[O] R) = 0) : algebraMap O R lam ∣ x := by

  let f : O →ₐ[O] k := Algebra.ofId O k
  have hf : Function.Surjective f := hs
  have hker : RingHom.ker f = Ideal.span {lam} := by
    ext a
    rw [RingHom.mem_ker, Ideal.mem_span_singleton]
    exact hk a
  let e : (O ⧸ RingHom.ker f) ≃ₐ[O] k := Ideal.quotientKerAlgEquivOfSurjective hf
  let φ : k ⊗[O] R ≃ₗ[O] R ⧸ (RingHom.ker f • (⊤ : Submodule O R)) :=
    (TensorProduct.congr e.symm.toLinearEquiv (LinearEquiv.refl O R)).trans
      (TensorProduct.quotTensorEquivQuotSMul R (RingHom.ker f))
  have he : e.symm (1 : k) = Ideal.Quotient.mk (RingHom.ker f) 1 := by simp
  have h1 : φ ((1 : k) ⊗ₜ[O] x) = Submodule.Quotient.mk x := by
    simp only [φ, LinearEquiv.trans_apply, TensorProduct.congr_tmul, AlgEquiv.toLinearEquiv_apply,
      LinearEquiv.refl_apply, he, TensorProduct.quotTensorEquivQuotSMul_mk_tmul, one_smul]
  have h2 : x ∈ RingHom.ker f • (⊤ : Submodule O R) := by
    rw [← Submodule.Quotient.mk_eq_zero, ← h1, hx, map_zero]
  rw [hker, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h2
  obtain ⟨y, -, hy⟩ := h2
  exact ⟨y, by rw [← hy, Algebra.smul_def]⟩

/- English proof (translation)
Introduce `l _ P LL k _ _ lam hs hk x hx h1`. Establish `hd : algebraMap (↥(OL LL)) (RW LL) lam ∣ x` using `dvd_of_one_tmul_eq_zero lam hs hk x h1`. Establish `hnu : ¬ IsUnit lam`. Introduce `hu`. Establish `h0 : algebraMap (↥(OL LL)) k 1 = 0` using `(hk 1).2 hu.dvd`.

Simplify using `at h0`. Take `⟨m, hm⟩` from `(GlobalTheory.EtaleExact.isUnit_or_dvd_pow P LL lam).resolve_left hnu`. Apply `GlobalTheory.EtaleExact.sep_RW LL x` to reduce the goal to its premises. Introduce `n`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[map_pow, map_natCast]`. Use `_ ∣ algebraMap (↥(OL LL)) (RW LL) (lam ^ (m * n)) := map_dvd _ (by rw [pow_mul]; exact pow_dvd_pow_of_dvd hm n)`. Use `_ ∣ algebraMap (↥(OL LL)) (RW LL) lam ^ (m * n + 1) := by`. Rewrite using `[map_pow]`. Conclude with `pow_dvd_pow _ (Nat.le_succ _)`.

Use `_ ∣ x ^ (m * n + 1) := pow_dvd_pow_of_dvd hd _`. Use `_ = x := hx.pow_succ_eq _`.
-/
theorem idem_eq_zero : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (LL : FinExt l) (k : Type) [Field k] [Algebra ↥(OL LL) k] (lam : ↥(OL LL)), Function.Surjective (algebraMap ↥(OL LL) k) → (∀ x, algebraMap ↥(OL LL) k x = 0 ↔ lam ∣ x) → ∀ x : RW LL, IsIdempotentElem x → ((1 : k) ⊗ₜ[↥(OL LL)] x : k ⊗[↥(OL LL)] RW LL) = 0 → x = 0 := by
  intro l _ P LL k _ _ lam hs hk x hx h1

  have hd : algebraMap (↥(OL LL)) (RW LL) lam ∣ x := dvd_of_one_tmul_eq_zero lam hs hk x h1
  have hnu : ¬ IsUnit lam := by
    intro hu
    have h0 : algebraMap (↥(OL LL)) k 1 = 0 := (hk 1).2 hu.dvd
    simp at h0
  obtain ⟨m, hm⟩ := (GlobalTheory.EtaleExact.isUnit_or_dvd_pow P LL lam).resolve_left hnu
  apply GlobalTheory.EtaleExact.sep_RW LL x
  intro n
  calc (l : RW LL) ^ n = algebraMap (↥(OL LL)) (RW LL) (((l : ℕ) : ↥(OL LL)) ^ n) := by
        rw [map_pow, map_natCast]
    _ ∣ algebraMap (↥(OL LL)) (RW LL) (lam ^ (m * n)) :=
        map_dvd _ (by rw [pow_mul]; exact pow_dvd_pow_of_dvd hm n)
    _ ∣ algebraMap (↥(OL LL)) (RW LL) lam ^ (m * n + 1) := by
        rw [map_pow]; exact pow_dvd_pow _ (Nat.le_succ _)
    _ ∣ x ^ (m * n + 1) := pow_dvd_pow_of_dvd hd _
    _ = x := hx.pow_succ_eq _

end GlobalTheory.IdemVanish
