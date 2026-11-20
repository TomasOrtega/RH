import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsDualDualRep
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPlaceOverMoveValCc
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel

namespace GlobalTheory.ResSel

/- English proof (translation)
Set `e : Multiplicative (ι → ZMod N) →* A` to `{ toFun := fun x => ∏ q, u q ^ (x.toAdd q).val map_one' := by simp map_mul' := fun x y => by`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun q _ => ?_` and prove the remaining obligations. Rewrite using `[toAdd_mul, Pi.add_apply, ZMod.val_add, ← pow_eq_pow_mod _ (hu q), pow_add] }`. Use `⟨MonoidAlgebra.lift R A _ e, fun q => ?_⟩` and prove the remaining obligations.

Rewrite using `[MonoidAlgebra.lift_of]`. Express the relevant statement in the definitionally equal form `∏ p, u p ^ ((Pi.single q (1 : ZMod N) : ι → ZMod N) p).val = u q`. Rewrite using `[Finset.prod_eq_single q]`. Rewrite using `[Pi.single_eq_same, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod _ (hu q), pow_one]`. Introduce `p _ hp`.

Rewrite using `[Pi.single_eq_of_ne hp, ZMod.val_zero, pow_zero]`. Simplify using the standard rewrite rules.
-/
theorem exists_algHom_groupRing {R A ι : Type} [CommRing R] [CommRing A] [Algebra R A] [Fintype ι] [DecidableEq ι]
    (N : ℕ) [NeZero N] (u : ι → A) (hu : ∀ q, u q ^ N = 1) :
    ∃ th : MonoidAlgebra R (Multiplicative (ι → ZMod N)) →ₐ[R] A,
      ∀ q, th (MonoidAlgebra.of R _ (Multiplicative.ofAdd (Pi.single q 1))) = u q := by
  let e : Multiplicative (ι → ZMod N) →* A :=
    { toFun := fun x => ∏ q, u q ^ (x.toAdd q).val
      map_one' := by simp
      map_mul' := fun x y => by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun q _ => ?_
        rw [toAdd_mul, Pi.add_apply, ZMod.val_add, ← pow_eq_pow_mod _ (hu q), pow_add] }
  refine ⟨MonoidAlgebra.lift R A _ e, fun q => ?_⟩
  rw [MonoidAlgebra.lift_of]
  change ∏ p, u p ^ ((Pi.single q (1 : ZMod N) : ι → ZMod N) p).val = u q
  rw [Finset.prod_eq_single q]
  · rw [Pi.single_eq_same, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod _ (hu q), pow_one]
  · intro p _ hp
    rw [Pi.single_eq_of_ne hp, ZMod.val_zero, pow_zero]
  · simp

/- English proof (translation)
Rewrite using `[MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]`. Use `Finset.dvd_sum fun m _ => ?_` and prove the remaining obligations. Distinguish the cases in `hm : m.degree < n`. Rewrite using `[Polynomial.algebraMap_apply, h m hm, map_zero, zero_mul]`. Conclude with `dvd_zero _`.

Use `Dvd.dvd.mul_left ?_ _` and prove the remaining obligations. Simplify using `only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]`. Conclude with `Dvd.dvd.mul_left (pow_dvd_pow _ (not_lt.1 hm)) _`.
-/
theorem X_pow_dvd_aeval_line {R K ι : Type} [CommRing R] [Field K] [Algebra R K] (b : ι → K) (n : ℕ)
    (F : MvPolynomial ι R) (h : ∀ m : ι →₀ ℕ, m.degree < n → algebraMap R K (F.coeff m) = 0) :
    (Polynomial.X : Polynomial K) ^ n ∣ MvPolynomial.aeval (fun q => Polynomial.C (b q) * Polynomial.X) F := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  refine Finset.dvd_sum fun m _ => ?_
  by_cases hm : m.degree < n
  · rw [Polynomial.algebraMap_apply, h m hm, map_zero, zero_mul]
    exact dvd_zero _
  · refine Dvd.dvd.mul_left ?_ _
    simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    exact Dvd.dvd.mul_left (pow_dvd_pow _ (not_lt.1 hm)) _

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Apply `hG` to reduce the goal to its premises. Establish `hF` using `X_pow_dvd_aeval_line b n F fun m hm => hK _ (fun hu => hcon ⟨m, hm, hu⟩)`. Establish `hp` using `X.lPrime i`. Establish `hl0 : ((X.l i : ℕ) : X.O0 i) ∈ IsLocalRing.maximalIdeal (X.O0 i)` using `fun hu => by`.

Use `hu.map (algebraMap (X.O0 i) (X.O i))` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Conclude with `X.O_l i this`. Establish `hlK : ((X.l i : ℕ) : K) = 0`. Use `hK _ hl0` as an intermediate fact.

Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis. Establish `: CharP K (X.l i)` using `(CharP.charP_iff_prime_eq_zero hp.out).2 hlK`. Establish `: NeZero (X.l i ^ M)` using `⟨pow_ne_zero _ hp.out.ne_zero⟩`. Set `I : Ideal (Polynomial K)` to `Ideal.span {Polynomial.X ^ n}`. Set `π : Polynomial K →ₐ[X.O0 i] (Polynomial K ⧸ I)` to `Ideal.Quotient.mkₐ (X.O0 i) I`.

Establish `hu : ∀ q, (π (Polynomial.C (b q) * Polynomial.X + 1)) ^ (X.l i ^ M) = 1` using `fun q => by`. Rewrite using `[← map_pow, add_pow_char_pow, one_pow, map_add, map_one, add_eq_right]`. Use `Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton.2 ?_)` and prove the remaining obligations. Rewrite using `[mul_pow]`. Conclude with `Dvd.dvd.mul_left (pow_dvd_pow _ hn) _`.

Take `⟨th, hth⟩` from `exists_algHom_groupRing (R := X.O0 i) (X.l i ^ M) _ hu`. Establish `hc : th.comp (toLam X i M ι) = π.comp (MvPolynomial.aeval (fun q => Polynomial.C (b q) * Polynomial.X))`. Use `MvPolynomial.algHom_ext fun q => ?_` and prove the remaining obligations. Use `hth q` as an intermediate fact. Simplify using `only [AlgHom.comp_apply, toLam, MvPolynomial.aeval_X, map_sub, map_one]`.

Rewrite using `[sub_eq_iff_eq_add, ← map_one π, ← map_add, ← this]`. Establish `h1` using `DFunLike.congr_fun hc F`. Establish `h2` using `DFunLike.congr_fun hc G`. Simplify using `only [AlgHom.comp_apply] at h1 h2`. Rewrite `h1` using `[hFG, h2]`.

Establish `h3` using `Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 h1)`. Simplify using `using dvd_add h3 hF`.
-/
theorem exists_unit_coeff_of_not_dvd_line (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂)
    (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw) (M : ℕ) (ι : Type) [Fintype ι] (K : Type) [Field K]
    [Algebra (X.O0 i) K] (hK : IsRes i K) (b : ι → K) (n : ℕ) (hn : n ≤ X.l i ^ M) (F G : MvPolynomial ι (X.O0 i))
    (hFG : toLam X i M ι F = toLam X i M ι G)
    (hG : ¬ (Polynomial.X : Polynomial K) ^ n ∣ MvPolynomial.aeval (fun q => Polynomial.C (b q) * Polynomial.X) G) :
    ∃ m : ι →₀ ℕ, m.degree < n ∧ IsUnit (F.coeff m) := by
  classical
  by_contra hcon
  apply hG
  have hF := X_pow_dvd_aeval_line b n F fun m hm => hK _ (fun hu => hcon ⟨m, hm, hu⟩)
  have hp := X.lPrime i
  have hl0 : ((X.l i : ℕ) : X.O0 i) ∈ IsLocalRing.maximalIdeal (X.O0 i) := fun hu => by
    have := hu.map (algebraMap (X.O0 i) (X.O i))
    rw [map_natCast] at this
    exact X.O_l i this
  have hlK : ((X.l i : ℕ) : K) = 0 := by
    have := hK _ hl0
    rwa [map_natCast] at this
  have : CharP K (X.l i) := (CharP.charP_iff_prime_eq_zero hp.out).2 hlK
  have : NeZero (X.l i ^ M) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  let I : Ideal (Polynomial K) := Ideal.span {Polynomial.X ^ n}
  let π : Polynomial K →ₐ[X.O0 i] (Polynomial K ⧸ I) := Ideal.Quotient.mkₐ (X.O0 i) I
  have hu : ∀ q, (π (Polynomial.C (b q) * Polynomial.X + 1)) ^ (X.l i ^ M) = 1 := fun q => by
    rw [← map_pow, add_pow_char_pow, one_pow, map_add, map_one, add_eq_right]
    refine Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton.2 ?_)
    rw [mul_pow]
    exact Dvd.dvd.mul_left (pow_dvd_pow _ hn) _
  obtain ⟨th, hth⟩ := exists_algHom_groupRing (R := X.O0 i) (X.l i ^ M) _ hu
  have hc : th.comp (toLam X i M ι) =
      π.comp (MvPolynomial.aeval (fun q => Polynomial.C (b q) * Polynomial.X)) := by
    refine MvPolynomial.algHom_ext fun q => ?_
    have := hth q
    simp only [AlgHom.comp_apply, toLam, MvPolynomial.aeval_X, map_sub, map_one]
    rw [sub_eq_iff_eq_add, ← map_one π, ← map_add, ← this]
  have h1 := DFunLike.congr_fun hc F
  have h2 := DFunLike.congr_fun hc G
  simp only [AlgHom.comp_apply] at h1 h2
  rw [hFG, h2] at h1
  have h3 := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 h1)
  simpa using dvd_add h3 hF

end GlobalTheory.ResSel
