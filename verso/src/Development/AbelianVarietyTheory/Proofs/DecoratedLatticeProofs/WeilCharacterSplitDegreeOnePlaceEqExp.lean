import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NatCastNotMemUnderSq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsGAtAllPlacesMul
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open NumberField IsDedekindDomain Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LocMod
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitDegOnePow

section Arith
variable {K : Type} [Field K] [NumberField K]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Take `⟨s, rfl⟩` from `ih (Ideal.pow_le_pow_right (Nat.le_succ n) hr)`. Establish `h1 : v.asIdeal ^ n * v.asIdeal ∣ v.asIdeal ^ n * (I ^ n * Ideal.span {(s : 𝓞 K)})`.

Rewrite using `[← pow_succ, ← mul_assoc, ← mul_pow, ← hpI, Ideal.span_singleton_pow, Ideal.span_singleton_mul_span_singleton, Ideal.dvd_span_singleton]`. Simplify using `using hr`. Rewrite `h1` using `[mul_dvd_mul_iff_left (pow_ne_zero n v.ne_bot)]`. Establish `h2 : (s : 𝓞 K) ∈ v.asIdeal` using `Ideal.dvd_span_singleton.1 (hvI.pow_right.dvd_of_dvd_mul_left h1)`. Establish `hpv : (p : 𝓞 K) ∈ v.asIdeal` using `(Ideal.span_singleton_le_iff_mem _).1 (hpI ▸ Ideal.mul_le_left)`.

Establish `h3 : (p : ℤ) ∣ s`. Assume the negation of the conclusion as `hc`. Take `⟨x, y, e⟩` from `((Nat.prime_iff_prime_int.mp hp).irreducible.coprime_iff_not_dvd).2 hc`. Establish `e' : (x : 𝓞 K) * p + y * s = 1` using `by exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 K) e`. Conclude with `v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (e' ▸ add_mem (Ideal.mul_mem_left _ _ hpv) (Ideal.mul_mem_left _ _ h2)))`.

Rewrite using `[pow_succ]`. Conclude with `mul_dvd_mul_left _ h3`.
-/
theorem pow_dvd_of_mem (p : ℕ) (hp : p.Prime) (v : HeightOneSpectrum (𝓞 K)) (I : Ideal (𝓞 K))
    (hvI : IsCoprime v.asIdeal I) (hpI : Ideal.span {(p : 𝓞 K)} = v.asIdeal * I) (n : ℕ) (r : ℤ)
    (hr : (r : 𝓞 K) ∈ v.asIdeal ^ n) : (p : ℤ) ^ n ∣ r := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨s, rfl⟩ := ih (Ideal.pow_le_pow_right (Nat.le_succ n) hr)
    have h1 : v.asIdeal ^ n * v.asIdeal ∣ v.asIdeal ^ n * (I ^ n * Ideal.span {(s : 𝓞 K)}) := by
      rw [← pow_succ, ← mul_assoc, ← mul_pow, ← hpI, Ideal.span_singleton_pow, Ideal.span_singleton_mul_span_singleton,
        Ideal.dvd_span_singleton]
      simpa using hr
    rw [mul_dvd_mul_iff_left (pow_ne_zero n v.ne_bot)] at h1
    have h2 : (s : 𝓞 K) ∈ v.asIdeal := Ideal.dvd_span_singleton.1 (hvI.pow_right.dvd_of_dvd_mul_left h1)
    have hpv : (p : 𝓞 K) ∈ v.asIdeal :=
      (Ideal.span_singleton_le_iff_mem _).1 (hpI ▸ Ideal.mul_le_left)
    have h3 : (p : ℤ) ∣ s := by
      by_contra hc
      obtain ⟨x, y, e⟩ := ((Nat.prime_iff_prime_int.mp hp).irreducible.coprime_iff_not_dvd).2 hc
      have e' : (x : 𝓞 K) * p + y * s = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 K) e
      exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
        (e' ▸ add_mem (Ideal.mul_mem_left _ _ hpv) (Ideal.mul_mem_left _ _ h2)))
    rw [pow_succ]
    exact mul_dvd_mul_left _ h3

/- English proof (translation)
Establish `hle : Ideal.span {(N : ℤ)} ≤ J.comap (Int.castRingHom (𝓞 K))`. Rewrite using `[Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast, ← hJ]`. Conclude with `Ideal.absNorm_mem J`. Establish `hi : Function.Injective (Ideal.quotientMap J (Int.castRingHom (𝓞 K)) hle)` using `Ideal.quotientMap_injective' fun r hr => Ideal.mem_span_singleton.2 (hinj r hr)`. Establish `hc : Nat.card (𝓞 K ⧸ J) = N` using `by rw [← hJ, Ideal.absNorm_apply, Submodule.cardQuot_apply]`.

Use `haveI : Finite (𝓞 K ⧸ J) := Nat.finite_of_card_ne_zero (hc ▸ hN)`. Establish `hb` using `hi.bijective_of_nat_card_le (by`. Rewrite using `[hc, Nat.card_congr (Int.quotientSpanNatEquivZMod N).toEquiv, Nat.card_zmod])`. Take `⟨r, hr⟩` from `hb.2 (Ideal.Quotient.mk J m)`. Take `⟨r, rfl⟩` from `Ideal.Quotient.mk_surjective r`.

Conclude with `⟨r, Ideal.Quotient.eq.1 hr.symm⟩`.
-/
theorem exists_int_sub_mem (N : ℕ) (hN : N ≠ 0) (J : Ideal (𝓞 K)) (hJ : Ideal.absNorm J = N)
    (hinj : ∀ r : ℤ, (r : 𝓞 K) ∈ J → (N : ℤ) ∣ r) (m : 𝓞 K) : ∃ r : ℤ, m - r ∈ J := by
  have hle : Ideal.span {(N : ℤ)} ≤ J.comap (Int.castRingHom (𝓞 K)) := by
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast, ← hJ]
    exact Ideal.absNorm_mem J
  have hi : Function.Injective (Ideal.quotientMap J (Int.castRingHom (𝓞 K)) hle) :=
    Ideal.quotientMap_injective' fun r hr => Ideal.mem_span_singleton.2 (hinj r hr)
  have hc : Nat.card (𝓞 K ⧸ J) = N := by rw [← hJ, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (𝓞 K ⧸ J) := Nat.finite_of_card_ne_zero (hc ▸ hN)
  have hb := hi.bijective_of_nat_card_le (by
    rw [hc, Nat.card_congr (Int.quotientSpanNatEquivZMod N).toEquiv, Nat.card_zmod])
  obtain ⟨r, hr⟩ := hb.2 (Ideal.Quotient.mk J m)
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  exact ⟨r, Ideal.Quotient.eq.1 hr.symm⟩

/- English proof (translation)
Set `b` to `Module.Free.chooseBasis ℤ (𝓞 K)`. Use `choose r hr using fun j => hsurj (b j)`. Establish `hy : ∀ j, ∃ y : 𝓞 K, y * N = (b j - r j) * t` using `fun j => Ideal.mem_span_singleton'.1 (hN ▸ Ideal.mul_mem_mul (hr j) ht)`. Use `choose y hy using hy`. Set `π : 𝓞 K →ₗ[ℤ] ℤ` to `b.constr ℤ r`.

Set `g : 𝓞 K →ₗ[ℤ] 𝓞 K` to `b.constr ℤ y`. Establish `hπ : ∀ m : 𝓞 K, m - (π m : 𝓞 K) ∈ J`. Establish `: (J.restrictScalars ℤ).mkQ ∘ₗ (LinearMap.id - (Algebra.linearMap ℤ (𝓞 K)) ∘ₗ π) = 0` using `b.ext fun j => (Submodule.Quotient.mk_eq_zero _).2 (by simpa [π] using hr j)`. Introduce `m`. Simplify using `using (Submodule.Quotient.mk_eq_zero _).1 (LinearMap.congr_fun this m)`.

Establish `hm : Algebra.lmul ℤ (𝓞 K) t = π.smulRight t + (N : ℤ) • g` using `b.ext fun j => by`. Simplify using `only [π, g, LinearMap.add_apply, LinearMap.smulRight_apply, LinearMap.smul_apply, Module.Basis.constr_basis, Algebra.coe_lmul_eq_mul, LinearMap.mul_apply']`. Rewrite using `[zsmul_eq_mul, zsmul_eq_mul, Int.cast_natCast]`. Take the linear combination `(-1 : 𝓞 K) * hy j`. Take `⟨c, hc⟩` from `hinj (π t - 1) (by`.

Use `sub_mem ht1 (hπ t)` as an intermediate fact. Use `push_cast`. Use `this using 1` and compare the differences between its conclusion and the goal. Use the proof step `ring)`. Use `⟨c + LinearMap.trace ℤ _ g, ?_⟩` and prove the remaining obligations.

Rewrite using `[Algebra.trace_apply, hm, map_add, map_smul, LinearMap.trace_smulRight, smul_eq_mul]`. Take the linear combination `hc`.
-/
theorem trace_idem (N : ℕ) (J I : Ideal (𝓞 K)) (hN : Ideal.span {(N : 𝓞 K)} = J * I)
    (hinj : ∀ r : ℤ, (r : 𝓞 K) ∈ J → (N : ℤ) ∣ r) (hsurj : ∀ m : 𝓞 K, ∃ r : ℤ, m - r ∈ J)
    (t : 𝓞 K) (ht : t ∈ I) (ht1 : t - 1 ∈ J) : ∃ m : ℤ, Algebra.trace ℤ (𝓞 K) t = 1 + N * m := by
  classical
  let b := Module.Free.chooseBasis ℤ (𝓞 K)
  choose r hr using fun j => hsurj (b j)
  have hy : ∀ j, ∃ y : 𝓞 K, y * N = (b j - r j) * t := fun j =>
    Ideal.mem_span_singleton'.1 (hN ▸ Ideal.mul_mem_mul (hr j) ht)
  choose y hy using hy
  let π : 𝓞 K →ₗ[ℤ] ℤ := b.constr ℤ r
  let g : 𝓞 K →ₗ[ℤ] 𝓞 K := b.constr ℤ y
  have hπ : ∀ m : 𝓞 K, m - (π m : 𝓞 K) ∈ J := by
    have : (J.restrictScalars ℤ).mkQ ∘ₗ (LinearMap.id - (Algebra.linearMap ℤ (𝓞 K)) ∘ₗ π) = 0 :=
      b.ext fun j => (Submodule.Quotient.mk_eq_zero _).2 (by simpa [π] using hr j)
    intro m
    simpa using (Submodule.Quotient.mk_eq_zero _).1 (LinearMap.congr_fun this m)
  have hm : Algebra.lmul ℤ (𝓞 K) t = π.smulRight t + (N : ℤ) • g := b.ext fun j => by
    simp only [π, g, LinearMap.add_apply, LinearMap.smulRight_apply, LinearMap.smul_apply, Module.Basis.constr_basis,
      Algebra.coe_lmul_eq_mul, LinearMap.mul_apply']
    rw [zsmul_eq_mul, zsmul_eq_mul, Int.cast_natCast]
    linear_combination (-1 : 𝓞 K) * hy j
  obtain ⟨c, hc⟩ := hinj (π t - 1) (by
    have := sub_mem ht1 (hπ t)
    push_cast
    convert this using 1
    ring)
  refine ⟨c + LinearMap.trace ℤ _ g, ?_⟩
  rw [Algebra.trace_apply, hm, map_add, map_smul, LinearMap.trace_smulRight, smul_eq_mul]
  linear_combination hc

/- English proof (translation)
Take `⟨I, hvI, hpI⟩` from `GlobalTheory.StdCharDegOne.exists_cofactor p v hnorm hsq`. Take `⟨u, hu, t, ht, hut⟩` from `Ideal.isCoprime_iff_exists.mp (hvI.pow (m := n) (n := n))`. Establish `hN : Ideal.span {((p ^ n : ℕ) : 𝓞 K)} = v.asIdeal ^ n * I ^ n`. Rewrite using `[← mul_pow, ← hpI, Ideal.span_singleton_pow, Nat.cast_pow]`. Establish `hinj : ∀ r : ℤ, (r : 𝓞 K) ∈ v.asIdeal ^ n → ((p ^ n : ℕ) : ℤ) ∣ r` using `fun r hr => by`.

Rewrite using `[Nat.cast_pow]`. Conclude with `pow_dvd_of_mem p hp v I hvI hpI n r hr`. Take `⟨m, hm⟩` from `trace_idem (p ^ n) _ _ hN hinj (exists_int_sub_mem _ (pow_ne_zero n hp.ne_zero) _ (by rw [map_pow, hnorm]) hinj) t ht (by`. Rewrite using `[show t - 1 = -u by linear_combination hut]; exact neg_mem hu)`. Establish `hp0 : (p : 𝓞 K) ^ n ≠ 0` using `pow_ne_zero _ (by exact_mod_cast hp.ne_zero)`.

Establish `hmemp : ∀ z ∈ v.asIdeal ^ n * I ^ n, ∃ y, z = (p : 𝓞 K) ^ n * y` using `fun z hz => by`. Rewrite `hz` using `[← hN, Ideal.mem_span_singleton']`. Take `⟨y, hy⟩` from `hz`. Conclude with `⟨y, by rw [← hy, mul_comm, Nat.cast_pow]⟩`. Use `⟨b * t, ⟨b * m, ?_⟩, fun w => ?_⟩` and prove the remaining obligations.

Rewrite using `[← zsmul_eq_mul, map_smul, Algebra.intTrace_eq_trace, hm, smul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hcomp : (α * algebraMap K (Af K) ((b : K) / (p : K) ^ n) - algebraMap K (Af K) ((((b : 𝓞 K) * t : 𝓞 K) : K) / (p : K) ^ n)) w = α w * algebraMap K (Af K) ((b : K) / (p : K) ^ n) w - algebraMap K (Af K) ((((b : 𝓞 K) * t : 𝓞 K) : K) / (p : K) ^ n) w` using `rfl`. Rewrite using `[hcomp]`.

Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality. Establish `h1 : α w = 1` using `hα1`. Establish `hsub : algebraMap K (Af K) ((b : K) / (p : K) ^ n) w - algebraMap K (Af K) ((((b : 𝓞 K) * t : 𝓞 K) : K) / (p : K) ^ n) w = algebraMap K (Af K) ((((b : 𝓞 K) - (b : 𝓞 K) * t : 𝓞 K) : K) / (((p : 𝓞 K) ^ n : 𝓞 K) : K)) w`. Rewrite using `[show ((((b : 𝓞 K) - (b : 𝓞 K) * t : 𝓞 K) : K) / (((p : 𝓞 K) ^ n : 𝓞 K) : K)) = (b : K) / (p : K) ^ n - ((((b : 𝓞 K) * t : 𝓞 K) : K) / (p : K) ^ n) by rw [← sub_div]; simp, map_sub]`.

Both sides reduce to the same expression. Rewrite using `[h1, one_mul, hsub]`. Take `⟨u', hu', s, hs, hus⟩` from `Ideal.isCoprime_iff_exists.mp (hvI.pow_right (n := n))`. Establish `hsv : s ∉ w.asIdeal` using `fun h => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr (hus ▸ add_mem hu' h))`. Establish `hmem : ((b : 𝓞 K) - (b : 𝓞 K) * t) * s ∈ w.asIdeal ^ n * I ^ n`.

Use `Ideal.mul_mem_mul ?_ hs` and prove the remaining obligations. Rewrite using `[show (b : 𝓞 K) - (b : 𝓞 K) * t = b * u by linear_combination (-b : 𝓞 K) * hut]`. Conclude with `Ideal.mul_mem_left _ _ hu`. Take `⟨y, hy⟩` from `hmemp _ hmem`. Conclude with `GlobalTheory.StdCharDegOne.integral_of_mul w _ _ s y hp0 hsv hy`.

Establish `h0 : α w = 0` using `hα0 w hw`. Rewrite using `[h0, zero_mul, zero_sub]`. Use `neg_mem ?_` and prove the remaining obligations. Choose the witnesses or unpack the hypotheses as in `⟨s, hsv, hsw⟩ : ∃ s ∈ v.asIdeal, s ∉ w.asIdeal := by`. Assume the negation of the conclusion as `hc`.

Use `push Not at hc`. Conclude with `hw (HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top hc).symm)`. Take `⟨y, hy⟩` from `hmemp _ (Ideal.mul_mem_mul (Ideal.pow_mem_pow hsv n) (Ideal.mul_mem_left _ (b : 𝓞 K) ht))`. Use `GlobalTheory.StdCharDegOne.integral_of_mul w ((p : 𝓞 K) ^ n) ((b : 𝓞 K) * t) (s ^ n) y hp0 (fun h => hsw (w.isPrime.mem_of_pow_mem n h)) (by rw [mul_comm]; exact hy)` as an intermediate fact. Simplify using `using this`.
-/
theorem fin_part (p : ℕ) (hp : p.Prime) (v : HeightOneSpectrum (𝓞 K))
    (hnorm : Ideal.absNorm v.asIdeal = p) (hsq : (p : 𝓞 K) ∉ v.asIdeal ^ 2) (α : Af K)
    (hα1 : evalV K v α = 1) (hα0 : ∀ w, w ≠ v → evalV K w α = 0) (b : ℤ) (n : ℕ) :
    ∃ x : 𝓞 K, (∃ m : ℤ, Algebra.intTrace ℤ (𝓞 K) x = b + (p : ℤ) ^ n * m) ∧
      ∀ w : HeightOneSpectrum (𝓞 K), (α * algebraMap K (Af K) ((b : K) / (p : K) ^ n) -
        algebraMap K (Af K) ((x : K) / (p : K) ^ n)) w ∈ w.adicCompletionIntegers K := by
  obtain ⟨I, hvI, hpI⟩ := GlobalTheory.StdCharDegOne.exists_cofactor p v hnorm hsq
  obtain ⟨u, hu, t, ht, hut⟩ := Ideal.isCoprime_iff_exists.mp (hvI.pow (m := n) (n := n))
  have hN : Ideal.span {((p ^ n : ℕ) : 𝓞 K)} = v.asIdeal ^ n * I ^ n := by
    rw [← mul_pow, ← hpI, Ideal.span_singleton_pow, Nat.cast_pow]
  have hinj : ∀ r : ℤ, (r : 𝓞 K) ∈ v.asIdeal ^ n → ((p ^ n : ℕ) : ℤ) ∣ r := fun r hr => by
    rw [Nat.cast_pow]; exact pow_dvd_of_mem p hp v I hvI hpI n r hr
  obtain ⟨m, hm⟩ := trace_idem (p ^ n) _ _ hN hinj
    (exists_int_sub_mem _ (pow_ne_zero n hp.ne_zero) _ (by rw [map_pow, hnorm]) hinj) t ht (by
      rw [show t - 1 = -u by linear_combination hut]; exact neg_mem hu)
  have hp0 : (p : 𝓞 K) ^ n ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
  have hmemp : ∀ z ∈ v.asIdeal ^ n * I ^ n, ∃ y, z = (p : 𝓞 K) ^ n * y := fun z hz => by
    rw [← hN, Ideal.mem_span_singleton'] at hz
    obtain ⟨y, hy⟩ := hz
    exact ⟨y, by rw [← hy, mul_comm, Nat.cast_pow]⟩
  refine ⟨b * t, ⟨b * m, ?_⟩, fun w => ?_⟩
  · rw [← zsmul_eq_mul, map_smul, Algebra.intTrace_eq_trace, hm, smul_eq_mul]
    push_cast
    ring
  have hcomp : (α * algebraMap K (Af K) ((b : K) / (p : K) ^ n) - algebraMap K (Af K) ((((b : 𝓞 K) * t : 𝓞 K) : K) / (p : K) ^ n)) w =
      α w * algebraMap K (Af K) ((b : K) / (p : K) ^ n) w - algebraMap K (Af K) ((((b : 𝓞 K) * t : 𝓞 K) : K) / (p : K) ^ n) w := rfl
  rw [hcomp]
  by_cases hw : w = v
  · subst hw
    have h1 : α w = 1 := hα1
    have hsub : algebraMap K (Af K) ((b : K) / (p : K) ^ n) w - algebraMap K (Af K) ((((b : 𝓞 K) * t : 𝓞 K) : K) / (p : K) ^ n) w =
        algebraMap K (Af K) ((((b : 𝓞 K) - (b : 𝓞 K) * t : 𝓞 K) : K) / (((p : 𝓞 K) ^ n : 𝓞 K) : K)) w := by
      rw [show ((((b : 𝓞 K) - (b : 𝓞 K) * t : 𝓞 K) : K) / (((p : 𝓞 K) ^ n : 𝓞 K) : K)) =
        (b : K) / (p : K) ^ n - ((((b : 𝓞 K) * t : 𝓞 K) : K) / (p : K) ^ n) by rw [← sub_div]; simp, map_sub]
      rfl
    rw [h1, one_mul, hsub]
    obtain ⟨u', hu', s, hs, hus⟩ := Ideal.isCoprime_iff_exists.mp (hvI.pow_right (n := n))
    have hsv : s ∉ w.asIdeal := fun h =>
      w.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr (hus ▸ add_mem hu' h))
    have hmem : ((b : 𝓞 K) - (b : 𝓞 K) * t) * s ∈ w.asIdeal ^ n * I ^ n := by
      refine Ideal.mul_mem_mul ?_ hs
      rw [show (b : 𝓞 K) - (b : 𝓞 K) * t = b * u by linear_combination (-b : 𝓞 K) * hut]
      exact Ideal.mul_mem_left _ _ hu
    obtain ⟨y, hy⟩ := hmemp _ hmem
    exact GlobalTheory.StdCharDegOne.integral_of_mul w _ _ s y hp0 hsv hy
  · have h0 : α w = 0 := hα0 w hw
    rw [h0, zero_mul, zero_sub]
    refine neg_mem ?_
    obtain ⟨s, hsv, hsw⟩ : ∃ s ∈ v.asIdeal, s ∉ w.asIdeal := by
      by_contra hc
      push Not at hc
      exact hw (HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top hc).symm)
    obtain ⟨y, hy⟩ := hmemp _ (Ideal.mul_mem_mul (Ideal.pow_mem_pow hsv n) (Ideal.mul_mem_left _ (b : 𝓞 K) ht))
    have := GlobalTheory.StdCharDegOne.integral_of_mul w ((p : 𝓞 K) ^ n) ((b : 𝓞 K) * t) (s ^ n) y hp0
      (fun h => hsw (w.isPrime.mem_of_pow_mem n h)) (by rw [mul_comm]; exact hy)
    simpa using this

end Arith

/- English proof (translation)
Take `⟨α, rfl, hα1, hα0⟩` from `hε`. Take `⟨x, ⟨m, hm⟩, hint⟩` from `fin_part p hp v hnorm hsq α hα1 hα0 b n`. Establish `hsplit : pairA D.host.F 0 α * algebraMap D.host.F (AF D.host.F) ((b : D.host.F) / (p : D.host.F) ^ n) = pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) ((x : D.host.F) / (p : D.host.F) ^ n)) + pairA D.host.F 0 (α * algebraMap D.host.F (Af D.host.F) ((b : D.host.F) / (p : D.ho …`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use `show (0 : Ainf D.host.F) * _ = 0 + 0`.

Rewrite using `[zero_mul, add_zero]`. Use `show α * algebraMap D.host.F (Af D.host.F) ((b : D.host.F) / (p : D.host.F) ^ n) = algebraMap D.host.F (Af D.host.F) ((x : D.host.F) / (p : D.host.F) ^ n) + (α * algebraMap D.host.F (Af D.host.F) ((b : D.host.F) / (p : D.host.F) ^ n) - algebraMap D.host.F (Af D.host.F) ((x : D.ho …`. Rewrite using `[add_sub_cancel]`. Establish `htr : ∀ r : 𝓞 D.host.F, Algebra.trace ℚ D.host.F (r : D.host.F) = ((Algebra.intTrace ℤ (𝓞 D.host.F) r : ℤ) : ℚ)` using `fun r => (Algebra.algebraMap_intTrace (A := ℤ) (K := ℚ) (L := D.host.F) r).symm`. Establish `h1 : ψ (pairA D.host.F 0 (α * algebraMap D.host.F (Af D.host.F) ((b : D.host.F) / (p : D.host.F) ^ n) - algebraMap D.host.F (Af D.host.F) ((x : D.host.F) / (p : D.host.F) ^ n))) = 1`.

Use `GlobalTheory.IntDense.mem_of_isClosed D.host.F (C := {y | ψ (pairA D.host.F 0 y) = 1}) (isClosed_eq (hψ.1.1.comp (Continuous.prodMk continuous_const continuous_id)) continuous_const) (fun r => ?_) _ hint` and prove the remaining obligations. Use `show ψ (pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) (r : D.host.F))) = 1`. Rewrite using `[GlobalTheory.StdRat.stdChar_fin_rat D ψ hψ, htr, mul_comm]`. Use `push_cast`. Conclude with `Complex.exp_int_mul_two_pi_mul_I _`.

Rewrite using `[hsplit, AddChar.map_add_eq_mul, h1, mul_one, GlobalTheory.StdRat.stdChar_fin_rat D ψ hψ]`. Establish `hq : Algebra.trace ℚ D.host.F ((x : D.host.F) / (p : D.host.F) ^ n) = ((b : ℚ) + p ^ n * m) / p ^ n`. Establish `e : (x : D.host.F) / (p : D.host.F) ^ n = (((p : ℚ) ^ n)⁻¹) • (x : D.host.F)`. Rewrite using `[Algebra.smul_def, map_inv₀, map_pow, map_natCast, div_eq_inv_mul]`. Rewrite using `[e, map_smul, htr, hm, smul_eq_mul]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hp0 : (p : ℂ) ≠ 0` using `by exact_mod_cast hp.ne_zero`. Rewrite using `[hq, show 2 * ↑Real.pi * Complex.I * ((((b : ℚ) + p ^ n * m) / p ^ n : ℚ) : ℂ) = 2 * Real.pi * Complex.I * b / (p : ℂ) ^ n + m * (2 * Real.pi * Complex.I) by push_cast; field_simp, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]`.
-/
theorem stdChar_placeIdem_div_pow (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (p : ℕ) (hp : p.Prime)
    (v : HeightOneSpectrum (𝓞 D.host.F)) (hnorm : Ideal.absNorm v.asIdeal = p) (hsq : (p : 𝓞 D.host.F) ∉ v.asIdeal ^ 2)
    (ε) (hε : IsPlaceIdem D v ε) (b : ℤ) (n : ℕ) :
    ψ (ε * algebraMap D.host.F (AF D.host.F) ((b : D.host.F) / (p : D.host.F) ^ n)) =
      Complex.exp (2 * Real.pi * Complex.I * b / (p : ℂ) ^ n) := by
  obtain ⟨α, rfl, hα1, hα0⟩ := hε
  obtain ⟨x, ⟨m, hm⟩, hint⟩ := fin_part p hp v hnorm hsq α hα1 hα0 b n
  have hsplit : pairA D.host.F 0 α * algebraMap D.host.F (AF D.host.F) ((b : D.host.F) / (p : D.host.F) ^ n) =
      pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) ((x : D.host.F) / (p : D.host.F) ^ n)) +
      pairA D.host.F 0 (α * algebraMap D.host.F (Af D.host.F) ((b : D.host.F) / (p : D.host.F) ^ n) -
        algebraMap D.host.F (Af D.host.F) ((x : D.host.F) / (p : D.host.F) ^ n)) := by
    refine Prod.ext ?_ ?_
    · show (0 : Ainf D.host.F) * _ = 0 + 0
      rw [zero_mul, add_zero]
    · show α * algebraMap D.host.F (Af D.host.F) ((b : D.host.F) / (p : D.host.F) ^ n) =
        algebraMap D.host.F (Af D.host.F) ((x : D.host.F) / (p : D.host.F) ^ n) +
        (α * algebraMap D.host.F (Af D.host.F) ((b : D.host.F) / (p : D.host.F) ^ n) -
          algebraMap D.host.F (Af D.host.F) ((x : D.host.F) / (p : D.host.F) ^ n))
      rw [add_sub_cancel]
  have htr : ∀ r : 𝓞 D.host.F, Algebra.trace ℚ D.host.F (r : D.host.F) = ((Algebra.intTrace ℤ (𝓞 D.host.F) r : ℤ) : ℚ) :=
    fun r => (Algebra.algebraMap_intTrace (A := ℤ) (K := ℚ) (L := D.host.F) r).symm
  have h1 : ψ (pairA D.host.F 0 (α * algebraMap D.host.F (Af D.host.F) ((b : D.host.F) / (p : D.host.F) ^ n) -
        algebraMap D.host.F (Af D.host.F) ((x : D.host.F) / (p : D.host.F) ^ n))) = 1 := by
    refine GlobalTheory.IntDense.mem_of_isClosed D.host.F (C := {y | ψ (pairA D.host.F 0 y) = 1})
      (isClosed_eq (hψ.1.1.comp (Continuous.prodMk continuous_const continuous_id)) continuous_const)
      (fun r => ?_) _ hint
    show ψ (pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) (r : D.host.F))) = 1
    rw [GlobalTheory.StdRat.stdChar_fin_rat D ψ hψ, htr, mul_comm]
    push_cast
    exact Complex.exp_int_mul_two_pi_mul_I _
  rw [hsplit, AddChar.map_add_eq_mul, h1, mul_one, GlobalTheory.StdRat.stdChar_fin_rat D ψ hψ]
  have hq : Algebra.trace ℚ D.host.F ((x : D.host.F) / (p : D.host.F) ^ n) = ((b : ℚ) + p ^ n * m) / p ^ n := by
    have e : (x : D.host.F) / (p : D.host.F) ^ n = (((p : ℚ) ^ n)⁻¹) • (x : D.host.F) := by
      rw [Algebra.smul_def, map_inv₀, map_pow, map_natCast, div_eq_inv_mul]
    rw [e, map_smul, htr, hm, smul_eq_mul]
    push_cast
    ring
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [hq, show 2 * ↑Real.pi * Complex.I * ((((b : ℚ) + p ^ n * m) / p ^ n : ℚ) : ℂ) =
      2 * Real.pi * Complex.I * b / (p : ℂ) ^ n + m * (2 * Real.pi * Complex.I) by
    push_cast; field_simp, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/- English proof (translation)
Introduce `D k _ _ _ _ q PP hid hp hsq hint ψ hψ ψk hch a b n hx`. Establish `hv` using `GlobalTheory.LocMod.PinInhab.v_eq_under q hid`. Establish `hPP : Ideal.absNorm PP.asIdeal = Formalism.L2.Col.qOf PP` using `rfl`. Generalize the expression as in `Formalism.L2.Col.qOf PP = p at hp hsq hx hPP ⊢`. Establish `hpr : ∀ y : D.host.E, (ofSplit q).pr y = q.pr (incA D y)` using `fun _ => rfl`.

Establish `hms : ∀ (x : AE D) (y : k), x * q.sec y = q.sec (q.pr x * y)` using `fun x y => by`. Establish `h` using `q.sec_pr (x * q.sec y)`. Establish `h'` using `q.sec_pr (q.sec y)`. Rewrite `h` using `[map_mul, q.pr_sec]`. Rewrite `h'` using `[q.pr_sec]`.

Rewrite using `[h, mul_left_comm, ← h']`. Establish `h0 : (ψk ((ofSplit q).pr a) : ℂ) = psiE ψ (q.sec (q.pr (incA D (D.host.xi0 * a))))`. Rewrite using `[map_mul, map_mul]`. Conclude with `(hch _).trans (congrArg _ (hms _ _))`. Rewrite using `[h0]`.

Generalize the expression as in `D.host.xi0 * a = x at hx`. Use `set c : D.host.F := (b : D.host.F) / (p : D.host.F) ^ n with hcdef`. Establish `hc : algebraMap D.host.F D.host.E c = (b : D.host.E) / (p : D.host.E) ^ n`. Rewrite using `[hcdef, map_div₀, map_pow, map_intCast, map_natCast]`. Establish `hxs : x = (x - (b : D.host.E) / (p : D.host.E) ^ n) + algebraMap D.host.F D.host.E c`.

Rewrite using `[hc]`. Expand and normalize the polynomial expressions, which then agree. Establish `hadd : ∀ u w : AE D, psiE ψ (u + w) = psiE ψ u * psiE ψ w`. Introduce `u w`. Simplify using `only [GlobalTheory.MixPer.psiE, map_add, AddChar.map_add_eq_mul]`.

Rewrite using `[hxs, map_add, map_add, map_add, hadd]`. Establish `hy : q.pr (incA D (x - (b : D.host.E) / (p : D.host.E) ^ n)) ∈ 𝒪[k]`. Rewrite using `[← hpr]`. Conclude with `(hint _).2 hx`. Establish `h1 : psiE ψ (q.sec (q.pr (incA D (x - (b : D.host.E) / (p : D.host.E) ^ n)))) = 1`.

Rewrite using `[GlobalTheory.MixPer.psiE, GlobalTheory.SplitCharCond.trace_sec q, GlobalTheory.SplitCharCond.snd_trace, GlobalTheory.SplitCharCond.char_int hψ (GlobalTheory.SplitCharCond.trace_int ((q.int_iff _).1 hy))]`. Rewrite using `[h1, one_mul]`. Take `⟨ε, hε, he⟩` from `q.above`. Establish `htr : Algebra.trace (AF D.host.F) (AE D) q.e = ε`. Use `Algebra.TensorProduct.includeLeft_injective (S := AF D.host.F) (algebraMap D.host.F D.host.E).injective ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `algebraMap (AF D.host.F) (AE D) _ = algebraMap (AF D.host.F) (AE D) _`. Rewrite using `[GlobalTheory.FockCompare.SymplVal.trace_AE, he]`. Establish `hinc : incA D (algebraMap D.host.F D.host.E c) = algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) c)` using `GlobalTheory.SplitCharCond.one_tmul_eq c`. Rewrite using `[q.sec_pr, hinc, mul_comm, ← Algebra.smul_def, GlobalTheory.MixPer.psiE, map_smul, smul_eq_mul, htr, mul_comm]`. Establish `hnorm : Ideal.absNorm q.v.asIdeal = p` using `by rw [hv]; exact GlobalTheory.SplitDegOneChar.absNorm_under PP p hp hPP`.

Establish `hsqv : (p : 𝓞 D.host.F) ∉ q.v.asIdeal ^ 2`. Rewrite using `[hv]`. Conclude with `GlobalTheory.SplitDegOneChar.natCast_not_mem_under_sq PP p hsq`. Conclude with `stdChar_placeIdem_div_pow D ψ hψ p hp q.v hnorm hsqv ε hε b n`.
-/
theorem weilChar_pr_eq_exp : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt q.e PP → (Formalism.L2.Col.qOf PP).Prime → ((Formalism.L2.Col.qOf PP : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal ^ 2 → (∀ x, (ofSplit q).pr x ∈ 𝒪[k] ↔ Formalism.L2.Col.IntAt PP x) → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ ψk : AddChar k Circle, (ofSplit q).IsChar ψ ψk → ∀ (a : D.host.E) (b : ℤ) (n : ℕ), Formalism.L2.Col.IntAt PP (D.host.xi0 * a - (b : D.host.E) / (Formalism.L2.Col.qOf PP : D.host.E) ^ n) → (ψk ((ofSplit q).pr a) : ℂ) = Complex.exp (2 * Real.pi * Complex.I * b / (Formalism.L2.Col.qOf PP : ℂ) ^ n) := by
  intro D k _ _ _ _ q PP hid hp hsq hint ψ hψ ψk hch a b n hx
  have hv := GlobalTheory.LocMod.PinInhab.v_eq_under q hid
  have hPP : Ideal.absNorm PP.asIdeal = Formalism.L2.Col.qOf PP := rfl
  generalize Formalism.L2.Col.qOf PP = p at hp hsq hx hPP ⊢
  have hpr : ∀ y : D.host.E, (ofSplit q).pr y = q.pr (incA D y) := fun _ => rfl
  have hms : ∀ (x : AE D) (y : k), x * q.sec y = q.sec (q.pr x * y) := fun x y => by
    have h := q.sec_pr (x * q.sec y)
    have h' := q.sec_pr (q.sec y)
    rw [map_mul, q.pr_sec] at h
    rw [q.pr_sec] at h'
    rw [h, mul_left_comm, ← h']
  have h0 : (ψk ((ofSplit q).pr a) : ℂ) = psiE ψ (q.sec (q.pr (incA D (D.host.xi0 * a)))) := by
    rw [map_mul, map_mul]
    exact (hch _).trans (congrArg _ (hms _ _))
  rw [h0]
  generalize D.host.xi0 * a = x at hx
  set c : D.host.F := (b : D.host.F) / (p : D.host.F) ^ n with hcdef
  have hc : algebraMap D.host.F D.host.E c = (b : D.host.E) / (p : D.host.E) ^ n := by
    rw [hcdef, map_div₀, map_pow, map_intCast, map_natCast]
  have hxs : x = (x - (b : D.host.E) / (p : D.host.E) ^ n) + algebraMap D.host.F D.host.E c := by
    rw [hc]; ring
  have hadd : ∀ u w : AE D, psiE ψ (u + w) = psiE ψ u * psiE ψ w := by
    intro u w; simp only [GlobalTheory.MixPer.psiE, map_add, AddChar.map_add_eq_mul]
  rw [hxs, map_add, map_add, map_add, hadd]
  have hy : q.pr (incA D (x - (b : D.host.E) / (p : D.host.E) ^ n)) ∈ 𝒪[k] := by
    rw [← hpr]; exact (hint _).2 hx
  have h1 : psiE ψ (q.sec (q.pr (incA D (x - (b : D.host.E) / (p : D.host.E) ^ n)))) = 1 := by
    rw [GlobalTheory.MixPer.psiE, GlobalTheory.SplitCharCond.trace_sec q, GlobalTheory.SplitCharCond.snd_trace,
      GlobalTheory.SplitCharCond.char_int hψ (GlobalTheory.SplitCharCond.trace_int ((q.int_iff _).1 hy))]
  rw [h1, one_mul]
  obtain ⟨ε, hε, he⟩ := q.above
  have htr : Algebra.trace (AF D.host.F) (AE D) q.e = ε := by
    refine Algebra.TensorProduct.includeLeft_injective (S := AF D.host.F) (algebraMap D.host.F D.host.E).injective ?_
    change algebraMap (AF D.host.F) (AE D) _ = algebraMap (AF D.host.F) (AE D) _
    rw [GlobalTheory.FockCompare.SymplVal.trace_AE, he]
  have hinc : incA D (algebraMap D.host.F D.host.E c) =
      algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) c) := GlobalTheory.SplitCharCond.one_tmul_eq c
  rw [q.sec_pr, hinc, mul_comm, ← Algebra.smul_def, GlobalTheory.MixPer.psiE, map_smul, smul_eq_mul, htr, mul_comm]
  have hnorm : Ideal.absNorm q.v.asIdeal = p := by rw [hv]; exact GlobalTheory.SplitDegOneChar.absNorm_under PP p hp hPP
  have hsqv : (p : 𝓞 D.host.F) ∉ q.v.asIdeal ^ 2 := by
    rw [hv]; exact GlobalTheory.SplitDegOneChar.natCast_not_mem_under_sq PP p hsq
  exact stdChar_placeIdem_div_pow D ψ hψ p hp q.v hnorm hsqv ε hε b n

end GlobalTheory.SplitDegOnePow
