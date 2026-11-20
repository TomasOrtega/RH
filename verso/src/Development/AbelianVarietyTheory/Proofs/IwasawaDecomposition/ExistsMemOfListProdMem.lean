import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.GramCEqTranspose
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSmulMemSpanIntegers

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.SupPowNorm

open Formalism.IndefR.Arith

section Clear

variable {Ks : Type} [Field Ks] [NumberField Ks] {WL : Type} [AddCommGroup WL] [Module Ks WL] [Module (𝓞 Ks) WL]
  [IsScalarTower (𝓞 Ks) Ks WL]

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.SmulMemSpanIntegers.exists_smul_mem_span_integers`. Consider the case `exact _root_.GlobalTheory.SmulMemSpanIntegers.exists_smul_mem_span_integers`. Consider the case `(apply _root_.GlobalTheory.SmulMemSpanIntegers.exists_smul_mem_span_integers <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.SmulMemSpanIntegers.exists_smul_mem_span_integers <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.SmulMemSpanIntegers.exists_smul_mem_span_integers <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.SmulMemSpanIntegers.exists_smul_mem_span_integers ..)`.
-/
theorem exists_smul_mem_span_int {T : Set WL} {g : WL} (hg : g ∈ Submodule.span Ks T) :
    ∃ d : 𝓞 Ks, d ≠ 0 ∧ d • g ∈ Submodule.span (𝓞 Ks) T := by
  first
  | exact @_root_.GlobalTheory.SmulMemSpanIntegers.exists_smul_mem_span_integers
  | exact _root_.GlobalTheory.SmulMemSpanIntegers.exists_smul_mem_span_integers
  | (apply _root_.GlobalTheory.SmulMemSpanIntegers.exists_smul_mem_span_integers <;> assumption)
  | (intros; apply _root_.GlobalTheory.SmulMemSpanIntegers.exists_smul_mem_span_integers <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SmulMemSpanIntegers.exists_smul_mem_span_integers <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SmulMemSpanIntegers.exists_smul_mem_span_integers ..)

end Clear

section Forms

variable {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
  {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
  [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL]
  {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
  {G : Type} [Group G] (A : FormsL LL Ks WL W G)

/- English proof (translation)
Take `⟨htW, htb⟩` from `ht`. Establish `hg` using `hW t htW`. Take `⟨d, hd, hdg⟩` from `exists_smul_mem_span_int (hspan _ hg)`. Establish `hdM : d • hL t ∈ A.MK` using `(Submodule.span_le.2 fun x hx => hT x hx) hdg`. Establish `hb : ∀ la y, FinitePlace.mk la (algebraMap (𝓞 Ks) Ks d) * A.nrm la y ⟨hL t, hg⟩ ≤ 1`.

Introduce `la y`. Take `⟨h1, h2⟩` from `hdM`. Use `h2 la y` as an intermediate fact. Establish `e : (⟨d • hL t, h1⟩ : A.WK) = (algebraMap (𝓞 Ks) Ks d) • ⟨hL t, hg⟩` using `Subtype.ext (algebraMap_smul Ks d (hL t)).symm`. Rewrite `this` using `[e, A.nrm_smul]`. Then use the resulting hypothesis.

Establish `hfin : {la : HeightOneSpectrum (𝓞 Ks) | la.asIdeal ∣ Ideal.span {(p : 𝓞 Ks)}}.Finite`. Use `Ideal.finite_factors ?_` and prove the remaining obligations. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `hp.ne_zero` after adjusting the coercions. Establish `hex : ∀ la : HeightOneSpectrum (𝓞 Ks), (p : 𝓞 Ks) ∈ la.asIdeal → ∃ n : ℕ, FinitePlace.mk la (N : Ks) ^ n ≤ FinitePlace.mk la (algebraMap (𝓞 Ks) Ks d)`.

Introduce `la hla`. Establish `hNla : (N : 𝓞 Ks) ∈ la.asIdeal`. Take `⟨k, rfl⟩` from `hpN`. Use `push_cast`. Conclude with `la.asIdeal.mul_mem_right _ hla`.

Establish `h1 : FinitePlace.mk la (N : Ks) < 1`. Rewrite using `[FinitePlace.mk_apply]`. Use `(FinitePlace.norm_lt_one_iff_mem Ks la (N : 𝓞 Ks)).2 hNla` as an intermediate fact. Simplify using `using this`. Establish `h2 : 0 < FinitePlace.mk la (algebraMap (𝓞 Ks) Ks d)` using `FinitePlace.pos_iff.2 (by simpa using hd)`.

Take `⟨n, hn⟩` from `exists_pow_lt_of_lt_one h2 h1`. Conclude with `⟨n, hn.le⟩`. Use `choose! nf hnf using hex`. Use `⟨hfin.toFinset.sup nf, fun m hm => ?_⟩` and prove the remaining obligations. Establish `hmW : N ^ m • hL t ∈ A.WK`.

Rewrite using `[← Nat.cast_smul_eq_nsmul Ks]`. Conclude with `A.WK.smul_mem _ hg`. Use `⟨hmW, fun la y => ?_⟩` and prove the remaining obligations. Establish `e : (⟨N ^ m • hL t, hmW⟩ : A.WK) = ((N : Ks) ^ m) • ⟨hL t, hg⟩` using `Subtype.ext (by rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]; rfl)`. Rewrite using `[e, A.nrm_smul, map_pow]`.

Establish `hN1 : FinitePlace.mk la (N : Ks) ≤ 1`. Rewrite using `[FinitePlace.mk_apply]`. Simplify using `using FinitePlace.norm_le_one Ks la (N : 𝓞 Ks)`. Establish `hN0 : 0 ≤ FinitePlace.mk la (N : Ks)` using `by positivity`. Establish `h0` using `A.nrm_nonneg la y ⟨hL t, hg⟩`.

Distinguish the cases in `hla : (p : 𝓞 Ks) ∈ la.asIdeal`. Establish `hmem : la ∈ hfin.toFinset`. Rewrite using `[Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]`. Conclude with `hla`. Establish `hle : nf la ≤ m` using `(Finset.le_sup hmem).trans hm`.

Combine the equalities or inequalities in the displayed calculation. Use `hsup la hla t htW (htb la) y` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_pow_smul_mem_MK (hL : WL →ₗ[LL] WL) (T : Finset WL) (hT : ∀ x ∈ T, x ∈ A.MK)
    (hspan : ∀ x ∈ A.WK, x ∈ Submodule.span Ks (T : Set WL)) (hW : ∀ x ∈ A.WK, hL x ∈ A.WK)
    {N p : ℕ} (hp : p.Prime) (hpN : p ∣ N)
    (hsup : ∀ la : HeightOneSpectrum (𝓞 Ks), (p : 𝓞 Ks) ∉ la.asIdeal → ∀ (f : WL) (hf : f ∈ A.WK),
      (∀ y, A.nrm la y ⟨f, hf⟩ ≤ 1) → ∀ y, A.nrm la y ⟨hL f, hW f hf⟩ ≤ 1)
    {t : WL} (ht : t ∈ A.MK) : ∃ n : ℕ, ∀ m, n ≤ m → N ^ m • hL t ∈ A.MK := by
  obtain ⟨htW, htb⟩ := ht
  have hg := hW t htW
  obtain ⟨d, hd, hdg⟩ := exists_smul_mem_span_int (hspan _ hg)
  have hdM : d • hL t ∈ A.MK := (Submodule.span_le.2 fun x hx => hT x hx) hdg
  have hb : ∀ la y, FinitePlace.mk la (algebraMap (𝓞 Ks) Ks d) * A.nrm la y ⟨hL t, hg⟩ ≤ 1 := by
    intro la y
    obtain ⟨h1, h2⟩ := hdM
    have := h2 la y
    have e : (⟨d • hL t, h1⟩ : A.WK) = (algebraMap (𝓞 Ks) Ks d) • ⟨hL t, hg⟩ :=
      Subtype.ext (algebraMap_smul Ks d (hL t)).symm
    rwa [e, A.nrm_smul] at this
  have hfin : {la : HeightOneSpectrum (𝓞 Ks) | la.asIdeal ∣ Ideal.span {(p : 𝓞 Ks)}}.Finite := by
    refine Ideal.finite_factors ?_
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  have hex : ∀ la : HeightOneSpectrum (𝓞 Ks), (p : 𝓞 Ks) ∈ la.asIdeal →
      ∃ n : ℕ, FinitePlace.mk la (N : Ks) ^ n ≤ FinitePlace.mk la (algebraMap (𝓞 Ks) Ks d) := by
    intro la hla
    have hNla : (N : 𝓞 Ks) ∈ la.asIdeal := by
      obtain ⟨k, rfl⟩ := hpN
      push_cast
      exact la.asIdeal.mul_mem_right _ hla
    have h1 : FinitePlace.mk la (N : Ks) < 1 := by
      rw [FinitePlace.mk_apply]
      have := (FinitePlace.norm_lt_one_iff_mem Ks la (N : 𝓞 Ks)).2 hNla
      simpa using this
    have h2 : 0 < FinitePlace.mk la (algebraMap (𝓞 Ks) Ks d) := FinitePlace.pos_iff.2 (by simpa using hd)
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one h2 h1
    exact ⟨n, hn.le⟩
  classical
  choose! nf hnf using hex
  refine ⟨hfin.toFinset.sup nf, fun m hm => ?_⟩
  have hmW : N ^ m • hL t ∈ A.WK := by
    rw [← Nat.cast_smul_eq_nsmul Ks]
    exact A.WK.smul_mem _ hg
  refine ⟨hmW, fun la y => ?_⟩
  have e : (⟨N ^ m • hL t, hmW⟩ : A.WK) = ((N : Ks) ^ m) • ⟨hL t, hg⟩ :=
    Subtype.ext (by rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]; rfl)
  rw [e, A.nrm_smul, map_pow]
  have hN1 : FinitePlace.mk la (N : Ks) ≤ 1 := by
    rw [FinitePlace.mk_apply]
    simpa using FinitePlace.norm_le_one Ks la (N : 𝓞 Ks)
  have hN0 : 0 ≤ FinitePlace.mk la (N : Ks) := by positivity
  have h0 := A.nrm_nonneg la y ⟨hL t, hg⟩
  by_cases hla : (p : 𝓞 Ks) ∈ la.asIdeal
  · have hmem : la ∈ hfin.toFinset := by
      rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
      exact hla
    have hle : nf la ≤ m := (Finset.le_sup hmem).trans hm
    calc FinitePlace.mk la (N : Ks) ^ m * A.nrm la y ⟨hL t, hg⟩
        ≤ FinitePlace.mk la (N : Ks) ^ nf la * A.nrm la y ⟨hL t, hg⟩ :=
          mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hN0 hN1 hle) h0
      _ ≤ FinitePlace.mk la (algebraMap (𝓞 Ks) Ks d) * A.nrm la y ⟨hL t, hg⟩ :=
          mul_le_mul_of_nonneg_right (hnf la hla) h0
      _ ≤ 1 := hb la y
  · have := hsup la hla t htW (htb la) y
    calc FinitePlace.mk la (N : Ks) ^ m * A.nrm la y ⟨hL t, hg⟩ ≤ 1 * 1 :=
          mul_le_mul (pow_le_one₀ hN0 hN1) this h0 zero_le_one
      _ = 1 := one_mul 1

end Forms

section Span

variable {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
  {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
  [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL] [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL]
  {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
  {G : Type} [Group G] (A : FormsL LL Ks WL W G)

/- English proof (translation)
Establish `hex : ∀ t ∈ T, ∃ n : ℕ, ∀ m, n ≤ m → N ^ m • hL t ∈ A.MK` using `fun t ht => exists_pow_smul_mem_MK A hL T hT hspan hW hp hpN hsup (hT t ht)`. Use `choose! nf hnf using hex`. Use `set n := T.sup nf`. Establish `hks : ∀ (a : Ks) (x : WL), hL (a • x) = a • hL x` using `fun a x => LinearMap.map_smul_of_tower hL a x`. Establish `h0 : ∀ f ∈ Submodule.span (𝓞 Ks) (T : Set WL), N ^ n • hL f ∈ A.MK`.

Introduce `f hfs`. Proceed by induction on `hfs using Submodule.span_induction with`. Consider the case `mem t ht => exact hnf t ht n (Finset.le_sup ht)`. Consider the case `zero => rw [map_zero, smul_zero]`. Conclude with `zero_mem _`.

Consider the case `add x y _ _ hx hy => rw [map_add, smul_add]`. Conclude with `add_mem hx hy`. Consider the case `smul a x _ hx`. Rewrite using `[← algebraMap_smul Ks a x, hks, algebraMap_smul, smul_comm]`. Conclude with `A.MK.smul_mem a hx`.

Establish `h1 : ∀ f ∈ A.MK, N ^ n • hL f ∈ A.MK` using `fun f hf => h0 f (hMK f hf)`. Use `⟨n, fun x hx => ?_⟩` and prove the remaining obligations. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem f hf => exact Submodule.subset_span (h1 f hf)`. Consider the case `zero => rw [map_zero, smul_zero]`.

Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [map_add, smul_add]`. Conclude with `add_mem hx hy`. Consider the case `smul b x _ hx`. Rewrite using `[LinearMap.map_smul_of_tower, smul_comm]`.

Conclude with `Submodule.smul_mem _ b hx`.
-/
theorem exists_pow_smul_mem_span (hL : WL →ₗ[LL] WL) (T : Finset WL) (hT : ∀ x ∈ T, x ∈ A.MK)
    (hMK : ∀ x ∈ A.MK, x ∈ Submodule.span (𝓞 Ks) (T : Set WL))
    (hspan : ∀ x ∈ A.WK, x ∈ Submodule.span Ks (T : Set WL)) (hW : ∀ x ∈ A.WK, hL x ∈ A.WK)
    {N p : ℕ} (hp : p.Prime) (hpN : p ∣ N)
    (hsup : ∀ la : HeightOneSpectrum (𝓞 Ks), (p : 𝓞 Ks) ∉ la.asIdeal → ∀ (f : WL) (hf : f ∈ A.WK),
      (∀ y, A.nrm la y ⟨f, hf⟩ ≤ 1) → ∀ y, A.nrm la y ⟨hL f, hW f hf⟩ ≤ 1) :
    ∃ n : ℕ, ∀ x ∈ Submodule.span (𝓞 LL) (A.MK : Set WL),
      N ^ n • hL x ∈ Submodule.span (𝓞 LL) (A.MK : Set WL) := by
  classical
  have hex : ∀ t ∈ T, ∃ n : ℕ, ∀ m, n ≤ m → N ^ m • hL t ∈ A.MK := fun t ht =>
    exists_pow_smul_mem_MK A hL T hT hspan hW hp hpN hsup (hT t ht)
  choose! nf hnf using hex
  set n := T.sup nf
  have hks : ∀ (a : Ks) (x : WL), hL (a • x) = a • hL x := fun a x => LinearMap.map_smul_of_tower hL a x
  have h0 : ∀ f ∈ Submodule.span (𝓞 Ks) (T : Set WL), N ^ n • hL f ∈ A.MK := by
    intro f hfs
    induction hfs using Submodule.span_induction with
    | mem t ht => exact hnf t ht n (Finset.le_sup ht)
    | zero => rw [map_zero, smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add, smul_add]; exact add_mem hx hy
    | smul a x _ hx =>
      rw [← algebraMap_smul Ks a x, hks, algebraMap_smul, smul_comm]
      exact A.MK.smul_mem a hx
  have h1 : ∀ f ∈ A.MK, N ^ n • hL f ∈ A.MK := fun f hf => h0 f (hMK f hf)
  refine ⟨n, fun x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem f hf => exact Submodule.subset_span (h1 f hf)
  | zero => rw [map_zero, smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add, smul_add]; exact add_mem hx hy
  | smul b x _ hx =>
    rw [LinearMap.map_smul_of_tower, smul_comm]
    exact Submodule.smul_mem _ b hx

end Span

section Prime

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
The claim follows from `| [], h => absurd ((Ideal.eq_top_iff_one _).2 (by simpa using h)) P.isPrime.ne_top | a :: l, h => by rw [List.prod_cons] at h rcases P.isPrime.mem_or_mem h with h | h · exact ⟨a, List.mem_cons_self, h⟩ · obtain ⟨x, hx, hxP⟩ := exists_mem_of_list_prod_mem P l h exact ⟨x, List.mem_ …`.
-/
theorem exists_mem_of_list_prod_mem (P : HeightOneSpectrum (𝓞 E)) :
    ∀ l : List (𝓞 E), l.prod ∈ P.asIdeal → ∃ x ∈ l, x ∈ P.asIdeal
  | [], h => absurd ((Ideal.eq_top_iff_one _).2 (by simpa using h)) P.isPrime.ne_top
  | a :: l, h => by
    rw [List.prod_cons] at h
    rcases P.isPrime.mem_or_mem h with h | h
    · exact ⟨a, List.mem_cons_self, h⟩
    · obtain ⟨x, hx, hxP⟩ := exists_mem_of_list_prod_mem P l h
      exact ⟨x, List.mem_cons_of_mem a hx, hxP⟩

/- English proof (translation)
Establish `e : Nat.card (𝓞 E ⧸ P.asIdeal) = Ideal.absNorm P.asIdeal`. Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Establish `hN : Ideal.absNorm P.asIdeal ≠ 0` using `Ideal.absNorm_eq_zero_iff.not.2 P.ne_bot`. Establish `hmem : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∈ P.asIdeal` using `Ideal.absNorm_mem _`. Rewrite `hmem` using `[← Nat.prod_primeFactorsList hN, Nat.cast_list_prod]`.

Take `⟨x, hx, hxP⟩` from `exists_mem_of_list_prod_mem P _ hmem`. Take `⟨p, hp, rfl⟩` from `List.mem_map.1 hx`. Conclude with `⟨p, Nat.prime_of_mem_primeFactorsList hp, hxP, e ▸ Nat.dvd_of_mem_primeFactorsList hp⟩`.
-/
theorem exists_prime_dvd_card (P : HeightOneSpectrum (𝓞 E)) :
    ∃ p : ℕ, p.Prime ∧ (p : 𝓞 E) ∈ P.asIdeal ∧ p ∣ Nat.card (𝓞 E ⧸ P.asIdeal) := by
  have e : Nat.card (𝓞 E ⧸ P.asIdeal) = Ideal.absNorm P.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hN : Ideal.absNorm P.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.2 P.ne_bot
  have hmem : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∈ P.asIdeal := Ideal.absNorm_mem _
  rw [← Nat.prod_primeFactorsList hN, Nat.cast_list_prod] at hmem
  obtain ⟨x, hx, hxP⟩ := exists_mem_of_list_prod_mem P _ hmem
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
  exact ⟨p, Nat.prime_of_mem_primeFactorsList hp, hxP, e ▸ Nat.dvd_of_mem_primeFactorsList hp⟩

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `hco : IsCoprime (p : 𝓞 E) (q : 𝓞 E)` using `((Nat.coprime_primes hp hq).2 hne).cast`. Take `⟨u, v, huv⟩` from `hco`. Conclude with `P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (huv ▸ P.asIdeal.add_mem (P.asIdeal.mul_mem_left _ hpP) (P.asIdeal.mul_mem_left _ hqP)))`.
-/
theorem prime_eq_of_mem (P : HeightOneSpectrum (𝓞 E)) {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpP : (p : 𝓞 E) ∈ P.asIdeal) (hqP : (q : 𝓞 E) ∈ P.asIdeal) : p = q := by
  by_contra hne
  have hco : IsCoprime (p : 𝓞 E) (q : 𝓞 E) := ((Nat.coprime_primes hp hq).2 hne).cast
  obtain ⟨u, v, huv⟩ := hco
  exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (huv ▸ P.asIdeal.add_mem (P.asIdeal.mul_mem_left _ hpP) (P.asIdeal.mul_mem_left _ hqP)))

end Prime

end GlobalTheory.SupPowNorm
