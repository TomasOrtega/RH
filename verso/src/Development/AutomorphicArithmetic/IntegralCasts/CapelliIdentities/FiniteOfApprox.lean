import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective

open IsLocalRing Polynomial

namespace UpperTheory.Reformulated.B.Ra2

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => intro Q _; exact ⟨0, Q, by simp, rfl⟩`. Consider the case `succ n ih`. Introduce `Q hQ`. Take `⟨c, hc⟩` from `hQ 0 (Nat.succ_pos n)`.

Take `⟨A, B, hAB, hB⟩` from `ih Q.divX (fun i hi => by`. Rewrite using `[coeff_divX]`. Conclude with `hQ _ (Nat.succ_lt_succ hi))`. Use `⟨A * X + C c, B, ?_, by rw [hB, coeff_divX]⟩` and prove the remaining obligations. Use `conv_lhs => rw [← divX_mul_X_add Q, hAB, hc]`.

Simplify using `only [C_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma split_low {O : Type} [CommRing O] (ϖ : O) (n : ℕ) :
    ∀ Q : O[X], (∀ i < n, ϖ ∣ Q.coeff i) →
      ∃ A B : O[X], Q = C ϖ * A + X ^ n * B ∧ B.coeff 0 = Q.coeff n := by
  induction n with
  | zero => intro Q _; exact ⟨0, Q, by simp, rfl⟩
  | succ n ih =>
    intro Q hQ
    obtain ⟨c, hc⟩ := hQ 0 (Nat.succ_pos n)
    obtain ⟨A, B, hAB, hB⟩ := ih Q.divX (fun i hi => by
      rw [coeff_divX]; exact hQ _ (Nat.succ_lt_succ hi))
    refine ⟨A * X + C c, B, ?_, by rw [hB, coeff_divX]⟩
    conv_lhs => rw [← divX_mul_X_add Q, hAB, hc]
    simp only [C_mul]
    ring

/- English proof (translation)
Establish `hp0 : algebraMap O R ϖ ≠ 0` using `fun h => hϖ.ne_zero (hinj (by rw [h, map_zero]))`. Establish `hfin : FiniteMultiplicity (C ϖ) P` using `FiniteMultiplicity.of_not_isUnit (fun h => hϖ.not_isUnit (Polynomial.isUnit_C.mp h)) hP`. Take `⟨Q, hPQ, hQ⟩` from `hfin.exists_eq_pow_mul_and_not_dvd`. Establish `hQx : aeval x Q = 0`. Rewrite `hPx` using `[hPQ, map_mul, map_pow, aeval_C]`.

Conclude with `(mul_eq_zero.mp hPx).resolve_left (pow_ne_zero _ hp0)`. Establish `hex : ∃ i, ¬ ϖ ∣ Q.coeff i`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Conclude with `hQ ((Polynomial.C_dvd_iff_dvd_coeff _ _).mpr hcon)`.

Establish `hn : ¬ ϖ ∣ Q.coeff (Nat.find hex)` using `Nat.find_spec hex`. Establish `hlow : ∀ i < Nat.find hex, ϖ ∣ Q.coeff i` using `fun i hi => not_not.mp (Nat.find_min hex hi)`. Take `⟨A, B, hAB, hB⟩` from `split_low ϖ _ Q hlow`. Establish `hu : IsUnit (B.coeff 0)`. Assume the negation of the conclusion as `hcon`.

Establish `h1 : B.coeff 0 ∈ maximalIdeal O` using `hcon`. Rewrite `h1` using `[hϖ.maximalIdeal_eq, Ideal.mem_span_singleton, hB]`. Conclude with `hn h1`. Establish `hBu : IsUnit (aeval x B)`. Assume the negation of the conclusion as `hcon`.

Establish `h1 : aeval x B ∈ maximalIdeal R` using `hcon`. Establish `h2 : aeval x B = aeval x B.divX * x + algebraMap O R (B.coeff 0)` using `by conv_lhs => rw [← divX_mul_X_add B]`. Simplify using the standard rewrite rules. Establish `h3 : algebraMap O R (B.coeff 0) ∈ maximalIdeal R`. Use `Ideal.sub_mem _ h1 (Ideal.mul_mem_left _ (aeval x B.divX) hx)` as an intermediate fact.

Rewrite `this` using `[h2, add_sub_cancel_left]`. Then use the resulting hypothesis. Conclude with `h3 (hu.map _)`. Use `⟨Nat.find hex, ?_⟩` and prove the remaining obligations. Rewrite using `[← Ideal.mul_unit_mem_iff_mem _ hBu]`. Establish `h0 : algebraMap O R ϖ * aeval x A + x ^ Nat.find hex * aeval x B = 0`.

Use `hQx` as an intermediate fact. Rewrite `this` using `[hAB]`. Simplify using `using this`. Rewrite using `[eq_neg_of_add_eq_zero_right h0]`. Conclude with `neg_mem (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))`.
-/
private lemma pow_mem_of_alg {O R : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing R] [IsDomain R] [IsLocalRing R] [Algebra O R] [IsLocalHom (algebraMap O R)]
    (hinj : Function.Injective (algebraMap O R)) {ϖ : O} (hϖ : Irreducible ϖ)
    {x : R} (hx : x ∈ maximalIdeal R) {P : O[X]} (hP : P ≠ 0) (hPx : aeval x P = 0) :
    ∃ n, x ^ n ∈ Ideal.span {algebraMap O R ϖ} := by
  classical
  have hp0 : algebraMap O R ϖ ≠ 0 := fun h =>
    hϖ.ne_zero (hinj (by rw [h, map_zero]))
  have hfin : FiniteMultiplicity (C ϖ) P :=
    FiniteMultiplicity.of_not_isUnit (fun h => hϖ.not_isUnit (Polynomial.isUnit_C.mp h)) hP
  obtain ⟨Q, hPQ, hQ⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  have hQx : aeval x Q = 0 := by
    rw [hPQ, map_mul, map_pow, aeval_C] at hPx
    exact (mul_eq_zero.mp hPx).resolve_left (pow_ne_zero _ hp0)
  have hex : ∃ i, ¬ ϖ ∣ Q.coeff i := by
    by_contra hcon
    push_neg at hcon
    exact hQ ((Polynomial.C_dvd_iff_dvd_coeff _ _).mpr hcon)
  have hn : ¬ ϖ ∣ Q.coeff (Nat.find hex) := Nat.find_spec hex
  have hlow : ∀ i < Nat.find hex, ϖ ∣ Q.coeff i := fun i hi =>
    not_not.mp (Nat.find_min hex hi)
  obtain ⟨A, B, hAB, hB⟩ := split_low ϖ _ Q hlow
  have hu : IsUnit (B.coeff 0) := by
    by_contra hcon
    have h1 : B.coeff 0 ∈ maximalIdeal O := hcon
    rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton, hB] at h1
    exact hn h1
  have hBu : IsUnit (aeval x B) := by
    by_contra hcon
    have h1 : aeval x B ∈ maximalIdeal R := hcon
    have h2 : aeval x B = aeval x B.divX * x + algebraMap O R (B.coeff 0) := by
      conv_lhs => rw [← divX_mul_X_add B]
      simp
    have h3 : algebraMap O R (B.coeff 0) ∈ maximalIdeal R := by
      have := Ideal.sub_mem _ h1 (Ideal.mul_mem_left _ (aeval x B.divX) hx)
      rwa [h2, add_sub_cancel_left] at this
    exact h3 (hu.map _)
  refine ⟨Nat.find hex, ?_⟩
  rw [← Ideal.mul_unit_mem_iff_mem _ hBu]
  have h0 : algebraMap O R ϖ * aeval x A + x ^ Nat.find hex * aeval x B = 0 := by
    have := hQx
    rw [hAB] at this
    simpa using this
  rw [eq_neg_of_add_eq_zero_right h0]
  exact neg_mem (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))

/- English proof (translation)
Take `⟨s, hs⟩ : I.FG` from `IsNoetherian.noetherian I`. Substitute `hs` using the available equality. Use `⟨Submodule.span O s, Submodule.fg_span s.finite_toSet, fun z hz => ?_⟩` and prove the remaining obligations. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem y hy => exact ⟨y, Submodule.subset_span hy, by simp⟩`.

Consider the case `zero => exact ⟨0, zero_mem _, by simp⟩`. Consider the case `add a b _ _ ha hb`. Take `⟨u, hu, hu'⟩` from `ha`. Take `⟨v, hv, hv'⟩` from `hb`. Use `⟨u + v, add_mem hu hv, ?_⟩` and prove the remaining obligations.

Use `add_mem hu' hv'` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Consider the case `smul r a ha' ha`. Take `⟨u, hu, hu'⟩` from `ha`.

Take `⟨c, hc⟩` from `UpperTheory.V.Alg.IsCO.res_surj (O := O) r`. Use `⟨c • u, Submodule.smul_mem _ _ hu, ?_⟩` and prove the remaining obligations. Establish `h1 : (r - algebraMap O R c) * a ∈ maximalIdeal R * Ideal.span (s : Set R)` using `Ideal.mul_mem_mul hc ha'`. Establish `h2` using `Ideal.mul_mem_left _ (algebraMap O R c) hu'`. Use `add_mem h1 h2 using 1` and compare the differences between its conclusion and the goal.

Rewrite using `[smul_eq_mul, Algebra.smul_def]`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma approx_ideal {O R : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R]
    [UpperTheory.V.Alg.IsCO O R] (I : Ideal R) :
    ∃ M : Submodule O R, M.FG ∧ ∀ z ∈ I, ∃ w ∈ M, z - w ∈ maximalIdeal R * I := by
  obtain ⟨s, hs⟩ : I.FG := IsNoetherian.noetherian I
  subst hs
  refine ⟨Submodule.span O s, Submodule.fg_span s.finite_toSet, fun z hz => ?_⟩
  induction hz using Submodule.span_induction with
  | mem y hy => exact ⟨y, Submodule.subset_span hy, by simp⟩
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨u, hu, hu'⟩ := ha
    obtain ⟨v, hv, hv'⟩ := hb
    refine ⟨u + v, add_mem hu hv, ?_⟩
    have := add_mem hu' hv'
    convert this using 1
    ring
  | smul r a ha' ha =>
    obtain ⟨u, hu, hu'⟩ := ha
    obtain ⟨c, hc⟩ := UpperTheory.V.Alg.IsCO.res_surj (O := O) r
    refine ⟨c • u, Submodule.smul_mem _ _ hu, ?_⟩
    have h1 : (r - algebraMap O R c) * a ∈ maximalIdeal R * Ideal.span (s : Set R) :=
      Ideal.mul_mem_mul hc ha'
    have h2 := Ideal.mul_mem_left _ (algebraMap O R c) hu'
    convert add_mem h1 h2 using 1
    rw [smul_eq_mul, Algebra.smul_def]
    ring

/- English proof (translation)
Proceed by induction on `N with`. Consider the case `zero => exact ⟨⊥, Submodule.fg_bot, fun z => ⟨0, zero_mem _, by simp⟩⟩`. Consider the case `succ N ih`. Take `⟨M, hM, h⟩` from `ih`. Take `⟨M', hM', h'⟩` from `approx_ideal (O := O) (maximalIdeal R ^ N)`.

Use `⟨M ⊔ M', hM.sup hM', fun z => ?_⟩` and prove the remaining obligations. Take `⟨w, hw, hzw⟩` from `h z`. Take `⟨w', hw', hzw'⟩` from `h' _ hzw`. Use `⟨w + w', add_mem (Submodule.mem_sup_left hw) (Submodule.mem_sup_right hw'), ?_⟩` and prove the remaining obligations. Rewrite using `[pow_succ', ← sub_sub]`.

Conclude with `hzw'`.
-/
private lemma approx_pow {O R : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R]
    [UpperTheory.V.Alg.IsCO O R] (N : ℕ) :
    ∃ M : Submodule O R, M.FG ∧ ∀ z : R, ∃ w ∈ M, z - w ∈ maximalIdeal R ^ N := by
  induction N with
  | zero => exact ⟨⊥, Submodule.fg_bot, fun z => ⟨0, zero_mem _, by simp⟩⟩
  | succ N ih =>
    obtain ⟨M, hM, h⟩ := ih
    obtain ⟨M', hM', h'⟩ := approx_ideal (O := O) (maximalIdeal R ^ N)
    refine ⟨M ⊔ M', hM.sup hM', fun z => ?_⟩
    obtain ⟨w, hw, hzw⟩ := h z
    obtain ⟨w', hw', hzw'⟩ := h' _ hzw
    refine ⟨w + w', add_mem (Submodule.mem_sup_left hw) (Submodule.mem_sup_right hw'), ?_⟩
    rw [pow_succ', ← sub_sub]
    exact hzw'

/- English proof (translation)
Take `⟨s, g, hg⟩` from `Submodule.fg_iff_exists_fin_generating_family.mp hM`. Establish `hϖI : ϖ ∈ maximalIdeal O` using `hϖ ▸ Ideal.mem_span_singleton_self ϖ`. Set `G : (Fin s → O) →ₗ[O] R` to `Fintype.linearCombination O g`. Establish `hstep : ∀ y : R, ∃ (c : Fin s → O) (y' : R), y = G c + algebraMap O R ϖ * y'`. Introduce `y`.

Take `⟨w, hw, hyw⟩` from `h y`. Rewrite `hw` using `[← hg, ← Fintype.range_linearCombination]`. Take `⟨c, rfl⟩` from `hw`. Take `⟨y', hy'⟩` from `Ideal.mem_span_singleton'.mp hyw`. Conclude with `⟨c, y', by rw [mul_comm, hy']; ring⟩`.

Use `choose φ ψ hφ using hstep`. Establish `hmap : ∀ (n : ℕ) (a : O), a ∈ maximalIdeal O ^ n → algebraMap O R a ∈ maximalIdeal R ^ n`. Introduce `n a ha`. Establish `hle : maximalIdeal O ≤ (maximalIdeal R).comap (algebraMap O R)` using `fun b hb => fun hu => hb (IsLocalHom.map_nonunit b hu)`. Conclude with `Ideal.le_comap_pow _ n (Ideal.pow_right_mono hle n ha)`.

Use `Module.Finite.of_surjective G fun z => ?_` and prove the remaining obligations. Set `y : ℕ → R` to `fun k => ψ^[k] z`. Set `S : ℕ → Fin s → O` to `fun n j => ∑ k ∈ Finset.range n, ϖ ^ k * φ (y k) j`. Establish `hSsucc : ∀ n, S (n + 1) = S n + ϖ ^ n • φ (y n)`. Introduce `n`.

Use function extensionality and compare the values at `j`. Simplify using `[S, Finset.sum_range_succ]`. Establish `hS : ∀ n, z = G (S n) + algebraMap O R ϖ ^ n * y n`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero`. Establish `h0 : S 0 = 0`. Use function extensionality and compare the values at `j`. Simplify using `[S]`. Simplify using `[h0, y]`.

Consider the case `succ n ih`. Establish `hy : y (n + 1) = ψ (y n)` using `Function.iterate_succ_apply' ψ n z`. Rewrite using `[hSsucc, map_add, map_smul, hy, Algebra.smul_def, map_pow]`. Use `conv_lhs => rw [ih, hφ (y n)]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hcauchy : ∀ j, ∀ {m n : ℕ}, m ≤ n → S m j ≡ S n j [SMOD (maximalIdeal O ^ m • ⊤ : Submodule O O)]`. Introduce `j m n hmn`. Proceed by induction on `n, hmn using Nat.le_induction with`. Consider the case `base => exact SModEq.refl _`. Consider the case `succ n hmn ih`.

Use `ih.trans ?_` and prove the remaining obligations. Rewrite using `[SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, hSsucc]`. Establish `: S n j - (S n + ϖ ^ n • φ (y n)) j = -(ϖ ^ n * φ (y n) j)`. Simplify using the standard rewrite rules. Rewrite using `[this]`.

Conclude with `neg_mem (Ideal.mul_mem_right _ _ (Ideal.pow_le_pow_right hmn (Ideal.pow_mem_pow hϖI n)))`. Establish `hL : ∀ j, ∃ L : O, ∀ n, S n j ≡ L [SMOD (maximalIdeal O ^ n • ⊤ : Submodule O O)]` using `fun j => IsPrecomplete.prec' _ (hcauchy j)`. Use `choose L hL using hL`. Use `⟨L, ?_⟩` and prove the remaining obligations. Use `(IsHausdorff.eq_iff_smodEq (I := maximalIdeal R)).mpr fun n => ?_` and prove the remaining obligations.

Rewrite using `[SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]`. Establish `hd : G L - z = G (L - S n) - algebraMap O R ϖ ^ n * y n` using `by conv_lhs => rw [hS n]`. Rewrite using `[map_sub]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hd]`.

Use `sub_mem ?_ (Ideal.mul_mem_right _ _ ?_)` and prove the remaining obligations. Establish `hG : G (L - S n) = ∑ j, (L - S n) j • g j` using `Fintype.linearCombination_apply O g _`. Rewrite using `[hG]`. Use `Ideal.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def]`.

Use `Ideal.mul_mem_right _ _ (hmap n _ ?_)` and prove the remaining obligations. Establish `h1` using `(hL j n).symm`. Rewrite `h1` using `[SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]`. Conclude with `h1`. Rewrite using `[← map_pow]`.

Conclude with `hmap n _ (Ideal.pow_mem_pow hϖI n)`.
-/
private lemma finite_of_approx {O R : Type} [CommRing O] [IsLocalRing O]
    [IsAdicComplete (maximalIdeal O) O] [CommRing R] [IsLocalRing R] [Algebra O R]
    [IsLocalHom (algebraMap O R)] [IsHausdorff (maximalIdeal R) R]
    {ϖ : O} (hϖ : maximalIdeal O = Ideal.span {ϖ}) {M : Submodule O R} (hM : M.FG)
    (h : ∀ z : R, ∃ w ∈ M, z - w ∈ Ideal.span {algebraMap O R ϖ}) : Module.Finite O R := by
  obtain ⟨s, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hM
  have hϖI : ϖ ∈ maximalIdeal O := hϖ ▸ Ideal.mem_span_singleton_self ϖ
  let G : (Fin s → O) →ₗ[O] R := Fintype.linearCombination O g
  have hstep : ∀ y : R, ∃ (c : Fin s → O) (y' : R), y = G c + algebraMap O R ϖ * y' := by
    intro y
    obtain ⟨w, hw, hyw⟩ := h y
    rw [← hg, ← Fintype.range_linearCombination] at hw
    obtain ⟨c, rfl⟩ := hw
    obtain ⟨y', hy'⟩ := Ideal.mem_span_singleton'.mp hyw
    exact ⟨c, y', by rw [mul_comm, hy']; ring⟩
  choose φ ψ hφ using hstep
  have hmap : ∀ (n : ℕ) (a : O), a ∈ maximalIdeal O ^ n →
      algebraMap O R a ∈ maximalIdeal R ^ n := by
    intro n a ha
    have hle : maximalIdeal O ≤ (maximalIdeal R).comap (algebraMap O R) := fun b hb =>
      fun hu => hb (IsLocalHom.map_nonunit b hu)
    exact Ideal.le_comap_pow _ n (Ideal.pow_right_mono hle n ha)
  refine Module.Finite.of_surjective G fun z => ?_
  let y : ℕ → R := fun k => ψ^[k] z
  let S : ℕ → Fin s → O := fun n j => ∑ k ∈ Finset.range n, ϖ ^ k * φ (y k) j
  have hSsucc : ∀ n, S (n + 1) = S n + ϖ ^ n • φ (y n) := by
    intro n
    funext j
    simp [S, Finset.sum_range_succ]
  have hS : ∀ n, z = G (S n) + algebraMap O R ϖ ^ n * y n := by
    intro n
    induction n with
    | zero =>
      have h0 : S 0 = 0 := by
        funext j
        simp [S]
      simp [h0, y]
    | succ n ih =>
      have hy : y (n + 1) = ψ (y n) := Function.iterate_succ_apply' ψ n z
      rw [hSsucc, map_add, map_smul, hy, Algebra.smul_def, map_pow]
      conv_lhs => rw [ih, hφ (y n)]
      ring
  have hcauchy : ∀ j, ∀ {m n : ℕ}, m ≤ n →
      S m j ≡ S n j [SMOD (maximalIdeal O ^ m • ⊤ : Submodule O O)] := by
    intro j m n hmn
    induction n, hmn using Nat.le_induction with
    | base => exact SModEq.refl _
    | succ n hmn ih =>
      refine ih.trans ?_
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, hSsucc]
      have : S n j - (S n + ϖ ^ n • φ (y n)) j = -(ϖ ^ n * φ (y n) j) := by
        simp
      rw [this]
      exact neg_mem (Ideal.mul_mem_right _ _
        (Ideal.pow_le_pow_right hmn (Ideal.pow_mem_pow hϖI n)))
  have hL : ∀ j, ∃ L : O, ∀ n, S n j ≡ L [SMOD (maximalIdeal O ^ n • ⊤ : Submodule O O)] :=
    fun j => IsPrecomplete.prec' _ (hcauchy j)
  choose L hL using hL
  refine ⟨L, ?_⟩
  refine (IsHausdorff.eq_iff_smodEq (I := maximalIdeal R)).mpr fun n => ?_
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
  have hd : G L - z = G (L - S n) - algebraMap O R ϖ ^ n * y n := by
    conv_lhs => rw [hS n]
    rw [map_sub]
    ring
  rw [hd]
  refine sub_mem ?_ (Ideal.mul_mem_right _ _ ?_)
  · have hG : G (L - S n) = ∑ j, (L - S n) j • g j := Fintype.linearCombination_apply O g _
    rw [hG]
    refine Ideal.sum_mem _ fun j _ => ?_
    rw [Algebra.smul_def]
    refine Ideal.mul_mem_right _ _ (hmap n _ ?_)
    have h1 := (hL j n).symm
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h1
    exact h1
  · rw [← map_pow]
    exact hmap n _ (Ideal.pow_mem_pow hϖI n)

end UpperTheory.Reformulated.B.Ra2

open UpperTheory.Reformulated.B.Ra2 in
/- English proof (translation)
Introduce `O R _ _ _ _ _ _ _ _ hinj halg`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Establish `hrad : maximalIdeal R ≤ (Ideal.span {algebraMap O R ϖ}).radical` using `fun x hx => by`. Take `⟨P, hP, hPx⟩` from `halg x`. Conclude with `pow_mem_of_alg hinj hϖ hx hP hPx`.

Take `⟨N, hN⟩` from `Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)`. Take `⟨M, hM, h⟩` from `approx_pow (O := O) (R := R) N`. Conclude with `finite_of_approx hϖ.maximalIdeal_eq hM fun z => by`. Take `⟨w, hw, hzw⟩` from `h z`. Conclude with `⟨w, hw, hN hzw⟩`.
-/
theorem UpperTheory.Reformulated.B.Ra2.finite_of_alg :
    ∀ {O R : Type} [inst : CommRing O] [inst_1 : IsDomain O] [inst_2 : IsDiscreteValuationRing O]
      [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [inst_4 : CommRing R] [IsDomain R] [inst_6 : Algebra O R]
      [UpperTheory.V.Alg.IsCO O R],
      Function.Injective (⇑(Algebra.algebraMap O R) : O → R) →
        (∀ (a : R), ∃ (P : Polynomial O), P ≠ (0 : Polynomial O) ∧ (Polynomial.aeval a : Polynomial O → R) P = (0 : R)) →
          Module.Finite O R := by
  intro O R _ _ _ _ _ _ _ _ hinj halg
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hrad : maximalIdeal R ≤ (Ideal.span {algebraMap O R ϖ}).radical := fun x hx => by
    obtain ⟨P, hP, hPx⟩ := halg x
    exact pow_mem_of_alg hinj hϖ hx hP hPx
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  obtain ⟨M, hM, h⟩ := approx_pow (O := O) (R := R) N
  exact finite_of_approx hϖ.maximalIdeal_eq hM fun z => by
    obtain ⟨w, hw, hzw⟩ := h z
    exact ⟨w, hw, hN hzw⟩
