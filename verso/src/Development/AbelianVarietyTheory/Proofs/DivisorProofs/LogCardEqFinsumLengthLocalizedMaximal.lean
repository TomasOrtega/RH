import Mathlib

namespace GlobalTheory.CardLength

variable {R : Type} [CommRing R]

noncomputable def lenAt (w : Ideal R) [w.IsPrime] (Q : Type) [AddCommGroup Q] [Module R Q] : ℕ∞ :=
  Module.length (Localization.AtPrime w) (LocalizedModule w.primeCompl Q)

/- English proof (translation)
The claim follows from `Module.length_eq_add_of_exact (LocalizedModule.map w.primeCompl f) (LocalizedModule.map w.primeCompl g) (LocalizedModule.map_injective _ f hf) (LocalizedModule.map_surjective _ g hg) (LocalizedModule.map_exact _ f g H)`.
-/
theorem lenAt_exact (w : Ideal R) [w.IsPrime] {N M P : Type} [AddCommGroup N] [Module R N]
    [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P] (f : N →ₗ[R] M) (g : M →ₗ[R] P)
    (hf : Function.Injective f) (hg : Function.Surjective g) (H : Function.Exact f g) :
    lenAt w M = lenAt w N + lenAt w P :=
  Module.length_eq_add_of_exact (LocalizedModule.map w.primeCompl f)
    (LocalizedModule.map w.primeCompl g) (LocalizedModule.map_injective _ f hf)
    (LocalizedModule.map_surjective _ g hg) (LocalizedModule.map_exact _ f g H)

/- English proof (translation)
The claim follows from `le_antisymm (Module.length_le_of_injective (LocalizedModule.map w.primeCompl e.toLinearMap) (LocalizedModule.map_injective _ _ e.injective)) (Module.length_le_of_injective (LocalizedModule.map w.primeCompl e.symm.toLinearMap) (LocalizedModule.map_injective _ _ e.symm.injective))`.
-/
theorem lenAt_congr (w : Ideal R) [w.IsPrime] {M N : Type} [AddCommGroup N] [Module R N]
    [AddCommGroup M] [Module R M] (e : M ≃ₗ[R] N) : lenAt w M = lenAt w N :=
  le_antisymm
    (Module.length_le_of_injective (LocalizedModule.map w.primeCompl e.toLinearMap)
      (LocalizedModule.map_injective _ _ e.injective))
    (Module.length_le_of_injective (LocalizedModule.map w.primeCompl e.symm.toLinearMap)
      (LocalizedModule.map_injective _ _ e.symm.injective))

/- English proof (translation)
The claim follows from `Module.length_eq_zero_iff.2 (IsLocalizedModule.subsingleton_of_subsingleton w.primeCompl (LocalizedModule.mkLinearMap w.primeCompl Q))`.
-/
theorem lenAt_subsingleton (w : Ideal R) [w.IsPrime] (Q : Type) [AddCommGroup Q] [Module R Q]
    [Subsingleton Q] : lenAt w Q = 0 :=
  Module.length_eq_zero_iff.2 (IsLocalizedModule.subsingleton_of_subsingleton w.primeCompl
    (LocalizedModule.mkLinearMap w.primeCompl Q))

/- English proof (translation)
Use `Module.length_eq_zero_iff.2 ((IsLocalizedModule.subsingleton_iff w.primeCompl (LocalizedModule.mkLinearMap w.primeCompl (R ⧸ m))).2 ?_)` and prove the remaining obligations. Establish `hnle : ¬ m ≤ w` using `fun hle => h (hm.eq_of_le hw.ne_top hle).symm`. Take `⟨s, hsm, hsw⟩` from `SetLike.not_le_iff_exists.1 hnle`. Introduce `x`. Use `⟨s, hsw, ?_⟩` and prove the remaining obligations.

Take `⟨y, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Rewrite using `[Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `m.mul_mem_right _ hsm`.
-/
theorem lenAt_quot_ne (w m : Ideal R) [hw : w.IsMaximal] [hm : m.IsMaximal] (h : w ≠ m) :
    lenAt w (R ⧸ m) = 0 := by
  refine Module.length_eq_zero_iff.2 ((IsLocalizedModule.subsingleton_iff w.primeCompl
    (LocalizedModule.mkLinearMap w.primeCompl (R ⧸ m))).2 ?_)
  have hnle : ¬ m ≤ w := fun hle => h (hm.eq_of_le hw.ne_top hle).symm
  obtain ⟨s, hsm, hsw⟩ := SetLike.not_le_iff_exists.1 hnle
  intro x
  refine ⟨s, hsw, ?_⟩
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  exact m.mul_mem_right _ hsm

/- English proof (translation)
Use `Module.length_eq_one_iff.2 (isSimpleModule_iff_toSpanSingleton_surjective.2 ⟨?_, ?_⟩)` and prove the remaining obligations. Rewrite using `[← not_subsingleton_iff_nontrivial, IsLocalizedModule.subsingleton_iff m.primeCompl (LocalizedModule.mkLinearMap m.primeCompl (R ⧸ m))]`. Introduce `h`. Take `⟨r, hr, hr0⟩` from `h 1`. Rewrite `hr0` using `[Algebra.smul_def, Ideal.Quotient.algebraMap_eq, mul_one, Ideal.Quotient.eq_zero_iff_mem]`.

Conclude with `hr hr0`. Introduce `x hx y`. Proceed by induction on `x using LocalizedModule.induction_on with`. Consider the case `h a s`. Proceed by induction on `y using LocalizedModule.induction_on with`.

Consider the case `h c t`. Take `⟨r, rfl⟩` from `Ideal.Quotient.mk_surjective a`. Take `⟨r', rfl⟩` from `Ideal.Quotient.mk_surjective c`. Establish `hr : r ∈ m.primeCompl`. Introduce `hrm`.

Apply `hx` to reduce the goal to its premises. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem.2 hrm, LocalizedModule.zero_mk]`. Use `⟨Localization.mk (r' * s) (⟨r, hr⟩ * t), ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.toSpanSingleton_apply, LocalizedModule.mk_smul_mk, LocalizedModule.mk_eq]`. Use `⟨1, ?_⟩` and prove the remaining obligations.

Simplify using `only [Submonoid.smul_def, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Submonoid.coe_mul, Submonoid.coe_one]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lenAt_quot_self (m : Ideal R) [hm : m.IsMaximal] : lenAt m (R ⧸ m) = 1 := by
  refine Module.length_eq_one_iff.2 (isSimpleModule_iff_toSpanSingleton_surjective.2 ⟨?_, ?_⟩)
  · rw [← not_subsingleton_iff_nontrivial, IsLocalizedModule.subsingleton_iff m.primeCompl
      (LocalizedModule.mkLinearMap m.primeCompl (R ⧸ m))]
    intro h
    obtain ⟨r, hr, hr0⟩ := h 1
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, mul_one,
      Ideal.Quotient.eq_zero_iff_mem] at hr0
    exact hr hr0
  · intro x hx y
    induction x using LocalizedModule.induction_on with
    | h a s =>
    induction y using LocalizedModule.induction_on with
    | h c t =>
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨r', rfl⟩ := Ideal.Quotient.mk_surjective c
    have hr : r ∈ m.primeCompl := by
      intro hrm
      apply hx
      rw [Ideal.Quotient.eq_zero_iff_mem.2 hrm, LocalizedModule.zero_mk]
    refine ⟨Localization.mk (r' * s) (⟨r, hr⟩ * t), ?_⟩
    rw [LinearMap.toSpanSingleton_apply, LocalizedModule.mk_smul_mk, LocalizedModule.mk_eq]
    refine ⟨1, ?_⟩
    simp only [Submonoid.smul_def, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
      Submonoid.coe_mul, Submonoid.coe_one]
    congr 1
    ring

/- English proof (translation)
Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `Q _ _ _ hn`. Distinguish the cases in `hQ : Subsingleton Q`.

Use `⟨0, fun w => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[lenAt_subsingleton]`. Simplify using the standard rewrite rules. Rewrite using `[Finsupp.prod_zero_index]`. Conclude with `Nat.card_of_subsingleton 0`.

Rewrite `hQ` using `[not_subsingleton_iff_nontrivial]`. Break down `eq_top_or_exists_le_coatom (⊥ : Submodule R Q) with h | ⟨Q1, hQ1, -⟩` into its components or cases. Conclude with `absurd h bot_ne_top`. Establish `hsimple : IsSimpleModule R (Q ⧸ Q1)` using `isSimpleModule_iff_isCoatom.2 hQ1`. Take `⟨m0, hm0, ⟨e⟩⟩` from `isSimpleModule_iff_quot_maximal.1 hsimple`.

Establish `hnt : Nontrivial (Q ⧸ Q1)` using `IsSimpleModule.nontrivial R _`. Establish `hcard : Nat.card Q = Nat.card Q1 * Nat.card (Q ⧸ Q1)` using `Submodule.card_eq_card_quotient_mul_card Q1`. Establish `hfq : Finite (Q ⧸ Q1)` using `Finite.of_surjective _ Q1.mkQ_surjective`. Establish `h1 : 1 < Nat.card (Q ⧸ Q1)` using `Finite.one_lt_card`. Establish `h2 : 0 < Nat.card Q1` using `Nat.card_pos`.

Establish `hlt : Nat.card Q1 < n`. Rewrite using `[← hn, hcard]`. Use the polynomial consequences of the given equalities and inequalities. Take `⟨k1, hk1, hk1c⟩` from `ih _ hlt Q1 rfl`. Use `⟨k1 + Finsupp.single ⟨m0, hm0⟩ 1, fun w => ?_, ?_⟩` and prove the remaining obligations.

Use `w.isMaximal` as an intermediate fact. Rewrite using `[lenAt_exact w.asIdeal Q1.subtype Q1.mkQ Q1.injective_subtype Q1.mkQ_surjective (LinearMap.exact_subtype_mkQ Q1), hk1 w, lenAt_congr w.asIdeal e, Finsupp.add_apply, Finsupp.single_apply]`. Distinguish the cases in `hw : (⟨m0, hm0⟩ : MaximalSpectrum R) = w`. Substitute `hw` using the available equality. Rewrite using `[if_pos rfl, lenAt_quot_self]`.

Simplify using the standard rewrite rules. Rewrite using `[if_neg hw, lenAt_quot_ne w.asIdeal m0 (fun h => hw (MaximalSpectrum.ext h.symm))]`. Simplify using the standard rewrite rules. Establish `hz : ∀ w : MaximalSpectrum R, Nat.card (R ⧸ w.asIdeal) ^ 0 = 1` using `fun _ => pow_zero _`. Establish `ha : ∀ (w : MaximalSpectrum R) (a c : ℕ), Nat.card (R ⧸ w.asIdeal) ^ (a + c) = Nat.card (R ⧸ w.asIdeal) ^ a * Nat.card (R ⧸ w.asIdeal) ^ c` using `fun _ _ _ => pow_add _ _ _`.

Rewrite using `[Finsupp.prod_add_index' (h := fun (w : MaximalSpectrum R) (j : ℕ) => Nat.card (R ⧸ w.asIdeal) ^ j) hz ha, Finsupp.prod_single_index (h := fun (w : MaximalSpectrum R) (j : ℕ) => Nat.card (R ⧸ w.asIdeal) ^ j) (hz _), pow_one, hcard, hk1c, Nat.card_congr e.toEquiv]`.
-/
theorem card_eq_prod_lenAt : ∀ (n : ℕ) (Q : Type) [AddCommGroup Q] [Module R Q] [Finite Q],
    Nat.card Q = n → ∃ k : MaximalSpectrum R →₀ ℕ,
      (∀ w : MaximalSpectrum R, lenAt w.asIdeal Q = (k w : ℕ∞)) ∧
      Nat.card Q = k.prod fun w j => Nat.card (R ⧸ w.asIdeal) ^ j := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Q _ _ _ hn
  by_cases hQ : Subsingleton Q
  · refine ⟨0, fun w => ?_, ?_⟩
    · rw [lenAt_subsingleton]; simp
    · rw [Finsupp.prod_zero_index]; exact Nat.card_of_subsingleton 0
  · rw [not_subsingleton_iff_nontrivial] at hQ
    rcases eq_top_or_exists_le_coatom (⊥ : Submodule R Q) with h | ⟨Q1, hQ1, -⟩
    · exact absurd h bot_ne_top
    · have hsimple : IsSimpleModule R (Q ⧸ Q1) := isSimpleModule_iff_isCoatom.2 hQ1
      obtain ⟨m0, hm0, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.1 hsimple
      have hnt : Nontrivial (Q ⧸ Q1) := IsSimpleModule.nontrivial R _
      have hcard : Nat.card Q = Nat.card Q1 * Nat.card (Q ⧸ Q1) :=
        Submodule.card_eq_card_quotient_mul_card Q1
      have hfq : Finite (Q ⧸ Q1) := Finite.of_surjective _ Q1.mkQ_surjective
      have h1 : 1 < Nat.card (Q ⧸ Q1) := Finite.one_lt_card
      have h2 : 0 < Nat.card Q1 := Nat.card_pos
      have hlt : Nat.card Q1 < n := by
        rw [← hn, hcard]; nlinarith
      obtain ⟨k1, hk1, hk1c⟩ := ih _ hlt Q1 rfl
      refine ⟨k1 + Finsupp.single ⟨m0, hm0⟩ 1, fun w => ?_, ?_⟩
      · have := w.isMaximal
        rw [lenAt_exact w.asIdeal Q1.subtype Q1.mkQ Q1.injective_subtype Q1.mkQ_surjective
          (LinearMap.exact_subtype_mkQ Q1), hk1 w, lenAt_congr w.asIdeal e, Finsupp.add_apply,
          Finsupp.single_apply]
        by_cases hw : (⟨m0, hm0⟩ : MaximalSpectrum R) = w
        · subst hw
          rw [if_pos rfl, lenAt_quot_self]; simp
        · rw [if_neg hw, lenAt_quot_ne w.asIdeal m0
            (fun h => hw (MaximalSpectrum.ext h.symm))]; simp
      · have hz : ∀ w : MaximalSpectrum R, Nat.card (R ⧸ w.asIdeal) ^ 0 = 1 :=
          fun _ => pow_zero _
        have ha : ∀ (w : MaximalSpectrum R) (a c : ℕ), Nat.card (R ⧸ w.asIdeal) ^ (a + c) =
            Nat.card (R ⧸ w.asIdeal) ^ a * Nat.card (R ⧸ w.asIdeal) ^ c := fun _ _ _ => pow_add _ _ _
        rw [Finsupp.prod_add_index'
            (h := fun (w : MaximalSpectrum R) (j : ℕ) => Nat.card (R ⧸ w.asIdeal) ^ j) hz ha,
          Finsupp.prod_single_index
            (h := fun (w : MaximalSpectrum R) (j : ℕ) => Nat.card (R ⧸ w.asIdeal) ^ j) (hz _),
          pow_one, hcard, hk1c, Nat.card_congr e.toEquiv]

/- English proof (translation)
Introduce `B _ N _ _ _`. Take `⟨k, hk, hc⟩` from `card_eq_prod_lenAt (R := B) _ N rfl`. Establish `hlen : ∀ m : MaximalSpectrum B, (Module.length (Localization.AtPrime m.asIdeal) (LocalizedModule m.asIdeal.primeCompl N)).toNat = k m` using `fun m => by`. Establish `h` using `hk m`. Unfold `lenAt at h`.

Rewrite using `[h]`. Both sides reduce to the same expression. Repeatedly rewrite using `[hlen]`. Rewrite using `[finsum_eq_sum_of_support_subset (s := k.support) _ ?_]`. Establish `h0 : (k.prod fun w j => Nat.card (B ⧸ w.asIdeal) ^ j) ≠ 0`.

Rewrite using `[← hc]`. Conclude with `Nat.card_pos.ne'`. Rewrite `h0` using `[Finsupp.prod, Finset.prod_ne_zero_iff]`. Rewrite using `[hc, Finsupp.prod, Nat.cast_prod, Real.log_prod]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations.

Rewrite using `[Nat.cast_pow, Real.log_pow]`. Introduce `m hm`. Conclude with `h0 m hm` after adjusting the coercions. Introduce `m hm`. Rewrite `hm` using `[Function.mem_support]`.

Rewrite using `[Finset.mem_coe, Finsupp.mem_support_iff]`. Introduce `h0`. Apply `hm` to reduce the goal to its premises. Simplify using `[h0]`.
-/
theorem log_card_eq_finsum_length : ∀ (B : Type) [CommRing B] (N : Type) [AddCommGroup N]
    [Module B N] [Finite N], Real.log (Nat.card N) = ∑ᶠ m : MaximalSpectrum B,
      ((Module.length (Localization.AtPrime m.asIdeal)
        (LocalizedModule m.asIdeal.primeCompl N)).toNat : ℝ) * Real.log (Nat.card (B ⧸ m.asIdeal)) := by
  intro B _ N _ _ _
  classical
  obtain ⟨k, hk, hc⟩ := card_eq_prod_lenAt (R := B) _ N rfl
  have hlen : ∀ m : MaximalSpectrum B, (Module.length (Localization.AtPrime m.asIdeal)
      (LocalizedModule m.asIdeal.primeCompl N)).toNat = k m := fun m => by
    have h := hk m
    unfold lenAt at h
    rw [h]; rfl
  simp_rw [hlen]
  rw [finsum_eq_sum_of_support_subset (s := k.support) _ ?_]
  · have h0 : (k.prod fun w j => Nat.card (B ⧸ w.asIdeal) ^ j) ≠ 0 := by
      rw [← hc]; exact Nat.card_pos.ne'
    rw [Finsupp.prod, Finset.prod_ne_zero_iff] at h0
    rw [hc, Finsupp.prod, Nat.cast_prod, Real.log_prod]
    · refine Finset.sum_congr rfl fun m _ => ?_
      rw [Nat.cast_pow, Real.log_pow]
    · intro m hm
      exact_mod_cast h0 m hm
  · intro m hm
    rw [Function.mem_support] at hm
    rw [Finset.mem_coe, Finsupp.mem_support_iff]
    intro h0; apply hm; simp [h0]

end GlobalTheory.CardLength
