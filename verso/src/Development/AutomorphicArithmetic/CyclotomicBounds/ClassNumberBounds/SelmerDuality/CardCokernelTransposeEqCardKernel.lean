import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.SelmerDuality.Frobenius

namespace KStar.Selmer

open Matrix Module

variable {R : Type*} [CommRing R] {m n : Type*} [Fintype m] [Fintype n]

/- English proof (translation)
Establish `hfin : Finite (Ideal R)` using `Finite.of_injective _ SetLike.coe_injective`. Take `⟨I, hI, hmin⟩` from `(wellFounded_lt (α := Ideal R)).has_min {I : Ideal R | ∀ t : R, (∀ x ∈ I, t * x = 0) → t ∈ p} ⟨⊤, fun t ht => by`. Establish `: t = 0` using `by simpa using ht 1 trivial`. Simplify using `[this]⟩`. Distinguish the cases in `h : ∀ t : R, (∀ x ∈ p • I, t * x = 0) → t ∈ p`.

It suffices to derive a contradiction. Establish `hle : p • I ≤ I` using `Submodule.smul_le_right`. Establish `heq : p • I = I`. Assume the negation of the conclusion as `hne`. Conclude with `hmin _ h (lt_of_le_of_ne hle hne)`.

Take `⟨e, he1, he⟩` from `Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul p I (IsNoetherian.noetherian I) heq.ge`. Establish `hep : e ∈ p` using `hI e he`. Establish `h1 : (1 : R) ∈ p` using `by simpa using p.sub_mem hep he1`. Conclude with `hp.ne_top ((Ideal.eq_top_iff_one p).2 h1)`. Use `push Not at h`.

Take `⟨t, ht, htp⟩` from `h`. Establish `h2 : ¬ ∀ x ∈ I, t * x = 0` using `fun h => htp (hI t h)`. Use `push Not at h2`. Take `⟨b, hb, hb0⟩` from `h2`. Use `⟨t * b, hb0, fun x hx => ?_⟩` and prove the remaining obligations.

Use `ht (x • b) (Submodule.smul_mem_smul hx hb)` as an intermediate fact. Rewrite using `[← this, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem exists_annihilator_of_maximal [Finite R] (p : Ideal R) (hp : p.IsMaximal) :
    ∃ a : R, a ≠ 0 ∧ ∀ x ∈ p, x * a = 0 := by
  have hfin : Finite (Ideal R) := Finite.of_injective _ SetLike.coe_injective
  obtain ⟨I, hI, hmin⟩ := (wellFounded_lt (α := Ideal R)).has_min
    {I : Ideal R | ∀ t : R, (∀ x ∈ I, t * x = 0) → t ∈ p}
    ⟨⊤, fun t ht => by
      have : t = 0 := by simpa using ht 1 trivial
      simp [this]⟩
  by_cases h : ∀ t : R, (∀ x ∈ p • I, t * x = 0) → t ∈ p
  · exfalso
    have hle : p • I ≤ I := Submodule.smul_le_right
    have heq : p • I = I := by
      by_contra hne
      exact hmin _ h (lt_of_le_of_ne hle hne)
    obtain ⟨e, he1, he⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul p I
      (IsNoetherian.noetherian I) heq.ge
    have hep : e ∈ p := hI e he
    have h1 : (1 : R) ∈ p := by simpa using p.sub_mem hep he1
    exact hp.ne_top ((Ideal.eq_top_iff_one p).2 h1)
  · push Not at h
    obtain ⟨t, ht, htp⟩ := h
    have h2 : ¬ ∀ x ∈ I, t * x = 0 := fun h => htp (hI t h)
    push Not at h2
    obtain ⟨b, hb, hb0⟩ := h2
    refine ⟨t * b, hb0, fun x hx => ?_⟩
    have := ht (x • b) (Submodule.smul_mem_smul hx hb)
    rw [← this, smul_eq_mul]
    ring

/- English proof (translation)
The claim follows from `Finite.of_injective (fun f : Module.Dual R M => (f : M → R)) DFunLike.coe_injective`.
-/
private theorem finite_module_dual_of_finite [Finite R] (M : Type*) [AddCommGroup M] [Module R M] [Finite M] :
    Finite (Module.Dual R M) :=
  Finite.of_injective (fun f : Module.Dual R M => (f : M → R)) DFunLike.coe_injective

/- English proof (translation)
Establish `hs : Function.Surjective N.dualRestrict` using `fun g => hR.extension_property N.subtype N.injective_subtype g`. Rewrite using `[Submodule.card_eq_card_quotient_mul_card (LinearMap.ker N.dualRestrict), Nat.card_congr (N.dualRestrict.quotKerEquivOfSurjective hs).toEquiv, Submodule.dualRestrict_ker_eq_dualAnnihilator, Nat.card_congr N.dualQuotEquivDualAnnihilator.toEquiv]`.
-/
private theorem card_dual_mul_quotient (hR : Module.Baer R R) {M : Type*} [AddCommGroup M] [Module R M]
    (N : Submodule R M) : Nat.card (Module.Dual R M) =
      Nat.card (Module.Dual R (M ⧸ N)) * Nat.card (Module.Dual R N) := by
  have hs : Function.Surjective N.dualRestrict := fun g =>
    hR.extension_property N.subtype N.injective_subtype g
  rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.ker N.dualRestrict),
    Nat.card_congr (N.dualRestrict.quotKerEquivOfSurjective hs).toEquiv,
    Submodule.dualRestrict_ker_eq_dualAnnihilator,
    Nat.card_congr N.dualQuotEquivDualAnnihilator.toEquiv]

/- English proof (translation)
Take `⟨p, hp, ⟨e⟩⟩` from `isSimpleModule_iff_quot_maximal.1 ‹IsSimpleModule R M›`. Rewrite using `[Nat.card_congr e.toEquiv, ← Nat.card_congr e.dualMap.toEquiv]`. Take `⟨a, ha, hpa⟩` from `exists_annihilator_of_maximal p hp`. Establish `hle : p ≤ LinearMap.ker (LinearMap.toSpanSingleton R R a)` using `fun x hx => hpa x hx`. Establish `hge : LinearMap.ker (LinearMap.toSpanSingleton R R a) ≤ p`.

Use `(hp.eq_of_le ?_ hle).ge` and prove the remaining obligations. Introduce `h`. Establish `: (1 : R) ∈ LinearMap.ker (LinearMap.toSpanSingleton R R a)` using `h ▸ trivial`. Conclude with `ha (by simpa using this)`. Set `ι : (R ⧸ p) →ₗ[R] R` to `Submodule.liftQ p (LinearMap.toSpanSingleton R R a) hle`.

Establish `hι : Function.Injective ι`. Rewrite using `[← LinearMap.ker_eq_bot]`. Conclude with `Submodule.ker_liftQ_eq_bot _ _ _ hge`. Establish `: Finite (R ⧸ p)` using `Finite.of_surjective _ Ideal.Quotient.mk_surjective`. Use `finite_module_dual_of_finite (R := R) (R ⧸ p)` as an intermediate fact.

Use `Nat.card_le_card_of_injective (fun y : R ⧸ p => (ι ∘ₗ LinearMap.mulLeft R y : Module.Dual R (R ⧸ p))) ?_` and prove the remaining obligations. Introduce `y z hyz`. Simplify using `using hι (LinearMap.congr_fun hyz 1)`.
-/
private theorem card_le_card_dual_of_simple [Finite R] (M : Type*) [AddCommGroup M] [Module R M]
    [IsSimpleModule R M] : Nat.card M ≤ Nat.card (Module.Dual R M) := by
  obtain ⟨p, hp, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.1 ‹IsSimpleModule R M›
  rw [Nat.card_congr e.toEquiv, ← Nat.card_congr e.dualMap.toEquiv]
  obtain ⟨a, ha, hpa⟩ := exists_annihilator_of_maximal p hp
  have hle : p ≤ LinearMap.ker (LinearMap.toSpanSingleton R R a) := fun x hx => hpa x hx
  have hge : LinearMap.ker (LinearMap.toSpanSingleton R R a) ≤ p := by
    refine (hp.eq_of_le ?_ hle).ge
    intro h
    have : (1 : R) ∈ LinearMap.ker (LinearMap.toSpanSingleton R R a) := h ▸ trivial
    exact ha (by simpa using this)
  let ι : (R ⧸ p) →ₗ[R] R := Submodule.liftQ p (LinearMap.toSpanSingleton R R a) hle
  have hι : Function.Injective ι := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ hge
  have : Finite (R ⧸ p) := Finite.of_surjective _ Ideal.Quotient.mk_surjective
  have := finite_module_dual_of_finite (R := R) (R ⧸ p)
  refine Nat.card_le_card_of_injective
    (fun y : R ⧸ p => (ι ∘ₗ LinearMap.mulLeft R y : Module.Dual R (R ⧸ p))) ?_
  intro y z hyz
  simpa using hι (LinearMap.congr_fun hyz 1)

/- English proof (translation)
Proceed by induction on `k using Nat.strong_induction_on with`. Consider the case `_ k ih`. Introduce `M _ _ _ hk`. Use `finite_module_dual_of_finite (R := R) M` as an intermediate fact. Break down `subsingleton_or_nontrivial M with hM | hM` into its components or cases.

Rewrite using `[Nat.card_unique]`. Conclude with `Nat.card_pos`. Distinguish the cases in `h : ∀ N : Submodule R M, N = ⊥ ∨ N = ⊤`. Establish `: IsSimpleModule R M` using `{ eq_bot_or_eq_top := h }`. Conclude with `card_le_card_dual_of_simple M`.

Use `push Not at h`. Take `⟨N, h0, h1⟩` from `h`. Establish `hq : Finite (M ⧸ N)` using `Finite.of_surjective _ N.mkQ_surjective`. Establish `hN : Nontrivial N` using `Submodule.nontrivial_iff_ne_bot.2 h0`. Establish `hQ : Nontrivial (M ⧸ N)` using `Submodule.Quotient.nontrivial_iff.2 h1`.

Establish `a1 : 1 < Nat.card N` using `Finite.one_lt_card`. Establish `a2 : 1 < Nat.card (M ⧸ N)` using `Finite.one_lt_card`. Establish `hc` using `Submodule.card_eq_card_quotient_mul_card N`. Establish `b1` using `ih (Nat.card N) (by rw [← hk, hc]; nlinarith) N rfl`. Establish `b2` using `ih (Nat.card (M ⧸ N)) (by rw [← hk, hc]; nlinarith) (M ⧸ N) rfl`.

Rewrite using `[card_dual_mul_quotient hR N, hc, mul_comm]`. Conclude with `Nat.mul_le_mul b2 b1`.
-/
private theorem card_le_card_dual [Finite R] (hR : Module.Baer R R) (k : ℕ) :
    ∀ (M : Type*) [AddCommGroup M] [Module R M] [Finite M], Nat.card M = k →
      Nat.card M ≤ Nat.card (Module.Dual R M) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro M _ _ _ hk
    have := finite_module_dual_of_finite (R := R) M
    rcases subsingleton_or_nontrivial M with hM | hM
    · rw [Nat.card_unique]
      exact Nat.card_pos
    by_cases h : ∀ N : Submodule R M, N = ⊥ ∨ N = ⊤
    · have : IsSimpleModule R M := { eq_bot_or_eq_top := h }
      exact card_le_card_dual_of_simple M
    push Not at h
    obtain ⟨N, h0, h1⟩ := h
    have hq : Finite (M ⧸ N) := Finite.of_surjective _ N.mkQ_surjective
    have hN : Nontrivial N := Submodule.nontrivial_iff_ne_bot.2 h0
    have hQ : Nontrivial (M ⧸ N) := Submodule.Quotient.nontrivial_iff.2 h1
    have a1 : 1 < Nat.card N := Finite.one_lt_card
    have a2 : 1 < Nat.card (M ⧸ N) := Finite.one_lt_card
    have hc := Submodule.card_eq_card_quotient_mul_card N
    have b1 := ih (Nat.card N) (by rw [← hk, hc]; nlinarith) N rfl
    have b2 := ih (Nat.card (M ⧸ N)) (by rw [← hk, hc]; nlinarith) (M ⧸ N) rfl
    rw [card_dual_mul_quotient hR N, hc, mul_comm]
    exact Nat.mul_le_mul b2 b1

/- English proof (translation)
Use `le_antisymm ?_ (card_le_card_dual hR _ M rfl)` and prove the remaining obligations. Use `Fintype.ofFinite M` as an intermediate fact. Set `g : (M → R) →ₗ[R] M` to `Fintype.linearCombination R id`. Establish `hg : Function.Surjective g` using `fun x => ⟨Pi.single x 1, by simp [g]⟩`. Establish `e` using `g.quotKerEquivOfSurjective hg`.

Establish `h1` using `card_dual_mul_quotient hR (LinearMap.ker g)`. Rewrite `h1` using `[← Nat.card_congr (dotProductEquiv R M).toEquiv, Submodule.card_eq_card_quotient_mul_card (LinearMap.ker g), Nat.card_congr e.toEquiv, ← Nat.card_congr e.dualMap.toEquiv, mul_comm]`. Establish `h2` using `card_le_card_dual hR _ (LinearMap.ker g) rfl`. Establish `h3 : 0 < Nat.card (LinearMap.ker g)` using `Nat.card_pos`. Use `Nat.le_of_mul_le_mul_right ?_ h3` and prove the remaining obligations.

Rewrite using `[h1]`. Conclude with `Nat.mul_le_mul_left _ h2`.
-/
theorem card_dual_of_baer [Finite R] (hR : Module.Baer R R) (M : Type*) [AddCommGroup M]
    [Module R M] [Finite M] : Nat.card (Module.Dual R M) = Nat.card M := by
  classical
  refine le_antisymm ?_ (card_le_card_dual hR _ M rfl)
  have := Fintype.ofFinite M
  let g : (M → R) →ₗ[R] M := Fintype.linearCombination R id
  have hg : Function.Surjective g := fun x => ⟨Pi.single x 1, by simp [g]⟩
  have e := g.quotKerEquivOfSurjective hg
  have h1 := card_dual_mul_quotient hR (LinearMap.ker g)
  rw [← Nat.card_congr (dotProductEquiv R M).toEquiv,
    Submodule.card_eq_card_quotient_mul_card (LinearMap.ker g), Nat.card_congr e.toEquiv,
    ← Nat.card_congr e.dualMap.toEquiv, mul_comm] at h1
  have h2 := card_le_card_dual hR _ (LinearMap.ker g) rfl
  have h3 : 0 < Nat.card (LinearMap.ker g) := Nat.card_pos
  refine Nat.le_of_mul_le_mul_right ?_ h3
  rw [h1]
  exact Nat.mul_le_mul_left _ h2

end KStar.Selmer
