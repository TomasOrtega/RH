import Mathlib

namespace Formalism.MainNotions.V.Pf.V2

open IsLocalRing

section Exact

variable {O : Type*} [CommRing O]
  {A B C : Type*} [AddCommGroup A] [Module O A] [AddCommGroup B] [Module O B]
  [AddCommGroup C] [Module O C]

/- English proof (translation)
Establish `h1 : Module.length O B = Module.length O (LinearMap.ker g) + Module.length O (LinearMap.range g)` using `Module.length_eq_add_of_exact (LinearMap.ker g).subtype g.rangeRestrict (Submodule.injective_subtype _) g.surjective_rangeRestrict (by`. Introduce `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Use `⟨⟨x, ?_⟩, rfl⟩` and prove the remaining obligations.

Use `congrArg Subtype.val hx` as an intermediate fact. Simplify using `using this`. Introduce and unpack `⟨y, rfl⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Use the proof step `simp)`.

Establish `h2 : Module.length O (LinearMap.ker g) ≤ Module.length O A`. Establish `hk : LinearMap.ker g = LinearMap.range f` using `(LinearMap.exact_iff.mp h)`. Rewrite using `[hk]`. Conclude with `Module.length_le_of_surjective f.rangeRestrict f.surjective_rangeRestrict`. Establish `h3 : Module.length O (LinearMap.range g) ≤ Module.length O C` using `Module.length_le_of_injective (LinearMap.range g).subtype (Submodule.injective_subtype _)`.

Rewrite using `[h1]`. Conclude with `add_le_add h2 h3`.
-/
theorem length_le_of_exact (f : A →ₗ[O] B) (g : B →ₗ[O] C) (h : Function.Exact f g) :
    Module.length O B ≤ Module.length O A + Module.length O C := by
  have h1 : Module.length O B =
      Module.length O (LinearMap.ker g) + Module.length O (LinearMap.range g) :=
    Module.length_eq_add_of_exact (LinearMap.ker g).subtype g.rangeRestrict
      (Submodule.injective_subtype _) g.surjective_rangeRestrict (by
        intro x
        constructor
        · intro hx
          refine ⟨⟨x, ?_⟩, rfl⟩
          have := congrArg Subtype.val hx
          simpa using this
        · rintro ⟨y, rfl⟩
          apply Subtype.ext
          simp)
  have h2 : Module.length O (LinearMap.ker g) ≤ Module.length O A := by
    have hk : LinearMap.ker g = LinearMap.range f := (LinearMap.exact_iff.mp h)
    rw [hk]
    exact Module.length_le_of_surjective f.rangeRestrict f.surjective_rangeRestrict
  have h3 : Module.length O (LinearMap.range g) ≤ Module.length O C :=
    Module.length_le_of_injective (LinearMap.range g).subtype (Submodule.injective_subtype _)
  rw [h1]
  exact add_le_add h2 h3

end Exact

section Card

variable {O : Type*} [CommRing O] [IsLocalRing O] [Finite (ResidueField O)]

/- English proof (translation)
Proceed by induction on `h with`. Consider the case `of_subsingleton`. Use `⟨inferInstance, 0, ?_, ?_⟩` and prove the remaining obligations. Simplify using `[Module.length_eq_zero]`. Simplify using the standard rewrite rules.

Consider the case `@of_simple_quotient M _ _ N hs _ ih`. Take `⟨hfin, n, hn, hc⟩` from `ih`. Take `⟨I, hI, ⟨e⟩⟩` from `isSimpleModule_iff_quot_maximal.mp hs`. Establish `hIm : I = maximalIdeal O` using `IsLocalRing.eq_maximalIdeal hI`. Substitute `hIm` using the available equality.

Establish `hq : Nat.card (M ⧸ N) = Nat.card (ResidueField O)` using `Nat.card_congr e.toEquiv`. Establish `hfq : Finite (M ⧸ N)` using `Finite.of_equiv (ResidueField O) e.symm.toEquiv`. Establish `hcard : Nat.card M = Nat.card (M ⧸ N) * Nat.card N` using `(Submodule.card_eq_card_quotient_mul_card N).trans (mul_comm _ _)`. Establish `hfM : Finite M`. Apply `Nat.finite_of_card_ne_zero` to reduce the goal to its premises.

Rewrite using `[hcard, hq, hc]`. Establish `: Nat.card (ResidueField O) ≠ 0` using `Nat.card_pos.ne'`. Check the signs of the components of the expression. Use `⟨hfM, n + 1, ?_, ?_⟩` and prove the remaining obligations. Use `Module.length_eq_add_of_exact N.subtype N.mkQ (Submodule.injective_subtype _) (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ N)` as an intermediate fact.

Rewrite using `[this, hn, Module.length_eq_one O (M ⧸ N)]`. Use `norm_cast`. Rewrite using `[hcard, hq, hc, pow_succ, mul_comm]`.
-/
theorem card_of_isFiniteLength {M : Type*} [AddCommGroup M] [Module O M]
    (h : IsFiniteLength O M) :
    Finite M ∧ ∃ n : ℕ, Module.length O M = n ∧ Nat.card M = Nat.card (ResidueField O) ^ n := by
  induction h with
  | of_subsingleton =>
    refine ⟨inferInstance, 0, ?_, ?_⟩
    · simp [Module.length_eq_zero]
    · simp
  | @of_simple_quotient M _ _ N hs _ ih =>
    obtain ⟨hfin, n, hn, hc⟩ := ih
    obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hs
    have hIm : I = maximalIdeal O := IsLocalRing.eq_maximalIdeal hI
    subst hIm
    have hq : Nat.card (M ⧸ N) = Nat.card (ResidueField O) := Nat.card_congr e.toEquiv
    have hfq : Finite (M ⧸ N) := Finite.of_equiv (ResidueField O) e.symm.toEquiv
    have hcard : Nat.card M = Nat.card (M ⧸ N) * Nat.card N :=
      (Submodule.card_eq_card_quotient_mul_card N).trans (mul_comm _ _)
    have hfM : Finite M := by
      apply Nat.finite_of_card_ne_zero
      rw [hcard, hq, hc]
      have : Nat.card (ResidueField O) ≠ 0 := Nat.card_pos.ne'
      positivity
    refine ⟨hfM, n + 1, ?_, ?_⟩
    · have := Module.length_eq_add_of_exact N.subtype N.mkQ (Submodule.injective_subtype _)
        (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ N)
      rw [this, hn, Module.length_eq_one O (M ⧸ N)]
      norm_cast
    · rw [hcard, hq, hc, pow_succ, mul_comm]

end Card

section Hom

variable {O : Type*} [CommRing O] [IsLocalRing O]
  {Q : Type*} [AddCommGroup Q] [Module O Q]

/- English proof (translation)
Proceed by induction on `h with`. Consider the case `@of_subsingleton M _ _ _`. Establish `: Subsingleton (M →ₗ[O] Q)` using `⟨fun f g => LinearMap.ext fun x => by`. Rewrite using `[Subsingleton.elim x 0, map_zero, map_zero]⟩`. Rewrite using `[Module.length_eq_zero (R := O) (M := M →ₗ[O] Q)]`.

Conclude with `bot_le`. Consider the case `@of_simple_quotient M _ _ N hs _ ih`. Take `⟨I, hI, ⟨e⟩⟩` from `isSimpleModule_iff_quot_maximal.mp hs`. Establish `hIm : I = maximalIdeal O` using `IsLocalRing.eq_maximalIdeal hI`. Substitute `hIm` using the available equality.

Establish `hex : Function.Exact (LinearMap.lcomp O Q N.mkQ) (LinearMap.lcomp O Q N.subtype)`. Introduce `g`. Prove the components needed by the constructor for the conclusion. Introduce `hg`. Use `⟨N.liftQ g ?_, ?_⟩` and prove the remaining obligations.

Introduce `x hx`. Use `LinearMap.congr_fun hg ⟨x, hx⟩` as an intermediate fact. Simplify using `using this`. Use extensionality with `x`. Simplify using the standard rewrite rules.

Introduce and unpack `⟨k, rfl⟩`. Use extensionality with `x`. Establish `: N.mkQ (x : M) = 0` using `(Submodule.Quotient.mk_eq_zero N).mpr x.2`. Use `show k (N.mkQ (x : M)) = 0`. Rewrite using `[this, map_zero]`.

Establish `h1` using `length_le_of_exact _ _ hex`. Establish `h2 : Module.length O ((M ⧸ N) →ₗ[O] Q) ≤ 1`. Rewrite using `[(LinearEquiv.congrLeft Q O e).length_eq]`. Conclude with `hQ`. Establish `h3` using `Module.length_eq_add_of_exact N.subtype N.mkQ (Submodule.injective_subtype _) (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ N)`.

Rewrite using `[h3, Module.length_eq_one O (M ⧸ N), add_comm]`. Conclude with `h1.trans (add_le_add h2 ih)`.
-/
theorem length_hom_le (hQ : Module.length O ((O ⧸ maximalIdeal O) →ₗ[O] Q) ≤ 1)
    {M : Type*} [AddCommGroup M] [Module O M] (h : IsFiniteLength O M) :
    Module.length O (M →ₗ[O] Q) ≤ Module.length O M := by
  induction h with
  | @of_subsingleton M _ _ _ =>
    have : Subsingleton (M →ₗ[O] Q) := ⟨fun f g => LinearMap.ext fun x => by
      rw [Subsingleton.elim x 0, map_zero, map_zero]⟩
    rw [Module.length_eq_zero (R := O) (M := M →ₗ[O] Q)]
    exact bot_le
  | @of_simple_quotient M _ _ N hs _ ih =>
    obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hs
    have hIm : I = maximalIdeal O := IsLocalRing.eq_maximalIdeal hI
    subst hIm
    have hex : Function.Exact (LinearMap.lcomp O Q N.mkQ) (LinearMap.lcomp O Q N.subtype) := by
      intro g
      constructor
      · intro hg
        refine ⟨N.liftQ g ?_, ?_⟩
        · intro x hx
          have := LinearMap.congr_fun hg ⟨x, hx⟩
          simpa using this
        · ext x
          simp
      · rintro ⟨k, rfl⟩
        ext x
        have : N.mkQ (x : M) = 0 := (Submodule.Quotient.mk_eq_zero N).mpr x.2
        show k (N.mkQ (x : M)) = 0
        rw [this, map_zero]
    have h1 := length_le_of_exact _ _ hex
    have h2 : Module.length O ((M ⧸ N) →ₗ[O] Q) ≤ 1 := by
      rw [(LinearEquiv.congrLeft Q O e).length_eq]
      exact hQ
    have h3 := Module.length_eq_add_of_exact N.subtype N.mkQ (Submodule.injective_subtype _)
        (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ N)
    rw [h3, Module.length_eq_one O (M ⧸ N), add_comm]
    exact h1.trans (add_le_add h2 ih)

end Hom

section Socle

variable {O : Type*} [CommRing O] [IsDomain O] [IsLocalRing O]

/- English proof (translation)
Break down `Nat.eq_zero_or_pos k with rfl | hk` into its components or cases. Establish `hs : Subsingleton (O ⧸ Ideal.span {p ^ 0})`. Rewrite using `[pow_zero, Ideal.span_singleton_one]`. Conclude with `Ideal.Quotient.subsingleton_iff.mpr rfl`. Establish `: Subsingleton ((O ⧸ maximalIdeal O) →ₗ[O] (O ⧸ Ideal.span {p ^ 0}))` using `⟨fun f g => LinearMap.ext fun x => Subsingleton.elim _ _⟩`.

Rewrite using `[Module.length_eq_zero]`. Conclude with `bot_le`. Take `⟨j, rfl⟩ : ∃ j, k = j + 1` from `⟨k - 1, by omega⟩`. Set `t : O ⧸ Ideal.span {p ^ (j + 1)}` to `Ideal.Quotient.mk _ (p ^ j)`. Establish `ht : ∀ c ∈ maximalIdeal O, c • t = 0`.

Introduce `c hc`. Rewrite `hc` using `[hp, Ideal.mem_span_singleton]`. Take `⟨d, rfl⟩` from `hc`. Use `show (p * d) • (Ideal.Quotient.mk _ (p ^ j)) = 0`. Rewrite using `[Algebra.smul_def]`.

Use `show Ideal.Quotient.mk _ (p * d) * Ideal.Quotient.mk _ (p ^ j) = 0`. Rewrite using `[← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]`. Conclude with `⟨d, by ring⟩`. Set `φ : (O ⧸ maximalIdeal O) →ₗ[O] (O ⧸ Ideal.span {p ^ (j + 1)})` to `Submodule.liftQ _ (LinearMap.toSpanSingleton O _ t) (by`. Introduce `c hc`.

Simplify `ht c hc)` using `[LinearMap.mem_ker]`. Set `ev : ((O ⧸ maximalIdeal O) →ₗ[O] (O ⧸ Ideal.span {p ^ (j + 1)})) →ₗ[O] (O ⧸ Ideal.span {p ^ (j + 1)})` to `LinearMap.applyₗ (1 : O ⧸ maximalIdeal O)`. Establish `hev : Function.Injective ev`. Introduce `f g hfg`. Use `ext`.

Simplify `hfg` using `[ev]`. Establish `hran : ∀ f, ev f ∈ LinearMap.range φ`. Introduce `f`. Take `⟨y, hy⟩` from `Ideal.Quotient.mk_surjective (ev f)`. Establish `h0 : p • ev f = 0` using `by show p • f 1 = 0`.

Rewrite using `[← map_smul]`. Establish `: p • (1 : O ⧸ maximalIdeal O) = 0`. Rewrite using `[Algebra.smul_def, mul_one]`. Use `show Ideal.Quotient.mk _ p = 0`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem, hp]`.

Conclude with `Ideal.mem_span_singleton_self p`. Rewrite using `[this, map_zero]`. Rewrite `h0` using `[← hy, Algebra.smul_def]`. Establish `h1 : Ideal.Quotient.mk (Ideal.span {p ^ (j + 1)}) (p * y) = 0`. Rewrite using `[map_mul]`.

Conclude with `h0`. Rewrite `h1` using `[Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]`. Take `⟨d, hd⟩` from `h1`. Establish `h2 : y = p ^ j * d`. Apply `mul_left_cancel₀ hp0` to reduce the goal to its premises.

Rewrite using `[hd]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨Ideal.Quotient.mk _ d, ?_⟩` and prove the remaining obligations. Rewrite using `[← hy, h2]`. Use `show d • t = _`.

Rewrite using `[Algebra.smul_def]`. Use `show Ideal.Quotient.mk _ d * Ideal.Quotient.mk _ (p ^ j) = _`. Rewrite using `[← map_mul, mul_comm]`. Establish `h1 : Module.length O ((O ⧸ maximalIdeal O) →ₗ[O] (O ⧸ Ideal.span {p ^ (j + 1)})) ≤ Module.length O (LinearMap.range φ)` using `Module.length_le_of_injective (ev.codRestrict _ hran) (by`. Introduce `f g hfg`.

Conclude with `hev (congrArg Subtype.val hfg))`. Establish `h2 : Module.length O (LinearMap.range φ) ≤ Module.length O (O ⧸ maximalIdeal O)` using `Module.length_le_of_surjective φ.rangeRestrict φ.surjective_rangeRestrict`. Establish `h3 : Module.length O (O ⧸ maximalIdeal O) = 1`. Establish `: IsSimpleModule O (O ⧸ maximalIdeal O)` using `isSimpleModule_iff_quot_maximal.mpr ⟨_, inferInstance, ⟨LinearEquiv.refl _ _⟩⟩`. Conclude with `Module.length_eq_one _ _`.

Conclude with `h1.trans (h2.trans h3.le)`.
-/
theorem length_hom_residue_le (p : O) (hp : maximalIdeal O = Ideal.span {p}) (hp0 : p ≠ 0) (k : ℕ) :
    Module.length O ((O ⧸ maximalIdeal O) →ₗ[O] (O ⧸ Ideal.span {p ^ k})) ≤ 1 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have hs : Subsingleton (O ⧸ Ideal.span {p ^ 0}) := by
      rw [pow_zero, Ideal.span_singleton_one]
      exact Ideal.Quotient.subsingleton_iff.mpr rfl
    have : Subsingleton ((O ⧸ maximalIdeal O) →ₗ[O] (O ⧸ Ideal.span {p ^ 0})) :=
      ⟨fun f g => LinearMap.ext fun x => Subsingleton.elim _ _⟩
    rw [Module.length_eq_zero]
    exact bot_le
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩

    let t : O ⧸ Ideal.span {p ^ (j + 1)} := Ideal.Quotient.mk _ (p ^ j)
    have ht : ∀ c ∈ maximalIdeal O, c • t = 0 := by
      intro c hc
      rw [hp, Ideal.mem_span_singleton] at hc
      obtain ⟨d, rfl⟩ := hc
      show (p * d) • (Ideal.Quotient.mk _ (p ^ j)) = 0
      rw [Algebra.smul_def]
      show Ideal.Quotient.mk _ (p * d) * Ideal.Quotient.mk _ (p ^ j) = 0
      rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
      exact ⟨d, by ring⟩
    let φ : (O ⧸ maximalIdeal O) →ₗ[O] (O ⧸ Ideal.span {p ^ (j + 1)}) :=
      Submodule.liftQ _ (LinearMap.toSpanSingleton O _ t) (by
        intro c hc
        simpa [LinearMap.mem_ker] using ht c hc)
    let ev : ((O ⧸ maximalIdeal O) →ₗ[O] (O ⧸ Ideal.span {p ^ (j + 1)})) →ₗ[O]
        (O ⧸ Ideal.span {p ^ (j + 1)}) := LinearMap.applyₗ (1 : O ⧸ maximalIdeal O)
    have hev : Function.Injective ev := by
      intro f g hfg
      ext
      simpa [ev] using hfg
    have hran : ∀ f, ev f ∈ LinearMap.range φ := by
      intro f
      obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (ev f)
      have h0 : p • ev f = 0 := by
        show p • f 1 = 0
        rw [← map_smul]
        have : p • (1 : O ⧸ maximalIdeal O) = 0 := by
          rw [Algebra.smul_def, mul_one]
          show Ideal.Quotient.mk _ p = 0
          rw [Ideal.Quotient.eq_zero_iff_mem, hp]
          exact Ideal.mem_span_singleton_self p
        rw [this, map_zero]
      rw [← hy, Algebra.smul_def] at h0
      have h1 : Ideal.Quotient.mk (Ideal.span {p ^ (j + 1)}) (p * y) = 0 := by
        rw [map_mul]; exact h0
      rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h1
      obtain ⟨d, hd⟩ := h1
      have h2 : y = p ^ j * d := by
        apply mul_left_cancel₀ hp0
        rw [hd]; ring
      refine ⟨Ideal.Quotient.mk _ d, ?_⟩
      rw [← hy, h2]
      show d • t = _
      rw [Algebra.smul_def]
      show Ideal.Quotient.mk _ d * Ideal.Quotient.mk _ (p ^ j) = _
      rw [← map_mul, mul_comm]
    have h1 : Module.length O ((O ⧸ maximalIdeal O) →ₗ[O] (O ⧸ Ideal.span {p ^ (j + 1)})) ≤
        Module.length O (LinearMap.range φ) :=
      Module.length_le_of_injective (ev.codRestrict _ hran) (by
        intro f g hfg
        exact hev (congrArg Subtype.val hfg))
    have h2 : Module.length O (LinearMap.range φ) ≤ Module.length O (O ⧸ maximalIdeal O) :=
      Module.length_le_of_surjective φ.rangeRestrict φ.surjective_rangeRestrict
    have h3 : Module.length O (O ⧸ maximalIdeal O) = 1 := by
      have : IsSimpleModule O (O ⧸ maximalIdeal O) :=
        isSimpleModule_iff_quot_maximal.mpr ⟨_, inferInstance, ⟨LinearEquiv.refl _ _⟩⟩
      exact Module.length_eq_one _ _
    exact h1.trans (h2.trans h3.le)

end Socle

end Formalism.MainNotions.V.Pf.V2
