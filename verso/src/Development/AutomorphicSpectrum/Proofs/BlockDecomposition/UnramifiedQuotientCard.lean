import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResAlgSplitTwo

open PositivityTheory.PfSWUS.Loc

namespace GlobalTheory.CompanionTheory.UnrDens

private def mulPow {R : Type} [CommRing R] (ϖ : R) (k : ℕ) : R →+ R ⧸ lev ϖ (k + 1) :=
  ((Ideal.Quotient.mk (lev ϖ (k + 1))).toAddMonoidHom).comp (AddMonoidHom.mulLeft (ϖ ^ k))

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem mulPow_apply {R : Type} [CommRing R] (ϖ : R) (k : ℕ) (a : R) :
    mulPow ϖ k a = Ideal.Quotient.mk (lev ϖ (k + 1)) (ϖ ^ k * a) := rfl

/- English proof (translation)
Conclude with `Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow ϖ (Nat.le_succ k))`.
-/
private theorem lev_succ_le {R : Type} [CommRing R] (ϖ : R) (k : ℕ) : lev ϖ (k + 1) ≤ lev ϖ k := by
  exact Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow ϖ (Nat.le_succ k))

/- English proof (translation)
Use extensionality with `a`. Rewrite using `[AddMonoidHom.mem_ker, mulPow_apply, Ideal.Quotient.eq_zero_iff_mem, Submodule.mem_toAddSubgroup]`. Simplify using `only [lev, Ideal.mem_span_singleton]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, hc⟩`.

Use `⟨c, ?_⟩` and prove the remaining obligations. Establish `hinj : Function.Injective (fun y : R => ϖ ^ k • y)` using `hr.pow k`. Apply `hinj` to reduce the goal to its premises. Use `show ϖ ^ k • a = ϖ ^ k • (ϖ ^ 1 * c)`. Rewrite using `[smul_eq_mul, smul_eq_mul, hc]`.

Expand and normalize the polynomial expressions, which then agree. Introduce and unpack `⟨c, hc⟩`. Conclude with `⟨c, by rw [hc]; ring⟩`.
-/
private theorem mulPow_ker {R : Type} [CommRing R] {ϖ : R} (hr : IsSMulRegular R ϖ) (k : ℕ) :
    (mulPow ϖ k).ker = (lev ϖ 1).toAddSubgroup := by
  ext a
  rw [AddMonoidHom.mem_ker, mulPow_apply, Ideal.Quotient.eq_zero_iff_mem, Submodule.mem_toAddSubgroup]
  simp only [lev, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    have hinj : Function.Injective (fun y : R => ϖ ^ k • y) := hr.pow k
    apply hinj
    show ϖ ^ k • a = ϖ ^ k • (ϖ ^ 1 * c)
    rw [smul_eq_mul, smul_eq_mul, hc]
    ring
  · rintro ⟨c, hc⟩
    exact ⟨c, by rw [hc]; ring⟩

/- English proof (translation)
Take `⟨φ, hφ⟩ : ∃ φ : R ⧸ lev ϖ (k + 1) →+ R ⧸ lev ϖ k, ∀ a, φ (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ a` from `⟨(Ideal.Quotient.lift (lev ϖ (k + 1)) (Ideal.Quotient.mk (lev ϖ k)) (fun a ha => Ideal.Quotient.eq_zero_iff_mem.mpr (lev_succ_le ϖ k ha))).toAddMonoidHom, fun a => by simp⟩`. Establish `hsurj : Function.Surjective φ`. Introduce `y`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Conclude with `⟨Ideal.Quotient.mk _ a, hφ a⟩`.

Establish `hker : φ.ker = (mulPow ϖ k).range`. Use extensionality with `x`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Rewrite using `[AddMonoidHom.mem_ker, hφ, AddMonoidHom.mem_range, Ideal.Quotient.eq_zero_iff_mem]`. Prove the components needed by the constructor for the conclusion.

Introduce `ha`. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton.mp ha`. Conclude with `⟨c, by rw [mulPow_apply, ← hc]⟩`. Introduce and unpack `⟨c, hc⟩`. Rewrite `hc` using `[mulPow_apply, Ideal.Quotient.eq]`.

Establish `h1 : ϖ ^ k * c - a ∈ lev ϖ k` using `lev_succ_le ϖ k hc`. Establish `h2 : ϖ ^ k * c ∈ lev ϖ k` using `Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)`. Use `sub_mem h2 h1` as an intermediate fact. Simplify using `using this`. Establish `e1` using `AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup φ.ker`.

Establish `e2 : Nat.card ((R ⧸ lev ϖ (k + 1)) ⧸ φ.ker) = Nat.card (R ⧸ lev ϖ k)` using `Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective φ hsurj).toEquiv`. Establish `e3 : Nat.card φ.ker = Nat.card (R ⧸ lev ϖ 1)`. Rewrite using `[hker]`. Use `Nat.card_congr (QuotientAddGroup.quotientKerEquivRange (mulPow ϖ k)).toEquiv` as an intermediate fact. Rewrite using `[← this, mulPow_ker hr]`.

Both sides reduce to the same expression. Rewrite using `[e1, e2, e3]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem card_quot_lev_succ {R : Type} [CommRing R] {ϖ : R} (hr : IsSMulRegular R ϖ) (k : ℕ) :
    Nat.card (R ⧸ lev ϖ (k + 1)) = Nat.card (R ⧸ lev ϖ 1) * Nat.card (R ⧸ lev ϖ k) := by
  obtain ⟨φ, hφ⟩ : ∃ φ : R ⧸ lev ϖ (k + 1) →+ R ⧸ lev ϖ k,
      ∀ a, φ (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ a :=
    ⟨(Ideal.Quotient.lift (lev ϖ (k + 1)) (Ideal.Quotient.mk (lev ϖ k))
      (fun a ha => Ideal.Quotient.eq_zero_iff_mem.mpr (lev_succ_le ϖ k ha))).toAddMonoidHom,
      fun a => by simp⟩
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Ideal.Quotient.mk _ a, hφ a⟩
  have hker : φ.ker = (mulPow ϖ k).range := by
    ext x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [AddMonoidHom.mem_ker, hφ, AddMonoidHom.mem_range, Ideal.Quotient.eq_zero_iff_mem]
    constructor
    · intro ha
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp ha
      exact ⟨c, by rw [mulPow_apply, ← hc]⟩
    · rintro ⟨c, hc⟩
      rw [mulPow_apply, Ideal.Quotient.eq] at hc
      have h1 : ϖ ^ k * c - a ∈ lev ϖ k := lev_succ_le ϖ k hc
      have h2 : ϖ ^ k * c ∈ lev ϖ k := Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
      have := sub_mem h2 h1
      simpa using this
  have e1 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup φ.ker
  have e2 : Nat.card ((R ⧸ lev ϖ (k + 1)) ⧸ φ.ker) = Nat.card (R ⧸ lev ϖ k) :=
    Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective φ hsurj).toEquiv
  have e3 : Nat.card φ.ker = Nat.card (R ⧸ lev ϖ 1) := by
    rw [hker]
    have := Nat.card_congr (QuotientAddGroup.quotientKerEquivRange (mulPow ϖ k)).toEquiv
    rw [← this, mulPow_ker hr]
    rfl
  rw [e1, e2, e3]
  ring

/- English proof (translation)
Introduce `R _ σ ϖ q ε hR k`. Proceed by induction on `k with`. Consider the case `zero`. Establish `htop : lev ϖ 0 = ⊤` using `by show Ideal.span {ϖ ^ 0} = ⊤`. Rewrite using `[pow_zero]`.

Conclude with `Ideal.span_singleton_one`. Rewrite using `[Nat.mul_zero, pow_zero]`. Conclude with `Nat.card_eq_one_iff_unique.mpr ⟨Ideal.Quotient.subsingleton_iff.mpr htop, ⟨0⟩⟩`. Consider the case `succ k ih`. Rewrite using `[card_quot_lev_succ hR.reg k, ih, hR.card]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem card_quot_lev : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ),
    IsUnrQuad R σ ϖ q ε → ∀ k : ℕ, Nat.card (R ⧸ lev ϖ k) = q ^ (2 * k) := by
  intro R _ σ ϖ q ε hR k
  induction k with
  | zero =>
    have htop : lev ϖ 0 = ⊤ := by
      show Ideal.span {ϖ ^ 0} = ⊤
      rw [pow_zero]
      exact Ideal.span_singleton_one
    rw [Nat.mul_zero, pow_zero]
    exact Nat.card_eq_one_iff_unique.mpr ⟨Ideal.Quotient.subsingleton_iff.mpr htop, ⟨0⟩⟩
  | succ k ih =>
    rw [card_quot_lev_succ hR.reg k, ih, hR.card]
    ring

end GlobalTheory.CompanionTheory.UnrDens
