import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.PowComp

/- English proof (translation)
Rewrite using `[SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`.
-/
theorem smodEq_span_iff {S : Type} [CommRing S] (a x y : S) (n : ℕ) :
    x ≡ y [SMOD ((Ideal.span {a}) ^ n • ⊤ : Submodule S S)] ↔ a ^ n ∣ x - y := by
  rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

/- English proof (translation)
Establish `hiff : ∀ f g : S, (∃ N, (ϖ ^ k) ^ N ∈ Ideal.span {f, g}) ↔ (∃ N, ϖ ^ N ∈ Ideal.span {f, g})`. Introduce `f g`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨N, hN⟩`. Conclude with `⟨k * N, by rwa [pow_mul]⟩`.

Introduce and unpack `⟨N, hN⟩`. Use `⟨N, ?_⟩` and prove the remaining obligations. Rewrite using `[← pow_mul]`. Establish `hle : N ≤ k * N` using `Nat.le_mul_of_pos_left N (Nat.pos_of_ne_zero hk)`. Rewrite using `[← Nat.add_sub_cancel' hle, pow_add]`.

Conclude with `Ideal.mul_mem_right _ _ hN`. Unfold `Val`. Prove the components needed by the constructor for the conclusion. Introduce `h f g hfg`. Conclude with `h f g ((hiff f g).mpr hfg)`.

Introduce `h f g hfg`. Conclude with `h f g ((hiff f g).mp hfg)`.
-/
theorem val_pow_iff {S : Type} [CommRing S] (ϖ : S) (k : ℕ) (hk : k ≠ 0) : Val (ϖ ^ k) ↔ Val ϖ := by
  have hiff : ∀ f g : S, (∃ N, (ϖ ^ k) ^ N ∈ Ideal.span {f, g}) ↔ (∃ N, ϖ ^ N ∈ Ideal.span {f, g}) := by
    intro f g
    constructor
    · rintro ⟨N, hN⟩
      exact ⟨k * N, by rwa [pow_mul]⟩
    · rintro ⟨N, hN⟩
      refine ⟨N, ?_⟩
      rw [← pow_mul]
      have hle : N ≤ k * N := Nat.le_mul_of_pos_left N (Nat.pos_of_ne_zero hk)
      rw [← Nat.add_sub_cancel' hle, pow_add]
      exact Ideal.mul_mem_right _ _ hN
  unfold Val
  constructor
  · intro h f g hfg
    exact h f g ((hiff f g).mpr hfg)
  · intro h f g hfg
    exact h f g ((hiff f g).mp hfg)

/- English proof (translation)
Establish `hH : IsHausdorff (Ideal.span {ϖ ^ k}) S` using `h.toIsHausdorff`. Establish `hP : IsPrecomplete (Ideal.span {ϖ ^ k}) S` using `h.toIsPrecomplete`. Establish `hkpos : 0 < k` using `Nat.pos_of_ne_zero hk`. Establish `H1 : IsHausdorff (Ideal.span {ϖ}) S`. Use `⟨fun x hx => hH.haus' x (fun n => ?_)⟩` and prove the remaining obligations.

Use `hx (k * n)` as an intermediate fact. Rewrite `this`, the goal using `[smodEq_span_iff]`. Rewrite using `[← pow_mul]` and apply the resulting hypothesis. Establish `H2 : IsPrecomplete (Ideal.span {ϖ}) S`. Use `⟨fun f hf => ?_⟩` and prove the remaining obligations.

Take `⟨L, hL⟩` from `hP.prec' (fun n => f (k * n)) (fun {m n} hmn => by`. Use `hf (Nat.mul_le_mul_left k hmn)` as an intermediate fact. Rewrite `this`, the goal using `[smodEq_span_iff]`. Rewrite using `[← pow_mul])` and apply the resulting hypothesis. Use `⟨L, fun n => ?_⟩` and prove the remaining obligations.

Establish `h1` using `hf (Nat.le_mul_of_pos_left n hkpos)`. Establish `h2` using `hL n`. Rewrite `h1`, `h2`, the goal using `[smodEq_span_iff]`. Rewrite `h2` using `[← pow_mul]`. Establish `h3 : ϖ ^ n ∣ f (k * n) - L` using `(pow_dvd_pow ϖ (Nat.le_mul_of_pos_left n hkpos)).trans h2`.

Use `dvd_add h1 h3` as an intermediate fact. Rewrite `this` using `[sub_add_sub_cancel]`. Then use the resulting hypothesis. Conclude with `{ toIsHausdorff := H1, toIsPrecomplete := H2 }`.
-/
theorem isAdicComplete_of_pow {S : Type} [CommRing S] (ϖ : S) (k : ℕ) (hk : k ≠ 0)
    (h : IsAdicComplete (Ideal.span {ϖ ^ k}) S) : IsAdicComplete (Ideal.span {ϖ}) S := by
  have hH : IsHausdorff (Ideal.span {ϖ ^ k}) S := h.toIsHausdorff
  have hP : IsPrecomplete (Ideal.span {ϖ ^ k}) S := h.toIsPrecomplete
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk
  have H1 : IsHausdorff (Ideal.span {ϖ}) S := by
    refine ⟨fun x hx => hH.haus' x (fun n => ?_)⟩
    have := hx (k * n)
    rw [smodEq_span_iff] at this ⊢
    rwa [← pow_mul]
  have H2 : IsPrecomplete (Ideal.span {ϖ}) S := by
    refine ⟨fun f hf => ?_⟩
    obtain ⟨L, hL⟩ := hP.prec' (fun n => f (k * n)) (fun {m n} hmn => by
      have := hf (Nat.mul_le_mul_left k hmn)
      rw [smodEq_span_iff] at this ⊢
      rwa [← pow_mul])
    refine ⟨L, fun n => ?_⟩
    have h1 := hf (Nat.le_mul_of_pos_left n hkpos)
    have h2 := hL n
    rw [smodEq_span_iff] at h1 h2 ⊢
    rw [← pow_mul] at h2
    have h3 : ϖ ^ n ∣ f (k * n) - L := (pow_dvd_pow ϖ (Nat.le_mul_of_pos_left n hkpos)).trans h2
    have := dvd_add h1 h3
    rwa [sub_add_sub_cancel] at this
  exact { toIsHausdorff := H1, toIsPrecomplete := H2 }

/- English proof (translation)
Introduce `S _ ϖ k hk`. Conclude with `⟨val_pow_iff ϖ k hk, isAdicComplete_of_pow ϖ k hk⟩`.
-/
theorem val_pow : ∀ {S : Type} [CommRing S] (ϖ : S) (k : ℕ), k ≠ 0 →
    (Val (ϖ ^ k) ↔ Val ϖ) ∧ (IsAdicComplete (Ideal.span {ϖ ^ k}) S → IsAdicComplete (Ideal.span {ϖ}) S) := by
  intro S _ ϖ k hk
  exact ⟨val_pow_iff ϖ k hk, isAdicComplete_of_pow ϖ k hk⟩

end GlobalTheory.CompanionTheory.PowComp
