import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicIntExistsPowSubNormLeOfExactLevelStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormPowPrimePowSubOneStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory

/- English proof (translation)
Rewrite using `[PadicInt.norm_p, inv_pow, ← zpow_natCast, ← zpow_neg, PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_one, sub_eq_zero, Units.ext_iff]`. Simplify using the standard rewrite rules.
-/
theorem units_map_toZModPow_eq_one_iff (l : ℕ) [Fact l.Prime] (m : ℕ) (u : ℤ_[l]ˣ) :
    Units.map (PadicInt.toZModPow (p := l) m).toMonoidHom u = 1 ↔
      ‖(u : ℤ_[l]) - 1‖ ≤ ‖((l : ℕ) : ℤ_[l])‖ ^ m := by
  rw [PadicInt.norm_p, inv_pow, ← zpow_natCast, ← zpow_neg,
    PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub,
    map_one, sub_eq_zero, Units.ext_iff]
  simp

/- English proof (translation)
Establish `hl : l ≠ 0` using `(Fact.out : l.Prime).ne_zero`. Set `φ : ∀ n : ℕ, G →* (ZMod (l ^ (k + n)))ˣ` to `fun n => (Units.map (PadicInt.toZModPow (p := l) (k + n)).toMonoidHom).comp η`. Establish `hmem : ∀ n g, g ∈ (φ n).ker ↔ ‖(η g : ℤ_[l]) - 1‖ ≤ ‖((l : ℕ) : ℤ_[l])‖ ^ (k + n)` using `fun n g => by`. Rewrite using `[MonoidHom.mem_ker]`. Conclude with `units_map_toZModPow_eq_one_iff l (k + n) (η g)`.

Establish `hlte : ∀ n, ‖(η (γ ^ l ^ n) : ℤ_[l]) - 1‖ = ‖((l : ℕ) : ℤ_[l])‖ ^ (k + n)` using `fun n => by`. Rewrite using `[map_pow, Units.val_pow_eq_pow_val]`. Conclude with `GlobalTheory.T.norm_pow_prime_pow_sub_one_of_norm_sub_one l _ k hk hγ n`. Use `⟨fun n => (φ n).ker, hmem, fun n => inferInstance, fun n => ?_, fun n => ?_, fun n => ?_, fun n h hh => ?_⟩` and prove the remaining obligations. Establish `: NeZero (l ^ (k + n))` using `⟨pow_ne_zero _ hl⟩`.

Rewrite using `[Subgroup.index_ker]`. Conclude with `Nat.card_pos.ne'`. Establish `: NeZero (l ^ (k + n))` using `⟨pow_ne_zero _ hl⟩`. Rewrite using `[Subgroup.index_ker]`. Combine the equalities or inequalities in the displayed calculation.

Conclude with `(hmem n _).2 (hlte n).le`. Take `⟨i, hi⟩` from `GlobalTheory.T.padicInt_exists_pow_sub_norm_le_of_exact_level' l (η (γ ^ l ^ n) : ℤ_[l]) (η h : ℤ_[l]) (k + n) (by omega) (hlte n) ((hmem n h).1 hh)`. Use `⟨i, (hmem (n + 1) _).2 ?_⟩` and prove the remaining obligations. Use `set w : ℤ_[l]ˣ := η ((γ ^ l ^ n) ^ i) with hw`. Establish `hwv : (w : ℤ_[l]) = (η (γ ^ l ^ n) : ℤ_[l]) ^ i`.

Rewrite using `[hw, map_pow η (γ ^ l ^ n) i, Units.val_pow_eq_pow_val]`. Establish `key : ((η (((γ ^ l ^ n) ^ i)⁻¹ * h) : ℤ_[l]ˣ) : ℤ_[l]) - 1 = -((w⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) * ((w : ℤ_[l]) - (η h : ℤ_[l]))`. Rewrite using `[map_mul, map_inv, ← hw, Units.val_mul, mul_sub, neg_mul, neg_mul, Units.inv_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key, norm_mul, norm_neg, hwv]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem congruence_chain_of_character {G : Type*} [Group G] (l : ℕ) [Fact l.Prime]
    (η : G →* ℤ_[l]ˣ) (γ : G) (k : ℕ) (hk : 2 ≤ k)
    (hγ : ‖(η γ : ℤ_[l]) - 1‖ = ‖((l : ℕ) : ℤ_[l])‖ ^ k) :
    ∃ H : ℕ → Subgroup G,
      (∀ n g, g ∈ H n ↔ ‖(η g : ℤ_[l]) - 1‖ ≤ ‖((l : ℕ) : ℤ_[l])‖ ^ (k + n)) ∧
      (∀ n, (H n).Normal) ∧ (∀ n, (H n).index ≠ 0) ∧ (∀ n, (H n).index ≤ l ^ (k + n)) ∧
      (∀ n, γ ^ l ^ n ∈ H n) ∧
      ∀ n, ∀ h ∈ H n, ∃ i : ℕ, ((γ ^ l ^ n) ^ i)⁻¹ * h ∈ H (n + 1) := by
  have hl : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  let φ : ∀ n : ℕ, G →* (ZMod (l ^ (k + n)))ˣ := fun n =>
    (Units.map (PadicInt.toZModPow (p := l) (k + n)).toMonoidHom).comp η
  have hmem : ∀ n g, g ∈ (φ n).ker ↔
      ‖(η g : ℤ_[l]) - 1‖ ≤ ‖((l : ℕ) : ℤ_[l])‖ ^ (k + n) := fun n g => by
    rw [MonoidHom.mem_ker]
    exact units_map_toZModPow_eq_one_iff l (k + n) (η g)
  have hlte : ∀ n, ‖(η (γ ^ l ^ n) : ℤ_[l]) - 1‖ = ‖((l : ℕ) : ℤ_[l])‖ ^ (k + n) := fun n => by
    rw [map_pow, Units.val_pow_eq_pow_val]
    exact GlobalTheory.T.norm_pow_prime_pow_sub_one_of_norm_sub_one l _ k hk hγ n
  refine ⟨fun n => (φ n).ker, hmem, fun n => inferInstance, fun n => ?_, fun n => ?_,
    fun n => ?_, fun n h hh => ?_⟩
  · have : NeZero (l ^ (k + n)) := ⟨pow_ne_zero _ hl⟩
    rw [Subgroup.index_ker]
    exact Nat.card_pos.ne'
  · have : NeZero (l ^ (k + n)) := ⟨pow_ne_zero _ hl⟩
    rw [Subgroup.index_ker]
    calc Nat.card (φ n).range ≤ Nat.card (ZMod (l ^ (k + n))) :=
          Nat.card_le_card_of_injective (fun x => ((x : (ZMod (l ^ (k + n)))ˣ) : ZMod (l ^ (k + n))))
            (fun x y hxy => Subtype.ext (Units.ext hxy))
      _ = l ^ (k + n) := Nat.card_zmod _
  · exact (hmem n _).2 (hlte n).le
  · obtain ⟨i, hi⟩ := GlobalTheory.T.padicInt_exists_pow_sub_norm_le_of_exact_level' l (η (γ ^ l ^ n) : ℤ_[l]) (η h : ℤ_[l]) (k + n) (by omega)
      (hlte n) ((hmem n h).1 hh)
    refine ⟨i, (hmem (n + 1) _).2 ?_⟩
    set w : ℤ_[l]ˣ := η ((γ ^ l ^ n) ^ i) with hw
    have hwv : (w : ℤ_[l]) = (η (γ ^ l ^ n) : ℤ_[l]) ^ i := by
      rw [hw, map_pow η (γ ^ l ^ n) i, Units.val_pow_eq_pow_val]
    have key : ((η (((γ ^ l ^ n) ^ i)⁻¹ * h) : ℤ_[l]ˣ) : ℤ_[l]) - 1 =
        -((w⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) * ((w : ℤ_[l]) - (η h : ℤ_[l])) := by
      rw [map_mul, map_inv, ← hw, Units.val_mul, mul_sub, neg_mul, neg_mul, Units.inv_mul]
      ring
    rw [key, norm_mul, norm_neg, hwv]
    calc _ ≤ 1 * ‖(η (γ ^ l ^ n) : ℤ_[l]) ^ i - (η h : ℤ_[l])‖ :=
          mul_le_mul_of_nonneg_right (PadicInt.norm_le_one _) (norm_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact hi

/- English proof (translation)
Introduce `l _ η γ k hk hγ` and use `congruence_chain_of_character l η γ k hk hγ`.
-/
theorem galois_congruence_chain : ∀ (l : ℕ) [Fact l.Prime] (η : GQ l →* ℤ_[l]ˣ) (γ : GQ l) (k : ℕ), 2 ≤ k → ‖(η γ : ℤ_[l]) - 1‖ = ‖((l : ℕ) : ℤ_[l])‖ ^ k → ∃ H : ℕ → Subgroup (GQ l), (∀ n g, g ∈ H n ↔ ‖(η g : ℤ_[l]) - 1‖ ≤ ‖((l : ℕ) : ℤ_[l])‖ ^ (k + n)) ∧ (∀ n, (H n).Normal) ∧ (∀ n, (H n).index ≠ 0) ∧ (∀ n, (H n).index ≤ l ^ (k + n)) ∧ (∀ n, γ ^ l ^ n ∈ H n) ∧ ∀ n, ∀ h ∈ H n, ∃ i : ℕ, ((γ ^ l ^ n) ^ i)⁻¹ * h ∈ H (n + 1) :=
  fun l _ η γ k hk hγ => congruence_chain_of_character l η γ k hk hγ

end GlobalTheory
