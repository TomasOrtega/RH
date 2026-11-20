import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PullbackBijectiveDegreesOneTwo
open CategoryTheory GlobalTheory.CxCoh

namespace GlobalTheory.TowerLift

/- English proof (translation)
Establish `step : ∀ n (x : {a : A n // d n a = b n}), ∃ y : {a : A (n + 1) // d (n + 1) a = b (n + 1)}, s n y.1 = x.1`. Introduce `n x`. Take `⟨x', hx'⟩` from `hrg (n + 1)`. Establish `h0 : d n (x.1 - s n x') = 0`. Rewrite using `[map_sub, x.2, ← htd, hx', hb, sub_self]`.

Take `⟨a', w, ha', hw⟩` from `hcl n _ h0`. Take `⟨w', rfl⟩` from `hr n w`. Use `⟨⟨x' + a' + c (n + 1) w', ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, map_add, hx', ha', hdc, add_zero, add_zero]`. Use `show s n (x' + a' + c (n + 1) w') = x.1`.

Rewrite using `[map_add, map_add, hsc, add_assoc, ← hw, add_sub_cancel]`. Use `choose f hf using step`. Take `⟨a₀, ha₀⟩` from `hrg 0`. Set `g : ∀ n, {a : A n // d n a = b n}` to `fun n => Nat.rec ⟨a₀, ha₀⟩ (fun n x => f n x) n`. Conclude with `⟨fun n => (g n).1, fun n => hf n (g n), fun n => (g n).2⟩`.
-/
theorem closed_lift (W A B : ℕ → Type 1) [∀ n, AddCommGroup (W n)] [∀ n, AddCommGroup (A n)] [∀ n, AddCommGroup (B n)] (c : ∀ n, W n →+ A n) (d : ∀ n, A n →+ B n) (r : ∀ n, W (n + 1) →+ W n) (s : ∀ n, A (n + 1) →+ A n) (t : ∀ n, B (n + 1) →+ B n)
    (hdc : ∀ n x, d n (c n x) = 0) (hsc : ∀ n x, s n (c (n + 1) x) = c n (r n x)) (htd : ∀ n x, t n (d (n + 1) x) = d n (s n x))
    (hr : ∀ n, Function.Surjective (r n)) (hcl : ∀ n a, d n a = 0 → ∃ a' w, d (n + 1) a' = 0 ∧ a = s n a' + c n w)
    (b : ∀ n, B n) (hb : ∀ n, t n (b (n + 1)) = b n) (hrg : ∀ n, ∃ a, d n a = b n) :
    ∃ a : ∀ n, A n, (∀ n, s n (a (n + 1)) = a n) ∧ ∀ n, d n (a n) = b n := by
  have step : ∀ n (x : {a : A n // d n a = b n}), ∃ y : {a : A (n + 1) // d (n + 1) a = b (n + 1)}, s n y.1 = x.1 := by
    intro n x
    obtain ⟨x', hx'⟩ := hrg (n + 1)
    have h0 : d n (x.1 - s n x') = 0 := by
      rw [map_sub, x.2, ← htd, hx', hb, sub_self]
    obtain ⟨a', w, ha', hw⟩ := hcl n _ h0
    obtain ⟨w', rfl⟩ := hr n w
    refine ⟨⟨x' + a' + c (n + 1) w', ?_⟩, ?_⟩
    · rw [map_add, map_add, hx', ha', hdc, add_zero, add_zero]
    · show s n (x' + a' + c (n + 1) w') = x.1
      rw [map_add, map_add, hsc, add_assoc, ← hw, add_sub_cancel]
  choose f hf using step
  obtain ⟨a₀, ha₀⟩ := hrg 0
  let g : ∀ n, {a : A n // d n a = b n} := fun n => Nat.rec ⟨a₀, ha₀⟩ (fun n x => f n x) n
  exact ⟨fun n => (g n).1, fun n => hf n (g n), fun n => (g n).2⟩

/- English proof (translation)
Introduce `b₀ hb₀`. Establish `step : ∀ n (x : Z n), ∃ y : Z (n + 1), t n y.1 = x.1`. Introduce `n x`. Take `⟨b', hb', a, ha⟩` from `hl n x.1 x.2`. Take `⟨a'', rfl⟩` from `hs n a`.

Use `⟨⟨b' + d (n + 1) a'', (Z (n + 1)).add_mem hb' (hd _ _)⟩, ?_⟩` and prove the remaining obligations. Use `show t n (b' + d (n + 1) a'') = x.1`. Rewrite using `[map_add, htd, ha]`. Use `choose f hf using step`. Set `g : ∀ n, Z n` to `fun n => Nat.rec ⟨b₀, hb₀⟩ (fun n x => f n x) n`.

Conclude with `⟨fun n => (g n).1, rfl, fun n => (g n).2, fun n => hf n (g n)⟩`.
-/
theorem closed_extend (A B : ℕ → Type 1) [∀ n, AddCommGroup (A n)] [∀ n, AddCommGroup (B n)] (Z : ∀ n, AddSubgroup (B n)) (d : ∀ n, A n →+ B n) (s : ∀ n, A (n + 1) →+ A n) (t : ∀ n, B (n + 1) →+ B n)
    (hd : ∀ n x, d n x ∈ Z n) (htd : ∀ n x, t n (d (n + 1) x) = d n (s n x)) (hs : ∀ n, Function.Surjective (s n))
    (hZ : ∀ n, ∀ x ∈ Z (n + 1), t n x ∈ Z n) (hl : ∀ n, ∀ b ∈ Z n, ∃ b' ∈ Z (n + 1), ∃ a, b = t n b' + d n a) :
    ∀ b₀ ∈ Z 0, ∃ b : ∀ n, B n, b 0 = b₀ ∧ (∀ n, b n ∈ Z n) ∧ ∀ n, t n (b (n + 1)) = b n := by
  intro b₀ hb₀
  have step : ∀ n (x : Z n), ∃ y : Z (n + 1), t n y.1 = x.1 := by
    intro n x
    obtain ⟨b', hb', a, ha⟩ := hl n x.1 x.2
    obtain ⟨a'', rfl⟩ := hs n a
    refine ⟨⟨b' + d (n + 1) a'', (Z (n + 1)).add_mem hb' (hd _ _)⟩, ?_⟩
    show t n (b' + d (n + 1) a'') = x.1
    rw [map_add, htd, ha]
  choose f hf using step
  let g : ∀ n, Z n := fun n => Nat.rec ⟨b₀, hb₀⟩ (fun n x => f n x) n
  exact ⟨fun n => (g n).1, rfl, fun n => (g n).2, fun n => hf n (g n)⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨closed_lift, closed_extend⟩`.
-/
theorem tower_lemmas : (∀ (W A B : ℕ → Type 1) [∀ n, AddCommGroup (W n)] [∀ n, AddCommGroup (A n)] [∀ n, AddCommGroup (B n)] (c : ∀ n, W n →+ A n) (d : ∀ n, A n →+ B n) (r : ∀ n, W (n + 1) →+ W n) (s : ∀ n, A (n + 1) →+ A n) (t : ∀ n, B (n + 1) →+ B n), (∀ n x, d n (c n x) = 0) → (∀ n x, s n (c (n + 1) x) = c n (r n x)) → (∀ n x, t n (d (n + 1) x) = d n (s n x)) → (∀ n, Function.Surjective (r n)) → (∀ n a, d n a = 0 → ∃ a' w, d (n + 1) a' = 0 ∧ a = s n a' + c n w) → ∀ b : ∀ n, B n, (∀ n, t n (b (n + 1)) = b n) → (∀ n, ∃ a, d n a = b n) → ∃ a : ∀ n, A n, (∀ n, s n (a (n + 1)) = a n) ∧ ∀ n, d n (a n) = b n) ∧ ∀ (A B : ℕ → Type 1) [∀ n, AddCommGroup (A n)] [∀ n, AddCommGroup (B n)] (Z : ∀ n, AddSubgroup (B n)) (d : ∀ n, A n →+ B n) (s : ∀ n, A (n + 1) →+ A n) (t : ∀ n, B (n + 1) →+ B n), (∀ n x, d n x ∈ Z n) → (∀ n x, t n (d (n + 1) x) = d n (s n x)) → (∀ n, Function.Surjective (s n)) → (∀ n, ∀ x ∈ Z (n + 1), t n x ∈ Z n) → (∀ n, ∀ b ∈ Z n, ∃ b' ∈ Z (n + 1), ∃ a, b = t n b' + d n a) → ∀ b₀ ∈ Z 0, ∃ b : ∀ n, B n, b 0 = b₀ ∧ (∀ n, b n ∈ Z n) ∧ ∀ n, t n (b (n + 1)) = b n :=
  ⟨closed_lift, closed_extend⟩

end GlobalTheory.TowerLift
