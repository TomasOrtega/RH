import Mathlib

universe u_1

namespace GlobalTheory.SaturatedNotDvd

/- English proof (translation)
Set `K : Ideal A` to `{ carrier := {u | ∃ k : ℕ, x ^ k * u ∈ I} add_mem' := by`. Introduce and unpack `u v ⟨k, hk⟩ ⟨l, hl⟩`. Use `⟨k + l, ?_⟩` and prove the remaining obligations. Establish `e : x ^ (k + l) * (u + v) = x ^ l * (x ^ k * u) + x ^ k * (x ^ l * v)` using `by ring`. Rewrite using `[e]`.

Conclude with `I.add_mem (I.mul_mem_left _ hk) (I.mul_mem_left _ hl)`. Use the proof step `zero_mem' := ⟨0, by simp⟩`. Use the proof step `smul_mem' := by`. Introduce and unpack `c u ⟨k, hk⟩`. Use `⟨k, ?_⟩` and prove the remaining obligations.

Establish `e : x ^ k * (c • u) = c * (x ^ k * u)` using `by rw [smul_eq_mul]; ring`. Rewrite using `[e]`. Conclude with `I.mul_mem_left _ hk }`. Use `⟨K, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `hK`.

Apply `hI` to reduce the goal to its premises. Rewrite `hK`, the goal using `[eq_bot_iff]`. Introduce `r hr`. Conclude with `hK (show ∃ k : ℕ, x ^ k * r ∈ I from ⟨0, by simpa using hr⟩)`. Introduce and unpack `u ⟨k, hk⟩`.

Conclude with `⟨k + 1, by rw [pow_succ, mul_assoc]; exact hk⟩`. Introduce and unpack `r ⟨k, hk⟩`. Take `⟨s, hs, hrs⟩` from `h _ hk`. Establish `hdvd : x ^ k ∣ b * s` using `⟨a * r, by rw [← hrs]; ring⟩`. Take `⟨s', hs'⟩` from `hx.pow_dvd_of_dvd_mul_left k hb hdvd`.

Use `⟨s', ⟨k, by rw [← hs']; exact hs⟩, ?_⟩` and prove the remaining obligations. Establish `hxk : x ^ k ≠ 0` using `pow_ne_zero _ hx.ne_zero`. Apply `mul_left_cancel₀ hxk` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_saturated {A : Type u_1} [CommRing A] [IsDomain A] {x a b : A} (hx : Prime x)
    (hb : ¬ x ∣ b) {I : Ideal A} (hI : I ≠ ⊥) (h : ∀ r ∈ I, ∃ s ∈ I, a * r = b * s) :
    ∃ K : Ideal A, K ≠ ⊥ ∧ (∀ u, x * u ∈ K → u ∈ K) ∧ ∀ r ∈ K, ∃ s ∈ K, a * r = b * s := by
  let K : Ideal A :=
    { carrier := {u | ∃ k : ℕ, x ^ k * u ∈ I}
      add_mem' := by
        rintro u v ⟨k, hk⟩ ⟨l, hl⟩
        refine ⟨k + l, ?_⟩
        have e : x ^ (k + l) * (u + v) = x ^ l * (x ^ k * u) + x ^ k * (x ^ l * v) := by ring
        rw [e]
        exact I.add_mem (I.mul_mem_left _ hk) (I.mul_mem_left _ hl)
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c u ⟨k, hk⟩
        refine ⟨k, ?_⟩
        have e : x ^ k * (c • u) = c * (x ^ k * u) := by rw [smul_eq_mul]; ring
        rw [e]
        exact I.mul_mem_left _ hk }
  refine ⟨K, ?_, ?_, ?_⟩
  · intro hK
    apply hI
    rw [eq_bot_iff] at hK ⊢
    intro r hr
    exact hK (show ∃ k : ℕ, x ^ k * r ∈ I from ⟨0, by simpa using hr⟩)
  · rintro u ⟨k, hk⟩
    exact ⟨k + 1, by rw [pow_succ, mul_assoc]; exact hk⟩
  · rintro r ⟨k, hk⟩
    obtain ⟨s, hs, hrs⟩ := h _ hk
    have hdvd : x ^ k ∣ b * s := ⟨a * r, by rw [← hrs]; ring⟩
    obtain ⟨s', hs'⟩ := hx.pow_dvd_of_dvd_mul_left k hb hdvd
    refine ⟨s', ⟨k, by rw [← hs']; exact hs⟩, ?_⟩
    have hxk : x ^ k ≠ 0 := pow_ne_zero _ hx.ne_zero
    apply mul_left_cancel₀ hxk
    calc x ^ k * (a * r) = a * (x ^ k * r) := by ring
      _ = b * s := hrs
      _ = b * (x ^ k * s') := by rw [hs']
      _ = x ^ k * (b * s') := by ring

/- English proof (translation)
Assume the negation of the conclusion as `hall`. Use `push_neg at hall`. Apply `hK` to reduce the goal to its premises. Apply `Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (Ideal.span {x}) K (IsNoetherian.noetherian K)` to reduce the goal to its premises. Introduce `u hu`.

Take `⟨u', rfl⟩` from `hall u hu`. Conclude with `Submodule.smul_mem_smul (Ideal.mem_span_singleton_self x) (hs u' hu)`. Rewrite using `[IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]`. Conclude with `(Ideal.span_singleton_le_iff_mem _).2 ((IsLocalRing.mem_maximalIdeal x).2 hx)`.
-/
theorem exists_not_dvd {A : Type u_1} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] {x : A}
    (hx : ¬ IsUnit x) {K : Ideal A} (hK : K ≠ ⊥) (hs : ∀ u, x * u ∈ K → u ∈ K) :
    ∃ u ∈ K, ¬ x ∣ u := by
  by_contra hall
  push_neg at hall
  apply hK
  apply Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (Ideal.span {x}) K (IsNoetherian.noetherian K)
  · intro u hu
    obtain ⟨u', rfl⟩ := hall u hu
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self x) (hs u' hu)
  · rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact (Ideal.span_singleton_le_iff_mem _).2 ((IsLocalRing.mem_maximalIdeal x).2 hx)

/- English proof (translation)
Introduce `d1 A _ _ _ _ x hx hd a b hb I hI h`. Establish `hd' : ∀ (a b : A ⧸ Ideal.span {x}) (I : Ideal (A ⧸ Ideal.span {x})), b ≠ 0 → I ≠ ⊥ → (∀ r ∈ I, ∃ s ∈ I, a * r = b * s) → b ∣ a` using `hd`. Take `⟨K, hK, hsat, hKa⟩` from `exists_saturated hx hb hI h`. Take `⟨u₀, hu₀, hxu⟩` from `exists_not_dvd hx.not_unit hK hsat`. Establish `hz : ∀ y : A, Ideal.Quotient.mk (Ideal.span {x}) y = 0 ↔ x ∣ y` using `fun y => by`.

Rewrite using `[Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]`. Establish `step : ∀ a : A, (∀ r ∈ K, ∃ s ∈ K, a * r = b * s) → ∃ c d : A, a = b * c + x * d ∧ ∀ r ∈ K, ∃ s ∈ K, d * r = b * s`. Introduce `a ha`. Establish `hdiv : Ideal.Quotient.mk (Ideal.span {x}) b ∣ Ideal.Quotient.mk (Ideal.span {x}) a`. Use `hd' _ _ (K.map (Ideal.Quotient.mk (Ideal.span {x}))) (fun h0 => hb ((hz b).1 h0)) ?_ ?_` and prove the remaining obligations.

Introduce `hbot`. Establish `hm` using `Ideal.mem_map_of_mem (Ideal.Quotient.mk (Ideal.span {x})) hu₀`. Rewrite `hm` using `[hbot, Ideal.mem_bot]`. Conclude with `hxu ((hz _).1 hm)`. Introduce `r hr`.

Take `⟨r', hr', rfl⟩` from `(Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hr`. Take `⟨s, hs, hrs⟩` from `ha r' hr'`. Conclude with `⟨_, Ideal.mem_map_of_mem _ hs, by rw [← map_mul, ← map_mul, hrs]⟩`. Take `⟨c', hc'⟩` from `hdiv`. Take `⟨c, rfl⟩` from `Ideal.Quotient.mk_surjective c'`.

Establish `hxd : x ∣ a - b * c` using `(hz _).1 (by rw [map_sub, map_mul, hc', sub_self])`. Take `⟨d, hdd⟩` from `hxd`. Use `⟨c, d, by linear_combination hdd, ?_⟩` and prove the remaining obligations. Introduce `r hr`. Take `⟨s, hs, hrs⟩` from `ha r hr`.

Establish `h1 : b * (s - c * r) = x * (d * r)` using `by linear_combination r * hdd - hrs`. Establish `h2 : x ∣ s - c * r` using `(hx.dvd_or_dvd ⟨_, h1⟩).resolve_left hb`. Take `⟨w, hw⟩` from `h2`. Establish `hwK : w ∈ K` using `hsat w (hw ▸ K.sub_mem hs (K.mul_mem_left c hr))`. Use `⟨w, hwK, ?_⟩` and prove the remaining obligations.

Apply `mul_left_cancel₀ hx.ne_zero` to reduce the goal to its premises. Rewrite using `[← h1, hw]`. Expand and normalize the polynomial expressions, which then agree. Establish `iter : ∀ n : ℕ, ∀ a : A, (∀ r ∈ K, ∃ s ∈ K, a * r = b * s) → ∃ c y : A, a = b * c + x ^ n * y`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero => intro a _; exact ⟨0, a, by simp⟩`. Consider the case `succ n ih`. Introduce `a ha`. Take `⟨c, d, rfl, hd2⟩` from `step a ha`.

Take `⟨c', y, rfl⟩` from `ih d hd2`. Conclude with `⟨c + x * c', y, by ring⟩`. Establish `hne : Ideal.span {x} ≠ ⊤` using `fun h => hx.not_unit (Ideal.span_singleton_eq_top.1 h)`. Establish `hk` using `Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := A ⧸ Ideal.span {b}) (Ideal.span {x}) hne`. Establish `hmem : Ideal.Quotient.mk (Ideal.span {b}) a ∈ (⨅ i : ℕ, Ideal.span {x} ^ i • ⊤ : Submodule A (A ⧸ Ideal.span {b}))`.

Rewrite using `[Submodule.mem_iInf]`. Introduce `n`. Take `⟨c, y, hcy⟩` from `iter n a hKa`. Establish `: Ideal.Quotient.mk (Ideal.span {b}) a = x ^ n • Ideal.Quotient.mk (Ideal.span {b}) y`. Express the relevant statement in the definitionally equal form `_ = Ideal.Quotient.mk (Ideal.span {b}) (x ^ n * y)`.

Rewrite using `[Ideal.Quotient.eq, Ideal.mem_span_singleton]`. Conclude with `⟨c, by rw [hcy]; ring⟩`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem_smul (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self x) n) Submodule.mem_top`. Rewrite `hmem` using `[hk, Submodule.mem_bot, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]`.

Conclude with `hmem`.
-/
theorem main : (let d1 : (A : Type u_1) → [CommRing A] → Prop := @(fun (A : Type u_1) [CommRing A] ↦ ∀ (a b : A) (I : Ideal A), b ≠ (0 : A) → I ≠ ⊥ → (∀ r ∈ I, ∃ s ∈ I, a * r = b * s) → b ∣ a); ∀ {A : Type u_1} [inst : CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A] {x : A}, Prime x → d1 (A ⧸ Ideal.span {x}) → ∀ {a b : A}, ¬x ∣ b → ∀ {I : Ideal A}, I ≠ ⊥ → (∀ r ∈ I, ∃ s ∈ I, a * r = b * s) → b ∣ a) := by
  intro d1 A _ _ _ _ x hx hd a b hb I hI h
  have hd' : ∀ (a b : A ⧸ Ideal.span {x}) (I : Ideal (A ⧸ Ideal.span {x})), b ≠ 0 → I ≠ ⊥ →
      (∀ r ∈ I, ∃ s ∈ I, a * r = b * s) → b ∣ a := hd
  obtain ⟨K, hK, hsat, hKa⟩ := exists_saturated hx hb hI h
  obtain ⟨u₀, hu₀, hxu⟩ := exists_not_dvd hx.not_unit hK hsat
  have hz : ∀ y : A, Ideal.Quotient.mk (Ideal.span {x}) y = 0 ↔ x ∣ y := fun y => by
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  have step : ∀ a : A, (∀ r ∈ K, ∃ s ∈ K, a * r = b * s) →
      ∃ c d : A, a = b * c + x * d ∧ ∀ r ∈ K, ∃ s ∈ K, d * r = b * s := by
    intro a ha
    have hdiv : Ideal.Quotient.mk (Ideal.span {x}) b ∣ Ideal.Quotient.mk (Ideal.span {x}) a := by
      refine hd' _ _ (K.map (Ideal.Quotient.mk (Ideal.span {x}))) (fun h0 => hb ((hz b).1 h0)) ?_ ?_
      · intro hbot
        have hm := Ideal.mem_map_of_mem (Ideal.Quotient.mk (Ideal.span {x})) hu₀
        rw [hbot, Ideal.mem_bot] at hm
        exact hxu ((hz _).1 hm)
      · intro r hr
        obtain ⟨r', hr', rfl⟩ :=
          (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hr
        obtain ⟨s, hs, hrs⟩ := ha r' hr'
        exact ⟨_, Ideal.mem_map_of_mem _ hs, by rw [← map_mul, ← map_mul, hrs]⟩
    obtain ⟨c', hc'⟩ := hdiv
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c'
    have hxd : x ∣ a - b * c := (hz _).1 (by rw [map_sub, map_mul, hc', sub_self])
    obtain ⟨d, hdd⟩ := hxd
    refine ⟨c, d, by linear_combination hdd, ?_⟩
    intro r hr
    obtain ⟨s, hs, hrs⟩ := ha r hr
    have h1 : b * (s - c * r) = x * (d * r) := by linear_combination r * hdd - hrs
    have h2 : x ∣ s - c * r := (hx.dvd_or_dvd ⟨_, h1⟩).resolve_left hb
    obtain ⟨w, hw⟩ := h2
    have hwK : w ∈ K := hsat w (hw ▸ K.sub_mem hs (K.mul_mem_left c hr))
    refine ⟨w, hwK, ?_⟩
    apply mul_left_cancel₀ hx.ne_zero
    rw [← h1, hw]; ring
  have iter : ∀ n : ℕ, ∀ a : A, (∀ r ∈ K, ∃ s ∈ K, a * r = b * s) →
      ∃ c y : A, a = b * c + x ^ n * y := by
    intro n
    induction n with
    | zero => intro a _; exact ⟨0, a, by simp⟩
    | succ n ih =>
      intro a ha
      obtain ⟨c, d, rfl, hd2⟩ := step a ha
      obtain ⟨c', y, rfl⟩ := ih d hd2
      exact ⟨c + x * c', y, by ring⟩
  have hne : Ideal.span {x} ≠ ⊤ := fun h => hx.not_unit (Ideal.span_singleton_eq_top.1 h)
  have hk := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := A ⧸ Ideal.span {b})
    (Ideal.span {x}) hne
  have hmem : Ideal.Quotient.mk (Ideal.span {b}) a ∈
      (⨅ i : ℕ, Ideal.span {x} ^ i • ⊤ : Submodule A (A ⧸ Ideal.span {b})) := by
    rw [Submodule.mem_iInf]
    intro n
    obtain ⟨c, y, hcy⟩ := iter n a hKa
    have : Ideal.Quotient.mk (Ideal.span {b}) a
        = x ^ n • Ideal.Quotient.mk (Ideal.span {b}) y := by
      change _ = Ideal.Quotient.mk (Ideal.span {b}) (x ^ n * y)
      rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
      exact ⟨c, by rw [hcy]; ring⟩
    rw [this]
    exact Submodule.smul_mem_smul (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self x) n)
      Submodule.mem_top
  rw [hk, Submodule.mem_bot, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hmem
  exact hmem

end GlobalTheory.SaturatedNotDvd
