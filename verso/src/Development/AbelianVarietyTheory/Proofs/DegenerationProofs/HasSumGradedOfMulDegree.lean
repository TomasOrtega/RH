import Mathlib

open scoped BigOperators

namespace GlobalTheory

/- English proof (translation)
Establish `: NonarchimedeanRing C` using `⟨fun U hU => NonarchimedeanAddGroup.is_nonarchimedean U hU⟩`. Establish `hp : HasSum (fun i : X × X => a i.1 * a' i.2) (S * S')` using `h.mul_of_nonarchimedean h'`. Set `e : X × X ≃ X × X` to `{ toFun := fun p => (p.2, p.1 - p.2) invFun := fun q => (q.1 + q.2, q.1) left_inv := by rintro ⟨x, y⟩; simp right_inv := by rintro ⟨x, y⟩; simp }`. Establish `hq : HasSum (fun p : X × X => a p.2 * a' (p.1 - p.2)) (S * S')` using `e.hasSum_iff.2 hp`. Conclude with `hq.prod_fiberwise hc`.
-/
theorem hasSum_conv_of_ultrametric {C : Type} [NormedField C] [IsUltrametricDist C]
    {X : Type} [AddCommGroup X] {a a' a'' : X → C} {S S' : C}
    (h : HasSum a S) (h' : HasSum a' S')
    (hc : ∀ α, HasSum (fun χ => a χ * a' (α - χ)) (a'' α)) : HasSum a'' (S * S') := by
  have : NonarchimedeanRing C := ⟨fun U hU => NonarchimedeanAddGroup.is_nonarchimedean U hU⟩
  have hp : HasSum (fun i : X × X => a i.1 * a' i.2) (S * S') := h.mul_of_nonarchimedean h'
  let e : X × X ≃ X × X :=
    { toFun := fun p => (p.2, p.1 - p.2)
      invFun := fun q => (q.1 + q.2, q.1)
      left_inv := by rintro ⟨x, y⟩; simp
      right_inv := by rintro ⟨x, y⟩; simp }
  have hq : HasSum (fun p : X × X => a p.2 * a' (p.1 - p.2)) (S * S') := e.hasSum_iff.2 hp
  exact hq.prod_fiberwise hc

/- English proof (translation)
Introduce `C _ _ _ X _ Rel n k hn hk hmul hkap`. Take `⟨κ, hκ, hkap⟩` from `hkap`. Take `⟨m, rfl⟩ : ∃ m, n = m + 1` from `⟨n - 1, by omega⟩`. Establish `key : ∀ a c S, Rel k a c → HasSum a S → ∀ b d T, Rel k b d → HasSum b T → ∀ j : ℕ, ∃ e, Rel ((j + 1) * k) e (c ^ j * d) ∧ HasSum e (S ^ j * T)`. Introduce `a c S hac hS b d T hbd hT j`.

Proceed by induction on `j with`. Consider the case `zero => exact ⟨b, by simpa using hbd, by simpa using hT⟩`. Consider the case `succ j ih`. Take `⟨e, he, heT⟩` from `ih`. Establish `hjk : 1 ≤ (j + 1) * k` using `le_trans hk (Nat.le_mul_of_pos_left k (Nat.succ_pos j))`.

Take `⟨e', he', hconv⟩` from `hmul ((j + 1) * k) k e a (c ^ j * d) c hjk hk he hac`. Use `⟨e', ?_, ?_⟩` and prove the remaining obligations. Establish `h2 : (j + 1) * k + k = (j + 1 + 1) * k` using `by ring`. Establish `h3 : c ^ j * d * c = c ^ (j + 1) * d` using `by ring`. Rewrite `he'` using `[h2, h3]`.

Conclude with `he'`. Establish `h4` using `hasSum_conv_of_ultrametric heT hS hconv`. Establish `h5 : S ^ j * T * S = S ^ (j + 1) * T` using `by ring`. Rewrite `h4` using `[h5]`. Conclude with `h4`.

Establish `eqn : ∀ a c S, Rel k a c → HasSum a S → ∀ b d T, Rel k b d → HasSum b T → S ^ m * T = κ * (c ^ m * d)`. Introduce `a c S hac hS b d T hbd hT`. Take `⟨e, he, heT⟩` from `key a c S hac hS b d T hbd hT m`. Conclude with `heT.unique (hkap e _ he)`. Distinguish the cases in `hex : ∃ a c, Rel k a c ∧ Summable a ∧ c ≠ 0`.

Take `⟨a, c, hac, hsa, hc0⟩` from `hex set S := ∑' x, a x with hSdef`. Establish `h0` using `eqn a c S hac hsa.hasSum a c S hac hsa.hasSum`. Establish `hSn : S ^ (m + 1) = κ * c ^ (m + 1)` using `by linear_combination h0`. Establish `hS0 : S ≠ 0`. Introduce `hz`.

Rewrite `hSn` using `[hz, zero_pow (Nat.succ_ne_zero m)]`. Conclude with `(mul_ne_zero hκ (pow_ne_zero _ hc0)) hSn.symm`. Use `⟨S / c, div_ne_zero hS0 hc0, ?_⟩` and prove the remaining obligations. Introduce `b d hbd hsb`. Establish `h1` using `eqn a c S hac hsa.hasSum b d (∑' x, b x) hbd hsb.hasSum`.

Establish `hT : ∑' x, b x = S / c * d`. Rewrite using `[div_mul_eq_mul_div, eq_div_iff hc0]`. Apply `mul_left_cancel₀ (pow_ne_zero m hS0)` to reduce the goal to its premises. Take the linear combination `c * h1 - d * hSn`. Rewrite using `[← hT]`.

Conclude with `hsb.hasSum`. Use `push Not at hex`. Use `⟨1, one_ne_zero, ?_⟩` and prove the remaining obligations. Introduce `b d hbd hsb`. Establish `hd` using `hex b d hbd hsb`.

Substitute `hd` using the available equality. Establish `h1` using `eqn b 0 _ hbd hsb.hasSum b 0 _ hbd hsb.hasSum`. Establish `hpow : (∑' x, b x) ^ (m + 1) = 0`. Rewrite using `[pow_succ, h1]`. Simplify using the standard rewrite rules.

Establish `hT : ∑' x, b x = 0` using `pow_eq_zero_iff (Nat.succ_ne_zero m) |>.1 hpow`. Rewrite using `[one_mul, ← hT]`. Conclude with `hsb.hasSum`.
-/
theorem hasSum_graded_of_mul_degree :
    ∀ (C : Type) [NormedField C] [IsUltrametricDist C] [CompleteSpace C] (X : Type) [AddCommGroup X] (Rel : ℕ → (X → C) → C → Prop) (n k : ℕ), 1 ≤ n → 1 ≤ k → (∀ (l l' : ℕ) (a a' : X → C) (c c' : C), 1 ≤ l → 1 ≤ l' → Rel l a c → Rel l' a' c' → ∃ a'', Rel (l + l') a'' (c * c') ∧ ∀ α, HasSum (fun χ => a χ * a' (α - χ)) (a'' α)) → (∃ κ : C, κ ≠ 0 ∧ ∀ a c, Rel (n * k) a c → HasSum a (κ * c)) → ∃ u : C, u ≠ 0 ∧ ∀ a c, Rel k a c → Summable a → HasSum a (u * c) := by
  intro C _ _ _ X _ Rel n k hn hk hmul hkap
  obtain ⟨κ, hκ, hkap⟩ := hkap
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩

  have key : ∀ a c S, Rel k a c → HasSum a S → ∀ b d T, Rel k b d → HasSum b T →
      ∀ j : ℕ, ∃ e, Rel ((j + 1) * k) e (c ^ j * d) ∧ HasSum e (S ^ j * T) := by
    intro a c S hac hS b d T hbd hT j
    induction j with
    | zero => exact ⟨b, by simpa using hbd, by simpa using hT⟩
    | succ j ih =>
      obtain ⟨e, he, heT⟩ := ih
      have hjk : 1 ≤ (j + 1) * k := le_trans hk (Nat.le_mul_of_pos_left k (Nat.succ_pos j))
      obtain ⟨e', he', hconv⟩ := hmul ((j + 1) * k) k e a (c ^ j * d) c hjk hk he hac
      refine ⟨e', ?_, ?_⟩
      · have h2 : (j + 1) * k + k = (j + 1 + 1) * k := by ring
        have h3 : c ^ j * d * c = c ^ (j + 1) * d := by ring
        rw [h2, h3] at he'
        exact he'
      · have h4 := hasSum_conv_of_ultrametric heT hS hconv
        have h5 : S ^ j * T * S = S ^ (j + 1) * T := by ring
        rw [h5] at h4
        exact h4
  have eqn : ∀ a c S, Rel k a c → HasSum a S → ∀ b d T, Rel k b d → HasSum b T →
      S ^ m * T = κ * (c ^ m * d) := by
    intro a c S hac hS b d T hbd hT
    obtain ⟨e, he, heT⟩ := key a c S hac hS b d T hbd hT m
    exact heT.unique (hkap e _ he)
  by_cases hex : ∃ a c, Rel k a c ∧ Summable a ∧ c ≠ 0
  · obtain ⟨a, c, hac, hsa, hc0⟩ := hex
    set S := ∑' x, a x with hSdef
    have h0 := eqn a c S hac hsa.hasSum a c S hac hsa.hasSum
    have hSn : S ^ (m + 1) = κ * c ^ (m + 1) := by linear_combination h0
    have hS0 : S ≠ 0 := by
      intro hz
      rw [hz, zero_pow (Nat.succ_ne_zero m)] at hSn
      exact (mul_ne_zero hκ (pow_ne_zero _ hc0)) hSn.symm
    refine ⟨S / c, div_ne_zero hS0 hc0, ?_⟩
    intro b d hbd hsb
    have h1 := eqn a c S hac hsa.hasSum b d (∑' x, b x) hbd hsb.hasSum
    have hT : ∑' x, b x = S / c * d := by
      rw [div_mul_eq_mul_div, eq_div_iff hc0]
      apply mul_left_cancel₀ (pow_ne_zero m hS0)
      linear_combination c * h1 - d * hSn
    rw [← hT]
    exact hsb.hasSum
  · push Not at hex
    refine ⟨1, one_ne_zero, ?_⟩
    intro b d hbd hsb
    have hd := hex b d hbd hsb
    subst hd
    have h1 := eqn b 0 _ hbd hsb.hasSum b 0 _ hbd hsb.hasSum
    have hpow : (∑' x, b x) ^ (m + 1) = 0 := by
      rw [pow_succ, h1]
      simp
    have hT : ∑' x, b x = 0 := pow_eq_zero_iff (Nat.succ_ne_zero m) |>.1 hpow
    rw [one_mul, ← hT]
    exact hsb.hasSum

end GlobalTheory
