import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTrSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointOfLatticeTauLatticeMembership
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.RelTors

/- English proof (translation)
Rewrite using `[h.2, PeriodPair.mem_lattice]`. Simplify using `only [tauPair, mul_one]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, v, e⟩`. Conclude with `⟨u, v, (mul_left_cancel₀ h.1 e).symm⟩`.

Introduce and unpack `⟨u, v, e⟩`. Conclude with `⟨u, v, by rw [← e]⟩`.
-/
theorem mul_mem_iff {L : PeriodPair} {c : ℂ} {τ : ℍ} (h : IsTauOf L c τ) (z : ℂ) :
    c * z ∈ L.lattice ↔ z ∈ (tauPair τ).lattice := by
  rw [h.2, PeriodPair.mem_lattice]
  simp only [tauPair, mul_one]
  constructor
  · rintro ⟨u, v, e⟩
    exact ⟨u, v, (mul_left_cancel₀ h.1 e).symm⟩
  · rintro ⟨u, v, e⟩
    exact ⟨u, v, by rw [← e]⟩

/- English proof (translation)
Introduce `K _ _ ι Λ₀ Λ₁ T c₀ c₁ τ₀ τ₁ hT h0 h1 N _ R hR`. Take `⟨-, a2, a3, a4, -⟩` from `GlobalTheory.WpFam.TorsMem.main N τ₀`. Take `⟨-, b2, b3, b4, b5⟩` from `GlobalTheory.WpFam.TorsMem.main N τ₁`. Establish `H0` using `mul_mem_iff h0`. Establish `H1` using `mul_mem_iff h1`.

Establish `hN : (N : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr (NeZero.ne N)`. Establish `T00 : T 0 0` using `hT.triv 0 0 (by simp) (by simp)`. Establish `Tneg : ∀ a b, T a b → T (-a) (-b)` using `fun a b h => by`. Simplify using `using hT.sub 0 0 a b T00 h`. Establish `Tadd : ∀ a b c d, T a b → T c d → T (a + c) (b + d)` using `fun a b c d h h' => by`.

Simplify using `using hT.sub _ _ _ _ h (Tneg _ _ h')`. Establish `Tnat : ∀ (n : ℕ) a b, T a b → T (n * a) (n * b)`. Introduce `n a b h`. Proceed by induction on `n with`. Consider the case `zero => simpa using T00`.

Consider the case `succ n ih => simpa [add_mul] using Tadd _ _ _ _ ih h`. Establish `adj : ∀ k k' m m', T k k' → ι k - ι m ∈ Λ₀.lattice → ι k' - ι m' ∈ Λ₁.lattice → T m m'`. Introduce `k k' m m' h hm hm'`. Use `hT.sub _ _ _ _ h (hT.triv (k - m) (k' - m') (by rwa [map_sub]) (by rwa [map_sub]))` as an intermediate fact. Simplify using `using this`.

Establish `real0 : ∀ (w : ℂ) (k : K), w - ι k ∈ Λ₀.lattice → ∃ m, ι m = w`. Introduce `w k h`. Take `⟨l, hl⟩` from `hT.rat₀ _ h`. Conclude with `⟨k + l, by rw [map_add, hl]; ring⟩`. Establish `real1 : ∀ (w : ℂ) (k : K), w - ι k ∈ Λ₁.lattice → ∃ m, ι m = w`.

Introduce `w k h`. Take `⟨l, hl⟩` from `hT.rat₁ _ h`. Conclude with `⟨k + l, by rw [map_add, hl]; ring⟩`. Use `⟨fun x => ?_, fun x y x' y' hxy hxy' => ?_, fun x y hxy => ?_⟩` and prove the remaining obligations. Take `⟨l, hl⟩` from `hT.rat₀ ((N : ℂ) * (c₀ * tors N τ₀ x)) (by rw [show (N : ℂ) * (c₀ * tors N τ₀ x) = c₀ * (N * tors N τ₀ x) by ring, H0]; exact a4 x)`.

Use `set k : K := l / N with hkdef`. Establish `hk : ι k = c₀ * tors N τ₀ x`. Rewrite using `[hkdef, map_div₀, hl, map_natCast]`. Clear the denominators using the available nonvanishing facts. Take `⟨k'', hk''⟩` from `hT.left k`.

Establish `m1 : ι ((N : K) * k'') ∈ Λ₁.lattice`. Use `(hT.mem_iff _ _ (Tnat N _ _ hk'')).1 ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_natCast, hk, show (N : ℂ) * (c₀ * tors N τ₀ x) = c₀ * (N * tors N τ₀ x) by ring, H0]`. Conclude with `a4 x`. Establish `hc1` using `h1.1`.

Establish `hz : (N : ℂ) * (ι k'' / c₁) ∈ (tauPair τ₁).lattice`. Rewrite using `[← H1]`. Use `m1 using 1` and compare the differences between its conclusion and the goal. Rewrite using `[map_mul, map_natCast]`. Clear the denominators using the available nonvanishing facts.

Take `⟨y, hy⟩` from `b5 _ hz`. Establish `hy' : ι k'' - c₁ * tors N τ₁ y ∈ Λ₁.lattice`. Use `(H1 _).2 hy` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Clear the denominators using the available nonvanishing facts.

Take `⟨k', hk'⟩` from `real1 (c₁ * tors N τ₁ y) k'' (by rw [← neg_sub]; exact neg_mem hy')`. Conclude with `⟨y, (hR x y).2 ⟨k, k', hk, hk', adj k k'' k k' hk'' (by simp) (by rw [hk']; exact hy')⟩⟩`. Take `⟨k₁, k₁', e₁, e₁', t₁⟩` from `(hR _ _).1 hxy`. Take `⟨k₂, k₂', e₂, e₂', t₂⟩` from `(hR _ _).1 hxy'`. Establish `t₁₂` using `hT.sub _ _ _ _ t₁ t₂`.

Establish `d0 : c₀ * tors N τ₀ (x - x') - ι (k₁ - k₂) ∈ Λ₀.lattice`. Rewrite using `[map_sub, e₁, e₂, show c₀ * tors N τ₀ (x - x') - (c₀ * tors N τ₀ x - c₀ * tors N τ₀ x') = c₀ * -(tors N τ₀ (x - x' + x') - (tors N τ₀ (x - x') + tors N τ₀ x')) by`. Rewrite using `[sub_add_cancel]`. Use the proof step `ring, H0]`. Conclude with `neg_mem (a2 _ _)`.

Establish `d1 : c₁ * tors N τ₁ (y - y') - ι (k₁' - k₂') ∈ Λ₁.lattice`. Rewrite using `[map_sub, e₁', e₂', show c₁ * tors N τ₁ (y - y') - (c₁ * tors N τ₁ y - c₁ * tors N τ₁ y') = c₁ * -(tors N τ₁ (y - y' + y') - (tors N τ₁ (y - y') + tors N τ₁ y')) by`. Rewrite using `[sub_add_cancel]`. Use the proof step `ring, H1]`. Conclude with `neg_mem (b2 _ _)`.

Take `⟨m, hm⟩` from `real0 _ _ d0`. Take `⟨m', hm'⟩` from `real1 _ _ d1`. Conclude with `(hR _ _).2 ⟨m, m', hm, hm', adj _ _ m m' t₁₂ (by rw [hm, ← neg_sub]; exact neg_mem d0) (by rw [hm', ← neg_sub]; exact neg_mem d1)⟩`. Take `⟨k, k', e, e', t⟩` from `(hR _ _).1 hxy`. Rewrite using `[← a3 x, ← b3 y, ← H0, ← H1, ← e, ← e']`.

Conclude with `hT.mem_iff k k' t`.
-/
theorem main : ∀ (K : Type) [Field K] [CharZero K] (ι : K →+* ℂ) (Λ₀ Λ₁ : PeriodPair) (T : K → K → Prop) (c₀ c₁ : ℂ) (τ₀ τ₁ : ℍ), IsTr ι Λ₀ Λ₁ T → IsTauOf Λ₀ c₀ τ₀ → IsTauOf Λ₁ c₁ τ₁ → ∀ (N : ℕ) [NeZero N] (R : (Fin 2 → ZMod N) → (Fin 2 → ZMod N) → Prop), (∀ x y, R x y ↔ ∃ k k' : K, ι k = c₀ * tors N τ₀ x ∧ ι k' = c₁ * tors N τ₁ y ∧ T k k') → (∀ x, ∃ y, R x y) ∧ (∀ x y x' y', R x y → R x' y' → R (x - x') (y - y')) ∧ (∀ x y, R x y → (x = 0 ↔ y = 0)) := by
  intro K _ _ ι Λ₀ Λ₁ T c₀ c₁ τ₀ τ₁ hT h0 h1 N _ R hR
  obtain ⟨-, a2, a3, a4, -⟩ := GlobalTheory.WpFam.TorsMem.main N τ₀
  obtain ⟨-, b2, b3, b4, b5⟩ := GlobalTheory.WpFam.TorsMem.main N τ₁
  have H0 := mul_mem_iff h0
  have H1 := mul_mem_iff h1
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have T00 : T 0 0 := hT.triv 0 0 (by simp) (by simp)
  have Tneg : ∀ a b, T a b → T (-a) (-b) := fun a b h => by
    simpa using hT.sub 0 0 a b T00 h
  have Tadd : ∀ a b c d, T a b → T c d → T (a + c) (b + d) := fun a b c d h h' => by
    simpa using hT.sub _ _ _ _ h (Tneg _ _ h')
  have Tnat : ∀ (n : ℕ) a b, T a b → T (n * a) (n * b) := by
    intro n a b h
    induction n with
    | zero => simpa using T00
    | succ n ih => simpa [add_mul] using Tadd _ _ _ _ ih h
  have adj : ∀ k k' m m', T k k' → ι k - ι m ∈ Λ₀.lattice → ι k' - ι m' ∈ Λ₁.lattice → T m m' := by
    intro k k' m m' h hm hm'
    have := hT.sub _ _ _ _ h (hT.triv (k - m) (k' - m') (by rwa [map_sub]) (by rwa [map_sub]))
    simpa using this
  have real0 : ∀ (w : ℂ) (k : K), w - ι k ∈ Λ₀.lattice → ∃ m, ι m = w := by
    intro w k h
    obtain ⟨l, hl⟩ := hT.rat₀ _ h
    exact ⟨k + l, by rw [map_add, hl]; ring⟩
  have real1 : ∀ (w : ℂ) (k : K), w - ι k ∈ Λ₁.lattice → ∃ m, ι m = w := by
    intro w k h
    obtain ⟨l, hl⟩ := hT.rat₁ _ h
    exact ⟨k + l, by rw [map_add, hl]; ring⟩
  refine ⟨fun x => ?_, fun x y x' y' hxy hxy' => ?_, fun x y hxy => ?_⟩
  ·
    obtain ⟨l, hl⟩ := hT.rat₀ ((N : ℂ) * (c₀ * tors N τ₀ x))
      (by rw [show (N : ℂ) * (c₀ * tors N τ₀ x) = c₀ * (N * tors N τ₀ x) by ring, H0]; exact a4 x)
    set k : K := l / N with hkdef
    have hk : ι k = c₀ * tors N τ₀ x := by
      rw [hkdef, map_div₀, hl, map_natCast]; field_simp
    obtain ⟨k'', hk''⟩ := hT.left k
    have m1 : ι ((N : K) * k'') ∈ Λ₁.lattice := by
      refine (hT.mem_iff _ _ (Tnat N _ _ hk'')).1 ?_
      rw [map_mul, map_natCast, hk, show (N : ℂ) * (c₀ * tors N τ₀ x) = c₀ * (N * tors N τ₀ x) by ring, H0]
      exact a4 x
    have hc1 := h1.1
    have hz : (N : ℂ) * (ι k'' / c₁) ∈ (tauPair τ₁).lattice := by
      rw [← H1]
      convert m1 using 1
      rw [map_mul, map_natCast]; field_simp
    obtain ⟨y, hy⟩ := b5 _ hz
    have hy' : ι k'' - c₁ * tors N τ₁ y ∈ Λ₁.lattice := by
      have := (H1 _).2 hy
      convert this using 1
      field_simp
    obtain ⟨k', hk'⟩ := real1 (c₁ * tors N τ₁ y) k'' (by rw [← neg_sub]; exact neg_mem hy')
    exact ⟨y, (hR x y).2 ⟨k, k', hk, hk', adj k k'' k k' hk'' (by simp) (by rw [hk']; exact hy')⟩⟩
  ·
    obtain ⟨k₁, k₁', e₁, e₁', t₁⟩ := (hR _ _).1 hxy
    obtain ⟨k₂, k₂', e₂, e₂', t₂⟩ := (hR _ _).1 hxy'
    have t₁₂ := hT.sub _ _ _ _ t₁ t₂
    have d0 : c₀ * tors N τ₀ (x - x') - ι (k₁ - k₂) ∈ Λ₀.lattice := by
      rw [map_sub, e₁, e₂, show c₀ * tors N τ₀ (x - x') - (c₀ * tors N τ₀ x - c₀ * tors N τ₀ x')
        = c₀ * -(tors N τ₀ (x - x' + x') - (tors N τ₀ (x - x') + tors N τ₀ x')) by
          rw [sub_add_cancel]; ring, H0]
      exact neg_mem (a2 _ _)
    have d1 : c₁ * tors N τ₁ (y - y') - ι (k₁' - k₂') ∈ Λ₁.lattice := by
      rw [map_sub, e₁', e₂', show c₁ * tors N τ₁ (y - y') - (c₁ * tors N τ₁ y - c₁ * tors N τ₁ y')
        = c₁ * -(tors N τ₁ (y - y' + y') - (tors N τ₁ (y - y') + tors N τ₁ y')) by
          rw [sub_add_cancel]; ring, H1]
      exact neg_mem (b2 _ _)
    obtain ⟨m, hm⟩ := real0 _ _ d0
    obtain ⟨m', hm'⟩ := real1 _ _ d1
    exact (hR _ _).2 ⟨m, m', hm, hm', adj _ _ m m' t₁₂
      (by rw [hm, ← neg_sub]; exact neg_mem d0) (by rw [hm', ← neg_sub]; exact neg_mem d1)⟩
  ·
    obtain ⟨k, k', e, e', t⟩ := (hR _ _).1 hxy
    rw [← a3 x, ← b3 y, ← H0, ← H1, ← e, ← e']
    exact hT.mem_iff k k' t

end GlobalTheory.RelTors
