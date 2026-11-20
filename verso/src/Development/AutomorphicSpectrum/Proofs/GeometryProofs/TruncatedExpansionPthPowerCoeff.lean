import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TranslDiffEq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.CoefAlg

/- English proof (translation)
Establish `hpp : p.Prime` using `Fact.out`. Establish `hp2 : 2 ≤ p` using `hpp.two_le`. Break down `subsingleton_or_nontrivial B with hB | hB` into its components or cases. Conclude with `Subsingleton.elim _ _`. Use `haveI : CharP B p := by`.

Establish `h` using `CharP.ringChar_of_prime_eq_zero hpp hp0`. Rewrite using `[← h]`. Conclude with `ringChar.charP B`. Rewrite using `[sum_pow_char p]`. Establish `hterm : ∀ i : Fin (p + 1), (a i * δ ^ (i : ℕ)) ^ p = (if i = 0 then 1 else 0) + (if i = ⟨1, h1⟩ then a ⟨1, h1⟩ ^ p * δ ^ p else 0)`.

Introduce `i`. Distinguish the cases in `hi0 : i = 0`. Substitute `hi0` using the available equality. Establish `: (0 : Fin (p + 1)) ≠ ⟨1, h1⟩`. Introduce `h`.

Use `congrArg Fin.val h` as an intermediate fact. Simplify using `at this`. Simplify using `[ha0, this]`. Distinguish the cases in `hi1 : i = ⟨1, h1⟩`. Substitute `hi1` using the available equality.

Establish `: (⟨1, h1⟩ : Fin (p + 1)) ≠ 0`. Introduce `h`. Use `congrArg Fin.val h` as an intermediate fact. Simplify using `at this`. Simplify using `[this, mul_pow]`.

Establish `hv0 : (i : ℕ) ≠ 0` using `fun h => hi0 (Fin.ext h)`. Establish `hv1 : (i : ℕ) ≠ 1` using `fun h => hi1 (Fin.ext h)`. Establish `hv : 2 ≤ (i : ℕ)` using `by omega`. Establish `hle : p + 1 ≤ (i : ℕ) * p` using `by nlinarith`. Establish `hz : δ ^ ((i : ℕ) * p) = 0`.

Take `⟨k, hk⟩` from `Nat.exists_eq_add_of_le hle`. Rewrite using `[hk, pow_add, hδ, zero_mul]`. Simplify using `[hi0, hi1, mul_pow, ← pow_mul, hz]`. Simplify using `only [hterm, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]`.
-/
theorem pow_frobenius_truncated {B : Type} [CommRing B] (δ : B) (p : ℕ) [Fact p.Prime]
    (hp0 : (p : B) = 0) (hδ : δ ^ (p + 1) = 0) (a : Fin (p + 1) → B) (ha0 : a 0 = 1)
    (h1 : 1 < p + 1) :
    (∑ i, a i * δ ^ (i : ℕ)) ^ p = 1 + a ⟨1, h1⟩ ^ p * δ ^ p := by
  have hpp : p.Prime := Fact.out
  have hp2 : 2 ≤ p := hpp.two_le
  rcases subsingleton_or_nontrivial B with hB | hB
  · exact Subsingleton.elim _ _
  haveI : CharP B p := by
    have h := CharP.ringChar_of_prime_eq_zero hpp hp0
    rw [← h]
    exact ringChar.charP B
  rw [sum_pow_char p]
  have hterm : ∀ i : Fin (p + 1), (a i * δ ^ (i : ℕ)) ^ p =
      (if i = 0 then 1 else 0) + (if i = ⟨1, h1⟩ then a ⟨1, h1⟩ ^ p * δ ^ p else 0) := by
    intro i
    by_cases hi0 : i = 0
    · subst hi0
      have : (0 : Fin (p + 1)) ≠ ⟨1, h1⟩ := by
        intro h
        have := congrArg Fin.val h
        simp at this
      simp [ha0, this]
    by_cases hi1 : i = ⟨1, h1⟩
    · subst hi1
      have : (⟨1, h1⟩ : Fin (p + 1)) ≠ 0 := by
        intro h
        have := congrArg Fin.val h
        simp at this
      simp [this, mul_pow]
    · have hv0 : (i : ℕ) ≠ 0 := fun h => hi0 (Fin.ext h)
      have hv1 : (i : ℕ) ≠ 1 := fun h => hi1 (Fin.ext h)
      have hv : 2 ≤ (i : ℕ) := by omega
      have hle : p + 1 ≤ (i : ℕ) * p := by nlinarith
      have hz : δ ^ ((i : ℕ) * p) = 0 := by
        obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
        rw [hk, pow_add, hδ, zero_mul]
      simp [hi0, hi1, mul_pow, ← pow_mul, hz]
  simp only [hterm, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/- English proof (translation)
Rewrite using `[Fin.sum_univ_succ, mul_add, Finset.mul_sum]`. Establish `hz : ∀ i : Fin p, δ ^ p * (b i.succ * δ ^ ((i.succ : Fin (p + 1)) : ℕ)) = 0`. Introduce `i`. Establish `: δ ^ p * (b i.succ * δ ^ ((i.succ : Fin (p + 1)) : ℕ)) = b i.succ * (δ ^ (p + 1) * δ ^ (i : ℕ))`. Simplify using `only [Fin.val_succ]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, hδ]`. Simplify using the standard rewrite rules. Rewrite using `[Finset.sum_eq_zero (fun i _ => hz i)]`. Simplify using `[hb0]`.
-/
theorem delta_pow_mul_truncated {B : Type} [CommRing B] (δ : B) (p : ℕ)
    (hδ : δ ^ (p + 1) = 0) (b : Fin (p + 1) → B) (hb0 : b 0 = 1) :
    δ ^ p * ∑ i, b i * δ ^ (i : ℕ) = δ ^ p := by
  rw [Fin.sum_univ_succ, mul_add, Finset.mul_sum]
  have hz : ∀ i : Fin p, δ ^ p * (b i.succ * δ ^ ((i.succ : Fin (p + 1)) : ℕ)) = 0 := by
    intro i
    have : δ ^ p * (b i.succ * δ ^ ((i.succ : Fin (p + 1)) : ℕ)) =
        b i.succ * (δ ^ (p + 1) * δ ^ (i : ℕ)) := by
      simp only [Fin.val_succ]
      ring
    rw [this, hδ]
    simp
  rw [Finset.sum_eq_zero (fun i _ => hz i)]
  simp [hb0]

/- English proof (translation)
Introduce `A B _ _ π δ p _ hp0 hδ huniq u c₁ c₂ hu0 hc₁ hc₂ hmain`. Establish `h1 : 1 < p + 1` using `Nat.succ_lt_succ (Nat.Prime.pos Fact.out)`. Establish `hfrob` using `pow_frobenius_truncated δ p hp0 hδ (fun i => π (u i)) (by simp [hu0]) h1`. Establish `hdel` using `delta_pow_mul_truncated δ p hδ (fun i => π (c₂ i)) (by simp [hc₂])`. Establish `hlast : ∀ i : Fin (p + 1), π (Function.update c₂ (Fin.last p) (c₂ (Fin.last p) + u ⟨1, h1⟩ ^ p) i) * δ ^ (i : ℕ) = π (c₂ i) * δ ^ (i : ℕ) + (if i = Fin.last p then π (u ⟨1, h1⟩) ^ p * δ ^ p else 0)`.

Introduce `i`. Distinguish the cases in `hi : i = Fin.last p`. Substitute `hi` using the available equality. Simplify using `[add_mul]`. Simplify using `[Function.update_of_ne hi, hi]`.

Establish `hsum : ∑ i, π (c₁ i) * δ ^ (i : ℕ) = ∑ i, π (Function.update c₂ (Fin.last p) (c₂ (Fin.last p) + u ⟨1, h1⟩ ^ p) i) * δ ^ (i : ℕ)`. Simplify using `only [hlast, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Rewrite using `[hmain, hfrob, add_mul, _root_.one_mul, _root_.mul_assoc, hdel]`. Use `huniq _ _ hsum` as an intermediate fact. Rewrite using `[this]`.

Simplify using the standard rewrite rules.
-/
theorem coeff_comparison : ∀ (A B : Type) [CommRing A] [CommRing B] (π : A →+* B) (δ : B) (p : ℕ) [Fact p.Prime], (p : B) = 0 → δ ^ (p + 1) = 0 → (∀ c c' : Fin (p + 1) → A, ∑ i, π (c i) * δ ^ (i : ℕ) = ∑ i, π (c' i) * δ ^ (i : ℕ) → c = c') → ∀ (u c₁ c₂ : Fin (p + 1) → A), u 0 = 1 → c₁ 0 = 1 → c₂ 0 = 1 → ∑ i, π (c₁ i) * δ ^ (i : ℕ) = (∑ i, π (u i) * δ ^ (i : ℕ)) ^ p * ∑ i, π (c₂ i) * δ ^ (i : ℕ) → c₁ (Fin.last p) = c₂ (Fin.last p) + u ⟨1, Nat.succ_lt_succ (Nat.Prime.pos Fact.out)⟩ ^ p := by
  intro A B _ _ π δ p _ hp0 hδ huniq u c₁ c₂ hu0 hc₁ hc₂ hmain
  have h1 : 1 < p + 1 := Nat.succ_lt_succ (Nat.Prime.pos Fact.out)
  have hfrob := pow_frobenius_truncated δ p hp0 hδ (fun i => π (u i)) (by simp [hu0]) h1
  have hdel := delta_pow_mul_truncated δ p hδ (fun i => π (c₂ i)) (by simp [hc₂])
  have hlast : ∀ i : Fin (p + 1),
      π (Function.update c₂ (Fin.last p) (c₂ (Fin.last p) + u ⟨1, h1⟩ ^ p) i) * δ ^ (i : ℕ) =
        π (c₂ i) * δ ^ (i : ℕ) +
          (if i = Fin.last p then π (u ⟨1, h1⟩) ^ p * δ ^ p else 0) := by
    intro i
    by_cases hi : i = Fin.last p
    · subst hi
      simp [add_mul]
    · simp [Function.update_of_ne hi, hi]
  have hsum : ∑ i, π (c₁ i) * δ ^ (i : ℕ) = ∑ i,
      π (Function.update c₂ (Fin.last p) (c₂ (Fin.last p) + u ⟨1, h1⟩ ^ p) i) * δ ^ (i : ℕ) := by
    simp only [hlast, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [hmain, hfrob, add_mul, _root_.one_mul, _root_.mul_assoc, hdel]
  have := huniq _ _ hsum
  rw [this]
  simp

end GlobalTheory.CompanionTheory.Ar.CoefAlg
