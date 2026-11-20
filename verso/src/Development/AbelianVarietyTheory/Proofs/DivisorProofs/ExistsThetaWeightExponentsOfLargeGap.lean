import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.AllWt (Psi wtOf)

namespace GlobalTheory.ThetaWtGap

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

/- English proof (translation)
Establish `h0 : ∀ x, 0 ≤ (wtOf Dw la m).1 x`. Introduce `x`. Simplify using `only [wtOf]`. Use `split_ifs with h hi h' hi`. Use `hb ⟨x.1, h⟩ ⟨x.2, by omega⟩ hi` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Conclude with `le_rfl`. Use `hs ⟨_, h'⟩ ⟨Dw.p + (Dw.q - 1 - x.2), by omega⟩ (Nat.le_add_right _ _)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Conclude with `le_rfl`.

Conclude with `le_rfl`. Use `⟨h0, fun τ i j hij => ?_⟩` and prove the remaining obligations. Establish `hi0` using `h0 (τ, i)`. Simplify using `only [wtOf] at hi0 ⊢`. Distinguish the cases in `h : τ (H.rt : E) = H.rt0`.

Simplify using `only [dif_pos h] at hi0 ⊢`. Distinguish the cases in `hj : j < Dw.p`. Establish `hi : i < Dw.p` using `by omega`. Simplify using `only [dif_pos hi, dif_pos hj]`. Use `ha ⟨τ, h⟩ (show (⟨i, by omega⟩ : Fin (Dw.p + Dw.q)) ≤ ⟨j, by omega⟩ from hij)` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Simplify `hi0` using `only [dif_neg hj]`. Establish `h'` using `AllWt.conj_mem h`. Simplify using `only [dif_neg h, dif_pos h'] at hi0 ⊢`. Distinguish the cases in `hj : j < Dw.q`.

Establish `hi : i < Dw.q` using `by omega`. Simplify using `only [dif_pos hi, dif_pos hj]`. Use `ha ⟨_, h'⟩ (show (⟨Dw.p + (Dw.q - 1 - j), by omega⟩ : Fin (Dw.p + Dw.q)) ≤ ⟨Dw.p + (Dw.q - 1 - i), by omega⟩ from Fin.mk_le_mk.2 (by omega))` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Simplify `hi0` using `only [dif_neg hj]`.
-/
theorem wtOf_nonneg_antitone (la : AllWt.Weight Dw) (m : ℤ) (ha : ∀ τ, Antitone (la τ))
    (hb : ∀ τ (k : Fin (Dw.p + Dw.q)), (k : ℕ) < Dw.p → m ≤ la τ k)
    (hs : ∀ τ (k : Fin (Dw.p + Dw.q)), Dw.p ≤ (k : ℕ) → la τ k ≤ -m) :
    (∀ x, 0 ≤ (wtOf Dw la m).1 x) ∧ ∀ τ, Antitone fun i => (wtOf Dw la m).1 (τ, i) := by
  have h0 : ∀ x, 0 ≤ (wtOf Dw la m).1 x := by
    intro x
    simp only [wtOf]
    split_ifs with h hi h' hi
    · have := hb ⟨x.1, h⟩ ⟨x.2, by omega⟩ hi
      omega
    · exact le_rfl
    · have := hs ⟨_, h'⟩ ⟨Dw.p + (Dw.q - 1 - x.2), by omega⟩ (Nat.le_add_right _ _)
      omega
    · exact le_rfl
    · exact le_rfl
  refine ⟨h0, fun τ i j hij => ?_⟩
  have hi0 := h0 (τ, i)
  simp only [wtOf] at hi0 ⊢
  by_cases h : τ (H.rt : E) = H.rt0
  · simp only [dif_pos h] at hi0 ⊢
    by_cases hj : j < Dw.p
    · have hi : i < Dw.p := by omega
      simp only [dif_pos hi, dif_pos hj]
      have := ha ⟨τ, h⟩ (show (⟨i, by omega⟩ : Fin (Dw.p + Dw.q)) ≤ ⟨j, by omega⟩ from hij)
      omega
    · simpa only [dif_neg hj] using hi0
  · have h' := AllWt.conj_mem h
    simp only [dif_neg h, dif_pos h'] at hi0 ⊢
    by_cases hj : j < Dw.q
    · have hi : i < Dw.q := by omega
      simp only [dif_pos hi, dif_pos hj]
      have := ha ⟨_, h'⟩ (show (⟨Dw.p + (Dw.q - 1 - j), by omega⟩ : Fin (Dw.p + Dw.q)) ≤
        ⟨Dw.p + (Dw.q - 1 - i), by omega⟩ from Fin.mk_le_mk.2 (by omega))
      omega
    · simpa only [dif_neg hj] using hi0

/- English proof (translation)
Use `set lb : AllWt.Weight Dw := la + GlobalTheory.FlatLine.parWt Dw (fun τ => 1 + (m : ℤ) - la τ ⟨Dw.p - 1, by omega⟩) with hlb`. Establish `e : ∀ τ k, lb τ k = la τ k + (1 + (m : ℤ) - la τ ⟨Dw.p - 1, by omega⟩)` using `fun _ _ => rfl`. Establish `hb : ∀ τ (k : Fin (Dw.p + Dw.q)), (k : ℕ) < Dw.p → (m : ℤ) < lb τ k`. Introduce `τ k hk`. Use `ha τ (show k ≤ (⟨Dw.p - 1, by omega⟩ : Fin (Dw.p + Dw.q)) from Fin.le_def.2 (by simp only; omega))` as an intermediate fact.

Rewrite using `[e]`. Use linear arithmetic over natural numbers and integers. Establish `hs : ∀ τ (k : Fin (Dw.p + Dw.q)), Dw.p ≤ (k : ℕ) → lb τ k ≤ -(m : ℤ)`. Introduce `τ k hk`. Establish `hk2` using `k.2`.

Establish `hlt : Dw.p - 1 + 1 < Dw.p + Dw.q` using `by omega`. Establish `h1` using `hg τ`. Rewrite `h1` using `[GlobalTheory.CompHS.gap, dif_pos hlt]`. Establish `h2` using `ha τ (show (⟨Dw.p - 1 + 1, hlt⟩ : Fin (Dw.p + Dw.q)) ≤ k from Fin.le_def.2 (by simp only; omega))`. Rewrite using `[e]`.

Move the coercions through the operations in `at h1`. Use linear arithmetic over natural numbers and integers. Establish `hanti : ∀ τ, Antitone (lb τ)` using `fun τ i j hij => by`. Use `ha τ hij` as an intermediate fact. Rewrite using `[e, e]`.

Use linear arithmetic over natural numbers and integers. Take `⟨h0, h1⟩` from `wtOf_nonneg_antitone lb m hanti (fun τ k hk => (hb τ k hk).le) hs`. Establish `hm : 2 * m / 2 = m` using `by omega`. Establish `hla : GlobalTheory.CovTop.laOf Dw (fun x => ((wtOf Dw lb m).1 x).toNat) (2 * m) = lb`. Rewrite using `[GlobalTheory.CovTop.laOf, hm]`.

Simplify using `only [Int.toNat_of_nonneg (h0 _)]`. Conclude with `AllWt.weightOf_wtOf lb m`. Use `⟨fun x => ((wtOf Dw lb m).1 x).toNat, ⟨fun τ i j hij => Int.toNat_le_toNat (h1 τ hij), even_two_mul m⟩, hla, ?_⟩` and prove the remaining obligations. Introduce `τ k hk`. Rewrite using `[hla, hm]`.

Conclude with `hb τ k hk`.
-/
theorem exists_exponents (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (m : ℕ) (la : AllWt.Weight Dw) (hp : 1 ≤ Dw.p) (ha : ∀ τ, Antitone (la τ))
    (hg : ∀ τ, ((2 * m + 2 : ℕ) : ℤ) ≤ GlobalTheory.CompHS.gap (la τ) (Dw.p - 1)) :
    ∃ a : (E →+* ℂ) × ℕ → ℕ, Formalism.L2.Pj.Dom a (2 * m) ∧
      GlobalTheory.CovTop.laOf Dw a (2 * m) =
        la + GlobalTheory.FlatLine.parWt Dw (fun τ => 1 + (m : ℤ) - la τ ⟨Dw.p - 1, by omega⟩) ∧
      ∀ (τ : Psi H) (k : Fin (Dw.p + Dw.q)), (k : ℕ) < Dw.p →
        (((2 * m) / 2 : ℕ) : ℤ) < GlobalTheory.CovTop.laOf Dw a (2 * m) τ k := by
  set lb : AllWt.Weight Dw := la + GlobalTheory.FlatLine.parWt Dw (fun τ => 1 + (m : ℤ) - la τ ⟨Dw.p - 1, by omega⟩) with hlb
  have e : ∀ τ k, lb τ k = la τ k + (1 + (m : ℤ) - la τ ⟨Dw.p - 1, by omega⟩) := fun _ _ => rfl
  have hb : ∀ τ (k : Fin (Dw.p + Dw.q)), (k : ℕ) < Dw.p → (m : ℤ) < lb τ k := by
    intro τ k hk
    have := ha τ (show k ≤ (⟨Dw.p - 1, by omega⟩ : Fin (Dw.p + Dw.q)) from Fin.le_def.2 (by simp only; omega))
    rw [e]; omega
  have hs : ∀ τ (k : Fin (Dw.p + Dw.q)), Dw.p ≤ (k : ℕ) → lb τ k ≤ -(m : ℤ) := by
    intro τ k hk
    have hk2 := k.2
    have hlt : Dw.p - 1 + 1 < Dw.p + Dw.q := by omega
    have h1 := hg τ
    rw [GlobalTheory.CompHS.gap, dif_pos hlt] at h1
    have h2 := ha τ (show (⟨Dw.p - 1 + 1, hlt⟩ : Fin (Dw.p + Dw.q)) ≤ k from Fin.le_def.2 (by simp only; omega))
    rw [e]; push_cast at h1; omega
  have hanti : ∀ τ, Antitone (lb τ) := fun τ i j hij => by
    have := ha τ hij
    rw [e, e]; omega
  obtain ⟨h0, h1⟩ := wtOf_nonneg_antitone lb m hanti (fun τ k hk => (hb τ k hk).le) hs
  have hm : 2 * m / 2 = m := by omega
  have hla : GlobalTheory.CovTop.laOf Dw (fun x => ((wtOf Dw lb m).1 x).toNat) (2 * m) = lb := by
    rw [GlobalTheory.CovTop.laOf, hm]
    simp only [Int.toNat_of_nonneg (h0 _)]
    exact AllWt.weightOf_wtOf lb m
  refine ⟨fun x => ((wtOf Dw lb m).1 x).toNat, ⟨fun τ i j hij => Int.toNat_le_toNat (h1 τ hij), even_two_mul m⟩, hla, ?_⟩
  intro τ k hk
  rw [hla, hm]
  exact hb τ k hk

end GlobalTheory.ThetaWtGap
