import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.WtMatchArithBar

/- English proof (translation)
Establish `hN' : (1 : ℤ) ≤ N` using `by exact_mod_cast hN`. Establish `hk0 : (0 : ℤ) ≤ k` using `Int.natCast_nonneg k`. Establish `hM0 : (0 : ℤ) ≤ M` using `Int.natCast_nonneg M`. Use `set X : ℤ := ((k : ℤ) + 1) * f ⟨p - 1, by omega⟩ - M with hX`. Use `⟨-(X / N), fun i hi => ?_, fun i hi => ?_⟩` and prove the remaining obligations.

Establish `h1 : f i ≥ f ⟨p - 1, by omega⟩` using `hf (by simp [Fin.le_def]; omega)`. Establish `h2 : ((k : ℤ) + 1) * f ⟨p - 1, by omega⟩ ≤ ((k : ℤ) + 1) * f i` using `mul_le_mul_of_nonneg_left h1 (by linarith)`. Establish `h3` using `Int.emod_nonneg X (by omega : (N : ℤ) ≠ 0)`. Establish `h4` using `Int.emod_add_mul_ediv X (N : ℤ)`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h1 : f i ≤ f ⟨p, by omega⟩` using `hf (by simp [Fin.le_def]; omega)`. Establish `hg` using `hg0`. Unfold `GlobalTheory.CompHS.gap at hg`. Rewrite `hg` using `[dif_pos (by omega)]`. Establish `e : (⟨p - 1 + 1, by omega⟩ : Fin (p + q)) = ⟨p, by omega⟩` using `Fin.ext (by simp; omega)`.

Rewrite `hg` using `[e]`. Establish `h2 : ((k : ℤ) + 1) * f i ≤ ((k : ℤ) + 1) * (f ⟨p - 1, by omega⟩ - 1)` using `mul_le_mul_of_nonneg_left (by linarith) (by linarith)`. Establish `h3` using `Int.emod_lt_of_pos X (by omega : (0 : ℤ) < N)`. Establish `h4` using `Int.emod_add_mul_ediv X (N : ℤ)`. Establish `hk' : (2 * M + N : ℤ) ≤ k + 1` using `by exact_mod_cast hk`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem exists_shift {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) (f : Fin (p + q) → ℤ) (hf : Antitone f)
    (hg0 : 1 ≤ GlobalTheory.CompHS.gap f (p - 1))
    (N M k : ℕ) (hN : 0 < N) (hk : 2 * M + N ≤ k + 1) :
    ∃ w : ℤ, (∀ i : Fin (p + q), (i : ℕ) < p → 0 ≤ ((k : ℤ) + 1) * f i + N * w - M) ∧
      (∀ i : Fin (p + q), p ≤ (i : ℕ) → 0 ≤ -(((k : ℤ) + 1) * f i) - N * w - M) := by
  have hN' : (1 : ℤ) ≤ N := by exact_mod_cast hN
  have hk0 : (0 : ℤ) ≤ k := Int.natCast_nonneg k
  have hM0 : (0 : ℤ) ≤ M := Int.natCast_nonneg M
  set X : ℤ := ((k : ℤ) + 1) * f ⟨p - 1, by omega⟩ - M with hX
  refine ⟨-(X / N), fun i hi => ?_, fun i hi => ?_⟩
  · have h1 : f i ≥ f ⟨p - 1, by omega⟩ := hf (by simp [Fin.le_def]; omega)
    have h2 : ((k : ℤ) + 1) * f ⟨p - 1, by omega⟩ ≤ ((k : ℤ) + 1) * f i := mul_le_mul_of_nonneg_left h1 (by linarith)
    have h3 := Int.emod_nonneg X (by omega : (N : ℤ) ≠ 0)
    have h4 := Int.emod_add_mul_ediv X (N : ℤ)
    linarith
  · have h1 : f i ≤ f ⟨p, by omega⟩ := hf (by simp [Fin.le_def]; omega)
    have hg := hg0
    unfold GlobalTheory.CompHS.gap at hg
    rw [dif_pos (by omega)] at hg
    have e : (⟨p - 1 + 1, by omega⟩ : Fin (p + q)) = ⟨p, by omega⟩ := Fin.ext (by simp; omega)
    rw [e] at hg
    have h2 : ((k : ℤ) + 1) * f i ≤ ((k : ℤ) + 1) * (f ⟨p - 1, by omega⟩ - 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have h3 := Int.emod_lt_of_pos X (by omega : (0 : ℤ) < N)
    have h4 := Int.emod_add_mul_ediv X (N : ℤ)
    have hk' : (2 * M + N : ℤ) ≤ k + 1 := by exact_mod_cast hk
    nlinarith

open GlobalTheory.AllWt in

/- English proof (translation)
Introduce `E _ _ _ H Dw la hp hq hanti hgap N M k hN hk`. Establish `key : ∀ σ : Psi H, ∃ w : ℤ, (∀ i : Fin (Dw.p + Dw.q), (i : ℕ) < Dw.p → 0 ≤ ((k : ℤ) + 1) * la σ i + N * w - M) ∧ (∀ i : Fin (Dw.p + Dw.q), Dw.p ≤ (i : ℕ) → 0 ≤ -(((k : ℤ) + 1) * la σ i) - N * w - M)` using `fun σ => exists_shift hp hq (la σ) (hanti σ) (hgap σ) N M k hN hk`. Use `choose w hwb hws using key`. Establish `hantiσ : ∀ (σ : Psi H) (i j : Fin (Dw.p + Dw.q)), i ≤ j → la σ j ≤ la σ i` using `fun σ _ _ h => hanti σ h`. Use `set val : (E →+* ℂ) × ℕ → ℤ := fun x => ((k : ℤ) + 1) * (wtOf Dw la 0).1 x + (wtOf Dw (GlobalTheory.FlatLine.parWt Dw fun τ => (N : ℤ) * w τ) (M : ℤ)).1 x with hval`.

Establish `vbig : ∀ (σ : Psi H) (i : ℕ) (hi : i < Dw.p), val (σ.1, i) = ((k : ℤ) + 1) * la σ ⟨i, by omega⟩ + (N * w σ - M)`. Introduce `σ i hi`. Simplify using `only [hval]`. Rewrite using `[wtOf_big _ _ σ i hi, wtOf_big _ _ σ i hi]`. Simplify using `[GlobalTheory.FlatLine.parWt]`.

Establish `vsmall : ∀ (σ : Psi H) (i : ℕ) (hi : i < Dw.q), val (conjEmb σ.1, i) = -(((k : ℤ) + 1) * la σ ⟨Dw.p + (Dw.q - 1 - i), by omega⟩) - N * w σ - M`. Introduce `σ i hi`. Simplify using `only [hval]`. Rewrite using `[wtOf_small _ _ σ i hi, wtOf_small _ _ σ i hi]`. Simplify using `[GlobalTheory.FlatLine.parWt]`.

Expand and normalize the polynomial expressions, which then agree. Establish `split : ∀ τ : E →+* ℂ, (∃ σ : Psi H, σ.1 = τ ∧ Dw.mult τ = Dw.p) ∨ (∃ σ : Psi H, conjEmb σ.1 = τ ∧ Dw.mult τ = Dw.q)`. Introduce `τ`. Distinguish the cases in `h : τ (H.rt : E) = H.rt0`. Conclude with `Or.inl ⟨⟨τ, h⟩, rfl, by simp [Datum.mult, h]⟩`.

Conclude with `Or.inr ⟨⟨conjEmb τ, conj_mem h⟩, conjEmb_conjEmb τ, by simp [Datum.mult, h]⟩`. Establish `nonneg : ∀ (τ : E →+* ℂ) (i : ℕ), i < Dw.mult τ → 0 ≤ val (τ, i)`. Introduce `τ i hi`. Break down `split τ with ⟨σ, rfl, hm⟩ | ⟨σ, rfl, hm⟩` into its components or cases. Rewrite using `[hm] at hi; rw [vbig σ i hi]; have := hwb σ ⟨i, by omega⟩ hi; linarith`.

Rewrite using `[hm] at hi; rw [vsmall σ i hi]; exact hws σ _ (by simp)`. Establish `mono : ∀ (τ : E →+* ℂ) (i j : ℕ), i ≤ j → j < Dw.mult τ → val (τ, j) ≤ val (τ, i)`. Introduce `τ i j hij hj`. Establish `hk0 : (0 : ℤ) ≤ (k : ℤ) + 1` using `by positivity`. Break down `split τ with ⟨σ, rfl, hm⟩ | ⟨σ, rfl, hm⟩` into its components or cases.

Rewrite `hj` using `[hm]`. Rewrite using `[vbig σ i (by omega), vbig σ j hj]`. Use `hantiσ σ ⟨i, by omega⟩ ⟨j, by omega⟩ (by simp [Fin.le_def]; omega)` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Rewrite `hj` using `[hm]`.

Rewrite using `[vsmall σ i (by omega), vsmall σ j hj]`. Use `hantiσ σ ⟨Dw.p + (Dw.q - 1 - j), by omega⟩ ⟨Dw.p + (Dw.q - 1 - i), by omega⟩ (by simp [Fin.le_def]; omega)` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Use `⟨w, fun x => if x.2 < Dw.mult x.1 then (val x).toNat else 0, ⟨fun τ => ?_, even_two_mul M⟩, ?_⟩` and prove the remaining obligations. Introduce `i j hij`.

Simplify using `only`. Use `split_ifs with hj hi hi`. Conclude with `Int.toNat_le_toNat (mono τ i j hij hj)`. Use linear arithmetic over natural numbers and integers. Conclude with `Nat.zero_le _`.

Conclude with `le_refl _`. Use function extensionality and compare the values at `x`. Break down `x with _ | ⟨τ, i⟩` into its components or cases. Simplify using `[ex, exOf, exZ, wtOf]`. Establish `hi : (i : ℕ) < Dw.mult τ` using `i.2 show (((if (i : ℕ) < Dw.mult τ then (val (τ, (i : ℕ))).toNat else 0 : ℕ)) : ℤ) = _`.

Rewrite using `[if_pos hi, Int.toNat_of_nonneg (nonneg τ i hi)]`. Rewrite using `[Pi.add_apply, Pi.smul_apply]`. Use `show _ = (k + 1) • (wtOf Dw la 0).1 (τ, (i : ℕ)) + (wtOf Dw (GlobalTheory.FlatLine.parWt Dw fun τ => (N : ℤ) * w τ) (M : ℤ)).1 (τ, (i : ℕ))`. Rewrite using `[nsmul_eq_mul]`. Simplify using `only [hval]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_dom_exponents_bar : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (la : GlobalTheory.AllWt.Weight Dw), 1 ≤ Dw.p → 1 ≤ Dw.q → (∀ τ, Antitone (la τ)) → (∀ τ, 1 ≤ GlobalTheory.CompHS.gap (la τ) (Dw.p - 1)) → ∀ (N M k : ℕ), 0 < N → 2 * M + N ≤ k + 1 → ∃ (w : GlobalTheory.AllWt.Psi H → ℤ) (a : (E →+* ℂ) × ℕ → ℕ), Dom a (2 * M) ∧ (fun i => (ex Dw a (2 * M) i : ℤ)) = (k + 1) • GlobalTheory.AllWt.exOf Dw la 0 + GlobalTheory.AllWt.exOf Dw (GlobalTheory.FlatLine.parWt Dw fun τ => (N : ℤ) * w τ) M := by
  intro E _ _ _ H Dw la hp hq hanti hgap N M k hN hk
  have key : ∀ σ : Psi H, ∃ w : ℤ,
      (∀ i : Fin (Dw.p + Dw.q), (i : ℕ) < Dw.p → 0 ≤ ((k : ℤ) + 1) * la σ i + N * w - M) ∧
      (∀ i : Fin (Dw.p + Dw.q), Dw.p ≤ (i : ℕ) → 0 ≤ -(((k : ℤ) + 1) * la σ i) - N * w - M) :=
    fun σ => exists_shift hp hq (la σ) (hanti σ) (hgap σ) N M k hN hk
  choose w hwb hws using key
  have hantiσ : ∀ (σ : Psi H) (i j : Fin (Dw.p + Dw.q)), i ≤ j → la σ j ≤ la σ i :=
    fun σ _ _ h => hanti σ h
  set val : (E →+* ℂ) × ℕ → ℤ := fun x => ((k : ℤ) + 1) * (wtOf Dw la 0).1 x +
    (wtOf Dw (GlobalTheory.FlatLine.parWt Dw fun τ => (N : ℤ) * w τ) (M : ℤ)).1 x with hval
  have vbig : ∀ (σ : Psi H) (i : ℕ) (hi : i < Dw.p),
      val (σ.1, i) = ((k : ℤ) + 1) * la σ ⟨i, by omega⟩ + (N * w σ - M) := by
    intro σ i hi
    simp only [hval]
    rw [wtOf_big _ _ σ i hi, wtOf_big _ _ σ i hi]
    simp [GlobalTheory.FlatLine.parWt]
  have vsmall : ∀ (σ : Psi H) (i : ℕ) (hi : i < Dw.q),
      val (conjEmb σ.1, i) = -(((k : ℤ) + 1) * la σ ⟨Dw.p + (Dw.q - 1 - i), by omega⟩) - N * w σ - M := by
    intro σ i hi
    simp only [hval]
    rw [wtOf_small _ _ σ i hi, wtOf_small _ _ σ i hi]
    simp [GlobalTheory.FlatLine.parWt]
    ring
  have split : ∀ τ : E →+* ℂ, (∃ σ : Psi H, σ.1 = τ ∧ Dw.mult τ = Dw.p) ∨
      (∃ σ : Psi H, conjEmb σ.1 = τ ∧ Dw.mult τ = Dw.q) := by
    intro τ
    by_cases h : τ (H.rt : E) = H.rt0
    · exact Or.inl ⟨⟨τ, h⟩, rfl, by simp [Datum.mult, h]⟩
    · exact Or.inr ⟨⟨conjEmb τ, conj_mem h⟩, conjEmb_conjEmb τ, by simp [Datum.mult, h]⟩
  have nonneg : ∀ (τ : E →+* ℂ) (i : ℕ), i < Dw.mult τ → 0 ≤ val (τ, i) := by
    intro τ i hi
    rcases split τ with ⟨σ, rfl, hm⟩ | ⟨σ, rfl, hm⟩
    · rw [hm] at hi; rw [vbig σ i hi]; have := hwb σ ⟨i, by omega⟩ hi; linarith
    · rw [hm] at hi; rw [vsmall σ i hi]; exact hws σ _ (by simp)
  have mono : ∀ (τ : E →+* ℂ) (i j : ℕ), i ≤ j → j < Dw.mult τ → val (τ, j) ≤ val (τ, i) := by
    intro τ i j hij hj
    have hk0 : (0 : ℤ) ≤ (k : ℤ) + 1 := by positivity
    rcases split τ with ⟨σ, rfl, hm⟩ | ⟨σ, rfl, hm⟩
    · rw [hm] at hj
      rw [vbig σ i (by omega), vbig σ j hj]
      have := hantiσ σ ⟨i, by omega⟩ ⟨j, by omega⟩ (by simp [Fin.le_def]; omega)
      nlinarith
    · rw [hm] at hj
      rw [vsmall σ i (by omega), vsmall σ j hj]
      have := hantiσ σ ⟨Dw.p + (Dw.q - 1 - j), by omega⟩ ⟨Dw.p + (Dw.q - 1 - i), by omega⟩
        (by simp [Fin.le_def]; omega)
      nlinarith
  refine ⟨w, fun x => if x.2 < Dw.mult x.1 then (val x).toNat else 0, ⟨fun τ => ?_, even_two_mul M⟩, ?_⟩
  · intro i j hij
    simp only
    split_ifs with hj hi hi
    · exact Int.toNat_le_toNat (mono τ i j hij hj)
    · omega
    · exact Nat.zero_le _
    · exact le_refl _
  · funext x
    rcases x with _ | ⟨τ, i⟩
    · simp [ex, exOf, exZ, wtOf]
    · have hi : (i : ℕ) < Dw.mult τ := i.2
      show (((if (i : ℕ) < Dw.mult τ then (val (τ, (i : ℕ))).toNat else 0 : ℕ)) : ℤ) = _
      rw [if_pos hi, Int.toNat_of_nonneg (nonneg τ i hi)]
      rw [Pi.add_apply, Pi.smul_apply]
      show _ = (k + 1) • (wtOf Dw la 0).1 (τ, (i : ℕ)) +
        (wtOf Dw (GlobalTheory.FlatLine.parWt Dw fun τ => (N : ℤ) * w τ) (M : ℤ)).1 (τ, (i : ℕ))
      rw [nsmul_eq_mul]
      simp only [hval]
      push_cast
      ring

end GlobalTheory.WtMatchArithBar
