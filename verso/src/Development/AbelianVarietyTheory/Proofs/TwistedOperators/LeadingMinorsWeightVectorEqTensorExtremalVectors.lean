import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurePreservingMulRight
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqBotOrTopOfTensor
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining

open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries

noncomputable section

namespace GlobalTheory.HwTen

/- English proof (translation)
Unfold `Formalism.GradedWeylDivisibility.lpMinor minor`. Rewrite using `[AlgHom.map_det]`. Use `congr 1`. Use extensionality with `p q`. Simplify using `[Formalism.GradedWeylDivisibility.blockEmb, rename_X]`.
-/
theorem blockEmb_lpMinor {ι : Type} [Fintype ι] [DecidableEq ι] (n : ℕ) (τ : ι) (l : Fin n) :
    Formalism.GradedWeylDivisibility.blockEmb ℂ τ (Formalism.GradedWeylDivisibility.lpMinor ℂ (r := n) (n := n) (l.val + 1) (by omega) (by omega)) = minor n τ l := by
  unfold Formalism.GradedWeylDivisibility.lpMinor minor
  rw [AlgHom.map_det]
  congr 1
  ext p q
  simp [Formalism.GradedWeylDivisibility.blockEmb, rename_X]

/- English proof (translation)
Establish `hn : 0 < n` using `Fin.pos s`. Establish `hd : mu.detShift = mu.w ⟨n - 1, by omega⟩` using `by simp [DomWeight.detShift, hn]`. Unfold `Formalism.GradedWeylDivisibility.nuNext DomWeight.natW`. Rewrite using `[hd]`. Use `split_ifs with h`.

Establish `h1` using `mu.anti (show s ≤ ⟨s.val + 1, h⟩ from by rw [Fin.le_def]; simp)`. Establish `h2` using `mu.anti (show (⟨s.val + 1, h⟩ : Fin n) ≤ ⟨n - 1, by omega⟩ from by rw [Fin.le_def]; simp; omega)`. Use linear arithmetic over natural numbers and integers. Establish `: s = ⟨n - 1, by omega⟩` using `Fin.ext (by simp; omega)`. Rewrite using `[← this]`.

Simplify using the standard rewrite rules.
-/
theorem natW_sub_nuNext {n : ℕ} (mu : DomWeight n) (s : Fin n) :
    mu.natW s - Formalism.GradedWeylDivisibility.nuNext mu.natW s =
      if h : s.val + 1 < n then (mu.w s - mu.w ⟨s.val + 1, h⟩).toNat else 0 := by
  have hn : 0 < n := Fin.pos s
  have hd : mu.detShift = mu.w ⟨n - 1, by omega⟩ := by simp [DomWeight.detShift, hn]
  unfold Formalism.GradedWeylDivisibility.nuNext DomWeight.natW
  rw [hd]
  split_ifs with h
  · have h1 := mu.anti (show s ≤ ⟨s.val + 1, h⟩ from by rw [Fin.le_def]; simp)
    have h2 := mu.anti (show (⟨s.val + 1, h⟩ : Fin n) ≤ ⟨n - 1, by omega⟩ from by rw [Fin.le_def]; simp; omega)
    omega
  · have : s = ⟨n - 1, by omega⟩ := Fin.ext (by simp; omega)
    rw [← this]
    simp

/- English proof (translation)
Introduce `ι _ _ n lam lam' hl`. Unfold `hwVec Formalism.L2.DIV.ten`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Unfold `Formalism.BasicNotions.extremal Formalism.GradedWeylDivisibility.hw`. Rewrite using `[map_prod, Finset.prod_filter]`.

Use `Finset.prod_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[map_pow, blockEmb_lpMinor, natW_sub_nuNext]`. Use `split_ifs with h`. Use `congr 1`. Rewrite using `[← hl τ s, ← hl τ ⟨s.val + 1, h⟩]`.

Both sides reduce to the same expression.
-/
theorem hwVec_eq_ten : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (n : ℕ) (lam : ι → ℕ → ℤ) (lam' : ι → DomWeight n), (∀ τ (i : Fin n), (lam' τ).w i = lam τ i) → hwVec n lam = Formalism.L2.DIV.ten (fun τ => Formalism.BasicNotions.extremal ℂ n (lam' τ)) := by
  intro ι _ _ n lam lam' hl
  unfold hwVec Formalism.L2.DIV.ten
  refine Finset.prod_congr rfl fun τ _ => ?_
  unfold Formalism.BasicNotions.extremal Formalism.GradedWeylDivisibility.hw
  rw [map_prod, Finset.prod_filter]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_pow, blockEmb_lpMinor, natW_sub_nuNext]
  split_ifs with h
  · congr 1
    rw [← hl τ s, ← hl τ ⟨s.val + 1, h⟩]
  · rfl

end GlobalTheory.HwTen
