import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsLocSec
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorIJMap
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockDiagonalMinorVanishing
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.TriStep

open GlobalTheory.CompanionTheory.Ar.PB.MinorCalc

variable {N : ℕ}

/- English proof (translation)
Distinguish the cases in `e : I.card = S.card`. Establish `hs : ¬ I ⊆ S` using `fun hs => hI (Finset.eq_of_subset_of_card_le hs e.ge)`. Take `⟨a, ha, has⟩` from `Finset.not_subset.mp hs`. Conclude with `minorIJ_eq_zero_of_row _ ha fun c hc => Matrix.one_apply_ne fun h => has (h ▸ hc)`. Conclude with `minorIJ_of_card_ne _ e`.
-/
theorem minorIJ_one_of_ne {I S : Finset (Fin N)} (hI : I ≠ S) :
    minorIJ (1 : Matrix (Fin N) (Fin N) ℂ) I S = 0 := by
  by_cases e : I.card = S.card
  · have hs : ¬ I ⊆ S := fun hs => hI (Finset.eq_of_subset_of_card_le hs e.ge)
    obtain ⟨a, ha, has⟩ := Finset.not_subset.mp hs
    exact minorIJ_eq_zero_of_row _ ha fun c hc => Matrix.one_apply_ne fun h => has (h ▸ hc)
  · exact minorIJ_of_card_ne _ e

/- English proof (translation)
Rewrite using `[minorIJ_eq_det _ S S _ rfl rfl, Matrix.submatrix_one _ (S.orderEmbOfFin rfl).injective, Matrix.det_one]`.
-/
theorem minorIJ_one_self' (S : Finset (Fin N)) : minorIJ (1 : Matrix (Fin N) (Fin N) ℂ) S S = 1 := by
  rw [minorIJ_eq_det _ S S _ rfl rfl, Matrix.submatrix_one _ (S.orderEmbOfFin rfl).injective, Matrix.det_one]

/- English proof (translation)
Distinguish the cases in `hf : Function.Injective f`. Set `σ` to `Tuple.sort f`. Establish `hm : StrictMono (f ∘ σ)` using `(Tuple.monotone_sort f).strictMono_of_injective (hf.comp σ.injective)`. Establish `hc : (Finset.univ.image f).card = S.card`. Rewrite using `[Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]`.

Establish `hu : f ∘ σ = (Finset.univ.image f).orderEmbOfFin hc` using `Finset.orderEmbOfFin_unique hc (fun y => Finset.mem_image_of_mem _ (Finset.mem_univ _)) hm`. Establish `hI : Finset.univ.image f ≠ S` using `fun e => hx (e ▸ Finset.mem_image_of_mem _ (Finset.mem_univ _))`. Establish `h0` using `hA _ hI`. Rewrite `h0` using `[minorIJ_eq_det A _ S _ hc rfl, ← hu]`. Establish `h1 : A.submatrix (f ∘ σ) (S.orderEmbOfFin rfl) = (A.submatrix f (S.orderEmbOfFin rfl)).submatrix σ id`.

Use extensionality with `a b`. Both sides reduce to the same expression. Rewrite `h0` using `[h1, Matrix.det_permute]`. Break down `mul_eq_zero.mp h0 with h | h` into its components or cases. It suffices to derive a contradiction.

Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with e | e <;> simp [e] at h`. Conclude with `h`. Choose the witnesses or unpack the hypotheses as in `⟨a, b, hab, hne⟩ : ∃ a b, f a = f b ∧ a ≠ b := by`. Simplify `hf` using `[Function.Injective]`. Conclude with `Matrix.det_zero_of_row_eq hne (by ext y; simp [hab])`.
-/
theorem det_submatrix_eq_zero (A : Matrix (Fin N) (Fin N) ℂ) (S : Finset (Fin N))
    (hA : ∀ I, I ≠ S → minorIJ A I S = 0) (f : Fin S.card → Fin N) (x : Fin S.card) (hx : f x ∉ S) :
    (A.submatrix f (S.orderEmbOfFin rfl)).det = 0 := by
  by_cases hf : Function.Injective f
  · let σ := Tuple.sort f
    have hm : StrictMono (f ∘ σ) :=
      (Tuple.monotone_sort f).strictMono_of_injective (hf.comp σ.injective)
    have hc : (Finset.univ.image f).card = S.card := by
      rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]
    have hu : f ∘ σ = (Finset.univ.image f).orderEmbOfFin hc :=
      Finset.orderEmbOfFin_unique hc (fun y => Finset.mem_image_of_mem _ (Finset.mem_univ _)) hm
    have hI : Finset.univ.image f ≠ S := fun e => hx (e ▸ Finset.mem_image_of_mem _ (Finset.mem_univ _))
    have h0 := hA _ hI
    rw [minorIJ_eq_det A _ S _ hc rfl, ← hu] at h0
    have h1 : A.submatrix (f ∘ σ) (S.orderEmbOfFin rfl) =
        (A.submatrix f (S.orderEmbOfFin rfl)).submatrix σ id := by
      ext a b; rfl
    rw [h1, Matrix.det_permute] at h0
    rcases mul_eq_zero.mp h0 with h | h
    · exfalso
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with e | e <;> simp [e] at h
    · exact h
  · obtain ⟨a, b, hab, hne⟩ : ∃ a b, f a = f b ∧ a ≠ b := by
      simpa [Function.Injective] using hf
    exact Matrix.det_zero_of_row_eq hne (by ext y; simp [hab])

/- English proof (translation)
Use `set e := S.orderEmbOfFin rfl with he`. Establish `hu : IsUnit B.det` using `isUnit_iff_ne_zero.mpr hB`. Establish `hS : minorIJ B S S ≠ 0`. Introduce `h0`. Establish `h1` using `minorIJ_mul B⁻¹ B S S`.

Rewrite `h1` using `[Matrix.nonsing_inv_mul _ hu, minorIJ_one_self', Finset.sum_eq_single S (fun I _ hI => by rw [hA I hI, mul_zero]) (by simp), h0, mul_zero]`. Conclude with `one_ne_zero h1`. Rewrite `hS` using `[minorIJ_eq_det B S S _ rfl rfl]`. Set `M` to `B.submatrix e e`. Set `v : Fin S.card → ℂ` to `fun y => B r (e y)`.

Establish `hcr : Matrix.cramer Mᵀ v = 0`. Use function extensionality and compare the values at `x`. Establish `h1 : Mᵀ.updateCol x v = (B.submatrix (Function.update e x r) e)ᵀ`. Use extensionality with `a b`. Distinguish the cases in `hb : b = x`.

Substitute `hb` using the available equality. Simplify using `[Matrix.updateCol_apply, v]`. Simplify using `[Matrix.updateCol_apply, hb, M, Function.update_of_ne hb]`. Rewrite using `[Matrix.cramer_apply, h1, Matrix.det_transpose]`. Conclude with `det_submatrix_eq_zero B S hA _ x (by simpa using hr)`.

Establish `hv : Mᵀ.det • v = 0` using `by rw [← Matrix.mulVec_cramer, hcr, Matrix.mulVec_zero]`. Establish `hv0 : v = 0`. Break down `smul_eq_zero.mp hv with h | h` into its components or cases. Rewrite `h` using `[Matrix.det_transpose]`. Conclude with `absurd h hS`.

Conclude with `h`. Establish `hr' : c ∈ Set.range e` using `by rw [he, Finset.range_orderEmbOfFin]; exact hc`. Take `⟨y, rfl⟩` from `hr'`. Conclude with `congrFun hv0 y`.
-/
theorem eq_zero_of_minors (B : Matrix (Fin N) (Fin N) ℂ) (hB : B.det ≠ 0) (S : Finset (Fin N))
    (hA : ∀ I, I ≠ S → minorIJ B I S = 0) (r c : Fin N) (hr : r ∉ S) (hc : c ∈ S) : B r c = 0 := by
  set e := S.orderEmbOfFin rfl with he
  have hu : IsUnit B.det := isUnit_iff_ne_zero.mpr hB
  have hS : minorIJ B S S ≠ 0 := by
    intro h0
    have h1 := minorIJ_mul B⁻¹ B S S
    rw [Matrix.nonsing_inv_mul _ hu, minorIJ_one_self',
      Finset.sum_eq_single S (fun I _ hI => by rw [hA I hI, mul_zero]) (by simp), h0, mul_zero] at h1
    exact one_ne_zero h1
  rw [minorIJ_eq_det B S S _ rfl rfl] at hS
  let M := B.submatrix e e
  let v : Fin S.card → ℂ := fun y => B r (e y)
  have hcr : Matrix.cramer Mᵀ v = 0 := by
    funext x
    have h1 : Mᵀ.updateCol x v = (B.submatrix (Function.update e x r) e)ᵀ := by
      ext a b
      by_cases hb : b = x
      · subst hb; simp [Matrix.updateCol_apply, v]
      · simp [Matrix.updateCol_apply, hb, M, Function.update_of_ne hb]
    rw [Matrix.cramer_apply, h1, Matrix.det_transpose]
    exact det_submatrix_eq_zero B S hA _ x (by simpa using hr)
  have hv : Mᵀ.det • v = 0 := by rw [← Matrix.mulVec_cramer, hcr, Matrix.mulVec_zero]
  have hv0 : v = 0 := by
    rcases smul_eq_zero.mp hv with h | h
    · rw [Matrix.det_transpose] at h; exact absurd h hS
    · exact h
  have hr' : c ∈ Set.range e := by rw [he, Finset.range_orderEmbOfFin]; exact hc
  obtain ⟨y, rfl⟩ := hr'
  exact congrFun hv0 y

/- English proof (translation)
Introduce `N j h g hj hh hg hdh hdg hμ`. Establish `huh : IsUnit h.det` using `isUnit_iff_ne_zero.mpr hdh`. Establish `hbd : IsBlockDiag j (h⁻¹ * g)` using `(hh.inv huh).mul hg`. Establish `hdet : (h⁻¹ * g).det ≠ 0`. Rewrite using `[Matrix.det_mul, Matrix.det_nonsing_inv]`.

Conclude with `mul_ne_zero (by simpa using hdh) hdg`. Establish `hstep : ∀ i : Fin N, IsProperStep N j i → ∀ r c : Fin N, r ∉ stepCols N j i → c ∈ stepCols N j i → (h⁻¹ * g) r c = 0`. Introduce `i hi r c hr hc`. Take `⟨μ, hm⟩` from `hμ i hi`. Use `eq_zero_of_minors _ hdet _ (fun I hI => ?_) r c hr hc` and prove the remaining obligations.

Establish `h1 : minorIJ (h⁻¹ * g) I (stepCols N j i) = μ * minorIJ (h⁻¹ * h) I (stepCols N j i)`. Rewrite using `[minorIJ_mul, minorIJ_mul, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun I' _ => by rw [hm I']; ring`. Rewrite using `[h1, Matrix.nonsing_inv_mul _ huh, minorIJ_one_of_ne hI, mul_zero]`. Introduce `r s hrs`.

Establish `hsr : (s : ℕ) < r` using `hrs`. Establish `hrN` using `r.2`. Distinguish the cases in `hb : ((r : ℕ) < N - j ↔ (s : ℕ) < N - j)`. Distinguish the cases in `hω : (r : ℕ) < N - j`. Establish `hi : (s : ℕ) + j < N` using `by omega`.

Use `hstep ⟨(s : ℕ) + j, hi⟩ ⟨?_, ?_⟩ r s ?_ ?_` and prove the remaining obligations. Simplify using `only`. Use linear arithmetic over natural numbers and integers. Simplify using `only`. Use linear arithmetic over natural numbers and integers.

Simplify using `only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]`. Rewrite using `[if_neg (by omega)]; omega`. Simplify using `only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]`. Rewrite using `[if_neg (by omega)]; omega`. Establish `hs' : N - j ≤ (s : ℕ)`.

Assume the negation of the conclusion as `hc; exact hω (hb.mpr (by omega))`. Establish `hi : (s : ℕ) - (N - j) < N` using `by omega`. Use `hstep ⟨(s : ℕ) - (N - j), hi⟩ ⟨?_, ?_⟩ r s ?_ ?_` and prove the remaining obligations. Simplify using `only`. Use linear arithmetic over natural numbers and integers.

Simplify using `only`. Use linear arithmetic over natural numbers and integers. Simplify using `only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]`. Rewrite using `[if_pos (by omega)]; omega`. Simplify using `only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]`.

Rewrite using `[if_pos (by omega)]; omega`. Conclude with `hbd r s hb`.
-/
theorem triangular_of_minors_proportional : ∀ (N j : ℕ) (h g : Matrix (Fin N) (Fin N) ℂ), j ≤ N → IsBlockDiag j h →
    IsBlockDiag j g → h.det ≠ 0 → g.det ≠ 0 →
    (∀ i : Fin N, IsProperStep N j i → ∃ μ : ℂ, ∀ I, minorIJ g I (stepCols N j i) = μ * minorIJ h I (stepCols N j i)) →
    (h⁻¹ * g).BlockTriangular id := by
  intro N j h g hj hh hg hdh hdg hμ
  have huh : IsUnit h.det := isUnit_iff_ne_zero.mpr hdh
  have hbd : IsBlockDiag j (h⁻¹ * g) := (hh.inv huh).mul hg
  have hdet : (h⁻¹ * g).det ≠ 0 := by
    rw [Matrix.det_mul, Matrix.det_nonsing_inv]
    exact mul_ne_zero (by simpa using hdh) hdg
  have hstep : ∀ i : Fin N, IsProperStep N j i → ∀ r c : Fin N, r ∉ stepCols N j i → c ∈ stepCols N j i →
      (h⁻¹ * g) r c = 0 := by
    intro i hi r c hr hc
    obtain ⟨μ, hm⟩ := hμ i hi
    refine eq_zero_of_minors _ hdet _ (fun I hI => ?_) r c hr hc
    have h1 : minorIJ (h⁻¹ * g) I (stepCols N j i) =
        μ * minorIJ (h⁻¹ * h) I (stepCols N j i) := by
      rw [minorIJ_mul, minorIJ_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun I' _ => by rw [hm I']; ring
    rw [h1, Matrix.nonsing_inv_mul _ huh, minorIJ_one_of_ne hI, mul_zero]
  intro r s hrs
  have hsr : (s : ℕ) < r := hrs
  have hrN := r.2
  by_cases hb : ((r : ℕ) < N - j ↔ (s : ℕ) < N - j)
  · by_cases hω : (r : ℕ) < N - j
    · have hi : (s : ℕ) + j < N := by omega
      refine hstep ⟨(s : ℕ) + j, hi⟩ ⟨?_, ?_⟩ r s ?_ ?_
      · simp only; omega
      · simp only; omega
      · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [if_neg (by omega)]; omega
      · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [if_neg (by omega)]; omega
    · have hs' : N - j ≤ (s : ℕ) := by
        by_contra hc; exact hω (hb.mpr (by omega))
      have hi : (s : ℕ) - (N - j) < N := by omega
      refine hstep ⟨(s : ℕ) - (N - j), hi⟩ ⟨?_, ?_⟩ r s ?_ ?_
      · simp only; omega
      · simp only; omega
      · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [if_pos (by omega)]; omega
      · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [if_pos (by omega)]; omega
  · exact hbd r s hb

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.TriStep
