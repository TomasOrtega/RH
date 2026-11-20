import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedCechToCatCochainsOneApplyValueAtSubset
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ModelS.FMem

variable {n : ℕ}

/- English proof (translation)
The claim follows from `contDiff_apply_apply ℝ ℂ a b`.
-/
theorem contDiff_entry (a b : Fin n) : ContDiff ℝ ∞ (fun g : Mat n => g a b) :=
  contDiff_apply_apply ℝ ℂ a b

/- English proof (translation)
Simplify using `only [Matrix.det_apply']`. Use `ContDiff.sum fun σ _ => contDiff_const.mul ?_` and prove the remaining obligations. Conclude with `contDiff_prod fun i _ => h _ _`.
-/
theorem contDiff_det_of_entries {ι : Type} [Fintype ι] [DecidableEq ι] {M : Mat n → Matrix ι ι ℂ}
    (h : ∀ a b, ContDiff ℝ ∞ fun g => M g a b) : ContDiff ℝ ∞ fun g => (M g).det := by
  simp only [Matrix.det_apply']
  refine ContDiff.sum fun σ _ => contDiff_const.mul ?_
  exact contDiff_prod fun i _ => h _ _

/- English proof (translation)
The claim follows from `contDiff_det_of_entries fun _ _ => contDiff_entry _ _`.
-/
theorem contDiff_lm (j : Fin n) : ContDiff ℝ ∞ (lm j) :=
  contDiff_det_of_entries fun _ _ => contDiff_entry _ _

/- English proof (translation)
Use `contDiff_det_of_entries fun a b => ?_` and prove the remaining obligations. Simplify using `only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply, id]`. Apply the tactic sequence `refine ContDiff.sum fun k _ => (contDiff_entry _ _).mul ?_`. Apply the tactic sequence `exact Complex.conjCLE.contDiff.comp (contDiff_entry _ _)`.
-/
theorem contDiff_gm (j : Fin n) : ContDiff ℝ ∞ (gm j) := by
  refine contDiff_det_of_entries fun a b => ?_
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply, id]
  refine ContDiff.sum fun k _ => (contDiff_entry _ _).mul ?_
  exact Complex.conjCLE.contDiff.comp (contDiff_entry _ _)

/- English proof (translation)
Take `⟨k, rfl | rfl⟩` from `m.eq_nat_or_neg`. Simplify `hf.pow k` using `only [zpow_natCast]`. Simplify using `only [_root_.zpow_neg, zpow_natCast]`. Conclude with `(hf.pow k).inv fun x hx => pow_ne_zero k (h x hx)`.
-/
theorem zpow_contDiffOn {f : Mat n → ℂ} {s : Set (Mat n)} (hf : ContDiffOn ℝ ∞ f s)
    (h : ∀ x ∈ s, f x ≠ 0) (m : ℤ) : ContDiffOn ℝ ∞ (fun x => f x ^ m) s := by
  obtain ⟨k, rfl | rfl⟩ := m.eq_nat_or_neg
  · simpa only [zpow_natCast] using hf.pow k
  · simp only [_root_.zpow_neg, zpow_natCast]
    exact (hf.pow k).inv fun x hx => pow_ne_zero k (h x hx)

open scoped ComplexOrder in

/- English proof (translation)
Introduce `h0`. Take `⟨v, hv, hAv⟩` from `Matrix.exists_mulVec_eq_zero_iff.mpr h0`. Establish `h1 : (g.submatrix (ini j) id)ᴴ *ᵥ v = 0` using `(Matrix.self_mul_conjTranspose_mulVec_eq_zero _ v).mp hAv`. Establish `hu : IsUnit g.det` using `isUnit_iff_ne_zero.mpr hg`. Establish `hAB : g.submatrix (ini j) id * (g⁻¹).submatrix id (ini j) = 1`.

Establish `h2` using `Matrix.submatrix_mul g g⁻¹ (ini j) id (ini j) Function.bijective_id`. Establish `hi : Function.Injective (ini j)` using `Fin.castLE_injective _`. Rewrite `h2` using `[Matrix.mul_nonsing_inv g hu, Matrix.submatrix_one _ hi]`. Conclude with `h2.symm`. Establish `hBA : ((g⁻¹).submatrix id (ini j))ᴴ * (g.submatrix (ini j) id)ᴴ = 1`.

Rewrite using `[← Matrix.conjTranspose_mul, hAB, Matrix.conjTranspose_one]`. Apply `hv` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hBA, Matrix.one_mulVec]`. Use `_ = ((g⁻¹).submatrix id (ini j))ᴴ *ᵥ ((g.submatrix (ini j) id)ᴴ *ᵥ v) := (Matrix.mulVec_mulVec _ _ _).symm`.

Use `_ = 0 := by rw [h1, Matrix.mulVec_zero]`.
-/
theorem gm_ne_zero (j : Fin n) {g : Mat n} (hg : g ∈ GLs n) : gm j g ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have h1 : (g.submatrix (ini j) id)ᴴ *ᵥ v = 0 :=
    (Matrix.self_mul_conjTranspose_mulVec_eq_zero _ v).mp hAv
  have hu : IsUnit g.det := isUnit_iff_ne_zero.mpr hg
  have hAB : g.submatrix (ini j) id * (g⁻¹).submatrix id (ini j) = 1 := by
    have h2 := Matrix.submatrix_mul g g⁻¹ (ini j) id (ini j) Function.bijective_id
    have hi : Function.Injective (ini j) := Fin.castLE_injective _
    rw [Matrix.mul_nonsing_inv g hu, Matrix.submatrix_one _ hi] at h2
    exact h2.symm
  have hBA : ((g⁻¹).submatrix id (ini j))ᴴ * (g.submatrix (ini j) id)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hAB, Matrix.conjTranspose_one]
  apply hv
  calc v = (((g⁻¹).submatrix id (ini j))ᴴ * (g.submatrix (ini j) id)ᴴ) *ᵥ v := by
        rw [hBA, Matrix.one_mulVec]
    _ = ((g⁻¹).submatrix id (ini j))ᴴ *ᵥ ((g.submatrix (ini j) id)ᴴ *ᵥ v) :=
        (Matrix.mulVec_mulVec _ _ _).symm
    _ = 0 := by rw [h1, Matrix.mulVec_zero]

/- English proof (translation)
Introduce `a b hab`. Establish `h1` using `hlam hab`. Establish `h2 : lev a ≤ lev b` using `hlev hab`. Establish `c1 : (univ.filter fun c => lev b < lev c).card ≤ (univ.filter fun c => lev a < lev c).card` using `Finset.card_le_card fun c hc => by`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢`.

Use linear arithmetic over natural numbers and integers. Establish `c2 : (univ.filter fun c => lev c < lev a).card ≤ (univ.filter fun c => lev c < lev b).card` using `Finset.card_le_card fun c hc => by`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢`. Use linear arithmetic over natural numbers and integers. Simplify using `only [muZ]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem muZ_antitone {lam : Fin n → ℤ} {lev : Fin n → ℕ} (hlam : Antitone lam) (hlev : Monotone lev) :
    Antitone (muZ lam lev) := by
  intro a b hab
  have h1 := hlam hab
  have h2 : lev a ≤ lev b := hlev hab
  have c1 : (univ.filter fun c => lev b < lev c).card ≤ (univ.filter fun c => lev a < lev c).card :=
    Finset.card_le_card fun c hc => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      omega
  have c2 : (univ.filter fun c => lev c < lev a).card ≤ (univ.filter fun c => lev c < lev b).card :=
    Finset.card_le_card fun c hc => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      omega
  simp only [muZ]
  omega

/- English proof (translation)
Establish `h1 : v ⟨j + 1, hj⟩ ≤ v j` using `h (Fin.le_def.mpr (Nat.le_succ _))`. Unfold `dif`. Rewrite using `[dif_pos hj]`. Use linear arithmetic over natural numbers and integers.
-/
theorem dif_nonneg_of_antitone {v : Fin n → ℤ} (h : Antitone v) (j : Fin n) (hj : (j : ℕ) + 1 < n) :
    0 ≤ dif v j := by
  have h1 : v ⟨j + 1, hj⟩ ≤ v j := h (Fin.le_def.mpr (Nat.le_succ _))
  unfold dif
  rw [dif_pos hj]
  omega

/- English proof (translation)
Establish `hb : Function.Bijective (ini j)` using `(Fintype.bijective_iff_injective_and_card _).mpr ⟨Fin.castLE_injective _, by`. Use `j.isLt` as an intermediate fact. Simplify using `only [Fintype.card_fin]`. Use the proof step `omega⟩`. Establish `e : lm j g = g.det` using `Matrix.det_submatrix_equiv_self (Equiv.ofBijective _ hb) g`.

Rewrite using `[e]`. Conclude with `hg`.
-/
theorem lm_ne_zero (j : Fin n) (hj : ¬ (j : ℕ) + 1 < n) {g : Mat n} (hg : g ∈ GLs n) : lm j g ≠ 0 := by
  have hb : Function.Bijective (ini j) :=
    (Fintype.bijective_iff_injective_and_card _).mpr ⟨Fin.castLE_injective _, by
      have := j.isLt
      simp only [Fintype.card_fin]
      omega⟩
  have e : lm j g = g.det := Matrix.det_submatrix_equiv_self (Equiv.ofBijective _ hb) g
  rw [e]
  exact hg

end GlobalTheory.CompanionTheory.ModelS.FMem

namespace GlobalTheory.CompanionTheory.ModelS

open FMem in

/- English proof (translation)
Introduce `n lam hlam lev hlev`. Use `⟨?_, fun g hg => Set.indicator_of_notMem hg _⟩` and prove the remaining obligations. Establish `key : ContDiffOn ℝ ∞ (fun g => ∏ j, lm j g ^ dif (muZ lam lev) j * gm j g ^ dif (yZ lam lev) j) (GLs n)`. Use `contDiffOn_prod fun j _ => ContDiffOn.mul ?_ (zpow_contDiffOn (contDiff_gm j).contDiffOn (fun g hg => gm_ne_zero j hg) _)` and prove the remaining obligations. Distinguish the cases in `hj : (j : ℕ) + 1 < n`.

Take `⟨k, hk⟩` from `Int.eq_ofNat_of_zero_le (dif_nonneg_of_antitone (muZ_antitone hlam hlev.1) j hj)`. Simplify using `only [hk, zpow_natCast]`. Conclude with `((contDiff_lm j).pow k).contDiffOn`. Conclude with `zpow_contDiffOn (contDiff_lm j).contDiffOn (fun g hg => lm_ne_zero j hj hg) _`. Conclude with `key.congr fun g hg => Set.indicator_of_mem hg _`.
-/
theorem fRaw_mem_SmF : ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ lev : Fin n → ℕ, IsLev lam lev →
    GlobalTheory.CompanionTheory.ModelS.fRaw lam lev ∈ GlobalTheory.CompanionTheory.ModelS.SmF n := by
  intro n lam hlam lev hlev
  refine ⟨?_, fun g hg => Set.indicator_of_notMem hg _⟩
  have key : ContDiffOn ℝ ∞
      (fun g => ∏ j, lm j g ^ dif (muZ lam lev) j * gm j g ^ dif (yZ lam lev) j) (GLs n) := by
    refine contDiffOn_prod fun j _ => ContDiffOn.mul ?_
      (zpow_contDiffOn (contDiff_gm j).contDiffOn (fun g hg => gm_ne_zero j hg) _)
    by_cases hj : (j : ℕ) + 1 < n
    · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (dif_nonneg_of_antitone (muZ_antitone hlam hlev.1) j hj)
      simp only [hk, zpow_natCast]
      exact ((contDiff_lm j).pow k).contDiffOn
    · exact zpow_contDiffOn (contDiff_lm j).contDiffOn (fun g hg => lm_ne_zero j hj hg) _
  exact key.congr fun g hg => Set.indicator_of_mem hg _

end GlobalTheory.CompanionTheory.ModelS
