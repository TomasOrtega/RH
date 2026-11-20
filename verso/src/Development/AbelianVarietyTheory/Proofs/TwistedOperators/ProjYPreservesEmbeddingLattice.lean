import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin

variable {D : D7}

/- English proof (translation)
Use extensionality with `i p`. Simplify using `only [colsOf, Matrix.mul_apply, Matrix.of_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Conclude with `mul_comm _ _`.
-/
theorem colsOf_eq_mul {n c k : ℕ} (a : Matrix (Fin n) (Fin c) D.host.E) (f : Fin k → Fin c) (s : Fin k → D.host.E) :
    colsOf a f s = a * Matrix.of (fun q p => if q = f p then s p else 0) := by
  ext i p
  simp only [colsOf, Matrix.mul_apply, Matrix.of_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact mul_comm _ _

/- English proof (translation)
Use `p.2` as an intermediate fact. Use `r.2` as an intermediate fact. Unfold `antiDiagonalSignGramMatrix`. Simplify using `only [Fin.ext_iff, Fin.val_rev, Fin.val_castLE]`. Apply the tactic sequence `split_ifs <;> first | rfl | omega`.
-/
theorem antiDiagonalGram_neg_one_castLE_row {c ρ : ℕ} (h : 2 * ρ ≤ c) (p : Fin ρ) (r : Fin c) :
    antiDiagonalSignGramMatrix c (-1 : D.host.E) (Fin.castLE (by omega) p) r = if r = (Fin.castLE (by omega) p : Fin c).rev then 1 else 0 := by
  have := p.2; have := r.2
  unfold antiDiagonalSignGramMatrix
  simp only [Fin.ext_iff, Fin.val_rev, Fin.val_castLE]
  split_ifs <;> first | rfl | omega

/- English proof (translation)
Introduce `D A B B₀ c ρ a d ⟨h, he, s, he'⟩ Λ 𝔟 v ⟨y, hy, u, hu, hv⟩`. Substitute `hv` using the available equality. Use `set f : Fin ρ → Fin c := Fin.castLE (by omega) with hf`. Use `set t : Fin ρ → D.host.E := fun p => (-D.host.xi0) ^ (p.1 + 1) with ht`. Use `set Pe : Matrix (Fin c) (Fin ρ) D.host.E := Matrix.of (fun q p => if q = f p then t p else 0) with hPe`.

Use `set Pe' : Matrix (Fin c) (Fin ρ) D.host.E := Matrix.of (fun q p => if q = (f p).rev then s p else 0) with hPe'`. Establish `hE : d.e = a.a * Pe` using `by rw [he, colsOf_eq_mul]`. Establish `hE' : d.e' = a.a * Pe'` using `by rw [he', colsOf_eq_mul]`. Establish `hG : B.gramᴴ = B.gram` using `GlobalTheory.MixModel.gram_conjTranspose B`. Establish `hperp : (frameMat B A a.ι)ᴴ * B.gram * a.a = 0` using `a.perp`.

Establish `hgram : a.aᴴ * B.gram * a.a = antiDiagonalSignGramMatrix c (-1)` using `a.gram`. Establish `hperp' : a.aᴴ * B.gram * frameMat B A a.ι = 0`. Use `congrArg Matrix.conjTranspose hperp` as an intermediate fact. Rewrite `this` using `[conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hG, conjTranspose_zero, ← Matrix.mul_assoc]`. Then use the resulting hypothesis. Establish `hQF : d.qY * frameMat B A a.ι = 0`.

Rewrite using `[HypDec.qY, hE, conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc a.aᴴ, hperp', Matrix.mul_zero]`. Establish `hQA : d.qY * a.a = Matrix.of (fun p r => if r = (f p).rev then star (t p) else 0)`. Rewrite using `[HypDec.qY, hE, conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc a.aᴴ, hgram]`. Use extensionality with `p r`. Simplify using `only [Matrix.mul_apply, Matrix.conjTranspose_apply, hPe, Matrix.of_apply, apply_ite star, star_zero, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, hf, antiDiagonalGram_neg_one_castLE_row h, mul_ite, mul_one, mul_zero]`.

Establish `hS : ∀ p, s p * star (t p) = 1`. Introduce `p`. Establish `h1 : d.eᴴ * B.gram * d.e' = 1`. Use `congrArg Matrix.conjTranspose d.e'e` as an intermediate fact. Rewrite `this` using `[conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hG, conjTranspose_one, ← Matrix.mul_assoc]`. Then use the resulting hypothesis.

Establish `h2 : (d.qY * a.a * Pe') p p = 1`. Rewrite using `[Matrix.mul_assoc, ← hE', HypDec.qY, h1, Matrix.one_apply_eq]`. Rewrite `h2` using `[hQA]`. Simplify using `only [Matrix.mul_apply, hPe', Matrix.of_apply, ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true] at h2`. Rewrite using `[mul_comm]`.

Conclude with `h2`. Use `⟨0, Λ.zero_mem, fun q => ∑ p, if q = (f p).rev then u q else 0, fun q => ?_, ?_⟩` and prove the remaining obligations. Use `Submodule.sum_mem _ fun p _ => ?_ split_ifs` and prove the remaining obligations. Conclude with `hu q`. Conclude with `Submodule.zero_mem _`.

Rewrite using `[mulVec_zero, zero_add, ← mulVec_mulVec, mulVec_add, mulVec_mulVec, mulVec_mulVec, hQF, zero_mulVec, zero_add, mulVec_mulVec, hQA, hE', Matrix.mul_assoc, ← mulVec_mulVec]`. Use `congr 1`. Use function extensionality and compare the values at `q`. Simplify using `only [mulVec, dotProduct, Matrix.mul_apply, hPe', Matrix.of_apply, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Distinguish the cases in `hq : q = (f p).rev`. Substitute `hq` using the available equality. Simplify using `only [if_true, mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, hS p, one_mul]`. Simplify using `only [hq, if_false, zero_mul, Finset.sum_const_zero]`.
-/
theorem projY_mem_lat : ∀ {D : D7} {A B B₀ : HSp D} {c ρ : ℕ} (a : HermitianOrthogonalExtensionData A B c (-1)) (d : HypDec B B₀ ρ), IsAuxiliaryVectorWittDec a d → ∀ (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (v : Fin B.rank → D.host.E), v ∈ a.lat Λ 𝔟 → (d.e' * d.qY) *ᵥ v ∈ a.lat Λ 𝔟 := by
  intro D A B B₀ c ρ a d ⟨h, he, s, he'⟩ Λ 𝔟 v ⟨y, hy, u, hu, hv⟩
  subst hv
  set f : Fin ρ → Fin c := Fin.castLE (by omega) with hf
  set t : Fin ρ → D.host.E := fun p => (-D.host.xi0) ^ (p.1 + 1) with ht
  set Pe : Matrix (Fin c) (Fin ρ) D.host.E := Matrix.of (fun q p => if q = f p then t p else 0) with hPe
  set Pe' : Matrix (Fin c) (Fin ρ) D.host.E := Matrix.of (fun q p => if q = (f p).rev then s p else 0) with hPe'
  have hE : d.e = a.a * Pe := by rw [he, colsOf_eq_mul]
  have hE' : d.e' = a.a * Pe' := by rw [he', colsOf_eq_mul]
  have hG : B.gramᴴ = B.gram := GlobalTheory.MixModel.gram_conjTranspose B
  have hperp : (frameMat B A a.ι)ᴴ * B.gram * a.a = 0 := a.perp
  have hgram : a.aᴴ * B.gram * a.a = antiDiagonalSignGramMatrix c (-1) := a.gram
  have hperp' : a.aᴴ * B.gram * frameMat B A a.ι = 0 := by
    have := congrArg Matrix.conjTranspose hperp
    rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hG, conjTranspose_zero, ← Matrix.mul_assoc] at this
  have hQF : d.qY * frameMat B A a.ι = 0 := by
    rw [HypDec.qY, hE, conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc a.aᴴ, hperp', Matrix.mul_zero]
  have hQA : d.qY * a.a = Matrix.of (fun p r => if r = (f p).rev then star (t p) else 0) := by
    rw [HypDec.qY, hE, conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc a.aᴴ, hgram]
    ext p r
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hPe, Matrix.of_apply, apply_ite star, star_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, hf, antiDiagonalGram_neg_one_castLE_row h, mul_ite, mul_one, mul_zero]
  have hS : ∀ p, s p * star (t p) = 1 := by
    intro p
    have h1 : d.eᴴ * B.gram * d.e' = 1 := by
      have := congrArg Matrix.conjTranspose d.e'e
      rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hG, conjTranspose_one, ← Matrix.mul_assoc] at this
    have h2 : (d.qY * a.a * Pe') p p = 1 := by
      rw [Matrix.mul_assoc, ← hE', HypDec.qY, h1, Matrix.one_apply_eq]
    rw [hQA] at h2
    simp only [Matrix.mul_apply, hPe', Matrix.of_apply, ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq,
      Finset.mem_univ, if_true] at h2
    rw [mul_comm]; exact h2
  refine ⟨0, Λ.zero_mem, fun q => ∑ p, if q = (f p).rev then u q else 0, fun q => ?_, ?_⟩
  · refine Submodule.sum_mem _ fun p _ => ?_
    split_ifs
    · exact hu q
    · exact Submodule.zero_mem _
  · rw [mulVec_zero, zero_add, ← mulVec_mulVec, mulVec_add, mulVec_mulVec, mulVec_mulVec, hQF, zero_mulVec, zero_add,
      mulVec_mulVec, hQA, hE', Matrix.mul_assoc, ← mulVec_mulVec]
    congr 1
    funext q
    simp only [mulVec, dotProduct, Matrix.mul_apply, hPe', Matrix.of_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases hq : q = (f p).rev
    · subst hq
      simp only [if_true, mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, hS p, one_mul]
    · simp only [hq, if_false, zero_mul, Finset.sum_const_zero]

end GlobalTheory.AscFin
