import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MajINonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus

namespace GlobalTheory.ThKTorus.IntegralOfAdic

/- English proof (translation)
Use `show evalV F v 0 = 0`. Conclude with `map_zero _`.
-/
theorem evFin_realAd (F : Type) [Field F] [NumberField F] (v : Pl F) (x : ℝ) :
    evFin F v (realAd F x) = 0 := by
  show evalV F v 0 = 0
  exact map_zero _

/- English proof (translation)
Rewrite using `[tAd, map_add, evFin_realAd, map_one, add_zero]`.
-/
theorem evFin_tAd (F : Type) [Field F] [NumberField F] (v : Pl F) (s : ℝ) :
    evFin F v (tAd F s) = 1 := by
  rw [tAd, map_add, evFin_realAd, map_one, add_zero]

/- English proof (translation)
Establish `key : ∀ v : Pl F, v.valuation F ((m : F) * ξ j) ≤ 1`. Introduce `v`. Establish `hv` using `h v`. Establish `e : evFin F v ((m : AF F) * blkScale blk t (fun j => algebraMap F (AF F) (ξ j)) j) = algebraMap F (Fv F v) ((m : F) * ξ j)`. Simplify using `only [blkScale, map_mul, map_natCast, map_prod, AlgHom.commutes]`.

Establish `: ∀ i, evFin F v (if j ∈ blk i then tAd F (t i) else 1) = 1`. Introduce `i`. Use `split_ifs`. Conclude with `evFin_tAd F v _`. Conclude with `map_one _`.

Simplify using `only [this, Finset.prod_const_one, one_mul]`. Rewrite `hv` using `[e]`. Rewrite `hv` using `[HeightOneSpectrum.mem_adicCompletionIntegers]`. Rewrite using `[← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']`. Conclude with `hv`.

Take `⟨y, hy⟩` from `HeightOneSpectrum.mem_integers_of_valuation_le_one F _ key`. Rewrite using `[← hy]`. Conclude with `(y.isIntegral_coe)`.
-/
theorem integral_of_evFin_mem (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ] [DecidableEq κ] {q : ℕ}
    (blk : Fin q → Finset κ) (t : Fin q → ℝ) (m : ℕ) (ξ : κ → F) (j : κ)
    (h : ∀ v : Pl F, evFin F v ((m : AF F) * blkScale blk t (fun j => algebraMap F (AF F) (ξ j)) j) ∈ v.adicCompletionIntegers F) :
    IsIntegral ℤ ((m : F) * ξ j) := by
  have key : ∀ v : Pl F, v.valuation F ((m : F) * ξ j) ≤ 1 := by
    intro v
    have hv := h v
    have e : evFin F v ((m : AF F) * blkScale blk t (fun j => algebraMap F (AF F) (ξ j)) j)
        = algebraMap F (Fv F v) ((m : F) * ξ j) := by
      simp only [blkScale, map_mul, map_natCast, map_prod, AlgHom.commutes]
      have : ∀ i, evFin F v (if j ∈ blk i then tAd F (t i) else 1) = 1 := by
        intro i; split_ifs
        · exact evFin_tAd F v _
        · exact map_one _
      simp only [this, Finset.prod_const_one, one_mul]
    rw [e] at hv
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hv
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact hv
  obtain ⟨y, hy⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F _ key
  rw [← hy]
  exact (y.isIntegral_coe)

end GlobalTheory.ThKTorus.IntegralOfAdic
