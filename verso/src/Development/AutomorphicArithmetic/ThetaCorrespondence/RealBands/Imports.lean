import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.DecaysZero

open MeasureTheory Filter Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.FlagMeas GlobalTheory.RealInd UpperTheory.Lit.Cusp
open GlobalTheory.Dec (IsHaarSub IsIsoC NW IsSqIntIrr)
open scoped Topology InnerProductSpace

/- English proof (translation)
Introduce `n ε j W hW`. Take `⟨P, h0, h1, h2⟩` from `GlobalTheory.RealIwasawa.exists_proj (W (Fin.last 1))`. Establish `hJ` using `Jm_mul_self ε`. Establish `hPP : P * P = P` using `Matrix.ext_iff_mulVec.2 fun y => by rw [← mulVec_mulVec, h2 _ (h1 y)]`. Establish `hi : P * Jm ε * P = 0` using `GlobalTheory.RealIwasawa.proj_iso hW h0 fun y => h1 y`.

Establish `key : ∀ r : ℝ, ∃ t : UJ ε, uMat t = GlobalTheory.IsoTorus.tor P (Jm ε * P * Jm ε) (Real.exp r) (Real.exp (-r))`. Introduce `r`. Use `set Q := Jm ε * P * Jm ε with hQ`. Establish `hQQ : Q * Q = Q`. Simplify using `only [hQ, mul_assoc]`.

Rewrite using `[← mul_assoc (Jm ε) (Jm ε), hJ, one_mul, ← mul_assoc P P, hPP]`. Establish `hPQ : P * Q = 0` using `by rw [hQ, ← mul_assoc, ← mul_assoc, hi, zero_mul]`. Establish `hQP : Q * P = 0` using `by rw [hQ, mul_assoc, mul_assoc, ← mul_assoc P, hi, mul_zero]`. Use `set c : ℂ := (Real.exp r : ℂ) with hc`. Use `set d : ℂ := (Real.exp (-r) : ℂ) with hd`.

Establish `hH : (GlobalTheory.IsoTorus.tor P Q c d)ᴴ = GlobalTheory.IsoTorus.tor P Q c d`. Simplify using `[GlobalTheory.IsoTorus.tor, hQ, h0, Jm_conjTranspose, hc, hd, mul_assoc, -Complex.ofReal_exp]`. Establish `hm : (GlobalTheory.IsoTorus.tor P Q c d)ᴴ * Jm ε * GlobalTheory.IsoTorus.tor P Q c d = Jm ε`. Establish `e : GlobalTheory.IsoTorus.tor P Q c d * Jm ε = Jm ε * GlobalTheory.IsoTorus.tor P Q d c`. Simplify using `only [GlobalTheory.IsoTorus.tor, hQ, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, mul_assoc, hJ, ← mul_assoc (Jm ε) (Jm ε)]`.

Normalize the expressions using the abelian group laws. Rewrite using `[hH, e, mul_assoc, GlobalTheory.IsoTorus.tor_tor hPP hQQ hPQ hQP, hc, hd, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Real.exp_add, ← Real.exp_add]`. Simplify using `[GlobalTheory.IsoTorus.tor_one]`. Take `⟨t, ht, -⟩` from `GlobalTheory.RealIwasawa.exists_uMat _ hm`. Conclude with `⟨t, ht⟩`.

Use `choose a ha using key`. Establish `hs : ∀ t, IsSplit ε W (fun _ => t) (a t)` using `fun t => by`. Use `isSplit_of_tor hW h0 h1 h2 (ha t) using 2 with i` and compare the differences between its conclusion and the goal. Rewrite using `[if_pos (Fin.le_last _)]`. Use `⟨a, ?_, fun s t => ?_, hs⟩` and prove the remaining obligations.

Use `(Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isInducing.continuous_iff.2 ?_` and prove the remaining obligations. Use `Continuous.congr (f := fun r : ℝ => GlobalTheory.IsoTorus.tor P (Jm ε * P * Jm ε) (Real.exp r) (Real.exp (-r))) ?_ fun r => (ha r).symm` and prove the remaining obligations. Unfold `GlobalTheory.IsoTorus.tor`. Use `fun_prop`. Conclude with `(existsUnique_isSplit hW (fun _ => s + t)).unique (hs _) ((hs s).mul (hs t))`.
-/
theorem UpperTheory.Lit.Cusp.exists_split :
    ∀ (n : ℕ) (ε : Fin n → Bool) (j : Fin 1 → ℕ) (W : Flag n 1), IsIsoFlag ε j W →
      ∃ a : ℝ → UJ ε, Continuous a ∧ (∀ s t, a (s + t) = a s * a t) ∧ ∀ t, IsSplit ε W (fun _ => t) (a t) := by
  intro n ε j W hW
  obtain ⟨P, h0, h1, h2⟩ := GlobalTheory.RealIwasawa.exists_proj (W (Fin.last 1))
  have hJ := Jm_mul_self ε
  have hPP : P * P = P := Matrix.ext_iff_mulVec.2 fun y => by rw [← mulVec_mulVec, h2 _ (h1 y)]
  have hi : P * Jm ε * P = 0 := GlobalTheory.RealIwasawa.proj_iso hW h0 fun y => h1 y
  have key : ∀ r : ℝ, ∃ t : UJ ε,
      uMat t = GlobalTheory.IsoTorus.tor P (Jm ε * P * Jm ε) (Real.exp r) (Real.exp (-r)) := by
    intro r
    set Q := Jm ε * P * Jm ε with hQ
    have hQQ : Q * Q = Q := by
      simp only [hQ, mul_assoc]; rw [← mul_assoc (Jm ε) (Jm ε), hJ, one_mul, ← mul_assoc P P, hPP]
    have hPQ : P * Q = 0 := by rw [hQ, ← mul_assoc, ← mul_assoc, hi, zero_mul]
    have hQP : Q * P = 0 := by rw [hQ, mul_assoc, mul_assoc, ← mul_assoc P, hi, mul_zero]
    set c : ℂ := (Real.exp r : ℂ) with hc
    set d : ℂ := (Real.exp (-r) : ℂ) with hd
    have hH : (GlobalTheory.IsoTorus.tor P Q c d)ᴴ = GlobalTheory.IsoTorus.tor P Q c d := by
      simp [GlobalTheory.IsoTorus.tor, hQ, h0, Jm_conjTranspose, hc, hd, mul_assoc, -Complex.ofReal_exp]
    have hm : (GlobalTheory.IsoTorus.tor P Q c d)ᴴ * Jm ε * GlobalTheory.IsoTorus.tor P Q c d = Jm ε := by
      have e : GlobalTheory.IsoTorus.tor P Q c d * Jm ε = Jm ε * GlobalTheory.IsoTorus.tor P Q d c := by
        simp only [GlobalTheory.IsoTorus.tor, hQ, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
          mul_assoc, hJ, ← mul_assoc (Jm ε) (Jm ε)]
        abel
      rw [hH, e, mul_assoc, GlobalTheory.IsoTorus.tor_tor hPP hQQ hPQ hQP, hc, hd, ← Complex.ofReal_mul,
        ← Complex.ofReal_mul, ← Real.exp_add, ← Real.exp_add]
      simp [GlobalTheory.IsoTorus.tor_one]
    obtain ⟨t, ht, -⟩ := GlobalTheory.RealIwasawa.exists_uMat _ hm
    exact ⟨t, ht⟩
  choose a ha using key
  have hs : ∀ t, IsSplit ε W (fun _ => t) (a t) := fun t => by
    convert isSplit_of_tor hW h0 h1 h2 (ha t) using 2 with i
    rw [if_pos (Fin.le_last _)]
  refine ⟨a, ?_, fun s t => ?_, hs⟩
  · refine (Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isInducing.continuous_iff.2 ?_
    refine Continuous.congr (f := fun r : ℝ => GlobalTheory.IsoTorus.tor P (Jm ε * P * Jm ε) (Real.exp r) (Real.exp (-r)))
      ?_ fun r => (ha r).symm
    unfold GlobalTheory.IsoTorus.tor
    fun_prop
  · exact (existsUnique_isSplit hW (fun _ => s + t)).unique (hs _) ((hs s).mul (hs t))
