import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModModT
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsParamFunOne

open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio

open scoped Matrix ComplexOrder

namespace GlobalTheory.NormRatio

/- English proof (translation)
Unfold `Formalism.BasicNotions.TH.gramAt`. Rewrite using `[h]`. Conclude with `Matrix.map_one _ (map_zero _) (map_one _)`.
-/
theorem gramAt_eq_one_of_gram {D : D7} (V : HSp D) (h : V.gram = 1) (τ : D.what₂.Tau) : gramAt D V τ = 1 := by
  unfold Formalism.BasicNotions.TH.gramAt
  rw [h]
  exact Matrix.map_one _ (map_zero _) (map_one _)

/- English proof (translation)
Take `⟨e, P, hP⟩` from `hV τ`. Establish `h1 : (V.gram.map τ).reindex e e = 1`. Rewrite using `[hg, Matrix.map_one _ (map_zero τ) (map_one τ)]`. Conclude with `Matrix.submatrix_one_equiv _`. Rewrite `hP` using `[h1, Matrix.mul_one]`.

Establish `hP' : (P.1)ᴴ * P.1 = Formalism.UG.Jpq (V.sig τ).1 (V.sig τ).2` using `hP`. Assume the negation of the conclusion as `hq`. Set `k : Fin (V.sig τ).2` to `⟨0, Nat.pos_of_ne_zero hq⟩`. Establish `hk` using `congrArg (fun M => (M (Sum.inr k) (Sum.inr k)).re) hP'`. Simplify using `only [Formalism.UG.Jpq, Matrix.fromBlocks_apply₂₂, Matrix.neg_apply, Matrix.one_apply_eq, Complex.neg_re, Complex.one_re] at hk`.

Establish `: 0 ≤ (((P.1)ᴴ * P.1) (Sum.inr k) (Sum.inr k)).re`. Rewrite using `[Matrix.mul_apply, Complex.re_sum]`. Conclude with `Finset.sum_nonneg fun l _ => by`. Rewrite using `[Matrix.conjTranspose_apply, Complex.star_def, ← Complex.normSq_eq_conj_mul_self]`. Conclude with `Complex.normSq_nonneg _`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sig_snd_eq_zero_of_gram {D : D7} {V : HSp D} (hg : V.gram = 1) (hV : V.SigOK) (τ : D.host.E →+* ℂ) :
    (V.sig τ).2 = 0 := by
  obtain ⟨e, P, hP⟩ := hV τ
  have h1 : (V.gram.map τ).reindex e e = 1 := by
    rw [hg, Matrix.map_one _ (map_zero τ) (map_one τ)]; exact Matrix.submatrix_one_equiv _
  rw [h1, Matrix.mul_one] at hP
  have hP' : (P.1)ᴴ * P.1 = Formalism.UG.Jpq (V.sig τ).1 (V.sig τ).2 := hP
  by_contra hq
  let k : Fin (V.sig τ).2 := ⟨0, Nat.pos_of_ne_zero hq⟩
  have hk := congrArg (fun M => (M (Sum.inr k) (Sum.inr k)).re) hP'
  simp only [Formalism.UG.Jpq, Matrix.fromBlocks_apply₂₂, Matrix.neg_apply, Matrix.one_apply_eq, Complex.neg_re,
    Complex.one_re] at hk
  have : 0 ≤ (((P.1)ᴴ * P.1) (Sum.inr k) (Sum.inr k)).re := by
    rw [Matrix.mul_apply, Complex.re_sum]
    exact Finset.sum_nonneg fun l _ => by
      rw [Matrix.conjTranspose_apply, Complex.star_def, ← Complex.normSq_eq_conj_mul_self]; exact Complex.normSq_nonneg _
  linarith

/- English proof (translation)
Introduce `D cc δ t0 Q P X hX h1 h2`. Take `⟨hF, hW⟩` from `hX`. Establish `gA` using `gramAt_eq_one_of_gram X.A hF.gramA`. Establish `gB` using `gramAt_eq_one_of_gram X.B hF.gramB`. Establish `hI : ∀ k : ℕ, IsCartanInv (1 : Matrix (Fin k) (Fin k) ℂ) 1` using `fun k => ⟨by simp, by simp, by simpa using Matrix.PosDef.one⟩`.

Establish `hA : X.A.SigOK` using `hF.defA.1`. Establish `hq` using `sig_snd_eq_zero_of_gram hF.gramA hA`. Take `⟨cA, hc⟩` from `GlobalTheory.Cusp.exists_isCartanFrame X.A hA`. Take `⟨ν, 𝓕, hν⟩` from `GlobalTheory.MixModel.exists_isCovolOne D X.B.rank X.A.rank`. Establish `hone : ∀ τ, compAt X.θ τ (1 : GL (Fin X.A.rank) (AE D)).1 = 1` using `fun τ => by`.

Conclude with `Matrix.map_one ((X.θ τ).comp (infPart D)) (map_zero _) (map_one _)`. Establish `rA` using `X.rkA`. Establish `rB` using `X.rkB`. Use `⟨cA, 1, ν, 𝓕, ⟨by omega, by omega, by omega, hW.inf, hA, hc, fun τ => ?_, fun τ => ?_, fun τ => ?_⟩, (GlobalTheory.Doubling.isMaj_iff hW.inf).2 fun τ => ⟨fun _ => true, ?_⟩, fun τ => ?_, hW.weil, hν⟩` and prove the remaining obligations. Rewrite using `[gA]`.

Conclude with `hI _`. Rewrite using `[gB]`. Conclude with `hI _`. Establish `hJ : Formalism.UG.Jpq (X.A.sig (tauE D τ)).1 (X.A.sig (tauE D τ)).2 = 1`. Establish `: IsEmpty (Fin (X.A.sig (tauE D τ)).2)` using `by rw [hq]; infer_instance`.

Rewrite using `[Formalism.UG.Jpq, ← Matrix.fromBlocks_one]`. Use `congr 1`. Conclude with `Subsingleton.elim _ _`. Rewrite using `[hJ]`. Simplify using the standard rewrite rules.

Rewrite using `[hone, gA]`. Simplify using the standard rewrite rules. Rewrite using `[hone, gA]`. Simplify using the standard rewrite rules.
-/
theorem exists_ipPair_one : ∀ {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} (P : Pair D cc δ t0 Q) (X : Data P), IsDict P X → 1 ≤ P.a → P.a < P.d →
  ∃ (cA : GlobalTheory.Mem.Th.CptF X.A) (a : GL (Fin X.A.rank) (AE D)) (ν : Measure (WO X.A X.B)) (𝓕 : Set (WO X.A X.B)),
    GlobalTheory.Core.Rk.IP.Pair X.ψ X.θ X.A X.B X.χA X.χB (fun _ => 1) (fun _ => 1) (P.d - P.a) cA a X.om ν 𝓕 := by
  intro D cc δ t0 Q P X hX h1 h2
  obtain ⟨hF, hW⟩ := hX
  have gA := gramAt_eq_one_of_gram X.A hF.gramA
  have gB := gramAt_eq_one_of_gram X.B hF.gramB
  have hI : ∀ k : ℕ, IsCartanInv (1 : Matrix (Fin k) (Fin k) ℂ) 1 := fun k =>
    ⟨by simp, by simp, by simpa using Matrix.PosDef.one⟩
  have hA : X.A.SigOK := hF.defA.1
  have hq := sig_snd_eq_zero_of_gram hF.gramA hA
  obtain ⟨cA, hc⟩ := GlobalTheory.Cusp.exists_isCartanFrame X.A hA
  obtain ⟨ν, 𝓕, hν⟩ := GlobalTheory.MixModel.exists_isCovolOne D X.B.rank X.A.rank
  have hone : ∀ τ, compAt X.θ τ (1 : GL (Fin X.A.rank) (AE D)).1 = 1 := fun τ => by
    exact Matrix.map_one ((X.θ τ).comp (infPart D)) (map_zero _) (map_one _)
  have rA := X.rkA
  have rB := X.rkB
  refine ⟨cA, 1, ν, 𝓕, ⟨by omega, by omega, by omega, hW.inf, hA, hc, fun τ => ?_, fun τ => ?_, fun τ => ?_⟩,
    (GlobalTheory.Doubling.isMaj_iff hW.inf).2 fun τ => ⟨fun _ => true, ?_⟩, fun τ => ?_, hW.weil, hν⟩
  · rw [gA]; exact hI _
  · rw [gB]; exact hI _
  · have hJ : Formalism.UG.Jpq (X.A.sig (tauE D τ)).1 (X.A.sig (tauE D τ)).2 = 1 := by
      have : IsEmpty (Fin (X.A.sig (tauE D τ)).2) := by rw [hq]; infer_instance
      rw [Formalism.UG.Jpq, ← Matrix.fromBlocks_one]
      congr 1
      exact Subsingleton.elim _ _
    rw [hJ]; simp
  · rw [hone, gA]; simp
  · rw [hone, gA]; simp

end GlobalTheory.NormRatio
