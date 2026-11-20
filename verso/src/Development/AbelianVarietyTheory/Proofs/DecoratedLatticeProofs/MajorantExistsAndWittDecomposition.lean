import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankOrth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWittDecompositionIsotropicSplitUnipotent
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.EmbRelExistsUnique
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
noncomputable section

namespace GlobalTheory.Core.Rk.WittDec

variable {D : D7}

/- English proof (translation)
Use `h.2.1.fintype_card_le_finrank` as an intermediate fact. Simplify using `using this`.
-/
theorem isoFrame_le {W : HSp D} {r : ℕ} {C : Matrix (Fin W.rank) (Fin r) D.host.E} (h : IsIsoFrame W C) :
    r ≤ W.rank := by
  have := h.2.1.fintype_card_le_finrank
  simpa using this

/- English proof (translation)
Use `set M : Matrix (Fin W.rank) (Fin r ⊕ Fin s) D.host.E := Matrix.fromCols d.e (d.i₀ * C₀) with hM`. Establish `hG : (HSpace.gram W)ᴴ = HSpace.gram W` using `GlobalTheory.MixModel.gram_conjTranspose W`. Establish `hi₀e : d.eᴴ * HSpace.gram W * d.i₀ = 0`. Establish `h` using `congrArg Matrix.conjTranspose d.i₀e`. Simplify `h` using `[Matrix.conjTranspose_mul, hG, Matrix.mul_assoc]`.

Establish `he'i₀ : d.e'ᴴ * HSpace.gram W * d.i₀ = 0`. Establish `h` using `congrArg Matrix.conjTranspose d.i₀e'`. Simplify `h` using `[Matrix.conjTranspose_mul, hG, Matrix.mul_assoc]`. Establish `hC₀iso : C₀ᴴ * HSpace.gram W₀ * C₀ = 0` using `hC₀.2.2`. Establish `hiso : Mᴴ * HSpace.gram W * M = 0`.

Rewrite using `[hM, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols]`. Establish `h1 : d.eᴴ * HSpace.gram W * d.e = 0` using `d.ee`. Establish `h2 : d.eᴴ * HSpace.gram W * (d.i₀ * C₀) = 0` using `by rw [← Matrix.mul_assoc, hi₀e, Matrix.zero_mul]`. Establish `h3 : (d.i₀ * C₀)ᴴ * HSpace.gram W * d.e = 0`. Rewrite using `[Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc d.i₀ᴴ, d.i₀e, Matrix.mul_zero]`.

Establish `h4 : (d.i₀ * C₀)ᴴ * HSpace.gram W * (d.i₀ * C₀) = 0`. Rewrite using `[Matrix.conjTranspose_mul, show C₀ᴴ * d.i₀ᴴ * HSpace.gram W * (d.i₀ * C₀) = C₀ᴴ * (d.i₀ᴴ * HSpace.gram W * d.i₀) * C₀ by simp only [Matrix.mul_assoc], d.iso, hC₀iso]`. Rewrite using `[h1, h2, h3, h4, Matrix.fromBlocks_zero]`. Establish `hker : ∀ v, M *ᵥ v = 0 → v = 0`. Introduce `v hv`.

Rewrite `hv` using `[hM, Matrix.fromCols_mulVec]`. Establish `ha : v ∘ Sum.inl = 0`. Establish `h` using `congrArg (fun x => (d.e'ᴴ * HSpace.gram W) *ᵥ x) hv`. Simplify using `only [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_zero] at h`. Rewrite `h` using `[d.e'e, ← Matrix.mul_assoc, he'i₀, Matrix.zero_mul, Matrix.zero_mulVec, add_zero, Matrix.one_mulVec]`. Then use the resulting hypothesis.

Establish `hb' : d.i₀ *ᵥ (C₀ *ᵥ (v ∘ Sum.inr)) = 0`. Rewrite `hv` using `[ha, Matrix.mulVec_zero, zero_add]`. Rewrite using `[Matrix.mulVec_mulVec]`. Conclude with `hv`. Establish `hb'' : HSpace.gram W₀ *ᵥ (C₀ *ᵥ (v ∘ Sum.inr)) = 0`.

Rewrite using `[← d.iso, ← Matrix.mulVec_mulVec, hb', Matrix.mulVec_zero]`. Establish `hc : C₀ *ᵥ (v ∘ Sum.inr) = 0` using `Matrix.eq_zero_of_mulVec_eq_zero (gram_det_ne W₀) hb''`. Establish `hinj₀ : Function.Injective C₀.mulVec` using `Matrix.mulVec_injective_iff.2 hC₀.2.1`. Establish `hb : v ∘ Sum.inr = 0` using `hinj₀ (by rw [hc, Matrix.mulVec_zero])`. Use function extensionality and compare the values at `x`.

Consider the cases of `x with`. Consider the case `inl i => exact congrFun ha i`. Consider the case `inr j => exact congrFun hb j`. Use `⟨M.submatrix id finSumFinEquiv.symm, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `hC₀.1` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Apply `Matrix.mulVec_injective_iff.1` to reduce the goal to its premises. Introduce `v w h`. Establish `hsub : M.submatrix id finSumFinEquiv.symm *ᵥ (v - w) = 0`. Rewrite using `[Matrix.mulVec_sub, h, sub_self]`.

Rewrite `hsub` using `[Matrix.submatrix_mulVec_equiv]`. Establish `h0` using `hker _ (by simpa using hsub)`. Establish `h1 : v - w = 0`. Use function extensionality and compare the values at `i`. Use `congrFun h0 (finSumFinEquiv.symm i)` as an intermediate fact.

Simplify using `using this`. Conclude with `sub_eq_zero.1 h1`. Use `show (M.submatrix id finSumFinEquiv.symm)ᴴ * HSpace.gram W * M.submatrix id finSumFinEquiv.symm = 0`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Conclude with `congrFun (congrFun hiso (finSumFinEquiv.symm i)) (finSumFinEquiv.symm j)`.
-/
theorem isoFrame_extend {W W₀ : HSp D} {r s : ℕ} (d : HypDec W W₀ r)
    {C₀ : Matrix (Fin W₀.rank) (Fin s) D.host.E} (hC₀ : IsIsoFrame W₀ C₀) :
    ∃ C : Matrix (Fin W.rank) (Fin (r + s)) D.host.E, IsIsoFrame W C := by
  classical
  set M : Matrix (Fin W.rank) (Fin r ⊕ Fin s) D.host.E := Matrix.fromCols d.e (d.i₀ * C₀) with hM
  have hG : (HSpace.gram W)ᴴ = HSpace.gram W := GlobalTheory.MixModel.gram_conjTranspose W
  have hi₀e : d.eᴴ * HSpace.gram W * d.i₀ = 0 := by
    have h := congrArg Matrix.conjTranspose d.i₀e
    simpa [Matrix.conjTranspose_mul, hG, Matrix.mul_assoc] using h
  have he'i₀ : d.e'ᴴ * HSpace.gram W * d.i₀ = 0 := by
    have h := congrArg Matrix.conjTranspose d.i₀e'
    simpa [Matrix.conjTranspose_mul, hG, Matrix.mul_assoc] using h
  have hC₀iso : C₀ᴴ * HSpace.gram W₀ * C₀ = 0 := hC₀.2.2
  have hiso : Mᴴ * HSpace.gram W * M = 0 := by
    rw [hM, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.fromRows_mul,
      Matrix.fromRows_mul_fromCols]
    have h1 : d.eᴴ * HSpace.gram W * d.e = 0 := d.ee
    have h2 : d.eᴴ * HSpace.gram W * (d.i₀ * C₀) = 0 := by rw [← Matrix.mul_assoc, hi₀e, Matrix.zero_mul]
    have h3 : (d.i₀ * C₀)ᴴ * HSpace.gram W * d.e = 0 := by
      rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc d.i₀ᴴ, d.i₀e,
        Matrix.mul_zero]
    have h4 : (d.i₀ * C₀)ᴴ * HSpace.gram W * (d.i₀ * C₀) = 0 := by
      rw [Matrix.conjTranspose_mul, show C₀ᴴ * d.i₀ᴴ * HSpace.gram W * (d.i₀ * C₀) =
        C₀ᴴ * (d.i₀ᴴ * HSpace.gram W * d.i₀) * C₀ by simp only [Matrix.mul_assoc], d.iso, hC₀iso]
    rw [h1, h2, h3, h4, Matrix.fromBlocks_zero]
  have hker : ∀ v, M *ᵥ v = 0 → v = 0 := by
    intro v hv
    rw [hM, Matrix.fromCols_mulVec] at hv
    have ha : v ∘ Sum.inl = 0 := by
      have h := congrArg (fun x => (d.e'ᴴ * HSpace.gram W) *ᵥ x) hv
      simp only [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_zero] at h
      rwa [d.e'e, ← Matrix.mul_assoc, he'i₀, Matrix.zero_mul, Matrix.zero_mulVec, add_zero,
        Matrix.one_mulVec] at h
    have hb' : d.i₀ *ᵥ (C₀ *ᵥ (v ∘ Sum.inr)) = 0 := by
      rw [ha, Matrix.mulVec_zero, zero_add] at hv
      rw [Matrix.mulVec_mulVec]; exact hv
    have hb'' : HSpace.gram W₀ *ᵥ (C₀ *ᵥ (v ∘ Sum.inr)) = 0 := by
      rw [← d.iso, ← Matrix.mulVec_mulVec, hb', Matrix.mulVec_zero]
    have hc : C₀ *ᵥ (v ∘ Sum.inr) = 0 := Matrix.eq_zero_of_mulVec_eq_zero (gram_det_ne W₀) hb''
    have hinj₀ : Function.Injective C₀.mulVec := Matrix.mulVec_injective_iff.2 hC₀.2.1
    have hb : v ∘ Sum.inr = 0 := hinj₀ (by rw [hc, Matrix.mulVec_zero])
    funext x
    cases x with
    | inl i => exact congrFun ha i
    | inr j => exact congrFun hb j
  refine ⟨M.submatrix id finSumFinEquiv.symm, ?_, ?_, ?_⟩
  · have := hC₀.1; omega
  · apply Matrix.mulVec_injective_iff.1
    intro v w h
    have hsub : M.submatrix id finSumFinEquiv.symm *ᵥ (v - w) = 0 := by
      rw [Matrix.mulVec_sub, h, sub_self]
    rw [Matrix.submatrix_mulVec_equiv] at hsub
    have h0 := hker _ (by simpa using hsub)
    have h1 : v - w = 0 := by
      funext i
      have := congrFun h0 (finSumFinEquiv.symm i)
      simpa using this
    exact sub_eq_zero.1 h1
  · show (M.submatrix id finSumFinEquiv.symm)ᴴ * HSpace.gram W * M.submatrix id finSumFinEquiv.symm = 0
    refine Matrix.ext fun i j => ?_
    exact congrFun (congrFun hiso (finSumFinEquiv.symm i)) (finSumFinEquiv.symm j)

/- English proof (translation)
Distinguish the cases in `hA : IsAniso W`. Conclude with `Or.inl hA`. Use `right`. Establish `hex : ∃ r, ∃ C : Matrix (Fin W.rank) (Fin r) D.host.E, IsIsoFrame W C`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Conclude with `hA fun r C => h r C`. Take `⟨r₁, C₁, hC₁⟩` from `hex`. Set `P : ℕ → Prop` to `fun r => ∃ C : Matrix (Fin W.rank) (Fin r) D.host.E, IsIsoFrame W C`. Establish `hPr : P (Nat.findGreatest P W.rank)` using `Nat.findGreatest_spec (isoFrame_le hC₁) ⟨C₁, hC₁⟩`.

Establish `hmax : ∀ s, P s → s ≤ Nat.findGreatest P W.rank` using `fun s hs => Nat.le_findGreatest (isoFrame_le hs.choose_spec) hs`. Take `⟨C, hC⟩` from `hPr`. Take `⟨W₀, ⟨hrk, ι, hι, C', hC', horth⟩, -⟩` from `GlobalTheory.WittLow.wittLowEx D W (Nat.findGreatest P W.rank) ⟨C, hC.2.1, hC.2.2⟩`. Establish `hpos : 0 < Nat.findGreatest P W.rank` using `hC.1`. Establish `hG : (HSpace.gram W)ᴴ = HSpace.gram W` using `GlobalTheory.MixModel.gram_conjTranspose W`.

Establish `hsplit : GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit W W₀ C' (frameMat W W₀ ι)`. Use `⟨⟨hpos, hC'.1, hC'.2⟩, GlobalTheory.AutFunCounterexample.gram_pull W W₀ ι hι, ?_, by omega⟩` and prove the remaining obligations. Use `show C'ᴴ * HSpace.gram W * frameMat W W₀ ι = 0`. Establish `h : (frameMat W W₀ ι)ᴴ * HSpace.gram W * C' = 0` using `horth`. Establish `h2` using `congrArg Matrix.conjTranspose h`.

Simplify `h2` using `[Matrix.conjTranspose_mul, hG, Matrix.mul_assoc]`. Take `⟨d, -, -, -⟩` from `GlobalTheory.WittSect.exists_hypDec_mem_NI D W W₀ _ C' _ hsplit`. Use `⟨W₀, _, d, fun s C₀ hC₀ => ?_, hpos⟩` and prove the remaining obligations. Take `⟨C₂, hC₂⟩` from `isoFrame_extend d hC₀`. Establish `h1` using `hmax _ ⟨C₂, hC₂⟩`.

Establish `h2` using `hC₀.1`. Use linear arithmetic over natural numbers and integers.
-/
theorem aniso_or_hypDec (W : HSp D) :
    IsAniso W ∨ ∃ (W₀ : HSp D) (r' : ℕ) (_ : HypDec W W₀ r'), IsAniso W₀ ∧ 0 < r' := by
  classical
  by_cases hA : IsAniso W
  · exact Or.inl hA
  right
  have hex : ∃ r, ∃ C : Matrix (Fin W.rank) (Fin r) D.host.E, IsIsoFrame W C := by
    by_contra h
    push_neg at h
    exact hA fun r C => h r C
  obtain ⟨r₁, C₁, hC₁⟩ := hex
  let P : ℕ → Prop := fun r => ∃ C : Matrix (Fin W.rank) (Fin r) D.host.E, IsIsoFrame W C
  have hPr : P (Nat.findGreatest P W.rank) := Nat.findGreatest_spec (isoFrame_le hC₁) ⟨C₁, hC₁⟩
  have hmax : ∀ s, P s → s ≤ Nat.findGreatest P W.rank := fun s hs =>
    Nat.le_findGreatest (isoFrame_le hs.choose_spec) hs
  obtain ⟨C, hC⟩ := hPr
  obtain ⟨W₀, ⟨hrk, ι, hι, C', hC', horth⟩, -⟩ :=
    GlobalTheory.WittLow.wittLowEx D W (Nat.findGreatest P W.rank) ⟨C, hC.2.1, hC.2.2⟩
  have hpos : 0 < Nat.findGreatest P W.rank := hC.1
  have hG : (HSpace.gram W)ᴴ = HSpace.gram W := GlobalTheory.MixModel.gram_conjTranspose W
  have hsplit : GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit W W₀ C' (frameMat W W₀ ι) := by
    refine ⟨⟨hpos, hC'.1, hC'.2⟩, GlobalTheory.AutFunCounterexample.gram_pull W W₀ ι hι, ?_, by omega⟩
    show C'ᴴ * HSpace.gram W * frameMat W W₀ ι = 0
    have h : (frameMat W W₀ ι)ᴴ * HSpace.gram W * C' = 0 := horth
    have h2 := congrArg Matrix.conjTranspose h
    simpa [Matrix.conjTranspose_mul, hG, Matrix.mul_assoc] using h2
  obtain ⟨d, -, -, -⟩ := GlobalTheory.WittSect.exists_hypDec_mem_NI D W W₀ _ C' _ hsplit
  refine ⟨W₀, _, d, fun s C₀ hC₀ => ?_, hpos⟩
  obtain ⟨C₂, hC₂⟩ := isoFrame_extend d hC₀
  have h1 := hmax _ ⟨C₂, hC₂⟩
  have h2 := hC₀.1
  omega

/- English proof (translation)
Introduce `_ W _` and use `⟨GlobalTheory.Doubling.exists_isMaj W, aniso_or_hypDec W⟩`.
-/
theorem maj_and_witt : ∀ (D : D7) (W : HSp D), HSpace.SigOK W →
    (∃ b : GL (Fin W.rank) (AE D), IsMaj W b) ∧
      (IsAniso W ∨ ∃ (W₀ : HSp D) (r' : ℕ) (_ : HypDec W W₀ r'), IsAniso W₀ ∧ 0 < r') :=
  fun _ W _ => ⟨GlobalTheory.Doubling.exists_isMaj W, aniso_or_hypDec W⟩

end GlobalTheory.Core.Rk.WittDec
