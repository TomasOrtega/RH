import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurePreservingMulRight
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqBotOrTopOfTensor
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeadingMinorsWeightVectorEqTensorExtremalVectors
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChiGridHighestWeightEqCompactChainParameter

noncomputable section

open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped Matrix

namespace GlobalTheory.CoefPsi

section General

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Unfold `hwVec Formalism.L2.DIV.ten Formalism.BasicNotions.extremal Formalism.GradedWeylDivisibility.hw`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[map_prod, Finset.prod_filter]`. Use `Finset.prod_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[map_pow]`.

Establish `hm : Formalism.GradedWeylDivisibility.blockEmb ℂ τ (Formalism.GradedWeylDivisibility.lpMinor ℂ (s.val + 1) (Nat.succ_le_of_lt s.isLt) (Nat.succ_le_of_lt s.isLt)) = minor n τ s`. Unfold `Formalism.GradedWeylDivisibility.blockEmb Formalism.GradedWeylDivisibility.lpMinor minor`. Rewrite using `[AlgHom.map_det]`. Use `congr 1`. Use extensionality with `p q`.

Simplify using `[rename_X]`. Rewrite using `[hm]`. Establish `hs0` using `s.isLt`. Use `split_ifs with hs`. Use `congr 1`.

Simplify using `only [Formalism.GradedWeylDivisibility.nuNext, DomWeight.natW, DomWeight.detShift, dif_pos hs, dif_pos (show 0 < n by omega), hl, Fin.val_mk]`. Establish `a1` using `(lam' τ).anti (show s ≤ (⟨s.val + 1, hs⟩ : Fin n) by simp [Fin.le_def])`. Establish `a2` using `(lam' τ).anti (show (⟨s.val + 1, hs⟩ : Fin n) ≤ ⟨n - 1, by omega⟩ by simp [Fin.le_def]; omega)`. Rewrite `a1`, `a2` using `[hl, hl]`. Simplify using `only [Fin.val_mk] at a1 a2`.

Use linear arithmetic over natural numbers and integers. Establish `hs' : s.val = n - 1` using `by omega`. Establish `h0 : (lam' τ).natW s = 0`. Establish `e : s = ⟨n - 1, by omega⟩` using `Fin.ext hs'`. Simplify using `only [DomWeight.natW, DomWeight.detShift, dif_pos (show 0 < n by omega), e]`.

Simplify using the standard rewrite rules. Rewrite using `[h0, Nat.zero_sub, pow_zero]`.
-/
theorem hwVec_eq_ten (n : ℕ) (lam : ι → ℕ → ℤ) (lam' : ι → DomWeight n)
    (hl : ∀ τ (i : Fin n), (lam' τ).w i = lam τ i) :
    hwVec n lam = Formalism.L2.DIV.ten (fun τ => Formalism.BasicNotions.extremal ℂ n (lam' τ)) := by
  unfold hwVec Formalism.L2.DIV.ten Formalism.BasicNotions.extremal Formalism.GradedWeylDivisibility.hw
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_prod, Finset.prod_filter]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_pow]
  have hm : Formalism.GradedWeylDivisibility.blockEmb ℂ τ (Formalism.GradedWeylDivisibility.lpMinor ℂ (s.val + 1) (Nat.succ_le_of_lt s.isLt) (Nat.succ_le_of_lt s.isLt)) =
      minor n τ s := by
    unfold Formalism.GradedWeylDivisibility.blockEmb Formalism.GradedWeylDivisibility.lpMinor minor
    rw [AlgHom.map_det]
    congr 1
    ext p q
    simp [rename_X]
  rw [hm]
  have hs0 := s.isLt
  split_ifs with hs
  · congr 1
    simp only [Formalism.GradedWeylDivisibility.nuNext, DomWeight.natW, DomWeight.detShift, dif_pos hs, dif_pos (show 0 < n by omega), hl,
      Fin.val_mk]
    have a1 := (lam' τ).anti (show s ≤ (⟨s.val + 1, hs⟩ : Fin n) by simp [Fin.le_def])
    have a2 := (lam' τ).anti (show (⟨s.val + 1, hs⟩ : Fin n) ≤ ⟨n - 1, by omega⟩ by simp [Fin.le_def]; omega)
    rw [hl, hl] at a1 a2
    simp only [Fin.val_mk] at a1 a2
    omega
  · have hs' : s.val = n - 1 := by omega
    have h0 : (lam' τ).natW s = 0 := by
      have e : s = ⟨n - 1, by omega⟩ := Fin.ext hs'
      simp only [DomWeight.natW, DomWeight.detShift, dif_pos (show 0 < n by omega), e]
      simp
    rw [h0, Nat.zero_sub, pow_zero]

/- English proof (translation)
Simplify using `only [leftRep, linSub, homMat, MonoidHom.coe_comp, Function.comp_apply, MonoidHom.inr_apply, MonoidHom.coe_mk, OneHom.coe_mk, AlgHom.toLinearMap_apply, Formalism.L2.DIV.trAct, Formalism.GradedWeylDivisibility.blockAct]`. Use `congrArg (fun f => aeval f F) ?_` and prove the remaining obligations. Use function extensionality and compare the values at `p`. Simplify using `[Matrix.kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type, GlobalTheory.Branching.unitaryIncl_coe, Matrix.transpose_apply, mul_ite]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_eq_single p.2.2 (fun b _ hb => by simp [hb]) (by simp)]`. Simplify using the standard rewrite rules.
-/
theorem leftRep_eq (n : ℕ) (g : UG ι n) (F : GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.Pol ι n n) :
    leftRep n g F = Formalism.L2.DIV.trAct (fun τ => GlobalTheory.Branching.unitaryIncl n (g τ)) F := by
  simp only [leftRep, linSub, homMat, MonoidHom.coe_comp, Function.comp_apply, MonoidHom.inr_apply,
    MonoidHom.coe_mk, OneHom.coe_mk, AlgHom.toLinearMap_apply, Formalism.L2.DIV.trAct, Formalism.GradedWeylDivisibility.blockAct]
  refine congrArg (fun f => aeval f F) ?_
  funext p
  simp [Matrix.kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type, GlobalTheory.Branching.unitaryIncl_coe,
    Matrix.transpose_apply, mul_ite]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_eq_single p.2.2 (fun b _ hb => by simp [hb]) (by simp)]
  simp

/- English proof (translation)
Proceed by induction on `F using MvPolynomial.induction_on`. Use `next a =>`. Simplify using `[Formalism.GradedWeylDivisibility.blockAct, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]`. Use `next p q hp hq =>`. Simplify using `only [map_add, hp, hq]`.

Use `next p v hp =>`. Simplify using `only [map_mul, hp, map_X, Formalism.L2.DIV.blockAct_X, map_sum, map_C, Matrix.map_apply]`.
-/
private theorem map_conj_blockAct {ι : Type} [Fintype ι] {n : ℕ} (U : ι → Matrix (Fin n) (Fin n) ℂ)
    (F : Formalism.L2.DIV.Pol ℂ ι n) :
    map (starRingEnd ℂ) (Formalism.GradedWeylDivisibility.blockAct ℂ U F) =
      Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => (U τ).map (starRingEnd ℂ)) (map (starRingEnd ℂ) F) := by
  induction F using MvPolynomial.induction_on
  next a =>
    simp [Formalism.GradedWeylDivisibility.blockAct, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
  next p q hp hq =>
    simp only [map_add, hp, hq]
  next p v hp =>
    simp only [map_mul, hp, map_X, Formalism.L2.DIV.blockAct_X, map_sum, map_C, Matrix.map_apply]

/- English proof (translation)
Establish `h1` using `map_conj_blockAct (fun τ => ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ) F`. Establish `hU : (fun τ => ((((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ).map (starRingEnd ℂ))ᴴ) = fun τ => ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)`. Use function extensionality and compare the values at `τ`. Use extensionality with `i j`. Simplify using `[Matrix.conjTranspose_apply]`.

Establish `h3 : (fun τ => ((invTrK g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ * ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)) = fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)`. Use function extensionality and compare the values at `τ`. Rewrite using `[invTrK_coe, Matrix.transpose_transpose, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one]`. Establish `h2 : Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)) (Formalism.L2.DIV.trAct (invTrK g) F') = F'`. Establish `e` using `congrArg (fun φ => φ F') (Formalism.L2.DIV.blockAct_comp (K := ℂ) (fun τ => ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)) (fun τ => ((invTrK g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ))`.

Simplify using `only [AlgHom.comp_apply] at e`. Rewrite using `[show Formalism.L2.DIV.trAct (invTrK g) F' = Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => ((invTrK g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ) F' from rfl, e, h3, Formalism.L2.DIV.blockAct_one]`. Both sides reduce to the same expression. Use `show fockS (map (starRingEnd ℂ) (Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ) F)) _ = _`. Rewrite using `[h1, Formalism.L2.DIV.fockSAdj ℂ ι n, hU, h2]`.
-/
theorem fockS_conj_trAct (n : ℕ) (g : ι → GL (Fin n) ℂ) (F F' : Formalism.L2.DIV.Pol ℂ ι n) :
    fockS (map (starRingEnd ℂ) (Formalism.L2.DIV.trAct g F)) (Formalism.L2.DIV.trAct (invTrK g) F') =
      fockS (map (starRingEnd ℂ) F) F' := by
  have h1 := map_conj_blockAct (fun τ => ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ) F
  have hU : (fun τ => ((((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ).map (starRingEnd ℂ))ᴴ) =
      fun τ => ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) := by
    funext τ
    ext i j
    simp [Matrix.conjTranspose_apply]
  have h3 : (fun τ => ((invTrK g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ * ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)) =
      fun _ => (1 : Matrix (Fin n) (Fin n) ℂ) := by
    funext τ
    rw [invTrK_coe, Matrix.transpose_transpose, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.GeneralLinearGroup.coe_one]
  have h2 : Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)) (Formalism.L2.DIV.trAct (invTrK g) F') = F' := by
    have e := congrArg (fun φ => φ F') (Formalism.L2.DIV.blockAct_comp (K := ℂ) (fun τ => ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ))
      (fun τ => ((invTrK g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ))
    simp only [AlgHom.comp_apply] at e
    rw [show Formalism.L2.DIV.trAct (invTrK g) F' = Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => ((invTrK g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ) F' from rfl,
      e, h3, Formalism.L2.DIV.blockAct_one]
    rfl
  show fockS (map (starRingEnd ℂ) (Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ) F)) _ = _
  rw [h1, Formalism.L2.DIV.fockSAdj ℂ ι n, hU, h2]

/- English proof (translation)
Conclude with `GlobalTheory.Proof.TensorMapDescent.map_mem_VV (starRingEnd ℂ) lam' F hF`.
-/
theorem conj_mem_VV (n : ℕ) (lam' : ι → DomWeight n) {F : Formalism.L2.DIV.Pol ℂ ι n}
    (hF : F ∈ Formalism.L2.DIV.VV ℂ lam') : map (starRingEnd ℂ) F ∈ Formalism.L2.DIV.VV ℂ lam' := by
  exact GlobalTheory.Proof.TensorMapDescent.map_mem_VV (starRingEnd ℂ) lam' F hF

/- English proof (translation)
Establish `hterm : ∀ m, star (F.coeff m) * F.coeff m * ((mfact m : ℕ) : ℂ) = ((Complex.normSq (F.coeff m) * (mfact m : ℝ) : ℝ) : ℂ)`. Introduce `m`. Rewrite using `[Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self, Complex.ofReal_natCast]`. Both sides reduce to the same expression. Establish `hsum : ∑ m ∈ F.support, Complex.normSq (F.coeff m) * (mfact m : ℝ) = 0`.

Rewrite `h` using `[fockS, Finset.sum_congr rfl (fun m _ => hterm m)]`. Establish `h'` using `congrArg Complex.re h`. Rewrite `h'` using `[Complex.re_sum]`. Simplify `h'` using `only [Complex.ofReal_re, Complex.zero_re]`. Establish `hall` using `(Finset.sum_eq_zero_iff_of_nonneg (fun m _ => mul_nonneg (Complex.normSq_nonneg _) (Nat.cast_nonneg _))).1 hsum`.

Use extensionality with `m`. Rewrite using `[coeff_zero]`. Assume the negation of the conclusion as `hne`. Establish `hm : m ∈ F.support` using `mem_support_iff.mpr hne`. Establish `hfac : (mfact m : ℝ) ≠ 0`.

Rewrite using `[Nat.cast_ne_zero]`. Conclude with `Finset.prod_ne_zero_iff.mpr fun k _ => Nat.factorial_ne_zero _`. Break down `mul_eq_zero.1 (hall m hm) with h0 | h0` into its components or cases. Conclude with `hne (Complex.normSq_eq_zero.1 h0)`. Conclude with `hfac h0`.
-/
theorem eq_zero_of_fockS_self {σ : Type} (F : MvPolynomial σ ℂ) (h : fockS F F = 0) : F = 0 := by
  have hterm : ∀ m, star (F.coeff m) * F.coeff m * ((mfact m : ℕ) : ℂ) =
      ((Complex.normSq (F.coeff m) * (mfact m : ℝ) : ℝ) : ℂ) := by
    intro m
    rw [Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self, Complex.ofReal_natCast]
    rfl
  have hsum : ∑ m ∈ F.support, Complex.normSq (F.coeff m) * (mfact m : ℝ) = 0 := by
    rw [fockS, Finset.sum_congr rfl (fun m _ => hterm m)] at h
    have h' := congrArg Complex.re h
    rw [Complex.re_sum] at h'
    simpa only [Complex.ofReal_re, Complex.zero_re] using h'
  have hall := (Finset.sum_eq_zero_iff_of_nonneg
    (fun m _ => mul_nonneg (Complex.normSq_nonneg _) (Nat.cast_nonneg _))).1 hsum
  ext m
  rw [coeff_zero]
  by_contra hne
  have hm : m ∈ F.support := mem_support_iff.mpr hne
  have hfac : (mfact m : ℝ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => Nat.factorial_ne_zero _
  rcases mul_eq_zero.1 (hall m hm) with h0 | h0
  · exact hne (Complex.normSq_eq_zero.1 h0)
  · exact hfac h0

/- English proof (translation)
Establish `hext : ∀ τ, Formalism.BasicNotions.extremal ℂ n (lam' τ) ∈ nablaSq ℂ n (lam' τ)` using `fun τ => Formalism.GradedWeylDivisibility.hwMem ℂ n n le_rfl _ (Formalism.L2.DIV.natW_antitone (lam' τ))`. Establish `h0 : Formalism.L2.DIV.ten (fun τ => Formalism.BasicNotions.extremal ℂ n (lam' τ)) ∈ Formalism.L2.DIV.VV ℂ lam'` using `GlobalTheory.Proof.TensorMapDescent.ten_mem lam' _ hext`. Establish `hne : Formalism.L2.DIV.ten (fun τ => Formalism.BasicNotions.extremal ℂ n (lam' τ)) ≠ 0` using `GlobalTheory.Proof.TensorMapDescent.ten_ne_zero _ fun τ => Formalism.GradedWeylDivisibility.hwNe ℂ n n le_rfl _`. Establish `hdt : ∀ g : ι → GL (Fin n) ℂ, Formalism.L2.DIV.detTwK lam' g ≠ 0`. Introduce `g`.

Rewrite using `[detTw_eq]`. Conclude with `Finset.prod_ne_zero_iff.2 fun τ _ => zpow_ne_zero _ (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit (g τ))))`. Establish `htr : ∀ (g : ι → GL (Fin n) ℂ) (x : Formalism.L2.DIV.Pol ℂ ι n), x ∈ Formalism.L2.DIV.VV ℂ lam' → Formalism.L2.DIV.trAct g x ∈ Formalism.L2.DIV.VV ℂ lam'`. Introduce `g x hx`. Establish `hA` using `polyAction_mem_VV lam' g hx`.

Establish `e : Formalism.L2.DIV.trAct g x = (Formalism.L2.DIV.detTwK lam' g)⁻¹ • Formalism.L2.DIV.actP lam' g x`. Rewrite using `[Formalism.L2.DIV.actP, LinearMap.smul_apply, AlgHom.toLinearMap_apply, smul_smul, inv_mul_cancel₀ (hdt g), one_smul]`. Rewrite using `[e]`. Conclude with `Submodule.smul_mem _ _ hA`. Establish `hW : weylSub n lam = Submodule.span ℂ (Set.range fun g : UG ι n => Formalism.L2.DIV.trAct (fun τ => GlobalTheory.Branching.unitaryIncl n (g τ)) (Formalism.L2.DIV.ten fun τ => Formalism.BasicNotions.extremal ℂ n (lam' τ)))`.

Unfold `weylSub`. Simplify using `only [leftRep_eq, hwVec_eq_ten n lam lam' hl]`. Rewrite using `[hW]`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨g, rfl⟩`. Conclude with `htr _ _ h0`. Use `set S := Submodule.span ℂ (Set.range fun g : UG ι n => Formalism.L2.DIV.trAct (fun τ => GlobalTheory.Branching.unitaryIncl n (g τ)) (Formalism.L2.DIV.ten fun τ => Formalism.BasicNotions.extremal ℂ n (lam' τ))) with hS`. Establish `hstab : ∀ h : ι → GL (Fin n) ℂ, (∀ τ, (h τ : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ) → ∀ x ∈ S, Formalism.L2.DIV.trAct h x ∈ S`. Introduce `h hh x hx`.

Use `Submodule.span_induction (p := fun x _ => Formalism.L2.DIV.trAct h x ∈ S) ?_ ?_ ?_ ?_ hx` and prove the remaining obligations. Introduce and unpack `_ ⟨u, rfl⟩`. Use `Submodule.subset_span ⟨fun τ => ⟨(h τ : Matrix (Fin n) (Fin n) ℂ), hh τ⟩ * u τ, ?_⟩` and prove the remaining obligations. Use `show Formalism.L2.DIV.trAct _ _ = Formalism.L2.DIV.trAct h (Formalism.L2.DIV.trAct _ _)`. Rewrite using `[← AlgHom.comp_apply, ← Formalism.L2.DIV.trAct_mul]`.

Use `congrArg (fun A => Formalism.L2.DIV.trAct A _) ?_` and prove the remaining obligations. Use function extensionality and compare the values at `τ`. Use extensionality with `i j`. Simplify using `[GlobalTheory.Branching.unitaryIncl_coe]`. Simplify using the standard rewrite rules.

Introduce `x y _ _ hx hy`. Rewrite using `[map_add]`. Conclude with `S.add_mem hx hy`. Introduce `c x _ hx`. Rewrite using `[map_smul]`.

Conclude with `S.smul_mem c hx`. Set `U : Submodule ℂ (Formalism.L2.DIV.VV ℂ lam')` to `S.comap (Formalism.L2.DIV.VV ℂ lam').subtype`. Establish `hU` using `GlobalTheory.CoefIrred.vv_irreducible_unitary ι n lam' U (by`. Introduce `h hh x hx`. Use `show ((Formalism.L2.DIV.rhoK lam' h x : Formalism.L2.DIV.VV ℂ lam') : Formalism.L2.DIV.Pol ℂ ι n) ∈ S`.

Rewrite using `[Formalism.L2.DIV.rhoK_coe, Formalism.L2.DIV.actP, LinearMap.smul_apply, AlgHom.toLinearMap_apply]`. Conclude with `S.smul_mem _ (hstab h hh _ hx))`. Break down `hU with hU | hU` into its components or cases. It suffices to derive a contradiction. Establish `h1 : Formalism.L2.DIV.trAct (fun τ => GlobalTheory.Branching.unitaryIncl n ((1 : UG ι n) τ)) (Formalism.L2.DIV.ten fun τ => Formalism.BasicNotions.extremal ℂ n (lam' τ)) ∈ S` using `Submodule.subset_span ⟨1, rfl⟩`.

Establish `e1 : (fun τ => GlobalTheory.Branching.unitaryIncl n ((1 : UG ι n) τ)) = 1`. Use function extensionality and compare the values at `τ`. Simplify using the standard rewrite rules. Rewrite `h1` using `[e1, Formalism.L2.DIV.trAct_one, AlgHom.id_apply]`. Establish `hmem : (⟨_, h0⟩ : Formalism.L2.DIV.VV ℂ lam') ∈ U` using `h1`.

Rewrite `hmem` using `[hU, Submodule.mem_bot]`. Conclude with `hne (congrArg Subtype.val hmem)`. Introduce `x hx`. Establish `hx' : (⟨x, hx⟩ : Formalism.L2.DIV.VV ℂ lam') ∈ U`. Rewrite using `[hU]`.

Conclude with `Submodule.mem_top`. Conclude with `hx'`.
-/
theorem weylSub_eq (n : ℕ) (lam : ι → ℕ → ℤ) (lam' : ι → DomWeight n)
    (hl : ∀ τ (i : Fin n), (lam' τ).w i = lam τ i) : weylSub n lam = Formalism.L2.DIV.VV ℂ lam' := by
  have hext : ∀ τ, Formalism.BasicNotions.extremal ℂ n (lam' τ) ∈ nablaSq ℂ n (lam' τ) := fun τ =>
    Formalism.GradedWeylDivisibility.hwMem ℂ n n le_rfl _ (Formalism.L2.DIV.natW_antitone (lam' τ))
  have h0 : Formalism.L2.DIV.ten (fun τ => Formalism.BasicNotions.extremal ℂ n (lam' τ)) ∈ Formalism.L2.DIV.VV ℂ lam' :=
    GlobalTheory.Proof.TensorMapDescent.ten_mem lam' _ hext
  have hne : Formalism.L2.DIV.ten (fun τ => Formalism.BasicNotions.extremal ℂ n (lam' τ)) ≠ 0 :=
    GlobalTheory.Proof.TensorMapDescent.ten_ne_zero _ fun τ => Formalism.GradedWeylDivisibility.hwNe ℂ n n le_rfl _
  have hdt : ∀ g : ι → GL (Fin n) ℂ, Formalism.L2.DIV.detTwK lam' g ≠ 0 := by
    intro g
    rw [detTw_eq]
    exact Finset.prod_ne_zero_iff.2 fun τ _ => zpow_ne_zero _
      (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit (g τ))))
  have htr : ∀ (g : ι → GL (Fin n) ℂ) (x : Formalism.L2.DIV.Pol ℂ ι n), x ∈ Formalism.L2.DIV.VV ℂ lam' →
      Formalism.L2.DIV.trAct g x ∈ Formalism.L2.DIV.VV ℂ lam' := by
    intro g x hx
    have hA := polyAction_mem_VV lam' g hx
    have e : Formalism.L2.DIV.trAct g x = (Formalism.L2.DIV.detTwK lam' g)⁻¹ • Formalism.L2.DIV.actP lam' g x := by
      rw [Formalism.L2.DIV.actP, LinearMap.smul_apply, AlgHom.toLinearMap_apply, smul_smul, inv_mul_cancel₀ (hdt g), one_smul]
    rw [e]
    exact Submodule.smul_mem _ _ hA
  have hW : weylSub n lam = Submodule.span ℂ (Set.range fun g : UG ι n =>
      Formalism.L2.DIV.trAct (fun τ => GlobalTheory.Branching.unitaryIncl n (g τ)) (Formalism.L2.DIV.ten fun τ => Formalism.BasicNotions.extremal ℂ n (lam' τ))) := by
    unfold weylSub
    simp only [leftRep_eq, hwVec_eq_ten n lam lam' hl]
  rw [hW]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    exact htr _ _ h0
  · set S := Submodule.span ℂ (Set.range fun g : UG ι n =>
      Formalism.L2.DIV.trAct (fun τ => GlobalTheory.Branching.unitaryIncl n (g τ)) (Formalism.L2.DIV.ten fun τ => Formalism.BasicNotions.extremal ℂ n (lam' τ))) with hS
    have hstab : ∀ h : ι → GL (Fin n) ℂ, (∀ τ, (h τ : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ) →
        ∀ x ∈ S, Formalism.L2.DIV.trAct h x ∈ S := by
      intro h hh x hx
      refine Submodule.span_induction (p := fun x _ => Formalism.L2.DIV.trAct h x ∈ S) ?_ ?_ ?_ ?_ hx
      · rintro _ ⟨u, rfl⟩
        refine Submodule.subset_span ⟨fun τ => ⟨(h τ : Matrix (Fin n) (Fin n) ℂ), hh τ⟩ * u τ, ?_⟩
        show Formalism.L2.DIV.trAct _ _ = Formalism.L2.DIV.trAct h (Formalism.L2.DIV.trAct _ _)
        rw [← AlgHom.comp_apply, ← Formalism.L2.DIV.trAct_mul]
        refine congrArg (fun A => Formalism.L2.DIV.trAct A _) ?_
        funext τ
        ext i j
        simp [GlobalTheory.Branching.unitaryIncl_coe]
      · simp
      · intro x y _ _ hx hy
        rw [map_add]
        exact S.add_mem hx hy
      · intro c x _ hx
        rw [map_smul]
        exact S.smul_mem c hx
    let U : Submodule ℂ (Formalism.L2.DIV.VV ℂ lam') := S.comap (Formalism.L2.DIV.VV ℂ lam').subtype
    have hU := GlobalTheory.CoefIrred.vv_irreducible_unitary ι n lam' U (by
      intro h hh x hx
      show ((Formalism.L2.DIV.rhoK lam' h x : Formalism.L2.DIV.VV ℂ lam') : Formalism.L2.DIV.Pol ℂ ι n) ∈ S
      rw [Formalism.L2.DIV.rhoK_coe, Formalism.L2.DIV.actP, LinearMap.smul_apply, AlgHom.toLinearMap_apply]
      exact S.smul_mem _ (hstab h hh _ hx))
    rcases hU with hU | hU
    · exfalso
      have h1 : Formalism.L2.DIV.trAct (fun τ => GlobalTheory.Branching.unitaryIncl n ((1 : UG ι n) τ))
          (Formalism.L2.DIV.ten fun τ => Formalism.BasicNotions.extremal ℂ n (lam' τ)) ∈ S := Submodule.subset_span ⟨1, rfl⟩
      have e1 : (fun τ => GlobalTheory.Branching.unitaryIncl n ((1 : UG ι n) τ)) = 1 := by
        funext τ
        simp
      rw [e1, Formalism.L2.DIV.trAct_one, AlgHom.id_apply] at h1
      have hmem : (⟨_, h0⟩ : Formalism.L2.DIV.VV ℂ lam') ∈ U := h1
      rw [hU, Submodule.mem_bot] at hmem
      exact hne (congrArg Subtype.val hmem)
    · intro x hx
      have hx' : (⟨x, hx⟩ : Formalism.L2.DIV.VV ℂ lam') ∈ U := by
        rw [hU]
        exact Submodule.mem_top
      exact hx'

end General

end GlobalTheory.CoefPsi

namespace GlobalTheory.CoefPsi

section General2

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def bilF (n : ℕ) : Formalism.L2.DIV.Pol ℂ ι n →ₗ[ℂ] Formalism.L2.DIV.Pol ℂ ι n →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun F F' => fockS (map (starRingEnd ℂ) F) F')
    (fun F₁ F₂ F' => by simp only [map_add, ← fockL_apply, LinearMap.add_apply])
    (fun c F F' => by
      simp only [← fockL_apply, smul_eq_C_mul, map_mul, map_C, RingHom.coe_comp, Function.comp_apply]
      rw [← smul_eq_C_mul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]
      simp)
    (fun F F₁ F₂ => by simp only [← fockL_apply, map_add])
    (fun c F F' => by simp only [← fockL_apply, map_smul, smul_eq_mul])

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem bilF_apply (n : ℕ) (F F' : Formalism.L2.DIV.Pol ℂ ι n) : bilF n F F' = fockS (map (starRingEnd ℂ) F) F' := rfl

end General2

end GlobalTheory.CoefPsi

namespace GlobalTheory.CoefPsi

section General3

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Rewrite using `[LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul]`.
-/
theorem bilF_smul_left (n : ℕ) (c : ℂ) (F F' : Formalism.L2.DIV.Pol ℂ ι n) : bilF n (c • F) F' = c * bilF n F F' := by
  rw [LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul]

/- English proof (translation)
Establish `hdet : ∀ x : GL (Fin n) ℂ, ((x⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).det * (x : Matrix (Fin n) (Fin n) ℂ).det = 1`. Introduce `x`. Rewrite using `[← Matrix.det_mul, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one, Matrix.det_one]`. Establish `key : ∀ τ, ((((invTrK (fun τ => GlobalTheory.Branching.unitaryIncl n (g τ)))⁻¹ τ : GL (Fin n) ℂ)) : Matrix (Fin n) (Fin n) ℂ).det = ((g τ : Matrix.unitaryGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).det`. Introduce `τ`.

Rewrite using `[Pi.inv_apply]`. Establish `h2 : ((invTrK (fun τ => GlobalTheory.Branching.unitaryIncl n (g τ)) τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).det * ((g τ : Matrix.unitaryGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).det = 1`. Rewrite using `[invTrK_coe, Matrix.det_transpose]`. Use `hdet (GlobalTheory.Branching.unitaryIncl n (g τ))` as an intermediate fact. Rewrite `this` using `[GlobalTheory.Branching.unitaryIncl_coe]`. Then use the resulting hypothesis.

Establish `h3` using `hdet (invTrK (fun τ => GlobalTheory.Branching.unitaryIncl n (g τ)) τ)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[detTw_eq]`. Simplify using `only [detChar, detU, MonoidHom.coe_mk, OneHom.coe_mk, Units.coe_prod, Units.val_zpow_eq_zpow_val, MonoidHom.coe_toHomUnits, MonoidHom.coe_comp, Function.comp_apply, Matrix.coe_detMonoidHom, Submonoid.coe_subtype]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations.

Rewrite using `[key τ]`. Break down `Nat.eq_zero_or_pos n with hn | hn` into its components or cases. Substitute `hn` using the available equality. Simplify using the standard rewrite rules. Use `congr 1`.

Simplify using `only [DomWeight.detShift, dif_pos hn]`. Conclude with `hl τ _`.
-/
theorem detTwK_inv_invTrK (n : ℕ) (lam : ι → ℕ → ℤ) (lam' : ι → DomWeight n)
    (hl : ∀ τ (i : Fin n), (lam' τ).w i = lam τ i) (g : UG ι n) :
    detTwK lam' (invTrK (fun τ => GlobalTheory.Branching.unitaryIncl n (g τ)))⁻¹ =
      ((detChar n (fun τ => lam τ (n - 1)) g : ℂˣ) : ℂ) := by
  have hdet : ∀ x : GL (Fin n) ℂ,
      ((x⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).det * (x : Matrix (Fin n) (Fin n) ℂ).det = 1 := by
    intro x
    rw [← Matrix.det_mul, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one, Matrix.det_one]
  have key : ∀ τ, ((((invTrK (fun τ => GlobalTheory.Branching.unitaryIncl n (g τ)))⁻¹ τ : GL (Fin n) ℂ)) :
      Matrix (Fin n) (Fin n) ℂ).det = ((g τ : Matrix.unitaryGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).det := by
    intro τ
    rw [Pi.inv_apply]
    have h2 : ((invTrK (fun τ => GlobalTheory.Branching.unitaryIncl n (g τ)) τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).det *
        ((g τ : Matrix.unitaryGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).det = 1 := by
      rw [invTrK_coe, Matrix.det_transpose]
      have := hdet (GlobalTheory.Branching.unitaryIncl n (g τ))
      rwa [GlobalTheory.Branching.unitaryIncl_coe] at this
    have h3 := hdet (invTrK (fun τ => GlobalTheory.Branching.unitaryIncl n (g τ)) τ)
    calc _ = ((((invTrK (fun τ => GlobalTheory.Branching.unitaryIncl n (g τ)) τ)⁻¹ : GL (Fin n) ℂ)) : Matrix (Fin n) (Fin n) ℂ).det *
          (((invTrK (fun τ => GlobalTheory.Branching.unitaryIncl n (g τ)) τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).det *
            ((g τ : Matrix.unitaryGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).det) := by rw [h2, mul_one]
      _ = _ := by rw [← mul_assoc, h3, one_mul]
  rw [detTw_eq]
  simp only [detChar, detU, MonoidHom.coe_mk, OneHom.coe_mk, Units.coe_prod, Units.val_zpow_eq_zpow_val,
    MonoidHom.coe_toHomUnits, MonoidHom.coe_comp, Function.comp_apply, Matrix.coe_detMonoidHom, Submonoid.coe_subtype]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [key τ]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp
  · congr 1
    simp only [DomWeight.detShift, dif_pos hn]
    exact hl τ _

end General3

end GlobalTheory.CoefPsi

namespace GlobalTheory.CoefPsi

section General4

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Use `haveI : FiniteDimensional ℂ (Formalism.L2.DIV.VV ℂ lam') := Module.Finite.of_basis (Formalism.L2.DIV.bVV ℂ lam')`. Set `Φ : Formalism.L2.DIV.VV ℂ lam' →ₗ[ℂ] Module.Dual ℂ (Formalism.L2.DIV.VV ℂ lam')` to `((bilF n).compl₂ (Formalism.L2.DIV.VV ℂ lam').subtype).comp (Formalism.L2.DIV.VV ℂ lam').subtype`. Establish `hΦ : Function.Injective Φ`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `x hx`.

Establish `hc : map (starRingEnd ℂ) (x : Formalism.L2.DIV.Pol ℂ ι n) ∈ Formalism.L2.DIV.VV ℂ lam'` using `conj_mem_VV n lam' x.2`. Establish `h1` using `LinearMap.congr_fun hx ⟨_, hc⟩`. Simplify using `only [Φ, LinearMap.comp_apply, LinearMap.compl₂_apply, Submodule.coe_subtype, LinearMap.zero_apply, bilF_apply] at h1`. Establish `h2` using `eq_zero_of_fockS_self _ h1`. Establish `h3 : (x : Formalism.L2.DIV.Pol ℂ ι n) = 0` using `MvPolynomial.map_injective _ (starRingEnd ℂ).injective (by rw [h2, map_zero])`.

Conclude with `Subtype.ext h3`. Set `E : Formalism.L2.DIV.VV ℂ lam' ≃ₗ[ℂ] Module.Dual ℂ (Formalism.L2.DIV.VV ℂ lam')` to `LinearMap.linearEquivOfInjective Φ hΦ (Subspace.dual_finrank_eq).symm`. Use `⟨(LinearEquiv.ofEq _ _ (weylSub_eq n lam lam' hl)).trans E, fun g F => ?_⟩` and prove the remaining obligations. Use extensionality with `y`. Simplify using `only [E, LinearEquiv.trans_apply, LinearMap.comp_apply, LinearMap.linearEquivOfInjective_apply, Φ, LinearMap.compl₂_apply, Submodule.coe_subtype, LinearEquiv.coe_ofEq_apply]`.

Rewrite using `[Formalism.L2.DIV.rhoK_coe, Formalism.L2.DIV.actP, LinearMap.smul_apply, AlgHom.toLinearMap_apply, LinearMap.map_smul, smul_eq_mul, detTwK_inv_invTrK n lam lam' hl g]`. Establish `hw : ((weylRep n lam g F : weylSub n lam) : Pol ι n n) = ((detChar n (fun τ => lam τ (n - 1)) g : ℂˣ) : ℂ) • leftRep n g (F : Pol ι n n)` using `rfl`. Rewrite using `[hw, bilF_smul_left, leftRep_eq]`. Use `congr 1`. Rewrite using `[bilF_apply, bilF_apply]`.

Establish `key` using `fockS_conj_trAct n (fun τ => GlobalTheory.Branching.unitaryIncl n (g τ)) (F : Formalism.L2.DIV.Pol ℂ ι n) (Formalism.L2.DIV.trAct (invTrK (fun τ => GlobalTheory.Branching.unitaryIncl n (g τ)))⁻¹ (y : Formalism.L2.DIV.Pol ℂ ι n))`. Rewrite using `[← key]`. Use `congr 1`. Rewrite using `[← AlgHom.comp_apply, ← Formalism.L2.DIV.trAct_mul, mul_inv_cancel, Formalism.L2.DIV.trAct_one, AlgHom.id_apply]`.
-/
theorem exists_equiv (n : ℕ) (lam : ι → ℕ → ℤ) (lam' : ι → DomWeight n)
    (hl : ∀ τ (i : Fin n), (lam' τ).w i = lam τ i) :
    ∃ A : weylSub n lam ≃ₗ[ℂ] Module.Dual ℂ (Formalism.L2.DIV.VV ℂ lam'), ∀ (g : UG ι n) (F : weylSub n lam),
      A (weylRep n lam g F) =
        A F ∘ₗ Formalism.L2.DIV.rhoK lam' (invTrK (fun τ => GlobalTheory.Branching.unitaryIncl n (g τ)))⁻¹ := by
  classical
  haveI : FiniteDimensional ℂ (Formalism.L2.DIV.VV ℂ lam') := Module.Finite.of_basis (Formalism.L2.DIV.bVV ℂ lam')
  let Φ : Formalism.L2.DIV.VV ℂ lam' →ₗ[ℂ] Module.Dual ℂ (Formalism.L2.DIV.VV ℂ lam') :=
    ((bilF n).compl₂ (Formalism.L2.DIV.VV ℂ lam').subtype).comp (Formalism.L2.DIV.VV ℂ lam').subtype
  have hΦ : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have hc : map (starRingEnd ℂ) (x : Formalism.L2.DIV.Pol ℂ ι n) ∈ Formalism.L2.DIV.VV ℂ lam' := conj_mem_VV n lam' x.2
    have h1 := LinearMap.congr_fun hx ⟨_, hc⟩
    simp only [Φ, LinearMap.comp_apply, LinearMap.compl₂_apply, Submodule.coe_subtype, LinearMap.zero_apply,
      bilF_apply] at h1
    have h2 := eq_zero_of_fockS_self _ h1
    have h3 : (x : Formalism.L2.DIV.Pol ℂ ι n) = 0 :=
      MvPolynomial.map_injective _ (starRingEnd ℂ).injective (by rw [h2, map_zero])
    exact Subtype.ext h3
  let E : Formalism.L2.DIV.VV ℂ lam' ≃ₗ[ℂ] Module.Dual ℂ (Formalism.L2.DIV.VV ℂ lam') :=
    LinearMap.linearEquivOfInjective Φ hΦ (Subspace.dual_finrank_eq).symm
  refine ⟨(LinearEquiv.ofEq _ _ (weylSub_eq n lam lam' hl)).trans E, fun g F => ?_⟩
  ext y
  simp only [E, LinearEquiv.trans_apply, LinearMap.comp_apply, LinearMap.linearEquivOfInjective_apply, Φ,
    LinearMap.compl₂_apply, Submodule.coe_subtype, LinearEquiv.coe_ofEq_apply]
  rw [Formalism.L2.DIV.rhoK_coe, Formalism.L2.DIV.actP, LinearMap.smul_apply, AlgHom.toLinearMap_apply, LinearMap.map_smul, smul_eq_mul,
    detTwK_inv_invTrK n lam lam' hl g]
  have hw : ((weylRep n lam g F : weylSub n lam) : Pol ι n n) =
      ((detChar n (fun τ => lam τ (n - 1)) g : ℂˣ) : ℂ) • leftRep n g (F : Pol ι n n) := rfl
  rw [hw, bilF_smul_left, leftRep_eq]
  congr 1
  rw [bilF_apply, bilF_apply]
  have key := fockS_conj_trAct n (fun τ => GlobalTheory.Branching.unitaryIncl n (g τ)) (F : Formalism.L2.DIV.Pol ℂ ι n)
    (Formalism.L2.DIV.trAct (invTrK (fun τ => GlobalTheory.Branching.unitaryIncl n (g τ)))⁻¹ (y : Formalism.L2.DIV.Pol ℂ ι n))
  rw [← key]
  congr 1
  rw [← AlgHom.comp_apply, ← Formalism.L2.DIV.trAct_mul, mul_inv_cancel, Formalism.L2.DIV.trAct_one, AlgHom.id_apply]

end General4

end GlobalTheory.CoefPsi

namespace GlobalTheory.CoefPsi

section General5

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Substitute `h` using the available equality. Take `⟨A, hA⟩` from `exists_equiv n lam lam' hl`. Conclude with `⟨A, fun g F => hA g F⟩`.
-/
theorem exists_equiv_cast (n n' : ℕ) (h : n = n') (lam : ι → ℕ → ℤ) (lam' : ι → DomWeight n')
    (hl : ∀ τ (i : Fin n'), (lam' τ).w i = lam τ i) :
    ∃ A : weylSub n lam ≃ₗ[ℂ] Module.Dual ℂ (Formalism.L2.DIV.VV ℂ lam'), ∀ (g : UG ι n) (F : weylSub n lam),
      A (weylRep n lam g F) =
        A F ∘ₗ Formalism.L2.DIV.rhoK lam'
          (invTrK (fun τ => GlobalTheory.Branching.unitaryIncl n' (GlobalTheory.RowReal.castU h (g τ))))⁻¹ := by
  subst h
  obtain ⟨A, hA⟩ := exists_equiv n lam lam' hl
  exact ⟨A, fun g F => hA g F⟩

end General5

section Grid

open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowReal Formalism.IndefR.Links

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

/- English proof (translation)
Take `⟨hpw, hmem⟩` from `GlobalTheory.RowReal.WeightsX.psiPar_props D C τ`. Establish `hlen` using `GlobalTheory.RowReal.WeightsX.length_psiPar D C τ`. Establish `hf : StrictAnti (fun j : Fin (rankP D D.R.m) => (rowEntries D C τ).psiPar.getD j 0)`. Introduce `a b hab`. Establish `ha : (a : ℕ) < (rowEntries D C τ).psiPar.length` using `by rw [hlen]; exact a.isLt`.

Establish `hb : (b : ℕ) < (rowEntries D C τ).psiPar.length` using `by rw [hlen]; exact b.isLt`. Simplify using `only [List.getD_eq_getElem _ _ ha, List.getD_eq_getElem _ _ hb]`. Conclude with `List.pairwise_iff_getElem.1 hpw a b ha hb hab`. Establish `hm : ∀ j : Fin (rankP D D.R.m), (rowEntries D C τ).psiPar.getD j 0 ∈ (num D C τ).weightX 0`. Introduce `j`.

Establish `hj : (j : ℕ) < (rowEntries D C τ).psiPar.length` using `by rw [hlen]; exact j.isLt`. Rewrite using `[List.getD_eq_getElem _ _ hj]`. Conclude with `hmem _ (List.getElem_mem hj)`. Establish `hd` using `GlobalTheory.SignedHC.descEnum_unique (card_weight D C τ) hf hm`. Use `show ⌊GlobalTheory.SignedHC.highestWeight _ (card_weight D C τ) i⌋ = ⌊(rowEntries D C τ).psiPar.getD i 0 - ((((rowEntries D C τ).psiPar.length : ℚ) - 1) / 2 - ((i : ℕ) : ℚ))⌋`.

Unfold `GlobalTheory.SignedHC.highestWeight`. Rewrite using `[hd, hlen]`.
-/
theorem La_eq_hw (D : D7) (C : ℝ) (τ : D.what₂.Tau) (i : Fin (rankP D D.R.m)) :
    (La D C τ).w i = hw (rowEntries D C τ).psiPar i := by
  obtain ⟨hpw, hmem⟩ := GlobalTheory.RowReal.WeightsX.psiPar_props D C τ
  have hlen := GlobalTheory.RowReal.WeightsX.length_psiPar D C τ
  have hf : StrictAnti (fun j : Fin (rankP D D.R.m) => (rowEntries D C τ).psiPar.getD j 0) := by
    intro a b hab
    have ha : (a : ℕ) < (rowEntries D C τ).psiPar.length := by rw [hlen]; exact a.isLt
    have hb : (b : ℕ) < (rowEntries D C τ).psiPar.length := by rw [hlen]; exact b.isLt
    simp only [List.getD_eq_getElem _ _ ha, List.getD_eq_getElem _ _ hb]
    exact List.pairwise_iff_getElem.1 hpw a b ha hb hab
  have hm : ∀ j : Fin (rankP D D.R.m), (rowEntries D C τ).psiPar.getD j 0 ∈ (num D C τ).weightX 0 := by
    intro j
    have hj : (j : ℕ) < (rowEntries D C τ).psiPar.length := by rw [hlen]; exact j.isLt
    rw [List.getD_eq_getElem _ _ hj]
    exact hmem _ (List.getElem_mem hj)
  have hd := GlobalTheory.SignedHC.descEnum_unique (card_weight D C τ) hf hm
  show ⌊GlobalTheory.SignedHC.highestWeight _ (card_weight D C τ) i⌋ =
    ⌊(rowEntries D C τ).psiPar.getD i 0 - ((((rowEntries D C τ).psiPar.length : ℚ) - 1) / 2 - ((i : ℕ) : ℚ))⌋
  unfold GlobalTheory.SignedHC.highestWeight
  rw [hd, hlen]

/- English proof (translation)
Rewrite using `[GlobalTheory.CoefModel.realGL_coe, ← compAt_vtxPt hX u τ]`. Both sides reduce to the same expression.
-/
theorem realGL_vtxPt (W : G.Weil) {X : Node} (hX : PosOnb W X) (u : UG D.what₂.Tau (G.V X).rank) (τ : D.what₂.Tau) :
    (GlobalTheory.CoefModel.realGL W.θ (G.V X) (vtxPt W X u) τ : Matrix (Fin (G.V X).rank) (Fin (G.V X).rank) ℂ) =
      W.onb X τ * (u τ : Matrix (Fin (G.V X).rank) (Fin (G.V X).rank) ℂ) * (W.onb X τ)⁻¹ := by
  rw [GlobalTheory.CoefModel.realGL_coe, ← compAt_vtxPt hX u τ]
  rfl

end Grid

end GlobalTheory.CoefPsi

namespace GlobalTheory.CoefPsi

section Grid2

open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowReal Formalism.IndefR.Links

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} [DecidableEq D.what₂.Tau]

/- English proof (translation)
Simplify using `[rowComp, Fin.snoc, (rowSizes D).m_pos]`. Both sides reduce to the same expression.
-/
theorem rowComp_zero (g : Gc D.what₂.Tau (rowSizes D)) :
    rowComp (rowSizes D) g 0 = g.1 ⟨0, (rowSizes D).m_pos⟩ := by
  simp [rowComp, Fin.snoc, (rowSizes D).m_pos]
  rfl

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Establish `hr : (rowSizes D).nR 0 = (G.V (.top 0)).rank` using `(GlobalTheory.RowReal.rank_top G (Nat.zero_le _)).symm`. Establish `hl : ∀ τ (i : Fin (G.V (.top 0)).rank), (LaP G τ).w i = psiWt (rowEntries D sc.cGap) τ i`. Introduce `τ i`. Use `show (La D sc.cGap τ).w (Fin.cast (rank_Xp G) i) = hw (rowEntries D sc.cGap τ).psiPar i`. Rewrite using `[La_eq_hw]`.

Both sides reduce to the same expression. Take `⟨A0, hA0⟩` from `exists_equiv_cast _ _ hr (psiWt (rowEntries D sc.cGap)) (LaP G) hl`. Establish `hdet : ∀ τ, (W.onb (.top 0) τ).det ≠ 0`. Introduce `τ h`. Establish `e` using `congrArg Matrix.det (h0 τ)`.

Rewrite `e` using `[Matrix.det_mul, Matrix.det_mul, h, mul_zero, Matrix.det_one]`. Conclude with `zero_ne_one e`. Set `Bg : D.what₂.Tau → GL (Fin (G.V (.top 0)).rank) ℂ` to `fun τ => Matrix.GeneralLinearGroup.mkOfDetNeZero _ (hdet τ)`. Establish `hBg : ∀ τ, ((Bg τ : GL (Fin (G.V (.top 0)).rank) ℂ) : Matrix (Fin (G.V (.top 0)).rank) (Fin (G.V (.top 0)).rank) ℂ) = W.onb (.top 0) τ` using `fun τ => rfl`. Set `e : Formalism.L2.DIV.VV ℂ (LaP G) ≃ₗ[ℂ] Formalism.L2.DIV.VV ℂ (LaP G)` to `LinearEquiv.ofLinear (Formalism.L2.DIV.rhoK (LaP G) (invTrK Bg)⁻¹) (Formalism.L2.DIV.rhoK (LaP G) (invTrK Bg)) (LinearMap.ext fun x => by show (Formalism.L2.DIV.rhoK (LaP G) (invTrK Bg)⁻¹ * Formalism.L2.DIV.rhoK (LaP G) (invTrK Bg)) x = x`.

Rewrite using `[← map_mul, inv_mul_cancel, map_one]`. Use the proof step `rfl)`. Use the proof step `(LinearMap.ext fun x => by show (Formalism.L2.DIV.rhoK (LaP G) (invTrK Bg) * Formalism.L2.DIV.rhoK (LaP G) (invTrK Bg)⁻¹) x = x`. Rewrite using `[← map_mul, mul_inv_cancel, map_one]`. Use the proof step `rfl)`.

Use `⟨A0.trans e.dualMap, fun g F => ?_⟩` and prove the remaining obligations. Set `U : D.what₂.Tau → GL (Fin (G.V (.top 0)).rank) ℂ` to `fun τ => GlobalTheory.Branching.unitaryIncl _ (castU hr (g.1 ⟨0, (rowSizes D).m_pos⟩ τ))`. Establish `hM : GlobalTheory.CoefModel.realGL W.θ (G.V (.top 0)) ((kappa W g).1 ⟨0, (rowSizes D).m_pos⟩) = Bg * U * Bg⁻¹`. Use function extensionality and compare the values at `τ`. Apply `Units.ext` to reduce the goal to its premises.

Rewrite using `[kappa_fst]`. Use `(realGL_vtxPt W h0 (rowU G ⟨0, (rowSizes D).m_pos⟩ g) τ).trans ?_` and prove the remaining obligations. Simplify using `only [Pi.mul_apply, Pi.inv_apply, Units.val_mul, Matrix.coe_units_inv, hBg, U, GlobalTheory.Branching.unitaryIncl_coe]`. Apply the tactic sequence `all_goals rfl`. Establish `key : (invTrK Bg)⁻¹ * invTrK (GlobalTheory.CoefModel.realGL W.θ (G.V (.top 0)) ((kappa W g).1 ⟨0, (rowSizes D).m_pos⟩)⁻¹) = (invTrK U)⁻¹ * (invTrK Bg)⁻¹`.

Rewrite using `[map_inv, hM, map_inv, map_mul, map_mul, map_inv]`. Use `group`. Establish `main : (A0.trans e.dualMap) (weylRep _ (psiWt (rowEntries D sc.cGap)) (g.1 ⟨0, (rowSizes D).m_pos⟩) F) = (A0.trans e.dualMap) F ∘ₗ Formalism.L2.DIV.rhoK (LaP G) (invTrK (GlobalTheory.CoefModel.realGL W.θ (G.V (.top 0)) ((kappa W g).1 ⟨0, (rowSizes D).m_pos⟩)⁻¹))`. Use `LinearMap.ext fun y => ?_` and prove the remaining obligations. Use `show A0 (weylRep _ (psiWt (rowEntries D sc.cGap)) (g.1 ⟨0, (rowSizes D).m_pos⟩) F) (e y) = A0 F (e (Formalism.L2.DIV.rhoK (LaP G) (invTrK (GlobalTheory.CoefModel.realGL W.θ (G.V (.top 0)) ((kappa W g).1 ⟨0, (rowSizes D).m_pos⟩)⁻¹)) y))`.

Establish `hA1` using `LinearMap.congr_fun (hA0 (g.1 ⟨0, (rowSizes D).m_pos⟩) F) (e y)`. Rewrite `hA1` using `[LinearMap.comp_apply]`. Use `hA1.trans (congrArg (fun v => A0 F v) ?_)` and prove the remaining obligations. Use `show (Formalism.L2.DIV.rhoK (LaP G) (invTrK U)⁻¹ * Formalism.L2.DIV.rhoK (LaP G) (invTrK Bg)⁻¹) y = (Formalism.L2.DIV.rhoK (LaP G) (invTrK Bg)⁻¹ * Formalism.L2.DIV.rhoK (LaP G) (invTrK (GlobalTheory.CoefModel.realGL W.θ (G.V (.top 0)) ((kappa W g).1 ⟨0, (rowSizes D).m_pos⟩)⁻¹))) …`. Rewrite using `[← map_mul, ← map_mul, key]`.

Establish `e1 : psiRep (rowEntries D sc.cGap) g F = weylRep _ (psiWt (rowEntries D sc.cGap)) (g.1 ⟨0, (rowSizes D).m_pos⟩) F` using `by show weylRep _ _ (rowComp (rowSizes D) g 0) F = _`. Rewrite using `[rowComp_zero]`. Apply the tactic sequence `all_goals rfl`. Rewrite using `[e1]`. Conclude with `main`.
-/
theorem coefPsi (W : G.Weil) (h0 : PosOnb W (.top 0)) :
    ∃ A : weylSub ((rowSizes D).nR (0 : Fin ((rowSizes D).m + 1))) (psiWt (rowEntries D sc.cGap)) ≃ₗ[ℂ]
        Module.Dual ℂ (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus G W.θ).W,
      ∀ g F, A (psiRep (rowEntries D sc.cGap) g F) =
        A F ∘ₗ (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus G W.θ).ρ ((kappa W g).1 ⟨0, (rowSizes D).m_pos⟩)⁻¹ := by
  classical
  have hr : (rowSizes D).nR 0 = (G.V (.top 0)).rank := (GlobalTheory.RowReal.rank_top G (Nat.zero_le _)).symm
  have hl : ∀ τ (i : Fin (G.V (.top 0)).rank), (LaP G τ).w i = psiWt (rowEntries D sc.cGap) τ i := by
    intro τ i
    show (La D sc.cGap τ).w (Fin.cast (rank_Xp G) i) = hw (rowEntries D sc.cGap τ).psiPar i
    rw [La_eq_hw]
    rfl
  obtain ⟨A0, hA0⟩ := exists_equiv_cast _ _ hr (psiWt (rowEntries D sc.cGap)) (LaP G) hl
  have hdet : ∀ τ, (W.onb (.top 0) τ).det ≠ 0 := by
    intro τ h
    have e := congrArg Matrix.det (h0 τ)
    rw [Matrix.det_mul, Matrix.det_mul, h, mul_zero, Matrix.det_one] at e
    exact zero_ne_one e
  let Bg : D.what₂.Tau → GL (Fin (G.V (.top 0)).rank) ℂ := fun τ => Matrix.GeneralLinearGroup.mkOfDetNeZero _ (hdet τ)
  have hBg : ∀ τ, ((Bg τ : GL (Fin (G.V (.top 0)).rank) ℂ) : Matrix (Fin (G.V (.top 0)).rank) (Fin (G.V (.top 0)).rank) ℂ) =
      W.onb (.top 0) τ := fun τ => rfl
  let e : Formalism.L2.DIV.VV ℂ (LaP G) ≃ₗ[ℂ] Formalism.L2.DIV.VV ℂ (LaP G) :=
    LinearEquiv.ofLinear (Formalism.L2.DIV.rhoK (LaP G) (invTrK Bg)⁻¹) (Formalism.L2.DIV.rhoK (LaP G) (invTrK Bg))
      (LinearMap.ext fun x => by
        show (Formalism.L2.DIV.rhoK (LaP G) (invTrK Bg)⁻¹ * Formalism.L2.DIV.rhoK (LaP G) (invTrK Bg)) x = x
        rw [← map_mul, inv_mul_cancel, map_one]
        rfl)
      (LinearMap.ext fun x => by
        show (Formalism.L2.DIV.rhoK (LaP G) (invTrK Bg) * Formalism.L2.DIV.rhoK (LaP G) (invTrK Bg)⁻¹) x = x
        rw [← map_mul, mul_inv_cancel, map_one]
        rfl)
  refine ⟨A0.trans e.dualMap, fun g F => ?_⟩
  let U : D.what₂.Tau → GL (Fin (G.V (.top 0)).rank) ℂ := fun τ =>
    GlobalTheory.Branching.unitaryIncl _ (castU hr (g.1 ⟨0, (rowSizes D).m_pos⟩ τ))
  have hM : GlobalTheory.CoefModel.realGL W.θ (G.V (.top 0)) ((kappa W g).1 ⟨0, (rowSizes D).m_pos⟩) = Bg * U * Bg⁻¹ := by
    funext τ
    apply Units.ext
    rw [kappa_fst]
    refine (realGL_vtxPt W h0 (rowU G ⟨0, (rowSizes D).m_pos⟩ g) τ).trans ?_
    simp only [Pi.mul_apply, Pi.inv_apply, Units.val_mul, Matrix.coe_units_inv, hBg, U, GlobalTheory.Branching.unitaryIncl_coe]
    all_goals rfl
  have key : (invTrK Bg)⁻¹ * invTrK (GlobalTheory.CoefModel.realGL W.θ (G.V (.top 0)) ((kappa W g).1 ⟨0, (rowSizes D).m_pos⟩)⁻¹) =
      (invTrK U)⁻¹ * (invTrK Bg)⁻¹ := by
    rw [map_inv, hM, map_inv, map_mul, map_mul, map_inv]
    group
  have main : (A0.trans e.dualMap) (weylRep _ (psiWt (rowEntries D sc.cGap)) (g.1 ⟨0, (rowSizes D).m_pos⟩) F) =
      (A0.trans e.dualMap) F ∘ₗ Formalism.L2.DIV.rhoK (LaP G)
        (invTrK (GlobalTheory.CoefModel.realGL W.θ (G.V (.top 0)) ((kappa W g).1 ⟨0, (rowSizes D).m_pos⟩)⁻¹)) := by
    refine LinearMap.ext fun y => ?_
    show A0 (weylRep _ (psiWt (rowEntries D sc.cGap)) (g.1 ⟨0, (rowSizes D).m_pos⟩) F) (e y) =
      A0 F (e (Formalism.L2.DIV.rhoK (LaP G)
        (invTrK (GlobalTheory.CoefModel.realGL W.θ (G.V (.top 0)) ((kappa W g).1 ⟨0, (rowSizes D).m_pos⟩)⁻¹)) y))
    have hA1 := LinearMap.congr_fun (hA0 (g.1 ⟨0, (rowSizes D).m_pos⟩) F) (e y)
    rw [LinearMap.comp_apply] at hA1
    refine hA1.trans (congrArg (fun v => A0 F v) ?_)
    show (Formalism.L2.DIV.rhoK (LaP G) (invTrK U)⁻¹ * Formalism.L2.DIV.rhoK (LaP G) (invTrK Bg)⁻¹) y =
      (Formalism.L2.DIV.rhoK (LaP G) (invTrK Bg)⁻¹ *
        Formalism.L2.DIV.rhoK (LaP G) (invTrK (GlobalTheory.CoefModel.realGL W.θ (G.V (.top 0)) ((kappa W g).1 ⟨0, (rowSizes D).m_pos⟩)⁻¹))) y
    rw [← map_mul, ← map_mul, key]
  have e1 : psiRep (rowEntries D sc.cGap) g F =
      weylRep _ (psiWt (rowEntries D sc.cGap)) (g.1 ⟨0, (rowSizes D).m_pos⟩) F := by
    show weylRep _ _ (rowComp (rowSizes D) g 0) F = _
    rw [rowComp_zero]
    all_goals rfl
  rw [e1]
  exact main

end Grid2

end GlobalTheory.CoefPsi
