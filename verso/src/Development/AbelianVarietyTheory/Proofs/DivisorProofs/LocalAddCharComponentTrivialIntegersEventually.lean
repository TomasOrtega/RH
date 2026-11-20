import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegerAddConjEqOneOfFormallyUnramified
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.AdelicU GlobalTheory.WeilM

noncomputable section

namespace GlobalTheory

/- English proof (translation)
Assume the negation of the conclusion as `hw`. Establish `hd : 0 < ‖w - 1‖` using `norm_pos_iff.2 (sub_ne_zero.2 hw)`. Take `⟨N, hN⟩` from `exists_nat_gt (1 / ‖w - 1‖)`. Establish `hre : ∀ k : ℕ, 1 / 2 < (w ^ k).re`. Introduce `k`.

Establish `h1` using `(Complex.abs_re_le_norm (w ^ k - 1)).trans_lt (h k)`. Rewrite `h1` using `[Complex.sub_re, Complex.one_re]`. Combine the linear relations using `[(abs_lt.1 h1).1]`. Establish `hsum : (N : ℝ) / 2 ≤ (∑ k ∈ Finset.range N, w ^ k).re`. Rewrite using `[Complex.re_sum]`.

Use `Finset.sum_le_sum (s := Finset.range N) (fun k _ => (hre k).le)` as an intermediate fact. Simplify `this` using `[div_eq_mul_inv, mul_comm]`. Establish `hnorm : (N : ℝ) / 2 ≤ ‖∑ k ∈ Finset.range N, w ^ k‖` using `hsum.trans (Complex.re_le_norm _)`. Establish `hgeom : ‖∑ k ∈ Finset.range N, w ^ k‖ * ‖w - 1‖ < 1 / 2`. Rewrite using `[← norm_mul, geom_sum_mul]`.

Conclude with `h N`. Establish `: (N : ℝ) / 2 * ‖w - 1‖ < 1 / 2` using `lt_of_le_of_lt (mul_le_mul_of_nonneg_right hnorm hd.le) hgeom`. Establish `h2 : (N : ℝ) * ‖w - 1‖ < 1` using `by linarith`. Rewrite `hN` using `[div_lt_iff₀ hd]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem eq_one_of_forall_norm_pow_sub_one_lt (w : ℂ) (h : ∀ n : ℕ, ‖w ^ n - 1‖ < 1 / 2) : w = 1 := by
  by_contra hw
  have hd : 0 < ‖w - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hw)
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ‖w - 1‖)
  have hre : ∀ k : ℕ, 1 / 2 < (w ^ k).re := by
    intro k
    have h1 := (Complex.abs_re_le_norm (w ^ k - 1)).trans_lt (h k)
    rw [Complex.sub_re, Complex.one_re] at h1
    linarith [(abs_lt.1 h1).1]
  have hsum : (N : ℝ) / 2 ≤ (∑ k ∈ Finset.range N, w ^ k).re := by
    rw [Complex.re_sum]
    have := Finset.sum_le_sum (s := Finset.range N) (fun k _ => (hre k).le)
    simpa [div_eq_mul_inv, mul_comm] using this
  have hnorm : (N : ℝ) / 2 ≤ ‖∑ k ∈ Finset.range N, w ^ k‖ :=
    hsum.trans (Complex.re_le_norm _)
  have hgeom : ‖∑ k ∈ Finset.range N, w ^ k‖ * ‖w - 1‖ < 1 / 2 := by
    rw [← norm_mul, geom_sum_mul]; exact h N
  have : (N : ℝ) / 2 * ‖w - 1‖ < 1 / 2 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hnorm hd.le) hgeom
  have h2 : (N : ℝ) * ‖w - 1‖ < 1 := by linarith
  rw [div_lt_iff₀ hd] at hN
  linarith

open Filter Topology in

/- English proof (translation)
Set `ι : (∀ v : HeightOneSpectrum (𝓞 F), ↥(v.adicCompletionIntegers F)) → AF F` to `fun y => LinearMap.inr F (Ainf F) (Af F) (RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite (fun v => ⟨(y v).1, (y v).2⟩))`. Establish `hι : Continuous ι`. Establish `hs : Continuous (fun y : (∀ v : HeightOneSpectrum (𝓞 F), ↥(v.adicCompletionIntegers F)) => RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite (fun v => ⟨(y v).1, …` using `RestrictedProduct.isEmbedding_structureMap.continuous`. Conclude with `continuous_const.prodMk hs`. Establish `hopen : IsOpen {y | ‖ψ (ι y) - 1‖ < 1 / 2}` using `isOpen_lt ((hψ.comp hι).sub continuous_const).norm continuous_const`.

Establish `h0 : (0 : ∀ v : HeightOneSpectrum (𝓞 F), ↥(v.adicCompletionIntegers F)) ∈ {y | ‖ψ (ι y) - 1‖ < 1 / 2}`. Establish `: ι 0 = 0`. Use `Prod.ext rfl ?_` and prove the remaining obligations. Use `show RestrictedProduct.structureMap _ _ _ _ = (0 : Af F)`. Use `af_ext fun w => ?_` and prove the remaining obligations.

Both sides reduce to the same expression. Simplify using `[this, AddChar.map_zero_eq_one]`. Take `⟨I, u, hu, hsub⟩` from `isOpen_pi_iff.1 hopen 0 h0`. Establish `key : ∀ v, v ∉ I → ∀ x ∈ v.adicCompletionIntegers F, ‖GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.psiLoc ψ v x - 1‖ < 1 / 2`. Introduce `v hv x hx`.

Set `y : ∀ u : HeightOneSpectrum (𝓞 F), ↥(u.adicCompletionIntegers F)` to `Pi.single v ⟨x, hx⟩`. Establish `hy : y ∈ (I : Set _).pi u`. Introduce `a ha`. Establish `hav : a ≠ v` using `fun e => hv (e ▸ ha)`. Establish `: y a = 0` using `Pi.single_eq_of_ne hav _`.

Rewrite using `[this]`. Conclude with `(hu a ha).2`. Establish `hmem` using `hsub hy`. Establish `hιy : ι y = LinearMap.inr F (Ainf F) (Af F) (singleFin v x)`. Use `congrArg (LinearMap.inr F (Ainf F) (Af F)) (af_ext fun w => ?_)` and prove the remaining obligations.

Distinguish the cases in `e : w = v`. Substitute `e` using the available equality. Rewrite using `[evalV_singleFin_self] show ((y w : w.adicCompletion F)) = x`. Simplify using `[y]`. Rewrite using `[evalV_singleFin_ne e] show ((y w : w.adicCompletion F)) = 0`.

Simplify using `[y, Pi.single_eq_of_ne e]`. Simplify `hmem` using `[hιy, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.psiLoc]`. Establish `hfin : {v : HeightOneSpectrum (𝓞 F) | ¬ ∀ x ∈ v.adicCompletionIntegers F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.psiLoc ψ v x = 1}.Finite`. Use `(I.finite_toSet).subset fun v hv => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hvI`.

Apply `hv` to reduce the goal to its premises. Introduce `x hx`. Use `eq_one_of_forall_norm_pow_sub_one_lt _ fun n => ?_` and prove the remaining obligations. Establish `hnx : n • x ∈ v.adicCompletionIntegers F` using `nsmul_mem hx n`. Use `key v hvI (n • x) hnx` as an intermediate fact.

Establish `hpow : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.psiLoc ψ v (n • x) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.psiLoc ψ v x ^ n`. Simplify using `only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.psiLoc, map_nsmul]`. Conclude with `AddChar.map_nsmul_eq_pow ψ n _`. Rewrite `this` using `[hpow]`. Then use the resulting hypothesis. Conclude with `Filter.eventually_cofinite.2 hfin`.
-/
theorem psiLoc_eventually_trivial_integers {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ)
    (hψ : Continuous ψ) :
    ∀ᶠ v in Filter.cofinite, ∀ x ∈ (v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F,
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.psiLoc ψ v x = 1 := by
  classical
  let ι : (∀ v : HeightOneSpectrum (𝓞 F), ↥(v.adicCompletionIntegers F)) → AF F := fun y =>
    LinearMap.inr F (Ainf F) (Af F)
      (RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
        (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite
        (fun v => ⟨(y v).1, (y v).2⟩))
  have hι : Continuous ι := by
    have hs : Continuous (fun y : (∀ v : HeightOneSpectrum (𝓞 F), ↥(v.adicCompletionIntegers F)) =>
        RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
          (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite
          (fun v => ⟨(y v).1, (y v).2⟩)) :=
      RestrictedProduct.isEmbedding_structureMap.continuous
    exact continuous_const.prodMk hs
  have hopen : IsOpen {y | ‖ψ (ι y) - 1‖ < 1 / 2} :=
    isOpen_lt ((hψ.comp hι).sub continuous_const).norm continuous_const
  have h0 : (0 : ∀ v : HeightOneSpectrum (𝓞 F), ↥(v.adicCompletionIntegers F)) ∈ {y | ‖ψ (ι y) - 1‖ < 1 / 2} := by
    have : ι 0 = 0 := by
      refine Prod.ext rfl ?_
      show RestrictedProduct.structureMap _ _ _ _ = (0 : Af F)
      refine af_ext fun w => ?_
      rfl
    simp [this, AddChar.map_zero_eq_one]
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.1 hopen 0 h0
  have key : ∀ v, v ∉ I → ∀ x ∈ v.adicCompletionIntegers F, ‖GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.psiLoc ψ v x - 1‖ < 1 / 2 := by
    intro v hv x hx
    let y : ∀ u : HeightOneSpectrum (𝓞 F), ↥(u.adicCompletionIntegers F) := Pi.single v ⟨x, hx⟩
    have hy : y ∈ (I : Set _).pi u := by
      intro a ha
      have hav : a ≠ v := fun e => hv (e ▸ ha)
      have : y a = 0 := Pi.single_eq_of_ne hav _
      rw [this]; exact (hu a ha).2
    have hmem := hsub hy
    have hιy : ι y = LinearMap.inr F (Ainf F) (Af F) (singleFin v x) := by
      refine congrArg (LinearMap.inr F (Ainf F) (Af F)) (af_ext fun w => ?_)
      by_cases e : w = v
      · subst e; rw [evalV_singleFin_self]
        show ((y w : w.adicCompletion F)) = x
        simp [y]
      · rw [evalV_singleFin_ne e]
        show ((y w : w.adicCompletion F)) = 0
        simp [y, Pi.single_eq_of_ne e]
    simpa [hιy, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.psiLoc] using hmem
  have hfin : {v : HeightOneSpectrum (𝓞 F) | ¬ ∀ x ∈ v.adicCompletionIntegers F,
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.psiLoc ψ v x = 1}.Finite := by
    refine (I.finite_toSet).subset fun v hv => ?_
    by_contra hvI
    apply hv
    intro x hx
    refine eq_one_of_forall_norm_pow_sub_one_lt _ fun n => ?_
    have hnx : n • x ∈ v.adicCompletionIntegers F := nsmul_mem hx n
    have := key v hvI (n • x) hnx
    have hpow : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.psiLoc ψ v (n • x) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.psiLoc ψ v x ^ n := by
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.psiLoc, map_nsmul]
      exact AddChar.map_nsmul_eq_pow ψ n _
    rwa [hpow] at this
  exact Filter.eventually_cofinite.2 hfin

end GlobalTheory
