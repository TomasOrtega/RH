import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplTupBijective
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMinorsMemInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDetCharInvariantsLeSpanProdMaximalMinors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PluckerMinorsProportional
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PluckerStar

open MvPolynomial Matrix

variable {a a' : ℕ}

def joinFun (h : a + a' = a + a') (s : {s : Fin a → Fin (a + a') // StrictMono s}) : Fin (a + a') → Fin (a + a') :=
  Fin.addCases (fun i => s.1 i) (fun j => (GlobalTheory.BotMatch.complSub h s).1 j)

/- English proof (translation)
Establish `hr` using `GlobalTheory.BotMatch.range_complSub h s`. Establish `hc : ∀ j i, (GlobalTheory.BotMatch.complSub h s).1 j ≠ s.1 i`. Introduce `j i e`. Establish `: (GlobalTheory.BotMatch.complSub h s).1 j ∈ Set.range (GlobalTheory.BotMatch.complSub h s).1` using `⟨j, rfl⟩`. Rewrite `this` using `[hr, e]`.

Conclude with `this ⟨i, rfl⟩`. Introduce `k₁ k₂`. Apply the tactic sequence `refine Fin.addCases (fun i => ?_) (fun j => ?_) k₁ <;> refine Fin.addCases (fun i' => ?_) (fun j' => ?_) k₂ <;>`. Apply the tactic sequence `simp only [joinFun, Fin.addCases_left, Fin.addCases_right] <;> intro e`. Rewrite using `[s.2.injective e]`.

Conclude with `absurd e.symm (hc j' i)`. Conclude with `absurd e (hc j i')`. Rewrite using `[(GlobalTheory.BotMatch.complSub h s).2.injective e]`.
-/
theorem joinFun_injective (h : a + a' = a + a') (s : {s : Fin a → Fin (a + a') // StrictMono s}) :
    Function.Injective (joinFun h s) := by
  have hr := GlobalTheory.BotMatch.range_complSub h s
  have hc : ∀ j i, (GlobalTheory.BotMatch.complSub h s).1 j ≠ s.1 i := by
    intro j i e
    have : (GlobalTheory.BotMatch.complSub h s).1 j ∈ Set.range (GlobalTheory.BotMatch.complSub h s).1 := ⟨j, rfl⟩
    rw [hr, e] at this
    exact this ⟨i, rfl⟩
  intro k₁ k₂
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k₁ <;> refine Fin.addCases (fun i' => ?_) (fun j' => ?_) k₂ <;>
    simp only [joinFun, Fin.addCases_left, Fin.addCases_right] <;> intro e
  · rw [s.2.injective e]
  · exact absurd e.symm (hc j' i)
  · exact absurd e (hc j i')
  · rw [(GlobalTheory.BotMatch.complSub h s).2.injective e]

def joinPerm (h : a + a' = a + a') (s : {s : Fin a → Fin (a + a') // StrictMono s}) : Equiv.Perm (Fin (a + a')) :=
  Equiv.ofBijective (joinFun h s) (Finite.injective_iff_bijective.mp (joinFun_injective h s))

/- English proof (translation)
Simplify using `[joinPerm, joinFun]`.
-/
theorem joinPerm_castAdd (h : a + a' = a + a') (s : {s : Fin a → Fin (a + a') // StrictMono s}) (i : Fin a) :
    joinPerm h s (Fin.castAdd a' i) = s.1 i := by
  simp [joinPerm, joinFun]

/- English proof (translation)
Simplify using `[joinPerm, joinFun]`.
-/
theorem joinPerm_natAdd (h : a + a' = a + a') (s : {s : Fin a → Fin (a + a') // StrictMono s}) (j : Fin a') :
    joinPerm h s (Fin.natAdd a j) = (GlobalTheory.BotMatch.complSub h s).1 j := by
  simp [joinPerm, joinFun]

/- English proof (translation)
Establish `hU : IsUnit N.det` using `isUnit_iff_ne_zero.mpr hN`. Establish `h1 : N⁻¹.submatrix id π * N.submatrix π id = 1`. Rewrite using `[Matrix.submatrix_mul_equiv (e₂ := π) (e₃ := id)]`. Simplify using `[Matrix.nonsing_inv_mul _ hU]`. Use `set e := (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a'))`.

Establish `h2 : (N⁻¹.submatrix id π).submatrix e e * (N.submatrix π id).submatrix e e = 1`. Rewrite using `[Matrix.submatrix_mul_equiv (e₂ := e), h1, Matrix.submatrix_one_equiv]`. Establish `h3` using `GlobalTheory.det_mul_det_toBlocks₂₂_of_mul_eq_one _ _ h2`. Establish `hd : ((N⁻¹.submatrix id π).submatrix e e).det = ((Equiv.Perm.sign π : ℤ) : ℂ) * (N.det)⁻¹`. Rewrite using `[Matrix.det_submatrix_equiv_self, Matrix.det_permute', Matrix.det_nonsing_inv, Ring.inverse_eq_inv']`.

Rewrite `h3` using `[hd]`. Establish `hA : (Matrix.of fun i i' : Fin a => N⁻¹ (Fin.castAdd a' i') (π (Fin.castAdd a' i))) = ((N⁻¹.submatrix id π).submatrix e e).toBlocks₁₁.transpose`. Use extensionality with `i i'`. Simplify using `[Matrix.toBlocks₁₁, e]`. Establish `hB : (Matrix.of fun j j' : Fin a' => N (π (Fin.natAdd a j)) (Fin.natAdd a j')) = ((N.submatrix π id).submatrix e e).toBlocks₂₂`.

Use extensionality with `j j'`. Simplify using `[Matrix.toBlocks₂₂, e]`. Rewrite using `[hA, hB, Matrix.det_transpose, ← h3]`.
-/
theorem jacobi (N : Matrix (Fin (a + a')) (Fin (a + a')) ℂ) (hN : N.det ≠ 0) (π : Equiv.Perm (Fin (a + a'))) :
    (Matrix.of fun i i' : Fin a => N⁻¹ (Fin.castAdd a' i') (π (Fin.castAdd a' i))).det =
      ((Equiv.Perm.sign π : ℤ) : ℂ) * (N.det)⁻¹ *
        (Matrix.of fun j j' : Fin a' => N (π (Fin.natAdd a j)) (Fin.natAdd a j')).det := by
  have hU : IsUnit N.det := isUnit_iff_ne_zero.mpr hN
  have h1 : N⁻¹.submatrix id π * N.submatrix π id = 1 := by
    rw [Matrix.submatrix_mul_equiv (e₂ := π) (e₃ := id)]
    simp [Matrix.nonsing_inv_mul _ hU]
  set e := (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a'))
  have h2 : (N⁻¹.submatrix id π).submatrix e e * (N.submatrix π id).submatrix e e = 1 := by
    rw [Matrix.submatrix_mul_equiv (e₂ := e), h1, Matrix.submatrix_one_equiv]
  have h3 := GlobalTheory.det_mul_det_toBlocks₂₂_of_mul_eq_one _ _ h2
  have hd : ((N⁻¹.submatrix id π).submatrix e e).det = ((Equiv.Perm.sign π : ℤ) : ℂ) * (N.det)⁻¹ := by
    rw [Matrix.det_submatrix_equiv_self, Matrix.det_permute', Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  rw [hd] at h3
  have hA : (Matrix.of fun i i' : Fin a => N⁻¹ (Fin.castAdd a' i') (π (Fin.castAdd a' i))) =
      ((N⁻¹.submatrix id π).submatrix e e).toBlocks₁₁.transpose := by
    ext i i'; simp [Matrix.toBlocks₁₁, e]
  have hB : (Matrix.of fun j j' : Fin a' => N (π (Fin.natAdd a j)) (Fin.natAdd a j')) =
      ((N.submatrix π id).submatrix e e).toBlocks₂₂ := by
    ext j j'; simp [Matrix.toBlocks₂₂, e]
  rw [hA, hB, Matrix.det_transpose, ← h3]

variable {ι : Type} [Fintype ι]

/- English proof (translation)
Establish `hQS : Q * S = 0` using `MvPolynomial.funext fun x => by`. Distinguish the cases in `hx : eval x S = 0`. Simplify using `[hx]`. Simplify using `[h x hx]`. Establish `hS0 : S ≠ 0`.

Introduce and unpack `rfl`. Take `⟨x, hx⟩` from `hS`. Simplify using `at hx`. Conclude with `(mul_eq_zero.mp hQS).resolve_right hS0`.
-/
theorem eq_zero_of_eval {σ : Type} (Q S : MvPolynomial σ ℂ) (hS : ∃ x, eval x S ≠ 0)
    (h : ∀ x, eval x S ≠ 0 → eval x Q = 0) : Q = 0 := by
  have hQS : Q * S = 0 := MvPolynomial.funext fun x => by
    by_cases hx : eval x S = 0
    · simp [hx]
    · simp [h x hx]
  have hS0 : S ≠ 0 := by
    rintro rfl
    obtain ⟨x, hx⟩ := hS
    simp at hx
  exact (mul_eq_zero.mp hQS).resolve_right hS0

/- English proof (translation)
Establish `: (eval x).comp (GlobalTheory.MinorFrame.rowSub κ : GlobalTheory.MinorFrame.Pol ι d b →ₐ[ℂ] GlobalTheory.MinorFrame.Pol ι d b).toRingHom = eval (fun y => ∑ i', κ y.1 i' y.2.1 * x (y.1, i', y.2.2))`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `r`. Simplify using `[GlobalTheory.MinorFrame.rowSub]`. Introduce `y`.

Simplify using `[GlobalTheory.MinorFrame.rowSub]`. Conclude with `RingHom.congr_fun this P`.
-/
theorem eval_rowSub {d b : ℕ} (κ : ι → Matrix (Fin d) (Fin d) ℂ) (x : ι × Fin d × Fin b → ℂ)
    (P : GlobalTheory.MinorFrame.Pol ι d b) :
    eval x (GlobalTheory.MinorFrame.rowSub κ P) = eval (fun y => ∑ i', κ y.1 i' y.2.1 * x (y.1, i', y.2.2)) P := by
  have : (eval x).comp (GlobalTheory.MinorFrame.rowSub κ : GlobalTheory.MinorFrame.Pol ι d b →ₐ[ℂ] GlobalTheory.MinorFrame.Pol ι d b).toRingHom =
      eval (fun y => ∑ i', κ y.1 i' y.2.1 * x (y.1, i', y.2.2)) := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [GlobalTheory.MinorFrame.rowSub]
    · intro y; simp [GlobalTheory.MinorFrame.rowSub]
  exact RingHom.congr_fun this P

def xPt (N : ι → Matrix (Fin (a + a')) (Fin (a + a')) ℂ) : ι × Fin (a + a') × Fin a → ℂ :=
  fun y => (N y.1)⁻¹ (Fin.castAdd a' y.2.2) y.2.1

def yPt (N : ι → Matrix (Fin (a + a')) (Fin (a + a')) ℂ) : ι × Fin (a + a') × Fin a' → ℂ :=
  fun y => N y.1 y.2.1 (Fin.natAdd a y.2.2)

/- English proof (translation)
Rewrite using `[GlobalTheory.MinorFrame.minorAt, RingHom.map_det]`. Use `congr 1`. Use extensionality with `i i'`. Simplify using the standard rewrite rules.
-/
theorem eval_minorAt {d b : ℕ} (x : ι × Fin d × Fin b → ℂ) (τ : ι) (s : Fin b → Fin d) :
    eval x (GlobalTheory.MinorFrame.minorAt τ s) = (Matrix.of fun i i' : Fin b => x (τ, s i, i')).det := by
  rw [GlobalTheory.MinorFrame.minorAt, RingHom.map_det]
  congr 1
  ext i i'
  simp

/- English proof (translation)
Rewrite using `[eval_minorAt, eval_minorAt]`. Use `jacobi (N τ) hN (joinPerm h s)` as an intermediate fact. Simplify using `only [joinPerm_castAdd, joinPerm_natAdd] at this`. Conclude with `this`.
-/
theorem eval_xPt_minorAt (h : a + a' = a + a') (N : ι → Matrix (Fin (a + a')) (Fin (a + a')) ℂ) (τ : ι)
    (hN : (N τ).det ≠ 0) (s : {s : Fin a → Fin (a + a') // StrictMono s}) :
    eval (xPt N) (GlobalTheory.MinorFrame.minorAt τ s.1) =
      ((Equiv.Perm.sign (joinPerm h s) : ℤ) : ℂ) * ((N τ).det)⁻¹ *
        eval (yPt N) (GlobalTheory.MinorFrame.minorAt τ (GlobalTheory.BotMatch.complSub h s).1) := by
  rw [eval_minorAt, eval_minorAt]
  have := jacobi (N τ) hN (joinPerm h s)
  simp only [joinPerm_castAdd, joinPerm_natAdd] at this
  exact this

def sgn {n : ι → ℕ} (h : a + a' = a + a') (T : GlobalTheory.MinorFrame.Tup ι a (a + a') n) : ℤˣ :=
  ∏ τ, ∏ j, Equiv.Perm.sign (joinPerm h (T τ j))

def cTup {n : ι → ℕ} (h : a + a' = a + a') (T : GlobalTheory.MinorFrame.Tup ι a (a + a') n) : GlobalTheory.MinorFrame.Tup ι a' (a + a') n :=
  fun τ k => GlobalTheory.BotMatch.complSub h (T τ k)

def lam (n : ι → ℕ) (N : ι → Matrix (Fin (a + a')) (Fin (a + a')) ℂ) : ℂ := ∏ τ, ((N τ).det)⁻¹ ^ n τ

/- English proof (translation)
Simplify using `only [GlobalTheory.MinorFrame.prodMinors, map_prod, eval_xPt_minorAt h N _ (hN _), Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, lam, sgn, cTup, Units.coe_prod, Int.cast_prod]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eval_xPt_prodMinors {n : ι → ℕ} (h : a + a' = a + a') (N : ι → Matrix (Fin (a + a')) (Fin (a + a')) ℂ)
    (hN : ∀ τ, (N τ).det ≠ 0) (T : GlobalTheory.MinorFrame.Tup ι a (a + a') n) :
    eval (xPt N) (GlobalTheory.MinorFrame.prodMinors T) =
      lam n N * (((sgn h T : ℤˣ) : ℤ) : ℂ) * eval (yPt N) (GlobalTheory.MinorFrame.prodMinors (cTup h T)) := by
  simp only [GlobalTheory.MinorFrame.prodMinors, map_prod, eval_xPt_minorAt h N _ (hN _), Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, lam, sgn, cTup, Units.coe_prod, Int.cast_prod]
  ring

def bottomMinors : GlobalTheory.MinorFrame.Pol ι (a + a') a' := ∏ τ, GlobalTheory.MinorFrame.minorAt τ (fun j : Fin a' => Fin.natAdd a j)

/- English proof (translation)
Simplify using `only [bottomMinors, map_prod, eval_minorAt]`.
-/
theorem eval_bottomMinors (y : ι × Fin (a + a') × Fin a' → ℂ) :
    eval y (bottomMinors (a := a)) = ∏ τ, (Matrix.of fun j j' : Fin a' => y (τ, Fin.natAdd a j, j')).det := by
  simp only [bottomMinors, map_prod, eval_minorAt]

/- English proof (translation)
Use `⟨yPt (fun _ => 1), ?_⟩` and prove the remaining obligations. Rewrite using `[eval_bottomMinors, Finset.prod_ne_zero_iff]`. Introduce `τ _`. Establish `: (Matrix.of fun j j' : Fin a' => yPt (a` using `a) (ι := ι) (fun _ => 1) (τ, Fin.natAdd a j, j')) = 1 := by`. Use extensionality with `j j'`.

Simplify using `[yPt, Matrix.one_apply]`. Rewrite using `[this, Matrix.det_one]`. Conclude with `one_ne_zero`.
-/
theorem exists_eval_bottomMinors_ne_zero : ∃ y : ι × Fin (a + a') × Fin a' → ℂ, eval y (bottomMinors (a := a)) ≠ 0 := by
  refine ⟨yPt (fun _ => 1), ?_⟩
  rw [eval_bottomMinors, Finset.prod_ne_zero_iff]
  intro τ _
  have : (Matrix.of fun j j' : Fin a' => yPt (a := a) (ι := ι) (fun _ => 1) (τ, Fin.natAdd a j, j')) = 1 := by
    ext j j'
    simp [yPt, Matrix.one_apply]
  rw [this, Matrix.det_one]
  exact one_ne_zero

/- English proof (translation)
Rewrite `hy` using `[eval_bottomMinors, Finset.prod_ne_zero_iff]`. Use `⟨fun τ => (Matrix.fromBlocks (1 : Matrix (Fin a) (Fin a) ℂ) (Matrix.of fun i j => y (τ, Fin.castAdd a' i, j)) 0 (Matrix.of fun i j => y (τ, Fin.natAdd a i, j))).reindex finSumFinEquiv finSumFinEquiv, fun τ => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul]`. Conclude with `hy τ (Finset.mem_univ _)`. Use function extensionality and compare the values at `⟨τ, k, j⟩`.

Simplify using `only [yPt, Matrix.reindex_apply, Matrix.submatrix_apply]`. Apply the tactic sequence `refine Fin.addCases (fun i => ?_) (fun i => ?_) k <;> simp`.
-/
theorem exists_frame (y : ι × Fin (a + a') × Fin a' → ℂ) (hy : eval y (bottomMinors (a := a)) ≠ 0) :
    ∃ N : ι → Matrix (Fin (a + a')) (Fin (a + a')) ℂ, (∀ τ, (N τ).det ≠ 0) ∧ yPt N = y := by
  rw [eval_bottomMinors, Finset.prod_ne_zero_iff] at hy
  refine ⟨fun τ => (Matrix.fromBlocks (1 : Matrix (Fin a) (Fin a) ℂ) (Matrix.of fun i j => y (τ, Fin.castAdd a' i, j)) 0
    (Matrix.of fun i j => y (τ, Fin.natAdd a i, j))).reindex finSumFinEquiv finSumFinEquiv, fun τ => ?_, ?_⟩
  · rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul]
    exact hy τ (Finset.mem_univ _)
  · funext ⟨τ, k, j⟩
    simp only [yPt, Matrix.reindex_apply, Matrix.submatrix_apply]
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k <;> simp

/- English proof (translation)
Set `A : (GlobalTheory.MinorFrame.Tup ι a (a + a') n → ℂ) →ₗ[ℂ] GlobalTheory.MinorFrame.Pol ι (a + a') a` to `Fintype.linearCombination ℂ (fun T => GlobalTheory.MinorFrame.prodMinors T)`. Set `B : (GlobalTheory.MinorFrame.Tup ι a (a + a') n → ℂ) →ₗ[ℂ] GlobalTheory.MinorFrame.Pol ι (a + a') a'` to `Fintype.linearCombination ℂ (fun T => (((sgn h T : ℤˣ) : ℤ) : ℂ) • GlobalTheory.MinorFrame.prodMinors (cTup h T))`. Establish `key : ∀ c N, (∀ τ, (N τ).det ≠ 0) → eval (xPt N) (A c) = lam n N * eval (yPt N) (B c)`. Introduce `c N hN`. Simplify using `only [A, B, Fintype.linearCombination_apply, map_sum, smul_eq_C_mul, eval_mul, eval_C, Finset.mul_sum, eval_xPt_prodMinors h N hN]`.

Use `Finset.sum_congr rfl fun T _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `hlam : ∀ N : ι → Matrix (Fin (a + a')) (Fin (a + a')) ℂ, (∀ τ, (N τ).det ≠ 0) → lam n N ≠ 0`. Introduce `N hN`. Conclude with `Finset.prod_ne_zero_iff.mpr fun τ _ => pow_ne_zero _ (inv_ne_zero (hN τ))`.

Establish `hker : LinearMap.ker A ≤ LinearMap.ker B`. Introduce `c hc`. Rewrite `hc`, the goal using `[LinearMap.mem_ker]`. Apply `eq_zero_of_eval _ (bottomMinors (a := a)) exists_eval_bottomMinors_ne_zero` to reduce the goal to its premises. Introduce `y hy`.

Take `⟨N, hN, rfl⟩` from `exists_frame y hy`. Use `key c N hN` as an intermediate fact. Rewrite `this` using `[hc, map_zero]`. Conclude with `(mul_eq_zero.mp this.symm).resolve_left (hlam N hN)`. Set `f : LinearMap.range A →ₗ[ℂ] GlobalTheory.MinorFrame.Pol ι (a + a') a'` to `((LinearMap.ker A).liftQ B hker).comp A.quotKerEquivRange.symm.toLinearMap`.

Take `⟨Pl, hPl⟩` from `LinearMap.exists_extend f`. Establish `hPlA : ∀ c, Pl (A c) = B c`. Introduce `c`. Use `LinearMap.congr_fun hPl ⟨A c, LinearMap.mem_range_self A c⟩` as an intermediate fact. Simplify using `only [LinearMap.comp_apply, Submodule.subtype_apply] at this`.

Rewrite using `[this]`. Simplify using `only [f, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply]`. Establish `hsingle : ∀ T, A (Pi.single T 1) = GlobalTheory.MinorFrame.prodMinors T`. Introduce `T`. Simplify using `[A, Fintype.linearCombination_apply_single]`.

Establish `hrange : ∀ Q ∈ GlobalTheory.MinorFrame.inv (ι` using `ι) a (a + a') n, ∃ c, A c = Q := by`. Introduce `Q hQ`. Establish `hle : Submodule.span ℂ (Set.range (GlobalTheory.MinorFrame.prodMinors (ι` using `ι) (a := a) (d := a + a') (n := n))) ≤ LinearMap.range A := by`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨T, rfl⟩`.

Conclude with `⟨Pi.single T 1, hsingle T⟩`. Conclude with `hle (GlobalTheory.MinorFrame.inv_le_span_prodMinors a (a + a') n hQ)`. Use `⟨Pl, fun T => ?_, fun κ P hP => ?_⟩` and prove the remaining obligations. Rewrite using `[← hsingle T, hPlA]`. Simplify using `[B, Fintype.linearCombination_apply_single]`.

Take `⟨c, rfl⟩` from `hrange P hP`. Take `⟨c', hc'⟩` from `hrange _ (GlobalTheory.MinorFrame.rowSub_mem_inv (fun τ => (κ τ : Matrix (Fin (a + a')) (Fin (a + a')) ℂ).map (starRingEnd ℂ)) hP)`. Rewrite using `[← hc', hPlA, hPlA, ← sub_eq_zero]`. Apply `eq_zero_of_eval _ (bottomMinors (a := a)) exists_eval_bottomMinors_ne_zero` to reduce the goal to its premises. Introduce `y hy`.

Take `⟨N, hN, rfl⟩` from `exists_frame y hy`. Establish `hu : ∀ τ, (κ τ : Matrix (Fin (a + a')) (Fin (a + a')) ℂ)ᵀ * (κ τ : Matrix (Fin (a + a')) (Fin (a + a')) ℂ).map (starRingEnd ℂ) = 1`. Introduce `τ`. Establish `h0 : star (κ τ : Matrix (Fin (a + a')) (Fin (a + a')) ℂ) * (κ τ : Matrix (Fin (a + a')) (Fin (a + a')) ℂ) = 1` using `(κ τ).2.1`. Use extensionality with `i j`.

Use `congrArg (fun M : Matrix (Fin (a + a')) (Fin (a + a')) ℂ => M j i) h0` as an intermediate fact. Simplify `this` using `[Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply, eq_comm, mul_comm]`. Establish `hκ : ∀ τ, (κ τ : Matrix (Fin (a + a')) (Fin (a + a')) ℂ).det ≠ 0`. Introduce `τ hz`. Use `congrArg Matrix.det (hu τ)` as an intermediate fact.

Rewrite `this` using `[Matrix.det_mul, Matrix.det_transpose, hz, zero_mul, Matrix.det_one]`. Conclude with `zero_ne_one this`. Set `N' : ι → Matrix (Fin (a + a')) (Fin (a + a')) ℂ` to `fun τ => (κ τ : Matrix (Fin (a + a')) (Fin (a + a')) ℂ)ᵀ * N τ`. Establish `hN' : ∀ τ, (N' τ).det ≠ 0`. Introduce `τ`.

Simplify using `only [N', Matrix.det_mul, Matrix.det_transpose]`. Conclude with `mul_ne_zero (hκ τ) (hN τ)`. Establish `hX : xPt N' = fun y => ∑ i', (κ y.1 : Matrix (Fin (a + a')) (Fin (a + a')) ℂ).map (starRingEnd ℂ) i' y.2.1 * xPt N (y.1, i', y.2.2)`. Use function extensionality and compare the values at `⟨τ, k, i⟩`. Establish `hinv : (N' τ)⁻¹ = (N τ)⁻¹ * (κ τ : Matrix (Fin (a + a')) (Fin (a + a')) ℂ).map (starRingEnd ℂ)`.

Simplify using `only [N']`. Rewrite using `[Matrix.mul_inv_rev, Matrix.inv_eq_right_inv (hu τ)]`. Simplify using `only [xPt, hinv, Matrix.mul_apply]`. Use `Finset.sum_congr rfl fun _ _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Establish `hY : yPt N' = fun y => ∑ i', (κ y.1 : Matrix (Fin (a + a')) (Fin (a + a')) ℂ) i' y.2.1 * yPt N (y.1, i', y.2.2)`. Use function extensionality and compare the values at `⟨τ, k, j⟩`. Simplify using `[yPt, N', Matrix.mul_apply]`. Establish `hlam' : lam n N' = lam n N * (GlobalTheory.MinorFrame.detChar n (fun τ => (κ τ : Matrix (Fin (a + a')) (Fin (a + a')) ℂ)))⁻¹`. Simplify using `only [lam, N', GlobalTheory.MinorFrame.detChar, Matrix.det_mul, Matrix.det_transpose, mul_inv, mul_pow, Finset.prod_mul_distrib, inv_pow, Finset.prod_inv_distrib]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hX' : ∀ Q, eval (xPt N) (GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin (a + a')) (Fin (a + a')) ℂ).map (starRingEnd ℂ)) Q) = eval (xPt N') Q`. Introduce `Q`. Rewrite using `[eval_rowSub, hX]`. Establish `hY' : ∀ Q, eval (yPt N') Q = eval (yPt N) (GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin (a + a')) (Fin (a + a')) ℂ)) Q)`.

Introduce `Q`. Rewrite using `[eval_rowSub, hY]`. Establish `e1` using `key c' N hN`. Establish `e2` using `key c N' hN'`. Rewrite `e1` using `[hc', hX', e2, hY', hlam']`.

Rewrite using `[map_sub, smul_eq_C_mul, eval_mul, eval_C, sub_eq_zero]`. Apply `mul_left_cancel₀ (hlam N hN)` to reduce the goal to its premises. Rewrite using `[← e1]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_star (n : ι → ℕ) (h : a + a' = a + a') :
    ∃ Pl : GlobalTheory.MinorFrame.Pol ι (a + a') a →ₗ[ℂ] GlobalTheory.MinorFrame.Pol ι (a + a') a',
      (∀ T : GlobalTheory.MinorFrame.Tup ι a (a + a') n,
        Pl (GlobalTheory.MinorFrame.prodMinors T) = (((sgn h T : ℤˣ) : ℤ) : ℂ) • GlobalTheory.MinorFrame.prodMinors (cTup h T)) ∧
      ∀ (κ : ι → Matrix.unitaryGroup (Fin (a + a')) ℂ), ∀ P ∈ GlobalTheory.MinorFrame.inv (ι := ι) a (a + a') n,
        Pl (GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin (a + a')) (Fin (a + a')) ℂ).map (starRingEnd ℂ)) P) =
          (GlobalTheory.MinorFrame.detChar n (fun τ => (κ τ : Matrix (Fin (a + a')) (Fin (a + a')) ℂ)))⁻¹ •
            GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin (a + a')) (Fin (a + a')) ℂ)) (Pl P) := by
  classical
  let A : (GlobalTheory.MinorFrame.Tup ι a (a + a') n → ℂ) →ₗ[ℂ] GlobalTheory.MinorFrame.Pol ι (a + a') a :=
    Fintype.linearCombination ℂ (fun T => GlobalTheory.MinorFrame.prodMinors T)
  let B : (GlobalTheory.MinorFrame.Tup ι a (a + a') n → ℂ) →ₗ[ℂ] GlobalTheory.MinorFrame.Pol ι (a + a') a' :=
    Fintype.linearCombination ℂ (fun T => (((sgn h T : ℤˣ) : ℤ) : ℂ) • GlobalTheory.MinorFrame.prodMinors (cTup h T))
  have key : ∀ c N, (∀ τ, (N τ).det ≠ 0) → eval (xPt N) (A c) = lam n N * eval (yPt N) (B c) := by
    intro c N hN
    simp only [A, B, Fintype.linearCombination_apply, map_sum, smul_eq_C_mul, eval_mul, eval_C, Finset.mul_sum,
      eval_xPt_prodMinors h N hN]
    refine Finset.sum_congr rfl fun T _ => ?_
    ring
  have hlam : ∀ N : ι → Matrix (Fin (a + a')) (Fin (a + a')) ℂ, (∀ τ, (N τ).det ≠ 0) → lam n N ≠ 0 := by
    intro N hN
    exact Finset.prod_ne_zero_iff.mpr fun τ _ => pow_ne_zero _ (inv_ne_zero (hN τ))
  have hker : LinearMap.ker A ≤ LinearMap.ker B := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    apply eq_zero_of_eval _ (bottomMinors (a := a)) exists_eval_bottomMinors_ne_zero
    intro y hy
    obtain ⟨N, hN, rfl⟩ := exists_frame y hy
    have := key c N hN
    rw [hc, map_zero] at this
    exact (mul_eq_zero.mp this.symm).resolve_left (hlam N hN)
  let f : LinearMap.range A →ₗ[ℂ] GlobalTheory.MinorFrame.Pol ι (a + a') a' :=
    ((LinearMap.ker A).liftQ B hker).comp A.quotKerEquivRange.symm.toLinearMap
  obtain ⟨Pl, hPl⟩ := LinearMap.exists_extend f
  have hPlA : ∀ c, Pl (A c) = B c := by
    intro c
    have := LinearMap.congr_fun hPl ⟨A c, LinearMap.mem_range_self A c⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
    rw [this]
    simp only [f, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.quotKerEquivRange_symm_apply_image,
      Submodule.mkQ_apply, Submodule.liftQ_apply]
  have hsingle : ∀ T, A (Pi.single T 1) = GlobalTheory.MinorFrame.prodMinors T := by
    intro T
    simp [A, Fintype.linearCombination_apply_single]
  have hrange : ∀ Q ∈ GlobalTheory.MinorFrame.inv (ι := ι) a (a + a') n, ∃ c, A c = Q := by
    intro Q hQ
    have hle : Submodule.span ℂ (Set.range (GlobalTheory.MinorFrame.prodMinors (ι := ι) (a := a) (d := a + a') (n := n))) ≤
        LinearMap.range A := by
      rw [Submodule.span_le]
      rintro _ ⟨T, rfl⟩
      exact ⟨Pi.single T 1, hsingle T⟩
    exact hle (GlobalTheory.MinorFrame.inv_le_span_prodMinors a (a + a') n hQ)
  refine ⟨Pl, fun T => ?_, fun κ P hP => ?_⟩
  · rw [← hsingle T, hPlA]
    simp [B, Fintype.linearCombination_apply_single]
  · obtain ⟨c, rfl⟩ := hrange P hP
    obtain ⟨c', hc'⟩ := hrange _ (GlobalTheory.MinorFrame.rowSub_mem_inv
      (fun τ => (κ τ : Matrix (Fin (a + a')) (Fin (a + a')) ℂ).map (starRingEnd ℂ)) hP)
    rw [← hc', hPlA, hPlA, ← sub_eq_zero]
    apply eq_zero_of_eval _ (bottomMinors (a := a)) exists_eval_bottomMinors_ne_zero
    intro y hy
    obtain ⟨N, hN, rfl⟩ := exists_frame y hy
    have hu : ∀ τ, (κ τ : Matrix (Fin (a + a')) (Fin (a + a')) ℂ)ᵀ *
        (κ τ : Matrix (Fin (a + a')) (Fin (a + a')) ℂ).map (starRingEnd ℂ) = 1 := by
      intro τ
      have h0 : star (κ τ : Matrix (Fin (a + a')) (Fin (a + a')) ℂ) * (κ τ : Matrix (Fin (a + a')) (Fin (a + a')) ℂ) = 1 := (κ τ).2.1
      ext i j
      have := congrArg (fun M : Matrix (Fin (a + a')) (Fin (a + a')) ℂ => M j i) h0
      simpa [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply, eq_comm, mul_comm] using this
    have hκ : ∀ τ, (κ τ : Matrix (Fin (a + a')) (Fin (a + a')) ℂ).det ≠ 0 := by
      intro τ hz
      have := congrArg Matrix.det (hu τ)
      rw [Matrix.det_mul, Matrix.det_transpose, hz, zero_mul, Matrix.det_one] at this
      exact zero_ne_one this
    let N' : ι → Matrix (Fin (a + a')) (Fin (a + a')) ℂ :=
      fun τ => (κ τ : Matrix (Fin (a + a')) (Fin (a + a')) ℂ)ᵀ * N τ
    have hN' : ∀ τ, (N' τ).det ≠ 0 := by
      intro τ
      simp only [N', Matrix.det_mul, Matrix.det_transpose]
      exact mul_ne_zero (hκ τ) (hN τ)
    have hX : xPt N' = fun y => ∑ i', (κ y.1 : Matrix (Fin (a + a')) (Fin (a + a')) ℂ).map (starRingEnd ℂ) i' y.2.1 *
        xPt N (y.1, i', y.2.2) := by
      funext ⟨τ, k, i⟩
      have hinv : (N' τ)⁻¹ = (N τ)⁻¹ * (κ τ : Matrix (Fin (a + a')) (Fin (a + a')) ℂ).map (starRingEnd ℂ) := by
        simp only [N']
        rw [Matrix.mul_inv_rev, Matrix.inv_eq_right_inv (hu τ)]
      simp only [xPt, hinv, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun _ _ => ?_
      ring
    have hY : yPt N' = fun y => ∑ i', (κ y.1 : Matrix (Fin (a + a')) (Fin (a + a')) ℂ) i' y.2.1 * yPt N (y.1, i', y.2.2) := by
      funext ⟨τ, k, j⟩
      simp [yPt, N', Matrix.mul_apply]
    have hlam' : lam n N' = lam n N * (GlobalTheory.MinorFrame.detChar n (fun τ => (κ τ : Matrix (Fin (a + a')) (Fin (a + a')) ℂ)))⁻¹ := by
      simp only [lam, N', GlobalTheory.MinorFrame.detChar, Matrix.det_mul, Matrix.det_transpose, mul_inv, mul_pow,
        Finset.prod_mul_distrib, inv_pow, Finset.prod_inv_distrib]
      ring
    have hX' : ∀ Q, eval (xPt N) (GlobalTheory.MinorFrame.rowSub
        (fun τ => (κ τ : Matrix (Fin (a + a')) (Fin (a + a')) ℂ).map (starRingEnd ℂ)) Q) = eval (xPt N') Q := by
      intro Q
      rw [eval_rowSub, hX]
    have hY' : ∀ Q, eval (yPt N') Q =
        eval (yPt N) (GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin (a + a')) (Fin (a + a')) ℂ)) Q) := by
      intro Q
      rw [eval_rowSub, hY]
    have e1 := key c' N hN
    have e2 := key c N' hN'
    rw [hc', hX', e2, hY', hlam'] at e1
    rw [map_sub, smul_eq_C_mul, eval_mul, eval_C, sub_eq_zero]
    apply mul_left_cancel₀ (hlam N hN)
    rw [← e1]
    ring

end GlobalTheory.PluckerStar

namespace GlobalTheory.BotMatch

/- English proof (translation)
Unfold `GlobalTheory.BotFormula.minorF`. Establish `: (fun k : D.what₂.Tau × Fin d × Fin a => (k.1, Fin.cast (rfl : d = d) k.2.1, Fin.cast (rfl : a = a) k.2.2)) = id`. Use function extensionality and compare the values at `k`. Simplify using the standard rewrite rules. Rewrite using `[this, MvPolynomial.rename_id]`.

Both sides reduce to the same expression.
-/
theorem minorF_rfl_eq_prodMinors {D : D7} {a d : ℕ} {n : D.what₂.Tau → ℕ} (T : GlobalTheory.NormSum.Tup D a d n) :
    GlobalTheory.BotFormula.minorF rfl rfl T = GlobalTheory.MinorFrame.prodMinors (ι := D.what₂.Tau) T := by
  unfold GlobalTheory.BotFormula.minorF
  have : (fun k : D.what₂.Tau × Fin d × Fin a => (k.1, Fin.cast (rfl : d = d) k.2.1, Fin.cast (rfl : a = a) k.2.2)) = id := by
    funext k
    simp
  rw [this, MvPolynomial.rename_id]
  rfl

/- English proof (translation)
Introduce `D a a' d had n`. Substitute `had` using the available equality. Take `⟨Pl, h1, h2⟩` from `GlobalTheory.PluckerStar.exists_star (ι := D.what₂.Tau) n (rfl : a + a' = a + a')`. Use `⟨Pl, fun T => GlobalTheory.PluckerStar.sgn rfl T, fun T => ?_, h2⟩` and prove the remaining obligations. Rewrite using `[minorF_rfl_eq_prodMinors, minorF_rfl_eq_prodMinors]`.

Conclude with `h1 T`.
-/
theorem complementary_minor_map : ∀ (D : D7) {a a' d : ℕ} (had : a + a' = d) (n : D.what₂.Tau → ℕ),
    ∃ (Pl : PolF D d a →ₗ[ℂ] PolF D d a') (ε : Tup D a d n → ℤˣ),
      (∀ T : Tup D a d n, Pl (GlobalTheory.BotFormula.minorF rfl rfl T) =
        ((ε T : ℤ) : ℂ) • GlobalTheory.BotFormula.minorF rfl rfl (GlobalTheory.BotMatch.complTup D had T)) ∧
      ∀ (κ : D.what₂.Tau → Matrix.unitaryGroup (Fin d) ℂ), ∀ P ∈ GlobalTheory.MinorFrame.inv (ι := D.what₂.Tau) a d n,
        Pl (GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ).map (starRingEnd ℂ)) P) =
          (GlobalTheory.MinorFrame.detChar n (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)))⁻¹ • GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) (Pl P) := by
  intro D a a' d had n
  subst had
  obtain ⟨Pl, h1, h2⟩ := GlobalTheory.PluckerStar.exists_star (ι := D.what₂.Tau) n (rfl : a + a' = a + a')
  refine ⟨Pl, fun T => GlobalTheory.PluckerStar.sgn rfl T, fun T => ?_, h2⟩
  rw [minorF_rfl_eq_prodMinors, minorF_rfl_eq_prodMinors]
  exact h1 T

end GlobalTheory.BotMatch
