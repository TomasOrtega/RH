import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadNatZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsTermZero
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ZintZero
import Development.AbelianVarietyTheory.Definitions.Divisors.MemMspan
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurDir
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldMirabolic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralThetaSeriesUnfoldMirabolic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPsiLocNeOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalWhittakerCoeffEqIteratedColumnTransform
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGenericOfIsLocComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsIntegralEntireTheta
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open GlobalTheory.MirTower GlobalTheory.CuspGeneric
open GroundTheory.Automorphic.FourierWhittaker (partialCoeff blockGL uGL)

noncomputable section

namespace GlobalTheory.PartialBlock

open GroundTheory.Automorphic.FourierWhittaker (partialCoeff_self coe_blockGL blockMat_apply diagonal_blockGL)

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Use `⟨hφ, fun γ _ g => hl γ g, ?_, hv⟩` and prove the remaining obligations. Introduce `j hj y g`. Establish `he : IsEmpty (UnipotentBlockColumnIndex (k + 1) j j)` using `⟨fun t => by have := t.1.2.isLt; have := t.2; omega⟩`. Establish `hy : y = 0` using `Subsingleton.elim _ _`. Substitute `hy` using the available equality.

Establish `hd : dot (eLast (k + 1) j) (0 : UnipotentBlockColumnIndex (k + 1) j j → Ad E) = 0` using `by simp [dot]`. Rewrite using `[hd, AddChar.map_zero_eq_one, one_mul]`. Unfold `blkU`. Rewrite using `[posU_zero, one_mul]`.
-/
theorem good_top {ψ : AddChar (Ad E) ℂ} {k : ℕ} {φ : GA E (k + 1) → ℂ} (hφ : Continuous φ)
    (hl : ∀ γ g, φ (ratGL E (k + 1) γ * g) = φ g)
    (hv : ∀ r, 0 < r → r ≤ k → ∀ g, avg (ratV E (UnipotentBlockColumnIndex (k + 1) r k)) (fun x => φ (blkU x * g)) = 0) :
    Good ψ k φ := by
  refine ⟨hφ, fun γ _ g => hl γ g, ?_, hv⟩
  intro j hj y g
  have he : IsEmpty (UnipotentBlockColumnIndex (k + 1) j j) := ⟨fun t => by have := t.1.2.isLt; have := t.2; omega⟩
  have hy : y = 0 := Subsingleton.elim _ _
  subst hy
  have hd : dot (eLast (k + 1) j) (0 : UnipotentBlockColumnIndex (k + 1) j j → Ad E) = 0 := by simp [dot]
  rw [hd, AddChar.map_zero_eq_one, one_mul]
  unfold blkU
  rw [posU_zero, one_mul]

/- English proof (translation)
Proceed by induction on `hm using Nat.decreasingInduction with`. Consider the case `self => rw [partialCoeff_self]`. Conclude with `good_top hφ hl hv`. Consider the case `of_succ m hm ih`. Rewrite using `[← GlobalTheory.WhitCols.colT_partialCoeff hφ (fun γ _ g => hl γ g) (by omega : m + 1 < k + 1)]`.

Conclude with `GlobalTheory.CuspRep.Generic.good_colT (GlobalTheory.StdCharConductor.stdPsi_psi E) (by omega) ih`.
-/
theorem good_partialCoeff {k : ℕ} {φ : GA E (k + 1) → ℂ} (hφ : Continuous φ)
    (hl : ∀ γ g, φ (ratGL E (k + 1) γ * g) = φ g)
    (hv : ∀ r, 0 < r → r ≤ k → ∀ g, avg (ratV E (UnipotentBlockColumnIndex (k + 1) r k)) (fun x => φ (blkU x * g)) = 0)
    {m : ℕ} (hm : m ≤ k) : Good (GlobalTheory.StdCharConductor.psi E) m (partialCoeff φ (m + 1)) := by
  induction hm using Nat.decreasingInduction with
  | self => rw [partialCoeff_self]; exact good_top hφ hl hv
  | of_succ m hm ih =>
    rw [← GlobalTheory.WhitCols.colT_partialCoeff hφ (fun γ _ g => hl γ g) (by omega : m + 1 < k + 1)]
    exact GlobalTheory.CuspRep.Generic.good_colT (GlobalTheory.StdCharConductor.stdPsi_psi E) (by omega) ih

/- English proof (translation)
Rewrite using `[← posM_block_entry]`. Both sides reduce to the same expression.
-/
theorem blkU_entry {R : Type} [CommRing R] {a r m : ℕ} (y : UnipotentBlockColumnIndex a r m → R) (i k : Fin a) :
    (blkU y : GL (Fin a) R).val i k = (1 : Matrix (Fin a) (Fin a) R) i k +
      if h : (i : ℕ) < r ∧ r ≤ (k : ℕ) ∧ (k : ℕ) ≤ m then y ⟨(i, k), h⟩ else 0 := by
  rw [← posM_block_entry]; rfl

def blkEquiv {n m : ℕ} (h : m + 1 ≤ n) (r : ℕ) : UnipotentBlockColumnIndex n r m ≃ UnipotentBlockColumnIndex (m + 1) r m where
  toFun t := ⟨(⟨t.1.1.1, by have := t.2; omega⟩, ⟨t.1.2.1, by have := t.2; omega⟩), t.2⟩
  invFun t := ⟨(⟨t.1.1.1, by have := t.2; omega⟩, ⟨t.1.2.1, by have := t.2; omega⟩), t.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def blkHom {n m : ℕ} (h : m + 1 ≤ n) (r : ℕ) : (UnipotentBlockColumnIndex (m + 1) r m → Ad E) ≃ₜ+ (UnipotentBlockColumnIndex n r m → Ad E) where
  toFun x := fun t => x (blkEquiv h r t)
  invFun y := fun i => y ((blkEquiv h r).symm i)
  left_inv x := by funext i; simp
  right_inv y := by funext t; simp
  map_add' x y := rfl
  continuous_toFun := continuous_pi fun t => continuous_apply _
  continuous_invFun := continuous_pi fun i => continuous_apply _

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, hc⟩`. Conclude with `⟨fun i => c ((blkEquiv h r).symm i), funext fun i => congrFun hc ((blkEquiv h r).symm i)⟩`. Introduce and unpack `⟨c, rfl⟩`. Conclude with `⟨fun t => c (blkEquiv h r t), rfl⟩`.
-/
theorem blkHom_mem_iff {n m : ℕ} (h : m + 1 ≤ n) (r : ℕ) (x : UnipotentBlockColumnIndex (m + 1) r m → Ad E) :
    blkHom h r x ∈ ratV E (UnipotentBlockColumnIndex n r m) ↔ x ∈ ratV E (UnipotentBlockColumnIndex (m + 1) r m) := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨fun i => c ((blkEquiv h r).symm i), funext fun i => congrFun hc ((blkEquiv h r).symm i)⟩
  · rintro ⟨c, rfl⟩
    exact ⟨fun t => c (blkEquiv h r t), rfl⟩

/- English proof (translation)
Use `Units.ext ?_` and prove the remaining obligations. Use extensionality with `i j`. Rewrite using `[coe_blockGL, blockMat_apply, blkU_entry]`. Distinguish the cases in `hi : (i : ℕ) < m + 1`. Distinguish the cases in `hj : (j : ℕ) < m + 1`.

Rewrite using `[dif_pos hi, dif_pos hj, blkU_entry]`. Use `congr 1`. Simplify using `only [Matrix.one_apply, Fin.ext_iff]`. Establish `hne : i ≠ j` using `fun e => hj (e ▸ hi)`. Rewrite using `[dif_pos hi, dif_neg hj, dif_neg (by omega), Matrix.one_apply_ne hne, add_zero]`.

Rewrite using `[dif_neg hi, dif_neg (by omega), add_zero, Matrix.one_apply]`.
-/
theorem blockGL_blkU {n m : ℕ} (h : m + 1 ≤ n) (r : ℕ) (x : UnipotentBlockColumnIndex (m + 1) r m → Ad E) :
    (blockGL h (blkU x) : GL (Fin n) (Ad E)) = blkU (blkHom h r x) := by
  refine Units.ext ?_
  ext i j
  rw [coe_blockGL, blockMat_apply, blkU_entry]
  by_cases hi : (i : ℕ) < m + 1
  · by_cases hj : (j : ℕ) < m + 1
    · rw [dif_pos hi, dif_pos hj, blkU_entry]
      congr 1
      simp only [Matrix.one_apply, Fin.ext_iff]
    · have hne : i ≠ j := fun e => hj (e ▸ hi)
      rw [dif_pos hi, dif_neg hj, dif_neg (by omega), Matrix.one_apply_ne hne, add_zero]
  · rw [dif_neg hi, dif_neg (by omega), add_zero, Matrix.one_apply]

omit [NumberField E] in
/- English proof (translation)
Introduce `i j hij`. Rewrite using `[coe_blockGL, blockMat_apply]`. Distinguish the cases in `hi : (i : ℕ) < m + 1`. Distinguish the cases in `hj : (j : ℕ) < m + 1`. Rewrite using `[dif_pos hi, dif_pos hj, hγ _ _ hij]`.

Simplify using `only [Matrix.one_apply, Fin.ext_iff]`. Establish `hne : i ≠ j` using `fun e => hj (e ▸ hi)`. Rewrite using `[dif_pos hi, dif_neg hj, Matrix.one_apply_ne hne]`. Rewrite using `[dif_neg hi, Matrix.one_apply]`.
-/
theorem isMir_blockGL {n m : ℕ} (h : m + 1 ≤ n) {γ : GL (Fin (m + 1)) E} (hγ : IsMir m γ) :
    IsMir m (blockGL h γ : GL (Fin n) E) := by
  intro i j hij
  rw [coe_blockGL, blockMat_apply]
  by_cases hi : (i : ℕ) < m + 1
  · by_cases hj : (j : ℕ) < m + 1
    · rw [dif_pos hi, dif_pos hj, hγ _ _ hij]
      simp only [Matrix.one_apply, Fin.ext_iff]
    · have hne : i ≠ j := fun e => hj (e ▸ hi)
      rw [dif_pos hi, dif_neg hj, Matrix.one_apply_ne hne]
  · rw [dif_neg hi, Matrix.one_apply]

/- English proof (translation)
Use `⟨hF.cont.comp (GlobalTheory.RSnm.continuous_blockGL h), ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `γ hγ g`. Establish `e : (blockGL h (ratGL E (m + 1) γ) : GA E n) = ratGL E n (blockGL h γ)` using `(diagonal_blockGL h γ).symm`. Simplify using `only [map_mul]`. Rewrite using `[e, hF.left _ (isMir_blockGL h hγ)]`.

Introduce `j hj y g`. Establish `he : IsEmpty (UnipotentBlockColumnIndex (m + 1) j j)` using `⟨fun t => by have := t.1.2.isLt; have := t.2; omega⟩`. Establish `hy : y = 0` using `Subsingleton.elim _ _`. Substitute `hy` using the available equality. Establish `hd : dot (eLast (m + 1) j) (0 : UnipotentBlockColumnIndex (m + 1) j j → Ad E) = 0` using `by simp [dot]`.

Rewrite using `[hd, AddChar.map_zero_eq_one, one_mul]`. Unfold `blkU`. Rewrite using `[posU_zero, one_mul]`. Introduce `r hr hrm g`. Establish `hP` using `per_blk (r := r) (m := m) hF.cont (fun c g => hF.left _ (isMir_blkU c) g) (blockGL h g)`.

Rewrite using `[← hF.van r hr hrm (blockGL h g), ← avg_equiv _ _ _ _ (isCoLat_ratV E _) (isCoLat_ratV E _) (blkHom h r) (blkHom_mem_iff h r) _ hP]`. Simplify using `only [map_mul, blockGL_blkU]`.
-/
theorem good_restrict {ψ : AddChar (Ad E) ℂ} {n m : ℕ} (h : m + 1 ≤ n) {F : GA E n → ℂ} (hF : Good ψ m F) :
    Good ψ m (fun g : GA E (m + 1) => F (blockGL h g)) := by
  refine ⟨hF.cont.comp (GlobalTheory.RSnm.continuous_blockGL h), ?_, ?_, ?_⟩
  · intro γ hγ g
    have e : (blockGL h (ratGL E (m + 1) γ) : GA E n) = ratGL E n (blockGL h γ) := (diagonal_blockGL h γ).symm
    simp only [map_mul]
    rw [e, hF.left _ (isMir_blockGL h hγ)]
  · intro j hj y g
    have he : IsEmpty (UnipotentBlockColumnIndex (m + 1) j j) := ⟨fun t => by have := t.1.2.isLt; have := t.2; omega⟩
    have hy : y = 0 := Subsingleton.elim _ _
    subst hy
    have hd : dot (eLast (m + 1) j) (0 : UnipotentBlockColumnIndex (m + 1) j j → Ad E) = 0 := by simp [dot]
    rw [hd, AddChar.map_zero_eq_one, one_mul]
    unfold blkU
    rw [posU_zero, one_mul]
  · intro r hr hrm g
    have hP := per_blk (r := r) (m := m) hF.cont (fun c g => hF.left _ (isMir_blkU c) g) (blockGL h g)
    rw [← hF.van r hr hrm (blockGL h g), ← avg_equiv _ _ _ _ (isCoLat_ratV E _) (isCoLat_ratV E _) (blkHom h r)
      (blkHom_mem_iff h r) _ hP]
    simp only [map_mul, blockGL_blkU]

/- English proof (translation)
Introduce `E _ _ k m hmk φ hφ hl hv`. Conclude with `good_restrict _ (good_partialCoeff hφ hl hv (by omega))`.
-/
theorem good_partialCoeff_blockGL : ∀ (E : Type) [Field E] [NumberField E] (k m : ℕ) (hmk : m + 1 ≤ k) (φ : GA E (k + 1) → ℂ),
    Continuous φ → (∀ γ g, φ (ratGL E (k + 1) γ * g) = φ g) →
    (∀ r, 0 < r → r ≤ k → ∀ g, avg (ratV E (UnipotentBlockColumnIndex (k + 1) r k)) (fun x => φ (blkU x * g)) = 0) →
    Good (GlobalTheory.StdCharConductor.psi E) m (fun h => partialCoeff φ (m + 1) (blockGL (by omega : m + 1 ≤ k + 1) h)) := by
  intro E _ _ k m hmk φ hφ hl hv
  exact good_restrict _ (good_partialCoeff hφ hl hv (by omega))

end GlobalTheory.PartialBlock

end
