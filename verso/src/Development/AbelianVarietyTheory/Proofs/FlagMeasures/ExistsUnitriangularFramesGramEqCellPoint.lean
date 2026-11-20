import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsTrm
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.DetMulEqSumProdMulDetSubmatrix
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitriangularChangeRationalFlagIffRationalUnipotStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LocOver

section MatrixFacts

variable {K : Type*} [Field K] {N : ℕ}

/- English proof (translation)
Establish `hbt : U.BlockTriangular id` using `fun i j hij => (hU i j).1 hij`. Establish `hdet : U.det = 1`. Rewrite using `[Matrix.det_of_upperTriangular hbt]`. Conclude with `Finset.prod_eq_one fun i _ => (hU i i).2 rfl`. Establish `hu : IsUnit U.det` using `by rw [hdet]; exact isUnit_one`.

Establish `h1 : U * U⁻¹ = 1` using `Matrix.mul_nonsing_inv U hu`. Establish `h2 : U⁻¹ * U = 1` using `Matrix.nonsing_inv_mul U hu`. Use `letI := Matrix.invertibleOfIsUnitDet U hu`. Establish `hbt' : U⁻¹.BlockTriangular id` using `Matrix.blockTriangular_inv_of_blockTriangular hbt`. Use `⟨fun i j => ⟨fun hij => hbt' hij, fun hij => ?_⟩, h1, h2⟩` and prove the remaining obligations.

Substitute `hij` using the available equality. Establish `e` using `congrFun (congrFun h2 i) i`. Rewrite `e` using `[Matrix.mul_apply, Finset.sum_eq_single i]`. Rewrite `e` using `[(hU i i).2 rfl, mul_one]`. Simplify using `using e`.

Introduce `k _ hk`. Break down `lt_or_gt_of_ne hk with h | h` into its components or cases. Rewrite using `[hbt' h, zero_mul]`. Rewrite using `[(hU k i).1 h, mul_zero]`. Simplify using the standard rewrite rules.
-/
theorem upUni_inv_facts {U : Matrix (Fin N) (Fin N) K} (hU : IsUpUni U) :
    IsUpUni U⁻¹ ∧ U * U⁻¹ = 1 ∧ U⁻¹ * U = 1 := by
  have hbt : U.BlockTriangular id := fun i j hij => (hU i j).1 hij
  have hdet : U.det = 1 := by
    rw [Matrix.det_of_upperTriangular hbt]
    exact Finset.prod_eq_one fun i _ => (hU i i).2 rfl
  have hu : IsUnit U.det := by rw [hdet]; exact isUnit_one
  have h1 : U * U⁻¹ = 1 := Matrix.mul_nonsing_inv U hu
  have h2 : U⁻¹ * U = 1 := Matrix.nonsing_inv_mul U hu
  letI := Matrix.invertibleOfIsUnitDet U hu
  have hbt' : U⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hbt
  refine ⟨fun i j => ⟨fun hij => hbt' hij, fun hij => ?_⟩, h1, h2⟩
  subst hij
  have e := congrFun (congrFun h2 i) i
  rw [Matrix.mul_apply, Finset.sum_eq_single i] at e
  · rw [(hU i i).2 rfl, mul_one] at e; simpa using e
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [hbt' h, zero_mul]
    · rw [(hU k i).1 h, mul_zero]
  · simp

/- English proof (translation)
Establish `hT : IsUpUni L.transpose` using `fun i j => ⟨fun hij => (hL j i).1 hij, fun hij => by subst hij; simpa using (hL i i).2 rfl⟩`. Take `⟨h0, -, -⟩` from `upUni_inv_facts hT`. Establish `hbt : L.transpose.BlockTriangular id` using `fun i j hij => (hT i j).1 hij`. Establish `hdet : L.det = 1`. Rewrite using `[← Matrix.det_transpose, Matrix.det_of_upperTriangular hbt]`.

Conclude with `Finset.prod_eq_one fun i _ => (hT i i).2 rfl`. Establish `hu : IsUnit L.det` using `by rw [hdet]; exact isUnit_one`. Use `⟨fun i j => ?_, Matrix.mul_nonsing_inv L hu, Matrix.nonsing_inv_mul L hu⟩` and prove the remaining obligations. Establish `e : L⁻¹ i j = (L.transpose)⁻¹ j i` using `by rw [← Matrix.transpose_nonsing_inv]; rfl`. Rewrite using `[e]`.

Conclude with `⟨fun hij => (h0 j i).1 hij, fun hij => (h0 j i).2 hij.symm⟩`.
-/
theorem loUni_inv_facts {L : Matrix (Fin N) (Fin N) K} (hL : IsLoUni L) :
    IsLoUni L⁻¹ ∧ L * L⁻¹ = 1 ∧ L⁻¹ * L = 1 := by
  have hT : IsUpUni L.transpose := fun i j => ⟨fun hij => (hL j i).1 hij, fun hij => by subst hij; simpa using (hL i i).2 rfl⟩
  obtain ⟨h0, -, -⟩ := upUni_inv_facts hT
  have hbt : L.transpose.BlockTriangular id := fun i j hij => (hT i j).1 hij
  have hdet : L.det = 1 := by
    rw [← Matrix.det_transpose, Matrix.det_of_upperTriangular hbt]
    exact Finset.prod_eq_one fun i _ => (hT i i).2 rfl
  have hu : IsUnit L.det := by rw [hdet]; exact isUnit_one
  refine ⟨fun i j => ?_, Matrix.mul_nonsing_inv L hu, Matrix.nonsing_inv_mul L hu⟩
  have e : L⁻¹ i j = (L.transpose)⁻¹ j i := by rw [← Matrix.transpose_nonsing_inv]; rfl
  rw [e]
  exact ⟨fun hij => (h0 j i).1 hij, fun hij => (h0 j i).2 hij.symm⟩

end MatrixFacts

/- English proof (translation)
Establish `hs : ∀ n : ℕ, ((-1 : K) ^ n) * ((-1) ^ n) = 1`. Introduce `n`. Rewrite using `[← mul_pow]`. Simplify using the standard rewrite rules. Use extensionality with `i j`.

Simplify using `only [Formalism.MainNotions.BridgeLemma₂.rows_tw, Matrix.of_apply]`. Take the linear combination `(B i j * (-1) ^ (r - j.val) * (-1) ^ (r - j.val)) * hs (r - i.val) + B i j * hs (r - j.val)`.
-/
theorem tw_tw {K : Type*} [CommRing K] {r : ℕ} (B : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    Formalism.MainNotions.BridgeLemma₂.rows_tw (Formalism.MainNotions.BridgeLemma₂.rows_tw B) = B := by
  have hs : ∀ n : ℕ, ((-1 : K) ^ n) * ((-1) ^ n) = 1 := by
    intro n; rw [← mul_pow]; simp
  ext i j
  simp only [Formalism.MainNotions.BridgeLemma₂.rows_tw, Matrix.of_apply]
  linear_combination (B i j * (-1) ^ (r - j.val) * (-1) ^ (r - j.val)) * hs (r - i.val) + B i j * hs (r - j.val)

/- English proof (translation)
Introduce `i j`. Use `⟨fun hij => by simp [Formalism.MainNotions.BridgeLemma₂.rows_tw, (hB i j).1 hij], fun hij => ?_⟩` and prove the remaining obligations. Substitute `hij` using the available equality. Simplify using `only [Formalism.MainNotions.BridgeLemma₂.rows_tw, Matrix.of_apply, (hB i i).2 rfl, mul_one]`. Rewrite using `[← mul_pow]`.

Simplify using the standard rewrite rules.
-/
theorem tw_upUni {K : Type*} [CommRing K] {r : ℕ} {B : Matrix (Fin (r + 1)) (Fin (r + 1)) K}
    (hB : IsUpUni B) : IsUpUni (Formalism.MainNotions.BridgeLemma₂.rows_tw B) := by
  intro i j
  refine ⟨fun hij => by simp [Formalism.MainNotions.BridgeLemma₂.rows_tw, (hB i j).1 hij], fun hij => ?_⟩
  subst hij
  simp only [Formalism.MainNotions.BridgeLemma₂.rows_tw, Matrix.of_apply, (hB i i).2 rfl, mul_one]
  rw [← mul_pow]; simp

variable {D : D7}

/- English proof (translation)
Use extensionality with `a b`. Establish `e2 : F₂.fl.fvec a = ∑ c, A c a • F.fl.fvec c` using `h₂ a`. Establish `e3 : F₃.fl.fvec b = ∑ d, A' d b • F₁.fl.fvec d` using `h₃ b`. Simplify using `only [ZhatL, Zhat, brS, Matrix.mul_apply, Matrix.conjTranspose_apply]`. Rewrite using `[e2, e3]`.

Simplify using `only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Simplify using `only [RingHom.id_apply, starRingEnd_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem zhatL_chg {T T' : D.host.E} {F F₂ : LFlag (VS D) D.R.rS T} {F₁ F₃ : LFlag (VS D) D.R.rS T'}
    {A A' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E}
    (h₂ : Chg (frame F) A (frame F₂)) (h₃ : Chg (frame F₁) A' (frame F₃)) :
    ZhatL F₂ F₃ = A.conjTranspose * ZhatL F F₁ * A' := by
  ext a b
  have e2 : F₂.fl.fvec a = ∑ c, A c a • F.fl.fvec c := h₂ a
  have e3 : F₃.fl.fvec b = ∑ d, A' d b • F₁.fl.fvec d := h₃ b
  simp only [ZhatL, Zhat, brS, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [e2, e3]
  simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => ?_
  simp only [RingHom.id_apply, starRingEnd_apply]
  ring

/- English proof (translation)
Unfold `leadMinorE`. Use `split_ifs with hl`. Conclude with `Formalism.HermitianLatticeCounting.P.leadingMinorTriangularInvariant D.host.E _ l hl _ _ _ (fun i => by simp [Matrix.conjTranspose_apply, hA.2 i]) (fun i j hij => by simp [Matrix.conjTranspose_apply, hA.1 j i hij]) (fun i => hA'.2 i) (fun i j hij => hA'.1 i j hij)`. Both sides reduce to the same expression.
-/
theorem zhatL_leadMinor {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T) (F₁ : LFlag (VS D) D.R.rS T')
    {A A' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E} (hA : Uni A) (hA' : Uni A') (l : ℕ) :
    leadMinorE (A.conjTranspose * ZhatL F F₁ * A') l = leadMinorE (ZhatL F F₁) l := by
  unfold leadMinorE
  split_ifs with hl
  · exact Formalism.HermitianLatticeCounting.P.leadingMinorTriangularInvariant D.host.E _ l hl _ _ _
      (fun i => by simp [Matrix.conjTranspose_apply, hA.2 i])
      (fun i j hij => by simp [Matrix.conjTranspose_apply, hA.1 j i hij])
      (fun i => hA'.2 i) (fun i j hij => hA'.1 i j hij)
  · rfl

/- English proof (translation)
Introduce `D T T' F F₁ w hT hT' hcell`. Take `⟨L, U, hL, hU, hZ⟩` from `hcell`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Take `⟨hLi, -, hLL⟩` from `loUni_inv_facts hL`. Take `⟨hUi, hUU, -⟩` from `upUni_inv_facts hU`.

Establish `hA : Uni (L⁻¹).conjTranspose` using `⟨fun a b hba => by simp [Matrix.conjTranspose_apply, (hLi b a).1 hba], fun a => by simp [Matrix.conjTranspose_apply, (hLi a a).2 rfl]⟩`. Establish `hA'u` using `tw_upUni hUi`. Establish `hA' : Uni (Formalism.MainNotions.BridgeLemma₂.rows_tw U⁻¹)` using `⟨fun a b hba => (hA'u a b).1 hba, fun a => (hA'u a a).2 rfl⟩`. Take `⟨F00, h00⟩` from `(GlobalTheory.T.unitriangularChange_rationalFlag_iff_rationalUnipotent D F hT).1 _ hA`. Take `⟨F'0, h'0⟩` from `(GlobalTheory.T.unitriangularChange_rationalFlag_iff_rationalUnipotent D F₁ hT').1 _ hA'`.

Use `⟨F00, F'0, ⟨_, hA, h00⟩, ⟨_, hA', h'0⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[zhatL_chg h00 h'0, Formalism.MainNotions.BridgeLemma₂.rows_ZhatOM_mul, hZ, tw_tw, Matrix.conjTranspose_conjTranspose]`. Combine the equalities or inequalities in the displayed calculation. Introduce and unpack `F₂ F₃ ⟨A, hA, h2⟩ ⟨A', hA', h3⟩`. Establish `hZ2` using `zhatL_chg h2 h3`.

Prove the components needed by the constructor for the conclusion. Establish `hAl : IsLoUni A.conjTranspose` using `fun i j => ⟨fun hij => by simp [Matrix.conjTranspose_apply, hA.1 j i hij], fun hij => by subst hij; simp [Matrix.conjTranspose_apply, hA.2 i]⟩`. Establish `hAu : IsUpUni A'` using `fun i j => ⟨fun hij => hA'.1 i j hij, fun hij => by subst hij; exact hA'.2 i⟩`. Use `⟨A.conjTranspose * L, U * Formalism.MainNotions.BridgeLemma₂.rows_tw A', Formalism.MainNotions.BridgeLemma₂.rows_loUni_mul hAl hL, Formalism.MainNotions.BridgeLemma₂.rows_upUni_mul hU (tw_upUni hAu), ?_⟩` and prove the remaining obligations. Rewrite using `[hZ2, Formalism.MainNotions.BridgeLemma₂.rows_ZhatOM_mul, hZ]`.

Simplify using `only [Matrix.mul_assoc]`. Use `show Gflag F₂.fl F₃.fl = Gflag F.fl F₁.fl`. Establish `hD : ∀ l, Dl F₂.fl F₃.fl l = Dl F.fl F₁.fl l` using `fun l => by show leadMinorE (ZhatL F₂ F₃) l = leadMinorE (ZhatL F F₁) l`. Rewrite using `[hZ2]`. Conclude with `zhatL_leadMinor F F₁ hA hA' l`.

Unfold `Gflag`. Rewrite using `[hD, hD]`.
-/
theorem base_frames_at_point : ∀ (D : D7) {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T) (F₁ : LFlag (VS D) D.R.rS T') (w : Point D.host.E (D.R.rS + 1)), T ≠ 0 → T' ≠ 0 → IsInCell (ZhatOM (ZhatL F F₁)) w → (∃ (F00 : LFlag (VS D) D.R.rS T) (F'0 : LFlag (VS D) D.R.rS T'), Tri D.host.E (frame F) (frame F00) ∧ Tri D.host.E (frame F₁) (frame F'0) ∧ ZhatOM (ZhatL F00 F'0) = ptMat w) ∧ ∀ (F₂ : LFlag (VS D) D.R.rS T) (F₃ : LFlag (VS D) D.R.rS T'), Tri D.host.E (frame F) (frame F₂) → Tri D.host.E (frame F₁) (frame F₃) → IsInCell (ZhatOM (ZhatL F₂ F₃)) w ∧ Gval F₂ F₃ = Gval F F₁ := by
  intro D T T' F F₁ w hT hT' hcell
  obtain ⟨L, U, hL, hU, hZ⟩ := hcell
  refine ⟨?_, ?_⟩
  · obtain ⟨hLi, -, hLL⟩ := loUni_inv_facts hL
    obtain ⟨hUi, hUU, -⟩ := upUni_inv_facts hU
    have hA : Uni (L⁻¹).conjTranspose :=
      ⟨fun a b hba => by simp [Matrix.conjTranspose_apply, (hLi b a).1 hba],
        fun a => by simp [Matrix.conjTranspose_apply, (hLi a a).2 rfl]⟩
    have hA'u := tw_upUni hUi
    have hA' : Uni (Formalism.MainNotions.BridgeLemma₂.rows_tw U⁻¹) := ⟨fun a b hba => (hA'u a b).1 hba, fun a => (hA'u a a).2 rfl⟩
    obtain ⟨F00, h00⟩ := (GlobalTheory.T.unitriangularChange_rationalFlag_iff_rationalUnipotent D F hT).1 _ hA
    obtain ⟨F'0, h'0⟩ := (GlobalTheory.T.unitriangularChange_rationalFlag_iff_rationalUnipotent D F₁ hT').1 _ hA'
    refine ⟨F00, F'0, ⟨_, hA, h00⟩, ⟨_, hA', h'0⟩, ?_⟩
    rw [zhatL_chg h00 h'0, Formalism.MainNotions.BridgeLemma₂.rows_ZhatOM_mul, hZ, tw_tw, Matrix.conjTranspose_conjTranspose]
    calc L⁻¹ * (L * ptMat w * U) * U⁻¹ = (L⁻¹ * L) * ptMat w * (U * U⁻¹) := by simp only [Matrix.mul_assoc]
      _ = ptMat w := by rw [hLL, hUU, Matrix.one_mul, Matrix.mul_one]
  · rintro F₂ F₃ ⟨A, hA, h2⟩ ⟨A', hA', h3⟩
    have hZ2 := zhatL_chg h2 h3
    constructor
    · have hAl : IsLoUni A.conjTranspose := fun i j =>
        ⟨fun hij => by simp [Matrix.conjTranspose_apply, hA.1 j i hij],
          fun hij => by subst hij; simp [Matrix.conjTranspose_apply, hA.2 i]⟩
      have hAu : IsUpUni A' := fun i j => ⟨fun hij => hA'.1 i j hij, fun hij => by subst hij; exact hA'.2 i⟩
      refine ⟨A.conjTranspose * L, U * Formalism.MainNotions.BridgeLemma₂.rows_tw A', Formalism.MainNotions.BridgeLemma₂.rows_loUni_mul hAl hL,
        Formalism.MainNotions.BridgeLemma₂.rows_upUni_mul hU (tw_upUni hAu), ?_⟩
      rw [hZ2, Formalism.MainNotions.BridgeLemma₂.rows_ZhatOM_mul, hZ]
      simp only [Matrix.mul_assoc]
    · show Gflag F₂.fl F₃.fl = Gflag F.fl F₁.fl
      have hD : ∀ l, Dl F₂.fl F₃.fl l = Dl F.fl F₁.fl l := fun l => by
        show leadMinorE (ZhatL F₂ F₃) l = leadMinorE (ZhatL F F₁) l
        rw [hZ2]; exact zhatL_leadMinor F F₁ hA hA' l
      unfold Gflag
      rw [hD, hD]

end GlobalTheory.LocOver
