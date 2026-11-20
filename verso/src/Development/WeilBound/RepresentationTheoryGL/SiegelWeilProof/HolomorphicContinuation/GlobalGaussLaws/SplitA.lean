import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FourierZeroN
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousLeviBlock
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GaussianTwistedRealReadingEntireAndInjective
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnipotentAtTauMemStabilizer
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtensionAdeleRealComponentsCmType
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsMaximalCompactUnnComponentStandardCartanIn
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StabiliserEqCentraliserCartan
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsArchEquivEq

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

variable {D : D7} {n : ℕ}

/- English proof (translation)
Use `show ((GlobalTheory.AdelicU.matHom _ D.sp.cm.sig (Jst D n)) (a * b)).1 = _`. Rewrite using `[map_mul, Units.val_mul]`. Both sides reduce to the same expression.
-/
theorem mat_mul' (a b : G D n) : mat (a * b) = mat a * mat b := by
  show ((GlobalTheory.AdelicU.matHom _ D.sp.cm.sig (Jst D n)) (a * b)).1 = _
  rw [map_mul, Units.val_mul]; rfl

/- English proof (translation)
Use `show ((GlobalTheory.AdelicU.matHom _ D.sp.cm.sig (Jst D n)) 1).1 = 1`. Rewrite using `[map_one]`. Both sides reduce to the same expression.
-/
theorem mat_one' : mat (1 : G D n) = 1 := by
  show ((GlobalTheory.AdelicU.matHom _ D.sp.cm.sig (Jst D n)) 1).1 = 1
  rw [map_one]; rfl

/- English proof (translation)
The claim follows from `Subtype.ext (Units.ext h)`.
-/
theorem G_ext' {a b : G D n} (h : mat a = mat b) : a = b := Subtype.ext (Units.ext h)

/- English proof (translation)
Simplify using `[reidx, Matrix.submatrix_mul_equiv]`.
-/
theorem reidx_mul (A B : M2 n) : reidx (A * B) = reidx A * reidx B := by
  simp [reidx, Matrix.submatrix_mul_equiv]

/- English proof (translation)
Simplify using `[reidx, Matrix.submatrix_one_equiv]`.
-/
theorem reidx_one : reidx (1 : M2 n) = 1 := by simp [reidx, Matrix.submatrix_one_equiv]

/- English proof (translation)
Simplify using `[reidx, Matrix.conjTranspose_submatrix]`.
-/
theorem reidx_ct (A : M2 n) : reidx Aᴴ = (reidx A)ᴴ := by simp [reidx, Matrix.conjTranspose_submatrix]

/- English proof (translation)
Use `congrArg (fun M => M.submatrix finSumFinEquiv finSumFinEquiv) h` as an intermediate fact. Simplify `this` using `[reidx, Matrix.submatrix_submatrix]`.
-/
theorem reidx_inj {A B : M2 n} (h : reidx A = reidx B) : A = B := by
  have := congrArg (fun M => M.submatrix finSumFinEquiv finSumFinEquiv) h
  simpa [reidx, Matrix.submatrix_submatrix] using this

/- English proof (translation)
Apply `G_ext'` to reduce the goal to its premises. Rewrite using `[mat_mul', mat_mul']`. Take `⟨h1, h2, h3⟩` from `hι.2 y`. Use `GlobalTheory.StabAtPlace.mx_ext hθ ?_ fun τ' => ?_` and prove the remaining obligations. Rewrite using `[Matrix.map_mul, Matrix.map_mul, h3, Matrix.mul_one, Matrix.one_mul]`.

Rewrite using `[GlobalTheory.StabAtPlace.comp_mul, GlobalTheory.StabAtPlace.comp_mul]`. Distinguish the cases in `hτ : τ' = τ`. Substitute `hτ` using the available equality. Rewrite using `[hk, Matrix.one_mul, Matrix.mul_one]`. Rewrite using `[h2 τ' hτ, Matrix.one_mul, Matrix.mul_one]`.
-/
theorem comm_of_trivial {θ : InfFam D} (hθ : IsInfFam θ) {τ : D.what₂.Tau} {ι : GR n →* G D n} (hι : IsPlaceEmb θ τ ι)
    {k : G D n} (hk : compAt θ τ (mat k) = 1) (y : GR n) : k * ι y = ι y * k := by
  apply G_ext'
  rw [mat_mul', mat_mul']
  obtain ⟨h1, h2, h3⟩ := hι.2 y
  refine GlobalTheory.StabAtPlace.mx_ext hθ ?_ fun τ' => ?_
  · rw [Matrix.map_mul, Matrix.map_mul, h3, Matrix.mul_one, Matrix.one_mul]
  · rw [GlobalTheory.StabAtPlace.comp_mul, GlobalTheory.StabAtPlace.comp_mul]
    by_cases hτ : τ' = τ
    · subst hτ; rw [hk, Matrix.one_mul, Matrix.mul_one]
    · rw [h2 τ' hτ, Matrix.one_mul, Matrix.mul_one]

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `hι.2 y`. Use `show ι y ∈ GlobalTheory.AdelicU.levelAll D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n)) 1`. Rewrite using `[GlobalTheory.AdelicU.mem_levelAll]`. Use `⟨fun v => ?_, fun w => ?_⟩` and prove the remaining obligations. Establish `hinf : ι y ∈ GlobalTheory.AdelicU.infPts D.sp.cm.sig (Jst D n)` using `Units.ext h3`.

Rewrite using `[GlobalTheory.AdelicU.mem_infPts_iff_forall.1 hinf v]`. Conclude with `one_mem _`. Take `⟨ρ, rfl⟩` from `(GlobalTheory.AdelicU.placeOf_bijective D).2 w`. Rewrite using `[GlobalTheory.Doubling.mem_stabArch_iff_unitary (GlobalTheory.AdelicU.isCMExt_host D) (GlobalTheory.AdelicU.embOverOf D ρ) (Jst D n) 1 (ι y)]`. Rewrite using `[inv_one, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _)]`.

Simplify using `only [Matrix.one_mul, Matrix.mul_one]`. Establish `e1 : Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig (Jst D n) (GlobalTheory.AdelicU.infProj (GlobalTheory.AdelicU.embOverOf D ρ)) (ι y) = compAt θ ρ (mat (ι y))`. Rewrite using `[← GlobalTheory.AdelicU.eq_infProj hθ (GlobalTheory.AdelicU.embOverOf D ρ) rfl]`. Both sides reduce to the same expression. Rewrite using `[e1]`.

Distinguish the cases in `hρ : ρ = τ`. Substitute `hρ` using the available equality. Rewrite using `[h1, ← reidx_ct, ← reidx_mul, hy.2, reidx_one]`. Rewrite using `[h2 ρ hρ]`. Simplify using the standard rewrite rules.
-/
theorem iota_mem_K {θ : InfFam D} (hθ : IsInfFam θ) {τ : D.what₂.Tau} {ι : GR n →* G D n} (hι : IsPlaceEmb θ τ ι)
    {y : GR n} (hy : InK (mR y)) : ι y ∈ K D n := by
  obtain ⟨h1, h2, h3⟩ := hι.2 y
  show ι y ∈ GlobalTheory.AdelicU.levelAll D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n)) 1
  rw [GlobalTheory.AdelicU.mem_levelAll]
  refine ⟨fun v => ?_, fun w => ?_⟩
  · have hinf : ι y ∈ GlobalTheory.AdelicU.infPts D.sp.cm.sig (Jst D n) := Units.ext h3
    rw [GlobalTheory.AdelicU.mem_infPts_iff_forall.1 hinf v]; exact one_mem _
  · obtain ⟨ρ, rfl⟩ := (GlobalTheory.AdelicU.placeOf_bijective D).2 w
    rw [GlobalTheory.Doubling.mem_stabArch_iff_unitary (GlobalTheory.AdelicU.isCMExt_host D) (GlobalTheory.AdelicU.embOverOf D ρ) (Jst D n) 1 (ι y)]
    rw [inv_one, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _)]
    simp only [Matrix.one_mul, Matrix.mul_one]
    have e1 : Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig (Jst D n) (GlobalTheory.AdelicU.infProj (GlobalTheory.AdelicU.embOverOf D ρ)) (ι y) =
        compAt θ ρ (mat (ι y)) := by
      rw [← GlobalTheory.AdelicU.eq_infProj hθ (GlobalTheory.AdelicU.embOverOf D ρ) rfl]; rfl
    rw [e1]
    by_cases hρ : ρ = τ
    · subst hρ; rw [h1, ← reidx_ct, ← reidx_mul, hy.2, reidx_one]
    · rw [h2 ρ hρ]; simp

/- English proof (translation)
Establish `e1 : compAt θ τ (mat k) = Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig (Jst D n) (θ τ) k` using `rfl`. Establish `e2 : θ τ = GlobalTheory.AdelicU.infProj (GlobalTheory.AdelicU.embOverOf D τ)` using `GlobalTheory.AdelicU.eq_infProj hθ (GlobalTheory.AdelicU.embOverOf D τ) rfl`. Establish `hk' : k ∈ GlobalTheory.AdelicU.levelAll D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n)) 1` using `hk`. Establish `hw` using `(GlobalTheory.AdelicU.mem_levelAll.1 hk').2 (GlobalTheory.AdelicU.placeOf D τ)`. Establish `hunit` using `(GlobalTheory.Doubling.mem_stabArch_iff_unitary (GlobalTheory.AdelicU.isCMExt_host D) (GlobalTheory.AdelicU.embOverOf D τ) (Jst D n) 1 k).1 hw`.

Rewrite `hunit` using `[inv_one, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _)]`. Simplify using `only [Matrix.one_mul, Matrix.mul_one] at hunit`. Rewrite `hunit` using `[← e2, ← e1]`. Establish `hiso` using `(GlobalTheory.AdelicU.archEquiv (Jst D n) (GlobalTheory.AdelicU.isCMExt_host D) (GlobalTheory.AdelicU.embOverOf D τ) (GlobalTheory.AdelicU.projArch D.sp.cm.sig (Jst D n) (GlobalTheory.AdelicU.placeOf D τ) k)).2`. Establish `hiso' : (compAt θ τ (mat k))ᴴ * (Jst D n).map (GlobalTheory.AdelicU.embOverOf D τ).1 * compAt θ τ (mat k) = (Jst D n).map (GlobalTheory.AdelicU.embOverOf D τ).1`.

Rewrite using `[e1, e2, GlobalTheory.AdelicU.infMat_infProj (Jst D n) (GlobalTheory.AdelicU.isCMExt_host D)]`. Conclude with `hiso`. Rewrite `hiso'` using `[Jst, GlobalTheory.CartanPt.blkJ_map]`. Use `set M := compAt θ τ (mat k) with hM`. Use `set Y : M2 n := M.submatrix finSumFinEquiv finSumFinEquiv with hY`.

Establish `hYM : reidx Y = M` using `by simp [hY, reidx, Matrix.submatrix_submatrix]`. Establish `hJ : reidx (JJ n) = blk4 (0 : Matrix (Fin n) (Fin n) ℂ) 1 (-1) 0` using `rfl`. Establish `hu : Yᴴ * Y = 1` using `reidx_inj (by rw [reidx_mul, reidx_ct, hYM, reidx_one]; exact hunit)`. Establish `hG : Yᴴ * JJ n * Y = JJ n` using `reidx_inj (by rw [reidx_mul, reidx_mul, reidx_ct, hYM, hJ]; exact hiso')`. Establish `hu' : Y * Yᴴ = 1` using `mul_eq_one_comm.1 hu`.

Set `u : GL (Fin n ⊕ Fin n) ℂ` to `⟨Y, Yᴴ, hu', hu⟩`. Set `y : GR n` to `⟨u, hG⟩`. Establish `hyK : InK (mR y)` using `⟨hG, hu⟩`. Use `⟨y, hyK, (K D n).mul_mem ((K D n).inv_mem (iota_mem_K hθ hι hyK)) hk, ?_⟩` and prove the remaining obligations. Rewrite using `[mat_mul', GlobalTheory.StabAtPlace.comp_mul, ← map_inv, (hι.2 y⁻¹).1]`.

Use `show reidx Yᴴ * M = 1`. Rewrite using `[← hYM, ← reidx_mul, hu, reidx_one]`.
-/
theorem K_split {θ : InfFam D} (hθ : IsInfFam θ) {τ : D.what₂.Tau} {ι : GR n →* G D n} (hι : IsPlaceEmb θ τ ι)
    {k : G D n} (hk : k ∈ K D n) : ∃ y : GR n, InK (mR y) ∧ (ι y)⁻¹ * k ∈ K D n ∧ compAt θ τ (mat ((ι y)⁻¹ * k)) = 1 := by
  have e1 : compAt θ τ (mat k) = Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig (Jst D n) (θ τ) k := rfl
  have e2 : θ τ = GlobalTheory.AdelicU.infProj (GlobalTheory.AdelicU.embOverOf D τ) := GlobalTheory.AdelicU.eq_infProj hθ (GlobalTheory.AdelicU.embOverOf D τ) rfl
  have hk' : k ∈ GlobalTheory.AdelicU.levelAll D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n)) 1 := hk
  have hw := (GlobalTheory.AdelicU.mem_levelAll.1 hk').2 (GlobalTheory.AdelicU.placeOf D τ)
  have hunit := (GlobalTheory.Doubling.mem_stabArch_iff_unitary (GlobalTheory.AdelicU.isCMExt_host D) (GlobalTheory.AdelicU.embOverOf D τ) (Jst D n) 1 k).1 hw
  rw [inv_one, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.map_one _ (map_zero _) (map_one _)] at hunit
  simp only [Matrix.one_mul, Matrix.mul_one] at hunit
  rw [← e2, ← e1] at hunit
  have hiso := (GlobalTheory.AdelicU.archEquiv (Jst D n) (GlobalTheory.AdelicU.isCMExt_host D) (GlobalTheory.AdelicU.embOverOf D τ)
    (GlobalTheory.AdelicU.projArch D.sp.cm.sig (Jst D n) (GlobalTheory.AdelicU.placeOf D τ) k)).2
  have hiso' : (compAt θ τ (mat k))ᴴ * (Jst D n).map (GlobalTheory.AdelicU.embOverOf D τ).1 * compAt θ τ (mat k) =
      (Jst D n).map (GlobalTheory.AdelicU.embOverOf D τ).1 := by
    rw [e1, e2, GlobalTheory.AdelicU.infMat_infProj (Jst D n) (GlobalTheory.AdelicU.isCMExt_host D)]
    exact hiso
  rw [Jst, GlobalTheory.CartanPt.blkJ_map] at hiso'
  set M := compAt θ τ (mat k) with hM
  set Y : M2 n := M.submatrix finSumFinEquiv finSumFinEquiv with hY
  have hYM : reidx Y = M := by simp [hY, reidx, Matrix.submatrix_submatrix]
  have hJ : reidx (JJ n) = blk4 (0 : Matrix (Fin n) (Fin n) ℂ) 1 (-1) 0 := rfl
  have hu : Yᴴ * Y = 1 := reidx_inj (by rw [reidx_mul, reidx_ct, hYM, reidx_one]; exact hunit)
  have hG : Yᴴ * JJ n * Y = JJ n := reidx_inj (by rw [reidx_mul, reidx_mul, reidx_ct, hYM, hJ]; exact hiso')
  have hu' : Y * Yᴴ = 1 := mul_eq_one_comm.1 hu
  let u : GL (Fin n ⊕ Fin n) ℂ := ⟨Y, Yᴴ, hu', hu⟩
  let y : GR n := ⟨u, hG⟩
  have hyK : InK (mR y) := ⟨hG, hu⟩
  refine ⟨y, hyK, (K D n).mul_mem ((K D n).inv_mem (iota_mem_K hθ hι hyK)) hk, ?_⟩
  rw [mat_mul', GlobalTheory.StabAtPlace.comp_mul, ← map_inv, (hι.2 y⁻¹).1]
  show reidx Yᴴ * M = 1
  rw [← hYM, ← reidx_mul, hu, reidx_one]

/- English proof (translation)
Use extensionality with `i j`. Both sides reduce to the same expression.
-/
theorem blkA_map' {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (M : Matrix (Fin (n + n)) (Fin (n + n)) R) :
    (blkA M).map f = blkA (M.map f) := by
  ext i j; rfl

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[blkA, Matrix.toBlocks₁₁, Matrix.one_apply]`.
-/
theorem blkA_one' {R : Type} [CommRing R] : blkA (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) = 1 := by
  ext i j
  simp [blkA, Matrix.toBlocks₁₁, Matrix.one_apply]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[blkA, reidx, Matrix.toBlocks₁₁]`.
-/
theorem blkA_reidx (Y : M2 n) : blkA (reidx Y) = Y.toBlocks₁₁ := by
  ext i j
  simp [blkA, reidx, Matrix.toBlocks₁₁]

/- English proof (translation)
Use `set Q := mR q with hQ`. Use `set N := mR q⁻¹ with hN`. Establish `hQN : Q * N = 1` using `by show (q : GL (Fin n ⊕ Fin n) ℂ).1 * ((q⁻¹ : GR n) : GL (Fin n ⊕ Fin n) ℂ).1 = 1`. Rewrite using `[Subgroup.coe_inv, Units.mul_inv]`. Establish `hG : Qᴴ * JJ n * Q = JJ n` using `q.2`.

Rewrite `hG` using `[← Matrix.fromBlocks_toBlocks Q, hq, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]`. Take `⟨-, h12, -, -⟩` from `Matrix.fromBlocks_inj.1 hG`. Simplify using `only [Matrix.mul_zero, Matrix.mul_one, Matrix.conjTranspose_zero, Matrix.zero_mul, Matrix.mul_neg, zero_add, add_zero, neg_zero] at h12`. Establish `hAD : Q.toBlocks₁₁ᴴ * Q.toBlocks₂₂ = 1` using `by simpa using h12`. Establish `hDA : Q.toBlocks₂₂ * Q.toBlocks₁₁ᴴ = 1` using `mul_eq_one_comm.1 hAD`.

Establish `h1b : Matrix.toBlocks₂₁ (1 : M2 n) = 0`. Use extensionality with `i j`. Simplify using `[Matrix.toBlocks₂₁]`. Establish `h21 : Q.toBlocks₂₂ * N.toBlocks₂₁ = 0`. Use `congrArg Matrix.toBlocks₂₁ hQN` as an intermediate fact.

Rewrite `this` using `[← Matrix.fromBlocks_toBlocks Q, ← Matrix.fromBlocks_toBlocks N, Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₂₁, h1b]`. Rewrite `this` using `[hq, Matrix.zero_mul, zero_add]`. Conclude with `this`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Matrix.mul_assoc, hAD, Matrix.one_mul]`.

Use `_ = 0 := by rw [h21, Matrix.mul_zero]`.
-/
theorem up_inv {q : GR n} (hq : (mR q).toBlocks₂₁ = 0) : (mR q⁻¹).toBlocks₂₁ = 0 := by
  set Q := mR q with hQ
  set N := mR q⁻¹ with hN
  have hQN : Q * N = 1 := by
    show (q : GL (Fin n ⊕ Fin n) ℂ).1 * ((q⁻¹ : GR n) : GL (Fin n ⊕ Fin n) ℂ).1 = 1
    rw [Subgroup.coe_inv, Units.mul_inv]
  have hG : Qᴴ * JJ n * Q = JJ n := q.2
  rw [← Matrix.fromBlocks_toBlocks Q, hq, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply] at hG
  obtain ⟨-, h12, -, -⟩ := Matrix.fromBlocks_inj.1 hG
  simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.conjTranspose_zero, Matrix.zero_mul, Matrix.mul_neg, zero_add,
    add_zero, neg_zero] at h12
  have hAD : Q.toBlocks₁₁ᴴ * Q.toBlocks₂₂ = 1 := by simpa using h12
  have hDA : Q.toBlocks₂₂ * Q.toBlocks₁₁ᴴ = 1 := mul_eq_one_comm.1 hAD
  have h1b : Matrix.toBlocks₂₁ (1 : M2 n) = 0 := by
    ext i j; simp [Matrix.toBlocks₂₁]
  have h21 : Q.toBlocks₂₂ * N.toBlocks₂₁ = 0 := by
    have := congrArg Matrix.toBlocks₂₁ hQN
    rw [← Matrix.fromBlocks_toBlocks Q, ← Matrix.fromBlocks_toBlocks N, Matrix.fromBlocks_multiply,
      Matrix.toBlocks_fromBlocks₂₁, h1b] at this
    rw [hq, Matrix.zero_mul, zero_add] at this
    exact this
  calc N.toBlocks₂₁ = Q.toBlocks₁₁ᴴ * (Q.toBlocks₂₂ * N.toBlocks₂₁) := by
        rw [← Matrix.mul_assoc, hAD, Matrix.one_mul]
    _ = 0 := by rw [h21, Matrix.mul_zero]

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `hι.2 q`. Establish `hrc` using `(GlobalTheory.StdUnn.RealComp.real_components D θ hθ).2.2.2`. Establish `hne : finSumFinEquiv (Sum.inr i : Fin n ⊕ Fin n) ≠ finSumFinEquiv (Sum.inl j)`. Introduce `h`. Conclude with `Sum.inr_ne_inl (finSumFinEquiv.injective h)`.

Use `hrc _ (fun τ' => ?_) ?_` and prove the remaining obligations. Establish `e : θ τ' (infPart D (mat (ι q) (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)))) = compAt θ τ' (mat (ι q)) (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j))` using `rfl`. Rewrite using `[e]`. Distinguish the cases in `hτ : τ' = τ`. Substitute `hτ` using the available equality.

Rewrite using `[h1]`. Establish `h0 : (mR q).toBlocks₂₁ i j = 0` using `by rw [hq]; rfl`. Use `show (mR q) (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr i))) (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl j))) = 0`. Rewrite using `[Equiv.symm_apply_apply, Equiv.symm_apply_apply]`. Conclude with `h0`.

Rewrite using `[h2 τ' hτ, Matrix.one_apply_ne hne]`. Establish `e` using `congrFun (congrFun h3 (finSumFinEquiv (Sum.inr i))) (finSumFinEquiv (Sum.inl j))`. Rewrite `e` using `[Matrix.map_apply, Matrix.one_apply_ne hne]`. Conclude with `e`.
-/
theorem ll_zero {θ : InfFam D} (hθ : IsInfFam θ) {τ : D.what₂.Tau} {ι : GR n →* G D n} (hι : IsPlaceEmb θ τ ι)
    {q : GR n} (hq : (mR q).toBlocks₂₁ = 0) (i j : Fin n) :
    mat (ι q) (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) = 0 := by
  obtain ⟨h1, h2, h3⟩ := hι.2 q
  have hrc := (GlobalTheory.StdUnn.RealComp.real_components D θ hθ).2.2.2
  have hne : finSumFinEquiv (Sum.inr i : Fin n ⊕ Fin n) ≠ finSumFinEquiv (Sum.inl j) := by
    intro h; exact Sum.inr_ne_inl (finSumFinEquiv.injective h)
  refine hrc _ (fun τ' => ?_) ?_
  · have e : θ τ' (infPart D (mat (ι q) (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)))) =
        compAt θ τ' (mat (ι q)) (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) := rfl
    rw [e]
    by_cases hτ : τ' = τ
    · subst hτ; rw [h1]
      have h0 : (mR q).toBlocks₂₁ i j = 0 := by rw [hq]; rfl
      show (mR q) (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr i))) (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl j))) = 0
      rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      exact h0
    · rw [h2 τ' hτ, Matrix.one_apply_ne hne]
  · have e := congrFun (congrFun h3 (finSumFinEquiv (Sum.inr i))) (finSumFinEquiv (Sum.inl j))
    rw [Matrix.map_apply, Matrix.one_apply_ne hne] at e
    exact e

/- English proof (translation)
Establish `hx' : ∀ i, x (finSumFinEquiv (Sum.inr i)) = 0` using `fun i => congrFun (LinearMap.mem_ker.1 hx) i`. Use `LinearMap.mem_ker.2 (funext fun i => ?_)` and prove the remaining obligations. Use `show (M *ᵥ x) (finSumFinEquiv (Sum.inr i)) = 0`. Simplify using `only [Matrix.mulVec, dotProduct]`. Rewrite using `[← Equiv.sum_comp finSumFinEquiv, Fintype.sum_sum_type]`.

Rewrite using `[Finset.sum_eq_zero (fun a _ => by rw [hM, zero_mul]), Finset.sum_eq_zero (fun a _ => by rw [hx', mul_zero]), add_zero]`.
-/
theorem mulVec_upper {M : Matrix (Fin (n + n)) (Fin (n + n)) (AE D)}
    (hM : ∀ i j, M (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) = 0) {x : Fin (n + n) → AE D}
    (hx : x ∈ upperHalf D n) : M *ᵥ x ∈ upperHalf D n := by
  have hx' : ∀ i, x (finSumFinEquiv (Sum.inr i)) = 0 := fun i => congrFun (LinearMap.mem_ker.1 hx) i
  refine LinearMap.mem_ker.2 (funext fun i => ?_)
  show (M *ᵥ x) (finSumFinEquiv (Sum.inr i)) = 0
  simp only [Matrix.mulVec, dotProduct]
  rw [← Equiv.sum_comp finSumFinEquiv, Fintype.sum_sum_type]
  rw [Finset.sum_eq_zero (fun a _ => by rw [hM, zero_mul]), Finset.sum_eq_zero (fun a _ => by rw [hx', mul_zero]), add_zero]

/- English proof (translation)
Rewrite using `[P, Subgroup.mem_comap]`. Introduce `x`. Express the relevant statement in the definitionally equal form `x ∈ upperHalf D n ↔ mat (ι q) *ᵥ x ∈ upperHalf D n`. Use `⟨fun hx => mulVec_upper (ll_zero hθ hι hq) hx, fun hx => ?_⟩` and prove the remaining obligations. Establish `hinv : mat (ι q⁻¹) * mat (ι q) = 1`.

Rewrite using `[← mat_mul', ← map_mul, inv_mul_cancel, map_one, mat_one']`. Use `mulVec_upper (ll_zero hθ hι (up_inv hq)) hx` as an intermediate fact. Rewrite `this` using `[Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]`. Then use the resulting hypothesis.
-/
theorem iotaP_mem {θ : InfFam D} (hθ : IsInfFam θ) {τ : D.what₂.Tau} {ι : GR n →* G D n} (hι : IsPlaceEmb θ τ ι)
    {q : GR n} (hq : (mR q).toBlocks₂₁ = 0) : ι q ∈ P D n := by
  rw [P, Subgroup.mem_comap]
  intro x
  change x ∈ upperHalf D n ↔ mat (ι q) *ᵥ x ∈ upperHalf D n
  refine ⟨fun hx => mulVec_upper (ll_zero hθ hι hq) hx, fun hx => ?_⟩
  have hinv : mat (ι q⁻¹) * mat (ι q) = 1 := by
    rw [← mat_mul', ← map_mul, inv_mul_cancel, map_one, mat_one']
  have := mulVec_upper (ll_zero hθ hι (up_inv hq)) hx
  rwa [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec] at this

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem compAt_map' {θ : InfFam D} (τ : D.what₂.Tau) {m k : ℕ} (M : Mx D m k) :
    compAt θ τ M = M.map ((θ τ).comp (infPart D)) := rfl

/- English proof (translation)
Take `⟨a, ha⟩` from `GlobalTheory.StdUnn.LeftInvSect.exists_blkA hP`. Use `⟨a, ha, ?_⟩` and prove the remaining obligations. Take `⟨h1, h2, h3⟩` from `hι.2 q`. Establish `hdet : ((Matrix.GeneralLinearGroup.det a : (AE D)ˣ) : AE D) = (blkA (mat (ι q))).det`. Rewrite using `[Matrix.GeneralLinearGroup.val_det_apply, ← ha]`.

Establish `hf : finPart D ((Matrix.GeneralLinearGroup.det a : (AE D)ˣ) : AE D) = 1`. Rewrite using `[hdet, RingHom.map_det, RingHom.mapMatrix_apply, blkA_map', h3, blkA_one', Matrix.det_one]`. Establish `hτv : ∀ τ', θ τ' (infPart D ((Matrix.GeneralLinearGroup.det a : (AE D)ˣ) : AE D)) = (blkA (compAt θ τ' (mat (ι q)))).det`. Introduce `τ'`. Rewrite using `[hdet, compAt_map', ← blkA_map', ← RingHom.mapMatrix_apply, ← RingHom.map_det]`.

Both sides reduce to the same expression. Establish `hi : ∀ τ', τ' ≠ τ → θ τ' (infPart D ((Matrix.GeneralLinearGroup.det a : (AE D)ˣ) : AE D)) = 1`. Introduce `τ' h`. Rewrite using `[hτv, h2 τ' h, blkA_one', Matrix.det_one]`. Establish `habs` using `GlobalTheory.StabAtPlace.absE_single hθ (Matrix.GeneralLinearGroup.det a) τ hf hi`.

Rewrite `habs` using `[hτv, h1, blkA_reidx]`. Establish `habs' : absA D (Matrix.GeneralLinearGroup.det a) = ‖(mR q).toBlocks₁₁.det‖₊ ^ 2` using `habs`. Rewrite using `[habs']`. Simplify using the standard rewrite rules.
-/
theorem iota_abs {θ : InfFam D} (hθ : IsInfFam θ) {τ : D.what₂.Tau} {ι : GR n →* G D n} (hι : IsPlaceEmb θ τ ι)
    {q : GR n} (hP : ι q ∈ P D n) : ∃ a : GL (Fin n) (AE D), blkA (mat (ι q)) = a.1 ∧
      (absA D (Matrix.GeneralLinearGroup.det a) : ℝ) = ‖(mR q).toBlocks₁₁.det‖ ^ 2 := by
  obtain ⟨a, ha⟩ := GlobalTheory.StdUnn.LeftInvSect.exists_blkA hP
  refine ⟨a, ha, ?_⟩
  obtain ⟨h1, h2, h3⟩ := hι.2 q
  have hdet : ((Matrix.GeneralLinearGroup.det a : (AE D)ˣ) : AE D) = (blkA (mat (ι q))).det := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, ← ha]
  have hf : finPart D ((Matrix.GeneralLinearGroup.det a : (AE D)ˣ) : AE D) = 1 := by
    rw [hdet, RingHom.map_det, RingHom.mapMatrix_apply, blkA_map', h3, blkA_one', Matrix.det_one]
  have hτv : ∀ τ', θ τ' (infPart D ((Matrix.GeneralLinearGroup.det a : (AE D)ˣ) : AE D)) =
      (blkA (compAt θ τ' (mat (ι q)))).det := by
    intro τ'
    rw [hdet, compAt_map', ← blkA_map', ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rfl
  have hi : ∀ τ', τ' ≠ τ → θ τ' (infPart D ((Matrix.GeneralLinearGroup.det a : (AE D)ˣ) : AE D)) = 1 := by
    intro τ' h
    rw [hτv, h2 τ' h, blkA_one', Matrix.det_one]
  have habs := GlobalTheory.StabAtPlace.absE_single hθ (Matrix.GeneralLinearGroup.det a) τ hf hi
  rw [hτv, h1, blkA_reidx] at habs
  have habs' : absA D (Matrix.GeneralLinearGroup.det a) = ‖(mR q).toBlocks₁₁.det‖₊ ^ 2 := habs
  rw [habs']
  simp

/- English proof (translation)
Assemble the required witnesses or components as `⟨iotaP_mem hθ hι hq, iota_abs hθ hι (iotaP_mem hθ hι hq)⟩`.
-/
theorem iota_mem_P {θ : InfFam D} (hθ : IsInfFam θ) {τ : D.what₂.Tau} {ι : GR n →* G D n} (hι : IsPlaceEmb θ τ ι)
    {q : GR n} (hq : (mR q).toBlocks₂₁ = 0) : ι q ∈ P D n ∧ ∃ a : GL (Fin n) (AE D), blkA (mat (ι q)) = a.1 ∧
      (absA D (Matrix.GeneralLinearGroup.det a) : ℝ) = ‖(mR q).toBlocks₁₁.det‖ ^ 2 :=
  ⟨iotaP_mem hθ hι hq, iota_abs hθ hι (iotaP_mem hθ hι hq)⟩

end PositivityTheory.Rg.Sw.Glob
