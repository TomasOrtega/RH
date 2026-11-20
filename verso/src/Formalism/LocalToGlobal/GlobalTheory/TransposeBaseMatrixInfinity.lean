import Formalism.LocalToGlobal.GlobalTheory.NatInvMemIntW
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ExistsPrimeToLe

noncomputable section

open Matrix NumberField

namespace Formalism.L2.GlobalTheoryTheory.ColValS

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.Inhab

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

/- English proof (translation)
Use `haveI := D.host.isCMField_hostE`. Use `show D.host.emb (D.eTau τ : D.R.GG) (Formalism.L2.Forms.sigD D a) = starRingEnd ℂ (D.host.emb (D.eTau τ : D.R.GG) a)`. Conclude with `NumberField.IsCMField.complexEmbedding_complexConj D.host.E _ a`.
-/
theorem embT_sigD (τ : D.what₂.Tau) (a : D.host.E) :
    Formalism.L2.Forms.embT D τ (Formalism.L2.Forms.sigD D a) = starRingEnd ℂ (Formalism.L2.Forms.embT D τ a) := by
  haveI := D.host.isCMField_hostE
  show D.host.emb (D.eTau τ : D.R.GG) (Formalism.L2.Forms.sigD D a) = starRingEnd ℂ (D.host.emb (D.eTau τ : D.R.GG) a)
  exact NumberField.IsCMField.complexEmbedding_complexConj D.host.E _ a

/- English proof (translation)
Rewrite using `[rhoC_conj D.what₂.embLL τ a]`. Use `congr 1`. Conclude with `(Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwA_embT_eq D τ a).symm`.
-/
theorem embLL_rhoC (τ : D.what₂.Tau) (a : D.host.E) :
    D.what₂.embLL (rhoC D τ a) = starRingEnd ℂ (Formalism.L2.Forms.embT D τ a) := by
  rw [rhoC_conj D.what₂.embLL τ a]
  congr 1
  exact (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwA_embT_eq D τ a).symm

/- English proof (translation)
Use `letI := D.host.cmStar`. Simplify using `only [Formalism.L2.Forms.gramN, Matrix.reindex_apply, Matrix.submatrix_apply, Formalism.BasicNotions.HSpace.gram]`. Use `first`. Consider the case `exact ((D.sp.X 0).herm _ _).symm`. Consider the case `exact ((D.sp.X 0).herm.eq _ _).symm`.
-/
theorem gramN_sig (i j : Fin (D.R.N 0)) :
    Formalism.L2.Forms.gramN D 0 (Nat.zero_le _) i j = Formalism.L2.Forms.sigD D (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _) j i) := by
  letI := D.host.cmStar
  simp only [Formalism.L2.Forms.gramN, Matrix.reindex_apply, Matrix.submatrix_apply, Formalism.BasicNotions.HSpace.gram]
  first
  | exact ((D.sp.X 0).herm _ _).symm
  | exact ((D.sp.X 0).herm.eq _ _).symm

def BaseBlockInverse (Y : GL (Fin (D.R.N 0)) D.host.E) : GL (Fin (D.R.N 0)) D.host.E :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    (Formalism.UG.cT (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *
      Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (by
    rw [Matrix.det_mul, Formalism.UG.cT, Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact mul_ne_zero ((map_ne_zero _).2 (Matrix.isUnits_det_units Y).ne_zero) gramN_det_ne)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem B0inv_coe (Y : GL (Fin (D.R.N 0)) D.host.E) :
    ((BaseBlockInverse Y : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) =
      Formalism.UG.cT (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *
        Formalism.L2.Forms.gramN D 0 (Nat.zero_le _) := rfl

/- English proof (translation)
Rewrite using `[B0inv_coe]`. Use extensionality with `i j`. Simplify using `only [Matrix.transpose_apply, Matrix.map_apply, Formalism.L2.Forms.atInf, Formalism.UG.cT, Matrix.mul_apply, map_sum, map_mul, AlgHom.coe_toRingHom]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[embLL_rhoC, embLL_rhoC, gramN_sig j k, embT_sigD, embT_sigD, starRingEnd_self_apply, mul_comm]`.
-/
theorem transpose_base_matrix_infinity (Y : GL (Fin (D.R.N 0)) D.host.E) (τ : D.what₂.Tau) :
    (((Formalism.L2.Forms.gramN D 0 (Nat.zero_le _) * (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)).map (rhoC D τ)).map
      D.what₂.embLL)ᵀ =
      Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) ((BaseBlockInverse Y : GL (Fin (D.R.N 0)) D.host.E) :
        Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ := by
  rw [B0inv_coe]
  ext i j
  simp only [Matrix.transpose_apply, Matrix.map_apply, Formalism.L2.Forms.atInf, Formalism.UG.cT, Matrix.mul_apply, map_sum, map_mul,
    AlgHom.coe_toRingHom]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [embLL_rhoC, embLL_rhoC, gramN_sig j k, embT_sigD, embT_sigD, starRingEnd_self_apply, mul_comm]

variable {u : D.what₂.Word} (B : ColBase D u)

/- English proof (translation)
Establish `hMb : IsUnit (Mb B c τ).det` using `isUnit_iff_ne_zero.mpr (Mb_det_ne B c τ)`. Establish `hGY : ((Formalism.L2.Forms.gramN D 0 (Nat.zero_le _) * (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)).map (rhoC D τ)).det ≠ 0`. Rewrite using `[← RingHom.mapMatrix_apply, ← RingHom.map_det, Matrix.det_mul]`. Conclude with `(map_ne_zero _).2 (mul_ne_zero gramN_det_ne (Matrix.isUnits_det_units Y).ne_zero)`. Establish `hA : (Mb B c τ * (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E).map (rhoC D τ))⁻¹ * (Mb B c τ * ((Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map (rhoC D τ))⁻¹) = ((Formalism.L2.Forms.gramN D 0 (Nat.zero_le _) * (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)).map …`.

Rewrite using `[Matrix.map_mul, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_assoc, ← Matrix.mul_assoc (Mb B c τ)⁻¹, Matrix.nonsing_inv_mul _ hMb, Matrix.one_mul]`. Rewrite using `[gC_coe, hB, hA, ← transpose_base_matrix_infinity Y τ, ← Matrix.transpose_mul, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hGY)]`. Simplify using the standard rewrite rules.
-/
theorem h_T_mul (hB : B.rho = rhoC D) (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) (Y : GL (Fin (D.R.N 0)) D.host.E) :
    (((Mb B c τ * (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E).map (B.rho τ))⁻¹ *
        ((gC B c τ : GL (Fin (D.R.N 0)) D.what₂.LL) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL)).map D.what₂.embLL)ᵀ *
      Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) ((BaseBlockInverse Y : GL (Fin (D.R.N 0)) D.host.E) :
        Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ = 1 := by
  have hMb : IsUnit (Mb B c τ).det := isUnit_iff_ne_zero.mpr (Mb_det_ne B c τ)
  have hGY : ((Formalism.L2.Forms.gramN D 0 (Nat.zero_le _) *
      (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)).map (rhoC D τ)).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, Matrix.det_mul]
    exact (map_ne_zero _).2 (mul_ne_zero gramN_det_ne (Matrix.isUnits_det_units Y).ne_zero)
  have hA : (Mb B c τ * (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E).map (rhoC D τ))⁻¹ *
      (Mb B c τ * ((Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map (rhoC D τ))⁻¹) =
      ((Formalism.L2.Forms.gramN D 0 (Nat.zero_le _) *
        (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)).map (rhoC D τ))⁻¹ := by
    rw [Matrix.map_mul, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_assoc,
      ← Matrix.mul_assoc (Mb B c τ)⁻¹, Matrix.nonsing_inv_mul _ hMb, Matrix.one_mul]
  rw [gC_coe, hB, hA, ← transpose_base_matrix_infinity Y τ, ← Matrix.transpose_mul, ← Matrix.map_mul,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hGY)]
  simp

/- English proof (translation)
Unfold `Formalism.L2.Forms.atInf`. Rewrite using `[← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Conclude with `(Matrix.isUnits_det_units (BaseBlockInverse Y)).map _`.
-/
theorem isUnit_base_inverse_infinity (Y : GL (Fin (D.R.N 0)) D.host.E) (τ : D.what₂.Tau) :
    IsUnit (Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) ((BaseBlockInverse Y : GL (Fin (D.R.N 0)) D.host.E) :
      Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ).det := by
  unfold Formalism.L2.Forms.atInf
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (Matrix.isUnits_det_units (BaseBlockInverse Y)).map _

/- English proof (translation)
Establish `: Fact (D.what₂.places.resChar w).Prime` using `⟨D.what₂.places.resChar_prime w⟩`. Use `set p := co0 T0 x c with hp`. Use `set lam := (D.fm u).lam 0 with hlam`. Use `set Gf := Formalism.L2.Forms.gramC (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Formalism.L2.Forms.embT D) with hGf`. Use `set s0 := Formalism.L2.Forms.shiftOf (Formalism.L2.Forms.lamT u 0) with hs0`.

Use `set hh : D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ := fun τ => ((Mb B c τ * (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E).map (B.rho τ))⁻¹ * ((gC B c τ : GL (Fin (D.R.N 0)) D.what₂.LL) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL)).map D.what₂.embLL wi …`. Use `set N0 : D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ := Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) ((BaseBlockInverse Y : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) with hN0`. Establish `hK : (fun τ => (hh τ)ᵀ * N0 τ) = 1` using `funext fun τ => h_T_mul B hB c τ Y`. Establish `hs : ∀ τ, s0 τ = (lam τ).detShift` using `fun τ => by rw [hs0, Formalism.L2.Forms.lamT_zero]; rfl`. Establish `hemb : ∀ z, (D.fm u).emb 0 x c z = Formalism.L2.Forms.fnOf Gf s0 1 (MvPolynomial.map D.what₂.embLL p) (T0.val0.eY z)` using `fun z => pol_spec T0 x c z`.

Establish `hRHS : Formalism.MainNotions.flipTwoThree.actAll lam (fun τ => (Mb B c τ * (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E).map (B.rho τ))⁻¹) (coT T0 (gC B) x c) ∈ Formalism.MainNotions.flipTwoThree.IntSpanAt D w lam ↔ Formalism.MainNotions.flipTwoThree.actAll lam hh (MvPoly …`. Rewrite using `[coT_apply, actAll_comp, mem_intSpanAt_iff_map, map_actAll]`. Establish `hfn : Formalism.L2.Forms.fnOf Gf s0 N0 (Formalism.MainNotions.flipTwoThree.actAll lam hh (MvPolynomial.map D.what₂.embLL p)) = Formalism.L2.Forms.fnOf Gf s0 1 (MvPolynomial.map D.what₂.embLL p)`. Establish `h1` using `Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.fnOf_mul Gf s0 (fun τ => (hh τ)ᵀ) N0 (MvPolynomial.map D.what₂.embLL p)`. Rewrite `h1` using `[hK]`.

Rewrite using `[h1, actAll_eq_subP, MvPolynomial.smul_eq_C_mul]`. Use `congr 3`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.det_transpose, hs]`. Establish `hB0 : Formalism.L2.Forms.IsLocBasis (D.what₂.places.resChar w) (dualSet (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Formalism.L2.Forms.clsCrd D u 0 (Nat.zero_le _) c)) (BaseBlockInverse Y)⁻¹` using `isLocBasis_dual (D.what₂.places.resChar w) _ _ (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_clsCrd_lat D u 0 (Nat.zero_le _) c).fg hY _ (by rw [inv_inv]; rfl)`.

Establish `hN0' : Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) ((((BaseBlockInverse Y)⁻¹)⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) = N0`. Rewrite using `[inv_inv]`. Rewrite using `[hRHS]`. Prove the components needed by the constructor for the conclusion. Introduce `hAll`.

Take `⟨P, hP, hPz⟩` from `hAll _ hB0`. Rewrite `hPz` using `[hN0']`. Establish `hPe : Formalism.L2.Forms.fnOf Gf s0 N0 P = Formalism.L2.Forms.fnOf Gf s0 N0 (Formalism.MainNotions.flipTwoThree.actAll lam hh (MvPolynomial.map D.what₂.embLL p))`. Use function extensionality and compare the values at `y`. Take `⟨z, rfl⟩` from `T0.val0.eY.surjective y`.

Rewrite using `[hfn, ← hemb, hPz]`. Use `Formalism.L2.Col.fnOf_injective Gf s0 N0 (isUnit_base_inverse_infinity Y) (Formalism.MainNotions.Ext.Lw.frOne Gf) hPe` as an intermediate fact. Rewrite using `[← this]`. Conclude with `hP`. Introduce `hQ Bb hBb`.

Take `⟨Q₂, hQ₂, hQe⟩` from `basis_change D w lam Gf s0 hB0 hBb _ hQ`. Rewrite `hQe` using `[hN0']`. Use `⟨Q₂, hQ₂, fun z => ?_⟩` and prove the remaining obligations. Rewrite using `[hemb, ← hfn, hQe]`.
-/
theorem clause_iff (T0 : Formalism.L2.Forms.Forms0 D u) (hB : B.rho = rhoC D) (w : D.what₂.places.Pl) (c : (D.mem u).C.cls 0)
    (Y : GL (Fin (D.R.N 0)) D.host.E)
    (hY : Formalism.L2.Forms.IsLocBasis (D.what₂.places.resChar w)
      (Formalism.L2.Forms.clsCrd D u 0 (Nat.zero_le _) c : Set (Fin (D.R.N 0) → D.host.E)) Y)
    (x : ((D.fm u).lat 0).V) :
    (∀ Bb : GL (Fin (D.R.N 0)) D.host.E,
      Formalism.L2.Forms.IsLocBasis (D.what₂.places.resChar w)
        (dualSet (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _))
          (Formalism.L2.Forms.clsCrd D u 0 (Nat.zero_le _) c)) Bb →
      ∃ P ∈ Formalism.L2.Forms.IntSpan D w ((D.fm u).lam 0),
        ∀ z, (D.fm u).emb 0 x c z =
          Formalism.L2.Forms.fnOf _ (Formalism.L2.Forms.shiftOf (Formalism.L2.Forms.lamT u 0))
            (Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) (Bb⁻¹ : GL (Fin (D.R.N 0)) D.host.E).1) P (T0.val0.eY z)) ↔
    Formalism.MainNotions.flipTwoThree.actAll ((D.fm u).lam 0)
      (fun τ => (Mb B c τ * (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E).map (B.rho τ))⁻¹)
      (coT T0 (gC B) x c) ∈ Formalism.MainNotions.flipTwoThree.IntSpanAt D w ((D.fm u).lam 0) := by
  have : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
  set p := co0 T0 x c with hp
  set lam := (D.fm u).lam 0 with hlam
  set Gf := Formalism.L2.Forms.gramC (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Formalism.L2.Forms.embT D) with hGf
  set s0 := Formalism.L2.Forms.shiftOf (Formalism.L2.Forms.lamT u 0) with hs0
  set hh : D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ := fun τ =>
    ((Mb B c τ * (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E).map (B.rho τ))⁻¹ *
      ((gC B c τ : GL (Fin (D.R.N 0)) D.what₂.LL) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL)).map D.what₂.embLL with hhh
  set N0 : D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ :=
    Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) ((BaseBlockInverse Y : GL (Fin (D.R.N 0)) D.host.E) :
      Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) with hN0
  have hK : (fun τ => (hh τ)ᵀ * N0 τ) = 1 := funext fun τ => h_T_mul B hB c τ Y
  have hs : ∀ τ, s0 τ = (lam τ).detShift := fun τ => by rw [hs0, Formalism.L2.Forms.lamT_zero]; rfl
  have hemb : ∀ z, (D.fm u).emb 0 x c z =
      Formalism.L2.Forms.fnOf Gf s0 1 (MvPolynomial.map D.what₂.embLL p) (T0.val0.eY z) := fun z => pol_spec T0 x c z
  have hRHS : Formalism.MainNotions.flipTwoThree.actAll lam
      (fun τ => (Mb B c τ * (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E).map (B.rho τ))⁻¹)
      (coT T0 (gC B) x c) ∈ Formalism.MainNotions.flipTwoThree.IntSpanAt D w lam ↔
      Formalism.MainNotions.flipTwoThree.actAll lam hh (MvPolynomial.map D.what₂.embLL p) ∈ Formalism.L2.Forms.IntSpan D w lam := by
    rw [coT_apply, actAll_comp, mem_intSpanAt_iff_map, map_actAll]
  have hfn : Formalism.L2.Forms.fnOf Gf s0 N0 (Formalism.MainNotions.flipTwoThree.actAll lam hh (MvPolynomial.map D.what₂.embLL p)) =
      Formalism.L2.Forms.fnOf Gf s0 1 (MvPolynomial.map D.what₂.embLL p) := by
    have h1 := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.fnOf_mul Gf s0 (fun τ => (hh τ)ᵀ) N0 (MvPolynomial.map D.what₂.embLL p)
    rw [hK] at h1
    rw [h1, actAll_eq_subP, MvPolynomial.smul_eq_C_mul]
    congr 3
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [Matrix.det_transpose, hs]
  have hB0 : Formalism.L2.Forms.IsLocBasis (D.what₂.places.resChar w)
      (dualSet (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _))
        (Formalism.L2.Forms.clsCrd D u 0 (Nat.zero_le _) c)) (BaseBlockInverse Y)⁻¹ :=
    isLocBasis_dual (D.what₂.places.resChar w) _ _ (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_clsCrd_lat D u 0 (Nat.zero_le _) c).fg hY _
      (by rw [inv_inv]; rfl)
  have hN0' : Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) ((((BaseBlockInverse Y)⁻¹)⁻¹ : GL (Fin (D.R.N 0)) D.host.E) :
      Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) = N0 := by
    rw [inv_inv]
  rw [hRHS]
  constructor
  · intro hAll
    obtain ⟨P, hP, hPz⟩ := hAll _ hB0
    rw [hN0'] at hPz
    have hPe : Formalism.L2.Forms.fnOf Gf s0 N0 P =
        Formalism.L2.Forms.fnOf Gf s0 N0 (Formalism.MainNotions.flipTwoThree.actAll lam hh (MvPolynomial.map D.what₂.embLL p)) := by
      funext y
      obtain ⟨z, rfl⟩ := T0.val0.eY.surjective y
      rw [hfn, ← hemb, hPz]
    have := Formalism.L2.Col.fnOf_injective Gf s0 N0 (isUnit_base_inverse_infinity Y) (Formalism.MainNotions.Ext.Lw.frOne Gf) hPe
    rw [← this]
    exact hP
  · intro hQ Bb hBb
    obtain ⟨Q₂, hQ₂, hQe⟩ := basis_change D w lam Gf s0 hB0 hBb _ hQ
    rw [hN0'] at hQe
    refine ⟨Q₂, hQ₂, fun z => ?_⟩
    rw [hemb, ← hfn, hQe]

/- English proof (translation)
Introduce `w`. Establish `: Fact (D.what₂.places.resChar w).Prime` using `⟨D.what₂.places.resChar_prime w⟩`. Establish `hex : ∀ c : (D.mem u).C.cls 0, ∃ Y : GL (Fin (D.R.N 0)) D.host.E, Formalism.L2.Forms.IsLocBasis (D.what₂.places.resChar w) (Formalism.L2.Forms.clsCrd D u 0 (Nat.zero_le _) c : Set (Fin (D.R.N 0) → D.host.E)) Y` using `fun c => Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.exists_isLocBasis (l := D.what₂.places.resChar w) (K := D.host.E) _ (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_clsCrd_lat D u 0 (Nat.zero_le _) c).fg (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB …`. Use `choose Y hY using hex`. Use `⟨fun c τ => Mb B c τ * (Y c : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E).map (B.rho τ), fun c τ => locBasis_gamma B hB w c τ (Y c) (hY c), fun x => ?_⟩` and prove the remaining obligations.

Rewrite using `[Formalism.L2.G.Cmp.locWCrit_proved T u w x]`. Conclude with `forall_congr' fun c => clause_iff B (T u) hB w c (Y c) (hY c) x`.
-/
theorem finCo_of (T : ∀ u : D.what₂.Word, Formalism.L2.Forms.Forms0 D u) (u : D.what₂.Word) (B : ColBase D u)
    (hB : B.rho = rhoC D) : FinCo (T u) B := by
  intro w
  have : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
  have hex : ∀ c : (D.mem u).C.cls 0, ∃ Y : GL (Fin (D.R.N 0)) D.host.E,
      Formalism.L2.Forms.IsLocBasis (D.what₂.places.resChar w)
        (Formalism.L2.Forms.clsCrd D u 0 (Nat.zero_le _) c : Set (Fin (D.R.N 0) → D.host.E)) Y := fun c =>
    Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.exists_isLocBasis (l := D.what₂.places.resChar w) (K := D.host.E) _
      (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_clsCrd_lat D u 0 (Nat.zero_le _) c).fg
      (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_clsCrd_lat D u 0 (Nat.zero_le _) c).span_eq_top
  choose Y hY using hex
  refine ⟨fun c τ => Mb B c τ * (Y c : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E).map (B.rho τ),
    fun c τ => locBasis_gamma B hB w c τ (Y c) (hY c), fun x => ?_⟩
  rw [Formalism.L2.G.Cmp.locWCrit_proved T u w x]
  exact forall_congr' fun c => clause_iff B (T u) hB w c (Y c) (hY c) x

/- English proof (translation)
The claim follows from `colValOfTiedS_of_fin fun _ F _ u B hB => finCo_of (fun u => (F.forms u).to0) u B hB`.
-/
theorem colValOfTiedS_holds : Formalism.MainNotions.RT.ColumnValuationFromTwistCompatibility :=
  colValOfTiedS_of_fin fun _ F _ u B hB => finCo_of (fun u => (F.forms u).to0) u B hB

end Formalism.L2.GlobalTheoryTheory.ColValS
