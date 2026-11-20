import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRatPairIff

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilPairPartner

/- English proof (translation)
Rewrite using `[← Matrix.map_mul, M.mul_nonsing_inv (isUnit_iff_ne_zero.mpr h), Matrix.map_one _ f.map_zero f.map_one]`.
-/
theorem map_mul_map_inv {R S : Type} [Field R] [CommRing S] (f : R →+* S) {n : Type} [Fintype n] [DecidableEq n]
    (M : Matrix n n R) (h : M.det ≠ 0) : M.map f * (M⁻¹).map f = 1 := by
  rw [← Matrix.map_mul, M.mul_nonsing_inv (isUnit_iff_ne_zero.mpr h), Matrix.map_one _ f.map_zero f.map_one]

/- English proof (translation)
Rewrite using `[← Matrix.map_mul, M.nonsing_inv_mul (isUnit_iff_ne_zero.mpr h), Matrix.map_one _ f.map_zero f.map_one]`.
-/
theorem map_inv_mul_map {R S : Type} [Field R] [CommRing S] (f : R →+* S) {n : Type} [Fintype n] [DecidableEq n]
    (M : Matrix n n R) (h : M.det ≠ 0) : (M⁻¹).map f * M.map f = 1 := by
  rw [← Matrix.map_mul, M.nonsing_inv_mul (isUnit_iff_ne_zero.mpr h), Matrix.map_one _ f.map_zero f.map_one]

/- English proof (translation)
Use extensionality with `i j`. Simplify using the standard rewrite rules.
-/
theorem map_smul_eq {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {m n : Type} (r : R) (M : Matrix m n R) :
    (r • M).map f = f r • M.map f := by
  ext i j
  simp

/- English proof (translation)
Establish `hbN : Bᵀ * N * B.map c = N`. Establish `h1 : Bᵀ * (ξ • K) * B.map c = ξ • K` using `by rw [Matrix.mul_smul, Matrix.smul_mul, hb]`. Rewrite `h1` using `[hK, Matrix.mul_smul, Matrix.smul_mul]`. Conclude with `hu.smul_left_cancel.mp h1`. Establish `hcc : Bi.map c * B.map c = 1`.

Rewrite using `[← Matrix.map_mul, hBB', Matrix.map_one _ c.map_zero c.map_one]`. Establish `hTT : Biᵀ * Bᵀ = 1` using `by rw [← Matrix.transpose_mul, hBB, Matrix.transpose_one]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem conj_inv_transpose {S : Type} [CommRing S] (c : S →+* S) {n : Type} [Fintype n] [DecidableEq n] (ξ u : S)
    (hu : IsUnit u) (B Bi K G N : Matrix n n S) (hb : Bᵀ * K * B.map c = K) (hBB : B * Bi = 1) (hBB' : Bi * B = 1)
    (hK : ξ • K = u • N) (hGN : G * N = 1) (hNG : N * G = 1) : Bi.map c * G * Biᵀ = G := by
  have hbN : Bᵀ * N * B.map c = N := by
    have h1 : Bᵀ * (ξ • K) * B.map c = ξ • K := by rw [Matrix.mul_smul, Matrix.smul_mul, hb]
    rw [hK, Matrix.mul_smul, Matrix.smul_mul] at h1
    exact hu.smul_left_cancel.mp h1
  have hcc : Bi.map c * B.map c = 1 := by
    rw [← Matrix.map_mul, hBB', Matrix.map_one _ c.map_zero c.map_one]
  have hTT : Biᵀ * Bᵀ = 1 := by rw [← Matrix.transpose_mul, hBB, Matrix.transpose_one]
  calc Bi.map c * G * Biᵀ = Bi.map c * G * Biᵀ * (N * G) := by rw [hNG, Matrix.mul_one]
    _ = Bi.map c * G * Biᵀ * ((Bᵀ * N * B.map c) * G) := by rw [hbN]
    _ = Bi.map c * G * (Biᵀ * Bᵀ) * N * B.map c * G := by simp only [Matrix.mul_assoc]
    _ = Bi.map c * (G * N) * B.map c * G := by rw [hTT, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = G := by rw [hGN, Matrix.mul_one, hcc, Matrix.one_mul]

/- English proof (translation)
Introduce `D S T JA JB ξ hA hB a b`. Establish `hmap : ∀ {m n : Type} (X : Matrix m n (AE D)), X.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) = X.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig)` using `fun X => Matrix.ext fun i j => rfl`. Establish `ha : (a.1.val)ᵀ * incM D.host.F JA * (a.1.val).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) = incM D.host.F JA` using `a.2`. Use `set A : Matrix (Fin T.rank) (Fin T.rank) (AE D) := a.1.val with hAdef`. Establish `hJA : incM D.host.F JA = (incM D.host.F T.gram)ᵀ`.

Rewrite using `[hA]`. Both sides reduce to the same expression. Rewrite `ha` using `[hJA]`. Establish `ha'` using `congrArg Matrix.transpose ha`. Simplify using `only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc] at ha'`.

Establish `hmemA : a.1 ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (AF D.host.F) D.sp.cm.sig T.gram` using `by show Formalism.UG.cT _ a.1.val * _ * a.1.val = _`. Simplify using `only [Formalism.UG.cT, hmap]`. Rewrite using `[Matrix.mul_assoc]`. Conclude with `ha'`. Take `⟨cR, hcR⟩ : ∃ f, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig = f` from `⟨_, rfl⟩`.

Establish `hb : (b.1.val)ᵀ * incM D.host.F JB * (b.1.val).map cR = incM D.host.F JB`. Rewrite using `[← hcR, hmap]`. Conclude with `b.2`. Establish `hBB : b.1.val * (b⁻¹).1.val = 1`. Rewrite using `[Subgroup.coe_inv]`.

Conclude with `(b.1).mul_inv`. Establish `hBB' : (b⁻¹).1.val * b.1.val = 1`. Rewrite using `[Subgroup.coe_inv]`. Conclude with `(b.1).inv_mul`. Take `⟨B, hBdef⟩ : ∃ B : Matrix (Fin S.rank) (Fin S.rank) (AE D), b.1.val = B` from `⟨_, rfl⟩`.

Take `⟨Bi, hBidef⟩ : ∃ B : Matrix (Fin S.rank) (Fin S.rank) (AE D), (b⁻¹).1.val = B` from `⟨_, rfl⟩`. Rewrite `hb`, `hBB`, `hBB'` using `[hBdef]`. Rewrite `hBB`, `hBB'` using `[hBidef]`. Establish `hGN` using `GlobalTheory.WeilPairPartner.map_mul_map_inv (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F)) S.gram (GlobalTheory.VolHeckeCompare.gram_det_ne_zero S)`. Establish `hNG` using `GlobalTheory.WeilPairPartner.map_inv_mul_map (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F)) S.gram (GlobalTheory.VolHeckeCompare.gram_det_ne_zero S)`.

Establish `hsm : incM D.host.F (D.host.xi0 • S.gram⁻¹) = inclR (F` using `D.host.F) (AF D.host.F) D.host.xi0 • incM D.host.F S.gram⁻¹ := GlobalTheory.WeilPairPartner.map_smul_eq _ _ _`. Establish `hu : IsUnit (inclR (F` using `D.host.F) (AF D.host.F) D.host.xi0) := (isUnit_iff_ne_zero.mpr (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)).map _`. Establish `hcore` using `GlobalTheory.WeilPairPartner.conj_inv_transpose cR ξ _ hu B Bi (incM D.host.F JB) (incM D.host.F S.gram) (incM D.host.F S.gram⁻¹) hb hBB hBB' (hB.trans hsm) hGN hNG`. Establish `hTT : Biᵀ * Bᵀ = 1`. Rewrite using `[← Matrix.transpose_mul, hBB, Matrix.transpose_one]`.

Set `gU : GL (Fin S.rank) (AE D)` to `⟨Biᵀ, Bᵀ, hTT, by rw [← Matrix.transpose_mul, hBB', Matrix.transpose_one]⟩`. Establish `hmemB : gU ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (AF D.host.F) D.sp.cm.sig S.gram` using `by show Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) Biᵀ * incM D.host.F S.gram * Biᵀ = incM D.host.F S.gram`. Rewrite using `[hcR]`. Simplify using `only [Formalism.UG.cT, Matrix.transpose_map, Matrix.transpose_transpose]`. Conclude with `hcore`.

Use `⟨⟨gU, hmemB⟩, ⟨a.1, hmemA⟩, rfl, ?_⟩` and prove the remaining obligations. Use `show Biᵀ = ((b⁻¹).1.val)ᵀ`. Rewrite using `[hBidef]`.
-/
theorem pair_partner : ∀ (D : D7) (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E)
    (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
    ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
    ∀ (a : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA))
      (b : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB)),
      ∃ (g : GA D S) (h : GA D T), mt T h = a.1.1 ∧ mt S g = (b⁻¹).1.1ᵀ := by
  intro D S T JA JB ξ hA hB a b
  have hmap : ∀ {m n : Type} (X : Matrix m n (AE D)),
      X.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) = X.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) :=
    fun X => Matrix.ext fun i j => rfl

  have ha : (a.1.val)ᵀ * incM D.host.F JA * (a.1.val).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) = incM D.host.F JA := a.2
  set A : Matrix (Fin T.rank) (Fin T.rank) (AE D) := a.1.val with hAdef
  have hJA : incM D.host.F JA = (incM D.host.F T.gram)ᵀ := by
    rw [hA]; rfl
  rw [hJA] at ha
  have ha' := congrArg Matrix.transpose ha
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc] at ha'
  have hmemA : a.1 ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (AF D.host.F) D.sp.cm.sig T.gram := by
    show Formalism.UG.cT _ a.1.val * _ * a.1.val = _
    simp only [Formalism.UG.cT, hmap]
    rw [Matrix.mul_assoc]
    exact ha'

  obtain ⟨cR, hcR⟩ : ∃ f, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig = f := ⟨_, rfl⟩
  have hb : (b.1.val)ᵀ * incM D.host.F JB * (b.1.val).map cR = incM D.host.F JB := by
    rw [← hcR, hmap]; exact b.2
  have hBB : b.1.val * (b⁻¹).1.val = 1 := by
    rw [Subgroup.coe_inv]; exact (b.1).mul_inv
  have hBB' : (b⁻¹).1.val * b.1.val = 1 := by
    rw [Subgroup.coe_inv]; exact (b.1).inv_mul
  obtain ⟨B, hBdef⟩ : ∃ B : Matrix (Fin S.rank) (Fin S.rank) (AE D), b.1.val = B := ⟨_, rfl⟩
  obtain ⟨Bi, hBidef⟩ : ∃ B : Matrix (Fin S.rank) (Fin S.rank) (AE D), (b⁻¹).1.val = B := ⟨_, rfl⟩
  rw [hBdef] at hb hBB hBB'
  rw [hBidef] at hBB hBB'
  have hGN := GlobalTheory.WeilPairPartner.map_mul_map_inv (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F)) S.gram
    (GlobalTheory.VolHeckeCompare.gram_det_ne_zero S)
  have hNG := GlobalTheory.WeilPairPartner.map_inv_mul_map (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F)) S.gram
    (GlobalTheory.VolHeckeCompare.gram_det_ne_zero S)
  have hsm : incM D.host.F (D.host.xi0 • S.gram⁻¹) = inclR (F := D.host.F) (AF D.host.F) D.host.xi0 •
      incM D.host.F S.gram⁻¹ :=
    GlobalTheory.WeilPairPartner.map_smul_eq _ _ _
  have hu : IsUnit (inclR (F := D.host.F) (AF D.host.F) D.host.xi0) :=
    (isUnit_iff_ne_zero.mpr (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)).map _
  have hcore := GlobalTheory.WeilPairPartner.conj_inv_transpose cR ξ _ hu B Bi (incM D.host.F JB) (incM D.host.F S.gram)
    (incM D.host.F S.gram⁻¹) hb hBB hBB' (hB.trans hsm) hGN hNG
  have hTT : Biᵀ * Bᵀ = 1 := by
    rw [← Matrix.transpose_mul, hBB, Matrix.transpose_one]
  let gU : GL (Fin S.rank) (AE D) :=
    ⟨Biᵀ, Bᵀ, hTT, by rw [← Matrix.transpose_mul, hBB', Matrix.transpose_one]⟩
  have hmemB : gU ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (AF D.host.F) D.sp.cm.sig S.gram := by
    show Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) Biᵀ * incM D.host.F S.gram * Biᵀ =
      incM D.host.F S.gram
    rw [hcR]
    simp only [Formalism.UG.cT, Matrix.transpose_map, Matrix.transpose_transpose]
    exact hcore
  refine ⟨⟨gU, hmemB⟩, ⟨a.1, hmemA⟩, rfl, ?_⟩
  show Biᵀ = ((b⁻¹).1.val)ᵀ
  rw [hBidef]

end GlobalTheory.WeilPairPartner
