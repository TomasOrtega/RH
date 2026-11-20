import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ScalesBy
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrOfIsotropic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalCoordinatesGroupLaw
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentFrameCoordsOfMemIsotropicUnipoten
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentRadicalPointWithCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviSectionIsotropicFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicFrameDecompositionSubgroupProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameLeviNormalizesRadicalProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemidirectHaarMeasureProduct
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulVecCEApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSkewA
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)
open GlobalTheory.ResidueEisenstein.ModConj

noncomputable section

namespace GlobalTheory.ResidueEisenstein.LeviConj

open GlobalTheory.SphEis GlobalTheory.SphEis.UnipCrd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Use extensionality with `i k`. Simplify using `[cT]`.
-/
theorem cT_smul' (s : AF F ⊗[F] E →+* AF F ⊗[F] E) {p q : Type} (a : AF F ⊗[F] E) (M : Matrix p q (AF F ⊗[F] E)) :
    cT s (a • M) = s a • cT s M := by
  ext i k; simp [cT]

/- English proof (translation)
Establish `hd` using `congrArg Matrix.det h`. Rewrite `hd` using `[Matrix.det_mul, Matrix.det_mul]`. Establish `e : (cT s M).det = s M.det`. Rewrite using `[cT, Matrix.det_transpose]`. Conclude with `(RingHom.map_det s M).symm`.

Rewrite `hd` using `[e]`. Apply `hK.mul_right_cancel` to reduce the goal to its premises. Rewrite using `[one_mul]`. Use `nth_rewrite 2 [← hd]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem det_conj_mul_det (s : AF F ⊗[F] E →+* AF F ⊗[F] E) {k : ℕ} (M K : Matrix (Fin k) (Fin k) (AF F ⊗[F] E))
    (hK : IsUnit K.det) (h : cT s M * K * M = K) : s M.det * M.det = 1 := by
  have hd := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul] at hd
  have e : (cT s M).det = s M.det := by
    rw [cT, Matrix.det_transpose]; exact (RingHom.map_det s M).symm
  rw [e] at hd
  apply hK.mul_right_cancel
  rw [one_mul]; nth_rewrite 2 [← hd]; ring

open GlobalTheory.SphEis.UnipCrd in

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n J j m C D Z J₀ hF g l γ hC hD`. Use `set s := sigR (AF F) σ with hs`. Use `set G := (matHom _ σ J g).1 with hG`. Establish `hU : cT s G * adMat F J * G = adMat F J` using `g.2`. Establish `pres : ∀ {p q : ℕ} (X : Matrix (Fin n) (Fin p) (AF F ⊗[F] E)) (Y : Matrix (Fin n) (Fin q) (AF F ⊗[F] E)), cT s (G * X) * adMat F J * (G * Y) = cT s X * adMat F J * Y`.

Introduce `p q X Y`. Rewrite using `[Formalism.UG.cT_mul]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = _ := by rw [hU]`.

Establish `g0 : ∀ {p q : ℕ} (X : Matrix (Fin n) (Fin p) E) (Y : Matrix (Fin n) (Fin q) E), cT (σ : E →+* E) X * J * Y = 0 → cT s (adMat F X) * adMat F J * adMat F Y = 0`. Introduce `p q X Y h`. Use `gr_adMat (F := F) σ J X Y` as an intermediate fact. Rewrite `this` using `[h]`. Simplify `this` using `[gr]`.

Establish `hcd : cT s (adMat F C) * adMat F J * adMat F D = 1`. Use `gr_adMat (F := F) σ J C D` as an intermediate fact. Rewrite `this` using `[hF.cd]`. Simplify `this` using `[gr]`. Establish `hzz : cT s (adMat F Z) * adMat F J * adMat F Z = adMat F J₀`.

Use `gr_adMat (F := F) σ J Z Z` as an intermediate fact. Rewrite `this` using `[hF.zz]`. Simplify `this` using `[gr]`. Establish `hcz` using `g0 C Z hF.cz`. Establish `hdz` using `g0 D Z hF.dz`.

Establish `linv : (l : AF F ⊗[F] E) * ((l⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) = 1` using `Units.mul_inv l`. Establish `sinv : s (l : AF F ⊗[F] E) * s ((l⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) = 1` using `by rw [← map_mul, linv, map_one]`. Establish `ssl : ∀ x, s (s x) = x` using `sigR_invol σ hF.cm`. Establish `hγ : γ = s ((l⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • 1`. Establish `e` using `pres (adMat F C) (adMat F D)`.

Rewrite `e` using `[hC, hD, hcd, GlobalTheory.ResidueEisenstein.LeviConj.cT_smul', Matrix.smul_mul, Matrix.smul_mul, ← Matrix.mul_assoc, hcd, Matrix.one_mul]`. Combine the equalities or inequalities in the displayed calculation. Establish `hcgz : cT s (adMat F C) * adMat F J * (G * adMat F Z) = 0`. Establish `e` using `pres (adMat F C) (adMat F Z)`. Rewrite `e` using `[hC, hcz, GlobalTheory.ResidueEisenstein.LeviConj.cT_smul', Matrix.smul_mul, Matrix.smul_mul]`.

Combine the equalities or inequalities in the displayed calculation. Establish `cTγ : cT s γ = ((l⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • 1`. Rewrite using `[hγ, GlobalTheory.ResidueEisenstein.LeviConj.cT_smul', ssl, Formalism.UG.cT_one]`. Establish `hdgz : cT s (adMat F D) * adMat F J * (G * adMat F Z) = 0`. Establish `e` using `pres (adMat F D) (adMat F Z)`.

Rewrite `e` using `[hD, hdz, Formalism.UG.cT_mul, cTγ, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.smul_mul]`. Combine the equalities or inequalities in the displayed calculation. Establish `hsum : adMat F C * (cT s (adMat F D) * adMat F J) + adMat F Z * (adMat F J₀⁻¹ * (cT s (adMat F Z) * adMat F J)) + adMat F D * (cT s (adMat F C) * adMat F J) = 1`. Use `congrArg (fun M => adMat F M) hF.sum` as an intermediate fact. Simplify using `only [adMat, Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at this`.

Rewrite using `[cT_adMat, cT_adMat, cT_adMat]`. Simplify `this` using `only [adMat]`. Take `⟨δ₀, hδ₀⟩ : ∃ X, X = adMat F J₀⁻¹ * (cT s (adMat F Z) * adMat F J * (G * adMat F Z))` from `⟨_, rfl⟩`. Establish `hGZ : G * adMat F Z = adMat F Z * δ₀`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.add_mul, Matrix.mul_assoc]`. Simplify using `only [← Matrix.mul_assoc (cT s (adMat F D)), ← Matrix.mul_assoc (cT s (adMat F C)), ← Matrix.mul_assoc (cT s (adMat F Z))]`. Rewrite using `[hdgz, hcgz, Matrix.mul_zero, Matrix.mul_zero, zero_add, add_zero, hδ₀]`. Establish `hδu : cT s δ₀ * adMat F J₀ * δ₀ = adMat F J₀`. Establish `e` using `pres (adMat F Z) (adMat F Z)`.

Rewrite `e` using `[hGZ, hzz, Formalism.UG.cT_mul]`. Combine the equalities or inequalities in the displayed calculation. Establish `hu0 : IsUnit J₀.det` using `isUnit_iff_ne_zero.mpr hF.herm₀.2`. Establish `jj : adMat F J₀⁻¹ * adMat F J₀ = 1`. Rewrite using `[adMat, adMat, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hu0, Matrix.map_one _ (map_zero _) (map_one _)]`.

Establish `jj' : adMat F J₀ * adMat F J₀⁻¹ = 1`. Rewrite using `[adMat, adMat, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hu0, Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `hJ0 : cT s (adMat F J₀) = adMat F J₀`. Rewrite using `[cT_adMat]`. Use `congr 1`.

Use extensionality with `i k`. Simplify using `[Formalism.UG.cT, hF.herm₀.1]`. Establish `hJ0i : cT s (adMat F J₀⁻¹) = adMat F J₀⁻¹`. Rewrite using `[cT_adMat, cT_inv_herm σ J₀ hF.herm₀]`. Establish `hK : IsUnit (adMat F J₀).det`.

Rewrite using `[show (adMat F J₀).det = inclR (F := F) (AF F) J₀.det from (RingHom.map_det _ _).symm]`. Conclude with `hu0.map _`. Take `⟨δi, hδi⟩ : ∃ X, X = adMat F J₀⁻¹ * cT s δ₀ * adMat F J₀` from `⟨_, rfl⟩`. Establish `hl : δi * δ₀ = 1`. Rewrite using `[hδi, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT s δ₀), hδu, jj]`.

Establish `hr : δ₀ * δi = 1` using `mul_eq_one_comm.mp hl`. Set `δ : GL (Fin m) (AF F ⊗[F] E)` to `⟨δi, δ₀, hl, hr⟩`. Establish `hδval : δ.1 = δi` using `rfl`. Establish `hiu : cT s δi * adMat F J₀ * δi = adMat F J₀`. Combine the equalities or inequalities in the displayed calculation.

Establish `cTδi : cT s δi = adMat F J₀ * δ₀ * adMat F J₀⁻¹`. Rewrite using `[hδi, Formalism.UG.cT_mul, Formalism.UG.cT_mul, hJ0, hJ0i, cT_cT σ hF.cm, Matrix.mul_assoc]`. Establish `key : δ₀ * adMat F J₀⁻¹ = adMat F J₀⁻¹ * cT s δi`. Rewrite using `[cTδi, ← Matrix.mul_assoc, ← Matrix.mul_assoc, jj, Matrix.one_mul]`. Use `⟨δ, ?_, ?_, ?_⟩` and prove the remaining obligations.

Establish `h1` using `GlobalTheory.ResidueEisenstein.LeviConj.det_conj_mul_det s δi (adMat F J₀) hK hiu`. Establish `hu : GlobalTheory.Doubling.conjUnit σ (Matrix.GeneralLinearGroup.det δ) * Matrix.GeneralLinearGroup.det δ = 1`. Use `ext`. Use `show sigR (AF F) σ _ * _ = 1`. Conclude with `h1`.

Establish `h2` using `congrArg (absE F E) hu`. Rewrite `h2` using `[map_mul, GlobalTheory.Doubling.absE_conjUnit, map_one, ← sq]`. Conclude with `(pow_eq_one_iff_of_nonneg (by positivity) two_ne_zero).1 h2`. Rewrite using `[hδval, Matrix.mul_assoc, ← key, hδi]`. Combine the equalities or inequalities in the displayed calculation.

Introduce `u b c hu set Gi := (matHom _ σ J g⁻¹).1 with hGi`. Establish `hGiG : Gi * G = 1`. Rewrite using `[hGi, hG, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]`. Establish `iC : Gi * adMat F C = ((l⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • adMat F C`. Establish `e : adMat F C = ((l⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • (G * adMat F C)`.

Rewrite using `[hC, smul_smul, Units.inv_mul, one_smul]`. Use `conv_lhs => rw [e]`. Rewrite using `[Matrix.mul_smul, ← Matrix.mul_assoc, hGiG, Matrix.one_mul]`. Establish `iZ : Gi * adMat F Z = adMat F Z * δi`. Establish `e : adMat F Z = G * adMat F Z * δi` using `by rw [hGZ, Matrix.mul_assoc, hr, Matrix.mul_one]`.

Use `conv_lhs => rw [e]`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, hGiG, Matrix.one_mul]`. Establish `hGD : G * adMat F D = s ((l⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • adMat F D`. Rewrite using `[hD, hγ, Matrix.mul_smul, Matrix.mul_one]`. Establish `iD : Gi * adMat F D = s (l : AF F ⊗[F] E) • adMat F D`.

Establish `e : adMat F D = s (l : AF F ⊗[F] E) • (G * adMat F D)`. Rewrite using `[hGD, smul_smul, sinv, one_smul]`. Use `conv_lhs => rw [e]`. Rewrite using `[Matrix.mul_smul, ← Matrix.mul_assoc, hGiG, Matrix.one_mul]`. Establish `hplus : adMat F Z * GlobalTheory.SphEis.plus σ J₀ ((l : AF F ⊗[F] E) • (b * δi)) = s (l : AF F ⊗[F] E) • (G * (adMat F Z * GlobalTheory.SphEis.plus σ J₀ b))`.

Simplify using `only [GlobalTheory.SphEis.plus]`. Rewrite using `[GlobalTheory.ResidueEisenstein.LeviConj.cT_smul', Formalism.UG.cT_mul, ← Matrix.mul_assoc G, hGZ, Matrix.mul_smul, Matrix.mul_smul]`. Use `congr 1`. Rewrite using `[← hs, ← Matrix.mul_assoc (adMat F J₀⁻¹), ← key]`. Simplify using `only [Matrix.mul_assoc]`.

Establish `hm : (matHom _ σ J (g * u * g⁻¹)).1 = G * (matHom _ σ J u).1 * Gi`. Rewrite using `[map_mul, map_mul, Units.val_mul, Units.val_mul]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hm]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Matrix.mul_assoc, iC, Matrix.mul_smul, Matrix.mul_assoc]`. Use `_ = adMat F C := by rw [hu.onC, hC, smul_smul, Units.inv_mul, one_smul]`. Rewrite using `[hm, hδval]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_assoc, iZ, ← Matrix.mul_assoc, Matrix.mul_assoc G]`.

Use `_ = _ := by`. Rewrite using `[hu.onZ, Matrix.mul_add, ← Matrix.mul_assoc G (adMat F C), hGZ, hC, Matrix.add_mul, Matrix.mul_assoc, hr, Matrix.mul_one, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]`. Rewrite using `[hm, hδval, hplus]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_assoc, iD, Matrix.mul_smul, Matrix.mul_assoc]`.

Use `_ = s (l : AF F ⊗[F] E) • (G * adMat F D - G * (adMat F Z * GlobalTheory.SphEis.plus σ J₀ b) + G * (adMat F C * c)) := by`. Rewrite using `[hu.onD, Matrix.mul_add, Matrix.mul_sub]`. Use `_ = _ := by`. Rewrite using `[hGD, ← Matrix.mul_assoc G (adMat F C), hC]`. Simplify using `only [smul_add, smul_sub, smul_smul, sinv, one_smul, Matrix.smul_mul, Matrix.mul_smul]`.

Rewrite using `[mul_comm (s (l : AF F ⊗[F] E))]`.
-/
theorem crd_conj_scalar : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), GlobalTheory.SphEis.Fr σ J C D Z J₀ → ∀ (g : GAd σ J) (l : (AF F ⊗[F] E)ˣ) (γ : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)), (matHom _ σ J g).1 * adMat F C = (l : AF F ⊗[F] E) • adMat F C → (matHom _ σ J g).1 * adMat F D = adMat F D * γ → ∃ δ : GL (Fin m) (AF F ⊗[F] E), absE F E (Matrix.GeneralLinearGroup.det δ) = 1 ∧ δ.1 * adMat F J₀⁻¹ * cT (sigR (AF F) σ) δ.1 = adMat F J₀⁻¹ ∧ ∀ u b c, GlobalTheory.SphEis.Crd σ J C D Z J₀ u b c → GlobalTheory.SphEis.Crd σ J C D Z J₀ (g * u * g⁻¹) ((l : AF F ⊗[F] E) • (b * δ.1)) (((l : AF F ⊗[F] E) * sigR (AF F) σ (l : AF F ⊗[F] E)) • c) := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF g l γ hC hD
  set s := sigR (AF F) σ with hs
  set G := (matHom _ σ J g).1 with hG
  have hU : cT s G * adMat F J * G = adMat F J := g.2
  have pres : ∀ {p q : ℕ} (X : Matrix (Fin n) (Fin p) (AF F ⊗[F] E)) (Y : Matrix (Fin n) (Fin q) (AF F ⊗[F] E)),
      cT s (G * X) * adMat F J * (G * Y) = cT s X * adMat F J * Y := by
    intro p q X Y
    rw [Formalism.UG.cT_mul]
    calc cT s X * cT s G * adMat F J * (G * Y) = cT s X * (cT s G * adMat F J * G) * Y := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hU]
  have g0 : ∀ {p q : ℕ} (X : Matrix (Fin n) (Fin p) E) (Y : Matrix (Fin n) (Fin q) E), cT (σ : E →+* E) X * J * Y = 0 →
      cT s (adMat F X) * adMat F J * adMat F Y = 0 := by
    intro p q X Y h; have := gr_adMat (F := F) σ J X Y; rw [h] at this; simpa [gr] using this
  have hcd : cT s (adMat F C) * adMat F J * adMat F D = 1 := by
    have := gr_adMat (F := F) σ J C D; rw [hF.cd] at this; simpa [gr] using this
  have hzz : cT s (adMat F Z) * adMat F J * adMat F Z = adMat F J₀ := by
    have := gr_adMat (F := F) σ J Z Z; rw [hF.zz] at this; simpa [gr] using this
  have hcz := g0 C Z hF.cz
  have hdz := g0 D Z hF.dz
  have linv : (l : AF F ⊗[F] E) * ((l⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) = 1 := Units.mul_inv l
  have sinv : s (l : AF F ⊗[F] E) * s ((l⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) = 1 := by rw [← map_mul, linv, map_one]
  have ssl : ∀ x, s (s x) = x := sigR_invol σ hF.cm

  have hγ : γ = s ((l⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • 1 := by
    have e := pres (adMat F C) (adMat F D)
    rw [hC, hD, hcd, GlobalTheory.ResidueEisenstein.LeviConj.cT_smul', Matrix.smul_mul, Matrix.smul_mul, ← Matrix.mul_assoc, hcd,
      Matrix.one_mul] at e
    calc γ = (s ((l⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * s (l : AF F ⊗[F] E)) • γ := by rw [mul_comm, sinv, one_smul]
      _ = _ := by rw [← smul_smul, e]

  have hcgz : cT s (adMat F C) * adMat F J * (G * adMat F Z) = 0 := by
    have e := pres (adMat F C) (adMat F Z)
    rw [hC, hcz, GlobalTheory.ResidueEisenstein.LeviConj.cT_smul', Matrix.smul_mul, Matrix.smul_mul] at e
    calc _ = (s ((l⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * s (l : AF F ⊗[F] E)) •
          (cT s (adMat F C) * adMat F J * (G * adMat F Z)) := by rw [mul_comm, sinv, one_smul]
      _ = 0 := by rw [← smul_smul, e, smul_zero]
  have cTγ : cT s γ = ((l⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • 1 := by
    rw [hγ, GlobalTheory.ResidueEisenstein.LeviConj.cT_smul', ssl, Formalism.UG.cT_one]
  have hdgz : cT s (adMat F D) * adMat F J * (G * adMat F Z) = 0 := by
    have e := pres (adMat F D) (adMat F Z)
    rw [hD, hdz, Formalism.UG.cT_mul, cTγ, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.smul_mul] at e
    calc _ = ((l : AF F ⊗[F] E) * ((l⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)) •
          (cT s (adMat F D) * adMat F J * (G * adMat F Z)) := by rw [linv, one_smul]
      _ = 0 := by rw [← smul_smul, e, smul_zero]
  have hsum : adMat F C * (cT s (adMat F D) * adMat F J) + adMat F Z * (adMat F J₀⁻¹ * (cT s (adMat F Z) * adMat F J))
      + adMat F D * (cT s (adMat F C) * adMat F J) = 1 := by
    have := congrArg (fun M => adMat F M) hF.sum
    simp only [adMat, Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at this
    rw [cT_adMat, cT_adMat, cT_adMat]
    simpa only [adMat] using this
  obtain ⟨δ₀, hδ₀⟩ : ∃ X, X = adMat F J₀⁻¹ * (cT s (adMat F Z) * adMat F J * (G * adMat F Z)) := ⟨_, rfl⟩
  have hGZ : G * adMat F Z = adMat F Z * δ₀ := by
    calc G * adMat F Z = (adMat F C * (cT s (adMat F D) * adMat F J) + adMat F Z * (adMat F J₀⁻¹ * (cT s (adMat F Z) * adMat F J))
      + adMat F D * (cT s (adMat F C) * adMat F J)) * (G * adMat F Z) := by rw [hsum, Matrix.one_mul]
      _ = _ := by
        simp only [Matrix.add_mul, Matrix.mul_assoc]
        simp only [← Matrix.mul_assoc (cT s (adMat F D)), ← Matrix.mul_assoc (cT s (adMat F C)),
          ← Matrix.mul_assoc (cT s (adMat F Z))]
        rw [hdgz, hcgz, Matrix.mul_zero, Matrix.mul_zero, zero_add, add_zero, hδ₀]
  have hδu : cT s δ₀ * adMat F J₀ * δ₀ = adMat F J₀ := by
    have e := pres (adMat F Z) (adMat F Z)
    rw [hGZ, hzz, Formalism.UG.cT_mul] at e
    calc cT s δ₀ * adMat F J₀ * δ₀ = cT s δ₀ * (cT s (adMat F Z) * adMat F J * adMat F Z) * δ₀ := by rw [hzz]
      _ = _ := by rw [← e]; simp only [Matrix.mul_assoc]

  have hu0 : IsUnit J₀.det := isUnit_iff_ne_zero.mpr hF.herm₀.2
  have jj : adMat F J₀⁻¹ * adMat F J₀ = 1 := by
    rw [adMat, adMat, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hu0, Matrix.map_one _ (map_zero _) (map_one _)]
  have jj' : adMat F J₀ * adMat F J₀⁻¹ = 1 := by
    rw [adMat, adMat, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hu0, Matrix.map_one _ (map_zero _) (map_one _)]
  have hJ0 : cT s (adMat F J₀) = adMat F J₀ := by
    rw [cT_adMat]; congr 1; ext i k; simp [Formalism.UG.cT, hF.herm₀.1]
  have hJ0i : cT s (adMat F J₀⁻¹) = adMat F J₀⁻¹ := by
    rw [cT_adMat, cT_inv_herm σ J₀ hF.herm₀]
  have hK : IsUnit (adMat F J₀).det := by
    rw [show (adMat F J₀).det = inclR (F := F) (AF F) J₀.det from (RingHom.map_det _ _).symm]; exact hu0.map _
  obtain ⟨δi, hδi⟩ : ∃ X, X = adMat F J₀⁻¹ * cT s δ₀ * adMat F J₀ := ⟨_, rfl⟩
  have hl : δi * δ₀ = 1 := by
    rw [hδi, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT s δ₀), hδu, jj]
  have hr : δ₀ * δi = 1 := mul_eq_one_comm.mp hl
  let δ : GL (Fin m) (AF F ⊗[F] E) := ⟨δi, δ₀, hl, hr⟩
  have hδval : δ.1 = δi := rfl
  have hiu : cT s δi * adMat F J₀ * δi = adMat F J₀ := by
    calc cT s δi * adMat F J₀ * δi = cT s δi * (cT s δ₀ * adMat F J₀ * δ₀) * δi := by rw [hδu]
      _ = cT s (δ₀ * δi) * adMat F J₀ * (δ₀ * δi) := by rw [Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hr, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]
  have cTδi : cT s δi = adMat F J₀ * δ₀ * adMat F J₀⁻¹ := by
    rw [hδi, Formalism.UG.cT_mul, Formalism.UG.cT_mul, hJ0, hJ0i, cT_cT σ hF.cm, Matrix.mul_assoc]
  have key : δ₀ * adMat F J₀⁻¹ = adMat F J₀⁻¹ * cT s δi := by
    rw [cTδi, ← Matrix.mul_assoc, ← Matrix.mul_assoc, jj, Matrix.one_mul]
  refine ⟨δ, ?_, ?_, ?_⟩
  · have h1 := GlobalTheory.ResidueEisenstein.LeviConj.det_conj_mul_det s δi (adMat F J₀) hK hiu
    have hu : GlobalTheory.Doubling.conjUnit σ (Matrix.GeneralLinearGroup.det δ) * Matrix.GeneralLinearGroup.det δ = 1 := by
      ext
      show sigR (AF F) σ _ * _ = 1
      exact h1
    have h2 := congrArg (absE F E) hu
    rw [map_mul, GlobalTheory.Doubling.absE_conjUnit, map_one, ← sq] at h2
    exact (pow_eq_one_iff_of_nonneg (by positivity) two_ne_zero).1 h2
  · rw [hδval, Matrix.mul_assoc, ← key, hδi]
    calc adMat F J₀⁻¹ * cT s δ₀ * adMat F J₀ * (δ₀ * adMat F J₀⁻¹)
        = adMat F J₀⁻¹ * (cT s δ₀ * adMat F J₀ * δ₀) * adMat F J₀⁻¹ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hδu, jj, Matrix.one_mul]
  · intro u b c hu
    set Gi := (matHom _ σ J g⁻¹).1 with hGi
    have hGiG : Gi * G = 1 := by
      rw [hGi, hG, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
    have iC : Gi * adMat F C = ((l⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • adMat F C := by
      have e : adMat F C = ((l⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • (G * adMat F C) := by
        rw [hC, smul_smul, Units.inv_mul, one_smul]
      conv_lhs => rw [e]
      rw [Matrix.mul_smul, ← Matrix.mul_assoc, hGiG, Matrix.one_mul]
    have iZ : Gi * adMat F Z = adMat F Z * δi := by
      have e : adMat F Z = G * adMat F Z * δi := by rw [hGZ, Matrix.mul_assoc, hr, Matrix.mul_one]
      conv_lhs => rw [e]
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hGiG, Matrix.one_mul]
    have hGD : G * adMat F D = s ((l⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • adMat F D := by
      rw [hD, hγ, Matrix.mul_smul, Matrix.mul_one]
    have iD : Gi * adMat F D = s (l : AF F ⊗[F] E) • adMat F D := by
      have e : adMat F D = s (l : AF F ⊗[F] E) • (G * adMat F D) := by
        rw [hGD, smul_smul, sinv, one_smul]
      conv_lhs => rw [e]
      rw [Matrix.mul_smul, ← Matrix.mul_assoc, hGiG, Matrix.one_mul]
    have hplus : adMat F Z * GlobalTheory.SphEis.plus σ J₀ ((l : AF F ⊗[F] E) • (b * δi)) =
        s (l : AF F ⊗[F] E) • (G * (adMat F Z * GlobalTheory.SphEis.plus σ J₀ b)) := by
      simp only [GlobalTheory.SphEis.plus]
      rw [GlobalTheory.ResidueEisenstein.LeviConj.cT_smul', Formalism.UG.cT_mul, ← Matrix.mul_assoc G, hGZ, Matrix.mul_smul, Matrix.mul_smul]
      congr 1
      rw [← hs, ← Matrix.mul_assoc (adMat F J₀⁻¹), ← key]; simp only [Matrix.mul_assoc]
    have hm : (matHom _ σ J (g * u * g⁻¹)).1 = G * (matHom _ σ J u).1 * Gi := by
      rw [map_mul, map_mul, Units.val_mul, Units.val_mul]
    refine ⟨?_, ?_, ?_⟩
    · rw [hm]
      calc G * (matHom _ σ J u).1 * Gi * adMat F C
          = ((l⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • (G * ((matHom _ σ J u).1 * adMat F C)) := by
            rw [Matrix.mul_assoc, iC, Matrix.mul_smul, Matrix.mul_assoc]
        _ = adMat F C := by rw [hu.onC, hC, smul_smul, Units.inv_mul, one_smul]
    · rw [hm, hδval]
      calc G * (matHom _ σ J u).1 * Gi * adMat F Z = G * ((matHom _ σ J u).1 * adMat F Z) * δi := by
            rw [Matrix.mul_assoc, iZ, ← Matrix.mul_assoc, Matrix.mul_assoc G]
        _ = _ := by
            rw [hu.onZ, Matrix.mul_add, ← Matrix.mul_assoc G (adMat F C), hGZ, hC, Matrix.add_mul, Matrix.mul_assoc,
              hr, Matrix.mul_one, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
    · rw [hm, hδval, hplus]
      calc G * (matHom _ σ J u).1 * Gi * adMat F D
          = s (l : AF F ⊗[F] E) • (G * ((matHom _ σ J u).1 * adMat F D)) := by
            rw [Matrix.mul_assoc, iD, Matrix.mul_smul, Matrix.mul_assoc]
        _ = s (l : AF F ⊗[F] E) • (G * adMat F D - G * (adMat F Z * GlobalTheory.SphEis.plus σ J₀ b) + G * (adMat F C * c)) := by
            rw [hu.onD, Matrix.mul_add, Matrix.mul_sub]
        _ = _ := by
            rw [hGD, ← Matrix.mul_assoc G (adMat F C), hC]
            simp only [smul_add, smul_sub, smul_smul, sinv, one_smul, Matrix.smul_mul, Matrix.mul_smul]
            rw [mul_comm (s (l : AF F ⊗[F] E))]

end GlobalTheory.ResidueEisenstein.LeviConj

end
