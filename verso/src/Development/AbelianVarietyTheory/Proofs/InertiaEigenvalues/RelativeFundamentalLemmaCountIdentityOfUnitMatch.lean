import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ValIrreducible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToMatrixTwRight
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCompactIntMatrix
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralRightCosetFunEqFinsum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemRangeAlgebraMapOfStarEqStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormLeIffValuationLe
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFixedBasis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SgnLatSpanBasis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanSelfDual
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowerBasisOfCharpolySeparable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetTracePowAddMulUnitNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HermBasisOrthonormal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OrthonormalIffUnitary
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryGroupPositiveCharacterTrivialAndUnimodulaStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GeneralLinearHaarIsMulRightInvariantUnramified
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisBorderedMatrixNormalFormInvariants
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisTransferFactorKrylovDet
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualHermitianLatticeBasisExistsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocallyCompactOfComplete

open Matrix Module MeasureTheory

noncomputable section

namespace GlobalTheory.CountId

open GlobalTheory.JR GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Basic

/- English proof (translation)
Take `⟨F, nF, nE, hE, nA, st, hU, h1, h2⟩` from `GlobalTheory.UnitLemma.UQ.exists_unram K`. Use `⟨F, K.E, nF, nE, nA, st, hU, ?_⟩` and prove the remaining obligations. Establish `key : ∀ (f₁ f₂ : Field K.E), f₁ = f₂ → ∃ φ : @RingEquiv K.E K.E f₂.toMul f₁.toMul f₂.toAdd f₁.toAdd, ∀ y, φ y = y`. Introduce and unpack `f₁ f₂ rfl`. Conclude with `⟨@RingEquiv.refl K.E f₁.toMul f₁.toAdd, fun _ => rfl⟩`.

Take `⟨φ, hφ⟩` from `key nE.toField K.fE hE`. Use `⟨φ, fun y => ?_, fun y => ?_⟩` and prove the remaining obligations. Conclude with `(hφ _).trans ((h1 y).symm.trans (congrArg _ (hφ y).symm))`. Conclude with `(iff_of_eq (congrArg (fun t => nE.norm t ≤ 1) (hφ y))).trans (h2 y)`.
-/
theorem exists_normed (K : UQ) : ∃ (F E : Type) (_ : NontriviallyNormedField F) (_ : NontriviallyNormedField E)
    (_ : NormedAlgebra F E) (_ : StarRing E) (_ : Unram F E) (φ : K.E ≃+* E),
    (∀ y, φ (K.c y) = star (φ y)) ∧ ∀ y : K.E, ‖φ y‖ ≤ 1 ↔ y ∈ (algebraMap K.O K.E).range := by
  obtain ⟨F, nF, nE, hE, nA, st, hU, h1, h2⟩ := GlobalTheory.UnitLemma.UQ.exists_unram K
  refine ⟨F, K.E, nF, nE, nA, st, hU, ?_⟩
  have key : ∀ (f₁ f₂ : Field K.E), f₁ = f₂ →
      ∃ φ : @RingEquiv K.E K.E f₂.toMul f₁.toMul f₂.toAdd f₁.toAdd, ∀ y, φ y = y := by
    rintro f₁ f₂ rfl
    exact ⟨@RingEquiv.refl K.E f₁.toMul f₁.toAdd, fun _ => rfl⟩
  obtain ⟨φ, hφ⟩ := key nE.toField K.fE hE
  refine ⟨φ, fun y => ?_, fun y => ?_⟩
  · exact (hφ _).trans ((h1 y).symm.trans (congrArg _ (hφ y).symm))
  · exact (iff_of_eq (congrArg (fun t => nE.norm t ≤ 1) (hφ y))).trans (h2 y)

variable {K : UQ} (B : InvAlg K)

/- English proof (translation)
Take `⟨a, rfl⟩` from `h`. Take `⟨b, hb⟩` from `K.c_int a`. Conclude with `⟨b, hb.symm⟩`.
-/
theorem c_mem {a : K.E} (h : a ∈ (algebraMap K.O K.E).range) : K.c a ∈ (algebraMap K.O K.E).range := by
  obtain ⟨a, rfl⟩ := h
  obtain ⟨b, hb⟩ := K.c_int a
  exact ⟨b, hb.symm⟩

/- English proof (translation)
Rewrite using `[Algebra.smul_def, map_mul, B.σ_alg, ← Algebra.smul_def]`.
-/
theorem sigma_smul (a : K.E) (y : B.A) : B.σ (a • y) = K.c a • B.σ y := by
  rw [Algebra.smul_def, map_mul, B.σ_alg, ← Algebra.smul_def]

/- English proof (translation)
Establish `: B.σ y = ∑ j, K.c (e.repr y j) • e j` using `by conv_lhs => rw [← e.sum_repr y]`. Simplify using `only [map_sum, sigma_smul, he]`. Rewrite using `[this]`. Simplify using `[Finsupp.single_apply]`.
-/
theorem repr_sigma {n : ℕ} (e : Basis (Fin n) K.E B.A) (he : ∀ i, B.σ (e i) = e i) (y : B.A) (i : Fin n) :
    e.repr (B.σ y) i = K.c (e.repr y i) := by
  have : B.σ y = ∑ j, K.c (e.repr y j) • e j := by
    conv_lhs => rw [← e.sum_repr y]
    simp only [map_sum, sigma_smul, he]
  rw [this]; simp [Finsupp.single_apply]

/- English proof (translation)
Simplify using `[UQ.eta, norm_zpow]`.
-/
theorem norm_eta (a : K.E) : ‖((K.eta a : ℚ) : ℂ)‖ = 1 := by
  simp [UQ.eta, norm_zpow]

section Normed
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

def iota (F : Type) [NontriviallyNormedField F] [NormedAlgebra F E] (φ : K.E ≃+* E) : F →+* K.E :=
  φ.symm.toRingHom.comp (algebraMap F E)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem iota_apply (φ : K.E ≃+* E) (x : F) : iota F φ x = φ.symm (algebraMap F E x) := rfl

/- English proof (translation)
Rewrite using `[← hi, iota_apply, RingEquiv.apply_symm_apply, norm_algebraMap']`.
-/
theorem iota_mem {φ : K.E ≃+* E} (hi : ∀ y : K.E, ‖φ y‖ ≤ 1 ↔ y ∈ (algebraMap K.O K.E).range) (x : F) :
    iota F φ x ∈ (algebraMap K.O K.E).range ↔ ‖x‖ ≤ 1 := by
  rw [← hi, iota_apply, RingEquiv.apply_symm_apply, norm_algebraMap']

variable [Unram F E]

/- English proof (translation)
Apply `φ.injective` to reduce the goal to its premises. Rewrite using `[hs, iota_apply, RingEquiv.apply_symm_apply, Unram.star_fix]`.
-/
theorem c_iota {φ : K.E ≃+* E} (hs : ∀ y, φ (K.c y) = star (φ y)) (x : F) : K.c (iota F φ x) = iota F φ x := by
  apply φ.injective
  rw [hs, iota_apply, RingEquiv.apply_symm_apply, Unram.star_fix]

/- English proof (translation)
Take `⟨x, hx⟩` from `GlobalTheory.T.mem_range_algebraMap_of_star_eq F E (φ a) (by rw [← hs, h])`. Conclude with `⟨x, by rw [iota_apply, hx, RingEquiv.symm_apply_apply]⟩`.
-/
theorem exists_iota {φ : K.E ≃+* E} (hs : ∀ y, φ (K.c y) = star (φ y)) {a : K.E} (h : K.c a = a) :
    ∃ x : F, iota F φ x = a := by
  obtain ⟨x, hx⟩ := GlobalTheory.T.mem_range_algebraMap_of_star_eq F E (φ a) (by rw [← hs, h])
  exact ⟨x, by rw [iota_apply, hx, RingEquiv.symm_apply_apply]⟩

open Classical in

def wG (u : B.A) (L : Submodule K.O B.A) : ℂ :=
  if (∀ y ∈ L, B.g * y ∈ L) ∧ u ∈ L ∧ ∀ z ∈ L, Algebra.trace K.E B.A z ∈ (algebraMap K.O K.E).range
  then ((B.sgnLat L : ℚ) : ℂ) else 0

/- English proof (translation)
Establish `hom : omega Y = ((B.sgnLat (lat K.O e) : ℚ) : ℂ)`. Establish `h1 : omega Y = eta (Cm Y).det`. Unfold `omega eta`. Rewrite using `[(GlobalTheory.JR.transfer_factor_lemma F _).1 Y, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]`. Rewrite using `[h1, GlobalTheory.EtaCompare.eta_eq_uq_eta K F E φ hi, lat, GlobalTheory.UnitLemma.SgnBasis.sgnLat_span_basis K B e, ← iota_apply, RingHom.map_det, RingHom.mapMatrix_apply, ← Cm_mapGl, hY, Cm_Yb]`.

Simplify using `only [LinearMap.pow_mulLeft, LinearMap.mulLeft_apply]`. Establish `h1` using `lat_stable_iff K.O e (LinearMap.mulLeft K.E B.g)`. Establish `h2` using `mem_lat K.O e u`. Establish `h3` using `lat_fun_iff K.O e (Algebra.trace K.E B.A)`. Simplify using `only [mapGl, Yb, Prod.mk.injEq] at hY`.

Take `⟨y1, y2, y3, y4⟩` from `hY`. Establish `y4' : Y.2.2.2 = 0` using `(map_eq_zero _).1 y4`. Simplify using `only [← y1, Matrix.map_apply, iota_mem hi, LinearMap.mulLeft_apply] at h1`. Simplify using `only [← fun i => congrFun y2 i, iota_mem hi] at h2`. Simplify using `only [← fun i => congrFun y3 i, iota_mem hi] at h3`.

Unfold `wG unitG`. Rewrite using `[h1, h2, h3, hom]`. Simplify using `only [Set.indicator, Set.mem_setOf_eq, y4', norm_zero, zero_le_one, and_true, Pi.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem integrandG {φ : K.E ≃+* E} (hi : ∀ y : K.E, ‖φ y‖ ≤ 1 ↔ y ∈ (algebraMap K.O K.E).range) (u : B.A)
    (e : Basis (Fin (finrank K.E B.A)) K.E B.A) (Y : Gl (finrank K.E B.A) F)
    (hY : mapGl (iota F φ) Y = Yb e (LinearMap.mulLeft K.E B.g) u (Algebra.trace K.E B.A)) :
    unitG _ F Y * omega Y = wG B u (lat K.O e) := by
  have hom : omega Y = ((B.sgnLat (lat K.O e) : ℚ) : ℂ) := by
    have h1 : omega Y = eta (Cm Y).det := by
      unfold omega eta
      rw [(GlobalTheory.JR.transfer_factor_lemma F _).1 Y, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    rw [h1, GlobalTheory.EtaCompare.eta_eq_uq_eta K F E φ hi, lat, GlobalTheory.UnitLemma.SgnBasis.sgnLat_span_basis K B e, ← iota_apply, RingHom.map_det,
      RingHom.mapMatrix_apply, ← Cm_mapGl, hY, Cm_Yb]
    simp only [LinearMap.pow_mulLeft, LinearMap.mulLeft_apply]
  have h1 := lat_stable_iff K.O e (LinearMap.mulLeft K.E B.g)
  have h2 := mem_lat K.O e u
  have h3 := lat_fun_iff K.O e (Algebra.trace K.E B.A)
  simp only [mapGl, Yb, Prod.mk.injEq] at hY
  obtain ⟨y1, y2, y3, y4⟩ := hY
  have y4' : Y.2.2.2 = 0 := (map_eq_zero _).1 y4
  simp only [← y1, Matrix.map_apply, iota_mem hi, LinearMap.mulLeft_apply] at h1
  simp only [← fun i => congrFun y2 i, iota_mem hi] at h2
  simp only [← fun i => congrFun y3 i, iota_mem hi] at h3
  unfold wG unitG
  rw [h1, h2, h3, hom]
  simp only [Set.indicator, Set.mem_setOf_eq, y4', norm_zero, zero_le_one, and_true, Pi.one_apply]
  split_ifs <;> simp

/- English proof (translation)
Rewrite using `[tw_apply, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[sigma_smul, he, ← map_inv, Matrix.GeneralLinearGroup.map_apply, c_iota hs]`.
-/
theorem tw_fixed {n : ℕ} {φ : K.E ≃+* E} (hs : ∀ y, φ (K.c y) = star (φ y))
    (e : Basis (Fin n) K.E B.A) (he : ∀ i, B.σ (e i) = e i) (γ : GL (Fin n) F) (j : Fin n) :
    B.σ (tw e (Matrix.GeneralLinearGroup.map (iota F φ) γ) j) =
      tw e (Matrix.GeneralLinearGroup.map (iota F φ) γ) j := by
  rw [tw_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sigma_smul, he, ← map_inv, Matrix.GeneralLinearGroup.map_apply, c_iota hs]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨γ, rfl⟩`. Use `⟨⟨lat_fg _ _, span_lat _ _⟩, fun y hy => ?_⟩` and prove the remaining obligations. Establish `hf` using `tw_fixed B hs e he γ`. Rewrite `hy`, the goal using `[mem_lat]`.

Introduce `i`. Rewrite using `[repr_sigma B _ hf]`. Conclude with `c_mem (hy i)`. Introduce and unpack `⟨hL, hσ⟩`. Take `⟨e', h1, h2⟩` from `GlobalTheory.GaloisDescentLattice.exists_fixed_basis K B L hL hσ`.

Take `⟨γ, rfl⟩` from `exists_tw e e'`. Establish `a1 : ∀ i j, ∃ x : F, iota F φ x = γ.val i j` using `fun i j => by`. Use `exists_iota hs ?_` and prove the remaining obligations. Rewrite using `[← toMatrix_tw_left e γ, Basis.toMatrix_apply, ← repr_sigma B _ h2, he]`. Establish `a2 : ∀ i j, ∃ x : F, iota F φ x = (γ⁻¹).val i j` using `fun i j => by`.

Use `exists_iota hs ?_` and prove the remaining obligations. Rewrite using `[← toMatrix_tw_right e γ, Basis.toMatrix_apply, ← repr_sigma B _ he, h2]`. Use `choose P hP using a1`. Use `choose Q hQ using a2`. Establish `hP' : (Matrix.of P).map (iota F φ) = γ.val` using `by ext i j; exact hP i j`.

Establish `hQ' : (Matrix.of Q).map (iota F φ) = (γ⁻¹).val` using `by ext i j; exact hQ i j`. Establish `hinj : Function.Injective fun A : Matrix (Fin (finrank K.E B.A)) (Fin (finrank K.E B.A)) F => A.map (iota F φ)` using `Matrix.map_injective (iota F φ).injective`. Set `δ : GL (Fin (finrank K.E B.A)) F` to `⟨Matrix.of P, Matrix.of Q, hinj (by simp only [Matrix.map_mul, hP', hQ']; simp), hinj (by simp only [Matrix.map_mul, hP', hQ']; simp)⟩`. Establish `hδ : Matrix.GeneralLinearGroup.map (iota F φ) δ = γ` using `Units.ext hP'`. Conclude with `⟨δ, by simp only [hδ]; exact h1⟩`.
-/
theorem range_piG {φ : K.E ≃+* E} (hs : ∀ y, φ (K.c y) = star (φ y))
    (e : Basis (Fin (finrank K.E B.A)) K.E B.A) (he : ∀ i, B.σ (e i) = e i) (L : Submodule K.O B.A) :
    L ∈ Set.range (fun γ : GL (Fin (finrank K.E B.A)) F =>
      lat K.O (tw e (Matrix.GeneralLinearGroup.map (iota F φ) γ))) ↔ IsLat K.O K.E L ∧ ∀ y ∈ L, B.σ y ∈ L := by
  constructor
  · rintro ⟨γ, rfl⟩
    refine ⟨⟨lat_fg _ _, span_lat _ _⟩, fun y hy => ?_⟩
    have hf := tw_fixed B hs e he γ
    rw [mem_lat] at hy ⊢
    intro i
    rw [repr_sigma B _ hf]
    exact c_mem (hy i)
  · rintro ⟨hL, hσ⟩
    obtain ⟨e', h1, h2⟩ := GlobalTheory.GaloisDescentLattice.exists_fixed_basis K B L hL hσ
    obtain ⟨γ, rfl⟩ := exists_tw e e'
    have a1 : ∀ i j, ∃ x : F, iota F φ x = γ.val i j := fun i j => by
      refine exists_iota hs ?_
      rw [← toMatrix_tw_left e γ, Basis.toMatrix_apply, ← repr_sigma B _ h2, he]
    have a2 : ∀ i j, ∃ x : F, iota F φ x = (γ⁻¹).val i j := fun i j => by
      refine exists_iota hs ?_
      rw [← toMatrix_tw_right e γ, Basis.toMatrix_apply, ← repr_sigma B _ he, h2]
    choose P hP using a1
    choose Q hQ using a2
    have hP' : (Matrix.of P).map (iota F φ) = γ.val := by ext i j; exact hP i j
    have hQ' : (Matrix.of Q).map (iota F φ) = (γ⁻¹).val := by ext i j; exact hQ i j
    have hinj : Function.Injective fun A : Matrix (Fin (finrank K.E B.A)) (Fin (finrank K.E B.A)) F =>
      A.map (iota F φ) := Matrix.map_injective (iota F φ).injective
    let δ : GL (Fin (finrank K.E B.A)) F := ⟨Matrix.of P, Matrix.of Q,
      hinj (by simp only [Matrix.map_mul, hP', hQ']; simp), hinj (by simp only [Matrix.map_mul, hP', hQ']; simp)⟩
    have hδ : Matrix.GeneralLinearGroup.map (iota F φ) δ = γ := Units.ext hP'
    exact ⟨δ, by simp only [hδ]; exact h1⟩

/- English proof (translation)
Use `letI := M.mG`. Use `haveI := M.bG`. Use `haveI := GlobalTheory.JR.gl_unimodular F E _ M`. Use `haveI : IsUltrametricDist F := Unram.ultraF E`. Establish `h` using `GlobalTheory.integral_rightCoset_fun_eq_finsum (GL (Fin (finrank K.E B.A)) F) (Submodule K.O B.A) M.μG (glO _ F) (MeasExist.isOpen_glO _ F) M.volG (fun γ => lat K.O (tw e (Matrix.GeneralLinearGroup.map (iota F φ) γ))) (fun g g' => by`.

Rewrite using `[lat_tw_eq_iff, ← map_inv, ← map_mul, ← map_inv]`. Simplify using `only [Matrix.GeneralLinearGroup.map_apply, iota_mem hi]`. Use the proof step `rfl)`. Use the proof step `(wG B u) (fun l => by`. Unfold `wG`.

Use `split_ifs`. Conclude with `Or.inr (norm_eta _)`. Conclude with `Or.inl rfl)`. Unfold `orbG`. Rewrite using `[show (fun g => unitG _ F (act g Y) * omega (act g Y)) = fun γ => wG B u (lat K.O (tw e (Matrix.GeneralLinearGroup.map (iota F φ) γ))) from`.

Use function extensionality and compare the values at `fun γ => integrandG B hi u _ _ (by rw [mapGl_act, hY, Yb_tw]), h, InvAlg.GG]`. Use `Eq.trans ?_ ((Rat.castHom ℂ).toAddMonoidHom.map_finsum_of_injective Rat.cast_injective _).symm` and prove the remaining obligations. Use `finsum_congr fun L => ?_` and prove the remaining obligations. Simplify using `only [range_piG B hs e he L, finsum_eq_if, wG, InvAlg.Lin, Set.mem_setOf_eq]`. Apply the tactic sequence `split_ifs <;> simp_all`.
-/
theorem orbG_eq {φ : K.E ≃+* E} (hs : ∀ y, φ (K.c y) = star (φ y))
    (hi : ∀ y : K.E, ‖φ y‖ ≤ 1 ↔ y ∈ (algebraMap K.O K.E).range) (M : Meas (finrank K.E B.A) F E) (u : B.A)
    (e : Basis (Fin (finrank K.E B.A)) K.E B.A) (he : ∀ i, B.σ (e i) = e i) (Y : Gl (finrank K.E B.A) F)
    (hY : mapGl (iota F φ) Y = Yb e (LinearMap.mulLeft K.E B.g) u (Algebra.trace K.E B.A)) :
    orbG M (unitG _ F) Y = ((B.GG u : ℚ) : ℂ) := by
  classical
  letI := M.mG
  haveI := M.bG
  haveI := GlobalTheory.JR.gl_unimodular F E _ M
  haveI : IsUltrametricDist F := Unram.ultraF E
  have h := GlobalTheory.integral_rightCoset_fun_eq_finsum (GL (Fin (finrank K.E B.A)) F) (Submodule K.O B.A) M.μG (glO _ F)
    (MeasExist.isOpen_glO _ F) M.volG
    (fun γ => lat K.O (tw e (Matrix.GeneralLinearGroup.map (iota F φ) γ)))
    (fun g g' => by
      rw [lat_tw_eq_iff, ← map_inv, ← map_mul, ← map_inv]
      simp only [Matrix.GeneralLinearGroup.map_apply, iota_mem hi]
      rfl)
    (wG B u) (fun l => by
      unfold wG
      split_ifs
      · exact Or.inr (norm_eta _)
      · exact Or.inl rfl)
  unfold orbG
  rw [show (fun g => unitG _ F (act g Y) * omega (act g Y)) = fun γ => wG B u
      (lat K.O (tw e (Matrix.GeneralLinearGroup.map (iota F φ) γ))) from
    funext fun γ => integrandG B hi u _ _ (by rw [mapGl_act, hY, Yb_tw]), h, InvAlg.GG]
  refine Eq.trans ?_ ((Rat.castHom ℂ).toAddMonoidHom.map_finsum_of_injective Rat.cast_injective _).symm
  refine finsum_congr fun L => ?_
  simp only [range_piG B hs e he L, finsum_eq_if, wG, InvAlg.Lin, Set.mem_setOf_eq]
  split_ifs <;> simp_all

def toGLU {n : ℕ} (φ : K.E ≃+* E) : Matrix.unitaryGroup (Fin n) E →* GL (Fin n) K.E :=
  (Matrix.GeneralLinearGroup.map φ.symm.toRingHom).comp Unitary.toUnits

omit [Unram F E] in
/- English proof (translation)
Unfold `actU Hn.toGl act`. Use `Prod.ext rfl (Prod.ext rfl (Prod.ext ?_ rfl))` and prove the remaining obligations. Conclude with `Matrix.star_mulVec γ.1 X.2.1`.
-/
theorem toGl_actU {n : ℕ} (γ : Matrix.unitaryGroup (Fin n) E) (X : Hn n F E) :
    (actU γ X).toGl = act (Unitary.toUnits γ) X.toGl := by
  unfold actU Hn.toGl act
  refine Prod.ext rfl (Prod.ext rfl (Prod.ext ?_ rfl))
  exact Matrix.star_mulVec γ.1 X.2.1

/- English proof (translation)
Establish `h1 : star (P.map φ) = ((P.map K.c)ᵀ).map φ`. Use extensionality with `i j`. Simplify using `[hs]`. Rewrite using `[h1, ← Matrix.map_mul, ← Matrix.map_one φ (map_zero φ) (map_one φ)]`. Conclude with `(Matrix.map_injective φ.injective).eq_iff.symm`.
-/
theorem unit_iff {n : ℕ} {φ : K.E ≃+* E} (hs : ∀ y, φ (K.c y) = star (φ y)) (P : Matrix (Fin n) (Fin n) K.E) :
    (P.map K.c)ᵀ * P = 1 ↔ star (P.map φ) * P.map φ = 1 := by
  have h1 : star (P.map φ) = ((P.map K.c)ᵀ).map φ := by
    ext i j; simp [hs]
  rw [h1, ← Matrix.map_mul, ← Matrix.map_one φ (map_zero φ) (map_one φ)]
  exact (Matrix.map_injective φ.injective).eq_iff.symm

open Classical in

def wU (w : B.A) (L : Submodule K.O B.A) : ℂ :=
  if (∀ y ∈ L, B.g * y ∈ L) ∧ w ∈ L then 1 else 0

omit [Unram F E] in
/- English proof (translation)
Establish `h1` using `lat_stable_iff K.O e (LinearMap.mulLeft K.E B.g)`. Establish `h2` using `mem_lat K.O e w`. Simplify using `only [mapGl, Yb, Hn.toGl, Prod.mk.injEq] at hX`. Take `⟨y1, y2, -, y4⟩` from `hX`. Establish `y4' : X.2.2 = 0` using `(map_eq_zero _).1 ((map_eq_zero _).1 y4)`.

Simplify using `only [← y1, Matrix.map_apply, ← hi, LinearMap.mulLeft_apply] at h1`. Simplify using `only [← fun i => congrFun y2 i, ← hi] at h2`. Simplify using `only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.apply_symm_apply] at h1 h2`. Unfold `wU unitU`. Rewrite using `[h1, h2]`.

Simplify using `only [Set.indicator, Set.mem_setOf_eq, y4', norm_zero, zero_le_one, and_true, Pi.one_apply]`. Apply the tactic sequence `split_ifs <;> rfl`.
-/
theorem integrandU {n : ℕ} {φ : K.E ≃+* E} (hi : ∀ y : K.E, ‖φ y‖ ≤ 1 ↔ y ∈ (algebraMap K.O K.E).range) (w : B.A)
    (l : B.A →ₗ[K.E] K.E) (e : Basis (Fin n) K.E B.A) (X : Hn n F E)
    (hX : mapGl φ.symm.toRingHom X.toGl = Yb e (LinearMap.mulLeft K.E B.g) w l) :
    unitU n F E X = wU B w (lat K.O e) := by
  have h1 := lat_stable_iff K.O e (LinearMap.mulLeft K.E B.g)
  have h2 := mem_lat K.O e w
  simp only [mapGl, Yb, Hn.toGl, Prod.mk.injEq] at hX
  obtain ⟨y1, y2, -, y4⟩ := hX
  have y4' : X.2.2 = 0 := (map_eq_zero _).1 ((map_eq_zero _).1 y4)
  simp only [← y1, Matrix.map_apply, ← hi, LinearMap.mulLeft_apply] at h1
  simp only [← fun i => congrFun y2 i, ← hi] at h2
  simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.apply_symm_apply] at h1 h2
  unfold wU unitU
  rw [h1, h2]
  simp only [Set.indicator, Set.mem_setOf_eq, y4', norm_zero, zero_le_one, and_true, Pi.one_apply]
  split_ifs <;> rfl

/- English proof (translation)
Simplify using `[InvAlg.herm, mul_add, add_mul]`.
-/
theorem herm_add_left (x a b c : B.A) : B.herm x (a + b) c = B.herm x a c + B.herm x b c := by
  simp [InvAlg.herm, mul_add, add_mul]

/- English proof (translation)
The claim follows from `GlobalTheory.T.self_dual_hermitian_lattice_basis_exists K B.A (B.herm x) (herm_add_left B x) (fun c y z => herm_smul_left B x y z c) (herm_symm B x hx) L hL.1 hL.2 hd`.
-/
theorem exists_orth {x : B.A} (hx : B.σ x = x) (L : Submodule K.O B.A) (hL : IsLat K.O K.E L)
    (hd : ∀ y, y ∈ L ↔ ∀ z ∈ L, B.herm x y z ∈ (algebraMap K.O K.E).range) :
    ∃ b : Basis (Fin (finrank K.E B.A)) K.E B.A, lat K.O b = L ∧
      ∀ i j, B.herm x (b i) (b j) = if i = j then 1 else 0 :=
  GlobalTheory.T.self_dual_hermitian_lattice_basis_exists K B.A (B.herm x) (herm_add_left B x) (fun c y z => herm_smul_left B x y z c)
    (herm_symm B x hx) L hL.1 hL.2 hd

/- English proof (translation)
Establish `hm : ∀ γ : Matrix.unitaryGroup (Fin (finrank K.E B.A)) E, (toGLU φ γ).val.map φ = γ.1`. Introduce `γ`. Use extensionality with `i j`. Conclude with `φ.apply_symm_apply _`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨γ, rfl⟩`. Use `⟨⟨lat_fg _ _, span_lat _ _⟩, GlobalTheory.UnitLemma.OrthoSelfDual.span_selfDual K B x _ _ ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.UnitLemma.BaseChange.orthonormal_iff_unitary K B x _ e _ he, toMatrix_tw_right, unit_iff hs, ← map_inv, hm]`. Conclude with `(γ⁻¹).2.1`. Introduce and unpack `⟨hL, hd⟩`.

Take `⟨b, h1, h2⟩` from `exists_orth B hx L hL hd`. Take `⟨γ, rfl⟩` from `exists_tw e b`. Rewrite `h2` using `[GlobalTheory.UnitLemma.BaseChange.orthonormal_iff_unitary K B x _ e _ he, toMatrix_tw_right, unit_iff hs]`. Use `⟨(⟨_, Matrix.mem_unitaryGroup_iff'.2 h2⟩ : Matrix.unitaryGroup _ E)⁻¹, ?_⟩` and prove the remaining obligations. Simplify using `only`.

Rewrite using `[← h1, map_inv]`. Use `congr 2`. Rewrite using `[inv_eq_iff_eq_inv]`. Use extensionality with `i j`. Conclude with `φ.symm_apply_apply _`.
-/
theorem range_piU {φ : K.E ≃+* E} (hs : ∀ y, φ (K.c y) = star (φ y)) {x : B.A} (hx : B.σ x = x)
    (e : Basis (Fin (finrank K.E B.A)) K.E B.A) (he : ∀ i j, B.herm x (e i) (e j) = if i = j then 1 else 0)
    (L : Submodule K.O B.A) :
    L ∈ Set.range (fun γ : Matrix.unitaryGroup (Fin (finrank K.E B.A)) E => lat K.O (tw e (toGLU φ γ))) ↔
      IsLat K.O K.E L ∧ ∀ y, y ∈ L ↔ ∀ z ∈ L, B.herm x y z ∈ (algebraMap K.O K.E).range := by
  have hm : ∀ γ : Matrix.unitaryGroup (Fin (finrank K.E B.A)) E, (toGLU φ γ).val.map φ = γ.1 := by
    intro γ; ext i j; exact φ.apply_symm_apply _
  constructor
  · rintro ⟨γ, rfl⟩
    refine ⟨⟨lat_fg _ _, span_lat _ _⟩, GlobalTheory.UnitLemma.OrthoSelfDual.span_selfDual K B x _ _ ?_⟩
    rw [GlobalTheory.UnitLemma.BaseChange.orthonormal_iff_unitary K B x _ e _ he, toMatrix_tw_right, unit_iff hs, ← map_inv, hm]
    exact (γ⁻¹).2.1
  · rintro ⟨hL, hd⟩
    obtain ⟨b, h1, h2⟩ := exists_orth B hx L hL hd
    obtain ⟨γ, rfl⟩ := exists_tw e b
    rw [GlobalTheory.UnitLemma.BaseChange.orthonormal_iff_unitary K B x _ e _ he, toMatrix_tw_right, unit_iff hs] at h2
    refine ⟨(⟨_, Matrix.mem_unitaryGroup_iff'.2 h2⟩ : Matrix.unitaryGroup _ E)⁻¹, ?_⟩
    simp only
    rw [← h1, map_inv]
    congr 2
    rw [inv_eq_iff_eq_inv]
    ext i j
    exact φ.symm_apply_apply _

/- English proof (translation)
Use `letI := M.mU`. Use `haveI := M.bU`. Use `haveI := (GlobalTheory.T.unitaryGroup_positiveCharacter_trivial_and_unimodular F E _).2 M`. Use `haveI : IsUltrametricDist E := Unram.ultraE F`. Establish `hm : ∀ (γ : Matrix.unitaryGroup (Fin (finrank K.E B.A)) E) i j, φ ((toGLU φ γ).val i j) = γ.1 i j` using `fun γ i j => φ.apply_symm_apply _`.

Establish `h` using `GlobalTheory.integral_rightCoset_fun_eq_finsum (Matrix.unitaryGroup (Fin (finrank K.E B.A)) E) (Submodule K.O B.A) M.μU (uO _ E) (MeasExist.isOpen_uO _ E) M.volU (fun γ => lat K.O (tw e (toGLU φ γ))) (fun g g' => by`. Rewrite using `[lat_tw_eq_iff, ← map_inv, ← map_mul, ← map_inv]`. Simplify using `only [← hi, hm]`. Use `⟨fun H i j => (H i j).1, fun H i j => ⟨H i j, ?_⟩⟩` and prove the remaining obligations. Conclude with `(Unram.norm_star (F := F) _).trans_le (H j i))`.

Use the proof step `(wU B w) (fun l => by`. Unfold `wU`. Use `split_ifs`. Conclude with `Or.inr norm_one`. Conclude with `Or.inl rfl)`.

Unfold `orbU`. Rewrite using `[show (fun g => unitU _ F E (actU g X)) = fun γ => wU B w (lat K.O (tw e (toGLU φ γ))) from`. Use function extensionality and compare the values at `fun γ => integrandU B hi w l _ _ (by rw [toGl_actU, mapGl_act, hX, Yb_tw]; rfl), h]`. Establish `hc : B.UU x w = ∑ᶠ L ∈ {L | L ∈ B.X x ∧ w ∈ L}, 1`. Rewrite using `[finsum_one, InvAlg.UU, ← Nat.card_coe_set_eq]`.

Conclude with `Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ B.X x) (w ∈ ·))`. Rewrite using `[hc]`. Use `Eq.trans ?_ ((Nat.castAddMonoidHom ℂ).map_finsum_of_injective Nat.cast_injective _).symm` and prove the remaining obligations. Use `finsum_congr fun L => ?_` and prove the remaining obligations. Simplify using `only [range_piU B hs hx e he L, finsum_eq_if, wU, InvAlg.X, Set.mem_setOf_eq]`.

Use `split_ifs with h1 h2 h3 h4 h5`. Simplify using the standard rewrite rules. Conclude with `absurd ⟨⟨h1.1, h2.1, h1.2⟩, h2.2⟩ h3`. Conclude with `absurd ⟨h4.1.2.1, h4.2⟩ h2`. Simplify using the standard rewrite rules.

Conclude with `absurd ⟨h5.1.1, h5.1.2.2⟩ h1`. Simplify using the standard rewrite rules.
-/
theorem orbU_eq {φ : K.E ≃+* E} (hs : ∀ y, φ (K.c y) = star (φ y))
    (hi : ∀ y : K.E, ‖φ y‖ ≤ 1 ↔ y ∈ (algebraMap K.O K.E).range) (M : Meas (finrank K.E B.A) F E)
    {x : B.A} (hx : B.σ x = x) (w : B.A) (l : B.A →ₗ[K.E] K.E)
    (e : Basis (Fin (finrank K.E B.A)) K.E B.A) (he : ∀ i j, B.herm x (e i) (e j) = if i = j then 1 else 0)
    (X : Hn (finrank K.E B.A) F E)
    (hX : mapGl φ.symm.toRingHom X.toGl = Yb e (LinearMap.mulLeft K.E B.g) w l) :
    orbU M (unitU _ F E) X = (B.UU x w : ℂ) := by
  classical
  letI := M.mU
  haveI := M.bU
  haveI := (GlobalTheory.T.unitaryGroup_positiveCharacter_trivial_and_unimodular F E _).2 M
  haveI : IsUltrametricDist E := Unram.ultraE F
  have hm : ∀ (γ : Matrix.unitaryGroup (Fin (finrank K.E B.A)) E) i j, φ ((toGLU φ γ).val i j) = γ.1 i j :=
    fun γ i j => φ.apply_symm_apply _
  have h := GlobalTheory.integral_rightCoset_fun_eq_finsum (Matrix.unitaryGroup (Fin (finrank K.E B.A)) E) (Submodule K.O B.A) M.μU (uO _ E)
    (MeasExist.isOpen_uO _ E) M.volU
    (fun γ => lat K.O (tw e (toGLU φ γ)))
    (fun g g' => by
      rw [lat_tw_eq_iff, ← map_inv, ← map_mul, ← map_inv]
      simp only [← hi, hm]
      refine ⟨fun H i j => (H i j).1, fun H i j => ⟨H i j, ?_⟩⟩
      exact (Unram.norm_star (F := F) _).trans_le (H j i))
    (wU B w) (fun l => by
      unfold wU
      split_ifs
      · exact Or.inr norm_one
      · exact Or.inl rfl)
  unfold orbU
  rw [show (fun g => unitU _ F E (actU g X)) = fun γ => wU B w (lat K.O (tw e (toGLU φ γ))) from
    funext fun γ => integrandU B hi w l _ _ (by rw [toGl_actU, mapGl_act, hX, Yb_tw]; rfl), h]
  have hc : B.UU x w = ∑ᶠ L ∈ {L | L ∈ B.X x ∧ w ∈ L}, 1 := by
    rw [finsum_one, InvAlg.UU, ← Nat.card_coe_set_eq]
    exact Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ B.X x) (w ∈ ·))
  rw [hc]
  refine Eq.trans ?_ ((Nat.castAddMonoidHom ℂ).map_finsum_of_injective Nat.cast_injective _).symm
  refine finsum_congr fun L => ?_
  simp only [range_piU B hs hx e he L, finsum_eq_if, wU, InvAlg.X, Set.mem_setOf_eq]
  split_ifs with h1 h2 h3 h4 h5
  · simp
  · exact absurd ⟨⟨h1.1, h2.1, h1.2⟩, h2.2⟩ h3
  · exact absurd ⟨h4.1.2.1, h4.2⟩ h2
  · simp
  · exact absurd ⟨h5.1.1, h5.1.2.2⟩ h1
  · simp

end Normed

/- English proof (translation)
Establish `: ∀ z, B.herm x z (b i) = (Algebra.trace K.E B.A ∘ₗ LinearMap.mulLeft K.E (x * B.σ (b i))) z`. Introduce `z`. Simplify using `only [InvAlg.herm, LinearMap.comp_apply, LinearMap.mulLeft_apply]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Establish `h2 : ∀ j, (Algebra.trace K.E B.A ∘ₗ LinearMap.mulLeft K.E (x * B.σ (b i))) (b j) = if j = i then 1 else 0` using `fun j => by rw [← this, hb]`. Rewrite using `[this]`. Use `conv_rhs => rw [← b.sum_repr y, map_sum]`. Simplify using `only [map_smul, h2]`. Simplify using the standard rewrite rules.
-/
theorem repr_orth {n : ℕ} {x : B.A} (b : Basis (Fin n) K.E B.A)
    (hb : ∀ i j, B.herm x (b i) (b j) = if i = j then 1 else 0) (y : B.A) (i : Fin n) :
    b.repr y i = B.herm x y (b i) := by
  have : ∀ z, B.herm x z (b i) = (Algebra.trace K.E B.A ∘ₗ LinearMap.mulLeft K.E (x * B.σ (b i))) z := by
    intro z; simp only [InvAlg.herm, LinearMap.comp_apply, LinearMap.mulLeft_apply]; congr 1; ring
  have h2 : ∀ j, (Algebra.trace K.E B.A ∘ₗ LinearMap.mulLeft K.E (x * B.σ (b i))) (b j) = if j = i then 1 else 0 :=
    fun j => by rw [← this, hb]
  rw [this]
  conv_rhs => rw [← b.sum_repr y, map_sum]
  simp only [map_smul, h2]
  simp

/- English proof (translation)
Rewrite using `[(GlobalTheory.JR.normalForm_invariants k n).2.2.1 Y]`. Both sides reduce to the same expression.
-/
theorem Delta_inv {n : ℕ} {k : Type} [Field k] (Y : Gl n k) : Delta (JR.inv Y) = (Cm Y * Bm Y).det := by
  rw [(GlobalTheory.JR.normalForm_invariants k n).2.2.1 Y]; rfl

/- English proof (translation)
Introduce `K B hreg x w hx hw`. Take `⟨F, E, _, _, _, _, _, φ, hs, hi⟩` from `exists_normed K`. Take `⟨M⟩` from `MeasExist.nonempty_meas (finrank K.E B.A) F E`. Take `⟨e, he⟩` from `GlobalTheory.UnitLemma.exists_basis_pow_of_separable K B hreg.2`. Establish `heσ : ∀ i, B.σ (e i) = e i` using `fun i => by rw [he, map_pow, hreg.1]`.

Establish `hspan : Submodule.span K.E (Set.range fun l : ℕ => B.g ^ l) = ⊤`. Rewrite using `[eq_top_iff, ← e.span_eq]`. Use `Submodule.span_mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `⟨i, (he i).symm⟩`.

Use `set u := x * (w * B.σ w) with hu`. Establish `huσ : B.σ u = u` using `by rw [hu, map_mul, map_mul, hx.2, B.σ_σ, mul_comm w]`. Establish `huu : IsUnit u` using `hx.1.mul (hw.mul (hw.map B.σ))`. Use `set T := LinearMap.mulLeft K.E B.g with hT`. Use `set lw : B.A →ₗ[K.E] K.E := Algebra.trace K.E B.A ∘ₗ LinearMap.mulLeft K.E (x * B.σ w) with hlw`.

Establish `hlw' : ∀ y, lw y = B.herm x y w`. Introduce `y`. Simplify using `only [hlw, InvAlg.herm, LinearMap.comp_apply, LinearMap.mulLeft_apply]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Choose the witnesses or unpack the hypotheses as in `⟨Y, hY⟩ : ∃ Y : Gl (finrank K.E B.A) F, mapGl (iota F φ) Y = Yb e T u (Algebra.trace K.E B.A) := by`. Establish `a1 : ∀ i j, ∃ t : F, iota F φ t = LinearMap.toMatrix e e T i j` using `fun i j => by`. Use `exists_iota hs ?_` and prove the remaining obligations. Rewrite using `[LinearMap.toMatrix_apply, ← repr_sigma B e heσ, hT, LinearMap.mulLeft_apply, map_mul, hreg.1, heσ]`. Establish `a2 : ∀ i, ∃ t : F, iota F φ t = e.repr u i` using `fun i => by`.

Use `exists_iota hs ?_` and prove the remaining obligations. Rewrite using `[← repr_sigma B e heσ, huσ]`. Establish `a3 : ∀ i, ∃ t : F, iota F φ t = Algebra.trace K.E B.A (e i)` using `fun i => by`. Use `exists_iota hs ?_` and prove the remaining obligations. Rewrite using `[← trace_sigma, heσ]`.

Use `choose P hP using a1`. Use `choose b hb using a2`. Use `choose c hc using a3`. Conclude with `⟨(Matrix.of P, b, c, 0), Prod.ext (Matrix.ext hP) (Prod.ext (funext hb) (Prod.ext (funext hc) (map_zero _)))⟩`. Establish `hinv : ∀ b : Basis (Fin (finrank K.E B.A)) K.E B.A, JR.inv (Yb b T w lw) = (JR.inv Y).map (iota F φ)`.

Introduce `b`. Rewrite using `[← inv_mapGl, hY, inv_Yb, inv_Yb]`. Use `Prod.ext rfl (Prod.ext (funext fun i => ?_) rfl)` and prove the remaining obligations. Simplify using `only [hlw, hT, hu, LinearMap.pow_mulLeft, LinearMap.comp_apply, LinearMap.mulLeft_apply]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Establish `hΔE : Delta ((JR.inv Y).map (iota F φ)) ≠ 0`. Rewrite using `[← inv_mapGl, hY, Delta_inv, Cm_mul_Bm]`. Simplify using `only [mom_Yb, hT, LinearMap.pow_mulLeft, LinearMap.mulLeft_apply]`. Conclude with `GlobalTheory.T.det_trace_pow_add_mul_unit_ne_zero K B hreg.2 u huu`.

Establish `hΔ : Delta (JR.inv Y) ≠ 0`. Introduce `h0`. Apply `hΔE` to reduce the goal to its premises. Rewrite using `[← inv_mapGl, Delta_inv, Cm_mapGl, Bm_mapGl, ← Matrix.map_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← Delta_inv, h0, map_zero]`. Establish `hG : orbG M (unitG _ F) (sec (JR.inv Y)) = ((B.GG u : ℚ) : ℂ)`.

Take `⟨γ, ⟨hγ, -⟩, -⟩` from `(GlobalTheory.JR.normalForm_invariants F _).2.2.2.2 Y (sec (JR.inv Y)) hΔ ((GlobalTheory.JR.normalForm_invariants F _).2.1 _)`. Conclude with `orbG_eq B hs hi M u _ (tw_fixed B hs e heσ γ) _ (by rw [← hγ, mapGl_act, hY, Yb_tw])`. Take `⟨m1, m2⟩` from `hUM _ F E M (JR.inv Y) hΔ`. Rewrite `m2` using `[hG]`. Distinguish the cases in `hex : ∃ X : Hn (finrank K.E B.A) F E, HasInv X (JR.inv Y)`.

Take `⟨X, hX⟩` from `hex`. Establish `h1 : JR.inv (mapGl φ.symm.toRingHom X.toGl) = JR.inv (Yb e T w lw)`. Rewrite using `[inv_mapGl, hX, hinv]`. Both sides reduce to the same expression. Take `⟨γ, ⟨hγ, -⟩, -⟩` from `(GlobalTheory.JR.normalForm_invariants K.E _).2.2.2.2 _ _ (by rw [hinv]; exact hΔE) h1`.

Rewrite `hγ` using `[← Yb_tw]`. Establish `hγ'` using `hγ`. Simplify using `only [mapGl, Yb, Hn.toGl, Prod.mk.injEq] at hγ'`. Take `⟨y1, y2, y3, -⟩` from `hγ'`. Establish `hcs : ∀ t : E, K.c (φ.symm t) = φ.symm (star t)` using `fun t => by`.

Apply `φ.injective` to reduce the goal to its premises. Rewrite using `[hs]`. Simplify using the standard rewrite rules. Establish `horth` using `GlobalTheory.UnitLemma.herm_basis_orthonormal K B x w hreg.1 hw hspan _ (tw e γ) (fun i j => by`. Establish `e1` using `congrFun (congrFun y1 i) j`.

Establish `e2` using `congrFun (congrFun y1 j) i`. Rewrite `e1`, `e2` using `[LinearMap.toMatrix_apply, hT, LinearMap.mulLeft_apply]`. Rewrite using `[e1, e2]`. Conclude with `(hcs _).trans (congrArg φ.symm (congrFun (congrFun X.1.2 j) i))) (fun j => by`. Rewrite using `[← hlw', congrFun y3 j, congrFun y2 j]`.

Conclude with `(hcs _).symm)`. Establish `h2` using `m1 X hX`. Rewrite `h2` using `[hG, orbU_eq B hs hi M hx.2 w lw _ horth X hγ.symm]`. Conclude with `h2` after adjusting the coercions. Establish `h0 : B.GG u = 0` using `by exact_mod_cast m2 hex`.

Rewrite using `[h0]`. Assume the negation of the conclusion as `hne`. Establish `hne' : B.UU x w ≠ 0` using `fun h => hne (by rw [h]; rfl)`. Take `⟨⟨⟨L, hL⟩, -⟩⟩` from `(Nat.card_ne_zero.1 hne').1`. Take `⟨b, -, hb⟩` from `exists_orth B hx.2 L hL.1 hL.2.2`.

Apply `hex` to reduce the goal to its premises. Establish `hsa : IsSelfAdjoint ((LinearMap.toMatrix b b T).map φ)`. Use extensionality with `i j`. Simplify using `only [Matrix.star_apply, Matrix.map_apply, LinearMap.toMatrix_apply, ← hs, repr_orth B b hb, hT, LinearMap.mulLeft_apply]`. Rewrite using `[← herm_symm B x hx.2, herm_mul_left B x B.g (b j), hreg.1]`.

Use `⟨(⟨_, hsa⟩, fun i => φ (b.repr w i), 0), ?_⟩` and prove the remaining obligations. Apply `Inv_map_injective φ.symm.toRingHom φ.symm.injective` to reduce the goal to its premises. Simplify using `only`. Rewrite using `[← inv_mapGl, Inv_map_map]`. Use `Eq.trans (congrArg JR.inv ?_) (hinv b)` and prove the remaining obligations.

Use `Prod.ext (Matrix.ext fun i j => φ.symm_apply_apply _) (Prod.ext (funext fun i => φ.symm_apply_apply _) (Prod.ext (funext fun j => ?_) ?_))` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `φ.symm (star (φ (b.repr w j))) = lw (b j)`. Rewrite using `[← hs, RingEquiv.symm_apply_apply, hlw', repr_orth B b hb, ← herm_symm B x hx.2]`. Simplify using `[mapGl, Hn.toGl, Yb]`.
-/
theorem countIdentity_of_unitMatch (hUM : ∀ r : ℕ, GlobalTheory.JR.UnitMatch r) : CountIdentity := by
  intro K B hreg x w hx hw
  obtain ⟨F, E, _, _, _, _, _, φ, hs, hi⟩ := exists_normed K
  obtain ⟨M⟩ := MeasExist.nonempty_meas (finrank K.E B.A) F E
  obtain ⟨e, he⟩ := GlobalTheory.UnitLemma.exists_basis_pow_of_separable K B hreg.2
  have heσ : ∀ i, B.σ (e i) = e i := fun i => by rw [he, map_pow, hreg.1]
  have hspan : Submodule.span K.E (Set.range fun l : ℕ => B.g ^ l) = ⊤ := by
    rw [eq_top_iff, ← e.span_eq]
    refine Submodule.span_mono ?_
    rintro _ ⟨i, rfl⟩
    exact ⟨i, (he i).symm⟩
  set u := x * (w * B.σ w) with hu
  have huσ : B.σ u = u := by rw [hu, map_mul, map_mul, hx.2, B.σ_σ, mul_comm w]
  have huu : IsUnit u := hx.1.mul (hw.mul (hw.map B.σ))
  set T := LinearMap.mulLeft K.E B.g with hT
  set lw : B.A →ₗ[K.E] K.E := Algebra.trace K.E B.A ∘ₗ LinearMap.mulLeft K.E (x * B.σ w) with hlw
  have hlw' : ∀ y, lw y = B.herm x y w := by
    intro y; simp only [hlw, InvAlg.herm, LinearMap.comp_apply, LinearMap.mulLeft_apply]; congr 1; ring
  obtain ⟨Y, hY⟩ : ∃ Y : Gl (finrank K.E B.A) F, mapGl (iota F φ) Y = Yb e T u (Algebra.trace K.E B.A) := by
    have a1 : ∀ i j, ∃ t : F, iota F φ t = LinearMap.toMatrix e e T i j := fun i j => by
      refine exists_iota hs ?_
      rw [LinearMap.toMatrix_apply, ← repr_sigma B e heσ, hT, LinearMap.mulLeft_apply, map_mul, hreg.1, heσ]
    have a2 : ∀ i, ∃ t : F, iota F φ t = e.repr u i := fun i => by
      refine exists_iota hs ?_
      rw [← repr_sigma B e heσ, huσ]
    have a3 : ∀ i, ∃ t : F, iota F φ t = Algebra.trace K.E B.A (e i) := fun i => by
      refine exists_iota hs ?_
      rw [← trace_sigma, heσ]
    choose P hP using a1
    choose b hb using a2
    choose c hc using a3
    exact ⟨(Matrix.of P, b, c, 0), Prod.ext (Matrix.ext hP) (Prod.ext (funext hb) (Prod.ext (funext hc) (map_zero _)))⟩
  have hinv : ∀ b : Basis (Fin (finrank K.E B.A)) K.E B.A,
      JR.inv (Yb b T w lw) = (JR.inv Y).map (iota F φ) := by
    intro b
    rw [← inv_mapGl, hY, inv_Yb, inv_Yb]
    refine Prod.ext rfl (Prod.ext (funext fun i => ?_) rfl)
    simp only [hlw, hT, hu, LinearMap.pow_mulLeft, LinearMap.comp_apply, LinearMap.mulLeft_apply]
    congr 1; ring
  have hΔE : Delta ((JR.inv Y).map (iota F φ)) ≠ 0 := by
    rw [← inv_mapGl, hY, Delta_inv, Cm_mul_Bm]
    simp only [mom_Yb, hT, LinearMap.pow_mulLeft, LinearMap.mulLeft_apply]
    exact GlobalTheory.T.det_trace_pow_add_mul_unit_ne_zero K B hreg.2 u huu
  have hΔ : Delta (JR.inv Y) ≠ 0 := by
    intro h0
    apply hΔE
    rw [← inv_mapGl, Delta_inv, Cm_mapGl, Bm_mapGl, ← Matrix.map_mul, ← RingHom.mapMatrix_apply,
      ← RingHom.map_det, ← Delta_inv, h0, map_zero]
  have hG : orbG M (unitG _ F) (sec (JR.inv Y)) = ((B.GG u : ℚ) : ℂ) := by
    obtain ⟨γ, ⟨hγ, -⟩, -⟩ := (GlobalTheory.JR.normalForm_invariants F _).2.2.2.2 Y (sec (JR.inv Y)) hΔ ((GlobalTheory.JR.normalForm_invariants F _).2.1 _)
    exact orbG_eq B hs hi M u _ (tw_fixed B hs e heσ γ) _ (by rw [← hγ, mapGl_act, hY, Yb_tw])
  obtain ⟨m1, m2⟩ := hUM _ F E M (JR.inv Y) hΔ
  rw [hG] at m2
  by_cases hex : ∃ X : Hn (finrank K.E B.A) F E, HasInv X (JR.inv Y)
  · obtain ⟨X, hX⟩ := hex
    have h1 : JR.inv (mapGl φ.symm.toRingHom X.toGl) = JR.inv (Yb e T w lw) := by
      rw [inv_mapGl, hX, hinv]; rfl
    obtain ⟨γ, ⟨hγ, -⟩, -⟩ := (GlobalTheory.JR.normalForm_invariants K.E _).2.2.2.2 _ _ (by rw [hinv]; exact hΔE) h1
    rw [← Yb_tw] at hγ
    have hγ' := hγ
    simp only [mapGl, Yb, Hn.toGl, Prod.mk.injEq] at hγ'
    obtain ⟨y1, y2, y3, -⟩ := hγ'
    have hcs : ∀ t : E, K.c (φ.symm t) = φ.symm (star t) := fun t => by
      apply φ.injective; rw [hs]; simp
    have horth := GlobalTheory.UnitLemma.herm_basis_orthonormal K B x w hreg.1 hw hspan _ (tw e γ) (fun i j => by
      have e1 := congrFun (congrFun y1 i) j
      have e2 := congrFun (congrFun y1 j) i
      rw [LinearMap.toMatrix_apply, hT, LinearMap.mulLeft_apply] at e1 e2
      rw [e1, e2]
      exact (hcs _).trans (congrArg φ.symm (congrFun (congrFun X.1.2 j) i))) (fun j => by
      rw [← hlw', congrFun y3 j, congrFun y2 j]
      exact (hcs _).symm)
    have h2 := m1 X hX
    rw [hG, orbU_eq B hs hi M hx.2 w lw _ horth X hγ.symm] at h2
    exact_mod_cast h2
  · have h0 : B.GG u = 0 := by exact_mod_cast m2 hex
    rw [h0]
    by_contra hne
    have hne' : B.UU x w ≠ 0 := fun h => hne (by rw [h]; rfl)
    obtain ⟨⟨⟨L, hL⟩, -⟩⟩ := (Nat.card_ne_zero.1 hne').1
    obtain ⟨b, -, hb⟩ := exists_orth B hx.2 L hL.1 hL.2.2
    apply hex
    have hsa : IsSelfAdjoint ((LinearMap.toMatrix b b T).map φ) := by
      ext i j
      simp only [Matrix.star_apply, Matrix.map_apply, LinearMap.toMatrix_apply, ← hs, repr_orth B b hb, hT,
        LinearMap.mulLeft_apply]
      rw [← herm_symm B x hx.2, herm_mul_left B x B.g (b j), hreg.1]
    refine ⟨(⟨_, hsa⟩, fun i => φ (b.repr w i), 0), ?_⟩
    apply Inv_map_injective φ.symm.toRingHom φ.symm.injective
    simp only
    rw [← inv_mapGl, Inv_map_map]
    refine Eq.trans (congrArg JR.inv ?_) (hinv b)
    refine Prod.ext (Matrix.ext fun i j => φ.symm_apply_apply _) (Prod.ext (funext fun i => φ.symm_apply_apply _)
      (Prod.ext (funext fun j => ?_) ?_))
    · change φ.symm (star (φ (b.repr w j))) = lw (b j)
      rw [← hs, RingEquiv.symm_apply_apply, hlw', repr_orth B b hb, ← herm_symm B x hx.2]
    · simp [mapGl, Hn.toGl, Yb]

end GlobalTheory.CountId
