import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsKInfEqMul
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProjArchOfInfEmbArchPi
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryRealPointsStructureRealPlaces
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryActionAtRealPlace
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsArchEquivEq

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ComplexOrder

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.Published GlobalTheory.Published.AutFin

namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.ArchIwasawa

/- English proof (translation)
Establish `hJi : J⁻¹ * J = 1` using `Matrix.nonsing_inv_mul J hJu`. Establish `hJi' : J * J⁻¹ = 1` using `Matrix.mul_nonsing_inv J hJu`. Establish `hJH : (J⁻¹)ᴴ = J⁻¹` using `hJ.inv.eq`. Establish `hPH : Pᴴ = P` using `hP.isHermitian.eq`. Establish `hYX : Yᴴ * J * X = 1`.

Use `congrArg conjTranspose hXY` as an intermediate fact. Simplify `this` using `only [conjTranspose_mul, conjTranspose_conjTranspose, hJ.eq, conjTranspose_one, Matrix.mul_assoc]`. Establish `hXinj : Function.Injective X.mulVec` using `fun a b hab => by`. Use `congrArg (Matrix.mulVec (Yᴴ * J)) hab` as an intermediate fact. Simplify `this` using `only [Matrix.mulVec_mulVec, hYX, Matrix.one_mulVec]`.

Establish `hG : (Xᴴ * P * X).PosDef` using `hP.conjTranspose_mul_mul_same hXinj`. Take `⟨R, hRt, hR⟩` from `GroundTheory.Automorphic.exists_isUpperTriangular_conjTranspose_mul_self hG`. Establish `hRu : IsUnit R.det`. Establish `hd : IsUnit (Rᴴ * R).det` using `by rw [hR]; exact (Matrix.isUnit_iff_isUnit_det _).1 hG.isUnit`. Rewrite `hd` using `[Matrix.det_mul]`.

Conclude with `isUnit_of_mul_isUnit_right hd`. Use `letI := Matrix.invertibleOfIsUnitDet R hRu`. Establish `hBt : (R⁻¹).BlockTriangular id` using `blockTriangular_inv_of_blockTriangular hRt`. Establish `hRi : R⁻¹ * R = 1` using `Matrix.nonsing_inv_mul R hRu`. Establish `hRi' : R * R⁻¹ = 1` using `Matrix.mul_nonsing_inv R hRu`.

Establish `hRiH : (R⁻¹)ᴴ * Rᴴ = 1` using `by rw [← conjTranspose_mul, hRi', conjTranspose_one]`. Establish `hX'P : (X * R⁻¹)ᴴ * P * (X * R⁻¹) = 1`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = ((R⁻¹)ᴴ * Rᴴ) * (R * R⁻¹) := by rw [← hR]; simp only [Matrix.mul_assoc]`.

Use `_ = 1 := by rw [hRiH, hRi', Matrix.one_mul]`. Establish `hX'J : (X * R⁻¹)ᴴ * J * (X * R⁻¹) = 0`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = 0 := by rw [hXX, Matrix.mul_zero, Matrix.zero_mul]`.

Use `set X' : Matrix (Fin n) (Fin r) ℂ := X * R⁻¹ with hX'`. Establish `hY'J : (J⁻¹ * (P * X'))ᴴ * J * (J⁻¹ * (P * X')) = 0`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [conjTranspose_mul, hJH, hPH, Matrix.mul_assoc]`. Use `_ = 0 := by rw [hJi', Matrix.mul_one, hPJ, hX'J]`.

Establish `hXY' : X'ᴴ * J * (J⁻¹ * (P * X')) = 1`. Combine the equalities or inequalities in the displayed calculation. Establish `hPX' : P * X' = J * (J⁻¹ * (P * X'))`. Rewrite using `[← Matrix.mul_assoc J, hJi', Matrix.one_mul]`. Take `⟨p, k, h1, h2, h3, h4, B, hB, hpB⟩` from `GlobalTheory.CompanionTheory.WittIwasawa.iwasawa_witt_flag n r J P X' _ hJ hJu hX'J hY'J hXY' hP hPJ hPX' g hg`.

Use `⟨p, k, h1, h2, h3, h4, R⁻¹ * B * R, (hBt.mul hB).mul hRt, ?_⟩` and prove the remaining obligations. Establish `hXX' : X = X' * R` using `by rw [hX', Matrix.mul_assoc, hRi, Matrix.mul_one]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem iwasawa_majorant (n r : ℕ) (J P : Matrix (Fin n) (Fin n) ℂ) (X Y : Matrix (Fin n) (Fin r) ℂ)
    (hJ : J.IsHermitian) (hJu : IsUnit J.det) (hXX : Xᴴ * J * X = 0) (hXY : Xᴴ * J * Y = 1) (hP : P.PosDef)
    (hPJ : P * J⁻¹ * P = J) (g : Matrix (Fin n) (Fin n) ℂ) (hg : gᴴ * J * g = J) :
    ∃ p k : Matrix (Fin n) (Fin n) ℂ, pᴴ * J * p = J ∧ kᴴ * J * k = J ∧ kᴴ * P * k = P ∧
      g = p * k ∧ ∃ B : Matrix (Fin r) (Fin r) ℂ, B.BlockTriangular id ∧ p * X = X * B := by
  have hJi : J⁻¹ * J = 1 := Matrix.nonsing_inv_mul J hJu
  have hJi' : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv J hJu
  have hJH : (J⁻¹)ᴴ = J⁻¹ := hJ.inv.eq
  have hPH : Pᴴ = P := hP.isHermitian.eq
  have hYX : Yᴴ * J * X = 1 := by
    have := congrArg conjTranspose hXY
    simpa only [conjTranspose_mul, conjTranspose_conjTranspose, hJ.eq, conjTranspose_one, Matrix.mul_assoc] using this
  have hXinj : Function.Injective X.mulVec := fun a b hab => by
    have := congrArg (Matrix.mulVec (Yᴴ * J)) hab
    simpa only [Matrix.mulVec_mulVec, hYX, Matrix.one_mulVec] using this
  have hG : (Xᴴ * P * X).PosDef := hP.conjTranspose_mul_mul_same hXinj
  obtain ⟨R, hRt, hR⟩ := GroundTheory.Automorphic.exists_isUpperTriangular_conjTranspose_mul_self hG
  have hRu : IsUnit R.det := by
    have hd : IsUnit (Rᴴ * R).det := by rw [hR]; exact (Matrix.isUnit_iff_isUnit_det _).1 hG.isUnit
    rw [Matrix.det_mul] at hd
    exact isUnit_of_mul_isUnit_right hd
  letI := Matrix.invertibleOfIsUnitDet R hRu
  have hBt : (R⁻¹).BlockTriangular id := blockTriangular_inv_of_blockTriangular hRt
  have hRi : R⁻¹ * R = 1 := Matrix.nonsing_inv_mul R hRu
  have hRi' : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv R hRu
  have hRiH : (R⁻¹)ᴴ * Rᴴ = 1 := by rw [← conjTranspose_mul, hRi', conjTranspose_one]
  have hX'P : (X * R⁻¹)ᴴ * P * (X * R⁻¹) = 1 := by
    calc (X * R⁻¹)ᴴ * P * (X * R⁻¹) = (R⁻¹)ᴴ * (Xᴴ * P * X) * R⁻¹ := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = ((R⁻¹)ᴴ * Rᴴ) * (R * R⁻¹) := by rw [← hR]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hRiH, hRi', Matrix.one_mul]
  have hX'J : (X * R⁻¹)ᴴ * J * (X * R⁻¹) = 0 := by
    calc (X * R⁻¹)ᴴ * J * (X * R⁻¹) = (R⁻¹)ᴴ * (Xᴴ * J * X) * R⁻¹ := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = 0 := by rw [hXX, Matrix.mul_zero, Matrix.zero_mul]
  set X' : Matrix (Fin n) (Fin r) ℂ := X * R⁻¹ with hX'
  have hY'J : (J⁻¹ * (P * X'))ᴴ * J * (J⁻¹ * (P * X')) = 0 := by
    calc (J⁻¹ * (P * X'))ᴴ * J * (J⁻¹ * (P * X')) = X'ᴴ * (P * J⁻¹ * (J * J⁻¹) * P) * X' := by
          simp only [conjTranspose_mul, hJH, hPH, Matrix.mul_assoc]
      _ = 0 := by rw [hJi', Matrix.mul_one, hPJ, hX'J]
  have hXY' : X'ᴴ * J * (J⁻¹ * (P * X')) = 1 := by
    calc X'ᴴ * J * (J⁻¹ * (P * X')) = X'ᴴ * (J * J⁻¹) * P * X' := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hJi', Matrix.mul_one, hX'P]
  have hPX' : P * X' = J * (J⁻¹ * (P * X')) := by
    rw [← Matrix.mul_assoc J, hJi', Matrix.one_mul]
  obtain ⟨p, k, h1, h2, h3, h4, B, hB, hpB⟩ := GlobalTheory.CompanionTheory.WittIwasawa.iwasawa_witt_flag n r J P X' _ hJ hJu hX'J hY'J hXY' hP hPJ
    hPX' g hg
  refine ⟨p, k, h1, h2, h3, h4, R⁻¹ * B * R, (hBt.mul hB).mul hRt, ?_⟩
  have hXX' : X = X' * R := by rw [hX', Matrix.mul_assoc, hRi, Matrix.mul_one]
  calc p * X = (p * X') * R := by rw [Matrix.mul_assoc, ← hXX']
    _ = X' * (B * R) := by rw [hpB, Matrix.mul_assoc]
    _ = X * (R⁻¹ * B * R) := by simp only [hX', Matrix.mul_assoc]

/- English proof (translation)
Establish `hd : IsUnit f.det` using `(Matrix.isUnit_iff_isUnit_det f).1 hf`. Establish `h1 : f⁻¹ * f = 1` using `Matrix.nonsing_inv_mul f hd`. Establish `h2 : f * f⁻¹ = 1` using `Matrix.mul_nonsing_inv f hd`. Establish `h3 : fᴴ * (f⁻¹)ᴴ = 1` using `by rw [← conjTranspose_mul, h1, conjTranspose_one]`. Establish `h4 : (f⁻¹)ᴴ * fᴴ = 1` using `by rw [← conjTranspose_mul, h2, conjTranspose_one]`.

Establish `hJ` using `Formalism.REAL.Jm_mul_self e`. Establish `hinv : (fᴴ * Formalism.REAL.Jm e * f)⁻¹ = f⁻¹ * Formalism.REAL.Jm e * (f⁻¹)ᴴ`. Use `Matrix.inv_eq_right_inv ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h2, Matrix.mul_one]`.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = 1 := by rw [hJ, Matrix.mul_one, h3]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `(Matrix.PosDef.one (n := Fin n) (R := ℂ)).conjTranspose_mul_mul_same (Matrix.mulVec_injective_iff_isUnit.2 hf)` as an intermediate fact. Simplify using `using this`.

Rewrite using `[hinv]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem frame_majorant {n : ℕ} {e : Fin n → Bool} {f : Matrix (Fin n) (Fin n) ℂ} (hf : IsUnit f) :
    (fᴴ * f).PosDef ∧ (fᴴ * f) * (fᴴ * Formalism.REAL.Jm e * f)⁻¹ * (fᴴ * f) = fᴴ * Formalism.REAL.Jm e * f := by
  have hd : IsUnit f.det := (Matrix.isUnit_iff_isUnit_det f).1 hf
  have h1 : f⁻¹ * f = 1 := Matrix.nonsing_inv_mul f hd
  have h2 : f * f⁻¹ = 1 := Matrix.mul_nonsing_inv f hd
  have h3 : fᴴ * (f⁻¹)ᴴ = 1 := by rw [← conjTranspose_mul, h1, conjTranspose_one]
  have h4 : (f⁻¹)ᴴ * fᴴ = 1 := by rw [← conjTranspose_mul, h2, conjTranspose_one]
  have hJ := Formalism.REAL.Jm_mul_self e
  have hinv : (fᴴ * Formalism.REAL.Jm e * f)⁻¹ = f⁻¹ * Formalism.REAL.Jm e * (f⁻¹)ᴴ := by
    refine Matrix.inv_eq_right_inv ?_
    calc fᴴ * Formalism.REAL.Jm e * f * (f⁻¹ * Formalism.REAL.Jm e * (f⁻¹)ᴴ)
        = fᴴ * Formalism.REAL.Jm e * (f * f⁻¹) * Formalism.REAL.Jm e * (f⁻¹)ᴴ := by simp only [Matrix.mul_assoc]
      _ = fᴴ * (Formalism.REAL.Jm e * Formalism.REAL.Jm e) * (f⁻¹)ᴴ := by
          rw [h2, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hJ, Matrix.mul_one, h3]
  refine ⟨?_, ?_⟩
  · have := (Matrix.PosDef.one (n := Fin n) (R := ℂ)).conjTranspose_mul_mul_same
      (Matrix.mulVec_injective_iff_isUnit.2 hf)
    simpa using this
  · rw [hinv]
    calc fᴴ * f * (f⁻¹ * Formalism.REAL.Jm e * (f⁻¹)ᴴ) * (fᴴ * f)
        = fᴴ * (f * f⁻¹) * Formalism.REAL.Jm e * ((f⁻¹)ᴴ * fᴴ) * f := by simp only [Matrix.mul_assoc]
      _ = fᴴ * Formalism.REAL.Jm e * f := by rw [h2, h4, Matrix.mul_one, Matrix.mul_one]

/- English proof (translation)
Establish `hd : IsUnit f.det` using `(Matrix.isUnit_iff_isUnit_det f).1 hf`. Establish `h1 : f⁻¹ * f = 1` using `Matrix.nonsing_inv_mul f hd`. Establish `h2 : f * f⁻¹ = 1` using `Matrix.mul_nonsing_inv f hd`. Establish `h4 : (f⁻¹)ᴴ * fᴴ = 1` using `by rw [← conjTranspose_mul, h2, conjTranspose_one]`. Establish `key : ∀ M : Matrix (Fin n) (Fin n) ℂ, kᴴ * (fᴴ * M * f) * k = fᴴ * M * f → (f * k * f⁻¹)ᴴ * M * (f * k * f⁻¹) = M` using `fun M hM => by`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = ((f⁻¹)ᴴ * fᴴ) * M * (f * f⁻¹) := by rw [hM]; simp only [Matrix.mul_assoc]`. Use `_ = M := by rw [h4, h2, Matrix.one_mul, Matrix.mul_one]`. Establish `hm1 : (f * k * f⁻¹)ᴴ * (f * k * f⁻¹) = 1`.

Use `key 1 (by simpa using hk2)` as an intermediate fact. Simplify using `using this`. Establish `hm2` using `key _ hk1`. Use `set m : Matrix (Fin n) (Fin n) ℂ := f * k * f⁻¹ with hm`. Establish `hm3 : m * mᴴ = 1` using `mul_eq_one_comm.1 hm1`.

Establish `hK : m ∈ Formalism.REAL.Kset e`. Use `⟨Matrix.mem_unitaryGroup_iff'.2 hm1, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite `hK` using `[← Formalism.REAL.range_toMK]`. Take `⟨κ, hκ⟩` from `hK`.

Use `⟨κ, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Formalism.REAL.toMK κ = m at hκ`. Rewrite using `[hκ, hm]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_KG_of_stab {n : ℕ} {e : Fin n → Bool} {f k : Matrix (Fin n) (Fin n) ℂ} (hf : IsUnit f)
    (hk1 : kᴴ * (fᴴ * Formalism.REAL.Jm e * f) * k = fᴴ * Formalism.REAL.Jm e * f) (hk2 : kᴴ * (fᴴ * f) * k = fᴴ * f) :
    ∃ κ : Formalism.REAL.KG e, k = f⁻¹ * Formalism.REAL.toMK κ * f := by
  have hd : IsUnit f.det := (Matrix.isUnit_iff_isUnit_det f).1 hf
  have h1 : f⁻¹ * f = 1 := Matrix.nonsing_inv_mul f hd
  have h2 : f * f⁻¹ = 1 := Matrix.mul_nonsing_inv f hd
  have h4 : (f⁻¹)ᴴ * fᴴ = 1 := by rw [← conjTranspose_mul, h2, conjTranspose_one]
  have key : ∀ M : Matrix (Fin n) (Fin n) ℂ, kᴴ * (fᴴ * M * f) * k = fᴴ * M * f →
      (f * k * f⁻¹)ᴴ * M * (f * k * f⁻¹) = M := fun M hM => by
    calc (f * k * f⁻¹)ᴴ * M * (f * k * f⁻¹) = (f⁻¹)ᴴ * (kᴴ * (fᴴ * M * f) * k) * f⁻¹ := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = ((f⁻¹)ᴴ * fᴴ) * M * (f * f⁻¹) := by rw [hM]; simp only [Matrix.mul_assoc]
      _ = M := by rw [h4, h2, Matrix.one_mul, Matrix.mul_one]
  have hm1 : (f * k * f⁻¹)ᴴ * (f * k * f⁻¹) = 1 := by
    have := key 1 (by simpa using hk2)
    simpa using this
  have hm2 := key _ hk1
  set m : Matrix (Fin n) (Fin n) ℂ := f * k * f⁻¹ with hm
  have hm3 : m * mᴴ = 1 := mul_eq_one_comm.1 hm1
  have hK : m ∈ Formalism.REAL.Kset e := by
    refine ⟨Matrix.mem_unitaryGroup_iff'.2 hm1, ?_⟩
    calc m * Formalism.REAL.Jm e = m * (mᴴ * Formalism.REAL.Jm e * m) := by rw [hm2]
      _ = (m * mᴴ) * Formalism.REAL.Jm e * m := by simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm e * m := by rw [hm3, Matrix.one_mul]
  rw [← Formalism.REAL.range_toMK] at hK
  obtain ⟨κ, hκ⟩ := hK
  refine ⟨κ, ?_⟩
  change Formalism.REAL.toMK κ = m at hκ
  rw [hκ, hm]
  calc k = (f⁻¹ * f) * k * (f⁻¹ * f) := by rw [h1, Matrix.one_mul, Matrix.mul_one]
    _ = f⁻¹ * (f * k * f⁻¹) * f := by simp only [Matrix.mul_assoc]

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}
  {ε : D.what₂.Tau → Fin V.rank → Bool} {fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}

open GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.KInf in

/- English proof (translation)
Establish `R` using `(GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ V`. Establish `hat` using `fun τ => isAtTau_kAt θ V hθ τ (hfr τ).1 (hfr τ).2 (κ τ)`. Use `⟨list_prod_mem fun x hx => ?_, fun τ => ?_⟩` and prove the remaining obligations. Take `⟨τ, -, rfl⟩` from `List.mem_map.1 hx`. Conclude with `(hat τ).1`.

Establish `key : ∀ l : List D.what₂.Tau, l.Nodup → (τ ∈ l → infMat D.sp.cm.sig V.gram (θ τ) ((l.map fun τ => kAt θ V τ (ε τ) (fr τ) (κ τ)).prod) = (fr τ)⁻¹ * Formalism.REAL.toMK (κ τ) * fr τ) ∧ (τ ∉ l → infMat D.sp.cm.sig V.gram (θ τ) ((l.map fun τ => kAt θ V τ (ε τ) (fr τ) (κ τ)).prod) = 1 …`. Introduce `l`. Proceed by induction on `l with`. Consider the case `nil`. Introduce `_`.

Conclude with `⟨fun h => absurd h List.not_mem_nil, fun _ => R.2.2.2.2.1 1 (one_mem _) τ⟩`. Consider the case `cons a l ih`. Introduce `hn`. Take `⟨ha, hl⟩` from `List.nodup_cons.1 hn`. Take `⟨i1, i2⟩` from `ih hl`.

Rewrite using `[List.map_cons, List.prod_cons, R.2.2.2.1]`. Distinguish the cases in `h : a = τ`. Substitute `h` using the available equality. Conclude with `⟨fun _ => by rw [(hat a).2.1, i2 ha, Matrix.mul_one], fun hh => absurd List.mem_cons_self hh⟩`. Rewrite using `[(hat a).2.2 τ (Ne.symm h), Matrix.one_mul]`.

Conclude with `⟨fun hm => i1 (List.mem_of_ne_of_mem (Ne.symm h) hm), fun hm => i2 fun q => hm (List.mem_cons_of_mem _ q)⟩`. Conclude with `(key _ (Finset.nodup_toList _)).1 (Finset.mem_toList.2 (Finset.mem_univ τ))`.
-/
theorem kInf_spec (hθ : IsInfFam θ) (hfr : IsFrameFam V ε fr) (κ : ∀ τ, Formalism.REAL.KG (ε τ)) :
    kInf θ V ε fr κ ∈ GinfC V ∧ ∀ τ, infMat D.sp.cm.sig V.gram (θ τ) (kInf θ V ε fr κ) =
      (fr τ)⁻¹ * Formalism.REAL.toMK (κ τ) * fr τ := by
  have R := (GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ V
  have hat := fun τ => isAtTau_kAt θ V hθ τ (hfr τ).1 (hfr τ).2 (κ τ)
  refine ⟨list_prod_mem fun x hx => ?_, fun τ => ?_⟩
  · obtain ⟨τ, -, rfl⟩ := List.mem_map.1 hx
    exact (hat τ).1
  · have key : ∀ l : List D.what₂.Tau, l.Nodup →
        (τ ∈ l → infMat D.sp.cm.sig V.gram (θ τ) ((l.map fun τ => kAt θ V τ (ε τ) (fr τ) (κ τ)).prod) =
          (fr τ)⁻¹ * Formalism.REAL.toMK (κ τ) * fr τ) ∧
        (τ ∉ l → infMat D.sp.cm.sig V.gram (θ τ) ((l.map fun τ => kAt θ V τ (ε τ) (fr τ) (κ τ)).prod) = 1) := by
      intro l
      induction l with
      | nil =>
        intro _
        exact ⟨fun h => absurd h List.not_mem_nil, fun _ => R.2.2.2.2.1 1 (one_mem _) τ⟩
      | cons a l ih =>
        intro hn
        obtain ⟨ha, hl⟩ := List.nodup_cons.1 hn
        obtain ⟨i1, i2⟩ := ih hl
        rw [List.map_cons, List.prod_cons, R.2.2.2.1]
        by_cases h : a = τ
        · subst h
          exact ⟨fun _ => by rw [(hat a).2.1, i2 ha, Matrix.mul_one], fun hh => absurd List.mem_cons_self hh⟩
        · rw [(hat a).2.2 τ (Ne.symm h), Matrix.one_mul]
          exact ⟨fun hm => i1 (List.mem_of_ne_of_mem (Ne.symm h) hm), fun hm => i2 fun q => hm (List.mem_cons_of_mem _ q)⟩
    exact (key _ (Finset.nodup_toList _)).1 (Finset.mem_toList.2 (Finset.mem_univ τ))

/- English proof (translation)
Establish `hs : ∀ w : NumberField.InfinitePlace D.host.F, ∃ (τ : GlobalTheory.AdelicU.EmbOver D.host.E w) (ρ : D.what₂.Tau), τ.1 = tauE D ρ`. Introduce `w`. Take `⟨ρ, rfl⟩` from `(GlobalTheory.AdelicU.placeOf_bijective D).2 w`. Conclude with `⟨GlobalTheory.AdelicU.embOverOf D ρ, ρ, rfl⟩`. Use `choose τ ρ hτ using hs`.

Use `GlobalTheory.CompanionTheory.SiegelArch.mem_minPar_of V.gram (GlobalTheory.AdelicU.isCMExt_host D) τ hp hQ fun w => ?_` and prove the remaining obligations. Take `⟨B, hB, e⟩` from `h (ρ w)`. Use `⟨B, hB, ?_⟩` and prove the remaining obligations. Rewrite using `[hτ w, GlobalTheory.Orb.archMat_eq_archEquiv _ (GlobalTheory.AdelicU.isCMExt_host D), ← GlobalTheory.AdelicU.infMat_infProj, ← GlobalTheory.AdelicU.eq_infProj hθ (τ w) (hτ w)]`. Conclude with `e`.
-/
theorem mem_minPar_real (hθ : IsInfFam θ) {r : ℕ} {X : Matrix (Fin V.rank) (Fin r) D.host.E}
    {Q : Matrix (Fin r) (Fin V.rank) D.host.E} (hQ : Q * X = 1) {p : GA D V} (hp : p ∈ GinfC V)
    (h : ∀ ρ, ∃ B : Matrix (Fin r) (Fin r) ℂ, B.BlockTriangular id ∧
      infMat D.sp.cm.sig V.gram (θ ρ) p * X.map (tauE D ρ) = X.map (tauE D ρ) * B) :
    p ∈ PositivityTheory.ThKR.minPar D.sp.cm.sig V.gram X := by
  have hs : ∀ w : NumberField.InfinitePlace D.host.F, ∃ (τ : GlobalTheory.AdelicU.EmbOver D.host.E w) (ρ : D.what₂.Tau), τ.1 = tauE D ρ := by
    intro w
    obtain ⟨ρ, rfl⟩ := (GlobalTheory.AdelicU.placeOf_bijective D).2 w
    exact ⟨GlobalTheory.AdelicU.embOverOf D ρ, ρ, rfl⟩
  choose τ ρ hτ using hs
  refine GlobalTheory.CompanionTheory.SiegelArch.mem_minPar_of V.gram (GlobalTheory.AdelicU.isCMExt_host D) τ hp hQ fun w => ?_
  obtain ⟨B, hB, e⟩ := h (ρ w)
  refine ⟨B, hB, ?_⟩
  rw [hτ w, GlobalTheory.Orb.archMat_eq_archEquiv _ (GlobalTheory.AdelicU.isCMExt_host D), ← GlobalTheory.AdelicU.infMat_infProj,
    ← GlobalTheory.AdelicU.eq_infProj hθ (τ w) (hτ w)]
  exact e

/- English proof (translation)
Introduce `D θ hθ V ε fr hfr m X Y hW g hg`. Establish `hcm` using `GlobalTheory.AdelicU.isCMExt_host D`. Establish `R` using `(GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ V`. Establish `hher` using `fun τ => GlobalTheory.SmoothForms.RealPts.gramAt_herm V τ`. Establish `hmap : ∀ (τ : D.what₂.Tau) {A B : Matrix (Fin V.rank) (Fin m) D.host.E}, (A.map (tauE D τ))ᴴ * gramAt D V τ * B.map (tauE D τ) = (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) A * V.gram * B).map (tauE D τ)` using `fun τ {A B} => by`.

Rewrite using `[show gramAt D V τ = V.gram.map (tauE D τ) from rfl, Matrix.map_mul, Matrix.map_mul, GlobalTheory.CompanionTheory.SiegelArch.conjT_map hcm]`. Establish `hxx : ∀ τ, (X.map (tauE D τ))ᴴ * gramAt D V τ * X.map (tauE D τ) = 0` using `fun τ => by`. Rewrite using `[hmap, hW.xx]`. Simplify using the standard rewrite rules. Establish `hxy : ∀ τ, (X.map (tauE D τ))ᴴ * gramAt D V τ * Y.map (tauE D τ) = 1` using `fun τ => by`.

Rewrite using `[hmap, hW.xy, Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `hyx : ∀ τ, (Y.map (tauE D τ))ᴴ * gramAt D V τ * X.map (tauE D τ) = 1` using `fun τ => by`. Establish `h` using `congrArg conjTranspose (hxy τ)`. Rewrite `h` using `[conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hher τ, conjTranspose_one]`. Rewrite using `[Matrix.mul_assoc]`.

Conclude with `h`. Take `⟨w₀⟩ : Nonempty (NumberField.InfinitePlace D.host.F)` from `inferInstance`. Take `⟨τ₀, -⟩` from `(GlobalTheory.AdelicU.placeOf_bijective D).2 w₀`. Establish `hQ : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Y * V.gram * X = 1`. Establish `h : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Y * V.gram * X).map (tauE D τ₀) = (1 : Matrix (Fin m) (Fin m) D.host.E).map (tauE D τ₀)`.

Rewrite using `[← hmap, hyx, Matrix.map_one _ (map_zero _) (map_one _)]`. Conclude with `Matrix.map_injective (tauE D τ₀).injective h`. Establish `place : ∀ τ, ∃ (q : Matrix (Fin V.rank) (Fin V.rank) ℂ) (κ : Formalism.REAL.KG (ε τ)), infMat D.sp.cm.sig V.gram (θ τ) g = q * ((fr τ)⁻¹ * Formalism.REAL.toMK κ * fr τ) ∧ ∃ B : Matrix (Fin m) (Fin m) ℂ, B.BlockTriangular id ∧ q * X.map (tauE D τ) = X.map (tauE D τ) * B`. Introduce `τ`. Establish `hG : (fr τ)ᴴ * Formalism.REAL.Jm (ε τ) * fr τ = gramAt D V τ` using `(hfr τ).2`.

Take `⟨hPd, hPJ⟩` from `frame_majorant (e := ε τ) (hfr τ).1`. Rewrite `hPJ` using `[hG]`. Take `⟨p, k, -, h2, h3, h4, B, hB, hpB⟩` from `iwasawa_majorant V.rank m (gramAt D V τ) ((fr τ)ᴴ * fr τ) _ _ (hher τ) (GlobalTheory.SmoothForms.RealPts.gramAt_unit V τ) (hxx τ) (hxy τ) hPd hPJ _ (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V g τ)`. Take `⟨κ, hκ⟩` from `exists_KG_of_stab (e := ε τ) (hfr τ).1 (by rw [hG]; exact h2) h3`. Conclude with `⟨p, κ, hκ ▸ h4, B, hB, hpB⟩`.

Use `choose q κ hq2 hq3 using place`. Take `⟨hk, hkm⟩` from `kInf_spec hθ hfr κ`. Use `set k := GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.KInf.kInf θ V ε fr κ with hkdef`. Use `⟨g * k⁻¹, ?_, κ, (inv_mul_cancel_right g k).symm⟩` and prove the remaining obligations. Use `mem_minPar_real hθ hQ (mul_mem hg (inv_mem hk)) fun τ => ?_` and prove the remaining obligations.

Establish `e : infMat D.sp.cm.sig V.gram (θ τ) (g * k⁻¹) = q τ`. Establish `h2 : infMat D.sp.cm.sig V.gram (θ τ) k * infMat D.sp.cm.sig V.gram (θ τ) k⁻¹ = 1`. Rewrite using `[← R.2.2.2.1, mul_inv_cancel]`. Conclude with `R.2.2.2.2.1 1 (one_mem _) τ`. Rewrite using `[R.2.2.2.1, hq2 τ, ← hkm τ, Matrix.mul_assoc, h2, Matrix.mul_one]`.

Rewrite using `[e]`. Conclude with `hq3 τ`.
-/
theorem exists_archIwasawa : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), IsFrameFam V ε fr → ∀ (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ g ∈ GinfC V, ∃ p ∈ PositivityTheory.ThKR.minPar D.sp.cm.sig V.gram X, ∃ κ : (∀ τ, Formalism.REAL.KG (ε τ)), g = p * GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.KInf.kInf θ V ε fr κ := by
  intro D θ hθ V ε fr hfr m X Y hW g hg
  have hcm := GlobalTheory.AdelicU.isCMExt_host D
  have R := (GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ V
  have hher := fun τ => GlobalTheory.SmoothForms.RealPts.gramAt_herm V τ
  have hmap : ∀ (τ : D.what₂.Tau) {A B : Matrix (Fin V.rank) (Fin m) D.host.E},
      (A.map (tauE D τ))ᴴ * gramAt D V τ * B.map (tauE D τ) =
        (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) A * V.gram * B).map (tauE D τ) := fun τ {A B} => by
    rw [show gramAt D V τ = V.gram.map (tauE D τ) from rfl, Matrix.map_mul, Matrix.map_mul, GlobalTheory.CompanionTheory.SiegelArch.conjT_map hcm]
  have hxx : ∀ τ, (X.map (tauE D τ))ᴴ * gramAt D V τ * X.map (tauE D τ) = 0 := fun τ => by
    rw [hmap, hW.xx]; simp
  have hxy : ∀ τ, (X.map (tauE D τ))ᴴ * gramAt D V τ * Y.map (tauE D τ) = 1 := fun τ => by
    rw [hmap, hW.xy, Matrix.map_one _ (map_zero _) (map_one _)]
  have hyx : ∀ τ, (Y.map (tauE D τ))ᴴ * gramAt D V τ * X.map (tauE D τ) = 1 := fun τ => by
    have h := congrArg conjTranspose (hxy τ)
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hher τ, conjTranspose_one] at h
    rw [Matrix.mul_assoc]
    exact h
  obtain ⟨w₀⟩ : Nonempty (NumberField.InfinitePlace D.host.F) := inferInstance
  obtain ⟨τ₀, -⟩ := (GlobalTheory.AdelicU.placeOf_bijective D).2 w₀
  have hQ : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Y * V.gram * X = 1 := by
    have h : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Y * V.gram * X).map (tauE D τ₀) =
        (1 : Matrix (Fin m) (Fin m) D.host.E).map (tauE D τ₀) := by
      rw [← hmap, hyx, Matrix.map_one _ (map_zero _) (map_one _)]
    exact Matrix.map_injective (tauE D τ₀).injective h
  have place : ∀ τ, ∃ (q : Matrix (Fin V.rank) (Fin V.rank) ℂ) (κ : Formalism.REAL.KG (ε τ)),
      infMat D.sp.cm.sig V.gram (θ τ) g = q * ((fr τ)⁻¹ * Formalism.REAL.toMK κ * fr τ) ∧
      ∃ B : Matrix (Fin m) (Fin m) ℂ, B.BlockTriangular id ∧ q * X.map (tauE D τ) = X.map (tauE D τ) * B := by
    intro τ
    have hG : (fr τ)ᴴ * Formalism.REAL.Jm (ε τ) * fr τ = gramAt D V τ := (hfr τ).2
    obtain ⟨hPd, hPJ⟩ := frame_majorant (e := ε τ) (hfr τ).1
    rw [hG] at hPJ
    obtain ⟨p, k, -, h2, h3, h4, B, hB, hpB⟩ := iwasawa_majorant V.rank m (gramAt D V τ) ((fr τ)ᴴ * fr τ) _ _ (hher τ)
      (GlobalTheory.SmoothForms.RealPts.gramAt_unit V τ) (hxx τ) (hxy τ) hPd hPJ _ (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V g τ)
    obtain ⟨κ, hκ⟩ := exists_KG_of_stab (e := ε τ) (hfr τ).1 (by rw [hG]; exact h2) h3
    exact ⟨p, κ, hκ ▸ h4, B, hB, hpB⟩
  choose q κ hq2 hq3 using place
  obtain ⟨hk, hkm⟩ := kInf_spec hθ hfr κ
  set k := GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.KInf.kInf θ V ε fr κ with hkdef
  refine ⟨g * k⁻¹, ?_, κ, (inv_mul_cancel_right g k).symm⟩
  refine mem_minPar_real hθ hQ (mul_mem hg (inv_mem hk)) fun τ => ?_
  have e : infMat D.sp.cm.sig V.gram (θ τ) (g * k⁻¹) = q τ := by
    have h2 : infMat D.sp.cm.sig V.gram (θ τ) k * infMat D.sp.cm.sig V.gram (θ τ) k⁻¹ = 1 := by
      rw [← R.2.2.2.1, mul_inv_cancel]
      exact R.2.2.2.2.1 1 (one_mem _) τ
    rw [R.2.2.2.1, hq2 τ, ← hkm τ, Matrix.mul_assoc, h2, Matrix.mul_one]
  rw [e]
  exact hq3 τ

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.ArchIwasawa
