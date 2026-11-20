import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsHermRingRat
import Formalism.SatakeDualWeyl.Statement
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HermitianBlockTriangular
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HermitianBlockDiagonal
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HermitianProjectionEq

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes in
/- English proof (translation)
Take `⟨_, _, _, hs⟩` from `h`. Set `t : E →+* ℂ` to `(IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom`. Apply `t.injective` to reduce the goal to its premises. Rewrite using `[hs, hs, star_star]`.
-/
private theorem sigma_sq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨_, _, _, hs⟩ := h
  let t : E →+* ℂ := (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom
  apply t.injective
  rw [hs, hs, star_star]

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes in
/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a e => simp [sigR, h]`. Consider the case `add a b ha hb => simp [ha, hb]`.
-/
private theorem sigR_sq {F E : Type} [Field F] [Field E] [Algebra F E] (A : Type) [CommRing A] [Algebra F A]
    {σ : E →ₐ[F] E} (h : ∀ x, σ (σ x) = x) (x : TensorProduct F A E) :
    sigR A σ (sigR A σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [sigR, h]
  | add a b ha hb => simp [ha, hb]

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes in
/- English proof (translation)
Simplify using `[sigR, inclR]`.
-/
private theorem sigR_incl {F E : Type} [Field F] [Field E] [Algebra F E] (A : Type) [CommRing A] [Algebra F A]
    (σ : E →ₐ[F] E) (e : E) : sigR A σ (inclR A e) = inclR A (σ e) := by
  simp [sigR, inclR]

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes in
/- English proof (translation)
Rewrite using `[Matrix.map_mul]`. Use `congr 1`.
-/
private theorem dual_map {F E : Type} [Field F] [Field E] [Algebra F E] (A : Type) [CommRing A] [Algebra F A]
    (σ : E →ₐ[F] E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (X : Matrix (Fin n) (Fin r) E) :
    (Formalism.UG.cT (↑σ : E →+* E) X * J).map (inclR A) =
      ((X.map (inclR A)).map (sigR A σ)).transpose * JR A J := by
  rw [Matrix.map_mul]
  congr 1

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n J r X Y hCM hH hW A _ _ _ p B hB hpX`. Take `⟨hXX, hYY, hXY, -⟩` from `hW`. Establish `hτ` using `sigR_sq A (sigma_sq hCM)`. Set `τ` to `Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR A σ`. Set `ι` to `Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (E := E) A`.

Set `JA` to `Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (F := F) A J`. Set `Xa` to `X.map ι`. Set `Ya` to `Y.map ι`. Set `Xd` to `(Formalism.UG.cT (↑σ : E →+* E) X * J).map ι`. Set `Yd` to `(Formalism.UG.cT (↑σ : E →+* E) Y * J).map ι`.

Set `g : Matrix (Fin n) (Fin n) (TensorProduct F A E)` to `↑(GlobalTheory.AdelicU.matHom A σ J p)`. Establish `hXd : Xd = (Xa.map τ).transpose * JA` using `dual_map A σ J X`. Establish `hYd : Yd = (Ya.map τ).transpose * JA` using `dual_map A σ J Y`. Establish `hJh : (JA.map τ).transpose = JA`. Use extensionality with `i j`.

Simplify using `only [JA, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR, Matrix.transpose_apply, Matrix.map_apply, τ]`. Rewrite using `[sigR_incl]`. Conclude with `congrArg _ (hH.1 i j)`. Establish `hJu : IsUnit JA.det`. Establish `h1 : JA.det = ι J.det` using `(RingHom.map_det ι J).symm`.

Rewrite using `[h1]`. Conclude with `(isUnit_iff_ne_zero.mpr hH.2).map ι`. Establish `hXX' : Xd * Xa = 0`. Simplify using `only [Xd, Xa]`. Rewrite using `[← Matrix.map_mul, hXX]`.

Simplify using the standard rewrite rules. Establish `hYY' : Yd * Ya = 0`. Simplify using `only [Yd, Ya]`. Rewrite using `[← Matrix.map_mul, hYY]`. Simplify using the standard rewrite rules.

Establish `hXY' : Xd * Ya = 1`. Simplify using `only [Xd, Ya]`. Rewrite using `[← Matrix.map_mul, hXY]`. Simplify using the standard rewrite rules. Establish `hgJ : (g.map τ).transpose * JA * g = JA` using `p.2`.

Take `⟨hYX, hYgX, hXg, hdiag⟩` from `UpperTheory.hermitian_block_triangular τ hτ JA g Xa Ya B Xd Yd hJh hXd hYd hXY' hgJ hB hpX`. Set `d : Fin r → TensorProduct F A E` to `fun i => (Yd * g * Xa) i i`. Set `e : Fin r → TensorProduct F A E` to `fun i => (Xd * g * Ya) i i`. Set `P` to `1 - Xa * Yd - Ya * Xd`. Set `M` to `GlobalTheory.CompanionTheory.KFin.leviMat σ J A X Y g`.

Establish `hM : M = (Xa * Matrix.diagonal d) * Yd + (Ya * Matrix.diagonal e) * Xd + P * g * P` using `rfl`. Establish `hdB : ∀ i, d i = B i i` using `fun i => by simp only [d, hYgX]`. Establish `hde : ∀ i, τ (e i) * d i = 1` using `fun i => by rw [hdB]; exact hdiag i`. Establish `hdu : ∀ i, IsUnit (d i)` using `fun i => IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact hde i)`. Take `⟨hu, hun, hmX, hmY⟩` from `UpperTheory.hermitian_block_diagonal τ hτ JA g P M Xa Ya (Xd * g * Ya) Xd Yd d e hJh hJu hXd hYd hXX' hYY' hXY' hgJ hXg hde rfl hM`.

Take `⟨⟨B', hB1, hB2, hB3⟩, hz⟩` from `UpperTheory.hermitian_projection_eq g P M Xa Ya B (Xd * g * Ya) Xd Yd d e hXX' hYY' hXY' hYX hB hpX hXg hdB hdu rfl hM hu`. Set `m : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA A σ J` to `⟨Matrix.nonsingInvUnit M hu, hun⟩`. Establish `hmv : (↑(GlobalTheory.AdelicU.matHom A σ J m) : Matrix (Fin n) (Fin n) (TensorProduct F A E)) = M` using `rfl`. Establish `hinv : (↑(GlobalTheory.AdelicU.matHom A σ J (m⁻¹ * p)) : Matrix (Fin n) (Fin n) (TensorProduct F A E)) = M⁻¹ * g`. Rewrite using `[map_mul, map_inv, Units.val_mul, Matrix.coe_units_inv, hmv]`.

Use `⟨m, rfl, ⟨d, hmX⟩, ⟨e, hmY⟩, ⟨B', hB1, hB2, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hinv]`. Conclude with `hB3`. Introduce `z hzz`. Rewrite using `[hinv]`.

Conclude with `hz z hzz`.
-/
theorem UpperTheory.Reformulated.B.Gka3.exists_levi :
    ∀ {F E : Type} [inst : Field F] [inst_1 : NumberField F] [inst_2 : Field E] [inst_3 : NumberField E]
      [inst_4 : Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ}
      {X Y : Matrix (Fin n) (Fin r) E},
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ →
        Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsHermND σ J →
          GlobalTheory.SiegelSet.IsWittFrame σ J X Y →
            ∀ (A : Type) [inst_5 : CommRing A] [inst_6 : Algebra F A] [TopologicalSpace A] (p : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA A σ J)
              (B : Matrix (Fin r) (Fin r) (TensorProduct F A E)),
              B.BlockTriangular id →
                (↑((GlobalTheory.AdelicU.matHom A σ J : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA A σ J → GL (Fin n) (TensorProduct F A E)) p) :
                                 Matrix (Fin n) (Fin n) (TensorProduct F A E)) *
                      X.map (⇑(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR A) : E → TensorProduct F A E) =
                    X.map (⇑(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR A) : E → TensorProduct F A E) * B →
                  ∃ (m : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA A σ J),
                    (↑((GlobalTheory.AdelicU.matHom A σ J : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA A σ J → GL (Fin n) (TensorProduct F A E)) m) :
                          Matrix (Fin n) (Fin n) (TensorProduct F A E)) =
                        GlobalTheory.CompanionTheory.KFin.leviMat σ J A X Y
                          (↑((GlobalTheory.AdelicU.matHom A σ J : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA A σ J → GL (Fin n) (TensorProduct F A E)) p) :
                            Matrix (Fin n) (Fin n) (TensorProduct F A E)) ∧
                      (∃ (d : Fin r → TensorProduct F A E),
                          (↑((GlobalTheory.AdelicU.matHom A σ J : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA A σ J → GL (Fin n) (TensorProduct F A E)) m) :
                                Matrix (Fin n) (Fin n) (TensorProduct F A E)) *
                              X.map (⇑(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR A) : E → TensorProduct F A E) =
                            X.map (⇑(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR A) : E → TensorProduct F A E) * Matrix.diagonal d) ∧
                        (∃ (d' : Fin r → TensorProduct F A E),
                            (↑((GlobalTheory.AdelicU.matHom A σ J : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA A σ J → GL (Fin n) (TensorProduct F A E))
                                               m) :
                                  Matrix (Fin n) (Fin n) (TensorProduct F A E)) *
                                Y.map (⇑(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR A) : E → TensorProduct F A E) =
                              Y.map (⇑(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR A) : E → TensorProduct F A E) * Matrix.diagonal d') ∧
                          (∃ (B' : Matrix (Fin r) (Fin r) (TensorProduct F A E)),
                              B'.BlockTriangular id ∧
                                (∀ (i : Fin r), B' i i = (1 : TensorProduct F A E)) ∧
                                  (↑((GlobalTheory.AdelicU.matHom A σ J :
                                                       Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA A σ J → GL (Fin n) (TensorProduct F A E))
                                                     (m⁻¹ * p)) :
                                        Matrix (Fin n) (Fin n) (TensorProduct F A E)) *
                                      X.map (⇑(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR A) : E → TensorProduct F A E) =
                                    X.map (⇑(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR A) : E → TensorProduct F A E) * B') ∧
                            ∀ (z : Fin n → TensorProduct F A E),
                              ((Formalism.UG.cT (↑σ : E →+* E) X * J).map
                                              (⇑(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR A) : E → TensorProduct F A E)).mulVec
                                          z =
                                  (0 : Fin r → TensorProduct F A E) →
                                ∃ (a : Fin r → TensorProduct F A E),
                                  ((↑((GlobalTheory.AdelicU.matHom A σ J :
                                                           Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA A σ J → GL (Fin n) (TensorProduct F A E))
                                                         (m⁻¹ * p)) :
                                                     Matrix (Fin n) (Fin n) (TensorProduct F A E)) -
                                                   (1 : Matrix (Fin n) (Fin n) (TensorProduct F A E))).mulVec
                                      z =
                                    (X.map (⇑(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR A) : E → TensorProduct F A E)).mulVec a := by
  intro F E _ _ _ _ _ σ n J r X Y hCM hH hW A _ _ _ p B hB hpX
  obtain ⟨hXX, hYY, hXY, -⟩ := hW
  have hτ := sigR_sq A (sigma_sq hCM)
  let τ := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR A σ
  let ι := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (E := E) A
  let JA := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (F := F) A J
  let Xa := X.map ι
  let Ya := Y.map ι
  let Xd := (Formalism.UG.cT (↑σ : E →+* E) X * J).map ι
  let Yd := (Formalism.UG.cT (↑σ : E →+* E) Y * J).map ι
  let g : Matrix (Fin n) (Fin n) (TensorProduct F A E) := ↑(GlobalTheory.AdelicU.matHom A σ J p)
  have hXd : Xd = (Xa.map τ).transpose * JA := dual_map A σ J X
  have hYd : Yd = (Ya.map τ).transpose * JA := dual_map A σ J Y
  have hJh : (JA.map τ).transpose = JA := by
    ext i j
    simp only [JA, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR, Matrix.transpose_apply, Matrix.map_apply, τ]
    rw [sigR_incl]
    exact congrArg _ (hH.1 i j)
  have hJu : IsUnit JA.det := by
    have h1 : JA.det = ι J.det := (RingHom.map_det ι J).symm
    rw [h1]
    exact (isUnit_iff_ne_zero.mpr hH.2).map ι
  have hXX' : Xd * Xa = 0 := by
    simp only [Xd, Xa]
    rw [← Matrix.map_mul, hXX]
    simp
  have hYY' : Yd * Ya = 0 := by
    simp only [Yd, Ya]
    rw [← Matrix.map_mul, hYY]
    simp
  have hXY' : Xd * Ya = 1 := by
    simp only [Xd, Ya]
    rw [← Matrix.map_mul, hXY]
    simp
  have hgJ : (g.map τ).transpose * JA * g = JA := p.2
  obtain ⟨hYX, hYgX, hXg, hdiag⟩ := UpperTheory.hermitian_block_triangular τ hτ JA g Xa Ya B Xd Yd hJh hXd hYd hXY' hgJ hB hpX
  let d : Fin r → TensorProduct F A E := fun i => (Yd * g * Xa) i i
  let e : Fin r → TensorProduct F A E := fun i => (Xd * g * Ya) i i
  let P := 1 - Xa * Yd - Ya * Xd
  let M := GlobalTheory.CompanionTheory.KFin.leviMat σ J A X Y g
  have hM : M = (Xa * Matrix.diagonal d) * Yd + (Ya * Matrix.diagonal e) * Xd + P * g * P := rfl
  have hdB : ∀ i, d i = B i i := fun i => by simp only [d, hYgX]
  have hde : ∀ i, τ (e i) * d i = 1 := fun i => by rw [hdB]; exact hdiag i
  have hdu : ∀ i, IsUnit (d i) := fun i => IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact hde i)
  obtain ⟨hu, hun, hmX, hmY⟩ := UpperTheory.hermitian_block_diagonal τ hτ JA g P M Xa Ya (Xd * g * Ya) Xd Yd d e hJh hJu hXd hYd
    hXX' hYY' hXY' hgJ hXg hde rfl hM
  obtain ⟨⟨B', hB1, hB2, hB3⟩, hz⟩ := UpperTheory.hermitian_projection_eq g P M Xa Ya B (Xd * g * Ya) Xd Yd d e hXX' hYY' hXY' hYX
    hB hpX hXg hdB hdu rfl hM hu
  let m : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA A σ J := ⟨Matrix.nonsingInvUnit M hu, hun⟩
  have hmv : (↑(GlobalTheory.AdelicU.matHom A σ J m) : Matrix (Fin n) (Fin n) (TensorProduct F A E)) = M := rfl
  have hinv : (↑(GlobalTheory.AdelicU.matHom A σ J (m⁻¹ * p)) : Matrix (Fin n) (Fin n) (TensorProduct F A E)) = M⁻¹ * g := by
    rw [map_mul, map_inv, Units.val_mul, Matrix.coe_units_inv, hmv]
  refine ⟨m, rfl, ⟨d, hmX⟩, ⟨e, hmY⟩, ⟨B', hB1, hB2, ?_⟩, ?_⟩
  · rw [hinv]
    exact hB3
  · intro z hzz
    rw [hinv]
    exact hz z hzz
