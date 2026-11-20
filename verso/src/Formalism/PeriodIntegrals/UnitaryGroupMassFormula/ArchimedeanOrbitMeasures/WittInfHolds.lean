import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.OrbRing
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.StLamOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.LocalSum
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.StFix
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.InclRAlgebraMap
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianDiagonalization.ExistsOrthogonalFamily
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.HaarUniqInfHolds

noncomputable section

namespace PI.AprimeInfWitt

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField Matrix Formalism.UG PI.VolStabSW.OrbR
open scoped TensorProduct

/- English proof (translation)
Use `set T := gramE σ J X0 with hTdef`. Set `sE : E →+* E` to `σ`. Establish `hTH : IsHerm sE T`. Use extensionality with `i j`. Conclude with `hT i j`.

Establish `hh : PI.UnitaryGroupMassFormula.HermConj.IsHermForm sE (hform sE T)` using `{ add := fun x y z => by`. Rewrite using `[PIW.AdelicOrbitU.hform_eq_dot, PIW.AdelicOrbitU.hform_eq_dot, PIW.AdelicOrbitU.hform_eq_dot, mulVec_add, dotProduct_add]`. Use `smul := fun x c y => PIW.AdelicOrbitU.hform_smul_right sE T c x y`. Use `herm := fun x y => (PIW.AdelicOrbitU.hform_conj sE T hinv hTH x y).symm }`. Take `⟨v, hvli, hvo⟩` from `PI.UnitaryGroupMassFormula.HermConj.exists_orthogonal_family sE a (Fin a → E) (by simp) (hform sE T) hh`.

Use `set P : Matrix (Fin a) (Fin a) E := tM v with hP`. Establish `hPu : IsUnit P.det`. Establish `h1 : IsUnit (Matrix.of v)` using `Matrix.linearIndependent_rows_iff_isUnit.mp hvli`. Establish `h2 : P = (Matrix.of v)ᵀ` using `rfl`. Rewrite using `[h2, det_transpose]`.

Conclude with `(Matrix.isUnit_iff_isUnit_det _).mp h1`. Use `set D := cT sE P * T * P with hD`. Establish `hDv : ∀ j k, hform sE T (v j) (v k) = D j k` using `fun j k => gram_tM sE T v j k`. Establish `hDoff : ∀ j k, j ≠ k → D j k = 0` using `fun j k hjk => by rw [← hDv]; exact hvo j k hjk`. Establish `hDdiag : D = Matrix.diagonal fun j => D j j`.

Use extensionality with `j k`. Distinguish the cases in `hjk : j = k`. Substitute `hjk` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[hDoff j k hjk, Matrix.diagonal_apply_ne _ hjk]`.

Establish `hDdet : D.det ≠ 0`. Establish `hc : (cT sE P).det = sE P.det`. Rewrite using `[cT, det_transpose, RingHom.map_det]`. Both sides reduce to the same expression. Rewrite using `[hD, det_mul, det_mul, hc]`.

Use `mul_ne_zero (mul_ne_zero ?_ hdet) hPu.ne_zero` and prove the remaining obligations. Conclude with `(map_ne_zero sE).mpr hPu.ne_zero`. Establish `hDne : ∀ j, D j j ≠ 0`. Introduce `j`. Rewrite `hDdet` using `[hDdiag, det_diagonal]`.

Conclude with `Finset.prod_ne_zero_iff.mp hDdet j (Finset.mem_univ j)`. Establish `hDfix : ∀ j, σ (D j j) = D j j` using `fun j => by`. Rewrite using `[← hDv]`. Conclude with `PIW.AdelicOrbitU.hform_conj sE T hinv hTH _ _`. Set `sS` to `sigR R σ`.

Set `JS` to `JR (F := F) R J`. Establish `hsS : ∀ z, sS (sS z) = z` using `(PIW.AdelicOrbitU.stFix F E σ h2 hfix R).1`. Establish `hJS : IsHerm sS JS` using `PIW.AdelicOrbitU.isHerm_JR R σ J hJ.1`. Establish `hJSd : IsUnit JS.det` using `PIW.AdelicOrbitU.isUnit_det_JR (F := F) R J hJ.2`. Establish `hcTmap : ∀ {p q : ℕ} (N : Matrix (Fin p) (Fin q) E), cT sS (N.map (inclR (F` using `F) R)) = (cT sE N).map (inclR (F := F) R) := by`.

Introduce `p q N`. Use extensionality with `i j`. Simplify using `only [cT, Matrix.map_apply, Matrix.transpose_apply]`. Conclude with `PIW.AdelicOrbitU.sigR_inclR (F := F) R σ _`. Use `set Xm : Matrix (Fin M) (Fin a) (R ⊗[F] E) := (tM X0).map (inclR (F := F) R) with hXm`.

Use `set Pm : Matrix (Fin a) (Fin a) (R ⊗[F] E) := P.map (inclR (F := F) R) with hPm`. Establish `hTg : cT sE (tM X0) * J * tM X0 = T`. Use extensionality with `i j`. Rewrite using `[← gram_tM]`. Both sides reduce to the same expression.

Establish `hyg : cT sS (tM y) * JS * tM y = T.map (inclR (F` using `F) R) := by`. Use extensionality with `i j`. Rewrite using `[← gram_tM]`. Conclude with `congrFun (congrFun hy i) j`. Set `x' : Fin a → Fin M → R ⊗[F] E` to `fun j r => (Xm * Pm) r j`.

Set `y' : Fin a → Fin M → R ⊗[F] E` to `fun j r => (tM y * Pm) r j`. Establish `hGx : ∀ j k, hform sS JS (x' j) (x' k) = inclR (F` using `F) R (D j k) := by`. Introduce `j k`. Rewrite using `[gram_tM]`. Establish `e : tM x' = Xm * Pm` using `rfl`.

Rewrite using `[e, gram_mul, hXm, hPm, hcTmap, hcTmap]`. Use `show ((cT sE P).map (inclR (F := F) R) * ((cT sE (tM X0)).map (inclR (F := F) R) * J.map (inclR (F := F) R) * (tM X0).map (inclR (F := F) R)) * P.map (inclR (F := F) R)) j k = _`. Rewrite using `[← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, hTg]`. Both sides reduce to the same expression. Establish `hGy : ∀ j k, hform sS JS (y' j) (y' k) = inclR (F` using `F) R (D j k) := by`.

Introduce `j k`. Rewrite using `[gram_tM]`. Establish `e : tM y' = tM y * Pm` using `rfl`. Rewrite using `[e, gram_mul, hyg, hPm, hcTmap, ← Matrix.map_mul, ← Matrix.map_mul]`. Both sides reduce to the same expression.

Take `⟨g, hgU, hgx⟩` from `orb_orth sS JS hsS hJS hJSd a x' y' (fun j k hjk => by rw [hGx, hDoff j k hjk, map_zero]) (fun j k => by rw [hGx, hGy]) (fun j => by rw [hGx]; exact (isUnit_iff_ne_zero.mpr (hDne j)).map _) (fun j t => by`. Take `⟨β, hβ⟩` from `(hfix _).mp (hDfix j)`. Establish `hβ0 : β ≠ 0`. Introduce and unpack `rfl; exact hDne j (by rw [← hβ, map_zero])`. Take `⟨lam, hlam, hu⟩` from `PIW.AdelicOrbitU.stLam F E σ h2 hfix R hU t β hβ0`.

Use `⟨lam, hlam, ?_⟩` and prove the remaining obligations. Rewrite using `[hGx, ← hβ, PIW.AdelicOrbitU.inclR_algebraMap]`. Conclude with `hu)`. Establish `hmat : (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * Xm * Pm = tM y * Pm`. Use extensionality with `r j`.

Rewrite using `[Matrix.mul_assoc]`. Use `congrFun (hgx j) r` as an intermediate fact. Simplify `this` using `[x', y', Matrix.mul_apply, mulVec, dotProduct]`. Establish `hPmu : IsUnit Pm.det` using `by show IsUnit ((inclR (F := F) R).mapMatrix P).det`. Rewrite using `[← RingHom.map_det]`.

Conclude with `hPu.map _`. Establish `hmat2 : (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * Xm = tM y`. Use `congrArg (fun N => N * Pm⁻¹) hmat` as an intermediate fact. Simplify `this` using `only [Matrix.mul_nonsing_inv_cancel_right _ _ hPmu]`. Use `⟨(⟨g, hgU⟩ : HR R σ J), ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `i`. Use function extensionality and compare the values at `r`. Use `show ((g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ ratTup (F := F) R X0 i) r = y i r`. Use `congrFun (congrFun hmat2 r) i` as an intermediate fact. Simplify `this` using `[Xm, tM, ratTup, Matrix.mul_apply, mulVec, dotProduct]`.
-/
theorem witt_R {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h2 : Module.finrank F E = 2) (hfix : ∀ a : E, σ a = a ↔ a ∈ (algebraMap F E).range)
    (hinv : ∀ x, σ (σ x) = x) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) {a : ℕ}
    (X0 : Fin a → Fin M → E) (hT : ∀ i j, σ (gramE σ J X0 j i) = gramE σ J X0 i j)
    (hdet : (gramE σ J X0).det ≠ 0) (R : Type) [CommRing R] [Algebra F R]
    (hU : PIW.AdelicOrbitU.UnitChoice R) (y : Fin a → Fin M → R ⊗[F] E)
    (hy : gramR R σ J y = (gramE σ J X0).map (inclR R)) :
    ∃ g : HA R σ J, g • ratTup (F := F) R X0 = y := by
  set T := gramE σ J X0 with hTdef
  let sE : E →+* E := σ
  have hTH : IsHerm sE T := by
    ext i j; exact hT i j
  have hh : PI.UnitaryGroupMassFormula.HermConj.IsHermForm sE (hform sE T) :=
    { add := fun x y z => by
        rw [PIW.AdelicOrbitU.hform_eq_dot, PIW.AdelicOrbitU.hform_eq_dot,
          PIW.AdelicOrbitU.hform_eq_dot, mulVec_add, dotProduct_add]
      smul := fun x c y => PIW.AdelicOrbitU.hform_smul_right sE T c x y
      herm := fun x y => (PIW.AdelicOrbitU.hform_conj sE T hinv hTH x y).symm }
  obtain ⟨v, hvli, hvo⟩ := PI.UnitaryGroupMassFormula.HermConj.exists_orthogonal_family sE a (Fin a → E)
    (by simp) (hform sE T) hh
  set P : Matrix (Fin a) (Fin a) E := tM v with hP
  have hPu : IsUnit P.det := by
    have h1 : IsUnit (Matrix.of v) := Matrix.linearIndependent_rows_iff_isUnit.mp hvli
    have h2 : P = (Matrix.of v)ᵀ := rfl
    rw [h2, det_transpose]
    exact (Matrix.isUnit_iff_isUnit_det _).mp h1
  set D := cT sE P * T * P with hD
  have hDv : ∀ j k, hform sE T (v j) (v k) = D j k := fun j k => gram_tM sE T v j k
  have hDoff : ∀ j k, j ≠ k → D j k = 0 := fun j k hjk => by rw [← hDv]; exact hvo j k hjk
  have hDdiag : D = Matrix.diagonal fun j => D j j := by
    ext j k
    by_cases hjk : j = k
    · subst hjk; simp
    · rw [hDoff j k hjk, Matrix.diagonal_apply_ne _ hjk]
  have hDdet : D.det ≠ 0 := by
    have hc : (cT sE P).det = sE P.det := by
      rw [cT, det_transpose, RingHom.map_det]; rfl
    rw [hD, det_mul, det_mul, hc]
    refine mul_ne_zero (mul_ne_zero ?_ hdet) hPu.ne_zero
    exact (map_ne_zero sE).mpr hPu.ne_zero
  have hDne : ∀ j, D j j ≠ 0 := by
    intro j
    rw [hDdiag, det_diagonal] at hDdet
    exact Finset.prod_ne_zero_iff.mp hDdet j (Finset.mem_univ j)
  have hDfix : ∀ j, σ (D j j) = D j j := fun j => by
    rw [← hDv]; exact PIW.AdelicOrbitU.hform_conj sE T hinv hTH _ _

  let sS := sigR R σ
  let JS := JR (F := F) R J
  have hsS : ∀ z, sS (sS z) = z := (PIW.AdelicOrbitU.stFix F E σ h2 hfix R).1
  have hJS : IsHerm sS JS := PIW.AdelicOrbitU.isHerm_JR R σ J hJ.1
  have hJSd : IsUnit JS.det := PIW.AdelicOrbitU.isUnit_det_JR (F := F) R J hJ.2
  have hcTmap : ∀ {p q : ℕ} (N : Matrix (Fin p) (Fin q) E),
      cT sS (N.map (inclR (F := F) R)) = (cT sE N).map (inclR (F := F) R) := by
    intro p q N; ext i j
    simp only [cT, Matrix.map_apply, Matrix.transpose_apply]
    exact PIW.AdelicOrbitU.sigR_inclR (F := F) R σ _
  set Xm : Matrix (Fin M) (Fin a) (R ⊗[F] E) := (tM X0).map (inclR (F := F) R) with hXm
  set Pm : Matrix (Fin a) (Fin a) (R ⊗[F] E) := P.map (inclR (F := F) R) with hPm
  have hTg : cT sE (tM X0) * J * tM X0 = T := by
    ext i j; rw [← gram_tM]; rfl
  have hyg : cT sS (tM y) * JS * tM y = T.map (inclR (F := F) R) := by
    ext i j; rw [← gram_tM]; exact congrFun (congrFun hy i) j
  let x' : Fin a → Fin M → R ⊗[F] E := fun j r => (Xm * Pm) r j
  let y' : Fin a → Fin M → R ⊗[F] E := fun j r => (tM y * Pm) r j
  have hGx : ∀ j k, hform sS JS (x' j) (x' k) = inclR (F := F) R (D j k) := by
    intro j k
    rw [gram_tM]
    have e : tM x' = Xm * Pm := rfl
    rw [e, gram_mul, hXm, hPm, hcTmap, hcTmap]
    show ((cT sE P).map (inclR (F := F) R) * ((cT sE (tM X0)).map (inclR (F := F) R) * J.map (inclR (F := F) R) *
      (tM X0).map (inclR (F := F) R)) * P.map (inclR (F := F) R)) j k = _
    rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, hTg]
    rfl
  have hGy : ∀ j k, hform sS JS (y' j) (y' k) = inclR (F := F) R (D j k) := by
    intro j k
    rw [gram_tM]
    have e : tM y' = tM y * Pm := rfl
    rw [e, gram_mul, hyg, hPm, hcTmap, ← Matrix.map_mul, ← Matrix.map_mul]
    rfl
  obtain ⟨g, hgU, hgx⟩ := orb_orth sS JS hsS hJS hJSd a x' y'
    (fun j k hjk => by rw [hGx, hDoff j k hjk, map_zero])
    (fun j k => by rw [hGx, hGy])
    (fun j => by rw [hGx]; exact (isUnit_iff_ne_zero.mpr (hDne j)).map _)
    (fun j t => by
      obtain ⟨β, hβ⟩ := (hfix _).mp (hDfix j)
      have hβ0 : β ≠ 0 := by
        rintro rfl; exact hDne j (by rw [← hβ, map_zero])
      obtain ⟨lam, hlam, hu⟩ := PIW.AdelicOrbitU.stLam F E σ h2 hfix R hU t β hβ0
      refine ⟨lam, hlam, ?_⟩
      rw [hGx, ← hβ, PIW.AdelicOrbitU.inclR_algebraMap]
      exact hu)
  have hmat : (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * Xm * Pm = tM y * Pm := by
    ext r j
    rw [Matrix.mul_assoc]
    have := congrFun (hgx j) r
    simpa [x', y', Matrix.mul_apply, mulVec, dotProduct] using this
  have hPmu : IsUnit Pm.det := by
    show IsUnit ((inclR (F := F) R).mapMatrix P).det
    rw [← RingHom.map_det]; exact hPu.map _
  have hmat2 : (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * Xm = tM y := by
    have := congrArg (fun N => N * Pm⁻¹) hmat
    simpa only [Matrix.mul_nonsing_inv_cancel_right _ _ hPmu] using this
  refine ⟨(⟨g, hgU⟩ : HR R σ J), ?_⟩
  funext i
  funext r
  show ((g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ ratTup (F := F) R X0 i) r = y i r
  have := congrFun (congrFun hmat2 r) i
  simpa [Xm, tM, ratTup, Matrix.mul_apply, mulVec, dotProduct] using this

end PI.AprimeInfWitt

namespace PI.AprimeInfW

open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

/- English proof (translation)
Introduce `D X u' ψ hT μinf νinf fibInf hP y hy`. Establish `h2 : Module.finrank X.B.I.F X.B.I.E = 2` using `X.B.I.cm.deg2`. Establish `hfix : ∀ a : X.B.I.E, X.B.I.cm.sig a = a ↔ a ∈ (algebraMap X.B.I.F X.B.I.E).range` using `fun a => X.B.I.cm.fixed a`. Establish `hinv : ∀ x, X.B.I.cm.sig (X.B.I.cm.sig x) = x` using `fun x => star_star x`. Establish `hJ : IsHermND X.B.I.cm.sig X.B.I.J`.

Use `⟨fun i j => ?_, X.B.I.J_det⟩` and prove the remaining obligations. Use `congrFun (congrFun X.B.I.J_herm i) j` as an intermediate fact. Simplify using `only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply] at this`. Conclude with `this`. Establish `hdet` using `detNZ_holds X u' ψ hT μinf νinf fibInf hP`.

Establish `hU : PIW.AdelicOrbitU.UnitChoice (Ainf X.B.I.F)` using `PIW.AdelicOrbitU.uc_pi (fun v : NumberField.InfinitePlace X.B.I.F => v.Completion)`. Establish `hyG : gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J y = (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (Ainf X.B.I.F))` using `Set.mem_singleton_iff.1 (Set.mem_preimage.1 hy.1)`. Take `⟨g, hg⟩` from `PI.AprimeInfWitt.witt_R X.B.I.cm.sig h2 hfix hinv X.B.I.J hJ (tupH (frameOf X u')) hT hdet (Ainf X.B.I.F) hU y hyG`. Conclude with `⟨g, hg⟩`.
-/
theorem wittInf_holds : WittInf := by
  intro D X u' ψ hT μinf νinf fibInf hP y hy
  have h2 : Module.finrank X.B.I.F X.B.I.E = 2 := X.B.I.cm.deg2
  have hfix : ∀ a : X.B.I.E, X.B.I.cm.sig a = a ↔ a ∈ (algebraMap X.B.I.F X.B.I.E).range :=
    fun a => X.B.I.cm.fixed a
  have hinv : ∀ x, X.B.I.cm.sig (X.B.I.cm.sig x) = x := fun x => star_star x
  have hJ : IsHermND X.B.I.cm.sig X.B.I.J := by
    refine ⟨fun i j => ?_, X.B.I.J_det⟩
    have := congrFun (congrFun X.B.I.J_herm i) j
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply] at this
    exact this
  have hdet := detNZ_holds X u' ψ hT μinf νinf fibInf hP
  have hU : PIW.AdelicOrbitU.UnitChoice (Ainf X.B.I.F) :=
    PIW.AdelicOrbitU.uc_pi (fun v : NumberField.InfinitePlace X.B.I.F => v.Completion)
  have hyG : gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J y =
      (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (Ainf X.B.I.F)) :=
    Set.mem_singleton_iff.1 (Set.mem_preimage.1 hy.1)
  obtain ⟨g, hg⟩ := PI.AprimeInfWitt.witt_R X.B.I.cm.sig h2 hfix hinv X.B.I.J hJ (tupH (frameOf X u')) hT hdet
    (Ainf X.B.I.F) hU y hyG
  exact ⟨g, hg⟩

end PI.AprimeInfW
