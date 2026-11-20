import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.ExStabSt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.OrbRing
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.HformSmulRight
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.InclRAlgebraMap
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.StLamOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.LocalSum
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.StFix
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianDiagonalization.ExistsOrthogonalFamily

noncomputable section

namespace PI.VolStabSW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField Matrix Formalism.UG PI.VolStabSW.OrbR
open scoped TensorProduct

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `ha`. Assume the negation of the conclusion as `hn`. Establish `hli : LinearIndependent F ![(1 : E), a]`. Rewrite using `[LinearIndependent.pair_iff]`.

Introduce `p q hpq`. Distinguish the cases in `hq : q = 0`. Substitute `hq` using the available equality. Simplify using `only [zero_smul, add_zero] at hpq`. Conclude with `⟨by simpa using hpq, rfl⟩`.

It suffices to derive a contradiction. Apply `hn` to reduce the goal to its premises. Use `⟨-(p / q), ?_⟩` and prove the remaining obligations. Establish `e : q • a = -(p • (1 : E))` using `by linear_combination hpq`. Rewrite `e` using `[Algebra.smul_def, Algebra.smul_def, mul_one]`.

Establish `hq' : algebraMap F E q ≠ 0` using `by simpa using hq`. Rewrite using `[map_neg, map_div₀]`. Clear the denominators using the available nonvanishing facts. Take the linear combination `-e`. Establish `hcard : Fintype.card (Fin 2) = Module.finrank F E` using `by rw [h.2.2.1]; rfl`.

Set `b` to `basisOfLinearIndependentOfCardEqFinrank hli hcard`. Establish `hid : σ.toLinearMap = LinearMap.id`. Use `b.ext fun i => ?_` and prove the remaining obligations. Use `fin_cases i`. Simplify using `[b]`.

Simplify using `[b, ha]`. Take `⟨τ⟩` from `(inferInstance : Nonempty (E →+* ℂ))`. Establish `hreal : ComplexEmbedding.IsReal τ`. Rewrite using `[ComplexEmbedding.isReal_iff]`. Use extensionality with `x`.

Rewrite using `[ComplexEmbedding.conjugate_coe_eq]`. Establish `e1` using `h.2.2.2 τ x`. Establish `e2 : σ x = x`. Use `congrArg (fun f : E →ₗ[F] E => f x) hid` as an intermediate fact. Simplify using `using this`.

Rewrite `e1` using `[e2]`. Rewrite using `[starRingEnd_apply, ← e1]`. Establish `hc` using `h.2.1.isComplex (InfinitePlace.mk τ)`. Conclude with `(InfinitePlace.not_isComplex_iff_isReal.mpr ⟨τ, hreal, rfl⟩) hc`. Introduce and unpack `⟨b, rfl⟩`.

Conclude with `σ.commutes b`.
-/
theorem cm_fixed {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (a : E) : σ a = a ↔ a ∈ (algebraMap F E).range := by
  constructor
  · intro ha
    by_contra hn
    have hli : LinearIndependent F ![(1 : E), a] := by
      rw [LinearIndependent.pair_iff]
      intro p q hpq
      by_cases hq : q = 0
      · subst hq
        simp only [zero_smul, add_zero] at hpq
        exact ⟨by simpa using hpq, rfl⟩
      · exfalso
        apply hn
        refine ⟨-(p / q), ?_⟩
        have e : q • a = -(p • (1 : E)) := by linear_combination hpq
        rw [Algebra.smul_def, Algebra.smul_def, mul_one] at e
        have hq' : algebraMap F E q ≠ 0 := by simpa using hq
        rw [map_neg, map_div₀]
        field_simp
        linear_combination -e
    have hcard : Fintype.card (Fin 2) = Module.finrank F E := by rw [h.2.2.1]; rfl
    let b := basisOfLinearIndependentOfCardEqFinrank hli hcard
    have hid : σ.toLinearMap = LinearMap.id := by
      refine b.ext fun i => ?_
      fin_cases i
      · simp [b]
      · simp [b, ha]
    obtain ⟨τ⟩ := (inferInstance : Nonempty (E →+* ℂ))
    have hreal : ComplexEmbedding.IsReal τ := by
      rw [ComplexEmbedding.isReal_iff]
      ext x
      rw [ComplexEmbedding.conjugate_coe_eq]
      have e1 := h.2.2.2 τ x
      have e2 : σ x = x := by
        have := congrArg (fun f : E →ₗ[F] E => f x) hid
        simpa using this
      rw [e2] at e1
      rw [starRingEnd_apply, ← e1]
    have hc := h.2.1.isComplex (InfinitePlace.mk τ)
    exact (InfinitePlace.not_isComplex_iff_isReal.mpr ⟨τ, hreal, rfl⟩) hc
  · rintro ⟨b, rfl⟩; exact σ.commutes b

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM M J hJ _ _ a _ _ X0 hT hdet y hy`. Establish `h2 : Module.finrank F E = 2` using `hCM.2.2.1`. Establish `hinv : ∀ x, σ (σ x) = x`. Introduce `x`. Take `⟨τ⟩` from `(inferInstance : Nonempty (E →+* ℂ))`.

Apply `τ.injective` to reduce the goal to its premises. Rewrite using `[hCM.2.2.2, hCM.2.2.2, star_star]`. Establish `hfix` using `cm_fixed σ hCM`. Use `set T := gramE σ J X0 with hTdef`. Set `sE : E →+* E` to `σ`.

Establish `hTH : IsHerm sE T`. Use extensionality with `i j`. Conclude with `hT i j`. Establish `hh : PI.UnitaryGroupMassFormula.HermConj.IsHermForm sE (hform sE T)` using `{ add := fun x y z => by`. Rewrite using `[PIW.AdelicOrbitU.hform_eq_dot, PIW.AdelicOrbitU.hform_eq_dot, PIW.AdelicOrbitU.hform_eq_dot, mulVec_add, dotProduct_add]`.

Use `smul := fun x c y => PIW.AdelicOrbitU.hform_smul_right sE T c x y`. Use `herm := fun x y => (PIW.AdelicOrbitU.hform_conj sE T hinv hTH x y).symm }`. Take `⟨v, hvli, hvo⟩` from `PI.UnitaryGroupMassFormula.HermConj.exists_orthogonal_family sE a (Fin a → E) (by simp) (hform sE T) hh`. Use `set P : Matrix (Fin a) (Fin a) E := tM v with hP`. Establish `hPu : IsUnit P.det`.

Establish `h1 : IsUnit (Matrix.of v)` using `Matrix.linearIndependent_rows_iff_isUnit.mp hvli`. Establish `h2 : P = (Matrix.of v)ᵀ` using `rfl`. Rewrite using `[h2, det_transpose]`. Conclude with `(Matrix.isUnit_iff_isUnit_det _).mp h1`. Use `set D := cT sE P * T * P with hD`.

Establish `hDv : ∀ j k, hform sE T (v j) (v k) = D j k` using `fun j k => gram_tM sE T v j k`. Establish `hDoff : ∀ j k, j ≠ k → D j k = 0` using `fun j k hjk => by rw [← hDv]; exact hvo j k hjk`. Establish `hDdiag : D = Matrix.diagonal fun j => D j j`. Use extensionality with `j k`. Distinguish the cases in `hjk : j = k`.

Substitute `hjk` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[hDoff j k hjk, Matrix.diagonal_apply_ne _ hjk]`. Establish `hDdet : D.det ≠ 0`. Establish `hc : (cT sE P).det = sE P.det`.

Rewrite using `[cT, det_transpose, RingHom.map_det]`. Both sides reduce to the same expression. Rewrite using `[hD, det_mul, det_mul, hc]`. Use `mul_ne_zero (mul_ne_zero ?_ hdet) hPu.ne_zero` and prove the remaining obligations. Conclude with `(map_ne_zero sE).mpr hPu.ne_zero`.

Establish `hDne : ∀ j, D j j ≠ 0`. Introduce `j`. Rewrite `hDdet` using `[hDdiag, det_diagonal]`. Conclude with `Finset.prod_ne_zero_iff.mp hDdet j (Finset.mem_univ j)`. Establish `hDfix : ∀ j, σ (D j j) = D j j` using `fun j => by`.

Rewrite using `[← hDv]`. Conclude with `PIW.AdelicOrbitU.hform_conj sE T hinv hTH _ _`. Set `R` to `AF F`. Set `sS` to `sigR R σ`. Set `JS` to `JR (F := F) R J`.

Establish `hsS : ∀ z, sS (sS z) = z` using `(PIW.AdelicOrbitU.stFix F E σ h2 hfix R).1`. Establish `hJS : IsHerm sS JS` using `PIW.AdelicOrbitU.isHerm_JR R σ J hJ.1`. Establish `hJSd : IsUnit JS.det` using `PIW.AdelicOrbitU.isUnit_det_JR (F := F) R J hJ.2`. Establish `hcTmap : ∀ {p q : ℕ} (N : Matrix (Fin p) (Fin q) E), cT sS (N.map (inclR (F` using `F) R)) = (cT sE N).map (inclR (F := F) R) := by`. Introduce `p q N`.

Use extensionality with `i j`. Simplify using `only [cT, Matrix.map_apply, Matrix.transpose_apply]`. Conclude with `PIW.AdelicOrbitU.sigR_inclR (F := F) R σ _`. Use `set Xm : Matrix (Fin M) (Fin a) (R ⊗[F] E) := (tM X0).map (inclR (F := F) R) with hXm`. Use `set Pm : Matrix (Fin a) (Fin a) (R ⊗[F] E) := P.map (inclR (F := F) R) with hPm`.

Establish `hTg : cT sE (tM X0) * J * tM X0 = T`. Use extensionality with `i j`. Rewrite using `[← gram_tM]`. Both sides reduce to the same expression. Establish `hyg : cT sS (tM y) * JS * tM y = T.map (inclR (F` using `F) R) := by`.

Use extensionality with `i j`. Rewrite using `[← gram_tM]`. Conclude with `congrFun (congrFun hy i) j`. Set `x' : Fin a → Fin M → R ⊗[F] E` to `fun j r => (Xm * Pm) r j`. Set `y' : Fin a → Fin M → R ⊗[F] E` to `fun j r => (tM y * Pm) r j`.

Establish `hGx : ∀ j k, hform sS JS (x' j) (x' k) = inclR (F` using `F) R (D j k) := by`. Introduce `j k`. Rewrite using `[gram_tM]`. Establish `e : tM x' = Xm * Pm` using `rfl`. Rewrite using `[e, gram_mul, hXm, hPm, hcTmap, hcTmap]`.

Use `show ((cT sE P).map (inclR (F := F) R) * ((cT sE (tM X0)).map (inclR (F := F) R) * J.map (inclR (F := F) R) * (tM X0).map (inclR (F := F) R)) * P.map (inclR (F := F) R)) j k = _`. Rewrite using `[← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, hTg]`. Both sides reduce to the same expression. Establish `hGy : ∀ j k, hform sS JS (y' j) (y' k) = inclR (F` using `F) R (D j k) := by`. Introduce `j k`.

Rewrite using `[gram_tM]`. Establish `e : tM y' = tM y * Pm` using `rfl`. Rewrite using `[e, gram_mul, hyg, hPm, hcTmap, ← Matrix.map_mul, ← Matrix.map_mul]`. Both sides reduce to the same expression. Take `⟨g, hgU, hgx⟩` from `orb_orth sS JS hsS hJS hJSd a x' y' (fun j k hjk => by rw [hGx, hDoff j k hjk, map_zero]) (fun j k => by rw [hGx, hGy]) (fun j => by rw [hGx]; exact (isUnit_iff_ne_zero.mpr (hDne j)).map _) (fun j t => by`.

Take `⟨β, hβ⟩` from `(hfix _).mp (hDfix j)`. Establish `hβ0 : β ≠ 0`. Introduce and unpack `rfl; exact hDne j (by rw [← hβ, map_zero])`. Take `⟨lam, hlam, hu⟩` from `PIW.AdelicOrbitU.stLam F E σ h2 hfix R (PIW.AdelicOrbitU.stP F) t β hβ0`. Use `⟨lam, hlam, ?_⟩` and prove the remaining obligations.

Rewrite using `[hGx, ← hβ, PIW.AdelicOrbitU.inclR_algebraMap]`. Conclude with `hu)`. Establish `hmat : (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * Xm * Pm = tM y * Pm`. Use extensionality with `r j`. Rewrite using `[Matrix.mul_assoc]`.

Use `congrFun (hgx j) r` as an intermediate fact. Simplify `this` using `[x', y', Matrix.mul_apply, mulVec, dotProduct]`. Establish `hPmu : IsUnit Pm.det` using `by show IsUnit ((inclR (F := F) R).mapMatrix P).det`. Rewrite using `[← RingHom.map_det]`. Conclude with `hPu.map _`.

Establish `hmat2 : (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * Xm = tM y`. Use `congrArg (fun N => N * Pm⁻¹) hmat` as an intermediate fact. Simplify `this` using `only [Matrix.mul_nonsing_inv_cancel_right _ _ hPmu]`. Use `⟨(⟨g, hgU⟩ : HR (AF F) σ J), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`.

Use function extensionality and compare the values at `r`. Use `show ((g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ ratTup (AF F) X0 i) r = y i r`. Use `congrFun (congrFun hmat2 r) i` as an intermediate fact. Simplify `this` using `[Xm, tM, ratTup, Matrix.mul_apply, mulVec, dotProduct]`.
-/
theorem orbTup_holds : OrbTup := by
  intro F E _ _ _ _ _ σ hCM M J hJ _ _ a _ _ X0 hT hdet y hy
  have h2 : Module.finrank F E = 2 := hCM.2.2.1
  have hinv : ∀ x, σ (σ x) = x := by
    intro x
    obtain ⟨τ⟩ := (inferInstance : Nonempty (E →+* ℂ))
    apply τ.injective
    rw [hCM.2.2.2, hCM.2.2.2, star_star]
  have hfix := cm_fixed σ hCM
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

  let R := AF F
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
      obtain ⟨lam, hlam, hu⟩ := PIW.AdelicOrbitU.stLam F E σ h2 hfix R (PIW.AdelicOrbitU.stP F) t β hβ0
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
  refine ⟨(⟨g, hgU⟩ : HR (AF F) σ J), ?_⟩
  funext i
  funext r
  show ((g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ ratTup (AF F) X0 i) r = y i r
  have := congrFun (congrFun hmat2 r) i
  simpa [Xm, tM, ratTup, Matrix.mul_apply, mulVec, dotProduct] using this

end PI.VolStabSW
