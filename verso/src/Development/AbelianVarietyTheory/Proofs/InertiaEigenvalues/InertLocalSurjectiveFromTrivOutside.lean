import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProdRecSatakeLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteInertHeckeSupportCosets
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertSatakeParametersEqOfIso
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDoubleCosetFiniteLeftCosets
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMaxCompactOfTrivOutsideLocalIntegral
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDoubleCosetsDefiniteUnitaryMaximalLevelStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open TensorProduct

namespace GlobalTheory.InertSurj

/- English proof (translation)
Set `b : Module.Basis (Fin 2) (maximalRealSubfield L) L` to `Module.finBasisOfFinrankEq _ _ (Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield L) L)`. Take `⟨a, c, h⟩` from `GlobalTheory.InertUmax.tensor_decomp b m`. Use `⟨b 0 ⊗ₜ[maximalRealSubfield L] GlobalTheory.InertUmax.sgl L v a + b 1 ⊗ₜ[maximalRealSubfield L] GlobalTheory.InertUmax.sgl L v c, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.sgl_same, GlobalTheory.InertUmax.sgl_same, h]`. Introduce `u hu`.

Rewrite using `[map_add, GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.sgl_ne L v a hu, GlobalTheory.InertUmax.sgl_ne L v c hu, tmul_zero, tmul_zero, add_zero]`.
-/
theorem exists_supported (L : Type) [Field L] [NumberField L] [IsCMField L]
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (m : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L)) :
    ∃ z : AL L, compAt L v z = m ∧ ∀ u, u ≠ v → compAt L u z = 0 := by
  let b : Module.Basis (Fin 2) (maximalRealSubfield L) L := Module.finBasisOfFinrankEq _ _
    (Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield L) L)
  obtain ⟨a, c, h⟩ := GlobalTheory.InertUmax.tensor_decomp b m
  refine ⟨b 0 ⊗ₜ[maximalRealSubfield L] GlobalTheory.InertUmax.sgl L v a +
    b 1 ⊗ₜ[maximalRealSubfield L] GlobalTheory.InertUmax.sgl L v c, ?_, ?_⟩
  · rw [map_add, GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.sgl_same,
      GlobalTheory.InertUmax.sgl_same, h]
  · intro u hu
    rw [map_add, GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.sgl_ne L v a hu,
      GlobalTheory.InertUmax.sgl_ne L v c hu, tmul_zero, tmul_zero, add_zero]

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b`. Rewrite using `[GlobalTheory.InertUmax.compAt_tmul]`. Simplify using `[conjAL, Formalism.UG.sigR, Algebra.TensorProduct.map_tmul, GlobalTheory.InertUmax.compAt_tmul]`.

Consider the case `add a b ha hb => simp only [map_add, ha, hb]`.
-/
theorem compAt_conjAL (L : Type) [Field L] [NumberField L] [IsCMField L]
    (u : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (z : AL L) :
    compAt L u (conjAL L z) = Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom
      (u.adicCompletion (maximalRealSubfield L)) (compAt L u z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [GlobalTheory.InertUmax.compAt_tmul]
    simp [conjAL, Formalism.UG.sigR, Algebra.TensorProduct.map_tmul, GlobalTheory.InertUmax.compAt_tmul]
  | add a b ha hb => simp only [map_add, ha, hb]

/- English proof (translation)
Introduce `L _ _ _ n v w Dv y hy`. Set `sig` to `Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom (v.adicCompletion (maximalRealSubfield L))`. Set `eS : w.adicCompletion L →+* L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L)` to `Dv.e.symm.toRingHom`. Establish `hcomm : ∀ a, sig (eS a) = eS (Dv.σw a)`. Introduce `a`.

Apply `Dv.e.injective` to reduce the goal to its premises. Establish `h` using `Dv.comm (eS a)`. Simplify using `only [eS, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply] at h ⊢`. Conclude with `h`. Set `Pm : Matrix (Fin n) (Fin n) (w.adicCompletion L)` to `(Dv.P : Matrix (Fin n) (Fin n) _)`.

Set `Qm : Matrix (Fin n) (Fin n) (w.adicCompletion L)` to `((Dv.P⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _)`. Set `Ym : Matrix (Fin n) (Fin n) (w.adicCompletion L)` to `(y : Matrix (Fin n) (Fin n) _)`. Establish `hPQ : Pm * Qm = 1` using `by simp [Pm, Qm]`. Establish `hy' : Formalism.UG.cT Dv.σw Ym * Formalism.UG.antiJ (w.adicCompletion L) n * Ym = Formalism.UG.antiJ (w.adicCompletion L) n` using `hy`. Set `X` to `Pm * Ym * Qm`.

Establish `hX : Formalism.UG.cT Dv.σw X * X = 1`. Establish `hP` using `Dv.Panti`. Express the relevant statement in the definitionally equal form `Formalism.UG.cT Dv.σw Pm * Pm = _ at hP`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [X, Formalism.UG.cT_mul, Matrix.mul_assoc]`.

Use `_ = Formalism.UG.cT Dv.σw Qm * (Formalism.UG.cT Dv.σw Pm * Pm) * Qm := by rw [hP, hy']`. Use `_ = Formalism.UG.cT Dv.σw (Pm * Qm) * (Pm * Qm) := by`. Simplify using `only [Formalism.UG.cT_mul, Matrix.mul_assoc]`. Use `_ = 1 := by rw [hPQ, Formalism.UG.cT_one, Matrix.one_mul]`. Establish `hX' : X * Formalism.UG.cT Dv.σw X = 1` using `mul_eq_one_comm.mp hX`.

Set `M` to `X.map eS`. Establish `hMc : conjT sig M = (Formalism.UG.cT Dv.σw X).map eS`. Use extensionality with `i j`. Simplify using `[M, conjT, Formalism.UG.cT, hcomm]`. Establish `hM : M * conjT sig M = 1`.

Rewrite using `[hMc]`. Express the relevant statement in the definitionally equal form `X.map eS * (Formalism.UG.cT Dv.σw X).map eS = 1`. Rewrite using `[← Matrix.map_mul, hX', Matrix.map_one _ (map_zero _) (map_one _)]`. Use `choose lift hlv hlw using GlobalTheory.InertSurj.exists_supported L v`. Set `E : AL L` to `(1 : L) ⊗ₜ[maximalRealSubfield L] GlobalTheory.InertUmax.sgl L v 1`.

Establish `hEv : compAt L v E = 1`. Rewrite using `[GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.sgl_same]`. Both sides reduce to the same expression. Establish `hEw : ∀ u, u ≠ v → compAt L u E = 0`. Introduce `u hu`.

Rewrite using `[GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.sgl_ne L v 1 hu, tmul_zero]`. Set `Z : Matrix (Fin n) (Fin n) (AL L)` to `M.map lift + (1 - E) • (1 : Matrix (Fin n) (Fin n) (AL L))`. Establish `hZv : Z.map (compAt L v) = M`. Use extensionality with `i j`. Simplify using `only [Z, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul, map_sub, map_one, hEv, hlv, sub_self, zero_mul, add_zero]`.

Establish `hZw : ∀ u, u ≠ v → Z.map (compAt L u) = 1`. Introduce `u hu`. Use extensionality with `i j`. Simplify using `only [Z, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul, map_sub, map_one, hEw u hu, hlw _ u hu, sub_zero, one_mul, zero_add]`. Rewrite using `[Matrix.one_apply, Matrix.one_apply]`.

Apply the tactic sequence `split_ifs <;> simp`. Establish `hZconj : ∀ u, (conjT (conjAL L) Z).map (compAt L u) = conjT (Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom (u.adicCompletion (maximalRealSubfield L))) (Z.map (compAt L u))`. Introduce `u`. Use extensionality with `i j`. Simplify using `[conjT, GlobalTheory.InertSurj.compAt_conjAL]`.

Establish `hZZ : Z * conjT (conjAL L) Z = 1`. Use extensionality with `i j`. Rewrite using `[← sub_eq_zero]`. Apply `GlobalTheory.InertUmax.eq_zero_of_compAt` to reduce the goal to its premises. Introduce `u`.

Establish `key : (Z * conjT (conjAL L) Z).map (compAt L u) = 1`. Rewrite using `[Matrix.map_mul, hZconj]`. Break down `eq_or_ne u v with rfl | hu` into its components or cases. Rewrite using `[hZv]`. Conclude with `hM`.

Rewrite using `[hZw u hu, conjT_one, Matrix.one_mul]`. Establish `h1` using `congrFun (congrFun key i) j`. Establish `h2` using `congrFun (congrFun (Matrix.map_one (compAt L u) (map_zero _) (map_one _)) i) j`. Simplify using `only [Matrix.map_apply] at h1 h2`. Rewrite using `[map_sub, h1, h2, sub_self]`.

Establish `hZZ' : conjT (conjAL L) Z * Z = 1` using `mul_eq_one_comm.mp hZZ`. Set `g : GL (Fin n) (AL L)` to `⟨Z, conjT (conjAL L) Z, hZZ, hZZ'⟩`. Establish `hg : g ∈ ReciprocityTheory.Aut.GA L n` using `hZZ`. Use `⟨⟨g, hg⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `u hu`.

Conclude with `hZw u (by simpa using hu)`. Establish `hb : Formalism.UG.bc (n` using `Fin n) (Dv.e : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L) →+* w.adicCompletion L) (Matrix.GeneralLinearGroup.map (compAt L v) (((⟨g, hg⟩ : GAf L n)) : GL (Fin n) (AL L))) = Dv.P * y * Dv.P⁻¹ := by`. Apply `Units.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(Z.map (compAt L v)).map _ = X`. Rewrite using `[hZv]`.

Use extensionality with `i j`. Simplify using `[M, eS]`. Unfold `InertDatum.loc`. Rewrite using `[hb]`. Use `group`.
-/
theorem loc_surj : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (y : GL (Fin n) (w.adicCompletion L)), y ∈ Formalism.UG.GU Dv.σw n → ∃ x : GAf L n, TrivOutside {v} x ∧ Dv.loc x = y := by
  intro L _ _ _ n v w Dv y hy
  classical
  let sig := Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom (v.adicCompletion (maximalRealSubfield L))
  let eS : w.adicCompletion L →+* L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L) :=
    Dv.e.symm.toRingHom
  have hcomm : ∀ a, sig (eS a) = eS (Dv.σw a) := by
    intro a
    apply Dv.e.injective
    have h := Dv.comm (eS a)
    simp only [eS, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply] at h ⊢
    exact h
  let Pm : Matrix (Fin n) (Fin n) (w.adicCompletion L) := (Dv.P : Matrix (Fin n) (Fin n) _)
  let Qm : Matrix (Fin n) (Fin n) (w.adicCompletion L) := ((Dv.P⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _)
  let Ym : Matrix (Fin n) (Fin n) (w.adicCompletion L) := (y : Matrix (Fin n) (Fin n) _)
  have hPQ : Pm * Qm = 1 := by simp [Pm, Qm]
  have hy' : Formalism.UG.cT Dv.σw Ym * Formalism.UG.antiJ (w.adicCompletion L) n * Ym =
      Formalism.UG.antiJ (w.adicCompletion L) n := hy
  let X := Pm * Ym * Qm
  have hX : Formalism.UG.cT Dv.σw X * X = 1 := by
    have hP := Dv.Panti
    change Formalism.UG.cT Dv.σw Pm * Pm = _ at hP
    calc Formalism.UG.cT Dv.σw X * X
        = Formalism.UG.cT Dv.σw Qm * (Formalism.UG.cT Dv.σw Ym * (Formalism.UG.cT Dv.σw Pm * Pm) * Ym) * Qm := by
          simp only [X, Formalism.UG.cT_mul, Matrix.mul_assoc]
      _ = Formalism.UG.cT Dv.σw Qm * (Formalism.UG.cT Dv.σw Pm * Pm) * Qm := by rw [hP, hy']
      _ = Formalism.UG.cT Dv.σw (Pm * Qm) * (Pm * Qm) := by
          simp only [Formalism.UG.cT_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hPQ, Formalism.UG.cT_one, Matrix.one_mul]
  have hX' : X * Formalism.UG.cT Dv.σw X = 1 := mul_eq_one_comm.mp hX
  let M := X.map eS
  have hMc : conjT sig M = (Formalism.UG.cT Dv.σw X).map eS := by
    ext i j
    simp [M, conjT, Formalism.UG.cT, hcomm]
  have hM : M * conjT sig M = 1 := by
    rw [hMc]
    change X.map eS * (Formalism.UG.cT Dv.σw X).map eS = 1
    rw [← Matrix.map_mul, hX', Matrix.map_one _ (map_zero _) (map_one _)]
  choose lift hlv hlw using GlobalTheory.InertSurj.exists_supported L v
  let E : AL L := (1 : L) ⊗ₜ[maximalRealSubfield L] GlobalTheory.InertUmax.sgl L v 1
  have hEv : compAt L v E = 1 := by
    rw [GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.sgl_same]; rfl
  have hEw : ∀ u, u ≠ v → compAt L u E = 0 := by
    intro u hu
    rw [GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.sgl_ne L v 1 hu, tmul_zero]
  let Z : Matrix (Fin n) (Fin n) (AL L) := M.map lift + (1 - E) • (1 : Matrix (Fin n) (Fin n) (AL L))
  have hZv : Z.map (compAt L v) = M := by
    ext i j
    simp only [Z, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul,
      map_sub, map_one, hEv, hlv, sub_self, zero_mul, add_zero]
  have hZw : ∀ u, u ≠ v → Z.map (compAt L u) = 1 := by
    intro u hu
    ext i j
    simp only [Z, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul,
      map_sub, map_one, hEw u hu, hlw _ u hu, sub_zero, one_mul, zero_add]
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hZconj : ∀ u, (conjT (conjAL L) Z).map (compAt L u) =
      conjT (Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom (u.adicCompletion (maximalRealSubfield L)))
        (Z.map (compAt L u)) := by
    intro u
    ext i j
    simp [conjT, GlobalTheory.InertSurj.compAt_conjAL]
  have hZZ : Z * conjT (conjAL L) Z = 1 := by
    ext i j
    rw [← sub_eq_zero]
    apply GlobalTheory.InertUmax.eq_zero_of_compAt
    intro u
    have key : (Z * conjT (conjAL L) Z).map (compAt L u) = 1 := by
      rw [Matrix.map_mul, hZconj]
      rcases eq_or_ne u v with rfl | hu
      · rw [hZv]; exact hM
      · rw [hZw u hu, conjT_one, Matrix.one_mul]
    have h1 := congrFun (congrFun key i) j
    have h2 := congrFun (congrFun (Matrix.map_one (compAt L u) (map_zero _) (map_one _)) i) j
    simp only [Matrix.map_apply] at h1 h2
    rw [map_sub, h1, h2, sub_self]
  have hZZ' : conjT (conjAL L) Z * Z = 1 := mul_eq_one_comm.mp hZZ
  let g : GL (Fin n) (AL L) := ⟨Z, conjT (conjAL L) Z, hZZ, hZZ'⟩
  have hg : g ∈ ReciprocityTheory.Aut.GA L n := hZZ
  refine ⟨⟨g, hg⟩, ?_, ?_⟩
  · intro u hu
    exact hZw u (by simpa using hu)
  · have hb : Formalism.UG.bc (n := Fin n)
        (Dv.e : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L) →+* w.adicCompletion L)
        (Matrix.GeneralLinearGroup.map (compAt L v) (((⟨g, hg⟩ : GAf L n)) : GL (Fin n) (AL L))) =
        Dv.P * y * Dv.P⁻¹ := by
      apply Units.ext
      change (Z.map (compAt L v)).map _ = X
      rw [hZv]
      ext i j
      simp [M, eS]
    unfold InertDatum.loc
    rw [hb]
    group

end GlobalTheory.InertSurj
