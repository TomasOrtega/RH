import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDoubleCosetsDefiniteUnitaryMaximalLevelStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsCharacterEigenvectorOfCommutingRepresentat
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvMemDoubleCosetAndComm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDoubleCosetFiniteLeftCosetsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMaxCompactOfTrivOutsideLocalIntegralStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteInertHeckeSupportCosetsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.UG

noncomputable section
open TensorProduct

namespace GlobalTheory.InertLocSurj

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b`. Simplify using `only [conjAL, RingHom.coe_coe, AlgHom.toRingHom_eq_coe, Algebra.TensorProduct.map_tmul, GlobalTheory.InertUmax.compAt_tmul, Formalism.UG.sigR, AlgHom.coe_id, id_eq]`. Consider the case `add a b ha hb => simp only [map_add]`.

Rewrite using `[ha, hb]`.
-/
theorem compAt_conjAL (u : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (z : AL L) :
    compAt L u (conjAL L z) = Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom
      (u.adicCompletion (maximalRealSubfield L)) (compAt L u z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp only [conjAL, RingHom.coe_coe, AlgHom.toRingHom_eq_coe, Algebra.TensorProduct.map_tmul,
      GlobalTheory.InertUmax.compAt_tmul, Formalism.UG.sigR, AlgHom.coe_id, id_eq]
  | add a b ha hb => simp only [map_add]; rw [ha, hb]

/- English proof (translation)
Set `b : Module.Basis (Fin 2) (maximalRealSubfield L) L` to `Module.finBasisOfFinrankEq _ _ (Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield L) L)`. Take `⟨a, c, rfl⟩` from `GlobalTheory.InertUmax.tensor_decomp b t`. Use `⟨b 0 ⊗ₜ GlobalTheory.InertUmax.sgl L v a + b 1 ⊗ₜ GlobalTheory.InertUmax.sgl L v c, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.sgl_same, GlobalTheory.InertUmax.sgl_same]`. Introduce `u hu`.

Rewrite using `[map_add, GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.sgl_ne L v a hu, GlobalTheory.InertUmax.sgl_ne L v c hu, tmul_zero, tmul_zero, add_zero]`.
-/
theorem exists_supported (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (t : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L)) :
    ∃ T : AL L, compAt L v T = t ∧ ∀ u, u ≠ v → compAt L u T = 0 := by
  let b : Module.Basis (Fin 2) (maximalRealSubfield L) L := Module.finBasisOfFinrankEq _ _
    (Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield L) L)
  obtain ⟨a, c, rfl⟩ := GlobalTheory.InertUmax.tensor_decomp b t
  refine ⟨b 0 ⊗ₜ GlobalTheory.InertUmax.sgl L v a + b 1 ⊗ₜ GlobalTheory.InertUmax.sgl L v c, ?_, ?_⟩
  · rw [map_add, GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.sgl_same,
      GlobalTheory.InertUmax.sgl_same]
  · intro u hu
    rw [map_add, GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.sgl_ne L v a hu,
      GlobalTheory.InertUmax.sgl_ne L v c hu, tmul_zero, tmul_zero, add_zero]

/- English proof (translation)
Introduce `L _ _ _ n v w Dv y hy`. Establish `hy' : Formalism.UG.cT Dv.σw (y : Matrix (Fin n) (Fin n) (w.adicCompletion L)) * Formalism.UG.antiJ (w.adicCompletion L) n * (y : Matrix (Fin n) (Fin n) (w.adicCompletion L)) = Formalism.UG.antiJ (w.adicCompletion L) n` using `hy`. Set `Z : Matrix (Fin n) (Fin n) (w.adicCompletion L)` to `((Dv.P * y * Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) _)`. Establish `hPP : (Dv.P : Matrix (Fin n) (Fin n) (w.adicCompletion L)) * ((Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) _) = 1`. Rewrite using `[← Units.val_mul, mul_inv_cancel, Units.val_one]`.

Establish `hZ : Formalism.UG.cT Dv.σw Z * Z = 1`. Simplify using `only [Z, Units.val_mul, Formalism.UG.cT_mul]`. Establish `h1` using `Dv.Panti`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`.

Use `_ = Formalism.UG.cT Dv.σw ((Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) _) * (Formalism.UG.cT Dv.σw (Dv.P : Matrix (Fin n) (Fin n) _) * (Dv.P : Matrix (Fin n) (Fin n) _)) * ((Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) _) := by`. Rewrite using `[h1, hy']`. Use `_ = Formalism.UG.cT Dv.σw ((Dv.P : Matrix (Fin n) (Fin n) (w.adicCompletion L)) * ((Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) _)) * ((Dv.P : Matrix (Fin n) (Fin n) _) * ((Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) _)) := by`. Rewrite using `[Formalism.UG.cT_mul]`. Simplify using `only [Matrix.mul_assoc]`.

Use `_ = 1 := by rw [hPP, Formalism.UG.cT_one, Matrix.one_mul]`. Establish `hZ' : Z * Formalism.UG.cT Dv.σw Z = 1` using `mul_eq_one_comm.mp hZ`. Use `set sg := Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom (v.adicCompletion (maximalRealSubfield L)) with hsg`. Set `Xv : Matrix (Fin n) (Fin n) (L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L))` to `Z.map Dv.e.symm`. Establish `hXZ : Xv.map Dv.e = Z` using `by ext i j; simp [Xv]`.

Establish `hX : Xv * conjT sg Xv = 1`. Establish `hcomm : ∀ z, Dv.e.symm (Dv.σw z) = sg (Dv.e.symm z)`. Introduce `z`. Apply `Dv.e.injective` to reduce the goal to its premises. Rewrite using `[RingEquiv.apply_symm_apply, Dv.comm, RingEquiv.apply_symm_apply]`.

Establish `h2` using `congrArg (fun M => M.map Dv.e.symm) hZ'`. Simplify using `only [Matrix.map_mul] at h2`. Rewrite `h2` using `[Matrix.map_one _ (map_zero _) (map_one _)]`. Use `h2 using 2` and compare the differences between its conclusion and the goal. Use extensionality with `i j`.

Simplify using `[conjT, Formalism.UG.cT, Xv, hcomm]`. Use `choose T hTv hTu using GlobalTheory.InertLocSurj.exists_supported (L := L) v`. Take `⟨E, hEv, hEu⟩` from `GlobalTheory.InertLocSurj.exists_supported (L := L) v 1`. Set `A : Matrix (Fin n) (Fin n) (AL L)` to `fun i j => T (Xv i j) + if i = j then 1 - E else 0`. Establish `hAv : A.map (compAt L v) = Xv`.

Use extensionality with `i j`. Use `show compAt L v (T (Xv i j) + if i = j then 1 - E else 0) = Xv i j`. Distinguish the cases in `h : i = j`. Rewrite using `[if_pos h, map_add, hTv, map_sub, map_one, hEv, sub_self, add_zero]`. Rewrite using `[if_neg h, map_add, hTv, map_zero, add_zero]`.

Establish `hAu : ∀ u, u ≠ v → A.map (compAt L u) = 1`. Introduce `u hu`. Use extensionality with `i j`. Use `show compAt L u (T (Xv i j) + if i = j then 1 - E else 0) = (1 : Matrix (Fin n) (Fin n) _) i j`. Rewrite using `[Matrix.one_apply]`.

Distinguish the cases in `h : i = j`. Rewrite using `[if_pos h, if_pos h, map_add, hTu _ u hu, map_sub, map_one, hEu u hu, zero_add, sub_zero]`. Rewrite using `[if_neg h, if_neg h, map_add, hTu _ u hu, map_zero, add_zero]`. Establish `hmap : ∀ u, (A * conjT (conjAL L) A).map (compAt L u) = A.map (compAt L u) * conjT (Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom (u.adicCompletion (maximalRealSubfield L))) (A.map (compAt L u))`. Introduce `u`.

Rewrite using `[Matrix.map_mul]`. Use `congr 1`. Use extensionality with `i j`. Simplify using `[conjT, GlobalTheory.InertLocSurj.compAt_conjAL]`. Establish `hA : A * conjT (conjAL L) A = 1`.

Use extensionality with `i j`. Rewrite using `[← sub_eq_zero]`. Apply `GlobalTheory.InertUmax.eq_zero_of_compAt` to reduce the goal to its premises. Introduce `u`. Establish `h3 : (A * conjT (conjAL L) A).map (compAt L u) = (1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L u)`.

Rewrite using `[hmap, Matrix.map_one _ (map_zero _) (map_one _)]`. Break down `eq_or_ne u v with rfl | hu` into its components or cases. Rewrite using `[hAv]`. Conclude with `hX`. Rewrite using `[hAu u hu, conjT_one, Matrix.one_mul]`.

Establish `h4` using `congrFun (congrFun h3 i) j`. Simplify using `only [Matrix.map_apply] at h4`. Rewrite using `[map_sub, h4, sub_self]`. Set `g : GL (Fin n) (AL L)` to `⟨A, conjT (conjAL L) A, hA, mul_eq_one_comm.mp hA⟩`. Establish `hg : g ∈ GA L n` using `hA`.

Use `⟨⟨g, hg⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `u hu`. Conclude with `hAu u (by simpa using hu)`. Establish `hbc : Formalism.UG.bc (n` using `Fin n) (Dv.e : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L) →+* w.adicCompletion L) (Matrix.GeneralLinearGroup.map (compAt L v) g) = Dv.P * y * Dv.P⁻¹ := by`. Apply `Units.ext` to reduce the goal to its premises.

Use `show (A.map (compAt L v)).map Dv.e = Z`. Rewrite using `[hAv, hXZ]`. Unfold `InertDatum.loc`. Use `show Dv.P⁻¹ * Formalism.UG.bc (n := Fin n) (Dv.e : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L) →+* w.adicCompletion L) (Matrix.GeneralLinearGroup.map (compAt L v) g) * Dv.P = y`. Rewrite using `[hbc]`.

Use `group`.
-/
theorem exists_trivOutside_loc_eq : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L))
    (Dv : InertDatum L n v w), ∀ y : GL (Fin n) (w.adicCompletion L), y ∈ GU Dv.σw n →
    ∃ x : GAf L n, TrivOutside {v} x ∧ Dv.loc x = y := by
  intro L _ _ _ n v w Dv y hy
  classical
  have hy' : Formalism.UG.cT Dv.σw (y : Matrix (Fin n) (Fin n) (w.adicCompletion L)) *
      Formalism.UG.antiJ (w.adicCompletion L) n * (y : Matrix (Fin n) (Fin n) (w.adicCompletion L)) =
      Formalism.UG.antiJ (w.adicCompletion L) n := hy
  let Z : Matrix (Fin n) (Fin n) (w.adicCompletion L) :=
    ((Dv.P * y * Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) _)
  have hPP : (Dv.P : Matrix (Fin n) (Fin n) (w.adicCompletion L)) *
      ((Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) _) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hZ : Formalism.UG.cT Dv.σw Z * Z = 1 := by
    simp only [Z, Units.val_mul, Formalism.UG.cT_mul]
    have h1 := Dv.Panti
    calc Formalism.UG.cT Dv.σw ((Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) _) *
          (Formalism.UG.cT Dv.σw (y : Matrix (Fin n) (Fin n) _) * Formalism.UG.cT Dv.σw (Dv.P : Matrix (Fin n) (Fin n) _)) *
          ((Dv.P : Matrix (Fin n) (Fin n) _) * (y : Matrix (Fin n) (Fin n) _) *
            ((Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) _))
        = Formalism.UG.cT Dv.σw ((Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) _) *
          (Formalism.UG.cT Dv.σw (y : Matrix (Fin n) (Fin n) _) *
            (Formalism.UG.cT Dv.σw (Dv.P : Matrix (Fin n) (Fin n) _) * (Dv.P : Matrix (Fin n) (Fin n) _)) *
            (y : Matrix (Fin n) (Fin n) _)) *
          ((Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) _) := by
          simp only [Matrix.mul_assoc]
      _ = Formalism.UG.cT Dv.σw ((Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) _) *
          (Formalism.UG.cT Dv.σw (Dv.P : Matrix (Fin n) (Fin n) _) * (Dv.P : Matrix (Fin n) (Fin n) _)) *
          ((Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) _) := by
          rw [h1, hy']
      _ = Formalism.UG.cT Dv.σw ((Dv.P : Matrix (Fin n) (Fin n) (w.adicCompletion L)) *
            ((Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) _)) *
          ((Dv.P : Matrix (Fin n) (Fin n) _) *
            ((Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) _)) := by
          rw [Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hPP, Formalism.UG.cT_one, Matrix.one_mul]
  have hZ' : Z * Formalism.UG.cT Dv.σw Z = 1 := mul_eq_one_comm.mp hZ
  set sg := Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom
      (v.adicCompletion (maximalRealSubfield L)) with hsg
  let Xv : Matrix (Fin n) (Fin n) (L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L)) :=
    Z.map Dv.e.symm
  have hXZ : Xv.map Dv.e = Z := by ext i j; simp [Xv]
  have hX : Xv * conjT sg Xv = 1 := by
    have hcomm : ∀ z, Dv.e.symm (Dv.σw z) = sg (Dv.e.symm z) := by
      intro z
      apply Dv.e.injective
      rw [RingEquiv.apply_symm_apply, Dv.comm, RingEquiv.apply_symm_apply]
    have h2 := congrArg (fun M => M.map Dv.e.symm) hZ'
    simp only [Matrix.map_mul] at h2
    rw [Matrix.map_one _ (map_zero _) (map_one _)] at h2
    convert h2 using 2
    ext i j
    simp [conjT, Formalism.UG.cT, Xv, hcomm]
  choose T hTv hTu using GlobalTheory.InertLocSurj.exists_supported (L := L) v
  obtain ⟨E, hEv, hEu⟩ := GlobalTheory.InertLocSurj.exists_supported (L := L) v 1
  let A : Matrix (Fin n) (Fin n) (AL L) := fun i j => T (Xv i j) + if i = j then 1 - E else 0
  have hAv : A.map (compAt L v) = Xv := by
    ext i j
    show compAt L v (T (Xv i j) + if i = j then 1 - E else 0) = Xv i j
    by_cases h : i = j
    · rw [if_pos h, map_add, hTv, map_sub, map_one, hEv, sub_self, add_zero]
    · rw [if_neg h, map_add, hTv, map_zero, add_zero]
  have hAu : ∀ u, u ≠ v → A.map (compAt L u) = 1 := by
    intro u hu
    ext i j
    show compAt L u (T (Xv i j) + if i = j then 1 - E else 0) = (1 : Matrix (Fin n) (Fin n) _) i j
    rw [Matrix.one_apply]
    by_cases h : i = j
    · rw [if_pos h, if_pos h, map_add, hTu _ u hu, map_sub, map_one, hEu u hu, zero_add, sub_zero]
    · rw [if_neg h, if_neg h, map_add, hTu _ u hu, map_zero, add_zero]
  have hmap : ∀ u, (A * conjT (conjAL L) A).map (compAt L u) =
      A.map (compAt L u) * conjT (Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom
        (u.adicCompletion (maximalRealSubfield L))) (A.map (compAt L u)) := by
    intro u
    rw [Matrix.map_mul]
    congr 1
    ext i j
    simp [conjT, GlobalTheory.InertLocSurj.compAt_conjAL]
  have hA : A * conjT (conjAL L) A = 1 := by
    ext i j
    rw [← sub_eq_zero]
    apply GlobalTheory.InertUmax.eq_zero_of_compAt
    intro u
    have h3 : (A * conjT (conjAL L) A).map (compAt L u) = (1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L u) := by
      rw [hmap, Matrix.map_one _ (map_zero _) (map_one _)]
      rcases eq_or_ne u v with rfl | hu
      · rw [hAv]; exact hX
      · rw [hAu u hu, conjT_one, Matrix.one_mul]
    have h4 := congrFun (congrFun h3 i) j
    simp only [Matrix.map_apply] at h4
    rw [map_sub, h4, sub_self]
  let g : GL (Fin n) (AL L) := ⟨A, conjT (conjAL L) A, hA, mul_eq_one_comm.mp hA⟩
  have hg : g ∈ GA L n := hA
  refine ⟨⟨g, hg⟩, ?_, ?_⟩
  · intro u hu
    exact hAu u (by simpa using hu)
  · have hbc : Formalism.UG.bc (n := Fin n)
        (Dv.e : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L) →+* w.adicCompletion L)
        (Matrix.GeneralLinearGroup.map (compAt L v) g) = Dv.P * y * Dv.P⁻¹ := by
      apply Units.ext
      show (A.map (compAt L v)).map Dv.e = Z
      rw [hAv, hXZ]
    unfold InertDatum.loc
    show Dv.P⁻¹ * Formalism.UG.bc (n := Fin n)
        (Dv.e : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L) →+* w.adicCompletion L)
        (Matrix.GeneralLinearGroup.map (compAt L v) g) * Dv.P = y
    rw [hbc]
    group

end GlobalTheory.InertLocSurj
