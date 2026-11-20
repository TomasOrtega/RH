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

namespace GlobalTheory.InertInvar

open scoped TensorProduct

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
  {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {w : HeightOneSpectrum (𝓞 L)}

/- English proof (translation)
Establish `key : ALint L ≤ (tensInt (F` using `maximalRealSubfield L) (v.adicCompletion (maximalRealSubfield L)) (intOE L) (Formalism.UG.Ov (maximalRealSubfield L) v)).comap (compAt L v) := by`. Rewrite using `[ALint, Subring.closure_le]`. Introduce and unpack `_ (⟨y, rfl⟩ | ⟨a, ha, rfl⟩)`. Apply `Subring.subset_closure left` to reduce the goal to its premises. Use `⟨⟨(y : L), y, rfl⟩, ?_⟩` and prove the remaining obligations.

Use `show _ = compAt L v ((y : L) ⊗ₜ[maximalRealSubfield L] (1 : AFplus L))`. Rewrite using `[GlobalTheory.InertUmax.compAt_tmul]`. Both sides reduce to the same expression. Apply `Subring.subset_closure right` to reduce the goal to its premises. Use `⟨⟨a v, ha v⟩, ?_⟩` and prove the remaining obligations.

Use `show _ = compAt L v ((1 : L) ⊗ₜ[maximalRealSubfield L] a)`. Rewrite using `[GlobalTheory.InertUmax.compAt_tmul]`. Conclude with `key hx`.
-/
theorem compAt_mem_tensInt (x : AL L) (hx : x ∈ ALint L) :
    compAt L v x ∈ tensInt (F := maximalRealSubfield L) (v.adicCompletion (maximalRealSubfield L))
      (intOE L) (Formalism.UG.Ov (maximalRealSubfield L) v) := by
  have key : ALint L ≤ (tensInt (F := maximalRealSubfield L) (v.adicCompletion (maximalRealSubfield L))
      (intOE L) (Formalism.UG.Ov (maximalRealSubfield L) v)).comap (compAt L v) := by
    rw [ALint, Subring.closure_le]
    rintro _ (⟨y, rfl⟩ | ⟨a, ha, rfl⟩)
    · apply Subring.subset_closure
      left
      refine ⟨⟨(y : L), y, rfl⟩, ?_⟩
      show _ = compAt L v ((y : L) ⊗ₜ[maximalRealSubfield L] (1 : AFplus L))
      rw [GlobalTheory.InertUmax.compAt_tmul]
      rfl
    · apply Subring.subset_closure
      right
      refine ⟨⟨a v, ha v⟩, ?_⟩
      show _ = compAt L v ((1 : L) ⊗ₜ[maximalRealSubfield L] a)
      rw [GlobalTheory.InertUmax.compAt_tmul]
  exact key hx

/- English proof (translation)
Establish `hP` using `GlobalTheory.InertUmax.entries_mem_of_range _ _ Dv.Pint`. Establish `hP'` using `GlobalTheory.InertUmax.entries_mem_of_range _ _ (inv_mem Dv.Pint)`. Establish `hm : ∀ k l, ((Formalism.UG.bc (n` using `Fin n) (Dv.e : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L) →+* w.adicCompletion L) (Matrix.GeneralLinearGroup.map (compAt L v) (z : GL (Fin n) (AL L))) : GL (Fin n) _) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) k l ∈ intL (w.adicCompletion L) := by`. Introduce `k l`. Establish `hzk : ((z.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) k l ∈ ALint L` using `hz k l`.

Conclude with `(Dv.integ _).1 (compAt_mem_tensInt (v := v) _ hzk)`. Unfold `InertDatum.loc`. Simplify using `only [Units.val_mul, Matrix.mul_apply]`. Conclude with `Subring.sum_mem _ fun k _ => Subring.mul_mem _ (Subring.sum_mem _ fun l _ => Subring.mul_mem _ (hP' i l) (hm l k)) (hP k j)`.
-/
theorem loc_entries_int (Dv : InertDatum L n v w) (z : GAf L n) (hz : z ∈ Umax L n) (i j : Fin n) :
    ((Dv.loc z : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) i j ∈
      intL (w.adicCompletion L) := by
  have hP := GlobalTheory.InertUmax.entries_mem_of_range _ _ Dv.Pint
  have hP' := GlobalTheory.InertUmax.entries_mem_of_range _ _ (inv_mem Dv.Pint)
  have hm : ∀ k l, ((Formalism.UG.bc (n := Fin n)
      (Dv.e : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L) →+* w.adicCompletion L)
      (Matrix.GeneralLinearGroup.map (compAt L v) (z : GL (Fin n) (AL L))) : GL (Fin n) _) :
        Matrix (Fin n) (Fin n) (w.adicCompletion L)) k l ∈ intL (w.adicCompletion L) := by
    intro k l
    have hzk : ((z.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) k l ∈ ALint L := hz k l
    exact (Dv.integ _).1 (compAt_mem_tensInt (v := v) _ hzk)
  unfold InertDatum.loc
  simp only [Units.val_mul, Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _
    (Subring.sum_mem _ fun l _ => Subring.mul_mem _ (hP' i l) (hm l k)) (hP k j)

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b`. Simplify using `[conjAL, compAt, Formalism.UG.sigR, Algebra.TensorProduct.map_tmul]`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`.
-/
theorem compAt_conjAL (x : AL L) :
    compAt L v (conjAL L x) =
      Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom (v.adicCompletion (maximalRealSubfield L)) (compAt L v x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp [conjAL, compAt, Formalism.UG.sigR, Algebra.TensorProduct.map_tmul]
  | add a b ha hb => simp only [map_add, ha, hb]

/- English proof (translation)
Use `set φ : AL L →+* w.adicCompletion L := (Dv.e : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L) →+* w.adicCompletion L).comp (compAt L v) with hφ`. Use `set Y : Matrix (Fin n) (Fin n) (w.adicCompletion L) := ((z.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)).map φ with hY`. Establish `hφc : ∀ x, φ (conjAL L x) = Dv.σw (φ x)`. Introduce `x`. Simplify using `only [hφ, RingHom.comp_apply, compAt_conjAL]`.

Conclude with `Dv.comm _`. Establish `hz : ((z.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) * conjT (conjAL L) ((z.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = 1` using `z.2`. Establish `hYY : Y * Formalism.UG.cT Dv.σw Y = 1`. Use `congrArg (fun M => M.map φ) hz` as an intermediate fact. Simplify using `only [Matrix.map_mul, Matrix.map_one _ (map_zero φ) (map_one φ)] at this`.

Rewrite using `[← this]`. Use `congr 1`. Use extensionality with `i j`. Simplify using `[Formalism.UG.cT, conjT, hY, hφc]`. Establish `hYY' : Formalism.UG.cT Dv.σw Y * Y = 1` using `mul_eq_one_comm.1 hYY`.

Use `set P : Matrix (Fin n) (Fin n) (w.adicCompletion L) := (Dv.P : Matrix (Fin n) (Fin n) (w.adicCompletion L))`. Use `set Pi : Matrix (Fin n) (Fin n) (w.adicCompletion L) := ((Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L))`. Establish `hPPi : P * Pi = 1` using `by simp [P, Pi]`. Establish `hPi : Formalism.UG.cT Dv.σw Pi * Formalism.UG.cT Dv.σw P = 1`. Rewrite using `[← Formalism.UG.cT_mul, hPPi, Formalism.UG.cT_one]`.

Establish `hloc : ((Dv.loc z : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) = Pi * Y * P` using `rfl`. Use `show Formalism.UG.cT Dv.σw ((Dv.loc z : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) _) * Formalism.UG.antiJ (w.adicCompletion L) n * ((Dv.loc z : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) _) = Formalism.UG.antiJ (w.adicCompletion L) n`. Rewrite using `[hloc, ← Dv.Panti, Formalism.UG.cT_mul, Formalism.UG.cT_mul]`. Express the relevant statement in the definitionally equal form `Formalism.UG.cT Dv.σw P * (Formalism.UG.cT Dv.σw Y * Formalism.UG.cT Dv.σw Pi) * (Formalism.UG.cT Dv.σw P * P) * (Pi * Y * P) = Formalism.UG.cT Dv.σw P * P`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = Formalism.UG.cT Dv.σw P * (Formalism.UG.cT Dv.σw Y * Y) * P := by`. Rewrite using `[hPi, hPPi]`. Simplify using `only [Matrix.mul_one, Matrix.mul_assoc]`. Use `_ = Formalism.UG.cT Dv.σw P * P := by rw [hYY', Matrix.mul_one]`.
-/
theorem loc_mem_GU (Dv : InertDatum L n v w) (z : GAf L n) : Dv.loc z ∈ Formalism.UG.GU Dv.σw n := by
  set φ : AL L →+* w.adicCompletion L :=
    (Dv.e : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L) →+* w.adicCompletion L).comp
      (compAt L v) with hφ
  set Y : Matrix (Fin n) (Fin n) (w.adicCompletion L) :=
    ((z.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)).map φ with hY
  have hφc : ∀ x, φ (conjAL L x) = Dv.σw (φ x) := by
    intro x
    simp only [hφ, RingHom.comp_apply, compAt_conjAL]
    exact Dv.comm _
  have hz : ((z.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
      conjT (conjAL L) ((z.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = 1 := z.2
  have hYY : Y * Formalism.UG.cT Dv.σw Y = 1 := by
    have := congrArg (fun M => M.map φ) hz
    simp only [Matrix.map_mul, Matrix.map_one _ (map_zero φ) (map_one φ)] at this
    rw [← this]
    congr 1
    ext i j
    simp [Formalism.UG.cT, conjT, hY, hφc]
  have hYY' : Formalism.UG.cT Dv.σw Y * Y = 1 := mul_eq_one_comm.1 hYY
  set P : Matrix (Fin n) (Fin n) (w.adicCompletion L) := (Dv.P : Matrix (Fin n) (Fin n) (w.adicCompletion L))
  set Pi : Matrix (Fin n) (Fin n) (w.adicCompletion L) :=
    ((Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L))
  have hPPi : P * Pi = 1 := by simp [P, Pi]
  have hPi : Formalism.UG.cT Dv.σw Pi * Formalism.UG.cT Dv.σw P = 1 := by
    rw [← Formalism.UG.cT_mul, hPPi, Formalism.UG.cT_one]
  have hloc : ((Dv.loc z : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) =
      Pi * Y * P := rfl
  show Formalism.UG.cT Dv.σw ((Dv.loc z : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) _) *
      Formalism.UG.antiJ (w.adicCompletion L) n * ((Dv.loc z : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) _) =
    Formalism.UG.antiJ (w.adicCompletion L) n
  rw [hloc, ← Dv.Panti, Formalism.UG.cT_mul, Formalism.UG.cT_mul]
  change Formalism.UG.cT Dv.σw P * (Formalism.UG.cT Dv.σw Y * Formalism.UG.cT Dv.σw Pi) * (Formalism.UG.cT Dv.σw P * P) * (Pi * Y * P) =
    Formalism.UG.cT Dv.σw P * P
  calc Formalism.UG.cT Dv.σw P * (Formalism.UG.cT Dv.σw Y * Formalism.UG.cT Dv.σw Pi) * (Formalism.UG.cT Dv.σw P * P) * (Pi * Y * P)
      = Formalism.UG.cT Dv.σw P * Formalism.UG.cT Dv.σw Y * (Formalism.UG.cT Dv.σw Pi * Formalism.UG.cT Dv.σw P) * (P * Pi) * Y * P := by
        simp only [Matrix.mul_assoc]
    _ = Formalism.UG.cT Dv.σw P * (Formalism.UG.cT Dv.σw Y * Y) * P := by
        rw [hPi, hPPi]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = Formalism.UG.cT Dv.σw P * P := by rw [hYY', Matrix.mul_one]

/- English proof (translation)
Apply `GlobalTheory.SatInd.DCoset.mem_KU_of_entries` to reduce the goal to its premises. Introduce `i j`. Conclude with `(Valuation.mem_integer_iff _ _).1 (loc_entries_int Dv z hz i j)`. Introduce `i j`. Establish `e : (((⟨Dv.loc z, loc_mem_GU Dv z⟩ : Formalism.UG.GU Dv.σw n)⁻¹ : Formalism.UG.GU Dv.σw n) : GL (Fin n) (w.adicCompletion L)) = Dv.loc z⁻¹` using `by show (Dv.loc z)⁻¹ = GlobalTheory.SatInd.CosetFin.locHom Dv z⁻¹`.

Rewrite using `[map_inv]`. Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `(Valuation.mem_integer_iff _ _).1 (loc_entries_int Dv z⁻¹ (inv_mem hz) i j)`.
-/
theorem loc_mem_KU (Dv : InertDatum L n v w) (z : GAf L n) (hz : z ∈ Umax L n) :
    (⟨Dv.loc z, loc_mem_GU Dv z⟩ : Formalism.UG.GU Dv.σw n) ∈ Formalism.UG.KU Dv.σw n := by
  apply GlobalTheory.SatInd.DCoset.mem_KU_of_entries
  · intro i j
    exact (Valuation.mem_integer_iff _ _).1 (loc_entries_int Dv z hz i j)
  · intro i j
    have e : (((⟨Dv.loc z, loc_mem_GU Dv z⟩ : Formalism.UG.GU Dv.σw n)⁻¹ : Formalism.UG.GU Dv.σw n) :
        GL (Fin n) (w.adicCompletion L)) = Dv.loc z⁻¹ := by
      show (Dv.loc z)⁻¹ = GlobalTheory.SatInd.CosetFin.locHom Dv z⁻¹
      rw [map_inv]; rfl
    rw [e]
    exact (Valuation.mem_integer_iff _ _).1 (loc_entries_int Dv z⁻¹ (inv_mem hz) i j)

/- English proof (translation)
Unfold `InertDatum.hval`. Distinguish the cases in `hm : m ∈ Formalism.UG.GU Dv.σw n`. Establish `hm' : (k₁ : GL (Fin n) (w.adicCompletion L)) * m * k₂ ∈ Formalism.UG.GU Dv.σw n` using `mul_mem (mul_mem k₁.2 hm) k₂.2`. Rewrite using `[dif_pos hm', dif_pos hm]`. Use `hbi ⟨k₁, hk₁⟩ ⟨k₂, hk₂⟩ ⟨m, hm⟩` as an intermediate fact.

Conclude with `this`. Establish `hm' : (k₁ : GL (Fin n) (w.adicCompletion L)) * m * k₂ ∉ Formalism.UG.GU Dv.σw n`. Introduce `h'`. Apply `hm` to reduce the goal to its premises. Establish `e : m = (k₁⁻¹ : Formalism.UG.GU Dv.σw n) * ((k₁ : GL (Fin n) (w.adicCompletion L)) * m * k₂) * (k₂⁻¹ : Formalism.UG.GU Dv.σw n)`.

Simplify using `[mul_assoc]`. Rewrite using `[e]`. Conclude with `mul_mem (mul_mem (k₁⁻¹).2 h') (k₂⁻¹).2`. Rewrite using `[dif_neg hm', dif_neg hm]`.
-/
theorem hval_mul_KU (Dv : InertDatum L n v w) (h : Formalism.UG.GU Dv.σw n → ℂ)
    (hbi : IsBiInv (Formalism.UG.KU Dv.σw n) h) (k₁ k₂ : Formalism.UG.GU Dv.σw n)
    (hk₁ : k₁ ∈ Formalism.UG.KU Dv.σw n) (hk₂ : k₂ ∈ Formalism.UG.KU Dv.σw n) (m : GL (Fin n) (w.adicCompletion L)) :
    Dv.hval h ((k₁ : GL (Fin n) (w.adicCompletion L)) * m * k₂) = Dv.hval h m := by
  unfold InertDatum.hval
  by_cases hm : m ∈ Formalism.UG.GU Dv.σw n
  · have hm' : (k₁ : GL (Fin n) (w.adicCompletion L)) * m * k₂ ∈ Formalism.UG.GU Dv.σw n :=
      mul_mem (mul_mem k₁.2 hm) k₂.2
    rw [dif_pos hm', dif_pos hm]
    have := hbi ⟨k₁, hk₁⟩ ⟨k₂, hk₂⟩ ⟨m, hm⟩
    exact this
  · have hm' : (k₁ : GL (Fin n) (w.adicCompletion L)) * m * k₂ ∉ Formalism.UG.GU Dv.σw n := by
      intro h'
      apply hm
      have e : m = (k₁⁻¹ : Formalism.UG.GU Dv.σw n) * ((k₁ : GL (Fin n) (w.adicCompletion L)) * m * k₂) *
          (k₂⁻¹ : Formalism.UG.GU Dv.σw n) := by
        simp [mul_assoc]
      rw [e]
      exact mul_mem (mul_mem (k₁⁻¹).2 h') (k₂⁻¹).2
    rw [dif_neg hm', dif_neg hm]

end GlobalTheory.InertInvar

open GlobalTheory.InertInvar GlobalTheory.SatInd.CosetFin in
/- English proof (translation)
Introduce `L _ _ _ n v w Dv U hU hsplit W _ _ h hh f hf κ hκ`. Take `⟨a, b, rfl, haU, hat, hbU, hbc⟩` from `hsplit κ hκ`. Establish `hfr : ∀ r ∈ U, ∀ y, f (y * r) = f y` using `fun r hr y => congrFun (hf r hr) y`. Establish `haM : a ∈ Umax L n` using `(hU a hat).1 haU`. Establish `hbi : IsBiInv (KU Dv.σw n) h` using `hh.1`.

Establish `h1 : ∀ g, heckeFunI L n U Dv h f (g * (a * b)) = heckeFunI L n U Dv h f (g * a)`. Introduce `g`. Unfold `heckeFunI`. Use `finsum_congr fun c => ?_` and prove the remaining obligations. Use `split_ifs with hc`.

Use `congr 1`. Establish `e : g * (a * b) * hc.choose = g * a * hc.choose * b`. Simplify using `only [mul_assoc]`. Rewrite using `[← hbc _ hc.choose_spec.2]`. Rewrite using `[e, hfr b hbU]`.

Both sides reduce to the same expression. Establish `h2 : ∀ g, heckeFunI L n U Dv h f (g * a) = heckeFunI L n U Dv h f g`. Introduce `g`. Unfold `heckeFunI`. Use `Eq.trans ?_ (finsum_comp_equiv (MulAction.toPerm a : GAf L n ⧸ U ≃ GAf L n ⧸ U))` and prove the remaining obligations.

Use `finsum_congr fun c => ?_` and prove the remaining obligations. Establish `hac : (MulAction.toPerm a : GAf L n ⧸ U ≃ GAf L n ⧸ U) c = a • c` using `rfl`. Distinguish the cases in `hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x`. Take `⟨x0, hx0, hx0t⟩` from `id hc`. Establish `hc' : ∃ y : GAf L n, (y : GAf L n ⧸ U) = (MulAction.toPerm a : GAf L n ⧸ U ≃ GAf L n ⧸ U) c ∧ TrivOutside {v} y` using `⟨a * x0, by rw [hac, ← hx0, MulAction.Quotient.smul_mk, smul_eq_mul], trivOutside_mul hat hx0t⟩`.

Rewrite using `[dif_pos hc, dif_pos hc']`. Use `set x := hc.choose with hxdef`. Use `set y := hc'.choose with hydef`. Establish `hx` using `hc.choose_spec`. Establish `hy` using `hc'.choose_spec`.

Rewrite `hx` using `[← hxdef]`. Rewrite `hy` using `[← hydef]`. Establish `hq : ((a * x : GAf L n) : GAf L n ⧸ U) = (y : GAf L n ⧸ U)`. Rewrite using `[hy.1, hac, ← hx.1, MulAction.Quotient.smul_mk, smul_eq_mul]`. Establish `hrU : (a * x)⁻¹ * y ∈ U` using `QuotientGroup.eq.1 hq`.

Establish `hrt : TrivOutside {v} ((a * x)⁻¹ * y)` using `trivOutside_mul (trivOutside_inv (trivOutside_mul hat hx.2)) hy.2`. Establish `hrM : (a * x)⁻¹ * y ∈ Umax L n` using `(hU _ hrt).1 hrU`. Establish `hye : y = a * x * ((a * x)⁻¹ * y)` using `by group`. Establish `hloc : Dv.loc y = Dv.loc a * Dv.loc x * Dv.loc ((a * x)⁻¹ * y)` using `by conv_lhs => rw [hye] show locHom Dv _ = locHom Dv a * locHom Dv x * locHom Dv _`. Rewrite using `[map_mul, map_mul]`.

Establish `hfy : f (g * y) = f (g * a * x)` using `by conv_lhs => rw [hye]`. Rewrite using `[← hfr _ hrU (g * a * x)]`. Simplify using `only [mul_assoc]`. Rewrite using `[hfy, hloc, hval_mul_KU Dv h hbi ⟨Dv.loc a, loc_mem_GU Dv a⟩ ⟨Dv.loc _, loc_mem_GU Dv _⟩ (loc_mem_KU Dv a haM) (loc_mem_KU Dv _ hrM) (Dv.loc x)]`. Establish `hc' : ¬ ∃ y : GAf L n, (y : GAf L n ⧸ U) = (MulAction.toPerm a : GAf L n ⧸ U ≃ GAf L n ⧸ U) c ∧ TrivOutside {v} y`.

Introduce and unpack `⟨y, hy1, hy2⟩`. Use `hc ⟨a⁻¹ * y, ?_, trivOutside_mul (trivOutside_inv hat) hy2⟩` and prove the remaining obligations. Establish `e : ((a⁻¹ * y : GAf L n) : GAf L n ⧸ U) = a⁻¹ • (y : GAf L n ⧸ U)`. Rewrite using `[MulAction.Quotient.smul_mk, smul_eq_mul]`. Rewrite using `[e, hy1, hac]`.

Conclude with `inv_smul_smul a c`. Rewrite using `[dif_neg hc, dif_neg hc']`. Use function extensionality and compare the values at `g`. Use `show heckeFunI L n U Dv h f (g * (a * b)) = heckeFunI L n U Dv h f g`. Rewrite using `[h1, h2]`.
-/
theorem GlobalTheory.heckeFunI_rt_invariant : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (U : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) → (∀ u ∈ U, ∃ a b : GAf L n, u = a * b ∧ a ∈ U ∧ TrivOutside {v} a ∧ b ∈ U ∧ ∀ x : GAf L n, TrivOutside {v} x → x * b = b * x) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W], ∀ h ∈ Hecke ℂ (KU Dv.σw n), ∀ f : GAf L n → W, (∀ κ ∈ U, NG.rt L n κ f = f) → ∀ κ ∈ U, NG.rt L n κ (heckeFunI L n U Dv h f) = heckeFunI L n U Dv h f := by
  intro L _ _ _ n v w Dv U hU hsplit W _ _ h hh f hf κ hκ
  obtain ⟨a, b, rfl, haU, hat, hbU, hbc⟩ := hsplit κ hκ
  have hfr : ∀ r ∈ U, ∀ y, f (y * r) = f y := fun r hr y => congrFun (hf r hr) y
  have haM : a ∈ Umax L n := (hU a hat).1 haU
  have hbi : IsBiInv (KU Dv.σw n) h := hh.1

  have h1 : ∀ g, heckeFunI L n U Dv h f (g * (a * b)) = heckeFunI L n U Dv h f (g * a) := by
    intro g
    unfold heckeFunI
    refine finsum_congr fun c => ?_
    split_ifs with hc
    · congr 1
      have e : g * (a * b) * hc.choose = g * a * hc.choose * b := by
        simp only [mul_assoc]
        rw [← hbc _ hc.choose_spec.2]
      rw [e, hfr b hbU]
    · rfl

  have h2 : ∀ g, heckeFunI L n U Dv h f (g * a) = heckeFunI L n U Dv h f g := by
    intro g
    unfold heckeFunI
    refine Eq.trans ?_ (finsum_comp_equiv (MulAction.toPerm a : GAf L n ⧸ U ≃ GAf L n ⧸ U))
    refine finsum_congr fun c => ?_
    have hac : (MulAction.toPerm a : GAf L n ⧸ U ≃ GAf L n ⧸ U) c = a • c := rfl
    by_cases hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x
    · obtain ⟨x0, hx0, hx0t⟩ := id hc
      have hc' : ∃ y : GAf L n, (y : GAf L n ⧸ U) = (MulAction.toPerm a : GAf L n ⧸ U ≃ GAf L n ⧸ U) c ∧
          TrivOutside {v} y :=
        ⟨a * x0, by rw [hac, ← hx0, MulAction.Quotient.smul_mk, smul_eq_mul], trivOutside_mul hat hx0t⟩
      rw [dif_pos hc, dif_pos hc']
      set x := hc.choose with hxdef
      set y := hc'.choose with hydef
      have hx := hc.choose_spec
      have hy := hc'.choose_spec
      rw [← hxdef] at hx
      rw [← hydef] at hy
      have hq : ((a * x : GAf L n) : GAf L n ⧸ U) = (y : GAf L n ⧸ U) := by
        rw [hy.1, hac, ← hx.1, MulAction.Quotient.smul_mk, smul_eq_mul]
      have hrU : (a * x)⁻¹ * y ∈ U := QuotientGroup.eq.1 hq
      have hrt : TrivOutside {v} ((a * x)⁻¹ * y) :=
        trivOutside_mul (trivOutside_inv (trivOutside_mul hat hx.2)) hy.2
      have hrM : (a * x)⁻¹ * y ∈ Umax L n := (hU _ hrt).1 hrU
      have hye : y = a * x * ((a * x)⁻¹ * y) := by group
      have hloc : Dv.loc y = Dv.loc a * Dv.loc x * Dv.loc ((a * x)⁻¹ * y) := by
        conv_lhs => rw [hye]
        show locHom Dv _ = locHom Dv a * locHom Dv x * locHom Dv _
        rw [map_mul, map_mul]
      have hfy : f (g * y) = f (g * a * x) := by
        conv_lhs => rw [hye]
        rw [← hfr _ hrU (g * a * x)]
        simp only [mul_assoc]
      rw [hfy, hloc, hval_mul_KU Dv h hbi ⟨Dv.loc a, loc_mem_GU Dv a⟩ ⟨Dv.loc _, loc_mem_GU Dv _⟩
        (loc_mem_KU Dv a haM) (loc_mem_KU Dv _ hrM) (Dv.loc x)]
    · have hc' : ¬ ∃ y : GAf L n, (y : GAf L n ⧸ U) = (MulAction.toPerm a : GAf L n ⧸ U ≃ GAf L n ⧸ U) c ∧
          TrivOutside {v} y := by
        rintro ⟨y, hy1, hy2⟩
        refine hc ⟨a⁻¹ * y, ?_, trivOutside_mul (trivOutside_inv hat) hy2⟩
        have e : ((a⁻¹ * y : GAf L n) : GAf L n ⧸ U) = a⁻¹ • (y : GAf L n ⧸ U) := by
          rw [MulAction.Quotient.smul_mk, smul_eq_mul]
        rw [e, hy1, hac]
        exact inv_smul_smul a c
      rw [dif_neg hc, dif_neg hc']
  funext g
  show heckeFunI L n U Dv h f (g * (a * b)) = heckeFunI L n U Dv h f g
  rw [h1, h2]
