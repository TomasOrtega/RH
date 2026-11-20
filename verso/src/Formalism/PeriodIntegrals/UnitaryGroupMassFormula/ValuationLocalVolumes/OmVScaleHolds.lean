import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.GramMulTupHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.MulTupDiagonal
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVLatHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.HostStarConj
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.InclRMemOEv
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SelfDualContinuity.SdExistsHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensFibV

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmVc

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  MeasureTheory NumberField IsDedekindDomain PI.DegenerateSiegelWeil.Scale PI.NcVal.OmVc2 PI.VolStabSW PI.VolStabSW.TensAllW
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

/- English proof (translation)
Use `Fin.addCases (fun a => ?_) (fun b => ?_) i` and prove the remaining obligations. Rewrite using `[scl, Fin.append_left]`. Conclude with `OmW.alp_ne_zero v _ _`. Rewrite using `[scl, Fin.append_right]`. Conclude with `inv_ne_zero (OmW.alp_ne_zero v _ _)`.
-/
theorem scl_ne_zero (v : PlX X) (i : Fin (D.R.rS + 1 + D.R.rS)) : scl X v i ≠ 0 := by
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · rw [scl, Fin.append_left]; exact OmW.alp_ne_zero v _ _
  · rw [scl, Fin.append_right]; exact inv_ne_zero (OmW.alp_ne_zero v _ _)

/- English proof (translation)
Use `Fin.addCases (fun a => ?_) (fun b => ?_) i` and prove the remaining obligations. Use `Fin.lastCases ?_ (fun j => ?_) a` and prove the remaining obligations. Rewrite using `[OmW.pivot_castAdd_last, scl, Fin.append_left, OmW.alp_last, inv_one]`. Rewrite using `[OmW.piv_e, scl, Fin.append_left, Fin.append_right]`. Rewrite using `[OmW.piv_f, scl, Fin.append_left, Fin.append_right, inv_inv]`.
-/
theorem scl_piv (v : PlX X) (i : Fin (D.R.rS + 1 + D.R.rS)) :
    scl X v (OmW.piv D.R.rS i) = (scl X v i)⁻¹ := by
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · refine Fin.lastCases ?_ (fun j => ?_) a
    · rw [OmW.pivot_castAdd_last, scl, Fin.append_left, OmW.alp_last, inv_one]
    · rw [OmW.piv_e, scl, Fin.append_left, Fin.append_right]
  · rw [OmW.piv_f, scl, Fin.append_left, Fin.append_right, inv_inv]

def dU (v : PlX X) (i : Fin (D.R.rS + 1 + D.R.rS)) : (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)ˣ where
  val := sc (E := X.B.I.E) v (scl X v i)
  inv := sc (E := X.B.I.E) v (scl X v i)⁻¹
  val_inv := by
    rw [sc, sc, Algebra.TensorProduct.tmul_mul_tmul, mul_inv_cancel₀ (scl_ne_zero X v i), one_mul,
      Algebra.TensorProduct.one_def]
  inv_val := by
    rw [sc, sc, Algebra.TensorProduct.tmul_mul_tmul, inv_mul_cancel₀ (scl_ne_zero X v i), one_mul,
      Algebra.TensorProduct.one_def]

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use `show sc (E := X.B.I.E) v (scl X v (OmW.piv D.R.rS i)) = sc (E := X.B.I.E) v (scl X v i)⁻¹`. Rewrite using `[scl_piv]`.
-/
theorem dU_piv (v : PlX X) (i : Fin (D.R.rS + 1 + D.R.rS)) : dU X v (OmW.piv D.R.rS i) = (dU X v i)⁻¹ := by
  apply Units.ext
  show sc (E := X.B.I.E) v (scl X v (OmW.piv D.R.rS i)) = sc (E := X.B.I.E) v (scl X v i)⁻¹
  rw [scl_piv]

/- English proof (translation)
Use `show _ = mulTup (Matrix.diagonal fun i => (dU X v i : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) _`. Rewrite using `[mulTup_diagonal]`. Use function extensionality and compare the values at `j i`. Both sides reduce to the same expression.
-/
theorem yTup_eq (v : PlX X) :
    yTup X u' v = mulTup ((diagUnit (dU X v) : (Matrix _ _ _)ˣ) : Matrix _ _ _)
      (ratTup (Fv X.B.I.F v) (tupH (frameOf X u'))) := by
  show _ = mulTup (Matrix.diagonal fun i => (dU X v i : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) _
  rw [mulTup_diagonal]
  funext j i
  rfl

/- English proof (translation)
Use function extensionality and compare the values at `a b`. Conclude with `OmW.hR_ratTup (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J _ a b`.
-/
theorem gram_ratTup (v : PlX X) :
    gramR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (ratTup (Fv X.B.I.F v) (tupH (frameOf X u'))) = localGramMatrixFrame X u' v := by
  funext a b
  exact OmW.hR_ratTup (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J _ a b

/- English proof (translation)
Rewrite using `[mulTup_diagonal, mulTup_diagonal]`. Use function extensionality and compare the values at `j i`. Use `show g.mulVec (f j • Y j) i = f j * g.mulVec (Y j) i`. Rewrite using `[Matrix.mulVec_smul]`. Both sides reduce to the same expression.
-/
theorem act_mulTup {K : Type} [CommRing K] {a M : ℕ} (g : Matrix (Fin M) (Fin M) K) (f : Fin a → K)
    (Y : Fin a → Fin M → K) :
    (fun j => g.mulVec (mulTup (Matrix.diagonal f) Y j)) = mulTup (Matrix.diagonal f) (fun j => g.mulVec (Y j)) := by
  rw [mulTup_diagonal, mulTup_diagonal]
  funext j i
  show g.mulVec (f j • Y j) i = f j * g.mulVec (Y j) i
  rw [Matrix.mulVec_smul]
  rfl

/- English proof (translation)
Establish `hc : ∀ k : HA (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J, k • yTup X u' v = mulTup ((diagUnit (dU X v) : (Matrix _ _ _)ˣ) : Matrix _ _ _) (k • ratTup (Fv X.B.I.F v) (tupH (frameOf X u')))`. Introduce `k`. Rewrite using `[yTup_eq]`. Conclude with `act_mulTup _ _ _`. Use extensionality with `Y`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨k, hk, rfl⟩`. Conclude with `⟨_, ⟨k, hk, rfl⟩, (hc k).symm⟩`. Introduce and unpack `⟨Z, ⟨k, hk, rfl⟩, rfl⟩`. Conclude with `⟨k, hk, (hc k).symm⟩`.
-/
theorem orbit_eq (v : PlX X) :
    {Y | ∃ k ∈ Kv X.B.I.cm.sig X.B.I.J (abelian₂ X) v, Y = k • yTup X u' v} =
      mulTup ((diagUnit (dU X v) : (Matrix _ _ _)ˣ) : Matrix _ _ _) ''
        {Y | ∃ k ∈ Kv X.B.I.cm.sig X.B.I.J (abelian₂ X) v, Y = k • ratTup (Fv X.B.I.F v) (tupH (frameOf X u'))} := by
  have hc : ∀ k : HA (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J,
      k • yTup X u' v = mulTup ((diagUnit (dU X v) : (Matrix _ _ _)ˣ) : Matrix _ _ _)
        (k • ratTup (Fv X.B.I.F v) (tupH (frameOf X u'))) := by
    intro k
    rw [yTup_eq]
    exact act_mulTup _ _ _
  ext Y
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨_, ⟨k, hk, rfl⟩, (hc k).symm⟩
  · rintro ⟨Z, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨k, hk, (hc k).symm⟩

/- English proof (translation)
Introduce `h1 h2 v`. Establish `hS` using `OmW.omVStd_holds X ψ h1 h2`. Establish `hσ : ∀ x, X.B.I.cm.sig (X.B.I.cm.sig x) = x` using `PI.VolStabSW.sigma_invol _ hS.1.2.2.2`. Establish `hJ : ∀ i j, X.B.I.cm.sig (X.B.I.J j i) = X.B.I.J i j` using `hS.2.1.1`. Establish `: FiniteDimensional X.B.I.F X.B.I.E` using `Module.finite_of_finrank_pos (by rw [hS.1.2.2.1]; norm_num)`.

Rewrite using `[orbit_eq]`. Unfold `omAt`. Use `split_ifs with hT`. Use `swap`. Both sides reduce to the same expression.

Unfold `omFam`. Use `split_ifs with hfib`. Use `swap`. Both sides reduce to the same expression. Use `PI.VolStabSW.secondCountable_Fv X.B.I.F v` as an intermediate fact.

Use `PI.VolStabSW.locallyCompact_Fv X.B.I.F v` as an intermediate fact. Establish `: SecondCountableTopology (Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E))` using `inferInstanceAs (SecondCountableTopology (Fin (D.R.rS + 1 + D.R.rS) → Fin (D.R.rS + 1 + D.R.rS) → Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E))`. Establish `: SecondCountableTopology (HermR (Fv X.B.I.F v) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS))` using `TopologicalSpace.Subtype.secondCountableTopology _`. Establish `hEx` using `PI.SelfDualBridge.W.sdExists_holds X.B.I.cm.sig X.B.I.J ψ v (D.R.rS + 1 + D.R.rS) (Fin 1) hS`. Establish `hμ : SdW X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J (Fv X.B.I.F v) (psiV X.B.I.F ψ v) (D.R.rS + 1 + D.R.rS) (dX X.B.I.cm.sig X.B.I.J ψ v (D.R.rS + 1 + D.R.rS))`.

Unfold `dX`. Rewrite using `[dif_pos hEx.1]`. Conclude with `hEx.1.choose_spec`. Establish `hν : SdHerm X.B.I.F X.B.I.E X.B.I.cm.sig (Fv X.B.I.F v) (psiV X.B.I.F ψ v) (D.R.rS + 1 + D.R.rS) (dT X.B.I.cm.sig ψ v (D.R.rS + 1 + D.R.rS))`. Unfold `dT`.

Rewrite using `[dif_pos hEx.2.1]`. Conclude with `hEx.2.1.choose_spec`. Use `hμ.1` as an intermediate fact. Use `hν.1` as an intermediate fact. Establish `hπ : ∀ i, (Function.Involutive.toPerm _ (OmW.piv_invol D.R.rS)) ((Function.Involutive.toPerm _ (OmW.piv_invol D.R.rS)) i) = i` using `fun i => OmW.piv_invol D.R.rS i`.

Establish `hd : ∀ i, dU X v ((Function.Involutive.toPerm _ (OmW.piv_invol D.R.rS)) i) = (dU X v i)⁻¹` using `fun i => dU_piv X v i`. Establish `hfix : hermMap (Fv X.B.I.F v) X.B.I.cm.sig hσ ((diagUnit (dU X v) : (Matrix _ _ _)ˣ) : Matrix _ _ _) ⟨localGramMatrixFrame X u' v, hT⟩ = ⟨localGramMatrixFrame X u' v, hT⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hermMap_coe]`. Use `show _ * localGramMatrixFrame X u' v * _ = localGramMatrixFrame X u' v`.

Establish `hg` using `OmW.omVGram_holds X u' v`. Rewrite `hg` using `[yTup_eq, PI.NcVal.OmVc1.gramMulTup_holds _ _ _ _ _ _ _ _ _, gram_ratTup]`. Conclude with `hg`. Establish `key` using `fib_image_mulTup X.B.I.cm.sig hσ X.B.I.J hJ (Fv X.B.I.F v) PI.NcVal.OmVc1.gramMulTup_holds (PI.VolStabSW.isOpen_units_Fv X.B.I.F v) (lip_field _) _ _ hfib.choose hfib.choose_spec (diagUnit (dU X v)) ⟨localGramMatrixFrame X u' v, hT⟩ hfix {Y | ∃ k ∈ Kv X.B.I.cm.sig X.B.I.J (abelia …`. Rewrite `key` using `[cTup_eq_one (Fv X.B.I.F v) (dU X v) _ hπ hd, cHerm_eq_one X.B.I.cm.sig hσ (Fv X.B.I.F v) (dU X v) _ hπ hd]`.

Simplify using `only [ENNReal.coe_one, one_mul] at key`. Conclude with `key.symm`.
-/
theorem omVScale_holds : OmVScale X u' ψ := by
  intro h1 h2 v
  have hS := OmW.omVStd_holds X ψ h1 h2
  have hσ : ∀ x, X.B.I.cm.sig (X.B.I.cm.sig x) = x := PI.VolStabSW.sigma_invol _ hS.1.2.2.2
  have hJ : ∀ i j, X.B.I.cm.sig (X.B.I.J j i) = X.B.I.J i j := hS.2.1.1
  have : FiniteDimensional X.B.I.F X.B.I.E :=
    Module.finite_of_finrank_pos (by rw [hS.1.2.2.1]; norm_num)
  rw [orbit_eq]
  unfold omAt
  split_ifs with hT
  swap
  · rfl
  unfold omFam
  split_ifs with hfib
  swap
  · rfl
  have := PI.VolStabSW.secondCountable_Fv X.B.I.F v
  have := PI.VolStabSW.locallyCompact_Fv X.B.I.F v
  have : SecondCountableTopology (Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS))
      (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) :=
    inferInstanceAs (SecondCountableTopology (Fin (D.R.rS + 1 + D.R.rS) → Fin (D.R.rS + 1 + D.R.rS) →
      Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E))
  have : SecondCountableTopology (HermR (Fv X.B.I.F v) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  have hEx := PI.SelfDualBridge.W.sdExists_holds X.B.I.cm.sig X.B.I.J ψ v (D.R.rS + 1 + D.R.rS) (Fin 1) hS
  have hμ : SdW X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J (Fv X.B.I.F v) (psiV X.B.I.F ψ v)
      (D.R.rS + 1 + D.R.rS) (dX X.B.I.cm.sig X.B.I.J ψ v (D.R.rS + 1 + D.R.rS)) := by
    unfold dX; rw [dif_pos hEx.1]; exact hEx.1.choose_spec
  have hν : SdHerm X.B.I.F X.B.I.E X.B.I.cm.sig (Fv X.B.I.F v) (psiV X.B.I.F ψ v) (D.R.rS + 1 + D.R.rS)
      (dT X.B.I.cm.sig ψ v (D.R.rS + 1 + D.R.rS)) := by
    unfold dT; rw [dif_pos hEx.2.1]; exact hEx.2.1.choose_spec
  have := hμ.1
  have := hν.1
  have hπ : ∀ i, (Function.Involutive.toPerm _ (OmW.piv_invol D.R.rS)) ((Function.Involutive.toPerm _
      (OmW.piv_invol D.R.rS)) i) = i := fun i => OmW.piv_invol D.R.rS i
  have hd : ∀ i, dU X v ((Function.Involutive.toPerm _ (OmW.piv_invol D.R.rS)) i) = (dU X v i)⁻¹ :=
    fun i => dU_piv X v i
  have hfix : hermMap (Fv X.B.I.F v) X.B.I.cm.sig hσ
      ((diagUnit (dU X v) : (Matrix _ _ _)ˣ) : Matrix _ _ _) ⟨localGramMatrixFrame X u' v, hT⟩ = ⟨localGramMatrixFrame X u' v, hT⟩ := by
    apply Subtype.ext
    rw [hermMap_coe]
    show _ * localGramMatrixFrame X u' v * _ = localGramMatrixFrame X u' v
    have hg := OmW.omVGram_holds X u' v
    rw [yTup_eq, PI.NcVal.OmVc1.gramMulTup_holds _ _ _ _ _ _ _ _ _, gram_ratTup] at hg
    exact hg
  have key := fib_image_mulTup X.B.I.cm.sig hσ X.B.I.J hJ (Fv X.B.I.F v) PI.NcVal.OmVc1.gramMulTup_holds
    (PI.VolStabSW.isOpen_units_Fv X.B.I.F v) (lip_field _) _ _ hfib.choose hfib.choose_spec
    (diagUnit (dU X v)) ⟨localGramMatrixFrame X u' v, hT⟩ hfix
    {Y | ∃ k ∈ Kv X.B.I.cm.sig X.B.I.J (abelian₂ X) v, Y = k • ratTup (Fv X.B.I.F v) (tupH (frameOf X u'))}
  rw [cTup_eq_one (Fv X.B.I.F v) (dU X v) _ hπ hd, cHerm_eq_one X.B.I.cm.sig hσ (Fv X.B.I.F v) (dU X v) _ hπ hd]
    at key
  simp only [ENNReal.coe_one, one_mul] at key
  exact key.symm

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmVc
