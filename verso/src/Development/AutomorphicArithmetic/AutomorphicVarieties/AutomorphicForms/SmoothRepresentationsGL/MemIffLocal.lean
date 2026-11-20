import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.SphDefs

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

/- English proof (translation)
Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails. Establish an intermediate fact. Simplify using the standard rewrite rules.

Establish an intermediate fact. Simplify using the standard rewrite rules.
-/
private theorem lamS_perm {n : ℕ} (S T : Finset (Fin n)) (h : S.card = T.card) :
    ∃ σ : Equiv.Perm (Fin n), Spherical.lamS T ∘ σ = Spherical.lamS S := by
  classical
  let e : {x // x ∈ S} ≃ {x // x ∈ T} := Finset.equivOfCardEq h
  refine ⟨e.extendSubtype, funext fun i => ?_⟩
  by_cases hi : i ∈ S
  · have := Equiv.extendSubtype_mem e i hi
    simp [Spherical.lamS, hi, this]
  · have := Equiv.extendSubtype_not_mem e i hi
    simp [Spherical.lamS, hi, this]

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Apply an available result and prove the equalities needed to match it to the conclusion. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
private theorem mem_iff_local {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {n r : ℕ} (hr : r ≤ n) (g : GL (Fin n) F) :
    g ∈ Spherical.minusculeSet F n r ↔ ∃ a ∈ GLnLocal.integralGL F n, ∃ b ∈ GLnLocal.integralGL F n,
      (g : Matrix (Fin n) (Fin n) F) = (a : Matrix (Fin n) (Fin n) F) *
        Formalism.UG.diagJ n (GLnLocal.uniformizer F : F) r * (b : Matrix (Fin n) (Fin n) F) := by
  classical
  let T : Finset (Fin n) := Finset.univ.filter fun i => i.val < r
  have hT : T.card = r := by
    simp [T, Fin.card_filter_val_lt, hr]
  have hD : ((Iwasawa.torusPow F n (Spherical.lamS T) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      Formalism.UG.diagJ n (GLnLocal.uniformizer F : F) r := by
    rw [Iwasawa.coe_torusPow, Formalism.UG.diagJ]
    congr 1
    funext i
    by_cases hi : i.val < r <;> simp [Spherical.lamS, T, hi]
  have hU : ∀ (S : Finset (Fin n)) c, Spherical.unipC (F := F) S c ∈ GLnLocal.integralGL F n := by
    intro S c
    have := (Spherical.torusPow_conj_unipC_mem (l := 0) antitone_const S c).2
    have h0 : Iwasawa.torusPow F n 0 = 1 := Units.ext (by simp [Iwasawa.coe_torusPow])
    simpa [h0] using this
  rw [← hD]
  constructor
  · intro hg
    obtain ⟨S, hS, c, hc⟩ := Spherical.exists_gMat hg
    have hk := QuotientGroup.eq.1 hc
    obtain ⟨σ, hσ⟩ := lamS_perm S T (hS.trans hT.symm)
    have hp := GLnLocal.permGL_mem_integralGL F n σ
    refine ⟨_, mul_mem (hU S c) (inv_mem hp), _, mul_mem hp hk, ?_⟩
    rw [← Units.val_mul, ← Units.val_mul]
    congr 1
    have h1 := Spherical.permGL_conj_torusPow (F := F) σ (Spherical.lamS T)
    rw [hσ] at h1
    rw [Spherical.gMat, ← h1]
    group
  · rintro ⟨a, ha, b, hb, e⟩
    rw [← Units.val_mul, ← Units.val_mul] at e
    have e' := Units.ext e
    have h0 := Spherical.gMat_mem_minusculeSet (F := F) T (fun _ => 0)
    rw [hT] at h0
    have := Spherical.mul_mem_minusculeSet h0 (mul_mem ha (inv_mem (hU T fun _ => 0))) hb
    rw [e']
    convert this using 1
    rw [Spherical.gMat]
    group

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

By extensionality, compare the relevant components. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Af.Smo.tjSet :
    UpperTheory.V.Af.Smo.SphDict → UpperTheory.V.Af.Smo.TjSet := by
  intro hd E _ _ n w r hr
  have hK : GLnLocal.integralGL (w.adicCompletion E) n = Formalism.UG.GLint (Fin n) (Formalism.UG.Ov E w) :=
    (hd E n w).1
  unfold Formalism.UG.Tj
  rw [← hK]
  congr 1
  ext g
  exact (mem_iff_local hr g).symm
