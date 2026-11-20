import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.SecondProjWeightVectorZero

noncomputable section

namespace PIW.MassDataColumns

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets Formalism.L2.SG.Measures Formalism.L2.SG.Sub
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain Formalism.FourierDecayAlt.S3 MassDataIdxSteps MassDataIdxStIm MassDataIdxSpl
open scoped Matrix TensorProduct

variable {D : D7}

/- English proof (translation)
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules.
-/
theorem hEmb_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {r k : ℕ} (M : Matrix (Fin k) (Fin k) A) :
    (hEmb r M).map f = hEmb r (M.map f) := by
  unfold hEmb midEmb
  simp only [Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero f), Matrix.map_one _ (map_zero f) (map_one f)]

section Vec

variable (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)
  (Q : GL (Idx D.R.rS D.R.k) (FpX X p))

def mkVec (w : Idx D.R.rS D.R.k → FpX X p) : Fin X.B.I.n → TpX X p :=
  fun m => θ.symm (((Q : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p)) *ᵥ w) ((idxEquiv X) m), 0)

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
-/
theorem firstProj_mkVec_eq_mulVec (w : Idx D.R.rS D.R.k → FpX X p) :
    pr1 θ (mkVec X p θ Q w) ∘ (idxEquiv X).symm = (Q : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p)) *ᵥ w := by
  funext i
  simp [pr1, mkVec]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
-/
theorem secondProj_mkVec_zero (w : Idx D.R.rS D.R.k → FpX X p) : pr2 θ (mkVec X p θ Q w) = 0 := by
  funext m
  simp [pr2, mkVec]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem crd_mkVec (w : Idx D.R.rS D.R.k → FpX X p) : crd X p θ Q (mkVec X p θ Q w) = w := by
  unfold crd
  rw [firstProj_mkVec_eq_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Apply function extensionality and compare values at an arbitrary argument. Reduce the claim to the hypotheses of an applicable result.

Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem eq_of_crd (v w : Fin X.B.I.n → TpX X p) (h1 : crd X p θ Q v = crd X p θ Q w) (h2 : pr2 θ v = pr2 θ w) :
    v = w := by
  have h3 : pr1 θ v ∘ (idxEquiv X).symm = pr1 θ w ∘ (idxEquiv X).symm := by
    have := congrArg (fun x => (Q : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p)) *ᵥ x) h1
    simpa [crd, Matrix.mulVec_mulVec] using this
  funext m
  apply θ.injective
  have hm := congrFun h3 (idxEquiv X m)
  have hm2 := congrFun h2 m
  simp only [Function.comp_apply, Equiv.symm_apply_apply] at hm
  simp only [pr1, pr2] at hm hm2
  exact Prod.ext hm hm2

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem oep_int (hL : LatBasis X p θ (reindex₂ X p Q)) (t : TpX X p) (ht : t ∈ OEp X p) :
    (θ t).1 ∈ p.1.adicCompletionIntegers X.B.I.F := by
  have hk : Nonempty (Idx D.R.rS D.R.k) := by
    have hn := imA_n_pos X
    rw [← card_idx X] at hn
    exact Fintype.card_pos_iff.1 hn
  obtain ⟨s0⟩ := hk
  set μ := mkVec X p θ Q (Pi.single s0 1) with hμ
  have hμL : μ ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by
    refine lat_of_crd X p θ Q hL μ (secondProj_mkVec_zero X p θ Q _) fun s => ?_
    rw [crd_mkVec]
    by_cases hs : s = s0
    · subst hs; simp
    · simp [Pi.single_apply, hs]
  have h2 := crd_int_of_lat X p θ Q hL _ (imA_lat_OEp X p ht hμL) s0
  rw [crd_smul, crd_mkVec] at h2
  simpa using h2

end Vec

end PIW.MassDataColumns
