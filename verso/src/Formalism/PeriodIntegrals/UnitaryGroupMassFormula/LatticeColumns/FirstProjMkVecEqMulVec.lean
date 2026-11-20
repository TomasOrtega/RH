import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.SecondProjWeightVectorZero

noncomputable section

namespace PIW.MassDataColumns

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets Formalism.L2.SG.Measures Formalism.L2.SG.Sub
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain Formalism.FourierDecayAlt.S3 MassDataIdxSteps MassDataIdxStIm MassDataIdxSpl
open scoped Matrix TensorProduct

variable {D : D7}

/- English proof (translation)
Unfold `hEmb midEmb`. Simplify using `only [Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero f), Matrix.map_one _ (map_zero f) (map_one f)]`.
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
Use function extensionality and compare the values at `i`. Simplify using `[pr1, mkVec]`.
-/
theorem firstProj_mkVec_eq_mulVec (w : Idx D.R.rS D.R.k → FpX X p) :
    pr1 θ (mkVec X p θ Q w) ∘ (idxEquiv X).symm = (Q : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p)) *ᵥ w := by
  funext i
  simp [pr1, mkVec]

/- English proof (translation)
Use function extensionality and compare the values at `m`. Simplify using `[pr2, mkVec]`.
-/
theorem secondProj_mkVec_zero (w : Idx D.R.rS D.R.k → FpX X p) : pr2 θ (mkVec X p θ Q w) = 0 := by
  funext m
  simp [pr2, mkVec]

/- English proof (translation)
Unfold `crd`. Rewrite using `[firstProj_mkVec_eq_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]`.
-/
theorem crd_mkVec (w : Idx D.R.rS D.R.k → FpX X p) : crd X p θ Q (mkVec X p θ Q w) = w := by
  unfold crd
  rw [firstProj_mkVec_eq_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

/- English proof (translation)
Establish `h3 : pr1 θ v ∘ (idxEquiv X).symm = pr1 θ w ∘ (idxEquiv X).symm`. Use `congrArg (fun x => (Q : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p)) *ᵥ x) h1` as an intermediate fact. Simplify `this` using `[crd, Matrix.mulVec_mulVec]`. Use function extensionality and compare the values at `m`. Apply `θ.injective` to reduce the goal to its premises.

Establish `hm` using `congrFun h3 (idxEquiv X m)`. Establish `hm2` using `congrFun h2 m`. Simplify using `only [Function.comp_apply, Equiv.symm_apply_apply] at hm`. Simplify using `only [pr1, pr2] at hm hm2`. Conclude with `Prod.ext hm hm2`.
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
Establish `hk : Nonempty (Idx D.R.rS D.R.k)`. Establish `hn` using `imA_n_pos X`. Rewrite `hn` using `[← card_idx X]`. Conclude with `Fintype.card_pos_iff.1 hn`. Take `⟨s0⟩` from `hk`.

Use `set μ := mkVec X p θ Q (Pi.single s0 1) with hμ`. Establish `hμL : μ ∈ latLoc (E` using `X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by`. Use `lat_of_crd X p θ Q hL μ (secondProj_mkVec_zero X p θ Q _) fun s => ?_` and prove the remaining obligations. Rewrite using `[crd_mkVec]`. Distinguish the cases in `hs : s = s0`.

Substitute `hs` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, hs]`. Establish `h2` using `crd_int_of_lat X p θ Q hL _ (imA_lat_OEp X p ht hμL) s0`. Rewrite `h2` using `[crd_smul, crd_mkVec]`.

Simplify using `using h2`.
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
