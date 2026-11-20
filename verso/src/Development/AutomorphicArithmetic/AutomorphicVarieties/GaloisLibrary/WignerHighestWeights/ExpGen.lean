import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.ExpGenC
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.IsAlgIsoRefl
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualInfinitesimalCharacterRegular
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

/- English proof (translation)
A detailed English derivation is pending.
-/
private theorem exp_map_eval {ι : Type} [Fintype ι] {a : ℕ} (X : Matrix (Fin a) (Fin a) (ι → ℂ)) (w : ι) :
    (NormedSpace.exp X).map (fun x => x w) = NormedSpace.exp (X.map fun x => x w) := by
  open scoped Matrix.Norms.Operator in
  exact NormedSpace.map_exp ((Pi.evalRingHom (fun _ : ι => ℂ) w).mapMatrix (m := Fin a))
    (Continuous.matrix_map continuous_id (continuous_apply w)) X

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Express the relevant assertion in an equivalent form by its definition. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Treat this case separately.

Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
private theorem gen_pi {ι : Type} [Fintype ι] {a : ℕ} (H : Submonoid (Matrix (Fin a) (Fin a) (ι → ℂ)))
    (hH : ∀ X, NormedSpace.exp X ∈ H) (y : Matrix (Fin a) (Fin a) (ι → ℂ)) (hy : IsUnit y) : y ∈ H := by
  classical
  let e : Matrix (Fin a) (Fin a) (ι → ℂ) ≃+* (ι → Matrix (Fin a) (Fin a) ℂ) :=
    Matrix.piRingEquiv (β := fun _ : ι => ℂ)
  have he : ∀ X w, e X w = X.map (fun x => x w) := fun _ _ => rfl
  let H' : Submonoid (ι → Matrix (Fin a) (Fin a) ℂ) := H.comap (e.symm : _ →* _)
  have h1 : ∀ (w : ι) (g : Matrix (Fin a) (Fin a) ℂ), g.det ≠ 0 → Pi.mulSingle w g ∈ H' := by
    intro w g hg
    refine UpperTheory.V.AlgRepEndIrreducible.expGenC a (H'.comap (MonoidHom.mulSingle (fun _ : ι => Matrix (Fin a) (Fin a) ℂ) w)) ?_ g hg
    intro X
    change e.symm (Pi.mulSingle w (NormedSpace.exp X)) ∈ H
    have : e.symm (Pi.mulSingle w (NormedSpace.exp X)) = NormedSpace.exp (e.symm (Pi.single w X)) := by
      rw [RingEquiv.symm_apply_eq]
      funext v
      rw [he, exp_map_eval, ← he, RingEquiv.apply_symm_apply]
      by_cases hv : v = w
      · subst hv
        simp
      · simp [hv]
    rw [this]
    exact hH _
  have h2 : ∀ w, (e y w).det ≠ 0 := by
    intro w
    have : IsUnit (e y w) := (hy.map e).map (Pi.evalRingHom (fun _ : ι => Matrix (Fin a) (Fin a) ℂ) w)
    exact ((Matrix.isUnit_iff_isUnit_det _).1 this).ne_zero
  have h3 : ∀ s : Finset ι, s.piecewise (e y) 1 ∈ H' := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using H'.one_mem
    | insert w s hw ih =>
      have : (insert w s).piecewise (e y) 1 = Pi.mulSingle w (e y w) * s.piecewise (e y) 1 := by
        funext v
        by_cases hv : v = w
        · subst hv
          simp [Finset.piecewise, hw]
        · simp [Finset.piecewise, hv]
      rw [this]
      exact H'.mul_mem (h1 w _ (h2 w)) ih
  have h4 := h3 Finset.univ
  rw [Finset.piecewise_univ] at h4
  have h5 : e.symm (e y) ∈ H := h4
  simpa using h5

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. Extract witnesses or component facts from the available result. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem UpperTheory.V.AlgRepEndIrreducible.expGen :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (H : Submonoid (GL (Fin a) (Cinf E))),
      (∀ (X : Matrix (Fin a) (Fin a) (Cinf E)) (y : GL (Fin a) (Cinf E)), y.val = NormedSpace.exp X → y ∈ H) → ∀ y, y ∈ H := by
  intro E _ _ _ a H hH y
  have h : y.val ∈ H.map (Units.coeHom _) := by
    refine gen_pi (ι := InfinitePlace E) (H.map (Units.coeHom _)) ?_ y.val y.isUnit
    intro X
    obtain ⟨u, hu⟩ := Matrix.isUnit_exp X
    exact ⟨u, hH X u hu, hu⟩
  obtain ⟨u, hu, h'⟩ := h
  have : u = y := Units.ext h'
  exact this ▸ hu
