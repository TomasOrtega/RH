import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.ExpGenC
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.IsAlgIsoRefl
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualInfinitesimalCharacterRegular
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

/- English proof (translation)
Use `open scoped Matrix.Norms.Operator in`. Conclude with `NormedSpace.map_exp ((Pi.evalRingHom (fun _ : ι => ℂ) w).mapMatrix (m := Fin a)) (Continuous.matrix_map continuous_id (continuous_apply w)) X`.
-/
private theorem exp_map_eval {ι : Type} [Fintype ι] {a : ℕ} (X : Matrix (Fin a) (Fin a) (ι → ℂ)) (w : ι) :
    (NormedSpace.exp X).map (fun x => x w) = NormedSpace.exp (X.map fun x => x w) := by
  open scoped Matrix.Norms.Operator in
  exact NormedSpace.map_exp ((Pi.evalRingHom (fun _ : ι => ℂ) w).mapMatrix (m := Fin a))
    (Continuous.matrix_map continuous_id (continuous_apply w)) X

/- English proof (translation)
Set `e : Matrix (Fin a) (Fin a) (ι → ℂ) ≃+* (ι → Matrix (Fin a) (Fin a) ℂ)` to `Matrix.piRingEquiv (β := fun _ : ι => ℂ)`. Establish `he : ∀ X w, e X w = X.map (fun x => x w)` using `fun _ _ => rfl`. Set `H' : Submonoid (ι → Matrix (Fin a) (Fin a) ℂ)` to `H.comap (e.symm : _ →* _)`. Establish `h1 : ∀ (w : ι) (g : Matrix (Fin a) (Fin a) ℂ), g.det ≠ 0 → Pi.mulSingle w g ∈ H'`. Introduce `w g hg`.

Use `UpperTheory.V.AlgRepEndIrreducible.expGenC a (H'.comap (MonoidHom.mulSingle (fun _ : ι => Matrix (Fin a) (Fin a) ℂ) w)) ?_ g hg` and prove the remaining obligations. Introduce `X`. Express the relevant statement in the definitionally equal form `e.symm (Pi.mulSingle w (NormedSpace.exp X)) ∈ H`. Establish `: e.symm (Pi.mulSingle w (NormedSpace.exp X)) = NormedSpace.exp (e.symm (Pi.single w X))`. Rewrite using `[RingEquiv.symm_apply_eq]`.

Use function extensionality and compare the values at `v`. Rewrite using `[he, exp_map_eval, ← he, RingEquiv.apply_symm_apply]`. Distinguish the cases in `hv : v = w`. Substitute `hv` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[hv]`. Rewrite using `[this]`. Conclude with `hH _`. Establish `h2 : ∀ w, (e y w).det ≠ 0`. Introduce `w`.

Establish `: IsUnit (e y w)` using `(hy.map e).map (Pi.evalRingHom (fun _ : ι => Matrix (Fin a) (Fin a) ℂ) w)`. Conclude with `((Matrix.isUnit_iff_isUnit_det _).1 this).ne_zero`. Establish `h3 : ∀ s : Finset ι, s.piecewise (e y) 1 ∈ H'`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`.

Consider the case `empty => simpa using H'.one_mem`. Consider the case `insert w s hw ih`. Establish `: (insert w s).piecewise (e y) 1 = Pi.mulSingle w (e y w) * s.piecewise (e y) 1`. Use function extensionality and compare the values at `v`. Distinguish the cases in `hv : v = w`.

Substitute `hv` using the available equality. Simplify using `[Finset.piecewise, hw]`. Simplify using `[Finset.piecewise, hv]`. Rewrite using `[this]`. Conclude with `H'.mul_mem (h1 w _ (h2 w)) ih`.

Establish `h4` using `h3 Finset.univ`. Rewrite `h4` using `[Finset.piecewise_univ]`. Establish `h5 : e.symm (e y) ∈ H` using `h4`. Simplify using `using h5`.
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
Introduce `E _ _ _ a H hH y`. Establish `h : y.val ∈ H.map (Units.coeHom _)`. Use `gen_pi (ι := InfinitePlace E) (H.map (Units.coeHom _)) ?_ y.val y.isUnit` and prove the remaining obligations. Introduce `X`. Take `⟨u, hu⟩` from `Matrix.isUnit_exp X`.

Conclude with `⟨u, hH X u hu, hu⟩`. Take `⟨u, hu, h'⟩` from `h`. Establish `: u = y` using `Units.ext h'`. Conclude with `this ▸ hu`.
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
