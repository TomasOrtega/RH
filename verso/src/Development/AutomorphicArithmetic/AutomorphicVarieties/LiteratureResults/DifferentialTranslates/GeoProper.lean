import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.SecondFromFirstStatement
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.BoundInf
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.FinField
open UpperTheory.V.Lit.Dr
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af

/- English proof (translation)
Introduce `E _ _ _ a ho U Ξ hU K hK hKc s s'`. Take `⟨C, hC⟩` from `boundInf E a K hK hKc`. Take `⟨x, rfl⟩` from `QuotientGroup.mk_surjective s`. Take `⟨x', rfl⟩` from `QuotientGroup.mk_surjective s'`. Establish `hT : ∀ i j : Fin a, IsCompact ((fun u : GL (Fin a) (Af E) => (x' * u * x⁻¹).val i j) '' (U : Set (GL (Fin a) (Af E))))`.

Introduce `i j`. Use `hU.image ?_` and prove the remaining obligations. Establish `h1 : Continuous fun u : GL (Fin a) (Af E) => (x' * u * x⁻¹).val` using `Units.continuous_val.comp ((continuous_const.mul continuous_id).mul continuous_const)`. Conclude with `h1.matrix_elem i j`. Establish `hF` using `Set.Finite.pi' fun i : Fin a => Set.Finite.pi' fun j : Fin a => finField E C _ (hT i j)`.

Establish `hinj : Function.Injective fun (γ : (⊤ : Subgroup (GL (Fin a) E))) (i j : Fin a) => γ.1.val i j`. Introduce `γ δ h`. Conclude with `Subtype.ext (Units.ext (Matrix.ext fun i j => congrFun (congrFun h i) j))`. Use `(hF.preimage hinj.injOn).subset ?_` and prove the remaining obligations. Introduce and unpack `γ ⟨hσ, p, hp, hp'⟩ i j`.

Use `⟨fun w => ?_, ?_⟩` and prove the remaining obligations. Establish `h` using `hC _ p hp hp'`. Establish `h2 : ‖toL (GeneralLinearGroup.map (pInf E) (ratGL E a γ.1)).val i j w‖ ≤ C` using `((norm_le_pi_norm _ w).trans ((norm_le_pi_norm _ j).trans (norm_le_pi_norm _ i))).trans h`. Establish `h3 : toL (GeneralLinearGroup.map (pInf E) (ratGL E a γ.1)).val i j w = pInf E (algebraMap E (Ad E) (γ.1.val i j)) w` using `rfl`. Rewrite `h2` using `[h3, pInf_algebraMap, InfinitePlace.norm_embedding_eq]`. Then use the resulting hypothesis.

Rewrite `hσ` using `[geo_σ, MulAction.Quotient.smul_mk, eq_comm, QuotientGroup.eq]`. Use `⟨_, hσ, ?_⟩` and prove the remaining obligations. Establish `h4 : x' * (x'⁻¹ * (GeneralLinearGroup.map (algebraMap E (Af E)) γ.1 • x)) * x⁻¹ = GeneralLinearGroup.map (algebraMap E (Af E)) γ.1`. Rewrite using `[smul_eq_mul]`. Use `group`.

Use `beta_reduce`. Rewrite using `[h4]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.V.Lit.Dr.geoProper :
    GeoProper := by
  intro E _ _ _ a ho U Ξ hU K hK hKc s s'
  obtain ⟨C, hC⟩ := boundInf E a K hK hKc
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
  obtain ⟨x', rfl⟩ := QuotientGroup.mk_surjective s'
  have hT : ∀ i j : Fin a, IsCompact
      ((fun u : GL (Fin a) (Af E) => (x' * u * x⁻¹).val i j) '' (U : Set (GL (Fin a) (Af E)))) := by
    intro i j
    refine hU.image ?_
    have h1 : Continuous fun u : GL (Fin a) (Af E) => (x' * u * x⁻¹).val :=
      Units.continuous_val.comp ((continuous_const.mul continuous_id).mul continuous_const)
    exact h1.matrix_elem i j
  have hF := Set.Finite.pi' fun i : Fin a => Set.Finite.pi' fun j : Fin a => finField E C _ (hT i j)
  have hinj : Function.Injective fun (γ : (⊤ : Subgroup (GL (Fin a) E))) (i j : Fin a) => γ.1.val i j := by
    intro γ δ h
    exact Subtype.ext (Units.ext (Matrix.ext fun i j => congrFun (congrFun h i) j))
  refine (hF.preimage hinj.injOn).subset ?_
  rintro γ ⟨hσ, p, hp, hp'⟩ i j
  refine ⟨fun w => ?_, ?_⟩
  · have h := hC _ p hp hp'
    have h2 : ‖toL (GeneralLinearGroup.map (pInf E) (ratGL E a γ.1)).val i j w‖ ≤ C :=
      ((norm_le_pi_norm _ w).trans ((norm_le_pi_norm _ j).trans (norm_le_pi_norm _ i))).trans h
    have h3 : toL (GeneralLinearGroup.map (pInf E) (ratGL E a γ.1)).val i j w
        = pInf E (algebraMap E (Ad E) (γ.1.val i j)) w := rfl
    rwa [h3, pInf_algebraMap, InfinitePlace.norm_embedding_eq] at h2
  · rw [geo_σ, MulAction.Quotient.smul_mk, eq_comm, QuotientGroup.eq] at hσ
    refine ⟨_, hσ, ?_⟩
    have h4 : x' * (x'⁻¹ * (GeneralLinearGroup.map (algebraMap E (Af E)) γ.1 • x)) * x⁻¹
        = GeneralLinearGroup.map (algebraMap E (Af E)) γ.1 := by
      rw [smul_eq_mul]; group
    beta_reduce
    rw [h4]
    rfl
