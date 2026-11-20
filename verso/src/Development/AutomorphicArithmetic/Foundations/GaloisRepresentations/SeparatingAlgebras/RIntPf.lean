import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StLocB

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument.

Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion repeatedly using the stated equalities. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem UpperTheory.Gal.Gen.rInt_pf :
    UpperTheory.Gal.Gen.InjAE → UpperTheory.Gal.Gen.RDens → UpperTheory.Gal.Gen.HalfInt → UpperTheory.Gal.Gen.DensCont → UpperTheory.Gal.Gen.RInt := by
  intro h1 h2 h3 h4 n t ht0 ht1 l hl
  obtain ⟨hh, -, hev, hnorm⟩ := h4 n t ht0 ht1
  have hpt : ∀ (θ : Fin n → UnitAddCircle) (σ : Equiv.Perm (Fin n)), pt θ ∘ ⇑σ = pt (θ ∘ ⇑σ) :=
    fun _ _ => rfl
  set F : (Fin n → UnitAddCircle) → ℂ := fun θ => monomialChar l (pt θ) * half (t : ℂ) (pt θ) with hF
  have hmc : Continuous fun θ : Fin n → UnitAddCircle => monomialChar l (pt θ) := by
    have := hev (AddMonoidAlgebra.single l 1)
    simpa [evalAt_single] using this
  have hFc : Continuous F := hmc.mul hh
  have hperm : ∀ σ : Equiv.Perm (Fin n),
      ∫ θ : Fin n → UnitAddCircle, F (θ ∘ ⇑σ) = ∫ θ : Fin n → UnitAddCircle, F θ := by
    intro σ
    have hmp := volume_measurePreserving_piCongrLeft (fun _ : Fin n => UnitAddCircle) σ.symm
    rw [← hmp.integral_comp' F]
    congr 1
    funext θ
    congr 1
    funext j
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
  have hae : (fun θ : Fin n → UnitAddCircle => evalAt (pt θ) (hlR (t : ℂ) l) * dens (t : ℂ) (pt θ)) =ᵐ[volume]
      fun θ => ∑ σ : Equiv.Perm (Fin n), F (θ ∘ ⇑σ) := by
    filter_upwards [h1 n] with θ hθ
    rw [h2 n t ht0 ht1 l (pt θ) hθ (hnorm θ)]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [hpt]
  rw [integral_congr_ae hae, integral_finset_sum]
  · simp_rw [hperm]
    rw [hF, h3 n t ht0 ht1 l hl, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
    split_ifs <;> simp
  · intro σ _
    have hc : Continuous fun θ : Fin n → UnitAddCircle => θ ∘ ⇑σ :=
      continuous_pi fun i => continuous_apply (σ i)
    exact (hFc.comp hc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
