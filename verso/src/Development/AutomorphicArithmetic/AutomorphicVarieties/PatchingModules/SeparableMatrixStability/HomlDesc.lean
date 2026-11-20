import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.MapEta

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Assume the hypotheses and unpack their components.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Pa.homl_desc :
    ∀ (l : ℕ) [Fact l.Prime] (Γ Γ' : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] [Group Γ'] [TopologicalSpace Γ'] [IsTopologicalGroup Γ'] [CompactSpace Γ'] [TotallyDisconnectedSpace Γ'] (f : Γ →* Γ') (H : Subgroup Γ'), Continuous f → Function.Surjective f → Finite (HomL l (H.comap f)) → Finite (HomL l H) ∧ Nat.card (HomL l H) ≤ Nat.card (HomL l (H.comap f)) := by
  intro l _ Γ Γ' _ _ _ _ _ _ _ _ _ _ f H hf hsurj hfin
  let g : (H.comap f) →* H := f.subgroupComap H
  have hg : Continuous g := (hf.comp continuous_subtype_val).subtype_mk _
  have hgs : Function.Surjective g := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hsurj y
    exact ⟨⟨x, hy⟩, rfl⟩
  let Φ : HomL l H → HomL l (H.comap f) := fun φ =>
    ⟨φ.1.comp g, by
      show IsOpen (g ⁻¹' (φ.1.ker : Set H))
      exact φ.2.preimage hg⟩
  have hinj : Function.Injective Φ := by
    intro φ ψ h
    apply Subtype.ext
    apply MonoidHom.ext
    intro y
    obtain ⟨x, rfl⟩ := hgs y
    have := congrArg (fun χ : HomL l (H.comap f) => χ.1 x) h
    simpa [Φ] using this
  have hF : Finite (HomL l H) := Finite.of_injective Φ hinj
  exact ⟨hF, Nat.card_le_card_of_injective Φ hinj⟩
