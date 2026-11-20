import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.GroupDetAlt

namespace UpperTheory.Gal.Gen

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Establish an intermediate fact. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Use linear arithmetic over natural numbers and integers. A detailed English derivation is pending.
-/
theorem codim_pf : Codim := by
  intro k V M _ _ _ _ _ _ Ψ A B _ h
  let f : V →ₗ[k] M ⧸ A := A.mkQ ∘ₗ Ψ
  have hker : LinearMap.ker f = A.comap Ψ := by
    ext v
    simp [f, Submodule.Quotient.mk_eq_zero]
  have hrange : LinearMap.range f ≤ B.map A.mkQ := by
    rintro _ ⟨v, rfl⟩
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp (h v)
    refine ⟨b, hb, ?_⟩
    have hz : A.mkQ a = 0 := by simpa [Submodule.Quotient.mk_eq_zero] using ha
    simp only [f, LinearMap.comp_apply, ← hab, map_add, hz, zero_add]
  haveI : FiniteDimensional k (B.map A.mkQ) :=
    Module.Finite.map B A.mkQ
  have h1 : Module.finrank k (LinearMap.range f) ≤ Module.finrank k (B.map A.mkQ) :=
    Submodule.finrank_mono hrange
  have h2 : Module.finrank k (B.map A.mkQ) ≤ Module.finrank k B :=
    Submodule.finrank_map_le A.mkQ B
  have h3 := LinearMap.finrank_range_add_finrank_ker f
  rw [hker] at h3
  omega

end UpperTheory.Gal.Gen
