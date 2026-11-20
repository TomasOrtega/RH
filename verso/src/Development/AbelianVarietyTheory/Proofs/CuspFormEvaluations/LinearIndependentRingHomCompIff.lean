import Mathlib

namespace GlobalTheory

/- English proof (translation)
Equip the data with the indicated structure. A detailed English derivation is pending.
-/
theorem linearIndependent_ringHom_comp_iff {A F : Type} [CommRing A] [Field F] (φ : A →+* F)
    (hφ : Function.Injective φ) {ι μ : Type} [Finite μ] (c : ι → μ → A) :
    LinearIndependent F (fun i m => φ (c i m)) ↔ LinearIndependent A c := by
  letI : Algebra A F := φ.toAlgebra
  haveI : FaithfulSMul A F := (faithfulSMul_iff_algebraMap_injective A F).2 hφ
  exact linearIndependent_algebraMap_comp_iff (R := A) (S := F) (v := c)

/- English proof (translation)
Extract witnesses or component facts from the available result. Equip the data with the indicated structure. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Assume the hypotheses and unpack their components. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem finrank_span_ringHom_comp_le {A F F' : Type} [CommRing A] [Field F] [Field F']
    (φ : A →+* F) (ψ : A →+* F') (hφ : Function.Injective φ) (hψ : Function.Injective ψ)
    {ι μ : Type} [Finite ι] [Finite μ] (c : ι → μ → A) :
    Module.finrank F (Submodule.span F (Set.range fun i m => φ (c i m))) ≤
      Module.finrank F' (Submodule.span F' (Set.range fun i m => ψ (c i m))) := by
  obtain ⟨κ, a, ha, hs, hl⟩ := exists_linearIndependent' F (fun i m => φ (c i m))
  haveI : Finite κ := Finite.of_injective a ha
  letI : Fintype κ := Fintype.ofFinite κ
  have h1 : LinearIndependent A (fun k => c (a k)) :=
    (linearIndependent_ringHom_comp_iff φ hφ (fun k => c (a k))).1 hl
  have h2 : LinearIndependent F' (fun k m => ψ (c (a k) m)) :=
    (linearIndependent_ringHom_comp_iff ψ hψ (fun k => c (a k))).2 h1
  rw [← hs, finrank_span_eq_card hl, ← finrank_span_eq_card h2]
  apply Submodule.finrank_mono
  apply Submodule.span_mono
  rintro _ ⟨k, rfl⟩
  exact ⟨a k, rfl⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem finrank_span_ringHom_comp_eq {A F F' : Type} [CommRing A] [Field F] [Field F']
    (φ : A →+* F) (ψ : A →+* F') (hφ : Function.Injective φ) (hψ : Function.Injective ψ)
    {ι μ : Type} [Finite ι] [Finite μ] (c : ι → μ → A) :
    Module.finrank F (Submodule.span F (Set.range fun i m => φ (c i m))) =
      Module.finrank F' (Submodule.span F' (Set.range fun i m => ψ (c i m))) :=
  le_antisymm (finrank_span_ringHom_comp_le φ ψ hφ hψ c)
    (finrank_span_ringHom_comp_le ψ φ hψ hφ c)

/- English proof (translation)
Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Prove the components needed by the constructor for the conclusion.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem mem_span_iff_finrank_option_eq {F V ι : Type} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (v : Option ι → V) :
    v none ∈ Submodule.span F (Set.range fun i => v (some i)) ↔
      Module.finrank F (Submodule.span F (Set.range fun i => v (some i))) =
        Module.finrank F (Submodule.span F (Set.range v)) := by
  have hle : Submodule.span F (Set.range fun i => v (some i)) ≤ Submodule.span F (Set.range v) := by
    apply Submodule.span_mono
    rintro _ ⟨k, rfl⟩
    exact ⟨some k, rfl⟩
  constructor
  · intro h
    have : Submodule.span F (Set.range fun i => v (some i)) = Submodule.span F (Set.range v) := by
      refine le_antisymm hle (Submodule.span_le.2 ?_)
      rintro _ ⟨_ | k, rfl⟩
      · exact h
      · exact Submodule.subset_span ⟨k, rfl⟩
    rw [this]
  · intro h
    rw [Submodule.eq_of_le_of_finrank_eq hle h]
    exact Submodule.subset_span ⟨none, rfl⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem rank_indep_mem_embedding_invariant :
    ∀ (A F F' : Type) [CommRing A] [Field F] [Field F'] (φ : A →+* F) (ψ : A →+* F'), Function.Injective φ → Function.Injective ψ → ∀ (ι μ : Type) [Fintype ι] [Fintype μ] (c : ι → μ → A), (LinearIndependent F (fun i m => φ (c i m)) ↔ LinearIndependent F' (fun i m => ψ (c i m))) ∧ (∀ q : μ → A, (fun m => φ (q m)) ∈ Submodule.span F (Set.range fun i m => φ (c i m)) ↔ (fun m => ψ (q m)) ∈ Submodule.span F' (Set.range fun i m => ψ (c i m))) ∧ Module.finrank F (Submodule.span F (Set.range fun i m => φ (c i m))) = Module.finrank F' (Submodule.span F' (Set.range fun i m => ψ (c i m))) := by
  intro A F F' _ _ _ φ ψ hφ hψ ι μ _ _ c
  refine ⟨?_, fun q => ?_, finrank_span_ringHom_comp_eq φ ψ hφ hψ c⟩
  · rw [linearIndependent_ringHom_comp_iff φ hφ, linearIndependent_ringHom_comp_iff ψ hψ]
  · let d : Option ι → μ → A := fun o => o.elim q c
    have h1 := mem_span_iff_finrank_option_eq (F := F) (fun o m => φ (d o m))
    have h2 := mem_span_iff_finrank_option_eq (F := F') (fun o m => ψ (d o m))
    have e1 := finrank_span_ringHom_comp_eq φ ψ hφ hψ c
    have e2 := finrank_span_ringHom_comp_eq φ ψ hφ hψ d
    refine h1.trans (Iff.trans ?_ h2.symm)
    rw [e2]
    exact e1 ▸ Iff.rfl

end GlobalTheory
