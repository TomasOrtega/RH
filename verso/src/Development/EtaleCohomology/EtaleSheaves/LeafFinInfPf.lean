import Development.EtaleCohomology.EtaleSheaves.LeafOrdInfLocalPf

namespace LateralTheory.E.E4

open Polynomial

/- English proof (translation)
Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem finInf_comm {k B L : Type} [Field k] [CommRing B] [Field L] [Algebra k B] [Algebra k L]
    [Algebra B L] [IsScalarTower k B L] (g : Polynomial k →ₐ[k] B) (p : Polynomial k) :
    aeval (algebraMap B L (g X)) p = algebraMap B L (g p) := by
  have h : (aeval (algebraMap B L (g X)) : Polynomial k →ₐ[k] L) =
      (IsScalarTower.toAlgHom k B L).comp g := by
    apply Polynomial.algHom_ext
    simp
  rw [h]; rfl

/- English proof (translation)
Establish an intermediate fact. Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem finInf_integral {k B L : Type} [Field k] [CommRing B] [Field L] [Algebra k B] [Algebra k L]
    [Algebra B L] [IsScalarTower k B L] (g : Polynomial k →ₐ[k] B) (hf : g.Finite)
    (K : IntermediateField k L) (hT : algebraMap B L (g X) ∈ K) (b : B) :
    IsIntegral K (algebraMap B L b) := by
  have hi : g.toRingHom.IsIntegral := RingHom.IsIntegral.of_finite hf
  obtain ⟨p, hp, hpb⟩ := hi b
  let φ : Polynomial k →ₐ[k] K := aeval (⟨_, hT⟩ : K)
  have hc : (algebraMap K L).comp φ.toRingHom = (algebraMap B L).comp g.toRingHom := by
    refine RingHom.ext fun q => ?_
    have h1 := finInf_comm (L := L) g q
    have h2 := Polynomial.aeval_algebraMap_apply L (⟨_, hT⟩ : K) q
    exact h2.symm.trans h1
  refine ⟨p.map φ.toRingHom, hp.map _, ?_⟩
  rw [eval₂_map, hc, ← Polynomial.hom_eval₂, hpb, map_zero]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the indicated hypotheses using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Simplify to obtain the desired conclusion from the available facts. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Extract witnesses or component facts from the available result. Introduce a local definition for the expression.

Establish an intermediate fact. Establish an intermediate fact. Assume the hypotheses and unpack their components. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities.

Treat this case separately. Treat this case separately. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem LeafFinInf_of : LeafFinInf := by
  intro k B _ _ _ _ _ hft g hg hf
  have hinj : Function.Injective (algebraMap B (FractionRing B)) := IsFractionRing.injective B _
  have htr : Transcendental k (algebraMap B (FractionRing B) (g X)) := by
    rw [transcendental_iff]
    intro p hp
    rw [finInf_comm] at hp
    apply hg
    apply hinj
    simpa using hp
  refine ⟨fun h => htr (IsAlgebraic.inv_iff.mp h), ?_⟩
  set K := IntermediateField.adjoin k {(algebraMap B (FractionRing B) (g X))⁻¹} with hK
  have hT : algebraMap B (FractionRing B) (g X) ∈ K := by
    have : (algebraMap B (FractionRing B) (g X))⁻¹ ∈ K :=
      IntermediateField.subset_adjoin k _ (Set.mem_singleton _)
    simpa using K.inv_mem this
  obtain ⟨S, hS⟩ := hft.out
  let S' : Set (FractionRing B) := algebraMap B (FractionRing B) '' (S : Set B)
  have : Finite S' := (S.finite_toSet.image _).to_subtype
  have hfd : FiniteDimensional K (IntermediateField.adjoin K S') :=
    IntermediateField.finiteDimensional_adjoin (by
      rintro _ ⟨b, -, rfl⟩
      exact finInf_integral g hf K hT b)
  have hB : ∀ b : B, algebraMap B (FractionRing B) b ∈ IntermediateField.adjoin K S' := by
    intro b
    have hb : b ∈ Algebra.adjoin k (S : Set B) := hS ▸ Algebra.mem_top
    induction hb using Algebra.adjoin_induction with
    | mem x hx => exact IntermediateField.subset_adjoin K S' ⟨x, hx, rfl⟩
    | algebraMap r =>
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply k K (FractionRing B)]
      exact IntermediateField.algebraMap_mem _ _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  have htop : IntermediateField.adjoin K S' = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := B) x
    exact div_mem (hB a) (hB b)
  rw [htop] at hfd
  exact IntermediateField.topEquiv.toLinearEquiv.finiteDimensional

end LateralTheory.E.E4
