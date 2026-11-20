import Formalism.SatakeDualWeyl.Statement

noncomputable section

namespace Formalism.UG.P

open Formalism.UG

variable {G : Type} [Group G] (K : Subgroup G)

/- English proof (translation)
Both sides reduce to the same expression.
-/
private lemma smul_quotient_mk (g x : G) : (g • (x : G ⧸ K)) = ((g * x : G) : G ⧸ K) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
private lemma subgroup_smul_quotient_mk (k : K) (x : G) : (k • (x : G ⧸ K)) = (((k : G) * x : G) : G ⧸ K) := rfl

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Simplify using the standard rewrite rules. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities.

Simplify to obtain the desired conclusion from the available facts.
-/
theorem stabilizer_coset_eq (s : G) :
    MulAction.stabilizer K ((s : G ⧸ K)) = (K.map (MulAut.conj s).toMonoidHom).subgroupOf K := by
  ext k
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_map, subgroup_smul_quotient_mk,
    QuotientGroup.eq]
  constructor
  · intro hk
    refine ⟨s⁻¹ * k * s, ?_, ?_⟩
    · have := K.inv_mem hk
      simpa [mul_assoc] using this
    · simp [MulAut.conj_apply, mul_assoc]
  · rintro ⟨t, ht, hts⟩
    rw [← hts]
    simpa [MulAut.conj_apply, mul_assoc] using K.inv_mem ht

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem orbit_coset_finite (hK : IsCommensurated K) (s : G) :
    (MulAction.orbit K ((s : G ⧸ K))).Finite := by
  have h1 : ((K.map (MulAut.conj s).toMonoidHom).subgroupOf K).index ≠ 0 := hK s
  rw [← stabilizer_coset_eq] at h1
  haveI : Finite (K ⧸ MulAction.stabilizer K ((s : G ⧸ K))) := Nat.finite_of_card_ne_zero h1
  exact Set.finite_coe_iff.mp ((MulAction.orbitEquivQuotientStabilizer K _).finite_iff.mpr this)

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Apply an available result and prove the equalities needed to match it to the conclusion.

A detailed English derivation is pending.
-/
theorem finite_supp_translate (hK : IsCommensurated K) {k : Type} [Zero k] (f : G → k)
    (hf : FinDosetSupp K f) (h : G) :
    {x : G ⧸ K | f (h * x.out) ≠ 0}.Finite := by
  obtain ⟨S, hS⟩ := hf
  refine (S.finite_toSet.biUnion fun s _ =>
    (orbit_coset_finite K hK s).image (fun y : G ⧸ K => h⁻¹ • y)).subset ?_
  intro x hx
  obtain ⟨s, hs, a, b, hab⟩ := hS _ hx
  refine Set.mem_biUnion (Finset.mem_coe.2 hs) ⟨a • ((s : G ⧸ K)), ⟨a, rfl⟩, ?_⟩
  simp only [smul_quotient_mk, subgroup_smul_quotient_mk]
  rw [← QuotientGroup.out_eq' x, QuotientGroup.eq]
  have hx' : x.out = h⁻¹ * ((a : G) * s * b) := by rw [← hab]; group
  rw [hx']
  convert b.2 using 1
  group

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Apply an available result and prove the equalities needed to match it to the conclusion.

A detailed English derivation is pending.
-/
theorem finite_supp_inv (hK : IsCommensurated K) {k : Type} [Zero k] (f : G → k)
    (hf : FinDosetSupp K f) (g : G) :
    {y : G ⧸ K | f (y.out⁻¹ * g) ≠ 0}.Finite := by
  obtain ⟨S, hS⟩ := hf
  refine (S.finite_toSet.biUnion fun s _ =>
    (orbit_coset_finite K hK s⁻¹).image (fun y : G ⧸ K => g • y)).subset ?_
  intro y hy
  obtain ⟨s, hs, a, b, hab⟩ := hS _ hy
  refine Set.mem_biUnion (Finset.mem_coe.2 hs) ⟨b⁻¹ • (((s⁻¹ : G)) : G ⧸ K), ⟨b⁻¹, rfl⟩, ?_⟩
  simp only [smul_quotient_mk, subgroup_smul_quotient_mk, Subgroup.coe_inv]
  rw [← QuotientGroup.out_eq' y, QuotientGroup.eq]
  have hy' : y.out = g * ((a : G) * s * b)⁻¹ := by rw [← hab]; group
  rw [hy']
  convert K.inv_mem a.2 using 1
  group

end Formalism.UG.P
