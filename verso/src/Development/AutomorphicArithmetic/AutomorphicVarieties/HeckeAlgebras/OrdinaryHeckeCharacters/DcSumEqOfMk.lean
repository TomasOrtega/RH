import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
open IsLocalRing Matrix UpperTheory.V.Hi

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Chain the equalities or inequalities of the calculation.
-/
private theorem dcSum_eq_of_mk {A H M : Type} [CommRing A] [Group H] [AddCommGroup M] [Module A M]
    (ρ : Representation A H M) (K' : Subgroup H) {v : M} (hv : v ∈ fixd ρ K') {y z : H}
    (h : (y : H ⧸ K') = (z : H ⧸ K')) : ρ y v = ρ z v := by
  have h1 : y⁻¹ * z ∈ K' := QuotientGroup.eq.mp h
  have h2 : ρ (y⁻¹ * z) v = v := hv _ h1
  calc ρ y v = ρ y (ρ (y⁻¹ * z) v) := by rw [h2]
    _ = ρ (y * (y⁻¹ * z)) v := by rw [map_mul ρ y]; rfl
    _ = ρ z v := by rw [mul_inv_cancel_left]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
private theorem dcSum_apply {A H M : Type} [CommRing A] [Group H] [AddCommGroup M] [Module A M]
    (ρ : Representation A H M) (K K' : Subgroup H) (x : H)
    [Fintype (MulAction.orbit K (x : H ⧸ K'))] (v : M) :
    dc ρ K K' x v = ∑ q : MulAction.orbit K (x : H ⧸ K'), ρ (q : H ⧸ K').out v := by
  rw [dc, finsum_eq_sum_of_fintype, LinearMap.sum_apply]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Equip the data with the indicated structure. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Use symmetry to reverse the relation. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Both sides reduce to the same expression. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.

Chain the equalities or inequalities of the calculation. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Hi.dcSum :
    ∀ (A H M : Type) [CommRing A] [Group H] [AddCommGroup M] [Module A M] (ρ : Representation A H M) (K K' : Subgroup H) (x : H), (MulAction.orbit K (x : H ⧸ K')).Finite → (∀ s : Finset H, (∀ y ∈ s, (y : H ⧸ K') ∈ MulAction.orbit K (x : H ⧸ K')) → (∀ q ∈ MulAction.orbit K (x : H ⧸ K'), ∃! y, y ∈ s ∧ (y : H ⧸ K') = q) → ∀ v ∈ fixd ρ K', dc ρ K K' x v = ∑ y ∈ s, ρ y v) ∧ (∀ v ∈ fixd ρ K', dc ρ K K' x v ∈ fixd ρ K) ∧ (∀ V : Subgroup H, (∀ u ∈ V, u * x = x * u ∧ ∀ k ∈ K, u * k = k * u) → ∀ v ∈ fixd ρ K', v ∈ fixd ρ V → dc ρ K K' x v ∈ fixd ρ V) ∧ ∀ (A' M' : Type) [CommRing A'] [AddCommGroup M'] [Module A' M'] (ρ' : Representation A' H M') (f : M →+ M'), (∀ h v, f (ρ h v) = ρ' h (f v)) → ∀ v, f (dc ρ K K' x v) = dc ρ' K K' x (f v) := by
  intro A H M _ _ _ _ ρ K K' x hfin
  letI : Fintype (MulAction.orbit K (x : H ⧸ K')) := hfin.fintype
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hs hu v hv
    rw [dcSum_apply]
    symm
    refine Finset.sum_bij (fun y hy => (⟨(y : H ⧸ K'), hs y hy⟩ : MulAction.orbit K (x : H ⧸ K')))
      (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
    · intro y hy z hz h
      have h' : (y : H ⧸ K') = (z : H ⧸ K') := congrArg Subtype.val h
      exact (hu _ (hs z hz)).unique ⟨hy, h'⟩ ⟨hz, rfl⟩
    · intro q _
      obtain ⟨y, ⟨hy, hq⟩, -⟩ := hu q.1 q.2
      exact ⟨y, hy, Subtype.ext hq⟩
    · intro y hy
      exact dcSum_eq_of_mk ρ K' hv (QuotientGroup.out_eq' _).symm
  · intro v hv u hu
    rw [dcSum_apply, map_sum]
    refine Fintype.sum_equiv (MulAction.toPerm (⟨u, hu⟩ : K)) _ _ ?_
    intro q
    have : ρ u (ρ (q : H ⧸ K').out v) = ρ (u * (q : H ⧸ K').out) v := by rw [map_mul]; rfl
    rw [this]
    apply dcSum_eq_of_mk ρ K' hv
    rw [QuotientGroup.out_eq']
    change _ = u • (q : H ⧸ K')
    conv_rhs => rw [← QuotientGroup.out_eq' (q : H ⧸ K')]
    rfl
  · intro V hV v hv hvV u hu
    rw [dcSum_apply, map_sum]
    refine Finset.sum_congr rfl ?_
    rintro ⟨q, k, hk⟩ _
    have h1 : ρ q.out v = ρ ((k : H) * x) v := by
      apply dcSum_eq_of_mk ρ K' hv
      rw [QuotientGroup.out_eq', ← hk]
      rfl
    have h2 : u * ((k : H) * x) = ((k : H) * x) * u := by
      rw [← mul_assoc, (hV u hu).2 k k.2, mul_assoc, (hV u hu).1, mul_assoc]
    change ρ u (ρ q.out v) = ρ q.out v
    rw [h1]
    calc ρ u (ρ ((k : H) * x) v) = ρ (u * ((k : H) * x)) v := by rw [map_mul ρ u]; rfl
      _ = ρ ((k : H) * x) (ρ u v) := by rw [h2, map_mul ρ _ u]; rfl
      _ = _ := by rw [hvV u hu]
  · intro A' M' _ _ _ ρ' f hf v
    rw [dcSum_apply, dcSum_apply, map_sum]
    exact Finset.sum_congr rfl fun q _ => hf _ _
