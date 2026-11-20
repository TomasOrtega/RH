import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.TopLeCopiesSelf

open GlobalTheory.PRep Matrix UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite
open scoped ComplexOrder

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Replace the chosen expression with an arbitrary variable. Substitute using the available equality. Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.repAvg :
    ∀ {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V] [CharZero k] [TopologicalSpace G] [IsTopologicalGroup G] (ρ : Representation k G V) (K : Subgroup G) (χ : K →* kˣ), IsCompact (K : Set G) → IsOpen {x : K | χ x = 1} → ∀ v : V, IsOpen {g : G | ρ g v = v} → ∃ (s : Finset K), s.Nonempty ∧ ∀ (V' : Type) [AddCommGroup V'] [Module k V'] (ρ' : Representation k G V') (v' : V'), (∀ g, ρ g v = v → ρ' g v' = v') → ((s.card : k)⁻¹ • ∑ x ∈ s, (((χ x)⁻¹ : kˣ) : k) • ρ' x v') ∈ eig ρ' K χ := by
  intro k G V _ _ _ _ _ _ _ ρ K χ hK hχ v hv
  classical
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  let S : Subgroup K :=
    { carrier := {x | ρ (x : G) v = v ∧ χ x = 1}
      mul_mem' := by
        rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
        refine ⟨?_, by rw [map_mul, hx', hy', mul_one]⟩
        rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, hy, hx]
      one_mem' := ⟨by simp, map_one χ⟩
      inv_mem' := by
        rintro x ⟨hx, hx'⟩
        refine ⟨?_, by rw [map_inv, hx', inv_one]⟩
        conv_lhs => rw [← hx]
        rw [← Module.End.mul_apply, ← map_mul]
        simp }
  have hSo : IsOpen (S : Set K) := (hv.preimage continuous_subtype_val).inter hχ
  haveI : Finite (K ⧸ S) := S.quotient_finite_of_isOpen hSo
  haveI : Fintype (K ⧸ S) := Fintype.ofFinite _
  refine ⟨Finset.univ.image (fun q : K ⧸ S => q.out), ?_, ?_⟩
  · exact ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ ((1 : K) : K ⧸ S))⟩
  intro V' _ _ ρ' v' h'
  refine Submodule.smul_mem _ _ ?_
  have hinj : Function.Injective (fun q : K ⧸ S => q.out) := Quotient.out_injective
  rw [Finset.sum_image (fun a _ b _ hab => hinj hab)]
  set F : K → V' := fun x => (((χ x)⁻¹ : kˣ) : k) • ρ' x v' with hF
  have hcos : ∀ a b : K, (a : K ⧸ S) = (b : K ⧸ S) → F a = F b := by
    intro a b hab
    obtain ⟨h1, h2⟩ : a⁻¹ * b ∈ S := QuotientGroup.eq.1 hab
    have e : b = a * (a⁻¹ * b) := by group
    generalize a⁻¹ * b = c at h1 h2 e
    subst e
    simp only [hF, map_mul, h2, mul_one, Subgroup.coe_mul, Module.End.mul_apply, h' _ h1]
  have hmul : ∀ y x : K, ρ' y (F x) = (χ y : k) • F (y * x) := by
    intro y x
    simp only [hF, map_smul, map_mul, Subgroup.coe_mul, Module.End.mul_apply, smul_smul]
    congr 1
    rw [← Units.val_mul]
    congr 1
    rw [mul_inv, mul_inv_cancel_left]
  intro y
  show ρ' y (∑ q : K ⧸ S, F q.out) = (χ y : k) • ∑ q : K ⧸ S, F q.out
  rw [map_sum, Finset.smul_sum]
  refine Fintype.sum_equiv (MulAction.toPerm y) _ _ fun q => ?_
  rw [hmul]
  congr 1
  apply hcos
  rw [QuotientGroup.out_eq']
  show _ = y • q
  conv_rhs => rw [← QuotientGroup.out_eq' q]
  rfl
