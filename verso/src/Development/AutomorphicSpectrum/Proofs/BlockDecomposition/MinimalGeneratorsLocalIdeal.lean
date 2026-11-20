import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.H1DimGeAbelianDim
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfSmallExtension
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CechHOneVanishesOnOpenOfIsAffineOpen
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrMulTrInv
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.FewEq
open GlobalTheory.AbLaw (rs)

namespace GlobalTheory.CompanionTheory.FewEq

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Separate the alternatives or extract the components of the hypothesis.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_fin_span_eq_of_unit_coeff {R : Type} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (I : Ideal R) {n : ℕ} (t : Fin (n + 1) → R)
    (ht : Ideal.span (Set.range t) = I) (x : Fin (n + 1) → R)
    (hx : ∑ i, x i * t i ∈ IsLocalRing.maximalIdeal R * I) (l : Fin (n + 1))
    (hu : IsUnit (x l)) : ∃ s : Fin n → R, Ideal.span (Set.range s) = I := by
  refine ⟨fun j => t (l.succAbove j), le_antisymm ?_ ?_⟩
  · rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    rw [← ht]
    exact Ideal.subset_span ⟨_, rfl⟩
  set N : Ideal R := Ideal.span (Set.range fun j => t (l.succAbove j)) with hN
  have hmem : ∀ j, t (l.succAbove j) ∈ N := fun j => Ideal.subset_span ⟨j, rfl⟩
  have htl : t l ∈ N ⊔ IsLocalRing.maximalIdeal R • I := by
    obtain ⟨u, hu⟩ := hu
    have hsum : x l * t l = ∑ i, x i * t i - ∑ j, x (l.succAbove j) * t (l.succAbove j) := by
      rw [Fin.sum_univ_succAbove _ l]
      ring
    have h1 : x l * t l ∈ N ⊔ IsLocalRing.maximalIdeal R • I := by
      rw [hsum]
      refine Ideal.sub_mem _ (Ideal.mem_sup_right (by simpa [smul_eq_mul] using hx)) ?_
      exact Ideal.mem_sup_left (Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hmem j))
    have h2 : t l = (↑u⁻¹ : R) * (x l * t l) := by
      rw [← hu, ← mul_assoc, Units.inv_mul, one_mul]
    rw [h2]
    exact Ideal.mul_mem_left _ _ h1
  have hle : I ≤ N ⊔ IsLocalRing.maximalIdeal R • I := by
    conv_lhs => rw [← ht]
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rcases Fin.eq_self_or_eq_succAbove l i with h | ⟨j, h⟩
    · rw [h]; exact htl
    · rw [h]; exact Ideal.mem_sup_left (hmem j)
  exact Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian I)
    (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge hle

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Assume the negation of the conclusion and derive a contradiction.

Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Replace the chosen expression with an arbitrary variable. Split into cases according to the possible forms of the given data.

Treat this case separately. Treat this case separately. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers. A detailed English derivation is pending.
-/
theorem exists_minimal_generators : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R),
    ∃ (r : ℕ) (t : Fin r → R), Ideal.span (Set.range t) = I ∧
      ∀ x : Fin r → R, ∑ i, x i * t i ∈ IsLocalRing.maximalIdeal R * I → ∀ i, x i ∈ IsLocalRing.maximalIdeal R := by
  intro R _ _ _ I
  classical
  have hex : ∃ r : ℕ, ∃ t : Fin r → R, Ideal.span (Set.range t) = I :=
    Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian I)
  obtain ⟨t, ht⟩ := Nat.find_spec hex
  refine ⟨_, t, ht, fun x hx l => ?_⟩
  by_contra hl
  have hu : IsUnit (x l) := by
    by_contra h
    exact hl ((IsLocalRing.mem_maximalIdeal _).mpr h)
  have hmin : ∀ m : ℕ, (∃ s : Fin m → R, Ideal.span (Set.range s) = I) → Nat.find hex ≤ m :=
    fun m h => Nat.find_min' hex h
  generalize Nat.find hex = r at t ht x hx l hu hmin
  cases r with
  | zero => exact l.elim0
  | succ n =>
    have := hmin n (exists_fin_span_eq_of_unit_coeff I t ht x hx l hu)
    omega

end GlobalTheory.CompanionTheory.FewEq
