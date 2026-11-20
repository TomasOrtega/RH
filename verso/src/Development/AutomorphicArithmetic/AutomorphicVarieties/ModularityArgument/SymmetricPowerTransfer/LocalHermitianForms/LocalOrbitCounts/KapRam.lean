import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.LcountNorm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.SumShift
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.DatSmul
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.SplitM
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.RamUnit

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
private theorem inv_norm {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] {Δ τ : K} (L : IsLoc O Δ)
    {c : K} {d m : EL Δ τ} (h : IsDat c d m) : ∀ t ∈ NE τ, ∀ x : Kˣ,
    lcount O c d (((t * x : Kˣ) : K) • m) = lcount O c d ((x : K) • m) := fun t ht x => by
  rw [Units.val_mul, mul_smul]
  exact lcountNorm O K Δ τ L c d _ (datSmul K Δ τ c d m h x) t ht

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction.

Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Assume the hypotheses and unpack their components. Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Take a linear combination of the given relations to obtain the conclusion. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Replace the relevant objects with their definitions. Take a linear combination of the given relations to obtain the conclusion.

A detailed English derivation is pending.
-/
theorem UpperTheory.V.Z.Sym.Loc.kapRam : UpperTheory.V.Z.Sym.Loc.KapRam := by
  intro O K _ _ _ _ _ Δ τ L c d m h hτ hodd
  obtain ⟨a, rfl⟩ := hτ
  have h2 := L.two
  have hu : IsUnit (2 - a) := by
    by_contra hn
    apply hodd
    have hp : IsUnit (2 + a) := by
      by_contra hp
      have hsum := IsLocalRing.nonunits_add hn hp
      apply hsum
      have e : (2 - a) + (2 + a) = 2 * 2 := by ring
      rw [e]
      exact h2.mul h2
    refine ⟨hp.unit, 1, one_ne_zero, ?_⟩
    simp [map_add, map_ofNat]
  obtain ⟨v, hv⟩ := hu
  have hv' : algebraMap O K (v : O) = 2 - algebraMap O K a := by
    rw [hv, map_sub, map_ofNat]
  have hex : ∃ u : Oˣ, algebraMap O K ↑u = 2 - algebraMap O K a := ⟨v, hv'⟩
  refine ⟨hex, ?_⟩
  have hD : ¬ EvenVal O (algebraMap O K a ^ 2 - 4) := by
    rintro ⟨u, s, hs0, hus⟩
    apply hodd
    refine ⟨-(u * v⁻¹), s, hs0, ?_⟩
    have hw : algebraMap O K (v : O) * algebraMap O K ((v⁻¹ : Oˣ) : O) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    rw [hv'] at hw
    simp only [Units.val_neg, Units.val_mul, map_neg, map_mul]
    linear_combination (-(algebraMap O K ((v⁻¹ : Oˣ) : O))) * hus + (-(2 + algebraMap O K a)) * hw
  have hreg := h.reg
  obtain ⟨ε, hε⟩ := ramUnit O K Δ L _ hreg hD
  have hinv : ∀ t ∈ NE (algebraMap O K a), ∀ x : Kˣ,
      lcount O c d (((t * x : Kˣ) : K) • m) = lcount O c d ((x : K) • m) :=
    fun t ht x => inv_norm L h t ht x
  have hg : ((Units.map (algebraMap O K : O →* K) ε : Kˣ) : K) = algebraMap O K ε := rfl
  obtain ⟨_, h2', _⟩ := sumShift O K Δ _ L hreg (fun y : Kˣ => lcount O c d ((y : K) • m)) hinv
    (Units.map (algebraMap O K : O →* K) ε)
  have hshift : ∀ x : Kˣ, lcount O c d (((x * Units.map (algebraMap O K : O →* K) ε : Kˣ) : K) • m)
      = lcount O c d ((x : K) • m) := by
    intro x
    rw [Units.val_mul, hg, mul_comm, mul_smul]
    exact splitM O K Δ _ L c d _ (datSmul K Δ _ c d m h x) ⟨a, rfl⟩ hex ε
  simp only [hshift, hg, hε] at h2'
  have h3 : kapSum O c d m = -1 * kapSum O c d m := by
    unfold kapSum
    exact h2'
  linear_combination h3 / 2
