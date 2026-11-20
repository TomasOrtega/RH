import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteAdeleStrongApproximationModNat
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IntegralFiniteAdeleCompactClosedMultiples

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

namespace GlobalTheory.CompanionTheory.SW.Core.AfTop

variable (F : Type) [Field F] [NumberField F]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem isCompact_Oh : IsCompact (Oh F) :=
  (GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties F).1

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem isOpen_Oh : IsOpen (Oh F) := by
  haveI : Fact (∀ v : HeightOneSpectrum (𝓞 F),
      IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    ⟨fun _ ↦ Valued.isOpen_valuationSubring _⟩
  exact RestrictedProduct.isOpen_forall_mem
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Fact.out

/- English proof (translation)
Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Treat this case separately.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem natCast_mul_mem_Oh (N : ℕ) {x : A F} (hx : x ∈ Oh F) : (N : A F) * x ∈ Oh F := by
  induction N with
  | zero =>
    intro v
    rw [Nat.cast_zero, zero_mul]
    exact zero_mem (v.adicCompletionIntegers F)
  | succ n ih =>
    intro v
    rw [Nat.cast_succ, add_mul, one_mul]
    exact add_mem (ih v) (hx v)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Assume the hypotheses and unpack their components.

A detailed English derivation is pending.
-/
theorem algebraMap_mem_Oh_iff (b : F) : algebraMap F (A F) b ∈ Oh F ↔ ∃ r : 𝓞 F, (r : F) = b := by
  constructor
  · intro h
    obtain ⟨y, hy⟩ := (GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties F).2.2.2.1 b h
    exact ⟨y, hy.symm⟩
  · rintro ⟨r, rfl⟩ v
    exact HeightOneSpectrum.coe_mem_adicCompletionIntegers v r

/- English proof (translation)
Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations.

Assume the hypotheses and unpack their components. Supply the required witnesses or components. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Extract witnesses or component facts from the available result. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Use the resulting assumption. Supply the required witnesses or components.

A detailed English derivation is pending.
-/
theorem exists_mul_Oh_subset (U : Set (A F)) (hU : U ∈ 𝓝 (0 : A F)) :
    ∃ N : ℕ, 0 < N ∧ ∀ x ∈ Oh F, (N : A F) * x ∈ U := by
  obtain ⟨h1, h2, h3, -⟩ := GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties F
  let V : ℕ+ → Set (A F) := fun N => {a | ∃ c ∈ Oh F, a = ((N : ℕ) : A F) * c}
  have hV : Directed (· ⊇ ·) V := by
    intro M N
    refine ⟨M * N, ?_, ?_⟩
    · rintro _ ⟨c, hc, rfl⟩
      exact ⟨_, natCast_mul_mem_Oh F N hc, by push_cast; ring⟩
    · rintro _ ⟨c, hc, rfl⟩
      exact ⟨_, natCast_mul_mem_Oh F M hc, by push_cast; ring⟩
  have hc : ∀ N, IsCompact (V N) := by
    intro N
    have : V N = (fun c => ((N : ℕ) : A F) * c) '' Oh F := by
      ext a
      simp only [V, Set.mem_setOf_eq, Set.mem_image, eq_comm]
    rw [this]
    exact (isCompact_Oh F).image (continuous_const.mul continuous_id)
  obtain ⟨N, hN⟩ := exists_subset_nhds_of_isCompact' hV hc (fun N => h2 N N.pos) (U := U) (by
    intro x hx
    have : x = 0 := h3 x fun M hM => Set.mem_iInter.1 hx ⟨M, hM⟩
    rwa [this])
  exact ⟨N, N.pos, fun x hx => hN ⟨x, hx, rfl⟩⟩

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Apply an available result and prove the equalities needed to match it to the conclusion. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion.

Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

A detailed English derivation is pending.
-/
theorem exists_mul_mem_Oh_of_isCompact (K : Set (A F)) (hK : IsCompact K) :
    ∃ N : ℕ, 0 < N ∧ ∀ x ∈ K, (N : A F) * x ∈ Oh F := by
  let V : ℕ+ → Set (A F) := fun N => {a | ((N : ℕ) : A F) * a ∈ Oh F}
  have hV : Directed (· ⊆ ·) V := by
    intro M N
    refine ⟨M * N, fun a ha => ?_, fun a ha => ?_⟩
    · have := natCast_mul_mem_Oh F N ha
      show (((M * N : ℕ+) : ℕ) : A F) * a ∈ Oh F
      convert this using 1
      push_cast; ring
    · have := natCast_mul_mem_Oh F M ha
      show (((M * N : ℕ+) : ℕ) : A F) * a ∈ Oh F
      convert this using 1
      push_cast; ring
  obtain ⟨N, hN⟩ := hK.elim_directed_cover V
    (fun N => (isOpen_Oh F).preimage (continuous_const.mul continuous_id)) (fun a _ => by
      obtain ⟨M, hM, h⟩ := (GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties F).2.2.2.2.1 a
      exact Set.mem_iUnion.2 ⟨⟨M, hM⟩, h⟩) hV
  exact ⟨N, N.pos, fun x hx => hN hx⟩

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. By extensionality, compare the relevant components.

Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. Use the resulting assumption. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isOpen_mul_Oh (N : ℕ) (hN : 0 < N) :
    IsOpen {x : A F | ∃ y ∈ Oh F, x = (N : A F) * y} := by
  have hN' : (N : F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have h1 : (N : A F) * algebraMap F (A F) (N : F)⁻¹ = 1 := by
    rw [← map_natCast (algebraMap F (A F)), ← map_mul, mul_inv_cancel₀ hN', map_one]
  have : {x : A F | ∃ y ∈ Oh F, x = (N : A F) * y} =
      (fun x => algebraMap F (A F) (N : F)⁻¹ * x) ⁻¹' Oh F := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      show _ * (_ * y) ∈ Oh F
      rwa [← mul_assoc, mul_comm _ (N : A F), h1, one_mul]
    · intro hx
      exact ⟨_, hx, by rw [← mul_assoc, h1, one_mul]⟩
  rw [this]
  exact (isOpen_Oh F).preimage (continuous_const.mul continuous_id)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. A detailed English derivation is pending.
-/
theorem denseRange_algebraMap : DenseRange (algebraMap F (A F)) := by
  intro y
  rw [mem_closure_iff_nhds]
  intro U hU
  have hc : Continuous fun z : A F => y - z := continuous_const.sub continuous_id
  have hU' : (fun z : A F => y - z) ⁻¹' U ∈ 𝓝 (0 : A F) :=
    hc.continuousAt.preimage_mem_nhds (by simpa using hU)
  obtain ⟨N, hN, h⟩ := exists_mul_Oh_subset F _ hU'
  obtain ⟨x, a, ha, hy⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat F N hN).1 y
  refine ⟨algebraMap F (A F) x, ?_, x, rfl⟩
  have h2 : y - (N : A F) * a ∈ U := h a ha
  have h3 : y - (N : A F) * a = algebraMap F (A F) x := by
    rw [sub_eq_iff_eq_add, ← nsmul_eq_mul]
    exact hy
  rwa [h3] at h2

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. Supply the required witnesses or components.
-/
theorem finiteAdele_topology : ∀ (F : Type) [Field F] [NumberField F], LocallyCompactSpace (A F) ∧ SecondCountableTopology (A F) ∧ T2Space (A F) ∧ IsCompact (Oh F) ∧ IsOpen (Oh F) ∧ DenseRange (algebraMap F (A F)) ∧ (∀ b : F, algebraMap F (A F) b ∈ Oh F ↔ ∃ r : 𝓞 F, (r : F) = b) ∧ (∀ U ∈ 𝓝 (0 : A F), ∃ N : ℕ, 0 < N ∧ ∀ x ∈ Oh F, (N : A F) * x ∈ U) ∧ (∀ K : Set (A F), IsCompact K → ∃ N : ℕ, 0 < N ∧ ∀ x ∈ K, (N : A F) * x ∈ Oh F) ∧ ∀ N : ℕ, 0 < N → IsOpen {x : A F | ∃ y ∈ Oh F, x = (N : A F) * y} :=
  fun F _ _ => ⟨GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F,
    GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F, GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F,
    isCompact_Oh F, isOpen_Oh F, denseRange_algebraMap F, algebraMap_mem_Oh_iff F,
    exists_mul_Oh_subset F, exists_mul_mem_Oh_of_isCompact F, isOpen_mul_Oh F⟩

end GlobalTheory.CompanionTheory.SW.Core.AfTop
