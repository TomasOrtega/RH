import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUnitOfSumEqOne

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm

/- English proof (translation)
Equip the data with the indicated structure. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem smooth_of_away_mvPolynomial {R L ι : Type} [CommRing R] [CommRing L] [Finite ι]
    (g : R →+* L) (ψ : MvPolynomial ι R →+* L) (hg : ψ.comp MvPolynomial.C = g) (f : MvPolynomial ι R)
    (hl : @IsLocalization.Away _ _ f L _ ψ.toAlgebra) : g.Smooth := by
  letI := ψ.toAlgebra
  haveI := hl
  have h1 : ψ.Smooth := (Algebra.Smooth.of_isLocalization_Away f : Algebra.Smooth (MvPolynomial ι R) L)
  have h2 : (algebraMap R (MvPolynomial ι R)).Smooth :=
    RingHom.smooth_algebraMap.2 ⟨inferInstance, inferInstance⟩
  rw [MvPolynomial.algebraMap_eq] at h2
  rw [← hg]
  exact RingHom.Smooth.comp h2 h1

def evalSub {Ω K : Type} [Field Ω] [Field K] [Algebra Ω K] {ι : Type} (R : Subring Ω) (v : ι → K) :
    MvPolynomial ι R →+* K :=
  MvPolynomial.eval₂Hom ((algebraMap Ω K).comp R.subtype) v

/- English proof (translation)
Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem evalSub_injective {Ω K : Type} [Field Ω] [Field K] [Algebra Ω K] {ι : Type} (R : Subring Ω)
    (v : ι → K) (hv : AlgebraicIndependent Ω v) : Function.Injective (evalSub R v) := by
  have e : evalSub R v =
      (MvPolynomial.aeval v : MvPolynomial ι Ω →ₐ[Ω] K).toRingHom.comp (MvPolynomial.map R.subtype) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [evalSub]
    · intro i
      simp [evalSub]
  rw [e]
  exact fun p q hpq => MvPolynomial.map_injective _ R.subtype_injective
    (algebraicIndependent_iff_injective_aeval.1 hv hpq)

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Assume the hypotheses and unpack their components. Proceed by induction. Treat this case separately. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Treat this case separately. Rewrite the conclusion using the stated equalities. Treat this case separately. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Supply the required witnesses or components.

Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem evalSub_range {Ω K : Type} [Field Ω] [Field K] [Algebra Ω K] {ι : Type} (R : Subring Ω)
    (v : ι → K) : (evalSub R v).range =
      Subring.closure (((R.map (algebraMap Ω K) : Subring K) : Set K) ∪ Set.range v) := by
  apply le_antisymm
  · rintro _ ⟨a, rfl⟩
    induction a using MvPolynomial.induction_on with
    | C a =>
      refine Subring.subset_closure (Or.inl ⟨a, a.2, ?_⟩)
      simp [evalSub]
    | add p q hp hq =>
      rw [map_add]
      exact add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul]
      refine mul_mem hp (Subring.subset_closure (Or.inr ⟨i, ?_⟩))
      simp [evalSub]
  · refine Subring.closure_le.2 ?_
    rintro x (⟨a, ha, rfl⟩ | ⟨i, rfl⟩)
    · exact ⟨MvPolynomial.C ⟨a, ha⟩, by simp [evalSub]⟩
    · exact ⟨MvPolynomial.X i, by simp [evalSub]⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Replace the chosen expression with an arbitrary variable. Substitute using the available equality. Establish an intermediate fact.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Express the relevant assertion in an equivalent form by its definition.

Simplify using the standard rewrite rules. Equip the data with the indicated structure. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Simplify to obtain the desired conclusion from the available facts. Assume the hypotheses and unpack their components.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses.

Supply the required witnesses or components.
-/
theorem smooth_locSub_closure : ∀ {Ω K : Type} [Field Ω] [Field K] [Algebra Ω K] {ι : Type} [Finite ι] (R : Subring Ω) (v : ι → K), AlgebraicIndependent Ω v → ∀ ℓ : K, ℓ ∈ Subring.closure (((R.map (algebraMap Ω K) : Subring K) : Set K) ∪ Set.range v) → ℓ ≠ 0 → ∀ h : (∀ a ∈ R, algebraMap Ω K a ∈ locSub (Subring.closure (((R.map (algebraMap Ω K) : Subring K) : Set K) ∪ Set.range v)) ℓ), (((algebraMap Ω K).comp R.subtype).codRestrict (locSub (Subring.closure (((R.map (algebraMap Ω K) : Subring K) : Set K) ∪ Set.range v)) ℓ) (fun a => h a a.2)).Smooth := by
  intro Ω K _ _ _ ι _ R v hv ℓ hℓ h0 h
  have hr := evalSub_range R v
  generalize Subring.closure (((R.map (algebraMap Ω K) : Subring K) : Set K) ∪ Set.range v) = B at *
  subst hr
  have hinj := evalSub_injective R v hv
  have hmem : ∀ a, evalSub R v a ∈ locSub (evalSub R v).range ℓ :=
    fun a => le_locSub _ _ ⟨a, rfl⟩
  obtain ⟨f, hf⟩ := hℓ
  refine smooth_of_away_mvPolynomial _ ((evalSub R v).codRestrict _ hmem) ?_ f ?_
  · ext a
    change evalSub R v (MvPolynomial.C a) = algebraMap Ω K a
    simp [evalSub]
  · letI := ((evalSub R v).codRestrict _ hmem).toAlgebra
    have hval : ∀ a : MvPolynomial ι R,
        ((algebraMap (MvPolynomial ι R) (locSub (evalSub R v).range ℓ) a : locSub (evalSub R v).range ℓ) : K)
          = evalSub R v a := fun a => rfl
    refine { map_units := ?_, surj := ?_, exists_of_eq := ?_ }
    · rintro ⟨_, n, rfl⟩
      have hu : IsUnit (algebraMap (MvPolynomial ι R) (locSub (evalSub R v).range ℓ) f) := by
        refine IsUnit.of_mul_eq_one ⟨ℓ⁻¹, inv_mem_locSub _ _⟩ (Subtype.ext ?_)
        simp [hval, hf, h0]
      simpa using hu.pow n
    · rintro ⟨z, hz⟩
      obtain ⟨k, hk⟩ := (mem_locSub_iff (RingHom.mem_range.2 ⟨f, hf⟩) h0 z).1 hz
      obtain ⟨a, ha⟩ := RingHom.mem_range.1 hk
      refine ⟨⟨a, ⟨f ^ k, k, rfl⟩⟩, Subtype.ext ?_⟩
      simp [hval, hf, ha, mul_comm]
    · intro x y hxy
      exact ⟨1, by rw [hinj (congrArg Subtype.val hxy)]⟩

end GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell
