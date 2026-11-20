import Mathlib
import Formalism.PeriodIntegrals.SqPair
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarePairLocal.SqPairLocalOfSteps
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UnimodGenus

noncomputable section
open NumberField Matrix

namespace PI.SqPairLocal

open PI.SqPair Formalism.L2.PairingIndexBounds.Eq.SqG PI.UG

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [StarRing E]

/- English proof (translation)
Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem isLattice_of_isSDG {N : ℕ} {L : Submodule (𝓞 E) (Fin N → E)} (h : IsSDG E N L) :
    Submodule.IsLattice E L := by
  obtain ⟨h1, h2, -⟩ := h
  exact ⟨h1, h2⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Replace the relevant objects with their definitions. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem isUnimodular_of_isSDG {N : ℕ} {L : Submodule (𝓞 E) (Fin N → E)} (h : IsSDG E N L) :
    IsUnimodular (hStd E N) L := by
  obtain ⟨-, -, h3⟩ := h
  unfold PI.UG.IsUnimodular PI.UG.dual
  ext y
  simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply, Submodule.mem_one]
  rw [h3 y]
  exact forall₂_congr fun x _ => RingHom.mem_range.symm

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Substitute using the available equality. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. A detailed English derivation is pending.
-/
theorem mem_hcompl_of_inert {Q : Ideal (𝓞 E)} (hQ : Q.IsPrime) (hc : Q.comap (cj E) = Q) (s : 𝓞 E) :
    s ∈ hcompl (K := E) Q ↔ s ∉ Q := by
  haveI := hQ
  constructor
  · intro h
    have hle : hcompl (K := E) Q ≤ Q.primeCompl := Submonoid.closure_le.mpr fun s hs => hs.1
    exact hle h
  · intro hs
    apply Submonoid.subset_closure
    refine ⟨hs, fun t ht => ?_⟩
    have htc : t = cj E s := by
      apply RingOfIntegers.ext
      exact ht
    subst htc
    intro hcs
    apply hs
    have h2 : s ∈ Q.comap (cj E) := Ideal.mem_comap.mpr hcs
    rwa [hc] at h2

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem mem_loc_inert {Q : Ideal (𝓞 E)} (hQ : Q.IsPrime) (hc : Q.comap (cj E) = Q) {N : ℕ}
    (L : Submodule (𝓞 E) (Fin N → E)) (y : Fin N → E) :
    y ∈ loc (K := E) Q L ↔ ∃ s : 𝓞 E, s ∉ Q ∧ s • y ∈ L := by
  simp [loc, locS, mem_hcompl_of_inert hQ hc]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. A detailed English derivation is pending.
-/
theorem mem_loc_stdLat {Q : Ideal (𝓞 E)} (hQ : Q.IsPrime) (hc : Q.comap (cj E) = Q) {N : ℕ}
    (x : Fin N → E) : x ∈ loc (K := E) Q (stdLat E N) ↔ ∀ i, IntAt Q (x i) := by
  rw [mem_loc_inert hQ hc]
  constructor
  · rintro ⟨s, hs, hx⟩ i
    obtain ⟨w, hw⟩ := Submodule.mem_one.mp ((Submodule.mem_pi.mp hx) i (Set.mem_univ i))
    refine ⟨s, hs, w, ?_⟩
    change algebraMap (𝓞 E) E s * x i = algebraMap (𝓞 E) E w
    rw [hw, Pi.smul_apply, Algebra.smul_def]
  · intro h
    choose s hs w hw using h
    haveI := hQ
    refine ⟨∏ i, s i, ?_, ?_⟩
    · have : (∏ i, s i) ∈ Q.primeCompl := Submonoid.prod_mem _ fun i _ => hs i
      exact this
    · refine Submodule.mem_pi.mpr fun i _ => Submodule.mem_one.mpr
        ⟨(∏ j ∈ Finset.univ.erase i, s j) * w i, ?_⟩
      rw [Pi.smul_apply, Algebra.smul_def, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i), map_mul,
        map_mul, mul_assoc]
      congr 1
      exact (hw i).symm

/- English proof (translation)
By extensionality, compare the relevant components. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem unitary_of_isom {N : ℕ} {g : (Fin N → E) ≃ₗ[E] (Fin N → E)} (hg : g ∈ isom (hStd E N)) :
    (LinearMap.toMatrix' (g : (Fin N → E) →ₗ[E] (Fin N → E)))ᴴ *
      LinearMap.toMatrix' (g : (Fin N → E) →ₗ[E] (Fin N → E)) = 1 := by
  ext i j
  have h1 : hStd E N (g (PI.UG.W.eStd E N i)) (g (PI.UG.W.eStd E N j)) = if i = j then 1 else 0 :=
    (hg _ _).trans (PI.UG.W.hStd_eStd E N i j)
  rw [PI.UG.W.hStd_apply] at h1
  rw [Matrix.mul_apply, Matrix.one_apply, ← h1]
  simp only [conjTranspose_apply, LinearMap.toMatrix'_apply, LinearEquiv.coe_coe, PI.UG.W.eStd]

end SlopeTestRemainingChoices

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components.

Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components.
-/
theorem dict : Dict := by
  intro E _ _ _ hE N L hL Q hQ hc
  obtain ⟨g, hg, hgL⟩ := unimodular_genus_unique E N hE L (isLattice_of_isSDG hL) (isUnimodular_of_isSDG hL) Q hQ
  have h1 := unitary_of_isom hg
  have h2 := mul_eq_one_comm.mp h1
  refine ⟨LinearMap.toMatrix' (g : (Fin N → E) →ₗ[E] (Fin N → E)), h1, h2, fun y => ?_⟩
  have hQp := hQ.isPrime
  rw [← mem_loc_inert hQp hc, ← mem_loc_stdLat hQp hc]
  change y ∈ loc (K := E) Q L ↔ _
  rw [← hgL]
  have hs : g.symm y = (LinearMap.toMatrix' (g : (Fin N → E) →ₗ[E] (Fin N → E)))ᴴ *ᵥ y := by
    rw [LinearEquiv.symm_apply_eq]
    rw [← LinearEquiv.coe_coe, ← LinearMap.toMatrix'_mulVec, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
  rw [← hs]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro h
    exact ⟨g.symm y, h, by simp⟩

end PI.SqPairLocal
