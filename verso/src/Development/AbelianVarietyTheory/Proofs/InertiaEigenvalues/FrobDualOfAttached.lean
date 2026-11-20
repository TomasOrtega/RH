import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPlaceOverMoveValCc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaCompatibleConjugationRepresentation

open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.TripleFrobDual

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem charpoly_smul {n : ℕ} (M N : Matrix (Fin n) (Fin n) ℂ) (h : M * N = 1) (m : Multiset ℂ) (c : ℂ)
    (hM : M.charpoly = (m.map fun β => X - C β).prod) :
    (c • M).charpoly = (m.map fun β => X - C (c * β)).prod := by
  have h1 := GlobalTheory.ConjPoly.charpoly_smul_inv M N h m 1 hM
  have h2 := GlobalTheory.ConjPoly.charpoly_smul_inv N M (mul_eq_one_comm.1 h) (m.map (·⁻¹)) c
    (by rw [one_smul] at h1; rw [h1, Multiset.map_map]; simp)
  rw [h2, Multiset.map_map]
  simp

/- English proof (translation)
Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.
-/
theorem cyclotomicChar_frobenius_eq_normPlace {D : D7} (i : D.ntw.Tw) {v : HeightOneSpectrum (𝓞 D.host.E)}
    (hv : v ∉ placesOver D.host.E (D.ntw.l i)) {A : ValuationSubring D.nd.Om} (hA : IsPlaceOver (F := D.host.E) A v)
    {σ : Gen.GE D.nd} (hσ : IsFrob (F := D.host.E) A (normV v) σ) :
    ((eps0 D.ntw i σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) = (normV v : ℕ) := by
  have h := cycZ_of_isFrob hv hA hσ
  change algebraMap ℤ_[D.ntw.l i] (D.ntw.O0 i) ((cycZ D.host.E D.nd.Om (D.ntw.l i) σ : ℤ_[D.ntw.l i]ˣ) : _) = _
  rw [h, map_natCast]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem rd_injective {D : D7} (i : D.ntw.Tw) (ι : FractionRing (D.ntw.O0 i) →+* ℂ) :
    Function.Injective (rd i ι) :=
  ι.injective.comp (IsFractionRing.injective _ _)

/- English proof (translation)
Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities.

Clear the denominators using the available nonvanishing facts. Take a linear combination of the given relations to obtain the conclusion. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem frobDual_of_tripleAtt : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i),
    TripleAtt D.naut bkP i s → FrobDual i s := by
  rintro D bkP i s ⟨ι, π₁, π, -, hT, hR, -⟩ P hP - - A hA g g' hg hg'
  obtain rfl : g' = GlobalTheory.TwistDet.cConj D.ntw g := AlgEquiv.ext fun x => by rw [hg', GlobalTheory.TwistDet.cConj_apply]
  obtain ⟨bar, -, hbar⟩ := GlobalTheory.ConjPoly.exists_conj D
  obtain ⟨hcj, hn, -⟩ := hbar P
  have hl : P ∉ placesOver D.host.E (D.ntw.l i) := fun h => hP (D.ntw.twistExcludedPlaces_contains_residueChar i h)
  have hl' : bar P ∉ placesOver D.host.E (D.ntw.l i) := fun h =>
    hl (GlobalTheory.TwistDet.mem_placesOver_conj (GlobalTheory.TwistDet.isConjPl_symm hcj) h)
  have hu := hR.unr P (fun k h => hP (D.ntw.placesOver_subset_exceptional i k h)) fun h => hP (D.ntw.primes_subset_exceptional i h)
  obtain ⟨hu', he⟩ := D.naut.csd_unr π P (bar P) hR.csd hcj hu
  have hA' := GlobalTheory.TwistDet.isPlaceOver_moveVal_cc D.ntw hcj hA
  have hg2 := GlobalTheory.TwistDet.isFrob_cConj D.ntw hg
  rw [← hn] at hg2
  have e1 := hT.frob P hl hu A g hA hg
  have e2 := hT.frob _ hl' hu' _ _ hA' hg2
  rw [D.naut.frobEig_tw _ _ hu, ← Matrix.charpoly_map, Tgl_coe] at e1
  rw [D.naut.frobEig_tw _ _ hu', he, hn, ← Matrix.charpoly_map, Tgl_coe] at e2
  have hinv : ∀ x, (Tmat i s x).map (rd i ι) * ((Tmat i s x)⁻¹).map (rd i ι) = 1 := fun x => by
    rw [← Matrix.map_mul, ← Tgl_coe, Matrix.mul_nonsing_inv _ (Matrix.isUnit_iff_isUnit_det _ |>.1 (Units.isUnit _)),
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hq : ((normV P : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (GlobalTheory.ConjPoly.normV_ne_zero P)
  have e3 := charpoly_smul _ _ (hinv _) _ (((normV P : ℕ) : ℂ) ^ D.R.t) e1
  have e4 := GlobalTheory.ConjPoly.charpoly_smul_inv _ _ (hinv _) _ ((normV P : ℕ) : ℂ) e2
  apply Polynomial.map_injective _ (rd_injective i ι)
  rw [Tdual, ← Matrix.transpose_smul, Matrix.charpoly_transpose, ← Matrix.charpoly_map, ← Matrix.charpoly_map,
    cyclotomicChar_frobenius_eq_normPlace i hl hA hg, cyclotomicChar_frobenius_eq_normPlace i hl' hA' hg2, hn]
  refine Eq.trans ?_ (e4.trans (Eq.trans ?_ (e3.symm.trans ?_)))
  · congr 1
    ext a b
    simp
  · rw [Multiset.map_map, Multiset.map_map, Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun a _ => ?_
    simp only [Function.comp_apply]
    have h2 := GlobalTheory.ConjPoly.cpow_sq hq ((1 - (D.R.t : ℝ)) / 2) (1 - D.R.t) (by push_cast; ring)
    have h3 : ((normV P : ℕ) : ℂ) ^ (((1 - (D.R.t : ℝ)) / 2 : ℝ) : ℂ) ≠ 0 := by simp [hq]
    rw [zpow_sub₀ hq, zpow_one, zpow_natCast, div_eq_iff (pow_ne_zero _ hq)] at h2
    congr 2
    rw [mul_inv, inv_inv]
    field_simp
    linear_combination a * h2
  · congr 1
    ext a b
    simp

end GlobalTheory.TripleFrobDual
