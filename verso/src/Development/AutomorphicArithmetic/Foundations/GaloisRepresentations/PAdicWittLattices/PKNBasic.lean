import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoprimeNsmulEndomorphismPreservesCompletioStatement
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.InvMemLatMonoidOfMemAwaySupp

open UpperTheory.Gal.G3

/- English proof (translation)
Introduce `v hv`. Take `⟨w, hw, e⟩` from `hu _ (hi v hv)`. Use `⟨j • L.actG g w, hj w hw, ?_⟩` and prove the remaining obligations. Establish `h1 : L.actG g (L.actG g⁻¹ v) = v`. Rewrite using `[← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]`.

Establish `key : j' • L.actG (g * u * g⁻¹) v = j' • (v + N • j • L.actG g w)`. Establish `e2` using `congrArg (L.actG g) e`. Simplify using `only [map_add, map_nsmul, h1] at e2`. Rewrite using `[map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, e2, smul_add, smul_smul, smul_smul]`. Use `congr 2`.

Expand and normalize the polynomial expressions, which then agree. Establish `hj0 : (j' : ℚ) ≠ 0` using `by exact_mod_cast hj'.ne'`. Rewrite `key` using `[← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ]`. Conclude with `smul_right_injective _ hj0 key`.
-/
private theorem congOne_conj {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {G : GlobalTheory.LKTrip.HTGroup p}
    (L : GlobalTheory.LKGeo.Link D G) (N : ℕ) (g : G.GAf) (j j' : ℕ) (hj' : 0 < j')
    (hj : ∀ v ∈ GlobalTheory.LKGeo.LaHat D, j • L.actG g v ∈ GlobalTheory.LKGeo.LaHat D)
    (hi : ∀ v ∈ GlobalTheory.LKGeo.LaHat D, j' • L.actG g⁻¹ v ∈ GlobalTheory.LKGeo.LaHat D)
    (u : G.GAf) (hu : L.CongOne (N * (j * j')) u) : L.CongOne N (g * u * g⁻¹) := by
  intro v hv
  obtain ⟨w, hw, e⟩ := hu _ (hi v hv)
  refine ⟨j • L.actG g w, hj w hw, ?_⟩
  have h1 : L.actG g (L.actG g⁻¹ v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have key : j' • L.actG (g * u * g⁻¹) v = j' • (v + N • j • L.actG g w) := by
    have e2 := congrArg (L.actG g) e
    simp only [map_add, map_nsmul, h1] at e2
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, e2, smul_add, smul_smul, smul_smul]
    congr 2
    ring
  have hj0 : (j' : ℚ) ≠ 0 := by exact_mod_cast hj'.ne'
  rw [← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ] at key
  exact smul_right_injective _ hj0 key

/- English proof (translation)
Introduce `p _ D G L N`. Use `⟨fun k hk u hu => ?_, fun g => ?_, fun M hN hM => GlobalTheory.W2.relIndex_KN_ne_zero L hN hM⟩` and prove the remaining obligations. Establish `key : ∀ u, L.CongOne N u → L.CongOne N (k * u * k⁻¹)`. Introduce `u hu v hv`. Take `⟨w, hw, e⟩` from `hu _ (UpperTheory.Gal.Int.Geo.integ_of_mem (inv_mem hk) v hv)`.

Use `⟨L.actG k w, UpperTheory.Gal.Int.Geo.integ_of_mem hk w hw, ?_⟩` and prove the remaining obligations. Establish `h1 : L.actG k (L.actG k⁻¹ v) = v`. Rewrite using `[← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]`. Rewrite using `[map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, e, map_add, map_nsmul, h1]`. Use `⟨key u hu.1, ?_⟩` and prove the remaining obligations.

Establish `e : (k * u * k⁻¹)⁻¹ = k * u⁻¹ * k⁻¹` using `by group`. Rewrite using `[e]`. Conclude with `key _ hu.2`. Take `⟨j, hj0, hjp, hj⟩` from `GlobalTheory.T.exists_coprime_nsmul_endomorphism_preserves_completion p D (L.actG g)`. Take `⟨j', hj0', hjp', hj'⟩` from `GlobalTheory.T.exists_coprime_nsmul_endomorphism_preserves_completion p D (L.actG g⁻¹)`.

Use `⟨j * j', ?_, fun u hu => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Conclude with `Nat.Coprime.mul_left hjp hjp'`. Conclude with `congOne_conj L N g j j' hj0' hj hj' u hu.1`. Establish `e : (g * u * g⁻¹)⁻¹ = g * u⁻¹ * g⁻¹` using `by group`. Rewrite using `[e]`.

Conclude with `congOne_conj L N g j j' hj0' hj hj' _ hu.2`.
-/
theorem UpperTheory.Gal.G3.pKNBasic :
    KNBasic := by
  intro p _ D G L N
  refine ⟨fun k hk u hu => ?_, fun g => ?_, fun M hN hM => GlobalTheory.W2.relIndex_KN_ne_zero L hN hM⟩
  · have key : ∀ u, L.CongOne N u → L.CongOne N (k * u * k⁻¹) := by
      intro u hu v hv
      obtain ⟨w, hw, e⟩ := hu _ (UpperTheory.Gal.Int.Geo.integ_of_mem (inv_mem hk) v hv)
      refine ⟨L.actG k w, UpperTheory.Gal.Int.Geo.integ_of_mem hk w hw, ?_⟩
      have h1 : L.actG k (L.actG k⁻¹ v) = v := by
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
      rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, e, map_add, map_nsmul, h1]
    refine ⟨key u hu.1, ?_⟩
    have e : (k * u * k⁻¹)⁻¹ = k * u⁻¹ * k⁻¹ := by group
    rw [e]
    exact key _ hu.2
  · obtain ⟨j, hj0, hjp, hj⟩ := GlobalTheory.T.exists_coprime_nsmul_endomorphism_preserves_completion p D (L.actG g)
    obtain ⟨j', hj0', hjp', hj'⟩ := GlobalTheory.T.exists_coprime_nsmul_endomorphism_preserves_completion p D (L.actG g⁻¹)
    refine ⟨j * j', ?_, fun u hu => ⟨?_, ?_⟩⟩
    · exact Nat.Coprime.mul_left hjp hjp'
    · exact congOne_conj L N g j j' hj0' hj hj' u hu.1
    · have e : (g * u * g⁻¹)⁻¹ = g * u⁻¹ * g⁻¹ := by group
      rw [e]
      exact congOne_conj L N g j j' hj0' hj hj' _ hu.2
