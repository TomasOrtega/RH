import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.WitSys
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsNsmulMemClosure
open NumberField
open GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo UpperTheory.Gal.W2.Wit
open scoped TensorProduct

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.ExistsNsmulMemClosure.exists_nsmul_mem_closure s w hw`.
-/
private lemma exists_nsmul_mem_closure {V : Type*} [AddCommGroup V] [Module ℚ V] (s : Set V) (w : V)
    (hw : w ∈ Submodule.span ℚ s) : ∃ k : ℕ, 0 < k ∧ k • w ∈ AddSubgroup.closure s :=
  _root_.UpperTheory.Reformulated.B.ExistsNsmulMemClosure.exists_nsmul_mem_closure s w hw

/- English proof (translation)
Introduce `p hp D M hM`. Take `⟨-, s, hs, hmem⟩` from `hM`. Establish `hprime : p.Prime` using `hp.out`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `m w hm hw`.

Take `⟨m', hm', hc⟩` from `(hmem _).1 hw`. Use `(hmem _).2 ⟨m' * m, Nat.Coprime.mul_left hm' hm, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_smul]` and apply the resulting hypothesis. Introduce `w`. Take `⟨k, hk, hkw⟩` from `exists_nsmul_mem_closure (s : Set (VQ D)) w (by rw [hs]; trivial)`.

Take `⟨r, k', hk', rfl⟩` from `Nat.exists_eq_pow_mul_and_not_dvd hk.ne' p hprime.ne_one`. Use `⟨r, (hmem _).2 ⟨k', ((Nat.Prime.coprime_iff_not_dvd hprime).2 hk').symm, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[smul_smul, mul_comm]`. Conclude with `hkw`.
-/
theorem UpperTheory.p_lattice_saturated_and_cofinite :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (M : AddSubgroup (VQ D)), UpperTheory.Gal.W2.IsPLat D M → (∀ (m : ℕ) (w : VQ D), m.Coprime p → m • w ∈ M → w ∈ M) ∧ ∀ w : VQ D, ∃ r : ℕ, p ^ r • w ∈ M := by
  intro p hp D M hM
  obtain ⟨-, s, hs, hmem⟩ := hM
  have hprime : p.Prime := hp.out
  refine ⟨?_, ?_⟩
  · intro m w hm hw
    obtain ⟨m', hm', hc⟩ := (hmem _).1 hw
    refine (hmem _).2 ⟨m' * m, Nat.Coprime.mul_left hm' hm, ?_⟩
    rwa [mul_smul]
  · intro w
    obtain ⟨k, hk, hkw⟩ := exists_nsmul_mem_closure (s : Set (VQ D)) w (by rw [hs]; trivial)
    obtain ⟨r, k', hk', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hk.ne' p hprime.ne_one
    refine ⟨r, (hmem _).2 ⟨k', ((Nat.Prime.coprime_iff_not_dvd hprime).2 hk').symm, ?_⟩⟩
    rw [smul_smul, mul_comm]
    exact hkw
