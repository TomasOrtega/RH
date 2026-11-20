import Mathlib
import Formalism.FrobeniusOrbits.HostThickExists
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Orbits

noncomputable section

namespace Formalism.FrobeniusOrbits

open Formalism.TwoAdicCyclotomicDecomposition

namespace Stab

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_open_normal_orderOf {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
    (x : G) (hx : IsOfFinOrder x) :
    ∃ N : OpenNormalSubgroup G,
      orderOf (QuotientGroup.mk x : G ⧸ (N.toSubgroup)) = orderOf x := by
  classical
  have hn : 0 < orderOf x := hx.orderOf_pos
  set S : Set G := (fun i : ℕ => x ^ i) '' Set.Ioo 0 (orderOf x) with hSdef
  have hS : IsClosed S := ((Set.finite_Ioo 0 (orderOf x)).image _).isClosed
  have h1 : (1 : G) ∈ Sᶜ := by
    rintro ⟨i, ⟨hi0, hin⟩, hi⟩
    exact pow_ne_one_of_lt_orderOf hi0.ne' hin hi
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hS.isOpen_compl h1
  refine ⟨N, le_antisymm ?_ ?_⟩
  · exact Nat.le_of_dvd hn (orderOf_map_dvd (QuotientGroup.mk' N.toSubgroup) x)
  · by_contra hlt
    push_neg at hlt
    have hfo : IsOfFinOrder (QuotientGroup.mk x : G ⧸ N.toSubgroup) := by
      rw [isOfFinOrder_iff_pow_eq_one]
      exact ⟨orderOf x, hn, by rw [← QuotientGroup.mk_pow, pow_orderOf_eq_one]; rfl⟩
    have hj := hfo.orderOf_pos
    have hmem : x ^ orderOf (QuotientGroup.mk x : G ⧸ N.toSubgroup) ∈ N.toSubgroup := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, pow_orderOf_eq_one]
    exact hN hmem ⟨_, ⟨hj, hlt⟩, rfl⟩

end Stab

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem hostProG : HostProG := by
  intro g hg G _ _ _ _ _ hN x hx
  obtain ⟨N, hNx⟩ := Stab.exists_open_normal_orderOf x hx
  obtain ⟨m, hm⟩ := hN N.toSubgroup N.toOpenSubgroup.isOpen inferInstance
  have hdvd : orderOf x ∣ g ^ m := by
    rw [← hNx, ← hm]
    exact orderOf_dvd_natCard _
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hg).1 hdvd
  exact ⟨j, hj⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction.

Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction.

Treat this case separately. Simplify using the standard rewrite rules. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. By extensionality, compare the relevant components. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Consider separately whether the proposition holds or fails.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result.

Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result.

Split into cases according to the possible forms of the given data. Treat this case separately. Treat this case separately. It suffices to derive a contradiction. Reduce the claim to the hypotheses of an applicable result.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem hostStab : HostStab := by
  classical
  intro e q d hqd L _ _ ζ a b hL k g hg hlt Γ hΓ
  haveI := Fact.mk hg
  have hn := Galois.finrank_cmField hqd hL
  have key : ∀ δ : Matrix.GeneralLinearGroup (Fin k) (hostE ζ a b), δ ^ g = 1 → δ = 1 := by
    intro δ hδ
    by_contra hne
    let M : Matrix (Fin k) (Fin k) (hostE ζ a b) := δ
    let f : Module.End ℚ (Fin k → hostE ζ a b) := (Matrix.mulVecLin M).restrictScalars ℚ
    have hfpow : ∀ n : ℕ, ∀ v, (f ^ n) v = (M ^ n).mulVec v := by
      intro n
      induction n with
      | zero => intro v; simp
      | succ n ih =>
        intro v
        rw [pow_succ, Module.End.mul_apply, ih, pow_succ]
        simp [f, Matrix.mulVec_mulVec]
    have hMg : M ^ g = 1 := by
      have h := congrArg (fun u : Matrix.GeneralLinearGroup (Fin k) (hostE ζ a b) =>
        (u : Matrix (Fin k) (Fin k) (hostE ζ a b))) hδ
      simpa [M] using h
    have hf1 : f ^ g = 1 := by
      apply LinearMap.ext
      intro v
      rw [hfpow, hMg]
      simp
    have hfne : f ≠ 1 := by
      intro h
      apply hne
      apply Units.ext
      show M = 1
      ext i j
      have h2 := congrFun (LinearMap.congr_fun h (Pi.single j 1)) i
      simpa [f, Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply, eq_comm] using h2
    have hQne : (Polynomial.X - 1 : Polynomial ℚ) * Polynomial.cyclotomic g ℚ ≠ 0 := by
      rw [mul_comm, Polynomial.cyclotomic_prime_mul_X_sub_one ℚ g]
      exact Polynomial.X_pow_sub_C_ne_zero hg.pos 1
    have hdvd : minpoly ℚ f ∣ (Polynomial.X - 1) * Polynomial.cyclotomic g ℚ := by
      apply minpoly.dvd
      rw [mul_comm, Polynomial.cyclotomic_prime_mul_X_sub_one ℚ g]
      simp [hf1]
    have hP0 : minpoly ℚ f ≠ 0 := fun h0 => hQne (zero_dvd_iff.1 (h0 ▸ hdvd))
    have hirr : Irreducible (Polynomial.cyclotomic g ℚ) := Polynomial.cyclotomic.irreducible_rat hg.pos
    by_cases hc : Polynomial.cyclotomic g ℚ ∣ minpoly ℚ f
    · have h1 := Polynomial.natDegree_le_of_dvd hc hP0
      have h2 := Polynomial.natDegree_le_of_dvd (LinearMap.minpoly_dvd_charpoly f)
        (LinearMap.charpoly_monic f).ne_zero
      rw [LinearMap.charpoly_natDegree] at h2
      rw [Polynomial.natDegree_cyclotomic, Nat.totient_prime hg] at h1
      have hdim : Module.finrank ℚ (Fin k → hostE ζ a b) = 2 ^ (e + 2) * k := by
        rw [Module.finrank_pi_fintype]
        simp [hn, mul_comm]
      have h3 := h1.trans h2
      rw [hdim] at h3
      exact absurd hlt (not_lt.2 h3)
    · have hcop : IsCoprime (Polynomial.cyclotomic g ℚ) (minpoly ℚ f) :=
        (Irreducible.coprime_iff_not_dvd hirr).2 hc
      have h1 : minpoly ℚ f ∣ Polynomial.X - 1 := hcop.symm.dvd_of_dvd_mul_right hdvd
      have h0 : Polynomial.aeval f (Polynomial.X - 1 : Polynomial ℚ) = 0 := by
        obtain ⟨r, hr⟩ := h1
        rw [hr, map_mul, minpoly.aeval, zero_mul]
      apply hfne
      simpa [sub_eq_zero] using h0
  rw [eq_bot_iff]
  intro γ hγ
  rw [Subgroup.mem_bot]
  obtain ⟨m, hm⟩ := hΓ γ hγ
  cases m with
  | zero => simpa using hm
  | succ m =>
    exfalso
    apply pow_ne_one_of_lt_orderOf (n := g ^ m) (x := γ) (pow_ne_zero _ hg.ne_zero)
      (by rw [hm, pow_succ]; exact lt_mul_of_one_lt_right (pow_pos hg.pos _) hg.one_lt)
    apply key
    rw [← pow_mul, ← pow_succ, ← hm, pow_orderOf_eq_one]

end Formalism.FrobeniusOrbits
