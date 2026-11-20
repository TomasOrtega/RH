import Mathlib
import Formalism.FrobeniusOrbits.HostThickExists
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Orbits

noncomputable section

namespace Formalism.FrobeniusOrbits

open Formalism.TwoAdicCyclotomicDecomposition

namespace Stab

/- English proof (translation)
Establish `hn : 0 < orderOf x` using `hx.orderOf_pos`. Use `set S : Set G := (fun i : ℕ => x ^ i) '' Set.Ioo 0 (orderOf x) with hSdef`. Establish `hS : IsClosed S` using `((Set.finite_Ioo 0 (orderOf x)).image _).isClosed`. Establish `h1 : (1 : G) ∈ Sᶜ`. Introduce and unpack `⟨i, ⟨hi0, hin⟩, hi⟩`.

Conclude with `pow_ne_one_of_lt_orderOf hi0.ne' hin hi`. Take `⟨N, hN⟩` from `ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hS.isOpen_compl h1`. Use `⟨N, le_antisymm ?_ ?_⟩` and prove the remaining obligations. Conclude with `Nat.le_of_dvd hn (orderOf_map_dvd (QuotientGroup.mk' N.toSubgroup) x)`. Assume the negation of the conclusion as `hlt push_neg at hlt`.

Establish `hfo : IsOfFinOrder (QuotientGroup.mk x : G ⧸ N.toSubgroup)`. Rewrite using `[isOfFinOrder_iff_pow_eq_one]`. Conclude with `⟨orderOf x, hn, by rw [← QuotientGroup.mk_pow, pow_orderOf_eq_one]; rfl⟩`. Establish `hj` using `hfo.orderOf_pos`. Establish `hmem : x ^ orderOf (QuotientGroup.mk x : G ⧸ N.toSubgroup) ∈ N.toSubgroup`.

Rewrite using `[← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, pow_orderOf_eq_one]`. Conclude with `hN hmem ⟨_, ⟨hj, hlt⟩, rfl⟩`.
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
Introduce `g hg G _ _ _ _ _ hN x hx`. Take `⟨N, hNx⟩` from `Stab.exists_open_normal_orderOf x hx`. Take `⟨m, hm⟩` from `hN N.toSubgroup N.toOpenSubgroup.isOpen inferInstance`. Establish `hdvd : orderOf x ∣ g ^ m`. Rewrite using `[← hNx, ← hm]`.

Conclude with `orderOf_dvd_natCard _`. Take `⟨j, -, hj⟩` from `(Nat.dvd_prime_pow hg).1 hdvd`. Conclude with `⟨j, hj⟩`.
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
Introduce `e q d hqd L _ _ ζ a b hL k g hg hlt Γ hΓ`. Use `haveI := Fact.mk hg`. Establish `hn` using `Galois.finrank_cmField hqd hL`. Establish `key : ∀ δ : Matrix.GeneralLinearGroup (Fin k) (hostE ζ a b), δ ^ g = 1 → δ = 1`. Introduce `δ hδ`.

Assume the negation of the conclusion as `hne`. Set `M : Matrix (Fin k) (Fin k) (hostE ζ a b)` to `δ`. Set `f : Module.End ℚ (Fin k → hostE ζ a b)` to `(Matrix.mulVecLin M).restrictScalars ℚ`. Establish `hfpow : ∀ n : ℕ, ∀ v, (f ^ n) v = (M ^ n).mulVec v`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero => intro v`. Simplify using the standard rewrite rules. Consider the case `succ n ih`. Introduce `v`.

Rewrite using `[pow_succ, Module.End.mul_apply, ih, pow_succ]`. Simplify using `[f, Matrix.mulVec_mulVec]`. Establish `hMg : M ^ g = 1`. Establish `h` using `congrArg (fun u : Matrix.GeneralLinearGroup (Fin k) (hostE ζ a b) => (u : Matrix (Fin k) (Fin k) (hostE ζ a b))) hδ`. Simplify `h` using `[M]`.

Establish `hf1 : f ^ g = 1`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `v`. Rewrite using `[hfpow, hMg]`. Simplify using the standard rewrite rules.

Establish `hfne : f ≠ 1`. Introduce `h`. Apply `hne` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Use `show M = 1`.

Use extensionality with `i j`. Establish `h2` using `congrFun (LinearMap.congr_fun h (Pi.single j 1)) i`. Simplify `h2` using `[f, Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply, eq_comm]`. Establish `hQne : (Polynomial.X - 1 : Polynomial ℚ) * Polynomial.cyclotomic g ℚ ≠ 0`. Rewrite using `[mul_comm, Polynomial.cyclotomic_prime_mul_X_sub_one ℚ g]`.

Conclude with `Polynomial.X_pow_sub_C_ne_zero hg.pos 1`. Establish `hdvd : minpoly ℚ f ∣ (Polynomial.X - 1) * Polynomial.cyclotomic g ℚ`. Apply `minpoly.dvd` to reduce the goal to its premises. Rewrite using `[mul_comm, Polynomial.cyclotomic_prime_mul_X_sub_one ℚ g]`. Simplify using `[hf1]`.

Establish `hP0 : minpoly ℚ f ≠ 0` using `fun h0 => hQne (zero_dvd_iff.1 (h0 ▸ hdvd))`. Establish `hirr : Irreducible (Polynomial.cyclotomic g ℚ)` using `Polynomial.cyclotomic.irreducible_rat hg.pos`. Distinguish the cases in `hc : Polynomial.cyclotomic g ℚ ∣ minpoly ℚ f`. Establish `h1` using `Polynomial.natDegree_le_of_dvd hc hP0`. Establish `h2` using `Polynomial.natDegree_le_of_dvd (LinearMap.minpoly_dvd_charpoly f) (LinearMap.charpoly_monic f).ne_zero`.

Rewrite `h2` using `[LinearMap.charpoly_natDegree]`. Rewrite `h1` using `[Polynomial.natDegree_cyclotomic, Nat.totient_prime hg]`. Establish `hdim : Module.finrank ℚ (Fin k → hostE ζ a b) = 2 ^ (e + 2) * k`. Rewrite using `[Module.finrank_pi_fintype]`. Simplify using `[hn, mul_comm]`.

Establish `h3` using `h1.trans h2`. Rewrite `h3` using `[hdim]`. Conclude with `absurd hlt (not_lt.2 h3)`. Establish `hcop : IsCoprime (Polynomial.cyclotomic g ℚ) (minpoly ℚ f)` using `(Irreducible.coprime_iff_not_dvd hirr).2 hc`. Establish `h1 : minpoly ℚ f ∣ Polynomial.X - 1` using `hcop.symm.dvd_of_dvd_mul_right hdvd`.

Establish `h0 : Polynomial.aeval f (Polynomial.X - 1 : Polynomial ℚ) = 0`. Take `⟨r, hr⟩` from `h1`. Rewrite using `[hr, map_mul, minpoly.aeval, zero_mul]`. Apply `hfne` to reduce the goal to its premises. Simplify `h0` using `[sub_eq_zero]`.

Rewrite using `[eq_bot_iff]`. Introduce `γ hγ`. Rewrite using `[Subgroup.mem_bot]`. Take `⟨m, hm⟩` from `hΓ γ hγ`. Consider the cases of `m with`.

Consider the case `zero => simpa using hm`. Consider the case `succ m`. It suffices to derive a contradiction. Apply `pow_ne_one_of_lt_orderOf (n := g ^ m) (x := γ) (pow_ne_zero _ hg.ne_zero) (by rw [hm, pow_succ]; exact lt_mul_of_one_lt_right (pow_pos hg.pos _) hg.one_lt)` to reduce the goal to its premises. Apply `key` to reduce the goal to its premises.

Rewrite using `[← pow_mul, ← pow_succ, ← hm, pow_orderOf_eq_one]`.
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
