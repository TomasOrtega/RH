import Mathlib

open NumberField IsDedekindDomain

namespace GlobalTheory

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push_neg at h`. Establish `h1 : c ≤ (P : FractionalIdeal (nonZeroDivisors R) K) * c` using `fun b hb => h b hb`. Establish `h2 : c * c⁻¹ ≤ (P : FractionalIdeal (nonZeroDivisors R) K) * c * c⁻¹` using `by gcongr`. Rewrite `h2` using `[mul_assoc, mul_inv_cancel₀ hc, mul_one, ← FractionalIdeal.coeIdeal_top, FractionalIdeal.coeIdeal_le_coeIdeal]`.

Conclude with `hP (top_le_iff.mp h2)`.
-/
theorem exists_mem_notMem_coeIdeal_mul {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (c : FractionalIdeal (nonZeroDivisors R) K) (hc : c ≠ 0)
    (P : Ideal R) (hP : P ≠ ⊤) :
    ∃ b : K, b ∈ c ∧ b ∉ (P : FractionalIdeal (nonZeroDivisors R) K) * c := by
  by_contra h
  push_neg at h
  have h1 : c ≤ (P : FractionalIdeal (nonZeroDivisors R) K) * c := fun b hb => h b hb
  have h2 : c * c⁻¹ ≤ (P : FractionalIdeal (nonZeroDivisors R) K) * c * c⁻¹ := by
    gcongr
  rw [mul_assoc, mul_inv_cancel₀ hc, mul_one, ← FractionalIdeal.coeIdeal_top,
    FractionalIdeal.coeIdeal_le_coeIdeal] at h2
  exact hP (top_le_iff.mp h2)

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => exact ⟨0, c.zero_mem, by simp⟩`. Consider the case `insert P S hPS ih`. Take `⟨a, ha, haS⟩` from `ih (fun Q hQ => hS Q (Finset.mem_insert_of_mem hQ))`. Establish `hP : P.IsMaximal` using `hS P (Finset.mem_insert_self _ _)`.

Distinguish the cases in `haP : a ∈ (P : FractionalIdeal (nonZeroDivisors R) K) * c`. Use `swap`. Use `⟨a, ha, fun Q hQ => ?_⟩` and prove the remaining obligations. Break down `Finset.mem_insert.mp hQ with rfl | hQ` into its components or cases. Conclude with `haP`.

Conclude with `haS Q hQ`. Take `⟨b, hb, hbP⟩` from `exists_mem_notMem_coeIdeal_mul c hc P hP.ne_top`. Establish `hnle : ¬ S.inf id ≤ P`. Rewrite using `[hP.isPrime.inf_le']`. Introduce and unpack `⟨Q, hQ, hQP⟩`.

Establish `: Q = P` using `(hS Q (Finset.mem_insert_of_mem hQ)).eq_of_le hP.ne_top hQP`. Conclude with `hPS (this ▸ hQ)`. Take `⟨e, heS, heP⟩` from `SetLike.not_le_iff_exists.mp hnle`. Establish `key : ∀ (Q : Ideal R) (x : R), x ∈ Q → x • b ∈ (Q : FractionalIdeal (nonZeroDivisors R) K) * c`. Introduce `Q x hx`.

Rewrite using `[Algebra.smul_def]`. Conclude with `FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem _ hx) hb`. Use `⟨a + e • b, (c : Submodule R K).add_mem ha ((c : Submodule R K).smul_mem e hb), fun Q hQ h => ?_⟩` and prove the remaining obligations. Break down `Finset.mem_insert.mp hQ with rfl | hQ` into its components or cases. Take `⟨y, p, hp, hy⟩` from `hP.exists_inv heP set J : Submodule R K := (((Q : FractionalIdeal (nonZeroDivisors R) K) * c : FractionalIdeal (nonZeroDivisors R) K) : Submodule R K) with hJ`.

Establish `h1 : e • b ∈ J` using `(J.add_mem_iff_right haP).mp h`. Establish `h2 : y • (e • b) + p • b ∈ J` using `J.add_mem (J.smul_mem y h1) (key Q p hp)`. Rewrite `h2` using `[smul_smul, ← add_smul, hy, one_smul]`. Conclude with `hbP h2`. Establish `heQ : e ∈ Q` using `(Finset.inf_le (f := id) hQ) heS set J : Submodule R K := (((Q : FractionalIdeal (nonZeroDivisors R) K) * c : FractionalIdeal (nonZeroDivisors R) K) : Submodule R K) with hJ`.

Conclude with `haS Q hQ ((J.add_mem_iff_left (key Q e heQ)).mp h)`.
-/
theorem exists_mem_forall_notMem_coeIdeal_mul {R K : Type} [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] (c : FractionalIdeal (nonZeroDivisors R) K)
    (hc : c ≠ 0) (S : Finset (Ideal R)) (hS : ∀ Q ∈ S, Q.IsMaximal) :
    ∃ a : K, a ∈ c ∧ ∀ Q ∈ S, a ∉ (Q : FractionalIdeal (nonZeroDivisors R) K) * c := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, c.zero_mem, by simp⟩
  | insert P S hPS ih =>
    obtain ⟨a, ha, haS⟩ := ih (fun Q hQ => hS Q (Finset.mem_insert_of_mem hQ))
    have hP : P.IsMaximal := hS P (Finset.mem_insert_self _ _)
    by_cases haP : a ∈ (P : FractionalIdeal (nonZeroDivisors R) K) * c
    swap
    · refine ⟨a, ha, fun Q hQ => ?_⟩
      rcases Finset.mem_insert.mp hQ with rfl | hQ
      · exact haP
      · exact haS Q hQ
    obtain ⟨b, hb, hbP⟩ := exists_mem_notMem_coeIdeal_mul c hc P hP.ne_top
    have hnle : ¬ S.inf id ≤ P := by
      rw [hP.isPrime.inf_le']
      rintro ⟨Q, hQ, hQP⟩
      have : Q = P := (hS Q (Finset.mem_insert_of_mem hQ)).eq_of_le hP.ne_top hQP
      exact hPS (this ▸ hQ)
    obtain ⟨e, heS, heP⟩ := SetLike.not_le_iff_exists.mp hnle
    have key : ∀ (Q : Ideal R) (x : R), x ∈ Q →
        x • b ∈ (Q : FractionalIdeal (nonZeroDivisors R) K) * c := by
      intro Q x hx
      rw [Algebra.smul_def]
      exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem _ hx) hb
    refine ⟨a + e • b, (c : Submodule R K).add_mem ha ((c : Submodule R K).smul_mem e hb),
      fun Q hQ h => ?_⟩
    rcases Finset.mem_insert.mp hQ with rfl | hQ
    · obtain ⟨y, p, hp, hy⟩ := hP.exists_inv heP
      set J : Submodule R K := (((Q : FractionalIdeal (nonZeroDivisors R) K) * c :
        FractionalIdeal (nonZeroDivisors R) K) : Submodule R K) with hJ
      have h1 : e • b ∈ J := (J.add_mem_iff_right haP).mp h
      have h2 : y • (e • b) + p • b ∈ J := J.add_mem (J.smul_mem y h1) (key Q p hp)
      rw [smul_smul, ← add_smul, hy, one_smul] at h2
      exact hbP h2
    · have heQ : e ∈ Q := (Finset.inf_le (f := id) hQ) heS
      set J : Submodule R K := (((Q : FractionalIdeal (nonZeroDivisors R) K) * c :
        FractionalIdeal (nonZeroDivisors R) K) : Submodule R K) with hJ
      exact haS Q hQ ((J.add_mem_iff_left (key Q e heQ)).mp h)

/- English proof (translation)
Introduce `E _ _ c hc N hN`. Establish `hN' : Ideal.span {N} ≠ (0 : Ideal (𝓞 E))`. Simplify using `using hN`. Establish `hfin : {Q : Ideal (𝓞 E) | Q.IsMaximal ∧ N ∈ Q}.Finite`. Use `((Ideal.finite_factors hN').image (fun v => v.asIdeal)).subset ?_` and prove the remaining obligations.

Introduce and unpack `Q ⟨hQ, hNQ⟩`. Establish `h0 : Q ≠ ⊥`. Introduce and unpack `rfl`. Conclude with `hN (by simpa using hNQ)`. Use `⟨⟨Q, hQ.isPrime, h0⟩, ?_, rfl⟩` and prove the remaining obligations.

Simplify `hNQ` using `[Ideal.dvd_iff_le]`. Take `⟨a, ha, h⟩` from `exists_mem_forall_notMem_coeIdeal_mul c hc hfin.toFinset (fun Q hQ => (hfin.mem_toFinset.mp hQ).1)`. Conclude with `⟨a, ha, fun Q hQ hNQ => h Q (hfin.mem_toFinset.mpr ⟨hQ, hNQ⟩)⟩`.
-/
theorem exists_mem_fractionalIdeal_generator_at_primes_over :
    ∀ (E : Type) [Field E] [NumberField E] (c : FractionalIdeal (nonZeroDivisors (𝓞 E)) E),
      c ≠ 0 → ∀ N : 𝓞 E, N ≠ 0 → ∃ a : E, a ∈ c ∧ ∀ Q : Ideal (𝓞 E), Q.IsMaximal → N ∈ Q →
        a ∉ (Q : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c := by
  intro E _ _ c hc N hN
  have hN' : Ideal.span {N} ≠ (0 : Ideal (𝓞 E)) := by
    simpa using hN
  have hfin : {Q : Ideal (𝓞 E) | Q.IsMaximal ∧ N ∈ Q}.Finite := by
    refine ((Ideal.finite_factors hN').image (fun v => v.asIdeal)).subset ?_
    rintro Q ⟨hQ, hNQ⟩
    have h0 : Q ≠ ⊥ := by
      rintro rfl
      exact hN (by simpa using hNQ)
    refine ⟨⟨Q, hQ.isPrime, h0⟩, ?_, rfl⟩
    simpa [Ideal.dvd_iff_le] using hNQ
  obtain ⟨a, ha, h⟩ := exists_mem_forall_notMem_coeIdeal_mul c hc hfin.toFinset
    (fun Q hQ => (hfin.mem_toFinset.mp hQ).1)
  exact ⟨a, ha, fun Q hQ hNQ => h Q (hfin.mem_toFinset.mpr ⟨hQ, hNQ⟩)⟩

end GlobalTheory
