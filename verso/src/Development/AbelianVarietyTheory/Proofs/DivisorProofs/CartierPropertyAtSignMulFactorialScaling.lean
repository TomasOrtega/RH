import Development.AbelianVarietyTheory.Definitions.Divisors.IsFlatLift
open GlobalTheory GlobalTheory.DI

namespace GlobalTheory.DI

/- English proof (translation)
Establish `hcop : IsCoprime ((-1 : ℤ) ^ a * (a.factorial : ℤ)) (p : ℤ)`. Apply `IsCoprime.mul_left` to reduce the goal to its premises. Conclude with `IsCoprime.pow_left (isCoprime_one_left.neg_left)`. Rewrite using `[Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]`. Conclude with `Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp.out).2 (fun h => absurd ((Nat.Prime.dvd_factorial hp.out).1 h) (by omega)))`.

Take `⟨u, v, huv⟩` from `hcop`. Use `⟨u, fun y => ?_⟩` and prove the remaining obligations. Establish `h1 : u * ((-1 : ℤ) ^ a * (a.factorial : ℤ)) = 1 - v * p` using `by linarith`. Rewrite using `[h1, sub_smul, one_smul, mul_smul, natCast_zsmul, hE, smul_zero, sub_zero]`.
-/
theorem exists_inv_signFactorial {E : Type} [AddCommGroup E] (p : ℕ) [hp : Fact p.Prime]
    (hE : ∀ x : E, p • x = 0) (a : ℕ) (ha : a < p) :
    ∃ u : ℤ, ∀ y : E, (u * ((-1 : ℤ) ^ a * (a.factorial : ℤ))) • y = y := by
  have hcop : IsCoprime ((-1 : ℤ) ^ a * (a.factorial : ℤ)) (p : ℤ) := by
    apply IsCoprime.mul_left
    · exact IsCoprime.pow_left (isCoprime_one_left.neg_left)
    · rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
      exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp.out).2
        (fun h => absurd ((Nat.Prime.dvd_factorial hp.out).1 h) (by omega)))
  obtain ⟨u, v, huv⟩ := hcop
  refine ⟨u, fun y => ?_⟩
  have h1 : u * ((-1 : ℤ) ^ a * (a.factorial : ℤ)) = 1 - v * p := by linarith
  rw [h1, sub_smul, one_smul, mul_smul, natCast_zsmul, hE, smul_zero, sub_zero]

/- English proof (translation)
Introduce `E _ p hp d γ γ' N T hE hN hγ hC`. Establish `hp0 : 0 < p` using `hp.out.pos`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx h0`. Rewrite `h0` using `[hγ 0 x hx]`.

Simplify using `at h0`. Conclude with `hC.inj_zero x hx h0`. Introduce `a x hx z hz h`. Distinguish the cases in `hpa : p ≤ a + 1`. Rewrite `hx` using `[hN _ hpa]`.

Conclude with `(AddSubgroup.mem_bot.1 hx)`. Take `⟨u, hu⟩` from `exists_inv_signFactorial (E := E) p hE (a + 1) (by omega)`. Apply `hC.inj_succ a x hx (u • z) (AddSubgroup.zsmul_mem _ hz u)` to reduce the goal to its premises. Rewrite `h` using `[hγ _ x hx]`. Rewrite using `[map_zsmul, ← h, ← mul_smul, hu]`.

Introduce `y hy hd`. Take `⟨x, hx, rfl⟩` from `hC.surj_zero y hy hd`. Conclude with `⟨x, hx, by rw [hγ 0 x hx]; simp⟩`. Introduce `a y hy hd`. Take `⟨x, hx, z, hz, rfl⟩` from `hC.surj_succ a y hy hd`.

Distinguish the cases in `hpa : p ≤ a + 1`. Establish `hx0 : x = 0` using `by rw [hN _ hpa] at hx; exact AddSubgroup.mem_bot.1 hx`. Substitute `hx0` using the available equality. Use `⟨0, AddSubgroup.zero_mem _, z, hz, ?_⟩` and prove the remaining obligations. Rewrite using `[hγ (a + 1) 0 (AddSubgroup.zero_mem _)]`.

Simplify using the standard rewrite rules. Take `⟨u, hu⟩` from `exists_inv_signFactorial (E := E) p hE (a + 1) (by omega)`. Use `⟨u • x, AddSubgroup.zsmul_mem _ hx u, z, hz, ?_⟩` and prove the remaining obligations. Rewrite using `[hγ _ _ (AddSubgroup.zsmul_mem _ hx u), map_zsmul, ← mul_smul, mul_comm, hu]`.
-/
theorem cartierAt_signFactorial : ∀ {E : Type} [AddCommGroup E] (p : ℕ) [Fact p.Prime] (d γ : E →+ E) (γ' : E → E)
    (N T : ℕ → AddSubgroup E), (∀ x : E, p • x = 0) → (∀ a, p ≤ a → N a = ⊥) →
    (∀ a, ∀ x ∈ N a, γ' x = ((-1 : ℤ) ^ a * (a.factorial : ℤ)) • γ x) → CartierAt d γ N T → CartierAt d γ' N T := by
  intro E _ p hp d γ γ' N T hE hN hγ hC
  have hp0 : 0 < p := hp.out.pos
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx h0
    rw [hγ 0 x hx] at h0
    simp at h0
    exact hC.inj_zero x hx h0
  · intro a x hx z hz h
    by_cases hpa : p ≤ a + 1
    · rw [hN _ hpa] at hx; exact (AddSubgroup.mem_bot.1 hx)
    · obtain ⟨u, hu⟩ := exists_inv_signFactorial (E := E) p hE (a + 1) (by omega)
      apply hC.inj_succ a x hx (u • z) (AddSubgroup.zsmul_mem _ hz u)
      rw [hγ _ x hx] at h
      rw [map_zsmul, ← h, ← mul_smul, hu]
  · intro y hy hd
    obtain ⟨x, hx, rfl⟩ := hC.surj_zero y hy hd
    exact ⟨x, hx, by rw [hγ 0 x hx]; simp⟩
  · intro a y hy hd
    obtain ⟨x, hx, z, hz, rfl⟩ := hC.surj_succ a y hy hd
    by_cases hpa : p ≤ a + 1
    · have hx0 : x = 0 := by rw [hN _ hpa] at hx; exact AddSubgroup.mem_bot.1 hx
      subst hx0
      refine ⟨0, AddSubgroup.zero_mem _, z, hz, ?_⟩
      rw [hγ (a + 1) 0 (AddSubgroup.zero_mem _)]; simp
    · obtain ⟨u, hu⟩ := exists_inv_signFactorial (E := E) p hE (a + 1) (by omega)
      refine ⟨u • x, AddSubgroup.zsmul_mem _ hx u, z, hz, ?_⟩
      rw [hγ _ _ (AddSubgroup.zsmul_mem _ hx u), map_zsmul, ← mul_smul, mul_comm, hu]

end GlobalTheory.DI
