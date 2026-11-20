import Mathlib

universe u_1

namespace GlobalTheory.CoprimeNatNotMem

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem natCast_not_mem_of_coprime {Rg : Type u_1} [CommRing Rg] {P : Ideal Rg} (hP : P ≠ ⊤)
    {p n : ℕ} (h : Nat.Coprime p n) (hp : (p : Rg) ∈ P) : (n : Rg) ∉ P := by
  intro hn

  obtain ⟨u, v, huv⟩ : IsCoprime (p : Rg) (n : Rg) := by
    have hz : IsCoprime (p : ℤ) (n : ℤ) := Nat.isCoprime_iff_coprime.mpr h
    simpa using hz.map (Int.castRingHom Rg)
  apply hP
  rw [Ideal.eq_top_iff_one, ← huv]
  exact P.add_mem (P.mul_mem_left u hp) (P.mul_mem_left v hn)

end GlobalTheory.CoprimeNatNotMem
