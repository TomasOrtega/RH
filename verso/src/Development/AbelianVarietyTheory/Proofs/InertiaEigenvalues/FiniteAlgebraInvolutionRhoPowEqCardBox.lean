import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma

/- English proof (translation)
Introduce `K B a r φ c hφ hker hint k`. Establish `hK : (intUnits K.O B.A).subgroupOf B.T = φ.ker`. Use extensionality with `t`. Rewrite using `[MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hker]`. Unfold `InvAlg.rho`.

Rewrite using `[hK]`. Set `e` to `QuotientGroup.quotientKerEquivOfSurjective φ hφ`. Establish `he : ∀ q : B.T ⧸ φ.ker, e q = φ (Quotient.out q)`. Introduce `q`. Use `conv_lhs => rw [← QuotientGroup.out_eq' q]`.

Both sides reduce to the same expression. Establish `h1 : Nat.card {q : B.T ⧸ φ.ker // IsIntegral K.O ((((Quotient.out q : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * algebraMap K.O B.A a ^ k : B.A)} = Nat.card {v : Fin r → ℤ // ∀ i, v i ∈ Set.Icc (-((k * c i : ℕ) : ℤ)) ((k * c i : ℕ) : ℤ)}`. Apply `Nat.card_congr` to reduce the goal to its premises. Use `(e.toEquiv.trans Multiplicative.toAdd).subtypeEquiv ?_` and prove the remaining obligations. Introduce `q`.

Simplify using `only [MulEquiv.toEquiv_eq_coe, Equiv.trans_apply, MulEquiv.coe_toEquiv, he, Set.mem_Icc, ← abs_le]`. Conclude with `hint _ k`. Rewrite using `[h1, Nat.card_congr (Equiv.subtypePiEquivPi), Nat.card_pi]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `h2 : Nat.card (Set.Icc (-((k * c i : ℕ) : ℤ)) ((k * c i : ℕ) : ℤ)) = 2 * k * c i + 1`.

Rewrite using `[Nat.card_eq_card_toFinset, Set.toFinset_Icc, Int.card_Icc, show 2 * k * c i = 2 * (k * c i) by ring]`. Use linear arithmetic over natural numbers and integers. Conclude with `h2`.
-/
theorem rho_pow_eq_card_box : ∀ (K : UQ) (B : InvAlg K) (a : K.O) (r : ℕ) (φ : B.T →* Multiplicative (Fin r → ℤ)) (c : Fin r → ℕ), Function.Surjective φ → (∀ t : B.T, φ t = 1 ↔ (t : B.Aˣ) ∈ intUnits K.O B.A) → (∀ (t : B.T) (k : ℕ), IsIntegral K.O ((((t : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * algebraMap K.O B.A a ^ k) ↔ ∀ i, |Multiplicative.toAdd (φ t) i| ≤ ((k * c i : ℕ) : ℤ)) → ∀ k : ℕ, B.rho (algebraMap K.O B.A a ^ k) = ∏ i, (2 * k * c i + 1) := by
  intro K B a r φ c hφ hker hint k
  have hK : (intUnits K.O B.A).subgroupOf B.T = φ.ker := by
    ext t
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hker]
  unfold InvAlg.rho
  rw [hK]
  let e := QuotientGroup.quotientKerEquivOfSurjective φ hφ
  have he : ∀ q : B.T ⧸ φ.ker, e q = φ (Quotient.out q) := by
    intro q
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  have h1 : Nat.card {q : B.T ⧸ φ.ker //
      IsIntegral K.O ((((Quotient.out q : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * algebraMap K.O B.A a ^ k : B.A)} =
      Nat.card {v : Fin r → ℤ // ∀ i, v i ∈ Set.Icc (-((k * c i : ℕ) : ℤ)) ((k * c i : ℕ) : ℤ)} := by
    apply Nat.card_congr
    refine (e.toEquiv.trans Multiplicative.toAdd).subtypeEquiv ?_
    intro q
    simp only [MulEquiv.toEquiv_eq_coe, Equiv.trans_apply, MulEquiv.coe_toEquiv, he, Set.mem_Icc, ← abs_le]
    exact hint _ k
  rw [h1, Nat.card_congr (Equiv.subtypePiEquivPi), Nat.card_pi]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h2 : Nat.card (Set.Icc (-((k * c i : ℕ) : ℤ)) ((k * c i : ℕ) : ℤ)) = 2 * k * c i + 1 := by
    rw [Nat.card_eq_card_toFinset, Set.toFinset_Icc, Int.card_Icc, show 2 * k * c i = 2 * (k * c i) by ring]
    omega
  exact h2

end GlobalTheory.UnitLemma
