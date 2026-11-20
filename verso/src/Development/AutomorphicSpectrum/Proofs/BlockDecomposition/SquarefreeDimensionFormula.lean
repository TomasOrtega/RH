import Mathlib
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardParabolicSubgroupStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HarishChandraDimensionStatement

open ReciprocityTheory.Ty.Fin

namespace GlobalTheory.CompanionTheory.TyFin

/- English proof (translation)
Establish `e : Finset.Icc 1 d = Finset.Ico 1 (d + 1)`. Use extensionality with `x`. Simplify using `only [Finset.mem_Icc, Finset.mem_Ico]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[e, Finset.prod_Ico_succ_top h]`.
-/
theorem prod_Icc_one_eq (f : ℕ → ℤ) (d : ℕ) (h : 1 ≤ d) :
    ∏ i ∈ Finset.Icc 1 d, f i = (∏ i ∈ Finset.Ico 1 d, f i) * f d := by
  have e : Finset.Icc 1 d = Finset.Ico 1 (d + 1) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [e, Finset.prod_Ico_succ_top h]

/- English proof (translation)
Introduce `K _ _ _ n s b lam hb hd`. Establish `hq1 : (1 : ℤ) < (Fintype.card K : ℤ)`. Use `Fintype.one_lt_card (α := K)` as an intermediate fact. Conclude with `this` after adjusting the coercions. Establish `hne : ∀ i : ℕ, 1 ≤ i → (Fintype.card K : ℤ) ^ i - 1 ≠ 0`.

Introduce `i hi h`. Establish `: (1 : ℤ) < (Fintype.card K : ℤ) ^ i` using `one_lt_pow₀ hq1 (by omega)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hdim` using `GlobalTheory.T.harish_chandra_dimension K (Fin n) s b lam`. Take `⟨hGL, hP⟩` from `GlobalTheory.T.card_parabolic_subgroup K (Fin n)`.

Take `⟨hPc, hch⟩` from `hP s b`. Rewrite `hGL`, `hch` using `[Fintype.card_fin]`. Establish `hblk : ∀ c, (Nat.card (GL {i // b i = c} K) : ℤ) = (Fintype.card K : ℤ) ^ (Fintype.card {i // b i = c}).choose 2 * ((∏ i ∈ Finset.Ico 1 (Fintype.card {i // b i = c}), ((Fintype.card K : ℤ) ^ i - 1)) * ((Fintype.card K : ℤ) ^ Fintype.card {i // b i = c} - 1))`. Introduce `c`. Establish `hpos : 1 ≤ Fintype.card {i // b i = c}`.

Take `⟨i, hi⟩` from `hb c`. Conclude with `Fintype.card_pos_iff.2 ⟨⟨i, hi⟩⟩`. Rewrite using `[(GlobalTheory.T.card_parabolic_subgroup K {i // b i = c}).1, prod_Icc_one_eq (fun i => (Fintype.card K : ℤ) ^ i - 1) _ hpos]`. Establish `hZ : (Module.finrank ℂ (Formalism.IrreducibleCountingLemmas.TYPES.hcSpace K b lam) : ℤ) * (Nat.card (Formalism.IrreducibleCountingLemmas.TYPES.parab K b) : ℤ) = (Nat.card (GL (Fin n) K) : ℤ) * ∏ c, (Module.finrank ℂ (lam c) : ℤ)`. Conclude with `hdim` after adjusting the coercions.

Establish `hPz : (Nat.card (Formalism.IrreducibleCountingLemmas.TYPES.parab K b) : ℤ) = (Fintype.card K : ℤ) ^ Fintype.card {p : Fin n × Fin n // b p.1 < b p.2} * ((Fintype.card K : ℤ) ^ (∑ c, (Fintype.card {i // b i = c}).choose 2) * ((∏ c, ∏ i ∈ Finset.Ico 1 (Fintype.card {i // b i = c}), …`. Rewrite using `[hPc]`. Use `push_cast`. Rewrite using `[Finset.prod_congr rfl (fun c _ => hblk c), Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]`. Rewrite `hZ` using `[hPz, hGL, hch, Finset.prod_congr rfl (fun c _ => hd c), pow_add]`.

Establish `hA : (∏ c, ∏ i ∈ Finset.Ico 1 (Fintype.card {i // b i = c}), ((Fintype.card K : ℤ) ^ i - 1)) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun c _ => Finset.prod_ne_zero_iff.2 fun i hi => hne i (Finset.mem_Ico.1 hi).1`. Establish `hq0 : (Fintype.card K : ℤ) ≠ 0` using `by linarith`. Establish `hc : (Fintype.card K : ℤ) ^ Fintype.card {p : Fin n × Fin n // b p.1 < b p.2} * (Fintype.card K : ℤ) ^ (∑ c, (Fintype.card {i // b i = c}).choose 2) * (∏ c, ∏ i ∈ Finset.Ico 1 (Fintype.card {i // b i = c}), ((Fintype.card K : ℤ) ^ i - 1)) ≠ 0` using `mul_ne_zero (mul_ne_zero (pow_ne_zero _ hq0) (pow_ne_zero _ hq0)) hA`. Apply `mul_left_cancel₀ hc` to reduce the goal to its premises. Take the linear combination `hZ`.
-/
theorem sqfreeDimAll : ReciprocityTheory.Ty.Fin.St.SqfreeDimAll := by
  intro K _ _ _ n s b lam hb hd
  have hq1 : (1 : ℤ) < (Fintype.card K : ℤ) := by
    have := Fintype.one_lt_card (α := K)
    exact_mod_cast this
  have hne : ∀ i : ℕ, 1 ≤ i → (Fintype.card K : ℤ) ^ i - 1 ≠ 0 := by
    intro i hi h
    have : (1 : ℤ) < (Fintype.card K : ℤ) ^ i := one_lt_pow₀ hq1 (by omega)
    linarith
  have hdim := GlobalTheory.T.harish_chandra_dimension K (Fin n) s b lam
  obtain ⟨hGL, hP⟩ := GlobalTheory.T.card_parabolic_subgroup K (Fin n)
  obtain ⟨hPc, hch⟩ := hP s b
  rw [Fintype.card_fin] at hGL hch
  have hblk : ∀ c, (Nat.card (GL {i // b i = c} K) : ℤ) =
      (Fintype.card K : ℤ) ^ (Fintype.card {i // b i = c}).choose 2 *
        ((∏ i ∈ Finset.Ico 1 (Fintype.card {i // b i = c}), ((Fintype.card K : ℤ) ^ i - 1)) *
          ((Fintype.card K : ℤ) ^ Fintype.card {i // b i = c} - 1)) := by
    intro c
    have hpos : 1 ≤ Fintype.card {i // b i = c} := by
      obtain ⟨i, hi⟩ := hb c
      exact Fintype.card_pos_iff.2 ⟨⟨i, hi⟩⟩
    rw [(GlobalTheory.T.card_parabolic_subgroup K {i // b i = c}).1,
      prod_Icc_one_eq (fun i => (Fintype.card K : ℤ) ^ i - 1) _ hpos]
  have hZ : (Module.finrank ℂ (Formalism.IrreducibleCountingLemmas.TYPES.hcSpace K b lam) : ℤ) *
      (Nat.card (Formalism.IrreducibleCountingLemmas.TYPES.parab K b) : ℤ) =
      (Nat.card (GL (Fin n) K) : ℤ) * ∏ c, (Module.finrank ℂ (lam c) : ℤ) := by
    exact_mod_cast hdim
  have hPz : (Nat.card (Formalism.IrreducibleCountingLemmas.TYPES.parab K b) : ℤ) =
      (Fintype.card K : ℤ) ^ Fintype.card {p : Fin n × Fin n // b p.1 < b p.2} *
        ((Fintype.card K : ℤ) ^ (∑ c, (Fintype.card {i // b i = c}).choose 2) *
          ((∏ c, ∏ i ∈ Finset.Ico 1 (Fintype.card {i // b i = c}), ((Fintype.card K : ℤ) ^ i - 1)) *
            ∏ c, ((Fintype.card K : ℤ) ^ Fintype.card {i // b i = c} - 1))) := by
    rw [hPc]
    push_cast
    rw [Finset.prod_congr rfl (fun c _ => hblk c), Finset.prod_mul_distrib,
      Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [hPz, hGL, hch, Finset.prod_congr rfl (fun c _ => hd c), pow_add] at hZ
  have hA : (∏ c, ∏ i ∈ Finset.Ico 1 (Fintype.card {i // b i = c}),
      ((Fintype.card K : ℤ) ^ i - 1)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun c _ => Finset.prod_ne_zero_iff.2 fun i hi =>
      hne i (Finset.mem_Ico.1 hi).1
  have hq0 : (Fintype.card K : ℤ) ≠ 0 := by linarith
  have hc : (Fintype.card K : ℤ) ^ Fintype.card {p : Fin n × Fin n // b p.1 < b p.2} *
      (Fintype.card K : ℤ) ^ (∑ c, (Fintype.card {i // b i = c}).choose 2) *
      (∏ c, ∏ i ∈ Finset.Ico 1 (Fintype.card {i // b i = c}), ((Fintype.card K : ℤ) ^ i - 1)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ hq0) (pow_ne_zero _ hq0)) hA
  apply mul_left_cancel₀ hc
  linear_combination hZ

end GlobalTheory.CompanionTheory.TyFin
