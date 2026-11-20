import Formalism.PadicSubsetSums.CentralIdempotents.GaloisIrreducibility

open Polynomial

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

variable {K : Type} [Field K] {N : ℕ}

/- English proof (translation)
The claim follows from `degree_sum_fin_lt c`.
-/
theorem monicOf_degree_lt (c : Fin N → K) :
    (∑ i : Fin N, C (c i) * X ^ (i : ℕ)).degree < (N : WithBot ℕ) := degree_sum_fin_lt c

/- English proof (translation)
Rewrite using `[monicOf]`. Conclude with `monic_X_pow_add (monicOf_degree_lt c)`.
-/
theorem monicOf_monic (c : Fin N → K) : (monicOf c).Monic := by
  rw [monicOf]
  exact monic_X_pow_add (monicOf_degree_lt c)

/- English proof (translation)
Rewrite using `[monicOf, natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]`. Rewrite using `[degree_X_pow]`. Conclude with `monicOf_degree_lt c`.
-/
theorem monicOf_natDegree (c : Fin N → K) : (monicOf c).natDegree = N := by
  rw [monicOf, natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
  rw [degree_X_pow]
  exact monicOf_degree_lt c

/- English proof (translation)
Rewrite using `[monicOf, coeff_add, coeff_X_pow, if_neg (Nat.ne_of_lt i.isLt), zero_add, finset_sum_coeff]`. Simplify using `only [coeff_C_mul_X_pow]`. Rewrite using `[Finset.sum_eq_single i]`. Simplify using the standard rewrite rules. Introduce `j _ hj`.

Rewrite using `[if_neg]`. Conclude with `fun h => hj (Fin.ext h).symm`. Simplify using the standard rewrite rules.
-/
theorem monicOf_coeff (c : Fin N → K) (i : Fin N) : (monicOf c).coeff i = c i := by
  rw [monicOf, coeff_add, coeff_X_pow, if_neg (Nat.ne_of_lt i.isLt), zero_add,
    finset_sum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [if_neg]
    exact fun h => hj (Fin.ext h).symm
  · simp

/- English proof (translation)
Introduce `c d h`. Use function extensionality and compare the values at `i`. Rewrite using `[← monicOf_coeff c i, ← monicOf_coeff d i, h]`.
-/
theorem monicOf_injective : Function.Injective (monicOf : (Fin N → K) → K[X]) := by
  intro c d h
  funext i
  rw [← monicOf_coeff c i, ← monicOf_coeff d i, h]

/- English proof (translation)
Substitute `hN` using the available equality. Rewrite using `[monicOf, Fin.sum_univ_eq_sum_range (fun i => C (p.coeff i) * X ^ i)]`. Conclude with `hp.as_sum.symm`.
-/
theorem monicOf_coeffs {p : K[X]} (hp : p.Monic) (hN : p.natDegree = N) :
    monicOf (fun i : Fin N => p.coeff i) = p := by
  subst hN
  rw [monicOf, Fin.sum_univ_eq_sum_range (fun i => C (p.coeff i) * X ^ i)]
  exact hp.as_sum.symm

/- English proof (translation)
Introduce `K _ _ d hd`. Establish `hq1 : 1 < Fintype.card K` using `Fintype.one_lt_card`. Establish `hd0 : d ≠ 0` using `by omega`. Establish `hdvd : ∀ f : K[X], Irreducible f → f.natDegree = d → f ∣ X ^ (Fintype.card K ^ d) - X`. Introduce `f hf hfd`.

Use `haveI := Fact.mk hf`. Use `haveI : Module.Finite K (AdjoinRoot f) := (AdjoinRoot.powerBasis hf.ne_zero).finite`. Use `haveI : Finite (AdjoinRoot f) := Module.finite_of_finite K`. Use `letI : Fintype (AdjoinRoot f) := Fintype.ofFinite _`. Establish `hcard : Fintype.card (AdjoinRoot f) = Fintype.card K ^ d`.

Rewrite using `[Module.card_fintype (AdjoinRoot.powerBasis hf.ne_zero).basis, Fintype.card_fin, AdjoinRoot.powerBasis_dim, hfd]`. Rewrite using `[← AdjoinRoot.mk_eq_zero, map_sub, map_pow, AdjoinRoot.mk_X, ← hcard, FiniteField.pow_card, sub_self]`. Establish `main : ∀ S : Finset (Fin d → K), (∀ c ∈ S, Irreducible (monicOf c)) → d * S.card ≤ Fintype.card K ^ d`. Introduce `S hS`. Establish `hcop : ∀ c ∈ S, ∀ c' ∈ S, c ≠ c' → IsCoprime (monicOf c) (monicOf c')`.

Introduce `c hc c' hc' hne`. Rewrite using `[(hS c hc).coprime_iff_not_dvd]`. Introduce `hdv`. Apply `hne` to reduce the goal to its premises. Apply `monicOf_injective` to reduce the goal to its premises.

Conclude with `eq_of_monic_of_associated (monicOf_monic c) (monicOf_monic c') ((hS c hc).associated_of_dvd (hS c' hc') hdv)`. Establish `hprod : ∏ c ∈ S, monicOf c ∣ X ^ (Fintype.card K ^ d) - X` using `Finset.prod_dvd_of_coprime (fun c hc c' hc' hne => hcop c hc c' hc' hne) (fun c hc => hdvd _ (hS c hc) (monicOf_natDegree c))`. Establish `hdeg : (∏ c ∈ S, monicOf c).natDegree = d * S.card`. Rewrite using `[natDegree_prod_of_monic _ _ (fun c _ => monicOf_monic c), Finset.sum_congr rfl (fun c _ => monicOf_natDegree c), Finset.sum_const, smul_eq_mul, mul_comm]`. Establish `hle` using `natDegree_le_of_dvd hprod (FiniteField.X_pow_card_pow_sub_X_ne_zero K hd0 hq1)`.

Rewrite `hle` using `[hdeg, FiniteField.X_pow_card_pow_sub_X_natDegree_eq K hd0 hq1]`. Conclude with `hle`. Conclude with `main _ (fun c hc => (Finset.mem_filter.mp hc).2)`.
-/
theorem irreducible_count_upper : IrredCountUpper := by
  intro K _ _ d hd
  classical
  have hq1 : 1 < Fintype.card K := Fintype.one_lt_card
  have hd0 : d ≠ 0 := by omega
  have hdvd : ∀ f : K[X], Irreducible f → f.natDegree = d → f ∣ X ^ (Fintype.card K ^ d) - X := by
    intro f hf hfd
    haveI := Fact.mk hf
    haveI : Module.Finite K (AdjoinRoot f) := (AdjoinRoot.powerBasis hf.ne_zero).finite
    haveI : Finite (AdjoinRoot f) := Module.finite_of_finite K
    letI : Fintype (AdjoinRoot f) := Fintype.ofFinite _
    have hcard : Fintype.card (AdjoinRoot f) = Fintype.card K ^ d := by
      rw [Module.card_fintype (AdjoinRoot.powerBasis hf.ne_zero).basis, Fintype.card_fin,
        AdjoinRoot.powerBasis_dim, hfd]
    rw [← AdjoinRoot.mk_eq_zero, map_sub, map_pow, AdjoinRoot.mk_X, ← hcard, FiniteField.pow_card,
      sub_self]
  have main : ∀ S : Finset (Fin d → K), (∀ c ∈ S, Irreducible (monicOf c)) →
      d * S.card ≤ Fintype.card K ^ d := by
    intro S hS
    have hcop : ∀ c ∈ S, ∀ c' ∈ S, c ≠ c' → IsCoprime (monicOf c) (monicOf c') := by
      intro c hc c' hc' hne
      rw [(hS c hc).coprime_iff_not_dvd]
      intro hdv
      apply hne
      apply monicOf_injective
      exact eq_of_monic_of_associated (monicOf_monic c) (monicOf_monic c')
        ((hS c hc).associated_of_dvd (hS c' hc') hdv)
    have hprod : ∏ c ∈ S, monicOf c ∣ X ^ (Fintype.card K ^ d) - X :=
      Finset.prod_dvd_of_coprime (fun c hc c' hc' hne => hcop c hc c' hc' hne)
        (fun c hc => hdvd _ (hS c hc) (monicOf_natDegree c))
    have hdeg : (∏ c ∈ S, monicOf c).natDegree = d * S.card := by
      rw [natDegree_prod_of_monic _ _ (fun c _ => monicOf_monic c),
        Finset.sum_congr rfl (fun c _ => monicOf_natDegree c), Finset.sum_const, smul_eq_mul, mul_comm]
    have hle := natDegree_le_of_dvd hprod (FiniteField.X_pow_card_pow_sub_X_ne_zero K hd0 hq1)
    rw [hdeg, FiniteField.X_pow_card_pow_sub_X_natDegree_eq K hd0 hq1] at hle
    exact hle
  exact main _ (fun c hc => (Finset.mem_filter.mp hc).2)

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
