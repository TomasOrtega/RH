import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.IsChainFirst

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top.FlDeg.CoeffDelta

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Top.FlDeg

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [m.degree_one, m.leadingCoeff_one]`. Consider the case `insert a s has ih`. Take `⟨ih1, ih2⟩` from `ih fun i hi => h i (Finset.mem_insert_of_mem hi)`. Take `⟨ha1, ha2⟩` from `h a (Finset.mem_insert_self a s)`.

Establish `hne : ∀ f : MvPolynomial σ ℝ, m.leadingCoeff f = 1 → f ≠ 0` using `fun f hf => m.leadingCoeff_ne_zero_iff.mp (by rw [hf]; exact one_ne_zero)`. Rewrite using `[Finset.prod_insert has, Finset.sum_insert has, m.degree_mul (hne _ ha2) (hne _ ih2), m.leadingCoeff_mul, ha1, ih1, ha2, ih2]`. Simplify using the standard rewrite rules.
-/
theorem degree_prod_monic {σ ι : Type*} (m : MonomialOrder σ) (s : Finset ι)
    (P : ι → MvPolynomial σ ℝ) (d : ι → σ →₀ ℕ)
    (h : ∀ i ∈ s, m.degree (P i) = d i ∧ m.leadingCoeff (P i) = 1) :
    m.degree (∏ i ∈ s, P i) = ∑ i ∈ s, d i ∧ m.leadingCoeff (∏ i ∈ s, P i) = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [m.degree_one, m.leadingCoeff_one]
  | insert a s has ih =>
    obtain ⟨ih1, ih2⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    obtain ⟨ha1, ha2⟩ := h a (Finset.mem_insert_self a s)
    have hne : ∀ f : MvPolynomial σ ℝ, m.leadingCoeff f = 1 → f ≠ 0 := fun f hf =>
      m.leadingCoeff_ne_zero_iff.mp (by rw [hf]; exact one_ne_zero)
    rw [Finset.prod_insert has, Finset.sum_insert has,
      m.degree_mul (hne _ ha2) (hne _ ih2), m.leadingCoeff_mul, ha1, ih1, ha2, ih2]
    simp

/- English proof (translation)
Establish `hlt : ∀ s, a < s → (MonomialOrder.lex : MonomialOrder σ).toSyn (Finsupp.single (v s) 1) < (MonomialOrder.lex : MonomialOrder σ).toSyn (Finsupp.single (v a) 1)` using `fun s hs => MonomialOrder.lex_lt_iff.mpr (Finsupp.Lex.single_strictAnti (hv hs))`. Establish `hzero : (MonomialOrder.lex : MonomialOrder σ).toSyn 0 < (MonomialOrder.lex : MonomialOrder σ).toSyn (Finsupp.single (v a) 1)`. Rewrite using `[map_zero, ← MonomialOrder.bot_eq_zero]`. Use `bot_lt_iff_ne_bot.mpr fun h => ?_` and prove the remaining obligations. Rewrite `h` using `[MonomialOrder.bot_eq_zero]`.

Establish `h0` using `(MonomialOrder.lex : MonomialOrder σ).toSyn.injective (h.trans (map_zero _).symm)`. Simplify using `at h0`. Establish `hdegX : (MonomialOrder.lex : MonomialOrder σ).degree (X (v a) : MvPolynomial σ ℝ) = Finsupp.single (v a) 1` using `MonomialOrder.degree_X`. Establish `hrest : (MonomialOrder.lex : MonomialOrder σ).toSyn ((MonomialOrder.lex : MonomialOrder σ).degree (∑ s ∈ Finset.Ioo a b, (X (v s) : MvPolynomial σ ℝ))) < (MonomialOrder.lex : MonomialOrder σ).toSyn ((MonomialOrder.lex : MonomialOrder σ).degree (X (v a) : MvPolynomial σ ℝ))`. Rewrite using `[hdegX, MonomialOrder.degree_lt_iff hzero]`.

Introduce `c hc`. Take `⟨s, hs, hcs⟩` from `Finset.mem_biUnion.mp (MvPolynomial.support_sum hc)`. Rewrite `hcs` using `[X, support_monomial, if_neg one_ne_zero, Finset.mem_singleton]`. Rewrite using `[hcs]`. Conclude with `hlt s (Finset.mem_Ioo.mp hs).1`.

Rewrite using `[← Finset.Ioo_insert_left hab, Finset.sum_insert (by simp)]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[MonomialOrder.degree_add_of_lt hrest, hdegX]`. Rewrite using `[MonomialOrder.leadingCoeff_add_of_lt hrest, MonomialOrder.leadingCoeff_X]`.
-/
theorem lex_sum_Ico {σ : Type*} [LinearOrder σ] [WellFoundedGT σ] {n : ℕ} (v : Fin n → σ)
    (hv : StrictMono v) {a b : Fin n} (hab : a < b) :
    (MonomialOrder.lex : MonomialOrder σ).degree (∑ s ∈ Finset.Ico a b, (X (v s) : MvPolynomial σ ℝ))
        = Finsupp.single (v a) 1 ∧
      (MonomialOrder.lex : MonomialOrder σ).leadingCoeff
        (∑ s ∈ Finset.Ico a b, (X (v s) : MvPolynomial σ ℝ)) = 1 := by
  have hlt : ∀ s, a < s → (MonomialOrder.lex : MonomialOrder σ).toSyn (Finsupp.single (v s) 1) <
      (MonomialOrder.lex : MonomialOrder σ).toSyn (Finsupp.single (v a) 1) := fun s hs =>
    MonomialOrder.lex_lt_iff.mpr (Finsupp.Lex.single_strictAnti (hv hs))
  have hzero : (MonomialOrder.lex : MonomialOrder σ).toSyn 0 <
      (MonomialOrder.lex : MonomialOrder σ).toSyn (Finsupp.single (v a) 1) := by
    rw [map_zero, ← MonomialOrder.bot_eq_zero]
    refine bot_lt_iff_ne_bot.mpr fun h => ?_
    rw [MonomialOrder.bot_eq_zero] at h
    have h0 := (MonomialOrder.lex : MonomialOrder σ).toSyn.injective (h.trans (map_zero _).symm)
    simp at h0
  have hdegX : (MonomialOrder.lex : MonomialOrder σ).degree (X (v a) : MvPolynomial σ ℝ)
      = Finsupp.single (v a) 1 := MonomialOrder.degree_X
  have hrest : (MonomialOrder.lex : MonomialOrder σ).toSyn
      ((MonomialOrder.lex : MonomialOrder σ).degree
        (∑ s ∈ Finset.Ioo a b, (X (v s) : MvPolynomial σ ℝ))) <
      (MonomialOrder.lex : MonomialOrder σ).toSyn
        ((MonomialOrder.lex : MonomialOrder σ).degree (X (v a) : MvPolynomial σ ℝ)) := by
    rw [hdegX, MonomialOrder.degree_lt_iff hzero]
    intro c hc
    obtain ⟨s, hs, hcs⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hc)
    rw [X, support_monomial, if_neg one_ne_zero, Finset.mem_singleton] at hcs
    rw [hcs]
    exact hlt s (Finset.mem_Ioo.mp hs).1
  rw [← Finset.Ioo_insert_left hab, Finset.sum_insert (by simp)]
  refine ⟨?_, ?_⟩
  · rw [MonomialOrder.degree_add_of_lt hrest, hdegX]
  · rw [MonomialOrder.leadingCoeff_add_of_lt hrest, MonomialOrder.leadingCoeff_X]

end GlobalTheory.CompanionTheory.Ar.Top.FlDeg.CoeffDelta

namespace GlobalTheory.CompanionTheory.Ar.Top.FlDeg

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Top.FlDeg

/- English proof (translation)
Use extensionality with `⟨τ, a⟩`. Simplify using `only [Finsupp.coe_finset_sum, Finset.sum_apply, Finset.sum_const, smul_eq_mul, Finsupp.coe_smul, Pi.smul_apply, Finsupp.single_apply, Prod.mk.injEq]`. Rewrite using `[Finset.sum_eq_single τ, Finset.sum_eq_single a]`. Simplify using `[rhoM, Fin.card_Ioi]`. Introduce `b _ hb`.

Simplify using `[hb]`. Simplify using the standard rewrite rules. Introduce `τ' _ h`. Simplify using `[h]`. Simplify using the standard rewrite rules.
-/
theorem rhoM_eq_sum (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) :
    (∑ τ : Ψ, ∑ a : Fin N, ∑ _b ∈ Finset.Ioi a, Finsupp.single (τ, a) 1 : (Ψ × Fin N) →₀ ℕ)
      = rhoM Ψ N := by
  ext ⟨τ, a⟩
  simp only [Finsupp.coe_finset_sum, Finset.sum_apply, Finset.sum_const, smul_eq_mul,
    Finsupp.coe_smul, Pi.smul_apply, Finsupp.single_apply, Prod.mk.injEq]
  rw [Finset.sum_eq_single τ, Finset.sum_eq_single a]
  · simp [rhoM, Fin.card_Ioi]
  · intro b _ hb; simp [hb]
  · simp
  · intro τ' _ h; simp [h]
  · simp

/- English proof (translation)
Set `e` to `Fintype.equivFin Ψ`. Use `letI : LinearOrder (Ψ × Fin N) := LinearOrder.lift' (fun p => toLex (e p.1, p.2)) (fun p q h => by`. Establish `h' : (e p.1, p.2) = (e q.1, q.2)` using `toLex.injective h`. Take `⟨h1, h2⟩` from `Prod.mk.inj h'`. Conclude with `Prod.ext (e.injective h1) h2)`.

Use `haveI : WellFoundedGT (Ψ × Fin N) := Finite.to_wellFoundedGT`. Establish `hv : ∀ τ : Ψ, StrictMono (fun s : Fin N => (τ, s))` using `fun τ s t hst => by show toLex (e τ, s) < toLex (e τ, t)`. Conclude with `Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, hst⟩)`. Establish `key` using `CoeffDelta.degree_prod_monic (MonomialOrder.lex : MonomialOrder (Ψ × Fin N)) Finset.univ (fun τ : Ψ => ∏ a : Fin N, ∏ b ∈ Finset.Ioi a, ∑ s ∈ Finset.Ico a b, (X (τ, s) : MvPolynomial _ ℝ)) (fun τ => ∑ a : Fin N, ∑ _b ∈ Finset.Ioi a, Finsupp.single (τ, a) 1) (fun τ _ => CoeffDelta …`. Establish `h2` using `key.2`.

Rewrite `h2` using `[MonomialOrder.leadingCoeff, key.1, rhoM_eq_sum]`. Conclude with `h2`.
-/
theorem coeff_rhoM_gapDelta (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) :
    coeff (rhoM Ψ N) (gapDelta Ψ N) = 1 := by
  let e := Fintype.equivFin Ψ
  letI : LinearOrder (Ψ × Fin N) :=
    LinearOrder.lift' (fun p => toLex (e p.1, p.2)) (fun p q h => by
      have h' : (e p.1, p.2) = (e q.1, q.2) := toLex.injective h
      obtain ⟨h1, h2⟩ := Prod.mk.inj h'
      exact Prod.ext (e.injective h1) h2)
  haveI : WellFoundedGT (Ψ × Fin N) := Finite.to_wellFoundedGT
  have hv : ∀ τ : Ψ, StrictMono (fun s : Fin N => (τ, s)) := fun τ s t hst => by
    show toLex (e τ, s) < toLex (e τ, t)
    exact Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, hst⟩)
  have key := CoeffDelta.degree_prod_monic (MonomialOrder.lex : MonomialOrder (Ψ × Fin N))
    Finset.univ
    (fun τ : Ψ => ∏ a : Fin N, ∏ b ∈ Finset.Ioi a, ∑ s ∈ Finset.Ico a b, (X (τ, s) : MvPolynomial _ ℝ))
    (fun τ => ∑ a : Fin N, ∑ _b ∈ Finset.Ioi a, Finsupp.single (τ, a) 1)
    (fun τ _ => CoeffDelta.degree_prod_monic _ Finset.univ _ _ fun a _ =>
      CoeffDelta.degree_prod_monic _ _ _ _ fun b hb =>
        CoeffDelta.lex_sum_Ico (fun s => (τ, s)) (hv τ) (Finset.mem_Ioi.mp hb))
  have h2 := key.2
  rw [MonomialOrder.leadingCoeff, key.1, rhoM_eq_sum] at h2
  exact h2

end GlobalTheory.CompanionTheory.Ar.Top.FlDeg
