import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvDer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffSubstEqZeroOfDegreeLt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffSubstRestrictSumVariables
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer
open TensorProduct

namespace GlobalTheory.PairingEv

/- English proof (translation)
Establish `hP : ∀ P : MvPolynomial σ R, (P : MvPowerSeries σ R) ∈ S` using `fun P => by`. Proceed by induction on `P using MvPolynomial.induction_on' with`. Consider the case `monomial γ a`. Rewrite using `[MvPolynomial.coe_monomial]`. Use `S.smul_mem a (h1 γ)` as an intermediate fact.

Rewrite `this` using `[← map_smul, smul_eq_mul, mul_one]`. Then use the resulting hypothesis. Consider the case `add P Q hP hQ => rw [MvPolynomial.coe_add]`. Conclude with `S.add_mem hP hQ`. Use `S.add_mem (hP (trunc' R (Finsupp.equivFunOnFinite.symm fun _ => N) H)) (h2 (H - (trunc' R (Finsupp.equivFunOnFinite.symm fun _ => N) H : MvPolynomial σ R)) ?_)` as an intermediate fact. Simplify using `using this`.

Introduce `α hα`. Rewrite using `[map_sub, MvPolynomial.coeff_coe, coeff_trunc', if_pos, sub_self]`. Introduce `j`. Conclude with `(Finsupp.le_degree j α).trans hα.le`.
-/
theorem mem_of_monomial_mem_of_tail_mem {σ R : Type} [CommRing R] [Fintype σ]
    (S : Submodule R (MvPowerSeries σ R)) (N : ℕ) (h1 : ∀ γ : σ →₀ ℕ, monomial γ (1 : R) ∈ S)
    (h2 : ∀ T : MvPowerSeries σ R, (∀ α : σ →₀ ℕ, α.degree < N → coeff α T = 0) → T ∈ S)
    (H : MvPowerSeries σ R) : H ∈ S := by
  classical
  have hP : ∀ P : MvPolynomial σ R, (P : MvPowerSeries σ R) ∈ S := fun P => by
    induction P using MvPolynomial.induction_on' with
    | monomial γ a =>
      rw [MvPolynomial.coe_monomial]
      have := S.smul_mem a (h1 γ)
      rwa [← map_smul, smul_eq_mul, mul_one] at this
    | add P Q hP hQ => rw [MvPolynomial.coe_add]; exact S.add_mem hP hQ
  have := S.add_mem (hP (trunc' R (Finsupp.equivFunOnFinite.symm fun _ => N) H))
    (h2 (H - (trunc' R (Finsupp.equivFunOnFinite.symm fun _ => N) H : MvPolynomial σ R)) ?_)
  · simpa using this
  · intro α hα
    rw [map_sub, MvPolynomial.coeff_coe, coeff_trunc', if_pos, sub_self]
    intro j
    exact (Finsupp.le_degree j α).trans hα.le

/- English proof (translation)
Rewrite using `[atZero, (coeff_subst_restrict_sum _).1, coeff_pderiv, Finsupp.mapDomain_of_notMem_range _ _ (by simp)]`. Simplify using the standard rewrite rules.
-/
theorem coeff_atZero_pderiv_inr {R : Type} [CommRing R] {d : ℕ}
    (H : MvPowerSeries (Fin d ⊕ Fin d) R) (i : Fin d) (α : Fin d →₀ ℕ) :
    coeff α (atZero (pderiv R (Sum.inr i) H)) =
      coeff (α.mapDomain Sum.inl + Finsupp.single (Sum.inr i) 1) H := by
  rw [atZero, (coeff_subst_restrict_sum _).1, coeff_pderiv,
    Finsupp.mapDomain_of_notMem_range _ _ (by simp)]
  simp

/- English proof (translation)
Use extensionality with `γ`. Rewrite using `[coeff_atZero_pderiv_inr, map_smul, lin, coeff_monomial, coeff_monomial, coeff_monomial]`. Establish `: γ.mapDomain Sum.inl + Finsupp.single (Sum.inr i) 1 = γ.sumElim (Finsupp.single i 1)`. Rewrite using `[Finsupp.sumElim_eq_add, Finsupp.mapDomain_single]`. Rewrite using `[this]`.

Establish `h2 : γ.sumElim (Finsupp.single i 1) = α.sumElim β ↔ γ = α ∧ Finsupp.single i 1 = β`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `⟨Finsupp.ext fun j => by simpa using DFunLike.congr_fun h (Sum.inl j), Finsupp.ext fun j => by simpa using DFunLike.congr_fun h (Sum.inr j)⟩`. Introduce and unpack `⟨rfl, rfl⟩`.

Both sides reduce to the same expression. Simplify using `only [h2]`. Apply the tactic sequence `by_cases h3 : γ = α <;> by_cases h4 : Finsupp.single i 1 = β <;> simp [h3, h4]`.
-/
theorem atZero_pderiv_inr_monomial {R : Type} [CommRing R] {d : ℕ} (α β : Fin d →₀ ℕ) (i : Fin d) :
    atZero (pderiv R (Sum.inr i) (monomial (α.sumElim β) (1 : R))) =
      lin (monomial β (1 : R)) i • monomial α (1 : R) := by
  classical
  ext γ
  rw [coeff_atZero_pderiv_inr, map_smul, lin, coeff_monomial, coeff_monomial, coeff_monomial]
  have : γ.mapDomain Sum.inl + Finsupp.single (Sum.inr i) 1 = γ.sumElim (Finsupp.single i 1) := by
    rw [Finsupp.sumElim_eq_add, Finsupp.mapDomain_single]
  rw [this]
  have h2 : γ.sumElim (Finsupp.single i 1) = α.sumElim β ↔ γ = α ∧ Finsupp.single i 1 = β := by
    constructor
    · intro h
      exact ⟨Finsupp.ext fun j => by simpa using DFunLike.congr_fun h (Sum.inl j),
        Finsupp.ext fun j => by simpa using DFunLike.congr_fun h (Sum.inr j)⟩
    · rintro ⟨rfl, rfl⟩; rfl
  simp only [h2]
  by_cases h3 : γ = α <;> by_cases h4 : Finsupp.single i 1 = β <;> simp [h3, h4]

/- English proof (translation)
Simplify using `only [monomial_one_eq]`. Rewrite using `[Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_sum_type]`. Simplify using `only [map_mul, map_prod, map_pow, (c.isEval n).1, (c.isEval₂ n).1, Sum.elim_inl, Sum.elim_inr, Finsupp.sumElim_inl, Finsupp.sumElim_inr]`. Establish `e1` using `map_prod (Algebra.TensorProduct.includeLeft : G.A n →ₐ[O] G.A n ⊗[O] G.A n) (fun j => c.x n j ^ α j) Finset.univ`. Establish `e2` using `map_prod (Algebra.TensorProduct.includeRight : G.A n →ₐ[O] G.A n ⊗[O] G.A n) (fun j => c.x n j ^ β j) Finset.univ`.

Simplify using `only [map_pow, Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply] at e1 e2`. Rewrite using `[← e1, ← e2, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]`.
-/
theorem chart_ev₂_monomial {p : ℕ} {O : Type} [CommRing O] {G : PDivGroup p O} {d : ℕ}
    (c : QLog.Chart G d) (n : ℕ) (α β : Fin d →₀ ℕ) :
    c.ev₂ n (monomial (α.sumElim β) 1) = c.ev n (monomial α 1) ⊗ₜ[O] c.ev n (monomial β 1) := by
  simp only [monomial_one_eq]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_sum_type]
  simp only [map_mul, map_prod, map_pow, (c.isEval n).1, (c.isEval₂ n).1, Sum.elim_inl,
    Sum.elim_inr, Finsupp.sumElim_inl, Finsupp.sumElim_inr]
  have e1 := map_prod (Algebra.TensorProduct.includeLeft : G.A n →ₐ[O] G.A n ⊗[O] G.A n)
    (fun j => c.x n j ^ α j) Finset.univ
  have e2 := map_prod (Algebra.TensorProduct.includeRight : G.A n →ₐ[O] G.A n ⊗[O] G.A n)
    (fun j => c.x n j ^ β j) Finset.univ
  simp only [map_pow, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply] at e1 e2
  rw [← e1, ← e2, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/- English proof (translation)
Introduce `p O _ G d c n m hp u φ hφ ψ H`. Take `⟨N₁, h₁⟩` from `(c.isEval n).2 1`. Take `⟨N₂, h₂⟩` from `(c.isEval₂ n).2 1`. Apply the tactic sequence `have hs : HasSubst (Sum.elim (fun i => (X i : MvPowerSeries (Fin d) O)) (fun _ : Fin d => 0)) := hasSubst_of_constantCoeff_zero (by rintro (j | j) <;> simp)`. Set `D : MvPowerSeries (Fin d ⊕ Fin d) O →ₗ[O] MvPowerSeries (Fin d) O` to `∑ i, u i • ((substAlgHom hs).toLinearMap ∘ₗ (pderiv O (Sum.inr i)).toLinearMap)`.

Establish `hD : ∀ H, D H = ∑ i, u i • atZero (pderiv O (Sum.inr i) H)` using `fun H => by`. Simplify using `[D, atZero, LinearMap.sum_apply, coe_substAlgHom]`. Set `P : G.A n ⊗[O] G.A n →ₗ[O] O` to `LinearMap.mul' O O ∘ₗ TensorProduct.map ψ φ.ofConv`. Set `L : MvPowerSeries (Fin d ⊕ Fin d) O →ₗ[O] O` to `P ∘ₗ (c.ev₂ n).toLinearMap - ψ ∘ₗ (c.ev n).toLinearMap ∘ₗ D`. Establish `hL : ∀ H, L H = P (c.ev₂ n H) - ψ (c.ev n (∑ i, u i • atZero (pderiv O (Sum.inr i) H)))` using `fun H => by rw [← hD]; rfl`.

Establish `key` using `mem_of_monomial_mem_of_tail_mem (Submodule.comap L m) (N₁ + N₂ + 1) ?_ ?_ H`. Rewrite `key` using `[Submodule.mem_comap, hL]`. Conclude with `key`. Introduce `γ`. Rewrite using `[Submodule.mem_comap, hL, ← Finsupp.comapDomain_sumElim_comapDomain γ]`.

Generalize the expression as in `Finsupp.comapDomain Sum.inl γ _ = α`. Generalize the expression as in `Finsupp.comapDomain Sum.inr γ _ = β`. Rewrite using `[chart_ev₂_monomial]`. Simplify using `only [atZero_pderiv_inr_monomial, smul_smul, ← Finset.sum_smul, map_smul, smul_eq_mul]`. Use `m.mul_mem_left (ψ (c.ev n (monomial α 1))) (hφ (monomial β 1))` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Establish `e : P (c.ev n (monomial α 1) ⊗ₜ[O] c.ev n (monomial β 1)) = ψ (c.ev n (monomial α 1)) * φ (c.ev n (monomial β 1))`. Simplify using `only [P, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.mul'_apply]`. Rewrite using `[e]`. Expand and normalize the polynomial expressions, which then agree.

Introduce `T hT`. Rewrite using `[Submodule.mem_comap, hL]`. Take `⟨a, ha⟩` from `h₂ T fun α hα => hT α (by omega)`. Take `⟨b, hb⟩` from `h₁ (∑ i, u i • atZero (pderiv O (Sum.inr i) T)) fun α hα => by`. Rewrite using `[map_sum]`.

Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, coeff_atZero_pderiv_inr, hT, smul_zero]`. Rewrite using `[map_add, Finsupp.degree_mapDomain, Finsupp.degree_single]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[ha, hb, pow_one, pow_one, ← nsmul_eq_mul, ← nsmul_eq_mul, map_nsmul, map_nsmul, nsmul_eq_mul, nsmul_eq_mul]`.

Conclude with `m.sub_mem (m.mul_mem_right _ hp) (m.mul_mem_right _ hp)`.
-/
theorem pairing_ev₂_sub_mem : ∀ (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (n : ℕ) (m : Ideal O), (p : O) ∈ m → ∀ (u : Fin d → O) (φ : G.dual.A n), (∀ F, φ (c.ev n F) - ∑ i, u i * lin F i ∈ m) → ∀ (ψ : G.A n →ₗ[O] O) (H : MvPowerSeries (Fin d ⊕ Fin d) O), LinearMap.mul' O O (TensorProduct.map ψ φ.ofConv (c.ev₂ n H)) - ψ (c.ev n (∑ i, u i • atZero (pderiv O (Sum.inr i) H))) ∈ m := by
  intro p O _ G d c n m hp u φ hφ ψ H
  obtain ⟨N₁, h₁⟩ := (c.isEval n).2 1
  obtain ⟨N₂, h₂⟩ := (c.isEval₂ n).2 1
  have hs : HasSubst (Sum.elim (fun i => (X i : MvPowerSeries (Fin d) O)) (fun _ : Fin d => 0)) :=
    hasSubst_of_constantCoeff_zero (by rintro (j | j) <;> simp)
  let D : MvPowerSeries (Fin d ⊕ Fin d) O →ₗ[O] MvPowerSeries (Fin d) O :=
    ∑ i, u i • ((substAlgHom hs).toLinearMap ∘ₗ (pderiv O (Sum.inr i)).toLinearMap)
  have hD : ∀ H, D H = ∑ i, u i • atZero (pderiv O (Sum.inr i) H) := fun H => by
    simp [D, atZero, LinearMap.sum_apply, coe_substAlgHom]
  let P : G.A n ⊗[O] G.A n →ₗ[O] O := LinearMap.mul' O O ∘ₗ TensorProduct.map ψ φ.ofConv
  let L : MvPowerSeries (Fin d ⊕ Fin d) O →ₗ[O] O :=
    P ∘ₗ (c.ev₂ n).toLinearMap - ψ ∘ₗ (c.ev n).toLinearMap ∘ₗ D
  have hL : ∀ H, L H = P (c.ev₂ n H) - ψ (c.ev n (∑ i, u i • atZero (pderiv O (Sum.inr i) H))) :=
    fun H => by rw [← hD]; rfl
  have key := mem_of_monomial_mem_of_tail_mem (Submodule.comap L m) (N₁ + N₂ + 1) ?_ ?_ H
  · rw [Submodule.mem_comap, hL] at key
    exact key
  · intro γ
    rw [Submodule.mem_comap, hL, ← Finsupp.comapDomain_sumElim_comapDomain γ]
    generalize Finsupp.comapDomain Sum.inl γ _ = α
    generalize Finsupp.comapDomain Sum.inr γ _ = β
    rw [chart_ev₂_monomial]
    simp only [atZero_pderiv_inr_monomial, smul_smul, ← Finset.sum_smul, map_smul, smul_eq_mul]
    have := m.mul_mem_left (ψ (c.ev n (monomial α 1))) (hφ (monomial β 1))
    convert this using 1
    have e : P (c.ev n (monomial α 1) ⊗ₜ[O] c.ev n (monomial β 1)) =
        ψ (c.ev n (monomial α 1)) * φ (c.ev n (monomial β 1)) := by
      simp only [P, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.mul'_apply]
    rw [e]; ring
  · intro T hT
    rw [Submodule.mem_comap, hL]
    obtain ⟨a, ha⟩ := h₂ T fun α hα => hT α (by omega)
    obtain ⟨b, hb⟩ := h₁ (∑ i, u i • atZero (pderiv O (Sum.inr i) T)) fun α hα => by
      rw [map_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [map_smul, coeff_atZero_pderiv_inr, hT, smul_zero]
      rw [map_add, Finsupp.degree_mapDomain, Finsupp.degree_single]
      omega
    rw [ha, hb, pow_one, pow_one, ← nsmul_eq_mul, ← nsmul_eq_mul, map_nsmul, map_nsmul,
      nsmul_eq_mul, nsmul_eq_mul]
    exact m.sub_mem (m.mul_mem_right _ hp) (m.mul_mem_right _ hp)

end GlobalTheory.PairingEv
