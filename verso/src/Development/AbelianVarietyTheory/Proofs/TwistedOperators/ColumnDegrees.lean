import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ISupEigenspaceEqTop
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumRowDegreeEqOfHarmonicHighestCasimirStatement

noncomputable section

open MvPolynomial GlobalTheory.Capelli Formalism.BasicNotions.TH GlobalTheory.JointHarm

namespace GlobalTheory.JointHarm.ColumnDegree

/- English proof (translation)
Establish `hQN : Q.totalDegree ≤ N` using `by rwa [mem_restrictTotalDegree] at hQ`. Establish `hadd : ∀ a b : σ →₀ ℕ, ((a + b).sum fun _ e => e) = (a.sum fun _ e => e) + (b.sum fun _ e => e)` using `fun a b => Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)`. Establish `hone : ∀ w : σ, ((Finsupp.single w 1).sum fun _ e => e) = 1` using `fun w => Finsupp.sum_single_index rfl`. Establish `key : ∀ s ∈ Q.support, X u * pderiv v (monomial s (coeff s Q)) ∈ restrictTotalDegree σ ℂ N`. Introduce `s hs`.

Establish `hsN : (s.sum fun _ e => e) ≤ N` using `(le_totalDegree hs).trans hQN`. Rewrite using `[pderiv_monomial]`. Distinguish the cases in `hv : s v = 0`. Rewrite using `[hv]`. Simplify using the standard rewrite rules.

Establish `hle : Finsupp.single v 1 ≤ s` using `Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hv)`. Rewrite using `[mem_restrictTotalDegree, X, monomial_mul, one_mul]`. Use `(totalDegree_monomial_le _ _).trans ?_` and prove the remaining obligations. Establish `e1 : s = (s - Finsupp.single v 1) + Finsupp.single v 1` using `(tsub_add_cancel_of_le hle).symm`. Establish `h1` using `hadd (s - Finsupp.single v 1) (Finsupp.single v 1)`.

Rewrite `h1` using `[← e1, hone]`. Establish `h2` using `hadd (Finsupp.single u 1) (s - Finsupp.single v 1)`. Rewrite `h2` using `[hone]`. Express the relevant statement in the definitionally equal form `((Finsupp.single u 1 + (s - Finsupp.single v 1)).sum fun _ e => e) ≤ N`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[polar_apply, Q.as_sum, map_sum, Finset.mul_sum]`. Conclude with `Submodule.sum_mem _ key`.
-/
theorem polar_mem {σ : Type} (u v : σ) (N : ℕ) (Q : MvPolynomial σ ℂ)
    (hQ : Q ∈ restrictTotalDegree σ ℂ N) : polar ℂ u v Q ∈ restrictTotalDegree σ ℂ N := by
  classical
  have hQN : Q.totalDegree ≤ N := by rwa [mem_restrictTotalDegree] at hQ
  have hadd : ∀ a b : σ →₀ ℕ, ((a + b).sum fun _ e => e) = (a.sum fun _ e => e) + (b.sum fun _ e => e) :=
    fun a b => Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)
  have hone : ∀ w : σ, ((Finsupp.single w 1).sum fun _ e => e) = 1 :=
    fun w => Finsupp.sum_single_index rfl
  have key : ∀ s ∈ Q.support,
      X u * pderiv v (monomial s (coeff s Q)) ∈ restrictTotalDegree σ ℂ N := by
    intro s hs
    have hsN : (s.sum fun _ e => e) ≤ N := (le_totalDegree hs).trans hQN
    rw [pderiv_monomial]
    by_cases hv : s v = 0
    · rw [hv]; simp
    · have hle : Finsupp.single v 1 ≤ s := Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hv)
      rw [mem_restrictTotalDegree, X, monomial_mul, one_mul]
      refine (totalDegree_monomial_le _ _).trans ?_
      have e1 : s = (s - Finsupp.single v 1) + Finsupp.single v 1 := (tsub_add_cancel_of_le hle).symm
      have h1 := hadd (s - Finsupp.single v 1) (Finsupp.single v 1)
      rw [← e1, hone] at h1
      have h2 := hadd (Finsupp.single u 1) (s - Finsupp.single v 1)
      rw [hone] at h2
      change ((Finsupp.single u 1 + (s - Finsupp.single v 1)).sum fun _ e => e) ≤ N
      omega
  rw [polar_apply, Q.as_sum, map_sum, Finset.mul_sum]
  exact Submodule.sum_mem _ key

/- English proof (translation)
Rewrite using `[colOp_apply]`. Conclude with `Submodule.sum_mem _ fun i _ => by`. Simplify `polar_mem (z (i, a)) (z (i, b)) N Q hQ` using `only [polar_apply]`.
-/
theorem colOp_mem {σ I J : Type} [Fintype I] (z : I × J → σ) (a b : J) (N : ℕ)
    (Q : MvPolynomial σ ℂ) (hQ : Q ∈ restrictTotalDegree σ ℂ N) :
    colOp ℂ z a b Q ∈ restrictTotalDegree σ ℂ N := by
  rw [colOp_apply]
  exact Submodule.sum_mem _ fun i _ => by
    simpa only [polar_apply] using polar_mem (z (i, a)) (z (i, b)) N Q hQ

/- English proof (translation)
Rewrite using `[rowOp_apply]`. Conclude with `Submodule.sum_mem _ fun t _ => by`. Simplify `polar_mem (z (a, t)) (z (b, t)) N Q hQ` using `only [polar_apply]`.
-/
theorem rowOp_mem {σ I J : Type} [Fintype J] (z : I × J → σ) (a b : I) (N : ℕ)
    (Q : MvPolynomial σ ℂ) (hQ : Q ∈ restrictTotalDegree σ ℂ N) :
    rowOp ℂ z a b Q ∈ restrictTotalDegree σ ℂ N := by
  rw [rowOp_apply]
  exact Submodule.sum_mem _ fun t _ => by
    simpa only [polar_apply] using polar_mem (z (a, t)) (z (b, t)) N Q hQ

/- English proof (translation)
Establish `hexp : ∀ t k, pderiv (z (i, t)) (pderiv (y (j, t)) (X (z (a, k)) * pderiv (z (b, k)) Q)) = X (z (a, k)) * pderiv (z (i, t)) (pderiv (y (j, t)) (pderiv (z (b, k)) Q)) + (if i = a ∧ t = k then pderiv (y (j, t)) (pderiv (z (b, k)) Q) else 0)`. Introduce `t k`. Rewrite using `[pderiv_X_mul', if_neg (fun h => hzy _ _ h.symm), add_zero, pderiv_X_mul']`. Use `congr 1`. Simplify using `only [hz.eq_iff, Prod.mk.injEq]`.

Establish `hA : ∑ t, ∑ k, X (z (a, k)) * pderiv (z (i, t)) (pderiv (y (j, t)) (pderiv (z (b, k)) Q)) = 0`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.mul_sum]`. Establish `hsw : ∀ t, pderiv (z (i, t)) (pderiv (y (j, t)) (pderiv (z (b, k)) Q)) = pderiv (z (b, k)) (pderiv (z (i, t)) (pderiv (y (j, t)) Q))`.

Introduce `t`. Rewrite using `[pderiv_swap (y (j, t)) (z (b, k)), pderiv_swap (z (i, t)) (z (b, k))]`. Simplify using `only [hsw]`. Rewrite using `[← map_sum, hQ i j, map_zero, mul_zero]`. Establish `hB : ∑ t, ∑ k, (if i = a ∧ t = k then pderiv (y (j, t)) (pderiv (z (b, k)) Q) else 0) = 0`.

Distinguish the cases in `hia : i = a`. Simplify using `only [hia, true_and, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Rewrite using `[← hQ b j]`. Conclude with `Finset.sum_congr rfl fun t _ => pderiv_swap _ _ _`. Simplify using `[hia]`.

Rewrite using `[rowOp_apply]`. Simplify using `only [map_sum, hexp, Finset.sum_add_distrib, hA, hB, add_zero]`.
-/
theorem harmonic_rowOp {σ I I' J : Type} [Fintype J] (z : I × J → σ) (y : I' × J → σ)
    (hz : Function.Injective z) (hzy : ∀ u w, z u ≠ y w) (Q : MvPolynomial σ ℂ)
    (hQ : ∀ i j, ∑ t, pderiv (z (i, t)) (pderiv (y (j, t)) Q) = 0) (a b : I) (i : I) (j : I') :
    ∑ t, pderiv (z (i, t)) (pderiv (y (j, t)) (rowOp ℂ z a b Q)) = 0 := by
  classical
  have hexp : ∀ t k, pderiv (z (i, t)) (pderiv (y (j, t)) (X (z (a, k)) * pderiv (z (b, k)) Q)) =
      X (z (a, k)) * pderiv (z (i, t)) (pderiv (y (j, t)) (pderiv (z (b, k)) Q)) +
        (if i = a ∧ t = k then pderiv (y (j, t)) (pderiv (z (b, k)) Q) else 0) := by
    intro t k
    rw [pderiv_X_mul', if_neg (fun h => hzy _ _ h.symm), add_zero, pderiv_X_mul']
    congr 1
    simp only [hz.eq_iff, Prod.mk.injEq]
  have hA : ∑ t, ∑ k, X (z (a, k)) * pderiv (z (i, t)) (pderiv (y (j, t)) (pderiv (z (b, k)) Q))
      = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [← Finset.mul_sum]
    have hsw : ∀ t, pderiv (z (i, t)) (pderiv (y (j, t)) (pderiv (z (b, k)) Q)) =
        pderiv (z (b, k)) (pderiv (z (i, t)) (pderiv (y (j, t)) Q)) := by
      intro t
      rw [pderiv_swap (y (j, t)) (z (b, k)), pderiv_swap (z (i, t)) (z (b, k))]
    simp only [hsw]
    rw [← map_sum, hQ i j, map_zero, mul_zero]
  have hB : ∑ t, ∑ k, (if i = a ∧ t = k then pderiv (y (j, t)) (pderiv (z (b, k)) Q) else 0)
      = 0 := by
    by_cases hia : i = a
    · simp only [hia, true_and, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [← hQ b j]
      exact Finset.sum_congr rfl fun t _ => pderiv_swap _ _ _
    · simp [hia]
  rw [rowOp_apply]
  simp only [map_sum, hexp, Finset.sum_add_distrib, hA, hB, add_zero]

/- English proof (translation)
Proceed by induction on `Q using MvPolynomial.induction_on' with`. Consider the case `monomial u c`. Establish `hc : (monomial u c : MvPolynomial σ ℂ) = c • monomial u 1`. Rewrite using `[smul_monomial, smul_eq_mul, mul_one]`. Rewrite using `[hc, map_smul, hg, smul_smul]`.

Simplify using `only [coeff_smul, coeff_monomial, smul_eq_mul]`. Use `split_ifs with h`. Substitute `h` using the available equality. Expand and normalize the polynomial expressions, which then agree. Expand and normalize the polynomial expressions, which then agree.

Consider the case `add p q hp hq => rw [map_add, coeff_add, coeff_add, hp, hq, mul_add]`.
-/
private theorem coeff_apply_of_diagonal_on_monomials' {σ : Type} (g : Module.End ℂ (MvPolynomial σ ℂ))
    (w : (σ →₀ ℕ) → ℂ) (hg : ∀ u, g (monomial u 1) = w u • monomial u 1) (m : σ →₀ ℕ)
    (Q : MvPolynomial σ ℂ) : coeff m (g Q) = w m * coeff m Q := by
  classical
  induction Q using MvPolynomial.induction_on' with
  | monomial u c =>
    have hc : (monomial u c : MvPolynomial σ ℂ) = c • monomial u 1 := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [hc, map_smul, hg, smul_smul]
    simp only [coeff_smul, coeff_monomial, smul_eq_mul]
    split_ifs with h
    · subst h; ring
    · ring
  | add p q hp hq => rw [map_add, coeff_add, coeff_add, hp, hq, mul_add]

/- English proof (translation)
Use `coeff_apply_of_diagonal_on_monomials' _ (fun u => ((∑ i, ∑ t, (u (z (i, t)) : ℤ) : ℤ) : ℂ)) (fun u => ?_) m Q` and prove the remaining obligations. Rewrite using `[LinearMap.sum_apply]`. Simplify using `only [rowOp_monomial]`. Rewrite using `[← Finset.sum_smul]`. Use `push_cast`.

Both sides reduce to the same expression.
-/
theorem coeff_euler {σ : Type} {k n : ℕ} (z : Fin k × Fin n → σ) (m : σ →₀ ℕ)
    (Q : MvPolynomial σ ℂ) :
    coeff m ((∑ i, rowOp ℂ z i i) Q) = ((∑ i, ∑ t, (m (z (i, t)) : ℤ) : ℤ) : ℂ) * coeff m Q := by
  refine coeff_apply_of_diagonal_on_monomials' _ (fun u => ((∑ i, ∑ t, (u (z (i, t)) : ℤ) : ℤ) : ℂ)) (fun u => ?_) m Q
  rw [LinearMap.sum_apply]
  simp only [rowOp_monomial]
  rw [← Finset.sum_smul]
  push_cast
  rfl

/- English proof (translation)
Use `show (∑ i, rowOp ℂ z i i) * rowOp ℂ z a b = rowOp ℂ z a b * ∑ i, rowOp ℂ z i i`. Rewrite using `[← sub_eq_zero, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]`. Simplify using `only [rowOp_lie z hz, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, sub_self]`.
-/
theorem commute_euler {σ : Type} {k n : ℕ} (z : Fin k × Fin n → σ) (hz : Function.Injective z)
    (a b : Fin k) : Commute (∑ i, rowOp ℂ z i i) (rowOp ℂ z a b) := by
  show (∑ i, rowOp ℂ z i i) * rowOp ℂ z a b = rowOp ℂ z a b * ∑ i, rowOp ℂ z i i
  rw [← sub_eq_zero, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  simp only [rowOp_lie z hz, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, sub_self]

/- English proof (translation)
Establish `hne : v.support.Nonempty`. Rewrite using `[Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]`. Conclude with `hv`. Take `⟨m, hm⟩` from `hne`. Use `⟨fun i => ∑ t, m (z (i, t)), fun i => ?_⟩` and prove the remaining obligations.

Establish `h` using `(rowOp_eq_smul_iff z i v (a i : ℂ)).1 (ha i) m hm`. Conclude with `h` after adjusting the coercions.
-/
theorem weight_nat {σ : Type} {k n : ℕ} (z : Fin k × Fin n → σ) (v : MvPolynomial σ ℂ)
    (hv : v ≠ 0) (a : Fin k → ℤ) (ha : ∀ i, rowOp ℂ z i i v = (a i : ℂ) • v) :
    ∃ a' : Fin k → ℕ, ∀ i, (a' i : ℤ) = a i := by
  classical
  have hne : v.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]
    exact hv
  obtain ⟨m, hm⟩ := hne
  refine ⟨fun i => ∑ t, m (z (i, t)), fun i => ?_⟩
  have h := (rowOp_eq_smul_iff z i v (a i : ℂ)).1 (ha i) m hm
  exact_mod_cast h

/- English proof (translation)
Establish `hPV : P ∈ restrictTotalDegree σ ℂ P.totalDegree` using `by rw [mem_restrictTotalDegree]`. Establish `hmixV : ∀ i j, ∀ Q ∈ restrictTotalDegree σ ℂ P.totalDegree, mixedOp ℂ z y i j Q ∈ restrictTotalDegree σ ℂ P.totalDegree`. Introduce `i j Q hQ`. Rewrite using `[mixedOp_apply, ← colOp_apply (K := ℂ) z i j Q, ← colOp_apply (K := ℂ) y j i Q]`. Conclude with `Submodule.sub_mem _ (colOp_mem z i j _ Q hQ) (colOp_mem y j i _ Q hQ)`.

Establish `hκ : Antitone κ` using `highest_weight_antitone (mixedOp ℂ z y) (mixedOp_lie z hz y hy hzy) (restrictTotalDegree σ ℂ P.totalDegree) hmixV P hPV hP0 κ hup hwt`. Take `⟨W, hW⟩ : ∃ W : Submodule ℂ (MvPolynomial σ ℂ), ∀ Q, Q ∈ W ↔ (Q ∈ restrictTotalDegree σ ℂ P.totalDegree ∧ (∀ i j, ∑ t, pderiv (z (i, t)) (pderiv (y (j, t)) Q) = 0) ∧ (∀ i j, i < j → mixedOp ℂ z y i j Q = 0) ∧ ∀ t, mixedOp ℂ z y t t Q = (κ t : ℂ) • Q)` from `⟨{ carrier := {Q | Q ∈ restrictTotalDegree σ ℂ P.totalDegree ∧ (∀ i j, ∑ t, pderiv (z (i, t)) (pderiv (y (j, t)) Q) = 0) ∧ (∀ i j, i < j → mixedOp ℂ z y i j Q = 0) ∧ ∀ t, mixedOp ℂ z y t t Q = (κ t : ℂ) • Q} add_mem' := by`. Introduce and unpack `Q R ⟨h1, h2, h3, h4⟩ ⟨g1, g2, g3, g4⟩`. Use `⟨Submodule.add_mem _ h1 g1, fun i j => ?_, fun i j hij => ?_, fun t => ?_⟩` and prove the remaining obligations. Simplify using `only [map_add, Finset.sum_add_distrib, h2 i j, g2 i j, add_zero]`.

Rewrite using `[map_add, h3 i j hij, g3 i j hij, add_zero]`. Rewrite using `[map_add, h4 t, g4 t, smul_add]`. Use the proof step `zero_mem' := ⟨Submodule.zero_mem _, fun i j => by simp, fun i j _ => map_zero _, fun t => by simp⟩`. Use the proof step `smul_mem' := by`. Introduce and unpack `c Q ⟨h1, h2, h3, h4⟩`.

Use `⟨Submodule.smul_mem _ c h1, fun i j => ?_, fun i j hij => ?_, fun t => ?_⟩` and prove the remaining obligations. Simplify using `only [Derivation.map_smul, ← Finset.smul_sum, h2 i j, smul_zero]`. Rewrite using `[map_smul, h3 i j hij, smul_zero]`. Rewrite using `[map_smul, h4 t, smul_comm] }, fun Q => Iff.rfl⟩`. Establish `hPW : P ∈ W` using `(hW P).2 ⟨hPV, hharm, hup, hwt⟩`.

Establish `hWz : ∀ a b, ∀ Q ∈ W, rowOp ℂ z a b Q ∈ W`. Introduce `a b Q hQ`. Take `⟨h1, h2, h3, h4⟩` from `(hW Q).1 hQ`. Use `(hW _).2 ⟨rowOp_mem z a b _ Q h1, fun i j => harmonic_rowOp z y hz hzy Q h2 a b i j, fun i j hij => ?_, fun t => ?_⟩` and prove the remaining obligations. Rewrite using `[← Module.End.mul_apply, ← (commute_rowOp_left_mixedOp z hz y hzy a b i j).eq, Module.End.mul_apply, h3 i j hij, map_zero]`.

Rewrite using `[← Module.End.mul_apply, ← (commute_rowOp_left_mixedOp z hz y hzy a b t t).eq, Module.End.mul_apply, h4 t, map_smul]`. Establish `hWy : ∀ a b, ∀ Q ∈ W, rowOp ℂ y a b Q ∈ W`. Introduce `a b Q hQ`. Take `⟨h1, h2, h3, h4⟩` from `(hW Q).1 hQ`. Establish `h2' : ∀ i j, ∑ t, pderiv (y (i, t)) (pderiv (z (j, t)) Q) = 0`.

Introduce `i j`. Rewrite using `[← h2 j i]`. Conclude with `Finset.sum_congr rfl fun t _ => pderiv_swap _ _ _`. Use `(hW _).2 ⟨rowOp_mem y a b _ Q h1, fun i j => ?_, fun i j hij => ?_, fun t => ?_⟩` and prove the remaining obligations. Rewrite using `[← harmonic_rowOp y z hy (fun u w h => hzy w u h.symm) Q h2' a b j i]`.

Conclude with `Finset.sum_congr rfl fun t _ => pderiv_swap _ _ _`. Rewrite using `[← Module.End.mul_apply, ← (commute_rowOp_right_mixedOp z y hy hzy a b i j).eq, Module.End.mul_apply, h3 i j hij, map_zero]`. Rewrite using `[← Module.End.mul_apply, ← (commute_rowOp_right_mixedOp z y hy hzy a b t t).eq, Module.End.mul_apply, h4 t, map_smul]`. Take `⟨E, hE⟩ : ∃ E : Module.End ℂ (MvPolynomial σ ℂ), E = ∑ i, rowOp ℂ z i i` from `⟨_, rfl⟩`. Take `⟨zdeg, hzdeg⟩ : ∃ f : (σ →₀ ℕ) → ℤ, ∀ m, f m = ∑ i, ∑ t, (m (z (i, t)) : ℤ)` from `⟨_, fun _ => rfl⟩`.

Establish `hcoeffE : ∀ m Q, coeff m (E Q) = (zdeg m : ℂ) * coeff m Q`. Introduce `m Q`. Rewrite using `[hE, hzdeg]`. Conclude with `coeff_euler z m Q`. Establish `hWE : ∀ Q ∈ W, E Q ∈ W`.

Introduce `Q hQ`. Rewrite using `[hE, LinearMap.sum_apply]`. Conclude with `Submodule.sum_mem _ fun i _ => hWz i i Q hQ`. Establish `hkey : ∀ Q ∈ W, Q ≠ 0 → ∀ μ : ℂ, E Q = μ • Q → μ = ((∑ t, max (κ t) 0 : ℤ) : ℂ)`. Introduce `Q hQW hQ0 μ hμ`.

Take `⟨W', hW'⟩ : ∃ W' : Submodule ℂ (MvPolynomial σ ℂ), ∀ R, R ∈ W' ↔ (R ∈ W ∧ E R = μ • R)` from `⟨{ carrier := {R | R ∈ W ∧ E R = μ • R} add_mem' := by`. Introduce and unpack `R R' ⟨h1, h2⟩ ⟨g1, g2⟩`. Conclude with `⟨W.add_mem h1 g1, by rw [map_add, h2, g2, smul_add]⟩`. Use the proof step `zero_mem' := ⟨W.zero_mem, by simp⟩`. Use the proof step `smul_mem' := by`.

Introduce and unpack `c R ⟨h1, h2⟩`. Conclude with `⟨W.smul_mem c h1, by rw [map_smul, h2, smul_comm]⟩ }, fun R => Iff.rfl⟩`. Establish `hW'V : W' ≤ restrictTotalDegree σ ℂ P.totalDegree` using `fun R hR => ((hW R).1 ((hW' R).1 hR).1).1`. Establish `: FiniteDimensional ℂ W'` using `Submodule.finiteDimensional_of_le hW'V`. Establish `hEz : ∀ a b, Commute E (rowOp ℂ z a b)`.

Introduce `a b`. Rewrite using `[hE]`. Conclude with `commute_euler z hz a b`. Establish `hEy : ∀ a b, Commute E (rowOp ℂ y a b)`. Introduce `a b`.

Rewrite using `[hE]`. Conclude with `Commute.sum_left _ _ _ fun i _ => commute_rowOp_rowOp z y hzy i i a b`. Establish `hW'z : ∀ a b, ∀ R ∈ W', rowOp ℂ z a b R ∈ W'`. Introduce `a b R hR`. Take `⟨h1, h2⟩` from `(hW' R).1 hR`.

Use `(hW' _).2 ⟨hWz a b R h1, ?_⟩` and prove the remaining obligations. Rewrite using `[← Module.End.mul_apply, (hEz a b).eq, Module.End.mul_apply, h2, map_smul]`. Establish `hW'y : ∀ a b, ∀ R ∈ W', rowOp ℂ y a b R ∈ W'`. Introduce `a b R hR`. Take `⟨h1, h2⟩` from `(hW' R).1 hR`.

Use `(hW' _).2 ⟨hWy a b R h1, ?_⟩` and prove the remaining obligations. Rewrite using `[← Module.End.mul_apply, (hEy a b).eq, Module.End.mul_apply, h2, map_smul]`. Establish `hQW' : Q ∈ W'` using `(hW' Q).2 ⟨hQW, hμ⟩`. Establish `hW'0 : W' ≠ ⊥`. Introduce `h`.

Rewrite `hQW'` using `[h]`. Conclude with `hQ0 ((Submodule.mem_bot ℂ).1 hQW')`. Take `⟨v, hvW, hv0, hvz, hvy, a, b, ha, hb⟩` from `exists_highest_pair (rowOp ℂ z) (rowOp ℂ y) (rowOp_lie z hz) (rowOp_lie y hy) (commute_rowOp_rowOp z y hzy) (iSup_eigenspace_eq_top (fun i => rowOp ℂ z i i) (fun m i => ∑ t, (m (z (i, t)) : ℤ)) (fun m i => rowOp_monomial z i m)) (iSup_eigenspace_eq_top (fun i => rowOp ℂ y i i) (f …`. Take `⟨hvW1, hvE⟩` from `(hW' v).1 hvW`. Take `⟨-, hvH, hvU, hvK⟩` from `(hW v).1 hvW1`.

Take `⟨a', ha'⟩` from `weight_nat z v hv0 a ha`. Take `⟨b', hb'⟩` from `weight_nat y v hv0 b hb`. Establish `haa : Antitone a` using `highest_weight_antitone (rowOp ℂ z) (rowOp_lie z hz) W' hW'z v hvW hv0 a hvz ha`. Establish `hbb : Antitone b` using `highest_weight_antitone (rowOp ℂ y) (rowOp_lie y hy) W' hW'y v hvW hv0 b hvy hb`. Establish `ha'a : Antitone a'` using `fun i j hij => by`.

Establish `h` using `haa hij`. Rewrite `h` using `[← ha' i, ← ha' j]`. Conclude with `h` after adjusting the coercions. Establish `hb'b : Antitone b'` using `fun i j hij => by`. Establish `h` using `hbb hij`.

Rewrite `h` using `[← hb' i, ← hb' j]`. Conclude with `h` after adjusting the coercions. Establish `hza : ∀ i, rowOp ℂ z i i v = (a' i : ℂ) • v` using `fun i => by`. Rewrite using `[ha i, ← ha' i, Int.cast_natCast]`. Establish `hyb : ∀ i, rowOp ℂ y i i v = (b' i : ℂ) • v` using `fun i => by`.

Rewrite using `[hb i, ← hb' i, Int.cast_natCast]`. Establish `hT` using `GlobalTheory.T.sum_row_degree_eq_of_harmonic_highest_casimir σ k l n z y hz hy hzy v a' b' κ hv0 ha'a hb'b hκ hvz hza hvy hyb hvH hvU hvK`. Establish `hEv : E v = ((∑ i, (a' i : ℤ) : ℤ) : ℂ) • v`. Rewrite using `[hE, LinearMap.sum_apply]`. Simplify using `only [hza]`.

Rewrite using `[← Finset.sum_smul]`. Use `push_cast`. Both sides reduce to the same expression. Establish `hzero : (μ - ((∑ i, (a' i : ℤ) : ℤ) : ℂ)) • v = 0`. Rewrite using `[sub_smul, ← hvE, hEv, sub_self]`.

Break down `smul_eq_zero.1 hzero with h | h` into its components or cases. Rewrite using `[← hT]`. Conclude with `sub_eq_zero.1 h`. Conclude with `absurd h hv0`. Establish `hdeg : ∀ m ∈ P.support, zdeg m = ∑ t, max (κ t) 0`.

Introduce `m0 hm0`. Assume the negation of the conclusion as `hne`. Establish `hiter : ∀ s : Finset ℤ, ∃ Q ∈ W, ∀ m, coeff m Q = (∏ D ∈ s, ((zdeg m : ℂ) - (D : ℂ))) * coeff m P`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`.

Consider the case `empty => exact ⟨P, hPW, fun m => by simp⟩`. Consider the case `insert D s hD ih`. Take `⟨Q, hQW, hQ⟩` from `ih`. Use `⟨E Q - (D : ℂ) • Q, W.sub_mem (hWE Q hQW) (W.smul_mem _ hQW), fun m => ?_⟩` and prove the remaining obligations. Rewrite using `[coeff_sub, coeff_smul, hcoeffE, hQ, Finset.prod_insert hD, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Take `⟨Q, hQW, hQ⟩` from `hiter ((P.support.image zdeg).erase (zdeg m0))`. Establish `hQm0 : coeff m0 Q ≠ 0`. Rewrite using `[hQ]`. Use `mul_ne_zero (Finset.prod_ne_zero_iff.2 fun D hD => sub_ne_zero.2 ?_) (mem_support_iff.1 hm0)` and prove the remaining obligations.

Introduce `h`. Conclude with `(Finset.mem_erase.1 hD).1 (by exact_mod_cast h.symm)`. Establish `hQ0 : Q ≠ 0` using `fun h => hQm0 (by rw [h, coeff_zero])`. Establish `hEQ : E Q = (zdeg m0 : ℂ) • Q`. Use extensionality with `m`.

Rewrite using `[hcoeffE, coeff_smul, smul_eq_mul]`. Distinguish the cases in `hm : coeff m Q = 0`. Rewrite using `[hm, mul_zero, mul_zero]`. Establish `hmP : m ∈ P.support`. Rewrite using `[mem_support_iff]`.

Introduce `h`. Apply `hm` to reduce the goal to its premises. Rewrite using `[hQ, h, mul_zero]`. Establish `hmm : zdeg m = zdeg m0`. Assume the negation of the conclusion as `hne'`.

Apply `hm` to reduce the goal to its premises. Rewrite using `[hQ]`. Use `mul_eq_zero_of_left (Finset.prod_eq_zero (i := zdeg m) (f := fun D : ℤ => (zdeg m : ℂ) - (D : ℂ)) (Finset.mem_erase.2 ⟨hne', Finset.mem_image_of_mem _ hmP⟩) (sub_self (zdeg m : ℂ))) _` and prove the remaining obligations. Rewrite using `[hmm]`. Conclude with `hne (by exact_mod_cast hkey Q hQW hQ0 _ hEQ)`.

Use `⟨hκ, fun m hm t => ?_⟩` and prove the remaining obligations. Establish `hcol : ∀ t, (∑ i, (m (z (i, t)) : ℤ)) - ∑ j, (m (y (j, t)) : ℤ) = κ t`. Introduce `t`. Establish `h1 : coeff m (mixedOp ℂ z y t t P) = (((∑ i, (m (z (i, t)) : ℤ)) - ∑ j, (m (y (j, t)) : ℤ) : ℤ) : ℂ) * coeff m P`. Use `coeff_apply_of_diagonal_on_monomials' _ (fun u => (((∑ i, (u (z (i, t)) : ℤ)) - ∑ j, (u (y (j, t)) : ℤ) : ℤ) : ℂ)) (fun u => ?_) m P` and prove the remaining obligations.

Rewrite using `[mixedOp_apply, ← colOp_apply (K := ℂ) z t t, ← colOp_apply (K := ℂ) y t t, colOp_monomial, colOp_monomial, ← sub_smul]`. Use `push_cast`. Both sides reduce to the same expression. Rewrite `h1` using `[hwt t, coeff_smul, smul_eq_mul]`. Establish `hc : coeff m P ≠ 0` using `mem_support_iff.1 hm`.

Conclude with `(mul_right_cancel₀ hc h1).symm` after adjusting the coercions. Establish `hsum : ∑ t, (∑ i, (m (z (i, t)) : ℤ)) = ∑ t, max (κ t) 0`. Rewrite using `[Finset.sum_comm, ← hzdeg]`. Conclude with `hdeg m hm`. Establish `hle : ∀ t ∈ (Finset.univ : Finset (Fin n)), max (κ t) 0 ≤ ∑ i, (m (z (i, t)) : ℤ)`.

Introduce `t _`. Establish `h0 : 0 ≤ ∑ j, (m (y (j, t)) : ℤ)` using `Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _`. Establish `h0' : 0 ≤ ∑ i, (m (z (i, t)) : ℤ)` using `Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _`. Establish `h` using `hcol t`. Conclude with `max_le (by linarith) h0'`.

Establish `heq` using `(Finset.sum_eq_sum_iff_of_le hle).1 hsum.symm t (Finset.mem_univ t)`. Establish `h` using `hcol t`. Use `⟨heq.symm, ?_⟩` and prove the remaining obligations. Break down `le_total 0 (κ t) with hk | hk` into its components or cases. Rewrite `heq` using `[max_eq_left hk]`.

Rewrite using `[max_eq_right (by linarith)]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite `heq` using `[max_eq_right hk]`. Rewrite using `[max_eq_left (by linarith)]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem column_degrees (σ : Type) [Fintype σ] [DecidableEq σ] (k l n : ℕ)
    (z : Fin k × Fin n → σ) (y : Fin l × Fin n → σ) (hz : Function.Injective z)
    (hy : Function.Injective y) (hzy : ∀ u w, z u ≠ y w) (P : MvPolynomial σ ℂ) (κ : Fin n → ℤ)
    (hP0 : P ≠ 0) (hharm : ∀ i j, ∑ t, pderiv (z (i, t)) (pderiv (y (j, t)) P) = 0)
    (hup : ∀ i j, i < j → mixedOp ℂ z y i j P = 0)
    (hwt : ∀ t, mixedOp ℂ z y t t P = (κ t : ℂ) • P) :
    Antitone κ ∧ ∀ m ∈ P.support, ∀ t, ∑ i, (m (z (i, t)) : ℤ) = max (κ t) 0 ∧
      ∑ j, (m (y (j, t)) : ℤ) = max (-κ t) 0 := by
  classical
  have hPV : P ∈ restrictTotalDegree σ ℂ P.totalDegree := by rw [mem_restrictTotalDegree]
  have hmixV : ∀ i j, ∀ Q ∈ restrictTotalDegree σ ℂ P.totalDegree,
      mixedOp ℂ z y i j Q ∈ restrictTotalDegree σ ℂ P.totalDegree := by
    intro i j Q hQ
    rw [mixedOp_apply, ← colOp_apply (K := ℂ) z i j Q, ← colOp_apply (K := ℂ) y j i Q]
    exact Submodule.sub_mem _ (colOp_mem z i j _ Q hQ) (colOp_mem y j i _ Q hQ)
  have hκ : Antitone κ :=
    highest_weight_antitone (mixedOp ℂ z y) (mixedOp_lie z hz y hy hzy)
      (restrictTotalDegree σ ℂ P.totalDegree) hmixV P hPV hP0 κ hup hwt

  obtain ⟨W, hW⟩ : ∃ W : Submodule ℂ (MvPolynomial σ ℂ), ∀ Q, Q ∈ W ↔
      (Q ∈ restrictTotalDegree σ ℂ P.totalDegree ∧
        (∀ i j, ∑ t, pderiv (z (i, t)) (pderiv (y (j, t)) Q) = 0) ∧
        (∀ i j, i < j → mixedOp ℂ z y i j Q = 0) ∧ ∀ t, mixedOp ℂ z y t t Q = (κ t : ℂ) • Q) :=
    ⟨{ carrier := {Q | Q ∈ restrictTotalDegree σ ℂ P.totalDegree ∧
          (∀ i j, ∑ t, pderiv (z (i, t)) (pderiv (y (j, t)) Q) = 0) ∧
          (∀ i j, i < j → mixedOp ℂ z y i j Q = 0) ∧ ∀ t, mixedOp ℂ z y t t Q = (κ t : ℂ) • Q}
       add_mem' := by
         rintro Q R ⟨h1, h2, h3, h4⟩ ⟨g1, g2, g3, g4⟩
         refine ⟨Submodule.add_mem _ h1 g1, fun i j => ?_, fun i j hij => ?_, fun t => ?_⟩
         · simp only [map_add, Finset.sum_add_distrib, h2 i j, g2 i j, add_zero]
         · rw [map_add, h3 i j hij, g3 i j hij, add_zero]
         · rw [map_add, h4 t, g4 t, smul_add]
       zero_mem' := ⟨Submodule.zero_mem _, fun i j => by simp, fun i j _ => map_zero _,
         fun t => by simp⟩
       smul_mem' := by
         rintro c Q ⟨h1, h2, h3, h4⟩
         refine ⟨Submodule.smul_mem _ c h1, fun i j => ?_, fun i j hij => ?_, fun t => ?_⟩
         · simp only [Derivation.map_smul, ← Finset.smul_sum, h2 i j, smul_zero]
         · rw [map_smul, h3 i j hij, smul_zero]
         · rw [map_smul, h4 t, smul_comm] }, fun Q => Iff.rfl⟩
  have hPW : P ∈ W := (hW P).2 ⟨hPV, hharm, hup, hwt⟩
  have hWz : ∀ a b, ∀ Q ∈ W, rowOp ℂ z a b Q ∈ W := by
    intro a b Q hQ
    obtain ⟨h1, h2, h3, h4⟩ := (hW Q).1 hQ
    refine (hW _).2 ⟨rowOp_mem z a b _ Q h1, fun i j => harmonic_rowOp z y hz hzy Q h2 a b i j,
      fun i j hij => ?_, fun t => ?_⟩
    · rw [← Module.End.mul_apply, ← (commute_rowOp_left_mixedOp z hz y hzy a b i j).eq,
        Module.End.mul_apply, h3 i j hij, map_zero]
    · rw [← Module.End.mul_apply, ← (commute_rowOp_left_mixedOp z hz y hzy a b t t).eq,
        Module.End.mul_apply, h4 t, map_smul]
  have hWy : ∀ a b, ∀ Q ∈ W, rowOp ℂ y a b Q ∈ W := by
    intro a b Q hQ
    obtain ⟨h1, h2, h3, h4⟩ := (hW Q).1 hQ
    have h2' : ∀ i j, ∑ t, pderiv (y (i, t)) (pderiv (z (j, t)) Q) = 0 := by
      intro i j
      rw [← h2 j i]
      exact Finset.sum_congr rfl fun t _ => pderiv_swap _ _ _
    refine (hW _).2 ⟨rowOp_mem y a b _ Q h1, fun i j => ?_, fun i j hij => ?_, fun t => ?_⟩
    · rw [← harmonic_rowOp y z hy (fun u w h => hzy w u h.symm) Q h2' a b j i]
      exact Finset.sum_congr rfl fun t _ => pderiv_swap _ _ _
    · rw [← Module.End.mul_apply, ← (commute_rowOp_right_mixedOp z y hy hzy a b i j).eq,
        Module.End.mul_apply, h3 i j hij, map_zero]
    · rw [← Module.End.mul_apply, ← (commute_rowOp_right_mixedOp z y hy hzy a b t t).eq,
        Module.End.mul_apply, h4 t, map_smul]

  obtain ⟨E, hE⟩ : ∃ E : Module.End ℂ (MvPolynomial σ ℂ), E = ∑ i, rowOp ℂ z i i := ⟨_, rfl⟩
  obtain ⟨zdeg, hzdeg⟩ : ∃ f : (σ →₀ ℕ) → ℤ, ∀ m, f m = ∑ i, ∑ t, (m (z (i, t)) : ℤ) :=
    ⟨_, fun _ => rfl⟩
  have hcoeffE : ∀ m Q, coeff m (E Q) = (zdeg m : ℂ) * coeff m Q := by
    intro m Q
    rw [hE, hzdeg]
    exact coeff_euler z m Q
  have hWE : ∀ Q ∈ W, E Q ∈ W := by
    intro Q hQ
    rw [hE, LinearMap.sum_apply]
    exact Submodule.sum_mem _ fun i _ => hWz i i Q hQ

  have hkey : ∀ Q ∈ W, Q ≠ 0 → ∀ μ : ℂ, E Q = μ • Q → μ = ((∑ t, max (κ t) 0 : ℤ) : ℂ) := by
    intro Q hQW hQ0 μ hμ
    obtain ⟨W', hW'⟩ : ∃ W' : Submodule ℂ (MvPolynomial σ ℂ), ∀ R, R ∈ W' ↔ (R ∈ W ∧ E R = μ • R) :=
      ⟨{ carrier := {R | R ∈ W ∧ E R = μ • R}
         add_mem' := by
           rintro R R' ⟨h1, h2⟩ ⟨g1, g2⟩
           exact ⟨W.add_mem h1 g1, by rw [map_add, h2, g2, smul_add]⟩
         zero_mem' := ⟨W.zero_mem, by simp⟩
         smul_mem' := by
           rintro c R ⟨h1, h2⟩
           exact ⟨W.smul_mem c h1, by rw [map_smul, h2, smul_comm]⟩ }, fun R => Iff.rfl⟩
    have hW'V : W' ≤ restrictTotalDegree σ ℂ P.totalDegree := fun R hR =>
      ((hW R).1 ((hW' R).1 hR).1).1
    have : FiniteDimensional ℂ W' := Submodule.finiteDimensional_of_le hW'V
    have hEz : ∀ a b, Commute E (rowOp ℂ z a b) := by
      intro a b; rw [hE]; exact commute_euler z hz a b
    have hEy : ∀ a b, Commute E (rowOp ℂ y a b) := by
      intro a b; rw [hE]
      exact Commute.sum_left _ _ _ fun i _ => commute_rowOp_rowOp z y hzy i i a b
    have hW'z : ∀ a b, ∀ R ∈ W', rowOp ℂ z a b R ∈ W' := by
      intro a b R hR
      obtain ⟨h1, h2⟩ := (hW' R).1 hR
      refine (hW' _).2 ⟨hWz a b R h1, ?_⟩
      rw [← Module.End.mul_apply, (hEz a b).eq, Module.End.mul_apply, h2, map_smul]
    have hW'y : ∀ a b, ∀ R ∈ W', rowOp ℂ y a b R ∈ W' := by
      intro a b R hR
      obtain ⟨h1, h2⟩ := (hW' R).1 hR
      refine (hW' _).2 ⟨hWy a b R h1, ?_⟩
      rw [← Module.End.mul_apply, (hEy a b).eq, Module.End.mul_apply, h2, map_smul]
    have hQW' : Q ∈ W' := (hW' Q).2 ⟨hQW, hμ⟩
    have hW'0 : W' ≠ ⊥ := by
      intro h
      rw [h] at hQW'
      exact hQ0 ((Submodule.mem_bot ℂ).1 hQW')
    obtain ⟨v, hvW, hv0, hvz, hvy, a, b, ha, hb⟩ :=
      exists_highest_pair (rowOp ℂ z) (rowOp ℂ y) (rowOp_lie z hz) (rowOp_lie y hy)
        (commute_rowOp_rowOp z y hzy)
        (iSup_eigenspace_eq_top (fun i => rowOp ℂ z i i) (fun m i => ∑ t, (m (z (i, t)) : ℤ))
          (fun m i => rowOp_monomial z i m))
        (iSup_eigenspace_eq_top (fun i => rowOp ℂ y i i) (fun m i => ∑ t, (m (y (i, t)) : ℤ))
          (fun m i => rowOp_monomial y i m))
        W' hW'z hW'y hW'0
    obtain ⟨hvW1, hvE⟩ := (hW' v).1 hvW
    obtain ⟨-, hvH, hvU, hvK⟩ := (hW v).1 hvW1
    obtain ⟨a', ha'⟩ := weight_nat z v hv0 a ha
    obtain ⟨b', hb'⟩ := weight_nat y v hv0 b hb
    have haa : Antitone a := highest_weight_antitone (rowOp ℂ z) (rowOp_lie z hz) W' hW'z v hvW hv0 a hvz ha
    have hbb : Antitone b := highest_weight_antitone (rowOp ℂ y) (rowOp_lie y hy) W' hW'y v hvW hv0 b hvy hb
    have ha'a : Antitone a' := fun i j hij => by
      have h := haa hij
      rw [← ha' i, ← ha' j] at h
      exact_mod_cast h
    have hb'b : Antitone b' := fun i j hij => by
      have h := hbb hij
      rw [← hb' i, ← hb' j] at h
      exact_mod_cast h
    have hza : ∀ i, rowOp ℂ z i i v = (a' i : ℂ) • v := fun i => by
      rw [ha i, ← ha' i, Int.cast_natCast]
    have hyb : ∀ i, rowOp ℂ y i i v = (b' i : ℂ) • v := fun i => by
      rw [hb i, ← hb' i, Int.cast_natCast]
    have hT := GlobalTheory.T.sum_row_degree_eq_of_harmonic_highest_casimir σ k l n z y hz hy hzy v a' b' κ hv0 ha'a hb'b hκ hvz hza hvy hyb hvH hvU hvK
    have hEv : E v = ((∑ i, (a' i : ℤ) : ℤ) : ℂ) • v := by
      rw [hE, LinearMap.sum_apply]
      simp only [hza]
      rw [← Finset.sum_smul]
      push_cast
      rfl
    have hzero : (μ - ((∑ i, (a' i : ℤ) : ℤ) : ℂ)) • v = 0 := by
      rw [sub_smul, ← hvE, hEv, sub_self]
    rcases smul_eq_zero.1 hzero with h | h
    · rw [← hT]; exact sub_eq_zero.1 h
    · exact absurd h hv0

  have hdeg : ∀ m ∈ P.support, zdeg m = ∑ t, max (κ t) 0 := by
    intro m0 hm0
    by_contra hne
    have hiter : ∀ s : Finset ℤ, ∃ Q ∈ W, ∀ m,
        coeff m Q = (∏ D ∈ s, ((zdeg m : ℂ) - (D : ℂ))) * coeff m P := by
      intro s
      induction s using Finset.induction_on with
      | empty => exact ⟨P, hPW, fun m => by simp⟩
      | insert D s hD ih =>
        obtain ⟨Q, hQW, hQ⟩ := ih
        refine ⟨E Q - (D : ℂ) • Q, W.sub_mem (hWE Q hQW) (W.smul_mem _ hQW), fun m => ?_⟩
        rw [coeff_sub, coeff_smul, hcoeffE, hQ, Finset.prod_insert hD, smul_eq_mul]
        ring
    obtain ⟨Q, hQW, hQ⟩ := hiter ((P.support.image zdeg).erase (zdeg m0))
    have hQm0 : coeff m0 Q ≠ 0 := by
      rw [hQ]
      refine mul_ne_zero (Finset.prod_ne_zero_iff.2 fun D hD => sub_ne_zero.2 ?_)
        (mem_support_iff.1 hm0)
      intro h
      exact (Finset.mem_erase.1 hD).1 (by exact_mod_cast h.symm)
    have hQ0 : Q ≠ 0 := fun h => hQm0 (by rw [h, coeff_zero])
    have hEQ : E Q = (zdeg m0 : ℂ) • Q := by
      ext m
      rw [hcoeffE, coeff_smul, smul_eq_mul]
      by_cases hm : coeff m Q = 0
      · rw [hm, mul_zero, mul_zero]
      · have hmP : m ∈ P.support := by
          rw [mem_support_iff]
          intro h
          apply hm
          rw [hQ, h, mul_zero]
        have hmm : zdeg m = zdeg m0 := by
          by_contra hne'
          apply hm
          rw [hQ]
          refine mul_eq_zero_of_left (Finset.prod_eq_zero (i := zdeg m)
            (f := fun D : ℤ => (zdeg m : ℂ) - (D : ℂ))
            (Finset.mem_erase.2 ⟨hne', Finset.mem_image_of_mem _ hmP⟩) (sub_self (zdeg m : ℂ))) _
        rw [hmm]
    exact hne (by exact_mod_cast hkey Q hQW hQ0 _ hEQ)
  refine ⟨hκ, fun m hm t => ?_⟩
  have hcol : ∀ t, (∑ i, (m (z (i, t)) : ℤ)) - ∑ j, (m (y (j, t)) : ℤ) = κ t := by
    intro t
    have h1 : coeff m (mixedOp ℂ z y t t P) =
        (((∑ i, (m (z (i, t)) : ℤ)) - ∑ j, (m (y (j, t)) : ℤ) : ℤ) : ℂ) * coeff m P := by
      refine coeff_apply_of_diagonal_on_monomials' _
        (fun u => (((∑ i, (u (z (i, t)) : ℤ)) - ∑ j, (u (y (j, t)) : ℤ) : ℤ) : ℂ))
        (fun u => ?_) m P
      rw [mixedOp_apply, ← colOp_apply (K := ℂ) z t t, ← colOp_apply (K := ℂ) y t t,
        colOp_monomial, colOp_monomial, ← sub_smul]
      push_cast
      rfl
    rw [hwt t, coeff_smul, smul_eq_mul] at h1
    have hc : coeff m P ≠ 0 := mem_support_iff.1 hm
    exact_mod_cast (mul_right_cancel₀ hc h1).symm
  have hsum : ∑ t, (∑ i, (m (z (i, t)) : ℤ)) = ∑ t, max (κ t) 0 := by
    rw [Finset.sum_comm, ← hzdeg]
    exact hdeg m hm
  have hle : ∀ t ∈ (Finset.univ : Finset (Fin n)), max (κ t) 0 ≤ ∑ i, (m (z (i, t)) : ℤ) := by
    intro t _
    have h0 : 0 ≤ ∑ j, (m (y (j, t)) : ℤ) := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
    have h0' : 0 ≤ ∑ i, (m (z (i, t)) : ℤ) := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
    have h := hcol t
    exact max_le (by linarith) h0'
  have heq := (Finset.sum_eq_sum_iff_of_le hle).1 hsum.symm t (Finset.mem_univ t)
  have h := hcol t
  refine ⟨heq.symm, ?_⟩
  rcases le_total 0 (κ t) with hk | hk
  · rw [max_eq_left hk] at heq
    rw [max_eq_right (by linarith)]
    linarith
  · rw [max_eq_right hk] at heq
    rw [max_eq_left (by linarith)]
    linarith

end GlobalTheory.JointHarm.ColumnDegree
