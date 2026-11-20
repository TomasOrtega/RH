import Development.AbelianVarietyTheory.Definitions.Foundations.IsFirstChernClassOfLineBundle
open GlobalTheory.NeedB Polynomial

namespace GlobalTheory

open MvPolynomial

/- English proof (translation)
Introduce `F K _ _ _ _ hF n d f hf hd hdn`. Use `set m := Module.finrank F K with hm`. Establish `hm0 : 0 < m` using `Module.finrank_pos`. Set `b : Module.Basis (Fin m) F K` to `Module.finBasis F K`. Set `e : Fin n × Fin m ≃ Fin (n * m)` to `finProdFinEquiv`.

Set `g : Fin n → MvPolynomial (Fin (n * m)) K` to `fun i => ∑ j, MvPolynomial.C (b j) * MvPolynomial.X (e (i, j))`. Establish `hg : ∀ i, (g i).IsHomogeneous 1` using `fun i => IsHomogeneous.sum _ _ _ (fun j _ => isHomogeneous_C_mul_X _ _)`. Set `G : MvPolynomial (Fin (n * m)) K` to `aeval g f`. Establish `hG : G.IsHomogeneous d`. Establish `h1` using `hf.aeval g hg`.

Rewrite `h1` using `[one_mul]`. Then use the resulting hypothesis. Set `P : Fin m → MvPolynomial (Fin (n * m)) F` to `fun l => ∑ s ∈ G.support, monomial s (b.repr (G.coeff s) l)`. Establish `hP : ∀ l, (P l).IsHomogeneous d` using `fun l => IsHomogeneous.sum _ _ _ (fun s hs => isHomogeneous_monomial _ (by`. Rewrite using `[Finsupp.degree_eq_weight_one]`. Conclude with `hG (mem_support_iff.mp hs)))`.

Establish `hlt : m * d < n * m`. Rewrite using `[mul_comm n m]`. Conclude with `Nat.mul_lt_mul_of_pos_left hdn hm0`. Take `⟨y, hy0, hy⟩` from `hF (n * m) m d P hP hd hlt`. Set `x : Fin n → K` to `fun i => ∑ j, algebraMap F K (y (e (i, j))) * b j`.

Use `⟨x, ?_, ?_⟩` and prove the remaining obligations. Introduce `hx`. Apply `hy0` to reduce the goal to its premises. Use function extensionality and compare the values at `k`. Take `⟨⟨i, j⟩, rfl⟩` from `e.surjective k`.

Establish `hxi : ∑ j, y (e (i, j)) • b j = 0`. Use `congrFun hx i` as an intermediate fact. Simplify `this` using `[x, Algebra.smul_def]`. Conclude with `Fintype.linearIndependent_iff.mp b.linearIndependent (fun j => y (e (i, j))) hxi j`. Establish `key : MvPolynomial.eval x f = MvPolynomial.eval (fun k => algebraMap F K (y k)) G`.

Rewrite using `[← MvPolynomial.coe_aeval_eq_eval, ← MvPolynomial.coe_aeval_eq_eval]`. Use `show _ = MvPolynomial.aeval _ (MvPolynomial.bind₁ g f)`. Rewrite using `[MvPolynomial.aeval_bind₁]`. Establish `hxe : x = fun i => MvPolynomial.aeval (fun k => algebraMap F K (y k)) (g i)`. Use function extensionality and compare the values at `i`.

Simplify using `[g, x, mul_comm]`. Rewrite using `[hxe]`. Both sides reduce to the same expression. Establish `key2 : MvPolynomial.eval (fun k => algebraMap F K (y k)) G = ∑ l, algebraMap F K (MvPolynomial.eval y (P l)) * b l`. Simplify using `only [P, map_sum, MvPolynomial.eval_monomial, Finset.sum_mul]`.

Rewrite using `[Finset.sum_comm, MvPolynomial.eval_eq]`. Use `Finset.sum_congr rfl (fun s hs => ?_)` and prove the remaining obligations. Use `conv_lhs => rw [← b.sum_repr (G.coeff s)]`. Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_congr rfl (fun l _ => ?_)` and prove the remaining obligations.

Simplify using `[Finsupp.prod, map_prod, map_pow, Algebra.smul_def]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key, key2]`. Conclude with `Finset.sum_eq_zero (fun l _ => by rw [hy l, map_zero, zero_mul])`.
-/
theorem is_c1_of_finite_of_tsen_lang_systems : ∀ (F K : Type) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K],
  (∀ (n r d : ℕ) (f : Fin r → MvPolynomial (Fin n) F), (∀ i, (f i).IsHomogeneous d) → 0 < d → r * d < n →
    ∃ x : Fin n → F, x ≠ 0 ∧ ∀ i, MvPolynomial.eval x (f i) = 0) → IsFirstChernClassOfLineBundle K := by
  intro F K _ _ _ _ hF n d f hf hd hdn
  set m := Module.finrank F K with hm
  have hm0 : 0 < m := Module.finrank_pos
  let b : Module.Basis (Fin m) F K := Module.finBasis F K
  let e : Fin n × Fin m ≃ Fin (n * m) := finProdFinEquiv
  let g : Fin n → MvPolynomial (Fin (n * m)) K := fun i => ∑ j, MvPolynomial.C (b j) * MvPolynomial.X (e (i, j))
  have hg : ∀ i, (g i).IsHomogeneous 1 := fun i =>
    IsHomogeneous.sum _ _ _ (fun j _ => isHomogeneous_C_mul_X _ _)
  let G : MvPolynomial (Fin (n * m)) K := aeval g f
  have hG : G.IsHomogeneous d := by
    have h1 := hf.aeval g hg
    rwa [one_mul] at h1
  let P : Fin m → MvPolynomial (Fin (n * m)) F := fun l =>
    ∑ s ∈ G.support, monomial s (b.repr (G.coeff s) l)
  have hP : ∀ l, (P l).IsHomogeneous d := fun l =>
    IsHomogeneous.sum _ _ _ (fun s hs => isHomogeneous_monomial _ (by
      rw [Finsupp.degree_eq_weight_one]; exact hG (mem_support_iff.mp hs)))
  have hlt : m * d < n * m := by
    rw [mul_comm n m]; exact Nat.mul_lt_mul_of_pos_left hdn hm0
  obtain ⟨y, hy0, hy⟩ := hF (n * m) m d P hP hd hlt
  let x : Fin n → K := fun i => ∑ j, algebraMap F K (y (e (i, j))) * b j
  refine ⟨x, ?_, ?_⟩
  · intro hx
    apply hy0
    funext k
    obtain ⟨⟨i, j⟩, rfl⟩ := e.surjective k
    have hxi : ∑ j, y (e (i, j)) • b j = 0 := by
      have := congrFun hx i
      simpa [x, Algebra.smul_def] using this
    exact Fintype.linearIndependent_iff.mp b.linearIndependent (fun j => y (e (i, j))) hxi j
  · have key : MvPolynomial.eval x f = MvPolynomial.eval (fun k => algebraMap F K (y k)) G := by
      rw [← MvPolynomial.coe_aeval_eq_eval, ← MvPolynomial.coe_aeval_eq_eval]
      show _ = MvPolynomial.aeval _ (MvPolynomial.bind₁ g f)
      rw [MvPolynomial.aeval_bind₁]
      have hxe : x = fun i => MvPolynomial.aeval (fun k => algebraMap F K (y k)) (g i) := by
        funext i
        simp [g, x, mul_comm]
      rw [hxe]
      rfl
    have key2 : MvPolynomial.eval (fun k => algebraMap F K (y k)) G
        = ∑ l, algebraMap F K (MvPolynomial.eval y (P l)) * b l := by
      simp only [P, map_sum, MvPolynomial.eval_monomial, Finset.sum_mul]
      rw [Finset.sum_comm, MvPolynomial.eval_eq]
      refine Finset.sum_congr rfl (fun s hs => ?_)
      conv_lhs => rw [← b.sum_repr (G.coeff s)]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      simp [Finsupp.prod, map_prod, map_pow, Algebra.smul_def]
      ring
    rw [key, key2]
    exact Finset.sum_eq_zero (fun l _ => by rw [hy l, map_zero, zero_mul])

end GlobalTheory
