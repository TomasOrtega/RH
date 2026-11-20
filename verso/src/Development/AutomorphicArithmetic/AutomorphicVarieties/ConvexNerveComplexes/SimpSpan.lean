import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.NerveFaceClosed
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.Perturb

open Set UpperTheory.V.ConeExtensionAcyclic

/- English proof (translation)
Introduce `E Y _ _ q T hq n t ht k hk hkq`. Take `⟨x, hx, hxt⟩` from `ht`. Assume the negation of the conclusion as `hk0`. Establish `hxk : 0 < x k` using `hx k hk hk0`. Take `⟨N, hN⟩ : ∃ N : ℝ, N = (n : ℝ) + 1` from `⟨_, rfl⟩`.

Establish `hNpos : (0 : ℝ) < N` using `by rw [hN]; positivity`. Take `⟨c, hc⟩ : ∃ c : E, c = N⁻¹ • ∑ j, (t j).1` from `⟨_, rfl⟩`. Establish `hlin : ∀ f : E →L[ℝ] ℝ, f c = N⁻¹ * ∑ j, f (t j).1`. Introduce `f`. Rewrite using `[hc, map_smul, map_sum, smul_eq_mul]`.

Establish `hpoly : ∀ j, (t j).1 ∈ poly q` using `fun j => (t j).2.1`. Establish `hconst : ∀ a : ℝ, (∑ _j : Fin (n + 1), a) = N * a`. Introduce `a`. Simplify using `[hN]`. Establish `hcpoly : c ∈ poly q`.

Introduce `y`. Rewrite using `[hlin, le_inv_mul_iff₀ hNpos]`. Establish `h1` using `hconst 1`. Rewrite `h1` using `[mul_one]`. Rewrite using `[mul_one, ← h1]`.

Conclude with `Finset.sum_le_sum fun j _ => hpoly j y`. Establish `htight : ∀ y, q y c = 1 → ∀ j, q y (t j).1 = 1`. Introduce `y hy j`. Rewrite `hy` using `[hlin, inv_mul_eq_one₀ hNpos.ne']`. Establish `hnn : ∀ i ∈ Finset.univ, 0 ≤ q y (t i).1 - 1` using `fun i _ => sub_nonneg.mpr (hpoly i y)`.

Establish `hz : ∑ i, (q y (t i).1 - 1) = 0`. Rewrite using `[Finset.sum_sub_distrib, ← hy, hconst, mul_one, sub_self]`. Use `(Finset.sum_eq_zero_iff_of_nonneg hnn).mp hz j (Finset.mem_univ j)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨ε, hε, hpert⟩` from `perturb hq c hcpoly k (fun y hy => hkq y (htight y hy))`.

Establish `hmem : c + (-ε) • k ∈ poly q` using `hpert (-ε) (by rw [abs_neg, abs_of_pos hε])`. Establish `hsum_le : ∑ j, x (t j).1 ≤ N * x (c + (-ε) • k)`. Rewrite using `[← hconst]`. Conclude with `Finset.sum_le_sum fun j _ => hxt j _ hmem`. Establish `hexp : x (c + (-ε) • k) = x c - ε * x k`.

Rewrite using `[map_add, map_smul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hxc : N * x c = ∑ j, x (t j).1`. Rewrite using `[hlin x, ← mul_assoc, mul_inv_cancel₀ hNpos.ne', one_mul]`. Rewrite `hsum_le` using `[hexp, ← hxc]`.

Use polynomial arithmetic with `[mul_pos hNpos (mul_pos hε hxk)]`.
-/
theorem UpperTheory.V.ConeExtensionAcyclic.simp_span :
    ∀ {E Y : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {q : Y → E →L[ℝ] ℝ} {T : Set E}, LocFin q → ∀ (n : ℕ) (t : Fin (n + 1) → Vert q), t ∈ simp q T (n + 1) → ∀ k ∈ T, (∀ y, (∀ j, q y (t j).1 = 1) → q y k = 0) → k = 0 := by
  intro E Y _ _ q T hq n t ht k hk hkq
  obtain ⟨x, hx, hxt⟩ := ht
  by_contra hk0
  have hxk : 0 < x k := hx k hk hk0
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = (n : ℝ) + 1 := ⟨_, rfl⟩
  have hNpos : (0 : ℝ) < N := by rw [hN]; positivity
  obtain ⟨c, hc⟩ : ∃ c : E, c = N⁻¹ • ∑ j, (t j).1 := ⟨_, rfl⟩
  have hlin : ∀ f : E →L[ℝ] ℝ, f c = N⁻¹ * ∑ j, f (t j).1 := by
    intro f
    rw [hc, map_smul, map_sum, smul_eq_mul]
  have hpoly : ∀ j, (t j).1 ∈ poly q := fun j => (t j).2.1
  have hconst : ∀ a : ℝ, (∑ _j : Fin (n + 1), a) = N * a := by
    intro a
    simp [hN]
  have hcpoly : c ∈ poly q := by
    intro y
    rw [hlin, le_inv_mul_iff₀ hNpos]
    have h1 := hconst 1
    rw [mul_one] at h1
    rw [mul_one, ← h1]
    exact Finset.sum_le_sum fun j _ => hpoly j y
  have htight : ∀ y, q y c = 1 → ∀ j, q y (t j).1 = 1 := by
    intro y hy j
    rw [hlin, inv_mul_eq_one₀ hNpos.ne'] at hy
    have hnn : ∀ i ∈ Finset.univ, 0 ≤ q y (t i).1 - 1 := fun i _ => sub_nonneg.mpr (hpoly i y)
    have hz : ∑ i, (q y (t i).1 - 1) = 0 := by
      rw [Finset.sum_sub_distrib, ← hy, hconst, mul_one, sub_self]
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hz j (Finset.mem_univ j)
    linarith
  obtain ⟨ε, hε, hpert⟩ := perturb hq c hcpoly k (fun y hy => hkq y (htight y hy))
  have hmem : c + (-ε) • k ∈ poly q := hpert (-ε) (by rw [abs_neg, abs_of_pos hε])
  have hsum_le : ∑ j, x (t j).1 ≤ N * x (c + (-ε) • k) := by
    rw [← hconst]
    exact Finset.sum_le_sum fun j _ => hxt j _ hmem
  have hexp : x (c + (-ε) • k) = x c - ε * x k := by
    rw [map_add, map_smul, smul_eq_mul]
    ring
  have hxc : N * x c = ∑ j, x (t j).1 := by
    rw [hlin x, ← mul_assoc, mul_inv_cancel₀ hNpos.ne', one_mul]
  rw [hexp, ← hxc] at hsum_le
  nlinarith [mul_pos hNpos (mul_pos hε hxk)]
