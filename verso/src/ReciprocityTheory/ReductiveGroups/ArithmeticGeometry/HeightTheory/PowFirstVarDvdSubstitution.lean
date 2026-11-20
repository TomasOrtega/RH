import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.AevalElimEqRenameLinearSubstitution
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.RelationMapCommTransvection

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MvPolynomial

/- English proof (translation)
Establish `key : ∀ m ∈ F.support, ∏ t, (if t.1 ∈ s then l * r t else r t) ^ m t = l ^ (s.card * d0) * ∏ t, r t ^ m t`. Introduce `m hm`. Establish `h1 : ∀ t : Fin B × Fin n, (if t.1 ∈ s then l * r t else r t) ^ m t = (if t.1 ∈ s then l ^ m t else 1) * r t ^ m t`. Introduce `t`. Apply the tactic sequence `split_ifs <;> simp [mul_pow]`.

Repeatedly rewrite using `[h1, Finset.prod_mul_distrib]`. Use `congr 1`. Rewrite using `[Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_pow_eq_pow_sum]`. Use `congr 1`. Rewrite using `[Finset.sum_filter, Fintype.sum_prod_type]`.

Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl (fun b _ => ?_)` and prove the remaining obligations. Use `split_ifs with hb`. Conclude with `hF m hm b`. Simplify using the standard rewrite rules.

Use `_ = s.card * d0 := by`. Rewrite using `[← Finset.sum_filter, Finset.sum_const, Finset.filter_mem_eq_inter, Finset.univ_inter, smul_eq_mul]`. Use `conv_lhs => rw [F.as_sum]`. Use `conv_rhs => rw [F.as_sum]`. Simplify using `only [map_sum, aeval_monomial, Finset.mul_sum]`.

Use `Finset.sum_congr rfl (fun m hm => ?_)` and prove the remaining obligations. Rewrite using `[Finsupp.prod_fintype, Finsupp.prod_fintype]`. Use `beta_reduce`. Rewrite using `[key m hm]`. Expand and normalize the polynomial expressions, which then agree.

Introduce `i`. Simplify using the standard rewrite rules. Introduce `i`. Simplify using the standard rewrite rules.
-/
theorem aeval_scale_rows {R : Type*} [CommRing R] {B n : ℕ} (d0 : ℕ)
    (F : MvPolynomial (Fin B × Fin n) R) (hF : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => d0) F)
    {S : Type*} [CommRing S] [Algebra R S] (r : Fin B × Fin n → S) (s : Finset (Fin B)) (l : S) :
    aeval (fun t => if t.1 ∈ s then l * r t else r t) F = l ^ (s.card * d0) * aeval r F := by
  have key : ∀ m ∈ F.support, ∏ t, (if t.1 ∈ s then l * r t else r t) ^ m t =
      l ^ (s.card * d0) * ∏ t, r t ^ m t := by
    intro m hm
    have h1 : ∀ t : Fin B × Fin n, (if t.1 ∈ s then l * r t else r t) ^ m t =
        (if t.1 ∈ s then l ^ m t else 1) * r t ^ m t := by
      intro t
      split_ifs <;> simp [mul_pow]
    simp_rw [h1, Finset.prod_mul_distrib]
    congr 1
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_pow_eq_pow_sum]
    congr 1
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    calc ∑ b, ∑ j, (if b ∈ s then m (b, j) else 0) = ∑ b, (if b ∈ s then d0 else 0) := by
          refine Finset.sum_congr rfl (fun b _ => ?_)
          split_ifs with hb
          · exact hF m hm b
          · simp
      _ = s.card * d0 := by
          rw [← Finset.sum_filter, Finset.sum_const, Finset.filter_mem_eq_inter, Finset.univ_inter,
            smul_eq_mul]
  conv_lhs => rw [F.as_sum]
  conv_rhs => rw [F.as_sum]
  simp only [map_sum, aeval_monomial, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  rw [Finsupp.prod_fintype, Finsupp.prod_fintype]
  · beta_reduce
    rw [key m hm]
    ring
  · intro i
    simp
  · intro i
    simp

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

/- English proof (translation)
Use `revert hks`. Use `Finset.induction_on s (fun _ => by simp) ?_` and prove the remaining obligations. Introduce `i s hi ih hks`. Establish `hik : i ≠ k` using `fun h => hks (h ▸ Finset.mem_insert_self _ _)`. Establish `hks' : k ∉ s` using `fun h => hks (Finset.mem_insert_of_mem h)`.

Rewrite using `[← ih hks', ← d.aeval_trv c F0 hF0 hker i k hik (fun t => if t.1 ∈ s then r t + b t.1 * r (k, t.2) else r t) (b i)]`. Use `congr 2`. Use function extensionality and compare the values at `t`. Distinguish the cases in `h1 : t.1 = i`. Simplify using `[h1, hi, hks']`.

Simplify using `[h1, Finset.mem_insert]`.
-/
theorem aeval_trv_set (c : ι) (F0 : KTp K d.D d.N) (hF0 : F0 ≠ 0)
    (hker : ∀ Q : KTp K d.D d.N, d.relationEliminateColumn c Q = 0 ↔ F0 ∣ Q) (k : Fin (d.D + 1))
    (s : Finset (Fin (d.D + 1))) (hks : k ∉ s)
    {S : Type*} [CommRing S] [Algebra K S] (r : TVar d.D d.N → S) (b : Fin (d.D + 1) → S) :
    aeval (fun t => if t.1 ∈ s then r t + b t.1 * r (k, t.2) else r t) F0 = aeval r F0 := by
  classical
  revert hks
  refine Finset.induction_on s (fun _ => by simp) ?_
  intro i s hi ih hks
  have hik : i ≠ k := fun h => hks (h ▸ Finset.mem_insert_self _ _)
  have hks' : k ∉ s := fun h => hks (Finset.mem_insert_of_mem h)
  rw [← ih hks', ← d.aeval_trv c F0 hF0 hker i k hik
    (fun t => if t.1 ∈ s then r t + b t.1 * r (k, t.2) else r t) (b i)]
  congr 2
  funext t
  by_cases h1 : t.1 = i
  · simp [h1, hi, hks']
  · simp [h1, Finset.mem_insert]

/- English proof (translation)
Set `S` to `FractionRing (MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K)`. Set `φ : MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K →ₐ[K] S` to `IsScalarTower.toAlgHom K _ S`. Establish `hφ : Function.Injective φ` using `IsFractionRing.injective _ S`. Set `x : Fin (d.D + 2) → S` to `fun i => φ (X (Sum.inr i))`. Set `U : Fin (d.D + 2) → Fin (d.N + 1) → S` to `fun a j => φ (X (Sum.inl (a, j)))`.

Establish `hx : ∀ i, x i ≠ 0` using `fun i h0 => X_ne_zero (R := K) (Sum.inr i : (Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) (hφ (h0.trans (map_zero φ).symm))`. Establish `hx1` using `hx 1`. Set `r : TVar d.D d.N → S` to `fun t => x 0 * U t.1.succ t.2 - x t.1.succ * U 0 t.2`. Establish `hG : φ (bilinearSubstitution F0) = aeval r F0`. Rewrite using `[bilinearSubstitution, ← AlgHom.comp_apply, MvPolynomial.comp_aeval]`.

Use `congr 2`. Use function extensionality and compare the values at `t`. Simplify using `[r, x, U]`. Set `s : Finset (Fin (d.D + 1))` to `Finset.univ.erase 0`. Establish `hs : s.card = d.D` using `by simp [s, Finset.card_erase_of_mem]`.

Set `W : TVar d.D d.N → S` to `fun t => U t.1.succ t.2 - x t.1.succ / x 1 * U 1 t.2`. Establish `e1` using `d.aeval_trv_set c F0 hF0 hker 0 s (by simp [s]) r (fun i => -(x i.succ / x 1))`. Establish `hrows : (fun t : TVar d.D d.N => if t.1 ∈ s then r t + -(x t.1.succ / x 1) * r (0, t.2) else r t) = fun t => if t.1 ∈ s then x 0 * (if t.1 ∈ s then W t else r t) else (if t.1 ∈ s then W t else r t)`. Use function extensionality and compare the values at `t`. Use `split_ifs`.

Simplify using `only [r, W, Fin.succ_zero_eq_one]`. Take the linear combination `(x t.1.succ * U 0 t.2) * mul_inv_cancel₀ hx1`. Both sides reduce to the same expression. Rewrite `e1` using `[hrows, aeval_scale_rows d0 F0 hmh _ s (x 0), hs]`. Establish `e2` using `aeval_scale_rows d0 F0 hmh (fun t => if t.1 ∈ s then W t else r t) s (x 1)`.

Rewrite `e2` using `[hs]`. Set `P : TVar d.D d.N → MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K` to `fun t => if t.1 ∈ s then X (Sum.inr 1) * X (Sum.inl (t.1.succ, t.2)) - X (Sum.inr t.1.succ) * X (Sum.inl (1, t.2)) else X (Sum.inr 0) * X (Sum.inl (t.1.succ, t.2)) - X (Sum.inr t.1.succ) * X (Sum.inl (0, t.2))`. Establish `hP : φ (aeval P F0) = aeval (fun t => if t.1 ∈ s then x 1 * (if t.1 ∈ s then W t else r t) else (if t.1 ∈ s then W t else r t)) F0`. Rewrite using `[← AlgHom.comp_apply, MvPolynomial.comp_aeval]`. Use `congr 2`.

Use function extensionality and compare the values at `t`. Simplify using `only [P]`. Use `split_ifs`. Simplify using `only [map_sub, map_mul, W, x, U]`. Simplify using `only [x] at hx1`.

Take the linear combination `(φ (X (Sum.inr t.1.succ)) * φ (X (Sum.inl (1, t.2)))) * mul_inv_cancel₀ hx1`. Simplify using `[r, x, U]`. Establish `key : φ (X (Sum.inr 1) ^ (d.D * d0) * bilinearSubstitution F0) = φ (X (Sum.inr 0) ^ (d.D * d0) * aeval P F0)`. Rewrite using `[map_mul, map_mul, map_pow, map_pow]`. Use `show x 1 ^ (d.D * d0) * φ (bilinearSubstitution F0) = x 0 ^ (d.D * d0) * φ (aeval P F0)`.

Rewrite using `[hG, ← e1, hP, e2]`. Expand and normalize the polynomial expressions, which then agree. Establish `key'` using `hφ key`. Establish `hp : Prime (X (Sum.inr 0) : MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K)` using `MvPolynomial.X_prime`. Establish `hnd : ¬ (X (Sum.inr 0) : MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K) ∣ X (Sum.inr 1) ^ (d.D * d0)`.

Introduce `h`. Take `⟨q, hq⟩` from `hp.dvd_of_dvd_pow h`. Use `congrArg (MvPolynomial.eval (fun v => if v = Sum.inr 0 then (0 : K) else 1)) hq` as an intermediate fact. Simplify using `at this`. Conclude with `hp.pow_dvd_of_dvd_mul_left _ hnd ⟨_, key'⟩`.
-/
theorem pow_first_var_dvd_substitution (c : ι) (F0 : KTp K d.D d.N) (hF0 : F0 ≠ 0)
    (hker : ∀ Q : KTp K d.D d.N, d.relationEliminateColumn c Q = 0 ↔ F0 ∣ Q) (d0 : ℕ)
    (hmh : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => d0) F0) :
    (X (Sum.inr 0) : MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K) ^ (d.D * d0) ∣
      bilinearSubstitution F0 := by
  classical
  let S := FractionRing (MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K)
  let φ : MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K →ₐ[K] S :=
    IsScalarTower.toAlgHom K _ S
  have hφ : Function.Injective φ := IsFractionRing.injective _ S
  let x : Fin (d.D + 2) → S := fun i => φ (X (Sum.inr i))
  let U : Fin (d.D + 2) → Fin (d.N + 1) → S := fun a j => φ (X (Sum.inl (a, j)))
  have hx : ∀ i, x i ≠ 0 := fun i h0 => X_ne_zero (R := K)
    (Sum.inr i : (Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) (hφ (h0.trans (map_zero φ).symm))
  have hx1 := hx 1
  let r : TVar d.D d.N → S := fun t => x 0 * U t.1.succ t.2 - x t.1.succ * U 0 t.2
  have hG : φ (bilinearSubstitution F0) = aeval r F0 := by
    rw [bilinearSubstitution, ← AlgHom.comp_apply, MvPolynomial.comp_aeval]
    congr 2; funext t; simp [r, x, U]
  let s : Finset (Fin (d.D + 1)) := Finset.univ.erase 0
  have hs : s.card = d.D := by simp [s, Finset.card_erase_of_mem]
  let W : TVar d.D d.N → S := fun t => U t.1.succ t.2 - x t.1.succ / x 1 * U 1 t.2
  have e1 := d.aeval_trv_set c F0 hF0 hker 0 s (by simp [s]) r (fun i => -(x i.succ / x 1))
  have hrows : (fun t : TVar d.D d.N => if t.1 ∈ s then r t + -(x t.1.succ / x 1) * r (0, t.2) else r t) =
      fun t => if t.1 ∈ s then x 0 * (if t.1 ∈ s then W t else r t)
        else (if t.1 ∈ s then W t else r t) := by
    funext t
    split_ifs
    · simp only [r, W, Fin.succ_zero_eq_one]
      linear_combination (x t.1.succ * U 0 t.2) * mul_inv_cancel₀ hx1
    · rfl
  rw [hrows, aeval_scale_rows d0 F0 hmh _ s (x 0), hs] at e1
  have e2 := aeval_scale_rows d0 F0 hmh (fun t => if t.1 ∈ s then W t else r t) s (x 1)
  rw [hs] at e2
  let P : TVar d.D d.N → MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K := fun t =>
    if t.1 ∈ s then X (Sum.inr 1) * X (Sum.inl (t.1.succ, t.2)) - X (Sum.inr t.1.succ) * X (Sum.inl (1, t.2))
    else X (Sum.inr 0) * X (Sum.inl (t.1.succ, t.2)) - X (Sum.inr t.1.succ) * X (Sum.inl (0, t.2))
  have hP : φ (aeval P F0) = aeval (fun t => if t.1 ∈ s then x 1 * (if t.1 ∈ s then W t else r t)
      else (if t.1 ∈ s then W t else r t)) F0 := by
    rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
    congr 2; funext t
    simp only [P]
    split_ifs
    · simp only [map_sub, map_mul, W, x, U]
      simp only [x] at hx1
      linear_combination (φ (X (Sum.inr t.1.succ)) * φ (X (Sum.inl (1, t.2)))) * mul_inv_cancel₀ hx1
    · simp [r, x, U]
  have key : φ (X (Sum.inr 1) ^ (d.D * d0) * bilinearSubstitution F0) = φ (X (Sum.inr 0) ^ (d.D * d0) * aeval P F0) := by
    rw [map_mul, map_mul, map_pow, map_pow]
    show x 1 ^ (d.D * d0) * φ (bilinearSubstitution F0) = x 0 ^ (d.D * d0) * φ (aeval P F0)
    rw [hG, ← e1, hP, e2]; ring
  have key' := hφ key
  have hp : Prime (X (Sum.inr 0) : MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K) :=
    MvPolynomial.X_prime
  have hnd : ¬ (X (Sum.inr 0) : MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K) ∣
      X (Sum.inr 1) ^ (d.D * d0) := by
    intro h
    obtain ⟨q, hq⟩ := hp.dvd_of_dvd_pow h
    have := congrArg (MvPolynomial.eval (fun v => if v = Sum.inr 0 then (0 : K) else 1)) hq
    simp at this
  exact hp.pow_dvd_of_dvd_mul_left _ hnd ⟨_, key'⟩

end Data

end ReciprocityTheory.ChartRestriction.G.T0
