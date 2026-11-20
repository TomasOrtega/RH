import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.ColAnti

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.S7.CapAd

open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli

variable {𝒰 : Type*} [Ring 𝒰] [Algebra ℂ 𝒰] {n : ℕ}

/- English proof (translation)
The claim follows from `| 0, f => by simp | p + 1, f => by rw [List.ofFn_succ, List.prod_cons, prod_ofFn_sum (fun j => f j.succ), Finset.sum_mul_sum, ← (Fin.consEquiv fun _ : Fin (p + 1) => α).sum_comp, Fintype.sum_prod_type] refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun γ _ => ?_ show …`.
-/
lemma prod_ofFn_sum {α : Type*} [Fintype α] : ∀ {p : ℕ} (f : Fin p → α → 𝒰),
    (List.ofFn fun j => ∑ a, f j a).prod = ∑ γ : Fin p → α, (List.ofFn fun j => f j (γ j)).prod
  | 0, f => by simp
  | p + 1, f => by
    rw [List.ofFn_succ, List.prod_cons, prod_ofFn_sum (fun j => f j.succ), Finset.sum_mul_sum,
      ← (Fin.consEquiv fun _ : Fin (p + 1) => α).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun γ _ => ?_
    show _ = (List.ofFn fun j => f j (Fin.cons (α := fun _ => α) a γ j)).prod
    simp only [List.ofFn_succ, List.prod_cons, Fin.cons_zero, Fin.cons_succ]

/- English proof (translation)
The claim follows from `| 0, s, a => by simp | p + 1, s, a => by simp only [List.ofFn_succ, List.prod_cons] rw [prod_ofFn_smul (fun j => s j.succ) (fun j => a j.succ), Fin.prod_univ_succ, smul_mul_smul_comm]`.
-/
lemma prod_ofFn_smul : ∀ {p : ℕ} (s : Fin p → ℂ) (a : Fin p → 𝒰),
    (List.ofFn fun j => s j • a j).prod = (∏ j, s j) • (List.ofFn a).prod
  | 0, s, a => by simp
  | p + 1, s, a => by
    simp only [List.ofFn_succ, List.prod_cons]
    rw [prod_ofFn_smul (fun j => s j.succ) (fun j => a j.succ), Fin.prod_univ_succ, smul_mul_smul_comm]

/- English proof (translation)
Simplify using `only [capEntry, smul_add, Finset.sum_add_distrib]`. Use `congr 1`. Simplify using `only [smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Rewrite using `[← Finset.sum_smul]`. Establish `h : ∑ c, P c a * Q b c = (Q * P) b a`.

Rewrite using `[Matrix.mul_apply]`. Conclude with `Finset.sum_congr rfl (fun c _ => mul_comm _ _)`. Rewrite using `[h, hQP, Matrix.one_apply]`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality.

Simplify using the standard rewrite rules. Rewrite using `[if_neg (Ne.symm hab), if_neg hab, zero_smul]`.
-/
lemma capEntry_ad (E : Fin n → Fin n → 𝒰) (P Q : Matrix (Fin n) (Fin n) ℂ) (hQP : Q * P = 1) (x : ℂ)
    (a b : Fin n) :
    capEntry (fun a b => ∑ c, ∑ d, (P c a * Q b d) • E c d) x a b =
      ∑ c, ∑ d, (P c a * Q b d) • capEntry E x c d := by
  simp only [capEntry, smul_add, Finset.sum_add_distrib]
  congr 1
  simp only [smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [← Finset.sum_smul]
  have h : ∑ c, P c a * Q b c = (Q * P) b a := by
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl (fun c _ => mul_comm _ _)
  rw [h, hQP, Matrix.one_apply]
  by_cases hab : a = b
  · subst hab; simp
  · rw [if_neg (Ne.symm hab), if_neg hab, zero_smul]

/- English proof (translation)
Rewrite using `[← Matrix.det_transpose, Matrix.det_apply]`. Use `Finset.sum_congr rfl (fun σ _ => ?_)` and prove the remaining obligations. Rewrite using `[Units.smul_def]`. Both sides reduce to the same expression.
-/
lemma coef_det (P : Matrix (Fin n) (Fin n) ℂ) (c : Fin n → Fin n) :
    ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤˣ) : ℤ) • ∏ j, P (c j) (σ j) = (P.submatrix c id).det := by
  rw [← Matrix.det_transpose, Matrix.det_apply]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [Units.smul_def]
  rfl

/- English proof (translation)
Establish `himg : ∑ τ : Equiv.Perm (Fin n), f τ = ∑ c ∈ Finset.univ.image (fun τ : Equiv.Perm (Fin n) => (τ : Fin n → Fin n)), f c`. Rewrite using `[Finset.sum_image]`. Introduce `a _ b _ h`. Conclude with `Equiv.ext (congrFun h)`. Rewrite using `[himg]`.

Use `symm`. Apply `Finset.sum_subset (Finset.subset_univ _)` to reduce the goal to its premises. Introduce `c _ hc`. Apply `hf` to reduce the goal to its premises. Introduce `hinj`.

Apply `hc` to reduce the goal to its premises. Rewrite using `[Finset.mem_image]`. Conclude with `⟨Equiv.ofBijective c (Finite.injective_iff_bijective.1 hinj), Finset.mem_univ _, rfl⟩`.
-/
lemma sum_fun_perm {M : Type*} [AddCommMonoid M] (f : (Fin n → Fin n) → M)
    (hf : ∀ c, ¬ Function.Injective c → f c = 0) : ∑ c, f c = ∑ τ : Equiv.Perm (Fin n), f τ := by
  classical
  have himg : ∑ τ : Equiv.Perm (Fin n), f τ =
      ∑ c ∈ Finset.univ.image (fun τ : Equiv.Perm (Fin n) => (τ : Fin n → Fin n)), f c := by
    rw [Finset.sum_image]
    intro a _ b _ h
    exact Equiv.ext (congrFun h)
  rw [himg]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro c _ hc
  apply hf
  intro hinj
  apply hc
  rw [Finset.mem_image]
  exact ⟨Equiv.ofBijective c (Finite.injective_iff_bijective.1 hinj), Finset.mem_univ _, rfl⟩

/- English proof (translation)
Apply the tactic sequence `have hstep : ∀ σ : Equiv.Perm (Fin n), (List.ofFn fun j : Fin n => capEntry (fun a b => ∑ c, ∑ d, (P c a * Q b d) • E c d) (x - ((j : ℕ) : ℂ)) (σ j) j).prod = ∑ γ : Fin n → Fin n × Fin n, (∏ j, (P (γ j).1 (σ j) * Q j (γ j).2)) • (List.ofFn fun j : Fin n => capEntry E (x - ((j : ℕ …`. Introduce `σ`. Apply the tactic sequence `have h1 : ∀ j : Fin n, capEntry (fun a b => ∑ c, ∑ d, (P c a * Q b d) • E c d) (x - ((j : ℕ) : ℂ)) (σ j) j = ∑ cd : Fin n × Fin n, (P cd.1 (σ j) * Q j cd.2) • capEntry E (x - ((j : ℕ) : ℂ)) cd.1 cd.2 := by`. Introduce `j`. Rewrite using `[capEntry_ad E P Q hQP, Fintype.sum_prod_type]`.

Repeatedly rewrite using `[h1]`. Rewrite using `[prod_ofFn_sum]`. Conclude with `Finset.sum_congr rfl (fun γ _ => prod_ofFn_smul _ _)`. Establish `hdet : ∀ c : Fin n → Fin n, ¬ Function.Injective c → (P.submatrix c id).det = 0`. Introduce `c hc`.

Choose the witnesses or unpack the hypotheses as in `⟨i, j, hij, hne⟩ : ∃ i j, c i = c j ∧ i ≠ j := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hc (fun i j hij => h i j hij)`. Conclude with `Matrix.det_zero_of_row_eq hne (by ext k; simp [hij])`.

Apply the tactic sequence `have hS : ∀ d : Fin n → Fin n, ∑ c : Fin n → Fin n, (P.submatrix c id).det • (List.ofFn fun j : Fin n => capEntry E (x - ((j : ℕ) : ℂ)) (c j) (d j)).prod = P.det • cminor E id d x := by`. Introduce `d`. Rewrite using `[sum_fun_perm _ (fun c hc => by rw [hdet c hc, zero_smul])]`. Unfold `cminor`. Rewrite using `[Finset.smul_sum]`.

Use `Finset.sum_congr rfl (fun τ _ => ?_)` and prove the remaining obligations. Rewrite using `[Matrix.det_permute, mul_comm, mul_smul, ← Int.cast_smul_eq_zsmul ℂ]`. Simplify using `only [id]`. Establish `hQ : ∑ ρ : Equiv.Perm (Fin n), ((Equiv.Perm.sign ρ : ℤˣ) : ℤ) • ∏ j, Q j (ρ j) = Q.det`. Use `coef_det Q id` as an intermediate fact.

Simplify using `using this`. Combine the equalities or inequalities in the displayed calculation. Unfold `capelliC cminor`. Simplify using `only [id]`. Repeatedly rewrite using `[hstep, Finset.smul_sum]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl (fun γ _ => ?_)` and prove the remaining obligations. Rewrite using `[← coef_det P (fun j => (γ j).1), Finset.sum_mul, Finset.sum_smul]`. Use `Finset.sum_congr rfl (fun σ _ => ?_)` and prove the remaining obligations. Rewrite using `[Finset.prod_mul_distrib, smul_mul_assoc, smul_assoc]`.

Apply the tactic sequence `_ = ∑ d : Fin n → Fin n, ∑ c : Fin n → Fin n, ((P.submatrix c id).det * ∏ j, Q j (d j)) • (List.ofFn fun j : Fin n => capEntry E (x - ((j : ℕ) : ℂ)) (c j) (d j)).prod := by`. Set `e : (Fin n → Fin n) × (Fin n → Fin n) ≃ (Fin n → Fin n × Fin n)` to `⟨fun cd j => (cd.1 j, cd.2 j), fun γ => (fun j => (γ j).1, fun j => (γ j).2), fun _ => rfl, fun _ => rfl⟩`. Rewrite using `[← e.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]`. Both sides reduce to the same expression. Use `_ = ∑ d : Fin n → Fin n, (∏ j, Q j (d j)) • (P.det • cminor E id d x) := by`.

Use `Finset.sum_congr rfl (fun d _ => ?_)` and prove the remaining obligations. Rewrite using `[← hS d, Finset.smul_sum]`. Use `Finset.sum_congr rfl (fun c _ => ?_)` and prove the remaining obligations. Rewrite using `[smul_smul, mul_comm]`. Use `_ = ∑ ρ : Equiv.Perm (Fin n), (∏ j, Q j (ρ j)) • (P.det • cminor E id ρ x) := by`.

Apply `sum_fun_perm` to reduce the goal to its premises. Introduce `d hd`. Rewrite using `[cminor_cols_not_inj E hE id d x hd, smul_zero, smul_zero]`. Use `_ = (P.det * Q.det) • capelliC E x := by`. Rewrite using `[← hQ, Finset.mul_sum, Finset.sum_smul]`.

Use `Finset.sum_congr rfl (fun ρ _ => ?_)` and prove the remaining obligations. Establish `hc` using `cminor_perm_cols E hE id id ρ x`. Unfold `capelliC`. Rewrite `hc` using `[show (id : Fin n → Fin n) ∘ ρ = ρ from rfl]`. Rewrite using `[hc, smul_smul, ← Int.cast_smul_eq_zsmul ℂ, smul_smul]`.

Use `congr 1`. Rewrite using `[zsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = capelliC E x := by`. Rewrite using `[← Matrix.det_mul, hPQ, Matrix.det_one, one_smul]`.
-/
theorem capelliC_ad (E : Fin n → Fin n → 𝒰) (hE : GlRelR E) (P Q : Matrix (Fin n) (Fin n) ℂ)
    (hQP : Q * P = 1) (hPQ : P * Q = 1) (x : ℂ) :
    capelliC (fun a b => ∑ c, ∑ d, (P c a * Q b d) • E c d) x = capelliC E x := by
  classical
  have hstep : ∀ σ : Equiv.Perm (Fin n),
      (List.ofFn fun j : Fin n =>
        capEntry (fun a b => ∑ c, ∑ d, (P c a * Q b d) • E c d) (x - ((j : ℕ) : ℂ)) (σ j) j).prod =
        ∑ γ : Fin n → Fin n × Fin n, (∏ j, (P (γ j).1 (σ j) * Q j (γ j).2)) •
          (List.ofFn fun j : Fin n => capEntry E (x - ((j : ℕ) : ℂ)) (γ j).1 (γ j).2).prod := by
    intro σ
    have h1 : ∀ j : Fin n, capEntry (fun a b => ∑ c, ∑ d, (P c a * Q b d) • E c d) (x - ((j : ℕ) : ℂ)) (σ j) j =
        ∑ cd : Fin n × Fin n, (P cd.1 (σ j) * Q j cd.2) • capEntry E (x - ((j : ℕ) : ℂ)) cd.1 cd.2 := by
      intro j
      rw [capEntry_ad E P Q hQP, Fintype.sum_prod_type]
    simp_rw [h1]
    rw [prod_ofFn_sum]
    exact Finset.sum_congr rfl (fun γ _ => prod_ofFn_smul _ _)
  have hdet : ∀ c : Fin n → Fin n, ¬ Function.Injective c → (P.submatrix c id).det = 0 := by
    intro c hc
    obtain ⟨i, j, hij, hne⟩ : ∃ i j, c i = c j ∧ i ≠ j := by
      by_contra h
      push_neg at h
      exact hc (fun i j hij => h i j hij)
    exact Matrix.det_zero_of_row_eq hne (by ext k; simp [hij])
  have hS : ∀ d : Fin n → Fin n,
      ∑ c : Fin n → Fin n, (P.submatrix c id).det •
        (List.ofFn fun j : Fin n => capEntry E (x - ((j : ℕ) : ℂ)) (c j) (d j)).prod =
        P.det • cminor E id d x := by
    intro d
    rw [sum_fun_perm _ (fun c hc => by rw [hdet c hc, zero_smul])]
    unfold cminor
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    rw [Matrix.det_permute, mul_comm, mul_smul, ← Int.cast_smul_eq_zsmul ℂ]
    simp only [id]
  have hQ : ∑ ρ : Equiv.Perm (Fin n), ((Equiv.Perm.sign ρ : ℤˣ) : ℤ) • ∏ j, Q j (ρ j) = Q.det := by
    have := coef_det Q id
    simpa using this
  calc capelliC (fun a b => ∑ c, ∑ d, (P c a * Q b d) • E c d) x
      = ∑ γ : Fin n → Fin n × Fin n,
          ((P.submatrix (fun j => (γ j).1) id).det * ∏ j, Q j (γ j).2) •
          (List.ofFn fun j : Fin n => capEntry E (x - ((j : ℕ) : ℂ)) (γ j).1 (γ j).2).prod := by
        unfold capelliC cminor
        simp only [id]
        simp_rw [hstep, Finset.smul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun γ _ => ?_)
        rw [← coef_det P (fun j => (γ j).1), Finset.sum_mul, Finset.sum_smul]
        refine Finset.sum_congr rfl (fun σ _ => ?_)
        rw [Finset.prod_mul_distrib, smul_mul_assoc, smul_assoc]
    _ = ∑ d : Fin n → Fin n, ∑ c : Fin n → Fin n,
          ((P.submatrix c id).det * ∏ j, Q j (d j)) •
          (List.ofFn fun j : Fin n => capEntry E (x - ((j : ℕ) : ℂ)) (c j) (d j)).prod := by
        let e : (Fin n → Fin n) × (Fin n → Fin n) ≃ (Fin n → Fin n × Fin n) :=
          ⟨fun cd j => (cd.1 j, cd.2 j), fun γ => (fun j => (γ j).1, fun j => (γ j).2),
            fun _ => rfl, fun _ => rfl⟩
        rw [← e.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
        rfl
    _ = ∑ d : Fin n → Fin n, (∏ j, Q j (d j)) • (P.det • cminor E id d x) := by
        refine Finset.sum_congr rfl (fun d _ => ?_)
        rw [← hS d, Finset.smul_sum]
        refine Finset.sum_congr rfl (fun c _ => ?_)
        rw [smul_smul, mul_comm]
    _ = ∑ ρ : Equiv.Perm (Fin n), (∏ j, Q j (ρ j)) • (P.det • cminor E id ρ x) := by
        apply sum_fun_perm
        intro d hd
        rw [cminor_cols_not_inj E hE id d x hd, smul_zero, smul_zero]
    _ = (P.det * Q.det) • capelliC E x := by
        rw [← hQ, Finset.mul_sum, Finset.sum_smul]
        refine Finset.sum_congr rfl (fun ρ _ => ?_)
        have hc := cminor_perm_cols E hE id id ρ x
        unfold capelliC
        rw [show (id : Fin n → Fin n) ∘ ρ = ρ from rfl] at hc
        rw [hc, smul_smul, ← Int.cast_smul_eq_zsmul ℂ, smul_smul]
        congr 1
        rw [zsmul_eq_mul]
        ring
    _ = capelliC E x := by
        rw [← Matrix.det_mul, hPQ, Matrix.det_one, one_smul]

end ReciprocityTheory.ChartRestriction.DS.S7.CapAd
