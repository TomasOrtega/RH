import Mathlib

namespace GlobalTheory

/- English proof (translation)
Use extensionality with `i j`. Use `set A := e.submatrix τ σ with hAdef`. Set `B : Matrix (Fin r) (Fin 1) K` to `Matrix.of fun k _ => e (τ k) j`. Set `C : Matrix (Fin 1) (Fin r) K` to `Matrix.of fun _ l => e i (σ l)`. Set `D : Matrix (Fin 1) (Fin 1) K` to `Matrix.of fun _ _ => e i j`.

Establish `hM : Matrix.fromBlocks A B C D = e.submatrix (Sum.elim τ fun _ => i) (Sum.elim σ fun _ => j)`. Apply the tactic sequence `ext (a | a) (b | b) <;> rfl`. Establish `h0 : (Matrix.fromBlocks A B C D).det = 0`. Rewrite using `[hM, ← Matrix.det_reindex_self finSumFinEquiv, Matrix.reindex_apply, Matrix.submatrix_submatrix]`. Conclude with `hmax _ _`.

Establish `: Invertible A` using `A.invertibleOfIsUnitDet (isUnit_iff_ne_zero.mpr hA)`. Rewrite `h0` using `[Matrix.det_fromBlocks₁₁, Matrix.det_fin_one, Matrix.invOf_eq_nonsing_inv]`. Establish `h1` using `(mul_eq_zero.mp h0).resolve_left hA`. Rewrite `h1` using `[Matrix.sub_apply, sub_eq_zero]`. Establish `h2 : (C * A⁻¹ * B) 0 0 = (e.submatrix id σ * A⁻¹ * e.submatrix τ id) i j` using `rfl`.

Rewrite using `[← h2, ← h1]`. Both sides reduce to the same expression.
-/
private theorem cur_decomposition_of_maximal_minor {K : Type} [Field K] {d r : ℕ} (e : Matrix (Fin d) (Fin d) K)
    (τ σ : Fin r → Fin d) (hA : (e.submatrix τ σ).det ≠ 0)
    (hmax : ∀ τ' σ' : Fin (r + 1) → Fin d, (e.submatrix τ' σ').det = 0) :
    e.submatrix id σ * (e.submatrix τ σ)⁻¹ * e.submatrix τ id = e := by
  ext i j
  set A := e.submatrix τ σ with hAdef
  let B : Matrix (Fin r) (Fin 1) K := Matrix.of fun k _ => e (τ k) j
  let C : Matrix (Fin 1) (Fin r) K := Matrix.of fun _ l => e i (σ l)
  let D : Matrix (Fin 1) (Fin 1) K := Matrix.of fun _ _ => e i j
  have hM : Matrix.fromBlocks A B C D =
      e.submatrix (Sum.elim τ fun _ => i) (Sum.elim σ fun _ => j) := by
    ext (a | a) (b | b) <;> rfl
  have h0 : (Matrix.fromBlocks A B C D).det = 0 := by
    rw [hM, ← Matrix.det_reindex_self finSumFinEquiv, Matrix.reindex_apply,
      Matrix.submatrix_submatrix]
    exact hmax _ _
  have : Invertible A := A.invertibleOfIsUnitDet (isUnit_iff_ne_zero.mpr hA)
  rw [Matrix.det_fromBlocks₁₁, Matrix.det_fin_one, Matrix.invOf_eq_nonsing_inv] at h0
  have h1 := (mul_eq_zero.mp h0).resolve_left hA
  rw [Matrix.sub_apply, sub_eq_zero] at h1
  have h2 : (C * A⁻¹ * B) 0 0 = (e.submatrix id σ * A⁻¹ * e.submatrix τ id) i j := rfl
  rw [← h2, ← h1]
  rfl

/- English proof (translation)
Rewrite using `[Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]`. Use `congr 1`. Express the relevant statement in the definitionally equal form `(Matrix.mulVec (e.submatrix τ σ).adjugate fun l => e (τ l) j) k = _`. Rewrite using `[← Matrix.cramer_eq_adjugate_mulVec, Matrix.cramer_apply]`. Use `congr 1`.

Use extensionality with `a c`. Distinguish the cases in `h : c = k`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h]`.
-/
private theorem inv_mul_submatrix_apply_eq_det_ratio {K : Type} [Field K] {d r : ℕ}
    (e : Matrix (Fin d) (Fin d) K) (τ σ : Fin r → Fin d) (k : Fin r) (j : Fin d) :
    ((e.submatrix τ σ)⁻¹ * e.submatrix τ id) k j =
      (e.submatrix τ σ).det⁻¹ * (e.submatrix τ (Function.update σ k j)).det := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
  congr 1
  change (Matrix.mulVec (e.submatrix τ σ).adjugate fun l => e (τ l) j) k = _
  rw [← Matrix.cramer_eq_adjugate_mulVec, Matrix.cramer_apply]
  congr 1
  ext a c
  by_cases h : c = k
  · subst h; simp
  · simp [h]

/- English proof (translation)
Set `P : ℕ → Prop` to `fun k => ∃ τ σ : Fin k → Fin d, (e.submatrix τ σ).det ≠ 0`. Use `set r := Nat.findGreatest P d with hr`. Establish `hPr : P r` using `Nat.findGreatest_spec (m := 0) (Nat.zero_le _) ⟨Fin.elim0, Fin.elim0, by simp⟩`. Establish `hnot : ∀ τ σ : Fin (r + 1) → Fin d, (e.submatrix τ σ).det = 0`. Introduce `τ σ`.

Assume the negation of the conclusion as `hne`. Distinguish the cases in `hle : r + 1 ≤ d`. Conclude with `Nat.findGreatest_is_greatest (Nat.lt_succ_self r) hle ⟨τ, σ, hne⟩`. Take `⟨a, b, hab, hτ⟩` from `Fintype.exists_ne_map_eq_of_card_lt τ (by simp; omega)`. Conclude with `hne (Matrix.det_zero_of_row_eq hab (by funext c; simp [hτ]))`.

Set `v` to `O.valuation`. Take `⟨τ0, σ0, h0⟩` from `hPr`. Take `⟨p, -, hp⟩` from `Finset.exists_max_image Finset.univ (fun p : (Fin r → Fin d) × (Fin r → Fin d) => v (e.submatrix p.1 p.2).det) ⟨(τ0, σ0), Finset.mem_univ _⟩`. Take `⟨τ, σ⟩` from `p`. Establish `hA : (e.submatrix τ σ).det ≠ 0`.

Introduce `hz`. Establish `hle` using `hp (τ0, σ0) (Finset.mem_univ _)`. Simplify using `only [hz, map_zero] at hle`. Conclude with `h0 ((Valuation.zero_iff _).mp (le_antisymm hle zero_le))`. Establish `hv : v (e.submatrix τ σ).det ≠ 0` using `(Valuation.ne_zero_iff _).mpr hA`.

Set `S : Matrix (Fin d) (Fin r) K` to `Matrix.of fun i k => if i = σ k then 1 else 0`. Establish `hS : ∀ {m : Type} [Fintype m] (M : Matrix m (Fin d) K), M * S = M.submatrix id σ`. Introduce `m _ M`. Use extensionality with `a k`. Simplify using `[S, Matrix.mul_apply]`.

Use `⟨r, (e.submatrix τ σ)⁻¹ * e.submatrix τ id, S, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `k j`. Rewrite using `[inv_mul_submatrix_apply_eq_det_ratio, ← O.valuation_le_one_iff, map_mul, map_inv₀]`. Establish `hle` using `hp (τ, Function.update σ k j) (Finset.mem_univ _)`. Combine the equalities or inequalities in the displayed calculation.

Introduce `i k`. Simplify using `only [S, Matrix.of_apply]`. Use `split_ifs`. Conclude with `O.one_mem`. Conclude with `O.zero_mem`.

Rewrite using `[Matrix.mul_assoc, hS]`. Conclude with `Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hA)`. Rewrite using `[Matrix.mul_assoc]`. Use `congr 1`. Use extensionality with `a c`.

Express the relevant statement in the definitionally equal form `(e * e) (τ a) c = e (τ a) c`. Rewrite using `[he]`. Rewrite using `[hS, ← Matrix.mul_assoc]`. Conclude with `cur_decomposition_of_maximal_minor e τ σ hA hnot`.
-/
theorem exists_integral_factor_of_idempotent {K : Type} [Field K] (O : ValuationSubring K) (d : ℕ)
    (e : Matrix (Fin d) (Fin d) K) (he : e * e = e) :
    ∃ (r : ℕ) (R : Matrix (Fin r) (Fin d) K) (S : Matrix (Fin d) (Fin r) K),
      (∀ i j, R i j ∈ O) ∧ (∀ i j, S i j ∈ O) ∧ R * S = 1 ∧ R * e = R ∧ e * S * R = e := by
  classical
  let P : ℕ → Prop := fun k => ∃ τ σ : Fin k → Fin d, (e.submatrix τ σ).det ≠ 0
  set r := Nat.findGreatest P d with hr
  have hPr : P r := Nat.findGreatest_spec (m := 0) (Nat.zero_le _) ⟨Fin.elim0, Fin.elim0, by simp⟩
  have hnot : ∀ τ σ : Fin (r + 1) → Fin d, (e.submatrix τ σ).det = 0 := by
    intro τ σ
    by_contra hne
    by_cases hle : r + 1 ≤ d
    · exact Nat.findGreatest_is_greatest (Nat.lt_succ_self r) hle ⟨τ, σ, hne⟩
    · obtain ⟨a, b, hab, hτ⟩ := Fintype.exists_ne_map_eq_of_card_lt τ (by simp; omega)
      exact hne (Matrix.det_zero_of_row_eq hab (by funext c; simp [hτ]))
  let v := O.valuation
  obtain ⟨τ0, σ0, h0⟩ := hPr
  obtain ⟨p, -, hp⟩ := Finset.exists_max_image Finset.univ
    (fun p : (Fin r → Fin d) × (Fin r → Fin d) => v (e.submatrix p.1 p.2).det)
    ⟨(τ0, σ0), Finset.mem_univ _⟩
  obtain ⟨τ, σ⟩ := p
  have hA : (e.submatrix τ σ).det ≠ 0 := by
    intro hz
    have hle := hp (τ0, σ0) (Finset.mem_univ _)
    simp only [hz, map_zero] at hle
    exact h0 ((Valuation.zero_iff _).mp (le_antisymm hle zero_le))
  have hv : v (e.submatrix τ σ).det ≠ 0 := (Valuation.ne_zero_iff _).mpr hA
  let S : Matrix (Fin d) (Fin r) K := Matrix.of fun i k => if i = σ k then 1 else 0
  have hS : ∀ {m : Type} [Fintype m] (M : Matrix m (Fin d) K), M * S = M.submatrix id σ := by
    intro m _ M
    ext a k
    simp [S, Matrix.mul_apply]
  refine ⟨r, (e.submatrix τ σ)⁻¹ * e.submatrix τ id, S, ?_, ?_, ?_, ?_, ?_⟩
  · intro k j
    rw [inv_mul_submatrix_apply_eq_det_ratio, ← O.valuation_le_one_iff, map_mul, map_inv₀]
    have hle := hp (τ, Function.update σ k j) (Finset.mem_univ _)
    calc (v (e.submatrix τ σ).det)⁻¹ * v (e.submatrix τ (Function.update σ k j)).det
        ≤ (v (e.submatrix τ σ).det)⁻¹ * v (e.submatrix τ σ).det := mul_le_mul_right hle _
      _ = 1 := inv_mul_cancel₀ hv
  · intro i k
    simp only [S, Matrix.of_apply]
    split_ifs
    · exact O.one_mem
    · exact O.zero_mem
  · rw [Matrix.mul_assoc, hS]
    exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hA)
  · rw [Matrix.mul_assoc]
    congr 1
    ext a c
    change (e * e) (τ a) c = e (τ a) c
    rw [he]
  · rw [hS, ← Matrix.mul_assoc]
    exact cur_decomposition_of_maximal_minor e τ σ hA hnot

/- English proof (translation)
Take `⟨e', rfl⟩ : ∃ e' : Matrix (Fin d) (Fin d) F, e'.map F.subtype = e` from `⟨Matrix.of fun i j => ⟨e i j, hF i j⟩, by ext; rfl⟩`. Set `O : ValuationSubring F` to `{ carrier := {x | ‖(x : C)‖ ≤ 1} mul_mem' := fun {a b} ha hb => by`. Simplify using `only [Set.mem_ofPred_eq, Subfield.coe_mul, norm_mul] at *`. Combine the equalities or inequalities in the displayed calculation. Use the proof step `one_mem' := by simp`.

Use the proof step `add_mem' := fun {a b} ha hb => by`. Simplify using `only [Set.mem_ofPred_eq, Subfield.coe_add] at *`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)`. Use the proof step `zero_mem' := by simp`. Use the proof step `neg_mem' := fun {a} ha => by simpa using ha`.

Use the proof step `mem_or_inv_mem' := fun x => by`. Break down `le_or_gt ‖(x : C)‖ 1 with h | h` into its components or cases. Conclude with `Or.inl h`. Use `right`. Express the relevant statement in the definitionally equal form `‖((x⁻¹ : F) : C)‖ ≤ 1`.

Rewrite using `[Subfield.coe_inv, norm_inv]`. Conclude with `inv_le_one_of_one_le₀ h.le }`. Establish `hinj : Function.Injective (F.subtype : F → C)` using `Subtype.val_injective`. Establish `he' : e' * e' = e'` using `Matrix.map_injective hinj (by`. Express the relevant statement in the definitionally equal form `(e' * e').map F.subtype = e'.map F.subtype`.

Rewrite using `[Matrix.map_mul, he])`. Take `⟨r, R, S, hR, hS, hRS, hRe, heSR⟩` from `exists_integral_factor_of_idempotent O d e' he'`. Use `⟨r, R.map F.subtype, S.map F.subtype, fun i j => ⟨(R i j).2, hR i j⟩, fun i j => ⟨(S i j).2, hS i j⟩, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← Matrix.map_mul, hRS, Matrix.map_one _ (map_zero _) (map_one _)]`. Rewrite using `[← Matrix.map_mul, hRe]`.

Rewrite using `[← Matrix.map_mul, ← Matrix.map_mul, heSR]`.
-/
theorem exists_integral_factor_of_idempotent_subfield (C : Type) [NormedField C]
    [IsUltrametricDist C] (F : Subfield C) (d : ℕ) (e : Matrix (Fin d) (Fin d) C)
    (hF : ∀ i j, e i j ∈ F) (he : e * e = e) :
    ∃ (r : ℕ) (R : Matrix (Fin r) (Fin d) C) (S : Matrix (Fin d) (Fin r) C),
      (∀ i j, R i j ∈ F ∧ ‖R i j‖ ≤ 1) ∧ (∀ i j, S i j ∈ F ∧ ‖S i j‖ ≤ 1) ∧
        R * S = 1 ∧ R * e = R ∧ e * S * R = e := by
  obtain ⟨e', rfl⟩ : ∃ e' : Matrix (Fin d) (Fin d) F, e'.map F.subtype = e :=
    ⟨Matrix.of fun i j => ⟨e i j, hF i j⟩, by ext; rfl⟩
  let O : ValuationSubring F :=
    { carrier := {x | ‖(x : C)‖ ≤ 1}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, Subfield.coe_mul, norm_mul] at *
        calc ‖(a : C)‖ * ‖(b : C)‖ ≤ 1 * 1 := mul_le_mul ha hb (norm_nonneg _) zero_le_one
          _ = 1 := one_mul 1
      one_mem' := by simp
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, Subfield.coe_add] at *
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
      zero_mem' := by simp
      neg_mem' := fun {a} ha => by simpa using ha
      mem_or_inv_mem' := fun x => by
        rcases le_or_gt ‖(x : C)‖ 1 with h | h
        · exact Or.inl h
        · right
          change ‖((x⁻¹ : F) : C)‖ ≤ 1
          rw [Subfield.coe_inv, norm_inv]
          exact inv_le_one_of_one_le₀ h.le }
  have hinj : Function.Injective (F.subtype : F → C) := Subtype.val_injective
  have he' : e' * e' = e' := Matrix.map_injective hinj (by
    change (e' * e').map F.subtype = e'.map F.subtype
    rw [Matrix.map_mul, he])
  obtain ⟨r, R, S, hR, hS, hRS, hRe, heSR⟩ := exists_integral_factor_of_idempotent O d e' he'
  refine ⟨r, R.map F.subtype, S.map F.subtype, fun i j => ⟨(R i j).2, hR i j⟩,
    fun i j => ⟨(S i j).2, hS i j⟩, ?_, ?_, ?_⟩
  · rw [← Matrix.map_mul, hRS, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [← Matrix.map_mul, hRe]
  · rw [← Matrix.map_mul, ← Matrix.map_mul, heSR]

end GlobalTheory
