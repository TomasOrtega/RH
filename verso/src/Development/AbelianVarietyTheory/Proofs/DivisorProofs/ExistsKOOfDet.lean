import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwasawaBlockTriangular

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.FunObj

namespace GlobalTheory.FunObj.DiagLattice

/- English proof (translation)
Set `A : Matrix ι ι 𝒪[k]` to `fun i j => ⟨M i j, h1 i j⟩`. Establish `hA : (algebraMap 𝒪[k] k).mapMatrix A = M` using `rfl`. Establish `hd : algebraMap 𝒪[k] k A.det = M.det` using `by rw [RingHom.map_det, hA]`. Establish `hu : IsUnit A.det` using `(Valuation.Integers.isUnit_iff_valuation_eq_one (Valuation.integer.integers (valuation k))).2 (by rw [hd, h2])`. Take `⟨u, hu⟩` from `(Matrix.isUnit_iff_isUnit_det A).2 hu`.

Use `⟨Matrix.GeneralLinearGroup.map (n := ι) (algebraMap 𝒪[k] k) u, ⟨u, rfl⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `u.val.map (algebraMap 𝒪[k] k) = _`. Rewrite using `[hu]`. Both sides reduce to the same expression.
-/
theorem exists_KO_of_det {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι k)
    (h1 : ∀ i j, M i j ∈ 𝒪[k]) (h2 : valuation k M.det = 1) : ∃ g ∈ KO k ι, g.val = M := by
  let A : Matrix ι ι 𝒪[k] := fun i j => ⟨M i j, h1 i j⟩
  have hA : (algebraMap 𝒪[k] k).mapMatrix A = M := rfl
  have hd : algebraMap 𝒪[k] k A.det = M.det := by rw [RingHom.map_det, hA]
  have hu : IsUnit A.det :=
    (Valuation.Integers.isUnit_iff_valuation_eq_one (Valuation.integer.integers (valuation k))).2 (by rw [hd, h2])
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det A).2 hu
  refine ⟨Matrix.GeneralLinearGroup.map (n := ι) (algebraMap 𝒪[k] k) u, ⟨u, rfl⟩, ?_⟩
  change u.val.map (algebraMap 𝒪[k] k) = _
  rw [hu]; rfl

/- English proof (translation)
Use `⟨(Model.mkNel p fun rs => Sum.elim (fun _ => (0 : k)) (fun i => v i rs.1.1) rs.1.2).1, Subtype.property _, ?_, ?_⟩` and prove the remaining obligations. Introduce `r i show Model.mkN p (fun rs => Sum.elim (fun _ => (0 : k)) (fun i => v i rs.1.1) rs.1.2) r (Sum.inr i) = _`. Simplify using `only [Model.mkN, of_apply, Sum.elim_inr]`. Use `split_ifs with h`. Both sides reduce to the same expression.

Break down `r with r | r` into its components or cases. Rewrite using `[h3 i (by simp [lev] at h; omega)]; simp`. Simplify using `only [lev, Sum.elim_inr] at h`. Break down `eq_or_lt_of_le (show i ≤ r by rw [Fin.le_def]; omega) with e | e` into its components or cases. Substitute `e` using the available equality.

Simplify using `[h1]`. Rewrite using `[h2 i r e, Matrix.one_apply_ne]`. Simplify using `using e.ne'`. Introduce `r s show Model.mkN p (fun rs => Sum.elim (fun _ => (0 : k)) (fun i => v i rs.1.1) rs.1.2) r (Sum.inl s) = _`. Simplify using `only [Model.mkN, of_apply, Sum.elim_inl]`.

Use `split_ifs with h`. Rewrite using `[Matrix.one_apply_ne]`. Introduce and unpack `rfl`. Conclude with `lt_irrefl _ h`. Both sides reduce to the same expression.
-/
theorem exists_unip {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} (p : ℕ)
    (v : Fin c → n ⊕ Fin c → k) (h1 : ∀ i, v i (Sum.inr i) = 1) (h2 : ∀ i l, i < l → v i (Sum.inr l) = 0)
    (h3 : ∀ i : Fin c, i.val < p → ∀ r, v i (Sum.inl r) = 0) :
    ∃ u ∈ N k n c p, (∀ r i, u.val r (Sum.inr i) = v i r) ∧
      ∀ r s, u.val r (Sum.inl s) = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r (Sum.inl s) := by
  refine ⟨(Model.mkNel p fun rs => Sum.elim (fun _ => (0 : k)) (fun i => v i rs.1.1) rs.1.2).1,
    Subtype.property _, ?_, ?_⟩
  · intro r i
    show Model.mkN p (fun rs => Sum.elim (fun _ => (0 : k)) (fun i => v i rs.1.1) rs.1.2) r (Sum.inr i) = _
    simp only [Model.mkN, of_apply, Sum.elim_inr]
    split_ifs with h
    · rfl
    · rcases r with r | r
      · rw [h3 i (by simp [lev] at h; omega)]; simp
      · simp only [lev, Sum.elim_inr] at h
        rcases eq_or_lt_of_le (show i ≤ r by rw [Fin.le_def]; omega) with e | e
        · subst e; simp [h1]
        · rw [h2 i r e, Matrix.one_apply_ne]
          simpa using e.ne'
  · intro r s
    show Model.mkN p (fun rs => Sum.elim (fun _ => (0 : k)) (fun i => v i rs.1.1) rs.1.2) r (Sum.inl s) = _
    simp only [Model.mkN, of_apply, Sum.elim_inl]
    split_ifs with h
    · rw [Matrix.one_apply_ne]
      rintro rfl; exact lt_irrefl _ h
    · rfl

/- English proof (translation)
Introduce `k _ _ _ _ n _ _ c d H hA hB`. Use `choose v v1 v2 v3 v4 using hA`. Take `⟨u, hu, uc, uX⟩` from `exists_unip ((c + 1) / 2) v v1 v2 v3`. Set `lv : n ⊕ Fin c → ℕ` to `Sum.elim (fun _ => 2 * (c / 2)) (fun i => 2 * i.val + 1)`. Take `⟨b, hb, w, hw, hbw⟩` from `iwasawa_blockTriangular k (n ⊕ Fin c) lv (u⁻¹ * H)`.

Establish `hbi : (b⁻¹).val.BlockTriangular lv`. Rewrite using `[Matrix.coe_units_inv]`. Use `haveI := b.invertible`. Conclude with `Matrix.blockTriangular_inv_of_blockTriangular hb`. Establish `hH : H = u * b * w` using `by rw [mul_assoc, ← hbw]; simp`.

Take `⟨w1, w2⟩` from `(mem_KO_iff w).1 hw`. Establish `hdiag : ∀ i, (b⁻¹).val (Sum.inr i) (Sum.inr i) * b.val (Sum.inr i) (Sum.inr i) = 1`. Introduce `i`. Establish `h` using `congrFun (congrFun b.inv_mul (Sum.inr i)) (Sum.inr i)`. Rewrite `h` using `[Matrix.mul_apply, Finset.sum_eq_single (Sum.inr i)]`.

Simplify using `using h`. Introduce `t _ ht`. Break down `lt_trichotomy (lv t) (lv (Sum.inr i)) with e | e | e` into its components or cases. Rewrite using `[hbi e, zero_mul]`. It suffices to derive a contradiction.

Break down `t with t | t` into its components or cases. Simplify using `only [lv, Sum.elim_inl, Sum.elim_inr] at e`. Use linear arithmetic over natural numbers and integers. Simplify using `only [lv, Sum.elim_inr] at e; exact ht (congrArg _ (Fin.ext (by omega)))`. Rewrite using `[hb e, mul_zero]`.

Simplify using the standard rewrite rules. Establish `hbl : ∀ i l : Fin c, i < l → b.val (Sum.inr l) (Sum.inr i) = 0` using `fun i l h => hb (by simp only [lv, Sum.elim_inr]; rw [Fin.lt_def] at h; omega)`. Establish `h3 : ∀ i, valuation k (b.val (Sum.inr i) (Sum.inr i)) ≤ valuation k (d i : k)`. Introduce `i`. Establish `key : ∀ t, (H.val *ᵥ fun s => (w⁻¹).val s (Sum.inr i)) t = ∑ s, u.val t (Sum.inl s) * b.val (Sum.inl s) (Sum.inr i) + ∑ l, v l t * b.val (Sum.inr l) (Sum.inr i)`.

Introduce `t`. Establish `: (H * w⁻¹).val t (Sum.inr i) = (u * b).val t (Sum.inr i)` using `by rw [hH]; simp`. Rewrite `this` using `[Units.val_mul, Units.val_mul, Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_sum_type (fun j => u.val t j * b.val j (Sum.inr i))]`. Simplify using `only [uc] at this`. Conclude with `this`.

Establish `h` using `hB i (fun s => (w⁻¹).val s (Sum.inr i)) (fun t => w2 _ _) ?_ ?_`. Rewrite `h` using `[key, Finset.sum_eq_single i]`. Simplify `h` using `[uX, v1]`. Introduce `l _ hl`. Break down `lt_or_gt_of_ne hl with e | e` into its components or cases.

Rewrite using `[v2 l i e, zero_mul]`. Rewrite using `[hbl i l e, mul_zero]`. Simplify using the standard rewrite rules. Introduce `l hl`. Rewrite using `[key, Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero]`.

Introduce `m _`. Break down `lt_or_ge m l with e | e` into its components or cases. Rewrite using `[v2 m l e, zero_mul]`. Rewrite using `[hbl i m (hl.trans_le e), mul_zero]`. Introduce `s _`.

Simplify using `[uX]`. Introduce `hi r`. Rewrite using `[key, Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero]`. Introduce `m _`. Break down `lt_or_ge i m with e | e` into its components or cases.

Rewrite using `[hbl i m e, mul_zero]`. Rewrite using `[v3 m (by rw [Fin.le_def] at e; omega), zero_mul]`. Introduce `s _`. Rewrite using `[hb (show lv (Sum.inr i) < lv (Sum.inl s) by simp only [lv, Sum.elim_inr, Sum.elim_inl]; omega), mul_zero]`. Establish `h4 : ∀ t i, (b⁻¹).val t (Sum.inr i) * (d i : k) ∈ 𝒪[k]`.

Introduce `t i`. Establish `e : b⁻¹ = w * H⁻¹ * u` using `by rw [hH]; group`. Establish `: (b⁻¹).val t (Sum.inr i) * (d i : k) = (w.val *ᵥ ((H⁻¹).val *ᵥ ((d i : k) • v i))) t`. Rewrite using `[Matrix.mulVec_mulVec, e, Units.val_mul, Units.val_mul, Matrix.mul_apply, Finset.sum_mul]`. Simplify using `only [Matrix.mulVec, dotProduct, uc, Pi.smul_apply, smul_eq_mul]`.

Conclude with `Finset.sum_congr rfl fun j _ => by ring`. Rewrite using `[this]`. Conclude with `sum_mem fun j _ => mul_mem (w1 _ _) (v4 i j)`. Set `A : Matrix (Fin c) (Fin c) k` to `Matrix.of fun l i => (b⁻¹).val (Sum.inr l) (Sum.inr i) * d i`. Set `β : Matrix n (Fin c) k` to `Matrix.of fun r i => (b⁻¹).val (Sum.inl r) (Sum.inr i) * d i`.

Establish `hAtri : A.BlockTriangular id` using `fun l i h => by`. Simplify using `only [A, of_apply]`. Rewrite using `[hbi (by simp only [lv, Sum.elim_inr]; rw [id, id, Fin.lt_def] at h; omega), zero_mul]`. Take `⟨κ, hκ, hκv⟩` from `exists_KO_of_det (fromBlocks 1 β 0 A) (by`. Introduce and unpack `(r | r) (s | s)`.

Apply the tactic sequence `simp only [fromBlocks_apply₁₁, Matrix.one_apply]; split_ifs <;> simp`. Conclude with `h4 _ _`. Conclude with `zero_mem _`. Conclude with `h4 _ _) (by`. Rewrite using `[det_fromBlocks_zero₂₁, det_one, one_mul, det_of_upperTriangular hAtri, map_prod]`.

Use `Finset.prod_eq_one fun i _ => le_antisymm (h4 (Sum.inr i) i) ?_` and prove the remaining obligations. Simplify using `only [A, of_apply, map_mul]`. Combine the equalities or inequalities in the displayed calculation. Establish `hB : (b * κ).val = fromBlocks b.val.toBlocks₁₁ 0 b.val.toBlocks₂₁ (diagonal fun i => (d i : k))`. Establish `col : ∀ t i, (b * κ).val t (Sum.inr i) = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) t (Sum.inr i) * d i`.

Introduce `t i`. Rewrite using `[← b.mul_inv, Units.val_mul, hκv, Matrix.mul_apply, Matrix.mul_apply, Finset.sum_mul]`. Use `Finset.sum_congr rfl ?_` and prove the remaining obligations. Apply the tactic sequence `rintro (j | j) _ <;> simp [A, β, mul_assoc]`. Use extensionality with `(r | r) (s | s)`.

Simplify using `[hκv, Matrix.mul_apply, Matrix.one_apply, toBlocks₁₁]`. Rewrite using `[col]`. Simplify using the standard rewrite rules. Simplify using `[hκv, Matrix.mul_apply, Matrix.one_apply, toBlocks₂₁]`. Rewrite using `[col]`.

Distinguish the cases in `h : r = s`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h]`. Establish `hg : b.val.toBlocks₁₁.det ≠ 0`.

Use `Matrix.GeneralLinearGroup.det_ne_zero (b * κ)` as an intermediate fact. Rewrite `this` using `[hB, det_fromBlocks_zero₁₂]`. Conclude with `left_ne_zero_of_mul this`. Set `g : GL n k` to `Matrix.GeneralLinearGroup.mkOfDetNeZero _ hg`. Establish `hlow : lowU b.val.toBlocks₂₁ ∈ N k n c (c / 2 + 1)`.

Rewrite using `[Model.mem_N_iff]`. Introduce and unpack `(r | r) (s | s) h`. Simplify using `[lowU, Matrix.one_apply]`. Simplify using `[lowU]`. Simplify using `only [lev, Sum.elim_inl, Sum.elim_inr] at h`.

Simplify using `only [lowU, fromBlocks_apply₂₁, toBlocks₂₁, of_apply]`. Rewrite using `[hb (show lv (Sum.inl s) < lv (Sum.inr r) by simp only [lv, Sum.elim_inr, Sum.elim_inl]; omega)]`. Simplify using the standard rewrite rules. Simplify using `[lowU, Matrix.one_apply]`. Establish `hfac : b * κ = embX c g * lowU b.val.toBlocks₂₁ * diagGL (Sum.elim (fun _ => 1) d)`.

Use `Units.ext ?_` and prove the remaining obligations. Establish `hD : (diagGL (Sum.elim (fun _ : n => (1 : kˣ)) d)).val = fromBlocks 1 0 0 (diagonal fun i => (d i : k))`. Rewrite using `[diagGL_val, ← diagonal_one, fromBlocks_diagonal]`. Use `congr 1`. Apply the tactic sequence `funext x; rcases x with x | x <;> simp`.

Rewrite using `[hB, Units.val_mul, Units.val_mul, hD]`. Use `show _ = fromBlocks b.val.toBlocks₁₁ 0 0 1 * fromBlocks 1 0 b.val.toBlocks₂₁ 1 * _`. Simplify using `[fromBlocks_multiply]`. Use `⟨u * (embX c g * lowU b.val.toBlocks₂₁), ?_, κ⁻¹ * w, mul_mem (inv_mem hκ) hw, ?_⟩` and prove the remaining obligations. Conclude with `mul_mem (Subgroup.mem_sup_right (Subgroup.mem_sup_left hu)) (mul_mem (Subgroup.mem_sup_left ⟨g, rfl⟩) (Subgroup.mem_sup_right (Subgroup.mem_sup_right hlow)))`.

Rewrite using `[mul_assoc u, ← hfac, hH]`. Use `group`.
-/
theorem exists_symR_diag : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) (d : Fin c → kˣ) (H : GL (n ⊕ Fin c) k),
  (∀ i : Fin c, ∃ v : n ⊕ Fin c → k, v (Sum.inr i) = 1 ∧ (∀ l : Fin c, i < l → v (Sum.inr l) = 0) ∧ (i.val < (c + 1) / 2 → ∀ r, v (Sum.inl r) = 0) ∧ ∀ t, ((H⁻¹).val *ᵥ ((d i : k) • v)) t ∈ 𝒪[k]) →
  (∀ (i : Fin c) (y : n ⊕ Fin c → k), (∀ t, y t ∈ 𝒪[k]) → (∀ l : Fin c, i < l → (H.val *ᵥ y) (Sum.inr l) = 0) → (i.val < c / 2 → ∀ r, (H.val *ᵥ y) (Sum.inl r) = 0) → valuation k ((H.val *ᵥ y) (Sum.inr i)) ≤ valuation k (d i : k)) →
  ∃ r ∈ symR k n c, ∃ w ∈ KO k (n ⊕ Fin c), H = r * diagGL (Sum.elim (fun _ => 1) d) * w := by
  intro k _ _ _ _ n _ _ c d H hA hB
  choose v v1 v2 v3 v4 using hA
  obtain ⟨u, hu, uc, uX⟩ := exists_unip ((c + 1) / 2) v v1 v2 v3
  let lv : n ⊕ Fin c → ℕ := Sum.elim (fun _ => 2 * (c / 2)) (fun i => 2 * i.val + 1)
  obtain ⟨b, hb, w, hw, hbw⟩ := iwasawa_blockTriangular k (n ⊕ Fin c) lv (u⁻¹ * H)
  have hbi : (b⁻¹).val.BlockTriangular lv := by
    rw [Matrix.coe_units_inv]
    haveI := b.invertible
    exact Matrix.blockTriangular_inv_of_blockTriangular hb
  have hH : H = u * b * w := by rw [mul_assoc, ← hbw]; simp
  obtain ⟨w1, w2⟩ := (mem_KO_iff w).1 hw
  have hdiag : ∀ i, (b⁻¹).val (Sum.inr i) (Sum.inr i) * b.val (Sum.inr i) (Sum.inr i) = 1 := by
    intro i
    have h := congrFun (congrFun b.inv_mul (Sum.inr i)) (Sum.inr i)
    rw [Matrix.mul_apply, Finset.sum_eq_single (Sum.inr i)] at h
    · simpa using h
    · intro t _ ht
      rcases lt_trichotomy (lv t) (lv (Sum.inr i)) with e | e | e
      · rw [hbi e, zero_mul]
      · exfalso
        rcases t with t | t
        · simp only [lv, Sum.elim_inl, Sum.elim_inr] at e; omega
        · simp only [lv, Sum.elim_inr] at e; exact ht (congrArg _ (Fin.ext (by omega)))
      · rw [hb e, mul_zero]
    · simp
  have hbl : ∀ i l : Fin c, i < l → b.val (Sum.inr l) (Sum.inr i) = 0 := fun i l h =>
    hb (by simp only [lv, Sum.elim_inr]; rw [Fin.lt_def] at h; omega)
  have h3 : ∀ i, valuation k (b.val (Sum.inr i) (Sum.inr i)) ≤ valuation k (d i : k) := by
    intro i
    have key : ∀ t, (H.val *ᵥ fun s => (w⁻¹).val s (Sum.inr i)) t =
        ∑ s, u.val t (Sum.inl s) * b.val (Sum.inl s) (Sum.inr i) + ∑ l, v l t * b.val (Sum.inr l) (Sum.inr i) := by
      intro t
      have : (H * w⁻¹).val t (Sum.inr i) = (u * b).val t (Sum.inr i) := by rw [hH]; simp
      rw [Units.val_mul, Units.val_mul, Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_sum_type
        (fun j => u.val t j * b.val j (Sum.inr i))] at this
      simp only [uc] at this
      exact this
    have h := hB i (fun s => (w⁻¹).val s (Sum.inr i)) (fun t => w2 _ _) ?_ ?_
    · rw [key, Finset.sum_eq_single i] at h
      · simpa [uX, v1] using h
      · intro l _ hl
        rcases lt_or_gt_of_ne hl with e | e
        · rw [v2 l i e, zero_mul]
        · rw [hbl i l e, mul_zero]
      · simp
    · intro l hl
      rw [key, Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero]
      · intro m _
        rcases lt_or_ge m l with e | e
        · rw [v2 m l e, zero_mul]
        · rw [hbl i m (hl.trans_le e), mul_zero]
      · intro s _; simp [uX]
    · intro hi r
      rw [key, Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero]
      · intro m _
        rcases lt_or_ge i m with e | e
        · rw [hbl i m e, mul_zero]
        · rw [v3 m (by rw [Fin.le_def] at e; omega), zero_mul]
      · intro s _
        rw [hb (show lv (Sum.inr i) < lv (Sum.inl s) by simp only [lv, Sum.elim_inr, Sum.elim_inl]; omega), mul_zero]
  have h4 : ∀ t i, (b⁻¹).val t (Sum.inr i) * (d i : k) ∈ 𝒪[k] := by
    intro t i
    have e : b⁻¹ = w * H⁻¹ * u := by rw [hH]; group
    have : (b⁻¹).val t (Sum.inr i) * (d i : k) = (w.val *ᵥ ((H⁻¹).val *ᵥ ((d i : k) • v i))) t := by
      rw [Matrix.mulVec_mulVec, e, Units.val_mul, Units.val_mul, Matrix.mul_apply, Finset.sum_mul]
      simp only [Matrix.mulVec, dotProduct, uc, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [this]
    exact sum_mem fun j _ => mul_mem (w1 _ _) (v4 i j)
  let A : Matrix (Fin c) (Fin c) k := Matrix.of fun l i => (b⁻¹).val (Sum.inr l) (Sum.inr i) * d i
  let β : Matrix n (Fin c) k := Matrix.of fun r i => (b⁻¹).val (Sum.inl r) (Sum.inr i) * d i
  have hAtri : A.BlockTriangular id := fun l i h => by
    simp only [A, of_apply]
    rw [hbi (by simp only [lv, Sum.elim_inr]; rw [id, id, Fin.lt_def] at h; omega), zero_mul]
  obtain ⟨κ, hκ, hκv⟩ := exists_KO_of_det (fromBlocks 1 β 0 A) (by
    rintro (r | r) (s | s)
    · simp only [fromBlocks_apply₁₁, Matrix.one_apply]; split_ifs <;> simp
    · exact h4 _ _
    · exact zero_mem _
    · exact h4 _ _) (by
    rw [det_fromBlocks_zero₂₁, det_one, one_mul, det_of_upperTriangular hAtri, map_prod]
    refine Finset.prod_eq_one fun i _ => le_antisymm (h4 (Sum.inr i) i) ?_
    simp only [A, of_apply, map_mul]
    calc (1 : ValueGroupWithZero k) = valuation k ((b⁻¹).val (Sum.inr i) (Sum.inr i)) *
          valuation k (b.val (Sum.inr i) (Sum.inr i)) := by rw [← map_mul, hdiag, map_one]
      _ ≤ _ := mul_le_mul_right (h3 i) _)
  have hB : (b * κ).val = fromBlocks b.val.toBlocks₁₁ 0 b.val.toBlocks₂₁ (diagonal fun i => (d i : k)) := by
    have col : ∀ t i, (b * κ).val t (Sum.inr i) = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) t (Sum.inr i) * d i := by
      intro t i
      rw [← b.mul_inv, Units.val_mul, hκv, Matrix.mul_apply, Matrix.mul_apply, Finset.sum_mul]
      refine Finset.sum_congr rfl ?_
      rintro (j | j) _ <;> simp [A, β, mul_assoc]
    ext (r | r) (s | s)
    · simp [hκv, Matrix.mul_apply, Matrix.one_apply, toBlocks₁₁]
    · rw [col]; simp
    · simp [hκv, Matrix.mul_apply, Matrix.one_apply, toBlocks₂₁]
    · rw [col]
      by_cases h : r = s
      · subst h; simp
      · simp [h]
  have hg : b.val.toBlocks₁₁.det ≠ 0 := by
    have := Matrix.GeneralLinearGroup.det_ne_zero (b * κ)
    rw [hB, det_fromBlocks_zero₁₂] at this
    exact left_ne_zero_of_mul this
  let g : GL n k := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hg
  have hlow : lowU b.val.toBlocks₂₁ ∈ N k n c (c / 2 + 1) := by
    rw [Model.mem_N_iff]
    rintro (r | r) (s | s) h
    · simp [lowU, Matrix.one_apply]
    · simp [lowU]
    · simp only [lev, Sum.elim_inl, Sum.elim_inr] at h
      simp only [lowU, fromBlocks_apply₂₁, toBlocks₂₁, of_apply]
      rw [hb (show lv (Sum.inl s) < lv (Sum.inr r) by simp only [lv, Sum.elim_inr, Sum.elim_inl]; omega)]
      simp
    · simp [lowU, Matrix.one_apply]
  have hfac : b * κ = embX c g * lowU b.val.toBlocks₂₁ * diagGL (Sum.elim (fun _ => 1) d) := by
    refine Units.ext ?_
    have hD : (diagGL (Sum.elim (fun _ : n => (1 : kˣ)) d)).val = fromBlocks 1 0 0 (diagonal fun i => (d i : k)) := by
      rw [diagGL_val, ← diagonal_one, fromBlocks_diagonal]
      congr 1
      funext x; rcases x with x | x <;> simp
    rw [hB, Units.val_mul, Units.val_mul, hD]
    show _ = fromBlocks b.val.toBlocks₁₁ 0 0 1 * fromBlocks 1 0 b.val.toBlocks₂₁ 1 * _
    simp [fromBlocks_multiply]
  refine ⟨u * (embX c g * lowU b.val.toBlocks₂₁), ?_, κ⁻¹ * w, mul_mem (inv_mem hκ) hw, ?_⟩
  · exact mul_mem (Subgroup.mem_sup_right (Subgroup.mem_sup_left hu))
      (mul_mem (Subgroup.mem_sup_left ⟨g, rfl⟩) (Subgroup.mem_sup_right (Subgroup.mem_sup_right hlow)))
  · rw [mul_assoc u, ← hfac, hH]; group

end GlobalTheory.FunObj.DiagLattice
