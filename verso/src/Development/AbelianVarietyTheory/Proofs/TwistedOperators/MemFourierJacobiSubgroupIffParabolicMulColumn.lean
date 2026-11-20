import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalBasic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilFormulaRootExchangeParabolicIntersection

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage

namespace GlobalTheory.RootEx.FourierJacobiGroup

/- English proof (translation)
Introduce `r s hrs`. Establish `: (A * M * B) r s = (A * (1 : Matrix ι ι k) * B) r s`. Simplify using `only [Matrix.mul_apply, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Distinguish the cases in `h1 : b r = b t`.

Distinguish the cases in `h2 : b u = b s`. Rewrite using `[hM t u (by omega)]`. Rewrite using `[hB u s h2, mul_zero, mul_zero]`. Simplify using `only [hA r t h1, zero_mul]`. Rewrite using `[this, Matrix.mul_one, hAB]`.
-/
theorem uni_conj {k : Type*} [Field k] {ι : Type*} [Fintype ι] [DecidableEq ι] {b : ι → ℕ}
    {A B M : Matrix ι ι k} (hA : ∀ r s, b r ≠ b s → A r s = 0) (hB : ∀ r s, b r ≠ b s → B r s = 0)
    (hAB : A * B = 1) (hM : Radical.Uni b M) : Radical.Uni b (A * M * B) := by
  intro r s hrs
  have : (A * M * B) r s = (A * (1 : Matrix ι ι k) * B) r s := by
    simp only [Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun t _ => ?_
    by_cases h1 : b r = b t
    · by_cases h2 : b u = b s
      · rw [hM t u (by omega)]
      · rw [hB u s h2, mul_zero, mul_zero]
    · simp only [hA r t h1, zero_mul]
  rw [this, Matrix.mul_one, hAB]

variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Simplify using `only [colE, upU, Units.val_mul, fromBlocks_multiply]`. Apply the tactic sequence `congr 1 <;> simp`. Use extensionality with `r i`. Apply the tactic sequence `by_cases h : i.val + 1 = q <;> simp [h, add_comm]`.
-/
theorem colE_add (q : ℕ) (β γ : n → k) : colE c q β * colE c q γ = colE c q (β + γ) := by
  apply Units.ext
  simp only [colE, upU, Units.val_mul, fromBlocks_multiply]
  congr 1 <;> simp
  ext r i
  by_cases h : i.val + 1 = q <;> simp [h, add_comm]

/- English proof (translation)
The claim follows from `inv_eq_of_mul_eq_one_right (QuotStep.colE_neg q β)`.
-/
theorem colE_inv (q : ℕ) (β : n → k) : (colE c q β)⁻¹ = colE c q (-β) :=
  inv_eq_of_mul_eq_one_right (QuotStep.colE_neg q β)

/- English proof (translation)
Use `QuotStep.colE_neg (c := c) q (0 : n → k)` as an intermediate fact. Rewrite `this` using `[colE_add, add_neg_cancel]`. Then use the resulting hypothesis.
-/
theorem colE_zero (q : ℕ) : colE c q (0 : n → k) = 1 := by
  have := QuotStep.colE_neg (c := c) q (0 : n → k)
  rwa [colE_add, add_neg_cancel] at this

/- English proof (translation)
Apply the tactic sequence `rcases r with r | r <;> rcases s with s | s`. Simplify using `[lev] at h`. Simplify using `only [lev, Sum.elim_inl, Sum.elim_inr] at h`. Simplify using `[colE, upU, h.symm]`. Simplify using `[colE, upU]`.

Establish `: r ≠ s`. Introduce and unpack `rfl`. Conclude with `h rfl`. Simplify using `[colE, upU, this]`.
-/
theorem colE_offdiag (q : ℕ) (β : n → k) (r s : n ⊕ Fin c) (h : lev q r ≠ lev q s) :
    (colE c q β).val r s = 0 := by
  rcases r with r | r <;> rcases s with s | s
  · simp [lev] at h
  · simp only [lev, Sum.elim_inl, Sum.elim_inr] at h
    simp [colE, upU, h.symm]
  · simp [colE, upU]
  · have : r ≠ s := by
      rintro rfl
      exact h rfl
    simp [colE, upU, this]

/- English proof (translation)
Rewrite `hu`, the goal using `[Radical.mem_N_iff]`. Rewrite using `[colE_inv]`. Conclude with `uni_conj (b := lev q) (colE_offdiag q β) (colE_offdiag q (-β)) (congrArg Units.val (QuotStep.colE_neg q β)) hu`.
-/
theorem colE_conj_mem (q : ℕ) (β : n → k) {u : GL (n ⊕ Fin c) k} (hu : u ∈ N k n c q) :
    colE c q β * u * (colE c q β)⁻¹ ∈ N k n c q := by
  rw [Radical.mem_N_iff] at hu ⊢
  rw [colE_inv]
  exact uni_conj (b := lev q) (colE_offdiag q β) (colE_offdiag q (-β))
    (congrArg Units.val (QuotStep.colE_neg q β)) hu

/- English proof (translation)
Set `β : n → k` to `fun x => g.val (Sum.inl x) (Sum.inr ⟨p, hp⟩)`. Use `⟨g * colE c (p + 1) (-β), ?_, β, by rw [mul_assoc, colE_add, neg_add_cancel, colE_zero, mul_one]⟩` and prove the remaining obligations. Establish `h1` using `(Radical.mem_N_iff _).1 (mul_mem hg (Radical.colE_mem (-β) (Nat.lt_succ_self p)))`. Establish `h0` using `(Radical.mem_N_iff _).1 hg`. Rewrite using `[Radical.mem_N_iff]`.

Introduce `r s hrs`. Distinguish the cases in `h : lev p s ≤ lev p r`. Conclude with `h1 r s h`. Apply the tactic sequence `rcases r with r | r <;> rcases s with s | s <;> simp only [lev, Sum.elim_inl, Sum.elim_inr] at h hrs`. Use linear arithmetic over natural numbers and integers.

Take `rfl : s = ⟨p, hp⟩` from `Fin.ext (by simp only; omega)`. Establish `h2 : ∀ y, g.val (Sum.inl r) (Sum.inl y) = (1 : Matrix n n k) r y` using `fun y => by`. Rewrite using `[h0 _ _ (by simp [lev])]; simp [Matrix.one_apply]`. Simplify using `[colE, upU, Matrix.mul_apply, Fintype.sum_sum_type, h2, Matrix.one_apply, β]`. Use linear arithmetic over natural numbers and integers.

Use linear arithmetic over natural numbers and integers.
-/
theorem exists_of_mem_N {p : ℕ} (hp : p < c) {g : GL (n ⊕ Fin c) k} (hg : g ∈ N k n c p) :
    ∃ u ∈ N k n c (p + 1), ∃ β : n → k, g = u * colE c (p + 1) β := by
  let β : n → k := fun x => g.val (Sum.inl x) (Sum.inr ⟨p, hp⟩)
  refine ⟨g * colE c (p + 1) (-β), ?_, β, by rw [mul_assoc, colE_add, neg_add_cancel, colE_zero, mul_one]⟩
  have h1 := (Radical.mem_N_iff _).1 (mul_mem hg (Radical.colE_mem (-β) (Nat.lt_succ_self p)))
  have h0 := (Radical.mem_N_iff _).1 hg
  rw [Radical.mem_N_iff]
  intro r s hrs
  by_cases h : lev p s ≤ lev p r
  · exact h1 r s h
  rcases r with r | r <;> rcases s with s | s <;> simp only [lev, Sum.elim_inl, Sum.elim_inr] at h hrs
  · omega
  · obtain rfl : s = ⟨p, hp⟩ := Fin.ext (by simp only; omega)
    have h2 : ∀ y, g.val (Sum.inl r) (Sum.inl y) = (1 : Matrix n n k) r y := fun y => by
      rw [h0 _ _ (by simp [lev])]; simp [Matrix.one_apply]
    simp [colE, upU, Matrix.mul_apply, Fintype.sum_sum_type, h2, Matrix.one_apply, β]
  · omega
  · omega

/- English proof (translation)
Take `⟨x, u, hu, rfl⟩` from `Radical.exists_of_mem_R hr`. Use `⟨embX c x * (colE c q ((x⁻¹).val.mulVec β) * u * (colE c q ((x⁻¹).val.mulVec β))⁻¹), mul_mem (Subgroup.mem_sup_left ⟨x, rfl⟩) (Subgroup.mem_sup_right (colE_conj_mem q _ hu)), (x⁻¹).val.mulVec β, ?_⟩` and prove the remaining obligations. Rewrite using `[← QuotStep.conj_colE, map_inv]`. Use `group`.
-/
theorem colE_conj_mem_R (q : ℕ) (β : n → k) {r : GL (n ⊕ Fin c) k} (hr : r ∈ R k n c q) :
    ∃ r' ∈ R k n c q, ∃ γ : n → k, colE c q β * r = r' * colE c q γ := by
  obtain ⟨x, u, hu, rfl⟩ := Radical.exists_of_mem_R hr
  refine ⟨embX c x * (colE c q ((x⁻¹).val.mulVec β) * u * (colE c q ((x⁻¹).val.mulVec β))⁻¹),
    mul_mem (Subgroup.mem_sup_left ⟨x, rfl⟩) (Subgroup.mem_sup_right (colE_conj_mem q _ hu)),
    (x⁻¹).val.mulVec β, ?_⟩
  rw [← QuotStep.conj_colE, map_inv]
  group

/- English proof (translation)
Introduce `k _ n _ _ c ρ _ hρ`. Use `⟨fun g => ⟨fun hg => ?_, ?_⟩, fun β u hu => colE_conj_mem _ β hu⟩` and prove the remaining obligations. Set `S : Subgroup (GL (n ⊕ Fin c) k)` to `{ carrier := {g | ∃ r ∈ R k n c (ρ + 1), ∃ β : n → k, g = r * colE c (ρ + 1) β} one_mem' := ⟨1, one_mem _, 0, by rw [colE_zero, mul_one]⟩ mul_mem' := by`. Introduce and unpack `_ _ ⟨r, hr, β, rfl⟩ ⟨r₂, hr₂, β₂, rfl⟩`. Take `⟨r', hr', γ, e⟩` from `colE_conj_mem_R (ρ + 1) β hr₂`.

Use `⟨r * r', mul_mem hr hr', γ + β₂, ?_⟩` and prove the remaining obligations. Rewrite using `[← colE_add, mul_assoc r, ← mul_assoc _ r₂, e]`. Simplify using `only [mul_assoc]`. Use the proof step `inv_mem' := by`. Introduce and unpack `_ ⟨r, hr, β, rfl⟩`.

Take `⟨r', hr', γ, e⟩` from `colE_conj_mem_R (ρ + 1) (-β) (inv_mem hr)`. Conclude with `⟨r', hr', γ, by rw [_root_.mul_inv_rev, colE_inv, e]⟩ }`. Establish `hR : R k n c (ρ + 1) ≤ S` using `fun r hr => ⟨r, hr, 0, by rw [colE_zero, mul_one]⟩`. Establish `: RFJ k n c ρ ≤ S`. Use `sup_le (sup_le (le_trans le_sup_left hR) fun g hg => ?_) hR` and prove the remaining obligations.

Take `⟨u, hu, β, rfl⟩` from `exists_of_mem_N hρ hg`. Conclude with `⟨u, Subgroup.mem_sup_right hu, β, rfl⟩`. Conclude with `this hg`. Introduce and unpack `⟨r, hr, β, rfl⟩`. Conclude with `mul_mem (Subgroup.mem_sup_right hr) (Subgroup.mem_sup_left (Subgroup.mem_sup_right (Radical.colE_mem β (Nat.lt_succ_self ρ))))`.
-/
theorem mem_RFJ_iff : ∀ (k : Type) [Field k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) (_ : 1 ≤ ρ) (_ : ρ < c), (∀ g, g ∈ RFJ k n c ρ ↔ ∃ r ∈ R k n c (ρ + 1), ∃ β : n → k, g = r * colE c (ρ + 1) β) ∧ ∀ β : n → k, ∀ u ∈ N k n c (ρ + 1), colE c (ρ + 1) β * u * (colE c (ρ + 1) β)⁻¹ ∈ N k n c (ρ + 1) := by
  intro k _ n _ _ c ρ _ hρ
  refine ⟨fun g => ⟨fun hg => ?_, ?_⟩, fun β u hu => colE_conj_mem _ β hu⟩
  · let S : Subgroup (GL (n ⊕ Fin c) k) :=
      { carrier := {g | ∃ r ∈ R k n c (ρ + 1), ∃ β : n → k, g = r * colE c (ρ + 1) β}
        one_mem' := ⟨1, one_mem _, 0, by rw [colE_zero, mul_one]⟩
        mul_mem' := by
          rintro _ _ ⟨r, hr, β, rfl⟩ ⟨r₂, hr₂, β₂, rfl⟩
          obtain ⟨r', hr', γ, e⟩ := colE_conj_mem_R (ρ + 1) β hr₂
          refine ⟨r * r', mul_mem hr hr', γ + β₂, ?_⟩
          rw [← colE_add, mul_assoc r, ← mul_assoc _ r₂, e]
          simp only [mul_assoc]
        inv_mem' := by
          rintro _ ⟨r, hr, β, rfl⟩
          obtain ⟨r', hr', γ, e⟩ := colE_conj_mem_R (ρ + 1) (-β) (inv_mem hr)
          exact ⟨r', hr', γ, by rw [_root_.mul_inv_rev, colE_inv, e]⟩ }
    have hR : R k n c (ρ + 1) ≤ S := fun r hr => ⟨r, hr, 0, by rw [colE_zero, mul_one]⟩
    have : RFJ k n c ρ ≤ S := by
      refine sup_le (sup_le (le_trans le_sup_left hR) fun g hg => ?_) hR
      obtain ⟨u, hu, β, rfl⟩ := exists_of_mem_N hρ hg
      exact ⟨u, Subgroup.mem_sup_right hu, β, rfl⟩
    exact this hg
  · rintro ⟨r, hr, β, rfl⟩
    exact mul_mem (Subgroup.mem_sup_right hr)
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right (Radical.colE_mem β (Nat.lt_succ_self ρ))))

end GlobalTheory.RootEx.FourierJacobiGroup
