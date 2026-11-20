import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.LatticeInclusionFormsInjective
open Formalism.L2.FormalSeriesBounds

noncomputable section

open scoped BigOperators
open Classical MvPowerSeries Formalism.IncomingBounds Formalism.UnitaryBoundIntegral

namespace GlobalTheory.MainToRows

variable {C : Type} [Field C]

/- English proof (translation)
Establish `hc : ∀ k, constantCoeff (killCompl e (a k)) = 0` using `fun k => by`. Rewrite using `[← coeff_zero_eq_constantCoeff_apply, coeff_killCompl, Finsupp.embDomain_zero, coeff_zero_eq_constantCoeff_apply, ha]`. Use extensionality with `x`. Rewrite using `[coeff_killCompl, coeff_subst (hasSubst_of_constantCoeff_zero ha), coeff_subst (hasSubst_of_constantCoeff_zero hc)]`. Use `finsum_congr fun d => ?_` and prove the remaining obligations.

Rewrite using `[← coeff_killCompl, map_finsuppProd]`. Simplify using `only [map_pow]`.
-/
theorem killCompl_subst {σ τ κ : Type} [Finite κ] (e : σ ↪ τ) (a : κ → MvPowerSeries τ C)
    (ha : ∀ k, constantCoeff (a k) = 0) (H : MvPowerSeries κ C) :
    killCompl e (subst a H) = subst (fun k => killCompl e (a k)) H := by
  have hc : ∀ k, constantCoeff (killCompl e (a k)) = 0 := fun k => by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_killCompl, Finsupp.embDomain_zero,
      coeff_zero_eq_constantCoeff_apply, ha]
  ext x
  rw [coeff_killCompl, coeff_subst (hasSubst_of_constantCoeff_zero ha),
    coeff_subst (hasSubst_of_constantCoeff_zero hc)]
  refine finsum_congr fun d => ?_
  rw [← coeff_killCompl, map_finsuppProd]
  simp only [map_pow]

def eps {n0 n : ℕ} (hn : n0 ≤ n) : Fin n0 ⊕ Fin n0 ↪ Fin n0 ⊕ Fin n :=
  Function.Embedding.sumMap (Function.Embedding.refl _) (Fin.castLEEmb hn)

/- English proof (translation)
The claim follows from `killCompl_X (e := eps hn) (Sum.inl c)`.
-/
theorem kill_inl {n0 n : ℕ} (hn : n0 ≤ n) (c : Fin n0) :
    killCompl (eps hn) (X (Sum.inl c) : MvPowerSeries (Fin n0 ⊕ Fin n) C) = X (Sum.inl c) :=
  killCompl_X (e := eps hn) (Sum.inl c)

/- English proof (translation)
The claim follows from `killCompl_X (e := eps hn) (Sum.inr c)`.
-/
theorem kill_inr {n0 n : ℕ} (hn : n0 ≤ n) (c : Fin n0) :
    killCompl (eps hn) (X (Sum.inr (Fin.castLE hn c)) : MvPowerSeries (Fin n0 ⊕ Fin n) C) =
      X (Sum.inr c) :=
  killCompl_X (e := eps hn) (Sum.inr c)

/- English proof (translation)
Use `killCompl_X_eq_zero ?_` and prove the remaining obligations. Introduce and unpack `⟨x | x, hx⟩`. Simplify using `[eps] at hx`. Conclude with `hb ⟨x, by simpa [eps] using hx⟩`.
-/
theorem kill_inr_zero {n0 n : ℕ} (hn : n0 ≤ n) (b : Fin n) (hb : b ∉ Set.range (Fin.castLE hn)) :
    killCompl (eps hn) (X (Sum.inr b) : MvPowerSeries (Fin n0 ⊕ Fin n) C) = 0 := by
  refine killCompl_X_eq_zero ?_
  rintro ⟨x | x, hx⟩
  · simp [eps] at hx
  · exact hb ⟨x, by simpa [eps] using hx⟩

/- English proof (translation)
The claim follows from `(Fintype.sum_of_injective (Fin.castLE hn) (Fin.castLE_injective hn) _ f hf (fun _ => rfl)).symm`.
-/
theorem sum_castLE {M : Type*} [AddCommMonoid M] {n0 n : ℕ} (hn : n0 ≤ n) (f : Fin n → M)
    (hf : ∀ b, b ∉ Set.range (Fin.castLE hn) → f b = 0) :
    ∑ b, f b = ∑ b : Fin n0, f (Fin.castLE hn b) :=
  (Fintype.sum_of_injective (Fin.castLE hn) (Fin.castLE_injective hn) _ f hf (fun _ => rfl)).symm

/- English proof (translation)
Unfold `hPullW`. Rewrite using `[killCompl_subst _ _ (fun k => by simp)]`. Use `congr 1`. Use function extensionality and compare the values at `w`. Rewrite using `[map_add, map_sum, map_sum, sum_castLE hn (fun b => killCompl (eps hn) (e' b w • X (Sum.inr b)))]`.

Simplify using `only [map_smul, kill_inl, kill_inr]`. Introduce `b hb`. Rewrite using `[map_smul, kill_inr_zero hn b hb, smul_zero]`.
-/
theorem kill_hPullW {I : Fin 2 → Type} [∀ g, Fintype (I g)] {n0 n : ℕ} (hn : n0 ≤ n)
    (H : MvPowerSeries (WV I) C) (e : Fin n0 → WV I → C) (e' : Fin n → WV I → C) :
    killCompl (eps hn) (hPullW H e e') = hPullW H e (fun b => e' (Fin.castLE hn b)) := by
  unfold hPullW
  rw [killCompl_subst _ _ (fun k => by simp)]
  congr 1
  funext w
  rw [map_add, map_sum, map_sum, sum_castLE hn (fun b => killCompl (eps hn) (e' b w • X (Sum.inr b)))]
  · simp only [map_smul, kill_inl, kill_inr]
  · intro b hb
    rw [map_smul, kill_inr_zero hn b hb, smul_zero]

/- English proof (translation)
Unfold `mainM`. Rewrite using `[map_smul, map_sum, sum_castLE hn]`. Simplify using `only [map_sum, map_smul, map_mul, map_pow, kill_inl, kill_inr]`. Introduce `b hb`. Simplify using `only [map_sum, map_smul, map_mul, kill_inr_zero hn b hb, mul_zero, smul_zero, Finset.sum_const_zero]`.
-/
theorem kill_mainM (V : VF C) (i : ℕ) {n0 n : ℕ} (hn : n0 ≤ n) (Φ : Fin n → Fin n0 → C) :
    killCompl (eps hn) (mainM V i Φ) = mainM V i (fun b c => Φ (Fin.castLE hn b) c) := by
  unfold mainM
  rw [map_smul, map_sum, sum_castLE hn]
  · simp only [map_sum, map_smul, map_mul, map_pow, kill_inl, kill_inr]
  · intro b hb
    simp only [map_sum, map_smul, map_mul, kill_inr_zero hn b hb, mul_zero, smul_zero,
      Finset.sum_const_zero]

/- English proof (translation)
The claim follows from `Finset.sum_congr rfl fun c _ => Finsupp.embDomain_apply_self (eps hn) μ (Sum.inl c)`.
-/
theorem sum_inl_eps {n0 n : ℕ} (hn : n0 ≤ n) (μ : Fin n0 ⊕ Fin n0 →₀ ℕ) :
    ∑ c, (Finsupp.embDomain (eps hn) μ) (Sum.inl c) = ∑ c, μ (Sum.inl c) :=
  Finset.sum_congr rfl fun c _ => Finsupp.embDomain_apply_self (eps hn) μ (Sum.inl c)

/- English proof (translation)
Rewrite using `[sum_castLE hn]`. Conclude with `Finset.sum_congr rfl fun c _ => Finsupp.embDomain_apply_self (eps hn) μ (Sum.inr c)`. Introduce `b hb`. Use `Finsupp.embDomain_of_notMem_range _ _ _ ?_` and prove the remaining obligations. Introduce and unpack `⟨x | x, hx⟩`.

Simplify using `[eps] at hx`. Conclude with `hb ⟨x, by simpa [eps] using hx⟩`.
-/
theorem sum_inr_eps {n0 n : ℕ} (hn : n0 ≤ n) (μ : Fin n0 ⊕ Fin n0 →₀ ℕ) :
    ∑ c, (Finsupp.embDomain (eps hn) μ) (Sum.inr c) = ∑ c, μ (Sum.inr c) := by
  rw [sum_castLE hn]
  · exact Finset.sum_congr rfl fun c _ => Finsupp.embDomain_apply_self (eps hn) μ (Sum.inr c)
  · intro b hb
    refine Finsupp.embDomain_of_notMem_range _ _ _ ?_
    rintro ⟨x | x, hx⟩
    · simp [eps] at hx
    · exact hb ⟨x, by simpa [eps] using hx⟩

def rowE {n0 : ℕ} (ρ : Fin n0) : Fin n0 ⊕ Fin n0 ↪ PVar n0 :=
  Function.Embedding.sumMap (Function.Embedding.sectR ρ (Fin n0)) (Function.Embedding.sectR ρ (Fin n0))

/- English proof (translation)
Unfold `hRows`. Use `Finset.sum_congr rfl fun ρ _ => ?_` and prove the remaining obligations. Rewrite using `[rename_eq_subst]`. Use `congr 1`. Use function extensionality and compare the values at `x`.

Apply the tactic sequence `rcases x with x | x <;> rfl`.
-/
theorem hRows_eq (n0 : ℕ) (H : MvPowerSeries (Fin n0 ⊕ Fin n0) C) :
    hRows n0 H = ∑ ρ : Fin n0, rename (rowE ρ) H := by
  unfold hRows
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [rename_eq_subst]
  congr 1
  funext x
  rcases x with x | x <;> rfl

/- English proof (translation)
Distinguish the cases in `h : m ∈ Set.range (Finsupp.mapDomain (rowE ρ))`. Take `⟨μ, rfl⟩` from `h`. Rewrite using `[← Finsupp.embDomain_eq_mapDomain]`. Establish `hout : ∀ x : PVar n0, rowOf x ≠ ρ → Finsupp.embDomain (rowE ρ) μ x = 0`. Introduce `x hx`.

Use `Finsupp.embDomain_of_notMem_range _ _ _ ?_` and prove the remaining obligations. Apply the tactic sequence `rintro ⟨y | y, rfl⟩ <;> exact hx rfl`. Use `Or.inr ⟨μ, coeff_embDomain_rename _ _ _, ?_, ?_, ?_⟩` and prove the remaining obligations. Unfold `degL`. Rewrite using `[Finset.sum_eq_single ρ]`.

Conclude with `Finset.sum_congr rfl fun c _ => Finsupp.embDomain_apply_self (rowE ρ) μ (Sum.inl c)`. Conclude with `fun b _ hb => Finset.sum_eq_zero fun c _ => hout _ hb`. Simplify using the standard rewrite rules. Unfold `degR`. Rewrite using `[Finset.sum_eq_single ρ]`.

Conclude with `Finset.sum_congr rfl fun c _ => Finsupp.embDomain_apply_self (rowE ρ) μ (Sum.inr c)`. Conclude with `fun b _ hb => Finset.sum_eq_zero fun c _ => hout _ hb`. Simplify using the standard rewrite rules. Introduce `x hx`. Assume the negation of the conclusion as `hne`.

Conclude with `(Finsupp.mem_support_iff.1 hx) (hout x hne)`. Conclude with `Or.inl (coeff_rename_eq_zero _ _ h)`.
-/
theorem coeff_row {n0 : ℕ} (ρ : Fin n0) (H : MvPowerSeries (Fin n0 ⊕ Fin n0) C) (m : PVar n0 →₀ ℕ) :
    coeff m (rename (rowE ρ) H) = 0 ∨ ∃ μ : Fin n0 ⊕ Fin n0 →₀ ℕ,
      coeff m (rename (rowE ρ) H) = coeff μ H ∧ degL m = ∑ c, μ (Sum.inl c) ∧
        degR m = ∑ c, μ (Sum.inr c) ∧ ∀ x ∈ m.support, rowOf x = ρ := by
  by_cases h : m ∈ Set.range (Finsupp.mapDomain (rowE ρ))
  · obtain ⟨μ, rfl⟩ := h
    rw [← Finsupp.embDomain_eq_mapDomain]
    have hout : ∀ x : PVar n0, rowOf x ≠ ρ → Finsupp.embDomain (rowE ρ) μ x = 0 := by
      intro x hx
      refine Finsupp.embDomain_of_notMem_range _ _ _ ?_
      rintro ⟨y | y, rfl⟩ <;> exact hx rfl
    refine Or.inr ⟨μ, coeff_embDomain_rename _ _ _, ?_, ?_, ?_⟩
    · unfold degL
      rw [Finset.sum_eq_single ρ]
      · exact Finset.sum_congr rfl fun c _ => Finsupp.embDomain_apply_self (rowE ρ) μ (Sum.inl c)
      · exact fun b _ hb => Finset.sum_eq_zero fun c _ => hout _ hb
      · simp
    · unfold degR
      rw [Finset.sum_eq_single ρ]
      · exact Finset.sum_congr rfl fun c _ => Finsupp.embDomain_apply_self (rowE ρ) μ (Sum.inr c)
      · exact fun b _ hb => Finset.sum_eq_zero fun c _ => hout _ hb
      · simp
    · intro x hx
      by_contra hne
      exact (Finsupp.mem_support_iff.1 hx) (hout x hne)
  · exact Or.inl (coeff_rename_eq_zero _ _ h)

/- English proof (translation)
Proceed by induction on `t with`. Consider the case `top => simp`. Consider the case `coe t => rw [← WithTop.coe_add, WithTop.coe_le_coe, WithTop.coe_le_coe, sub_le_iff_le_add]`.
-/
theorem le_add_iff (w r : ℝ) (t : WithTop ℝ) :
    (w : WithTop ℝ) ≤ t + (r : WithTop ℝ) ↔ ((w - r : ℝ) : WithTop ℝ) ≤ t := by
  induction t with
  | top => simp
  | coe t => rw [← WithTop.coe_add, WithTop.coe_le_coe, WithTop.coe_le_coe, sub_le_iff_le_add]

/- English proof (translation)
Unfold `mainM`. Use `Eq.trans (Finset.sum_congr rfl fun ρ _ => ?_) (Finset.smul_sum).symm` and prove the remaining obligations. Simplify using `only [ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true, map_smul, map_sum, map_mul, map_pow, rename_X, neg_smul, one_smul, map_neg, Finset.sum_neg_distrib, smul_neg]`. Both sides reduce to the same expression.
-/
theorem rows_main (V : VF C) (i n0 : ℕ) :
    ∑ ρ : Fin n0, rename (rowE ρ) (mainM V i (fun b c : Fin n0 => if b = c then (-1 : C) else 0)) =
      -((V.l : C) ^ (expE V.l i))⁻¹ • (∑ b : Fin n0, ∑ c : Fin n0,
        (X (Sum.inl (b, c)) ^ (V.l ^ i) * X (Sum.inr (b, c)) : MvPowerSeries (PVar n0) C)) := by
  unfold mainM
  refine Eq.trans (Finset.sum_congr rfl fun ρ _ => ?_) (Finset.smul_sum).symm
  simp only [ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true, map_smul, map_sum,
    map_mul, map_pow, rename_X, neg_smul, one_smul, map_neg, Finset.sum_neg_distrib, smul_neg]
  rfl

end GlobalTheory.MainToRows

open GlobalTheory.MainToRows in

/- English proof (translation)
Introduce `C _ V d _ I J _ _ X g a i U U' n0 e v' Φ hM hn`. Take `⟨-, -, -, -, -, hΦ, hwt, hax⟩` from `hM`. Use `set H := X.hGood g a i hn e v' - mainM V i (fun b c : Fin n0 => if b = c then (-1 : C) else 0) with hH`. Establish `hkill : H = killCompl (eps hn) (X.hM g a i e v' - mainM V i Φ)`. Rewrite using `[hH, map_sub, kill_mainM]`.

Unfold `RowData.hGood RowData.hM`. Rewrite using `[kill_hPullW]`. Use `congr 2`. Use function extensionality and compare the values at `b c`. Rewrite using `[hΦ _ c (by simp)]`.

Simplify using `[Fin.ext_iff]`. Establish `hco : ∀ μ, coeff μ H = coeff (Finsupp.embDomain (eps hn) μ) (X.hM g a i e v' - mainM V i Φ)` using `fun μ => by rw [hkill, coeff_killCompl]`. Establish `h1 : X.restrictedCurveSystemSeries g a i hn e v' = ∑ ρ : Fin n0, rename (rowE ρ) H` using `hRows_eq _ _`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[h1, hRows_eq, hP, ← rows_main, ← Finset.sum_add_distrib]`.

Use `Finset.sum_congr rfl fun ρ _ => ?_` and prove the remaining obligations. Rewrite using `[← map_add, hH, add_sub_cancel]`. Introduce `m`. Rewrite using `[h1, le_add_iff, map_sum]`. Use `V.v.map_le_sum fun ρ _ => ?_` and prove the remaining obligations.

Break down `coeff_row ρ H m with h | ⟨μ, h, hL, hR, -⟩` into its components or cases. Rewrite using `[h, V.v.map_zero]`. Conclude with `le_top`. Rewrite using `[h, hco, ← le_add_iff, hL, hR, ← sum_inl_eps hn, ← sum_inr_eps hn]`. Conclude with `hwt _`.

Introduce `m hm`. Rewrite `hm` using `[h1, map_sum]`. Take `⟨ρ, -, hρ⟩` from `Finset.exists_ne_zero_of_sum_ne_zero hm`. Break down `coeff_row ρ H m with h | ⟨μ, h, -, hR, -⟩` into its components or cases. Conclude with `absurd h hρ`.

Rewrite `hρ` using `[h, hco]`. Assume the negation of the conclusion as `hlt`. Use `hρ (hax _ ?_)` and prove the remaining obligations. Establish `h0 : ∑ c, (Finsupp.embDomain (eps hn) μ) (Sum.inr c) = 0`. Rewrite using `[sum_inr_eps, ← hR]`.

Use linear arithmetic over natural numbers and integers. Conclude with `fun b => (Finset.sum_eq_zero_iff.1 h0) b (Finset.mem_univ b)`. Introduce `hi hP`. Substitute `hi` using the available equality. Use `⟨fun ρ => rename (rowE ρ) H, h1, fun ρ m hm => ?_, fun ρ m hl hr => ?_⟩` and prove the remaining obligations.

Break down `coeff_row ρ H m with h | ⟨μ, -, -, -, h⟩` into its components or cases. Conclude with `absurd h hm`. Conclude with `h`. Break down `coeff_row ρ H m with h | ⟨μ, h, hL, hR, -⟩` into its components or cases. Rewrite using `[h, V.v.map_zero]`.

Conclude with `le_top`. Rewrite using `[h, hco]`. Conclude with `hP _ (by rw [sum_inl_eps, ← hL]; exact hl) (by rw [sum_inr_eps, ← hR]; exact hr)`.
-/
theorem GlobalTheory.mainTerm_to_rowHypothesis :
    ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)]
      [∀ g, Fintype (J g)] (X : RowData C V d I J), X.MtoHM := by
  intro C _ V d _ I J _ _ X g a i U U' n0 e v' Φ hM hn
  obtain ⟨-, -, -, -, -, hΦ, hwt, hax⟩ := hM
  set H := X.hGood g a i hn e v' - mainM V i (fun b c : Fin n0 => if b = c then (-1 : C) else 0)
    with hH
  have hkill : H = killCompl (eps hn) (X.hM g a i e v' - mainM V i Φ) := by
    rw [hH, map_sub, kill_mainM]
    unfold RowData.hGood RowData.hM
    rw [kill_hPullW]
    congr 2
    funext b c
    rw [hΦ _ c (by simp)]
    simp [Fin.ext_iff]
  have hco : ∀ μ, coeff μ H = coeff (Finsupp.embDomain (eps hn) μ) (X.hM g a i e v' - mainM V i Φ) :=
    fun μ => by rw [hkill, coeff_killCompl]
  have h1 : X.restrictedCurveSystemSeries g a i hn e v' = ∑ ρ : Fin n0, rename (rowE ρ) H := hRows_eq _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h1, hRows_eq, hP, ← rows_main, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [← map_add, hH, add_sub_cancel]
  · intro m
    rw [h1, le_add_iff, map_sum]
    refine V.v.map_le_sum fun ρ _ => ?_
    rcases coeff_row ρ H m with h | ⟨μ, h, hL, hR, -⟩
    · rw [h, V.v.map_zero]; exact le_top
    · rw [h, hco, ← le_add_iff, hL, hR, ← sum_inl_eps hn, ← sum_inr_eps hn]
      exact hwt _
  · intro m hm
    rw [h1, map_sum] at hm
    obtain ⟨ρ, -, hρ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
    rcases coeff_row ρ H m with h | ⟨μ, h, -, hR, -⟩
    · exact absurd h hρ
    · rw [h, hco] at hρ
      by_contra hlt
      refine hρ (hax _ ?_)
      have h0 : ∑ c, (Finsupp.embDomain (eps hn) μ) (Sum.inr c) = 0 := by
        rw [sum_inr_eps, ← hR]; omega
      exact fun b => (Finset.sum_eq_zero_iff.1 h0) b (Finset.mem_univ b)
  · intro hi hP
    subst hi
    refine ⟨fun ρ => rename (rowE ρ) H, h1, fun ρ m hm => ?_, fun ρ m hl hr => ?_⟩
    · rcases coeff_row ρ H m with h | ⟨μ, -, -, -, h⟩
      · exact absurd h hm
      · exact h
    · rcases coeff_row ρ H m with h | ⟨μ, h, hL, hR, -⟩
      · rw [h, V.v.map_zero]; exact le_top
      · rw [h, hco]
        exact hP _ (by rw [sum_inl_eps, ← hL]; exact hl) (by rw [sum_inr_eps, ← hR]; exact hr)
