import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BasePartFlagPt
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.LcFam

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

/- English proof (translation)
Rewrite using `[Matrix.mul_add, Matrix.mul_one, Matrix.add_apply]`. Use `congr 1`. Rewrite using `[Matrix.mul_apply]`. Distinguish the cases in `h : s = ca`. Substitute `h` using the available equality.

Simplify using `[Matrix.single_apply]`. Simplify using `[Matrix.single_apply, h, Ne.symm h]`.
-/
theorem mul_elem_apply (A : Matrix (Fin N) (Fin N) ℂ) (ca cb r s : Fin N) (t : ℂ) :
    (A * (1 + Matrix.single cb ca t)) r s = A r s + if s = ca then A r cb * t else 0 := by
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_apply]
  congr 1
  rw [Matrix.mul_apply]
  by_cases h : s = ca
  · subst h
    simp [Matrix.single_apply]
  · simp [Matrix.single_apply, h, Ne.symm h]

/- English proof (translation)
Use extensionality with `r s`. Rewrite using `[mul_elem_apply]`. Distinguish the cases in `h : s = ca`. Substitute `h` using the available equality. Distinguish the cases in `hr : cb = r`.

Substitute `hr` using the available equality. Simplify using `[Matrix.add_apply, Matrix.single_apply, Matrix.one_apply, hne, Ne.symm hne]`. Apply the tactic sequence `try ring`. Simplify using `[Matrix.add_apply, Matrix.single_apply, Matrix.one_apply, hne, Ne.symm hne, hr, Ne.symm hr]`. Simplify using `[Matrix.add_apply, Matrix.single_apply, h, Ne.symm h]`.
-/
theorem elem_mul_elem {ca cb : Fin N} (hne : ca ≠ cb) (t u : ℂ) :
    (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) * (1 + Matrix.single cb ca u) =
      1 + Matrix.single cb ca (t + u) := by
  ext r s
  rw [mul_elem_apply]
  by_cases h : s = ca
  · subst h
    by_cases hr : cb = r
    · subst hr
      simp [Matrix.add_apply, Matrix.single_apply, Matrix.one_apply, hne, Ne.symm hne]
      try ring
    · simp [Matrix.add_apply, Matrix.single_apply, Matrix.one_apply, hne, Ne.symm hne, hr, Ne.symm hr]
  · simp [Matrix.add_apply, Matrix.single_apply, h, Ne.symm h]

/- English proof (translation)
Rewrite using `[Matrix.mul_assoc, elem_mul_elem hne, add_neg_cancel, Matrix.single_zero, add_zero, Matrix.mul_one]`.
-/
theorem mul_elem_cancel {ca cb : Fin N} (hne : ca ≠ cb) (A : Matrix (Fin N) (Fin N) ℂ) (t : ℂ) :
    A * (1 + Matrix.single cb ca t) * (1 + Matrix.single cb ca (-t)) = A := by
  rw [Matrix.mul_assoc, elem_mul_elem hne, add_neg_cancel, Matrix.single_zero, add_zero, Matrix.mul_one]

/- English proof (translation)
Introduce `r s hrs`. Establish `h1 : (1 : Matrix (Fin N) (Fin N) ℂ) r s = 0` using `Matrix.one_apply_ne fun e => hrs (by rw [e])`. Establish `h2 : (Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) r s = 0`. Rewrite using `[Matrix.single_apply, if_neg]`. Introduce and unpack `⟨rfl, rfl⟩`.

Conclude with `hrs hs`. Rewrite using `[Matrix.add_apply, h1, h2, add_zero]`.
-/
theorem isBlockDiag_elem {ca cb : Fin N} (hs : (cb : ℕ) < N - j ↔ (ca : ℕ) < N - j) (t : ℂ) :
    IsBlockDiag j (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) := by
  intro r s hrs
  have h1 : (1 : Matrix (Fin N) (Fin N) ℂ) r s = 0 := Matrix.one_apply_ne fun e => hrs (by rw [e])
  have h2 : (Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) r s = 0 := by
    rw [Matrix.single_apply, if_neg]
    rintro ⟨rfl, rfl⟩
    exact hrs hs
  rw [Matrix.add_apply, h1, h2, add_zero]

/- English proof (translation)
Use `⟨fun r => ?_, fun r s hrs => ?_⟩` and prove the remaining obligations. Rewrite using `[mul_elem_apply, hA.1] split_ifs with h`. Substitute `h` using the available equality. Rewrite using `[hA.2 r cb hlt, zero_mul, add_zero]`. Rewrite using `[add_zero]`.

Rewrite using `[mul_elem_apply, hA.2 r s hrs] split_ifs with h`. Substitute `h` using the available equality. Rewrite using `[hA.2 r cb (hrs.trans hlt), zero_mul, add_zero]`. Rewrite using `[add_zero]`.
-/
theorem isLowerUni_mul_elem {ca cb : Fin N} (hlt : ca < cb) {A : Matrix (Fin N) (Fin N) ℂ} (hA : IsLowerUni A)
    (t : ℂ) : IsLowerUni (A * (1 + Matrix.single cb ca t)) := by
  refine ⟨fun r => ?_, fun r s hrs => ?_⟩
  · rw [mul_elem_apply, hA.1]
    split_ifs with h
    · subst h
      rw [hA.2 r cb hlt, zero_mul, add_zero]
    · rw [add_zero]
  · rw [mul_elem_apply, hA.2 r s hrs]
    split_ifs with h
    · subst h
      rw [hA.2 r cb (hrs.trans hlt), zero_mul, add_zero]
    · rw [add_zero]

/- English proof (translation)
Introduce `r s hrs`. Establish `hne : r ≠ s` using `fun e => hrs (by rw [e])`. Unfold `FC.Lc`. Rewrite using `[dif_neg (fun h => hrs h.1.2), if_neg hne]`.
-/
theorem isBlockDiag_Lc (τ : Ψ) (ca cb : Fin N) (c : FC.CIdx Ψ N j τ ca cb → ℂ) (τ' : Ψ) :
    IsBlockDiag j (FC.Lc τ ca cb c τ') := by
  intro r s hrs
  have hne : r ≠ s := fun e => hrs (by rw [e])
  unfold FC.Lc
  rw [dif_neg (fun h => hrs h.1.2), if_neg hne]

/- English proof (translation)
Use `⟨fun r => ?_, fun r s hrs => ?_⟩` and prove the remaining obligations. Unfold `FC.Lc`. Rewrite using `[dif_neg (fun h => lt_irrefl _ h.1.1), if_pos rfl]`. Unfold `FC.Lc`. Rewrite using `[dif_neg (fun h => lt_asymm hrs h.1.1), if_neg hrs.ne]`.
-/
theorem isLowerUni_Lc (τ : Ψ) (ca cb : Fin N) (c : FC.CIdx Ψ N j τ ca cb → ℂ) (τ' : Ψ) :
    IsLowerUni (FC.Lc τ ca cb c τ') := by
  refine ⟨fun r => ?_, fun r s hrs => ?_⟩
  · unfold FC.Lc
    rw [dif_neg (fun h => lt_irrefl _ h.1.1), if_pos rfl]
  · unfold FC.Lc
    rw [dif_neg (fun h => lt_asymm hrs h.1.1), if_neg hrs.ne]

/- English proof (translation)
Unfold `FC.Lc`. Rewrite using `[dif_pos (⟨q.1.2, q.2⟩ : _ ∧ _)]`.
-/
theorem Lc_apply_idx (τ : Ψ) (ca cb : Fin N) (c : FC.CIdx Ψ N j τ ca cb → ℂ) (q : FC.CIdx Ψ N j τ ca cb) :
    FC.Lc τ ca cb c q.1.1.1 q.1.1.2.1 q.1.1.2.2 = c q := by
  unfold FC.Lc
  rw [dif_pos (⟨q.1.2, q.2⟩ : _ ∧ _)]

/- English proof (translation)
Unfold `FC.Lc`. Rewrite using `[dif_neg (fun h => h.2 rfl), if_neg (Ne.symm hne)]`.
-/
theorem Lc_self_apply (τ : Ψ) {ca cb : Fin N} (hne : ca ≠ cb) (c : FC.CIdx Ψ N j τ ca cb → ℂ) :
    FC.Lc τ ca cb c τ cb ca = 0 := by
  unfold FC.Lc
  rw [dif_neg (fun h => h.2 rfl), if_neg (Ne.symm hne)]

/- English proof (translation)
Use function extensionality and compare the values at `τ'`. Use extensionality with `r s`. Unfold `FC.Lc`. Use `split_ifs with h hrs`. Both sides reduce to the same expression.

Substitute `hrs` using the available equality. Conclude with `((hL τ').2.1 r).symm`. Distinguish the cases in `e : (τ', r, s) = (τ, cb, ca)`. Take `⟨rfl, rfl, rfl⟩ : τ' = τ ∧ r = cb ∧ s = ca` from `by simpa using e`. Conclude with `h0.symm`.

Establish `hn : ¬ (s < r ∧ ((r : ℕ) < N - j ↔ (s : ℕ) < N - j))` using `fun h' => h ⟨h', e⟩`. Distinguish the cases in `hsr : s < r`. Conclude with `((hL τ').1 r s fun hb => hn ⟨hsr, hb⟩).symm`. Conclude with `((hL τ').2.2 r s (lt_of_le_of_ne (not_lt.1 hsr) hrs)).symm`.
-/
theorem Lc_of_entries (τ : Ψ) {ca cb : Fin N} (hne : ca ≠ cb) (L : Ψ → Matrix (Fin N) (Fin N) ℂ)
    (hL : ∀ τ', IsBlockDiag j (L τ') ∧ IsLowerUni (L τ')) (h0 : L τ cb ca = 0) :
    FC.Lc τ ca cb (fun q : FC.CIdx Ψ N j τ ca cb => L q.1.1.1 q.1.1.2.1 q.1.1.2.2) = L := by
  funext τ'
  ext r s
  unfold FC.Lc
  split_ifs with h hrs
  · rfl
  · subst hrs
    exact ((hL τ').2.1 r).symm
  · by_cases e : (τ', r, s) = (τ, cb, ca)
    · obtain ⟨rfl, rfl, rfl⟩ : τ' = τ ∧ r = cb ∧ s = ca := by simpa using e
      exact h0.symm
    · have hn : ¬ (s < r ∧ ((r : ℕ) < N - j ↔ (s : ℕ) < N - j)) := fun h' => h ⟨h', e⟩
      by_cases hsr : s < r
      · exact ((hL τ').1 r s fun hb => hn ⟨hsr, hb⟩).symm
      · exact ((hL τ').2.2 r s (lt_of_le_of_ne (not_lt.1 hsr) hrs)).symm

/- English proof (translation)
Unfold `FC.Lc`. Distinguish the cases in `h : (s < r ∧ ((r : ℕ) < N - j ↔ (s : ℕ) < N - j)) ∧ (τ', r, s) ≠ (τ, cb, ca)`. Simplify using `only [dif_pos h]`. Conclude with `(ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : FC.CIdx Ψ N j τ ca cb => ℂ) ⟨⟨(τ', r, s), h.1⟩, h.2⟩).analyticOnNhd _`. Simplify using `only [dif_neg h]`.

Conclude with `analyticOnNhd_const`.
-/
theorem Lc_analytic (τ : Ψ) (ca cb : Fin N) (τ' : Ψ) (r s : Fin N) :
    AnalyticOnNhd ℂ (fun c : FC.CIdx Ψ N j τ ca cb → ℂ => FC.Lc τ ca cb c τ' r s) Set.univ := by
  unfold FC.Lc
  by_cases h : (s < r ∧ ((r : ℕ) < N - j ↔ (s : ℕ) < N - j)) ∧ (τ', r, s) ≠ (τ, cb, ca)
  · simp only [dif_pos h]
    exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : FC.CIdx Ψ N j τ ca cb => ℂ)
      ⟨⟨(τ', r, s), h.1⟩, h.2⟩).analyticOnNhd _
  · simp only [dif_neg h]
    exact analyticOnNhd_const

/- English proof (translation)
Establish `hne : ca ≠ cb` using `hlt.ne`. Set `a : ℂ` to `L τ cb ca`. Set `L' : Ψ → Matrix (Fin N) (Fin N) ℂ` to `Function.update L τ (L τ * (1 + Matrix.single cb ca (-a)))`. Establish `hτ : L' τ = L τ * (1 + Matrix.single cb ca (-a))` using `Function.update_self _ _ _`. Establish `hL' : ∀ τ', IsBlockDiag j (L' τ') ∧ IsLowerUni (L' τ')`.

Introduce `τ'`. Distinguish the cases in `e : τ' = τ`. Substitute `e` using the available equality. Rewrite using `[hτ]`. Conclude with `⟨(hL _).1.mul (isBlockDiag_elem hs _), isLowerUni_mul_elem hlt (hL _).2 _⟩`.

Establish `: L' τ' = L τ'` using `Function.update_of_ne e _ _`. Rewrite using `[this]`. Conclude with `hL τ'`. Establish `h0 : L' τ cb ca = 0`. Rewrite using `[hτ, mul_elem_apply, if_pos rfl, (hL τ).2.1 cb, one_mul]`.

Conclude with `add_neg_cancel _`. Use `⟨fun q => L' q.1.1.1 q.1.1.2.1 q.1.1.2.2, a, ?_⟩` and prove the remaining obligations. Establish `hback : L τ * (1 + Matrix.single cb ca (-a)) * (1 + Matrix.single cb ca a) = L τ`. Use `mul_elem_cancel hne (L τ) (-a)` as an intermediate fact. Rewrite `this` using `[neg_neg]`. Then use the resulting hypothesis.

Unfold `FC.Lca`. Rewrite using `[Lc_of_entries τ hne L' hL' h0, hτ, hback]`. Use function extensionality and compare the values at `τ'`. Distinguish the cases in `e : τ' = τ`. Substitute `e` using the available equality.

Conclude with `Function.update_self _ _ _`. Rewrite using `[Function.update_of_ne e]`. Conclude with `Function.update_of_ne e _ _`.
-/
theorem exists_Lca (τ : Ψ) {ca cb : Fin N} (hlt : ca < cb) (hs : (cb : ℕ) < N - j ↔ (ca : ℕ) < N - j)
    (L : Ψ → Matrix (Fin N) (Fin N) ℂ) (hL : ∀ τ', IsBlockDiag j (L τ') ∧ IsLowerUni (L τ')) :
    ∃ (c : FC.CIdx Ψ N j τ ca cb → ℂ) (a : ℂ), FC.Lca τ ca cb c a = L := by
  have hne : ca ≠ cb := hlt.ne
  let a : ℂ := L τ cb ca
  let L' : Ψ → Matrix (Fin N) (Fin N) ℂ := Function.update L τ (L τ * (1 + Matrix.single cb ca (-a)))
  have hτ : L' τ = L τ * (1 + Matrix.single cb ca (-a)) := Function.update_self _ _ _
  have hL' : ∀ τ', IsBlockDiag j (L' τ') ∧ IsLowerUni (L' τ') := by
    intro τ'
    by_cases e : τ' = τ
    · subst e
      rw [hτ]
      exact ⟨(hL _).1.mul (isBlockDiag_elem hs _), isLowerUni_mul_elem hlt (hL _).2 _⟩
    · have : L' τ' = L τ' := Function.update_of_ne e _ _
      rw [this]
      exact hL τ'
  have h0 : L' τ cb ca = 0 := by
    rw [hτ, mul_elem_apply, if_pos rfl, (hL τ).2.1 cb, one_mul]
    exact add_neg_cancel _
  refine ⟨fun q => L' q.1.1.1 q.1.1.2.1 q.1.1.2.2, a, ?_⟩
  have hback : L τ * (1 + Matrix.single cb ca (-a)) * (1 + Matrix.single cb ca a) = L τ := by
    have := mul_elem_cancel hne (L τ) (-a)
    rwa [neg_neg] at this
  unfold FC.Lca
  rw [Lc_of_entries τ hne L' hL' h0, hτ, hback]
  funext τ'
  by_cases e : τ' = τ
  · subst e
    exact Function.update_self _ _ _
  · rw [Function.update_of_ne e]
    exact Function.update_of_ne e _ _

/- English proof (translation)
Unfold `FC.Lca`. Distinguish the cases in `e : τ' = τ`. Substitute `e` using the available equality. Rewrite using `[Function.update_self]`. Conclude with `⟨(isBlockDiag_Lc _ _ _ _ _).mul (isBlockDiag_elem hs _), isLowerUni_mul_elem hlt (isLowerUni_Lc _ _ _ _ _) _⟩`.

Rewrite using `[Function.update_of_ne e]`. Conclude with `⟨isBlockDiag_Lc _ _ _ _ _, isLowerUni_Lc _ _ _ _ _⟩`.
-/
theorem Lca_prop (τ : Ψ) {ca cb : Fin N} (hlt : ca < cb) (hs : (cb : ℕ) < N - j ↔ (ca : ℕ) < N - j)
    (c : FC.CIdx Ψ N j τ ca cb → ℂ) (a : ℂ) (τ' : Ψ) :
    IsBlockDiag j (FC.Lca τ ca cb c a τ') ∧ IsLowerUni (FC.Lca τ ca cb c a τ') := by
  unfold FC.Lca
  by_cases e : τ' = τ
  · subst e
    rw [Function.update_self]
    exact ⟨(isBlockDiag_Lc _ _ _ _ _).mul (isBlockDiag_elem hs _), isLowerUni_mul_elem hlt (isLowerUni_Lc _ _ _ _ _) _⟩
  · rw [Function.update_of_ne e]
    exact ⟨isBlockDiag_Lc _ _ _ _ _, isLowerUni_Lc _ _ _ _ _⟩

/- English proof (translation)
Establish `hne : ca ≠ cb` using `hlt.ne`. Establish `hτ : FC.Lc τ ca cb c τ * (1 + Matrix.single cb ca a) = FC.Lc τ ca cb c' τ * (1 + Matrix.single cb ca a')`. Use `congrFun h τ` as an intermediate fact. Unfold `FC.Lca at this`. Rewrite `this` using `[Function.update_self, Function.update_self]`. Then use the resulting hypothesis.

Apply the tactic sequence `have entry : ∀ (d : FC.CIdx Ψ N j τ ca cb → ℂ) (t : ℂ), (FC.Lc τ ca cb d τ * (1 + Matrix.single cb ca t)) cb ca = t := fun d t => by`. Rewrite using `[mul_elem_apply, if_pos rfl, Lc_self_apply τ hne, (isLowerUni_Lc τ ca cb d τ).1 cb, zero_add, one_mul]`. Establish `ha : a = a'`. Apply the tactic sequence `rw [← entry c a, hτ, entry]`. Substitute `ha` using the available equality.

Establish `hc : FC.Lc τ ca cb c = FC.Lc τ ca cb c'`. Use function extensionality and compare the values at `τ'`. Distinguish the cases in `e : τ' = τ`. Substitute `e` using the available equality. Rewrite using `[← mul_elem_cancel hne (FC.Lc τ' ca cb c τ') a, hτ, mul_elem_cancel hne]`.

Use `congrFun h τ'` as an intermediate fact. Unfold `FC.Lca at this`. Rewrite `this` using `[Function.update_of_ne e, Function.update_of_ne e]`. Then use the resulting hypothesis. Use `⟨funext fun q => ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[← Lc_apply_idx τ ca cb c q, hc, Lc_apply_idx]`.
-/
theorem Lca_injective (τ : Ψ) {ca cb : Fin N} (hlt : ca < cb) (c c' : FC.CIdx Ψ N j τ ca cb → ℂ) (a a' : ℂ)
    (h : FC.Lca τ ca cb c a = FC.Lca τ ca cb c' a') : c = c' ∧ a = a' := by
  have hne : ca ≠ cb := hlt.ne
  have hτ : FC.Lc τ ca cb c τ * (1 + Matrix.single cb ca a) = FC.Lc τ ca cb c' τ * (1 + Matrix.single cb ca a') := by
    have := congrFun h τ
    unfold FC.Lca at this
    rwa [Function.update_self, Function.update_self] at this
  have entry : ∀ (d : FC.CIdx Ψ N j τ ca cb → ℂ) (t : ℂ),
      (FC.Lc τ ca cb d τ * (1 + Matrix.single cb ca t)) cb ca = t := fun d t => by
    rw [mul_elem_apply, if_pos rfl, Lc_self_apply τ hne, (isLowerUni_Lc τ ca cb d τ).1 cb, zero_add, one_mul]
  have ha : a = a' := by
    rw [← entry c a, hτ, entry]
  subst ha
  have hc : FC.Lc τ ca cb c = FC.Lc τ ca cb c' := by
    funext τ'
    by_cases e : τ' = τ
    · subst e
      rw [← mul_elem_cancel hne (FC.Lc τ' ca cb c τ') a, hτ, mul_elem_cancel hne]
    · have := congrFun h τ'
      unfold FC.Lca at this
      rwa [Function.update_of_ne e, Function.update_of_ne e] at this
  refine ⟨funext fun q => ?_, rfl⟩
  rw [← Lc_apply_idx τ ca cb c q, hc, Lc_apply_idx]

/- English proof (translation)
Introduce `Ψ _ _ N j τ ca cb hlt hs`. Use `⟨fun c τ' => ⟨isBlockDiag_Lc τ ca cb c τ', ?_⟩, fun τ' r s => Lc_analytic τ ca cb τ' r s, fun L hL => exists_Lca τ hlt hs L hL, fun c a τ' => Lca_prop τ hlt hs c a τ', fun c c' a a' h => Lca_injective τ hlt c c' a a' h⟩` and prove the remaining obligations. Rewrite using `[(isLowerUni_Lc τ ca cb c τ').det]`. Conclude with `one_ne_zero`.
-/
theorem lc_main : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (τ : Ψ) (ca cb : Fin N), ca < cb → ((cb : ℕ) < N - j ↔ (ca : ℕ) < N - j) → (∀ (c : FC.CIdx Ψ N j τ ca cb → ℂ) τ', IsBlockDiag j (FC.Lc τ ca cb c τ') ∧ (FC.Lc τ ca cb c τ').det ≠ 0) ∧ (∀ τ' r s, AnalyticOnNhd ℂ (fun c : FC.CIdx Ψ N j τ ca cb → ℂ => FC.Lc τ ca cb c τ' r s) Set.univ) ∧ (∀ L : Ψ → Matrix (Fin N) (Fin N) ℂ, (∀ τ', IsBlockDiag j (L τ') ∧ IsLowerUni (L τ')) → ∃ (c : FC.CIdx Ψ N j τ ca cb → ℂ) (a : ℂ), FC.Lca τ ca cb c a = L) ∧ (∀ (c : FC.CIdx Ψ N j τ ca cb → ℂ) (a : ℂ) τ', IsBlockDiag j (FC.Lca τ ca cb c a τ') ∧ IsLowerUni (FC.Lca τ ca cb c a τ')) ∧ ∀ (c c' : FC.CIdx Ψ N j τ ca cb → ℂ) (a a' : ℂ), FC.Lca τ ca cb c a = FC.Lca τ ca cb c' a' → c = c' ∧ a = a' := by
  intro Ψ _ _ N j τ ca cb hlt hs
  refine ⟨fun c τ' => ⟨isBlockDiag_Lc τ ca cb c τ', ?_⟩, fun τ' r s => Lc_analytic τ ca cb τ' r s,
    fun L hL => exists_Lca τ hlt hs L hL, fun c a τ' => Lca_prop τ hlt hs c a τ',
    fun c c' a a' h => Lca_injective τ hlt c c' a a' h⟩
  rw [(isLowerUni_Lc τ ca cb c τ').det]
  exact one_ne_zero

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.LcFam
