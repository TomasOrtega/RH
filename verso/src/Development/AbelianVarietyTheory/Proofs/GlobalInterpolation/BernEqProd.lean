import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LFunctionPositiveConductorFourEight
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SharpRestriction.GlobalSchurBounds.MainIn
import Formalism.SharpRestriction.GlobalSchurBounds.ZetaZeroFreeRegion
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ChoiceOfTopsStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ParameterInequalitiesGoodStatement

open GlobalTheory.NT Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.BasicNotions NumberField IsDedekindDomain

namespace GlobalTheory.TopsChoice

open Formalism.FrobeniusOrbits Finset

/- English proof (translation)
Simplify using `[bern, Finset.card_univ_diff]`.
-/
lemma bern_eq_prod {α : Type} [Fintype α] [DecidableEq α] (δ : ℝ) (T : Finset α) :
    bern δ T = (∏ _a ∈ T, δ) * ∏ _a ∈ univ \ T, (1 - δ) := by
  simp [bern, Finset.card_univ_diff]

/- English proof (translation)
Use `set g : α → ℝ := fun a => if a ∈ (univ \ S).image f then 0 else δ with hg`. Use `set h : α → ℝ := fun a => if a ∈ S.image f then 0 else 1 - δ with hh`. Establish `h1` using `Finset.prod_add g h (univ : Finset α)`. Rewrite `h1` using `[powerset_univ]`. Establish `h2 : ∏ a, (g a + h a) = bern δ S`.

Rewrite using `[← Finset.prod_subset (subset_univ ((univ : Finset β).image f)), prod_image hf.injOn]`. Rewrite using `[bern_eq_prod, ← prod_sdiff (subset_univ S), mul_comm]`. Use `congr 1`. Use `prod_congr rfl fun i hi => ?_` and prove the remaining obligations. Simplify using `[hg, hh, hf.eq_iff, hi]`.

Use `prod_congr rfl fun i hi => ?_` and prove the remaining obligations. Establish `hi' : i ∉ S` using `(mem_sdiff.mp hi).2`. Simplify using `[hg, hh, hf.eq_iff, hi']`. Introduce `a _ ha`. Establish `ha1 : a ∉ (univ \ S).image f` using `fun h' => ha (image_subset_image (subset_univ _) h')`.

Establish `ha2 : a ∉ S.image f` using `fun h' => ha (image_subset_image (subset_univ _) h')`. Simplify using `only [hg, hh, if_neg ha1, if_neg ha2]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← h2, h1]`. Use `sum_congr rfl fun T _ => ?_` and prove the remaining obligations.

Use `split_ifs with hT`. Rewrite using `[bern_eq_prod]`. Use `congr 1`. Use `prod_congr rfl fun a ha => ?_` and prove the remaining obligations. Establish `: a ∉ (univ \ S).image f`.

Introduce `h'`. Take `⟨i, hi, rfl⟩` from `mem_image.mp h'`. Conclude with `(mem_sdiff.mp hi).2 (hT ▸ mem_filter.mpr ⟨mem_univ _, ha⟩)`. Simplify using `only [hg, if_neg this]`. Use `prod_congr rfl fun a ha => ?_` and prove the remaining obligations.

Establish `: a ∉ S.image f`. Introduce `h'`. Take `⟨i, hi, rfl⟩` from `mem_image.mp h'`. Rewrite `hi` using `[← hT]`. Conclude with `(mem_sdiff.mp ha).2 (mem_filter.mp hi).2`.

Simplify using `only [hh, if_neg this]`. Establish `: ∃ i, ¬ (f i ∈ T ↔ i ∈ S)`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Conclude with `hT (by ext i; simp [hc i])`.

Take `⟨i, hi⟩` from `this`. Distinguish the cases in `hiS : i ∈ S`. Establish `hT' : f i ∉ T` using `fun h' => hi ⟨fun _ => hiS, fun _ => h'⟩`. Rewrite using `[prod_eq_zero (s := univ \ T) (i := f i) (by simp [hT']), mul_zero]`. Simplify using `only [hh, if_pos (mem_image_of_mem f hiS)]`.

Establish `hT' : f i ∈ T`. Assume the negation of the conclusion as `h'`. Conclude with `hi ⟨fun h'' => absurd h'' h', fun h'' => absurd h'' hiS⟩`. Rewrite using `[prod_eq_zero (s := T) (i := f i) hT', zero_mul]`. Simplify using `only [hg, if_pos (mem_image_of_mem f (mem_sdiff.mpr ⟨mem_univ i, hiS⟩))]`.
-/
lemma fibre_sum {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (δ : ℝ)
    (f : β → α) (hf : Function.Injective f) (S : Finset β) :
    ∑ T : Finset α, (if univ.filter (fun i => f i ∈ T) = S then bern δ T else 0) = bern δ S := by
  classical
  set g : α → ℝ := fun a => if a ∈ (univ \ S).image f then 0 else δ with hg
  set h : α → ℝ := fun a => if a ∈ S.image f then 0 else 1 - δ with hh
  have h1 := Finset.prod_add g h (univ : Finset α)
  rw [powerset_univ] at h1
  have h2 : ∏ a, (g a + h a) = bern δ S := by
    rw [← Finset.prod_subset (subset_univ ((univ : Finset β).image f)), prod_image hf.injOn]
    · rw [bern_eq_prod, ← prod_sdiff (subset_univ S), mul_comm]
      congr 1
      · refine prod_congr rfl fun i hi => ?_
        simp [hg, hh, hf.eq_iff, hi]
      · refine prod_congr rfl fun i hi => ?_
        have hi' : i ∉ S := (mem_sdiff.mp hi).2
        simp [hg, hh, hf.eq_iff, hi']
    · intro a _ ha
      have ha1 : a ∉ (univ \ S).image f := fun h' => ha (image_subset_image (subset_univ _) h')
      have ha2 : a ∉ S.image f := fun h' => ha (image_subset_image (subset_univ _) h')
      simp only [hg, hh, if_neg ha1, if_neg ha2]
      ring
  rw [← h2, h1]
  refine sum_congr rfl fun T _ => ?_
  split_ifs with hT
  · rw [bern_eq_prod]
    congr 1
    · refine prod_congr rfl fun a ha => ?_
      have : a ∉ (univ \ S).image f := by
        intro h'
        obtain ⟨i, hi, rfl⟩ := mem_image.mp h'
        exact (mem_sdiff.mp hi).2 (hT ▸ mem_filter.mpr ⟨mem_univ _, ha⟩)
      simp only [hg, if_neg this]
    · refine prod_congr rfl fun a ha => ?_
      have : a ∉ S.image f := by
        intro h'
        obtain ⟨i, hi, rfl⟩ := mem_image.mp h'
        rw [← hT] at hi
        exact (mem_sdiff.mp ha).2 (mem_filter.mp hi).2
      simp only [hh, if_neg this]
  · have : ∃ i, ¬ (f i ∈ T ↔ i ∈ S) := by
      by_contra hc
      push Not at hc
      exact hT (by ext i; simp [hc i])
    obtain ⟨i, hi⟩ := this
    by_cases hiS : i ∈ S
    · have hT' : f i ∉ T := fun h' => hi ⟨fun _ => hiS, fun _ => h'⟩
      rw [prod_eq_zero (s := univ \ T) (i := f i) (by simp [hT']), mul_zero]
      simp only [hh, if_pos (mem_image_of_mem f hiS)]
    · have hT' : f i ∈ T := by
        by_contra h'
        exact hi ⟨fun h'' => absurd h'' h', fun h'' => absurd h'' hiS⟩
      rw [prod_eq_zero (s := T) (i := f i) hT', zero_mul]
      simp only [hg, if_pos (mem_image_of_mem f (mem_sdiff.mpr ⟨mem_univ i, hiS⟩))]

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Use `sum_congr rfl fun T _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_ite_eq]`. Simplify using the standard rewrite rules. Use `_ = ∑ S : Finset β, if A S then bern δ S else 0 := by`.

Rewrite using `[sum_comm]`. Use `sum_congr rfl fun S _ => ?_` and prove the remaining obligations. Distinguish the cases in `hA : A S`. Simplify using `only [if_pos hA]`. Conclude with `fibre_sum δ f hf S`.

Simplify using `[hA]`.
-/
lemma marginal {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (δ : ℝ)
    (f : β → α) (hf : Function.Injective f) (A : Finset β → Prop) [DecidablePred A] :
    ∑ T : Finset α, (if A (univ.filter (fun i => f i ∈ T)) then bern δ T else 0) =
      ∑ S : Finset β, if A S then bern δ S else 0 := by
  calc ∑ T : Finset α, (if A (univ.filter (fun i => f i ∈ T)) then bern δ T else 0)
      = ∑ T : Finset α, ∑ S : Finset β,
          (if univ.filter (fun i => f i ∈ T) = S then (if A S then bern δ T else 0) else 0) := by
        refine sum_congr rfl fun T _ => ?_
        rw [Finset.sum_ite_eq]
        simp
    _ = ∑ S : Finset β, if A S then bern δ S else 0 := by
        rw [sum_comm]
        refine sum_congr rfl fun S _ => ?_
        by_cases hA : A S
        · simp only [if_pos hA]
          exact fibre_sum δ f hf S
        · simp [hA]

open Classical in
/- English proof (translation)
Unfold `Formalism.G0.condProbAt`. Rewrite using `[sum_mul]`. Use `Finset.sum_bij (fun S _ => S.map Fin.valEmbedding) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `S _`. Rewrite using `[mem_powerset]`.

Introduce `x hx`. Take `⟨i, _, rfl⟩` from `mem_map.mp hx`. Simplify using the standard rewrite rules. Introduce `S _ S' _ h`. Conclude with `Finset.map_injective _ h`.

Introduce `T hT`. Use `⟨univ.filter (fun i : Fin n => (i : ℕ) ∈ T), mem_univ _, ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Simplify using `only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨i, hi, rfl⟩`. Conclude with `hi`. Introduce `hx`. Conclude with `⟨⟨x, mem_range.mp (mem_powerset.mp hT hx)⟩, hx, rfl⟩`. Introduce `S _`.

Establish `hm : (i₀ : ℕ) ∈ S.map Fin.valEmbedding ↔ i₀ ∈ S` using `Finset.mem_map' Fin.valEmbedding`. Simplify using `only [hm]`. Use `split_ifs with h`. Establish `hc : 1 ≤ S.card` using `card_pos.mpr ⟨i₀, h.1⟩`. Take `⟨k, hk⟩` from `Nat.exists_eq_add_of_le' hc`.

Simplify using `only [bern, card_map, Fintype.card_fin, hk, Nat.add_sub_cancel]`. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules.
-/
lemma fin_sum_eq (n : ℕ) (δ : ℝ) (i₀ : Fin n) (A : Finset ℕ → Prop) :
    (∑ S : Finset (Fin n), if i₀ ∈ S ∧ A (S.map Fin.valEmbedding) then bern δ S else 0) =
      Formalism.G0.condProbAt n δ i₀ A * δ := by
  unfold Formalism.G0.condProbAt
  rw [sum_mul]
  refine Finset.sum_bij (fun S _ => S.map Fin.valEmbedding) ?_ ?_ ?_ ?_
  · intro S _
    rw [mem_powerset]
    intro x hx
    obtain ⟨i, _, rfl⟩ := mem_map.mp hx
    simp
  · intro S _ S' _ h
    exact Finset.map_injective _ h
  · intro T hT
    refine ⟨univ.filter (fun i : Fin n => (i : ℕ) ∈ T), mem_univ _, ?_⟩
    ext x
    simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact hi
    · intro hx
      exact ⟨⟨x, mem_range.mp (mem_powerset.mp hT hx)⟩, hx, rfl⟩
  · intro S _
    have hm : (i₀ : ℕ) ∈ S.map Fin.valEmbedding ↔ i₀ ∈ S :=
      Finset.mem_map' Fin.valEmbedding
    simp only [hm]
    split_ifs with h
    · have hc : 1 ≤ S.card := card_pos.mpr ⟨i₀, h.1⟩
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' hc
      simp only [bern, card_map, Fintype.card_fin, hk, Nat.add_sub_cancel]
      ring
    · simp

open Classical in

/- English proof (translation)
Take `⟨i, hi⟩` from `ht`. Establish `hpos : 0 < addOrderOf h` using `addOrderOf_pos h`. Establish `hlt : i % addOrderOf h < addOrderOf h` using `Nat.mod_lt _ hpos`. Use `⟨i % addOrderOf h, hlt, ?_⟩` and prove the remaining obligations. Establish `hinj : Function.Injective (fun j : Fin (addOrderOf h) => b + (j : ℕ) • h)`.

Introduce `j k hjk`. Use `add_left_cancel hjk` as an intermediate fact. Conclude with `Fin.ext (nsmul_injOn_Iio_addOrderOf j.2 k.2 this)`. Rewrite using `[← fin_sum_eq (addOrderOf h) δ ⟨_, hlt⟩ A, ← marginal δ _ hinj (fun S => (⟨_, hlt⟩ : Fin (addOrderOf h)) ∈ S ∧ A (S.map Fin.valEmbedding))]`. Use `sum_congr rfl fun T _ => ?_` and prove the remaining obligations.

Establish `: t ∈ T ↔ (⟨_, hlt⟩ : Fin (addOrderOf h)) ∈ univ.filter (fun i : Fin (addOrderOf h) => b + (i : ℕ) • h ∈ T)`. Simplify using `[mod_addOrderOf_nsmul, hi]`. Simplify using `only [this]`.
-/
lemma orbit_sum {α : Type} [Fintype α] [DecidableEq α] [AddCommGroup α] (δ : ℝ) (b h t : α)
    (ht : ∃ i : ℕ, b + i • h = t) (A : Finset ℕ → Prop) :
    ∃ i₀ < addOrderOf h,
      (∑ T : Finset α, if t ∈ T ∧ A ((univ.filter
          (fun i : Fin (addOrderOf h) => b + (i : ℕ) • h ∈ T)).map Fin.valEmbedding)
        then bern δ T else 0) = Formalism.G0.condProbAt (addOrderOf h) δ i₀ A * δ := by
  obtain ⟨i, hi⟩ := ht
  have hpos : 0 < addOrderOf h := addOrderOf_pos h
  have hlt : i % addOrderOf h < addOrderOf h := Nat.mod_lt _ hpos
  refine ⟨i % addOrderOf h, hlt, ?_⟩
  have hinj : Function.Injective (fun j : Fin (addOrderOf h) => b + (j : ℕ) • h) := by
    intro j k hjk
    have := add_left_cancel hjk
    exact Fin.ext (nsmul_injOn_Iio_addOrderOf j.2 k.2 this)
  rw [← fin_sum_eq (addOrderOf h) δ ⟨_, hlt⟩ A, ← marginal δ _ hinj
    (fun S => (⟨_, hlt⟩ : Fin (addOrderOf h)) ∈ S ∧ A (S.map Fin.valEmbedding))]
  refine sum_congr rfl fun T _ => ?_
  have : t ∈ T ↔ (⟨_, hlt⟩ : Fin (addOrderOf h)) ∈ univ.filter
      (fun i : Fin (addOrderOf h) => b + (i : ℕ) • h ∈ T) := by
    simp [mod_addOrderOf_nsmul, hi]
  simp only [this]

end GlobalTheory.TopsChoice

namespace GlobalTheory

open GlobalTheory.TopsChoice

/- English proof (translation)
Introduce `eps he he'`. Take `⟨Cb, x₀, hCb, hnum⟩` from `GlobalTheory.T.parameter_inequalities_good eps he he'`. Use `⟨Cb, max x₀ 32, hCb, ?_⟩` and prove the remaining obligations. Introduce `s hs hx e L₂ hlo hhi hL bs hbs _ PP hp ω hω hPP`. Establish `hx1 : 1 < s.x` using `s.one_lt_alt`.

Establish `hx0 : 0 < s.x` using `by linarith`. Establish `hx32 : 32 ≤ s.x` using `le_trans (le_max_right _ _) hx`. Establish `hδ : 0 < s.delta1` using `Real.rpow_pos_of_pos hx0 _`. Establish `hδ1 : s.delta1 ≤ 1` using `Real.rpow_le_one_of_one_le_of_nonpos hx1.le (by have := s.eps_pos; linarith)`. Use `haveI : NeZero (2 ^ e) := ⟨by positivity⟩`.

Establish `hcard : Fintype.card (ZMod (2 ^ e)) = 2 ^ e` using `ZMod.card _`. Establish `h16 : 16 ≤ s.delta1 * (Fintype.card (ZMod (2 ^ e)) : ℝ)`. Rewrite using `[hcard]`. Establish `h1 : s.x ≤ s.delta1 * s.x ^ Formalism.MainNotions.G.hG s`. Unfold `Scale.delta1 Formalism.MainNotions.G.hG`.

Rewrite using `[← Real.rpow_add hx0]`. Combine the equalities or inequalities in the displayed calculation. Use `mul_le_mul_of_nonneg_left hlo hδ.le` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hβ : 0 ≤ Cb * s.x ^ (-2 : ℝ)` using `by positivity`.

Take `⟨T, hT1, hT2, hT3⟩` from `Formalism.FrobeniusOrbits.hostTops (ZMod (2 ^ e)) PP s.delta1 (Cb * s.x ^ (-2 : ℝ)) (fun p => ω p) (fun p t T => ¬ Formalism.MainNotions.G.IsGoodOrbit (addOrderOf (hp p)) (Finset.univ.filter (fun i : Fin (addOrderOf (hp p)) => bs (hp p) t + (i : ℕ) • hp p ∈ T)) L₂ (Formalism.Main …`. Introduce `p t`. Establish `hn : ((addOrderOf (hp p) : ℕ) : ℝ) ≤ 2 * s.x ^ Formalism.MainNotions.G.hG s`. Use `le_trans ?_ hhi` and prove the remaining obligations. Conclude with `Nat.cast_le.mpr (addOrderOf_le_card_univ.trans hcard.le)`.

Take `⟨h1, h2⟩` from `hnum s hs (le_trans (le_max_left _ _) hx) (addOrderOf (hp p)) L₂ (hPP p p.2) hn hL`. Take `⟨i₀, hi₀, hsum⟩` from `orbit_sum s.delta1 (bs (hp p) t) (hp p) t (hbs _ _) (fun T => ¬ Formalism.G0.GoodOrbitIntervalTileCondition (addOrderOf (hp p)) T L₂ (Formalism.MainNotions.G.KG s) (Formalism.MainNotions.G.rG s) (Formalism.MainNotions.G.goodU s.delta1) (Formalism.MainNotions.G.orbitSmallMultiplic …`. Establish `hu : 1 ≤ Formalism.MainNotions.G.goodU s.delta1` using `Nat.ceil_pos.mpr (by positivity)`. Establish `h3` using `GlobalTheory.T.choice_of_tops (addOrderOf (hp p)) s.delta1 L₂ (Formalism.MainNotions.G.KG s) (Formalism.MainNotions.G.rG s) (Formalism.MainNotions.G.goodU s.delta1) (Formalism.MainNotions.G.orbitSmallMultiplicity (Formalism.MainNotions.G.rG s) (Formalism.MainNotions.G.hG s) s.x) …`. Use `le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_right (h3.trans h2) hδ.le)` and prove the remaining obligations.

Rewrite using `[← hsum]`. Unfold `Formalism.MainNotions.G.IsGoodOrbit`. Use `rfl)` and compare the differences between its conclusion and the goal. Rewrite `hT1`, `hT2`, `hT3` using `[hcard]`. Use `⟨T, hT1, hT2, ?_⟩` and prove the remaining obligations.

Rewrite using `[← Finset.sum_coe_sort PP, ← Finset.sum_coe_sort PP ω]`. Use `le_trans (le_of_eq ?_) hT3` and prove the remaining obligations. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Use `congr 2`. Rewrite using `[← Set.ncard_coe_finset, Finset.coe_filter]`.
-/
theorem topsChoice : ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ Cb x₀ : ℝ, 0 < Cb ∧ ∀ s : Scale, s.eps = eps → x₀ ≤ s.x → ∀ e L₂ : ℕ, s.x ^ Formalism.MainNotions.G.hG s / 2 ≤ ((2 ^ e : ℕ) : ℝ) → ((2 ^ e : ℕ) : ℝ) ≤ 2 * s.x ^ Formalism.MainNotions.G.hG s → (L₂ : ℝ) ≤ 1242 / eps → ∀ bs : ZMod (2 ^ e) → ZMod (2 ^ e) → ZMod (2 ^ e), (∀ h t, ∃ i : ℕ, bs h t + i • h = t) → (∀ h t, bs h (t + h) = bs h t) → ∀ (PP : Finset ℕ) (hp : ℕ → ZMod (2 ^ e)) (ω : ℕ → ℝ), (∀ p, 0 ≤ ω p) → (∀ p ∈ PP, s.x ^ (eps / 4) ≤ (addOrderOf (hp p) : ℝ)) → ∃ TT : Finset (ZMod (2 ^ e)), s.delta1 * ((2 ^ e : ℕ) : ℝ) / 2 ≤ (TT.card : ℝ) ∧ (TT.card : ℝ) ≤ 2 * s.delta1 * ((2 ^ e : ℕ) : ℝ) ∧ ∑ p ∈ PP, ω p * (({t : ZMod (2 ^ e) | t ∈ TT ∧ ¬ Formalism.MainNotions.G.IsGoodOrbit (addOrderOf (hp p)) (Finset.univ.filter (fun i : Fin (addOrderOf (hp p)) => bs (hp p) t + (i : ℕ) • hp p ∈ TT)) L₂ (Formalism.MainNotions.G.KG s) (Formalism.MainNotions.G.rG s) s.delta1 (Formalism.MainNotions.G.hG s) s.x}.ncard : ℕ) : ℝ) ≤ 4 * (Cb * s.x ^ (-2 : ℝ)) * s.delta1 * ((2 ^ e : ℕ) : ℝ) * ∑ p ∈ PP, ω p := by
  classical
  intro eps he he'
  obtain ⟨Cb, x₀, hCb, hnum⟩ := GlobalTheory.T.parameter_inequalities_good eps he he'
  refine ⟨Cb, max x₀ 32, hCb, ?_⟩
  intro s hs hx e L₂ hlo hhi hL bs hbs _ PP hp ω hω hPP
  have hx1 : 1 < s.x := s.one_lt_alt
  have hx0 : 0 < s.x := by linarith
  have hx32 : 32 ≤ s.x := le_trans (le_max_right _ _) hx
  have hδ : 0 < s.delta1 := Real.rpow_pos_of_pos hx0 _
  have hδ1 : s.delta1 ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hx1.le (by have := s.eps_pos; linarith)
  haveI : NeZero (2 ^ e) := ⟨by positivity⟩
  have hcard : Fintype.card (ZMod (2 ^ e)) = 2 ^ e := ZMod.card _
  have h16 : 16 ≤ s.delta1 * (Fintype.card (ZMod (2 ^ e)) : ℝ) := by
    rw [hcard]
    have h1 : s.x ≤ s.delta1 * s.x ^ Formalism.MainNotions.G.hG s := by
      unfold Scale.delta1 Formalism.MainNotions.G.hG
      rw [← Real.rpow_add hx0]
      calc s.x = s.x ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx1.le (by have := s.eps_pos; linarith)
    have := mul_le_mul_of_nonneg_left hlo hδ.le
    linarith
  have hβ : 0 ≤ Cb * s.x ^ (-2 : ℝ) := by positivity
  obtain ⟨T, hT1, hT2, hT3⟩ := Formalism.FrobeniusOrbits.hostTops (ZMod (2 ^ e)) PP s.delta1 (Cb * s.x ^ (-2 : ℝ))
    (fun p => ω p)
    (fun p t T => ¬ Formalism.MainNotions.G.IsGoodOrbit (addOrderOf (hp p)) (Finset.univ.filter
      (fun i : Fin (addOrderOf (hp p)) => bs (hp p) t + (i : ℕ) • hp p ∈ T)) L₂ (Formalism.MainNotions.G.KG s)
      (Formalism.MainNotions.G.rG s) s.delta1 (Formalism.MainNotions.G.hG s) s.x)
    hδ hδ1 hβ (fun p => hω p) h16 (by
      intro p t
      have hn : ((addOrderOf (hp p) : ℕ) : ℝ) ≤ 2 * s.x ^ Formalism.MainNotions.G.hG s := by
        refine le_trans ?_ hhi
        exact Nat.cast_le.mpr (addOrderOf_le_card_univ.trans hcard.le)
      obtain ⟨h1, h2⟩ := hnum s hs (le_trans (le_max_left _ _) hx) (addOrderOf (hp p)) L₂
        (hPP p p.2) hn hL
      obtain ⟨i₀, hi₀, hsum⟩ := orbit_sum s.delta1 (bs (hp p) t) (hp p) t (hbs _ _)
        (fun T => ¬ Formalism.G0.GoodOrbitIntervalTileCondition (addOrderOf (hp p)) T L₂ (Formalism.MainNotions.G.KG s) (Formalism.MainNotions.G.rG s)
          (Formalism.MainNotions.G.goodU s.delta1) (Formalism.MainNotions.G.orbitSmallMultiplicity (Formalism.MainNotions.G.rG s) (Formalism.MainNotions.G.hG s) s.x)
          (Formalism.MainNotions.G.goodG' (Formalism.MainNotions.G.rG s) s.delta1 (Formalism.MainNotions.G.hG s) s.x)
          (Formalism.MainNotions.G.orbitWindowCount (Formalism.MainNotions.G.rG s) s.delta1 (Formalism.MainNotions.G.hG s) s.x))
      have hu : 1 ≤ Formalism.MainNotions.G.goodU s.delta1 := Nat.ceil_pos.mpr (by positivity)
      have h3 := GlobalTheory.T.choice_of_tops (addOrderOf (hp p)) s.delta1 L₂ (Formalism.MainNotions.G.KG s) (Formalism.MainNotions.G.rG s)
        (Formalism.MainNotions.G.goodU s.delta1) (Formalism.MainNotions.G.orbitSmallMultiplicity (Formalism.MainNotions.G.rG s) (Formalism.MainNotions.G.hG s) s.x)
        (Formalism.MainNotions.G.goodG' (Formalism.MainNotions.G.rG s) s.delta1 (Formalism.MainNotions.G.hG s) s.x)
        (Formalism.MainNotions.G.orbitWindowCount (Formalism.MainNotions.G.rG s) s.delta1 (Formalism.MainNotions.G.hG s) s.x) i₀ hδ.le hδ1
        (Nat.le_add_left 1 _) hu h1 hi₀
      refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_right (h3.trans h2) hδ.le)
      rw [← hsum]
      unfold Formalism.MainNotions.G.IsGoodOrbit
      convert rfl)
  rw [hcard] at hT1 hT2 hT3
  refine ⟨T, hT1, hT2, ?_⟩
  rw [← Finset.sum_coe_sort PP, ← Finset.sum_coe_sort PP ω]
  refine le_trans (le_of_eq ?_) hT3
  refine Finset.sum_congr rfl fun p _ => ?_
  congr 2
  rw [← Set.ncard_coe_finset, Finset.coe_filter]

end GlobalTheory
