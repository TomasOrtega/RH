import Mathlib
import Formalism.PeriodIntegrals.PairCorankPos
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PairCorankPositivity.EqZeroOfMulVec
import Lemmata.GeneralBFactLeftAlt.Imports

noncomputable section

open scoped Classical

namespace PI.PairCorankPos.W

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [StarRing E]

/- English proof (translation)
Apply the tactic sequence `first | exact Bl.general_b_fact_left_alt.goal1 .. | (apply Bl.general_b_fact_left_alt.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_left_alt.goal1 <;> assumption) | (apply @Bl.general_b_fact_left_alt.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_left_alt.go …`.
-/
theorem exists_smul_mem {S : HSpace E} (Λ : Submodule (𝓞 E) S.V) (hΛ : Submodule.IsLattice E Λ)
    (v : S.V) : ∃ c : 𝓞 E, c ≠ 0 ∧ c • v ∈ Λ := by
  first | exact Bl.general_b_fact_left_alt.goal1 .. | (apply Bl.general_b_fact_left_alt.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_left_alt.goal1 <;> assumption) | (apply @Bl.general_b_fact_left_alt.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_left_alt.goal1 <;> assumption) | (apply @Bl.general_b_fact_left_alt.goal1 <;> first | assumption | infer_instance)

/- English proof (translation)
Set `Φ : S.V →ₗ[E] (ι → E)` to `LinearMap.pi (fun i => S.hT (u i))`. Establish `hle : orth S U ≤ LinearMap.ker Φ`. Introduce `v hv`. Rewrite using `[LinearMap.mem_ker]`. Use function extensionality and compare the values at `i`.

Establish `h1` using `(Submodule.mem_iInf _).1 hv (u i)`. Establish `h2` using `(Submodule.mem_iInf _).1 h1 (hU i)`. Conclude with `h2`. Establish `hrange : LinearMap.range Φ = ⊤`. Assume the negation of the conclusion as `hne`.

Take `⟨f, hf0, hfle⟩` from `Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)`. Use `set c : ι → E := fun i => f (fun j => if i = j then 1 else 0) with hc`. Use `set w : S.V := ∑ i, star (c i) • u i with hw`. Establish `hwv : ∀ v, S.hT w v = 0`. Introduce `v`.

Establish `h1 : f (Φ v) = 0` using `hfle (LinearMap.mem_range_self Φ v)`. Rewrite `h1` using `[LinearMap.pi_apply_eq_sum_univ f (Φ v)]`. Rewrite using `[hw, map_sum, LinearMap.sum_apply]`. Rewrite using `[← h1]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[LinearMap.map_smulₛₗ, LinearMap.smul_apply, starRingEnd_apply, star_star, smul_eq_mul, smul_eq_mul, mul_comm]`. Both sides reduce to the same expression. Establish `hw0 : w = 0` using `S.nondeg.1 w hwv`. Establish `hci : ∀ i, c i = 0`. Introduce `i`.

Use `Fintype.linearIndependent_iff.1 hu (fun i => star (c i)) (by rw [← hw0])` as an intermediate fact. Conclude with `star_eq_zero.1 (this i)`. Apply `hf0` to reduce the goal to its premises. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `y`.

Rewrite using `[LinearMap.pi_apply_eq_sum_univ f y, LinearMap.zero_apply]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Establish `: f (fun j => if i = j then 1 else 0) = 0` using `hci i`. Rewrite using `[this, smul_zero]`. Establish `h1` using `LinearMap.finrank_range_add_finrank_ker Φ`.

Rewrite `h1` using `[hrange, finrank_top, Module.finrank_fintype_fun_eq_card]`. Establish `h2` using `Submodule.finrank_mono hle`. Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_orth_add_le (S : HSpace E) {ι : Type} [Fintype ι] (u : ι → S.V)
    (hu : LinearIndependent E u) (U : Submodule E S.V) (hU : ∀ i, u i ∈ U) :
    finrank E (orth S U) + Fintype.card ι ≤ finrank E S.V := by
  let Φ : S.V →ₗ[E] (ι → E) := LinearMap.pi (fun i => S.hT (u i))
  have hle : orth S U ≤ LinearMap.ker Φ := by
    intro v hv
    rw [LinearMap.mem_ker]
    funext i
    have h1 := (Submodule.mem_iInf _).1 hv (u i)
    have h2 := (Submodule.mem_iInf _).1 h1 (hU i)
    exact h2
  have hrange : LinearMap.range Φ = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hfle⟩ :=
      Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    set c : ι → E := fun i => f (fun j => if i = j then 1 else 0) with hc
    set w : S.V := ∑ i, star (c i) • u i with hw
    have hwv : ∀ v, S.hT w v = 0 := by
      intro v
      have h1 : f (Φ v) = 0 := hfle (LinearMap.mem_range_self Φ v)
      rw [LinearMap.pi_apply_eq_sum_univ f (Φ v)] at h1
      rw [hw, map_sum, LinearMap.sum_apply]
      rw [← h1]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, starRingEnd_apply, star_star, smul_eq_mul,
        smul_eq_mul, mul_comm]
      rfl
    have hw0 : w = 0 := S.nondeg.1 w hwv
    have hci : ∀ i, c i = 0 := by
      intro i
      have := Fintype.linearIndependent_iff.1 hu (fun i => star (c i)) (by rw [← hw0])
      exact star_eq_zero.1 (this i)
    apply hf0
    apply LinearMap.ext
    intro y
    rw [LinearMap.pi_apply_eq_sum_univ f y, LinearMap.zero_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    have : f (fun j => if i = j then 1 else 0) = 0 := hci i
    rw [this, smul_zero]
  have h1 := LinearMap.finrank_range_add_finrank_ker Φ
  rw [hrange, finrank_top, Module.finrank_fintype_fun_eq_card] at h1
  have h2 := Submodule.finrank_mono hle
  omega

/- English proof (translation)
Establish `hUU : ∀ x, x ∈ UU Λ F F' → x ∈ UUE Λ F F'` using `fun x hx => Submodule.subset_span hx`. Establish `hA : XLam Λ F ≤ UU Λ F F'`. Unfold `UU`. Conclude with `le_sup_left.trans (le_sup_left.trans le_sup_left)`. Establish `hB : Submodule.span (𝓞 E) {F.zt} ≤ UU Λ F F'`.

Unfold `UU`. Conclude with `le_sup_right.trans (le_sup_left.trans le_sup_left)`. Establish `hC : XLam Λ F' ≤ UU Λ F F'`. Unfold `UU`. Conclude with `le_sup_right.trans le_sup_left`.

Establish `hD : Submodule.span (𝓞 E) {F'.zt} ≤ UU Λ F F'`. Unfold `UU`. Conclude with `le_sup_right`. Establish `hX : ∀ {T₀ : E} (G : LFlag S r T₀), XLam Λ G ≤ UU Λ F F' → ∀ j : Fin r, G.fl.e j ∈ UUE Λ F F'`. Introduce `T₀ G hG j`.

Take `⟨c, hc, hcv⟩` from `exists_smul_mem Λ hΛ (G.fl.e j)`. Establish `hcX : c • G.fl.e j ∈ XLam Λ G`. Use `Submodule.mem_inf.2 ⟨hcv, ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.restrictScalars_mem, ← algebraMap_smul E c (G.fl.e j)]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)`.

Establish `h1 : c • G.fl.e j ∈ UUE Λ F F'` using `hUU _ (hG hcX)`. Establish `hc' : algebraMap (𝓞 E) E c ≠ 0`. Introduce `h`. Apply `hc` to reduce the goal to its premises. Conclude with `(IsFractionRing.injective (𝓞 E) E) (by rw [h, map_zero])`.

Rewrite `h1` using `[← algebraMap_smul E c (G.fl.e j)]`. Use `Submodule.smul_mem (UUE Λ F F') (algebraMap (𝓞 E) E c)⁻¹ h1` as an intermediate fact. Rewrite `this` using `[smul_smul, inv_mul_cancel₀ hc', one_smul]`. Then use the resulting hypothesis. Introduce and unpack `(i | i)`. Proceed by induction on `i using Fin.lastCases with`.

Consider the case `last => show F.fl.fvec (Fin.last r) ∈ UUE Λ F F'`. Rewrite using `[FlagG.fvec, Fin.snoc_last, ← hL.2]`. Conclude with `hUU _ (hB (Submodule.mem_span_singleton_self _))`. Consider the case `cast j => show F.fl.fvec (Fin.castSucc j) ∈ UUE Λ F F'`. Rewrite using `[FlagG.fvec, Fin.snoc_castSucc]`.

Conclude with `hX F hA j`. Proceed by induction on `i using Fin.lastCases with`. Consider the case `last => show F'.fl.fvec (Fin.last r) ∈ UUE Λ F F'`. Rewrite using `[FlagG.fvec, Fin.snoc_last, ← hL'.2]`. Conclude with `hUU _ (hD (Submodule.mem_span_singleton_self _))`.

Consider the case `cast j => show F'.fl.fvec (Fin.castSucc j) ∈ UUE Λ F F'`. Rewrite using `[FlagG.fvec, Fin.snoc_castSucc]`. Conclude with `hX F' hC j`.
-/
theorem frame_mem_UUE {S : HSpace E} {r : ℕ} {T T' : E} (Λ : Submodule (𝓞 E) S.V)
    (hΛ : Submodule.IsLattice E Λ) (F : LFlag S r T) (F' : LFlag S r T')
    (hL : IsLift Λ F) (hL' : IsLift Λ F') :
    ∀ s, Sum.elim F.fl.fvec F'.fl.fvec s ∈ UUE Λ F F' := by
  have hUU : ∀ x, x ∈ UU Λ F F' → x ∈ UUE Λ F F' := fun x hx => Submodule.subset_span hx
  have hA : XLam Λ F ≤ UU Λ F F' := by
    unfold UU; exact le_sup_left.trans (le_sup_left.trans le_sup_left)
  have hB : Submodule.span (𝓞 E) {F.zt} ≤ UU Λ F F' := by
    unfold UU; exact le_sup_right.trans (le_sup_left.trans le_sup_left)
  have hC : XLam Λ F' ≤ UU Λ F F' := by
    unfold UU; exact le_sup_right.trans le_sup_left
  have hD : Submodule.span (𝓞 E) {F'.zt} ≤ UU Λ F F' := by
    unfold UU; exact le_sup_right

  have hX : ∀ {T₀ : E} (G : LFlag S r T₀), XLam Λ G ≤ UU Λ F F' → ∀ j : Fin r,
      G.fl.e j ∈ UUE Λ F F' := by
    intro T₀ G hG j
    obtain ⟨c, hc, hcv⟩ := exists_smul_mem Λ hΛ (G.fl.e j)
    have hcX : c • G.fl.e j ∈ XLam Λ G := by
      refine Submodule.mem_inf.2 ⟨hcv, ?_⟩
      rw [Submodule.restrictScalars_mem, ← algebraMap_smul E c (G.fl.e j)]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    have h1 : c • G.fl.e j ∈ UUE Λ F F' := hUU _ (hG hcX)
    have hc' : algebraMap (𝓞 E) E c ≠ 0 := by
      intro h; apply hc
      exact (IsFractionRing.injective (𝓞 E) E) (by rw [h, map_zero])
    rw [← algebraMap_smul E c (G.fl.e j)] at h1
    have := Submodule.smul_mem (UUE Λ F F') (algebraMap (𝓞 E) E c)⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hc', one_smul] at this
  rintro (i | i)
  · induction i using Fin.lastCases with
    | last =>
      show F.fl.fvec (Fin.last r) ∈ UUE Λ F F'
      rw [FlagG.fvec, Fin.snoc_last, ← hL.2]
      exact hUU _ (hB (Submodule.mem_span_singleton_self _))
    | cast j =>
      show F.fl.fvec (Fin.castSucc j) ∈ UUE Λ F F'
      rw [FlagG.fvec, Fin.snoc_castSucc]
      exact hX F hA j
  · induction i using Fin.lastCases with
    | last =>
      show F'.fl.fvec (Fin.last r) ∈ UUE Λ F F'
      rw [FlagG.fvec, Fin.snoc_last, ← hL'.2]
      exact hUU _ (hD (Submodule.mem_span_singleton_self _))
    | cast j =>
      show F'.fl.fvec (Fin.castSucc j) ∈ UUE Λ F F'
      rw [FlagG.fvec, Fin.snoc_castSucc]
      exact hX F' hC j

/- English proof (translation)
Introduce `x hx`. Take `⟨p, hp, rfl⟩` from `Submodule.mem_map.1 hx`. Establish `h1` using `(Submodule.mem_inf.1 (Submodule.mem_inf.1 hp).1).1`. Conclude with `(Submodule.mem_prod.1 h1).1`.
-/
theorem Th_le_Hp {S : HSpace E} {r : ℕ} {T T' : E} (Λ : Submodule (𝓞 E) S.V)
    (F : LFlag S r T) (F' F'' : LFlag S r T') (β : S.V ≃ₗ[E] S.V) :
    Th Λ F F' F'' β ≤ Hp Λ F F' := by
  intro x hx
  obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.1 hx
  have h1 := (Submodule.mem_inf.1 (Submodule.mem_inf.1 hp).1).1
  exact (Submodule.mem_prod.1 h1).1

/- English proof (translation)
Introduce `E _ _ _ S r k hdim Λ hΛ T T' F F' F'' β hL hL' hG`. Establish `hu` using `linIndep F.fl F'.fl hG`. Establish `h1` using `finrank_orth_add_le S _ hu (UUE Λ F F') (frame_mem_UUE Λ hΛ F F' hL hL')`. Rewrite `h1` using `[Fintype.card_sum, Fintype.card_fin]`. Establish `h2 : finrank E (Th Λ F F' F'' β) ≤ finrank E (Hp Λ F F')` using `Submodule.finrank_mono (Th_le_Hp Λ F F' F'' β)`.

Establish `h3 : finrank E (Hp Λ F F') = finrank E (orth S (UUE Λ F F'))` using `rfl`. Use `show 1 ≤ k - finrank E (Th Λ F F' F'' β)`. Use linear arithmetic over natural numbers and integers.
-/
theorem corankPosG : PI.PairCorankPos.CorankPosG := by
  intro E _ _ _ S r k hdim Λ hΛ T T' F F' F'' β hL hL' hG
  have hu := linIndep F.fl F'.fl hG
  have h1 := finrank_orth_add_le S _ hu (UUE Λ F F') (frame_mem_UUE Λ hΛ F F' hL hL')
  rw [Fintype.card_sum, Fintype.card_fin] at h1
  have h2 : finrank E (Th Λ F F' F'' β) ≤ finrank E (Hp Λ F F') :=
    Submodule.finrank_mono (Th_le_Hp Λ F F' F'' β)
  have h3 : finrank E (Hp Λ F F') = finrank E (orth S (UUE Λ F F')) := rfl
  show 1 ≤ k - finrank E (Th Λ F F' F'' β)
  omega

end PI.PairCorankPos.W
