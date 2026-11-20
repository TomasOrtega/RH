import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitLoc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFinsetNormOne
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FiniteAdeleSndAlgebraMap
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.SplitChar

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField Topology Filter
open Formalism.IndefR.Fin.U1 GlobalTheory.HeckeSplitAll.Approx
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeckeSplitAll

section Local

variable {F : Type} [Field F] [NumberField F]

def GoodAt (N : ℕ) (Δ α β : F) (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  ‖algebraMap F (v.adicCompletion F) α - 1‖ ≤ ‖(N : v.adicCompletion F)‖ ∧
  ‖algebraMap F (v.adicCompletion F) β‖ ≤ ‖(N : v.adicCompletion F)‖ ∧
  ‖algebraMap F (v.adicCompletion F) (α * α - Δ * (β * β))‖ = 1

/- English proof (translation)
Use `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := x - 1) (y := 1) (by rw [norm_one]; exact h.ne)` as an intermediate fact. Rewrite `this` using `[sub_add_cancel, norm_one, max_eq_right h.le]`. Conclude with `this`.
-/
theorem norm_eq_one_of_sub_lt {K : Type*} [NormedField K] [IsUltrametricDist K] {x : K} (h : ‖x - 1‖ < 1) :
    ‖x‖ = 1 := by
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := x - 1) (y := 1) (by rw [norm_one]; exact h.ne)
  rw [sub_add_cancel, norm_one, max_eq_right h.le] at this
  exact this

/- English proof (translation)
Use `IsUltrametricDist.norm_add_le_max (x - 1) 1` as an intermediate fact. Rewrite `this` using `[sub_add_cancel, norm_one]`. Conclude with `this.trans (max_le h le_rfl)`.
-/
theorem norm_le_one_of_sub_le {K : Type*} [NormedField K] [IsUltrametricDist K] {x : K} (h : ‖x - 1‖ ≤ 1) :
    ‖x‖ ≤ 1 := by
  have := IsUltrametricDist.norm_add_le_max (x - 1) 1
  rw [sub_add_cancel, norm_one] at this
  exact this.trans (max_le h le_rfl)

/- English proof (translation)
Establish `e1 : ‖a * a‖ = ‖a‖ * ‖a‖` using `norm_mul _ _`. Establish `e2 : ‖Δ * (b * b)‖ = ‖b‖ * ‖b‖` using `by rw [norm_mul, norm_mul, hΔ, one_mul]`. Establish `ha0` using `norm_nonneg a`. Establish `hb0` using `norm_nonneg b`. Establish `hab' : ‖a‖ = 1 ∧ ‖b‖ = 1`.

Assume the negation of the conclusion as `hc`. Apply `hn` to reduce the goal to its premises. Break down `hab with h | h` into its components or cases. Establish `hb1 : ‖b‖ < 1` using `lt_of_le_of_ne hb fun h' => hc ⟨h, h'⟩`. Rewrite using `[norm_sub_eq_max v (by rw [e1, e2, h]; nlinarith), e1, e2, h, max_eq_left (by nlinarith), one_mul]`.

Establish `ha1 : ‖a‖ < 1` using `lt_of_le_of_ne ha fun h' => hc ⟨h', h⟩`. Rewrite using `[norm_sub_eq_max v (by rw [e1, e2, h]; nlinarith), e1, e2, h, max_eq_right (by nlinarith), one_mul]`. Establish `hle : ‖a * a - Δ * (b * b)‖ ≤ 1`. Rewrite using `[sub_eq_add_neg]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans ?_` and prove the remaining obligations.

Rewrite using `[norm_neg, e1, e2, hab'.1, hab'.2]`. Simplify using the standard rewrite rules. Use `sq_of_nonint v Δ ((a * a + Δ * (b * b)) / (a * a - Δ * (b * b))) (2 * a * b / (a * a - Δ * (b * b))) h2 hΔ ?_ (Or.inr ?_)` and prove the remaining obligations. Rewrite using `[div_mul_div_comm, div_mul_div_comm, ← mul_div_assoc, div_sub_div_same, div_eq_one_iff_eq (mul_ne_zero hn0 hn0)]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[norm_div, norm_mul, norm_mul, h2, hab'.1, hab'.2, one_mul, one_mul, one_lt_div (norm_pos_iff.2 hn0)]`. Conclude with `lt_of_le_of_ne hle hn`.
-/
theorem unit_or_square (v : HeightOneSpectrum (𝓞 F)) (Δ a b : v.adicCompletion F)
    (h2 : ‖(2 : v.adicCompletion F)‖ = 1) (hΔ : ‖Δ‖ = 1) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hab : ‖a‖ = 1 ∨ ‖b‖ = 1)
    (hn0 : a * a - Δ * (b * b) ≠ 0) (hn : ‖a * a - Δ * (b * b)‖ ≠ 1) : ∃ s, s * s = Δ := by
  have e1 : ‖a * a‖ = ‖a‖ * ‖a‖ := norm_mul _ _
  have e2 : ‖Δ * (b * b)‖ = ‖b‖ * ‖b‖ := by rw [norm_mul, norm_mul, hΔ, one_mul]
  have ha0 := norm_nonneg a
  have hb0 := norm_nonneg b
  have hab' : ‖a‖ = 1 ∧ ‖b‖ = 1 := by
    by_contra hc
    apply hn
    rcases hab with h | h
    · have hb1 : ‖b‖ < 1 := lt_of_le_of_ne hb fun h' => hc ⟨h, h'⟩
      rw [norm_sub_eq_max v (by rw [e1, e2, h]; nlinarith), e1, e2, h, max_eq_left (by nlinarith), one_mul]
    · have ha1 : ‖a‖ < 1 := lt_of_le_of_ne ha fun h' => hc ⟨h', h⟩
      rw [norm_sub_eq_max v (by rw [e1, e2, h]; nlinarith), e1, e2, h, max_eq_right (by nlinarith), one_mul]
  have hle : ‖a * a - Δ * (b * b)‖ ≤ 1 := by
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
    rw [norm_neg, e1, e2, hab'.1, hab'.2]; simp
  refine sq_of_nonint v Δ ((a * a + Δ * (b * b)) / (a * a - Δ * (b * b))) (2 * a * b / (a * a - Δ * (b * b))) h2 hΔ
    ?_ (Or.inr ?_)
  · rw [div_mul_div_comm, div_mul_div_comm, ← mul_div_assoc, div_sub_div_same,
      div_eq_one_iff_eq (mul_ne_zero hn0 hn0)]
    ring
  · rw [norm_div, norm_mul, norm_mul, h2, hab'.1, hab'.2, one_mul, one_mul,
      one_lt_div (norm_pos_iff.2 hn0)]
    exact lt_of_le_of_ne hle hn

/- English proof (translation)
Take `⟨Q, hQ0, hQ⟩` from `exists_nat_small (2 * (Δ : F)) (mul_ne_zero two_ne_zero hΔ)`. Take `⟨α, hα0, hαw, hαv⟩` from `strong_approx v₀ a 1 (N * Q) (mul_ne_zero hN hQ0) ε hε`. Take `⟨P, hP0, hP⟩` from `exists_nat_small α hα0`. Set `s : FiniteAdeleRing (𝓞 F) F` to `RestrictedProduct.mk (fun v => if ‖algebraMap F (v.adicCompletion F) α‖ = 1 then 0 else 1) (Eventually.of_forall fun v => by split_ifs`. Conclude with `zero_mem _`.

Conclude with `one_mem _)`. Take `⟨β, -, hβw, hβv⟩` from `strong_approx v₀ b s (N * Q * P) (mul_ne_zero (mul_ne_zero hN hQ0) hP0) ε hε`. Establish `hn0` using `hns α β hα0`. Take `⟨B, hB⟩` from `exists_finset_norm_one _ hn0`. Establish `key : ∀ v, v ≠ v₀ → ¬ GoodAt N (Δ : F) α β v → ‖algebraMap F (v.adicCompletion F) (α * α - Δ * (β * β))‖ ≠ 1 ∧ ∃ s, s * s = algebraMap F (v.adicCompletion F) Δ`.

Introduce `v hv hg`. Establish `h1 : ‖algebraMap F (v.adicCompletion F) α - 1‖ ≤ ‖((N * Q : ℕ) : v.adicCompletion F)‖` using `hαv v hv`. Establish `h2 : ‖algebraMap F (v.adicCompletion F) β - (if ‖algebraMap F (v.adicCompletion F) α‖ = 1 then 0 else 1)‖ ≤ ‖((N * Q * P : ℕ) : v.adicCompletion F)‖` using `hβv v hv`. Simplify using `only [Nat.cast_mul, norm_mul] at h1 h2`. Establish `hN1` using `norm_nat_le_one v N`.

Establish `hQ1` using `norm_nat_le_one v Q`. Establish `hP1` using `norm_nat_le_one v P`. Establish `hN0` using `norm_nonneg (N : v.adicCompletion F)`. Establish `hQ0'` using `norm_nonneg (Q : v.adicCompletion F)`. Establish `hP0'` using `norm_nonneg (P : v.adicCompletion F)`.

Establish `hΔ1` using `norm_int_le_one v Δ`. Establish `hNQ : ‖(N : v.adicCompletion F)‖ * ‖(Q : v.adicCompletion F)‖ ≤ ‖(N : v.adicCompletion F)‖` using `mul_le_of_le_one_right hN0 hQ1`. Establish `hNQP : ‖(N : v.adicCompletion F)‖ * ‖(Q : v.adicCompletion F)‖ * ‖(P : v.adicCompletion F)‖ ≤ ‖(N : v.adicCompletion F)‖ * ‖(Q : v.adicCompletion F)‖` using `mul_le_of_le_one_right (by positivity) hP1`. Distinguish the cases in `hlt : ‖(N : v.adicCompletion F)‖ * ‖(Q : v.adicCompletion F)‖ < 1`. It suffices to derive a contradiction.

Establish `ha` using `norm_eq_one_of_sub_lt (h1.trans_lt hlt)`. Rewrite `h2` using `[if_pos ha, sub_zero]`. Use `hg ⟨h1.trans hNQ, h2.trans (hNQP.trans hNQ), ?_⟩` and prove the remaining obligations. Establish `hb : ‖algebraMap F (v.adicCompletion F) β‖ < 1` using `(h2.trans hNQP).trans_lt hlt`. Establish `hb0` using `norm_nonneg (algebraMap F (v.adicCompletion F) β)`.

Establish `hlt2 : ‖algebraMap F (v.adicCompletion F) Δ * (algebraMap F (v.adicCompletion F) β * algebraMap F (v.adicCompletion F) β)‖ < 1`. Rewrite using `[norm_mul, norm_mul]`. Conclude with `(mul_le_of_le_one_left (by positivity) hΔ1).trans_lt (by nlinarith)`. Simplify using `only [map_sub, map_mul]`. Rewrite using `[norm_sub_eq_max v (by rw [norm_mul, ha, one_mul]; exact hlt2.ne'), norm_mul, ha, one_mul, max_eq_left hlt2.le]`.

Establish `hN' : ‖(N : v.adicCompletion F)‖ = 1` using `le_antisymm hN1 (by linarith)`. Establish `hQ' : ‖algebraMap F (v.adicCompletion F) (2 * (Δ : F))‖ = 1`. Assume the negation of the conclusion as `hc`. Use `hQ v hc` as an intermediate fact. Rewrite `hlt` using `[hN']`.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite `hQ'` using `[map_mul, map_ofNat, norm_mul]`. Establish `h21 : ‖(2 : v.adicCompletion F)‖ ≤ 1` using `by exact_mod_cast norm_nat_le_one v 2`. Establish `h20` using `norm_nonneg (2 : v.adicCompletion F)`. Establish `hΔ0` using `norm_nonneg (algebraMap F (v.adicCompletion F) Δ)`.

Establish `ha : ‖algebraMap F (v.adicCompletion F) α‖ ≤ 1` using `norm_le_one_of_sub_le (h1.trans (hNQ.trans hN1))`. Establish `hb : ‖algebraMap F (v.adicCompletion F) β‖ ≤ 1 ∧ (‖algebraMap F (v.adicCompletion F) α‖ = 1 ∨ ‖algebraMap F (v.adicCompletion F) β‖ = 1)`. Distinguish the cases in `hc : ‖algebraMap F (v.adicCompletion F) α‖ = 1`. Rewrite `h2` using `[if_pos hc, sub_zero]`. Conclude with `⟨h2.trans (hNQP.trans (hNQ.trans hN1)), Or.inl hc⟩`.

Rewrite `h2` using `[if_neg hc]`. Use `norm_eq_one_of_sub_lt (h2.trans_lt ((mul_le_of_le_one_left hP0' (hNQ.trans hN1)).trans_lt (hP v hc)))` as an intermediate fact. Conclude with `⟨this.le, Or.inr this⟩`. Establish `hn : ‖algebraMap F (v.adicCompletion F) (α * α - Δ * (β * β))‖ ≠ 1` using `fun h => hg ⟨h1.trans hNQ, hN' ▸ hb.1, h⟩`. Use `⟨hn, unit_or_square v _ _ _ (le_antisymm h21 (by nlinarith)) (le_antisymm hΔ1 (by nlinarith)) ha hb.1 hb.2 ?_ ?_⟩` and prove the remaining obligations.

Use `(map_ne_zero (algebraMap F (v.adicCompletion F))).2 hn0` as an intermediate fact. Simplify `this` using `only [map_sub, map_mul]`. Simplify `hn` using `only [map_sub, map_mul]`. Use `⟨α, β, hα0, hαw, hβw, (insert v₀ B).filter fun v => ¬ GoodAt N (Δ : F) α β v, fun v hv => ?_, fun v hv => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hg`.

Rewrite `hv` using `[Finset.mem_filter, Finset.mem_insert, not_and]`. Establish `h` using `not_or.1 (mt hv (not_not.2 hg))`. Conclude with `(key v h.1 hg).1 (hB v h.2)`. Distinguish the cases in `h : v = v₀`. Conclude with `Or.inl h`.

Conclude with `Or.inr (key v h (Finset.mem_filter.1 hv).2).2`.
-/
theorem exists_pair (v₀ : HeightOneSpectrum (𝓞 F)) (N : ℕ) (hN : N ≠ 0) (Δ : 𝓞 F) (hΔ : (Δ : F) ≠ 0)
    (hns : ∀ α β : F, α ≠ 0 → α * α - Δ * (β * β) ≠ 0) (a b : InfiniteAdeleRing F) (ε : ℝ) (hε : 0 < ε) :
    ∃ α β : F, α ≠ 0 ∧ (∀ w : InfinitePlace F, ‖algebraMap F w.Completion α - a w‖ < ε) ∧
      (∀ w : InfinitePlace F, ‖algebraMap F w.Completion β - b w‖ < ε) ∧
      ∃ T : Finset (HeightOneSpectrum (𝓞 F)), (∀ v ∉ T, GoodAt N (Δ : F) α β v) ∧
        ∀ v ∈ T, v = v₀ ∨ ∃ s, s * s = algebraMap F (v.adicCompletion F) Δ := by
  classical
  obtain ⟨Q, hQ0, hQ⟩ := exists_nat_small (2 * (Δ : F)) (mul_ne_zero two_ne_zero hΔ)
  obtain ⟨α, hα0, hαw, hαv⟩ := strong_approx v₀ a 1 (N * Q) (mul_ne_zero hN hQ0) ε hε
  obtain ⟨P, hP0, hP⟩ := exists_nat_small α hα0
  let s : FiniteAdeleRing (𝓞 F) F := RestrictedProduct.mk
    (fun v => if ‖algebraMap F (v.adicCompletion F) α‖ = 1 then 0 else 1)
    (Eventually.of_forall fun v => by
      split_ifs
      · exact zero_mem _
      · exact one_mem _)
  obtain ⟨β, -, hβw, hβv⟩ := strong_approx v₀ b s (N * Q * P) (mul_ne_zero (mul_ne_zero hN hQ0) hP0) ε hε
  have hn0 := hns α β hα0
  obtain ⟨B, hB⟩ := exists_finset_norm_one _ hn0
  have key : ∀ v, v ≠ v₀ → ¬ GoodAt N (Δ : F) α β v →
      ‖algebraMap F (v.adicCompletion F) (α * α - Δ * (β * β))‖ ≠ 1 ∧
        ∃ s, s * s = algebraMap F (v.adicCompletion F) Δ := by
    intro v hv hg
    have h1 : ‖algebraMap F (v.adicCompletion F) α - 1‖ ≤ ‖((N * Q : ℕ) : v.adicCompletion F)‖ := hαv v hv
    have h2 : ‖algebraMap F (v.adicCompletion F) β -
      (if ‖algebraMap F (v.adicCompletion F) α‖ = 1 then 0 else 1)‖ ≤ ‖((N * Q * P : ℕ) : v.adicCompletion F)‖ :=
      hβv v hv
    simp only [Nat.cast_mul, norm_mul] at h1 h2
    have hN1 := norm_nat_le_one v N
    have hQ1 := norm_nat_le_one v Q
    have hP1 := norm_nat_le_one v P
    have hN0 := norm_nonneg (N : v.adicCompletion F)
    have hQ0' := norm_nonneg (Q : v.adicCompletion F)
    have hP0' := norm_nonneg (P : v.adicCompletion F)
    have hΔ1 := norm_int_le_one v Δ
    have hNQ : ‖(N : v.adicCompletion F)‖ * ‖(Q : v.adicCompletion F)‖ ≤ ‖(N : v.adicCompletion F)‖ :=
      mul_le_of_le_one_right hN0 hQ1
    have hNQP : ‖(N : v.adicCompletion F)‖ * ‖(Q : v.adicCompletion F)‖ * ‖(P : v.adicCompletion F)‖ ≤
        ‖(N : v.adicCompletion F)‖ * ‖(Q : v.adicCompletion F)‖ := mul_le_of_le_one_right (by positivity) hP1
    by_cases hlt : ‖(N : v.adicCompletion F)‖ * ‖(Q : v.adicCompletion F)‖ < 1
    · exfalso
      have ha := norm_eq_one_of_sub_lt (h1.trans_lt hlt)
      rw [if_pos ha, sub_zero] at h2
      refine hg ⟨h1.trans hNQ, h2.trans (hNQP.trans hNQ), ?_⟩
      have hb : ‖algebraMap F (v.adicCompletion F) β‖ < 1 := (h2.trans hNQP).trans_lt hlt
      have hb0 := norm_nonneg (algebraMap F (v.adicCompletion F) β)
      have hlt2 : ‖algebraMap F (v.adicCompletion F) Δ *
          (algebraMap F (v.adicCompletion F) β * algebraMap F (v.adicCompletion F) β)‖ < 1 := by
        rw [norm_mul, norm_mul]
        exact (mul_le_of_le_one_left (by positivity) hΔ1).trans_lt (by nlinarith)
      simp only [map_sub, map_mul]
      rw [norm_sub_eq_max v (by rw [norm_mul, ha, one_mul]; exact hlt2.ne'), norm_mul, ha, one_mul,
        max_eq_left hlt2.le]
    · have hN' : ‖(N : v.adicCompletion F)‖ = 1 := le_antisymm hN1 (by linarith)
      have hQ' : ‖algebraMap F (v.adicCompletion F) (2 * (Δ : F))‖ = 1 := by
        by_contra hc
        have := hQ v hc
        rw [hN'] at hlt
        linarith
      rw [map_mul, map_ofNat, norm_mul] at hQ'
      have h21 : ‖(2 : v.adicCompletion F)‖ ≤ 1 := by exact_mod_cast norm_nat_le_one v 2
      have h20 := norm_nonneg (2 : v.adicCompletion F)
      have hΔ0 := norm_nonneg (algebraMap F (v.adicCompletion F) Δ)
      have ha : ‖algebraMap F (v.adicCompletion F) α‖ ≤ 1 := norm_le_one_of_sub_le (h1.trans (hNQ.trans hN1))
      have hb : ‖algebraMap F (v.adicCompletion F) β‖ ≤ 1 ∧
          (‖algebraMap F (v.adicCompletion F) α‖ = 1 ∨ ‖algebraMap F (v.adicCompletion F) β‖ = 1) := by
        by_cases hc : ‖algebraMap F (v.adicCompletion F) α‖ = 1
        · rw [if_pos hc, sub_zero] at h2
          exact ⟨h2.trans (hNQP.trans (hNQ.trans hN1)), Or.inl hc⟩
        · rw [if_neg hc] at h2
          have := norm_eq_one_of_sub_lt (h2.trans_lt
            ((mul_le_of_le_one_left hP0' (hNQ.trans hN1)).trans_lt (hP v hc)))
          exact ⟨this.le, Or.inr this⟩
      have hn : ‖algebraMap F (v.adicCompletion F) (α * α - Δ * (β * β))‖ ≠ 1 := fun h =>
        hg ⟨h1.trans hNQ, hN' ▸ hb.1, h⟩
      refine ⟨hn, unit_or_square v _ _ _ (le_antisymm h21 (by nlinarith)) (le_antisymm hΔ1 (by nlinarith)) ha hb.1 hb.2
        ?_ ?_⟩
      · have := (map_ne_zero (algebraMap F (v.adicCompletion F))).2 hn0
        simpa only [map_sub, map_mul] using this
      · simpa only [map_sub, map_mul] using hn
  refine ⟨α, β, hα0, hαw, hβw, (insert v₀ B).filter fun v => ¬ GoodAt N (Δ : F) α β v, fun v hv => ?_, fun v hv => ?_⟩
  · by_contra hg
    rw [Finset.mem_filter, Finset.mem_insert, not_and] at hv
    have h := not_or.1 (mt hv (not_not.2 hg))
    exact (key v h.1 hg).1 (hB v h.2)
  · by_cases h : v = v₀
    · exact Or.inl h
    · exact Or.inr (key v h (Finset.mem_filter.1 hv).2).2

end Local

section Cut

variable {S R : Type*} [CommRing S] [CommRing R] [Algebra S R]

def cut {ε : S} (hε : ε * ε = ε) (x : Rˣ) : Rˣ where
  val := algebraMap S R ε * x + (1 - algebraMap S R ε)
  inv := algebraMap S R ε * (x⁻¹ : Rˣ) + (1 - algebraMap S R ε)
  val_inv := by
    have h : algebraMap S R ε * algebraMap S R ε = algebraMap S R ε := by rw [← map_mul, hε]
    linear_combination algebraMap S R ε ^ 2 * x.mul_inv + (2 - (x : R) - (x⁻¹ : Rˣ)) * h
  inv_val := by
    have h : algebraMap S R ε * algebraMap S R ε = algebraMap S R ε := by rw [← map_mul, hε]
    linear_combination algebraMap S R ε ^ 2 * x.mul_inv + (2 - (x : R) - (x⁻¹ : Rˣ)) * h

/- English proof (translation)
Take the linear combination `hε`.
-/
theorem idem_compl {ε : S} (hε : ε * ε = ε) : (1 - ε) * (1 - ε) = 1 - ε := by linear_combination hε

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cut_val {ε : S} (hε : ε * ε = ε) (x : Rˣ) :
    (cut hε x : R) = algebraMap S R ε * x + (1 - algebraMap S R ε) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cut_inv {ε : S} (hε : ε * ε = ε) (x : Rˣ) :
    (((cut hε x)⁻¹ : Rˣ) : R) = algebraMap S R ε * (x⁻¹ : Rˣ) + (1 - algebraMap S R ε) := rfl

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Establish `h : algebraMap S R ε * algebraMap S R ε = algebraMap S R ε` using `by rw [← map_mul, hε]`. Rewrite using `[Units.val_mul, cut_val, cut_val, map_sub, map_one]`. Take the linear combination `(2 * (x : R) - x * x - 1) * h`.
-/
theorem cut_mul {ε : S} (hε : ε * ε = ε) (x : Rˣ) : cut hε x * cut (idem_compl hε) x = x := by
  apply Units.ext
  have h : algebraMap S R ε * algebraMap S R ε = algebraMap S R ε := by rw [← map_mul, hε]
  rw [Units.val_mul, cut_val, cut_val, map_sub, map_one]
  linear_combination (2 * (x : R) - x * x - 1) * h

/- English proof (translation)
Simplify using `[mkE]`.
-/
theorem map_mkE {F E : Type} [Field F] [Field E] [Algebra F E] {R R' : Type} [CommRing R] [Algebra F R] [CommRing R']
    [Algebra F R'] (φ : R →ₐ[F] R') (δ : E) (a b : R) :
    (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom (mkE (F := F) δ R a b) =
      mkE (F := F) δ R' (φ a) (φ b) := by
  simp [mkE]

/- English proof (translation)
Rewrite using `[← mkE_one (F := F) δ R, mkE_sub, sub_zero, ha, hb, ← smul_mkE, map_natCast]`.
-/
theorem mkE_sub_one {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R] (δ : E)
    (N : ℕ) (a b za zb : R) (ha : a - 1 = N * za) (hb : b = N * zb) :
    mkE (F := F) δ R a b - 1 = (N : R ⊗[F] E) * mkE (F := F) δ R za zb := by
  rw [← mkE_one (F := F) δ R, mkE_sub, sub_zero, ha, hb, ← smul_mkE, map_natCast]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem af_sub_one {F : Type} [Field F] [NumberField F] (y : Af F) (v : HeightOneSpectrum (𝓞 F)) :
    (y - 1) v = y v - 1 := rfl

end Cut

section Main

variable {D : D7}

/- English proof (translation)
Rewrite using `[← map_one (algebraMap (AF D.host.F) (AE D)), ← map_sub, pt, pt, smul_mkE, algebraMap_eq_mkE δ (AF D.host.F) (1 - ε), mkE_add, add_zero]`.
-/
theorem cut_pt (δ : D.host.E) (ε a b : AF D.host.F) :
    algebraMap (AF D.host.F) (AE D) ε * pt δ a b + (1 - algebraMap (AF D.host.F) (AE D) ε) =
      pt δ (ε * a + (1 - ε)) (ε * b) := by
  rw [← map_one (algebraMap (AF D.host.F) (AE D)), ← map_sub, pt, pt, smul_mkE,
    algebraMap_eq_mkE δ (AF D.host.F) (1 - ε), mkE_add, add_zero]

/- English proof (translation)
The claim follows from `map_mkE (sndA D.host.F) δ a b`.
-/
theorem finPart_pt (δ : D.host.E) (a b : AF D.host.F) :
    finPart D (pt δ a b) = mkE (F := D.host.F) δ (Af D.host.F) a.2 b.2 :=
  map_mkE (sndA D.host.F) δ a b

/- English proof (translation)
The claim follows from `map_mkE (fstA D.host.F) δ a b`.
-/
theorem infPart_pt (δ : D.host.E) (a b : AF D.host.F) :
    infPart D (pt δ a b) = mkE (F := D.host.F) δ (Ainf D.host.F) a.1 b.1 :=
  map_mkE (fstA D.host.F) δ a b

/- English proof (translation)
Use `((continuous_pt δ).tendsto (a, b)).comp (hA.prodMk_nhds hB)` as an intermediate fact. Simplify `this` using `only [Function.comp_def]`.
-/
theorem tendsto_pt (δ : D.host.E) {A B : ℕ → AF D.host.F} {a b : AF D.host.F} (hA : Tendsto A atTop (𝓝 a))
    (hB : Tendsto B atTop (𝓝 b)) : Tendsto (fun k => pt δ (A k) (B k)) atTop (𝓝 (pt δ a b)) := by
  have := ((continuous_pt δ).tendsto (a, b)).comp (hA.prodMk_nhds hB)
  simpa only [Function.comp_def] using this

/- English proof (translation)
The claim follows from `add_mem (AddSubgroup.subset_closure ⟨a, fun v => (norm_le_one_iff_int v _).1 (ha v), 1, rfl⟩) (AddSubgroup.subset_closure ⟨b, fun v => (norm_le_one_iff_int v _).1 (hb v), δ, rfl⟩)`.
-/
theorem mkE_mem_intAE (δ : 𝓞 D.host.E) (a b : Af D.host.F) (ha : ∀ v, ‖a v‖ ≤ 1) (hb : ∀ v, ‖b v‖ ≤ 1) :
    mkE (F := D.host.F) (δ : D.host.E) (Af D.host.F) a b ∈ intAE D :=
  add_mem (AddSubgroup.subset_closure ⟨a, fun v => (norm_le_one_iff_int v _).1 (ha v), 1, rfl⟩)
    (AddSubgroup.subset_closure ⟨b, fun v => (norm_le_one_iff_int v _).1 (hb v), δ, rfl⟩)

/- English proof (translation)
Use `⟨algebraMap F (Af F) ((N : F)⁻¹) * y, fun v => ?_, ?_⟩` and prove the remaining obligations. Use `show ‖algebraMap F (v.adicCompletion F) ((N : F)⁻¹) * y v‖ ≤ 1`. Establish `hN0 : 0 < ‖(N : v.adicCompletion F)‖` using `norm_pos_iff.2 (nat_ne_zero_fin v hN)`. Rewrite using `[map_inv₀, map_natCast, norm_mul, norm_inv, inv_mul_le_iff₀ hN0, mul_one]`. Conclude with `hy v`.

Rewrite using `[← mul_assoc, ← map_natCast (algebraMap F (Af F)) N, ← map_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hN), map_one, one_mul]`.
-/
theorem exists_div_nat {F : Type} [Field F] [NumberField F] (y : Af F) (N : ℕ) (hN : N ≠ 0)
    (hy : ∀ v, ‖y v‖ ≤ ‖(N : v.adicCompletion F)‖) :
    ∃ z : Af F, (∀ v, ‖z v‖ ≤ 1) ∧ y = (N : Af F) * z := by
  refine ⟨algebraMap F (Af F) ((N : F)⁻¹) * y, fun v => ?_, ?_⟩
  · show ‖algebraMap F (v.adicCompletion F) ((N : F)⁻¹) * y v‖ ≤ 1
    have hN0 : 0 < ‖(N : v.adicCompletion F)‖ := norm_pos_iff.2 (nat_ne_zero_fin v hN)
    rw [map_inv₀, map_natCast, norm_mul, norm_inv, inv_mul_le_iff₀ hN0, mul_one]
    exact hy v
  · rw [← mul_assoc, ← map_natCast (algebraMap F (Af F)) N, ← map_mul,
      mul_inv_cancel₀ (Nat.cast_ne_zero.2 hN), map_one, one_mul]

/- English proof (translation)
Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty`. Introduce `_ x a b a' b' hx hx' ha hb hg`. Establish `hg'` using `fun v => hg v (Finset.notMem_empty v)`. Use `Subgroup.subset_closure (Or.inr ⟨?_, ?_, ?_⟩)` and prove the remaining obligations.

Rewrite using `[hx, infPart_pt, ha, hb, mkE_one]`. Take `⟨za, hza, ea⟩` from `exists_div_nat (a.2 - 1) N hN fun v => by rw [af_sub_one]; exact (hg' v).1`. Take `⟨zb, hzb, eb⟩` from `exists_div_nat b.2 N hN fun v => (hg' v).2.1`. Use `⟨_, mkE_mem_intAE δ za zb hza hzb, ?_⟩` and prove the remaining obligations. Rewrite using `[hx, finPart_pt]`.

Conclude with `mkE_sub_one _ N _ _ _ _ ea eb`. Rewrite using `[hx', finPart_pt]`. Conclude with `mkE_mem_intAE δ _ _ (fun v => (hg' v).2.2.1) fun v => (hg' v).2.2.2`. Consider the case `insert v T hvT ih`. Introduce `hT x a b a' b' hx hx' ha hb hg`.

Take `⟨e, he, hee⟩` from `hT v (Finset.mem_insert_self v T)`. Rewrite using `[← cut_mul (epv_sq v) x]`. Use `mul_mem (Subgroup.subset_closure (Or.inl (Or.inr ⟨e, he, ?_⟩))) ?_` and prove the remaining obligations. Establish `h : algebraMap (AF D.host.F) (AE D) (epv v) * algebraMap (AF D.host.F) (AE D) (epv v) = algebraMap (AF D.host.F) (AE D) (epv v)` using `by rw [← map_mul, epv_sq]`. Rewrite using `[hee, cut_val]`.

Take the linear combination `((x : AE D) - 1) * h`. Use `ih (fun w hw => hT w (Finset.mem_insert_of_mem hw)) _ _ _ _ _ (by rw [cut_val, hx, cut_pt]) (by rw [cut_inv, hx', cut_pt]) ?_ ?_ fun w hw => ?_` and prove the remaining obligations. Simplify using `only [finite_adele_fst_add, finite_adele_fst_mul, finite_adele_fst_sub, ha, epv_fst, finite_adele_fst_one]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[finite_adele_fst_mul, hb, mul_zero]`.

Simplify using `only [finite_adele_snd_add, finite_adele_snd_mul, finite_adele_snd_sub, finite_adele_snd_one]`. Distinguish the cases in `hwv : w = v`. Substitute `hwv` using the available equality. Rewrite using `[epv_self]`. Simplify using the standard rewrite rules.

Rewrite using `[epv_ne hwv]`. Simplify using `using hg w (by rw [Finset.mem_insert, not_or]; exact ⟨hwv, hw⟩)`.
-/
theorem mem_grpH_of_good (N : ℕ) (hN : N ≠ 0) (δ : 𝓞 D.host.E) (T : Finset (HeightOneSpectrum (𝓞 D.host.F))) :
    (∀ v ∈ T, ∃ e, IsSplitIdem D e ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) (epv v)) →
    ∀ (x : (AE D)ˣ) (a b a' b' : AF D.host.F), (x : AE D) = pt (δ : D.host.E) a b →
      ((x⁻¹ : (AE D)ˣ) : AE D) = pt (δ : D.host.E) a' b' → a.1 = 1 → b.1 = 0 →
      (∀ v ∉ T, ‖a.2 v - 1‖ ≤ ‖(N : v.adicCompletion D.host.F)‖ ∧ ‖b.2 v‖ ≤ ‖(N : v.adicCompletion D.host.F)‖ ∧
        ‖a'.2 v‖ ≤ 1 ∧ ‖b'.2 v‖ ≤ 1) → x ∈ grpH D N := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro _ x a b a' b' hx hx' ha hb hg
    have hg' := fun v => hg v (Finset.notMem_empty v)
    refine Subgroup.subset_closure (Or.inr ⟨?_, ?_, ?_⟩)
    · rw [hx, infPart_pt, ha, hb, mkE_one]
    · obtain ⟨za, hza, ea⟩ := exists_div_nat (a.2 - 1) N hN fun v => by rw [af_sub_one]; exact (hg' v).1
      obtain ⟨zb, hzb, eb⟩ := exists_div_nat b.2 N hN fun v => (hg' v).2.1
      refine ⟨_, mkE_mem_intAE δ za zb hza hzb, ?_⟩
      rw [hx, finPart_pt]
      exact mkE_sub_one _ N _ _ _ _ ea eb
    · rw [hx', finPart_pt]
      exact mkE_mem_intAE δ _ _ (fun v => (hg' v).2.2.1) fun v => (hg' v).2.2.2
  | insert v T hvT ih =>
    intro hT x a b a' b' hx hx' ha hb hg
    obtain ⟨e, he, hee⟩ := hT v (Finset.mem_insert_self v T)
    rw [← cut_mul (epv_sq v) x]
    refine mul_mem (Subgroup.subset_closure (Or.inl (Or.inr ⟨e, he, ?_⟩))) ?_
    · have h : algebraMap (AF D.host.F) (AE D) (epv v) * algebraMap (AF D.host.F) (AE D) (epv v) =
          algebraMap (AF D.host.F) (AE D) (epv v) := by rw [← map_mul, epv_sq]
      rw [hee, cut_val]
      linear_combination ((x : AE D) - 1) * h
    · refine ih (fun w hw => hT w (Finset.mem_insert_of_mem hw)) _ _ _ _ _
        (by rw [cut_val, hx, cut_pt]) (by rw [cut_inv, hx', cut_pt]) ?_ ?_ fun w hw => ?_
      · simp only [finite_adele_fst_add, finite_adele_fst_mul, finite_adele_fst_sub, ha, epv_fst, finite_adele_fst_one]; ring
      · rw [finite_adele_fst_mul, hb, mul_zero]
      · simp only [finite_adele_snd_add, finite_adele_snd_mul, finite_adele_snd_sub, finite_adele_snd_one]
        by_cases hwv : w = v
        · subst hwv
          rw [epv_self]
          simp
        · rw [epv_ne hwv]
          simpa using hg w (by rw [Finset.mem_insert, not_or]; exact ⟨hwv, hw⟩)

/- English proof (translation)
Take `⟨α, rfl, h1, h2⟩` from `h`. Rewrite using `[epv, pairA_eq_iff]`. Use `⟨rfl, fa_ext fun w => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality.

Rewrite using `[single_self]`. Conclude with `h1`. Rewrite using `[single_ne _ hw]`. Conclude with `h2 w hw`.
-/
theorem placeIdem_eq {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (h : IsPlaceIdem D v ε) : ε = epv v := by
  obtain ⟨α, rfl, h1, h2⟩ := h
  rw [epv, pairA_eq_iff]
  refine ⟨rfl, fa_ext fun w => ?_⟩
  by_cases hw : w = v
  · subst hw; rw [single_self]; exact h1
  · rw [single_ne _ hw]; exact h2 w hw

/- English proof (translation)
Take `⟨δ0, h1, h2⟩` from `exists_delta_D D`. Take `⟨d, hd0, hd⟩` from `((IsFractionRing.isAlgebraic_iff ℤ ℚ D.host.E).2 (Algebra.IsAlgebraic.isAlgebraic δ0)).exists_integral_multiple`. Establish `h3 : D.sp.cm.sig (d • δ0) = -(d • δ0)` using `by rw [map_zsmul, h1, smul_neg]`. Take `⟨Δ, hΔ⟩` from `exists_Delta D (d • δ0) h3`. Establish `h4 : IsIntegral ℤ Δ` using `(isIntegral_algebraMap_iff (algebraMap D.host.F D.host.E).injective).1 (hΔ ▸ hd.mul hd)`.

Conclude with `⟨⟨d • δ0, hd⟩, ⟨Δ, h4⟩, h3, smul_ne_zero hd0 h2, hΔ⟩`.
-/
theorem exists_int_delta (D : D7) : ∃ (δ : 𝓞 D.host.E) (Δ : 𝓞 D.host.F), D.sp.cm.sig (δ : D.host.E) = -δ ∧
    (δ : D.host.E) ≠ 0 ∧ algebraMap D.host.F D.host.E Δ = δ * δ := by
  obtain ⟨δ0, h1, h2⟩ := exists_delta_D D
  obtain ⟨d, hd0, hd⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ D.host.E).2
    (Algebra.IsAlgebraic.isAlgebraic δ0)).exists_integral_multiple
  have h3 : D.sp.cm.sig (d • δ0) = -(d • δ0) := by rw [map_zsmul, h1, smul_neg]
  obtain ⟨Δ, hΔ⟩ := exists_Delta D (d • δ0) h3
  have h4 : IsIntegral ℤ Δ :=
    (isIntegral_algebraMap_iff (algebraMap D.host.F D.host.E).injective).1 (hΔ ▸ hd.mul hd)
  exact ⟨⟨d • δ0, hd⟩, ⟨Δ, h4⟩, h3, smul_ne_zero hd0 h2, hΔ⟩

def epInf (F : Type) [Field F] [NumberField F] : AF F := pairA F 1 0

/- English proof (translation)
Rewrite using `[epInf, pairA_mul, mul_one, mul_zero]`.
-/
theorem epInf_sq (F : Type) [Field F] [NumberField F] : epInf F * epInf F = epInf F := by
  rw [epInf, pairA_mul, mul_one, mul_zero]

/- English proof (translation)
Use `set n : D.host.F := α * α - Δ * (β * β) with hndef`. Establish `hyy : (algebraMap D.host.F D.host.E α + algebraMap D.host.F D.host.E β * δ) * (algebraMap D.host.F D.host.E (α / n) + algebraMap D.host.F D.host.E (-β / n) * δ) = 1`. Establish `h0 : algebraMap D.host.F D.host.E n ≠ 0` using `(map_ne_zero _).2 hn`. Establish `h1 : algebraMap D.host.F D.host.E n = algebraMap D.host.F D.host.E α * algebraMap D.host.F D.host.E α - δ * δ * (algebraMap D.host.F D.host.E β * algebraMap D.host.F D.host.E β)`. Rewrite using `[hndef, map_sub, map_mul, map_mul, map_mul, hΔ]`.

Rewrite using `[map_div₀, map_div₀, map_neg]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[h1]`. Expand and normalize the polynomial expressions, which then agree. Set `y : D.host.Eˣ` to `⟨_, _, hyy, by rw [mul_comm]; exact hyy⟩`.

Set `Y : (AE D)ˣ` to `Units.map (incA D).toMonoidHom y`. Establish `hY : Y ∈ grpH D N` using `Subgroup.subset_closure (Or.inl (Or.inl ⟨y, rfl⟩))`. Establish `hY1 : (Y : AE D) = pt (δ : D.host.E) (algebraMap _ _ α) (algebraMap _ _ β)` using `incA_eq_pt _ α β`. Establish `hY2 : ((Y⁻¹ : (AE D)ˣ) : AE D) = pt (δ : D.host.E) (algebraMap _ _ (α / n)) (algebraMap _ _ (-β / n))` using `incA_eq_pt _ _ _`. Establish `e1 : ∀ c : D.host.F, epInf D.host.F * algebraMap _ _ c + (1 - epInf D.host.F) = pairA D.host.F (algebraMap _ _ c) 1` using `fun c => by`.

Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use `show 1 * algebraMap D.host.F (Ainf D.host.F) c + (1 - 1) = algebraMap D.host.F (Ainf D.host.F) c`. Expand and normalize the polynomial expressions, which then agree. Use `show 0 * algebraMap D.host.F (Af D.host.F) c + (1 - 0) = 1`. Expand and normalize the polynomial expressions, which then agree.

Establish `e2 : ∀ c : D.host.F, epInf D.host.F * algebraMap _ _ c = pairA D.host.F (algebraMap _ _ c) 0` using `fun c => by`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use `show 1 * algebraMap D.host.F (Ainf D.host.F) c = algebraMap D.host.F (Ainf D.host.F) c`. Expand and normalize the polynomial expressions, which then agree. Use `show 0 * algebraMap D.host.F (Af D.host.F) c = 0`.

Expand and normalize the polynomial expressions, which then agree. Establish `e3 : ∀ (c : D.host.F) v, ((1 - epInf D.host.F) * algebraMap _ _ c + (1 - (1 - epInf D.host.F))).2 v = algebraMap D.host.F (v.adicCompletion D.host.F) c` using `fun c v => by show (1 - 0) * algebraMap D.host.F (v.adicCompletion D.host.F) c + (1 - (1 - 0)) = _`. Expand and normalize the polynomial expressions, which then agree. Establish `e4 : ∀ (c : D.host.F) v, ((1 - epInf D.host.F) * algebraMap _ _ c).2 v = algebraMap D.host.F (v.adicCompletion D.host.F) c` using `fun c v => by show (1 - 0) * algebraMap D.host.F (v.adicCompletion D.host.F) c = _`. Expand and normalize the polynomial expressions, which then agree.

Establish `hx : cut (idem_compl (epInf_sq D.host.F)) Y ∈ grpH D N`. Use `mem_grpH_of_good N hN δ T hT _ _ _ _ _ (by rw [cut_val, hY1, cut_pt]) (by rw [cut_inv, hY2, cut_pt]) ?_ ?_ fun v hv => ?_` and prove the remaining obligations. Use `show (1 - 1) * algebraMap D.host.F (Ainf D.host.F) α + (1 - (1 - 1)) = 1`. Expand and normalize the polynomial expressions, which then agree. Use `show (1 - 1) * algebraMap D.host.F (Ainf D.host.F) β = 0`.

Expand and normalize the polynomial expressions, which then agree. Take `⟨g1, g2, g3⟩` from `hg v hv`. Rewrite using `[e3, e4, e3, e4, map_div₀, map_div₀, norm_div, norm_div, g3, div_one, div_one, map_neg, norm_neg]`. Conclude with `⟨g1, g2, norm_le_one_of_sub_le (g1.trans (norm_nat_le_one v N)), g2.trans (norm_nat_le_one v N)⟩`. Use `⟨cut (epInf_sq D.host.F) Y, ?_, by rw [cut_val, hY1, cut_pt, e1, e2], by rw [cut_inv, hY2, cut_pt, e1, e2]⟩` and prove the remaining obligations.

Rewrite using `[eq_mul_inv_of_mul_eq (cut_mul (epInf_sq D.host.F) Y)]`. Conclude with `mul_mem hY (inv_mem hx)`.
-/
theorem exists_mem_grpH (N : ℕ) (hN : N ≠ 0) (δ : 𝓞 D.host.E) (Δ : 𝓞 D.host.F)
    (hδ : D.sp.cm.sig (δ : D.host.E) = -δ) (hδ0 : (δ : D.host.E) ≠ 0)
    (hΔ : algebraMap D.host.F D.host.E Δ = δ * δ) (α β : D.host.F) (hn : α * α - Δ * (β * β) ≠ 0)
    (T : Finset (HeightOneSpectrum (𝓞 D.host.F))) (hg : ∀ v ∉ T, GoodAt N (Δ : D.host.F) α β v)
    (hT : ∀ v ∈ T, ∃ e, IsSplitIdem D e ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) (epv v)) :
    ∃ g ∈ grpH D N,
      (g : AE D) = pt (δ : D.host.E) (pairA D.host.F (algebraMap _ _ α) 1) (pairA D.host.F (algebraMap _ _ β) 0) ∧
      ((g⁻¹ : (AE D)ˣ) : AE D) =
        pt (δ : D.host.E) (pairA D.host.F (algebraMap _ _ (α / (α * α - Δ * (β * β)))) 1)
          (pairA D.host.F (algebraMap _ _ (-β / (α * α - Δ * (β * β)))) 0) := by
  set n : D.host.F := α * α - Δ * (β * β) with hndef
  have hyy : (algebraMap D.host.F D.host.E α + algebraMap D.host.F D.host.E β * δ) *
      (algebraMap D.host.F D.host.E (α / n) + algebraMap D.host.F D.host.E (-β / n) * δ) = 1 := by
    have h0 : algebraMap D.host.F D.host.E n ≠ 0 := (map_ne_zero _).2 hn
    have h1 : algebraMap D.host.F D.host.E n = algebraMap D.host.F D.host.E α * algebraMap D.host.F D.host.E α -
        δ * δ * (algebraMap D.host.F D.host.E β * algebraMap D.host.F D.host.E β) := by
      rw [hndef, map_sub, map_mul, map_mul, map_mul, hΔ]
    rw [map_div₀, map_div₀, map_neg]
    field_simp
    rw [h1]; ring
  let y : D.host.Eˣ := ⟨_, _, hyy, by rw [mul_comm]; exact hyy⟩
  let Y : (AE D)ˣ := Units.map (incA D).toMonoidHom y
  have hY : Y ∈ grpH D N := Subgroup.subset_closure (Or.inl (Or.inl ⟨y, rfl⟩))
  have hY1 : (Y : AE D) = pt (δ : D.host.E) (algebraMap _ _ α) (algebraMap _ _ β) := incA_eq_pt _ α β
  have hY2 : ((Y⁻¹ : (AE D)ˣ) : AE D) = pt (δ : D.host.E) (algebraMap _ _ (α / n)) (algebraMap _ _ (-β / n)) :=
    incA_eq_pt _ _ _
  have e1 : ∀ c : D.host.F, epInf D.host.F * algebraMap _ _ c + (1 - epInf D.host.F) =
      pairA D.host.F (algebraMap _ _ c) 1 := fun c => by
    refine Prod.ext ?_ ?_
    · show 1 * algebraMap D.host.F (Ainf D.host.F) c + (1 - 1) = algebraMap D.host.F (Ainf D.host.F) c
      ring
    · show 0 * algebraMap D.host.F (Af D.host.F) c + (1 - 0) = 1
      ring
  have e2 : ∀ c : D.host.F, epInf D.host.F * algebraMap _ _ c = pairA D.host.F (algebraMap _ _ c) 0 := fun c => by
    refine Prod.ext ?_ ?_
    · show 1 * algebraMap D.host.F (Ainf D.host.F) c = algebraMap D.host.F (Ainf D.host.F) c
      ring
    · show 0 * algebraMap D.host.F (Af D.host.F) c = 0
      ring
  have e3 : ∀ (c : D.host.F) v, ((1 - epInf D.host.F) * algebraMap _ _ c + (1 - (1 - epInf D.host.F))).2 v =
      algebraMap D.host.F (v.adicCompletion D.host.F) c := fun c v => by
    show (1 - 0) * algebraMap D.host.F (v.adicCompletion D.host.F) c + (1 - (1 - 0)) = _
    ring
  have e4 : ∀ (c : D.host.F) v, ((1 - epInf D.host.F) * algebraMap _ _ c).2 v =
      algebraMap D.host.F (v.adicCompletion D.host.F) c := fun c v => by
    show (1 - 0) * algebraMap D.host.F (v.adicCompletion D.host.F) c = _
    ring
  have hx : cut (idem_compl (epInf_sq D.host.F)) Y ∈ grpH D N := by
    refine mem_grpH_of_good N hN δ T hT _ _ _ _ _ (by rw [cut_val, hY1, cut_pt]) (by rw [cut_inv, hY2, cut_pt])
      ?_ ?_ fun v hv => ?_
    · show (1 - 1) * algebraMap D.host.F (Ainf D.host.F) α + (1 - (1 - 1)) = 1
      ring
    · show (1 - 1) * algebraMap D.host.F (Ainf D.host.F) β = 0
      ring
    · obtain ⟨g1, g2, g3⟩ := hg v hv
      rw [e3, e4, e3, e4, map_div₀, map_div₀, norm_div, norm_div, g3, div_one, div_one, map_neg, norm_neg]
      exact ⟨g1, g2, norm_le_one_of_sub_le (g1.trans (norm_nat_le_one v N)), g2.trans (norm_nat_le_one v N)⟩
  refine ⟨cut (epInf_sq D.host.F) Y, ?_, by rw [cut_val, hY1, cut_pt, e1, e2], by rw [cut_inv, hY2, cut_pt, e1, e2]⟩
  rw [eq_mul_inv_of_mul_eq (cut_mul (epInf_sq D.host.F) Y)]
  exact mul_mem hY (inv_mem hx)

/- English proof (translation)
Take `⟨δ, Δ, hδ, hδ0, hΔ⟩` from `exists_int_delta D`. Establish `hΔ0 : (Δ : D.host.F) ≠ 0`. Introduce `h`. Rewrite `hΔ` using `[h, map_zero]`. Conclude with `hδ0 (mul_self_eq_zero.mp hΔ.symm)`.

Establish `hns : ∀ α β : D.host.F, α ≠ 0 → α * α - Δ * (β * β) ≠ 0`. Introduce `α β hα h`. Establish `hli` using `LinearIndependent.pair_iff.1 (linIndep_one_delta D.sp.cm.sig (δ : D.host.E) hδ hδ0)`. Establish `h1 : (α • (1 : D.host.E) + β • (δ : D.host.E)) * (α • (1 : D.host.E) + (-β) • (δ : D.host.E)) = 0`. Use `congrArg (algebraMap D.host.F D.host.E) h` as an intermediate fact.

Rewrite `this` using `[map_sub, map_mul, map_mul, map_mul, hΔ, map_zero]`. Simplify using `only [Algebra.smul_def, map_neg]`. Take the linear combination `this`. Break down `mul_eq_zero.1 h1 with h2 | h2` into its components or cases. Conclude with `hα (hli _ _ h2).1`.

Conclude with `hα (hli _ _ h2).1`. Take `⟨e₀, he₀⟩` from `Formalism.IndefR.Fin.SplitChar.exists_splitIdem_D D`. Take `⟨v₀, ε₀, hε₀, hee₀⟩` from `he₀.2.2`. Rewrite `hee₀` using `[placeIdem_eq hε₀]`. Take `⟨a, b, hab⟩ : ∃ a b, (z : AE D) = pt (δ : D.host.E) a b` from `⟨_, _, (pt_co _ hδ hδ0 _).symm⟩`.

Take `⟨a', b', hab'⟩ : ∃ a b, ((z⁻¹ : (AE D)ˣ) : AE D) = pt (δ : D.host.E) a b` from `⟨_, _, (pt_co _ hδ hδ0 _).symm⟩`. Establish `hz' : finPart D ((z⁻¹ : (AE D)ˣ) : AE D) = 1`. Use `congrArg (finPart D) z.mul_inv` as an intermediate fact. Rewrite `this` using `[map_mul, hz, one_mul, map_one]`. Then use the resulting hypothesis. Rewrite `hz` using `[hab, finPart_pt, ← mkE_one (F := D.host.F) (δ : D.host.E) (Af D.host.F)]`.

Rewrite `hz'` using `[hab', finPart_pt, ← mkE_one (F := D.host.F) (δ : D.host.E) (Af D.host.F)]`. Take `⟨f1, f2⟩` from `mkE_inj D.sp.cm.sig _ hδ hδ0 D.sp.cm.deg2 _ hz`. Take `⟨f1', f2'⟩` from `mkE_inj D.sp.cm.sig _ hδ hδ0 D.sp.cm.deg2 _ hz'`. Establish `hmul` using `z.mul_inv`. Rewrite `hmul` using `[hab, hab', pt_mul _ _ hΔ, ← pt_one (δ : D.host.E)]`.

Take `⟨m1, m2⟩` from `pt_inj _ hδ hδ0 hmul`. Establish `hch` using `fun k : ℕ => exists_pair v₀ N hN.ne' Δ hΔ0 hns a.1 b.1 (1 / ((k : ℝ) + 1)) Nat.one_div_pos_of_nat`. Use `choose α β hα0 hα hβ T hg hT using hch`. Establish `hG` using `fun k => exists_mem_grpH N hN.ne' δ Δ hδ hδ0 hΔ (α k) (β k) (hns _ _ (hα0 k)) (T k) (hg k) fun v hv => by`. Break down `hT k v hv with rfl | ⟨s, hs⟩` into its components or cases.

Conclude with `⟨e₀, he₀, hee₀⟩`. Conclude with `exists_splitIdem' _ hδ hδ0 _ hΔ v s hs`. Use `choose g hgm hg1 hg2 using hG`. Establish `tα : ∀ w, Tendsto (fun k => algebraMap D.host.F w.Completion (α k)) atTop (𝓝 (a.1 w))` using `fun w => tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ => norm_nonneg _) (fun k => (hα k w).le) tendsto_one_div_add_atTop_nhds_zero_nat)`. Establish `tβ : ∀ w, Tendsto (fun k => algebraMap D.host.F w.Completion (β k)) atTop (𝓝 (b.1 w))` using `fun w => tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ => norm_nonneg _) (fun k => (hβ k w).le) tendsto_one_div_add_atTop_nhds_zero_nat)`.

Establish `tinv : ∀ w, Tendsto (fun k => algebraMap D.host.F w.Completion (α k / (α k * α k - Δ * (β k * β k)))) atTop (𝓝 (a'.1 w)) ∧ Tendsto (fun k => algebraMap D.host.F w.Completion (-β k / (α k * α k - Δ * (β k * β k)))) atTop (𝓝 (b'.1 w))` using `fun w => by`. Establish `p1 : a.1 w * a'.1 w + algebraMap D.host.F w.Completion Δ * (b.1 w * b'.1 w) = 1` using `congrArg (fun x : AF D.host.F => x.1 w) m1`. Establish `p2 : a.1 w * b'.1 w + b.1 w * a'.1 w = 0` using `congrArg (fun x : AF D.host.F => x.1 w) m2`. Establish `h0 : a.1 w * a.1 w - algebraMap D.host.F w.Completion Δ * (b.1 w * b.1 w) ≠ 0` using `left_ne_zero_of_mul_eq_one (b := a'.1 w * a'.1 w - algebraMap D.host.F w.Completion Δ * (b'.1 w * b'.1 w)) (by`. Take the linear combination `(a.1 w * a'.1 w + algebraMap D.host.F w.Completion Δ * (b.1 w * b'.1 w) + 1) * p1 - algebraMap D.host.F w.Completion Δ * (a.1 w * b'.1 w + b.1 w * a'.1 w) * p2)`.

Establish `tn` using `((tα w).mul (tα w)).sub (((tβ w).mul (tβ w)).const_mul (algebraMap D.host.F w.Completion Δ))`. Establish `q1 : a'.1 w = a.1 w / (a.1 w * a.1 w - algebraMap D.host.F w.Completion Δ * (b.1 w * b.1 w))`. Rewrite using `[eq_div_iff h0]`. Take the linear combination `a.1 w * p1 - algebraMap D.host.F w.Completion Δ * b.1 w * p2`. Establish `q2 : b'.1 w = -b.1 w / (a.1 w * a.1 w - algebraMap D.host.F w.Completion Δ * (b.1 w * b.1 w))`.

Rewrite using `[eq_div_iff h0]`. Take the linear combination `a.1 w * p2 - b.1 w * p1`. Rewrite using `[q1, q2]`. Simplify using `only [map_div₀, map_sub, map_mul, map_neg]`. Conclude with `⟨(tα w).div tn h0, (tβ w).neg.div tn h0⟩`.

Establish `tpt : ∀ (c d : ℕ → D.host.F) (A B : AF D.host.F), A.2 = 1 → B.2 = 0 → (∀ w, Tendsto (fun k => algebraMap D.host.F w.Completion (c k)) atTop (𝓝 (A.1 w))) → (∀ w, Tendsto (fun k => algebraMap D.host.F w.Completion (d k)) atTop (𝓝 (B.1 w))) → Tendsto (fun k => pt (δ : D.host.E) (pai …`. Introduce `c d A B hA hB hc hd`. Establish `t1 : Tendsto (fun k => pairA D.host.F (algebraMap _ _ (c k)) 1) atTop (𝓝 A)`. Rewrite using `[← hA]`. Conclude with `Tendsto.prodMk_nhds (tendsto_pi_nhds.2 hc) tendsto_const_nhds`.

Establish `t2 : Tendsto (fun k => pairA D.host.F (algebraMap _ _ (d k)) 0) atTop (𝓝 B)`. Rewrite using `[← hB]`. Conclude with `Tendsto.prodMk_nhds (tendsto_pi_nhds.2 hd) tendsto_const_nhds`. Conclude with `tendsto_pt _ t1 t2`. Use `mem_closure_of_tendsto (f := g) (b := atTop) ?_ (Eventually.of_forall hgm)` and prove the remaining obligations.

Use `Units.isInducing_embedProduct.tendsto_nhds_iff.2 (Tendsto.prodMk_nhds ?_ ?_)` and prove the remaining obligations. Use `show Tendsto (fun k => (g k : AE D)) atTop (𝓝 (z : AE D))`. Simplify using `only [hg1, hab]`. Conclude with `tpt _ _ _ _ f1 f2 tα tβ`. Use `(MulOpposite.continuous_op.tendsto _).comp ?_ show Tendsto (fun k => (((g k)⁻¹ : (AE D)ˣ) : AE D)) atTop (𝓝 ((z⁻¹ : (AE D)ˣ) : AE D))` and prove the remaining obligations.

Simplify using `only [hg2, hab']`. Conclude with `tpt _ _ _ _ f1' f2' (fun w => (tinv w).1) fun w => (tinv w).2`.
-/
theorem mem_closure_grpH_of_finPart_eq_one (D : D7) (N : ℕ) (hN : 0 < N) (z : (AE D)ˣ)
    (hz : finPart D (z : AE D) = 1) : z ∈ closure (grpH D N : Set (AE D)ˣ) := by
  obtain ⟨δ, Δ, hδ, hδ0, hΔ⟩ := exists_int_delta D
  have hΔ0 : (Δ : D.host.F) ≠ 0 := by
    intro h; rw [h, map_zero] at hΔ; exact hδ0 (mul_self_eq_zero.mp hΔ.symm)
  have hns : ∀ α β : D.host.F, α ≠ 0 → α * α - Δ * (β * β) ≠ 0 := by
    intro α β hα h
    have hli := LinearIndependent.pair_iff.1 (linIndep_one_delta D.sp.cm.sig (δ : D.host.E) hδ hδ0)
    have h1 : (α • (1 : D.host.E) + β • (δ : D.host.E)) * (α • (1 : D.host.E) + (-β) • (δ : D.host.E)) = 0 := by
      have := congrArg (algebraMap D.host.F D.host.E) h
      rw [map_sub, map_mul, map_mul, map_mul, hΔ, map_zero] at this
      simp only [Algebra.smul_def, map_neg]
      linear_combination this
    rcases mul_eq_zero.1 h1 with h2 | h2
    · exact hα (hli _ _ h2).1
    · exact hα (hli _ _ h2).1
  obtain ⟨e₀, he₀⟩ := Formalism.IndefR.Fin.SplitChar.exists_splitIdem_D D
  obtain ⟨v₀, ε₀, hε₀, hee₀⟩ := he₀.2.2
  rw [placeIdem_eq hε₀] at hee₀
  obtain ⟨a, b, hab⟩ : ∃ a b, (z : AE D) = pt (δ : D.host.E) a b := ⟨_, _, (pt_co _ hδ hδ0 _).symm⟩
  obtain ⟨a', b', hab'⟩ : ∃ a b, ((z⁻¹ : (AE D)ˣ) : AE D) = pt (δ : D.host.E) a b :=
    ⟨_, _, (pt_co _ hδ hδ0 _).symm⟩
  have hz' : finPart D ((z⁻¹ : (AE D)ˣ) : AE D) = 1 := by
    have := congrArg (finPart D) z.mul_inv
    rwa [map_mul, hz, one_mul, map_one] at this
  rw [hab, finPart_pt, ← mkE_one (F := D.host.F) (δ : D.host.E) (Af D.host.F)] at hz
  rw [hab', finPart_pt, ← mkE_one (F := D.host.F) (δ : D.host.E) (Af D.host.F)] at hz'
  obtain ⟨f1, f2⟩ := mkE_inj D.sp.cm.sig _ hδ hδ0 D.sp.cm.deg2 _ hz
  obtain ⟨f1', f2'⟩ := mkE_inj D.sp.cm.sig _ hδ hδ0 D.sp.cm.deg2 _ hz'
  have hmul := z.mul_inv
  rw [hab, hab', pt_mul _ _ hΔ, ← pt_one (δ : D.host.E)] at hmul
  obtain ⟨m1, m2⟩ := pt_inj _ hδ hδ0 hmul
  have hch := fun k : ℕ => exists_pair v₀ N hN.ne' Δ hΔ0 hns a.1 b.1 (1 / ((k : ℝ) + 1)) Nat.one_div_pos_of_nat
  choose α β hα0 hα hβ T hg hT using hch
  have hG := fun k => exists_mem_grpH N hN.ne' δ Δ hδ hδ0 hΔ (α k) (β k) (hns _ _ (hα0 k)) (T k) (hg k) fun v hv => by
    rcases hT k v hv with rfl | ⟨s, hs⟩
    · exact ⟨e₀, he₀, hee₀⟩
    · exact exists_splitIdem' _ hδ hδ0 _ hΔ v s hs
  choose g hgm hg1 hg2 using hG
  have tα : ∀ w, Tendsto (fun k => algebraMap D.host.F w.Completion (α k)) atTop (𝓝 (a.1 w)) := fun w =>
    tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ => norm_nonneg _) (fun k => (hα k w).le)
      tendsto_one_div_add_atTop_nhds_zero_nat)
  have tβ : ∀ w, Tendsto (fun k => algebraMap D.host.F w.Completion (β k)) atTop (𝓝 (b.1 w)) := fun w =>
    tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ => norm_nonneg _) (fun k => (hβ k w).le)
      tendsto_one_div_add_atTop_nhds_zero_nat)
  have tinv : ∀ w, Tendsto (fun k => algebraMap D.host.F w.Completion (α k / (α k * α k - Δ * (β k * β k)))) atTop
      (𝓝 (a'.1 w)) ∧ Tendsto (fun k => algebraMap D.host.F w.Completion (-β k / (α k * α k - Δ * (β k * β k)))) atTop
      (𝓝 (b'.1 w)) := fun w => by
    have p1 : a.1 w * a'.1 w + algebraMap D.host.F w.Completion Δ * (b.1 w * b'.1 w) = 1 :=
      congrArg (fun x : AF D.host.F => x.1 w) m1
    have p2 : a.1 w * b'.1 w + b.1 w * a'.1 w = 0 := congrArg (fun x : AF D.host.F => x.1 w) m2
    have h0 : a.1 w * a.1 w - algebraMap D.host.F w.Completion Δ * (b.1 w * b.1 w) ≠ 0 :=
      left_ne_zero_of_mul_eq_one (b := a'.1 w * a'.1 w - algebraMap D.host.F w.Completion Δ * (b'.1 w * b'.1 w)) (by
        linear_combination (a.1 w * a'.1 w + algebraMap D.host.F w.Completion Δ * (b.1 w * b'.1 w) + 1) * p1 -
          algebraMap D.host.F w.Completion Δ * (a.1 w * b'.1 w + b.1 w * a'.1 w) * p2)
    have tn := ((tα w).mul (tα w)).sub (((tβ w).mul (tβ w)).const_mul (algebraMap D.host.F w.Completion Δ))
    have q1 : a'.1 w = a.1 w / (a.1 w * a.1 w - algebraMap D.host.F w.Completion Δ * (b.1 w * b.1 w)) := by
      rw [eq_div_iff h0]
      linear_combination a.1 w * p1 - algebraMap D.host.F w.Completion Δ * b.1 w * p2
    have q2 : b'.1 w = -b.1 w / (a.1 w * a.1 w - algebraMap D.host.F w.Completion Δ * (b.1 w * b.1 w)) := by
      rw [eq_div_iff h0]
      linear_combination a.1 w * p2 - b.1 w * p1
    rw [q1, q2]
    simp only [map_div₀, map_sub, map_mul, map_neg]
    exact ⟨(tα w).div tn h0, (tβ w).neg.div tn h0⟩
  have tpt : ∀ (c d : ℕ → D.host.F) (A B : AF D.host.F), A.2 = 1 → B.2 = 0 →
      (∀ w, Tendsto (fun k => algebraMap D.host.F w.Completion (c k)) atTop (𝓝 (A.1 w))) →
      (∀ w, Tendsto (fun k => algebraMap D.host.F w.Completion (d k)) atTop (𝓝 (B.1 w))) →
      Tendsto (fun k => pt (δ : D.host.E) (pairA D.host.F (algebraMap _ _ (c k)) 1)
        (pairA D.host.F (algebraMap _ _ (d k)) 0)) atTop (𝓝 (pt (δ : D.host.E) A B)) := by
    intro c d A B hA hB hc hd
    have t1 : Tendsto (fun k => pairA D.host.F (algebraMap _ _ (c k)) 1) atTop (𝓝 A) := by
      rw [← hA]
      exact Tendsto.prodMk_nhds (tendsto_pi_nhds.2 hc) tendsto_const_nhds
    have t2 : Tendsto (fun k => pairA D.host.F (algebraMap _ _ (d k)) 0) atTop (𝓝 B) := by
      rw [← hB]
      exact Tendsto.prodMk_nhds (tendsto_pi_nhds.2 hd) tendsto_const_nhds
    exact tendsto_pt _ t1 t2
  refine mem_closure_of_tendsto (f := g) (b := atTop) ?_ (Eventually.of_forall hgm)
  refine Units.isInducing_embedProduct.tendsto_nhds_iff.2 (Tendsto.prodMk_nhds ?_ ?_)
  · show Tendsto (fun k => (g k : AE D)) atTop (𝓝 (z : AE D))
    simp only [hg1, hab]
    exact tpt _ _ _ _ f1 f2 tα tβ
  · refine (MulOpposite.continuous_op.tendsto _).comp ?_
    show Tendsto (fun k => (((g k)⁻¹ : (AE D)ˣ) : AE D)) atTop (𝓝 ((z⁻¹ : (AE D)ˣ) : AE D))
    simp only [hg2, hab']
    exact tpt _ _ _ _ f1' f2' (fun w => (tinv w).1) fun w => (tinv w).2

end Main

end GlobalTheory.HeckeSplitAll

end
