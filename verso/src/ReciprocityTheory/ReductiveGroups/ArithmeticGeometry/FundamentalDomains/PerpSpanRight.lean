import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ExistsUnitaryBasisSameFlag
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LminorSubmatrixCastSucc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.UMatUpper

namespace ReciprocityTheory.ChartRestriction.G.FD.GramSchmidtSelfImaginary

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {r : ℕ}
  (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)

def hL (v : Fin r → ℂ) : (Fin r → ℂ) →ₗ[ℂ] ℂ where
  toFun u := hermC τ G u v
  map_add' u u' := hermC_add_left τ G u u' v
  map_smul' c u := by simp [hermC_smul_left]

/- English proof (translation)
Introduce `y hy`. Establish `hle : Submodule.span ℂ s ≤ LinearMap.ker (hL τ G v)` using `Submodule.span_le.mpr (fun z hz => LinearMap.mem_ker.mpr (h z hz))`. Conclude with `LinearMap.mem_ker.mp (hle hy)`.
-/
theorem perp_span {s : Set (Fin r → ℂ)} {v : Fin r → ℂ} (h : ∀ y ∈ s, hermC τ G y v = 0) :
    ∀ y ∈ Submodule.span ℂ s, hermC τ G y v = 0 := by
  intro y hy
  have hle : Submodule.span ℂ s ≤ LinearMap.ker (hL τ G v) :=
    Submodule.span_le.mpr (fun z hz => LinearMap.mem_ker.mpr (h z hz))
  exact LinearMap.mem_ker.mp (hle hy)

/- English proof (translation)
Introduce `y hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx => exact h x hx`. Consider the case `zero => simp [hermC]`. Consider the case `add x y _ _ hx hy`.

Establish `e : hermC τ G v (x + y) = hermC τ G v x + hermC τ G v y`. Simplify using `only [hermC, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]`. Rewrite using `[e, hx, hy, add_zero]`. Consider the case `smul c x _ hx`. Establish `e : hermC τ G v (c • x) = conj c * hermC τ G v x`.

Simplify using `only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, hx, mul_zero]`.
-/
theorem perp_span_right (hG : ∀ a b, cc (G a b) = G b a) {s : Set (Fin r → ℂ)} {v : Fin r → ℂ}
    (h : ∀ y ∈ s, hermC τ G v y = 0) : ∀ y ∈ Submodule.span ℂ s, hermC τ G v y = 0 := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => simp [hermC]
  | add x y _ _ hx hy =>
    have e : hermC τ G v (x + y) = hermC τ G v x + hermC τ G v y := by
      simp only [hermC, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]
    rw [e, hx, hy, add_zero]
  | smul c x _ hx =>
    have e : hermC τ G v (c • x) = conj c * hermC τ G v x := by
      simp only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
      ring
    rw [e, hx, mul_zero]

/- English proof (translation)
Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨j, hj, rfl⟩` from `hx`. Use `⟨Pi.single j 1, fun i hi => ?_, ?_⟩` and prove the remaining obligations. Establish `hij : i ≠ j` using `fun e => hi (e ▸ hj)`.

Simplify using `[Pi.single_apply, hij]`. Simplify using `[Pi.single_apply]`. Consider the case `zero => exact ⟨0, fun _ _ => rfl, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨w, hw, rfl⟩` from `hx`.

Take `⟨w', hw', rfl⟩` from `hy`. Use `⟨w + w', fun i hi => by simp [hw i hi, hw' i hi], ?_⟩` and prove the remaining obligations. Simplify using `[add_smul, Finset.sum_add_distrib]`. Consider the case `smul c x _ hx`. Take `⟨w, hw, rfl⟩` from `hx`.

Use `⟨c • w, fun i hi => by simp [hw i hi], ?_⟩` and prove the remaining obligations. Simplify using `[Finset.smul_sum, smul_smul]`.
-/
theorem coef_of_mem {n : ℕ} (Y : Fin n → Fin r → ℂ) (S : Set (Fin n)) {v : Fin r → ℂ}
    (hv : v ∈ Submodule.span ℂ (Y '' S)) :
    ∃ w : Fin n → ℂ, (∀ j, j ∉ S → w j = 0) ∧ v = ∑ j, w j • Y j := by
  classical
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, hj, rfl⟩ := hx
    refine ⟨Pi.single j 1, fun i hi => ?_, ?_⟩
    · have hij : i ≠ j := fun e => hi (e ▸ hj)
      simp [Pi.single_apply, hij]
    · simp [Pi.single_apply]
  | zero => exact ⟨0, fun _ _ => rfl, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨w, hw, rfl⟩ := hx
    obtain ⟨w', hw', rfl⟩ := hy
    refine ⟨w + w', fun i hi => by simp [hw i hi, hw' i hi], ?_⟩
    simp [add_smul, Finset.sum_add_distrib]
  | smul c x _ hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    refine ⟨c • w, fun i hi => by simp [hw i hi], ?_⟩
    simp [Finset.smul_sum, smul_smul]

/- English proof (translation)
Use `Submodule.sum_mem _ (fun j _ => ?_)` and prove the remaining obligations. Distinguish the cases in `hj : j ∈ S`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)`. Rewrite using `[hw j hj, zero_smul]`. Conclude with `Submodule.zero_mem _`.
-/
theorem sum_mem_of {n : ℕ} (Y : Fin n → Fin r → ℂ) (S : Set (Fin n)) (w : Fin n → ℂ)
    (hw : ∀ j, j ∉ S → w j = 0) : ∑ j, w j • Y j ∈ Submodule.span ℂ (Y '' S) := by
  refine Submodule.sum_mem _ (fun j _ => ?_)
  by_cases hj : j ∈ S
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)
  · rw [hw j hj, zero_smul]
    exact Submodule.zero_mem _

variable (hG : ∀ a b, cc (G a b) = G b a)
include hG

/- English proof (translation)
Establish `hτ : ∀ a b, conj (τ (G a b)) = τ (G b a)`. Introduce `a b`. Rewrite using `[← hG a b]`. Use `first`. Consider the case `exact (NumberField.IsCMField.complexEmbedding_complexConj τ (G a b)).symm`.

Consider the case `exact (IsCMField.complexEmbedding_complexConj τ (G a b)).symm`. Consider the case `(simp only [cc]; exact (NumberField.IsCMField.complexEmbedding_complexConj τ (G a b)).symm)`. Consider the case `(simp [cc])`. Establish `hc : conj (hermC τ G v v) = hermC τ G v v`. Simplify using `only [hermC, map_sum, map_mul, Complex.conj_conj]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))` and prove the remaining obligations. Rewrite using `[hτ]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `Complex.conj_eq_iff_im.mp hc`.
-/
theorem hC_self_im (v : Fin r → ℂ) : (hermC τ G v v).im = 0 := by
  have hτ : ∀ a b, conj (τ (G a b)) = τ (G b a) := by
    intro a b
    rw [← hG a b]
    first
    | exact (NumberField.IsCMField.complexEmbedding_complexConj τ (G a b)).symm
    | exact (IsCMField.complexEmbedding_complexConj τ (G a b)).symm
    | (simp only [cc]; exact (NumberField.IsCMField.complexEmbedding_complexConj τ (G a b)).symm)
    | (simp [cc])
  have hc : conj (hermC τ G v v) = hermC τ G v v := by
    simp only [hermC, map_sum, map_mul, Complex.conj_conj]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    rw [hτ]
    ring
  exact Complex.conj_eq_iff_im.mp hc

/- English proof (translation)
Take `⟨ε, hε⟩ : ∃ ε : Fin n → ℂ, ε = fun c : Fin n => (if (c : ℕ) < p then 1 else -1 : ℂ)` from `⟨fun c : Fin n => (if (c : ℕ) < p then 1 else -1 : ℂ), rfl⟩`. Establish `hτ : ∀ a b, conj (τ (G a b)) = τ (G b a)`. Introduce `a b`. Rewrite using `[← hG a b]`. Use `first`.

Consider the case `exact (NumberField.IsCMField.complexEmbedding_complexConj τ (G a b)).symm`. Consider the case `exact (IsCMField.complexEmbedding_complexConj τ (G a b)).symm`. Consider the case `(simp only [cc]; exact (NumberField.IsCMField.complexEmbedding_complexConj τ (G a b)).symm)`. Consider the case `(simp [cc])`. Establish `csym : ∀ u w, conj (hermC τ G u w) = hermC τ G w u`.

Introduce `u w`. Simplify using `only [hermC, map_sum, map_mul, Complex.conj_conj]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))` and prove the remaining obligations. Rewrite using `[hτ]`.

Expand and normalize the polynomial expressions, which then agree. Establish `smulL : ∀ (c : ℂ) u w, hermC τ G (c • u) w = c * hermC τ G u w` using `fun c u w => map_smul (hL τ G w) c u`. Establish `subL : ∀ u u' w, hermC τ G (u - u') w = hermC τ G u w - hermC τ G u' w` using `fun u u' w => map_sub (hL τ G w) u u'`. Establish `sumL : ∀ (s : Finset (Fin n)) (f : Fin n → Fin r → ℂ) w, hermC τ G (∑ a ∈ s, f a) w = ∑ a ∈ s, hermC τ G (f a) w` using `fun s f w => map_sum (hL τ G w) f s`. Establish `smulR : ∀ (c : ℂ) u w, hermC τ G u (c • w) = conj c * hermC τ G u w`.

Introduce `c u w`. Rewrite using `[← csym, smulL, map_mul, csym]`. Establish `cross : ∀ a c : Fin n, ¬((a : ℕ) < p ↔ (c : ℕ) < p) → ∀ u ∈ Submodule.span ℂ (Y '' {j | ((j : ℕ) < p ↔ (a : ℕ) < p)}), ∀ w ∈ Submodule.span ℂ (Y '' {j | ((j : ℕ) < p ↔ (c : ℕ) < p)}), hermC τ G u w = 0`. Introduce `a c hac u hu w hw`. Use `perp_span τ G ?_ u hu` and prove the remaining obligations.

Introduce and unpack `_ ⟨j, hj, rfl⟩`. Use `perp_span_right τ G hG ?_ w hw` and prove the remaining obligations. Introduce and unpack `_ ⟨k, hk, rfl⟩`. Simplify using `only [Set.mem_setOf_eq] at hj hk`. Distinguish the cases in `hjp : (j : ℕ) < p`.

Establish `hkp : p ≤ (k : ℕ)`. Assume the negation of the conclusion as `hkp`. Conclude with `hac ⟨fun _ => hk.mp (not_le.mp hkp), fun _ => hj.mp hjp⟩`. Conclude with `horth j k hjp hkp`. Establish `hkp : (k : ℕ) < p`.

Assume the negation of the conclusion as `hkp`. Conclude with `hac ⟨fun ha => absurd (hj.mpr ha) hjp, fun hc => absurd (hk.mpr hc) hkp⟩`. Rewrite using `[← csym, horth k j hkp (not_lt.mp hjp), map_zero]`. Establish `step : ∀ m : ℕ, m ≤ n → ∃ g : Fin n → Fin r → ℂ, (∀ c a : Fin n, (c : ℕ) < m → (a : ℕ) < m → hermC τ G (g c) (g a) = if c = a then ε c else 0) ∧ (∀ c : Fin n, (c : ℕ) < m → g c ∈ Submodule.span ℂ (Y '' {j | (j : ℕ) ≤ c ∧ ((j : ℕ) < p ↔ (c : ℕ) < p)})) ∧ (∀ j : Fin n, (j : ℕ) < m …`. Introduce `m`.

Proceed by induction on `m with`. Consider the case `zero => exact fun _ => ⟨0, fun c _ h => absurd h (Nat.not_lt_zero _), fun c h => absurd h (Nat.not_lt_zero _), fun j h => absurd h (Nat.not_lt_zero _)⟩`. Consider the case `succ m ih`. Introduce `hmn`. Take `⟨g, horg, hspg, hspY⟩` from `ih (Nat.le_of_succ_le hmn)`.

Use `set c₀ : Fin n := ⟨m, hmn⟩ with hc₀`. Use `set T : Finset (Fin n) := Finset.univ.filter (fun a : Fin n => (a : ℕ) < m) with hT`. Use `set v : Fin r → ℂ := Y c₀ - ∑ a ∈ T, (ε a * hermC τ G (Y c₀) (g a)) • g a with hv`. Establish `hεsq : ∀ a, ε a * ε a = 1`. Introduce `a`.

Rewrite using `[hε]`. Simplify using `only`. Apply the tactic sequence `split_ifs <;> norm_num`. Establish `hvg : ∀ a ∈ T, hermC τ G v (g a) = 0`. Introduce `a ha`.

Establish `ham : (a : ℕ) < m` using `(Finset.mem_filter.mp ha).2`. Rewrite using `[hv, subL, sumL]`. Establish `: ∀ b ∈ T, hermC τ G ((ε b * hermC τ G (Y c₀) (g b)) • g b) (g a) = if b = a then hermC τ G (Y c₀) (g a) else 0`. Introduce `b hb`. Rewrite using `[smulL, horg b a (Finset.mem_filter.mp hb).2 ham]`.

Use `split_ifs with hba`. Rewrite using `[hba, mul_comm (ε a), mul_assoc, hεsq, mul_one]`. Rewrite using `[mul_zero]`. Rewrite using `[Finset.sum_congr rfl this, Finset.sum_ite_eq' T a, if_pos ha, sub_self]`. Use `set S₀ : Set (Fin n) := {j | (j : ℕ) ≤ c₀ ∧ ((j : ℕ) < p ↔ (c₀ : ℕ) < p)} with hS₀`.

Establish `hgS : ∀ a ∈ T, ((a : ℕ) < p ↔ (c₀ : ℕ) < p) → g a ∈ Submodule.span ℂ (Y '' S₀)`. Introduce `a ha hblk`. Establish `ham : (a : ℕ) < m` using `(Finset.mem_filter.mp ha).2`. Use `Submodule.span_mono (Set.image_mono ?_) (hspg a ham)` and prove the remaining obligations. Introduce and unpack `j ⟨hj1, hj2⟩`.

Conclude with `⟨le_trans hj1 (le_of_lt ham), hj2.trans hblk⟩`. Establish `hcoef0 : ∀ a ∈ T, ¬((a : ℕ) < p ↔ (c₀ : ℕ) < p) → hermC τ G (Y c₀) (g a) = 0`. Introduce `a ha hblk`. Establish `ham : (a : ℕ) < m` using `(Finset.mem_filter.mp ha).2`. Use `cross c₀ a (fun h => hblk h.symm) (Y c₀) (Submodule.subset_span ⟨c₀, Iff.rfl, rfl⟩) (g a) (Submodule.span_mono (Set.image_mono ?_) (hspg a ham))` and prove the remaining obligations.

Introduce and unpack `j ⟨_, hj2⟩`. Conclude with `hj2`. Establish `hvS : v ∈ Submodule.span ℂ (Y '' S₀)`. Rewrite using `[hv]`. Use `Submodule.sub_mem _ (Submodule.subset_span ⟨c₀, ⟨le_refl _, Iff.rfl⟩, rfl⟩) ?_` and prove the remaining obligations.

Use `Submodule.sum_mem _ (fun a ha => ?_)` and prove the remaining obligations. Distinguish the cases in `hblk : ((a : ℕ) < p ↔ (c₀ : ℕ) < p)`. Conclude with `Submodule.smul_mem _ _ (hgS a ha hblk)`. Rewrite using `[hcoef0 a ha hblk, mul_zero, zero_smul]`. Conclude with `Submodule.zero_mem _`.

Establish `hv0 : v ≠ 0`. Introduce `hv0`. Establish `hY : Y c₀ = ∑ a ∈ T, (ε a * hermC τ G (Y c₀) (g a)) • g a`. Rewrite `hv0` using `[hv]`. Conclude with `sub_eq_zero.mp hv0`.

Establish `hin : Y c₀ ∈ Submodule.span ℂ (Y '' {j | (j : ℕ) < m})`. Rewrite using `[hY]`. Use `Submodule.sum_mem _ (fun a ha => Submodule.smul_mem _ _ ?_)` and prove the remaining obligations. Establish `ham : (a : ℕ) < m` using `(Finset.mem_filter.mp ha).2`. Use `Submodule.span_mono (Set.image_mono ?_) (hspg a ham)` and prove the remaining obligations.

Introduce and unpack `j ⟨hj1, _⟩`. Conclude with `lt_of_le_of_lt hj1 ham`. Establish `hnot : c₀ ∉ {j : Fin n | (j : ℕ) < m}`. Simplify using `[hc₀]`. Use `first`.

Consider the case `exact hind.not_mem_span_image hnot hin`. Consider the case `exact hind.notMem_span_image hnot hin`. Establish `hsign : 0 < (ε c₀ * hermC τ G v v).re`. Take `⟨w, hw, hvw⟩` from `coef_of_mem Y S₀ hvS`. Establish `hw0 : w ≠ 0`.

Introduce and unpack `rfl`. Apply `hv0` to reduce the goal to its premises. Rewrite using `[hvw]`. Simplify using the standard rewrite rules. Rewrite using `[hε]`.

Simplify using `only`. Distinguish the cases in `hcp : (c₀ : ℕ) < p`. Rewrite using `[if_pos hcp, one_mul, hvw]`. Use `hpos w (fun j hj => hw j ?_) hw0` and prove the remaining obligations. Introduce and unpack `⟨_, hj2⟩`.

Conclude with `absurd (hj2.mpr hcp) (not_lt.mpr hj)`. Rewrite using `[if_neg hcp, hvw]`. Use `hneg w (fun j hj => hw j ?_) hw0` as an intermediate fact. Simplify using `only [neg_mul, one_mul, Complex.neg_re]`. Combine the linear equalities and inequalities to obtain the conclusion.

Introduce and unpack `⟨_, hj2⟩`. Conclude with `hcp (hj2.mp hj)`. Use `set t : ℝ := (ε c₀ * hermC τ G v v).re with ht`. Establish `hvv : hermC τ G v v = ε c₀ * (t : ℂ)`. Establish `hεc : ε c₀ = 1 ∨ ε c₀ = -1`.

Rewrite using `[hε]`. Simplify using `only`. Use `split_ifs`. Conclude with `Or.inl rfl`. Conclude with `Or.inr rfl`.

Establish `him` using `hC_self_im τ G hG v`. Apply `Complex.ext` to reduce the goal to its premises. Apply the tactic sequence `rcases hεc with h | h <;> simp [ht, h]`. Apply the tactic sequence `rcases hεc with h | h <;> simp [ht, h, him]`. Use `set s : ℂ := (((Real.sqrt t)⁻¹ : ℝ) : ℂ) with hs`.

Establish `hss : s * (conj s * (ε c₀ * (t : ℂ))) = ε c₀`. Establish `hr : ((Real.sqrt t)⁻¹ * ((Real.sqrt t)⁻¹ * t) : ℝ) = 1`. Rewrite using `[← mul_assoc, ← mul_inv, Real.mul_self_sqrt hsign.le, inv_mul_cancel₀ hsign.ne']`. Rewrite using `[hs, Complex.conj_ofReal]`. Establish `hc : ((Real.sqrt t)⁻¹ : ℂ) * (((Real.sqrt t)⁻¹ : ℂ) * (t : ℂ)) = 1`.

Conclude with `hr` after adjusting the coercions. Combine the equalities or inequalities in the displayed calculation. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `_ = ε c₀ := by rw [hc, mul_one]`.

Use `⟨Function.update g c₀ (s • v), ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `hlt : ∀ c : Fin n, (c : ℕ) < m + 1 → c ≠ c₀ → (c : ℕ) < m`. Introduce `c hc hne`. Establish `: (c : ℕ) ≠ m` using `fun h => hne (Fin.ext h)`. Use linear arithmetic over natural numbers and integers.

Establish `hTm : ∀ c : Fin n, (c : ℕ) < m → c ∈ T` using `fun c hc => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩`. Introduce `c a hc ha`. Apply the tactic sequence `by_cases hc0 : c = c₀ <;> by_cases ha0 : a = c₀`. Substitute `hc0` using the available equality. Substitute `ha0` using the available equality.

Rewrite using `[Function.update_self, smulL, smulR, hvv, hss, if_pos rfl]`. Substitute `hc0` using the available equality. Rewrite using `[Function.update_self, Function.update_of_ne ha0, smulL, hvg a (hTm a (hlt a ha ha0)), mul_zero, if_neg (Ne.symm ha0)]`. Substitute `ha0` using the available equality. Rewrite using `[Function.update_self, Function.update_of_ne hc0, smulR, ← csym, hvg c (hTm c (hlt c hc hc0)), map_zero, mul_zero, if_neg hc0]`.

Rewrite using `[Function.update_of_ne hc0, Function.update_of_ne ha0]`. Conclude with `horg c a (hlt c hc hc0) (hlt a ha ha0)`. Introduce `c hc`. Distinguish the cases in `hc0 : c = c₀`. Substitute `hc0` using the available equality.

Rewrite using `[Function.update_self]`. Conclude with `Submodule.smul_mem _ _ hvS`. Rewrite using `[Function.update_of_ne hc0]`. Establish `: (c : ℕ) ≠ m` using `fun h => hc0 (Fin.ext h)`. Conclude with `hspg c (by omega)`.

Introduce `j hj`. Distinguish the cases in `hj0 : j = c₀`. Substitute `hj0` using the available equality. Establish `hY : Y c₀ = s⁻¹ • (s • v) + ∑ a ∈ T, (ε a * hermC τ G (Y c₀) (g a)) • g a`. Establish `hs0 : s ≠ 0`.

Rewrite using `[hs]`. Conclude with `(inv_pos.mpr (Real.sqrt_pos.mpr hsign)).ne'` after adjusting the coercions. Rewrite using `[smul_smul, inv_mul_cancel₀ hs0, one_smul, hv, sub_add_cancel]`. Rewrite using `[hY]`. Use `Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨c₀, ⟨le_refl _, Iff.rfl⟩, Function.update_self _ _ _⟩)) ?_` and prove the remaining obligations.

Use `Submodule.sum_mem _ (fun a ha => ?_)` and prove the remaining obligations. Establish `ham : (a : ℕ) < m` using `(Finset.mem_filter.mp ha).2`. Establish `hac : a ≠ c₀` using `fun h => by rw [h] at ham; exact lt_irrefl _ ham`. Distinguish the cases in `hblk : ((a : ℕ) < p ↔ (c₀ : ℕ) < p)`. Use `Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, ⟨le_of_lt ham, hblk⟩, ?_⟩)` and prove the remaining obligations.

Conclude with `Function.update_of_ne hac _ _`. Rewrite using `[hcoef0 a ha hblk, mul_zero, zero_smul]`. Conclude with `Submodule.zero_mem _`. Establish `hjm : (j : ℕ) < m`. Establish `: (j : ℕ) ≠ m` using `fun h => hj0 (Fin.ext h)`.

Use linear arithmetic over natural numbers and integers. Use `Submodule.span_mono ?_ (hspY j hjm)` and prove the remaining obligations. Introduce and unpack `_ ⟨c, hc, rfl⟩`. Use `⟨c, hc, ?_⟩` and prove the remaining obligations. Establish `hcc : c ≠ c₀`.

Introduce `h`. Rewrite `hc` using `[h]`. Conclude with `absurd (lt_of_le_of_lt hc.1 hjm) (lt_irrefl _)`. Conclude with `Function.update_of_ne hcc _ _`. Take `⟨g, horg, hspg, hspY⟩` from `step n le_rfl`.

Use `⟨g, fun c a => ?_, fun c hc => ?_, fun c => ?_, fun j => ?_⟩` and prove the remaining obligations. Rewrite using `[horg c a c.isLt a.isLt, hε]`. Use `Submodule.span_mono (Set.image_mono ?_) (hspg c c.isLt)` and prove the remaining obligations. Introduce and unpack `j ⟨_, hj2⟩`. Conclude with `hj2.mpr hc`.

Use `Submodule.span_mono (Set.image_subset_range _ _) (hspg c c.isLt)` and prove the remaining obligations. Take `⟨β, hβ, hYβ⟩` from `coef_of_mem g _ (hspY j j.isLt)`. Use `⟨β, fun c hc => hβ c ?_, hYβ⟩` and prove the remaining obligations. Introduce and unpack `⟨_, h2⟩`. Conclude with `hc h2`.
-/
theorem gs_exists {n : ℕ} (p : ℕ) (Y : Fin n → Fin r → ℂ) (hind : LinearIndependent ℂ Y)
    (horth : ∀ j k : Fin n, (j : ℕ) < p → p ≤ (k : ℕ) → hermC τ G (Y j) (Y k) = 0)
    (hpos : ∀ w : Fin n → ℂ, (∀ j : Fin n, p ≤ (j : ℕ) → w j = 0) → w ≠ 0 →
      0 < (hermC τ G (∑ j, w j • Y j) (∑ j, w j • Y j)).re)
    (hneg : ∀ w : Fin n → ℂ, (∀ j : Fin n, (j : ℕ) < p → w j = 0) → w ≠ 0 →
      (hermC τ G (∑ j, w j • Y j) (∑ j, w j • Y j)).re < 0) :
    ∃ g : Fin n → Fin r → ℂ,
      (∀ c a : Fin n, hermC τ G (g c) (g a) =
        if c = a then (if (c : ℕ) < p then 1 else -1) else 0) ∧
      (∀ c : Fin n, (c : ℕ) < p → g c ∈ Submodule.span ℂ (Y '' {j | (j : ℕ) < p})) ∧
      (∀ c : Fin n, g c ∈ Submodule.span ℂ (Set.range Y)) ∧
      (∀ j : Fin n, ∃ β : Fin n → ℂ, (∀ c : Fin n, ¬((c : ℕ) < p ↔ (j : ℕ) < p) → β c = 0) ∧
        Y j = ∑ c, β c • g c) := by
  classical
  obtain ⟨ε, hε⟩ : ∃ ε : Fin n → ℂ, ε = fun c : Fin n => (if (c : ℕ) < p then 1 else -1 : ℂ) :=
    ⟨fun c : Fin n => (if (c : ℕ) < p then 1 else -1 : ℂ), rfl⟩
  have hτ : ∀ a b, conj (τ (G a b)) = τ (G b a) := by
    intro a b
    rw [← hG a b]
    first
    | exact (NumberField.IsCMField.complexEmbedding_complexConj τ (G a b)).symm
    | exact (IsCMField.complexEmbedding_complexConj τ (G a b)).symm
    | (simp only [cc]; exact (NumberField.IsCMField.complexEmbedding_complexConj τ (G a b)).symm)
    | (simp [cc])
  have csym : ∀ u w, conj (hermC τ G u w) = hermC τ G w u := by
    intro u w
    simp only [hermC, map_sum, map_mul, Complex.conj_conj]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    rw [hτ]
    ring
  have smulL : ∀ (c : ℂ) u w, hermC τ G (c • u) w = c * hermC τ G u w := fun c u w =>
    map_smul (hL τ G w) c u
  have subL : ∀ u u' w, hermC τ G (u - u') w = hermC τ G u w - hermC τ G u' w := fun u u' w =>
    map_sub (hL τ G w) u u'
  have sumL : ∀ (s : Finset (Fin n)) (f : Fin n → Fin r → ℂ) w,
      hermC τ G (∑ a ∈ s, f a) w = ∑ a ∈ s, hermC τ G (f a) w := fun s f w =>
    map_sum (hL τ G w) f s
  have smulR : ∀ (c : ℂ) u w, hermC τ G u (c • w) = conj c * hermC τ G u w := by
    intro c u w
    rw [← csym, smulL, map_mul, csym]

  have cross : ∀ a c : Fin n, ¬((a : ℕ) < p ↔ (c : ℕ) < p) →
      ∀ u ∈ Submodule.span ℂ (Y '' {j | ((j : ℕ) < p ↔ (a : ℕ) < p)}),
      ∀ w ∈ Submodule.span ℂ (Y '' {j | ((j : ℕ) < p ↔ (c : ℕ) < p)}), hermC τ G u w = 0 := by
    intro a c hac u hu w hw
    refine perp_span τ G ?_ u hu
    rintro _ ⟨j, hj, rfl⟩
    refine perp_span_right τ G hG ?_ w hw
    rintro _ ⟨k, hk, rfl⟩
    simp only [Set.mem_setOf_eq] at hj hk
    by_cases hjp : (j : ℕ) < p
    · have hkp : p ≤ (k : ℕ) := by
        by_contra hkp
        exact hac ⟨fun _ => hk.mp (not_le.mp hkp), fun _ => hj.mp hjp⟩
      exact horth j k hjp hkp
    · have hkp : (k : ℕ) < p := by
        by_contra hkp
        exact hac ⟨fun ha => absurd (hj.mpr ha) hjp, fun hc => absurd (hk.mpr hc) hkp⟩
      rw [← csym, horth k j hkp (not_lt.mp hjp), map_zero]

  have step : ∀ m : ℕ, m ≤ n → ∃ g : Fin n → Fin r → ℂ,
      (∀ c a : Fin n, (c : ℕ) < m → (a : ℕ) < m → hermC τ G (g c) (g a) = if c = a then ε c else 0) ∧
      (∀ c : Fin n, (c : ℕ) < m →
        g c ∈ Submodule.span ℂ (Y '' {j | (j : ℕ) ≤ c ∧ ((j : ℕ) < p ↔ (c : ℕ) < p)})) ∧
      (∀ j : Fin n, (j : ℕ) < m →
        Y j ∈ Submodule.span ℂ (g '' {c | (c : ℕ) ≤ j ∧ ((c : ℕ) < p ↔ (j : ℕ) < p)})) := by
    intro m
    induction m with
    | zero => exact fun _ => ⟨0, fun c _ h => absurd h (Nat.not_lt_zero _),
        fun c h => absurd h (Nat.not_lt_zero _), fun j h => absurd h (Nat.not_lt_zero _)⟩
    | succ m ih =>
      intro hmn
      obtain ⟨g, horg, hspg, hspY⟩ := ih (Nat.le_of_succ_le hmn)
      set c₀ : Fin n := ⟨m, hmn⟩ with hc₀
      set T : Finset (Fin n) := Finset.univ.filter (fun a : Fin n => (a : ℕ) < m) with hT
      set v : Fin r → ℂ := Y c₀ - ∑ a ∈ T, (ε a * hermC τ G (Y c₀) (g a)) • g a with hv
      have hεsq : ∀ a, ε a * ε a = 1 := by
        intro a
        rw [hε]
        dsimp only
        split_ifs <;> norm_num
      have hvg : ∀ a ∈ T, hermC τ G v (g a) = 0 := by
        intro a ha
        have ham : (a : ℕ) < m := (Finset.mem_filter.mp ha).2
        rw [hv, subL, sumL]
        have : ∀ b ∈ T, hermC τ G ((ε b * hermC τ G (Y c₀) (g b)) • g b) (g a) =
            if b = a then hermC τ G (Y c₀) (g a) else 0 := by
          intro b hb
          rw [smulL, horg b a (Finset.mem_filter.mp hb).2 ham]
          split_ifs with hba
          · rw [hba, mul_comm (ε a), mul_assoc, hεsq, mul_one]
          · rw [mul_zero]
        rw [Finset.sum_congr rfl this, Finset.sum_ite_eq' T a, if_pos ha, sub_self]

      set S₀ : Set (Fin n) := {j | (j : ℕ) ≤ c₀ ∧ ((j : ℕ) < p ↔ (c₀ : ℕ) < p)} with hS₀
      have hgS : ∀ a ∈ T, ((a : ℕ) < p ↔ (c₀ : ℕ) < p) → g a ∈ Submodule.span ℂ (Y '' S₀) := by
        intro a ha hblk
        have ham : (a : ℕ) < m := (Finset.mem_filter.mp ha).2
        refine Submodule.span_mono (Set.image_mono ?_) (hspg a ham)
        rintro j ⟨hj1, hj2⟩
        exact ⟨le_trans hj1 (le_of_lt ham), hj2.trans hblk⟩
      have hcoef0 : ∀ a ∈ T, ¬((a : ℕ) < p ↔ (c₀ : ℕ) < p) → hermC τ G (Y c₀) (g a) = 0 := by
        intro a ha hblk
        have ham : (a : ℕ) < m := (Finset.mem_filter.mp ha).2
        refine cross c₀ a (fun h => hblk h.symm) (Y c₀) (Submodule.subset_span ⟨c₀, Iff.rfl, rfl⟩)
          (g a) (Submodule.span_mono (Set.image_mono ?_) (hspg a ham))
        rintro j ⟨_, hj2⟩
        exact hj2
      have hvS : v ∈ Submodule.span ℂ (Y '' S₀) := by
        rw [hv]
        refine Submodule.sub_mem _ (Submodule.subset_span ⟨c₀, ⟨le_refl _, Iff.rfl⟩, rfl⟩) ?_
        refine Submodule.sum_mem _ (fun a ha => ?_)
        by_cases hblk : ((a : ℕ) < p ↔ (c₀ : ℕ) < p)
        · exact Submodule.smul_mem _ _ (hgS a ha hblk)
        · rw [hcoef0 a ha hblk, mul_zero, zero_smul]
          exact Submodule.zero_mem _
      have hv0 : v ≠ 0 := by
        intro hv0
        have hY : Y c₀ = ∑ a ∈ T, (ε a * hermC τ G (Y c₀) (g a)) • g a := by
          rw [hv] at hv0
          exact sub_eq_zero.mp hv0
        have hin : Y c₀ ∈ Submodule.span ℂ (Y '' {j | (j : ℕ) < m}) := by
          rw [hY]
          refine Submodule.sum_mem _ (fun a ha => Submodule.smul_mem _ _ ?_)
          have ham : (a : ℕ) < m := (Finset.mem_filter.mp ha).2
          refine Submodule.span_mono (Set.image_mono ?_) (hspg a ham)
          rintro j ⟨hj1, _⟩
          exact lt_of_le_of_lt hj1 ham
        have hnot : c₀ ∉ {j : Fin n | (j : ℕ) < m} := by
          simp [hc₀]
        first
        | exact hind.not_mem_span_image hnot hin
        | exact hind.notMem_span_image hnot hin

      have hsign : 0 < (ε c₀ * hermC τ G v v).re := by
        obtain ⟨w, hw, hvw⟩ := coef_of_mem Y S₀ hvS
        have hw0 : w ≠ 0 := by
          rintro rfl
          apply hv0
          rw [hvw]
          simp
        rw [hε]
        dsimp only
        by_cases hcp : (c₀ : ℕ) < p
        · rw [if_pos hcp, one_mul, hvw]
          refine hpos w (fun j hj => hw j ?_) hw0
          rintro ⟨_, hj2⟩
          exact absurd (hj2.mpr hcp) (not_lt.mpr hj)
        · rw [if_neg hcp, hvw]
          have := hneg w (fun j hj => hw j ?_) hw0
          · simp only [neg_mul, one_mul, Complex.neg_re]
            linarith
          · rintro ⟨_, hj2⟩
            exact hcp (hj2.mp hj)
      set t : ℝ := (ε c₀ * hermC τ G v v).re with ht
      have hvv : hermC τ G v v = ε c₀ * (t : ℂ) := by
        have hεc : ε c₀ = 1 ∨ ε c₀ = -1 := by
          rw [hε]
          dsimp only
          split_ifs
          · exact Or.inl rfl
          · exact Or.inr rfl
        have him := hC_self_im τ G hG v
        apply Complex.ext
        · rcases hεc with h | h <;> simp [ht, h]
        · rcases hεc with h | h <;> simp [ht, h, him]
      set s : ℂ := (((Real.sqrt t)⁻¹ : ℝ) : ℂ) with hs
      have hss : s * (conj s * (ε c₀ * (t : ℂ))) = ε c₀ := by
        have hr : ((Real.sqrt t)⁻¹ * ((Real.sqrt t)⁻¹ * t) : ℝ) = 1 := by
          rw [← mul_assoc, ← mul_inv, Real.mul_self_sqrt hsign.le, inv_mul_cancel₀ hsign.ne']
        rw [hs, Complex.conj_ofReal]
        have hc : ((Real.sqrt t)⁻¹ : ℂ) * (((Real.sqrt t)⁻¹ : ℂ) * (t : ℂ)) = 1 := by
          exact_mod_cast hr
        calc ((((Real.sqrt t)⁻¹ : ℝ)) : ℂ) * ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) * (ε c₀ * (t : ℂ)))
            = ε c₀ * (((Real.sqrt t)⁻¹ : ℂ) * (((Real.sqrt t)⁻¹ : ℂ) * (t : ℂ))) := by
              push_cast
              ring
          _ = ε c₀ := by rw [hc, mul_one]

      refine ⟨Function.update g c₀ (s • v), ?_, ?_, ?_⟩
      · have hlt : ∀ c : Fin n, (c : ℕ) < m + 1 → c ≠ c₀ → (c : ℕ) < m := by
          intro c hc hne
          have : (c : ℕ) ≠ m := fun h => hne (Fin.ext h)
          omega
        have hTm : ∀ c : Fin n, (c : ℕ) < m → c ∈ T := fun c hc => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩
        intro c a hc ha
        by_cases hc0 : c = c₀ <;> by_cases ha0 : a = c₀
        · subst hc0
          subst ha0
          rw [Function.update_self, smulL, smulR, hvv, hss, if_pos rfl]
        · subst hc0
          rw [Function.update_self, Function.update_of_ne ha0, smulL,
            hvg a (hTm a (hlt a ha ha0)), mul_zero, if_neg (Ne.symm ha0)]
        · subst ha0
          rw [Function.update_self, Function.update_of_ne hc0, smulR, ← csym,
            hvg c (hTm c (hlt c hc hc0)), map_zero, mul_zero, if_neg hc0]
        · rw [Function.update_of_ne hc0, Function.update_of_ne ha0]
          exact horg c a (hlt c hc hc0) (hlt a ha ha0)
      · intro c hc
        by_cases hc0 : c = c₀
        · subst hc0
          rw [Function.update_self]
          exact Submodule.smul_mem _ _ hvS
        · rw [Function.update_of_ne hc0]
          have : (c : ℕ) ≠ m := fun h => hc0 (Fin.ext h)
          exact hspg c (by omega)
      · intro j hj
        by_cases hj0 : j = c₀
        · subst hj0
          have hY : Y c₀ = s⁻¹ • (s • v) + ∑ a ∈ T, (ε a * hermC τ G (Y c₀) (g a)) • g a := by
            have hs0 : s ≠ 0 := by
              rw [hs]
              exact_mod_cast (inv_pos.mpr (Real.sqrt_pos.mpr hsign)).ne'
            rw [smul_smul, inv_mul_cancel₀ hs0, one_smul, hv, sub_add_cancel]
          rw [hY]
          refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span
            ⟨c₀, ⟨le_refl _, Iff.rfl⟩, Function.update_self _ _ _⟩)) ?_
          refine Submodule.sum_mem _ (fun a ha => ?_)
          have ham : (a : ℕ) < m := (Finset.mem_filter.mp ha).2
          have hac : a ≠ c₀ := fun h => by rw [h] at ham; exact lt_irrefl _ ham
          by_cases hblk : ((a : ℕ) < p ↔ (c₀ : ℕ) < p)
          · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, ⟨le_of_lt ham, hblk⟩, ?_⟩)
            exact Function.update_of_ne hac _ _
          · rw [hcoef0 a ha hblk, mul_zero, zero_smul]
            exact Submodule.zero_mem _
        · have hjm : (j : ℕ) < m := by
            have : (j : ℕ) ≠ m := fun h => hj0 (Fin.ext h)
            omega
          refine Submodule.span_mono ?_ (hspY j hjm)
          rintro _ ⟨c, hc, rfl⟩
          refine ⟨c, hc, ?_⟩
          have hcc : c ≠ c₀ := by
            intro h
            rw [h] at hc
            exact absurd (lt_of_le_of_lt hc.1 hjm) (lt_irrefl _)
          exact Function.update_of_ne hcc _ _
  obtain ⟨g, horg, hspg, hspY⟩ := step n le_rfl
  refine ⟨g, fun c a => ?_, fun c hc => ?_, fun c => ?_, fun j => ?_⟩
  · rw [horg c a c.isLt a.isLt, hε]
  · refine Submodule.span_mono (Set.image_mono ?_) (hspg c c.isLt)
    rintro j ⟨_, hj2⟩
    exact hj2.mpr hc
  · refine Submodule.span_mono (Set.image_subset_range _ _) (hspg c c.isLt)
  · obtain ⟨β, hβ, hYβ⟩ := coef_of_mem g _ (hspY j j.isLt)
    refine ⟨β, fun c hc => hβ c ?_, hYβ⟩
    rintro ⟨_, h2⟩
    exact hc h2

end

end ReciprocityTheory.ChartRestriction.G.FD.GramSchmidtSelfImaginary
