import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsLieDataCircle
import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.ExistsIntMulIsIntegralOfTrace

open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology

namespace GlobalTheory.SmoothForms

open Module Submodule

/- English proof (translation)
Establish `hneg : house (-(h x v)) = house (h x v)` using `by simp [house]`. Establish `h0 : 0 ≤ T` using `by linarith`. Establish `h1 : house (h v v) ≤ T * T` using `(H.form_le v v).trans (mul_le_mul hv hv (H.nonneg _) h0)`. Establish `h2 : house (h x v) ≤ T * T` using `(H.form_le x v).trans (mul_le_mul hx hv (H.nonneg _) h0)`. Establish `h3 : ν (h v v • x) ≤ T * T * T` using `(H.smul_le _ _).trans (mul_le_mul h1 hx (H.nonneg _) (by positivity))`.

Establish `h4 : ν ((-(h x v)) • v) ≤ T * T * T` using `(H.smul_le _ _).trans (by rw [hneg]; exact mul_le_mul h2 hv (H.nonneg _) (by positivity))`. Rewrite using `[sub_eq_add_neg, ← neg_smul]`. Establish `h5 : 2 * (T * T * T) ≤ T * (T * T * T)` using `mul_le_mul_of_nonneg_right hT (by positivity)`. Use `(H.add_le _ _).trans ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem Sized.proj_le {E : Type} [Field E] [NumberField E] [IsCMField E] {V : Type} [AddCommGroup V] [Module E V]
    {h : V →ₗ[E] V →ₗ⋆[E] E} {Λ : Submodule ℤ V} {N : ℤ} {ν : V → ℝ} {B : ℝ} (H : Sized h Λ N ν B)
    {T : ℝ} (hT : 2 ≤ T) {v x : V} (hv : ν v ≤ T) (hx : ν x ≤ T) :
    ν (h v v • x - h x v • v) ≤ T ^ 4 := by
  have hneg : house (-(h x v)) = house (h x v) := by simp [house]
  have h0 : 0 ≤ T := by linarith
  have h1 : house (h v v) ≤ T * T := (H.form_le v v).trans (mul_le_mul hv hv (H.nonneg _) h0)
  have h2 : house (h x v) ≤ T * T := (H.form_le x v).trans (mul_le_mul hx hv (H.nonneg _) h0)
  have h3 : ν (h v v • x) ≤ T * T * T :=
    (H.smul_le _ _).trans (mul_le_mul h1 hx (H.nonneg _) (by positivity))
  have h4 : ν ((-(h x v)) • v) ≤ T * T * T :=
    (H.smul_le _ _).trans (by rw [hneg]; exact mul_le_mul h2 hv (H.nonneg _) (by positivity))
  rw [sub_eq_add_neg, ← neg_smul]
  have h5 : 2 * (T * T * T) ≤ T * (T * T * T) := mul_le_mul_of_nonneg_right hT (by positivity)
  refine (H.add_le _ _).trans ?_
  calc _ ≤ 2 * (T * T * T) := by linarith
    _ ≤ _ := h5
    _ = _ := by ring

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `N _`. Conclude with `⟨∅, 0, Set.finite_empty, by simp, fun V _ _ _ _ _ _ _ _ _ => ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩⟩`.

Consider the case `succ n ih`. Introduce `N hN`. Take `⟨S₁, k₁, hS₁, h0₁, H₁⟩` from `HA (n + 1) n.succ_ne_zero N hN`. Take `⟨M, hM, hMS⟩` from `GlobalTheory.HermClass.exists_int_mul_isIntegral E (hS₁.image fun a => a⁻¹)`. Take `⟨S₂, k₂, hS₂, h0₂, H₂⟩` from `ih _ (mul_ne_zero hM hN)`.

Use `⟨S₁ ∪ S₂, k₁ + (k₁ + 1) * 4 * k₂, hS₁.union hS₂, by simp [h0₁, h0₂], ?_⟩` and prove the remaining obligations. Introduce `V _ _ _ h Λ ν B hV H`. Take `⟨v, hv, hvS, hvν⟩` from `H₁ V h Λ ν B hV H`. Establish `hs` using `H.symm`. Establish `hO` using `H.stable`.

Establish `hint` using `H.int`. Establish `hB1 : 1 ≤ B` using `by linarith [H.two_le]`. Establish `hBT : B ≤ B ^ (k₁ + 1)` using `le_self_pow₀ hB1 (Nat.succ_ne_zero _)`. Establish `hT2 : 2 ≤ B ^ (k₁ + 1)` using `H.two_le.trans hBT`. Establish `hvT : ν v ≤ B ^ (k₁ + 1)` using `hvν.trans (pow_le_pow_right₀ hB1 (Nat.le_succ _))`.

Establish `hproj : ∀ x, ν x ≤ B → ν (h v v • x - h x v • v) ≤ (B ^ (k₁ + 1)) ^ 4` using `fun x hx => H.proj_le hT2 hvT (hx.trans hBT)`. Use `set a := h v v with ha`. Establish `ha0 : a ≠ 0` using `fun h0 => h0₁ (h0 ▸ hvS)`. Establish `hai : IsIntegral ℤ a` using `hint v hv v hv`. Establish `has : star a = a` using `(hs v v).symm`.

Set `W : Submodule E V` to `LinearMap.ker (h.flip v)`. Establish `hW : ∀ x, x ∈ W ↔ h x v = 0` using `fun x => Iff.rfl`. Establish `hWr : finrank E W = n`. Establish `h1` using `LinearMap.finrank_range_add_finrank_ker (h.flip v)`. Establish `h2 : LinearMap.range (h.flip v) = ⊤`.

Rewrite using `[eq_top_iff]`. Introduce `c _`. Conclude with `⟨(c / a) • v, by simp [← ha, ha0]⟩`. Rewrite `h1` using `[h2, finrank_top, finrank_self, hV]`. Express the relevant statement in the definitionally equal form `1 + finrank E W = _ at h1`.

Use linear arithmetic over natural numbers and integers. Set `p : V →ₗ[E] W` to `LinearMap.codRestrict W (a • LinearMap.id - (h.flip v).smulRight v) fun x => by`. Rewrite using `[hW]`. Simplify using `[← ha, mul_comm]`. Establish `hp : ∀ x, (p x : V) = a • x - h x v • v` using `fun x => rfl`.

Set `Λ' : Submodule ℤ W` to `Λ.comap (W.subtype.restrictScalars ℤ)`. Establish `hΛ' : ∀ x : W, x ∈ Λ' ↔ (x : V) ∈ Λ` using `fun x => Iff.rfl`. Establish `hpΛ : ∀ x ∈ Λ, p x ∈ Λ'` using `fun x hx => by`. Rewrite using `[hΛ', hp]`. Conclude with `sub_mem (hO _ hai _ hx) (hO _ (hint x hx v hv) _ hv)`.

Establish `hyp : ∀ (y : W) (x : V), h y (p x) = a * h y x` using `fun y x => by`. Establish `: h y v = 0` using `y.2`. Simplify using `[hp, starRingEnd_apply, has, this]`. Establish `H' : Sized (h.domRestrict₁₂ W W) Λ' (M * N) (fun w : W => ν w) ((B ^ (k₁ + 1)) ^ 4)` using `{ symm := fun x y => hs x y nondeg := fun y hy => Subtype.ext (H.nondeg y fun x => by`. Establish `h1 : h y (p x) = 0` using `hy (p x)`.

Rewrite `h1` using `[hyp]`. Conclude with `(mul_eq_zero.1 h1).resolve_left ha0)`. Use `fg := by`. Apply `Submodule.fg_of_fg_map_injective (W.subtype.restrictScalars ℤ) W.subtype_injective` to reduce the goal to its premises. Conclude with `H.fg.of_le (map_comap_le _ _)`.

Use `stable := fun c hc x hx => hO c hc x hx`. Use `int := fun x hx y hy => hint x hx y hy`. Use `dual := fun y hy => by`. Establish `h1 : (N : E) • a • (y : V) ∈ Λ` using `H.dual _ fun x hx => by`. Rewrite using `[map_smul, LinearMap.smul_apply, smul_eq_mul, ← hyp]`.

Conclude with `hy _ (hpΛ x hx)`. Establish `h2` using `hO _ (hMS _ ⟨a, hvS, rfl⟩) _ h1`. Rewrite `h2` using `[smul_smul, smul_smul]`. Rewrite using `[hΛ', Submodule.coe_smul]`. Use `h2 using 2` and compare the differences between its conclusion and the goal.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Use `two_le := hT2.trans (le_self_pow₀ (by linarith) (by norm_num))`. Use `nonneg := fun x => H.nonneg x`. Use `add_le := fun x y => H.add_le x y`.

Use `smul_le := fun c x => H.smul_le c x`. Use `form_le := fun x y => H.form_le x y`. Use `span := by`. Rewrite using `[eq_top_iff]`. Introduce `w _`.

Establish `h1 : span E {x | x ∈ Λ ∧ ν x ≤ B} ≤ (span E {x : W | x ∈ Λ' ∧ ν x ≤ (B ^ (k₁ + 1)) ^ 4}).comap p` using `span_le.2 fun x hx => subset_span ⟨hpΛ x hx.1, hproj x hx.2⟩`. Establish `h2 : p w ∈ span E {x : W | x ∈ Λ' ∧ ν x ≤ (B ^ (k₁ + 1)) ^ 4}` using `h1 (H.span ▸ mem_top)`. Establish `h3 : w = a⁻¹ • p w` using `Subtype.ext (by`. Establish `: h w v = 0` using `w.2`. Simplify using `[hp, this, ha0])`.

Rewrite using `[h3]`. Conclude with `smul_mem _ _ h2 }`. Take `⟨u, huΛ, huo, huS⟩` from `H₂ W (h.domRestrict₁₂ W W) Λ' _ _ hWr H'`. Use `⟨Fin.cons v fun i => u i, fun i => ?_, fun i j hij => ?_, fun i => ?_⟩` and prove the remaining obligations. Consider the cases of `i using Fin.cases with`.

Consider the case `zero => exact hv`. Consider the case `succ i => exact huΛ i`. Consider the cases of `i using Fin.cases with`. Consider the case `zero`. Consider the cases of `j using Fin.cases with`.

Consider the case `zero => exact (hij rfl).elim`. Consider the case `succ j`. Establish `: h (u j) v = 0` using `(u j).2`. Simplify using `only [Fin.cons_zero, Fin.cons_succ]`. Rewrite using `[hs, this, star_zero]`.

Consider the case `succ i`. Consider the cases of `j using Fin.cases with`. Consider the case `zero => exact (u i).2`. Consider the case `succ j => exact huo i j fun h0 => hij (congrArg _ h0)`. Consider the cases of `i using Fin.cases with`.

Consider the case `zero => exact ⟨Or.inl hvS, hvν.trans (pow_le_pow_right₀ hB1 (Nat.le_add_right _ _))⟩`. Consider the case `succ i`. Use `⟨Or.inr (huS i).1, (huS i).2.trans ?_⟩` and prove the remaining obligations. Rewrite using `[← pow_mul, ← pow_mul, ← mul_assoc]`. Conclude with `pow_le_pow_right₀ hB1 (Nat.le_add_left _ _)`.
-/
theorem orthoSmall_of_anisoSmall (E : Type) [Field E] [NumberField E] [IsCMField E] (HA : AnisoSmall E) :
    OrthoSmall E := by
  intro n
  induction n with
  | zero =>
    intro N _
    exact ⟨∅, 0, Set.finite_empty, by simp, fun V _ _ _ _ _ _ _ _ _ =>
      ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩⟩
  | succ n ih =>
    intro N hN
    obtain ⟨S₁, k₁, hS₁, h0₁, H₁⟩ := HA (n + 1) n.succ_ne_zero N hN
    obtain ⟨M, hM, hMS⟩ := GlobalTheory.HermClass.exists_int_mul_isIntegral E (hS₁.image fun a => a⁻¹)
    obtain ⟨S₂, k₂, hS₂, h0₂, H₂⟩ := ih _ (mul_ne_zero hM hN)
    refine ⟨S₁ ∪ S₂, k₁ + (k₁ + 1) * 4 * k₂, hS₁.union hS₂, by simp [h0₁, h0₂], ?_⟩
    intro V _ _ _ h Λ ν B hV H
    obtain ⟨v, hv, hvS, hvν⟩ := H₁ V h Λ ν B hV H
    have hs := H.symm
    have hO := H.stable
    have hint := H.int
    have hB1 : 1 ≤ B := by linarith [H.two_le]
    have hBT : B ≤ B ^ (k₁ + 1) := le_self_pow₀ hB1 (Nat.succ_ne_zero _)
    have hT2 : 2 ≤ B ^ (k₁ + 1) := H.two_le.trans hBT
    have hvT : ν v ≤ B ^ (k₁ + 1) := hvν.trans (pow_le_pow_right₀ hB1 (Nat.le_succ _))
    have hproj : ∀ x, ν x ≤ B → ν (h v v • x - h x v • v) ≤ (B ^ (k₁ + 1)) ^ 4 := fun x hx =>
      H.proj_le hT2 hvT (hx.trans hBT)
    set a := h v v with ha
    have ha0 : a ≠ 0 := fun h0 => h0₁ (h0 ▸ hvS)
    have hai : IsIntegral ℤ a := hint v hv v hv
    have has : star a = a := (hs v v).symm
    let W : Submodule E V := LinearMap.ker (h.flip v)
    have hW : ∀ x, x ∈ W ↔ h x v = 0 := fun x => Iff.rfl
    have hWr : finrank E W = n := by
      have h1 := LinearMap.finrank_range_add_finrank_ker (h.flip v)
      have h2 : LinearMap.range (h.flip v) = ⊤ := by
        rw [eq_top_iff]
        intro c _
        exact ⟨(c / a) • v, by simp [← ha, ha0]⟩
      rw [h2, finrank_top, finrank_self, hV] at h1
      change 1 + finrank E W = _ at h1
      omega
    let p : V →ₗ[E] W := LinearMap.codRestrict W
      (a • LinearMap.id - (h.flip v).smulRight v) fun x => by
        rw [hW]; simp [← ha, mul_comm]
    have hp : ∀ x, (p x : V) = a • x - h x v • v := fun x => rfl
    let Λ' : Submodule ℤ W := Λ.comap (W.subtype.restrictScalars ℤ)
    have hΛ' : ∀ x : W, x ∈ Λ' ↔ (x : V) ∈ Λ := fun x => Iff.rfl
    have hpΛ : ∀ x ∈ Λ, p x ∈ Λ' := fun x hx => by
      rw [hΛ', hp]; exact sub_mem (hO _ hai _ hx) (hO _ (hint x hx v hv) _ hv)
    have hyp : ∀ (y : W) (x : V), h y (p x) = a * h y x := fun y x => by
      have : h y v = 0 := y.2
      simp [hp, starRingEnd_apply, has, this]
    have H' : Sized (h.domRestrict₁₂ W W) Λ' (M * N) (fun w : W => ν w) ((B ^ (k₁ + 1)) ^ 4) :=
      { symm := fun x y => hs x y
        nondeg := fun y hy => Subtype.ext (H.nondeg y fun x => by
          have h1 : h y (p x) = 0 := hy (p x)
          rw [hyp] at h1
          exact (mul_eq_zero.1 h1).resolve_left ha0)
        fg := by
          apply Submodule.fg_of_fg_map_injective (W.subtype.restrictScalars ℤ) W.subtype_injective
          exact H.fg.of_le (map_comap_le _ _)
        stable := fun c hc x hx => hO c hc x hx
        int := fun x hx y hy => hint x hx y hy
        dual := fun y hy => by
          have h1 : (N : E) • a • (y : V) ∈ Λ := H.dual _ fun x hx => by
            rw [map_smul, LinearMap.smul_apply, smul_eq_mul, ← hyp]
            exact hy _ (hpΛ x hx)
          have h2 := hO _ (hMS _ ⟨a, hvS, rfl⟩) _ h1
          rw [smul_smul, smul_smul] at h2
          rw [hΛ', Submodule.coe_smul]
          convert h2 using 2
          push_cast; field_simp
        two_le := hT2.trans (le_self_pow₀ (by linarith) (by norm_num))
        nonneg := fun x => H.nonneg x
        add_le := fun x y => H.add_le x y
        smul_le := fun c x => H.smul_le c x
        form_le := fun x y => H.form_le x y
        span := by
          rw [eq_top_iff]
          intro w _
          have h1 : span E {x | x ∈ Λ ∧ ν x ≤ B} ≤
              (span E {x : W | x ∈ Λ' ∧ ν x ≤ (B ^ (k₁ + 1)) ^ 4}).comap p :=
            span_le.2 fun x hx => subset_span ⟨hpΛ x hx.1, hproj x hx.2⟩
          have h2 : p w ∈ span E {x : W | x ∈ Λ' ∧ ν x ≤ (B ^ (k₁ + 1)) ^ 4} := h1 (H.span ▸ mem_top)
          have h3 : w = a⁻¹ • p w := Subtype.ext (by
            have : h w v = 0 := w.2
            simp [hp, this, ha0])
          rw [h3]; exact smul_mem _ _ h2 }
    obtain ⟨u, huΛ, huo, huS⟩ := H₂ W (h.domRestrict₁₂ W W) Λ' _ _ hWr H'
    refine ⟨Fin.cons v fun i => u i, fun i => ?_, fun i j hij => ?_, fun i => ?_⟩
    · cases i using Fin.cases with
      | zero => exact hv
      | succ i => exact huΛ i
    · cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => exact (hij rfl).elim
        | succ j =>
          have : h (u j) v = 0 := (u j).2
          simp only [Fin.cons_zero, Fin.cons_succ]
          rw [hs, this, star_zero]
      | succ i =>
        cases j using Fin.cases with
        | zero => exact (u i).2
        | succ j => exact huo i j fun h0 => hij (congrArg _ h0)
    · cases i using Fin.cases with
      | zero => exact ⟨Or.inl hvS, hvν.trans (pow_le_pow_right₀ hB1 (Nat.le_add_right _ _))⟩
      | succ i =>
        refine ⟨Or.inr (huS i).1, (huS i).2.trans ?_⟩
        rw [← pow_mul, ← pow_mul, ← mul_assoc]
        exact pow_le_pow_right₀ hB1 (Nat.le_add_left _ _)

end GlobalTheory.SmoothForms
