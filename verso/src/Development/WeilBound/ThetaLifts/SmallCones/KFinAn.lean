import Mathlib
import Development.WeilBound.ThetaLifts.SchwartzMoments.PolynomialFunctionalEvalContinuous

noncomputable section

namespace PositivityTheory.ThKCT.So

open PositivityTheory.ThKOwn.KPol
open scoped SchwartzMap LineDeriv

section Fil

variable {S ι : Type} [AddCommGroup S] [Module ℂ S]

def fil (P : Submodule ℂ S) (D : ι → S →ₗ[ℂ] S) : ℕ → Submodule ℂ S
  | 0 => P
  | m + 1 => fil P D m ⊔ ⨆ i, (fil P D m).map (D i)

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => exact (inferInstance : FiniteDimensional ℂ P)`. Consider the case `succ m ih => exact (inferInstance : FiniteDimensional ℂ ↥(fil P D m ⊔ ⨆ i, (fil P D m).map (D i)))`.
-/
theorem fil_fin [Finite ι] (P : Submodule ℂ S) [FiniteDimensional ℂ P] (D : ι → S →ₗ[ℂ] S) (m : ℕ) :
    FiniteDimensional ℂ (fil P D m) := by
  induction m with
  | zero => exact (inferInstance : FiniteDimensional ℂ P)
  | succ m ih => exact (inferInstance : FiniteDimensional ℂ ↥(fil P D m ⊔ ⨆ i, (fil P D m).map (D i)))

/- English proof (translation)
The claim follows from `monotone_nat_of_le_succ fun _ => le_sup_left`.
-/
theorem fil_mono (P : Submodule ℂ S) (D : ι → S →ₗ[ℂ] S) : Monotone (fil P D) := monotone_nat_of_le_succ fun _ => le_sup_left

/- English proof (translation)
Use `(Submodule.span_le.2 ?_ : _ ≤ fil P D (m + 1)) hg` and prove the remaining obligations. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `Submodule.mem_sup_right (Submodule.mem_iSup_of_mem i ⟨f, hf, rfl⟩)`.
-/
theorem fil_step (P : Submodule ℂ S) (D : ι → S →ₗ[ℂ] S) {m : ℕ} {f g : S} (hf : f ∈ fil P D m)
    (hg : g ∈ Submodule.span ℂ (Set.range fun i => D i f)) : g ∈ fil P D (m + 1) := by
  refine (Submodule.span_le.2 ?_ : _ ≤ fil P D (m + 1)) hg
  rintro _ ⟨i, rfl⟩
  exact Submodule.mem_sup_right (Submodule.mem_iSup_of_mem i ⟨f, hf, rfl⟩)

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => exact h0`. Consider the case `succ m ih`. Use `sup_le (fun f hf => Submodule.mem_sup_left (ih hf)) (iSup_le fun i => ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨f, hf, rfl⟩`.

Conclude with `fil_step P D (ih hf) (h i f)`.
-/
theorem fil_stab (P : Submodule ℂ S) (D : ι → S →ₗ[ℂ] S) (A : S →ₗ[ℂ] S) (h0 : ∀ f ∈ P, A f ∈ P)
    (h : ∀ i f, A (D i f) ∈ Submodule.span ℂ (Set.range fun j => D j (A f))) (m : ℕ) : fil P D m ≤ (fil P D m).comap A := by
  induction m with
  | zero => exact h0
  | succ m ih =>
    refine sup_le (fun f hf => Submodule.mem_sup_left (ih hf)) (iSup_le fun i => ?_)
    rintro _ ⟨f, hf, rfl⟩
    exact fil_step P D (ih hf) (h i f)

end Fil

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (lam : V →ₗ[ℝ] V →L[ℝ] ℝ)

def dopL (w : V × V) : 𝓢(V, ℂ) →ₗ[ℂ] 𝓢(V, ℂ) where
  toFun := dop w.1 (lam w.2)
  map_add' f g := by
    ext x
    have : fderiv ℝ (f + g : 𝓢(V, ℂ)) x = fderiv ℝ f x + fderiv ℝ g x := ((f.hasFDerivAt x).add (g.hasFDerivAt x)).fderiv
    simp only [SchwartzMap.add_apply, dop_apply, this, ContinuousLinearMap.add_apply]
    ring
  map_smul' c f := by
    ext x
    have : fderiv ℝ (c • f : 𝓢(V, ℂ)) x = c • fderiv ℝ f x := ((f.hasFDerivAt x).const_smul c).fderiv
    simp only [SchwartzMap.smul_apply, dop_apply, this, ContinuousLinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem dopL_apply (w : V × V) (f : 𝓢(V, ℂ)) : dopL lam w f = dop w.1 (lam w.2) f := rfl

def evD (f : 𝓢(V, ℂ)) (x : V) : V × V →ₗ[ℝ] ℂ where
  toFun w := dopL lam w f x
  map_add' a b := by
    simp only [dopL_apply, Prod.fst_add, Prod.snd_add, map_add, dop_add, SchwartzMap.add_apply]
  map_smul' c a := by
    simp only [dopL_apply, dop_apply, Prod.smul_fst, Prod.smul_snd, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul,
      RingHom.id_apply, Complex.real_smul]
    push_cast
    ring

/- English proof (translation)
Establish `: dopL lam w f = ∑ i, (b.repr w i : ℂ) • dopL lam (b i) f`. Use extensionality with `x`. Establish `h` using `congrArg (evD lam f x) (b.sum_repr w).symm`. Rewrite `h` using `[map_sum]`. Rewrite using `[SchwartzMap.sum_apply]`.

Use `h.trans (Finset.sum_congr rfl fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[map_smul]`. Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`.
-/
theorem dopL_mem {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ (V × V)) (w : V × V) (f : 𝓢(V, ℂ)) :
    dopL lam w f ∈ Submodule.span ℂ (Set.range fun i => dopL lam (b i) f) := by
  have : dopL lam w f = ∑ i, (b.repr w i : ℂ) • dopL lam (b i) f := by
    ext x
    have h := congrArg (evD lam f x) (b.sum_repr w).symm
    rw [map_sum] at h
    rw [SchwartzMap.sum_apply]
    refine h.trans (Finset.sum_congr rfl fun i _ => ?_)
    rw [map_smul]
    rfl
  rw [this]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

def vacs (S : Set ((V × V) × V × V)) : Submodule ℂ 𝓢(V, ℂ) :=
  ⨅ γ ∈ S, LinearMap.ker (dopL lam γ.2 - Complex.I • dopL lam γ.1)

/- English proof (translation)
Simplify using `only [vacs, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, sub_eq_zero]`.
-/
theorem mem_vacs {S : Set ((V × V) × V × V)} {f : 𝓢(V, ℂ)} :
    f ∈ vacs lam S ↔ ∀ γ ∈ S, dopL lam γ.2 f = Complex.I • dopL lam γ.1 f := by
  simp only [vacs, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, sub_eq_zero]

/- English proof (translation)
Establish `hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => f (t • x) * Complex.exp (-((t : ℂ) ^ 2 * c / 2))) 0 t` using `fun t => by`. Establish `h1 : HasDerivAt (fun t : ℝ => f (t • x)) (fderiv ℝ f (t • x) x) t` using `(f.hasFDerivAt (t • x)).comp_hasDerivAt t (by simpa using (hasDerivAt_id t).smul_const x)`. Establish `h2 : HasDerivAt (fun t : ℝ => -((t : ℂ) ^ 2 * c / 2)) (-(t * c)) t`. Use `((((hasDerivAt_id t).ofReal_comp).fun_pow 2).mul_const c).div_const 2 |>.fun_neg` as an intermediate fact. Use `this.congr_deriv ?_` and prove the remaining obligations.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Use `(h1.fun_mul h2.cexp).congr_deriv ?_` and prove the remaining obligations. Rewrite using `[h]`. Expand and normalize the polynomial expressions, which then agree.

Use `is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) 1 0` as an intermediate fact. Simplify `this` using `[h0]`.
-/
theorem ray_zero (f : 𝓢(V, ℂ)) (x : V) (c : ℂ) (h : ∀ t : ℝ, fderiv ℝ f (t • x) x = t * c * f (t • x)) (h0 : f 0 = 0) : f x = 0 := by
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => f (t • x) * Complex.exp (-((t : ℂ) ^ 2 * c / 2))) 0 t := fun t => by
    have h1 : HasDerivAt (fun t : ℝ => f (t • x)) (fderiv ℝ f (t • x) x) t :=
      (f.hasFDerivAt (t • x)).comp_hasDerivAt t (by simpa using (hasDerivAt_id t).smul_const x)
    have h2 : HasDerivAt (fun t : ℝ => -((t : ℂ) ^ 2 * c / 2)) (-(t * c)) t := by
      have := ((((hasDerivAt_id t).ofReal_comp).fun_pow 2).mul_const c).div_const 2 |>.fun_neg
      refine this.congr_deriv ?_
      simp
      ring
    refine (h1.fun_mul h2.cexp).congr_deriv ?_
    rw [h]
    ring
  have := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) 1 0
  simpa [h0] using this

/- English proof (translation)
Set `Γ` to `Submodule.span ℝ S`. Establish `hΓ : ∀ f ∈ vacs lam S, ∀ x, ∀ γ ∈ Γ, evD lam f x γ.2 = Complex.I * evD lam f x γ.1` using `fun f hf x γ hγ => by`. Proceed by induction on `hγ using Submodule.span_induction with`. Consider the case `mem γ h => exact DFunLike.congr_fun ((mem_vacs lam).1 hf γ h) x`. Consider the case `zero => simp`.

Consider the case `add a b _ _ ha hb => rw [Prod.fst_add, Prod.snd_add, map_add, map_add, ha, hb, mul_add]`. Consider the case `smul c a _ ha => rw [Prod.smul_fst, Prod.smul_snd, map_smul, map_smul, ha, mul_smul_comm]`. Establish `key : ∀ f ∈ vacs lam S, f 0 = 0 → f = 0` using `fun f hf h0 => by`. Set `π : Γ →ₗ[ℝ] V × V` to `((LinearMap.fst ℝ V V).prodMap (LinearMap.fst ℝ V V)) ∘ₗ Γ.subtype`. Distinguish the cases in `hπ : Function.Injective π`.

Establish `h1` using `LinearMap.finrank_le_finrank_of_injective hπ`. Establish `h2` using `LinearMap.finrank_le_finrank_of_surjective (f := LinearMap.fst ℝ (V × V) (V × V) ∘ₗ Γ.subtype) fun p => by`. Take `⟨γ, h, e⟩` from `hS p`. Conclude with `⟨⟨γ, Submodule.subset_span h⟩, e⟩`. Establish `hs` using `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (le_antisymm h1 h2)).1 hπ`.

Use extensionality with `x`. Take `⟨⟨⟨⟨a, b⟩, a', b'⟩, hγ⟩, e⟩` from `hs (0, x)`. Take `⟨rfl, rfl⟩ : a = 0 ∧ a' = x` from `Prod.ext_iff.1 e`. Use `ray_zero f a' (2 * Real.pi * Complex.I * (lam b' a' - Complex.I * lam b a')) (fun t => ?_) h0` and prove the remaining obligations. Use `hΓ f hf (t • a') _ hγ` as an intermediate fact.

Simplify using `only [evD, LinearMap.coe_mk, AddHom.coe_mk, dopL_apply, dop_apply, map_zero, map_smul, smul_eq_mul] at this`. Move the coercions through the operations in `at this`. Take the linear combination `this`. Take `⟨⟨⟨⟨a, b⟩, a', b'⟩, hγ⟩, e, hne⟩` from `(Submodule.ne_bot_iff _).1 fun h => hπ (LinearMap.ker_eq_bot.1 h)`. Take `⟨rfl, rfl⟩ : a = 0 ∧ a' = 0` from `Prod.ext_iff.1 e`.

Establish `hz : ∀ x, f x ≠ 0 → lam b x = 0 ∧ lam b' x = 0` using `fun x hx => by`. Use `hΓ f hf x _ hγ` as an intermediate fact. Simplify using `only [evD, LinearMap.coe_mk, AddHom.coe_mk, dopL_apply, dop_apply, map_zero] at this`. Establish `h3 : (2 * Real.pi * Complex.I) * f x * (lam b' x - Complex.I * lam b x) = 0` using `by linear_combination -this`. Establish `h4` using `(mul_eq_zero.1 h3).resolve_left (mul_ne_zero (by simp [Real.pi_ne_zero]) hx)`.

Establish `h5` using `congrArg Complex.re h4`. Establish `h6` using `congrArg Complex.im h4`. Simplify using `at h5 h6`. Conclude with `⟨h6, h5⟩`. Assume the negation of the conclusion as `hf0`.

Choose the witnesses or unpack the hypotheses as in `⟨x, hx⟩ : ∃ x, f x ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Conclude with `hf0 (SchwartzMap.ext hc)`. Establish `hk : ∀ c, (∀ x, f x ≠ 0 → lam c x = 0) → c = 0` using `fun c hc => by`.

Establish `ht : LinearMap.ker (lam c).toLinearMap = ⊤` using `Submodule.eq_top_of_nonempty_interior' _ ⟨x, mem_interior.2 ⟨{y | f y ≠ 0}, hc, isOpen_ne_fun f.continuous continuous_const, hx⟩⟩`. Use `hl ?_` and prove the remaining obligations. Rewrite using `[map_zero]`. Use extensionality with `y`. Conclude with `(ht ▸ Submodule.mem_top : y ∈ LinearMap.ker (lam c).toLinearMap)`.

Take `rfl` from `hk b fun x hx => (hz x hx).1`. Take `rfl` from `hk b' fun x hx => (hz x hx).2`. Conclude with `hne rfl`. Set `ev : vacs lam S →ₗ[ℂ] ℂ` to `{ toFun := fun f => f.1 0, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }`. Conclude with `FiniteDimensional.of_injective ev ((injective_iff_map_eq_zero ev).2 fun f h => Subtype.ext (key f.1 f.2 h))`.
-/
theorem vacs_fin [FiniteDimensional ℝ V] (hl : Function.Injective lam) (S : Set ((V × V) × V × V)) (hS : ∀ p, ∃ γ ∈ S, γ.1 = p) :
    FiniteDimensional ℂ (vacs lam S) := by
  let Γ := Submodule.span ℝ S
  have hΓ : ∀ f ∈ vacs lam S, ∀ x, ∀ γ ∈ Γ, evD lam f x γ.2 = Complex.I * evD lam f x γ.1 := fun f hf x γ hγ => by
    induction hγ using Submodule.span_induction with
    | mem γ h => exact DFunLike.congr_fun ((mem_vacs lam).1 hf γ h) x
    | zero => simp
    | add a b _ _ ha hb => rw [Prod.fst_add, Prod.snd_add, map_add, map_add, ha, hb, mul_add]
    | smul c a _ ha => rw [Prod.smul_fst, Prod.smul_snd, map_smul, map_smul, ha, mul_smul_comm]
  have key : ∀ f ∈ vacs lam S, f 0 = 0 → f = 0 := fun f hf h0 => by
    let π : Γ →ₗ[ℝ] V × V := ((LinearMap.fst ℝ V V).prodMap (LinearMap.fst ℝ V V)) ∘ₗ Γ.subtype
    by_cases hπ : Function.Injective π
    · have h1 := LinearMap.finrank_le_finrank_of_injective hπ
      have h2 := LinearMap.finrank_le_finrank_of_surjective (f := LinearMap.fst ℝ (V × V) (V × V) ∘ₗ Γ.subtype) fun p => by
        obtain ⟨γ, h, e⟩ := hS p
        exact ⟨⟨γ, Submodule.subset_span h⟩, e⟩
      have hs := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (le_antisymm h1 h2)).1 hπ
      ext x
      obtain ⟨⟨⟨⟨a, b⟩, a', b'⟩, hγ⟩, e⟩ := hs (0, x)
      obtain ⟨rfl, rfl⟩ : a = 0 ∧ a' = x := Prod.ext_iff.1 e
      refine ray_zero f a' (2 * Real.pi * Complex.I * (lam b' a' - Complex.I * lam b a')) (fun t => ?_) h0
      have := hΓ f hf (t • a') _ hγ
      simp only [evD, LinearMap.coe_mk, AddHom.coe_mk, dopL_apply, dop_apply, map_zero, map_smul, smul_eq_mul] at this
      push_cast at this
      linear_combination this
    · obtain ⟨⟨⟨⟨a, b⟩, a', b'⟩, hγ⟩, e, hne⟩ := (Submodule.ne_bot_iff _).1 fun h => hπ (LinearMap.ker_eq_bot.1 h)
      obtain ⟨rfl, rfl⟩ : a = 0 ∧ a' = 0 := Prod.ext_iff.1 e
      have hz : ∀ x, f x ≠ 0 → lam b x = 0 ∧ lam b' x = 0 := fun x hx => by
        have := hΓ f hf x _ hγ
        simp only [evD, LinearMap.coe_mk, AddHom.coe_mk, dopL_apply, dop_apply, map_zero] at this
        have h3 : (2 * Real.pi * Complex.I) * f x * (lam b' x - Complex.I * lam b x) = 0 := by linear_combination -this
        have h4 := (mul_eq_zero.1 h3).resolve_left (mul_ne_zero (by simp [Real.pi_ne_zero]) hx)
        have h5 := congrArg Complex.re h4
        have h6 := congrArg Complex.im h4
        simp at h5 h6
        exact ⟨h6, h5⟩
      by_contra hf0
      obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
        by_contra hc
        push Not at hc
        exact hf0 (SchwartzMap.ext hc)
      have hk : ∀ c, (∀ x, f x ≠ 0 → lam c x = 0) → c = 0 := fun c hc => by
        have ht : LinearMap.ker (lam c).toLinearMap = ⊤ := Submodule.eq_top_of_nonempty_interior' _
          ⟨x, mem_interior.2 ⟨{y | f y ≠ 0}, hc, isOpen_ne_fun f.continuous continuous_const, hx⟩⟩
        refine hl ?_
        rw [map_zero]
        ext y
        exact (ht ▸ Submodule.mem_top : y ∈ LinearMap.ker (lam c).toLinearMap)
      obtain rfl := hk b fun x hx => (hz x hx).1
      obtain rfl := hk b' fun x hx => (hz x hx).2
      exact hne rfl
  let ev : vacs lam S →ₗ[ℂ] ℂ := { toFun := fun f => f.1 0, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  exact FiniteDimensional.of_injective ev ((injective_iff_map_eq_zero ev).2 fun f h => Subtype.ext (key f.1 f.2 h))

/- English proof (translation)
Take `⟨s, -, hs⟩` from `hC.elim_nhds_subcover (fun y => {y' | y' - y ∈ U}) fun y _ => (continuous_id.sub continuous_const).continuousAt.preimage_mem_nhds (by simpa using hU)`. Set `ev : N →ₗ[ℂ] (s → P.map c)` to `{ toFun := fun Ψ y => ⟨fun x => Ψ.1 (pt x y), by`. Take `⟨f, hf, e⟩` from `h1 _ Ψ.2 y`. Conclude with `⟨f, hf, funext fun x => (e x).symm⟩⟩`. Use the proof step `map_add' := fun _ _ => rfl`.

Use the proof step `map_smul' := fun _ _ => rfl }`. Use `FiniteDimensional.of_injective ev ((injective_iff_map_eq_zero ev).2 fun Ψ h => Subtype.ext (funext fun z => ?_))` and prove the remaining obligations. Take `⟨x, y, rfl⟩` from `hpt z`. Distinguish the cases in `hy : y ∈ C`. Take `⟨y₀, h₀, hy₀⟩` from `Set.mem_iUnion₂.1 (hs hy)`.

Use `h3 _ Ψ.2 x y₀ _ hy₀` as an intermediate fact. Rewrite `this` using `[add_sub_cancel]`. Rewrite using `[this]`. Conclude with `congrFun (congrArg Subtype.val (congrFun h ⟨y₀, h₀⟩)) x`. Conclude with `h2 _ Ψ.2 x y hy`.
-/
theorem level_fin {X Y Z S : Type} [AddCommGroup Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y] [AddCommGroup S] [Module ℂ S]
    (pt : X → Y → Z) (hpt : ∀ z, ∃ x y, z = pt x y) (c : S →ₗ[ℂ] (X → ℂ)) (P : Submodule ℂ S) [FiniteDimensional ℂ P] {C U : Set Y}
    (hC : IsCompact C) (hU : U ∈ nhds 0) (N : Submodule ℂ (Z → ℂ)) (h1 : ∀ Ψ ∈ N, ∀ y, ∃ f ∈ P, ∀ x, Ψ (pt x y) = c f x)
    (h2 : ∀ Ψ ∈ N, ∀ x, ∀ y ∉ C, Ψ (pt x y) = 0) (h3 : ∀ Ψ ∈ N, ∀ x y, ∀ u ∈ U, Ψ (pt x (y + u)) = Ψ (pt x y)) :
    FiniteDimensional ℂ N := by
  obtain ⟨s, -, hs⟩ := hC.elim_nhds_subcover (fun y => {y' | y' - y ∈ U}) fun y _ =>
    (continuous_id.sub continuous_const).continuousAt.preimage_mem_nhds (by simpa using hU)
  let ev : N →ₗ[ℂ] (s → P.map c) :=
    { toFun := fun Ψ y => ⟨fun x => Ψ.1 (pt x y), by
        obtain ⟨f, hf, e⟩ := h1 _ Ψ.2 y
        exact ⟨f, hf, funext fun x => (e x).symm⟩⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine FiniteDimensional.of_injective ev ((injective_iff_map_eq_zero ev).2 fun Ψ h => Subtype.ext (funext fun z => ?_))
  obtain ⟨x, y, rfl⟩ := hpt z
  by_cases hy : y ∈ C
  · obtain ⟨y₀, h₀, hy₀⟩ := Set.mem_iUnion₂.1 (hs hy)
    have := h3 _ Ψ.2 x y₀ _ hy₀
    rw [add_sub_cancel] at this
    rw [this]
    exact congrFun (congrArg Subtype.val (congrFun h ⟨y₀, h₀⟩)) x
  · exact h2 _ Ψ.2 x y hy

end PositivityTheory.ThKCT.So

end
