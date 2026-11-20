import Mathlib

open Topology Filter

namespace GlobalTheory.SmoothFix

/- English proof (translation)
Establish `h1 : ∀ k : ℕ, (3 / 2 : ℝ) ^ k * ‖x - 1‖ ≤ ‖x ^ (2 ^ k) - 1‖` using `fun k => by`. Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Take `⟨y, hy⟩ : ∃ y, y = x ^ (2 ^ k) - 1` from `⟨_, rfl⟩`.

Establish `e : (2 : ℂ) • y = (x ^ (2 ^ (k + 1)) - 1) - y * y`. Rewrite using `[pow_succ 2, pow_mul, hy, two_smul, sq]`. Use `noncomm_ring`. Establish `h2 : 2 * ‖y‖ ≤ ‖x ^ (2 ^ (k + 1)) - 1‖ + ‖y‖ * ‖y‖`. Use `norm_sub_le (x ^ (2 ^ (k + 1)) - 1) (y * y)` as an intermediate fact.

Rewrite `this` using `[← e, norm_smul, Complex.norm_ofNat]`. Combine the linear relations using `[norm_mul_le y y]`. Establish `h3 : ‖y‖ * ‖y‖ ≤ 1 / 2 * ‖y‖` using `mul_le_mul_of_nonneg_right (hy ▸ h _) (norm_nonneg y)`. Rewrite `ih` using `[← hy]`. Rewrite using `[pow_succ]`.

Combine the linear equalities and inequalities to obtain the conclusion. Assume the negation of the conclusion as `hz`. Establish `hp : 0 < ‖x - 1‖` using `norm_pos_iff.mpr (sub_ne_zero.mpr hz)`. Take `⟨k, hk⟩` from `pow_unbounded_of_one_lt (‖x - 1‖⁻¹) (show (1 : ℝ) < 3 / 2 by norm_num)`. Establish `h4` using `(h1 k).trans (h _)`.

Establish `h5` using `mul_lt_mul_of_pos_right hk hp`. Rewrite `h5` using `[inv_mul_cancel₀ hp.ne']`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem eq_one_of_pow_norm_sub_one_le_half {A : Type} [NormedRing A] [NormedAlgebra ℂ A] {x : A}
    (h : ∀ m : ℕ, ‖x ^ m - 1‖ ≤ 1 / 2) : x = 1 := by
  have h1 : ∀ k : ℕ, (3 / 2 : ℝ) ^ k * ‖x - 1‖ ≤ ‖x ^ (2 ^ k) - 1‖ := fun k => by
    induction k with
    | zero => simp
    | succ k ih =>
      obtain ⟨y, hy⟩ : ∃ y, y = x ^ (2 ^ k) - 1 := ⟨_, rfl⟩
      have e : (2 : ℂ) • y = (x ^ (2 ^ (k + 1)) - 1) - y * y := by
        rw [pow_succ 2, pow_mul, hy, two_smul, sq]; noncomm_ring
      have h2 : 2 * ‖y‖ ≤ ‖x ^ (2 ^ (k + 1)) - 1‖ + ‖y‖ * ‖y‖ := by
        have := norm_sub_le (x ^ (2 ^ (k + 1)) - 1) (y * y)
        rw [← e, norm_smul, Complex.norm_ofNat] at this
        linarith [norm_mul_le y y]
      have h3 : ‖y‖ * ‖y‖ ≤ 1 / 2 * ‖y‖ := mul_le_mul_of_nonneg_right (hy ▸ h _) (norm_nonneg y)
      rw [← hy] at ih
      rw [pow_succ]
      linarith
  by_contra hz
  have hp : 0 < ‖x - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (‖x - 1‖⁻¹) (show (1 : ℝ) < 3 / 2 by norm_num)
  have h4 := (h1 k).trans (h _)
  have h5 := mul_lt_mul_of_pos_right hk hp
  rw [inv_mul_cancel₀ hp.ne'] at h5
  linarith

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/- English proof (translation)
Introduce `hfd G _ _ H V _ _ S hmul h1 hcont hsmall v`. Take `⟨K₀, hK₀H, hK₀c, ⟨O₀, hO₀o, hO₀1, hO₀K⟩, -⟩` from `hsmall Set.univ univ_mem`. Set `s : Set V` to `(fun k => S k v) '' (K₀ : Set G)`. Establish `hb : ∀ l : V →ₗ[ℂ] ℂ, ∃ C : ℝ, ∀ x ∈ s, ‖l x‖ ≤ C`. Introduce `l`.

Take `⟨C, hC⟩` from `hK₀c.exists_bound_of_continuousOn ((hcont l v).mono hK₀H)`. Conclude with `⟨C, by rintro _ ⟨k, hk, rfl⟩; exact hC k hk⟩`. Use `haveI : FiniteDimensional ℂ (Submodule.span ℂ s) := hfd s hb`. Use `set W := Submodule.span ℂ s with hW`. Establish `hinv : ∀ k ∈ K₀, ∀ w ∈ W, S k w ∈ W`.

Introduce `k hk w hw`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨k', hk', rfl⟩` from `hx`. Use `show S k (S k' v) ∈ W`.

Rewrite using `[← Module.End.mul_apply, ← hmul k (hK₀H hk) k' (hK₀H hk')]`. Conclude with `Submodule.subset_span ⟨k * k', K₀.mul_mem hk hk', rfl⟩`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `W.add_mem hx hy`.

Consider the case `smul c x _ hx => rw [map_smul]`. Conclude with `W.smul_mem c hx`. Set `R : K₀ → Module.End ℂ W` to `fun k => (S k).restrict (hinv k.1 k.2)`. Establish `hRv : ∀ (k : K₀) (w : W), (R k w : V) = S k w` using `fun _ _ => rfl`. Establish `hRpow : ∀ (k : K₀) (m : ℕ), R (k ^ m) = R k ^ m`.

Introduce `k m`. Proceed by induction on `m with`. Consider the case `zero`. Use extensionality with `w`. Simplify using `[hRv, h1]`.

Consider the case `succ m ih`. Use extensionality with `w`. Rewrite using `[pow_succ, pow_succ, Module.End.mul_apply, ← ih, hRv, hRv, hRv]`. Establish `hm : ((k ^ m : K₀) : G) ∈ H` using `hK₀H (k ^ m).2`. Simplify using `only [Subgroup.coe_mul]`.

Rewrite using `[hmul _ hm _ (hK₀H k.2), Module.End.mul_apply]`. Set `b` to `Module.finBasis ℂ W`. Use `choose c hc using fun i => LinearMap.exists_extend (b.coord i)`. Set `M : G → Matrix (Fin (Module.finrank ℂ W)) (Fin (Module.finrank ℂ W)) ℂ` to `fun x i j => c i (S x (b j))`. Establish `hMR : ∀ k : K₀, LinearMap.toMatrixAlgEquiv b (R k) = M k`.

Introduce `k`. Use extensionality with `i j`. Rewrite using `[LinearMap.toMatrixAlgEquiv_apply]`. Use `LinearMap.congr_fun (hc i) (R k (b j))` as an intermediate fact. Simplify using `only [LinearMap.comp_apply, Submodule.subtype_apply, Module.Basis.coord_apply] at this`.

Rewrite using `[← this, hRv]`. Establish `hR1 : R 1 = 1`. Use extensionality with `w`. Simplify using `[hRv, h1]`. Establish `hM1 : M 1 = 1`.

Use `hMR 1` as an intermediate fact. Rewrite `this` using `[hR1, map_one]`. Simplify using `using this.symm`. Establish `hM : ContinuousOn M (H : Set G)` using `continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => hcont (c i) (b j)`. Establish `hN : ContinuousWithinAt (fun x => ‖M x - 1‖) (H : Set G) 1` using `((hM 1 H.one_mem).sub continuousWithinAt_const).norm`.

Establish `hev : {x | ‖M x - 1‖ < 1 / 2} ∈ 𝓝[(H : Set G)] 1` using `hN (Iio_mem_nhds (by show ‖M 1 - 1‖ < 1 / 2; rw [hM1, sub_self, norm_zero]; norm_num))`. Take `⟨u, hu, h1u, hsub⟩` from `mem_nhdsWithin.1 hev`. Take `⟨K, hKH, -, ⟨O, hOo, hO1, hOK⟩, hKU⟩` from `hsmall (u ∩ O₀) (Filter.inter_mem (hu.mem_nhds h1u) (hO₀o.mem_nhds hO₀1))`. Establish `hvW : v ∈ W` using `Submodule.subset_span ⟨1, K₀.one_mem, by simp [h1]⟩`. Use `⟨O, hOo.mem_nhds hO1, fun x hxO hxH => ?_⟩` and prove the remaining obligations.

Establish `hxK : x ∈ K` using `hOK x hxO hxH`. Establish `hxK₀ : x ∈ K₀` using `hO₀K x (hKU hxK).2 (hKH hxK)`. Set `kk : K₀` to `⟨x, hxK₀⟩`. Establish `hpow : ∀ m : ℕ, ‖(LinearMap.toMatrixAlgEquiv b (R kk)) ^ m - 1‖ ≤ 1 / 2`. Introduce `m`.

Rewrite using `[← map_pow, ← hRpow, hMR]`. Establish `hm : x ^ m ∈ K` using `K.pow_mem hxK m`. Use `hsub ⟨(hKU hm).1, hKH hm⟩` as an intermediate fact. Conclude with `le_of_lt (by simpa using this)`. Establish `hone` using `eq_one_of_pow_norm_sub_one_le_half hpow`.

Rewrite `hone` using `[← map_one (LinearMap.toMatrixAlgEquiv b)]`. Establish `hRk` using `(LinearMap.toMatrixAlgEquiv b).injective hone`. Use `congrArg Subtype.val (LinearMap.congr_fun hRk ⟨v, hvW⟩)` as an intermediate fact. Simplify `this` using `[hRv]`.
-/
theorem exists_nhds_fix : (∀ {V : Type} [AddCommGroup V] [Module ℂ V] (s : Set V),
    (∀ l : V →ₗ[ℂ] ℂ, ∃ C : ℝ, ∀ x ∈ s, ‖l x‖ ≤ C) → FiniteDimensional ℂ (Submodule.span ℂ s)) →
  ∀ {G : Type} [Group G] [TopologicalSpace G] (H : Subgroup G) {V : Type} [AddCommGroup V] [Module ℂ V]
    (S : G → Module.End ℂ V), (∀ x ∈ H, ∀ y ∈ H, S (x * y) = S x * S y) → S 1 = 1 →
    (∀ (l : V →ₗ[ℂ] ℂ) (w : V), ContinuousOn (fun x => l (S x w)) (H : Set G)) →
    (∀ U ∈ 𝓝 (1 : G), ∃ K : Subgroup G, K ≤ H ∧ IsCompact (K : Set G) ∧
      (∃ O : Set G, IsOpen O ∧ (1 : G) ∈ O ∧ ∀ x ∈ O, x ∈ H → x ∈ K) ∧ (K : Set G) ⊆ U) →
    ∀ v : V, ∃ U ∈ 𝓝 (1 : G), ∀ x ∈ U, x ∈ H → S x v = v := by
  intro hfd G _ _ H V _ _ S hmul h1 hcont hsmall v
  obtain ⟨K₀, hK₀H, hK₀c, ⟨O₀, hO₀o, hO₀1, hO₀K⟩, -⟩ := hsmall Set.univ univ_mem
  let s : Set V := (fun k => S k v) '' (K₀ : Set G)
  have hb : ∀ l : V →ₗ[ℂ] ℂ, ∃ C : ℝ, ∀ x ∈ s, ‖l x‖ ≤ C := by
    intro l
    obtain ⟨C, hC⟩ := hK₀c.exists_bound_of_continuousOn ((hcont l v).mono hK₀H)
    exact ⟨C, by rintro _ ⟨k, hk, rfl⟩; exact hC k hk⟩
  haveI : FiniteDimensional ℂ (Submodule.span ℂ s) := hfd s hb
  set W := Submodule.span ℂ s with hW
  have hinv : ∀ k ∈ K₀, ∀ w ∈ W, S k w ∈ W := by
    intro k hk w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k', hk', rfl⟩ := hx
      show S k (S k' v) ∈ W
      rw [← Module.End.mul_apply, ← hmul k (hK₀H hk) k' (hK₀H hk')]
      exact Submodule.subset_span ⟨k * k', K₀.mul_mem hk hk', rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact W.add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact W.smul_mem c hx
  let R : K₀ → Module.End ℂ W := fun k => (S k).restrict (hinv k.1 k.2)
  have hRv : ∀ (k : K₀) (w : W), (R k w : V) = S k w := fun _ _ => rfl
  have hRpow : ∀ (k : K₀) (m : ℕ), R (k ^ m) = R k ^ m := by
    intro k m
    induction m with
    | zero =>
      ext w
      simp [hRv, h1]
    | succ m ih =>
      ext w
      rw [pow_succ, pow_succ, Module.End.mul_apply, ← ih, hRv, hRv, hRv]
      have hm : ((k ^ m : K₀) : G) ∈ H := hK₀H (k ^ m).2
      simp only [Subgroup.coe_mul]
      rw [hmul _ hm _ (hK₀H k.2), Module.End.mul_apply]
  let b := Module.finBasis ℂ W
  choose c hc using fun i => LinearMap.exists_extend (b.coord i)
  let M : G → Matrix (Fin (Module.finrank ℂ W)) (Fin (Module.finrank ℂ W)) ℂ := fun x i j => c i (S x (b j))
  have hMR : ∀ k : K₀, LinearMap.toMatrixAlgEquiv b (R k) = M k := by
    intro k
    ext i j
    rw [LinearMap.toMatrixAlgEquiv_apply]
    have := LinearMap.congr_fun (hc i) (R k (b j))
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, Module.Basis.coord_apply] at this
    rw [← this, hRv]
  have hR1 : R 1 = 1 := by
    ext w
    simp [hRv, h1]
  have hM1 : M 1 = 1 := by
    have := hMR 1
    rw [hR1, map_one] at this
    simpa using this.symm
  have hM : ContinuousOn M (H : Set G) :=
    continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => hcont (c i) (b j)
  have hN : ContinuousWithinAt (fun x => ‖M x - 1‖) (H : Set G) 1 :=
    ((hM 1 H.one_mem).sub continuousWithinAt_const).norm
  have hev : {x | ‖M x - 1‖ < 1 / 2} ∈ 𝓝[(H : Set G)] 1 :=
    hN (Iio_mem_nhds (by show ‖M 1 - 1‖ < 1 / 2; rw [hM1, sub_self, norm_zero]; norm_num))
  obtain ⟨u, hu, h1u, hsub⟩ := mem_nhdsWithin.1 hev
  obtain ⟨K, hKH, -, ⟨O, hOo, hO1, hOK⟩, hKU⟩ :=
    hsmall (u ∩ O₀) (Filter.inter_mem (hu.mem_nhds h1u) (hO₀o.mem_nhds hO₀1))
  have hvW : v ∈ W := Submodule.subset_span ⟨1, K₀.one_mem, by simp [h1]⟩
  refine ⟨O, hOo.mem_nhds hO1, fun x hxO hxH => ?_⟩
  have hxK : x ∈ K := hOK x hxO hxH
  have hxK₀ : x ∈ K₀ := hO₀K x (hKU hxK).2 (hKH hxK)
  let kk : K₀ := ⟨x, hxK₀⟩
  have hpow : ∀ m : ℕ, ‖(LinearMap.toMatrixAlgEquiv b (R kk)) ^ m - 1‖ ≤ 1 / 2 := by
    intro m
    rw [← map_pow, ← hRpow, hMR]
    have hm : x ^ m ∈ K := K.pow_mem hxK m
    have := hsub ⟨(hKU hm).1, hKH hm⟩
    exact le_of_lt (by simpa using this)
  have hone := eq_one_of_pow_norm_sub_one_le_half hpow
  rw [← map_one (LinearMap.toMatrixAlgEquiv b)] at hone
  have hRk := (LinearMap.toMatrixAlgEquiv b).injective hone
  have := congrArg Subtype.val (LinearMap.congr_fun hRk ⟨v, hvW⟩)
  simpa [hRv] using this

end GlobalTheory.SmoothFix
