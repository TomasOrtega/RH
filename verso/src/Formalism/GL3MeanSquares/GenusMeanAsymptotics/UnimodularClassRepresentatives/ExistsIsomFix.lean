import Formalism.HermitianLattices.StatementLat

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.WA

variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]

def quasiRefl (h : V →ₗ⋆[K] V →ₗ[K] K) (u : V) (a : K) : V →ₗ[K] V :=
  LinearMap.id - a • (h u).smulRight u

/- English proof (translation)
Use `first`. Consider the case `simp [quasiRefl, smul_smul]`. Consider the case `rw [quasiRefl, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply, LinearMap.smulRight_apply, smul_smul]`.
-/
theorem quasiRefl_apply (h : V →ₗ⋆[K] V →ₗ[K] K) (u : V) (a : K) (v : V) :
    quasiRefl h u a v = v - (a * h u v) • u := by
  first
  | simp [quasiRefl, smul_smul]
  | rw [quasiRefl, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply,
      LinearMap.smulRight_apply, smul_smul]

/- English proof (translation)
Use extensionality with `v`. Simplify using `only [LinearMap.comp_apply, LinearMap.id_apply]`. Rewrite using `[quasiRefl_apply, quasiRefl_apply]`. Simplify using `only [map_sub, map_smul, map_smulₛₗ, RingHom.id_apply, smul_eq_mul]`. Rewrite using `[sub_sub, ← add_smul, sub_eq_self, smul_eq_zero]`.

Use `left`. Take the linear combination `(h u v) * hab`.
-/
theorem quasiRefl_comp (h : V →ₗ⋆[K] V →ₗ[K] K) (u : V) {a b : K}
    (hab : a + b = a * b * h u u) : quasiRefl h u a ∘ₗ quasiRefl h u b = LinearMap.id := by
  ext v
  simp only [LinearMap.comp_apply, LinearMap.id_apply]
  rw [quasiRefl_apply, quasiRefl_apply]
  simp only [map_sub, map_smul, map_smulₛₗ, RingHom.id_apply, smul_eq_mul]
  rw [sub_sub, ← add_smul, sub_eq_self, smul_eq_zero]
  left
  linear_combination (h u v) * hab

/- English proof (translation)
Establish `hsym : star (h u v) = h v u`. Use `hs.eq u v` as an intermediate fact. Simplify `this` using `[starRingEnd_apply]`. Rewrite using `[quasiRefl_apply, quasiRefl_apply]`. Simplify using `only [map_sub, map_smulₛₗ, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_mul, hsym, RingHom.id_apply]`.

Take the linear combination `(-(h v u * h u w)) * ha`.
-/
theorem quasiRefl_isom {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (u : V) {a : K}
    (ha : a + star a = a * star a * h u u) (v w : V) :
    h (quasiRefl h u a v) (quasiRefl h u a w) = h v w := by
  have hsym : star (h u v) = h v u := by
    have := hs.eq u v
    simpa [starRingEnd_apply] using this
  rw [quasiRefl_apply, quasiRefl_apply]
  simp only [map_sub, map_smulₛₗ, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
    starRingEnd_apply, star_mul, hsym, RingHom.id_apply]
  linear_combination (-(h v u * h u w)) * ha

/- English proof (translation)
Establish `hsym : ∀ p q : V, star (h p q) = h q p` using `fun p q => by`. Use `hs.eq p q` as an intermediate fact. Simplify `this` using `[starRingEnd_apply]`. Distinguish the cases in `hyx : h y x = 1`. Establish `hxy : h x y = 1` using `by rw [← hsym, hyx, star_one]`.

Establish `hu : h (x - y) (x - y) = 0`. Simplify using `only [map_sub, LinearMap.sub_apply, hx, hy, hxy, hyx]`. Expand and normalize the polynomial expressions, which then agree. Establish `hxy' : x = y` using `sub_eq_zero.mp (hd _ hu)`. Substitute `hxy'` using the available equality.

Conclude with `⟨1, one_mem _, rfl, fun v _ _ => rfl⟩`. Establish `hp : (1 : K) - h y x ≠ 0` using `sub_ne_zero.mpr (Ne.symm hyx)`. Establish `hq : (1 : K) - h x y ≠ 0`. Introduce `h0`. Apply `hp` to reduce the goal to its premises.

Use `congrArg star h0` as an intermediate fact. Rewrite `this` using `[star_sub, star_one, hsym, star_zero]`. Conclude with `this`. Establish `huu : h (x - y) (x - y) = (1 - h y x) + (1 - h x y)`. Simplify using `only [map_sub, LinearMap.sub_apply, hx, hy]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hux : h (x - y) x = 1 - h y x`. Simplify using `only [map_sub, LinearMap.sub_apply, hx]`. Establish `hsa : star ((1 - h y x)⁻¹) = (1 - h x y)⁻¹` using `by first`. Consider the case `rw [star_inv₀, star_sub, star_one, hsym]`.

Consider the case `rw [star_inv', star_sub, star_one, hsym]`. Establish `e1 : (1 - h y x)⁻¹ * (1 - h y x) = 1` using `inv_mul_cancel₀ hp`. Establish `e2 : (1 - h x y)⁻¹ * (1 - h x y) = 1` using `inv_mul_cancel₀ hq`. Establish `ha : (1 - h y x)⁻¹ + star ((1 - h y x)⁻¹) = (1 - h y x)⁻¹ * star ((1 - h y x)⁻¹) * h (x - y) (x - y)`. Rewrite using `[hsa, huu]`.

Take the linear combination `(-(1 - h x y)⁻¹) * e1 - (1 - h y x)⁻¹ * e2`. Establish `hb : star ((1 - h y x)⁻¹) + (1 - h y x)⁻¹ = star ((1 - h y x)⁻¹) * (1 - h y x)⁻¹ * h (x - y) (x - y)`. Rewrite using `[add_comm, mul_comm (star _) _]`. Conclude with `ha`. Use `⟨LinearEquiv.ofLinear (quasiRefl h (x - y) ((1 - h y x)⁻¹)) (quasiRefl h (x - y) (star ((1 - h y x)⁻¹))) (quasiRefl_comp h (x - y) ha) (quasiRefl_comp h (x - y) hb), ?_, ?_, ?_⟩` and prove the remaining obligations.

Use `first`. Consider the case `exact fun v w => quasiRefl_isom hs (x - y) ha v w`. Consider the case `(intro v w; exact quasiRefl_isom hs (x - y) ha v w)`. Consider the case `(show ∀ v w, _ = _; intro v w; exact quasiRefl_isom hs (x - y) ha v w)`. Use `show quasiRefl h (x - y) ((1 - h y x)⁻¹) x = y`.

Rewrite using `[quasiRefl_apply, hux, inv_mul_cancel₀ hp, one_smul, sub_sub_cancel]`. Introduce `v h1 h2 show quasiRefl h (x - y) ((1 - h y x)⁻¹) v = v`. Rewrite using `[quasiRefl_apply, map_sub, LinearMap.sub_apply, h1, h2, sub_zero, mul_zero, zero_smul, sub_zero]`.
-/
theorem exists_isom_fix {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : ∀ x, h x x = 0 → x = 0)
    {x y : V} (hx : h x x = 1) (hy : h y y = 1) :
    ∃ τ ∈ Formalism.HermitianLatticesTheory.isom h, τ x = y ∧ ∀ v, h x v = 0 → h y v = 0 → τ v = v := by
  have hsym : ∀ p q : V, star (h p q) = h q p := fun p q => by
    have := hs.eq p q
    simpa [starRingEnd_apply] using this
  by_cases hyx : h y x = 1
  · have hxy : h x y = 1 := by rw [← hsym, hyx, star_one]
    have hu : h (x - y) (x - y) = 0 := by
      simp only [map_sub, LinearMap.sub_apply, hx, hy, hxy, hyx]; ring
    have hxy' : x = y := sub_eq_zero.mp (hd _ hu)
    subst hxy'
    exact ⟨1, one_mem _, rfl, fun v _ _ => rfl⟩
  · have hp : (1 : K) - h y x ≠ 0 := sub_ne_zero.mpr (Ne.symm hyx)
    have hq : (1 : K) - h x y ≠ 0 := by
      intro h0
      apply hp
      have := congrArg star h0
      rw [star_sub, star_one, hsym, star_zero] at this
      exact this
    have huu : h (x - y) (x - y) = (1 - h y x) + (1 - h x y) := by
      simp only [map_sub, LinearMap.sub_apply, hx, hy]; ring
    have hux : h (x - y) x = 1 - h y x := by
      simp only [map_sub, LinearMap.sub_apply, hx]
    have hsa : star ((1 - h y x)⁻¹) = (1 - h x y)⁻¹ := by
      first
      | rw [star_inv₀, star_sub, star_one, hsym]
      | rw [star_inv', star_sub, star_one, hsym]
    have e1 : (1 - h y x)⁻¹ * (1 - h y x) = 1 := inv_mul_cancel₀ hp
    have e2 : (1 - h x y)⁻¹ * (1 - h x y) = 1 := inv_mul_cancel₀ hq
    have ha : (1 - h y x)⁻¹ + star ((1 - h y x)⁻¹) =
        (1 - h y x)⁻¹ * star ((1 - h y x)⁻¹) * h (x - y) (x - y) := by
      rw [hsa, huu]
      linear_combination (-(1 - h x y)⁻¹) * e1 - (1 - h y x)⁻¹ * e2
    have hb : star ((1 - h y x)⁻¹) + (1 - h y x)⁻¹ =
        star ((1 - h y x)⁻¹) * (1 - h y x)⁻¹ * h (x - y) (x - y) := by
      rw [add_comm, mul_comm (star _) _]; exact ha
    refine ⟨LinearEquiv.ofLinear (quasiRefl h (x - y) ((1 - h y x)⁻¹))
      (quasiRefl h (x - y) (star ((1 - h y x)⁻¹))) (quasiRefl_comp h (x - y) ha)
      (quasiRefl_comp h (x - y) hb), ?_, ?_, ?_⟩
    · first
      | exact fun v w => quasiRefl_isom hs (x - y) ha v w
      | (intro v w; exact quasiRefl_isom hs (x - y) ha v w)
      | (show ∀ v w, _ = _; intro v w; exact quasiRefl_isom hs (x - y) ha v w)
    · show quasiRefl h (x - y) ((1 - h y x)⁻¹) x = y
      rw [quasiRefl_apply, hux, inv_mul_cancel₀ hp, one_smul, sub_sub_cancel]
    · intro v h1 h2
      show quasiRefl h (x - y) ((1 - h y x)⁻¹) v = v
      rw [quasiRefl_apply, map_sub, LinearMap.sub_apply, h1, h2, sub_zero, mul_zero, zero_smul, sub_zero]

end Formalism.HermitianLattices.Ext.L3.WA
