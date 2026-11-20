import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.AdelicThetaPoissonSummation

noncomputable section

open Module

namespace Formalism.L2.SG.Pf.G4

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA

variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K}

/- English proof (translation)
Establish `hsym : ∀ u v, star (h u v) = h v u` using `fun u v => by`. Rewrite using `[← starRingEnd_apply]`. Conclude with `hs.eq u v`. Take `⟨z, hz⟩ : ∃ z, z = x - y` from `⟨_, rfl⟩`. Take `⟨b, hbd⟩ : ∃ b, b = h x x - h y x` from `⟨_, rfl⟩`.

Establish `hb0 : b ≠ 0` using `hbd ▸ hb`. Establish `hsb0 : star b ≠ 0` using `star_ne_zero.2 hb0`. Establish `hzx : h z x = b`. Rewrite using `[hz, hbd, map_sub, LinearMap.sub_apply]`. Establish `hzv : ∀ v, h z v = h x v - h y v` using `fun v => by`.

Rewrite using `[hz, map_sub, LinearMap.sub_apply]`. Establish `hzz : h z z = b + star b`. Establish `h1 : star b = h x x - h x y`. Rewrite using `[hbd, star_sub, hsym, hsym]`. Rewrite using `[h1, hbd, hzv, hz, map_sub, map_sub, hxy]`.

Expand and normalize the polynomial expressions, which then agree. Set `τl : V →ₗ[K] V` to `LinearMap.id - (b⁻¹ • h z).smulRight z`. Set `σl : V →ₗ[K] V` to `LinearMap.id - ((star b)⁻¹ • h z).smulRight z`. Establish `hτ : ∀ v, τl v = v - (b⁻¹ * h z v) • z` using `fun v => rfl`. Establish `hσ : ∀ v, σl v = v - ((star b)⁻¹ * h z v) • z` using `fun v => rfl`.

Establish `key : ∀ c d : K, c + d = c * d * h z z → ∀ v : V, (v - (c * h z v) • z) - (d * h z (v - (c * h z v) • z)) • z = v`. Introduce `c d hcd v`. Rewrite using `[map_sub, map_smul, smul_eq_mul, sub_sub, ← add_smul]`. Establish `h0 : c * h z v + d * (h z v - c * h z v * h z z) = 0`. Take the linear combination `(h z v) * hcd`.

Rewrite using `[h0, zero_smul, sub_zero]`. Establish `hcd : (star b)⁻¹ + b⁻¹ = (star b)⁻¹ * b⁻¹ * h z z`. Rewrite using `[hzz]`. Clear the denominators using the available nonvanishing facts. Apply the tactic sequence `try ring`.

Establish `h₁ : τl.comp σl = LinearMap.id`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `v`. Use `show τl (σl v) = v`. Rewrite using `[hτ, hσ]`.

Conclude with `key _ _ hcd v`. Establish `h₂ : σl.comp τl = LinearMap.id`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `v`. Use `show σl (τl v) = v`.

Rewrite using `[hσ, hτ]`. Conclude with `key _ _ (by rw [add_comm, mul_comm b⁻¹]; exact hcd) v`. Use `⟨LinearEquiv.ofLinear τl σl h₁ h₂, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `show ∀ u v, h (τl u) (τl v) = h u v`. Introduce `u v`.

Rewrite using `[hτ, hτ]`. Establish `hu : h u z = star (h z u)` using `(hsym z u).symm`. Simplify using `only [map_sub, map_smulₛₗ, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_mul, star_inv₀, RingHom.id_apply, hu, hzz]`. Clear the denominators using the available nonvanishing facts. Apply the tactic sequence `try ring`.

Use `show τl x = y`. Rewrite using `[hτ, hzx, inv_mul_cancel₀ hb0, one_smul, hz, sub_sub_cancel]`. Introduce `v hxv hyv show τl v = v`. Rewrite using `[hτ, hzv, hxv, hyv, sub_zero, mul_zero, zero_smul, sub_zero]`. Introduce `W hxW hyW v`.

Establish `hzW : z ∈ W` using `hz ▸ W.sub_mem hxW hyW`. Use `show v ∈ W ↔ τl v ∈ W`. Rewrite using `[hτ]`. Prove the components needed by the constructor for the conclusion. Introduce `hv`.

Conclude with `W.sub_mem hv (W.smul_mem _ hzW)`. Introduce `hv`. Use `W.add_mem hv (W.smul_mem (b⁻¹ * h z v) hzW)` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis.
-/
theorem exists_isom_move' (hs : h.IsSymm) {x y : V} (hxy : h x x = h y y)
    (hb : h x x - h y x ≠ 0) :
    ∃ τ ∈ Formalism.HermitianLatticesTheory.isom h, τ x = y ∧ (∀ v, h x v = 0 → h y v = 0 → τ v = v) ∧
      ∀ W : Submodule K V, x ∈ W → y ∈ W → ∀ v, v ∈ W ↔ τ v ∈ W := by
  have hsym : ∀ u v, star (h u v) = h v u := fun u v => by
    rw [← starRingEnd_apply]
    exact hs.eq u v
  obtain ⟨z, hz⟩ : ∃ z, z = x - y := ⟨_, rfl⟩
  obtain ⟨b, hbd⟩ : ∃ b, b = h x x - h y x := ⟨_, rfl⟩
  have hb0 : b ≠ 0 := hbd ▸ hb
  have hsb0 : star b ≠ 0 := star_ne_zero.2 hb0
  have hzx : h z x = b := by
    rw [hz, hbd, map_sub, LinearMap.sub_apply]
  have hzv : ∀ v, h z v = h x v - h y v := fun v => by
    rw [hz, map_sub, LinearMap.sub_apply]
  have hzz : h z z = b + star b := by
    have h1 : star b = h x x - h x y := by
      rw [hbd, star_sub, hsym, hsym]
    rw [h1, hbd, hzv, hz, map_sub, map_sub, hxy]
    ring
  let τl : V →ₗ[K] V := LinearMap.id - (b⁻¹ • h z).smulRight z
  let σl : V →ₗ[K] V := LinearMap.id - ((star b)⁻¹ • h z).smulRight z
  have hτ : ∀ v, τl v = v - (b⁻¹ * h z v) • z := fun v => rfl
  have hσ : ∀ v, σl v = v - ((star b)⁻¹ * h z v) • z := fun v => rfl
  have key : ∀ c d : K, c + d = c * d * h z z → ∀ v : V,
      (v - (c * h z v) • z) - (d * h z (v - (c * h z v) • z)) • z = v := by
    intro c d hcd v
    rw [map_sub, map_smul, smul_eq_mul, sub_sub, ← add_smul]
    have h0 : c * h z v + d * (h z v - c * h z v * h z z) = 0 := by
      linear_combination (h z v) * hcd
    rw [h0, zero_smul, sub_zero]
  have hcd : (star b)⁻¹ + b⁻¹ = (star b)⁻¹ * b⁻¹ * h z z := by
    rw [hzz]
    field_simp
    try ring
  have h₁ : τl.comp σl = LinearMap.id := by
    apply LinearMap.ext
    intro v
    show τl (σl v) = v
    rw [hτ, hσ]
    exact key _ _ hcd v
  have h₂ : σl.comp τl = LinearMap.id := by
    apply LinearMap.ext
    intro v
    show σl (τl v) = v
    rw [hσ, hτ]
    exact key _ _ (by rw [add_comm, mul_comm b⁻¹]; exact hcd) v
  refine ⟨LinearEquiv.ofLinear τl σl h₁ h₂, ?_, ?_, ?_, ?_⟩
  · show ∀ u v, h (τl u) (τl v) = h u v
    intro u v
    rw [hτ, hτ]
    have hu : h u z = star (h z u) := (hsym z u).symm
    simp only [map_sub, map_smulₛₗ, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      smul_eq_mul, starRingEnd_apply, star_mul, star_inv₀, RingHom.id_apply, hu, hzz]
    field_simp
    try ring
  · show τl x = y
    rw [hτ, hzx, inv_mul_cancel₀ hb0, one_smul, hz, sub_sub_cancel]
  · intro v hxv hyv
    show τl v = v
    rw [hτ, hzv, hxv, hyv, sub_zero, mul_zero, zero_smul, sub_zero]
  · intro W hxW hyW v
    have hzW : z ∈ W := hz ▸ W.sub_mem hxW hyW
    show v ∈ W ↔ τl v ∈ W
    rw [hτ]
    constructor
    · intro hv
      exact W.sub_mem hv (W.smul_mem _ hzW)
    · intro hv
      have := W.add_mem hv (W.smul_mem (b⁻¹ * h z v) hzW)
      rwa [sub_add_cancel] at this

/- English proof (translation)
Take `⟨ψ, hψ, hψz, hψv⟩` from `exists_isom_scale hs hz hb`. Use `⟨ψ, hψ, hψz, hψv, ?_⟩` and prove the remaining obligations. Introduce `W hzW v`. Establish `hdec : h z (v - (h z v * (h z z)⁻¹) • z) = 0`. Rewrite using `[map_sub, map_smul, smul_eq_mul, inv_mul_cancel_right₀ hz, sub_self]`.

Establish `hψv' : ψ v = (h z v * (h z z)⁻¹) • (b • z) + (v - (h z v * (h z z)⁻¹) • z)`. Establish `e : v = (h z v * (h z z)⁻¹) • z + (v - (h z v * (h z z)⁻¹) • z)` using `by abel`. Use `conv_lhs => rw [e]`. Rewrite using `[map_add, map_smul, hψz, hψv _ hdec]`. Prove the components needed by the constructor for the conclusion.

Introduce `hv`. Rewrite using `[hψv']`. Conclude with `W.add_mem (W.smul_mem _ (W.smul_mem _ hzW)) (W.sub_mem hv (W.smul_mem _ hzW))`. Introduce `hv`. Rewrite `hv` using `[hψv']`.

Establish `h1` using `W.sub_mem hv (W.smul_mem (h z v * (h z z)⁻¹) (W.smul_mem b hzW))`. Rewrite `h1` using `[add_sub_cancel_left]`. Establish `h2` using `W.add_mem h1 (W.smul_mem (h z v * (h z z)⁻¹) hzW)`. Rewrite `h2` using `[sub_add_cancel]`. Then use the resulting hypothesis.
-/
theorem exists_isom_scale' (hs : h.IsSymm) {z : V} (hz : h z z ≠ 0) {b : K} (hb : star b * b = 1) :
    ∃ ψ ∈ Formalism.HermitianLatticesTheory.isom h, ψ z = b • z ∧ (∀ v, h z v = 0 → ψ v = v) ∧
      ∀ W : Submodule K V, z ∈ W → ∀ v, v ∈ W ↔ ψ v ∈ W := by
  obtain ⟨ψ, hψ, hψz, hψv⟩ := exists_isom_scale hs hz hb
  refine ⟨ψ, hψ, hψz, hψv, ?_⟩
  intro W hzW v
  have hdec : h z (v - (h z v * (h z z)⁻¹) • z) = 0 := by
    rw [map_sub, map_smul, smul_eq_mul, inv_mul_cancel_right₀ hz, sub_self]
  have hψv' : ψ v = (h z v * (h z z)⁻¹) • (b • z) + (v - (h z v * (h z z)⁻¹) • z) := by
    have e : v = (h z v * (h z z)⁻¹) • z + (v - (h z v * (h z z)⁻¹) • z) := by abel
    conv_lhs => rw [e]
    rw [map_add, map_smul, hψz, hψv _ hdec]
  constructor
  · intro hv
    rw [hψv']
    exact W.add_mem (W.smul_mem _ (W.smul_mem _ hzW)) (W.sub_mem hv (W.smul_mem _ hzW))
  · intro hv
    rw [hψv'] at hv
    have h1 := W.sub_mem hv (W.smul_mem (h z v * (h z z)⁻¹) (W.smul_mem b hzW))
    rw [add_sub_cancel_left] at h1
    have h2 := W.add_mem h1 (W.smul_mem (h z v * (h z z)⁻¹) hzW)
    rwa [sub_add_cancel] at h2

/- English proof (translation)
Distinguish the cases in `hb : h x x - h y x = 0`. Establish `hxy' : h x x = h (-y) (-y)`. Simplify using `only [map_neg, LinearMap.neg_apply, neg_neg]`. Conclude with `hxy`. Establish `hyx : h y x = h x x` using `by linear_combination -hb`.

Establish `hb' : h x x - h (-y) x ≠ 0`. Simplify using `only [map_neg, LinearMap.neg_apply, sub_neg_eq_add]`. Rewrite using `[hyx, ← two_mul]`. Conclude with `mul_ne_zero h2 hx0`. Take `⟨τ, hτ, hτx, hτv, hτW⟩` from `exists_isom_move' hs hxy' hb'`.

Establish `hy0 : h y y ≠ 0` using `hxy ▸ hx0`. Take `⟨ψ, hψ, hψy, hψv, hψW⟩` from `exists_isom_scale' hs hy0 (b := -1) (by rw [star_neg, star_one]; norm_num)`. Use `⟨ψ * τ, mul_mem hψ hτ, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `show ψ (τ x) = y`. Rewrite using `[hτx, map_neg, hψy, neg_one_smul, neg_neg]`.

Introduce `v hxv hyv show ψ (τ v) = v`. Establish `hyv' : h (-y) v = 0`. Simplify using `only [map_neg, LinearMap.neg_apply, hyv, neg_zero]`. Rewrite using `[hτv v hxv hyv', hψv v hyv]`. Introduce `W hxW hyW v show v ∈ W ↔ ψ (τ v) ∈ W`.

Rewrite using `[hτW W hxW (W.neg_mem hyW) v]`. Conclude with `hψW W hyW (τ v)`. Conclude with `exists_isom_move' hs hxy hb`.
-/
theorem exists_isom_map_of_eq_norm (hs : h.IsSymm) (h2 : (2 : K) ≠ 0) {x y : V} (hxy : h x x = h y y)
    (hx0 : h x x ≠ 0) :
    ∃ τ ∈ Formalism.HermitianLatticesTheory.isom h, τ x = y ∧ (∀ v, h x v = 0 → h y v = 0 → τ v = v) ∧
      ∀ W : Submodule K V, x ∈ W → y ∈ W → ∀ v, v ∈ W ↔ τ v ∈ W := by
  by_cases hb : h x x - h y x = 0
  · have hxy' : h x x = h (-y) (-y) := by
      simp only [map_neg, LinearMap.neg_apply, neg_neg]
      exact hxy
    have hyx : h y x = h x x := by linear_combination -hb
    have hb' : h x x - h (-y) x ≠ 0 := by
      simp only [map_neg, LinearMap.neg_apply, sub_neg_eq_add]
      rw [hyx, ← two_mul]
      exact mul_ne_zero h2 hx0
    obtain ⟨τ, hτ, hτx, hτv, hτW⟩ := exists_isom_move' hs hxy' hb'
    have hy0 : h y y ≠ 0 := hxy ▸ hx0
    obtain ⟨ψ, hψ, hψy, hψv, hψW⟩ := exists_isom_scale' hs hy0 (b := -1)
      (by rw [star_neg, star_one]; norm_num)
    refine ⟨ψ * τ, mul_mem hψ hτ, ?_, ?_, ?_⟩
    · show ψ (τ x) = y
      rw [hτx, map_neg, hψy, neg_one_smul, neg_neg]
    · intro v hxv hyv
      show ψ (τ v) = v
      have hyv' : h (-y) v = 0 := by
        simp only [map_neg, LinearMap.neg_apply, hyv, neg_zero]
      rw [hτv v hxv hyv', hψv v hyv]
    · intro W hxW hyW v
      show v ∈ W ↔ ψ (τ v) ∈ W
      rw [hτW W hxW (W.neg_mem hyW) v]
      exact hψW W hyW (τ v)
  · exact exists_isom_move' hs hxy hb

/- English proof (translation)
Establish `hφ' : ∀ a c, h (φ a) (φ c) = h a c` using `hφ`. Establish `hφx : φ x ∈ W₂` using `(hW x).1 hx`. Establish `hn : h (φ x) (φ x) = h X X` using `by rw [hφ' x x]; exact hxX`. Establish `hn0 : h (φ x) (φ x) ≠ 0` using `by rw [hφ' x x]; exact hx0`. Take `⟨τ, hτ, hτx, hτv, hτW⟩` from `exists_isom_map_of_eq_norm hs h2 hn hn0`.

Establish `hτ' : ∀ a c, h (τ a) (τ c) = h a c` using `hτ`. Use `⟨τ * φ, mul_mem hτ hφ, hτx, ?_, ?_⟩` and prove the remaining obligations. Introduce `v show v ∈ cutW h W₁ x ↔ τ (φ v) ∈ cutW h W₂ X`. Rewrite using `[mem_cutW, mem_cutW, ← hτW W₂ hφx hX (φ v), ← hW v, ← hτx, hτ' (φ x) (φ v), hφ' x v]`. Introduce `v hv show τ (φ v) = φ v`.

Apply `hτv` to reduce the goal to its premises. Rewrite using `[hφ' x v]`. Conclude with `hv x hx`. Take `⟨x', rfl⟩` from `φ.surjective X`. Rewrite using `[hφ' x' v]`.

Conclude with `hv x' ((hW x').2 hX)`.
-/
theorem exists_prep' (hs : h.IsSymm) (h2 : (2 : K) ≠ 0) {W₁ W₂ : Submodule K V}
    {φ : V ≃ₗ[K] V} (hφ : φ ∈ Formalism.HermitianLatticesTheory.isom h) (hW : ∀ v, v ∈ W₁ ↔ φ v ∈ W₂) {x X : V}
    (hx : x ∈ W₁) (hX : X ∈ W₂) (hxX : h x x = h X X) (hx0 : h x x ≠ 0) :
    ∃ φ' ∈ Formalism.HermitianLatticesTheory.isom h, φ' x = X ∧ (∀ v, v ∈ cutW h W₁ x ↔ φ' v ∈ cutW h W₂ X) ∧
      ∀ v, (∀ w ∈ W₁, h w v = 0) → φ' v = φ v := by
  have hφ' : ∀ a c, h (φ a) (φ c) = h a c := hφ
  have hφx : φ x ∈ W₂ := (hW x).1 hx
  have hn : h (φ x) (φ x) = h X X := by rw [hφ' x x]; exact hxX
  have hn0 : h (φ x) (φ x) ≠ 0 := by rw [hφ' x x]; exact hx0
  obtain ⟨τ, hτ, hτx, hτv, hτW⟩ := exists_isom_map_of_eq_norm hs h2 hn hn0
  have hτ' : ∀ a c, h (τ a) (τ c) = h a c := hτ
  refine ⟨τ * φ, mul_mem hτ hφ, hτx, ?_, ?_⟩
  · intro v
    show v ∈ cutW h W₁ x ↔ τ (φ v) ∈ cutW h W₂ X
    rw [mem_cutW, mem_cutW, ← hτW W₂ hφx hX (φ v), ← hW v, ← hτx, hτ' (φ x) (φ v), hφ' x v]
  · intro v hv
    show τ (φ v) = φ v
    apply hτv
    · rw [hφ' x v]
      exact hv x hx
    · obtain ⟨x', rfl⟩ := φ.surjective X
      rw [hφ' x' v]
      exact hv x' ((hW x').2 hX)

/- English proof (translation)
Establish `hsym : ∀ u v, star (h u v) = h v u` using `fun u v => by`. Rewrite using `[← starRingEnd_apply]`. Conclude with `hs.eq u v`. Proceed by induction on `n with`. Consider the case `zero`.

Introduce `W₁ W₂ M N φ hr hnd hM hN hφ hW`. Establish `hW0 : W₁ = ⊥` using `Submodule.finrank_eq_zero.1 (Nat.le_zero.1 hr)`. Use `⟨φ, hφ, fun v _ => rfl, fun v => ⟨fun hv => ?_, fun hv => ?_⟩⟩` and prove the remaining obligations. Establish `h0 : v = 0`. Use `hM.le v hv` as an intermediate fact.

Rewrite `this` using `[hW0, Submodule.mem_bot]`. Then use the resulting hypothesis. Rewrite using `[h0, map_zero]`. Conclude with `N.zero_mem`. Establish `h0 : v = 0`. Use `(hW v).2 (hN.le _ hv)` as an intermediate fact.

Rewrite `this` using `[hW0, Submodule.mem_bot]`. Then use the resulting hypothesis. Rewrite using `[h0]`. Conclude with `M.zero_mem`. Consider the case `succ n ih`. Introduce `W₁ W₂ M N φ hr hnd hM hN hφ hW`.

Distinguish the cases in `hW0 : W₁ = ⊥`. Use `⟨φ, hφ, fun v _ => rfl, fun v => ⟨fun hv => ?_, fun hv => ?_⟩⟩` and prove the remaining obligations. Establish `h0 : v = 0`. Use `hM.le v hv` as an intermediate fact. Rewrite `this` using `[hW0, Submodule.mem_bot]`. Then use the resulting hypothesis.

Rewrite using `[h0, map_zero]`. Conclude with `N.zero_mem`. Establish `h0 : v = 0`. Use `(hW v).2 (hN.le _ hv)` as an intermediate fact. Rewrite `this` using `[hW0, Submodule.mem_bot]`. Then use the resulting hypothesis.

Rewrite using `[h0]`. Conclude with `M.zero_mem`. Establish `hφ' : ∀ a c, h (φ a) (φ c) = h a c` using `hφ`. Take `⟨ξ, hξ, hξ0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hW0`. Take `⟨x, hxM, hxu⟩` from `IsSD.exists_unit_norm' hS hπ hs hnd hM hξ hξ0`.

Establish `hx : x ∈ W₁` using `hM.le x hxM`. Establish `hφx : φ x ∈ W₂` using `(hW x).1 hx`. Take `⟨X, hXN, hXx⟩` from `IsSD.exists_norm' hS hπ hs hN hφx hxu (hφ' x x)`. Establish `hx0 : h x x ≠ 0` using `hxu.1`. Establish `hXu : IsUnitIn S (h X X)`.

Rewrite using `[hXx]`. Conclude with `hxu`. Take `⟨φ₁, hφ₁, hφ₁x, hφ₁W, hφ₁v⟩` from `exists_prep' hs h2 hφ hW hx (hN.le X hXN) hXx.symm hx0`. Establish `hr' : finrank K (cutW h W₁ x) ≤ n`. Establish `hlt : finrank K (cutW h W₁ x) < finrank K W₁`.

Apply `Submodule.finrank_lt_finrank_of_lt` to reduce the goal to its premises. Rewrite using `[lt_iff_le_and_ne]`. Use `⟨fun v hv => (mem_cutW.1 hv).1, fun heq => ?_⟩` and prove the remaining obligations. Establish `hxc : x ∈ cutW h W₁ x`. Rewrite using `[heq]`.

Conclude with `hx`. Conclude with `hx0 (mem_cutW.1 hxc).2`. Use linear arithmetic over natural numbers and integers. Take `⟨g, hg, hgv, hgM⟩` from `ih (cutW h W₁ x) (cutW h W₂ X) (cutM h M x) (cutM h N X) φ₁ hr' (nondegOn_cut hnd hx hx0) (hM.cut hxM hxu) (hN.cut hXN hXu) hφ₁ hφ₁W`. Establish `hg' : ∀ a c, h (g a) (g c) = h a c` using `hg`.

Establish `horth : ∀ w ∈ cutW h W₁ x, h w x = 0` using `fun w hw => by`. Rewrite using `[← hsym x w, (mem_cutW.1 hw).2, star_zero]`. Establish `hgx : g x = X`. Rewrite using `[hgv x horth, hφ₁x]`. Establish `hdec : ∀ v : V, v = (v - (h x v * (h x x)⁻¹) • x) + (h x v * (h x x)⁻¹) • x` using `fun v => by abel`.

Establish `hgdec : ∀ v, g v = g (v - (h x v * (h x x)⁻¹) • x) + (h x v * (h x x)⁻¹) • X` using `fun v => by conv_lhs => rw [hdec v]`. Rewrite using `[map_add, map_smul, hgx]`. Use `⟨g, hg, fun v hv => ?_, fun v => ?_⟩` and prove the remaining obligations. Rewrite using `[hgv v (fun w hw => hv w (mem_cutW.1 hw).1), hφ₁v v hv]`. Establish `hxvX : h X (g v) = h x v`.

Rewrite using `[← hgx, hg']`. Establish `hxxinv : (h x x)⁻¹ ∈ S` using `hxu.2.2`. Prove the components needed by the constructor for the conclusion. Introduce `hv`. Establish `ha : h x v * (h x x)⁻¹ ∈ S` using `S.mul_mem (hM.int x hxM v hv) hxxinv`.

Establish `hp` using `proj_mem hM.toIsLatIn hxM hxu hv`. Establish `hgp` using `(hgM _).1 hp`. Rewrite using `[hgdec v]`. Conclude with `N.add_mem (AddSubgroup.mem_inf.1 hgp).1 (hN.smul_mem _ ha X hXN)`. Introduce `hv`.

Establish `hiS : h x v ∈ S`. Rewrite using `[← hxvX]`. Conclude with `hN.int X hXN (g v) hv`. Establish `ha : h x v * (h x x)⁻¹ ∈ S` using `S.mul_mem hiS hxxinv`. Establish `hq` using `proj_mem hN.toIsLatIn hXN hXu hv`.

Rewrite `hq` using `[hxvX, hXx]`. Establish `hq' : g (v - (h x v * (h x x)⁻¹) • x) ∈ cutM h N X`. Rewrite using `[map_sub, map_smul, hgx]`. Conclude with `hq`. Establish `hp` using `(hgM _).2 hq'`.

Rewrite using `[hdec v]`. Conclude with `M.add_mem (AddSubgroup.mem_inf.1 hp).1 (hM.smul_mem _ ha x hxM)`.
-/
theorem sd_main' [FiniteDimensional K V] (hS : IsHermSemilocal S) (hπ : IsUnif S π)
    (hs : h.IsSymm) (h2 : (2 : K) ≠ 0) (n : ℕ) :
    ∀ (W₁ W₂ : Submodule K V) (M N : AddSubgroup V) (φ : V ≃ₗ[K] V), finrank K W₁ ≤ n →
      NondegOn h W₁ → IsSD S h W₁ M → IsSD S h W₂ N → φ ∈ Formalism.HermitianLatticesTheory.isom h →
      (∀ v, v ∈ W₁ ↔ φ v ∈ W₂) →
      ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, (∀ v, (∀ w ∈ W₁, h w v = 0) → g v = φ v) ∧ ∀ v, v ∈ M ↔ g v ∈ N := by
  have hsym : ∀ u v, star (h u v) = h v u := fun u v => by
    rw [← starRingEnd_apply]
    exact hs.eq u v
  induction n with
  | zero =>
    intro W₁ W₂ M N φ hr hnd hM hN hφ hW
    have hW0 : W₁ = ⊥ := Submodule.finrank_eq_zero.1 (Nat.le_zero.1 hr)
    refine ⟨φ, hφ, fun v _ => rfl, fun v => ⟨fun hv => ?_, fun hv => ?_⟩⟩
    · have h0 : v = 0 := by
        have := hM.le v hv
        rwa [hW0, Submodule.mem_bot] at this
      rw [h0, map_zero]
      exact N.zero_mem
    · have h0 : v = 0 := by
        have := (hW v).2 (hN.le _ hv)
        rwa [hW0, Submodule.mem_bot] at this
      rw [h0]
      exact M.zero_mem
  | succ n ih =>
    intro W₁ W₂ M N φ hr hnd hM hN hφ hW
    by_cases hW0 : W₁ = ⊥
    · refine ⟨φ, hφ, fun v _ => rfl, fun v => ⟨fun hv => ?_, fun hv => ?_⟩⟩
      · have h0 : v = 0 := by
          have := hM.le v hv
          rwa [hW0, Submodule.mem_bot] at this
        rw [h0, map_zero]
        exact N.zero_mem
      · have h0 : v = 0 := by
          have := (hW v).2 (hN.le _ hv)
          rwa [hW0, Submodule.mem_bot] at this
        rw [h0]
        exact M.zero_mem
    have hφ' : ∀ a c, h (φ a) (φ c) = h a c := hφ
    obtain ⟨ξ, hξ, hξ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
    obtain ⟨x, hxM, hxu⟩ := IsSD.exists_unit_norm' hS hπ hs hnd hM hξ hξ0
    have hx : x ∈ W₁ := hM.le x hxM
    have hφx : φ x ∈ W₂ := (hW x).1 hx
    obtain ⟨X, hXN, hXx⟩ := IsSD.exists_norm' hS hπ hs hN hφx hxu (hφ' x x)
    have hx0 : h x x ≠ 0 := hxu.1
    have hXu : IsUnitIn S (h X X) := by
      rw [hXx]
      exact hxu
    obtain ⟨φ₁, hφ₁, hφ₁x, hφ₁W, hφ₁v⟩ := exists_prep' hs h2 hφ hW hx (hN.le X hXN) hXx.symm hx0
    have hr' : finrank K (cutW h W₁ x) ≤ n := by
      have hlt : finrank K (cutW h W₁ x) < finrank K W₁ := by
        apply Submodule.finrank_lt_finrank_of_lt
        rw [lt_iff_le_and_ne]
        refine ⟨fun v hv => (mem_cutW.1 hv).1, fun heq => ?_⟩
        have hxc : x ∈ cutW h W₁ x := by
          rw [heq]
          exact hx
        exact hx0 (mem_cutW.1 hxc).2
      omega
    obtain ⟨g, hg, hgv, hgM⟩ := ih (cutW h W₁ x) (cutW h W₂ X) (cutM h M x) (cutM h N X) φ₁ hr'
      (nondegOn_cut hnd hx hx0) (hM.cut hxM hxu) (hN.cut hXN hXu) hφ₁ hφ₁W
    have hg' : ∀ a c, h (g a) (g c) = h a c := hg
    have horth : ∀ w ∈ cutW h W₁ x, h w x = 0 := fun w hw => by
      rw [← hsym x w, (mem_cutW.1 hw).2, star_zero]
    have hgx : g x = X := by
      rw [hgv x horth, hφ₁x]
    have hdec : ∀ v : V, v = (v - (h x v * (h x x)⁻¹) • x) + (h x v * (h x x)⁻¹) • x :=
      fun v => by abel
    have hgdec : ∀ v, g v = g (v - (h x v * (h x x)⁻¹) • x) + (h x v * (h x x)⁻¹) • X := fun v => by
      conv_lhs => rw [hdec v]
      rw [map_add, map_smul, hgx]
    refine ⟨g, hg, fun v hv => ?_, fun v => ?_⟩
    · rw [hgv v (fun w hw => hv w (mem_cutW.1 hw).1), hφ₁v v hv]
    have hxvX : h X (g v) = h x v := by
      rw [← hgx, hg']
    have hxxinv : (h x x)⁻¹ ∈ S := hxu.2.2
    constructor
    · intro hv
      have ha : h x v * (h x x)⁻¹ ∈ S := S.mul_mem (hM.int x hxM v hv) hxxinv
      have hp := proj_mem hM.toIsLatIn hxM hxu hv
      have hgp := (hgM _).1 hp
      rw [hgdec v]
      exact N.add_mem (AddSubgroup.mem_inf.1 hgp).1 (hN.smul_mem _ ha X hXN)
    · intro hv
      have hiS : h x v ∈ S := by
        rw [← hxvX]
        exact hN.int X hXN (g v) hv
      have ha : h x v * (h x x)⁻¹ ∈ S := S.mul_mem hiS hxxinv
      have hq := proj_mem hN.toIsLatIn hXN hXu hv
      rw [hxvX, hXx] at hq
      have hq' : g (v - (h x v * (h x x)⁻¹) • x) ∈ cutM h N X := by
        rw [map_sub, map_smul, hgx]
        exact hq
      have hp := (hgM _).2 hq'
      rw [hdec v]
      exact M.add_mem (AddSubgroup.mem_inf.1 hp).1 (hM.smul_mem _ ha x hxM)

end Formalism.L2.SG.Pf.G4
