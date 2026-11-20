import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsEquivOfMemEndL

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.D2

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

/- English proof (translation)
Establish `key : ∀ x : V, h x x = 0 → x = 0`. Introduce `x hx`. Assume the negation of the conclusion as `hne`. Take `⟨φ⟩ : Nonempty (K →+* ℂ)` from `inferInstance`. Establish `h1` using `hd x hne φ`.

Rewrite `h1` using `[hx, map_zero, Complex.zero_re]`. Conclude with `lt_irrefl _ h1`. Conclude with `⟨fun x hx => key x (hx x), fun y hy => key y (hy y)⟩`.
-/
theorem nondegenerate {h : V →ₗ⋆[K] V →ₗ[K] K} (hd : IsTotPosDef h) : h.Nondegenerate := by
  have key : ∀ x : V, h x x = 0 → x = 0 := by
    intro x hx
    by_contra hne
    obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
    have h1 := hd x hne φ
    rw [hx, map_zero, Complex.zero_re] at h1
    exact lt_irrefl _ h1
  exact ⟨fun x hx => key x (hx x), fun y hy => key y (hy y)⟩

/- English proof (translation)
Take `⟨π, hπ, hπ'⟩` from `exists_unif h𝔭`. Take `⟨b, hb, -⟩` from `LocalSpans.exists_basis_locF hA₀ h𝔭`. Establish `hnd` using `nondegenerate hd`. Take `⟨bs, hbs⟩` from `Formalism.HermitianLatticesTheory.dualLattice_dualBasis h hnd b`. Use `choose n hn using fun j => exists_pow_smul_mem hA₀ h𝔭 hπ (bs j)`.

Use `⟨∑ j, n j, fun k x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[Formalism.HermitianLatticesTheory.dualLattice_expand h hnd b bs hbs x]`. Use `Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Take `⟨c, hc, e⟩` from `(mem_pK_iff_unif h𝔭 hπ hπ').1 (hx (b j) (LocF.le_locF 𝔭 A₀ (hb j)))`. Rewrite using `[e]`.

Establish `hle : n j ≤ ∑ j, n j` using `Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)`. Use `(mem_smul_iff_unif h𝔭 hπ hπ' A₀).2 ⟨(c * algebraMap F K (π : F) ^ (∑ j, n j - n j)) • (algebraMap F K (π : F) ^ n j • bs j), smul_mem_locF h𝔭 A₀ (by simpa using mul_mem_pK h𝔭 hc (unif_pow_mem_pK_zero hπ _)) (hn j), ?_⟩` and prove the remaining obligations. Rewrite using `[smul_smul, smul_smul]`. Use `congr 1`. Establish `: k + ∑ j, n j = k + (∑ j, n j - n j) + n j` using `by omega`.

Rewrite using `[this, pow_add, pow_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_dual_bound (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsLattice K A₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ e : ℕ, ∀ (k : ℕ) (x : V), (∀ y ∈ locF 𝔭 A₀, h y x ∈ pK K 𝔭 (k + e)) →
      x ∈ extP K 𝔭 ^ k • locF 𝔭 A₀ := by
  classical
  obtain ⟨π, hπ, hπ'⟩ := exists_unif h𝔭
  obtain ⟨b, hb, -⟩ := LocalSpans.exists_basis_locF hA₀ h𝔭
  have hnd := nondegenerate hd
  obtain ⟨bs, hbs⟩ := Formalism.HermitianLatticesTheory.dualLattice_dualBasis h hnd b
  choose n hn using fun j => exists_pow_smul_mem hA₀ h𝔭 hπ (bs j)
  refine ⟨∑ j, n j, fun k x hx => ?_⟩
  rw [Formalism.HermitianLatticesTheory.dualLattice_expand h hnd b bs hbs x]
  refine Submodule.sum_mem _ fun j _ => ?_
  obtain ⟨c, hc, e⟩ := (mem_pK_iff_unif h𝔭 hπ hπ').1 (hx (b j) (LocF.le_locF 𝔭 A₀ (hb j)))
  rw [e]
  have hle : n j ≤ ∑ j, n j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  refine (mem_smul_iff_unif h𝔭 hπ hπ' A₀).2
    ⟨(c * algebraMap F K (π : F) ^ (∑ j, n j - n j)) • (algebraMap F K (π : F) ^ n j • bs j),
      smul_mem_locF h𝔭 A₀ (by simpa using mul_mem_pK h𝔭 hc (unif_pow_mem_pK_zero hπ _)) (hn j), ?_⟩
  rw [smul_smul, smul_smul]
  congr 1
  have : k + ∑ j, n j = k + (∑ j, n j - n j) + n j := by omega
  rw [this, pow_add, pow_add]; ring

/- English proof (translation)
Take `⟨r1, h1⟩` from `exists_smul_le hA₀ hB₀ h𝔭`. Take `⟨r2, h2⟩` from `exists_smul_le hB₀ hA₀ h𝔭`. Take `⟨π, hπ, hπ'⟩` from `exists_unif h𝔭`. Establish `hπ0` using `unif_ne_zero (K := K) hπ'`. Use `⟨r1 + r2, fun d D hD y hy => ?_⟩` and prove the remaining obligations.

Establish `hy'` using `h2 ((mem_smul_iff_unif h𝔭 hπ hπ' B₀).2 ⟨y, hy, rfl⟩)`. Take `⟨z, hz, e⟩` from `(mem_smul_iff_unif h𝔭 hπ hπ' A₀).1 (hD _ hy')`. Establish `hz'` using `h1 ((mem_smul_iff_unif h𝔭 hπ hπ' A₀).2 ⟨z, hz, rfl⟩)`. Use `(mem_smul_iff_unif h𝔭 hπ hπ' B₀).2 ⟨_, hz', ?_⟩` and prove the remaining obligations. Apply `smul_right_injective V (pow_ne_zero r2 hπ0)` to reduce the goal to its premises.

Use `show algebraMap F K (π : F) ^ r2 • D y = algebraMap F K (π : F) ^ r2 • _`. Rewrite using `[← map_smul, e, smul_smul, smul_smul]`. Use `congr 1`. Rewrite using `[pow_add, pow_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_endL_le {A₀ B₀ : Submodule (𝓞 K) V} (hA₀ : Submodule.IsLattice K A₀)
    (hB₀ : Submodule.IsLattice K B₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ r : ℕ, ∀ d : ℕ, endL (locF 𝔭 A₀) (extP K 𝔭 ^ (d + r) • locF 𝔭 A₀) ≤
      endL (locF 𝔭 B₀) (extP K 𝔭 ^ d • locF 𝔭 B₀) := by
  obtain ⟨r1, h1⟩ := exists_smul_le hA₀ hB₀ h𝔭
  obtain ⟨r2, h2⟩ := exists_smul_le hB₀ hA₀ h𝔭
  obtain ⟨π, hπ, hπ'⟩ := exists_unif h𝔭
  have hπ0 := unif_ne_zero (K := K) hπ'
  refine ⟨r1 + r2, fun d D hD y hy => ?_⟩
  have hy' := h2 ((mem_smul_iff_unif h𝔭 hπ hπ' B₀).2 ⟨y, hy, rfl⟩)
  obtain ⟨z, hz, e⟩ := (mem_smul_iff_unif h𝔭 hπ hπ' A₀).1 (hD _ hy')
  have hz' := h1 ((mem_smul_iff_unif h𝔭 hπ hπ' A₀).2 ⟨z, hz, rfl⟩)
  refine (mem_smul_iff_unif h𝔭 hπ hπ' B₀).2 ⟨_, hz', ?_⟩
  apply smul_right_injective V (pow_ne_zero r2 hπ0)
  show algebraMap F K (π : F) ^ r2 • D y = algebraMap F K (π : F) ^ r2 • _
  rw [← map_smul, e, smul_smul, smul_smul]
  congr 1
  rw [pow_add, pow_add]; ring

/- English proof (translation)
Take `⟨r2, h2⟩` from `exists_smul_le hB₀ hA₀ h𝔭`. Take `⟨π, hπ, hπ'⟩` from `exists_unif h𝔭`. Establish `hπ0` using `unif_ne_zero (K := K) hπ'`. Use `⟨r2 + r2, fun d s hs x hx y hy => ?_⟩` and prove the remaining obligations. Establish `hx'` using `h2 ((mem_smul_iff_unif h𝔭 hπ hπ' B₀).2 ⟨x, hx, rfl⟩)`.

Establish `hy'` using `h2 ((mem_smul_iff_unif h𝔭 hπ hπ' B₀).2 ⟨y, hy, rfl⟩)`. Take `⟨c, hc, e⟩` from `(mem_pK_iff_unif h𝔭 hπ hπ').1 (hs _ hx' _ hy')`. Use `(mem_pK_iff_unif h𝔭 hπ hπ').2 ⟨c, hc, ?_⟩` and prove the remaining obligations. Rewrite `e` using `[map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, starRingEnd_apply, star_pow, MeanB.star_algebraMap hF]`. Apply `mul_left_cancel₀ (pow_ne_zero (r2 + r2) hπ0)` to reduce the goal to its premises.

Rewrite `*` using `[pow_add, pow_add]`. Take the linear combination `e`.
-/
theorem exists_sesqL_le (hF : IsFixF K F) {A₀ B₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsLattice K A₀) (hB₀ : Submodule.IsLattice K B₀) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) :
    ∃ r : ℕ, ∀ d : ℕ, sesqL (locF 𝔭 A₀) 𝔭 (d + r) ≤ sesqL (locF 𝔭 B₀) 𝔭 d := by
  obtain ⟨r2, h2⟩ := exists_smul_le hB₀ hA₀ h𝔭
  obtain ⟨π, hπ, hπ'⟩ := exists_unif h𝔭
  have hπ0 := unif_ne_zero (K := K) hπ'
  refine ⟨r2 + r2, fun d s hs x hx y hy => ?_⟩
  have hx' := h2 ((mem_smul_iff_unif h𝔭 hπ hπ' B₀).2 ⟨x, hx, rfl⟩)
  have hy' := h2 ((mem_smul_iff_unif h𝔭 hπ hπ' B₀).2 ⟨y, hy, rfl⟩)
  obtain ⟨c, hc, e⟩ := (mem_pK_iff_unif h𝔭 hπ hπ').1 (hs _ hx' _ hy')
  refine (mem_pK_iff_unif h𝔭 hπ hπ').2 ⟨c, hc, ?_⟩
  rw [map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, starRingEnd_apply,
    star_pow, MeanB.star_algebraMap hF] at e
  apply mul_left_cancel₀ (pow_ne_zero (r2 + r2) hπ0)
  rw [pow_add, pow_add] at *
  linear_combination e

/- English proof (translation)
Introduce and unpack `X ⟨hX, hX'⟩`. Use `⟨hX, fun x hx y hy => ?_⟩` and prove the remaining obligations. Establish `hx0 : x ∈ extP K 𝔭 ^ 0 • locF 𝔭 A₀` using `by rwa [pow_zero_smul]`. Establish `hy0 : y ∈ extP K 𝔭 ^ 0 • locF 𝔭 A₀` using `by rwa [pow_zero_smul]`. Establish `e : h (X x) (X y) - h x y = h (X x - x) y + h x (X y - y) + h (X x - x) (X y - y)`.

Simplify using `only [map_sub, LinearMap.sub_apply]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Use `add_mem (add_mem ?_ ?_) ?_` and prove the remaining obligations. Simplify using `using form_mem_pK hF hA₀i h𝔭 (hX' x hx) hy0`.

Simplify using `using form_mem_pK hF hA₀i h𝔭 hx0 (hX' y hy)`. Conclude with `pK_anti 𝔭 (Nat.le_add_right k k) (form_mem_pK hF hA₀i h𝔭 (hX' x hx) (hX' y hy))`.
-/
theorem nSub_le_sSub (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} {A₀ : Submodule (𝓞 K) V}
    (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) :
    nSub (locF 𝔭 A₀) 𝔭 k ≤ sSub h (locF 𝔭 A₀) 𝔭 k := by
  rintro X ⟨hX, hX'⟩
  refine ⟨hX, fun x hx y hy => ?_⟩
  have hx0 : x ∈ extP K 𝔭 ^ 0 • locF 𝔭 A₀ := by rwa [pow_zero_smul]
  have hy0 : y ∈ extP K 𝔭 ^ 0 • locF 𝔭 A₀ := by rwa [pow_zero_smul]
  have e : h (X x) (X y) - h x y = h (X x - x) y + h x (X y - y) + h (X x - x) (X y - y) := by
    simp only [map_sub, LinearMap.sub_apply]; ring
  rw [e]
  refine add_mem (add_mem ?_ ?_) ?_
  · simpa using form_mem_pK hF hA₀i h𝔭 (hX' x hx) hy0
  · simpa using form_mem_pK hF hA₀i h𝔭 hx0 (hX' y hy)
  · exact pK_anti 𝔭 (Nat.le_add_right k k) (form_mem_pK hF hA₀i h𝔭 (hX' x hx) (hX' y hy))

/- English proof (translation)
Take `⟨r, hr⟩` from `exists_endL_le hA₀ hB₀ h𝔭`. Use `⟨1 + r, fun k hk X hX => mem_glSub_of_sub_mem hB₀ h𝔭 fun y hy => ?_⟩` and prove the remaining obligations. Establish `h1 : ((X : V →ₗ[K] V) - LinearMap.id) ∈ endL (locF 𝔭 A₀) (extP K 𝔭 ^ (1 + r) • locF 𝔭 A₀)` using `fun x hx => smul_anti 𝔭 _ hk (hX.2 x hx)`. Use `hr 1 h1 y hy` as an intermediate fact. Rewrite `this` using `[pow_one]`. Then use the resulting hypothesis.
-/
theorem nSub_le_glSub {A₀ B₀ : Submodule (𝓞 K) V} (hA₀ : Submodule.IsLattice K A₀)
    (hB₀ : Submodule.IsLattice K B₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ k₀ : ℕ, ∀ k ≥ k₀, nSub (locF 𝔭 A₀) 𝔭 k ≤ glSub (locF 𝔭 B₀) := by
  obtain ⟨r, hr⟩ := exists_endL_le hA₀ hB₀ h𝔭
  refine ⟨1 + r, fun k hk X hX => mem_glSub_of_sub_mem hB₀ h𝔭 fun y hy => ?_⟩
  have h1 : ((X : V →ₗ[K] V) - LinearMap.id) ∈ endL (locF 𝔭 A₀) (extP K 𝔭 ^ (1 + r) • locF 𝔭 A₀) :=
    fun x hx => smul_anti 𝔭 _ hk (hX.2 x hx)
  have := hr 1 h1 y hy
  rwa [pow_one] at this

end Formalism.HermitianLattices.Ext.L3.D2
