import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.LocWitt

section Abstract

variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]

def Rel (h : V →ₗ⋆[K] V →ₗ[K] K) (Λ : AddSubgroup V) (x y : V) : Prop :=
  ∃ g ∈ isom h, (∀ v, g v ∈ Λ ↔ v ∈ Λ) ∧ g x = y

/- English proof (translation)
Take `⟨g, hg, g1, g2⟩` from `a`. Take `⟨k, hk, k1, k2⟩` from `b`. Use `⟨k * g, (isom h).mul_mem hk hg, fun v => (k1 _).trans (g1 v), ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `k (g x) = z`. Rewrite using `[g2, k2]`.
-/
theorem Rel.trans {h : V →ₗ⋆[K] V →ₗ[K] K} {Λ : AddSubgroup V} {x y z : V}
    (a : Rel h Λ x y) (b : Rel h Λ y z) : Rel h Λ x z := by
  obtain ⟨g, hg, g1, g2⟩ := a
  obtain ⟨k, hk, k1, k2⟩ := b
  refine ⟨k * g, (isom h).mul_mem hk hg, fun v => (k1 _).trans (g1 v), ?_⟩
  change k (g x) = z
  rw [g2, k2]

/- English proof (translation)
The claim follows from `hs.eq x y`.
-/
theorem symm' {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (x y : V) : star (h x y) = h y x :=
  hs.eq x y

/- English proof (translation)
Establish `hc1 : star c ≠ 0` using `star_ne_zero.2 hc0`. Set `s : K → V →ₗ[K] V` to `fun b => LinearMap.id - (b • h u).smulRight u`. Establish `hsv : ∀ b v, s b v = v - (b * h u v) • u` using `fun b v => by simp [s]`. Establish `inv : ∀ b b' : K, b + b' = b * b' * h u u → ∀ v, s b (s b' v) = v`. Introduce `b b' eb v`.

Rewrite using `[hsv, hsv, sub_sub, ← add_smul]`. Establish `: b' * h u v + b * h u (v - (b' * h u v) • u) = 0`. Simplify using `only [map_sub, map_smul, smul_eq_mul]`. Take the linear combination `(h u v) * eb`. Rewrite using `[this]`.

Simplify using the standard rewrite rules. Establish `e1 : c⁻¹ + (star c)⁻¹ = c⁻¹ * (star c)⁻¹ * h u u`. Rewrite using `[← e]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Establish `e2 : (star c)⁻¹ + c⁻¹ = (star c)⁻¹ * c⁻¹ * h u u`. Rewrite using `[← e]`. Clear the denominators using the available nonvanishing facts. Establish `mem : ∀ b ∈ A, ∀ v ∈ Λ, s b v ∈ Λ` using `fun b hb v hv => by`. Rewrite using `[hsv]`.

Conclude with `Λ.sub_mem hv (hΛ _ (A.mul_mem hb (hi _ hu _ hv)) _ hu)`. Establish `hc' : (star c)⁻¹ ∈ A` using `by rw [← star_inv₀]; exact hA _ hc`. Set `g : V ≃ₗ[K] V` to `LinearEquiv.ofLinear (s c⁻¹) (s (star c)⁻¹) (LinearMap.ext (inv _ _ e1)) (LinearMap.ext (inv _ _ e2))`. Establish `hg : ∀ v, g v = s c⁻¹ v` using `fun v => rfl`. Use `⟨g, ?_, fun v => ⟨fun hv => ?_, fun hv => mem _ hc v hv⟩, fun v => by rw [hg, hsv]⟩` and prove the remaining obligations.

Introduce `v w`. Rewrite using `[hg, hg, hsv, hsv]`. Simplify using `only [map_sub, map_smul, LinearMap.map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_mul', star_inv₀, symm' hs, RingHom.id_apply]`. Take the linear combination `(-(h v u) * (h u w)) * e1`. Use `mem _ hc' _ hv` as an intermediate fact.

Rewrite `this` using `[hg, inv _ _ e2]`. Then use the resulting hypothesis.
-/
theorem refl {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {Λ : AddSubgroup V} {A : Subring K}
    (hA : ∀ a ∈ A, star a ∈ A) (hΛ : ∀ a ∈ A, ∀ v ∈ Λ, a • v ∈ Λ) (hi : ∀ v ∈ Λ, ∀ w ∈ Λ, h v w ∈ A)
    {u : V} (hu : u ∈ Λ) {c : K} (hc0 : c ≠ 0) (hc : c⁻¹ ∈ A) (e : c + star c = h u u) :
    ∃ g ∈ isom h, (∀ v, g v ∈ Λ ↔ v ∈ Λ) ∧ ∀ v, g v = v - (c⁻¹ * h u v) • u := by
  have hc1 : star c ≠ 0 := star_ne_zero.2 hc0
  let s : K → V →ₗ[K] V := fun b => LinearMap.id - (b • h u).smulRight u
  have hsv : ∀ b v, s b v = v - (b * h u v) • u := fun b v => by simp [s]
  have inv : ∀ b b' : K, b + b' = b * b' * h u u → ∀ v, s b (s b' v) = v := by
    intro b b' eb v
    rw [hsv, hsv, sub_sub, ← add_smul]
    have : b' * h u v + b * h u (v - (b' * h u v) • u) = 0 := by
      simp only [map_sub, map_smul, smul_eq_mul]
      linear_combination (h u v) * eb
    rw [this]; simp
  have e1 : c⁻¹ + (star c)⁻¹ = c⁻¹ * (star c)⁻¹ * h u u := by
    rw [← e]; field_simp; ring
  have e2 : (star c)⁻¹ + c⁻¹ = (star c)⁻¹ * c⁻¹ * h u u := by
    rw [← e]; field_simp
  have mem : ∀ b ∈ A, ∀ v ∈ Λ, s b v ∈ Λ := fun b hb v hv => by
    rw [hsv]
    exact Λ.sub_mem hv (hΛ _ (A.mul_mem hb (hi _ hu _ hv)) _ hu)
  have hc' : (star c)⁻¹ ∈ A := by rw [← star_inv₀]; exact hA _ hc
  let g : V ≃ₗ[K] V := LinearEquiv.ofLinear (s c⁻¹) (s (star c)⁻¹)
    (LinearMap.ext (inv _ _ e1)) (LinearMap.ext (inv _ _ e2))
  have hg : ∀ v, g v = s c⁻¹ v := fun v => rfl
  refine ⟨g, ?_, fun v => ⟨fun hv => ?_, fun hv => mem _ hc v hv⟩, fun v => by rw [hg, hsv]⟩
  · intro v w
    rw [hg, hg, hsv, hsv]
    simp only [map_sub, map_smul, LinearMap.map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply,
      smul_eq_mul, starRingEnd_apply, star_mul', star_inv₀, symm' hs, RingHom.id_apply]
    linear_combination (-(h v u) * (h u w)) * e1
  · have := mem _ hc' _ hv
    rwa [hg, inv _ _ e2] at this

/- English proof (translation)
Establish `ne0 : ∀ {a : K}, a ∉ M → a ≠ 0` using `fun ha e => ha (e ▸ M.zero_mem)`. Establish `umul : ∀ {a b : K}, a ∈ A → a ∉ M → b ∉ M → a * b ∉ M`. Introduce `a b ha ha' hb hab`. Use `hM _ (hinv a ha ha') _ hab` as an intermediate fact. Rewrite `this` using `[← mul_assoc, inv_mul_cancel₀ (ne0 ha'), one_mul]`.

Conclude with `hb this`. Establish `uinv : ∀ {a : K}, a ∈ A → a ∉ M → a⁻¹ ∉ M`. Introduce `a ha ha' hb`. Use `hM _ ha _ hb` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel₀ (ne0 ha')]`.

Conclude with `h1 this`. Establish `ustar : ∀ {a : K}, a ∈ A → a ∉ M → star a ∉ M`. Introduce `a ha ha' hb`. Use `hM _ (hA _ (hinv a ha ha')) _ hb` as an intermediate fact. Rewrite `this` using `[← star_mul', inv_mul_cancel₀ (ne0 ha'), star_one]`.

Conclude with `h1 this`. Establish `uadd : ∀ {a m : K}, a ∉ M → m ∈ M → a + m ∉ M`. Introduce `a m ha hm e`. Conclude with `ha (by simpa using M.sub_mem e hm)`. Establish `step : ∀ x ∈ Λ, ∀ y ∈ Λ, h x x = h y y → h x x - h y x ∉ M → Rel h Λ x y`.

Introduce `x hx y hy hn hc`. Establish `hcA : h x x - h y x ∈ A` using `A.sub_mem (hi _ hx _ hx) (hi _ hy _ hx)`. Take `⟨g, g1, g2, g3⟩` from `refl hs hA hΛ hi (Λ.sub_mem hx hy) (ne0 hc) (hinv _ hcA hc) (by`. Simplify using `only [map_sub, LinearMap.sub_apply, star_sub, symm' hs]`. Take the linear combination `hn)`.

Use `⟨g, g1, g2, ?_⟩` and prove the remaining obligations. Rewrite using `[g3, map_sub, LinearMap.sub_apply, inv_mul_cancel₀ (ne0 hc)]`. Simplify using the standard rewrite rules. Distinguish the cases in `hc : h x x - h y x ∈ M`. Use `swap`.

Conclude with `step x hx y hy hn hc`. Establish `hsθ` using `hA _ hθ`. Establish `hδA : θ - star θ ∈ A` using `A.sub_mem hθ hsθ`. Distinguish the cases in `hnM : h x x ∈ M`. Choose the witnesses or unpack the hypotheses as in `⟨w, hw, w1, w2⟩ : ∃ w ∈ Λ, h w x ∉ M ∧ h w y ∉ M := by`.

Take `⟨w, hw, e⟩` from `px`. Take `⟨w', hw', e'⟩` from `py`. Distinguish the cases in `a : h w y ∈ M`. Distinguish the cases in `b : h w' x ∈ M`. Use `⟨w + w', Λ.add_mem hw hw', ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_add, LinearMap.add_apply, e]`. Conclude with `uadd h1 b`. Rewrite using `[map_add, LinearMap.add_apply, e', add_comm]`. Conclude with `uadd h1 a`. Conclude with `⟨w', hw', b, e' ▸ h1⟩`.

Conclude with `⟨w, hw, e ▸ h1, a⟩`. Choose the witnesses or unpack the hypotheses as in `⟨c, cA, cM, ce⟩ : ∃ c ∈ A, c ∉ M ∧ c + star c = h w w := by`. Establish `h0` using `ne0 hδ`. Establish `h0' : star θ - θ ≠ 0` using `fun e => h0 (by linear_combination -e)`. Establish `tA : θ * (θ - star θ)⁻¹ * h w w ∈ A` using `A.mul_mem (A.mul_mem hθ (hinv _ hδA hδ)) (hi _ hw _ hw)`.

Establish `te : θ * (θ - star θ)⁻¹ * h w w + star (θ * (θ - star θ)⁻¹ * h w w) = h w w`. Simplify using `only [star_mul', star_inv₀, star_sub, star_star, symm' hs]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Distinguish the cases in `a : θ * (θ - star θ)⁻¹ * h w w ∈ M`.

Use `⟨(θ - star θ) + θ * (θ - star θ)⁻¹ * h w w, A.add_mem hδA tA, uadd hδ a, ?_⟩` and prove the remaining obligations. Rewrite using `[star_add, star_sub, star_star]`. Take the linear combination `te`. Conclude with `⟨_, tA, a, te⟩`. Take `⟨g, g1, g2, g3⟩` from `refl hs hA hΛ hi hw (ne0 cM) (hinv _ cA cM) ce`.

Establish `hgx : h (g x) (g x) = h x x` using `g1 x x`. Use `Rel.trans ⟨g, g1, g2, rfl⟩ (step _ ((g2 x).2 hx) y hy (hgx.trans hn) ?_)` and prove the remaining obligations. Establish `: h (g x) (g x) - h y (g x) = (c⁻¹ * (h w x * star (h w y))) + (h x x - h y x)`. Rewrite using `[hgx, g3, symm' hs]`. Simplify using `only [map_sub, map_smul, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `uadd (umul (hinv _ cA cM) (uinv cA cM) (umul (hi _ hw _ hx) w1 (ustar (hi _ hw _ hy) w2))) hc`. Establish `θM : θ ∉ M` using `fun a => by`. Distinguish the cases in `b : star θ ∈ M`.

Conclude with `hδ (M.sub_mem a b)`. Conclude with `ustar hsθ b (by rwa [star_star])`. Establish `sM` using `ustar hθ θM`. Establish `t0` using `ne0 θM`. Establish `s0` using `ne0 sM`.

Establish `hxx` using `hi _ hx _ hx`. Establish `μA : star θ * θ⁻¹ ∈ A` using `A.mul_mem hsθ (hinv _ hθ θM)`. Establish `hz` using `hΛ _ μA y hy`. Establish `e1 : ∀ v, h ((star θ * θ⁻¹) • y) v = θ * (star θ)⁻¹ * h y v` using `fun v => by`. Simplify using `[LinearMap.map_smulₛₗ, starRingEnd_apply, star_mul', star_inv₀]`.

Establish `e2 : h ((star θ * θ⁻¹) • y) ((star θ * θ⁻¹) • y) = h y y`. Rewrite using `[e1, map_smul, smul_eq_mul]`. Clear the denominators using the available nonvanishing facts. Use `Rel.trans (step x hx _ hz (hn.trans e2.symm) ?_) (step _ hz y hy e2 ?_)` and prove the remaining obligations. Establish `: h x x - h ((star θ * θ⁻¹) • y) x = -((θ - star θ) * ((star θ)⁻¹ * h x x)) + θ * (star θ)⁻¹ * (h x x - h y x)`.

Rewrite using `[e1]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Use `uadd ?_ (hM _ (A.mul_mem hθ (hinv _ hsθ sM)) _ hc)` and prove the remaining obligations.

Rewrite using `[neg_mem_iff]`. Conclude with `umul hδA hδ (umul (hinv _ hsθ sM) (uinv hsθ sM) hnM)`. Establish `: h ((star θ * θ⁻¹) • y) ((star θ * θ⁻¹) • y) - h y ((star θ * θ⁻¹) • y) = (θ - star θ) * (θ⁻¹ * h x x)`. Rewrite using `[e2, map_smul, smul_eq_mul, hn]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[this]`. Conclude with `umul hδA hδ (umul (hinv _ hθ θM) (uinv hθ θM) hnM)`.
-/
theorem abs_main {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {Λ : AddSubgroup V} {A : Subring K}
    {M : AddSubgroup K}
    (hA : ∀ a ∈ A, star a ∈ A) (hΛ : ∀ a ∈ A, ∀ v ∈ Λ, a • v ∈ Λ) (hi : ∀ v ∈ Λ, ∀ w ∈ Λ, h v w ∈ A)
    (hM : ∀ a ∈ A, ∀ m ∈ M, a * m ∈ M) (h1 : (1 : K) ∉ M) (hinv : ∀ a ∈ A, a ∉ M → a⁻¹ ∈ A)
    {θ : K} (hθ : θ ∈ A) (hδ : θ - star θ ∉ M)
    {x y : V} (hx : x ∈ Λ) (hy : y ∈ Λ) (hn : h x x = h y y)
    (px : ∃ w ∈ Λ, h w x = 1) (py : ∃ w ∈ Λ, h w y = 1) : Rel h Λ x y := by
  have ne0 : ∀ {a : K}, a ∉ M → a ≠ 0 := fun ha e => ha (e ▸ M.zero_mem)
  have umul : ∀ {a b : K}, a ∈ A → a ∉ M → b ∉ M → a * b ∉ M := by
    intro a b ha ha' hb hab
    have := hM _ (hinv a ha ha') _ hab
    rw [← mul_assoc, inv_mul_cancel₀ (ne0 ha'), one_mul] at this
    exact hb this
  have uinv : ∀ {a : K}, a ∈ A → a ∉ M → a⁻¹ ∉ M := by
    intro a ha ha' hb
    have := hM _ ha _ hb
    rw [mul_inv_cancel₀ (ne0 ha')] at this
    exact h1 this
  have ustar : ∀ {a : K}, a ∈ A → a ∉ M → star a ∉ M := by
    intro a ha ha' hb
    have := hM _ (hA _ (hinv a ha ha')) _ hb
    rw [← star_mul', inv_mul_cancel₀ (ne0 ha'), star_one] at this
    exact h1 this
  have uadd : ∀ {a m : K}, a ∉ M → m ∈ M → a + m ∉ M := by
    intro a m ha hm e
    exact ha (by simpa using M.sub_mem e hm)
  have step : ∀ x ∈ Λ, ∀ y ∈ Λ, h x x = h y y → h x x - h y x ∉ M → Rel h Λ x y := by
    intro x hx y hy hn hc
    have hcA : h x x - h y x ∈ A := A.sub_mem (hi _ hx _ hx) (hi _ hy _ hx)
    obtain ⟨g, g1, g2, g3⟩ := refl hs hA hΛ hi (Λ.sub_mem hx hy) (ne0 hc) (hinv _ hcA hc) (by
      simp only [map_sub, LinearMap.sub_apply, star_sub, symm' hs]
      linear_combination hn)
    refine ⟨g, g1, g2, ?_⟩
    rw [g3, map_sub, LinearMap.sub_apply, inv_mul_cancel₀ (ne0 hc)]
    simp
  by_cases hc : h x x - h y x ∈ M
  swap
  · exact step x hx y hy hn hc
  have hsθ := hA _ hθ
  have hδA : θ - star θ ∈ A := A.sub_mem hθ hsθ
  by_cases hnM : h x x ∈ M
  · obtain ⟨w, hw, w1, w2⟩ : ∃ w ∈ Λ, h w x ∉ M ∧ h w y ∉ M := by
      obtain ⟨w, hw, e⟩ := px
      obtain ⟨w', hw', e'⟩ := py
      by_cases a : h w y ∈ M
      · by_cases b : h w' x ∈ M
        · refine ⟨w + w', Λ.add_mem hw hw', ?_, ?_⟩
          · rw [map_add, LinearMap.add_apply, e]; exact uadd h1 b
          · rw [map_add, LinearMap.add_apply, e', add_comm]; exact uadd h1 a
        · exact ⟨w', hw', b, e' ▸ h1⟩
      · exact ⟨w, hw, e ▸ h1, a⟩
    obtain ⟨c, cA, cM, ce⟩ : ∃ c ∈ A, c ∉ M ∧ c + star c = h w w := by
      have h0 := ne0 hδ
      have h0' : star θ - θ ≠ 0 := fun e => h0 (by linear_combination -e)
      have tA : θ * (θ - star θ)⁻¹ * h w w ∈ A :=
        A.mul_mem (A.mul_mem hθ (hinv _ hδA hδ)) (hi _ hw _ hw)
      have te : θ * (θ - star θ)⁻¹ * h w w + star (θ * (θ - star θ)⁻¹ * h w w) = h w w := by
        simp only [star_mul', star_inv₀, star_sub, star_star, symm' hs]
        field_simp
        ring
      by_cases a : θ * (θ - star θ)⁻¹ * h w w ∈ M
      · refine ⟨(θ - star θ) + θ * (θ - star θ)⁻¹ * h w w, A.add_mem hδA tA, uadd hδ a, ?_⟩
        rw [star_add, star_sub, star_star]
        linear_combination te
      · exact ⟨_, tA, a, te⟩
    obtain ⟨g, g1, g2, g3⟩ := refl hs hA hΛ hi hw (ne0 cM) (hinv _ cA cM) ce
    have hgx : h (g x) (g x) = h x x := g1 x x
    refine Rel.trans ⟨g, g1, g2, rfl⟩ (step _ ((g2 x).2 hx) y hy (hgx.trans hn) ?_)
    have : h (g x) (g x) - h y (g x) = (c⁻¹ * (h w x * star (h w y))) + (h x x - h y x) := by
      rw [hgx, g3, symm' hs]
      simp only [map_sub, map_smul, smul_eq_mul]
      ring
    rw [this]
    exact uadd (umul (hinv _ cA cM) (uinv cA cM) (umul (hi _ hw _ hx) w1 (ustar (hi _ hw _ hy) w2))) hc
  · have θM : θ ∉ M := fun a => by
      by_cases b : star θ ∈ M
      · exact hδ (M.sub_mem a b)
      · exact ustar hsθ b (by rwa [star_star])
    have sM := ustar hθ θM
    have t0 := ne0 θM
    have s0 := ne0 sM
    have hxx := hi _ hx _ hx
    have μA : star θ * θ⁻¹ ∈ A := A.mul_mem hsθ (hinv _ hθ θM)
    have hz := hΛ _ μA y hy
    have e1 : ∀ v, h ((star θ * θ⁻¹) • y) v = θ * (star θ)⁻¹ * h y v := fun v => by
      simp [LinearMap.map_smulₛₗ, starRingEnd_apply, star_mul', star_inv₀]
    have e2 : h ((star θ * θ⁻¹) • y) ((star θ * θ⁻¹) • y) = h y y := by
      rw [e1, map_smul, smul_eq_mul]; field_simp
    refine Rel.trans (step x hx _ hz (hn.trans e2.symm) ?_) (step _ hz y hy e2 ?_)
    · have : h x x - h ((star θ * θ⁻¹) • y) x =
          -((θ - star θ) * ((star θ)⁻¹ * h x x)) + θ * (star θ)⁻¹ * (h x x - h y x) := by
        rw [e1]; field_simp; ring
      rw [this]
      refine uadd ?_ (hM _ (A.mul_mem hθ (hinv _ hsθ sM)) _ hc)
      rw [neg_mem_iff]
      exact umul hδA hδ (umul (hinv _ hsθ sM) (uinv hsθ sM) hnM)
    · have : h ((star θ * θ⁻¹) • y) ((star θ * θ⁻¹) • y) - h y ((star θ * θ⁻¹) • y) =
          (θ - star θ) * (θ⁻¹ * h x x) := by
        rw [e2, map_smul, smul_eq_mul, hn]; field_simp
      rw [this]
      exact umul hδA hδ (umul (hinv _ hθ θM) (uinv hθ θM) hnM)

end Abstract

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨star (r : K), (r.isIntegral_coe).map (starRingEnd K).toIntAlgHom⟩, rfl⟩`.
-/
theorem star_int {K : Type} [Field K] [NumberField K] [StarRing K] (r : 𝓞 K) :
    ∃ t : 𝓞 K, algebraMap (𝓞 K) K t = star (algebraMap (𝓞 K) K r) :=
  ⟨⟨star (r : K), (r.isIntegral_coe).map (starRingEnd K).toIntAlgHom⟩, rfl⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hs`. Use `hP.isPrime` as an intermediate fact. Conclude with `(Submonoid.closure_le (S := P.primeCompl)).2 (fun _ a => a.1) hs`. Introduce `hs`.

Use `Submonoid.subset_closure ⟨hs, fun t e ht => hs ?_⟩` and prove the remaining obligations. Rewrite using `[← hc]`. Conclude with `Ideal.subset_span ⟨t, ht, by rw [e, star_star]⟩`.
-/
theorem mem_hcompl {K : Type} [Field K] [NumberField K] [StarRing K] {P : Ideal (𝓞 K)}
    (hP : P.IsMaximal) (hc : conjIdeal (K := K) P = P) (s : 𝓞 K) :
    s ∈ hcompl (K := K) P ↔ s ∉ P := by
  constructor
  · intro hs
    have := hP.isPrime
    exact (Submonoid.closure_le (S := P.primeCompl)).2 (fun _ a => a.1) hs
  · intro hs
    refine Submonoid.subset_closure ⟨hs, fun t e ht => hs ?_⟩
    rw [← hc]
    exact Ideal.subset_span ⟨t, ht, by rw [e, star_star]⟩

/- English proof (translation)
Introduce `K V _ _ _ _ _ _ _ _ h hK hs _ L _ P hP hc hu x hx y hy hn px py`. Establish `hp` using `hP.isPrime`. Establish `inj : Function.Injective (algebraMap (𝓞 K) K)` using `RingOfIntegers.coe_injective`. Establish `one : (1 : 𝓞 K) ∉ P` using `fun a => hP.ne_top ((Ideal.eq_top_iff_one P).2 a)`. Establish `nm : ∀ {a b : 𝓞 K}, a ∉ P → b ∉ P → a * b ∉ P` using `fun ha hb e => (hp.mem_or_mem e).elim ha hb`.

Establish `mL : ∀ v, v ∈ loc (K` using `K) P L ↔ ∃ s, s ∉ P ∧ s • v ∈ L := fun v => exists_congr fun s => and_congr_left' (mem_hcompl hP hc s)`. Establish `mR : ∀ a : K, a ∈ locR (K` using `K) P ↔ ∃ s, s ∉ P ∧ ∃ r : 𝓞 K, algebraMap (𝓞 K) K r = algebraMap (𝓞 K) K s * a := fun a => exists_congr fun s => and_congr (mem_hcompl hP hc s) (by rw [Submodule.mem_one, Algebra.smul_def])`. Set `A : Subring K` to `{ carrier := {a | a ∈ locR (K := K) P} zero_mem' := (locR (K := K) P).zero_mem add_mem' := fun ha hb => (locR (K := K) P).add_mem ha hb neg_mem' := fun ha => (locR (K := K) P).neg_mem ha one_mem' := (mR 1).2 ⟨1, one, 1, by simp⟩ mul_mem' := by`. Introduce `a b ha hb`. Take `⟨s, hs, r, e⟩` from `(mR a).1 ha`.

Take `⟨s', hs', r', e'⟩` from `(mR b).1 hb`. Conclude with `(mR _).2 ⟨s * s', nm hs hs', r * r', by rw [map_mul, map_mul, e, e']; ring⟩ }`. Establish `mA : ∀ a, a ∈ A ↔ a ∈ locR (K` using `K) P := fun _ => Iff.rfl`. Set `M : AddSubgroup K` to `{ carrier := {a | ∃ s, s ∉ P ∧ ∃ r ∈ P, algebraMap (𝓞 K) K r = algebraMap (𝓞 K) K s * a} zero_mem' := ⟨1, one, 0, P.zero_mem, by simp⟩ add_mem' := by`. Introduce and unpack `a b ⟨s, hs, r, hr, e⟩ ⟨s', hs', r', hr', e'⟩`.

Conclude with `⟨s * s', nm hs hs', s' * r + s * r', P.add_mem (P.mul_mem_left _ hr) (P.mul_mem_left _ hr'), by simp only [map_add, map_mul, e, e']; ring⟩`. Use the proof step `neg_mem' := by`. Introduce and unpack `a ⟨s, hs, r, hr, e⟩`. Conclude with `⟨s, hs, -r, P.neg_mem hr, by rw [map_neg, e]; ring⟩ }`. Take `⟨θ, t, et, hθ⟩` from `hK.2.2 P hP`.

Establish `key : Rel h (loc (K` using `K) P L).toAddSubgroup x y := by`. Use `abs_main (A := A) (M := M) (θ := algebraMap (𝓞 K) K θ) hs ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy hn px py` and prove the remaining obligations. Introduce `a ha`. Take `⟨s, hs, r, e⟩` from `(mR a).1 ha`. Take `⟨s', es⟩` from `star_int s`.

Take `⟨r', er⟩` from `star_int r`. Use `(mR _).2 ⟨s', fun a => hs ?_, r', by rw [er, es, e, star_mul']⟩` and prove the remaining obligations. Rewrite using `[← hc]`. Conclude with `Ideal.subset_span ⟨s', a, by rw [es, star_star]⟩`. Introduce `a ha v hv`.

Take `⟨s, hs, r, e⟩` from `(mR a).1 ha`. Take `⟨s', hs', e'⟩` from `(mL v).1 hv`. Use `(mL _).2 ⟨s * s', nm hs hs', ?_⟩` and prove the remaining obligations. Establish `: (s * s') • a • v = r • s' • v`. Rewrite using `[← algebraMap_smul K (s * s'), ← algebraMap_smul K r, ← algebraMap_smul K s', smul_smul, smul_smul, e, map_mul]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `L.smul_mem r e'`. Introduce `v hv w hw`.

Establish `hw' : w ∈ dualAt h P (loc (K` using `K) P L) := by rw [hu]; exact hw`. Simplify using `only [dualAt, Submodule.mem_iInf, Submodule.mem_comap] at hw'`. Conclude with `hw' v hv`. Introduce and unpack `a ha m ⟨s', hs', r', hr', e'⟩`. Take `⟨s, hs, r, e⟩` from `(mR a).1 ha`.

Conclude with `⟨s * s', nm hs hs', r * r', P.mul_mem_left _ hr', by rw [map_mul, map_mul, e, e']; ring⟩`. Introduce and unpack `⟨s, hs, r, hr, e⟩`. Rewrite `e` using `[mul_one]`. Conclude with `hs (inj e ▸ hr)`. Introduce `a ha haM`.

Take `⟨s, hs, r, e⟩` from `(mR a).1 ha`. Establish `hr : r ∉ P` using `fun hr => haM ⟨s, hs, r, hr, e⟩`. Establish `a0 : a ≠ 0` using `fun e0 => haM (e0 ▸ M.zero_mem)`. Conclude with `(mR _).2 ⟨r, hr, s, by rw [e]; field_simp⟩`. Conclude with `(mR _).2 ⟨1, one, θ, by simp⟩`.

Introduce and unpack `⟨s, hs, r, hr, e⟩`. Rewrite `e` using `[← et, ← map_sub, ← map_mul]`. Conclude with `nm hs hθ (inj e ▸ hr)`. Take `⟨g, g1, g2, g3⟩` from `key`. Use `⟨g, g1, ?_, g3⟩` and prove the remaining obligations.

Use extensionality with `v`. Simplify using `only [gmap, Submodule.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, hw, rfl⟩`. Conclude with `(g2 w).2 hw`.

Introduce `hv`. Use `⟨g.symm v, (g2 _).1 (by simpa using hv), by simp⟩` and prove the remaining obligations.
-/
theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → h.Nondegenerate → ∀ (L : Submodule (𝓞 K) V), Submodule.IsLattice K L → ∀ P : Ideal (𝓞 K), P.IsMaximal → conjIdeal (K := K) P = P → IsUnimodularAt h P L → ∀ x ∈ loc (K := K) P L, ∀ y ∈ loc (K := K) P L, h x x = h y y → (∃ w ∈ loc (K := K) P L, h w x = 1) → (∃ w ∈ loc (K := K) P L, h w y = 1) → ∃ g ∈ isom h, gmap g (loc (K := K) P L) = loc (K := K) P L ∧ g x = y := by
  intro K V _ _ _ _ _ _ _ _ h hK hs _ L _ P hP hc hu x hx y hy hn px py
  have hp := hP.isPrime
  have inj : Function.Injective (algebraMap (𝓞 K) K) := RingOfIntegers.coe_injective
  have one : (1 : 𝓞 K) ∉ P := fun a => hP.ne_top ((Ideal.eq_top_iff_one P).2 a)
  have nm : ∀ {a b : 𝓞 K}, a ∉ P → b ∉ P → a * b ∉ P := fun ha hb e => (hp.mem_or_mem e).elim ha hb
  have mL : ∀ v, v ∈ loc (K := K) P L ↔ ∃ s, s ∉ P ∧ s • v ∈ L := fun v =>
    exists_congr fun s => and_congr_left' (mem_hcompl hP hc s)
  have mR : ∀ a : K, a ∈ locR (K := K) P ↔ ∃ s, s ∉ P ∧ ∃ r : 𝓞 K,
      algebraMap (𝓞 K) K r = algebraMap (𝓞 K) K s * a := fun a =>
    exists_congr fun s => and_congr (mem_hcompl hP hc s) (by rw [Submodule.mem_one, Algebra.smul_def])
  let A : Subring K :=
    { carrier := {a | a ∈ locR (K := K) P}
      zero_mem' := (locR (K := K) P).zero_mem
      add_mem' := fun ha hb => (locR (K := K) P).add_mem ha hb
      neg_mem' := fun ha => (locR (K := K) P).neg_mem ha
      one_mem' := (mR 1).2 ⟨1, one, 1, by simp⟩
      mul_mem' := by
        intro a b ha hb
        obtain ⟨s, hs, r, e⟩ := (mR a).1 ha
        obtain ⟨s', hs', r', e'⟩ := (mR b).1 hb
        exact (mR _).2 ⟨s * s', nm hs hs', r * r', by rw [map_mul, map_mul, e, e']; ring⟩ }
  have mA : ∀ a, a ∈ A ↔ a ∈ locR (K := K) P := fun _ => Iff.rfl
  let M : AddSubgroup K :=
    { carrier := {a | ∃ s, s ∉ P ∧ ∃ r ∈ P, algebraMap (𝓞 K) K r = algebraMap (𝓞 K) K s * a}
      zero_mem' := ⟨1, one, 0, P.zero_mem, by simp⟩
      add_mem' := by
        rintro a b ⟨s, hs, r, hr, e⟩ ⟨s', hs', r', hr', e'⟩
        exact ⟨s * s', nm hs hs', s' * r + s * r', P.add_mem (P.mul_mem_left _ hr) (P.mul_mem_left _ hr'),
          by simp only [map_add, map_mul, e, e']; ring⟩
      neg_mem' := by
        rintro a ⟨s, hs, r, hr, e⟩
        exact ⟨s, hs, -r, P.neg_mem hr, by rw [map_neg, e]; ring⟩ }
  obtain ⟨θ, t, et, hθ⟩ := hK.2.2 P hP
  have key : Rel h (loc (K := K) P L).toAddSubgroup x y := by
    refine abs_main (A := A) (M := M) (θ := algebraMap (𝓞 K) K θ) hs ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy hn px py
    · intro a ha
      obtain ⟨s, hs, r, e⟩ := (mR a).1 ha
      obtain ⟨s', es⟩ := star_int s
      obtain ⟨r', er⟩ := star_int r
      refine (mR _).2 ⟨s', fun a => hs ?_, r', by rw [er, es, e, star_mul']⟩
      rw [← hc]
      exact Ideal.subset_span ⟨s', a, by rw [es, star_star]⟩
    · intro a ha v hv
      obtain ⟨s, hs, r, e⟩ := (mR a).1 ha
      obtain ⟨s', hs', e'⟩ := (mL v).1 hv
      refine (mL _).2 ⟨s * s', nm hs hs', ?_⟩
      have : (s * s') • a • v = r • s' • v := by
        rw [← algebraMap_smul K (s * s'), ← algebraMap_smul K r, ← algebraMap_smul K s', smul_smul,
          smul_smul, e, map_mul]
        congr 1; ring
      rw [this]
      exact L.smul_mem r e'
    · intro v hv w hw
      have hw' : w ∈ dualAt h P (loc (K := K) P L) := by rw [hu]; exact hw
      simp only [dualAt, Submodule.mem_iInf, Submodule.mem_comap] at hw'
      exact hw' v hv
    · rintro a ha m ⟨s', hs', r', hr', e'⟩
      obtain ⟨s, hs, r, e⟩ := (mR a).1 ha
      exact ⟨s * s', nm hs hs', r * r', P.mul_mem_left _ hr', by rw [map_mul, map_mul, e, e']; ring⟩
    · rintro ⟨s, hs, r, hr, e⟩
      rw [mul_one] at e
      exact hs (inj e ▸ hr)
    · intro a ha haM
      obtain ⟨s, hs, r, e⟩ := (mR a).1 ha
      have hr : r ∉ P := fun hr => haM ⟨s, hs, r, hr, e⟩
      have a0 : a ≠ 0 := fun e0 => haM (e0 ▸ M.zero_mem)
      exact (mR _).2 ⟨r, hr, s, by rw [e]; field_simp⟩
    · exact (mR _).2 ⟨1, one, θ, by simp⟩
    · rintro ⟨s, hs, r, hr, e⟩
      rw [← et, ← map_sub, ← map_mul] at e
      exact nm hs hθ (inj e ▸ hr)
  obtain ⟨g, g1, g2, g3⟩ := key
  refine ⟨g, g1, ?_, g3⟩
  ext v
  simp only [gmap, Submodule.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (g2 w).2 hw
  · intro hv
    refine ⟨g.symm v, (g2 _).1 (by simpa using hv), by simp⟩

end GlobalTheory.Mass.LocWitt
