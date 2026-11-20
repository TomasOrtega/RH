import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.InLZeroIff

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.WCB

section Alg

variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]

def skewY (h : V →ₗ⋆[K] V →ₗ[K] K) (u w : V) (θ : K) : V →ₗ[K] V :=
  (θ • h u - h w).smulRight u + (h u).smulRight w

/- English proof (translation)
Simplify using `[skewY]`.
-/
theorem skewY_apply (h : V →ₗ⋆[K] V →ₗ[K] K) (u w : V) (θ : K) (z : V) :
    skewY h u w θ z = (θ * h u z - h w z) • u + h u z • w := by
  simp [skewY]

/- English proof (translation)
Establish `e1 : star (h u a) = h a u` using `hs.eq u a`. Establish `e2 : star (h w a) = h a w` using `hs.eq w a`. Rewrite using `[skewY_apply, skewY_apply]`. Simplify using `only [map_add, map_smul, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_sub, star_mul', e1, e2, hθ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem skewY_skew {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (u w : V) {θ : K} (hθ : star θ = -θ)
    (a b : V) : h (skewY h u w θ a) b + h a (skewY h u w θ b) = 0 := by
  have e1 : star (h u a) = h a u := hs.eq u a
  have e2 : star (h w a) = h a w := hs.eq w a
  rw [skewY_apply, skewY_apply]
  simp only [map_add, map_smul, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    starRingEnd_apply, star_sub, star_mul', e1, e2, hθ]
  ring

/- English proof (translation)
Apply `han` to reduce the goal to its premises. Establish `h1 : h z z = m * h z (Y z)`. Use `congrArg (h z) hz` as an intermediate fact. Rewrite `this` using `[map_smul, smul_eq_mul]`. Then use the resulting hypothesis. Establish `h2 : h z z = l * h (Y z) z`.

Use `congrArg (fun t => h t z) hz` as an intermediate fact. Simplify using `only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, hm] at this`. Conclude with `this`. Establish `h3` using `hY z z`. Establish `h4 : h z (Y z) = 0` using `by linear_combination (-(h z (Y z))) * hl - h1 + h2 + l * h3`.

Rewrite using `[h1, h4, mul_zero]`.
-/
theorem laurent_adjoin_eq_of_image_eq {h : V →ₗ⋆[K] V →ₗ[K] K} (han : ∀ x, h x x = 0 → x = 0) {Y : V →ₗ[K] V}
    (hY : ∀ a b, h (Y a) b + h a (Y b) = 0) {l m : K} (hm : star m = l) (hl : l + m = 1) {z : V}
    (hz : z = m • Y z) : z = 0 := by
  apply han
  have h1 : h z z = m * h z (Y z) := by
    have := congrArg (h z) hz
    rwa [map_smul, smul_eq_mul] at this
  have h2 : h z z = l * h (Y z) z := by
    have := congrArg (fun t => h t z) hz
    simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, hm] at this
    exact this
  have h3 := hY z z
  have h4 : h z (Y z) = 0 := by linear_combination (-(h z (Y z))) * hl - h1 + h2 + l * h3
  rw [h1, h4, mul_zero]

/- English proof (translation)
Set `S : V →ₗ[K] V` to `LinearMap.id - star l • Y`. Set `T : V →ₗ[K] V` to `LinearMap.id + l • Y`. Establish `hS : Function.Injective S`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `z hz`.

Establish `hz' : z - star l • Y z = 0` using `hz`. Conclude with `laurent_adjoin_eq_of_image_eq han hY (star_star l) hl (sub_eq_zero.1 hz')`. Establish `hT : Function.Injective T`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `z hz`.

Establish `hz' : z + l • Y z = 0` using `hz`. Establish `hY' : ∀ a b, h ((-Y) a) b + h a ((-Y) b) = 0`. Introduce `a b`. Simplify using `only [LinearMap.neg_apply, map_neg]`. Take the linear combination `(-1 : K) * hY a b`.

Use `laurent_adjoin_eq_of_image_eq (l := star l) (m := l) han hY' rfl (by rw [add_comm]; exact hl) ?_` and prove the remaining obligations. Rewrite using `[LinearMap.neg_apply, smul_neg]`. Conclude with `eq_neg_of_add_eq_zero_left hz'`. Set `eS` to `LinearEquiv.ofInjectiveEndo S hS`. Set `eT` to `LinearEquiv.ofInjectiveEndo T hT`.

Establish `heS : ∀ z, eS z = z - star l • Y z` using `fun z => rfl`. Establish `heT : ∀ z, eT z = z + l • Y z` using `fun z => rfl`. Use `⟨eS.symm.trans eT, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x y`. Take `⟨a, rfl⟩` from `eS.surjective x`.

Take `⟨b, rfl⟩` from `eS.surjective y`. Simplify using `only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]`. Rewrite using `[heS, heS, heT, heT]`. Simplify using `only [map_add, map_sub, map_smul, map_smulₛₗ, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_star]`. Take the linear combination `(l + star l) * hY a b`.

Introduce `z`. Rewrite using `[← heS, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, heT]`. Introduce `z`. Conclude with `⟨eS.symm z, by rw [← heS, LinearEquiv.apply_symm_apply]⟩`. Introduce `z`.

Conclude with `⟨eT.symm z, by rw [← heT, LinearEquiv.apply_symm_apply]⟩`.
-/
theorem exists_cayley [FiniteDimensional K V] {h : V →ₗ⋆[K] V →ₗ[K] K}
    (han : ∀ x, h x x = 0 → x = 0) {Y : V →ₗ[K] V} (hY : ∀ a b, h (Y a) b + h a (Y b) = 0) {l : K}
    (hl : l + star l = 1) :
    ∃ g : V ≃ₗ[K] V, g ∈ Formalism.HermitianLatticesTheory.isom h ∧ (∀ z, g (z - star l • Y z) = z + l • Y z) ∧
      (∀ z, ∃ z', z' - star l • Y z' = z) ∧ (∀ z, ∃ z', z' + l • Y z' = z) := by
  let S : V →ₗ[K] V := LinearMap.id - star l • Y
  let T : V →ₗ[K] V := LinearMap.id + l • Y
  have hS : Function.Injective S := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    have hz' : z - star l • Y z = 0 := hz
    exact laurent_adjoin_eq_of_image_eq han hY (star_star l) hl (sub_eq_zero.1 hz')
  have hT : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    have hz' : z + l • Y z = 0 := hz
    have hY' : ∀ a b, h ((-Y) a) b + h a ((-Y) b) = 0 := by
      intro a b
      simp only [LinearMap.neg_apply, map_neg]
      linear_combination (-1 : K) * hY a b
    refine laurent_adjoin_eq_of_image_eq (l := star l) (m := l) han hY' rfl (by rw [add_comm]; exact hl) ?_
    rw [LinearMap.neg_apply, smul_neg]
    exact eq_neg_of_add_eq_zero_left hz'
  let eS := LinearEquiv.ofInjectiveEndo S hS
  let eT := LinearEquiv.ofInjectiveEndo T hT
  have heS : ∀ z, eS z = z - star l • Y z := fun z => rfl
  have heT : ∀ z, eT z = z + l • Y z := fun z => rfl
  refine ⟨eS.symm.trans eT, ?_, ?_, ?_, ?_⟩
  · intro x y
    obtain ⟨a, rfl⟩ := eS.surjective x
    obtain ⟨b, rfl⟩ := eS.surjective y
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    rw [heS, heS, heT, heT]
    simp only [map_add, map_sub, map_smul, map_smulₛₗ, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_star]
    linear_combination (l + star l) * hY a b
  · intro z
    rw [← heS, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, heT]
  · intro z
    exact ⟨eS.symm z, by rw [← heS, LinearEquiv.apply_symm_apply]⟩
  · intro z
    exact ⟨eT.symm z, by rw [← heT, LinearEquiv.apply_symm_apply]⟩

end Alg

section Int

open WCA

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {𝔭 : Ideal (𝓞 F)} {A : Submodule (𝓞 K) V}

/- English proof (translation)
Rewrite using `[skewY_apply]`. Use `InL.add hp ?_ ?_` and prove the remaining obligations. Use `(InL.smul hp (i := J) ?_ hu).mono (by omega)` and prove the remaining obligations. Conclude with `InI.sub hp ((hθ.mul hp (hu.form hp hF hA hz)).mono (by omega)) ((hw.form hp hF hA hz).mono (by omega))`. Conclude with `(InL.smul hp (hu.form hp hF hA hz) hw).mono (by omega)`.
-/
theorem skewY_mem (hp : 𝔭.IsPrime) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hA : Formalism.HermitianLatticesTheory.IsIntegralLat h A) {J : ℕ} {u w z : V} {θ : K} (hu : InL 𝔭 A 0 u)
    (hw : InL 𝔭 A J w) (hθ : InI 𝔭 J θ) (hz : InL 𝔭 A 0 z) : InL 𝔭 A J (skewY h u w θ z) := by
  rw [skewY_apply]
  refine InL.add hp ?_ ?_
  · refine (InL.smul hp (i := J) ?_ hu).mono (by omega)
    exact InI.sub hp ((hθ.mul hp (hu.form hp hF hA hz)).mono (by omega))
      ((hw.form hp hF hA hz).mono (by omega))
  · exact (InL.smul hp (hu.form hp hF hA hz) hw).mono (by omega)

/- English proof (translation)
Establish `hp` using `h𝔭.isPrime`. Take `⟨b, hb⟩ : ∃ b : K, b = h u z'` from `⟨_, rfl⟩`. Take `⟨a, ha⟩ : ∃ a : K, a = θ * b - h w z'` from `⟨_, rfl⟩`. Establish `e' : z' = z + (c * a) • u + (c * b) • w`. Rewrite `e` using `[skewY_apply, ← hb, ← ha]`.

Rewrite using `[← e, smul_add, smul_smul, smul_smul]`. Normalize the expressions using the abelian group laws. Establish `eb : b = h u z + c * a * h u u + c * b * h u w` using `by conv_lhs => rw [hb, e']`. Rewrite using `[map_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]`. Establish `ew : h w z' = h w z + c * a * h w u + c * b * h w w` using `by conv_lhs => rw [e']`.

Rewrite using `[map_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]`. Establish `Iν : InI 𝔭 0 (h u u)` using `hu.form hp hF hA hu`. Establish `Ip : InI 𝔭 1 (h u w)` using `(hu.form hp hF hA hw).mono (by omega)`. Establish `Ir : InI 𝔭 1 (h w u)` using `(hw.form hp hF hA hu).mono (by omega)`. Establish `Is : InI 𝔭 1 (h w w)` using `(hw.form hp hF hA hw).mono (by omega)`.

Establish `Iβ : InI 𝔭 0 (h u z)` using `hu.form hp hF hA hz`. Establish `Iγ : InI 𝔭 0 (h w z)` using `(hw.form hp hF hA hz).mono (by omega)`. Establish `m01 : ∀ {x y : K}, InI 𝔭 0 x → InI 𝔭 1 y → InI 𝔭 1 (x * y)` using `fun hx hy => (hx.mul hp hy).mono (by omega)`. Establish `m00 : ∀ {x y : K}, InI 𝔭 0 x → InI 𝔭 0 y → InI 𝔭 0 (x * y)` using `fun hx hy => hx.mul hp hy`. Establish `Icr : InI 𝔭 1 (c * h w u)` using `m01 hc Ir`.

Establish `Iκ : InI 𝔭 1 (θ - c * h w w)` using `hθ.sub hp (m01 hc Is)`. Take `⟨hE1, IE1⟩` from `InI.unit h𝔭 hF Icr`. Establish `Iε : InI 𝔭 1 (c * h w u - c * h u w - c * h u w * (c * h w u) - c * h u u * (θ - c * h w w))` using `((Icr.sub hp (m01 hc Ip)).sub hp (m01 (m00 hc (Ip.mono (by omega))) Icr)).sub hp (m01 (m00 hc Iν) Iκ)`. Take `⟨hD, ID⟩` from `InI.unit h𝔭 hF Iε`. Establish `ea : a * (1 + c * h w u) = b * (θ - c * h w w) - h w z`.

Take the linear combination `ha - ew`. Establish `ebD : b * (1 + (c * h w u - c * h u w - c * h u w * (c * h w u) - c * h u u * (θ - c * h w w))) = h u z * (1 + c * h w u) - c * h u u * h w z`. Take the linear combination `(1 + c * h w u) * eb + c * h u u * ea`. Establish `Ib : InI 𝔭 0 b`. Rewrite using `[(eq_mul_inv_iff_mul_eq₀ hD).2 ebD]`.

Conclude with `m00 ((m00 Iβ ((InI.one hp).add hp (Icr.mono (by omega)))).sub hp (m00 (m00 hc Iν) Iγ)) ID`. Establish `Ia : InI 𝔭 0 a`. Rewrite using `[(eq_mul_inv_iff_mul_eq₀ hE1).2 ea]`. Conclude with `m00 ((m00 Ib (Iκ.mono (by omega))).sub hp Iγ) IE1`. Rewrite using `[e']`.

Establish `h1 : InL 𝔭 A 0 ((c * a) • u)` using `(InL.smul hp (m00 hc Ia) hu).mono (by omega)`. Establish `h2 : InL 𝔭 A 0 ((c * b) • w)` using `(InL.smul hp (m00 hc Ib) hw).mono (by omega)`. Conclude with `(hz.add hp h1).add hp h2`.
-/
theorem mem_of_resolvent (h𝔭 : 𝔭.IsMaximal) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hA : Formalism.HermitianLatticesTheory.IsIntegralLat h A) {u w z z' : V} {θ c : K} (hu : InL 𝔭 A 0 u)
    (hw : InL 𝔭 A 1 w) (hθ : InI 𝔭 1 θ) (hc : InI 𝔭 0 c) (hz : InL 𝔭 A 0 z)
    (e : z' - c • skewY h u w θ z' = z) : InL 𝔭 A 0 z' := by
  have hp := h𝔭.isPrime
  obtain ⟨b, hb⟩ : ∃ b : K, b = h u z' := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : K, a = θ * b - h w z' := ⟨_, rfl⟩
  have e' : z' = z + (c * a) • u + (c * b) • w := by
    rw [skewY_apply, ← hb, ← ha] at e
    rw [← e, smul_add, smul_smul, smul_smul]
    abel
  have eb : b = h u z + c * a * h u u + c * b * h u w := by
    conv_lhs => rw [hb, e']
    rw [map_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have ew : h w z' = h w z + c * a * h w u + c * b * h w w := by
    conv_lhs => rw [e']
    rw [map_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have Iν : InI 𝔭 0 (h u u) := hu.form hp hF hA hu
  have Ip : InI 𝔭 1 (h u w) := (hu.form hp hF hA hw).mono (by omega)
  have Ir : InI 𝔭 1 (h w u) := (hw.form hp hF hA hu).mono (by omega)
  have Is : InI 𝔭 1 (h w w) := (hw.form hp hF hA hw).mono (by omega)
  have Iβ : InI 𝔭 0 (h u z) := hu.form hp hF hA hz
  have Iγ : InI 𝔭 0 (h w z) := (hw.form hp hF hA hz).mono (by omega)
  have m01 : ∀ {x y : K}, InI 𝔭 0 x → InI 𝔭 1 y → InI 𝔭 1 (x * y) := fun hx hy =>
    (hx.mul hp hy).mono (by omega)
  have m00 : ∀ {x y : K}, InI 𝔭 0 x → InI 𝔭 0 y → InI 𝔭 0 (x * y) := fun hx hy => hx.mul hp hy
  have Icr : InI 𝔭 1 (c * h w u) := m01 hc Ir
  have Iκ : InI 𝔭 1 (θ - c * h w w) := hθ.sub hp (m01 hc Is)
  obtain ⟨hE1, IE1⟩ := InI.unit h𝔭 hF Icr
  have Iε : InI 𝔭 1 (c * h w u - c * h u w - c * h u w * (c * h w u)
      - c * h u u * (θ - c * h w w)) :=
    ((Icr.sub hp (m01 hc Ip)).sub hp (m01 (m00 hc (Ip.mono (by omega))) Icr)).sub hp
      (m01 (m00 hc Iν) Iκ)
  obtain ⟨hD, ID⟩ := InI.unit h𝔭 hF Iε
  have ea : a * (1 + c * h w u) = b * (θ - c * h w w) - h w z := by
    linear_combination ha - ew
  have ebD : b * (1 + (c * h w u - c * h u w - c * h u w * (c * h w u)
      - c * h u u * (θ - c * h w w))) = h u z * (1 + c * h w u) - c * h u u * h w z := by
    linear_combination (1 + c * h w u) * eb + c * h u u * ea
  have Ib : InI 𝔭 0 b := by
    rw [(eq_mul_inv_iff_mul_eq₀ hD).2 ebD]
    exact m00 ((m00 Iβ ((InI.one hp).add hp (Icr.mono (by omega)))).sub hp (m00 (m00 hc Iν) Iγ)) ID
  have Ia : InI 𝔭 0 a := by
    rw [(eq_mul_inv_iff_mul_eq₀ hE1).2 ea]
    exact m00 ((m00 Ib (Iκ.mono (by omega))).sub hp Iγ) IE1
  rw [e']
  have h1 : InL 𝔭 A 0 ((c * a) • u) := (InL.smul hp (m00 hc Ia) hu).mono (by omega)
  have h2 : InL 𝔭 A 0 ((c * b) • w) := (InL.smul hp (m00 hc Ib) hw).mono (by omega)
  exact (hz.add hp h1).add hp h2

end Int

end Formalism.HermitianLattices.Ext.L3.WCB
