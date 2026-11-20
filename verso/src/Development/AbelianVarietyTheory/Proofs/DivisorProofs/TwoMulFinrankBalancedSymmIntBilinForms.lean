import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemBalBil
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PolFan

noncomputable section

namespace GlobalTheory.BalRankSym

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Apply `RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[H.bar_eq, H.bar_eq]`. Conclude with `IsCMField.complexConj_apply_apply E _`.
-/
theorem host_bar_bar (H : Host E) (a : 𝓞 E) : H.bar (H.bar a) = a := by
  apply RingOfIntegers.ext
  rw [H.bar_eq, H.bar_eq]
  exact IsCMField.complexConj_apply_apply E _

/- English proof (translation)
Establish `h1 : (H.bar H.rt) ^ 2 = H.rt ^ 2` using `by rw [← map_pow, H.rt_sq]; simp`. Break down `sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h` into its components or cases. It suffices to derive a contradiction. Take `⟨φ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Establish `h2 : IsCMField.complexConj E (H.rt : E) = (H.rt : E)` using `by rw [← H.bar_eq, h]`.

Establish `h3` using `IsCMField.complexEmbedding_complexConj E φ (H.rt : E)`. Rewrite `h3` using `[h2]`. Establish `h4 : (φ (H.rt : E)) ^ 2 = -(H.d : ℂ)`. Use `congrArg (fun x : 𝓞 E => φ (x : E)) H.rt_sq` as an intermediate fact. Simplify using `using this`.

Establish `h5 : (φ (H.rt : E)).im = 0` using `Complex.conj_eq_iff_im.1 h3.symm`. Establish `h6` using `congrArg Complex.re h4`. Simplify using `[sq, h5] at h6`. Establish `h7 : (0 : ℝ) < H.d` using `by exact_mod_cast H.d_prime.pos`. Use polynomial arithmetic with `[mul_self_nonneg (φ (H.rt : E)).re]`.

Conclude with `h`.
-/
theorem host_bar_rt (H : Host E) : H.bar H.rt = -H.rt := by
  have h1 : (H.bar H.rt) ^ 2 = H.rt ^ 2 := by rw [← map_pow, H.rt_sq]; simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
  · exfalso
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have h2 : IsCMField.complexConj E (H.rt : E) = (H.rt : E) := by rw [← H.bar_eq, h]
    have h3 := IsCMField.complexEmbedding_complexConj E φ (H.rt : E)
    rw [h2] at h3
    have h4 : (φ (H.rt : E)) ^ 2 = -(H.d : ℂ) := by
      have := congrArg (fun x : 𝓞 E => φ (x : E)) H.rt_sq
      simpa using this
    have h5 : (φ (H.rt : E)).im = 0 := Complex.conj_eq_iff_im.1 h3.symm
    have h6 := congrArg Complex.re h4
    simp [sq, h5] at h6
    have h7 : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    nlinarith [mul_self_nonneg (φ (H.rt : E)).re]
  · exact h

variable (H : Host E) (X : Type) [AddCommGroup X] [Module (𝓞 E) X]

def rtMul : X →ₗ[ℤ] X := (DistribMulAction.toAddMonoidHom X H.rt).toIntLinearMap

variable {H X}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem rtMul_apply (y : X) : rtMul H X y = H.rt • y := rfl

/- English proof (translation)
Rewrite using `[smul_smul, ← sq, H.rt_sq, neg_smul, ← Int.cast_natCast, Int.cast_smul_eq_zsmul]`.
-/
theorem rt_smul_rt_smul (y : X) : H.rt • H.rt • y = -((H.d : ℤ) • y) := by
  rw [smul_smul, ← sq, H.rt_sq, neg_smul, ← Int.cast_natCast, Int.cast_smul_eq_zsmul]

/- English proof (translation)
Introduce `a y z`. Use `show β z (a • y) = β (H.bar a • z) y`. Rewrite using `[hβ (H.bar a) z y, host_bar_bar]`.
-/
theorem flip_mem_balBil {β : LinearMap.BilinForm ℤ X} (hβ : β ∈ GlobalTheory.BalRank.balBil H.bar X) :
    β.flip ∈ GlobalTheory.BalRank.balBil H.bar X := by
  intro a y z
  show β z (a • y) = β (H.bar a • z) y
  rw [hβ (H.bar a) z y, host_bar_bar]

/- English proof (translation)
Introduce `a y z`. Simplify using `only [LinearMap.comp_apply, rtMul_apply]`. Rewrite using `[smul_comm, hβ]`.
-/
theorem comp_rt_mem_balBil {β : LinearMap.BilinForm ℤ X} (hβ : β ∈ GlobalTheory.BalRank.balBil H.bar X) :
    β ∘ₗ rtMul H X ∈ GlobalTheory.BalRank.balBil H.bar X := by
  intro a y z
  simp only [LinearMap.comp_apply, rtMul_apply]
  rw [smul_comm, hβ]

/- English proof (translation)
Rewrite using `[hβ, host_bar_rt, neg_smul, map_neg, hs]`.
-/
theorem comp_rt_antisymm {β : LinearMap.BilinForm ℤ X} (hβ : β ∈ GlobalTheory.BalRank.balBil H.bar X)
    (hs : ∀ y z, β y z = β z y) (y z : X) : β (H.rt • y) z = -β (H.rt • z) y := by
  rw [hβ, host_bar_rt, neg_smul, map_neg, hs]

/- English proof (translation)
Rewrite using `[hβ, host_bar_rt, neg_smul, map_neg, hs, neg_neg]`.
-/
theorem comp_rt_symm {β : LinearMap.BilinForm ℤ X} (hβ : β ∈ GlobalTheory.BalRank.balBil H.bar X)
    (hs : ∀ y z, β y z = -β z y) (y z : X) : β (H.rt • y) z = β (H.rt • z) y := by
  rw [hβ, host_bar_rt, neg_smul, map_neg, hs, neg_neg]

end GlobalTheory.BalRankSym

namespace GlobalTheory.BalRankSym

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Type) [AddCommGroup X] [Module (𝓞 E) X]

def symPart : GlobalTheory.BalRank.balBil H.bar X →ₗ[ℤ] balForms H.bar X where
  toFun β := ⟨β.1 + β.1.flip, fun y z => by simp [add_comm], fun a y z => by
    have h1 := β.2 a y z
    have h2 := flip_mem_balBil β.2 a y z
    simp only [LinearMap.add_apply]
    rw [h1, h2]⟩
  map_add' β γ := by
    apply Subtype.ext
    ext y z
    simp only [Submodule.coe_add, LinearMap.add_apply, LinearMap.flip_apply, LinearMap.BilinForm.flip_apply]
    ring
  map_smul' n β := by
    apply Subtype.ext
    ext y z
    simp only [SetLike.val_smul, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.flip_apply, LinearMap.BilinForm.flip_apply, RingHom.id_apply, smul_eq_mul]
    ring

def antiPart : GlobalTheory.BalRank.balBil H.bar X →ₗ[ℤ] balForms H.bar X where
  toFun β := ⟨(β.1 - β.1.flip) ∘ₗ rtMul H X,
    fun y z => by
      have hm : β.1 - β.1.flip ∈ GlobalTheory.BalRank.balBil H.bar X := sub_mem β.2 (flip_mem_balBil β.2)
      have := comp_rt_symm hm (fun y z => by simp) y z
      simpa [rtMul_apply] using this,
    comp_rt_mem_balBil (sub_mem β.2 (flip_mem_balBil β.2))⟩
  map_add' β γ := by
    apply Subtype.ext
    ext y z
    simp only [Submodule.coe_add, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.flip_apply, LinearMap.BilinForm.flip_apply]
    ring
  map_smul' n β := by
    apply Subtype.ext
    ext y z
    simp only [SetLike.val_smul, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.flip_apply, LinearMap.BilinForm.flip_apply,
      RingHom.id_apply, smul_eq_mul]
    ring

def symIncl : balForms H.bar X →ₗ[ℤ] GlobalTheory.BalRank.balBil H.bar X where
  toFun s := ⟨s.1, s.2.2⟩
  map_add' s t := rfl
  map_smul' n t := rfl

def rtPart : balForms H.bar X →ₗ[ℤ] GlobalTheory.BalRank.balBil H.bar X where
  toFun t := ⟨t.1 ∘ₗ rtMul H X, comp_rt_mem_balBil t.2.2⟩
  map_add' s t := by
    apply Subtype.ext
    ext y z
    simp
  map_smul' n t := by
    apply Subtype.ext
    ext y z
    simp

variable {H X}

/- English proof (translation)
Rewrite using `[← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]`. Introduce `β hβ`. Rewrite `hβ` using `[LinearMap.mem_ker, LinearMap.prod_apply, Prod.mk_eq_zero]`. Take `⟨h1, h2⟩` from `hβ`. Establish `e1 : ∀ y z, β.1 y z + β.1 z y = 0` using `fun y z => by`.

Use `congrArg (fun γ : balForms H.bar X => γ.1 y z) h1` as an intermediate fact. Simplify `this` using `[symPart]`. Establish `e2 : ∀ y z, β.1 (H.rt • y) z - β.1 z (H.rt • y) = 0` using `fun y z => by`. Use `congrArg (fun γ : balForms H.bar X => γ.1 y z) h2` as an intermediate fact. Simplify `this` using `[antiPart, rtMul_apply]`.

Establish `hd : (H.d : ℤ) ≠ 0` using `by exact_mod_cast H.d_prime.ne_zero`. Establish `e3 : ∀ y z, β.1 y z - β.1 z y = 0` using `fun y z => by`. Use `e2 (H.rt • y) z` as an intermediate fact. Rewrite `this` using `[rt_smul_rt_smul, map_neg, map_zsmul, LinearMap.neg_apply, LinearMap.smul_apply, map_neg, map_zsmul]`. Simplify using `only [smul_eq_mul] at this`.

Establish `: (H.d : ℤ) * (β.1 y z - β.1 z y) = 0` using `by linear_combination -this`. Conclude with `(mul_eq_zero.1 this).resolve_left hd`. Apply `Subtype.ext` to reduce the goal to its premises. Use extensionality with `y z`. Use `e1 y z` as an intermediate fact.

Use `e3 y z` as an intermediate fact. Simplify using `only [ZeroMemClass.coe_zero, LinearMap.zero_apply]`. Use linear arithmetic over natural numbers and integers.
-/
theorem symPart_antiPart_injective :
    Function.Injective (LinearMap.prod (symPart H X) (antiPart H X)) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro β hβ
  rw [LinearMap.mem_ker, LinearMap.prod_apply, Prod.mk_eq_zero] at hβ
  obtain ⟨h1, h2⟩ := hβ
  have e1 : ∀ y z, β.1 y z + β.1 z y = 0 := fun y z => by
    have := congrArg (fun γ : balForms H.bar X => γ.1 y z) h1
    simpa [symPart] using this
  have e2 : ∀ y z, β.1 (H.rt • y) z - β.1 z (H.rt • y) = 0 := fun y z => by
    have := congrArg (fun γ : balForms H.bar X => γ.1 y z) h2
    simpa [antiPart, rtMul_apply] using this
  have hd : (H.d : ℤ) ≠ 0 := by exact_mod_cast H.d_prime.ne_zero
  have e3 : ∀ y z, β.1 y z - β.1 z y = 0 := fun y z => by
    have := e2 (H.rt • y) z
    rw [rt_smul_rt_smul, map_neg, map_zsmul, LinearMap.neg_apply, LinearMap.smul_apply, map_neg, map_zsmul] at this
    simp only [smul_eq_mul] at this
    have : (H.d : ℤ) * (β.1 y z - β.1 z y) = 0 := by linear_combination -this
    exact (mul_eq_zero.1 this).resolve_left hd
  apply Subtype.ext
  ext y z
  have := e1 y z
  have := e3 y z
  simp only [ZeroMemClass.coe_zero, LinearMap.zero_apply]
  omega

/- English proof (translation)
Rewrite using `[← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]`. Introduce and unpack `⟨s, t⟩ hst`. Rewrite `hst` using `[LinearMap.mem_ker, LinearMap.coprod_apply]`. Establish `e : ∀ y z, s.1 y z + t.1 (H.rt • y) z = 0` using `fun y z => by`. Use `congrArg (fun γ : GlobalTheory.BalRank.balBil H.bar X => γ.1 y z) hst` as an intermediate fact.

Simplify `this` using `[symIncl, rtPart, rtMul_apply, Submodule.coe_inclusion]`. Establish `hd : (H.d : ℤ) ≠ 0` using `by exact_mod_cast H.d_prime.ne_zero`. Establish `et : ∀ y z, t.1 (H.rt • y) z = 0` using `fun y z => by`. Establish `a1` using `e y z`. Establish `a2` using `e z y`.

Establish `a3` using `s.2.1 y z`. Establish `a4` using `comp_rt_antisymm t.2.2 t.2.1 y z`. Use linear arithmetic over natural numbers and integers. Establish `ht : ∀ y z, t.1 y z = 0` using `fun y z => by`. Use `et (H.rt • y) z` as an intermediate fact.

Rewrite `this` using `[rt_smul_rt_smul, map_neg, map_zsmul, LinearMap.neg_apply, LinearMap.smul_apply]`. Simplify using `only [smul_eq_mul] at this`. Establish `: (H.d : ℤ) * t.1 y z = 0` using `by linear_combination -this`. Conclude with `(mul_eq_zero.1 this).resolve_left hd`. Establish `hs : ∀ y z, s.1 y z = 0` using `fun y z => by`.

Use `e y z` as an intermediate fact. Rewrite `this` using `[et]`. Use linear arithmetic over natural numbers and integers. Simplify using `only [Prod.mk_eq_zero]`. Conclude with `⟨Subtype.ext (LinearMap.ext fun y => LinearMap.ext fun z => hs y z), Subtype.ext (LinearMap.ext fun y => LinearMap.ext fun z => ht y z)⟩`.
-/
theorem symIncl_rtPart_injective :
    Function.Injective (LinearMap.coprod (symIncl H X) (rtPart H X)) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  rintro ⟨s, t⟩ hst
  rw [LinearMap.mem_ker, LinearMap.coprod_apply] at hst
  have e : ∀ y z, s.1 y z + t.1 (H.rt • y) z = 0 := fun y z => by
    have := congrArg (fun γ : GlobalTheory.BalRank.balBil H.bar X => γ.1 y z) hst
    simpa [symIncl, rtPart, rtMul_apply, Submodule.coe_inclusion] using this
  have hd : (H.d : ℤ) ≠ 0 := by exact_mod_cast H.d_prime.ne_zero
  have et : ∀ y z, t.1 (H.rt • y) z = 0 := fun y z => by
    have a1 := e y z
    have a2 := e z y
    have a3 := s.2.1 y z
    have a4 := comp_rt_antisymm t.2.2 t.2.1 y z
    omega
  have ht : ∀ y z, t.1 y z = 0 := fun y z => by
    have := et (H.rt • y) z
    rw [rt_smul_rt_smul, map_neg, map_zsmul, LinearMap.neg_apply, LinearMap.smul_apply] at this
    simp only [smul_eq_mul] at this
    have : (H.d : ℤ) * t.1 y z = 0 := by linear_combination -this
    exact (mul_eq_zero.1 this).resolve_left hd
  have hs : ∀ y z, s.1 y z = 0 := fun y z => by
    have := e y z
    rw [et] at this
    omega
  simp only [Prod.mk_eq_zero]
  exact ⟨Subtype.ext (LinearMap.ext fun y => LinearMap.ext fun z => hs y z),
    Subtype.ext (LinearMap.ext fun y => LinearMap.ext fun z => ht y z)⟩

/- English proof (translation)
Establish `h1` using `LinearMap.finrank_le_finrank_of_injective (symPart_antiPart_injective (H := H) (X := X))`. Establish `h2` using `LinearMap.finrank_le_finrank_of_injective (symIncl_rtPart_injective (H := H) (X := X))`. Rewrite `h1`, `h2` using `[Module.finrank_prod]`. Use linear arithmetic over natural numbers and integers.
-/
theorem two_mul_finrank_balForms (H : Host E) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X]
    [Module.Finite ℤ X] :
    2 * Module.finrank ℤ (balForms H.bar X) = Module.finrank ℤ (GlobalTheory.BalRank.balBil H.bar X) := by
  have h1 := LinearMap.finrank_le_finrank_of_injective (symPart_antiPart_injective (H := H) (X := X))
  have h2 := LinearMap.finrank_le_finrank_of_injective (symIncl_rtPart_injective (H := H) (X := X))
  rw [Module.finrank_prod] at h1 h2
  omega

end GlobalTheory.BalRankSym
