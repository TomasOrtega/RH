import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneHolomorphicGermPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlTwoPosRatMobiusBasicLawsStatement
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.KZ.H3.KumHom

/- English proof (translation)
The claim follows from `(GlobalTheory.T.upperHalfPlane_holomorphic_germ_properties.1 b (fun _ => 0) hb (differentiableOn_const 0)).2 h`.
-/
theorem germ_zero_of_vanish {b : ℂ → ℂ} (hb : DifferentiableOn ℂ b Hs) (h : ∀ z ∈ Hs, b z = 0) :
    (b : Mero) = 0 :=
  (GlobalTheory.T.upperHalfPlane_holomorphic_germ_properties.1 b (fun _ => 0) hb (differentiableOn_const 0)).2 h

/- English proof (translation)
Introduce `w hw`. Establish `h1` using `GlobalTheory.T.glTwoPosRatMobius_basic_laws.2.1 g g⁻¹ w hw`. Rewrite `h1` using `[mul_inv_cancel, GlobalTheory.T.glTwoPosRatMobius_basic_laws.2.2.1]`. Rewrite using `[h1]`. Conclude with `h _ (GlobalTheory.T.glTwoPosRatMobius_basic_laws.1 _ w hw)`.
-/
theorem vanish_of_comp {b : ℂ → ℂ} (g : GQ) (h : ∀ z ∈ Hs, b (mob g z) = 0) : ∀ z ∈ Hs, b z = 0 := by
  intro w hw
  have h1 := GlobalTheory.T.glTwoPosRatMobius_basic_laws.2.1 g g⁻¹ w hw
  rw [mul_inv_cancel, GlobalTheory.T.glTwoPosRatMobius_basic_laws.2.2.1] at h1
  rw [h1]
  exact h _ (GlobalTheory.T.glTwoPosRatMobius_basic_laws.1 _ w hw)

/- English proof (translation)
The claim follows from `hb.comp (GlobalTheory.T.glTwoPosRatMobius_basic_laws.2.2.2.1 g) (fun z hz => GlobalTheory.T.glTwoPosRatMobius_basic_laws.1 g z hz)`.
-/
theorem diff_comp {b : ℂ → ℂ} (hb : DifferentiableOn ℂ b Hs) (g : GQ) :
    DifferentiableOn ℂ (fun z => b (mob g z)) Hs :=
  hb.comp (GlobalTheory.T.glTwoPosRatMobius_basic_laws.2.2.2.1 g) (fun z hz => GlobalTheory.T.glTwoPosRatMobius_basic_laws.1 g z hz)

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

/- English proof (translation)
Introduce `ha`. Take `⟨hda, hdb, hb0, he⟩` from `h`. Rewrite `he` using `[germ_zero_of_vanish hda ha, zero_pow hm.ne']`. Establish `hbm : (b : Mero) ^ m = 0`. Use `congrArg (X.an ((f⁻¹ : X.Kˣ) : X.K) * ·) he` as an intermediate fact.

Simplify using `only [mul_zero, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul] at this`. Conclude with `this`. Establish `hdbm : DifferentiableOn ℂ (fun z => b z ^ m) Hs` using `hdb.pow m`. Establish `h0 : ((fun z => b z ^ m : ℂ → ℂ) : Mero) = ((fun _ => 0 : ℂ → ℂ) : Mero)` using `hbm`. Establish `hz` using `(GlobalTheory.T.upperHalfPlane_holomorphic_germ_properties.1 _ (fun _ => 0) hdbm (differentiableOn_const 0)).1 h0`.

Conclude with `hb0 (germ_zero_of_vanish hdb fun z hz' => (pow_eq_zero_iff hm.ne').1 (hz z hz'))`.
-/
theorem num_not_vanish {X : Tower Ω ε} {m : ℕ} (hm : 0 < m) {f : X.Kˣ} {a b : ℂ → ℂ} (h : IsRoot X m f a b) :
    ¬ ∀ z ∈ Hs, a z = 0 := by
  intro ha
  obtain ⟨hda, hdb, hb0, he⟩ := h
  rw [germ_zero_of_vanish hda ha, zero_pow hm.ne'] at he
  have hbm : (b : Mero) ^ m = 0 := by
    have := congrArg (X.an ((f⁻¹ : X.Kˣ) : X.K) * ·) he
    simp only [mul_zero, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul] at this
    exact this
  have hdbm : DifferentiableOn ℂ (fun z => b z ^ m) Hs := hdb.pow m
  have h0 : ((fun z => b z ^ m : ℂ → ℂ) : Mero) = ((fun _ => 0 : ℂ → ℂ) : Mero) := hbm
  have hz := (GlobalTheory.T.upperHalfPlane_holomorphic_germ_properties.1 _ (fun _ => 0) hdbm (differentiableOn_const 0)).1 h0
  exact hb0 (germ_zero_of_vanish hdb fun z hz' => (pow_eq_zero_iff hm.ne').1 (hz z hz'))

end GlobalTheory.KZ.H3.KumHom

namespace GlobalTheory.KZ.H3.KumHom

/- English proof (translation)
Rewrite `h` using `[← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int]`. Take `⟨k, hk⟩` from `h`. Establish `hm : (m : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 (NeZero.ne m)`. Establish `h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0` using `by simp [Real.pi_ne_zero, Complex.I_ne_zero]`. Establish `hc : ((u.val : ℤ) : ℂ) = ((v.val + w.val + k * m : ℤ) : ℂ)`.

Use `push_cast`. Apply `mul_left_cancel₀ h2` to reduce the goal to its premises. Clear denominators, using `at hk` for the nonvanishing conditions. Take the linear combination `(2 * (Real.pi : ℂ) * Complex.I) * hk`. Establish `hi : (u.val : ℤ) = v.val + w.val + k * m` using `Int.cast_injective hc`.

Use `congrArg (Int.cast : ℤ → ZMod m) hi` as an intermediate fact. Move the coercions through the operations in `at this`. Simplify `this` using `[ZMod.natCast_val, ZMod.cast_id', ZMod.natCast_self]`.
-/
theorem zmod_eq_of_exp {m : ℕ} [NeZero m] (u v w : ZMod m)
    (h : Complex.exp (2 * Real.pi * Complex.I * (u.val : ℂ) / (m : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I * (v.val : ℂ) / (m : ℂ)) *
        Complex.exp (2 * Real.pi * Complex.I * (w.val : ℂ) / (m : ℂ))) : u = v + w := by
  rw [← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int] at h
  obtain ⟨k, hk⟩ := h
  have hm : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne m)
  have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hc : ((u.val : ℤ) : ℂ) = ((v.val + w.val + k * m : ℤ) : ℂ) := by
    push_cast
    apply mul_left_cancel₀ h2
    field_simp at hk
    linear_combination (2 * (Real.pi : ℂ) * Complex.I) * hk
  have hi : (u.val : ℤ) = v.val + w.val + k * m := Int.cast_injective hc
  have := congrArg (Int.cast : ℤ → ZMod m) hi
  push_cast at this
  simpa [ZMod.natCast_val, ZMod.cast_id', ZMod.natCast_self] using this

/- English proof (translation)
Introduce `Ω _ _ ε X l _ n x χ hK`. Take `⟨f, a, b, M, hM, -, hr, hrel⟩` from `hK`. Use `⟨M, hM, fun δ hδ δ' hδ' => ?_⟩` and prove the remaining obligations. Establish `hpos : 0 < l ^ n` using `pow_pos (Fact.out : l.Prime).pos n`. Use `haveI : NeZero (l ^ n) := ⟨hpos.ne'⟩`.

Use `set E : ZMod (l ^ n) → ℂ := fun v => Complex.exp (2 * Real.pi * Complex.I * (v.val : ℂ) / ((l : ℂ) ^ n)) with hE`. Take `⟨hda, hdb, hb0, -⟩` from `id hr`. Use `set g := ofSL δ`. Use `set g' := ofSL δ'`. Establish `key : ∀ z ∈ Hs, ((E (χ (δ * δ')) - E (χ δ) * E (χ δ')) * a z) * (b (mob g (mob g' z)) * b (mob g' z)) = 0`.

Introduce `z hz`. Establish `h1` using `hrel (δ * δ') (Subgroup.mul_mem _ hδ hδ') z hz`. Rewrite `h1` using `[map_mul, GlobalTheory.T.glTwoPosRatMobius_basic_laws.2.1 _ _ z hz]`. Establish `h2` using `hrel δ hδ (mob g' z) (GlobalTheory.T.glTwoPosRatMobius_basic_laws.1 _ z hz)`. Establish `h3` using `hrel δ' hδ' z hz`.

Simplify using `only [hE]`. Take the linear combination `(-b (mob g' z)) * h1 + b z * h2 + Complex.exp (2 * Real.pi * Complex.I * ((χ δ).val : ℂ) / ((l : ℂ) ^ n)) * b (mob g (mob g' z)) * h3`. Establish `hA : DifferentiableOn ℂ (fun z => (E (χ (δ * δ')) - E (χ δ) * E (χ δ')) * a z) Hs` using `(differentiableOn_const _).mul hda`. Establish `hB : DifferentiableOn ℂ (fun z => b (mob g (mob g' z)) * b (mob g' z)) Hs`. Use `DifferentiableOn.mul ?_ (diff_comp hdb g')` and prove the remaining obligations.

Use `diff_comp hdb (g * g')` as an intermediate fact. Use `this.congr fun z hz => ?_` and prove the remaining obligations. Simplify using `only [GlobalTheory.T.glTwoPosRatMobius_basic_laws.2.1 g g' z hz]`. Establish `hc : E (χ (δ * δ')) - E (χ δ) * E (χ δ') = 0`. Break down `GlobalTheory.T.upperHalfPlane_holomorphic_germ_properties.2.1 _ _ hA hB key with h | h` into its components or cases.

Assume the negation of the conclusion as `hne`. Conclude with `num_not_vanish hpos hr fun z hz => (mul_eq_zero.1 (h z hz)).resolve_left hne`. It suffices to derive a contradiction. Break down `GlobalTheory.T.upperHalfPlane_holomorphic_germ_properties.2.1 _ _ (diff_comp (diff_comp hdb g) g') (diff_comp hdb g') h with h' | h'` into its components or cases. Conclude with `hb0 (germ_zero_of_vanish hdb (vanish_of_comp g (vanish_of_comp g' h')))`.

Conclude with `hb0 (germ_zero_of_vanish hdb (vanish_of_comp g' h'))`. Use `sub_eq_zero.1 hc` as an intermediate fact. Simplify using `only [hE] at this`. Conclude with `zmod_eq_of_exp _ _ _ (by exact_mod_cast this)`.
-/
theorem kum_hom : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], ∀ n : ℕ,
    ∀ (x : X.Khat l) (χ : SL(2, ℤ) → ZMod (l ^ n)), Kum X l n x χ → ∃ M : ℕ, 0 < M ∧
      ∀ δ ∈ CongruenceSubgroup.Gamma M, ∀ δ' ∈ CongruenceSubgroup.Gamma M, χ (δ * δ') = χ δ + χ δ' := by
  intro Ω _ _ ε X l _ n x χ hK
  obtain ⟨f, a, b, M, hM, -, hr, hrel⟩ := hK
  refine ⟨M, hM, fun δ hδ δ' hδ' => ?_⟩
  have hpos : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
  haveI : NeZero (l ^ n) := ⟨hpos.ne'⟩
  set E : ZMod (l ^ n) → ℂ := fun v => Complex.exp (2 * Real.pi * Complex.I * (v.val : ℂ) / ((l : ℂ) ^ n)) with hE
  obtain ⟨hda, hdb, hb0, -⟩ := id hr
  set g := ofSL δ
  set g' := ofSL δ'
  have key : ∀ z ∈ Hs, ((E (χ (δ * δ')) - E (χ δ) * E (χ δ')) * a z) * (b (mob g (mob g' z)) * b (mob g' z)) = 0 := by
    intro z hz
    have h1 := hrel (δ * δ') (Subgroup.mul_mem _ hδ hδ') z hz
    rw [map_mul, GlobalTheory.T.glTwoPosRatMobius_basic_laws.2.1 _ _ z hz] at h1
    have h2 := hrel δ hδ (mob g' z) (GlobalTheory.T.glTwoPosRatMobius_basic_laws.1 _ z hz)
    have h3 := hrel δ' hδ' z hz
    simp only [hE]
    linear_combination (-b (mob g' z)) * h1 + b z * h2 +
      Complex.exp (2 * Real.pi * Complex.I * ((χ δ).val : ℂ) / ((l : ℂ) ^ n)) * b (mob g (mob g' z)) * h3
  have hA : DifferentiableOn ℂ (fun z => (E (χ (δ * δ')) - E (χ δ) * E (χ δ')) * a z) Hs :=
    (differentiableOn_const _).mul hda
  have hB : DifferentiableOn ℂ (fun z => b (mob g (mob g' z)) * b (mob g' z)) Hs := by
    refine DifferentiableOn.mul ?_ (diff_comp hdb g')
    have := diff_comp hdb (g * g')
    refine this.congr fun z hz => ?_
    simp only [GlobalTheory.T.glTwoPosRatMobius_basic_laws.2.1 g g' z hz]
  have hc : E (χ (δ * δ')) - E (χ δ) * E (χ δ') = 0 := by
    rcases GlobalTheory.T.upperHalfPlane_holomorphic_germ_properties.2.1 _ _ hA hB key with h | h
    · by_contra hne
      exact num_not_vanish hpos hr fun z hz => (mul_eq_zero.1 (h z hz)).resolve_left hne
    · exfalso
      rcases GlobalTheory.T.upperHalfPlane_holomorphic_germ_properties.2.1 _ _ (diff_comp (diff_comp hdb g) g') (diff_comp hdb g') h with h' | h'
      · exact hb0 (germ_zero_of_vanish hdb (vanish_of_comp g (vanish_of_comp g' h')))
      · exact hb0 (germ_zero_of_vanish hdb (vanish_of_comp g' h'))
  have := sub_eq_zero.1 hc
  simp only [hE] at this
  exact zmod_eq_of_exp _ _ _ (by exact_mod_cast this)

end GlobalTheory.KZ.H3.KumHom
