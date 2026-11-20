import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerUnitClassModPrimePowPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneHolomorphicGermPropertiesStatement

noncomputable section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.KZ.H3.KumAdd

/- English proof (translation)
Rewrite `hδ`, the goal using `[CongruenceSubgroup.Gamma_mem]`. Take `⟨h1, h2, h3, h4⟩` from `hδ`. Establish `e : ∀ x : ℤ, ZMod.castHom h (ZMod M) (x : ZMod N) = (x : ZMod M)` using `fun x => map_intCast _ x`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← e, h1, map_one]`.

Rewrite using `[← e, h2, map_zero]`. Rewrite using `[← e, h3, map_zero]`. Rewrite using `[← e, h4, map_one]`.
-/
theorem gamma_of_dvd {M N : ℕ} (h : M ∣ N) {δ : SL(2, ℤ)} (hδ : δ ∈ CongruenceSubgroup.Gamma N) :
    δ ∈ CongruenceSubgroup.Gamma M := by
  rw [CongruenceSubgroup.Gamma_mem] at hδ ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hδ
  have e : ∀ x : ℤ, ZMod.castHom h (ZMod M) (x : ZMod N) = (x : ZMod M) := fun x => map_intCast _ x
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← e, h1, map_one]
  · rw [← e, h2, map_zero]
  · rw [← e, h3, map_zero]
  · rw [← e, h4, map_one]

/- English proof (translation)
Establish `hm : (m : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 (NeZero.ne m)`. Establish `hs` using `Nat.mod_add_div (x.val + y.val) m`. Rewrite using `[ZMod.val_add, ← Complex.exp_add]`. Establish `key : 2 * Real.pi * Complex.I * (x.val : ℂ) / (m : ℂ) + 2 * Real.pi * Complex.I * (y.val : ℂ) / (m : ℂ) = 2 * Real.pi * Complex.I * (((x.val + y.val) % m : ℕ) : ℂ) / (m : ℂ) + (((x.val + y.val) / m : ℕ) : ℂ) * (2 * Real.pi * Complex.I)`. Establish `hc : (((x.val + y.val) % m : ℕ) : ℂ) + (m : ℂ) * (((x.val + y.val) / m : ℕ) : ℂ) = (x.val : ℂ) + (y.val : ℂ)`.

Conclude with `hs` after adjusting the coercions. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[key, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]`.
-/
theorem exp_val_add {m : ℕ} [NeZero m] (x y : ZMod m) :
    Complex.exp (2 * Real.pi * Complex.I * (((x + y).val : ℕ) : ℂ) / (m : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I * ((x.val : ℕ) : ℂ) / (m : ℂ)) *
        Complex.exp (2 * Real.pi * Complex.I * ((y.val : ℕ) : ℂ) / (m : ℂ)) := by
  have hm : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne m)
  have hs := Nat.mod_add_div (x.val + y.val) m
  rw [ZMod.val_add, ← Complex.exp_add]
  have key : 2 * Real.pi * Complex.I * (x.val : ℂ) / (m : ℂ) + 2 * Real.pi * Complex.I * (y.val : ℂ) / (m : ℂ) =
      2 * Real.pi * Complex.I * (((x.val + y.val) % m : ℕ) : ℂ) / (m : ℂ) +
        (((x.val + y.val) / m : ℕ) : ℂ) * (2 * Real.pi * Complex.I) := by
    have hc : (((x.val + y.val) % m : ℕ) : ℂ) + (m : ℂ) * (((x.val + y.val) / m : ℕ) : ℂ) = (x.val : ℂ) + (y.val : ℂ) := by
      exact_mod_cast hs
    calc 2 * Real.pi * Complex.I * (x.val : ℂ) / (m : ℂ) + 2 * Real.pi * Complex.I * (y.val : ℂ) / (m : ℂ)
        = 2 * Real.pi * Complex.I * ((x.val : ℂ) + (y.val : ℂ)) / (m : ℂ) := by ring
      _ = 2 * Real.pi * Complex.I * ((((x.val + y.val) % m : ℕ) : ℂ) + (m : ℂ) * (((x.val + y.val) / m : ℕ) : ℂ)) /
            (m : ℂ) := by rw [hc]
      _ = _ := by field_simp <;> ring
  rw [key, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]

instance neZero_pow (l n : ℕ) [Fact l.Prime] : NeZero (l ^ n) :=
  ⟨pow_ne_zero n (Fact.out : l.Prime).ne_zero⟩

end GlobalTheory.KZ.H3.KumAdd

namespace GlobalTheory.KZ.H3.KumAdd

/- English proof (translation)
Use `exp_val_add (m := l ^ n) x y` as an intermediate fact. Move the coercions through the operations in `at this`. Conclude with `this`.
-/
theorem exp_val_add_pow (l n : ℕ) [Fact l.Prime] (x y : ZMod (l ^ n)) :
    Complex.exp (2 * Real.pi * Complex.I * (((x + y).val : ℕ) : ℂ) / ((l : ℂ) ^ n)) =
      Complex.exp (2 * Real.pi * Complex.I * ((x.val : ℕ) : ℂ) / ((l : ℂ) ^ n)) *
        Complex.exp (2 * Real.pi * Complex.I * ((y.val : ℕ) : ℂ) / ((l : ℂ) ^ n)) := by
  have := exp_val_add (m := l ^ n) x y
  push_cast at this
  exact this

/- English proof (translation)
Introduce `H`. Establish `h0 : DifferentiableOn ℂ (fun _ => (0 : ℂ)) Hs` using `differentiableOn_const 0`. Establish `e` using `(GlobalTheory.T.upperHalfPlane_holomorphic_germ_properties.1 (b * b') (fun _ => 0) (hb.mul hb') h0).1 (by rw [H]; rfl)`. Break down `GlobalTheory.T.upperHalfPlane_holomorphic_germ_properties.2.1 b b' hb hb' (fun z hz => by simpa using e z hz) with h1 | h1` into its components or cases. Conclude with `h (by rw [(GlobalTheory.T.upperHalfPlane_holomorphic_germ_properties.1 b (fun _ => 0) hb h0).2 h1]; rfl)`.

Conclude with `h' (by rw [(GlobalTheory.T.upperHalfPlane_holomorphic_germ_properties.1 b' (fun _ => 0) hb' h0).2 h1]; rfl)`.
-/
theorem germ_mul_ne_zero {b b' : ℂ → ℂ} (hb : DifferentiableOn ℂ b Hs) (hb' : DifferentiableOn ℂ b' Hs)
    (h : (b : Mero) ≠ 0) (h' : (b' : Mero) ≠ 0) : ((b * b' : ℂ → ℂ) : Mero) ≠ 0 := by
  intro H
  have h0 : DifferentiableOn ℂ (fun _ => (0 : ℂ)) Hs := differentiableOn_const 0
  have e := (GlobalTheory.T.upperHalfPlane_holomorphic_germ_properties.1 (b * b') (fun _ => 0) (hb.mul hb') h0).1 (by rw [H]; rfl)
  rcases GlobalTheory.T.upperHalfPlane_holomorphic_germ_properties.2.1 b b' hb hb' (fun z hz => by simpa using e z hz) with h1 | h1
  · exact h (by rw [(GlobalTheory.T.upperHalfPlane_holomorphic_germ_properties.1 b (fun _ => 0) hb h0).2 h1]; rfl)
  · exact h' (by rw [(GlobalTheory.T.upperHalfPlane_holomorphic_germ_properties.1 b' (fun _ => 0) hb' h0).2 h1]; rfl)

/- English proof (translation)
Introduce `Ω _ _ ε X l _ n`. Establish `C` using `GlobalTheory.T.towerUnitClassModPrimePow_properties Ω ε X l n`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `x x' χ χ' ⟨f, a, b, M, hM, hx, ⟨ha, hb, hb0, hr⟩, hδ⟩ ⟨f', a', b', M', hM', hx', ⟨ha', hb', hb0', hr'⟩, hδ'⟩`. Use `⟨f * f', a * a', b * b', M * M', Nat.mul_pos hM hM', ?_, ⟨ha.mul ha', hb.mul hb', germ_mul_ne_zero hb hb' hb0 hb0', ?_⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_add, hx, hx', C.2.2.1]`. Rewrite using `[Units.val_mul, map_mul, Filter.Germ.coe_mul, Filter.Germ.coe_mul, mul_pow, mul_pow, ← hr, ← hr']`. Expand and normalize the polynomial expressions, which then agree. Introduce `δ hδM z hz`. Establish `e1` using `hδ δ (gamma_of_dvd (dvd_mul_right M M') hδM) z hz`.

Establish `e2` using `hδ' δ (gamma_of_dvd (dvd_mul_left M' M) hδM) z hz`. Simplify using `only [Pi.mul_apply, Pi.add_apply]`. Rewrite using `[exp_val_add_pow]`. Take the linear combination `(a' (mob (ofSL δ) z) * b' z) * e1 + (Complex.exp (2 * Real.pi * Complex.I * (((χ δ).val : ℕ) : ℂ) / ((l : ℂ) ^ n)) * (a z * b (mob (ofSL δ) z))) * e2`. Use `⟨1, fun _ => 1, fun _ => 1, 1, one_pos, ?_, isRoot_one X _ ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_zero, C.2.2.2.1]`. Introduce `H`. Use `(GlobalTheory.T.upperHalfPlane_holomorphic_germ_properties.1 (fun _ => (1 : ℂ)) (fun _ => 0) (differentiableOn_const 1) (differentiableOn_const 0)).1 (by rw [H]; rfl) Complex.I (by simp [Hs])` as an intermediate fact. Simplify using `at this`. Introduce `δ _ z _`.

Simplify using the standard rewrite rules. Introduce and unpack `x χ χ' ⟨f, a, b, M, hM, hx, hr, hδ⟩ ⟨M', hM', hN⟩`. Use `⟨f, a, b, M * M', Nat.mul_pos hM hM', hx, hr, fun δ hδM z hz => ?_⟩` and prove the remaining obligations. Rewrite using `[← hN δ (gamma_of_dvd (dvd_mul_left M' M) hδM)]`. Conclude with `hδ δ (gamma_of_dvd (dvd_mul_right M M') hδM) z hz`.
-/
theorem kum_add_zero_near : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime],
    ∀ n : ℕ, (∀ (x x' : X.Khat l) (χ χ' : SL(2, ℤ) → ZMod (l ^ n)), Kum X l n x χ → Kum X l n x' χ' →
      Kum X l n (x + x') (χ + χ')) ∧ Kum X l n 0 0 ∧
      (∀ (x : X.Khat l) (χ χ' : SL(2, ℤ) → ZMod (l ^ n)), Kum X l n x χ → Near χ χ' → Kum X l n x χ') := by
  intro Ω _ _ ε X l _ n
  have C := GlobalTheory.T.towerUnitClassModPrimePow_properties Ω ε X l n
  refine ⟨?_, ?_, ?_⟩
  · rintro x x' χ χ' ⟨f, a, b, M, hM, hx, ⟨ha, hb, hb0, hr⟩, hδ⟩ ⟨f', a', b', M', hM', hx', ⟨ha', hb', hb0', hr'⟩, hδ'⟩
    refine ⟨f * f', a * a', b * b', M * M', Nat.mul_pos hM hM', ?_,
      ⟨ha.mul ha', hb.mul hb', germ_mul_ne_zero hb hb' hb0 hb0', ?_⟩, ?_⟩
    · rw [map_add, hx, hx', C.2.2.1]
    · rw [Units.val_mul, map_mul, Filter.Germ.coe_mul, Filter.Germ.coe_mul, mul_pow, mul_pow, ← hr, ← hr']
      ring
    · intro δ hδM z hz
      have e1 := hδ δ (gamma_of_dvd (dvd_mul_right M M') hδM) z hz
      have e2 := hδ' δ (gamma_of_dvd (dvd_mul_left M' M) hδM) z hz
      simp only [Pi.mul_apply, Pi.add_apply]
      rw [exp_val_add_pow]
      linear_combination (a' (mob (ofSL δ) z) * b' z) * e1 +
        (Complex.exp (2 * Real.pi * Complex.I * (((χ δ).val : ℕ) : ℂ) / ((l : ℂ) ^ n)) *
          (a z * b (mob (ofSL δ) z))) * e2
  · refine ⟨1, fun _ => 1, fun _ => 1, 1, one_pos, ?_, isRoot_one X _ ?_, ?_⟩
    · rw [map_zero, C.2.2.2.1]
    · intro H
      have := (GlobalTheory.T.upperHalfPlane_holomorphic_germ_properties.1 (fun _ => (1 : ℂ)) (fun _ => 0) (differentiableOn_const 1)
        (differentiableOn_const 0)).1 (by rw [H]; rfl) Complex.I (by simp [Hs])
      simp at this
    · intro δ _ z _
      simp
  · rintro x χ χ' ⟨f, a, b, M, hM, hx, hr, hδ⟩ ⟨M', hM', hN⟩
    refine ⟨f, a, b, M * M', Nat.mul_pos hM hM', hx, hr, fun δ hδM z hz => ?_⟩
    rw [← hN δ (gamma_of_dvd (dvd_mul_left M' M) hδM)]
    exact hδ δ (gamma_of_dvd (dvd_mul_right M M') hδM) z hz

end GlobalTheory.KZ.H3.KumAdd
