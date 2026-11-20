import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ResidueOfTraceIsFiberSum

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section
variable {L : Type} [Field L] [Algebra ℂ L] (B : Subalgebra ℂ L) (e : B →ₐ[ℂ] ℂ)

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
private theorem mem_loc' {v : L} : v ∈ loc B e ↔ ∃ b : B, e b ≠ 0 ∧ (b : L) * v ∈ B := Iff.rfl

/- English proof (translation)
Establish `h1 : b' * c = b * c'` using `Subtype.ext (by`. Use `push_cast`. Rewrite using `[← h, ← h']`. Use the proof step `ring)`. Establish `h2` using `congrArg e h1`.

Rewrite `h2` using `[map_mul, map_mul]`. Rewrite using `[div_eq_div_iff hb hb']`. Take the linear combination `h2`.
-/
private theorem val_indep {v : L} (b b' c c' : B) (hb : e b ≠ 0) (hb' : e b' ≠ 0)
    (h : (b : L) * v = c) (h' : (b' : L) * v = c') : e c / e b = e c' / e b' := by
  have h1 : b' * c = b * c' := Subtype.ext (by
    push_cast
    rw [← h, ← h']
    ring)
  have h2 := congrArg e h1
  rw [map_mul, map_mul] at h2
  rw [div_eq_div_iff hb hb']
  linear_combination h2

private noncomputable def evF (w : loc B e) : ℂ :=
  e ⟨_, (Classical.choose_spec ((mem_loc' B e).1 w.2)).2⟩ / e (Classical.choose ((mem_loc' B e).1 w.2))

/- English proof (translation)
Take `⟨hb0, hc0⟩` from `Classical.choose_spec ((mem_loc' B e).1 w.2)`. Unfold `evF`. Conclude with `val_indep B e _ b _ c hb0 hb rfl h`.
-/
private theorem evF_eq (w : loc B e) (b c : B) (hb : e b ≠ 0) (h : (b : L) * w = c) :
    evF B e w = e c / e b := by
  obtain ⟨hb0, hc0⟩ := Classical.choose_spec ((mem_loc' B e).1 w.2)
  unfold evF
  exact val_indep B e _ b _ c hb0 hb rfl h

private noncomputable def evH : loc B e →ₐ[ℂ] ℂ where
  toFun := evF B e
  map_one' := by
    rw [evF_eq B e 1 1 1 (by simp) (by simp)]
    simp
  map_zero' := by
    rw [evF_eq B e 0 1 0 (by simp) (by simp)]
    simp
  map_mul' w w' := by
    obtain ⟨b, hb, h⟩ := (mem_loc' B e).1 w.2
    obtain ⟨b', hb', h'⟩ := (mem_loc' B e).1 w'.2
    rw [evF_eq B e w b ⟨_, h⟩ hb rfl, evF_eq B e w' b' ⟨_, h'⟩ hb' rfl,
      evF_eq B e (w * w') (b * b') (⟨_, h⟩ * ⟨_, h'⟩) (by simp [hb, hb'])
        (by push_cast; ring), map_mul, map_mul, mul_div_mul_comm]
  map_add' w w' := by
    obtain ⟨b, hb, h⟩ := (mem_loc' B e).1 w.2
    obtain ⟨b', hb', h'⟩ := (mem_loc' B e).1 w'.2
    rw [evF_eq B e w b ⟨_, h⟩ hb rfl, evF_eq B e w' b' ⟨_, h'⟩ hb' rfl,
      evF_eq B e (w + w') (b * b') (b' * ⟨_, h⟩ + b * ⟨_, h'⟩) (by simp [hb, hb'])
        (by push_cast; ring), map_add, map_mul, map_mul, map_mul]
    field_simp
  commutes' r := by
    rw [evF_eq B e (algebraMap ℂ _ r) 1 (algebraMap ℂ B r) (by simp) (by simp)]
    simp

/- English proof (translation)
The claim follows from `evF_eq B e w b c hb h`.
-/
private theorem evH_eq (w : loc B e) (b c : B) (hb : e b ≠ 0) (h : (b : L) * w = c) :
    evH B e w = e c / e b :=
  evF_eq B e w b c hb h

end

/- English proof (translation)
Introduce `L _ _ B e`. Use `⟨fun b hb => ⟨1, by simp, by simpa using hb⟩, ⟨evH B e, fun v c => ⟨?_, ?_⟩⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨b, hb, hbv, h1, h2⟩`. Use `⟨⟨⟨b, hb⟩, h1, hbv⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[evH_eq B e _ ⟨b, hb⟩ ⟨_, hbv⟩ h1 rfl, h2]`.

Clear the denominators using the available nonvanishing facts. Introduce and unpack `⟨h, rfl⟩`. Take `⟨b, hb, hbv⟩` from `(mem_loc' B e).1 h`. Use `⟨b, b.2, hbv, hb, ?_⟩` and prove the remaining obligations. Rewrite using `[evH_eq B e ⟨v, h⟩ b ⟨_, hbv⟩ hb rfl]`.

Clear the denominators using the available nonvanishing facts. Introduce `b`. Use `⟨1, B.one_mem, by simp, by simpa using (map_one e).symm ▸ one_ne_zero, ?_⟩` and prove the remaining obligations. Establish `h1 : (⟨1, B.one_mem⟩ : B) = 1` using `rfl`. Establish `h2 : (⟨1 * (b : L), by simp⟩ : B) = b` using `Subtype.ext (one_mul _)`.

Rewrite using `[h1, h2, map_one, one_mul]`. Introduce and unpack `v c ⟨b, hb, hbv, h1, h2⟩ hc`. Establish `h3 : e ⟨b * v, hbv⟩ ≠ 0`. Rewrite using `[h2]`. Conclude with `mul_ne_zero h1 hc`.

Establish `hv : v ≠ 0`. Introduce and unpack `rfl`. Apply `h3` to reduce the goal to its premises. Establish `: (⟨b * 0, hbv⟩ : B) = 0` using `Subtype.ext (mul_zero _)`. Rewrite using `[this, map_zero]`.

Use `⟨hv, ⟨b * v, hbv⟩, h3, ?_⟩` and prove the remaining obligations. Use `show b * v * v⁻¹ ∈ B`. Rewrite using `[mul_inv_cancel_right₀ hv]` and apply the resulting hypothesis.
-/
theorem UpperTheory.Gal.productCup_of_system.valBasic_of :
    ValBasic := by
  intro L _ _ B e
  refine ⟨fun b hb => ⟨1, by simp, by simpa using hb⟩, ⟨evH B e, fun v c => ⟨?_, ?_⟩⟩, ?_, ?_⟩
  · rintro ⟨b, hb, hbv, h1, h2⟩
    refine ⟨⟨⟨b, hb⟩, h1, hbv⟩, ?_⟩
    rw [evH_eq B e _ ⟨b, hb⟩ ⟨_, hbv⟩ h1 rfl, h2]
    field_simp
  · rintro ⟨h, rfl⟩
    obtain ⟨b, hb, hbv⟩ := (mem_loc' B e).1 h
    refine ⟨b, b.2, hbv, hb, ?_⟩
    rw [evH_eq B e ⟨v, h⟩ b ⟨_, hbv⟩ hb rfl]
    field_simp
  · intro b
    refine ⟨1, B.one_mem, by simp, by simpa using (map_one e).symm ▸ one_ne_zero, ?_⟩
    have h1 : (⟨1, B.one_mem⟩ : B) = 1 := rfl
    have h2 : (⟨1 * (b : L), by simp⟩ : B) = b := Subtype.ext (one_mul _)
    rw [h1, h2, map_one, one_mul]
  · rintro v c ⟨b, hb, hbv, h1, h2⟩ hc
    have h3 : e ⟨b * v, hbv⟩ ≠ 0 := by
      rw [h2]
      exact mul_ne_zero h1 hc
    have hv : v ≠ 0 := by
      rintro rfl
      apply h3
      have : (⟨b * 0, hbv⟩ : B) = 0 := Subtype.ext (mul_zero _)
      rw [this, map_zero]
    refine ⟨hv, ⟨b * v, hbv⟩, h3, ?_⟩
    show b * v * v⁻¹ ∈ B
    rwa [mul_inv_cancel_right₀ hv]
