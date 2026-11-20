import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.QuadraticBasis.StatementO

namespace Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis

section
variable {W O : Type} [CommRing W] [CommRing O]

def pbE (j : W →+* O) (θ w : O) (t : W × W × W × W) : O :=
  j t.1 + j t.2.1 * θ + j t.2.2.1 * w + j t.2.2.2 * θ * w

def pbM (f0 f1 ϖ : W) (t s : W × W × W × W) : W × W × W × W :=
  (t.1 * s.1 - t.2.1 * s.2.1 * f0 + ϖ * (t.2.2.1 * s.2.2.1 - t.2.2.2 * s.2.2.2 * f0),
   t.1 * s.2.1 + t.2.1 * s.1 - t.2.1 * s.2.1 * f1
     + ϖ * (t.2.2.1 * s.2.2.2 + t.2.2.2 * s.2.2.1 - t.2.2.2 * s.2.2.2 * f1),
   t.1 * s.2.2.1 - t.2.1 * s.2.2.2 * f0 + t.2.2.1 * s.1 - t.2.2.2 * s.2.1 * f0,
   t.1 * s.2.2.2 + t.2.1 * s.2.2.1 - t.2.1 * s.2.2.2 * f1 + t.2.2.1 * s.2.1 + t.2.2.2 * s.1
     - t.2.2.2 * s.2.1 * f1)

/- English proof (translation)
Simplify using `only [pbE, pbM, map_add, map_sub, map_mul]`. Take the linear combination `(j t.2.2.1 * j s.2.2.1 + (j t.2.2.1 * j s.2.2.2 + j t.2.2.2 * j s.2.2.1) * θ + j t.2.2.2 * j s.2.2.2 * θ ^ 2) * hw + (j t.2.1 * j s.2.1 + (j t.2.1 * j s.2.2.2 + j t.2.2.2 * j s.2.1) * w + j t.2.2.2 * j s.2.2.2 * j ϖ) * hθ`.
-/
theorem pbE_mul (j : W →+* O) (θ w : O) (f0 f1 ϖ : W) (hθ : θ ^ 2 + j f1 * θ + j f0 = 0)
    (hw : w ^ 2 = j ϖ) (t s : W × W × W × W) :
    pbE j θ w t * pbE j θ w s = pbE j θ w (pbM f0 f1 ϖ t s) := by
  simp only [pbE, pbM, map_add, map_sub, map_mul]
  linear_combination (j t.2.2.1 * j s.2.2.1 + (j t.2.2.1 * j s.2.2.2 + j t.2.2.2 * j s.2.2.1) * θ +
      j t.2.2.2 * j s.2.2.2 * θ ^ 2) * hw +
    (j t.2.1 * j s.2.1 + (j t.2.1 * j s.2.2.2 + j t.2.2.2 * j s.2.1) * w +
      j t.2.2.2 * j s.2.2.2 * j ϖ) * hθ

/- English proof (translation)
Simplify using `only [pbE, Prod.fst_add, Prod.snd_add, map_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pbE_add (j : W →+* O) (θ w : O) (t s : W × W × W × W) :
    pbE j θ w t + pbE j θ w s = pbE j θ w (t + s) := by
  simp only [pbE, Prod.fst_add, Prod.snd_add, map_add]
  ring

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `t s hts`. Take `⟨u, -, hu⟩` from `h (pbE j θ w t)`. Conclude with `(hu t rfl).trans (hu s hts).symm`. Introduce `x`.

Take `⟨t, ht, -⟩` from `h x`. Conclude with `⟨t, ht.symm⟩`.
-/
theorem pbE_bij {j : W →+* O} {θ w : O} (h : IsQuadBasis j θ w) : Function.Bijective (pbE j θ w) := by
  constructor
  · intro t s hts
    obtain ⟨u, -, hu⟩ := h (pbE j θ w t)
    exact (hu t rfl).trans (hu s hts).symm
  · intro x
    obtain ⟨t, ht, -⟩ := h x
    exact ⟨t, ht.symm⟩

end

def pbF {W₁ W₂ : Type} [CommRing W₁] [CommRing W₂] (φ : W₁ ≃+* W₂) (t : W₁ × W₁ × W₁ × W₁) :
    W₂ × W₂ × W₂ × W₂ :=
  (φ t.1, φ t.2.1, φ t.2.2.1, φ t.2.2.2)

/- English proof (translation)
Simplify using `[pbF, pbM]`.
-/
private theorem pbF_pbM_eq_pbM_map {W₁ W₂ : Type} [CommRing W₁] [CommRing W₂] (φ : W₁ ≃+* W₂)
    (f0 f1 ϖ : W₁) (t s : W₁ × W₁ × W₁ × W₁) :
    pbF φ (pbM f0 f1 ϖ t s) = pbM (φ f0) (φ f1) (φ ϖ) (pbF φ t) (pbF φ s) := by
  simp [pbF, pbM]

/- English proof (translation)
Simplify using `[pbF]`.
-/
private theorem pbF_add {W₁ W₂ : Type} [CommRing W₁] [CommRing W₂] (φ : W₁ ≃+* W₂)
    (t s : W₁ × W₁ × W₁ × W₁) : pbF φ (t + s) = pbF φ t + pbF φ s := by
  simp [pbF]

/- English proof (translation)
Introduce `W₁ W₂ O₁ O₂ _ _ _ _ j₁ j₂ θ₁ w₁ θ₂ w₂ f0 f1 ϖ φW hθ₁ hθ₂ hw₁ hw₂ hB₁ hB₂`. Set `e₁ : (W₁ × W₁ × W₁ × W₁) ≃ O₁` to `Equiv.ofBijective _ (pbE_bij hB₁)`. Set `e₂ : (W₂ × W₂ × W₂ × W₂) ≃ O₂` to `Equiv.ofBijective _ (pbE_bij hB₂)`. Set `eF : (W₁ × W₁ × W₁ × W₁) ≃ (W₂ × W₂ × W₂ × W₂)` to `{ toFun := pbF φW invFun := pbF φW.symm left_inv := fun t => by simp [pbF] right_inv := fun t => by simp [pbF] }`. Set `E : O₁ ≃ O₂` to `(e₁.symm.trans eF).trans e₂`.

Establish `hE : ∀ t, E (pbE j₁ θ₁ w₁ t) = pbE j₂ θ₂ w₂ (pbF φW t)`. Introduce `t`. Establish `h1 : e₁.symm (pbE j₁ θ₁ w₁ t) = t` using `e₁.symm_apply_apply t`. Simplify using `only [E, Equiv.trans_apply, h1]`. Both sides reduce to the same expression.

Establish `hsurj : ∀ x : O₁, ∃ t, x = pbE j₁ θ₁ w₁ t` using `fun x => ⟨e₁.symm x, (e₁.apply_symm_apply x).symm⟩`. Use `⟨{ E with map_mul' := ?_ map_add' := ?_ }, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x y`. Take `⟨t, rfl⟩` from `hsurj x`. Take `⟨s, rfl⟩` from `hsurj y`.

Use `show E _ = E _ * E _`. Rewrite using `[pbE_mul j₁ θ₁ w₁ f0 f1 ϖ hθ₁ hw₁, hE, hE, hE, pbF_pbM_eq_pbM_map, pbE_mul j₂ θ₂ w₂ (φW f0) (φW f1) (φW ϖ) hθ₂ hw₂]`. Introduce `x y`. Take `⟨t, rfl⟩` from `hsurj x`. Take `⟨s, rfl⟩` from `hsurj y`.

Use `show E _ = E _ + E _`. Rewrite using `[pbE_add, hE, hE, hE, pbF_add, pbE_add]`. Introduce `x`. Establish `h1` using `hE (x, 0, 0, 0)`. Rewrite `h1` using `[show pbE j₁ θ₁ w₁ (x, 0, 0, 0) = j₁ x by simp [pbE]]`.

Use `show E (j₁ x) = j₂ (φW x)`. Rewrite using `[h1]`. Simplify using `[pbE, pbF]`. Establish `h1` using `hE (0, 0, 1, 0)`. Rewrite `h1` using `[show pbE j₁ θ₁ w₁ (0, 0, 1, 0) = w₁ by simp [pbE]]`.

Use `show E w₁ = w₂`. Rewrite using `[h1]`. Simplify using `[pbE, pbF]`. Establish `h1` using `hE (0, 1, 0, 0)`. Rewrite `h1` using `[show pbE j₁ θ₁ w₁ (0, 1, 0, 0) = θ₁ by simp [pbE]]`.

Use `show E θ₁ = θ₂`. Rewrite using `[h1]`. Simplify using `[pbE, pbF]`.
-/
theorem presentationIso_holds : PresIso := by
  intro W₁ W₂ O₁ O₂ _ _ _ _ j₁ j₂ θ₁ w₁ θ₂ w₂ f0 f1 ϖ φW hθ₁ hθ₂ hw₁ hw₂ hB₁ hB₂
  let e₁ : (W₁ × W₁ × W₁ × W₁) ≃ O₁ := Equiv.ofBijective _ (pbE_bij hB₁)
  let e₂ : (W₂ × W₂ × W₂ × W₂) ≃ O₂ := Equiv.ofBijective _ (pbE_bij hB₂)
  let eF : (W₁ × W₁ × W₁ × W₁) ≃ (W₂ × W₂ × W₂ × W₂) :=
    { toFun := pbF φW
      invFun := pbF φW.symm
      left_inv := fun t => by simp [pbF]
      right_inv := fun t => by simp [pbF] }
  let E : O₁ ≃ O₂ := (e₁.symm.trans eF).trans e₂
  have hE : ∀ t, E (pbE j₁ θ₁ w₁ t) = pbE j₂ θ₂ w₂ (pbF φW t) := by
    intro t
    have h1 : e₁.symm (pbE j₁ θ₁ w₁ t) = t := e₁.symm_apply_apply t
    simp only [E, Equiv.trans_apply, h1]
    rfl
  have hsurj : ∀ x : O₁, ∃ t, x = pbE j₁ θ₁ w₁ t :=
    fun x => ⟨e₁.symm x, (e₁.apply_symm_apply x).symm⟩
  refine ⟨{ E with
    map_mul' := ?_
    map_add' := ?_ }, ?_, ?_, ?_⟩
  · intro x y
    obtain ⟨t, rfl⟩ := hsurj x
    obtain ⟨s, rfl⟩ := hsurj y
    show E _ = E _ * E _
    rw [pbE_mul j₁ θ₁ w₁ f0 f1 ϖ hθ₁ hw₁, hE, hE, hE, pbF_pbM_eq_pbM_map,
      pbE_mul j₂ θ₂ w₂ (φW f0) (φW f1) (φW ϖ) hθ₂ hw₂]
  · intro x y
    obtain ⟨t, rfl⟩ := hsurj x
    obtain ⟨s, rfl⟩ := hsurj y
    show E _ = E _ + E _
    rw [pbE_add, hE, hE, hE, pbF_add, pbE_add]
  · intro x
    have h1 := hE (x, 0, 0, 0)
    rw [show pbE j₁ θ₁ w₁ (x, 0, 0, 0) = j₁ x by simp [pbE]] at h1
    show E (j₁ x) = j₂ (φW x)
    rw [h1]
    simp [pbE, pbF]
  · have h1 := hE (0, 0, 1, 0)
    rw [show pbE j₁ θ₁ w₁ (0, 0, 1, 0) = w₁ by simp [pbE]] at h1
    show E w₁ = w₂
    rw [h1]
    simp [pbE, pbF]
  · have h1 := hE (0, 1, 0, 0)
    rw [show pbE j₁ θ₁ w₁ (0, 1, 0, 0) = θ₁ by simp [pbE]] at h1
    show E θ₁ = θ₂
    rw [h1]
    simp [pbE, pbF]

end Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis
