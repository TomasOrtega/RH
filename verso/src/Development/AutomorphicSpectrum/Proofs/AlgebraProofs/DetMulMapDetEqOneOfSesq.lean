import Mathlib

open NumberField

namespace GlobalTheory.CompanionTheory.Ar.Flat

/- English proof (translation)
Set `b` to `Module.finBasis E V`. Set `S : Matrix _ _ E` to `Matrix.of fun i j => H (b i) (b j)`. Set `G` to `LinearMap.toMatrix b b g`. Establish `hgb : ∀ j, g (b j) = ∑ i, G i j • b i`. Introduce `j`.

Simplify using `only [G, LinearMap.toMatrix_apply]`. Conclude with `(b.sum_repr (g (b j))).symm`. Establish `hS : G.transpose * S * σ.mapMatrix G = S`. Use extensionality with `i j`. Establish `h1 : S i j = H (g (b i)) (g (b j))` using `(hg _ _).symm`.

Rewrite using `[h1, hgb, hgb]`. Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply, RingHom.mapMatrix_apply, Matrix.map_apply, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul, S, Matrix.of_apply]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm]`. Establish `hdet : S.det ≠ 0`.

Introduce `h0`. Take `⟨v, hv, hvS⟩` from `Matrix.exists_vecMul_eq_zero_iff.mpr h0`. Apply `hv` to reduce the goal to its premises. Establish `hx : ∑ i, v i • b i = 0`. Apply `hH` to reduce the goal to its premises.

Establish `: H (∑ i, v i • b i) = 0`. Apply `b.ext` to reduce the goal to its premises. Introduce `j`. Use `congrFun hvS j` as an intermediate fact. Simplify `this` using `[Matrix.vecMul, dotProduct, S, map_sum, LinearMap.sum_apply]`.

Introduce `y`. Rewrite using `[this]`. Both sides reduce to the same expression. Use function extensionality and compare the values at `i`. Conclude with `Fintype.linearIndependent_iff.mp b.linearIndependent v hx i`.

Establish `hd` using `congrArg Matrix.det hS`. Rewrite `hd` using `[Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, ← RingHom.map_det]`. Establish `hG : G.det = LinearMap.det g` using `LinearMap.det_toMatrix b g`. Rewrite `hd` using `[hG]`. Apply `mul_left_cancel₀ hdet` to reduce the goal to its premises.

Take the linear combination `hd`.
-/
theorem det_mul_map_det_eq_one_of_sesq {E : Type*} [Field E] {V : Type*} [AddCommGroup V]
    [Module E V] [FiniteDimensional E V] (σ : E →+* E) (H : V →ₗ[E] V →ₛₗ[σ] E)
    (hH : ∀ x, (∀ y, H x y = 0) → x = 0) (g : V →ₗ[E] V)
    (hg : ∀ x y, H (g x) (g y) = H x y) :
    LinearMap.det g * σ (LinearMap.det g) = 1 := by
  classical
  let b := Module.finBasis E V
  let S : Matrix _ _ E := Matrix.of fun i j => H (b i) (b j)
  let G := LinearMap.toMatrix b b g
  have hgb : ∀ j, g (b j) = ∑ i, G i j • b i := by
    intro j
    simp only [G, LinearMap.toMatrix_apply]
    exact (b.sum_repr (g (b j))).symm
  have hS : G.transpose * S * σ.mapMatrix G = S := by
    ext i j
    have h1 : S i j = H (g (b i)) (g (b j)) := (hg _ _).symm
    rw [h1, hgb, hgb]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, RingHom.mapMatrix_apply,
      Matrix.map_apply, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
      LinearMap.map_smulₛₗ, smul_eq_mul, S, Matrix.of_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [mul_comm]
  have hdet : S.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv, hvS⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h0
    apply hv
    have hx : ∑ i, v i • b i = 0 := by
      apply hH
      have : H (∑ i, v i • b i) = 0 := by
        apply b.ext
        intro j
        have := congrFun hvS j
        simpa [Matrix.vecMul, dotProduct, S, map_sum, LinearMap.sum_apply] using this
      intro y
      rw [this]; rfl
    funext i
    exact Fintype.linearIndependent_iff.mp b.linearIndependent v hx i
  have hd := congrArg Matrix.det hS
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, ← RingHom.map_det] at hd
  have hG : G.det = LinearMap.det g := LinearMap.det_toMatrix b g
  rw [hG] at hd
  apply mul_left_cancel₀ hdet
  linear_combination hd

/- English proof (translation)
Introduce `E _ _ _ V _ _ _ _ _ B hB hc g hg`. Establish `hnd` using `traceForm_nondegenerate ℚ E`. Establish `hext : ∀ u v : E, (∀ a, Algebra.trace ℚ E (u * a) = Algebra.trace ℚ E (v * a)) → u = v`. Introduce `u v huv`. Apply `((Algebra.traceForm ℚ E).toDual hnd).injective` to reduce the goal to its premises.

Use extensionality with `a`. Simplify `huv a` using `[LinearMap.BilinForm.toDual_def, Algebra.traceForm_apply]`. Establish `hex : ∀ x y : V, ∃ u : E, ∀ a, Algebra.trace ℚ E (u * a) = B (a • x) y`. Introduce `x y`. Take `⟨u, hu⟩` from `((Algebra.traceForm ℚ E).toDual hnd).surjective ((LinearMap.flip B y) ∘ₗ (LinearMap.toSpanSingleton E V x).restrictScalars ℚ)`.

Use `⟨u, fun a => ?_⟩` and prove the remaining obligations. Use `LinearMap.congr_fun hu a` as an intermediate fact. Simplify `this` using `[LinearMap.BilinForm.toDual_def, Algebra.traceForm_apply]`. Use `choose h hh using hex`. Set `σ : E →+* E` to `(IsCMField.complexConj E : E →+* E)`.

Establish `hσ : ∀ a, σ a = IsCMField.complexConj E a` using `fun _ => rfl`. Set `H : V →ₗ[E] V →ₛₗ[σ] E` to `LinearMap.mk₂'ₛₗ (RingHom.id E) σ h (fun x x' y => hext _ _ fun a => by`. Rewrite using `[add_mul, map_add, hh, hh, hh, smul_add, map_add, LinearMap.add_apply])`. Use the proof step `(fun c x y => hext _ _ fun a => by`. Rewrite using `[RingHom.id_apply, smul_eq_mul, mul_comm c, mul_assoc, hh, hh, smul_smul, mul_comm])`.

Use the proof step `(fun x y y' => hext _ _ fun a => by`. Rewrite using `[add_mul, map_add, hh, hh, hh, map_add])`. Use the proof step `(fun c x y => hext _ _ fun a => by`. Rewrite using `[smul_eq_mul, mul_comm (σ c), mul_assoc, hh, hh, mul_smul, hc (σ c), hσ, IsCMField.complexConj_apply_apply])`. Establish `hH : ∀ x y, H x y = h x y` using `fun _ _ => rfl`.

Use `det_mul_map_det_eq_one_of_sesq σ H (fun x hx => hB x fun y => ?_) g (fun x y => ?_)` and prove the remaining obligations. Use `hh x y 1` as an intermediate fact. Rewrite `this` using `[← hH, hx, zero_mul, map_zero, one_smul]`. Conclude with `this.symm`. Rewrite using `[hH, hH]`.

Use `hext _ _ fun a => ?_` and prove the remaining obligations. Rewrite using `[hh, hh, ← map_smul, hg]`.
-/
theorem det_mul_complexConj_det_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (V : Type) [AddCommGroup V] [Module E V] [Module ℚ V] [IsScalarTower ℚ E V] [FiniteDimensional E V] (B : LinearMap.BilinForm ℚ V), (∀ x, (∀ y, B x y = 0) → x = 0) → (∀ (a : E) x y, B (a • x) y = B x (IsCMField.complexConj E a • y)) → ∀ g : V →ₗ[E] V, (∀ x y, B (g x) (g y) = B x y) → LinearMap.det g * IsCMField.complexConj E (LinearMap.det g) = 1 := by
  intro E _ _ _ V _ _ _ _ _ B hB hc g hg
  have hnd := traceForm_nondegenerate ℚ E
  have hext : ∀ u v : E, (∀ a, Algebra.trace ℚ E (u * a) = Algebra.trace ℚ E (v * a)) → u = v := by
    intro u v huv
    apply ((Algebra.traceForm ℚ E).toDual hnd).injective
    ext a
    simpa [LinearMap.BilinForm.toDual_def, Algebra.traceForm_apply] using huv a
  have hex : ∀ x y : V, ∃ u : E, ∀ a, Algebra.trace ℚ E (u * a) = B (a • x) y := by
    intro x y
    obtain ⟨u, hu⟩ := ((Algebra.traceForm ℚ E).toDual hnd).surjective
      ((LinearMap.flip B y) ∘ₗ (LinearMap.toSpanSingleton E V x).restrictScalars ℚ)
    refine ⟨u, fun a => ?_⟩
    have := LinearMap.congr_fun hu a
    simpa [LinearMap.BilinForm.toDual_def, Algebra.traceForm_apply] using this
  choose h hh using hex
  let σ : E →+* E := (IsCMField.complexConj E : E →+* E)
  have hσ : ∀ a, σ a = IsCMField.complexConj E a := fun _ => rfl
  let H : V →ₗ[E] V →ₛₗ[σ] E := LinearMap.mk₂'ₛₗ (RingHom.id E) σ h
    (fun x x' y => hext _ _ fun a => by
      rw [add_mul, map_add, hh, hh, hh, smul_add, map_add, LinearMap.add_apply])
    (fun c x y => hext _ _ fun a => by
      rw [RingHom.id_apply, smul_eq_mul, mul_comm c, mul_assoc, hh, hh, smul_smul, mul_comm])
    (fun x y y' => hext _ _ fun a => by
      rw [add_mul, map_add, hh, hh, hh, map_add])
    (fun c x y => hext _ _ fun a => by
      rw [smul_eq_mul, mul_comm (σ c), mul_assoc, hh, hh, mul_smul, hc (σ c), hσ,
        IsCMField.complexConj_apply_apply])
  have hH : ∀ x y, H x y = h x y := fun _ _ => rfl
  refine det_mul_map_det_eq_one_of_sesq σ H (fun x hx => hB x fun y => ?_) g (fun x y => ?_)
  · have := hh x y 1
    rw [← hH, hx, zero_mul, map_zero, one_smul] at this
    exact this.symm
  · rw [hH, hH]
    refine hext _ _ fun a => ?_
    rw [hh, hh, ← map_smul, hg]

end GlobalTheory.CompanionTheory.Ar.Flat
