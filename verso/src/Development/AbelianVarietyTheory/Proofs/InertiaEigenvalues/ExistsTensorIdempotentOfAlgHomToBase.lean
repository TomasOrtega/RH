import Mathlib
open NumberField IsDedekindDomain TensorProduct Polynomial

namespace GlobalTheory

/- English proof (translation)
Use `set A := K ⊗[E] E'`. Set `pb` to `Field.powerBasisOfFiniteOfSeparable E E'`. Use `set θ := pb.gen`. Set `T : A` to `Algebra.TensorProduct.includeRight θ`. Use `set α : K := ψ T`.

Set `f : E[X]` to `minpoly E θ`. Set `fK : K[X]` to `f.map (algebraMap E K)`. Establish `hfT : aeval T fK = 0`. Rewrite using `[aeval_map_algebraMap]`. Establish `: aeval T f = Algebra.TensorProduct.includeRight (aeval θ f)`.

Rewrite using `[aeval_algHom_apply]`. Rewrite using `[this, minpoly.aeval, map_zero]`. Establish `hroot : IsRoot fK α`. Establish `h1 : aeval α fK = ψ (aeval T fK)`. Rewrite using `[aeval_algHom_apply]`.

Rewrite `h1` using `[hfT, map_zero]`. Simplify `h1` using `[IsRoot, aeval_def, eval₂_eq_eval_map]`. Establish `hsep : fK.Separable` using `Polynomial.Separable.map (p := f) (Algebra.IsSeparable.isSeparable E θ)`. Use `set g : K[X] := fK /ₘ (X - C α)`. Establish `hfac : (X - C α) * g = fK` using `(mul_divByMonic_eq_iff_isRoot).2 hroot`.

Establish `hgα : g.eval α ≠ 0`. Establish `hd` using `hsep.eval₂_derivative_ne_zero (RingHom.id K) (x := α) (by simpa [eval₂_id] using hroot)`. Rewrite `hd` using `[eval₂_id, ← hfac]`. Simplify `hd` using `[derivative_mul]`. Set `e : A` to `algebraMap K A (g.eval α)⁻¹ * aeval T g`.

Establish `hψg : ψ (aeval T g) = g.eval α`. Rewrite using `[← aeval_algHom_apply]`. Both sides reduce to the same expression. Establish `hψe : ψ e = 1`. Establish `hc : ψ (algebraMap K A (g.eval α)⁻¹) = (g.eval α)⁻¹` using `ψ.commutes _`.

Simplify using `only [e, map_mul, hc, hψg]`. Conclude with `inv_mul_cancel₀ hgα`. Establish `hTe : e * T = algebraMap K A (ψ T) * e`. Establish `h0 : (T - algebraMap K A α) * aeval T g = 0`. Establish `: aeval T ((X - C α) * g) = (T - algebraMap K A α) * aeval T g`.

Simplify using `[map_mul, map_sub]`. Rewrite using `[← this, hfac, hfT]`. Establish `h1 : T * aeval T g = algebraMap K A α * aeval T g`. Rewrite `h0` using `[sub_mul]`. Conclude with `sub_eq_zero.1 h0`.

Simplify using `only [e]`. Combine the equalities or inequalities in the displayed calculation. Set `Q : A → Prop` to `fun a => e * a = algebraMap K A (ψ a) * e`. Establish `Qmul : ∀ a b, Q a → Q b → Q (a * b)`. Introduce `a b ha hb`.

Use `show e * (a * b) = algebraMap K A (ψ (a * b)) * e`. Rewrite using `[map_mul, map_mul, ← mul_assoc, ha, mul_assoc, hb]`. Expand and normalize the polynomial expressions, which then agree. Establish `Qadd : ∀ a b, Q a → Q b → Q (a + b)`. Introduce `a b ha hb`.

Use `show e * (a + b) = algebraMap K A (ψ (a + b)) * e`. Rewrite using `[map_add, map_add, mul_add, ha, hb, add_mul]`. Establish `Qalg : ∀ k : K, Q (algebraMap K A k)`. Introduce `k`. Use `show e * algebraMap K A k = algebraMap K A (ψ (algebraMap K A k)) * e`.

Rewrite using `[AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, mul_comm]`. Establish `Qright : ∀ x : E', Q (Algebra.TensorProduct.includeRight x)`. Introduce `x`. Establish `hx : x ∈ Algebra.adjoin E ({θ} : Set E')` using `by rw [pb.adjoin_gen_eq_top]; trivial`. Proceed by induction on `hx using Algebra.adjoin_induction with`.

Consider the case `mem y hy`. Rewrite using `[Set.mem_singleton_iff.1 hy]`. Conclude with `hTe`. Consider the case `algebraMap r`. Establish `: (Algebra.TensorProduct.includeRight (algebraMap E E' r) : A) = algebraMap K A (algebraMap E K r)`.

Rewrite using `[AlgHom.commutes, IsScalarTower.algebraMap_apply E K A]`. Rewrite using `[this]`. Conclude with `Qalg _`. Consider the case `add y z _ _ hy hz => rw [map_add]`. Conclude with `Qadd _ _ hy hz`.

Consider the case `mul y z _ _ hy hz => rw [map_mul]`. Conclude with `Qmul _ _ hy hz`. Use `⟨e, hψe, fun a => ?_⟩` and prove the remaining obligations. Proceed by induction on `a using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul k x`. Establish `: (k ⊗ₜ[E] x : A) = algebraMap K A k * Algebra.TensorProduct.includeRight x`. Rewrite using `[Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, Algebra.algebraMap_self, RingHom.id_apply, one_mul]`. Rewrite using `[this]`. Conclude with `Qmul _ _ (Qalg k) (Qright x)`.

Consider the case `add a b ha hb => exact Qadd _ _ ha hb`.
-/
theorem exists_tensor_idem_of_algHom (E K E' : Type) [Field E] [CharZero E] [Field K] [Field E']
    [Algebra E K] [Algebra E E'] [FiniteDimensional E E'] (ψ : K ⊗[E] E' →ₐ[K] K) :
    ∃ e : K ⊗[E] E', ψ e = 1 ∧ ∀ a, e * a = algebraMap K (K ⊗[E] E') (ψ a) * e := by
  classical
  set A := K ⊗[E] E'
  let pb := Field.powerBasisOfFiniteOfSeparable E E'
  set θ := pb.gen
  let T : A := Algebra.TensorProduct.includeRight θ
  set α : K := ψ T
  let f : E[X] := minpoly E θ
  let fK : K[X] := f.map (algebraMap E K)
  have hfT : aeval T fK = 0 := by
    rw [aeval_map_algebraMap]
    have : aeval T f = Algebra.TensorProduct.includeRight (aeval θ f) := by
      rw [aeval_algHom_apply]
    rw [this, minpoly.aeval, map_zero]
  have hroot : IsRoot fK α := by
    have h1 : aeval α fK = ψ (aeval T fK) := by
      rw [aeval_algHom_apply]
    rw [hfT, map_zero] at h1
    simpa [IsRoot, aeval_def, eval₂_eq_eval_map] using h1
  have hsep : fK.Separable := Polynomial.Separable.map (p := f) (Algebra.IsSeparable.isSeparable E θ)
  set g : K[X] := fK /ₘ (X - C α)
  have hfac : (X - C α) * g = fK := (mul_divByMonic_eq_iff_isRoot).2 hroot
  have hgα : g.eval α ≠ 0 := by
    have hd := hsep.eval₂_derivative_ne_zero (RingHom.id K) (x := α) (by simpa [eval₂_id] using hroot)
    rw [eval₂_id, ← hfac] at hd
    simpa [derivative_mul] using hd
  let e : A := algebraMap K A (g.eval α)⁻¹ * aeval T g
  have hψg : ψ (aeval T g) = g.eval α := by
    rw [← aeval_algHom_apply]; rfl
  have hψe : ψ e = 1 := by
    have hc : ψ (algebraMap K A (g.eval α)⁻¹) = (g.eval α)⁻¹ := ψ.commutes _
    simp only [e, map_mul, hc, hψg]
    exact inv_mul_cancel₀ hgα
  have hTe : e * T = algebraMap K A (ψ T) * e := by
    have h0 : (T - algebraMap K A α) * aeval T g = 0 := by
      have : aeval T ((X - C α) * g) = (T - algebraMap K A α) * aeval T g := by
        simp [map_mul, map_sub]
      rw [← this, hfac, hfT]
    have h1 : T * aeval T g = algebraMap K A α * aeval T g := by
      rw [sub_mul] at h0; exact sub_eq_zero.1 h0
    simp only [e]
    calc algebraMap K A (g.eval α)⁻¹ * aeval T g * T
        = algebraMap K A (g.eval α)⁻¹ * (T * aeval T g) := by ring
      _ = algebraMap K A α * (algebraMap K A (g.eval α)⁻¹ * aeval T g) := by rw [h1]; ring

  let Q : A → Prop := fun a => e * a = algebraMap K A (ψ a) * e
  have Qmul : ∀ a b, Q a → Q b → Q (a * b) := by
    intro a b ha hb
    show e * (a * b) = algebraMap K A (ψ (a * b)) * e
    rw [map_mul, map_mul, ← mul_assoc, ha, mul_assoc, hb]; ring
  have Qadd : ∀ a b, Q a → Q b → Q (a + b) := by
    intro a b ha hb
    show e * (a + b) = algebraMap K A (ψ (a + b)) * e
    rw [map_add, map_add, mul_add, ha, hb, add_mul]
  have Qalg : ∀ k : K, Q (algebraMap K A k) := by
    intro k
    show e * algebraMap K A k = algebraMap K A (ψ (algebraMap K A k)) * e
    rw [AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, mul_comm]
  have Qright : ∀ x : E', Q (Algebra.TensorProduct.includeRight x) := by
    intro x
    have hx : x ∈ Algebra.adjoin E ({θ} : Set E') := by rw [pb.adjoin_gen_eq_top]; trivial
    induction hx using Algebra.adjoin_induction with
    | mem y hy =>
      rw [Set.mem_singleton_iff.1 hy]; exact hTe
    | algebraMap r =>
      have : (Algebra.TensorProduct.includeRight (algebraMap E E' r) : A)
          = algebraMap K A (algebraMap E K r) := by
        rw [AlgHom.commutes, IsScalarTower.algebraMap_apply E K A]
      rw [this]; exact Qalg _
    | add y z _ _ hy hz => rw [map_add]; exact Qadd _ _ hy hz
    | mul y z _ _ hy hz => rw [map_mul]; exact Qmul _ _ hy hz
  refine ⟨e, hψe, fun a => ?_⟩
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul k x =>
    have : (k ⊗ₜ[E] x : A) = algebraMap K A k * Algebra.TensorProduct.includeRight x := by
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.includeRight_apply,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, Algebra.algebraMap_self, RingHom.id_apply, one_mul]
    rw [this]; exact Qmul _ _ (Qalg k) (Qright x)
  | add a b ha hb => exact Qadd _ _ ha hb

end GlobalTheory
