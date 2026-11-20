import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SameBlockOfPosC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverUpqClosureExpTopAndCartanStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfFactorialBoundStatement

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

namespace GlobalTheory.FockTensor

/- English proof (translation)
Take `⟨C, ρ, hC, hρ, hk⟩` from `hb Y hY y`. Use `set A := D.HK.act Y with hA`. Establish `hpow : ∀ k : ℕ, (A ^ (k + 1)) y = A ((A ^ k) y)` using `fun k => by`. Rewrite using `[pow_succ', Module.End.mul_apply]`. Set `g : ℕ → ℝ → πU.H` to `fun k s => πU.π (T.expt (s • Y)) (E ((A ^ k) y)) - J (D.U.π (T.expt (s • Y)) (D.ι ((A ^ k) y)))`.

Establish `key : ∀ k s, g k s = 0`. Use `GlobalTheory.T.eq_zero_of_factorial_bound_of_vanish_at_zero πU.H g (2 * C) ρ (by linarith) hρ ?_ ?_ ?_` and prove the remaining obligations. Introduce `k s`. Establish `h1` using `hasDerivAt_orbit πU hY (hder Y hY ((A ^ k) y)) s`. Establish `h2` using `hasDerivAt_orbit D.U hY (D.11 Y hY ((A ^ k) y)) s`.

Establish `h3` using `(J.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s h2`. Establish `h4` using `h1.sub h3`. Establish `hsucc : g (k + 1) s = πU.π (T.expt (s • Y)) (E (A ((A ^ k) y))) - J (D.U.π (T.expt (s • Y)) (D.ι (A ((A ^ k) y))))`. Simplify using `only [g, hpow]`. Rewrite using `[hsucc]`.

Conclude with `h4`. Introduce `k s`. Establish `e1 : ‖πU.π (T.expt (s • Y)) (E ((A ^ k) y))‖ = ‖D.ι ((A ^ k) y)‖`. Rewrite using `[πU.6, hn]`. Establish `e2 : ‖J (D.U.π (T.expt (s • Y)) (D.ι ((A ^ k) y)))‖ = ‖D.ι ((A ^ k) y)‖`.

Rewrite using `[hJn, D.U.6]`. Combine the equalities or inequalities in the displayed calculation. Introduce `k`. Simplify using `only [g, zero_smul, T.expt_zero, map_one, ContinuousLinearMap.one_apply, hJ, sub_self]`. Establish `h0` using `key 0 t`.

Simplify using `only [g, pow_zero, Module.End.one_apply] at h0`. Conclude with `(sub_eq_zero.mp h0).symm`.
-/
private theorem J_pi_expt_iota_eq {p q : ℕ} {T : GrpData p q} (D : DSRep T) (πU : URep T)
    (E : D.HK.V →ₗ[ℂ] πU.H) (J : D.U.H →L[ℂ] πU.H) (hJ : ∀ y, J (D.ι y) = E y)
    (hder : ∀ Y ∈ upq p q, ∀ y, HasDerivAt (fun t : ℝ => πU.π (T.expt (t • Y)) (E y))
      (E (D.HK.act Y y)) 0)
    (hn : ∀ y, ‖E y‖ = ‖D.ι y‖) (hJn : ∀ x, ‖J x‖ = ‖x‖)
    (hb : ∀ Y ∈ upq p q, ∀ y, ∃ C ρ : ℝ, 0 ≤ C ∧ 0 < ρ ∧
      ∀ k : ℕ, ‖D.ι ((D.HK.act Y ^ k) y)‖ ≤ C * ρ ^ k * (k.factorial : ℝ))
    {Y : Mat p q} (hY : Y ∈ upq p q) (y : D.HK.V) (t : ℝ) :
    J (D.U.π (T.expt (t • Y)) (D.ι y)) = πU.π (T.expt (t • Y)) (E y) := by
  obtain ⟨C, ρ, hC, hρ, hk⟩ := hb Y hY y
  set A := D.HK.act Y with hA
  have hpow : ∀ k : ℕ, (A ^ (k + 1)) y = A ((A ^ k) y) := fun k => by
    rw [pow_succ', Module.End.mul_apply]
  let g : ℕ → ℝ → πU.H := fun k s =>
    πU.π (T.expt (s • Y)) (E ((A ^ k) y)) - J (D.U.π (T.expt (s • Y)) (D.ι ((A ^ k) y)))
  have key : ∀ k s, g k s = 0 := by
    refine GlobalTheory.T.eq_zero_of_factorial_bound_of_vanish_at_zero πU.H g (2 * C) ρ (by linarith) hρ ?_ ?_ ?_
    · intro k s
      have h1 := hasDerivAt_orbit πU hY (hder Y hY ((A ^ k) y)) s
      have h2 := hasDerivAt_orbit D.U hY (D.11 Y hY ((A ^ k) y)) s
      have h3 := (J.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s h2
      have h4 := h1.sub h3
      have hsucc : g (k + 1) s = πU.π (T.expt (s • Y)) (E (A ((A ^ k) y))) -
          J (D.U.π (T.expt (s • Y)) (D.ι (A ((A ^ k) y)))) := by
        simp only [g, hpow]
      rw [hsucc]
      exact h4
    · intro k s
      have e1 : ‖πU.π (T.expt (s • Y)) (E ((A ^ k) y))‖ = ‖D.ι ((A ^ k) y)‖ := by
        rw [πU.6, hn]
      have e2 : ‖J (D.U.π (T.expt (s • Y)) (D.ι ((A ^ k) y)))‖ = ‖D.ι ((A ^ k) y)‖ := by
        rw [hJn, D.U.6]
      calc ‖g k s‖ ≤ ‖πU.π (T.expt (s • Y)) (E ((A ^ k) y))‖ +
            ‖J (D.U.π (T.expt (s • Y)) (D.ι ((A ^ k) y)))‖ := norm_sub_le _ _
        _ = 2 * ‖D.ι ((A ^ k) y)‖ := by rw [e1, e2]; ring
        _ ≤ 2 * (C * ρ ^ k * (k.factorial : ℝ)) := by gcongr; exact hk k
        _ = 2 * C * ρ ^ k * (k.factorial : ℝ) := by ring
    · intro k
      simp only [g, zero_smul, T.expt_zero, map_one, ContinuousLinearMap.one_apply, hJ, sub_self]
  have h0 := key 0 t
  simp only [g, pow_zero, Module.End.one_apply] at h0
  exact (sub_eq_zero.mp h0).symm

/- English proof (translation)
Introduce `p q hpq T D πU E hd hn hder hb`. Set `J : D.U.H →L[ℂ] πU.H` to `E.extendOfNorm D.ι`. Establish `hJ : ∀ y, J (D.ι y) = E y` using `fun y => LinearMap.extendOfNorm_eq hd ⟨1, fun x => by rw [hn, one_mul]⟩ y`. Establish `hJn : ∀ x, ‖J x‖ = ‖x‖`. Establish `hfun` using `Continuous.ext_on hd (f := fun x => ‖J x‖) (g := fun x => ‖x‖) J.continuous.norm continuous_norm (by`.

Introduce and unpack `_ ⟨y, rfl⟩`. Use `show ‖J (D.ι y)‖ = ‖D.ι y‖`. Rewrite using `[hJ, hn])`. Conclude with `fun x => congrFun hfun x`. Establish `hexp : ∀ Y ∈ upq p q, ∀ x, J (D.U.π (T.expt Y) x) = πU.π (T.expt Y) (J x)`.

Introduce `Y hY`. Establish `hfun` using `Continuous.ext_on hd (f := fun x => J (D.U.π (T.expt Y) x)) (g := fun x => πU.π (T.expt Y) (J x)) (J.continuous.comp (D.U.π (T.expt Y)).continuous) ((πU.π (T.expt Y)).continuous.comp J.continuous) (by`. Introduce and unpack `_ ⟨y, rfl⟩`. Establish `h` using `J_pi_expt_iota_eq D πU E J hJ hder hn hJn hb hY y 1`. Simplify using `only [one_smul] at h`.

Use `show J (D.U.π (T.expt Y) (D.ι y)) = πU.π (T.expt Y) (J (D.ι y))`. Rewrite using `[hJ]`. Conclude with `h)`. Conclude with `fun x => congrFun hfun x`. Establish `cancelU : ∀ (a : T.G) (z : πU.H), πU.π a⁻¹ (πU.π a z) = z`.

Introduce `a z`. Rewrite using `[← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel, map_one, ContinuousLinearMap.one_apply]`. Establish `cancelD : ∀ (a : T.G) (z : D.U.H), D.U.π a (D.U.π a⁻¹ z) = z`. Introduce `a z`. Rewrite using `[← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one, ContinuousLinearMap.one_apply]`.

Set `S : Subgroup T.G` to `{ carrier := {a | ∀ x, J (D.U.π a x) = πU.π a (J x)} one_mem' := by`. Simplify using `only [Set.mem_setOf_eq, map_one, ContinuousLinearMap.one_apply, implies_true]`. Use the proof step `mul_mem' := by`. Introduce `a b ha hb' x`. Simplify using `only [Set.mem_setOf_eq] at ha hb'`.

Simplify using `only [map_mul, ContinuousLinearMap.mul_apply]`. Rewrite using `[ha, hb']`. Use the proof step `inv_mem' := by`. Introduce `a ha x`. Simplify using `only [Set.mem_setOf_eq] at ha`.

Establish `h1` using `ha (D.U.π a⁻¹ x)`. Rewrite `h1` using `[cancelD]`. Rewrite using `[h1, cancelU] }`. Establish `hle : Subgroup.closure (T.expt '' upq p q) ≤ S`. Rewrite using `[Subgroup.closure_le]`.

Introduce and unpack `_ ⟨Y, hY, rfl⟩`. Conclude with `hexp Y hY`. Establish `hall : ∀ a : T.G, a ∈ S` using `fun a => hle ((GlobalTheory.T.coverUpq_closure_exp_top_and_cartan p q hpq T).1 ▸ Subgroup.mem_top a)`. Use `⟨{ toLinearMap := J.toLinearMap, norm_map' := hJn }, hJ, ?_⟩` and prove the remaining obligations. Introduce `a x`.

Conclude with `hall a x`.
-/
theorem exists_isometry_intertwiner_of_derived :
    ∀ (p q : ℕ), 1 ≤ p + q → ∀ (T : GrpData p q) (D : DSRep T) (πU : URep T) (E : D.HK.V →ₗ[ℂ] πU.H), Dense (Set.range D.ι) → (∀ y, ‖E y‖ = ‖D.ι y‖) → (∀ Y ∈ upq p q, ∀ y, HasDerivAt (fun t : ℝ => πU.π (T.expt (t • Y)) (E y)) (E (D.HK.act Y y)) 0) → (∀ Y ∈ upq p q, ∀ y, ∃ C ρ : ℝ, 0 ≤ C ∧ 0 < ρ ∧ ∀ k : ℕ, ‖D.ι ((D.HK.act Y ^ k) y)‖ ≤ C * ρ ^ k * (k.factorial : ℝ)) → ∃ j : D.U.H →ₗᵢ[ℂ] πU.H, (∀ y, j (D.ι y) = E y) ∧ ∀ g x, j (D.U.π g x) = πU.π g (j x) := by
  intro p q hpq T D πU E hd hn hder hb
  let J : D.U.H →L[ℂ] πU.H := E.extendOfNorm D.ι
  have hJ : ∀ y, J (D.ι y) = E y := fun y =>
    LinearMap.extendOfNorm_eq hd ⟨1, fun x => by rw [hn, one_mul]⟩ y
  have hJn : ∀ x, ‖J x‖ = ‖x‖ := by
    have hfun := Continuous.ext_on hd (f := fun x => ‖J x‖) (g := fun x => ‖x‖)
      J.continuous.norm continuous_norm (by
        rintro _ ⟨y, rfl⟩
        show ‖J (D.ι y)‖ = ‖D.ι y‖
        rw [hJ, hn])
    exact fun x => congrFun hfun x
  have hexp : ∀ Y ∈ upq p q, ∀ x, J (D.U.π (T.expt Y) x) = πU.π (T.expt Y) (J x) := by
    intro Y hY
    have hfun := Continuous.ext_on hd (f := fun x => J (D.U.π (T.expt Y) x))
      (g := fun x => πU.π (T.expt Y) (J x))
      (J.continuous.comp (D.U.π (T.expt Y)).continuous)
      ((πU.π (T.expt Y)).continuous.comp J.continuous) (by
        rintro _ ⟨y, rfl⟩
        have h := J_pi_expt_iota_eq D πU E J hJ hder hn hJn hb hY y 1
        simp only [one_smul] at h
        show J (D.U.π (T.expt Y) (D.ι y)) = πU.π (T.expt Y) (J (D.ι y))
        rw [hJ]
        exact h)
    exact fun x => congrFun hfun x
  have cancelU : ∀ (a : T.G) (z : πU.H), πU.π a⁻¹ (πU.π a z) = z := by
    intro a z
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      ContinuousLinearMap.one_apply]
  have cancelD : ∀ (a : T.G) (z : D.U.H), D.U.π a (D.U.π a⁻¹ z) = z := by
    intro a z
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      ContinuousLinearMap.one_apply]
  let S : Subgroup T.G :=
    { carrier := {a | ∀ x, J (D.U.π a x) = πU.π a (J x)}
      one_mem' := by
        simp only [Set.mem_setOf_eq, map_one, ContinuousLinearMap.one_apply, implies_true]
      mul_mem' := by
        intro a b ha hb' x
        simp only [Set.mem_setOf_eq] at ha hb'
        simp only [map_mul, ContinuousLinearMap.mul_apply]
        rw [ha, hb']
      inv_mem' := by
        intro a ha x
        simp only [Set.mem_setOf_eq] at ha
        have h1 := ha (D.U.π a⁻¹ x)
        rw [cancelD] at h1
        rw [h1, cancelU] }
  have hle : Subgroup.closure (T.expt '' upq p q) ≤ S := by
    rw [Subgroup.closure_le]
    rintro _ ⟨Y, hY, rfl⟩
    exact hexp Y hY
  have hall : ∀ a : T.G, a ∈ S := fun a =>
    hle ((GlobalTheory.T.coverUpq_closure_exp_top_and_cartan p q hpq T).1 ▸ Subgroup.mem_top a)
  refine ⟨{ toLinearMap := J.toLinearMap, norm_map' := hJn }, hJ, ?_⟩
  intro a x
  exact hall a x

end GlobalTheory.FockTensor
