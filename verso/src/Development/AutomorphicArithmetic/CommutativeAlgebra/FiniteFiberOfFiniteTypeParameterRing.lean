import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TcoMem
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FibFiniteAndSep

open GlobalTheory GlobalTheory.PD

set_option autoImplicit false

noncomputable section

namespace UpperTheory

end UpperTheory

/- English proof (translation)
Introduce `F K _ _ _ _ _ _ d x hx hft`. Establish `hmem : ∀ c : rA ℂ x {0}, algebraMap F K (c : F) ∈ rB ℂ K x {0}`. Introduce `c`. Use `show algebraMap F K (c : F) ∈ (integralClosure (rA ℂ x {0}) K).restrictScalars ℂ`. Rewrite using `[Subalgebra.mem_restrictScalars, mem_integralClosure_iff]`.

Conclude with `isIntegral_algebraMap (x := c)`. Set `ι : rA ℂ x {0} →ₐ[ℂ] rB ℂ K x {0}` to `((IsScalarTower.toAlgHom ℂ F K).comp (rA ℂ x {0}).val).codRestrict _ hmem`. Establish `key : ∀ e1 e2 : fib ℂ K x, ∀ c : rA ℂ x {0}, e1.1 (ι c) = e2.1 (ι c)`. Introduce `e1 e2 c`. Take `⟨c, hc⟩` from `c`.

Proceed by induction on `hc using Algebra.adjoin_induction with`. Consider the case `mem y hy`. Take `⟨i, hi, j, rfl⟩` from `hy`. Rewrite `hi` using `[Finset.mem_singleton]`. Substitute `hi` using the available equality.

Break down `Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩` into its components or cases. Establish `h3 : ∀ (e : fib ℂ K x) (h : x 0 / x 0 ∈ rA ℂ x {0}), e.1 (ι ⟨x 0 / x 0, h⟩) = 1`. Introduce `e h`. Establish `h1 : (⟨x 0 / x 0, h⟩ : rA ℂ x {0}) = 1` using `Subtype.ext (div_self (hx.ne 0))`. Rewrite using `[h1, map_one, map_one]`.

Conclude with `(h3 e1 _).trans (h3 e2 _).symm`. Conclude with `(e1.2 j').trans (e2.2 j').symm`. Consider the case `algebraMap r => show e1.1 (ι (algebraMap ℂ (rA ℂ x {0}) r)) = e2.1 (ι (algebraMap ℂ (rA ℂ x {0}) r))`. Simplify using `only [AlgHom.commutes]`. Consider the case `add y z hy hz ihy ihz => show e1.1 (ι (⟨y, hy⟩ + ⟨z, hz⟩)) = e2.1 (ι (⟨y, hy⟩ + ⟨z, hz⟩))`.

Simplify using `only [map_add, ihy, ihz]`. Consider the case `mul y z hy hz ihy ihz => show e1.1 (ι (⟨y, hy⟩ * ⟨z, hz⟩)) = e2.1 (ι (⟨y, hy⟩ * ⟨z, hz⟩))`. Simplify using `only [map_mul, ihy, ihz]`. Break down `isEmpty_or_nonempty (fib ℂ K x) with hE | hE` into its components or cases. Use `infer_instance`.

Take `⟨e0⟩` from `hE`. Take `⟨s, hs⟩` from `hft.out`. Set `ψ : rA ℂ x {0} →+* ℂ` to `(e0.1.comp ι).toRingHom`. Establish `hint : ∀ b : rB ℂ K x {0}, IsIntegral (rA ℂ x {0}) (b : K)` using `fun b => b.2`. Set `R : rB ℂ K x {0} → Finset ℂ` to `fun b => (((hint b).choose).map ψ).roots.toFinset`.

Establish `hR : ∀ (e : fib ℂ K x) (b : rB ℂ K x {0}), e.1 b ∈ R b`. Introduce `e b`. Take `⟨hm, hp⟩` from `(hint b).choose_spec`. Establish `h0 : Polynomial.eval₂ (ι : rA ℂ x {0} →+* rB ℂ K x {0}) b (hint b).choose = 0`. Apply `Subtype.ext` to reduce the goal to its premises.

Use `Polynomial.hom_eval₂ (hint b).choose (ι : rA ℂ x {0} →+* rB ℂ K x {0}) (rB ℂ K x {0}).val.toRingHom b` as an intermediate fact. Use `this.trans ?_` and prove the remaining obligations. Rewrite using `[Subalgebra.coe_zero]`. Conclude with `hp`. Establish `h1` using `Polynomial.hom_eval₂ (hint b).choose (ι : rA ℂ x {0} →+* rB ℂ K x {0}) e.1.toRingHom b`.

Rewrite `h1` using `[h0, map_zero]`. Establish `h2 : e.1.toRingHom.comp (ι : rA ℂ x {0} →+* rB ℂ K x {0}) = ψ` using `RingHom.ext fun c => key e e0 c`. Rewrite `h1` using `[h2]`. Establish `hne : ((hint b).choose.map ψ) ≠ 0` using `(hm.map ψ).ne_zero`. Rewrite using `[Multiset.mem_toFinset, Polynomial.mem_roots hne, Polynomial.IsRoot, Polynomial.eval_map]`.

Conclude with `h1.symm`. Set `Φ : fib ℂ K x → ((t : s) → (R t : Set ℂ))` to `fun e t => ⟨e.1 t, hR e t⟩`. Apply `Finite.of_injective Φ` to reduce the goal to its premises. Introduce `e1 e2 h`. Apply `Subtype.ext` to reduce the goal to its premises.

Apply `AlgHom.ext_of_adjoin_eq_top hs` to reduce the goal to its premises. Introduce `t ht`. Use `congrFun h ⟨t, ht⟩` as an intermediate fact. Conclude with `congrArg Subtype.val this`.
-/
theorem UpperTheory.finite_fiber_of_finiteType_parameter_ring :
    ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K]
      (d : ℕ) (x : Fin (d + 1) → F), IsPd ℂ x → Algebra.FiniteType ℂ (rB ℂ K x {0}) →
      Finite (fib ℂ K x) := by
  intro F K _ _ _ _ _ _ d x hx hft
  classical
  have hmem : ∀ c : rA ℂ x {0}, algebraMap F K (c : F) ∈ rB ℂ K x {0} := by
    intro c
    show algebraMap F K (c : F) ∈ (integralClosure (rA ℂ x {0}) K).restrictScalars ℂ
    rw [Subalgebra.mem_restrictScalars, mem_integralClosure_iff]
    exact isIntegral_algebraMap (x := c)
  let ι : rA ℂ x {0} →ₐ[ℂ] rB ℂ K x {0} :=
    ((IsScalarTower.toAlgHom ℂ F K).comp (rA ℂ x {0}).val).codRestrict _ hmem
  have key : ∀ e1 e2 : fib ℂ K x, ∀ c : rA ℂ x {0}, e1.1 (ι c) = e2.1 (ι c) := by
    intro e1 e2 c
    obtain ⟨c, hc⟩ := c
    induction hc using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨i, hi, j, rfl⟩ := hy
      rw [Finset.mem_singleton] at hi
      subst hi
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
      · have h3 : ∀ (e : fib ℂ K x) (h : x 0 / x 0 ∈ rA ℂ x {0}), e.1 (ι ⟨x 0 / x 0, h⟩) = 1 := by
          intro e h
          have h1 : (⟨x 0 / x 0, h⟩ : rA ℂ x {0}) = 1 := Subtype.ext (div_self (hx.ne 0))
          rw [h1, map_one, map_one]
        exact (h3 e1 _).trans (h3 e2 _).symm
      · exact (e1.2 j').trans (e2.2 j').symm
    | algebraMap r =>
      show e1.1 (ι (algebraMap ℂ (rA ℂ x {0}) r)) = e2.1 (ι (algebraMap ℂ (rA ℂ x {0}) r))
      simp only [AlgHom.commutes]
    | add y z hy hz ihy ihz =>
      show e1.1 (ι (⟨y, hy⟩ + ⟨z, hz⟩)) = e2.1 (ι (⟨y, hy⟩ + ⟨z, hz⟩))
      simp only [map_add, ihy, ihz]
    | mul y z hy hz ihy ihz =>
      show e1.1 (ι (⟨y, hy⟩ * ⟨z, hz⟩)) = e2.1 (ι (⟨y, hy⟩ * ⟨z, hz⟩))
      simp only [map_mul, ihy, ihz]
  rcases isEmpty_or_nonempty (fib ℂ K x) with hE | hE
  · infer_instance
  obtain ⟨e0⟩ := hE
  obtain ⟨s, hs⟩ := hft.out
  let ψ : rA ℂ x {0} →+* ℂ := (e0.1.comp ι).toRingHom
  have hint : ∀ b : rB ℂ K x {0}, IsIntegral (rA ℂ x {0}) (b : K) := fun b => b.2
  let R : rB ℂ K x {0} → Finset ℂ := fun b => (((hint b).choose).map ψ).roots.toFinset
  have hR : ∀ (e : fib ℂ K x) (b : rB ℂ K x {0}), e.1 b ∈ R b := by
    intro e b
    obtain ⟨hm, hp⟩ := (hint b).choose_spec
    have h0 : Polynomial.eval₂ (ι : rA ℂ x {0} →+* rB ℂ K x {0}) b (hint b).choose = 0 := by
      apply Subtype.ext
      have := Polynomial.hom_eval₂ (hint b).choose (ι : rA ℂ x {0} →+* rB ℂ K x {0})
        (rB ℂ K x {0}).val.toRingHom b
      refine this.trans ?_
      rw [Subalgebra.coe_zero]
      exact hp
    have h1 := Polynomial.hom_eval₂ (hint b).choose (ι : rA ℂ x {0} →+* rB ℂ K x {0}) e.1.toRingHom b
    rw [h0, map_zero] at h1
    have h2 : e.1.toRingHom.comp (ι : rA ℂ x {0} →+* rB ℂ K x {0}) = ψ :=
      RingHom.ext fun c => key e e0 c
    rw [h2] at h1
    have hne : ((hint b).choose.map ψ) ≠ 0 := (hm.map ψ).ne_zero
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hne, Polynomial.IsRoot, Polynomial.eval_map]
    exact h1.symm
  let Φ : fib ℂ K x → ((t : s) → (R t : Set ℂ)) := fun e t => ⟨e.1 t, hR e t⟩
  apply Finite.of_injective Φ
  intro e1 e2 h
  apply Subtype.ext
  apply AlgHom.ext_of_adjoin_eq_top hs
  intro t ht
  have := congrFun h ⟨t, ht⟩
  exact congrArg Subtype.val this
