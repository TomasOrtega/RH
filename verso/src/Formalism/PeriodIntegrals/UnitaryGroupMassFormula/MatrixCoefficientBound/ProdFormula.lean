import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GGMirabolic
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MatrixCoefficientBound.PermRepApply

open Finset

noncomputable section

open Classical

namespace PI.GGMatBoundW

open Formalism.L2.SG.GGMirabolic

section Prod

variable {ι : Type} [Fintype ι] {Fq : ι → Type} [∀ v, Field (Fq v)] [∀ v, Fintype (Fq v)] {k : ℕ}

def beta (ψ : ∀ v, AddChar (Fq v) ℂ) (s : Finset ι) (x : ∀ v, GL (Fin k) (Fq v)) : ℂ :=
  if ∀ w, w ∉ s → x w = 1 then ∏ v ∈ s, gam (ψ v) (x v) else 0

/- English proof (translation)
Establish `hz : ∀ w, ((Pi.mulSingle a (z a))⁻¹ * z : ∀ v, GL (Fin k) (Fq v)) w = if w = a then 1 else z w`. Introduce `w`. Distinguish the cases in `hw : w = a`. Substitute `hw` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[hw, Pi.mulSingle_eq_of_ne hw]`. Rewrite using `[Finset.sum_eq_single (z a)]`. Unfold `beta`. Establish `hcond : (∀ w, w ∉ insert a s → z w = 1) ↔ (∀ w, w ∉ s → ((Pi.mulSingle a (z a))⁻¹ * z : ∀ v, GL (Fin k) (Fq v)) w = 1)`. Prove the components needed by the constructor for the conclusion.

Introduce `h w hw`. Rewrite using `[hz]`. Distinguish the cases in `hwa : w = a`. Rewrite using `[if_pos hwa]`. Rewrite using `[if_neg hwa]`.

Conclude with `h w (by simp [hwa, hw])`. Introduce `h w hw`. Simplify using `only [Finset.mem_insert, not_or] at hw`. Use `h w hw.2` as an intermediate fact. Rewrite `this` using `[hz, if_neg hw.1]`. Then use the resulting hypothesis.

Establish `hprod : ∏ v ∈ s, gam (ψ v) (((Pi.mulSingle a (z a))⁻¹ * z : ∀ v, GL (Fin k) (Fq v)) v) = ∏ v ∈ s, gam (ψ v) (z v)`. Use `Finset.prod_congr rfl fun v hv => ?_` and prove the remaining obligations. Rewrite using `[hz, if_neg (fun (h : v = a) => ha (h ▸ hv))]`. Distinguish the cases in `h : ∀ w, w ∉ insert a s → z w = 1`. Rewrite using `[if_pos h, if_pos (hcond.mp h), hprod, Finset.prod_insert ha]`.

Rewrite using `[if_neg h, if_neg (fun h' => h (hcond.mpr h')), mul_zero]`. Introduce `y _ hy`. Unfold `beta`. Rewrite using `[if_neg, mul_zero]`. Introduce `h`.

Apply `hy` to reduce the goal to its premises. Use `h a ha` as an intermediate fact. Simplify using `only [Pi.mul_apply, Pi.inv_apply, Pi.mulSingle_eq_same] at this`. Conclude with `inv_mul_eq_one.mp this`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem beta_insert (ψ : ∀ v, AddChar (Fq v) ℂ) {a : ι} {s : Finset ι} (ha : a ∉ s)
    (z : ∀ v, GL (Fin k) (Fq v)) :
    beta ψ (insert a s) z =
      ∑ y : GL (Fin k) (Fq a), gam (ψ a) y * beta ψ s ((Pi.mulSingle a y)⁻¹ * z) := by
  have hz : ∀ w, ((Pi.mulSingle a (z a))⁻¹ * z : ∀ v, GL (Fin k) (Fq v)) w = if w = a then 1 else z w := by
    intro w
    by_cases hw : w = a
    · subst hw
      simp
    · simp [hw, Pi.mulSingle_eq_of_ne hw]
  rw [Finset.sum_eq_single (z a)]
  · unfold beta
    have hcond : (∀ w, w ∉ insert a s → z w = 1) ↔
        (∀ w, w ∉ s → ((Pi.mulSingle a (z a))⁻¹ * z : ∀ v, GL (Fin k) (Fq v)) w = 1) := by
      constructor
      · intro h w hw
        rw [hz]
        by_cases hwa : w = a
        · rw [if_pos hwa]
        · rw [if_neg hwa]
          exact h w (by simp [hwa, hw])
      · intro h w hw
        simp only [Finset.mem_insert, not_or] at hw
        have := h w hw.2
        rwa [hz, if_neg hw.1] at this
    have hprod : ∏ v ∈ s, gam (ψ v) (((Pi.mulSingle a (z a))⁻¹ * z : ∀ v, GL (Fin k) (Fq v)) v) =
        ∏ v ∈ s, gam (ψ v) (z v) := by
      refine Finset.prod_congr rfl fun v hv => ?_
      rw [hz, if_neg (fun (h : v = a) => ha (h ▸ hv))]
    by_cases h : ∀ w, w ∉ insert a s → z w = 1
    · rw [if_pos h, if_pos (hcond.mp h), hprod, Finset.prod_insert ha]
    · rw [if_neg h, if_neg (fun h' => h (hcond.mpr h')), mul_zero]
  · intro y _ hy
    unfold beta
    rw [if_neg, mul_zero]
    intro h
    apply hy
    have := h a ha
    simp only [Pi.mul_apply, Pi.inv_apply, Pi.mulSingle_eq_same] at this
    exact inv_mul_eq_one.mp this
  · intro h
    exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Unfold `beta gamProd`. Rewrite using `[if_pos (fun w hw => absurd (Finset.mem_univ w) hw)]`.
-/
theorem beta_univ (ψ : ∀ v, AddChar (Fq v) ℂ) (x : ∀ v, GL (Fin k) (Fq v)) :
    beta ψ Finset.univ x = gamProd ψ x := by
  unfold beta gamProd
  rw [if_pos (fun w hw => absurd (Finset.mem_univ w) hw)]

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Simplify using `only [placeOp, LinearMap.sum_apply, LinearMap.smul_apply]`.
-/
theorem placeOp_apply (ψ : ∀ v, AddChar (Fq v) ℂ) (π : Representation ℂ (∀ v, GL (Fin k) (Fq v)) V)
    (v : ι) (w : V) : placeOp ψ π v w = ∑ y, gam (ψ v) y • π (Pi.mulSingle v y) w := by
  simp only [placeOp, LinearMap.sum_apply, LinearMap.smul_apply]

/- English proof (translation)
Simplify using `only [totOp, LinearMap.sum_apply, LinearMap.smul_apply]`.
-/
theorem totOp_apply (ψ : ∀ v, AddChar (Fq v) ℂ) (π : Representation ℂ (∀ v, GL (Fin k) (Fq v)) V)
    (w : V) : totOp ψ π w = ∑ x, gamProd ψ x • π x w := by
  simp only [totOp, LinearMap.sum_apply, LinearMap.smul_apply]

/- English proof (translation)
Rewrite using `[Finset.sum_eq_single 1]`. Unfold `beta`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Unfold `beta`.

Rewrite using `[if_neg, zero_smul]`. Introduce `h`. Conclude with `hb (funext fun v => h v (by simp))`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem sum_beta_empty (ψ : ∀ v, AddChar (Fq v) ℂ) (π : Representation ℂ (∀ v, GL (Fin k) (Fq v)) V)
    (w : V) : ∑ x, beta ψ ∅ x • π x w = w := by
  rw [Finset.sum_eq_single 1]
  · unfold beta
    simp
  · intro b _ hb
    unfold beta
    rw [if_neg, zero_smul]
    intro h
    exact hb (funext fun v => h v (by simp))
  · intro h
    exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Rewrite using `[placeOp_apply]`. Repeatedly rewrite using `[beta_insert ψ ha, Finset.sum_smul, map_sum, map_smul, Finset.smul_sum]`. Use `conv_lhs => rw [Finset.sum_comm]`. Use `Finset.sum_congr rfl fun y _ => ?_` and prove the remaining obligations. Use `Fintype.sum_equiv (Equiv.mulLeft (Pi.mulSingle a y)⁻¹) _ _ fun z => ?_` and prove the remaining obligations.

Simplify using `only [Equiv.coe_mulLeft]`. Establish `hπ : π (Pi.mulSingle a y) (π ((Pi.mulSingle a y)⁻¹ * z) w) = π z w`. Establish `h2` using `congrArg (fun f => f w) (map_mul π (Pi.mulSingle a y) ((Pi.mulSingle a y)⁻¹ * z))`. Simplify using `only [mul_inv_cancel_left] at h2`. Conclude with `h2.symm`.

Rewrite using `[hπ, mul_smul]`.
-/
theorem sum_beta_insert (ψ : ∀ v, AddChar (Fq v) ℂ) (π : Representation ℂ (∀ v, GL (Fin k) (Fq v)) V)
    {a : ι} {s : Finset ι} (ha : a ∉ s) (w : V) :
    ∑ x, beta ψ (insert a s) x • π x w = placeOp ψ π a (∑ x, beta ψ s x • π x w) := by
  rw [placeOp_apply]
  simp_rw [beta_insert ψ ha, Finset.sum_smul, map_sum, map_smul, Finset.smul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  refine Fintype.sum_equiv (Equiv.mulLeft (Pi.mulSingle a y)⁻¹) _ _ fun z => ?_
  simp only [Equiv.coe_mulLeft]
  have hπ : π (Pi.mulSingle a y) (π ((Pi.mulSingle a y)⁻¹ * z) w) = π z w := by
    have h2 := congrArg (fun f => f w) (map_mul π (Pi.mulSingle a y) ((Pi.mulSingle a y)⁻¹ * z))
    simp only [mul_inv_cancel_left] at h2
    exact h2.symm
  rw [hπ, mul_smul]

end Prod

/- English proof (translation)
Introduce `ι _ Fq _ _ k ψ V _ _ π μ w hμ`. Establish `key : ∀ s : Finset ι, ∑ x, beta ψ s x • π x w = (∏ v ∈ s, μ v) • w`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => rw [sum_beta_empty, Finset.prod_empty, one_smul]`.

Consider the case `@insert a s ha ih`. Rewrite using `[sum_beta_insert ψ π ha w, ih, map_smul, hμ, smul_smul, Finset.prod_insert ha, mul_comm]`. Rewrite using `[totOp_apply, ← key Finset.univ]`. Repeatedly rewrite using `[beta_univ]`.
-/
theorem prod_formula' : ProdFormula := by
  intro ι _ Fq _ _ k ψ V _ _ π μ w hμ
  have key : ∀ s : Finset ι, ∑ x, beta ψ s x • π x w = (∏ v ∈ s, μ v) • w := by
    intro s
    induction s using Finset.induction_on with
    | empty => rw [sum_beta_empty, Finset.prod_empty, one_smul]
    | @insert a s ha ih =>
      rw [sum_beta_insert ψ π ha w, ih, map_smul, hμ, smul_smul, Finset.prod_insert ha, mul_comm]
  rw [totOp_apply, ← key Finset.univ]
  simp_rw [beta_univ]

end PI.GGMatBoundW
