import Formalism.LocalToGlobal.GlobalTheory.BlockActions.NormBoundOfTorsionCharacter
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.GlintPrincRelIndexNeZero

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms

/- English proof (translation)
Introduce `D u Ch chOf Tf c`. Set `P : ℂ → Prop` to `fun z => ∃ k : ℕ, 0 < k ∧ z ^ k = 1`. Establish `h1 : P 1` using `⟨1, one_pos, one_pow _⟩`. Establish `hmul : ∀ x y, P x → P y → P (x * y)`. Introduce and unpack `x y ⟨k, hk, hx⟩ ⟨l, hl, hy⟩`.

Use `⟨k * l, Nat.mul_pos hk hl, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_pow, pow_mul, hx, one_pow, one_mul, mul_comm k l, pow_mul, hy, one_pow]`. Establish `hfac : ∀ a v h, P (((Tf.lamM a v h ((Tf.glevM).red a v h (Tf.tilAd.ka c)) : ℂˣ) : ℂ))⁻¹`. Introduce `a v h`. Use `haveI : Finite (Formalism.L2.Forms.kv D.host.F v) := Formalism.UG.P.glint_finite_residueField v`.

Use `⟨orderOf ((Tf.glevM).red a v h (Tf.tilAd.ka c)), orderOf_pos _, ?_⟩` and prove the remaining obligations. Rewrite using `[inv_pow, ← Units.val_pow_eq_pow_val, ← map_pow, pow_orderOf_eq_one, map_one, Units.val_one, inv_one]`. Use `show P _`. Rewrite using `[(Tf.glevM).chi_eq]`. Use `Finset.prod_induction _ P hmul h1 fun a _ => ?_` and prove the remaining obligations.

Use `finprod_induction P h1 hmul fun v => ?_` and prove the remaining obligations. Conclude with `finprod_induction P h1 hmul fun h => hfac a v h`.
-/
theorem chiTors : ChiTors := by
  intro D u Ch chOf Tf c
  classical
  let P : ℂ → Prop := fun z => ∃ k : ℕ, 0 < k ∧ z ^ k = 1
  have h1 : P 1 := ⟨1, one_pos, one_pow _⟩
  have hmul : ∀ x y, P x → P y → P (x * y) := by
    rintro x y ⟨k, hk, hx⟩ ⟨l, hl, hy⟩
    refine ⟨k * l, Nat.mul_pos hk hl, ?_⟩
    rw [mul_pow, pow_mul, hx, one_pow, one_mul, mul_comm k l, pow_mul, hy, one_pow]
  have hfac : ∀ a v h, P (((Tf.lamM a v h ((Tf.glevM).red a v h (Tf.tilAd.ka c)) : ℂˣ) : ℂ))⁻¹ := by
    intro a v h
    haveI : Finite (Formalism.L2.Forms.kv D.host.F v) := Formalism.UG.P.glint_finite_residueField v
    refine ⟨orderOf ((Tf.glevM).red a v h (Tf.tilAd.ka c)), orderOf_pos _, ?_⟩
    rw [inv_pow, ← Units.val_pow_eq_pow_val, ← map_pow, pow_orderOf_eq_one, map_one, Units.val_one, inv_one]
  show P _
  rw [(Tf.glevM).chi_eq]
  refine Finset.prod_induction _ P hmul h1 fun a _ => ?_
  refine finprod_induction P h1 hmul fun v => ?_
  exact finprod_induction P h1 hmul fun h => hfac a v h

/- English proof (translation)
The claim follows from `normClsAt_of_tors chiTors`.
-/
theorem normClsAt_holds : NormClsAt := normClsAt_of_tors chiTors

/- English proof (translation)
The claim follows from `norm_bound_of_classes h1 h2 normClsAt_holds`.
-/
theorem norm_bound_of_injective_stable (h1 : ClassMapInjective) (h2 : StabiliserMapBijective) : NormBoundAtInfinity :=
  norm_bound_of_classes h1 h2 normClsAt_holds

end Formalism.L2.GlobalTheoryTheory.Br
