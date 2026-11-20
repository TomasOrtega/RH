import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Target

noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.Choice
open scoped Classical
set_option synthInstance.maxHeartbeats 200000

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Tail

/- English proof (translation)
Unfold `qU`. Use `split_ifs with h`. Conclude with `zpow_add _ x y`. Conclude with `(mul_one 1).symm`.
-/
theorem qU_add {E : Type} [Field E] [NumberField E] [IsCMField E] (w : Pl E) (x y : ℤ) :
    qU w (x + y) = qU w x * qU w y := by
  unfold qU
  split_ifs with h
  · exact zpow_add _ x y
  · exact (mul_one 1).symm

/- English proof (translation)
Introduce `E _ _ _ n w s sg ξ ξa ξb hstd hchi`. Establish `hk : ∀ k : Fin n, chiOf w s ξa ξb k = chiN w ξ k` using `fun k => congrFun hchi k`. Prove the components needed by the constructor for the conclusion. Introduce `i`. Establish `h` using `hk (s.e (Sum.inl i))`.

Establish `he` using `hstd (s.e (Sum.inl i))`. Simplify using `only [chiOf, chiN, Equiv.symm_apply_apply, Sum.elim_inl] at h`. Simplify using `only [Equiv.symm_apply_apply, Sum.elim_inl] at he`. Rewrite `h` using `[he, mul_assoc, ← mul_assoc (qU w _), mul_comm (qU w _) (ξa i), mul_assoc (ξa i), ← qU_add]`. Establish `hr : rh n ↑(s.e (Sum.inl i)) - rh s.a ↑i + (↑s.a - 1 - 2 * ↑↑i) = rh n ↑(s.e (Sum.inl i))`.

Simplify using `only [rh]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h` using `[hr, ← mul_assoc]`. Rewrite using `[eq_mul_inv_iff_mul_eq, mul_comm]`. Conclude with `mul_right_cancel h`.

Introduce `j`. Establish `h` using `hk (s.e (Sum.inr j))`. Establish `he` using `hstd (s.e (Sum.inr j))`. Simplify using `only [chiOf, chiN, Equiv.symm_apply_apply, Sum.elim_inr] at h`. Simplify using `only [Equiv.symm_apply_apply, Sum.elim_inr] at he`.

Rewrite `h` using `[he, mul_assoc, ← mul_assoc (qU w _), mul_comm (qU w _) (ξb j), mul_assoc (ξb j), ← qU_add]`. Establish `hr : rh n ↑(s.e (Sum.inr j)) - rh s.b ↑j + (↑s.b - 1 - 2 * ↑↑j) = rh n ↑(s.e (Sum.inr j))`. Simplify using `only [rh]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h` using `[hr, ← mul_assoc]`.

Rewrite using `[eq_mul_inv_iff_mul_eq, mul_comm]`. Conclude with `mul_right_cancel h`.
-/
theorem targetAlg : TargetAlg := by
  intro E _ _ _ n w s sg ξ ξa ξb hstd hchi
  have hk : ∀ k : Fin n, chiOf w s ξa ξb k = chiN w ξ k := fun k => congrFun hchi k
  constructor
  · intro i
    have h := hk (s.e (Sum.inl i))
    have he := hstd (s.e (Sum.inl i))
    simp only [chiOf, chiN, Equiv.symm_apply_apply, Sum.elim_inl] at h
    simp only [Equiv.symm_apply_apply, Sum.elim_inl] at he
    rw [he, mul_assoc, ← mul_assoc (qU w _), mul_comm (qU w _) (ξa i), mul_assoc (ξa i),
      ← qU_add] at h
    have hr : rh n ↑(s.e (Sum.inl i)) - rh s.a ↑i + (↑s.a - 1 - 2 * ↑↑i) = rh n ↑(s.e (Sum.inl i)) := by
      simp only [rh]
      ring
    rw [hr, ← mul_assoc] at h
    rw [eq_mul_inv_iff_mul_eq, mul_comm]
    exact mul_right_cancel h
  · intro j
    have h := hk (s.e (Sum.inr j))
    have he := hstd (s.e (Sum.inr j))
    simp only [chiOf, chiN, Equiv.symm_apply_apply, Sum.elim_inr] at h
    simp only [Equiv.symm_apply_apply, Sum.elim_inr] at he
    rw [he, mul_assoc, ← mul_assoc (qU w _), mul_comm (qU w _) (ξb j), mul_assoc (ξb j),
      ← qU_add] at h
    have hr : rh n ↑(s.e (Sum.inr j)) - rh s.b ↑j + (↑s.b - 1 - 2 * ↑↑j) = rh n ↑(s.e (Sum.inr j)) := by
      simp only [rh]
      ring
    rw [hr, ← mul_assoc] at h
    rw [eq_mul_inv_iff_mul_eq, mul_comm]
    exact mul_right_cancel h

/- English proof (translation)
Introduce `n s sg ξ hξ hsg`. Establish `hn : ∀ k, ‖((ξ k * (sg k)⁻¹ : ℂˣ) : ℂ)‖ = ‖((ξ k : ℂˣ) : ℂ)‖` using `fun k => by`. Rewrite using `[Units.val_mul, norm_mul, Units.val_inv_eq_inv_val, norm_inv, hsg k, inv_one, mul_one]`. Prove the components needed by the constructor for the conclusion. Introduce `i j hij`.

Simplify using `only [hn]`. Conclude with `hξ _ _ (s.monoL.monotone hij)`. Introduce `i j hij`. Simplify using `only [hn]`. Conclude with `hξ _ _ (s.monoR.monotone hij)`.
-/
theorem monoRes : MonoRes := by
  intro n s sg ξ hξ hsg
  have hn : ∀ k, ‖((ξ k * (sg k)⁻¹ : ℂˣ) : ℂ)‖ = ‖((ξ k : ℂˣ) : ℂ)‖ := fun k => by
    rw [Units.val_mul, norm_mul, Units.val_inv_eq_inv_val, norm_inv, hsg k, inv_one, mul_one]
  constructor
  · intro i j hij
    simp only [hn]
    exact hξ _ _ (s.monoL.monotone hij)
  · intro i j hij
    simp only [hn]
    exact hξ _ _ (s.monoR.monotone hij)

end PositivityTheory.Rg.BcB.F.Tail

end
