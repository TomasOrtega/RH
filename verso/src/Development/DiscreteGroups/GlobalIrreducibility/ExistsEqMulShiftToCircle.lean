import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzMatchCut
import GroundTheory.LocalFields.LocalFourierPadic

noncomputable section

open NumberField IsDedekindDomain

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_eq_mulShift_toCircle (g : ℕ) [NeZero g] (l : AddChar (ZMod g) Circle) :
    ∃ s : ZMod g, l = (ZMod.toCircle : AddChar (ZMod g) Circle).mulShift s := by
  classical
  let e : AddChar (ZMod g) Circle → AddChar (ZMod g) ℂ := fun χ => Circle.coeHom.compAddChar χ
  have he : Function.Injective e :=
    MonoidHom.compAddChar_injective_right _ (fun a b h => Circle.coe_inj.mp h)
  have hp : (e ZMod.toCircle).IsPrimitive := ZMod.isPrimitive_stdAddChar g
  have hbij : Function.Bijective (e ZMod.toCircle).mulShift :=
    (Fintype.bijective_iff_injective_and_card _).mpr
      ⟨AddChar.to_mulShift_inj_of_isPrimitive hp, AddChar.card_eq.symm⟩
  obtain ⟨s, hs⟩ := hbij.2 (e l)
  refine ⟨s, DFunLike.ext _ _ fun t => ?_⟩
  have := congrArg (fun χ : AddChar (ZMod g) ℂ => χ t) hs
  simp only [e, AddChar.mulShift_apply, MonoidHom.compAddChar_apply, Function.comp_apply] at this
  rw [AddChar.mulShift_apply]
  exact (Circle.coe_inj.mp this).symm

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Clear the denominators using the available nonvanishing facts.

Move the embeddings inside the algebraic operations. Take a linear combination of the given relations to obtain the conclusion. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Move the embeddings inside the algebraic operations.

Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem stdChar_shift_intCast (g : ℕ) [Fact g.Prime] (s : ZMod g) (x : ℤ_[g]) :
    GroundTheory.LocalField.Padic.stdChar g (((s.val : ℚ_[g]) / g) * (x : ℚ_[g])) =
      ZMod.toCircle (s * PadicInt.toZMod x) := by
  have hg0 : (g : ℚ_[g]) ≠ 0 := by exact_mod_cast (Fact.out : g.Prime).ne_zero
  set j : ZMod g := s * PadicInt.toZMod x with hj
  have hmem : (s.val : ℤ_[g]) * x - (j.val : ℤ_[g]) ∈ RingHom.ker (PadicInt.toZMod (p := g)) := by
    rw [RingHom.mem_ker, map_sub, map_mul, map_natCast, map_natCast, ZMod.natCast_zmod_val,
      ZMod.natCast_zmod_val, hj, sub_self]
  rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hc' : ((s.val : ℚ_[g]) / g) * (x : ℚ_[g]) - ((j.val : ℤ) : ℚ_[g]) / (g : ℚ_[g]) ^ 1 = (c : ℚ_[g]) := by
    have := congrArg (fun z : ℤ_[g] => (z : ℚ_[g])) hc
    simp only [PadicInt.coe_mul, PadicInt.coe_natCast, PadicInt.coe_sub] at this
    rw [pow_one]
    field_simp
    push_cast
    linear_combination (-1 : ℚ_[g]) * this
  rw [GroundTheory.LocalField.Padic.stdChar_apply g _ (j.val : ℤ) 1 (by rw [hc']; exact c.2),
    ZMod.toCircle_eq_circleExp, Real.fourierChar_apply']
  congr 1
  push_cast
  ring

/- English proof (translation)
Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem continuous_symm' {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ}
    [Fact g.Prime] (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i) : Continuous i.symm := by
  have ho : IsOpenMap i :=
    AddMonoidHom.isOpenMap_of_sigmaCompact i.toRingHom.toAddMonoidHom i.surjective hi
  exact (i.toEquiv.toHomeomorphOfContinuousOpen hi ho).symm.continuous

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Introduce a local definition for the expression.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem lPsi : LPsi := by
  intro E _ _ w g _ i hi ψ₀ h₀
  have : NeZero g := ⟨(Fact.out : g.Prime).ne_zero⟩
  obtain ⟨s, hs⟩ := exists_eq_mulShift_toCircle g ψ₀
  let ψQ : AddChar ℚ_[g] Circle := (GroundTheory.LocalField.Padic.stdChar g).mulShift ((s.val : ℚ_[g]) / g)
  let ψ : AddChar (w.adicCompletion E) Circle := ψQ.compAddMonoidHom i.symm.toAddMonoidHom
  have key : ∀ x : ℤ_[g], ψ (i (x : ℚ_[g])) = ψ₀ (PadicInt.toZMod x) := fun x => by
    show GroundTheory.LocalField.Padic.stdChar g (((s.val : ℚ_[g]) / g) * i.symm (i (x : ℚ_[g]))) = ψ₀ _
    rw [RingEquiv.symm_apply_apply, stdChar_shift_intCast, hs, AddChar.mulShift_apply]
  refine ⟨ψ, ?_, ?_, key⟩
  · exact (GroundTheory.LocalField.Padic.continuous_stdChar g).comp (continuous_const.mul (continuous_symm' i hi))
  · intro h1
    apply h₀
    refine DFunLike.ext _ _ fun k => ?_
    obtain ⟨x, rfl⟩ := ZMod.ringHom_surjective (PadicInt.toZMod (p := g)) k
    rw [← key, h1, AddChar.one_apply, AddChar.one_apply]

end DiscreteGroups.sglob.DzType
