import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzMatchCut
import GroundTheory.LocalFields.LocalFourierPadic

noncomputable section

open NumberField IsDedekindDomain

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Set `e : AddChar (ZMod g) Circle → AddChar (ZMod g) ℂ` to `fun χ => Circle.coeHom.compAddChar χ`. Establish `he : Function.Injective e` using `MonoidHom.compAddChar_injective_right _ (fun a b h => Circle.coe_inj.mp h)`. Establish `hp : (e ZMod.toCircle).IsPrimitive` using `ZMod.isPrimitive_stdAddChar g`. Establish `hbij : Function.Bijective (e ZMod.toCircle).mulShift` using `(Fintype.bijective_iff_injective_and_card _).mpr ⟨AddChar.to_mulShift_inj_of_isPrimitive hp, AddChar.card_eq.symm⟩`. Take `⟨s, hs⟩` from `hbij.2 (e l)`.

Use `⟨s, DFunLike.ext _ _ fun t => ?_⟩` and prove the remaining obligations. Use `congrArg (fun χ : AddChar (ZMod g) ℂ => χ t) hs` as an intermediate fact. Simplify using `only [e, AddChar.mulShift_apply, MonoidHom.compAddChar_apply, Function.comp_apply] at this`. Rewrite using `[AddChar.mulShift_apply]`. Conclude with `(Circle.coe_inj.mp this).symm`.
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
Establish `hg0 : (g : ℚ_[g]) ≠ 0` using `by exact_mod_cast (Fact.out : g.Prime).ne_zero`. Use `set j : ZMod g := s * PadicInt.toZMod x with hj`. Establish `hmem : (s.val : ℤ_[g]) * x - (j.val : ℤ_[g]) ∈ RingHom.ker (PadicInt.toZMod (p` using `g)) := by`. Rewrite using `[RingHom.mem_ker, map_sub, map_mul, map_natCast, map_natCast, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, hj, sub_self]`. Rewrite `hmem` using `[PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton']`.

Take `⟨c, hc⟩` from `hmem`. Establish `hc' : ((s.val : ℚ_[g]) / g) * (x : ℚ_[g]) - ((j.val : ℤ) : ℚ_[g]) / (g : ℚ_[g]) ^ 1 = (c : ℚ_[g])`. Use `congrArg (fun z : ℤ_[g] => (z : ℚ_[g])) hc` as an intermediate fact. Simplify using `only [PadicInt.coe_mul, PadicInt.coe_natCast, PadicInt.coe_sub] at this`. Rewrite using `[pow_one]`.

Clear the denominators using the available nonvanishing facts. Use `push_cast`. Take the linear combination `(-1 : ℚ_[g]) * this`. Rewrite using `[GroundTheory.LocalField.Padic.stdChar_apply g _ (j.val : ℤ) 1 (by rw [hc']; exact c.2), ZMod.toCircle_eq_circleExp, Real.fourierChar_apply']`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
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
Establish `ho : IsOpenMap i` using `AddMonoidHom.isOpenMap_of_sigmaCompact i.toRingHom.toAddMonoidHom i.surjective hi`. Conclude with `(i.toEquiv.toHomeomorphOfContinuousOpen hi ho).symm.continuous`.
-/
theorem continuous_symm' {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ}
    [Fact g.Prime] (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i) : Continuous i.symm := by
  have ho : IsOpenMap i :=
    AddMonoidHom.isOpenMap_of_sigmaCompact i.toRingHom.toAddMonoidHom i.surjective hi
  exact (i.toEquiv.toHomeomorphOfContinuousOpen hi ho).symm.continuous

/- English proof (translation)
Introduce `E _ _ w g _ i hi ψ₀ h₀`. Establish `: NeZero g` using `⟨(Fact.out : g.Prime).ne_zero⟩`. Take `⟨s, hs⟩` from `exists_eq_mulShift_toCircle g ψ₀`. Set `ψQ : AddChar ℚ_[g] Circle` to `(GroundTheory.LocalField.Padic.stdChar g).mulShift ((s.val : ℚ_[g]) / g)`. Set `ψ : AddChar (w.adicCompletion E) Circle` to `ψQ.compAddMonoidHom i.symm.toAddMonoidHom`.

Establish `key : ∀ x : ℤ_[g], ψ (i (x : ℚ_[g])) = ψ₀ (PadicInt.toZMod x)` using `fun x => by show GroundTheory.LocalField.Padic.stdChar g (((s.val : ℚ_[g]) / g) * i.symm (i (x : ℚ_[g]))) = ψ₀ _`. Rewrite using `[RingEquiv.symm_apply_apply, stdChar_shift_intCast, hs, AddChar.mulShift_apply]`. Use `⟨ψ, ?_, ?_, key⟩` and prove the remaining obligations. Conclude with `(GroundTheory.LocalField.Padic.continuous_stdChar g).comp (continuous_const.mul (continuous_symm' i hi))`. Introduce `h1`.

Apply `h₀` to reduce the goal to its premises. Use `DFunLike.ext _ _ fun k => ?_` and prove the remaining obligations. Take `⟨x, rfl⟩` from `ZMod.ringHom_surjective (PadicInt.toZMod (p := g)) k`. Rewrite using `[← key, h1, AddChar.one_apply, AddChar.one_apply]`.
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
