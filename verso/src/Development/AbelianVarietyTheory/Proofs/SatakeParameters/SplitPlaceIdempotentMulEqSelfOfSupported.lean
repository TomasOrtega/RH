import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelesCmFieldEqZeroOfComponents
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

namespace GlobalTheory.PlaceSupp

/- English proof (translation)
Substitute `h` using the available equality. Conclude with `⟨v, α, rfl, h1, h0⟩`.
-/
theorem tensCast_tmul_one {E : Type} [Field E] [NumberField E] {F1 F2 : Subfield E} (h : F1 = F2)
    (v : HeightOneSpectrum (𝓞 F1)) (α : FiniteAdeleRing (𝓞 F1) F1) (h1 : α v = 1) (h0 : ∀ v', v' ≠ v → α v' = 0) :
    ∃ (w : HeightOneSpectrum (𝓞 F2)) (α' : FiniteAdeleRing (𝓞 F2) F2),
      GlobalTheory.NJoin.tensCast h (α ⊗ₜ[F1] (1 : E)) = (1 : E) ⊗ₜ[F2] α' ∧ α' w = 1 ∧ ∀ v', v' ≠ w → α' v' = 0 := by
  subst h
  exact ⟨v, α, rfl, h1, h0⟩

open Classical in

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul m n => simp [TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]`. Consider the case `add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]`.
-/
theorem equivFinsuppOfBasisRight_rTensor {K M N N' ι : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] [AddCommGroup N'] [Module K N']
    (b : Module.Basis ι K M) (f : N →ₗ[K] N') (x : N ⊗[K] M) (i : ι) :
    TensorProduct.equivFinsuppOfBasisRight b (LinearMap.rTensor M f x) i =
      f (TensorProduct.equivFinsuppOfBasisRight b x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m n => simp [TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

/- English proof (translation)
Set `e` to `TensorProduct.equivFinsuppOfBasisRight (M := N) b`. Establish `hc : ∀ i, e x i = 0`. Introduce `i`. Apply `hfg` to reduce the goal to its premises. Use `equivFinsuppOfBasisRight_rTensor b f x i` as an intermediate fact.

Rewrite `this` using `[h1, map_zero, Finsupp.zero_apply]`. Conclude with `this.symm`. Use `equivFinsuppOfBasisRight_rTensor b g x i` as an intermediate fact. Rewrite `this` using `[h2, map_zero, Finsupp.zero_apply]`. Conclude with `this.symm`.

Establish `: e x = 0` using `Finsupp.ext hc`. Simplify using `using congrArg e.symm this`.
-/
theorem rTensor_eq_zero {K M N P Q ι : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] [AddCommGroup P] [Module K P] [AddCommGroup Q] [Module K Q]
    (b : Module.Basis ι K M) (f : N →ₗ[K] P) (g : N →ₗ[K] Q) (hfg : ∀ n, f n = 0 → g n = 0 → n = 0)
    (x : N ⊗[K] M) (h1 : LinearMap.rTensor M f x = 0) (h2 : LinearMap.rTensor M g x = 0) : x = 0 := by
  classical
  let e := TensorProduct.equivFinsuppOfBasisRight (M := N) b
  have hc : ∀ i, e x i = 0 := by
    intro i
    apply hfg
    · have := equivFinsuppOfBasisRight_rTensor b f x i
      rw [h1, map_zero, Finsupp.zero_apply] at this
      exact this.symm
    · have := equivFinsuppOfBasisRight_rTensor b g x i
      rw [h2, map_zero, Finsupp.zero_apply] at this
      exact this.symm
  have : e x = 0 := Finsupp.ext hc
  simpa using congrArg e.symm this

/- English proof (translation)
Set `b` to `Module.finBasis D.host.F D.host.E`. Use `rTensor_eq_zero b (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA D.host.F).toLinearMap (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA D.host.F).toLinearMap (fun n hf hs => Prod.ext hf hs) x ?_ ?_` and prove the remaining obligations. Rewrite using `[← h1]`. Use `clear h1 h2`. Proceed by induction on `x using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul m n => rfl`. Consider the case `add x y hx hy => rw [LinearMap.map_add, RingHom.map_add, hx, hy]`. Rewrite using `[← h2]`. Use `clear h1 h2`.

Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul m n => rfl`. Consider the case `add x y hx hy => rw [LinearMap.map_add, RingHom.map_add, hx, hy]`.
-/
theorem AE_eq_zero (D : D7) (x : Formalism.L2.Theta.AE D) (h1 : Formalism.L2.Theta.infPart D x = 0)
    (h2 : Formalism.L2.Theta.finPart D x = 0) : x = 0 := by
  classical
  let b := Module.finBasis D.host.F D.host.E
  refine rTensor_eq_zero b (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA D.host.F).toLinearMap (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA D.host.F).toLinearMap
    (fun n hf hs => Prod.ext hf hs) x ?_ ?_
  · rw [← h1]; clear h1 h2
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul m n => rfl
    | add x y hx hy => rw [LinearMap.map_add, RingHom.map_add, hx, hy]
  · rw [← h2]; clear h1 h2
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul m n => rfl
    | add x y hx hy => rw [LinearMap.map_add, RingHom.map_add, hx, hy]

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Introduce `D s hF p c hπ a ha0 haf`. Take `⟨he2, hec, v, ε, ⟨α, rfl, hα1, hα0⟩, hsum⟩` from `p.split`. Rewrite using `[hsum]`. Establish `hι1 : p.ι 1 = p.e`. Use `p.ι_π 1` as an intermediate fact.

Rewrite `this` using `[map_one, mul_one]`. Then use the resulting hypothesis. Establish `hπe : p.π p.e = 1` using `by rw [← hι1, p.π_ι]`. Establish `hee : p.e * algebraMap (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) (Formalism.L2.Theta.AE D) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.pairA D.host.F 0 α) = p.e`. Rewrite using `[← hsum, mul_add, he2, hec, add_zero]`. Establish `hfin : Formalism.L2.Theta.finPart D (algebraMap (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) (Formalism.L2.Theta.AE D) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.pairA D.host.F 0 α)) = α ⊗ₜ[D.host.F] (1 : D.host.E)` using `rfl`.

Take `⟨w, α', hT, hw1, hw0⟩` from `tensCast_tmul_one hF v α hα1 hα0`. Establish `hws : w = s.v`. Assume the negation of the conclusion as `hne`. Establish `h0 : α' s.v = 0` using `hw0 s.v (Ne.symm hne)`. Establish `hz : p.π (algebraMap (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) (Formalism.L2.Theta.AE D) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.pairA D.host.F 0 α)) = 0`.

Rewrite using `[hπ, hfin, hT]`. Establish `: s.proj ((1 : D.host.E) ⊗ₜ α') = 0`. Rewrite using `[SplitPlace.proj, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.lift_tmul, map_one, one_mul]`. Conclude with `h0`. Rewrite using `[this, map_zero]`.

Use `congrArg p.π hee` as an intermediate fact. Rewrite `this` using `[map_mul, hz, mul_zero, hπe]`. Conclude with `zero_ne_one this`. Substitute `hws` using the available equality. Use `set x := algebraMap (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) (Formalism.L2.Theta.AE D) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.pairA D.host.F 0 α) with hx`.

It suffices to establish `hb : x * a - a = 0 from sub_eq_zero.mp hb`. Apply `AE_eq_zero D` to reduce the goal to its premises. Rewrite using `[RingHom.map_sub, RingHom.map_mul, ha0, mul_zero, sub_zero]`. Establish `key : GlobalTheory.NJoin.tensCast hF (Formalism.L2.Theta.finPart D (x * a - a)) = 0`. Apply `GlobalTheory.AL_eq_zero_of_compAt` to reduce the goal to its premises.

Introduce `v''`. Rewrite using `[(Formalism.L2.Theta.finPart D).map_sub, (Formalism.L2.Theta.finPart D).map_mul, (GlobalTheory.NJoin.tensCast hF).map_sub, (GlobalTheory.NJoin.tensCast hF).map_mul, (compAt D.host.E v'').map_sub, (compAt D.host.E v'').map_mul, hfin, hT]`. Distinguish the cases in `hv : v'' = s.v`. Substitute `hv` using the available equality. Establish `: compAt D.host.E s.v ((1 : D.host.E) ⊗ₜ α') = 1`.

Rewrite using `[compAt, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]`. Express the relevant statement in the definitionally equal form `(1 : D.host.E) ⊗ₜ (α' s.v) = 1`. Rewrite using `[hw1]`. Both sides reduce to the same expression. Rewrite using `[this, one_mul, sub_self]`.

Rewrite using `[haf v'' hv, mul_zero, sub_zero]`. Conclude with `(GlobalTheory.NJoin.tensCast hF).map_eq_zero_iff.mp key`.
-/
theorem idem_mul_eq_self : ∀ (D : D7) (s : SplitPlace D.host.E) (hF : D.host.F = maximalRealSubfield D.host.E) (p : GlobalTheory.LocMod.Place D (s.w.adicCompletion D.host.E)) (c : s.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* s.w.adicCompletion D.host.E), (∀ a : Formalism.L2.Theta.AE D, p.π a = c (s.proj (GlobalTheory.NJoin.tensCast hF (Formalism.L2.Theta.finPart D a)))) → ∀ a : Formalism.L2.Theta.AE D, Formalism.L2.Theta.infPart D a = 0 → (∀ v' : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)), v' ≠ s.v → ReciprocityTheory.Aut.compAt D.host.E v' (GlobalTheory.NJoin.tensCast hF (Formalism.L2.Theta.finPart D a)) = 0) → (p.e + Formalism.L2.Theta.cA D p.e) * a = a := by
  intro D s hF p c hπ a ha0 haf
  obtain ⟨he2, hec, v, ε, ⟨α, rfl, hα1, hα0⟩, hsum⟩ := p.split
  rw [hsum]
  have hι1 : p.ι 1 = p.e := by
    have := p.ι_π 1
    rwa [map_one, mul_one] at this
  have hπe : p.π p.e = 1 := by rw [← hι1, p.π_ι]
  have hee : p.e * algebraMap (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) (Formalism.L2.Theta.AE D) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.pairA D.host.F 0 α) = p.e := by
    rw [← hsum, mul_add, he2, hec, add_zero]
  have hfin : Formalism.L2.Theta.finPart D (algebraMap (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) (Formalism.L2.Theta.AE D)
      (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.pairA D.host.F 0 α)) = α ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
  obtain ⟨w, α', hT, hw1, hw0⟩ := tensCast_tmul_one hF v α hα1 hα0
  have hws : w = s.v := by
    by_contra hne
    have h0 : α' s.v = 0 := hw0 s.v (Ne.symm hne)
    have hz : p.π (algebraMap (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) (Formalism.L2.Theta.AE D) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.pairA D.host.F 0 α)) = 0 := by
      rw [hπ, hfin, hT]
      have : s.proj ((1 : D.host.E) ⊗ₜ α') = 0 := by
        rw [SplitPlace.proj, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
        exact h0
      rw [this, map_zero]
    have := congrArg p.π hee
    rw [map_mul, hz, mul_zero, hπe] at this
    exact zero_ne_one this
  subst hws
  set x := algebraMap (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) (Formalism.L2.Theta.AE D) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.pairA D.host.F 0 α) with hx
  suffices hb : x * a - a = 0 from sub_eq_zero.mp hb
  apply AE_eq_zero D
  · rw [RingHom.map_sub, RingHom.map_mul, ha0, mul_zero, sub_zero]
  · have key : GlobalTheory.NJoin.tensCast hF (Formalism.L2.Theta.finPart D (x * a - a)) = 0 := by
      apply GlobalTheory.AL_eq_zero_of_compAt
      intro v''
      rw [(Formalism.L2.Theta.finPart D).map_sub, (Formalism.L2.Theta.finPart D).map_mul, (GlobalTheory.NJoin.tensCast hF).map_sub,
        (GlobalTheory.NJoin.tensCast hF).map_mul, (compAt D.host.E v'').map_sub, (compAt D.host.E v'').map_mul, hfin, hT]
      by_cases hv : v'' = s.v
      · subst hv
        have : compAt D.host.E s.v ((1 : D.host.E) ⊗ₜ α') = 1 := by
          rw [compAt, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
          change (1 : D.host.E) ⊗ₜ (α' s.v) = 1
          rw [hw1]
          rfl
        rw [this, one_mul, sub_self]
      · rw [haf v'' hv, mul_zero, sub_zero]
    exact (GlobalTheory.NJoin.tensCast hF).map_eq_zero_iff.mp key

end GlobalTheory.PlaceSupp
