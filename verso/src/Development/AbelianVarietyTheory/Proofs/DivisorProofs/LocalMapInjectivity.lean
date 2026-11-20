import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSigmaLiftW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicTensorNumberFieldIsReduced
import GroundTheory.Brauer.TensorSimple
open NumberField IsDedekindDomain GlobalTheory.LKMid GlobalTheory.LKTrip GlobalTheory.LKRes
open scoped TensorProduct

namespace GlobalTheory.HTGroupLocInj
variable {p : ℕ} [Fact p.Prime] (G : HTGroup p)

noncomputable def iotaZ : ℚ_[p] ⊗[ℚ] G.F →ₐ[ℚ_[p]] ℚ_[p] ⊗[ℚ] G.C :=
  Algebra.TensorProduct.map (AlgHom.id ℚ_[p] ℚ_[p]) (IsScalarTower.toAlgHom ℚ G.F G.C)

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a y`. Express the relevant statement in the definitionally equal form `(Algebra.ofId ℚ_[p] (Matrix (Fin G.n) (Fin G.n) (G.Fw i)) a) * (G.rho i (algebraMap G.F G.C y)) = algebraMap (G.Fw i) _ (algebraMap ℚ_[p] (G.Fw i) a * G.embW i y)`. Rewrite using `[G.rho_F, Algebra.ofId_apply, map_mul, ← IsScalarTower.algebraMap_apply]`.

Use `congr 1`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem locW_iotaZ (i : Fin G.m) (z : ℚ_[p] ⊗[ℚ] G.F) :
    G.locW i (iotaZ G z) = algebraMap (G.Fw i) (Matrix (Fin G.n) (Fin G.n) (G.Fw i)) (G.liftW i z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a y =>
    change (Algebra.ofId ℚ_[p] (Matrix (Fin G.n) (Fin G.n) (G.Fw i)) a) * (G.rho i (algebraMap G.F G.C y)) =
      algebraMap (G.Fw i) _ (algebraMap ℚ_[p] (G.Fw i) a * G.embW i y)
    rw [G.rho_F, Algebra.ofId_apply, map_mul, ← IsScalarTower.algebraMap_apply]
    congr 1
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a y`. Simplify using `[iotaZ, starT_tmul, G.star_F]`. Consider the case `add x y hx hy => simp only [map_add, MulOpposite.unop_add, hx, hy]`.
-/
theorem starT_iotaZ (z : ℚ_[p] ⊗[ℚ] G.F) :
    (starT G.star ℚ_[p] (iotaZ G z)).unop = iotaZ G (conjT G.F ℚ_[p] z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a y =>
    simp [iotaZ, starT_tmul, G.star_F]
  | add x y hx hy => simp only [map_add, MulOpposite.unop_add, hx, hy]

/- English proof (translation)
Establish `hJ : z ∈ (⊥ : Ideal (ℚ_[p] ⊗[ℚ] G.F)).jacobson`. Rewrite using `[Ideal.jacobson, Ideal.mem_sInf]`. Introduce and unpack `M ⟨-, hM⟩`. Apply the tactic sequence `obtain ⟨i, hi | hi⟩ := GlobalTheory.MaxIdealTensorPadic.main p G M hM <;> rw [hi, RingHom.mem_ker]`. Conclude with `h1 i`.

Conclude with `h2 i`. Use `haveI : IsArtinianRing (ℚ_[p] ⊗[ℚ] G.F) := IsArtinianRing.of_finite ℚ_[p] _`. Take `⟨k, hk⟩` from `IsArtinianRing.isNilpotent_jacobson_bot (R := ℚ_[p] ⊗[ℚ] G.F)`. Establish `hk0 : z ^ k = 0`. Use `Ideal.pow_mem_pow hJ k` as an intermediate fact.

Rewrite `this` using `[hk]`. Simplify using `using this`. Use `haveI := GlobalTheory.padic_tensor_numberField_isReduced p G.F`. Conclude with `IsReduced.eq_zero _ ⟨k, hk0⟩`.
-/
theorem inj_Z (z : ℚ_[p] ⊗[ℚ] G.F) (h1 : ∀ i, G.liftW i z = 0) (h2 : ∀ i, G.liftW i (conjT G.F ℚ_[p] z) = 0) :
    z = 0 := by
  have hJ : z ∈ (⊥ : Ideal (ℚ_[p] ⊗[ℚ] G.F)).jacobson := by
    rw [Ideal.jacobson, Ideal.mem_sInf]
    rintro M ⟨-, hM⟩
    obtain ⟨i, hi | hi⟩ := GlobalTheory.MaxIdealTensorPadic.main p G M hM <;> rw [hi, RingHom.mem_ker]
    · exact h1 i
    · exact h2 i
  haveI : IsArtinianRing (ℚ_[p] ⊗[ℚ] G.F) := IsArtinianRing.of_finite ℚ_[p] _
  obtain ⟨k, hk⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := ℚ_[p] ⊗[ℚ] G.F)
  have hk0 : z ^ k = 0 := by
    have := Ideal.pow_mem_pow hJ k
    rw [hk] at this
    simpa using this
  haveI := GlobalTheory.padic_tensor_numberField_isReduced p G.F
  exact IsReduced.eq_zero _ ⟨k, hk0⟩

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => rw [map_add]`. Conclude with `hx.add_right hy`. Consider the case `tmul a y`.

Proceed by induction on `d using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => exact hx.add_left hy`. Consider the case `tmul b c`. Simplify using `only [iotaZ, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, IsScalarTower.coe_toAlgHom']`.

Use `show (b ⊗ₜ c) * (a ⊗ₜ algebraMap G.F G.C y) = (a ⊗ₜ algebraMap G.F G.C y) * (b ⊗ₜ c)`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_comm b a, Algebra.commutes]`.
-/
theorem iotaZ_comm (d : ℚ_[p] ⊗[ℚ] G.C) (z : ℚ_[p] ⊗[ℚ] G.F) : Commute d (iotaZ G z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add]; exact hx.add_right hy
  | tmul a y =>
    induction d using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => exact hx.add_left hy
    | tmul b c =>
      simp only [iotaZ, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, IsScalarTower.coe_toAlgHom']
      show (b ⊗ₜ c) * (a ⊗ₜ algebraMap G.F G.C y) = (a ⊗ₜ algebraMap G.F G.C y) * (b ⊗ₜ c)
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_comm b a,
        Algebra.commutes]

/- English proof (translation)
Use `letI algD : Algebra G.F (ℚ_[p] ⊗[ℚ] G.C) := RingHom.toAlgebra' ((iotaZ G).toRingHom.comp (Algebra.TensorProduct.includeRight.toRingHom)) (by`. Introduce `c d`. Use `show iotaZ G ((1 : ℚ_[p]) ⊗ₜ c) * d = d * iotaZ G ((1 : ℚ_[p]) ⊗ₜ c)`. Conclude with `(iotaZ_comm G d _).symm.eq)`. Use `letI algZ : Algebra G.F (ℚ_[p] ⊗[ℚ] G.F) := Algebra.TensorProduct.rightAlgebra`.

Set `f : G.C →ₐ[G.F] ℚ_[p] ⊗[ℚ] G.C` to `{ (Algebra.TensorProduct.includeRight : G.C →ₐ[ℚ] ℚ_[p] ⊗[ℚ] G.C).toRingHom with commutes' := fun c => by show (1 : ℚ_[p]) ⊗ₜ algebraMap G.F G.C c = iotaZ G ((1 : ℚ_[p]) ⊗ₜ c)`. Simplify using `[iotaZ] }`. Set `g : (ℚ_[p] ⊗[ℚ] G.F) →ₐ[G.F] ℚ_[p] ⊗[ℚ] G.C` to `{ (iotaZ G).toRingHom with commutes' := fun c => rfl }`. Set `Φ` to `Algebra.TensorProduct.lift f g (fun c z => iotaZ_comm G _ _)`. Establish `hΦ1 : ∀ z, Φ ((1 : G.C) ⊗ₜ z) = iotaZ G z` using `fun z => by`.

Rewrite using `[Algebra.TensorProduct.lift_tmul, map_one, one_mul]`. Both sides reduce to the same expression. Establish `hΦs : Function.Surjective Φ`. Introduce `d`. Proceed by induction on `d using TensorProduct.induction_on with`.

Consider the case `zero => exact ⟨0, map_zero _⟩`. Consider the case `tmul a c`. Use `⟨c ⊗ₜ (a ⊗ₜ (1 : G.F)), ?_⟩` and prove the remaining obligations. Rewrite using `[Algebra.TensorProduct.lift_tmul]`. Use `show ((1 : ℚ_[p]) ⊗ₜ c) * iotaZ G (a ⊗ₜ 1) = a ⊗ₜ c`.

Simplify using `[iotaZ, Algebra.TensorProduct.tmul_mul_tmul]`. Consider the case `add x y hx hy`. Take `⟨x', rfl⟩` from `hx`. Take `⟨y', rfl⟩` from `hy`. Conclude with `⟨x' + y', map_add _ _ _⟩`.

Set `ψ : ℚ_[p] ⊗[ℚ] G.C →+* ((i : Fin G.m) → Matrix (Fin G.n) (Fin G.n) (G.Fw i)) × ((i : Fin G.m) → (Matrix (Fin G.n) (Fin G.n) (G.Fw i))ᵐᵒᵖ)` to `RingHom.prod (RingHom.pi fun i => (G.locW i).toRingHom) (RingHom.pi fun i => (RingHom.op (G.locW i).toRingHom).comp (starT G.star ℚ_[p]))`. Establish `hψ : ∀ d, ψ d = 0 ↔ (∀ i, G.locW i d = 0) ∧ ∀ i, G.locW i (starT G.star ℚ_[p] d).unop = 0`. Introduce `d`. Simplify using `only [ψ, Prod.ext_iff, funext_iff, RingHom.prod_apply, Pi.ringHom_apply, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, RingHom.comp_apply]`. Use `and_congr Iff.rfl (forall_congr' fun i => ?_)` and prove the remaining obligations.

Rewrite using `[← MulOpposite.unop_inj]`. Both sides reduce to the same expression. Set `J : TwoSidedIdeal (G.C ⊗[G.F] (ℚ_[p] ⊗[ℚ] G.F))` to `TwoSidedIdeal.ker (ψ.comp Φ.toRingHom)`. Establish `hJ : J = ⊥`. Assume the negation of the conclusion as `hne`.

Take `⟨z, hz0, hz⟩` from `GroundTheory.Brauer.exists_one_tmul_mem_of_ne_bot J hne`. Apply `hz0` to reduce the goal to its premises. Rewrite `hz` using `[TwoSidedIdeal.mem_ker, RingHom.comp_apply]`. Express the relevant statement in the definitionally equal form `ψ (Φ ((1 : G.C) ⊗ₜ z)) = 0 at hz`. Rewrite `hz` using `[hΦ1, hψ]`.

Use `haveI : Nonempty (Fin G.n) := ⟨⟨0, G.n_pos⟩⟩`. Apply `inj_Z G z` to reduce the goal to its premises. Introduce `i`. Use `hz.1 i` as an intermediate fact. Rewrite `this` using `[locW_iotaZ]`.

Conclude with `(FaithfulSMul.algebraMap_injective (G.Fw i) _) (this.trans (map_zero _).symm)`. Introduce `i`. Use `hz.2 i` as an intermediate fact. Rewrite `this` using `[starT_iotaZ, locW_iotaZ]`. Conclude with `(FaithfulSMul.algebraMap_injective (G.Fw i) _) (this.trans (map_zero _).symm)`.

Take `⟨y, rfl⟩` from `hΦs x`. Establish `hy : y ∈ J`. Rewrite using `[TwoSidedIdeal.mem_ker]`. Conclude with `(hψ _).2 ⟨h1, h2⟩`. Rewrite `hy` using `[hJ, TwoSidedIdeal.mem_bot]`.

Rewrite using `[hy, map_zero]`.
-/
theorem locW_inj (x : ℚ_[p] ⊗[ℚ] G.C) (h1 : ∀ i, G.locW i x = 0)
    (h2 : ∀ i, G.locW i (starT G.star ℚ_[p] x).unop = 0) : x = 0 := by
  classical
  letI algD : Algebra G.F (ℚ_[p] ⊗[ℚ] G.C) :=
    RingHom.toAlgebra' ((iotaZ G).toRingHom.comp (Algebra.TensorProduct.includeRight.toRingHom)) (by
      intro c d
      show iotaZ G ((1 : ℚ_[p]) ⊗ₜ c) * d = d * iotaZ G ((1 : ℚ_[p]) ⊗ₜ c)
      exact (iotaZ_comm G d _).symm.eq)
  letI algZ : Algebra G.F (ℚ_[p] ⊗[ℚ] G.F) := Algebra.TensorProduct.rightAlgebra
  let f : G.C →ₐ[G.F] ℚ_[p] ⊗[ℚ] G.C :=
    { (Algebra.TensorProduct.includeRight : G.C →ₐ[ℚ] ℚ_[p] ⊗[ℚ] G.C).toRingHom with
      commutes' := fun c => by
        show (1 : ℚ_[p]) ⊗ₜ algebraMap G.F G.C c = iotaZ G ((1 : ℚ_[p]) ⊗ₜ c)
        simp [iotaZ] }
  let g : (ℚ_[p] ⊗[ℚ] G.F) →ₐ[G.F] ℚ_[p] ⊗[ℚ] G.C :=
    { (iotaZ G).toRingHom with
      commutes' := fun c => rfl }
  let Φ := Algebra.TensorProduct.lift f g (fun c z => iotaZ_comm G _ _)
  have hΦ1 : ∀ z, Φ ((1 : G.C) ⊗ₜ z) = iotaZ G z := fun z => by
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]; rfl
  have hΦs : Function.Surjective Φ := by
    intro d
    induction d using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul a c =>
      refine ⟨c ⊗ₜ (a ⊗ₜ (1 : G.F)), ?_⟩
      rw [Algebra.TensorProduct.lift_tmul]
      show ((1 : ℚ_[p]) ⊗ₜ c) * iotaZ G (a ⊗ₜ 1) = a ⊗ₜ c
      simp [iotaZ, Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy =>
      obtain ⟨x', rfl⟩ := hx
      obtain ⟨y', rfl⟩ := hy
      exact ⟨x' + y', map_add _ _ _⟩
  let ψ : ℚ_[p] ⊗[ℚ] G.C →+* ((i : Fin G.m) → Matrix (Fin G.n) (Fin G.n) (G.Fw i)) ×
      ((i : Fin G.m) → (Matrix (Fin G.n) (Fin G.n) (G.Fw i))ᵐᵒᵖ) :=
    RingHom.prod (RingHom.pi fun i => (G.locW i).toRingHom)
      (RingHom.pi fun i => (RingHom.op (G.locW i).toRingHom).comp (starT G.star ℚ_[p]))
  have hψ : ∀ d, ψ d = 0 ↔ (∀ i, G.locW i d = 0) ∧ ∀ i, G.locW i (starT G.star ℚ_[p] d).unop = 0 := by
    intro d
    simp only [ψ, Prod.ext_iff, funext_iff, RingHom.prod_apply, Pi.ringHom_apply, Prod.fst_zero, Prod.snd_zero,
      Pi.zero_apply, RingHom.comp_apply]
    refine and_congr Iff.rfl (forall_congr' fun i => ?_)
    rw [← MulOpposite.unop_inj]
    rfl
  let J : TwoSidedIdeal (G.C ⊗[G.F] (ℚ_[p] ⊗[ℚ] G.F)) := TwoSidedIdeal.ker (ψ.comp Φ.toRingHom)
  have hJ : J = ⊥ := by
    by_contra hne
    obtain ⟨z, hz0, hz⟩ := GroundTheory.Brauer.exists_one_tmul_mem_of_ne_bot J hne
    apply hz0
    rw [TwoSidedIdeal.mem_ker, RingHom.comp_apply] at hz
    change ψ (Φ ((1 : G.C) ⊗ₜ z)) = 0 at hz
    rw [hΦ1, hψ] at hz
    haveI : Nonempty (Fin G.n) := ⟨⟨0, G.n_pos⟩⟩
    apply inj_Z G z
    · intro i
      have := hz.1 i
      rw [locW_iotaZ] at this
      exact (FaithfulSMul.algebraMap_injective (G.Fw i) _) (this.trans (map_zero _).symm)
    · intro i
      have := hz.2 i
      rw [starT_iotaZ, locW_iotaZ] at this
      exact (FaithfulSMul.algebraMap_injective (G.Fw i) _) (this.trans (map_zero _).symm)
  obtain ⟨y, rfl⟩ := hΦs x
  have hy : y ∈ J := by
    rw [TwoSidedIdeal.mem_ker]
    exact (hψ _).2 ⟨h1, h2⟩
  rw [hJ, TwoSidedIdeal.mem_bot] at hy
  rw [hy, map_zero]

end GlobalTheory.HTGroupLocInj
