import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LeftEqIffLieVecSmul
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SumEmbeddingDualInt
open NumberField

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT.LatMult

open Module

variable {E : Type} [Field E] [NumberField E] (X : Type) [AddCommGroup X] [Module (𝓞 E) X]
  (k : Type) [Field k]

def pullAct : 𝓞 E →+* Module.End k (X →+ k) where
  toFun a :=
    { toFun := fun c => c.comp (DistribMulAction.toAddMonoidHom X a)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by ext c x; simp
  map_mul' a b := by
    ext c x
    simp [mul_comm a b, mul_smul]
  map_zero' := by ext c x; simp
  map_add' a b := by
    ext c x
    simp [add_smul]

variable {X k}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pullAct_apply (a : 𝓞 E) (c : X →+ k) (x : X) : pullAct X k a c x = c (a • x) := rfl

/- English proof (translation)
Set `b` to `Module.Free.chooseBasis ℤ X`. Set `B` to `GlobalTheory.Diag.dualBasis k b`. Use `⟨∑ i, b.repr (a • b i) i, ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.trace_eq_matrix_trace k B, Matrix.trace]`. Use `push_cast`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.diag_apply, LinearMap.toMatrix_apply, GlobalTheory.Diag.dualBasis_repr, pullAct_apply, GlobalTheory.Diag.dualBasis_apply]`.
-/
theorem trace_pullAct [Module.Free ℤ X] [Module.Finite ℤ X] [FiniteDimensional k (X →+ k)] (a : 𝓞 E) :
    ∃ n : ℤ, LinearMap.trace k (X →+ k) (pullAct X k a) = (n : k) := by
  classical
  let b := Module.Free.chooseBasis ℤ X
  let B := GlobalTheory.Diag.dualBasis k b
  refine ⟨∑ i, b.repr (a • b i) i, ?_⟩
  rw [LinearMap.trace_eq_matrix_trace k B, Matrix.trace]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, GlobalTheory.Diag.dualBasis_repr, pullAct_apply,
    GlobalTheory.Diag.dualBasis_apply]

/- English proof (translation)
Use extensionality with `c`. Establish `hσ : ∀ a : 𝓞 E, σ (a : E) = τ a` using `fun a => by rw [← h]; rfl`. Simplify using `only [GlobalTheory.CompanionTheory.Ar.HT.eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, Module.End.smul_def, Module.End.one_apply, hσ]`. Prove the components needed by the constructor for the conclusion. Introduce `hc a`.

Use extensionality with `x`. Simplify `hc a x` using `[pullAct_apply]`. Introduce `hc a x`. Simplify `DFunLike.congr_fun (hc a) x` using `[pullAct_apply]`.
-/
theorem eigenHom_eq_eigSp (τ : 𝓞 E →+* k) (σ : E →+* k) (h : σ.comp (algebraMap (𝓞 E) E) = τ) :
    GlobalTheory.Diag.eigenHom X τ = GlobalTheory.CompanionTheory.Ar.HT.eigSp (pullAct X k) σ := by
  ext c
  have hσ : ∀ a : 𝓞 E, σ (a : E) = τ a := fun a => by rw [← h]; rfl
  simp only [GlobalTheory.CompanionTheory.Ar.HT.eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    sub_eq_zero, Module.End.smul_def, Module.End.one_apply, hσ]
  constructor
  · intro hc a
    ext x
    simpa [pullAct_apply] using hc a x
  · intro hc a x
    simpa [pullAct_apply] using DFunLike.congr_fun (hc a) x

/- English proof (translation)
Introduce `E _ _ X _ _ _ _ k _ _ _ τ`. Establish `hinj : Function.Injective τ`. Rewrite using `[RingHom.injective_iff_ker_eq_bot]`. Use `Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_` and prove the remaining obligations. Rewrite using `[RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]`.

Conclude with `RingHom.injective_int _`. Set `σ : E →+* k` to `IsFractionRing.lift hinj`. Establish `hσ : σ.comp (algebraMap (𝓞 E) E) = τ` using `RingHom.ext fun a => IsFractionRing.lift_algebraMap hinj a`. Set `b` to `Module.Free.chooseBasis ℤ X`. Set `B` to `GlobalTheory.Diag.dualBasis k b`.

Use `haveI : FiniteDimensional k (X →+ k) := Module.Finite.of_basis B`. Establish `hV : finrank k (X →+ k) = finrank ℤ X`. Rewrite using `[finrank_eq_card_basis B, finrank_eq_card_basis b]`. Establish `hmul` using `GlobalTheory.CompanionTheory.Ar.HT.EigDim.finrank_eigSp_mul k (X →+ k) E (pullAct X k) trace_pullAct σ`. Rewrite `hmul` using `[← eigenHom_eq_eigSp τ σ hσ, hV]`.

Establish `hd : 0 < finrank ℚ E` using `Module.finrank_pos`. Establish `hdim : finrank k (GlobalTheory.Diag.eigenHom X τ) = finrank ℤ X / finrank ℚ E`. Rewrite using `[← hmul, Nat.mul_div_cancel _ hd]`. Use `haveI : FiniteDimensional k (GlobalTheory.Diag.eigenHom X τ) := inferInstance`. Conclude with `⟨Module.finBasisOfFinrankEq _ _ hdim⟩`.
-/
theorem nonempty_basis_eigenHom :
    ∀ (E : Type) [Field E] [NumberField E] (X : Type) [AddCommGroup X] [Module.Free ℤ X]
      [Module.Finite ℤ X] [Module (𝓞 E) X] (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
      (τ : 𝓞 E →+* k),
      Nonempty (Module.Basis (Fin (Module.finrank ℤ X / Module.finrank ℚ E)) k
        (GlobalTheory.Diag.eigenHom X τ)) := by
  intro E _ _ X _ _ _ _ k _ _ _ τ
  classical
  have hinj : Function.Injective τ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_
    rw [RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
    exact RingHom.injective_int _
  let σ : E →+* k := IsFractionRing.lift hinj
  have hσ : σ.comp (algebraMap (𝓞 E) E) = τ :=
    RingHom.ext fun a => IsFractionRing.lift_algebraMap hinj a
  let b := Module.Free.chooseBasis ℤ X
  let B := GlobalTheory.Diag.dualBasis k b
  haveI : FiniteDimensional k (X →+ k) := Module.Finite.of_basis B
  have hV : finrank k (X →+ k) = finrank ℤ X := by
    rw [finrank_eq_card_basis B, finrank_eq_card_basis b]
  have hmul := GlobalTheory.CompanionTheory.Ar.HT.EigDim.finrank_eigSp_mul k (X →+ k) E (pullAct X k)
    trace_pullAct σ
  rw [← eigenHom_eq_eigSp τ σ hσ, hV] at hmul
  have hd : 0 < finrank ℚ E := Module.finrank_pos
  have hdim : finrank k (GlobalTheory.Diag.eigenHom X τ) = finrank ℤ X / finrank ℚ E := by
    rw [← hmul, Nat.mul_div_cancel _ hd]
  haveI : FiniteDimensional k (GlobalTheory.Diag.eigenHom X τ) := inferInstance
  exact ⟨Module.finBasisOfFinrankEq _ _ hdim⟩

end GlobalTheory.CompanionTheory.Ar.HT.LatMult
