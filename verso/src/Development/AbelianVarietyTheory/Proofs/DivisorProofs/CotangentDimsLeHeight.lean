import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowFinrankCotangentLeFinrankFrobeniusKernelQuotiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativeFrobeniusKernelIdealLeFrobeniusKernelIdeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapMapEqSelfOfInjectiveFiniteHopfStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulPMemFrobeniusKernelOfVerschiebungEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFrobeniusDualAddFinrankKerVerschiebungStatement
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PDivGroup.CotDim

/- English proof (translation)
Set `f : (A ⧸ I) →ₗ[k] (A ⧸ J)` to `(Ideal.Quotient.factorₐ k hIJ).toLinearMap`. Establish `hf : Function.Surjective f` using `Ideal.Quotient.factor_surjective hIJ`. Use `LinearMap.finrank_range_le f` as an intermediate fact. Rewrite `this` using `[LinearMap.range_eq_top.2 hf, finrank_top]`. Then use the resulting hypothesis.
-/
theorem quot_finrank_le {k A : Type} [Field k] [CommRing A] [Algebra k A] [Module.Finite k A]
    {I J : Ideal A} (hIJ : I ≤ J) : Module.finrank k (A ⧸ J) ≤ Module.finrank k (A ⧸ I) := by
  let f : (A ⧸ I) →ₗ[k] (A ⧸ J) := (Ideal.Quotient.factorₐ k hIJ).toLinearMap
  have hf : Function.Surjective f := Ideal.Quotient.factor_surjective hIJ
  have := LinearMap.finrank_range_le f
  rwa [LinearMap.range_eq_top.2 hf, finrank_top] at this

/- English proof (translation)
Take `⟨q⟩ : Nonempty (PrimeSpectrum k)` from `inferInstance`. Establish `h` using `G.rank_eq 1 q`. Rewrite `h` using `[Module.rankAtStalk_eq_finrank_of_free]`. Simplify using `using h`.
-/
theorem finrank_level_one {p : ℕ} {k : Type} [Field k] (G : PDivGroup p k) :
    Module.finrank k (G.A 1) = p ^ G.height := by
  obtain ⟨q⟩ : Nonempty (PrimeSpectrum k) := inferInstance
  have h := G.rank_eq 1 q
  rw [Module.rankAtStalk_eq_finrank_of_free] at h
  simpa using h

end GlobalTheory.PDivGroup.CotDim

open GlobalTheory.PDivGroup.CotDim in

/- English proof (translation)
Establish `hp : (p : k) = 0` using `CharP.cast_eq_zero k p`. Establish `hp2 : 2 ≤ p` using `(Fact.out : p.Prime).two_le`. Establish `hdimD` using `finrank_level_one Γ.dual`. Establish `hmulP : Function.Injective (Γ.mulP 1)` using `fun a b e => by`. Use `CartierDual.eq_of_forall_apply (R := k) fun φ => ?_` and prove the remaining obligations.

Take `⟨ψ, rfl⟩` from `Γ.dual_mulP_surjective 1 φ`. Express the relevant statement in the definitionally equal form `ψ.ofConv (Γ.mulP 1 a) = ψ.ofConv (Γ.mulP 1 b)`. Rewrite using `[e]`. Establish `hord` using `finrank_eq_ker_mul_range k (Γ.dual.A 1) _ ((relFrob hp Γ.dual).app 1)`. Establish `haD : p ^ Module.finrank k (Cot k (Γ.dual.A 1)) ≤ Module.finrank k (Γ.dual.A 1 ⧸ kerIdeal ((relFrob hp Γ.dual).app 1))` using `(GlobalTheory.T.pow_finrank_cotangent_le_finrank_frobeniusKernelQuotient p k (Γ.dual.A 1)).trans (quot_finrank_le (GlobalTheory.T.relativeFrobeniusKernelIdeal_le_frobeniusKernelIdeal p k hp Γ.dual 1))`.

Establish `hker : LinearMap.ker ((verschiebung hp Γ).app 1 : Γ.A 1 →ₐ[k] (frobTwist hp Γ).A 1).toLinearMap ≤ (kerIdeal ((relFrob hp Γ).app 1)).restrictScalars k` using `fun a ha => by`. Establish `h1` using `GlobalTheory.T.mulP_mem_kerIdeal_comp_relFrob_of_verschiebung_eq_zero p k hp Γ a ha`. Rewrite `h1` using `[kerIdeal_comp]`. Rewrite using `[Submodule.restrictScalars_mem, ← GlobalTheory.T.comap_map_eq_self_of_injective_finiteHopf k _ _ (Γ.mulP 1) hmulP (kerIdeal ((relFrob hp Γ).app 1))]`. Conclude with `h1`.

Establish `hV` using `GlobalTheory.T.finrank_frobeniusDual_add_finrank_ker_verschiebung p k hp Γ`. Establish `hq` using `Submodule.finrank_quotient_add_finrank ((kerIdeal ((relFrob hp Γ).app 1)).restrictScalars k)`. Rewrite `hq` using `[(Submodule.Quotient.restrictScalarsEquiv k (kerIdeal ((relFrob hp Γ).app 1))).finrank_eq]`. Establish `hmono` using `Submodule.finrank_mono hker`. Establish `haA : p ^ Module.finrank k (Cot k (Γ.A 1)) ≤ Module.finrank k (Γ.A 1 ⧸ kerIdeal ((relFrob hp Γ).app 1))` using `(GlobalTheory.T.pow_finrank_cotangent_le_finrank_frobeniusKernelQuotient p k (Γ.A 1)).trans (quot_finrank_le (GlobalTheory.T.relativeFrobeniusKernelIdeal_le_frobeniusKernelIdeal p k hp Γ 1))`.

Establish `hrD : Module.finrank k (Γ.A 1 ⧸ kerIdeal ((relFrob hp Γ).app 1)) ≤ Module.finrank k (LinearMap.range ((relFrob hp Γ.dual).app 1 : (frobTwist hp Γ.dual).A 1 →ₐ[k] Γ.dual.A 1).toLinearMap)` using `by omega`. Establish `key : p ^ (Module.finrank k (Cot k (Γ.A 1)) + Module.finrank k (Cot k (Γ.dual.A 1))) ≤ p ^ Γ.height`. Rewrite using `[pow_add, mul_comm, ← hdimD, hord]`. Conclude with `Nat.mul_le_mul haD (haA.trans hrD)`. Conclude with `(Nat.pow_le_pow_iff_right hp2).1 key`.
-/
theorem GlobalTheory.PDivGroup.finrank_cot_add_finrank_cot_dual_le (p : ℕ) [Fact p.Prime] (k : Type) [Field k]
    [IsAlgClosed k] [CharP k p] (Γ : PDivGroup p k) :
    Module.finrank k (Cot k (Γ.A 1)) + Module.finrank k (Cot k (Γ.dual.A 1)) ≤ Γ.height := by
  have hp : (p : k) = 0 := CharP.cast_eq_zero k p
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hdimD := finrank_level_one Γ.dual
  have hmulP : Function.Injective (Γ.mulP 1) := fun a b e => by
    refine CartierDual.eq_of_forall_apply (R := k) fun φ => ?_
    obtain ⟨ψ, rfl⟩ := Γ.dual_mulP_surjective 1 φ
    change ψ.ofConv (Γ.mulP 1 a) = ψ.ofConv (Γ.mulP 1 b)
    rw [e]

  have hord := finrank_eq_ker_mul_range k (Γ.dual.A 1) _ ((relFrob hp Γ.dual).app 1)
  have haD : p ^ Module.finrank k (Cot k (Γ.dual.A 1)) ≤
      Module.finrank k (Γ.dual.A 1 ⧸ kerIdeal ((relFrob hp Γ.dual).app 1)) :=
    (GlobalTheory.T.pow_finrank_cotangent_le_finrank_frobeniusKernelQuotient p k (Γ.dual.A 1)).trans (quot_finrank_le (GlobalTheory.T.relativeFrobeniusKernelIdeal_le_frobeniusKernelIdeal p k hp Γ.dual 1))

  have hker : LinearMap.ker ((verschiebung hp Γ).app 1 :
        Γ.A 1 →ₐ[k] (frobTwist hp Γ).A 1).toLinearMap ≤
      (kerIdeal ((relFrob hp Γ).app 1)).restrictScalars k := fun a ha => by
    have h1 := GlobalTheory.T.mulP_mem_kerIdeal_comp_relFrob_of_verschiebung_eq_zero p k hp Γ a ha
    rw [kerIdeal_comp] at h1
    rw [Submodule.restrictScalars_mem,
      ← GlobalTheory.T.comap_map_eq_self_of_injective_finiteHopf k _ _ (Γ.mulP 1) hmulP (kerIdeal ((relFrob hp Γ).app 1))]
    exact h1
  have hV := GlobalTheory.T.finrank_frobeniusDual_add_finrank_ker_verschiebung p k hp Γ
  have hq := Submodule.finrank_quotient_add_finrank
    ((kerIdeal ((relFrob hp Γ).app 1)).restrictScalars k)
  rw [(Submodule.Quotient.restrictScalarsEquiv k (kerIdeal ((relFrob hp Γ).app 1))).finrank_eq] at hq
  have hmono := Submodule.finrank_mono hker
  have haA : p ^ Module.finrank k (Cot k (Γ.A 1)) ≤
      Module.finrank k (Γ.A 1 ⧸ kerIdeal ((relFrob hp Γ).app 1)) :=
    (GlobalTheory.T.pow_finrank_cotangent_le_finrank_frobeniusKernelQuotient p k (Γ.A 1)).trans (quot_finrank_le (GlobalTheory.T.relativeFrobeniusKernelIdeal_le_frobeniusKernelIdeal p k hp Γ 1))
  have hrD : Module.finrank k (Γ.A 1 ⧸ kerIdeal ((relFrob hp Γ).app 1)) ≤
      Module.finrank k (LinearMap.range ((relFrob hp Γ.dual).app 1 :
        (frobTwist hp Γ.dual).A 1 →ₐ[k] Γ.dual.A 1).toLinearMap) := by omega
  have key : p ^ (Module.finrank k (Cot k (Γ.A 1)) + Module.finrank k (Cot k (Γ.dual.A 1))) ≤
      p ^ Γ.height := by
    rw [pow_add, mul_comm, ← hdimD, hord]
    exact Nat.mul_le_mul haD (haA.trans hrD)
  exact (Nat.pow_le_pow_iff_right hp2).1 key
