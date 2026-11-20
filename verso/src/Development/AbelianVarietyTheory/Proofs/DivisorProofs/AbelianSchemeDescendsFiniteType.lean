import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FormalAlgebraisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescendsToFinitelyGeneratedSubring

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.AbelianLimit

/- English proof (translation)
Introduce `R _ A _ F hA`. Use `hA.comm` as an intermediate fact. Use `hA.proper` as an intermediate fact. Take `⟨k, A₀, _, _, φ₀, hF, hk, _, _, _, h₀⟩` from `smooth_grpScheme_descends_to_fg_subring R A F hA.smooth inferInstance inferInstance`. Establish `: IsNoetherianRing k` using `Algebra.FiniteType.isNoetherianRing ℤ k`.

Establish `h₁ : IsPullback φ₀ A.hom A₀.hom (spMap (algebraMap k R))` using `h₀.1`. Establish `: UniversallyClosed (pullback.snd A₀.hom (spMap (algebraMap k R)))`. Rewrite using `[← h₁.isoPullback_inv_snd]`. Use `infer_instance`. Take `⟨s, hs⟩` from `ProperLimit.exists_finset_isProper k R A₀.hom`.

Set `S : Subalgebra k R` to `Algebra.adjoin k (s : Set R)`. Set `t : Sp S.toSubring ⟶ Sp k` to `spMap (algebraMap k S)`. Establish `e : spMap S.toSubring.subtype ≫ t = spMap k.subtype` using `Spread.spMap_algHom_comp S.val`. Take `⟨φ, hφ⟩` from `GoodVal.exists_isGrpPullback_of_comp A₀ t (spMap S.toSubring.subtype) (e ▸ h₀)`. Establish `: Smooth ((Over.pullback t).obj A₀).hom` using `inferInstanceAs (Smooth (pullback.snd A₀.hom t))`.

Establish `: IsProper ((Over.pullback t).obj A₀).hom` using `hs`. Establish `hd : IsDominant (spMap S.toSubring.subtype)` using `⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical S.toSubring.subtype).2 (by`. Rewrite using `[(RingHom.injective_iff_ker_eq_bot _).1 Subtype.val_injective]`. Conclude with `bot_le)⟩`. Conclude with `⟨S.toSubring, (Over.pullback t).obj A₀, inferInstance, φ, fun x hx => S.algebraMap_mem ⟨x, hF hx⟩, SpreadGroup.finiteType_of_fg hk (Subalgebra.fg_adjoin_finset s), isAbelianScheme_of_isDominant hφ hA, hφ⟩`.
-/
theorem abelianScheme_descends_to_fg_subring_anyDim :
    ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (F : Finset R), IsAbelianScheme A →
    ∃ (S : Subring R) (B : Over (Sp S)) (_ : GrpObj B) (φ : A.left ⟶ B.left), (F : Set R) ⊆ S ∧
      Algebra.FiniteType ℤ S ∧ IsAbelianScheme B ∧ IsGrpPullback A B (spMap S.subtype) φ := by
  intro R _ A _ F hA
  have := hA.comm
  have := hA.proper
  obtain ⟨k, A₀, _, _, φ₀, hF, hk, _, _, _, h₀⟩ :=
    smooth_grpScheme_descends_to_fg_subring R A F hA.smooth inferInstance inferInstance
  have : IsNoetherianRing k := Algebra.FiniteType.isNoetherianRing ℤ k
  have h₁ : IsPullback φ₀ A.hom A₀.hom (spMap (algebraMap k R)) := h₀.1
  have : UniversallyClosed (pullback.snd A₀.hom (spMap (algebraMap k R))) := by
    rw [← h₁.isoPullback_inv_snd]
    infer_instance
  obtain ⟨s, hs⟩ := ProperLimit.exists_finset_isProper k R A₀.hom
  let S : Subalgebra k R := Algebra.adjoin k (s : Set R)
  let t : Sp S.toSubring ⟶ Sp k := spMap (algebraMap k S)
  have e : spMap S.toSubring.subtype ≫ t = spMap k.subtype := Spread.spMap_algHom_comp S.val
  obtain ⟨φ, hφ⟩ := GoodVal.exists_isGrpPullback_of_comp A₀ t (spMap S.toSubring.subtype) (e ▸ h₀)
  have : Smooth ((Over.pullback t).obj A₀).hom := inferInstanceAs (Smooth (pullback.snd A₀.hom t))
  have : IsProper ((Over.pullback t).obj A₀).hom := hs
  have hd : IsDominant (spMap S.toSubring.subtype) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical S.toSubring.subtype).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 Subtype.val_injective]
      exact bot_le)⟩
  exact ⟨S.toSubring, (Over.pullback t).obj A₀, inferInstance, φ, fun x hx => S.algebraMap_mem ⟨x, hF hx⟩,
    SpreadGroup.finiteType_of_fg hk (Subalgebra.fg_adjoin_finset s), isAbelianScheme_of_isDominant hφ hA, hφ⟩

end GlobalTheory.AbelianLimit
