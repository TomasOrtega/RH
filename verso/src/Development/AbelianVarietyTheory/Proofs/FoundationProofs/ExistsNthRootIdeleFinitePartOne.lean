import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RealAdelesCmFieldEquivComplexCmType

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IdeleDiv

/- English proof (translation)
Take `⟨⟨θ, hθ⟩, H⟩` from `GlobalTheory.Member.infiniteAdele_bijective D`. Take `⟨-, -, hb⟩` from `H θ hθ`. Use `choose r hr using fun τ : {τ : D.host.E →+* ℂ // τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD} => IsAlgClosed.exists_pow_nat_eq (θ τ.1 z) hn`. Take `⟨w, hw⟩` from `hb.2 r`. Use `⟨w, hb.1 ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `τ`. Establish `h1 : θ τ.1 w = r τ` using `congrFun hw τ`. Express the relevant statement in the definitionally equal form `θ τ.1 (w ^ n) = θ τ.1 z`. Rewrite using `[map_pow, h1, hr]`.
-/
theorem exists_infAdele_pow_eq (D : D7) (n : ℕ) (hn : 0 < n)
    (z : InfiniteAdeleRing D.host.F ⊗[D.host.F] D.host.E) :
    ∃ w : InfiniteAdeleRing D.host.F ⊗[D.host.F] D.host.E, w ^ n = z := by
  obtain ⟨⟨θ, hθ⟩, H⟩ := GlobalTheory.Member.infiniteAdele_bijective D
  obtain ⟨-, -, hb⟩ := H θ hθ
  choose r hr using fun τ : {τ : D.host.E →+* ℂ // τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD} =>
    IsAlgClosed.exists_pow_nat_eq (θ τ.1 z) hn
  obtain ⟨w, hw⟩ := hb.2 r
  refine ⟨w, hb.1 ?_⟩
  funext τ
  have h1 : θ τ.1 w = r τ := congrFun hw τ
  change θ τ.1 (w ^ n) = θ τ.1 z
  rw [map_pow, h1, hr]

/- English proof (translation)
Introduce `D n hn x hx`. Take `⟨e, he, -, -⟩` from `GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E`. Take `⟨w, hw⟩` from `exists_infAdele_pow_eq D n hn (e (x : AE D)).1`. Establish `h2 : (e (x : AE D)).2 = 1` using `(he _).2.trans hx`. Establish `hy : (e.symm (w, 1)) ^ n = (x : AE D)`.

Apply `e.injective` to reduce the goal to its premises. Rewrite using `[map_pow, RingEquiv.apply_symm_apply]`. Conclude with `Prod.ext hw (by rw [h2]; exact one_pow n)`. Establish `hu : IsUnit (e.symm (w, 1))` using `(isUnit_pow_iff hn.ne').1 (hy ▸ x.isUnit)`. Take `⟨y, hy'⟩` from `hu`.

Use `⟨y, Units.ext ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_pow_eq_pow_val, hy']`. Conclude with `hy`.
-/
theorem exists_pow_eq_of_finPart_eq_one : ∀ (D : D7) (n : ℕ), 0 < n → ∀ x : (AE D)ˣ, finPart D (x : AE D) = 1 → ∃ y : (AE D)ˣ, y ^ n = x := by
  intro D n hn x hx
  obtain ⟨e, he, -, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  obtain ⟨w, hw⟩ := exists_infAdele_pow_eq D n hn (e (x : AE D)).1
  have h2 : (e (x : AE D)).2 = 1 := (he _).2.trans hx
  have hy : (e.symm (w, 1)) ^ n = (x : AE D) := by
    apply e.injective
    rw [map_pow, RingEquiv.apply_symm_apply]
    exact Prod.ext hw (by rw [h2]; exact one_pow n)
  have hu : IsUnit (e.symm (w, 1)) := (isUnit_pow_iff hn.ne').1 (hy ▸ x.isUnit)
  obtain ⟨y, hy'⟩ := hu
  refine ⟨y, Units.ext ?_⟩
  rw [Units.val_pow_eq_pow_val, hy']
  exact hy

end GlobalTheory.IdeleDiv
