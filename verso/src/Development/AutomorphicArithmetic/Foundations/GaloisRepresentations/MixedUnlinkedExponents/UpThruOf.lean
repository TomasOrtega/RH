import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.GamMixedOf

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open GroundTheory.Global.SemiLocal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
open UpperTheory.Gal.GamX

/- English proof (translation)
Unfold `UpThruOf UpThru`. Introduce `hC K L _ _ _ _ _ v w s`. Rewrite using `[Multiset.filter_eq_self]`. Introduce `ζ hζ`. Take `⟨ξ, hξ, rfl⟩` from `Multiset.mem_map.1 hζ`.

Establish `hs : IsSmoothChar ξ` using `(hC _ s).2.1 ξ hξ`. Use `⟨ξ⁻¹, IsSmoothChar.inv hs, fun x _ => by simp⟩` and prove the remaining obligations.
-/
theorem UpperTheory.Gal.GamX.upThruOf :
    UpperTheory.Gal.GamX.UpThruOf := by
  unfold UpThruOf UpThru
  intro hC K L _ _ _ _ _ v w s
  rw [Multiset.filter_eq_self]
  intro ζ hζ
  obtain ⟨ξ, hξ, rfl⟩ := Multiset.mem_map.1 hζ
  have hs : IsSmoothChar ξ := (hC _ s).2.1 ξ hξ
  refine ⟨ξ⁻¹, IsSmoothChar.inv hs, fun x _ => by simp⟩
