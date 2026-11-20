import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWTie
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibExtMarked
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitDetRoot

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.LatticeUnitRoot

/- English proof (translation)
Introduce `D V Λ hΛ k hk hm`. Establish `hu : ∀ z ∈ GlobalTheory.Ker.hatV Λ, ∃ y ∈ GlobalTheory.Ker.hatV Λ, (finHom V k).1.mulVec z - z = (1 : ℕ) • y` using `fun z hz => ⟨_, sub_mem ((hm _).2 ⟨z, hz, rfl⟩) hz, (one_nsmul _).symm⟩`. Take `⟨w, hw, hwe⟩` from `GlobalTheory.MarkDet.det_sub_one_of_cong D.host.F Λ hΛ.1.fg hΛ.1.span_eq_top 1 one_ne_zero _ hu`. Rewrite `hw` using `[← GlobalTheory.IdeleParts.integralFiniteAdeles_eq_adelicCompletion_integers]`. Establish `hn` using `GlobalTheory.RecDict.det_finHom_norm V k`.

Take `⟨y, y', hy, hy', hyy, hroot, -⟩` from `GlobalTheory.OddRoot.exists_root_odd D 1 odd_one _ w hw hwe hn`. Take `⟨Y, hY1, hY2, hY3⟩` from `GlobalTheory.DetRootCong.exists_idele D y y' hyy`. Use `⟨Y, ⟨hY1, hY2 ▸ hy, hY3 ▸ hy'⟩, ?_⟩` and prove the remaining obligations. Establish `hdet : (finHom V k).1.det = finPart D (matHom V k).1.det` using `((finPart D).map_det _).symm`. Establish `hdet' : (infHom V k).1.det = infPart D (matHom V k).1.det` using `((infPart D).map_det _).symm`.

Establish `hk1 : infHom V k = 1` using `hk`. Rewrite `hdet'` using `[hk1, Units.val_one, Matrix.det_one]`. Take `⟨e, he, -⟩` from `GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E`. Apply `e.injective` to reduce the goal to its premises. Use `Prod.ext (((he _).1.trans ?_).trans (he _).1.symm) (((he _).2.trans ?_).trans (he _).2.symm)` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `infPart D (Y : AE D) = infPart D ((matHom V k).1.det * sigR (AF D.host.F) D.sp.cm.sig (Y : AE D))`. Rewrite using `[RingHom.map_mul, ← hdet', GlobalTheory.UnitDetRoot.infPart_sigR_one D _ hY1, hY1, _root_.mul_one]`. Express the relevant statement in the definitionally equal form `finPart D (Y : AE D) = finPart D ((matHom V k).1.det * sigR (AF D.host.F) D.sp.cm.sig (Y : AE D))`. Rewrite using `[RingHom.map_mul, ← hdet, GlobalTheory.DetRootCong.finPart_sigR, hY2]`. Conclude with `hroot`.
-/
theorem exists_finUnit_isDetRoot : ∀ (D : D7) (S : HSp D) (Λ : Lt D.host.E S.rank), IsSelfDualC S Λ → ∀ k ∈ GfC S, GlobalTheory.Ker.IsMov (GlobalTheory.Ker.fmt S k) Λ Λ → ∃ x : (AE D)ˣ, FinUnit x ∧ IsDetRoot S k x := by
  intro D V Λ hΛ k hk hm
  have hu : ∀ z ∈ GlobalTheory.Ker.hatV Λ, ∃ y ∈ GlobalTheory.Ker.hatV Λ, (finHom V k).1.mulVec z - z = (1 : ℕ) • y := fun z hz =>
    ⟨_, sub_mem ((hm _).2 ⟨z, hz, rfl⟩) hz, (one_nsmul _).symm⟩
  obtain ⟨w, hw, hwe⟩ := GlobalTheory.MarkDet.det_sub_one_of_cong D.host.F Λ hΛ.1.fg hΛ.1.span_eq_top 1 one_ne_zero _ hu
  rw [← GlobalTheory.IdeleParts.integralFiniteAdeles_eq_adelicCompletion_integers] at hw
  have hn := GlobalTheory.RecDict.det_finHom_norm V k
  obtain ⟨y, y', hy, hy', hyy, hroot, -⟩ := GlobalTheory.OddRoot.exists_root_odd D 1 odd_one _ w hw hwe hn
  obtain ⟨Y, hY1, hY2, hY3⟩ := GlobalTheory.DetRootCong.exists_idele D y y' hyy
  refine ⟨Y, ⟨hY1, hY2 ▸ hy, hY3 ▸ hy'⟩, ?_⟩
  have hdet : (finHom V k).1.det = finPart D (matHom V k).1.det := ((finPart D).map_det _).symm
  have hdet' : (infHom V k).1.det = infPart D (matHom V k).1.det := ((infPart D).map_det _).symm
  have hk1 : infHom V k = 1 := hk
  rw [hk1, Units.val_one, Matrix.det_one] at hdet'
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  apply e.injective
  refine Prod.ext (((he _).1.trans ?_).trans (he _).1.symm) (((he _).2.trans ?_).trans (he _).2.symm)
  · change infPart D (Y : AE D) = infPart D ((matHom V k).1.det * sigR (AF D.host.F) D.sp.cm.sig (Y : AE D))
    rw [RingHom.map_mul, ← hdet', GlobalTheory.UnitDetRoot.infPart_sigR_one D _ hY1, hY1, _root_.mul_one]
  · change finPart D (Y : AE D) = finPart D ((matHom V k).1.det * sigR (AF D.host.F) D.sp.cm.sig (Y : AE D))
    rw [RingHom.map_mul, ← hdet, GlobalTheory.DetRootCong.finPart_sigR, hY2]
    exact hroot

end GlobalTheory.LatticeUnitRoot
