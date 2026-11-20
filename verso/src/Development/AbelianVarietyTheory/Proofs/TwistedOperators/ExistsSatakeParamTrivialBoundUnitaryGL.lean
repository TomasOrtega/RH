import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SphericalEigenvectorGeneratesIrreducibleSubrepreStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormSatakeLeOfUnitarySphericalGLStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PowDvdOfHermMatEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SatakeParameterGLStarEqInvOfUnitarisable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SatakeParameterOfSpherical
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinZeta.ParGL

/- English proof (translation)
Introduce `E _ _ w n V _ _ ρ hun x hx0 hxf hs`. Establish `hK : IsCommensurated (KGL w n)` using `Formalism.UG.Final.GLintComm E w n`. Take `⟨U, hU, hxU, hirr, hunU, hline⟩` from `GlobalTheory.T.spherical_eigenvector_generates_irreducible_subrepresentation ρ (KGL w n) (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).1 hK hun x hx0 hxf hs`. Use `set π := GlobalTheory.PRep.sub ρ U hU with hπ`. Set `x' : U` to `⟨x, hxU⟩`.

Establish `hx'0 : x' ≠ 0` using `fun e => hx0 (congrArg Subtype.val e)`. Establish `hx'f : x' ∈ fixed π (KGL w n)` using `GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext (GlobalTheory.LGrp.mem_fixed.1 hxf k hk)`. Establish `hsub : ∀ g (y : U), U.subtype (π g y) = ρ g (U.subtype y)` using `fun _ _ => rfl`. Establish `heig : ∀ h ∈ Hecke ℂ (KGL w n), ∃ c : ℂ, ∀ y ∈ fixed π (KGL w n), heckeVec π (KGL w n) h y = c • y`. Introduce `h hh`.

Take `⟨c, hc⟩` from `hs h hh`. Establish `e1 : heckeVec π (KGL w n) h x' = c • x'` using `Subtype.val_injective (by`. Use `map_heckeVec hK hh U.subtype hsub (x := x')` as an intermediate fact. Conclude with `this.trans hc)`. Use `⟨c, fun y hy => ?_⟩` and prove the remaining obligations.

Take `⟨a, rfl⟩` from `hline y hy`. Use `map_heckeVec hK hh (ρ := π) (ρ' := π) (a • LinearMap.id) (fun g y => by simp) (x := x')` as an intermediate fact. Simplify using `only [LinearMap.smul_apply, LinearMap.id_apply] at this`. Rewrite using `[← this, e1, smul_comm]`. Take `⟨B, hB⟩` from `GlobalTheory.LFun.ExSatGL.exists_hasSatGL E w n U π ((Submodule.ne_bot_iff _).2 ⟨x', hx'f, hx'0⟩) heig`.

Establish `hx' : IsSatVecGL w π x' B` using `hB.2 x' hx'f hx'0`. Establish `hup` using `GlobalTheory.T.norm_satake_le_of_unitary_spherical_GL GlobalTheory.SatakeBound.satakeTrivialBound E w n _ π B hirr hunU hB`. Use `⟨B, hx'.map U.subtype hsub hx0, fun β hβ => ⟨hup β hβ, ?_⟩⟩` and prove the remaining obligations. Establish `hst` using `GlobalTheory.LFun.UnitaryParam.map_star_eq_map_inv E w n _ π x' B hunU hx'`. Establish `h1 : β⁻¹ ∈ B.map star` using `hst ▸ Multiset.mem_map_of_mem _ hβ`.

Take `⟨β', hβ', e⟩` from `Multiset.mem_map.1 h1`. Establish `h2 : ‖((β⁻¹ : ℂˣ) : ℂ)‖ = ‖(β' : ℂ)‖`. Rewrite using `[← e]`. Simplify using the standard rewrite rules. Rewrite using `[h2]`.

Conclude with `hup β' hβ'`.
-/
theorem exists_isSatVecGL_bound : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V), IsUnitarisable ρ → ∀ x : V, x ≠ 0 → x ∈ fixed ρ (KGL w n) → (∀ h ∈ Hecke ℂ (KGL w n), ∃ c : ℂ, heckeVec ρ (KGL w n) h x = c • x) → ∃ B, IsSatVecGL w ρ x B ∧ ∀ β ∈ B, ‖(β : ℂ)‖ ≤ (qV E w : ℝ) ^ (((n : ℝ) - 1) / 2) ∧ ‖((β⁻¹ : ℂˣ) : ℂ)‖ ≤ (qV E w : ℝ) ^ (((n : ℝ) - 1) / 2) := by
  intro E _ _ w n V _ _ ρ hun x hx0 hxf hs
  have hK : IsCommensurated (KGL w n) := Formalism.UG.Final.GLintComm E w n
  obtain ⟨U, hU, hxU, hirr, hunU, hline⟩ :=
    GlobalTheory.T.spherical_eigenvector_generates_irreducible_subrepresentation ρ (KGL w n) (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).1 hK hun x hx0 hxf hs
  set π := GlobalTheory.PRep.sub ρ U hU with hπ
  let x' : U := ⟨x, hxU⟩
  have hx'0 : x' ≠ 0 := fun e => hx0 (congrArg Subtype.val e)
  have hx'f : x' ∈ fixed π (KGL w n) :=
    GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext (GlobalTheory.LGrp.mem_fixed.1 hxf k hk)
  have hsub : ∀ g (y : U), U.subtype (π g y) = ρ g (U.subtype y) := fun _ _ => rfl
  have heig : ∀ h ∈ Hecke ℂ (KGL w n), ∃ c : ℂ, ∀ y ∈ fixed π (KGL w n), heckeVec π (KGL w n) h y = c • y := by
    intro h hh
    obtain ⟨c, hc⟩ := hs h hh
    have e1 : heckeVec π (KGL w n) h x' = c • x' := Subtype.val_injective (by
      have := map_heckeVec hK hh U.subtype hsub (x := x')
      exact this.trans hc)
    refine ⟨c, fun y hy => ?_⟩
    obtain ⟨a, rfl⟩ := hline y hy
    have := map_heckeVec hK hh (ρ := π) (ρ' := π) (a • LinearMap.id) (fun g y => by simp) (x := x')
    simp only [LinearMap.smul_apply, LinearMap.id_apply] at this
    rw [← this, e1, smul_comm]
  obtain ⟨B, hB⟩ := GlobalTheory.LFun.ExSatGL.exists_hasSatGL E w n U π
    ((Submodule.ne_bot_iff _).2 ⟨x', hx'f, hx'0⟩) heig
  have hx' : IsSatVecGL w π x' B := hB.2 x' hx'f hx'0
  have hup := GlobalTheory.T.norm_satake_le_of_unitary_spherical_GL GlobalTheory.SatakeBound.satakeTrivialBound E w n _ π B hirr hunU hB
  refine ⟨B, hx'.map U.subtype hsub hx0, fun β hβ => ⟨hup β hβ, ?_⟩⟩
  have hst := GlobalTheory.LFun.UnitaryParam.map_star_eq_map_inv E w n _ π x' B hunU hx'
  have h1 : β⁻¹ ∈ B.map star := hst ▸ Multiset.mem_map_of_mem _ hβ
  obtain ⟨β', hβ', e⟩ := Multiset.mem_map.1 h1
  have h2 : ‖((β⁻¹ : ℂˣ) : ℂ)‖ = ‖(β' : ℂ)‖ := by
    rw [← e]
    simp
  rw [h2]
  exact hup β' hβ'

end GlobalTheory.FinZeta.ParGL

end
