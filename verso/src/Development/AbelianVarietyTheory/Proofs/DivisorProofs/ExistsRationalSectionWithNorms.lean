import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriModOfBlockTriangular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometricOfSameNorms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularOfIntegralValuationBound
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LinearIndependentOfCutSec

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat GlobalTheory.LatChain Filter Topology
open scoped Classical

namespace GlobalTheory.LatChain

open GlobalTheory.CoverNorm.Isom in

/- English proof (translation)
Introduce `F _ _ Y V M lg ⟨r, hr, hu, hc, hf⟩`. Use `haveI := CoverHt.isPreimmersion_j V`. Establish `hη` using `j_gen_specializes V`. Set `ρ : V.X.functionField ≃+* V.G.functionField` to `RingEquiv.ofBijective (SmallSec.fnMap V.j hη) ⟨(SmallSec.fnMap V.j hη).injective, SmallSec.fnMap_surjective V.j hη⟩`. Establish `hρ : ∀ (U : V.X.Opens) (hU : genericPoint V.X ∈ U) (hU' : genericPoint V.G ∈ V.j ⁻¹ᵁ U) (s : Γ(V.X, U)), ρ (fnOf U hU s) = fnOf (V.j ⁻¹ᵁ U) hU' (V.j.app U s)` using `fun U hU hU' s => SmallSec.fnMap_fnOf V.j hη hU hU' s`.

Establish `hj : V.j (genericPoint V.G) = genericPoint V.X` using `(hη.antisymm (genericPoint_specializes _)).eq`. Establish `hv : ∀ {K : Type} [Field K] (y : Sp K ⟶ V.G) (g : V.X.functionField), TrueGeo.valAt (y ≫ V.j) g = TrueGeo.valAt y (ρ g)` using `fun y g => ModelFn.valAt_comp V.j hη y g`. Establish `hR` using `InducedIsom.isRatSec_lift V.j ρ hρ hj M.B hr`. Establish `hu' : ∀ i, ∀ x ∈ (M.B.pull V.j).U i, UnitAt x (r i : V.G.functionField)` using `fun i x hx => by`. Simplify using `using hu i x hx`.

Establish `eρ : ∀ i, ρ ((Units.map ρ.symm.toMonoidHom (r fun _ => i) : V.X.functionFieldˣ) : V.X.functionField) = (r fun _ => i : V.G.functionField)` using `fun i => ρ.apply_symm_apply _`. Establish `hreg : ∀ (z : V.G) (g : V.X.functionField), RegAt z (ρ g) → RegAt (V.j z) g` using `fun z g h => (SmallSec.regAt_fnMap_iff V.j hη).1 h`. Establish `hU : ∀ i (z : V.G), V.j z ∈ M.B.U i → UnitAt (V.j z) ((Units.map ρ.symm.toMonoidHom (r fun _ => i) : V.X.functionFieldˣ) : V.X.functionField)`. Introduce `i z hz`. Establish `m₁ : z ∈ (M.B.pull V.j).U fun _ => i` using `Set.mem_iInter.2 fun _ => hz`.

Establish `hw` using `hu' _ _ m₁`. Use `(unitAt_iff (Units.ne_zero _)).2 ⟨hreg _ _ ?_, hreg _ _ ?_⟩` and prove the remaining obligations. Rewrite using `[eρ]`. Conclude with `hw.regAt`. Rewrite using `[map_inv₀, eρ]`.

Conclude with `hw.inv.regAt`. Use `⟨_, hR, fun τ y => ?_, hU, fun v e y z yt i e₁ e₂ h₁ => ?_⟩` and prove the remaining obligations. Take `⟨σ, rfl, z, hz⟩` from `cxPts_from_generic_fibre V τ y`. Establish `hun : under y = V.j (under z)`. Express the relevant statement in the definitionally equal form `y.1 _ = _`.

Rewrite using `[hz]`. Both sides reduce to the same expression. Use `⟨mem_offSupp.2 fun hs => ?_, ?_⟩` and prove the remaining obligations. Take `⟨i, hi⟩` from `exists_chart M.isLB (under y)`. Use `((presents_divOfRatSec M.isLB hR).isEqn i _ hi).mem_supp_iff.1 hs ?_` and prove the remaining obligations.

Rewrite `hi`, the goal using `[hun]`. Conclude with `hU i _ hi`. Rewrite using `[logNorm]`. Establish `hyj` using `CxPts.mem_pick (M.φ (σ.comp (algebraMap (𝓞 F) F))).isLB y`. Generalize the expression as in `CxPts.pick (M.φ (σ.comp (algebraMap (𝓞 F) F))).isLB y = j at hyj ⊢`.

Set `y₀ : Pts Y σ` to `⟨z.1 ≫ V.π, by rw [Category.assoc]; exact z.2⟩`. Establish `m₁ : under z ∈ (M.B.pull V.j).U fun _ => j` using `Set.mem_iInter.2 fun _ => by`. Express the relevant statement in the definitionally equal form `V.j (under z) ∈ M.B.U j`. Rewrite using `[← hun]`. Conclude with `CxPts.mem_ptsIn.1 hyj`.

Establish `H` using `hc σ z y₀ y (fun _ => j) rfl hz m₁`. Establish `hq : ratVal ((Units.map ρ.symm.toMonoidHom (r fun _ => j) : V.X.functionFieldˣ) : V.X.functionField) y = ratVal (r fun _ => j : V.G.functionField) z`. Rewrite using `[ModelFn.ratVal_eq, ModelFn.ratVal_eq, hz, hv, eρ]`. Simplify using `only [map_one, one_mul] at H`. Rewrite using `[hq]`.

Use `first`. Consider the case `linarith`. Consider the case `(beta_reduce at H; linarith)`. Establish `h₂ : ⊤ ≤ yt ⁻¹ᵁ M.B.U ((fun _ => i : (M.B.pull V.j).ι) PUnit.unit)` using `h₁`. Establish `H` using `hf v e y z yt (fun _ => i) e₁ e₂ h₂`.

Simplify using `only [map_one, one_mul] at H`. Rewrite using `[hv, eρ]`. Conclude with `H`.
-/
theorem exists_normsX : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (M : HermLB V.p) (lg : ∀ v : HeightOneSpectrum (𝓞 F), TrueGeo.Ext v → AlgPt Y → ℝ), Norms V M (fun _ => 1) (fun _ _ => 0) lg → ∃ (r : M.B.ι → V.X.functionFieldˣ) (hr : IsRatSec M.B r), NormsX V M lg r hr := by
  intro F _ _ Y V M lg ⟨r, hr, hu, hc, hf⟩
  haveI := CoverHt.isPreimmersion_j V
  have hη := j_gen_specializes V
  let ρ : V.X.functionField ≃+* V.G.functionField := RingEquiv.ofBijective (SmallSec.fnMap V.j hη)
    ⟨(SmallSec.fnMap V.j hη).injective, SmallSec.fnMap_surjective V.j hη⟩
  have hρ : ∀ (U : V.X.Opens) (hU : genericPoint V.X ∈ U) (hU' : genericPoint V.G ∈ V.j ⁻¹ᵁ U)
      (s : Γ(V.X, U)), ρ (fnOf U hU s) = fnOf (V.j ⁻¹ᵁ U) hU' (V.j.app U s) :=
    fun U hU hU' s => SmallSec.fnMap_fnOf V.j hη hU hU' s
  have hj : V.j (genericPoint V.G) = genericPoint V.X := (hη.antisymm (genericPoint_specializes _)).eq
  have hv : ∀ {K : Type} [Field K] (y : Sp K ⟶ V.G) (g : V.X.functionField),
      TrueGeo.valAt (y ≫ V.j) g = TrueGeo.valAt y (ρ g) :=
    fun y g => ModelFn.valAt_comp V.j hη y g
  have hR := InducedIsom.isRatSec_lift V.j ρ hρ hj M.B hr
  have hu' : ∀ i, ∀ x ∈ (M.B.pull V.j).U i, UnitAt x (r i : V.G.functionField) := fun i x hx => by
    simpa using hu i x hx
  have eρ : ∀ i, ρ ((Units.map ρ.symm.toMonoidHom (r fun _ => i) : V.X.functionFieldˣ) :
      V.X.functionField) = (r fun _ => i : V.G.functionField) := fun i => ρ.apply_symm_apply _
  have hreg : ∀ (z : V.G) (g : V.X.functionField), RegAt z (ρ g) → RegAt (V.j z) g :=
    fun z g h => (SmallSec.regAt_fnMap_iff V.j hη).1 h
  have hU : ∀ i (z : V.G), V.j z ∈ M.B.U i → UnitAt (V.j z)
      ((Units.map ρ.symm.toMonoidHom (r fun _ => i) : V.X.functionFieldˣ) : V.X.functionField) := by
    intro i z hz
    have m₁ : z ∈ (M.B.pull V.j).U fun _ => i := Set.mem_iInter.2 fun _ => hz
    have hw := hu' _ _ m₁
    refine (unitAt_iff (Units.ne_zero _)).2 ⟨hreg _ _ ?_, hreg _ _ ?_⟩
    · rw [eρ]; exact hw.regAt
    · rw [map_inv₀, eρ]; exact hw.inv.regAt
  refine ⟨_, hR, fun τ y => ?_, hU, fun v e y z yt i e₁ e₂ h₁ => ?_⟩
  · obtain ⟨σ, rfl, z, hz⟩ := cxPts_from_generic_fibre V τ y
    have hun : under y = V.j (under z) := by
      change y.1 _ = _
      rw [hz]
      rfl
    refine ⟨mem_offSupp.2 fun hs => ?_, ?_⟩
    · obtain ⟨i, hi⟩ := exists_chart M.isLB (under y)
      refine ((presents_divOfRatSec M.isLB hR).isEqn i _ hi).mem_supp_iff.1 hs ?_
      rw [hun] at hi ⊢
      exact hU i _ hi
    rw [logNorm]
    have hyj := CxPts.mem_pick (M.φ (σ.comp (algebraMap (𝓞 F) F))).isLB y
    generalize CxPts.pick (M.φ (σ.comp (algebraMap (𝓞 F) F))).isLB y = j at hyj ⊢
    let y₀ : Pts Y σ := ⟨z.1 ≫ V.π, by rw [Category.assoc]; exact z.2⟩
    have m₁ : under z ∈ (M.B.pull V.j).U fun _ => j := Set.mem_iInter.2 fun _ => by
      change V.j (under z) ∈ M.B.U j
      rw [← hun]
      exact CxPts.mem_ptsIn.1 hyj
    have H := hc σ z y₀ y (fun _ => j) rfl hz m₁
    have hq : ratVal ((Units.map ρ.symm.toMonoidHom (r fun _ => j) : V.X.functionFieldˣ) :
        V.X.functionField) y = ratVal (r fun _ => j : V.G.functionField) z := by
      rw [ModelFn.ratVal_eq, ModelFn.ratVal_eq, hz, hv, eρ]
    simp only [map_one, one_mul] at H
    rw [hq]
    first
      | linarith
      | (beta_reduce at H; linarith)
  · have h₂ : ⊤ ≤ yt ⁻¹ᵁ M.B.U ((fun _ => i : (M.B.pull V.j).ι) PUnit.unit) := h₁
    have H := hf v e y z yt (fun _ => i) e₁ e₂ h₂
    simp only [map_one, one_mul] at H
    rw [hv, eρ]
    exact H

end GlobalTheory.LatChain

end
