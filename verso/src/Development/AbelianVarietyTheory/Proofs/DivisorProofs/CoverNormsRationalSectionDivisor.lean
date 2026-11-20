import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ChernOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSmoothFunctionCInfAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDegreeMixedLinearRoot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOnPts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometricOfSameNorms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleFiniteIndex
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal Classical
open MvPolynomial GlobalTheory.ArInt
open CategoryTheory AlgebraicGeometry GlobalTheory GlobalTheory.Mean4O GlobalTheory.HermLB

open GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ShFam.Pad GlobalTheory.FlatSecCover

set_option autoImplicit false

noncomputable section

open GlobalTheory.CxPts

namespace GlobalTheory.CoverNorm.Lift

/- English proof (translation)
Introduce `F _ _ Y V L φ a l ⟨r, hr, hu, hc, _⟩ hC`. Use `letI : IsLocallyNoetherian V.X := V.ar.isLocallyNoetherian`. Use `haveI := CoverHt.isPreimmersion_j V`. Establish `hη` using `Isom.j_gen_specializes V`. Set `ρ : V.X.functionField ≃+* V.G.functionField` to `RingEquiv.ofBijective (SmallSec.fnMap V.j hη) ⟨(SmallSec.fnMap V.j hη).injective, SmallSec.fnMap_surjective V.j hη⟩`.

Establish `hρ : ∀ (U : V.X.Opens) (hU : genericPoint V.X ∈ U) (hU' : genericPoint V.G ∈ V.j ⁻¹ᵁ U) (s : Γ(V.X, U)), ρ (fnOf U hU s) = fnOf (V.j ⁻¹ᵁ U) hU' (V.j.app U s)` using `fun U hU hU' s => SmallSec.fnMap_fnOf V.j hη hU hU' s`. Establish `hj : V.j (genericPoint V.G) = genericPoint V.X` using `(hη.antisymm (genericPoint_specializes _)).eq`. Establish `hφ : V.φ φ ≠ 0`. Take `⟨i, hi⟩` from `exists_chart L.isLB (V.j (genericPoint V.G))`. Conclude with `left_ne_zero_of_mul (hu (fun _ => i) _ (Set.mem_iInter.2 fun _ => hi)).ne_zero`.

Set `c : V.G.functionFieldˣ` to `Units.mk0 _ hφ`. Set `r' : (L.B.pull V.j).ι → V.G.functionFieldˣ` to `fun i => c * r i`. Establish `hr' : IsRatSec (L.B.pull V.j) r'` using `fun i i' h => by`. Simplify using `only [r', Units.val_mul, hr i i' h]`. Expand and normalize the polynomial expressions, which then agree.

Set `R : L.B.ι → V.X.functionFieldˣ` to `fun i => Units.map ρ.symm.toMonoidHom (r' fun _ => i)`. Establish `hR : IsRatSec L.B R` using `InducedIsom.isRatSec_lift V.j ρ hρ hj L.B hr'`. Establish `hρR : ∀ i, ρ (R i : V.X.functionField) = V.φ φ * r (fun _ => i)` using `fun i => ρ.apply_symm_apply _`. Establish `hP` using `presents_divOfRatSec L.isLB hR`. Use `⟨R, hR, fun z hz hz0 => ?_, fun σ' => ?_⟩` and prove the remaining obligations.

Take `⟨x, rfl⟩` from `Isom.mem_range_j V hz0`. Take `⟨i, hi⟩` from `exists_chart L.isLB (V.j x)`. Establish `hx : x ∈ (L.B.pull V.j).U (fun _ => i)` using `Set.mem_iInter.2 fun _ => hi`. Establish `hU : UnitAt (V.j x) (R i : V.X.functionField)`. Use `Mean4O.RootLine.unitAt_of_fnMap V.j hη ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `UnitAt x (ρ (R i : V.X.functionField))`. Rewrite using `[hρR]`. Conclude with `hu _ _ hx`. Conclude with `(hP.isEqn i _ hi).mem_supp_iff.1 (CartierDiv.mem_supp_of_mult_ne_zero hz) hU`. Establish `hτ` using `ringOfIntegers_hom_complex_injective F σ'`.

Take `⟨σ, hσ⟩ : ∃ σ : F →+* ℂ, σ.comp (algebraMap (𝓞 F) F) = σ'` from `⟨IsFractionRing.lift (K := F) hτ, RingHom.ext fun x => IsFractionRing.lift_algebraMap (K := F) hτ x⟩`. Take `⟨C, hC'⟩` from `hC σ`. Use `⟨C, fun y hy => ?_⟩` and prove the remaining obligations. Take `⟨σ₁, hσ₁, z, hz⟩` from `Isom.cxPts_from_generic_fibre V σ' y`. Establish `e : σ₁ = σ` using `IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 F)) (hσ₁.trans hσ.symm)`.

Substitute `e` using the available equality. Substitute `hσ₁` using the available equality. Set `y₀ : Pts Y σ₁` to `⟨z.1 ≫ V.π, by rw [Category.assoc]; exact z.2⟩`. Establish `hun : under y = V.j (under z)`. Express the relevant statement in the definitionally equal form `y.1 _ = _`.

Rewrite using `[hz]`. Both sides reduce to the same expression. Take `⟨i, hi⟩` from `exists_chart L.isLB (under y)`. Establish `hm : under z ∈ (L.B.pull V.j).U fun _ => i` using `Set.mem_iInter.2 fun _ => by`. Express the relevant statement in the definitionally equal form `V.j (under z) ∈ L.B.U i`.

Rewrite using `[← hun]`. Conclude with `hi`. Establish `H` using `hc σ₁ z y₀ y (fun _ => i) rfl hz hm`. Rewrite using `[logNorm_eq (L.φ _) hR hy (mem_ptsIn.2 hi), ModelFn.ratVal_eq, hz, ModelFn.valAt_comp V.j hη, ← ModelFn.ratVal_eq z]`. Establish `hv : SmallSec.fnMap V.j hη (R i : V.X.functionField) = V.φ φ * r (fun _ => i)` using `hρR i`.

Rewrite using `[hv, ← hC' y₀]`. Use `first`. Consider the case `linarith`. Consider the case `(beta_reduce at H; linarith)`. Consider the case `(dsimp only at H ⊢; linarith)`.
-/
theorem exists_ratSec_vertical_const : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (L : HermLB V.p) (φ : Y.Fn)
    (a : ∀ σ : F →+* ℂ, Pts Y σ → ℝ) (l : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ),
    GlobalTheory.CoverNorm.Norms V L (fun _ => φ) a l → (∀ σ, ∃ C : ℝ, ∀ y, a σ y = C) →
    letI : IsLocallyNoetherian V.X := V.ar.isLocallyNoetherian
    ∃ (r : L.B.ι → V.X.functionFieldˣ) (hr : IsRatSec L.B r),
      (∀ z, (L.div hr).mult z ≠ 0 → (V.p z).asIdeal ≠ ⊥) ∧
      ∀ σ, ∃ a : ℝ, ∀ y ∈ offSupp V.p σ (L.div hr), logNorm (L.φ σ) r y = a := by
  intro F _ _ Y V L φ a l ⟨r, hr, hu, hc, _⟩ hC
  letI : IsLocallyNoetherian V.X := V.ar.isLocallyNoetherian
  haveI := CoverHt.isPreimmersion_j V
  have hη := Isom.j_gen_specializes V
  let ρ : V.X.functionField ≃+* V.G.functionField := RingEquiv.ofBijective (SmallSec.fnMap V.j hη)
    ⟨(SmallSec.fnMap V.j hη).injective, SmallSec.fnMap_surjective V.j hη⟩
  have hρ : ∀ (U : V.X.Opens) (hU : genericPoint V.X ∈ U) (hU' : genericPoint V.G ∈ V.j ⁻¹ᵁ U) (s : Γ(V.X, U)),
      ρ (fnOf U hU s) = fnOf (V.j ⁻¹ᵁ U) hU' (V.j.app U s) := fun U hU hU' s => SmallSec.fnMap_fnOf V.j hη hU hU' s
  have hj : V.j (genericPoint V.G) = genericPoint V.X := (hη.antisymm (genericPoint_specializes _)).eq

  have hφ : V.φ φ ≠ 0 := by
    obtain ⟨i, hi⟩ := exists_chart L.isLB (V.j (genericPoint V.G))
    exact left_ne_zero_of_mul (hu (fun _ => i) _ (Set.mem_iInter.2 fun _ => hi)).ne_zero
  let c : V.G.functionFieldˣ := Units.mk0 _ hφ
  let r' : (L.B.pull V.j).ι → V.G.functionFieldˣ := fun i => c * r i
  have hr' : IsRatSec (L.B.pull V.j) r' := fun i i' h => by
    simp only [r', Units.val_mul, hr i i' h]
    ring
  let R : L.B.ι → V.X.functionFieldˣ := fun i => Units.map ρ.symm.toMonoidHom (r' fun _ => i)
  have hR : IsRatSec L.B R := InducedIsom.isRatSec_lift V.j ρ hρ hj L.B hr'
  have hρR : ∀ i, ρ (R i : V.X.functionField) = V.φ φ * r (fun _ => i) := fun i => ρ.apply_symm_apply _
  have hP := presents_divOfRatSec L.isLB hR
  refine ⟨R, hR, fun z hz hz0 => ?_, fun σ' => ?_⟩
  · obtain ⟨x, rfl⟩ := Isom.mem_range_j V hz0
    obtain ⟨i, hi⟩ := exists_chart L.isLB (V.j x)
    have hx : x ∈ (L.B.pull V.j).U (fun _ => i) := Set.mem_iInter.2 fun _ => hi
    have hU : UnitAt (V.j x) (R i : V.X.functionField) := by
      refine Mean4O.RootLine.unitAt_of_fnMap V.j hη ?_
      change UnitAt x (ρ (R i : V.X.functionField))
      rw [hρR]
      exact hu _ _ hx
    exact (hP.isEqn i _ hi).mem_supp_iff.1 (CartierDiv.mem_supp_of_mult_ne_zero hz) hU
  · have hτ := ringOfIntegers_hom_complex_injective F σ'
    obtain ⟨σ, hσ⟩ : ∃ σ : F →+* ℂ, σ.comp (algebraMap (𝓞 F) F) = σ' :=
      ⟨IsFractionRing.lift (K := F) hτ, RingHom.ext fun x => IsFractionRing.lift_algebraMap (K := F) hτ x⟩
    obtain ⟨C, hC'⟩ := hC σ
    refine ⟨C, fun y hy => ?_⟩
    obtain ⟨σ₁, hσ₁, z, hz⟩ := Isom.cxPts_from_generic_fibre V σ' y
    have e : σ₁ = σ := IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 F))
      (hσ₁.trans hσ.symm)
    subst e
    subst hσ₁
    let y₀ : Pts Y σ₁ := ⟨z.1 ≫ V.π, by rw [Category.assoc]; exact z.2⟩
    have hun : under y = V.j (under z) := by
      change y.1 _ = _
      rw [hz]
      rfl
    obtain ⟨i, hi⟩ := exists_chart L.isLB (under y)
    have hm : under z ∈ (L.B.pull V.j).U fun _ => i := Set.mem_iInter.2 fun _ => by
      change V.j (under z) ∈ L.B.U i
      rw [← hun]
      exact hi
    have H := hc σ₁ z y₀ y (fun _ => i) rfl hz hm
    rw [logNorm_eq (L.φ _) hR hy (mem_ptsIn.2 hi), ModelFn.ratVal_eq, hz,
      ModelFn.valAt_comp V.j hη, ← ModelFn.ratVal_eq z]
    have hv : SmallSec.fnMap V.j hη (R i : V.X.functionField) = V.φ φ * r (fun _ => i) := hρR i
    rw [hv, ← hC' y₀]
    first
      | linarith
      | (beta_reduce at H; linarith)
      | (dsimp only at H ⊢; linarith)

end GlobalTheory.CoverNorm.Lift
