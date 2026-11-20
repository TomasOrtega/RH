import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsCuspidalOfConstantTermEqZero

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Fb in
/- English proof (translation)
Establish `hD' : IsAddFundamentalDomain (unipLattice E a r) D (unipMeasure E a r)` using `hD.mono (Measure.absolutelyContinuous_isAddHaarMeasure _ _)`. Rewrite `h` using `[constantTerm_eq_setIntegral hl hD']`. Rewrite using `[Measure.isAddLeftInvariant_eq_smul ν (unipMeasure E a r), Measure.restrict_smul, integral_smul_nnreal_measure, h, smul_zero]`.
-/
private theorem setIntegral_haar {E : Type} [Field E] [NumberField E] {a r : ℕ} {φ : GA E a → ℂ}
    (hl : IsLeftInvariant φ) (g : GA E a) (h : constantTerm r φ g = 0) (ν : Measure (UPos a r → Ad E))
    [ν.IsAddHaarMeasure] {D : Set (UPos a r → Ad E)} (hD : IsAddFundamentalDomain (unipLattice E a r) D ν) :
    ∫ x in D, φ (unipGL x * g) ∂ν = 0 := by
  have hD' : IsAddFundamentalDomain (unipLattice E a r) D (unipMeasure E a r) :=
    hD.mono (Measure.absolutelyContinuous_isAddHaarMeasure _ _)
  rw [constantTerm_eq_setIntegral hl hD'] at h
  rw [Measure.isAddLeftInvariant_eq_smul ν (unipMeasure E a r), Measure.restrict_smul, integral_smul_nnreal_measure, h,
    smul_zero]

open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Fb in
private def ixEq (a r : ℕ) : UPos a r ≃ BlockIx a r where
  toFun p := ⟨p.1, p.2.1, p.2.2⟩
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Fb in
/- English proof (translation)
Use `Units.ext ?_` and prove the remaining obligations. Apply the tactic sequence `change 1 + blockEntry (fun p => x (ixEq a r p)) = 1 + nilM x`. Use `congr 1`.
-/
private theorem unipGL_ixEq {R : Type} [CommRing R] {a r : ℕ} (x : BlockIx a r → R) :
    unipGL (fun p => x (ixEq a r p)) = unip x := by
  refine Units.ext ?_
  change 1 + blockEntry (fun p => x (ixEq a r p)) = 1 + nilM x
  congr 1

open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Fb in
/- English proof (translation)
Introduce `r h0 h1 i1 i2 μ 𝓕 hμ hF g`. Take `rfl : i1 = MeasurableSpace.pi` from `(@BorelSpace.measurable_eq _ _ i1 i2).trans (@BorelSpace.measurable_eq _ _ _ Pi.borelSpace).symm`. Set `β : (BlockIx a r → Ad E) ≃ₜ+ (UPos a r → Ad E)` to `{ toFun := fun x p => x (ixEq a r p) invFun := fun x p => x ((ixEq a r).symm p) left_inv := fun x => rfl right_inv := fun x => rfl map_add' := fun x y => rfl continuous_toFun := continuous_pi fun p => continuous_apply _ continuous_invFun := continuous_pi fun p => continuous_apply …`. Set `e : unipLattice E a r ≃ ratN E a r` to `{ toFun := fun y => ⟨β.symm y, by`. Take `⟨_, y, rfl⟩` from `y`.

Conclude with `⟨fun p => y ((ixEq a r).symm p), rfl⟩⟩`. Use `invFun := fun x => ⟨β x, by`. Take `⟨_, y, rfl⟩` from `x`. Conclude with `⟨fun p => y (ixEq a r p), rfl⟩⟩`. Use `left_inv := fun y => Subtype.ext (β.apply_symm_apply y)`.

Use `right_inv := fun x => Subtype.ext (β.symm_apply_apply x) }`. Set `m` to `β.toHomeomorph.toMeasurableEquiv`. Use `haveI : (μ.map m).IsAddHaarMeasure := β.isAddHaarMeasure_map μ`. Establish `h2` using `setIntegral_haar hl g (hφ r h0 h1 g) (μ.map m) (D := m '' 𝓕) (hF.image_of_equiv m.toEquiv (MeasurePreserving.symm m ⟨m.measurable, rfl⟩).quasiMeasurePreserving e fun y x => by`. Express the relevant statement in the definitionally equal form `β (β.symm y + x) = y + β x`.

Rewrite using `[map_add, β.apply_symm_apply])`. Rewrite `h2` using `[m.measurableEmbedding.setIntegral_map, m.injective.preimage_image]`. Rewrite using `[← h2]`. Use `congr 1`. Use function extensionality and compare the values at `x`.

Conclude with `congrArg (fun u => φ (u * g)) (unipGL_ixEq x).symm`.
-/
private theorem cusp_of {E : Type} [Field E] [NumberField E] {a : ℕ} {φ : GA E a → ℂ}
    (hl : IsLeftInvariant φ) (hφ : AutomorphicForm.IsCuspidal φ) : GlobalTheory.CuspRep.IsCuspidal φ := by
  intro r h0 h1 i1 i2 μ 𝓕 hμ hF g
  obtain rfl : i1 = MeasurableSpace.pi :=
    (@BorelSpace.measurable_eq _ _ i1 i2).trans (@BorelSpace.measurable_eq _ _ _ Pi.borelSpace).symm
  let β : (BlockIx a r → Ad E) ≃ₜ+ (UPos a r → Ad E) :=
    { toFun := fun x p => x (ixEq a r p)
      invFun := fun x p => x ((ixEq a r).symm p)
      left_inv := fun x => rfl
      right_inv := fun x => rfl
      map_add' := fun x y => rfl
      continuous_toFun := continuous_pi fun p => continuous_apply _
      continuous_invFun := continuous_pi fun p => continuous_apply _ }
  let e : unipLattice E a r ≃ ratN E a r :=
    { toFun := fun y => ⟨β.symm y, by
        obtain ⟨_, y, rfl⟩ := y
        exact ⟨fun p => y ((ixEq a r).symm p), rfl⟩⟩
      invFun := fun x => ⟨β x, by
        obtain ⟨_, y, rfl⟩ := x
        exact ⟨fun p => y (ixEq a r p), rfl⟩⟩
      left_inv := fun y => Subtype.ext (β.apply_symm_apply y)
      right_inv := fun x => Subtype.ext (β.symm_apply_apply x) }
  let m := β.toHomeomorph.toMeasurableEquiv
  haveI : (μ.map m).IsAddHaarMeasure := β.isAddHaarMeasure_map μ
  have h2 := setIntegral_haar hl g (hφ r h0 h1 g) (μ.map m) (D := m '' 𝓕)
    (hF.image_of_equiv m.toEquiv (MeasurePreserving.symm m ⟨m.measurable, rfl⟩).quasiMeasurePreserving e fun y x => by
      change β (β.symm y + x) = y + β x
      rw [map_add, β.apply_symm_apply])
  rw [m.measurableEmbedding.setIntegral_map, m.injective.preimage_image] at h2
  rw [← h2]
  congr 1
  funext x
  exact congrArg (fun u => φ (u * g)) (unipGL_ixEq x).symm

open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.ConvolutionTheory.R2.Pp in
/- English proof (translation)
Introduce `r hr hr2 g`. Take `rfl : r = 1` from `by omega`. Use `letI : Unique (UPos 2 1) := ⟨⟨⟨(0, 1), by decide⟩⟩, by decide⟩`. Rewrite using `[← h0 g, ← int_one (ι := UPos 2 1)]`. Use `integral_congr_ae (Eventually.of_forall fun x => ?_)` and prove the remaining obligations.

Establish `: gl (nU (x default)) = unipGL x`. Use `Units.ext ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(nU (x default)).1 = unipMatrix x`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [nU, unipMatrix, blockEntry_apply]`.

Both sides reduce to the same expression. Simplify using `only [this]`.
-/
private theorem found_cusp {E : Type} [Field E] [NumberField E] {Φ : GL (Fin 2) (A E) → ℂ}
    (h0 : ∀ h, ∫ b in fundamentalSet E, Φ (gl (nU b) * h) ∂(adeleMeasure E) = 0) :
    AutomorphicForm.IsCuspidal Φ := by
  intro r hr hr2 g
  obtain rfl : r = 1 := by omega
  letI : Unique (UPos 2 1) := ⟨⟨⟨(0, 1), by decide⟩⟩, by decide⟩
  rw [← h0 g, ← int_one (ι := UPos 2 1)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  have : gl (nU (x default)) = unipGL x := by
    refine Units.ext ?_
    change (nU (x default)).1 = unipMatrix x
    ext i j
    fin_cases i <;> fin_cases j <;> simp [nU, unipMatrix, blockEntry_apply]
    rfl
  simp only [this]

/- English proof (translation)
Introduce `E _ _ Φ hl h0`. Conclude with `cusp_of hl (found_cusp h0)`.
-/
theorem UpperTheory.ConvolutionTheory.R2.G.cuspOf :
    ∀ (E : Type) [Field E] [NumberField E] (Φ : GL (Fin 2) (A E) → ℂ), (∀ γ h, Φ (ratGL E 2 γ * h) = Φ h) →
    (∀ h, ∫ b in fundamentalSet E, Φ (gl (nU b) * h) ∂(adeleMeasure E) = 0) → GlobalTheory.CuspRep.IsCuspidal Φ := by
  intro E _ _ Φ hl h0
  exact cusp_of hl (found_cusp h0)
