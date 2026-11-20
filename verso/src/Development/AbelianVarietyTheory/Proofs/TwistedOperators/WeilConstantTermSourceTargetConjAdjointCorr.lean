import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CompatibleThetaRestrictions
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistSwap

open GlobalTheory.MixModel

variable {D : D7}

/- English proof (translation)
Take `⟨i1, i2, i3, i4, i5, -⟩` from `lattice_Mx D a b`. Take `⟨j1, j2, j3, j4, j5, -⟩` from `lattice_Mx D c d`. Use `haveI : BorelSpace (Mx D a b) := ⟨rfl⟩`. Use `haveI : BorelSpace (Mx D c d) := ⟨rfl⟩`. Set `m : Mx D a b ≃ᵐ Mx D c d` to `{ toEquiv := f.toEquiv measurable_toFun := hf.measurable measurable_invFun := hfs.measurable }`.

Establish `hm : (m : Mx D a b → Mx D c d) = f` using `rfl`. Establish `hmp : MeasurePreserving m μ (μ.map f)` using `⟨m.measurable, rfl⟩`. Establish `hmp' : MeasurePreserving f.symm (μ.map f) μ` using `hmp.symm`. Establish `hpre : f ⁻¹' (f.symm ⁻¹' 𝓖) = 𝓖`. Use extensionality with `y`.

Simplify using the standard rewrite rules. Take `⟨hμ, hF, h1⟩` from `h`. Use `⟨⟨f.isAddHaarMeasure_map μ hf hfs, ?_, ?_⟩, fun g => ?_⟩` and prove the remaining obligations. Set `e : ratMx D a b → ratMx D c d` to `fun y => ⟨f y, (hΓ _).2 y.2⟩`. Establish `he : Function.Bijective e`.

Prove the components needed by the constructor for the conclusion. Introduce `x y hxy`. Conclude with `Subtype.ext (f.injective (congrArg Subtype.val hxy))`. Introduce `x`. Use `⟨⟨f.symm x, (hΓ _).1 (by simpa using x.2)⟩, Subtype.ext ?_⟩` and prove the remaining obligations.

Simplify using `[e]`. Use `hF.preimage_of_equiv hmp'.quasiMeasurePreserving he ?_` and prove the remaining obligations. Introduce `y x`. Simplify using `[e, AddSubgroup.vadd_def]`. Rewrite using `[← hm, MeasurableEquiv.map_apply, hm, hpre, h1]`.

Rewrite using `[← hm, m.measurableEmbedding.setIntegral_map, hm, hpre]`.
-/
theorem covolOne_map {a b c d : ℕ} (f : Mx D a b ≃+ Mx D c d) (hf : Continuous f) (hfs : Continuous f.symm)
    (hΓ : ∀ x, f x ∈ ratMx D c d ↔ x ∈ ratMx D a b) {μ : Measure (Mx D a b)} {𝓖 : Set (Mx D a b)}
    (h : IsCovolOne (ratMx D a b) μ 𝓖) :
    IsCovolOne (ratMx D c d) (μ.map f) (f.symm ⁻¹' 𝓖) ∧
      ∀ g : Mx D c d → ℂ, ∫ x in f.symm ⁻¹' 𝓖, g x ∂(μ.map f) = ∫ y in 𝓖, g (f y) ∂μ := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := lattice_Mx D a b
  obtain ⟨j1, j2, j3, j4, j5, -⟩ := lattice_Mx D c d
  haveI : BorelSpace (Mx D a b) := ⟨rfl⟩
  haveI : BorelSpace (Mx D c d) := ⟨rfl⟩
  let m : Mx D a b ≃ᵐ Mx D c d :=
    { toEquiv := f.toEquiv
      measurable_toFun := hf.measurable
      measurable_invFun := hfs.measurable }
  have hm : (m : Mx D a b → Mx D c d) = f := rfl
  have hmp : MeasurePreserving m μ (μ.map f) := ⟨m.measurable, rfl⟩
  have hmp' : MeasurePreserving f.symm (μ.map f) μ := hmp.symm
  have hpre : f ⁻¹' (f.symm ⁻¹' 𝓖) = 𝓖 := by
    ext y; simp
  obtain ⟨hμ, hF, h1⟩ := h
  refine ⟨⟨f.isAddHaarMeasure_map μ hf hfs, ?_, ?_⟩, fun g => ?_⟩
  · let e : ratMx D a b → ratMx D c d := fun y => ⟨f y, (hΓ _).2 y.2⟩
    have he : Function.Bijective e := by
      constructor
      · intro x y hxy
        exact Subtype.ext (f.injective (congrArg Subtype.val hxy))
      · intro x
        refine ⟨⟨f.symm x, (hΓ _).1 (by simpa using x.2)⟩, Subtype.ext ?_⟩
        simp [e]
    refine hF.preimage_of_equiv hmp'.quasiMeasurePreserving he ?_
    intro y x
    simp [e, AddSubgroup.vadd_def]
  · rw [← hm, MeasurableEquiv.map_apply, hm, hpre, h1]
  · rw [← hm, m.measurableEmbedding.setIntegral_map, hm, hpre]

def swapE (S : HSp D) (t : ℕ) : Mx D S.rank t ≃+ Mx D t S.rank where
  toFun y := adj y ⬝ gA S
  invFun x := giA S ⬝ adj x
  left_inv y := by
    simp only [adj_mul, adj_gA, adj_adj, giA_gA_cancel]
  right_inv x := by
    simp only [adj_mul, adj_giA, adj_adj, Matrix.mul_assoc, giA_mul_gA, Matrix.mul_one]
  map_add' x y := by
    simp only [adj_add, Matrix.add_mul]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem swapE_apply (S : HSp D) (t : ℕ) (y : Mx D S.rank t) : swapE S t y = adj y ⬝ gA S := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem swapE_symm_apply (S : HSp D) (t : ℕ) (x : Mx D t S.rank) : (swapE S t).symm x = giA S ⬝ adj x := rfl

/- English proof (translation)
The claim follows from `continuous_adj.matrix_mul continuous_const`.
-/
theorem continuous_swapE (S : HSp D) (t : ℕ) : Continuous (swapE S t) :=
  continuous_adj.matrix_mul continuous_const

/- English proof (translation)
The claim follows from `continuous_const.matrix_mul continuous_adj`.
-/
theorem continuous_swapE_symm (S : HSp D) (t : ℕ) : Continuous (swapE S t).symm :=
  continuous_const.matrix_mul continuous_adj

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hy`. Establish `e : y = (swapE S t).symm (swapE S t y)` using `((swapE S t).symm_apply_apply y).symm`. Rewrite using `[e, swapE_symm_apply]`. Conclude with `ratMx_mul (rat_mem _) (ratMx_adj hy)`.

Introduce `hy`. Conclude with `ratMx_mul (ratMx_adj hy) (rat_mem _)`.
-/
theorem swapE_mem_iff (S : HSp D) (t : ℕ) (y : Mx D S.rank t) :
    swapE S t y ∈ ratMx D t S.rank ↔ y ∈ ratMx D S.rank t := by
  constructor
  · intro hy
    have e : y = (swapE S t).symm (swapE S t y) := ((swapE S t).symm_apply_apply y).symm
    rw [e, swapE_symm_apply]
    exact ratMx_mul (rat_mem _) (ratMx_adj hy)
  · intro hy
    exact ratMx_mul (ratMx_adj hy) (rat_mem _)

/- English proof (translation)
Rewrite using `[← swapE_mem_iff, AddEquiv.apply_symm_apply]`.
-/
theorem swapE_symm_mem_iff (S : HSp D) (t : ℕ) (x : Mx D t S.rank) :
    (swapE S t).symm x ∈ ratMx D S.rank t ↔ x ∈ ratMx D t S.rank := by
  rw [← swapE_mem_iff, AddEquiv.apply_symm_apply]

end GlobalTheory.TwistSwap

namespace GlobalTheory.TwistSwap

open GlobalTheory.MixModel

variable {D : D7}

/- English proof (translation)
Establish `e1 : ∀ {m n : ℕ} (x : Matrix (Fin m) (Fin n) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.adel x = rat x` using `fun _ => rfl`. Establish `e2 : ∀ {m n : ℕ} (x : Matrix (Fin m) (Fin n) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.ct x = xᴴ` using `fun _ => rfl`. Establish `e3 : ∀ (A B : HSp D) (z : WO B A), GlobalTheory.PairLift.adjO A B z = giA B ⬝ adj z ⬝ gA A` using `fun _ _ _ => rfl`. Establish `g1 : ∀ A : HSp D, rat A.gram = gA A` using `fun _ => rfl`. Establish `g2 : ∀ A : HSp D, rat A.gram⁻¹ = giA A` using `fun _ => rfl`.

Rewrite using `[e3, e3, e1, e1, e1, e2, e2, swapE_apply]`. Simplify using `only [e1, rat_mul, rat_conjTranspose, g1, g2, adj_add, adj_mul, adj_adj, adj_gA, adj_giA, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, giA_gA_cancel]`.
-/
theorem adjO_split (S T T' : HSp D) {t : ℕ} (ι : T'.V →ₗ[D.host.E] T.V) (C : Matrix (Fin T.rank) (Fin t) D.host.E)
    (y : Mx D S.rank t) (w' : WO T' S) :
    GlobalTheory.PairLift.adjO S T ((y : Matrix (Fin S.rank) (Fin t) (AE D)) *
                 GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.adel (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.ct C * T.gram) +
      (w' : Matrix (Fin S.rank) (Fin T'.rank) (AE D)) *
        GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.adel (T'.gram⁻¹ * GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.ct (frameMat T T' ι) * T.gram)) =
    GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.adel C * (swapE S t y : Matrix (Fin t) (Fin S.rank) (AE D)) +
      GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.adel (frameMat T T' ι) * GlobalTheory.PairLift.adjO S T' w' := by
  have e1 : ∀ {m n : ℕ} (x : Matrix (Fin m) (Fin n) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.adel x = rat x := fun _ => rfl
  have e2 : ∀ {m n : ℕ} (x : Matrix (Fin m) (Fin n) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.ct x = xᴴ := fun _ => rfl
  have e3 : ∀ (A B : HSp D) (z : WO B A), GlobalTheory.PairLift.adjO A B z = giA B ⬝ adj z ⬝ gA A := fun _ _ _ => rfl
  have g1 : ∀ A : HSp D, rat A.gram = gA A := fun _ => rfl
  have g2 : ∀ A : HSp D, rat A.gram⁻¹ = giA A := fun _ => rfl
  rw [e3, e3, e1, e1, e1, e2, e2, swapE_apply]
  simp only [e1, rat_mul, rat_conjTranspose, g1, g2, adj_add, adj_mul, adj_adj, adj_gA, adj_giA, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_assoc, giA_gA_cancel]

/- English proof (translation)
Introduce `D S T T' t ι C`. Establish `key : ∀ (μ : Measure (Mx D t S.rank)) (𝓖 : Set (Mx D t S.rank)) (μ' : Measure (Mx D S.rank t)) (𝓖' : Set (Mx D S.rank t)), (∀ G : Mx D t S.rank → ℂ, ∫ y in 𝓖', G (swapE S t y) ∂μ' = ∫ x in 𝓖, G x ∂μ) → ∀ φ : WO S T → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.r …`. Introduce `μ 𝓖 μ' 𝓖' hI φ`. Use function extensionality and compare the values at `w'`. Simplify using `only [GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.resS, GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.resT, GlobalTheory.PairLift.dag, adjO_split]`.

Rewrite using `[integral_conj, hI (fun x => φ (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.adel C * (x : Matrix (Fin t) (Fin S.rank) (AE D)) + GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.adel (frameMat T T' ι) * GlobalTheory.PairLift.adjO S T' w'))]`. Use `⟨fun μ 𝓖 h => ?_, fun μ' 𝓖' h => ?_⟩` and prove the remaining obligations. Take `⟨h1, h2⟩` from `covolOne_map (swapE S t).symm (continuous_swapE_symm S t) (continuous_swapE S t) (swapE_symm_mem_iff S t) h`. Use `⟨_, _, h1, key μ 𝓖 _ _ fun G => ?_⟩` and prove the remaining obligations. Conclude with `(h2 fun y => G (swapE S t y)).trans (by simp)`.

Take `⟨h1, h2⟩` from `covolOne_map (swapE S t) (continuous_swapE S t) (continuous_swapE_symm S t) (swapE_mem_iff S t) h`. Conclude with `⟨_, _, h1, key _ _ μ' 𝓖' fun G => (h2 G).symm⟩`.
-/
theorem res_dag_swap : ∀ (D : D7) (S T T' : HSp D) (t : ℕ) (ι : T'.V →ₗ[D.host.E] T.V) (C : Matrix (Fin T.rank) (Fin t) D.host.E), (∀ μ 𝓖, IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.ratMx D t S.rank) μ 𝓖 → ∃ μ' 𝓖', IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.ratMx D S.rank t) μ' 𝓖' ∧ ∀ φ : WO S T → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.resS T T' S ι C μ' 𝓖' (GlobalTheory.PairLift.dag S T φ) = GlobalTheory.PairLift.dag S T' (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.resT S T T' ι C μ 𝓖 φ)) ∧ ∀ μ' 𝓖', IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.ratMx D S.rank t) μ' 𝓖' → ∃ μ 𝓖, IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.ratMx D t S.rank) μ 𝓖 ∧ ∀ φ : WO S T → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.resS T T' S ι C μ' 𝓖' (GlobalTheory.PairLift.dag S T φ) = GlobalTheory.PairLift.dag S T' (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.resT S T T' ι C μ 𝓖 φ) := by
  intro D S T T' t ι C
  have key : ∀ (μ : Measure (Mx D t S.rank)) (𝓖 : Set (Mx D t S.rank)) (μ' : Measure (Mx D S.rank t))
      (𝓖' : Set (Mx D S.rank t)),
      (∀ G : Mx D t S.rank → ℂ, ∫ y in 𝓖', G (swapE S t y) ∂μ' = ∫ x in 𝓖, G x ∂μ) →
      ∀ φ : WO S T → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.resS T T' S ι C μ' 𝓖' (GlobalTheory.PairLift.dag S T φ) =
        GlobalTheory.PairLift.dag S T' (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.resT S T T' ι C μ 𝓖 φ) := by
    intro μ 𝓖 μ' 𝓖' hI φ
    funext w'
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.resS, GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.resT, GlobalTheory.PairLift.dag, adjO_split]
    rw [integral_conj, hI (fun x => φ (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.adel C * (x : Matrix (Fin t) (Fin S.rank) (AE D)) +
      GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.adel (frameMat T T' ι) * GlobalTheory.PairLift.adjO S T' w'))]
  refine ⟨fun μ 𝓖 h => ?_, fun μ' 𝓖' h => ?_⟩
  · obtain ⟨h1, h2⟩ := covolOne_map (swapE S t).symm (continuous_swapE_symm S t) (continuous_swapE S t)
      (swapE_symm_mem_iff S t) h
    refine ⟨_, _, h1, key μ 𝓖 _ _ fun G => ?_⟩
    exact (h2 fun y => G (swapE S t y)).trans (by simp)
  · obtain ⟨h1, h2⟩ := covolOne_map (swapE S t) (continuous_swapE S t) (continuous_swapE_symm S t) (swapE_mem_iff S t) h
    exact ⟨_, _, h1, key _ _ μ' 𝓖' fun G => (h2 G).symm⟩

end GlobalTheory.TwistSwap
