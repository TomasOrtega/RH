import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff

noncomputable section

namespace GlobalTheory.SiegelOpen
open GlobalTheory

/- English proof (translation)
The claim follows from `continuous_matrix fun i j => (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)`.
-/
theorem continuous_tauU (g : ℕ) : Continuous (tauU (g := g)) :=
  continuous_matrix fun i j =>
    (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [tauU, transpose_apply, of_apply]`. Conclude with `s.2 j i`.
-/
theorem isSymm_tauU {g : ℕ} (s : symMat g) : (tauU s).IsSymm := by
  ext i j
  simp only [tauU, transpose_apply, of_apply]
  exact s.2 j i

/- English proof (translation)
Use `isOpen_iff_mem_nhds.mpr fun s hs => ?_` and prove the remaining obligations. Use `filter_upwards [(continuous_tauU g).continuousAt.eventually (IsSiegel.eventually_isSiegel hs)] with t ht`. Conclude with `ht (isSymm_tauU t)`.
-/
theorem isOpen_siegel (g : ℕ) : IsOpen (siegel g) := by
  refine isOpen_iff_mem_nhds.mpr fun s hs => ?_
  filter_upwards [(continuous_tauU g).continuousAt.eventually
    (IsSiegel.eventually_isSiegel hs)] with t ht
  exact ht (isSymm_tauU t)

/- English proof (translation)
The claim follows from `(((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin g => ℂ) j).comp (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin g => Fin g → ℂ) i)).comp (Submodule.subtypeL (symMat g))).differentiable`.
-/
theorem differentiable_tauU_apply (g : ℕ) (i j : Fin g) :
    Differentiable ℂ (fun s : symMat g => tauU s i j) :=
  (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin g => ℂ) j).comp
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin g => Fin g → ℂ) i)).comp
      (Submodule.subtypeL (symMat g))).differentiable

/- English proof (translation)
Introduce `x hx y hy a b ha hb hab`. Use `⟨isSymm_tauU _, ?_⟩` and prove the remaining obligations. Establish `e : (tauU (a • x + b • y)).map Complex.im = a • (tauU x).map Complex.im + b • (tauU y).map Complex.im`. Use extensionality with `i j`. Simplify using `[tauU]`.

Rewrite using `[e]`. Break down `ha.eq_or_lt with rfl | ha'` into its components or cases. Establish `: b = 1` using `by simpa using hab`. Substitute `this` using the available equality. Simplify using `using hy.2`.

Conclude with `(hx.2.smul ha').add_posSemidef (hy.2.posSemidef.smul hb)`.
-/
theorem convex_siegel (g : ℕ) : Convex ℝ (siegel g) := by
  intro x hx y hy a b ha hb hab
  refine ⟨isSymm_tauU _, ?_⟩
  have e : (tauU (a • x + b • y)).map Complex.im =
      a • (tauU x).map Complex.im + b • (tauU y).map Complex.im := by
    ext i j
    simp [tauU]
  rw [e]
  rcases ha.eq_or_lt with rfl | ha'
  · have : b = 1 := by simpa using hab
    subst this
    simpa using hy.2
  · exact (hx.2.smul ha').add_posSemidef (hy.2.posSemidef.smul hb)

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨Matrix.of fun i j => (Complex.I • (1 : Matrix (Fin g) (Fin g) ℂ)) i j, fun i j => by simp [Matrix.one_apply, eq_comm]⟩, isSiegel_I_smul_one (ι := Fin g)⟩`.
-/
theorem siegel_nonempty (g : ℕ) : (siegel g).Nonempty :=
  ⟨⟨Matrix.of fun i j => (Complex.I • (1 : Matrix (Fin g) (Fin g) ℂ)) i j, fun i j => by
    simp [Matrix.one_apply, eq_comm]⟩, isSiegel_I_smul_one (ι := Fin g)⟩

/- English proof (translation)
Use `haveI := (convex_siegel g).contractibleSpace (siegel_nonempty g)`. Use `infer_instance`.
-/
theorem simplyConnected_siegel (g : ℕ) : SimplyConnectedSpace (siegel g) := by
  haveI := (convex_siegel g).contractibleSpace (siegel_nonempty g)
  infer_instance

/- English proof (translation)
Introduce `g` and use `⟨⟨isOpen_siegel g, fun i j => (differentiable_tauU_apply g i j).differentiableOn, fun _ hb => hb⟩, simplyConnected_siegel g⟩`.
-/
theorem isPeriodMap_tauU_and_simplyConnected :
    ∀ g : ℕ, IsPeriodMap (siegel g) tauU ∧ SimplyConnectedSpace (siegel g) := fun g =>
  ⟨⟨isOpen_siegel g, fun i j => (differentiable_tauU_apply g i j).differentiableOn,
    fun _ hb => hb⟩, simplyConnected_siegel g⟩

end GlobalTheory.SiegelOpen
