import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StProjBundleArith
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsSmoothHermOfIsPullHermInl
import GroundTheory.HeightsAndTheta.Heights.Intersections.StProjBundleMultiHomog
import GroundTheory.HeightsAndTheta.Heights.Intersections.StProjBundleDim
import GroundTheory.HeightsAndTheta.Heights.Intersections.PProjBundleFibre
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

section Lemmas

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [Fintype K] [∀ k, Fintype (ι k)] in

/- English proof (translation)
Express the relevant statement in the definitionally equal form `f ∈ imageZ (inlV (ι₂ := fun _ : Unit => Fin N1)) (projBundleIdeal P B) ↔ f ∈ P`. Rewrite using `[imageZ_projBundleIdeal]`.
-/
theorem rename_inlV_mem_projBundleIdeal_iff (P : Ideal (MRing ι)) {N1 n : ℕ}
    (B : Matrix (Fin n) (Fin N1) (FnField P)) (f : MRing ι) :
    rename (inlV (ι₂ := fun _ : Unit => Fin N1)) f ∈ projBundleIdeal P B ↔ f ∈ P := by
  change f ∈ imageZ (inlV (ι₂ := fun _ : Unit => Fin N1)) (projBundleIdeal P B) ↔ f ∈ P
  rw [imageZ_projBundleIdeal]

end Lemmas

/- English proof (translation)
Introduce `K _ ι _ N1 t P d c m B hP hQ hB`. Establish `hP'` using `hP`. Take `⟨hK, ⟨_, _, hPr⟩, hPz, hPd⟩` from `hP`. Establish `hmem` using `rename_inlV_mem_projBundleIdeal_iff P B`. Use `⟨inferInstance, ⟨RingHom.ker_isPrime _, hMH K ι N1 t 2 P d c m B hP' hQ hB, ?_⟩, ?_, ?_⟩` and prove the remaining obligations.

Introduce and unpack `(k | u)`. Take `⟨i, hi⟩` from `hPr k`. Use `⟨i, fun h => hi ((hmem _).1 ?_)⟩` and prove the remaining obligations. Simplify `h` using `[inlV]`. Take `⟨j, hj⟩` from `Function.ne_iff.mp (hB.1.ne_zero 0)`.

Use `⟨j, fun h => hj ?_⟩` and prove the remaining obligations. Establish `h' : projBundleMap P B (X ⟨Sum.inr u, j⟩) = 0` using `h`. Rewrite `h'` using `[projBundleMap_X_inr]`. Use `congrArg (coeff (Finsupp.single 0 1)) h'` as an intermediate fact. Simplify `this` using `[coeff_X, Finsupp.single_eq_single_iff]`.

Use extensionality with `z`. Rewrite using `[Ideal.mem_comap, Ideal.mem_bot]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h2 : (C z : MRing ι) ∈ P` using `(hmem (C z)).1 (by simpa using h)`.

Establish `h3 : z ∈ P.comap (C : ℤ →+* MRing ι)` using `h2`. Rewrite `h3` using `[hPz]`. Conclude with `h3`. Introduce and unpack `rfl`. Simplify using the standard rewrite rules.

Rewrite using `[hDim K ι N1 2 P d B hP' hB.1, hPd, ← Nat.cast_add]`. Use `congr 1`. Simplify using `[Fintype.card_sum]`. Use linear arithmetic over natural numbers and integers.
-/
theorem ProjBundleArith.proof (hMH : ProjBundleMultiHomog.Statement) (hDim : ProjBundleDim.Statement) :
    ProjBundleArith.Statement := by
  intro K _ ι _ N1 t P d c m B hP hQ hB
  have hP' := hP
  obtain ⟨hK, ⟨_, _, hPr⟩, hPz, hPd⟩ := hP
  have hmem := rename_inlV_mem_projBundleIdeal_iff P B
  refine ⟨inferInstance, ⟨RingHom.ker_isPrime _, hMH K ι N1 t 2 P d c m B hP' hQ hB, ?_⟩, ?_, ?_⟩
  · rintro (k | u)
    · obtain ⟨i, hi⟩ := hPr k
      refine ⟨i, fun h => hi ((hmem _).1 ?_)⟩
      simpa [inlV] using h
    · obtain ⟨j, hj⟩ := Function.ne_iff.mp (hB.1.ne_zero 0)
      refine ⟨j, fun h => hj ?_⟩
      have h' : projBundleMap P B (X ⟨Sum.inr u, j⟩) = 0 := h
      rw [projBundleMap_X_inr] at h'
      have := congrArg (coeff (Finsupp.single 0 1)) h'
      simpa [coeff_X, Finsupp.single_eq_single_iff] using this
  · ext z
    rw [Ideal.mem_comap, Ideal.mem_bot]
    constructor
    · intro h
      have h2 : (C z : MRing ι) ∈ P := (hmem (C z)).1 (by simpa using h)
      have h3 : z ∈ P.comap (C : ℤ →+* MRing ι) := h2
      rw [hPz] at h3
      exact h3
    · rintro rfl
      simp
  · rw [hDim K ι N1 2 P d B hP' hB.1, hPd, ← Nat.cast_add]
    congr 1
    simp [Fintype.card_sum]
    omega

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
