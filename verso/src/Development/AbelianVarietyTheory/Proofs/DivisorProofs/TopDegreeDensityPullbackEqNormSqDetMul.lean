import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst

set_option autoImplicit false

noncomputable section

open Matrix
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open scoped ComplexConjugate

namespace GlobalTheory.CxForm

open Module

variable {K M : Type} [Field K] [AddCommGroup M] [Module K M]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Separate the alternatives or extract the components of the hypothesis. Rewrite the indicated hypotheses using the stated equalities.

A detailed English derivation is pending.
-/
theorem exterior_repr_univ_of_mem {N k : ℕ} (b : Basis (Fin N) K M) (hk : k ≠ N) {x : ExteriorAlgebra K M}
    (hx : x ∈ ⋀[K]^k M) : b.ExteriorAlgebra.repr x Finset.univ = 0 := by
  rw [Basis.ExteriorAlgebra, Basis.repr_reindex_apply]
  have h1 : (Set.powersetCard.prodEquiv.symm (Finset.univ : Finset (Fin N))).1 = N := by
    simp [Set.powersetCard.prodEquiv]
  rcases e : Set.powersetCard.prodEquiv.symm (Finset.univ : Finset (Fin N)) with ⟨j, a⟩
  rw [e] at h1
  exact DirectSum.IsInternal.collectedBasis_repr_of_mem_ne _ _ (fun h => hk (h.trans h1)) hx

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Substitute using the available equality. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify by unfolding definitions. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify by unfolding definitions. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem exterior_repr_univ_map {N : ℕ} (b : Basis (Fin N) K M) (f : M →ₗ[K] M) (x : ExteriorAlgebra K M) :
    b.ExteriorAlgebra.repr (ExteriorAlgebra.map f x) Finset.univ =
      LinearMap.det f * b.ExteriorAlgebra.repr x Finset.univ := by
  have key : ∀ s, b.ExteriorAlgebra.repr (ExteriorAlgebra.map f (b.ExteriorAlgebra s)) Finset.univ =
      LinearMap.det f * b.ExteriorAlgebra.repr (b.ExteriorAlgebra s) Finset.univ := by
    intro s
    by_cases hs : s = Finset.univ
    · subst hs
      set g : M [⋀^Fin N]→ₗ[K] K :=
        (Finsupp.lapply Finset.univ ∘ₗ b.ExteriorAlgebra.repr.toLinearMap).compAlternatingMap
          (ExteriorAlgebra.ιMulti K N) with hg
      have hb : ∀ w : Fin N → M, g w = b.ExteriorAlgebra.repr (ExteriorAlgebra.ιMulti K N w) Finset.univ := fun _ => rfl
      have he := AlternatingMap.eq_smul_basis_det b g
      rw [ExteriorAlgebra.basis_apply_ofCard _ (by simp : (Finset.univ : Finset (Fin N)).card = N)]
      dsimp only [ExteriorAlgebra.ιMulti_family]
      rw [ExteriorAlgebra.map_apply_ιMulti, ← hb, ← hb, he,
        AlternatingMap.smul_apply, AlternatingMap.smul_apply, Basis.det_comp, smul_eq_mul, smul_eq_mul]
      ring
    · have hc : s.card ≠ N := fun h => hs (Finset.eq_univ_of_card s (by simpa using h))
      rw [Basis.repr_self, Finsupp.single_apply, if_neg hs, mul_zero,
        ExteriorAlgebra.basis_apply]
      dsimp only [ExteriorAlgebra.ιMulti_family]
      rw [ExteriorAlgebra.map_apply_ιMulti]
      exact exterior_repr_univ_of_mem b hc (ExteriorAlgebra.ιMulti_range K _ ⟨_, rfl⟩)
  have := b.ExteriorAlgebra.ext
    (f₁ := Finsupp.lapply Finset.univ ∘ₗ b.ExteriorAlgebra.repr.toLinearMap ∘ₗ (ExteriorAlgebra.map f).toLinearMap)
    (f₂ := LinearMap.det f • (Finsupp.lapply Finset.univ ∘ₗ b.ExteriorAlgebra.repr.toLinearMap))
    (fun s => by simpa using key s)
  simpa using LinearMap.congr_fun this x

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Establish an intermediate fact.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem det_pull_gen {n : ℕ} (L : V n →L[ℂ] V n) :
    LinearMap.det (Matrix.toLin' (fromBlocks (of fun b a => L (coordVec b) a) 0 0
      (of fun b a => conj (L (coordVec b) a)))) = ((‖L.det‖ ^ 2 : ℝ) : ℂ) := by
  rw [LinearMap.det_toLin', det_fromBlocks_zero₂₁]
  have hP : (of fun b a => L (coordVec b) a).det = L.det := by
    rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin n) ℂ).toBasis,
      ← det_transpose]
    congr 1
  have hQ : (of fun b a => conj (L (coordVec b) a)) = (starRingEnd ℂ).mapMatrix (of fun b a => L (coordVec b) a) := by
    ext i j; simp
  rw [hQ, ← RingHom.map_det, hP, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem dens_pull {n : ℕ} (L : V n →L[ℂ] V n) (ω : Alt n) :
    dens (pull L ω) = ((‖L.det‖ ^ 2 : ℝ) : ℂ) * dens ω := by
  simp only [dens, pull, bas]
  rw [exterior_repr_univ_map, det_pull_gen, mul_div_assoc]

end GlobalTheory.CxForm
