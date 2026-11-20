import Mathlib

namespace GlobalTheory.PolarU

open Module

/- English proof (translation)
Set `bE` to `Module.finBasis ℝ E`. Set `v : Fin (Module.finrank ℝ E) → W` to `fun i => j (bE i)`. Establish `hsum : ∀ c : Fin (Module.finrank ℝ E) → ℝ, j (∑ i, c i • bE i) = ∑ i, (c i : ℂ) • v i`. Introduce `c`. Rewrite using `[map_sum]`.

Conclude with `Finset.sum_congr rfl (fun i _ => hj (c i) (bE i))`. Establish `hli : LinearIndependent ℂ v`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg i`. Establish `key : j (∑ k, (g k).re • bE k) + Complex.I • j (∑ k, (g k).im • bE k) = 0`.

Rewrite using `[hsum, hsum, Finset.smul_sum, ← Finset.sum_add_distrib]`. Use `(Finset.sum_congr rfl (fun k _ => ?_)).trans hg` and prove the remaining obligations. Rewrite using `[smul_smul, ← add_smul, mul_comm Complex.I, Complex.re_add_im]`. Take `⟨h1, h2⟩` from `hinj _ _ key`. Establish `r1` using `Fintype.linearIndependent_iff.mp bE.linearIndependent (fun k => (g k).re) h1 i`.

Establish `r2` using `Fintype.linearIndependent_iff.mp bE.linearIndependent (fun k => (g k).im) h2 i`. Conclude with `Complex.ext (by simpa using r1) (by simpa using r2)`. Establish `hsp : ⊤ ≤ Submodule.span ℂ (Set.range v)`. Establish `hmem : ∀ a : E, j a ∈ Submodule.span ℂ (Set.range v)`. Introduce `a`.

Rewrite using `[← bE.sum_repr a, hsum]`. Conclude with `Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))`. Introduce `w _`. Take `⟨a, b, rfl⟩` from `hspan w`. Conclude with `Submodule.add_mem _ (hmem a) (Submodule.smul_mem _ _ (hmem b))`.

Set `bW : Basis (Fin (Module.finrank ℝ E)) ℂ W` to `Basis.mk hli hsp`. Establish `hbW : ∀ i, bW i = v i` using `fun i => Basis.mk_apply hli hsp i`. Establish `hmat : LinearMap.toMatrix bW bW S = (LinearMap.toMatrix bE bE T).map Complex.ofRealHom`. Use extensionality with `i k`. Establish `e : S (bW k) = ∑ l, ((bE.repr (T (bE k)) l : ℝ) : ℂ) • bW l`.

Simplify using `only [hbW]`. Rewrite using `[← hsum (bE.repr (T (bE k))), bE.sum_repr]`. Conclude with `hS (bE k)`. Rewrite using `[LinearMap.toMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply, e, bW.repr_sum_self]`. Both sides reduce to the same expression.

Rewrite using `[← LinearMap.det_toMatrix bW S, ← LinearMap.det_toMatrix bE T, hmat]`. Conclude with `(RingHom.map_det Complex.ofRealHom _).symm`.
-/
theorem det_complexification (E W : Type) [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    [AddCommGroup W] [Module ℂ W] (j : E →+ W) (T : E →ₗ[ℝ] E) (S : W →ₗ[ℂ] W)
    (hj : ∀ (t : ℝ) (x : E), j (t • x) = (t : ℂ) • j x)
    (hspan : ∀ w, ∃ a b, w = j a + Complex.I • j b)
    (hinj : ∀ a b, j a + Complex.I • j b = 0 → a = 0 ∧ b = 0)
    (hS : ∀ x, S (j x) = j (T x)) :
    LinearMap.det S = ((LinearMap.det T : ℝ) : ℂ) := by
  classical
  let bE := Module.finBasis ℝ E
  let v : Fin (Module.finrank ℝ E) → W := fun i => j (bE i)

  have hsum : ∀ c : Fin (Module.finrank ℝ E) → ℝ, j (∑ i, c i • bE i) = ∑ i, (c i : ℂ) • v i := by
    intro c
    rw [map_sum]
    exact Finset.sum_congr rfl (fun i _ => hj (c i) (bE i))

  have hli : LinearIndependent ℂ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have key : j (∑ k, (g k).re • bE k) + Complex.I • j (∑ k, (g k).im • bE k) = 0 := by
      rw [hsum, hsum, Finset.smul_sum, ← Finset.sum_add_distrib]
      refine (Finset.sum_congr rfl (fun k _ => ?_)).trans hg
      rw [smul_smul, ← add_smul, mul_comm Complex.I, Complex.re_add_im]
    obtain ⟨h1, h2⟩ := hinj _ _ key
    have r1 := Fintype.linearIndependent_iff.mp bE.linearIndependent (fun k => (g k).re) h1 i
    have r2 := Fintype.linearIndependent_iff.mp bE.linearIndependent (fun k => (g k).im) h2 i
    exact Complex.ext (by simpa using r1) (by simpa using r2)

  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range v) := by
    have hmem : ∀ a : E, j a ∈ Submodule.span ℂ (Set.range v) := by
      intro a
      rw [← bE.sum_repr a, hsum]
      exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
    intro w _
    obtain ⟨a, b, rfl⟩ := hspan w
    exact Submodule.add_mem _ (hmem a) (Submodule.smul_mem _ _ (hmem b))
  let bW : Basis (Fin (Module.finrank ℝ E)) ℂ W := Basis.mk hli hsp
  have hbW : ∀ i, bW i = v i := fun i => Basis.mk_apply hli hsp i

  have hmat : LinearMap.toMatrix bW bW S = (LinearMap.toMatrix bE bE T).map Complex.ofRealHom := by
    ext i k
    have e : S (bW k) = ∑ l, ((bE.repr (T (bE k)) l : ℝ) : ℂ) • bW l := by
      simp only [hbW]
      rw [← hsum (bE.repr (T (bE k))), bE.sum_repr]
      exact hS (bE k)
    rw [LinearMap.toMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply, e, bW.repr_sum_self]
    rfl
  rw [← LinearMap.det_toMatrix bW S, ← LinearMap.det_toMatrix bE T, hmat]
  exact (RingHom.map_det Complex.ofRealHom _).symm

end GlobalTheory.PolarU
