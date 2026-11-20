import Mathlib
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.IntToFracInjective
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LogGaussNormSupportFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Use `gaussNormOf_le w (gaussNormOf_nonneg w x) fun d => ?_` and prove the remaining obligations. Distinguish the cases in `hd : ∃ m, Finsupp.mapDomain f m = d`. Take `⟨m, rfl⟩` from `hd`. Rewrite using `[coeff_rename_mapDomain f hf]`.

Conclude with `le_gaussNormOf w x m`. Rewrite using `[coeff_rename_eq_zero f x d fun m h => (hd ⟨m, h⟩).elim, map_zero]`. Conclude with `gaussNormOf_nonneg w x`. Use `gaussNormOf_le w (gaussNormOf_nonneg w _) fun m => ?_` and prove the remaining obligations. Rewrite using `[← coeff_rename_mapDomain f hf]`.

Conclude with `le_gaussNormOf w _ _`.
-/
theorem gaussNormOf_rename {R : Type*} [CommRing R] (w : AbsoluteValue R ℝ) {σ τ : Type*}
    {f : σ → τ} (hf : Function.Injective f) (x : MvPolynomial σ R) :
    gaussNormOf w (rename f x) = gaussNormOf w x := by
  classical
  apply le_antisymm
  · refine gaussNormOf_le w (gaussNormOf_nonneg w x) fun d => ?_
    by_cases hd : ∃ m, Finsupp.mapDomain f m = d
    · obtain ⟨m, rfl⟩ := hd
      rw [coeff_rename_mapDomain f hf]
      exact le_gaussNormOf w x m
    · rw [coeff_rename_eq_zero f x d fun m h => (hd ⟨m, h⟩).elim, map_zero]
      exact gaussNormOf_nonneg w x
  · refine gaussNormOf_le w (gaussNormOf_nonneg w _) fun m => ?_
    rw [← coeff_rename_mapDomain f hf]
    exact le_gaussNormOf w _ _

/- English proof (translation)
Unfold `specFirst`. Rewrite using `[map_bind₁]`. Use `congr 2`. Use function extensionality and compare the values at `ij`. Break down `ij with ⟨i, j⟩` into its components or cases.

Use `Fin.cases ?_ (fun i => ?_) i` and prove the remaining obligations. Simplify using `[specFirstVar]`. Simplify using `[specFirstVar]`.
-/
theorem specFirst_map {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S) {n k : ℕ}
    (g : MvPolynomial (Fin (k + 1) × Fin n) R) (u : Fin n → R) :
    specFirst (g.map φ) (fun j => φ (u j)) = (specFirst g u).map φ := by
  unfold specFirst
  rw [map_bind₁]
  congr 2
  funext ij
  rcases ij with ⟨i, j⟩
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [specFirstVar]
  · simp [specFirstVar]

/- English proof (translation)
Take `⟨m, hm⟩` from `hg`. Apply `le_antisymm` to reduce the goal to its premises. Use `gaussNormOf_le _ zero_le_one fun d => ?_` and prove the remaining obligations. Rewrite using `[coeff_map, ← FinitePlace.norm_embedding]`. Conclude with `FinitePlace.norm_le_one K (v := v) (g.coeff d)`.

Establish `h1` using `le_gaussNormOf (NumberField.HeightOneSpectrum.adicAbv K v) (g.map (algebraMap (𝓞 K) K)) m`. Rewrite `h1` using `[coeff_map, ← FinitePlace.norm_embedding, (FinitePlace.norm_eq_one_iff_notMem K (v := v) _).mpr hm]`. Conclude with `h1`.
-/
theorem gaussNorm_map_eq_one {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    {σ : Type*} (g : MvPolynomial σ (𝓞 K)) (hg : ∃ m, g.coeff m ∉ v.asIdeal) :
    gaussNorm v (g.map (algebraMap (𝓞 K) K)) = 1 := by
  obtain ⟨m, hm⟩ := hg
  apply le_antisymm
  · refine gaussNormOf_le _ zero_le_one fun d => ?_
    rw [coeff_map, ← FinitePlace.norm_embedding]
    exact FinitePlace.norm_le_one K (v := v) (g.coeff d)
  · have h1 := le_gaussNormOf (NumberField.HeightOneSpectrum.adicAbv K v) (g.map (algebraMap (𝓞 K) K)) m
    rw [coeff_map, ← FinitePlace.norm_embedding, (FinitePlace.norm_eq_one_iff_notMem K (v := v) _).mpr hm] at h1
    exact h1

/- English proof (translation)
Introduce `K _ _ n e I g u v hI hf hu hprim`. Use `h3 K e n v` as an intermediate fact. Establish `hord` using `h1 K n e I g u v hI hf hu hprim`. Use `⟨?_, gaussNorm_map_eq_one v g hprim⟩` and prove the remaining obligations. Use `set h := rename (Sum.inl : Fin e × Fin n → Par e n) (specFirst g u) with hh`.

Establish `hne : h ≠ 0`. Introduce `h0`. Rewrite `hord` using `[h0, map_zero, Ring.ord_eq_addVal, IsDiscreteValuationRing.addVal_zero]`. Conclude with `ENat.top_ne_natCast _ hord`. Establish `hG` using `h2 K e n v h hne`.

Rewrite `hG` using `[hord, ENat.toNat_natCast]`. Establish `hmap : h.map (algebraMap (𝓞 K) K) = rename (Sum.inl : Fin e × Fin n → Par e n) ((specFirst g u).map (algebraMap (𝓞 K) K))`. Rewrite using `[hh, map_rename]`. Rewrite `hG` using `[hmap, gaussNorm_eq_gaussNormOf, gaussNormOf_rename _ Sum.inl_injective, ← gaussNorm_eq_gaussNormOf, ← specFirst_map]`. Conclude with `hG`.
-/
theorem GaussEq.proof (h1 : OrdEq.Statement) (h2 : GaussDVR.Statement) (h3 : ParDVRIsDVR.Statement) :
    GaussEq.Statement := by
  intro K _ _ n e I g u v hI hf hu hprim
  have := h3 K e n v
  have hord := h1 K n e I g u v hI hf hu hprim
  refine ⟨?_, gaussNorm_map_eq_one v g hprim⟩
  set h := rename (Sum.inl : Fin e × Fin n → Par e n) (specFirst g u) with hh
  have hne : h ≠ 0 := by
    intro h0
    rw [h0, map_zero, Ring.ord_eq_addVal, IsDiscreteValuationRing.addVal_zero] at hord
    exact ENat.top_ne_natCast _ hord
  have hG := h2 K e n v h hne
  rw [hord, ENat.toNat_natCast] at hG
  have hmap : h.map (algebraMap (𝓞 K) K) =
      rename (Sum.inl : Fin e × Fin n → Par e n) ((specFirst g u).map (algebraMap (𝓞 K) K)) := by
    rw [hh, map_rename]
  rw [hmap, gaussNorm_eq_gaussNormOf, gaussNormOf_rename _ Sum.inl_injective, ← gaussNorm_eq_gaussNormOf,
    ← specFirst_map] at hG
  exact hG

end

end GroundTheory.Heights₂.Heights.Vertical
