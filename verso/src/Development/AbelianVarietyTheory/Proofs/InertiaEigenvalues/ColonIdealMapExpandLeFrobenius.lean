import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapMemA
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ImageStableDegreeBounds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowerSeriesExistsUniqueDecompOverFrobeniusLikeEnStatement
open PowerSeries GlobalTheory.BK Matrix GlobalTheory.LiftCoker

namespace GlobalTheory.LiftCoker

/- English proof (translation)
Introduce `O K _ _ _ _ _ l _ ι κ _ _ G`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `α hα`. Rewrite using `[Ideal.mem_comap, mem_colon]`. Introduce `w hw`.

Establish `hl2 : 2 ≤ l` using `(Fact.out : l.Prime).two_le`. Establish `hf : ∀ i, ∃ f : O⟦X⟧, PowerSeries.map (algebraMap O K) f = w i` using `fun i => by`. Take `⟨f, hf⟩` from `(equivA O K).surjective ⟨w i, hw i⟩`. Conclude with `⟨f, by rw [← coe_equivA, hf]⟩`. Use `choose f hf using hf`.

Establish `hdec` using `fun i => (GlobalTheory.T.powerSeries_existsUnique_decomp_over_frobeniusLike_endo l hl2 (PowerSeries.expand l (Fact.out : l.Prime).ne_zero) (fun g m => PowerSeries.coeff_expand _ _ g) (f i)).exists`. Use `choose g hg using hdec`. Establish `hα'` using `fun j : Fin l => (mem_colon.1 hα) (fun i => PowerSeries.map (algebraMap O K) (g i j)) (fun i => map_mem_A _)`. Use `choose m hm hmeq using hα'`. Establish `hX : (X : K⟦X⟧) ∈ A O K` using `by simpa using map_mem_A (O := O) (K := K) X`.

Use `⟨∑ j : Fin l, (X : K⟦X⟧) ^ j.val • frobV l (m j), fun i => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.sum_apply]`. Use `Subalgebra.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Pi.smul_apply, smul_eq_mul, frobV_apply]`. Conclude with `mul_mem (pow_mem hX _) (frob_mem_A l (hm j i))`.

Use function extensionality and compare the values at `i`. Establish `hwi : w i = ∑ j : Fin l, (X : K⟦X⟧) ^ j.val * frob K l (PowerSeries.map (algebraMap O K) (g i j))`. Rewrite using `[← hf i, hg i, map_sum]`. Simplify using `[map_mul, map_pow, map_X, map_expand, frob]`. Establish `key : ∀ j : Fin l, frob K l (PowerSeries.map (algebraMap O K) α) * frob K l (PowerSeries.map (algebraMap O K) (g i j)) = (G.map (frob K l) *ᵥ frobV l (m j)) i`.

Introduce `j`. Rewrite using `[← map_mul]`. Use `congrFun (hmeq j) i` as an intermediate fact. Rewrite `this` using `[Pi.smul_apply, smul_eq_mul]`. Rewrite using `[this]`.

Conclude with `RingHom.map_mulVec (frob K l).toRingHom G (m j) i`. Rewrite using `[Pi.smul_apply, smul_eq_mul, map_expand, hwi, Finset.mul_sum, Matrix.mulVec_sum, Finset.sum_apply]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, ← key j]`. Simplify using `only [frob]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem colon_map_expand_le : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] (l : ℕ) [Fact l.Prime] (ι κ : Type) [Fintype ι] [Fintype κ] (G : Matrix κ ι K⟦X⟧),
    (colon O K G).map (PowerSeries.expand l (Fact.out : l.Prime).ne_zero) ≤ colon O K (G.map (frob K l)) := by
  intro O K _ _ _ _ _ l _ ι κ _ _ G
  rw [Ideal.map_le_iff_le_comap]
  intro α hα
  rw [Ideal.mem_comap, mem_colon]
  intro w hw
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hf : ∀ i, ∃ f : O⟦X⟧, PowerSeries.map (algebraMap O K) f = w i := fun i => by
    obtain ⟨f, hf⟩ := (equivA O K).surjective ⟨w i, hw i⟩
    exact ⟨f, by rw [← coe_equivA, hf]⟩
  choose f hf using hf
  have hdec := fun i => (GlobalTheory.T.powerSeries_existsUnique_decomp_over_frobeniusLike_endo l hl2 (PowerSeries.expand l (Fact.out : l.Prime).ne_zero)
    (fun g m => PowerSeries.coeff_expand _ _ g) (f i)).exists
  choose g hg using hdec
  have hα' := fun j : Fin l => (mem_colon.1 hα) (fun i => PowerSeries.map (algebraMap O K) (g i j))
    (fun i => map_mem_A _)
  choose m hm hmeq using hα'
  have hX : (X : K⟦X⟧) ∈ A O K := by simpa using map_mem_A (O := O) (K := K) X
  refine ⟨∑ j : Fin l, (X : K⟦X⟧) ^ j.val • frobV l (m j), fun i => ?_, ?_⟩
  · rw [Finset.sum_apply]
    refine Subalgebra.sum_mem _ fun j _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, frobV_apply]
    exact mul_mem (pow_mem hX _) (frob_mem_A l (hm j i))
  · funext i
    have hwi : w i = ∑ j : Fin l, (X : K⟦X⟧) ^ j.val * frob K l (PowerSeries.map (algebraMap O K) (g i j)) := by
      rw [← hf i, hg i, map_sum]
      simp [map_mul, map_pow, map_X, map_expand, frob]
    have key : ∀ j : Fin l, frob K l (PowerSeries.map (algebraMap O K) α) *
        frob K l (PowerSeries.map (algebraMap O K) (g i j)) = (G.map (frob K l) *ᵥ frobV l (m j)) i := by
      intro j
      rw [← map_mul]
      have := congrFun (hmeq j) i
      rw [Pi.smul_apply, smul_eq_mul] at this
      rw [this]
      exact RingHom.map_mulVec (frob K l).toRingHom G (m j) i
    rw [Pi.smul_apply, smul_eq_mul, map_expand, hwi, Finset.mul_sum, Matrix.mulVec_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, ← key j]
    simp only [frob]
    ring

end GlobalTheory.LiftCoker
