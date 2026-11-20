import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapMemA
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ImageStableDegreeBounds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowerSeriesExistsUniqueDecompOverFrobeniusLikeEnStatement
open PowerSeries GlobalTheory.BK Matrix GlobalTheory.LiftCoker

noncomputable section

namespace GlobalTheory.LiftCoker

/- English proof (translation)
Rewrite using `[h, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_pow, map_X, map_expand]`. Both sides reduce to the same expression.
-/
theorem map_decomp_frob {O K : Type} [CommRing O] [NormedField K] [Algebra O K] (l : ℕ) [Fact l.Prime]
    {f : O⟦X⟧} {g : Fin l → O⟦X⟧}
    (h : f = ∑ j : Fin l, X ^ j.val * PowerSeries.expand l (Fact.out : l.Prime).ne_zero (g j)) :
    PowerSeries.map (algebraMap O K) f =
      ∑ j : Fin l, X ^ j.val * frob K l (PowerSeries.map (algebraMap O K) (g j)) := by
  rw [h, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_pow, map_X, map_expand]
  rfl

/- English proof (translation)
Introduce `O K _ _ _ _ _ l _ ι κ _ _ G β hβ`. Establish `hl2 : 2 ≤ l` using `(Fact.out : l.Prime).two_le`. Establish `decO : ∀ f : O⟦X⟧, ∃! g : Fin l → O⟦X⟧, f = ∑ j : Fin l, X ^ j.val * PowerSeries.expand l (Fact.out : l.Prime).ne_zero (g j)` using `GlobalTheory.T.powerSeries_existsUnique_decomp_over_frobeniusLike_endo l hl2 _ (fun f m => coeff_expand _ _ f)`. Establish `uniqK : ∀ f : K⟦X⟧, ∃! g : Fin l → K⟦X⟧, f = ∑ j : Fin l, X ^ j.val * frob K l (g j)` using `GlobalTheory.T.powerSeries_existsUnique_decomp_over_frobeniusLike_endo l hl2 (frob K l) (fun f m => coeff_frob l f m)`. Take `⟨b, hb, -⟩` from `decO β`.

Establish `hbK` using `map_decomp_frob (K := K) l hb`. Establish `key : ∀ j, b j ∈ colon O K G`. Introduce `j w hw`. Take `⟨M, hM, hMeq⟩` from `hβ (frobV l w) (fun i => frob_mem_A l (hw i))`. Establish `lift : ∀ k, ∃ μ : O⟦X⟧, PowerSeries.map (algebraMap O K) μ = M k` using `fun k => by`.

Take `⟨μ, hμ⟩` from `(equivA O K).surjective ⟨M k, hM k⟩`. Conclude with `⟨μ, by rw [← coe_equivA, hμ]⟩`. Use `choose μ hμ using lift`. Use `choose c hc using fun k => (decO (μ k)).exists`. Establish `hMk : ∀ k, M k = ∑ j : Fin l, X ^ j.val * frob K l (PowerSeries.map (algebraMap O K) (c k j))` using `fun k => by rw [← hμ k]; exact map_decomp_frob l (hc k)`.

Use `⟨fun k => PowerSeries.map (algebraMap O K) (c k j), fun k => map_mem_A _, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Establish `e1` using `congrFun hMeq i`. Simplify using `only [Pi.smul_apply, smul_eq_mul, frobV_apply] at e1`. Take `⟨g, -, hg⟩` from `uniqK (PowerSeries.map (algebraMap O K) β * frob K l (w i))`.

Establish `E1 : PowerSeries.map (algebraMap O K) β * frob K l (w i) = ∑ j : Fin l, X ^ j.val * frob K l (PowerSeries.map (algebraMap O K) (b j) * w i)`. Rewrite using `[hbK, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, mul_assoc]`. Establish `E2 : PowerSeries.map (algebraMap O K) β * frob K l (w i) = ∑ j : Fin l, X ^ j.val * frob K l ((G *ᵥ fun k => PowerSeries.map (algebraMap O K) (c k j)) i)`.

Rewrite using `[e1]`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.map_apply, hMk, Finset.mul_sum, map_sum, map_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Establish `h1` using `hg _ E1`. Establish `h2` using `hg _ E2`. Rewrite using `[Pi.smul_apply, smul_eq_mul]`. Conclude with `(congrFun h1 j).trans (congrFun h2 j).symm`. Rewrite using `[hb]`.

Conclude with `Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (key j))`.
-/
theorem colon_map_frob_le : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] (l : ℕ) [Fact l.Prime] (ι κ : Type) [Fintype ι] [Fintype κ] (G : Matrix κ ι K⟦X⟧),
    colon O K (G.map (frob K l)) ≤
      (colon O K G).map (PowerSeries.expand l (Fact.out : l.Prime).ne_zero) := by
  intro O K _ _ _ _ _ l _ ι κ _ _ G β hβ
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have decO : ∀ f : O⟦X⟧, ∃! g : Fin l → O⟦X⟧,
      f = ∑ j : Fin l, X ^ j.val * PowerSeries.expand l (Fact.out : l.Prime).ne_zero (g j) :=
    GlobalTheory.T.powerSeries_existsUnique_decomp_over_frobeniusLike_endo l hl2 _ (fun f m => coeff_expand _ _ f)
  have uniqK : ∀ f : K⟦X⟧, ∃! g : Fin l → K⟦X⟧, f = ∑ j : Fin l, X ^ j.val * frob K l (g j) :=
    GlobalTheory.T.powerSeries_existsUnique_decomp_over_frobeniusLike_endo l hl2 (frob K l) (fun f m => coeff_frob l f m)
  obtain ⟨b, hb, -⟩ := decO β
  have hbK := map_decomp_frob (K := K) l hb
  have key : ∀ j, b j ∈ colon O K G := by
    intro j w hw
    obtain ⟨M, hM, hMeq⟩ := hβ (frobV l w) (fun i => frob_mem_A l (hw i))
    have lift : ∀ k, ∃ μ : O⟦X⟧, PowerSeries.map (algebraMap O K) μ = M k := fun k => by
      obtain ⟨μ, hμ⟩ := (equivA O K).surjective ⟨M k, hM k⟩
      exact ⟨μ, by rw [← coe_equivA, hμ]⟩
    choose μ hμ using lift
    choose c hc using fun k => (decO (μ k)).exists
    have hMk : ∀ k, M k = ∑ j : Fin l, X ^ j.val * frob K l (PowerSeries.map (algebraMap O K) (c k j)) :=
      fun k => by rw [← hμ k]; exact map_decomp_frob l (hc k)
    refine ⟨fun k => PowerSeries.map (algebraMap O K) (c k j), fun k => map_mem_A _, ?_⟩
    funext i
    have e1 := congrFun hMeq i
    simp only [Pi.smul_apply, smul_eq_mul, frobV_apply] at e1
    obtain ⟨g, -, hg⟩ := uniqK (PowerSeries.map (algebraMap O K) β * frob K l (w i))
    have E1 : PowerSeries.map (algebraMap O K) β * frob K l (w i) =
        ∑ j : Fin l, X ^ j.val * frob K l (PowerSeries.map (algebraMap O K) (b j) * w i) := by
      rw [hbK, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, mul_assoc]
    have E2 : PowerSeries.map (algebraMap O K) β * frob K l (w i) =
        ∑ j : Fin l, X ^ j.val *
          frob K l ((G *ᵥ fun k => PowerSeries.map (algebraMap O K) (c k j)) i) := by
      rw [e1]
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, hMk, Finset.mul_sum, map_sum, map_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      ring
    have h1 := hg _ E1
    have h2 := hg _ E2
    rw [Pi.smul_apply, smul_eq_mul]
    exact (congrFun h1 j).trans (congrFun h2 j).symm

  rw [hb]
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (key j))

end GlobalTheory.LiftCoker
