import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsMoreRest
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ChartRingOverOneBlockEqChartRing
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ZpowMemSubringOfInvMem
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver)

section GenericFibre

variable {S : Type} [CommRing S] {F : Type} [Field F] [Algebra S F] {Ω : Type} [Field Ω] [Algebra S Ω]
  [Algebra F Ω] [IsScalarTower S F Ω]

/- English proof (translation)
Proceed by induction on `hb using Algebra.adjoin_induction with`. Consider the case `mem u hu => exact ⟨1, by simp, by rw [map_one, one_mul]; exact Algebra.subset_adjoin hu⟩`. Consider the case `algebraMap f`. Take `⟨a, t, ht, rfl⟩` from `IsFractionRing.div_surjective (A := S) f`. Establish `ht' : algebraMap S F t ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ht`.

Establish `hte : algebraMap S Ω t = algebraMap F Ω (algebraMap S F t)` using `IsScalarTower.algebraMap_apply S F Ω t`. Establish `htΩ : algebraMap S Ω t ≠ 0`. Rewrite using `[hte]`. Conclude with `(map_ne_zero (algebraMap F Ω)).mpr ht'`. Use `⟨t, htΩ, ?_⟩` and prove the remaining obligations.

Establish `e : algebraMap S Ω t * algebraMap F Ω (algebraMap S F a / algebraMap S F t) = algebraMap S Ω a`. Rewrite using `[map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, mul_div_cancel₀ _ htΩ]`. Rewrite using `[e]`. Conclude with `Subalgebra.algebraMap_mem _ a`. Consider the case `add u v _ _ hu hv`.

Take `⟨s, hs, hsu⟩` from `hu`. Take `⟨t, ht, htv⟩` from `hv`. Use `⟨s * t, by rw [map_mul]; exact mul_ne_zero hs ht, ?_⟩` and prove the remaining obligations. Establish `e : algebraMap S Ω (s * t) * (u + v) = algebraMap S Ω t * (algebraMap S Ω s * u) + algebraMap S Ω s * (algebraMap S Ω t * v)`. Rewrite using `[map_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `add_mem (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ t) hsu) (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ s) htv)`. Consider the case `mul u v _ _ hu hv`. Take `⟨s, hs, hsu⟩` from `hu`.

Take `⟨t, ht, htv⟩` from `hv`. Use `⟨s * t, by rw [map_mul]; exact mul_ne_zero hs ht, ?_⟩` and prove the remaining obligations. Establish `e : algebraMap S Ω (s * t) * (u * v) = (algebraMap S Ω s * u) * (algebraMap S Ω t * v)`. Rewrite using `[map_mul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Conclude with `Subalgebra.mul_mem _ hsu htv`.
-/
theorem exists_scalar_mul_mem_chartRingOver [IsDomain S] [IsFractionRing S F] {N : ℕ} (x : Fin (N + 1) → Ω)
    (c : Unit → Fin (N + 1)) {b : Ω} (hb : b ∈ chartRingOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) c) :
    ∃ s : S, algebraMap S Ω s ≠ 0 ∧ algebraMap S Ω s * b ∈ chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) c := by
  induction hb using Algebra.adjoin_induction with
  | mem u hu => exact ⟨1, by simp, by rw [map_one, one_mul]; exact Algebra.subset_adjoin hu⟩
  | algebraMap f =>
    obtain ⟨a, t, ht, rfl⟩ := IsFractionRing.div_surjective (A := S) f
    have ht' : algebraMap S F t ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ht
    have hte : algebraMap S Ω t = algebraMap F Ω (algebraMap S F t) := IsScalarTower.algebraMap_apply S F Ω t
    have htΩ : algebraMap S Ω t ≠ 0 := by
      rw [hte]
      exact (map_ne_zero (algebraMap F Ω)).mpr ht'
    refine ⟨t, htΩ, ?_⟩
    have e : algebraMap S Ω t * algebraMap F Ω (algebraMap S F a / algebraMap S F t) = algebraMap S Ω a := by
      rw [map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
        mul_div_cancel₀ _ htΩ]
    rw [e]
    exact Subalgebra.algebraMap_mem _ a
  | add u v _ _ hu hv =>
    obtain ⟨s, hs, hsu⟩ := hu
    obtain ⟨t, ht, htv⟩ := hv
    refine ⟨s * t, by rw [map_mul]; exact mul_ne_zero hs ht, ?_⟩
    have e : algebraMap S Ω (s * t) * (u + v) =
        algebraMap S Ω t * (algebraMap S Ω s * u) + algebraMap S Ω s * (algebraMap S Ω t * v) := by
      rw [map_mul]; ring
    rw [e]
    exact add_mem (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ t) hsu)
      (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ s) htv)
  | mul u v _ _ hu hv =>
    obtain ⟨s, hs, hsu⟩ := hu
    obtain ⟨t, ht, htv⟩ := hv
    refine ⟨s * t, by rw [map_mul]; exact mul_ne_zero hs ht, ?_⟩
    have e : algebraMap S Ω (s * t) * (u * v) = (algebraMap S Ω s * u) * (algebraMap S Ω t * v) := by
      rw [map_mul]; ring
    rw [e]
    exact Subalgebra.mul_mem _ hsu htv

end GenericFibre

/- English proof (translation)
Introduce `S _ _ F _ _ Ω _ _ _ _ _ N N' x x' _ _ _ hsame i hi b hb`. Use `set C : Subalgebra F Ω := chartRingOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) (fun _ => i) with hCdef`. Establish `hbC : b ∈ C`. Use `mem_of_forall_mem_locIn C fun m hm => ?_` and prove the remaining obligations. Use `hm.isPrime` as an intermediate fact.

Establish `hCm : ∀ u ∈ C, u ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn C m` using `fun u hu => (mem_locIn (A := C) (p := m)).mpr ⟨⟨u, hu⟩, 1, one_not_mem_of_prime hm.isPrime, by simp⟩`. Establish `hpt : IndefiniteRowSideFullHecke.Kleiman2.locIn C m ∈ IndefiniteRowSideFullHecke.Kleiman2.modelPts F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x)` using `⟨fun _ => i, fun _ => hi, m, hm.isPrime, rfl⟩`. Rewrite `hpt` using `[← hsame]`. Take `⟨c', hc', p', hp', hz⟩` from `hpt`. Use `hp'` as an intermediate fact.

Establish `hj : x' (c' ()) ≠ 0` using `hc' ()`. Establish `hbP` using `mem_pairRing_of_mem_domRing (S := S) hj hi hb`. Use `clear hb`. Proceed by induction on `hbP using Algebra.adjoin_induction with`. Consider the case `mem u hu`.

Break down `hu with ⟨a, rfl⟩ | ⟨a, rfl⟩` into its components or cases. Rewrite using `[hz]`. Establish `ha : x' a / x' (c' ()) ∈ chartRingOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') c'` using `Algebra.subset_adjoin ⟨⟨(), a⟩, rfl⟩`. Conclude with `(mem_locIn (A := chartRingOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') c') (p := p')).mpr ⟨⟨_, ha⟩, 1, one_not_mem_of_prime hp', by simp⟩`. Conclude with `hCm _ (Algebra.subset_adjoin ⟨⟨(), a⟩, rfl⟩)`.

Consider the case `algebraMap r`. Rewrite using `[IsScalarTower.algebraMap_apply S F Ω]`. Conclude with `hCm _ (Subalgebra.algebraMap_mem _ _)`. Consider the case `add u v _ _ hu hv => exact add_mem hu hv`. Consider the case `mul u v _ _ hu hv => exact mul_mem hu hv`.

Take `⟨s, hs, hsb⟩` from `exists_scalar_mul_mem_chartRingOver (S := S) x (fun _ => i) hbC`. Rewrite `hsb` using `[chartRingOver_oneBlock_eq_chartRing x (fun _ => i) hi]`. Conclude with `⟨s, hs, hsb⟩`.
-/
theorem GenericFibreScalars.full : GenericFibreScalars.Statement := by
  intro S _ _ F _ _ Ω _ _ _ _ _ N N' x x' _ _ _ hsame i hi b hb
  set C : Subalgebra F Ω := chartRingOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) (fun _ => i) with hCdef
  have hbC : b ∈ C := by
    refine mem_of_forall_mem_locIn C fun m hm => ?_
    have := hm.isPrime
    have hCm : ∀ u ∈ C, u ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn C m := fun u hu =>
      (mem_locIn (A := C) (p := m)).mpr ⟨⟨u, hu⟩, 1, one_not_mem_of_prime hm.isPrime, by simp⟩
    have hpt : IndefiniteRowSideFullHecke.Kleiman2.locIn C m ∈ IndefiniteRowSideFullHecke.Kleiman2.modelPts F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) :=
      ⟨fun _ => i, fun _ => hi, m, hm.isPrime, rfl⟩
    rw [← hsame] at hpt
    obtain ⟨c', hc', p', hp', hz⟩ := hpt
    have := hp'
    have hj : x' (c' ()) ≠ 0 := hc' ()
    have hbP := mem_pairRing_of_mem_domRing (S := S) hj hi hb
    clear hb
    induction hbP using Algebra.adjoin_induction with
    | mem u hu =>
      rcases hu with ⟨a, rfl⟩ | ⟨a, rfl⟩
      · rw [hz]
        have ha : x' a / x' (c' ()) ∈ chartRingOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') c' :=
          Algebra.subset_adjoin ⟨⟨(), a⟩, rfl⟩
        exact (mem_locIn (A := chartRingOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') c') (p := p')).mpr
          ⟨⟨_, ha⟩, 1, one_not_mem_of_prime hp', by simp⟩
      · exact hCm _ (Algebra.subset_adjoin ⟨⟨(), a⟩, rfl⟩)
    | algebraMap r =>
      rw [IsScalarTower.algebraMap_apply S F Ω]
      exact hCm _ (Subalgebra.algebraMap_mem _ _)
    | add u v _ _ hu hv => exact add_mem hu hv
    | mul u v _ _ hu hv => exact mul_mem hu hv
  obtain ⟨s, hs, hsb⟩ := exists_scalar_mul_mem_chartRingOver (S := S) x (fun _ => i) hbC
  rw [chartRingOver_oneBlock_eq_chartRing x (fun _ => i) hi] at hsb
  exact ⟨s, hs, hsb⟩

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
