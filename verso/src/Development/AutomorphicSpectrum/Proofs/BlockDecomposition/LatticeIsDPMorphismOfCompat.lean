import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit

open DividedPowers CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LatDP

/- English proof (translation)
Establish `h1` using `(Lat.γB f ξ).factorial_mul_dpow_eq_pow (n := n) hy`. Establish `h2` using `(Lat.γB f' ξ').factorial_mul_dpow_eq_pow (n := n) hy'`. Establish `hu : IsUnit (n.factorial : B')`. Use `(IsUnit.mk0 (n.factorial : ℚ) (by exact_mod_cast n.factorial_ne_zero)).map (algebraMap ℚ B')` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis.

Apply `hu.mul_left_cancel` to reduce the goal to its premises. Rewrite using `[h2, ← map_pow, ← h1, map_mul, map_natCast]`.
-/
theorem γB_map {W B W' B' : Type} [CommRing W] [CommRing B] [Algebra ℚ B] [CommRing W'] [CommRing B']
    [Algebra ℚ B'] (f : W →+* B) (ξ : W) (f' : W' →+* B') (ξ' : W') (g : B →+* B') {y : B}
    (hy : y ∈ Lat.IB f ξ) (hy' : g y ∈ Lat.IB f' ξ') (n : ℕ) :
    g ((Lat.γB f ξ).dpow n y) = (Lat.γB f' ξ').dpow n (g y) := by
  have h1 := (Lat.γB f ξ).factorial_mul_dpow_eq_pow (n := n) hy
  have h2 := (Lat.γB f' ξ').factorial_mul_dpow_eq_pow (n := n) hy'
  have hu : IsUnit (n.factorial : B') := by
    have := (IsUnit.mk0 (n.factorial : ℚ) (by exact_mod_cast n.factorial_ne_zero)).map (algebraMap ℚ B')
    rwa [map_natCast] at this
  apply hu.mul_left_cancel
  rw [h2, ← map_pow, ← h1, map_mul, map_natCast]

/- English proof (translation)
Establish `hB : ∀ x ∈ Lat.I f ξ l M, g (Lat.ι f ξ l M x) ∈ Lat.IB f' ξ'`. Introduce `x hx`. Establish `hx' : Lat.ι f ξ l M x ∈ Lat.IB f ξ` using `hx`. Simplify using `only [Lat.IB, Ideal.mem_span_singleton] at hx' ⊢`. Take `⟨c, hc0⟩` from `hx'`.

Use `⟨f' u * g c, ?_⟩` and prove the remaining obligations. Rewrite using `[hc0, map_mul, hg, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hI : ∀ x ∈ Lat.I f ξ l M, Lat.map f ξ f' ξ' l M g hmap x ∈ Lat.I f' ξ' l M`. Introduce `x hx`.

Use `show Lat.ι f' ξ' l M (Lat.map f ξ f' ξ' l M g hmap x) ∈ Lat.IB f' ξ'`. Rewrite using `[Lat.ι_map]`. Conclude with `hB x hx`. Use `⟨Ideal.map_le_iff_le_comap.2 fun x hx => hI x hx, fun {n} x hx => ?_⟩` and prove the remaining obligations. Apply `Lat.ι_injective f' ξ' l M` to reduce the goal to its premises.

Rewrite using `[Lat.ι_γ f' ξ' l M hc' (hI x hx)]`. Simplify using `only [Lat.ι_map]`. Rewrite using `[Lat.ι_γ f ξ l M hc hx]`. Establish `hx' : Lat.ι f ξ l M x ∈ Lat.IB f ξ` using `hx`. Conclude with `(γB_map f ξ f' ξ' g hx' (hB x hx) n).symm`.
-/
theorem isDPMorphism_map {W B W' B' : Type} [CommRing W] [CommRing B] [Algebra ℚ B] [CommRing W']
    [CommRing B'] [Algebra ℚ B'] (f : W →+* B) (ξ : W) (f' : W' →+* B') (ξ' : W') (l M : ℕ)
    (g : B →+* B') (hmap : ∀ x ∈ Lat.sub f ξ l M, g x ∈ Lat.sub f' ξ' l M) (u : W')
    (hg : g (f ξ) = f' (u * ξ')) (hc : Lat.DPClosed (Lat.ι f ξ l M) (Lat.γB f ξ))
    (hc' : Lat.DPClosed (Lat.ι f' ξ' l M) (Lat.γB f' ξ')) :
    IsDPMorphism (Lat.γ f ξ l M hc) (Lat.γ f' ξ' l M hc') (Lat.map f ξ f' ξ' l M g hmap) := by
  have hB : ∀ x ∈ Lat.I f ξ l M, g (Lat.ι f ξ l M x) ∈ Lat.IB f' ξ' := by
    intro x hx
    have hx' : Lat.ι f ξ l M x ∈ Lat.IB f ξ := hx
    simp only [Lat.IB, Ideal.mem_span_singleton] at hx' ⊢
    obtain ⟨c, hc0⟩ := hx'
    refine ⟨f' u * g c, ?_⟩
    rw [hc0, map_mul, hg, map_mul]; ring
  have hI : ∀ x ∈ Lat.I f ξ l M, Lat.map f ξ f' ξ' l M g hmap x ∈ Lat.I f' ξ' l M := by
    intro x hx
    show Lat.ι f' ξ' l M (Lat.map f ξ f' ξ' l M g hmap x) ∈ Lat.IB f' ξ'
    rw [Lat.ι_map]; exact hB x hx
  refine ⟨Ideal.map_le_iff_le_comap.2 fun x hx => hI x hx, fun {n} x hx => ?_⟩
  apply Lat.ι_injective f' ξ' l M
  rw [Lat.ι_γ f' ξ' l M hc' (hI x hx)]
  simp only [Lat.ι_map]
  rw [Lat.ι_γ f ξ l M hc hx]
  have hx' : Lat.ι f ξ l M x ∈ Lat.IB f ξ := hx
  exact (γB_map f ξ f' ξ' g hx' (hB x hx) n).symm

end GlobalTheory.CompanionTheory.LatDP
