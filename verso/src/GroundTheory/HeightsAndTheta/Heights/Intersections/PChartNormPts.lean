import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StChartNormPts
import GroundTheory.HeightsAndTheta.Heights.Intersections.PChartNormPtsA
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

/- English proof (translation)
Introduce `K _ ι _ K' _ ι' _ κ v P' G j hv hP' hj z' hw hz1`. Establish `hcast : ∀ p : MRing ι', eval z' (map (Int.castRingHom ℂ) p) = aeval z' p` using `fun p => by`. Rewrite using `[eval_map, aeval_def, algebraMap_int_eq]`. Establish `hcoef : (eval₂Hom (Int.castRingHom ℂ) fun p => z' (v p)) = (aeval (z' ∘ v) : MRing ι →ₐ[ℤ] ℂ).toRingHom`. Use extensionality with `c`.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish `hφ : (algebraMap G.Φ G.Φ').comp (aeval G.x : MRing ι →ₐ[ℤ] G.Φ).toRingHom = (aeval (G.x' ∘ v) : MRing ι →ₐ[ℤ] G.Φ').toRingHom`. Use extensionality with `c`. Simplify using the standard rewrite rules.

Simplify using `[G.compat]`. Rewrite using `[hφ, hcoef]`. Prove the components needed by the constructor for the conclusion. Introduce `hz F hF`. Establish `hH : ChartNormPts.homogenise v (fun q : Σ k : FibreBlock κ, ι' k.1 => (⟨q.1.1, q.2⟩ : Σ k', ι' k')) (fun q => ⟨q.1.1, j q.1⟩) F ∈ P'`.

Rewrite using `[← G.genericFibre_ker_target, RingHom.mem_ker]`. Use `show aeval G.x' _ = 0`. Rewrite using `[ChartNormPts.aeval_homogenise_div v _ _ F G.x' fun q => hj q.1, hF, mul_zero]`. Establish `h0` using `hz.2 _ hH`. Rewrite `h0` using `[hcast, ChartNormPts.aeval_homogenise_one v _ _ F z' fun q => hz1 q.1]`. Then use the resulting hypothesis.

Introduce `hF`. Use `⟨fun k' => ?_, fun f hf => ?_⟩` and prove the remaining obligations. Distinguish the cases in `h : k' ∈ Set.range κ`. Take `⟨k, rfl⟩` from `h`. Take `⟨i, hi⟩` from `hw.1 k`.

Use `replace hi : z' (v ⟨k, i⟩) ≠ 0 := hi`. Use `revert hi`. Generalize the expression as in `hq : v ⟨k, i⟩ = q`. Take `⟨k₀, i₀⟩` from `q`. Introduce `hi`.

Establish `e : k₀ = κ k` using `by rw [← hv.2.2.1 ⟨k, i⟩, hq]`. Substitute `e` using the available equality. Conclude with `⟨i₀, hi⟩`. Conclude with `⟨j ⟨k', h⟩, by rw [hz1 ⟨k', h⟩]; exact one_ne_zero⟩`. Take `⟨S, hS, rfl⟩` from `hP'`.

It suffices to establish `hle : Ideal.span S ≤ RingHom.ker (aeval z' : MRing ι' →ₐ[ℤ] ℂ) by`. Rewrite using `[hcast]`. Conclude with `hle hf`. Rewrite using `[Ideal.span_le]`. Introduce `g hg`.

Take `⟨a, ha⟩` from `hS g hg`. Set `σ : (Σ k', ι' k') → MvPolynomial (Σ k : FibreBlock κ, ι' k.1) (MRing ι)` to `fun q' => if h : q'.1 ∈ Set.range κ then C (X (hv.2.2.2 q' h).choose) else X ⟨⟨q'.1, h⟩, q'.2⟩`. Establish `hcomp : ∀ {R : Type} [CommRing R] (ψ : MvPolynomial (Σ k : FibreBlock κ, ι' k.1) (MRing ι) →+* R), ψ (aeval σ g) = aeval (fun q' => ψ (σ q')) g` using `fun ψ => comp_aeval_apply (f := σ) ψ.toIntAlgHom g`. Establish `h1` using `hF (aeval σ g)`. Rewrite `h1` using `[← coe_eval₂Hom, ← coe_eval₂Hom, hcomp, hcomp]`.

Set `c : K' → G.Φ'` to `fun k' => if h : k' ∈ Set.range κ then 1 else (G.x' ⟨k', j ⟨k', h⟩⟩)⁻¹`. Establish `hx : (fun q' => eval₂Hom (aeval (G.x' ∘ v) : MRing ι →ₐ[ℤ] G.Φ').toRingHom (fun q => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, j q.1⟩) (σ q')) = fun q' => c q'.1 * G.x' q'`. Use function extensionality and compare the values at `q'`. Distinguish the cases in `h : q'.1 ∈ Set.range κ`. Simplify using `only [σ, c, dif_pos h, coe_eval₂Hom, eval₂_C, one_mul]`.

Simplify using `[(hv.2.2.2 q' h).choose_spec]`. Simplify using `only [σ, c, dif_neg h, coe_eval₂Hom, eval₂_X]`. Rewrite using `[div_eq_inv_mul]`. Establish `hz : (fun q' => eval₂Hom (aeval (z' ∘ v) : MRing ι →ₐ[ℤ] ℂ).toRingHom (fun q => z' ⟨q.1.1, q.2⟩) (σ q')) = z'`. Use function extensionality and compare the values at `q'`.

Distinguish the cases in `h : q'.1 ∈ Set.range κ`. Simplify using `only [σ, dif_pos h, coe_eval₂Hom, eval₂_C]`. Simplify using `[(hv.2.2.2 q' h).choose_spec]`. Simplify using `only [σ, dif_neg h, coe_eval₂Hom, eval₂_X]`. Rewrite `h1` using `[hx, hz, ChartNormPts.aeval_smul_homog g a ha]`.

Establish `hg0 : aeval G.x' g = 0`. Establish `: g ∈ RingHom.ker (aeval G.x' : MRing ι' →ₐ[ℤ] G.Φ')`. Rewrite using `[G.genericFibre_ker_target]`. Conclude with `Ideal.subset_span hg`. Conclude with `this`.

Conclude with `h1 (by rw [hg0, mul_zero])`.
-/
theorem ChartNormPts.proof : ChartNormPts.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' G j hv hP' hj z' hw hz1
  classical
  have hcast : ∀ p : MRing ι', eval z' (map (Int.castRingHom ℂ) p) = aeval z' p := fun p => by
    rw [eval_map, aeval_def, algebraMap_int_eq]
  have hcoef : (eval₂Hom (Int.castRingHom ℂ) fun p => z' (v p)) =
      (aeval (z' ∘ v) : MRing ι →ₐ[ℤ] ℂ).toRingHom := by
    ext c
    · simp
    · simp
  have hφ : (algebraMap G.Φ G.Φ').comp (aeval G.x : MRing ι →ₐ[ℤ] G.Φ).toRingHom =
      (aeval (G.x' ∘ v) : MRing ι →ₐ[ℤ] G.Φ').toRingHom := by
    ext c
    · simp
    · simp [G.compat]
  rw [hφ, hcoef]
  constructor
  · intro hz F hF
    have hH : ChartNormPts.homogenise v (fun q : Σ k : FibreBlock κ, ι' k.1 => (⟨q.1.1, q.2⟩ : Σ k', ι' k'))
        (fun q => ⟨q.1.1, j q.1⟩) F ∈ P' := by
      rw [← G.genericFibre_ker_target, RingHom.mem_ker]
      show aeval G.x' _ = 0
      rw [ChartNormPts.aeval_homogenise_div v _ _ F G.x' fun q => hj q.1, hF, mul_zero]
    have h0 := hz.2 _ hH
    rwa [hcast, ChartNormPts.aeval_homogenise_one v _ _ F z' fun q => hz1 q.1] at h0
  · intro hF
    refine ⟨fun k' => ?_, fun f hf => ?_⟩
    · by_cases h : k' ∈ Set.range κ
      · obtain ⟨k, rfl⟩ := h
        obtain ⟨i, hi⟩ := hw.1 k
        replace hi : z' (v ⟨k, i⟩) ≠ 0 := hi
        revert hi
        generalize hq : v ⟨k, i⟩ = q
        obtain ⟨k₀, i₀⟩ := q
        intro hi
        have e : k₀ = κ k := by rw [← hv.2.2.1 ⟨k, i⟩, hq]
        subst e
        exact ⟨i₀, hi⟩
      · exact ⟨j ⟨k', h⟩, by rw [hz1 ⟨k', h⟩]; exact one_ne_zero⟩
    obtain ⟨S, hS, rfl⟩ := hP'
    suffices hle : Ideal.span S ≤ RingHom.ker (aeval z' : MRing ι' →ₐ[ℤ] ℂ) by
      rw [hcast]; exact hle hf
    rw [Ideal.span_le]
    intro g hg
    obtain ⟨a, ha⟩ := hS g hg
    let σ : (Σ k', ι' k') → MvPolynomial (Σ k : FibreBlock κ, ι' k.1) (MRing ι) := fun q' =>
      if h : q'.1 ∈ Set.range κ then C (X (hv.2.2.2 q' h).choose) else X ⟨⟨q'.1, h⟩, q'.2⟩
    have hcomp : ∀ {R : Type} [CommRing R] (ψ : MvPolynomial (Σ k : FibreBlock κ, ι' k.1) (MRing ι) →+* R),
        ψ (aeval σ g) = aeval (fun q' => ψ (σ q')) g := fun ψ =>
      comp_aeval_apply (f := σ) ψ.toIntAlgHom g
    have h1 := hF (aeval σ g)
    rw [← coe_eval₂Hom, ← coe_eval₂Hom, hcomp, hcomp] at h1
    let c : K' → G.Φ' := fun k' => if h : k' ∈ Set.range κ then 1 else (G.x' ⟨k', j ⟨k', h⟩⟩)⁻¹
    have hx : (fun q' => eval₂Hom (aeval (G.x' ∘ v) : MRing ι →ₐ[ℤ] G.Φ').toRingHom
        (fun q => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, j q.1⟩) (σ q')) = fun q' => c q'.1 * G.x' q' := by
      funext q'
      by_cases h : q'.1 ∈ Set.range κ
      · simp only [σ, c, dif_pos h, coe_eval₂Hom, eval₂_C, one_mul]
        simp [(hv.2.2.2 q' h).choose_spec]
      · simp only [σ, c, dif_neg h, coe_eval₂Hom, eval₂_X]
        rw [div_eq_inv_mul]
    have hz : (fun q' => eval₂Hom (aeval (z' ∘ v) : MRing ι →ₐ[ℤ] ℂ).toRingHom
        (fun q => z' ⟨q.1.1, q.2⟩) (σ q')) = z' := by
      funext q'
      by_cases h : q'.1 ∈ Set.range κ
      · simp only [σ, dif_pos h, coe_eval₂Hom, eval₂_C]
        simp [(hv.2.2.2 q' h).choose_spec]
      · simp only [σ, dif_neg h, coe_eval₂Hom, eval₂_X]
    rw [hx, hz, ChartNormPts.aeval_smul_homog g a ha] at h1
    have hg0 : aeval G.x' g = 0 := by
      have : g ∈ RingHom.ker (aeval G.x' : MRing ι' →ₐ[ℤ] G.Φ') := by
        rw [G.genericFibre_ker_target]; exact Ideal.subset_span hg
      exact this
    exact h1 (by rw [hg0, mul_zero])

end GroundTheory.Heights₂.Heights.Inter
