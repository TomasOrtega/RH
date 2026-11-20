import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsProjFrameGenPtRel
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PProjFrameFibrePt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

open ProjFrameFibrePt in

/- English proof (translation)
Introduce `D Ω _ _ κ _ x e _ hF G`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `n hn`. Establish `h1 : (C (n : ℤ) : MRing (Sum.elim (GlobalTheory κ) (GlobalTheory (Fin (D + 1))))) ∈ graphP x e`. Rewrite using `[graphP, ← G.genericFibre_ker_target, RingHom.mem_ker, aeval_C, eq_intCast, Int.cast_natCast]`.

Conclude with `hn`. Rewrite `h1` using `[graphP, graphIdeal, RingHom.mem_ker, graphMap, eval₂Hom_C, eq_intCast, Int.cast_natCast, ← map_natCast (C : (MRing (GlobalTheory κ) ⧸ coordIdeal ℤ x) →+* MvPolynomial Unit _), C_eq_zero, ← map_natCast (Ideal.Quotient.mk (coordIdeal ℤ x)), Ideal.Quotient.eq_zero_iff_mem, coordIde …`. Conclude with `h1` after adjusting the coercions. Establish `hker : ∀ h : MRing (GlobalTheory κ), aeval (fun p : Ix κ => G.x' ⟨Sum.inl p.1, p.2⟩) h = 0 ↔ h ∈ coordIdeal ℤ x`. Introduce `h`.

Prove the components needed by the constructor for the conclusion. Introduce `h0`. Establish `h2 : rename (fun p : Ix κ => aV D p.2) h ∈ graphP x e`. Rewrite using `[graphP, ← G.genericFibre_ker_target, RingHom.mem_ker, aeval_rename]`. Conclude with `h0`.

Rewrite `h2` using `[graphP, graphIdeal, RingHom.mem_ker, graphMap_rename_inl, C_eq_zero, Ideal.Quotient.eq_zero_iff_mem]`. Then use the resulting hypothesis. Introduce `hh`. Conclude with `aeval_inl_eq_zero G hh`. Use extensionality with `f`. Establish `hu : f ∈ coordIdeal ℤ (fun p : Ix κ => G.x' ⟨Sum.inl p.1, p.2⟩) ↔ ∀ d, homogeneousComponent d f ∈ coordIdeal ℤ x`.

Rewrite using `[coordIdeal, RingHom.mem_ker, Polynomial.ext_iff]`. Simplify using `only [coeff_coneMap, Polynomial.coeff_zero, hker]`. Rewrite using `[hu]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Rewrite using `[← sum_homogeneousComponent f]`. Conclude with `Ideal.sum_mem _ fun d _ => h d`. Introduce `h d`. Conclude with `coordIdeal_isHomogIdeal ℤ x f h d`. Introduce `k`.

Establish `h` using `x'_frame_mul G (e := e) k`. Express the relevant statement in the definitionally equal form `G.x' (bV κ k) * G.x' (aV D (e 0).2) = G.x' (bV κ 0) * G.x' (aV D (e k).2)`. Take the linear combination `-h`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `y hy`.

Rewrite `hy` using `[RingHom.mem_fieldRange]`. Take `⟨c, rfl⟩` from `hy`. Take `⟨f, g, _, rfl⟩` from `G.gen c`. Establish `key : ∀ h : MRing (GlobalTheory (Fin (D + 1))), algebraMap G.Φ G.Φ' (aeval G.x h) ∈ Subfield.closure (Set.range fun k : Fin (D + 1) => G.x' ⟨Sum.inr (), k⟩)`. Introduce `h`.

Proceed by induction on `h using MvPolynomial.induction_on with`. Consider the case `C a`. Rewrite using `[aeval_C, eq_intCast, map_intCast]`. Conclude with `intCast_mem _ a`. Consider the case `add p q hp hq`.

Rewrite using `[map_add, map_add]`. Conclude with `add_mem hp hq`. Consider the case `mul_X p i hp`. Rewrite using `[map_mul, map_mul, aeval_X]`. Conclude with `mul_mem hp (Subfield.subset_closure ⟨i.2, G.compat i⟩)`.

Rewrite using `[map_div₀]`. Conclude with `div_mem (key f) (key g)`. Rewrite using `[Subfield.closure_le]`. Introduce and unpack `_ ⟨k, rfl⟩`. Conclude with `⟨G.x ⟨(), k⟩, (G.compat ⟨(), k⟩).symm⟩`.
-/
theorem ProjFrameGenPtRel.proof : ProjFrameGenPtRel.Statement := by
  intro D Ω _ _ κ _ x e _ hF G
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    intro n hn
    have h1 : (C (n : ℤ) : MRing (Sum.elim (GlobalTheory κ) (GlobalTheory (Fin (D + 1))))) ∈ graphP x e := by
      rw [graphP, ← G.genericFibre_ker_target, RingHom.mem_ker, aeval_C, eq_intCast, Int.cast_natCast]
      exact hn
    rw [graphP, graphIdeal, RingHom.mem_ker, graphMap, eval₂Hom_C, eq_intCast, Int.cast_natCast,
      ← map_natCast (C : (MRing (GlobalTheory κ) ⧸ coordIdeal ℤ x) →+* MvPolynomial Unit _), C_eq_zero,
      ← map_natCast (Ideal.Quotient.mk (coordIdeal ℤ x)), Ideal.Quotient.eq_zero_iff_mem, coordIdeal,
      RingHom.mem_ker, map_natCast, ← map_natCast (Polynomial.C : Ω →+* Polynomial Ω), Polynomial.C_eq_zero] at h1
    exact_mod_cast h1
  ·
    have hker : ∀ h : MRing (GlobalTheory κ),
        aeval (fun p : Ix κ => G.x' ⟨Sum.inl p.1, p.2⟩) h = 0 ↔ h ∈ coordIdeal ℤ x := by
      intro h
      constructor
      · intro h0
        have h2 : rename (fun p : Ix κ => aV D p.2) h ∈ graphP x e := by
          rw [graphP, ← G.genericFibre_ker_target, RingHom.mem_ker, aeval_rename]
          exact h0
        rwa [graphP, graphIdeal, RingHom.mem_ker, graphMap_rename_inl, C_eq_zero,
          Ideal.Quotient.eq_zero_iff_mem] at h2
      · intro hh
        exact aeval_inl_eq_zero G hh
    ext f
    have hu : f ∈ coordIdeal ℤ (fun p : Ix κ => G.x' ⟨Sum.inl p.1, p.2⟩) ↔
        ∀ d, homogeneousComponent d f ∈ coordIdeal ℤ x := by
      rw [coordIdeal, RingHom.mem_ker, Polynomial.ext_iff]
      simp only [coeff_coneMap, Polynomial.coeff_zero, hker]
    rw [hu]
    constructor
    · intro h
      rw [← sum_homogeneousComponent f]
      exact Ideal.sum_mem _ fun d _ => h d
    · intro h d
      exact coordIdeal_isHomogIdeal ℤ x f h d
  ·
    intro k
    have h := x'_frame_mul G (e := e) k
    change G.x' (bV κ k) * G.x' (aV D (e 0).2) = G.x' (bV κ 0) * G.x' (aV D (e k).2)
    linear_combination -h
  ·
    apply le_antisymm
    · intro y hy
      rw [RingHom.mem_fieldRange] at hy
      obtain ⟨c, rfl⟩ := hy
      obtain ⟨f, g, _, rfl⟩ := G.gen c
      have key : ∀ h : MRing (GlobalTheory (Fin (D + 1))), algebraMap G.Φ G.Φ' (aeval G.x h) ∈
          Subfield.closure (Set.range fun k : Fin (D + 1) => G.x' ⟨Sum.inr (), k⟩) := by
        intro h
        induction h using MvPolynomial.induction_on with
        | C a =>
          rw [aeval_C, eq_intCast, map_intCast]
          exact intCast_mem _ a
        | add p q hp hq =>
          rw [map_add, map_add]
          exact add_mem hp hq
        | mul_X p i hp =>
          rw [map_mul, map_mul, aeval_X]
          exact mul_mem hp (Subfield.subset_closure ⟨i.2, G.compat i⟩)
      rw [map_div₀]
      exact div_mem (key f) (key g)
    · rw [Subfield.closure_le]
      rintro _ ⟨k, rfl⟩
      exact ⟨G.x ⟨(), k⟩, (G.compat ⟨(), k⟩).symm⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
