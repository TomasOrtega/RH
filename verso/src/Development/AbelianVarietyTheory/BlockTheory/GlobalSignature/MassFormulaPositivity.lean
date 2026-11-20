import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
import Formalism.HermitianLattices.HermitianLatticesProofs.MassBasic

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.MassFormulaPositivity

open NumberField Formalism.BasicNotions

def MassPlane : Prop :=
  ∀ (D : D7), letI := D.host.cmStar
    ∀ W : HSpace D.host.E, W.rank = 2 → W.SigOK → (∀ τ : D.host.E →+* ℂ, W.sig τ = (2, 0)) →
      Formalism.HermitianLatticesTheory.mass W.hT W.L0 = Formalism.MainNotions.StandardLattice.massI D 2

open scoped ComplexOrder in

/- English proof (translation)
Take `⟨e, P, hP⟩` from `h`. Establish `hJ : Formalism.UG.Jpq p 0 = 1`. Use extensionality with `i j`. Break down `i with i | i` into its components or cases. Break down `j with j | j` into its components or cases.

Simplify using `[Formalism.UG.Jpq, Matrix.one_apply]`. Conclude with `j.elim0`. Conclude with `i.elim0`. Establish `hc : Formalism.UG.cT (starRingEnd ℂ) (P : Matrix (Fin p ⊕ Fin 0) (Fin p ⊕ Fin 0) ℂ) = star (P : Matrix (Fin p ⊕ Fin 0) (Fin p ⊕ Fin 0) ℂ)`. Use extensionality with `i j`.

Both sides reduce to the same expression. Rewrite `hP` using `[hJ, hc]`. Establish `h1 : (J.reindex e e).PosDef`. Rewrite using `[← Matrix.IsUnit.posDef_star_left_conjugate_iff (Units.isUnit P), hP]`. Conclude with `Matrix.PosDef.one`.

Establish `h2` using `h1.submatrix (e := e) e.injective`. Simplify using `using h2`.
-/
theorem posDef_of_hasSignature {n : Type} [Fintype n] [DecidableEq n] {J : Matrix n n ℂ} {p : ℕ}
    (h : Formalism.UG.HasSignature J p 0) : J.PosDef := by
  obtain ⟨e, P, hP⟩ := h
  have hJ : Formalism.UG.Jpq p 0 = 1 := by
    ext i j
    rcases i with i | i
    · rcases j with j | j
      · simp [Formalism.UG.Jpq, Matrix.one_apply]
      · exact j.elim0
    · exact i.elim0
  have hc : Formalism.UG.cT (starRingEnd ℂ) (P : Matrix (Fin p ⊕ Fin 0) (Fin p ⊕ Fin 0) ℂ) =
      star (P : Matrix (Fin p ⊕ Fin 0) (Fin p ⊕ Fin 0) ℂ) := by
    ext i j; rfl
  rw [hJ, hc] at hP
  have h1 : (J.reindex e e).PosDef := by
    rw [← Matrix.IsUnit.posDef_star_left_conjugate_iff (Units.isUnit P), hP]
    exact Matrix.PosDef.one
  have h2 := h1.submatrix (e := e) e.injective
  simpa using h2

/- English proof (translation)
Establish `hloc : ∀ τ : E →+* ℂ, 0 < (τ (W.hT x x)).re`. Introduce `τ`. Establish `h0` using `hs τ`. Rewrite `h0` using `[hp τ]`. Establish `hpd` using `posDef_of_hasSignature h0`.

Establish `hv : (fun i => τ (W.frame.repr x i)) ≠ 0`. Introduce `h`. Apply `hx` to reduce the goal to its premises. Apply `W.frame.repr.injective` to reduce the goal to its premises. Use extensionality with `i`.

Simplify using `using congrFun h i`. Establish `h1` using `hpd.re_dotProduct_pos hv`. Establish `h2 : τ (W.hT x x) = star (fun i => τ (W.frame.repr x i)) ⬝ᵥ (W.gram.map τ).mulVec (fun i => τ (W.frame.repr x i))` using `by conv_lhs => rw [← W.frame.sum_repr x]`. Simplify using `only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, map_mul, RingHom.id_apply, starRingEnd_apply, hst, dotProduct, Matrix.mulVec, Matrix.map_apply, HSpace.gram, Pi.star_apply, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h2]`. Conclude with `h1`. Establish `ht` using `trace_eq_sum_embeddings ℂ (K := ℚ) (L := E) (x := W.hT x x)`.

Establish `hre` using `congrArg Complex.re ht`. Rewrite `hre` using `[Complex.re_sum]`. Establish `hpos : 0 < ∑ σ : E →ₐ[ℚ] ℂ, (σ (W.hT x x)).re` using `Finset.sum_pos (fun σ _ => hloc (σ : E →+* ℂ)) ⟨IsAlgClosed.lift, Finset.mem_univ _⟩`. Rewrite `hpos` using `[← hre]`. Simplify using `using hpos`.
-/
theorem trace_pos {E : Type} [Field E] [NumberField E] [StarRing E]
    (hst : ∀ (φ : E →+* ℂ) (a : E), φ (star a) = starRingEnd ℂ (φ a))
    (W : HSpace E) (hs : W.SigOK) {p : ℕ} (hp : ∀ τ : E →+* ℂ, W.sig τ = (p, 0))
    (x : W.V) (hx : x ≠ 0) : 0 < Algebra.trace ℚ E (W.hT x x) := by
  classical
  have hloc : ∀ τ : E →+* ℂ, 0 < (τ (W.hT x x)).re := by
    intro τ
    have h0 := hs τ
    rw [hp τ] at h0
    have hpd := posDef_of_hasSignature h0
    have hv : (fun i => τ (W.frame.repr x i)) ≠ 0 := by
      intro h
      apply hx
      apply W.frame.repr.injective
      ext i
      simpa using congrFun h i
    have h1 := hpd.re_dotProduct_pos hv
    have h2 : τ (W.hT x x) = star (fun i => τ (W.frame.repr x i)) ⬝ᵥ
        (W.gram.map τ).mulVec (fun i => τ (W.frame.repr x i)) := by
      conv_lhs => rw [← W.frame.sum_repr x]
      simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
        smul_eq_mul, map_mul, RingHom.id_apply, starRingEnd_apply, hst, dotProduct, Matrix.mulVec,
        Matrix.map_apply, HSpace.gram, Pi.star_apply, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [h2]
    exact h1
  have ht := trace_eq_sum_embeddings ℂ (K := ℚ) (L := E) (x := W.hT x x)
  have hre := congrArg Complex.re ht
  rw [Complex.re_sum] at hre
  have hpos : 0 < ∑ σ : E →ₐ[ℚ] ℂ, (σ (W.hT x x)).re :=
    Finset.sum_pos (fun σ _ => hloc (σ : E →+* ℂ)) ⟨IsAlgClosed.lift, Finset.mem_univ _⟩
  rw [← hre] at hpos
  simpa using hpos

/- English proof (translation)
Use `letI := D.host.cmStar`. Introduce `W hs hp`. Establish `hpos` using `trace_pos D.sp.cm.cmUnram.2.1 W hs hp`. Take `⟨h1, h2, h3⟩` from `Formalism.HermitianLatticesTheory.massBasic _ _ W.hT W.herm hpos W.L0 W.standardTuple_isLattice`. Take `⟨-, hwt, -⟩` from `Formalism.ThetaLiftIndependence.classRepsDefinite _ _ W.hT W.herm hpos W.L0 W.standardTuple_isLattice`.

Use `⟨h1, fun L hL => ?_, h2, h3⟩` and prove the remaining obligations. Take `⟨n, hn, hLn⟩` from `hwt L hL`. Establish `hc : Nat.card (Formalism.ThetaLiftIndependence.autL W.hT L) = n`. Unfold `Formalism.ThetaLiftIndependence.latWt at hLn`. Conclude with `inv_inj.mp hLn` after adjusting the coercions.

Rewrite using `[hc]`. Conclude with `hn`.
-/
theorem mass_formula₂ (D : D7) : letI := D.host.cmStar
    ∀ W : HSpace D.host.E, W.SigOK → (∀ τ : D.host.E →+* ℂ, W.sig τ = (2, 0)) →
      (∃ s, Formalism.ThetaLiftIndependence.IsClassReps W.hT W.L0 s) ∧
      (∀ L ∈ Formalism.HermitianLatticesTheory.genus W.hT W.L0, 0 < Nat.card (Formalism.ThetaLiftIndependence.autL W.hT L)) ∧
      (∀ s, Formalism.ThetaLiftIndependence.IsClassReps W.hT W.L0 s →
        Formalism.HermitianLatticesTheory.mass W.hT W.L0 = ∑ L ∈ s, ((Nat.card (Formalism.ThetaLiftIndependence.autL W.hT L) : ℕ) : ℝ)⁻¹) ∧
      0 < Formalism.HermitianLatticesTheory.mass W.hT W.L0 := by
  letI := D.host.cmStar
  intro W hs hp
  have hpos := trace_pos D.sp.cm.cmUnram.2.1 W hs hp
  obtain ⟨h1, h2, h3⟩ := Formalism.HermitianLatticesTheory.massBasic _ _ W.hT W.herm hpos W.L0 W.standardTuple_isLattice
  obtain ⟨-, hwt, -⟩ := Formalism.ThetaLiftIndependence.classRepsDefinite _ _ W.hT W.herm hpos W.L0 W.standardTuple_isLattice
  refine ⟨h1, fun L hL => ?_, h2, h3⟩
  obtain ⟨n, hn, hLn⟩ := hwt L hL
  have hc : Nat.card (Formalism.ThetaLiftIndependence.autL W.hT L) = n := by
    unfold Formalism.ThetaLiftIndependence.latWt at hLn
    exact_mod_cast inv_inj.mp hLn
  rw [hc]
  exact hn

end GlobalTheory.IndefiniteRowSideFullHecke.MassFormulaPositivity
