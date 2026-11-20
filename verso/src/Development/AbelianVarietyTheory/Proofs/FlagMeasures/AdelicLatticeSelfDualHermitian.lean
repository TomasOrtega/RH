import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointLatticeIntersectionSelfDualProperties

open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

namespace GlobalTheory.AdelicLattice

/- English proof (translation)
Introduce `I y`. Establish `hsig : ((I.cm.sig : I.E →ₐ[I.F] I.E) : I.E →+* I.E) = starRingEnd I.E`. Use extensionality with `a`. Both sides reduce to the same expression. Establish `hdual : ∀ x : Fin I.n → I.E, x ∈ I.L ↔ ∀ z ∈ I.L, Formalism.UG.hform ((I.cm.sig : I.E →ₐ[I.F] I.E) : I.E →+* I.E) I.J z x ∈ (algebraMap (𝓞 I.E) I.E).range`.

Rewrite using `[hsig]`. Conclude with `I.L_dual`. Establish `hgen : Set.range (fun x : I.L => fun i => Formalism.UG.inclE (F` using `I.F) (Af I.F) ((x : Fin I.n → I.E) i)) = (fun x : Fin I.n → I.E => fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (x i)) '' (I.L : Set (Fin I.n → I.E)) := by`. Use extensionality with `v`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨x, rfl⟩`. Conclude with `⟨x, x.2, rfl⟩`. Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `⟨⟨x, hx⟩, rfl⟩`. Establish `hLf : ∀ u, u ∈ I.Lf ↔ u ∈ Submodule.span (IntAf I.F I.E) ((fun x : Fin I.n → I.E => fun i => Formalism.UG.inclE (F` using `I.F) (Af I.F) (x i)) '' (I.L : Set (Fin I.n → I.E))) := by`.

Introduce `u`. Use `show u ∈ Submodule.span _ _ ↔ _`. Rewrite using `[hgen]`. Prove the components needed by the constructor for the conclusion. Introduce `hy y' hy'`.

Establish `hy''` using `(hLf y').1 hy'`. Unfold `hAf`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem v hv`. Take `⟨x, rfl⟩` from `hv`.

Conclude with `Formalism.UG.P.csDual_span I.cm.sig I.J I.L (x : Fin I.n → I.E) ((hdual _).1 x.2) y' hy''`. Consider the case `zero`. Rewrite using `[Formalism.UG.P.csScale_hform_zero_right]`. Conclude with `zero_mem _`. Consider the case `add u v _ _ hu hv`.

Rewrite using `[Formalism.UG.P.csScale_hform_add_right]`. Conclude with `add_mem hu hv`. Consider the case `smul c v _ hv`. Rewrite using `[Subring.smul_def, Formalism.UG.P.csScale_hform_smul_right]`. Conclude with `mul_mem c.2 hv`.

Introduce `h`. Establish `hmem` using `GlobalTheory.PointLattice.mem_latS_of_integral (F := I.F) I.cm.sig I.J I.L hdual I.L_span y (fun w hw => h w ((hLf w).2 hw))`. Conclude with `(hLf y).2 hmem`.
-/
theorem adelicLattice_selfDual : ∀ (I : AutInst) (y : Fin I.n → (I.E ⊗[I.F] Af I.F)), y ∈ I.Lf ↔ ∀ y' ∈ I.Lf, hAf I y' y ∈ IntAf I.F I.E := by
  intro I y
  have hsig : ((I.cm.sig : I.E →ₐ[I.F] I.E) : I.E →+* I.E) = starRingEnd I.E := by
    ext a
    rfl
  have hdual : ∀ x : Fin I.n → I.E, x ∈ I.L ↔ ∀ z ∈ I.L,
      Formalism.UG.hform ((I.cm.sig : I.E →ₐ[I.F] I.E) : I.E →+* I.E) I.J z x ∈
        (algebraMap (𝓞 I.E) I.E).range := by
    rw [hsig]
    exact I.L_dual

  have hgen : Set.range (fun x : I.L => fun i => Formalism.UG.inclE (F := I.F) (Af I.F) ((x : Fin I.n → I.E) i)) =
      (fun x : Fin I.n → I.E => fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (x i)) '' (I.L : Set (Fin I.n → I.E)) := by
    ext v
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hLf : ∀ u, u ∈ I.Lf ↔ u ∈ Submodule.span (IntAf I.F I.E)
      ((fun x : Fin I.n → I.E => fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (x i)) '' (I.L : Set (Fin I.n → I.E))) := by
    intro u
    show u ∈ Submodule.span _ _ ↔ _
    rw [hgen]
  constructor
  · intro hy y' hy'
    have hy'' := (hLf y').1 hy'
    unfold hAf
    induction hy using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨x, rfl⟩ := hv
      exact Formalism.UG.P.csDual_span I.cm.sig I.J I.L (x : Fin I.n → I.E) ((hdual _).1 x.2) y' hy''
    | zero =>
      rw [Formalism.UG.P.csScale_hform_zero_right]
      exact zero_mem _
    | add u v _ _ hu hv =>
      rw [Formalism.UG.P.csScale_hform_add_right]
      exact add_mem hu hv
    | smul c v _ hv =>
      rw [Subring.smul_def, Formalism.UG.P.csScale_hform_smul_right]
      exact mul_mem c.2 hv
  · intro h
    have hmem := GlobalTheory.PointLattice.mem_latS_of_integral (F := I.F) I.cm.sig I.J I.L hdual I.L_span y
      (fun w hw => h w ((hLf w).2 hw))
    exact (hLf y).2 hmem

end GlobalTheory.AdelicLattice
