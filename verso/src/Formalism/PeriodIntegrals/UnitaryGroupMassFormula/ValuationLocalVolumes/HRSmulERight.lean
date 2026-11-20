import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.InclRMemOEv
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.HRSmulRight

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmW

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  NumberField IsDedekindDomain Matrix
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))

/- English proof (translation)
Simplify using `only [hR, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hR_smulE_right (c : Fv F v ⊗[F] E) (x y : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J x (c • y) = c * hR (Fv F v) σ J x y := by
  simp only [hR, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp only [Finset.sum_empty]`. Conclude with `hR_zero_right σ J v x`. Consider the case `insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hR_add_right, ih]`.
-/
theorem hR_sum_right {ι : Type} (s : Finset ι) (x : Fin n → Fv F v ⊗[F] E) (f : ι → Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J x (∑ i ∈ s, f i) = ∑ i ∈ s, hR (Fv F v) σ J x (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact hR_zero_right σ J v x
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hR_add_right, ih]

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨a, _, rfl⟩` from `hx`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy`.

Take `⟨b, _, rfl⟩` from `hy`. Rewrite using `[← map_mul]`. Conclude with `Submodule.subset_span ⟨a * b, trivial, by simp⟩`. Consider the case `zero => rw [mul_zero]`. Conclude with `Submodule.zero_mem _`.

Consider the case `add y y' _ _ h1 h2 => rw [mul_add]`. Conclude with `Submodule.add_mem _ h1 h2`. Consider the case `smul c y _ h => rw [mul_smul_comm]`. Conclude with `Submodule.smul_mem _ c h`. Consider the case `zero => rw [zero_mul]`.

Conclude with `Submodule.zero_mem _`. Consider the case `add x x' _ _ h1 h2 => rw [add_mul]`. Conclude with `Submodule.add_mem _ h1 h2`. Consider the case `smul c x _ h => rw [smul_mul_assoc]`. Conclude with `Submodule.smul_mem _ c h`.
-/
theorem oev_mul {x y : Fv F v ⊗[F] E} (hx : x ∈ OEv (E := E) v) (hy : y ∈ OEv (E := E) v) :
    x * y ∈ OEv (E := E) v := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, _, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, _, rfl⟩ := hy
      rw [← map_mul]
      exact Submodule.subset_span ⟨a * b, trivial, by simp⟩
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add y y' _ _ h1 h2 => rw [mul_add]; exact Submodule.add_mem _ h1 h2
    | smul c y _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ c h
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add x x' _ _ h1 h2 => rw [add_mul]; exact Submodule.add_mem _ h1 h2
  | smul c x _ h => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c h

end Gen

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)

/- English proof (translation)
Proceed by induction on `hc using Submodule.span_induction with`. Consider the case `mem c hc`. Take `⟨o, _, rfl⟩` from `hc`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨l, hl, rfl⟩` from `hx`. Use `Submodule.subset_span ⟨o • l, X.B.I.L.smul_mem o hl, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Simplify using `only [ratV, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[← map_mul]`.

Both sides reduce to the same expression. Consider the case `zero => rw [smul_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x x' _ _ h1 h2 => rw [smul_add]`. Conclude with `Submodule.add_mem _ h1 h2`.

Consider the case `smul d x _ h => beta_reduce beta_reduce at h`. Establish `e : inclR (F` using `X.B.I.F) (Fv X.B.I.F v) (o : X.B.I.E) • (d • x) = d • (inclR (F := X.B.I.F) (Fv X.B.I.F v) (o : X.B.I.E) • x) := by`. Use function extensionality and compare the values at `i`. Express the relevant statement in the definitionally equal form `_ * ((d : Fv X.B.I.F v) • x i) = (d : Fv X.B.I.F v) • (_ * x i)`. Rewrite using `[mul_smul_comm]`.

Rewrite using `[e]`. Conclude with `Submodule.smul_mem _ d h`. Consider the case `zero => rw [zero_smul]`. Conclude with `Submodule.zero_mem _`. Consider the case `add c c' _ _ h1 h2 => rw [add_smul]`.

Conclude with `Submodule.add_mem _ h1 h2`. Consider the case `smul d c _ h`. Establish `e : (d • c) • x = d • (c • x)`. Use function extensionality and compare the values at `i`. Express the relevant statement in the definitionally equal form `((d : Fv X.B.I.F v) • c) * x i = (d : Fv X.B.I.F v) • (c * x i)`.

Rewrite using `[smul_mul_assoc]`. Rewrite using `[e]`. Conclude with `Submodule.smul_mem _ d h`.
-/
theorem lat_oev_smul (v : PlX X) {c : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E} (hc : c ∈ OEv (E := X.B.I.E) v)
    {x : Fin X.B.I.n → Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E} (hx : x ∈ latLoc (E := X.B.I.E) v (abelian₂ X)) :
    c • x ∈ latLoc (E := X.B.I.E) v (abelian₂ X) := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨o, _, rfl⟩ := hc
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨l, hl, rfl⟩ := hx
      refine Submodule.subset_span ⟨o • l, X.B.I.L.smul_mem o hl, ?_⟩
      funext i
      simp only [ratV, Pi.smul_apply, smul_eq_mul]
      rw [← map_mul]
      rfl
    | zero => rw [smul_zero]; exact Submodule.zero_mem _
    | add x x' _ _ h1 h2 => rw [smul_add]; exact Submodule.add_mem _ h1 h2
    | smul d x _ h =>
      beta_reduce
      beta_reduce at h
      have e : inclR (F := X.B.I.F) (Fv X.B.I.F v) (o : X.B.I.E) • (d • x) =
          d • (inclR (F := X.B.I.F) (Fv X.B.I.F v) (o : X.B.I.E) • x) := by
        funext i
        change _ * ((d : Fv X.B.I.F v) • x i) = (d : Fv X.B.I.F v) • (_ * x i)
        rw [mul_smul_comm]
      rw [e]; exact Submodule.smul_mem _ d h
  | zero => rw [zero_smul]; exact Submodule.zero_mem _
  | add c c' _ _ h1 h2 => rw [add_smul]; exact Submodule.add_mem _ h1 h2
  | smul d c _ h =>
    have e : (d • c) • x = d • (c • x) := by
      funext i
      change ((d : Fv X.B.I.F v) • c) * x i = (d : Fv X.B.I.F v) • (c * x i)
      rw [smul_mul_assoc]
    rw [e]; exact Submodule.smul_mem _ d h

abbrev zi : Fin (D.R.rS + 1 + D.R.rS) := Fin.castAdd D.R.rS (Fin.last D.R.rS)

/- English proof (translation)
Rewrite using `[gram_eq, diagonal_mul]`. Simplify using `only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq, Function.Involutive.coe_toPerm]`. Distinguish the cases in `h : i = piv D.R.rS j`. Rewrite using `[if_pos h.symm, if_pos h, mul_one]`. Rewrite using `[if_neg (fun e => h e.symm), if_neg h, mul_zero]`.
-/
theorem gramE_entry (j i : Fin (D.R.rS + 1 + D.R.rS)) :
    gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) j i = if i = piv D.R.rS j then cD X u' j else 0 := by
  rw [gram_eq, diagonal_mul]
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
    Option.some.injEq, Function.Involutive.coe_toPerm]
  by_cases h : i = piv D.R.rS j
  · rw [if_pos h.symm, if_pos h, mul_one]
  · rw [if_neg (fun e => h e.symm), if_neg h, mul_zero]

def OmVMem : Prop := ∀ (v : PlX X) (i : Fin (D.R.rS + 1 + D.R.rS)), yTup X u' v i ∈ latLoc (E := X.B.I.E) v (abelian₂ X)

def OmVZPrim : Prop :=
  ∀ v : PlX X, ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal → ∀ c : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E,
    c • yTup X u' v (zi (D := D)) ∈ latLoc (E := X.B.I.E) v (abelian₂ X) → c ∈ OEv (E := X.B.I.E) v

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmW
