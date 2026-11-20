import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.HostStarConj

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmW

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  NumberField IsDedekindDomain
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))

/- English proof (translation)
Rewrite using `[Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, sigR_tmul_one]`.
-/
theorem sigR_alg (c : Fv F v) :
    sigR (Fv F v) σ (algebraMap (Fv F v) (Fv F v ⊗[F] E) c) = algebraMap (Fv F v) (Fv F v ⊗[F] E) c := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, sigR_tmul_one]

/- English proof (translation)
Simplify using `only [hR, Formalism.UG.hform, Pi.smul_apply, Algebra.smul_def, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hR_smul_right (c : Fv F v) (x y : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J x (c • y) = c • hR (Fv F v) σ J x y := by
  simp only [hR, Formalism.UG.hform, Pi.smul_apply, Algebra.smul_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Simplify using `only [hR, Formalism.UG.hform, Pi.smul_apply, Algebra.smul_def, Finset.mul_sum, map_mul, sigR_alg]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hR_smul_left (c : Fv F v) (x y : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J (c • x) y = c • hR (Fv F v) σ J x y := by
  simp only [hR, Formalism.UG.hform, Pi.smul_apply, Algebra.smul_def, Finset.mul_sum, map_mul, sigR_alg]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Simplify using `only [hR, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]`.
-/
theorem hR_add_right (x y y' : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J x (y + y') = hR (Fv F v) σ J x y + hR (Fv F v) σ J x y' := by
  simp only [hR, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [hR, Formalism.UG.hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]`.
-/
theorem hR_add_left (x x' y : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J (x + x') y = hR (Fv F v) σ J x y + hR (Fv F v) σ J x' y := by
  simp only [hR, Formalism.UG.hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `[hR, Formalism.UG.hform]`.
-/
theorem hR_zero_right (x : Fin n → Fv F v ⊗[F] E) : hR (Fv F v) σ J x 0 = 0 := by
  simp [hR, Formalism.UG.hform]

/- English proof (translation)
Simplify using `[hR, Formalism.UG.hform]`.
-/
theorem hR_zero_left (y : Fin n → Fv F v ⊗[F] E) : hR (Fv F v) σ J 0 y = 0 := by
  simp [hR, Formalism.UG.hform]

/- English proof (translation)
The claim follows from `Submodule.smul_mem _ c hw`.
-/
theorem oev_smul {c : v.adicCompletionIntegers F} {w : Fv F v ⊗[F] E} (hw : w ∈ OEv (E := E) v) :
    (c : Fv F v) • w ∈ OEv (E := E) v :=
  Submodule.smul_mem _ c hw

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨a, ha, rfl⟩` from `hx`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy`.

Take `⟨b, hb, rfl⟩` from `hy`. Take `⟨o, ho⟩` from `hL a ha b hb`. Establish `h' : hR (Fv F v) σ J (fun i => inclR (Fv F v) (a i)) (fun i => inclR (Fv F v) (b i)) = inclR (Fv F v) (hE σ J a b)` using `hR_ratTup (Fv F v) σ J ![a, b] 0 1`. Express the relevant statement in the definitionally equal form `hR (Fv F v) σ J (fun i => inclR (Fv F v) (a i)) (fun i => inclR (Fv F v) (b i)) ∈ _`. Rewrite using `[h', ho]`.

Conclude with `Submodule.subset_span ⟨o, trivial, rfl⟩`. Consider the case `zero => rw [hR_zero_right]`. Conclude with `Submodule.zero_mem _`. Consider the case `add y y' _ _ h1 h2 => rw [hR_add_right]`. Conclude with `Submodule.add_mem _ h1 h2`.

Consider the case `smul c y _ h`. Express the relevant statement in the definitionally equal form `hR (Fv F v) σ J _ ((c : Fv F v) • y) ∈ _`. Rewrite using `[hR_smul_right]`. Conclude with `oev_smul v h`. Consider the case `zero => rw [hR_zero_left]`.

Conclude with `Submodule.zero_mem _`. Consider the case `add x x' _ _ h1 h2 => rw [hR_add_left]`. Conclude with `Submodule.add_mem _ h1 h2`. Consider the case `smul c x _ h`. Express the relevant statement in the definitionally equal form `hR (Fv F v) σ J ((c : Fv F v) • x) _ ∈ _`.

Rewrite using `[hR_smul_left]`. Conclude with `oev_smul v h`.
-/
theorem hR_mem_of (Λ : Set (Fin n → E))
    (hL : ∀ a ∈ Λ, ∀ b ∈ Λ, ∃ o : 𝓞 E, hE σ J a b = (o : E))
    {x y : Fin n → Fv F v ⊗[F] E} (hx : x ∈ latLoc (E := E) v Λ) (hy : y ∈ latLoc (E := E) v Λ) :
    hR (Fv F v) σ J x y ∈ OEv (E := E) v := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, hb, rfl⟩ := hy
      obtain ⟨o, ho⟩ := hL a ha b hb
      have h' : hR (Fv F v) σ J (fun i => inclR (Fv F v) (a i)) (fun i => inclR (Fv F v) (b i)) =
          inclR (Fv F v) (hE σ J a b) := hR_ratTup (Fv F v) σ J ![a, b] 0 1
      change hR (Fv F v) σ J (fun i => inclR (Fv F v) (a i)) (fun i => inclR (Fv F v) (b i)) ∈ _
      rw [h', ho]
      exact Submodule.subset_span ⟨o, trivial, rfl⟩
    | zero => rw [hR_zero_right]; exact Submodule.zero_mem _
    | add y y' _ _ h1 h2 => rw [hR_add_right]; exact Submodule.add_mem _ h1 h2
    | smul c y _ h =>
      change hR (Fv F v) σ J _ ((c : Fv F v) • y) ∈ _
      rw [hR_smul_right]; exact oev_smul v h
  | zero => rw [hR_zero_left]; exact Submodule.zero_mem _
  | add x x' _ _ h1 h2 => rw [hR_add_left]; exact Submodule.add_mem _ h1 h2
  | smul c x _ h =>
    change hR (Fv F v) σ J ((c : Fv F v) • x) _ ∈ _
    rw [hR_smul_left]; exact oev_smul v h

end Gen

variable {D : D7} (X : HidaSetting D)

/- English proof (translation)
Take `⟨o, ho⟩` from `(X.B.I.L_dual b).1 hb a ha`. Conclude with `⟨o, ho.symm⟩`.
-/
theorem hE_L (a : Fin X.B.I.n → X.B.I.E) (ha : a ∈ abelian₂ X) (b : Fin X.B.I.n → X.B.I.E) (hb : b ∈ abelian₂ X) :
    ∃ o : 𝓞 X.B.I.E, hE X.B.I.cm.sig X.B.I.J a b = (o : X.B.I.E) := by
  obtain ⟨o, ho⟩ := (X.B.I.L_dual b).1 hb a ha
  exact ⟨o, ho.symm⟩

/- English proof (translation)
The claim follows from `hR_mem_of X.B.I.cm.sig X.B.I.J v (abelian₂ X) (hE_L X) hx hy`.
-/
theorem omVSD_fwd (v : PlX X) {x y : Fin X.B.I.n → Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E}
    (hx : x ∈ latLoc (E := X.B.I.E) v (abelian₂ X)) (hy : y ∈ latLoc (E := X.B.I.E) v (abelian₂ X)) :
    hR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J x y ∈ OEv (E := X.B.I.E) v :=
  hR_mem_of X.B.I.cm.sig X.B.I.J v (abelian₂ X) (hE_L X) hx hy

def OmVSDBwd : Prop :=
  ∀ (v : PlX X) (y : Fin X.B.I.n → Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E),
    (∀ x ∈ latLoc (E := X.B.I.E) v (abelian₂ X), hR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J x y ∈ OEv (E := X.B.I.E) v) →
      y ∈ latLoc (E := X.B.I.E) v (abelian₂ X)

/- English proof (translation)
Introduce `v y` and use `⟨fun hy x hx => omVSD_fwd X v hx hy, h v y⟩`.
-/
theorem omVSD_of (h : OmVSDBwd X) : OmVSD X := fun v y =>
  ⟨fun hy x hx => omVSD_fwd X v hx hy, h v y⟩

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmW
