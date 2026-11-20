import Mathlib

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.Et.TrivTors

abbrev triv (n : ℕ) (V : Scheme.{0}) : Scheme.{0} := ∐ fun _ : ZMod n => V

abbrev proj (n : ℕ) (V : Scheme.{0}) : triv n V ⟶ V := Sigma.desc fun _ => 𝟙 V

def shift (n : ℕ) (V : Scheme.{0}) (k : ZMod n) : triv n V ⟶ triv n V :=
  Sigma.desc fun h => Sigma.ι (fun _ : ZMod n => V) (h + k)

def idx (n : ℕ) (V : Scheme.{0}) : C(↥(triv n V), ZMod n) :=
  ⟨fun x => ((sigmaMk (fun _ : ZMod n => V)).symm x).1,
    (continuous_sigma fun _ => continuous_const).comp (sigmaMk (fun _ : ZMod n => V)).symm.continuous⟩

variable {n : ℕ} {V : Scheme.{0}}

@[reassoc (attr := simp)]
/- English proof (translation)
Simplify using `[shift]`. Use the proof step `@[reassoc (attr := simp)]`.
-/
theorem ι_shift (k h : ZMod n) :
    Sigma.ι (fun _ : ZMod n => V) h ≫ shift n V k = Sigma.ι (fun _ : ZMod n => V) (h + k) := by
  simp [shift]

@[reassoc (attr := simp)]
/- English proof (translation)
Use extensionality with `h`. Simplify using `[shift]`. Use the proof step `@[simp]`.
-/
theorem shift_proj (k : ZMod n) : shift n V k ≫ proj n V = proj n V := by
  ext h
  simp [shift]

@[simp]
/- English proof (translation)
Establish `e` using `sigmaMk_mk (fun _ : ZMod n => V) h x`. Express the relevant statement in the definitionally equal form `((sigmaMk (fun _ : ZMod n => V)).symm ((Sigma.ι (fun _ : ZMod n => V) h).base x)).1 = h`. Establish `e' : (sigmaMk (fun _ : ZMod n => V)).symm ((Sigma.ι (fun _ : ZMod n => V) h).base x) = ⟨h, x⟩` using `(sigmaMk (fun _ : ZMod n => V)).symm_apply_eq.mpr e.symm`. Rewrite using `[e']`.
-/
theorem idx_ι (h : ZMod n) (x : V) : idx n V ((Sigma.ι (fun _ : ZMod n => V) h).base x) = h := by
  have e := sigmaMk_mk (fun _ : ZMod n => V) h x
  change ((sigmaMk (fun _ : ZMod n => V)).symm ((Sigma.ι (fun _ : ZMod n => V) h).base x)).1 = h
  have e' : (sigmaMk (fun _ : ZMod n => V)).symm ((Sigma.ι (fun _ : ZMod n => V) h).base x) = ⟨h, x⟩ :=
    (sigmaMk (fun _ : ZMod n => V)).symm_apply_eq.mpr e.symm
  rw [e']

end GlobalTheory.Et.TrivTors

end
