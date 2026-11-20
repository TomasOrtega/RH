import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwEig

/- English proof (translation)
The claim follows from `LinearMap.ext fun _ => rfl`.
-/
theorem map_mul (s : Bool) {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (f g : Module.End ℂ E) :
    (Tw.map s (f * g) : Module.End ℂ (Tw s E)) = Tw.map s f * Tw.map s g := LinearMap.ext fun _ => rfl

/- English proof (translation)
Proceed by induction on `k generalizing y with`. Consider the case `zero => rfl`. Consider the case `succ k ih`. Rewrite using `[pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ← ih]`. Both sides reduce to the same expression.
-/
theorem pow_sub_apply (s : Bool) {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (f : Module.End ℂ E)
    (μ : ℂ) (k : ℕ) (y : Tw s E) :
    Tw.out ((((Tw.map s f : Module.End ℂ (Tw s E)) - μ • 1) ^ k) y) = ((f - cj s μ • 1) ^ k) (Tw.out y) := by
  induction k generalizing y with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ← ih]
    rfl

/- English proof (translation)
Rewrite using `[Module.End.mem_maxGenEigenspace, Module.End.mem_maxGenEigenspace]`. Use `exists_congr fun k => ?_` and prove the remaining obligations. Rewrite using `[← pow_sub_apply]`. Both sides reduce to the same expression.
-/
theorem mem_maxGen (s : Bool) {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (f : Module.End ℂ E)
    (μ : ℂ) (y : Tw s E) :
    y ∈ Module.End.maxGenEigenspace (Tw.map s f : Module.End ℂ (Tw s E)) μ ↔ Tw.out y ∈ f.maxGenEigenspace (cj s μ) := by
  rw [Module.End.mem_maxGenEigenspace, Module.End.mem_maxGenEigenspace]
  refine exists_congr fun k => ?_
  rw [← pow_sub_apply]
  rfl

/- English proof (translation)
Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce `hy`. Conclude with `⟨Tw.out y, hy, rfl⟩`. Introduce and unpack `⟨x, hx, rfl⟩`.

Conclude with `hx`.
-/
theorem sub_eq_map (s : Bool) {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (V : Submodule ℂ E) :
    Tw.sub s V = V.map (Tw.mkL s E) := by
  ext y
  constructor
  · intro hy; exact ⟨Tw.out y, hy, rfl⟩
  · rintro ⟨x, hx, rfl⟩; exact hx

/- English proof (translation)
Simplify using `only [sub_eq_map, Submodule.map_iSup]`.
-/
theorem sub_iSup' (s : Bool) {E : Type} {C : Sort*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (Ec : C → Submodule ℂ E) :
    Tw.sub s (⨆ c, Ec c) = ⨆ c, Tw.sub s (Ec c) := by
  simp only [sub_eq_map, Submodule.map_iSup]

/- English proof (translation)
Use extensionality with `y`. Simplify using `only [Formalism.L2.Col.eigAt, Submodule.mem_iInf, mem_maxGen]`. Use `show _ ↔ Tw.out y ∈ ⨅ i, (h i).maxGenEigenspace (cj s (x i))`. Rewrite using `[Submodule.mem_iInf]`.
-/
theorem eigAt_tw (s : Bool) {E I : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (h : I → Module.End ℂ E)
    (x : I → ℂ) :
    Formalism.L2.Col.eigAt (fun i => (Tw.map s (h i) : Module.End ℂ (Tw s E))) x =
      Tw.sub s (Formalism.L2.Col.eigAt h fun i => cj s (x i)) := by
  ext y
  simp only [Formalism.L2.Col.eigAt, Submodule.mem_iInf, mem_maxGen]
  show _ ↔ Tw.out y ∈ ⨅ i, (h i).maxGenEigenspace (cj s (x i))
  rw [Submodule.mem_iInf]

end GlobalTheory.TwEig

open GlobalTheory.TwEig in
/- English proof (translation)
Introduce `s E I _ _ h`. Use `⟨fun hc i j => ?_, fun Q => ?_, fun Ec => sub_iSup' s Ec⟩` and prove the remaining obligations. Use `show Tw.map s (h i) * Tw.map s (h j) = Tw.map s (h j) * Tw.map s (h i)`. Rewrite using `[← map_mul, ← map_mul, (hc i j).eq]`. Simplify using `only [Formalism.L2.Col.eigSum, eigAt_tw]`.

Rewrite using `[sub_iSup']`. Set `e : (I → ℂ) ≃ (I → ℂ)` to `⟨fun x i => cj s (x i), fun x i => cj s (x i), fun x => funext fun i => cj_cj s (x i), fun x => funext fun i => cj_cj s (x i)⟩`. Rewrite using `[← e.iSup_comp]`. Use `iSup_congr fun x => ?_` and prove the remaining obligations. Simplify using `[e, cj_cj]`.

Conclude with `(sub_iSup' (E := E) s (fun _ : (Q fun i => cj s (x i)) => Formalism.L2.Col.eigAt h x)).symm`.
-/
theorem GlobalTheory.TwEig.pairComm_eigSum_sub_iSup : ∀ (s : Bool) {E I : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (h : I → Module.End ℂ E), (Formalism.L2.Col.PairComm h → Formalism.L2.Col.PairComm (fun i => (Tw.map s (h i) : Module.End ℂ (Tw s E)))) ∧ (∀ Q : (I → ℂ) → Prop, Formalism.L2.Col.eigSum (fun i => (Tw.map s (h i) : Module.End ℂ (Tw s E))) Q = Tw.sub s (Formalism.L2.Col.eigSum h fun x => Q fun i => cj s (x i))) ∧ ∀ {C : Type} (Ec : C → Submodule ℂ E), Tw.sub s (⨆ c, Ec c) = ⨆ c, Tw.sub s (Ec c) := by
  intro s E I _ _ h
  refine ⟨fun hc i j => ?_, fun Q => ?_, fun Ec => sub_iSup' s Ec⟩
  · show Tw.map s (h i) * Tw.map s (h j) = Tw.map s (h j) * Tw.map s (h i)
    rw [← map_mul, ← map_mul, (hc i j).eq]
  · simp only [Formalism.L2.Col.eigSum, eigAt_tw]
    rw [sub_iSup']
    let e : (I → ℂ) ≃ (I → ℂ) := ⟨fun x i => cj s (x i), fun x i => cj s (x i),
      fun x => funext fun i => cj_cj s (x i), fun x => funext fun i => cj_cj s (x i)⟩
    rw [← e.iSup_comp]
    refine iSup_congr fun x => ?_
    simp [e, cj_cj]
    exact (sub_iSup' (E := E) s (fun _ : (Q fun i => cj s (x i)) => Formalism.L2.Col.eigAt h x)).symm
