import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsTer

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical

/- English proof (translation)
Use `ext`. Simplify using `[aE, Matrix.GeneralLinearGroup.det, Matrix.det_fin_two]`.
-/
private theorem det_aE {F : Type} [Field F] [NumberField F] (a : (A F)ˣ) :
    Matrix.GeneralLinearGroup.det (aE (E := F) a) = a := by
  ext
  simp [aE, Matrix.GeneralLinearGroup.det, Matrix.det_fin_two]

/- English proof (translation)
Introduce `F _ _`. Rewrite using `[eq_top_iff]`. Introduce `h _`. Use `set C := Subgroup.closure (Set.range (fun b => gl (nU (F := F) b)) ∪ {gl (wW F)} ∪ Set.range (aE (E := F))) with hC`. Establish `hSL : ∀ s : G1 F, gl s ∈ C`.

Introduce `s`. Establish `hs : s ∈ Subgroup.closure (Set.range (nU (F` using `F)) ∪ {wW F}) := by`. Rewrite using `[(UpperTheory.ConvolutionTheory.R2.gen F).1]`. Discharge the goal by the elementary cases of `trivial`. Proceed by induction on `hs using Subgroup.closure_induction with`.

Consider the case `mem x hx`. Apply `Subgroup.subset_closure` to reduce the goal to its premises. Break down `hx with ⟨b, rfl⟩ | hx` into its components or cases. Conclude with `Or.inl (Or.inl ⟨b, rfl⟩)`. Rewrite `hx` using `[Set.mem_singleton_iff]`.

Substitute `hx` using the available equality. Conclude with `Or.inl (Or.inr rfl)`. Consider the case `one => simpa using C.one_mem`. Consider the case `mul x y _ _ hx hy => simpa using C.mul_mem hx hy`. Consider the case `inv x _ hx => simpa using C.inv_mem hx`.

Establish `hA : ∀ a, aE (E` using `F) a ∈ C := fun a => Subgroup.subset_closure (Or.inr ⟨a, rfl⟩)`. Use `set d := Matrix.GeneralLinearGroup.det h with hd`. Establish `hdet : Matrix.det (h * (aE (E` using `F) d)⁻¹).val = 1 := by`. Establish `: Matrix.GeneralLinearGroup.det (h * (aE (E` using `F) d)⁻¹) = 1 := by`. Rewrite using `[map_mul, map_inv, det_aE, ← hd, mul_inv_cancel]`.

Conclude with `congrArg Units.val this`. Establish `hs : gl (⟨(h * (aE (E` using `F) d)⁻¹).val, hdet⟩ : G1 F) = h * (aE (E := F) d)⁻¹ := by`. Use extensionality with `i j`. Both sides reduce to the same expression. Establish `h1 : h * (aE (E` using `F) d)⁻¹ ∈ C := hs ▸ hSL _`.

Use `C.mul_mem h1 (hA d)` as an intermediate fact. Simplify using `using this`.
-/
theorem UpperTheory.ConvolutionTheory.R2.D.genE :
    ∀ (F : Type) [Field F] [NumberField F], Subgroup.closure (Set.range (fun b => gl (nU (F := F) b)) ∪ {gl (wW F)} ∪ Set.range (aE (E := F))) = ⊤ := by
  intro F _ _
  rw [eq_top_iff]
  intro h _
  set C := Subgroup.closure (Set.range (fun b => gl (nU (F := F) b)) ∪ {gl (wW F)} ∪ Set.range (aE (E := F))) with hC
  have hSL : ∀ s : G1 F, gl s ∈ C := by
    intro s
    have hs : s ∈ Subgroup.closure (Set.range (nU (F := F)) ∪ {wW F}) := by
      rw [(UpperTheory.ConvolutionTheory.R2.gen F).1]
      trivial
    induction hs using Subgroup.closure_induction with
    | mem x hx =>
      apply Subgroup.subset_closure
      rcases hx with ⟨b, rfl⟩ | hx
      · exact Or.inl (Or.inl ⟨b, rfl⟩)
      · rw [Set.mem_singleton_iff] at hx
        subst hx
        exact Or.inl (Or.inr rfl)
    | one => simpa using C.one_mem
    | mul x y _ _ hx hy => simpa using C.mul_mem hx hy
    | inv x _ hx => simpa using C.inv_mem hx
  have hA : ∀ a, aE (E := F) a ∈ C := fun a => Subgroup.subset_closure (Or.inr ⟨a, rfl⟩)
  set d := Matrix.GeneralLinearGroup.det h with hd
  have hdet : Matrix.det (h * (aE (E := F) d)⁻¹).val = 1 := by
    have : Matrix.GeneralLinearGroup.det (h * (aE (E := F) d)⁻¹) = 1 := by
      rw [map_mul, map_inv, det_aE, ← hd, mul_inv_cancel]
    exact congrArg Units.val this
  have hs : gl (⟨(h * (aE (E := F) d)⁻¹).val, hdet⟩ : G1 F) = h * (aE (E := F) d)⁻¹ := by
    ext i j
    rfl
  have h1 : h * (aE (E := F) d)⁻¹ ∈ C := hs ▸ hSL _
  have := C.mul_mem h1 (hA d)
  simpa using this
