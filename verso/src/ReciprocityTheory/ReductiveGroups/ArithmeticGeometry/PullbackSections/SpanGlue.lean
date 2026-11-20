import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra

section Abstract

variable {K : Type*} [Field K] {σ : K →+* ℂ} {C : Type*} [AddCommGroup C] [Module K C]
  {W : Type*} [AddCommGroup W] [Module ℂ W]

def IndepToC (j : C →ₛₗ[σ] W) : Prop :=
  ∀ (n : ℕ) (b : Fin n → C), LinearIndependent K b → LinearIndependent ℂ (fun i => j (b i))

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩`. Consider the case `zero => simp`. Consider the case `add y w _ _ hy hw => rw [map_add]`. Conclude with `Submodule.add_mem _ hy hw`.

Consider the case `smul a y _ hy => rw [LinearMap.map_smulₛₗ]`. Conclude with `Submodule.smul_mem _ _ hy`.
-/
theorem map_mem_span_of_mem_span (j : C →ₛₗ[σ] W) (T : Set C) {x : C}
    (hx : x ∈ Submodule.span K T) : j x ∈ Submodule.span ℂ (j '' T) := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
  | zero => simp
  | add y w _ _ hy hw => rw [map_add]; exact Submodule.add_mem _ hy hw
  | smul a y _ hy => rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ hy

/- English proof (translation)
Rewrite using `[eq_top_iff]`. Introduce `f _`. Assume the negation of the conclusion as `hf`. Take `⟨T, hTS, hfT⟩` from `Submodule.mem_span_finite_of_mem_span (hS f)`. Take `⟨T', hT'S, rfl⟩` from `Finset.subset_set_image_iff.mp hTS`.

Take `⟨b, hbT, hspan, hli⟩` from `exists_linearIndependent K (T' : Set C)`. Establish `hbfin : b.Finite` using `(T'.finite_toSet).subset hbT`. Establish `hjf : j f ∈ Submodule.span ℂ (j '' b)`. Establish `hle : Submodule.span ℂ ((T'.image j : Finset W) : Set W) ≤ Submodule.span ℂ (j '' b)`. Rewrite using `[Submodule.span_le]`.

Introduce `y hy`. Rewrite `hy` using `[Finset.coe_image]`. Take `⟨t, ht, rfl⟩` from `hy`. Apply `map_mem_span_of_mem_span` to reduce the goal to its premises. Rewrite using `[hspan]`.

Conclude with `Submodule.subset_span ht`. Conclude with `hle hfT`. Establish `hfb : f ∉ Submodule.span K b`. Introduce `h`. Apply `hf` to reduce the goal to its premises.

Rewrite `h` using `[hspan]`. Conclude with `Submodule.span_mono hT'S h`. Establish `hli' : LinearIndependent K (fun y : ↥(insert f b) => (y : C))` using `LinearIndepOn.insert (v := id) (s := b) (x := f) hli (by simpa using hfb)`. Establish `hfin : (insert f b).Finite` using `hbfin.insert f`. Use `haveI := hfin.fintype`.

Set `e` to `Fintype.equivFin ↥(insert f b)`. Establish `hC` using `hj _ (fun i => ((e.symm i : ↥(insert f b)) : C)) (hli'.comp _ e.symm.injective)`. Establish `hC' : LinearIndependent ℂ (fun y : ↥(insert f b) => j (y : C))`. Use `hC.comp _ e.injective` as an intermediate fact. Simplify `this` using `[Function.comp_def]`.

Establish `hnot` using `hC'.notMem_span_image (s := {y : ↥(insert f b) | (y : C) ∈ b}) (x := ⟨f, Set.mem_insert f b⟩) (by`. Introduce `hx`. Conclude with `hfb (Submodule.subset_span hx))`. Apply `hnot` to reduce the goal to its premises. Use `hjf using 2` and compare the differences between its conclusion and the goal.

Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz, rfl⟩`. Conclude with `⟨z, hz, rfl⟩`. Introduce and unpack `⟨z, hz, rfl⟩`.

Conclude with `⟨⟨z, Set.mem_insert_of_mem f hz⟩, hz, rfl⟩`.
-/
theorem span_eq_top_of_indepToC (j : C →ₛₗ[σ] W) (hj : IndepToC j) (S : Set C)
    (hS : ∀ f, j f ∈ Submodule.span ℂ (j '' S)) : Submodule.span K S = ⊤ := by
  classical
  rw [eq_top_iff]
  intro f _
  by_contra hf
  obtain ⟨T, hTS, hfT⟩ := Submodule.mem_span_finite_of_mem_span (hS f)
  obtain ⟨T', hT'S, rfl⟩ := Finset.subset_set_image_iff.mp hTS
  obtain ⟨b, hbT, hspan, hli⟩ := exists_linearIndependent K (T' : Set C)
  have hbfin : b.Finite := (T'.finite_toSet).subset hbT

  have hjf : j f ∈ Submodule.span ℂ (j '' b) := by
    have hle : Submodule.span ℂ ((T'.image j : Finset W) : Set W) ≤ Submodule.span ℂ (j '' b) := by
      rw [Submodule.span_le]
      intro y hy
      rw [Finset.coe_image] at hy
      obtain ⟨t, ht, rfl⟩ := hy
      apply map_mem_span_of_mem_span
      rw [hspan]
      exact Submodule.subset_span ht
    exact hle hfT

  have hfb : f ∉ Submodule.span K b := by
    intro h
    apply hf
    rw [hspan] at h
    exact Submodule.span_mono hT'S h
  have hli' : LinearIndependent K (fun y : ↥(insert f b) => (y : C)) :=
    LinearIndepOn.insert (v := id) (s := b) (x := f) hli (by simpa using hfb)
  have hfin : (insert f b).Finite := hbfin.insert f
  haveI := hfin.fintype
  let e := Fintype.equivFin ↥(insert f b)
  have hC := hj _ (fun i => ((e.symm i : ↥(insert f b)) : C)) (hli'.comp _ e.symm.injective)
  have hC' : LinearIndependent ℂ (fun y : ↥(insert f b) => j (y : C)) := by
    have := hC.comp _ e.injective
    simpa [Function.comp_def] using this
  have hnot := hC'.notMem_span_image (s := {y : ↥(insert f b) | (y : C) ∈ b})
    (x := ⟨f, Set.mem_insert f b⟩) (by
      intro hx
      exact hfb (Submodule.subset_span hx))
  apply hnot
  convert hjf using 2
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨⟨z, Set.mem_insert_of_mem f hz⟩, hz, rfl⟩

end Abstract

/- English proof (translation)
Unfold `SpanAt`. Apply `span_eq_top_of_indepToC J hJ` to reduce the goal to its premises. Introduce `f`. Establish `h1 : Submodule.span ℂ A ≤ Submodule.span ℂ (J '' ((X.shortTh ka : Submodule (𝓞 B.KO) (B.Cusp j ka)) : Set (B.Cusp j ka)))`. Rewrite using `[Submodule.span_le]`.

Conclude with `hA`. Conclude with `h1 (hsp (hmem f))`.
-/
theorem spanAt_of_chain {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j)
    (ka : WeightFamilies.Wt D j) {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : B.KO →+* ℂ}
    (J : B.Cusp j ka →ₛₗ[σ] W) (hJ : IndepToC J) (Sp : Submodule ℂ W) (A : Set W)
    (hmem : ∀ f, J f ∈ Sp) (hsp : Sp ≤ Submodule.span ℂ A)
    (hA : A ⊆ Submodule.span ℂ (J '' ((X.shortTh ka : Submodule (𝓞 B.KO) (B.Cusp j ka)) : Set (B.Cusp j ka)))) :
    SpanAt X ka := by
  unfold SpanAt
  apply span_eq_top_of_indepToC J hJ
  intro f
  have h1 : Submodule.span ℂ A ≤
      Submodule.span ℂ (J '' ((X.shortTh ka : Submodule (𝓞 B.KO) (B.Cusp j ka)) : Set (B.Cusp j ka))) := by
    rw [Submodule.span_le]
    exact hA
  exact h1 (hsp (hmem f))

end ReciprocityTheory.ChartRestriction.G.PullbackSections
