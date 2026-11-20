import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.MatchPowAlt

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical
open UpperTheory.Gal.InertialTypesAlt.G

/- English proof (translation)
Introduce `G _ _ _ K f hK hN hf`. Take `⟨hlc, hcs⟩` from `hf`. Establish `h1 : ∀ x : G, ∃ V : Subgroup G, IsOpen (V : Set G) ∧ ∀ a ∈ V, f (a * x) = f x`. Introduce `x`. Establish `hopen : IsOpen ((fun a : G => a * x) ⁻¹' (f ⁻¹' {f x}))` using `(hlc.isOpen_fiber (f x)).preimage (continuous_mul_right x)`.

Take `⟨V, hV, hVs⟩` from `hN _ (hopen.mem_nhds (by simp))`. Conclude with `⟨V, hV, fun a ha => by simpa using hVs (SetLike.mem_coe.2 ha)⟩`. Use `choose V hVo hVc using h1`. Take `⟨t, -, hcov⟩` from `hcs.isCompact.elim_nhds_subcover (fun x => (fun y : G => y * x⁻¹) ⁻¹' (V x : Set G)) (fun x _ => ((hVo x).preimage (continuous_mul_right x⁻¹)).mem_nhds (by simp [one_mem]))`. Establish `hz : ∀ y, (∀ x ∈ t, y * x⁻¹ ∉ V x) → f y = 0`.

Introduce `y hy`. Assume the negation of the conclusion as `h`. Establish `hm` using `hcov (subset_tsupport f (Function.mem_support.2 h))`. Simplify using `only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe, exists_prop] at hm`. Take `⟨x, hx, hxy⟩` from `hm`.

Conclude with `hy x hx hxy`. Establish `hNU : (K : Set G) ∩ ⋂ x ∈ t, (V x : Set G) ∈ nhds (1 : G)` using `inter_mem (hK.mem_nhds K.one_mem) ((Filter.biInter_finset_mem t).2 fun x _ => (hVo x).mem_nhds (V x).one_mem)`. Take `⟨U, hU, hUs⟩` from `hN _ hNU`. Use `⟨U, hU, fun u hu => (hUs hu).1, fun u hu g => ?_⟩` and prove the remaining obligations. Establish `hUV : ∀ x ∈ t, u ∈ V x` using `fun x hx => by`.

Establish `h2` using `(hUs hu).2`. Simplify using `only [Set.mem_iInter, SetLike.mem_coe] at h2`. Conclude with `h2 x hx`. Distinguish the cases in `hg : ∃ x ∈ t, g * x⁻¹ ∈ V x`. Take `⟨x, hx, hgx⟩` from `hg`.

Establish `e1` using `hVc x _ hgx`. Establish `e2` using `hVc x _ ((V x).mul_mem (hUV x hx) hgx)`. Establish `r1 : g * x⁻¹ * x = g` using `by group`. Establish `r2 : u * (g * x⁻¹) * x = u * g` using `by group`. Rewrite `e1` using `[r1]`.

Rewrite `e2` using `[r2]`. Rewrite using `[e1, e2]`. Use `push_neg at hg`. Rewrite using `[hz g hg, hz (u * g)]`. Introduce `x hx hm`.

Apply `hg x hx` to reduce the goal to its premises. Establish `h3` using `(V x).mul_mem ((V x).inv_mem (hUV x hx)) hm`. Establish `r3 : u⁻¹ * (u * g * x⁻¹) = g * x⁻¹` using `by group`. Rewrite `h3` using `[r3]`. Then use the resulting hypothesis.
-/
theorem UpperTheory.Gal.InertialTypesAlt.G.levEx :
    UpperTheory.Gal.InertialTypesAlt.G.LevEx := by
  intro G _ _ _ K f hK hN hf
  obtain ⟨hlc, hcs⟩ := hf
  have h1 : ∀ x : G, ∃ V : Subgroup G, IsOpen (V : Set G) ∧ ∀ a ∈ V, f (a * x) = f x := by
    intro x
    have hopen : IsOpen ((fun a : G => a * x) ⁻¹' (f ⁻¹' {f x})) :=
      (hlc.isOpen_fiber (f x)).preimage (continuous_mul_right x)
    obtain ⟨V, hV, hVs⟩ := hN _ (hopen.mem_nhds (by simp))
    exact ⟨V, hV, fun a ha => by simpa using hVs (SetLike.mem_coe.2 ha)⟩
  choose V hVo hVc using h1
  obtain ⟨t, -, hcov⟩ := hcs.isCompact.elim_nhds_subcover
    (fun x => (fun y : G => y * x⁻¹) ⁻¹' (V x : Set G))
    (fun x _ => ((hVo x).preimage (continuous_mul_right x⁻¹)).mem_nhds (by simp [one_mem]))
  have hz : ∀ y, (∀ x ∈ t, y * x⁻¹ ∉ V x) → f y = 0 := by
    intro y hy
    by_contra h
    have hm := hcov (subset_tsupport f (Function.mem_support.2 h))
    simp only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe, exists_prop] at hm
    obtain ⟨x, hx, hxy⟩ := hm
    exact hy x hx hxy
  have hNU : (K : Set G) ∩ ⋂ x ∈ t, (V x : Set G) ∈ nhds (1 : G) :=
    inter_mem (hK.mem_nhds K.one_mem)
      ((Filter.biInter_finset_mem t).2 fun x _ => (hVo x).mem_nhds (V x).one_mem)
  obtain ⟨U, hU, hUs⟩ := hN _ hNU
  refine ⟨U, hU, fun u hu => (hUs hu).1, fun u hu g => ?_⟩
  have hUV : ∀ x ∈ t, u ∈ V x := fun x hx => by
    have h2 := (hUs hu).2
    simp only [Set.mem_iInter, SetLike.mem_coe] at h2
    exact h2 x hx
  by_cases hg : ∃ x ∈ t, g * x⁻¹ ∈ V x
  · obtain ⟨x, hx, hgx⟩ := hg
    have e1 := hVc x _ hgx
    have e2 := hVc x _ ((V x).mul_mem (hUV x hx) hgx)
    have r1 : g * x⁻¹ * x = g := by group
    have r2 : u * (g * x⁻¹) * x = u * g := by group
    rw [r1] at e1
    rw [r2] at e2
    rw [e1, e2]
  · push_neg at hg
    rw [hz g hg, hz (u * g)]
    intro x hx hm
    apply hg x hx
    have h3 := (V x).mul_mem ((V x).inv_mem (hUV x hx)) hm
    have r3 : u⁻¹ * (u * g * x⁻¹) = g * x⁻¹ := by group
    rwa [r3] at h3
