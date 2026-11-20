import Mathlib
import GroundTheory.AutomorphicForms.ContragredientTranspose.Character
import GroundTheory.AutomorphicForms.LocallyProfinite

noncomputable section

open GroundTheory.Automorphic GroundTheory.Automorphic.HeckeAlgebra GroundTheory.Automorphic.ContragredientTranspose
  GroundTheory.Automorphic.Whittaker MeasureTheory

namespace PositivityTheory.PfBern.Unit

section Faith

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsHaarMeasure]
  {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

section Level

variable {K : Subgroup G} (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))

/- English proof (translation)
The claim follows from `Subtype.ext (by change heckeAct μ ρ ((c • (h : HeckeAlgebra μ) : HeckeAlgebra μ) : G → ℂ) (w : V) = c • heckeAct μ ρ ((h : HeckeAlgebra μ) : G → ℂ) (w : V) rw [HeckeAlgebra.coe_smul] exact heckeAct_smul_left c (h : HeckeAlgebra μ).mem (smooth_of_mem_fixedVectors hKo w.2))`.
-/
theorem level_smul_smul (c : ℂ) (h : HeckeAlgebraLevel μ K hKc hKo) (w : fixedVectors ρ K) :
    (c • h) • w = c • (h • w) := Subtype.ext (by
  change heckeAct μ ρ ((c • (h : HeckeAlgebra μ) : HeckeAlgebra μ) : G → ℂ) (w : V) =
    c • heckeAct μ ρ ((h : HeckeAlgebra μ) : G → ℂ) (w : V)
  rw [HeckeAlgebra.coe_smul]
  exact heckeAct_smul_left c (h : HeckeAlgebra μ).mem (smooth_of_mem_fixedVectors hKo w.2))

/- English proof (translation)
The claim follows from `Subtype.ext (by change heckeAct μ ρ ((h : HeckeAlgebra μ) : G → ℂ) (c • (w : V)) = c • heckeAct μ ρ ((h : HeckeAlgebra μ) : G → ℂ) (w : V) exact heckeAct_smul_right (h : HeckeAlgebra μ).mem c (smooth_of_mem_fixedVectors hKo w.2))`.
-/
theorem level_smul_comm (c : ℂ) (h : HeckeAlgebraLevel μ K hKc hKo) (w : fixedVectors ρ K) :
    h • (c • w) = c • (h • w) := Subtype.ext (by
  change heckeAct μ ρ ((h : HeckeAlgebra μ) : G → ℂ) (c • (w : V)) =
    c • heckeAct μ ρ ((h : HeckeAlgebra μ) : G → ℂ) (w : V)
  exact heckeAct_smul_right (h : HeckeAlgebra μ).mem c (smooth_of_mem_fixedVectors hKo w.2))

/- English proof (translation)
Establish `hs` using `isSimpleModule_fixedVectors (μ := μ) hKc hKo hρ hK`. Set `φℂ : Module.End ℂ (fixedVectors ρ K)` to `{ toFun := φ map_add' := φ.map_add map_smul' := fun c w => by`. Establish `e : c • w = (c • (1 : HeckeAlgebraLevel μ K hKc hKo)) • w`. Rewrite using `[level_smul_smul, one_smul]`. Rewrite using `[RingHom.id_apply, e, φ.map_smul, level_smul_smul, one_smul] }`.

Establish `hnt : Nontrivial (fixedVectors ρ K)` using `Submodule.nontrivial_iff_ne_bot.2 hK`. Take `⟨c, hc⟩` from `Module.End.exists_eigenvalue φℂ`. Take `⟨w₀, hw₀⟩` from `hc.exists_hasEigenvector`. Set `ψ : Module.End (HeckeAlgebraLevel μ K hKc hKo) (fixedVectors ρ K)` to `{ toFun := fun w => φ w - c • w map_add' := fun a b => by rw [map_add, smul_add]; abel map_smul' := fun h w => by rw [RingHom.id_apply, φ.map_smul, smul_sub, level_smul_comm] }`. Establish `hw₀ker : w₀ ∈ LinearMap.ker ψ`.

Rewrite using `[LinearMap.mem_ker]`. Use `show φ w₀ - c • w₀ = 0`. Rewrite using `[sub_eq_zero]`. Conclude with `Module.End.mem_eigenspace_iff.1 hw₀.1`. Establish `hker : LinearMap.ker ψ ≠ ⊥` using `fun hb => hw₀.2 (by rw [hb] at hw₀ker; exact (Submodule.mem_bot _).1 hw₀ker)`.

Establish `htop` using `(eq_bot_or_eq_top (LinearMap.ker ψ)).resolve_left hker`. Use `⟨c, fun w => ?_⟩` and prove the remaining obligations. Establish `hw : w ∈ LinearMap.ker ψ` using `by rw [htop]; exact Submodule.mem_top`. Conclude with `sub_eq_zero.1 hw`.
-/
theorem level_schur (hρ : IsSmooth ρ) [ρ.IsIrreducible] [FiniteDimensional ℂ (fixedVectors ρ K)]
    (hK : fixedVectors ρ K ≠ ⊥) (φ : Module.End (HeckeAlgebraLevel μ K hKc hKo) (fixedVectors ρ K)) :
    ∃ c : ℂ, ∀ w, φ w = c • w := by
  have hs := isSimpleModule_fixedVectors (μ := μ) hKc hKo hρ hK
  let φℂ : Module.End ℂ (fixedVectors ρ K) :=
    { toFun := φ
      map_add' := φ.map_add
      map_smul' := fun c w => by
        have e : c • w = (c • (1 : HeckeAlgebraLevel μ K hKc hKo)) • w := by
          rw [level_smul_smul, one_smul]
        rw [RingHom.id_apply, e, φ.map_smul, level_smul_smul, one_smul] }
  have hnt : Nontrivial (fixedVectors ρ K) := Submodule.nontrivial_iff_ne_bot.2 hK
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue φℂ
  obtain ⟨w₀, hw₀⟩ := hc.exists_hasEigenvector
  let ψ : Module.End (HeckeAlgebraLevel μ K hKc hKo) (fixedVectors ρ K) :=
    { toFun := fun w => φ w - c • w
      map_add' := fun a b => by rw [map_add, smul_add]; abel
      map_smul' := fun h w => by rw [RingHom.id_apply, φ.map_smul, smul_sub, level_smul_comm] }
  have hw₀ker : w₀ ∈ LinearMap.ker ψ := by
    rw [LinearMap.mem_ker]
    show φ w₀ - c • w₀ = 0
    rw [sub_eq_zero]
    exact Module.End.mem_eigenspace_iff.1 hw₀.1
  have hker : LinearMap.ker ψ ≠ ⊥ := fun hb => hw₀.2 (by rw [hb] at hw₀ker; exact (Submodule.mem_bot _).1 hw₀ker)
  have htop := (eq_bot_or_eq_top (LinearMap.ker ψ)).resolve_left hker
  refine ⟨c, fun w => ?_⟩
  have hw : w ∈ LinearMap.ker ψ := by rw [htop]; exact Submodule.mem_top
  exact sub_eq_zero.1 hw

/- English proof (translation)
Establish `hs` using `isSimpleModule_fixedVectors (μ := μ) hKc hKo hρ hK`. Set `fE : Module.End (Module.End (HeckeAlgebraLevel μ K hKc hKo) (fixedVectors ρ K)) (fixedVectors ρ K)` to `{ toFun := A map_add' := A.map_add map_smul' := fun φ w => by`. Rewrite using `[Module.End.smul_def, RingHom.id_apply, Module.End.smul_def]`. Take `⟨c, hc⟩` from `level_schur hKc hKo hρ hK φ`. Rewrite using `[hc, hc, A.map_smul] }`.

Set `b` to `Module.finBasis ℂ (fixedVectors ρ K)`. Take `⟨r, hr⟩` from `jacobson_density fE (Finset.univ.image b)`. Use `⟨r, b.ext fun i => ?_⟩` and prove the remaining obligations. Use `hr (b i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))` as an intermediate fact. Conclude with `this.symm`.
-/
theorem level_density (hρ : IsSmooth ρ) [ρ.IsIrreducible] [FiniteDimensional ℂ (fixedVectors ρ K)]
    (hK : fixedVectors ρ K ≠ ⊥) (A : Module.End ℂ (fixedVectors ρ K)) :
    ∃ r : HeckeAlgebraLevel μ K hKc hKo, levelLin hKc hKo ρ r = A := by
  classical
  have hs := isSimpleModule_fixedVectors (μ := μ) hKc hKo hρ hK
  let fE : Module.End (Module.End (HeckeAlgebraLevel μ K hKc hKo) (fixedVectors ρ K)) (fixedVectors ρ K) :=
    { toFun := A
      map_add' := A.map_add
      map_smul' := fun φ w => by
        rw [Module.End.smul_def, RingHom.id_apply, Module.End.smul_def]
        obtain ⟨c, hc⟩ := level_schur hKc hKo hρ hK φ
        rw [hc, hc, A.map_smul] }
  let b := Module.finBasis ℂ (fixedVectors ρ K)
  obtain ⟨r, hr⟩ := jacobson_density fE (Finset.univ.image b)
  refine ⟨r, b.ext fun i => ?_⟩
  have := hr (b i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  exact this.symm

end Level

/- English proof (translation)
Use `LinearMap.ext fun v => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.zero_apply]`. Distinguish the cases in `hv0 : v = 0`. Rewrite using `[hv0, map_zero]`. Establish `hU : (stabilizerOf ρ v : Set G) ∩ (stabilizerOf ρ (S v) : Set G) ∈ nhds (1 : G)` using `Filter.inter_mem ((hρ.1 v).mem_nhds (one_mem _)) ((hρ.1 (S v)).mem_nhds (one_mem _))`.

Take `⟨K, hKc, hKU⟩` from `exists_openSubgroup_isCompact_subset hU`. Establish `hKo : IsOpen ((K : Subgroup G) : Set G)` using `K.isOpen`. Use `haveI := hρ.2 (K : Subgroup G) hKc hKo`. Establish `hvW : v ∈ fixedVectors ρ (K : Subgroup G)`. Rewrite using `[mem_fixedVectors]`.

Introduce `x hx`. Conclude with `(hKU hx).1`. Establish `hSvW : S v ∈ fixedVectors ρ (K : Subgroup G)`. Rewrite using `[mem_fixedVectors]`. Introduce `x hx`.

Conclude with `(hKU hx).2`. Establish `hW : fixedVectors ρ (K : Subgroup G) ≠ ⊥` using `fun hb => hv0 (by`. Use `hvW` as an intermediate fact. Rewrite `this` using `[hb]`. Conclude with `(Submodule.mem_bot ℂ).1 this)`.

Set `M : Module.End ℂ (fixedVectors ρ (K : Subgroup G))` to `fixedProj ρ hρ.1 hKc hKo ∘ₗ S ∘ₗ (fixedVectors ρ (K : Subgroup G)).subtype`. Establish `htr : ∀ r : HeckeAlgebraLevel μ (K : Subgroup G) hKc hKo, LinearMap.trace ℂ (fixedVectors ρ (K : Subgroup G)) (levelLin hKc hKo ρ r ∘ₗ M) = 0`. Introduce `r`. Establish `hle : LinearMap.range (heckeLin μ hρ.1 (r : HeckeAlgebra μ) ∘ₗ S) ≤ fixedVectors ρ (K : Subgroup G)`. Introduce and unpack `_ ⟨x, rfl⟩`.

Conclude with `range_heckeLin_le μ hρ.1 (r : HeckeAlgebra μ) (K := (K : Subgroup G)) (fun k hk y => HeckeAlgebraLevel.apply_mul_left hKc hKo r hk y) (LinearMap.mem_range_self _ (S x))`. Establish `h0` using `h (r : HeckeAlgebra μ)`. Rewrite `h0` using `[← finTrace_eq_trace _ _ hle]`. Use `h0 using 2` and compare the differences between its conclusion and the goal. Use `LinearMap.ext fun w => Subtype.ext ?_` and prove the remaining obligations.

Establish `hri : idem μ hKc hKo * (r : HeckeAlgebra μ) = (r : HeckeAlgebra μ) ∧ (r : HeckeAlgebra μ) * idem μ hKc hKo = (r : HeckeAlgebra μ)` using `(mem_biInvariant_iff_idem hKc hKo).1 (HeckeAlgebraLevel.val_mem hKc hKo r)`. Express the relevant statement in the definitionally equal form `heckeAct μ ρ ((r : HeckeAlgebra μ) : G → ℂ) (fixedProj ρ hρ.1 hKc hKo (S w) : V) = heckeAct μ ρ ((r : HeckeAlgebra μ) : G → ℂ) (S w)`. Rewrite using `[← heckeAct_idem_eq_fixedProj (μ := μ) hKc hKo hρ.1, ← heckeAct_groupConv (r : HeckeAlgebra μ).mem (idem μ hKc hKo).mem (hρ.1 _), ← HeckeAlgebra.coe_mul, hri.2]`. Establish `hM : M = 0`. Use `LinearMap.ext fun w => ?_` and prove the remaining obligations.

Rewrite using `[LinearMap.zero_apply]`. Assume the negation of the conclusion as `hne`. Choose the witnesses or unpack the hypotheses as in `⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ (fixedVectors ρ (K : Subgroup G)), φ (M w) ≠ 0 := by`. Assume the negation of the conclusion as `hall`. Use `push_neg at hall`.

Conclude with `hne ((Module.forall_dual_apply_eq_zero_iff ℂ (M w)).1 hall)`. Take `⟨r, hr⟩` from `level_density (μ := μ) hKc hKo hρ.1 hW (φ.smulRight w)`. Use `htr r` as an intermediate fact. Rewrite `this` using `[hr]`. Establish `e : φ.smulRight w ∘ₗ M = (φ ∘ₗ M).smulRight w` using `LinearMap.ext fun x => rfl`.

Rewrite `this` using `[e, LinearMap.trace_smulRight]`. Conclude with `hφ this`. Establish `h1 : (M ⟨v, hvW⟩ : V) = S v` using `fixedProj_apply_of_mem hρ.1 hKc hKo hSvW`. Rewrite using `[← h1, hM, LinearMap.zero_apply, Submodule.coe_zero]`.
-/
theorem trace_faithful (hρ : IsAdmissible ρ) [ρ.IsIrreducible] (S : Module.End ℂ V)
    (h : ∀ f : locallyConstantCompactSupport G ℂ ℂ, finTrace (heckeLin μ hρ.1 f ∘ₗ S) = 0) : S = 0 := by
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.zero_apply]
  by_cases hv0 : v = 0
  · rw [hv0, map_zero]
  have hU : (stabilizerOf ρ v : Set G) ∩ (stabilizerOf ρ (S v) : Set G) ∈ nhds (1 : G) :=
    Filter.inter_mem ((hρ.1 v).mem_nhds (one_mem _)) ((hρ.1 (S v)).mem_nhds (one_mem _))
  obtain ⟨K, hKc, hKU⟩ := exists_openSubgroup_isCompact_subset hU
  have hKo : IsOpen ((K : Subgroup G) : Set G) := K.isOpen
  haveI := hρ.2 (K : Subgroup G) hKc hKo
  have hvW : v ∈ fixedVectors ρ (K : Subgroup G) := by
    rw [mem_fixedVectors]; intro x hx; exact (hKU hx).1
  have hSvW : S v ∈ fixedVectors ρ (K : Subgroup G) := by
    rw [mem_fixedVectors]; intro x hx; exact (hKU hx).2
  have hW : fixedVectors ρ (K : Subgroup G) ≠ ⊥ := fun hb => hv0 (by
    have := hvW; rw [hb] at this; exact (Submodule.mem_bot ℂ).1 this)
  let M : Module.End ℂ (fixedVectors ρ (K : Subgroup G)) :=
    fixedProj ρ hρ.1 hKc hKo ∘ₗ S ∘ₗ (fixedVectors ρ (K : Subgroup G)).subtype
  have htr : ∀ r : HeckeAlgebraLevel μ (K : Subgroup G) hKc hKo,
      LinearMap.trace ℂ (fixedVectors ρ (K : Subgroup G)) (levelLin hKc hKo ρ r ∘ₗ M) = 0 := by
    intro r
    have hle : LinearMap.range (heckeLin μ hρ.1 (r : HeckeAlgebra μ) ∘ₗ S) ≤ fixedVectors ρ (K : Subgroup G) := by
      rintro _ ⟨x, rfl⟩
      exact range_heckeLin_le μ hρ.1 (r : HeckeAlgebra μ) (K := (K : Subgroup G))
        (fun k hk y => HeckeAlgebraLevel.apply_mul_left hKc hKo r hk y) (LinearMap.mem_range_self _ (S x))
    have h0 := h (r : HeckeAlgebra μ)
    rw [← finTrace_eq_trace _ _ hle] at h0
    convert h0 using 2
    refine LinearMap.ext fun w => Subtype.ext ?_
    have hri : idem μ hKc hKo * (r : HeckeAlgebra μ) = (r : HeckeAlgebra μ) ∧
        (r : HeckeAlgebra μ) * idem μ hKc hKo = (r : HeckeAlgebra μ) :=
      (mem_biInvariant_iff_idem hKc hKo).1 (HeckeAlgebraLevel.val_mem hKc hKo r)
    change heckeAct μ ρ ((r : HeckeAlgebra μ) : G → ℂ) (fixedProj ρ hρ.1 hKc hKo (S w) : V) =
      heckeAct μ ρ ((r : HeckeAlgebra μ) : G → ℂ) (S w)
    rw [← heckeAct_idem_eq_fixedProj (μ := μ) hKc hKo hρ.1,
      ← heckeAct_groupConv (r : HeckeAlgebra μ).mem (idem μ hKc hKo).mem (hρ.1 _), ← HeckeAlgebra.coe_mul, hri.2]
  have hM : M = 0 := by
    refine LinearMap.ext fun w => ?_
    rw [LinearMap.zero_apply]
    by_contra hne
    obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ (fixedVectors ρ (K : Subgroup G)), φ (M w) ≠ 0 := by
      by_contra hall
      push_neg at hall
      exact hne ((Module.forall_dual_apply_eq_zero_iff ℂ (M w)).1 hall)
    obtain ⟨r, hr⟩ := level_density (μ := μ) hKc hKo hρ.1 hW (φ.smulRight w)
    have := htr r
    rw [hr] at this
    have e : φ.smulRight w ∘ₗ M = (φ ∘ₗ M).smulRight w := LinearMap.ext fun x => rfl
    rw [e, LinearMap.trace_smulRight] at this
    exact hφ this
  have h1 : (M ⟨v, hvW⟩ : V) = S v := fixedProj_apply_of_mem hρ.1 hKc hKo hSvW
  rw [← h1, hM, LinearMap.zero_apply, Submodule.coe_zero]

end Faith

end PositivityTheory.PfBern.Unit
