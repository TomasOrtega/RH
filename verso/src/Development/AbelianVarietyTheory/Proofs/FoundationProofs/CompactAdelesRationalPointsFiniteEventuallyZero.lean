import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValHalfInf
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberField
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CocompactTensor
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.Doubling GlobalTheory.Eis.Conv

namespace GlobalTheory.Eis.Conv.Discr

open Filter Topology

section Abstract

variable {A E : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [Field E]
  (ι : E →+* A)

/- English proof (translation)
Take `⟨U, hU, hx⟩` from `h`. Use `hΩ.induction_on (p := fun s => {x : E | ι x ∈ s}.Finite) (by simp) (fun s t hst ht => ht.subset fun x hx => hst hx) (fun s t hs ht => (hs.union ht).subset fun x hx => hx) fun a _ => ?_` and prove the remaining obligations. Establish `hc : ContinuousAt (fun p : A × A => p.1 - p.2) (a, a)` using `by fun_prop`. Establish `h1 : (fun p : A × A => p.1 - p.2) ⁻¹' U ∈ 𝓝 (a, a)` using `hc.preimage_mem_nhds (by simpa using hU)`. Rewrite `h1` using `[nhds_prod_eq, Filter.mem_prod_self_iff]`.

Take `⟨V, hV, hVU⟩` from `h1`. Use `⟨V, mem_nhdsWithin_of_mem_nhds hV, Set.Subsingleton.finite fun x hx' y hy => ?_⟩` and prove the remaining obligations. Use `sub_eq_zero.1 (hx _ ?_)` and prove the remaining obligations. Rewrite using `[map_sub]`. Conclude with `hVU (Set.mk_mem_prod hx' hy)`.
-/
theorem finite_of_isCompact (h : ∃ U ∈ 𝓝 (0 : A), ∀ x : E, ι x ∈ U → x = 0) {Ω : Set A}
    (hΩ : IsCompact Ω) : {x : E | ι x ∈ Ω}.Finite := by
  obtain ⟨U, hU, hx⟩ := h
  refine hΩ.induction_on (p := fun s => {x : E | ι x ∈ s}.Finite) (by simp)
    (fun s t hst ht => ht.subset fun x hx => hst hx)
    (fun s t hs ht => (hs.union ht).subset fun x hx => hx) fun a _ => ?_
  have hc : ContinuousAt (fun p : A × A => p.1 - p.2) (a, a) := by fun_prop
  have h1 : (fun p : A × A => p.1 - p.2) ⁻¹' U ∈ 𝓝 (a, a) :=
    hc.preimage_mem_nhds (by simpa using hU)
  rw [nhds_prod_eq, Filter.mem_prod_self_iff] at h1
  obtain ⟨V, hV, hVU⟩ := h1
  refine ⟨V, mem_nhdsWithin_of_mem_nhds hV, Set.Subsingleton.finite fun x hx' y hy => ?_⟩
  refine sub_eq_zero.1 (hx _ ?_)
  rw [map_sub]
  exact hVU (Set.mk_mem_prod hx' hy)

/- English proof (translation)
Establish `hK : IsCompact ((fun p : A × A => p.1 * p.2) '' (insert ε (Set.range fun m : ℕ => s ^ m) ×ˢ Ω))` using `(hs.isCompact_insert_range.prod hΩ).image (by fun_prop)`. Establish `hfin` using `finite_of_isCompact ι h hK`. Establish `hev : ∀ x : E, ∀ᶠ m : ℕ in atTop, ∀ ω ∈ Ω, ι x = s ^ m * ω → x = 0`. Introduce `x`. Distinguish the cases in `hx : x = 0`.

Conclude with `Eventually.of_forall fun _ _ _ _ => hx`. Establish `h1 : ∀ᶠ t in 𝓝 ε, ∀ ω ∈ Ω, ι x ≠ t * ω`. Use `hΩ.eventually_forall_of_forall_eventually (P := fun t ω => ι x ≠ t * ω) fun ω _ => ?_` and prove the remaining obligations. Establish `ho : IsOpen {p : A × A | ι x ≠ p.1 * p.2}` using `isOpen_ne_fun continuous_const (by fun_prop)`. Use `ho.mem_nhds fun he => hε ?_` and prove the remaining obligations.

Establish `hu : IsUnit (ε * ω)`. Use `(IsUnit.mk0 x hx).map ι` as an intermediate fact. Rewrite `this` using `[he]`. Then use the resulting hypothesis. Conclude with `isUnit_of_mul_isUnit_left hu`. Use `filter_upwards [hs.eventually h1] with m hm ω hω he`.

Conclude with `absurd he (hm ω hω)`. Take `⟨m₀, hm₀⟩` from `eventually_atTop.1 ((eventually_all_finite hfin).2 fun x _ => hev x)`. Use `⟨m₀, fun m hm ω hω x hx => hm₀ m hm x ?_ ω hω hx⟩` and prove the remaining obligations. Conclude with `⟨(s ^ m, ω), ⟨Or.inr ⟨m, rfl⟩, hω⟩, hx.symm⟩`.
-/
theorem eventually_eq_zero [T2Space A] (h : ∃ U ∈ 𝓝 (0 : A), ∀ x : E, ι x ∈ U → x = 0)
    {Ω : Set A} (hΩ : IsCompact Ω) {s ε : A} (hs : Tendsto (fun m : ℕ => s ^ m) atTop (𝓝 ε))
    (hε : ¬ IsUnit ε) :
    ∃ m₀ : ℕ, ∀ m, m₀ ≤ m → ∀ ω ∈ Ω, ∀ x : E, ι x = s ^ m * ω → x = 0 := by
  have hK : IsCompact ((fun p : A × A => p.1 * p.2) ''
      (insert ε (Set.range fun m : ℕ => s ^ m) ×ˢ Ω)) :=
    (hs.isCompact_insert_range.prod hΩ).image (by fun_prop)
  have hfin := finite_of_isCompact ι h hK
  have hev : ∀ x : E, ∀ᶠ m : ℕ in atTop, ∀ ω ∈ Ω, ι x = s ^ m * ω → x = 0 := by
    intro x
    by_cases hx : x = 0
    · exact Eventually.of_forall fun _ _ _ _ => hx
    have h1 : ∀ᶠ t in 𝓝 ε, ∀ ω ∈ Ω, ι x ≠ t * ω := by
      refine hΩ.eventually_forall_of_forall_eventually (P := fun t ω => ι x ≠ t * ω)
        fun ω _ => ?_
      have ho : IsOpen {p : A × A | ι x ≠ p.1 * p.2} :=
        isOpen_ne_fun continuous_const (by fun_prop)
      refine ho.mem_nhds fun he => hε ?_
      have hu : IsUnit (ε * ω) := by
        have := (IsUnit.mk0 x hx).map ι
        rwa [he] at this
      exact isUnit_of_mul_isUnit_left hu
    filter_upwards [hs.eventually h1] with m hm ω hω he
    exact absurd he (hm ω hω)
  obtain ⟨m₀, hm₀⟩ := eventually_atTop.1 ((eventually_all_finite hfin).2 fun x _ => hev x)
  refine ⟨m₀, fun m hm ω hω x hx => hm₀ m hm x ?_ ω hω hx⟩
  exact ⟨(s ^ m, ω), ⟨Or.inr ⟨m, rfl⟩, hω⟩, hx.symm⟩

end Abstract

/- English proof (translation)
Establish `h1 : Tendsto (fun m : ℕ => (algebraMap F (Ainf F) 2⁻¹) ^ m) atTop (𝓝 0)`. Use `tendsto_pi_nhds.2 fun v => ?_` and prove the remaining obligations. Establish `h : ‖algebraMap F (Ainf F) 2⁻¹ v‖ < 1`. Rewrite using `[InfiniteAdeleRing.algebraMap_apply, InfinitePlace.Completion.norm_coe]`. Express the relevant statement in the definitionally equal form `v (2⁻¹ : F) < 1`.

Rewrite using `[← InfinitePlace.norm_embedding_eq, map_inv₀, map_ofNat, norm_inv]`. Evaluate the numerical expressions. Conclude with `tendsto_pow_atTop_nhds_zero_of_norm_lt_one h`. Establish `h2 : Tendsto (fun m : ℕ => (1 : FiniteAdeleRing (𝓞 F) F) ^ m) atTop (𝓝 1)`. Simplify using `only [one_pow]`.

Conclude with `tendsto_const_nhds`. Conclude with `h1.prodMk_nhds h2`.
-/
theorem tendsto_halfInf_pow (F : Type) [Field F] [NumberField F] :
    Tendsto (fun m : ℕ => (halfInf F).1 ^ m) atTop (𝓝 ((0, 1) : AF F)) := by
  have h1 : Tendsto (fun m : ℕ => (algebraMap F (Ainf F) 2⁻¹) ^ m) atTop (𝓝 0) := by
    refine tendsto_pi_nhds.2 fun v => ?_
    have h : ‖algebraMap F (Ainf F) 2⁻¹ v‖ < 1 := by
      rw [InfiniteAdeleRing.algebraMap_apply, InfinitePlace.Completion.norm_coe]
      change v (2⁻¹ : F) < 1
      rw [← InfinitePlace.norm_embedding_eq, map_inv₀, map_ofNat, norm_inv]
      norm_num
    exact tendsto_pow_atTop_nhds_zero_of_norm_lt_one h
  have h2 : Tendsto (fun m : ℕ => (1 : FiniteAdeleRing (𝓞 F) F) ^ m) atTop (𝓝 1) := by
    simp only [one_pow]
    exact tendsto_const_nhds
  exact h1.prodMk_nhds h2

/- English proof (translation)
Introduce `F E _ _ _ _ _ Ω hΩ`. Establish `: IsModuleTopology (AF F) (AF F ⊗[F] E)` using `⟨rfl⟩`. Establish `: IsTopologicalRing (AF F ⊗[F] E)` using `IsModuleTopology.isTopologicalRing (AF F) _`. Establish `: T2Space (AF F)` using `GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField _`. Take `⟨e⟩` from `GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)`.

Establish `: T2Space (AF F ⊗[F] E)` using `e.isEmbedding.t2Space`. Establish `h` using `GlobalTheory.AdelicMatrixLattice.discrete_tensor (F := F) (E := E) (AF F) (GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero F)`. Use `⟨finite_of_isCompact _ h hΩ, eventually_eq_zero _ h hΩ (ε := algebraMap (AF F) (AF F ⊗[F] E) (0, 1)) ?_ fun hu => ?_⟩` and prove the remaining obligations. Establish `hc : Continuous (algebraMap (AF F) (AF F ⊗[F] E))` using `IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AF F) (AF F ⊗[F] E))`. Use `(hc.tendsto _).comp (tendsto_halfInf_pow F)` as an intermediate fact.

Use `this.congr fun m => ?_` and prove the remaining obligations. Conclude with `map_pow (algebraMap (AF F) (AF F ⊗[F] E)) _ m`. Establish `h0 : algebraMap (AF F) (AF F ⊗[F] E) (0, 1) * algebraMap (AF F) (AF F ⊗[F] E) (1, 0) = 0`. Use `(map_mul (algebraMap (AF F) (AF F ⊗[F] E)) _ _).symm.trans ?_` and prove the remaining obligations. Use `(congrArg (algebraMap (AF F) (AF F ⊗[F] E)) ?_).trans (map_zero _)` and prove the remaining obligations.

Conclude with `Prod.ext (zero_mul _) (mul_zero _)`. Establish `h1` using `hu.mul_right_eq_zero.1 h0`. Establish `hinj : Function.Injective (algebraMap (AF F) (AF F ⊗[F] E))` using `Algebra.TensorProduct.includeLeft_injective (S := F) (algebraMap F E).injective`. Establish `h2 : ((1, 0) : AF F) = 0` using `hinj (h1.trans (map_zero _).symm)`. Take `⟨v⟩ : Nonempty (InfinitePlace F)` from `inferInstance`.

Establish `h3 : (1 : v.Completion) = 0` using `congrFun (congrArg Prod.fst h2) v`. Conclude with `one_ne_zero h3`.
-/
theorem finite_and_eventually_eq_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (Ω : Set (AF F ⊗[F] E)), IsCompact Ω → {x : E | inclR (F := F) (AF F) x ∈ Ω}.Finite ∧ ∃ m₀ : ℕ, ∀ m, m₀ ≤ m → ∀ ω ∈ Ω, ∀ x : E, inclR (F := F) (AF F) x = (halfE F E).1 ^ m * ω → x = 0 := by
  intro F E _ _ _ _ _ Ω hΩ
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField _
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  have : T2Space (AF F ⊗[F] E) := e.isEmbedding.t2Space
  have h := GlobalTheory.AdelicMatrixLattice.discrete_tensor (F := F) (E := E) (AF F)
    (GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero F)
  refine ⟨finite_of_isCompact _ h hΩ, eventually_eq_zero _ h hΩ
    (ε := algebraMap (AF F) (AF F ⊗[F] E) (0, 1)) ?_ fun hu => ?_⟩
  · have hc : Continuous (algebraMap (AF F) (AF F ⊗[F] E)) :=
      IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AF F) (AF F ⊗[F] E))
    have := (hc.tendsto _).comp (tendsto_halfInf_pow F)
    refine this.congr fun m => ?_
    exact map_pow (algebraMap (AF F) (AF F ⊗[F] E)) _ m
  · have h0 : algebraMap (AF F) (AF F ⊗[F] E) (0, 1) * algebraMap (AF F) (AF F ⊗[F] E) (1, 0) = 0 := by
      refine (map_mul (algebraMap (AF F) (AF F ⊗[F] E)) _ _).symm.trans ?_
      refine (congrArg (algebraMap (AF F) (AF F ⊗[F] E)) ?_).trans (map_zero _)
      exact Prod.ext (zero_mul _) (mul_zero _)
    have h1 := hu.mul_right_eq_zero.1 h0
    have hinj : Function.Injective (algebraMap (AF F) (AF F ⊗[F] E)) :=
      Algebra.TensorProduct.includeLeft_injective (S := F) (algebraMap F E).injective
    have h2 : ((1, 0) : AF F) = 0 := hinj (h1.trans (map_zero _).symm)
    obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
    have h3 : (1 : v.Completion) = 0 := congrFun (congrArg Prod.fst h2) v
    exact one_ne_zero h3

end GlobalTheory.Eis.Conv.Discr
