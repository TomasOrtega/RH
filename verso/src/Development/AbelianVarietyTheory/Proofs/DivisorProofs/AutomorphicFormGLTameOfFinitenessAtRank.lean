import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrowthOfTame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieGrowthOfFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraFinitenessAutomorphicGLOfEigen

noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology GlobalTheory.HCF

namespace GlobalTheory.AutGrowth.RankLocal

open GlobalTheory.AutGrowth.KilledFin GlobalTheory.AutGrowth.SmoothFinite

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

/- English proof (translation)
Use `haveI hW' : FiniteDimensional ℂ (GlobalTheory.Published.AutFin.coeffSpan ρ) := GlobalTheory.T.finiteDimensional_matrixCoefficientSpan _ W ρ`. Set `χ : Module.End ℂ (Sm E a) → ℂ` to `fun z => if hz : ∃ s : ℂ, ∀ φ : Sm E a, (∀ τ u, cap τ u φ = c τ u • φ) → z φ = s • φ then hz.choose else 0`. Establish `hsub : GlobalTheory.Published.AutFinGL.forms L ρ c ⊆ formsGL E a L (GlobalTheory.Published.AutFin.coeffSpan ρ) {χ} 1`. Introduce and unpack `φ ⟨h1, h2, h3, h4⟩`. Use `⟨h1, h2, h3, χ, rfl, ?_⟩` and prove the remaining obligations.

Introduce `zs hlen hzs`. Use `match zs, hlen with`. Consider the case `[z], _`. Establish `hz : z ∈ Zalg E a` using `hzs z (List.mem_singleton_self z)`. Establish `hex` using `GlobalTheory.T.center_acts_by_scalar_on_eigenforms E a c z hz`.

Establish `hχ : χ z = hex.choose` using `dif_pos hex`. Simplify using `only [List.foldr_cons, List.foldr_nil]`. Rewrite using `[hχ, hex.choose_spec φ h4, sub_self]`. Establish `hfin` using `h L hL (GlobalTheory.Published.AutFin.coeffSpan ρ) hW' {χ} (Set.finite_singleton χ) 1`. Conclude with `Submodule.finiteDimensional_of_le (Submodule.span_mono hsub)`.
-/
theorem finite_forms (h : ∀ (L' : Subgroup (GL (Fin a) (Af E))), IsOpen (L' : Set (GL (Fin a) (Af E))) →
      ∀ W' : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W' →
      ∀ X' : Set (Module.End ℂ (Sm E a) → ℂ), X'.Finite → ∀ N' : ℕ,
        FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.HCF.formsGL E a L' W' X' N')))
    (L : Subgroup (GL (Fin a) (Af E))) (hL : IsOpen (L : Set (GL (Fin a) (Af E))))
    (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (Kinf E a) W)
    (c : (E →+* ℂ) → ℂ → ℂ) :
    FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.Published.AutFinGL.forms L ρ c)) := by
  classical
  haveI hW' : FiniteDimensional ℂ (GlobalTheory.Published.AutFin.coeffSpan ρ) := GlobalTheory.T.finiteDimensional_matrixCoefficientSpan _ W ρ
  let χ : Module.End ℂ (Sm E a) → ℂ := fun z =>
    if hz : ∃ s : ℂ, ∀ φ : Sm E a, (∀ τ u, cap τ u φ = c τ u • φ) → z φ = s • φ then hz.choose else 0
  have hsub : GlobalTheory.Published.AutFinGL.forms L ρ c ⊆ formsGL E a L (GlobalTheory.Published.AutFin.coeffSpan ρ) {χ} 1 := by
    rintro φ ⟨h1, h2, h3, h4⟩
    refine ⟨h1, h2, h3, χ, rfl, ?_⟩
    intro zs hlen hzs
    match zs, hlen with
    | [z], _ =>
      have hz : z ∈ Zalg E a := hzs z (List.mem_singleton_self z)
      have hex := GlobalTheory.T.center_acts_by_scalar_on_eigenforms E a c z hz
      have hχ : χ z = hex.choose := dif_pos hex
      simp only [List.foldr_cons, List.foldr_nil]
      rw [hχ, hex.choose_spec φ h4, sub_self]
  have hfin := h L hL (GlobalTheory.Published.AutFin.coeffSpan ρ) hW' {χ} (Set.finite_singleton χ) 1
  exact Submodule.finiteDimensional_of_le (Submodule.span_mono hsub)

/- English proof (translation)
Use `haveI := hWf`. Establish `hF` using `finite_forms h L hL W (GlobalTheory.PRep.sub (cptRep E a) W hW) c`. Use `haveI := hF`. Establish `hmem : ∀ T ∈ N, ∀ w, T w ∈ GlobalTheory.Published.AutFinGL.forms L (GlobalTheory.PRep.sub (cptRep E a) W hW) c`. Introduce `T hT w`.

Establish `hm : (∀ k w, T (GlobalTheory.PRep.sub (cptRep E a) W hW k w) = cptRep E a k (T w)) ∧ ∀ w, T w ∈ tame E a ∧ (∀ γ g, (T w).1 (ratGL E a γ * g) = (T w).1 g) ∧ ∀ k ∈ L, finRep E a k (T w) = T w` using `hN hT`. Take `⟨heq, hall⟩` from `hm`. Take `⟨htame, hleft, hfix⟩` from `hall w`. Establish `hZ : ∀ z ∈ Zalg E a, ∃ s : ℂ, z ∘ₗ T = s • T`. Introduce `z hz`.

Proceed by induction on `hz using Algebra.adjoin_induction with`. Consider the case `mem x hx => obtain ⟨τ, u, rfl⟩ := hx`. Conclude with `⟨c τ u, hcap T hT τ u⟩`. Consider the case `algebraMap r => exact ⟨r, LinearMap.ext fun v => by simp⟩`. Consider the case `add x y _ _ hx hy`.

Take `⟨s, hs⟩` from `hx`. Take `⟨t, ht⟩` from `hy`. Conclude with `⟨s + t, by rw [LinearMap.add_comp, hs, ht, add_smul]⟩`. Consider the case `mul x y _ _ hx hy`. Take `⟨s, hs⟩` from `hx`.

Take `⟨t, ht⟩` from `hy`. Conclude with `⟨t * s, by rw [Module.End.mul_eq_comp, LinearMap.comp_assoc, ht, LinearMap.comp_smul, hs, smul_smul]⟩`. Use `⟨⟨hleft, ?_, ?_, ?_, ?_⟩, hfix, GlobalTheory.Published.AutFinGL.type_of_map _ T heq w, fun τ u => ?_⟩` and prove the remaining obligations. Conclude with `isOpen_stab_of_mem_nhds (finRep E a) (T w) (Filter.mem_of_superset (hL.mem_nhds L.one_mem) fun k hk => hfix k hk)`. Use `Submodule.finiteDimensional_of_le (S₂ := LinearMap.range T) (Submodule.span_le.2 ?_)` and prove the remaining obligations.

Introduce and unpack `_ ⟨k, rfl⟩`. Conclude with `⟨_, heq k w⟩`. Use `Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ {T w}) (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨z, hz, rfl⟩`. Take `⟨s, hs⟩` from `hZ z hz`.

Establish `e : z (T w) = s • T w` using `LinearMap.congr_fun hs w`. Use `show z (T w) ∈ _`. Rewrite using `[e]`. Conclude with `Submodule.smul_mem _ s (Submodule.mem_span_singleton_self _)`. Conclude with `growth_of_tame htame`.

Conclude with `LinearMap.congr_fun (hcap T hT τ u) w`. Set `Φ : N →ₗ[ℂ] (W →ₗ[ℂ] Submodule.span ℂ (GlobalTheory.Published.AutFinGL.forms L (GlobalTheory.PRep.sub (cptRep E a) W hW) c))` to `{ toFun := fun T => LinearMap.codRestrict _ T.1 fun w => Submodule.subset_span (hmem T.1 T.2 w) map_add' := fun T T' => LinearMap.ext fun w => rfl map_smul' := fun r T => LinearMap.ext fun w => rfl }`. Establish `hinj : Function.Injective Φ` using `fun T T' h => Subtype.ext (LinearMap.ext fun w => congrArg Subtype.val (LinearMap.congr_fun h w))`. Conclude with `Module.Finite.of_injective Φ hinj`.
-/
theorem finiteDimensional_capEigen_maps_rank (h : ∀ (L' : Subgroup (GL (Fin a) (Af E))), IsOpen (L' : Set (GL (Fin a) (Af E))) →
      ∀ W' : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W' →
      ∀ X' : Set (Module.End ℂ (Sm E a) → ℂ), X'.Finite → ∀ N' : ℕ,
        FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.HCF.formsGL E a L' W' X' N')))
    (L : Subgroup (GL (Fin a) (Af E))) (hL : IsOpen (L : Set (GL (Fin a) (Af E))))
    (W : Submodule ℂ (Sm E a)) (hW : ∀ k, ∀ w ∈ W, cptRep E a k w ∈ W) (hWf : FiniteDimensional ℂ W)
    (c : (E →+* ℂ) → ℂ → ℂ) (N : Submodule ℂ (W →ₗ[ℂ] Sm E a)) (hN : N ≤ maps L W hW)
    (hcap : ∀ T ∈ N, ∀ τ u, cap τ u ∘ₗ T = c τ u • T) : FiniteDimensional ℂ N := by
  haveI := hWf
  have hF := finite_forms h L hL W (GlobalTheory.PRep.sub (cptRep E a) W hW) c
  haveI := hF
  have hmem : ∀ T ∈ N, ∀ w, T w ∈ GlobalTheory.Published.AutFinGL.forms L (GlobalTheory.PRep.sub (cptRep E a) W hW) c := by
    intro T hT w
    have hm : (∀ k w, T (GlobalTheory.PRep.sub (cptRep E a) W hW k w) = cptRep E a k (T w)) ∧
        ∀ w, T w ∈ tame E a ∧ (∀ γ g, (T w).1 (ratGL E a γ * g) = (T w).1 g) ∧
          ∀ k ∈ L, finRep E a k (T w) = T w := hN hT
    obtain ⟨heq, hall⟩ := hm
    obtain ⟨htame, hleft, hfix⟩ := hall w
    have hZ : ∀ z ∈ Zalg E a, ∃ s : ℂ, z ∘ₗ T = s • T := by
      intro z hz
      induction hz using Algebra.adjoin_induction with
      | mem x hx => obtain ⟨τ, u, rfl⟩ := hx; exact ⟨c τ u, hcap T hT τ u⟩
      | algebraMap r => exact ⟨r, LinearMap.ext fun v => by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨s, hs⟩ := hx
        obtain ⟨t, ht⟩ := hy
        exact ⟨s + t, by rw [LinearMap.add_comp, hs, ht, add_smul]⟩
      | mul x y _ _ hx hy =>
        obtain ⟨s, hs⟩ := hx
        obtain ⟨t, ht⟩ := hy
        exact ⟨t * s, by rw [Module.End.mul_eq_comp, LinearMap.comp_assoc, ht, LinearMap.comp_smul, hs, smul_smul]⟩
    refine ⟨⟨hleft, ?_, ?_, ?_, ?_⟩, hfix, GlobalTheory.Published.AutFinGL.type_of_map _ T heq w, fun τ u => ?_⟩
    · exact isOpen_stab_of_mem_nhds (finRep E a) (T w)
        (Filter.mem_of_superset (hL.mem_nhds L.one_mem) fun k hk => hfix k hk)
    · refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range T) (Submodule.span_le.2 ?_)
      rintro _ ⟨k, rfl⟩
      exact ⟨_, heq k w⟩
    · refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ {T w}) (Submodule.span_le.2 ?_)
      rintro _ ⟨z, hz, rfl⟩
      obtain ⟨s, hs⟩ := hZ z hz
      have e : z (T w) = s • T w := LinearMap.congr_fun hs w
      show z (T w) ∈ _
      rw [e]
      exact Submodule.smul_mem _ s (Submodule.mem_span_singleton_self _)
    · exact growth_of_tame htame
    · exact LinearMap.congr_fun (hcap T hT τ u) w
  let Φ : N →ₗ[ℂ] (W →ₗ[ℂ] Submodule.span ℂ (GlobalTheory.Published.AutFinGL.forms L (GlobalTheory.PRep.sub (cptRep E a) W hW) c)) :=
    { toFun := fun T => LinearMap.codRestrict _ T.1 fun w => Submodule.subset_span (hmem T.1 T.2 w)
      map_add' := fun T T' => LinearMap.ext fun w => rfl
      map_smul' := fun r T => LinearMap.ext fun w => rfl }
  have hinj : Function.Injective Φ := fun T T' h =>
    Subtype.ext (LinearMap.ext fun w => congrArg Subtype.val (LinearMap.congr_fun h w))
  exact Module.Finite.of_injective Φ hinj

/- English proof (translation)
Establish `hcap : ∀ (τ : E →+* ℂ) (u : ℂ), cap (a` using `a) τ u ∈ Zalg E a := fun τ u => Algebra.subset_adjoin ⟨τ, u, rfl⟩`. Set `S : Set (Module.End ℂ (mapsJ φ L))` to `{s | ∃ τ u, s = postZ φ L (cap τ u) (hcap τ u)}`. Use `GlobalTheory.T.finiteDimensional_of_commuting_finiteAlgebra_jointEigen (mapsJ φ L) S ?_ ?_ ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨τ, u, rfl⟩ _ ⟨τ', u', rfl⟩`. Use `LinearMap.ext fun T => Subtype.ext (LinearMap.ext fun w => ?_)` and prove the remaining obligations.

Use `show cap τ u (cap τ' u' (T.1 w)) = cap τ' u' (cap τ u (T.1 w))`. Rewrite using `[← Module.End.mul_apply, (Zalg_commute (hcap τ u) (hcap τ' u')).eq, Module.End.mul_apply]`. Set `ev : Zalg E a →ₗ[ℂ] Sm E a` to `(LinearMap.applyₗ φ).comp (Zalg E a).val.toLinearMap`. Establish `hker : LinearMap.ker ev ≤ LinearMap.ker (postZAlg φ L).toLinearMap`. Introduce `z hz`.

Rewrite `hz`, the goal using `[LinearMap.mem_ker]`. Use `LinearMap.ext fun T => Subtype.ext (LinearMap.ext fun w => ?_)` and prove the remaining obligations. Establish `hT : T.1 ∈ maps L (spanK E a φ) (spanK_stable φ) ∧ ∀ z ∈ Zalg E a, z φ = 0 → ∀ w, z (T.1 w) = 0` using `T.2`. Conclude with `hT.2 z.1 z.2 hz w`. Establish `hev : FiniteDimensional ℂ (LinearMap.range ev)`.

Establish `h1 : LinearMap.range ev ≤ Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a)`. Introduce and unpack `_ ⟨z, rfl⟩`. Conclude with `Submodule.subset_span ⟨z.1, z.2, rfl⟩`. Use `haveI := hφ.zfin`. Conclude with `Submodule.finiteDimensional_of_le h1`.

Use `fd_adjoin_of_ker_le (mapsJ φ L) (Zalg E a) (Sm E a) (postZAlg φ L) ev hev hker S ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨τ, u, rfl⟩`. Conclude with `⟨⟨cap τ u, hcap τ u⟩, rfl⟩`. Introduce `c`. Set `J` to `⨅ s ∈ S, LinearMap.ker (s - algebraMap ℂ (Module.End ℂ (mapsJ φ L)) (c s))`.

Set `N : Submodule ℂ (spanK E a φ →ₗ[ℂ] Sm E a)` to `J.map (mapsJ φ L).subtype`. Establish `hNle : N ≤ maps L (spanK E a φ) (spanK_stable φ)`. Introduce and unpack `_ ⟨T, _, rfl⟩`. Establish `hT : T.1 ∈ maps L (spanK E a φ) (spanK_stable φ) ∧ ∀ z ∈ Zalg E a, z φ = 0 → ∀ w, z (T.1 w) = 0` using `T.2`. Conclude with `hT.1`.

Establish `hNe : ∀ T ∈ N, ∀ (τ : E →+* ℂ) (u : ℂ), cap τ u ∘ₗ T = c (postZ φ L (cap τ u) (hcap τ u)) • T`. Introduce and unpack `_ ⟨T, hT, rfl⟩ τ u`. Establish `hT' : T ∈ ⨅ s ∈ S, LinearMap.ker (s - algebraMap ℂ (Module.End ℂ (mapsJ φ L)) (c s))` using `hT`. Establish `h₀` using `(Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hT' (postZ φ L (cap τ u) (hcap τ u))) ⟨τ, u, rfl⟩`. Rewrite `h₀` using `[LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, Module.algebraMap_end_apply]`.

Conclude with `congrArg Subtype.val h₀`. Establish `hN : FiniteDimensional ℂ N` using `finiteDimensional_capEigen_maps_rank h L hL (spanK E a φ) (spanK_stable φ) hφ.kfin (fun τ u => c (postZ φ L (cap τ u) (hcap τ u))) N hNle hNe`. Conclude with `LinearEquiv.finiteDimensional (Submodule.equivMapOfInjective (mapsJ φ L).subtype Subtype.val_injective J).symm`.
-/
theorem finiteDimensional_mapsJ_rank (h : ∀ (L' : Subgroup (GL (Fin a) (Af E))), IsOpen (L' : Set (GL (Fin a) (Af E))) →
      ∀ W' : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W' →
      ∀ X' : Set (Module.End ℂ (Sm E a) → ℂ), X'.Finite → ∀ N' : ℕ,
        FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.HCF.formsGL E a L' W' X' N')))
    (φ : Sm E a) (hφ : IsAutForm φ) (L : Subgroup (GL (Fin a) (Af E)))
    (hL : IsOpen (L : Set (GL (Fin a) (Af E)))) : FiniteDimensional ℂ (mapsJ φ L) := by
  have hcap : ∀ (τ : E →+* ℂ) (u : ℂ), cap (a := a) τ u ∈ Zalg E a := fun τ u =>
    Algebra.subset_adjoin ⟨τ, u, rfl⟩
  let S : Set (Module.End ℂ (mapsJ φ L)) := {s | ∃ τ u, s = postZ φ L (cap τ u) (hcap τ u)}
  refine GlobalTheory.T.finiteDimensional_of_commuting_finiteAlgebra_jointEigen (mapsJ φ L) S ?_ ?_ ?_
  · rintro _ ⟨τ, u, rfl⟩ _ ⟨τ', u', rfl⟩
    refine LinearMap.ext fun T => Subtype.ext (LinearMap.ext fun w => ?_)
    show cap τ u (cap τ' u' (T.1 w)) = cap τ' u' (cap τ u (T.1 w))
    rw [← Module.End.mul_apply, (Zalg_commute (hcap τ u) (hcap τ' u')).eq, Module.End.mul_apply]
  · let ev : Zalg E a →ₗ[ℂ] Sm E a := (LinearMap.applyₗ φ).comp (Zalg E a).val.toLinearMap
    have hker : LinearMap.ker ev ≤ LinearMap.ker (postZAlg φ L).toLinearMap := by
      intro z hz
      rw [LinearMap.mem_ker] at hz ⊢
      refine LinearMap.ext fun T => Subtype.ext (LinearMap.ext fun w => ?_)
      have hT : T.1 ∈ maps L (spanK E a φ) (spanK_stable φ) ∧
          ∀ z ∈ Zalg E a, z φ = 0 → ∀ w, z (T.1 w) = 0 := T.2
      exact hT.2 z.1 z.2 hz w
    have hev : FiniteDimensional ℂ (LinearMap.range ev) := by
      have h1 : LinearMap.range ev ≤
          Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a) := by
        rintro _ ⟨z, rfl⟩
        exact Submodule.subset_span ⟨z.1, z.2, rfl⟩
      haveI := hφ.zfin
      exact Submodule.finiteDimensional_of_le h1
    refine fd_adjoin_of_ker_le (mapsJ φ L) (Zalg E a) (Sm E a) (postZAlg φ L) ev hev hker S ?_
    rintro _ ⟨τ, u, rfl⟩
    exact ⟨⟨cap τ u, hcap τ u⟩, rfl⟩
  · intro c
    let J := ⨅ s ∈ S, LinearMap.ker (s - algebraMap ℂ (Module.End ℂ (mapsJ φ L)) (c s))
    let N : Submodule ℂ (spanK E a φ →ₗ[ℂ] Sm E a) := J.map (mapsJ φ L).subtype
    have hNle : N ≤ maps L (spanK E a φ) (spanK_stable φ) := by
      rintro _ ⟨T, _, rfl⟩
      have hT : T.1 ∈ maps L (spanK E a φ) (spanK_stable φ) ∧
          ∀ z ∈ Zalg E a, z φ = 0 → ∀ w, z (T.1 w) = 0 := T.2
      exact hT.1
    have hNe : ∀ T ∈ N, ∀ (τ : E →+* ℂ) (u : ℂ),
        cap τ u ∘ₗ T = c (postZ φ L (cap τ u) (hcap τ u)) • T := by
      rintro _ ⟨T, hT, rfl⟩ τ u
      have hT' : T ∈ ⨅ s ∈ S, LinearMap.ker (s - algebraMap ℂ (Module.End ℂ (mapsJ φ L)) (c s)) := hT
      have h₀ := (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hT' (postZ φ L (cap τ u) (hcap τ u))) ⟨τ, u, rfl⟩
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, Module.algebraMap_end_apply] at h₀
      exact congrArg Subtype.val h₀
    have hN : FiniteDimensional ℂ N :=
      finiteDimensional_capEigen_maps_rank h L hL (spanK E a φ) (spanK_stable φ) hφ.kfin
        (fun τ u => c (postZ φ L (cap τ u) (hcap τ u))) N hNle hNe
    exact LinearEquiv.finiteDimensional
      (Submodule.equivMapOfInjective (mapsJ φ L).subtype Subtype.val_injective J).symm

/- English proof (translation)
Set `w0 : spanK E a φ` to `⟨φ, self_mem_spanK φ⟩`. Use `haveI := finiteDimensional_mapsJ_rank h φ hφ (stabL φ) hφ.level`. Use `⟨(mapsJ φ (stabL φ)).map (LinearMap.applyₗ w0), inferInstance, ?_, fun α hα hK => ⟨GlobalTheory.T.realLieSmoothing_mem_smoothAdelicFunctions E a ν α hα φ.1 φ.2, smoothMap ν hα _, smoothMap_mem ν hα hK hφ, rfl⟩⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨T, hT, rfl⟩`. Conclude with `(hT.1.2 w0).1`.
-/
theorem exists_finite_space_rank (h : ∀ (L' : Subgroup (GL (Fin a) (Af E))), IsOpen (L' : Set (GL (Fin a) (Af E))) →
      ∀ W' : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W' →
      ∀ X' : Set (Module.End ℂ (Sm E a) → ℂ), X'.Finite → ∀ N' : ℕ,
        FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.HCF.formsGL E a L' W' X' N')))
    (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] (φ : Sm E a) (hφ : IsAutForm φ) :
    ∃ V : Submodule ℂ (Sm E a), FiniteDimensional ℂ V ∧ V ≤ tame E a ∧ ∀ α, IsTest (invSet E a) α → KInv α →
      ∃ h : smoothing ν α φ.1 ∈ Sm E a, (⟨smoothing ν α φ.1, h⟩ : Sm E a) ∈ V := by
  let w0 : spanK E a φ := ⟨φ, self_mem_spanK φ⟩
  haveI := finiteDimensional_mapsJ_rank h φ hφ (stabL φ) hφ.level
  refine ⟨(mapsJ φ (stabL φ)).map (LinearMap.applyₗ w0), inferInstance, ?_, fun α hα hK =>
    ⟨GlobalTheory.T.realLieSmoothing_mem_smoothAdelicFunctions E a ν α hα φ.1 φ.2, smoothMap ν hα _, smoothMap_mem ν hα hK hφ, rfl⟩⟩
  rintro _ ⟨T, hT, rfl⟩
  exact (hT.1.2 w0).1

/- English proof (translation)
Introduce `E _ _ _ a hfin φ hφ`. Set `ν : Measure (Lie E a)` to `Measure.addHaar`. Take `⟨α, hα, hlim⟩` from `GlobalTheory.T.exists_conjInvariant_approxIdentity_realLieSmoothing E a ν`. Take `⟨V, hVf, hVt, hV⟩` from `exists_finite_space_rank hfin ν φ hφ`. Set `V' : Submodule ℂ (GA E a → ℂ)` to `V.map (Sm E a).subtype`.

Establish `hc : IsClosed (V' : Set (GA E a → ℂ))` using `Submodule.closed_of_finiteDimensional V'`. Establish `hmem : ∀ n, smoothing ν (α n) φ.1 ∈ V'` using `fun n => by`. Take `⟨h, hv⟩` from `hV (α n) (hα n).1 (hα n).2`. Conclude with `⟨_, hv, rfl⟩`. Establish `hφ' : φ.1 ∈ V'` using `hc.mem_of_tendsto (tendsto_pi_nhds.2 fun g => hlim φ.1 φ.2 g) (Eventually.of_forall hmem)`.

Take `⟨ψ, hψ, e⟩` from `hφ'`. Establish `e' : ψ = φ` using `Subtype.ext e`. Conclude with `hVt (e' ▸ hψ)`.
-/
theorem tame_of_autForm_rank : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ),
    (∀ (L' : Subgroup (GL (Fin n) (Af E))), IsOpen (L' : Set (GL (Fin n) (Af E))) →
      ∀ W' : Submodule ℂ (Kinf E n → ℂ), FiniteDimensional ℂ W' →
      ∀ X' : Set (Module.End ℂ (Sm E n) → ℂ), X'.Finite → ∀ N' : ℕ,
        FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.HCF.formsGL E n L' W' X' N'))) →
    ∀ φ : Sm E n, IsAutForm φ → φ ∈ GlobalTheory.AutGrowth.tame E n := by
  intro E _ _ _ a hfin φ hφ
  let ν : Measure (Lie E a) := Measure.addHaar
  obtain ⟨α, hα, hlim⟩ := GlobalTheory.T.exists_conjInvariant_approxIdentity_realLieSmoothing E a ν
  obtain ⟨V, hVf, hVt, hV⟩ := exists_finite_space_rank hfin ν φ hφ
  let V' : Submodule ℂ (GA E a → ℂ) := V.map (Sm E a).subtype
  have hc : IsClosed (V' : Set (GA E a → ℂ)) := Submodule.closed_of_finiteDimensional V'
  have hmem : ∀ n, smoothing ν (α n) φ.1 ∈ V' := fun n => by
    obtain ⟨h, hv⟩ := hV (α n) (hα n).1 (hα n).2
    exact ⟨_, hv, rfl⟩
  have hφ' : φ.1 ∈ V' :=
    hc.mem_of_tendsto (tendsto_pi_nhds.2 fun g => hlim φ.1 φ.2 g) (Eventually.of_forall hmem)
  obtain ⟨ψ, hψ, e⟩ := hφ'
  have e' : ψ = φ := Subtype.ext e
  exact hVt (e' ▸ hψ)

end GlobalTheory.AutGrowth.RankLocal

end
