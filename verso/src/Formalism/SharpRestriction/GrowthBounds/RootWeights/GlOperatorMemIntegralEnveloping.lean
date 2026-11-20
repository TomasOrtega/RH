import Formalism.SharpRestriction.GrowthBounds.RootWeights.ExistsHighestCoordinateFunctional

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section hw

variable {n : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {V : Type*} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]

/- English proof (translation)
Rewrite using `[UZmon.eq_1]`. Apply `Submonoid.subset_closure` to reduce the goal to its premises. Simplify using `only [UZgens.eq_1, Set.mem_setOf_eq]`. Distinguish the cases in `hab : a = b`. Substitute `hab right` using the available equality.

Conclude with `⟨a, 1, by simp [binomE.eq_1]⟩`. Use `left`. Conclude with `⟨a, b, 1, hab, by simp [divPowE.eq_1]⟩`.
-/
theorem gl_operator_mem_integral_enveloping (E : GLOps n (KK O) V) (a b : Fin n) : E a b ∈ UZmon E := by
  rw [UZmon.eq_1]
  apply Submonoid.subset_closure
  simp only [UZgens.eq_1, Set.mem_setOf_eq]
  by_cases hab : a = b
  · subst hab
    right
    exact ⟨a, 1, by simp [binomE.eq_1]⟩
  · left
    exact ⟨a, b, 1, hab, by simp [divPowE.eq_1]⟩

/- English proof (translation)
Rewrite using `[Umon.eq_1, Submonoid.closure_le]`. Introduce and unpack `_ ⟨⟨a, b⟩, rfl⟩`. Conclude with `gl_operator_mem_integral_enveloping E a b`.
-/
theorem enveloping_le_integral_enveloping (E : GLOps n (KK O) V) : Umon E ≤ UZmon E := by
  rw [Umon.eq_1, Submonoid.closure_le]
  rintro _ ⟨⟨a, b⟩, rfl⟩
  exact gl_operator_mem_integral_enveloping E a b

/- English proof (translation)
Rewrite using `[Nabla.eq_1, Set.mem_setOf_eq]`. Prove the components needed by the constructor for the conclusion. Introduce `H u hu`. Take `⟨c, hc⟩` from `H u hu`. Use `⟨c, ?_⟩` and prove the remaining obligations.

Establish `h` using `h2 _ hc`. Rewrite `h` using `[map_sub, map_smul, h1, smul_eq_mul, mul_one, sub_eq_zero]`. Conclude with `h`. Introduce `H u hu`. Take `⟨c, hc⟩` from `H u hu`.

Use `⟨c, ?_⟩` and prove the remaining obligations. Establish `h` using `h3 (u x)`. Rewrite `h` using `[hc]`. Conclude with `h`.
-/
theorem mem_nabla_iff_coordinate_integral {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V} {xi : V →ₗ[KK O] KK O} (h1 : xi v = 1)
    (h2 : ∀ w ∈ otherWts E lam, xi w = 0) (h3 : ∀ x, x - xi x • v ∈ otherWts E lam) (x : V) :
    x ∈ Nabla (O := O) E lam v ↔ ∀ u ∈ UZmon E, ∃ c : O, xi (u x) = algebraMap O (KK O) c := by
  rw [Nabla.eq_1, Set.mem_setOf_eq]
  constructor
  · intro H u hu
    obtain ⟨c, hc⟩ := H u hu
    refine ⟨c, ?_⟩
    have h := h2 _ hc
    rw [map_sub, map_smul, h1, smul_eq_mul, mul_one, sub_eq_zero] at h
    exact h
  · intro H u hu
    obtain ⟨c, hc⟩ := H u hu
    refine ⟨c, ?_⟩
    have h := h3 (u x)
    rw [hc] at h
    exact h

/- English proof (translation)
Set `W : Submodule (KK O) V` to `⨅ u : UZmon E, LinearMap.ker (xi ∘ₗ (u : Module.End (KK O) V))`. Establish `hmemW : ∀ y, y ∈ W ↔ ∀ u ∈ UZmon E, xi (u y) = 0`. Introduce `y`. Rewrite using `[Submodule.mem_iInf]`. Prove the components needed by the constructor for the conclusion.

Introduce `h u hu`. Establish `h'` using `h ⟨u, hu⟩`. Rewrite `h'` using `[LinearMap.mem_ker, LinearMap.comp_apply]`. Then use the resulting hypothesis. Introduce `h u`. Rewrite using `[LinearMap.mem_ker, LinearMap.comp_apply]`.

Conclude with `h u.1 u.2`. Establish `hxW : x ∈ W` using `(hmemW x).2 hx`. Establish `hWst : ∀ a b, ∀ y ∈ W, E a b y ∈ W`. Introduce `a b y hy`. Rewrite `hy`, the goal using `[hmemW]`.

Introduce `u hu`. Establish `h'` using `hy (u * E a b) (Submonoid.mul_mem _ hu (gl_operator_mem_integral_enveloping E a b))`. Rewrite `h'` using `[Module.End.mul_apply]`. Then use the resulting hypothesis. Establish `hvW : v ∉ W`. Introduce `h`.

Establish `h'` using `(hmemW v).1 h 1 (Submonoid.one_mem _)`. Rewrite `h'` using `[Module.End.one_apply, h1]`. Conclude with `one_ne_zero h'`. Take `⟨W', hC, hW'st⟩` from `hCR W hWst`. Establish `hv2 : v ∈ W ⊔ W'`.

Rewrite using `[hC.sup_eq_top]`. Conclude with `Submodule.mem_top`. Take `⟨w, hw, w', hw', hvs⟩` from `Submodule.mem_sup.mp hv2`. Establish `hv` using `hI.2.2.1`. Establish `hvw : ∀ a, E a a v = (lam a : KK O) • v`.

Introduce `a`. Establish `h1'` using `(Submodule.mem_iInf _).mp hv.2.1 a`. Rewrite `h1'` using `[LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]`. Simplify using `using h1'`. Establish `hww : w ∈ weightSp E lam`.

Unfold `weightSp`. Use `(Submodule.mem_iInf _).mpr fun a => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]`. Establish `hd : E a a w - (lam a : KK O) • w ∈ W` using `sub_mem (hWst a a w hw) (Submodule.smul_mem W _ hw)`. Establish `hd' : E a a w' - (lam a : KK O) • w' ∈ W'` using `sub_mem (hW'st a a w' hw') (Submodule.smul_mem W' _ hw')`.

Establish `hsum : (E a a w - (lam a : KK O) • w) + (E a a w' - (lam a : KK O) • w') = 0`. Establish `h2` using `hvw a`. Rewrite `h2` using `[← hvs, map_add, smul_add]`. Rewrite using `[sub_add_sub_comm, h2, sub_self]`. Establish `hneg : E a a w - (lam a : KK O) • w ∈ W'`.

Rewrite using `[eq_neg_of_add_eq_zero_left hsum]`. Conclude with `W'.neg_mem hd'`. Conclude with `(Submodule.disjoint_def.mp hC.disjoint) _ hd hneg`. Establish `hmem` using `top_le_line_sup_higher_weights hI (Submodule.mem_top : w ∈ (⊤ : Submodule (KK O) V))`. Take `⟨y, hy, z, hz, hyz⟩` from `Submodule.mem_sup.mp hmem`.

Take `⟨c, rfl⟩` from `Submodule.mem_span_singleton.mp hy`. Establish `hzw : z ∈ weightSp E lam`. Establish `e : z = w - c • v`. Rewrite using `[← hyz]`. Normalize the expressions using the abelian group laws.

Rewrite using `[e]`. Conclude with `sub_mem hww (Submodule.smul_mem _ c hv.2.1)`. Establish `hz0 : z = 0` using `weight_support_sum_eq_zero E (fun nu => weightHeightAscending lam < weightHeightAscending nu) hzw hz (lt_irrefl _)`. Establish `hwc : w = c • v`. Rewrite using `[← hyz, hz0, add_zero]`.

Establish `hc0 : c = 0`. Assume the negation of the conclusion as `hc`. Apply `hvW` to reduce the goal to its premises. Establish `e : v = c⁻¹ • w`. Rewrite using `[hwc, smul_smul, inv_mul_cancel₀ hc, one_smul]`.

Rewrite using `[e]`. Conclude with `Submodule.smul_mem W _ hw`. Establish `hvW' : v ∈ W'`. Rewrite `hvs` using `[hwc, hc0, zero_smul, zero_add]`. Rewrite using `[← hvs]`.

Conclude with `hw'`. Establish `htop` using `irreducible_stable_contains_eq_top hI hW'st hvW'`. Establish `hxW' : x ∈ W'`. Rewrite using `[htop]`. Conclude with `Submodule.mem_top`.

Conclude with `(Submodule.disjoint_def.mp hC.disjoint) x hxW hxW'`.
-/
theorem enveloping_coordinate_separates [NeZero n] [CharZero (KK O)] {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V}
    (hI : IsIrrHW E lam v)
    (hCR : ∀ W : Submodule (KK O) V, (∀ a b, ∀ x ∈ W, E a b x ∈ W) →
      ∃ W' : Submodule (KK O) V, IsCompl W W' ∧ ∀ a b, ∀ x ∈ W', E a b x ∈ W')
    {xi : V →ₗ[KK O] KK O} (h1 : xi v = 1) {x : V} (hx : ∀ u ∈ UZmon E, xi (u x) = 0) : x = 0 := by
  classical

  let W : Submodule (KK O) V := ⨅ u : UZmon E, LinearMap.ker (xi ∘ₗ (u : Module.End (KK O) V))
  have hmemW : ∀ y, y ∈ W ↔ ∀ u ∈ UZmon E, xi (u y) = 0 := by
    intro y
    rw [Submodule.mem_iInf]
    constructor
    · intro h u hu
      have h' := h ⟨u, hu⟩
      rwa [LinearMap.mem_ker, LinearMap.comp_apply] at h'
    · intro h u
      rw [LinearMap.mem_ker, LinearMap.comp_apply]
      exact h u.1 u.2
  have hxW : x ∈ W := (hmemW x).2 hx
  have hWst : ∀ a b, ∀ y ∈ W, E a b y ∈ W := by
    intro a b y hy
    rw [hmemW] at hy ⊢
    intro u hu
    have h' := hy (u * E a b) (Submonoid.mul_mem _ hu (gl_operator_mem_integral_enveloping E a b))
    rwa [Module.End.mul_apply] at h'
  have hvW : v ∉ W := by
    intro h
    have h' := (hmemW v).1 h 1 (Submonoid.one_mem _)
    rw [Module.End.one_apply, h1] at h'
    exact one_ne_zero h'
  obtain ⟨W', hC, hW'st⟩ := hCR W hWst
  have hv2 : v ∈ W ⊔ W' := by
    rw [hC.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨w, hw, w', hw', hvs⟩ := Submodule.mem_sup.mp hv2
  have hv := hI.2.2.1
  have hvw : ∀ a, E a a v = (lam a : KK O) • v := by
    intro a
    have h1' := (Submodule.mem_iInf _).mp hv.2.1 a
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h1'
    simpa using h1'

  have hww : w ∈ weightSp E lam := by
    unfold weightSp
    refine (Submodule.mem_iInf _).mpr fun a => ?_
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
    have hd : E a a w - (lam a : KK O) • w ∈ W := sub_mem (hWst a a w hw) (Submodule.smul_mem W _ hw)
    have hd' : E a a w' - (lam a : KK O) • w' ∈ W' :=
      sub_mem (hW'st a a w' hw') (Submodule.smul_mem W' _ hw')
    have hsum : (E a a w - (lam a : KK O) • w) + (E a a w' - (lam a : KK O) • w') = 0 := by
      have h2 := hvw a
      rw [← hvs, map_add, smul_add] at h2
      rw [sub_add_sub_comm, h2, sub_self]
    have hneg : E a a w - (lam a : KK O) • w ∈ W' := by
      rw [eq_neg_of_add_eq_zero_left hsum]
      exact W'.neg_mem hd'
    exact (Submodule.disjoint_def.mp hC.disjoint) _ hd hneg

  have hmem := top_le_line_sup_higher_weights hI (Submodule.mem_top : w ∈ (⊤ : Submodule (KK O) V))
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hmem
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
  have hzw : z ∈ weightSp E lam := by
    have e : z = w - c • v := by
      rw [← hyz]
      abel
    rw [e]
    exact sub_mem hww (Submodule.smul_mem _ c hv.2.1)
  have hz0 : z = 0 :=
    weight_support_sum_eq_zero E (fun nu => weightHeightAscending lam < weightHeightAscending nu) hzw hz (lt_irrefl _)
  have hwc : w = c • v := by
    rw [← hyz, hz0, add_zero]
  have hc0 : c = 0 := by
    by_contra hc
    apply hvW
    have e : v = c⁻¹ • w := by
      rw [hwc, smul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [e]
    exact Submodule.smul_mem W _ hw
  have hvW' : v ∈ W' := by
    rw [hwc, hc0, zero_smul, zero_add] at hvs
    rw [← hvs]
    exact hw'
  have htop := irreducible_stable_contains_eq_top hI hW'st hvW'
  have hxW' : x ∈ W' := by
    rw [htop]
    exact Submodule.mem_top
  exact (Submodule.disjoint_def.mp hC.disjoint) x hxW hxW'

/- English proof (translation)
Take `⟨b, hbXi, hbspan, hbli⟩` from `exists_linearIndependent (KK O) Xi`. Establish `hbfin : b.Finite` using `hbli.setFinite`. Use `haveI : Fintype b := hbfin.fintype`. Establish `hbsep : ∀ w : W, (∀ ξ ∈ b, ξ w = 0) → w = 0`. Introduce `w hw`.

Apply `hsep` to reduce the goal to its premises. Introduce `ξ hξ`. Establish `hle' : Submodule.span (KK O) b ≤ LinearMap.ker (Module.Dual.eval (KK O) W w)`. Rewrite using `[Submodule.span_le]`. Introduce `η hη`.

Simplify using `only [SetLike.mem_coe, LinearMap.mem_ker, Module.Dual.eval_apply]`. Conclude with `hw η hη`. Establish `hmem : ξ ∈ Submodule.span (KK O) b`. Rewrite using `[hbspan]`. Conclude with `Submodule.subset_span hξ`.

Establish `h` using `hle' hmem`. Simplify using `using h`. Set `Φ : W →ₗ[O] (b → KK O)` to `LinearMap.pi fun ξ => (ξ.1).restrictScalars O`. Establish `hΦ : Function.Injective Φ`. Use `(injective_iff_map_eq_zero Φ).2 ?_` and prove the remaining obligations.

Introduce `w hw`. Apply `hbsep` to reduce the goal to its premises. Introduce `ξ hξ`. Establish `h` using `congrFun hw ⟨ξ, hξ⟩`. Simplify `h` using `[Φ]`.

Set `g : (b → O) →ₗ[O] (b → KK O)` to `LinearMap.pi fun i => (Algebra.linearMap O (KK O)).comp (LinearMap.proj i)`. Establish `hle : N.map Φ ≤ LinearMap.range g`. Introduce and unpack `_ ⟨w, hw, rfl⟩`. Use `choose c hc using fun ξ : b => hint ξ.1 (hbXi ξ.2) w hw`. Rewrite using `[LinearMap.mem_range]`.

Use `⟨c, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `ξ`. Simplify using `[g, Φ, hc]`. Apply `Submodule.fg_of_fg_map_injective Φ hΦ` to reduce the goal to its premises. Establish `hQ : ((N.map Φ).comap g).FG` using `IsNoetherian.noetherian _`.

Establish `h` using `hQ.map g`. Rewrite `h` using `[Submodule.map_comap_eq, inf_eq_right.mpr hle]`. Then use the resulting hypothesis.
-/
theorem lattice_fg_of_integral_functionals {W : Type*} [AddCommGroup W] [Module (KK O) W] [Module O W] [IsScalarTower O (KK O) W]
    [FiniteDimensional (KK O) W] (N : Submodule O W) (Xi : Set (W →ₗ[KK O] KK O))
    (hsep : ∀ w, (∀ ξ ∈ Xi, ξ w = 0) → w = 0)
    (hint : ∀ ξ ∈ Xi, ∀ w ∈ N, ∃ c : O, ξ w = algebraMap O (KK O) c) : N.FG := by
  classical
  obtain ⟨b, hbXi, hbspan, hbli⟩ := exists_linearIndependent (KK O) Xi
  have hbfin : b.Finite := hbli.setFinite
  haveI : Fintype b := hbfin.fintype
  have hbsep : ∀ w : W, (∀ ξ ∈ b, ξ w = 0) → w = 0 := by
    intro w hw
    apply hsep
    intro ξ hξ
    have hle' : Submodule.span (KK O) b ≤ LinearMap.ker (Module.Dual.eval (KK O) W w) := by
      rw [Submodule.span_le]
      intro η hη
      simp only [SetLike.mem_coe, LinearMap.mem_ker, Module.Dual.eval_apply]
      exact hw η hη
    have hmem : ξ ∈ Submodule.span (KK O) b := by
      rw [hbspan]
      exact Submodule.subset_span hξ
    have h := hle' hmem
    simpa using h
  let Φ : W →ₗ[O] (b → KK O) := LinearMap.pi fun ξ => (ξ.1).restrictScalars O
  have hΦ : Function.Injective Φ := by
    refine (injective_iff_map_eq_zero Φ).2 ?_
    intro w hw
    apply hbsep
    intro ξ hξ
    have h := congrFun hw ⟨ξ, hξ⟩
    simpa [Φ] using h
  let g : (b → O) →ₗ[O] (b → KK O) :=
    LinearMap.pi fun i => (Algebra.linearMap O (KK O)).comp (LinearMap.proj i)
  have hle : N.map Φ ≤ LinearMap.range g := by
    rintro _ ⟨w, hw, rfl⟩
    choose c hc using fun ξ : b => hint ξ.1 (hbXi ξ.2) w hw
    rw [LinearMap.mem_range]
    refine ⟨c, ?_⟩
    funext ξ
    simp [g, Φ, hc]
  apply Submodule.fg_of_fg_map_injective Φ hΦ
  have hQ : ((N.map Φ).comap g).FG := IsNoetherian.noetherian _
  have h := hQ.map g
  rwa [Submodule.map_comap_eq, inf_eq_right.mpr hle] at h

end hw

end Formalism.MainNotions.G.GLWeightTheory
