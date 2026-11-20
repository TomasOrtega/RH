import Formalism.WachLatticeTwists.LatticeDualFibres.FibreDualStable
import Formalism.WachLatticeTwists.LatticeDualFibres.LatticeDualProofs.PropLoc

universe u

open Formalism.NG (KO annih)
open ReciprocityTheory.Gal

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.LOC

/- English proof (translation)
Establish `hc' : algebraMap O (FractionRing O) c ≠ 0`. Simplify using `using hc`. Prove the components needed by the constructor for the conclusion. Introduce `v w h`. Establish `h' : algebraMap O (FractionRing O) c • v = algebraMap O (FractionRing O) c • w`.

Simplify `h` using `only [algebraMap_smul]`. Conclude with `smul_right_injective V hc' h'`. Introduce `v`. Use `⟨(algebraMap O (FractionRing O) c)⁻¹ • v, ?_⟩` and prove the remaining obligations. Use `show c • _ = v`.

Rewrite using `[← algebraMap_smul (FractionRing O) c, smul_smul, mul_inv_cancel₀ hc', one_smul]`.
-/
theorem smul_bij {O V : Type u} [CommRing O] [IsDomain O] [AddCommGroup V] [Module O V]
    [Module (FractionRing O) V] [IsScalarTower O (FractionRing O) V] (c : O) (hc : c ≠ 0) :
    Function.Bijective fun v : V => c • v := by
  have hc' : algebraMap O (FractionRing O) c ≠ 0 := by
    simpa using hc
  constructor
  · intro v w h
    have h' : algebraMap O (FractionRing O) c • v = algebraMap O (FractionRing O) c • w := by
      simpa only [algebraMap_smul] using h
    exact smul_right_injective V hc' h'
  · intro v
    refine ⟨(algebraMap O (FractionRing O) c)⁻¹ • v, ?_⟩
    show c • _ = v
    rw [← algebraMap_smul (FractionRing O) c, smul_smul, mul_inv_cancel₀ hc', one_smul]

/- English proof (translation)
Use `⟨fun r hr => ?_⟩` and prove the remaining obligations. Establish `hr0 : r ≠ 0` using `hr.ne_zero`. Establish `key : ∀ x : H1 ρ, r • x = 0 → x = 0`. Introduce `x`. Proceed by induction on `x using Submodule.Quotient.induction_on with`.

Consider the case `H z`. Introduce `h`. Rewrite `h` using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Take `⟨m, hm⟩` from `(mem_coboundaries1 ρ _).1 h`. Take `⟨m', hm'⟩` from `(hb r hr0).2 m`.

Rewrite using `[Submodule.Quotient.mk_eq_zero]`. Use `(mem_coboundaries1 ρ _).2 ⟨m', fun g => (hb r hr0).1 ?_⟩` and prove the remaining obligations. Establish `h1 : r • z.1 g = ρ g m - m` using `hm g`. Use `show r • z.1 g = r • (ρ g m' - m')`. Establish `hm'' : r • m' = m` using `hm'`.

Rewrite using `[h1, smul_sub, ← map_smul, hm'']`. Introduce `x y hxy`. Establish `hxy' : r • x = r • y` using `hxy`. Establish `: r • (x - y) = 0` using `by rw [smul_sub, hxy', sub_self]`. Conclude with `sub_eq_zero.1 (key _ this)`.
-/
theorem h_one_torsion_free {O G V : Type u} [CommRing O] [IsDomain O] [Group G] [TopologicalSpace G]
    [AddCommGroup V] [Module O V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [ContinuousConstSMul O V] (ρ : Representation O G V)
    (hb : ∀ c : O, c ≠ 0 → Function.Bijective fun v : V => c • v) :
    Module.IsTorsionFree O (H1 ρ) := by
  refine ⟨fun r hr => ?_⟩
  have hr0 : r ≠ 0 := hr.ne_zero
  have key : ∀ x : H1 ρ, r • x = 0 → x = 0 := by
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H z =>
      intro h
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
      obtain ⟨m, hm⟩ := (mem_coboundaries1 ρ _).1 h
      obtain ⟨m', hm'⟩ := (hb r hr0).2 m
      rw [Submodule.Quotient.mk_eq_zero]
      refine (mem_coboundaries1 ρ _).2 ⟨m', fun g => (hb r hr0).1 ?_⟩
      have h1 : r • z.1 g = ρ g m - m := hm g
      show r • z.1 g = r • (ρ g m' - m')
      have hm'' : r • m' = m := hm'
      rw [h1, smul_sub, ← map_smul, hm'']
  intro x y hxy
  have hxy' : r • x = r • y := hxy
  have : r • (x - y) = 0 := by rw [smul_sub, hxy', sub_self]
  exact sub_eq_zero.1 (key _ this)

/- English proof (translation)
Introduce `O G VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ D HfV HfV' ℓ e' ι₁ ι₂ P Q hT hperf hfin hc hBK hP hQ`. Establish `h1` using `hDual O G VT VT' D.ε D.ρT D.ρT' D.bT D.T hT D.stT hperf D.eqT`. Establish `hT' : IsLatticeIn D.T'` using `h1.1`. Establish `hrk : Module.finrank O D.T' = Module.finrank O D.T` using `h1.2.1`. Take `⟨e, he⟩ : ∃ e : (VT' ⧸ D.T') →ₗ[O] (Fin (Module.finrank O D.T) → KO O), Function.Injective e` from `hrk ▸ (hEmb O VT' D.T' hT').2`.

Establish `htf : Module.IsTorsionFree O (H1 D.ρT')` using `h_one_torsion_free D.ρT' (fun c hc => smul_bij c hc)`. Establish `a1 : ∀ a : VT' ⧸ D.T', ∃ c : O, c ≠ 0 ∧ c • a = 0`. Introduce `a`. Take `⟨c, hc, h⟩` from `pi_torsion (e a)`. Use `⟨c, hc, he ?_⟩` and prove the remaining obligations.

Rewrite using `[map_smul, h, map_zero]`. Establish `a2 : LinearMap.ker D.T'.mkQ = LinearMap.range D.T'.subtype`. Rewrite using `[Submodule.ker_mkQ, Submodule.range_subtype]`. Establish `a3 : ∀ (g : G) (m : D.T'), D.T'.subtype (D.ρTl' g m) = D.ρT' g (D.T'.subtype m)` using `fun _ _ => rfl`. Establish `a4 : ∀ (g : G) (m : VT'), D.T'.mkQ (D.ρT' g m) = D.ρA' g (D.T'.mkQ m)` using `fun _ _ => rfl`.

Establish `a5 : Topology.IsEmbedding D.T'.subtype` using `Topology.IsEmbedding.subtypeVal`. Establish `hC` using `hConn O G D.T' VT' (VT' ⧸ D.T') D.ρTl' D.ρT' D.ρA' D.T'.subtype D.T'.mkQ a5 a3 a4 (Submodule.mkQ_surjective _) a2 D.contT' (fun c hc => smul_bij c hc) a1`. Take `⟨δ, hδ⟩` from `hC`. Set `ι : H0 D.ρA' →ₗ[O] (Fin (Module.finrank O D.T) → KO O)` to `e ∘ₗ (H0 D.ρA').subtype`. Establish `hι : Function.Injective ι` using `he.comp (Submodule.injective_subtype _)`.

Set `δ' : LinearMap.range ι →ₗ[O] H1 D.ρTl'` to `δ ∘ₗ (LinearEquiv.ofInjective ι hι).symm.toLinearMap`. Establish `hδ' : LinearMap.range δ' = Submodule.torsion O (H1 D.ρTl')`. Rewrite using `[← hδ]`. Conclude with `LinearEquiv.range_comp _ _`. Establish `main` using `propLoc O (H1 D.ρA) (H1 D.ρT) (H1 D.ρTl') (H1 D.ρT') D.q D.j' D.pr HfV HfV' ℓ e' (Module.finrank O D.T) (LinearMap.range ι) δ' ι₁ ι₂ (fun i => (P i).toDirect) (fun i => (Q i).toDual hc) hBK hδ' hP hQ`.

Use `⟨main.1, main.2.1, ?_⟩` and prove the remaining obligations. Conclude with `main.2.2`.
-/
theorem propLocCont_of (hConn : StatConnTors.{u}) (hEmb : StatQuotEmbeds.{u})
    (hDual : StatDualLattice.{u}) : StatPropLocCont.{u} := by
  intro O G VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ D HfV HfV' ℓ e' ι₁ ι₂ P Q
    hT hperf hfin hc hBK hP hQ
  have h1 := hDual O G VT VT' D.ε D.ρT D.ρT' D.bT D.T hT D.stT hperf D.eqT
  have hT' : IsLatticeIn D.T' := h1.1
  have hrk : Module.finrank O D.T' = Module.finrank O D.T := h1.2.1
  obtain ⟨e, he⟩ : ∃ e : (VT' ⧸ D.T') →ₗ[O] (Fin (Module.finrank O D.T) → KO O),
      Function.Injective e := hrk ▸ (hEmb O VT' D.T' hT').2
  have htf : Module.IsTorsionFree O (H1 D.ρT') := h_one_torsion_free D.ρT' (fun c hc => smul_bij c hc)
  have a1 : ∀ a : VT' ⧸ D.T', ∃ c : O, c ≠ 0 ∧ c • a = 0 := by
    intro a
    obtain ⟨c, hc, h⟩ := pi_torsion (e a)
    refine ⟨c, hc, he ?_⟩
    rw [map_smul, h, map_zero]
  have a2 : LinearMap.ker D.T'.mkQ = LinearMap.range D.T'.subtype := by
    rw [Submodule.ker_mkQ, Submodule.range_subtype]
  have a3 : ∀ (g : G) (m : D.T'), D.T'.subtype (D.ρTl' g m) = D.ρT' g (D.T'.subtype m) :=
    fun _ _ => rfl
  have a4 : ∀ (g : G) (m : VT'), D.T'.mkQ (D.ρT' g m) = D.ρA' g (D.T'.mkQ m) := fun _ _ => rfl
  have a5 : Topology.IsEmbedding D.T'.subtype := Topology.IsEmbedding.subtypeVal
  have hC := hConn O G D.T' VT' (VT' ⧸ D.T') D.ρTl' D.ρT' D.ρA' D.T'.subtype D.T'.mkQ
    a5 a3 a4 (Submodule.mkQ_surjective _) a2 D.contT' (fun c hc => smul_bij c hc) a1
  obtain ⟨δ, hδ⟩ := hC
  let ι : H0 D.ρA' →ₗ[O] (Fin (Module.finrank O D.T) → KO O) := e ∘ₗ (H0 D.ρA').subtype
  have hι : Function.Injective ι := he.comp (Submodule.injective_subtype _)
  let δ' : LinearMap.range ι →ₗ[O] H1 D.ρTl' := δ ∘ₗ (LinearEquiv.ofInjective ι hι).symm.toLinearMap
  have hδ' : LinearMap.range δ' = Submodule.torsion O (H1 D.ρTl') := by
    rw [← hδ]
    exact LinearEquiv.range_comp _ _
  have main := propLoc O (H1 D.ρA) (H1 D.ρT) (H1 D.ρTl') (H1 D.ρT') D.q D.j' D.pr HfV HfV' ℓ e'
    (Module.finrank O D.T) (LinearMap.range ι) δ' ι₁ ι₂ (fun i => (P i).toDirect)
    (fun i => (Q i).toDual hc) hBK hδ' hP hQ
  refine ⟨main.1, main.2.1, ?_⟩
  exact main.2.2

end Formalism.RepresentationBoundsCohomology.LOC
