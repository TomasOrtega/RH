import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSRing

/- English proof (translation)
Introduce `R _ A _ _ A' _ i h O _ a cO ψ hiso hlag hperf hadj hK hEq ι m χ ub hb hspan hind heig hbasis τ τb hconj j`. Establish `hsp : ⊤ ≤ Submodule.span R (Set.range fun k => (Submodule.Quotient.mk (hb k) : HdR A ⧸ Fil A))`. Establish `e : (Fil A).mkQ '' Set.range hb = Set.range fun k => (Submodule.Quotient.mk (hb k) : HdR A ⧸ Fil A)`. Rewrite using `[← Set.range_comp]`. Both sides reduce to the same expression.

Rewrite using `[← e, ← Submodule.map_span]`. Introduce `q _`. Take `⟨x, rfl⟩` from `(Fil A).mkQ_surjective q`. Establish `hx : x ∈ Submodule.span R (Set.range hb) ⊔ Fil A` using `hspan ▸ Submodule.mem_top`. Take `⟨y, hy, g, hg, rfl⟩` from `Submodule.mem_sup.1 hx`.

Use `⟨y, hy, ?_⟩` and prove the remaining obligations. Establish `hg0 : (Fil A).mkQ g = 0` using `(Submodule.Quotient.mk_eq_zero _).2 hg`. Rewrite using `[map_add, hg0, add_zero]`. Set `B` to `Module.Basis.mk hind hsp`. Set `k₀ : (Σ σ, Fin (m σ))` to `⟨τb, j⟩`.

Take `⟨f, hl⟩` from `hperf.bijective_left.2 (B.coord k₀ ∘ₗ (Fil A).mkQ)`. Establish `hval : ∀ x, ψ f x = B.coord k₀ ((Fil A).mkQ x)` using `fun x => by rw [hl]; rfl`. Establish `hf : f ∈ Fil A` using `hlag f fun g hg => by`. Establish `hg0 : (Fil A).mkQ g = 0` using `(Submodule.Quotient.mk_eq_zero _).2 hg`. Rewrite using `[hval, hg0, map_zero]`.

Establish `hδ : ∀ k, ψ f (hb k) = if k = k₀ then 1 else 0` using `fun k => by`. Establish `e : (Fil A).mkQ (hb k) = B k` using `by simp [B]`. Rewrite using `[hval, e, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]`. Establish `hact : ∀ z, act (dp0 R) (𝟙 _) a z f = χ τ z • f` using `fun z => by haveI := a.hom z`. Establish `hz : act (dp0 R) (𝟙 _) a z f ∈ Fil A`.

Rewrite using `[act_apply]`. Conclude with `push_mem_Fil _ hf`. Establish `hf' : act (dp0 R) (𝟙 _) a z f - χ τ z • f ∈ Fil A` using `sub_mem hz (Submodule.smul_mem _ _ hf)`. Establish `hker : (Submodule.span R (Set.range hb) ⊔ Fil A) ≤ LinearMap.ker (ψ (act (dp0 R) (𝟙 _) a z f - χ τ z • f))`. Use `sup_le ((Submodule.span_le).2 ?_) fun g hg => hiso _ hf' g hg` and prove the remaining obligations.

Introduce and unpack `_ ⟨k, rfl⟩`. Establish `e` using `hiso f hf _ (heig k (cO z))`. Rewrite `e` using `[map_sub, map_smul, sub_eq_zero]`. Establish `e2` using `hadj z f (hb k)`. Express the relevant statement in the definitionally equal form `ψ (act (dp0 R) (𝟙 _) a z f - χ τ z • f) (hb k) = 0`.

Rewrite using `[map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, e2, e, hδ]`. Distinguish the cases in `hk : k = k₀`. Substitute `hk` using the available equality. Simplify using `[k₀, hconj z]`. Simplify using `[hk]`.

Establish `h0 : ψ (act (dp0 R) (𝟙 _) a z f - χ τ z • f) = 0`. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Establish `: x ∈ Submodule.span R (Set.range hb) ⊔ Fil A` using `hspan ▸ Submodule.mem_top`. Conclude with `hker this`. Conclude with `sub_eq_zero.1 (hperf.bijective_left.1 (h0.trans (map_zero ψ).symm))`.

Take `⟨w, hw, hu⟩` from `hK f hf`. Establish `htan : IsTangent w`. Take `⟨k, -, l⟩` from `hw`. Conclude with `l.1`. Establish `heq : ∀ z, w ≫ a.act z = GlobalTheory.GrpTangent.epsScale (χ τ z) ≫ w` using `fun z => by`.

Establish `e1` using `hEq z f w hw`. Rewrite `e1` using `[hact z]`. Conclude with `(hK _ (Submodule.smul_mem _ _ hf)).unique e1 (hw.smul _)`. Take `⟨cf, hcf⟩` from `hbasis τ w htan heq`. Conclude with `⟨cf, w, hcf, f, hf, fun k => by convert hδ k, hw⟩`.
-/
theorem ksRow_exists_lieComb_ring : ∀ {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] [IsCommMonObj A] {A' : Over (Sp (DualNumber R))} [GrpObj A'] {i : A.left ⟶ A'.left} (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed R) i) {O : Type} [CommRing O] (a : OAct O A) (cO : O → O) (ψ : LinearMap.BilinForm R (HdR A)), (∀ f ∈ Fil A, ∀ g ∈ Fil A, ψ f g = 0) → (∀ f, (∀ g ∈ Fil A, ψ f g = 0) → f ∈ Fil A) → LinearMap.IsPerfPair ψ → IsAdjointFor a cO ψ → KSRegular h → (∀ (z : O) (f : HdR A) (w : epsR R ⟶ A), IsKSValue h f w → IsKSValue h (act (dp0 R) (𝟙 _) a z f) (w ≫ a.act z)) → ∀ {ι : Type} {m : ι → ℕ} (χ : ι → O →+* R) (ub : ∀ σ, Fin (m σ) → (epsR R ⟶ A)) (hb : (Σ σ, Fin (m σ)) → HdR A), Submodule.span R (Set.range hb) ⊔ Fil A = ⊤ → LinearIndependent R (fun k => (Submodule.Quotient.mk (hb k) : HdR A ⧸ Fil A)) → (∀ k (z : O), act (dp0 R) (𝟙 _) a z (hb k) - χ k.1 z • hb k ∈ Fil A) → (∀ σ (w : epsR R ⟶ A), IsTangent w → (∀ z, w ≫ a.act z = GlobalTheory.GrpTangent.epsScale (χ σ z) ≫ w) → ∃ cf, IsLieComb cf (ub σ) w) → ∀ (τ τb : ι), (∀ z, χ τb (cO z) = χ τ z) → ∀ (j : Fin (m τb)), ∃ cf : Fin (m τ) → R, ∃ w, IsLieComb cf (ub τ) w ∧ GlobalTheory.FlagTan.IsKSRow h ψ hb ⟨τb, j⟩ w := by
  intro R _ A _ _ A' _ i h O _ a cO ψ hiso hlag hperf hadj hK hEq ι m χ ub hb hspan hind heig hbasis τ τb hconj j
  classical

  have hsp : ⊤ ≤ Submodule.span R (Set.range fun k => (Submodule.Quotient.mk (hb k) : HdR A ⧸ Fil A)) := by
    have e : (Fil A).mkQ '' Set.range hb =
        Set.range fun k => (Submodule.Quotient.mk (hb k) : HdR A ⧸ Fil A) := by
      rw [← Set.range_comp]; rfl
    rw [← e, ← Submodule.map_span]
    intro q _
    obtain ⟨x, rfl⟩ := (Fil A).mkQ_surjective q
    have hx : x ∈ Submodule.span R (Set.range hb) ⊔ Fil A := hspan ▸ Submodule.mem_top
    obtain ⟨y, hy, g, hg, rfl⟩ := Submodule.mem_sup.1 hx
    refine ⟨y, hy, ?_⟩
    have hg0 : (Fil A).mkQ g = 0 := (Submodule.Quotient.mk_eq_zero _).2 hg
    rw [map_add, hg0, add_zero]
  let B := Module.Basis.mk hind hsp
  let k₀ : (Σ σ, Fin (m σ)) := ⟨τb, j⟩
  obtain ⟨f, hl⟩ := hperf.bijective_left.2 (B.coord k₀ ∘ₗ (Fil A).mkQ)
  have hval : ∀ x, ψ f x = B.coord k₀ ((Fil A).mkQ x) := fun x => by rw [hl]; rfl
  have hf : f ∈ Fil A := hlag f fun g hg => by
    have hg0 : (Fil A).mkQ g = 0 := (Submodule.Quotient.mk_eq_zero _).2 hg
    rw [hval, hg0, map_zero]
  have hδ : ∀ k, ψ f (hb k) = if k = k₀ then 1 else 0 := fun k => by
    have e : (Fil A).mkQ (hb k) = B k := by simp [B]
    rw [hval, e, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]

  have hact : ∀ z, act (dp0 R) (𝟙 _) a z f = χ τ z • f := fun z => by
    haveI := a.hom z
    have hz : act (dp0 R) (𝟙 _) a z f ∈ Fil A := by
      rw [act_apply]; exact push_mem_Fil _ hf
    have hf' : act (dp0 R) (𝟙 _) a z f - χ τ z • f ∈ Fil A :=
      sub_mem hz (Submodule.smul_mem _ _ hf)
    have hker : (Submodule.span R (Set.range hb) ⊔ Fil A) ≤
        LinearMap.ker (ψ (act (dp0 R) (𝟙 _) a z f - χ τ z • f)) := by
      refine sup_le ((Submodule.span_le).2 ?_) fun g hg => hiso _ hf' g hg
      rintro _ ⟨k, rfl⟩
      have e := hiso f hf _ (heig k (cO z))
      rw [map_sub, map_smul, sub_eq_zero] at e
      have e2 := hadj z f (hb k)
      change ψ (act (dp0 R) (𝟙 _) a z f - χ τ z • f) (hb k) = 0
      rw [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, e2, e, hδ]
      by_cases hk : k = k₀
      · subst hk
        simp [k₀, hconj z]
      · simp [hk]
    have h0 : ψ (act (dp0 R) (𝟙 _) a z f - χ τ z • f) = 0 := by
      refine LinearMap.ext fun x => ?_
      have : x ∈ Submodule.span R (Set.range hb) ⊔ Fil A := hspan ▸ Submodule.mem_top
      exact hker this
    exact sub_eq_zero.1 (hperf.bijective_left.1 (h0.trans (map_zero ψ).symm))

  obtain ⟨w, hw, hu⟩ := hK f hf
  have htan : IsTangent w := by
    obtain ⟨k, -, l⟩ := hw
    exact l.1
  have heq : ∀ z, w ≫ a.act z = GlobalTheory.GrpTangent.epsScale (χ τ z) ≫ w := fun z => by
    have e1 := hEq z f w hw
    rw [hact z] at e1
    exact (hK _ (Submodule.smul_mem _ _ hf)).unique e1 (hw.smul _)
  obtain ⟨cf, hcf⟩ := hbasis τ w htan heq
  exact ⟨cf, w, hcf, f, hf, fun k => by convert hδ k, hw⟩

end GlobalTheory.KSRing
