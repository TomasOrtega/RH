import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrdInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumPullbackEqZeroIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorRelationLatticeNonzerodivisorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorBundleSectionsFiniteProjectiveStatement

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.GroupBplus (AffOp)
open GlobalTheory.RingChain (RChain mv baseOf Qt IsFrobLin)
open GlobalTheory.ChainPts.PullHT (pullA)
open GlobalTheory.PerfdLat (piMap)
open scoped TensorProduct Pointwise
open GlobalTheory.ChainPts
open GlobalTheory.ChainDesc

namespace GlobalTheory.ChainDesc.KerRho

/- English proof (translation)
Establish `hm : ∀ x, piMap g (Fin h) (κ x) ∈ L` using `fun x => by`. Establish `: κ x ∈ L.comap (piMap g (Fin h))` using `hL ▸ LinearMap.mem_range_self κ x`. Conclude with `this`. Establish `hbase : ∀ v ∈ baseOf π h, piMap g (Fin h) v ∈ baseOf π' h` using `fun v hv => by`. Take `⟨u, -, rfl⟩` from `(Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hv`.

Rewrite using `[map_smulₛₗ, hπ]`. Conclude with `Submodule.smul_mem_pointwise_smul _ _ _ trivial`. Set `G : P →ₛₗ[g] Qt L (baseOf π' h)` to `(Submodule.mkQ _).comp (((piMap g (Fin h)).comp κ).codRestrict L hm)`. Establish `hG : ∀ x, G x = Submodule.Quotient.mk ⟨_, hm x⟩` using `fun _ => rfl`. Use `le_antisymm (Submodule.span_mono ?_) (Submodule.span_le.2 ?_)` and prove the remaining obligations.

Introduce and unpack `_ ⟨x₀, h0, rfl⟩`. Use `⟨⟨_, hm x₀⟩, ?_, rfl⟩` and prove the remaining obligations. Take `⟨z, hz⟩` from `(hq _).1 h0`. Establish `key : ∀ z : LA, ∃ x, t x = jA z ∧ G x ∈ LinearMap.range jB` using `fun z => by`. Establish `hz : z ∈ Submodule.span A (Set.range a)` using `ha ▸ trivial`.

Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem _ hs`. Take `⟨s, rfl⟩` from `hs`. Take `⟨x, y, h1, h2, h3⟩` from `hj s`. Use `⟨x, h3.symm, b s, h2.trans ?_⟩` and prove the remaining obligations.

Rewrite using `[hG]`. Use `congr 1`. Conclude with `Subtype.ext h1`. Consider the case `zero => exact ⟨0, by simp, by simp⟩`. Consider the case `add _ _ _ _ h1 h2`.

Take `⟨x, e, m⟩` from `h1`. Take `⟨x', e', m'⟩` from `h2`. Conclude with `⟨x + x', by rw [map_add, map_add, e, e'], by rw [map_add]; exact add_mem m m'⟩`. Consider the case `smul c _ _ h1`. Take `⟨x, e, m⟩` from `h1`.

Conclude with `⟨c • x, by rw [map_smul, map_smul, e], by rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ m⟩`. Take `⟨x, e, m⟩` from `key z`. Establish `h1 : G (x₀ - x) = 0`. Rewrite using `[hG, Submodule.Quotient.mk_eq_zero]`. Conclude with `hbase _ ((ht _).1 (by rw [map_sub, e, hz, sub_self]))`.

Rewrite `h1` using `[map_sub, sub_eq_zero]`. Rewrite using `[← hG, h1]`. Conclude with `m`. Introduce and unpack `_ ⟨y₀, ⟨z, hz⟩, rfl⟩ set T := Submodule.span R {z | ∃ x₀ : P, q (t x₀) = 0 ∧ z = piMap (φ.comp g) (Fin h) (κ x₀)} with hT`. Establish `hbT : ∀ v ∈ baseOf π' h, piMap φ (Fin h) v ∈ T` using `fun v hv => by`.

Take `⟨u, -, rfl⟩` from `(Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hv`. Establish `e : piMap φ (Fin h) (π' • u) = ∑ i, φ (u i) • piMap (φ.comp g) (Fin h) (π • Pi.single i 1)`. Use extensionality with `k`. Simplify using `[Finset.sum_apply, Pi.single_apply, apply_ite, hπ, mul_comm]`. Rewrite using `[e]`.

Use `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)` and prove the remaining obligations. Establish `hi : π • Pi.single i (1 : A) ∈ baseOf π h` using `Submodule.smul_mem_pointwise_smul _ _ _ trivial`. Establish `hi' : π • Pi.single i (1 : A) ∈ LinearMap.range κ`. Rewrite using `[hL]`. Conclude with `hb (hbase _ hi)`.

Take `⟨x, hx⟩` from `hi'`. Conclude with `⟨x, by rw [(ht x).2 (hx ▸ hi), map_zero], by rw [hx]⟩`. Establish `key : ∀ z : LB, ∃ y : L, Submodule.Quotient.mk y = jB z ∧ piMap φ (Fin h) y.1 ∈ T` using `fun z => by`. Establish `hz : z ∈ Submodule.span Bp (Set.range b)` using `hb' ▸ trivial`. Proceed by induction on `hz using Submodule.span_induction with`.

Consider the case `mem _ hs`. Take `⟨s, rfl⟩` from `hs`. Take `⟨x, y, h1, h2, h3⟩` from `hj s`. Use `⟨y, h2.symm, Submodule.subset_span ⟨x, ?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[← h3]`.

Conclude with `hq.apply_apply_eq_zero _`. Rewrite using `[h1]`. Both sides reduce to the same expression. Consider the case `zero => exact ⟨0, by simp, by simp⟩`. Consider the case `add _ _ _ _ h1 h2`.

Take `⟨x, e, m⟩` from `h1`. Take `⟨x', e', m'⟩` from `h2`. Conclude with `⟨x + x', by rw [Submodule.Quotient.mk_add, map_add, e, e'], by rw [Submodule.coe_add, map_add]; exact add_mem m m'⟩`. Consider the case `smul c _ _ h1`. Take `⟨x, e, m⟩` from `h1`.

Conclude with `⟨c • x, by rw [Submodule.Quotient.mk_smul, map_smul, e], by rw [Submodule.coe_smul, map_smulₛₗ]; exact Submodule.smul_mem _ _ m⟩`. Take `⟨y, e, m⟩` from `key z`. Establish `h0 : y₀ - y ∈ (baseOf π' h).comap L.subtype` using `(Submodule.Quotient.eq _).1 (hz.symm.trans e.symm)`. Establish `h1` using `hbT _ h0`. Rewrite `h1` using `[Submodule.subtype_apply, Submodule.coe_sub, map_sub]`.

Simplify using `using add_mem h1 m`.
-/
theorem span_eq {A Bp R : Type} [CommRing A] [CommRing Bp] [CommRing R] (g : A →+* Bp) (φ : Bp →+* R) {h : ℕ}
    {P Q Q' LA LB S : Type} [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module A Q] [AddCommGroup Q'] [Module A Q']
    [AddCommGroup LA] [Module A LA] [AddCommGroup LB] [Module Bp LB] (κ : P →ₗ[A] (Fin h → A)) (t : P →ₗ[A] Q)
    (q : Q →ₗ[A] Q') (π : A) (π' : Bp) (hπ : g π = π') (L : Submodule Bp (Fin h → Bp)) (hb : baseOf π' h ≤ L)
    (hL : LinearMap.range κ = L.comap (piMap g (Fin h))) (ht : ∀ s, t s = 0 ↔ κ s ∈ baseOf π h)
    (jA : LA →ₗ[A] Q) (jB : LB →ₗ[Bp] Qt L (baseOf π' h)) (hq : Function.Exact jA q) (a : S → LA) (b : S → LB)
    (ha : Submodule.span A (Set.range a) = ⊤) (hb' : Submodule.span Bp (Set.range b) = ⊤)
    (hj : ∀ s, ∃ (x : P) (y : L), y.1 = piMap g (Fin h) (κ x) ∧ jB (b s) = Submodule.Quotient.mk y ∧ jA (a s) = t x) :
    Submodule.span R {z | ∃ x₀ : P, q (t x₀) = 0 ∧ z = piMap (φ.comp g) (Fin h) (κ x₀)} =
      Submodule.span R {z | ∃ x₀ : L, Submodule.Quotient.mk x₀ ∈ LinearMap.range jB ∧ z = piMap φ _ x₀.1} := by
  have hm : ∀ x, piMap g (Fin h) (κ x) ∈ L := fun x => by
    have : κ x ∈ L.comap (piMap g (Fin h)) := hL ▸ LinearMap.mem_range_self κ x
    exact this
  have hbase : ∀ v ∈ baseOf π h, piMap g (Fin h) v ∈ baseOf π' h := fun v hv => by
    obtain ⟨u, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hv
    rw [map_smulₛₗ, hπ]
    exact Submodule.smul_mem_pointwise_smul _ _ _ trivial
  let G : P →ₛₗ[g] Qt L (baseOf π' h) :=
    (Submodule.mkQ _).comp (((piMap g (Fin h)).comp κ).codRestrict L hm)
  have hG : ∀ x, G x = Submodule.Quotient.mk ⟨_, hm x⟩ := fun _ => rfl
  refine le_antisymm (Submodule.span_mono ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨x₀, h0, rfl⟩
    refine ⟨⟨_, hm x₀⟩, ?_, rfl⟩
    obtain ⟨z, hz⟩ := (hq _).1 h0
    have key : ∀ z : LA, ∃ x, t x = jA z ∧ G x ∈ LinearMap.range jB := fun z => by
      have hz : z ∈ Submodule.span A (Set.range a) := ha ▸ trivial
      induction hz using Submodule.span_induction with
      | mem _ hs =>
        obtain ⟨s, rfl⟩ := hs
        obtain ⟨x, y, h1, h2, h3⟩ := hj s
        refine ⟨x, h3.symm, b s, h2.trans ?_⟩
        rw [hG]; congr 1; exact Subtype.ext h1
      | zero => exact ⟨0, by simp, by simp⟩
      | add _ _ _ _ h1 h2 =>
        obtain ⟨x, e, m⟩ := h1
        obtain ⟨x', e', m'⟩ := h2
        exact ⟨x + x', by rw [map_add, map_add, e, e'], by rw [map_add]; exact add_mem m m'⟩
      | smul c _ _ h1 =>
        obtain ⟨x, e, m⟩ := h1
        exact ⟨c • x, by rw [map_smul, map_smul, e], by rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ m⟩
    obtain ⟨x, e, m⟩ := key z
    have h1 : G (x₀ - x) = 0 := by
      rw [hG, Submodule.Quotient.mk_eq_zero]
      exact hbase _ ((ht _).1 (by rw [map_sub, e, hz, sub_self]))
    rw [map_sub, sub_eq_zero] at h1
    rw [← hG, h1]
    exact m
  · rintro _ ⟨y₀, ⟨z, hz⟩, rfl⟩
    set T := Submodule.span R {z | ∃ x₀ : P, q (t x₀) = 0 ∧ z = piMap (φ.comp g) (Fin h) (κ x₀)} with hT
    have hbT : ∀ v ∈ baseOf π' h, piMap φ (Fin h) v ∈ T := fun v hv => by
      obtain ⟨u, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hv
      have e : piMap φ (Fin h) (π' • u) = ∑ i, φ (u i) • piMap (φ.comp g) (Fin h) (π • Pi.single i 1) := by
        ext k
        simp [Finset.sum_apply, Pi.single_apply, apply_ite, hπ, mul_comm]
      rw [e]
      refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      have hi : π • Pi.single i (1 : A) ∈ baseOf π h := Submodule.smul_mem_pointwise_smul _ _ _ trivial
      have hi' : π • Pi.single i (1 : A) ∈ LinearMap.range κ := by
        rw [hL]; exact hb (hbase _ hi)
      obtain ⟨x, hx⟩ := hi'
      exact ⟨x, by rw [(ht x).2 (hx ▸ hi), map_zero], by rw [hx]⟩
    have key : ∀ z : LB, ∃ y : L, Submodule.Quotient.mk y = jB z ∧ piMap φ (Fin h) y.1 ∈ T := fun z => by
      have hz : z ∈ Submodule.span Bp (Set.range b) := hb' ▸ trivial
      induction hz using Submodule.span_induction with
      | mem _ hs =>
        obtain ⟨s, rfl⟩ := hs
        obtain ⟨x, y, h1, h2, h3⟩ := hj s
        refine ⟨y, h2.symm, Submodule.subset_span ⟨x, ?_, ?_⟩⟩
        · rw [← h3]; exact hq.apply_apply_eq_zero _
        · rw [h1]; rfl
      | zero => exact ⟨0, by simp, by simp⟩
      | add _ _ _ _ h1 h2 =>
        obtain ⟨x, e, m⟩ := h1
        obtain ⟨x', e', m'⟩ := h2
        exact ⟨x + x', by rw [Submodule.Quotient.mk_add, map_add, e, e'],
          by rw [Submodule.coe_add, map_add]; exact add_mem m m'⟩
      | smul c _ _ h1 =>
        obtain ⟨x, e, m⟩ := h1
        exact ⟨c • x, by rw [Submodule.Quotient.mk_smul, map_smul, e],
          by rw [Submodule.coe_smul, map_smulₛₗ]; exact Submodule.smul_mem _ _ m⟩
    obtain ⟨y, e, m⟩ := key z
    have h0 : y₀ - y ∈ (baseOf π' h).comap L.subtype := (Submodule.Quotient.eq _).1 (hz.symm.trans e.symm)
    have h1 := hbT _ h0
    rw [Submodule.subtype_apply, Submodule.coe_sub, map_sub] at h1
    simpa using add_mem h1 m

set_option maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in

/- English proof (translation)
Introduce `O _ _ _ p B B' Λ _ h o Lie Om π γ M C f g E ι Q t j ρ k hLie hι hQ U hJ hR R _ φ hφ hw r e`. Establish `hV` using `k.isAffineOpen U`. Use `haveI := hQ.1`. Use `haveI := (hι 0).2.1`. Use `haveI : ((pullA f.f).obj Lie).V.IsQuasicoherent := isQuasicoherent_pullback f.f Lie.V`.

Use `haveI : (cokernel j).V.IsQuasicoherent := isQuasicoherent_of_iso (Examples₂.cokV j).symm`. Establish `hc` using `isColimitOfHasCokernelOfPreservesColimit (Action.forget B'.X.Modules Λ) j`. Establish `hz : j.hom ≫ (cokernel.π j).hom = 0`. Rewrite using `[← Action.comp_hom, cokernel.condition]`. Both sides reduce to the same expression.

Use `haveI : Epi (cokernel.π j).hom := inferInstanceAs (Epi ((Action.forget B'.X.Modules Λ).map (cokernel.π j)))`. Establish `hex` using `exact_and_surjective_app_of_exact_of_epi (S := ShortComplex.mk _ _ hz) (ShortComplex.exact_of_g_is_cokernel _ hc) hV`. Take `⟨q1, q2, -⟩` from `hQ.2 _ hV`. Establish `hL` using `((hι 0).2.2 U).1`. Rewrite `hL` using `[Nat.zero_min]`.

Use `haveI := (GlobalTheory.T.vector_bundle_sections_finite_projective _ _ _ (hι 0).1 _ hV).2`. Establish `ha : Submodule.span Γ(B'.X, f.f ⁻¹ᵁ U.1) (Set.range fun s => pullbackSections f.f Lie.V le_rfl s : Set Γ((Scheme.Modules.pullback f.f).obj Lie.V, f.f ⁻¹ᵁ U.1)) = ⊤`. Use `letI := appLEAlgebra f.f (le_refl (f.f ⁻¹ᵁ U.1))`. Use `letI := appLEModule f.f ((Scheme.Modules.pullback f.f).obj Lie.V) (le_refl (f.f ⁻¹ᵁ U.1))`. Use `haveI := appLE_isScalarTower f.f ((Scheme.Modules.pullback f.f).obj Lie.V) (le_refl (f.f ⁻¹ᵁ U.1))`.

Establish `hbc` using `isBaseChange_pullbackSections f.f Lie.V hV U.2.1 le_rfl`. Use `eq_top_iff.2 fun x _ => ?_` and prove the remaining obligations. Proceed by induction on `x using hbc.inductionOn with`. Consider the case `zero => exact zero_mem _`. Consider the case `tmul s => exact Submodule.subset_span ⟨s, rfl⟩`.

Consider the case `smul c x hx => exact Submodule.smul_mem _ _ (hx trivial)`. Consider the case `add x y hx hy => exact add_mem (hx trivial) (hy trivial)`. Establish `hb : Submodule.span U.Bp (Set.range fun s : Γ(Lie.V, U.1) => (1 ⊗ₜ s : SecBp Lie.V U)) = ⊤`. Use `eq_top_iff.2 fun x _ => ?_` and prove the remaining obligations. Proceed by induction on `x using TensorProduct.induction_on with`.

Consider the case `zero => exact zero_mem _`. Consider the case `tmul c s`. Rewrite using `[← mul_one c, ← smul_eq_mul, ← TensorProduct.smul_tmul']`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, rfl⟩)`. Consider the case `add x y hx hy => exact add_mem (hx trivial) (hy trivial)`.

Establish `hsp` using `span_eq (g U) φ (crd (ι 0) _) (appLinear t _) (appLinear (cokernel.π j).hom _) _ _ (k.map_cst U π) ((C U).L 0) ((C U).base_le 0) hL q2 (appLinear j.hom _) (C U).j hex.1 _ _ ha hb hJ`. Establish `hbl : baseOf (resG B'.X le_top (f.f.appTop π)) h ≤ LinearMap.range (crd (ι 0) (f.f ⁻¹ᵁ U.1))` using `fun v hv => by`. Take `⟨u, -, rfl⟩` from `(Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hv`. Express the relevant statement in the definitionally equal form `_ ∈ latOf (ι 0) _`. Rewrite using `[hL, Submodule.mem_comap, map_smulₛₗ, k.map_cst]`.

Conclude with `(C U).base_le 0 (Submodule.smul_mem_pointwise_smul _ _ _ trivial)`. Use `choose x y hy hρ hx using fun l => hR (e l)`. Use `letI : Algebra Γ(B'.X, f.f ⁻¹ᵁ U.1) R := (φ.comp (g U)).toAlgebra`. Use extensionality with `c`. Establish `h1` using `(GlobalTheory.ChainPts.KerTens.main B'.X R _ _ ρ.hom _ r (fun l => pullbackSections f.f Om.V le_rfl (e l)) c).1 hV hw`.

Establish `h2` using `GlobalTheory.T.tensor_relation_lattice_nonzerodivisor Γ(B'.X, f.f ⁻¹ᵁ U.1) R h _ _ (crd (ι 0) _) (appLinear (t ≫ (cokernel.π j).hom) _) _ (crd_injective _ _) hbl (by rw [← k.map_cst] at hφ; exact hφ) (hex.2.comp q1) r x c`. Use `h1.trans ?_` and prove the remaining obligations. Establish `h3 : ∀ l, ρ.hom.app _ (pullbackSections f.f Om.V le_rfl (e l)) = appLinear (t ≫ (cokernel.π j).hom) _ (x l)` using `hx`. Simplify using `only [h3]`. Use `h2.trans ?_` and prove the remaining obligations.

Establish `h4 : ∀ l, piMap (algebraMap Γ(B'.X, f.f ⁻¹ᵁ U.1) R) (Fin h) (crd (ι 0) _ (x l)) = piMap φ _ (y l).1` using `fun l => by`. Rewrite using `[hy]`. Both sides reduce to the same expression. Simplify using `only [h4]`. Use `(SetLike.ext_iff.1 hsp _).trans ⟨fun hh => ⟨y, hρ, hh⟩, fun ⟨y', hρ', hh⟩ => ?_⟩` and prove the remaining obligations.

Establish `h5 : ∑ l, c l • piMap φ _ (y l).1 = ∑ l, c l • piMap φ _ (y' l).1 + ∑ l, c l • piMap φ _ (y l - y' l).1`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[Submodule.coe_sub, map_sub, ← smul_add, add_sub_cancel]`. Rewrite using `[h5]`.

Use `add_mem hh (Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ?_, rfl⟩))` and prove the remaining obligations. Rewrite using `[Submodule.Quotient.mk_sub]`. Conclude with `(Submodule.Quotient.eq _).1 ((hρ l).symm.trans (hρ' l))`.
-/
theorem kerAt_eq_kerR : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) (B B' : GlobalTheory.Vert.Model O) (Λ : Type) [CommRing Λ] (h o : ℕ) (Lie Om : AM B Λ) (π : Γ(B.X, ⊤)) (γ : ℕ → Γ(B.X, ⊤)) (M : Λ →+* Matrix (Fin h) (Fin h) ℤ) (C : ChainsBp p h o Lie Om π γ) (f : GlobalTheory.Vert.Model.Hom B' B) (g : ∀ U : AffOp B.X, Γ(B'.X, f.f ⁻¹ᵁ U.1) →+* U.Bp) (E : ℕ → B'.X.Modules) (ι : ∀ n, E n ⟶ freeModule B'.X (Fin h)) (Q : AM B' Λ) (t : E 0 ⟶ Q.V) (j : (pullA f.f).obj Lie ⟶ Q) (ρ : (pullA f.f).obj Om ⟶ cokernel j) (k : IsCov f g), Lie.V.IsQuasicoherent → IsLatOf C f g ι → IsQuot M (ι 0) (baseOn h (f.f.appTop π)) Q t → ∀ U : AffOp B.X, JUp C f g U (ι 0) t j.hom → RUp C f g U (ι 0) (t ≫ (cokernel.π j).hom) ρ.hom → ∀ (R : Type) [CommRing R] (φ : U.Bp →+* R), φ (cstBp U π) ∈ nonZeroDivisors R → ∀ (hw : ⊤ ≤ (spMap (φ.comp (g U)) ≫ (k.isAffineOpen U).fromSpec) ⁻¹ᵁ f.f ⁻¹ᵁ U.1) (r : ℕ) (e : Fin r → Γ(Om.V, U.1)), kerAt (spMap (φ.comp (g U)) ≫ (k.isAffineOpen U).fromSpec) ρ.hom hw (fun l => pullbackSections f.f Om.V le_rfl (e l)) = (C U).kerR φ fun l => 1 ⊗ₜ e l := by
  intro O _ _ _ p B B' Λ _ h o Lie Om π γ M C f g E ι Q t j ρ k hLie hι hQ U hJ hR R _ φ hφ hw r e
  have hV := k.isAffineOpen U
  haveI := hQ.1
  haveI := (hι 0).2.1
  haveI : ((pullA f.f).obj Lie).V.IsQuasicoherent := isQuasicoherent_pullback f.f Lie.V
  haveI : (cokernel j).V.IsQuasicoherent := isQuasicoherent_of_iso (Examples₂.cokV j).symm
  have hc := isColimitOfHasCokernelOfPreservesColimit (Action.forget B'.X.Modules Λ) j
  have hz : j.hom ≫ (cokernel.π j).hom = 0 := by
    rw [← Action.comp_hom, cokernel.condition]; rfl
  haveI : Epi (cokernel.π j).hom := inferInstanceAs (Epi ((Action.forget B'.X.Modules Λ).map (cokernel.π j)))
  have hex := exact_and_surjective_app_of_exact_of_epi (S := ShortComplex.mk _ _ hz)
    (ShortComplex.exact_of_g_is_cokernel _ hc) hV
  obtain ⟨q1, q2, -⟩ := hQ.2 _ hV
  have hL := ((hι 0).2.2 U).1
  rw [Nat.zero_min] at hL
  haveI := (GlobalTheory.T.vector_bundle_sections_finite_projective _ _ _ (hι 0).1 _ hV).2
  have ha : Submodule.span Γ(B'.X, f.f ⁻¹ᵁ U.1) (Set.range fun s => pullbackSections f.f Lie.V le_rfl s :
      Set Γ((Scheme.Modules.pullback f.f).obj Lie.V, f.f ⁻¹ᵁ U.1)) = ⊤ := by
    letI := appLEAlgebra f.f (le_refl (f.f ⁻¹ᵁ U.1))
    letI := appLEModule f.f ((Scheme.Modules.pullback f.f).obj Lie.V) (le_refl (f.f ⁻¹ᵁ U.1))
    haveI := appLE_isScalarTower f.f ((Scheme.Modules.pullback f.f).obj Lie.V) (le_refl (f.f ⁻¹ᵁ U.1))
    have hbc := isBaseChange_pullbackSections f.f Lie.V hV U.2.1 le_rfl
    refine eq_top_iff.2 fun x _ => ?_
    induction x using hbc.inductionOn with
    | zero => exact zero_mem _
    | tmul s => exact Submodule.subset_span ⟨s, rfl⟩
    | smul c x hx => exact Submodule.smul_mem _ _ (hx trivial)
    | add x y hx hy => exact add_mem (hx trivial) (hy trivial)
  have hb : Submodule.span U.Bp (Set.range fun s : Γ(Lie.V, U.1) => (1 ⊗ₜ s : SecBp Lie.V U)) = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    induction x using TensorProduct.induction_on with
    | zero => exact zero_mem _
    | tmul c s =>
      rw [← mul_one c, ← smul_eq_mul, ← TensorProduct.smul_tmul']
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, rfl⟩)
    | add x y hx hy => exact add_mem (hx trivial) (hy trivial)
  have hsp := span_eq (g U) φ (crd (ι 0) _) (appLinear t _) (appLinear (cokernel.π j).hom _) _ _ (k.map_cst U π)
    ((C U).L 0) ((C U).base_le 0) hL q2 (appLinear j.hom _) (C U).j hex.1 _ _ ha hb hJ
  have hbl : baseOf (resG B'.X le_top (f.f.appTop π)) h ≤ LinearMap.range (crd (ι 0) (f.f ⁻¹ᵁ U.1)) := fun v hv => by
    obtain ⟨u, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hv
    change _ ∈ latOf (ι 0) _
    rw [hL, Submodule.mem_comap, map_smulₛₗ, k.map_cst]
    exact (C U).base_le 0 (Submodule.smul_mem_pointwise_smul _ _ _ trivial)
  choose x y hy hρ hx using fun l => hR (e l)
  letI : Algebra Γ(B'.X, f.f ⁻¹ᵁ U.1) R := (φ.comp (g U)).toAlgebra
  ext c
  have h1 := (GlobalTheory.ChainPts.KerTens.main B'.X R _ _ ρ.hom _ r (fun l => pullbackSections f.f Om.V le_rfl (e l)) c).1 hV hw
  have h2 := GlobalTheory.T.tensor_relation_lattice_nonzerodivisor Γ(B'.X, f.f ⁻¹ᵁ U.1) R h _ _ (crd (ι 0) _) (appLinear (t ≫ (cokernel.π j).hom) _) _
    (crd_injective _ _) hbl (by rw [← k.map_cst] at hφ; exact hφ) (hex.2.comp q1) r x c
  refine h1.trans ?_
  have h3 : ∀ l, ρ.hom.app _ (pullbackSections f.f Om.V le_rfl (e l)) =
    appLinear (t ≫ (cokernel.π j).hom) _ (x l) := hx
  simp only [h3]
  refine h2.trans ?_
  have h4 : ∀ l, piMap (algebraMap Γ(B'.X, f.f ⁻¹ᵁ U.1) R) (Fin h) (crd (ι 0) _ (x l)) = piMap φ _ (y l).1 := fun l => by
    rw [hy]; rfl
  simp only [h4]
  refine (SetLike.ext_iff.1 hsp _).trans ⟨fun hh => ⟨y, hρ, hh⟩, fun ⟨y', hρ', hh⟩ => ?_⟩
  have h5 : ∑ l, c l • piMap φ _ (y l).1 = ∑ l, c l • piMap φ _ (y' l).1 + ∑ l, c l • piMap φ _ (y l - y' l).1 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Submodule.coe_sub, map_sub, ← smul_add, add_sub_cancel]
  rw [h5]
  refine add_mem hh (Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ?_, rfl⟩))
  rw [Submodule.Quotient.mk_sub]
  exact (Submodule.Quotient.eq _).1 ((hρ l).symm.trans (hρ' l))

end GlobalTheory.ChainDesc.KerRho
