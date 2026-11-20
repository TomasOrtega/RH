import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HodgeTateLatticePointFinrankTateModule
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPrimitiveIdempotentMapEqOne
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PadicUnitQuotientPrincipalBasis

open NumberField GlobalTheory.HTLat GlobalTheory.EigenSplit Classical
open scoped TensorProduct NNReal

namespace GlobalTheory.TateLocFree

/- English proof (translation)
Introduce `p _ C _ _ _ v O _ _ _ E _ _ _ P φ`. Use `haveI : IsDomain O := P.integers.hom_inj.isDomain (algebraMap O C)`. Take `⟨w, hw⟩` from `GlobalTheory.exists_placeU_mem_emb p (𝓞 E) O (embO P.integers φ)`. Take `⟨hdom, hpid, -⟩` from `GlobalTheory.PlaceMono.place_monogenic p (𝓞 E) w`. Set `A` to `ℤ_[p] ⊗[ℤ] 𝓞 E`.

Set `e : A` to `w.e`. Set `I : Ideal A` to `Ideal.span {1 - e}`. Use `letI : Module A P.T := Module.compHom P.T (tensorAction P.actT).toRingHom`. Establish `hsmul : ∀ (a : A) (t : P.T), a • t = tensorAction P.actT a t` using `fun _ _ => rfl`. Use `haveI : IsScalarTower ℤ_[p] A P.T := ⟨fun c a t => by`.

Rewrite using `[hsmul, hsmul, map_smul]`. Use the proof step `rfl⟩`. Set `M : Submodule A P.T` to `LinearMap.range (LinearMap.lsmul A P.T e)`. Establish `hee : e * e = e` using `w.idem`. Establish `hfix : ∀ m ∈ M, e • m = m`.

Introduce and unpack `_ ⟨t, rfl⟩`. Express the relevant statement in the definitionally equal form `e • e • t = e • t`. Rewrite using `[smul_smul, hee]`. Establish `htor : Module.IsTorsionBySet A M I`. Introduce `x a`.

Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.1 a.2`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[Submodule.coe_smul, ← hc, mul_smul, sub_smul, one_smul, hfix _ x.2, sub_self, smul_zero, Submodule.coe_zero]`. Use `letI : Module (A ⧸ I) M := htor.module`. Use `haveI : IsScalarTower A (A ⧸ I) M := htor.isScalarTower`.

Use `haveI : IsDomain (A ⧸ I) := hdom`. Use `haveI : IsPrincipalIdealRing (A ⧸ I) := hpid`. Use `haveI : IsNoetherianRing A := IsNoetherianRing.of_finite ℤ_[p] A`. Use `haveI : Module.Finite A P.T := Module.Finite.of_restrictScalars_finite ℤ_[p] A P.T`. Use `haveI : Module.Finite (A ⧸ I) M := Module.Finite.of_restrictScalars_finite A (A ⧸ I) M`.

Use `haveI : Module.Finite ℤ_[p] (A ⧸ I) := Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℤ_[p] I).toLinearMap (Ideal.Quotient.mkₐ_surjective ℤ_[p] I)`. Use `haveI : Module.IsTorsionFree (A ⧸ I) M := by`. Use `Module.IsTorsionFree.of_smul_eq_zero fun r m h => ?_` and prove the remaining obligations. Distinguish the cases in `hr : r = 0`. Conclude with `Or.inl hr`.

Use `right`. Establish `hne` using `Ideal.comap_ne_bot_of_integral_mem (R := ℤ_[p]) hr (Ideal.mem_span_singleton_self r) (Algebra.IsIntegral.isIntegral r)`. Take `⟨c, hc, hc0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hne`. Take `⟨s, hs⟩` from `Ideal.mem_span_singleton'.1 (Ideal.mem_comap.1 hc)`. Establish `h1 : (algebraMap ℤ_[p] A c) • (m : P.T) = 0`.

Establish `: (algebraMap ℤ_[p] (A ⧸ I) c) • m = 0` using `by rw [← hs, mul_smul, h, smul_zero]`. Establish `h2 : (((algebraMap ℤ_[p] (A ⧸ I) c) • m : M) : P.T) = 0` using `by rw [this]; rfl`. Conclude with `h2`. Rewrite `h1` using `[algebraMap_smul]`. Apply `Subtype.ext` to reduce the goal to its premises.

Conclude with `(smul_eq_zero.1 h1).resolve_left hc0`. Take `⟨n, b⟩` from `Module.basisOfFiniteTypeTorsionFree' (R := A ⧸ I) (M := M)`. Establish `hI : (I : Submodule A A) ≤ LinearMap.ker (LinearMap.mulLeft A e)`. Introduce `x hx`. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.1 hx`.

Rewrite using `[LinearMap.mem_ker, LinearMap.mulLeft_apply]`. Take the linear combination `c * (1 - hee)`. Set `liftE : (A ⧸ I) →ₗ[A] A` to `Submodule.liftQ I (LinearMap.mulLeft A e) hI`. Establish `hlift : ∀ (r : A ⧸ I) (m : M), liftE r • (m : P.T) = ((r • m : M) : P.T)`. Introduce `r m`.

Take `⟨x, rfl⟩` from `Ideal.Quotient.mk_surjective r`. Establish `h1 : liftE (Ideal.Quotient.mk I x) = e * x` using `Submodule.liftQ_apply _ _ _`. Rewrite using `[h1, mul_comm, mul_smul, hfix _ m.2]`. Both sides reduce to the same expression. Set `emap : P.T →ₗ[A] M` to `(LinearMap.lsmul A P.T e).rangeRestrict`.

Set `L : Fin n → (P.T →ₗ[A] A)` to `fun j => liftE ∘ₗ ((b.coord j).restrictScalars A) ∘ₗ emap`. Use `⟨n, fun j => (b j : P.T), fun j => (L j).restrictScalars ℤ_[p], e, ?_, hw, ?_⟩` and prove the remaining obligations. Introduce `j a t`. Establish `h1 : P.actT a t = (1 ⊗ₜ a : A) • t`. Rewrite using `[hsmul, tensorAction_tmul, one_smul]`.

Rewrite using `[LinearMap.restrictScalars_apply, LinearMap.restrictScalars_apply, h1, map_smul, smul_eq_mul]`. Introduce `t`. Establish `h0 : ((emap t : M) : P.T) = e • t` using `rfl`. Rewrite using `[← hsmul, ← h0, ← b.sum_repr (emap t), Submodule.coe_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[← hsmul, ← hlift]`. Both sides reduce to the same expression.
-/
theorem exists_place_decomp : ∀ {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C] [Algebra ℤ_[p] O] {E : Type} [Field E] [NumberField E] [StarRing (𝓞 E)] (P : Point p v O (𝓞 E)) (φ : E →+* C), ∃ (m : ℕ) (u : Fin m → P.T) (ℓ : Fin m → (P.T →ₗ[ℤ_[p]] ℤ_[p] ⊗[ℤ] 𝓞 E)) (e : ℤ_[p] ⊗[ℤ] 𝓞 E), (∀ j a t, ℓ j (P.actT a t) = (1 ⊗ₜ a) * ℓ j t) ∧ ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.tauExt (embO P.integers φ) e = 1 ∧ ∀ t, tensorAction P.actT e t = ∑ j, tensorAction P.actT (ℓ j t) (u j) := by
  intro p _ C _ _ _ v O _ _ _ E _ _ _ P φ
  haveI : IsDomain O := P.integers.hom_inj.isDomain (algebraMap O C)
  obtain ⟨w, hw⟩ := GlobalTheory.exists_placeU_mem_emb p (𝓞 E) O (embO P.integers φ)
  obtain ⟨hdom, hpid, -⟩ := GlobalTheory.PlaceMono.place_monogenic p (𝓞 E) w
  let A := ℤ_[p] ⊗[ℤ] 𝓞 E
  let e : A := w.e
  let I : Ideal A := Ideal.span {1 - e}
  letI : Module A P.T := Module.compHom P.T (tensorAction P.actT).toRingHom
  have hsmul : ∀ (a : A) (t : P.T), a • t = tensorAction P.actT a t := fun _ _ => rfl
  haveI : IsScalarTower ℤ_[p] A P.T := ⟨fun c a t => by
    rw [hsmul, hsmul, map_smul]; rfl⟩
  let M : Submodule A P.T := LinearMap.range (LinearMap.lsmul A P.T e)
  have hee : e * e = e := w.idem
  have hfix : ∀ m ∈ M, e • m = m := by
    rintro _ ⟨t, rfl⟩
    change e • e • t = e • t
    rw [smul_smul, hee]
  have htor : Module.IsTorsionBySet A M I := by
    intro x a
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 a.2
    apply Subtype.ext
    rw [Submodule.coe_smul, ← hc, mul_smul, sub_smul, one_smul, hfix _ x.2, sub_self, smul_zero,
      Submodule.coe_zero]
  letI : Module (A ⧸ I) M := htor.module
  haveI : IsScalarTower A (A ⧸ I) M := htor.isScalarTower
  haveI : IsDomain (A ⧸ I) := hdom
  haveI : IsPrincipalIdealRing (A ⧸ I) := hpid
  haveI : IsNoetherianRing A := IsNoetherianRing.of_finite ℤ_[p] A
  haveI : Module.Finite A P.T := Module.Finite.of_restrictScalars_finite ℤ_[p] A P.T
  haveI : Module.Finite (A ⧸ I) M := Module.Finite.of_restrictScalars_finite A (A ⧸ I) M
  haveI : Module.Finite ℤ_[p] (A ⧸ I) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℤ_[p] I).toLinearMap
      (Ideal.Quotient.mkₐ_surjective ℤ_[p] I)
  haveI : Module.IsTorsionFree (A ⧸ I) M := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun r m h => ?_
    by_cases hr : r = 0
    · exact Or.inl hr
    right
    have hne := Ideal.comap_ne_bot_of_integral_mem (R := ℤ_[p]) hr
      (Ideal.mem_span_singleton_self r) (Algebra.IsIntegral.isIntegral r)
    obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 (Ideal.mem_comap.1 hc)
    have h1 : (algebraMap ℤ_[p] A c) • (m : P.T) = 0 := by
      have : (algebraMap ℤ_[p] (A ⧸ I) c) • m = 0 := by rw [← hs, mul_smul, h, smul_zero]
      have h2 : (((algebraMap ℤ_[p] (A ⧸ I) c) • m : M) : P.T) = 0 := by rw [this]; rfl
      exact h2
    rw [algebraMap_smul] at h1
    apply Subtype.ext
    exact (smul_eq_zero.1 h1).resolve_left hc0
  obtain ⟨n, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := A ⧸ I) (M := M)
  have hI : (I : Submodule A A) ≤ LinearMap.ker (LinearMap.mulLeft A e) := by
    intro x hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    rw [LinearMap.mem_ker, LinearMap.mulLeft_apply]
    linear_combination c * (1 - hee)
  let liftE : (A ⧸ I) →ₗ[A] A := Submodule.liftQ I (LinearMap.mulLeft A e) hI
  have hlift : ∀ (r : A ⧸ I) (m : M), liftE r • (m : P.T) = ((r • m : M) : P.T) := by
    intro r m
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective r
    have h1 : liftE (Ideal.Quotient.mk I x) = e * x := Submodule.liftQ_apply _ _ _
    rw [h1, mul_comm, mul_smul, hfix _ m.2]
    rfl
  let emap : P.T →ₗ[A] M := (LinearMap.lsmul A P.T e).rangeRestrict
  let L : Fin n → (P.T →ₗ[A] A) := fun j => liftE ∘ₗ ((b.coord j).restrictScalars A) ∘ₗ emap
  refine ⟨n, fun j => (b j : P.T), fun j => (L j).restrictScalars ℤ_[p], e, ?_, hw, ?_⟩
  · intro j a t
    have h1 : P.actT a t = (1 ⊗ₜ a : A) • t := by
      rw [hsmul, tensorAction_tmul, one_smul]
    rw [LinearMap.restrictScalars_apply, LinearMap.restrictScalars_apply, h1, map_smul, smul_eq_mul]
  · intro t
    have h0 : ((emap t : M) : P.T) = e • t := rfl
    rw [← hsmul, ← h0, ← b.sum_repr (emap t), Submodule.coe_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hsmul, ← hlift]
    rfl
end GlobalTheory.TateLocFree
