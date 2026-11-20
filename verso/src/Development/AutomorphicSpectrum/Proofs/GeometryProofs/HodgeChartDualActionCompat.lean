import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsExtendLin
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat.HTL

/- English proof (translation)
Introduce `A K _ _ _ _ _ _ _ E _ _ c hc p R N _ Li _ _ D ρ hact σ m hproj hsurj`. Establish `hp : (p : K) ≠ 0` using `Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero`. Establish `hpm : ((p : K) ^ m) ≠ 0` using `pow_ne_zero _ hp`. Establish `hmemM : ∀ w ∈ D.om', eigProj D.ρΩ σ w ∈ D.omHT σ` using `fun w hw => ⟨w, hw, rfl⟩`. Establish `hh : ∀ i : Fin N, D.h (Pi.single i 1) ∈ D.om'` using `fun i => Submodule.mem_sup_left (Submodule.subset_span ⟨_, rfl⟩)`.

Set `v : Fin N → D.omHT σ` to `fun i => ⟨eigProj D.ρΩ σ (D.h (Pi.single i 1)), hmemM _ (hh i)⟩`. Set `Q : (Fin N → A) →ₗ[A] D.omHT σ` to `Fintype.linearCombination A v`. Establish `hQ : ∀ x, ((Q x : D.omHT σ) : Module.Dual K Li) = D.q σ x`. Introduce `x`. Simplify using `[Q, Fintype.linearCombination_apply, HTChart.q, v]`.

Set `P : Submodule A (D.omHT σ)` to `LinearMap.range (((p : A) ^ m) • (LinearMap.id : D.omHT σ →ₗ[A] D.omHT σ))`. Establish `hsurjQ : Function.Surjective (P.mkQ ∘ₗ Q)`. Introduce `y`. Take `⟨z, rfl⟩` from `P.mkQ_surjective y`. Take `⟨x, y', hy', h⟩` from `hsurj z z.2`.

Use `⟨x, ?_⟩` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, Submodule.mkQ_apply]`. Rewrite using `[Submodule.Quotient.eq]`. Use `⟨-⟨y', hy'⟩, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises.

Simplify using `[hQ, h]`. Take `⟨r, hr⟩` from `Module.projective_lifting_property (P.mkQ ∘ₗ Q) P.mkQ hsurjQ`. Establish `hr' : ∀ z : D.omHT σ, ∃ z' : D.omHT σ, Q (r z) = z + ((p : A) ^ m) • z'`. Introduce `z`. Use `LinearMap.congr_fun hr z` as an intermediate fact.

Simplify using `only [LinearMap.comp_apply, Submodule.mkQ_apply] at this`. Rewrite `this` using `[Submodule.Quotient.eq]`. Take `⟨z', hz'⟩` from `this`. Use `⟨z', ?_⟩` and prove the remaining obligations. Simplify using `only [LinearMap.smul_apply, LinearMap.id_apply] at hz'`.

Rewrite using `[hz']`. Normalize the expressions using the abelian group laws. Establish `hvec` using `fun k => HTL.exists_vec D ρ hc hact σ ((LinearMap.proj k) ∘ₗ r)`. Use `choose ev hev hevz using hvec`. Set `Rr : (Fin N → K) →ₗ[K] Li` to `Fintype.linearCombination K ev`.

Establish `hRr : ∀ x, Rr x = ∑ k, x k • ev k` using `fun x => by simp [Rr, Fintype.linearCombination_apply]`. Establish `hzL : ∀ e ∈ HTL.latOn D (GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ (σ.comp c.toRingHom)) 1 (algebraMap A K).range, ∀ z : D.omHT σ, (z : Module.Dual K Li) e ∈ (algebraMap A K).range`. Introduce `e he z`. Take `⟨w, hw, hz⟩` from `z.2`. Establish `hz' : eigProj D.ρΩ σ w = z` using `hz`.

Rewrite using `[← hz', eigProj_apply D ρ hc hact σ he.1 w]`. Simplify using `using he.2 w hw`. Use `⟨Rr, fun k => ?_, fun e he => ?_⟩` and prove the remaining obligations. Establish `h1 : Rr (Pi.single k 1) = ev k` using `by simp [hRr, Pi.single_apply]`. Rewrite using `[h1]`.

Use `⟨hev k, fun w hw => ?_⟩` and prove the remaining obligations. Rewrite using `[one_mul, ← eigProj_apply D ρ hc hact σ (hev k) w]`. Conclude with `⟨_, (hevz k ⟨_, hmemM w hw⟩).symm⟩`. Set `x : Fin N → K` to `fun l => D.h (Pi.single l 1) e`. Establish `hRx : Rr x ∈ GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ (σ.comp c.toRingHom)`.

Rewrite using `[hRr]`. Conclude with `Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hev k)`. Establish `key : ∀ z : D.omHT σ, ∃ z' : D.omHT σ, (z : Module.Dual K Li) (Rr x) = (z : Module.Dual K Li) e + (p : K) ^ m * (z' : Module.Dual K Li) e`. Introduce `z`. Take `⟨z', hz'⟩` from `hr' z`.

Use `⟨z', ?_⟩` and prove the remaining obligations. Establish `h1 : (z : Module.Dual K Li) (Rr x) = ∑ k, x k * algebraMap A K (r z k)`. Rewrite using `[hRr, map_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, hevz k z]`.

Both sides reduce to the same expression. Establish `h2 : ((Q (r z) : D.omHT σ) : Module.Dual K Li) e = ∑ k, algebraMap A K (r z k) * x k`. Rewrite using `[hQ, HTChart.q, LinearMap.sum_apply]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.smul_apply, eigProj_apply D ρ hc hact σ he.1, Algebra.smul_def]`.

Establish `h3 : ((Q (r z) : D.omHT σ) : Module.Dual K Li) e = (z : Module.Dual K Li) e + (p : K) ^ m * (z' : Module.Dual K Li) e`. Rewrite using `[hz']`. Simplify using `[Algebra.smul_def]`. Rewrite using `[h1, ← h3, h2]`. Conclude with `Finset.sum_congr rfl fun k _ => mul_comm _ _`.

Establish `hsub` using `Submodule.sub_mem _ hRx he.1`. Use `⟨((p : K) ^ m)⁻¹ • (Rr x - e), ⟨Submodule.smul_mem _ _ hsub, fun w hw => ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[one_mul, ← eigProj_apply D ρ hc hact σ (Submodule.smul_mem _ _ hsub) w]`. Take `⟨z', hz'⟩` from `key ⟨_, hmemM w hw⟩`. Establish `hval : eigProj D.ρΩ σ w (((p : K) ^ m)⁻¹ • (Rr x - e)) = (z' : Module.Dual K Li) e`.

Rewrite using `[map_smul, map_sub]`. Establish `: eigProj D.ρΩ σ w (Rr x) = eigProj D.ρΩ σ w e + (p : K) ^ m * (z' : Module.Dual K Li) e` using `hz'`. Rewrite using `[this, add_sub_cancel_left, smul_eq_mul, inv_mul_cancel_left₀ hpm]`. Rewrite using `[hval]`. Conclude with `hzL e he z'`.

Rewrite using `[smul_smul, mul_inv_cancel₀ hpm, one_smul]`. Normalize the expressions using the abelian group laws.
-/
theorem exists_retraction_mod : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Li : Type) [AddCommGroup Li] [Module K Li] (D : HTChart A K c p R N (Module.Dual K Li)) (ρ : 𝓞 E →+* Module.End K Li), (∀ (a : 𝓞 E) (w : Module.Dual K Li), D.ρΩ a w = w ∘ₗ ρ (RingOfIntegers.mapRingEquiv c a)) → ∀ (σ : E →+* K) (m : ℕ), Module.Projective A (D.omHT σ) → (∀ y ∈ D.omHT σ, ∃ x : Fin N → A, ∃ y' ∈ D.omHT σ, y = D.q σ x + ((p : A) ^ m) • y') → ∃ Rr : (Fin N → K) →ₗ[K] Li, (∀ k, Rr (Pi.single k 1) ∈ HTL.latOn D (GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ (σ.comp c.toRingHom)) 1 (algebraMap A K).range) ∧ ∀ e ∈ HTL.latOn D (GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ (σ.comp c.toRingHom)) 1 (algebraMap A K).range, ∃ e' ∈ HTL.latOn D (GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ (σ.comp c.toRingHom)) 1 (algebraMap A K).range, Rr (fun l => D.h (Pi.single l 1) e) = e + ((p : K) ^ m) • e' := by
  intro A K _ _ _ _ _ _ _ E _ _ c hc p R N _ Li _ _ D ρ hact σ m hproj hsurj
  classical
  have hp : (p : K) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hpm : ((p : K) ^ m) ≠ 0 := pow_ne_zero _ hp
  have hmemM : ∀ w ∈ D.om', eigProj D.ρΩ σ w ∈ D.omHT σ := fun w hw => ⟨w, hw, rfl⟩
  have hh : ∀ i : Fin N, D.h (Pi.single i 1) ∈ D.om' := fun i =>
    Submodule.mem_sup_left (Submodule.subset_span ⟨_, rfl⟩)
  let v : Fin N → D.omHT σ := fun i => ⟨eigProj D.ρΩ σ (D.h (Pi.single i 1)), hmemM _ (hh i)⟩
  let Q : (Fin N → A) →ₗ[A] D.omHT σ := Fintype.linearCombination A v
  have hQ : ∀ x, ((Q x : D.omHT σ) : Module.Dual K Li) = D.q σ x := by
    intro x
    simp [Q, Fintype.linearCombination_apply, HTChart.q, v]
  let P : Submodule A (D.omHT σ) := LinearMap.range (((p : A) ^ m) • (LinearMap.id : D.omHT σ →ₗ[A] D.omHT σ))
  have hsurjQ : Function.Surjective (P.mkQ ∘ₗ Q) := by
    intro y
    obtain ⟨z, rfl⟩ := P.mkQ_surjective y
    obtain ⟨x, y', hy', h⟩ := hsurj z z.2
    refine ⟨x, ?_⟩
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply]
    rw [Submodule.Quotient.eq]
    refine ⟨-⟨y', hy'⟩, ?_⟩
    apply Subtype.ext
    simp [hQ, h]
  obtain ⟨r, hr⟩ := Module.projective_lifting_property (P.mkQ ∘ₗ Q) P.mkQ hsurjQ
  have hr' : ∀ z : D.omHT σ, ∃ z' : D.omHT σ, Q (r z) = z + ((p : A) ^ m) • z' := by
    intro z
    have := LinearMap.congr_fun hr z
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply] at this
    rw [Submodule.Quotient.eq] at this
    obtain ⟨z', hz'⟩ := this
    refine ⟨z', ?_⟩
    simp only [LinearMap.smul_apply, LinearMap.id_apply] at hz'
    rw [hz']; abel
  have hvec := fun k => HTL.exists_vec D ρ hc hact σ ((LinearMap.proj k) ∘ₗ r)
  choose ev hev hevz using hvec
  let Rr : (Fin N → K) →ₗ[K] Li := Fintype.linearCombination K ev
  have hRr : ∀ x, Rr x = ∑ k, x k • ev k := fun x => by simp [Rr, Fintype.linearCombination_apply]
  have hzL : ∀ e ∈ HTL.latOn D (GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ (σ.comp c.toRingHom)) 1 (algebraMap A K).range,
      ∀ z : D.omHT σ, (z : Module.Dual K Li) e ∈ (algebraMap A K).range := by
    intro e he z
    obtain ⟨w, hw, hz⟩ := z.2
    have hz' : eigProj D.ρΩ σ w = z := hz
    rw [← hz', eigProj_apply D ρ hc hact σ he.1 w]
    simpa using he.2 w hw
  refine ⟨Rr, fun k => ?_, fun e he => ?_⟩
  · have h1 : Rr (Pi.single k 1) = ev k := by simp [hRr, Pi.single_apply]
    rw [h1]
    refine ⟨hev k, fun w hw => ?_⟩
    rw [one_mul, ← eigProj_apply D ρ hc hact σ (hev k) w]
    exact ⟨_, (hevz k ⟨_, hmemM w hw⟩).symm⟩
  · let x : Fin N → K := fun l => D.h (Pi.single l 1) e
    have hRx : Rr x ∈ GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ (σ.comp c.toRingHom) := by
      rw [hRr]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hev k)
    have key : ∀ z : D.omHT σ, ∃ z' : D.omHT σ, (z : Module.Dual K Li) (Rr x) =
        (z : Module.Dual K Li) e + (p : K) ^ m * (z' : Module.Dual K Li) e := by
      intro z
      obtain ⟨z', hz'⟩ := hr' z
      refine ⟨z', ?_⟩
      have h1 : (z : Module.Dual K Li) (Rr x) = ∑ k, x k * algebraMap A K (r z k) := by
        rw [hRr, map_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [map_smul, hevz k z]
        rfl
      have h2 : ((Q (r z) : D.omHT σ) : Module.Dual K Li) e = ∑ k, algebraMap A K (r z k) * x k := by
        rw [hQ, HTChart.q, LinearMap.sum_apply]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [LinearMap.smul_apply, eigProj_apply D ρ hc hact σ he.1, Algebra.smul_def]
      have h3 : ((Q (r z) : D.omHT σ) : Module.Dual K Li) e =
          (z : Module.Dual K Li) e + (p : K) ^ m * (z' : Module.Dual K Li) e := by
        rw [hz']
        simp [Algebra.smul_def]
      rw [h1, ← h3, h2]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    have hsub := Submodule.sub_mem _ hRx he.1
    refine ⟨((p : K) ^ m)⁻¹ • (Rr x - e), ⟨Submodule.smul_mem _ _ hsub, fun w hw => ?_⟩, ?_⟩
    · rw [one_mul, ← eigProj_apply D ρ hc hact σ (Submodule.smul_mem _ _ hsub) w]
      obtain ⟨z', hz'⟩ := key ⟨_, hmemM w hw⟩
      have hval : eigProj D.ρΩ σ w (((p : K) ^ m)⁻¹ • (Rr x - e)) = (z' : Module.Dual K Li) e := by
        rw [map_smul, map_sub]
        have : eigProj D.ρΩ σ w (Rr x) = eigProj D.ρΩ σ w e + (p : K) ^ m * (z' : Module.Dual K Li) e := hz'
        rw [this, add_sub_cancel_left, smul_eq_mul, inv_mul_cancel_left₀ hpm]
      rw [hval]
      exact hzL e he z'
    · rw [smul_smul, mul_inv_cancel₀ hpm, one_smul]
      abel

end GlobalTheory.CompanionTheory.Ar.Flat.HTL
