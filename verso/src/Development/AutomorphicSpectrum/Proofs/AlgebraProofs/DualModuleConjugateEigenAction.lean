import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.EigCoordApply

open scoped NNReal
open NumberField GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Flat.ExG

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.ExG.DualRank

/- English proof (translation)
Use extensionality with `y`. Establish `key : ∀ t, t ≠ s' → φ (HT.eigProj ρ t y) = 0`. Introduce `t ht`. Establish `hmem` using `HT.LatBasic.mem_eigSp.1 (HT.LatBasic.eigProj_mem ρ t y)`. Establish `hex : ∃ a : 𝓞 E, t (a : E) ≠ s' (a : E)`.

Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `ht (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext hc))`. Take `⟨a, ha⟩` from `hex`. Establish `h1` using `LinearMap.congr_fun (hφ a) (HT.eigProj ρ t y)`.

Simplify using `only [LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul] at h1`. Rewrite `h1` using `[hmem a, map_smul, smul_eq_mul]`. Establish `h2 : (t (a : E) - s' (a : E)) * φ (HT.eigProj ρ t y) = 0`. Rewrite using `[sub_mul, h1, sub_self]`. Conclude with `(mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 ha)`.

Establish `e : φ y = φ (HT.eigProj ρ s' y)` using `by conv_lhs => rw [← hsum y]`. Rewrite using `[map_sum, Finset.sum_eq_single s' (fun t _ ht => key t ht) (by simp)]`. Conclude with `e.symm`.
-/
theorem comp_eigProj_eq {E : Type} [Field E] [NumberField E] {C : Type} [Field C]
    [Fintype (E →+* C)] {W : Type} [AddCommGroup W] [Module C W]
    {ρ : 𝓞 E →+* Module.End C W} {s' : E →+* C}
    (hsum : ∀ y, ∑ t, HT.eigProj ρ t y = y) {φ : Module.Dual C W}
    (hφ : ∀ a : 𝓞 E, φ ∘ₗ ρ a = s' (a : E) • φ) :
    φ ∘ₗ HT.eigProj ρ s' = φ := by
  classical
  ext y
  have key : ∀ t, t ≠ s' → φ (HT.eigProj ρ t y) = 0 := by
    intro t ht
    have hmem := HT.LatBasic.mem_eigSp.1 (HT.LatBasic.eigProj_mem ρ t y)
    have hex : ∃ a : 𝓞 E, t (a : E) ≠ s' (a : E) := by
      by_contra hc
      push_neg at hc
      exact ht (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext hc))
    obtain ⟨a, ha⟩ := hex
    have h1 := LinearMap.congr_fun (hφ a) (HT.eigProj ρ t y)
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul] at h1
    rw [hmem a, map_smul, smul_eq_mul] at h1
    have h2 : (t (a : E) - s' (a : E)) * φ (HT.eigProj ρ t y) = 0 := by
      rw [sub_mul, h1, sub_self]
    exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 ha)
  have e : φ y = φ (HT.eigProj ρ s' y) := by
    conv_lhs => rw [← hsum y]
    rw [map_sum, Finset.sum_eq_single s' (fun t _ ht => key t ht) (by simp)]
  exact e.symm

/- English proof (translation)
Introduce `E _ _ C _ _ bar s s' W _ _ _ ρ ρH hsum hs hbar hH`. Use `set U := HT.eigSp ρH s ⊓ LinearMap.ker (LinearMap.fst C W (Module.Dual C W)) with hU`. Use `set T := HT.eigSp ρ s' with hT`. Set `F : U →ₗ[C] Module.Dual C T` to `T.dualRestrict ∘ₗ LinearMap.snd C W (Module.Dual C W) ∘ₗ U.subtype`. Establish `hFapply : ∀ (u : U) (x : T), F u x = (u : W × Module.Dual C W).2 x` using `fun _ _ => rfl`.

Establish `hfst : ∀ u : U, (u : W × Module.Dual C W).1 = 0` using `fun u => u.2.2`. Establish `hact : ∀ u : U, ∀ a : 𝓞 E, (u : W × Module.Dual C W).2 ∘ₗ ρ a = s' (a : E) • (u : W × Module.Dual C W).2`. Introduce `u a`. Establish `h1` using `HT.LatBasic.mem_eigSp.1 u.2.1 (bar a)`. Establish `h2 : (u : W × Module.Dual C W) = (0, (u : W × Module.Dual C W).2)` using `Prod.ext (hfst u) rfl`.

Rewrite `h1` using `[h2, hH, hbar]`. Establish `h3` using `congrArg Prod.snd h1`. Simplify `h3` using `[hs a]`. Establish `hinj : Function.Injective F`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`.

Introduce `u hu`. Establish `h0` using `comp_eigProj_eq hsum (hact u)`. Apply `Subtype.ext` to reduce the goal to its premises. Use `Prod.ext (hfst u) ?_` and prove the remaining obligations. Rewrite using `[← h0]`.

Use extensionality with `y`. Use `hFapply u ⟨HT.eigProj ρ s' y, HT.LatBasic.eigProj_mem ρ s' y⟩` as an intermediate fact. Rewrite `this` using `[hu]`. Simplify using `using this.symm`. Establish `hsurj : Function.Surjective F`.

Introduce `ψ`. Set `e : W →ₗ[C] T` to `LinearMap.codRestrict T (HT.eigProj ρ s') (HT.LatBasic.eigProj_mem ρ s')`. Establish `he : ∀ (b : 𝓞 E) (x : W), e (ρ b x) = s' (b : E) • e x` using `fun b x => Subtype.ext (HodgeDeterminantLattice.eigProj_act s' b x)`. Establish `hmem : ((0 : W), ψ ∘ₗ e) ∈ U`. Use `⟨HT.LatBasic.mem_eigSp.2 fun a => ?_, rfl⟩` and prove the remaining obligations.

Rewrite using `[hH]`. Use `Prod.ext (by simp) ?_` and prove the remaining obligations. Use extensionality with `x`. Simplify using `[he, hs, hbar]`. Use `⟨⟨_, hmem⟩, ?_⟩` and prove the remaining obligations.

Use extensionality with `x`. Rewrite using `[hFapply]`. Establish `: e x = x` using `Subtype.ext (HT.LatBasic.eigProj_of_mem x.2)`. Simplify using `[this]`. Rewrite using `[(LinearEquiv.ofBijective F ⟨hinj, hsurj⟩).finrank_eq, Subspace.dual_finrank_eq]`.
-/
theorem finrank_eigSp_inf_ker_fst :
    ∀ (E : Type) [Field E] [NumberField E] (C : Type) [Field C] [Fintype (E →+* C)] (bar : 𝓞 E ≃+* 𝓞 E) (s s' : E →+* C) (W : Type) [AddCommGroup W] [Module C W] [FiniteDimensional C W] (ρ : 𝓞 E →+* Module.End C W) (ρH : 𝓞 E →+* Module.End C (W × Module.Dual C W)), (∀ y, ∑ t, HT.eigProj ρ t y = y) → (∀ a : 𝓞 E, s' (a : E) = s (bar a : 𝓞 E)) → (∀ a, bar (bar a) = a) → (∀ a φ, ρH a (0, φ) = (0, φ ∘ₗ ρ (bar a))) → Module.finrank C ↥(HT.eigSp ρH s ⊓ LinearMap.ker (LinearMap.fst C W (Module.Dual C W))) = Module.finrank C (HT.eigSp ρ s') := by
  intro E _ _ C _ _ bar s s' W _ _ _ ρ ρH hsum hs hbar hH
  set U := HT.eigSp ρH s ⊓ LinearMap.ker (LinearMap.fst C W (Module.Dual C W)) with hU
  set T := HT.eigSp ρ s' with hT
  let F : U →ₗ[C] Module.Dual C T :=
    T.dualRestrict ∘ₗ LinearMap.snd C W (Module.Dual C W) ∘ₗ U.subtype
  have hFapply : ∀ (u : U) (x : T), F u x = (u : W × Module.Dual C W).2 x := fun _ _ => rfl
  have hfst : ∀ u : U, (u : W × Module.Dual C W).1 = 0 := fun u => u.2.2
  have hact : ∀ u : U, ∀ a : 𝓞 E,
      (u : W × Module.Dual C W).2 ∘ₗ ρ a = s' (a : E) • (u : W × Module.Dual C W).2 := by
    intro u a
    have h1 := HT.LatBasic.mem_eigSp.1 u.2.1 (bar a)
    have h2 : (u : W × Module.Dual C W) = (0, (u : W × Module.Dual C W).2) :=
      Prod.ext (hfst u) rfl
    rw [h2, hH, hbar] at h1
    have h3 := congrArg Prod.snd h1
    simpa [hs a] using h3
  have hinj : Function.Injective F := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    have h0 := comp_eigProj_eq hsum (hact u)
    apply Subtype.ext
    refine Prod.ext (hfst u) ?_
    rw [← h0]
    ext y
    have := hFapply u ⟨HT.eigProj ρ s' y, HT.LatBasic.eigProj_mem ρ s' y⟩
    rw [hu] at this
    simpa using this.symm
  have hsurj : Function.Surjective F := by
    intro ψ
    let e : W →ₗ[C] T := LinearMap.codRestrict T (HT.eigProj ρ s') (HT.LatBasic.eigProj_mem ρ s')
    have he : ∀ (b : 𝓞 E) (x : W), e (ρ b x) = s' (b : E) • e x := fun b x =>
      Subtype.ext (HodgeDeterminantLattice.eigProj_act s' b x)
    have hmem : ((0 : W), ψ ∘ₗ e) ∈ U := by
      refine ⟨HT.LatBasic.mem_eigSp.2 fun a => ?_, rfl⟩
      rw [hH]
      refine Prod.ext (by simp) ?_
      ext x
      simp [he, hs, hbar]
    refine ⟨⟨_, hmem⟩, ?_⟩
    ext x
    rw [hFapply]
    have : e x = x := Subtype.ext (HT.LatBasic.eigProj_of_mem x.2)
    simp [this]
  rw [(LinearEquiv.ofBijective F ⟨hinj, hsurj⟩).finrank_eq, Subspace.dual_finrank_eq]

end GlobalTheory.CompanionTheory.Ar.Flat.ExG.DualRank
