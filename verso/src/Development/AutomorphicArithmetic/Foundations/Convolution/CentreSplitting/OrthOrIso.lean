import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.LocalRepresentationL2
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.InnerZero

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V
open private stab_orthRel from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.InnerZero

/- English proof (translation)
Establish `uniq : ∀ (x : M) (a b : U'), x - a ∈ C → x - b ∈ C → a = b` using `fun x a b ha hb => by`. Establish `h1 : (a : M) - b ∈ U' ⊓ C` using `⟨U'.sub_mem a.2 b.2, by simpa using C.sub_mem hb ha⟩`. Rewrite `h1` using `[hd, Submodule.mem_bot, sub_eq_zero]`. Conclude with `Subtype.ext h1`. Establish `ex : ∀ x : U, ∃ a : U', (x : M) - a ∈ C` using `fun x => by`.

Take `⟨a, ha, c, hc, e⟩` from `Submodule.mem_sup.1 (hle x.2)`. Conclude with `⟨⟨a, ha⟩, by rw [← e]; simpa using hc⟩`. Use `choose p hp using ex`. Set `P : U →ₗ[ℂ] U'` to `{ toFun := p map_add' := fun x y => uniq _ _ _ (hp _) (by`. Use `C.add_mem (hp x) (hp y)` as an intermediate fact.

Rewrite using `[sub_add_sub_comm] at this)` and apply the resulting hypothesis. Use the proof step `map_smul' := fun c x => uniq _ _ _ (hp _) (by`. Use `C.smul_mem c (hp x)` as an intermediate fact. Rewrite using `[smul_sub] at this) }` and apply the resulting hypothesis. Establish `hP : ∀ i (φ ψ : U), ψ.1 = A i φ.1 → (P ψ).1 = A i (P φ).1` using `fun i φ ψ e => congrArg Subtype.val (uniq ψ.1 (p ψ) ⟨_, hU' i _ (p φ).2⟩ (hp ψ) (by rw [e, ← map_sub]; exact hC i _ (hp φ)))`.

Break down `hi (U ⊓ C) inf_le_left fun i x hx => ⟨hU i x hx.1, hC i x hx.2⟩ with h0 | h0` into its components or cases. Establish `hinj : Function.Injective P` using `(injective_iff_map_eq_zero P).2 fun x hx => by`. Establish `h1` using `hp x`. Rewrite `h1` using `[show p x = 0 from hx]`. Establish `h2 : x.1 ∈ U ⊓ C` using `⟨x.2, by simpa using h1⟩`.

Rewrite `h2` using `[h0]`. Conclude with `Subtype.ext h2`. Break down `hi' ((LinearMap.range P).map U'.subtype) (Submodule.map_subtype_le _ _) (by` into its components or cases. Introduce and unpack `i _ ⟨_, ⟨x, rfl⟩, rfl⟩`. Conclude with `⟨_, ⟨⟨_, hU i _ x.2⟩, rfl⟩, hP i x _ rfl⟩) with h1 | h1`.

Use `Or.inl fun x hx => ?_` and prove the remaining obligations. Establish `h2 : (P ⟨x, hx⟩).1 ∈ (LinearMap.range P).map U'.subtype` using `⟨_, ⟨_, rfl⟩, rfl⟩`. Rewrite `h2` using `[h1, Submodule.mem_bot]`. Establish `h3` using `hp ⟨x, hx⟩`. Rewrite `h3` using `[show (p ⟨x, hx⟩).1 = 0 from h2]`.

Simplify using `using h3`. Use `Or.inr ⟨LinearEquiv.ofBijective P ⟨hinj, fun y => ?_⟩, hP⟩` and prove the remaining obligations. Take `⟨_, ⟨x, rfl⟩, e⟩` from `h1.ge y.2`. Conclude with `⟨x, Subtype.ext e⟩`. Conclude with `Or.inl (inf_eq_left.1 h0)`.
-/
private theorem le_or_iso {M I : Type} [AddCommGroup M] [Module ℂ M] (A : I → M →ₗ[ℂ] M) (U U' C : Submodule ℂ M)
    (hU : ∀ i, ∀ x ∈ U, A i x ∈ U) (hU' : ∀ i, ∀ x ∈ U', A i x ∈ U') (hC : ∀ i, ∀ x ∈ C, A i x ∈ C)
    (hi : ∀ W ≤ U, (∀ i, ∀ x ∈ W, A i x ∈ W) → W = ⊥ ∨ W = U) (hi' : ∀ W ≤ U', (∀ i, ∀ x ∈ W, A i x ∈ W) → W = ⊥ ∨ W = U')
    (hd : U' ⊓ C = ⊥) (hle : U ≤ U' ⊔ C) :
    U ≤ C ∨ ∃ T : U ≃ₗ[ℂ] U', ∀ i (φ ψ : U), ψ.1 = A i φ.1 → (T ψ).1 = A i (T φ).1 := by
  have uniq : ∀ (x : M) (a b : U'), x - a ∈ C → x - b ∈ C → a = b := fun x a b ha hb => by
    have h1 : (a : M) - b ∈ U' ⊓ C := ⟨U'.sub_mem a.2 b.2, by simpa using C.sub_mem hb ha⟩
    rw [hd, Submodule.mem_bot, sub_eq_zero] at h1
    exact Subtype.ext h1
  have ex : ∀ x : U, ∃ a : U', (x : M) - a ∈ C := fun x => by
    obtain ⟨a, ha, c, hc, e⟩ := Submodule.mem_sup.1 (hle x.2)
    exact ⟨⟨a, ha⟩, by rw [← e]; simpa using hc⟩
  choose p hp using ex
  let P : U →ₗ[ℂ] U' :=
    { toFun := p
      map_add' := fun x y => uniq _ _ _ (hp _) (by
        have := C.add_mem (hp x) (hp y)
        rwa [sub_add_sub_comm] at this)
      map_smul' := fun c x => uniq _ _ _ (hp _) (by
        have := C.smul_mem c (hp x)
        rwa [smul_sub] at this) }
  have hP : ∀ i (φ ψ : U), ψ.1 = A i φ.1 → (P ψ).1 = A i (P φ).1 := fun i φ ψ e =>
    congrArg Subtype.val (uniq ψ.1 (p ψ) ⟨_, hU' i _ (p φ).2⟩ (hp ψ) (by rw [e, ← map_sub]; exact hC i _ (hp φ)))
  rcases hi (U ⊓ C) inf_le_left fun i x hx => ⟨hU i x hx.1, hC i x hx.2⟩ with h0 | h0
  · have hinj : Function.Injective P := (injective_iff_map_eq_zero P).2 fun x hx => by
      have h1 := hp x
      rw [show p x = 0 from hx] at h1
      have h2 : x.1 ∈ U ⊓ C := ⟨x.2, by simpa using h1⟩
      rw [h0] at h2
      exact Subtype.ext h2
    rcases hi' ((LinearMap.range P).map U'.subtype) (Submodule.map_subtype_le _ _) (by
      rintro i _ ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨_, ⟨⟨_, hU i _ x.2⟩, rfl⟩, hP i x _ rfl⟩) with h1 | h1
    · refine Or.inl fun x hx => ?_
      have h2 : (P ⟨x, hx⟩).1 ∈ (LinearMap.range P).map U'.subtype := ⟨_, ⟨_, rfl⟩, rfl⟩
      rw [h1, Submodule.mem_bot] at h2
      have h3 := hp ⟨x, hx⟩
      rw [show (p ⟨x, hx⟩).1 = 0 from h2] at h3
      simpa using h3
    · refine Or.inr ⟨LinearEquiv.ofBijective P ⟨hinj, fun y => ?_⟩, hP⟩
      obtain ⟨_, ⟨x, rfl⟩, e⟩ := h1.ge y.2
      exact ⟨x, Subtype.ext e⟩
  · exact Or.inl (inf_eq_left.1 h0)

/- English proof (translation)
Introduce `K _ _ n μ _ U U' l l' hs hs' hi hi'`. Establish `hC` using `stab_orthRel (CuspidalSpectrum.cuspToL2 μ) (fun X a ha c hc => petersson_inner_lieAlgebra_skewAdjoint μ X ha hc) (fun k a ha c hc => petersson_inner_maximalCompact_invariant μ k ha hc) (fun g a ha c hc => petersson_inner_finiteAdelic_invariant μ g ha hc) l' hs'`. Establish `hsup` using `CuspidalSpectrum.sup_orthRel_centralCuspForms μ _ l' hs'.ρ hs'.τ`. Establish `hinf` using `inf_orthRel_eq_bot (ι := CuspidalSpectrum.cuspToL2 μ) l' fun a ha h0 => CuspidalSpectrum.eq_zero_of_cuspVecL_eq_zero (μ := μ) ha h0`. Set `A : ((isExpLieAlgebra K n).lieSubalgebra ⊕ archCompact K n ⊕ AdelicGLn.FiniteAdelicGL K n) → cuspForms K n →ₗ[ℂ] cuspForms K n` to `Sum.elim (fun X => (gkModuleCusp K n).ρ X) (Sum.elim (fun k => (gkModuleCusp K n).σ k) fun g => finRepCusp K n g)`.

Establish `hA : ∀ W, Fb.Stab W ↔ ∀ i, ∀ x ∈ W, A i x ∈ W` using `fun W => ⟨fun h i => by`. Break down `i with X | k | g` into its components or cases. Use `exacts [h.ρ X, h.σ k, h.τ g], fun h => ⟨fun X => h (.inl X), fun k => h (.inr (.inl k)), fun g => h (.inr (.inr g))⟩⟩`. Break down `le_or_iso A U U' _ ((hA _).1 hs) ((hA _).1 hs') ((hA _).1 hC) (fun W h1 h2 => hi W h1 ((hA _).2 h2)) (fun W h1 h2 => hi' W h1 ((hA _).2 h2)) hinf (l.trans hsup.ge) with h | ⟨T, hT⟩` into its components or cases. Use `Or.inl (Submodule.IsOrtho.symm ?_)` and prove the remaining obligations.

Rewrite using `[Submodule.isOrtho_iff_inner_eq]`. Introduce and unpack `_ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩`. Conclude with `(h hb).2 a ha`. Conclude with `Or.inr ⟨T, fun X => hT (.inl X), fun k => hT (.inr (.inl k)), fun g => hT (.inr (.inr g))⟩`.
-/
theorem UpperTheory.ConvolutionTheory.Dp.orthOrIso :
    UpperTheory.ConvolutionTheory.Dp.OrthOrIso := by
  intro K _ _ n μ _ U U' l l' hs hs' hi hi'
  have hC := stab_orthRel (CuspidalSpectrum.cuspToL2 μ) (fun X a ha c hc => petersson_inner_lieAlgebra_skewAdjoint μ X ha hc)
    (fun k a ha c hc => petersson_inner_maximalCompact_invariant μ k ha hc) (fun g a ha c hc => petersson_inner_finiteAdelic_invariant μ g ha hc) l' hs'
  have hsup := CuspidalSpectrum.sup_orthRel_centralCuspForms μ _ l' hs'.ρ hs'.τ
  have hinf := inf_orthRel_eq_bot (ι := CuspidalSpectrum.cuspToL2 μ) l' fun a ha h0 =>
    CuspidalSpectrum.eq_zero_of_cuspVecL_eq_zero (μ := μ) ha h0
  let A : ((isExpLieAlgebra K n).lieSubalgebra ⊕ archCompact K n ⊕ AdelicGLn.FiniteAdelicGL K n) → cuspForms K n →ₗ[ℂ] cuspForms K n :=
    Sum.elim (fun X => (gkModuleCusp K n).ρ X) (Sum.elim (fun k => (gkModuleCusp K n).σ k) fun g => finRepCusp K n g)
  have hA : ∀ W, Fb.Stab W ↔ ∀ i, ∀ x ∈ W, A i x ∈ W := fun W =>
    ⟨fun h i => by
      rcases i with X | k | g
      exacts [h.ρ X, h.σ k, h.τ g], fun h => ⟨fun X => h (.inl X), fun k => h (.inr (.inl k)), fun g => h (.inr (.inr g))⟩⟩
  rcases le_or_iso A U U' _ ((hA _).1 hs) ((hA _).1 hs') ((hA _).1 hC) (fun W h1 h2 => hi W h1 ((hA _).2 h2))
    (fun W h1 h2 => hi' W h1 ((hA _).2 h2)) hinf (l.trans hsup.ge) with h | ⟨T, hT⟩
  · refine Or.inl (Submodule.IsOrtho.symm ?_)
    rw [Submodule.isOrtho_iff_inner_eq]
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact (h hb).2 a ha
  · exact Or.inr ⟨T, fun X => hT (.inl X), fun k => hT (.inr (.inl k)), fun g => hT (.inr (.inr g))⟩
