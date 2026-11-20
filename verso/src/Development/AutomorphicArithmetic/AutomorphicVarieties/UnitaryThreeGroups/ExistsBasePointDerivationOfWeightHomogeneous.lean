import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.MopBase
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.DerExtend
open Matrix IsLocalRing UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.U3.Mop

/- English proof (translation)
Rewrite using `[MvPowerSeries.coeff_mul, Finsupp.antidiagonal_single, Finset.sum_map]`. Simplify using `[Finset.Nat.antidiagonal_succ, mul_comm]`.
-/
private theorem coeff_single_mul {E σ : Type} [CommRing E] (i : σ) (f g : MvPowerSeries σ E) :
    MvPowerSeries.coeff (Finsupp.single i 1) (f * g) =
      MvPowerSeries.constantCoeff f * MvPowerSeries.coeff (Finsupp.single i 1) g +
      MvPowerSeries.constantCoeff g * MvPowerSeries.coeff (Finsupp.single i 1) f := by
  classical
  rw [MvPowerSeries.coeff_mul, Finsupp.antidiagonal_single, Finset.sum_map]
  simp [Finset.Nat.antidiagonal_succ, mul_comm]

/- English proof (translation)
Set `W'` to `WPres.free O (fun _ : σ => (0 : ℤ))`. Establish `h' : W'.HasOrigin` using `fun f hf => by`. Establish `: f = 0` using `hf`. Rewrite using `[this, map_zero]`. Establish `ho : ∀ f, W'.origin h' f = MvPowerSeries.constantCoeff f` using `fun f => W'.origin_π h' f`.

Establish `h0` using `(der_extend O _ ℤ W' h' Q).2 (D - E) (fun f g => by`. Rewrite using `[ho, ho]`. Simplify using `only [LinearMap.sub_apply]`. Rewrite using `[hD, hE, smul_sub, smul_sub]`. Use the proof step `abel) (fun (s : σ) => by`.

Use `show D (MvPowerSeries.X s) - E (MvPowerSeries.X s) = 0`. Rewrite using `[hX, sub_self])`. Rewrite using `[sub_eq_zero.1 h0]`.
-/
private theorem free_ext {O σ Q : Type} [CommRing O] [Fintype σ] [AddCommGroup Q] [Module O Q]
    (D E : MvPowerSeries σ O →ₗ[O] Q)
    (hD : ∀ f g, D (f * g) = MvPowerSeries.constantCoeff f • D g + MvPowerSeries.constantCoeff g • D f)
    (hE : ∀ f g, E (f * g) = MvPowerSeries.constantCoeff f • E g + MvPowerSeries.constantCoeff g • E f)
    (hX : ∀ s, D (MvPowerSeries.X s) = E (MvPowerSeries.X s)) (f : MvPowerSeries σ O) : D f = E f := by
  let W' := WPres.free O (fun _ : σ => (0 : ℤ))
  have h' : W'.HasOrigin := fun f hf => by
    have : f = 0 := hf
    rw [this, map_zero]
  have ho : ∀ f, W'.origin h' f = MvPowerSeries.constantCoeff f := fun f => W'.origin_π h' f
  have h0 := (der_extend O _ ℤ W' h' Q).2 (D - E) (fun f g => by
    rw [ho, ho]
    simp only [LinearMap.sub_apply]
    rw [hD, hE, smul_sub, smul_sub]
    abel) (fun (s : σ) => by
    show D (MvPowerSeries.X s) - E (MvPowerSeries.X s) = 0
    rw [hX, sub_self])
  rw [sub_eq_zero.1 h0]

/- English proof (translation)
Set `L : MvPowerSeries σ O →ₗ[O] O` to `∑ s, (MvPowerSeries.coeff (Finsupp.single s 1) : MvPowerSeries σ O →ₗ[O] O).smulRight (d s)`. Establish `hL : ∀ f, L f = ∑ s, MvPowerSeries.coeff (Finsupp.single s 1) f • d s` using `fun f => by`. Simplify using `[L]`. Use `⟨L, fun f g => ?_, fun s => ?_, hL⟩` and prove the remaining obligations. Rewrite using `[hL, hL, hL]`.

Simplify using `only [coeff_single_mul, add_smul, mul_smul, Finset.sum_add_distrib, Finset.smul_sum]`. Rewrite using `[hL]`. Simplify using `[MvPowerSeries.coeff_X, Finsupp.single_left_inj]`.
-/
private theorem free_ex {O σ : Type} [CommRing O] [Fintype σ] (d : σ → O) :
    ∃ L : MvPowerSeries σ O →ₗ[O] O,
      (∀ f g, L (f * g) = MvPowerSeries.constantCoeff f • L g + MvPowerSeries.constantCoeff g • L f) ∧
      (∀ s, L (MvPowerSeries.X s) = d s) ∧
      ∀ f, L f = ∑ s, MvPowerSeries.coeff (Finsupp.single s 1) f • d s := by
  classical
  let L : MvPowerSeries σ O →ₗ[O] O :=
    ∑ s, (MvPowerSeries.coeff (Finsupp.single s 1) : MvPowerSeries σ O →ₗ[O] O).smulRight (d s)
  have hL : ∀ f, L f = ∑ s, MvPowerSeries.coeff (Finsupp.single s 1) f • d s := fun f => by
    simp [L]
  refine ⟨L, fun f g => ?_, fun s => ?_, hL⟩
  · rw [hL, hL, hL]
    simp only [coeff_single_mul, add_smul, mul_smul, Finset.sum_add_distrib, Finset.smul_sum]
  · rw [hL]
    simp [MvPowerSeries.coeff_X, Finsupp.single_left_inj]

/- English proof (translation)
Introduce `O B R S Q _ _ _ _ _ _ _ _ _ WB hB W h τ e hwt hker qh x₀ hx p hp j D hD hDw D₁ hD₁ hD₁w hpD`. Establish `hd : ∀ s : W.σ, ∃ d : O, (∀ t, s = e (.inl t) → d = D₁ (WB.z t)) ∧ (W.wt s ≠ j → d = 0) ∧ p d = D (qh (W.z s))` using `fun s => by`. Take `⟨u, rfl⟩` from `e.surjective s`. Break down `u with t | t` into its components or cases. Use `⟨D₁ (WB.z t), fun t' ht => ?_, fun hj => hD₁w t (by rwa [← hwt]), hpD t⟩` and prove the remaining obligations.

Rewrite using `[Sum.inl.inj (e.injective ht)]`. Distinguish the cases in `hj : W.wt (e (.inr t)) = j`. Take `⟨a, ha⟩` from `hp (D (qh (W.z (e (.inr t)))))`. Conclude with `⟨a, fun t' ht => absurd (e.injective ht) Sum.inr_ne_inl, fun h' => absurd hj h', ha⟩`. Conclude with `⟨0, fun t' ht => absurd (e.injective ht) Sum.inr_ne_inl, fun _ => rfl, by rw [map_zero, hDw _ hj]⟩`.

Use `choose d hd1 hd2 hd3 using hd`. Take `⟨L, hL, hLX, hLs⟩` from `free_ex d`. Establish `hren : ∀ g, L (MvPowerSeries.rename (fun s => e (.inl s)) g) = D₁ (WB.π g)` using `free_ext (L ∘ₗ (MvPowerSeries.rename (fun s => e (.inl s)) : MvPowerSeries WB.σ O →ₐ[O] _).toLinearMap) (D₁ ∘ₗ WB.π.toLinearMap) (fun f g => by`. Simplify using `only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_mul, hL, MvPowerSeries.constantCoeff_rename])`. Use the proof step `(fun f g => by`.

Establish `h1 : D₁ (WB.π f * WB.π g) = _` using `hD₁ _ _`. Simplify using `only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_mul, h1, WB.origin_π])`. Use the proof step `(fun s => by`. Simplify using `only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, MvPowerSeries.rename_X, hLX]`. Conclude with `hd1 _ s rfl)`.

Establish `hk : ∀ f, W.π f = 0 → L f = 0` using `fun f hf => by`. Establish `hf' : f ∈ RingHom.ker W.π` using `hf`. Establish `key : ∀ f ∈ (RingHom.ker WB.π).map (MvPowerSeries.rename fun s => e (.inl s)), L f = 0`. Introduce `f hf`. Proceed by induction on `hf using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨g, hg, rfl⟩` from `hx`. Establish `hg' : WB.π g = 0` using `hg`. Rewrite using `[hren, hg', map_zero]`. Consider the case `zero => exact map_zero L`.

Consider the case `add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]`. Consider the case `smul a x hx hx'`. Establish `: x ∈ RingHom.ker W.π` using `by rw [hker]; exact hx`. Rewrite using `[smul_eq_mul, hL, hx', h x this, smul_zero, zero_smul, add_zero]`. Conclude with `key f (hker ▸ hf')`.

Establish `hs : Function.Surjective W.π.toLinearMap` using `W.surj`. Set `E : R →ₗ[O] O` to `((LinearMap.ker W.π.toLinearMap).liftQ L (fun f hf => hk f hf)) ∘ₗ (W.π.toLinearMap.quotKerEquivOfSurjective hs).symm.toLinearMap`. Establish `hE : ∀ f, E (W.π f) = L f` using `fun f => by`. Establish `: (W.π.toLinearMap.quotKerEquivOfSurjective hs).symm (W.π f) = Submodule.Quotient.mk f`. Rewrite using `[LinearEquiv.symm_apply_eq]`.

Both sides reduce to the same expression. Use `show (LinearMap.ker W.π.toLinearMap).liftQ L (fun f hf => hk f hf) ((W.π.toLinearMap.quotKerEquivOfSurjective hs).symm (W.π f)) = _`. Rewrite using `[this]`. Both sides reduce to the same expression. Establish `hEd : ∀ a b, E (a * b) = W.origin h a • E b + W.origin h b • E a` using `fun a b => by`.

Take `⟨f, rfl⟩` from `W.surj a`. Take `⟨g, rfl⟩` from `W.surj b`. Rewrite using `[← map_mul, hE, hE, hE, hL, W.origin_π, W.origin_π]`. Establish `hxo : ∀ f, x₀ (qh (W.π f)) = MvPowerSeries.constantCoeff f` using `fun f => by`. Rewrite using `[← AlgHom.comp_apply, hx, W.origin_π]`.

Establish `hred : ∀ f, D (qh (W.π f)) = p (L f)` using `free_ext (D ∘ₗ (qh.comp W.π).toLinearMap) (p ∘ₗ L) (fun f g => by`. Establish `h1 : D (qh (W.π f) * qh (W.π g)) = _` using `hD _ _`. Simplify using `only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply, map_mul, h1, hxo])`. Use the proof step `(fun f g => by simp only [LinearMap.comp_apply, hL, map_add, map_smul])`. Use the proof step `(fun s => by`.

Simplify using `only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply, hLX, hd3]`. Use the proof step `rfl)`. Use `⟨E ∘ₗ W.A.val.toLinearMap, fun a b => hEd a b, fun i hi a ha => ?_, fun a => ?_⟩` and prove the remaining obligations. Take `⟨f, hf, hfa⟩` from `ha`. Establish `hfa' : W.π f = (a : R)` using `hfa`.

Use `show E (a : R) = 0`. Rewrite using `[← hfa', hE, hLs]`. Use `Finset.sum_eq_zero fun s _ => ?_` and prove the remaining obligations. Distinguish the cases in `hs : W.wt s = j`. Rewrite using `[hf (Finsupp.single s 1) (by simpa [Finsupp.weight_single, hs] using hi.symm), zero_smul]`.

Rewrite using `[hd2 s hs, smul_zero]`. Take `⟨f, hf⟩` from `W.surj (a : R) show D (qh (a : R)) = p (E (a : R))`. Rewrite using `[← hf, hE, hred]`.
-/
theorem UpperTheory.exists_base_pointDerivation_of_weight_homogeneous :
    ∀ {O B R S Q : Type} [CommRing O] [CommRing B] [Algebra O B] [CommRing R] [Algebra O R] [CommRing S] [Algebra O S] [AddCommGroup Q] [Module O Q]
          (WB : WPres O ℤ B) (hB : WB.HasOrigin) (W : WPres O ℤ R) (h : W.HasOrigin) {τ : Type} (e : WB.σ ⊕ τ ≃ W.σ), (∀ s, W.wt (e (.inl s)) = WB.wt s) →
          RingHom.ker W.π = (RingHom.ker WB.π).map (MvPowerSeries.rename fun s => e (.inl s)) →
          ∀ (qh : R →ₐ[O] S) (x₀ : S →ₐ[O] O), x₀.comp qh = W.origin h → ∀ (p : O →ₗ[O] Q), Function.Surjective p → ∀ (j : ℤ),
          ∀ D ∈ PtDer x₀ Q, (∀ s, W.wt s ≠ j → D (qh (W.z s)) = 0) → ∀ D₁ ∈ PtDer (WB.origin hB) O, (∀ s, WB.wt s ≠ j → D₁ (WB.z s) = 0) →
          (∀ s, p (D₁ (WB.z s)) = D (qh (W.z (e (.inl s))))) →
          ∃ D' ∈ PtDer (W.originA h) O, HasWt W.gr j D' ∧ ∀ f : W.A, D (qh f) = p (D' f) := by
  intro O B R S Q _ _ _ _ _ _ _ _ _ WB hB W h τ e hwt hker qh x₀ hx p hp j D hD hDw D₁ hD₁ hD₁w hpD
  classical
  have hd : ∀ s : W.σ, ∃ d : O, (∀ t, s = e (.inl t) → d = D₁ (WB.z t)) ∧ (W.wt s ≠ j → d = 0) ∧
      p d = D (qh (W.z s)) := fun s => by
    obtain ⟨u, rfl⟩ := e.surjective s
    rcases u with t | t
    · refine ⟨D₁ (WB.z t), fun t' ht => ?_, fun hj => hD₁w t (by rwa [← hwt]), hpD t⟩
      rw [Sum.inl.inj (e.injective ht)]
    · by_cases hj : W.wt (e (.inr t)) = j
      · obtain ⟨a, ha⟩ := hp (D (qh (W.z (e (.inr t)))))
        exact ⟨a, fun t' ht => absurd (e.injective ht) Sum.inr_ne_inl, fun h' => absurd hj h', ha⟩
      · exact ⟨0, fun t' ht => absurd (e.injective ht) Sum.inr_ne_inl, fun _ => rfl,
          by rw [map_zero, hDw _ hj]⟩
  choose d hd1 hd2 hd3 using hd
  obtain ⟨L, hL, hLX, hLs⟩ := free_ex d
  have hren : ∀ g, L (MvPowerSeries.rename (fun s => e (.inl s)) g) = D₁ (WB.π g) :=
    free_ext (L ∘ₗ (MvPowerSeries.rename (fun s => e (.inl s)) : MvPowerSeries WB.σ O →ₐ[O] _).toLinearMap)
      (D₁ ∘ₗ WB.π.toLinearMap)
      (fun f g => by
        simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_mul, hL,
          MvPowerSeries.constantCoeff_rename])
      (fun f g => by
        have h1 : D₁ (WB.π f * WB.π g) = _ := hD₁ _ _
        simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_mul, h1, WB.origin_π])
      (fun s => by
        simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, MvPowerSeries.rename_X, hLX]
        exact hd1 _ s rfl)
  have hk : ∀ f, W.π f = 0 → L f = 0 := fun f hf => by
    have hf' : f ∈ RingHom.ker W.π := hf
    have key : ∀ f ∈ (RingHom.ker WB.π).map (MvPowerSeries.rename fun s => e (.inl s)), L f = 0 := by
      intro f hf
      induction hf using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨g, hg, rfl⟩ := hx
        have hg' : WB.π g = 0 := hg
        rw [hren, hg', map_zero]
      | zero => exact map_zero L
      | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
      | smul a x hx hx' =>
        have : x ∈ RingHom.ker W.π := by rw [hker]; exact hx
        rw [smul_eq_mul, hL, hx', h x this, smul_zero, zero_smul, add_zero]
    exact key f (hker ▸ hf')
  have hs : Function.Surjective W.π.toLinearMap := W.surj
  let E : R →ₗ[O] O := ((LinearMap.ker W.π.toLinearMap).liftQ L (fun f hf => hk f hf)) ∘ₗ
    (W.π.toLinearMap.quotKerEquivOfSurjective hs).symm.toLinearMap
  have hE : ∀ f, E (W.π f) = L f := fun f => by
    have : (W.π.toLinearMap.quotKerEquivOfSurjective hs).symm (W.π f) = Submodule.Quotient.mk f := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    show (LinearMap.ker W.π.toLinearMap).liftQ L (fun f hf => hk f hf)
      ((W.π.toLinearMap.quotKerEquivOfSurjective hs).symm (W.π f)) = _
    rw [this]
    rfl
  have hEd : ∀ a b, E (a * b) = W.origin h a • E b + W.origin h b • E a := fun a b => by
    obtain ⟨f, rfl⟩ := W.surj a
    obtain ⟨g, rfl⟩ := W.surj b
    rw [← map_mul, hE, hE, hE, hL, W.origin_π, W.origin_π]
  have hxo : ∀ f, x₀ (qh (W.π f)) = MvPowerSeries.constantCoeff f := fun f => by
    rw [← AlgHom.comp_apply, hx, W.origin_π]
  have hred : ∀ f, D (qh (W.π f)) = p (L f) :=
    free_ext (D ∘ₗ (qh.comp W.π).toLinearMap) (p ∘ₗ L)
      (fun f g => by
        have h1 : D (qh (W.π f) * qh (W.π g)) = _ := hD _ _
        simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply, map_mul, h1, hxo])
      (fun f g => by simp only [LinearMap.comp_apply, hL, map_add, map_smul])
      (fun s => by
        simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply, hLX, hd3]
        rfl)
  refine ⟨E ∘ₗ W.A.val.toLinearMap, fun a b => hEd a b, fun i hi a ha => ?_, fun a => ?_⟩
  · obtain ⟨f, hf, hfa⟩ := ha
    have hfa' : W.π f = (a : R) := hfa
    show E (a : R) = 0
    rw [← hfa', hE, hLs]
    refine Finset.sum_eq_zero fun s _ => ?_
    by_cases hs : W.wt s = j
    · rw [hf (Finsupp.single s 1) (by simpa [Finsupp.weight_single, hs] using hi.symm), zero_smul]
    · rw [hd2 s hs, smul_zero]
  · obtain ⟨f, hf⟩ := W.surj (a : R)
    show D (qh (a : R)) = p (E (a : R))
    rw [← hf, hE, hred]
