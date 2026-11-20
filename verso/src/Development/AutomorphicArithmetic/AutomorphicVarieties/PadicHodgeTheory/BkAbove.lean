import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IotaSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DecJFacts
open Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc Topology NumberField IsDedekindDomain

/- English proof (translation)
Use `haveI : Fintype (G ⧸ H) := Fintype.ofFinite _`. Use `set f' : G → W := fun g => f g - (a g x - x) with hf'`. Establish `hc : ∀ g h, f' (g * h) = f' g + a g (f' h)`. Introduce `g h`. Simplify using `only [hf', hf, hmul, map_sub]`.

Normalize the expressions using the abelian group laws. Establish `hH : ∀ g h, h ∈ H → f' (g * h) = f' g`. Introduce `g h hh`. Rewrite using `[hc]`. Establish `: f' h = 0` using `by simp only [hf', hx h hh, sub_self]`.

Rewrite using `[this, map_zero, add_zero]`. Set `F : G ⧸ H → W` to `Quotient.lift f' (by`. Introduce `g g' hgg`. Establish `h1 : g⁻¹ * g' ∈ H` using `QuotientGroup.leftRel_apply.1 hgg`. Use `hH g _ h1` as an intermediate fact.

Rewrite `this` using `[mul_inv_cancel_left]`. Conclude with `this.symm)`. Establish `hF : ∀ (g : G) (q : G ⧸ H), F (g • q) = f' g + a g (F q)`. Introduce `g q`. Proceed by induction on `q using QuotientGroup.induction_on with`.

Consider the case `H z => exact hc g z`. Use `set S : W := ∑ q, F q with hS`. Establish `hsum : ∀ g, S = (Fintype.card (G ⧸ H) : k) • f' g + a g S`. Introduce `g`. Establish `e1 : ∑ q, F (g • q) = S` using `Equiv.sum_comp (MulAction.toPerm g) F`.

Use `e1.symm.trans ?_` and prove the remaining obligations. Simplify using `only [hF, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ← map_sum, Nat.cast_smul_eq_nsmul, ← hS]`. Establish `hn : (Fintype.card (G ⧸ H) : k) ≠ 0` using `Nat.cast_ne_zero.2 Fintype.card_ne_zero`. Use `⟨x - (Fintype.card (G ⧸ H) : k)⁻¹ • S, fun g => ?_⟩` and prove the remaining obligations. Establish `e : f' g = (Fintype.card (G ⧸ H) : k)⁻¹ • (S - a g S)`.

Rewrite using `[eq_inv_smul_iff₀ hn, eq_sub_iff_add_eq]`. Conclude with `(hsum g).symm`. Establish `e2 : f g = f' g + (a g x - x)` using `by simp only [hf', sub_add_cancel]`. Rewrite using `[e2, e, map_sub, map_smul, smul_sub]`. Normalize the expressions using the abelian group laws.
-/
private theorem bkAbove_avg {k G W : Type} [Field k] [CharZero k] [Group G] [AddCommGroup W] [Module k W]
    (a : G → W →ₗ[k] W) (hmul : ∀ g h w, a (g * h) w = a g (a h w)) (f : G → W)
    (hf : ∀ g h, f (g * h) = f g + a g (f h)) (H : Subgroup G) [H.FiniteIndex] (x : W)
    (hx : ∀ h ∈ H, f h = a h x - x) : ∃ y, ∀ g, f g = a g y - y := by
  classical
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  set f' : G → W := fun g => f g - (a g x - x) with hf'
  have hc : ∀ g h, f' (g * h) = f' g + a g (f' h) := by
    intro g h
    simp only [hf', hf, hmul, map_sub]
    abel
  have hH : ∀ g h, h ∈ H → f' (g * h) = f' g := by
    intro g h hh
    rw [hc]
    have : f' h = 0 := by simp only [hf', hx h hh, sub_self]
    rw [this, map_zero, add_zero]
  let F : G ⧸ H → W := Quotient.lift f' (by
    intro g g' hgg
    have h1 : g⁻¹ * g' ∈ H := QuotientGroup.leftRel_apply.1 hgg
    have := hH g _ h1
    rw [mul_inv_cancel_left] at this
    exact this.symm)
  have hF : ∀ (g : G) (q : G ⧸ H), F (g • q) = f' g + a g (F q) := by
    intro g q
    induction q using QuotientGroup.induction_on with
    | H z => exact hc g z
  set S : W := ∑ q, F q with hS
  have hsum : ∀ g, S = (Fintype.card (G ⧸ H) : k) • f' g + a g S := by
    intro g
    have e1 : ∑ q, F (g • q) = S := Equiv.sum_comp (MulAction.toPerm g) F
    refine e1.symm.trans ?_
    simp only [hF, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ← map_sum,
      Nat.cast_smul_eq_nsmul, ← hS]
  have hn : (Fintype.card (G ⧸ H) : k) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  refine ⟨x - (Fintype.card (G ⧸ H) : k)⁻¹ • S, fun g => ?_⟩
  have e : f' g = (Fintype.card (G ⧸ H) : k)⁻¹ • (S - a g S) := by
    rw [eq_inv_smul_iff₀ hn, eq_sub_iff_add_eq]
    exact (hsum g).symm
  have e2 : f g = f' g + (a g x - x) := by simp only [hf', sub_add_cancel]
  rw [e2, e, map_sub, map_smul, smul_sub]
  abel

/- English proof (translation)
Introduce `F Ω _ _ _ _ _ _ l _ j H _ _ _ φ ψ hφ hj C V _ _ _ _ _ _ _ _ _ ρ c hc`. Set `θ : H →* ↥(UpperTheory.V.Af.decJ F j)` to `(ψ.prod φ).codRestrict _ (fun h y => hj h y)`. Set `s : ↥(UpperTheory.V.Af.decJ F j) →* GQ l` to `(MonoidHom.snd _ _).comp (UpperTheory.V.Af.decJ F j).subtype`. Set `p : ↥(UpperTheory.V.Af.decJ F j) →* G F Ω` to `(MonoidHom.fst _ _).comp (UpperTheory.V.Af.decJ F j).subtype`. Establish `hs : IsOpenEmbedding s` using `(UpperTheory.V.Loc.decJFacts (F := F) j).1`.

Establish `hθ : Continuous θ` using `hs.isEmbedding.continuous_iff.2 hφ.continuous`. Establish `hp : Continuous p` using `continuous_fst.comp continuous_subtype_val`. Establish `hψ : Continuous ψ` using `hp.comp hθ`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨-, x, hx⟩`.

Use `⟨⟨hc.1.comp hp, fun g h => hc.2 _ _⟩, ?_⟩` and prove the remaining obligations. Use `haveI : CompactSpace (GQ l) := inferInstanceAs (CompactSpace (Om l ≃ₐ[ℚ_[l]] Om l))`. Use `haveI : Finite (GQ l ⧸ φ.range) := Subgroup.quotient_finite_of_isOpen _ hφ.isOpen_range`. Use `haveI : φ.range.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient`. Use `haveI : (φ.range.comap s).FiniteIndex := ⟨by`.

Rewrite using `[Subgroup.index_comap]`. Conclude with `Subgroup.FiniteIndex.index_ne_zero⟩`. Use `bkAbove_avg (k := ℚ_[l]) (fun g => (actC s (ρ.comp p) g).restrictScalars ℚ_[l]) ?_ (fun g => c (p g) ⊗ₜ[ℚ_[l]] (1 : Bcr l)) ?_ (φ.range.comap s) x ?_` and prove the remaining obligations. Introduce `g h w`. Proceed by induction on `w using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul v b => simp [actC]`. Consider the case `add u v hu hv => simp only [map_add, hu, hv]`. Introduce `g h`. Simplify using `[actC, hc.2 (p g) (p h), TensorProduct.add_tmul]`.

Introduce and unpack `g ⟨h, hh⟩`. Take `rfl : θ h = g` from `hs.injective hh`. Conclude with `hx h`. Introduce and unpack `⟨-, x, hx⟩`. Conclude with `⟨⟨hc.1.comp hψ, fun g h => (congrArg c (map_mul ψ g h)).trans (hc.2 _ _)⟩, x, fun h => hx (θ h)⟩`.
-/
theorem UpperTheory.V.Loc.bkAbove :
    ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [CharZero Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] (j : Ω →+* Om l) {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (φ : H →* GQ l) (ψ : H →* G F Ω), IsOpenEmbedding φ → (∀ h y, φ h (j y) = j (ψ h y)) → ∀ {C V : Type} [CommRing C] [Algebra ℚ_[l] C] [AddCommGroup V] [Module C V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] C V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul C V] (ρ : Representation C (G F Ω) V), ∀ c ∈ Z1 ρ, ((fun h => c (ψ h)) ∈ finiteCocycles φ (ρ.comp ψ) ↔ (fun x : ↥(UpperTheory.V.Af.decJ F j) => c x.1.1) ∈ finiteCocycles ((MonoidHom.snd _ _).comp (UpperTheory.V.Af.decJ F j).subtype) (ρ.comp ((MonoidHom.fst _ _).comp (UpperTheory.V.Af.decJ F j).subtype))) := by
  intro F Ω _ _ _ _ _ _ l _ j H _ _ _ φ ψ hφ hj C V _ _ _ _ _ _ _ _ _ ρ c hc
  let θ : H →* ↥(UpperTheory.V.Af.decJ F j) := (ψ.prod φ).codRestrict _ (fun h y => hj h y)
  let s : ↥(UpperTheory.V.Af.decJ F j) →* GQ l := (MonoidHom.snd _ _).comp (UpperTheory.V.Af.decJ F j).subtype
  let p : ↥(UpperTheory.V.Af.decJ F j) →* G F Ω := (MonoidHom.fst _ _).comp (UpperTheory.V.Af.decJ F j).subtype
  have hs : IsOpenEmbedding s := (UpperTheory.V.Loc.decJFacts (F := F) j).1
  have hθ : Continuous θ := hs.isEmbedding.continuous_iff.2 hφ.continuous
  have hp : Continuous p := continuous_fst.comp continuous_subtype_val
  have hψ : Continuous ψ := hp.comp hθ
  constructor
  · rintro ⟨-, x, hx⟩
    refine ⟨⟨hc.1.comp hp, fun g h => hc.2 _ _⟩, ?_⟩
    haveI : CompactSpace (GQ l) := inferInstanceAs (CompactSpace (Om l ≃ₐ[ℚ_[l]] Om l))
    haveI : Finite (GQ l ⧸ φ.range) := Subgroup.quotient_finite_of_isOpen _ hφ.isOpen_range
    haveI : φ.range.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    haveI : (φ.range.comap s).FiniteIndex := ⟨by
      rw [Subgroup.index_comap]
      exact Subgroup.FiniteIndex.index_ne_zero⟩
    refine bkAbove_avg (k := ℚ_[l]) (fun g => (actC s (ρ.comp p) g).restrictScalars ℚ_[l]) ?_
      (fun g => c (p g) ⊗ₜ[ℚ_[l]] (1 : Bcr l)) ?_ (φ.range.comap s) x ?_
    · intro g h w
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul v b => simp [actC]
      | add u v hu hv => simp only [map_add, hu, hv]
    · intro g h
      simp [actC, hc.2 (p g) (p h), TensorProduct.add_tmul]
    · rintro g ⟨h, hh⟩
      obtain rfl : θ h = g := hs.injective hh
      exact hx h
  · rintro ⟨-, x, hx⟩
    exact ⟨⟨hc.1.comp hψ, fun g h => (congrArg c (map_mul ψ g h)).trans (hc.2 _ _)⟩, x, fun h => hx (θ h)⟩
