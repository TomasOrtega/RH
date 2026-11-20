import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

/- English proof (translation)
Use `haveI : Fintype (G ⧸ H) := Fintype.ofFinite _`. Use `set f' : G → W := fun g => f g - (a g x - x) with hf'`. Establish `hc : ∀ g h, f' (g * h) = f' g + a g (f' h)`. Introduce `g h`. Simplify using `only [hf', hf, hmul, map_sub]`.

Normalize the expressions using the abelian group laws. Establish `hH : ∀ g h, h ∈ H → f' (g * h) = f' g`. Introduce `g h hh`. Rewrite using `[hc]`. Establish `: f' h = 0` using `by simp only [hf', hx h hh, sub_self]`.

Rewrite using `[this, map_zero, add_zero]`. Set `F : G ⧸ H → W` to `Quotient.lift f' (by`. Introduce `g g' hgg`. Establish `h1 : g⁻¹ * g' ∈ H` using `QuotientGroup.leftRel_apply.1 hgg`. Use `hH g _ h1` as an intermediate fact.

Rewrite `this` using `[mul_inv_cancel_left]`. Conclude with `this.symm)`. Establish `hF : ∀ (g : G) (q : G ⧸ H), F (g • q) = f' g + a g (F q)`. Introduce `g q`. Proceed by induction on `q using QuotientGroup.induction_on with`.

Consider the case `H z => exact hc g z`. Use `set S : W := ∑ q, F q with hS`. Establish `hsum : ∀ g, S = (Fintype.card (G ⧸ H) : k) • f' g + a g S`. Introduce `g`. Establish `e1 : ∑ q, F (g • q) = S` using `Equiv.sum_comp (MulAction.toPerm g) F`.

Use `e1.symm.trans ?_` and prove the remaining obligations. Simplify using `only [hF, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ← map_sum, Nat.cast_smul_eq_nsmul, ← hS]`. Establish `hn : (Fintype.card (G ⧸ H) : k) ≠ 0` using `Nat.cast_ne_zero.2 Fintype.card_ne_zero`. Use `⟨x - (Fintype.card (G ⧸ H) : k)⁻¹ • S, fun g => ?_⟩` and prove the remaining obligations. Establish `e : f' g = (Fintype.card (G ⧸ H) : k)⁻¹ • (S - a g S)`.

Rewrite using `[eq_inv_smul_iff₀ hn, eq_sub_iff_add_eq]`. Conclude with `(hsum g).symm`. Establish `e2 : f g = f' g + (a g x - x)` using `by simp only [hf', sub_add_cancel]`. Rewrite using `[e2, e, map_sub, map_smul, smul_sub]`. Normalize the expressions using the abelian group laws.
-/
private theorem z1fDesc_avg {k G W : Type} [Field k] [CharZero k] [Group G] [AddCommGroup W] [Module k W]
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
Introduce `l _ G _ _ _ φ A _ _ V _ _ _ _ _ _ _ _ _ ρ H _ _ c hc`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨-, x, hx⟩`. Conclude with `⟨⟨hc.1.comp continuous_subtype_val, fun g h => hc.2 g h⟩, x, fun h => hx h⟩`. Introduce and unpack `⟨-, x, hx⟩`.

Use `⟨hc, ?_⟩` and prove the remaining obligations. Use `z1fDesc_avg (k := ℚ_[l]) (fun g => (actC φ ρ g).restrictScalars ℚ_[l]) ?_ (fun g => c g ⊗ₜ[ℚ_[l]] (1 : Bcr l)) ?_ H x (fun h hh => hx ⟨h, hh⟩)` and prove the remaining obligations. Introduce `g h w`. Proceed by induction on `w using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul v b => simp [actC]`. Consider the case `add u v hu hv => simp only [map_add, hu, hv]`. Introduce `g h`. Simplify using `[actC, hc.2 g h, add_tmul]`.
-/
theorem UpperTheory.V.Loc.z1fDesc :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) {A : Type} [CommRing A] [Algebra ℚ_[l] A] {V : Type} [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul A V] (ρ : Representation A G V) (H : Subgroup G) [H.Normal] [H.FiniteIndex], ∀ c ∈ Z1 ρ, (c ∈ UpperTheory.V.Loc.finiteCocycles φ ρ ↔ (fun h : H => c h) ∈ UpperTheory.V.Loc.finiteCocycles (φ.comp H.subtype) (ρ.comp H.subtype : Representation A H V)) := by
  intro l _ G _ _ _ φ A _ _ V _ _ _ _ _ _ _ _ _ ρ H _ _ c hc
  constructor
  · rintro ⟨-, x, hx⟩
    exact ⟨⟨hc.1.comp continuous_subtype_val, fun g h => hc.2 g h⟩, x, fun h => hx h⟩
  · rintro ⟨-, x, hx⟩
    refine ⟨hc, ?_⟩
    refine z1fDesc_avg (k := ℚ_[l]) (fun g => (actC φ ρ g).restrictScalars ℚ_[l]) ?_
      (fun g => c g ⊗ₜ[ℚ_[l]] (1 : Bcr l)) ?_ H x (fun h hh => hx ⟨h, hh⟩)
    · intro g h w
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul v b => simp [actC]
      | add u v hu hv => simp only [map_add, hu, hv]
    · intro g h
      simp [actC, hc.2 g h, add_tmul]
