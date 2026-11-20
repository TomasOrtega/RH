import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.LenCokerLe

open ReciprocityTheory.Gal UpperTheory.V.Base

/- English proof (translation)
Use `Fintype.ofFinite I` as an intermediate fact. Set `φ : Submodule.span R {f} →ₗ[R] (Π i : I, Submodule.span R {(f : I → N) i})` to `{ toFun := fun g i => ⟨((g : Z) : I → N) i, by`. Take `⟨r, hr⟩` from `Submodule.mem_span_singleton.mp g.2`. Rewrite using `[← hr]`. Conclude with `Submodule.mem_span_singleton.mpr ⟨r, by simp⟩⟩`.

Use the proof step `map_add' := fun g h => by ext i; simp`. Use the proof step `map_smul' := fun r g => by ext i; simp }`. Establish `hφ : Function.Injective φ`. Introduce `g h e`. Apply `Subtype.ext` to reduce the goal to its premises.

Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Conclude with `congrArg Subtype.val (congrFun e i)`. Use `ne_top_of_le_ne_top ?_ (Module.length_le_of_injective φ hφ)` and prove the remaining obligations. Rewrite using `[Module.length_pi_of_fintype]`.

Conclude with `(WithTop.sum_lt_top.mpr fun i _ => (hN _).lt_top).ne`.
-/
private theorem UpperTheory.V.Base.length_span_cocycle_finite {R N I : Type} [CommRing R] [AddCommGroup N] [Module R N] [Finite I]
    (hN : ∀ m : N, Module.length R (Submodule.span R {m}) ≠ ⊤) (Z : Submodule R (I → N)) (f : Z) :
    Module.length R (Submodule.span R {f}) ≠ ⊤ := by
  classical
  have := Fintype.ofFinite I
  let φ : Submodule.span R {f} →ₗ[R] (Π i : I, Submodule.span R {(f : I → N) i}) :=
    { toFun := fun g i => ⟨((g : Z) : I → N) i, by
        obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp g.2
        rw [← hr]
        exact Submodule.mem_span_singleton.mpr ⟨r, by simp⟩⟩
      map_add' := fun g h => by ext i; simp
      map_smul' := fun r g => by ext i; simp }
  have hφ : Function.Injective φ := by
    intro g h e
    apply Subtype.ext
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun e i)
  refine ne_top_of_le_ne_top ?_ (Module.length_le_of_injective φ hφ)
  rw [Module.length_pi_of_fintype]
  exact (WithTop.sum_lt_top.mpr fun i _ => (hN _).lt_top).ne

/- English proof (translation)
Introduce `R Q N _ _ _ _ _ _ _ _ _ _ _ _ σ hcomm hN hsc`. Use `choose c hc using hsc`. Use `set J : Ideal R := Ideal.span (Set.range fun g => c g - 1) with hJ`. Use `set a : R := Submodule.IsPrincipal.generator J with ha`. Establish `haJ : a ∈ J` using `Submodule.IsPrincipal.generator_mem J`.

Establish `hJa : ∀ g, ∃ r : R, c g - 1 = r * a`. Introduce `g`. Establish `hmem : c g - 1 ∈ J` using `Ideal.subset_span ⟨g, rfl⟩`. Rewrite `hmem` using `[← Ideal.span_singleton_generator J]`. Take `⟨r, hr⟩` from `Ideal.mem_span_singleton'.mp hmem`.

Conclude with `⟨r, hr.symm⟩`. Establish `hH0 : ∀ m : N, a • m = 0 → m ∈ H0 σ`. Introduce `m hm`. Rewrite using `[H0, Representation.mem_invariants]`. Introduce `g`.

Take `⟨r, hr⟩` from `hJa g`. Establish `hz : (c g - 1) • m = 0` using `by rw [hr, mul_smul, hm, smul_zero]`. Rewrite using `[hc, ← sub_eq_zero, ← hz, sub_smul, one_smul]`. Establish `hB : ∀ f : Z2 σ, a • (f : Q × Q → N) ∈ B2 σ`. Introduce `f`.

Use `set F : Q × Q → N := (f : Q × Q → N) with hF`. Take `⟨-, hcoc⟩` from `f.2`. Use `Submodule.span_induction (p := fun x _ => x • F ∈ B2 σ) ?_ ?_ ?_ ?_ haJ` and prove the remaining obligations. Introduce and unpack `_ ⟨g, rfl⟩`. Rewrite using `[separated_dvr_second_cohomology_mem]`.

Use `⟨fun x => F (g, x) - F (x, g), continuous_of_discreteTopology, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `⟨x, y⟩`. Establish `e1` using `hcoc g x y`. Establish `e2` using `hcoc x g y`. Establish `e3` using `hcoc x y g`.

Rewrite `e1`, `e2`, `e3` using `[hc]`. Rewrite `e2` using `[hcomm x g]`. Rewrite `e3` using `[hcomm y g]`. Simplify using `only [d1_apply, hc, Pi.smul_apply]`. Establish `key : c x • (F (g, y) - F (y, g)) - (F (g, x * y) - F (x * y, g)) + (F (g, x) - F (x, g)) - (c g - 1) • F (x, y) = -((c g • F (x, y) - F (g * x, y) + F (g, x * y) - F (g, x)) - (c x • F (g, y) - F (g * x, y) + F (x, g * y) - F (x, g)) + (c x • F (y, g) - F (x * y, g) + F (x, g * …`.

Simplify using `only [smul_sub, sub_smul, one_smul]`. Normalize the expressions using the abelian group laws. Rewrite `key` using `[e1, e2, e3]`. Simplify `key` using `[sub_eq_zero]`. Rewrite using `[zero_smul]`.

Conclude with `zero_mem _`. Introduce `x y _ _ hx hy`. Rewrite using `[add_smul]`. Conclude with `add_mem hx hy`. Introduce `r x _ hx`.

Rewrite using `[smul_eq_mul, mul_smul]`. Conclude with `Submodule.smul_mem _ r hx`. Set `Zs` to `Z2 σ`. Set `mul : Zs →ₗ[R] Zs` to `a • LinearMap.id`. Establish `h1 : Module.length R (H2 σ) ≤ Module.length R (Zs ⧸ LinearMap.range mul)`.

Set `q` to `Submodule.liftQ (LinearMap.range mul) (Submodule.mkQ (Submodule.comap Zs.subtype (B2 σ))) (by`. Introduce and unpack `_ ⟨z, rfl⟩`. Rewrite using `[LinearMap.mem_ker, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]`. Conclude with `hB z)`. Use `Module.length_le_of_surjective q ?_` and prove the remaining obligations.

Introduce `y`. Take `⟨z, rfl⟩` from `Submodule.mkQ_surjective _ y`. Conclude with `⟨Submodule.mkQ _ z, rfl⟩`. Establish `h2` using `lenCokerLe R Zs (UpperTheory.V.Base.length_span_cocycle_finite hN Zs) a`. Establish `h3 : Module.length R (LinearMap.ker mul) ≤ Module.length R (Q × Q → H0 σ)`.

Set `φ : LinearMap.ker mul →ₗ[R] (Q × Q → H0 σ)` to `{ toFun := fun z p => ⟨((z : Zs) : Q × Q → N) p, hH0 _ (by`. Establish `hz : mul (z : Zs) = 0` using `LinearMap.mem_ker.mp z.2`. Conclude with `congrFun (congrArg Subtype.val hz) p)⟩`. Use the proof step `map_add' := fun _ _ => by ext; simp`. Use the proof step `map_smul' := fun _ _ => by ext; simp }`.

Use `Module.length_le_of_injective φ ?_` and prove the remaining obligations. Introduce `z w e`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `p`.

Establish `hp` using `congrArg Subtype.val (congrFun e p)`. Conclude with `hp`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Module.length_pi]`. Use `congr 1`.

Rewrite using `[ENat.card_eq_coe_natCard, Nat.card_prod, pow_two]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem UpperTheory.V.Base.h2Ab :
    ∀ (R Q N : Type) [CommRing R] [TopologicalSpace Q] [DiscreteTopology Q] [Finite Q] [AddCommGroup N] [Module R N]
      [TopologicalSpace N] [IsTopologicalAddGroup N] [ContinuousConstSMul R N] [DiscreteTopology N] [IsPrincipalIdealRing R] [Group Q] (σ : Representation R Q N), (∀ a b : Q, a * b = b * a) → (∀ m : N, Module.length R (Submodule.span R {m}) ≠ ⊤) →
      (∀ g, ∃ c : R, ∀ m, σ g m = c • m) → Module.length R (H2 σ) ≤ (Nat.card Q : ℕ∞) ^ 2 * Module.length R (H0 σ) := by
  intro R Q N _ _ _ _ _ _ _ _ _ _ _ _ σ hcomm hN hsc
  classical
  choose c hc using hsc
  set J : Ideal R := Ideal.span (Set.range fun g => c g - 1) with hJ
  set a : R := Submodule.IsPrincipal.generator J with ha
  have haJ : a ∈ J := Submodule.IsPrincipal.generator_mem J
  have hJa : ∀ g, ∃ r : R, c g - 1 = r * a := by
    intro g
    have hmem : c g - 1 ∈ J := Ideal.subset_span ⟨g, rfl⟩
    rw [← Ideal.span_singleton_generator J] at hmem
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hmem
    exact ⟨r, hr.symm⟩
  have hH0 : ∀ m : N, a • m = 0 → m ∈ H0 σ := by
    intro m hm
    rw [H0, Representation.mem_invariants]
    intro g
    obtain ⟨r, hr⟩ := hJa g
    have hz : (c g - 1) • m = 0 := by rw [hr, mul_smul, hm, smul_zero]
    rw [hc, ← sub_eq_zero, ← hz, sub_smul, one_smul]
  have hB : ∀ f : Z2 σ, a • (f : Q × Q → N) ∈ B2 σ := by
    intro f
    set F : Q × Q → N := (f : Q × Q → N) with hF
    obtain ⟨-, hcoc⟩ := f.2
    refine Submodule.span_induction (p := fun x _ => x • F ∈ B2 σ) ?_ ?_ ?_ ?_ haJ
    · rintro _ ⟨g, rfl⟩
      rw [separated_dvr_second_cohomology_mem]
      refine ⟨fun x => F (g, x) - F (x, g), continuous_of_discreteTopology, ?_⟩
      funext ⟨x, y⟩
      have e1 := hcoc g x y
      have e2 := hcoc x g y
      have e3 := hcoc x y g
      rw [hc] at e1 e2 e3
      rw [hcomm x g] at e2
      rw [hcomm y g] at e3
      simp only [d1_apply, hc, Pi.smul_apply]
      have key : c x • (F (g, y) - F (y, g)) - (F (g, x * y) - F (x * y, g)) + (F (g, x) - F (x, g))
            - (c g - 1) • F (x, y)
          = -((c g • F (x, y) - F (g * x, y) + F (g, x * y) - F (g, x))
            - (c x • F (g, y) - F (g * x, y) + F (x, g * y) - F (x, g))
            + (c x • F (y, g) - F (x * y, g) + F (x, g * y) - F (x, y))) := by
        simp only [smul_sub, sub_smul, one_smul]
        abel
      rw [e1, e2, e3] at key
      simpa [sub_eq_zero] using key
    · rw [zero_smul]
      exact zero_mem _
    · intro x y _ _ hx hy
      rw [add_smul]
      exact add_mem hx hy
    · intro r x _ hx
      rw [smul_eq_mul, mul_smul]
      exact Submodule.smul_mem _ r hx
  let Zs := Z2 σ
  let mul : Zs →ₗ[R] Zs := a • LinearMap.id
  have h1 : Module.length R (H2 σ) ≤ Module.length R (Zs ⧸ LinearMap.range mul) := by
    let q := Submodule.liftQ (LinearMap.range mul) (Submodule.mkQ (Submodule.comap Zs.subtype (B2 σ))) (by
      rintro _ ⟨z, rfl⟩
      rw [LinearMap.mem_ker, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
      exact hB z)
    refine Module.length_le_of_surjective q ?_
    intro y
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ y
    exact ⟨Submodule.mkQ _ z, rfl⟩
  have h2 := lenCokerLe R Zs (UpperTheory.V.Base.length_span_cocycle_finite hN Zs) a
  have h3 : Module.length R (LinearMap.ker mul) ≤ Module.length R (Q × Q → H0 σ) := by
    let φ : LinearMap.ker mul →ₗ[R] (Q × Q → H0 σ) :=
      { toFun := fun z p => ⟨((z : Zs) : Q × Q → N) p, hH0 _ (by
            have hz : mul (z : Zs) = 0 := LinearMap.mem_ker.mp z.2
            exact congrFun (congrArg Subtype.val hz) p)⟩
        map_add' := fun _ _ => by ext; simp
        map_smul' := fun _ _ => by ext; simp }
    refine Module.length_le_of_injective φ ?_
    intro z w e
    apply Subtype.ext
    apply Subtype.ext
    funext p
    have hp := congrArg Subtype.val (congrFun e p)
    exact hp
  calc Module.length R (H2 σ) ≤ _ := h1
    _ ≤ _ := h2
    _ ≤ _ := h3
    _ = (Nat.card Q : ℕ∞) ^ 2 * Module.length R (H0 σ) := by
      rw [Module.length_pi]
      congr 1
      rw [ENat.card_eq_coe_natCard, Nat.card_prod, pow_two]
      push_cast
      rfl
