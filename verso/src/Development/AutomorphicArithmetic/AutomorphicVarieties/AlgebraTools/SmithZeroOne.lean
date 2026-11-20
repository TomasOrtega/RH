import Mathlib

open Polynomial Matrix IsLocalRing TensorProduct

/- English proof (translation)
Introduce `A _ _ _ F V _ _ _ _ _ _ _ _ ϖ Y Z hϖ hZ hYZ hmY`. Use `haveI := hZ`. Establish `hfr : Module.finrank A Z = Module.finrank F V`. Apply `Module.finrank_eq_of_rank_eq` to reduce the goal to its premises. Rewrite using `[Submodule.IsLattice.rank' F Z, Module.finrank_eq_rank]`.

Set `b0 : Module.Basis (Fin (Module.finrank F V)) A Z` to `Module.finBasisOfFinrankEq A Z hfr`. Set `N : Submodule A Z` to `Y.comap Z.subtype`. Establish `hϖm : ϖ ∈ maximalIdeal A` using `(IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit`. Establish `hN : ∀ z : Z, ϖ • z ∈ N` using `fun z => hmY (Submodule.smul_mem_smul hϖm z.2)`. Establish `hrk : Module.finrank A N = Module.finrank A Z`.

Apply `le_antisymm (Submodule.finrank_le N)` to reduce the goal to its premises. Set `g : Z →ₗ[A] N` to `(ϖ • LinearMap.id : Z →ₗ[A] Z).codRestrict N (fun z => hN z)`. Apply `LinearMap.finrank_le_finrank_of_injective (f := g)` to reduce the goal to its premises. Introduce `x y hxy`. Establish `h1 : ϖ • x = ϖ • y` using `congrArg Subtype.val hxy`.

Conclude with `smul_right_injective _ hϖ.ne_zero h1`. Take `⟨b', a, ab', hab⟩` from `Submodule.exists_smith_normal_form_of_rank_eq b0 hrk`. Establish `hdiv : ∀ i, a i ∣ ϖ`. Introduce `i`. Set `x : N` to `⟨ϖ • b' i, hN _⟩`.

Establish `hx : (x : Z) = ∑ j, (ab'.repr x j * a j) • b' j`. Establish `h` using `congrArg Subtype.val (ab'.sum_repr x)`. Rewrite using `[← h, Submodule.coe_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Submodule.coe_smul, hab, mul_smul]`.

Use `congrArg (fun m => b'.repr m i) hx` as an intermediate fact. Simplify using `[x, Finsupp.single_apply, Finset.sum_apply'] at this`. Conclude with `⟨ab'.repr x i, by rw [this, mul_comm]⟩`. Set `B` to `b'.extendOfIsLattice F`. Set `S : Finset (Fin (Module.finrank F V))` to `Finset.univ.filter fun i => ¬ IsUnit (a i)`.

Use `⟨B, S, ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : Submodule.map Z.subtype (⊤ : Submodule A Z) = Z` using `by simp`. Rewrite using `[← h1, ← b'.span_eq, Submodule.map_span, ← Set.range_comp]`. Use `congr 2`. Use extensionality with `i`.

Simplify using `[B]`. Establish `hY : Y = Submodule.map Z.subtype N`. Rewrite using `[Submodule.map_comap_subtype]`. Conclude with `(inf_eq_right.2 hYZ).symm`. Establish `hNs : Submodule.map N.subtype (⊤ : Submodule A N) = N` using `by simp`.

Establish `hv : Y = Submodule.span A (Set.range fun i => a i • B i)`. Rewrite using `[hY, ← hNs, ← ab'.span_eq, Submodule.map_span, Submodule.map_span, ← Set.image_comp, ← Set.range_comp]`. Use `congr 2`. Use extensionality with `i`. Simplify using `[B, hab]`.

Establish `hu : ∀ i, ∃ u : Aˣ, a i • B i = (u : A) • (if i ∈ S then ϖ • B i else B i)`. Introduce `i`. Take `⟨c, hc⟩` from `hdiv i`. Distinguish the cases in `hai : IsUnit (a i)`. Use `⟨hai.unit, ?_⟩` and prove the remaining obligations.

Establish `: i ∉ S` using `by simp [S, hai]`. Simplify using `[this]`. Establish `hcu : IsUnit c`. Break down `hϖ.isUnit_or_isUnit hc with h | h` into its components or cases. Conclude with `absurd h hai`.

Conclude with `h`. Establish `: i ∈ S` using `by simp [S, hai]`. Use `⟨hcu.unit⁻¹, ?_⟩` and prove the remaining obligations. Rewrite using `[if_pos this, smul_smul, hc]`. Use `congr 1`.

Rewrite using `[mul_comm (a i) c, ← mul_assoc]`. Simplify using the standard rewrite rules. Rewrite using `[hv]`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨i, rfl⟩`. Take `⟨u, hu'⟩` from `hu i`. Use `show a i • B i ∈ _`. Rewrite using `[hu']`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Take `⟨u, hu'⟩` from `hu i`. Establish `: (if i ∈ S then ϖ • B i else B i) = ((u⁻¹ : Aˣ) : A) • (a i • B i)`. Rewrite using `[hu', smul_smul]`.

Simplify using the standard rewrite rules. Use `show (if i ∈ S then ϖ • B i else B i) ∈ _`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`.
-/
theorem UpperTheory.V.AlgebraTools.smith_zero_one :
    ∀ {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {F V : Type} [Field F] [Algebra A F] [IsFractionRing A F] [AddCommGroup V] [Module F V] [Module A V] [IsScalarTower A F V] [Module.Finite F V] (ϖ : A) (Y Z : Submodule A V), Irreducible ϖ → Submodule.IsLattice F Z → Y ≤ Z → maximalIdeal A • Z ≤ Y → ∃ (b : Module.Basis (Fin (Module.finrank F V)) F V) (S : Finset (Fin (Module.finrank F V))), Z = Submodule.span A (Set.range b) ∧ Y = Submodule.span A (Set.range fun i => if i ∈ S then ϖ • b i else b i) := by
  intro A _ _ _ F V _ _ _ _ _ _ _ _ ϖ Y Z hϖ hZ hYZ hmY
  classical
  haveI := hZ
  have hfr : Module.finrank A Z = Module.finrank F V := by
    apply Module.finrank_eq_of_rank_eq
    rw [Submodule.IsLattice.rank' F Z, Module.finrank_eq_rank]
  let b0 : Module.Basis (Fin (Module.finrank F V)) A Z := Module.finBasisOfFinrankEq A Z hfr
  let N : Submodule A Z := Y.comap Z.subtype
  have hϖm : ϖ ∈ maximalIdeal A := (IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit
  have hN : ∀ z : Z, ϖ • z ∈ N := fun z => hmY (Submodule.smul_mem_smul hϖm z.2)
  have hrk : Module.finrank A N = Module.finrank A Z := by
    apply le_antisymm (Submodule.finrank_le N)
    let g : Z →ₗ[A] N := (ϖ • LinearMap.id : Z →ₗ[A] Z).codRestrict N (fun z => hN z)
    apply LinearMap.finrank_le_finrank_of_injective (f := g)
    intro x y hxy
    have h1 : ϖ • x = ϖ • y := congrArg Subtype.val hxy
    exact smul_right_injective _ hϖ.ne_zero h1
  obtain ⟨b', a, ab', hab⟩ := Submodule.exists_smith_normal_form_of_rank_eq b0 hrk
  have hdiv : ∀ i, a i ∣ ϖ := by
    intro i
    let x : N := ⟨ϖ • b' i, hN _⟩
    have hx : (x : Z) = ∑ j, (ab'.repr x j * a j) • b' j := by
      have h := congrArg Subtype.val (ab'.sum_repr x)
      rw [← h, Submodule.coe_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Submodule.coe_smul, hab, mul_smul]
    have := congrArg (fun m => b'.repr m i) hx
    simp [x, Finsupp.single_apply, Finset.sum_apply'] at this
    exact ⟨ab'.repr x i, by rw [this, mul_comm]⟩
  let B := b'.extendOfIsLattice F
  let S : Finset (Fin (Module.finrank F V)) := Finset.univ.filter fun i => ¬ IsUnit (a i)
  refine ⟨B, S, ?_, ?_⟩
  · have h1 : Submodule.map Z.subtype (⊤ : Submodule A Z) = Z := by simp
    rw [← h1, ← b'.span_eq, Submodule.map_span, ← Set.range_comp]
    congr 2
    ext i
    simp [B]
  · have hY : Y = Submodule.map Z.subtype N := by
      rw [Submodule.map_comap_subtype]
      exact (inf_eq_right.2 hYZ).symm
    have hNs : Submodule.map N.subtype (⊤ : Submodule A N) = N := by simp
    have hv : Y = Submodule.span A (Set.range fun i => a i • B i) := by
      rw [hY, ← hNs, ← ab'.span_eq, Submodule.map_span, Submodule.map_span, ← Set.image_comp,
        ← Set.range_comp]
      congr 2
      ext i
      simp [B, hab]
    have hu : ∀ i, ∃ u : Aˣ, a i • B i = (u : A) • (if i ∈ S then ϖ • B i else B i) := by
      intro i
      obtain ⟨c, hc⟩ := hdiv i
      by_cases hai : IsUnit (a i)
      · refine ⟨hai.unit, ?_⟩
        have : i ∉ S := by simp [S, hai]
        simp [this]
      · have hcu : IsUnit c := by
          rcases hϖ.isUnit_or_isUnit hc with h | h
          · exact absurd h hai
          · exact h
        have : i ∈ S := by simp [S, hai]
        refine ⟨hcu.unit⁻¹, ?_⟩
        rw [if_pos this, smul_smul, hc]
        congr 1
        rw [mul_comm (a i) c, ← mul_assoc]
        simp
    rw [hv]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      obtain ⟨u, hu'⟩ := hu i
      show a i • B i ∈ _
      rw [hu']
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      obtain ⟨u, hu'⟩ := hu i
      have : (if i ∈ S then ϖ • B i else B i) = ((u⁻¹ : Aˣ) : A) • (a i • B i) := by
        rw [hu', smul_smul]
        simp
      show (if i ∈ S then ϖ • B i else B i) ∈ _
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
