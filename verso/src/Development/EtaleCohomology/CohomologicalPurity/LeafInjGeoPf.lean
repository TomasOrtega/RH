import Development.EtaleCohomology.CohomologicalPurity.LeafExcSheafCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.CohomologicalPurity

/- English proof (translation)
Establish `h1 : (pullback.fst (pullback.fst f f ≫ f) ι ≫ pullback.fst f f) ≫ f = pullback.snd (pullback.fst f f ≫ f) ι ≫ ι`. Rewrite using `[Category.assoc]`. Conclude with `pullback.condition`. Establish `h2 : (pullback.fst (pullback.fst f f ≫ f) ι ≫ pullback.snd f f) ≫ f = pullback.snd (pullback.fst f f ≫ f) ι ≫ ι`. Rewrite using `[Category.assoc, ← pullback.condition]`.

Conclude with `h1`. Establish `e1` using `hp.lift_fst _ _ h1`. Establish `e2` using `hp.lift_fst _ _ h2`. Establish `s1` using `hp.lift_snd _ _ h1`. Establish `s2` using `hp.lift_snd _ _ h2`.

Rewrite `s1`, `s2` using `[Category.comp_id]`. Rewrite using `[← e1, ← e2, s1, s2]`.
-/
theorem injGeo_fib {X' X Z : Scheme.{0}} (f : X' ⟶ X) (ι' : Z ⟶ X') (ι : Z ⟶ X)
    (hp : IsPullback ι' (𝟙 Z) f ι) :
    pullback.fst (pullback.fst f f ≫ f) ι ≫ pullback.fst f f =
      pullback.fst (pullback.fst f f ≫ f) ι ≫ pullback.snd f f := by
  have h1 : (pullback.fst (pullback.fst f f ≫ f) ι ≫ pullback.fst f f) ≫ f =
      pullback.snd (pullback.fst f f ≫ f) ι ≫ ι := by
    rw [Category.assoc]; exact pullback.condition
  have h2 : (pullback.fst (pullback.fst f f ≫ f) ι ≫ pullback.snd f f) ≫ f =
      pullback.snd (pullback.fst f f ≫ f) ι ≫ ι := by
    rw [Category.assoc, ← pullback.condition]; exact h1
  have e1 := hp.lift_fst _ _ h1
  have e2 := hp.lift_fst _ _ h2
  have s1 := hp.lift_snd _ _ h1
  have s2 := hp.lift_snd _ _ h2
  rw [Category.comp_id] at s1 s2
  rw [← e1, ← e2, s1, s2]

/- English proof (translation)
Apply `pullback.hom_ext` to reduce the goal to its premises. Simplify using the standard rewrite rules. Simplify using `[injGeo_fib f ι' ι hp]`.
-/
theorem injGeo_fib_diag {X' X Z : Scheme.{0}} (f : X' ⟶ X) (ι' : Z ⟶ X') (ι : Z ⟶ X)
    (hp : IsPullback ι' (𝟙 Z) f ι) :
    pullback.fst (pullback.fst f f ≫ f) ι =
      (pullback.fst (pullback.fst f f ≫ f) ι ≫ pullback.fst f f) ≫ pullback.diagonal f := by
  apply pullback.hom_ext
  · simp
  · simp [injGeo_fib f ι' ι hp]

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨r, rfl⟩ : q ∈ Set.range (pullback.fst (pullback.fst f f ≫ f) ι) := by`. Rewrite using `[Scheme.Pullback.range_fst]`. Conclude with `hq`. Rewrite using `[injGeo_fib_diag f ι' ι hp]`. Conclude with `⟨(pullback.fst (pullback.fst f f ≫ f) ι ≫ pullback.fst f f) r, rfl⟩`.
-/
theorem injGeo_mem {X' X Z : Scheme.{0}} (f : X' ⟶ X) (ι' : Z ⟶ X') (ι : Z ⟶ X)
    (hp : IsPullback ι' (𝟙 Z) f ι) (q : ↑(pullback f f))
    (hq : (pullback.fst f f ≫ f) q ∈ Set.range ι) : q ∈ Set.range (pullback.diagonal f) := by
  obtain ⟨r, rfl⟩ : q ∈ Set.range (pullback.fst (pullback.fst f f ≫ f) ι) := by
    rw [Scheme.Pullback.range_fst]; exact hq
  rw [injGeo_fib_diag f ι' ι hp]
  exact ⟨(pullback.fst (pullback.fst f f ≫ f) ι ≫ pullback.fst f f) r, rfl⟩

/- English proof (translation)
Introduce `X' X Z f _ ι' ι _ hp U hU T y₁ y₂ hy`. Set `p : T ⟶ pullback f f` to `pullback.lift y₁ y₂ hy`. Set `W : T.Opens` to `p ⁻¹ᵁ (pullback.diagonal f).opensRange`. Set `V : T.Opens` to `(y₁ ≫ f) ⁻¹ᵁ U`. Establish `hW : ∀ (O : T.Opens), O ≤ W → O.ι ≫ y₁ = O.ι ≫ y₂`.

Introduce `O hO`. Establish `H : Set.range (O.ι ≫ p) ⊆ Set.range (pullback.diagonal f)`. Introduce and unpack `_ ⟨t, rfl⟩`. Use `hO (show O.ι t ∈ O by rw [← SetLike.mem_coe, ← Scheme.Opens.range_ι]; exact ⟨t, rfl⟩)` as an intermediate fact. Simplify `this` using `[W]`.

Establish `hl` using `IsOpenImmersion.lift_fac (pullback.diagonal f) (O.ι ≫ p) H`. Establish `a1 : O.ι ≫ y₁ = (O.ι ≫ p) ≫ pullback.fst f f` using `by simp only [p, Category.assoc, pullback.lift_fst]`. Establish `a2 : O.ι ≫ y₂ = (O.ι ≫ p) ≫ pullback.snd f f` using `by simp only [p, Category.assoc, pullback.lift_snd]`. Rewrite using `[a1, a2, ← hl, Category.assoc, Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd]`. Set `O : T → T.Opens` to `fun τ => if (y₁ ≫ f) τ ∈ (U : Set X) then V else W`.

Establish `hO : ∀ τ, O τ ≤ W ∨ O τ ≤ V`. Introduce `τ`. Simplify using `only [O]`. Use `split_ifs`. Conclude with `Or.inr le_rfl`.

Conclude with `Or.inl le_rfl`. Establish `hcov : ∀ τ, τ ∈ O τ`. Introduce `τ`. Simplify using `only [O]`. Use `split_ifs with h`.

Simplify `h` using `[V]`. Establish `h' : (y₁ ≫ f) τ ∈ Set.range ι`. Establish `: (y₁ ≫ f) τ ∉ (Set.range ι)ᶜ` using `by rw [← hU]; exact h`. Simplify using `using this`. Establish `hq : (pullback.fst f f ≫ f) (p τ) ∈ Set.range ι`.

Establish `: p ≫ pullback.fst f f ≫ f = y₁ ≫ f` using `by simp only [p, pullback.lift_fst_assoc]`. Rewrite `h'` using `[← this]`. Simplify using `using h'`. Simplify `injGeo_mem f ι' ι hp (p τ) hq` using `[W]`. Use `⟨Sieve.generate (Presieve.ofArrows (fun τ => (O τ).toScheme) (fun τ => (O τ).ι)), Precoverage.generate_mem_toGrothendieck ((Scheme.ofArrows_mem_precoverage_iff (P := @Etale)).2 ?_), ?_⟩` and prove the remaining obligations.

Use `⟨fun τ => ⟨τ, ?_⟩, fun τ => inferInstance⟩` and prove the remaining obligations. Conclude with `⟨⟨τ, hcov τ⟩, rfl⟩`. Introduce and unpack `Y g ⟨Y', h, _, ⟨τ⟩, rfl⟩`. Break down `hO τ with h1 | h1` into its components or cases. Use `left`.

Simplify using `only [Category.assoc, hW _ h1]`. Use `right`. Use `⟨h ≫ (y₁ ≫ f).resLE U (O τ) h1, ?_⟩` and prove the remaining obligations. Simplify using `[Scheme.Hom.resLE_comp_ι]`.
-/
theorem LeafInjGeo_of : LeafInjGeo := by
  intro X' X Z f _ ι' ι _ hp U hU T y₁ y₂ hy
  classical
  let p : T ⟶ pullback f f := pullback.lift y₁ y₂ hy
  let W : T.Opens := p ⁻¹ᵁ (pullback.diagonal f).opensRange
  let V : T.Opens := (y₁ ≫ f) ⁻¹ᵁ U
  have hW : ∀ (O : T.Opens), O ≤ W → O.ι ≫ y₁ = O.ι ≫ y₂ := by
    intro O hO
    have H : Set.range (O.ι ≫ p) ⊆ Set.range (pullback.diagonal f) := by
      rintro _ ⟨t, rfl⟩
      have := hO (show O.ι t ∈ O by rw [← SetLike.mem_coe, ← Scheme.Opens.range_ι]; exact ⟨t, rfl⟩)
      simpa [W] using this
    have hl := IsOpenImmersion.lift_fac (pullback.diagonal f) (O.ι ≫ p) H
    have a1 : O.ι ≫ y₁ = (O.ι ≫ p) ≫ pullback.fst f f := by simp only [p, Category.assoc, pullback.lift_fst]
    have a2 : O.ι ≫ y₂ = (O.ι ≫ p) ≫ pullback.snd f f := by simp only [p, Category.assoc, pullback.lift_snd]
    rw [a1, a2, ← hl, Category.assoc, Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd]
  let O : T → T.Opens := fun τ => if (y₁ ≫ f) τ ∈ (U : Set X) then V else W
  have hO : ∀ τ, O τ ≤ W ∨ O τ ≤ V := by
    intro τ; simp only [O]; split_ifs
    · exact Or.inr le_rfl
    · exact Or.inl le_rfl
  have hcov : ∀ τ, τ ∈ O τ := by
    intro τ; simp only [O]; split_ifs with h
    · simpa [V] using h
    · have h' : (y₁ ≫ f) τ ∈ Set.range ι := by
        have : (y₁ ≫ f) τ ∉ (Set.range ι)ᶜ := by rw [← hU]; exact h
        simpa using this
      have hq : (pullback.fst f f ≫ f) (p τ) ∈ Set.range ι := by
        have : p ≫ pullback.fst f f ≫ f = y₁ ≫ f := by simp only [p, pullback.lift_fst_assoc]
        rw [← this] at h'; simpa using h'
      simpa [W] using injGeo_mem f ι' ι hp (p τ) hq
  refine ⟨Sieve.generate (Presieve.ofArrows (fun τ => (O τ).toScheme) (fun τ => (O τ).ι)),
    Precoverage.generate_mem_toGrothendieck ((Scheme.ofArrows_mem_precoverage_iff (P := @Etale)).2 ?_), ?_⟩
  · refine ⟨fun τ => ⟨τ, ?_⟩, fun τ => inferInstance⟩
    exact ⟨⟨τ, hcov τ⟩, rfl⟩
  · rintro Y g ⟨Y', h, _, ⟨τ⟩, rfl⟩
    rcases hO τ with h1 | h1
    · left
      simp only [Category.assoc, hW _ h1]
    · right
      refine ⟨h ≫ (y₁ ≫ f).resLE U (O τ) h1, ?_⟩
      simp [Scheme.Hom.resLE_comp_ι]
