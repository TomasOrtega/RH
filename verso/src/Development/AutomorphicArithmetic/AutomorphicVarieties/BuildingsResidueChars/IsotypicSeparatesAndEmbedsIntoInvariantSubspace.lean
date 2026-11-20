import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.CoefficientRepTrivialOnUnramified
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.MemIsotypicOfInjective
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne UpperTheory.V.Hi
open UpperTheory.V.W (Plc)

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
private theorem sepMod {R M S ι : Type} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup S] [Module R S]
    [IsSimpleModule R S] (Φ : (ι →₀ S) →ₗ[R] M) (hs : Function.Surjective Φ) (x : M) (hx : x ≠ 0) :
    ∃ p : M →ₗ[R] S, p x ≠ 0 := by
  obtain ⟨s, hs'⟩ := IsSemisimpleModule.lifting_property Φ hs (LinearMap.id : M →ₗ[R] M)
  have h0 : s x ≠ 0 := fun e => hx (by rw [← LinearMap.id_apply (R := R) x, ← hs', LinearMap.comp_apply, e, map_zero])
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 h0
  exact ⟨Finsupp.lapply i ∘ₗ s, hi⟩

/- English proof (translation)
Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components.

Supply the required witnesses or components. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Extract witnesses or component facts from the available result. Introduce a local definition for the expression.

Supply the required witnesses or components.
-/
private theorem sepRep {G V V' : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (ρ : Representation ℂ G V) (ρ' : Representation ℂ G V') (hρ : ρ'.IsIrreducible)
    (h : ∀ y, y ∈ ⨆ f : {f : V' →ₗ[ℂ] V // ∀ g v, f (ρ' g v) = ρ g (f v)}, LinearMap.range f.1) (x : V) (hx : x ≠ 0) :
    ∃ p : V →ₗ[ℂ] V', (∀ g v, p (ρ g v) = ρ' g (p v)) ∧ p x ≠ 0 := by
  classical
  let F : {f : V' →ₗ[ℂ] V // ∀ g v, f (ρ' g v) = ρ g (f v)} → ρ'.asModule →ₗ[MonoidAlgebra ℂ G] ρ.asModule := fun f =>
    Representation.IntertwiningMap.equivLinearMapAsModule ρ' ρ ⟨f.1, fun g => LinearMap.ext (f.2 g)⟩
  let Φ := Finsupp.lsum ℕ F
  have hs : Function.Surjective Φ := fun y => by
    refine Submodule.iSup_induction _ (motive := fun y : V => ∃ z, Φ z = y) (h y) ?_ ⟨0, map_zero Φ⟩ ?_
    · rintro f _ ⟨v, rfl⟩
      exact ⟨Finsupp.single f v, Finsupp.lsum_single _ _ _ _⟩
    · rintro _ _ ⟨z, rfl⟩ ⟨z', rfl⟩
      exact ⟨z + z', map_add Φ z z'⟩
  obtain ⟨p, hp⟩ := sepMod Φ hs x hx
  let q := (Representation.IntertwiningMap.equivLinearMapAsModule ρ ρ').symm p
  exact ⟨q.toLinearMap, fun g v => q.isIntertwining _ _ g v, hp⟩

private def piRep {G M : Type} [Group G] [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M) (ι : Type) :
    Representation ℂ G (ι → M) where
  toFun g := (ρ g).compLeft ι
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

/- English proof (translation)
Split into cases according to the possible forms of the given data. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components.

Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument. Express the relevant assertion in an equivalent form by its definition. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
private theorem piIso {G M S : Type} [Group G] [AddCommGroup M] [Module ℂ M] [AddCommGroup S] [Module ℂ S]
    (ρ : Representation ℂ G M) (σ : Representation ℂ G S) (ι : Type) [Finite ι]
    (h : ∀ y, y ∈ ⨆ f : {f : S →ₗ[ℂ] M // ∀ g v, f (σ g v) = ρ g (f v)}, LinearMap.range f.1) (y : ι → M) :
    y ∈ ⨆ f : {f : S →ₗ[ℂ] (ι → M) // ∀ g v, f (σ g v) = piRep ρ ι g (f v)}, LinearMap.range f.1 := by
  classical
  cases nonempty_fintype ι
  rw [← Finset.univ_sum_single y]
  refine Submodule.sum_mem _ fun i _ => ?_
  refine Submodule.iSup_induction _ (motive := fun z : M => (Pi.single i z : ι → M) ∈ _) (h (y i)) ?_ ?_ ?_
  · rintro f _ ⟨v, rfl⟩
    refine Submodule.mem_iSup_of_mem ⟨LinearMap.single ℂ (fun _ : ι => M) i ∘ₗ f.1, fun g v => ?_⟩ ⟨v, rfl⟩
    funext j
    change (Pi.single i (f.1 (σ g v)) : ι → M) j = ρ g ((Pi.single i (f.1 v) : ι → M) j)
    by_cases hj : j = i
    · subst hj; simp [f.2]
    · simp [Pi.single_eq_of_ne hj]
  · simp
  · intro a b ha hb
    rw [Pi.single_add]; exact add_mem ha hb

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Introduce a local definition for the expression.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Simplify using the standard rewrite rules. Establish an intermediate fact. Introduce a local definition for the expression. Separate the alternatives or extract the components of the hypothesis. Reduce the conclusion to the remaining proof obligations.

A detailed English derivation is pending.
-/
theorem UpperTheory.isotypic_separates_and_embeds_into_invariant_subspace :
    ∀ (H M : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ H M) (σ : SmIrr H), IsoSum ρ ⊤ σ → (∀ x : M, x ≠ 0 → ∃ p : M →ₗ[ℂ] σ.V, (∀ g v, p (ρ g v) = σ.ρ g (p v)) ∧ p x ≠ 0) ∧ ∀ (ι : Type) [Finite ι] (Y : Submodule ℂ (ι → M)), Y ≠ ⊥ → (∀ g, ∀ F ∈ Y, (fun i => ρ g (F i)) ∈ Y) → ∃ s : σ.V →ₗ[ℂ] (ι → M), Function.Injective s ∧ (∀ v, s v ∈ Y) ∧ ∀ g v i, s (σ.ρ g v) i = ρ g (s v i) := by
  intro H M _ _ _ _ _ ρ σ hI
  have h : ∀ y, y ∈ ⨆ f : {f : σ.V →ₗ[ℂ] M // ∀ g v, f (σ.ρ g v) = ρ g (f v)}, LinearMap.range f.1 := fun y => by
    refine (le_trans hI (iSup_le fun f => ?_)) (Submodule.mem_top (x := y))
    exact le_iSup_of_le (f := fun f : {f : σ.V →ₗ[ℂ] M // ∀ g v, f (σ.ρ g v) = ρ g (f v)} => LinearMap.range f.1)
      ⟨f.1, f.2.1⟩ le_rfl
  refine ⟨sepRep ρ σ.ρ σ.irred h, fun ι _ Y hY hst => ?_⟩
  let π : Representation ℂ H Y := (piRep ρ ι).subrepresentation Y fun g F hF => hst g F hF
  have h2 := UpperTheory.V.PiLin.iso_sub σ.ρ π (piRep ρ ι) σ.irred Y.subtype Y.injective_subtype (fun _ _ => rfl)
    fun y => piIso ρ σ.ρ ι h _
  obtain ⟨f, hf⟩ : ∃ f : {f : σ.V →ₗ[ℂ] Y // ∀ g v, f (σ.ρ g v) = π g (f v)}, f.1 ≠ 0 := by
    by_contra hc
    push Not at hc
    obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff Y).1 hY
    have := h2 ⟨y, hy⟩
    simp only [hc, LinearMap.range_zero, iSup_bot, Submodule.mem_bot] at this
    exact hy0 (congrArg Subtype.val this)
  haveI := σ.irred
  have hi : Function.Injective f.1 := by
    let F : σ.ρ.IntertwiningMap π := ⟨f.1, fun g => LinearMap.ext (f.2 g)⟩
    rcases Representation.IsIrreducible.injective_or_eq_zero F with hi | hz
    · exact hi
    · exact absurd (congrArg Representation.IntertwiningMap.toLinearMap hz) hf
  refine ⟨Y.subtype ∘ₗ f.1, Y.injective_subtype.comp hi, fun v => (f.1 v).2, fun g v i => ?_⟩
  exact congrFun (congrArg Subtype.val (f.2 g v)) i
