import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.CoefficientRepTrivialOnUnramified
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.MemIsotypicOfInjective
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne UpperTheory.V.Hi
open UpperTheory.V.W (Plc)

/- English proof (translation)
Take `⟨s, hs'⟩` from `IsSemisimpleModule.lifting_property Φ hs (LinearMap.id : M →ₗ[R] M)`. Establish `h0 : s x ≠ 0` using `fun e => hx (by rw [← LinearMap.id_apply (R := R) x, ← hs', LinearMap.comp_apply, e, map_zero])`. Take `⟨i, hi⟩` from `Finsupp.ne_iff.1 h0`. Conclude with `⟨Finsupp.lapply i ∘ₗ s, hi⟩`.
-/
private theorem sepMod {R M S ι : Type} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup S] [Module R S]
    [IsSimpleModule R S] (Φ : (ι →₀ S) →ₗ[R] M) (hs : Function.Surjective Φ) (x : M) (hx : x ≠ 0) :
    ∃ p : M →ₗ[R] S, p x ≠ 0 := by
  obtain ⟨s, hs'⟩ := IsSemisimpleModule.lifting_property Φ hs (LinearMap.id : M →ₗ[R] M)
  have h0 : s x ≠ 0 := fun e => hx (by rw [← LinearMap.id_apply (R := R) x, ← hs', LinearMap.comp_apply, e, map_zero])
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 h0
  exact ⟨Finsupp.lapply i ∘ₗ s, hi⟩

/- English proof (translation)
Set `F : {f : V' →ₗ[ℂ] V // ∀ g v, f (ρ' g v) = ρ g (f v)} → ρ'.asModule →ₗ[MonoidAlgebra ℂ G] ρ.asModule` to `fun f => Representation.IntertwiningMap.equivLinearMapAsModule ρ' ρ ⟨f.1, fun g => LinearMap.ext (f.2 g)⟩`. Set `Φ` to `Finsupp.lsum ℕ F`. Establish `hs : Function.Surjective Φ` using `fun y => by`. Use `Submodule.iSup_induction _ (motive := fun y : V => ∃ z, Φ z = y) (h y) ?_ ⟨0, map_zero Φ⟩ ?_` and prove the remaining obligations. Introduce and unpack `f _ ⟨v, rfl⟩`.

Conclude with `⟨Finsupp.single f v, Finsupp.lsum_single _ _ _ _⟩`. Introduce and unpack `_ _ ⟨z, rfl⟩ ⟨z', rfl⟩`. Conclude with `⟨z + z', map_add Φ z z'⟩`. Take `⟨p, hp⟩` from `sepMod Φ hs x hx`. Set `q` to `(Representation.IntertwiningMap.equivLinearMapAsModule ρ ρ').symm p`.

Conclude with `⟨q.toLinearMap, fun g v => q.isIntertwining _ _ g v, hp⟩`.
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
Consider the cases of `nonempty_fintype ι`. Rewrite using `[← Finset.univ_sum_single y]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Use `Submodule.iSup_induction _ (motive := fun z : M => (Pi.single i z : ι → M) ∈ _) (h (y i)) ?_ ?_ ?_` and prove the remaining obligations. Introduce and unpack `f _ ⟨v, rfl⟩`.

Use `Submodule.mem_iSup_of_mem ⟨LinearMap.single ℂ (fun _ : ι => M) i ∘ₗ f.1, fun g v => ?_⟩ ⟨v, rfl⟩` and prove the remaining obligations. Use function extensionality and compare the values at `j`. Express the relevant statement in the definitionally equal form `(Pi.single i (f.1 (σ g v)) : ι → M) j = ρ g ((Pi.single i (f.1 v) : ι → M) j)`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality.

Simplify using `[f.2]`. Simplify using `[Pi.single_eq_of_ne hj]`. Simplify using the standard rewrite rules. Introduce `a b ha hb`. Rewrite using `[Pi.single_add]`.

Conclude with `add_mem ha hb`.
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
Introduce `H M _ _ _ _ _ ρ σ hI`. Establish `h : ∀ y, y ∈ ⨆ f : {f : σ.V →ₗ[ℂ] M // ∀ g v, f (σ.ρ g v) = ρ g (f v)}, LinearMap.range f.1` using `fun y => by`. Use `(le_trans hI (iSup_le fun f => ?_)) (Submodule.mem_top (x := y))` and prove the remaining obligations. Conclude with `le_iSup_of_le (f := fun f : {f : σ.V →ₗ[ℂ] M // ∀ g v, f (σ.ρ g v) = ρ g (f v)} => LinearMap.range f.1) ⟨f.1, f.2.1⟩ le_rfl`. Use `⟨sepRep ρ σ.ρ σ.irred h, fun ι _ Y hY hst => ?_⟩` and prove the remaining obligations.

Set `π : Representation ℂ H Y` to `(piRep ρ ι).subrepresentation Y fun g F hF => hst g F hF`. Establish `h2` using `UpperTheory.V.PiLin.iso_sub σ.ρ π (piRep ρ ι) σ.irred Y.subtype Y.injective_subtype (fun _ _ => rfl) fun y => piIso ρ σ.ρ ι h _`. Choose the witnesses or unpack the hypotheses as in `⟨f, hf⟩ : ∃ f : {f : σ.V →ₗ[ℂ] Y // ∀ g v, f (σ.ρ g v) = π g (f v)}, f.1 ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`.

Take `⟨y, hy, hy0⟩` from `(Submodule.ne_bot_iff Y).1 hY`. Use `h2 ⟨y, hy⟩` as an intermediate fact. Simplify using `only [hc, LinearMap.range_zero, iSup_bot, Submodule.mem_bot] at this`. Conclude with `hy0 (congrArg Subtype.val this)`. Use `haveI := σ.irred`.

Establish `hi : Function.Injective f.1`. Set `F : σ.ρ.IntertwiningMap π` to `⟨f.1, fun g => LinearMap.ext (f.2 g)⟩`. Break down `Representation.IsIrreducible.injective_or_eq_zero F with hi | hz` into its components or cases. Conclude with `hi`. Conclude with `absurd (congrArg Representation.IntertwiningMap.toLinearMap hz) hf`.

Use `⟨Y.subtype ∘ₗ f.1, Y.injective_subtype.comp hi, fun v => (f.1 v).2, fun g v i => ?_⟩` and prove the remaining obligations. Conclude with `congrFun (congrArg Subtype.val (f.2 g v)) i`.
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
