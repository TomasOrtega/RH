import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryApproximation.WeakApproxF

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace PI.UnitaryApproxFinWork

/- English proof (translation)
Set `f : E →+* (R ⧸ m)` to `(Ideal.Quotient.mk m).comp ι`. Set `gb : Matrix n n (R ⧸ m)` to `g.map (Ideal.Quotient.mk m)`. Set `P : Polynomial (R ⧸ m)` to `((1 : Matrix n n (Polynomial (R ⧸ m))) + (Polynomial.X : Polynomial (R ⧸ m)) • gb.map Polynomial.C).det`. Establish `hev : ∀ c : R ⧸ m, P.eval c = (1 + c • gb).det`. Introduce `c`.

Establish `h` using `(Polynomial.evalRingHom c).map_det ((1 : Matrix n n (Polynomial (R ⧸ m))) + (Polynomial.X : Polynomial (R ⧸ m)) • gb.map Polynomial.C)`. Rewrite `h` using `[Polynomial.coe_evalRingHom]`. Use `show Polynomial.eval c (Matrix.det _) = _`. Rewrite using `[h]`. Use `congr 1`.

Use extensionality with `i j`. Apply the tactic sequence `by_cases hij : i = j <;> simp [Matrix.one_apply, hij] <;> ring`. Establish `hP0 : P ≠ 0`. Introduce `h`. Establish `h0` using `hev 0`.

Rewrite `h0` using `[h]`. Simplify using `at h0`. Establish `hfin : {c : R ⧸ m | P.eval c = 0}.Finite`. Apply `(P.roots.toFinset.finite_toSet).subset` to reduce the goal to its premises. Introduce `c hc`.

Simplify using `only [Set.mem_setOf_eq] at hc`. Simplify using `[Polynomial.mem_roots hP0, hc]`. Apply `(hfin.preimage (fun _ _ _ _ h => f.injective h)).subset` to reduce the goal to its premises. Introduce `μ hμ`. Simplify using `only [Set.mem_setOf_eq, Set.mem_preimage] at hμ ⊢`.

Rewrite using `[hev]`. Establish `h1 : Ideal.Quotient.mk m (1 + ι μ • g).det = 0` using `Ideal.Quotient.eq_zero_iff_mem.mpr hμ`. Rewrite `h1` using `[RingHom.map_det]`. Use `h1 using 2` and compare the differences between its conclusion and the goal. Use extensionality with `i j`.

Apply the tactic sequence `by_cases hij : i = j <;> simp [f, gb, Matrix.one_apply, hij]`.
-/
theorem ea_finite_bad {E R : Type*} [Field E] [CommRing R] (ι : E →+* R)
    {n : Type*} [Fintype n] [DecidableEq n] (g : Matrix n n R) (m : Ideal R) [m.IsMaximal] :
    {μ : E | (1 + ι μ • g).det ∈ m}.Finite := by
  classical
  let f : E →+* (R ⧸ m) := (Ideal.Quotient.mk m).comp ι
  let gb : Matrix n n (R ⧸ m) := g.map (Ideal.Quotient.mk m)
  let P : Polynomial (R ⧸ m) :=
    ((1 : Matrix n n (Polynomial (R ⧸ m))) + (Polynomial.X : Polynomial (R ⧸ m)) • gb.map Polynomial.C).det
  have hev : ∀ c : R ⧸ m, P.eval c = (1 + c • gb).det := by
    intro c
    have h := (Polynomial.evalRingHom c).map_det
      ((1 : Matrix n n (Polynomial (R ⧸ m))) + (Polynomial.X : Polynomial (R ⧸ m)) • gb.map Polynomial.C)
    rw [Polynomial.coe_evalRingHom] at h
    show Polynomial.eval c (Matrix.det _) = _
    rw [h]
    congr 1
    ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij] <;> ring
  have hP0 : P ≠ 0 := by
    intro h
    have h0 := hev 0
    rw [h] at h0
    simp at h0
  have hfin : {c : R ⧸ m | P.eval c = 0}.Finite := by
    apply (P.roots.toFinset.finite_toSet).subset
    intro c hc
    simp only [Set.mem_setOf_eq] at hc
    simp [Polynomial.mem_roots hP0, hc]
  apply (hfin.preimage (fun _ _ _ _ h => f.injective h)).subset
  intro μ hμ
  simp only [Set.mem_setOf_eq, Set.mem_preimage] at hμ ⊢
  rw [hev]
  have h1 : Ideal.Quotient.mk m (1 + ι μ • g).det = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hμ
  rw [RingHom.map_det] at h1
  convert h1 using 2
  ext i j
  by_cases hij : i = j <;> simp [f, gb, Matrix.one_apply, hij]

/- English proof (translation)
Use `haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Use `haveI : IsArtinianRing (v.adicCompletion F ⊗[F] E) := IsArtinianRing.of_finite (v.adicCompletion F) _`. Establish `hs : Function.Surjective (Algebra.TensorProduct.comm F (v.adicCompletion F) E)` using `(Algebra.TensorProduct.comm F (v.adicCompletion F) E).surjective`. Use `first`. Consider the case `exact hs.isArtinianRing`.

Consider the case `exact IsArtinianRing.of_surjective _ hs`. Consider the case `exact Function.Surjective.isArtinianRing hs`.
-/
theorem ea_artinian {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) : IsArtinianRing (E ⊗[F] v.adicCompletion F) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsArtinianRing (v.adicCompletion F ⊗[F] E) := IsArtinianRing.of_finite (v.adicCompletion F) _
  have hs : Function.Surjective (Algebra.TensorProduct.comm F (v.adicCompletion F) E) :=
    (Algebra.TensorProduct.comm F (v.adicCompletion F) E).surjective
  first
    | exact hs.isArtinianRing
    | exact IsArtinianRing.of_surjective _ hs
    | exact Function.Surjective.isArtinianRing hs

/- English proof (translation)
Introduce `F E _ _ _ _ _ n _ _ σ hσ hθ T g`. Take `⟨θ, hθ⟩` from `hθ`. Set `bad : Set E` to `⋃ v ∈ (T : Set (HeightOneSpectrum (𝓞 F))), ⋃ m ∈ {m : Ideal (E ⊗[F] v.adicCompletion F) | m.IsMaximal}, {μ : E | (1 + PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) μ • g v).det ∈ m}`. Establish `hbad : bad.Finite`. Use `Set.Finite.biUnion T.finite_toSet fun v _ => ?_` and prove the remaining obligations.

Use `haveI : IsArtinianRing (E ⊗[F] v.adicCompletion F) := ea_artinian v`. Use `Set.Finite.biUnion (IsArtinianRing.setOfPred_isMaximal_finite _) fun m hm => ?_` and prove the remaining obligations. Use `haveI : m.IsMaximal := hm`. Conclude with `ea_finite_bad _ (g v) m`. Establish `hnz1 : ∀ t : ℕ, (t : E) + θ ≠ 0`.

Introduce `t h`. Apply `hθ` to reduce the goal to its premises. Establish `h' : θ = -(t : E)` using `by linear_combination h`. Rewrite using `[h', map_neg, map_natCast]`. Establish `hnz2 : ∀ t : ℕ, (t : E) + σ θ ≠ 0`.

Introduce `t h`. Apply `hθ` to reduce the goal to its premises. Establish `h' : σ θ = -(t : E)` using `by linear_combination h`. Establish `h'' : θ = -(t : E)` using `by rw [← hσ θ, h', map_neg, map_natCast]`. Rewrite using `[h', h'']`.

Set `f : ℕ → E` to `fun t => ((t : E) + θ) / ((t : E) + σ θ)`. Establish `hinj : Function.Injective f`. Introduce `s t hst`. Establish `hst' : ((s : E) + θ) / ((s : E) + σ θ) = ((t : E) + θ) / ((t : E) + σ θ)` using `hst`. Rewrite `hst'` using `[div_eq_div_iff (hnz2 s) (hnz2 t)]`.

Establish `h2 : ((s : E) - t) * (σ θ - θ) = 0` using `by linear_combination hst'`. Break down `mul_eq_zero.mp h2 with h | h` into its components or cases. Conclude with `sub_eq_zero.mp h` after adjusting the coercions. Conclude with `absurd (sub_eq_zero.mp h) hθ`. Establish `hrange : ¬ Set.range f ⊆ bad` using `fun h => Set.infinite_range_of_injective hinj (hbad.subset h)`.

Take `⟨_, ⟨t, rfl⟩, ht⟩` from `Set.not_subset.mp hrange`. Use `⟨f t, ?_, ?_⟩` and prove the remaining obligations. Use `show σ (((t : E) + θ) / ((t : E) + σ θ)) * (((t : E) + θ) / ((t : E) + σ θ)) = 1`. Rewrite using `[map_div₀, map_add, map_add, map_natCast, hσ]`. Establish `h1` using `hnz1 t`.

Establish `h2` using `hnz2 t`. Clear the denominators using the available nonvanishing facts. Introduce `v hv`. Assume the negation of the conclusion as `hu`. Take `⟨m, hm, hmem⟩` from `exists_max_ideal_of_mem_nonunits hu`.

Conclude with `ht (Set.mem_iUnion₂.mpr ⟨v, Finset.mem_coe.mpr hv, Set.mem_iUnion₂.mpr ⟨m, hm, hmem⟩⟩)`.
-/
theorem eigenvalue_avoidance : EigAvoid := by
  intro F E _ _ _ _ _ n _ _ σ hσ hθ T g
  classical
  obtain ⟨θ, hθ⟩ := hθ
  let bad : Set E := ⋃ v ∈ (T : Set (HeightOneSpectrum (𝓞 F))),
    ⋃ m ∈ {m : Ideal (E ⊗[F] v.adicCompletion F) | m.IsMaximal},
      {μ : E | (1 + PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) μ • g v).det ∈ m}
  have hbad : bad.Finite := by
    refine Set.Finite.biUnion T.finite_toSet fun v _ => ?_
    haveI : IsArtinianRing (E ⊗[F] v.adicCompletion F) := ea_artinian v
    refine Set.Finite.biUnion (IsArtinianRing.setOfPred_isMaximal_finite _) fun m hm => ?_
    haveI : m.IsMaximal := hm
    exact ea_finite_bad _ (g v) m
  have hnz1 : ∀ t : ℕ, (t : E) + θ ≠ 0 := by
    intro t h
    apply hθ
    have h' : θ = -(t : E) := by linear_combination h
    rw [h', map_neg, map_natCast]
  have hnz2 : ∀ t : ℕ, (t : E) + σ θ ≠ 0 := by
    intro t h
    apply hθ
    have h' : σ θ = -(t : E) := by linear_combination h
    have h'' : θ = -(t : E) := by rw [← hσ θ, h', map_neg, map_natCast]
    rw [h', h'']
  let f : ℕ → E := fun t => ((t : E) + θ) / ((t : E) + σ θ)
  have hinj : Function.Injective f := by
    intro s t hst
    have hst' : ((s : E) + θ) / ((s : E) + σ θ) = ((t : E) + θ) / ((t : E) + σ θ) := hst
    rw [div_eq_div_iff (hnz2 s) (hnz2 t)] at hst'
    have h2 : ((s : E) - t) * (σ θ - θ) = 0 := by linear_combination hst'
    rcases mul_eq_zero.mp h2 with h | h
    · exact_mod_cast sub_eq_zero.mp h
    · exact absurd (sub_eq_zero.mp h) hθ
  have hrange : ¬ Set.range f ⊆ bad := fun h =>
    Set.infinite_range_of_injective hinj (hbad.subset h)
  obtain ⟨_, ⟨t, rfl⟩, ht⟩ := Set.not_subset.mp hrange
  refine ⟨f t, ?_, ?_⟩
  · show σ (((t : E) + θ) / ((t : E) + σ θ)) * (((t : E) + θ) / ((t : E) + σ θ)) = 1
    rw [map_div₀, map_add, map_add, map_natCast, hσ]
    have h1 := hnz1 t
    have h2 := hnz2 t
    field_simp
  · intro v hv
    by_contra hu
    obtain ⟨m, hm, hmem⟩ := exists_max_ideal_of_mem_nonunits hu
    exact ht (Set.mem_iUnion₂.mpr ⟨v, Finset.mem_coe.mpr hv, Set.mem_iUnion₂.mpr ⟨m, hm, hmem⟩⟩)

end PI.UnitaryApproxFinWork

end
