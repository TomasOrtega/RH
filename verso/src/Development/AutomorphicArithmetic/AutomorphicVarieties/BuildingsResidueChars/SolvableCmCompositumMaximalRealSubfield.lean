import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SignAgreement.ExistsCompositumWithPrimeDegreeGalois
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

/- English proof (translation)
Introduce `φ`. Establish `h : x ∈ maximalRealSubfield L`. Rewrite using `[IsTotallyReal.maximalRealSubfield_eq_top]`. Discharge the goal by the elementary cases of `trivial`. Conclude with `h (φ.comp f)`.
-/
private theorem rcsup_mem_real {L M' : Type} [Field L] [Field M'] (f : L →+* M') (hL : IsTotallyReal L) (x : L) :
    f x ∈ maximalRealSubfield M' := by
  intro φ
  have h : x ∈ maximalRealSubfield L := by
    rw [IsTotallyReal.maximalRealSubfield_eq_top]; trivial
  exact h (φ.comp f)

/- English proof (translation)
Introduce `φ` and use `hx (φ.comp g)`.
-/
private theorem rcsup_map_real {M M' : Type} [Field M] [Field M'] (g : M →+* M') {x : M}
    (hx : x ∈ maximalRealSubfield M) : g x ∈ maximalRealSubfield M' :=
  fun φ => hx (φ.comp g)

/- English proof (translation)
Establish `hli : LinearIndependent (maximalRealSubfield K) ![(1 : K), d]`. Rewrite using `[LinearIndependent.pair_iff]`. Introduce `s t hst`. Set `φ : K →+* ℂ` to `Classical.choice (inferInstance : Nonempty _)`. Establish `h0 : (s : K) + (t : K) * d = 0`.

Simplify `hst` using `[Subfield.smul_def]`. Establish `h1 : φ s + φ t * φ d = 0`. Rewrite using `[← map_mul, ← map_add, h0, map_zero]`. Establish `h2 : φ s - φ t * φ d = 0`. Use `congrArg star h1` as an intermediate fact.

Rewrite `this` using `[star_add, star_mul', s.2 φ, t.2 φ, hd φ, star_zero]`. Take the linear combination `this`. Establish `h3 : φ s = 0` using `by linear_combination (h1 + h2) / 2`. Establish `hs : (s : K) = 0` using `(map_eq_zero φ).mp h3`. Establish `ht : (t : K) = 0`.

Rewrite `h0` using `[hs, zero_add]`. Conclude with `(mul_eq_zero.mp h0).resolve_right hd0`. Conclude with `⟨Subtype.ext hs, Subtype.ext ht⟩`. Establish `hsp : ⊤ ≤ Submodule.span (maximalRealSubfield K) (Set.range ![(1 : K), d])`. Introduce `y _`.

Take `⟨a, ha, b, hb, rfl⟩` from `hspan y`. Establish `e : a + b * d = (⟨a, ha⟩ : maximalRealSubfield K) • (1 : K) + (⟨b, hb⟩ : maximalRealSubfield K) • d`. Simplify using `[Subfield.smul_def]`. Rewrite using `[e]`. Conclude with `Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)) (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))`.

Establish `hrk : Module.finrank (maximalRealSubfield K) K = 2`. Rewrite using `[Module.finrank_eq_card_basis (Module.Basis.mk hli hsp)]`. Simplify using the standard rewrite rules. Use `haveI : Algebra.IsQuadraticExtension (maximalRealSubfield K) K := { finrank_eq_two' := hrk }`. Conclude with `{}`.
-/
private theorem rcsup_cm_of_pair {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] (d : K) (hd0 : d ≠ 0)
    (hd : ∀ φ : K →+* ℂ, star (φ d) = - φ d)
    (hspan : ∀ y : K, ∃ a ∈ maximalRealSubfield K, ∃ b ∈ maximalRealSubfield K, y = a + b * d) :
    IsCMField K := by
  have hli : LinearIndependent (maximalRealSubfield K) ![(1 : K), d] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    let φ : K →+* ℂ := Classical.choice (inferInstance : Nonempty _)
    have h0 : (s : K) + (t : K) * d = 0 := by
      simpa [Subfield.smul_def] using hst
    have h1 : φ s + φ t * φ d = 0 := by
      rw [← map_mul, ← map_add, h0, map_zero]
    have h2 : φ s - φ t * φ d = 0 := by
      have := congrArg star h1
      rw [star_add, star_mul', s.2 φ, t.2 φ, hd φ, star_zero] at this
      linear_combination this
    have h3 : φ s = 0 := by linear_combination (h1 + h2) / 2
    have hs : (s : K) = 0 := (map_eq_zero φ).mp h3
    have ht : (t : K) = 0 := by
      rw [hs, zero_add] at h0
      exact (mul_eq_zero.mp h0).resolve_right hd0
    exact ⟨Subtype.ext hs, Subtype.ext ht⟩
  have hsp : ⊤ ≤ Submodule.span (maximalRealSubfield K) (Set.range ![(1 : K), d]) := by
    intro y _
    obtain ⟨a, ha, b, hb, rfl⟩ := hspan y
    have e : a + b * d = (⟨a, ha⟩ : maximalRealSubfield K) • (1 : K) + (⟨b, hb⟩ : maximalRealSubfield K) • d := by
      simp [Subfield.smul_def]
    rw [e]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  have hrk : Module.finrank (maximalRealSubfield K) K = 2 := by
    rw [Module.finrank_eq_card_basis (Module.Basis.mk hli hsp)]
    simp
  haveI : Algebra.IsQuadraticExtension (maximalRealSubfield K) K := { finrank_eq_two' := hrk }
  exact {}

/- English proof (translation)
Introduce `L M M' _ _ _ _ _ _ _ f hL htop hM`. Break down `hM with hM | hM` into its components or cases. Use `left`. Rewrite using `[← maximalRealSubfield_eq_top_iff_isTotallyReal, eq_top_iff]`. Introduce `y _`.

Establish `hy : y ∈ Algebra.adjoin M (Set.range f)` using `htop ▸ Algebra.mem_top`. Proceed by induction on `hy using Algebra.adjoin_induction with`. Consider the case `mem x hx => obtain ⟨z, rfl⟩ := hx`. Conclude with `rcsup_mem_real f hL z`. Consider the case `algebraMap r => exact rcsup_mem_real _ hM r`.

Consider the case `add x y _ _ hx hy => exact add_mem (hx trivial) (hy trivial)`. Consider the case `mul x y _ _ hx hy => exact mul_mem (hx trivial) (hy trivial)`. Use `right haveI : IsTotallyComplex M' := isTotallyComplex_of_algebra M M'`. Choose the witnesses or unpack the hypotheses as in `⟨x, hx⟩ : ∃ x : M, IsCMField.complexConj M x ≠ x := by`. Assume the negation of the conclusion as `h`.

Apply `IsCMField.complexConj_ne_one M` to reduce the goal to its premises. Use extensionality with `x`. Assume the negation of the conclusion as `h'`. Conclude with `h ⟨x, h'⟩`. Use `set δ : M := x - IsCMField.complexConj M x with hδ`.

Establish `hδ0 : δ ≠ 0` using `sub_ne_zero.mpr hx.symm`. Establish `hcδ : IsCMField.complexConj M δ = -δ`. Rewrite using `[hδ, map_sub, IsCMField.complexConj_apply_apply]`. Expand and normalize the polynomial expressions, which then agree. Establish `hd : ∀ φ : M' →+* ℂ, star (φ (algebraMap M M' δ)) = - φ (algebraMap M M' δ)`.

Introduce `φ`. Use `IsCMField.complexEmbedding_complexConj M (φ.comp (algebraMap M M')) δ` as an intermediate fact. Rewrite `this` using `[hcδ, map_neg]`. Conclude with `this.symm`. Establish `hsq : algebraMap M M' δ * algebraMap M M' δ ∈ maximalRealSubfield M'`.

Introduce `φ`. Rewrite using `[map_mul, star_mul', hd φ]`. Expand and normalize the polynomial expressions, which then agree. Use `rcsup_cm_of_pair (algebraMap M M' δ) ((_root_.map_ne_zero _).mpr hδ0) hd ?_` and prove the remaining obligations. Introduce `y`.

Establish `hy : y ∈ Algebra.adjoin M (Set.range f)` using `htop ▸ Algebra.mem_top`. Proceed by induction on `hy using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Take `⟨z, rfl⟩` from `hx`. Conclude with `⟨f z, rcsup_mem_real f hL z, 0, zero_mem _, by simp⟩`.

Consider the case `algebraMap r`. Use `⟨algebraMap M M' ((r + IsCMField.complexConj M r) / 2), rcsup_map_real _ ?_, algebraMap M M' ((r - IsCMField.complexConj M r) / (2 * δ)), rcsup_map_real _ ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← IsCMField.complexConj_eq_self_iff, map_div₀, map_add, IsCMField.complexConj_apply_apply, map_ofNat, add_comm]`. Rewrite using `[← IsCMField.complexConj_eq_self_iff, map_div₀, map_sub, map_mul, IsCMField.complexConj_apply_apply, map_ofNat, hcδ]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← map_mul, ← map_add]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Consider the case `add x y _ _ hx hy`. Take `⟨a, ha, b, hb, rfl⟩` from `hx`. Take `⟨a', ha', b', hb', rfl⟩` from `hy`. Conclude with `⟨a + a', add_mem ha ha', b + b', add_mem hb hb', by ring⟩`. Consider the case `mul x y _ _ hx hy`.

Take `⟨a, ha, b, hb, rfl⟩` from `hx`. Take `⟨a', ha', b', hb', rfl⟩` from `hy`. Conclude with `⟨a * a' + b * b' * (algebraMap M M' δ * algebraMap M M' δ), add_mem (mul_mem ha ha') (mul_mem (mul_mem hb hb') hsq), a * b' + b * a', add_mem (mul_mem ha hb') (mul_mem hb ha'), by ring⟩`.
-/
theorem UpperTheory.solvable_cm_compositum_maximalRealSubfield :
    UpperTheory.V.Af.Sol.RCSup := by
  intro L M M' _ _ _ _ _ _ _ f hL htop hM
  rcases hM with hM | hM
  · left
    rw [← maximalRealSubfield_eq_top_iff_isTotallyReal, eq_top_iff]
    intro y _
    have hy : y ∈ Algebra.adjoin M (Set.range f) := htop ▸ Algebra.mem_top
    induction hy using Algebra.adjoin_induction with
    | mem x hx => obtain ⟨z, rfl⟩ := hx; exact rcsup_mem_real f hL z
    | algebraMap r => exact rcsup_mem_real _ hM r
    | add x y _ _ hx hy => exact add_mem (hx trivial) (hy trivial)
    | mul x y _ _ hx hy => exact mul_mem (hx trivial) (hy trivial)
  · right
    haveI : IsTotallyComplex M' := isTotallyComplex_of_algebra M M'
    obtain ⟨x, hx⟩ : ∃ x : M, IsCMField.complexConj M x ≠ x := by
      by_contra h
      apply IsCMField.complexConj_ne_one M
      ext x
      by_contra h'
      exact h ⟨x, h'⟩
    set δ : M := x - IsCMField.complexConj M x with hδ
    have hδ0 : δ ≠ 0 := sub_ne_zero.mpr hx.symm
    have hcδ : IsCMField.complexConj M δ = -δ := by
      rw [hδ, map_sub, IsCMField.complexConj_apply_apply]; ring
    have hd : ∀ φ : M' →+* ℂ, star (φ (algebraMap M M' δ)) = - φ (algebraMap M M' δ) := by
      intro φ
      have := IsCMField.complexEmbedding_complexConj M (φ.comp (algebraMap M M')) δ
      rw [hcδ, map_neg] at this
      exact this.symm
    have hsq : algebraMap M M' δ * algebraMap M M' δ ∈ maximalRealSubfield M' := by
      intro φ
      rw [map_mul, star_mul', hd φ]; ring
    refine rcsup_cm_of_pair (algebraMap M M' δ) ((_root_.map_ne_zero _).mpr hδ0) hd ?_
    intro y
    have hy : y ∈ Algebra.adjoin M (Set.range f) := htop ▸ Algebra.mem_top
    induction hy using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨z, rfl⟩ := hx
      exact ⟨f z, rcsup_mem_real f hL z, 0, zero_mem _, by simp⟩
    | algebraMap r =>
      refine ⟨algebraMap M M' ((r + IsCMField.complexConj M r) / 2), rcsup_map_real _ ?_,
        algebraMap M M' ((r - IsCMField.complexConj M r) / (2 * δ)), rcsup_map_real _ ?_, ?_⟩
      · rw [← IsCMField.complexConj_eq_self_iff, map_div₀, map_add, IsCMField.complexConj_apply_apply, map_ofNat, add_comm]
      · rw [← IsCMField.complexConj_eq_self_iff, map_div₀, map_sub, map_mul, IsCMField.complexConj_apply_apply, map_ofNat, hcδ]
        field_simp
        ring
      · rw [← map_mul, ← map_add]
        congr 1
        field_simp
        ring
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hx
      obtain ⟨a', ha', b', hb', rfl⟩ := hy
      exact ⟨a + a', add_mem ha ha', b + b', add_mem hb hb', by ring⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hx
      obtain ⟨a', ha', b', hb', rfl⟩ := hy
      exact ⟨a * a' + b * b' * (algebraMap M M' δ * algebraMap M M' δ),
        add_mem (mul_mem ha ha') (mul_mem (mul_mem hb hb') hsq),
        a * b' + b * a', add_mem (mul_mem ha hb') (mul_mem hb ha'), by ring⟩
