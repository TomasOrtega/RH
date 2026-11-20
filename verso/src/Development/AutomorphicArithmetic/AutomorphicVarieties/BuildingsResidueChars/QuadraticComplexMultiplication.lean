import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealTransport.RealTransport
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Published
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc

/- English proof (translation)
Introduce `F Ω _ _ _ _ _ _ d δ hδ hd`. Establish `halg : Algebra.IsAlgebraic F Ω` using `IsAlgClosure.isAlgebraic`. Establish `hint : IsIntegral F δ` using `(halg.isAlgebraic δ).isIntegral`. Set `K : IntermediateField F Ω` to `IntermediateField.adjoin F {δ}`. Use `haveI : FiniteDimensional F K := IntermediateField.adjoin.finiteDimensional hint`.

Use `haveI : NumberField K := NumberField.of_module_finite F K`. Set `y : K` to `IntermediateField.AdjoinSimple.gen F δ`. Establish `hy : algebraMap K Ω y = δ` using `rfl`. Establish `hy2 : y ^ 2 = algebraMap F K d`. Apply `(algebraMap K Ω).injective` to reduce the goal to its premises.

Rewrite using `[map_pow, hy, hδ, ← IsScalarTower.algebraMap_apply]`. Establish `hle : (minpoly F δ).natDegree ≤ 2`. Establish `hm : (X ^ 2 - C d : F[X]).Monic` using `monic_X_pow_sub_C d (by norm_num)`. Establish `h1` using `minpoly.min F δ hm (by simp [hδ])`. Establish `h2` using `natDegree_le_natDegree h1`.

Rewrite `h2` using `[natDegree_X_pow_sub_C]`. Then use the resulting hypothesis. Establish `hne : (minpoly F δ).natDegree ≠ 1`. Introduce `h`. Take `⟨c, hc⟩` from `(minpoly.natDegree_eq_one_iff).1 h`. Establish `hcd : c ^ 2 = d`.

Apply `(algebraMap F Ω).injective` to reduce the goal to its premises. Rewrite using `[map_pow, hc, hδ]`. Set `v : InfinitePlace F` to `Classical.arbitrary _`. Establish `h3` using `hd (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v))`. Rewrite `h3` using `[← hcd, map_pow]`.

Conclude with `absurd h3 (not_lt.2 (sq_nonneg _))`. Establish `hpos` using `minpoly.natDegree_pos hint`. Establish `hdeg : (minpoly F δ).natDegree = 2` using `by omega`. Establish `hrk : Module.finrank F K = 2`. Rewrite using `[← hdeg]`.

Conclude with `IntermediateField.adjoin.finrank hint`. Use `haveI : IsTotallyComplex K := by`. Use `⟨fun v => ?_⟩` and prove the remaining obligations. Rewrite using `[← InfinitePlace.not_isReal_iff_isComplex]`. Introduce `hv`.

Establish `h3` using `hd ((InfinitePlace.embedding_of_isReal hv).comp (algebraMap F K))`. Rewrite `h3` using `[RingHom.comp_apply, ← hy2, map_pow]`. Conclude with `absurd h3 (not_lt.2 (sq_nonneg _))`. Use `haveI : Algebra.IsQuadraticExtension F K := { finrank_eq_two' := hrk }`. Use `haveI : IsAlgClosure K Ω := { isAlgClosed := IsAlgClosure.isAlgClosed F isAlgebraic := Algebra.IsAlgebraic.tower_top (K := F) K }`.

Use `⟨K, inferInstance, inferInstance, IsCMField.ofCMExtension F K, inferInstance, inferInstance, inferInstance, inferInstance, hrk, y, hy, fun x => ?_⟩` and prove the remaining obligations. Take `⟨f, hf, hx⟩` from `(IntermediateField.adjoin.powerBasis hint).exists_eq_aeval x`. Rewrite `hf` using `[IntermediateField.adjoin.powerBasis_dim, hdeg]`. Use `⟨f.coeff 0, f.coeff 1, ?_⟩` and prove the remaining obligations. Rewrite using `[hx, IntermediateField.adjoin.powerBasis_gen]`.

Use `conv_lhs => rw [eq_X_add_C_of_natDegree_le_one (p := f) (by omega)]`. Simplify using `only [map_add, map_mul, aeval_C, aeval_X]`. Conclude with `add_comm _ _`.
-/
theorem UpperTheory.quadratic_complex_multiplication :
    UpperTheory.V.Af.Cr.QuadCM := by
  intro F Ω _ _ _ _ _ _ d δ hδ hd
  have halg : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  have hint : IsIntegral F δ := (halg.isAlgebraic δ).isIntegral
  let K : IntermediateField F Ω := IntermediateField.adjoin F {δ}
  haveI : FiniteDimensional F K := IntermediateField.adjoin.finiteDimensional hint
  haveI : NumberField K := NumberField.of_module_finite F K
  let y : K := IntermediateField.AdjoinSimple.gen F δ
  have hy : algebraMap K Ω y = δ := rfl
  have hy2 : y ^ 2 = algebraMap F K d := by
    apply (algebraMap K Ω).injective
    rw [map_pow, hy, hδ, ← IsScalarTower.algebraMap_apply]
  have hle : (minpoly F δ).natDegree ≤ 2 := by
    have hm : (X ^ 2 - C d : F[X]).Monic := monic_X_pow_sub_C d (by norm_num)
    have h1 := minpoly.min F δ hm (by simp [hδ])
    have h2 := natDegree_le_natDegree h1
    rwa [natDegree_X_pow_sub_C] at h2
  have hne : (minpoly F δ).natDegree ≠ 1 := by
    intro h
    obtain ⟨c, hc⟩ := (minpoly.natDegree_eq_one_iff).1 h
    have hcd : c ^ 2 = d := by
      apply (algebraMap F Ω).injective
      rw [map_pow, hc, hδ]
    let v : InfinitePlace F := Classical.arbitrary _
    have h3 := hd (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v))
    rw [← hcd, map_pow] at h3
    exact absurd h3 (not_lt.2 (sq_nonneg _))
  have hpos := minpoly.natDegree_pos hint
  have hdeg : (minpoly F δ).natDegree = 2 := by omega
  have hrk : Module.finrank F K = 2 := by
    rw [← hdeg]; exact IntermediateField.adjoin.finrank hint
  haveI : IsTotallyComplex K := by
    refine ⟨fun v => ?_⟩
    rw [← InfinitePlace.not_isReal_iff_isComplex]
    intro hv
    have h3 := hd ((InfinitePlace.embedding_of_isReal hv).comp (algebraMap F K))
    rw [RingHom.comp_apply, ← hy2, map_pow] at h3
    exact absurd h3 (not_lt.2 (sq_nonneg _))
  haveI : Algebra.IsQuadraticExtension F K := { finrank_eq_two' := hrk }
  haveI : IsAlgClosure K Ω :=
    { isAlgClosed := IsAlgClosure.isAlgClosed F
      isAlgebraic := Algebra.IsAlgebraic.tower_top (K := F) K }
  refine ⟨K, inferInstance, inferInstance, IsCMField.ofCMExtension F K, inferInstance, inferInstance,
    inferInstance, inferInstance, hrk, y, hy, fun x => ?_⟩
  obtain ⟨f, hf, hx⟩ := (IntermediateField.adjoin.powerBasis hint).exists_eq_aeval x
  rw [IntermediateField.adjoin.powerBasis_dim, hdeg] at hf
  refine ⟨f.coeff 0, f.coeff 1, ?_⟩
  rw [hx, IntermediateField.adjoin.powerBasis_gen]
  conv_lhs => rw [eq_X_add_C_of_natDegree_le_one (p := f) (by omega)]
  simp only [map_add, map_mul, aeval_C, aeval_X]
  exact add_comm _ _
