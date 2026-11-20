import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.IsTanZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FinDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.CopNormLt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.MapApi
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.RepApi

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

/- English proof (translation)
Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Establish `sumlt : ∀ (t : Finset ℕ) (f : ℕ → K) (r : ℝ), 0 < r → (∀ i ∈ t, ‖f i‖ < r) → ‖∑ i ∈ t, f i‖ < r`. Introduce `t f r hr`. Proceed by induction on `t using Finset.induction_on with`.

Consider the case `empty => intro _`. Simplify using `using hr`. Consider the case `insert j t hj ih`. Introduce `hf`. Rewrite using `[Finset.sum_insert hj]`.

Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt (hf j (Finset.mem_insert_self _ _)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi)))`. Establish `hsum : p.eval s = s ^ p.natDegree + ∑ i ∈ Finset.range p.natDegree, p.coeff i * s ^ i` using `by conv_lhs => rw [hp.as_sum]`. Simplify using `[eval_finset_sum]`. Establish `hpos : 0 < ‖s‖` using `lt_of_lt_of_le one_pos hlt`. Establish `hlt2 : ‖∑ i ∈ Finset.range p.natDegree, p.coeff i * s ^ i‖ < ‖s‖ ^ p.natDegree`.

Apply `sumlt _ _ _ (pow_pos hpos _)` to reduce the goal to its premises. Introduce `i hi`. Rewrite `hi` using `[Finset.mem_range]`. Rewrite using `[norm_mul, norm_pow]`. Combine the equalities or inequalities in the displayed calculation.

Establish `heq : s ^ p.natDegree = -∑ i ∈ Finset.range p.natDegree, p.coeff i * s ^ i`. Rewrite `hsum` using `[hs]`. Conclude with `eq_neg_of_add_eq_zero_left hsum.symm`. Establish `h3` using `congrArg norm heq`. Rewrite `h3` using `[norm_neg, norm_pow]`.

Rewrite `hlt2` using `[h3]`. Conclude with `lt_irrefl _ hlt2`.
-/
private theorem rn_root {K : Type} [NormedField K] [IsUltrametricDist K] (p : K[X]) (hp : p.Monic)
    (hc : ∀ i < p.natDegree, ‖p.coeff i‖ < 1) (s : K) (hs : p.eval s = 0) : ‖s‖ < 1 := by
  by_contra hlt
  push_neg at hlt
  have sumlt : ∀ (t : Finset ℕ) (f : ℕ → K) (r : ℝ), 0 < r → (∀ i ∈ t, ‖f i‖ < r) → ‖∑ i ∈ t, f i‖ < r := by
    intro t f r hr
    induction t using Finset.induction_on with
    | empty => intro _; simpa using hr
    | insert j t hj ih =>
      intro hf
      rw [Finset.sum_insert hj]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt
        (max_lt (hf j (Finset.mem_insert_self _ _)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi)))
  have hsum : p.eval s = s ^ p.natDegree + ∑ i ∈ Finset.range p.natDegree, p.coeff i * s ^ i := by
    conv_lhs => rw [hp.as_sum]
    simp [eval_finset_sum]
  have hpos : 0 < ‖s‖ := lt_of_lt_of_le one_pos hlt
  have hlt2 : ‖∑ i ∈ Finset.range p.natDegree, p.coeff i * s ^ i‖ < ‖s‖ ^ p.natDegree := by
    apply sumlt _ _ _ (pow_pos hpos _)
    intro i hi
    rw [Finset.mem_range] at hi
    rw [norm_mul, norm_pow]
    calc ‖p.coeff i‖ * ‖s‖ ^ i < 1 * ‖s‖ ^ i :=
          mul_lt_mul_of_pos_right (hc i hi) (pow_pos hpos _)
      _ = ‖s‖ ^ i := one_mul _
      _ ≤ ‖s‖ ^ p.natDegree := pow_le_pow_right₀ hlt hi.le
  have heq : s ^ p.natDegree = -∑ i ∈ Finset.range p.natDegree, p.coeff i * s ^ i := by
    rw [hs] at hsum
    exact eq_neg_of_add_eq_zero_left hsum.symm
  have h3 := congrArg norm heq
  rw [norm_neg, norm_pow] at h3
  rw [h3] at hlt2
  exact lt_irrefl _ hlt2

/- English proof (translation)
Introduce `l _ F c n r B x ρ hD g a ha t ht`. Establish `hsing : ∀ {A A' : Type} [CommRing A] [CommRing A'] (f : A →+* A'), MonoidAlgebra.mapRingHom F.G₀ f (MonoidAlgebra.single g 1) = MonoidAlgebra.single g 1`. Introduce `A A' _ _ f`. Simplify using `[MonoidAlgebra.mapRingHom]`. Use `set Q := B.u.D.chi (MonoidAlgebra.single g 1) with hQ`.

Establish `hx : (W.mat ρ g).charpoly = Q.map (x : B.B →+* PadicAlgCl l)`. Establish `h1` using `(AlgebraTools.Det.mapApi B.u.D (x : B.B →+* PadicAlgCl l)).1 (MonoidAlgebra.single g 1)`. Rewrite `h1` using `[hsing, hD, (AlgebraTools.Det.repApi (W.mat ρ)).2.1]`. Conclude with `h1`. Establish `hred : Q.map (res c.O B.B : B.B →+* ResidueField c.O) = (X - C (residue c.O a)) ^ n`.

Establish `h1` using `(AlgebraTools.Det.mapApi B.u.D (res c.O B.B : B.B →+* ResidueField c.O)).1 (MonoidAlgebra.single g 1)`. Rewrite `h1` using `[hsing, B.u.red, W.Resid.Dbar, (AlgebraTools.Det.repApi _).2.1]`. Rewrite using `[← h1]`. Use `show (Matrix.diagonal _).charpoly = _`. Rewrite using `[Matrix.charpoly_diagonal]`.

Simplify using `[← ha]`. Use `set Q' := Q.comp (X + C (algebraMap c.O B.B a)) with hQ'`. Use `set p := (W.mat ρ g).charpoly.comp (X + C (a : PadicAlgCl l)) with hp`. Establish `hpQ : p = Q'.map (x : B.B →+* PadicAlgCl l)`. Rewrite using `[hp, hQ', hx, Polynomial.map_comp]`.

Simplify using the standard rewrite rules. Establish `hQm : ∀ i < n, Q'.coeff i ∈ maximalIdeal B.B`. Introduce `i hi`. Rewrite using `[← res_eq_zero_iff c.O B.B, ← RingHom.coe_coe (res c.O B.B), ← Polynomial.coeff_map, hQ', Polynomial.map_comp, hred]`. Simplify using `[ResidueField.algebraMap_eq, Polynomial.coeff_X_pow, hi.ne]`.

Take `⟨_, a0, ha1, _, hb⟩` from `(coPt c B.B).1 x`. Establish `hmon : p.Monic` using `(Matrix.charpoly_monic _).comp_X_add_C _`. Establish `hdeg : p.natDegree = n`. Rewrite using `[hp, Polynomial.natDegree_comp, Matrix.charpoly_natDegree_eq_dim, Polynomial.natDegree_X_add_C]`. Simplify using the standard rewrite rules.

Establish `hc : ∀ i < p.natDegree, ‖p.coeff i‖ < 1`. Introduce `i hi`. Rewrite `hi` using `[hdeg]`. Rewrite using `[hpQ, Polynomial.coeff_map]`. Use `hb 1 _ (by rw [pow_one]; exact hQm i hi)` as an intermediate fact.

Rewrite `this` using `[pow_one]`. Conclude with `this.trans_lt ha1`. Establish `hroot : p.eval (t - (a : PadicAlgCl l)) = 0`. Rewrite using `[hp, Polynomial.eval_comp]`. Simplify using `only [eval_add, eval_X, eval_C, sub_add_cancel]`.

Conclude with `(Polynomial.mem_roots'.mp ht).2`. Conclude with `rn_root p hmon hc _ hroot`.
-/
theorem UpperTheory.V.Ws.Eb.rootsNear :
    ∀ {l : ℕ} [Fact l.Prime] {F : W.GFrame l} {c : Coef l} {n : ℕ} {r : W.Resid F c.O n} (B : W.UniversalOrdinaryDeterminantRing r) (x : B.B →ₐ[c.O] PadicAlgCl l) (ρ : F.G₀ →* GL (Fin n) (PadicAlgCl l)), B.u.D.map (x : B.B →+* PadicAlgCl l) = W.GDet.ofRep (W.mat ρ) →
        ∀ g (a : c.O), (∀ i, residue c.O a = r.chib i g) → ∀ t ∈ (W.mat ρ g).charpoly.roots, ‖t - (a : PadicAlgCl l)‖ < 1 := by
  intro l _ F c n r B x ρ hD g a ha t ht
  have hsing : ∀ {A A' : Type} [CommRing A] [CommRing A'] (f : A →+* A'),
      MonoidAlgebra.mapRingHom F.G₀ f (MonoidAlgebra.single g 1) = MonoidAlgebra.single g 1 := by
    intro A A' _ _ f
    simp [MonoidAlgebra.mapRingHom]
  set Q := B.u.D.chi (MonoidAlgebra.single g 1) with hQ
  have hx : (W.mat ρ g).charpoly = Q.map (x : B.B →+* PadicAlgCl l) := by
    have h1 := (AlgebraTools.Det.mapApi B.u.D (x : B.B →+* PadicAlgCl l)).1 (MonoidAlgebra.single g 1)
    rw [hsing, hD, (AlgebraTools.Det.repApi (W.mat ρ)).2.1] at h1
    exact h1
  have hred : Q.map (res c.O B.B : B.B →+* ResidueField c.O) = (X - C (residue c.O a)) ^ n := by
    have h1 := (AlgebraTools.Det.mapApi B.u.D (res c.O B.B : B.B →+* ResidueField c.O)).1 (MonoidAlgebra.single g 1)
    rw [hsing, B.u.red, W.Resid.Dbar, (AlgebraTools.Det.repApi _).2.1] at h1
    rw [← h1]
    show (Matrix.diagonal _).charpoly = _
    rw [Matrix.charpoly_diagonal]
    simp [← ha]
  set Q' := Q.comp (X + C (algebraMap c.O B.B a)) with hQ'
  set p := (W.mat ρ g).charpoly.comp (X + C (a : PadicAlgCl l)) with hp
  have hpQ : p = Q'.map (x : B.B →+* PadicAlgCl l) := by
    rw [hp, hQ', hx, Polynomial.map_comp]
    simp
  have hQm : ∀ i < n, Q'.coeff i ∈ maximalIdeal B.B := by
    intro i hi
    rw [← res_eq_zero_iff c.O B.B, ← RingHom.coe_coe (res c.O B.B), ← Polynomial.coeff_map, hQ',
      Polynomial.map_comp, hred]
    simp [ResidueField.algebraMap_eq, Polynomial.coeff_X_pow, hi.ne]
  obtain ⟨_, a0, ha1, _, hb⟩ := (coPt c B.B).1 x
  have hmon : p.Monic := (Matrix.charpoly_monic _).comp_X_add_C _
  have hdeg : p.natDegree = n := by
    rw [hp, Polynomial.natDegree_comp, Matrix.charpoly_natDegree_eq_dim, Polynomial.natDegree_X_add_C]
    simp
  have hc : ∀ i < p.natDegree, ‖p.coeff i‖ < 1 := by
    intro i hi
    rw [hdeg] at hi
    rw [hpQ, Polynomial.coeff_map]
    have := hb 1 _ (by rw [pow_one]; exact hQm i hi)
    rw [pow_one] at this
    exact this.trans_lt ha1
  have hroot : p.eval (t - (a : PadicAlgCl l)) = 0 := by
    rw [hp, Polynomial.eval_comp]
    simp only [eval_add, eval_X, eval_C, sub_add_cancel]
    exact (Polynomial.mem_roots'.mp ht).2
  exact rn_root p hmon hc _ hroot
