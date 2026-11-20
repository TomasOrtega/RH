import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.EllipticityFromProductFormula
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SiegelConj
open NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped NumberField.AdeleRing

section BlockTri

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] (Q : ι → Prop) [DecidablePred Q]

private def LowZero (M : Matrix ι ι R) : Prop := ∀ j, ¬ Q j → ∀ i, Q i → M j i = 0

/- English proof (translation)
Introduce `j hj i hi`. Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Distinguish the cases in `hk : Q k`. Rewrite using `[hA j hj k hk, zero_mul]`.

Rewrite using `[hB k hk i hi, mul_zero]`.
-/
private theorem lowZero_mul {A B : Matrix ι ι R} (hA : LowZero Q A) (hB : LowZero Q B) :
    LowZero Q (A * B) := by
  intro j hj i hi
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : Q k
  · rw [hA j hj k hk, zero_mul]
  · rw [hB k hk i hi, mul_zero]

/- English proof (translation)
Use extensionality with `⟨i, hi⟩ ⟨l, hl⟩`. Express the relevant statement in the definitionally equal form `(A * B) i l = ∑ k : {x // Q x}, A i k * B k l`. Rewrite using `[Matrix.mul_apply, ← Fintype.sum_subtype_add_sum_subtype Q]`. Establish `h0 : ∑ k : {x // ¬ Q x}, A i k * B k l = 0` using `Finset.sum_eq_zero fun k _ => by rw [hB k k.2 l hl, mul_zero]`. Rewrite using `[h0, add_zero]`.
-/
private theorem toSq_mul {A B : Matrix ι ι R} (hB : LowZero Q B) :
    (A * B).toSquareBlockProp Q = A.toSquareBlockProp Q * B.toSquareBlockProp Q := by
  ext ⟨i, hi⟩ ⟨l, hl⟩
  change (A * B) i l = ∑ k : {x // Q x}, A i k * B k l
  rw [Matrix.mul_apply, ← Fintype.sum_subtype_add_sum_subtype Q]
  have h0 : ∑ k : {x // ¬ Q x}, A i k * B k l = 0 :=
    Finset.sum_eq_zero fun k _ => by rw [hB k k.2 l hl, mul_zero]
  rw [h0, add_zero]

/- English proof (translation)
Establish `hz : ∀ i, ¬ Q i → ∀ j, Q j → M.charmatrix i j = 0`. Introduce `i hi j hj`. Establish `hij : i ≠ j` using `fun h => hi (h ▸ hj)`. Rewrite using `[Matrix.charmatrix_apply_ne M i j hij, hM i hi j hj]`. Simplify using the standard rewrite rules.

Establish `hsq : (M.charmatrix).toSquareBlockProp Q = (M.toSquareBlockProp Q).charmatrix` using `by ext1 ⟨i, hi⟩ ⟨j, hj⟩`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Express the relevant statement in the definitionally equal form `M.charmatrix i i = (M.toSquareBlockProp Q).charmatrix ⟨i, hi⟩ ⟨i, hi⟩`. Rewrite using `[Matrix.charmatrix_apply_eq, Matrix.charmatrix_apply_eq]`.

Both sides reduce to the same expression. Establish `hne : (⟨i, hi⟩ : {x // Q x}) ≠ ⟨j, hj⟩` using `fun h => hij (congrArg Subtype.val h)`. Express the relevant statement in the definitionally equal form `M.charmatrix i j = (M.toSquareBlockProp Q).charmatrix ⟨i, hi⟩ ⟨j, hj⟩`. Rewrite using `[Matrix.charmatrix_apply_ne M i j hij, Matrix.charmatrix_apply_ne _ _ _ hne]`. Both sides reduce to the same expression.

Establish `h` using `Matrix.twoBlockTriangular_det (M.charmatrix) Q hz`. Rewrite `h` using `[hsq]`. Conclude with `⟨_, h⟩`.
-/
private theorem charpoly_toSq_dvd {M : Matrix ι ι R} (hM : LowZero Q M) :
    (M.toSquareBlockProp Q).charpoly ∣ M.charpoly := by
  have hz : ∀ i, ¬ Q i → ∀ j, Q j → M.charmatrix i j = 0 := by
    intro i hi j hj
    have hij : i ≠ j := fun h => hi (h ▸ hj)
    rw [Matrix.charmatrix_apply_ne M i j hij, hM i hi j hj]
    simp
  have hsq : (M.charmatrix).toSquareBlockProp Q = (M.toSquareBlockProp Q).charmatrix := by
    ext1 ⟨i, hi⟩ ⟨j, hj⟩
    by_cases hij : i = j
    · subst hij
      change M.charmatrix i i = (M.toSquareBlockProp Q).charmatrix ⟨i, hi⟩ ⟨i, hi⟩
      rw [Matrix.charmatrix_apply_eq, Matrix.charmatrix_apply_eq]
      rfl
    · have hne : (⟨i, hi⟩ : {x // Q x}) ≠ ⟨j, hj⟩ := fun h => hij (congrArg Subtype.val h)
      change M.charmatrix i j = (M.toSquareBlockProp Q).charmatrix ⟨i, hi⟩ ⟨j, hj⟩
      rw [Matrix.charmatrix_apply_ne M i j hij, Matrix.charmatrix_apply_ne _ _ _ hne]
      rfl
  have h := Matrix.twoBlockTriangular_det (M.charmatrix) Q hz
  rw [hsq] at h
  exact ⟨_, h⟩

end BlockTri

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hgen n δ p hp hpc r hr0 hrn`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Set `Q : Fin n → Prop` to `fun i => (i : ℕ) < r`. Establish `hL : LowZero Q (δ : Matrix (Fin n) (Fin n) E)` using `fun j hj i hi => hcon i j hi (not_lt.mp hj)`.

Establish `hdet : ((δ : Matrix (Fin n) (Fin n) E).toSquareBlockProp Q).det ≠ 0`. Introduce `h0`. Establish `h` using `Matrix.twoBlockTriangular_det (δ : Matrix (Fin n) (Fin n) E) Q hL`. Rewrite `h` using `[h0, zero_mul]`. Establish `hu : IsUnit (δ : Matrix (Fin n) (Fin n) E).det` using `(Matrix.isUnit_iff_isUnit_det _).mp δ.isUnit`.

Conclude with `hu.ne_zero h`. Set `δ₁ : GL {i // Q i} E` to `Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet`. Establish `hδ₁ : (δ₁ : Matrix {i // Q i} {i // Q i} E) = (δ : Matrix (Fin n) (Fin n) E).toSquareBlockProp Q` using `rfl`. Establish `key : ∀ m : ℕ, LowZero Q ((twNorm (sigmaGL σ) m δ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) ∧ ((twNorm (sigmaGL σ) m δ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).toSquareBlockProp Q = ((twNorm (sigmaGL σ) m δ₁ : GL {i // Q i} E) : Matrix {i // Q i} {i // Q i} E)`. Introduce `m`.

Proceed by induction on `m with`. Consider the case `zero`. Prove the components needed by the constructor for the conclusion. Introduce `j hj i hi`. Establish `hij : j ≠ i` using `fun h => hj (h ▸ hi)`.

Simplify using `[hij]`. Use extensionality with `⟨i, hi⟩ ⟨l, hl⟩`. Simplify using `[Matrix.toSquareBlockProp, Matrix.one_apply]`. Consider the case `succ m ih`. Take `⟨ih1, ih2⟩` from `ih`.

Establish `hpow : ((((sigmaGL σ : Monoid.End (GL (Fin n) E)) ^ m) δ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = (δ : Matrix (Fin n) (Fin n) E).map (σ ^ m)`. Rewrite using `[← sigmaGL_pow, sigmaGL_val]`. Establish `hpow₁ : ((((sigmaGL σ : Monoid.End (GL {i // Q i} E)) ^ m) δ₁ : GL {i // Q i} E) : Matrix {i // Q i} {i // Q i} E) = (δ₁ : Matrix {i // Q i} {i // Q i} E).map (σ ^ m)`. Rewrite using `[← sigmaGL_pow, sigmaGL_val]`. Establish `hLm : LowZero Q ((δ : Matrix (Fin n) (Fin n) E).map (σ ^ m))`.

Introduce `j hj i hi`. Simplify using `[hL j hj i hi]`. Rewrite using `[twNorm_succ, twNorm_succ, Units.val_mul, Units.val_mul, hpow, hpow₁]`. Use `⟨lowZero_mul Q ih1 hLm, ?_⟩` and prove the remaining obligations. Rewrite using `[toSq_mul Q hLm, ih2, hδ₁]`.

Both sides reduce to the same expression. Establish `hdvd : ((normGL σ δ₁ : GL {i // Q i} E) : Matrix {i // Q i} {i // Q i} E).charpoly ∣ ((normGL σ δ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly`. Establish `h` using `charpoly_toSq_dvd Q (key (Module.finrank F E)).1`. Rewrite `h` using `[(key (Module.finrank F E)).2]`. Conclude with `h`.

Take `⟨P₁, hP₁⟩` from `charpoly_normGL_lifts σ hgen δ₁`. Establish `hdvd' : P₁ ∣ p`. Rewrite using `[← Polynomial.map_dvd_map' (algebraMap F E), hP₁, hpc]`. Conclude with `hdvd`. Establish `hdegP : P₁.natDegree = Fintype.card {i // Q i}`.

Rewrite using `[← Polynomial.natDegree_map (algebraMap F E) (p := P₁), hP₁, Matrix.charpoly_natDegree_eq_dim]`. Establish `hdegp : p.natDegree = n`. Rewrite using `[← Polynomial.natDegree_map (algebraMap F E) (p := p), hpc, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]`. Establish `hpos : 0 < Fintype.card {i // Q i}` using `Fintype.card_pos_iff.mpr ⟨⟨⟨0, by omega⟩, hr0⟩⟩`. Establish `hlt : Fintype.card {i // Q i} < n`.

Establish `h` using `Fintype.card_subtype_lt (p := Q) (x := (⟨r, hrn⟩ : Fin n)) (by simp [Q])`. Simplify using `using h`. Break down `hp.dvd_iff.mp hdvd' with hu | ha` into its components or cases. Establish `h0` using `Polynomial.natDegree_eq_zero_of_isUnit hu`. Use linear arithmetic over natural numbers and integers.

Establish `h1` using `Polynomial.natDegree_eq_of_degree_eq (Polynomial.degree_eq_degree_of_associated ha)`. Use linear arithmetic over natural numbers and integers.
-/
theorem UpperTheory.exists_lower_entry_ne_zero_of_norm_charpoly_irreducible :
    ∀ (F E : Type) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
          (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) → ∀ (n : ℕ) (δ : GL (Fin n) E) (p : F[X]), Irreducible p →
          p.map (algebraMap F E) = ((normGL σ δ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly →
          ∀ r : ℕ, 0 < r → r < n → ∃ i j : Fin n, (i : ℕ) < r ∧ r ≤ (j : ℕ) ∧ (δ : Matrix (Fin n) (Fin n) E) j i ≠ 0 := by
  intro F E _ _ _ _ _ σ hgen n δ p hp hpc r hr0 hrn
  by_contra hcon
  push_neg at hcon
  let Q : Fin n → Prop := fun i => (i : ℕ) < r
  have hL : LowZero Q (δ : Matrix (Fin n) (Fin n) E) :=
    fun j hj i hi => hcon i j hi (not_lt.mp hj)
  have hdet : ((δ : Matrix (Fin n) (Fin n) E).toSquareBlockProp Q).det ≠ 0 := by
    intro h0
    have h := Matrix.twoBlockTriangular_det (δ : Matrix (Fin n) (Fin n) E) Q hL
    rw [h0, zero_mul] at h
    have hu : IsUnit (δ : Matrix (Fin n) (Fin n) E).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp δ.isUnit
    exact hu.ne_zero h
  let δ₁ : GL {i // Q i} E := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet
  have hδ₁ : (δ₁ : Matrix {i // Q i} {i // Q i} E) =
      (δ : Matrix (Fin n) (Fin n) E).toSquareBlockProp Q := rfl
  have key : ∀ m : ℕ,
      LowZero Q ((twNorm (sigmaGL σ) m δ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) ∧
      ((twNorm (sigmaGL σ) m δ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).toSquareBlockProp Q =
        ((twNorm (sigmaGL σ) m δ₁ : GL {i // Q i} E) : Matrix {i // Q i} {i // Q i} E) := by
    intro m
    induction m with
    | zero =>
      constructor
      · intro j hj i hi
        have hij : j ≠ i := fun h => hj (h ▸ hi)
        simp [hij]
      · ext ⟨i, hi⟩ ⟨l, hl⟩
        simp [Matrix.toSquareBlockProp, Matrix.one_apply]
    | succ m ih =>
      obtain ⟨ih1, ih2⟩ := ih
      have hpow : ((((sigmaGL σ : Monoid.End (GL (Fin n) E)) ^ m) δ : GL (Fin n) E) :
          Matrix (Fin n) (Fin n) E) = (δ : Matrix (Fin n) (Fin n) E).map (σ ^ m) := by
        rw [← sigmaGL_pow, sigmaGL_val]
      have hpow₁ : ((((sigmaGL σ : Monoid.End (GL {i // Q i} E)) ^ m) δ₁ : GL {i // Q i} E) :
          Matrix {i // Q i} {i // Q i} E) =
            (δ₁ : Matrix {i // Q i} {i // Q i} E).map (σ ^ m) := by
        rw [← sigmaGL_pow, sigmaGL_val]
      have hLm : LowZero Q ((δ : Matrix (Fin n) (Fin n) E).map (σ ^ m)) := by
        intro j hj i hi
        simp [hL j hj i hi]
      rw [twNorm_succ, twNorm_succ, Units.val_mul, Units.val_mul, hpow, hpow₁]
      refine ⟨lowZero_mul Q ih1 hLm, ?_⟩
      rw [toSq_mul Q hLm, ih2, hδ₁]
      rfl
  have hdvd : ((normGL σ δ₁ : GL {i // Q i} E) : Matrix {i // Q i} {i // Q i} E).charpoly ∣
      ((normGL σ δ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly := by
    have h := charpoly_toSq_dvd Q (key (Module.finrank F E)).1
    rw [(key (Module.finrank F E)).2] at h
    exact h
  obtain ⟨P₁, hP₁⟩ := charpoly_normGL_lifts σ hgen δ₁
  have hdvd' : P₁ ∣ p := by
    rw [← Polynomial.map_dvd_map' (algebraMap F E), hP₁, hpc]
    exact hdvd
  have hdegP : P₁.natDegree = Fintype.card {i // Q i} := by
    rw [← Polynomial.natDegree_map (algebraMap F E) (p := P₁), hP₁, Matrix.charpoly_natDegree_eq_dim]
  have hdegp : p.natDegree = n := by
    rw [← Polynomial.natDegree_map (algebraMap F E) (p := p), hpc, Matrix.charpoly_natDegree_eq_dim,
      Fintype.card_fin]
  have hpos : 0 < Fintype.card {i // Q i} :=
    Fintype.card_pos_iff.mpr ⟨⟨⟨0, by omega⟩, hr0⟩⟩
  have hlt : Fintype.card {i // Q i} < n := by
    have h := Fintype.card_subtype_lt (p := Q) (x := (⟨r, hrn⟩ : Fin n)) (by simp [Q])
    simpa using h
  rcases hp.dvd_iff.mp hdvd' with hu | ha
  · have h0 := Polynomial.natDegree_eq_zero_of_isUnit hu
    omega
  · have h1 := Polynomial.natDegree_eq_of_degree_eq (Polynomial.degree_eq_degree_of_associated ha)
    omega
