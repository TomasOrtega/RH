import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.CjApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap
open IsLocalRing Matrix NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th UpperTheory.V.Th.Nm GlobalTheory.GalOfCusp

section SlopeTestRemainingChoices

open Polynomial

/- English proof (translation)
Use `letI : Algebra A K[X] := ((algebraMap K K[X]).comp f).toAlgebra`. Rewrite using `[← Matrix.charpoly_map]`. Express the relevant statement in the definitionally equal form `(GDet.repAlg ρ K[X] _).det = (Matrix.charmatrix _).det`. Use `congr 1`. Use extensionality with `i j : 1`.

Establish `h : ∀ a, algebraMap A K[X] a = C (f a)` using `fun _ => rfl`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using `[GDet.repAlg, h]`. Simplify using `[GDet.repAlg, h, hij]`.
-/
private theorem chi_map_ofRep {n : ℕ} {A K G : Type} [CommRing A] [CommRing K] [Group G] (f : A →+* K)
    (ρ : G →* Matrix (Fin n) (Fin n) A) (g : G) :
    ((GDet.ofRep ρ).map f).chi (MonoidAlgebra.single g 1) = (ρ g).charpoly.map f := by
  letI : Algebra A K[X] := ((algebraMap K K[X]).comp f).toAlgebra
  rw [← Matrix.charpoly_map]
  change (GDet.repAlg ρ K[X] _).det = (Matrix.charmatrix _).det
  congr 1
  ext i j : 1
  have h : ∀ a, algebraMap A K[X] a = C (f a) := fun _ => rfl
  by_cases hij : i = j
  · subst hij
    simp [GDet.repAlg, h]
  · simp [GDet.repAlg, h, hij]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(GDet.repAlg ρ A[X] _).det = (Matrix.charmatrix _).det`. Use `congr 1`. Use extensionality with `i j : 1`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality.

Simplify using `[GDet.repAlg]`. Simplify using `[GDet.repAlg, hij]`.
-/
private theorem chi_ofRep {n : ℕ} {A G : Type} [CommRing A] [Group G]
    (ρ : G →* Matrix (Fin n) (Fin n) A) (g : G) :
    (GDet.ofRep ρ).chi (MonoidAlgebra.single g 1) = (ρ g).charpoly := by
  change (GDet.repAlg ρ A[X] _).det = (Matrix.charmatrix _).det
  congr 1
  ext i j : 1
  by_cases hij : i = j
  · subst hij
    simp [GDet.repAlg]
  · simp [GDet.repAlg, hij]

/- English proof (translation)
Use `Polynomial.map_aeval_eq_aeval_map ?_ q M` and prove the remaining obligations. Use extensionality with `a i j`. Apply the tactic sequence `by_cases h : i = j <;> simp [Matrix.algebraMap_eq_diagonal, h]`.
-/
private theorem aeval_mapM {n : ℕ} {A K : Type} [CommRing A] [CommRing K] (f : A →+* K)
    (M : Matrix (Fin n) (Fin n) A) (q : A[X]) :
    f.mapMatrix (aeval M q) = aeval (f.mapMatrix M) (q.map f) := by
  refine Polynomial.map_aeval_eq_aeval_map ?_ q M
  ext a i j
  by_cases h : i = j <;> simp [Matrix.algebraMap_eq_diagonal, h]

/- English proof (translation)
Establish `hp : ∀ k : ℕ, N ^ k * Y = Y * M ^ k`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih => rw [pow_succ', mul_assoc, ih, ← mul_assoc, h, mul_assoc, ← pow_succ']`.

Proceed by induction on `q using Polynomial.induction_on' with`. Consider the case `add p q hp hq => simp [add_mul, mul_add, hp, hq]`. Consider the case `monomial k a => simp [aeval_monomial, ← Algebra.smul_def, hp]`.
-/
private theorem aeval_inter {n : ℕ} {K : Type} [CommRing K] (M N Y : Matrix (Fin n) (Fin n) K)
    (h : N * Y = Y * M) (q : K[X]) : aeval N q * Y = Y * aeval M q := by
  have hp : ∀ k : ℕ, N ^ k * Y = Y * M ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', mul_assoc, ih, ← mul_assoc, h, mul_assoc, ← pow_succ']
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp [add_mul, mul_add, hp, hq]
  | monomial k a => simp [aeval_monomial, ← Algebra.smul_def, hp]

/- English proof (translation)
Establish `h1` using `aeval_inter M (x • M) Y (by rw [← hY, ← Matrix.smul_mul]) M.charpoly`. Rewrite `h1` using `[Matrix.aeval_self_charpoly, mul_zero]`. Establish `hn : IsNilpotent (f.mapMatrix M - algebraMap K _ c)`. Use `⟨n, ?_⟩` and prove the remaining obligations. Use `aeval_mapM f M M.charpoly` as an intermediate fact.

Rewrite `this` using `[Matrix.aeval_self_charpoly, map_zero, hM]`. Simplify using `using this.symm`. Establish `hu : IsUnit (f.mapMatrix (x • M) - algebraMap K _ c)`. Establish `e : f.mapMatrix (x • M) - algebraMap K _ c = f x • (f.mapMatrix M - algebraMap K _ c) + algebraMap K _ ((f x - 1) * c)`. Use extensionality with `a b`.

Apply the tactic sequence `by_cases h : a = b <;> simp [Matrix.algebraMap_eq_diagonal, h]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Use `IsNilpotent.isUnit_add_right_of_commute (hn.smul _) ?_ (Algebra.commute_algebraMap_right _ _)` and prove the remaining obligations. Conclude with `(IsUnit.mk0 _ (mul_ne_zero (sub_ne_zero.2 hx) hc)).map _`.

Establish `hd : (aeval (x • M) M.charpoly).det ≠ 0`. Introduce `h0`. Establish `h2` using `RingHom.map_det f (aeval (x • M) M.charpoly)`. Rewrite `h2` using `[h0, map_zero, aeval_mapM, hM, map_pow, map_sub, aeval_X, aeval_C]`. Conclude with `((Matrix.isUnit_iff_isUnit_det _).1 (hu.pow n)).ne_zero h2.symm`.

Establish `h3 : (aeval (x • M) M.charpoly).det • Y = 0`. Use `congrArg (fun W => (aeval (x • M) M.charpoly).adjugate * W) h1` as an intermediate fact. Simplify `this` using `only [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_zero]`. Use extensionality with `i j`. Establish `h4` using `congrFun (congrFun h3 i) j`.

Simplify using `only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at h4`. Conclude with `(mul_eq_zero.1 h4).resolve_left hd`.
-/
private theorem key {n : ℕ} {A K : Type} [CommRing A] [IsDomain A] [Field K] (f : A →+* K)
    (M : Matrix (Fin n) (Fin n) A) (x : A) (c : K) (hc : c ≠ 0) (hx : f x ≠ 1)
    (hM : M.charpoly.map f = (X - C c) ^ n) (Y : Matrix (Fin n) (Fin n) A)
    (hY : x • (M * Y) = Y * M) : Y = 0 := by
  have h1 := aeval_inter M (x • M) Y (by rw [← hY, ← Matrix.smul_mul]) M.charpoly
  rw [Matrix.aeval_self_charpoly, mul_zero] at h1
  have hn : IsNilpotent (f.mapMatrix M - algebraMap K _ c) := by
    refine ⟨n, ?_⟩
    have := aeval_mapM f M M.charpoly
    rw [Matrix.aeval_self_charpoly, map_zero, hM] at this
    simpa using this.symm
  have hu : IsUnit (f.mapMatrix (x • M) - algebraMap K _ c) := by
    have e : f.mapMatrix (x • M) - algebraMap K _ c =
        f x • (f.mapMatrix M - algebraMap K _ c) + algebraMap K _ ((f x - 1) * c) := by
      ext a b
      by_cases h : a = b <;> simp [Matrix.algebraMap_eq_diagonal, h]
      ring
    rw [e]
    refine IsNilpotent.isUnit_add_right_of_commute (hn.smul _) ?_ (Algebra.commute_algebraMap_right _ _)
    exact (IsUnit.mk0 _ (mul_ne_zero (sub_ne_zero.2 hx) hc)).map _
  have hd : (aeval (x • M) M.charpoly).det ≠ 0 := by
    intro h0
    have h2 := RingHom.map_det f (aeval (x • M) M.charpoly)
    rw [h0, map_zero, aeval_mapM, hM, map_pow, map_sub, aeval_X, aeval_C] at h2
    exact ((Matrix.isUnit_iff_isUnit_det _).1 (hu.pow n)).ne_zero h2.symm
  have h3 : (aeval (x • M) M.charpoly).det • Y = 0 := by
    have := congrArg (fun W => (aeval (x • M) M.charpoly).adjugate * W) h1
    simpa only [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_zero] using this
  ext i j
  have h4 := congrFun (congrFun h3 i) j
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at h4
  exact (mul_eq_zero.1 h4).resolve_left hd

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `l _ n F O _ _ _ _ _ r ρ h hred Z hZ`. Take `⟨-, h2, g, hg, h3⟩` from `h`. Use extensionality with `i i'`. It suffices to establish `H : Z = 0 by rw [H]`. Use `key (res O O : O →+* ResidueField O) (mat ρ g) ((F.eps O O g : Oˣ) : O) (r.chib i g) (Units.ne_zero _) ?_ ?_ Z (hZ g hg)` and prove the remaining obligations.

Introduce `h4`. Apply `h3` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_one, ← h4]`. Conclude with `((res O O).commutes _).symm`.

Establish `h` using `congrArg (fun D => GDet.chi D (MonoidAlgebra.single g 1)) hred`. Simplify using `only [Resid.Dbar, chi_map_ofRep, chi_ofRep] at h`. Rewrite using `[h]`. Express the relevant statement in the definitionally equal form `(Matrix.diagonal _).charpoly = _`. Rewrite using `[Matrix.charpoly_diagonal]`.

Simplify using `only [fun k => h2 g hg k i]`. Rewrite using `[Finset.prod_const, Finset.card_univ, Fintype.card_fin]`.
-/
theorem UpperTheory.V.Th.Nm.n4 :
    ∀ {l : ℕ} [Fact l.Prime] {n : ℕ} (F : GFrame l) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [Algebra ℤ_[l] O] (r : Resid F O n) (ρ : F.G₀ →* GL (Fin n) O), r.V0ok → (GDet.ofRep (mat ρ)).map (res O O : O →+* ResidueField O) = r.Dbar → ∀ Z : Matrix (Fin n) (Fin n) O, (∀ g ∈ F.D0, ((F.eps O O g : Oˣ) : O) • (mat ρ g * Z) = Z * mat ρ g) → Z = 0 := by
  intro l _ n F O _ _ _ _ _ r ρ h hred Z hZ
  obtain ⟨-, h2, g, hg, h3⟩ := h
  ext i i'
  suffices H : Z = 0 by rw [H]
  refine key (res O O : O →+* ResidueField O) (mat ρ g) ((F.eps O O g : Oˣ) : O) (r.chib i g)
    (Units.ne_zero _) ?_ ?_ Z (hZ g hg)
  · intro h4
    apply h3
    apply Units.ext
    rw [Units.val_one, ← h4]
    exact ((res O O).commutes _).symm
  · have h := congrArg (fun D => GDet.chi D (MonoidAlgebra.single g 1)) hred
    simp only [Resid.Dbar, chi_map_ofRep, chi_ofRep] at h
    rw [h]
    change (Matrix.diagonal _).charpoly = _
    rw [Matrix.charpoly_diagonal]
    simp only [fun k => h2 g hg k i]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
