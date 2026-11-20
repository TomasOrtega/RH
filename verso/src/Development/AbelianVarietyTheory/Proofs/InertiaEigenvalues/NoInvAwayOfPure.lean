import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied

open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.PurityInvariants

/- English proof (translation)
Establish `hdet : (Matrix.scalar (Fin n) c - M.map f).det = 0`. Rewrite using `[← Matrix.exists_mulVec_eq_zero_iff]`. Use `⟨x, hx, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.sub_mulVec, h]`. Use extensionality with `j`.

Simplify using `[Matrix.scalar_apply]`. Establish `hroot : ((M.map f).charpoly).eval c = 0`. Rewrite using `[Matrix.eval_charpoly]`. Conclude with `hdet`. Unfold `Polynomial.IsRoot`.

Rewrite using `[← Polynomial.map_map, ← Matrix.charpoly_map, Polynomial.eval_map, Polynomial.eval₂_hom, hroot, map_zero]`.
-/
theorem isRoot_of_eigen {R K : Type} [CommRing R] [Field K] (f : R →+* K) (ι : K →+* ℂ) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (c : K) (x : Fin n → K) (hx : x ≠ 0)
    (h : (M.map f).mulVec x = c • x) : (M.charpoly.map (ι.comp f)).IsRoot (ι c) := by
  classical
  have hdet : (Matrix.scalar (Fin n) c - M.map f).det = 0 := by
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    refine ⟨x, hx, ?_⟩
    rw [Matrix.sub_mulVec, h]
    ext j
    simp [Matrix.scalar_apply]
  have hroot : ((M.map f).charpoly).eval c = 0 := by
    rw [Matrix.eval_charpoly]
    exact hdet
  unfold Polynomial.IsRoot
  rw [← Polynomial.map_map, ← Matrix.charpoly_map, Polynomial.eval_map, Polynomial.eval₂_hom,
    hroot, map_zero]

/- English proof (translation)
Establish `key : M.transpose * (c • M⁻¹.transpose) = c • (1 : Matrix (Fin n) (Fin n) R)`. Rewrite using `[Matrix.mul_smul, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hM, Matrix.transpose_one]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mulVec_mulVec, Matrix.map_mul]`. Use `_ = f c • x := by`.

Rewrite using `[key]`. Use extensionality with `j`. Simplify using `[Matrix.mulVec, dotProduct, Matrix.one_apply, apply_ite f, ite_mul, Finset.sum_ite_eq]`.
-/
theorem eigen_of_dual {R K : Type} [CommRing R] [Field K] (f : R →+* K) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (hM : IsUnit M.det) (c : R) (x : Fin n → K)
    (h : ((c • M⁻¹.transpose).map f).mulVec x = x) : (M.transpose.map f).mulVec x = f c • x := by
  have key : M.transpose * (c • M⁻¹.transpose) = c • (1 : Matrix (Fin n) (Fin n) R) := by
    rw [Matrix.mul_smul, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hM, Matrix.transpose_one]
  calc (M.transpose.map f).mulVec x
      = (M.transpose.map f).mulVec (((c • M⁻¹.transpose).map f).mulVec x) := by rw [h]
    _ = ((M.transpose * (c • M⁻¹.transpose)).map f).mulVec x := by
        rw [Matrix.mulVec_mulVec, Matrix.map_mul]
    _ = f c • x := by
        rw [key]
        ext j
        simp [Matrix.mulVec, dotProduct, Matrix.one_apply, apply_ite f, ite_mul, Finset.sum_ite_eq]

/- English proof (translation)
Establish `h1 : normV v = Ideal.absNorm v.asIdeal`. Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Both sides reduce to the same expression. Establish `hne1 : Ideal.absNorm v.asIdeal ≠ 1`. Rewrite using `[Ne, Ideal.absNorm_eq_one_iff]`.

Conclude with `v.isPrime.ne_top`. Establish `hne0 : Ideal.absNorm v.asIdeal ≠ 0`. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff]`. Conclude with `v.ne_bot`. Establish `: 1 < normV v` using `by omega`.

Conclude with `this` after adjusting the coercions.
-/
theorem one_lt_norm {E : Type} [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) :
    (1 : ℝ) < ((normV v : ℕ) : ℝ) := by
  have h1 : normV v = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  have hne1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact v.isPrime.ne_top
  have hne0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  have : 1 < normV v := by omega
  exact_mod_cast this

/- English proof (translation)
Introduce `D i s ι hP v hv hs`. Establish `hq : (1 : ℝ) < ((normV v : ℕ) : ℝ)` using `one_lt_norm v`. Establish `ht : (5 : ℝ) ≤ (D.R.t : ℝ)`. Use `D.R.rank_add_five_le` as an intermediate fact. Conclude with `(by omega : 5 ≤ D.R.t)` after adjusting the coercions.

Establish `hlt : ((normV v : ℕ) : ℝ) ^ ((1 - (D.R.t : ℝ)) / 2) < 1` using `Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith)`. Establish `hl : ((D.ntw.l i : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal`. Introduce `h`. Apply `hv` to reduce the goal to its premises. Unfold `placesOver`.

Conclude with `h`. Prove the components needed by the constructor for the conclusion. Introduce `A hA x hx`. Assume the negation of the conclusion as `hx0`. Take `⟨σ, hσ⟩` from `ReciprocityTheory.Gal.exists_isFrob (F := D.host.E) hA`.

Establish `hdec : σ ∈ Dec (F` using `D.host.E) A := by`. Unfold `Formalism.ConjugateSelfDual.IsFrob at hσ`. Conclude with `hσ.1`. Establish `e` using `hx σ hdec`. Establish `hr` using `isRoot_of_eigen (algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i))) ι (Tmat i s σ) 1 x hx0 (by rw [one_smul]; exact e)`.

Establish `hn` using `hP v hv hs A hA σ hσ _ hr`. Rewrite `hn` using `[map_one, norm_one]`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `A hA x hx`. Assume the negation of the conclusion as `hx0`.

Take `⟨σ, hσ⟩` from `ReciprocityTheory.Gal.exists_isFrob (F := D.host.E) hA`. Establish `hdec : σ ∈ Dec (F` using `D.host.E) A := by`. Unfold `Formalism.ConjugateSelfDual.IsFrob at hσ`. Conclude with `hσ.1`. Establish `e` using `hx σ hdec`.

Establish `hu : IsUnit (Tmat i s σ).det`. Unfold `Tmat`. Rewrite using `[Matrix.det_smul]`. Conclude with `((Units.isUnit _).pow _).mul ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _))`. Establish `e2` using `eigen_of_dual (algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i))) (Tmat i s σ) hu ((eps0 D.ntw i σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) x (by unfold Tdual at e; exact e)`.

Establish `hr` using `isRoot_of_eigen (algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i))) ι (Tmat i s σ).transpose _ x hx0 e2`. Rewrite `hr` using `[Matrix.charpoly_transpose]`. Establish `hn` using `hP v hv hs A hA σ hσ _ hr`. Establish `hc : ((eps0 D.ntw i σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) = (normV v : ℕ)`. Unfold `eps0`.

Rewrite using `[MonoidHom.comp_apply, Units.coe_map]`. Conclude with `(congrArg (algebraMap _ (D.ntw.O0 i)) (ReciprocityTheory.Gal.cycZ_of_isFrob hl hA hσ)).trans (map_natCast _ _)`. Rewrite `hn` using `[hc, map_natCast, map_natCast, Complex.norm_natCast]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem noInv_of_pure : ∀ (D : D7) (i : D.ntw.Tw) (s : D.ntw.Sig i) (ι : FractionRing (D.ntw.O0 i) →+* ℂ), Pure i s ι → ∀ v, v ∉ placesOver D.host.E (D.ntw.l i) → v ∉ Spl (X := D.ntw) i → NoInv i (Tmat i s) v ∧ NoInv i (Tdual i s) v := by
  intro D i s ι hP v hv hs
  have hq : (1 : ℝ) < ((normV v : ℕ) : ℝ) := one_lt_norm v
  have ht : (5 : ℝ) ≤ (D.R.t : ℝ) := by
    have := D.R.rank_add_five_le
    exact_mod_cast (by omega : 5 ≤ D.R.t)
  have hlt : ((normV v : ℕ) : ℝ) ^ ((1 - (D.R.t : ℝ)) / 2) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith)
  have hl : ((D.ntw.l i : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal := by
    intro h
    apply hv
    unfold placesOver
    exact h
  constructor
  · intro A hA x hx
    by_contra hx0
    obtain ⟨σ, hσ⟩ := ReciprocityTheory.Gal.exists_isFrob (F := D.host.E) hA
    have hdec : σ ∈ Dec (F := D.host.E) A := by
      unfold Formalism.ConjugateSelfDual.IsFrob at hσ
      exact hσ.1
    have e := hx σ hdec
    have hr := isRoot_of_eigen (algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i))) ι (Tmat i s σ) 1 x hx0
      (by rw [one_smul]; exact e)
    have hn := hP v hv hs A hA σ hσ _ hr
    rw [map_one, norm_one] at hn
    linarith
  · intro A hA x hx
    by_contra hx0
    obtain ⟨σ, hσ⟩ := ReciprocityTheory.Gal.exists_isFrob (F := D.host.E) hA
    have hdec : σ ∈ Dec (F := D.host.E) A := by
      unfold Formalism.ConjugateSelfDual.IsFrob at hσ
      exact hσ.1
    have e := hx σ hdec
    have hu : IsUnit (Tmat i s σ).det := by
      unfold Tmat
      rw [Matrix.det_smul]
      exact ((Units.isUnit _).pow _).mul ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _))
    have e2 := eigen_of_dual (algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i))) (Tmat i s σ) hu
      ((eps0 D.ntw i σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) x (by unfold Tdual at e; exact e)
    have hr := isRoot_of_eigen (algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i))) ι (Tmat i s σ).transpose _ x hx0 e2
    rw [Matrix.charpoly_transpose] at hr
    have hn := hP v hv hs A hA σ hσ _ hr
    have hc : ((eps0 D.ntw i σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) = (normV v : ℕ) := by
      unfold eps0
      rw [MonoidHom.comp_apply, Units.coe_map]
      exact (congrArg (algebraMap _ (D.ntw.O0 i)) (ReciprocityTheory.Gal.cycZ_of_isFrob hl hA hσ)).trans (map_natCast _ _)
    rw [hc, map_natCast, map_natCast, Complex.norm_natCast] at hn
    linarith

end GlobalTheory.PurityInvariants
