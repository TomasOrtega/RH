import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProdRecSatakeLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DefiniteUnitaryAutFormEqZeroOfFinitePoints
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open Matrix Pointwise

namespace GlobalTheory.WeightRealExt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

/- English proof (translation)
Introduce `g`. Take `⟨k, hk, x, hx, rfl⟩` from `GlobalTheory.DefU.exists_finU_mul_infU E n g`. Rewrite using `[GlobalTheory.DefU.fin_mul_inf hk hx]`. Establish `hc : Continuous (· * k : UA E n → UA E n)` using `continuous_mul_const k`. Use `closure_mono ?_ (image_closure_subset_closure_image hc ⟨x, GlobalTheory.DefiniteDense.mem_closure_rat_fin x hx, rfl⟩)` and prove the remaining obligations.

Introduce and unpack `_ ⟨_, ⟨γ, hγ, k', hk', rfl⟩, rfl⟩`. Conclude with `⟨γ, hγ, k' * k, (finU E n).mul_mem hk' hk, (mul_assoc _ _ _).symm⟩`.
-/
theorem dense_rat_fin : Dense ((ratU E n : Set (UA E n)) * (finU E n : Set (UA E n))) := by
  intro g
  obtain ⟨k, hk, x, hx, rfl⟩ := GlobalTheory.DefU.exists_finU_mul_infU E n g
  rw [GlobalTheory.DefU.fin_mul_inf hk hx]
  have hc : Continuous (· * k : UA E n → UA E n) := continuous_mul_const k
  refine closure_mono ?_
    (image_closure_subset_closure_image hc ⟨x, GlobalTheory.DefiniteDense.mem_closure_rat_fin x hx, rfl⟩)
  rintro _ ⟨_, ⟨γ, hγ, k', hk', rfl⟩, rfl⟩
  exact ⟨γ, hγ, k' * k, (finU E n).mul_mem hk' hk, (mul_assoc _ _ _).symm⟩

/- English proof (translation)
Establish `h0 : Formalism.UG.cT (conjAd E) (γ.1 : Matrix (Fin n) (Fin n) (Ad E)) * 1 * γ.1 = 1` using `γ.2`. Rewrite `h0` using `[mul_one, h]`. Establish `e : Formalism.UG.cT (conjAd E) ((γ₀ : Matrix (Fin n) (Fin n) E).map (algebraMap E (Ad E))) = (conjT (IsCMField.complexConj E : E →+* E) (γ₀ : Matrix (Fin n) (Fin n) E)).map (algebraMap E (Ad E))`. Use extensionality with `i j`. Simplify using `[Formalism.UG.cT, conjT, conjAd_algebraMap]`.

Express the relevant statement in the definitionally equal form `Formalism.UG.cT (conjAd E) ((γ₀ : Matrix (Fin n) (Fin n) E).map (algebraMap E (Ad E))) * (γ₀ : Matrix (Fin n) (Fin n) E).map (algebraMap E (Ad E)) = 1 at h0`. Rewrite `h0` using `[e, ← Matrix.map_mul, ← Matrix.map_one (algebraMap E (Ad E)) (map_zero _) (map_one _)]`. Establish `h1` using `Matrix.map_injective (NumberField.AdeleRing.algebraMap_injective (𝓞 E) E) h0`. Conclude with `mul_eq_one_comm.1 h1`.
-/
theorem mem_rationalGL_of_unitaryGroupGram_unitGram (γ : UA E n) (γ₀ : GL (Fin n) E) (h : γ.1 = ratGL E n γ₀) : γ₀ ∈ GQ0 E n := by
  have h0 : Formalism.UG.cT (conjAd E) (γ.1 : Matrix (Fin n) (Fin n) (Ad E)) * 1 * γ.1 = 1 := γ.2
  rw [mul_one, h] at h0
  have e : Formalism.UG.cT (conjAd E) ((γ₀ : Matrix (Fin n) (Fin n) E).map (algebraMap E (Ad E))) =
      (conjT (IsCMField.complexConj E : E →+* E) (γ₀ : Matrix (Fin n) (Fin n) E)).map (algebraMap E (Ad E)) := by
    ext i j
    simp [Formalism.UG.cT, conjT, conjAd_algebraMap]
  change Formalism.UG.cT (conjAd E) ((γ₀ : Matrix (Fin n) (Fin n) E).map (algebraMap E (Ad E))) *
      (γ₀ : Matrix (Fin n) (Fin n) E).map (algebraMap E (Ad E)) = 1 at h0
  rw [e, ← Matrix.map_mul, ← Matrix.map_one (algebraMap E (Ad E)) (map_zero _) (map_one _)] at h0
  have h1 := Matrix.map_injective (NumberField.AdeleRing.algebraMap_injective (𝓞 E) E) h0
  exact mul_eq_one_comm.1 h1

def ratPt : GQ0 E n →* GQ E n where
  toFun γ := ⟨⟨GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : E →+* AL E) γ.1, by
      have h0 : (γ.1 : Matrix (Fin n) (Fin n) E) * conjT (IsCMField.complexConj E : E →+* E) γ.1 = 1 := γ.2
      have e : conjT (conjAL E) ((γ.1 : Matrix (Fin n) (Fin n) E).map
          (Algebra.TensorProduct.includeLeftRingHom : E →+* AL E)) =
          (conjT (IsCMField.complexConj E : E →+* E) (γ.1 : Matrix (Fin n) (Fin n) E)).map
            (Algebra.TensorProduct.includeLeftRingHom : E →+* AL E) := by
        ext i j
        simp [conjT, conjAL]
      change (γ.1 : Matrix (Fin n) (Fin n) E).map (Algebra.TensorProduct.includeLeftRingHom : E →+* AL E) *
        conjT (conjAL E) ((γ.1 : Matrix (Fin n) (Fin n) E).map
          (Algebra.TensorProduct.includeLeftRingHom : E →+* AL E)) = 1
      rw [e, ← Matrix.map_mul, h0, Matrix.map_one _ (map_zero _) (map_one _)]⟩,
    Subgroup.mem_subgroupOf.2 ⟨γ.1, γ.2, rfl⟩⟩
  map_one' := Subtype.ext (Subtype.ext (map_one _))
  map_mul' x y := Subtype.ext (Subtype.ext (map_mul _ _ _))

def polyMat {ι : Type} (P : ι → ι → MvPolynomial ((E →+* ℂ) × Fin n × Fin n) ℂ) (g : UA E n) : Matrix ι ι ℂ :=
  fun i j => MvPolynomial.eval (fun p => coord p.1 ((cInf g : Matrix (Fin n) (Fin n) (Cinf E)) p.2.1 p.2.2)) (P i j)

/- English proof (translation)
Unfold `polyMat`. Rewrite using `[e]`.
-/
theorem polyMat_congr {ι : Type} (P : ι → ι → MvPolynomial ((E →+* ℂ) × Fin n × Fin n) ℂ) {g h : UA E n}
    (e : cInf g = cInf h) : polyMat P g = polyMat P h := by
  unfold polyMat
  rw [e]

/- English proof (translation)
Use function extensionality and compare the values at `i j`. Unfold `polyMat`. Use `congr 2`. Use function extensionality and compare the values at `p`. Rewrite using `[← coord_algebraMap p.1]`.

Use `congr 1`. Express the relevant statement in the definitionally equal form `pInf E ((γ.1 : Matrix (Fin n) (Fin n) (Ad E)) p.2.1 p.2.2) = _`. Rewrite using `[h]`. Both sides reduce to the same expression.
-/
theorem polyMat_rat {ι : Type} (P : ι → ι → MvPolynomial ((E →+* ℂ) × Fin n × Fin n) ℂ) (γ : UA E n)
    (γ₀ : GL (Fin n) E) (h : γ.1 = ratGL E n γ₀) :
    polyMat P γ = fun i j =>
      MvPolynomial.eval (fun p => p.1 ((γ₀ : Matrix (Fin n) (Fin n) E) p.2.1 p.2.2)) (P i j) := by
  funext i j
  unfold polyMat
  congr 2
  funext p
  rw [← coord_algebraMap p.1]
  congr 1
  change pInf E ((γ.1 : Matrix (Fin n) (Fin n) (Ad E)) p.2.1 p.2.2) = _
  rw [h]
  rfl

omit [NumberField E] [IsCMField E] in

/- English proof (translation)
Unfold `coord`. Use `split_ifs`. Conclude with `continuous_apply _`. Conclude with `Complex.continuous_conj.comp (continuous_apply _)`.
-/
theorem continuous_coord' (τ : E →+* ℂ) : Continuous (coord τ) := by
  unfold coord
  split_ifs
  · exact continuous_apply _
  · exact Complex.continuous_conj.comp (continuous_apply _)

/- English proof (translation)
The claim follows from `continuous_pi fun w => ((InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp (continuous_apply w)).comp continuous_fst`.
-/
theorem continuous_pInf' : Continuous (pInf E) :=
  continuous_pi fun w =>
    ((InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)).comp continuous_fst

/- English proof (translation)
Use `continuous_pi fun i => continuous_pi fun j => ?_` and prove the remaining obligations. Use `(MvPolynomial.continuous_eval (P i j)).comp (continuous_pi fun p => ?_)` and prove the remaining obligations. Use `(continuous_coord' p.1).comp (continuous_pInf'.comp (f := fun g : UA E n => (g.1 : Matrix (Fin n) (Fin n) (Ad E)) p.2.1 p.2.2) ?_)` and prove the remaining obligations. Conclude with `(Units.continuous_val.comp continuous_subtype_val).matrix_elem _ _`.
-/
theorem continuous_polyMat {ι : Type} (P : ι → ι → MvPolynomial ((E →+* ℂ) × Fin n × Fin n) ℂ) :
    Continuous (polyMat P) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  refine (MvPolynomial.continuous_eval (P i j)).comp (continuous_pi fun p => ?_)
  refine (continuous_coord' p.1).comp (continuous_pInf'.comp
    (f := fun g : UA E n => (g.1 : Matrix (Fin n) (Fin n) (Ad E)) p.2.1 p.2.2) ?_)
  exact (Units.continuous_val.comp continuous_subtype_val).matrix_elem _ _

/- English proof (translation)
Take `⟨γ₀, hγ₀⟩` from `Subgroup.mem_subgroupOf.1 hγ`. Conclude with `⟨⟨γ₀, mem_rationalGL_of_unitaryGroupGram_unitGram γ γ₀ hγ₀.symm⟩, hγ₀.symm⟩`.
-/
theorem exists_unitaryRationalMatrix_of_mem_definiteUnitaryRational {γ : UA E n} (hγ : γ ∈ ratU E n) : ∃ γ₀ : GQ0 E n, γ.1 = ratGL E n γ₀.1 := by
  obtain ⟨γ₀, hγ₀⟩ := Subgroup.mem_subgroupOf.1 hγ
  exact ⟨⟨γ₀, mem_rationalGL_of_unitaryGroupGram_unitGram γ γ₀ hγ₀.symm⟩, hγ₀.symm⟩

/- English proof (translation)
Establish `hcl : IsClosed {z : G × G | f (z.1 * z.2) = f z.1 * f z.2}` using `isClosed_eq (hf.comp (continuous_fst.mul continuous_snd)) ((hf.comp continuous_fst).mul (hf.comp continuous_snd))`. Conclude with `hcl.closure_subset_iff.2 (fun z hz => h z.1 hz.1 z.2 hz.2) ((hD.prod hD) (x, y))`.
-/
theorem mul_of_dense {G M : Type} [Mul G] [TopologicalSpace G] [ContinuousMul G] [Mul M] [TopologicalSpace M]
    [ContinuousMul M] [T2Space M] {D : Set G} (hD : Dense D) (f : G → M) (hf : Continuous f)
    (h : ∀ x ∈ D, ∀ y ∈ D, f (x * y) = f x * f y) (x y : G) : f (x * y) = f x * f y := by
  have hcl : IsClosed {z : G × G | f (z.1 * z.2) = f z.1 * f z.2} :=
    isClosed_eq (hf.comp (continuous_fst.mul continuous_snd))
      ((hf.comp continuous_fst).mul (hf.comp continuous_snd))
  exact hcl.closure_subset_iff.2 (fun z hz => h z.1 hz.1 z.2 hz.2) ((hD.prod hD) (x, y))

/- English proof (translation)
Use `mul_of_dense dense_rat_fin f hf fun x hx y hy => ?_` and prove the remaining obligations. Take `⟨γ, hγ, k, hk, hx⟩` from `Set.mem_mul.1 hx`. Take `⟨δ, hδ, l, hl, hy⟩` from `Set.mem_mul.1 hy`. Establish `hk' : cInf k = 1` using `hk`. Establish `hl' : cInf l = 1` using `hl`.

Establish `e1 : cInf x = cInf γ` using `by rw [← hx, map_mul, hk', mul_one]`. Establish `e2 : cInf y = cInf δ` using `by rw [← hy, map_mul, hl', mul_one]`. Rewrite using `[hi x γ e1, hi y δ e2, hi (x * y) (γ * δ) (by rw [map_mul, map_mul, e1, e2]), h γ hγ δ hδ]`.
-/
theorem mul_of_rat {M : Type} [Mul M] [TopologicalSpace M] [ContinuousMul M] [T2Space M] (f : UA E n → M)
    (hf : Continuous f) (hi : ∀ g h, cInf g = cInf h → f g = f h)
    (h : ∀ x ∈ ratU E n, ∀ y ∈ ratU E n, f (x * y) = f x * f y) : ∀ x y, f (x * y) = f x * f y := by
  refine mul_of_dense dense_rat_fin f hf fun x hx y hy => ?_
  obtain ⟨γ, hγ, k, hk, hx⟩ := Set.mem_mul.1 hx
  obtain ⟨δ, hδ, l, hl, hy⟩ := Set.mem_mul.1 hy
  have hk' : cInf k = 1 := hk
  have hl' : cInf l = 1 := hl
  have e1 : cInf x = cInf γ := by rw [← hx, map_mul, hk', mul_one]
  have e2 : cInf y = cInf δ := by rw [← hy, map_mul, hl', mul_one]
  rw [hi x γ e1, hi y δ e2, hi (x * y) (γ * δ) (by rw [map_mul, map_mul, e1, e2]), h γ hγ δ hδ]

/- English proof (translation)
Introduce `L _ _ _ n a`. Take `⟨_, ι, _, _, b, P, hP⟩` from `a.alg`. Establish `hrat : ∀ (γ : UA L n) (γQ : GQ L n) (γ₀ : GL (Fin n) L), γ.1 = ratGL L n γ₀ → (((γQ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = (γ₀ : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom → polyMat P γ = LinearMap.toMatrix b b (a.ρ γQ)` using `fun γ γQ γ₀ h1 h2 => (polyMat_rat P γ γ₀ h1).trans (hP γQ γ₀ h2).symm`. Establish `hrat' : ∀ (γ : UA L n) (γ₀ : GQ0 L n), γ.1 = ratGL L n γ₀.1 → polyMat P γ = LinearMap.toMatrix b b (a.ρ (ratPt γ₀))` using `fun γ γ₀ h => hrat γ _ γ₀.1 h rfl`. Establish `hone : polyMat P 1 = 1`.

Rewrite using `[hrat' 1 1 (map_one (ratGL L n)).symm, map_one, map_one, LinearMap.toMatrix_one]`. Establish `hmul : ∀ g h : UA L n, polyMat P (g * h) = polyMat P g * polyMat P h`. Use `mul_of_rat (polyMat P) (continuous_polyMat P) (fun _ _ => polyMat_congr P) fun γ hγ δ hδ => ?_` and prove the remaining obligations. Take `⟨γ₀, hγ₀⟩` from `exists_unitaryRationalMatrix_of_mem_definiteUnitaryRational hγ`. Take `⟨δ₀, hδ₀⟩` from `exists_unitaryRationalMatrix_of_mem_definiteUnitaryRational hδ`.

Establish `e : (γ * δ).1 = ratGL L n (γ₀ * δ₀).1`. Rewrite using `[Subgroup.coe_mul, Subgroup.coe_mul, map_mul, hγ₀, hδ₀]`. Rewrite using `[hrat' γ γ₀ hγ₀, hrat' δ δ₀ hδ₀, hrat' (γ * δ) (γ₀ * δ₀) e, map_mul, map_mul, LinearMap.toMatrix_mul]`. Use `⟨⟨⟨fun g => Matrix.toLin b b (polyMat P g), ?_⟩, fun g h => ?_⟩, fun k hk => ?_, fun γ γQ γ₀ h1 h2 => ?_, fun v μ => ?_⟩` and prove the remaining obligations. Rewrite using `[hone, Matrix.toLin_one]`.

Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `Matrix.toLin b b (polyMat P (g * h)) = _`. Rewrite using `[hmul, Matrix.toLin_mul b b b]`. Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `Matrix.toLin b b (polyMat P k) = 1`.

Rewrite using `[polyMat_congr P (g := k) (h := 1) ((show cInf k = 1 from hk).trans (map_one _).symm), hone, Matrix.toLin_one]`. Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `Matrix.toLin b b (polyMat P γ) = _`. Rewrite using `[hrat γ γQ γ₀ h1 h2, Matrix.toLin_toMatrix]`. Express the relevant statement in the definitionally equal form `Continuous fun g : UA L n => μ (Matrix.toLin b b (polyMat P g) v)`.

Establish `hc` using `continuous_polyMat P`. Simplify using `only [Matrix.toLin_apply, map_sum, map_smul, smul_eq_mul]`. Use `continuous_finset_sum _ fun j _ => Continuous.mul ?_ continuous_const` and prove the remaining obligations. Conclude with `(continuous_apply j).comp (hc.matrix_mulVec continuous_const)`.
-/
theorem exists_extension : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n), ∃ R : UA L n →* Module.End ℂ a.W, (∀ k ∈ finU L n, R k = 1) ∧ (∀ (γ : UA L n) (γQ : GQ L n) (γ₀ : GL (Fin n) L), γ.1 = ratGL L n γ₀ → (((γQ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = (γ₀ : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom → R γ = a.ρ γQ) ∧ ∀ (v : a.W) (μ : Module.Dual ℂ a.W), Continuous fun g : UA L n => μ (R g v) := by
  intro L _ _ _ n a
  obtain ⟨_, ι, _, _, b, P, hP⟩ := a.alg
  have hrat : ∀ (γ : UA L n) (γQ : GQ L n) (γ₀ : GL (Fin n) L), γ.1 = ratGL L n γ₀ →
      (((γQ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
        (γ₀ : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom →
      polyMat P γ = LinearMap.toMatrix b b (a.ρ γQ) := fun γ γQ γ₀ h1 h2 =>
    (polyMat_rat P γ γ₀ h1).trans (hP γQ γ₀ h2).symm
  have hrat' : ∀ (γ : UA L n) (γ₀ : GQ0 L n), γ.1 = ratGL L n γ₀.1 →
      polyMat P γ = LinearMap.toMatrix b b (a.ρ (ratPt γ₀)) := fun γ γ₀ h => hrat γ _ γ₀.1 h rfl
  have hone : polyMat P 1 = 1 := by
    rw [hrat' 1 1 (map_one (ratGL L n)).symm, map_one, map_one, LinearMap.toMatrix_one]
  have hmul : ∀ g h : UA L n, polyMat P (g * h) = polyMat P g * polyMat P h := by
    refine mul_of_rat (polyMat P) (continuous_polyMat P) (fun _ _ => polyMat_congr P) fun γ hγ δ hδ => ?_
    obtain ⟨γ₀, hγ₀⟩ := exists_unitaryRationalMatrix_of_mem_definiteUnitaryRational hγ
    obtain ⟨δ₀, hδ₀⟩ := exists_unitaryRationalMatrix_of_mem_definiteUnitaryRational hδ
    have e : (γ * δ).1 = ratGL L n (γ₀ * δ₀).1 := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, hγ₀, hδ₀]
    rw [hrat' γ γ₀ hγ₀, hrat' δ δ₀ hδ₀, hrat' (γ * δ) (γ₀ * δ₀) e, map_mul, map_mul, LinearMap.toMatrix_mul]
  refine ⟨⟨⟨fun g => Matrix.toLin b b (polyMat P g), ?_⟩, fun g h => ?_⟩, fun k hk => ?_, fun γ γQ γ₀ h1 h2 => ?_,
    fun v μ => ?_⟩
  · rw [hone, Matrix.toLin_one]
    rfl
  · change Matrix.toLin b b (polyMat P (g * h)) = _
    rw [hmul, Matrix.toLin_mul b b b]
    rfl
  · change Matrix.toLin b b (polyMat P k) = 1
    rw [polyMat_congr P (g := k) (h := 1) ((show cInf k = 1 from hk).trans (map_one _).symm), hone, Matrix.toLin_one]
    rfl
  · change Matrix.toLin b b (polyMat P γ) = _
    rw [hrat γ γQ γ₀ h1 h2, Matrix.toLin_toMatrix]
  · change Continuous fun g : UA L n => μ (Matrix.toLin b b (polyMat P g) v)
    have hc := continuous_polyMat P
    simp only [Matrix.toLin_apply, map_sum, map_smul, smul_eq_mul]
    refine continuous_finset_sum _ fun j _ => Continuous.mul ?_ continuous_const
    exact (continuous_apply j).comp (hc.matrix_mulVec continuous_const)

end GlobalTheory.WeightRealExt

end
