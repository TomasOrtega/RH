import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacFn
import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.SplitGLLift

open GlobalTheory.AdelicU.Supp (singleTens compFin_singleTens_self compFin_singleTens_ne compInf_singleTens singleTens_mul
  sigR_singleTens adTens_ext compFin_one_tmul)

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {v : HeightOneSpectrum (𝓞 F)}

def liftPair (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) : Fv F v × Fv F v →ₙ+* AF F ⊗[F] E :=
  (singleTens E v).comp ((splitAlgEquiv h τ).symm : Fv F v × Fv F v →ₙ+* Fv F v ⊗[F] E)

/- English proof (translation)
The claim follows from `compInf_singleTens w v _`.
-/
theorem compInf_liftPair (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (w : InfinitePlace F) (p : Fv F v × Fv F v) :
    compInf F E w (liftPair h τ p) = 0 := compInf_singleTens w v _

/- English proof (translation)
The claim follows from `compFin_singleTens_ne hu _`.
-/
theorem compFin_liftPair_ne (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) {u : HeightOneSpectrum (𝓞 F)} (hu : u ≠ v)
    (p : Fv F v × Fv F v) : compFin F E u (liftPair h τ p) = 0 := compFin_singleTens_ne hu _

/- English proof (translation)
Use `show splitProj τ (compFin F E v (singleTens E v _)) = p.1`. Rewrite using `[compFin_singleTens_self]`. Conclude with `splitProj_symm h τ p`.
-/
theorem piW_liftPair (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (p : Fv F v × Fv F v) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ (liftPair h τ p) = p.1 := by
  show splitProj τ (compFin F E v (singleTens E v _)) = p.1
  rw [compFin_singleTens_self]
  exact splitProj_symm h τ p

/- English proof (translation)
Use `show splitProj (τ.comp σ) (compFin F E v (singleTens E v _)) = p.2`. Rewrite using `[compFin_singleTens_self]`. Conclude with `splitProj_comp_symm h τ p`.
-/
theorem piW_comp_liftPair (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (p : Fv F v × Fv F v) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (τ.comp σ) (liftPair h τ p) = p.2 := by
  show splitProj (τ.comp σ) (compFin F E v (singleTens E v _)) = p.2
  rw [compFin_singleTens_self]
  exact splitProj_comp_symm h τ p

/- English proof (translation)
Use `show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ (singleTens E v _) = singleTens E v _`. Rewrite using `[sigR_singleTens]`. Use `congr 1`. Apply `(splitAlgEquiv h τ).injective` to reduce the goal to its premises. Rewrite using `[splitAlgEquiv_sigR]`.

Express the relevant statement in the definitionally equal form `((splitAlgEquiv h τ) ((splitAlgEquiv h τ).symm p)).swap = (splitAlgEquiv h τ) ((splitAlgEquiv h τ).symm p.swap)`. Simplify using the standard rewrite rules.
-/
theorem cA_liftPair (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (p : Fv F v × Fv F v) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ (liftPair h τ p) = liftPair h τ p.swap := by
  show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ (singleTens E v _) = singleTens E v _
  rw [sigR_singleTens]
  congr 1
  apply (splitAlgEquiv h τ).injective
  rw [splitAlgEquiv_sigR]
  change ((splitAlgEquiv h τ) ((splitAlgEquiv h τ).symm p)).swap =
    (splitAlgEquiv h τ) ((splitAlgEquiv h τ).symm p.swap)
  simp

/- English proof (translation)
Introduce `u hu`. Rewrite using `[Algebra.smul_def, mul_comm]`. Express the relevant statement in the definitionally equal form `singleTens E v _ * _ = 0`. Rewrite using `[singleTens_mul]`. Establish `: compFin F E v (algebraMap (AF F) (AF F ⊗[F] E) u) = 0`.

Express the relevant statement in the definitionally equal form `(evFin F v u) ⊗ₜ[F] (1 : E) = 0`. Rewrite using `[hu, TensorProduct.zero_tmul]`. Rewrite using `[this, mul_zero, map_zero]`.
-/
theorem at_liftPair (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (p : Fv F v × Fv F v) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) (liftPair h τ p) := by
  intro u hu
  rw [Algebra.smul_def, mul_comm]
  change singleTens E v _ * _ = 0
  rw [singleTens_mul]
  have : compFin F E v (algebraMap (AF F) (AF F ⊗[F] E) u) = 0 := by
    change (evFin F v u) ⊗ₜ[F] (1 : E) = 0
    rw [hu, TensorProduct.zero_tmul]
  rw [this, mul_zero, map_zero]

end General

section Mat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {v : HeightOneSpectrum (𝓞 F)} {n : Type} [Fintype n] [DecidableEq n]

def liftMat (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) :
    Matrix n n (Fv F v) × Matrix n n (Fv F v) →ₙ+* Matrix n n (AF F ⊗[F] E) where
  toFun p := Matrix.of fun i j => liftPair h τ (p.1 i j, p.2 i j)
  map_zero' := by
    ext i j
    simp only [Prod.fst_zero, Prod.snd_zero, Matrix.zero_apply, Matrix.of_apply]
    exact (liftPair h τ).map_zero
  map_add' p q := by
    ext i j
    simp only [Prod.fst_add, Prod.snd_add, Matrix.add_apply, Matrix.of_apply, ← map_add, Prod.mk_add_mk]
  map_mul' p q := by
    ext i j
    simp only [Prod.fst_mul, Prod.snd_mul, Matrix.mul_apply, Matrix.of_apply]
    rw [show ((∑ k, p.1 i k * q.1 k j), (∑ k, p.2 i k * q.2 k j)) =
        ∑ k, ((p.1 i k, p.2 i k) * (q.1 k j, q.2 k j)) by
      ext <;> simp [Prod.fst_sum, Prod.snd_sum]]
    rw [map_sum]
    simp only [map_mul]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem liftMat_apply (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (p : Matrix n n (Fv F v) × Matrix n n (Fv F v))
    (i j : n) : liftMat h τ p i j = liftPair h τ (p.1 i j, p.2 i j) := rfl

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.map_apply, Matrix.add_apply, map_add, liftMat_apply, hf, add_zero]`. Apply the tactic sequence `by_cases e : i = j <;> simp [Matrix.one_apply, e]`.
-/
theorem map_one_add_of_zero {R : Type} [CommRing R] (f : AF F ⊗[F] E →+* R) (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v)
    (hf : ∀ q, f (liftPair h τ q) = 0) (p : Matrix n n (Fv F v) × Matrix n n (Fv F v)) :
    (1 + liftMat h τ p).map f = 1 := by
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, map_add, liftMat_apply, hf, add_zero]
  by_cases e : i = j <;> simp [Matrix.one_apply, e]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.map_apply, Matrix.add_apply, map_add, liftMat_apply, piW_liftPair]`. Apply the tactic sequence `by_cases e : i = j <;> simp [Matrix.one_apply, e]`.
-/
theorem map_one_add_piW (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (p : Matrix n n (Fv F v) × Matrix n n (Fv F v)) :
    (1 + liftMat h τ p).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ) = 1 + p.1 := by
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, map_add, liftMat_apply, piW_liftPair]
  by_cases e : i = j <;> simp [Matrix.one_apply, e]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.map_apply, Matrix.add_apply, map_add, liftMat_apply, piW_comp_liftPair]`. Apply the tactic sequence `by_cases e : i = j <;> simp [Matrix.one_apply, e]`.
-/
theorem map_one_add_piW_comp (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v)
    (p : Matrix n n (Fv F v) × Matrix n n (Fv F v)) :
    (1 + liftMat h τ p).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (τ.comp σ)) = 1 + p.2 := by
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, map_add, liftMat_apply, piW_comp_liftPair]
  by_cases e : i = j <;> simp [Matrix.one_apply, e]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.map_apply, Matrix.add_apply, map_add, liftMat_apply, cA_liftPair, Prod.swap_prod_mk, Prod.fst_swap, Prod.snd_swap]`. Apply the tactic sequence `by_cases e : i = j <;> simp [Matrix.one_apply, e]`.
-/
theorem map_one_add_cA (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (p : Matrix n n (Fv F v) × Matrix n n (Fv F v)) :
    (1 + liftMat h τ p).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) = 1 + liftMat h τ p.swap := by
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, map_add, liftMat_apply, cA_liftPair, Prod.swap_prod_mk, Prod.fst_swap,
    Prod.snd_swap]
  by_cases e : i = j <;> simp [Matrix.one_apply, e]

/- English proof (translation)
Introduce `u hu`. Use extensionality with `i j`. Rewrite using `[Matrix.smul_apply, liftMat_apply]`. Conclude with `at_liftPair h τ _ u hu`.
-/
theorem at_liftMat (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (p : Matrix n n (Fv F v) × Matrix n n (Fv F v)) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) (liftMat h τ p) := by
  intro u hu
  ext i j
  rw [Matrix.smul_apply, liftMat_apply]
  exact at_liftPair h τ _ u hu

/- English proof (translation)
Use `show splitProj τ (compFin F E v ((1 : AF F) ⊗ₜ[F] x)) = τ x`. Rewrite using `[compFin_one_tmul, splitProj_tmul, one_mul]`.
-/
theorem piW_inclR (τ : E →ₐ[F] Fv F v) (x : E) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) x) = τ x := by
  show splitProj τ (compFin F E v ((1 : AF F) ⊗ₜ[F] x)) = τ x
  rw [compFin_one_tmul, splitProj_tmul, one_mul]

/- English proof (translation)
Use extensionality with `i j`. Use `adTens_ext (fun w => congrFun (congrFun (hinf w) i) j) fun u => ?_` and prove the remaining obligations. Distinguish the cases in `e : u = v`. Substitute `e` using the available equality. Conclude with `split_ext h τ (congrFun (congrFun h1 i) j) (congrFun (congrFun h2 i) j)`.

Conclude with `congrFun (congrFun (hfin u e) i) j`.
-/
theorem mat_ext (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) {M M' : Matrix n n (AF F ⊗[F] E)}
    (hinf : ∀ w, M.map (compInf F E w) = M'.map (compInf F E w))
    (hfin : ∀ u, u ≠ v → M.map (compFin F E u) = M'.map (compFin F E u))
    (h1 : M.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ) = M'.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ))
    (h2 : M.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (τ.comp σ)) = M'.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (τ.comp σ))) : M = M' := by
  ext i j
  refine adTens_ext (fun w => congrFun (congrFun (hinf w) i) j) fun u => ?_
  by_cases e : u = v
  · subst e
    exact split_ext h τ (congrFun (congrFun h1 i) j) (congrFun (congrFun h2 i) j)
  · exact congrFun (congrFun (hfin u e) i) j

end Mat

section Unitary

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {v : HeightOneSpectrum (𝓞 F)} {n : Type} [Fintype n] [DecidableEq n]

def pairHom {K : Type} [Field K] (J₀ : Matrix n n K) (hJ : IsUnit J₀.det) : GL n K →* Matrix n n K × Matrix n n K where
  toFun g := ((g : Matrix n n K), J₀⁻¹ * ((g⁻¹ : GL n K) : Matrix n n K)ᵀ * J₀)
  map_one' := by
    ext1
    · rfl
    · simp [Matrix.nonsing_inv_mul _ hJ]
  map_mul' g g' := by
    ext1
    · rfl
    · have e : J₀ * J₀⁻¹ = 1 := Matrix.mul_nonsing_inv _ hJ
      show J₀⁻¹ * (((g * g')⁻¹ : GL n K) : Matrix n n K)ᵀ * J₀ =
        (J₀⁻¹ * ((g⁻¹ : GL n K) : Matrix n n K)ᵀ * J₀) * (J₀⁻¹ * ((g'⁻¹ : GL n K) : Matrix n n K)ᵀ * J₀)
      rw [_root_.mul_inv_rev, Units.val_mul, Matrix.transpose_mul]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc J₀ J₀⁻¹, e, Matrix.one_mul]

def oneAdd {R S : Type} [Ring R] [Ring S] (Φ : R →ₙ+* S) : R →* S where
  toFun x := 1 + Φ (x - 1)
  map_one' := by simp
  map_mul' x y := by
    have e : x * y - 1 = (x - 1) + (y - 1) + (x - 1) * (y - 1) := by noncomm_ring
    rw [e, map_add, map_add, map_mul]
    noncomm_ring

/- English proof (translation)
Use `set p := pairHom (J.map τ) hJ g - 1 with hp`. Establish `hN : oneAdd (liftMat h τ) (pairHom (J.map τ) hJ g) = 1 + liftMat h τ p` using `rfl`. Rewrite using `[hN, map_one_add_cA]`. Establish `tr : ∀ {R : Type} [CommRing R] (f : AF F ⊗[F] E →+* R) (A B C : Matrix n n (AF F ⊗[F] E)), (Aᵀ * B * C).map f = (A.map f)ᵀ * B.map f * C.map f` using `fun f A B C => by`. Rewrite using `[Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]`.

Establish `e : J.map τ * (J.map τ)⁻¹ = 1` using `Matrix.mul_nonsing_inv _ hJ`. Establish `gi : ((g⁻¹ : GL n (Fv F v)) : Matrix n n (Fv F v)) * (g : Matrix n n (Fv F v)) = 1` using `Units.inv_mul g`. Apply `mat_ext h τ` to reduce the goal to its premises. Introduce `w`. Rewrite using `[tr, map_one_add_of_zero _ h τ (compInf_liftPair h τ w), map_one_add_of_zero _ h τ (compInf_liftPair h τ w)]`.

Simplify using the standard rewrite rules. Introduce `u hu`. Rewrite using `[tr, map_one_add_of_zero _ h τ (compFin_liftPair_ne h τ hu), map_one_add_of_zero _ h τ (compFin_liftPair_ne h τ hu)]`. Simplify using the standard rewrite rules. Rewrite using `[tr, map_one_add_piW, map_one_add_piW, Matrix.map_map]`.

Establish `hJm : J.map (⇑(GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ) ∘ ⇑(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F` using `F) (AF F))) = J.map τ := by`. Conclude with `Matrix.ext fun i j => piW_inclR τ (J i j)`. Rewrite using `[hJm]`. Simplify using `only [hp, Prod.fst_sub, Prod.snd_sub, Prod.swap, Prod.fst_one, Prod.snd_one, add_sub_cancel]`. Use `show (g : Matrix n n (Fv F v))ᵀ * J.map τ * ((J.map τ)⁻¹ * ((g⁻¹ : GL n (Fv F v)) : Matrix n n (Fv F v))ᵀ * J.map τ) = J.map τ`.

Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc _ (J.map τ), e, Matrix.mul_one, ← Matrix.transpose_mul, gi, Matrix.transpose_one, Matrix.one_mul]`. Rewrite using `[tr, map_one_add_piW_comp, map_one_add_piW_comp, Matrix.map_map]`. Establish `hJm : J.map (⇑(GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (τ.comp σ)) ∘ ⇑(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F` using `F) (AF F))) = (J.map τ)ᵀ := by`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Simplify using `only [Matrix.map_apply, Function.comp_apply, Matrix.transpose_apply]`.

Rewrite using `[piW_inclR, AlgHom.comp_apply, herm]`. Rewrite using `[hJm]`. Simplify using `only [hp, Prod.fst_sub, Prod.snd_sub, Prod.swap, Prod.fst_one, Prod.snd_one, add_sub_cancel]`. Use `show ((J.map τ)⁻¹ * ((g⁻¹ : GL n (Fv F v)) : Matrix n n (Fv F v))ᵀ * J.map τ)ᵀ * (J.map τ)ᵀ * (g : Matrix n n (Fv F v)) = (J.map τ)ᵀ`. Rewrite using `[Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]`.

Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc ((J.map τ)⁻¹)ᵀ, ← Matrix.transpose_mul, e, Matrix.transpose_one, Matrix.one_mul, gi, Matrix.mul_one]`.
-/
theorem unitary (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (J : Matrix n n E) (herm : ∀ i j, σ (J j i) = J i j)
    (hJ : IsUnit (J.map τ).det) (g : GL n (Fv F v)) :
    (oneAdd (liftMat h τ) (pairHom (J.map τ) hJ g))ᵀ * J.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F)) *
      (oneAdd (liftMat h τ) (pairHom (J.map τ) hJ g)).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) =
      J.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F)) := by
  set p := pairHom (J.map τ) hJ g - 1 with hp
  have hN : oneAdd (liftMat h τ) (pairHom (J.map τ) hJ g) = 1 + liftMat h τ p := rfl
  rw [hN, map_one_add_cA]
  have tr : ∀ {R : Type} [CommRing R] (f : AF F ⊗[F] E →+* R) (A B C : Matrix n n (AF F ⊗[F] E)),
      (Aᵀ * B * C).map f = (A.map f)ᵀ * B.map f * C.map f := fun f A B C => by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  have e : J.map τ * (J.map τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hJ
  have gi : ((g⁻¹ : GL n (Fv F v)) : Matrix n n (Fv F v)) * (g : Matrix n n (Fv F v)) = 1 := Units.inv_mul g
  apply mat_ext h τ
  · intro w
    rw [tr, map_one_add_of_zero _ h τ (compInf_liftPair h τ w), map_one_add_of_zero _ h τ (compInf_liftPair h τ w)]
    simp
  · intro u hu
    rw [tr, map_one_add_of_zero _ h τ (compFin_liftPair_ne h τ hu), map_one_add_of_zero _ h τ (compFin_liftPair_ne h τ hu)]
    simp
  · rw [tr, map_one_add_piW, map_one_add_piW, Matrix.map_map]
    have hJm : J.map (⇑(GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ) ∘ ⇑(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) = J.map τ := by
      exact Matrix.ext fun i j => piW_inclR τ (J i j)
    rw [hJm]
    simp only [hp, Prod.fst_sub, Prod.snd_sub, Prod.swap, Prod.fst_one, Prod.snd_one, add_sub_cancel]
    show (g : Matrix n n (Fv F v))ᵀ * J.map τ * ((J.map τ)⁻¹ * ((g⁻¹ : GL n (Fv F v)) : Matrix n n (Fv F v))ᵀ * J.map τ) =
      J.map τ
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc _ (J.map τ), e, Matrix.mul_one,
      ← Matrix.transpose_mul, gi, Matrix.transpose_one, Matrix.one_mul]
  · rw [tr, map_one_add_piW_comp, map_one_add_piW_comp, Matrix.map_map]
    have hJm : J.map (⇑(GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (τ.comp σ)) ∘ ⇑(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) = (J.map τ)ᵀ := by
      refine Matrix.ext fun i j => ?_
      simp only [Matrix.map_apply, Function.comp_apply, Matrix.transpose_apply]
      rw [piW_inclR, AlgHom.comp_apply, herm]
    rw [hJm]
    simp only [hp, Prod.fst_sub, Prod.snd_sub, Prod.swap, Prod.fst_one, Prod.snd_one, add_sub_cancel]
    show ((J.map τ)⁻¹ * ((g⁻¹ : GL n (Fv F v)) : Matrix n n (Fv F v))ᵀ * J.map τ)ᵀ * (J.map τ)ᵀ *
      (g : Matrix n n (Fv F v)) = (J.map τ)ᵀ
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc ((J.map τ)⁻¹)ᵀ, ← Matrix.transpose_mul, e, Matrix.transpose_one, Matrix.one_mul, gi,
      Matrix.mul_one]

end Unitary

end GlobalTheory.SplitGLLift

open GlobalTheory.SplitGLLift in

/- English proof (translation)
Introduce `D T L sc G W t i j M e Bs Γ X om om' h hTr`. Establish `hcm : IsCMExt D.host.F D.host.E D.sp.cm.sig` using `hTr.base.cm`. Establish `herm : ∀ a b, D.sp.cm.sig (Γ.V'.J b a) = Γ.V'.J a b` using `hTr.geo.hV'.herm`. Establish `hJ : IsUnit (Γ.V'.J.map Bs.τ₁).det`. Rewrite using `[isUnit_iff_ne_zero]`.

Establish `e1 : (Γ.V'.J.map Bs.τ₁).det = Bs.τ₁ Γ.V'.J.det`. Rewrite using `[AlgHom.map_det]`. Both sides reduce to the same expression. Rewrite using `[e1, h.JW₁, Matrix.det_smul]`. Rewrite using `[map_ne_zero]`.

Conclude with `mul_ne_zero (pow_ne_zero _ (by norm_num)) (Formalism.L2.Theta.gram_det_ne _)`. Set `N₀ : GL (Fin (G.V (.grid i j)).rank) (Fv D.host.F Bs.v₁) →* Matrix (Fin (G.V (.grid i j)).rank) (Fin (G.V (.grid i j)).rank) (AF D.host.F ⊗[D.host.F] D.host.E)` to `(oneAdd (liftMat hcm Bs.τ₁)).comp (pairHom (Γ.V'.J.map Bs.τ₁) hJ)`. Set `N : GL (Fin (G.V (.grid i j)).rank) (Fv D.host.F Bs.v₁) →* GL (Fin (G.V (.grid i j)).rank) (AF D.host.F ⊗[D.host.F] D.host.E)` to `(Matrix.GeneralLinearGroup.map (Formalism.L2.Theta.cA D)).comp N₀.toHomUnits`. Establish `hU` using `fun g => unitary hcm Bs.τ₁ Γ.V'.J herm hJ g`. Establish `hcc : ∀ g, ((N₀ g).map (Formalism.L2.Theta.cA D)).map (Formalism.L2.Theta.cA D) = N₀ g` using `fun g => Matrix.ext fun a b => Formalism.L2.Theta.cA_cA _`.

Establish `mem : ∀ g, N g ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (AF D.host.F) D.sp.cm.sig (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.spW₁ G i j).gram`. Introduce `g`. Establish `hU' : (N₀ g)ᵀ * Γ.V'.J.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F` using `D.host.F) (AF D.host.F)) * (N₀ g).map (Formalism.L2.Theta.cA D) = Γ.V'.J.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := D.host.F) (AF D.host.F)) := hU g`. Establish `hJi : Γ.V'.J.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F` using `D.host.F) (AF D.host.F)) = -GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.spW₁ G i j).gram := by show GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM Γ.V'.J = _`. Rewrite using `[h.JW₁, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul, map_neg, map_one, neg_one_smul]`.

Rewrite `hU'` using `[hJi, Matrix.mul_neg, Matrix.neg_mul, neg_inj]`. Use `show (((N₀ g).map (Formalism.L2.Theta.cA D)).map (Formalism.L2.Theta.cA D))ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.spW₁ G i j).gram * (N₀ g).map (Formalism.L2.Theta.cA D) = GlobalTheory.Indefi …`. Rewrite using `[hcc]`. Conclude with `hU'`. Use `⟨N.codRestrict _ mem, fun g => ?_⟩` and prove the remaining obligations.

Establish `hmat : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU _ (-1) h.JW₁ (N.codRestrict _ mem g)) = N₀ g` using `hcc g`. Establish `hN₀ : N₀ g = 1 + liftMat hcm Bs.τ₁ (pairHom (Γ.V'.J.map Bs.τ₁) hJ g - 1)` using `rfl`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Use `show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin D.host.F Bs.v₁) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat _ - 1) erw [hmat]`. Rewrite using `[hN₀, add_sub_cancel_left]`.

Conclude with `at_liftMat hcm Bs.τ₁ _`. Use `erw [hmat]`. Rewrite using `[hN₀, map_one_add_piW]`. Conclude with `add_sub_cancel _ _`. Use `erw [hmat]`.

Rewrite using `[hN₀, map_one_add_piW_comp]`. Conclude with `add_sub_cancel _ _`.
-/
theorem GlobalTheory.SplitGLLift.exists_hom_supp_split : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (t : T) (i j : Fin D.R.m) (M : Vol G)
    (e : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Num G i j) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j)
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.IsTripleOf W M t i j e Bs Γ X) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om'),
    ∃ K : GL (Fin (G.V (.grid i j)).rank) (Fv D.host.F Bs.v₁) →* GA D (G.V (.grid i j)), ∀ g,
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU _ (-1) h.JW₁ (K g) ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt D.sp.cm.sig Γ.V' (evFin D.host.F Bs.v₁) ∧
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU _ (-1) h.JW₁ (K g))).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW Bs.τ₁) = g.val ∧
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU _ (-1) h.JW₁ (K g))).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (Bs.τ₁.comp D.sp.cm.sig)) =
        (Γ.V'.J.map Bs.τ₁)⁻¹ * ((g⁻¹ : GL _ _).val)ᵀ * Γ.V'.J.map Bs.τ₁ := by
  intro D T L sc G W t i j M e Bs Γ X om om' h hTr
  have hcm : IsCMExt D.host.F D.host.E D.sp.cm.sig := hTr.base.cm
  have herm : ∀ a b, D.sp.cm.sig (Γ.V'.J b a) = Γ.V'.J a b := hTr.geo.hV'.herm
  have hJ : IsUnit (Γ.V'.J.map Bs.τ₁).det := by
    rw [isUnit_iff_ne_zero]
    have e1 : (Γ.V'.J.map Bs.τ₁).det = Bs.τ₁ Γ.V'.J.det := by
      rw [AlgHom.map_det]; rfl
    rw [e1, h.JW₁, Matrix.det_smul]
    rw [map_ne_zero]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (Formalism.L2.Theta.gram_det_ne _)
  let N₀ : GL (Fin (G.V (.grid i j)).rank) (Fv D.host.F Bs.v₁) →* Matrix (Fin (G.V (.grid i j)).rank)
      (Fin (G.V (.grid i j)).rank) (AF D.host.F ⊗[D.host.F] D.host.E) :=
    (oneAdd (liftMat hcm Bs.τ₁)).comp (pairHom (Γ.V'.J.map Bs.τ₁) hJ)
  let N : GL (Fin (G.V (.grid i j)).rank) (Fv D.host.F Bs.v₁) →* GL (Fin (G.V (.grid i j)).rank)
      (AF D.host.F ⊗[D.host.F] D.host.E) :=
    (Matrix.GeneralLinearGroup.map (Formalism.L2.Theta.cA D)).comp N₀.toHomUnits
  have hU := fun g => unitary hcm Bs.τ₁ Γ.V'.J herm hJ g

  have hcc : ∀ g, ((N₀ g).map (Formalism.L2.Theta.cA D)).map (Formalism.L2.Theta.cA D) = N₀ g := fun g =>
    Matrix.ext fun a b => Formalism.L2.Theta.cA_cA _
  have mem : ∀ g, N g ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (AF D.host.F) D.sp.cm.sig (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.spW₁ G i j).gram := by
    intro g
    have hU' : (N₀ g)ᵀ * Γ.V'.J.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := D.host.F) (AF D.host.F)) *
        (N₀ g).map (Formalism.L2.Theta.cA D) = Γ.V'.J.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := D.host.F) (AF D.host.F)) := hU g
    have hJi : Γ.V'.J.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := D.host.F) (AF D.host.F)) =
        -GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.spW₁ G i j).gram := by
      show GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM Γ.V'.J = _
      rw [h.JW₁, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul, map_neg, map_one, neg_one_smul]
    rw [hJi, Matrix.mul_neg, Matrix.neg_mul, neg_inj] at hU'
    show (((N₀ g).map (Formalism.L2.Theta.cA D)).map (Formalism.L2.Theta.cA D))ᵀ *
        GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.spW₁ G i j).gram * (N₀ g).map (Formalism.L2.Theta.cA D) =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.spW₁ G i j).gram
    rw [hcc]
    exact hU'
  refine ⟨N.codRestrict _ mem, fun g => ?_⟩
  have hmat : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU _ (-1) h.JW₁ (N.codRestrict _ mem g)) = N₀ g := hcc g
  have hN₀ : N₀ g = 1 + liftMat hcm Bs.τ₁ (pairHom (Γ.V'.J.map Bs.τ₁) hJ g - 1) := rfl
  refine ⟨?_, ?_, ?_⟩
  · show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin D.host.F Bs.v₁) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat _ - 1)
    erw [hmat]
    rw [hN₀, add_sub_cancel_left]
    exact at_liftMat hcm Bs.τ₁ _
  · erw [hmat]
    rw [hN₀, map_one_add_piW]
    exact add_sub_cancel _ _
  · erw [hmat]
    rw [hN₀, map_one_add_piW_comp]
    exact add_sub_cancel _ _
