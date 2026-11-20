import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataInst
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.TensInjHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.EventuallyStruct

noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting
open scoped TensorProduct

section Glue

variable {D : D7} (X : HidaSetting D)

/- English proof (translation)
Establish `h1 : ∀ᶠ v in Filter.cofinite, (algebraMap X.B.I.F (Af X.B.I.F) c) v ∈ v.adicCompletionIntegers X.B.I.F` using `(algebraMap X.B.I.F (Af X.B.I.F) c).2`. Establish `hev : ∀ᶠ v in Filter.cofinite, a v ∈ v.adicCompletionIntegers X.B.I.F` using `by filter_upwards [h1, T.eventually_cofinite_notMem] with v hv1 hv2`. Rewrite using `[ha v hv2]`. Conclude with `hv1`. Conclude with `⟨RestrictedProduct.mk a hev, fun v => rfl⟩`.
-/
theorem glue_af (T : Finset (HeightOneSpectrum (𝓞 X.B.I.F))) (a : ∀ v : HeightOneSpectrum (𝓞 X.B.I.F), Fv X.B.I.F v)
    (c : X.B.I.F) (ha : ∀ v, v ∉ T → a v = evalV X.B.I.F v (algebraMap X.B.I.F (Af X.B.I.F) c)) :
    ∃ A : Af X.B.I.F, ∀ v, evalV X.B.I.F v A = a v := by
  have h1 : ∀ᶠ v in Filter.cofinite, (algebraMap X.B.I.F (Af X.B.I.F) c) v ∈ v.adicCompletionIntegers X.B.I.F :=
    (algebraMap X.B.I.F (Af X.B.I.F) c).2
  have hev : ∀ᶠ v in Filter.cofinite, a v ∈ v.adicCompletionIntegers X.B.I.F := by
    filter_upwards [h1, T.eventually_cofinite_notMem] with v hv1 hv2
    rw [ha v hv2]
    exact hv1
  exact ⟨RestrictedProduct.mk a hev, fun v => rfl⟩

/- English proof (translation)
Establish `: Module.Finite X.B.I.F X.B.I.E` using `Module.finite_of_finrank_eq_succ (n := 1) X.B.I.cm.deg2`. Set `b` to `Module.finBasis X.B.I.F X.B.I.E`. Establish `key : ∀ i, ∃ A : Af X.B.I.F, ∀ v, evalV X.B.I.F v A = (Algebra.TensorProduct.basis (Fv X.B.I.F v) b).repr (m v) i` using `fun i => glue_af X T _ (b.repr c i) (fun v hv => by`. Rewrite using `[hm v hv, AlgHom.commutes]`. Simplify using `[inclR, Algebra.TensorProduct.includeRight_apply])`.

Use `choose A hA using key`. Use `⟨(Algebra.TensorProduct.basis (Af X.B.I.F) b).equivFun.symm A, fun v => ?_⟩` and prove the remaining obligations. Apply `(Algebra.TensorProduct.basis (Fv X.B.I.F v) b).repr.injective` to reduce the goal to its premises. Use `Finsupp.ext (fun i => ?_)` and prove the remaining obligations. Rewrite using `[tens_repr, ← hA i v]`.

Use `congr 1`. Conclude with `congrFun ((Algebra.TensorProduct.basis (Af X.B.I.F) b).equivFun.apply_symm_apply A) i`.
-/
theorem glue_tens (T : Finset (HeightOneSpectrum (𝓞 X.B.I.F)))
    (m : ∀ v : HeightOneSpectrum (𝓞 X.B.I.F), Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) (c : X.B.I.E)
    (hm : ∀ v, v ∉ T → m v = inclR (Fv X.B.I.F v) c) :
    ∃ M : Af X.B.I.F ⊗[X.B.I.F] X.B.I.E, ∀ v, tensMap (E := X.B.I.E) (evalV X.B.I.F v) M = m v := by
  have : Module.Finite X.B.I.F X.B.I.E := Module.finite_of_finrank_eq_succ (n := 1) X.B.I.cm.deg2
  let b := Module.finBasis X.B.I.F X.B.I.E
  have key : ∀ i, ∃ A : Af X.B.I.F, ∀ v, evalV X.B.I.F v A =
      (Algebra.TensorProduct.basis (Fv X.B.I.F v) b).repr (m v) i := fun i =>
    glue_af X T _ (b.repr c i) (fun v hv => by
      rw [hm v hv, AlgHom.commutes]
      simp [inclR, Algebra.TensorProduct.includeRight_apply])
  choose A hA using key
  refine ⟨(Algebra.TensorProduct.basis (Af X.B.I.F) b).equivFun.symm A, fun v => ?_⟩
  apply (Algebra.TensorProduct.basis (Fv X.B.I.F v) b).repr.injective
  refine Finsupp.ext (fun i => ?_)
  rw [tens_repr, ← hA i v]
  congr 1
  exact congrFun ((Algebra.TensorProduct.basis (Af X.B.I.F) b).equivFun.apply_symm_apply A) i

/- English proof (translation)
Establish `key : ∀ i j, ∃ a : Af X.B.I.F ⊗[X.B.I.F] X.B.I.E, ∀ v, tensMap (E` using `X.B.I.E) (evalV X.B.I.F v) a = m v i j := fun i j => glue_tens X T (fun v => m v i j) (C i j) (fun v hv => by rw [hm v hv]; rfl)`. Use `choose M hM using key`. Conclude with `⟨Matrix.of M, fun v => Matrix.ext (fun i j => by simp [hM])⟩`.
-/
theorem glue_mat (T : Finset (HeightOneSpectrum (𝓞 X.B.I.F)))
    (m : ∀ v : HeightOneSpectrum (𝓞 X.B.I.F), Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E))
    (C : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E)
    (hm : ∀ v, v ∉ T → m v = C.map (inclR (Fv X.B.I.F v))) :
    ∃ M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Af X.B.I.F ⊗[X.B.I.F] X.B.I.E),
      ∀ v, M.map (tensMap (E := X.B.I.E) (evalV X.B.I.F v)) = m v := by
  have key : ∀ i j, ∃ a : Af X.B.I.F ⊗[X.B.I.F] X.B.I.E, ∀ v,
      tensMap (E := X.B.I.E) (evalV X.B.I.F v) a = m v i j := fun i j =>
    glue_tens X T (fun v => m v i j) (C i j) (fun v hv => by rw [hm v hv]; rfl)
  choose M hM using key
  exact ⟨Matrix.of M, fun v => Matrix.ext (fun i j => by simp [hM])⟩

/- English proof (translation)
The claim follows from `Matrix.ext (fun i j => tensInj_holds X _ _ (fun v => by have := congrFun (congrFun (h v) i) j simpa using this))`.
-/
theorem mat_inj (M N : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Af X.B.I.F ⊗[X.B.I.F] X.B.I.E))
    (h : ∀ v, M.map (tensMap (E := X.B.I.E) (evalV X.B.I.F v)) = N.map (tensMap (E := X.B.I.E) (evalV X.B.I.F v))) :
    M = N :=
  Matrix.ext (fun i j => tensInj_holds X _ _ (fun v => by
    have := congrFun (congrFun (h v) i) j
    simpa using this))

/- English proof (translation)
Establish `hcT : (Formalism.UG.cT (sigR R X.B.I.cm.sig) g).map (tensMap (E` using `X.B.I.E) φ) = Formalism.UG.cT (sigR S X.B.I.cm.sig) (g.map (tensMap (E := X.B.I.E) φ)) := by`. Use extensionality with `i j`. Simplify using `[Formalism.UG.cT, Matrix.map_apply, Matrix.transpose_apply, tensMap, PI.VolStabSW.CompGAux.tmap_sigR]`. Establish `hJ : (JR R X.B.I.J).map (tensMap (E` using `X.B.I.E) φ) = JR S X.B.I.J := by`. Use extensionality with `i j`.

Simplify using `[JR, Matrix.map_apply, tensMap, PI.VolStabSW.CompGAux.tmap_inclR]`. Rewrite using `[Matrix.map_mul, Matrix.map_mul, hcT, hJ]`.
-/
theorem map_cT {R S : Type} [CommRing R] [Algebra X.B.I.F R] [CommRing S] [Algebra X.B.I.F S]
    (φ : R →ₐ[X.B.I.F] S) (g : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (R ⊗[X.B.I.F] X.B.I.E)) :
    (Formalism.UG.cT (sigR R X.B.I.cm.sig) g * JR R X.B.I.J * g).map (tensMap (E := X.B.I.E) φ) =
      Formalism.UG.cT (sigR S X.B.I.cm.sig) (g.map (tensMap (E := X.B.I.E) φ)) * JR S X.B.I.J *
        g.map (tensMap (E := X.B.I.E) φ) := by
  have hcT : (Formalism.UG.cT (sigR R X.B.I.cm.sig) g).map (tensMap (E := X.B.I.E) φ) =
      Formalism.UG.cT (sigR S X.B.I.cm.sig) (g.map (tensMap (E := X.B.I.E) φ)) := by
    ext i j
    simp [Formalism.UG.cT, Matrix.map_apply, Matrix.transpose_apply, tensMap, PI.VolStabSW.CompGAux.tmap_sigR]
  have hJ : (JR R X.B.I.J).map (tensMap (E := X.B.I.E) φ) = JR S X.B.I.J := by
    ext i j
    simp [JR, Matrix.map_apply, tensMap, PI.VolStabSW.CompGAux.tmap_inclR]
  rw [Matrix.map_mul, Matrix.map_mul, hcT, hJ]

end Glue

/- English proof (translation)
Introduce `D X t`. Set `T` to `typSet X.B.I.F (D.host.g 0) (D.host.g 1)`. Set `gt : ∀ v : HeightOneSpectrum (𝓞 X.B.I.F), GL (Fin X.B.I.n) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)` to `fun v => if hv : v ∈ T then HA.mat (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (t ⟨v, hv⟩) else 1`. Establish `hgt : ∀ v, gt v ∈ HR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J`. Introduce `v`.

Distinguish the cases in `hv : v ∈ T`. Simplify using `only [gt, dif_pos hv]`. Conclude with `(show ↥(HR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J) from t ⟨v, hv⟩).2`. Simplify using `only [gt, dif_neg hv]`. Conclude with `Subgroup.one_mem _`.

Establish `hout : ∀ v, v ∉ T → gt v = 1` using `fun v hv => by simp only [gt, dif_neg hv]`. Establish `h1 : ∀ (v : HeightOneSpectrum (𝓞 X.B.I.F)), (1 : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) = (1 : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (inclR (Fv X.B.I.F v))` using `fun v => (Matrix.map_one _ (map_zero _) (map_one _)).symm`. Take `⟨M, hM⟩` from `glue_mat X T (fun v => ((gt v : GL _ _) : Matrix _ _ _)) 1 (fun v hv => by simp only [hout v hv, Units.val_one]; exact h1 v)`. Take `⟨N, hN⟩` from `glue_mat X T (fun v => (((gt v)⁻¹ : GL _ _) : Matrix _ _ _)) 1 (fun v hv => by simp only [hout v hv, inv_one, Units.val_one]; exact h1 v)`. Establish `hMN : M * N = 1` using `mat_inj X _ _ (fun v => by`.

Rewrite using `[Matrix.map_mul, hM v, hN v, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)])`. Establish `hNM : N * M = 1` using `mat_inj X _ _ (fun v => by`. Rewrite using `[Matrix.map_mul, hM v, hN v, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)])`. Set `G : GL (Fin X.B.I.n) (Af X.B.I.F ⊗[X.B.I.F] X.B.I.E)` to `⟨M, N, hMN, hNM⟩`. Establish `hG : G ∈ HR (Af X.B.I.F) X.B.I.cm.sig X.B.I.J` using `by show Formalism.UG.cT (sigR (Af X.B.I.F) X.B.I.cm.sig) M * JR (Af X.B.I.F) X.B.I.J * M = JR (Af X.B.I.F) X.B.I.J`.

Apply `mat_inj X` to reduce the goal to its premises. Introduce `v`. Rewrite using `[map_cT X (evalV X.B.I.F v) M, hM v]`. Establish `hv : Formalism.UG.cT (sigR (Fv X.B.I.F v) X.B.I.cm.sig) ((gt v : GL _ _) : Matrix _ _ _) * JR (Fv X.B.I.F v) X.B.I.J * ((gt v : GL _ _) : Matrix _ _ _) = JR (Fv X.B.I.F v) X.B.I.J` using `hgt v`. Rewrite using `[hv]`.

Use extensionality with `i j`. Simplify using `[JR, Matrix.map_apply, tensMap, PI.VolStabSW.CompGAux.tmap_inclR]`. Set `hA : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J` to `(⟨G, hG⟩ : ↥(HR (Af X.B.I.F) X.B.I.cm.sig X.B.I.J))`. Establish `hc : ∀ v, haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F v) hA = (⟨gt v, hgt v⟩ : ↥(HR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J))` using `fun v => Subtype.ext (Units.ext (hM v))`. Use `⟨hA, fun p => ?_, fun v hv => ?_⟩` and prove the remaining obligations.

Rewrite using `[hc p.1]`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [gt]`. Rewrite using `[dif_pos (show p.1 ∈ T from p.2)]`. Both sides reduce to the same expression.

Rewrite using `[hc v]`. Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `hout v hv`.
-/
theorem glueHA_holds : GlueHA := by
  intro D X t
  classical
  let T := typSet X.B.I.F (D.host.g 0) (D.host.g 1)
  let gt : ∀ v : HeightOneSpectrum (𝓞 X.B.I.F), GL (Fin X.B.I.n) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) := fun v =>
    if hv : v ∈ T then HA.mat (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (t ⟨v, hv⟩) else 1
  have hgt : ∀ v, gt v ∈ HR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J := by
    intro v
    by_cases hv : v ∈ T
    · simp only [gt, dif_pos hv]
      exact (show ↥(HR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J) from t ⟨v, hv⟩).2
    · simp only [gt, dif_neg hv]
      exact Subgroup.one_mem _
  have hout : ∀ v, v ∉ T → gt v = 1 := fun v hv => by simp only [gt, dif_neg hv]
  have h1 : ∀ (v : HeightOneSpectrum (𝓞 X.B.I.F)),
      (1 : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) =
        (1 : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (inclR (Fv X.B.I.F v)) := fun v =>
    (Matrix.map_one _ (map_zero _) (map_one _)).symm
  obtain ⟨M, hM⟩ := glue_mat X T (fun v => ((gt v : GL _ _) : Matrix _ _ _)) 1
    (fun v hv => by simp only [hout v hv, Units.val_one]; exact h1 v)
  obtain ⟨N, hN⟩ := glue_mat X T (fun v => (((gt v)⁻¹ : GL _ _) : Matrix _ _ _)) 1
    (fun v hv => by simp only [hout v hv, inv_one, Units.val_one]; exact h1 v)
  have hMN : M * N = 1 := mat_inj X _ _ (fun v => by
    rw [Matrix.map_mul, hM v, hN v, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)])
  have hNM : N * M = 1 := mat_inj X _ _ (fun v => by
    rw [Matrix.map_mul, hM v, hN v, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)])
  let G : GL (Fin X.B.I.n) (Af X.B.I.F ⊗[X.B.I.F] X.B.I.E) := ⟨M, N, hMN, hNM⟩
  have hG : G ∈ HR (Af X.B.I.F) X.B.I.cm.sig X.B.I.J := by
    show Formalism.UG.cT (sigR (Af X.B.I.F) X.B.I.cm.sig) M * JR (Af X.B.I.F) X.B.I.J * M = JR (Af X.B.I.F) X.B.I.J
    apply mat_inj X
    intro v
    rw [map_cT X (evalV X.B.I.F v) M, hM v]
    have hv : Formalism.UG.cT (sigR (Fv X.B.I.F v) X.B.I.cm.sig) ((gt v : GL _ _) : Matrix _ _ _) *
        JR (Fv X.B.I.F v) X.B.I.J * ((gt v : GL _ _) : Matrix _ _ _) = JR (Fv X.B.I.F v) X.B.I.J := hgt v
    rw [hv]
    ext i j
    simp [JR, Matrix.map_apply, tensMap, PI.VolStabSW.CompGAux.tmap_inclR]
  let hA : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J := (⟨G, hG⟩ : ↥(HR (Af X.B.I.F) X.B.I.cm.sig X.B.I.J))
  have hc : ∀ v, haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F v) hA =
      (⟨gt v, hgt v⟩ : ↥(HR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J)) := fun v =>
    Subtype.ext (Units.ext (hM v))
  refine ⟨hA, fun p => ?_, fun v hv => ?_⟩
  · rw [hc p.1]
    apply Subtype.ext
    simp only [gt]
    rw [dif_pos (show p.1 ∈ T from p.2)]
    rfl
  · rw [hc v]
    apply Subtype.ext
    exact hout v hv

/- English proof (translation)
The claim follows from `global_product_of_local glueHA_holds tensInj_holds hl`.
-/
theorem globProd_of_k2Loc (hl : LevelCongruenceLocal) : GlobProd := global_product_of_local glueHA_holds tensInj_holds hl

end MassDataLevelSSteps
