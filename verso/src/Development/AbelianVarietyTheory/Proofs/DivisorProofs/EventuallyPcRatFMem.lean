import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmField
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EulerTwU

open GlobalTheory.EulerTw

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

/- English proof (translation)
Establish `hid : pLoc E v (idem E T) = if v ∈ T then 1 else 0` using `rfl`. Use `Units.ext (Matrix.ext fun i j => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `pLoc E v ((idem E T • g.val + (1 - idem E T) • (1 : Matrix (Fin n) (Fin n) (Af E))) i j) = _`. Simplify using `only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul, map_sub, map_one, hid]`. Use `split_ifs with h`.

Simplify using `[Matrix.one_apply, apply_ite (pLoc E v)]`. Simplify using `[Matrix.one_apply, apply_ite (pLoc E v)]`.
-/
theorem pc_prjG (T : Finset (Pl E)) (g : GL (Fin n) (Af E)) (v : Pl E) :
    GeneralLinearGroup.map (pLoc E v) (prjG E n T g) =
      if v ∈ T then GeneralLinearGroup.map (pLoc E v) g else 1 := by
  have hid : pLoc E v (idem E T) = if v ∈ T then 1 else 0 := rfl
  refine Units.ext (Matrix.ext fun i j => ?_)
  change pLoc E v ((idem E T • g.val + (1 - idem E T) • (1 : Matrix (Fin n) (Fin n) (Af E))) i j) = _
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul, map_sub, map_one, hid]
  split_ifs with h
  · simp [Matrix.one_apply, apply_ite (pLoc E v)]
  · simp [Matrix.one_apply, apply_ite (pLoc E v)]

/- English proof (translation)
Use extensionality with `i j : 2`. Conclude with `FiniteAdeleRing.ext _ fun v => congrArg (fun g : GL (Fin n) (v.adicCompletion E) => g.val i j) (h v)`.
-/
theorem gl_ext {k k' : GL (Fin n) (Af E)}
    (h : ∀ v : Pl E, GeneralLinearGroup.map (pLoc E v) k = GeneralLinearGroup.map (pLoc E v) k') : k = k' := by
  ext i j : 2
  exact FiniteAdeleRing.ext _ fun v => congrArg (fun g : GL (Fin n) (v.adicCompletion E) => g.val i j) (h v)

/- English proof (translation)
Simplify using `[orb]`.
-/
theorem mem_orb {u v : Pl E} : v ∈ orb E u ↔ v = u ∨ v = cPl E u := by
  simp [orb]

/- English proof (translation)
The claim follows from `GlobalTheory.ThetaPull.conjSrc_conjSrc v`.
-/
theorem cPl_cPl (v : Pl E) : cPl E (cPl E v) = v := GlobalTheory.ThetaPull.conjSrc_conjSrc v

/- English proof (translation)
Break down `mem_orb.1 hv with rfl | rfl` into its components or cases. Conclude with `mem_orb.2 (Or.inr rfl)`. Conclude with `mem_orb.2 (Or.inl (cPl_cPl u))`.
-/
theorem cPl_mem_orb {u v : Pl E} (hv : v ∈ orb E u) : cPl E v ∈ orb E u := by
  rcases mem_orb.1 hv with rfl | rfl
  · exact mem_orb.2 (Or.inr rfl)
  · exact mem_orb.2 (Or.inl (cPl_cPl u))

/- English proof (translation)
Take `⟨g, hg⟩` from `y.2`. Rewrite using `[← hg, pc_prjG, if_neg hv]`.
-/
theorem pc_gam {u v : Pl E} (y : Gam E n u) (hv : v ∉ orb E u) :
    GeneralLinearGroup.map (pLoc E v) (y : GL (Fin n) (Af E)) = 1 := by
  obtain ⟨g, hg⟩ := y.2
  rw [← hg, pc_prjG, if_neg hv]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `GeneralLinearGroup.map (pLoc E v) (prjG E n (orb E u) g) = _`. Rewrite using `[pc_prjG, if_pos hv]`.
-/
theorem pc_pfU {u v : Pl E} (hv : v ∈ orb E u) (g : GL (Fin n) (Af E)) :
    GeneralLinearGroup.map (pLoc E v) ((pfU E n u g : Gam E n u) : GL (Fin n) (Af E)) =
      GeneralLinearGroup.map (pLoc E v) g := by
  change GeneralLinearGroup.map (pLoc E v) (prjG E n (orb E u) g) = _
  rw [pc_prjG, if_pos hv]

/- English proof (translation)
Simplify using `[Kglob, Subgroup.mem_iInf]`.
-/
theorem mem_Kglob_iff (k : GL (Fin n) (Af E)) :
    k ∈ Kglob E n ↔ ∀ v : Pl E, GeneralLinearGroup.map (pLoc E v) k ∈ GlobalTheory.LFun.KGL v n := by
  simp [Kglob, Subgroup.mem_iInf]

/- English proof (translation)
The claim follows from `GlobalTheory.ThetaPull.map_thetaGL (pLoc E v) (RingHom.id _) (RingHom.id _) (fun _ => rfl) (GeneralLinearGroup.map (conjFin (IsCMField.complexConj E).toRingEquiv) x)`.
-/
theorem pc_thF (v : Pl E) (x : GL (Fin n) (Af E)) :
    GeneralLinearGroup.map (pLoc E v) (thF E n x) = thetaGL n (RingHom.id _)
      (GeneralLinearGroup.map (conjLoc (IsCMField.complexConj E).toRingEquiv v)
        (GeneralLinearGroup.map (pLoc E (cPl E v)) x)) :=
  GlobalTheory.ThetaPull.map_thetaGL (pLoc E v) (RingHom.id _) (RingHom.id _) (fun _ => rfl)
    (GeneralLinearGroup.map (conjFin (IsCMField.complexConj E).toRingEquiv) x)

/- English proof (translation)
The claim follows from `GlobalTheory.ThetaPull.thetaGL_thetaGL _ (fun y => GlobalTheory.ThetaPull.cFin_cFin y) x`.
-/
theorem thF_thF (x : GL (Fin n) (Af E)) : thF E n (thF E n x) = x :=
  GlobalTheory.ThetaPull.thetaGL_thetaGL _ (fun y => GlobalTheory.ThetaPull.cFin_cFin y) x

/- English proof (translation)
The claim follows from `Units.ext (Matrix.ext fun _ _ => rfl)`.
-/
theorem pc_ratF (v : Pl E) (δ : GL (Fin n) E) :
    GeneralLinearGroup.map (pLoc E v) (ratF E n δ) = GeneralLinearGroup.map (algebraMap E (v.adicCompletion E)) δ :=
  Units.ext (Matrix.ext fun _ _ => rfl)

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Apply `gl_ext` to reduce the goal to its premises. Introduce `v`. Distinguish the cases in `hv : v ∈ orb E u`. Express the relevant statement in the definitionally equal form `GeneralLinearGroup.map (pLoc E v) (prjG E n (orb E u) (thF E n (prjG E n (orb E u) (thF E n y.1)))) = _`.

Rewrite using `[pc_prjG, if_pos hv, pc_thF, pc_prjG, if_pos (cPl_mem_orb hv), ← pc_thF, thF_thF]`. Rewrite using `[pc_gam _ hv, pc_gam _ hv]`.
-/
theorem thU_thU (u : Pl E) (y : Gam E n u) : thU E n u (thU E n u y) = y := by
  apply Subtype.ext
  apply gl_ext
  intro v
  by_cases hv : v ∈ orb E u
  · change GeneralLinearGroup.map (pLoc E v) (prjG E n (orb E u) (thF E n (prjG E n (orb E u) (thF E n y.1)))) = _
    rw [pc_prjG, if_pos hv, pc_thF, pc_prjG, if_pos (cPl_mem_orb hv), ← pc_thF, thF_thF]
  · rw [pc_gam _ hv, pc_gam _ hv]

/- English proof (translation)
The claim follows from `Continuous.units_map _ (continuous_id.matrix_map (RestrictedProduct.continuous_eval v))`.
-/
theorem continuous_pc (v : Pl E) : Continuous (GeneralLinearGroup.map (n := Fin n) (pLoc E v)) :=
  Continuous.units_map _ (continuous_id.matrix_map (RestrictedProduct.continuous_eval v))

/- English proof (translation)
The claim follows from `(algebraMap E (FiniteAdeleRing (𝓞 E) E) x).2`.
-/
theorem eventually_int (x : E) :
    ∀ᶠ w : Pl E in cofinite, algebraMap E (w.adicCompletion E) x ∈ w.adicCompletionIntegers E :=
  (algebraMap E (FiniteAdeleRing (𝓞 E) E) x).2

/- English proof (translation)
Establish `hi : Function.Injective fun A : Matrix (Fin n) (Fin n) O => A.map O.subtype` using `Matrix.map_injective Subtype.val_injective`. Use `⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, hi ?_, hi ?_⟩, Units.ext rfl⟩` and prove the remaining obligations. Simplify using `only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]`. Conclude with `g.mul_inv`. Simplify using `only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]`.

Conclude with `g.inv_mul`.
-/
theorem mem_GLint {L : Type} [Field L] (O : Subring L) (g : GL (Fin n) L)
    (h1 : ∀ i j, g.1 i j ∈ O) (h2 : ∀ i j, g⁻¹.1 i j ∈ O) : g ∈ Formalism.UG.GLint (Fin n) O := by
  have hi : Function.Injective fun A : Matrix (Fin n) (Fin n) O => A.map O.subtype :=
    Matrix.map_injective Subtype.val_injective
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, hi ?_, hi ?_⟩, Units.ext rfl⟩
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.mul_inv
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.inv_mul

/- English proof (translation)
Establish `h : ∀ g : GL (Fin n) E, ∀ᶠ w : Pl E in cofinite, ∀ i j, algebraMap E (w.adicCompletion E) (g.val i j) ∈ w.adicCompletionIntegers E` using `fun g => by`. Simplify using `only [Filter.eventually_all]`. Conclude with `fun i j => eventually_int _`. Use `filter_upwards [h g, h g⁻¹] with w a b`. Rewrite using `[pc_ratF]`.

Conclude with `mem_GLint _ _ a (by rw [← map_inv]; exact b)`.
-/
theorem eventually_pc_ratF_mem (g : GL (Fin n) E) : ∀ᶠ v : Pl E in cofinite,
    GeneralLinearGroup.map (pLoc E v) (ratF E n g) ∈ GlobalTheory.LFun.KGL v n := by
  have h : ∀ g : GL (Fin n) E, ∀ᶠ w : Pl E in cofinite, ∀ i j,
      algebraMap E (w.adicCompletion E) (g.val i j) ∈ w.adicCompletionIntegers E := fun g => by
    simp only [Filter.eventually_all]; exact fun i j => eventually_int _
  filter_upwards [h g, h g⁻¹] with w a b
  rw [pc_ratF]
  exact mem_GLint _ _ a (by rw [← map_inv]; exact b)

end GlobalTheory.EulerTwU
