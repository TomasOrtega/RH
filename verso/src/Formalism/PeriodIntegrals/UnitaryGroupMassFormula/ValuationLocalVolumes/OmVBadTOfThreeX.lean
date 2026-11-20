import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVBadTOfFourX
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.PrimCosOf

noncomputable section

namespace PI.OmVd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory PI.OmLocU
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

def LeftInvO (a : ℕ) : Prop :=
  StdHyp σ J ψ → UnramAt (E := E) v →
  ∀ M : Matrix (Fin n) (Fin a) (Fv F v ⊗[F] E), (∀ k i, M k i ∈ OEv (E := E) v) →
    (∀ c : Fin a → Fv F v ⊗[F] E, (∀ k, Matrix.mulVec M c k ∈ OEv (E := E) v) → ∀ i, c i ∈ OEv (E := E) v) →
    ∃ N : Matrix (Fin a) (Fin n) (Fv F v ⊗[F] E), (∀ i k, N i k ∈ OEv (E := E) v) ∧ N * M = 1

/- English proof (translation)
Introduce `hS hSD hUn hL y hy`. Establish `hσ : ∀ x, σ (σ x) = x` using `PI.VolStabSW.sigma_invol σ hS.1.2.2.2`. Take `⟨e, he, hg⟩` from `hB hS hL hSD hUn`. Establish `hee : ∀ k l, hR (Fv F v) σ J (e k) (e l) = if k = l then 1 else 0`. Introduce `k l`.

Use `congrFun (congrFun hg k) l` as an intermediate fact. Simplify `this` using `[gramR, Matrix.one_apply]`. Establish `hcoord : ∀ i, ∃ c : Fin n → Fv F v ⊗[F] E, (∀ k, c k ∈ OEv (E` using `E) v) ∧ y i = ∑ k, c k • e k := fun i => (he (y i)).1 (hy.1 i)`. Use `choose M hM hyM using hcoord`. Take `⟨N, hN, hNM⟩` from `hLI hS hUn (Matrix.of fun k i => M i k) (fun k i => hM i k) (by`.

Introduce `c hc i`. Apply `hy.2 c _ i` to reduce the goal to its premises. Establish `e1 : ∑ i, c i • y i = ∑ k, Matrix.mulVec (Matrix.of fun k i => M i k) c k • e k`. Simplify using `only [hyM, Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_smul]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm]`. Rewrite using `[e1]`. Conclude with `(he _).2 ⟨_, hc, rfl⟩)`. Establish `hNM' : ∀ j i, ∑ l, N j l * M i l = if j = i then 1 else 0`.

Introduce `j i`. Use `congrFun (congrFun hNM j) i` as an intermediate fact. Simplify `this` using `[Matrix.mul_apply, Matrix.one_apply]`. Use `⟨fun j => ∑ l, sigR (Fv F v) σ (N j l) • e l, fun j => (he _).2 ⟨_, fun l => UnN.sigR_mem σ v (hN j l), rfl⟩, fun i j => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Establish `h1 : ∀ l, hR (Fv F v) σ J (y i) (e l) = sigR (Fv F v) σ (M i l)`.

Introduce `l`. Rewrite using `[hyM i, hR_sum_smul_left]`. Simplify using `[hee]`. Rewrite using `[hR_sum_smul_right]`. Simplify using `only [h1]`.

Establish `e2 : ∑ l, sigR (Fv F v) σ (N j l) * sigR (Fv F v) σ (M i l) = sigR (Fv F v) σ (∑ l, N j l * M i l)`. Rewrite using `[map_sum]`. Simplify using `only [map_mul]`. Rewrite using `[e2, hNM' j i]`. Distinguish the cases in `hij : i = j`.

Substitute `hij` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hij, Ne.symm hij]`. Establish `h2 : ∀ k, hR (Fv F v) σ J (∑ l, sigR (Fv F v) σ (N j l) • e l) (e k) = N j k`. Introduce `k`.

Rewrite using `[hR_sum_smul_left]`. Simplify using `only [hee, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Conclude with `PI.VolStabSW.sigR_invol (Fv F v) σ hσ (N j k)`. Rewrite using `[hyM i, hR_sum_smul_right]`. Simplify using `only [h2]`.

Establish `e3 : ∑ k, M i k * N j k = ∑ k, N j k * M i k` using `Finset.sum_congr rfl fun k _ => mul_comm _ _`. Rewrite using `[e3, hNM' j i]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[hij, Ne.symm hij]`.
-/
theorem primDual_of (a : ℕ) (hB : Red.OBas1 σ J ψ v Λ) (hLI : LeftInvO σ J ψ v (n := n) a) :
    PrimDual σ J ψ v Λ a := by
  classical
  intro hS hSD hUn hL y hy
  have hσ : ∀ x, σ (σ x) = x := PI.VolStabSW.sigma_invol σ hS.1.2.2.2
  obtain ⟨e, he, hg⟩ := hB hS hL hSD hUn
  have hee : ∀ k l, hR (Fv F v) σ J (e k) (e l) = if k = l then 1 else 0 := by
    intro k l
    have := congrFun (congrFun hg k) l
    simpa [gramR, Matrix.one_apply] using this
  have hcoord : ∀ i, ∃ c : Fin n → Fv F v ⊗[F] E, (∀ k, c k ∈ OEv (E := E) v) ∧ y i = ∑ k, c k • e k :=
    fun i => (he (y i)).1 (hy.1 i)
  choose M hM hyM using hcoord
  obtain ⟨N, hN, hNM⟩ := hLI hS hUn (Matrix.of fun k i => M i k) (fun k i => hM i k) (by
    intro c hc i
    apply hy.2 c _ i
    have e1 : ∑ i, c i • y i = ∑ k, Matrix.mulVec (Matrix.of fun k i => M i k) c k • e k := by
      simp only [hyM, Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
      rw [mul_comm]
    rw [e1]
    exact (he _).2 ⟨_, hc, rfl⟩)
  have hNM' : ∀ j i, ∑ l, N j l * M i l = if j = i then 1 else 0 := by
    intro j i
    have := congrFun (congrFun hNM j) i
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  refine ⟨fun j => ∑ l, sigR (Fv F v) σ (N j l) • e l,
    fun j => (he _).2 ⟨_, fun l => UnN.sigR_mem σ v (hN j l), rfl⟩, fun i j => ⟨?_, ?_⟩⟩
  · have h1 : ∀ l, hR (Fv F v) σ J (y i) (e l) = sigR (Fv F v) σ (M i l) := by
      intro l
      rw [hyM i, hR_sum_smul_left]
      simp [hee]
    rw [hR_sum_smul_right]
    simp only [h1]
    have e2 : ∑ l, sigR (Fv F v) σ (N j l) * sigR (Fv F v) σ (M i l) =
        sigR (Fv F v) σ (∑ l, N j l * M i l) := by
      rw [map_sum]
      simp only [map_mul]
    rw [e2, hNM' j i]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Ne.symm hij]
  · have h2 : ∀ k, hR (Fv F v) σ J (∑ l, sigR (Fv F v) σ (N j l) • e l) (e k) = N j k := by
      intro k
      rw [hR_sum_smul_left]
      simp only [hee, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      exact PI.VolStabSW.sigR_invol (Fv F v) σ hσ (N j k)
    rw [hyM i, hR_sum_smul_right]
    simp only [h2]
    have e3 : ∑ k, M i k * N j k = ∑ k, N j k * M i k := Finset.sum_congr rfl fun k _ => mul_comm _ _
    rw [e3, hNM' j i]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Ne.symm hij]

/- English proof (translation)
Establish `hR : Red.ResAlg σ J ψ v` using `Red.resAlg_of_sp σ J ψ v (Red.etaSp_holds σ J ψ v)`. Conclude with `Red.oBas1_of_unitV σ J ψ v Λ (Orb.unitV_of σ J ψ v Λ (PI.OmLocU.NormOneUnitFixedPoints.normOne_of σ J ψ v hR) (UnN.unitNorm_of_res σ J ψ v Λ hR))`.
-/
theorem oBas1_holds : Red.OBas1 σ J ψ v Λ := by
  have hR : Red.ResAlg σ J ψ v := Red.resAlg_of_sp σ J ψ v (Red.etaSp_holds σ J ψ v)
  exact Red.oBas1_of_unitV σ J ψ v Λ
    (Orb.unitV_of σ J ψ v Λ (PI.OmLocU.NormOneUnitFixedPoints.normOne_of σ J ψ v hR) (UnN.unitNorm_of_res σ J ψ v Λ hR))

/- English proof (translation)
The claim follows from `primDual_of σ J ψ v Λ a (oBas1_holds σ J ψ v Λ) hLI`.
-/
theorem primDual_of_left (a : ℕ) (hLI : LeftInvO σ J ψ v (n := n) a) : PrimDual σ J ψ v Λ a :=
  primDual_of σ J ψ v Λ a (oBas1_holds σ J ψ v Λ) hLI

end Gen

section Loc

open Formalism.L2.SG.Pf.NcVal.OmVSt Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

/- English proof (translation)
The claim follows from `omVBadT_of_primDual_cls X u' ψ hStd hLat hGram hExt (fun v => primCos_of _ _ _ _ _ _ (primDual_of_left _ _ _ _ _ _ (hLI v))) (fun v => primDual_of_left _ _ _ _ _ _ (hLI v)) hCl`.
-/
theorem omVBadT_of_std_lat_gram (hStd : OmVStd X ψ) (hLat : OmVLat X) (hGram : OmVGram X u')
    (hExt : ∀ v : PlX X, ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
      ExtP X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v))
    (hLI : ∀ v : PlX X, LeftInvO X.B.I.cm.sig X.B.I.J ψ v (n := X.B.I.n) (D.R.rS + 1 + D.R.rS))
    (hCl : ∀ v : PlX X, ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
      ClsP X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v)) :
    OmVBadT X u' ψ :=
  omVBadT_of_primDual_cls X u' ψ hStd hLat hGram hExt
    (fun v => primCos_of _ _ _ _ _ _ (primDual_of_left _ _ _ _ _ _ (hLI v)))
    (fun v => primDual_of_left _ _ _ _ _ _ (hLI v)) hCl

end Loc

end PI.OmVd
