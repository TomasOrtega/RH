import Formalism.LocalToGlobal.ProjectiveLattices.ResChPrime

noncomputable section

namespace Formalism.L2.Pj

open Formalism.BasicNotions Formalism.MainNotions NumberField

section Pull

variable {E : Type} [Field E] [NumberField E] {Y Y' : Type} [AddCommGroup Y] [Module (𝓞 E) Y]
  [AddCommGroup Y'] [Module (𝓞 E) Y']

def pullF (e : Y ≃ₗ[𝓞 E] Y') : (Y' →ₗ[ℤ] Y' →ₗ[ℤ] ℝ) →ₗ[ℝ] (Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) where
  toFun β := β.compl₁₂ (e.toAddEquiv.toIntLinearEquiv : Y →ₗ[ℤ] Y') (e.toAddEquiv.toIntLinearEquiv : Y →ₗ[ℤ] Y')
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

/- English proof (translation)
Simplify using `[pullF]`.
-/
@[simp] theorem pullF_apply (e : Y ≃ₗ[𝓞 E] Y') (β : Y' →ₗ[ℤ] Y' →ₗ[ℤ] ℝ) (a b : Y) :
    pullF e β a b = β (e a) (e b) := by
  simp [pullF]

def pullS (cj : E → E) (e : Y ≃ₗ[𝓞 E] Y') : ModuliIntegralCharts.SymB cj Y' →ₗ[ℝ] ModuliIntegralCharts.SymB cj Y :=
  (pullF e).restrict fun β hβ => by
    refine ⟨fun a b => ?_, fun c c' h a b => ?_⟩
    · simp only [pullF_apply]; exact hβ.1 _ _
    · simp only [pullF_apply, LinearEquiv.map_smul]; exact hβ.2 c c' h _ _

/- English proof (translation)
The claim follows from `pullF_apply e _ a b`.
-/
@[simp] theorem pullS_apply (cj : E → E) (e : Y ≃ₗ[𝓞 E] Y') (β : ModuliIntegralCharts.SymB cj Y') (a b : Y) :
    (pullS cj e β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a b = (β : Y' →ₗ[ℤ] Y' →ₗ[ℤ] ℝ) (e a) (e b) :=
  pullF_apply e _ a b

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Use extensionality with `a b`. Simplify using the standard rewrite rules.
-/
theorem pullS_symm (cj : E → E) (e : Y ≃ₗ[𝓞 E] Y') (β : ModuliIntegralCharts.SymB cj Y') :
    pullS cj e.symm (pullS cj e β) = β := by
  apply Subtype.ext; ext a b; simp

def phiSet (cj : E → E) {Z : Type} [AddCommGroup Z] [Module (𝓞 E) Z] (b : ModuliIntegralCharts.SymB cj Z) : Set ℝ :=
  {x | ∃ l : ModuliIntegralCharts.SymB cj Z →ₗ[ℝ] ℝ,
    (∀ β : ModuliIntegralCharts.SymB cj Z, (∀ a c, ∃ z : ℤ, (β : Z →ₗ[ℤ] Z →ₗ[ℤ] ℝ) a c = z) → ∃ z : ℤ, l β = z) ∧
    (∀ β : ModuliIntegralCharts.SymB cj Z, (∀ a, 0 ≤ (β : Z →ₗ[ℤ] Z →ₗ[ℤ] ℝ) a a) → β ≠ 0 → 0 < l β) ∧ x = l b}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem phiC_eq_sInf (cj : E → E) {Z : Type} [AddCommGroup Z] [Module (𝓞 E) Z] (b : ModuliIntegralCharts.SymB cj Z) :
    ModuliIntegralCharts.phiC cj b = sInf (phiSet cj b) := rfl

/- English proof (translation)
Introduce and unpack `x ⟨l, hI, hP, rfl⟩`. Use `⟨l.comp (pullS cj e), fun β hβ => hI _ fun a c => ?_, fun β hβ hne => hP _ (fun a => ?_) ?_, rfl⟩` and prove the remaining obligations. Take `⟨z, hz⟩` from `hβ (e a) (e c); exact ⟨z, by simpa using hz⟩`. Simplify using `using hβ (e a)`. Introduce `h0`.

Apply `hne` to reduce the goal to its premises. Establish `h1` using `congrArg (pullS cj e.symm) h0`. Rewrite `h1` using `[pullS_symm, map_zero]`. Conclude with `h1`.
-/
theorem phiSet_pull_sub (cj : E → E) (e : Y ≃ₗ[𝓞 E] Y') (b : ModuliIntegralCharts.SymB cj Y') :
    phiSet cj (pullS cj e b) ⊆ phiSet cj b := by
  rintro x ⟨l, hI, hP, rfl⟩
  refine ⟨l.comp (pullS cj e), fun β hβ => hI _ fun a c => ?_, fun β hβ hne => hP _ (fun a => ?_) ?_, rfl⟩
  · obtain ⟨z, hz⟩ := hβ (e a) (e c); exact ⟨z, by simpa using hz⟩
  · simpa using hβ (e a)
  · intro h0; apply hne
    have h1 := congrArg (pullS cj e.symm) h0
    rw [pullS_symm, map_zero] at h1; exact h1

/- English proof (translation)
Rewrite using `[phiC_eq_sInf, phiC_eq_sInf]`. Use `congr 1`. Use `(phiSet_pull_sub cj e b).antisymm ?_` and prove the remaining obligations. Establish `h` using `phiSet_pull_sub cj e.symm (pullS cj e b)`. Rewrite `h` using `[pullS_symm]`. Then use the resulting hypothesis.
-/
theorem phiC_pull (cj : E → E) (e : Y ≃ₗ[𝓞 E] Y') (b : ModuliIntegralCharts.SymB cj Y') :
    ModuliIntegralCharts.phiC cj (pullS cj e b) = ModuliIntegralCharts.phiC cj b := by
  rw [phiC_eq_sInf, phiC_eq_sInf]; congr 1
  refine (phiSet_pull_sub cj e b).antisymm ?_
  have h := phiSet_pull_sub cj e.symm (pullS cj e b)
  rwa [pullS_symm] at h

end Pull

namespace LocView

variable {D : D7} {r j p : ℕ} (L : ModuliIntegralCharts.Loc D r j p) {Z : L.Mdl} (y : L.Pt Z) {Y' : Type} [AddCommGroup Y']
  [Module (𝓞 D.host.E) Y']

/- English proof (translation)
The claim follows from `e.toAddEquiv.toIntLinearEquiv.finrank_eq`.
-/
theorem latticeRank_eq_finrank_of_linearEquiv (e : L.Ylat y ≃ₗ[𝓞 D.host.E] Y') : L.dP y = Module.finrank ℤ Y' :=
  e.toAddEquiv.toIntLinearEquiv.finrank_eq

/- English proof (translation)
The claim follows from `e.toEquiv.subsingleton_congr`.
-/
theorem good_of (e : L.Ylat y ≃ₗ[𝓞 D.host.E] Y') : L.good y ↔ Subsingleton Y' :=
  e.toEquiv.subsingleton_congr

/- English proof (translation)
Establish `hS : L.beS y = pullS _ e bA`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `LinearMap.ext₂` to reduce the goal to its premises. Introduce `a b`. Use `show L.be y a b = _`.

Rewrite using `[pullS_apply, h]`. Use `show ModuliIntegralCharts.phiC _ (L.beS y) = _`. Rewrite using `[hS, phiC_pull]`.
-/
theorem phiCy_of (e : L.Ylat y ≃ₗ[𝓞 D.host.E] Y') (bA : ModuliIntegralCharts.SymB (fun x : D.host.E => D.host.conj x) Y')
    (h : ∀ a b, (bA : Y' →ₗ[ℤ] Y' →ₗ[ℤ] ℝ) (e a) (e b) = L.be y a b) :
    L.phiCy y = ModuliIntegralCharts.phiC (fun x : D.host.E => D.host.conj x) bA := by
  have hS : L.beS y = pullS _ e bA := by
    apply Subtype.ext; apply LinearMap.ext₂; intro a b
    show L.be y a b = _
    rw [pullS_apply, h]
  show ModuliIntegralCharts.phiC _ (L.beS y) = _
  rw [hS, phiC_pull]

end LocView

namespace In66

variable {D : D7} {Q : Par D} (G : In66 Q)

/- English proof (translation)
Establish `h` using `hL j hj hm la z hz η hr A`. Conclude with `h.elim fun e _ => LocView.latticeRank_eq_finrank_of_linearEquiv _ η e`.
-/
theorem dP_eq (hL : G.PinLat) {j : ℕ} (hj : 1 ≤ j) (hm : j < D.R.m) {la : IsDedekindDomain.HeightOneSpectrum (𝓞 Q.c.F)}
    {z : PointsOfFlagModel.Pt (G.Tw j (WeightAlgebra.resCh la)) .yy} (hz : G.IsAlgPt j la z) {η} (hr : G.rel j (WeightAlgebra.resCh la) η z)
    (A : DatAt ((G.Tw j (WeightAlgebra.resCh la)).Y z.1) z.2.2.1) :
    (G.P.loc (G.dat j) (WeightAlgebra.resCh la)).dP η = Module.finrank ℤ A.Ylat := by
  have h := hL j hj hm la z hz η hr A
  exact h.elim fun e _ => LocView.latticeRank_eq_finrank_of_linearEquiv _ η e

/- English proof (translation)
Establish `h` using `hL j hj hm la z hz η hr A`. Conclude with `h.elim fun e _ => LocView.good_of _ η e`.
-/
theorem good_iff (hL : G.PinLat) {j : ℕ} (hj : 1 ≤ j) (hm : j < D.R.m) {la : IsDedekindDomain.HeightOneSpectrum (𝓞 Q.c.F)}
    {z : PointsOfFlagModel.Pt (G.Tw j (WeightAlgebra.resCh la)) .yy} (hz : G.IsAlgPt j la z) {η} (hr : G.rel j (WeightAlgebra.resCh la) η z)
    (A : DatAt ((G.Tw j (WeightAlgebra.resCh la)).Y z.1) z.2.2.1) :
    (G.P.loc (G.dat j) (WeightAlgebra.resCh la)).good η ↔ Subsingleton A.Ylat := by
  have h := hL j hj hm la z hz η hr A
  exact h.elim fun e _ => LocView.good_of _ η e

/- English proof (translation)
Establish `h` using `hL j hj hm la z hz η hr A`. Conclude with `h.elim fun e he => LocView.phiCy_of _ η e bA fun a b => (hb _ _).trans (he a b)`.
-/
theorem phiCy_eq (hL : G.PinLat) {j : ℕ} (hj : 1 ≤ j) (hm : j < D.R.m) {la : IsDedekindDomain.HeightOneSpectrum (𝓞 Q.c.F)}
    {z : PointsOfFlagModel.Pt (G.Tw j (WeightAlgebra.resCh la)) .yy} (hz : G.IsAlgPt j la z) {η} (hr : G.rel j (WeightAlgebra.resCh la) η z)
    (A : DatAt ((G.Tw j (WeightAlgebra.resCh la)).Y z.1) z.2.2.1)
    (bA : ModuliIntegralCharts.SymB (fun x : D.host.E => D.host.conj x) A.Ylat)
    (hb : ∀ a b, (bA : A.Ylat →ₗ[ℤ] A.Ylat →ₗ[ℤ] ℝ) a b = A.beta a b) :
    (G.P.loc (G.dat j) (WeightAlgebra.resCh la)).phiCy η = ModuliIntegralCharts.phiC (fun x : D.host.E => D.host.conj x) bA := by
  have h := hL j hj hm la z hz η hr A
  exact h.elim fun e he => LocView.phiCy_of _ η e bA fun a b => (hb _ _).trans (he a b)

end In66

end Formalism.L2.Pj
