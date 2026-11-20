import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.InvariantDerivIntegral
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AddCurveStableOfIntegralGaugedFormalGroupLaw

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open MvPowerSeries Formalism.L2.FormalSeriesBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf

namespace GlobalTheory.CurveJet

def cob {k : Type} [CommRing k] {dd : ℕ} (F : Fin dd → PS k 2 dd) (b : PS k 1 dd) : PS k 2 dd :=
  ev (n := 2) ![addOf F (pt k dd 0) (pt k dd 1)] b - ev (n := 2) ![pt k dd 0] b - ev (n := 2) ![pt k dd 1] b

variable {C : Type} [Field C] {dd m : ℕ}

def inT (σ : Type) (f : PowerSeries C) : MvPowerSeries (Option σ) C :=
  MvPowerSeries.subst (fun _ : Unit => (X none : MvPowerSeries (Option σ) C)) f

def cvPt (γ : Fin dd → PowerSeries C) (m : ℕ) (p : Fin (m + 1) × Fin dd) :
    MvPowerSeries (Option (Fin m × Fin dd)) C :=
  Fin.cases (motive := fun _ => MvPowerSeries (Option (Fin m × Fin dd)) C) (inT _ (γ p.2))
    (fun j => X (some (j, p.2))) p.1

def jetS (γ : Fin dd → PowerSeries C) (F : PS C (m + 1) dd) : PowerSeries (PS C m dd) :=
  optionEquivLeft (Fin m × Fin dd) C (subst (cvPt γ m) F)

def jet (γ : Fin dd → PowerSeries C) (n : ℕ) (F : PS C (m + 1) dd) : PS C m dd :=
  PowerSeries.coeff n (jetS γ F)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cvPt_zero (γ : Fin dd → PowerSeries C) (i : Fin dd) : cvPt γ m (0, i) = inT _ (γ i) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cvPt_succ (γ : Fin dd → PowerSeries C) (j : Fin m) (i : Fin dd) :
    cvPt γ m (j.succ, i) = X (some (j, i)) := rfl

/- English proof (translation)
Rewrite using `[inT, rename_eq_subst]`. Both sides reduce to the same expression.
-/
theorem inT_eq_rename (σ : Type) (f : PowerSeries C) :
    inT σ f = rename (fun _ : Unit => (none : Option σ)) f := by
  rw [inT, rename_eq_subst]
  rfl

/- English proof (translation)
Rewrite using `[inT_eq_rename, constantCoeff_rename]`. Conclude with `hf`.
-/
theorem constantCoeff_inT (σ : Type) {f : PowerSeries C} (hf : PowerSeries.constantCoeff f = 0) :
    constantCoeff (inT σ f) = 0 := by
  rw [inT_eq_rename, constantCoeff_rename]
  exact hf

/- English proof (translation)
Take `⟨j, i⟩` from `p`. Proceed by induction on `j using Fin.cases with`. Consider the case `zero => rw [cvPt_zero]`. Conclude with `constantCoeff_inT _ (hγ i)`. Consider the case `succ j => rw [cvPt_succ]`.

Conclude with `constantCoeff_X _`.
-/
theorem cvPt_const {γ : Fin dd → PowerSeries C} (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0)
    (p : Fin (m + 1) × Fin dd) : constantCoeff (cvPt γ m p) = 0 := by
  obtain ⟨j, i⟩ := p
  induction j using Fin.cases with
  | zero => rw [cvPt_zero]; exact constantCoeff_inT _ (hγ i)
  | succ j => rw [cvPt_succ]; exact constantCoeff_X _

/- English proof (translation)
Use extensionality with `n μ`. Rewrite using `[coeff_coeff_optionEquivLeft, PowerSeries.coeff_map, coeff_C, inT_eq_rename]`. Use `split_ifs with hμ`. Substitute `hμ` using the available equality. Set `e : Unit ↪ Option σ` to `⟨fun _ => none, fun _ _ _ => rfl⟩`.

Establish `he : Finsupp.optionElim n (0 : σ →₀ ℕ) = Finsupp.embDomain e (Finsupp.single () n)`. Rewrite using `[Finsupp.embDomain_single, Finsupp.optionElim_zero]`. Both sides reduce to the same expression. Rewrite using `[he]`. Conclude with `coeff_embDomain_rename e f (Finsupp.single () n)`.

Apply `coeff_rename_eq_zero` to reduce the goal to its premises. Introduce and unpack `⟨y, hy⟩`. Apply `hμ` to reduce the goal to its premises. Use extensionality with `s`. Establish `h1 : Finsupp.mapDomain (fun _ : Unit => (none : Option σ)) y (some s) = 0` using `Finsupp.mapDomain_of_notMem_range _ _ (by simp)`.

Rewrite `h1` using `[hy, Finsupp.optionElim_apply_some]`. Simplify using `using h1`.
-/
theorem optionEquivLeft_inT (σ : Type) (f : PowerSeries C) :
    optionEquivLeft σ C (inT σ f) = PowerSeries.map (MvPowerSeries.C : C →+* MvPowerSeries σ C) f := by
  classical
  ext n μ
  rw [coeff_coeff_optionEquivLeft, PowerSeries.coeff_map, coeff_C, inT_eq_rename]
  split_ifs with hμ
  · subst hμ
    let e : Unit ↪ Option σ := ⟨fun _ => none, fun _ _ _ => rfl⟩
    have he : Finsupp.optionElim n (0 : σ →₀ ℕ) = Finsupp.embDomain e (Finsupp.single () n) := by
      rw [Finsupp.embDomain_single, Finsupp.optionElim_zero]
      rfl
    rw [he]
    exact coeff_embDomain_rename e f (Finsupp.single () n)
  · apply coeff_rename_eq_zero
    rintro ⟨y, hy⟩
    apply hμ
    ext s
    have h1 : Finsupp.mapDomain (fun _ : Unit => (none : Option σ)) y (some s) = 0 :=
      Finsupp.mapDomain_of_notMem_range _ _ (by simp)
    rw [hy, Finsupp.optionElim_apply_some] at h1
    simpa using h1

/- English proof (translation)
Use extensionality with `n μ`. Rewrite using `[coeff_coeff_optionEquivLeft, PowerSeries.coeff_C]`. Use `split_ifs with hn`. Substitute `hn` using the available equality. Establish `he : Finsupp.optionElim 0 μ = Finsupp.embDomain (Function.Embedding.some) μ`.

Use extensionality with `t`. Apply the tactic sequence `cases t <;> simp`. Rewrite using `[he]`. Conclude with `coeff_embDomain_rename _ f μ`. Rewrite using `[map_zero]`.

Apply `coeff_rename_eq_zero` to reduce the goal to its premises. Introduce and unpack `⟨y, hy⟩`. Apply `hn` to reduce the goal to its premises. Establish `h1 : Finsupp.mapDomain (some : σ → Option σ) y none = 0` using `Finsupp.mapDomain_of_notMem_range _ _ (by simp)`. Rewrite `h1` using `[hy, Finsupp.optionElim_apply_none]`.

Conclude with `h1`.
-/
theorem optionEquivLeft_rename_some {σ : Type} [Finite σ] (f : MvPowerSeries σ C) :
    optionEquivLeft σ C (rename (some : σ → Option σ) f) = PowerSeries.C f := by
  ext n μ
  rw [coeff_coeff_optionEquivLeft, PowerSeries.coeff_C]
  split_ifs with hn
  · subst hn
    have he : Finsupp.optionElim 0 μ = Finsupp.embDomain (Function.Embedding.some) μ := by
      ext t
      cases t <;> simp
    rw [he]
    exact coeff_embDomain_rename _ f μ
  · rw [map_zero]
    apply coeff_rename_eq_zero
    rintro ⟨y, hy⟩
    apply hn
    have h1 : Finsupp.mapDomain (some : σ → Option σ) y none = 0 :=
      Finsupp.mapDomain_of_notMem_range _ _ (by simp)
    rw [hy, Finsupp.optionElim_apply_none] at h1
    exact h1

/- English proof (translation)
Use extensionality with `μ`. Rewrite using `[coeff_pderiv, coeff_coeff_optionEquivLeft, coeff_coeff_optionEquivLeft, coeff_pderiv]`. Establish `key : Finsupp.optionElim n (μ + Finsupp.single s 1) = Finsupp.optionElim n μ + Finsupp.single (some s) 1`. Use extensionality with `t`. Apply the tactic sequence `cases t <;> simp [Finsupp.single_apply]`.

Rewrite using `[key, Finsupp.optionElim_apply_some]`.
-/
theorem pderiv_coeff_optionEquivLeft {σ : Type} (f : MvPowerSeries (Option σ) C) (n : ℕ) (s : σ) :
    pderiv C s (PowerSeries.coeff n (optionEquivLeft σ C f)) =
      PowerSeries.coeff n (optionEquivLeft σ C (pderiv C (some s) f)) := by
  classical
  ext μ
  rw [coeff_pderiv, coeff_coeff_optionEquivLeft, coeff_coeff_optionEquivLeft, coeff_pderiv]
  have key : Finsupp.optionElim n (μ + Finsupp.single s 1) =
      Finsupp.optionElim n μ + Finsupp.single (some s) 1 := by
    ext t
    cases t <;> simp [Finsupp.single_apply]
  rw [key, Finsupp.optionElim_apply_some]

def jetHom {γ : Fin dd → PowerSeries C} (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0) (m : ℕ) :
    PS C (m + 1) dd →ₐ[C] PowerSeries (PS C m dd) :=
  (optionEquivLeft (Fin m × Fin dd) C).toAlgHom.comp
    (substAlgHom (hasSubst_of_constantCoeff_zero (cvPt_const (m := m) hγ)))

end GlobalTheory.CurveJet
