import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ConclusionAbsPow

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.Published.CharAboveModel

namespace GlobalTheory.ExpFrame.Inhab

variable (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]

/- English proof (translation)
Establish `hc : Continuous (cyc E Ω l)` using `(Continuous.units_map ((algebraMap ℚ_[l] (PadicAlgCl l)).comp PadicInt.Coe.ringHom).toMonoidHom ((continuous_algebraMap ℚ_[l] (PadicAlgCl l)).comp (continuous_subtype_val : Continuous fun z : ℤ_[l] => (z : ℚ_[l])))).comp (continuous_cycZ E Ω l)`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `h1 : Continuous (cyc E Ω l ^ m)` using `hc.pow m`. Use `(Continuous.units_map _ ?_).comp h1` and prove the remaining obligations. Conclude with `continuous_pi fun i => continuous_pi fun j => by fin_cases i; fin_cases j`.

Simplify using `using continuous_id'`. Introduce and unpack `P AI ⟨T⟩ w A - O _ _ _ Bw -`. Take `⟨hc, hm⟩` from `GlobalTheory.HTW.Rec.Model.cycPowSum_crys_mult T Bw.Kw Bw.LL (fun _ : Fin 1 => -(m : ℤ))`. Establish `hd` using `(GlobalTheory.Per.CrisDR.isDR_of_isCrys l P AI T Bw.Kw Bw.LL _ _ hc).1`. Establish `hM : IsModel Bw ((rk1 (cyc E Ω l ^ m)).comp (Dec (F` using `E) A).subtype) Bw.LL (powModel P Bw m) := by`.

Use `⟨le_rfl, MonoidHom.ext fun g => ?_⟩` and prove the remaining obligations. Establish `e` using `GlobalTheory.Survey.CrystallineCharacterRatio.chi_eq_cyc P Bw.j (g : G E Ω) (Bw.e g : GQ l) (Bw.e_comm g)`. Use extensionality with `a c`. Use `fin_cases a`. Use `fin_cases c`.

Simplify using `[powModel, rk1, mapRep, cycLL, P.PD_χ, e, cyc_eq_map_cycZ, Matrix.diagonal_pow]`. Rewrite using `[Matrix.diagonal_map (map_zero _), Matrix.diagonal_pow, Matrix.diagonal_apply_eq, Pi.pow_apply]`. Both sides reduce to the same expression. Establish `hC : Bw.IsCrysE P Bw.LL (powModel P Bw m)`. Rewrite using `[LocBridge.IsCrysE, repE_powModel]`.

Conclude with `hc`. Establish `hD : Bw.IsdRE P Bw.LL (powModel P Bw m)`. Rewrite using `[LocBridge.IsdRE, repE_powModel]`. Establish `h2 : Module.finrank ↥Bw.LL.1 ↥(Formalism.WeaklyAdmissibleFiltrations.DdR (P.PD Bw.Kw) (matRep (GlobalTheory.HTW.Rec.Model.cycPowSum P Bw.Kw Bw.LL (fun _ : Fin 1 => -(m : ℤ))))) = Module.finrank ℚ_[l] ↥Bw.Kw.1 * Module.finrank ↥Bw.LL.1 (Fin 1 → ↥Bw.LL.1)` using `hd`. Simplify using `using h2`.

Use `⟨⟨_, _, hM, hC⟩, fun τ LL' τ' hτ => ?_⟩` and prove the remaining obligations. Set `τ₂ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥Bw.LL.1` to `(LL'.1.val.comp τ').codRestrict Bw.LL.1.toSubalgebra fun x => Bw.LL_split _ x`. Use `⟨Bw.LL, _, hM, hD, τ₂, fun x => hτ x, fun n => ?_⟩` and prove the remaining obligations. Rewrite using `[LocBridge.multE, repE_powModel, hm τ₂ n]`. Simplify using `only [List.ofFn_succ, List.ofFn_zero, Multiset.count_singleton, List.count_cons, List.count_nil]`.

Distinguish the cases in `h : n = -(m : ℤ)`. Simplify using `[h]`. Simplify using `[h, Ne.symm h]`.
-/
theorem crysWith_cyc_pow (m : ℕ) : CrysWith (rk1 (cyc E Ω l ^ m)) fun _ => {-(m : ℤ)} := by
  have hc : Continuous (cyc E Ω l) :=
    (Continuous.units_map ((algebraMap ℚ_[l] (PadicAlgCl l)).comp PadicInt.Coe.ringHom).toMonoidHom
      ((continuous_algebraMap ℚ_[l] (PadicAlgCl l)).comp
        (continuous_subtype_val : Continuous fun z : ℤ_[l] => (z : ℚ_[l])))).comp (continuous_cycZ E Ω l)
  refine ⟨?_, ?_⟩
  · have h1 : Continuous (cyc E Ω l ^ m) := hc.pow m
    refine (Continuous.units_map _ ?_).comp h1
    exact continuous_pi fun i => continuous_pi fun j => by
      fin_cases i; fin_cases j
      simpa using continuous_id'
  rintro P AI ⟨T⟩ w A - O _ _ _ Bw -
  obtain ⟨hc, hm⟩ := GlobalTheory.HTW.Rec.Model.cycPowSum_crys_mult T Bw.Kw Bw.LL (fun _ : Fin 1 => -(m : ℤ))
  have hd := (GlobalTheory.Per.CrisDR.isDR_of_isCrys l P AI T Bw.Kw Bw.LL _ _ hc).1
  have hM : IsModel Bw ((rk1 (cyc E Ω l ^ m)).comp (Dec (F := E) A).subtype) Bw.LL (powModel P Bw m) := by
    refine ⟨le_rfl, MonoidHom.ext fun g => ?_⟩
    have e := GlobalTheory.Survey.CrystallineCharacterRatio.chi_eq_cyc P Bw.j (g : G E Ω) (Bw.e g : GQ l) (Bw.e_comm g)
    ext a c
    fin_cases a
    fin_cases c
    simp [powModel, rk1, mapRep, cycLL, P.PD_χ, e, cyc_eq_map_cycZ, Matrix.diagonal_pow]
    rw [Matrix.diagonal_map (map_zero _), Matrix.diagonal_pow, Matrix.diagonal_apply_eq, Pi.pow_apply]
    rfl
  have hC : Bw.IsCrysE P Bw.LL (powModel P Bw m) := by
    rw [LocBridge.IsCrysE, repE_powModel]; exact hc
  have hD : Bw.IsdRE P Bw.LL (powModel P Bw m) := by
    rw [LocBridge.IsdRE, repE_powModel]
    have h2 : Module.finrank ↥Bw.LL.1 ↥(Formalism.WeaklyAdmissibleFiltrations.DdR (P.PD Bw.Kw)
        (matRep (GlobalTheory.HTW.Rec.Model.cycPowSum P Bw.Kw Bw.LL (fun _ : Fin 1 => -(m : ℤ))))) =
        Module.finrank ℚ_[l] ↥Bw.Kw.1 * Module.finrank ↥Bw.LL.1 (Fin 1 → ↥Bw.LL.1) := hd
    simpa using h2
  refine ⟨⟨_, _, hM, hC⟩, fun τ LL' τ' hτ => ?_⟩
  let τ₂ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥Bw.LL.1 :=
    (LL'.1.val.comp τ').codRestrict Bw.LL.1.toSubalgebra fun x => Bw.LL_split _ x
  refine ⟨Bw.LL, _, hM, hD, τ₂, fun x => hτ x, fun n => ?_⟩
  rw [LocBridge.multE, repE_powModel, hm τ₂ n]
  simp only [List.ofFn_succ, List.ofFn_zero, Multiset.count_singleton, List.count_cons, List.count_nil]
  by_cases h : n = -(m : ℤ)
  · simp [h]
  · simp [h, Ne.symm h]

/- English proof (translation)
Use `⟨rk1 (cyc E Ω l ^ m), 0, 1, fun _ => cyc E Ω l ^ m, rfl, ?_, continuous_const, fun s => ?_, fun σ k => ?_⟩` and prove the remaining obligations. Simplify using `using crysWith_cyc_pow E Ω l m`. Simplify using `using crysWith_cyc_pow E Ω l m`. Establish `e : ((rk1 (cyc E Ω l ^ m) σ).val).charpoly = Polynomial.X - Polynomial.C (((cyc E Ω l ^ m) σ : (Qbar l)ˣ) : Qbar l)`. Rewrite using `[Matrix.charpoly, Matrix.det_fin_one, Matrix.charmatrix_apply_eq]`.

Simplify using `[rk1, Matrix.diagonal_pow]`. Rewrite using `[e]`. Simplify using `[Matrix.charpoly]`.
-/
theorem blockPair_cyc_pow (m : ℕ) : BlockPair E Ω l 1 1 (fun _ _ => -(m : ℤ)) fun _ => -(m : ℤ) := by
  refine ⟨rk1 (cyc E Ω l ^ m), 0, 1, fun _ => cyc E Ω l ^ m, rfl, ?_, continuous_const, fun s => ?_, fun σ k => ?_⟩
  · simpa using crysWith_cyc_pow E Ω l m
  · simpa using crysWith_cyc_pow E Ω l m
  · have e : ((rk1 (cyc E Ω l ^ m) σ).val).charpoly = Polynomial.X - Polynomial.C (((cyc E Ω l ^ m) σ : (Qbar l)ˣ) : Qbar l) := by
      rw [Matrix.charpoly, Matrix.det_fin_one, Matrix.charmatrix_apply_eq]
      simp [rk1, Matrix.diagonal_pow]
    rw [e]
    simp [Matrix.charpoly]

end GlobalTheory.ExpFrame.Inhab

end
