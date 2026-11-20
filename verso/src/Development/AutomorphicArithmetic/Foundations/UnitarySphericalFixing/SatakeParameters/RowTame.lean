import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingHomExtAdicCompletion
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.GoodLem
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsSplitPlace

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial
namespace GlobalTheory.RowPar
section Sat
open Formalism.UG GlobalTheory.SatInd
end Sat
section Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.SmGL GlobalTheory.LocLanglands

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation. A detailed English derivation is pending.
-/
theorem tame_locRec_m {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (hL : GlobalTheory.Published.LocalLanglandsGL) (h : IsPlaceOver A w) {n : ℕ}
    (τ : IrrRep (GL (Fin n) (w.adicCompletion E)))
    (hf : GlobalTheory.PRep.fixed τ.ρ (GlobalTheory.SplitWeil.KOne (w.adicCompletion E) (Fin n)) ≠ ⊥)
    (hq : UpperTheory.One.M.IsQg (w.adicCompletion E)) :
    (GlobalTheory.CuspRep.ParLaws.locRec hL h (cls τ)).tame := by
  obtain ⟨_, _, _, -, H⟩ := GlobalTheory.CuspRep.ParLaws.isRec_locRec hL h
  have hx : GlobalTheory.PRep.fixed (cls τ).rep (GlobalTheory.SplitWeil.KOne (w.adicCompletion E) (Fin (cls τ).1)) ≠ ⊥ :=
    GlobalTheory.LocLanglands.fixed_ne_bot_of_equiv (IrrRep.nonempty_equiv_rep τ).some.symm hf
  obtain ⟨m, b, hb, hw⟩ := haveI := UpperTheory.One.M.charZero_compl w; UpperTheory.One.M.Old.depth H _ (UpperTheory.One.M.good_of_fixed hq _ hx) hx
  rw [← hb, GlobalTheory.WeilDeligne.WD.tame_mk]
  intro g hg
  refine hw g ⟨GlobalTheory.WeilDeligne.Wild_le_Ine hg, fun x hx0 => ?_⟩
  have h1 := hg x hx0
  have e : ((g : G E Ω) x - x) = ((g : G E Ω) x / x - 1) * x := by field_simp
  rw [e, map_mul]
  have h2 : (0 : _) < A.valuation x := by
    rw [pos_iff_ne_zero]; exact (Valuation.ne_zero_iff _).2 hx0
  calc A.valuation ((g : G E Ω) x / x - 1) * A.valuation x < 1 * A.valuation x := by
        exact mul_lt_mul_of_pos_right h1 h2
    _ = A.valuation x := one_mul _

end Loc
end GlobalTheory.RowPar
end
end

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial
namespace GlobalTheory.RowPar
section Sat
open Formalism.UG GlobalTheory.SatInd
end Sat
section Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.SmGL GlobalTheory.LocLanglands
variable (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem parOf_tame_m (σ : D.what₂.FT) (s : SplitPlace D.host.E) (τ : IrrRep (GL (Fin D.R.r) (s.w.adicCompletion D.host.E)))
    (hτ : IsLocS (rep σ).S s τ)
    (hf : GlobalTheory.PRep.fixed τ.ρ (GlobalTheory.SplitWeil.KOne (s.w.adicCompletion D.host.E) (Fin D.R.r)) ≠ ⊥)
    (hq : UpperTheory.One.M.IsQg (s.w.adicCompletion D.host.E)) :
    (parOf hL D rep σ s.w).tame := by
  rw [parOf_eq hL D rep σ s τ hτ]
  exact tame_locRec_m hL _ τ hf hq

end Loc
end GlobalTheory.RowPar
end
end

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial
namespace GlobalTheory.RowPar
section Sat
open Formalism.UG GlobalTheory.SatInd
end Sat
section Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.SmGL GlobalTheory.LocLanglands
variable (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r)
end Loc
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the hypotheses and the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem exists_rowWD_rowTrue_m : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r), RowDepth D rep →
    ∃ Rw : RowWD D, RowTrue hL D rep Rw.par Rw.sat := by
  intro hL D rep hD
  refine ⟨⟨parOf hL D rep, fun σ => satOf (rep σ).S, parOf_dim hL D rep, fun σ k v => ?_⟩, ?_, ?_⟩
  · obtain ⟨s, τ, hs, hl, hf⟩ := hD σ k v
    obtain ⟨I⟩ := GlobalTheory.TypeRec.Model.nonempty_ident D
    have hq : UpperTheory.One.M.IsQg ((D.naut.plGw k v).adicCompletion D.host.E) := ⟨_, ⟨D.host.g_prime k⟩, I.i k v, I.cont k v⟩
    rw [← hs] at hq ⊢
    exact parOf_tame_m hL D rep σ s τ hl hf hq
  · intro σ s τ hτ
    exact parOf_eq hL D rep σ s τ hτ
  · intro σ v w hO Dv hα
    exact satOf_spec (rep σ).S v w hO Dv hα

end GlobalTheory.RowPar
end
end
