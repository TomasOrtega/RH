import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsHaarMeasureSUJ
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HarishChandraPermuteStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SignKeyTrueLtFalse
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SqIntIrrPerm
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryGroupStructuresPermConjInvariant
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace

namespace GlobalTheory.DSSU

/- English proof (translation)
Introduce `n hF`. Unfold `ClassF at hF`. Use `choose F hP hC hE using hF`. Take `⟨std, t, ht, hst, hren⟩` from `GlobalTheory.SignRenumber.block_renumbering n`. Establish `e1a : ∀ (ε : Fin n → Bool) (x : Fin n), std ε (t ε x) = ε x` using `fun ε x => congrFun (ht ε).1 x`.

Establish `hmono : ∀ (ε : Fin n → Bool) (a b : Fin n), a < b → std ε (t ε a) = std ε (t ε b) → t ε a < t ε b`. Introduce `ε a b hab h`. Rewrite `h` using `[e1a, e1a]`. Conclude with `(ht ε).2 a b hab h`. Use `⟨fun ε lam => (F (std ε)).H (lam ∘ (t ε).symm), fun ε lam => inferInstance, fun ε lam => inferInstance, fun ε lam g => (F (std ε)).π (lam ∘ (t ε).symm) (g.submatrix (t ε).symm (t ε).symm), ?_, ?_⟩` and prove the remaining obligations.

Introduce `ε lam hlam`. Establish `hpar : IsParU (lam ∘ (t ε).symm)` using `⟨hlam.1.injective.comp (t ε).symm.injective, fun a => hlam.2 _⟩`. Establish `e2 : (lam ∘ (t ε).symm) ∘ (t ε) = lam` using `by funext a; simp`. Establish `h1` using `GlobalTheory.T.harish_chandra_permute n (std ε) _ ((F (std ε)).π (lam ∘ (t ε).symm)) (lam ∘ (t ε).symm) (t ε) (hmono ε) (by rw [e2]; exact hlam.1) (hP _ _ hpar)`. Rewrite `h1` using `[(ht ε).1, e2]`.

Conclude with `h1`. Introduce `ε H' _ _ σ' hσ`. Set `σ₀ : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')` to `fun g => σ' (g.submatrix (t ε) (t ε))`. Establish `hσ₀ : IsSqIntIrr (std ε) σ₀`. Rewrite using `[(GlobalTheory.DSId.PermK.permKType n (std ε) (t ε) H' σ₀ (hmono ε)).2.2.2.1]`.

Establish `e3 : (fun g : Matrix (Fin n) (Fin n) ℂ => σ₀ (g.submatrix (t ε).symm (t ε).symm)) = σ'`. Use function extensionality and compare the values at `g`. Simplify using `only [σ₀, Matrix.submatrix_submatrix, Equiv.symm_comp_self, Matrix.submatrix_id_id]`. Rewrite using `[(ht ε).1, e3]`. Conclude with `hσ`.

Take `⟨lam₀, hpar₀, T, hT⟩` from `hE (std ε) H' σ₀ hσ₀`. Take `⟨w, s, hw, hanti, hs⟩` from `hren ε (lam₀ ∘ t ε) (hpar₀.1.comp (t ε).injective)`. Use `⟨s, ((lam₀ ∘ t ε) ∘ w) ∘ s, ⟨hanti, fun a => hpar₀.2 _⟩, hs, ?_⟩` and prove the remaining obligations. Establish `hstd : std (ε ∘ s) = std ε` using `(hst ε s).1`. Establish `htt : t (ε ∘ s) = s.trans (t ε)` using `Equiv.ext ((hst ε s).2 hs)`.

Use `show UEquiv (ε ∘ s) (fun g => σ' (g.submatrix s.symm s.symm)) (fun g => (F (std (ε ∘ s))).π ((((lam₀ ∘ t ε) ∘ w) ∘ s) ∘ (t (ε ∘ s)).symm) (g.submatrix (t (ε ∘ s)).symm (t (ε ∘ s)).symm))`. Rewrite using `[htt, hstd]`. Establish `hconj : ConjK (std ε) lam₀ ((((lam₀ ∘ t ε) ∘ w) ∘ s) ∘ (s.trans (t ε)).symm)`. Use `⟨(t ε).symm.trans (w.trans (t ε)), ?_, ?_⟩` and prove the remaining obligations. Introduce `a`.

Simplify using `only [Equiv.trans_apply]`. Rewrite using `[e1a, hw, ← e1a ε ((t ε).symm a), Equiv.apply_symm_apply]`. Use function extensionality and compare the values at `a`. Simplify using `[Equiv.symm_trans_apply]`. Take `⟨T2, hT2⟩` from `hC (std ε) lam₀ _ hpar₀ hconj`.

Use `⟨T.trans T2, ?_⟩` and prove the remaining obligations. Introduce `g hg v`. Establish `hcomp : std ε ∘ (s.trans (t ε)) = ε ∘ s`. Use function extensionality and compare the values at `a`. Simplify using `[Equiv.trans_apply, e1a]`.

Establish `hh : g.submatrix (s.trans (t ε)).symm (s.trans (t ε)).symm ∈ UJset (std ε)` using `(((GlobalTheory.Dec.PermGroup.permGroup n (std ε) (s.trans (t ε))).1 g).1).mp (by rw [hcomp]; exact hg)`. Establish `hσh : σ₀ (g.submatrix (s.trans (t ε)).symm (s.trans (t ε)).symm) = σ' (g.submatrix s.symm s.symm)` using `by show σ' ((g.submatrix _ _).submatrix (t ε) (t ε)) = _`. Rewrite using `[Matrix.submatrix_submatrix]`. Apply the tactic sequence `congr 2 <;> funext a <;> simp [Equiv.symm_trans_apply]`. Simplify using `only [LinearIsometryEquiv.trans_apply]`.

Rewrite using `[← hσh, hT _ hh, hT2 _ hh]`.
-/
theorem classU_of_classF : ∀ n : ℕ, (∀ ε : Fin n → Bool, ClassF ε) → ClassU n := by
  intro n hF
  unfold ClassF at hF
  choose F hP hC hE using hF
  obtain ⟨std, t, ht, hst, hren⟩ := GlobalTheory.SignRenumber.block_renumbering n
  have e1a : ∀ (ε : Fin n → Bool) (x : Fin n), std ε (t ε x) = ε x := fun ε x => congrFun (ht ε).1 x
  have hmono : ∀ (ε : Fin n → Bool) (a b : Fin n), a < b → std ε (t ε a) = std ε (t ε b) → t ε a < t ε b := by
    intro ε a b hab h
    rw [e1a, e1a] at h
    exact (ht ε).2 a b hab h
  refine ⟨fun ε lam => (F (std ε)).H (lam ∘ (t ε).symm), fun ε lam => inferInstance, fun ε lam => inferInstance,
    fun ε lam g => (F (std ε)).π (lam ∘ (t ε).symm) (g.submatrix (t ε).symm (t ε).symm), ?_, ?_⟩
  · intro ε lam hlam
    have hpar : IsParU (lam ∘ (t ε).symm) :=
      ⟨hlam.1.injective.comp (t ε).symm.injective, fun a => hlam.2 _⟩
    have e2 : (lam ∘ (t ε).symm) ∘ (t ε) = lam := by funext a; simp
    have h1 := GlobalTheory.T.harish_chandra_permute n (std ε) _ ((F (std ε)).π (lam ∘ (t ε).symm)) (lam ∘ (t ε).symm) (t ε)
      (hmono ε) (by rw [e2]; exact hlam.1) (hP _ _ hpar)
    rw [(ht ε).1, e2] at h1
    exact h1
  · intro ε H' _ _ σ' hσ
    let σ₀ : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H') := fun g => σ' (g.submatrix (t ε) (t ε))
    have hσ₀ : IsSqIntIrr (std ε) σ₀ := by
      rw [(GlobalTheory.DSId.PermK.permKType n (std ε) (t ε) H' σ₀ (hmono ε)).2.2.2.1]
      have e3 : (fun g : Matrix (Fin n) (Fin n) ℂ => σ₀ (g.submatrix (t ε).symm (t ε).symm)) = σ' := by
        funext g
        simp only [σ₀, Matrix.submatrix_submatrix, Equiv.symm_comp_self, Matrix.submatrix_id_id]
      rw [(ht ε).1, e3]
      exact hσ
    obtain ⟨lam₀, hpar₀, T, hT⟩ := hE (std ε) H' σ₀ hσ₀
    obtain ⟨w, s, hw, hanti, hs⟩ := hren ε (lam₀ ∘ t ε) (hpar₀.1.comp (t ε).injective)
    refine ⟨s, ((lam₀ ∘ t ε) ∘ w) ∘ s, ⟨hanti, fun a => hpar₀.2 _⟩, hs, ?_⟩
    have hstd : std (ε ∘ s) = std ε := (hst ε s).1
    have htt : t (ε ∘ s) = s.trans (t ε) := Equiv.ext ((hst ε s).2 hs)
    show UEquiv (ε ∘ s) (fun g => σ' (g.submatrix s.symm s.symm))
      (fun g => (F (std (ε ∘ s))).π ((((lam₀ ∘ t ε) ∘ w) ∘ s) ∘ (t (ε ∘ s)).symm)
        (g.submatrix (t (ε ∘ s)).symm (t (ε ∘ s)).symm))
    rw [htt, hstd]
    have hconj : ConjK (std ε) lam₀ ((((lam₀ ∘ t ε) ∘ w) ∘ s) ∘ (s.trans (t ε)).symm) := by
      refine ⟨(t ε).symm.trans (w.trans (t ε)), ?_, ?_⟩
      · intro a
        simp only [Equiv.trans_apply]
        rw [e1a, hw, ← e1a ε ((t ε).symm a), Equiv.apply_symm_apply]
      · funext a
        simp [Equiv.symm_trans_apply]
    obtain ⟨T2, hT2⟩ := hC (std ε) lam₀ _ hpar₀ hconj
    refine ⟨T.trans T2, ?_⟩
    intro g hg v
    have hcomp : std ε ∘ (s.trans (t ε)) = ε ∘ s := by
      funext a; simp [Equiv.trans_apply, e1a]
    have hh : g.submatrix (s.trans (t ε)).symm (s.trans (t ε)).symm ∈ UJset (std ε) :=
      (((GlobalTheory.Dec.PermGroup.permGroup n (std ε) (s.trans (t ε))).1 g).1).mp (by rw [hcomp]; exact hg)
    have hσh : σ₀ (g.submatrix (s.trans (t ε)).symm (s.trans (t ε)).symm) = σ' (g.submatrix s.symm s.symm) := by
      show σ' ((g.submatrix _ _).submatrix (t ε) (t ε)) = _
      rw [Matrix.submatrix_submatrix]
      congr 2 <;> funext a <;> simp [Equiv.symm_trans_apply]
    simp only [LinearIsometryEquiv.trans_apply]
    rw [← hσh, hT _ hh, hT2 _ hh]

end GlobalTheory.DSSU
