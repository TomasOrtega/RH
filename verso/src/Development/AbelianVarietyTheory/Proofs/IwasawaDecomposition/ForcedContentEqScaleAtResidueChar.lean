import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimes
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.Bl

/- English proof (translation)
Establish `hg : (p ∈ L.gTypes) ↔ ∃ i, p = D.host.g i`. Simplify using `only [Formalism.BasicNotions.SizeData₂.gTypes, Finset.mem_insert, Finset.mem_singleton]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `(h | h)`. Conclude with `⟨0, h⟩`.

Conclude with `⟨1, h⟩`. Apply the tactic sequence `rintro ⟨i, rfl⟩ fin_cases i <;> simp`. Unfold `FvalP FK`. Distinguish the cases in `h : ∃ i, p = D.host.g i`. Rewrite using `[if_pos (hg.mpr h), if_pos h]`.

Rewrite using `[if_neg (fun h' => h (hg.mp h')), if_neg h]`.
-/
theorem fvalP_eq_FK (D : D7) (L : SizeData₂ D) (j p : ℕ) :
    FvalP L j p = FK L.sc D j p := by
  have hg : (p ∈ L.gTypes) ↔ ∃ i, p = D.host.g i := by
    simp only [Formalism.BasicNotions.SizeData₂.gTypes, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (h | h)
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
  unfold FvalP FK
  by_cases h : ∃ i, p = D.host.g i
  · rw [if_pos (hg.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (hg.mp h')), if_neg h]

/- English proof (translation)
Introduce `D L j v`. Conclude with `fvalP_eq_FK D L j _`.
-/
theorem Fval_eq_FK : ∀ (D : D7) (L : SizeData₂ D) (j : ℕ) (v : D.what₂.places.Pl),
    Fval L j v = FK L.sc D j (D.what₂.places.resChar v) := by
  intro D L j v
  exact fvalP_eq_FK D L j _

/- English proof (translation)
Establish `hp : (D.what₂.places.resChar w).Prime` using `D.what₂.places.resChar_prime w`. Establish `hmem` using `Formalism.L2.Col.att_resChar_mem D.what₂.places D.plEq D.val_eq w`. Use `haveI : Nontrivial (𝓞 D.what₂.LL ⧸ (D.plEq w).asIdeal) := Ideal.Quotient.nontrivial_iff.2 (D.plEq w).isPrime.ne_top`. Establish `h0 : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL ⧸ (D.plEq w).asIdeal) = 0`. Use `(Ideal.Quotient.eq_zero_iff_mem).mpr hmem` as an intermediate fact.

Simplify using `using this`. Establish `hdvd : ringChar (𝓞 D.what₂.LL ⧸ (D.plEq w).asIdeal) ∣ D.what₂.places.resChar w` using `ringChar.dvd h0`. Break down `hp.eq_one_or_self_of_dvd _ hdvd with h1 | h1` into its components or cases. Conclude with `absurd h1 CharP.ringChar_ne_one`. Conclude with `h1.symm`.
-/
theorem resChar_eq_plc (D : D7) (w : D.what₂.places.Pl) :
    D.what₂.places.resChar w = Formalism.EigenvalueLevelCeiling.plc (D.plEq w) := by
  have hp : (D.what₂.places.resChar w).Prime := D.what₂.places.resChar_prime w
  have hmem := Formalism.L2.Col.att_resChar_mem D.what₂.places D.plEq D.val_eq w
  haveI : Nontrivial (𝓞 D.what₂.LL ⧸ (D.plEq w).asIdeal) :=
    Ideal.Quotient.nontrivial_iff.2 (D.plEq w).isPrime.ne_top
  have h0 : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL ⧸ (D.plEq w).asIdeal) = 0 := by
    have := (Ideal.Quotient.eq_zero_iff_mem).mpr hmem
    simpa using this
  have hdvd : ringChar (𝓞 D.what₂.LL ⧸ (D.plEq w).asIdeal) ∣ D.what₂.places.resChar w :=
    ringChar.dvd h0
  rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | h1
  · exact absurd h1 CharP.ringChar_ne_one
  · exact h1.symm

/- English proof (translation)
Establish `h` using `Formalism.L2.DIV.ofRecord_Fval D L Del h0 hK (j := (j : ℕ) + 1) (Nat.le_add_left 1 _) (Nat.succ_le_of_lt j.isLt) (D.plEq.symm y)`. Rewrite `h` using `[Fval_eq_FK]`. Establish `hc : D.what₂.places.resChar (D.plEq.symm y) = Formalism.EigenvalueLevelCeiling.plc y`. Rewrite using `[resChar_eq_plc, Equiv.apply_symm_apply]`. Unfold `F0K Formalism.L2.DIV.NumDatum.Fj`.

Rewrite using `[h, hc]`.
-/
theorem ofRecord_Fj_succ (D : D7) (L : SizeData₂ D) (Del h0 : ℕ) (hK : DV.KapDef D)
    (y : HeightOneSpectrum (𝓞 D.what₂.LL)) (j : Fin D.R.m) :
    (Formalism.L2.DIV.ofRecord D L Del h0).Fj ((j : ℕ) + 1) y = F0K L.sc D y j := by
  have h := Formalism.L2.DIV.ofRecord_Fval D L Del h0 hK (j := (j : ℕ) + 1) (Nat.le_add_left 1 _)
    (Nat.succ_le_of_lt j.isLt) (D.plEq.symm y)
  rw [Fval_eq_FK] at h
  have hc : D.what₂.places.resChar (D.plEq.symm y) = Formalism.EigenvalueLevelCeiling.plc y := by
    rw [resChar_eq_plc, Equiv.apply_symm_apply]
  unfold F0K Formalism.L2.DIV.NumDatum.Fj
  rw [h, hc]

end GlobalTheory.Mem.Top.Bl
