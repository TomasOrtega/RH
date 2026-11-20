import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GgNone
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesComplementUnitaryActsOnTerms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InfStabilizerSmulEqConj
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TsumTransversalEqTsumOrbitQuotientGeneral
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramePairCoordinatesTransportInnerData
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermsCorrespondStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsWtEqMulNuStatement

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.CoordSum

/- English proof (translation)
Introduce `F _ _ _ E _ _ _ _ M hM V _ _ H r k P S c R d0`. Use `hM.loc` as an intermediate fact. Use `hM.char0` as an intermediate fact. Take `⟨κ, hκ0, hκ⟩` from `GlobalTheory.T.exists_wt_eq_mul_nu' M hM H r k P S c d0`. Take `⟨-, -, hrel, -, -⟩` from `GlobalTheory.HL.CoordDatum.transport M hM H r k P S c`.

Take `⟨-, -, hex⟩` from `GlobalTheory.T.isTerm_and_om_eq_of_coord_isTermOver M hM H r k P S c`. Use `⟨κ, hκ0, fun φ hφ hφ0 => ?_⟩` and prove the remaining obligations. Establish `hmove : ∀ h ∈ S.H0, ∀ δ : S.Datum, (∃ Λ, S.IsTerm δ Λ) → ∃ Λ, S.IsTerm (h • δ) Λ`. Introduce and unpack `h hh δ ⟨Λ, hΛ⟩`. Conclude with `⟨h • Λ, (GlobalTheory.HL.ComplAct.main M.L r k S δ Λ hΛ h hh).1⟩`.

Establish `hψ0 : ∀ δ : S.Datum, (¬ ∃ Λ, S.IsTerm δ Λ) → ENNReal.ofReal (S.nu δ) * φ δ = 0`. Introduce `δ hδ`. Rewrite using `[hφ0 δ hδ, mul_zero]`. Establish `hterm : ∀ d : R.RD, ENNReal.ofReal (LocNG.Datum.wt d0 d.1) * φ (c.dat d.1) = ENNReal.ofReal κ * (ENNReal.ofReal (S.nu (c.dat d.1)) * φ (c.dat d.1))`. Introduce `d`.

Distinguish the cases in `hd : ∃ Λ, S.IsTerm (c.dat d.1) Λ`. Take `⟨Λ, hΛ⟩` from `hd`. Rewrite using `[hκ d.1 Λ hΛ, ENNReal.ofReal_mul hκ0, mul_assoc]`. Rewrite using `[hφ0 _ hd, mul_zero, mul_zero, mul_zero]`. Rewrite using `[tsum_congr hterm, ENNReal.tsum_mul_left]`.

Use `congr 1`. Set `A : Set R.RD` to `{a | ∃ Λ, S.IsTerm (c.dat a.1) Λ}`. Establish `h1 : ∑' a : A, ENNReal.ofReal (S.nu (c.dat a.1.1)) * φ (c.dat a.1.1) = ∑' d : R.RD, ENNReal.ofReal (S.nu (c.dat d.1)) * φ (c.dat d.1)`. Use `tsum_subtype_eq_of_support_subset (f := fun d : R.RD => ENNReal.ofReal (S.nu (c.dat d.1)) * φ (c.dat d.1)) ?_` and prove the remaining obligations. Introduce `a ha`.

Assume the negation of the conclusion as `hn`. Conclude with `ha (hψ0 _ hn)`. Establish `hT : ∀ g : S.H0, ∀ x : S.Datum, (∃ Λ, S.IsTerm x Λ) → ∃ Λ, S.IsTerm (g • x) Λ` using `fun g x hx => hmove g g.2 x hx`. Establish `hι : ∀ a : A, ∃ Λ, S.IsTerm (c.dat a.1.1) Λ` using `fun a => a.2`. Establish `hsurj : ∀ x : S.Datum, (∃ Λ, S.IsTerm x Λ) → ∃ a : A, ∃ g : S.H0, g • c.dat a.1.1 = x`.

Introduce `x hx`. Take `⟨Λ, hΛ⟩` from `hx`. Take `⟨d, rfl⟩` from `hex x Λ hΛ`. Take `⟨y, hyR, hy⟩` from `R.hRD.2.1 d (Set.mem_univ d)`. Take `⟨h, hh, hhy⟩` from `(hrel y d).1 hy`.

Establish `hTy : ∃ Λ, S.IsTerm (c.dat y) Λ`. Establish `h'` using `hmove h⁻¹ (S.H0.inv_mem hh) _ ⟨Λ, hΛ⟩`. Rewrite `h'` using `[← hhy, inv_smul_smul]`. Then use the resulting hypothesis. Conclude with `⟨⟨⟨y, hyR⟩, hTy⟩, ⟨h, hh⟩, hhy⟩`. Establish `hinj : ∀ a b : A, (∃ g : S.H0, g • c.dat a.1.1 = c.dat b.1.1) → a = b`.

Introduce and unpack `a b ⟨g, hg⟩`. Establish `hr : LocNG.Datum.Rel a.1.1 b.1.1` using `(hrel _ _).2 ⟨g, g.2, hg⟩`. Conclude with `Subtype.ext (Subtype.ext (R.hRD.2.2 _ a.1.2 _ b.1.2 hr))`. Establish `hinv : ∀ g : S.H0, ∀ x : S.Datum, (∃ Λ, S.IsTerm x Λ) → ENNReal.ofReal (S.nu (g • x)) * φ (g • x) = ENNReal.ofReal (S.nu x) * φ x`. Introduce and unpack `g x ⟨Λ, hΛ⟩`.

Use `show ENNReal.ofReal (S.nu ((g : S.GLV) • x)) * φ ((g : S.GLV) • x) = _`. Rewrite using `[(GlobalTheory.HL.Frames.nu_pos_and_smul M.L r k S x Λ hΛ).2 g g.2, hφ g g.2 x]`. Establish `h2` using `(GlobalTheory.tsum_transversal_eq_tsum_orbitQuotient (G := S.H0) (X := S.Datum) (A := A) (fun a => c.dat a.1.1) (fun x => ∃ Λ, S.IsTerm x Λ) hT hι hsurj hinj).2 (fun x => ENNReal.ofReal (S.nu x) * φ x) hinv`. Rewrite using `[← h1, h2]`. Use `show _ = ∑' o : MulAction.orbitRel.Quotient S.H0 S.Datum, ENNReal.ofReal (S.nu o.out) * φ o.out`.

Use `tsum_congr fun o => ?_` and prove the remaining obligations. Use `split_ifs with ho`. Both sides reduce to the same expression. Conclude with `(hψ0 _ ho).symm`.
-/
theorem tsum_reps_eq : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : Coord P S), ∀ (R : LocNG.Reps P) (d0 : LocNG.Datum P), ∃ κ : ℝ, 0 ≤ κ ∧ ∀ φ : S.Datum → ℝ≥0∞, (∀ h ∈ S.H0, ∀ δ, φ (h • δ) = φ δ) → (∀ δ, (¬ ∃ Λ, S.IsTerm δ Λ) → φ δ = 0) → (∑' d : R.RD, ENNReal.ofReal (LocNG.Datum.wt d0 d.1) * φ (c.dat d.1)) = ENNReal.ofReal κ * S.sumData φ := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P S c R d0
  have := hM.loc
  have := hM.char0
  obtain ⟨κ, hκ0, hκ⟩ := GlobalTheory.T.exists_wt_eq_mul_nu' M hM H r k P S c d0
  obtain ⟨-, -, hrel, -, -⟩ := GlobalTheory.HL.CoordDatum.transport M hM H r k P S c
  obtain ⟨-, -, hex⟩ := GlobalTheory.T.isTerm_and_om_eq_of_coord_isTermOver M hM H r k P S c
  refine ⟨κ, hκ0, fun φ hφ hφ0 => ?_⟩

  have hmove : ∀ h ∈ S.H0, ∀ δ : S.Datum, (∃ Λ, S.IsTerm δ Λ) → ∃ Λ, S.IsTerm (h • δ) Λ := by
    rintro h hh δ ⟨Λ, hΛ⟩
    exact ⟨h • Λ, (GlobalTheory.HL.ComplAct.main M.L r k S δ Λ hΛ h hh).1⟩

  have hψ0 : ∀ δ : S.Datum, (¬ ∃ Λ, S.IsTerm δ Λ) → ENNReal.ofReal (S.nu δ) * φ δ = 0 := by
    intro δ hδ
    rw [hφ0 δ hδ, mul_zero]
  have hterm : ∀ d : R.RD, ENNReal.ofReal (LocNG.Datum.wt d0 d.1) * φ (c.dat d.1) =
      ENNReal.ofReal κ * (ENNReal.ofReal (S.nu (c.dat d.1)) * φ (c.dat d.1)) := by
    intro d
    by_cases hd : ∃ Λ, S.IsTerm (c.dat d.1) Λ
    · obtain ⟨Λ, hΛ⟩ := hd
      rw [hκ d.1 Λ hΛ, ENNReal.ofReal_mul hκ0, mul_assoc]
    · rw [hφ0 _ hd, mul_zero, mul_zero, mul_zero]
  rw [tsum_congr hterm, ENNReal.tsum_mul_left]
  congr 1

  let A : Set R.RD := {a | ∃ Λ, S.IsTerm (c.dat a.1) Λ}
  have h1 : ∑' a : A, ENNReal.ofReal (S.nu (c.dat a.1.1)) * φ (c.dat a.1.1) =
      ∑' d : R.RD, ENNReal.ofReal (S.nu (c.dat d.1)) * φ (c.dat d.1) := by
    refine tsum_subtype_eq_of_support_subset (f := fun d : R.RD => ENNReal.ofReal (S.nu (c.dat d.1)) * φ (c.dat d.1)) ?_
    intro a ha
    by_contra hn
    exact ha (hψ0 _ hn)
  have hT : ∀ g : S.H0, ∀ x : S.Datum, (∃ Λ, S.IsTerm x Λ) → ∃ Λ, S.IsTerm (g • x) Λ :=
    fun g x hx => hmove g g.2 x hx
  have hι : ∀ a : A, ∃ Λ, S.IsTerm (c.dat a.1.1) Λ := fun a => a.2
  have hsurj : ∀ x : S.Datum, (∃ Λ, S.IsTerm x Λ) → ∃ a : A, ∃ g : S.H0, g • c.dat a.1.1 = x := by
    intro x hx
    obtain ⟨Λ, hΛ⟩ := hx
    obtain ⟨d, rfl⟩ := hex x Λ hΛ
    obtain ⟨y, hyR, hy⟩ := R.hRD.2.1 d (Set.mem_univ d)
    obtain ⟨h, hh, hhy⟩ := (hrel y d).1 hy
    have hTy : ∃ Λ, S.IsTerm (c.dat y) Λ := by
      have h' := hmove h⁻¹ (S.H0.inv_mem hh) _ ⟨Λ, hΛ⟩
      rwa [← hhy, inv_smul_smul] at h'
    exact ⟨⟨⟨y, hyR⟩, hTy⟩, ⟨h, hh⟩, hhy⟩
  have hinj : ∀ a b : A, (∃ g : S.H0, g • c.dat a.1.1 = c.dat b.1.1) → a = b := by
    rintro a b ⟨g, hg⟩
    have hr : LocNG.Datum.Rel a.1.1 b.1.1 := (hrel _ _).2 ⟨g, g.2, hg⟩
    exact Subtype.ext (Subtype.ext (R.hRD.2.2 _ a.1.2 _ b.1.2 hr))
  have hinv : ∀ g : S.H0, ∀ x : S.Datum, (∃ Λ, S.IsTerm x Λ) →
      ENNReal.ofReal (S.nu (g • x)) * φ (g • x) = ENNReal.ofReal (S.nu x) * φ x := by
    rintro g x ⟨Λ, hΛ⟩
    show ENNReal.ofReal (S.nu ((g : S.GLV) • x)) * φ ((g : S.GLV) • x) = _
    rw [(GlobalTheory.HL.Frames.nu_pos_and_smul M.L r k S x Λ hΛ).2 g g.2, hφ g g.2 x]
  have h2 := (GlobalTheory.tsum_transversal_eq_tsum_orbitQuotient (G := S.H0) (X := S.Datum) (A := A)
    (fun a => c.dat a.1.1) (fun x => ∃ Λ, S.IsTerm x Λ) hT hι hsurj hinj).2
    (fun x => ENNReal.ofReal (S.nu x) * φ x) hinv
  rw [← h1, h2]
  show _ = ∑' o : MulAction.orbitRel.Quotient S.H0 S.Datum, ENNReal.ofReal (S.nu o.out) * φ o.out
  refine tsum_congr fun o => ?_
  split_ifs with ho
  · rfl
  · exact (hψ0 _ ho).symm

end GlobalTheory.HL.CoordSum
