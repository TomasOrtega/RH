import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValLeOneOfMemKO
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSplitPlaceEqFixedTypePrimePlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DiagUniformiserConjTransposeInvMemUpperParahoric
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceCompletionIsoPreservesValuation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FixedNeBotOfFixedVector
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.UniLevelLift

/- English proof (translation)
Introduce `L _ _ _ n J χ s r q hq ψ₀ ξ hψ hU p hp hL`. Use `haveI : Fact (1 < q) := ⟨hq⟩`. Use `set h := s.loc n p with hh`. Establish `hone : ∀ i j : Fin r, ((((1 : GL (Fin r) (ZMod q)) : Matrix (Fin r) (Fin r) (ZMod q)) i j).val : s.v.adicCompletion (maximalRealSubfield L)) = if i = j then 1 else 0`. Introduce `i j`.

Rewrite using `[Units.val_one, Matrix.one_apply]`. Use `split_ifs`. Rewrite using `[ZMod.val_one, Nat.cast_one]`. Rewrite using `[ZMod.val_zero, Nat.cast_zero]`. Establish `hent : ∀ a b : Fin n, Valued.v ((h.val - 1) a b) < 1 ∧ (¬ (a.val < r ∧ b.val < r) → h.val a b = if a = b then 1 else 0)`.

Introduce `a b`. Use `hL a b` as an intermediate fact. Distinguish the cases in `hab : a.val < r ∧ b.val < r`. Rewrite `this` using `[dif_pos hab, hone]`. Use `⟨?_, fun h' => absurd hab h'⟩` and prove the remaining obligations.

Use `this using 3` and compare the differences between its conclusion and the goal. Rewrite using `[Matrix.sub_apply, Matrix.one_apply]`. Distinguish the cases in `e : a = b`. Substitute `e` using the available equality. Simplify using the standard rewrite rules.

Establish `e' : (⟨a.val, hab.1⟩ : Fin r) ≠ ⟨b.val, hab.2⟩` using `fun h2 => e (Fin.ext (by simpa using congrArg Fin.val h2))`. Rewrite using `[if_neg e, if_neg e']`. Rewrite `this` using `[dif_neg hab]`. Use `⟨?_, fun _ => this⟩` and prove the remaining obligations. Rewrite using `[Matrix.sub_apply, this, Matrix.one_apply]`.

Simplify using the standard rewrite rules. Establish `hK : h ∈ GlobalTheory.SplitWeil.KOne (s.v.adicCompletion (maximalRealSubfield L)) (Fin n)` using `(GlobalTheory.FixedAtSplit.mem_KOne_iff' h).2 fun a b => (hent a b).1`. Establish `hKi` using `(GlobalTheory.FixedAtSplit.mem_KOne_iff' _).1 (inv_mem hK)`. Establish `hint : ∀ (y c : s.v.adicCompletion (maximalRealSubfield L)), Valued.v (y - c) < 1 → Valued.v c ≤ 1 → Valued.v y ≤ 1`. Introduce `y c h1 h2`.

Use `Valuation.map_add_le Valued.v (le_of_lt h1) h2` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis. Establish `hone' : ∀ a b : Fin n, Valued.v ((1 : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) a b) ≤ 1`. Introduce `a b`. Rewrite using `[Matrix.one_apply]`.

Use `split_ifs`. Rewrite using `[map_one]`. Rewrite using `[map_zero]`. Conclude with `zero_le'`. Establish `huni : NG.UniRT s r h`.

Use `⟨⟨GlobalTheory.BlockConj.mem_GLint_of (fun a b => ?_) (fun a b => ?_), fun a b ha hb => ?_⟩, fun a b ha hb => ⟨fun hlt => ?_, fun he => ?_⟩⟩` and prove the remaining obligations. Use `(HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (hint _ _ ?_ (hone' a b))` and prove the remaining obligations. Rewrite using `[← Matrix.sub_apply]`. Conclude with `(hent a b).1`. Use `(HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (hint _ _ ?_ (hone' a b))` and prove the remaining obligations.

Rewrite using `[← Matrix.sub_apply]`. Conclude with `hKi a b`. Establish `hne : a ≠ b` using `fun e => by rw [e] at ha; omega`. Rewrite using `[(hent a b).2 (by omega), if_neg hne, map_zero]; exact zero_lt_one`. Establish `hne : a ≠ b` using `fun e => by rw [e] at hlt; omega`.

Use `(hent a b).1` as an intermediate fact. Rewrite `this` using `[Matrix.sub_apply, Matrix.one_apply, if_neg hne, sub_zero]`. Then use the resulting hypothesis. Substitute `he` using the available equality. Use `(hent a a).1` as an intermediate fact. Rewrite `this` using `[Matrix.sub_apply, Matrix.one_apply_eq]`. Then use the resulting hypothesis.

Establish `hpJ : p ∈ J` using `(hU.mem p hp).2 huni`. Establish `hdet : NG.detDD s r h = 1`. Establish `hm : (Matrix.of fun a b : {x : Fin n // r ≤ x.val} => h.val a.1 b.1) = 1`. Use extensionality with `a b`. Rewrite using `[Matrix.of_apply, (hent a.1 b.1).2 (by have := a.2; omega), Matrix.one_apply]`.

Simplify using `only [Subtype.ext_iff]`. Unfold `NG.detDD`. Rewrite using `[hm, Matrix.det_one]`. Establish `hchr` using `hU.chr p hpJ hp 1 (by rw [Units.val_one, hdet])`. Establish `hsup : ψ₀ (NG.supDiag s r h) = 1` using `hψ.1 _ (by`.

Unfold `NG.supDiag`. Use `Valuation.map_sum_lt _ one_ne_zero fun a _ => Valuation.map_sum_lt _ one_ne_zero fun b _ => ?_` and prove the remaining obligations. Use `split_ifs with hab`. Establish `hne : a ≠ b` using `fun e => by rw [e] at hab; omega`. Use `(hent a b).1` as an intermediate fact.

Rewrite `this` using `[Matrix.sub_apply, Matrix.one_apply, if_neg hne, sub_zero]`. Then use the resulting hypothesis. Rewrite using `[map_zero]`. Conclude with `zero_lt_one)`. Use `⟨hpJ, Units.ext ?_⟩` and prove the remaining obligations. Rewrite using `[hchr, hsup, map_one, one_mul, Units.val_one]`.
-/
theorem main : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) (s : SplitPlace L) (r q : ℕ), 1 < q → ∀ (ψ₀ : AddChar (s.v.adicCompletion (maximalRealSubfield L)) ℂ) (ξ : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ), NG.IsPsi0 s ψ₀ → NG.LevelUni J χ s r ψ₀ ξ → ∀ p : GAf L n, TrivOutside {s.v} p → IsLiftAt s r q (1 : GL (Fin r) (ZMod q)) (s.loc n p) → ∃ h : p ∈ J, χ ⟨p, h⟩ = 1 := by
  intro L _ _ _ n J χ s r q hq ψ₀ ξ hψ hU p hp hL
  haveI : Fact (1 < q) := ⟨hq⟩
  set h := s.loc n p with hh
  have hone : ∀ i j : Fin r, ((((1 : GL (Fin r) (ZMod q)) : Matrix (Fin r) (Fin r) (ZMod q)) i j).val :
      s.v.adicCompletion (maximalRealSubfield L)) = if i = j then 1 else 0 := by
    intro i j
    rw [Units.val_one, Matrix.one_apply]
    split_ifs
    · rw [ZMod.val_one, Nat.cast_one]
    · rw [ZMod.val_zero, Nat.cast_zero]
  have hent : ∀ a b : Fin n, Valued.v ((h.val - 1) a b) < 1 ∧
      (¬ (a.val < r ∧ b.val < r) → h.val a b = if a = b then 1 else 0) := by
    intro a b
    have := hL a b
    by_cases hab : a.val < r ∧ b.val < r
    · rw [dif_pos hab, hone] at this
      refine ⟨?_, fun h' => absurd hab h'⟩
      convert this using 3
      rw [Matrix.sub_apply, Matrix.one_apply]
      by_cases e : a = b
      · subst e; simp
      · have e' : (⟨a.val, hab.1⟩ : Fin r) ≠ ⟨b.val, hab.2⟩ := fun h2 => e (Fin.ext (by simpa using congrArg Fin.val h2))
        rw [if_neg e, if_neg e']
    · rw [dif_neg hab] at this
      refine ⟨?_, fun _ => this⟩
      rw [Matrix.sub_apply, this, Matrix.one_apply]
      simp
  have hK : h ∈ GlobalTheory.SplitWeil.KOne (s.v.adicCompletion (maximalRealSubfield L)) (Fin n) :=
    (GlobalTheory.FixedAtSplit.mem_KOne_iff' h).2 fun a b => (hent a b).1
  have hKi := (GlobalTheory.FixedAtSplit.mem_KOne_iff' _).1 (inv_mem hK)
  have hint : ∀ (y c : s.v.adicCompletion (maximalRealSubfield L)), Valued.v (y - c) < 1 → Valued.v c ≤ 1 →
      Valued.v y ≤ 1 := by
    intro y c h1 h2
    have := Valuation.map_add_le Valued.v (le_of_lt h1) h2
    rwa [sub_add_cancel] at this
  have hone' : ∀ a b : Fin n, Valued.v ((1 : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) a b) ≤ 1 := by
    intro a b
    rw [Matrix.one_apply]
    split_ifs
    · rw [map_one]
    · rw [map_zero]; exact zero_le'
  have huni : NG.UniRT s r h := by
    refine ⟨⟨GlobalTheory.BlockConj.mem_GLint_of (fun a b => ?_) (fun a b => ?_), fun a b ha hb => ?_⟩,
      fun a b ha hb => ⟨fun hlt => ?_, fun he => ?_⟩⟩
    · refine (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (hint _ _ ?_ (hone' a b))
      rw [← Matrix.sub_apply]; exact (hent a b).1
    · refine (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (hint _ _ ?_ (hone' a b))
      rw [← Matrix.sub_apply]; exact hKi a b
    · have hne : a ≠ b := fun e => by rw [e] at ha; omega
      rw [(hent a b).2 (by omega), if_neg hne, map_zero]; exact zero_lt_one
    · have hne : a ≠ b := fun e => by rw [e] at hlt; omega
      have := (hent a b).1
      rwa [Matrix.sub_apply, Matrix.one_apply, if_neg hne, sub_zero] at this
    · subst he
      have := (hent a a).1
      rwa [Matrix.sub_apply, Matrix.one_apply_eq] at this
  have hpJ : p ∈ J := (hU.mem p hp).2 huni
  have hdet : NG.detDD s r h = 1 := by
    have hm : (Matrix.of fun a b : {x : Fin n // r ≤ x.val} => h.val a.1 b.1) = 1 := by
      ext a b
      rw [Matrix.of_apply, (hent a.1 b.1).2 (by have := a.2; omega), Matrix.one_apply]
      simp only [Subtype.ext_iff]
    unfold NG.detDD
    rw [hm, Matrix.det_one]
  have hchr := hU.chr p hpJ hp 1 (by rw [Units.val_one, hdet])
  have hsup : ψ₀ (NG.supDiag s r h) = 1 := hψ.1 _ (by
    unfold NG.supDiag
    refine Valuation.map_sum_lt _ one_ne_zero fun a _ => Valuation.map_sum_lt _ one_ne_zero fun b _ => ?_
    split_ifs with hab
    · have hne : a ≠ b := fun e => by rw [e] at hab; omega
      have := (hent a b).1
      rwa [Matrix.sub_apply, Matrix.one_apply, if_neg hne, sub_zero] at this
    · rw [map_zero]; exact zero_lt_one)
  refine ⟨hpJ, Units.ext ?_⟩
  rw [hchr, hsup, map_one, one_mul, Units.val_one]

end GlobalTheory.UniLevelLift
