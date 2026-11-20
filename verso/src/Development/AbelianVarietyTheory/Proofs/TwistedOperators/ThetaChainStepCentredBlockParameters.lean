import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainParOfNodeGap

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec
open GlobalTheory.IndefiniteRowSideFullHecke.WeilSignShift (NcGapGt NcGapGe minSig lamS lamT StepGap)
open GlobalTheory.Chain.ItPairCompare GlobalTheory.Chain.ParOfSizes GlobalTheory.Chain.ParOfNodeGap

namespace GlobalTheory.ArchRec.ParChain

/- English proof (translation)
Establish `hq' : (q : ℝ) ≤ m` using `by exact_mod_cast hq`. Establish `hn' : (n : ℝ) ≤ N` using `by exact_mod_cast hn`. Establish `hm' : (1 : ℝ) ≤ m` using `by exact_mod_cast hm`. Establish `hN' : 8 * (m : ℝ) ≤ N` using `by exact_mod_cast hN`. Establish `h1 : (q : ℝ) ^ ((3 : ℝ) / 2) ≤ (m : ℝ) ^ 2`.

Combine the equalities or inequalities in the displayed calculation. Establish `h2 : 60 * (m : ℝ) ^ 2 ≤ (N : ℝ) ^ 2` using `by nlinarith`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem num_bound_two {n q m N : ℕ} (hq : q ≤ m) (hn : n ≤ N) (hm : 1 ≤ m) (hN : 8 * m ≤ N) :
    120 * (n : ℝ) * (q : ℝ) ^ ((3 : ℝ) / 2) ≤ 2 * (N : ℝ) ^ 3 := by
  have hq' : (q : ℝ) ≤ m := by exact_mod_cast hq
  have hn' : (n : ℝ) ≤ N := by exact_mod_cast hn
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hN' : 8 * (m : ℝ) ≤ N := by exact_mod_cast hN
  have h1 : (q : ℝ) ^ ((3 : ℝ) / 2) ≤ (m : ℝ) ^ 2 := by
    calc (q : ℝ) ^ ((3 : ℝ) / 2) ≤ (m : ℝ) ^ ((3 : ℝ) / 2) := by gcongr
      _ ≤ (m : ℝ) ^ ((2 : ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le hm' (by norm_num)
      _ = (m : ℝ) ^ 2 := Real.rpow_natCast _ _
  have h2 : 60 * (m : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := by nlinarith
  calc 120 * (n : ℝ) * (q : ℝ) ^ ((3 : ℝ) / 2) ≤ 120 * (N : ℝ) * (m : ℝ) ^ 2 := by gcongr
    _ = 2 * (N : ℝ) * (60 * (m : ℝ) ^ 2) := by ring
    _ ≤ 2 * (N : ℝ) * (N : ℝ) ^ 2 := by gcongr
    _ = 2 * (N : ℝ) ^ 3 := by ring

/- English proof (translation)
Introduce `τ`. Take `⟨N, hN, hgap⟩` from `h`. Use `set h₀ : ℝ := (D.R.t : ℝ) + 2 * (N : ℝ) ^ 3 + 1 with hh`. Establish `hg : ∀ (i : ℕ) (h : i + 1 < D.R.m), h₀ ≤ (((D.hc τ).b ⟨i + 1, h⟩ - (D.hc τ).b ⟨i, by omega⟩ : ℚ) : ℝ)`. Introduce `i h`.

Use `hgap τ ⟨i, by omega⟩ h` as an intermediate fact. Rewrite using `[hh]`. Conclude with `this` after adjusting the coercions. Establish `hS : NcGapGe (lamS D k τ) h₀`. Introduce and unpack `⟨x, s⟩ hx ⟨y, s'⟩ hy hs`.

Take `⟨a, rfl, rfl⟩` from `(mem_lamS k τ _ _).1 hx`. Take `⟨b, rfl, rfl⟩` from `(mem_lamS k τ _ _).1 hy`. Conclude with `le_val_sub _ hg _ _ a b hs`. Establish `hT : NcGapGe (lamT D k τ) h₀`. Introduce and unpack `⟨x, s⟩ hx ⟨y, s'⟩ hy hs`.

Take `⟨a, rfl, rfl⟩` from `(mem_lamT k τ _ _).1 hx`. Take `⟨b, rfl, rfl⟩` from `(mem_lamT k τ _ _).1 hy`. Conclude with `le_val_sub _ hg _ _ a b hs`. Establish `hr : ∀ j, j ≤ D.R.m → D.R.rankY j ≤ N` using `fun j hj => by`. Use `Nat.mul_le_mul_right D.R.t hj` as an intermediate fact.

Unfold `Ranks.rankX' at hN`. Unfold `Ranks.rankY`. Use linear arithmetic over natural numbers and integers. Establish `h3 : 8 * D.R.m ≤ N`. Establish `h8 : 8 ≤ D.R.t`.

Use `D.R.rank_add_five_le` as an intermediate fact. Use `D.R.m_add_three_le_k` as an intermediate fact. Use `D.R.two_le_m` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `Nat.mul_le_mul_left D.R.m h8` as an intermediate fact.

Unfold `Ranks.rankX' at hN`. Use linear arithmetic over natural numbers and integers. Establish `ht : (0 : ℝ) ≤ D.R.t` using `by positivity`. Establish `h1 : (D.R.rankY ((k : ℕ) + 1) : ℝ) ^ 3 < h₀`. Establish `h2 : (D.R.rankY ((k : ℕ) + 1) : ℝ) ≤ (N : ℝ)` using `by exact_mod_cast hr _ k.2`.

Establish `h3` using `pow_le_pow_left₀ (by positivity) h2 3`. Establish `h4 : (0 : ℝ) ≤ (N : ℝ) ^ 3` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2` using `num_bound_two (minSig_lamS_le k τ) (hr _ k.2.le) (by have := D.R.two_le_m; omega) h3`. Conclude with `⟨fun x hx y hy hs => h1.trans_le (hS x hx y hy hs), fun x hx y hy hs => h1.trans_le (hT x hx y hy hs), fun x hx y hy hs => le_trans (by linarith) (hS x hx y hy hs)⟩`.
-/
theorem stepGap_of_gap {D : D7} (h : NodeGap D) (k : Fin D.R.m) : StepGap D k := by
  intro τ
  obtain ⟨N, hN, hgap⟩ := h
  set h₀ : ℝ := (D.R.t : ℝ) + 2 * (N : ℝ) ^ 3 + 1 with hh
  have hg : ∀ (i : ℕ) (h : i + 1 < D.R.m),
      h₀ ≤ (((D.hc τ).b ⟨i + 1, h⟩ - (D.hc τ).b ⟨i, by omega⟩ : ℚ) : ℝ) := by
    intro i h
    have := hgap τ ⟨i, by omega⟩ h
    rw [hh]
    exact_mod_cast this
  have hS : NcGapGe (lamS D k τ) h₀ := by
    rintro ⟨x, s⟩ hx ⟨y, s'⟩ hy hs
    obtain ⟨a, rfl, rfl⟩ := (mem_lamS k τ _ _).1 hx
    obtain ⟨b, rfl, rfl⟩ := (mem_lamS k τ _ _).1 hy
    exact le_val_sub _ hg _ _ a b hs
  have hT : NcGapGe (lamT D k τ) h₀ := by
    rintro ⟨x, s⟩ hx ⟨y, s'⟩ hy hs
    obtain ⟨a, rfl, rfl⟩ := (mem_lamT k τ _ _).1 hx
    obtain ⟨b, rfl, rfl⟩ := (mem_lamT k τ _ _).1 hy
    exact le_val_sub _ hg _ _ a b hs
  have hr : ∀ j, j ≤ D.R.m → D.R.rankY j ≤ N := fun j hj => by
    have := Nat.mul_le_mul_right D.R.t hj
    unfold Ranks.rankX' at hN
    unfold Ranks.rankY
    omega
  have h3 : 8 * D.R.m ≤ N := by
    have h8 : 8 ≤ D.R.t := by
      have := D.R.rank_add_five_le; have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
    have := Nat.mul_le_mul_left D.R.m h8
    unfold Ranks.rankX' at hN
    omega
  have ht : (0 : ℝ) ≤ D.R.t := by positivity
  have h1 : (D.R.rankY ((k : ℕ) + 1) : ℝ) ^ 3 < h₀ := by
    have h2 : (D.R.rankY ((k : ℕ) + 1) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hr _ k.2
    have h3 := pow_le_pow_left₀ (by positivity) h2 3
    have h4 : (0 : ℝ) ≤ (N : ℝ) ^ 3 := by positivity
    linarith
  have h2 := num_bound_two (minSig_lamS_le k τ) (hr _ k.2.le) (by have := D.R.two_le_m; omega) h3
  exact ⟨fun x hx y hy hs => h1.trans_le (hS x hx y hy hs), fun x hx y hy hs => h1.trans_le (hT x hx y hy hs),
    fun x hx y hy hs => le_trans (by linarith) (hS x hx y hy hs)⟩

/- English proof (translation)
Introduce `D k τ`. Take `⟨al, be, ga, de, hA, hb, h1, h2⟩` from `exists_lists_chain k τ`. Use `⟨al, be, ga, de, ⟨hA, hb, fun hG => ?_⟩, eq_signed_iff.2 h1, eq_signed_iff.2 h2⟩` and prove the remaining obligations. Establish `h` using `stepGap_of_gap hG k τ`. Establish `hr : D.R.rankY ((k : ℕ) + 1) = D.R.rankY k + D.R.t` using `by simp only [Ranks.rankY]; ring`.

Rewrite `h` using `[hr]`. Use `(hypG_iff hA.2.2.2.2.2.2.1 (h1 ▸ card_lamS k τ)).2 ?_` and prove the remaining obligations. Rewrite using `[← h1, ← h2]` and apply the resulting hypothesis.
-/
theorem parChain : ∀ (D : D7) (k : Fin D.R.m) (τ : D.what₂.Tau), ∃ al be ga de : List ℚ, Centred D al be ga de ∧ parA (Ptw D) k τ = signed (al ++ be) (ga ++ de) (alT D k τ) ∧ parA (Ptw D) (k + 1) τ = signed (al ++ block D.R.t ++ de) (ga ++ be) (alS D k τ) := by
  intro D k τ
  obtain ⟨al, be, ga, de, hA, hb, h1, h2⟩ := exists_lists_chain k τ
  refine ⟨al, be, ga, de, ⟨hA, hb, fun hG => ?_⟩, eq_signed_iff.2 h1, eq_signed_iff.2 h2⟩
  have h := stepGap_of_gap hG k τ
  have hr : D.R.rankY ((k : ℕ) + 1) = D.R.rankY k + D.R.t := by simp only [Ranks.rankY]; ring
  rw [hr] at h
  refine (hypG_iff hA.2.2.2.2.2.2.1 (h1 ▸ card_lamS k τ)).2 ?_
  rwa [← h1, ← h2]

end GlobalTheory.ArchRec.ParChain

end
