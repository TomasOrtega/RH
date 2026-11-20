import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.MeanLogLeOfBounds
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoversOfLifts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HostBoundHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundHolds
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CovTop.CovSz

/- English proof (translation)
Establish `h0 : 0 ≤ PP ^ 2 * Dd ^ 2 * k` using `by positivity`. Establish `h1 : PP ^ 2 * Dd ^ 2 * k ≤ y ^ 7`. Combine the equalities or inequalities in the displayed calculation. Establish `h2 : PP ^ 2 * Dd ^ 2 * k / m ≤ y ^ 7` using `(div_le_self h0 hm).trans h1`. Establish `h3 : (⌈PP ^ 2 * Dd ^ 2 * k / m⌉₊ : ℝ) < PP ^ 2 * Dd ^ 2 * k / m + 1` using `Nat.ceil_lt_add_one (div_nonneg h0 (by linarith))`.

Establish `h4 : 1 ≤ y ^ 7` using `one_le_pow₀ (by linarith)`. Establish `h5 : (⌈PP ^ 2 * Dd ^ 2 * k / m⌉₊ : ℝ) ≤ y ^ 8`. Establish `: y ^ 8 = y ^ 7 * y` using `by ring`. Use the polynomial consequences of the given equalities and inequalities. Combine the equalities or inequalities in the displayed calculation.
-/
theorem ceil_mul_le_pow {y PP Dd k m : ℝ} (hy : 2 ≤ y) (hP0 : 0 ≤ PP) (hP : PP ≤ y) (hD0 : 0 ≤ Dd) (hD : Dd ≤ y ^ 2)
    (hk0 : 0 ≤ k) (hk : k ≤ y) (hm : 1 ≤ m) : (⌈PP ^ 2 * Dd ^ 2 * k / m⌉₊ : ℝ) * PP ≤ y ^ 9 := by
  have h0 : 0 ≤ PP ^ 2 * Dd ^ 2 * k := by positivity
  have h1 : PP ^ 2 * Dd ^ 2 * k ≤ y ^ 7 := by
    calc PP ^ 2 * Dd ^ 2 * k ≤ y ^ 2 * (y ^ 2) ^ 2 * y := by gcongr
      _ = y ^ 7 := by ring
  have h2 : PP ^ 2 * Dd ^ 2 * k / m ≤ y ^ 7 := (div_le_self h0 hm).trans h1
  have h3 : (⌈PP ^ 2 * Dd ^ 2 * k / m⌉₊ : ℝ) < PP ^ 2 * Dd ^ 2 * k / m + 1 :=
    Nat.ceil_lt_add_one (div_nonneg h0 (by linarith))
  have h4 : 1 ≤ y ^ 7 := one_le_pow₀ (by linarith)
  have h5 : (⌈PP ^ 2 * Dd ^ 2 * k / m⌉₊ : ℝ) ≤ y ^ 8 := by
    have : y ^ 8 = y ^ 7 * y := by ring
    nlinarith
  calc (⌈PP ^ 2 * Dd ^ 2 * k / m⌉₊ : ℝ) * PP ≤ y ^ 8 * y := by gcongr
    _ = y ^ 9 := by ring

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

/- English proof (translation)
Establish `hc : (Fintype.card (Psi p.T.Q.H) : ℝ) = D.R.f`. Rewrite using `[← hW.card, Nat.card_eq_fintype_card]`. Establish `hr : (((dat p i).p + (dat p i).q : ℕ) : ℝ) = D.R.r` using `by rw [hW.sig.2.2]`. Unfold `CovTop.kap sizeK`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`. Rewrite using `[hc, hr]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem kap_le {PP : ℝ} (hW : WtNum p i PP) : CovTop.kap p i ≤ (D.R.f : ℝ) * D.R.r * (4 * L.sc.b) := by
  have hc : (Fintype.card (Psi p.T.Q.H) : ℝ) = D.R.f := by
    rw [← hW.card, Nat.card_eq_fintype_card]
  have hr : (((dat p i).p + (dat p i).q : ℕ) : ℝ) = D.R.r := by rw [hW.sig.2.2]
  unfold CovTop.kap sizeK
  calc _ ≤ ∑ _τ : Psi p.T.Q.H, ∑ _k : Fin ((dat p i).p + (dat p i).q), 4 * L.sc.b :=
        Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun k _ => hW.up τ k
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [hc, hr]; ring

/- English proof (translation)
Take `⟨-, hL, -, -⟩` from `hH.big`. Take `⟨-, hPy, hfy⟩` from `hH.poly`. Establish `hroom` using `hH.room`. Establish `hlow` using `hH.ppLow`. Use `set y := L.sc.x ^ A with hy`.

Establish `hroom' : y ^ 18 ≤ L.sc.b`. Establish `: y ^ (18 : ℝ) = y ^ (18 : ℕ)` using `by exact_mod_cast Real.rpow_natCast y 18`. Rewrite `hroom` using `[this]`. Then use the resulting hypothesis. Establish `hm2` using `D.R.two_le_m`. Establish `hkm` using `D.R.m_add_three_le_k`.

Establish `hkr : D.R.k ≤ D.R.r` using `by unfold Ranks.r; omega`. Establish `hr1 : 1 ≤ D.R.r` using `by omega`. Establish `hn1 : 1 ≤ D.R.nV` using `by unfold Ranks.nV; omega`. Establish `hf8 : (8 : ℝ) ≤ D.R.f` using `by exact_mod_cast hH.f8`. Establish `hr1' : (1 : ℝ) ≤ D.R.r` using `by exact_mod_cast hr1`.

Establish `hn1' : (1 : ℝ) ≤ D.R.nV` using `by exact_mod_cast hn1`. Establish `hkr' : (D.R.k : ℝ) ≤ D.R.r` using `by exact_mod_cast hkr`. Establish `hm' : (1 : ℝ) ≤ D.R.m` using `by exact_mod_cast (by omega : 1 ≤ D.R.m)`. Establish `hfr : (8 : ℝ) ≤ (D.R.f : ℝ) * D.R.r` using `by nlinarith`. Establish `h10 : (D.R.f : ℝ) * D.R.r * 10 ≤ y`.

Use `le_trans ?_ hfy` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Establish `hy2 : 2 ≤ y` using `by linarith`. Establish `hb0 : 0 < L.sc.b` using `Real.exp_pos _`. Establish `hyb : y ≤ L.sc.b` using `(le_self_pow₀ (by linarith) (by norm_num)).trans hroom'`.

Establish `hP0 : 0 ≤ PP` using `le_trans (Even.pow_nonneg (by decide) _) hlow`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `hk` using `kap_le p i hW`. Establish `hk0 : 0 ≤ CovTop.kap p i` using `Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _`. Establish `hk2 : CovTop.kap p i ≤ Real.exp (2 * L.sc.L)`.

Establish `e : Real.exp (2 * L.sc.L) = L.sc.b * L.sc.b`. Unfold `Scale.b`. Rewrite using `[← Real.exp_add]`. Put the polynomial expressions in normal form. Rewrite using `[e]`.

Use the polynomial consequences of the given equalities and inequalities. Break down `hk0.eq_or_lt with h | h` into its components or cases. Rewrite using `[← h, Real.log_zero]`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `(Real.log_le_iff_le_exp h).2 hk2`.

Establish `hch : (D.R.r.choose 2 : ℝ) ≤ (D.R.r : ℝ) ^ 2` using `by exact_mod_cast Nat.choose_le_pow D.R.r 2`. Establish `hD : (CompHt.dimFlag (dat p i) : ℝ) ≤ y ^ 2`. Rewrite using `[hW.dim]`. Use `push_cast`. Combine the equalities or inequalities in the displayed calculation.

Establish `hky : (D.R.k : ℝ) ≤ y` using `by nlinarith`. Establish `h9` using `ceil_mul_le_pow hy2 hP0 hPy (Nat.cast_nonneg _) hD (Nat.cast_nonneg _) hky hm'`. Use `h9.trans (Real.le_sqrt_of_sq_le ?_)` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem kapT_at {PP A : ℝ} (hH : HostNum D L PP A 18) (hW : WtNum p i PP) :
    Real.log (CovTop.kap p i) ≤ 2 * L.sc.L ∧ (lenT p i PP : ℝ) * PP ≤ Real.sqrt L.sc.b := by
  obtain ⟨-, hL, -, -⟩ := hH.big
  obtain ⟨-, hPy, hfy⟩ := hH.poly
  have hroom := hH.room
  have hlow := hH.ppLow
  set y := L.sc.x ^ A with hy
  have hroom' : y ^ 18 ≤ L.sc.b := by
    have : y ^ (18 : ℝ) = y ^ (18 : ℕ) := by exact_mod_cast Real.rpow_natCast y 18
    rwa [this] at hroom
  have hm2 := D.R.two_le_m
  have hkm := D.R.m_add_three_le_k
  have hkr : D.R.k ≤ D.R.r := by unfold Ranks.r; omega
  have hr1 : 1 ≤ D.R.r := by omega
  have hn1 : 1 ≤ D.R.nV := by unfold Ranks.nV; omega
  have hf8 : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hH.f8
  have hr1' : (1 : ℝ) ≤ D.R.r := by exact_mod_cast hr1
  have hn1' : (1 : ℝ) ≤ D.R.nV := by exact_mod_cast hn1
  have hkr' : (D.R.k : ℝ) ≤ D.R.r := by exact_mod_cast hkr
  have hm' : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by omega : 1 ≤ D.R.m)
  have hfr : (8 : ℝ) ≤ (D.R.f : ℝ) * D.R.r := by nlinarith
  have h10 : (D.R.f : ℝ) * D.R.r * 10 ≤ y := by
    refine le_trans ?_ hfy
    calc (D.R.f : ℝ) * D.R.r * 10 = (D.R.f : ℝ) * D.R.r * 1 * 10 := by ring
      _ ≤ _ := by gcongr
  have hy2 : 2 ≤ y := by linarith
  have hb0 : 0 < L.sc.b := Real.exp_pos _
  have hyb : y ≤ L.sc.b := (le_self_pow₀ (by linarith) (by norm_num)).trans hroom'
  have hP0 : 0 ≤ PP := le_trans (Even.pow_nonneg (by decide) _) hlow
  refine ⟨?_, ?_⟩
  · have hk := kap_le p i hW
    have hk0 : 0 ≤ CovTop.kap p i :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hk2 : CovTop.kap p i ≤ Real.exp (2 * L.sc.L) := by
      have e : Real.exp (2 * L.sc.L) = L.sc.b * L.sc.b := by
        unfold Scale.b; rw [← Real.exp_add]; ring_nf
      rw [e]
      nlinarith
    rcases hk0.eq_or_lt with h | h
    · rw [← h, Real.log_zero]; linarith
    · exact (Real.log_le_iff_le_exp h).2 hk2
  · have hch : (D.R.r.choose 2 : ℝ) ≤ (D.R.r : ℝ) ^ 2 := by exact_mod_cast Nat.choose_le_pow D.R.r 2
    have hD : (CompHt.dimFlag (dat p i) : ℝ) ≤ y ^ 2 := by
      rw [hW.dim]; push_cast
      calc (D.R.f : ℝ) * (D.R.r.choose 2 : ℝ) ≤ (D.R.f : ℝ) ^ 2 * (D.R.r : ℝ) ^ 2 := by
            gcongr; nlinarith
        _ = ((D.R.f : ℝ) * D.R.r) ^ 2 := by ring
        _ ≤ y ^ 2 := by gcongr; linarith
    have hky : (D.R.k : ℝ) ≤ y := by nlinarith
    have h9 := ceil_mul_le_pow hy2 hP0 hPy (Nat.cast_nonneg _) hD (Nat.cast_nonneg _) hky hm'
    refine h9.trans (Real.le_sqrt_of_sq_le ?_)
    calc (y ^ 9) ^ 2 = y ^ 18 := by ring
      _ ≤ _ := hroom'

end Point

/- English proof (translation)
Introduce `_`. Use `(Formalism.MainNotions.Closed.and (Sizes.hostN 18) WtShape.wtN).imp fun Fm CH _ hh => ?_` and prove the remaining obligations. Take `⟨⟨C, hC, a, ha⟩, ⟨C', hC', b, hb⟩⟩` from `hh`. Conclude with `⟨C, hC, max a b, fun x hx hle ι p hp i _ _ _ => kapT_at p i (ha x hx ((le_max_left _ _).trans hle) ι p hp i) (hb x hx ((le_max_right _ _).trans hle) ι p hp i)⟩`.
-/
theorem kapT : Size → Covers fun Fm x _ ι p i Y PP _ =>
    Real.log (CovTop.kap p i) ≤ 2 * (Fm.L x ι).sc.L ∧ (lenT p i PP : ℝ) * PP ≤ Real.sqrt (Fm.L x ι).sc.b := by
  intro _
  refine (Formalism.MainNotions.Closed.and (Sizes.hostN 18) WtShape.wtN).imp fun Fm CH _ hh => ?_
  obtain ⟨⟨C, hC, a, ha⟩, ⟨C', hC', b, hb⟩⟩ := hh
  exact ⟨C, hC, max a b, fun x hx hle ι p hp i _ _ _ =>
    kapT_at p i (ha x hx ((le_max_left _ _).trans hle) ι p hp i) (hb x hx ((le_max_right _ _).trans hle) ι p hp i)⟩

end GlobalTheory.CovTop.CovSz

end
