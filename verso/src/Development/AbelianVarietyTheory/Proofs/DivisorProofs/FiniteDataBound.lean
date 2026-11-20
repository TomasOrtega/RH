import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoefficientBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlipsLossBoundedAtExceptionalPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedTensorUnfoldingIntegralValuationLossBoundStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

noncomputable section

namespace GlobalTheory.FunDat

section Val

variable {D : D7}

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, map_one _, Or.inr (by simp [Formalism.DivisionValues.ValuationRepresentative.vw_one])⟩`.
-/
theorem lossLe_one (w : PlL D) : LossLe w 1 0 := ⟨1, map_one _, Or.inr (by simp [Formalism.DivisionValues.ValuationRepresentative.vw_one])⟩

/- English proof (translation)
Take `⟨y, rfl, hy⟩` from `h`. Take `⟨y', rfl, hy'⟩` from `h'`. Use `⟨y * y', map_mul _ _ _, ?_⟩` and prove the remaining obligations. Distinguish the cases in `h0 : y = 0`. Conclude with `Or.inl (by simp [h0])`.

Distinguish the cases in `h0' : y' = 0`. Conclude with `Or.inl (by simp [h0'])`. Break down `hy with h1 | h1` into its components or cases. Conclude with `absurd h1 h0`. Break down `hy' with h2 | h2` into its components or cases.

Conclude with `absurd h2 h0'`. Use `Or.inr ?_` and prove the remaining obligations. Rewrite using `[Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ h0 h0', Int.cast_add]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem lossLe_mul {w : PlL D} {z z' : ℂ} {a a' : ℝ} (h : LossLe w z a) (h' : LossLe w z' a') :
    LossLe w (z * z') (a + a') := by
  obtain ⟨y, rfl, hy⟩ := h
  obtain ⟨y', rfl, hy'⟩ := h'
  refine ⟨y * y', map_mul _ _ _, ?_⟩
  by_cases h0 : y = 0
  · exact Or.inl (by simp [h0])
  by_cases h0' : y' = 0
  · exact Or.inl (by simp [h0'])
  rcases hy with h1 | h1
  · exact absurd h1 h0
  rcases hy' with h2 | h2
  · exact absurd h2 h0'
  refine Or.inr ?_
  rw [Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ h0 h0', Int.cast_add]
  linarith

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using lossLe_one w`. Consider the case `insert i s hi ih`. Rewrite using `[Finset.prod_insert hi, Finset.sum_insert hi]`. Conclude with `lossLe_mul (h i (Finset.mem_insert_self _ _)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))`.
-/
theorem lossLe_prod {w : PlL D} {ι : Type*} (s : Finset ι) (z : ι → ℂ) (a : ι → ℝ) (h : ∀ i ∈ s, LossLe w (z i) (a i)) :
    LossLe w (∏ i ∈ s, z i) (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using lossLe_one w
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact lossLe_mul (h i (Finset.mem_insert_self _ _)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/- English proof (translation)
Assemble the required witnesses or components as `⟨h.1, h.2.1, fun s => (h.2.2 s).trans hB⟩`.
-/
theorem loss_mono {dl : PlL D → ℝ} {B B' : ℝ} (h : Loss dl B) (hB : B ≤ B') : Loss dl B' :=
  ⟨h.1, h.2.1, fun s => (h.2.2 s).trans hB⟩

end Val

section Sum

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc)

def dlD (K : ℝ) (w : PlL D) : ℝ := ∑ P ∈ G.pl.W0, K * (cosExp G P : ℝ) * (vw w ((resCard (Kw P) : ℕ) : D.what₂.LL) : ℝ)

/- English proof (translation)
Establish `hinj : Set.InjOn G.pl.w (G.pl.S0 : Set (Pl D.host.F))` using `fun v hv v' hv' h => (G.pl.under_w hv).symm.trans ((congrArg _ h).trans (G.pl.under_w hv'))`. Rewrite using `[Places.W0, Finset.sum_image hinj, sig, Finset.mul_sum]`. Use `Finset.sum_le_sum fun v hv => ?_` and prove the remaining obligations. Take `⟨h1, -⟩` from `depthAt_w G hv`. Rewrite using `[h1, ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.ResCardPlace.resCard_Kw]`.

Establish `h2` using `ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.log_absNorm_le (G.pl.w v)`. Rewrite `h2` using `[G.pl.under_w hv]`. Establish `h3 : (0 : ℝ) ≤ (G.pl.depth sc v : ℝ)` using `by positivity`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem sum_cosExp_le : ∑ P ∈ G.pl.W0, (cosExp G P : ℝ) * Real.log (resCard (Kw P) : ℕ) ≤ 2 * sig G := by
  classical
  have hinj : Set.InjOn G.pl.w (G.pl.S0 : Set (Pl D.host.F)) := fun v hv v' hv' h =>
    (G.pl.under_w hv).symm.trans ((congrArg _ h).trans (G.pl.under_w hv'))
  rw [Places.W0, Finset.sum_image hinj, sig, Finset.mul_sum]
  refine Finset.sum_le_sum fun v hv => ?_
  obtain ⟨h1, -⟩ := depthAt_w G hv
  rw [h1, ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.ResCardPlace.resCard_Kw]
  have h2 := ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.log_absNorm_le (G.pl.w v)
  rw [G.pl.under_w hv] at h2
  have h3 : (0 : ℝ) ≤ (G.pl.depth sc v : ℝ) := by positivity
  calc (G.pl.depth sc v : ℝ) * Real.log (Ideal.absNorm (G.pl.w v).asIdeal : ℕ)
      ≤ (G.pl.depth sc v : ℝ) * (2 * Real.log (Ideal.absNorm v.asIdeal)) := mul_le_mul_of_nonneg_left h2 h3
    _ = _ := by ring

/- English proof (translation)
Use `⟨fun w => Finset.sum_nonneg fun P _ => mul_nonneg (by positivity) ?_, ?_, fun s => ?_⟩` and prove the remaining obligations. Conclude with `ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.vw_nat_nonneg w _` after adjusting the coercions. Use `((G.pl.W0.finite_toSet.biUnion fun P _ => ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.finite_vw_ne (K := D.what₂.LL) (resCard (Kw P)) (ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.resCard_ne P))).subset fun w hw => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Use `hw (Finset.sum_eq_zero fun P hP => ?_)` and prove the remaining obligations.

Establish `: vw w ((resCard (Kw P) : ℕ) : D.what₂.LL) = 0`. Assume the negation of the conclusion as `h'`. Conclude with `h (Set.mem_biUnion hP h')`. Simplify using `[this]`. Establish `h1 : ∑ w ∈ s, lw w * dlD G K w = ∑ P ∈ G.pl.W0, K * (cosExp G P : ℝ) * ∑ w ∈ s, lw w * (vw w ((resCard (Kw P) : ℕ) : D.what₂.LL) : ℝ)`.

Simplify using `only [dlD, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun P _ => Finset.sum_congr rfl fun w _ => by ring`. Establish `h2 : ∑ w ∈ s, lw w * dlD G K w ≤ ∑ P ∈ G.pl.W0, K * (cosExp G P : ℝ) * Real.log (resCard (Kw P) : ℕ)`. Rewrite using `[h1]`.

Conclude with `Finset.sum_le_sum fun P _ => mul_le_mul_of_nonneg_left (Formalism.EigenvalueLevelCeiling.sum_lw_vw_natCast_le s _ (ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.resCard_ne P)) (by positivity)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.mul_sum]; exact Finset.sum_congr rfl fun P _ => by ring`. Use `_ ≤ K * (2 * sig G) := mul_le_mul_of_nonneg_left (sum_cosExp_le G) hK`. Use `_ = 2 * K * sig G := by ring`.
-/
theorem loss_dlD {K : ℝ} (hK : 0 ≤ K) : Loss (dlD G K) (2 * K * sig G) := by
  classical
  refine ⟨fun w => Finset.sum_nonneg fun P _ => mul_nonneg (by positivity) ?_, ?_, fun s => ?_⟩
  · exact_mod_cast ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.vw_nat_nonneg w _
  · refine ((G.pl.W0.finite_toSet.biUnion fun P _ =>
      ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.finite_vw_ne (K := D.what₂.LL) (resCard (Kw P))
        (ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.resCard_ne P))).subset fun w hw => ?_
    by_contra h
    refine hw (Finset.sum_eq_zero fun P hP => ?_)
    have : vw w ((resCard (Kw P) : ℕ) : D.what₂.LL) = 0 := by
      by_contra h'
      exact h (Set.mem_biUnion hP h')
    simp [this]
  · have h1 : ∑ w ∈ s, lw w * dlD G K w =
        ∑ P ∈ G.pl.W0, K * (cosExp G P : ℝ) * ∑ w ∈ s, lw w * (vw w ((resCard (Kw P) : ℕ) : D.what₂.LL) : ℝ) := by
      simp only [dlD, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun P _ => Finset.sum_congr rfl fun w _ => by ring
    have h2 : ∑ w ∈ s, lw w * dlD G K w ≤ ∑ P ∈ G.pl.W0, K * (cosExp G P : ℝ) * Real.log (resCard (Kw P) : ℕ) := by
      rw [h1]
      exact Finset.sum_le_sum fun P _ => mul_le_mul_of_nonneg_left
        (Formalism.EigenvalueLevelCeiling.sum_lw_vw_natCast_le s _ (ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.resCard_ne P)) (by positivity)
    calc ∑ w ∈ s, lw w * dlD G K w ≤ _ := h2
      _ = K * ∑ P ∈ G.pl.W0, (cosExp G P : ℝ) * Real.log (resCard (Kw P) : ℕ) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun P _ => by ring
      _ ≤ K * (2 * sig G) := mul_le_mul_of_nonneg_left (sum_cosExp_le G) hK
      _ = 2 * K * sig G := by ring

end Sum

end GlobalTheory.FunDat

end

noncomputable section

namespace GlobalTheory.FunDat

section Cases

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc)

/- English proof (translation)
Distinguish the cases in `hP : P ∈ G.pl.W0`. Conclude with `Or.inl hP`. Establish `hQ : P ∈ L.Q t`. Break down `Finset.mem_union.1 hl with h | h` into its components or cases. Conclude with `absurd h hP`.

Conclude with `h`. Use `Or.inr ?_` and prove the remaining obligations. Break down `hA P hQ with h | h` into its components or cases. It suffices to derive a contradiction. Break down `G.pl.mem_S0_of_sum_eq.1 h with h | h` into its components or cases.

Conclude with `G.pl.levelPlace_ne_basePlace t P hQ h`. Conclude with `hP (by`. Rewrite using `[G.pl.w_Q t P hQ h]`. Conclude with `Finset.mem_image_of_mem _ (G.pl.mem_S0_of_sum_eq.2 (Or.inr h)))`. Conclude with `h _ (Formalism.EigenvalueLevelCeiling.plc_prime P) (Formalism.EigenvalueLevelCeiling.plc_mem P)`.
-/
theorem away_cases {t : T} {w : PlL D} (hA : Away G t w) {P : Pl D.host.E} (hl : P ∈ locPl G t) :
    P ∈ G.pl.W0 ∨ ((Formalism.EigenvalueLevelCeiling.plc P : ℕ) : 𝓞 D.what₂.LL) ∉ w.asIdeal := by
  classical
  by_cases hP : P ∈ G.pl.W0
  · exact Or.inl hP
  have hQ : P ∈ L.Q t := by
    rcases Finset.mem_union.1 hl with h | h
    · exact absurd h hP
    · exact h
  refine Or.inr ?_
  rcases hA P hQ with h | h
  · exfalso
    rcases G.pl.mem_S0_of_sum_eq.1 h with h | h
    · exact G.pl.levelPlace_ne_basePlace t P hQ h
    · exact hP (by
        rw [G.pl.w_Q t P hQ h]
        exact Finset.mem_image_of_mem _ (G.pl.mem_S0_of_sum_eq.2 (Or.inr h)))
  · exact h _ (Formalism.EigenvalueLevelCeiling.plc_prime P) (Formalism.EigenvalueLevelCeiling.plc_mem P)

/- English proof (translation)
Rewrite using `[Finset.sum_coe_sort (locPl G t) fun P => K * (cosExp G P : ℝ) * (vw w ((resCard (Kw P) : ℕ) : D.what₂.LL) : ℝ), dlD]`. Use `(Finset.sum_subset Finset.subset_union_left fun P _ hn => ?_).symm` and prove the remaining obligations. Simplify using `[(depthAt_of_notMem G hn).1]`.
-/
theorem sum_locPl (t : T) (K : ℝ) (w : PlL D) :
    ∑ v : locPl G t, K * (cosExp G v : ℝ) * (vw w ((resCard (Kw (v : Pl D.host.E)) : ℕ) : D.what₂.LL) : ℝ) = dlD G K w := by
  classical
  rw [Finset.sum_coe_sort (locPl G t) fun P => K * (cosExp G P : ℝ) * (vw w ((resCard (Kw P) : ℕ) : D.what₂.LL) : ℝ), dlD]
  refine (Finset.sum_subset Finset.subset_union_left fun P _ hn => ?_).symm
  simp [(depthAt_of_notMem G hn).1]

end Cases

/- English proof (translation)
Take `⟨CFa, hA⟩` from `hA`. Take `⟨CFb, hB⟩` from `hB`. Use `⟨max CFa CFb, fun CF hCF => ?_⟩` and prove the remaining obligations. Take `⟨c₁, hA⟩` from `hA CF ((le_max_left _ _).trans hCF)`. Take `⟨c₂, hB⟩` from `hB CF ((le_max_right _ _).trans hCF)`.

Use `⟨max 2 (2 * (max c₁ 0 + max c₂ 0)), fun ε C hC => ?_⟩` and prove the remaining obligations. Take `⟨xa, hA⟩` from `hA ε`. Take `⟨xb, hB⟩` from `hB ε`. Use `⟨max xa xb, fun D large₂ hε hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch hIs hSc hF => ?_⟩` and prove the remaining obligations. Establish `hA` using `hA D large₂ hε ((le_max_left _ _).trans hx) Γ Pl0 T A Ks R F s ch hIs hSc hF`.

Establish `hB` using `hB D large₂ hε ((le_max_right _ _).trans hx) Γ Pl0 T A Ks R F s ch hIs hSc hF`. Establish `hb : 1 ≤ large₂.sc.b` using `Real.one_le_exp (Real.rpow_nonneg (by linarith [large₂.sc.one_lt_alt]) _)`. Establish `hf : (1 : ℝ) ≤ D.R.f`. Establish `h1 : D.R.m ≤ D.R.f` using `D.R.m_le_f`. Establish `h2` using `D.R.two_le_m`.

Conclude with `(show 1 ≤ D.R.f by omega)` after adjusting the coercions. Use `set K0 : ℝ := max c₁ 0 + max c₂ 0 with hK0`. Establish `hK0' : 0 ≤ K0` using `add_nonneg (le_max_right _ _) (le_max_right _ _)`. Use `set M : ℝ := (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 with hM`. Establish `hM0 : 0 ≤ M` using `by positivity`.

Use `set K : ℝ := K0 * M * large₂.sc.b with hK`. Establish `hK' : 0 ≤ K` using `mul_nonneg (mul_nonneg hK0' hM0) (by linarith)`. Establish `hC2 : 2 * K0 ≤ C` using `(le_max_right _ _).trans hC`. Establish `hC0 : 0 ≤ C` using `(by norm_num : (0 : ℝ) ≤ 2).trans ((le_max_left _ _).trans hC)`. Establish `hsig` using `ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.sig_nonneg ch.G`.

Establish `hlb : 0 ≤ Real.log large₂.sc.b` using `Real.log_nonneg hb`. Establish `hbound : 2 * K * sig ch.G ≤ D.R.m * bOne ch.G C large₂.sc.b`. Establish `h1 : 2 * K0 * sig ch.G ≤ C * D.R.f * (Real.log large₂.sc.b + sig ch.G)`. Establish `h2 : 2 * K0 * sig ch.G ≤ C * sig ch.G` using `mul_le_mul_of_nonneg_right hC2 hsig`. Establish `h3 : C * sig ch.G ≤ C * D.R.f * (Real.log large₂.sc.b + sig ch.G)`.

Establish `h4 : sig ch.G ≤ D.R.f * (Real.log large₂.sc.b + sig ch.G)` using `by nlinarith`. Combine the equalities or inequalities in the displayed calculation. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h5` using `mul_le_mul_of_nonneg_right h1 (mul_nonneg hM0 (by linarith : (0 : ℝ) ≤ large₂.sc.b))`. Combine the equalities or inequalities in the displayed calculation.

Use `⟨dlD ch.G K, loss_mono (loss_dlD ch.G hK') hbound, fun t w hAw Φ β hβ x y => ?_⟩` and prove the remaining obligations. Establish `key : ∀ v : locPl ch.G t, LossLe w ((ch.S.term t Φ β v).datum (ch.S.colAt t v x) (ch.S.rowAt t v y)) (K * (cosExp ch.G v : ℝ) * (vw w ((resCard (Kw (v : Pl D.host.E)) : ℕ) : D.what₂.LL) : ℝ))`. Introduce `v`. Establish `hcase` using `away_cases ch.G hAw v.2`. Use `set e : ℝ := (cosExp ch.G v : ℝ) with he`.

Use `set q : ℝ := (vw w ((resCard (Kw (v : Pl D.host.E)) : ℕ) : D.what₂.LL) : ℝ) with hq`. Establish `he0 : 0 ≤ e` using `by positivity`. Establish `hq0 : 0 ≤ q`. Rewrite using `[hq]`. Conclude with `ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.vw_nat_nonneg w _` after adjusting the coercions.

Establish `hX : 0 ≤ M * large₂.sc.b * e * q` using `mul_nonneg (mul_nonneg (mul_nonneg hM0 (by linarith)) he0) hq0`. Use `set c : ℝ := max c₁ 0 * M * large₂.sc.b * e * q with hc`. Establish `hc0 : 0 ≤ c`. Establish `: c = max c₁ 0 * (M * large₂.sc.b * e * q)` using `by rw [hc]; ring`. Rewrite using `[this]`.

Conclude with `mul_nonneg (le_max_right _ _) hX`. Establish `h1 : ∀ z, LossLe w (Tflip ch.W ch.S.B t Φ v z) c` using `fun z => (hA t Φ v v.2 w hcase z).mono (by`. Establish `e1 : c₁ * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * large₂.sc.b * e * q = c₁ * (M * large₂.sc.b * e * q)` using `by rw [hM]; ring`. Establish `e2 : c = max c₁ 0 * (M * large₂.sc.b * e * q)` using `by rw [hc]; ring`. Rewrite using `[e1, e2]`.

Conclude with `mul_le_mul_of_nonneg_right (le_max_left _ _) hX)`. Use `(hB t Φ β hβ v w hcase c hc0 h1 _ _).mono ?_` and prove the remaining obligations. Establish `e3 : c₂ * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * e * q ≤ max c₂ 0 * M * large₂.sc.b * e * q`. Establish `hY : 0 ≤ M * e * q` using `mul_nonneg (mul_nonneg hM0 he0) hq0`. Combine the equalities or inequalities in the displayed calculation.

Combine the equalities or inequalities in the displayed calculation. Establish `hP` using `lossLe_prod Finset.univ _ _ fun v _ => key v`. Rewrite `hP` using `[sum_locPl ch.G t K w]`. Conclude with `hP`.
-/
theorem finDatK_of (hA : ∃ CF0 : ℝ, ∀ CF : ℝ, CF0 ≤ CF → ∃ c₁ : ℝ, ∀ ε : ℝ, ∃ x₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε → x₀ ≤ large₂.sc.x →
    ∀ (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m)
      (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), HidaSetting large₂ R F →
      ∀ ch : Choice R, ch.Is → ch.AtScale CF large₂.sc.b → ch.FieldOK →
      ∀ (t : T) (Φ : ch.G.Datum) (P : Pl D.host.E), P ∈ locPl ch.G t → ∀ w : PlL D,
        (P ∈ ch.G.pl.W0 ∨ ((Formalism.EigenvalueLevelCeiling.plc P : ℕ) : 𝓞 D.what₂.LL) ∉ w.asIdeal) →
        ∀ z, LossLe w (Tflip ch.W ch.S.B t Φ P z) (c₁ * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * large₂.sc.b * (cosExp ch.G P : ℝ) *
          (vw w ((resCard (Kw P) : ℕ) : D.what₂.LL) : ℝ))) (hB : ∃ CF0 : ℝ, ∀ CF : ℝ, CF0 ≤ CF → ∃ c₂ : ℝ, ∀ ε : ℝ, ∃ x₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε → x₀ ≤ large₂.sc.x →
    ∀ (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m)
      (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), HidaSetting large₂ R F →
      ∀ ch : Choice R, ch.Is → ch.AtScale CF large₂.sc.b → ch.FieldOK →
      ∀ (t : T) (Φ : ch.G.Datum), ∀ β ∈ ch.S.supp t Φ, ∀ (P : locPl ch.G t) (w : PlL D),
        ((P : Pl D.host.E) ∈ ch.G.pl.W0 ∨ ((Formalism.EigenvalueLevelCeiling.plc (P : Pl D.host.E) : ℕ) : 𝓞 D.what₂.LL) ∉ w.asIdeal) →
        ∀ c : ℝ, 0 ≤ c → (∀ z, LossLe w (Tflip ch.W ch.S.B t Φ P z) c) →
        ∀ X Y, LossLe w ((ch.S.term t Φ β P).datum X Y) (c + c₂ * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * (cosExp ch.G P : ℝ) *
          (vw w ((resCard (Kw (P : Pl D.host.E)) : ℕ) : D.what₂.LL) : ℝ))) : FinDatK := by
  obtain ⟨CFa, hA⟩ := hA
  obtain ⟨CFb, hB⟩ := hB
  refine ⟨max CFa CFb, fun CF hCF => ?_⟩
  obtain ⟨c₁, hA⟩ := hA CF ((le_max_left _ _).trans hCF)
  obtain ⟨c₂, hB⟩ := hB CF ((le_max_right _ _).trans hCF)
  refine ⟨max 2 (2 * (max c₁ 0 + max c₂ 0)), fun ε C hC => ?_⟩
  obtain ⟨xa, hA⟩ := hA ε
  obtain ⟨xb, hB⟩ := hB ε
  refine ⟨max xa xb, fun D large₂ hε hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch hIs hSc hF => ?_⟩
  have hA := hA D large₂ hε ((le_max_left _ _).trans hx) Γ Pl0 T A Ks R F s ch hIs hSc hF
  have hB := hB D large₂ hε ((le_max_right _ _).trans hx) Γ Pl0 T A Ks R F s ch hIs hSc hF
  have hb : 1 ≤ large₂.sc.b := Real.one_le_exp (Real.rpow_nonneg (by linarith [large₂.sc.one_lt_alt]) _)
  have hf : (1 : ℝ) ≤ D.R.f := by
    have h1 : D.R.m ≤ D.R.f := D.R.m_le_f
    have h2 := D.R.two_le_m
    exact_mod_cast (show 1 ≤ D.R.f by omega)
  set K0 : ℝ := max c₁ 0 + max c₂ 0 with hK0
  have hK0' : 0 ≤ K0 := add_nonneg (le_max_right _ _) (le_max_right _ _)
  set M : ℝ := (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 with hM
  have hM0 : 0 ≤ M := by positivity
  set K : ℝ := K0 * M * large₂.sc.b with hK
  have hK' : 0 ≤ K := mul_nonneg (mul_nonneg hK0' hM0) (by linarith)
  have hC2 : 2 * K0 ≤ C := (le_max_right _ _).trans hC
  have hC0 : 0 ≤ C := (by norm_num : (0 : ℝ) ≤ 2).trans ((le_max_left _ _).trans hC)
  have hsig := ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.sig_nonneg ch.G
  have hlb : 0 ≤ Real.log large₂.sc.b := Real.log_nonneg hb
  have hbound : 2 * K * sig ch.G ≤ D.R.m * bOne ch.G C large₂.sc.b := by
    have h1 : 2 * K0 * sig ch.G ≤ C * D.R.f * (Real.log large₂.sc.b + sig ch.G) := by
      have h2 : 2 * K0 * sig ch.G ≤ C * sig ch.G := mul_le_mul_of_nonneg_right hC2 hsig
      have h3 : C * sig ch.G ≤ C * D.R.f * (Real.log large₂.sc.b + sig ch.G) := by
        have h4 : sig ch.G ≤ D.R.f * (Real.log large₂.sc.b + sig ch.G) := by nlinarith
        calc C * sig ch.G ≤ C * (D.R.f * (Real.log large₂.sc.b + sig ch.G)) := mul_le_mul_of_nonneg_left h4 hC0
          _ = _ := by ring
      linarith
    have h5 := mul_le_mul_of_nonneg_right h1 (mul_nonneg hM0 (by linarith : (0 : ℝ) ≤ large₂.sc.b))
    calc 2 * K * sig ch.G = 2 * K0 * sig ch.G * (M * large₂.sc.b) := by rw [hK]; ring
      _ ≤ C * D.R.f * (Real.log large₂.sc.b + sig ch.G) * (M * large₂.sc.b) := h5
      _ = D.R.m * bOne ch.G C large₂.sc.b := by rw [bOne, hM]; ring
  refine ⟨dlD ch.G K, loss_mono (loss_dlD ch.G hK') hbound, fun t w hAw Φ β hβ x y => ?_⟩
  have key : ∀ v : locPl ch.G t, LossLe w ((ch.S.term t Φ β v).datum (ch.S.colAt t v x) (ch.S.rowAt t v y))
      (K * (cosExp ch.G v : ℝ) * (vw w ((resCard (Kw (v : Pl D.host.E)) : ℕ) : D.what₂.LL) : ℝ)) := by
    intro v
    have hcase := away_cases ch.G hAw v.2
    set e : ℝ := (cosExp ch.G v : ℝ) with he
    set q : ℝ := (vw w ((resCard (Kw (v : Pl D.host.E)) : ℕ) : D.what₂.LL) : ℝ) with hq
    have he0 : 0 ≤ e := by positivity
    have hq0 : 0 ≤ q := by
      rw [hq]; exact_mod_cast ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.vw_nat_nonneg w _
    have hX : 0 ≤ M * large₂.sc.b * e * q := mul_nonneg (mul_nonneg (mul_nonneg hM0 (by linarith)) he0) hq0
    set c : ℝ := max c₁ 0 * M * large₂.sc.b * e * q with hc
    have hc0 : 0 ≤ c := by
      have : c = max c₁ 0 * (M * large₂.sc.b * e * q) := by rw [hc]; ring
      rw [this]; exact mul_nonneg (le_max_right _ _) hX
    have h1 : ∀ z, LossLe w (Tflip ch.W ch.S.B t Φ v z) c := fun z => (hA t Φ v v.2 w hcase z).mono (by
      have e1 : c₁ * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * large₂.sc.b * e * q = c₁ * (M * large₂.sc.b * e * q) := by rw [hM]; ring
      have e2 : c = max c₁ 0 * (M * large₂.sc.b * e * q) := by rw [hc]; ring
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) hX)
    refine (hB t Φ β hβ v w hcase c hc0 h1 _ _).mono ?_
    have e3 : c₂ * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * e * q ≤ max c₂ 0 * M * large₂.sc.b * e * q := by
      have hY : 0 ≤ M * e * q := mul_nonneg (mul_nonneg hM0 he0) hq0
      calc c₂ * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * e * q = c₂ * (M * e * q) := by rw [hM]; ring
        _ ≤ max c₂ 0 * (M * e * q) := mul_le_mul_of_nonneg_right (le_max_left _ _) hY
        _ ≤ max c₂ 0 * (M * e * q) * large₂.sc.b := le_mul_of_one_le_right (mul_nonneg (le_max_right _ _) hY) hb
        _ = max c₂ 0 * M * large₂.sc.b * e * q := by ring
    calc c + c₂ * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * e * q ≤ c + max c₂ 0 * M * large₂.sc.b * e * q := by linarith
      _ = K * e * q := by rw [hc, hK, hK0]; ring
  have hP := lossLe_prod Finset.univ _ _ fun v _ => key v
  rw [sum_locPl ch.G t K w] at hP
  exact hP

/- English proof (translation)
Introduce `_` and use `finDatK_of GlobalTheory.T.flips_loss_bounded_at_exceptional_places GlobalTheory.T.movedTensor_unfolding_integral_valuation_loss_bound`.
-/
theorem finDatK : GlobalTheory.FunPr.Hypotheses₂ → FinDatK := fun _ => finDatK_of GlobalTheory.T.flips_loss_bounded_at_exceptional_places GlobalTheory.T.movedTensor_unfolding_integral_valuation_loss_bound

end GlobalTheory.FunDat

end
