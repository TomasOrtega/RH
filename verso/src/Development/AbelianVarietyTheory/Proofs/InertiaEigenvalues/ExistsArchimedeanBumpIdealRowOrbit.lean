import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocFacOfNeg
import Development.AbelianVarietyTheory.Definitions.Divisors.MemMspan
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenIsCompactUnitaryIntegralPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
import GroundTheory.GlobalFields.IdeleGroups.ClassGroup
import GroundTheory.GlobalFields.TateThesis.AdeleIdealMeasure
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

noncomputable section
namespace GlobalTheory.BumpOrbit
open GlobalTheory.RSTheta

section Local
variable {K : Type} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [ContinuousInv₀ K] [T2Space K]

/- English proof (translation)
Establish `hO : {y : Fin a → K | y ℓ ≠ 0} ∈ nhds (Pi.single ℓ (1:K))` using `(isOpen_ne_fun (continuous_apply ℓ) continuous_const).mem_nhds (by simp)`. Establish `hv : (fun y => rowMat ℓ y) =ᶠ[nhds (Pi.single ℓ (1:K))] fun y => ((rowGL ℓ y : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)` using `Filter.eventually_of_mem hO fun y hy => (val_rowGL (isUnit_iff_ne_zero.2 hy)).symm`. Establish `hc : Continuous fun y : Fin a → K => rowMat ℓ y` using `continuous_const.matrix_updateRow ℓ continuous_id`. Establish `hinv : ContinuousAt (fun y : Fin a → K => (rowMat ℓ y)⁻¹) (Pi.single ℓ 1)`. Use `ContinuousAt.comp (f := fun y => rowMat ℓ y) (g := Inv.inv) ?_ hc.continuousAt` and prove the remaining obligations.

Use `continuousAt_matrix_inv _ ?_` and prove the remaining obligations. Rewrite using `[det_rowMat, Ring.inverse_eq_inv']`. Simplify using `using continuousAt_inv₀ (one_ne_zero (α := K))`. Establish `hv' : (fun y => MulOpposite.op (rowMat ℓ y)⁻¹) =ᶠ[nhds (Pi.single ℓ (1:K))] fun y => MulOpposite.op (((rowGL ℓ y)⁻¹ : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)` using `hv.mono fun y hy => by simp only [Matrix.coe_units_inv, ← hy]`. Rewrite using `[Units.isEmbedding_embedProduct.isInducing.continuousAt_iff]`.

Conclude with `(hc.continuousAt.congr hv).prodMk ((MulOpposite.continuous_op.continuousAt.comp hinv).congr hv')`.
-/
theorem continuousAt_rowGL {a : ℕ} (ℓ : Fin a) :
    ContinuousAt (rowGL ℓ : (Fin a → K) → GL (Fin a) K) (Pi.single ℓ 1) := by
  have hO : {y : Fin a → K | y ℓ ≠ 0} ∈ nhds (Pi.single ℓ (1:K)) :=
    (isOpen_ne_fun (continuous_apply ℓ) continuous_const).mem_nhds (by simp)
  have hv : (fun y => rowMat ℓ y) =ᶠ[nhds (Pi.single ℓ (1:K))]
      fun y => ((rowGL ℓ y : GL (Fin a) K) : Matrix (Fin a) (Fin a) K) :=
    Filter.eventually_of_mem hO fun y hy => (val_rowGL (isUnit_iff_ne_zero.2 hy)).symm
  have hc : Continuous fun y : Fin a → K => rowMat ℓ y := continuous_const.matrix_updateRow ℓ continuous_id
  have hinv : ContinuousAt (fun y : Fin a → K => (rowMat ℓ y)⁻¹) (Pi.single ℓ 1) := by
    refine ContinuousAt.comp (f := fun y => rowMat ℓ y) (g := Inv.inv) ?_ hc.continuousAt
    refine continuousAt_matrix_inv _ ?_
    rw [det_rowMat, Ring.inverse_eq_inv']
    simpa using continuousAt_inv₀ (one_ne_zero (α := K))
  have hv' : (fun y => MulOpposite.op (rowMat ℓ y)⁻¹) =ᶠ[nhds (Pi.single ℓ (1:K))]
      fun y => MulOpposite.op (((rowGL ℓ y)⁻¹ : GL (Fin a) K) : Matrix (Fin a) (Fin a) K) :=
    hv.mono fun y hy => by simp only [Matrix.coe_units_inv, ← hy]
  rw [Units.isEmbedding_embedProduct.isInducing.continuousAt_iff]
  exact (hc.continuousAt.congr hv).prodMk ((MulOpposite.continuous_op.continuousAt.comp hinv).congr hv')

end Local

/- English proof (translation)
Take `⟨k, rfl⟩ : ∃ k, c = WithZero.exp k` from `⟨_, (WithZero.exp_log hc).symm⟩`. Use `⟨(-k + 1).toNat, ?_⟩` and prove the remaining obligations. Rewrite using `[WithZero.exp_lt_exp]`. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_exp_lt {c : WithZero (Multiplicative ℤ)} (hc : c ≠ 0) :
    ∃ N : ℕ, WithZero.exp (-(N:ℤ)) < c := by
  obtain ⟨k, rfl⟩ : ∃ k, c = WithZero.exp k := ⟨_, (WithZero.exp_log hc).symm⟩
  refine ⟨(-k + 1).toNat, ?_⟩
  rw [WithZero.exp_lt_exp]
  omega

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Rewrite `hV` using `[nhds_pi, Filter.mem_pi]`. Take `⟨I, -, t, ht, hsub⟩` from `hV`. Establish `h1 : ∀ j, ∃ N : ℕ, ∀ z : w.adicCompletion E, Valued.v (z - (Pi.single ℓ 1 : Fin a → w.adicCompletion E) j) ≤ WithZero.exp (-(N:ℤ)) → z ∈ t j`. Introduce `j`. Take `⟨γ, hγ⟩` from `Valued.mem_nhds.1 (ht j)`.

Establish `hc : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ (0 : WithZero (Multiplicative ℤ))` using `by simp`. Take `⟨N, hN⟩` from `exists_exp_lt hc`. Use `⟨N, fun z hz => hγ ?_⟩` and prove the remaining obligations. Simplify using `only [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding]`. Conclude with `lt_of_le_of_lt hz hN`.

Use `choose N hN using h1`. Use `⟨Finset.univ.sup N, fun y hy => hsub fun j _ => hN j _ ((hy j).trans ?_)⟩` and prove the remaining obligations. Rewrite using `[WithZero.exp_le_exp, neg_le_neg_iff, Nat.cast_le]`. Conclude with `Finset.le_sup (Finset.mem_univ j)`.
-/
theorem exists_nat_of_mem_nhds {a : ℕ} (ℓ : Fin a) (w : HeightOneSpectrum (𝓞 E))
    {V : Set (Fin a → w.adicCompletion E)} (hV : V ∈ nhds (Pi.single ℓ 1)) :
    ∃ N : ℕ, ∀ y : Fin a → w.adicCompletion E,
      (∀ j, Valued.v (y j - (Pi.single ℓ 1 : Fin a → w.adicCompletion E) j) ≤ WithZero.exp (-(N:ℤ))) → y ∈ V := by
  rw [nhds_pi, Filter.mem_pi] at hV
  obtain ⟨I, -, t, ht, hsub⟩ := hV
  have h1 : ∀ j, ∃ N : ℕ, ∀ z : w.adicCompletion E,
      Valued.v (z - (Pi.single ℓ 1 : Fin a → w.adicCompletion E) j) ≤ WithZero.exp (-(N:ℤ)) → z ∈ t j := by
    intro j
    obtain ⟨γ, hγ⟩ := Valued.mem_nhds.1 (ht j)
    have hc : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ (0 : WithZero (Multiplicative ℤ)) := by simp
    obtain ⟨N, hN⟩ := exists_exp_lt hc
    refine ⟨N, fun z hz => hγ ?_⟩
    simp only [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding]
    exact lt_of_le_of_lt hz hN
  choose N hN using h1
  refine ⟨Finset.univ.sup N, fun y hy => hsub fun j _ => hN j _ ((hy j).trans ?_)⟩
  rw [WithZero.exp_le_exp, neg_le_neg_iff, Nat.cast_le]
  exact Finset.le_sup (Finset.mem_univ j)

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simp`. Consider the case `cons v l ih`. Rewrite using `[List.map_cons, List.prod_cons, map_mul, ih (List.nodup_cons.1 hl).2]`. Distinguish the cases in `h : w = v`.

Substitute `h` using the available equality. Rewrite using `[pLoc_locGL, if_neg (List.nodup_cons.1 hl).1, if_pos List.mem_cons_self, mul_one]`. Rewrite using `[pLoc_locGL_of_ne h, one_mul]`. Simplify using `[h]`.
-/
theorem map_list_prod_locGL {a : ℕ} (g : ∀ w : HeightOneSpectrum (𝓞 E), GL (Fin a) (w.adicCompletion E))
    (l : List (HeightOneSpectrum (𝓞 E))) (hl : l.Nodup) (w : HeightOneSpectrum (𝓞 E)) :
    GeneralLinearGroup.map (pLoc E w) (l.map fun v => locGL E a v (g v)).prod = if w ∈ l then g w else 1 := by
  induction l with
  | nil => simp
  | cons v l ih =>
    rw [List.map_cons, List.prod_cons, map_mul, ih (List.nodup_cons.1 hl).2]
    by_cases h : w = v
    · subst h
      rw [pLoc_locGL, if_neg (List.nodup_cons.1 hl).1, if_pos List.mem_cons_self, mul_one]
    · rw [pLoc_locGL_of_ne h, one_mul]
      simp [h]

/- English proof (translation)
Distinguish the cases in `h : j = ℓ`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, h]`.
-/
theorem pLoc_single {a : ℕ} (ℓ j : Fin a) (w : HeightOneSpectrum (𝓞 E)) :
    pLoc E w ((Pi.single ℓ 1 : Fin a → Af E) j) = (Pi.single ℓ 1 : Fin a → w.adicCompletion E) j := by
  by_cases h : j = ℓ
  · subst h; simp
  · simp [Pi.single_apply, h]

/- English proof (translation)
Apply `exists_nat_of_mem_nhds` to reduce the goal to its premises. Establish `ho : IsOpen ((locGL E a w) ⁻¹' (U : Set (GL (Fin a) (Af E))) ∩ (KGL w a : Set (GL (Fin a) (w.adicCompletion E))))` using `(hU.preimage (GlobalTheory.CuspRep.CuspSub.continuous_locGL w)).inter (GlobalTheory.LFun.IntPtsUnitary.isOpen_GLint _ (Valued.isOpen_integer (w.adicCompletion E)))`. Conclude with `(continuousAt_rowGL ℓ).preimage_mem_nhds (ho.mem_nhds (by simp only [rowGL_single, Set.mem_inter_iff, Set.mem_preimage, map_one, SetLike.mem_coe, one_mem, and_self]))`.
-/
theorem exists_nat_rowGL_mem {a : ℕ} (ℓ : Fin a) {U : Subgroup (GL (Fin a) (Af E))}
    (hU : IsOpen (U : Set (GL (Fin a) (Af E)))) (w : HeightOneSpectrum (𝓞 E)) :
    ∃ N : ℕ, ∀ y : Fin a → w.adicCompletion E,
      (∀ j, Valued.v (y j - (Pi.single ℓ 1 : Fin a → w.adicCompletion E) j) ≤ WithZero.exp (-(N:ℤ))) →
      locGL E a w (rowGL ℓ y) ∈ U ∧ rowGL ℓ y ∈ KGL w a := by
  apply exists_nat_of_mem_nhds
  have ho : IsOpen ((locGL E a w) ⁻¹' (U : Set (GL (Fin a) (Af E))) ∩
      (KGL w a : Set (GL (Fin a) (w.adicCompletion E)))) :=
    (hU.preimage (GlobalTheory.CuspRep.CuspSub.continuous_locGL w)).inter
      (GlobalTheory.LFun.IntPtsUnitary.isOpen_GLint _ (Valued.isOpen_integer (w.adicCompletion E)))
  exact (continuousAt_rowGL ℓ).preimage_mem_nhds
    (ho.mem_nhds (by simp only [rowGL_single, Set.mem_inter_iff, Set.mem_preimage, map_one, SetLike.mem_coe,
      one_mem, and_self]))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pLoc_apply (w : HeightOneSpectrum (𝓞 E)) (x : Af E) : pLoc E w x = x w := rfl

/- English proof (translation)
Establish `h1` using `(GroundTheory.Global.mem_idealFiniteAdeles J).1 (hy j) w`. Rewrite `h1` using `[← pLoc_apply, Pi.sub_apply, map_sub, pLoc_single]`. Conclude with `h1`.
-/
theorem val_sub_single_le {a : ℕ} (ℓ : Fin a) {J : (FractionalIdeal (𝓞 E)⁰ E)ˣ} {y : Fin a → Af E}
    (hy : y - Pi.single ℓ 1 ∈ GlobalTheory.ThetaPoisson.latt a J) (w : HeightOneSpectrum (𝓞 E)) (j : Fin a) :
    Valued.v (pLoc E w (y j) - (Pi.single ℓ 1 : Fin a → w.adicCompletion E) j) ≤
      WithZero.exp (-FractionalIdeal.count E w (J : FractionalIdeal (𝓞 E)⁰ E)) := by
  have h1 := (GroundTheory.Global.mem_idealFiniteAdeles J).1 (hy j) w
  rw [← pLoc_apply, Pi.sub_apply, map_sub, pLoc_single] at h1
  exact h1

/- English proof (translation)
Introduce `E _ _ _ a ℓ T U hU`. Take `⟨r, hr, hball⟩` from `Metric.isOpen_iff.1 (isOpen_rowSet (E := E) ℓ) (Pi.single ℓ 1) (by`. Introduce `w`. Use the proof step `simp)`. Set `f : ContDiffBump (Pi.single ℓ 1 : Fin a → Cinf E)` to `⟨r / 4, r / 2, by positivity, by linarith⟩`.

Use `choose Nw hNw using fun w => exists_nat_rowGL_mem (E := E) ℓ hU w`. Use `set N : ℕ := T.sup Nw + 1 with hN`. Use `set n : HeightOneSpectrum (𝓞 E) → ℤ := fun w => if w ∈ T then (N : ℤ) else 0 with hn`. Establish `hfin : ∀ᶠ v in Filter.cofinite, n v = 0`. Use `Filter.eventually_cofinite.2 (T.finite_toSet.subset fun v hv => ?_)` and prove the remaining obligations.

Assume the negation of the conclusion as `h`. Simplify using `[hn, h] at hv`. Set `J : (FractionalIdeal (𝓞 E)⁰ E)ˣ` to `∏ᶠ w, GroundTheory.Global.primeIdealUnit w ^ n w`. Establish `hJ : ∀ w, FractionalIdeal.count E w (J : FractionalIdeal (𝓞 E)⁰ E) = n w` using `GroundTheory.Global.count_finprod_primeIdealUnit_zpow n hfin`. Use `⟨fun u => ((f u : ℝ) : ℂ), J, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Conclude with `Complex.ofRealCLM.contDiff.comp f.contDiff`. Conclude with `f.hasCompactSupport.comp_left Complex.ofReal_zero`. Use `(tsupport_comp_subset Complex.ofReal_zero f).trans ?_` and prove the remaining obligations. Rewrite using `[f.tsupport_eq]`. Conclude with `(Metric.closedBall_subset_ball (by show r / 2 < r; linarith)).trans hball`.

Introduce `u`. Simplify using `[f.nonneg]`. Simplify using `[f.one_of_mem_closedBall (Metric.mem_closedBall_self (by show (0:ℝ) ≤ r / 4; positivity))]`. Introduce `w hw`. Rewrite using `[hJ, hn]`.

Simplify using `[hw]`. Introduce `y hy`. Establish `hloc : ∀ w ∈ T, ∀ j, Valued.v (pLoc E w (y j) - (Pi.single ℓ 1 : Fin a → w.adicCompletion E) j) ≤ WithZero.exp (-(N : ℤ))`. Introduce `w hw j`. Establish `h1` using `val_sub_single_le ℓ hy w j`.

Rewrite `h1` using `[hJ, hn]`. Simplify `h1` using `only [hw, if_true]`. Establish `hmem : ∀ w ∈ T, locGL E a w (rowGL ℓ (fun j => pLoc E w (y j))) ∈ U ∧ rowGL ℓ (fun j => pLoc E w (y j)) ∈ KGL w a`. Introduce `w hw`. Use `hNw w _ fun j => (hloc w hw j).trans ?_` and prove the remaining obligations.

Rewrite using `[WithZero.exp_le_exp, neg_le_neg_iff, Nat.cast_le, hN]`. Conclude with `(Finset.le_sup hw).trans (Nat.le_succ _)`. Establish `hunit : ∀ w ∈ T, IsUnit (pLoc E w (y ℓ))`. Introduce `w hw`. Use `isUnit_iff_ne_zero.2 fun h0 => ?_` and prove the remaining obligations.

Establish `h2` using `hloc w hw ℓ`. Rewrite `h2` using `[h0, Pi.single_eq_same, zero_sub, Valuation.map_neg, Valuation.map_one, ← WithZero.exp_zero, WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers. Establish `key` using `map_list_prod_locGL (E := E) (a := a) (fun v => rowGL ℓ (fun j => pLoc E v (y j))) T.toList T.nodup_toList`. Use `⟨(T.toList.map fun v => locGL E a v (rowGL ℓ (fun j => pLoc E v (y j)))).prod, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Use `Subgroup.list_prod_mem U fun x hx => ?_` and prove the remaining obligations. Take `⟨v, hv, rfl⟩` from `List.mem_map.1 hx`. Conclude with `(hmem v (Finset.mem_toList.1 hv)).1`. Introduce `w`. Rewrite using `[key w]`.

Use `split_ifs with h`. Conclude with `(hmem w (Finset.mem_toList.1 h)).2`. Conclude with `one_mem _`. Introduce `w hw`. Rewrite using `[key w, if_neg (by simpa using hw)]`.

Introduce `w hw j`. Rewrite using `[key w, if_pos (Finset.mem_toList.2 hw), val_rowGL (hunit w hw)]`. Simplify using `[rowMat]`.
-/
theorem exists_bump_ideal_rowGL : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (ℓ : Fin a)
    (T : Finset (HeightOneSpectrum (𝓞 E))) (U : Subgroup (GL (Fin a) (Af E))), IsOpen (U : Set (GL (Fin a) (Af E))) →
    ∃ (Φ : (Fin a → Cinf E) → ℂ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ),
      ContDiff ℝ (⊤ : ℕ∞) Φ ∧ HasCompactSupport Φ ∧ tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E ℓ ∧
      (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) ∧ 0 < (Φ (Pi.single ℓ 1)).re ∧
      (∀ w ∉ T, FractionalIdeal.count E w (J : FractionalIdeal (𝓞 E)⁰ E) = 0) ∧
      ∀ y : Fin a → Af E, y - Pi.single ℓ 1 ∈ GlobalTheory.ThetaPoisson.latt a J →
        ∃ κ ∈ U, (∀ w, GeneralLinearGroup.map (pLoc E w) κ ∈ KGL w a) ∧
          (∀ w ∉ T, GeneralLinearGroup.map (pLoc E w) κ = 1) ∧
          ∀ w ∈ T, ∀ j, (GeneralLinearGroup.map (pLoc E w) κ : Matrix (Fin a) (Fin a) (w.adicCompletion E)) ℓ j = pLoc E w (y j) := by
  intro E _ _ _ a ℓ T U hU
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (isOpen_rowSet (E := E) ℓ) (Pi.single ℓ 1) (by
    intro w; simp)
  let f : ContDiffBump (Pi.single ℓ 1 : Fin a → Cinf E) := ⟨r / 4, r / 2, by positivity, by linarith⟩
  choose Nw hNw using fun w => exists_nat_rowGL_mem (E := E) ℓ hU w
  set N : ℕ := T.sup Nw + 1 with hN
  set n : HeightOneSpectrum (𝓞 E) → ℤ := fun w => if w ∈ T then (N : ℤ) else 0 with hn
  have hfin : ∀ᶠ v in Filter.cofinite, n v = 0 := by
    refine Filter.eventually_cofinite.2 (T.finite_toSet.subset fun v hv => ?_)
    by_contra h
    simp [hn, h] at hv
  let J : (FractionalIdeal (𝓞 E)⁰ E)ˣ := ∏ᶠ w, GroundTheory.Global.primeIdealUnit w ^ n w
  have hJ : ∀ w, FractionalIdeal.count E w (J : FractionalIdeal (𝓞 E)⁰ E) = n w :=
    GroundTheory.Global.count_finprod_primeIdealUnit_zpow n hfin
  refine ⟨fun u => ((f u : ℝ) : ℂ), J, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Complex.ofRealCLM.contDiff.comp f.contDiff
  · exact f.hasCompactSupport.comp_left Complex.ofReal_zero
  · refine (tsupport_comp_subset Complex.ofReal_zero f).trans ?_
    rw [f.tsupport_eq]
    exact (Metric.closedBall_subset_ball (by show r / 2 < r; linarith)).trans hball
  · intro u; simp [f.nonneg]
  · simp [f.one_of_mem_closedBall (Metric.mem_closedBall_self (by show (0:ℝ) ≤ r / 4; positivity))]
  · intro w hw; rw [hJ, hn]; simp [hw]
  · intro y hy
    have hloc : ∀ w ∈ T, ∀ j, Valued.v (pLoc E w (y j) - (Pi.single ℓ 1 : Fin a → w.adicCompletion E) j) ≤
        WithZero.exp (-(N : ℤ)) := by
      intro w hw j
      have h1 := val_sub_single_le ℓ hy w j
      rw [hJ, hn] at h1
      simpa only [hw, if_true] using h1
    have hmem : ∀ w ∈ T, locGL E a w (rowGL ℓ (fun j => pLoc E w (y j))) ∈ U ∧
        rowGL ℓ (fun j => pLoc E w (y j)) ∈ KGL w a := by
      intro w hw
      refine hNw w _ fun j => (hloc w hw j).trans ?_
      rw [WithZero.exp_le_exp, neg_le_neg_iff, Nat.cast_le, hN]
      exact (Finset.le_sup hw).trans (Nat.le_succ _)
    have hunit : ∀ w ∈ T, IsUnit (pLoc E w (y ℓ)) := by
      intro w hw
      refine isUnit_iff_ne_zero.2 fun h0 => ?_
      have h2 := hloc w hw ℓ
      rw [h0, Pi.single_eq_same, zero_sub, Valuation.map_neg, Valuation.map_one, ← WithZero.exp_zero,
        WithZero.exp_le_exp] at h2
      omega
    have key := map_list_prod_locGL (E := E) (a := a) (fun v => rowGL ℓ (fun j => pLoc E v (y j))) T.toList
      T.nodup_toList
    refine ⟨(T.toList.map fun v => locGL E a v (rowGL ℓ (fun j => pLoc E v (y j)))).prod, ?_, ?_, ?_, ?_⟩
    · refine Subgroup.list_prod_mem U fun x hx => ?_
      obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hx
      exact (hmem v (Finset.mem_toList.1 hv)).1
    · intro w
      rw [key w]
      split_ifs with h
      · exact (hmem w (Finset.mem_toList.1 h)).2
      · exact one_mem _
    · intro w hw
      rw [key w, if_neg (by simpa using hw)]
    · intro w hw j
      rw [key w, if_pos (Finset.mem_toList.2 hw), val_rowGL (hunit w hw)]
      simp [rowMat]

end GlobalTheory.BumpOrbit
