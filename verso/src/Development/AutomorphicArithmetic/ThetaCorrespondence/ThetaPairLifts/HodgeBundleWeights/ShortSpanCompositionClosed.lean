import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortLatticeSpanningSets
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsGoodCoverAtMinimalLevel
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.LogSumBadPrimesBoundOfCovering
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.UnramifiedPointsAtDeepLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortLatticeSpanningSetsStatement

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions.TH
namespace GlobalTheory.ShortSpanComp
end GlobalTheory.ShortSpanComp
namespace GlobalTheory.ShortSpanComp
set_option maxHeartbeats 2000000 in
/- English proof (translation)
Introduce `hP`. Take `⟨CG, hCG0, hGM⟩` from `_root_.GlobalTheory.T.exists_good_cover_at_minimal_level hP`. Take `⟨CB, hCB0, hBad⟩` from `_root_.GlobalTheory.T.log_sum_bad_primes_bound_of_covering hP`. Use `⟨11 * CG + CB + 500, by positivity, ?_⟩` and prove the remaining obligations. Introduce `D T hT j hp hq hE hj Y e o hY Lb hLb hM hEs hfr ho c₁ hc₁ hc₁b la hanti hgap hla Z`.

Establish `hL` using `GlobalTheory.LawsDeep.laws_deep D T j Y e o hT hj hY`. Establish `hrk : (T.Q.Dw j).p + (T.Q.Dw j).q = D.R.r`. Take `⟨h1, h2, -⟩` from `hT.pins.2.2.2 j hj`. Take `⟨hj1, hj2⟩` from `hj`. Rewrite using `[h1, h2]`.

Unfold `Formalism.BasicNotions.Ranks.sigW Formalism.BasicNotions.Ranks.r`. Simplify using `only`. Use linear arithmetic over natural numbers and integers. Establish `hcard : Nat.card (Psi T.Q.H) = D.R.f`. Establish `hpin` using `hT.pins.1`.

Establish `hb : Function.Bijective (fun t : D.what₂.Tau => (⟨DV.tauEmb D t, hpin.2.2.2 t⟩ : Psi T.Q.H))` using `⟨fun s t h => GlobalTheory.WeightExponents.tauEmb_injective D (congrArg Subtype.val h), fun τ => by`. Take `⟨t, ht⟩` from `ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.exists_tau_of_inPsi T.Q hpin τ.1 τ.2`. Conclude with `⟨t, Subtype.ext ht.symm⟩⟩`. Rewrite using `[← Nat.card_eq_of_bijective _ hb, Nat.card_eq_fintype_card, D.what₂.card_Tau]`. Establish `hf1 : 1 ≤ D.R.f`.

Establish `hn : 0 < D.R.ord` using `D.R.ord_pos`. Use `show 1 ≤ 2 * D.R.ord`. Use linear arithmetic over natural numbers and integers. Establish `hr1 : 1 ≤ D.R.r` using `by omega`. Use `set m : ℕ := D.R.f * D.R.r + 1 with hm`.

Establish `hgap' : ∀ τ, ((2 * (4 * m) + 2 : ℕ) : ℤ) ≤ gap (la τ) ((T.Q.Dw j).p - 1)` using `fun τ => by`. Establish `h` using `hgap τ`. Establish `e8 : 2 * (4 * m) + 2 = 8 * D.R.f * D.R.r + 10` using `by rw [hm]; ring`. Rewrite using `[e8]`. Conclude with `h`.

Take `⟨a, hDom, hlaOf, hbig⟩` from `GlobalTheory.T.exists_thetaWeight_exponents_of_large_gap D.host.E T.Q.H (T.Q.Dw j) (4 * m) la hp hanti hgap'`. Establish `hn2 : 2 * (4 * m) / 2 = 4 * m` using `by omega`. Use `set n₀ : Psi T.Q.H → ℤ := fun τ => 1 + ((4 * m : ℕ) : ℤ) - la τ ⟨(T.Q.Dw j).p - 1, by omega⟩ with hn₀`. Take `⟨hsizeK, hN0⟩` from `GlobalTheory.T.thetaWeight_and_flatExponent_size_bound D.host.E T.Q.H (T.Q.Dw j) a (2 * (4 * m)) la n₀ hp hlaOf (fun τ => by rw [hn2])`. Establish `hrkR : (((T.Q.Dw j).p + (T.Q.Dw j).q : ℕ) : ℝ) = D.R.r` using `by exact_mod_cast hrk`.

Rewrite `hsizeK` using `[hrkR, hcard, hn2]`. Rewrite `hN0` using `[hcard, hn2]`. Establish `hcast : ((4 * m : ℕ) : ℝ) + 1 = 4 * ((D.R.f : ℝ) * D.R.r + 1) + 1` using `by rw [hm]; push_cast; ring`. Rewrite `hsizeK`, `hN0` using `[hcast]`. Establish `hS : ∃ N : ℕ, (∑ τ, ∑ k, |(la τ k : ℝ)|) = N` using `⟨∑ τ, ∑ k, (la τ k).natAbs, by push_cast [Nat.cast_natAbs]; rfl⟩`.

Establish `hsz0 : 0 ≤ sizeK (T.Q.Dw j) a (2 * (4 * m))` using `sizeK_nonneg _ _ _`. Establish `hsz : Real.log (sizeK (T.Q.Dw j) a (2 * (4 * m))) ≤ 20 * Lb` using `GlobalTheory.T.log_le_twenty_mul_of_bounds D.R.f D.R.r Lb _ _ (by exact_mod_cast hf1) (by exact_mod_cast hr1) hLb hfr hS hla hsz0 (by rw [mul_comm (D.R.r : ℝ) (D.R.f : ℝ)] at hsizeK ⊢; linarith)`. Take `⟨s₀, hs₀lat, hs₀span, hs₀bd⟩` from `hGM D T hT j hp hq hE hj Y e o hY Lb hLb hM hEs hfr ho a (2 * (4 * m)) hDom ⟨4 * m, by ring⟩ (by rw [hm]; nlinarith) hbig hsz`. Take `⟨hKey, hth⟩` from `GlobalTheory.T.exists_keyUnit_pow_twistingSection_on_component D.host.E T.Q.H (T.Q.Dw j) Y.d.l₂ Y.d.Xo₂ Y.d.c₂ D.R.r Y.U (xiR D) hL.unf hL.xi hL.geo hL.pos hL.good`. Take `⟨t₁, ht₁lo, ht₁c⟩` from `hth Z m`.

Establish `hUn` using `_root_.GlobalTheory.T.unramified_points_of_deep_cover hP D T j Y e o hT hj hY`. Establish `hPts : HasPts Y.U Z` using `GlobalTheory.FlatLine.hasPts Y.U hL.pos hL.good hL.unf Z`. Take `⟨t₂, ht₂lo, ht₂c⟩` from `GlobalTheory.T.exists_short_integral_flatLine_twistingSection D.host.E T.Q.H (T.Q.Dw j) Y.d.l₂ Y.d.Xo₂ Y.d.c₂ D.R.r Y.U (xiR D) (badPrimes T.Q.H Y.d.l₂) hKey hL.unf hL.pos badPrimes_prime hUn c₁ hc₁ Z hPts (fun τ => -n₀ τ)`. Establish `hW` using `cuspW_laOf (Dw := T.Q.Dw j) Y.U hL.unf a (2 * (4 * m)) ⟨4 * m, by ring⟩`. Establish `hs₀c : Subtype.val '' s₀ ⊆ (cuspW Y.d.Xo₂ Y.d.c₂ Y.U (wtOf (T.Q.Dw j) (laOf (T.Q.Dw j) a (2 * (4 * m))) ((2 * (4 * m) / 2 : ℕ) : ℤ)) : Set (Rul Y.d.Xo₂ Y.d.c₂))`.

Introduce and unpack `_ ⟨f, -, rfl⟩`. Rewrite using `[SetLike.mem_coe, ← hW]`. Conclude with `f.2`. Establish `hs₀i : ∀ f ∈ Subtype.val '' s₀, ∀ la, ∀ v ∈ valSet Y.d.Xo₂ Y.d.c₂ (algCls Y.d.Xo₂ Y.d.c₂) la, 0 ≤ v f`. Introduce and unpack `_ ⟨f, hf, rfl⟩`.

Conclude with `(AllWt.mem_supLat).1 (hs₀lat hf)`. Establish `hs₀s : cuspW Y.d.Xo₂ Y.d.c₂ Y.U (wtOf (T.Q.Dw j) (laOf (T.Q.Dw j) a (2 * (4 * m))) ((2 * (4 * m) / 2 : ℕ) : ℤ)) ≤ Submodule.span Y.d.c₂.F (Subtype.val '' s₀)`. Rewrite using `[← hW]`. Introduce `g hg`. Establish `h1 : (⟨g, hg⟩ : Y.V (wtZ a (2 * (4 * m)))) ∈ Submodule.span Y.d.c₂.F s₀`.

Rewrite using `[hs₀span]`. Conclude with `Submodule.mem_top`. Conclude with `Submodule.apply_mem_span_image_of_mem_span (Y.V (wtZ a (2 * (4 * m)))).subtype h1`. Establish `hlo : ∀ w, 0 ≤ (t₁.mul t₂).lo w` using `fun w => add_nonneg (ht₁lo w) (ht₂lo w)`. Establish `hGG : wtOf (T.Q.Dw j) (laOf (T.Q.Dw j) a (2 * (4 * m))) ((2 * (4 * m) / 2 : ℕ) : ℤ) + (wtOf (T.Q.Dw j) 0 (-(4 * (m : ℤ))) + wtOf (T.Q.Dw j) (parWt (T.Q.Dw j) fun τ => -n₀ τ) 0) = wtOf (T.Q.Dw j) la 0`.

Rewrite using `[← AllWt.wtOf_add, ← AllWt.wtOf_add, hlaOf, hn2]`. Use `congr 1`. Use function extensionality and compare the values at `τ k`. Simplify using `[parWt]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `key` using `GlobalTheory.T.exists_spanning_family_mul_twistingSection D T.Q.H (T.Q.Dw j) Y.d.l₂ Y.d.Xo₂ Y.d.c₂ D.R.r Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z _ _ (t₁.mul t₂) hL.unf (AllWt.even_wtOf _ _) hlo _ hs₀c hs₀i hs₀s`. Rewrite `key` using `[hGG]`. Take `⟨s, hslat, hsspan, hsbd⟩` from `key`. Use `⟨s, hslat, hsspan, fun y hy σ => ?_⟩` and prove the remaining obligations.

Take `⟨f, ⟨f₀, hf₀, rfl⟩, hfbd⟩` from `hsbd y hy`. Establish `hP1 : petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) (laOf (T.Q.Dw j) a (2 * (4 * m))) ((2 * (4 * m) / 2 : ℕ) : ℤ)) σ (f₀ : Rul Y.d.Xo₂ Y.d.c₂) ≤ Real.exp (CG * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 * sizeK (T.Q.Dw j) a (2 * (4 * m)))`. Rewrite using `[petOn_congr Y.U (xiR D) (fun _ => D.sp.W j) Y.dict hL.unf Z (exZ_laOf (T.Q.Dw j) a (2 * (4 * m)) ⟨4 * m, by ring⟩)]`. Conclude with `(hs₀bd f₀ hf₀ σ).2 Z`. Establish `hc1 : t₁.cInf σ ≤ Real.exp (((D.R.f : ℝ) * D.R.r + 1) * (2 * ((D.R.f : ℝ) * D.R.r) * Real.log (2 * Real.pi)))`.

Establish `h` using `ht₁c σ`. Establish `hNR : ((Nat.card (Psi T.Q.H) * ((T.Q.Dw j).p + (T.Q.Dw j).q) : ℕ) : ℝ) = (D.R.f : ℝ) * D.R.r`. Rewrite using `[hcard, hrk]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `h` using `[hNR, Real.log_le_iff_le_exp (t₁.cInf_pos σ)]`. Use `h.trans (le_of_eq ?_)` and prove the remaining obligations. Use `congr 1`. Rewrite using `[hm]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hc2 : t₂.cInf σ ≤ Real.exp ((|c₁| + ((T.Q.Dw j).q : ℝ) * lrd D.host.E) * ∑ τ, |(n₀ τ : ℝ)| + logSum (badPrimes T.Q.H Y.d.l₂) + Real.log |(discr Y.d.c₂.F : ℝ)| / (2 * (Module.finrank ℚ Y.d.c₂.F : ℝ)) + 1)`. Establish `h` using `ht₂c σ`. Simplify using `only [Int.cast_neg, abs_neg] at h`. Rewrite `h` using `[Real.log_le_iff_le_exp (t₂.cInf_pos σ)]`. Then use the resulting hypothesis.

Establish `hdd : Real.log |(discr Y.d.c₂.F : ℝ)| / (2 * (Module.finrank ℚ Y.d.c₂.F : ℝ)) ≤ 391 / 2 * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2`. Establish `h` using `hY.rd`. Establish `hpos : (0 : ℝ) < Module.finrank ℚ Y.d.c₂.F` using `by exact_mod_cast Module.finrank_pos`. Rewrite using `[div_le_iff₀ (by positivity)]`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hlrd` using `lrd_bounds D.host.E`. Establish `hq_r : ((T.Q.Dw j).q : ℝ) ≤ D.R.r` using `by exact_mod_cast (show (T.Q.Dw j).q ≤ D.R.r by omega)`. Establish `hSnn : 0 ≤ ∑ τ, ∑ k, |(la τ k : ℝ)|` using `by positivity`. Establish `hNnn : 0 ≤ ∑ τ, |(n₀ τ : ℝ)|` using `by positivity`. Establish `hfin` using `GlobalTheory.T.covolume_numerical_bounds_collect CG CB D.R.f D.R.r Lb (∑ τ, ∑ k, |(la τ k : ℝ)|) (∑ τ, |(n₀ τ : ℝ)|) (sizeK (T.Q.Dw j) a (2 * (4 * m))) c₁ ((T.Q.Dw j).q) (lrd D.host.E) (logSum (badPrimes T.Q.H Y.d.l₂)) (Real.log |(discr Y.d.c₂.F : ℝ)| / (2 * (Module.finrank ℚ Y.d …`.

Use `(hfbd σ).trans ?_` and prove the remaining obligations. Use `show t₁.cInf σ * t₂.cInf σ * _ ≤ _`. Establish `hpet0 : 0 ≤ petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) (laOf (T.Q.Dw j) a (2 * (4 * m))) ((2 * (4 * m) / 2 : ℕ) : ℤ)) σ (f₀ : Rul Y.d.Xo₂ Y.d.c₂)` using `AllWt.petAt_nonneg _ _ _ _ _ _ _`. Combine the equalities or inequalities in the displayed calculation. Establish `h1` using `(t₁.cInf_pos σ).le`.

Establish `h2` using `(t₂.cInf_pos σ).le`. Use `gcongr`. Use `_ = Real.exp (_ + _ + _) := by rw [← Real.exp_add, ← Real.exp_add]`. Use `_ ≤ _ := Real.exp_le_exp.2 hfin`.
-/
theorem short_span_comp_mem : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ Lb : ℝ, 1 ≤ Lb → Real.log Y.d.l₂.M ≤ 30 * Lb → fieldSz D.host.E ≤ 3 * Lb → Real.log (D.R.f * D.R.r) ≤ Lb → o ≤ 391 * (D.R.f * D.R.r * Lb) ^ 2 → ∀ c₁ : ℝ, GlobalTheory.FlatLine.FlatExistsAt Y.U (xiR D) c₁ → |c₁| ≤ 9 * D.R.r * Lb → ∀ la : AllWt.Weight (T.Q.Dw j), (∀ τ, Antitone (la τ)) → (∀ τ, ((8 * D.R.f * D.R.r + 10 : ℕ) : ℤ) ≤ gap (la τ) ((T.Q.Dw j).p - 1)) → Real.log (∑ τ, ∑ k, |(la τ k : ℝ)|) ≤ 10 * Lb → ∀ Z, ∃ s : Set (cuspOn Y.U Z (wtOf (T.Q.Dw j) la 0)), s ⊆ (latOn Y.U Z (wtOf (T.Q.Dw j) la 0) : Set (cuspOn Y.U Z (wtOf (T.Q.Dw j) la 0))) ∧ Submodule.span Y.d.c₂.F s = ⊤ ∧ ∀ y ∈ s, ∀ σ, normOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) la 0) σ y ≤ Real.exp (C * (((D.R.f : ℝ) * D.R.r * Lb) ^ 3 * (∑ τ, ∑ k, |(la τ k : ℝ)|) + ((D.R.f : ℝ) * D.R.r * Lb) ^ 5)) := by
  intro hP
  obtain ⟨CG, hCG0, hGM⟩ := _root_.GlobalTheory.T.exists_good_cover_at_minimal_level hP
  obtain ⟨CB, hCB0, hBad⟩ := _root_.GlobalTheory.T.log_sum_bad_primes_bound_of_covering hP
  refine ⟨11 * CG + CB + 500, by positivity, ?_⟩
  intro D T hT j hp hq hE hj Y e o hY Lb hLb hM hEs hfr ho c₁ hc₁ hc₁b la hanti hgap hla Z
  have hL := GlobalTheory.LawsDeep.laws_deep D T j Y e o hT hj hY
  have hrk : (T.Q.Dw j).p + (T.Q.Dw j).q = D.R.r := by
    obtain ⟨h1, h2, -⟩ := hT.pins.2.2.2 j hj
    obtain ⟨hj1, hj2⟩ := hj
    rw [h1, h2]; unfold Formalism.BasicNotions.Ranks.sigW Formalism.BasicNotions.Ranks.r; simp only; omega
  have hcard : Nat.card (Psi T.Q.H) = D.R.f := by
    have hpin := hT.pins.1
    have hb : Function.Bijective (fun t : D.what₂.Tau => (⟨DV.tauEmb D t, hpin.2.2.2 t⟩ : Psi T.Q.H)) :=
      ⟨fun s t h => GlobalTheory.WeightExponents.tauEmb_injective D (congrArg Subtype.val h), fun τ => by
        obtain ⟨t, ht⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.exists_tau_of_inPsi T.Q hpin τ.1 τ.2
        exact ⟨t, Subtype.ext ht.symm⟩⟩
    rw [← Nat.card_eq_of_bijective _ hb, Nat.card_eq_fintype_card, D.what₂.card_Tau]
  have hf1 : 1 ≤ D.R.f := by
    have hn : 0 < D.R.ord := D.R.ord_pos
    show 1 ≤ 2 * D.R.ord
    omega
  have hr1 : 1 ≤ D.R.r := by omega
  set m : ℕ := D.R.f * D.R.r + 1 with hm
  have hgap' : ∀ τ, ((2 * (4 * m) + 2 : ℕ) : ℤ) ≤ gap (la τ) ((T.Q.Dw j).p - 1) := fun τ => by
    have h := hgap τ
    have e8 : 2 * (4 * m) + 2 = 8 * D.R.f * D.R.r + 10 := by rw [hm]; ring
    rw [e8]; exact h
  obtain ⟨a, hDom, hlaOf, hbig⟩ := GlobalTheory.T.exists_thetaWeight_exponents_of_large_gap D.host.E T.Q.H (T.Q.Dw j) (4 * m) la hp hanti hgap'
  have hn2 : 2 * (4 * m) / 2 = 4 * m := by omega
  set n₀ : Psi T.Q.H → ℤ := fun τ => 1 + ((4 * m : ℕ) : ℤ) - la τ ⟨(T.Q.Dw j).p - 1, by omega⟩ with hn₀
  obtain ⟨hsizeK, hN0⟩ := GlobalTheory.T.thetaWeight_and_flatExponent_size_bound D.host.E T.Q.H (T.Q.Dw j) a (2 * (4 * m)) la n₀ hp hlaOf
    (fun τ => by rw [hn2])
  have hrkR : (((T.Q.Dw j).p + (T.Q.Dw j).q : ℕ) : ℝ) = D.R.r := by exact_mod_cast hrk
  rw [hrkR, hcard, hn2] at hsizeK
  rw [hcard, hn2] at hN0
  have hcast : ((4 * m : ℕ) : ℝ) + 1 = 4 * ((D.R.f : ℝ) * D.R.r + 1) + 1 := by rw [hm]; push_cast; ring
  rw [hcast] at hsizeK hN0
  have hS : ∃ N : ℕ, (∑ τ, ∑ k, |(la τ k : ℝ)|) = N :=
    ⟨∑ τ, ∑ k, (la τ k).natAbs, by push_cast [Nat.cast_natAbs]; rfl⟩
  have hsz0 : 0 ≤ sizeK (T.Q.Dw j) a (2 * (4 * m)) := sizeK_nonneg _ _ _
  have hsz : Real.log (sizeK (T.Q.Dw j) a (2 * (4 * m))) ≤ 20 * Lb :=
    GlobalTheory.T.log_le_twenty_mul_of_bounds D.R.f D.R.r Lb _ _ (by exact_mod_cast hf1) (by exact_mod_cast hr1) hLb hfr hS hla hsz0
      (by rw [mul_comm (D.R.r : ℝ) (D.R.f : ℝ)] at hsizeK ⊢; linarith)
  obtain ⟨s₀, hs₀lat, hs₀span, hs₀bd⟩ := hGM D T hT j hp hq hE hj Y e o hY Lb hLb hM hEs hfr ho a (2 * (4 * m))
    hDom ⟨4 * m, by ring⟩ (by rw [hm]; nlinarith) hbig hsz
  obtain ⟨hKey, hth⟩ := GlobalTheory.T.exists_keyUnit_pow_twistingSection_on_component D.host.E T.Q.H (T.Q.Dw j) Y.d.l₂ Y.d.Xo₂ Y.d.c₂ D.R.r Y.U (xiR D) hL.unf hL.xi hL.geo
    hL.pos hL.good
  obtain ⟨t₁, ht₁lo, ht₁c⟩ := hth Z m
  have hUn := _root_.GlobalTheory.T.unramified_points_of_deep_cover hP D T j Y e o hT hj hY
  have hPts : HasPts Y.U Z := GlobalTheory.FlatLine.hasPts Y.U hL.pos hL.good hL.unf Z
  obtain ⟨t₂, ht₂lo, ht₂c⟩ := GlobalTheory.T.exists_short_integral_flatLine_twistingSection D.host.E T.Q.H (T.Q.Dw j) Y.d.l₂ Y.d.Xo₂ Y.d.c₂ D.R.r Y.U (xiR D)
    (badPrimes T.Q.H Y.d.l₂) hKey hL.unf hL.pos badPrimes_prime hUn c₁ hc₁ Z hPts (fun τ => -n₀ τ)
  have hW := cuspW_laOf (Dw := T.Q.Dw j) Y.U hL.unf a (2 * (4 * m)) ⟨4 * m, by ring⟩
  have hs₀c : Subtype.val '' s₀ ⊆ (cuspW Y.d.Xo₂ Y.d.c₂ Y.U (wtOf (T.Q.Dw j) (laOf (T.Q.Dw j) a (2 * (4 * m)))
      ((2 * (4 * m) / 2 : ℕ) : ℤ)) : Set (Rul Y.d.Xo₂ Y.d.c₂)) := by
    rintro _ ⟨f, -, rfl⟩
    rw [SetLike.mem_coe, ← hW]
    exact f.2
  have hs₀i : ∀ f ∈ Subtype.val '' s₀, ∀ la, ∀ v ∈ valSet Y.d.Xo₂ Y.d.c₂ (algCls Y.d.Xo₂ Y.d.c₂) la, 0 ≤ v f := by
    rintro _ ⟨f, hf, rfl⟩
    exact (AllWt.mem_supLat).1 (hs₀lat hf)
  have hs₀s : cuspW Y.d.Xo₂ Y.d.c₂ Y.U (wtOf (T.Q.Dw j) (laOf (T.Q.Dw j) a (2 * (4 * m)))
      ((2 * (4 * m) / 2 : ℕ) : ℤ)) ≤ Submodule.span Y.d.c₂.F (Subtype.val '' s₀) := by
    rw [← hW]
    intro g hg
    have h1 : (⟨g, hg⟩ : Y.V (wtZ a (2 * (4 * m)))) ∈ Submodule.span Y.d.c₂.F s₀ := by
      rw [hs₀span]; exact Submodule.mem_top
    exact Submodule.apply_mem_span_image_of_mem_span (Y.V (wtZ a (2 * (4 * m)))).subtype h1
  have hlo : ∀ w, 0 ≤ (t₁.mul t₂).lo w := fun w => add_nonneg (ht₁lo w) (ht₂lo w)
  have hGG : wtOf (T.Q.Dw j) (laOf (T.Q.Dw j) a (2 * (4 * m))) ((2 * (4 * m) / 2 : ℕ) : ℤ) +
      (wtOf (T.Q.Dw j) 0 (-(4 * (m : ℤ))) + wtOf (T.Q.Dw j) (parWt (T.Q.Dw j) fun τ => -n₀ τ) 0) =
      wtOf (T.Q.Dw j) la 0 := by
    rw [← AllWt.wtOf_add, ← AllWt.wtOf_add, hlaOf, hn2]
    congr 1
    · funext τ k; simp [parWt]
    · push_cast; ring
  have key := GlobalTheory.T.exists_spanning_family_mul_twistingSection D T.Q.H (T.Q.Dw j) Y.d.l₂ Y.d.Xo₂ Y.d.c₂ D.R.r Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z _ _
    (t₁.mul t₂) hL.unf (AllWt.even_wtOf _ _) hlo _ hs₀c hs₀i hs₀s
  rw [hGG] at key
  obtain ⟨s, hslat, hsspan, hsbd⟩ := key
  refine ⟨s, hslat, hsspan, fun y hy σ => ?_⟩
  obtain ⟨f, ⟨f₀, hf₀, rfl⟩, hfbd⟩ := hsbd y hy
  have hP1 : petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) (laOf (T.Q.Dw j) a (2 * (4 * m)))
      ((2 * (4 * m) / 2 : ℕ) : ℤ)) σ (f₀ : Rul Y.d.Xo₂ Y.d.c₂) ≤
      Real.exp (CG * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 * sizeK (T.Q.Dw j) a (2 * (4 * m))) := by
    rw [petOn_congr Y.U (xiR D) (fun _ => D.sp.W j) Y.dict hL.unf Z
      (exZ_laOf (T.Q.Dw j) a (2 * (4 * m)) ⟨4 * m, by ring⟩)]
    exact (hs₀bd f₀ hf₀ σ).2 Z
  have hc1 : t₁.cInf σ ≤
      Real.exp (((D.R.f : ℝ) * D.R.r + 1) * (2 * ((D.R.f : ℝ) * D.R.r) * Real.log (2 * Real.pi))) := by
    have h := ht₁c σ
    have hNR : ((Nat.card (Psi T.Q.H) * ((T.Q.Dw j).p + (T.Q.Dw j).q) : ℕ) : ℝ) = (D.R.f : ℝ) * D.R.r := by
      rw [hcard, hrk]; push_cast; ring
    rw [hNR, Real.log_le_iff_le_exp (t₁.cInf_pos σ)] at h
    refine h.trans (le_of_eq ?_)
    congr 1
    rw [hm]; push_cast; ring
  have hc2 : t₂.cInf σ ≤ Real.exp ((|c₁| + ((T.Q.Dw j).q : ℝ) * lrd D.host.E) * ∑ τ, |(n₀ τ : ℝ)| +
      logSum (badPrimes T.Q.H Y.d.l₂) + Real.log |(discr Y.d.c₂.F : ℝ)| / (2 * (Module.finrank ℚ Y.d.c₂.F : ℝ)) + 1) := by
    have h := ht₂c σ
    simp only [Int.cast_neg, abs_neg] at h
    rwa [Real.log_le_iff_le_exp (t₂.cInf_pos σ)] at h
  have hdd : Real.log |(discr Y.d.c₂.F : ℝ)| / (2 * (Module.finrank ℚ Y.d.c₂.F : ℝ)) ≤
      391 / 2 * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 := by
    have h := hY.rd
    have hpos : (0 : ℝ) < Module.finrank ℚ Y.d.c₂.F := by exact_mod_cast Module.finrank_pos
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hlrd := lrd_bounds D.host.E
  have hq_r : ((T.Q.Dw j).q : ℝ) ≤ D.R.r := by exact_mod_cast (show (T.Q.Dw j).q ≤ D.R.r by omega)
  have hSnn : 0 ≤ ∑ τ, ∑ k, |(la τ k : ℝ)| := by positivity
  have hNnn : 0 ≤ ∑ τ, |(n₀ τ : ℝ)| := by positivity
  have hfin := GlobalTheory.T.covolume_numerical_bounds_collect CG CB D.R.f D.R.r Lb (∑ τ, ∑ k, |(la τ k : ℝ)|) (∑ τ, |(n₀ τ : ℝ)|)
    (sizeK (T.Q.Dw j) a (2 * (4 * m))) c₁ ((T.Q.Dw j).q) (lrd D.host.E) (logSum (badPrimes T.Q.H Y.d.l₂))
    (Real.log |(discr Y.d.c₂.F : ℝ)| / (2 * (Module.finrank ℚ Y.d.c₂.F : ℝ))) hCG0 hCB0 (by exact_mod_cast hf1)
    (by exact_mod_cast hr1) hLb hSnn (Nat.cast_nonneg _) hq_r hlrd.1 (hlrd.2.trans hEs) hc₁b hNnn (by linarith [hN0])
    hsz0 (by linarith [hsizeK]) (hBad D T hT j hj Y e o hY Lb hLb hM hEs hfr) hdd
  refine (hfbd σ).trans ?_
  show t₁.cInf σ * t₂.cInf σ * _ ≤ _
  have hpet0 : 0 ≤ petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) (laOf (T.Q.Dw j) a (2 * (4 * m)))
      ((2 * (4 * m) / 2 : ℕ) : ℤ)) σ (f₀ : Rul Y.d.Xo₂ Y.d.c₂) := AllWt.petAt_nonneg _ _ _ _ _ _ _
  calc t₁.cInf σ * t₂.cInf σ * _ ≤ Real.exp (((D.R.f : ℝ) * D.R.r + 1) * (2 * ((D.R.f : ℝ) * D.R.r) * Real.log (2 * Real.pi))) *
        Real.exp ((|c₁| + ((T.Q.Dw j).q : ℝ) * lrd D.host.E) * ∑ τ, |(n₀ τ : ℝ)| +
          logSum (badPrimes T.Q.H Y.d.l₂) + Real.log |(discr Y.d.c₂.F : ℝ)| / (2 * (Module.finrank ℚ Y.d.c₂.F : ℝ)) + 1) *
        Real.exp (CG * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 * sizeK (T.Q.Dw j) a (2 * (4 * m))) := by
        have h1 := (t₁.cInf_pos σ).le
        have h2 := (t₂.cInf_pos σ).le
        gcongr
    _ = Real.exp (_ + _ + _) := by rw [← Real.exp_add, ← Real.exp_add]
    _ ≤ _ := Real.exp_le_exp.2 hfin
end GlobalTheory.ShortSpanComp
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @_root_.GlobalTheory.ShortSpanComp.short_span_comp_mem | exact _root_.GlobalTheory.ShortSpanComp.short_span_comp_mem | (intros; apply _root_.GlobalTheory.ShortSpanComp.short_span_comp_mem <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.short_span_composition_closed : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ Lb : ℝ, 1 ≤ Lb → Real.log Y.d.l₂.M ≤ 30 * Lb → fieldSz D.host.E ≤ 3 * Lb → Real.log (D.R.f * D.R.r) ≤ Lb → o ≤ 391 * (D.R.f * D.R.r * Lb) ^ 2 → ∀ c₁ : ℝ, GlobalTheory.FlatLine.FlatExistsAt Y.U (xiR D) c₁ → |c₁| ≤ 9 * D.R.r * Lb → ∀ la : AllWt.Weight (T.Q.Dw j), (∀ τ, Antitone (la τ)) → (∀ τ, ((8 * D.R.f * D.R.r + 10 : ℕ) : ℤ) ≤ gap (la τ) ((T.Q.Dw j).p - 1)) → Real.log (∑ τ, ∑ k, |(la τ k : ℝ)|) ≤ 10 * Lb → ∀ Z, ∃ s : Set (cuspOn Y.U Z (wtOf (T.Q.Dw j) la 0)), s ⊆ (latOn Y.U Z (wtOf (T.Q.Dw j) la 0) : Set (cuspOn Y.U Z (wtOf (T.Q.Dw j) la 0))) ∧ Submodule.span Y.d.c₂.F s = ⊤ ∧ ∀ y ∈ s, ∀ σ, normOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) la 0) σ y ≤ Real.exp (C * (((D.R.f : ℝ) * D.R.r * Lb) ^ 3 * (∑ τ, ∑ k, |(la τ k : ℝ)|) + ((D.R.f : ℝ) * D.R.r * Lb) ^ 5)) := by
  first | exact @_root_.GlobalTheory.ShortSpanComp.short_span_comp_mem | exact _root_.GlobalTheory.ShortSpanComp.short_span_comp_mem | (intros; apply _root_.GlobalTheory.ShortSpanComp.short_span_comp_mem <;> assumption)
end
