import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsSwap
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

section MixedDisc

variable {D : ℕ}

/- English proof (translation)
Unfold `mixedDisc`. Use `congr 1`. Use `Fintype.sum_equiv (Equiv.finsetCongr σ) _ _ fun S => ?_` and prove the remaining obligations. Rewrite using `[Equiv.finsetCongr_apply, Finset.card_map, Finset.sum_map]`. Both sides reduce to the same expression.
-/
theorem mixedDisc_comp_perm (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (σ : Equiv.Perm (Fin D)) :
    mixedDisc (A ∘ σ) = mixedDisc A := by
  unfold mixedDisc
  congr 1
  refine Fintype.sum_equiv (Equiv.finsetCongr σ) _ _ fun S => ?_
  rw [Equiv.finsetCongr_apply, Finset.card_map, Finset.sum_map]
  rfl

/- English proof (translation)
Unfold `maDensity`. Rewrite using `[show (fun k => cxHessian ((φ ∘ σ) k) z) = (fun k => cxHessian (φ k) z) ∘ σ from rfl, mixedDisc_comp_perm]`.
-/
theorem maDensity_comp_perm (φ : Fin D → (Fin D → ℂ) → ℝ) (σ : Equiv.Perm (Fin D)) (z : Fin D → ℂ) :
    maDensity (φ ∘ σ) z = maDensity φ z := by
  unfold maDensity
  rw [show (fun k => cxHessian ((φ ∘ σ) k) z) = (fun k => cxHessian (φ k) z) ∘ σ from rfl,
    mixedDisc_comp_perm]

end MixedDisc

section Integral

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

omit [∀ k, Fintype (ι k)] in

/- English proof (translation)
Unfold `ptsIntegral`. Use `split_ifs with h`. Unfold `ptsIntegralAt`. Use `congr 1`. Use function extensionality and compare the values at `y`.

Use `finsum_congr fun w => finsum_congr fun _ => ?_` and prove the remaining obligations. Unfold `sheetDensity`. Use `split_ifs with hγ`. Use `congr 1`. Conclude with `maDensity_comp_perm (fun j y' => φ j (hγ.choose y')) σ y`.

Both sides reduce to the same expression. Both sides reduce to the same expression.
-/
theorem ptsIntegral_comp_perm (P : Ideal (MRing ι)) {e : ℕ} (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    (σ : Equiv.Perm (Fin e)) (g : ((Σ k, ι k) → ℂ) → ℝ) :
    ptsIntegral P (φ ∘ σ) g = ptsIntegral P φ g := by
  unfold ptsIntegral
  split_ifs with h
  · unfold ptsIntegralAt
    congr 1
    funext y
    refine finsum_congr fun w => finsum_congr fun _ => ?_
    unfold sheetDensity
    split_ifs with hγ
    · congr 1
      exact maDensity_comp_perm (fun j y' => φ j (hγ.choose y')) σ y
    · rfl
  · rfl

end Integral

section Krull

variable {R : Type*} [CommRing R] [IsNoetherianRing R]

/- English proof (translation)
Establish `hWp : W.IsPrime` using `hW.isPrime`. Establish `h1` using `Ideal.map_height_le_one_of_mem_minimalPrimes hW`. Use `set q := Ideal.Quotient.mk V`. Establish `hker : RingHom.ker q = V` using `Ideal.mk_ker`. Establish `hW'm : (W'.map q).IsPrime` using `Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [hker]; exact hVW'.le)`.

Establish `hWm : (W.map q).IsPrime` using `Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [hker]; exact hVW'.le.trans hW'W.le)`. Establish `hlt : W'.map q < W.map q`. Use `lt_of_le_of_ne (Ideal.map_mono hW'W.le) fun he => hW'W.ne ?_` and prove the remaining obligations. Use `congrArg (Ideal.comap q) he` as an intermediate fact. Rewrite `this` using `[Ideal.comap_map_of_surjective' q Ideal.Quotient.mk_surjective, Ideal.comap_map_of_surjective' q Ideal.Quotient.mk_surjective, hker, sup_eq_left.mpr hVW'.le, sup_eq_left.mpr (hVW'.le.trans hW'W.le)]`. Then use the resulting hypothesis.

Establish `h2` using `Ideal.height_add_one_le_of_lt_of_isPrime hlt`. Establish `h0 : (W'.map q).height = 0`. Establish `h3` using `h2.trans h1`. Generalize the expression as in `(W'.map q).height = a at h3`. Consider the cases of `a with`.

Consider the case `top => simp at h3`. Consider the case `coe a => norm_cast at h3 ⊢`. Use linear arithmetic over natural numbers and integers. Establish `: IsDomain (R ⧸ V)` using `Ideal.Quotient.isDomain V`. Rewrite `h0` using `[Ideal.height_eq_zero_iff_eq_bot]`.

Apply `hVW'.ne` to reduce the goal to its premises. Apply `le_antisymm hVW'.le` to reduce the goal to its premises. Introduce `y hy`. Establish `: q y ∈ W'.map q` using `Ideal.mem_map_of_mem q hy`. Rewrite `this` using `[h0, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]`.

Conclude with `this`.
-/
theorem not_lt_lt_of_mem_minimalPrimes' {V W W' : Ideal R} [V.IsPrime] [W'.IsPrime] {x : R}
    (hW : W ∈ (V ⊔ Ideal.span {x}).minimalPrimes) (hVW' : V < W') (hW'W : W' < W) : False := by
  have hWp : W.IsPrime := hW.isPrime
  have h1 := Ideal.map_height_le_one_of_mem_minimalPrimes hW
  set q := Ideal.Quotient.mk V
  have hker : RingHom.ker q = V := Ideal.mk_ker
  have hW'm : (W'.map q).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [hker]; exact hVW'.le)
  have hWm : (W.map q).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by rw [hker]; exact hVW'.le.trans hW'W.le)
  have hlt : W'.map q < W.map q := by
    refine lt_of_le_of_ne (Ideal.map_mono hW'W.le) fun he => hW'W.ne ?_
    have := congrArg (Ideal.comap q) he
    rwa [Ideal.comap_map_of_surjective' q Ideal.Quotient.mk_surjective,
      Ideal.comap_map_of_surjective' q Ideal.Quotient.mk_surjective, hker,
      sup_eq_left.mpr hVW'.le, sup_eq_left.mpr (hVW'.le.trans hW'W.le)] at this
  have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  have h0 : (W'.map q).height = 0 := by
    have h3 := h2.trans h1
    generalize (W'.map q).height = a at h3
    cases a with
    | top => simp at h3
    | coe a => norm_cast at h3 ⊢; omega
  have : IsDomain (R ⧸ V) := Ideal.Quotient.isDomain V
  rw [Ideal.height_eq_zero_iff_eq_bot] at h0
  apply hVW'.ne
  apply le_antisymm hVW'.le
  intro y hy
  have : q y ∈ W'.map q := Ideal.mem_map_of_mem q hy
  rw [h0, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at this
  exact this

/- English proof (translation)
Establish `hWp : W.IsPrime` using `hW.1.1`. Use `⟨⟨hWp, sup_le (le_sup_left.trans hW.1.2) (Ideal.span_le.mpr (by simpa using htW))⟩, fun q hq hqW => ?_⟩` and prove the remaining obligations. Establish `: q.IsPrime` using `hq.1`. Establish `hPq : P < q` using `lt_of_le_of_ne (le_sup_left.trans hq.2) fun he => htP (he ▸ hq.2 (le_sup_right (a := P) (Ideal.subset_span rfl)))`. Break down `hqW.lt_or_eq with hlt | heq` into its components or cases.

Conclude with `(not_lt_lt_of_mem_minimalPrimes' hW hPq hlt).elim`. Conclude with `heq.ge`.
-/
theorem mem_minimalPrimes_of_mem {P W : Ideal R} [P.IsPrime] {s t : R}
    (hW : W ∈ (P ⊔ Ideal.span {s}).minimalPrimes) (htP : t ∉ P) (htW : t ∈ W) :
    W ∈ (P ⊔ Ideal.span {t}).minimalPrimes := by
  have hWp : W.IsPrime := hW.1.1
  refine ⟨⟨hWp, sup_le (le_sup_left.trans hW.1.2) (Ideal.span_le.mpr (by simpa using htW))⟩,
    fun q hq hqW => ?_⟩
  have : q.IsPrime := hq.1
  have hPq : P < q := lt_of_le_of_ne (le_sup_left.trans hq.2) fun he =>
    htP (he ▸ hq.2 (le_sup_right (a := P) (Ideal.subset_span rfl)))
  rcases hqW.lt_or_eq with hlt | heq
  · exact (not_lt_lt_of_mem_minimalPrimes' hW hPq hlt).elim
  · exact heq.ge

end Krull

section Cycles

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

/- English proof (translation)
Assemble the required witnesses or components as `⟨mem_minimalPrimes_of_mem hW.1 htP htW, hW.2⟩`.
-/
theorem mem_divSupp_of_mem {P W : Ideal (MRing ι)} [P.IsPrime] {s t : MRing ι}
    (hW : W ∈ divSupp P s) (htP : t ∉ P) (htW : t ∈ W) : W ∈ divSupp P t :=
  ⟨mem_minimalPrimes_of_mem hW.1 htP htW, hW.2⟩

/- English proof (translation)
Simplify using `only [divCycle, Finsupp.ofSupportFinite_coe]`. Rewrite using `[if_pos h]`.
-/
theorem divCycle_apply_of_mem {P W : Ideal (MRing ι)} {s : MRing ι} (h : W ∈ divSupp P s) :
    divCycle P s W = multAt (P ⊔ Ideal.span {s}) W := by
  classical
  simp only [divCycle, Finsupp.ofSupportFinite_coe]
  rw [if_pos h]

/- English proof (translation)
Simplify using `only [divCycle, Finsupp.ofSupportFinite_coe]`. Rewrite using `[if_neg h]`.
-/
theorem divCycle_apply_of_not_mem {P W : Ideal (MRing ι)} {s : MRing ι} (h : W ∉ divSupp P s) :
    divCycle P s W = 0 := by
  classical
  simp only [divCycle, Finsupp.ofSupportFinite_coe]
  rw [if_neg h]

/- English proof (translation)
Rewrite using `[finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite P s), Finsupp.sum]`. Establish `h1 : ∀ W ∈ (divSupp_finite P s).toFinset, (multAt (P ⊔ Ideal.span {s}) W : ℝ) * f W = (divCycle P s W : ℝ) * f W`. Introduce `W hW`. Rewrite `hW` using `[Set.Finite.mem_toFinset]`. Rewrite using `[divCycle_apply_of_mem hW]`.

Rewrite using `[Finset.sum_congr rfl h1]`. Use `symm`. Use `Finset.sum_subset (fun W hW => ?_) (fun W _ hW => ?_)` and prove the remaining obligations. Rewrite using `[Set.Finite.mem_toFinset]`. Assume the negation of the conclusion as `h`.

Conclude with `(Finsupp.mem_support_iff.mp hW) (divCycle_apply_of_not_mem h)`. Rewrite using `[Finsupp.notMem_support_iff.mp hW]`. Simplify using the standard rewrite rules.
-/
theorem finsum_divSupp_eq_sum (P : Ideal (MRing ι)) (s : MRing ι) (f : Ideal (MRing ι) → ℝ) :
    ∑ᶠ W ∈ divSupp P s, (multAt (P ⊔ Ideal.span {s}) W : ℝ) * f W =
      (divCycle P s).sum fun W m => (m : ℝ) * f W := by
  classical
  rw [finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite P s), Finsupp.sum]
  have h1 : ∀ W ∈ (divSupp_finite P s).toFinset,
      (multAt (P ⊔ Ideal.span {s}) W : ℝ) * f W = (divCycle P s W : ℝ) * f W := by
    intro W hW
    rw [Set.Finite.mem_toFinset] at hW
    rw [divCycle_apply_of_mem hW]
  rw [Finset.sum_congr rfl h1]
  symm
  refine Finset.sum_subset (fun W hW => ?_) (fun W _ hW => ?_)
  · rw [Set.Finite.mem_toFinset]
    by_contra h
    exact (Finsupp.mem_support_iff.mp hW) (divCycle_apply_of_not_mem h)
  · rw [Finsupp.notMem_support_iff.mp hW]
    simp

open Classical in

/- English proof (translation)
Rewrite using `[finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite P s), finsum_cond_eq_sum_of_cond_iff g (t := (divSupp_finite P s).toFinset.filter IsHorizontal) (fun {x} _ => by simp), Finset.sum_filter]`.
-/
theorem finsum_hor_eq (P : Ideal (MRing ι)) (s : MRing ι) (g : Ideal (MRing ι) → ℝ) :
    (∑ᶠ (W) (_ : W ∈ divSupp P s ∧ IsHorizontal W), g W) =
      ∑ᶠ W ∈ divSupp P s, (if IsHorizontal W then g W else 0) := by
  classical
  rw [finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite P s),
    finsum_cond_eq_sum_of_cond_iff g (t := (divSupp_finite P s).toFinset.filter IsHorizontal)
      (fun {x} _ => by simp), Finset.sum_filter]

/- English proof (translation)
Rewrite using `[Finsupp.sum_sum_index (fun _ => by simp) (fun _ _ _ => by push_cast; ring)]`. Use `Finsupp.sum_congr fun W _ => ?_` and prove the remaining obligations. Rewrite using `[Finsupp.sum_smul_index' (fun _ => by simp), Finsupp.mul_sum]`. Use `Finsupp.sum_congr fun U _ => ?_` and prove the remaining obligations. Simplify using `only [smul_eq_mul, Nat.cast_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_cycle_comp {α : Type*} (F : α →₀ ℕ) (G : α → α →₀ ℕ) (c : α → ℝ) :
    (F.sum fun W m => (m : ℝ) * (G W).sum fun U k => (k : ℝ) * c U) =
      (F.sum fun W m => m • G W).sum fun U k => (k : ℝ) * c U := by
  rw [Finsupp.sum_sum_index (fun _ => by simp) (fun _ _ _ => by push_cast; ring)]
  refine Finsupp.sum_congr fun W _ => ?_
  rw [Finsupp.sum_smul_index' (fun _ => by simp), Finsupp.mul_sum]
  refine Finsupp.sum_congr fun U _ => ?_
  simp only [smul_eq_mul, Nat.cast_mul]
  ring

omit [Fintype K] [∀ k, Fintype (ι k)] in

/- English proof (translation)
Establish `hmax : (W.comap (C : ℤ →+* MRing ι)).IsMaximal` using `Ideal.IsPrime.isMaximal (Ideal.comap_isPrime _ _) hv`. Conclude with `(hmax.eq_of_le (Ideal.comap_isPrime (C : ℤ →+* MRing ι) U).ne_top (Ideal.comap_mono hWU)).symm`.
-/
theorem comap_eq_of_vertical {W U : Ideal (MRing ι)} [W.IsPrime] [U.IsPrime] (hv : ¬ IsHorizontal W)
    (hWU : W ≤ U) : U.comap (C : ℤ →+* MRing ι) = W.comap (C : ℤ →+* MRing ι) := by
  have hmax : (W.comap (C : ℤ →+* MRing ι)).IsMaximal :=
    Ideal.IsPrime.isMaximal (Ideal.comap_isPrime _ _) hv
  exact (hmax.eq_of_le (Ideal.comap_isPrime (C : ℤ →+* MRing ι) U).ne_top (Ideal.comap_mono hWU)).symm

end Cycles

/- English proof (translation)
Introduce `K _ ι _ I P n L A A' s s' hR hP hL hA hA' hs hs' hd`. Establish `: P.IsPrime` using `hP.2.1.1`. Take `⟨b, hb, hsb, hsP⟩` from `id hs`. Take `⟨b', hb', hsb', hsP'⟩` from `id hs'`. Use `set c : Ideal (MRing ι) → ℝ := fun U => if IsHorizontal U then I U n L else (geoNum n U (fun j => (L j).a) : ℝ) * Real.log (charOf U) with hc`.

Establish `key : ∀ (B B' : HermLine ι) (u u' : MRing ι) (e' : K → ℕ), IsSectionOn P B u → IsSmoothHerm B' → (∀ k, B'.a k = e' k) → IsMultiHomog u' e' → (∀ W ∈ divSupp P u, u' ∉ W) → ∀ W ∈ divSupp P u, (if IsHorizontal W then I W (n + 1) (Fin.snoc L B') else (geoNum (n + 1) W (fun j => ((Fin …`. Introduce `B B' u u' e' hsec hB' hB'e hu'e hno W hW`. Establish `hdiv` using `divSuppArith K ι P (n + 1) B u W hP hsec hW`. Establish `hu'W : u' ∉ W` using `hno W hW`. Establish `: W.IsPrime` using `hW.1.1.1`.

Distinguish the cases in `hh : IsHorizontal W`. Rewrite using `[if_pos hh, if_pos hh, hR W L B' u' (hdiv.1 hh) hL hB' ⟨e', hB'e, hu'e, hu'W⟩, show recR I W L B' u' = (∑ᶠ U ∈ divSupp W u', (multAt (W ⊔ Ideal.span {u'}) U : ℝ) * c U) - arInt W u' B' L from rfl, finsum_divSupp_eq_sum]`. Rewrite using `[if_neg hh, if_neg hh, sub_zero]`. Take `⟨hWm, hWp, hWd⟩` from `hdiv.2 hh`. Establish `ha : (fun j => ((Fin.snoc L B' : Fin (n + 1) → HermLine ι) j).a) = Fin.snoc (fun j => (L j).a) (fun k => (e' k : ℤ))`.

Use function extensionality and compare the values at `j`. Use `Fin.lastCases ?_ (fun i => ?_) j` and prove the remaining obligations. Use function extensionality and compare the values at `k`. Simplify using `[hB'e]`. Simplify using the standard rewrite rules.

Rewrite using `[ha, hCut K ι W n (fun j => (L j).a) e' u' hWm hWp hWd hu'e hu'W, ← finsum_divSupp_eq_sum W u' c, finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite W u'), finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite W u'), Int.cast_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun U hU => ?_` and prove the remaining obligations. Rewrite `hU` using `[Set.Finite.mem_toFinset]`. Establish `: U.IsPrime` using `hU.1.1.1`. Establish `hWU : W ≤ U` using `le_sup_left.trans hU.1.1.2`.

Establish `hcm` using `comap_eq_of_vertical hh hWU`. Establish `hUh : ¬ IsHorizontal U`. Unfold `IsHorizontal`. Rewrite using `[hcm]`. Conclude with `hh`.

Establish `hch : charOf U = charOf W` using `congrArg (fun J : Ideal ℤ => (Submodule.IsPrincipal.generator J).natAbs) hcm`. Rewrite using `[hc]`. Simplify using `only [if_neg hUh, hch]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hs'W : ∀ W ∈ divSupp P s, s' ∉ W` using `fun W hW h => hd W hW (mem_divSupp_of_mem hW hsP' h)`. Establish `hsW' : ∀ W ∈ divSupp P s', s ∉ W` using `fun W hW h => hd W (mem_divSupp_of_mem hW hsP h) hW`. Establish `side : ∀ (B B' : HermLine ι) (u u' : MRing ι) (e' : K → ℕ), IsSectionOn P B u → IsSmoothHerm B' → (∀ k, B'.a k = e' k) → IsMultiHomog u' e' → (∀ W ∈ divSupp P u, u' ∉ W) → recR I P (Fin.snoc L B') B u = ((divCycle P u).sum fun W m => m • divCycle W u').sum (fun U k => (k : ℝ) * c …`. Introduce `B B' u u' e' hsec hB' hB'e hu'e hno`. Establish `hperm : (Fin.cons (fun z => Real.log (B'.h z)) (pot L) : Fin (n + 1) → _) = (fun j z => Real.log (((Fin.snoc L B' : Fin (n + 1) → HermLine ι) j).h z)) ∘ (finRotate (n + 1)).symm`.

Use function extensionality and compare the values at `i`. Use `Fin.cases ?_ (fun j => ?_) i` and prove the remaining obligations. Establish `h0 : (finRotate (n + 1)).symm 0 = Fin.last n` using `(Equiv.symm_apply_eq _).mpr finRotate_last.symm`. Simplify using `[h0]`. Establish `h1 : (finRotate (n + 1)).symm j.succ = j.castSucc` using `(Equiv.symm_apply_eq _).mpr (Fin.ext (by`.

Rewrite using `[coe_finRotate_of_ne_last (Fin.castSucc_lt_last j).ne]`. Use the proof step `simp))`. Simplify using `[h1]`. Both sides reduce to the same expression. Establish `hint : arInt P u B (Fin.snoc L B') = ptsIntegral P (Fin.cons (fun z => Real.log (B'.h z)) (pot L)) (logNorm B u)`.

Rewrite using `[hperm, ptsIntegral_comp_perm]`. Both sides reduce to the same expression. Establish `hrec : recR I P (Fin.snoc L B') B u = (∑ᶠ W ∈ divSupp P u, (multAt (P ⊔ Ideal.span {u}) W : ℝ) * ((divCycle W u').sum (fun U m => (m : ℝ) * c U) - (if IsHorizontal W then arInt W u' B' L else 0))) - arInt P u B (Fin.snoc L B')`. Unfold `recR`. Use `congr 1`.

Use `finsum_congr fun W => finsum_congr fun hW => ?_` and prove the remaining obligations. Rewrite using `[key B B' u u' e' hsec hB' hB'e hu'e hno W hW]`. Establish `hhor : (∑ᶠ W ∈ divSupp P u, if IsHorizontal W then (multAt (P ⊔ Ideal.span {u}) W : ℝ) * ptsIntegral W (pot L) (logNorm B' u') else 0) = ∑ᶠ W ∈ divSupp P u, (multAt (P ⊔ Ideal.span {u}) W : ℝ) * (if IsHorizontal W then arInt W u' B' L else 0)` using `finsum_congr fun W => finsum_congr fun _ => by rw [mul_ite, mul_zero]; rfl`. Rewrite using `[hrec, hint, finsum_divSupp_eq_sum, finsum_hor_eq, hhor, finsum_divSupp_eq_sum]`. Simplify using `only [mul_sub, Finsupp.sum_sub]`.

Rewrite using `[sum_cycle_comp]`. Rewrite using `[side A A' s s' b' hs hA' hb' hsb' hs'W, side A' A s' s b hs' hA hb hsb hsW', hCyc K ι P n A A' s s' hP hs hs' hd]`. Establish `h` using `hPL2 K ι P n L A A' s s' hP hL hA hA' hs hs' (fun W h1 h2 _ => hd W h1 h2)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem Swap.of_cycles (hCut : GeoNumCut.Statement) (hPL2 : SectionSpaceSymmetry)
    (hCyc : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ)
      (A A' : HermLine ι) (s s' : MRing ι), IsArithVar P (n + 2) → IsSectionOn P A s →
      IsSectionOn P A' s' → (∀ W, W ∈ divSupp P s → W ∉ divSupp P s') →
      ((divCycle P s).sum fun W m => m • divCycle W s') = (divCycle P s').sum fun W m => m • divCycle W s) :
    Swap.Statement := by
  intro K _ ι _ I P n L A A' s s' hR hP hL hA hA' hs hs' hd
  classical
  have : P.IsPrime := hP.2.1.1
  obtain ⟨b, hb, hsb, hsP⟩ := id hs
  obtain ⟨b', hb', hsb', hsP'⟩ := id hs'
  set c : Ideal (MRing ι) → ℝ := fun U => if IsHorizontal U then I U n L
    else (geoNum n U (fun j => (L j).a) : ℝ) * Real.log (charOf U) with hc

  have key : ∀ (B B' : HermLine ι) (u u' : MRing ι) (e' : K → ℕ), IsSectionOn P B u → IsSmoothHerm B' →
      (∀ k, B'.a k = e' k) → IsMultiHomog u' e' → (∀ W ∈ divSupp P u, u' ∉ W) → ∀ W ∈ divSupp P u,
      (if IsHorizontal W then I W (n + 1) (Fin.snoc L B')
        else (geoNum (n + 1) W (fun j => ((Fin.snoc L B' : Fin (n + 1) → HermLine ι) j).a) : ℝ) *
          Real.log (charOf W)) =
        (divCycle W u').sum (fun U m => (m : ℝ) * c U) -
          (if IsHorizontal W then arInt W u' B' L else 0) := by
    intro B B' u u' e' hsec hB' hB'e hu'e hno W hW
    have hdiv := divSuppArith K ι P (n + 1) B u W hP hsec hW
    have hu'W : u' ∉ W := hno W hW
    have : W.IsPrime := hW.1.1.1
    by_cases hh : IsHorizontal W
    · rw [if_pos hh, if_pos hh, hR W L B' u' (hdiv.1 hh) hL hB' ⟨e', hB'e, hu'e, hu'W⟩,
        show recR I W L B' u' = (∑ᶠ U ∈ divSupp W u', (multAt (W ⊔ Ideal.span {u'}) U : ℝ) * c U) -
          arInt W u' B' L from rfl, finsum_divSupp_eq_sum]
    · rw [if_neg hh, if_neg hh, sub_zero]
      obtain ⟨hWm, hWp, hWd⟩ := hdiv.2 hh
      have ha : (fun j => ((Fin.snoc L B' : Fin (n + 1) → HermLine ι) j).a) =
          Fin.snoc (fun j => (L j).a) (fun k => (e' k : ℤ)) := by
        funext j
        refine Fin.lastCases ?_ (fun i => ?_) j
        · funext k
          simp [hB'e]
        · simp
      rw [ha, hCut K ι W n (fun j => (L j).a) e' u' hWm hWp hWd hu'e hu'W,
        ← finsum_divSupp_eq_sum W u' c, finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite W u'),
        finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite W u'), Int.cast_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun U hU => ?_
      rw [Set.Finite.mem_toFinset] at hU
      have : U.IsPrime := hU.1.1.1
      have hWU : W ≤ U := le_sup_left.trans hU.1.1.2
      have hcm := comap_eq_of_vertical hh hWU
      have hUh : ¬ IsHorizontal U := by
        unfold IsHorizontal
        rw [hcm]
        exact hh
      have hch : charOf U = charOf W :=
        congrArg (fun J : Ideal ℤ => (Submodule.IsPrincipal.generator J).natAbs) hcm
      rw [hc]
      simp only [if_neg hUh, hch]
      push_cast
      ring
  have hs'W : ∀ W ∈ divSupp P s, s' ∉ W := fun W hW h => hd W hW (mem_divSupp_of_mem hW hsP' h)
  have hsW' : ∀ W ∈ divSupp P s', s ∉ W := fun W hW h => hd W (mem_divSupp_of_mem hW hsP h) hW

  have side : ∀ (B B' : HermLine ι) (u u' : MRing ι) (e' : K → ℕ), IsSectionOn P B u →
      IsSmoothHerm B' → (∀ k, B'.a k = e' k) → IsMultiHomog u' e' → (∀ W ∈ divSupp P u, u' ∉ W) →
      recR I P (Fin.snoc L B') B u =
        ((divCycle P u).sum fun W m => m • divCycle W u').sum (fun U k => (k : ℝ) * c U) -
          (∑ᶠ (W) (_ : W ∈ divSupp P u ∧ IsHorizontal W),
            (multAt (P ⊔ Ideal.span {u}) W : ℝ) * ptsIntegral W (pot L) (logNorm B' u')) -
          ptsIntegral P (Fin.cons (fun z => Real.log (B'.h z)) (pot L)) (logNorm B u) := by
    intro B B' u u' e' hsec hB' hB'e hu'e hno
    have hperm : (Fin.cons (fun z => Real.log (B'.h z)) (pot L) : Fin (n + 1) → _) =
        (fun j z => Real.log (((Fin.snoc L B' : Fin (n + 1) → HermLine ι) j).h z)) ∘
          (finRotate (n + 1)).symm := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · have h0 : (finRotate (n + 1)).symm 0 = Fin.last n :=
          (Equiv.symm_apply_eq _).mpr finRotate_last.symm
        simp [h0]
      · have h1 : (finRotate (n + 1)).symm j.succ = j.castSucc :=
          (Equiv.symm_apply_eq _).mpr (Fin.ext (by
            rw [coe_finRotate_of_ne_last (Fin.castSucc_lt_last j).ne]
            simp))
        simp [h1]
        rfl
    have hint : arInt P u B (Fin.snoc L B') =
        ptsIntegral P (Fin.cons (fun z => Real.log (B'.h z)) (pot L)) (logNorm B u) := by
      rw [hperm, ptsIntegral_comp_perm]
      rfl
    have hrec : recR I P (Fin.snoc L B') B u =
        (∑ᶠ W ∈ divSupp P u, (multAt (P ⊔ Ideal.span {u}) W : ℝ) *
          ((divCycle W u').sum (fun U m => (m : ℝ) * c U) -
            (if IsHorizontal W then arInt W u' B' L else 0))) - arInt P u B (Fin.snoc L B') := by
      unfold recR
      congr 1
      refine finsum_congr fun W => finsum_congr fun hW => ?_
      rw [key B B' u u' e' hsec hB' hB'e hu'e hno W hW]
    have hhor : (∑ᶠ W ∈ divSupp P u, if IsHorizontal W then
          (multAt (P ⊔ Ideal.span {u}) W : ℝ) * ptsIntegral W (pot L) (logNorm B' u') else 0) =
        ∑ᶠ W ∈ divSupp P u, (multAt (P ⊔ Ideal.span {u}) W : ℝ) *
          (if IsHorizontal W then arInt W u' B' L else 0) :=
      finsum_congr fun W => finsum_congr fun _ => by rw [mul_ite, mul_zero]; rfl
    rw [hrec, hint, finsum_divSupp_eq_sum, finsum_hor_eq, hhor, finsum_divSupp_eq_sum]
    simp only [mul_sub, Finsupp.sum_sub]
    rw [sum_cycle_comp]
  rw [side A A' s s' b' hs hA' hb' hsb' hs'W, side A' A s' s b hs' hA hb hsb hsW',
    hCyc K ι P n A A' s s' hP hs hs' hd]
  have h := hPL2 K ι P n L A A' s s' hP hL hA hA' hs hs' (fun W h1 h2 _ => hd W h1 h2)
  linarith

/- English proof (translation)
The claim follows from `Swap.of_cycles hCut hPL2 fun K _ ι _ P n _ _ s s' hP hs hs' hd => hCyc K ι P (n + 2) hs.choose hs'.choose s s' hP hs.choose_spec.2.1 hs'.choose_spec.2.1 hs.choose_spec.2.2 hs'.choose_spec.2.2 hd`.
-/
theorem Swap.proof (hCyc : SwapCycles.Statement) (hCut : GeoNumCut.Statement) (hPL2 : SectionSpaceSymmetry) :
    Swap.Statement :=
  Swap.of_cycles hCut hPL2 fun K _ ι _ P n _ _ s s' hP hs hs' hd =>
    hCyc K ι P (n + 2) hs.choose hs'.choose s s' hP hs.choose_spec.2.1 hs'.choose_spec.2.1
      hs.choose_spec.2.2 hs'.choose_spec.2.2 hd

end

end GroundTheory.Heights₂.Heights.Inter
