import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsAddBlockIsometric
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionPointValue
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsSemilocRing
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.LiftOldChartMonomialMemPrimeCompl
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ImageCoord
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry SectionBounded SectionPointValue

noncomputable section

set_option linter.unusedSectionVars false

namespace AddBlockIsometric

section Cycle

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Simplify using `only [divCycle, Finsupp.ofSupportFinite_coe]`. Rewrite using `[if_neg]`. Introduce `hW`. Simplify using `only [divSupp, Set.mem_ofPred_eq] at hW`. Conclude with `h ⟨hW.1.1.1, hW.2, le_sup_left.trans hW.1.1.2⟩`.
-/
theorem divCycle_eq_zero_of_not {P W : Ideal (MRing ι)} (f : MRing ι)
    (h : ¬ (W.IsPrime ∧ IsRelevant W ∧ P ≤ W)) : divCycle P f W = 0 := by
  simp only [divCycle, Finsupp.ofSupportFinite_coe]
  rw [if_neg]
  intro hW
  simp only [divSupp, Set.mem_ofPred_eq] at hW
  exact h ⟨hW.1.1.1, hW.2, le_sup_left.trans hW.1.1.2⟩

/- English proof (translation)
Use `set J := P ⊔ Ideal.span {f * g'} with hJdef`. Establish `hfg : f * g' ∈ J` using `Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)`. Establish `hIJ : P ≤ J` using `le_sup_left`. Establish `hf'g : f' * g ∈ J`. Establish `h` using `J.sub_mem hfg (hIJ hrel)`.

Rewrite `h` using `[sub_sub_cancel]`. Then use the resulting hypothesis. Establish `h1 : J ≤ P ⊔ Ideal.span {f}` using `sup_le le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_sup_right (Ideal.mul_mem_right g' _ (Ideal.mem_span_singleton_self f))))`. Establish `h2 : J ≤ P ⊔ Ideal.span {g}`. Use `sup_le le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr ?_)` and prove the remaining obligations. Establish `h` using `Ideal.add_mem _ (Ideal.mem_sup_left hrel : _ ∈ P ⊔ Ideal.span {g}) (Ideal.mem_sup_right (Ideal.mul_mem_left _ f' (Ideal.mem_span_singleton_self g)) : _ ∈ P ⊔ Ideal.span {g})`.

Rewrite `h` using `[sub_add_cancel]`. Then use the resulting hypothesis. Establish `hm1 : ∀ x ∈ P ⊔ Ideal.span {f}, g' * x ∈ J`. Introduce `x hx`. Take `⟨i, hi, y, hy, rfl⟩` from `Submodule.mem_sup.mp hx`. Take `⟨r, rfl⟩` from `Ideal.mem_span_singleton'.mp hy`.

Rewrite using `[mul_add, show g' * (r * f) = r * (f * g') by ring]`. Conclude with `J.add_mem (hIJ (P.mul_mem_left _ hi)) (J.mul_mem_left _ hfg)`. Establish `hm2 : ∀ x ∈ P ⊔ Ideal.span {g}, f' * x ∈ J`. Introduce `x hx`. Take `⟨i, hi, y, hy, rfl⟩` from `Submodule.mem_sup.mp hx`.

Take `⟨r, rfl⟩` from `Ideal.mem_span_singleton'.mp hy`. Rewrite using `[mul_add, show f' * (r * g) = r * (f' * g) by ring]`. Conclude with `J.add_mem (hIJ (P.mul_mem_left _ hi)) (J.mul_mem_left _ hf'g)`. Establish `e1` using `SectionCycle.mem_minimalPrimes_iff h1 hg' hm1`. Establish `e2` using `SectionCycle.mem_minimalPrimes_iff h2 hf' hm2`.

Establish `l1` using `SectionCycle.length_localized_eq h1 hg' hm1`. Establish `l2` using `SectionCycle.length_localized_eq h2 hf' hm2`. Simplify using `only [divCycle, Finsupp.ofSupportFinite_coe]`. Distinguish the cases in `hc : W ∈ divSupp P f`. Establish `hc' : W ∈ divSupp P g`.

Simplify using `only [divSupp, Set.mem_ofPred_eq] at hc ⊢`. Conclude with `⟨e2.mp (e1.mpr hc.1), hc.2⟩`. Rewrite using `[if_pos hc, if_pos hc', multAt, multAt, dif_pos hW, dif_pos hW]`. Conclude with `congrArg ENat.toNat (l1.symm.trans l2)`. Establish `hc' : W ∉ divSupp P g`.

Introduce `h`. Simplify using `only [divSupp, Set.mem_ofPred_eq] at hc h`. Conclude with `hc ⟨e1.mp (e2.mpr h.1), h.2⟩`. Rewrite using `[if_neg hc, if_neg hc']`.
-/
theorem divCycle_apply_eq_of_cross (P : Ideal (MRing ι)) {f g f' g' : MRing ι} {W : Ideal (MRing ι)} [hW : W.IsPrime]
    (hf' : f' ∉ W) (hg' : g' ∉ W) (hrel : f * g' - f' * g ∈ P) : divCycle P f W = divCycle P g W := by
  set J := P ⊔ Ideal.span {f * g'} with hJdef
  have hfg : f * g' ∈ J := Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  have hIJ : P ≤ J := le_sup_left
  have hf'g : f' * g ∈ J := by
    have h := J.sub_mem hfg (hIJ hrel)
    rwa [sub_sub_cancel] at h
  have h1 : J ≤ P ⊔ Ideal.span {f} := sup_le le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr
    (Ideal.mem_sup_right (Ideal.mul_mem_right g' _ (Ideal.mem_span_singleton_self f))))
  have h2 : J ≤ P ⊔ Ideal.span {g} := by
    refine sup_le le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
    have h := Ideal.add_mem _ (Ideal.mem_sup_left hrel : _ ∈ P ⊔ Ideal.span {g})
      (Ideal.mem_sup_right (Ideal.mul_mem_left _ f' (Ideal.mem_span_singleton_self g)) :
        _ ∈ P ⊔ Ideal.span {g})
    rwa [sub_add_cancel] at h
  have hm1 : ∀ x ∈ P ⊔ Ideal.span {f}, g' * x ∈ J := by
    intro x hx
    obtain ⟨i, hi, y, hy, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    rw [mul_add, show g' * (r * f) = r * (f * g') by ring]
    exact J.add_mem (hIJ (P.mul_mem_left _ hi)) (J.mul_mem_left _ hfg)
  have hm2 : ∀ x ∈ P ⊔ Ideal.span {g}, f' * x ∈ J := by
    intro x hx
    obtain ⟨i, hi, y, hy, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    rw [mul_add, show f' * (r * g) = r * (f' * g) by ring]
    exact J.add_mem (hIJ (P.mul_mem_left _ hi)) (J.mul_mem_left _ hf'g)
  have e1 := SectionCycle.mem_minimalPrimes_iff h1 hg' hm1
  have e2 := SectionCycle.mem_minimalPrimes_iff h2 hf' hm2
  have l1 := SectionCycle.length_localized_eq h1 hg' hm1
  have l2 := SectionCycle.length_localized_eq h2 hf' hm2
  simp only [divCycle, Finsupp.ofSupportFinite_coe]
  by_cases hc : W ∈ divSupp P f
  · have hc' : W ∈ divSupp P g := by
      simp only [divSupp, Set.mem_ofPred_eq] at hc ⊢
      exact ⟨e2.mp (e1.mpr hc.1), hc.2⟩
    rw [if_pos hc, if_pos hc', multAt, multAt, dif_pos hW, dif_pos hW]
    exact congrArg ENat.toNat (l1.symm.trans l2)
  · have hc' : W ∉ divSupp P g := by
      intro h
      simp only [divSupp, Set.mem_ofPred_eq] at hc h
      exact hc ⟨e1.mp (e2.mpr h.1), h.2⟩
    rw [if_neg hc, if_neg hc']

/- English proof (translation)
Use extensionality with `W`. Distinguish the cases in `hW : W.IsPrime ∧ IsRelevant W ∧ P ≤ W`. Take `⟨hp, hr, hle⟩` from `hW`. Take `⟨f', g', hf', hg', hrel⟩` from `h W hp hr hle`. Conclude with `divCycle_apply_eq_of_cross P hf' hg' hrel`.

Rewrite using `[divCycle_eq_zero_of_not f hW, divCycle_eq_zero_of_not g hW]`.
-/
theorem divCycle_eq_of_forall_cross (P : Ideal (MRing ι)) {f g : MRing ι}
    (h : ∀ W : Ideal (MRing ι), W.IsPrime → IsRelevant W → P ≤ W →
      ∃ f' g' : MRing ι, f' ∉ W ∧ g' ∉ W ∧ f * g' - f' * g ∈ P) :
    divCycle P f = divCycle P g := by
  ext W
  by_cases hW : W.IsPrime ∧ IsRelevant W ∧ P ≤ W
  · obtain ⟨hp, hr, hle⟩ := hW
    obtain ⟨f', g', hf', hg', hrel⟩ := h W hp hr hle
    exact divCycle_apply_eq_of_cross P hf' hg' hrel
  · rw [divCycle_eq_zero_of_not f hW, divCycle_eq_zero_of_not g hW]

/- English proof (translation)
Use `show F ∈ RingHom.ker (mConeMap y) ↔ _`. Rewrite using `[RingHom.mem_ker]`. Use `erw [mConeMap_homog y hF]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Establish `hM : (∏ k, (MvPolynomial.X k : MvPolynomial K Ω) ^ d k) ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (MvPolynomial.X_ne_zero k)`. Conclude with `MvPolynomial.C_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hM)`. Introduce `h`. Rewrite using `[h, map_zero, zero_mul]`.
-/
theorem mem_iff {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) {F : MRing ι} {d : K → ℕ} (hF : IsMultiHomog F d) :
    F ∈ mCoordIdeal y ↔ aeval y F = 0 := by
  show F ∈ RingHom.ker (mConeMap y) ↔ _
  rw [RingHom.mem_ker]
  erw [mConeMap_homog y hF]
  constructor
  · intro h
    have hM : (∏ k, (MvPolynomial.X k : MvPolynomial K Ω) ^ d k) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (MvPolynomial.X_ne_zero k)
    exact MvPolynomial.C_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hM)
  · intro h
    rw [h, map_zero, zero_mul]

end Cycle

section Block

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

/- English proof (translation)
The claim follows from `Function.extend_apply' _ _ _ fun ⟨_, h⟩ => Option.some_ne_none _ h`.
-/
theorem extend_some_none {α : Type} [Zero α] (a : K → α) :
    Function.extend (some : K → Option K) a 0 none = 0 :=
  Function.extend_apply' _ _ _ fun ⟨_, h⟩ => Option.some_ne_none _ h

/- English proof (translation)
The claim follows from `(Option.some_injective K).extend_apply a 0 k`.
-/
theorem extend_some_some {α : Type} [Zero α] (a : K → α) (k : K) :
    Function.extend (some : K → Option K) a 0 (some k) = a k :=
  (Option.some_injective K).extend_apply a 0 k

/- English proof (translation)
Use `show _ ∈ RingHom.ker (mConeMap (addBlock y v))`. Rewrite using `[RingHom.mem_ker, Targets.ImageCoord.mConeMap_rename some (oldV N) (fun _ => rfl)]`. Establish `h0 : mConeMap (addBlock y v ∘ oldV N) F = 0` using `RingHom.mem_ker.mp hF`. Rewrite using `[h0, map_zero]`.
-/
theorem rename_mem {N : ℕ} {y : (Σ k, ι k) → Ω} (v : Fin N → Ω) {F : MRing ι} (hF : F ∈ mCoordIdeal y) :
    rename (oldV (ι := ι) N) F ∈ mCoordIdeal (addBlock y v) := by
  show _ ∈ RingHom.ker (mConeMap (addBlock y v))
  rw [RingHom.mem_ker, Targets.ImageCoord.mConeMap_rename some (oldV N) (fun _ => rfl)]
  have h0 : mConeMap (addBlock y v ∘ oldV N) F = 0 := RingHom.mem_ker.mp hF
  rw [h0, map_zero]

/- English proof (translation)
Rewrite using `[aeval_rename]`. Both sides reduce to the same expression.
-/
theorem aeval_rename_old {N : ℕ} (y : (Σ k, ι k) → Ω) (v : Fin N → Ω) (F : MRing ι) :
    aeval (addBlock y v) (rename (oldV (ι := ι) N) F) = aeval y F := by
  rw [aeval_rename]
  rfl

/- English proof (translation)
Rewrite using `[map_rename, eval_rename]`. Both sides reduce to the same expression.
-/
theorem eval_rename_old {N : ℕ} (z : (Σ k, addIdx ι N k) → ℂ) (F : MRing ι) :
    eval z (map (Int.castRingHom ℂ) (rename (oldV (ι := ι) N) F)) = eval (basePart₂ z) (map (Int.castRingHom ℂ) F) := by
  rw [map_rename, eval_rename]
  rfl

/- English proof (translation)
Introduce `h`. Rewrite `h` using `[chartMon, map_prod]`. Take `⟨k, -, hk⟩` from `(Ideal.IsPrime.prod_mem_iff).mp h`. Rewrite `hk` using `[map_pow, rename_X]`. Conclude with `hc k (hW.mem_of_pow_mem _ hk)`.
-/
theorem not_mem_rename_chartMon {N : ℕ} {W : Ideal (MRing (addIdx ι N))} [hW : W.IsPrime] {c : ∀ k, ι k}
    (hc : ∀ k, (X ⟨some k, c k⟩ : MRing (addIdx ι N)) ∉ W) (e : K → ℕ) :
    rename (oldV (ι := ι) N) (chartMon c e) ∉ W := by
  intro h
  rw [chartMon, map_prod] at h
  obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff).mp h
  rw [map_pow, rename_X] at hk
  exact hc k (hW.mem_of_pow_mem _ hk)

/- English proof (translation)
Take `⟨dg, dh, hg, hh, hd, hy⟩` from `r`. Take `⟨dg', dh', hg', hh', hd', hy'⟩` from `r'`. Establish `hb` using `isBlockMap_oldV (ι := ι) N`. Use `(mem_iff _ (homog_sub (homog_mul (homog_mul (homog_X _) (Inter.rename_isMultiHomog hb hh)) (Inter.rename_isMultiHomog hb hg')) (homog_congr (homog_mul (homog_mul (homog_X _) (Inter.rename_isMultiHomog hb hh')) (Inter.rename_isMultiHomog hb hg)) fun k => ?_))).mpr ?_` and prove the remaining obligations. Consider the cases of `k with`.

Consider the case `none => simp only [Pi.add_apply, extend_some_none]`. Consider the case `some k`. Simplify using `only [Pi.add_apply, extend_some_some]`. Establish `e1` using `hd k`. Establish `e2` using `hd' k`.

Use `zify`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[map_sub, map_mul, map_mul, map_mul, map_mul, aeval_X, aeval_X, aeval_rename_old, aeval_rename_old, aeval_rename_old, aeval_rename_old, hy, hy'] show v i * _ * (v i' * _) - v i' * _ * (v i * _) = 0`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cross_mem {N : ℕ} {y : (Σ k, ι k) → Ω} {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} {m : ℕ} {v : Fin N → Ω} {i i' : Fin N}
    {G H G' H' : MRing ι} (r : IsRep y A.a m (v i) G H) (r' : IsRep y A.a m (v i') G' H') :
    (X ⟨none, i⟩ : MRing (addIdx ι N)) * rename (oldV N) H * rename (oldV N) G' -
      X ⟨none, i'⟩ * rename (oldV N) H' * rename (oldV N) G ∈ mCoordIdeal (addBlock y v) := by
  obtain ⟨dg, dh, hg, hh, hd, hy⟩ := r
  obtain ⟨dg', dh', hg', hh', hd', hy'⟩ := r'
  have hb := isBlockMap_oldV (ι := ι) N
  refine (mem_iff _ (homog_sub (homog_mul (homog_mul (homog_X _) (Inter.rename_isMultiHomog hb hh))
    (Inter.rename_isMultiHomog hb hg')) (homog_congr (homog_mul (homog_mul (homog_X _)
      (Inter.rename_isMultiHomog hb hh')) (Inter.rename_isMultiHomog hb hg)) fun k => ?_))).mpr ?_
  · cases k with
    | none => simp only [Pi.add_apply, extend_some_none]
    | some k =>
      simp only [Pi.add_apply, extend_some_some]
      have e1 := hd k
      have e2 := hd' k
      zify
      linarith
  · rw [map_sub, map_mul, map_mul, map_mul, map_mul, aeval_X, aeval_X, aeval_rename_old, aeval_rename_old,
      aeval_rename_old, aeval_rename_old, hy, hy']
    show v i * _ * (v i' * _) - v i' * _ * (v i * _) = 0
    ring

end Block

end AddBlockIsometric

open AddBlockIsometric in

/- English proof (translation)
Introduce `K _ _ ι _ Ω _ _ y D A m N v B L hY hm hv hgen hBa hLa hLh hBh`. Establish `hrel : IsRelevant (mCoordIdeal y)` using `hY.2.1.2.2`. Take `⟨c₀, hc₀⟩` from `SectionPointValue.exists_chart hrel`. Choose the witnesses or unpack the hypotheses as in `⟨j, hj⟩ : ∃ j, v j ≠ 0 := by`. Assume the negation of the conclusion as `h`.

Simplify using `only [not_exists, not_not] at h`. Take `⟨u, -, hu⟩` from `hgen c₀ hc₀`. Simplify using `[h] at hu`. Take `⟨e₀, δ₀, G₀, hG₀, hδ₀, hG₀v⟩` from `exists_chartForm y c₀ hc₀ (fun k => (m : ℤ) * A.a k) (hv j c₀ hc₀)`. Establish `hrep₀ : IsRep y A.a m (v j) G₀ (chartMon c₀ e₀)` using `⟨δ₀, e₀, hG₀, homog_chartMon c₀ e₀, fun k => by linear_combination hδ₀ k, by rw [aeval_chartMon]; exact hG₀v⟩`.

Establish `hb` using `isBlockMap_oldV (ι := ι) N`. Establish `hprod₀ : ∏ k, y ⟨k, c₀ k⟩ ^ e₀ k ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc₀ k)`. Use `⟨X ⟨none, j⟩ * rename (oldV N) (chartMon c₀ e₀), rename (oldV N) G₀, Pi.single none 1 + Function.extend some e₀ 0, Function.extend some δ₀ 0, homog_mul (homog_X _) (Inter.rename_isMultiHomog hb (homog_chartMon c₀ e₀)), Inter.rename_isMultiHomog hb hG₀, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_iff _ (homog_mul (homog_X _) (Inter.rename_isMultiHomog hb (homog_chartMon c₀ e₀))), map_mul, aeval_X, aeval_rename_old, aeval_chartMon]`. Conclude with `mul_ne_zero hj hprod₀`.

Rewrite using `[mem_iff _ (Inter.rename_isMultiHomog hb hG₀), aeval_rename_old, hG₀v]`. Conclude with `mul_ne_zero hj hprod₀`. Introduce `k`. Rewrite using `[hBa, hLa]`. Consider the cases of `k with`.

Consider the case `none`. Simplify using `[ReciprocityTheory.ChartRestriction.G.AI.I1.pullDeg, unitDeg]`. Consider the case `some k`. Simplify using `only [Pi.add_apply, extend_some_some, ReciprocityTheory.ChartRestriction.G.AI.I1.pullDeg]`. Use `hδ₀ k` as an intermediate fact.

Simplify using `[unitDeg]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `divCycle_eq_of_forall_cross _ fun W hWp hWr hPW => ?_` and prove the remaining obligations. Establish `hWr' : ∀ k : K, ∃ i : ι k, (X ⟨some k, i⟩ : MRing (addIdx ι N)) ∉ W` using `fun k => hWr (some k)`. Use `choose c hc using hWr'`.

Take `⟨i₀, hi₀⟩ : ∃ i : Fin N, (X ⟨none, i⟩ : MRing (addIdx ι N)) ∉ W` from `hWr none`. Establish `hyc : ∀ k, y ⟨k, c k⟩ ≠ 0`. Introduce `k h0`. Apply `hc k` to reduce the goal to its premises. Apply `hPW` to reduce the goal to its premises.

Establish `hX : (X ⟨k, c k⟩ : MRing ι) ∈ mCoordIdeal y` using `(mem_iff y (homog_X _)).mpr (by rw [aeval_X]; exact h0)`. Use `rename_mem v hX` as an intermediate fact. Rewrite `this` using `[rename_X]`. Then use the resulting hypothesis. Use `choose Ns δs Gs hGs hδs hGsv using fun i => exists_chartForm y c hyc (fun k => (m : ℤ) * A.a k) (hv i c hyc)`. Establish `hrep : ∀ i, IsRep y A.a m (v i) (Gs i) (chartMon c (Ns i))` using `fun i => ⟨δs i, Ns i, hGs i, homog_chartMon c _, fun k => by linear_combination hδs i k, by rw [aeval_chartMon]; exact hGsv i⟩`.

Use `⟨X ⟨none, i₀⟩ * rename (oldV N) (chartMon c (Ns i₀)), rename (oldV N) (Gs i₀), ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `h`. Break down `hWp.mem_or_mem h with h | h` into its components or cases. Conclude with `hi₀ h`. Conclude with `not_mem_rename_chartMon hc _ h`.

Introduce `hG`. Establish `hall : ∀ i, rename (oldV N) (Gs i) ∈ W`. Introduce `i`. Establish `hr` using `hPW (cross_mem (hrep i₀) (hrep i))`. Establish `h2 : (X ⟨none, i⟩ : MRing (addIdx ι N)) * rename (oldV N) (chartMon c (Ns i)) * rename (oldV N) (Gs i₀) ∈ W` using `W.mul_mem_left _ hG`.

Establish `h3` using `W.add_mem hr h2`. Rewrite `h3` using `[sub_add_cancel]`. Break down `hWp.mem_or_mem h3 with h4 | h4` into its components or cases. Break down `hWp.mem_or_mem h4 with h5 | h5` into its components or cases. Conclude with `absurd h5 hi₀`.

Conclude with `absurd h5 (not_mem_rename_chartMon hc _)`. Conclude with `h4`. Take `⟨u, hu, hsum⟩` from `hgen c hyc`. Establish `hsum' : ∑ i, u i * (v i * ∏ k, y ⟨k, c k⟩ ^ (-((m : ℤ) * A.a k))) = 1` using `hsum`. Use `choose ε U hU hUv using fun i => exists_form_of_mem_chartRingZ y c hyc (hu i)`.

Take `⟨Dt, hle⟩ : ∃ Dt : K → ℕ, ∀ i k, ε i k + δs i k ≤ Dt k` from `⟨fun k => ∑ i, (ε i k + δs i k), fun i k => Finset.single_le_sum (f := fun i => ε i k + δs i k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)⟩`. Establish `key : ∀ i, (∏ k, y ⟨k, c k⟩ ^ ε i k) * (∏ k, y ⟨k, c k⟩ ^ Ns i k) * (∏ k, y ⟨k, c k⟩ ^ (Dt k - (ε i k + δs i k))) = (∏ k, y ⟨k, c k⟩ ^ (-((m : ℤ) * A.a k))) * ∏ k, y ⟨k, c k⟩ ^ Dt k`. Introduce `i`. Rewrite using `[← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations.

Simplify using `only [← zpow_natCast, ← zpow_add₀ (hyc k)]`. Use `congr 1`. Establish `h1` using `hδs i k`. Establish `h2` using `hle i k`. Move the coercions through the operations in `[Nat.cast_sub h2]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hΦ : (∑ i, U i * Gs i * chartMon c (fun k => Dt k - (ε i k + δs i k))) - chartMon c Dt ∈ mCoordIdeal y`. Use `(mem_iff y (homog_sub (homog_sum _ fun i _ => homog_congr (homog_mul (homog_mul (hU i) (hGs i)) (homog_chartMon c _)) fun k => ?_) (homog_chartMon c Dt))).mpr ?_` and prove the remaining obligations. Simplify using `only [Pi.add_apply]`. Use `hle i k` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Rewrite using `[map_sub, map_sum, aeval_chartMon, sub_eq_zero]`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, hUv i, hGsv i, aeval_chartMon]`.

Combine the equalities or inequalities in the displayed calculation. Use `_ = ∏ k, y ⟨k, c k⟩ ^ Dt k := by rw [← Finset.sum_mul, hsum', one_mul]`. Establish `hΦW` using `hPW (rename_mem v hΦ)`. Establish `hS : rename (oldV N) (∑ i, U i * Gs i * chartMon c (fun k => Dt k - (ε i k + δs i k))) ∈ W`. Rewrite using `[map_sum]`.

Conclude with `W.sum_mem fun i _ => by`. Rewrite using `[map_mul, map_mul]`. Conclude with `W.mul_mem_right _ (W.mul_mem_left _ (hall i))`. Establish `hT` using `W.sub_mem hS hΦW`. Rewrite `hT` using `[map_sub, sub_sub_cancel]`.

Conclude with `not_mem_rename_chartMon hc Dt hT`. Conclude with `cross_mem hrep₀ (hrep i₀)`. Introduce `z hz`. Establish `hzo : basePart₂ z ∈ mcPts (mCoordIdeal y)`. Use `⟨fun k => hz.1 (some k), fun F hF => ?_⟩` and prove the remaining obligations.

Establish `h1` using `hz.2 _ (rename_mem v hF)`. Rewrite `h1` using `[eval_rename_old]`. Then use the resulting hypothesis. Establish `hval` using `val_spec (hv j) hzo hrep₀`. Establish `hsec` using `secNormAt_eq (hv j) hzo`. Establish `hB` using `hBh z hz j`.

Establish `hA` using `A.pos _ hzo.1`. Rewrite using `[hLh z, map_mul, map_mul, eval_rename_old, eval_rename_old, hval, map_X, eval_X]`. Rewrite using `[norm_mul, norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hA.le, ← hsec, ← hB]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem AddBlockIsometric.proof : AddBlockIsometric.Statement := by
  intro K _ _ ι _ Ω _ _ y D A m N v B L hY hm hv hgen hBa hLa hLh hBh
  classical
  have hrel : IsRelevant (mCoordIdeal y) := hY.2.1.2.2
  obtain ⟨c₀, hc₀⟩ := SectionPointValue.exists_chart hrel
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    obtain ⟨u, -, hu⟩ := hgen c₀ hc₀
    simp [h] at hu
  obtain ⟨e₀, δ₀, G₀, hG₀, hδ₀, hG₀v⟩ :=
    exists_chartForm y c₀ hc₀ (fun k => (m : ℤ) * A.a k) (hv j c₀ hc₀)
  have hrep₀ : IsRep y A.a m (v j) G₀ (chartMon c₀ e₀) :=
    ⟨δ₀, e₀, hG₀, homog_chartMon c₀ e₀, fun k => by linear_combination hδ₀ k, by rw [aeval_chartMon]; exact hG₀v⟩
  have hb := isBlockMap_oldV (ι := ι) N
  have hprod₀ : ∏ k, y ⟨k, c₀ k⟩ ^ e₀ k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc₀ k)
  refine ⟨X ⟨none, j⟩ * rename (oldV N) (chartMon c₀ e₀), rename (oldV N) G₀,
    Pi.single none 1 + Function.extend some e₀ 0, Function.extend some δ₀ 0,
    homog_mul (homog_X _) (Inter.rename_isMultiHomog hb (homog_chartMon c₀ e₀)),
    Inter.rename_isMultiHomog hb hG₀, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rw [mem_iff _ (homog_mul (homog_X _) (Inter.rename_isMultiHomog hb (homog_chartMon c₀ e₀))), map_mul, aeval_X,
      aeval_rename_old, aeval_chartMon]
    exact mul_ne_zero hj hprod₀
  ·
    rw [mem_iff _ (Inter.rename_isMultiHomog hb hG₀), aeval_rename_old, hG₀v]
    exact mul_ne_zero hj hprod₀
  ·
    intro k
    rw [hBa, hLa]
    cases k with
    | none =>
      simp [ReciprocityTheory.ChartRestriction.G.AI.I1.pullDeg, unitDeg]
    | some k =>
      simp only [Pi.add_apply, extend_some_some, ReciprocityTheory.ChartRestriction.G.AI.I1.pullDeg]
      have := hδ₀ k
      simp [unitDeg]
      linarith
  ·
    refine divCycle_eq_of_forall_cross _ fun W hWp hWr hPW => ?_
    have hWr' : ∀ k : K, ∃ i : ι k, (X ⟨some k, i⟩ : MRing (addIdx ι N)) ∉ W := fun k => hWr (some k)
    choose c hc using hWr'
    obtain ⟨i₀, hi₀⟩ : ∃ i : Fin N, (X ⟨none, i⟩ : MRing (addIdx ι N)) ∉ W := hWr none
    have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := by
      intro k h0
      apply hc k
      apply hPW
      have hX : (X ⟨k, c k⟩ : MRing ι) ∈ mCoordIdeal y :=
        (mem_iff y (homog_X _)).mpr (by rw [aeval_X]; exact h0)
      have := rename_mem v hX
      rwa [rename_X] at this
    choose Ns δs Gs hGs hδs hGsv using
      fun i => exists_chartForm y c hyc (fun k => (m : ℤ) * A.a k) (hv i c hyc)
    have hrep : ∀ i, IsRep y A.a m (v i) (Gs i) (chartMon c (Ns i)) := fun i =>
      ⟨δs i, Ns i, hGs i, homog_chartMon c _, fun k => by linear_combination hδs i k,
        by rw [aeval_chartMon]; exact hGsv i⟩
    refine ⟨X ⟨none, i₀⟩ * rename (oldV N) (chartMon c (Ns i₀)), rename (oldV N) (Gs i₀), ?_, ?_, ?_⟩
    · intro h
      rcases hWp.mem_or_mem h with h | h
      · exact hi₀ h
      · exact not_mem_rename_chartMon hc _ h
    · intro hG
      have hall : ∀ i, rename (oldV N) (Gs i) ∈ W := by
        intro i
        have hr := hPW (cross_mem (hrep i₀) (hrep i))
        have h2 : (X ⟨none, i⟩ : MRing (addIdx ι N)) * rename (oldV N) (chartMon c (Ns i)) *
            rename (oldV N) (Gs i₀) ∈ W := W.mul_mem_left _ hG
        have h3 := W.add_mem hr h2
        rw [sub_add_cancel] at h3
        rcases hWp.mem_or_mem h3 with h4 | h4
        · rcases hWp.mem_or_mem h4 with h5 | h5
          · exact absurd h5 hi₀
          · exact absurd h5 (not_mem_rename_chartMon hc _)
        · exact h4
      obtain ⟨u, hu, hsum⟩ := hgen c hyc
      have hsum' : ∑ i, u i * (v i * ∏ k, y ⟨k, c k⟩ ^ (-((m : ℤ) * A.a k))) = 1 := hsum
      choose ε U hU hUv using fun i => exists_form_of_mem_chartRingZ y c hyc (hu i)
      obtain ⟨Dt, hle⟩ : ∃ Dt : K → ℕ, ∀ i k, ε i k + δs i k ≤ Dt k :=
        ⟨fun k => ∑ i, (ε i k + δs i k), fun i k =>
          Finset.single_le_sum (f := fun i => ε i k + δs i k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)⟩
      have key : ∀ i, (∏ k, y ⟨k, c k⟩ ^ ε i k) * (∏ k, y ⟨k, c k⟩ ^ Ns i k) *
          (∏ k, y ⟨k, c k⟩ ^ (Dt k - (ε i k + δs i k))) =
            (∏ k, y ⟨k, c k⟩ ^ (-((m : ℤ) * A.a k))) * ∏ k, y ⟨k, c k⟩ ^ Dt k := by
        intro i
        rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun k _ => ?_
        simp only [← zpow_natCast, ← zpow_add₀ (hyc k)]
        congr 1
        have h1 := hδs i k
        have h2 := hle i k
        push_cast [Nat.cast_sub h2]
        linarith
      have hΦ : (∑ i, U i * Gs i * chartMon c (fun k => Dt k - (ε i k + δs i k))) - chartMon c Dt ∈
          mCoordIdeal y := by
        refine (mem_iff y (homog_sub (homog_sum _ fun i _ => homog_congr (homog_mul (homog_mul (hU i) (hGs i))
          (homog_chartMon c _)) fun k => ?_) (homog_chartMon c Dt))).mpr ?_
        · simp only [Pi.add_apply]
          have := hle i k
          omega
        · rw [map_sub, map_sum, aeval_chartMon, sub_eq_zero]
          calc ∑ i, aeval y (U i * Gs i * chartMon c (fun k => Dt k - (ε i k + δs i k)))
              = ∑ i, u i * (v i * ∏ k, y ⟨k, c k⟩ ^ (-((m : ℤ) * A.a k))) * ∏ k, y ⟨k, c k⟩ ^ Dt k := by
                refine Finset.sum_congr rfl fun i _ => ?_
                rw [map_mul, map_mul, hUv i, hGsv i, aeval_chartMon]
                calc (u i * ∏ k, y ⟨k, c k⟩ ^ ε i k) * (v i * ∏ k, y ⟨k, c k⟩ ^ Ns i k) *
                      ∏ k, y ⟨k, c k⟩ ^ (Dt k - (ε i k + δs i k))
                    = u i * v i * ((∏ k, y ⟨k, c k⟩ ^ ε i k) * (∏ k, y ⟨k, c k⟩ ^ Ns i k) *
                      (∏ k, y ⟨k, c k⟩ ^ (Dt k - (ε i k + δs i k)))) := by ring
                  _ = _ := by rw [key i]; ring
            _ = ∏ k, y ⟨k, c k⟩ ^ Dt k := by rw [← Finset.sum_mul, hsum', one_mul]
      have hΦW := hPW (rename_mem v hΦ)
      have hS : rename (oldV N) (∑ i, U i * Gs i * chartMon c (fun k => Dt k - (ε i k + δs i k))) ∈ W := by
        rw [map_sum]
        exact W.sum_mem fun i _ => by
          rw [map_mul, map_mul]
          exact W.mul_mem_right _ (W.mul_mem_left _ (hall i))
      have hT := W.sub_mem hS hΦW
      rw [map_sub, sub_sub_cancel] at hT
      exact not_mem_rename_chartMon hc Dt hT
    · exact cross_mem hrep₀ (hrep i₀)
  ·
    intro z hz
    have hzo : basePart₂ z ∈ mcPts (mCoordIdeal y) := by
      refine ⟨fun k => hz.1 (some k), fun F hF => ?_⟩
      have h1 := hz.2 _ (rename_mem v hF)
      rwa [eval_rename_old] at h1
    have hval := val_spec (hv j) hzo hrep₀
    have hsec := secNormAt_eq (hv j) hzo
    have hB := hBh z hz j
    have hA := A.pos _ hzo.1
    rw [hLh z, map_mul, map_mul, eval_rename_old, eval_rename_old, hval, map_X, eval_X]
    rw [norm_mul, norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hA.le, ← hsec,
      ← hB]
    ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
