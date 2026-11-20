import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsCovolOne
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdelicCharacterOrthogonalIsRationalStatement
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AdlEqZeroOfMemNbhd
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.NumFieldHosCountable
import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.FdSetIntegralCharEqZero
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.FourierComplete

open scoped Pointwise

section Gen

variable {V : Type*} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]

/- English proof (translation)
Set `p : C(V, V ⧸ Λ)` to `⟨QuotientAddGroup.mk, continuous_quotient_mk'⟩`. Establish `hq : Topology.IsQuotientMap p` using `QuotientAddGroup.isQuotientMap_mk Λ`. Establish `hfac : Function.FactorsThrough (⟨f, hf⟩ : C(V, ℂ)) p`. Introduce `a b hab`. Establish `h1 : -a + b ∈ Λ` using `QuotientAddGroup.eq.1 hab`.

Establish `h2` using `hp a _ h1`. Simplify using `using h2.symm`. Use `⟨hq.lift ⟨f, hf⟩ hfac, fun x => ?_⟩` and prove the remaining obligations. Conclude with `DFunLike.congr_fun (hq.lift_comp ⟨f, hf⟩ hfac) x`.
-/
theorem exists_descent (Λ : AddSubgroup V) (f : V → ℂ) (hf : Continuous f)
    (hp : ∀ x, ∀ l ∈ Λ, f (x + l) = f x) :
    ∃ h : C(V ⧸ Λ, ℂ), ∀ x, h (QuotientAddGroup.mk x) = f x := by
  let p : C(V, V ⧸ Λ) := ⟨QuotientAddGroup.mk, continuous_quotient_mk'⟩
  have hq : Topology.IsQuotientMap p := QuotientAddGroup.isQuotientMap_mk Λ
  have hfac : Function.FactorsThrough (⟨f, hf⟩ : C(V, ℂ)) p := by
    intro a b hab
    have h1 : -a + b ∈ Λ := QuotientAddGroup.eq.1 hab
    have h2 := hp a _ h1
    simpa using h2.symm
  refine ⟨hq.lift ⟨f, hf⟩ hfac, fun x => ?_⟩
  exact DFunLike.congr_fun (hq.lift_comp ⟨f, hf⟩ hfac) x

/- English proof (translation)
Use `⟨?_⟩` and prove the remaining obligations. Establish `himg : (QuotientAddGroup.mk '' K : Set (V ⧸ Λ)) = Set.univ`. Use `Set.eq_univ_of_forall fun q => ?_` and prove the remaining obligations. Take `⟨x, rfl⟩` from `QuotientAddGroup.mk_surjective q`. Take `⟨l, hl, hx⟩` from `hc x`.

Use `⟨x - l, hx, ?_⟩` and prove the remaining obligations. Rewrite using `[QuotientAddGroup.eq]`. Establish `h1 : -(x - l) + x = l` using `by abel`. Rewrite using `[h1]` and apply the resulting hypothesis. Rewrite using `[← himg]`.

Conclude with `hK.image continuous_quotient_mk'`.
-/
theorem compactSpace_quotient (Λ : AddSubgroup V) {K : Set V} (hK : IsCompact K)
    (hc : ∀ x, ∃ l ∈ Λ, x - l ∈ K) : CompactSpace (V ⧸ Λ) := by
  refine ⟨?_⟩
  have himg : (QuotientAddGroup.mk '' K : Set (V ⧸ Λ)) = Set.univ := by
    refine Set.eq_univ_of_forall fun q => ?_
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨l, hl, hx⟩ := hc x
    refine ⟨x - l, hx, ?_⟩
    rw [QuotientAddGroup.eq]
    have h1 : -(x - l) + x = l := by abel
    rwa [h1]
  rw [← himg]
  exact hK.image continuous_quotient_mk'

/- English proof (translation)
Use `set S : Submodule ℂ C(X, ℂ) := Submodule.span ℂ (Set.range c) with hS`. Establish `hcS : ∀ t, c t ∈ S` using `fun t => Submodule.subset_span ⟨t, rfl⟩`. Establish `h1 : (1 : C(X, ℂ)) ∈ S` using `h0 ▸ hcS 0`. Establish `hmul : ∀ x y, x ∈ S → y ∈ S → x * y ∈ S`. Introduce `x y hx hy`.

Establish `hle : S * S ≤ S`. Rewrite using `[hS, Submodule.span_mul_span]`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨_, ⟨s, rfl⟩, _, ⟨t, rfl⟩, rfl⟩`. Use `show c s * c t ∈ _`.

Rewrite using `[← hadd]`. Conclude with `hcS _`. Conclude with `hle (Submodule.mul_mem_mul hx hy)`. Establish `hst : ∀ x ∈ S, star x ∈ S`. Introduce `x hx`.

Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x h => obtain ⟨t, rfl⟩ := h`. Rewrite using `[hstar]`. Conclude with `hcS _`. Consider the case `zero => simp`.

Consider the case `add x y _ _ hx hy => rw [star_add]`. Conclude with `S.add_mem hx hy`. Consider the case `smul a x _ hx => rw [star_smul]`. Conclude with `S.smul_mem _ hx`. Set `A : StarSubalgebra ℂ C(X, ℂ)` to `{ toSubalgebra := S.toSubalgebra h1 hmul, star_mem' := fun {a} ha => hst a ha }`.

Establish `hA : A.SeparatesPoints`. Introduce `x y hxy`. Take `⟨t, ht⟩` from `hsep x y hxy`. Conclude with `⟨c t, ⟨c t, hcS t, rfl⟩, ht⟩`. Establish `htop` using `ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints A hA`.

Establish `hf : f ∈ (A.topologicalClosure : Set C(X, ℂ))`. Rewrite using `[htop]`. Discharge the goal by the elementary cases of `trivial`. Rewrite `hf` using `[StarSubalgebra.topologicalClosure_coe]`. Then use the resulting hypothesis.
-/
theorem mem_closure_span {X : Type*} [TopologicalSpace X] [CompactSpace X] {T : Type*} [AddCommGroup T]
    (c : T → C(X, ℂ)) (h0 : c 0 = 1) (hadd : ∀ s t, c (s + t) = c s * c t)
    (hstar : ∀ t, star (c t) = c (-t)) (hsep : ∀ x y, x ≠ y → ∃ t, c t x ≠ c t y) (f : C(X, ℂ)) :
    f ∈ closure ((Submodule.span ℂ (Set.range c) : Submodule ℂ C(X, ℂ)) : Set C(X, ℂ)) := by
  set S : Submodule ℂ C(X, ℂ) := Submodule.span ℂ (Set.range c) with hS
  have hcS : ∀ t, c t ∈ S := fun t => Submodule.subset_span ⟨t, rfl⟩
  have h1 : (1 : C(X, ℂ)) ∈ S := h0 ▸ hcS 0
  have hmul : ∀ x y, x ∈ S → y ∈ S → x * y ∈ S := by
    intro x y hx hy
    have hle : S * S ≤ S := by
      rw [hS, Submodule.span_mul_span]
      refine Submodule.span_le.2 ?_
      rintro _ ⟨_, ⟨s, rfl⟩, _, ⟨t, rfl⟩, rfl⟩
      show c s * c t ∈ _
      rw [← hadd]
      exact hcS _
    exact hle (Submodule.mul_mem_mul hx hy)
  have hst : ∀ x ∈ S, star x ∈ S := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x h => obtain ⟨t, rfl⟩ := h; rw [hstar]; exact hcS _
    | zero => simp
    | add x y _ _ hx hy => rw [star_add]; exact S.add_mem hx hy
    | smul a x _ hx => rw [star_smul]; exact S.smul_mem _ hx
  let A : StarSubalgebra ℂ C(X, ℂ) :=
    { toSubalgebra := S.toSubalgebra h1 hmul, star_mem' := fun {a} ha => hst a ha }
  have hA : A.SeparatesPoints := by
    intro x y hxy
    obtain ⟨t, ht⟩ := hsep x y hxy
    exact ⟨c t, ⟨c t, hcS t, rfl⟩, ht⟩
  have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints A hA
  have hf : f ∈ (A.topologicalClosure : Set C(X, ℂ)) := by
    rw [htop]
    trivial
  rwa [StarSubalgebra.topologicalClosure_coe] at hf

/- English proof (translation)
Use `haveI : CompactSpace (V ⧸ Λ) := compactSpace_quotient Λ hK hc`. Use `choose c hcχ using fun t => exists_descent Λ (χ t) (hχc t) (hχp t)`. Take `⟨gb, hgb⟩` from `exists_descent Λ g hg hgp`. Establish `hext : ∀ a b : C(V ⧸ Λ, ℂ), (∀ x : V, a (QuotientAddGroup.mk x) = b (QuotientAddGroup.mk x)) → a = b`. Introduce `a b h`.

Use extensionality with `q`. Take `⟨x, rfl⟩` from `QuotientAddGroup.mk_surjective q`. Conclude with `h x`. Establish `hc0 : c 0 = 1` using `hext _ _ fun x => by`. Rewrite using `[hcχ, h0]`.

Both sides reduce to the same expression. Establish `hcadd : ∀ s t, c (s + t) = c s * c t` using `fun s t => hext _ _ fun x => by`. Rewrite using `[hcχ, hadd, ContinuousMap.mul_apply, hcχ, hcχ]`. Establish `hcstar : ∀ t, star (c t) = c (-t)` using `fun t => hext _ _ fun x => by`. Rewrite using `[ContinuousMap.star_apply, hcχ, hcχ, hconj]`.

Establish `hsepc : ∀ p q : V ⧸ Λ, p ≠ q → ∃ t, c t p ≠ c t q`. Introduce `p q hpq`. Take `⟨a, rfl⟩` from `QuotientAddGroup.mk_surjective p`. Take `⟨b, rfl⟩` from `QuotientAddGroup.mk_surjective q`. Assume the negation of the conclusion as `hcon`.

Use `push Not at hcon`. Apply `hpq` to reduce the goal to its premises. Rewrite using `[QuotientAddGroup.eq]`. Conclude with `hsep a b fun t => by simpa [hcχ] using hcon t`. Establish `hfin : μ D < ⊤` using `Formalism.IndefR.Tow.fd_measure_lt_top hD hK (fun y => by`.

Take `⟨l, hl, hy⟩` from `hc y`. Use `⟨-l, Λ.neg_mem hl, ?_⟩` and prove the remaining obligations. Establish `h1 : -l + y = y - l` using `by abel`. Rewrite using `[h1])` and apply the resulting hypothesis. Use `haveI : IsFiniteMeasure (μ.restrict D) := ⟨by simpa using hfin⟩`.

Set `L : C(V ⧸ Λ, ℂ) → ℂ` to `fun s => ∫ b in D, g b * s (QuotientAddGroup.mk b) ∂μ`. Establish `hbd : ∀ (s : C(V ⧸ Λ, ℂ)) (b : V), ‖g b * s (QuotientAddGroup.mk b)‖ ≤ ‖gb‖ * ‖s‖`. Introduce `s b`. Rewrite using `[norm_mul, ← hgb b]`. Conclude with `mul_le_mul (gb.norm_coe_le_norm _) (s.norm_coe_le_norm _) (norm_nonneg _) (norm_nonneg _)`.

Establish `hint : ∀ s : C(V ⧸ Λ, ℂ), Integrable (fun b => g b * s (QuotientAddGroup.mk b)) (μ.restrict D)`. Introduce `s`. Establish `hcont : Continuous fun b => g b * s (QuotientAddGroup.mk b)` using `hg.mul (s.continuous.comp continuous_quotient_mk')`. Conclude with `Integrable.of_bound hcont.aestronglyMeasurable (‖gb‖ * ‖s‖) (ae_of_all _ (hbd s))`. Establish `hLc : Continuous L`.

Establish `hl : LipschitzWith (Real.toNNReal (‖gb‖ * (μ.restrict D).real Set.univ)) L`. Use `LipschitzWith.of_dist_le' fun s s' => ?_` and prove the remaining obligations. Rewrite using `[dist_eq_norm, dist_eq_norm]`. Establish `h1 : L s - L s' = ∫ b in D, g b * (s - s') (QuotientAddGroup.mk b) ∂μ` using `by show (∫ b in D, _ ∂μ) - (∫ b in D, _ ∂μ) = _`. Rewrite using `[← integral_sub (hint s) (hint s')]`.

Use `integral_congr_ae (ae_of_all _ fun b => ?_)` and prove the remaining obligations. Simplify using `[mul_sub]`. Rewrite using `[h1]`. Establish `h2` using `norm_integral_le_of_norm_le_const (μ := μ.restrict D) (ae_of_all _ (hbd (s - s')))`. Combine the equalities or inequalities in the displayed calculation.

Conclude with `hl.continuous`. Establish `hz : ∀ s ∈ Submodule.span ℂ (Set.range c), L s = 0`. Introduce `s hs`. Proceed by induction on `hs using Submodule.span_induction with`. Consider the case `mem s h`.

Take `⟨t, rfl⟩` from `h`. Establish `h1` using `hF (-t)`. Rewrite `h1` using `[neg_neg]`. Use `show ∫ b in D, g b * c t (QuotientAddGroup.mk b) ∂μ = 0`. Simplify `h1` using `only [hcχ]`.

Consider the case `zero => simp [L]`. Consider the case `add s s' _ _ hs hs'`. Establish `h1 : L (s + s') = L s + L s'` using `by show _ = (∫ b in D, _ ∂μ) + (∫ b in D, _ ∂μ)`. Rewrite using `[← integral_add (hint s) (hint s')]`. Use `integral_congr_ae (ae_of_all _ fun b => ?_)` and prove the remaining obligations.

Simplify using `[mul_add]`. Rewrite using `[h1, hs, hs', add_zero]`. Consider the case `smul a s _ hs`. Establish `h1 : L (a • s) = a * L s` using `by show _ = a * ∫ b in D, _ ∂μ`. Rewrite using `[← integral_const_mul]`.

Use `integral_congr_ae (ae_of_all _ fun b => ?_)` and prove the remaining obligations. Simplify using `only [ContinuousMap.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h1, hs, mul_zero]`. Establish `hL0 : L (star gb) = 0`.

Establish `hsub : ((Submodule.span ℂ (Set.range c) : Submodule ℂ C(V ⧸ Λ, ℂ)) : Set C(V ⧸ Λ, ℂ)) ⊆ {s | L s = 0}` using `fun s hs => hz s hs`. Conclude with `closure_minimal hsub (isClosed_eq hLc continuous_const) (mem_closure_span c hc0 hcadd hcstar hsepc (star gb))`. Establish `hpt : ∀ b, g b * (star gb) (QuotientAddGroup.mk b) = ((‖g b‖ ^ 2 : ℝ) : ℂ)`. Introduce `b`. Rewrite using `[ContinuousMap.star_apply, hgb]`.

Simplify using `using Complex.mul_conj' (g b)`. Establish `hR : ∫ b in D, ‖g b‖ ^ 2 ∂μ = 0`. Establish `h1 : ((∫ b in D, ‖g b‖ ^ 2 ∂μ : ℝ) : ℂ) = 0`. Rewrite using `[← integral_complex_ofReal, ← hL0]`. Conclude with `integral_congr_ae (ae_of_all _ fun b => (hpt b).symm)`.

Conclude with `h1` after adjusting the coercions. Establish `hRint : Integrable (fun b => ‖g b‖ ^ 2) (μ.restrict D)`. Establish `hcont : Continuous fun b => ‖g b‖ ^ 2` using `hg.norm.pow 2`. Use `Integrable.of_bound hcont.aestronglyMeasurable (‖gb‖ ^ 2) (ae_of_all _ fun b => ?_)` and prove the remaining obligations. Rewrite using `[Real.norm_of_nonneg (by positivity), ← hgb b]`.

Conclude with `pow_le_pow_left₀ (norm_nonneg _) (gb.norm_coe_le_norm _) 2`. Establish `hae` using `(integral_eq_zero_iff_of_nonneg (fun b => by positivity) hRint).1 hR`. Set `Z : Set V` to `{y | g y ≠ 0}`. Establish `hZo : IsOpen Z` using `isOpen_ne_fun hg continuous_const`. Establish `hZD : μ (Z ∩ D) = 0`.

Rewrite using `[← Measure.restrict_apply hZo.measurableSet]`. Use `measure_mono_null (fun y hy => ?_) (ae_iff.1 hae)` and prove the remaining obligations. Establish `hy' : g y ≠ 0` using `hy`. Simplify using `using hy'`. Establish `hZinv : ∀ l : Λ, l +ᵥ Z = Z`.

Introduce `l`. Use extensionality with `y`. Rewrite using `[Set.mem_vadd_set_iff_neg_vadd_mem]`. Establish `h1 : g (-l +ᵥ y) = g y`. Establish `h2` using `hgp y (-(l : V)) (Λ.neg_mem l.2)`.

Rewrite using `[← h2, add_comm]`. Both sides reduce to the same expression. Use `show g (-l +ᵥ y) ≠ 0 ↔ g y ≠ 0`. Rewrite using `[h1]`. Establish `hZ0` using `hD.measure_zero_of_invariant Z hZinv hZD`.

Establish `hZe : Z = ∅` using `(hZo.measure_eq_zero_iff μ).1 hZ0`. Assume the negation of the conclusion as `hx`. Establish `hxZ : x ∈ Z` using `hx`. Rewrite `hxZ` using `[hZe]`. Conclude with `hxZ`.
-/
theorem eq_zero_of_coeffs_vanish [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
    (Λ : AddSubgroup V) [Countable Λ] (μ : Measure V) [μ.IsAddHaarMeasure] {D : Set V}
    (hD : IsAddFundamentalDomain Λ D μ) {K : Set V} (hK : IsCompact K)
    (hc : ∀ x, ∃ l ∈ Λ, x - l ∈ K) {T : Type*} [AddCommGroup T] (χ : T → V → ℂ)
    (hχc : ∀ t, Continuous (χ t)) (hχp : ∀ t x, ∀ l ∈ Λ, χ t (x + l) = χ t x)
    (h0 : ∀ x, χ 0 x = 1) (hadd : ∀ s t x, χ (s + t) x = χ s x * χ t x)
    (hconj : ∀ t x, star (χ t x) = χ (-t) x)
    (hsep : ∀ x y, (∀ t, χ t x = χ t y) → -x + y ∈ Λ)
    (g : V → ℂ) (hg : Continuous g) (hgp : ∀ x, ∀ l ∈ Λ, g (x + l) = g x)
    (hF : ∀ t, ∫ b in D, g b * χ (-t) b ∂μ = 0) (x : V) : g x = 0 := by
  haveI : CompactSpace (V ⧸ Λ) := compactSpace_quotient Λ hK hc
  choose c hcχ using fun t => exists_descent Λ (χ t) (hχc t) (hχp t)
  obtain ⟨gb, hgb⟩ := exists_descent Λ g hg hgp
  have hext : ∀ a b : C(V ⧸ Λ, ℂ),
      (∀ x : V, a (QuotientAddGroup.mk x) = b (QuotientAddGroup.mk x)) → a = b := by
    intro a b h
    ext q
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    exact h x
  have hc0 : c 0 = 1 := hext _ _ fun x => by
    rw [hcχ, h0]; rfl
  have hcadd : ∀ s t, c (s + t) = c s * c t := fun s t => hext _ _ fun x => by
    rw [hcχ, hadd, ContinuousMap.mul_apply, hcχ, hcχ]
  have hcstar : ∀ t, star (c t) = c (-t) := fun t => hext _ _ fun x => by
    rw [ContinuousMap.star_apply, hcχ, hcχ, hconj]
  have hsepc : ∀ p q : V ⧸ Λ, p ≠ q → ∃ t, c t p ≠ c t q := by
    intro p q hpq
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective p
    obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective q
    by_contra hcon
    push Not at hcon
    apply hpq
    rw [QuotientAddGroup.eq]
    exact hsep a b fun t => by simpa [hcχ] using hcon t
  have hfin : μ D < ⊤ := Formalism.IndefR.Tow.fd_measure_lt_top hD hK (fun y => by
    obtain ⟨l, hl, hy⟩ := hc y
    refine ⟨-l, Λ.neg_mem hl, ?_⟩
    have h1 : -l + y = y - l := by abel
    rwa [h1])
  haveI : IsFiniteMeasure (μ.restrict D) := ⟨by simpa using hfin⟩
  let L : C(V ⧸ Λ, ℂ) → ℂ := fun s => ∫ b in D, g b * s (QuotientAddGroup.mk b) ∂μ
  have hbd : ∀ (s : C(V ⧸ Λ, ℂ)) (b : V), ‖g b * s (QuotientAddGroup.mk b)‖ ≤ ‖gb‖ * ‖s‖ := by
    intro s b
    rw [norm_mul, ← hgb b]
    exact mul_le_mul (gb.norm_coe_le_norm _) (s.norm_coe_le_norm _) (norm_nonneg _) (norm_nonneg _)
  have hint : ∀ s : C(V ⧸ Λ, ℂ),
      Integrable (fun b => g b * s (QuotientAddGroup.mk b)) (μ.restrict D) := by
    intro s
    have hcont : Continuous fun b => g b * s (QuotientAddGroup.mk b) :=
      hg.mul (s.continuous.comp continuous_quotient_mk')
    exact Integrable.of_bound hcont.aestronglyMeasurable (‖gb‖ * ‖s‖) (ae_of_all _ (hbd s))
  have hLc : Continuous L := by
    have hl : LipschitzWith (Real.toNNReal (‖gb‖ * (μ.restrict D).real Set.univ)) L := by
      refine LipschitzWith.of_dist_le' fun s s' => ?_
      rw [dist_eq_norm, dist_eq_norm]
      have h1 : L s - L s' = ∫ b in D, g b * (s - s') (QuotientAddGroup.mk b) ∂μ := by
        show (∫ b in D, _ ∂μ) - (∫ b in D, _ ∂μ) = _
        rw [← integral_sub (hint s) (hint s')]
        refine integral_congr_ae (ae_of_all _ fun b => ?_)
        simp [mul_sub]
      rw [h1]
      have h2 := norm_integral_le_of_norm_le_const (μ := μ.restrict D)
        (ae_of_all _ (hbd (s - s')))
      calc _ ≤ _ := h2
        _ = _ := by ring
    exact hl.continuous
  have hz : ∀ s ∈ Submodule.span ℂ (Set.range c), L s = 0 := by
    intro s hs
    induction hs using Submodule.span_induction with
    | mem s h =>
      obtain ⟨t, rfl⟩ := h
      have h1 := hF (-t)
      rw [neg_neg] at h1
      show ∫ b in D, g b * c t (QuotientAddGroup.mk b) ∂μ = 0
      simpa only [hcχ] using h1
    | zero => simp [L]
    | add s s' _ _ hs hs' =>
      have h1 : L (s + s') = L s + L s' := by
        show _ = (∫ b in D, _ ∂μ) + (∫ b in D, _ ∂μ)
        rw [← integral_add (hint s) (hint s')]
        refine integral_congr_ae (ae_of_all _ fun b => ?_)
        simp [mul_add]
      rw [h1, hs, hs', add_zero]
    | smul a s _ hs =>
      have h1 : L (a • s) = a * L s := by
        show _ = a * ∫ b in D, _ ∂μ
        rw [← integral_const_mul]
        refine integral_congr_ae (ae_of_all _ fun b => ?_)
        simp only [ContinuousMap.smul_apply, smul_eq_mul]
        ring
      rw [h1, hs, mul_zero]
  have hL0 : L (star gb) = 0 := by
    have hsub : ((Submodule.span ℂ (Set.range c) : Submodule ℂ C(V ⧸ Λ, ℂ)) : Set C(V ⧸ Λ, ℂ)) ⊆
        {s | L s = 0} := fun s hs => hz s hs
    exact closure_minimal hsub (isClosed_eq hLc continuous_const)
      (mem_closure_span c hc0 hcadd hcstar hsepc (star gb))
  have hpt : ∀ b, g b * (star gb) (QuotientAddGroup.mk b) = ((‖g b‖ ^ 2 : ℝ) : ℂ) := by
    intro b
    rw [ContinuousMap.star_apply, hgb]
    simpa using Complex.mul_conj' (g b)
  have hR : ∫ b in D, ‖g b‖ ^ 2 ∂μ = 0 := by
    have h1 : ((∫ b in D, ‖g b‖ ^ 2 ∂μ : ℝ) : ℂ) = 0 := by
      rw [← integral_complex_ofReal, ← hL0]
      exact integral_congr_ae (ae_of_all _ fun b => (hpt b).symm)
    exact_mod_cast h1
  have hRint : Integrable (fun b => ‖g b‖ ^ 2) (μ.restrict D) := by
    have hcont : Continuous fun b => ‖g b‖ ^ 2 := hg.norm.pow 2
    refine Integrable.of_bound hcont.aestronglyMeasurable (‖gb‖ ^ 2) (ae_of_all _ fun b => ?_)
    rw [Real.norm_of_nonneg (by positivity), ← hgb b]
    exact pow_le_pow_left₀ (norm_nonneg _) (gb.norm_coe_le_norm _) 2
  have hae := (integral_eq_zero_iff_of_nonneg (fun b => by positivity) hRint).1 hR
  let Z : Set V := {y | g y ≠ 0}
  have hZo : IsOpen Z := isOpen_ne_fun hg continuous_const
  have hZD : μ (Z ∩ D) = 0 := by
    rw [← Measure.restrict_apply hZo.measurableSet]
    refine measure_mono_null (fun y hy => ?_) (ae_iff.1 hae)
    have hy' : g y ≠ 0 := hy
    simpa using hy'
  have hZinv : ∀ l : Λ, l +ᵥ Z = Z := by
    intro l
    ext y
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    have h1 : g (-l +ᵥ y) = g y := by
      have h2 := hgp y (-(l : V)) (Λ.neg_mem l.2)
      rw [← h2, add_comm]
      rfl
    show g (-l +ᵥ y) ≠ 0 ↔ g y ≠ 0
    rw [h1]
  have hZ0 := hD.measure_zero_of_invariant Z hZinv hZD
  have hZe : Z = ∅ := (hZo.measure_eq_zero_iff μ).1 hZ0
  by_contra hx
  have hxZ : x ∈ Z := hx
  rw [hZe] at hxZ
  exact hxZ

end Gen

/- English proof (translation)
The claim follows from `(Module.finBasis ℚ F).equivFun.injective.countable`.
-/
theorem countable_numberField (F : Type) [Field F] [NumberField F] : Countable F :=
  (Module.finBasis ℚ F).equivFun.injective.countable

end GlobalTheory.CompanionTheory.FourierComplete
