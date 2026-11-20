import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsZeroCocycleSection
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace ZeroCocycleSection

set_option linter.unusedSectionVars false

open GenOnFibres

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

section Graded

variable {S : Type} [CommRing S] {V : Ideal (MRingOver S ι)}

/- English proof (translation)
Introduce `m hm k` and use `hp m (MvPolynomial.support_smul hm) k`.
-/
theorem homog_smul {p : MRingOver S ι} {a : K → ℕ} (r : S) (hp : IsMultiHomog p a) :
    IsMultiHomog (r • p) a :=
  fun m hm k => hp m (MvPolynomial.support_smul hm) k

/- English proof (translation)
Distinguish the cases in `hc : ∀ k, 0 ≤ c k`. Use `⟨hc, ?_⟩` and prove the remaining obligations. Establish `hm' : m ∈ Submodule.map (Ideal.Quotient.mkₐ S V).toLinearMap (Submodule.span S {p : MRingOver S ι | (∀ k, 0 ≤ c k) ∧ IsMultiHomog p (fun k => (c k).toNat)})`. Rewrite using `[← Submodule.span_image]`. Conclude with `hm`.

Take `⟨p, hp, rfl⟩` from `Submodule.mem_map.mp hm'`. Use `⟨p, ?_, rfl⟩` and prove the remaining obligations. Use `clear hm h0 hm'`. Proceed by induction on `hp using Submodule.span_induction with`. Consider the case `mem x hx => exact hx.2`.

Consider the case `zero => exact homog_zero _`. Consider the case `add x y _ _ hx hy => exact homog_add hx hy`. Consider the case `smul r x _ hx => exact homog_smul r hx`. It suffices to derive a contradiction. Apply `h0` to reduce the goal to its premises.

Establish `e : {p : MRingOver S ι | (∀ k, 0 ≤ c k) ∧ IsMultiHomog p (fun k => (c k).toNat)} = ∅` using `Set.eq_empty_of_forall_notMem fun p hp => hc hp.1`. Unfold `KH.quotPart at hm`. Rewrite `hm` using `[e, Set.image_empty, Submodule.span_empty, Submodule.mem_bot]`. Conclude with `hm`.
-/
theorem quotPart_eq_mk {c : K → ℤ} {m : MRingOver S ι ⧸ V} (hm : m ∈ KH.quotPart S V c) (h0 : m ≠ 0) :
    (∀ k, 0 ≤ c k) ∧ ∃ p, IsMultiHomog p (fun k => (c k).toNat) ∧ Ideal.Quotient.mk V p = m := by
  by_cases hc : ∀ k, 0 ≤ c k
  · refine ⟨hc, ?_⟩
    have hm' : m ∈ Submodule.map (Ideal.Quotient.mkₐ S V).toLinearMap
        (Submodule.span S {p : MRingOver S ι | (∀ k, 0 ≤ c k) ∧ IsMultiHomog p (fun k => (c k).toNat)}) := by
      rw [← Submodule.span_image]
      exact hm
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hm'
    refine ⟨p, ?_, rfl⟩
    clear hm h0 hm'
    induction hp using Submodule.span_induction with
    | mem x hx => exact hx.2
    | zero => exact homog_zero _
    | add x y _ _ hx hy => exact homog_add hx hy
    | smul r x _ hx => exact homog_smul r hx
  · exfalso
    apply h0
    have e : {p : MRingOver S ι | (∀ k, 0 ≤ c k) ∧ IsMultiHomog p (fun k => (c k).toNat)} = ∅ :=
      Set.eq_empty_of_forall_notMem fun p hp => hc hp.1
    unfold KH.quotPart at hm
    rw [e, Set.image_empty, Submodule.span_empty, Submodule.mem_bot] at hm
    exact hm

/- English proof (translation)
Establish `h` using `Submodule.mul_mem_mul hx hy`. Unfold `KH.quotPart at h ⊢`. Rewrite `h` using `[Submodule.span_mul_span]`. Use `Submodule.span_le.mpr ?_ h` and prove the remaining obligations. Introduce and unpack `_ ⟨_, ⟨p, ⟨hc, hp⟩, rfl⟩, _, ⟨q, ⟨hd, hq⟩, rfl⟩, rfl⟩`.

Use `Submodule.subset_span ⟨p * q, ⟨fun k => add_nonneg (hc k) (hd k), ?_⟩, map_mul _ _ _⟩` and prove the remaining obligations. Establish `e : (fun k => ((c + d) k).toNat) = (fun k => (c k).toNat) + fun k => (d k).toNat`. Use function extensionality and compare the values at `k`. Simplify using `[Int.toNat_add (hc k) (hd k)]`. Rewrite using `[e]`.

Conclude with `homog_mul hp hq`.
-/
theorem quotPart_mul {c d : K → ℤ} {x y : MRingOver S ι ⧸ V} (hx : x ∈ KH.quotPart S V c)
    (hy : y ∈ KH.quotPart S V d) : x * y ∈ KH.quotPart S V (c + d) := by
  have h := Submodule.mul_mem_mul hx hy
  unfold KH.quotPart at h ⊢
  rw [Submodule.span_mul_span] at h
  refine Submodule.span_le.mpr ?_ h
  rintro _ ⟨_, ⟨p, ⟨hc, hp⟩, rfl⟩, _, ⟨q, ⟨hd, hq⟩, rfl⟩, rfl⟩
  refine Submodule.subset_span ⟨p * q, ⟨fun k => add_nonneg (hc k) (hd k), ?_⟩, map_mul _ _ _⟩
  have e : (fun k => ((c + d) k).toNat) = (fun k => (c k).toNat) + fun k => (d k).toNat := by
    funext k
    simp [Int.toNat_add (hc k) (hd k)]
  rw [e]
  exact homog_mul hp hq

/- English proof (translation)
The claim follows from `Algebra.smul_def r a`.
-/
theorem smul_quot (r : MRingOver S ι) (a : MRingOver S ι ⧸ V) : r • a = Ideal.Quotient.mk V r * a :=
  Algebra.smul_def r a

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx => exact hx`. Consider the case `zero`. Conclude with `⟨0, 1, 0, homog_one, Submodule.zero_mem _, (LocalizedModule.zero_mk 1).symm⟩`. Consider the case `add x y _ _ hx hy`.

Take `⟨m, t, β, ht, hm, rfl⟩` from `hx`. Take `⟨m', t', β', ht', hm', rfl⟩` from `hy`. Use `⟨t' • m + t • m', t * t', β + β', homog_mul ht ht', ?_, LocalizedModule.mk_add_mk⟩` and prove the remaining obligations. Establish `deg : ∀ (s : T) (γ : K → ℕ), IsMultiHomog (s : MRingOver S ι) γ → Ideal.Quotient.mk V (s : MRingOver S ι) ∈ KH.quotPart S V (fun k => (γ k : ℤ))`. Introduce `s γ hs`.

Conclude with `Submodule.subset_span ⟨s, ⟨fun k => Int.natCast_nonneg _, by simpa using hs⟩, rfl⟩`. Establish `h1` using `quotPart_mul hm (deg t' β' ht')`. Establish `h2` using `quotPart_mul hm' (deg t β ht)`. Establish `e1 : ((c + fun k => (β k : ℤ)) + fun k => (β' k : ℤ)) = c + fun k => ((β + β') k : ℤ)`. Use function extensionality and compare the values at `k`.

Simplify using `only [Pi.add_apply, Nat.cast_add]`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : ((c + fun k => (β' k : ℤ)) + fun k => (β k : ℤ)) = c + fun k => ((β + β') k : ℤ)`. Use function extensionality and compare the values at `k`. Simplify using `only [Pi.add_apply, Nat.cast_add]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite `h1` using `[e1]`. Rewrite `h2` using `[e2]`. Rewrite using `[Submonoid.smul_def, Submonoid.smul_def, smul_quot, smul_quot, mul_comm _ m, mul_comm _ m']`. Conclude with `add_mem h1 h2`.

Consider the case `smul r x _ hx`. Take `⟨m, t, β, ht, hm, rfl⟩` from `hx`. Conclude with `⟨r • m, t, β, ht, Submodule.smul_mem _ r hm, LocalizedModule.smul'_mk r m t⟩`.
-/
theorem locPart_eq_mk {T : Submonoid (MRingOver S ι)} {c : K → ℤ}
    {x : LocalizedModule T (MRingOver S ι ⧸ V)} (hx : x ∈ KH.locPart ι (KH.quotPart S V) T c) :
    ∃ (m : MRingOver S ι ⧸ V) (t : T) (β : K → ℕ), IsMultiHomog (t : MRingOver S ι) β ∧
      m ∈ KH.quotPart S V (c + fun k => (β k : ℤ)) ∧ x = LocalizedModule.mk m t := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact hx
  | zero =>
    exact ⟨0, 1, 0, homog_one, Submodule.zero_mem _, (LocalizedModule.zero_mk 1).symm⟩
  | add x y _ _ hx hy =>
    obtain ⟨m, t, β, ht, hm, rfl⟩ := hx
    obtain ⟨m', t', β', ht', hm', rfl⟩ := hy
    refine ⟨t' • m + t • m', t * t', β + β', homog_mul ht ht', ?_, LocalizedModule.mk_add_mk⟩
    have deg : ∀ (s : T) (γ : K → ℕ), IsMultiHomog (s : MRingOver S ι) γ →
        Ideal.Quotient.mk V (s : MRingOver S ι) ∈ KH.quotPart S V (fun k => (γ k : ℤ)) := by
      intro s γ hs
      exact Submodule.subset_span ⟨s, ⟨fun k => Int.natCast_nonneg _, by simpa using hs⟩, rfl⟩
    have h1 := quotPart_mul hm (deg t' β' ht')
    have h2 := quotPart_mul hm' (deg t β ht)
    have e1 : ((c + fun k => (β k : ℤ)) + fun k => (β' k : ℤ)) = c + fun k => ((β + β') k : ℤ) := by
      funext k
      simp only [Pi.add_apply, Nat.cast_add]
      ring
    have e2 : ((c + fun k => (β' k : ℤ)) + fun k => (β k : ℤ)) = c + fun k => ((β + β') k : ℤ) := by
      funext k
      simp only [Pi.add_apply, Nat.cast_add]
      ring
    rw [e1] at h1
    rw [e2] at h2
    rw [Submonoid.smul_def, Submonoid.smul_def, smul_quot, smul_quot, mul_comm _ m, mul_comm _ m']
    exact add_mem h1 h2
  | smul r x _ hx =>
    obtain ⟨m, t, β, ht, hm, rfl⟩ := hx
    exact ⟨r • m, t, β, ht, Submodule.smul_mem _ r hm, LocalizedModule.smul'_mk r m t⟩

end Graded

variable {Ω : Type} [Field Ω] {y : (Σ k, ι k) → Ω}

/- English proof (translation)
Rewrite using `[show Int.castRingHom ℤ = RingHom.id ℤ from RingHom.ext_int _ _, MvPolynomial.map_id]`.
-/
theorem map_int (f : MRing ι) : MvPolynomial.map (Int.castRingHom ℤ) f = f := by
  rw [show Int.castRingHom ℤ = RingHom.id ℤ from RingHom.ext_int _ _, MvPolynomial.map_id]

variable (y) in

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a => simp [mConeMap]`. Consider the case `add p q hp hq => rw [map_add, map_add, map_add, hp, hq]`. Consider the case `mul_X p n hp => rw [map_mul, map_mul, map_mul, hp]`. Simplify using `[mConeMap]`.
-/
theorem aeval_eq_eval_mConeMap (f : MRing ι) :
    aeval y f = MvPolynomial.eval (fun _ : K => (1 : Ω)) (mConeMap y f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [mConeMap]
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p n hp => rw [map_mul, map_mul, map_mul, hp]; simp [mConeMap]

/- English proof (translation)
Establish `h : idealOver y ℤ ≤ RingHom.ker (aeval y : MRing ι →ₐ[ℤ] Ω)`. Use `Ideal.map_le_iff_le_comap.mpr fun g hg => ?_` and prove the remaining obligations. Rewrite using `[Ideal.mem_comap, RingHom.mem_ker, map_int, aeval_eq_eval_mConeMap, RingHom.mem_ker.mp hg, map_zero]`. Conclude with `RingHom.mem_ker.mp (h hf)`.
-/
theorem aeval_eq_zero_of_mem {f : MRing ι} (hf : f ∈ idealOver y ℤ) : aeval y f = 0 := by
  have h : idealOver y ℤ ≤ RingHom.ker (aeval y : MRing ι →ₐ[ℤ] Ω) := by
    refine Ideal.map_le_iff_le_comap.mpr fun g hg => ?_
    rw [Ideal.mem_comap, RingHom.mem_ker, map_int, aeval_eq_eval_mConeMap, RingHom.mem_ker.mp hg, map_zero]
  exact RingHom.mem_ker.mp (h hf)

/- English proof (translation)
Proceed by induction on `ht using Submonoid.closure_induction with`. Consider the case `mem x hx`. Take `⟨k, i, hi, rfl⟩` from `hx`. Rewrite using `[aeval_X]`. Conclude with `hI k i hi`.

Consider the case `one => simp`. Consider the case `mul x x' _ _ hx hx' => rw [map_mul]`. Conclude with `mul_ne_zero hx hx'`.
-/
theorem cellMon_aeval_ne {I : ∀ k, Finset (ι k)} (hI : ∀ k, ∀ i ∈ I k, y ⟨k, i⟩ ≠ 0) {t : MRing ι}
    (ht : t ∈ KH.cellMon ℤ I) : aeval y t ≠ 0 := by
  induction ht using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨k, i, hi, rfl⟩ := hx
    rw [aeval_X]
    exact hI k i hi
  | one => simp
  | mul x x' _ _ hx hx' => rw [map_mul]; exact mul_ne_zero hx hx'

variable (y) in

/- English proof (translation)
Rewrite using `[g.as_sum, map_sum, Finset.sum_div]`. Use `Subalgebra.sum_mem _ fun m hm => ?_` and prove the remaining obligations. Rewrite using `[aeval_monomial, mul_div_assoc]`. Use `Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) ?_` and prove the remaining obligations. Establish `key : m.prod (fun p e => y p ^ e) / ∏ k, y ⟨k, c k⟩ ^ d k = ∏ p, (y p / y ⟨p.1, c p.1⟩) ^ m p`.

Rewrite using `[Finsupp.prod_fintype _ _ (by simp)]`. Simplify using `only [div_pow]`. Rewrite using `[Finset.prod_div_distrib]`. Use `congr 1`. Rewrite using `[Fintype.prod_sigma]`.

Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `only`. Rewrite using `[Finset.prod_pow_eq_pow_sum, hg m hm k]`. Rewrite using `[key]`. Conclude with `Subalgebra.prod_mem _ fun p _ => Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_range_self (f := fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) p)) _`.
-/
theorem aeval_div_mem (c : ∀ k, ι k) {g : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d) :
    aeval y g / ∏ k, y ⟨k, c k⟩ ^ d k ∈ chartRingZ y c := by
  classical
  rw [g.as_sum, map_sum, Finset.sum_div]
  refine Subalgebra.sum_mem _ fun m hm => ?_
  rw [aeval_monomial, mul_div_assoc]
  refine Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) ?_
  have key : m.prod (fun p e => y p ^ e) / ∏ k, y ⟨k, c k⟩ ^ d k = ∏ p, (y p / y ⟨p.1, c p.1⟩) ^ m p := by
    rw [Finsupp.prod_fintype _ _ (by simp)]
    simp only [div_pow]
    rw [Finset.prod_div_distrib]
    congr 1
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    dsimp only
    rw [Finset.prod_pow_eq_pow_sum, hg m hm k]
  rw [key]
  exact Subalgebra.prod_mem _ fun p _ => Subalgebra.pow_mem _
    (Algebra.subset_adjoin (Set.mem_range_self (f := fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) p)) _

/- English proof (translation)
Take `⟨e, F, ⟨d, hF, hd, hv⟩, -, -⟩` from `ht`. Establish `hpe : ∏ k, y ⟨k, c k⟩ ^ e k ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)`. Establish `hpa : ∏ k, y ⟨k, c k⟩ ^ a k ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)`. Establish `hd' : ∏ k, y ⟨k, c k⟩ ^ d k = (∏ k, y ⟨k, c k⟩ ^ e k) * ∏ k, y ⟨k, c k⟩ ^ a k`. Rewrite using `[← Finset.prod_mul_distrib]`.

Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hc k), hd k]`. Establish `e1 : t * ∏ k, y ⟨k, c k⟩ ^ (-a k) = aeval y F / ∏ k, y ⟨k, c k⟩ ^ d k`. Rewrite using `[hv, hd']`. Simplify using `only [zpow_neg, Finset.prod_inv_distrib]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[e1]`. Conclude with `aeval_div_mem y c hF`.
-/
theorem mem_chartRingZ_of_isRep {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {T : Submonoid (MRing ι)}
    {x : LocalizedModule T (MRing ι ⧸ idealOver y ℤ)} {t : Ω} {a : K → ℤ}
    (ht : IsRep y ℤ T x c t a) : t * ∏ k, y ⟨k, c k⟩ ^ (-a k) ∈ chartRingZ y c := by
  obtain ⟨e, F, ⟨d, hF, hd, hv⟩, -, -⟩ := ht
  have hpe : ∏ k, y ⟨k, c k⟩ ^ e k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
  have hpa : ∏ k, y ⟨k, c k⟩ ^ a k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)
  have hd' : ∏ k, y ⟨k, c k⟩ ^ d k = (∏ k, y ⟨k, c k⟩ ^ e k) * ∏ k, y ⟨k, c k⟩ ^ a k := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hc k), hd k]
  have e1 : t * ∏ k, y ⟨k, c k⟩ ^ (-a k) = aeval y F / ∏ k, y ⟨k, c k⟩ ^ d k := by
    rw [hv, hd']
    simp only [zpow_neg, Finset.prod_inv_distrib]
    field_simp
  rw [e1]
  exact aeval_div_mem y c hF

def chartCell (c : ∀ k, ι k) : KH.Cell K ι 0 :=
  ⟨fun k => {c k}, fun _ => Finset.singleton_nonempty _, by simp⟩

/- English proof (translation)
Introduce `k i hi` and use `by rw [Finset.mem_singleton.mp hi]; exact hc k`.
-/
theorem chartCell_good {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    ∀ k, ∀ i ∈ (chartCell c).1 k, y ⟨k, i⟩ ≠ 0 :=
  fun k i hi => by rw [Finset.mem_singleton.mp hi]; exact hc k

/- English proof (translation)
Establish `hcard : ∀ k, (J.1 k).card = 1`. Introduce `k`. Establish `h0` using `(Finset.sum_eq_zero_iff.mp J.2.2) k (Finset.mem_univ k)`. Establish `h1` using `Finset.card_pos.mpr (J.2.1 k)`. Use linear arithmetic over natural numbers and integers.

Use `Subtype.ext (funext fun k => ?_)` and prove the remaining obligations. Take `⟨i, hi⟩` from `Finset.card_eq_one.mp (hcard k)`. Use `show J.1 k = {c k}`. Establish `h` using `hc k`. Rewrite `h`, the goal using `[hi]`.

Rewrite using `[Finset.mem_singleton.mp h]`.
-/
theorem eq_chartCell {J : KH.Cell K ι 0} {c : ∀ k, ι k} (hc : ∀ k, c k ∈ J.1 k) : J = chartCell c := by
  have hcard : ∀ k, (J.1 k).card = 1 := by
    intro k
    have h0 := (Finset.sum_eq_zero_iff.mp J.2.2) k (Finset.mem_univ k)
    have h1 := Finset.card_pos.mpr (J.2.1 k)
    omega
  refine Subtype.ext (funext fun k => ?_)
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp (hcard k)
  show J.1 k = {c k}
  have h := hc k
  rw [hi] at h ⊢
  rw [Finset.mem_singleton.mp h]

/- English proof (translation)
Proceed by induction on `ht using Submonoid.closure_induction with`. Consider the case `mem x hx`. Take `⟨k, i, hi, rfl⟩` from `hx`. Establish `hi' : i = c k` using `Finset.mem_singleton.mp hi`. Substitute `hi'` using the available equality.

Use `⟨Pi.single k 1, ?_⟩` and prove the remaining obligations. Unfold `cmon`. Rewrite using `[Finset.prod_eq_single k (fun k' _ hk' => by simp [hk']) (fun h => absurd (Finset.mem_univ k) h)]`. Simplify using the standard rewrite rules. Consider the case `one => exact ⟨0, by simp [cmon]⟩`.

Consider the case `mul x x' _ _ hx hx'`. Take `⟨f, rfl⟩` from `hx`. Take `⟨f', rfl⟩` from `hx'`. Conclude with `⟨f + f', (cmon_add c f f').symm⟩`.
-/
theorem mem_cellMon_chart {c : ∀ k, ι k} {t : MRing ι} (ht : t ∈ KH.cellMon ℤ (chartCell c).1) :
    ∃ e : K → ℕ, t = cmon c e := by
  classical
  induction ht using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨k, i, hi, rfl⟩ := hx
    have hi' : i = c k := Finset.mem_singleton.mp hi
    subst hi'
    refine ⟨Pi.single k 1, ?_⟩
    unfold cmon
    rw [Finset.prod_eq_single k (fun k' _ hk' => by simp [hk']) (fun h => absurd (Finset.mem_univ k) h)]
    simp
  | one => exact ⟨0, by simp [cmon]⟩
  | mul x x' _ _ hx hx' =>
    obtain ⟨f, rfl⟩ := hx
    obtain ⟨f', rfl⟩ := hx'
    exact ⟨f + f', (cmon_add c f f').symm⟩

/- English proof (translation)
Take `⟨m, t, β, ht, hm, rfl⟩` from `locPart_eq_mk hx`. Take `⟨e, he⟩` from `mem_cellMon_chart t.2`. Establish `hβ : β = e`. Establish `hne : cmon c e ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (X_ne_zero _)`. Take `⟨μ, hμ⟩ : (cmon c e).support.Nonempty` from `Finset.nonempty_iff_ne_empty.mpr (mt MvPolynomial.support_eq_empty.mp hne)`.

Rewrite `ht` using `[he]`. Conclude with `funext fun k => (ht μ hμ k).symm.trans (homog_cmon c e μ hμ k)`. Rewrite `hm` using `[hβ]`. Establish `hmem : ∀ f : K → ℕ, MvPolynomial.map (Int.castRingHom ℤ) (cmon c f) ∈ KH.cellMon ℤ (chartCell c).1` using `fun f => cmon_mem ℤ (I := (chartCell c).1) (fun k => Finset.mem_singleton_self (c k)) f`. Distinguish the cases in `h0 : m = 0`.

Substitute `h0` using the available equality. Use `⟨0, fun k => (-a k).toNat, 0, ⟨fun k => (a k).toNat, homog_zero _, fun k => by dsimp only; omega, by simp⟩, hmem _, ?_⟩` and prove the remaining obligations. Rewrite using `[map_zero, map_zero, LocalizedModule.zero_mk, LocalizedModule.zero_mk]`. Take `⟨hnn, p, hp, rfl⟩` from `quotPart_eq_mk hm h0`. Establish `hpe : ∏ k, y ⟨k, c k⟩ ^ e k ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)`.

Use `⟨aeval y p / ∏ k, y ⟨k, c k⟩ ^ e k, e, p, ⟨_, hp, fun k => ?_, (div_mul_cancel₀ _ hpe).symm⟩, hmem e, ?_⟩` and prove the remaining obligations. Use `hnn k` as an intermediate fact. Simplify using `only [Pi.add_apply] at this ⊢`. Use linear arithmetic over natural numbers and integers. Use `congr 1`.

Rewrite using `[map_int]`. Conclude with `Subtype.ext (he.trans (map_int _).symm)`.
-/
theorem exists_isRep {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {a : K → ℤ}
    {x : LocalizedModule (KH.cellMon ℤ (chartCell c).1) (MRing ι ⧸ idealOver y ℤ)}
    (hx : x ∈ KH.locPart ι (KH.quotPart ℤ (idealOver y ℤ)) (KH.cellMon ℤ (chartCell c).1) a) :
    ∃ s, IsRep y ℤ (KH.cellMon ℤ (chartCell c).1) x c s a := by
  obtain ⟨m, t, β, ht, hm, rfl⟩ := locPart_eq_mk hx
  obtain ⟨e, he⟩ := mem_cellMon_chart t.2
  have hβ : β = e := by
    have hne : cmon c e ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (X_ne_zero _)
    obtain ⟨μ, hμ⟩ : (cmon c e).support.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr (mt MvPolynomial.support_eq_empty.mp hne)
    rw [he] at ht
    exact funext fun k => (ht μ hμ k).symm.trans (homog_cmon c e μ hμ k)
  rw [hβ] at hm
  have hmem : ∀ f : K → ℕ, MvPolynomial.map (Int.castRingHom ℤ) (cmon c f) ∈ KH.cellMon ℤ (chartCell c).1 :=
    fun f => cmon_mem ℤ (I := (chartCell c).1) (fun k => Finset.mem_singleton_self (c k)) f
  by_cases h0 : m = 0
  · subst h0
    refine ⟨0, fun k => (-a k).toNat, 0, ⟨fun k => (a k).toNat, homog_zero _, fun k => by dsimp only; omega,
      by simp⟩, hmem _, ?_⟩
    rw [map_zero, map_zero, LocalizedModule.zero_mk, LocalizedModule.zero_mk]
  · obtain ⟨hnn, p, hp, rfl⟩ := quotPart_eq_mk hm h0
    have hpe : ∏ k, y ⟨k, c k⟩ ^ e k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
    refine ⟨aeval y p / ∏ k, y ⟨k, c k⟩ ^ e k, e, p, ⟨_, hp, fun k => ?_, (div_mul_cancel₀ _ hpe).symm⟩,
      hmem e, ?_⟩
    · have := hnn k
      simp only [Pi.add_apply] at this ⊢
      omega
    · congr 1
      · rw [map_int]
      · exact Subtype.ext (he.trans (map_int _).symm)

/- English proof (translation)
Take `⟨e1, F1, ⟨d1, -, -, hv1⟩, h1, rfl⟩` from `hx`. Take `⟨e2, F2, ⟨d2, -, -, hv2⟩, h2, hx'⟩` from `hx'`. Rewrite `hx'` using `[LocalizedModule.mk_eq]`. Take `⟨u, hu⟩` from `hx'`. Simplify using `only [Submonoid.smul_def, smul_mk, map_int] at hu`.

Rewrite `hu` using `[Ideal.Quotient.eq]`. Establish `h0` using `aeval_eq_zero_of_mem hu`. Establish `hu0` using `cellMon_aeval_ne hI u.2`. Rewrite `h0` using `[map_sub, map_mul, map_mul, map_mul, map_mul, aeval_cmon, aeval_cmon, hv1, hv2]`. Establish `p1 : ∏ k, y ⟨k, c k⟩ ^ e1 k ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)`.

Establish `p2 : ∏ k, y ⟨k, c' k⟩ ^ e2 k ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc' k)`. Establish `key : (aeval y (u : MRing ι) * (∏ k, y ⟨k, c' k⟩ ^ e2 k) * ∏ k, y ⟨k, c k⟩ ^ e1 k) * (s - s') = 0`. Take the linear combination `h0`. Break down `mul_eq_zero.mp key with h | h` into its components or cases. Conclude with `absurd h (mul_ne_zero (mul_ne_zero hu0 p2) p1)`.

Conclude with `sub_eq_zero.mp h`.
-/
theorem val_eq_of_isRep {I : ∀ k, Finset (ι k)} (hI : ∀ k, ∀ i ∈ I k, y ⟨k, i⟩ ≠ 0)
    {x : LocalizedModule (KH.cellMon ℤ I) (MRing ι ⧸ idealOver y ℤ)} {c c' : ∀ k, ι k} {s s' : Ω} {a : K → ℤ}
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (hc' : ∀ k, y ⟨k, c' k⟩ ≠ 0)
    (hx : IsRep y ℤ (KH.cellMon ℤ I) x c s a) (hx' : IsRep y ℤ (KH.cellMon ℤ I) x c' s' a) : s = s' := by
  obtain ⟨e1, F1, ⟨d1, -, -, hv1⟩, h1, rfl⟩ := hx
  obtain ⟨e2, F2, ⟨d2, -, -, hv2⟩, h2, hx'⟩ := hx'
  rw [LocalizedModule.mk_eq] at hx'
  obtain ⟨u, hu⟩ := hx'
  simp only [Submonoid.smul_def, smul_mk, map_int] at hu
  rw [Ideal.Quotient.eq] at hu
  have h0 := aeval_eq_zero_of_mem hu
  have hu0 := cellMon_aeval_ne hI u.2
  rw [map_sub, map_mul, map_mul, map_mul, map_mul, aeval_cmon, aeval_cmon, hv1, hv2] at h0
  have p1 : ∏ k, y ⟨k, c k⟩ ^ e1 k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
  have p2 : ∏ k, y ⟨k, c' k⟩ ^ e2 k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc' k)
  have key : (aeval y (u : MRing ι) * (∏ k, y ⟨k, c' k⟩ ^ e2 k) * ∏ k, y ⟨k, c k⟩ ^ e1 k) * (s - s') = 0 := by
    linear_combination h0
  rcases mul_eq_zero.mp key with h | h
  · exact absurd h (mul_ne_zero (mul_ne_zero hu0 p2) p1)
  · exact sub_eq_zero.mp h

section Cocycle

variable [LinearOrder K] [∀ k, LinearOrder (ι k)]

/- English proof (translation)
Establish `hne : ∀ k, (I.1 k).Nonempty` using `I.2.1`. Establish `h2 : (I.1 k0).card = 2` using `by rw [hI]; exact Finset.card_pair (ne_of_lt hlt)`. Establish `hface : ∀ i ∈ I.1 k0, (∀ l, (Function.update I.1 k0 ((I.1 k0).erase i) l).Nonempty) ∧ ∑ l, ((Function.update I.1 k0 ((I.1 k0).erase i) l).card - 1) = 0`. Introduce `i hi`. Establish `hc : ((I.1 k0).erase i).card = 1` using `by rw [Finset.card_erase_of_mem hi, h2]`.

Use `⟨fun l => ?_, Finset.sum_eq_zero fun l _ => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hl : l = k0`. Substitute `hl` using the available equality. Rewrite using `[Function.update_self]`. Conclude with `Finset.card_pos.mp (by omega)`.

Rewrite using `[Function.update_of_ne hl]`. Conclude with `hne l`. Distinguish the cases in `hl : l = k0`. Substitute `hl` using the available equality. Rewrite using `[Function.update_self, hc]`.

Both sides reduce to the same expression. Rewrite using `[Function.update_of_ne hl, hrest l hl]`. Both sides reduce to the same expression. Establish `hsumsign : ∑ l ∈ Finset.univ.filter (· < k0), ((I.1 l).card - 1) = 0` using `Finset.sum_eq_zero fun l hl => by rw [hrest l (ne_of_lt (Finset.mem_filter.mp hl).2)]; rfl`. Establish `hs1 : KH.faceSign I.1 k0 i1 = 1`.

Establish `f1 : (({i1, i2} : Finset (ι k0)).filter (· < i1)).card = 0`. Simplify using `[Finset.filter_insert, Finset.filter_singleton, not_lt.mpr hlt.le]`. Simplify using `only [KH.faceSign, hsumsign, hI, add_zero, f1]`. Evaluate the numerical expressions. Establish `hs2 : KH.faceSign I.1 k0 i2 = -1`.

Establish `f2 : (({i1, i2} : Finset (ι k0)).filter (· < i2)).card = 1`. Simplify using `[Finset.filter_insert, Finset.filter_singleton, hlt]`. Simplify using `only [KH.faceSign, hsumsign, hI, add_zero, f2]`. Evaluate the numerical expressions. Establish `hi1 : i1 ∈ I.1 k0` using `by rw [hI]; simp`.

Establish `hi2 : i2 ∈ I.1 k0` using `by rw [hI]; simp`. Establish `key : KH.cechD ℤ ι M 0 z I = KH.faceSign I.1 k0 i1 • KH.cellRes ℤ M (Function.update I.1 k0 ((I.1 k0).erase i1)) I.1 (z ⟨_, hface i1 hi1⟩) + KH.faceSign I.1 k0 i2 • KH.cellRes ℤ M (Function.update I.1 k0 ((I.1 k0).erase i2)) I.1 (z ⟨_, hface i2 hi2⟩)`. Rewrite using `[KH.cechD]`. Use `erw [LinearMap.pi_apply]`. Simplify using `only [LinearMap.sum_apply]`.

Rewrite using `[Finset.sum_eq_single k0]`. Rewrite using `[Finset.sum_eq_add_of_mem i1 i2 hi1 hi2 (ne_of_lt hlt)]`. Rewrite using `[dif_pos (hface i1 hi1), dif_pos (hface i2 hi2)]`. Both sides reduce to the same expression. Introduce `i hi hne'`.

Rewrite `hi` using `[hI]`. Simplify using `only [Finset.mem_insert, Finset.mem_singleton] at hi`. Break down `hi with rfl | rfl` into its components or cases. Conclude with `absurd rfl hne'.1`. Conclude with `absurd rfl hne'.2`.

Introduce `k _ hk`. Use `Finset.sum_eq_zero fun i hi => ?_` and prove the remaining obligations. Use `split_ifs with hc`. It suffices to derive a contradiction. Take `⟨hn, -⟩` from `hc`.

Establish `h3` using `hn k`. Rewrite `h3` using `[Function.update_self]`. Establish `h4` using `Finset.card_erase_of_mem hi`. Rewrite `h4` using `[hrest k hk]`. Establish `h5` using `Finset.card_pos.mpr h3`.

Use linear arithmetic over natural numbers and integers. Both sides reduce to the same expression. Introduce `h`. Conclude with `absurd (Finset.mem_univ k0) h`. Establish `e0 : KH.cechD ℤ ι M 0 z I = 0` using `by rw [hz]; rfl`.

Rewrite `e0` using `[key, hs1, hs2, one_smul, neg_one_smul, ← sub_eq_add_neg, sub_eq_zero]`. Take `⟨A1, hA1⟩` from `J1`. Take `⟨A2, hA2⟩` from `J2`. Simplify using `only at hJ1 hJ2`. Substitute `hJ1 hJ2` using the available equality.

Conclude with `e0`.
-/
theorem res_faces {M : Type} [AddCommGroup M] [Module (MRing ι) M] (z : KH.CechC ℤ ι M 0)
    (hz : KH.cechD ℤ ι M 0 z = 0) (I : KH.Cell K ι 1) (k0 : K) (i1 i2 : ι k0) (hlt : i1 < i2)
    (hI : I.1 k0 = {i1, i2}) (hrest : ∀ k ≠ k0, (I.1 k).card = 1) (J1 J2 : KH.Cell K ι 0)
    (hJ1 : J1.1 = Function.update I.1 k0 ((I.1 k0).erase i1))
    (hJ2 : J2.1 = Function.update I.1 k0 ((I.1 k0).erase i2)) :
    KH.cellRes ℤ M J1.1 I.1 (z J1) = KH.cellRes ℤ M J2.1 I.1 (z J2) := by
  have hne : ∀ k, (I.1 k).Nonempty := I.2.1
  have h2 : (I.1 k0).card = 2 := by rw [hI]; exact Finset.card_pair (ne_of_lt hlt)
  have hface : ∀ i ∈ I.1 k0, (∀ l, (Function.update I.1 k0 ((I.1 k0).erase i) l).Nonempty) ∧
      ∑ l, ((Function.update I.1 k0 ((I.1 k0).erase i) l).card - 1) = 0 := by
    intro i hi
    have hc : ((I.1 k0).erase i).card = 1 := by rw [Finset.card_erase_of_mem hi, h2]
    refine ⟨fun l => ?_, Finset.sum_eq_zero fun l _ => ?_⟩
    · by_cases hl : l = k0
      · subst hl
        rw [Function.update_self]
        exact Finset.card_pos.mp (by omega)
      · rw [Function.update_of_ne hl]
        exact hne l
    · by_cases hl : l = k0
      · subst hl
        rw [Function.update_self, hc]
        rfl
      · rw [Function.update_of_ne hl, hrest l hl]
        rfl
  have hsumsign : ∑ l ∈ Finset.univ.filter (· < k0), ((I.1 l).card - 1) = 0 :=
    Finset.sum_eq_zero fun l hl => by rw [hrest l (ne_of_lt (Finset.mem_filter.mp hl).2)]; rfl
  have hs1 : KH.faceSign I.1 k0 i1 = 1 := by
    have f1 : (({i1, i2} : Finset (ι k0)).filter (· < i1)).card = 0 := by
      simp [Finset.filter_insert, Finset.filter_singleton, not_lt.mpr hlt.le]
    simp only [KH.faceSign, hsumsign, hI, add_zero, f1]
    norm_num
  have hs2 : KH.faceSign I.1 k0 i2 = -1 := by
    have f2 : (({i1, i2} : Finset (ι k0)).filter (· < i2)).card = 1 := by
      simp [Finset.filter_insert, Finset.filter_singleton, hlt]
    simp only [KH.faceSign, hsumsign, hI, add_zero, f2]
    norm_num
  have hi1 : i1 ∈ I.1 k0 := by rw [hI]; simp
  have hi2 : i2 ∈ I.1 k0 := by rw [hI]; simp
  have key : KH.cechD ℤ ι M 0 z I =
      KH.faceSign I.1 k0 i1 • KH.cellRes ℤ M (Function.update I.1 k0 ((I.1 k0).erase i1)) I.1
        (z ⟨_, hface i1 hi1⟩) + KH.faceSign I.1 k0 i2 • KH.cellRes ℤ M
        (Function.update I.1 k0 ((I.1 k0).erase i2)) I.1 (z ⟨_, hface i2 hi2⟩) := by
    rw [KH.cechD]
    erw [LinearMap.pi_apply]
    simp only [LinearMap.sum_apply]
    rw [Finset.sum_eq_single k0]
    · rw [Finset.sum_eq_add_of_mem i1 i2 hi1 hi2 (ne_of_lt hlt)]
      · rw [dif_pos (hface i1 hi1), dif_pos (hface i2 hi2)]
        rfl
      · intro i hi hne'
        rw [hI] at hi
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi
        rcases hi with rfl | rfl
        · exact absurd rfl hne'.1
        · exact absurd rfl hne'.2
    · intro k _ hk
      refine Finset.sum_eq_zero fun i hi => ?_
      split_ifs with hc
      · exfalso
        obtain ⟨hn, -⟩ := hc
        have h3 := hn k
        rw [Function.update_self] at h3
        have h4 := Finset.card_erase_of_mem hi
        rw [hrest k hk] at h4
        have h5 := Finset.card_pos.mpr h3
        omega
      · rfl
    · intro h
      exact absurd (Finset.mem_univ k0) h
  have e0 : KH.cechD ℤ ι M 0 z I = 0 := by rw [hz]; rfl
  rw [key, hs1, hs2, one_smul, neg_one_smul, ← sub_eq_add_neg, sub_eq_zero] at e0
  obtain ⟨A1, hA1⟩ := J1
  obtain ⟨A2, hA2⟩ := J2
  simp only at hJ1 hJ2
  subst hJ1 hJ2
  exact e0

variable {a : K → ℤ} {v : KH.CechC ℤ ι (MRing ι ⧸ idealOver y ℤ) 0}

/- English proof (translation)
Establish `hne : c k0 ≠ d k0` using `ne_of_lt hlt`. Use `set A : ∀ k, Finset (ι k) := Function.update (fun k => ({c k} : Finset (ι k))) k0 {c k0, d k0} with hAdef`. Establish `hA0 : A k0 = {c k0, d k0}` using `Function.update_self _ _ _`. Establish `hAk : ∀ k ≠ k0, A k = {c k}` using `fun k hk => Function.update_of_ne hk _ _`. Establish `hAne : ∀ k, (A k).Nonempty`.

Introduce `k`. Distinguish the cases in `hk : k = k0`. Substitute `hk` using the available equality. Rewrite using `[hA0]`. Conclude with `Finset.insert_nonempty _ _`.

Rewrite using `[hAk k hk]`. Conclude with `Finset.singleton_nonempty _`. Establish `hAsum : ∑ k, ((A k).card - 1) = 1`. Rewrite using `[Finset.sum_eq_single k0 (fun k _ hk => by rw [hAk k hk]; rfl) (fun h => absurd (Finset.mem_univ k0) h), hA0, Finset.card_pair hne]`. Establish `hIy : ∀ k, ∀ i ∈ A k, y ⟨k, i⟩ ≠ 0`.

Introduce `k i hi`. Distinguish the cases in `hk : k = k0`. Substitute `hk` using the available equality. Rewrite `hi` using `[hA0]`. Break down `Finset.mem_insert.mp hi with h | h` into its components or cases.

Rewrite using `[h]`. Conclude with `hc _`. Rewrite using `[Finset.mem_singleton.mp h]`. Conclude with `hd _`. Rewrite `hi` using `[hAk k hk, Finset.mem_singleton]`.

Rewrite using `[hi]`. Conclude with `hc k`. Establish `hrest : ∀ k ≠ k0, (A k).card = 1` using `fun k hk => by rw [hAk k hk]; rfl`. Establish `hsc : ∀ k, (chartCell c).1 k ⊆ A k`. Introduce `k`.

Use `show {c k} ⊆ A k`. Distinguish the cases in `hk : k = k0`. Substitute `hk` using the available equality. Rewrite using `[hA0]`. Simplify using the standard rewrite rules.

Rewrite using `[hAk k hk]`. Establish `hsd : ∀ k, (chartCell d).1 k ⊆ A k`. Introduce `k`. Use `show {d k} ⊆ A k`. Distinguish the cases in `hk : k = k0`.

Substitute `hk` using the available equality. Rewrite using `[hA0]`. Simplify using the standard rewrite rules. Rewrite using `[hAk k hk, hcd k hk]`. Establish `e` using `res_faces v hz ⟨A, hAne, hAsum⟩ k0 (c k0) (d k0) hlt hA0 hrest (chartCell d) (chartCell c) ?_ ?_`.

Rewrite `e` using `[cellRes_of_le (cellMon_mono hsd), cellRes_of_le (cellMon_mono hsc)]`. Establish `h1` using `hs.lift (cellMon_mono hsc)`. Establish `h2` using `ht.lift (cellMon_mono hsd)`. Rewrite `h1` using `[← e]`. Conclude with `val_eq_of_isRep hIy hc hd h1 h2`.

Use function extensionality and compare the values at `k`. Distinguish the cases in `hk : k = k0`. Substitute `hk show ({d k} : Finset (ι k)) = Function.update A k ((A k).erase (c k)) k` using the available equality. Rewrite using `[Function.update_self, hA0, Finset.erase_insert (by simpa using hne)]`. Use `show ({d k} : Finset (ι k)) = Function.update A k0 ((A k0).erase (c k0)) k`.

Rewrite using `[Function.update_of_ne hk, hAk k hk, hcd k hk]`. Use function extensionality and compare the values at `k`. Distinguish the cases in `hk : k = k0`. Substitute `hk show ({c k} : Finset (ι k)) = Function.update A k ((A k).erase (d k)) k` using the available equality. Rewrite using `[Function.update_self, hA0, Finset.pair_comm, Finset.erase_insert (by simpa using hne.symm)]`.

Use `show ({c k} : Finset (ι k)) = Function.update A k0 ((A k0).erase (d k0)) k`. Rewrite using `[Function.update_of_ne hk, hAk k hk]`.
-/
theorem val_step_lt (hz : KH.cechD ℤ ι _ 0 v = 0) {c d : ∀ k, ι k}
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (hd : ∀ k, y ⟨k, d k⟩ ≠ 0) (k0 : K) (hcd : ∀ k ≠ k0, c k = d k)
    (hlt : c k0 < d k0) {s t : Ω}
    (hs : IsRep y ℤ (KH.cellMon ℤ (chartCell c).1) (v (chartCell c)) c s a)
    (ht : IsRep y ℤ (KH.cellMon ℤ (chartCell d).1) (v (chartCell d)) d t a) : s = t := by
  classical
  have hne : c k0 ≠ d k0 := ne_of_lt hlt
  set A : ∀ k, Finset (ι k) := Function.update (fun k => ({c k} : Finset (ι k))) k0 {c k0, d k0} with hAdef
  have hA0 : A k0 = {c k0, d k0} := Function.update_self _ _ _
  have hAk : ∀ k ≠ k0, A k = {c k} := fun k hk => Function.update_of_ne hk _ _
  have hAne : ∀ k, (A k).Nonempty := by
    intro k
    by_cases hk : k = k0
    · subst hk
      rw [hA0]
      exact Finset.insert_nonempty _ _
    · rw [hAk k hk]
      exact Finset.singleton_nonempty _
  have hAsum : ∑ k, ((A k).card - 1) = 1 := by
    rw [Finset.sum_eq_single k0 (fun k _ hk => by rw [hAk k hk]; rfl)
      (fun h => absurd (Finset.mem_univ k0) h), hA0, Finset.card_pair hne]
  have hIy : ∀ k, ∀ i ∈ A k, y ⟨k, i⟩ ≠ 0 := by
    intro k i hi
    by_cases hk : k = k0
    · subst hk
      rw [hA0] at hi
      rcases Finset.mem_insert.mp hi with h | h
      · rw [h]; exact hc _
      · rw [Finset.mem_singleton.mp h]; exact hd _
    · rw [hAk k hk, Finset.mem_singleton] at hi
      rw [hi]
      exact hc k
  have hrest : ∀ k ≠ k0, (A k).card = 1 := fun k hk => by rw [hAk k hk]; rfl
  have hsc : ∀ k, (chartCell c).1 k ⊆ A k := by
    intro k
    show {c k} ⊆ A k
    by_cases hk : k = k0
    · subst hk
      rw [hA0]
      simp
    · rw [hAk k hk]
  have hsd : ∀ k, (chartCell d).1 k ⊆ A k := by
    intro k
    show {d k} ⊆ A k
    by_cases hk : k = k0
    · subst hk
      rw [hA0]
      simp
    · rw [hAk k hk, hcd k hk]
  have e := res_faces v hz ⟨A, hAne, hAsum⟩ k0 (c k0) (d k0) hlt hA0 hrest (chartCell d) (chartCell c) ?_ ?_
  · rw [cellRes_of_le (cellMon_mono hsd), cellRes_of_le (cellMon_mono hsc)] at e
    have h1 := hs.lift (cellMon_mono hsc)
    have h2 := ht.lift (cellMon_mono hsd)
    rw [← e] at h1
    exact val_eq_of_isRep hIy hc hd h1 h2
  · funext k
    by_cases hk : k = k0
    · subst hk
      show ({d k} : Finset (ι k)) = Function.update A k ((A k).erase (c k)) k
      rw [Function.update_self, hA0, Finset.erase_insert (by simpa using hne)]
    · show ({d k} : Finset (ι k)) = Function.update A k0 ((A k0).erase (c k0)) k
      rw [Function.update_of_ne hk, hAk k hk, hcd k hk]
  · funext k
    by_cases hk : k = k0
    · subst hk
      show ({c k} : Finset (ι k)) = Function.update A k ((A k).erase (d k)) k
      rw [Function.update_self, hA0, Finset.pair_comm, Finset.erase_insert (by simpa using hne.symm)]
    · show ({c k} : Finset (ι k)) = Function.update A k0 ((A k0).erase (d k0)) k
      rw [Function.update_of_ne hk, hAk k hk]

/- English proof (translation)
Break down `lt_trichotomy (c k0) (d k0) with h | h | h` into its components or cases. Conclude with `val_step_lt hz hc hd k0 hcd h hs ht`. Establish `e : c = d` using `funext fun k => by`. Distinguish the cases in `hk : k = k0`. Substitute `hk` using the available equality.

Conclude with `h`. Conclude with `hcd k hk`. Substitute `e` using the available equality. Conclude with `val_eq_of_isRep (chartCell_good hc) hc hc hs ht`. Conclude with `(val_step_lt hz hd hc k0 (fun k hk => (hcd k hk).symm) h ht hs).symm`.
-/
theorem val_step (hz : KH.cechD ℤ ι _ 0 v = 0) {c d : ∀ k, ι k}
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (hd : ∀ k, y ⟨k, d k⟩ ≠ 0) (k0 : K) (hcd : ∀ k ≠ k0, c k = d k) {s t : Ω}
    (hs : IsRep y ℤ (KH.cellMon ℤ (chartCell c).1) (v (chartCell c)) c s a)
    (ht : IsRep y ℤ (KH.cellMon ℤ (chartCell d).1) (v (chartCell d)) d t a) : s = t := by
  rcases lt_trichotomy (c k0) (d k0) with h | h | h
  · exact val_step_lt hz hc hd k0 hcd h hs ht
  · have e : c = d := funext fun k => by
      by_cases hk : k = k0
      · subst hk; exact h
      · exact hcd k hk
    subst e
    exact val_eq_of_isRep (chartCell_good hc) hc hc hs ht
  · exact (val_step_lt hz hd hc k0 (fun k hk => (hcd k hk).symm) h ht hs).symm

/- English proof (translation)
Establish `hmix : ∀ (U : Finset K) k, y ⟨k, (fun k => if k ∈ U then d k else c k) k⟩ ≠ 0`. Introduce `U k`. Simplify using `only`. Use `split_ifs`. Use `exacts [hd k, hc k]`.

Establish `key : ∀ U : Finset K, ∀ t, IsRep y ℤ (KH.cellMon ℤ (chartCell fun k => if k ∈ U then d k else c k).1) (v (chartCell fun k => if k ∈ U then d k else c k)) (fun k => if k ∈ U then d k else c k) t a → s = t`. Introduce `U`. Proceed by induction on `U using Finset.induction_on with`. Consider the case `empty`. Introduce `t ht`.

Establish `e0 : (fun k => if k ∈ (∅ : Finset K) then d k else c k) = c` using `funext fun k => by simp`. Rewrite `ht` using `[e0]`. Conclude with `val_eq_of_isRep (chartCell_good hc) hc hc hs ht`. Consider the case `insert k0 U hk0 ih`. Introduce `t ht`.

Take `⟨t', ht'⟩` from `exists_isRep (hmix U) (hloc _)`. Rewrite using `[ih t' ht']`. Conclude with `val_step hz (hmix U) (hmix (insert k0 U)) k0 (fun k hk => by simp [Finset.mem_insert, hk]) ht' ht`. Establish `e1 : (fun k => if k ∈ (Finset.univ : Finset K) then d k else c k) = d` using `funext fun k => by simp`. Establish `h` using `key Finset.univ t`.

Rewrite `h` using `[e1]`. Conclude with `h ht`.
-/
theorem val_chart_eq (hz : KH.cechD ℤ ι _ 0 v = 0)
    (hloc : ∀ J : KH.Cell K ι 0, v J ∈ KH.locPart ι (KH.quotPart ℤ (idealOver y ℤ)) (KH.cellMon ℤ J.1) a)
    {c d : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (hd : ∀ k, y ⟨k, d k⟩ ≠ 0) {s t : Ω}
    (hs : IsRep y ℤ (KH.cellMon ℤ (chartCell c).1) (v (chartCell c)) c s a)
    (ht : IsRep y ℤ (KH.cellMon ℤ (chartCell d).1) (v (chartCell d)) d t a) : s = t := by
  classical
  have hmix : ∀ (U : Finset K) k, y ⟨k, (fun k => if k ∈ U then d k else c k) k⟩ ≠ 0 := by
    intro U k
    dsimp only
    split_ifs
    exacts [hd k, hc k]
  have key : ∀ U : Finset K, ∀ t,
      IsRep y ℤ (KH.cellMon ℤ (chartCell fun k => if k ∈ U then d k else c k).1)
        (v (chartCell fun k => if k ∈ U then d k else c k)) (fun k => if k ∈ U then d k else c k) t a → s = t := by
    intro U
    induction U using Finset.induction_on with
    | empty =>
      intro t ht
      have e0 : (fun k => if k ∈ (∅ : Finset K) then d k else c k) = c := funext fun k => by simp
      rw [e0] at ht
      exact val_eq_of_isRep (chartCell_good hc) hc hc hs ht
    | insert k0 U hk0 ih =>
      intro t ht
      obtain ⟨t', ht'⟩ := exists_isRep (hmix U) (hloc _)
      rw [ih t' ht']
      exact val_step hz (hmix U) (hmix (insert k0 U)) k0 (fun k hk => by simp [Finset.mem_insert, hk]) ht' ht
  have e1 : (fun k => if k ∈ (Finset.univ : Finset K) then d k else c k) = d := funext fun k => by simp
  have h := key Finset.univ t
  rw [e1] at h
  exact h ht

end Cocycle

end ZeroCocycleSection

open ZeroCocycleSection GenOnFibres in

/- English proof (translation)
Introduce `K _ _ ι _ _ Ω _ y a v hv`. Take `⟨hv1, hv2⟩` from `hv`. Establish `hloc : ∀ J : KH.Cell K ι 0, v J ∈ KH.locPart ι (KH.quotPart ℤ (idealOver y ℤ)) (KH.cellMon ℤ J.1) a` using `fun J => hv1 J (Set.mem_univ _)`. Establish `hz : KH.cechD ℤ ι _ 0 v = 0` using `hv2`. Distinguish the cases in `hex : ∃ c : ∀ k, ι k, ∀ k, y ⟨k, c k⟩ ≠ 0`.

Take `⟨c0, hc0⟩` from `hex`. Take `⟨s, hs⟩` from `exists_isRep hc0 (hloc (chartCell c0))`. Establish `hmem : s ∈ chartLat y a 1`. Introduce `c hc`. Take `⟨t, ht⟩` from `exists_isRep hc (hloc (chartCell c))`.

Rewrite using `[val_chart_eq hz hloc hc0 hc hs ht]`. Simplify using `only [Nat.cast_one, one_mul]`. Conclude with `mem_chartRingZ_of_isRep hc ht`. Use `⟨s, hmem, funext fun J => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hJ : ∀ k, y ⟨k, cellChart J k⟩ ≠ 0`.

Establish `eJ` using `eq_chartCell (cellChart_mem J)`. Establish `h1` using `secCoch_spec (S := ℤ) hmem J hJ`. Take `⟨t, ht⟩` from `exists_isRep hJ (hloc (chartCell (cellChart J)))`. Establish `hst` using `val_chart_eq hz hloc hc0 hJ hs ht`. Rewrite `ht` using `[← hst, ← eJ]`.

Conclude with `h1.unique ht`. Use `push Not at hJ`. Take `⟨k, h0⟩` from `hJ`. Use `subsingleton_loc (S := ℤ) (y := y) (cellChart_mem J k) h0` as an intermediate fact. Conclude with `Subsingleton.elim _ _`.

Use `⟨0, zero_mem _, funext fun J => ?_⟩ push Not at hex` and prove the remaining obligations. Take `⟨k, h0⟩` from `hex (cellChart J)`. Use `subsingleton_loc (S := ℤ) (y := y) (cellChart_mem J k) h0` as an intermediate fact. Conclude with `Subsingleton.elim _ _`.
-/
theorem ZeroCocycleSection.proof : ZeroCocycleSection.Statement := by
  intro K _ _ ι _ _ Ω _ y a v hv
  classical
  obtain ⟨hv1, hv2⟩ := hv
  have hloc : ∀ J : KH.Cell K ι 0,
      v J ∈ KH.locPart ι (KH.quotPart ℤ (idealOver y ℤ)) (KH.cellMon ℤ J.1) a :=
    fun J => hv1 J (Set.mem_univ _)
  have hz : KH.cechD ℤ ι _ 0 v = 0 := hv2
  by_cases hex : ∃ c : ∀ k, ι k, ∀ k, y ⟨k, c k⟩ ≠ 0
  · obtain ⟨c0, hc0⟩ := hex
    obtain ⟨s, hs⟩ := exists_isRep hc0 (hloc (chartCell c0))
    have hmem : s ∈ chartLat y a 1 := by
      intro c hc
      obtain ⟨t, ht⟩ := exists_isRep hc (hloc (chartCell c))
      rw [val_chart_eq hz hloc hc0 hc hs ht]
      simp only [Nat.cast_one, one_mul]
      exact mem_chartRingZ_of_isRep hc ht
    refine ⟨s, hmem, funext fun J => ?_⟩
    by_cases hJ : ∀ k, y ⟨k, cellChart J k⟩ ≠ 0
    · have eJ := eq_chartCell (cellChart_mem J)
      have h1 := secCoch_spec (S := ℤ) hmem J hJ
      obtain ⟨t, ht⟩ := exists_isRep hJ (hloc (chartCell (cellChart J)))
      have hst := val_chart_eq hz hloc hc0 hJ hs ht
      rw [← hst, ← eJ] at ht
      exact h1.unique ht
    · push Not at hJ
      obtain ⟨k, h0⟩ := hJ
      have := subsingleton_loc (S := ℤ) (y := y) (cellChart_mem J k) h0
      exact Subsingleton.elim _ _
  · refine ⟨0, zero_mem _, funext fun J => ?_⟩
    push Not at hex
    obtain ⟨k, h0⟩ := hex (cellChart J)
    have := subsingleton_loc (S := ℤ) (y := y) (cellChart_mem J k) h0
    exact Subsingleton.elim _ _

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
