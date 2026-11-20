import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveVertPointNagata
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.CurveCountObjects
import GroundTheory.HeightsAndTheta.Heights.Intersections.PLocRingPow
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.MemMCoordIdealOfAevalEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace CurveVerticalPointNagata

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [Fintype K] [∀ k, Fintype (ι k)] in

/- English proof (translation)
Rewrite using `[aeval_def, show algebraMap ℤ S = Int.castRingHom S from RingHom.ext_int _ _]`.
-/
theorem aeval_eq_eval₂ {S : Type*} [CommRing S] [Algebra ℤ S] (v : (Σ k, ι k) → S) (f : MRing ι) :
    aeval v f = eval₂ (Int.castRingHom S) v f := by
  rw [aeval_def, show algebraMap ℤ S = Int.castRingHom S from RingHom.ext_int _ _]

abbrev comp (e : K → ℕ) (f : MRing ι) : MRing ι :=
  weightedHomogeneousComponent (Inter.LocRingPow.multiDegWeight ι) e f

/- English proof (translation)
The claim follows from `Inter.LocRingPow.isMultiHomog_iff.mpr (weightedHomogeneousComponent_isWeightedHomogeneous _ _)`.
-/
theorem isMultiHomog_comp (e : K → ℕ) (f : MRing ι) : IsMultiHomog (comp e f) e :=
  Inter.LocRingPow.isMultiHomog_iff.mpr (weightedHomogeneousComponent_isWeightedHomogeneous _ _)

/- English proof (translation)
Use `conv_lhs => rw [g.as_sum]`. Use `conv_rhs => rw [g.as_sum]`. Rewrite using `[map_sum, map_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations. Establish `hdeg` using `hg m hm`.

Simplify using `only [aeval_monomial]`. Rewrite using `[Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]`. Simplify using `only [mul_pow, Finset.prod_mul_distrib]`. Establish `hX : (∏ p : Σ k, ι k, t p.1 ^ m p) = ∏ k, t k ^ e k`. Rewrite using `[Fintype.prod_sigma]`.

Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Use `show ∏ i, t k ^ m ⟨k, i⟩ = _`. Rewrite using `[Finset.prod_pow_eq_pow_sum, hdeg k]`. Rewrite using `[hX]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem aeval_mul_of_isMultiHomog {S : Type*} [CommRing S] [Algebra ℤ S] (r : (Σ k, ι k) → S) (t : K → S) {g : MRing ι}
    {e : K → ℕ} (hg : IsMultiHomog g e) :
    aeval (fun p => r p * t p.1) g = aeval r g * ∏ k, t k ^ e k := by
  classical
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  rw [map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg := hg m hm
  simp only [aeval_monomial]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [mul_pow, Finset.prod_mul_distrib]
  have hX : (∏ p : Σ k, ι k, t p.1 ^ m p) = ∏ k, t k ^ e k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, t k ^ m ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hdeg k]
  rw [hX]
  ring

/- English proof (translation)
Use `(aeval_mul_of_isMultiHomog (fun p => (MvPolynomial.C (r p) : MvPolynomial K S)) MvPolynomial.X hg).trans ?_` and prove the remaining obligations. Use `congr 1`. Rewrite using `[aeval_eq_eval₂, aeval_eq_eval₂, MvPolynomial.eval₂_comp_left, show (MvPolynomial.C : S →+* MvPolynomial K S).comp (Int.castRingHom S) = Int.castRingHom _ from RingHom.ext_int _ _]`. Both sides reduce to the same expression.
-/
theorem aeval_C_mul_X_of_isMultiHomog {S : Type*} [CommRing S] [Algebra ℤ S] [Algebra ℤ (MvPolynomial K S)] (r : (Σ k, ι k) → S) {g : MRing ι}
    {e : K → ℕ} (hg : IsMultiHomog g e) :
    (aeval (fun p => MvPolynomial.C (r p) * MvPolynomial.X p.1) g : MvPolynomial K S) =
      MvPolynomial.C (aeval r g) * ∏ k, (MvPolynomial.X k : MvPolynomial K S) ^ e k := by
  refine (aeval_mul_of_isMultiHomog (fun p => (MvPolynomial.C (r p) : MvPolynomial K S)) MvPolynomial.X hg).trans ?_
  congr 1
  rw [aeval_eq_eval₂, aeval_eq_eval₂, MvPolynomial.eval₂_comp_left,
    show (MvPolynomial.C : S →+* MvPolynomial K S).comp (Int.castRingHom S) = Int.castRingHom _ from
      RingHom.ext_int _ _]
  rfl

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on' with`. Consider the case `monomial u a0`. Establish `hu : IsMultiHomog (monomial u a0 : MRing ι) (fun k => ∑ i, u ⟨k, i⟩)`. Introduce `m hm k`. Use `Finset.mem_singleton.mp (support_monomial_subset hm)` as an intermediate fact.

Substitute `this` using the available equality. Both sides reduce to the same expression. Rewrite using `[aeval_C_mul_X_of_isMultiHomog r hu]`. Establish `hmono : ∀ (v : S) (D : K → ℕ), MvPolynomial.C v * ∏ k, (MvPolynomial.X k : MvPolynomial K S) ^ D k = monomial (Finsupp.equivFunOnFinite.symm D) v`. Introduce `v D`.

Rewrite using `[monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]`. Both sides reduce to the same expression. Rewrite using `[hmono, coeff_monomial]`. Establish `hw` using `Inter.LocRingPow.isMultiHomog_iff.mp hu`. Distinguish the cases in `h : Finsupp.equivFunOnFinite.symm (fun k => ∑ i, u ⟨k, i⟩) = n`.

Rewrite using `[if_pos h, comp, ← h, Finsupp.coe_equivFunOnFinite_symm, hw.weightedHomogeneousComponent_same]`. Rewrite using `[if_neg h, comp, hw.weightedHomogeneousComponent_ne _ (fun e => h (by`. Rewrite using `[← e, Finsupp.equivFunOnFinite_symm_coe])), map_zero]`. Consider the case `add p q hp hq => rw [map_add, coeff_add, hp, hq, comp, comp, comp, map_add, map_add]`.
-/
theorem coeff_aeval_C_mul_X {S : Type*} [CommRing S] [Algebra ℤ S] [Algebra ℤ (MvPolynomial K S)] (r : (Σ k, ι k) → S) (f : MRing ι) (n : K →₀ ℕ) :
    (aeval (fun p => MvPolynomial.C (r p) * MvPolynomial.X p.1) f : MvPolynomial K S).coeff n =
      aeval r (comp (⇑n) f) := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial u a0 =>
    have hu : IsMultiHomog (monomial u a0 : MRing ι) (fun k => ∑ i, u ⟨k, i⟩) := by
      intro m hm k
      have := Finset.mem_singleton.mp (support_monomial_subset hm)
      subst this
      rfl
    rw [aeval_C_mul_X_of_isMultiHomog r hu]
    have hmono : ∀ (v : S) (D : K → ℕ), MvPolynomial.C v * ∏ k, (MvPolynomial.X k : MvPolynomial K S) ^ D k =
        monomial (Finsupp.equivFunOnFinite.symm D) v := by
      intro v D
      rw [monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
      rfl
    rw [hmono, coeff_monomial]
    have hw := Inter.LocRingPow.isMultiHomog_iff.mp hu
    by_cases h : Finsupp.equivFunOnFinite.symm (fun k => ∑ i, u ⟨k, i⟩) = n
    · rw [if_pos h, comp, ← h, Finsupp.coe_equivFunOnFinite_symm, hw.weightedHomogeneousComponent_same]
    · rw [if_neg h, comp, hw.weightedHomogeneousComponent_ne _ (fun e => h (by
        rw [← e, Finsupp.equivFunOnFinite_symm_coe])), map_zero]
  | add p q hp hq => rw [map_add, coeff_add, hp, hq, comp, comp, comp, map_add, map_add]

end CurveVerticalPointNagata

open CurveVerticalPointNagata in

/- English proof (translation)
Introduce `K _ ι _ Ω _ y s d hP hs hsP W hW c hc _ _ a b hb hab`. Establish `hPW : mCoordIdeal y ≤ W` using `le_sup_left.trans hW.1.1.2`. Establish `hPh : IsMultiHomogIdeal (mCoordIdeal y)` using `hP.2.1.2.1`. Establish `hWh : IsMultiHomogIdeal W` using `isMultiHomogIdeal_of_mem_minimalPrimes hPh hs hW.1`. Establish `hformP : ∀ (g : MRing ι) (e : K → ℕ), IsMultiHomog g e → g ∈ mCoordIdeal y → aeval y g = 0`.

Introduce `g e hg hgP`. Establish `h0 : mConeMap y g = 0` using `hgP`. Rewrite `h0` using `[LowerBoundFree.mConeMap_of_isMultiHomog y hg]`. Break down `mul_eq_zero.mp h0 with h | h` into its components or cases. Conclude with `MvPolynomial.C_eq_zero.mp h`.

Conclude with `absurd h (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (X_ne_zero _))`. Establish `hyc : ∀ k, y ⟨k, c k⟩ ≠ 0` using `fun k => ne_zero_of_X_notMem fun h => hc k (hPW h)`. Establish `hycp : ∀ e : K → ℕ, ∏ k, y ⟨k, c k⟩ ^ e k ≠ 0` using `fun e => Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hyc k)`. Use `set m := curvePtIdeal y W with hm`. Set `Bm` to `Localization.AtPrime m`.

Set `r : (Σ k, ι k) → Bm` to `fun p => IsLocalization.mk' Bm (a p) (⟨b p, hb p⟩ : m.primeCompl)`. Choose the witnesses or unpack the hypotheses as in `⟨φ, hφ, hφalg, hφmk, hφaeval⟩ : ∃ φ : Bm →+* Ω, Function.Injective φ ∧ (∀ β : curveRing y, φ (algebraMap _ Bm β) = β) ∧ (∀ (α : curveRing y) (β : m.primeCompl), (α : Ω) = (β : Ω) * φ (IsLocalization.mk' Bm α β)) ∧ ∀ g : MRing ι, φ (aeval r g) = aeval (fun p => y p / y ⟨p.1, c p.1 …`. Establish `hu : ∀ u : m.primeCompl, IsUnit ((curveRing y).subtype u)`. Introduce `u`. Use `isUnit_iff_ne_zero.mpr fun h => u.2 ?_` and prove the remaining obligations.

Establish `: (u : curveRing y) = 0` using `Subtype.ext h`. Rewrite using `[this]`. Conclude with `zero_mem _`. Use `⟨IsLocalization.lift hu, (IsLocalization.lift_injective_iff (hg := hu)).mpr fun x z => ⟨fun h => by rw [IsLocalization.injective Bm (Ideal.primeCompl_le_nonZeroDivisors m) h], fun h => by rw [Subtype.ext h]⟩, fun β => IsLocalization.lift_eq hu β, fun α β => by` and prove the remaining obligations. Use `(IsLocalization.lift_mk'_spec (S := Bm) hu α (IsLocalization.lift hu (IsLocalization.mk' Bm α β)) β).mp rfl` as an intermediate fact.

Conclude with `this, fun g => ?_⟩`. Rewrite using `[aeval_eq_eval₂, aeval_eq_eval₂, MvPolynomial.eval₂_comp_left, show (IsLocalization.lift hu).comp (Int.castRingHom Bm) = Int.castRingHom Ω from RingHom.ext_int _ _]`. Use `congr 1`. Use function extensionality and compare the values at `p`. Use `show IsLocalization.lift hu (IsLocalization.mk' Bm (a p) (⟨b p, hb p⟩ : m.primeCompl)) = _`.

Rewrite using `[IsLocalization.lift_mk'_spec]`. Conclude with `(hab p).symm`. Establish `hφev : ∀ (g : MRing ι) (e : K → ℕ), IsMultiHomog g e → φ (aeval r g) = aeval y g / ∏ k, y ⟨k, c k⟩ ^ e k` using `fun g e hg => by`. Establish `h1` using `aeval_mul_of_isMultiHomog y (fun k => (y ⟨k, c k⟩)⁻¹) hg`. Simplify using `only [inv_pow, Finset.prod_inv_distrib, ← div_eq_mul_inv] at h1`.

Rewrite using `[hφaeval, h1]`. Establish `hcrit : ∀ (g : MRing ι) (e : K → ℕ), IsMultiHomog g e → (g ∈ W ↔ aeval r g ∈ IsLocalRing.maximalIdeal Bm)`. Introduce `g e hg`. Establish `h3` using `(hCh K ι Ω y s d hP hs hsP W hW c hc).2.2 e g hg`. Prove the components needed by the constructor for the conclusion.

Introduce `hgW`. Take `⟨α, β, hα, hβ, he⟩` from `h3.mp hgW`. Establish `: aeval r g = IsLocalization.mk' Bm α (⟨β, hβ⟩ : m.primeCompl)`. Apply `hφ` to reduce the goal to its premises. Establish `h1` using `hφmk α ⟨β, hβ⟩`.

Establish `hβ0 : (β : Ω) ≠ 0` using `fun h => hβ (by rw [show β = 0 from Subtype.ext h]; exact zero_mem _)`. Rewrite using `[hφev g e hg]`. Apply `mul_left_cancel₀ hβ0` to reduce the goal to its premises. Rewrite using `[← h1, mul_div_assoc', he, mul_div_cancel_right₀ _ (hycp e)]`. Rewrite using `[this]`.

Conclude with `(IsLocalization.AtPrime.mk'_mem_maximal_iff Bm m α _).mpr hα`. Introduce `hg'`. Take `⟨⟨α, β⟩, hαβ⟩` from `IsLocalization.mk'_surjective m.primeCompl (aeval r g)`. Establish `hα : α ∈ m`. Rewrite `hg'` using `[← hαβ]`.

Conclude with `(IsLocalization.AtPrime.mk'_mem_maximal_iff Bm m α β).mp hg'`. Use `h3.mpr ⟨α, β, hα, β.2, ?_⟩` and prove the remaining obligations. Establish `h1` using `hφmk α β`. Express the relevant statement in the definitionally equal form `IsLocalization.mk' Bm α β = aeval r g at hαβ`. Rewrite `h1` using `[hαβ, hφev g e hg]`.

Rewrite using `[h1, mul_div_assoc', div_mul_cancel₀ _ (hycp e)]`. Set `ψ : MRing ι →ₐ[ℤ] MvPolynomial K Bm` to `aeval (fun p : (Σ k, ι k) => MvPolynomial.C (r p) * MvPolynomial.X p.1)`. Set `M` to `(IsLocalRing.maximalIdeal Bm).map (MvPolynomial.C : Bm →+* MvPolynomial K Bm)`. Set `N` to `mNagataRing K Bm`. Establish `hψcoeff : ∀ f (n : K →₀ ℕ), (ψ f).coeff n = aeval r (comp (⇑n) f)` using `fun f n => coeff_aeval_C_mul_X r f n`.

Establish `hψform : ∀ (G : MRing ι) (e : K → ℕ), IsMultiHomog G e → ψ G = MvPolynomial.C (aeval r G) * ∏ k, (MvPolynomial.X k : MvPolynomial K Bm) ^ e k` using `fun G e hG => aeval_C_mul_X_of_isMultiHomog r hG`. Establish `hrc : ∀ k, r ⟨k, c k⟩ = 1`. Introduce `k`. Apply `hφ` to reduce the goal to its premises. Establish `h1` using `hφaeval (X ⟨k, c k⟩)`.

Rewrite `h1` using `[aeval_X, aeval_X]`. Rewrite using `[h1, map_one]`. Conclude with `div_self (hyc k)`. Establish `hψX : ∀ k, ψ (X ⟨k, c k⟩) = MvPolynomial.X k`. Introduce `k`.

Rewrite using `[show ψ (X ⟨k, c k⟩) = MvPolynomial.C (r ⟨k, c k⟩) * MvPolynomial.X k from aeval_X _ _, hrc, map_one, one_mul]`. Establish `hψW : ∀ h ∈ W, ψ h ∈ M`. Introduce `h hh`. Rewrite using `[MvPolynomial.mem_map_C_iff]`. Introduce `n`.

Rewrite using `[hψcoeff]`. Conclude with `(hcrit _ _ (isMultiHomog_comp _ h)).mp (Inter.LocRingPow.component_mem hWh hh _)`. Establish `hψnot : ∀ g ∉ W, ψ g ∉ M`. Introduce `g hg hM`. Take `⟨D, hD⟩` from `Inter.LocRingPow.exists_component_not_mem hg`.

Rewrite `hM` using `[MvPolynomial.mem_map_C_iff]`. Use `hM (Finsupp.equivFunOnFinite.symm D)` as an intermediate fact. Rewrite `this` using `[hψcoeff, Finsupp.coe_equivFunOnFinite_symm]`. Conclude with `hD ((hcrit _ _ (isMultiHomog_comp D g)).mpr this)`. Establish `hψP : ∀ f, ψ f = 0 ↔ f ∈ mCoordIdeal y`.

Introduce `f`. Prove the components needed by the constructor for the conclusion. Introduce `h0`. Assume the negation of the conclusion as `hf`. Take `⟨D, hD⟩` from `Inter.LocRingPow.exists_component_not_mem hf`.

Establish `h1` using `congrArg (fun q => MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm D) q) h0`. Simplify using `only [MvPolynomial.coeff_zero] at h1`. Rewrite `h1` using `[hψcoeff, Finsupp.coe_equivFunOnFinite_symm]`. Establish `h2` using `congrArg φ h1`. Rewrite `h2` using `[hφev _ _ (isMultiHomog_comp D f), map_zero, div_eq_zero_iff]`.

Conclude with `hD (LowerBoundFree.mem_mCoordIdeal_of_aeval_eq_zero y (isMultiHomog_comp D f) (h2.resolve_right (hycp D)))`. Introduce `hf`. Use extensionality with `n`. Rewrite using `[hψcoeff, MvPolynomial.coeff_zero]`. Apply `hφ` to reduce the goal to its premises.

Rewrite using `[hφev _ _ (isMultiHomog_comp _ f), hformP _ _ (isMultiHomog_comp _ f) (Inter.LocRingPow.component_mem hPh hf _), zero_div, map_zero]`. Establish `hunit : ∀ g : W.primeCompl, IsUnit ((algebraMap (MvPolynomial K Bm) N).comp ψ.toRingHom g)` using `fun g => IsLocalization.map_units N (⟨ψ g, hψnot g g.2⟩ : M.primeCompl)`. Set `Φ : Localization.AtPrime W →+* N` to `IsLocalization.lift hunit`. Establish `hΦ : ∀ f, Φ (algebraMap _ _ f) = algebraMap (MvPolynomial K Bm) N (ψ f)` using `fun f => IsLocalization.lift_eq hunit f`. Establish `hΦmk : ∀ (f : MRing ι) (g : W.primeCompl) (v : N), Φ (IsLocalization.mk' _ f g) = v ↔ algebraMap (MvPolynomial K Bm) N (ψ f) = algebraMap (MvPolynomial K Bm) N (ψ g) * v` using `fun f g v => IsLocalization.lift_mk'_spec hunit f v g`.

Establish `hinjN : Function.Injective (algebraMap (MvPolynomial K Bm) N)` using `IsLocalization.injective (R := MvPolynomial K Bm) (M := M.primeCompl) N (Ideal.primeCompl_le_nonZeroDivisors M)`. Use `⟨Φ, ?_, ?_, hΦ⟩` and prove the remaining obligations. Establish `hΦmax : ∀ x ∈ IsLocalRing.maximalIdeal (Localization.AtPrime W), Φ x ∈ M.map (algebraMap (MvPolynomial K Bm) N)`. Introduce `x hx`. Rewrite `hx` using `[← Localization.AtPrime.map_eq_maximalIdeal]`.

Establish `hle : (W.map (algebraMap _ (Localization.AtPrime W))).map Φ ≤ M.map (algebraMap (MvPolynomial K Bm) N)`. Rewrite using `[Ideal.map_map, Ideal.map_le_iff_le_comap]`. Introduce `h hh`. Rewrite using `[Ideal.mem_comap, RingHom.comp_apply, hΦ]`. Conclude with `Ideal.mem_map_of_mem _ (hψW h hh)`.

Conclude with `hle (Ideal.mem_map_of_mem Φ hx)`. Establish `hloc : ∀ x, IsUnit (Φ x) → IsUnit x`. Introduce `x hx`. Assume the negation of the conclusion as `hu`. Establish `hmem` using `hΦmax x ((IsLocalRing.mem_maximalIdeal _).mpr hu)`.

Rewrite `hmem` using `[Localization.AtPrime.map_eq_maximalIdeal]`. Conclude with `(IsLocalRing.mem_maximalIdeal _).mp hmem hx`. Establish `hpoly : ∀ f : MRing ι, ∃ x, Φ x = algebraMap (MvPolynomial K Bm) N (MvPolynomial.C (aeval r f))`. Introduce `f`. Proceed by induction on `f using MvPolynomial.induction_on' with`.

Consider the case `monomial u a0`. Establish `hu : IsMultiHomog (monomial u a0 : MRing ι) (fun k => ∑ i, u ⟨k, i⟩)`. Introduce `n hn k`. Use `Finset.mem_singleton.mp (support_monomial_subset hn)` as an intermediate fact. Substitute `this` using the available equality.

Both sides reduce to the same expression. Establish `hXc : (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ (∑ i, u ⟨k, i⟩)) ∈ W.primeCompl` using `Submonoid.prod_mem _ fun k _ => Submonoid.pow_mem _ (show X ⟨k, c k⟩ ∈ W.primeCompl from hc k) _`. Establish `hψXc : ψ (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ (∑ i, u ⟨k, i⟩)) = ∏ k, (MvPolynomial.X k : MvPolynomial K Bm) ^ (∑ i, u ⟨k, i⟩)`. Simplify using `only [map_prod, map_pow, hψX]`. Use `⟨IsLocalization.mk' (Localization.AtPrime W) (monomial u a0) (⟨_, hXc⟩ : W.primeCompl), (hΦmk _ _ _).mpr ?_⟩` and prove the remaining obligations.

Rewrite using `[← map_mul]`. Use `congr 1`. Use `show ψ (monomial u a0) = ψ (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ (∑ i, u ⟨k, i⟩)) * _`. Rewrite using `[hψform _ _ hu, hψXc, mul_comm]`. Consider the case `add p q hp hq`.

Take `⟨x, hx⟩` from `hp`. Take `⟨x', hx'⟩` from `hq`. Conclude with `⟨x + x', by rw [map_add, hx, hx', map_add, map_add, map_add]⟩`. Establish `hC : ∀ q : Bm, ∃ x, Φ x = algebraMap (MvPolynomial K Bm) N (MvPolynomial.C q)`. Introduce `q`.

Take `⟨⟨β, γ⟩, hq⟩` from `IsLocalization.mk'_surjective m.primeCompl q`. Express the relevant statement in the definitionally equal form `IsLocalization.mk' Bm β γ = q at hq`. Substitute `hq` using the available equality. Establish `hB : ∀ β : curveRing y, ∃ f : MRing ι, aeval r f = algebraMap _ Bm β`. Introduce `β`.

Establish `hβ` using `mem_curveRing.mp β.2 c hyc`. Rewrite `hβ` using `[chartRingZ, Algebra.adjoin_range_eq_range_aeval]`. Take `⟨f, hf⟩` from `hβ`. Conclude with `⟨f, hφ (by rw [hφaeval, hφalg]; exact hf)⟩`. Take `⟨f1, e1⟩` from `hB β`.

Take `⟨f2, e2⟩` from `hB γ`. Take `⟨x1, h1⟩` from `hpoly f1`. Take `⟨x2, h2⟩` from `hpoly f2`. Take `⟨u, rfl⟩` from `hloc x2 (by`. Rewrite using `[h2, e2]`.

Conclude with `((IsLocalization.map_units Bm γ).map MvPolynomial.C).map (algebraMap _ N))`. Establish `hβγ : algebraMap (MvPolynomial K Bm) N (MvPolynomial.C (algebraMap _ Bm β)) = algebraMap (MvPolynomial K Bm) N (MvPolynomial.C (IsLocalization.mk' Bm β γ)) * Φ ↑u`. Rewrite using `[h2, e2, ← map_mul, ← map_mul, IsLocalization.mk'_spec]`. Use `⟨x1 * ↑u⁻¹, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, h1, e1, hβγ, mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one]`.

Establish `hIm : ∀ q : MvPolynomial K Bm, ∃ x, Φ x = algebraMap (MvPolynomial K Bm) N q`. Introduce `q`. Use `MvPolynomial.induction_on (motive := fun q => ∃ x, Φ x = algebraMap (MvPolynomial K Bm) N q) q hC (fun p q hp hq => ?_) (fun p k hp => ?_)` and prove the remaining obligations. Take `⟨x, hx⟩` from `hp`. Take `⟨x', hx'⟩` from `hq`.

Conclude with `⟨x + x', by rw [map_add, hx, hx', map_add]⟩`. Take `⟨x, hx⟩` from `hp`. Use `⟨x * algebraMap (MRing ι) (Localization.AtPrime W) (X ⟨k, c k⟩ : MRing ι), ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, hx, hΦ, hψX, map_mul]`. Introduce `z`.

Take `⟨⟨q, q'⟩, hz⟩` from `IsLocalization.mk'_surjective M.primeCompl z`. Express the relevant statement in the definitionally equal form `IsLocalization.mk' N q q' = z at hz`. Substitute `hz` using the available equality. Take `⟨x1, h1⟩` from `hIm q`. Take `⟨x2, h2⟩` from `hIm q'`.

Take `⟨u, rfl⟩` from `hloc x2 (by rw [h2]; exact IsLocalization.map_units N q')`. Use `⟨x1 * ↑u⁻¹, ?_⟩` and prove the remaining obligations. Rewrite using `[IsLocalization.eq_mk'_iff_mul_eq, ← h1, ← h2, ← map_mul, mul_assoc, Units.inv_mul, mul_one]`. Use extensionality with `x`. Rewrite using `[RingHom.mem_ker]`.

Prove the components needed by the constructor for the conclusion. Introduce `hx`. Take `⟨⟨f, g⟩, rfl⟩` from `IsLocalization.mk'_surjective W.primeCompl x`. Establish `h1` using `(hΦmk f g 0).mp hx`. Rewrite `h1` using `[mul_zero, ← map_zero (algebraMap (MvPolynomial K Bm) N)]`.

Establish `hf : f ∈ mCoordIdeal y` using `(hψP f).mp (hinjN h1)`. Express the relevant statement in the definitionally equal form `IsLocalization.mk' (Localization.AtPrime W) f g ∈ _`. Rewrite using `[IsLocalization.mk'_eq_mul_mk'_one]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hf)`. Introduce `hx`.

Establish `hle : (mCoordIdeal y).map (algebraMap _ (Localization.AtPrime W)) ≤ RingHom.ker Φ`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `f hf`. Rewrite using `[Ideal.mem_comap, RingHom.mem_ker, hΦ, (hψP f).mpr hf, map_zero]`. Conclude with `hle hx`.
-/
theorem CurveVertPointNagata.proof (hCh : CurveVertPointChart.Statement) : CurveVertPointNagata.Statement := by
  intro K _ ι _ Ω _ y s d hP hs hsP W hW c hc _ _ a b hb hab
  classical

  have hPW : mCoordIdeal y ≤ W := le_sup_left.trans hW.1.1.2
  have hPh : IsMultiHomogIdeal (mCoordIdeal y) := hP.2.1.2.1
  have hWh : IsMultiHomogIdeal W := isMultiHomogIdeal_of_mem_minimalPrimes hPh hs hW.1
  have hformP : ∀ (g : MRing ι) (e : K → ℕ), IsMultiHomog g e → g ∈ mCoordIdeal y → aeval y g = 0 := by
    intro g e hg hgP
    have h0 : mConeMap y g = 0 := hgP
    rw [LowerBoundFree.mConeMap_of_isMultiHomog y hg] at h0
    rcases mul_eq_zero.mp h0 with h | h
    · exact MvPolynomial.C_eq_zero.mp h
    · exact absurd h (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (X_ne_zero _))
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => ne_zero_of_X_notMem fun h => hc k (hPW h)
  have hycp : ∀ e : K → ℕ, ∏ k, y ⟨k, c k⟩ ^ e k ≠ 0 := fun e =>
    Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hyc k)

  set m := curvePtIdeal y W with hm
  let Bm := Localization.AtPrime m
  let r : (Σ k, ι k) → Bm := fun p =>
    IsLocalization.mk' Bm (a p) (⟨b p, hb p⟩ : m.primeCompl)
  obtain ⟨φ, hφ, hφalg, hφmk, hφaeval⟩ : ∃ φ : Bm →+* Ω, Function.Injective φ ∧
      (∀ β : curveRing y, φ (algebraMap _ Bm β) = β) ∧
      (∀ (α : curveRing y) (β : m.primeCompl), (α : Ω) = (β : Ω) * φ (IsLocalization.mk' Bm α β)) ∧
      ∀ g : MRing ι, φ (aeval r g) = aeval (fun p => y p / y ⟨p.1, c p.1⟩) g := by
    have hu : ∀ u : m.primeCompl, IsUnit ((curveRing y).subtype u) := by
      intro u
      refine isUnit_iff_ne_zero.mpr fun h => u.2 ?_
      have : (u : curveRing y) = 0 := Subtype.ext h
      rw [this]
      exact zero_mem _
    refine ⟨IsLocalization.lift hu, (IsLocalization.lift_injective_iff (hg := hu)).mpr fun x z =>
      ⟨fun h => by rw [IsLocalization.injective Bm (Ideal.primeCompl_le_nonZeroDivisors m) h],
        fun h => by rw [Subtype.ext h]⟩, fun β => IsLocalization.lift_eq hu β,
      fun α β => by
        have := (IsLocalization.lift_mk'_spec (S := Bm) hu α
          (IsLocalization.lift hu (IsLocalization.mk' Bm α β)) β).mp rfl
        exact this, fun g => ?_⟩
    rw [aeval_eq_eval₂, aeval_eq_eval₂, MvPolynomial.eval₂_comp_left,
      show (IsLocalization.lift hu).comp (Int.castRingHom Bm) = Int.castRingHom Ω from RingHom.ext_int _ _]
    congr 1
    funext p
    show IsLocalization.lift hu (IsLocalization.mk' Bm (a p) (⟨b p, hb p⟩ : m.primeCompl)) = _
    rw [IsLocalization.lift_mk'_spec]
    exact (hab p).symm
  have hφev : ∀ (g : MRing ι) (e : K → ℕ), IsMultiHomog g e →
      φ (aeval r g) = aeval y g / ∏ k, y ⟨k, c k⟩ ^ e k := fun g e hg => by
    have h1 := aeval_mul_of_isMultiHomog y (fun k => (y ⟨k, c k⟩)⁻¹) hg
    simp only [inv_pow, Finset.prod_inv_distrib, ← div_eq_mul_inv] at h1
    rw [hφaeval, h1]

  have hcrit : ∀ (g : MRing ι) (e : K → ℕ), IsMultiHomog g e →
      (g ∈ W ↔ aeval r g ∈ IsLocalRing.maximalIdeal Bm) := by
    intro g e hg
    have h3 := (hCh K ι Ω y s d hP hs hsP W hW c hc).2.2 e g hg
    constructor
    · intro hgW
      obtain ⟨α, β, hα, hβ, he⟩ := h3.mp hgW
      have : aeval r g = IsLocalization.mk' Bm α (⟨β, hβ⟩ : m.primeCompl) := by
        apply hφ
        have h1 := hφmk α ⟨β, hβ⟩
        have hβ0 : (β : Ω) ≠ 0 := fun h => hβ (by rw [show β = 0 from Subtype.ext h]; exact zero_mem _)
        rw [hφev g e hg]
        apply mul_left_cancel₀ hβ0
        rw [← h1, mul_div_assoc', he, mul_div_cancel_right₀ _ (hycp e)]
      rw [this]
      exact (IsLocalization.AtPrime.mk'_mem_maximal_iff Bm m α _).mpr hα
    · intro hg'
      obtain ⟨⟨α, β⟩, hαβ⟩ := IsLocalization.mk'_surjective m.primeCompl (aeval r g)
      have hα : α ∈ m := by
        rw [← hαβ] at hg'
        exact (IsLocalization.AtPrime.mk'_mem_maximal_iff Bm m α β).mp hg'
      refine h3.mpr ⟨α, β, hα, β.2, ?_⟩
      have h1 := hφmk α β
      change IsLocalization.mk' Bm α β = aeval r g at hαβ
      rw [hαβ, hφev g e hg] at h1
      rw [h1, mul_div_assoc', div_mul_cancel₀ _ (hycp e)]

  let ψ : MRing ι →ₐ[ℤ] MvPolynomial K Bm :=
    aeval (fun p : (Σ k, ι k) => MvPolynomial.C (r p) * MvPolynomial.X p.1)
  let M := (IsLocalRing.maximalIdeal Bm).map (MvPolynomial.C : Bm →+* MvPolynomial K Bm)
  let N := mNagataRing K Bm
  have hψcoeff : ∀ f (n : K →₀ ℕ), (ψ f).coeff n = aeval r (comp (⇑n) f) := fun f n =>
    coeff_aeval_C_mul_X r f n
  have hψform : ∀ (G : MRing ι) (e : K → ℕ), IsMultiHomog G e →
      ψ G = MvPolynomial.C (aeval r G) * ∏ k, (MvPolynomial.X k : MvPolynomial K Bm) ^ e k :=
    fun G e hG => aeval_C_mul_X_of_isMultiHomog r hG
  have hrc : ∀ k, r ⟨k, c k⟩ = 1 := by
    intro k
    apply hφ
    have h1 := hφaeval (X ⟨k, c k⟩)
    rw [aeval_X, aeval_X] at h1
    rw [h1, map_one]
    exact div_self (hyc k)
  have hψX : ∀ k, ψ (X ⟨k, c k⟩) = MvPolynomial.X k := by
    intro k
    rw [show ψ (X ⟨k, c k⟩) = MvPolynomial.C (r ⟨k, c k⟩) * MvPolynomial.X k from aeval_X _ _, hrc, map_one,
      one_mul]
  have hψW : ∀ h ∈ W, ψ h ∈ M := by
    intro h hh
    rw [MvPolynomial.mem_map_C_iff]
    intro n
    rw [hψcoeff]
    exact (hcrit _ _ (isMultiHomog_comp _ h)).mp (Inter.LocRingPow.component_mem hWh hh _)
  have hψnot : ∀ g ∉ W, ψ g ∉ M := by
    intro g hg hM
    obtain ⟨D, hD⟩ := Inter.LocRingPow.exists_component_not_mem hg
    rw [MvPolynomial.mem_map_C_iff] at hM
    have := hM (Finsupp.equivFunOnFinite.symm D)
    rw [hψcoeff, Finsupp.coe_equivFunOnFinite_symm] at this
    exact hD ((hcrit _ _ (isMultiHomog_comp D g)).mpr this)
  have hψP : ∀ f, ψ f = 0 ↔ f ∈ mCoordIdeal y := by
    intro f
    constructor
    · intro h0
      by_contra hf
      obtain ⟨D, hD⟩ := Inter.LocRingPow.exists_component_not_mem hf
      have h1 := congrArg (fun q => MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm D) q) h0
      simp only [MvPolynomial.coeff_zero] at h1
      rw [hψcoeff, Finsupp.coe_equivFunOnFinite_symm] at h1
      have h2 := congrArg φ h1
      rw [hφev _ _ (isMultiHomog_comp D f), map_zero, div_eq_zero_iff] at h2
      exact hD (LowerBoundFree.mem_mCoordIdeal_of_aeval_eq_zero y (isMultiHomog_comp D f)
        (h2.resolve_right (hycp D)))
    · intro hf
      ext n
      rw [hψcoeff, MvPolynomial.coeff_zero]
      apply hφ
      rw [hφev _ _ (isMultiHomog_comp _ f),
        hformP _ _ (isMultiHomog_comp _ f) (Inter.LocRingPow.component_mem hPh hf _), zero_div, map_zero]

  have hunit : ∀ g : W.primeCompl,
      IsUnit ((algebraMap (MvPolynomial K Bm) N).comp ψ.toRingHom g) := fun g =>
    IsLocalization.map_units N (⟨ψ g, hψnot g g.2⟩ : M.primeCompl)
  let Φ : Localization.AtPrime W →+* N := IsLocalization.lift hunit
  have hΦ : ∀ f, Φ (algebraMap _ _ f) = algebraMap (MvPolynomial K Bm) N (ψ f) := fun f =>
    IsLocalization.lift_eq hunit f
  have hΦmk : ∀ (f : MRing ι) (g : W.primeCompl) (v : N),
      Φ (IsLocalization.mk' _ f g) = v ↔ algebraMap (MvPolynomial K Bm) N (ψ f) =
        algebraMap (MvPolynomial K Bm) N (ψ g) * v := fun f g v =>
    IsLocalization.lift_mk'_spec hunit f v g
  have hinjN : Function.Injective (algebraMap (MvPolynomial K Bm) N) :=
    IsLocalization.injective (R := MvPolynomial K Bm) (M := M.primeCompl) N
      (Ideal.primeCompl_le_nonZeroDivisors M)
  refine ⟨Φ, ?_, ?_, hΦ⟩
  ·
    have hΦmax : ∀ x ∈ IsLocalRing.maximalIdeal (Localization.AtPrime W),
        Φ x ∈ M.map (algebraMap (MvPolynomial K Bm) N) := by
      intro x hx
      rw [← Localization.AtPrime.map_eq_maximalIdeal] at hx
      have hle : (W.map (algebraMap _ (Localization.AtPrime W))).map Φ ≤
          M.map (algebraMap (MvPolynomial K Bm) N) := by
        rw [Ideal.map_map, Ideal.map_le_iff_le_comap]
        intro h hh
        rw [Ideal.mem_comap, RingHom.comp_apply, hΦ]
        exact Ideal.mem_map_of_mem _ (hψW h hh)
      exact hle (Ideal.mem_map_of_mem Φ hx)
    have hloc : ∀ x, IsUnit (Φ x) → IsUnit x := by
      intro x hx
      by_contra hu
      have hmem := hΦmax x ((IsLocalRing.mem_maximalIdeal _).mpr hu)
      rw [Localization.AtPrime.map_eq_maximalIdeal] at hmem
      exact (IsLocalRing.mem_maximalIdeal _).mp hmem hx

    have hpoly : ∀ f : MRing ι, ∃ x, Φ x = algebraMap (MvPolynomial K Bm) N (MvPolynomial.C (aeval r f)) := by
      intro f
      induction f using MvPolynomial.induction_on' with
      | monomial u a0 =>
        have hu : IsMultiHomog (monomial u a0 : MRing ι) (fun k => ∑ i, u ⟨k, i⟩) := by
          intro n hn k
          have := Finset.mem_singleton.mp (support_monomial_subset hn)
          subst this
          rfl
        have hXc : (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ (∑ i, u ⟨k, i⟩)) ∈ W.primeCompl :=
          Submonoid.prod_mem _ fun k _ => Submonoid.pow_mem _ (show X ⟨k, c k⟩ ∈ W.primeCompl from hc k) _
        have hψXc : ψ (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ (∑ i, u ⟨k, i⟩)) =
            ∏ k, (MvPolynomial.X k : MvPolynomial K Bm) ^ (∑ i, u ⟨k, i⟩) := by
          simp only [map_prod, map_pow, hψX]
        refine ⟨IsLocalization.mk' (Localization.AtPrime W) (monomial u a0) (⟨_, hXc⟩ : W.primeCompl),
          (hΦmk _ _ _).mpr ?_⟩
        rw [← map_mul]
        congr 1
        show ψ (monomial u a0) = ψ (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ (∑ i, u ⟨k, i⟩)) * _
        rw [hψform _ _ hu, hψXc, mul_comm]
      | add p q hp hq =>
        obtain ⟨x, hx⟩ := hp
        obtain ⟨x', hx'⟩ := hq
        exact ⟨x + x', by rw [map_add, hx, hx', map_add, map_add, map_add]⟩

    have hC : ∀ q : Bm, ∃ x, Φ x = algebraMap (MvPolynomial K Bm) N (MvPolynomial.C q) := by
      intro q
      obtain ⟨⟨β, γ⟩, hq⟩ := IsLocalization.mk'_surjective m.primeCompl q
      change IsLocalization.mk' Bm β γ = q at hq
      subst hq
      have hB : ∀ β : curveRing y, ∃ f : MRing ι, aeval r f = algebraMap _ Bm β := by
        intro β
        have hβ := mem_curveRing.mp β.2 c hyc
        rw [chartRingZ, Algebra.adjoin_range_eq_range_aeval] at hβ
        obtain ⟨f, hf⟩ := hβ
        exact ⟨f, hφ (by rw [hφaeval, hφalg]; exact hf)⟩
      obtain ⟨f1, e1⟩ := hB β
      obtain ⟨f2, e2⟩ := hB γ
      obtain ⟨x1, h1⟩ := hpoly f1
      obtain ⟨x2, h2⟩ := hpoly f2
      obtain ⟨u, rfl⟩ := hloc x2 (by
        rw [h2, e2]
        exact ((IsLocalization.map_units Bm γ).map MvPolynomial.C).map (algebraMap _ N))
      have hβγ : algebraMap (MvPolynomial K Bm) N (MvPolynomial.C (algebraMap _ Bm β)) =
          algebraMap (MvPolynomial K Bm) N (MvPolynomial.C (IsLocalization.mk' Bm β γ)) * Φ ↑u := by
        rw [h2, e2, ← map_mul, ← map_mul, IsLocalization.mk'_spec]
      refine ⟨x1 * ↑u⁻¹, ?_⟩
      rw [map_mul, h1, e1, hβγ, mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one]
    have hIm : ∀ q : MvPolynomial K Bm, ∃ x, Φ x = algebraMap (MvPolynomial K Bm) N q := by
      intro q
      refine MvPolynomial.induction_on (motive := fun q => ∃ x, Φ x = algebraMap (MvPolynomial K Bm) N q) q hC
        (fun p q hp hq => ?_) (fun p k hp => ?_)
      · obtain ⟨x, hx⟩ := hp
        obtain ⟨x', hx'⟩ := hq
        exact ⟨x + x', by rw [map_add, hx, hx', map_add]⟩
      · obtain ⟨x, hx⟩ := hp
        refine ⟨x * algebraMap (MRing ι) (Localization.AtPrime W) (X ⟨k, c k⟩ : MRing ι), ?_⟩
        rw [map_mul, hx, hΦ, hψX, map_mul]
    intro z
    obtain ⟨⟨q, q'⟩, hz⟩ := IsLocalization.mk'_surjective M.primeCompl z
    change IsLocalization.mk' N q q' = z at hz
    subst hz
    obtain ⟨x1, h1⟩ := hIm q
    obtain ⟨x2, h2⟩ := hIm q'
    obtain ⟨u, rfl⟩ := hloc x2 (by rw [h2]; exact IsLocalization.map_units N q')
    refine ⟨x1 * ↑u⁻¹, ?_⟩
    rw [IsLocalization.eq_mk'_iff_mul_eq, ← h1, ← h2, ← map_mul, mul_assoc, Units.inv_mul, mul_one]
  ·
    ext x
    rw [RingHom.mem_ker]
    constructor
    · intro hx
      obtain ⟨⟨f, g⟩, rfl⟩ := IsLocalization.mk'_surjective W.primeCompl x
      have h1 := (hΦmk f g 0).mp hx
      rw [mul_zero, ← map_zero (algebraMap (MvPolynomial K Bm) N)] at h1
      have hf : f ∈ mCoordIdeal y := (hψP f).mp (hinjN h1)
      change IsLocalization.mk' (Localization.AtPrime W) f g ∈ _
      rw [IsLocalization.mk'_eq_mul_mk'_one]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hf)
    · intro hx
      have hle : (mCoordIdeal y).map (algebraMap _ (Localization.AtPrime W)) ≤ RingHom.ker Φ := by
        rw [Ideal.map_le_iff_le_comap]
        intro f hf
        rw [Ideal.mem_comap, RingHom.mem_ker, hΦ, (hψP f).mpr hf, map_zero]
      exact hle hx

end

end GroundTheory.Heights₂.Heights.Targets
