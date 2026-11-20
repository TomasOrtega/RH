import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveVertIndexSteps
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveClosedPointChart
import GroundTheory.HeightsAndTheta.Heights.Intersections.NotIsUnitOfNumMem
import GroundTheory.HeightsAndTheta.Heights.Intersections.AvoidRing
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.MemMCoordIdealOfAevalEqZero
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.PCurveDivVertical
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Inter.AvoidRing

noncomputable section

namespace CurveVerticalPointResidue

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [Fintype K] in

/- English proof (translation)
Introduce `m hm k`. Break down `Finset.mem_union.mp (MvPolynomial.support_sub _ f g hm) with h | h` into its components or cases. Conclude with `hf m h k`. Conclude with `hg m h k`.
-/
theorem isMultiHomog_sub' {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f - g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (MvPolynomial.support_sub _ f g hm) with h | h
  · exact hf m h k
  · exact hg m h k

omit [Fintype K] in

/- English proof (translation)
Introduce `m hm k`. Break down `Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h` into its components or cases. Conclude with `hf m h k`. Conclude with `hg m h k`.
-/
theorem isMultiHomog_add' {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f + g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
  · exact hf m h k
  · exact hg m h k

omit [Fintype K] in

/- English proof (translation)
Introduce `m hm k`. Establish `hm' : m ∈ (monomial (0 : (Σ k, ι k) →₀ ℕ) a).support` using `hm`. Use `MvPolynomial.support_monomial_subset hm'` as an intermediate fact. Rewrite `this` using `[Finset.mem_singleton]`. Substitute `this` using the available equality.

Simplify using the standard rewrite rules.
-/
theorem isMultiHomog_C' (a : ℤ) : IsMultiHomog (C a : MRing ι) 0 := by
  classical
  intro m hm k
  have hm' : m ∈ (monomial (0 : (Σ k, ι k) →₀ ℕ) a).support := hm
  have := MvPolynomial.support_monomial_subset hm'
  rw [Finset.mem_singleton] at this
  subst this
  simp

/- English proof (translation)
Establish `hχp : ∀ n : K → ℕ, χ (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ n k) = 1` using `fun n => by`. Simplify using `[map_prod, hχ]`. Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a => exact ⟨0, C a, isMultiHomog_C' a, rfl⟩`. Consider the case `add p q hp hq`.

Take `⟨n₁, G₁, h₁, e₁⟩` from `hp`. Take `⟨n₂, G₂, h₂, e₂⟩` from `hq`. Use `⟨n₁ + n₂, G₁ * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ n₂ k + G₂ * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ n₁ k, isMultiHomog_add' (isMultiHomog_mul h₁ (isMultiHomog_coordProd c n₂)) ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[add_comm n₁]`. Conclude with `isMultiHomog_mul h₂ (isMultiHomog_coordProd c n₁)`.

Rewrite using `[map_add, map_mul, map_mul, hχp, hχp, mul_one, mul_one, e₁, e₂, map_add]`. Consider the case `mul_X p i hp`. Take `⟨n, G, h, e⟩` from `hp`. Conclude with `⟨n + Pi.single i.1 1, G * X i, isMultiHomog_mul h (isMultiHomog_X i.1 i.2), by`. Rewrite using `[map_mul, map_mul, e]⟩`.
-/
theorem exists_homog {S : Type*} [CommRing S] (χ : MRing ι →+* S) (c : ∀ k, ι k)
    (hχ : ∀ k, χ (X ⟨k, c k⟩) = 1) (f : MRing ι) :
    ∃ (n : K → ℕ) (G : MRing ι), IsMultiHomog G n ∧ χ G = χ f := by
  classical
  have hχp : ∀ n : K → ℕ, χ (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ n k) = 1 := fun n => by
    simp [map_prod, hχ]
  induction f using MvPolynomial.induction_on with
  | C a => exact ⟨0, C a, isMultiHomog_C' a, rfl⟩
  | add p q hp hq =>
    obtain ⟨n₁, G₁, h₁, e₁⟩ := hp
    obtain ⟨n₂, G₂, h₂, e₂⟩ := hq
    refine ⟨n₁ + n₂, G₁ * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ n₂ k + G₂ * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ n₁ k,
      isMultiHomog_add' (isMultiHomog_mul h₁ (isMultiHomog_coordProd c n₂)) ?_, ?_⟩
    · rw [add_comm n₁]
      exact isMultiHomog_mul h₂ (isMultiHomog_coordProd c n₁)
    · rw [map_add, map_mul, map_mul, hχp, hχp, mul_one, mul_one, e₁, e₂, map_add]
  | mul_X p i hp =>
    obtain ⟨n, G, h, e⟩ := hp
    exact ⟨n + Pi.single i.1 1, G * X i, isMultiHomog_mul h (isMultiHomog_X i.1 i.2), by
      rw [map_mul, map_mul, e]⟩

/- English proof (translation)
Establish `hχp : ∀ n : K → ℕ, χ (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ n k) = 1` using `fun n => by`. Simplify using `[map_prod, hχ]`. Take `⟨Sg, hSg, rfl⟩` from `hW`. Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨a, ha⟩` from `hSg x hx`. Conclude with `⟨a, x, Ideal.subset_span hx, ha, rfl⟩`. Consider the case `zero => exact ⟨0, 0, zero_mem _, fun m hm => absurd hm (by simp), rfl⟩`. Consider the case `add x z _ _ hx hz`. Take `⟨n₁, G₁, hG₁, h₁, e₁⟩` from `hx`.

Take `⟨n₂, G₂, hG₂, h₂, e₂⟩` from `hz`. Use `⟨n₁ + n₂, G₁ * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ n₂ k + G₂ * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ n₁ k, add_mem (Ideal.mul_mem_right _ _ hG₁) (Ideal.mul_mem_right _ _ hG₂), isMultiHomog_add' (isMultiHomog_mul h₁ (isMultiHomog_coordProd c n₂)) ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[add_comm n₁]`. Conclude with `isMultiHomog_mul h₂ (isMultiHomog_coordProd c n₁)`. Rewrite using `[map_add, map_mul, map_mul, hχp, hχp, mul_one, mul_one, e₁, e₂, map_add]`.

Consider the case `smul a x _ hx`. Take `⟨n, G, hG, h, e⟩` from `hx`. Take `⟨m, A, hA, eA⟩` from `exists_homog χ c hχ a`. Use `⟨m + n, A * G, Ideal.mul_mem_left _ _ hG, isMultiHomog_mul hA h, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_eq_mul, map_mul, map_mul, eA, e]`.
-/
theorem exists_homog_mem {S : Type*} [CommRing S] (χ : MRing ι →+* S) (c : ∀ k, ι k)
    (hχ : ∀ k, χ (X ⟨k, c k⟩) = 1) {W : Ideal (MRing ι)} (hW : IsMultiHomogIdeal W)
    {f : MRing ι} (hf : f ∈ W) :
    ∃ (n : K → ℕ) (G : MRing ι), G ∈ W ∧ IsMultiHomog G n ∧ χ G = χ f := by
  classical
  have hχp : ∀ n : K → ℕ, χ (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ n k) = 1 := fun n => by
    simp [map_prod, hχ]
  obtain ⟨Sg, hSg, rfl⟩ := hW
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha⟩ := hSg x hx
    exact ⟨a, x, Ideal.subset_span hx, ha, rfl⟩
  | zero => exact ⟨0, 0, zero_mem _, fun m hm => absurd hm (by simp), rfl⟩
  | add x z _ _ hx hz =>
    obtain ⟨n₁, G₁, hG₁, h₁, e₁⟩ := hx
    obtain ⟨n₂, G₂, hG₂, h₂, e₂⟩ := hz
    refine ⟨n₁ + n₂, G₁ * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ n₂ k + G₂ * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ n₁ k,
      add_mem (Ideal.mul_mem_right _ _ hG₁) (Ideal.mul_mem_right _ _ hG₂),
      isMultiHomog_add' (isMultiHomog_mul h₁ (isMultiHomog_coordProd c n₂)) ?_, ?_⟩
    · rw [add_comm n₁]
      exact isMultiHomog_mul h₂ (isMultiHomog_coordProd c n₁)
    · rw [map_add, map_mul, map_mul, hχp, hχp, mul_one, mul_one, e₁, e₂, map_add]
  | smul a x _ hx =>
    obtain ⟨n, G, hG, h, e⟩ := hx
    obtain ⟨m, A, hA, eA⟩ := exists_homog χ c hχ a
    refine ⟨m + n, A * G, Ideal.mul_mem_left _ _ hG, isMultiHomog_mul hA h, ?_⟩
    rw [smul_eq_mul, map_mul, map_mul, eA, e]

/- English proof (translation)
Rewrite using `[aeval_def, aeval_def, eval₂_eq, eval₂_eq, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations. Rewrite using `[mul_assoc]`. Use `congr 1`. Rewrite using `[Finset.prod_subset (Finset.subset_univ m.support) (fun p _ hp => by`.

Rewrite using `[Finsupp.notMem_support_iff.mp hp, pow_zero]),`. Use the proof step `Finset.prod_subset (Finset.subset_univ m.support) (fun p _ hp => by`. Rewrite using `[Finsupp.notMem_support_iff.mp hp, pow_zero])]`. Establish `hden : ∏ p : (Σ k, ι k), y ⟨p.1, c p.1⟩ ^ m p = ∏ k, y ⟨k, c k⟩ ^ n k`. Rewrite using `[Fintype.prod_sigma]`.

Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Use `show ∏ i, y ⟨k, c k⟩ ^ m ⟨k, i⟩ = _`. Rewrite using `[Finset.prod_pow_eq_pow_sum, hG m hm k]`. Repeatedly rewrite using `[div_pow]`. Rewrite using `[Finset.prod_div_distrib, hden, div_eq_mul_inv]`.
-/
theorem aeval_div {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k)
    (G : MRing ι) (n : K → ℕ) (hG : IsMultiHomog G n) :
    aeval (fun p => y p / y ⟨p.1, c p.1⟩) G = aeval y G * (∏ k, y ⟨k, c k⟩ ^ n k)⁻¹ := by
  classical
  rw [aeval_def, aeval_def, eval₂_eq, eval₂_eq, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [mul_assoc]
  congr 1
  rw [Finset.prod_subset (Finset.subset_univ m.support) (fun p _ hp => by
      rw [Finsupp.notMem_support_iff.mp hp, pow_zero]),
    Finset.prod_subset (Finset.subset_univ m.support) (fun p _ hp => by
      rw [Finsupp.notMem_support_iff.mp hp, pow_zero])]
  have hden : ∏ p : (Σ k, ι k), y ⟨p.1, c p.1⟩ ^ m p = ∏ k, y ⟨k, c k⟩ ^ n k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, y ⟨k, c k⟩ ^ m ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hG m hm k]
  simp_rw [div_pow]
  rw [Finset.prod_div_distrib, hden, div_eq_mul_inv]

end CurveVerticalPointResidue

open CurveVerticalPointResidue in

/- English proof (translation)
Introduce `K _ ι _ Ω _ y s d hP hs hsP W hW`. Take `⟨-, ⟨hPp, hPh, -⟩, -, hPdim⟩` from `id hP`. Take `⟨hWmin, hWrel⟩` from `hW`. Establish `hWp : W.IsPrime` using `hWmin.1.1`. Use `hWp` as an intermediate fact.

Use `hPp` as an intermediate fact. Establish `hPW : mCoordIdeal y ≤ W` using `le_sup_left.trans hWmin.1.2`. Establish `hWmh : IsMultiHomogIdeal W` using `isMultiHomogIdeal_of_mem_minimalPrimes hPh hs hWmin`. Establish `hdim : ringKrullDim (MRing ι ⧸ W) = ((0 + Fintype.card K : ℕ) : WithBot ℕ∞)`. Establish `h1` using `dim_quot_minimal_add_one (mCoordIdeal y) W s hsP hWmin`.

Rewrite `h1` using `[hPdim]`. Conclude with `withBot_eq_of_add_one (by rw [h1, show 1 + Fintype.card K = 0 + Fintype.card K + 1 by omega])`. Establish `hvert : ¬ IsHorizontal W` using `IndefiniteRowSideFullHecke.HeightsSet.CurveDivVertical.full K ι _ s d hP hs hsP W ⟨hWmin, hWrel⟩`. Establish `: Fact (charOf W).Prime` using `⟨charOf_prime hWp hvert⟩`. Establish `hp : (C ((charOf W : ℕ) : ℤ) : MRing ι) ∈ W`.

Establish `hgen` using `Submodule.IsPrincipal.generator_mem (W.comap (C : ℤ →+* MRing ι))`. Establish `: ((charOf W : ℕ) : ℤ) ∈ W.comap (C : ℤ →+* MRing ι)`. Unfold `charOf`. Rewrite using `[Int.natCast_natAbs]`. Apply the tactic sequence `rcases abs_choice (Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing ι))) with h | h <;> rw [h]`.

Conclude with `hgen`. Conclude with `neg_mem hgen`. Conclude with `Ideal.mem_comap.mp this`. Use `set c : ∀ k, ι k := fun k => (hWrel k).choose with hc`. Establish `hcW : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ W` using `fun k => (hWrel k).choose_spec`.

Use `set I0 := Ideal.span (Set.range fun k => (X ⟨k, c k⟩ : MRing ι) - 1) with hI0`. Use `set J := W ⊔ I0 with hJ`. Establish `hgeo : ∀ b, geoNum 0 W b = ((Module.length ℤ (MRing ι ⧸ J)).toNat : ℤ)`. Introduce `b`. Rewrite using `[geoNum, dif_pos hWrel]`.

Take `⟨hF, hFin, hcard⟩` from `Inter.regularityLocalResidue_holds.chart_field_card hWmh hcW hdim (charOf W) hp`. Use `letI : Field (MRing ι ⧸ J) := hF.toField`. Establish `hyc : ∀ k, y ⟨k, c k⟩ ≠ 0` using `fun k => ne_zero_of_X_notMem fun h => hcW k (hPW h)`. Establish `hD : ∀ n : K → ℕ, (∏ k, y ⟨k, c k⟩ ^ n k) ≠ 0` using `fun n => Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hyc k)`. Establish `haevalD : ∀ n : K → ℕ, aeval y (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ n k) = ∏ k, y ⟨k, c k⟩ ^ n k`.

Introduce `n`. Simplify using `[map_prod]`. Set `φ : MRing ι →+* Ω` to `(aeval fun p => y p / y ⟨p.1, c p.1⟩).toRingHom`. Establish `hφX : ∀ p, φ (X p) = y p / y ⟨p.1, c p.1⟩` using `fun p => aeval_X _ _`. Establish `hφc : ∀ k, φ (X ⟨k, c k⟩) = 1` using `fun k => by rw [hφX, div_self (hyc k)]`.

Establish `hφform : ∀ G n, IsMultiHomog G n → φ G = aeval y G * (∏ k, y ⟨k, c k⟩ ^ n k)⁻¹` using `fun G n hG => aeval_div y c G n hG`. Establish `hspan : I0 ≤ RingHom.ker φ`. Use `Ideal.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨k, rfl⟩`. Rewrite using `[SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one, hφc, sub_self]`.

Establish `hker : RingHom.ker φ ≤ J`. Introduce `f hf`. Rewrite `hf` using `[RingHom.mem_ker]`. Establish `hχ : ∀ k, Ideal.Quotient.mk I0 (X ⟨k, c k⟩) = 1` using `fun k => by`. Rewrite using `[← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq]`.

Conclude with `Ideal.subset_span ⟨k, rfl⟩`. Take `⟨n, G, hG, hGf⟩` from `exists_homog _ c hχ f`. Establish `hd : G - f ∈ I0` using `Ideal.Quotient.eq.mp hGf`. Establish `hG0 : aeval y G = 0`. Establish `h` using `hspan hd`.

Rewrite `h` using `[RingHom.mem_ker, map_sub, hf, sub_zero, hφform G n hG]`. Conclude with `(mul_eq_zero.mp h).resolve_right (inv_ne_zero (hD n))`. Establish `hGJ : G ∈ J` using `Ideal.mem_sup_left (hPW (LowerBoundFree.mem_mCoordIdeal_of_aeval_eq_zero y hG hG0))`. Simplify using `using sub_mem hGJ (Ideal.mem_sup_right hd : G - f ∈ J)`. Establish `hB : ∀ b : curveRing y, ∃ f, φ f = b`.

Introduce `b`. Establish `hb` using `mem_curveRing.mp b.2 c hyc`. Rewrite `hb` using `[chartRingZ, Algebra.adjoin_range_eq_range_aeval]`. Take `⟨f, hf⟩` from `(AlgHom.mem_range _).mp hb`. Conclude with `⟨f, hf⟩`.

Establish `hBr : ∀ b : curveRing y, (curveRing y).subtype b ∈ φ.range` using `fun b => hB b`. Set `e` to `RingHom.quotientKerEquivRange φ`. Set `ψ : φ.range →+* (MRing ι ⧸ J)` to `(Ideal.Quotient.factor hker).comp e.symm.toRingHom`. Establish `hψ : ∀ f (h : φ f ∈ φ.range), ψ ⟨φ f, h⟩ = Ideal.Quotient.mk J f`. Introduce `f h`.

Establish `h' : e.symm ⟨φ f, h⟩ = Ideal.Quotient.mk (RingHom.ker φ) f`. Rewrite using `[RingEquiv.symm_apply_eq]`. Both sides reduce to the same expression. Use `show Ideal.Quotient.factor hker (e.symm ⟨φ f, h⟩) = _`. Rewrite using `[h', Ideal.Quotient.factor_mk]`.

Set `incl : curveRing y →+* φ.range` to `(curveRing y).subtype.codRestrict φ.range hBr`. Set `Θ : curveRing y →+* (MRing ι ⧸ J)` to `ψ.comp incl`. Establish `hΘ : ∀ (b : curveRing y) f, φ f = b → Θ b = Ideal.Quotient.mk J f`. Introduce `b f hf`. Establish `h' : incl b = ⟨φ f, RingHom.mem_range_self φ f⟩` using `Subtype.ext hf.symm`.

Use `show ψ (incl b) = _`. Rewrite using `[h']`. Conclude with `hψ f _`. Establish `hΘmul : ∀ (b₁ b₂ : curveRing y) g, (b₁ : Ω) * φ g = b₂ → Θ b₁ * Ideal.Quotient.mk J g = Θ b₂`. Introduce `b₁ b₂ g h`.

Take `⟨f, hf⟩` from `hB b₁`. Rewrite using `[hΘ b₁ f hf, hΘ b₂ (f * g) (by rw [map_mul, hf, h]), map_mul]`. Establish `: Finite (MRing ι ⧸ J)` using `hFin`. Establish `hFF : IsField Θ.range` using `Finite.isDomain_to_isField _`. Establish `hmax : (RingHom.ker Θ).IsMaximal` using `Ideal.Quotient.maximal_of_isField _ (MulEquiv.isField hFF (RingHom.quotientKerEquivRange Θ).toMulEquiv)`.

Take `⟨t, hyt, hrat⟩` from `hC K ι Ω y hP (RingHom.ker Θ) hmax`. Establish `hgen : ∀ u : Σ k, ι k, Ideal.Quotient.mk J (X u) ∈ Θ.range`. Introduce and unpack `⟨k, u⟩`. Take `⟨ac, bc, hbc, hc'⟩` from `hrat ⟨k, c k⟩`. Take `⟨au, bu, hbu, hu'⟩` from `hrat ⟨k, u⟩`.

Simplify using `only at hc' hu'`. Establish `hyk` using `hyc k`. Establish `hytk` using `hyt k`. Establish `hac : Θ ac ≠ 0`. Introduce `h0`.

Apply `hbc` to reduce the goal to its premises. Rewrite using `[RingHom.mem_ker, ← hΘmul ac bc (X ⟨k, t k⟩) ?_, h0, zero_mul]`. Rewrite using `[hφX, ← hc']`. Clear the denominators using the available nonvanishing facts. Establish `hbu' : Θ bu ≠ 0` using `fun h0 => hbu (RingHom.mem_ker.mpr h0)`.

Establish `key : Θ (bu * ac) * Ideal.Quotient.mk J (X ⟨k, u⟩) = Θ (au * bc)`. Use `hΘmul _ _ _ ?_` and prove the remaining obligations. Use `push_cast`. Rewrite using `[hφX, ← hu', ← hc']`. Clear the denominators using the available nonvanishing facts.

Establish `hx : Θ (bu * ac) ≠ 0`. Rewrite using `[map_mul]`. Conclude with `mul_ne_zero hbu' hac`. Take `⟨w, hw⟩` from `hFF.mul_inv_cancel (a := ⟨Θ (bu * ac), bu * ac, rfl⟩) (fun h => hx (congrArg Subtype.val h))`. Establish `hw' : Θ (bu * ac) * (w : MRing ι ⧸ J) = 1` using `congrArg Subtype.val hw`.

Establish `h2 : Ideal.Quotient.mk J (X ⟨k, u⟩) = Θ (au * bc) * w`. Rewrite using `[← key, mul_comm (Θ (bu * ac)), mul_assoc, hw', mul_one]`. Rewrite using `[h2]`. Conclude with `mul_mem ⟨au * bc, rfl⟩ w.2`. Establish `hsurj : Function.Surjective Θ`.

Introduce `z`. Take `⟨f, rfl⟩` from `Ideal.Quotient.mk_surjective z`. It suffices to establish `h : Ideal.Quotient.mk J f ∈ Θ.range from h`. Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a`.

Rewrite using `[show Ideal.Quotient.mk J (C a) = (a : MRing ι ⧸ J) from eq_intCast ((Ideal.Quotient.mk J).comp C) a]`. Conclude with `intCast_mem _ a`. Consider the case `add p q hp hq`. Rewrite using `[map_add]`. Conclude with `add_mem hp hq`.

Consider the case `mul_X p i hp`. Rewrite using `[map_mul]`. Conclude with `mul_mem hp (hgen i)`. Establish `hkerΘ : RingHom.ker Θ = curvePtIdeal y W`. Apply `le_antisymm` to reduce the goal to its premises.

Introduce `b hb`. Rewrite `hb` using `[RingHom.mem_ker]`. Take `⟨f, hf⟩` from `hB b`. Rewrite `hb` using `[hΘ b f hf, Ideal.Quotient.eq_zero_iff_mem]`. Take `⟨w, hw, z, hz, rfl⟩` from `Submodule.mem_sup.mp hb`.

Take `⟨n, G, hGW, hG, hφG⟩` from `exists_homog_mem φ c hφc hWmh hw`. Establish `h1 : (b : Ω) = aeval y G * (∏ k, y ⟨k, c k⟩ ^ n k)⁻¹`. Rewrite using `[← hφform G n hG, hφG, ← hf, map_add, hspan hz, add_zero]`. Use `Ideal.subset_span ⟨n, G, ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ n k, hG, isMultiHomog_coordProd c n, hGW, coordProd_not_mem hWp c hcW n, ?_⟩` and prove the remaining obligations. Rewrite using `[h1, haevalD, mul_assoc, inv_mul_cancel₀ (hD n), mul_one]`.

Use `Ideal.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `b ⟨n, g, h, hg, hh, hgW, hhW, hbgh⟩`. Rewrite using `[SetLike.mem_coe, RingHom.mem_ker]`. Take `⟨f, hf⟩` from `hB b`. Establish `hid : (b : Ω) * φ h = φ g`.

Rewrite using `[hφform h _ hh, hφform g _ hg, ← mul_assoc, hbgh]`. Rewrite using `[hΘ b f hf]`. Establish `h1 : Ideal.Quotient.mk J f * Ideal.Quotient.mk J h = 0`. Rewrite using `[← map_mul, Ideal.Quotient.eq_zero_iff_mem]`. Establish `h3 : f * h - g ∈ J` using `hker (by rw [RingHom.mem_ker, map_sub, map_mul, hf, hid, sub_self])`.

Simplify using `using add_mem h3 (Ideal.mem_sup_left hgW : g ∈ J)`. Establish `h2 : Ideal.Quotient.mk J h ≠ 0`. Rewrite using `[Ne, Ideal.Quotient.eq_zero_iff_mem]`. Introduce `hJh`. Take `⟨w, hw, z, hz, hwz⟩` from `Submodule.mem_sup.mp hJh`.

Take `⟨n', G, hGW, hG, hφG⟩` from `exists_homog_mem φ c hφc hWmh hw`. Establish `e1 : φ G = φ h` using `by rw [hφG, ← hwz, map_add, hspan hz, add_zero]`. Establish `hmem : G * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ n k - h * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ n' k ∈ mCoordIdeal y`. Use `LowerBoundFree.mem_mCoordIdeal_of_aeval_eq_zero y (d := n' + n) (isMultiHomog_sub' (isMultiHomog_mul hG (isMultiHomog_coordProd c n)) ?_) ?_` and prove the remaining obligations. Rewrite using `[add_comm n']`.

Conclude with `isMultiHomog_mul hh (isMultiHomog_coordProd c n')`. Rewrite `e1` using `[hφform G n' hG, hφform h _ hh]`. Rewrite using `[map_sub, map_mul, map_mul, haevalD, haevalD, sub_eq_zero]`. Establish `hn` using `hD n`. Establish `hn'` using `hD n'`.

Clear denominators, using `at e1` for the nonvanishing conditions. Take the linear combination `e1`. Establish `h4 : h * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ n' k ∈ W`. Establish `h5` using `sub_mem (Ideal.mul_mem_right (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ n k) W hGW) (hPW hmem)`. Simplify using `using h5`.

Break down `hWp.mem_or_mem h4 with h3 | h3` into its components or cases. Conclude with `hhW h3`. Conclude with `coordProd_not_mem hWp c hcW n' h3`. Conclude with `(mul_eq_zero.mp h1).resolve_right h2`. Set `eq : (curveRing y ⧸ curvePtIdeal y W) ≃+* (MRing ι ⧸ J)` to `(Ideal.quotEquivOfEq hkerΘ.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)`.

Rewrite using `[Nat.card_congr eq.toEquiv, hcard, hgeo]`. Use `push_cast`. Rewrite using `[Real.log_pow]`.
-/
theorem CurveVertPointResidue.proof (hC : CurveClosedPointChart.Statement) :
    CurveVertPointResidue.Statement := by
  intro K _ ι _ Ω _ y s d hP hs hsP W hW
  classical
  obtain ⟨-, ⟨hPp, hPh, -⟩, -, hPdim⟩ := id hP
  obtain ⟨hWmin, hWrel⟩ := hW
  have hWp : W.IsPrime := hWmin.1.1
  have := hWp
  have := hPp
  have hPW : mCoordIdeal y ≤ W := le_sup_left.trans hWmin.1.2
  have hWmh : IsMultiHomogIdeal W := isMultiHomogIdeal_of_mem_minimalPrimes hPh hs hWmin
  have hdim : ringKrullDim (MRing ι ⧸ W) = ((0 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    have h1 := dim_quot_minimal_add_one (mCoordIdeal y) W s hsP hWmin
    rw [hPdim] at h1
    exact withBot_eq_of_add_one
      (by rw [h1, show 1 + Fintype.card K = 0 + Fintype.card K + 1 by omega])
  have hvert : ¬ IsHorizontal W :=
    IndefiniteRowSideFullHecke.HeightsSet.CurveDivVertical.full K ι _ s d hP hs hsP W ⟨hWmin, hWrel⟩
  have : Fact (charOf W).Prime := ⟨charOf_prime hWp hvert⟩
  have hp : (C ((charOf W : ℕ) : ℤ) : MRing ι) ∈ W := by
    have hgen := Submodule.IsPrincipal.generator_mem (W.comap (C : ℤ →+* MRing ι))
    have : ((charOf W : ℕ) : ℤ) ∈ W.comap (C : ℤ →+* MRing ι) := by
      unfold charOf
      rw [Int.natCast_natAbs]
      rcases abs_choice (Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing ι))) with h | h <;> rw [h]
      · exact hgen
      · exact neg_mem hgen
    exact Ideal.mem_comap.mp this
  set c : ∀ k, ι k := fun k => (hWrel k).choose with hc
  have hcW : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ W := fun k => (hWrel k).choose_spec
  set I0 := Ideal.span (Set.range fun k => (X ⟨k, c k⟩ : MRing ι) - 1) with hI0
  set J := W ⊔ I0 with hJ
  have hgeo : ∀ b, geoNum 0 W b = ((Module.length ℤ (MRing ι ⧸ J)).toNat : ℤ) := by
    intro b
    rw [geoNum, dif_pos hWrel]
  obtain ⟨hF, hFin, hcard⟩ := Inter.regularityLocalResidue_holds.chart_field_card hWmh hcW hdim (charOf W) hp
  letI : Field (MRing ι ⧸ J) := hF.toField
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => ne_zero_of_X_notMem fun h => hcW k (hPW h)
  have hD : ∀ n : K → ℕ, (∏ k, y ⟨k, c k⟩ ^ n k) ≠ 0 := fun n =>
    Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hyc k)
  have haevalD : ∀ n : K → ℕ, aeval y (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ n k) = ∏ k, y ⟨k, c k⟩ ^ n k := by
    intro n
    simp [map_prod]

  let φ : MRing ι →+* Ω := (aeval fun p => y p / y ⟨p.1, c p.1⟩).toRingHom
  have hφX : ∀ p, φ (X p) = y p / y ⟨p.1, c p.1⟩ := fun p => aeval_X _ _
  have hφc : ∀ k, φ (X ⟨k, c k⟩) = 1 := fun k => by rw [hφX, div_self (hyc k)]
  have hφform : ∀ G n, IsMultiHomog G n → φ G = aeval y G * (∏ k, y ⟨k, c k⟩ ^ n k)⁻¹ :=
    fun G n hG => aeval_div y c G n hG
  have hspan : I0 ≤ RingHom.ker φ := by
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one, hφc, sub_self]
  have hker : RingHom.ker φ ≤ J := by
    intro f hf
    rw [RingHom.mem_ker] at hf
    have hχ : ∀ k, Ideal.Quotient.mk I0 (X ⟨k, c k⟩) = 1 := fun k => by
      rw [← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq]
      exact Ideal.subset_span ⟨k, rfl⟩
    obtain ⟨n, G, hG, hGf⟩ := exists_homog _ c hχ f
    have hd : G - f ∈ I0 := Ideal.Quotient.eq.mp hGf
    have hG0 : aeval y G = 0 := by
      have h := hspan hd
      rw [RingHom.mem_ker, map_sub, hf, sub_zero, hφform G n hG] at h
      exact (mul_eq_zero.mp h).resolve_right (inv_ne_zero (hD n))
    have hGJ : G ∈ J := Ideal.mem_sup_left (hPW (LowerBoundFree.mem_mCoordIdeal_of_aeval_eq_zero y hG hG0))
    simpa using sub_mem hGJ (Ideal.mem_sup_right hd : G - f ∈ J)

  have hB : ∀ b : curveRing y, ∃ f, φ f = b := by
    intro b
    have hb := mem_curveRing.mp b.2 c hyc
    rw [chartRingZ, Algebra.adjoin_range_eq_range_aeval] at hb
    obtain ⟨f, hf⟩ := (AlgHom.mem_range _).mp hb
    exact ⟨f, hf⟩
  have hBr : ∀ b : curveRing y, (curveRing y).subtype b ∈ φ.range := fun b => hB b
  let e := RingHom.quotientKerEquivRange φ
  let ψ : φ.range →+* (MRing ι ⧸ J) := (Ideal.Quotient.factor hker).comp e.symm.toRingHom
  have hψ : ∀ f (h : φ f ∈ φ.range), ψ ⟨φ f, h⟩ = Ideal.Quotient.mk J f := by
    intro f h
    have h' : e.symm ⟨φ f, h⟩ = Ideal.Quotient.mk (RingHom.ker φ) f := by
      rw [RingEquiv.symm_apply_eq]
      rfl
    show Ideal.Quotient.factor hker (e.symm ⟨φ f, h⟩) = _
    rw [h', Ideal.Quotient.factor_mk]
  let incl : curveRing y →+* φ.range := (curveRing y).subtype.codRestrict φ.range hBr
  let Θ : curveRing y →+* (MRing ι ⧸ J) := ψ.comp incl
  have hΘ : ∀ (b : curveRing y) f, φ f = b → Θ b = Ideal.Quotient.mk J f := by
    intro b f hf
    have h' : incl b = ⟨φ f, RingHom.mem_range_self φ f⟩ := Subtype.ext hf.symm
    show ψ (incl b) = _
    rw [h']
    exact hψ f _
  have hΘmul : ∀ (b₁ b₂ : curveRing y) g, (b₁ : Ω) * φ g = b₂ →
      Θ b₁ * Ideal.Quotient.mk J g = Θ b₂ := by
    intro b₁ b₂ g h
    obtain ⟨f, hf⟩ := hB b₁
    rw [hΘ b₁ f hf, hΘ b₂ (f * g) (by rw [map_mul, hf, h]), map_mul]

  have : Finite (MRing ι ⧸ J) := hFin
  have hFF : IsField Θ.range := Finite.isDomain_to_isField _
  have hmax : (RingHom.ker Θ).IsMaximal :=
    Ideal.Quotient.maximal_of_isField _ (MulEquiv.isField hFF (RingHom.quotientKerEquivRange Θ).toMulEquiv)

  obtain ⟨t, hyt, hrat⟩ := hC K ι Ω y hP (RingHom.ker Θ) hmax
  have hgen : ∀ u : Σ k, ι k, Ideal.Quotient.mk J (X u) ∈ Θ.range := by
    rintro ⟨k, u⟩
    obtain ⟨ac, bc, hbc, hc'⟩ := hrat ⟨k, c k⟩
    obtain ⟨au, bu, hbu, hu'⟩ := hrat ⟨k, u⟩
    dsimp only at hc' hu'
    have hyk := hyc k
    have hytk := hyt k
    have hac : Θ ac ≠ 0 := by
      intro h0
      apply hbc
      rw [RingHom.mem_ker, ← hΘmul ac bc (X ⟨k, t k⟩) ?_, h0, zero_mul]
      rw [hφX, ← hc']
      field_simp
    have hbu' : Θ bu ≠ 0 := fun h0 => hbu (RingHom.mem_ker.mpr h0)
    have key : Θ (bu * ac) * Ideal.Quotient.mk J (X ⟨k, u⟩) = Θ (au * bc) := by
      refine hΘmul _ _ _ ?_
      push_cast
      rw [hφX, ← hu', ← hc']
      field_simp
    have hx : Θ (bu * ac) ≠ 0 := by
      rw [map_mul]
      exact mul_ne_zero hbu' hac
    obtain ⟨w, hw⟩ := hFF.mul_inv_cancel (a := ⟨Θ (bu * ac), bu * ac, rfl⟩)
      (fun h => hx (congrArg Subtype.val h))
    have hw' : Θ (bu * ac) * (w : MRing ι ⧸ J) = 1 := congrArg Subtype.val hw
    have h2 : Ideal.Quotient.mk J (X ⟨k, u⟩) = Θ (au * bc) * w := by
      rw [← key, mul_comm (Θ (bu * ac)), mul_assoc, hw', mul_one]
    rw [h2]
    exact mul_mem ⟨au * bc, rfl⟩ w.2
  have hsurj : Function.Surjective Θ := by
    intro z
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective z
    suffices h : Ideal.Quotient.mk J f ∈ Θ.range from h
    induction f using MvPolynomial.induction_on with
    | C a =>
      rw [show Ideal.Quotient.mk J (C a) = (a : MRing ι ⧸ J) from
        eq_intCast ((Ideal.Quotient.mk J).comp C) a]
      exact intCast_mem _ a
    | add p q hp hq =>
      rw [map_add]
      exact add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul]
      exact mul_mem hp (hgen i)

  have hkerΘ : RingHom.ker Θ = curvePtIdeal y W := by
    apply le_antisymm
    · intro b hb
      rw [RingHom.mem_ker] at hb
      obtain ⟨f, hf⟩ := hB b
      rw [hΘ b f hf, Ideal.Quotient.eq_zero_iff_mem] at hb
      obtain ⟨w, hw, z, hz, rfl⟩ := Submodule.mem_sup.mp hb
      obtain ⟨n, G, hGW, hG, hφG⟩ := exists_homog_mem φ c hφc hWmh hw
      have h1 : (b : Ω) = aeval y G * (∏ k, y ⟨k, c k⟩ ^ n k)⁻¹ := by
        rw [← hφform G n hG, hφG, ← hf, map_add, hspan hz, add_zero]
      refine Ideal.subset_span ⟨n, G, ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ n k, hG, isMultiHomog_coordProd c n, hGW,
        coordProd_not_mem hWp c hcW n, ?_⟩
      rw [h1, haevalD, mul_assoc, inv_mul_cancel₀ (hD n), mul_one]
    · refine Ideal.span_le.mpr ?_
      rintro b ⟨n, g, h, hg, hh, hgW, hhW, hbgh⟩
      rw [SetLike.mem_coe, RingHom.mem_ker]
      obtain ⟨f, hf⟩ := hB b
      have hid : (b : Ω) * φ h = φ g := by
        rw [hφform h _ hh, hφform g _ hg, ← mul_assoc, hbgh]
      rw [hΘ b f hf]
      have h1 : Ideal.Quotient.mk J f * Ideal.Quotient.mk J h = 0 := by
        rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
        have h3 : f * h - g ∈ J := hker (by rw [RingHom.mem_ker, map_sub, map_mul, hf, hid, sub_self])
        simpa using add_mem h3 (Ideal.mem_sup_left hgW : g ∈ J)
      have h2 : Ideal.Quotient.mk J h ≠ 0 := by
        rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
        intro hJh
        obtain ⟨w, hw, z, hz, hwz⟩ := Submodule.mem_sup.mp hJh
        obtain ⟨n', G, hGW, hG, hφG⟩ := exists_homog_mem φ c hφc hWmh hw
        have e1 : φ G = φ h := by rw [hφG, ← hwz, map_add, hspan hz, add_zero]
        have hmem : G * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ n k - h * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ n' k ∈
            mCoordIdeal y := by
          refine LowerBoundFree.mem_mCoordIdeal_of_aeval_eq_zero y (d := n' + n)
            (isMultiHomog_sub' (isMultiHomog_mul hG (isMultiHomog_coordProd c n)) ?_) ?_
          · rw [add_comm n']
            exact isMultiHomog_mul hh (isMultiHomog_coordProd c n')
          · rw [hφform G n' hG, hφform h _ hh] at e1
            rw [map_sub, map_mul, map_mul, haevalD, haevalD, sub_eq_zero]
            have hn := hD n
            have hn' := hD n'
            field_simp at e1
            linear_combination e1
        have h4 : h * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ n' k ∈ W := by
          have h5 := sub_mem (Ideal.mul_mem_right (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ n k) W hGW) (hPW hmem)
          simpa using h5
        rcases hWp.mem_or_mem h4 with h3 | h3
        · exact hhW h3
        · exact coordProd_not_mem hWp c hcW n' h3
      exact (mul_eq_zero.mp h1).resolve_right h2

  let eq : (curveRing y ⧸ curvePtIdeal y W) ≃+* (MRing ι ⧸ J) :=
    (Ideal.quotEquivOfEq hkerΘ.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)
  rw [Nat.card_congr eq.toEquiv, hcard, hgeo]
  push_cast
  rw [Real.log_pow]

end

end GroundTheory.Heights₂.Heights.Targets
