import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMinimalPrimeMultiHomog
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PColonMultiHomog
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSupSpanMultiHomog
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PGradedFinite
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.IsMultiHomogIdealIff
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open MvPolynomial NumbersDVR

noncomputable section

section

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {F : Type} [Field F]

/- English proof (translation)
Set `e : (∀ k, ι k) → (Σ k, ι k) →₀ ℕ` to `fun σ => Finsupp.equivFunOnFinite.symm (fun v => if v.2 = σ v.1 then 1 else 0)`. Establish `he : ∀ σ v, e σ v = if v.2 = σ v.1 then 1 else 0` using `fun σ v => rfl`. Establish `hrad : ∀ σ : (∀ k, ι k), (monomial (e σ) (1 : F)) ∈ J.radical`. Introduce `σ`. Rewrite using `[← Ideal.sInf_minimalPrimes, Submodule.mem_sInf]`.

Introduce `W hW`. Establish `hWp : Ideal.IsPrime W` using `hW.1.1`. Establish `hWh : IsMultiHomogIdeal W` using `MinimalPrimeMultiHomog.proof F K ι J W hJ hW`. Choose the witnesses or unpack the hypotheses as in `⟨k, hk⟩ : ∃ k, ∀ i : ι k, (X ⟨k, i⟩ : MRing ι F) ∈ W := by`. Assume the negation of the conclusion as `h`.

Use `push Not at h`. Conclude with `hrel W hWp hWh h hW.1.2`. Use `Ideal.mem_of_dvd _ ?_ (hk (σ k))` and prove the remaining obligations. Rewrite using `[← pow_one (X _), X_pow_eq_monomial, monomial_dvd_monomial]`. Use `⟨Or.inr ?_, one_dvd _⟩` and prove the remaining obligations.

Rewrite using `[Finsupp.single_le_iff, he]`. Simplify using the standard rewrite rules. Establish `hrad' : ∀ σ : (∀ k, ι k), ∃ n : ℕ, (monomial (e σ) (1 : F)) ^ n ∈ J` using `fun σ => hrad σ`. Use `choose N hN using hrad'`. Use `⟨Finset.univ.sup N, fun m hm x hx => ?_⟩` and prove the remaining obligations.

Rewrite using `[x.as_sum]`. Use `Ideal.sum_mem _ fun d hd => ?_` and prove the remaining obligations. Establish `hw` using `hx (mem_support_iff.mp hd)`. Rewrite `hw` using `[Bridge.weight_blockWeight]`. Establish `hσ : ∀ k, ∃ i : ι k, Finset.univ.sup N ≤ d ⟨k, i⟩`.

Introduce `k`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Establish `h1 : ∑ i, d ⟨k, i⟩ ≤ ∑ _i : ι k, Finset.univ.sup N` using `Finset.sum_le_sum fun i _ => (h i).le`. Establish `h2` using `congrFun hw k`.

Simplify using `only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at h1 h2`. Establish `h3` using `hm k`. Rewrite `h1` using `[h2]`. Rewrite `h3` using `[mul_comm]`. Use linear arithmetic over natural numbers and integers.

Use `choose σ hσ using hσ`. Establish `hmem : monomial (e σ) (1 : F) ^ Finset.univ.sup N ∈ J` using `Ideal.pow_mem_of_pow_mem _ (hN σ) (Finset.le_sup (Finset.mem_univ σ))`. Use `Ideal.mem_of_dvd _ ?_ hmem` and prove the remaining obligations. Rewrite using `[monomial_pow, one_pow, monomial_dvd_monomial]`. Use `⟨Or.inr ?_, one_dvd _⟩` and prove the remaining obligations.

Introduce `v`. Rewrite using `[Finsupp.smul_apply, he, smul_eq_mul]`. Use `split_ifs with hv`. Take `⟨k, i⟩` from `v`. Simplify using `only at hv`.

Substitute `hv` using the available equality. Simplify using `using hσ k`. Simplify using the standard rewrite rules.
-/
theorem exists_forms_mem_of_not_le_relevant {J : Ideal (MRing ι F)} (hJ : IsMultiHomogIdeal J)
    (hrel : ∀ W : Ideal (MRing ι F), W.IsPrime → IsMultiHomogIdeal W → IsRelevant W → ¬ J ≤ W) :
    ∃ n : ℕ, ∀ m : K → ℕ, (∀ k, n * Fintype.card (ι k) < m k) →
      ∀ x : MRing ι F, IsMultiHomog x m → x ∈ J := by
  classical

  let e : (∀ k, ι k) → (Σ k, ι k) →₀ ℕ := fun σ =>
    Finsupp.equivFunOnFinite.symm (fun v => if v.2 = σ v.1 then 1 else 0)
  have he : ∀ σ v, e σ v = if v.2 = σ v.1 then 1 else 0 := fun σ v => rfl
  have hrad : ∀ σ : (∀ k, ι k), (monomial (e σ) (1 : F)) ∈ J.radical := by
    intro σ
    rw [← Ideal.sInf_minimalPrimes, Submodule.mem_sInf]
    intro W hW
    have hWp : Ideal.IsPrime W := hW.1.1
    have hWh : IsMultiHomogIdeal W := MinimalPrimeMultiHomog.proof F K ι J W hJ hW
    obtain ⟨k, hk⟩ : ∃ k, ∀ i : ι k, (X ⟨k, i⟩ : MRing ι F) ∈ W := by
      by_contra h
      push Not at h
      exact hrel W hWp hWh h hW.1.2
    refine Ideal.mem_of_dvd _ ?_ (hk (σ k))
    rw [← pow_one (X _), X_pow_eq_monomial, monomial_dvd_monomial]
    refine ⟨Or.inr ?_, one_dvd _⟩
    rw [Finsupp.single_le_iff, he]
    simp
  have hrad' : ∀ σ : (∀ k, ι k), ∃ n : ℕ, (monomial (e σ) (1 : F)) ^ n ∈ J := fun σ => hrad σ
  choose N hN using hrad'
  refine ⟨Finset.univ.sup N, fun m hm x hx => ?_⟩
  rw [x.as_sum]
  refine Ideal.sum_mem _ fun d hd => ?_
  have hw := hx (mem_support_iff.mp hd)
  rw [Bridge.weight_blockWeight] at hw
  have hσ : ∀ k, ∃ i : ι k, Finset.univ.sup N ≤ d ⟨k, i⟩ := by
    intro k
    by_contra h
    push Not at h
    have h1 : ∑ i, d ⟨k, i⟩ ≤ ∑ _i : ι k, Finset.univ.sup N :=
      Finset.sum_le_sum fun i _ => (h i).le
    have h2 := congrFun hw k
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at h1 h2
    have h3 := hm k
    rw [h2] at h1
    rw [mul_comm] at h3
    omega
  choose σ hσ using hσ
  have hmem : monomial (e σ) (1 : F) ^ Finset.univ.sup N ∈ J :=
    Ideal.pow_mem_of_pow_mem _ (hN σ) (Finset.le_sup (Finset.mem_univ σ))
  refine Ideal.mem_of_dvd _ ?_ hmem
  rw [monomial_pow, one_pow, monomial_dvd_monomial]
  refine ⟨Or.inr ?_, one_dvd _⟩
  intro v
  rw [Finsupp.smul_apply, he, smul_eq_mul]
  split_ifs with hv
  · obtain ⟨k, i⟩ := v
    simp only at hv
    subst hv
    simpa using hσ k
  · simp

/- English proof (translation)
Use `hP.isPrime` as an intermediate fact. Take `⟨bf, bg, hf, hg, hb⟩` from `hs.degrees`. Use `set J : Ideal (MRing ι F) := (P ⊔ Ideal.span {g}).colon {f} with hJdef`. Establish `hJh : IsMultiHomogIdeal J` using `ColonMultiHomog.proof F K ι _ f bf (SupSpanMultiHomog.proof F K ι P g bg hP.multiHomog hg) hf`. Establish `hPJ : P ≤ J` using `fun p hp => by`.

Rewrite using `[hJdef, Submodule.mem_colon_singleton, smul_eq_mul]`. Conclude with `Ideal.mem_sup_left (P.mul_mem_right f hp)`. Establish `hrel : ∀ W : Ideal (MRing ι F), W.IsPrime → IsMultiHomogIdeal W → IsRelevant W → ¬ J ≤ W`. Introduce `W hWp hWh hWr hJW`. Take `⟨u, v, hu, huv⟩` from `hs.regular W ⟨hWp, hWh, hWr⟩ (hPJ.trans hJW)`.

Apply `hu` to reduce the goal to its premises. Apply `hJW` to reduce the goal to its premises. Rewrite using `[hJdef, Submodule.mem_colon_singleton, smul_eq_mul]`. Establish `: u * f = (u * f - v * g) + v * g` using `by ring`. Rewrite using `[this]`.

Conclude with `Ideal.add_mem _ (Ideal.mem_sup_left huv) (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)))`. Take `⟨n, hn⟩` from `exists_forms_mem_of_not_le_relevant hJh hrel`. Rewrite using `[Filter.eventually_atTop]`. Use `⟨fun k => |b k| + (n * Fintype.card (ι k) : ℕ) + 1, fun m hm => ?_⟩` and prove the remaining obligations. Establish `hm' : ∀ k, |b k| + (n * Fintype.card (ι k) : ℕ) + 1 ≤ m k` using `fun k => hm k`.

Establish `hb' : ∀ k, b k = (bf k : ℤ) - bg k` using `fun k => (congrFun hb k).symm`. Establish `hm0 : ∀ k, 0 ≤ m k` using `fun k => by have := hm' k; have := abs_nonneg (b k); omega`. Establish `hmb0 : ∀ k, 0 ≤ (m - b) k` using `fun k => by`. Use `hm' k` as an intermediate fact. Use `le_abs_self (b k)` as an intermediate fact.

Simplify using `only [Pi.sub_apply]`. Use linear arithmetic over natural numbers and integers. Use `set M : K → ℕ := fun k => (m k).toNat with hM`. Use `set M' : K → ℕ := fun k => ((m - b) k).toNat with hM'`. Establish `hdeg : M' + bf = M + bg`.

Use function extensionality and compare the values at `k`. Use `hm0 k` as an intermediate fact. Use `hmb0 k` as an intermediate fact. Use `hb' k` as an intermediate fact. Simplify using `only [Pi.add_apply, hM, hM', Pi.sub_apply] at *`.

Use linear arithmetic over natural numbers and integers. Establish `hbig : ∀ k, n * Fintype.card (ι k) < M' k`. Introduce `k`. Use `hm' k` as an intermediate fact. Use `le_abs_self (b k)` as an intermediate fact.

Simplify using `only [hM', Pi.sub_apply]`. Use linear arithmetic over natural numbers and integers. Establish `hfin` using `(FieldNumbers.GradedFinite.proof F K ι P M).1`. Establish `hfin'` using `(FieldNumbers.GradedFinite.proof F K ι P M').1`. Establish `e1 : hilbFn P m = Module.finrank F (gradedPiece P M)`.

Unfold `hilbFn`. Rewrite using `[if_pos hm0]`. Establish `e2 : hilbFn P (m - b) = Module.finrank F (gradedPiece P M')`. Unfold `hilbFn`. Rewrite using `[if_pos hmb0]`.

Rewrite using `[e1, e2, Nat.cast_le]`. Set `φ : MRing ι F → (MRing ι F ⧸ P) →ₗ[F] (MRing ι F ⧸ P)` to `fun a => LinearMap.mulLeft F (Ideal.Quotient.mk P a)`. Establish `hinj : ∀ a, a ∉ P → Function.Injective (φ a)`. Introduce `a ha`. Conclude with `mul_right_injective₀ (fun h => ha (Ideal.Quotient.eq_zero_iff_mem.mp h))`.

Establish `hle : (gradedPiece P M').map (φ f) ≤ (gradedPiece P M).map (φ g)`. Introduce and unpack `_ ⟨_, ⟨x, hx, rfl⟩, rfl⟩`. Establish `hxh : IsMultiHomog x M'` using `(mem_weightedHomogeneousSubmodule _ _ _ _).mp hx`. Establish `hxJ : x ∈ J` using `hn M' hbig x hxh`. Rewrite `hxJ` using `[hJdef, Submodule.mem_colon_singleton, smul_eq_mul, Submodule.mem_sup]`.

Take `⟨p, hp, q, hq, hpq⟩` from `hxJ`. Take `⟨a, rfl⟩` from `Ideal.mem_span_singleton'.mp hq`. Use `set y := weightedHomogeneousComponent (blockWeight ι) M a`. Establish `hxf : IsMultiHomog (x * f) (M + bg)`. Rewrite using `[← hdeg]`.

Conclude with `hxh.mul hf`. Establish `hcomp` using `congrArg (weightedHomogeneousComponent (blockWeight ι) (M + bg)) hpq`. Rewrite `hcomp` using `[map_add, ← component_mul_multiHomog a g M bg hg, hxf.weightedHomogeneousComponent_same]`. Establish `hpc : weightedHomogeneousComponent (blockWeight ι) (M + bg) p ∈ P` using `hP.multiHomog p hp _`. Use `⟨Ideal.Quotient.mk P y, ⟨y, weightedHomogeneousComponent_isWeightedHomogeneous _ _, rfl⟩, ?_⟩` and prove the remaining obligations.

Simplify using `only [φ, LinearMap.mulLeft_apply, Ideal.Quotient.mkₐ_eq_mk, AlgHom.toLinearMap_apply, ← map_mul]`. Rewrite using `[Ideal.Quotient.eq, mul_comm f x, ← hcomp]`. Establish `: g * y - (weightedHomogeneousComponent (blockWeight ι) (M + bg) p + y * g) = -weightedHomogeneousComponent (blockWeight ι) (M + bg) p` using `by ring`. Rewrite using `[this]`. Conclude with `P.neg_mem hpc`.

Combine the equalities or inequalities in the displayed calculation. Establish `: FiniteDimensional F ((gradedPiece P M).map (φ g))` using `Module.Finite.map _ _`. Conclude with `LinearMap.finrank_le_finrank_of_injective (f := Submodule.inclusion hle) (Submodule.inclusion_injective hle)`. Use `_ = Module.finrank F (gradedPiece P M) := ((Submodule.equivMapOfInjective _ (hinj g hs.den_not_mem) _).finrank_eq).symm`.
-/
theorem hilbFn_sub_le_of_regular {P : Ideal (MRing ι F)} (hP : IsMultiProjPrime P) {b : K → ℤ}
    {f g : MRing ι F} (hs : IsRegularSection P b f g) :
    ∀ᶠ m in Filter.atTop, hilbFn P (m - b) ≤ hilbFn P m := by
  classical
  have := hP.isPrime
  obtain ⟨bf, bg, hf, hg, hb⟩ := hs.degrees
  set J : Ideal (MRing ι F) := (P ⊔ Ideal.span {g}).colon {f} with hJdef
  have hJh : IsMultiHomogIdeal J :=
    ColonMultiHomog.proof F K ι _ f bf
      (SupSpanMultiHomog.proof F K ι P g bg hP.multiHomog hg) hf
  have hPJ : P ≤ J := fun p hp => by
    rw [hJdef, Submodule.mem_colon_singleton, smul_eq_mul]
    exact Ideal.mem_sup_left (P.mul_mem_right f hp)
  have hrel : ∀ W : Ideal (MRing ι F), W.IsPrime → IsMultiHomogIdeal W → IsRelevant W →
      ¬ J ≤ W := by
    intro W hWp hWh hWr hJW
    obtain ⟨u, v, hu, huv⟩ := hs.regular W ⟨hWp, hWh, hWr⟩ (hPJ.trans hJW)
    apply hu
    apply hJW
    rw [hJdef, Submodule.mem_colon_singleton, smul_eq_mul]
    have : u * f = (u * f - v * g) + v * g := by ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mem_sup_left huv)
      (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)))
  obtain ⟨n, hn⟩ := exists_forms_mem_of_not_le_relevant hJh hrel
  rw [Filter.eventually_atTop]
  refine ⟨fun k => |b k| + (n * Fintype.card (ι k) : ℕ) + 1, fun m hm => ?_⟩
  have hm' : ∀ k, |b k| + (n * Fintype.card (ι k) : ℕ) + 1 ≤ m k := fun k => hm k
  have hb' : ∀ k, b k = (bf k : ℤ) - bg k := fun k => (congrFun hb k).symm
  have hm0 : ∀ k, 0 ≤ m k := fun k => by have := hm' k; have := abs_nonneg (b k); omega
  have hmb0 : ∀ k, 0 ≤ (m - b) k := fun k => by
    have := hm' k; have := le_abs_self (b k); simp only [Pi.sub_apply]; omega
  set M : K → ℕ := fun k => (m k).toNat with hM
  set M' : K → ℕ := fun k => ((m - b) k).toNat with hM'
  have hdeg : M' + bf = M + bg := by
    funext k
    have := hm0 k; have := hmb0 k; have := hb' k
    simp only [Pi.add_apply, hM, hM', Pi.sub_apply] at *
    omega
  have hbig : ∀ k, n * Fintype.card (ι k) < M' k := by
    intro k
    have := hm' k; have := le_abs_self (b k)
    simp only [hM', Pi.sub_apply]
    omega
  have hfin := (FieldNumbers.GradedFinite.proof F K ι P M).1
  have hfin' := (FieldNumbers.GradedFinite.proof F K ι P M').1
  have e1 : hilbFn P m = Module.finrank F (gradedPiece P M) := by
    unfold hilbFn; rw [if_pos hm0]
  have e2 : hilbFn P (m - b) = Module.finrank F (gradedPiece P M') := by
    unfold hilbFn; rw [if_pos hmb0]
  rw [e1, e2, Nat.cast_le]

  let φ : MRing ι F → (MRing ι F ⧸ P) →ₗ[F] (MRing ι F ⧸ P) := fun a =>
    LinearMap.mulLeft F (Ideal.Quotient.mk P a)
  have hinj : ∀ a, a ∉ P → Function.Injective (φ a) := by
    intro a ha
    exact mul_right_injective₀ (fun h => ha (Ideal.Quotient.eq_zero_iff_mem.mp h))
  have hle : (gradedPiece P M').map (φ f) ≤ (gradedPiece P M).map (φ g) := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    have hxh : IsMultiHomog x M' := (mem_weightedHomogeneousSubmodule _ _ _ _).mp hx
    have hxJ : x ∈ J := hn M' hbig x hxh
    rw [hJdef, Submodule.mem_colon_singleton, smul_eq_mul, Submodule.mem_sup] at hxJ
    obtain ⟨p, hp, q, hq, hpq⟩ := hxJ
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hq
    set y := weightedHomogeneousComponent (blockWeight ι) M a
    have hxf : IsMultiHomog (x * f) (M + bg) := by
      rw [← hdeg]; exact hxh.mul hf
    have hcomp := congrArg (weightedHomogeneousComponent (blockWeight ι) (M + bg)) hpq
    rw [map_add, ← component_mul_multiHomog a g M bg hg,
      hxf.weightedHomogeneousComponent_same] at hcomp
    have hpc : weightedHomogeneousComponent (blockWeight ι) (M + bg) p ∈ P :=
      hP.multiHomog p hp _
    refine ⟨Ideal.Quotient.mk P y, ⟨y, weightedHomogeneousComponent_isWeightedHomogeneous _ _,
      rfl⟩, ?_⟩
    simp only [φ, LinearMap.mulLeft_apply, Ideal.Quotient.mkₐ_eq_mk, AlgHom.toLinearMap_apply,
      ← map_mul]
    rw [Ideal.Quotient.eq, mul_comm f x, ← hcomp]
    have : g * y - (weightedHomogeneousComponent (blockWeight ι) (M + bg) p + y * g) =
      -weightedHomogeneousComponent (blockWeight ι) (M + bg) p := by ring
    rw [this]
    exact P.neg_mem hpc
  calc Module.finrank F (gradedPiece P M')
      = Module.finrank F ((gradedPiece P M').map (φ f)) :=
        (Submodule.equivMapOfInjective _ (hinj f hs.num_not_mem) _).finrank_eq
    _ ≤ Module.finrank F ((gradedPiece P M).map (φ g)) := by
        have : FiniteDimensional F ((gradedPiece P M).map (φ g)) :=
          Module.Finite.map _ _
        exact LinearMap.finrank_le_finrank_of_injective (f := Submodule.inclusion hle)
          (Submodule.inclusion_injective hle)
    _ = Module.finrank F (gradedPiece P M) :=
        ((Submodule.equivMapOfInjective _ (hinj g hs.den_not_mem) _).finrank_eq).symm

end

/- English proof (translation)
Introduce `K _ _ ι _ F _ P hP _ b f g hs`. Establish `hev` using `hilbFn_sub_le_of_regular hP hs`. Unfold `intNum eventualValue`. Use `split_ifs with h`. Take `⟨m, hm1, hm2⟩` from `(h.choose_spec.and hev).exists`.

Rewrite using `[← hm1]`. Simplify using `only [mixedDiff, List.ofFn_succ, List.ofFn_zero, List.foldr_cons, List.foldr_nil, Matrix.cons_val_zero, diffStep]`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `le_rfl`.
-/
theorem SectionNef.proof : SectionNef.Statement := by
  intro K _ _ ι _ F _ P hP _ b f g hs
  have hev := hilbFn_sub_le_of_regular hP hs
  unfold intNum eventualValue
  split_ifs with h
  · obtain ⟨m, hm1, hm2⟩ := (h.choose_spec.and hev).exists
    rw [← hm1]
    simp only [mixedDiff, List.ofFn_succ, List.ofFn_zero, List.foldr_cons, List.foldr_nil,
      Matrix.cons_val_zero, diffStep]
    linarith
  · exact le_rfl

/- English proof (translation)
The claim follows from `SectionNefGenerated.of_sectionNef SectionNef.proof`.
-/
theorem SectionNefGenerated.proof : SectionNefGenerated.Statement :=
  SectionNefGenerated.of_sectionNef SectionNef.proof

end

end GroundTheory.Heights₂.Heights.Model
