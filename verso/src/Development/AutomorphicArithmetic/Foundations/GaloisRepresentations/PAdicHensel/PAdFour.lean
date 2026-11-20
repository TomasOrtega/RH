import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PadicUnitNorm
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

/- English proof (translation)
Establish `hcF : (c : F) ≠ 0` using `by simpa using hc`. Establish `hcv : algebraMap F (v.adicCompletion F) (c : F) ≠ 0`. Simplify using `using hcF`. Distinguish the cases in `hg : c ∉ v.asIdeal ∧ (((2 * (tr ^ 2 - 4 * nm) : ℤ) : 𝓞 F) ∉ v.asIdeal ∨ ∃ q : ℕ, q.Prime ∧ (q : 𝓞 F) ∈ v.asIdeal ∧ ¬ (q : ℤ) ∣ tr ^ 2 - 4 * nm ∧ ∃ r : ℤ, (q : ℤ) ∣ r ^ 2 - tr * r + nm)`. Take `⟨hcm, hor⟩` from `hg`.

Establish `hval : Valued.v (algebraMap F (v.adicCompletion F) (c : F)) = 1`. Use `(HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (c : F)).trans ?_` and prove the remaining obligations. Establish `h0 : v.valuation F (c : F) = v.intValuation c` using `HeightOneSpectrum.valuation_of_algebraMap v c`. Rewrite using `[h0]`. Use `first`.

Consider the case `exact (HeightOneSpectrum.intValuation_eq_one_iff v).2 hcm`. Consider the case `exact le_antisymm (v.intValuation_le_one c) (not_lt.1 fun h => hcm ((v.intValuation_lt_one_iff_mem c).1 h))`. Establish `hval' : Valued.v (algebraMap F (v.adicCompletion F) (c : F))⁻¹ = 1`. Rewrite using `[map_inv₀, hval, inv_one]`. Set `c1 : v.adicCompletionIntegers F` to `⟨_, hval.le⟩`.

Set `c2 : v.adicCompletionIntegers F` to `⟨_, hval'.le⟩`. Establish `h12 : c2 * c1 = 1` using `Subtype.ext (inv_mul_cancel₀ hcv)`. Establish `hu : IsUnit c2` using `isUnit_iff_exists_inv.2 ⟨c1, h12⟩`. Choose the witnesses or unpack the hypotheses as in `⟨a, b, hab⟩ : ∃ a b : v.adicCompletionIntegers F, qf tr nm a b = c2 := by`. Break down `hor with h | ⟨q, hq, hqv, hqd, hr⟩` into its components or cases.

Conclude with `hU F v tr nm h c2 hu`. Take `⟨ρ, h1, h2⟩` from `hR F v tr nm q hq hqv hqd hr`. Conclude with `hS _ tr nm ρ h1 h2 c2`. Establish `hab' : qf tr nm (a : v.adicCompletion F) (b : v.adicCompletion F) = (algebraMap F (v.adicCompletion F) (c : F))⁻¹`. Use `congrArg (Subtype.val) hab` as an intermediate fact.

Simplify `this` using `[qf]`. Use `⟨![a, b, 0, 0], ?_, fun _ _ i => ?_⟩` and prove the remaining obligations. Simplify using `only [Matrix.cons_val]`. Establish `h0 : qf tr nm (0 : v.adicCompletion F) 0 = 0` using `by simp [qf]`. Rewrite using `[hab', h0, add_zero, mul_inv_cancel₀ hcv]`.

Use `fin_cases i`. Conclude with `a.2`. Conclude with `b.2`. Conclude with `zero_mem _`. Conclude with `zero_mem _`.

Take `⟨a, b, a', b', h⟩` from `hF F v tr nm hd _ (inv_ne_zero hcv)`. Use `⟨![a, b, a', b'], ?_, fun h1 h2 => absurd ⟨h1, h2⟩ hg⟩` and prove the remaining obligations. Simplify using `only [Matrix.cons_val]`. Rewrite using `[h, mul_inv_cancel₀ hcv]`.
-/
private theorem UpperTheory.Gal.G1.exists_local (hF : LocFour) (hU : LocUnit) (hR : LocRoot) (hS : SplitRep)
    (F : Type) [Field F] [NumberField F] (tr nm : ℤ) (hd : tr ^ 2 - 4 * nm ≠ 0) (c : 𝓞 F) (hc : c ≠ 0)
    (v : HeightOneSpectrum (𝓞 F)) :
    ∃ f : Fin 4 → v.adicCompletion F,
      algebraMap F (v.adicCompletion F) (c : F) * (qf tr nm (f 0) (f 1) + qf tr nm (f 2) (f 3)) = 1 ∧
      (c ∉ v.asIdeal → (((2 * (tr ^ 2 - 4 * nm) : ℤ) : 𝓞 F) ∉ v.asIdeal ∨
        ∃ q : ℕ, q.Prime ∧ (q : 𝓞 F) ∈ v.asIdeal ∧ ¬ (q : ℤ) ∣ tr ^ 2 - 4 * nm ∧
          ∃ r : ℤ, (q : ℤ) ∣ r ^ 2 - tr * r + nm) → ∀ i, f i ∈ v.adicCompletionIntegers F) := by
  have hcF : (c : F) ≠ 0 := by simpa using hc
  have hcv : algebraMap F (v.adicCompletion F) (c : F) ≠ 0 := by
    simpa using hcF
  by_cases hg : c ∉ v.asIdeal ∧ (((2 * (tr ^ 2 - 4 * nm) : ℤ) : 𝓞 F) ∉ v.asIdeal ∨
        ∃ q : ℕ, q.Prime ∧ (q : 𝓞 F) ∈ v.asIdeal ∧ ¬ (q : ℤ) ∣ tr ^ 2 - 4 * nm ∧
          ∃ r : ℤ, (q : ℤ) ∣ r ^ 2 - tr * r + nm)
  · obtain ⟨hcm, hor⟩ := hg
    have hval : Valued.v (algebraMap F (v.adicCompletion F) (c : F)) = 1 := by
      refine (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (c : F)).trans ?_
      have h0 : v.valuation F (c : F) = v.intValuation c := HeightOneSpectrum.valuation_of_algebraMap v c
      rw [h0]
      first
        | exact (HeightOneSpectrum.intValuation_eq_one_iff v).2 hcm
        | exact le_antisymm (v.intValuation_le_one c)
            (not_lt.1 fun h => hcm ((v.intValuation_lt_one_iff_mem c).1 h))
    have hval' : Valued.v (algebraMap F (v.adicCompletion F) (c : F))⁻¹ = 1 := by
      rw [map_inv₀, hval, inv_one]
    let c1 : v.adicCompletionIntegers F := ⟨_, hval.le⟩
    let c2 : v.adicCompletionIntegers F := ⟨_, hval'.le⟩
    have h12 : c2 * c1 = 1 := Subtype.ext (inv_mul_cancel₀ hcv)
    have hu : IsUnit c2 := isUnit_iff_exists_inv.2 ⟨c1, h12⟩
    obtain ⟨a, b, hab⟩ : ∃ a b : v.adicCompletionIntegers F, qf tr nm a b = c2 := by
      rcases hor with h | ⟨q, hq, hqv, hqd, hr⟩
      · exact hU F v tr nm h c2 hu
      · obtain ⟨ρ, h1, h2⟩ := hR F v tr nm q hq hqv hqd hr
        exact hS _ tr nm ρ h1 h2 c2
    have hab' : qf tr nm (a : v.adicCompletion F) (b : v.adicCompletion F)
        = (algebraMap F (v.adicCompletion F) (c : F))⁻¹ := by
      have := congrArg (Subtype.val) hab
      simpa [qf] using this
    refine ⟨![a, b, 0, 0], ?_, fun _ _ i => ?_⟩
    · simp only [Matrix.cons_val]
      have h0 : qf tr nm (0 : v.adicCompletion F) 0 = 0 := by simp [qf]
      rw [hab', h0, add_zero, mul_inv_cancel₀ hcv]
    · fin_cases i
      · exact a.2
      · exact b.2
      · exact zero_mem _
      · exact zero_mem _
  · obtain ⟨a, b, a', b', h⟩ := hF F v tr nm hd _ (inv_ne_zero hcv)
    refine ⟨![a, b, a', b'], ?_, fun h1 h2 => absurd ⟨h1, h2⟩ hg⟩
    simp only [Matrix.cons_val]
    rw [h, mul_inv_cancel₀ hcv]

/- English proof (translation)
Introduce `hF hU hR hS F _ _ tr nm hd c hc`. Use `choose f hf1 hf2 using exists_local hF hU hR hS F tr nm hd c hc`. Establish `hD : ((2 * (tr ^ 2 - 4 * nm) : ℤ) : 𝓞 F) ≠ 0`. Establish `: (2 * (tr ^ 2 - 4 * nm) : ℤ) ≠ 0` using `mul_ne_zero two_ne_zero hd`. Conclude with `this` after adjusting the coercions.

Establish `hI : Ideal.span {((2 * (tr ^ 2 - 4 * nm) : ℤ) : 𝓞 F) * c} ≠ 0`. Rewrite using `[Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]`. Conclude with `mul_ne_zero hD hc`. Establish `hfin : {v : HeightOneSpectrum (𝓞 F) | ((2 * (tr ^ 2 - 4 * nm) : ℤ) : 𝓞 F) * c ∈ v.asIdeal}.Finite`. Use `(Ideal.finite_factors hI).subset fun v hv => ?_` and prove the remaining obligations.

Conclude with `Ideal.dvd_span_singleton.2 hv`. Establish `hev : ∀ i, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, f v i ∈ v.adicCompletionIntegers F`. Introduce `i`. Use `Filter.eventually_cofinite.2 (hfin.subset fun v hv => ?_)` and prove the remaining obligations. Assume the negation of the conclusion as `h`.

Establish `h1 : c ∉ v.asIdeal` using `fun hm => h (Ideal.mul_mem_left _ _ hm)`. Establish `h2 : ((2 * (tr ^ 2 - 4 * nm) : ℤ) : 𝓞 F) ∉ v.asIdeal` using `fun hm => h (Ideal.mul_mem_right _ _ hm)`. Conclude with `hv (hf2 v h1 (Or.inl h2) i)`. Set `A : Fin 4 → FiniteAdeleRing (𝓞 F) F` to `fun i => ⟨fun v => f v i, hev i⟩`. Use `⟨A, ?_, ?_⟩` and prove the remaining obligations.

Use `FiniteAdeleRing.ext _ fun v => ?_` and prove the remaining obligations. Use `hf1 v` as an intermediate fact. Set `φ : FiniteAdeleRing (𝓞 F) F →+* v.adicCompletion F` to `{ toFun := fun x => x v map_one' := rfl map_mul' := fun _ _ => rfl map_zero' := rfl map_add' := fun _ _ => rfl }`. Establish `key : φ (algebraMap F (FiniteAdeleRing (𝓞 F) F) (c : F) * (qf tr nm (A 0) (A 1) + qf tr nm (A 2) (A 3))) = φ 1`. Simplify using `only [qf, map_mul, map_add, map_pow, map_intCast, map_one]`.

Establish `hA : ∀ i, φ (A i) = f v i` using `fun _ => rfl`. Establish `hc' : φ (algebraMap F (FiniteAdeleRing (𝓞 F) F) (c : F)) = algebraMap F (v.adicCompletion F) (c : F)` using `rfl`. Rewrite using `[hc']`. Simplify using `only [hA]`. Simplify `this` using `only [qf]`.

Conclude with `key`. Introduce `v q hq hqv hqd hr hcv i`. Conclude with `hf2 v hcv (Or.inr ⟨q, hq, hqv, hqd, hr⟩) i`.
-/
theorem UpperTheory.Gal.G1.pAdFour :
    LocFour → LocUnit → LocRoot → SplitRep → AdFour := by
  intro hF hU hR hS F _ _ tr nm hd c hc
  choose f hf1 hf2 using exists_local hF hU hR hS F tr nm hd c hc
  have hD : ((2 * (tr ^ 2 - 4 * nm) : ℤ) : 𝓞 F) ≠ 0 := by
    have : (2 * (tr ^ 2 - 4 * nm) : ℤ) ≠ 0 := mul_ne_zero two_ne_zero hd
    exact_mod_cast this
  have hI : Ideal.span {((2 * (tr ^ 2 - 4 * nm) : ℤ) : 𝓞 F) * c} ≠ 0 := by
    rw [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]
    exact mul_ne_zero hD hc
  have hfin : {v : HeightOneSpectrum (𝓞 F) | ((2 * (tr ^ 2 - 4 * nm) : ℤ) : 𝓞 F) * c ∈ v.asIdeal}.Finite := by
    refine (Ideal.finite_factors hI).subset fun v hv => ?_
    exact Ideal.dvd_span_singleton.2 hv
  have hev : ∀ i, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, f v i ∈ v.adicCompletionIntegers F := by
    intro i
    refine Filter.eventually_cofinite.2 (hfin.subset fun v hv => ?_)
    by_contra h
    have h1 : c ∉ v.asIdeal := fun hm => h (Ideal.mul_mem_left _ _ hm)
    have h2 : ((2 * (tr ^ 2 - 4 * nm) : ℤ) : 𝓞 F) ∉ v.asIdeal := fun hm => h (Ideal.mul_mem_right _ _ hm)
    exact hv (hf2 v h1 (Or.inl h2) i)
  let A : Fin 4 → FiniteAdeleRing (𝓞 F) F := fun i => ⟨fun v => f v i, hev i⟩
  refine ⟨A, ?_, ?_⟩
  · refine FiniteAdeleRing.ext _ fun v => ?_
    have := hf1 v
    let φ : FiniteAdeleRing (𝓞 F) F →+* v.adicCompletion F :=
      { toFun := fun x => x v
        map_one' := rfl
        map_mul' := fun _ _ => rfl
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    have key : φ (algebraMap F (FiniteAdeleRing (𝓞 F) F) (c : F) *
        (qf tr nm (A 0) (A 1) + qf tr nm (A 2) (A 3))) = φ 1 := by
      simp only [qf, map_mul, map_add, map_pow, map_intCast, map_one]
      have hA : ∀ i, φ (A i) = f v i := fun _ => rfl
      have hc' : φ (algebraMap F (FiniteAdeleRing (𝓞 F) F) (c : F)) =
          algebraMap F (v.adicCompletion F) (c : F) := rfl
      rw [hc']
      simp only [hA]
      simpa only [qf] using this
    exact key
  · intro v q hq hqv hqd hr hcv i
    exact hf2 v hcv (Or.inr ⟨q, hq, hqv, hqd, hr⟩) i
