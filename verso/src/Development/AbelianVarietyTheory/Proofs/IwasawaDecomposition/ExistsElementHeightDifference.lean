import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory

/- English proof (translation)
Use `set H := Fintype.card (ClassGroup (𝓞 F)) with hH`. Establish `hu : u.asIdeal ∈ nonZeroDivisors (Ideal (𝓞 F))` using `mem_nonZeroDivisors_of_ne_zero u.ne_bot`. Establish `hp : u.asIdeal ^ H ∈ nonZeroDivisors (Ideal (𝓞 F))` using `pow_mem hu H`. Establish `h1 : ClassGroup.mk0 ⟨u.asIdeal ^ H, hp⟩ = 1`. Establish `: (⟨u.asIdeal ^ H, hp⟩ : nonZeroDivisors (Ideal (𝓞 F))) = ⟨u.asIdeal, hu⟩ ^ H` using `rfl`.

Rewrite using `[this, map_pow, hH, pow_card_eq_one]`. Take `⟨π, hπ⟩` from `((ClassGroup.mk0_eq_one_iff hp).1 h1).principal`. Establish `hπ' : u.asIdeal ^ H = Ideal.span {π}` using `hπ`. Establish `hπ0 : π ≠ 0`. Introduce and unpack `rfl`.

Rewrite `hπ'` using `[Ideal.span_singleton_zero]`. Conclude with `pow_ne_zero H u.ne_bot hπ'`. Use `⟨H, π, Fintype.card_pos, hπ0, ?_, fun v hv => ?_⟩` and prove the remaining obligations. Establish `hval : u.valuation F (algebraMap (𝓞 F) F π) = WithZero.exp (-(H : ℤ))`. Rewrite using `[HeightOneSpectrum.valuation_of_algebraMap, u.intValuation_if_neg hπ0, ← hπ', Associates.mk_pow, Associates.count_pow (Associates.mk_ne_zero.2 u.ne_bot) u.associates_irreducible, Associates.count_self u.associates_irreducible, mul_one]`.

Establish `h0 : u.valuation F (algebraMap (𝓞 F) F π) ≠ 0` using `by rw [hval]; exact WithZero.exp_ne_zero`. Rewrite using `[NumberField.HeightOneSpectrum.adicAbv_def, WithZeroMulInt.toNNReal_neg_apply _ h0]`. Establish `: Multiplicative.toAdd (WithZero.unzero h0) = -(H : ℤ)`. Simplify using `only [hval]`. Both sides reduce to the same expression.

Rewrite using `[this]`. Simplify using `[Real.log_inv, Real.log_pow]`. Establish `hn : π ∉ v.asIdeal`. Introduce `hm`. Establish `: u.asIdeal ^ H ≤ v.asIdeal`.

Rewrite using `[hπ', Ideal.span_singleton_le_iff_mem]`. Conclude with `hm`. Establish `h2 : u.asIdeal ≤ v.asIdeal` using `v.isPrime.le_of_pow_le this`. Conclude with `hv (HeightOneSpectrum.ext (u.isMaximal.eq_of_le v.isPrime.ne_top h2).symm)`. Establish `: NumberField.HeightOneSpectrum.adicAbv F v (algebraMap (𝓞 F) F π) = 1` using `(v.adicAbv_coe_eq_one_iff (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v) _).2 hn`.

Rewrite using `[this, Real.log_one]`.
-/
theorem exists_log_adicAbv_eq_single (F : Type) [Field F] [NumberField F]
    (u : HeightOneSpectrum (𝓞 F)) :
    ∃ (H : ℕ) (π : 𝓞 F), 0 < H ∧ π ≠ 0 ∧
      Real.log (NumberField.HeightOneSpectrum.adicAbv F u (algebraMap (𝓞 F) F π)) =
        -(H : ℝ) * Real.log (Ideal.absNorm u.asIdeal : ℝ) ∧
      ∀ v, v ≠ u →
        Real.log (NumberField.HeightOneSpectrum.adicAbv F v (algebraMap (𝓞 F) F π)) = 0 := by
  classical
  set H := Fintype.card (ClassGroup (𝓞 F)) with hH
  have hu : u.asIdeal ∈ nonZeroDivisors (Ideal (𝓞 F)) := mem_nonZeroDivisors_of_ne_zero u.ne_bot
  have hp : u.asIdeal ^ H ∈ nonZeroDivisors (Ideal (𝓞 F)) := pow_mem hu H
  have h1 : ClassGroup.mk0 ⟨u.asIdeal ^ H, hp⟩ = 1 := by
    have : (⟨u.asIdeal ^ H, hp⟩ : nonZeroDivisors (Ideal (𝓞 F))) = ⟨u.asIdeal, hu⟩ ^ H := rfl
    rw [this, map_pow, hH, pow_card_eq_one]
  obtain ⟨π, hπ⟩ := ((ClassGroup.mk0_eq_one_iff hp).1 h1).principal
  have hπ' : u.asIdeal ^ H = Ideal.span {π} := hπ
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_zero] at hπ'
    exact pow_ne_zero H u.ne_bot hπ'
  refine ⟨H, π, Fintype.card_pos, hπ0, ?_, fun v hv => ?_⟩
  · have hval : u.valuation F (algebraMap (𝓞 F) F π) = WithZero.exp (-(H : ℤ)) := by
      rw [HeightOneSpectrum.valuation_of_algebraMap, u.intValuation_if_neg hπ0, ← hπ',
        Associates.mk_pow, Associates.count_pow (Associates.mk_ne_zero.2 u.ne_bot) u.associates_irreducible,
        Associates.count_self u.associates_irreducible, mul_one]
    have h0 : u.valuation F (algebraMap (𝓞 F) F π) ≠ 0 := by rw [hval]; exact WithZero.exp_ne_zero
    rw [NumberField.HeightOneSpectrum.adicAbv_def, WithZeroMulInt.toNNReal_neg_apply _ h0]
    have : Multiplicative.toAdd (WithZero.unzero h0) = -(H : ℤ) := by
      simp only [hval]; rfl
    rw [this]
    simp [Real.log_inv, Real.log_pow]
  · have hn : π ∉ v.asIdeal := by
      intro hm
      have : u.asIdeal ^ H ≤ v.asIdeal := by
        rw [hπ', Ideal.span_singleton_le_iff_mem]; exact hm
      have h2 : u.asIdeal ≤ v.asIdeal := v.isPrime.le_of_pow_le this
      exact hv (HeightOneSpectrum.ext (u.isMaximal.eq_of_le v.isPrime.ne_top h2).symm)
    have : NumberField.HeightOneSpectrum.adicAbv F v (algebraMap (𝓞 F) F π) = 1 :=
      (v.adicAbv_coe_eq_one_iff (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v) _).2 hn
    rw [this, Real.log_one]

/- English proof (translation)
Establish `hlog : ∀ (v : HeightOneSpectrum (𝓞 F)) (x y : 𝓞 F) (k l : ℕ), x ≠ 0 → y ≠ 0 → Real.log (NumberField.HeightOneSpectrum.adicAbv F v (algebraMap (𝓞 F) F (x ^ k * y ^ l))) = k * Real.log (NumberField.HeightOneSpectrum.adicAbv F v (algebraMap (𝓞 F) F x)) + l * Real.log (NumberField.He …`. Introduce `v x y k l hx hy`. Establish `hne : ∀ x : 𝓞 F, x ≠ 0 → NumberField.HeightOneSpectrum.adicAbv F v (algebraMap (𝓞 F) F x) ≠ 0` using `fun x hx => (AbsoluteValue.ne_zero_iff _).2 ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).2 hx)`. Rewrite using `[map_mul, map_pow, map_pow, map_mul, map_pow, map_pow, Real.log_mul (pow_ne_zero _ (hne x hx)) (pow_ne_zero _ (hne y hy)), Real.log_pow, Real.log_pow]`. Establish `key : ∀ S : Finset (HeightOneSpectrum (𝓞 F)), ∃ (h : ℕ) (b b' : 𝓞 F), 0 < h ∧ b ≠ 0 ∧ b' ≠ 0 ∧ ∀ v, (h : ℝ) * (if v ∈ S then c v else 0) = Real.log (NumberField.HeightOneSpectrum.adicAbv F v (algebraMap (𝓞 F) F b)) - Real.log (NumberField.HeightOneSpectrum.adicAbv F v (algebraMap …`.

Introduce `S`. Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => exact ⟨1, 1, 1, one_pos, one_ne_zero, one_ne_zero, fun v => by simp⟩`. Consider the case `insert u S hu ih`. Take `⟨h, b, b', hh, hb, hb', hS⟩` from `ih`.

Take `⟨m, z, hm, hz⟩` from `hq u`. Take `⟨H, π, hH, hπ, h1, h2⟩` from `exists_log_adicAbv_eq_single F u`. Use `⟨h * (m * H), b ^ (m * H) * π ^ (h * (-z).toNat), b' ^ (m * H) * π ^ (h * z.toNat), by positivity, mul_ne_zero (pow_ne_zero _ hb) (pow_ne_zero _ hπ), mul_ne_zero (pow_ne_zero _ hb') (pow_ne_zero _ hπ), fun v => ?_⟩` and prove the remaining obligations. Rewrite using `[hlog v _ _ _ _ hb hπ, hlog v _ _ _ _ hb' hπ]`. Establish `hv` using `hS v`.

Establish `hz' : ((z.toNat : ℕ) : ℝ) - (((-z).toNat : ℕ) : ℝ) = z`. Use `Int.toNat_sub_toNat_neg z` as an intermediate fact. Conclude with `this` after adjusting the coercions. Distinguish the cases in `hvu : v = u`. Substitute `hvu` using the available equality.

Rewrite `hv` using `[if_neg hu]`. Rewrite using `[if_pos (Finset.mem_insert_self _ _), h1]`. Use `push_cast`. Take the linear combination `(m * H : ℝ) * hv + (h * H : ℝ) * hz - (h * H * Real.log (Ideal.absNorm v.asIdeal : ℝ)) * hz'`. Simplify using `only [Finset.mem_insert, hvu, false_or]`.

Rewrite using `[h2 v hvu]`. Use `push_cast`. Take the linear combination `(m * H : ℝ) * hv`. Take `⟨h, b, b', hh, hb, hb', hS⟩` from `key hc.toFinset`. Use `⟨⟨h, hh⟩, b, b', hb, hb', fun v => ?_⟩` and prove the remaining obligations.

Rewrite using `[← hS v]`. Distinguish the cases in `hv : v ∈ hc.toFinset`. Rewrite using `[if_pos hv]`. Both sides reduce to the same expression. Rewrite using `[if_neg hv]`.

Establish `: c v = 0` using `by simpa using hv`. Simplify using `[this]`.
-/
theorem exists_mul_eq_log_adicAbv_sub (F : Type) [Field F] [NumberField F]
    (c : HeightOneSpectrum (𝓞 F) → ℝ) (hc : (Function.support c).Finite)
    (hq : ∀ v, ∃ (m : ℕ) (z : ℤ), 0 < m ∧
      (m : ℝ) * c v = (z : ℝ) * Real.log (Ideal.absNorm v.asIdeal : ℝ)) :
    ∃ (h : ℕ+) (b b' : 𝓞 F), b ≠ 0 ∧ b' ≠ 0 ∧ ∀ v, ((h : ℕ) : ℝ) * c v =
      Real.log (NumberField.HeightOneSpectrum.adicAbv F v (algebraMap (𝓞 F) F b)) -
        Real.log (NumberField.HeightOneSpectrum.adicAbv F v (algebraMap (𝓞 F) F b')) := by
  classical
  have hlog : ∀ (v : HeightOneSpectrum (𝓞 F)) (x y : 𝓞 F) (k l : ℕ), x ≠ 0 → y ≠ 0 →
      Real.log (NumberField.HeightOneSpectrum.adicAbv F v (algebraMap (𝓞 F) F (x ^ k * y ^ l))) =
        k * Real.log (NumberField.HeightOneSpectrum.adicAbv F v (algebraMap (𝓞 F) F x)) +
        l * Real.log (NumberField.HeightOneSpectrum.adicAbv F v (algebraMap (𝓞 F) F y)) := by
    intro v x y k l hx hy
    have hne : ∀ x : 𝓞 F, x ≠ 0 →
        NumberField.HeightOneSpectrum.adicAbv F v (algebraMap (𝓞 F) F x) ≠ 0 := fun x hx =>
      (AbsoluteValue.ne_zero_iff _).2 ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).2 hx)
    rw [map_mul, map_pow, map_pow, map_mul, map_pow, map_pow,
      Real.log_mul (pow_ne_zero _ (hne x hx)) (pow_ne_zero _ (hne y hy)), Real.log_pow, Real.log_pow]
  have key : ∀ S : Finset (HeightOneSpectrum (𝓞 F)), ∃ (h : ℕ) (b b' : 𝓞 F), 0 < h ∧ b ≠ 0 ∧ b' ≠ 0 ∧
      ∀ v, (h : ℝ) * (if v ∈ S then c v else 0) =
      Real.log (NumberField.HeightOneSpectrum.adicAbv F v (algebraMap (𝓞 F) F b)) -
        Real.log (NumberField.HeightOneSpectrum.adicAbv F v (algebraMap (𝓞 F) F b')) := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨1, 1, 1, one_pos, one_ne_zero, one_ne_zero, fun v => by simp⟩
    | insert u S hu ih =>
      obtain ⟨h, b, b', hh, hb, hb', hS⟩ := ih
      obtain ⟨m, z, hm, hz⟩ := hq u
      obtain ⟨H, π, hH, hπ, h1, h2⟩ := exists_log_adicAbv_eq_single F u
      refine ⟨h * (m * H), b ^ (m * H) * π ^ (h * (-z).toNat), b' ^ (m * H) * π ^ (h * z.toNat),
        by positivity, mul_ne_zero (pow_ne_zero _ hb) (pow_ne_zero _ hπ),
        mul_ne_zero (pow_ne_zero _ hb') (pow_ne_zero _ hπ), fun v => ?_⟩
      rw [hlog v _ _ _ _ hb hπ, hlog v _ _ _ _ hb' hπ]
      have hv := hS v
      have hz' : ((z.toNat : ℕ) : ℝ) - (((-z).toNat : ℕ) : ℝ) = z := by
        have := Int.toNat_sub_toNat_neg z
        exact_mod_cast this
      by_cases hvu : v = u
      · subst hvu
        rw [if_neg hu] at hv
        rw [if_pos (Finset.mem_insert_self _ _), h1]
        push_cast
        linear_combination (m * H : ℝ) * hv + (h * H : ℝ) * hz -
          (h * H * Real.log (Ideal.absNorm v.asIdeal : ℝ)) * hz'
      · simp only [Finset.mem_insert, hvu, false_or]
        rw [h2 v hvu]
        push_cast
        linear_combination (m * H : ℝ) * hv
  obtain ⟨h, b, b', hh, hb, hb', hS⟩ := key hc.toFinset
  refine ⟨⟨h, hh⟩, b, b', hb, hb', fun v => ?_⟩
  rw [← hS v]
  by_cases hv : v ∈ hc.toFinset
  · rw [if_pos hv]; rfl
  · rw [if_neg hv]
    have : c v = 0 := by simpa using hv
    simp [this]

end GlobalTheory
