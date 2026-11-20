import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegZeroLocNoetherian
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegZeroLocQuot
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

/- English proof (translation)
Introduce `F _ K _ _ ι _ P hP W hW hPW`. Use `hP.isPrime` as an intermediate fact. Use `hW.isPrime` as an intermediate fact. Set `φ : MRing ι F →ₐ[F] FractionRing (MRing ι F ⧸ P)` to `(IsScalarTower.toAlgHom F (MRing ι F ⧸ P) _).comp (Ideal.Quotient.mkₐ F P)`. Establish `hφ : ∀ f, f ∉ P → φ f ≠ 0` using `fun f hf h0 => hf (by`.

Rewrite using `[AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem] at h0)` and apply the resulting hypothesis. Use `choose v hv using hW.relevant`. Set `e : MRing ι F →ₐ[F] FractionRing (MRing ι F ⧸ P)` to `aeval fun x => φ (X x) / φ (X ⟨x.1, v x.1⟩)`. Set `c : (K → ℕ) → MRing ι F` to `fun b => ∏ k, (X ⟨k, v k⟩ : MRing ι F) ^ b k`. Establish `hcW : ∀ b, c b ∉ W`.

Introduce `b`. Rewrite using `[Ideal.IsPrime.prod_mem_iff]`. Introduce and unpack `⟨k, -, hk⟩`. Conclude with `hv k (Ideal.IsPrime.mem_of_pow_mem inferInstance _ hk)`. Establish `hc : ∀ b, IsMultiHomog (c b) b`.

Introduce `b`. Establish `hprod` using `IsWeightedHomogeneous.prod (w := blockWeight ι) Finset.univ (fun k => (X ⟨k, v k⟩ : MRing ι F) ^ b k) (fun k => b k • blockWeight ι ⟨k, v k⟩) (fun k _ => (isWeightedHomogeneous_X F (blockWeight ι) _).pow (b k))`. Establish `hb : (∑ k, b k • blockWeight ι ⟨k, v k⟩) = b`. Use function extensionality and compare the values at `k'`. Simplify using `[blockWeight, Finset.sum_apply, Pi.single_apply]`.

Rewrite `hprod` using `[hb]`. Conclude with `hprod`. Establish `hcadd : ∀ b b', c (b + b') = c b * c b'` using `fun b b' => by`. Simplify using `only [c, Pi.add_apply, pow_add, Finset.prod_mul_distrib]`. Establish `hmono : ∀ m : (Σ k, ι k) →₀ ℕ, φ (monomial m 1) = e (monomial m 1) * φ (c (Finsupp.weight (blockWeight ι) m))`.

Introduce `m`. Use `Finsupp.induction m ?_ ?_` and prove the remaining obligations. Simplify using `[c]`. Introduce `x n m _ _ ih`. Establish `hs : φ (monomial (Finsupp.single x n) 1) = e (monomial (Finsupp.single x n) 1) * φ (c (Finsupp.weight (blockWeight ι) (Finsupp.single x n)))`.

Rewrite using `[Finsupp.weight_single, ← X_pow_eq_monomial, map_pow, map_pow, aeval_X]`. Establish `hcs : c (n • blockWeight ι x) = (X ⟨x.1, v x.1⟩ : MRing ι F) ^ n`. Simplify using `only [c, blockWeight]`. Rewrite using `[Finset.prod_eq_single x.1]`. Simplify using the standard rewrite rules.

Introduce `k _ hk`. Simplify using `[hk]`. Simplify using the standard rewrite rules. Rewrite using `[hcs, map_pow, ← mul_pow, div_mul_cancel₀ _ (hφ _ fun hm => hv x.1 (hPW hm))]`. Rewrite using `[← mul_one (1 : F), ← monomial_mul, map_mul, map_mul, ih, map_add, hcadd, map_mul, hs]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hhom : ∀ (b : K → ℕ) (f : MRing ι F), IsMultiHomog f b → φ f = e f * φ (c b)`. Introduce `b f hf`. Use `conv_lhs => rw [f.as_sum]`. Use `conv_rhs => rw [f.as_sum]`.

Rewrite using `[map_sum, map_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations. Establish `hw : Finsupp.weight (blockWeight ι) m = b` using `hf (mem_support_iff.mp hm)`. Establish `hmon : monomial m (coeff m f) = coeff m f • monomial m (1 : F)`. Rewrite using `[smul_monomial, smul_eq_mul, mul_one]`.

Rewrite using `[hmon, map_smul, map_smul, hmono, hw, smul_mul_assoc]`. Establish `hle : e.range ≤ degZeroLoc P {W}`. Rewrite using `[← Algebra.adjoin_range_eq_range_aeval, Algebra.adjoin_le_iff]`. Introduce and unpack `_ ⟨x, rfl⟩`. Conclude with `div_mem_degZeroLoc P {W} (isWeightedHomogeneous_X F (blockWeight ι) x) (isWeightedHomogeneous_X F (blockWeight ι) ⟨x.1, v x.1⟩) (fun hm => hv x.1 (hPW hm)) (fun W' hW' => (Set.mem_singleton_iff.mp hW') ▸ hv x.1)`.

Establish `: Algebra.FiniteType F e.range` using `Algebra.FiniteType.of_surjective e.rangeRestrict e.rangeRestrict_surjective`. Establish `_ : IsNoetherianRing e.range` using `Algebra.FiniteType.isNoetherianRing F e.range`. Set `_ : Algebra e.range (degZeroLoc P {W})` to `(Subalgebra.inclusion hle).toAlgebra`. Set `M : Submonoid e.range` to `(IsUnit.submonoid (degZeroLoc P {W})).comap (algebraMap e.range (degZeroLoc P {W}))`. Establish `hloc : IsLocalization M (degZeroLoc P {W})`.

Rewrite using `[isLocalization_iff]`. Use `⟨fun y => y.2, fun z => ?_, fun {x y} hxy => ⟨1, by rw [Subalgebra.inclusion_injective hle hxy]⟩⟩` and prove the remaining obligations. Take `⟨b, f, g, hf, hg, hgP, hgW, hz⟩` from `h F K ι P {W} (fun W' hW' => (Set.mem_singleton_iff.mp hW') ▸ hW.isPrime) z.1 z.2`. Establish `hgW' : g ∉ W` using `hgW W rfl`. Establish `hcb : φ (c b) ≠ 0` using `hφ _ fun hm => hcW b (hPW hm)`.

Establish `hz' : (z : FractionRing (MRing ι F ⧸ P)) = φ f / φ g` using `hz`. Establish `heg : e g ≠ 0`. Introduce `h0`. Apply `hφ g hgP` to reduce the goal to its premises. Rewrite using `[hhom b g hg, h0, zero_mul]`.

Establish `hinv : (e g)⁻¹ ∈ degZeroLoc P {W}`. Establish `hq : (e g)⁻¹ = φ (c b) / φ g`. Rewrite using `[hhom b g hg]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hq]`.

Conclude with `div_mem_degZeroLoc P {W} (hc b) hg hgP (fun W' hW' => (Set.mem_singleton_iff.mp hW') ▸ hgW')`. Establish `hunit : (⟨e g, g, rfl⟩ : e.range) ∈ M` using `isUnit_iff_exists_inv.mpr ⟨⟨(e g)⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ heg)⟩`. Use `⟨(⟨e f, f, rfl⟩, ⟨⟨e g, g, rfl⟩, hunit⟩), Subtype.ext ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(z : FractionRing (MRing ι F ⧸ P)) * e g = e f`. Rewrite using `[hz', hhom b f hf, hhom b g hg]`.

Clear the denominators using the available nonvanishing facts. Conclude with `IsLocalization.isNoetherianRing M _ inferInstance`.
-/
theorem DegZeroLocNoetherian.proof (h : DegZeroLocQuot.Statement.{u}) :
    DegZeroLocNoetherian.Statement.{u} := by
  intro F _ K _ _ ι _ P hP W hW hPW
  have := hP.isPrime
  have := hW.isPrime
  let φ : MRing ι F →ₐ[F] FractionRing (MRing ι F ⧸ P) :=
    (IsScalarTower.toAlgHom F (MRing ι F ⧸ P) _).comp (Ideal.Quotient.mkₐ F P)
  have hφ : ∀ f, f ∉ P → φ f ≠ 0 := fun f hf h0 => hf (by
    rwa [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', IsFractionRing.to_map_eq_zero_iff,
      Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem] at h0)
  choose v hv using hW.relevant
  let e : MRing ι F →ₐ[F] FractionRing (MRing ι F ⧸ P) :=
    aeval fun x => φ (X x) / φ (X ⟨x.1, v x.1⟩)
  let c : (K → ℕ) → MRing ι F := fun b => ∏ k, (X ⟨k, v k⟩ : MRing ι F) ^ b k
  have hcW : ∀ b, c b ∉ W := by
    intro b
    rw [Ideal.IsPrime.prod_mem_iff]
    rintro ⟨k, -, hk⟩
    exact hv k (Ideal.IsPrime.mem_of_pow_mem inferInstance _ hk)
  have hc : ∀ b, IsMultiHomog (c b) b := by
    intro b
    have hprod := IsWeightedHomogeneous.prod (w := blockWeight ι) Finset.univ
      (fun k => (X ⟨k, v k⟩ : MRing ι F) ^ b k) (fun k => b k • blockWeight ι ⟨k, v k⟩)
      (fun k _ => (isWeightedHomogeneous_X F (blockWeight ι) _).pow (b k))
    have hb : (∑ k, b k • blockWeight ι ⟨k, v k⟩) = b := by
      funext k'
      simp [blockWeight, Finset.sum_apply, Pi.single_apply]
    rw [hb] at hprod
    exact hprod
  have hcadd : ∀ b b', c (b + b') = c b * c b' := fun b b' => by
    simp only [c, Pi.add_apply, pow_add, Finset.prod_mul_distrib]

  have hmono : ∀ m : (Σ k, ι k) →₀ ℕ,
      φ (monomial m 1) = e (monomial m 1) * φ (c (Finsupp.weight (blockWeight ι) m)) := by
    intro m
    refine Finsupp.induction m ?_ ?_
    · simp [c]
    · intro x n m _ _ ih
      have hs : φ (monomial (Finsupp.single x n) 1) = e (monomial (Finsupp.single x n) 1) *
          φ (c (Finsupp.weight (blockWeight ι) (Finsupp.single x n))) := by
        rw [Finsupp.weight_single, ← X_pow_eq_monomial, map_pow, map_pow, aeval_X]
        have hcs : c (n • blockWeight ι x) = (X ⟨x.1, v x.1⟩ : MRing ι F) ^ n := by
          simp only [c, blockWeight]
          rw [Finset.prod_eq_single x.1]
          · simp
          · intro k _ hk
            simp [hk]
          · simp
        rw [hcs, map_pow, ← mul_pow, div_mul_cancel₀ _ (hφ _ fun hm => hv x.1 (hPW hm))]
      rw [← mul_one (1 : F), ← monomial_mul, map_mul, map_mul, ih, map_add, hcadd, map_mul, hs]
      ring

  have hhom : ∀ (b : K → ℕ) (f : MRing ι F), IsMultiHomog f b → φ f = e f * φ (c b) := by
    intro b f hf
    conv_lhs => rw [f.as_sum]
    conv_rhs => rw [f.as_sum]
    rw [map_sum, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hw : Finsupp.weight (blockWeight ι) m = b := hf (mem_support_iff.mp hm)
    have hmon : monomial m (coeff m f) = coeff m f • monomial m (1 : F) := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [hmon, map_smul, map_smul, hmono, hw, smul_mul_assoc]
  have hle : e.range ≤ degZeroLoc P {W} := by
    rw [← Algebra.adjoin_range_eq_range_aeval, Algebra.adjoin_le_iff]
    rintro _ ⟨x, rfl⟩
    exact div_mem_degZeroLoc P {W} (isWeightedHomogeneous_X F (blockWeight ι) x)
      (isWeightedHomogeneous_X F (blockWeight ι) ⟨x.1, v x.1⟩) (fun hm => hv x.1 (hPW hm))
      (fun W' hW' => (Set.mem_singleton_iff.mp hW') ▸ hv x.1)
  have : Algebra.FiniteType F e.range :=
    Algebra.FiniteType.of_surjective e.rangeRestrict e.rangeRestrict_surjective
  have _ : IsNoetherianRing e.range := Algebra.FiniteType.isNoetherianRing F e.range
  let _ : Algebra e.range (degZeroLoc P {W}) := (Subalgebra.inclusion hle).toAlgebra
  let M : Submonoid e.range :=
    (IsUnit.submonoid (degZeroLoc P {W})).comap (algebraMap e.range (degZeroLoc P {W}))
  have hloc : IsLocalization M (degZeroLoc P {W}) := by
    rw [isLocalization_iff]
    refine ⟨fun y => y.2, fun z => ?_,
      fun {x y} hxy => ⟨1, by rw [Subalgebra.inclusion_injective hle hxy]⟩⟩
    obtain ⟨b, f, g, hf, hg, hgP, hgW, hz⟩ := h F K ι P {W}
      (fun W' hW' => (Set.mem_singleton_iff.mp hW') ▸ hW.isPrime) z.1 z.2
    have hgW' : g ∉ W := hgW W rfl
    have hcb : φ (c b) ≠ 0 := hφ _ fun hm => hcW b (hPW hm)
    have hz' : (z : FractionRing (MRing ι F ⧸ P)) = φ f / φ g := hz
    have heg : e g ≠ 0 := by
      intro h0
      apply hφ g hgP
      rw [hhom b g hg, h0, zero_mul]
    have hinv : (e g)⁻¹ ∈ degZeroLoc P {W} := by
      have hq : (e g)⁻¹ = φ (c b) / φ g := by
        rw [hhom b g hg]
        field_simp
      rw [hq]
      exact div_mem_degZeroLoc P {W} (hc b) hg hgP
        (fun W' hW' => (Set.mem_singleton_iff.mp hW') ▸ hgW')
    have hunit : (⟨e g, g, rfl⟩ : e.range) ∈ M :=
      isUnit_iff_exists_inv.mpr ⟨⟨(e g)⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ heg)⟩
    refine ⟨(⟨e f, f, rfl⟩, ⟨⟨e g, g, rfl⟩, hunit⟩), Subtype.ext ?_⟩
    change (z : FractionRing (MRing ι F ⧸ P)) * e g = e f
    rw [hz', hhom b f hf, hhom b g hg]
    field_simp
  exact IsLocalization.isNoetherianRing M _ inferInstance

end

end GroundTheory.Heights₂.Heights.FieldNumbers
