import Formalism.SatakeDualWeyl.Statement
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.GlintPrincRelIndexNeZero
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Stabstd

noncomputable section
namespace Formalism.UG.P
open Formalism.UG IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped WithZero TensorProduct

section Adele

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Rewrite using `[algebraMap_adicCompletion]`. Conclude with `adicCompletion.valued_coe (K := F) (v := v) _`.
-/
theorem levelaf_valued_algebraMap (v : HeightOneSpectrum (𝓞 F)) (a : F) :
    Valued.v (algebraMap F (v.adicCompletion F) a) = v.valuation F a := by
  rw [algebraMap_adicCompletion]; exact adicCompletion.valued_coe (K := F) (v := v) _

/- English proof (translation)
Rewrite using `[mem_adicCompletionIntegers, IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F), levelaf_valued_algebraMap, valuation_of_algebraMap]`. Conclude with `intValuation_le_one v r`.
-/
theorem levelaf_int_mem_v (v : HeightOneSpectrum (𝓞 F)) (r : 𝓞 F) :
    algebraMap (𝓞 F) (v.adicCompletion F) r ∈ v.adicCompletionIntegers F := by
  rw [mem_adicCompletionIntegers, IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F),
    levelaf_valued_algebraMap, valuation_of_algebraMap]
  exact intValuation_le_one v r

/- English proof (translation)
Establish `hs : {y : v.adicCompletion F | Valued.v (y - x) < 1} ∈ nhds x` using `Valued.mem_nhds.2 ⟨1, fun y hy => by simpa [Valuation.restrict_lt_one_iff] using hy⟩`. Take `⟨a, ha⟩` from `(denseRange_algebraMap (K := F) v).mem_nhds hs`. Simplify using `only [Set.mem_ofPred_eq] at ha`. Take `⟨⟨num, den⟩, hnd⟩` from `IsLocalization.surj (nonZeroDivisors (𝓞 F)) a`. Use `⟨(den : 𝓞 F), nonZeroDivisors.ne_zero den.2, ?_⟩` and prove the remaining obligations.

Establish `h1 : algebraMap (𝓞 F) (v.adicCompletion F) num = algebraMap F (v.adicCompletion F) a * algebraMap (𝓞 F) (v.adicCompletion F) (den : 𝓞 F)`. Rewrite using `[IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F) num, ← hnd, map_mul, ← IsScalarTower.algebraMap_apply]`. Establish `e : algebraMap (𝓞 F) (v.adicCompletion F) (den : 𝓞 F) * x = algebraMap (𝓞 F) (v.adicCompletion F) num - algebraMap (𝓞 F) (v.adicCompletion F) (den : 𝓞 F) * (algebraMap F _ a - x)`. Rewrite using `[h1]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Use `sub_mem (levelaf_int_mem_v v _) (mul_mem (levelaf_int_mem_v v _) ?_)` and prove the remaining obligations. Rewrite using `[mem_adicCompletionIntegers]`. Conclude with `ha.le`.
-/
theorem levelaf_local_denom (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ algebraMap (𝓞 F) (v.adicCompletion F) d * x ∈ v.adicCompletionIntegers F := by
  have hs : {y : v.adicCompletion F | Valued.v (y - x) < 1} ∈ nhds x :=
    Valued.mem_nhds.2 ⟨1, fun y hy => by simpa [Valuation.restrict_lt_one_iff] using hy⟩
  obtain ⟨a, ha⟩ := (denseRange_algebraMap (K := F) v).mem_nhds hs
  simp only [Set.mem_ofPred_eq] at ha
  obtain ⟨⟨num, den⟩, hnd⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 F)) a
  refine ⟨(den : 𝓞 F), nonZeroDivisors.ne_zero den.2, ?_⟩
  have h1 : algebraMap (𝓞 F) (v.adicCompletion F) num =
      algebraMap F (v.adicCompletion F) a * algebraMap (𝓞 F) (v.adicCompletion F) (den : 𝓞 F) := by
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F) num, ← hnd, map_mul,
      ← IsScalarTower.algebraMap_apply]
  have e : algebraMap (𝓞 F) (v.adicCompletion F) (den : 𝓞 F) * x =
      algebraMap (𝓞 F) (v.adicCompletion F) num -
        algebraMap (𝓞 F) (v.adicCompletion F) (den : 𝓞 F) * (algebraMap F _ a - x) := by
    rw [h1]; ring
  rw [e]
  refine sub_mem (levelaf_int_mem_v v _) (mul_mem (levelaf_int_mem_v v _) ?_)
  rw [mem_adicCompletionIntegers]; exact ha.le

/- English proof (translation)
Introduce `v` and use `levelaf_int_mem_v v r`.
-/
theorem levelaf_int_mem (r : 𝓞 F) : algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) r ∈ intAd F :=
  fun v => levelaf_int_mem_v v r

/- English proof (translation)
Establish `hP : {v : HeightOneSpectrum (𝓞 F) | a v ∉ v.adicCompletionIntegers F}.Finite` using `Filter.eventually_cofinite.1 a.2`. Use `choose d hd0 hd using fun v : HeightOneSpectrum (𝓞 F) => levelaf_local_denom v (a v)`. Use `⟨∏ v ∈ hP.toFinset, d v, Finset.prod_ne_zero_iff.2 fun v _ => hd0 v, fun w => ?_⟩` and prove the remaining obligations. Use `show algebraMap (𝓞 F) (w.adicCompletion F) (∏ v ∈ hP.toFinset, d v) * a w ∈ _`. Distinguish the cases in `hw : w ∈ hP.toFinset`.

Rewrite using `[← Finset.mul_prod_erase _ _ hw, map_mul, mul_comm (algebraMap _ _ (d w)), mul_assoc]`. Conclude with `mul_mem (levelaf_int_mem_v w _) (hd w)`. Establish `: a w ∈ w.adicCompletionIntegers F` using `by simpa using hw`. Conclude with `mul_mem (levelaf_int_mem_v w _) this`.
-/
theorem levelaf_adele_denom (a : FiniteAdeleRing (𝓞 F) F) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) d * a ∈ intAd F := by
  classical
  have hP : {v : HeightOneSpectrum (𝓞 F) | a v ∉ v.adicCompletionIntegers F}.Finite :=
    Filter.eventually_cofinite.1 a.2
  choose d hd0 hd using fun v : HeightOneSpectrum (𝓞 F) => levelaf_local_denom v (a v)
  refine ⟨∏ v ∈ hP.toFinset, d v, Finset.prod_ne_zero_iff.2 fun v _ => hd0 v, fun w => ?_⟩
  show algebraMap (𝓞 F) (w.adicCompletion F) (∏ v ∈ hP.toFinset, d v) * a w ∈ _
  by_cases hw : w ∈ hP.toFinset
  · rw [← Finset.mul_prod_erase _ _ hw, map_mul, mul_comm (algebraMap _ _ (d w)), mul_assoc]
    exact mul_mem (levelaf_int_mem_v w _) (hd w)
  · have : a w ∈ w.adicCompletionIntegers F := by simpa using hw
    exact mul_mem (levelaf_int_mem_v w _) this

end Adele

section AdeleRes

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Establish `: ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D) = v.valuation F (algebraMap (𝓞 F) F D)` using `fun v => by`. Rewrite using `[IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F), levelaf_valued_algebraMap]`. Repeatedly rewrite using `[this, valuation_lt_one_iff_dvd]`. Apply `Ideal.finite_factors` to reduce the goal to its premises. Simplify using `only [Submodule.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot]`.
-/
theorem levelaf_finite_places (D : 𝓞 F) (hD : D ≠ 0) :
    {v : HeightOneSpectrum (𝓞 F) | Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D) < 1}.Finite := by
  have : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D) =
      v.valuation F (algebraMap (𝓞 F) F D) := fun v => by
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F), levelaf_valued_algebraMap]
  simp_rw [this, valuation_lt_one_iff_dvd]
  apply Ideal.finite_factors
  simpa only [Submodule.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot]

/- English proof (translation)
Introduce `h'`. Rewrite `h'` using `[IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F), map_eq_zero_iff _ (algebraMap F _).injective, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)]`. Conclude with `hD h'`.
-/
theorem levelaf_algebraMap_ne_zero (v : HeightOneSpectrum (𝓞 F)) (D : 𝓞 F) (hD : D ≠ 0) :
    algebraMap (𝓞 F) (v.adicCompletion F) D ≠ 0 := by
  intro h'
  rw [IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F),
    map_eq_zero_iff _ (algebraMap F _).injective,
    map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)] at h'
  exact hD h'

/- English proof (translation)
Use `set P := {v : HeightOneSpectrum (𝓞 F) | Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D) < 1} with hPdef`. Establish `hP : P.Finite` using `levelaf_finite_places D hD`. Establish `: Finite P` using `hP.to_subtype`. Set `Dv : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F` to `fun v => ⟨_, levelaf_int_mem_v v D⟩`. Establish `hDv0 : ∀ v, Dv v ≠ 0`.

Introduce `v h`. Conclude with `levelaf_algebraMap_ne_zero v D hD (congrArg Subtype.val h)`. Establish `: ∀ v : P, Finite ((v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F ⧸ Ideal.span {Dv v})` using `fun v => glint_finite_quotient_of_dvr (glint_finite_residueField (v : HeightOneSpectrum (𝓞 F))) _ (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hDv0 v)`. Set `φ : intAd F → ∀ v : P, (v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F ⧸ Ideal.span {Dv v}` to `fun a v => Ideal.Quotient.mk _ ⟨(a : FiniteAdeleRing (𝓞 F) F) v, a.2 v⟩`. Establish `key : ∀ a a' : intAd F, φ a = φ a' → ∃ y ∈ intAd F, (a : FiniteAdeleRing (𝓞 F) F) = a' + algebraMap (𝓞 F) _ D * y`.

Introduce `a a' h`. Establish `hle : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v ((a : FiniteAdeleRing (𝓞 F) F) v - (a' : FiniteAdeleRing (𝓞 F) F) v) ≤ Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D)`. Introduce `v`. Distinguish the cases in `hv : v ∈ P`. Use `congrFun h ⟨v, hv⟩` as an intermediate fact.

Simplify using `only [φ] at this`. Rewrite `this` using `[Ideal.Quotient.eq, Ideal.mem_span_singleton']`. Take `⟨z, hz⟩` from `this`. Establish `hz'` using `congrArg Subtype.val hz`. Simplify using `only [MulMemClass.coe_mul, AddSubgroupClass.coe_sub, Dv] at hz'`.

Rewrite using `[← hz', Valuation.map_mul]`. Combine the equalities or inequalities in the displayed calculation. Establish `h1 : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D) = 1` using `le_antisymm ((mem_adicCompletionIntegers _ _ _).1 (levelaf_int_mem_v v D)) (not_lt.1 hv)`. Rewrite using `[h1]`. Conclude with `(mem_adicCompletionIntegers _ _ _).1 (sub_mem (a.2 v) (a'.2 v))`.

Use `set y : FiniteAdeleRing (𝓞 F) F := algebraMap F _ (algebraMap (𝓞 F) F D)⁻¹ * ((a : FiniteAdeleRing (𝓞 F) F) - a') with hy`. Use `⟨y, fun v => ?_, ?_⟩` and prove the remaining obligations. Use `show algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F D)⁻¹ * ((a : FiniteAdeleRing (𝓞 F) F) v - (a' : FiniteAdeleRing (𝓞 F) F) v) ∈ _`. Establish `hne : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D) ≠ 0` using `(Valuation.ne_zero_iff _).2 (levelaf_algebraMap_ne_zero v D hD)`. Rewrite using `[mem_adicCompletionIntegers, Valuation.map_mul, map_inv₀, map_inv₀, ← IsScalarTower.algebraMap_apply]`.

Combine the equalities or inequalities in the displayed calculation. Establish `hD' : algebraMap (𝓞 F) F D ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hD`. Rewrite using `[hy, IsScalarTower.algebraMap_apply (𝓞 F) F (FiniteAdeleRing (𝓞 F) F), ← mul_assoc, ← map_mul, mul_inv_cancel₀ hD', map_one, one_mul]`. Expand and normalize the polynomial expressions, which then agree. Set `rep : (∀ v : P, (v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F ⧸ Ideal.span {Dv v}) → intAd F` to `fun q => if h : ∃ a, φ a = q then h.choose else 0`.

Use `⟨Set.range (fun q => ((rep q : intAd F) : FiniteAdeleRing (𝓞 F) F)), Set.finite_range _, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨q, rfl⟩`. Conclude with `(rep q).2`. Introduce `a ha`. Establish `hex : ∃ b, φ b = φ ⟨a, ha⟩` using `⟨_, rfl⟩`.

Establish `hrep : φ (rep (φ ⟨a, ha⟩)) = φ ⟨a, ha⟩`. Simplify using `only [rep, dif_pos hex]`. Conclude with `hex.choose_spec`. Take `⟨y, hy, e⟩` from `key ⟨a, ha⟩ _ hrep.symm`. Conclude with `⟨_, ⟨_, rfl⟩, y, hy, e⟩`.
-/
theorem levelaf_adele_res (D : 𝓞 F) (hD : D ≠ 0) :
    ∃ T : Set (FiniteAdeleRing (𝓞 F) F), T.Finite ∧ T ⊆ intAd F ∧
      ∀ a ∈ intAd F, ∃ t ∈ T, ∃ y ∈ intAd F, a = t + algebraMap (𝓞 F) _ D * y := by
  classical
  set P := {v : HeightOneSpectrum (𝓞 F) | Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D) < 1}
    with hPdef
  have hP : P.Finite := levelaf_finite_places D hD
  have : Finite P := hP.to_subtype
  let Dv : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F :=
    fun v => ⟨_, levelaf_int_mem_v v D⟩
  have hDv0 : ∀ v, Dv v ≠ 0 := by
    intro v h
    exact levelaf_algebraMap_ne_zero v D hD (congrArg Subtype.val h)
  have : ∀ v : P, Finite ((v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F ⧸
      Ideal.span {Dv v}) := fun v =>
    glint_finite_quotient_of_dvr (glint_finite_residueField (v : HeightOneSpectrum (𝓞 F))) _
      (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hDv0 v)
  let φ : intAd F → ∀ v : P, (v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F ⧸
      Ideal.span {Dv v} :=
    fun a v => Ideal.Quotient.mk _ ⟨(a : FiniteAdeleRing (𝓞 F) F) v, a.2 v⟩
  have key : ∀ a a' : intAd F, φ a = φ a' → ∃ y ∈ intAd F,
      (a : FiniteAdeleRing (𝓞 F) F) = a' + algebraMap (𝓞 F) _ D * y := by
    intro a a' h
    have hle : ∀ v : HeightOneSpectrum (𝓞 F),
        Valued.v ((a : FiniteAdeleRing (𝓞 F) F) v - (a' : FiniteAdeleRing (𝓞 F) F) v) ≤
          Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D) := by
      intro v
      by_cases hv : v ∈ P
      · have := congrFun h ⟨v, hv⟩
        simp only [φ] at this
        rw [Ideal.Quotient.eq, Ideal.mem_span_singleton'] at this
        obtain ⟨z, hz⟩ := this
        have hz' := congrArg Subtype.val hz
        simp only [MulMemClass.coe_mul, AddSubgroupClass.coe_sub, Dv] at hz'
        rw [← hz', Valuation.map_mul]
        calc _ ≤ 1 * Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D) :=
              mul_le_mul_left ((mem_adicCompletionIntegers _ _ _).1 z.2) _
          _ = _ := one_mul _
      · have h1 : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D) = 1 :=
          le_antisymm ((mem_adicCompletionIntegers _ _ _).1 (levelaf_int_mem_v v D)) (not_lt.1 hv)
        rw [h1]
        exact (mem_adicCompletionIntegers _ _ _).1 (sub_mem (a.2 v) (a'.2 v))
    set y : FiniteAdeleRing (𝓞 F) F :=
      algebraMap F _ (algebraMap (𝓞 F) F D)⁻¹ * ((a : FiniteAdeleRing (𝓞 F) F) - a') with hy
    refine ⟨y, fun v => ?_, ?_⟩
    · show algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F D)⁻¹ *
          ((a : FiniteAdeleRing (𝓞 F) F) v - (a' : FiniteAdeleRing (𝓞 F) F) v) ∈ _
      have hne : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D) ≠ 0 :=
        (Valuation.ne_zero_iff _).2 (levelaf_algebraMap_ne_zero v D hD)
      rw [mem_adicCompletionIntegers, Valuation.map_mul, map_inv₀, map_inv₀,
        ← IsScalarTower.algebraMap_apply]
      calc _ ≤ (Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D))⁻¹ *
            Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D) := mul_le_mul_right (hle v) _
        _ = 1 := inv_mul_cancel₀ hne
    · have hD' : algebraMap (𝓞 F) F D ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hD
      rw [hy, IsScalarTower.algebraMap_apply (𝓞 F) F (FiniteAdeleRing (𝓞 F) F), ← mul_assoc,
        ← map_mul, mul_inv_cancel₀ hD', map_one, one_mul]
      ring
  let rep : (∀ v : P, (v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F ⧸
      Ideal.span {Dv v}) → intAd F := fun q => if h : ∃ a, φ a = q then h.choose else 0
  refine ⟨Set.range (fun q => ((rep q : intAd F) : FiniteAdeleRing (𝓞 F) F)), Set.finite_range _,
    ?_, ?_⟩
  · rintro _ ⟨q, rfl⟩; exact (rep q).2
  · intro a ha
    have hex : ∃ b, φ b = φ ⟨a, ha⟩ := ⟨_, rfl⟩
    have hrep : φ (rep (φ ⟨a, ha⟩)) = φ ⟨a, ha⟩ := by
      simp only [rep, dif_pos hex]; exact hex.choose_spec
    obtain ⟨y, hy, e⟩ := key ⟨a, ha⟩ _ hrep.symm
    exact ⟨_, ⟨_, rfl⟩, y, hy, e⟩

end AdeleRes

section Tensor

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)

variable (E) in

def levelafC (d : 𝓞 F) : E ⊗[F] FiniteAdeleRing (𝓞 F) F :=
  (1 : E) ⊗ₜ[F] algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) d

/- English proof (translation)
Establish `: algebraMap (𝓞 E) E e ⊗ₜ[F] y = (algebraMap (𝓞 E) E e ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) * ((1 : E) ⊗ₜ[F] y)`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]`. Rewrite using `[this]`. Conclude with `mul_mem (Subring.subset_closure (Or.inl ⟨⟨_, ⟨e, rfl⟩⟩, rfl⟩)) (Subring.subset_closure (Or.inr ⟨⟨y, hy⟩, rfl⟩))`.
-/
theorem levelaf_tmul_mem (e : 𝓞 E) {y : FiniteAdeleRing (𝓞 F) F} (hy : y ∈ intAd F) :
    algebraMap (𝓞 E) E e ⊗ₜ[F] y ∈ 𝒮 := by
  have : algebraMap (𝓞 E) E e ⊗ₜ[F] y =
      (algebraMap (𝓞 E) E e ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) * ((1 : E) ⊗ₜ[F] y) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [this]
  exact mul_mem (Subring.subset_closure (Or.inl ⟨⟨_, ⟨e, rfl⟩⟩, rfl⟩))
    (Subring.subset_closure (Or.inr ⟨⟨y, hy⟩, rfl⟩))

/- English proof (translation)
Use `levelaf_tmul_mem (E := E) 1 (levelaf_int_mem d)` as an intermediate fact. Rewrite `this` using `[map_one]`. Then use the resulting hypothesis.
-/
theorem levelafC_mem (d : 𝓞 F) : levelafC E d ∈ 𝒮 := by
  have := levelaf_tmul_mem (E := E) 1 (levelaf_int_mem d)
  rwa [map_one] at this

/- English proof (translation)
Simplify using `only [levelafC, Algebra.TensorProduct.tmul_mul_tmul, one_mul, map_mul]`.
-/
theorem levelafC_mul (a b : 𝓞 F) : levelafC E (a * b) = levelafC E a * levelafC E b := by
  simp only [levelafC, Algebra.TensorProduct.tmul_mul_tmul, one_mul, map_mul]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨1, one_ne_zero, by rw [mul_zero]; exact zero_mem _⟩`. Consider the case `tmul e a`. Establish `halg : Algebra.IsAlgebraic ℤ E` using `(IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ)).2 inferInstance`. Take `⟨m, hm0, hm⟩` from `(halg.1 e).exists_integral_multiple`.

Take `⟨d, hd0, hd⟩` from `levelaf_adele_denom a`. Use `⟨(m : 𝓞 F) * d, mul_ne_zero (Int.cast_ne_zero.2 hm0) hd0, ?_⟩` and prove the remaining obligations. Establish `e1 : levelafC E ((m : 𝓞 F) * d) * (e ⊗ₜ a) = algebraMap (𝓞 E) E ⟨m • e, hm⟩ ⊗ₜ[F] (algebraMap (𝓞 F) _ d * a)`. Simplify using `only [levelafC, Algebra.TensorProduct.tmul_mul_tmul, one_mul, map_mul, map_intCast]`. Rewrite using `[show algebraMap (𝓞 E) E ⟨m • e, hm⟩ = m • e from rfl, TensorProduct.smul_tmul, zsmul_eq_mul, mul_assoc]`.

Rewrite using `[e1]`. Conclude with `levelaf_tmul_mem _ hd`. Consider the case `add x y hx hy`. Take `⟨dx, hx0, hx⟩` from `hx`. Take `⟨dy, hy0, hy⟩` from `hy`.

Use `⟨dx * dy, mul_ne_zero hx0 hy0, ?_⟩` and prove the remaining obligations. Establish `: levelafC E (dx * dy) * (x + y) = levelafC E dy * (levelafC E dx * x) + levelafC E dx * (levelafC E dy * y)`. Rewrite using `[levelafC_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`.

Conclude with `add_mem (mul_mem (levelafC_mem _) hx) (mul_mem (levelafC_mem _) hy)`.
-/
theorem levelaf_denom (x : 𝒜) : ∃ d : 𝓞 F, d ≠ 0 ∧ levelafC E d * x ∈ 𝒮 := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨1, one_ne_zero, by rw [mul_zero]; exact zero_mem _⟩
  | tmul e a =>
    have halg : Algebra.IsAlgebraic ℤ E :=
      (IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ)).2 inferInstance
    obtain ⟨m, hm0, hm⟩ := (halg.1 e).exists_integral_multiple
    obtain ⟨d, hd0, hd⟩ := levelaf_adele_denom a
    refine ⟨(m : 𝓞 F) * d, mul_ne_zero (Int.cast_ne_zero.2 hm0) hd0, ?_⟩
    have e1 : levelafC E ((m : 𝓞 F) * d) * (e ⊗ₜ a) =
        algebraMap (𝓞 E) E ⟨m • e, hm⟩ ⊗ₜ[F] (algebraMap (𝓞 F) _ d * a) := by
      simp only [levelafC, Algebra.TensorProduct.tmul_mul_tmul, one_mul, map_mul, map_intCast]
      rw [show algebraMap (𝓞 E) E ⟨m • e, hm⟩ = m • e from rfl, TensorProduct.smul_tmul,
        zsmul_eq_mul, mul_assoc]
    rw [e1]; exact levelaf_tmul_mem _ hd
  | add x y hx hy =>
    obtain ⟨dx, hx0, hx⟩ := hx
    obtain ⟨dy, hy0, hy⟩ := hy
    refine ⟨dx * dy, mul_ne_zero hx0 hy0, ?_⟩
    have : levelafC E (dx * dy) * (x + y) =
        levelafC E dy * (levelafC E dx * x) + levelafC E dx * (levelafC E dy * y) := by
      rw [levelafC_mul]; ring
    rw [this]
    exact add_mem (mul_mem (levelafC_mem _) hx) (mul_mem (levelafC_mem _) hy)

def levelafQ {m : ℕ} (b : Fin m → 𝓞 E) (s : 𝒜) : Prop :=
  ∃ r : Fin m → FiniteAdeleRing (𝓞 F) F, (∀ j, r j ∈ intAd F) ∧
    s = ∑ j, algebraMap (𝓞 E) E (b j) ⊗ₜ[F] r j

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, fun _ => zero_mem _, by simp⟩`.
-/
theorem levelafQ_zero {m : ℕ} (b : Fin m → 𝓞 E) : levelafQ (F := F) b 0 :=
  ⟨0, fun _ => zero_mem _, by simp⟩

/- English proof (translation)
Take `⟨r, hr, rfl⟩` from `hx`. Take `⟨r', hr', rfl⟩` from `hy`. Use `⟨r + r', fun j => add_mem (hr j) (hr' j), ?_⟩` and prove the remaining obligations. Rewrite using `[← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun j _ => (TensorProduct.tmul_add _ _ _).symm`.
-/
theorem levelafQ_add {m : ℕ} (b : Fin m → 𝓞 E) {x y : 𝒜} (hx : levelafQ b x) (hy : levelafQ b y) :
    levelafQ b (x + y) := by
  obtain ⟨r, hr, rfl⟩ := hx
  obtain ⟨r', hr', rfl⟩ := hy
  refine ⟨r + r', fun j => add_mem (hr j) (hr' j), ?_⟩
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => (TensorProduct.tmul_add _ _ _).symm

/- English proof (translation)
Take `⟨r, hr, rfl⟩` from `hx`. Use `⟨-r, fun j => neg_mem (hr j), ?_⟩` and prove the remaining obligations. Rewrite using `[← Finset.sum_neg_distrib]`. Conclude with `Finset.sum_congr rfl fun j _ => (TensorProduct.tmul_neg _ _).symm`.
-/
theorem levelafQ_neg {m : ℕ} (b : Fin m → 𝓞 E) {x : 𝒜} (hx : levelafQ b x) :
    levelafQ b (-x) := by
  obtain ⟨r, hr, rfl⟩ := hx
  refine ⟨-r, fun j => neg_mem (hr j), ?_⟩
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ => (TensorProduct.tmul_neg _ _).symm

/- English proof (translation)
The claim follows from `Finset.sum_induction f (levelafQ b) (fun _ _ hx hy => levelafQ_add b hx hy) (levelafQ_zero b) h`.
-/
theorem levelafQ_sum {m : ℕ} (b : Fin m → 𝓞 E) {ι : Type} (s : Finset ι) (f : ι → 𝒜)
    (h : ∀ i ∈ s, levelafQ b (f i)) : levelafQ b (∑ i ∈ s, f i) :=
  Finset.sum_induction f (levelafQ b) (fun _ _ hx hy => levelafQ_add b hx hy) (levelafQ_zero b) h

/- English proof (translation)
Establish `he : e ∈ Submodule.span ℤ (Set.range b)` using `by rw [hb]; exact Submodule.mem_top`. Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun ℤ).1 he`. Use `⟨fun j => c j • y, fun j => zsmul_mem hy _, ?_⟩` and prove the remaining obligations. Rewrite using `[← hc, map_sum, TensorProduct.sum_tmul]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[map_zsmul, TensorProduct.smul_tmul]`.
-/
theorem levelafQ_tmul {m : ℕ} (b : Fin m → 𝓞 E) (hb : Submodule.span ℤ (Set.range b) = ⊤)
    (e : 𝓞 E) {y : FiniteAdeleRing (𝓞 F) F} (hy : y ∈ intAd F) :
    levelafQ b (algebraMap (𝓞 E) E e ⊗ₜ[F] y) := by
  have he : e ∈ Submodule.span ℤ (Set.range b) := by rw [hb]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 he
  refine ⟨fun j => c j • y, fun j => zsmul_mem hy _, ?_⟩
  rw [← hc, map_sum, TensorProduct.sum_tmul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, TensorProduct.smul_tmul]

/- English proof (translation)
Take `⟨r, hr, rfl⟩` from `hx`. Take `⟨r', hr', rfl⟩` from `hy`. Rewrite using `[Finset.sum_mul_sum]`. Use `levelafQ_sum b _ _ fun j _ => levelafQ_sum b _ _ fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, ← map_mul]`.

Conclude with `levelafQ_tmul b hb _ (mul_mem (hr j) (hr' k))`.
-/
theorem levelafQ_mul {m : ℕ} (b : Fin m → 𝓞 E) (hb : Submodule.span ℤ (Set.range b) = ⊤)
    {x y : 𝒜} (hx : levelafQ b x) (hy : levelafQ b y) : levelafQ b (x * y) := by
  obtain ⟨r, hr, rfl⟩ := hx
  obtain ⟨r', hr', rfl⟩ := hy
  rw [Finset.sum_mul_sum]
  refine levelafQ_sum b _ _ fun j _ => levelafQ_sum b _ _ fun k _ => ?_
  rw [Algebra.TensorProduct.tmul_mul_tmul, ← map_mul]
  exact levelafQ_tmul b hb _ (mul_mem (hr j) (hr' k))

/- English proof (translation)
Use `Subring.closure_induction (p := fun s _ => levelafQ b s) ?_ ?_ ?_ ?_ ?_ ?_ hs` and prove the remaining obligations. Introduce and unpack `x (⟨⟨e, ⟨e', rfl⟩⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)`. Conclude with `levelafQ_tmul b hb e' (one_mem _)`. Use `levelafQ_tmul b hb 1 hy` as an intermediate fact. Rewrite `this` using `[map_one]`. Then use the resulting hypothesis.

Conclude with `levelafQ_zero b`. Use `levelafQ_tmul b hb 1 (one_mem (intAd F))` as an intermediate fact. Rewrite `this` using `[map_one, ← Algebra.TensorProduct.one_def]`. Then use the resulting hypothesis. Introduce `x y _ _ hx hy`. Conclude with `levelafQ_add b hx hy`.

Introduce `x _ hx`. Conclude with `levelafQ_neg b hx`. Introduce `x y _ _ hx hy`. Conclude with `levelafQ_mul b hb hx hy`.
-/
theorem levelaf_decomp {m : ℕ} (b : Fin m → 𝓞 E) (hb : Submodule.span ℤ (Set.range b) = ⊤)
    {s : 𝒜} (hs : s ∈ 𝒮) : levelafQ b s := by
  refine Subring.closure_induction (p := fun s _ => levelafQ b s) ?_ ?_ ?_ ?_ ?_ ?_ hs
  · rintro x (⟨⟨e, ⟨e', rfl⟩⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
    · exact levelafQ_tmul b hb e' (one_mem _)
    · have := levelafQ_tmul b hb 1 hy
      rwa [map_one] at this
  · exact levelafQ_zero b
  · have := levelafQ_tmul b hb 1 (one_mem (intAd F))
    rwa [map_one, ← Algebra.TensorProduct.one_def] at this
  · intro x y _ _ hx hy; exact levelafQ_add b hx hy
  · intro x _ hx; exact levelafQ_neg b hx
  · intro x y _ _ hx hy; exact levelafQ_mul b hb hx hy

end Tensor

section Quot

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)

/- English proof (translation)
Take `⟨m, b, hb⟩` from `Module.Finite.exists_fin (R := ℤ) (M := 𝓞 E)`. Take `⟨T, hT, hTsub, hTres⟩` from `levelaf_adele_res D hD`. Establish `: Finite T` using `hT.to_subtype`. Set `ψ : (Fin m → T) → 𝒮 ⧸ Ideal.span {c}` to `fun t => Ideal.Quotient.mk _ ⟨∑ j, algebraMap (𝓞 E) E (b j) ⊗ₜ[F] ((t j : T) : FiniteAdeleRing (𝓞 F) F), sum_mem fun j _ => levelaf_tmul_mem _ (hTsub (t j).2)⟩`. Use `Finite.of_surjective ψ ?_` and prove the remaining obligations.

Introduce `q`. Take `⟨s, rfl⟩` from `Ideal.Quotient.mk_surjective q`. Take `⟨r, hr, hs⟩` from `levelaf_decomp b hb s.2`. Use `choose t ht y hy hty using fun j => hTres (r j) (hr j)`. Use `⟨fun j => ⟨t j, ht j⟩, ?_⟩` and prove the remaining obligations.

Simplify using `only [ψ]`. Rewrite using `[Ideal.Quotient.eq, Ideal.mem_span_singleton']`. Use `⟨⟨-∑ j, algebraMap (𝓞 E) E (b j) ⊗ₜ[F] y j, neg_mem (sum_mem fun j _ => levelaf_tmul_mem _ (hy j))⟩, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [MulMemClass.coe_mul, AddSubgroupClass.coe_sub, hc]`.

Rewrite using `[hs]`. Simplify using `only [hty, TensorProduct.tmul_add, Finset.sum_add_distrib, levelafC, Finset.sum_mul, neg_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]`. Simplify using `only [mul_comm (y _)]`. Normalize the expressions using the abelian group laws.
-/
theorem levelaf_finite_quot (D : 𝓞 F) (hD : D ≠ 0) (c : 𝒮) (hc : (c : 𝒜) = levelafC E D) :
    Finite (𝒮 ⧸ Ideal.span {c}) := by
  classical
  obtain ⟨m, b, hb⟩ := Module.Finite.exists_fin (R := ℤ) (M := 𝓞 E)
  obtain ⟨T, hT, hTsub, hTres⟩ := levelaf_adele_res D hD
  have : Finite T := hT.to_subtype
  let ψ : (Fin m → T) → 𝒮 ⧸ Ideal.span {c} := fun t => Ideal.Quotient.mk _
    ⟨∑ j, algebraMap (𝓞 E) E (b j) ⊗ₜ[F] ((t j : T) : FiniteAdeleRing (𝓞 F) F),
      sum_mem fun j _ => levelaf_tmul_mem _ (hTsub (t j).2)⟩
  refine Finite.of_surjective ψ ?_
  intro q
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨r, hr, hs⟩ := levelaf_decomp b hb s.2
  choose t ht y hy hty using fun j => hTres (r j) (hr j)
  refine ⟨fun j => ⟨t j, ht j⟩, ?_⟩
  simp only [ψ]
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton']
  refine ⟨⟨-∑ j, algebraMap (𝓞 E) E (b j) ⊗ₜ[F] y j,
    neg_mem (sum_mem fun j _ => levelaf_tmul_mem _ (hy j))⟩, ?_⟩
  apply Subtype.ext
  simp only [MulMemClass.coe_mul, AddSubgroupClass.coe_sub, hc]
  rw [hs]
  simp only [hty, TensorProduct.tmul_add, Finset.sum_add_distrib, levelafC, Finset.sum_mul,
    neg_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  simp only [mul_comm (y _)]
  abel

end Quot

section Generic

variable {L : Type} [CommRing L] {n : Type} [Fintype n] [DecidableEq n]

/- English proof (translation)
Take `⟨A, hA⟩` from `h1`. Take `⟨B, hB⟩` from `h2`. Establish `inj : Function.Injective (RingHom.mapMatrix (m` using `n) O.subtype) := by`. Introduce `X Y h`. Use extensionality with `i j`.

Simplify using `using congrFun (congrFun h i) j`. Establish `hAB : A * B = 1` using `inj (by rw [map_mul, map_one, hA, hB, Units.mul_inv])`. Establish `hBA : B * A = 1` using `inj (by rw [map_mul, map_one, hA, hB, Units.inv_mul])`. Use `⟨⟨A, B, hAB, hBA⟩, ?_⟩` and prove the remaining obligations. Use extensionality with `: 1`.

Simplify using `only [bc, Units.coe_map]`. Conclude with `hA`.
-/
theorem levelaf_mem_range_of_integral (O : Subring L) (U : GL n L)
    (h1 : (U : Matrix n n L) ∈ (RingHom.mapMatrix (m := n) O.subtype).range)
    (h2 : ((U⁻¹ : GL n L) : Matrix n n L) ∈ (RingHom.mapMatrix (m := n) O.subtype).range) :
    U ∈ (bc (n := n) O.subtype).range := by
  obtain ⟨A, hA⟩ := h1
  obtain ⟨B, hB⟩ := h2
  have inj : Function.Injective (RingHom.mapMatrix (m := n) O.subtype) := by
    intro X Y h
    ext i j
    simpa using congrFun (congrFun h i) j
  have hAB : A * B = 1 := inj (by rw [map_mul, map_one, hA, hB, Units.mul_inv])
  have hBA : B * A = 1 := inj (by rw [map_mul, map_one, hA, hB, Units.inv_mul])
  refine ⟨⟨A, B, hAB, hBA⟩, ?_⟩
  ext : 1
  simp only [bc, Units.coe_map]
  exact hA

/- English proof (translation)
Establish `hm : RingHom.mapMatrix (m` using `n) (Ideal.Quotient.mk (Ideal.span {c * c})) (h : Matrix n n O) = RingHom.mapMatrix (m := n) (Ideal.Quotient.mk (Ideal.span {c * c})) 1 := by`. Rewrite using `[map_one]`. Conclude with `congrArg Units.val hh`. Establish `hent : ∀ a b, (h : Matrix n n O) a b - (1 : Matrix n n O) a b ∈ Ideal.span {c * c}`. Introduce `a b`.

Rewrite using `[← Ideal.Quotient.eq]`. Simplify `congrFun (congrFun hm a) b` using `only [RingHom.mapMatrix_apply, Matrix.map_apply]`. Use `choose e he using fun a b => Ideal.mem_span_singleton'.1 (hent a b)`. Set `E : Matrix n n O` to `Matrix.of e`. Establish `hL : ∀ a b, (((h : Matrix n n O) a b : O) : L) = (1 : Matrix n n L) a b + (c : L) * (c : L) * ((e a b : O) : L)`.

Introduce `a b`. Establish `h1` using `he a b`. Rewrite `h1`, the goal using `[Matrix.one_apply]`. Use `split_ifs at h1 ⊢ with hab`. Use `congrArg Subtype.val h1` as an intermediate fact.

Move the coercions through the operations in `at this`. Take the linear combination `-this`. Use `congrArg Subtype.val h1` as an intermediate fact. Move the coercions through the operations in `at this`. Take the linear combination `-this`.

Establish `hkey : ((bc (n` using `n) O.subtype h : GL n L) : Matrix n n L) = 1 + ((c : L) * (c : L)) • RingHom.mapMatrix (m := n) O.subtype E := by`. Use extensionality with `a b`. Simplify using `only [bc, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, E, Matrix.of_apply, Subring.coe_subtype]`. Conclude with `hL a b`. Establish `hcalc : ((g⁻¹ * bc (n` using `n) O.subtype h * g : GL n L) : Matrix n n L) = 1 + ((c : L) • ((g⁻¹ : GL n L) : Matrix n n L)) * RingHom.mapMatrix (m := n) O.subtype E * ((c : L) • (g : Matrix n n L)) := by`.

Rewrite using `[Units.val_mul, Units.val_mul, hkey, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, ← Units.val_mul, inv_mul_cancel, Units.val_one]`. Use `congr 1`. Simplify using `only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]`. Rewrite using `[hcalc]`. Conclude with `add_mem (one_mem _) (mul_mem (mul_mem hg' ⟨E, rfl⟩) hg)`.
-/
theorem levelaf_conj_integral (O : Subring L) (g : GL n L) (c : O)
    (hg : (c : L) • (g : Matrix n n L) ∈ (RingHom.mapMatrix (m := n) O.subtype).range)
    (hg' : (c : L) • ((g⁻¹ : GL n L) : Matrix n n L) ∈ (RingHom.mapMatrix (m := n) O.subtype).range)
    (h : GL n O) (hh : redGL (n := n) (Ideal.span {c * c}) h = 1) :
    ((g⁻¹ * bc (n := n) O.subtype h * g : GL n L) : Matrix n n L) ∈
      (RingHom.mapMatrix (m := n) O.subtype).range := by
  have hm : RingHom.mapMatrix (m := n) (Ideal.Quotient.mk (Ideal.span {c * c})) (h : Matrix n n O) =
      RingHom.mapMatrix (m := n) (Ideal.Quotient.mk (Ideal.span {c * c})) 1 := by
    rw [map_one]; exact congrArg Units.val hh
  have hent : ∀ a b, (h : Matrix n n O) a b - (1 : Matrix n n O) a b ∈ Ideal.span {c * c} := by
    intro a b
    rw [← Ideal.Quotient.eq]
    simpa only [RingHom.mapMatrix_apply, Matrix.map_apply] using congrFun (congrFun hm a) b
  choose e he using fun a b => Ideal.mem_span_singleton'.1 (hent a b)
  let E : Matrix n n O := Matrix.of e
  have hL : ∀ a b, (((h : Matrix n n O) a b : O) : L) =
      (1 : Matrix n n L) a b + (c : L) * (c : L) * ((e a b : O) : L) := by
    intro a b
    have h1 := he a b
    rw [Matrix.one_apply] at h1 ⊢
    split_ifs at h1 ⊢ with hab
    · have := congrArg Subtype.val h1
      push_cast at this
      linear_combination -this
    · have := congrArg Subtype.val h1
      push_cast at this
      linear_combination -this
  have hkey : ((bc (n := n) O.subtype h : GL n L) : Matrix n n L) =
      1 + ((c : L) * (c : L)) • RingHom.mapMatrix (m := n) O.subtype E := by
    ext a b
    simp only [bc, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe,
      RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      E, Matrix.of_apply, Subring.coe_subtype]
    exact hL a b
  have hcalc : ((g⁻¹ * bc (n := n) O.subtype h * g : GL n L) : Matrix n n L) =
      1 + ((c : L) • ((g⁻¹ : GL n L) : Matrix n n L)) * RingHom.mapMatrix (m := n) O.subtype E *
        ((c : L) • (g : Matrix n n L)) := by
    rw [Units.val_mul, Units.val_mul, hkey, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
      ← Units.val_mul, inv_mul_cancel, Units.val_one]
    congr 1
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
  rw [hcalc]
  exact add_mem (one_mem _) (mul_mem (mul_mem hg' ⟨E, rfl⟩) hg)

/- English proof (translation)
Introduce `k hk`. Simplify using `only [princ, congPre] at hk`. Take `⟨h, hh, rfl⟩` from `Subgroup.mem_map.1 hk`. Establish `hh' : redGL (n` using `n) (Ideal.span {c * c}) h = 1 := by`. Simplify `hh` using `only [Subgroup.mem_comap, Subgroup.mem_bot]`.

Establish `hh'' : redGL (n` using `n) (Ideal.span {c * c}) h⁻¹ = 1 := by rw [map_inv, hh', inv_one]`. Use `Subgroup.mem_map.2 ⟨g⁻¹ * bc (n := n) O.subtype h * g, ?_, ?_⟩` and prove the remaining obligations. Apply `levelaf_mem_range_of_integral` to reduce the goal to its premises. Conclude with `levelaf_conj_integral O g c hg hg' h hh'`. Establish `: (g⁻¹ * bc (n` using `n) O.subtype h * g)⁻¹ = g⁻¹ * bc (n := n) O.subtype h⁻¹ * g := by`.

Rewrite using `[map_inv]`. Use `group`. Rewrite using `[this]`. Conclude with `levelaf_conj_integral O g c hg hg' h⁻¹ hh''`. Simplify using `[MulAut.conj_apply, mul_assoc]`.
-/
theorem levelaf_princ_le_map_conj (O : Subring L) (g : GL n L) (c : O)
    (hg : (c : L) • (g : Matrix n n L) ∈ (RingHom.mapMatrix (m := n) O.subtype).range)
    (hg' : (c : L) • ((g⁻¹ : GL n L) : Matrix n n L) ∈ (RingHom.mapMatrix (m := n) O.subtype).range) :
    princ (n := n) O.subtype (Ideal.span {c * c}) ≤
      (bc (n := n) O.subtype).range.map (MulAut.conj g).toMonoidHom := by
  intro k hk
  simp only [princ, congPre] at hk
  obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.1 hk
  have hh' : redGL (n := n) (Ideal.span {c * c}) h = 1 := by
    simpa only [Subgroup.mem_comap, Subgroup.mem_bot] using hh
  have hh'' : redGL (n := n) (Ideal.span {c * c}) h⁻¹ = 1 := by rw [map_inv, hh', inv_one]
  refine Subgroup.mem_map.2 ⟨g⁻¹ * bc (n := n) O.subtype h * g, ?_, ?_⟩
  · apply levelaf_mem_range_of_integral
    · exact levelaf_conj_integral O g c hg hg' h hh'
    · have : (g⁻¹ * bc (n := n) O.subtype h * g)⁻¹ = g⁻¹ * bc (n := n) O.subtype h⁻¹ * g := by
        rw [map_inv]; group
      rw [this]
      exact levelaf_conj_integral O g c hg hg' h⁻¹ hh''
  · simp [MulAut.conj_apply, mul_assoc]

/- English proof (translation)
Establish `: Finite (Matrix n n (O ⧸ I))` using `inferInstanceAs (Finite (n → n → O ⧸ I))`. Establish `hN : (redGL (n` using `n) I).ker.index ≠ 0 := by`. Rewrite using `[Subgroup.index_ker]`. Conclude with `Nat.card_pos.ne'`. Establish `hsup : ((redGL (n` using `n) I).ker ⊔ (bc (n := n) O.subtype).ker).index ≠ 0 := by`.

Introduce `h`. Apply `hN` to reduce the goal to its premises. Establish `hd` using `Subgroup.index_dvd_of_le (le_sup_left : (redGL (n := n) I).ker ≤ (redGL (n := n) I).ker ⊔ (bc (n := n) O.subtype).ker)`. Rewrite `hd` using `[h]`. Conclude with `Nat.eq_zero_of_zero_dvd hd`.

Establish `hprinc : princ (n` using `n) O.subtype I = ((redGL (n := n) I).ker).map (bc (n := n) O.subtype) := by`. Unfold `princ congPre`. Rewrite using `[MonoidHom.comap_bot]`. Rewrite using `[hprinc, MonoidHom.range_eq_map, Subgroup.relIndex_map_map, top_sup_eq, Subgroup.relIndex_top_right]`. Conclude with `hsup`.
-/
theorem levelaf_princ_relIndex_ne_zero (O : Subring L) (I : Ideal O) [Finite (O ⧸ I)] :
    (princ (n := n) O.subtype I).relIndex (bc (n := n) O.subtype).range ≠ 0 := by
  classical
  have : Finite (Matrix n n (O ⧸ I)) := inferInstanceAs (Finite (n → n → O ⧸ I))
  have hN : (redGL (n := n) I).ker.index ≠ 0 := by
    rw [Subgroup.index_ker]
    exact Nat.card_pos.ne'
  have hsup : ((redGL (n := n) I).ker ⊔ (bc (n := n) O.subtype).ker).index ≠ 0 := by
    intro h
    apply hN
    have hd := Subgroup.index_dvd_of_le
      (le_sup_left : (redGL (n := n) I).ker ≤ (redGL (n := n) I).ker ⊔ (bc (n := n) O.subtype).ker)
    rw [h] at hd
    exact Nat.eq_zero_of_zero_dvd hd
  have hprinc : princ (n := n) O.subtype I = ((redGL (n := n) I).ker).map (bc (n := n) O.subtype) := by
    unfold princ congPre
    rw [MonoidHom.comap_bot]
  rw [hprinc, MonoidHom.range_eq_map, Subgroup.relIndex_map_map, top_sup_eq,
    Subgroup.relIndex_top_right]
  exact hsup

end Generic

section Final

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)

/- English proof (translation)
Set `f : (n × n) ⊕ (n × n) → 𝒜` to `fun i => match i with`. Consider the case `.inl p => (g : Matrix n n 𝒜) p.1 p.2`. Consider the case `.inr p => ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) p.1 p.2`. Use `choose d hd0 hd using fun i => levelaf_denom (E := E) (f i)`. Establish `hmem : ∀ i, levelafC E (∏ k, d k) * f i ∈ 𝒮`.

Introduce `i`. Rewrite using `[← Finset.mul_prod_erase _ _ (Finset.mem_univ i), levelafC_mul, mul_comm (levelafC E (d i)), mul_assoc]`. Conclude with `mul_mem (levelafC_mem _) (hd i)`. Use `⟨∏ k, d k, Finset.prod_ne_zero_iff.2 fun i _ => hd0 i, ⟨_, levelafC_mem _⟩, rfl, ?_, ?_⟩` and prove the remaining obligations. Use `⟨Matrix.of fun i j => ⟨levelafC E (∏ k, d k) * (g : Matrix n n 𝒜) i j, hmem (.inl (i, j))⟩, ?_⟩` and prove the remaining obligations.

Use extensionality with `i j`. Simplify using the standard rewrite rules. Use `⟨Matrix.of fun i j => ⟨levelafC E (∏ k, d k) * ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) i j, hmem (.inr (i, j))⟩, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Simplify using the standard rewrite rules.
-/
theorem levelaf_exists_denom (g : GL n 𝒜) : ∃ d : 𝓞 F, d ≠ 0 ∧ ∃ c : 𝒮, (c : 𝒜) = levelafC E d ∧
    (c : 𝒜) • (g : Matrix n n 𝒜) ∈ (RingHom.mapMatrix (m := n) (𝒮).subtype).range ∧
    (c : 𝒜) • ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) ∈ (RingHom.mapMatrix (m := n) (𝒮).subtype).range := by
  classical
  let f : (n × n) ⊕ (n × n) → 𝒜 := fun i => match i with
    | .inl p => (g : Matrix n n 𝒜) p.1 p.2
    | .inr p => ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) p.1 p.2
  choose d hd0 hd using fun i => levelaf_denom (E := E) (f i)
  have hmem : ∀ i, levelafC E (∏ k, d k) * f i ∈ 𝒮 := by
    intro i
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), levelafC_mul,
      mul_comm (levelafC E (d i)), mul_assoc]
    exact mul_mem (levelafC_mem _) (hd i)
  refine ⟨∏ k, d k, Finset.prod_ne_zero_iff.2 fun i _ => hd0 i, ⟨_, levelafC_mem _⟩, rfl, ?_, ?_⟩
  · refine ⟨Matrix.of fun i j => ⟨levelafC E (∏ k, d k) * (g : Matrix n n 𝒜) i j,
      hmem (.inl (i, j))⟩, ?_⟩
    ext i j; simp
  · refine ⟨Matrix.of fun i j => ⟨levelafC E (∏ k, d k) * ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) i j,
      hmem (.inr (i, j))⟩, ?_⟩
    ext i j; simp

end Final

/- English proof (translation)
Introduce `F E _ _ _ _ _ n _ _ σ J g`. Take `⟨d, hd0, c, hc, hg, hg'⟩` from `levelaf_exists_denom (E := E) (n := n) (g : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F))`. Establish `hcc : ((c * c : tensInt (F` using `F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) : E ⊗[F] FiniteAdeleRing (𝓞 F) F) = levelafC E (d * d) := by`. Rewrite using `[levelafC_mul, ← hc]`. Both sides reduce to the same expression.

Establish `hfin : Finite (tensInt (F` using `F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F) ⧸ Ideal.span {c * c}) := levelaf_finite_quot (d * d) (mul_ne_zero hd0 hd0) (c * c) hcc`. Establish `hP` using `levelaf_princ_le_map_conj _ (g : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) c hg hg'`. Establish `hne` using `levelaf_princ_relIndex_ne_zero (n := n) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (Ideal.span {c * c})`. Establish `hstab : stabGL (stdLat (n` using `n) (A := E ⊗[F] FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F))) = (bc (n := n) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)).subtype).range := stabilizer_standard_lattice _ _ n Subtype.val_injective`. Establish `hLU : levelAf σ J ≤ UPts σ J (FiniteAdeleRing (𝓞 F) F)` using `inf_le_left`.

Establish `hLS : levelAf σ J ≤ (bc (n` using `n) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)).subtype).range := hstab ▸ inf_le_right`. Establish `h1 : (princ (n` using `n) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)).subtype (Ideal.span {c * c})).subgroupOf (UPts σ J (FiniteAdeleRing (𝓞 F) F)) ≤ ((levelAf σ J).subgroupOf (UPts σ J (FiniteAdeleRing (𝓞 F) F))).map (MulAut.conj g).toMonoidHom := by`. Introduce `h hh`. Rewrite `hh` using `[Subgroup.mem_subgroupOf]`. Take `⟨l, hl, hlh⟩` from `Subgroup.mem_map.1 (hP hh)`.

Use `Subgroup.mem_map.2 ⟨g⁻¹ * h * g, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Subgroup.mem_subgroupOf]`. Use `Subgroup.mem_inf.2 ⟨(g⁻¹ * h * g).2, ?_⟩` and prove the remaining obligations. Establish `: ((g⁻¹ * h * g : UPts σ J (FiniteAdeleRing (𝓞 F) F)) : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) = l`. Simplify using `only [Subgroup.coe_mul, Subgroup.coe_inv, ← hlh, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]`.

Use `group`. Rewrite using `[this, hstab]`. Conclude with `hl`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]`.

Use `group`. Establish `h2 : ((princ (n` using `n) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)).subtype (Ideal.span {c * c})).subgroupOf (UPts σ J (FiniteAdeleRing (𝓞 F) F))).relIndex ((levelAf σ J).subgroupOf (UPts σ J (FiniteAdeleRing (𝓞 F) F))) ≠ 0 := by`. Rewrite using `[Subgroup.relIndex_subgroupOf hLU]`. Introduce `h0`. Conclude with `hne (Subgroup.relIndex_eq_zero_of_le_right hLS h0)`.

Introduce `h0`. Establish `hd` using `Subgroup.relIndex_dvd_of_le_left ((levelAf σ J).subgroupOf (UPts σ J (FiniteAdeleRing (𝓞 F) F))) h1`. Rewrite `hd` using `[h0]`. Conclude with `h2 (Nat.eq_zero_of_zero_dvd hd)`.
-/
theorem finite_adelic_level_commute : Formalism.UG.LevelAfComm := by
  intro F E _ _ _ _ _ n _ _ σ J g
  obtain ⟨d, hd0, c, hc, hg, hg'⟩ := levelaf_exists_denom (E := E) (n := n)
    (g : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
  have hcc : ((c * c : tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) :
      E ⊗[F] FiniteAdeleRing (𝓞 F) F) = levelafC E (d * d) := by
    rw [levelafC_mul, ← hc]; rfl
  have hfin : Finite (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F) ⧸
      Ideal.span {c * c}) := levelaf_finite_quot (d * d) (mul_ne_zero hd0 hd0) (c * c) hcc
  have hP := levelaf_princ_le_map_conj _ (g : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) c hg hg'
  have hne := levelaf_princ_relIndex_ne_zero (n := n)
    (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (Ideal.span {c * c})
  have hstab : stabGL (stdLat (n := n) (A := E ⊗[F] FiniteAdeleRing (𝓞 F) F)
      (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F))) =
      (bc (n := n) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)).subtype).range :=
    stabilizer_standard_lattice _ _ n Subtype.val_injective
  have hLU : levelAf σ J ≤ UPts σ J (FiniteAdeleRing (𝓞 F) F) := inf_le_left
  have hLS : levelAf σ J ≤
      (bc (n := n) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)).subtype).range :=
    hstab ▸ inf_le_right
  have h1 : (princ (n := n) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)).subtype
      (Ideal.span {c * c})).subgroupOf (UPts σ J (FiniteAdeleRing (𝓞 F) F)) ≤
      ((levelAf σ J).subgroupOf (UPts σ J (FiniteAdeleRing (𝓞 F) F))).map
        (MulAut.conj g).toMonoidHom := by
    intro h hh
    rw [Subgroup.mem_subgroupOf] at hh
    obtain ⟨l, hl, hlh⟩ := Subgroup.mem_map.1 (hP hh)
    refine Subgroup.mem_map.2 ⟨g⁻¹ * h * g, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      refine Subgroup.mem_inf.2 ⟨(g⁻¹ * h * g).2, ?_⟩
      have : ((g⁻¹ * h * g : UPts σ J (FiniteAdeleRing (𝓞 F) F)) :
          GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) = l := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, ← hlh, MulEquiv.coe_toMonoidHom,
          MulAut.conj_apply]
        group
      rw [this, hstab]; exact hl
    · apply Subtype.ext
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
      group
  have h2 : ((princ (n := n) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)).subtype
      (Ideal.span {c * c})).subgroupOf (UPts σ J (FiniteAdeleRing (𝓞 F) F))).relIndex
      ((levelAf σ J).subgroupOf (UPts σ J (FiniteAdeleRing (𝓞 F) F))) ≠ 0 := by
    rw [Subgroup.relIndex_subgroupOf hLU]
    intro h0
    exact hne (Subgroup.relIndex_eq_zero_of_le_right hLS h0)
  intro h0
  have hd := Subgroup.relIndex_dvd_of_le_left
    ((levelAf σ J).subgroupOf (UPts σ J (FiniteAdeleRing (𝓞 F) F))) h1
  rw [h0] at hd
  exact h2 (Nat.eq_zero_of_zero_dvd hd)

end Formalism.UG.P
