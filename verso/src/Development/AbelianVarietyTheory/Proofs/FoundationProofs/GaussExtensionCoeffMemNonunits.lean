import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory

open scoped MatrixGroups TensorProduct in
open Matrix in
variable {F L : Type} [Field F] [Field L] [Algebra F L] in
/- English proof (translation)
Rewrite using `[Polynomial.aeval_def, Polynomial.eval₂_map, Polynomial.eval₂_eq_sum_range]`. Apply `Valuation.map_sum_le` to reduce the goal to its premises. Introduce `j _`. Rewrite using `[map_mul, map_pow]`. Conclude with `le_trans (mul_le_of_le_one_right' (pow_le_one' ht j)) (hVW _ (q.coeff j).2)`.
-/
private theorem valuation_aeval_map_subtype_le_one (V : ValuationSubring F) (W : ValuationSubring L)
    (t : L) (ht : W.valuation t ≤ 1)
    (hVW : ∀ a : F, a ∈ V → W.valuation (algebraMap F L a) ≤ 1) (q : Polynomial V) :
    W.valuation (Polynomial.aeval t (q.map V.subtype)) ≤ 1 := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_map, Polynomial.eval₂_eq_sum_range]
  apply Valuation.map_sum_le
  intro j _
  rw [map_mul, map_pow]
  exact le_trans (mul_le_of_le_one_right' (pow_le_one' ht j)) (hVW _ (q.coeff j).2)

open scoped MatrixGroups TensorProduct in
open Matrix in
/- English proof (translation)
Use extensionality with `n`. Simplify using `[Polynomial.coeff_C_mul, Algebra.smul_def]`.
-/
private theorem polynomial_smul_eq_C_algebraMap_mul {R S : Type} [CommRing R] [CommRing S]
    [Algebra R S] (x : R) (p : Polynomial S) :
    x • p = Polynomial.C (algebraMap R S x) * p := by
  ext n
  simp [Polynomial.coeff_C_mul, Algebra.smul_def]

open scoped MatrixGroups TensorProduct in
open Matrix in
/- English proof (translation)
Establish `hΨ1 : Ψ ≠ 1`. Introduce and unpack `rfl`. Rewrite `hdeg` using `[Polynomial.natDegree_one]`. Use linear arithmetic over natural numbers and integers. Establish `hirrΨ : Irreducible Ψ` using `hΨ.irreducible_iff_natDegree.2 ⟨hΨ1, hirr⟩`.

Establish `hinj : Function.Injective (algebraMap (Polynomial k) (FractionRing (Polynomial k)))` using `IsFractionRing.injective _ _`. Establish `hirrK` using `(hΨ.irreducible_iff_irreducible_map_fraction_map (K := FractionRing (Polynomial k))).1 hirrΨ`. Establish `hRK : R.map (algebraMap (Polynomial k) (FractionRing (Polynomial k))) ≠ 0`. Rewrite using `[Ne, Polynomial.map_eq_zero_iff hinj]` and apply the resulting hypothesis. Establish `hcop` using `(Irreducible.coprime_iff_not_dvd hirrK).2 (fun hd => by`.

Use `Polynomial.natDegree_le_of_dvd hd hRK` as an intermediate fact. Rewrite `this` using `[Polynomial.natDegree_map_eq_of_injective hinj, Polynomial.natDegree_map_eq_of_injective hinj]`. Use the proof step `omega)`. Take `⟨a, b, hab⟩` from `hcop`. Take `⟨ca, hA⟩` from `IsLocalization.integerNormalization_map_to_map (nonZeroDivisors (Polynomial k)) a`.

Take `⟨cb, hB⟩` from `IsLocalization.integerNormalization_map_to_map (nonZeroDivisors (Polynomial k)) b`. Use `⟨Polynomial.C (ca : Polynomial k) * IsLocalization.integerNormalization (nonZeroDivisors (Polynomial k)) b, Polynomial.C (cb : Polynomial k) * IsLocalization.integerNormalization (nonZeroDivisors (Polynomial k)) a, (ca : Polynomial k) * cb, mul_ne_zero (nonZeroDivisors.coe_ne_zer …` and prove the remaining obligations. Apply `Polynomial.map_injective _ hinj` to reduce the goal to its premises. Simplify using `only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, hA, hB, polynomial_smul_eq_C_algebraMap_mul, map_mul, Polynomial.C_mul]`. Take the linear combination `(Polynomial.C (algebraMap (Polynomial k) (FractionRing (Polynomial k)) ca) * Polynomial.C (algebraMap (Polynomial k) (FractionRing (Polynomial k)) cb)) * hab`.
-/
private theorem exists_mul_add_mul_eq_C_of_monic_irreducible {k : Type} [Field k]
    (Ψ R : Polynomial (Polynomial k)) (hΨ : Ψ.Monic)
    (hirr : ∀ A B : Polynomial (Polynomial k), A.Monic → B.Monic → A * B = Ψ →
      A.natDegree = 0 ∨ B.natDegree = 0)
    (hR : R ≠ 0) (hdeg : R.natDegree < Ψ.natDegree) :
    ∃ (A B : Polynomial (Polynomial k)) (c : Polynomial k), c ≠ 0 ∧
      A * R + B * Ψ = Polynomial.C c := by
  have hΨ1 : Ψ ≠ 1 := by
    rintro rfl
    rw [Polynomial.natDegree_one] at hdeg
    omega
  have hirrΨ : Irreducible Ψ := hΨ.irreducible_iff_natDegree.2 ⟨hΨ1, hirr⟩
  have hinj : Function.Injective (algebraMap (Polynomial k) (FractionRing (Polynomial k))) :=
    IsFractionRing.injective _ _
  have hirrK := (hΨ.irreducible_iff_irreducible_map_fraction_map
    (K := FractionRing (Polynomial k))).1 hirrΨ
  have hRK : R.map (algebraMap (Polynomial k) (FractionRing (Polynomial k))) ≠ 0 := by
    rwa [Ne, Polynomial.map_eq_zero_iff hinj]
  have hcop := (Irreducible.coprime_iff_not_dvd hirrK).2 (fun hd => by
    have := Polynomial.natDegree_le_of_dvd hd hRK
    rw [Polynomial.natDegree_map_eq_of_injective hinj,
      Polynomial.natDegree_map_eq_of_injective hinj] at this
    omega)
  obtain ⟨a, b, hab⟩ := hcop
  obtain ⟨ca, hA⟩ := IsLocalization.integerNormalization_map_to_map
    (nonZeroDivisors (Polynomial k)) a
  obtain ⟨cb, hB⟩ := IsLocalization.integerNormalization_map_to_map
    (nonZeroDivisors (Polynomial k)) b
  refine ⟨Polynomial.C (ca : Polynomial k) *
      IsLocalization.integerNormalization (nonZeroDivisors (Polynomial k)) b,
    Polynomial.C (cb : Polynomial k) *
      IsLocalization.integerNormalization (nonZeroDivisors (Polynomial k)) a,
    (ca : Polynomial k) * cb,
    mul_ne_zero (nonZeroDivisors.coe_ne_zero ca) (nonZeroDivisors.coe_ne_zero cb), ?_⟩
  apply Polynomial.map_injective _ hinj
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, hA, hB,
    polynomial_smul_eq_C_algebraMap_mul, map_mul, Polynomial.C_mul]
  linear_combination (Polynomial.C (algebraMap (Polynomial k) (FractionRing (Polynomial k)) ca) *
    Polynomial.C (algebraMap (Polynomial k) (FractionRing (Polynomial k)) cb)) * hab

open scoped MatrixGroups TensorProduct in
open Matrix in
variable {F L : Type} [Field F] [Field L] [Algebra F L] in
/- English proof (translation)
Rewrite using `[Polynomial.eval₂_map, Polynomial.eval₂_eq_sum_range]`. Apply `Valuation.map_sum_le` to reduce the goal to its premises. Introduce `i _`. Rewrite using `[map_mul, map_pow]`. Conclude with `le_trans (mul_le_of_le_one_right' (pow_le_one' hω i)) (valuation_aeval_map_subtype_le_one V W t ht hVW (Q.coeff i))`.
-/
private theorem valuation_eval2_aeval_le_one (V : ValuationSubring F) (W : ValuationSubring L)
    (t ω : L) (ht : W.valuation t ≤ 1) (hω : W.valuation ω ≤ 1)
    (hVW : ∀ a : F, a ∈ V → W.valuation (algebraMap F L a) ≤ 1)
    (Q : Polynomial (Polynomial V)) :
    W.valuation ((Q.map (Polynomial.mapRingHom V.subtype)).eval₂
      (Polynomial.aeval t).toRingHom ω) ≤ 1 := by
  rw [Polynomial.eval₂_map, Polynomial.eval₂_eq_sum_range]
  apply Valuation.map_sum_le
  intro i _
  rw [map_mul, map_pow]
  exact le_trans (mul_le_of_le_one_right' (pow_le_one' hω i))
    (valuation_aeval_map_subtype_le_one V W t ht hVW (Q.coeff i))

open scoped MatrixGroups TensorProduct in
open Matrix in
variable {F L : Type} [Field F] [Field L] [Algebra F L] in
/- English proof (translation)
Rewrite using `[Polynomial.aeval_def, Polynomial.eval₂_map, Polynomial.eval₂_eq_sum_range]`. Apply `Valuation.map_sum_lt _ one_ne_zero` to reduce the goal to its premises. Introduce `j _`. Rewrite using `[map_mul, map_pow]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_right' (pow_le_one' ht j)) (hq j)`.
-/
private theorem valuation_aeval_map_subtype_lt_one (V : ValuationSubring F) (W : ValuationSubring L)
    (t : L) (ht : W.valuation t ≤ 1) (q : Polynomial V)
    (hq : ∀ j, W.valuation (algebraMap F L (q.coeff j)) < 1) :
    W.valuation (Polynomial.aeval t (q.map V.subtype)) < 1 := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_map, Polynomial.eval₂_eq_sum_range]
  apply Valuation.map_sum_lt _ one_ne_zero
  intro j _
  rw [map_mul, map_pow]
  exact lt_of_le_of_lt (mul_le_of_le_one_right' (pow_le_one' ht j)) (hq j)

open scoped MatrixGroups TensorProduct in
open Matrix in
variable {F L : Type} [Field F] [Field L] [Algebra F L] in
/- English proof (translation)
Rewrite using `[Polynomial.eval₂_map, Polynomial.eval₂_eq_sum_range]`. Apply `Valuation.map_sum_lt _ one_ne_zero` to reduce the goal to its premises. Introduce `i _`. Rewrite using `[map_mul, map_pow]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_right' (pow_le_one' hω i)) (valuation_aeval_map_subtype_lt_one V W t ht (Q.coeff i) (hQ i))`.
-/
private theorem valuation_eval2_aeval_lt_one (V : ValuationSubring F) (W : ValuationSubring L)
    (t ω : L) (ht : W.valuation t ≤ 1) (hω : W.valuation ω ≤ 1)
    (Q : Polynomial (Polynomial V))
    (hQ : ∀ i j, W.valuation (algebraMap F L ((Q.coeff i).coeff j)) < 1) :
    W.valuation ((Q.map (Polynomial.mapRingHom V.subtype)).eval₂
      (Polynomial.aeval t).toRingHom ω) < 1 := by
  rw [Polynomial.eval₂_map, Polynomial.eval₂_eq_sum_range]
  apply Valuation.map_sum_lt _ one_ne_zero
  intro i _
  rw [map_mul, map_pow]
  exact lt_of_le_of_lt (mul_le_of_le_one_right' (pow_le_one' hω i))
    (valuation_aeval_map_subtype_lt_one V W t ht (Q.coeff i) (hQ i))

open scoped MatrixGroups TensorProduct in
open Matrix in
open scoped MatrixGroups TensorProduct in
open Matrix in

/- English proof (translation)
Introduce `F _ L _ _ t V W hVW hgauss Ψ ω hΨ hroot hirr R hdeg hRV hRW i₀ j₀`. Assume the negation of the conclusion as `hnot`. Establish `hVle : ∀ a : F, a ∈ V → W.valuation (algebraMap F L a) ≤ 1` using `fun a ha => (W.valuation_le_one_iff _).2 ((hVW a).2 ha)`. Establish `hloc : ∀ a : F, a ∈ V.nonunits → W.valuation (algebraMap F L a) < 1`. Introduce `a ha`.

Rewrite `ha` using `[ValuationSubring.mem_nonunits_iff]`. Establish `haV : a ∈ V` using `(V.valuation_le_one_iff a).1 ha.le`. Use `lt_of_le_of_ne (hVle a haV) fun h1 => ?_` and prove the remaining obligations. Establish `ha0 : a ≠ 0`. Introduce and unpack `rfl`.

Simplify using `at h1`. Establish `hinv : a⁻¹ ∈ V`. Rewrite using `[← hVW, ← W.valuation_le_one_iff, map_inv₀, map_inv₀, h1, inv_one]`. Establish `hm : V.valuation a * V.valuation a⁻¹ = 1`. Rewrite using `[← map_mul, mul_inv_cancel₀ ha0, map_one]`.

Establish `hle : V.valuation a⁻¹ ≤ 1` using `(V.valuation_le_one_iff _).2 hinv`. Establish `h1le : (1 : V.ValueGroup) ≤ V.valuation a`. Combine the equalities or inequalities in the displayed calculation. Conclude with `absurd ha (not_lt.2 h1le)`. Establish `ht : W.valuation t ≤ 1`.

Establish `h` using `hgauss Polynomial.X (fun i => by`. Rewrite using `[Polynomial.coeff_X]`. Use `split_ifs`. Use `exacts [one_mem V, zero_mem V])`. Use the proof step `⟨1, by simp, by simp [one_mem V], by simp [one_mem V]⟩`.

Rewrite `h` using `[Polynomial.aeval_X]`. Conclude with `h.le`. Establish `hω : W.valuation ω ≤ 1`. Establish `hQm : ((Ψ.map (Polynomial.mapRingHom V.subtype)).map (Polynomial.aeval t).toRingHom).Monic` using `(hΨ.map _).map _`. Establish `hlift : (Ψ.map (Polynomial.mapRingHom V.subtype)).map (Polynomial.aeval t).toRingHom ∈ Polynomial.lifts (algebraMap W L)`.

Rewrite using `[Polynomial.lifts_iff_coeff_lifts]`. Introduce `n`. Use `⟨⟨((Ψ.map (Polynomial.mapRingHom V.subtype)).map (Polynomial.aeval t).toRingHom).coeff n, ?_⟩, rfl⟩` and prove the remaining obligations. Rewrite using `[← W.valuation_le_one_iff, Polynomial.coeff_map, Polynomial.coeff_map]`. Conclude with `valuation_aeval_map_subtype_le_one V W t ht hVle _`.

Take `⟨Q', hQ', -, hQ'm⟩` from `Polynomial.lifts_and_natDegree_eq_and_monic hlift hQm`. Establish `hint : IsIntegral W ω`. Use `⟨Q', hQ'm, ?_⟩` and prove the remaining obligations. Rewrite using `[← Polynomial.eval_map, hQ', Polynomial.eval_map]`. Conclude with `hroot`.

Take `⟨y, hy⟩` from `IsIntegrallyClosed.isIntegral_iff.1 hint`. Rewrite using `[← hy]`. Conclude with `(W.valuation_le_one_iff _).2 y.2`. Establish `hRl : R ∈ Polynomial.lifts (Polynomial.mapRingHom V.subtype)`. Rewrite using `[Polynomial.lifts_iff_coeff_lifts]`.

Introduce `n`. Establish `hn : R.coeff n ∈ Polynomial.lifts V.subtype`. Rewrite using `[Polynomial.lifts_iff_coeff_lifts]`. Introduce `m`. Conclude with `⟨⟨_, hRV n m⟩, rfl⟩`.

Conclude with `(Polynomial.lifts_iff_set_range _).1 hn`. Take `⟨Rv, hRv⟩` from `RingHom.mem_rangeS.1 hRl`. Rewrite `hRv` using `[Polynomial.coe_mapRingHom]`. Establish `hcoef : ∀ i j, (R.coeff i).coeff j = ((Rv.coeff i).coeff j : F)`. Introduce `i j`.

Rewrite using `[← hRv, Polynomial.coeff_map, Polynomial.coe_mapRingHom, Polynomial.coeff_map]`. Both sides reduce to the same expression. Establish `hRbar : Rv.map (Polynomial.mapRingHom (IsLocalRing.residue V)) ≠ 0`. Introduce `h`. Establish `h'` using `congrArg (fun P => (P.coeff i₀).coeff j₀) h`.

Simplify using `only [Polynomial.coeff_map, Polynomial.coe_mapRingHom, Polynomial.coeff_zero] at h'`. Apply `hnot` to reduce the goal to its premises. Rewrite using `[ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal, hcoef]`. Conclude with `⟨((Rv.coeff i₀).coeff j₀).2, (IsLocalRing.residue_eq_zero_iff _).1 h'⟩`. Establish `hinjV : Function.Injective (Polynomial.mapRingHom V.subtype)` using `Polynomial.map_injective _ Subtype.val_injective`.

Establish `hdegbar : (Rv.map (Polynomial.mapRingHom (IsLocalRing.residue V))).natDegree < (Ψ.map (Polynomial.mapRingHom (IsLocalRing.residue V))).natDegree`. Rewrite using `[hΨ.natDegree_map]`. Use `lt_of_le_of_lt Polynomial.natDegree_map_le ?_` and prove the remaining obligations. Rewrite `hdeg` using `[← hRv, Polynomial.natDegree_map_eq_of_injective hinjV]`. Conclude with `hdeg`.

Take `⟨A, B, c, hc0, hABc⟩` from `exists_mul_add_mul_eq_C_of_monic_irreducible (Ψ.map (Polynomial.mapRingHom (IsLocalRing.residue V))) (Rv.map (Polynomial.mapRingHom (IsLocalRing.residue V))) (hΨ.map _) (hirr _ (IsLocalRing.residue V)) hRbar hdegbar`. Take `⟨Av, rfl⟩` from `Polynomial.map_surjective (Polynomial.mapRingHom (IsLocalRing.residue V)) (Polynomial.map_surjective _ IsLocalRing.residue_surjective) A`. Take `⟨Bv, rfl⟩` from `Polynomial.map_surjective (Polynomial.mapRingHom (IsLocalRing.residue V)) (Polynomial.map_surjective _ IsLocalRing.residue_surjective) B`. Take `⟨cv, rfl⟩` from `Polynomial.map_surjective _ IsLocalRing.residue_surjective c`. Use `set D : Polynomial (Polynomial V) := Av * Rv + Bv * Ψ - Polynomial.C cv with hDdef`.

Establish `hDm : D.map (Polynomial.mapRingHom (IsLocalRing.residue V)) = 0`. Simplify using `only [hDdef, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C]`. Rewrite using `[sub_eq_zero]`. Conclude with `hABc`. Establish `hD : ∀ i j, W.valuation (algebraMap F L ((D.coeff i).coeff j : F)) < 1`.

Introduce `i j`. Establish `h'` using `congrArg (fun P => (P.coeff i).coeff j) hDm`. Simplify using `only [Polynomial.coeff_map, Polynomial.coe_mapRingHom, Polynomial.coeff_zero] at h'`. Conclude with `hloc _ (ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.2 ⟨((D.coeff i).coeff j).2, (IsLocalRing.residue_eq_zero_iff _).1 h'⟩)`. Set `ev : Polynomial (Polynomial V) →+* L` to `(Polynomial.eval₂RingHom (Polynomial.aeval t).toRingHom ω).comp (Polynomial.mapRingHom (Polynomial.mapRingHom V.subtype))`.

Establish `hev : ∀ P, ev P = (P.map (Polynomial.mapRingHom V.subtype)).eval₂ (Polynomial.aeval t).toRingHom ω` using `fun P => rfl`. Establish `hCeq : Polynomial.C cv = Av * Rv + Bv * Ψ - D` using `(sub_sub_cancel _ _).symm`. Establish `hsplit : ev (Polynomial.C cv) = ev Av * ev Rv + ev Bv * ev Ψ - ev D`. Rewrite using `[hCeq, map_sub, map_add, map_mul, map_mul]`. Rewrite `hsplit` using `[hev Ψ, hroot, mul_zero, add_zero]`.

Choose the witnesses or unpack the hypotheses as in `⟨j, hj⟩ : ∃ j, IsLocalRing.residue V (cv.coeff j) ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Apply `hc0` to reduce the goal to its premises. Use extensionality with `j`.

Simplify using `[Polynomial.coeff_map, h j]`. Establish `hu : V.valuation (V.subtype (cv.coeff j)) = 1` using `(ValuationSubring.valuation_eq_one_iff V _).1 ((IsLocalRing.residue_ne_zero_iff_isUnit _).1 hj)`. Establish `hC1 : W.valuation (ev (Polynomial.C cv)) = 1`. Rewrite using `[hev, Polynomial.map_C, Polynomial.eval₂_C, Polynomial.coe_mapRingHom]`. Apply the tactic sequence `refine hgauss _ (fun i => by rw [Polynomial.coeff_map]; exact (cv.coeff i).2) ⟨j, ?_, ?_, ?_⟩ <;>`.

Rewrite using `[Polynomial.coeff_map]`. Introduce `h0`. Rewrite `hu` using `[h0, map_zero]`. Conclude with `zero_ne_one hu`. Conclude with `(cv.coeff j).2`.

Rewrite using `[← V.valuation_le_one_iff, map_inv₀, hu, inv_one]`. Establish `hRsmall : W.valuation (ev Rv) < 1`. Rewrite using `[hev, hRv]`. Conclude with `(W.mem_nonunits_iff).1 hRW`. Establish `hAle : W.valuation (ev Av) ≤ 1` using `valuation_eval2_aeval_le_one V W t ω ht hω hVle Av`.

Establish `hDsmall : W.valuation (ev D) < 1` using `valuation_eval2_aeval_lt_one V W t ω ht hω D hD`. Establish `hprod : W.valuation (ev Av * ev Rv) < 1`. Rewrite using `[map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left' hAle) hRsmall`. Establish `hlt : W.valuation (ev Av * ev Rv - ev D) < 1`.

Rewrite using `[sub_eq_add_neg]`. Conclude with `Valuation.map_add_lt _ hprod (by rwa [Valuation.map_neg])`. Rewrite `hlt` using `[← hsplit, hC1]`. Conclude with `lt_irrefl _ hlt`.
-/
theorem _root_.GlobalTheory.gaussExtension_coeff_mem_nonunits : ∀ {F : Type} [Field F] {L : Type} [Field L] [Algebra F L] (t : L) (V : ValuationSubring F) (W : ValuationSubring L), (∀ a : F, algebraMap F L a ∈ W ↔ a ∈ V) → (∀ P : Polynomial F, (∀ i, P.coeff i ∈ V) → (∃ i, P.coeff i ≠ 0 ∧ P.coeff i ∈ V ∧ (P.coeff i)⁻¹ ∈ V) → W.valuation (Polynomial.aeval t P) = 1) → ∀ (Ψ : Polynomial (Polynomial V)) (ω : L), Ψ.Monic → (Ψ.map (Polynomial.mapRingHom V.subtype)).eval₂ (Polynomial.aeval t).toRingHom ω = 0 → (∀ (k : Type) [Field k] (φ : V →+* k) (A B : Polynomial (Polynomial k)), A.Monic → B.Monic → A * B = Ψ.map (Polynomial.mapRingHom φ) → A.natDegree = 0 ∨ B.natDegree = 0) → ∀ R : Polynomial (Polynomial F), R.natDegree < Ψ.natDegree → (∀ i j, (R.coeff i).coeff j ∈ V) → R.eval₂ (Polynomial.aeval t).toRingHom ω ∈ W.nonunits → ∀ i j, (R.coeff i).coeff j ∈ V.nonunits := by
  intro F _ L _ _ t V W hVW hgauss Ψ ω hΨ hroot hirr R hdeg hRV hRW i₀ j₀
  by_contra hnot
  have hVle : ∀ a : F, a ∈ V → W.valuation (algebraMap F L a) ≤ 1 :=
    fun a ha => (W.valuation_le_one_iff _).2 ((hVW a).2 ha)
  have hloc : ∀ a : F, a ∈ V.nonunits → W.valuation (algebraMap F L a) < 1 := by
    intro a ha
    rw [ValuationSubring.mem_nonunits_iff] at ha
    have haV : a ∈ V := (V.valuation_le_one_iff a).1 ha.le
    refine lt_of_le_of_ne (hVle a haV) fun h1 => ?_
    have ha0 : a ≠ 0 := by
      rintro rfl
      simp at h1
    have hinv : a⁻¹ ∈ V := by
      rw [← hVW, ← W.valuation_le_one_iff, map_inv₀, map_inv₀, h1, inv_one]
    have hm : V.valuation a * V.valuation a⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ ha0, map_one]
    have hle : V.valuation a⁻¹ ≤ 1 := (V.valuation_le_one_iff _).2 hinv
    have h1le : (1 : V.ValueGroup) ≤ V.valuation a := by
      calc (1 : V.ValueGroup) = V.valuation a * V.valuation a⁻¹ := hm.symm
        _ ≤ V.valuation a := mul_le_of_le_one_right' hle
    exact absurd ha (not_lt.2 h1le)
  have ht : W.valuation t ≤ 1 := by
    have h := hgauss Polynomial.X
      (fun i => by
        rw [Polynomial.coeff_X]
        split_ifs
        exacts [one_mem V, zero_mem V])
      ⟨1, by simp, by simp [one_mem V], by simp [one_mem V]⟩
    rw [Polynomial.aeval_X] at h
    exact h.le
  have hω : W.valuation ω ≤ 1 := by
    have hQm : ((Ψ.map (Polynomial.mapRingHom V.subtype)).map
        (Polynomial.aeval t).toRingHom).Monic := (hΨ.map _).map _
    have hlift : (Ψ.map (Polynomial.mapRingHom V.subtype)).map (Polynomial.aeval t).toRingHom ∈
        Polynomial.lifts (algebraMap W L) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      refine ⟨⟨((Ψ.map (Polynomial.mapRingHom V.subtype)).map
        (Polynomial.aeval t).toRingHom).coeff n, ?_⟩, rfl⟩
      rw [← W.valuation_le_one_iff, Polynomial.coeff_map, Polynomial.coeff_map]
      exact valuation_aeval_map_subtype_le_one V W t ht hVle _
    obtain ⟨Q', hQ', -, hQ'm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift hQm
    have hint : IsIntegral W ω := by
      refine ⟨Q', hQ'm, ?_⟩
      rw [← Polynomial.eval_map, hQ', Polynomial.eval_map]
      exact hroot
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    rw [← hy]
    exact (W.valuation_le_one_iff _).2 y.2
  have hRl : R ∈ Polynomial.lifts (Polynomial.mapRingHom V.subtype) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    have hn : R.coeff n ∈ Polynomial.lifts V.subtype := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro m
      exact ⟨⟨_, hRV n m⟩, rfl⟩
    exact (Polynomial.lifts_iff_set_range _).1 hn
  obtain ⟨Rv, hRv⟩ := RingHom.mem_rangeS.1 hRl
  rw [Polynomial.coe_mapRingHom] at hRv
  have hcoef : ∀ i j, (R.coeff i).coeff j = ((Rv.coeff i).coeff j : F) := by
    intro i j
    rw [← hRv, Polynomial.coeff_map, Polynomial.coe_mapRingHom, Polynomial.coeff_map]
    rfl
  have hRbar : Rv.map (Polynomial.mapRingHom (IsLocalRing.residue V)) ≠ 0 := by
    intro h
    have h' := congrArg (fun P => (P.coeff i₀).coeff j₀) h
    simp only [Polynomial.coeff_map, Polynomial.coe_mapRingHom, Polynomial.coeff_zero] at h'
    apply hnot
    rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal, hcoef]
    exact ⟨((Rv.coeff i₀).coeff j₀).2, (IsLocalRing.residue_eq_zero_iff _).1 h'⟩
  have hinjV : Function.Injective (Polynomial.mapRingHom V.subtype) :=
    Polynomial.map_injective _ Subtype.val_injective
  have hdegbar : (Rv.map (Polynomial.mapRingHom (IsLocalRing.residue V))).natDegree <
      (Ψ.map (Polynomial.mapRingHom (IsLocalRing.residue V))).natDegree := by
    rw [hΨ.natDegree_map]
    refine lt_of_le_of_lt Polynomial.natDegree_map_le ?_
    rw [← hRv, Polynomial.natDegree_map_eq_of_injective hinjV] at hdeg
    exact hdeg
  obtain ⟨A, B, c, hc0, hABc⟩ := exists_mul_add_mul_eq_C_of_monic_irreducible
    (Ψ.map (Polynomial.mapRingHom (IsLocalRing.residue V)))
    (Rv.map (Polynomial.mapRingHom (IsLocalRing.residue V))) (hΨ.map _)
    (hirr _ (IsLocalRing.residue V)) hRbar hdegbar
  obtain ⟨Av, rfl⟩ := Polynomial.map_surjective (Polynomial.mapRingHom (IsLocalRing.residue V))
    (Polynomial.map_surjective _ IsLocalRing.residue_surjective) A
  obtain ⟨Bv, rfl⟩ := Polynomial.map_surjective (Polynomial.mapRingHom (IsLocalRing.residue V))
    (Polynomial.map_surjective _ IsLocalRing.residue_surjective) B
  obtain ⟨cv, rfl⟩ := Polynomial.map_surjective _ IsLocalRing.residue_surjective c
  set D : Polynomial (Polynomial V) := Av * Rv + Bv * Ψ - Polynomial.C cv with hDdef
  have hDm : D.map (Polynomial.mapRingHom (IsLocalRing.residue V)) = 0 := by
    simp only [hDdef, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C]
    rw [sub_eq_zero]
    exact hABc
  have hD : ∀ i j, W.valuation (algebraMap F L ((D.coeff i).coeff j : F)) < 1 := by
    intro i j
    have h' := congrArg (fun P => (P.coeff i).coeff j) hDm
    simp only [Polynomial.coeff_map, Polynomial.coe_mapRingHom, Polynomial.coeff_zero] at h'
    exact hloc _ (ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.2
      ⟨((D.coeff i).coeff j).2, (IsLocalRing.residue_eq_zero_iff _).1 h'⟩)
  let ev : Polynomial (Polynomial V) →+* L :=
    (Polynomial.eval₂RingHom (Polynomial.aeval t).toRingHom ω).comp
      (Polynomial.mapRingHom (Polynomial.mapRingHom V.subtype))
  have hev : ∀ P, ev P = (P.map (Polynomial.mapRingHom V.subtype)).eval₂
      (Polynomial.aeval t).toRingHom ω := fun P => rfl
  have hCeq : Polynomial.C cv = Av * Rv + Bv * Ψ - D := (sub_sub_cancel _ _).symm
  have hsplit : ev (Polynomial.C cv) = ev Av * ev Rv + ev Bv * ev Ψ - ev D := by
    rw [hCeq, map_sub, map_add, map_mul, map_mul]
  rw [hev Ψ, hroot, mul_zero, add_zero] at hsplit
  obtain ⟨j, hj⟩ : ∃ j, IsLocalRing.residue V (cv.coeff j) ≠ 0 := by
    by_contra h
    push_neg at h
    apply hc0
    ext j
    simp [Polynomial.coeff_map, h j]
  have hu : V.valuation (V.subtype (cv.coeff j)) = 1 :=
    (ValuationSubring.valuation_eq_one_iff V _).1
      ((IsLocalRing.residue_ne_zero_iff_isUnit _).1 hj)
  have hC1 : W.valuation (ev (Polynomial.C cv)) = 1 := by
    rw [hev, Polynomial.map_C, Polynomial.eval₂_C, Polynomial.coe_mapRingHom]
    refine hgauss _ (fun i => by rw [Polynomial.coeff_map]; exact (cv.coeff i).2) ⟨j, ?_, ?_, ?_⟩ <;>
      rw [Polynomial.coeff_map]
    · intro h0
      rw [h0, map_zero] at hu
      exact zero_ne_one hu
    · exact (cv.coeff j).2
    · rw [← V.valuation_le_one_iff, map_inv₀, hu, inv_one]
  have hRsmall : W.valuation (ev Rv) < 1 := by
    rw [hev, hRv]
    exact (W.mem_nonunits_iff).1 hRW
  have hAle : W.valuation (ev Av) ≤ 1 := valuation_eval2_aeval_le_one V W t ω ht hω hVle Av
  have hDsmall : W.valuation (ev D) < 1 := valuation_eval2_aeval_lt_one V W t ω ht hω D hD
  have hprod : W.valuation (ev Av * ev Rv) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' hAle) hRsmall
  have hlt : W.valuation (ev Av * ev Rv - ev D) < 1 := by
    rw [sub_eq_add_neg]
    exact Valuation.map_add_lt _ hprod (by rwa [Valuation.map_neg])
  rw [← hsplit, hC1] at hlt
  exact lt_irrefl _ hlt

end GlobalTheory
