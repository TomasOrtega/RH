import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProdPrimePowDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegersCompleteDVR
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

namespace GlobalTheory.NL.WDiv

section Series
variable {O : Type} [CommRing O] {L : Type} [Field L] [Algebra O L]

/- English proof (translation)
Establish `h` using `ev.commutes c`. Rewrite `h` using `[PowerSeries.algebraMap_apply, PowerSeries.algebraMap_apply]`. Simplify using `using h`.
-/
theorem ev_C' (ev : PowerSeries O →ₐ[O] PowerSeries L) (c : O) :
    ev (PowerSeries.C c) = PowerSeries.C (algebraMap O L c) := by
  have h := ev.commutes c
  rw [PowerSeries.algebraMap_apply, PowerSeries.algebraMap_apply] at h
  simpa using h

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => exact fun f => ⟨0, 1, one_ne_zero, by simp⟩`. Consider the case `succ m ih`. Introduce `f`. Take `⟨w', hw'⟩` from `hw.exists_right_inv`.

Choose the witnesses or unpack the hypotheses as in `⟨g, hg⟩ : PowerSeries.X ∣ f - PowerSeries.C (PowerSeries.constantCoeff f) := by`. Rewrite using `[PowerSeries.X_dvd_iff]`. Simplify using the standard rewrite rules. Take `⟨a, d, hd, z, hz⟩` from `ih (w' * g)`. Take `⟨⟨n, e, he⟩, hne⟩` from `IsLocalization.surj (nonZeroDivisors O) (PowerSeries.constantCoeff f)`.

Establish `hne'` using `congrArg (PowerSeries.C (R := L)) hne`. Simplify using `only [map_mul] at hne'`. Use `⟨PowerSeries.C (d * n) + PowerSeries.C e * (PowerSeries.X - PowerSeries.C x) * a, d * e, mul_ne_zero hd (nonZeroDivisors.ne_zero he), PowerSeries.C (algebraMap O L e) * w * z, ?_⟩` and prove the remaining obligations. Simplify using `only [map_add, map_mul, map_sub, ev_C', hev]`. Take the linear combination `(-(PowerSeries.C (algebraMap O L d))) * hne' - PowerSeries.C (algebraMap O L d) * PowerSeries.C (algebraMap O L e) * hg + PowerSeries.C (algebraMap O L e) * PowerSeries.X * w * hz + PowerSeries.C (algebraMap O L e) * PowerSeries.X * PowerSeries.C (algebraMap O L d) * g * hw'`.
-/
theorem powerSeries_expansion_image_dense_with_denominator [IsDomain O] [IsFractionRing O L] (ev : PowerSeries O →ₐ[O] PowerSeries L) (x : O)
    {w : PowerSeries L} (hw : IsUnit w)
    (hev : ev PowerSeries.X = PowerSeries.C (algebraMap O L x) + PowerSeries.X * w) (m : ℕ) :
    ∀ f : PowerSeries L, ∃ (a : PowerSeries O) (d : O), d ≠ 0 ∧
      PowerSeries.X ^ m ∣ ev a - PowerSeries.C (algebraMap O L d) * f := by
  induction m with
  | zero => exact fun f => ⟨0, 1, one_ne_zero, by simp⟩
  | succ m ih =>
    intro f
    obtain ⟨w', hw'⟩ := hw.exists_right_inv
    obtain ⟨g, hg⟩ : PowerSeries.X ∣ f - PowerSeries.C (PowerSeries.constantCoeff f) := by
      rw [PowerSeries.X_dvd_iff]; simp
    obtain ⟨a, d, hd, z, hz⟩ := ih (w' * g)
    obtain ⟨⟨n, e, he⟩, hne⟩ := IsLocalization.surj (nonZeroDivisors O) (PowerSeries.constantCoeff f)
    have hne' := congrArg (PowerSeries.C (R := L)) hne
    simp only [map_mul] at hne'
    refine ⟨PowerSeries.C (d * n) + PowerSeries.C e * (PowerSeries.X - PowerSeries.C x) * a, d * e,
      mul_ne_zero hd (nonZeroDivisors.ne_zero he), PowerSeries.C (algebraMap O L e) * w * z, ?_⟩
    simp only [map_add, map_mul, map_sub, ev_C', hev]
    linear_combination (-(PowerSeries.C (algebraMap O L d))) * hne' -
      PowerSeries.C (algebraMap O L d) * PowerSeries.C (algebraMap O L e) * hg +
      PowerSeries.C (algebraMap O L e) * PowerSeries.X * w * hz +
      PowerSeries.C (algebraMap O L e) * PowerSeries.X * PowerSeries.C (algebraMap O L d) * g * hw'

/- English proof (translation)
Take `⟨a, d, hd, h⟩` from `powerSeries_expansion_image_dense_with_denominator ev x hw hev m f`. Establish `hd' : algebraMap O L d ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective O L)).2 hd`. Use `⟨a, (algebraMap O L d)⁻¹, inv_ne_zero hd', ?_⟩` and prove the remaining obligations. Establish `h2` using `h.mul_left (PowerSeries.C (algebraMap O L d)⁻¹)`. Rewrite `h2` using `[mul_sub, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hd', map_one, one_mul, ← PowerSeries.smul_eq_C_mul]`. Then use the resulting hypothesis.
-/
theorem dense [IsDomain O] [IsFractionRing O L] (ev : PowerSeries O →ₐ[O] PowerSeries L) (x : O)
    {w : PowerSeries L} (hw : IsUnit w)
    (hev : ev PowerSeries.X = PowerSeries.C (algebraMap O L x) + PowerSeries.X * w) (m : ℕ)
    (f : PowerSeries L) : ∃ (a : PowerSeries O) (c : L), c ≠ 0 ∧
      PowerSeries.X ^ m ∣ c • ev a - f := by
  obtain ⟨a, d, hd, h⟩ := powerSeries_expansion_image_dense_with_denominator ev x hw hev m f
  have hd' : algebraMap O L d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O L)).2 hd
  refine ⟨a, (algebraMap O L d)⁻¹, inv_ne_zero hd', ?_⟩
  have h2 := h.mul_left (PowerSeries.C (algebraMap O L d)⁻¹)
  rwa [mul_sub, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hd', map_one, one_mul,
    ← PowerSeries.smul_eq_C_mul] at h2

/- English proof (translation)
Use `haveI : Fact l.Prime := ⟨hp⟩`. Establish `h0 : ((l : ℕ) : IsLocalRing.ResidueField O) = 0`. Rewrite using `[← map_natCast (IsLocalRing.residue O)]`. Conclude with `(IsLocalRing.residue_eq_zero_iff _).2 hl`. Use `haveI : CharP (IsLocalRing.ResidueField O) l := (CharP.charP_iff_prime_eq_zero hp).2 h0`.

Introduce `h`. Establish `h1` using `(h.map (IsLocalRing.residue O)).pow (l ^ j)`. Rewrite `h1` using `[map_sub, map_one, sub_pow_char_pow, ← map_pow, hμ, map_one, one_pow, sub_self]`. Conclude with `not_isUnit_zero h1`.
-/
theorem not_isUnit_sub_one [IsLocalRing O] {l : ℕ} (hp : l.Prime) (hl : ¬ IsUnit (l : O)) {μ : O} {j : ℕ}
    (hμ : μ ^ l ^ j = 1) : ¬ IsUnit (μ - 1) := by
  haveI : Fact l.Prime := ⟨hp⟩
  have h0 : ((l : ℕ) : IsLocalRing.ResidueField O) = 0 := by
    rw [← map_natCast (IsLocalRing.residue O)]
    exact (IsLocalRing.residue_eq_zero_iff _).2 hl
  haveI : CharP (IsLocalRing.ResidueField O) l := (CharP.charP_iff_prime_eq_zero hp).2 h0
  intro h
  have h1 := (h.map (IsLocalRing.residue O)).pow (l ^ j)
  rw [map_sub, map_one, sub_pow_char_pow, ← map_pow, hμ, map_one, one_pow, sub_self] at h1
  exact not_isUnit_zero h1

/- English proof (translation)
Establish `h` using `(GlobalTheory.Per.weierstrass_test O L ↥S (fun μ => μ.1 - 1) (fun _ => k) (fun μ ν h => Subtype.ext (sub_left_injective h)) (fun μ => hS μ.1 μ.2) (fun μ => ev μ.1) (fun μ => hev μ.1 μ.2) a).1 (fun μ => ha μ.1 μ.2)`. Rewrite `h` using `[Finset.prod_pow, Finset.prod_coe_sort S (fun μ => PowerSeries.X - PowerSeries.C (μ - 1))]`. Use `h using 3 with μ` and compare the differences between its conclusion and the goal. Rewrite using `[map_sub, map_one]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem test [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [IsFractionRing O L] (S : Finset O) (hS : ∀ μ ∈ S, ¬ IsUnit (μ - 1))
    (ev : O → (PowerSeries O →ₐ[O] PowerSeries L))
    (hev : ∀ μ ∈ S, ∃ w : PowerSeries L, IsUnit w ∧
      ev μ PowerSeries.X = PowerSeries.C (algebraMap O L (μ - 1)) + PowerSeries.X * w)
    (k : ℕ) (a : PowerSeries O) (ha : ∀ μ ∈ S, PowerSeries.X ^ k ∣ ev μ a) :
    (∏ μ ∈ S, (1 + PowerSeries.X - PowerSeries.C μ)) ^ k ∣ a := by
  have h := (GlobalTheory.Per.weierstrass_test O L ↥S (fun μ => μ.1 - 1) (fun _ => k)
    (fun μ ν h => Subtype.ext (sub_left_injective h)) (fun μ => hS μ.1 μ.2) (fun μ => ev μ.1)
    (fun μ => hev μ.1 μ.2) a).1 (fun μ => ha μ.1 μ.2)
  rw [Finset.prod_pow, Finset.prod_coe_sort S (fun μ => PowerSeries.X - PowerSeries.C (μ - 1))] at h
  convert h using 3 with μ
  rw [map_sub, map_one]; ring

/- English proof (translation)
Use `congrArg (Polynomial.aeval (1 + PowerSeries.X : PowerSeries O)) (Polynomial.X_pow_sub_one_eq_prod hN h)` as an intermediate fact. Simplify `this` using `[map_prod, PowerSeries.algebraMap_apply]`.
-/
theorem prod_roots [IsDomain O] {N : ℕ} (hN : 0 < N) {μ : O} (h : IsPrimitiveRoot μ N) :
    ((1 + PowerSeries.X) ^ N - 1 : PowerSeries O) =
      ∏ ν ∈ Polynomial.nthRootsFinset N (1 : O), (1 + PowerSeries.X - PowerSeries.C ν) := by
  have := congrArg (Polynomial.aeval (1 + PowerSeries.X : PowerSeries O))
    (Polynomial.X_pow_sub_one_eq_prod hN h)
  simpa [map_prod, PowerSeries.algebraMap_apply] using this

/- English proof (translation)
Use `congrArg (Polynomial.aeval (1 + PowerSeries.X : PowerSeries O)) ((Polynomial.cyclotomic_prime_pow_eq_geom_sum (R := O) (n := j) hp).symm.trans (Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots h))` as an intermediate fact. Simplify `this` using `[map_prod, map_sum, PowerSeries.algebraMap_apply]`.
-/
theorem prod_prim [IsDomain O] {l : ℕ} (hp : l.Prime) {j : ℕ} {μ : O} (h : IsPrimitiveRoot μ (l ^ (j + 1))) :
    (∑ i ∈ Finset.range l, ((1 + PowerSeries.X) ^ l ^ j) ^ i : PowerSeries O) =
      ∏ ν ∈ primitiveRoots (l ^ (j + 1)) O, (1 + PowerSeries.X - PowerSeries.C ν) := by
  have := congrArg (Polynomial.aeval (1 + PowerSeries.X : PowerSeries O))
    ((Polynomial.cyclotomic_prime_pow_eq_geom_sum (R := O) (n := j) hp).symm.trans
      (Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots h))
  simpa [map_prod, map_sum, PowerSeries.algebraMap_apply] using this

end Series

section Wach

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero => simp`. Consider the case `succ j ih`. Establish `h : W.φA (1 + letπ) = (1 + letπ) ^ PD.p`. Rewrite using `[map_add, map_one, W.φA_π]`.

Use function extensionality and compare the values at `i`. Use `W.q₀_def` as an intermediate fact. Simplify using `only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.one_apply, letπ, LocWach.q]`. Take the linear combination `this`. Rewrite using `[pow_succ', AlgHom.mul_apply, ih, map_pow, h, ← pow_mul, pow_succ']`.
-/
theorem phi_pow_one_add (j : ℕ) : (W.φA ^ j) (1 + letπ) = (1 + letπ) ^ PD.p ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h : W.φA (1 + letπ) = (1 + letπ) ^ PD.p := by
      rw [map_add, map_one, W.φA_π]
      funext i
      have := W.q₀_def
      simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.one_apply, letπ, LocWach.q]
      linear_combination this
    rw [pow_succ', AlgHom.mul_apply, ih, map_pow, h, ← pow_mul, pow_succ']

/- English proof (translation)
Establish `h` using `phi_pow_one_add W (W.s - 1)`. Rewrite `h` using `[map_add, map_one]`. Establish `h2` using `congrFun h i`. Simplify using `only [Pi.add_apply, Pi.pow_apply, Pi.one_apply] at h2`. Express the relevant statement in the definitionally equal form `1 + W.X i = (1 + PowerSeries.X) ^ _ at h2`.

Take the linear combination `h2`.
-/
theorem X_eq (i : ZMod n) : W.X i = (1 + PowerSeries.X) ^ PD.p ^ (W.s - 1) - 1 := by
  have h := phi_pow_one_add W (W.s - 1)
  rw [map_add, map_one] at h
  have h2 := congrFun h i
  simp only [Pi.add_apply, Pi.pow_apply, Pi.one_apply] at h2
  change 1 + W.X i = (1 + PowerSeries.X) ^ _ at h2
  linear_combination h2

/- English proof (translation)
Establish `hq : W.q = ∑ k ∈ Finset.range PD.p, (1 + letπ) ^ k`. Use function extensionality and compare the values at `i`. Simplify using `only [Finset.sum_apply, Pi.add_apply, Pi.pow_apply, Pi.one_apply, letπ, LocWach.q]`. Apply `mul_left_cancel₀ (PowerSeries.X_ne_zero (R := O))` to reduce the goal to its premises. Rewrite using `[W.q₀_def, ← mul_geom_sum]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[LocWach.Q, hq, map_sum]`. Simplify using `only [map_pow, phi_pow_one_add, Finset.sum_apply, Pi.add_apply, Pi.pow_apply, Pi.one_apply, letπ]`.
-/
theorem Q_eq [IsDomain O] (i : ZMod n) :
    W.Q i = ∑ k ∈ Finset.range PD.p, ((1 + PowerSeries.X) ^ PD.p ^ (W.s - 1)) ^ k := by
  have hq : W.q = ∑ k ∈ Finset.range PD.p, (1 + letπ) ^ k := by
    funext i
    simp only [Finset.sum_apply, Pi.add_apply, Pi.pow_apply, Pi.one_apply, letπ, LocWach.q]
    apply mul_left_cancel₀ (PowerSeries.X_ne_zero (R := O))
    rw [W.q₀_def, ← mul_geom_sum]
    ring
  rw [LocWach.Q, hq, map_sum]
  simp only [map_pow, phi_pow_one_add, Finset.sum_apply, Pi.add_apply, Pi.pow_apply, Pi.one_apply, letπ]

noncomputable def ev (i : ZMod n) (ζ : LL) : PowerSeries O →ₐ[O] PowerSeries LL :=
  (W.lev i ζ).comp (AlgHom.pi fun _ => AlgHom.id O (PowerSeries O))

/- English proof (translation)
Rewrite using `[← sub_eq_zero, ev, AlgHom.comp_apply, ← map_sub]`. Conclude with `W.lev_letter _ _ _ (by simp)`.
-/
theorem lev_eq (i : ZMod n) (ζ : LL) (a : LetA O n) : W.lev i ζ a = ev W i ζ (a i) := by
  rw [← sub_eq_zero, ev, AlgHom.comp_apply, ← map_sub]
  exact W.lev_letter _ _ _ (by simp)

/- English proof (translation)
Take `⟨E, h0, h1, h2⟩` from `W.lev_π i _ ⟨j, h⟩`. Rewrite `h2` using `[lev_eq]`. Choose the witnesses or unpack the hypotheses as in `⟨g, hg⟩ : PowerSeries.X ∣ E - 1 := by`. Rewrite using `[PowerSeries.X_dvd_iff]`. Simplify using `[h0]`.

Establish `hg0 : PowerSeries.constantCoeff g = 1`. Establish `a1` using `congrArg (PowerSeries.coeff 1) hg`. Establish `a2` using `congrArg (PowerSeries.coeff 0) h1`. Rewrite `a2` using `[PowerSeries.coeff_derivative]`. Rewrite `a1` using `[map_sub, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_one]`.

Simplify using `[h0] at a1 a2`. Rewrite using `[← a1, a2]`. Use `⟨PowerSeries.C (algebraMap O LL μ) * g, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[PowerSeries.isUnit_iff_constantCoeff]`. Simplify `h.ne_zero hj.ne'` using `[hg0]`.

Simplify using `only [letπ] at h2`. Rewrite using `[map_sub, map_sub, map_one, map_one]`. Take the linear combination `h2 + PowerSeries.C (algebraMap O LL μ) * hg`.
-/
theorem ev_X (i : ZMod n) (μ : O) {j : ℕ} (hj : 0 < PD.p ^ j)
    (h : IsPrimitiveRoot (algebraMap O LL μ) (PD.p ^ j)) :
    ∃ w : PowerSeries LL, IsUnit w ∧ ev W i (algebraMap O LL μ) PowerSeries.X =
      PowerSeries.C (algebraMap O LL (μ - 1)) + PowerSeries.X * w := by
  obtain ⟨E, h0, h1, h2⟩ := W.lev_π i _ ⟨j, h⟩
  rw [lev_eq] at h2
  obtain ⟨g, hg⟩ : PowerSeries.X ∣ E - 1 := by
    rw [PowerSeries.X_dvd_iff]; simp [h0]
  have hg0 : PowerSeries.constantCoeff g = 1 := by
    have a1 := congrArg (PowerSeries.coeff 1) hg
    have a2 := congrArg (PowerSeries.coeff 0) h1
    rw [PowerSeries.coeff_derivative] at a2
    rw [map_sub, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_one] at a1
    simp [h0] at a1 a2
    rw [← a1, a2]
  refine ⟨PowerSeries.C (algebraMap O LL μ) * g, ?_, ?_⟩
  · rw [PowerSeries.isUnit_iff_constantCoeff]
    simpa [hg0] using h.ne_zero hj.ne'
  · simp only [letπ] at h2
    rw [map_sub, map_sub, map_one, map_one]
    linear_combination h2 + PowerSeries.C (algebraMap O LL μ) * hg

variable [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
  [IsFractionRing O LL]

/- English proof (translation)
Establish `hs : W.s = W.s - 1 + 1` using `by have := W.s_pos; omega`. Establish `hpos : 0 < PD.p ^ W.s` using `pow_pos PD.hp.pos _`. Establish `hi` using `IsFractionRing.injective O LL`. Establish `key : ∀ i, (W.Q ^ k) i ∣ a i` using `fun i => by`. Rewrite using `[Pi.pow_apply, Q_eq, prod_prim PD.hp (hs ▸ h₀), ← hs]`.

Use `test (L := LL) _ (fun μ hμ => not_isUnit_sub_one PD.hp hl ((mem_primitiveRoots hpos).1 hμ).pow_eq_one) (fun μ => ev W i (algebraMap O LL μ)) (fun μ hμ => ev_X W i μ hpos (((mem_primitiveRoots hpos).1 hμ).map_of_injective hi)) k _ (fun μ hμ => ?_)` and prove the remaining obligations. Rewrite using `[← lev_eq]`. Conclude with `Ideal.mem_span_singleton.1 (ha i _ (((mem_primitiveRoots hpos).1 hμ).map_of_injective hi))`. Use `choose b hb using key`. Conclude with `⟨b, funext hb⟩`.
-/
theorem Q_test (hl : ¬ IsUnit (PD.p : O)) {μ₀ : O} (h₀ : IsPrimitiveRoot μ₀ (PD.p ^ W.s)) (k : ℕ)
    (a : LetA O n) (ha : ∀ i ζ, IsPrimitiveRoot ζ (PD.p ^ W.s) → a ∈ van W i ζ k) : W.Q ^ k ∣ a := by
  have hs : W.s = W.s - 1 + 1 := by have := W.s_pos; omega
  have hpos : 0 < PD.p ^ W.s := pow_pos PD.hp.pos _
  have hi := IsFractionRing.injective O LL
  have key : ∀ i, (W.Q ^ k) i ∣ a i := fun i => by
    rw [Pi.pow_apply, Q_eq, prod_prim PD.hp (hs ▸ h₀), ← hs]
    refine test (L := LL) _ (fun μ hμ => not_isUnit_sub_one PD.hp hl
      ((mem_primitiveRoots hpos).1 hμ).pow_eq_one) (fun μ => ev W i (algebraMap O LL μ))
      (fun μ hμ => ev_X W i μ hpos (((mem_primitiveRoots hpos).1 hμ).map_of_injective hi)) k _
      (fun μ hμ => ?_)
    rw [← lev_eq]
    exact Ideal.mem_span_singleton.1 (ha i _ (((mem_primitiveRoots hpos).1 hμ).map_of_injective hi))
  choose b hb using key
  exact ⟨b, funext hb⟩

/- English proof (translation)
Establish `hs : W.s = W.s - 1 + 1` using `by have := W.s_pos; omega`. Establish `hpos : 0 < PD.p ^ (W.s - 1)` using `pow_pos PD.hp.pos _`. Establish `hi` using `IsFractionRing.injective O LL`. Establish `h₁ : IsPrimitiveRoot (μ₀ ^ PD.p) (PD.p ^ (W.s - 1))` using `h₀.pow (pow_pos PD.hp.pos _) (by conv_lhs => rw [hs, pow_succ'])`. Establish `key : ∀ i, (W.X ^ k) i ∣ a i` using `fun i => by`.

Rewrite using `[Pi.pow_apply, X_eq, prod_roots hpos h₁]`. Use `test (L := LL) _ (fun μ hμ => not_isUnit_sub_one PD.hp hl ((Polynomial.mem_nthRootsFinset hpos 1).1 hμ)) (fun μ => ev W i (algebraMap O LL μ)) (fun μ hμ => ?_) k _ (fun μ hμ => ?_)` and prove the remaining obligations. Establish `h1` using `(Polynomial.mem_nthRootsFinset hpos 1).1 hμ`. Take `⟨j, -, hj⟩` from `(Nat.dvd_prime_pow PD.hp).1 (orderOf_dvd_of_pow_eq_one h1)`. Conclude with `ev_X W i μ (j := j) (pow_pos PD.hp.pos _) ((hj ▸ IsPrimitiveRoot.orderOf μ).map_of_injective hi)`.

Rewrite using `[← lev_eq]`. Use `Ideal.mem_span_singleton.1 (ha i _ ?_)` and prove the remaining obligations. Rewrite using `[← map_pow, (Polynomial.mem_nthRootsFinset hpos 1).1 hμ, map_one]`. Use `choose b hb using key`. Conclude with `⟨b, funext hb⟩`.
-/
theorem X_test (hl : ¬ IsUnit (PD.p : O)) {μ₀ : O} (h₀ : IsPrimitiveRoot μ₀ (PD.p ^ W.s)) (k : ℕ)
    (a : LetA O n) (ha : ∀ i ζ, ζ ^ (PD.p ^ (W.s - 1)) = 1 → a ∈ van W i ζ k) : W.X ^ k ∣ a := by
  have hs : W.s = W.s - 1 + 1 := by have := W.s_pos; omega
  have hpos : 0 < PD.p ^ (W.s - 1) := pow_pos PD.hp.pos _
  have hi := IsFractionRing.injective O LL
  have h₁ : IsPrimitiveRoot (μ₀ ^ PD.p) (PD.p ^ (W.s - 1)) :=
    h₀.pow (pow_pos PD.hp.pos _) (by conv_lhs => rw [hs, pow_succ'])
  have key : ∀ i, (W.X ^ k) i ∣ a i := fun i => by
    rw [Pi.pow_apply, X_eq, prod_roots hpos h₁]
    refine test (L := LL) _ (fun μ hμ => not_isUnit_sub_one PD.hp hl
      ((Polynomial.mem_nthRootsFinset hpos 1).1 hμ)) (fun μ => ev W i (algebraMap O LL μ))
      (fun μ hμ => ?_) k _ (fun μ hμ => ?_)
    · have h1 := (Polynomial.mem_nthRootsFinset hpos 1).1 hμ
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow PD.hp).1 (orderOf_dvd_of_pow_eq_one h1)
      exact ev_X W i μ (j := j) (pow_pos PD.hp.pos _)
        ((hj ▸ IsPrimitiveRoot.orderOf μ).map_of_injective hi)
    · rw [← lev_eq]
      refine Ideal.mem_span_singleton.1 (ha i _ ?_)
      rw [← map_pow, (Polynomial.mem_nthRootsFinset hpos 1).1 hμ, map_one]
  choose b hb using key
  exact ⟨b, funext hb⟩

omit [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] in
/- English proof (translation)
Take `⟨w, hw, hev⟩` from `ev_X W i μ (pow_pos PD.hp.pos _) h`. Take `⟨a, c, hc, h⟩` from `dense _ _ hw hev m f`. Conclude with `⟨fun _ => a, c, hc, by rwa [lev_eq]⟩`.
-/
theorem lev_dense (i : ZMod n) (μ : O) {j : ℕ} (h : IsPrimitiveRoot (algebraMap O LL μ) (PD.p ^ j))
    (f : PowerSeries LL) (m : ℕ) : ∃ (a : LetA O n) (c : LL), c ≠ 0 ∧
      PowerSeries.X ^ m ∣ c • W.lev i (algebraMap O LL μ) a - f := by
  obtain ⟨w, hw, hev⟩ := ev_X W i μ (pow_pos PD.hp.pos _) h
  obtain ⟨a, c, hc, h⟩ := dense _ _ hw hev m f
  exact ⟨fun _ => a, c, hc, by rwa [lev_eq]⟩

omit [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] in
/- English proof (translation)
Establish `hpos : 0 < PD.p ^ j` using `pow_pos PD.hp.pos _`. Establish `hi` using `IsFractionRing.injective O LL`. Take `⟨μ, rfl⟩` from `hint ζ h`. Take `⟨w, hw, hev⟩` from `ev_X W i μ hpos h`. Use `set P : PowerSeries O := ∏ ν ∈ (primitiveRoots (PD.p ^ j) O).erase μ, (PowerSeries.X - PowerSeries.C (ν - 1)) ^ m with hP`.

Establish `hu : IsUnit (ev W i (algebraMap O LL μ) P)`. Rewrite using `[hP, map_prod]`. Use `IsUnit.prod_iff.2 fun ν hν => ?_` and prove the remaining obligations. Rewrite using `[map_pow, map_sub, hev, ev_C']`. Use `IsUnit.pow _ ?_` and prove the remaining obligations.

Rewrite using `[PowerSeries.isUnit_iff_constantCoeff]`. Establish `: algebraMap O LL μ ≠ algebraMap O LL ν` using `fun e => (Finset.ne_of_mem_erase hν) (hi e).symm`. Simplify `this` using `[sub_eq_zero]`. Take `⟨u, hu'⟩` from `hu.exists_right_inv`. Take `⟨a, c, hc, hd⟩` from `dense _ _ hw hev m (u * f)`.

Use `⟨Pi.single i (a * P), c, hc, ?_, fun i' ζ' h' hne => ?_⟩` and prove the remaining obligations. Rewrite using `[lev_eq, Pi.single_eq_same, map_mul]`. Use `hd.mul_left (ev W i (algebraMap O LL μ) P) using 1` and compare the differences between its conclusion and the goal. Rewrite using `[mul_sub, ← mul_assoc, hu', one_mul, mul_smul_comm, mul_comm]`. Use `Ideal.mem_comap.2 (Ideal.mem_span_singleton.2 ?_)` and prove the remaining obligations.

Rewrite using `[lev_eq]`. Distinguish the cases in `hii : i' = i`. Substitute `hii` using the available equality. Take `⟨ν, rfl⟩` from `hint ζ' h'`. Take `⟨w', -, hev'⟩` from `ev_X W i' ν hpos h'`.

Rewrite using `[Pi.single_eq_same, map_mul]`. Use `Dvd.dvd.mul_left ?_ _` and prove the remaining obligations. Establish `hν : ν ∈ (primitiveRoots (PD.p ^ j) O).erase μ` using `Finset.mem_erase.2 ⟨fun e => hne (by rw [e]), (mem_primitiveRoots hpos).2 (h'.of_map_of_injective hi)⟩`. Use `Dvd.dvd.trans ?_ (map_dvd _ (Finset.dvd_prod_of_mem (fun ν => (PowerSeries.X - PowerSeries.C (ν - 1)) ^ m) hν))` and prove the remaining obligations. Rewrite using `[map_pow, map_sub, hev', ev_C', add_sub_cancel_left]`.

Conclude with `pow_dvd_pow_of_dvd (dvd_mul_right _ _) _`. Rewrite using `[Pi.single_eq_of_ne hii, map_zero]`. Conclude with `dvd_zero _`.
-/
theorem lev_dense_van {j : ℕ}
    (hint : ∀ ζ : LL, IsPrimitiveRoot ζ (PD.p ^ j) → ∃ μ : O, algebraMap O LL μ = ζ)
    (i : ZMod n) (ζ : LL) (h : IsPrimitiveRoot ζ (PD.p ^ j))
    (f : PowerSeries LL) (m : ℕ) : ∃ (a : LetA O n) (c : LL), c ≠ 0 ∧
      PowerSeries.X ^ m ∣ c • W.lev i ζ a - f ∧
      ∀ i' ζ', IsPrimitiveRoot ζ' (PD.p ^ j) → (i', ζ') ≠ (i, ζ) → a ∈ van W i' ζ' m := by
  classical
  have hpos : 0 < PD.p ^ j := pow_pos PD.hp.pos _
  have hi := IsFractionRing.injective O LL
  obtain ⟨μ, rfl⟩ := hint ζ h
  obtain ⟨w, hw, hev⟩ := ev_X W i μ hpos h
  set P : PowerSeries O := ∏ ν ∈ (primitiveRoots (PD.p ^ j) O).erase μ,
    (PowerSeries.X - PowerSeries.C (ν - 1)) ^ m with hP
  have hu : IsUnit (ev W i (algebraMap O LL μ) P) := by
    rw [hP, map_prod]
    refine IsUnit.prod_iff.2 fun ν hν => ?_
    rw [map_pow, map_sub, hev, ev_C']
    refine IsUnit.pow _ ?_
    rw [PowerSeries.isUnit_iff_constantCoeff]
    have : algebraMap O LL μ ≠ algebraMap O LL ν := fun e => (Finset.ne_of_mem_erase hν) (hi e).symm
    simpa [sub_eq_zero] using this
  obtain ⟨u, hu'⟩ := hu.exists_right_inv
  obtain ⟨a, c, hc, hd⟩ := dense _ _ hw hev m (u * f)
  refine ⟨Pi.single i (a * P), c, hc, ?_, fun i' ζ' h' hne => ?_⟩
  · rw [lev_eq, Pi.single_eq_same, map_mul]
    convert hd.mul_left (ev W i (algebraMap O LL μ) P) using 1
    rw [mul_sub, ← mul_assoc, hu', one_mul, mul_smul_comm, mul_comm]
  · refine Ideal.mem_comap.2 (Ideal.mem_span_singleton.2 ?_)
    rw [lev_eq]
    by_cases hii : i' = i
    · subst hii
      obtain ⟨ν, rfl⟩ := hint ζ' h'
      obtain ⟨w', -, hev'⟩ := ev_X W i' ν hpos h'
      rw [Pi.single_eq_same, map_mul]
      refine Dvd.dvd.mul_left ?_ _
      have hν : ν ∈ (primitiveRoots (PD.p ^ j) O).erase μ :=
        Finset.mem_erase.2 ⟨fun e => hne (by rw [e]),
          (mem_primitiveRoots hpos).2 (h'.of_map_of_injective hi)⟩
      refine Dvd.dvd.trans ?_ (map_dvd _ (Finset.dvd_prod_of_mem
        (fun ν => (PowerSeries.X - PowerSeries.C (ν - 1)) ^ m) hν))
      rw [map_pow, map_sub, hev', ev_C', add_sub_cancel_left]
      exact pow_dvd_pow_of_dvd (dvd_mul_right _ _) _
    · rw [Pi.single_eq_of_ne hii, map_zero]
      exact dvd_zero _

end Wach

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨ζ, IsIntegral.of_pow hN (h ▸ isIntegral_one)⟩, rfl⟩`.
-/
theorem root_integral {l : ℕ} [Fact l.Prime] (LL : FinExt l) {ζ : ↥LL.1} {N : ℕ} (hN : 0 < N)
    (h : ζ ^ N = 1) : ∃ μ : ↥(OL LL), algebraMap ↥(OL LL) ↥LL.1 μ = ζ :=
  ⟨⟨ζ, IsIntegral.of_pow hN (h ▸ isIntegral_one)⟩, rfl⟩

/- English proof (translation)
Establish `hp : l.Prime` using `Fact.out`. Use `haveI : NeZero ((l ^ s : ℕ) : Om l) := ⟨by exact_mod_cast (pow_pos hp.pos s).ne'⟩`. Take `⟨z, hz⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) (l ^ s)`. Establish `h1 : z ∈ Ks K s` using `(le_sup_right : _ ≤ Ks K s) (IntermediateField.subset_adjoin _ _ hz.pow_eq_one)`. Establish `h2 : z ∈ LL.1` using `h.2.2.2 (Ks K s).val ⟨z, h1⟩`.

Establish `h3 : IsPrimitiveRoot (⟨z, h2⟩ : ↥LL.1) (l ^ s)` using `IsPrimitiveRoot.of_map_of_injective (f := LL.1.val) hz Subtype.val_injective`. Take `⟨μ, hμ⟩` from `root_integral LL (pow_pos hp.pos s) h3.pow_eq_one`. Conclude with `⟨μ, IsPrimitiveRoot.of_map_of_injective (f := algebraMap ↥(OL LL) ↥LL.1) (hμ ▸ h3) Subtype.val_injective⟩`.
-/
theorem exists_prim {l : ℕ} [Fact l.Prime] {K : FinExt l} {s : ℕ} {LL : FinExt l} (h : Good K s LL) :
    ∃ μ : ↥(OL LL), IsPrimitiveRoot μ (l ^ s) := by
  have hp : l.Prime := Fact.out
  haveI : NeZero ((l ^ s : ℕ) : Om l) := ⟨by exact_mod_cast (pow_pos hp.pos s).ne'⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) (l ^ s)
  have h1 : z ∈ Ks K s :=
    (le_sup_right : _ ≤ Ks K s) (IntermediateField.subset_adjoin _ _ hz.pow_eq_one)
  have h2 : z ∈ LL.1 := h.2.2.2 (Ks K s).val ⟨z, h1⟩
  have h3 : IsPrimitiveRoot (⟨z, h2⟩ : ↥LL.1) (l ^ s) :=
    IsPrimitiveRoot.of_map_of_injective (f := LL.1.val) hz Subtype.val_injective
  obtain ⟨μ, hμ⟩ := root_integral LL (pow_pos hp.pos s) h3.pow_eq_one
  exact ⟨μ, IsPrimitiveRoot.of_map_of_injective (f := algebraMap ↥(OL LL) ↥LL.1) (hμ ▸ h3)
    Subtype.val_injective⟩

/- English proof (translation)
Introduce `D HW l _ K s LL h W`. Take `⟨_, hc, -, hl, -, -, hf⟩` from `GlobalTheory.Per.integers_completeDVR l LL`. Establish `hp : l.Prime` using `Fact.out`. Establish `e : ((D.loc l).PD K).p = l` using `(D.loc l).PD_p K`. Establish `es : W.s = s` using `(HW l).W_s K s LL h`.

Take `⟨μ₀, h₀⟩` from `exists_prim h`. Use `⟨fun k a ha => Q_test W (by rwa [e]) (μ₀ := μ₀) (by rwa [e, es]) k a (by rwa [e, es]), fun k a ha => X_test W (by rwa [e]) (μ₀ := μ₀) (by rwa [e, es]) k a (by rwa [e, es]), ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `i ζ ⟨j, hj⟩ f m`. Take `⟨μ, rfl⟩` from `root_integral LL (pow_pos hp.pos j) hj.pow_eq_one`. Conclude with `lev_dense W i μ (j := j) (by rwa [e]) f m`.

Introduce `i ζ hζ f m`. Use `lev_dense_van W (j := s) (by` as an intermediate fact. Rewrite using `[e]; exact fun ζ hζ => root_integral LL (pow_pos hp.pos s) hζ.pow_eq_one) i ζ (by rwa [e]) f m`. Rewrite `this` using `[e]`. Then use the resulting hypothesis.
-/
theorem weierstrass_dense : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; (∀ (k : ℕ) (a : AA K LL), (∀ (i : Let K) (ζ : ↥LL.1), IsPrimitiveRoot ζ (l ^ s) → a ∈ van W i ζ k) → W.Q ^ k ∣ a) ∧ (∀ (k : ℕ) (a : AA K LL), (∀ (i : Let K) (ζ : ↥LL.1), ζ ^ (l ^ (s - 1)) = 1 → a ∈ van W i ζ k) → W.X ^ k ∣ a) ∧ (∀ (i : Let K) (ζ : ↥LL.1), (∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j)) → ∀ (f : PowerSeries ↥LL.1) (m : ℕ), ∃ (a : AA K LL) (c : ↥LL.1), c ≠ 0 ∧ PowerSeries.X ^ m ∣ c • W.lev i ζ a - f) ∧ ∀ (i : Let K) (ζ : ↥LL.1), IsPrimitiveRoot ζ (l ^ s) → ∀ (f : PowerSeries ↥LL.1) (m : ℕ), ∃ (a : AA K LL) (c : ↥LL.1), c ≠ 0 ∧ PowerSeries.X ^ m ∣ c • W.lev i ζ a - f ∧ ∀ (i' : Let K) (ζ' : ↥LL.1), IsPrimitiveRoot ζ' (l ^ s) → (i', ζ') ≠ (i, ζ) → a ∈ van W i' ζ' m := by
  intro D HW l _ K s LL h W
  obtain ⟨_, hc, -, hl, -, -, hf⟩ := GlobalTheory.Per.integers_completeDVR l LL
  have hp : l.Prime := Fact.out
  have e : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have es : W.s = s := (HW l).W_s K s LL h
  obtain ⟨μ₀, h₀⟩ := exists_prim h
  refine ⟨fun k a ha => Q_test W (by rwa [e]) (μ₀ := μ₀) (by rwa [e, es]) k a (by rwa [e, es]),
    fun k a ha => X_test W (by rwa [e]) (μ₀ := μ₀) (by rwa [e, es]) k a (by rwa [e, es]), ?_, ?_⟩
  · rintro i ζ ⟨j, hj⟩ f m
    obtain ⟨μ, rfl⟩ := root_integral LL (pow_pos hp.pos j) hj.pow_eq_one
    exact lev_dense W i μ (j := j) (by rwa [e]) f m
  · intro i ζ hζ f m
    have := lev_dense_van W (j := s) (by
      rw [e]; exact fun ζ hζ => root_integral LL (pow_pos hp.pos s) hζ.pow_eq_one) i ζ (by rwa [e]) f m
    rwa [e] at this

end GlobalTheory.NL.WDiv
