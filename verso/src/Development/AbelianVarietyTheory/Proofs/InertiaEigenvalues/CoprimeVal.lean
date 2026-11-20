import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddXMulDerivativeBin
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAlgEquivXAddC
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCosetRepresentativesOfFiniteSubgroupPadicIStatement

noncomputable section

open PowerSeries GlobalTheory.CycFr IsLocalRing

namespace GlobalTheory.CycRoots

/- English proof (translation)
Take `⟨σ, hσ⟩` from `GlobalTheory.NB.LT.exists_algEquiv_X_add_C I x hx`. Set `c : O⟦X⟧ →ₐ[O] O` to `{ (constantCoeff : O⟦X⟧ →+* O) with commutes' := fun r => by simp [show algebraMap O O⟦X⟧ = C from rfl] }`. Use `⟨c.comp σ.toAlgHom, ?_, fun f => dvd_sub_C_of_shift x σ hσ f⟩` and prove the remaining obligations. Use `show constantCoeff (σ X) = x`. Rewrite using `[hσ]`.

Simplify using the standard rewrite rules.
-/
theorem exists_ev {O : Type} [CommRing O] (I : Ideal O) [IsAdicComplete I O] (x : O) (hx : x ∈ I) :
    ∃ ev : O⟦X⟧ →ₐ[O] O, ev X = x ∧ ∀ f, X - C x ∣ f - C (ev f) := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.NB.LT.exists_algEquiv_X_add_C I x hx
  let c : O⟦X⟧ →ₐ[O] O := { (constantCoeff : O⟦X⟧ →+* O) with commutes' := fun r => by simp [show algebraMap O O⟦X⟧ = C from rfl] }
  refine ⟨c.comp σ.toAlgHom, ?_, fun f => dvd_sub_C_of_shift x σ hσ f⟩
  show constantCoeff (σ X) = x
  rw [hσ]; simp

/- English proof (translation)
The claim follows from `φ.commutes c`.
-/
theorem ev_C {O : Type} [CommRing O] (φ : O⟦X⟧ →ₐ[O] O) (c : O) : φ (C c) = c := φ.commutes c

/- English proof (translation)
Use `map_dvd φ (h f)` as an intermediate fact. Rewrite `this` using `[map_sub, map_sub, ev_C, ev_C, hφ, sub_self, zero_dvd_iff, sub_eq_zero]`. Conclude with `this`.
-/
theorem ev_unique {O : Type} [CommRing O] (φ ev : O⟦X⟧ →ₐ[O] O) (x : O) (hφ : φ X = x)
    (h : ∀ f, X - C x ∣ f - C (ev f)) (f : O⟦X⟧) : φ f = ev f := by
  have := map_dvd φ (h f)
  rw [map_sub, map_sub, ev_C, ev_C, hφ, sub_self, zero_dvd_iff, sub_eq_zero] at this
  exact this

/- English proof (translation)
Establish `h : (X : O⟦X⟧) ∣ f - C (constantCoeff f)` using `by rw [X_dvd_iff]; simp`. Use `map_dvd φ h` as an intermediate fact. Rewrite `this` using `[map_sub, ev_C]`. Then use the resulting hypothesis.
-/
theorem dvd_ev_sub {O : Type} [CommRing O] (φ : O⟦X⟧ →ₐ[O] O) (f : O⟦X⟧) :
    φ X ∣ φ f - constantCoeff f := by
  have h : (X : O⟦X⟧) ∣ f - C (constantCoeff f) := by rw [X_dvd_iff]; simp
  have := map_dvd φ h
  rwa [map_sub, ev_C] at this

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on generalizing f with`. Consider the case `empty => simp`. Consider the case `insert i s hi ih`. Establish `h1` using `h i f`. Rewrite `h1` using `[hf i (Finset.mem_insert_self _ _), map_zero, sub_zero]`.

Take `⟨g, rfl⟩` from `h1`. Rewrite using `[Finset.prod_insert hi]`. Use `mul_dvd_mul_left _ (ih g fun j hj => ?_)` and prove the remaining obligations. Establish `h2` using `hf j (Finset.mem_insert_of_mem hj)`. Rewrite `h2` using `[map_mul, map_sub, hx, ev_C]`.

Use `(mul_eq_zero.1 h2).resolve_left fun h3 => hi ?_` and prove the remaining obligations. Rewrite using `[← hinj (sub_eq_zero.1 h3)]` and apply the resulting hypothesis.
-/
theorem prod_dvd {O ι : Type} [CommRing O] [IsDomain O] (x : ι → O) (ev : ι → (O⟦X⟧ →ₐ[O] O))
    (hx : ∀ i, ev i X = x i) (h : ∀ i f, X - C (x i) ∣ f - C (ev i f)) (hinj : Function.Injective x)
    (s : Finset ι) (f : O⟦X⟧) (hf : ∀ i ∈ s, ev i f = 0) : ∏ i ∈ s, (X - C (x i)) ∣ f := by
  classical
  induction s using Finset.induction_on generalizing f with
  | empty => simp
  | insert i s hi ih =>
    have h1 := h i f
    rw [hf i (Finset.mem_insert_self _ _), map_zero, sub_zero] at h1
    obtain ⟨g, rfl⟩ := h1
    rw [Finset.prod_insert hi]
    refine mul_dvd_mul_left _ (ih g fun j hj => ?_)
    have h2 := hf j (Finset.mem_insert_of_mem hj)
    rw [map_mul, map_sub, hx, ev_C] at h2
    refine (mul_eq_zero.1 h2).resolve_left fun h3 => hi ?_
    rwa [← hinj (sub_eq_zero.1 h3)]

/- English proof (translation)
Take `⟨u, hu⟩` from `hξ`. Establish `h1` using `congrArg (PowerSeries.map (residue O)) hq`. Establish `h2` using `congrArg (PowerSeries.map (residue O)) hu`. Simplify using `only [map_sub, map_mul, map_prod, map_C, map_X, map_pow, (residue_eq_zero_iff _).2 hp, (residue_eq_zero_iff _).2 (hx _), map_zero, sub_zero, Finset.prod_const, Finset.card_univ] at h1 h2`. Rewrite `h2` using `[h1, mul_assoc]`.

Establish `h3` using `mul_left_cancel₀ (pow_ne_zero _ X_ne_zero) (h2.trans (mul_one _).symm)`. Establish `h4 : IsUnit (PowerSeries.map (residue O) q)` using `IsUnit.of_mul_eq_one _ h3`. Rewrite `h4`, the goal using `[isUnit_iff_constantCoeff]`. Rewrite `h4` using `[← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply]`. Conclude with `(residue_ne_zero_iff_isUnit _).1 h4.ne_zero`.
-/
theorem isUnit_quot {O ι : Type} [CommRing O] [IsLocalRing O] [Fintype ι] (x : ι → O)
    (hx : ∀ i, x i ∈ maximalIdeal O) (ξ q : O⟦X⟧) (p : O) (hp : p ∈ maximalIdeal O)
    (hξ : Associated ξ (X ^ Fintype.card ι)) (hq : ξ - C p = (∏ i, (X - C (x i))) * q) :
    IsUnit q := by
  obtain ⟨u, hu⟩ := hξ
  have h1 := congrArg (PowerSeries.map (residue O)) hq
  have h2 := congrArg (PowerSeries.map (residue O)) hu
  simp only [map_sub, map_mul, map_prod, map_C, map_X, map_pow, (residue_eq_zero_iff _).2 hp,
    (residue_eq_zero_iff _).2 (hx _), map_zero, sub_zero, Finset.prod_const, Finset.card_univ] at h1 h2
  rw [h1, mul_assoc] at h2
  have h3 := mul_left_cancel₀ (pow_ne_zero _ X_ne_zero) (h2.trans (mul_one _).symm)
  have h4 : IsUnit (PowerSeries.map (residue O) q) := IsUnit.of_mul_eq_one _ h3
  rw [isUnit_iff_constantCoeff] at h4 ⊢
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply] at h4
  exact (residue_ne_zero_iff_isUnit _).1 h4.ne_zero

/- English proof (translation)
Establish `hl : 0 < l` using `(Fact.out : l.Prime).pos`. Establish `h1` using `congrArg (Polynomial.aeval (1 + X : O⟦X⟧)) (X_pow_sub_C_eq_prod hζ hl (one_pow l))`. Simplify using `only [map_sub, map_pow, map_prod, Polynomial.aeval_X, Polynomial.aeval_C, map_one, mul_one] at h1`. Establish `h2 : ∏ i ∈ Finset.range l, (1 + X - (algebraMap O O⟦X⟧ ζ) ^ i) = ∏ b : ZMod l, (X - C (ζ ^ b.val - 1))`. Use `symm`.

Use `Finset.prod_bij (fun b _ => b.val) (fun b _ => Finset.mem_range.2 (ZMod.val_lt b)) (fun a _ b _ h => ZMod.val_injective l h) (fun i hi => ⟨(i : ZMod l), Finset.mem_univ _, ZMod.val_cast_of_lt (Finset.mem_range.1 hi)⟩) (fun b _ => ?_)` and prove the remaining obligations. Simplify using `only [map_sub, map_pow, map_one, show algebraMap O O⟦X⟧ = C from rfl]`. Expand and normalize the polynomial expressions, which then agree. Establish `h3` using `mul_lvl (l := l) (O := O) 0`. Rewrite `h1` using `[h2, ← Finset.mul_prod_erase _ _ (Finset.mem_univ (0 : ZMod l))]`.

Simplify using `only [pow_zero, pow_one, zero_add, add_sub_cancel_left] at h3`. Rewrite `h3` using `[h1]`. Simplify using `only [ZMod.val_zero, pow_zero, sub_self, map_zero, sub_zero] at h3`. Conclude with `mul_left_cancel₀ X_ne_zero h3`.
-/
theorem lvl_eq_prod {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] (ζ : O)
    (hζ : IsPrimitiveRoot ζ l) :
    lvl l O 0 = ∏ b ∈ (Finset.univ : Finset (ZMod l)).erase 0, (X - C (ζ ^ b.val - 1)) := by
  have hl : 0 < l := (Fact.out : l.Prime).pos
  have h1 := congrArg (Polynomial.aeval (1 + X : O⟦X⟧))
    (X_pow_sub_C_eq_prod hζ hl (one_pow l))
  simp only [map_sub, map_pow, map_prod, Polynomial.aeval_X, Polynomial.aeval_C, map_one,
    mul_one] at h1
  have h2 : ∏ i ∈ Finset.range l, (1 + X - (algebraMap O O⟦X⟧ ζ) ^ i) =
      ∏ b : ZMod l, (X - C (ζ ^ b.val - 1)) := by
    symm
    refine Finset.prod_bij (fun b _ => b.val) (fun b _ => Finset.mem_range.2 (ZMod.val_lt b))
      (fun a _ b _ h => ZMod.val_injective l h)
      (fun i hi => ⟨(i : ZMod l), Finset.mem_univ _, ZMod.val_cast_of_lt (Finset.mem_range.1 hi)⟩)
      (fun b _ => ?_)
    simp only [map_sub, map_pow, map_one, show algebraMap O O⟦X⟧ = C from rfl]; ring
  have h3 := mul_lvl (l := l) (O := O) 0
  rw [h2, ← Finset.mul_prod_erase _ _ (Finset.mem_univ (0 : ZMod l))] at h1
  simp only [pow_zero, pow_one, zero_add, add_sub_cancel_left] at h3
  rw [h1] at h3
  simp only [ZMod.val_zero, pow_zero, sub_self, map_zero, sub_zero] at h3
  exact mul_left_cancel₀ X_ne_zero h3

/- English proof (translation)
The claim follows from `(Nat.coprime_of_lt_prime (by rwa [ne_eq, ZMod.val_eq_zero]) (ZMod.val_lt b) Fact.out).symm`.
-/
theorem coprime_val {l : ℕ} [Fact l.Prime] (b : ZMod l) (hb : b ≠ 0) : b.val.Coprime l :=
  (Nat.coprime_of_lt_prime (by rwa [ne_eq, ZMod.val_eq_zero]) (ZMod.val_lt b) Fact.out).symm

/- English proof (translation)
The claim follows from `hζ.associated_sub_one_pow_sub_one_of_coprime (coprime_val b hb)`.
-/
theorem assoc_val {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] (ζ : O)
    (hζ : IsPrimitiveRoot ζ l) (b : ZMod l) (hb : b ≠ 0) : Associated (ζ - 1) (ζ ^ b.val - 1) :=
  hζ.associated_sub_one_pow_sub_one_of_coprime (coprime_val b hb)

/- English proof (translation)
Establish `h` using `congrArg constantCoeff (lvl_eq_prod ζ hζ)`. Establish `h1 : constantCoeff (lvl l O 0) = (l : O)` using `by simp [lvl]`. Rewrite `h` using `[h1, map_prod]`. Rewrite using `[h]`. Establish `: (ζ - 1) ^ (l - 1) = ∏ _b ∈ (Finset.univ : Finset (ZMod l)).erase 0, (ζ - 1)`.

Rewrite using `[Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]`. Rewrite using `[this]`. Use `Associated.prod _ _ _ fun b hb => ?_` and prove the remaining obligations. Rewrite using `[map_sub, constantCoeff_X, constantCoeff_C, zero_sub]`. Conclude with `(assoc_val ζ hζ b (Finset.ne_of_mem_erase hb)).neg_right`.
-/
theorem assoc_l {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] (ζ : O)
    (hζ : IsPrimitiveRoot ζ l) : Associated ((ζ - 1) ^ (l - 1)) (l : O) := by
  have h := congrArg constantCoeff (lvl_eq_prod ζ hζ)
  have h1 : constantCoeff (lvl l O 0) = (l : O) := by simp [lvl]
  rw [h1, map_prod] at h
  rw [h]
  have : (ζ - 1) ^ (l - 1) = ∏ _b ∈ (Finset.univ : Finset (ZMod l)).erase 0, (ζ - 1) := by
    rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]
  rw [this]
  refine Associated.prod _ _ _ fun b hb => ?_
  rw [map_sub, constantCoeff_X, constantCoeff_C, zero_sub]
  exact (assoc_val ζ hζ b (Finset.ne_of_mem_erase hb)).neg_right

/- English proof (translation)
Use `set d := (PadicInt.toZMod δ).val with hd`. Establish `h1 : (l : ℤ_[l]) ^ 1 ∣ δ - (d : ℤ_[l])`. Rewrite using `[pow_one, ← Ideal.mem_span_singleton, ← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_natCast, hd, ZMod.natCast_zmod_val, sub_self]`. Establish `h2` using `map_dvd φ (dvd_bin_sub (O := O) 1 δ d h1)`. Establish `h3 : φ (1 + X) = ζ ^ b.val` using `by rw [map_add, map_one, hφ]; ring`.

Rewrite `h2` using `[map_sub, map_pow, h3, map_one, pow_one, ← pow_mul, mul_comm, pow_mul, hζ, one_pow, sub_self, zero_dvd_iff, map_sub, sub_eq_zero, bin_nat, map_pow, h3]`. Rewrite using `[act_X, map_sub, map_one, h2, ZMod.val_mul, ← pow_eq_pow_mod _ hζ, pow_mul]`.
-/
theorem ev_act_X {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [CharZero O]
    [Algebra ℤ_[l] O] (ζ : O) (hζ : ζ ^ l = 1) (b : ZMod l) (φ : O⟦X⟧ →ₐ[O] O)
    (hφ : φ X = ζ ^ b.val - 1) (δ : ℤ_[l]) :
    φ (act O δ X) = ζ ^ (b * PadicInt.toZMod δ).val - 1 := by
  set d := (PadicInt.toZMod δ).val with hd
  have h1 : (l : ℤ_[l]) ^ 1 ∣ δ - (d : ℤ_[l]) := by
    rw [pow_one, ← Ideal.mem_span_singleton, ← PadicInt.maximalIdeal_eq_span_p,
      ← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_natCast, hd, ZMod.natCast_zmod_val,
      sub_self]
  have h2 := map_dvd φ (dvd_bin_sub (O := O) 1 δ d h1)
  have h3 : φ (1 + X) = ζ ^ b.val := by rw [map_add, map_one, hφ]; ring
  rw [map_sub, map_pow, h3, map_one, pow_one, ← pow_mul, mul_comm, pow_mul, hζ, one_pow, sub_self,
    zero_dvd_iff, map_sub, sub_eq_zero, bin_nat, map_pow, h3] at h2
  rw [act_X, map_sub, map_one, h2, ZMod.val_mul, ← pow_eq_pow_mod _ hζ, pow_mul]

/- English proof (translation)
Establish `hk : ((l : ℕ) : ResidueField O) = 0`. Rewrite using `[← map_natCast (residue O), residue_eq_zero_iff]`. Conclude with `hl`. Use `haveI : CharP (ResidueField O) l := (CharP.charP_iff_prime_eq_zero Fact.out).2 hk`. Establish `hζ : residue O ζ = 1`.

Use `(residue_eq_zero_iff _).2 hm` as an intermediate fact. Rewrite `this` using `[map_sub, map_one, sub_eq_zero]`. Then use the resulting hypothesis. Establish `key : ∀ (c : ZMod l) (ψ : O⟦X⟧ →ₐ[O] O), ψ X = ζ ^ c.val - 1 → ∃ y, ψ (X ^ s * w) = (ζ - 1) ^ s * y ∧ residue O y = ZMod.castHom (dvd_refl l) (ResidueField O) (c ^ s) * residue O (constantCoeff w)`. Introduce `c ψ hψ`. Use `⟨(∑ i ∈ Finset.range c.val, ζ ^ i) ^ s * ψ w, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul, map_pow, hψ, ← mul_geom_sum, mul_pow, mul_assoc]`. Establish `h1 : residue O (ψ w) = residue O (constantCoeff w)`. Rewrite using `[← sub_eq_zero, ← map_sub, residue_eq_zero_iff]`. Use `Ideal.mem_of_dvd _ (dvd_ev_sub ψ w) ?_` and prove the remaining obligations. Rewrite using `[hψ]`.

Conclude with `Ideal.mem_of_dvd _ (by simpa using sub_dvd_pow_sub_pow ζ 1 c.val) hm`. Rewrite using `[map_mul, h1, map_pow, map_pow, map_sum]`. Simplify using `[hζ]`. Take `⟨y, hy, hy2⟩` from `key b φ hφ`. Take `⟨y', hy', hy2'⟩` from `key b' φ' hφ'`.

Rewrite using `[hy, hy', ← mul_sub]`. Use `associated_mul_isUnit_left_iff ?_ |>.2 (Associated.refl _)` and prove the remaining obligations. Rewrite using `[← residue_ne_zero_iff_isUnit, map_sub, hy2, hy2', ← sub_mul]`. Use `mul_ne_zero (sub_ne_zero.2 fun h => hb (RingHom.injective _ h)) ?_` and prove the remaining obligations. Rewrite using `[residue_ne_zero_iff_isUnit]`.

Conclude with `hw.map _`.
-/
theorem assoc_sub {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsLocalRing O]
    (hl : ¬ IsUnit (l : O)) (ζ : O) (hm : ζ - 1 ∈ maximalIdeal O) (s : ℕ) (w : O⟦X⟧)
    (hw : IsUnit w) (b b' : ZMod l) (hb : b ^ s ≠ b' ^ s) (φ φ' : O⟦X⟧ →ₐ[O] O)
    (hφ : φ X = ζ ^ b.val - 1) (hφ' : φ' X = ζ ^ b'.val - 1) :
    Associated (φ (X ^ s * w) - φ' (X ^ s * w)) ((ζ - 1) ^ s) := by
  have hk : ((l : ℕ) : ResidueField O) = 0 := by
    rw [← map_natCast (residue O), residue_eq_zero_iff]; exact hl
  haveI : CharP (ResidueField O) l := (CharP.charP_iff_prime_eq_zero Fact.out).2 hk
  have hζ : residue O ζ = 1 := by
    have := (residue_eq_zero_iff _).2 hm
    rwa [map_sub, map_one, sub_eq_zero] at this
  have key : ∀ (c : ZMod l) (ψ : O⟦X⟧ →ₐ[O] O), ψ X = ζ ^ c.val - 1 → ∃ y, ψ (X ^ s * w) =
      (ζ - 1) ^ s * y ∧ residue O y = ZMod.castHom (dvd_refl l) (ResidueField O) (c ^ s) *
        residue O (constantCoeff w) := by
    intro c ψ hψ
    refine ⟨(∑ i ∈ Finset.range c.val, ζ ^ i) ^ s * ψ w, ?_, ?_⟩
    · rw [map_mul, map_pow, hψ, ← mul_geom_sum, mul_pow, mul_assoc]
    · have h1 : residue O (ψ w) = residue O (constantCoeff w) := by
        rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
        refine Ideal.mem_of_dvd _ (dvd_ev_sub ψ w) ?_
        rw [hψ]
        exact Ideal.mem_of_dvd _ (by simpa using sub_dvd_pow_sub_pow ζ 1 c.val) hm
      rw [map_mul, h1, map_pow, map_pow, map_sum]
      simp [hζ]
  obtain ⟨y, hy, hy2⟩ := key b φ hφ
  obtain ⟨y', hy', hy2'⟩ := key b' φ' hφ'
  rw [hy, hy', ← mul_sub]
  refine associated_mul_isUnit_left_iff ?_ |>.2 (Associated.refl _)
  rw [← residue_ne_zero_iff_isUnit, map_sub, hy2, hy2', ← sub_mul]
  refine mul_ne_zero (sub_ne_zero.2 fun h => hb (RingHom.injective _ h)) ?_
  rw [residue_ne_zero_iff_isUnit]
  exact hw.map _

/- English proof (translation)
Introduce `l _ O _ _ _ _ _ _ Δ _ ξ hl2 hl ⟨ζ, hζ⟩ hξ hinv`. Use `haveI := Fintype.ofFinite Δ`. Take `⟨e, a, hes, ha, hpow, hbij⟩` from `GlobalTheory.T.exists_coset_reps_finite_subgroup_padicInt_units Δ hl2`. Establish `hm : ζ - 1 ∈ maximalIdeal O` using `fun h => hl ((assoc_l ζ hζ).isUnit (h.pow _))`. Establish `hz : ∀ b : ZMod l, ζ ^ b.val - 1 ∈ maximalIdeal O` using `fun b => Ideal.mem_of_dvd _ (by simpa using sub_dvd_pow_sub_pow ζ 1 b.val) hm`.

Use `choose ev hevX hev using fun b : ZMod l => exists_ev (maximalIdeal O) _ (hz b)`. Establish `hinj : Function.Injective fun b : ZMod l => ζ ^ b.val - 1` using `fun b b' h => ZMod.val_injective l (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) (sub_left_inj.1 h))`. Establish `ha0 : ∀ τ, (a τ : ZMod l) ≠ 0` using `fun τ h => ha τ ((ZMod.natCast_eq_zero_iff _ _).1 h)`. Set `pt : Fin e × Δ → ZMod l` to `fun p => (a p.1 : ZMod l) * PadicInt.toZMod ((p.2 : ℤ_[l]ˣ) : ℤ_[l])`. Establish `pt0 : ∀ p, pt p ≠ 0` using `fun p => mul_ne_zero (ha0 _) ((Units.isUnit _).map PadicInt.toZMod).ne_zero`.

Establish `ptinj : Function.Injective pt` using `fun p p' h => (hbij _ (pt0 p)).unique rfl h`. Choose the witnesses or unpack the hypotheses as in `⟨w, hw, hξw⟩ : ∃ w : O⟦X⟧, IsUnit w ∧ ξ = X ^ Nat.card Δ * w := by`. Take `⟨u, hu⟩` from `hξ.symm`. Conclude with `⟨u, u.isUnit, hu.symm⟩`. Establish `hval : ∀ τ (δ : Δ), ev (pt (τ, δ)) ξ = ev (a τ) ξ`.

Introduce `τ δ`. Rewrite using `[← ev_unique ((ev (a τ)).comp (act O ((δ : ℤ_[l]ˣ) : ℤ_[l]))) _ _ (ev_act_X ζ hζ.pow_eq_one _ _ (hevX _) _) (hev (pt (τ, δ))) ξ, AlgHom.comp_apply, hinv _ δ.2]`. Establish `hϖ : ∀ τ, Associated (ev (a τ) ξ) ((ζ - 1) ^ Nat.card Δ)`. Introduce `τ`. Rewrite using `[hξw, map_mul, map_pow, hevX]`.

Conclude with `(associated_mul_isUnit_left_iff (hw.map _)).2 (assoc_val ζ hζ _ (ha0 τ)).symm.pow_pow`. Establish `hfac : ∀ τ, ∃ q, IsUnit q ∧ ξ - C (ev (a τ) ξ) = (∏ δ : Δ, (X - C (ζ ^ (pt (τ, δ)).val - 1))) * q`. Introduce `τ`. Take `⟨q, hq⟩` from `prod_dvd (fun δ : Δ => ζ ^ (pt (τ, δ)).val - 1) (fun δ => ev (pt (τ, δ))) (fun δ => hevX _) (fun δ => hev _) (fun δ δ' h => (Prod.ext_iff.1 (ptinj (hinj h))).2) Finset.univ (ξ - C (ev (a τ) ξ)) (fun δ _ => by rw [map_sub, ev_C, hval, sub_self])`. Use `⟨q, isUnit_quot _ (fun δ => hz _) ξ q _ ?_ (by rwa [← Nat.card_eq_fintype_card]) hq, hq⟩` and prove the remaining obligations.

Conclude with `Ideal.mem_of_dvd _ ((dvd_pow_self _ Nat.card_pos.ne').trans (hϖ τ).symm.dvd) hm`. Use `choose q hqu hq using hfac`. Use `⟨e, fun τ => ev (a τ) ξ, hes, fun τ => ?_, fun τ τ' h => ?_, ?_, fun τ => ?_⟩` and prove the remaining obligations. Use `(hϖ τ).pow_pow.trans ?_` and prove the remaining obligations. Rewrite using `[← pow_mul, mul_comm, hes]`.

Conclude with `assoc_l ζ hζ`. Use `Associated.trans ?_ (hϖ τ).symm` and prove the remaining obligations. Rewrite using `[hξw]`. Conclude with `assoc_sub hl ζ hm _ w hw _ _ (hpow τ τ' h) _ _ (hevX _) (hevX _)`. Simplify using `only [hq]`.

Rewrite using `[Finset.prod_mul_distrib, ← Fintype.prod_prod_type (fun p : Fin e × Δ => (X - C (ζ ^ (pt p).val - 1) : O⟦X⟧)), lvl_eq_prod ζ hζ]`. Use `(associated_mul_isUnit_left_iff (IsUnit.prod_univ_iff.2 hqu)).2 (Associated.of_eq ?_)` and prove the remaining obligations. Use `Finset.prod_bij (fun p _ => pt p) (fun p _ => by simpa using pt0 p) (fun p _ p' _ h => ptinj h) (fun b hb => ?_) (fun _ _ => rfl)` and prove the remaining obligations. Take `⟨p, hp, -⟩` from `hbij b (Finset.ne_of_mem_erase hb)`. Conclude with `⟨p, Finset.mem_univ _, hp.symm⟩`.

Use `⟨ζ ^ (pt (τ, 1)).val, (∏ δ ∈ Finset.univ.erase 1, (X - C (ζ ^ (pt (τ, δ)).val - 1))) * q τ, hζ.pow_of_coprime _ (coprime_val _ (pt0 _)), ?_, fun h => ?_⟩` and prove the remaining obligations. Rewrite using `[hq, ← Finset.mul_prod_erase _ _ (Finset.mem_univ (1 : Δ)), mul_assoc]`. Establish `h1` using `map_dvd (ev (pt (τ, 1))) h`. Rewrite `h1` using `[map_sub, hevX, ev_C, sub_self, zero_dvd_iff, map_mul, map_prod]`. Use `mul_ne_zero (Finset.prod_ne_zero_iff.2 fun δ hδ => ?_) ((hqu τ).map _).ne_zero h1` and prove the remaining obligations.

Rewrite using `[map_sub, hevX, ev_C, sub_ne_zero]`. Conclude with `fun h2 => Finset.ne_of_mem_erase hδ (Prod.ext_iff.1 (ptinj (hinj h2))).2.symm`.
-/
theorem exists_roots : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [CharZero O] [Algebra ℤ_[l] O] (Δ : Subgroup ℤ_[l]ˣ) [Finite Δ] (ξ : O⟦X⟧), l ≠ 2 → ¬ IsUnit (l : O) → (∃ ζ : O, IsPrimitiveRoot ζ l) → Associated ξ (X ^ Nat.card Δ) → (∀ δ ∈ Δ, act O (δ : ℤ_[l]) ξ = ξ) → ∃ (e : ℕ) (ϖ : Fin e → O), e * Nat.card Δ = l - 1 ∧ (∀ τ, Associated (ϖ τ ^ e) (l : O)) ∧ (∀ τ τ', τ ≠ τ' → Associated (ϖ τ - ϖ τ') (ϖ τ)) ∧ Associated (∏ τ, (ξ - C (ϖ τ))) (lvl l O 0) ∧ ∀ τ, ∃ (ζ : O) (w : O⟦X⟧), IsPrimitiveRoot ζ l ∧ ξ - C (ϖ τ) = (X - C (ζ - 1)) * w ∧ ¬ (X - C (ζ - 1)) ∣ w := by
  intro l _ O _ _ _ _ _ _ Δ _ ξ hl2 hl ⟨ζ, hζ⟩ hξ hinv
  classical
  haveI := Fintype.ofFinite Δ
  obtain ⟨e, a, hes, ha, hpow, hbij⟩ := GlobalTheory.T.exists_coset_reps_finite_subgroup_padicInt_units Δ hl2
  have hm : ζ - 1 ∈ maximalIdeal O := fun h => hl ((assoc_l ζ hζ).isUnit (h.pow _))
  have hz : ∀ b : ZMod l, ζ ^ b.val - 1 ∈ maximalIdeal O := fun b =>
    Ideal.mem_of_dvd _ (by simpa using sub_dvd_pow_sub_pow ζ 1 b.val) hm
  choose ev hevX hev using fun b : ZMod l => exists_ev (maximalIdeal O) _ (hz b)
  have hinj : Function.Injective fun b : ZMod l => ζ ^ b.val - 1 := fun b b' h =>
    ZMod.val_injective l (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) (sub_left_inj.1 h))
  have ha0 : ∀ τ, (a τ : ZMod l) ≠ 0 := fun τ h => ha τ ((ZMod.natCast_eq_zero_iff _ _).1 h)
  let pt : Fin e × Δ → ZMod l := fun p => (a p.1 : ZMod l) * PadicInt.toZMod ((p.2 : ℤ_[l]ˣ) : ℤ_[l])
  have pt0 : ∀ p, pt p ≠ 0 := fun p =>
    mul_ne_zero (ha0 _) ((Units.isUnit _).map PadicInt.toZMod).ne_zero
  have ptinj : Function.Injective pt := fun p p' h => (hbij _ (pt0 p)).unique rfl h
  obtain ⟨w, hw, hξw⟩ : ∃ w : O⟦X⟧, IsUnit w ∧ ξ = X ^ Nat.card Δ * w := by
    obtain ⟨u, hu⟩ := hξ.symm
    exact ⟨u, u.isUnit, hu.symm⟩
  have hval : ∀ τ (δ : Δ), ev (pt (τ, δ)) ξ = ev (a τ) ξ := by
    intro τ δ
    rw [← ev_unique ((ev (a τ)).comp (act O ((δ : ℤ_[l]ˣ) : ℤ_[l]))) _ _
      (ev_act_X ζ hζ.pow_eq_one _ _ (hevX _) _) (hev (pt (τ, δ))) ξ, AlgHom.comp_apply,
      hinv _ δ.2]
  have hϖ : ∀ τ, Associated (ev (a τ) ξ) ((ζ - 1) ^ Nat.card Δ) := by
    intro τ
    rw [hξw, map_mul, map_pow, hevX]
    exact (associated_mul_isUnit_left_iff (hw.map _)).2 (assoc_val ζ hζ _ (ha0 τ)).symm.pow_pow
  have hfac : ∀ τ, ∃ q, IsUnit q ∧
      ξ - C (ev (a τ) ξ) = (∏ δ : Δ, (X - C (ζ ^ (pt (τ, δ)).val - 1))) * q := by
    intro τ
    obtain ⟨q, hq⟩ := prod_dvd (fun δ : Δ => ζ ^ (pt (τ, δ)).val - 1) (fun δ => ev (pt (τ, δ)))
      (fun δ => hevX _) (fun δ => hev _)
      (fun δ δ' h => (Prod.ext_iff.1 (ptinj (hinj h))).2) Finset.univ (ξ - C (ev (a τ) ξ))
      (fun δ _ => by rw [map_sub, ev_C, hval, sub_self])
    refine ⟨q, isUnit_quot _ (fun δ => hz _) ξ q _ ?_ (by rwa [← Nat.card_eq_fintype_card]) hq, hq⟩
    exact Ideal.mem_of_dvd _ ((dvd_pow_self _ Nat.card_pos.ne').trans (hϖ τ).symm.dvd) hm
  choose q hqu hq using hfac
  refine ⟨e, fun τ => ev (a τ) ξ, hes, fun τ => ?_, fun τ τ' h => ?_, ?_, fun τ => ?_⟩
  · refine (hϖ τ).pow_pow.trans ?_
    rw [← pow_mul, mul_comm, hes]
    exact assoc_l ζ hζ
  · refine Associated.trans ?_ (hϖ τ).symm
    rw [hξw]
    exact assoc_sub hl ζ hm _ w hw _ _ (hpow τ τ' h) _ _ (hevX _) (hevX _)
  · simp only [hq]
    rw [Finset.prod_mul_distrib, ← Fintype.prod_prod_type
      (fun p : Fin e × Δ => (X - C (ζ ^ (pt p).val - 1) : O⟦X⟧)), lvl_eq_prod ζ hζ]
    refine (associated_mul_isUnit_left_iff (IsUnit.prod_univ_iff.2 hqu)).2 (Associated.of_eq ?_)
    refine Finset.prod_bij (fun p _ => pt p) (fun p _ => by simpa using pt0 p)
      (fun p _ p' _ h => ptinj h) (fun b hb => ?_) (fun _ _ => rfl)
    obtain ⟨p, hp, -⟩ := hbij b (Finset.ne_of_mem_erase hb)
    exact ⟨p, Finset.mem_univ _, hp.symm⟩
  · refine ⟨ζ ^ (pt (τ, 1)).val,
      (∏ δ ∈ Finset.univ.erase 1, (X - C (ζ ^ (pt (τ, δ)).val - 1))) * q τ,
      hζ.pow_of_coprime _ (coprime_val _ (pt0 _)), ?_, fun h => ?_⟩
    · rw [hq, ← Finset.mul_prod_erase _ _ (Finset.mem_univ (1 : Δ)), mul_assoc]
    · have h1 := map_dvd (ev (pt (τ, 1))) h
      rw [map_sub, hevX, ev_C, sub_self, zero_dvd_iff, map_mul, map_prod] at h1
      refine mul_ne_zero (Finset.prod_ne_zero_iff.2 fun δ hδ => ?_) ((hqu τ).map _).ne_zero h1
      rw [map_sub, hevX, ev_C, sub_ne_zero]
      exact fun h2 => Finset.ne_of_mem_erase hδ (Prod.ext_iff.1 (ptinj (hinj h2))).2.symm

end GlobalTheory.CycRoots
