import Mathlib
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSpecMax
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PChartDomain
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

set_option linter.unusedSectionVars false

namespace SpecChart

/- English proof (translation)
Take the linear combination `(-ci) * h + u * hc`.
-/
theorem solve_inl {L : Type*} [CommRing L] {u x ci S : L} (h : u * x + S = 0) (hc : ci * x = 1) :
    -(ci * S) = u := by
  linear_combination (-ci) * h + u * hc

/- English proof (translation)
Take the linear combination `(-ci) * h + u * hc`.
-/
theorem solve_inr {L : Type*} [CommRing L] {u x ci S : L} (h : u * x + S = 1) (hc : ci * x = 1) :
    ci * (1 - S) = u := by
  linear_combination (-ci) * h + u * hc

variable {K : Type} [Field K] [NumberField K] {n : ℕ} (e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
  (j : Fin n)

abbrev FreePar : Type := (Fin e × {m : Fin n // m ≠ j}) ⊕ {m : Fin n // m ≠ j}

def FreePar.val : FreePar e j → Par e n
  | .inl (i, m) => .inl (i, m.1)
  | .inr m => .inr m.1

abbrev Base : Type := ChartDomain.Base (integralModel I) j

abbrev Poly : Type := MvPolynomial (FreePar e j) (Base I j)

def toBase : MvPolynomial (Fin n) (𝓞 K) →+* Base I j :=
  (algebraMap _ (Base I j)).comp (Ideal.Quotient.mk (integralModel I))

def cx (l : Fin n) : Poly e I j := C (toBase I j (X l))

def cinv : Poly e I j := C (IsLocalization.Away.invSelf (Ideal.Quotient.mk (integralModel I) (X j)))

/- English proof (translation)
Rewrite using `[cinv, cx, ← map_mul, toBase, RingHom.comp_apply, mul_comm, IsLocalization.Away.mul_invSelf, map_one]`.
-/
theorem cinv_mul_cx : cinv e I j * cx e I j j = 1 := by
  rw [cinv, cx, ← map_mul, toBase, RingHom.comp_apply, mul_comm, IsLocalization.Away.mul_invSelf, map_one]

def val : Par e n → Poly e I j
  | .inl (i, l) => if h : l = j then -(cinv e I j * ∑ m : {m : Fin n // m ≠ j}, X (.inl (i, m)) * cx e I j m)
      else X (.inl (i, ⟨l, h⟩))
  | .inr l => if h : l = j then cinv e I j * (1 - ∑ m : {m : Fin n // m ≠ j}, X (.inr m) * cx e I j m)
      else X (.inr ⟨l, h⟩)

/- English proof (translation)
Apply the tactic sequence `rcases y with ⟨i, m⟩ | m <;> simp [FreePar.val, val, m.2]`.
-/
theorem val_free (y : FreePar e j) : val e I j (FreePar.val e j y) = X y := by
  rcases y with ⟨i, m⟩ | m <;> simp [FreePar.val, val, m.2]

def σ : MvPolynomial (Par e n) (𝓞 K) →+* Poly e I j :=
  eval₂Hom (C.comp ((toBase I j).comp C)) (val e I j)

/- English proof (translation)
The claim follows from `eval₂Hom_X' _ _ _`.
-/
theorem σ_X (p : Par e n) : σ e I j (X p) = val e I j p := eval₂Hom_X' _ _ _

/- English proof (translation)
Simplify using `[σ]`.
-/
theorem σ_C (c : 𝓞 K) : σ e I j (C c) = C (toBase I j (C c)) := by simp [σ]

/- English proof (translation)
Rewrite using `[Fintype.sum_eq_add_sum_subtype_ne _ j]`. Establish `h : ∀ m : {m : Fin n // m ≠ j}, val e I j (.inl (i, m.1)) = X (.inl (i, m))` using `fun m => by`. Simplify using `[val, m.2]`. Simplify using `only [h]`. Simplify using `only [val, dite_true]`.

Take the linear combination `(-(∑ m : {m : Fin n // m ≠ j}, X (.inl (i, m)) * cx e I j m)) * cinv_mul_cx e I j`.
-/
theorem sum_val_inl (i : Fin e) : ∑ m, val e I j (.inl (i, m)) * cx e I j m = 0 := by
  rw [Fintype.sum_eq_add_sum_subtype_ne _ j]
  have h : ∀ m : {m : Fin n // m ≠ j}, val e I j (.inl (i, m.1)) = X (.inl (i, m)) := fun m => by
    simp [val, m.2]
  simp only [h]
  simp only [val, dite_true]
  linear_combination (-(∑ m : {m : Fin n // m ≠ j}, X (.inl (i, m)) * cx e I j m)) * cinv_mul_cx e I j

/- English proof (translation)
Rewrite using `[Fintype.sum_eq_add_sum_subtype_ne _ j]`. Establish `h : ∀ m : {m : Fin n // m ≠ j}, val e I j (.inr m.1) = X (.inr m)` using `fun m => by`. Simplify using `[val, m.2]`. Simplify using `only [h]`. Simplify using `only [val, dite_true]`.

Take the linear combination `(1 - ∑ m : {m : Fin n // m ≠ j}, X (.inr m) * cx e I j m) * cinv_mul_cx e I j`.
-/
theorem sum_val_inr : ∑ m, val e I j (.inr m) * cx e I j m - 1 = 0 := by
  rw [Fintype.sum_eq_add_sum_subtype_ne _ j]
  have h : ∀ m : {m : Fin n // m ≠ j}, val e I j (.inr m.1) = X (.inr m) := fun m => by
    simp [val, m.2]
  simp only [h]
  simp only [val, dite_true]
  linear_combination (1 - ∑ m : {m : Fin n // m ≠ j}, X (.inr m) * cx e I j m) * cinv_mul_cx e I j

variable (W : Ideal (MvPolynomial (Fin n) (𝓞 K)))

def Wb : Ideal (Base I j) :=
  (W.map (Ideal.Quotient.mk (integralModel I))).map (algebraMap _ (Base I j))

def Q : Ideal (Poly e I j) :=
  RingHom.ker (MvPolynomial.map (Ideal.Quotient.mk (Wb I j W)) :
    Poly e I j →+* MvPolynomial (FreePar e j) (Base I j ⧸ Wb I j W))

/- English proof (translation)
Rewrite using `[Q, MvPolynomial.ker_map, Ideal.mk_ker]`.
-/
theorem Q_eq : Q e I j W = (Wb I j W).map C := by
  rw [Q, MvPolynomial.ker_map, Ideal.mk_ker]

variable {I W}

/- English proof (translation)
Establish `h2 : g ∈ Ideal.comap (Ideal.Quotient.mk (integralModel I)) (W.map (Ideal.Quotient.mk _))` using `h`. Rewrite `h2` using `[Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hPW]`. Conclude with `h2`.
-/
theorem mem_of_mk_mem [W.IsPrime] (hPW : integralModel I ≤ W) {g : MvPolynomial (Fin n) (𝓞 K)}
    (h : Ideal.Quotient.mk (integralModel I) g ∈ W.map (Ideal.Quotient.mk _)) : g ∈ W := by
  have h2 : g ∈ Ideal.comap (Ideal.Quotient.mk (integralModel I)) (W.map (Ideal.Quotient.mk _)) := h
  rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
    Ideal.mk_ker, sup_eq_left.mpr hPW] at h2
  exact h2

/- English proof (translation)
The claim follows from `Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])`.
-/
theorem map_mk_isPrime [W.IsPrime] (hPW : integralModel I ≤ W) :
    (W.map (Ideal.Quotient.mk (integralModel I))).IsPrime :=
  Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])

/- English proof (translation)
Rewrite using `[Set.disjoint_left]`. Introduce and unpack `_ ⟨k, rfl⟩ hk`. Simplify using `only [SetLike.mem_coe] at hk`. Rewrite `hk` using `[← map_pow]`. Conclude with `hXj (Ideal.IsPrime.mem_of_pow_mem ‹_› k (mem_of_mk_mem hPW hk))`.
-/
theorem disjoint_powers [W.IsPrime] (hPW : integralModel I ≤ W) (hXj : X j ∉ W) :
    Disjoint (↑(Submonoid.powers (Ideal.Quotient.mk (integralModel I) (X j))) :
        Set (MvPolynomial (Fin n) (𝓞 K) ⧸ integralModel I))
      ↑(W.map (Ideal.Quotient.mk (integralModel I))) := by
  rw [Set.disjoint_left]
  rintro _ ⟨k, rfl⟩ hk
  simp only [SetLike.mem_coe] at hk
  rw [← map_pow] at hk
  exact hXj (Ideal.IsPrime.mem_of_pow_mem ‹_› k (mem_of_mk_mem hPW hk))

/- English proof (translation)
The claim follows from `have := map_mk_isPrime hPW IsLocalization.isPrime_of_isPrime_disjoint _ _ _ this (disjoint_powers j hPW hXj)`.
-/
theorem Wb_isPrime [W.IsPrime] (hPW : integralModel I ≤ W) (hXj : X j ∉ W) : (Wb I j W).IsPrime :=
  have := map_mk_isPrime hPW
  IsLocalization.isPrime_of_isPrime_disjoint _ _ _ this (disjoint_powers j hPW hXj)

/- English proof (translation)
Use `map_mk_isPrime hPW` as an intermediate fact. Establish `h2` using `IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers _) (Base I j) this (disjoint_powers j hPW hXj)`. Apply `mem_of_mk_mem hPW` to reduce the goal to its premises. Rewrite using `[← h2]`. Conclude with `h`.
-/
theorem mem_of_toBase_mem [W.IsPrime] (hPW : integralModel I ≤ W) (hXj : X j ∉ W)
    {g : MvPolynomial (Fin n) (𝓞 K)} (h : toBase I j g ∈ Wb I j W) : g ∈ W := by
  have := map_mk_isPrime hPW
  have h2 := IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers _) (Base I j) this
    (disjoint_powers j hPW hXj)
  apply mem_of_mk_mem hPW
  rw [← h2]
  exact h

/- English proof (translation)
Use `Wb_isPrime j hPW hXj` as an intermediate fact. Conclude with `RingHom.ker_isPrime _`.
-/
theorem Q_isPrime [W.IsPrime] (hPW : integralModel I ≤ W) (hXj : X j ∉ W) : (Q e I j W).IsPrime := by
  have := Wb_isPrime j hPW hXj
  exact RingHom.ker_isPrime _

/- English proof (translation)
Rewrite using `[Q_eq]`. Conclude with `Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hg))`.
-/
theorem C_toBase_mem_Q {g : MvPolynomial (Fin n) (𝓞 K)} (hg : g ∈ W) : C (toBase I j g) ∈ Q e I j W := by
  rw [Q_eq]
  exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hg))

/- English proof (translation)
Rewrite `h` using `[Q, RingHom.mem_ker, map_C, C_eq_zero, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `mem_of_toBase_mem j hPW hXj h`.
-/
theorem mem_of_C_toBase_mem_Q [W.IsPrime] (hPW : integralModel I ≤ W) (hXj : X j ∉ W)
    {g : MvPolynomial (Fin n) (𝓞 K)} (h : C (toBase I j g) ∈ Q e I j W) : g ∈ W := by
  rw [Q, RingHom.mem_ker, map_C, C_eq_zero, Ideal.Quotient.eq_zero_iff_mem] at h
  exact mem_of_toBase_mem j hPW hXj h

variable {v : HeightOneSpectrum (𝓞 K)}

/- English proof (translation)
Introduce `g hg` and use `by rw [RingHom.mem_ker, toSecB, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem] exact Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hg))`.
-/
theorem toSecB_le : integralModel I ≤ RingHom.ker (toSecB e I v) := fun g hg => by
  rw [RingHom.mem_ker, toSecB, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hg))

/- English proof (translation)
Establish `h : Ideal.Quotient.mk (secIdeal (modelR e I v) (parY e n v)) (secForm (parY e n v) i) = 0` using `Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩)))`. Rewrite using `[← h, secForm, linForm, map_sum]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Use `congr 1`.

Simplify using `[toSecB]`.
-/
theorem secB_secForm (i : Fin e) :
    ∑ m, algebraMap (ParDVR e n v) (SecB e I v) (parY e n v (.inl (i, m))) * toSecB e I v (X m) = 0 := by
  have h : Ideal.Quotient.mk (secIdeal (modelR e I v) (parY e n v)) (secForm (parY e n v) i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩)))
  rw [← h, secForm, linForm, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul]
  congr 1
  simp [toSecB]

/- English proof (translation)
Establish `h : Ideal.Quotient.mk (secIdeal (modelR e I v) (parY e n v)) (chartForm (parY e n v)) = 1`. Rewrite using `[← sub_eq_zero, ← map_one (Ideal.Quotient.mk _), ← map_sub, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)`. Rewrite using `[← h, chartForm, linForm, map_sum]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations.

Rewrite using `[map_mul]`. Use `congr 1`. Simplify using `[toSecB]`.
-/
theorem secB_chartForm :
    ∑ m, algebraMap (ParDVR e n v) (SecB e I v) (parY e n v (.inr m)) * toSecB e I v (X m) = 1 := by
  have h : Ideal.Quotient.mk (secIdeal (modelR e I v) (parY e n v)) (chartForm (parY e n v)) = 1 := by
    rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk _), ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  rw [← h, chartForm, linForm, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul]
  congr 1
  simp [toSecB]

variable (𝔫 : Ideal (SecB e I v)) [𝔫.IsPrime]

def quotToBn : MvPolynomial (Fin n) (𝓞 K) ⧸ integralModel I →+* Localization.AtPrime 𝔫 :=
  Ideal.Quotient.lift _ ((algebraMap (SecB e I v) (Localization.AtPrime 𝔫)).comp (toSecB e I v))
    (fun g hg => by rw [RingHom.comp_apply, RingHom.mem_ker.mp (toSecB_le e hg), map_zero])

/- English proof (translation)
The claim follows from `Ideal.Quotient.lift_mk _ _ _`.
-/
theorem quotToBn_mk (g : MvPolynomial (Fin n) (𝓞 K)) :
    quotToBn e 𝔫 (Ideal.Quotient.mk _ g) = algebraMap _ (Localization.AtPrime 𝔫) (toSecB e I v g) :=
  Ideal.Quotient.lift_mk _ _ _

def parB (p : Par e n) : Localization.AtPrime 𝔫 :=
  algebraMap (SecB e I v) _ (algebraMap (ParDVR e n v) (SecB e I v) (parY e n v p))

variable {e j 𝔫}

def baseToBn (hj : toSecB e I v (X j) ∉ 𝔫) : Base I j →+* Localization.AtPrime 𝔫 :=
  IsLocalization.Away.lift (Ideal.Quotient.mk (integralModel I) (X j)) (g := quotToBn e 𝔫)
    (by
      rw [quotToBn_mk]
      exact IsLocalization.map_units (Localization.AtPrime 𝔫) (⟨toSecB e I v (X j), hj⟩ : 𝔫.primeCompl))

/- English proof (translation)
Rewrite using `[toBase, RingHom.comp_apply, baseToBn, IsLocalization.Away.lift_eq, quotToBn_mk]`.
-/
theorem baseToBn_toBase (hj : toSecB e I v (X j) ∉ 𝔫) (g : MvPolynomial (Fin n) (𝓞 K)) :
    baseToBn hj (toBase I j g) = algebraMap _ _ (toSecB e I v g) := by
  rw [toBase, RingHom.comp_apply, baseToBn, IsLocalization.Away.lift_eq, quotToBn_mk]

def Φ (hj : toSecB e I v (X j) ∉ 𝔫) : Poly e I j →+* Localization.AtPrime 𝔫 :=
  eval₂Hom (baseToBn hj) fun y => parB e 𝔫 (FreePar.val e j y)

/- English proof (translation)
The claim follows from `eval₂Hom_C _ _ _`.
-/
theorem Φ_C (hj : toSecB e I v (X j) ∉ 𝔫) (b : Base I j) : Φ hj (C b) = baseToBn hj b := eval₂Hom_C _ _ _

/- English proof (translation)
The claim follows from `eval₂Hom_X' _ _ _`.
-/
theorem Φ_X (hj : toSecB e I v (X j) ∉ 𝔫) (y : FreePar e j) : Φ hj (X y) = parB e 𝔫 (FreePar.val e j y) :=
  eval₂Hom_X' _ _ _

/- English proof (translation)
Rewrite using `[cx, Φ_C, baseToBn_toBase]`.
-/
theorem Φ_cx (hj : toSecB e I v (X j) ∉ 𝔫) (l : Fin n) :
    Φ hj (cx e I j l) = algebraMap _ _ (toSecB e I v (X l)) := by
  rw [cx, Φ_C, baseToBn_toBase]

/- English proof (translation)
Rewrite using `[← Φ_cx hj, ← map_mul, cinv_mul_cx, map_one]`.
-/
theorem Φ_cinv_mul (hj : toSecB e I v (X j) ∉ 𝔫) :
    Φ hj (cinv e I j) * algebraMap _ _ (toSecB e I v (X j)) = 1 := by
  rw [← Φ_cx hj, ← map_mul, cinv_mul_cx, map_one]

/- English proof (translation)
Establish `hc` using `Φ_cinv_mul hj`. Break down `p with ⟨i, l⟩ | l` into its components or cases. Distinguish the cases in `hl : l = j`. Substitute `hl` using the available equality. Establish `h` using `congrArg (algebraMap (SecB e I v) (Localization.AtPrime 𝔫)) (secB_secForm e (I := I) (v := v) i)`.

Rewrite `h` using `[map_sum, map_zero, Fintype.sum_eq_add_sum_subtype_ne _ l]`. Simplify using `only [map_mul] at h`. Simplify using `only [val, dite_true, map_neg, map_mul, map_sum, Φ_X, Φ_cx, FreePar.val, parB]`. Conclude with `solve_inl (L := Localization.AtPrime 𝔫) h hc`. Simplify using `only [val, hl, dite_false, Φ_X, FreePar.val]`.

Distinguish the cases in `hl : l = j`. Substitute `hl` using the available equality. Establish `h` using `congrArg (algebraMap (SecB e I v) (Localization.AtPrime 𝔫)) (secB_chartForm e (I := I) (v := v))`. Rewrite `h` using `[map_sum, map_one, Fintype.sum_eq_add_sum_subtype_ne _ l]`. Simplify using `only [map_mul] at h`.

Simplify using `only [val, dite_true, map_sub, map_one, map_mul, map_sum, Φ_X, Φ_cx, FreePar.val, parB]`. Conclude with `solve_inr (L := Localization.AtPrime 𝔫) h hc`. Simplify using `only [val, hl, dite_false, Φ_X, FreePar.val]`.
-/
theorem Φ_val (hj : toSecB e I v (X j) ∉ 𝔫) (p : Par e n) : Φ hj (val e I j p) = parB e 𝔫 p := by
  have hc := Φ_cinv_mul hj
  rcases p with ⟨i, l⟩ | l
  · by_cases hl : l = j
    · subst hl
      have h := congrArg (algebraMap (SecB e I v) (Localization.AtPrime 𝔫)) (secB_secForm e (I := I) (v := v) i)
      rw [map_sum, map_zero, Fintype.sum_eq_add_sum_subtype_ne _ l] at h
      simp only [map_mul] at h
      simp only [val, dite_true, map_neg, map_mul, map_sum, Φ_X, Φ_cx, FreePar.val, parB]
      exact solve_inl (L := Localization.AtPrime 𝔫) h hc
    · simp only [val, hl, dite_false, Φ_X, FreePar.val]
  · by_cases hl : l = j
    · subst hl
      have h := congrArg (algebraMap (SecB e I v) (Localization.AtPrime 𝔫)) (secB_chartForm e (I := I) (v := v))
      rw [map_sum, map_one, Fintype.sum_eq_add_sum_subtype_ne _ l] at h
      simp only [map_mul] at h
      simp only [val, dite_true, map_sub, map_one, map_mul, map_sum, Φ_X, Φ_cx, FreePar.val, parB]
      exact solve_inr (L := Localization.AtPrime 𝔫) h hc
    · simp only [val, hl, dite_false, Φ_X, FreePar.val]

/- English proof (translation)
Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `c`. Simplify using `only [RingHom.comp_apply, σ_C, Φ_C, baseToBn_toBase, toSecB_C]`. Introduce `p`. Simplify using `only [RingHom.comp_apply, σ_X, Φ_val, parB, parY]`.
-/
theorem Φ_σ (hj : toSecB e I v (X j) ∉ 𝔫) :
    (Φ hj).comp (σ e I j) = (algebraMap (SecB e I v) (Localization.AtPrime 𝔫)).comp
      ((algebraMap (ParDVR e n v) (SecB e I v)).comp (algebraMap _ (ParDVR e n v))) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp only [RingHom.comp_apply, σ_C, Φ_C, baseToBn_toBase, toSecB_C]
  · intro p
    simp only [RingHom.comp_apply, σ_X, Φ_val, parB, parY]

end SpecChart

end

end GroundTheory.Heights₂.Heights.Vertical
