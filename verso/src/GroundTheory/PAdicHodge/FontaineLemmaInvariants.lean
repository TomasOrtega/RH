import Mathlib
import GroundTheory.PAdicHodge.FontaineLemma
import GroundTheory.PAdicHodge.BCrisRegular
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open _root_.WittVector Polynomial

section Abstract

variable {R S T L : Type*} [CommRing R] [CommRing S] [CommRing T] [CommRing L]

/- English proof (translation)
Establish `hct : ∀ n : ℕ, f^[n] t = c ^ n * t`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih => rw [Function.iterate_succ_apply', ih, map_mul, map_pow, hc, ht, pow_succ]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[iterate_map_mul, iterate_map_pow, hct]`.
-/
theorem iterate_pow_mul_eq_of_map_eq (f : R →+* R) {t c : R} (hc : f c = c) (ht : f t = c * t)
    (x : R) (m n : ℕ) : f^[n] (t ^ m * x) = (c ^ n * t) ^ m * f^[n] x := by
  have hct : ∀ n : ℕ, f^[n] t = c ^ n * t := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Function.iterate_succ_apply', ih, map_mul, map_pow, hc, ht, pow_succ]; ring
  rw [iterate_map_mul, iterate_map_pow, hct]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih => rw [Function.iterate_succ_apply', ih, map_mul, map_pow, hc, ht, pow_succ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem iterate_map_eq_pow_mul (f : R →+* R) {t c : R} (hc : f c = c) (ht : f t = c * t) (n : ℕ) :
    f^[n] t = c ^ n * t := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', ih, map_mul, map_pow, hc, ht, pow_succ]; ring

/- English proof (translation)
Establish `hqm : IsUnit (q ^ (m + 1))` using `hq.pow _`. Use `⟨w * ↑hqm.unit⁻¹, ?_⟩` and prove the remaining obligations. Establish `h1 : c ^ (m + 1) * g ↑hqm.unit⁻¹ = 1`. Rewrite using `[← hgq, ← map_pow, ← map_mul, IsUnit.mul_val_inv, map_one]`. Establish `h2 : g w = c ^ (m + 1) * t ^ m * u` using `ht.mul_right_cancel (by rw [h]; ring)`.

Rewrite using `[map_mul, h2]`. Take the linear combination `t ^ m * u * h1`.
-/
theorem exists_map_eq_pow_mul_of_mul_eq (g : S →+* R) {t c u : R} (ht : IsUnit t) {q : S}
    (hq : IsUnit q) (hgq : g q = c) {w : S} {m : ℕ} (h : g w * t = (c * t) ^ (m + 1) * u) :
    ∃ z : S, g z = t ^ m * u := by
  have hqm : IsUnit (q ^ (m + 1)) := hq.pow _
  refine ⟨w * ↑hqm.unit⁻¹, ?_⟩
  have h1 : c ^ (m + 1) * g ↑hqm.unit⁻¹ = 1 := by
    rw [← hgq, ← map_pow, ← map_mul, IsUnit.mul_val_inv, map_one]
  have h2 : g w = c ^ (m + 1) * t ^ m * u :=
    ht.mul_right_cancel (by rw [h]; ring)
  rw [map_mul, h2]
  linear_combination t ^ m * u * h1

/- English proof (translation)
Establish `e : a = (c' ^ n * τ) ^ (k + 1) * κ` using `hj (by rw [h]; simp only [map_mul, map_pow, hc, ht, hx])`. Rewrite using `[e, map_mul, map_pow, map_mul, hτ, mul_zero, zero_pow (Nat.succ_ne_zero k), zero_mul]`.
-/
theorem map_eq_zero_of_eq_pow_mul {D : Type*} [CommRing D] (ι : S →+* T) (j : D →+* T)
    (hj : Function.Injective j) (θ : D →+* L) {a : D} {c t x : S} {c' τ κ : D} {n k : ℕ}
    (h : j a = ι ((c ^ n * t) ^ (k + 1) * x)) (hc : ι c = j c') (ht : ι t = j τ) (hx : ι x = j κ)
    (hτ : θ τ = 0) : θ a = 0 := by
  have e : a = (c' ^ n * τ) ^ (k + 1) * κ := hj (by rw [h]; simp only [map_mul, map_pow, hc, ht, hx])
  rw [e, map_mul, map_pow, map_mul, hτ, mul_zero, zero_pow (Nat.succ_ne_zero k), zero_mul]

/- English proof (translation)
Introduce `m`. Proceed by induction on `m with`. Consider the case `zero`. Introduce and unpack `x - ⟨y, hy⟩`. Conclude with `⟨y, by rw [hy, pow_zero, one_mul, Function.iterate_zero_apply]⟩`.

Consider the case `succ m ih`. Introduce `x hx hex`. Take `⟨z, hz⟩` from `ih (f x) (hP x hx) (step m x hx hex)`. Conclude with `⟨z, by rw [hz, Function.iterate_succ_apply]⟩`.
-/
theorem exists_eq_iterate_of_step (g : S →+* R) (f : R → R) (t : R) (P : R → Prop)
    (hP : ∀ x, P x → P (f x))
    (step : ∀ (m : ℕ) (x : R), P x → (∃ y, g y = t ^ (m + 1) * x) → ∃ z, g z = t ^ m * f x) :
    ∀ (m : ℕ) (x : R), P x → (∃ y, g y = t ^ m * x) → ∃ z, g z = f^[m] x := by
  intro m
  induction m with
  | zero =>
    rintro x - ⟨y, hy⟩
    exact ⟨y, by rw [hy, pow_zero, one_mul, Function.iterate_zero_apply]⟩
  | succ m ih =>
    intro x hx hex
    obtain ⟨z, hz⟩ := ih (f x) (hP x hx) (step m x hx hex)
    exact ⟨z, by rw [hz, Function.iterate_succ_apply]⟩

/- English proof (translation)
The claim follows from `hj (by rw [h, map_mul, map_pow, ht, hx, map_mul, map_pow])`.
-/
theorem eq_pow_mul_of_map_eq {D : Type*} [CommRing D] (ι : S →+* T) (j : D →+* T)
    (hj : Function.Injective j) {a : D} {t x : S} {τ κ : D} {m : ℕ} (h : j a = ι (t ^ m * x))
    (ht : ι t = j τ) (hx : ι x = j κ) : a = τ ^ m * κ :=
  hj (by rw [h, map_mul, map_pow, ht, hx, map_mul, map_pow])

/- English proof (translation)
Rewrite using `[map_mul, map_pow, map_mul, map_pow, hc]`.
-/
theorem map_pow_mul_pow_mul (g : S →+* R) {c : S} {c' : R} (hc : g c = c') (n m : ℕ) (t z : S) :
    g ((c ^ n * t) ^ m * z) = (c' ^ n * g t) ^ m * g z := by
  rw [map_mul, map_pow, map_mul, map_pow, hc]

def homogEval {A : Type*} [CommRing A] (f : A →+* S) (P : A[X]) (y s : S) : S :=
  ∑ i ∈ Finset.range (P.natDegree + 1), f (P.coeff i) * y ^ i * s ^ (P.natDegree - i)

/- English proof (translation)
Rewrite using `[homogEval, eval₂_eq_sum_range, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Establish `hi' : i ≤ P.natDegree` using `Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem homogEval_mul {A : Type*} [CommRing A] (f : A →+* S) (P : A[X]) (s z : S) :
    homogEval f P (s * z) s = s ^ P.natDegree * P.eval₂ f z := by
  rw [homogEval, eval₂_eq_sum_range, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ P.natDegree := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  calc f (P.coeff i) * (s * z) ^ i * s ^ (P.natDegree - i)
      = f (P.coeff i) * z ^ i * (s ^ i * s ^ (P.natDegree - i)) := by ring
    _ = s ^ P.natDegree * (f (P.coeff i) * z ^ i) := by rw [pow_mul_pow_sub _ hi']; ring

/- English proof (translation)
Simplify using `only [homogEval, map_sum, map_mul, map_pow, hf]`.
-/
theorem map_homogEval {A : Type*} [CommRing A] (f : A →+* S) (P : A[X]) (y s : S) (g : S →+* T)
    (f' : A →+* T) (hf : ∀ a, g (f a) = f' a) :
    g (homogEval f P y s) = homogEval f' P (g y) (g s) := by
  simp only [homogEval, map_sum, map_mul, map_pow, hf]

/- English proof (translation)
Take `⟨⟨a, s⟩, hs⟩` from `IsLocalization.surj (Submonoid.powers t) x`. Take `⟨m, hm⟩` from `s.2`. Use `⟨m, a, ?_⟩` and prove the remaining obligations. Rewrite using `[← hs, ← hm, map_pow, mul_comm]`.
-/
theorem Localization.Away.exists_algebraMap_eq_pow_mul (t : R) (x : Localization.Away t) :
    ∃ (m : ℕ) (y : R), algebraMap R (Localization.Away t) y =
      algebraMap R (Localization.Away t) t ^ m * x := by
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers t) x
  obtain ⟨m, hm⟩ := s.2
  refine ⟨m, a, ?_⟩
  rw [← hs, ← hm, map_pow, mul_comm]

/- English proof (translation)
Rewrite using `[map_pow, map_mul, map_pow, hc]`.
-/
theorem map_pow_mul_pow (g : S →+* R) {c : S} {c' : R} (hc : g c = c') (n m : ℕ) (t : S) :
    g ((c ^ n * t) ^ m) = (c' ^ n * g t) ^ m := by
  rw [map_pow, map_mul, map_pow, hc]

/- English proof (translation)
Establish `h1` using `congrArg g h`. Rewrite `h1` using `[map_mul, map_pow, map_zero]`. Conclude with `(mul_eq_zero.1 h1).resolve_left (pow_ne_zero _ hc)`.
-/
theorem map_eq_zero_of_pow_mul_eq_zero [IsDomain T] (g : S →+* T) {c z : S} {d : ℕ}
    (h : c ^ d * z = 0) (hc : g c ≠ 0) : g z = 0 := by
  have h1 := congrArg g h
  rw [map_mul, map_pow, map_zero] at h1
  exact (mul_eq_zero.1 h1).resolve_left (pow_ne_zero _ hc)

end Abstract

namespace ACris

section Generic

variable {F : Type*} [NontriviallyNormedField F] [IsUltrametricDist F]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField F p]
variable {ε : PreTilt (normInteger F) p} (hε : PreTilt.untilt ε = 1)

abbrev periodTCris : BCris hε :=
  algebraMap (BCrisPlus F p) (BCris hε) (algebraMap (ACris F p) (BCrisPlus F p) (periodT hε))

/- English proof (translation)
The claim follows from `IsLocalization.Away.algebraMap_isUnit _`.
-/
theorem isUnit_periodTCris : IsUnit (periodTCris hε) :=
  IsLocalization.Away.algebraMap_isUnit _

/- English proof (translation)
The claim follows from `((phiB_algebraMap hε _).trans (congrArg _ ((phiPlus_algebraMap _).trans (congrArg _ (phi_periodT_eq_mul hε))))).trans (by simp only [map_mul, map_natCast])`.
-/
theorem phiB_periodTCris : phiB hε (periodTCris hε) = (p : BCris hε) * periodTCris hε :=
  ((phiB_algebraMap hε _).trans
    (congrArg _ ((phiPlus_algebraMap _).trans (congrArg _ (phi_periodT_eq_mul hε))))).trans
    (by simp only [map_mul, map_natCast])

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rfl`. Consider the case `succ n ih => simp only [Function.iterate_succ_apply', ih, phiB_algebraMap]`.
-/
theorem iterate_phiB_algebraMap (n : ℕ) (y : BCrisPlus F p) :
    (phiB hε)^[n] (algebraMap (BCrisPlus F p) (BCris hε) y) =
      algebraMap (BCrisPlus F p) (BCris hε) ((phiPlus F p)^[n] y) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', ih, phiB_algebraMap]

/- English proof (translation)
The claim follows from `(iterate_phiB_algebraMap hε n y).symm.trans ((congrArg (phiB hε)^[n] hy).trans (iterate_pow_mul_eq_of_map_eq (phiB hε) (map_natCast _ p) (phiB_periodTCris hε) x m n))`.
-/
theorem algebraMap_iterate_phiPlus_eq {x : BCris hε} {m : ℕ} {y : BCrisPlus F p}
    (hy : algebraMap (BCrisPlus F p) (BCris hε) y = periodTCris hε ^ m * x) (n : ℕ) :
    algebraMap (BCrisPlus F p) (BCris hε) ((phiPlus F p)^[n] y) =
      ((p : BCris hε) ^ n * periodTCris hε) ^ m * (phiB hε)^[n] x :=
  (iterate_phiB_algebraMap hε n y).symm.trans ((congrArg (phiB hε)^[n] hy).trans
    (iterate_pow_mul_eq_of_map_eq (phiB hε) (map_natCast _ p) (phiB_periodTCris hε) x m n))

/- English proof (translation)
The claim follows from `iterate_map_eq_pow_mul (phiPlus F p) (map_natCast _ p) ((phiPlus_algebraMap _).trans ((congrArg _ (phi_periodT_eq_mul hε)).trans (by simp only [map_mul, map_natCast]))) n`.
-/
theorem iterate_phiPlus_periodT (n : ℕ) :
    (phiPlus F p)^[n] (algebraMap (ACris F p) (BCrisPlus F p) (periodT hε)) =
      (p : BCrisPlus F p) ^ n * algebraMap (ACris F p) (BCrisPlus F p) (periodT hε) :=
  iterate_map_eq_pow_mul (phiPlus F p) (map_natCast _ p)
    ((phiPlus_algebraMap _).trans ((congrArg _ (phi_periodT_eq_mul hε)).trans
      (by simp only [map_mul, map_natCast]))) n

/- English proof (translation)
The claim follows from `Localization.Away.exists_algebraMap_eq_pow_mul _ x`.
-/
theorem exists_algebraMap_eq_periodTCris_pow_mul (x : BCris hε) :
    ∃ (m : ℕ) (y : BCrisPlus F p), algebraMap (BCrisPlus F p) (BCris hε) y = periodTCris hε ^ m * x :=
  Localization.Away.exists_algebraMap_eq_pow_mul _ x

/- English proof (translation)
The claim follows from `iterate_map_pow _ _ _ _`.
-/
theorem iterate_phiPlus_pow (n k : ℕ) (z : BCrisPlus F p) :
    (phiPlus F p)^[n] (z ^ k) = ((phiPlus F p)^[n] z) ^ k :=
  iterate_map_pow _ _ _ _

variable [CharZero F]
  (hζ : PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt (normInteger F) p) p).symm ε) ≠ 1)

include hζ in
set_option maxHeartbeats 1600000 in

/- English proof (translation)
Take `⟨w, hw⟩` from `Ideal.mem_span_singleton'.1 (phiPlus_mem_span_periodT hε hζ hθ)`. Establish `hp1 : IsUnit (p : BCrisPlus F p)`. Use `IsLocalization.Away.algebraMap_isUnit (S := BCrisPlus F p) (p : ACris F p)` as an intermediate fact. Simplify `this` using `only [map_natCast]`. Establish `h : algebraMap (BCrisPlus F p) (BCris hε) w * periodTCris hε = ((p : BCris hε) * periodTCris hε) ^ (m + 1) * phiB hε x` using `(map_mul _ w _).symm.trans ((congrArg _ hw).trans ((phiB_algebraMap hε y).symm.trans ((congrArg (phiB hε) hy).trans (iterate_pow_mul_eq_of_map_eq (phiB hε) (map_natCast _ p) (phiB_periodTCris hε) x (m + 1) 1) |>.trans (by rw [pow_one]; rfl))))`.

Conclude with `exists_map_eq_pow_mul_of_mul_eq _ (isUnit_periodTCris hε) hp1 (map_natCast _ p) h`.
-/
theorem exists_algebraMap_eq_periodTCris_pow_mul_phiB {x : BCris hε} {m : ℕ} {y : BCrisPlus F p}
    (hy : algebraMap (BCrisPlus F p) (BCris hε) y = periodTCris hε ^ (m + 1) * x)
    (hθ : ∀ n : ℕ, IsPerfectoidField.thetaBDeRhamPlusField (K := F) p
      (iotaPlus F p ((phiPlus F p)^[n] y)) = 0) :
    ∃ z : BCrisPlus F p, algebraMap (BCrisPlus F p) (BCris hε) z =
      periodTCris hε ^ m * phiB hε x := by
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 (phiPlus_mem_span_periodT hε hζ hθ)
  have hp1 : IsUnit (p : BCrisPlus F p) := by
    have := IsLocalization.Away.algebraMap_isUnit (S := BCrisPlus F p) (p : ACris F p)
    simpa only [map_natCast] using this

  have h : algebraMap (BCrisPlus F p) (BCris hε) w * periodTCris hε =
      ((p : BCris hε) * periodTCris hε) ^ (m + 1) * phiB hε x :=
    (map_mul _ w _).symm.trans ((congrArg _ hw).trans ((phiB_algebraMap hε y).symm.trans
      ((congrArg (phiB hε) hy).trans (iterate_pow_mul_eq_of_map_eq (phiB hε) (map_natCast _ p)
        (phiB_periodTCris hε) x (m + 1) 1) |>.trans (by rw [pow_one]; rfl))))
  exact exists_map_eq_pow_mul_of_mul_eq _ (isUnit_periodTCris hε) hp1 (map_natCast _ p) h

end Generic

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝔹" => BDeRhamPlus (normInteger ℂ_[p]) p
local notation "𝔹dR" => BDeRham (normInteger ℂ_[p]) p

variable {ε : PreTilt (normInteger ℂ_[p]) p} (hε : PreTilt.untilt ε = 1)
  (hζ : PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt (normInteger ℂ_[p]) p) p).symm ε) ≠ 1)

/- English proof (translation)
The claim follows from `(phiB_algebraMap hε _).trans (congrArg _ (phiPlus_algebraMap_padic q))`.
-/
theorem phiB_algebraMap_padic (q : ℚ_[p]) :
    phiB hε (algebraMap (BCrisPlus ℂ_[p] p) (BCris hε) (algebraMap ℚ_[p] (BCrisPlus ℂ_[p] p) q)) =
      algebraMap (BCrisPlus ℂ_[p] p) (BCris hε) (algebraMap ℚ_[p] (BCrisPlus ℂ_[p] p) q) :=
  (phiB_algebraMap hε _).trans (congrArg _ (phiPlus_algebraMap_padic q))

/- English proof (translation)
Take `⟨τ, hτ⟩` from `(Normal.minpoly_eq_iff_mem_orbit (PadicAlgCl p)).1 h`. Establish `hτ' : τ β₁ = β` using `hτ`. Rewrite using `[← hτ']`. Conclude with `gal_mem_unramifiedClosure τ h₁`.
-/
theorem mem_unramifiedClosure_of_minpoly_eq {β β₁ : PadicAlgCl p}
    (h : minpoly ℚ_[p] β = minpoly ℚ_[p] β₁) (h₁ : β₁ ∈ unramifiedClosure p) :
    β ∈ unramifiedClosure p := by
  obtain ⟨τ, hτ⟩ := (Normal.minpoly_eq_iff_mem_orbit (PadicAlgCl p)).1 h
  have hτ' : τ β₁ = β := hτ
  rw [← hτ']
  exact gal_mem_unramifiedClosure τ h₁

variable {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => exact hx`. Consider the case `succ n ih`. Conclude with `(congrArg (galB hε σ) (Function.iterate_succ_apply' _ _ _)).trans ((phiB_galB hε σ _).symm.trans ((congrArg (phiB hε) ih).trans (Function.iterate_succ_apply' _ _ _).symm))`.
-/
theorem galB_iterate_phiB (σ : Gal(PadicAlgCl p/K)) {x : BCris hε} (hx : galB hε σ x = x)
    (n : ℕ) : galB hε σ ((phiB hε)^[n] x) = (phiB hε)^[n] x := by
  induction n with
  | zero => exact hx
  | succ n ih =>
    exact (congrArg (galB hε σ) (Function.iterate_succ_apply' _ _ _)).trans
      ((phiB_galB hε σ _).symm.trans ((congrArg (phiB hε) ih).trans
        (Function.iterate_succ_apply' _ _ _).symm))

/- English proof (translation)
The claim follows from `(iotaB_algebraMap hε hζ _).trans (congrArg _ (iotaPlus_algebraMap _))`.
-/
theorem iotaB_periodTCris :
    iotaB hε hζ (periodTCris hε) = algebraMap 𝔹 𝔹dR (iota ℂ_[p] p (periodT hε)) :=
  (iotaB_algebraMap hε hζ _).trans (congrArg _ (iotaPlus_algebraMap _))

/- English proof (translation)
The claim follows from `(thetaField_iota _).trans (by rw [theta_periodT]; rfl)`.
-/
theorem thetaField_iota_periodT :
    IsPerfectoidField.thetaBDeRhamPlusField (K := ℂ_[p]) p (iota ℂ_[p] p (periodT hε)) = 0 :=
  (thetaField_iota _).trans (by rw [theta_periodT]; rfl)

include hζ in
set_option maxHeartbeats 1600000 in

/- English proof (translation)
Take `⟨y', hyfix, hy'⟩` from `exists_bCrisPlus_fixed hk`. Conclude with `⟨y', hyfix, iotaB_injective hε hζ ((iotaB_algebraMap hε hζ y').trans ((congrArg _ hy').trans hx.symm))⟩`.
-/
theorem exists_bCrisPlus_fixed_eq_of_mem_maxUnramified {x : BCris hε} {k : PadicAlgCl p}
    (hk : k ∈ maxUnramified p K) (hx : iotaB hε hζ x = algebraMap 𝔹 𝔹dR (algClToBdR p k)) :
    ∃ y' : BCrisPlus ℂ_[p] p, (∀ σ : Gal(PadicAlgCl p/K), σ • y' = y') ∧
      algebraMap (BCrisPlus ℂ_[p] p) (BCris hε) y' = x := by
  obtain ⟨y', hyfix, hy'⟩ := exists_bCrisPlus_fixed hk
  exact ⟨y', hyfix, iotaB_injective hε hζ
    ((iotaB_algebraMap hε hζ y').trans ((congrArg _ hy').trans hx.symm))⟩

variable [FiniteDimensional ℚ_[p] K]

include hζ in
set_option maxHeartbeats 1600000 in

/- English proof (translation)
Take `⟨k, hk⟩` from `bCris_fixed hε hζ ((phiB hε)^[n] x) fun σ => galB_iterate_phiB hε σ (hx σ) n`. Conclude with `map_eq_zero_of_eq_pow_mul (iotaB hε hζ) (algebraMap 𝔹 𝔹dR) (IsFractionRing.injective 𝔹 𝔹dR) (IsPerfectoidField.thetaBDeRhamPlusField (K := ℂ_[p]) p) ((iotaB_algebraMap hε hζ _).symm.trans (congrArg _ (algebraMap_iterate_phiPlus_eq hε hy n))) ((map_natCast _ p).trans (map_natCast …`.
-/
theorem thetaField_iotaPlus_iterate_eq_zero {x : BCris hε}
    (hx : ∀ σ : Gal(PadicAlgCl p/K), galB hε σ x = x) {m : ℕ} {y : BCrisPlus ℂ_[p] p}
    (hy : algebraMap (BCrisPlus ℂ_[p] p) (BCris hε) y = periodTCris hε ^ (m + 1) * x) (n : ℕ) :
    IsPerfectoidField.thetaBDeRhamPlusField (K := ℂ_[p]) p
      (iotaPlus ℂ_[p] p ((phiPlus ℂ_[p] p)^[n] y)) = 0 := by
  obtain ⟨k, hk⟩ := bCris_fixed hε hζ ((phiB hε)^[n] x) fun σ => galB_iterate_phiB hε σ (hx σ) n
  exact map_eq_zero_of_eq_pow_mul (iotaB hε hζ) (algebraMap 𝔹 𝔹dR)
    (IsFractionRing.injective 𝔹 𝔹dR) (IsPerfectoidField.thetaBDeRhamPlusField (K := ℂ_[p]) p)
    ((iotaB_algebraMap hε hζ _).symm.trans (congrArg _ (algebraMap_iterate_phiPlus_eq hε hy n)))
    ((map_natCast _ p).trans (map_natCast _ p).symm) (iotaB_periodTCris hε hζ)
    (hk.trans (algebraMap_intermediateField_bDeRham K k)) (thetaField_iota_periodT hε)

include hζ in
set_option maxHeartbeats 1600000 in

/- English proof (translation)
The claim follows from `exists_eq_iterate_of_step (algebraMap (BCrisPlus ℂ_[p] p) (BCris hε)) (phiB hε) (periodTCris hε) (fun x => ∀ σ : Gal(PadicAlgCl p/K), galB hε σ x = x) (fun x hx σ => (phiB_galB hε σ x).symm.trans (congrArg (phiB hε) (hx σ))) (fun _ _ hx ⟨_, hy⟩ => exists_algebraMap_eq_periodTCris …`.
-/
theorem exists_iterate_phiB_eq (m : ℕ) (x : BCris hε)
    (hx : ∀ σ : Gal(PadicAlgCl p/K), galB hε σ x = x)
    (hxy : ∃ y : BCrisPlus ℂ_[p] p,
      algebraMap (BCrisPlus ℂ_[p] p) (BCris hε) y = periodTCris hε ^ m * x) :
    ∃ z : BCrisPlus ℂ_[p] p, algebraMap (BCrisPlus ℂ_[p] p) (BCris hε) z = (phiB hε)^[m] x :=
  exists_eq_iterate_of_step (algebraMap (BCrisPlus ℂ_[p] p) (BCris hε)) (phiB hε) (periodTCris hε)
    (fun x => ∀ σ : Gal(PadicAlgCl p/K), galB hε σ x = x)
    (fun x hx σ => (phiB_galB hε σ x).symm.trans (congrArg (phiB hε) (hx σ)))
    (fun _ _ hx ⟨_, hy⟩ => exists_algebraMap_eq_periodTCris_pow_mul_phiB hε hζ hy
      (thetaField_iotaPlus_iterate_eq_zero hε hζ hx hy)) m x hx hxy

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rfl`. Consider the case `succ n ih => rw [Function.iterate_succ_apply', ih, phiPlus_algebraMap_padic]`.
-/
theorem iterate_phiPlus_algebraMap_padic (n : ℕ) (q : ℚ_[p]) :
    (phiPlus ℂ_[p] p)^[n] (algebraMap ℚ_[p] (BCrisPlus ℂ_[p] p) q) =
      algebraMap ℚ_[p] (BCrisPlus ℂ_[p] p) q := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, phiPlus_algebraMap_padic]

include hζ in

/- English proof (translation)
Introduce `a b h` and use `iotaPlus_injective (K := ℂ_[p]) (p := p) (IsFractionRing.injective 𝔹 𝔹dR ((iotaB_algebraMap hε hζ a).symm.trans ((congrArg (iotaB hε hζ) h).trans (iotaB_algebraMap hε hζ b))))`.
-/
theorem algebraMap_bCrisPlus_bCris_injective :
    Function.Injective (algebraMap (BCrisPlus ℂ_[p] p) (BCris hε)) := fun a b h =>
  iotaPlus_injective (K := ℂ_[p]) (p := p) (IsFractionRing.injective 𝔹 𝔹dR
    ((iotaB_algebraMap hε hζ a).symm.trans ((congrArg (iotaB hε hζ) h).trans
      (iotaB_algebraMap hε hζ b))))

include hζ in

/- English proof (translation)
Rewrite using `[iota_periodT]`. Conclude with `fontaineT_ne_zero hε hζ`.
-/
theorem iota_periodT_ne_zero : iota ℂ_[p] p (periodT hε) ≠ 0 := by
  rw [iota_periodT]
  exact fontaineT_ne_zero hε hζ

include hζ in
set_option maxHeartbeats 1600000 in

/- English proof (translation)
Take `⟨t', ht'⟩ : ∃ t', algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p) (periodT hε) = t'` from `⟨_, rfl⟩`. Take `⟨τ, hτdef⟩ : ∃ τ, iota ℂ_[p] p (periodT hε) = τ` from `⟨_, rfl⟩`. Rewrite `hφy` using `[ht']`. Rewrite `hιy` using `[hτdef]`. Establish `hτ : iotaPlus ℂ_[p] p t' = τ` using `by rw [← ht', ← hτdef]; exact iotaPlus_algebraMap _`.

Take `⟨P, hP⟩ : ∃ P, minpoly ℚ_[p] β = P` from `⟨_, rfl⟩`. Rewrite using `[hP]`. Take `⟨f, hf⟩ : ∃ f, algebraMap ℚ_[p] (BCrisPlus ℂ_[p] p) = f` from `⟨_, rfl⟩`. Take `⟨R, hR⟩ : ∃ R, homogEval f P y (t' ^ m) = R` from `⟨_, rfl⟩`. Establish `hιs : iotaPlus ℂ_[p] p (t' ^ m) = τ ^ m` using `(map_pow _ _ _).trans (congrArg (· ^ m) hτ)`.

Establish `hιR : iotaPlus ℂ_[p] p R = 0`. Establish `e1 : iotaPlus ℂ_[p] p R = homogEval (algebraMap ℚ_[p] 𝔹) P (iotaPlus ℂ_[p] p y) (iotaPlus ℂ_[p] p (t' ^ m))`. Rewrite using `[← hR]`. Conclude with `map_homogEval f P y (t' ^ m) (iotaPlus ℂ_[p] p) (algebraMap ℚ_[p] 𝔹) (fun q => by rw [← hf]; exact iotaPlus_algebraMap_padic q)`. Establish `e2 : aeval (algClToBdR p β) P = 0`.

Rewrite using `[aeval_algHom_apply, ← hP, minpoly.aeval, map_zero]`. Rewrite using `[e1, hιy, hιs, homogEval_mul, ← aeval_def, e2, mul_zero]`. Establish `hR0 : R = 0` using `iotaPlus_injective (K := ℂ_[p]) (p := p) (hιR.trans (map_zero _).symm)`. Take `⟨c, hc⟩ : ∃ c, ((p : BCrisPlus ℂ_[p] p) ^ m * t') ^ m = c` from `⟨_, rfl⟩`. Rewrite `hφy` using `[hc]`.

Take `⟨Φ, hΦ⟩ : ∃ Φ, phiPlus ℂ_[p] p ^ m = Φ` from `⟨_, rfl⟩`. Establish `hΦf : ∀ q, Φ (f q) = f q` using `fun q => by`. Rewrite using `[← hΦ, ← hf]`. Conclude with `(congrFun (RingHom.coe_pow (phiPlus ℂ_[p] p) m) _).trans (iterate_phiPlus_algebraMap_padic m q)`. Establish `hΦy : Φ y = c * x₁`.

Rewrite using `[← hΦ]`. Conclude with `(congrFun (RingHom.coe_pow (phiPlus ℂ_[p] p) m) y).trans hφy`. Establish `hφt : (phiPlus ℂ_[p] p)^[m] t' = (p : BCrisPlus ℂ_[p] p) ^ m * t'`. Rewrite using `[← ht']`. Conclude with `iterate_map_eq_pow_mul (phiPlus ℂ_[p] p) (map_natCast _ p) ((phiPlus_algebraMap _).trans ((congrArg _ (phi_periodT_eq_mul hε)).trans (by simp only [map_mul, map_natCast]))) m`.

Establish `hΦs : Φ (t' ^ m) = c`. Rewrite using `[← hΦ, ← hc]`. Conclude with `(congrFun (RingHom.coe_pow (phiPlus ℂ_[p] p) m) _).trans ((iterate_map_pow (phiPlus ℂ_[p] p) m t' m).trans (congrArg (· ^ m) hφt))`. Establish `hΦR : c ^ P.natDegree * P.eval₂ f x₁ = 0`. Establish `e1 : Φ R = homogEval f P (Φ y) (Φ (t' ^ m))`.

Rewrite using `[← hR]`. Conclude with `map_homogEval f P y (t' ^ m) Φ f hΦf`. Rewrite `e1` using `[hΦy, hΦs, homogEval_mul, hR0, map_zero]`. Conclude with `e1.symm`. Establish `hιc : iotaPlus ℂ_[p] p c ≠ 0`.

Rewrite using `[← hc, map_pow_mul_pow (iotaPlus ℂ_[p] p) (map_natCast _ p) m m t', hτ]`. Conclude with `pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ (IsPerfectoidField.isUnit_natCast_p_bDeRhamPlus (K := ℂ_[p]) p).ne_zero) (by rw [← hτdef]; exact iota_periodT_ne_zero hε hζ))`. Establish `h1 : iotaPlus ℂ_[p] p (aeval x₁ P) = 0`. Rewrite using `[aeval_def, hf]`. Conclude with `map_eq_zero_of_pow_mul_eq_zero (iotaPlus ℂ_[p] p) hΦR hιc`.

Establish `h2` using `aeval_algHom_apply (iotaPlusAlg (p := p)) x₁ P`. Rewrite `h2` using `[iotaPlusAlg_apply, iotaPlusAlg_apply, hιx₁, h1, aeval_algHom_apply]`. Conclude with `(injective_algClToBdR p) (h2.trans (map_zero _).symm)`.
-/
theorem aeval_minpoly_eq_zero_of_iterate {y x₁ : BCrisPlus ℂ_[p] p} {m : ℕ}
    {β β₁ : PadicAlgCl p}
    (hιy : iotaPlus ℂ_[p] p y = iota ℂ_[p] p (periodT hε) ^ m * algClToBdR p β)
    (hιx₁ : iotaPlus ℂ_[p] p x₁ = algClToBdR p β₁)
    (hφy : (phiPlus ℂ_[p] p)^[m] y = ((p : BCrisPlus ℂ_[p] p) ^ m *
      algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p) (periodT hε)) ^ m * x₁) :
    aeval β₁ (minpoly ℚ_[p] β) = 0 := by
  obtain ⟨t', ht'⟩ : ∃ t', algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p) (periodT hε) = t' :=
    ⟨_, rfl⟩
  obtain ⟨τ, hτdef⟩ : ∃ τ, iota ℂ_[p] p (periodT hε) = τ := ⟨_, rfl⟩
  rw [ht'] at hφy
  rw [hτdef] at hιy
  have hτ : iotaPlus ℂ_[p] p t' = τ := by rw [← ht', ← hτdef]; exact iotaPlus_algebraMap _
  obtain ⟨P, hP⟩ : ∃ P, minpoly ℚ_[p] β = P := ⟨_, rfl⟩
  rw [hP]
  obtain ⟨f, hf⟩ : ∃ f, algebraMap ℚ_[p] (BCrisPlus ℂ_[p] p) = f := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R, homogEval f P y (t' ^ m) = R := ⟨_, rfl⟩

  have hιs : iotaPlus ℂ_[p] p (t' ^ m) = τ ^ m := (map_pow _ _ _).trans (congrArg (· ^ m) hτ)
  have hιR : iotaPlus ℂ_[p] p R = 0 := by
    have e1 : iotaPlus ℂ_[p] p R = homogEval (algebraMap ℚ_[p] 𝔹) P (iotaPlus ℂ_[p] p y)
        (iotaPlus ℂ_[p] p (t' ^ m)) := by
      rw [← hR]
      exact map_homogEval f P y (t' ^ m) (iotaPlus ℂ_[p] p) (algebraMap ℚ_[p] 𝔹)
        (fun q => by rw [← hf]; exact iotaPlus_algebraMap_padic q)
    have e2 : aeval (algClToBdR p β) P = 0 := by
      rw [aeval_algHom_apply, ← hP, minpoly.aeval, map_zero]
    rw [e1, hιy, hιs, homogEval_mul, ← aeval_def, e2, mul_zero]
  have hR0 : R = 0 := iotaPlus_injective (K := ℂ_[p]) (p := p) (hιR.trans (map_zero _).symm)

  obtain ⟨c, hc⟩ : ∃ c, ((p : BCrisPlus ℂ_[p] p) ^ m * t') ^ m = c := ⟨_, rfl⟩
  rw [hc] at hφy
  obtain ⟨Φ, hΦ⟩ : ∃ Φ, phiPlus ℂ_[p] p ^ m = Φ := ⟨_, rfl⟩
  have hΦf : ∀ q, Φ (f q) = f q := fun q => by
    rw [← hΦ, ← hf]
    exact (congrFun (RingHom.coe_pow (phiPlus ℂ_[p] p) m) _).trans
      (iterate_phiPlus_algebraMap_padic m q)
  have hΦy : Φ y = c * x₁ := by
    rw [← hΦ]
    exact (congrFun (RingHom.coe_pow (phiPlus ℂ_[p] p) m) y).trans hφy
  have hφt : (phiPlus ℂ_[p] p)^[m] t' = (p : BCrisPlus ℂ_[p] p) ^ m * t' := by
    rw [← ht']
    exact iterate_map_eq_pow_mul (phiPlus ℂ_[p] p) (map_natCast _ p)
      ((phiPlus_algebraMap _).trans ((congrArg _ (phi_periodT_eq_mul hε)).trans
        (by simp only [map_mul, map_natCast]))) m
  have hΦs : Φ (t' ^ m) = c := by
    rw [← hΦ, ← hc]
    exact (congrFun (RingHom.coe_pow (phiPlus ℂ_[p] p) m) _).trans
      ((iterate_map_pow (phiPlus ℂ_[p] p) m t' m).trans (congrArg (· ^ m) hφt))
  have hΦR : c ^ P.natDegree * P.eval₂ f x₁ = 0 := by
    have e1 : Φ R = homogEval f P (Φ y) (Φ (t' ^ m)) := by
      rw [← hR]
      exact map_homogEval f P y (t' ^ m) Φ f hΦf
    rw [hΦy, hΦs, homogEval_mul, hR0, map_zero] at e1
    exact e1.symm

  have hιc : iotaPlus ℂ_[p] p c ≠ 0 := by
    rw [← hc, map_pow_mul_pow (iotaPlus ℂ_[p] p) (map_natCast _ p) m m t', hτ]
    exact pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ (IsPerfectoidField.isUnit_natCast_p_bDeRhamPlus
      (K := ℂ_[p]) p).ne_zero) (by rw [← hτdef]; exact iota_periodT_ne_zero hε hζ))
  have h1 : iotaPlus ℂ_[p] p (aeval x₁ P) = 0 := by
    rw [aeval_def, hf]
    exact map_eq_zero_of_pow_mul_eq_zero (iotaPlus ℂ_[p] p) hΦR hιc
  have h2 := aeval_algHom_apply (iotaPlusAlg (p := p)) x₁ P
  rw [iotaPlusAlg_apply, iotaPlusAlg_apply, hιx₁, h1, aeval_algHom_apply] at h2
  exact (injective_algClToBdR p) (h2.trans (map_zero _).symm)

include hζ in
set_option maxHeartbeats 1600000 in

/- English proof (translation)
Take `⟨k, hk⟩` from `bCris_fixed hε hζ x hx`. Take `⟨k₁, hk₁⟩` from `bCris_fixed hε hζ ((phiB hε)^[m] x) fun σ => galB_iterate_phiB hε σ (hx σ) m`. Establish `hk'` using `hk.trans (algebraMap_intermediateField_bDeRham K k)`. Establish `hk₁'` using `hk₁.trans (algebraMap_intermediateField_bDeRham K k₁)`. Establish `hιy : iotaPlus ℂ_[p] p y = iota ℂ_[p] p (periodT hε) ^ m * algClToBdR p k` using `eq_pow_mul_of_map_eq (iotaB hε hζ) (algebraMap 𝔹 𝔹dR) (IsFractionRing.injective 𝔹 𝔹dR) ((iotaB_algebraMap hε hζ y).symm.trans (congrArg _ hy)) (iotaB_periodTCris hε hζ) hk'`.

Establish `hιx₁ : iotaPlus ℂ_[p] p x₁ = algClToBdR p k₁` using `IsFractionRing.injective 𝔹 𝔹dR ((iotaB_algebraMap hε hζ x₁).symm.trans ((congrArg _ hx₁).trans hk₁'))`. Establish `hφy : (phiPlus ℂ_[p] p)^[m] y = ((p : BCrisPlus ℂ_[p] p) ^ m * algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p) (periodT hε)) ^ m * x₁` using `algebraMap_bCrisPlus_bCris_injective hε hζ ((algebraMap_iterate_phiPlus_eq hε hy m).trans ((congrArg (fun z => ((p : BCris hε) ^ m * periodTCris hε) ^ m * z) hx₁.symm).trans (map_pow_mul_pow_mul (algebraMap (BCrisPlus ℂ_[p] p) (BCris hε)) (map_natCast _ p) m m (algebraMap (ACris …`. Establish `hroot` using `aeval_minpoly_eq_zero_of_iterate hε hζ hιy hιx₁ hφy`. Establish `hint : IsIntegral ℚ_[p] (k : PadicAlgCl p)` using `Algebra.IsIntegral.isIntegral _`. Establish `hmin : minpoly ℚ_[p] (k : PadicAlgCl p) = minpoly ℚ_[p] (k₁ : PadicAlgCl p)` using `minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hint) hroot (minpoly.monic hint)`.

Establish `hk0 : (k : PadicAlgCl p) ∈ maxUnramified p K` using `mem_maxUnramified.2 ⟨k.2, mem_unramifiedClosure_of_minpoly_eq hmin (mem_unramifiedClosure_of_iotaPlus_eq hιx₁)⟩`. Conclude with `exists_bCrisPlus_fixed_eq_of_mem_maxUnramified hε hζ hk0 hk'`.
-/
theorem exists_bCrisPlus_fixed_eq_of_iterate {x : BCris hε}
    (hx : ∀ σ : Gal(PadicAlgCl p/K), galB hε σ x = x) {m : ℕ} {y x₁ : BCrisPlus ℂ_[p] p}
    (hy : algebraMap (BCrisPlus ℂ_[p] p) (BCris hε) y = periodTCris hε ^ m * x)
    (hx₁ : algebraMap (BCrisPlus ℂ_[p] p) (BCris hε) x₁ = (phiB hε)^[m] x) :
    ∃ y' : BCrisPlus ℂ_[p] p, (∀ σ : Gal(PadicAlgCl p/K), σ • y' = y') ∧
      algebraMap (BCrisPlus ℂ_[p] p) (BCris hε) y' = x := by
  obtain ⟨k, hk⟩ := bCris_fixed hε hζ x hx
  obtain ⟨k₁, hk₁⟩ := bCris_fixed hε hζ ((phiB hε)^[m] x) fun σ => galB_iterate_phiB hε σ (hx σ) m
  have hk' := hk.trans (algebraMap_intermediateField_bDeRham K k)
  have hk₁' := hk₁.trans (algebraMap_intermediateField_bDeRham K k₁)
  have hιy : iotaPlus ℂ_[p] p y = iota ℂ_[p] p (periodT hε) ^ m * algClToBdR p k :=
    eq_pow_mul_of_map_eq (iotaB hε hζ) (algebraMap 𝔹 𝔹dR) (IsFractionRing.injective 𝔹 𝔹dR)
      ((iotaB_algebraMap hε hζ y).symm.trans (congrArg _ hy)) (iotaB_periodTCris hε hζ) hk'
  have hιx₁ : iotaPlus ℂ_[p] p x₁ = algClToBdR p k₁ :=
    IsFractionRing.injective 𝔹 𝔹dR
      ((iotaB_algebraMap hε hζ x₁).symm.trans ((congrArg _ hx₁).trans hk₁'))
  have hφy : (phiPlus ℂ_[p] p)^[m] y = ((p : BCrisPlus ℂ_[p] p) ^ m *
      algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p) (periodT hε)) ^ m * x₁ :=
    algebraMap_bCrisPlus_bCris_injective hε hζ ((algebraMap_iterate_phiPlus_eq hε hy m).trans
      ((congrArg (fun z => ((p : BCris hε) ^ m * periodTCris hε) ^ m * z) hx₁.symm).trans
        (map_pow_mul_pow_mul (algebraMap (BCrisPlus ℂ_[p] p) (BCris hε)) (map_natCast _ p) m m
          (algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p) (periodT hε)) x₁).symm))
  have hroot := aeval_minpoly_eq_zero_of_iterate hε hζ hιy hιx₁ hφy
  have hint : IsIntegral ℚ_[p] (k : PadicAlgCl p) := Algebra.IsIntegral.isIntegral _
  have hmin : minpoly ℚ_[p] (k : PadicAlgCl p) = minpoly ℚ_[p] (k₁ : PadicAlgCl p) :=
    minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hint) hroot (minpoly.monic hint)
  have hk0 : (k : PadicAlgCl p) ∈ maxUnramified p K :=
    mem_maxUnramified.2 ⟨k.2, mem_unramifiedClosure_of_minpoly_eq hmin
      (mem_unramifiedClosure_of_iotaPlus_eq hιx₁)⟩
  exact exists_bCrisPlus_fixed_eq_of_mem_maxUnramified hε hζ hk0 hk'

include hζ in
set_option maxHeartbeats 1600000 in

/- English proof (translation)
Take `⟨m, a, hs'⟩` from `exists_algebraMap_eq_periodTCris_pow_mul hε x`. Take `⟨x₁, hx₁⟩` from `exists_iterate_phiB_eq hε hζ m x hx ⟨a, hs'⟩`. Conclude with `exists_bCrisPlus_fixed_eq_of_iterate hε hζ hx hs' hx₁`.
-/
theorem exists_bCrisPlus_fixed_eq (x : BCris hε)
    (hx : ∀ σ : Gal(PadicAlgCl p/K), galB hε σ x = x) :
    ∃ y : BCrisPlus ℂ_[p] p, (∀ σ : Gal(PadicAlgCl p/K), σ • y = y) ∧
      algebraMap (BCrisPlus ℂ_[p] p) (BCris hε) y = x := by
  obtain ⟨m, a, hs'⟩ := exists_algebraMap_eq_periodTCris_pow_mul hε x
  obtain ⟨x₁, hx₁⟩ := exists_iterate_phiB_eq hε hζ m x hx ⟨a, hs'⟩
  exact exists_bCrisPlus_fixed_eq_of_iterate hε hζ hx hs' hx₁

include hζ in
set_option maxHeartbeats 1600000 in

/- English proof (translation)
Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Take `⟨y, hy, hyx⟩` from `exists_bCrisPlus_fixed_eq hε hζ x hx`. Conclude with `⟨y, hy, hyx⟩`.

Introduce and unpack `⟨y, hy, rfl⟩ σ`. Conclude with `(galB_algebraMap hε σ y).trans (congrArg _ (hy σ))`.
-/
theorem fixed_bCris_eq_image :
    {x : BCris hε | ∀ σ : Gal(PadicAlgCl p/K), galB hε σ x = x} =
      algebraMap (BCrisPlus ℂ_[p] p) (BCris hε) ''
        MulAction.fixedPoints Gal(PadicAlgCl p/K) (BCrisPlus ℂ_[p] p) := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := exists_bCrisPlus_fixed_eq hε hζ x hx
    exact ⟨y, hy, hyx⟩
  · rintro ⟨y, hy, rfl⟩ σ
    exact (galB_algebraMap hε σ y).trans (congrArg _ (hy σ))

include hζ in
set_option maxHeartbeats 1600000 in

/- English proof (translation)
Take `⟨y, hy, hyx⟩` from `exists_bCrisPlus_fixed_eq hε hζ x hx`. Take `⟨k, hk, hyk⟩` from `bCrisPlus_fixed y hy`. Conclude with `⟨k, hk, (congrArg (iotaB hε hζ) hyx).symm.trans ((iotaB_algebraMap hε hζ y).trans (congrArg _ hyk))⟩`.
-/
theorem bCris_fixed_mem_maxUnramified (x : BCris hε)
    (hx : ∀ σ : Gal(PadicAlgCl p/K), galB hε σ x = x) :
    ∃ k ∈ maxUnramified p K, iotaB hε hζ x = algebraMap 𝔹 𝔹dR (algClToBdR p k) := by
  obtain ⟨y, hy, hyx⟩ := exists_bCrisPlus_fixed_eq hε hζ x hx
  obtain ⟨k, hk, hyk⟩ := bCrisPlus_fixed y hy
  exact ⟨k, hk, (congrArg (iotaB hε hζ) hyx).symm.trans
    ((iotaB_algebraMap hε hζ y).trans (congrArg _ hyk))⟩

end ACris

end GroundTheory.PAdicHodge
