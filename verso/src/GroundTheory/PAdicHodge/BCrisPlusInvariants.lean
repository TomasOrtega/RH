import Mathlib
import GroundTheory.PAdicHodge.ACrisFrobFixed
import GroundTheory.PAdicHodge.BCrisGalois
import GroundTheory.PAdicHodge.BdRInvariants
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open _root_.WittVector Polynomial

namespace ACris

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝒪" => normInteger ℂ_[p]
local notation "𝒪♭" => PreTilt (normInteger ℂ_[p]) p
local notation "𝔹" => BDeRhamPlus (normInteger ℂ_[p]) p
local notation "φW" => WittVector.frobeniusEquiv p (PreTilt (normInteger ℂ_[p]) p)

section Teichmuller

omit hp in
/- English proof (translation)
Use `conv_lhs => rw [← Nat.div_add_mod k m, pow_add, pow_mul, hx, one_pow, one_mul]`.
-/
theorem pow_eq_pow_mod_of_pow_eq_one {M : Type*} [Monoid M] {x : M} {m : ℕ} (hx : x ^ m = 1)
    (k : ℕ) : x ^ k = x ^ (k % m) := by
  conv_lhs => rw [← Nat.div_add_mod k m, pow_add, pow_mul, hx, one_pow, one_mul]

/- English proof (translation)
Establish `h` using `congrArg norm hx`. Rewrite `h` using `[norm_pow, norm_one]`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 h`.
-/
theorem norm_eq_one_of_pow_eq_one {x : ℂ_[p]} {m : ℕ} (hm : 0 < m) (hx : x ^ m = 1) : ‖x‖ = 1 := by
  have h := congrArg norm hx
  rw [norm_pow, norm_one] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 h

/- English proof (translation)
Establish `hd : 1 ≤ m.totient` using `Nat.totient_pos.2 hm`. Establish `hmod : p ^ m.totient % m = 1 % m` using `Nat.ModEq.pow_totient (Nat.Coprime.symm hc)`. Establish `e1 : (ζ ^ p ^ ((n + 1) * (m.totient - 1))) ^ p = (ζ ^ p ^ (n * (m.totient - 1))) ^ p ^ m.totient`. Rewrite using `[← pow_mul, ← pow_mul, ← pow_succ, ← pow_add]`. Use `congr 2`.

Rewrite using `[add_mul, one_mul]`. Use linear arithmetic over natural numbers and integers. Establish `hx : (ζ ^ p ^ (n * (m.totient - 1))) ^ m = 1` using `by rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]`. Rewrite using `[e1, pow_eq_pow_mod_of_pow_eq_one hx, hmod, ← pow_eq_pow_mod_of_pow_eq_one hx, pow_one]`.
-/
theorem rootOfUnity_compatible {ζ : PadicAlgCl p} {m : ℕ} (hm : 0 < m) (hc : m.Coprime p)
    (hζ : ζ ^ m = 1) (n : ℕ) :
    (ζ ^ p ^ ((n + 1) * (m.totient - 1))) ^ p = ζ ^ p ^ (n * (m.totient - 1)) := by
  have hd : 1 ≤ m.totient := Nat.totient_pos.2 hm
  have hmod : p ^ m.totient % m = 1 % m := Nat.ModEq.pow_totient (Nat.Coprime.symm hc)
  have e1 : (ζ ^ p ^ ((n + 1) * (m.totient - 1))) ^ p =
      (ζ ^ p ^ (n * (m.totient - 1))) ^ p ^ m.totient := by
    rw [← pow_mul, ← pow_mul, ← pow_succ, ← pow_add]
    congr 2
    rw [add_mul, one_mul]
    omega
  have hx : (ζ ^ p ^ (n * (m.totient - 1))) ^ m = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  rw [e1, pow_eq_pow_mod_of_pow_eq_one hx, hmod, ← pow_eq_pow_mod_of_pow_eq_one hx, pow_one]

/- English proof (translation)
Use `set z : ℕ → PadicAlgCl p := fun n => ζ ^ p ^ (n * (m.totient - 1))`. Establish `hzm' : ∀ n, z n ^ m = 1` using `fun n => by`. Simplify using `only [z]`. Rewrite using `[← pow_mul, mul_comm, pow_mul, hζ, one_pow]`. Establish `hzm : ∀ n, (z n : ℂ_[p]) ^ m = 1` using `fun n => by`.

Rewrite using `[PadicComplex.coe_eq, ← map_pow, hzm' n, map_one]`. Establish `hmem : ∀ n, (z n : ℂ_[p]) ∈ normInteger ℂ_[p]` using `fun n => mem_normInteger.2 (norm_eq_one_of_pow_eq_one hm (hzm n)).le`. Use `set y : ℕ → 𝒪 := fun n => ⟨(z n : ℂ_[p]), hmem n⟩`. Establish `hy : ∀ n, y (n + 1) ^ p = y n` using `fun n => Subtype.ext (by`. Simplify using `only [y, SubmonoidClass.coe_pow]`.

Rewrite using `[PadicComplex.coe_eq, PadicComplex.coe_eq, ← map_pow]`. Conclude with `congrArg _ (rootOfUnity_compatible hm hc hζ n))`. Use `set ζf : 𝒪♭ := IsPerfectoidField.ofCompatible p y hy`. Establish `hζf : ζf ^ m = 1` using `IsPerfectoidField.preTilt_ext p fun n => by`. Rewrite using `[map_pow, IsPerfectoidField.coeff_ofCompatible, ← map_pow, map_one]`.

Establish `: y n ^ m = 1` using `Subtype.ext (by`. Simplify using `only [y, SubmonoidClass.coe_pow, OneMemClass.coe_one]`. Conclude with `hzm n)`. Rewrite using `[this, map_one]`. Use `⟨teichmuller p ζf, by rw [← map_pow, hζf, map_one], ?_⟩` and prove the remaining obligations.

Rewrite using `[fontaineTheta_teichmuller, IsPerfectoidField.untilt_ofCompatible]`. Simplify using `[y, z]`.
-/
theorem exists_teichmuller_rootOfUnity {ζ : PadicAlgCl p} {m : ℕ} (hm : 0 < m) (hc : m.Coprime p)
    (hζ : ζ ^ m = 1) :
    ∃ T : AInf ℂ_[p] p, T ^ m = 1 ∧
      ((fontaineTheta (normInteger ℂ_[p]) p T : 𝒪) : ℂ_[p]) = (ζ : ℂ_[p]) := by
  set z : ℕ → PadicAlgCl p := fun n => ζ ^ p ^ (n * (m.totient - 1))
  have hzm' : ∀ n, z n ^ m = 1 := fun n => by
    simp only [z]
    rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  have hzm : ∀ n, (z n : ℂ_[p]) ^ m = 1 := fun n => by
    rw [PadicComplex.coe_eq, ← map_pow, hzm' n, map_one]
  have hmem : ∀ n, (z n : ℂ_[p]) ∈ normInteger ℂ_[p] := fun n =>
    mem_normInteger.2 (norm_eq_one_of_pow_eq_one hm (hzm n)).le
  set y : ℕ → 𝒪 := fun n => ⟨(z n : ℂ_[p]), hmem n⟩
  have hy : ∀ n, y (n + 1) ^ p = y n := fun n => Subtype.ext (by
    simp only [y, SubmonoidClass.coe_pow]
    rw [PadicComplex.coe_eq, PadicComplex.coe_eq, ← map_pow]
    exact congrArg _ (rootOfUnity_compatible hm hc hζ n))
  set ζf : 𝒪♭ := IsPerfectoidField.ofCompatible p y hy
  have hζf : ζf ^ m = 1 := IsPerfectoidField.preTilt_ext p fun n => by
    rw [map_pow, IsPerfectoidField.coeff_ofCompatible, ← map_pow, map_one]
    have : y n ^ m = 1 := Subtype.ext (by
      simp only [y, SubmonoidClass.coe_pow, OneMemClass.coe_one]; exact hzm n)
    rw [this, map_one]
  refine ⟨teichmuller p ζf, by rw [← map_pow, hζf, map_one], ?_⟩
  rw [fontaineTheta_teichmuller, IsPerfectoidField.untilt_ofCompatible]
  simp [y, z]

/- English proof (translation)
Establish `h : (∑ i ∈ Finset.range m, u ^ i * v ^ (m - 1 - i)) * (u - v) = u ^ m - v ^ m` using `geom_sum₂_mul u v m`. Rewrite `h` using `[hu, hv, sub_self]`. Establish `hS : ∑ i ∈ Finset.range m, u ^ i * v ^ (m - 1 - i) ≠ 0`. Introduce `hS`. Establish `h1` using `congrArg (thetaAlgHom p) hS`.

Rewrite `h1` using `[map_zero, map_sum]`. Simplify using `only [map_mul, map_pow, hθ] at h1`. Rewrite using `[Finset.sum_congr rfl fun i hi => (by`. Rewrite using `[← pow_add]`. Use `congr 1`.

Use `Finset.mem_range.1 hi` as an intermediate fact. Use `omega : thetaAlgHom p v ^ i * thetaAlgHom p v ^ (m - 1 - i) = thetaAlgHom p v ^ (m - 1)),`. Use the proof step `Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1`. Conclude with `(mul_ne_zero (Nat.cast_ne_zero.2 hm.ne') (pow_ne_zero _ h0)) h1`. Conclude with `sub_eq_zero.1 ((mul_eq_zero.1 h).resolve_left hS)`.
-/
theorem eq_of_pow_eq_one_of_theta_eq {u v : 𝔹} {m : ℕ} (hm : 0 < m) (hu : u ^ m = 1)
    (hv : v ^ m = 1) (hθ : thetaAlgHom p u = thetaAlgHom p v) (h0 : thetaAlgHom p v ≠ 0) :
    u = v := by
  have h : (∑ i ∈ Finset.range m, u ^ i * v ^ (m - 1 - i)) * (u - v) = u ^ m - v ^ m :=
    geom_sum₂_mul u v m
  rw [hu, hv, sub_self] at h
  have hS : ∑ i ∈ Finset.range m, u ^ i * v ^ (m - 1 - i) ≠ 0 := by
    intro hS
    have h1 := congrArg (thetaAlgHom p) hS
    rw [map_zero, map_sum] at h1
    simp only [map_mul, map_pow, hθ] at h1
    rw [Finset.sum_congr rfl fun i hi => (by
      rw [← pow_add]; congr 1; have := Finset.mem_range.1 hi; omega :
        thetaAlgHom p v ^ i * thetaAlgHom p v ^ (m - 1 - i) = thetaAlgHom p v ^ (m - 1)),
      Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1
    exact (mul_ne_zero (Nat.cast_ne_zero.2 hm.ne') (pow_ne_zero _ h0)) h1
  exact sub_eq_zero.1 ((mul_eq_zero.1 h).resolve_left hS)

/- English proof (translation)
Take `⟨T, hT, hθT⟩` from `exists_teichmuller_rootOfUnity hm hc hζ`. Use `⟨algebraMap (AInf ℂ_[p] p) (ACris ℂ_[p] p) T, ?_⟩` and prove the remaining obligations. Establish `hζ0 : (ζ : ℂ_[p]) ≠ 0`. Introduce `h`. Use `norm_eq_one_of_pow_eq_one hm (show (ζ : ℂ_[p]) ^ m = 1 by` as an intermediate fact.

Rewrite using `[PadicComplex.coe_eq, ← map_pow, hζ, map_one])`. Rewrite `this` using `[h, norm_zero]`. Conclude with `zero_ne_one this`. Apply `eq_of_pow_eq_one_of_theta_eq hm` to reduce the goal to its premises. Rewrite using `[← map_pow, ← map_pow, hT, map_one, map_one]`.

Rewrite using `[← map_pow, hζ, map_one]`. Rewrite using `[thetaAlgHom_apply, thetaField_iota, theta_algebraMap, hθT, thetaAlgHom_algClToBdR]`. Rewrite using `[thetaAlgHom_algClToBdR]`. Conclude with `hζ0`.
-/
theorem iota_teichmuller_rootOfUnity {ζ : PadicAlgCl p} {m : ℕ} (hm : 0 < m) (hc : m.Coprime p)
    (hζ : ζ ^ m = 1) :
    ∃ x : ACris ℂ_[p] p, iota ℂ_[p] p x = algClToBdR p ζ := by
  obtain ⟨T, hT, hθT⟩ := exists_teichmuller_rootOfUnity hm hc hζ
  refine ⟨algebraMap (AInf ℂ_[p] p) (ACris ℂ_[p] p) T, ?_⟩
  have hζ0 : (ζ : ℂ_[p]) ≠ 0 := by
    intro h
    have := norm_eq_one_of_pow_eq_one hm (show (ζ : ℂ_[p]) ^ m = 1 by
      rw [PadicComplex.coe_eq, ← map_pow, hζ, map_one])
    rw [h, norm_zero] at this
    exact zero_ne_one this
  apply eq_of_pow_eq_one_of_theta_eq hm
  · rw [← map_pow, ← map_pow, hT, map_one, map_one]
  · rw [← map_pow, hζ, map_one]
  · rw [thetaAlgHom_apply, thetaField_iota, theta_algebraMap, hθT, thetaAlgHom_algClToBdR]
  · rw [thetaAlgHom_algClToBdR]; exact hζ0

end Teichmuller

section Padic

def padicIntToBCrisPlus : ℤ_[p] →+* BCrisPlus ℂ_[p] p :=
  (algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p)).comp
    ((algebraMap (AInf ℂ_[p] p) (ACris ℂ_[p] p)).comp
      (IsPerfectoidField.padicIntToWitt (K := ℂ_[p]) p))

/- English proof (translation)
Simplify using `using IsLocalization.Away.algebraMap_isUnit (S := BCrisPlus ℂ_[p] p) (p : ACris ℂ_[p] p)`.
-/
theorem isUnit_p_bCrisPlus : IsUnit ((p : ℕ) : BCrisPlus ℂ_[p] p) := by
  simpa using IsLocalization.Away.algebraMap_isUnit (S := BCrisPlus ℂ_[p] p) (p : ACris ℂ_[p] p)

/- English proof (translation)
Rewrite using `[PadicInt.unitCoeff_spec hx, map_mul, map_pow, map_natCast]`. Conclude with `((PadicInt.unitCoeff hx).isUnit.map _).mul (isUnit_p_bCrisPlus.pow _)`.
-/
theorem isUnit_padicIntToBCrisPlus {x : ℤ_[p]} (hx : x ≠ 0) : IsUnit (padicIntToBCrisPlus x) := by
  rw [PadicInt.unitCoeff_spec hx, map_mul, map_pow, map_natCast]
  exact ((PadicInt.unitCoeff hx).isUnit.map _).mul (isUnit_p_bCrisPlus.pow _)

def padicToBCrisPlus : ℚ_[p] →+* BCrisPlus ℂ_[p] p :=
  IsLocalization.lift (M := nonZeroDivisors ℤ_[p]) (S := ℚ_[p]) (g := padicIntToBCrisPlus)
    fun y => isUnit_padicIntToBCrisPlus (nonZeroDivisors.coe_ne_zero y)

instance algebraPadicBCrisPlus : Algebra ℚ_[p] (BCrisPlus ℂ_[p] p) := padicToBCrisPlus.toAlgebra

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem algebraMap_padic_bCrisPlus : algebraMap ℚ_[p] (BCrisPlus ℂ_[p] p) = padicToBCrisPlus :=
  rfl

/- English proof (translation)
Establish `h : (iotaPlus ℂ_[p] p).comp padicToBCrisPlus = algebraMap ℚ_[p] 𝔹`. Use `IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[p]) (RingHom.ext fun x => ?_)` and prove the remaining obligations. Simplify using `only [RingHom.comp_apply, padicToBCrisPlus, IsLocalization.lift_eq, padicIntToBCrisPlus, iotaPlus_algebraMap]`. Conclude with `iota_padicInt x`. Conclude with `RingHom.congr_fun h q`.
-/
theorem iotaPlus_algebraMap_padic (q : ℚ_[p]) :
    iotaPlus ℂ_[p] p (algebraMap ℚ_[p] (BCrisPlus ℂ_[p] p) q) = algebraMap ℚ_[p] 𝔹 q := by
  have h : (iotaPlus ℂ_[p] p).comp padicToBCrisPlus = algebraMap ℚ_[p] 𝔹 := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[p]) (RingHom.ext fun x => ?_)
    simp only [RingHom.comp_apply, padicToBCrisPlus, IsLocalization.lift_eq, padicIntToBCrisPlus,
      iotaPlus_algebraMap]
    exact iota_padicInt x
  exact RingHom.congr_fun h q

def iotaPlusAlg : BCrisPlus ℂ_[p] p →ₐ[ℚ_[p]] 𝔹 :=
  { iotaPlus ℂ_[p] p with commutes' := iotaPlus_algebraMap_padic }

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem iotaPlusAlg_apply (x : BCrisPlus ℂ_[p] p) : iotaPlusAlg x = iotaPlus ℂ_[p] p x :=
  rfl

/- English proof (translation)
Use `AInf.isAdicComplete_p (K := ℂ_[p]) (p := p)` as an intermediate fact. Conclude with `RingHom.congr_fun (ringHom_ext_padicInt ((φW : AInf ℂ_[p] p →+* AInf ℂ_[p] p).comp (IsPerfectoidField.padicIntToWitt (K := ℂ_[p]) p)) (IsPerfectoidField.padicIntToWitt (K := ℂ_[p]) p)) a`.
-/
theorem frobenius_padicIntToWitt (a : ℤ_[p]) :
    φW (IsPerfectoidField.padicIntToWitt (K := ℂ_[p]) p a) =
      IsPerfectoidField.padicIntToWitt (K := ℂ_[p]) p a := by
  have := AInf.isAdicComplete_p (K := ℂ_[p]) (p := p)
  exact RingHom.congr_fun (ringHom_ext_padicInt
    ((φW : AInf ℂ_[p] p →+* AInf ℂ_[p] p).comp (IsPerfectoidField.padicIntToWitt (K := ℂ_[p]) p))
    (IsPerfectoidField.padicIntToWitt (K := ℂ_[p]) p)) a

/- English proof (translation)
Establish `h : (phiPlus ℂ_[p] p).comp padicToBCrisPlus = padicToBCrisPlus`. Use `IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[p]) (RingHom.ext fun x => ?_)` and prove the remaining obligations. Simplify using `only [RingHom.comp_apply, padicToBCrisPlus, IsLocalization.lift_eq, padicIntToBCrisPlus, phiPlus_algebraMap, phi_algebraMap]`. Rewrite using `[frobenius_padicIntToWitt]`. Conclude with `RingHom.congr_fun h q`.
-/
theorem phiPlus_algebraMap_padic (q : ℚ_[p]) :
    phiPlus ℂ_[p] p (algebraMap ℚ_[p] (BCrisPlus ℂ_[p] p) q) =
      algebraMap ℚ_[p] (BCrisPlus ℂ_[p] p) q := by
  have h : (phiPlus ℂ_[p] p).comp padicToBCrisPlus = padicToBCrisPlus := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[p]) (RingHom.ext fun x => ?_)
    simp only [RingHom.comp_apply, padicToBCrisPlus, IsLocalization.lift_eq, padicIntToBCrisPlus,
      phiPlus_algebraMap, phi_algebraMap]
    rw [frobenius_padicIntToWitt]
  exact RingHom.congr_fun h q

def phiPlusAlg : BCrisPlus ℂ_[p] p →ₐ[ℚ_[p]] BCrisPlus ℂ_[p] p :=
  { phiPlus ℂ_[p] p with commutes' := phiPlus_algebraMap_padic }

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem phiPlusAlg_apply (x : BCrisPlus ℂ_[p] p) : phiPlusAlg x = phiPlus ℂ_[p] p x :=
  rfl

end Padic

section Unramified

def algClInBCrisPlus : Subalgebra ℚ_[p] (PadicAlgCl p) :=
  (iotaPlusAlg (p := p)).range.comap (algClToBdR p)

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_algClInBCrisPlus {β : PadicAlgCl p} :
    β ∈ algClInBCrisPlus ↔ ∃ x : BCrisPlus ℂ_[p] p, iotaPlus ℂ_[p] p x = algClToBdR p β :=
  Iff.rfl

/- English proof (translation)
Rewrite using `[unramifiedClosure, IntermediateField.adjoin_toSubalgebra_of_isAlgebraic fun x _ => Algebra.IsAlgebraic.isAlgebraic x]`. Use `Algebra.adjoin_le fun ζ hζ => ?_` and prove the remaining obligations. Take `⟨m, hm, hc, hζm⟩` from `hζ`. Take `⟨x, hx⟩` from `iota_teichmuller_rootOfUnity hm hc hζm`. Conclude with `⟨algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p) x, by show iotaPlus ℂ_[p] p _ = _`.

Rewrite using `[iotaPlus_algebraMap, hx]`. Use the proof step `rfl⟩`.
-/
theorem unramifiedClosure_le :
    (unramifiedClosure p).toSubalgebra ≤ algClInBCrisPlus (p := p) := by
  rw [unramifiedClosure, IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
    fun x _ => Algebra.IsAlgebraic.isAlgebraic x]
  refine Algebra.adjoin_le fun ζ hζ => ?_
  obtain ⟨m, hm, hc, hζm⟩ := hζ
  obtain ⟨x, hx⟩ := iota_teichmuller_rootOfUnity hm hc hζm
  exact ⟨algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p) x, by
    show iotaPlus ℂ_[p] p _ = _
    rw [iotaPlus_algebraMap, hx]
    rfl⟩

/- English proof (translation)
The claim follows from `mem_nonZeroDivisors_iff.2 ⟨fun z hz => eq_zero_of_p_mul_eq_zero hz, fun z hz => eq_zero_of_p_mul_eq_zero (by rw [mul_comm]; exact hz)⟩`.
-/
theorem p_mem_nonZeroDivisors_aCris : (p : ACris ℂ_[p] p) ∈ nonZeroDivisors (ACris ℂ_[p] p) :=
  mem_nonZeroDivisors_iff.2 ⟨fun z hz => eq_zero_of_p_mul_eq_zero hz,
    fun z hz => eq_zero_of_p_mul_eq_zero (by rw [mul_comm]; exact hz)⟩

/- English proof (translation)
The claim follows from `IsLocalization.injective (BCrisPlus ℂ_[p] p) (Submonoid.powers_le.2 p_mem_nonZeroDivisors_aCris)`.
-/
theorem algebraMap_aCris_injective :
    Function.Injective (algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p)) :=
  IsLocalization.injective (BCrisPlus ℂ_[p] p)
    (Submonoid.powers_le.2 p_mem_nonZeroDivisors_aCris)

set_option maxHeartbeats 1600000 in
/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rfl`. Consider the case `succ n ih => rw [Function.iterate_succ_apply', ih, phiPlus_algebraMap, Function.iterate_succ_apply']`.
-/
theorem phiPlus_iterate_algebraMap (n : ℕ) (a : ACris ℂ_[p] p) :
    (phiPlus ℂ_[p] p)^[n] (algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p) a) =
      algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p) ((phi ℂ_[p] p)^[n] a) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, phiPlus_algebraMap,
      Function.iterate_succ_apply']

/- English proof (translation)
Use `set Q' := Q.map (algebraMap ℚ_[p] (PadicAlgCl p))`. Establish `hQ' : Q'.Monic` using `hQ.map _`. Establish `hsplit : Q'.Splits` using `IsAlgClosed.splits Q'`. Establish `hprod` using `hsplit.eq_prod_roots_of_monic hQ'`. Establish `h1 : Q'.eval₂ (algClToBdR p : PadicAlgCl p →+* 𝔹) z = 0`.

Rewrite using `[Polynomial.eval₂_map, ← hz, aeval_def]`. Use `congr 1`. Conclude with `(algClToBdR p).comp_algebraMap`. Rewrite `h1` using `[hprod, Polynomial.eval₂_multiset_prod, Multiset.map_map]`. Take `⟨r, hr, hr0⟩` from `Multiset.mem_map.1 (Multiset.prod_eq_zero_iff.1 h1)`.

Simplify using `only [Function.comp_apply, eval₂_sub, eval₂_X, eval₂_C] at hr0`. Conclude with `⟨r, hr, sub_eq_zero.1 hr0⟩`.
-/
theorem exists_root_of_aeval_eq_zero {Q : ℚ_[p][X]} (hQ : Q.Monic) {z : 𝔹} (hz : aeval z Q = 0) :
    ∃ r ∈ (Q.map (algebraMap ℚ_[p] (PadicAlgCl p))).roots, z = algClToBdR p r := by
  set Q' := Q.map (algebraMap ℚ_[p] (PadicAlgCl p))
  have hQ' : Q'.Monic := hQ.map _
  have hsplit : Q'.Splits := IsAlgClosed.splits Q'
  have hprod := hsplit.eq_prod_roots_of_monic hQ'
  have h1 : Q'.eval₂ (algClToBdR p : PadicAlgCl p →+* 𝔹) z = 0 := by
    rw [Polynomial.eval₂_map, ← hz, aeval_def]
    congr 1
    exact (algClToBdR p).comp_algebraMap
  rw [hprod, Polynomial.eval₂_multiset_prod, Multiset.map_map] at h1
  obtain ⟨r, hr, hr0⟩ := Multiset.mem_map.1 (Multiset.prod_eq_zero_iff.1 h1)
  simp only [Function.comp_apply, eval₂_sub, eval₂_X, eval₂_C] at hr0
  exact ⟨r, hr, sub_eq_zero.1 hr0⟩

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Establish `hint : IsIntegral ℚ_[p] β` using `Algebra.IsIntegral.isIntegral β`. Use `set Q := minpoly ℚ_[p] β`. Establish `hQm : Q.Monic` using `minpoly.monic hint`. Establish `hQ0 : aeval x Q = 0`. Apply `iotaPlus_injective (K := ℂ_[p]) (p := p)` to reduce the goal to its premises.

Rewrite using `[map_zero, ← iotaPlusAlg_apply, ← aeval_algHom_apply, iotaPlusAlg_apply, hx, aeval_algHom_apply, minpoly.aeval, map_zero]`. Establish `hQn : ∀ n, aeval ((phiPlus ℂ_[p] p)^[n] x) Q = 0`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => exact hQ0`.

Consider the case `succ n ih`. Rewrite using `[Function.iterate_succ_apply', ← phiPlusAlg_apply, aeval_algHom_apply, ih, map_zero]`. Establish `hroot : ∀ n, ∃ r ∈ (Q.map (algebraMap ℚ_[p] (PadicAlgCl p))).roots, iotaPlus ℂ_[p] p ((phiPlus ℂ_[p] p)^[n] x) = algClToBdR p r` using `fun n => exists_root_of_aeval_eq_zero hQm (by`. Rewrite using `[← iotaPlusAlg_apply, aeval_algHom_apply, hQn, map_zero])`. Use `choose r hr hrx using hroot`.

Set `f : ℕ → (Q.map (algebraMap ℚ_[p] (PadicAlgCl p))).roots.toFinset` to `fun n => ⟨r n, Multiset.mem_toFinset.2 (hr n)⟩`. Take `⟨a₁, a₂, hne, hf⟩` from `Finite.exists_ne_map_eq_of_infinite f`. Establish `hr12 : r a₁ = r a₂`. Use `congrArg Subtype.val hf` as an intermediate fact. Simplify `this` using `[f]`.

Choose the witnesses or unpack the hypotheses as in `⟨n₁, n₂, hlt, hr'⟩ : ∃ n₁ n₂, n₁ < n₂ ∧ r n₁ = r n₂ := by`. Break down `lt_or_gt_of_ne hne with h | h` into its components or cases. Conclude with `⟨a₁, a₂, h, hr12⟩`. Conclude with `⟨a₂, a₁, h, hr12.symm⟩`. Use `set x' := (phiPlus ℂ_[p] p)^[n₁] x`.

Use `set N := n₂ - n₁`. Establish `hN : 1 ≤ N` using `by omega`. Establish `hfix : (phiPlus ℂ_[p] p)^[N] x' = x'`. Apply `iotaPlus_injective (K := ℂ_[p]) (p := p)` to reduce the goal to its premises. Rewrite using `[← Function.iterate_add_apply, Nat.sub_add_cancel hlt.le, hrx, hrx, hr']`.

Take `⟨⟨a, s⟩, hs⟩` from `IsLocalization.surj (Submonoid.powers (p : ACris ℂ_[p] p)) x'`. Take `⟨k, hk⟩` from `s.2`. Simplify using `only at hs`. Establish `hsk : algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p) (s : ACris ℂ_[p] p) = ((p : BCrisPlus ℂ_[p] p)) ^ k`. Rewrite using `[← hk, map_pow, map_natCast]`.

Establish `hphik : ∀ n, (phiPlus ℂ_[p] p)^[n] (((p : BCrisPlus ℂ_[p] p)) ^ k) = ((p : BCrisPlus ℂ_[p] p)) ^ k`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => rfl`. Consider the case `succ n ih => rw [Function.iterate_succ_apply', ih, map_pow, map_natCast]`.

Establish `ha : (phi ℂ_[p] p)^[N] a = a`. Apply `algebraMap_aCris_injective` to reduce the goal to its premises. Rewrite using `[← phiPlus_iterate_algebraMap, ← hs, hsk, ← RingHom.coe_pow, map_mul, RingHom.coe_pow, hfix, hphik]`. Take `⟨u₀, -⟩` from `exists_theta_approx_of_phi_iterate hN ha 0`. Establish `hθa : ((theta ℂ_[p] p a : 𝒪) : ℂ_[p]) = ((r n₁ * (p : PadicAlgCl p) ^ k : PadicAlgCl p) : ℂ_[p])`.

Establish `h1 : iota ℂ_[p] p a = algClToBdR p (r n₁ * (p : PadicAlgCl p) ^ k)`. Rewrite using `[← iotaPlus_algebraMap, ← hs, map_mul, hsk, map_pow, map_natCast, hrx, map_mul, map_pow, map_natCast]`. Rewrite using `[← thetaField_iota, ← thetaAlgHom_apply, h1, thetaAlgHom_algClToBdR]`. Establish `hpnorm : ‖(p : ℂ_[p])‖ = ‖(p : PadicAlgCl p)‖`. Rewrite using `[← PadicComplex.coe_natCast, PadicComplex.norm_extends]`.

Establish `hmem : r n₁ * (p : PadicAlgCl p) ^ k ∈ unramifiedClosure p`. Use `mem_unramifiedClosure_of_forall_approx fun m => ?_` and prove the remaining obligations. Take `⟨u, hu, hu'⟩` from `exists_theta_approx_of_phi_iterate hN ha m`. Use `⟨u, hu, ?_⟩` and prove the remaining obligations. Rewrite `hu'` using `[hθa, ← UniformSpace.Completion.coe_sub, PadicComplex.norm_extends, hpnorm]`.

Conclude with `hu'`. Establish `hrU : r n₁ ∈ unramifiedClosure p`. Establish `hpk : ((p : PadicAlgCl p) ^ k) ∈ unramifiedClosure p` using `pow_mem (natCast_mem _ p) k`. Establish `hpk0 : ((p : PadicAlgCl p) ^ k) ≠ 0` using `pow_ne_zero _ (Nat.cast_ne_zero.2 hp.out.ne_zero)`. Use `mul_mem hmem (inv_mem hpk)` as an intermediate fact.

Rewrite `this` using `[mul_assoc, mul_inv_cancel₀ hpk0, mul_one]`. Then use the resulting hypothesis. Establish `hQr : aeval (r n₁) Q = 0`. Establish `h` using `(mem_roots (hQm.map (algebraMap ℚ_[p] (PadicAlgCl p))).ne_zero).1 (hr n₁)`. Rewrite `h` using `[IsRoot, eval_map, ← aeval_def]`. Then use the resulting hypothesis. Establish `hmin : minpoly ℚ_[p] (r n₁) = minpoly ℚ_[p] β` using `(minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hint) hQr hQm).symm`.

Take `⟨τ, hτ⟩` from `(Normal.minpoly_eq_iff_mem_orbit (PadicAlgCl p)).1 hmin`. Establish `hτ' : τ β = r n₁` using `hτ`. Establish `hβ : β = τ⁻¹ (r n₁)`. Rewrite using `[← hτ', ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]`. Rewrite using `[hβ]`.

Conclude with `gal_mem_unramifiedClosure τ⁻¹ hrU`.
-/
theorem mem_unramifiedClosure_of_iotaPlus_eq {x : BCrisPlus ℂ_[p] p} {β : PadicAlgCl p}
    (hx : iotaPlus ℂ_[p] p x = algClToBdR p β) : β ∈ unramifiedClosure p := by
  classical
  have hint : IsIntegral ℚ_[p] β := Algebra.IsIntegral.isIntegral β
  set Q := minpoly ℚ_[p] β
  have hQm : Q.Monic := minpoly.monic hint

  have hQ0 : aeval x Q = 0 := by
    apply iotaPlus_injective (K := ℂ_[p]) (p := p)
    rw [map_zero, ← iotaPlusAlg_apply, ← aeval_algHom_apply, iotaPlusAlg_apply, hx,
      aeval_algHom_apply, minpoly.aeval, map_zero]
  have hQn : ∀ n, aeval ((phiPlus ℂ_[p] p)^[n] x) Q = 0 := by
    intro n
    induction n with
    | zero => exact hQ0
    | succ n ih =>
      rw [Function.iterate_succ_apply', ← phiPlusAlg_apply, aeval_algHom_apply, ih, map_zero]
  have hroot : ∀ n, ∃ r ∈ (Q.map (algebraMap ℚ_[p] (PadicAlgCl p))).roots,
      iotaPlus ℂ_[p] p ((phiPlus ℂ_[p] p)^[n] x) = algClToBdR p r := fun n =>
    exists_root_of_aeval_eq_zero hQm (by
      rw [← iotaPlusAlg_apply, aeval_algHom_apply, hQn, map_zero])
  choose r hr hrx using hroot

  let f : ℕ → (Q.map (algebraMap ℚ_[p] (PadicAlgCl p))).roots.toFinset := fun n =>
    ⟨r n, Multiset.mem_toFinset.2 (hr n)⟩
  obtain ⟨a₁, a₂, hne, hf⟩ := Finite.exists_ne_map_eq_of_infinite f
  have hr12 : r a₁ = r a₂ := by
    have := congrArg Subtype.val hf
    simpa [f] using this
  obtain ⟨n₁, n₂, hlt, hr'⟩ : ∃ n₁ n₂, n₁ < n₂ ∧ r n₁ = r n₂ := by
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨a₁, a₂, h, hr12⟩
    · exact ⟨a₂, a₁, h, hr12.symm⟩
  set x' := (phiPlus ℂ_[p] p)^[n₁] x
  set N := n₂ - n₁
  have hN : 1 ≤ N := by omega
  have hfix : (phiPlus ℂ_[p] p)^[N] x' = x' := by
    apply iotaPlus_injective (K := ℂ_[p]) (p := p)
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hlt.le, hrx, hrx, hr']

  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers (p : ACris ℂ_[p] p)) x'
  obtain ⟨k, hk⟩ := s.2
  simp only at hs
  have hsk : algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p) (s : ACris ℂ_[p] p) =
      ((p : BCrisPlus ℂ_[p] p)) ^ k := by
    rw [← hk, map_pow, map_natCast]
  have hphik : ∀ n, (phiPlus ℂ_[p] p)^[n] (((p : BCrisPlus ℂ_[p] p)) ^ k) =
      ((p : BCrisPlus ℂ_[p] p)) ^ k := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', ih, map_pow, map_natCast]
  have ha : (phi ℂ_[p] p)^[N] a = a := by
    apply algebraMap_aCris_injective
    rw [← phiPlus_iterate_algebraMap, ← hs, hsk, ← RingHom.coe_pow, map_mul, RingHom.coe_pow,
      hfix, hphik]
  obtain ⟨u₀, -⟩ := exists_theta_approx_of_phi_iterate hN ha 0

  have hθa : ((theta ℂ_[p] p a : 𝒪) : ℂ_[p]) = ((r n₁ * (p : PadicAlgCl p) ^ k : PadicAlgCl p) : ℂ_[p]) := by
    have h1 : iota ℂ_[p] p a = algClToBdR p (r n₁ * (p : PadicAlgCl p) ^ k) := by
      rw [← iotaPlus_algebraMap, ← hs, map_mul, hsk, map_pow, map_natCast, hrx, map_mul, map_pow,
        map_natCast]
    rw [← thetaField_iota, ← thetaAlgHom_apply, h1, thetaAlgHom_algClToBdR]
  have hpnorm : ‖(p : ℂ_[p])‖ = ‖(p : PadicAlgCl p)‖ := by
    rw [← PadicComplex.coe_natCast, PadicComplex.norm_extends]
  have hmem : r n₁ * (p : PadicAlgCl p) ^ k ∈ unramifiedClosure p := by
    refine mem_unramifiedClosure_of_forall_approx fun m => ?_
    obtain ⟨u, hu, hu'⟩ := exists_theta_approx_of_phi_iterate hN ha m
    refine ⟨u, hu, ?_⟩
    rw [hθa, ← UniformSpace.Completion.coe_sub, PadicComplex.norm_extends, hpnorm] at hu'
    exact hu'
  have hrU : r n₁ ∈ unramifiedClosure p := by
    have hpk : ((p : PadicAlgCl p) ^ k) ∈ unramifiedClosure p := pow_mem (natCast_mem _ p) k
    have hpk0 : ((p : PadicAlgCl p) ^ k) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hp.out.ne_zero)
    have := mul_mem hmem (inv_mem hpk)
    rwa [mul_assoc, mul_inv_cancel₀ hpk0, mul_one] at this

  have hQr : aeval (r n₁) Q = 0 := by
    have h := (mem_roots (hQm.map (algebraMap ℚ_[p] (PadicAlgCl p))).ne_zero).1 (hr n₁)
    rwa [IsRoot, eval_map, ← aeval_def] at h
  have hmin : minpoly ℚ_[p] (r n₁) = minpoly ℚ_[p] β :=
    (minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hint) hQr hQm).symm
  obtain ⟨τ, hτ⟩ := (Normal.minpoly_eq_iff_mem_orbit (PadicAlgCl p)).1 hmin
  have hτ' : τ β = r n₁ := hτ
  have hβ : β = τ⁻¹ (r n₁) := by
    rw [← hτ', ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  rw [hβ]
  exact gal_mem_unramifiedClosure τ⁻¹ hrU

end Unramified

section Invariants

variable {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

/- English proof (translation)
Establish `h : (iotaPlus ℂ_[p] p).comp (galPlus σ) = (galBdRHom σ).comp (iotaPlus ℂ_[p] p)`. Apply `IsLocalization.ringHom_ext (Submonoid.powers (p : ACris ℂ_[p] p))` to reduce the goal to its premises. Use extensionality with `y`. Simplify using `only [RingHom.comp_apply]`. Rewrite using `[galPlus_algebraMap, iotaPlus_algebraMap, iotaPlus_algebraMap, ← gal_smul_def, iota_gal_smul]`.

Both sides reduce to the same expression. Conclude with `RingHom.congr_fun h x`.
-/
theorem iotaPlus_gal_smul (σ : Gal(PadicAlgCl p/K)) (x : BCrisPlus ℂ_[p] p) :
    iotaPlus ℂ_[p] p (σ • x) = σ • iotaPlus ℂ_[p] p x := by
  have h : (iotaPlus ℂ_[p] p).comp (galPlus σ) = (galBdRHom σ).comp (iotaPlus ℂ_[p] p) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (p : ACris ℂ_[p] p))
    ext y
    simp only [RingHom.comp_apply]
    rw [galPlus_algebraMap, iotaPlus_algebraMap, iotaPlus_algebraMap, ← gal_smul_def,
      iota_gal_smul]
    rfl
  exact RingHom.congr_fun h x

variable [FiniteDimensional ℚ_[p] K]

/- English proof (translation)
Take `⟨k, hk⟩` from `bDeRhamPlus_fixed K (iotaPlus ℂ_[p] p x) fun σ => by`. Rewrite using `[← iotaPlus_gal_smul, hx σ]`. Conclude with `⟨k, ⟨k.2, mem_unramifiedClosure_of_iotaPlus_eq hk.symm⟩, hk.symm⟩`.
-/
theorem bCrisPlus_fixed (x : BCrisPlus ℂ_[p] p) (hx : ∀ σ : Gal(PadicAlgCl p/K), σ • x = x) :
    ∃ k ∈ maxUnramified p K, iotaPlus ℂ_[p] p x = algClToBdR p k := by
  obtain ⟨k, hk⟩ := bDeRhamPlus_fixed K (iotaPlus ℂ_[p] p x) fun σ => by
    rw [← iotaPlus_gal_smul, hx σ]
  exact ⟨k, ⟨k.2, mem_unramifiedClosure_of_iotaPlus_eq hk.symm⟩, hk.symm⟩

omit [FiniteDimensional ℚ_[p] K] in

/- English proof (translation)
Take `⟨x, hx⟩` from `(mem_algClInBCrisPlus (p := p)).1 (unramifiedClosure_le hk.2)`. Use `⟨x, fun σ => iotaPlus_injective (K := ℂ_[p]) (p := p) ?_, hx⟩` and prove the remaining obligations. Rewrite using `[iotaPlus_gal_smul, hx, gal_smul_algClToBdR]`. Use `congr 1`. Conclude with `σ.commutes ⟨k, hk.1⟩`.
-/
theorem exists_bCrisPlus_fixed {k : PadicAlgCl p} (hk : k ∈ maxUnramified p K) :
    ∃ x : BCrisPlus ℂ_[p] p, (∀ σ : Gal(PadicAlgCl p/K), σ • x = x) ∧
      iotaPlus ℂ_[p] p x = algClToBdR p k := by
  obtain ⟨x, hx⟩ := (mem_algClInBCrisPlus (p := p)).1 (unramifiedClosure_le hk.2)
  refine ⟨x, fun σ => iotaPlus_injective (K := ℂ_[p]) (p := p) ?_, hx⟩
  rw [iotaPlus_gal_smul, hx, gal_smul_algClToBdR]
  congr 1
  exact σ.commutes ⟨k, hk.1⟩

/- English proof (translation)
Use extensionality with `b`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Take `⟨k, hk, hxk⟩` from `bCrisPlus_fixed x hx`. Conclude with `⟨k, hk, hxk.symm⟩`.

Introduce and unpack `⟨k, hk, rfl⟩`. Take `⟨x, hx, hxk⟩` from `exists_bCrisPlus_fixed hk`. Conclude with `⟨x, hx, hxk⟩`.
-/
theorem image_iotaPlus_fixedPoints :
    iotaPlus ℂ_[p] p '' MulAction.fixedPoints Gal(PadicAlgCl p/K) (BCrisPlus ℂ_[p] p) =
      algClToBdR p '' (maxUnramified p K : Set (PadicAlgCl p)) := by
  ext b
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨k, hk, hxk⟩ := bCrisPlus_fixed x hx
    exact ⟨k, hk, hxk.symm⟩
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨x, hx, hxk⟩ := exists_bCrisPlus_fixed hk
    exact ⟨x, hx, hxk⟩

end Invariants

end ACris

end GroundTheory.PAdicHodge
