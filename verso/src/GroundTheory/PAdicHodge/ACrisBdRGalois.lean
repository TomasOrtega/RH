import Mathlib
import GroundTheory.PAdicHodge.ACrisBdRInj
import GroundTheory.PAdicHodge.ACrisLog
import GroundTheory.PAdicHodge.ACrisGalois
import GroundTheory.PAdicHodge.InstMulSemiringActionGalPlus
import GroundTheory.PAdicHodge.BdRGalois
import GroundTheory.PAdicHodge.UntiltFrobeniusEquivSymmEpsilonNeOne
import GroundTheory.PAdicHodge.BdRAlg
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open _root_.WittVector IsLocalRing

namespace ACris

section Plus

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p] [CharZero K]

/- English proof (translation)
Apply `iota_injective (K := K) (p := p)` to reduce the goal to its premises. Establish `h1` using `congrArg (iota K p) h`. Rewrite `h1` using `[map_mul, map_natCast, map_zero]`. Rewrite using `[map_zero]`. Conclude with `((IsPerfectoidField.isUnit_natCast_p_bDeRhamPlus (K := K) p).mul_right_eq_zero).1 h1`.
-/
theorem eq_zero_of_p_mul_eq_zero {x : ACris K p} (h : (p : ACris K p) * x = 0) : x = 0 := by
  apply iota_injective (K := K) (p := p)
  have h1 := congrArg (iota K p) h
  rw [map_mul, map_natCast, map_zero] at h1
  rw [map_zero]
  exact ((IsPerfectoidField.isUnit_natCast_p_bDeRhamPlus (K := K) p).mul_right_eq_zero).1 h1

variable (K p) in

def iotaPlus : BCrisPlus K p →+* BDeRhamPlus (normInteger K) p :=
  Localization.awayLift (iota K p) (p : ACris K p) (by
    rw [map_natCast]
    exact IsPerfectoidField.isUnit_natCast_p_bDeRhamPlus (K := K) p)

/- English proof (translation)
The claim follows from `IsLocalization.lift_eq _ x`.
-/
theorem iotaPlus_algebraMap (x : ACris K p) :
    iotaPlus K p (algebraMap (ACris K p) (BCrisPlus K p) x) = iota K p x :=
  IsLocalization.lift_eq _ x

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Take `⟨⟨a, s⟩, rfl⟩` from `IsLocalization.mk'_surjective (Submonoid.powers (p : ACris K p)) x`. Establish `h` using `IsLocalization.mk'_spec (BCrisPlus K p) a s`. Establish `h2` using `congrArg (iotaPlus K p) h`.

Rewrite `h2` using `[map_mul, hx, zero_mul, iotaPlus_algebraMap]`. Establish `ha : a = 0` using `iota_injective (K := K) (p := p) (by rw [← h2, map_zero])`. Substitute `ha` using the available equality. Conclude with `IsLocalization.mk'_zero _`.
-/
theorem iotaPlus_injective : Function.Injective (iotaPlus K p) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (p : ACris K p)) x
  have h := IsLocalization.mk'_spec (BCrisPlus K p) a s
  have h2 := congrArg (iotaPlus K p) h
  rw [map_mul, hx, zero_mul, iotaPlus_algebraMap] at h2
  have ha : a = 0 := iota_injective (K := K) (p := p) (by rw [← h2, map_zero])
  subst ha
  exact IsLocalization.mk'_zero _

/- English proof (translation)
The claim follows from `AdicCompletion.extendRingHom_of _ _ _ _ y`.
-/
theorem iotaM_of (m : ℕ) (y : ACrisZero K p) :
    embedding₂ K p m (_root_.AdicCompletion.of _ _ y) = iotaZero K p m y :=
  AdicCompletion.extendRingHom_of _ _ _ _ y

/- English proof (translation)
Rewrite using `[mk_eq_zero_iff]`. Rewrite `hx` using `[ker_eq_span_xiGen]`. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.1 hx`. Use `⟨dpow n c * algebraMap (AInf K p) _ (xiGen K p) ^ (n - m), ?_⟩` and prove the remaining obligations. Establish `hpow : algebraMap (AInf K p) (Localization.Away (p : AInf K p)) (xiGen K p) ^ n = algebraMap (AInf K p) _ (xiGen K p) ^ m * algebraMap (AInf K p) _ (xiGen K p) ^ (n - m)`.

Rewrite using `[← pow_add, Nat.add_sub_cancel' h]`. Rewrite using `[dpow_mul, map_pow, hpow]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mk_dpow_eq_zero {x : AInf K p} (hx : x ∈ RingHom.ker (fontaineTheta (normInteger K) p))
    {m n : ℕ} (h : m ≤ n) :
    Ideal.Quotient.mk (kerAway K p ^ m) (dpow n x) = 0 := by
  rw [mk_eq_zero_iff]
  rw [ker_eq_span_xiGen] at hx
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hx
  refine ⟨dpow n c * algebraMap (AInf K p) _ (xiGen K p) ^ (n - m), ?_⟩
  have hpow : algebraMap (AInf K p) (Localization.Away (p : AInf K p)) (xiGen K p) ^ n =
      algebraMap (AInf K p) _ (xiGen K p) ^ m * algebraMap (AInf K p) _ (xiGen K p) ^ (n - m) := by
    rw [← pow_add, Nat.add_sub_cancel' h]
  rw [dpow_mul, map_pow, hpow]
  ring

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Establish `hle : Ideal.span {(p : ACris K p)} ≤ (Ideal.span {(p : acrisQ K p m)}).comap (embedding₂ K p m)`. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_natCast]`. Conclude with `Ideal.mem_span_singleton_self _`. Establish `hsum` using `(isAdicSum_log hx).map (embedding₂ K p m) hle`. Establish `hterm : ∀ n, ((embedding₂ K p m (logTerm hx n) : acrisQ K p m) : Localization.Away (p : AInf K p) ⧸ kerAway K p ^ m) = Ideal.Quotient.mk (kerAway K p ^ m) (logTermZero hx n : Localization.Away (p : AInf K p))` using `fun n => by`.

Rewrite using `[logTerm, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, iotaM_of]`. Both sides reduce to the same expression. Establish `hzero : ∀ n, m ≤ n → embedding₂ K p m (logTerm hx n) = 0` using `fun n hn => by`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hterm, ZeroMemClass.coe_zero, logTermZero]`.

Simplify using `only [Subalgebra.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_neg, Subalgebra.coe_one, SubringClass.coe_natCast, coe_dpowZero, map_mul, mk_dpow_eq_zero hx (Nat.le_succ_of_le hn), mul_zero]`. Establish `h0` using `isAdicSum_of_eq_zero (I := Ideal.span {(p : acrisQ K p m)}) hzero`. Establish `h` using `hsum.unique h0`. Rewrite using `[iotaQ, RingHom.comp_apply, h, map_sum, map_sum]`. Conclude with `Finset.sum_congr rfl fun n _ => hterm n`.
-/
theorem iotaQ_log {x : AInf K p} (hx : x ∈ RingHom.ker (fontaineTheta (normInteger K) p)) (m : ℕ) :
    iotaQ K p m (log hx) = Ideal.Quotient.mk (kerAway K p ^ m)
      (∑ n ∈ Finset.range m, (logTermZero hx n : Localization.Away (p : AInf K p))) := by
  have hle : Ideal.span {(p : ACris K p)} ≤
      (Ideal.span {(p : acrisQ K p m)}).comap (embedding₂ K p m) := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_natCast]
    exact Ideal.mem_span_singleton_self _
  have hsum := (isAdicSum_log hx).map (embedding₂ K p m) hle
  have hterm : ∀ n, ((embedding₂ K p m (logTerm hx n) : acrisQ K p m) :
      Localization.Away (p : AInf K p) ⧸ kerAway K p ^ m) =
      Ideal.Quotient.mk (kerAway K p ^ m) (logTermZero hx n : Localization.Away (p : AInf K p)) :=
    fun n => by
      rw [logTerm, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        iotaM_of]
      rfl
  have hzero : ∀ n, m ≤ n → embedding₂ K p m (logTerm hx n) = 0 := fun n hn => by
    apply Subtype.ext
    rw [hterm, ZeroMemClass.coe_zero, logTermZero]
    simp only [Subalgebra.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_neg, Subalgebra.coe_one,
      SubringClass.coe_natCast, coe_dpowZero, map_mul, mk_dpow_eq_zero hx (Nat.le_succ_of_le hn),
      mul_zero]
  have h0 := isAdicSum_of_eq_zero (I := Ideal.span {(p : acrisQ K p m)}) hzero
  have h := hsum.unique h0
  rw [iotaQ, RingHom.comp_apply, h, map_sum, map_sum]
  exact Finset.sum_congr rfl fun n _ => hterm n

end Plus

section Cp

variable {p : ℕ} [hp : Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

local notation "𝒪♭" => PreTilt (normInteger ℂ_[p]) p
local notation "𝔸" => Localization.Away (p : AInf ℂ_[p] p)
local notation "𝔹" => BDeRhamPlus (normInteger ℂ_[p]) p
local notation "θ" => fontaineTheta (normInteger ℂ_[p]) p

def galS (σ : Gal(PadicAlgCl p/K)) (m : ℕ) : acrisQ ℂ_[p] p m →+* acrisQ ℂ_[p] p m :=
  ((galQuot σ m).comp (acrisQ ℂ_[p] p m).subtype).codRestrict (acrisQ ℂ_[p] p m) fun s => by
    obtain ⟨y, hy, hys⟩ := s.2
    rw [RingHom.comp_apply, Subring.subtype_apply, ← hys, galQuot_mk]
    exact ⟨ACris.galAway σ y, galAway_mem σ hy, rfl⟩

set_option maxHeartbeats 2000000 in
/- English proof (translation)
Use `ringHom_ext fun y => ?_` and prove the remaining obligations. Establish `h1 : galCris σ (_root_.AdicCompletion.of _ _ y) = _root_.AdicCompletion.of _ _ (σ • y)` using `galCris_of σ y`. Establish `h2` using `iotaM_of (p := p) m (σ • y)`. Establish `h3` using `iotaM_of (p := p) m y`. Rewrite using `[RingHom.comp_apply, RingHom.comp_apply, h1, h2, h3]`.

Apply `Subtype.ext` to reduce the goal to its premises. Use `show Ideal.Quotient.mk _ _ = galQuot σ m (Ideal.Quotient.mk _ _)`. Rewrite using `[galQuot_mk]`. Use `show Ideal.Quotient.mk _ ((σ • y : ACrisZero ℂ_[p] p) : 𝔸) = Ideal.Quotient.mk _ _`. Rewrite using `[coe_gal_smul_zero]`.

Both sides reduce to the same expression.
-/
theorem iotaM_gal_smul (σ : Gal(PadicAlgCl p/K)) (m : ℕ) :
    (embedding₂ ℂ_[p] p m).comp (galCris σ) = (galS σ m).comp (embedding₂ ℂ_[p] p m) := by
  refine ringHom_ext fun y => ?_
  have h1 : galCris σ (_root_.AdicCompletion.of _ _ y) = _root_.AdicCompletion.of _ _ (σ • y) :=
    galCris_of σ y
  have h2 := iotaM_of (p := p) m (σ • y)
  have h3 := iotaM_of (p := p) m y
  rw [RingHom.comp_apply, RingHom.comp_apply, h1, h2, h3]
  apply Subtype.ext
  show Ideal.Quotient.mk _ _ = galQuot σ m (Ideal.Quotient.mk _ _)
  rw [galQuot_mk]
  show Ideal.Quotient.mk _ ((σ • y : ACrisZero ℂ_[p] p) : 𝔸) = Ideal.Quotient.mk _ _
  rw [coe_gal_smul_zero]
  rfl

/- English proof (translation)
Rewrite using `[gal_smul_def, gal_smul_bdR_def]`. Use `IsPerfectoidField.evalB_ext (K := ℂ_[p]) (p := p) fun m => ?_` and prove the remaining obligations. Rewrite using `[evalB_galBdRHom]`. Express the relevant statement in the definitionally equal form `_root_.AdicCompletion.evalₐ (kerAway ℂ_[p] p) m (iota ℂ_[p] p (galCris σ x)) = galQuot σ m (_root_.AdicCompletion.evalₐ (kerAway ℂ_[p] p) m (iota ℂ_[p] p x))`. Rewrite using `[evalₐ_iota, evalₐ_iota]`.

Establish `h` using `congrArg (fun F => ((F x : acrisQ ℂ_[p] p m) : 𝔸 ⧸ kerAway ℂ_[p] p ^ m)) (iotaM_gal_smul σ m)`. Conclude with `h`.
-/
theorem iota_gal_smul (σ : Gal(PadicAlgCl p/K)) (x : ACris ℂ_[p] p) :
    iota ℂ_[p] p (σ • x) = σ • iota ℂ_[p] p x := by
  rw [gal_smul_def, gal_smul_bdR_def]
  refine IsPerfectoidField.evalB_ext (K := ℂ_[p]) (p := p) fun m => ?_
  rw [evalB_galBdRHom]
  change _root_.AdicCompletion.evalₐ (kerAway ℂ_[p] p) m (iota ℂ_[p] p (galCris σ x)) =
    galQuot σ m (_root_.AdicCompletion.evalₐ (kerAway ℂ_[p] p) m (iota ℂ_[p] p x))
  rw [evalₐ_iota, evalₐ_iota]
  have h := congrArg (fun F => ((F x : acrisQ ℂ_[p] p m) : 𝔸 ⧸ kerAway ℂ_[p] p ^ m))
    (iotaM_gal_smul σ m)
  exact h

/- English proof (translation)
Rewrite using `[iota_algebraMap, IsPerfectoidField.algebraMap_padic_coe]`.
-/
theorem iota_padicInt (a : ℤ_[p]) :
    iota ℂ_[p] p (algebraMap (AInf ℂ_[p] p) (ACris ℂ_[p] p) (IsPerfectoidField.padicIntToWitt p a)) =
      algebraMap ℚ_[p] 𝔹 (a : ℚ_[p]) := by
  rw [iota_algebraMap, IsPerfectoidField.algebraMap_padic_coe]

/- English proof (translation)
Establish `hu : IsUnit ((n + 1 : ℕ) : 𝔹)`. Use `(isUnit_natCast (K := ℂ_[p]) (p := p) (Nat.succ_ne_zero n)).map (toBDeRhamPlus (normInteger ℂ_[p]) p)` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis. Apply `hu.mul_left_cancel` to reduce the goal to its premises. Establish `e1 : ((n + 1 : ℕ) : 𝔹) * algebraMap ℚ 𝔹 (1 / (n + 1 : ℚ)) = 1`.

Rewrite using `[← map_natCast (algebraMap ℚ 𝔹), ← map_mul, ← map_one (algebraMap ℚ 𝔹)]`. Use `congr 1`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[map_mul (toBDeRhamPlus (normInteger ℂ_[p]) p) ((n + 1 : ℕ) : 𝔸), map_natCast]`. Use `_ = toBDeRhamPlus (normInteger ℂ_[p]) p (algebraMap (AInf ℂ_[p] p) 𝔸 x ^ (n + 1)) := by`. Rewrite using `[← mul_assoc, ← Nat.cast_mul, ← Nat.factorial_succ, factorial_mul_dpow]`. Use `_ = wittToBDeRhamPlus (normInteger ℂ_[p]) p x ^ (n + 1) := by rw [map_pow]; rfl`. Use `_ = ((n + 1 : ℕ) : 𝔹) * (algebraMap ℚ 𝔹 (1 / (n + 1 : ℚ)) * wittToBDeRhamPlus (normInteger ℂ_[p]) p x ^ (n + 1)) := by rw [← mul_assoc, e1, one_mul]`.
-/
theorem toBDeRhamPlus_factorial_mul_dpow (x : AInf ℂ_[p] p) (n : ℕ) :
    toBDeRhamPlus (normInteger ℂ_[p]) p ((n.factorial : 𝔸) * dpow (n + 1) x) =
      algebraMap ℚ 𝔹 (1 / (n + 1 : ℚ)) * wittToBDeRhamPlus (normInteger ℂ_[p]) p x ^ (n + 1) := by
  have hu : IsUnit ((n + 1 : ℕ) : 𝔹) := by
    have := (isUnit_natCast (K := ℂ_[p]) (p := p) (Nat.succ_ne_zero n)).map
      (toBDeRhamPlus (normInteger ℂ_[p]) p)
    rwa [map_natCast] at this
  apply hu.mul_left_cancel
  have e1 : ((n + 1 : ℕ) : 𝔹) * algebraMap ℚ 𝔹 (1 / (n + 1 : ℚ)) = 1 := by
    rw [← map_natCast (algebraMap ℚ 𝔹), ← map_mul, ← map_one (algebraMap ℚ 𝔹)]
    congr 1
    push_cast
    field_simp
  calc ((n + 1 : ℕ) : 𝔹) * toBDeRhamPlus (normInteger ℂ_[p]) p ((n.factorial : 𝔸) * dpow (n + 1) x)
      = toBDeRhamPlus (normInteger ℂ_[p]) p (((n + 1 : ℕ) : 𝔸) * ((n.factorial : 𝔸) * dpow (n + 1) x)) := by
        rw [map_mul (toBDeRhamPlus (normInteger ℂ_[p]) p) ((n + 1 : ℕ) : 𝔸), map_natCast]
    _ = toBDeRhamPlus (normInteger ℂ_[p]) p (algebraMap (AInf ℂ_[p] p) 𝔸 x ^ (n + 1)) := by
        rw [← mul_assoc, ← Nat.cast_mul, ← Nat.factorial_succ, factorial_mul_dpow]
    _ = wittToBDeRhamPlus (normInteger ℂ_[p]) p x ^ (n + 1) := by rw [map_pow]; rfl
    _ = ((n + 1 : ℕ) : 𝔹) * (algebraMap ℚ 𝔹 (1 / (n + 1 : ℚ)) *
        wittToBDeRhamPlus (normInteger ℂ_[p]) p x ^ (n + 1)) := by rw [← mul_assoc, e1, one_mul]

/- English proof (translation)
Use `IsPerfectoidField.evalB_ext (K := ℂ_[p]) (p := p) fun m => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_root_.AdicCompletion.evalₐ (kerAway ℂ_[p] p) m (iota ℂ_[p] p (periodT hε)) = IsPerfectoidField.evalB ℂ_[p] p m (fontaineT ε hε)`. Rewrite using `[evalₐ_iota, periodT, iotaQ_log]`. Establish `h1` using `Ideal.pow_le_pow_right (Nat.le_succ m) (fontaineT_sub_sum_mem hε (m + 1))`. Rewrite `h1` using `[← IsPerfectoidField.ker_evalB, RingHom.mem_ker, map_sub, sub_eq_zero]`.

Rewrite using `[h1, ← IsPerfectoidField.evalB_toBDeRhamPlus]`. Use `congr 1`. Rewrite using `[map_sum, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]`. Use `Finset.sum_congr rfl fun n _ => ?_` and prove the remaining obligations. Rewrite using `[logTermZero]`.

Simplify using `only [Subalgebra.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_neg, Subalgebra.coe_one, SubringClass.coe_natCast, coe_dpowZero]`. Rewrite using `[mul_assoc, map_mul, toBDeRhamPlus_factorial_mul_dpow, map_pow, map_neg, map_one, muBdR, add_comm 1 n]`. Establish `e : algebraMap ℚ 𝔹 ((-1) ^ (n + 1 + 1) / ((n + 1 : ℕ) : ℚ)) = (-1) ^ n * algebraMap ℚ 𝔹 (1 / (n + 1 : ℚ))`. Rewrite using `[← map_one (algebraMap ℚ 𝔹), ← map_neg, ← map_pow, ← map_mul]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem iota_periodT {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1) :
    iota ℂ_[p] p (periodT hε) = fontaineT ε hε := by
  refine IsPerfectoidField.evalB_ext (K := ℂ_[p]) (p := p) fun m => ?_
  change _root_.AdicCompletion.evalₐ (kerAway ℂ_[p] p) m (iota ℂ_[p] p (periodT hε)) =
    IsPerfectoidField.evalB ℂ_[p] p m (fontaineT ε hε)
  rw [evalₐ_iota, periodT, iotaQ_log]
  have h1 := Ideal.pow_le_pow_right (Nat.le_succ m) (fontaineT_sub_sum_mem hε (m + 1))
  rw [← IsPerfectoidField.ker_evalB, RingHom.mem_ker, map_sub, sub_eq_zero] at h1
  rw [h1, ← IsPerfectoidField.evalB_toBDeRhamPlus]
  congr 1
  rw [map_sum, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [logTermZero]
  simp only [Subalgebra.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_neg, Subalgebra.coe_one,
    SubringClass.coe_natCast, coe_dpowZero]
  rw [mul_assoc, map_mul, toBDeRhamPlus_factorial_mul_dpow, map_pow, map_neg, map_one, muBdR,
    add_comm 1 n]
  have e : algebraMap ℚ 𝔹 ((-1) ^ (n + 1 + 1) / ((n + 1 : ℕ) : ℚ)) =
      (-1) ^ n * algebraMap ℚ 𝔹 (1 / (n + 1 : ℚ)) := by
    rw [← map_one (algebraMap ℚ 𝔹), ← map_neg, ← map_pow, ← map_mul]
    congr 1
    push_cast
    ring
  rw [e]
  ring

/- English proof (translation)
Introduce `h`. Establish `h1` using `iota_periodT hε`. Rewrite `h1` using `[h, map_zero]`. Conclude with `fontaineT_ne_zero hε hζ h1.symm`.
-/
theorem periodT_ne_zero {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1)
    (hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ≠ 1) :
    periodT hε ≠ 0 := by
  intro h
  have h1 := iota_periodT hε
  rw [h, map_zero] at h1
  exact fontaineT_ne_zero hε hζ h1.symm

end Cp

end ACris

end GroundTheory.PAdicHodge
