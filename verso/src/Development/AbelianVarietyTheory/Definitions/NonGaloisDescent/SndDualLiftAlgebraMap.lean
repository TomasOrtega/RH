import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormPowLeNormFactorial
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DerivationMemPow

noncomputable section

namespace GlobalTheory.BK

open PowerSeries Filter Topology

section General

variable {A' B : Type} [CommRing A'] [CommRing B] (ι : A' →+* B) (s : A')

structure SameJets : Prop where
  div : ∀ (m : ℕ) (x : B), ∃ g h, x = ι g + ι s ^ m * h
  dvd : ∀ (m : ℕ) (g : A') (h : B), ι g = ι s ^ m * h → s ^ m ∣ g

def jetMap (m : ℕ) : A' ⧸ Ideal.span {s} ^ m →+* B ⧸ Ideal.span {ι s ^ m} :=
  Ideal.quotientMap _ ι (by
    rw [Ideal.span_singleton_pow, Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_pow]
    exact Ideal.mem_span_singleton_self _)

variable {ι s}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Take `⟨g, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Rewrite `hx` using `[jetMap, Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]`.

Take `⟨h, hh⟩` from `hx`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`. Conclude with `H.dvd m g h hh`. Introduce `y`. Take `⟨x, rfl⟩` from `Ideal.Quotient.mk_surjective y`.

Take `⟨g, h, rfl⟩` from `H.div m x`. Use `⟨Ideal.Quotient.mk _ g, ?_⟩` and prove the remaining obligations. Rewrite using `[jetMap, Ideal.quotientMap_mk, Ideal.Quotient.eq, Ideal.mem_span_singleton]`. Conclude with `⟨-h, by ring⟩`.
-/
theorem SameJets.bijective (H : SameJets ι s) (m : ℕ) : Function.Bijective (jetMap ι s m) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [jetMap, Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_span_singleton] at hx
    obtain ⟨h, hh⟩ := hx
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact H.dvd m g h hh
  · intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨g, h, rfl⟩ := H.div m x
    refine ⟨Ideal.Quotient.mk _ g, ?_⟩
    rw [jetMap, Ideal.quotientMap_mk, Ideal.Quotient.eq, Ideal.mem_span_singleton]
    exact ⟨-h, by ring⟩

def SameJets.jet (H : SameJets ι s) (m : ℕ) : B →+* A' ⧸ Ideal.span {s} ^ m :=
  (RingEquiv.ofBijective _ (H.bijective m)).symm.toRingHom.comp (Ideal.Quotient.mk _)

/- English proof (translation)
Rewrite using `[SameJets.jet, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.symm_apply_eq, RingEquiv.coe_ofBijective, jetMap, Ideal.quotientMap_mk, Ideal.Quotient.eq, Ideal.mem_span_singleton]`.
-/
theorem SameJets.jet_eq_iff (H : SameJets ι s) (m : ℕ) (x : B) (g : A') :
    H.jet m x = Ideal.Quotient.mk _ g ↔ ι s ^ m ∣ x - ι g := by
  rw [SameJets.jet, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    RingEquiv.symm_apply_eq, RingEquiv.coe_ofBijective, jetMap, Ideal.quotientMap_mk,
    Ideal.Quotient.eq, Ideal.mem_span_singleton]

/- English proof (translation)
Use extensionality with `x`. Take `⟨g, h, hx⟩` from `H.div n x`. Establish `h1 : ι s ^ n ∣ x - ι g` using `⟨h, by rw [hx]; ring⟩`. Rewrite using `[RingHom.comp_apply, (H.jet_eq_iff n x g).2 h1, (H.jet_eq_iff m x g).2 ((pow_dvd_pow _ hle).trans h1)]`. Both sides reduce to the same expression.
-/
theorem SameJets.jet_compat (H : SameJets ι s) {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow (Ideal.span {s}) hle).comp (H.jet n) = H.jet m := by
  ext x
  obtain ⟨g, h, hx⟩ := H.div n x
  have h1 : ι s ^ n ∣ x - ι g := ⟨h, by rw [hx]; ring⟩
  rw [RingHom.comp_apply, (H.jet_eq_iff n x g).2 h1,
    (H.jet_eq_iff m x g).2 ((pow_dvd_pow _ hle).trans h1)]
  rfl

def SameJets.toCompl (H : SameJets ι s) : B →+* AdicCompletion (Ideal.span {s}) A' :=
  AdicCompletion.liftRingHom _ H.jet H.jet_compat

/- English proof (translation)
Rewrite using `[SameJets.toCompl, AdicCompletion.evalₐ_liftRingHom, H.jet_eq_iff]`.
-/
theorem SameJets.evalₐ_toCompl_eq_iff (H : SameJets ι s) (m : ℕ) (x : B) (g : A') :
    AdicCompletion.evalₐ _ m (H.toCompl x) = Ideal.Quotient.mk _ g ↔ ι s ^ m ∣ x - ι g := by
  rw [SameJets.toCompl, AdicCompletion.evalₐ_liftRingHom, H.jet_eq_iff]

/- English proof (translation)
Use `AdicCompletion.ext_evalₐ fun m => ?_` and prove the remaining obligations. Rewrite using `[(H.evalₐ_toCompl_eq_iff m _ g).2 (by simp), AlgHom.commutes]`. Both sides reduce to the same expression.
-/
theorem SameJets.toCompl_ι (H : SameJets ι s) (g : A') :
    H.toCompl (ι g) = algebraMap A' _ g := by
  refine AdicCompletion.ext_evalₐ fun m => ?_
  rw [(H.evalₐ_toCompl_eq_iff m _ g).2 (by simp), AlgHom.commutes]
  rfl

variable {k : Type} [CommRing k] [Algebra k A'] (I : Ideal A') (D : Derivation k A' A')

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.DerivationPowerIdeal.derivation_mem_pow`. Consider the case `exact _root_.GlobalTheory.DerivationPowerIdeal.derivation_mem_pow`. Consider the case `(apply _root_.GlobalTheory.DerivationPowerIdeal.derivation_mem_pow <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.DerivationPowerIdeal.derivation_mem_pow <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.DerivationPowerIdeal.derivation_mem_pow <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.DerivationPowerIdeal.derivation_mem_pow ..)`.
-/
theorem derivation_mem_pow (n : ℕ) {x : A'} (hx : x ∈ I ^ (n + 1)) : D x ∈ I ^ n := by
  first
  | exact @_root_.GlobalTheory.DerivationPowerIdeal.derivation_mem_pow
  | exact _root_.GlobalTheory.DerivationPowerIdeal.derivation_mem_pow
  | (apply _root_.GlobalTheory.DerivationPowerIdeal.derivation_mem_pow <;> assumption)
  | (intros; apply _root_.GlobalTheory.DerivationPowerIdeal.derivation_mem_pow <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DerivationPowerIdeal.derivation_mem_pow <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DerivationPowerIdeal.derivation_mem_pow ..)

/- English proof (translation)
Take `⟨c, rfl⟩` from `AdicCompletion.mk_surjective I A' x`. Rewrite `h`, the goal using `[AdicCompletion.evalₐ_mk]`. Rewrite using `[← AdicCompletion.Ideal.mk_eq_mk I n.le_succ c]`. Rewrite `h`, the goal using `[Ideal.Quotient.eq]`. Conclude with `Ideal.pow_le_pow_right n.le_succ h`.
-/
theorem evalₐ_of_succ {x : AdicCompletion I A'} {n : ℕ} {r : A'}
    (h : AdicCompletion.evalₐ I (n + 1) x = Ideal.Quotient.mk _ r) :
    AdicCompletion.evalₐ I n x = Ideal.Quotient.mk _ r := by
  obtain ⟨c, rfl⟩ := AdicCompletion.mk_surjective I A' x
  rw [AdicCompletion.evalₐ_mk] at h ⊢
  rw [← AdicCompletion.Ideal.mk_eq_mk I n.le_succ c]
  rw [Ideal.Quotient.eq] at h ⊢
  exact Ideal.pow_le_pow_right n.le_succ h

def cauchyDer (c : AdicCompletion.AdicCauchySequence I A') :
    AdicCompletion.AdicCauchySequence I A' :=
  ⟨fun n => D (c.val (n + 1)), fun {m n} hmn => by
    have h := AdicCompletion.Ideal.mk_eq_mk I (Nat.succ_le_succ hmn) c
    rw [Ideal.Quotient.eq] at h
    rw [SModEq.sub_mem, ← map_sub]
    have := derivation_mem_pow I D m ((Ideal.neg_mem_iff _).2 h)
    simpa using this⟩

def complDerFun (x : AdicCompletion I A') : AdicCompletion I A' :=
  AdicCompletion.mk I A' (cauchyDer I D (AdicCompletion.mk_surjective I A' x).choose)

/- English proof (translation)
Rewrite `h` using `[← (AdicCompletion.mk_surjective I A' x).choose_spec, AdicCompletion.evalₐ_mk, Ideal.Quotient.eq]`. Rewrite using `[complDerFun, AdicCompletion.evalₐ_mk, Ideal.Quotient.eq]`. Conclude with `map_sub D _ _ ▸ derivation_mem_pow I D n h`.
-/
theorem evalₐ_complDerFun {x : AdicCompletion I A'} {n : ℕ} {r : A'}
    (h : AdicCompletion.evalₐ I (n + 1) x = Ideal.Quotient.mk _ r) :
    AdicCompletion.evalₐ I n (complDerFun I D x) = Ideal.Quotient.mk _ (D r) := by
  rw [← (AdicCompletion.mk_surjective I A' x).choose_spec, AdicCompletion.evalₐ_mk,
    Ideal.Quotient.eq] at h
  rw [complDerFun, AdicCompletion.evalₐ_mk, Ideal.Quotient.eq]
  exact map_sub D _ _ ▸ derivation_mem_pow I D n h

/- English proof (translation)
Use `AdicCompletion.ext_evalₐ fun n => ?_` and prove the remaining obligations. Take `⟨r, hr⟩` from `Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I (n + 1) x)`. Take `⟨t, ht⟩` from `Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I (n + 1) y)`. Rewrite using `[evalₐ_complDerFun I D (r := r * t) (by rw [map_mul, map_mul, hr, ht]), map_add, map_mul (AdicCompletion.evalₐ I n), map_mul (AdicCompletion.evalₐ I n), evalₐ_complDerFun I D hr.symm, evalₐ_complDerFun I D ht.symm, evalₐ_of_succ I hr.symm, evalₐ_of_succ I ht.symm, D.leibniz]`. Simplify using the standard rewrite rules.
-/
theorem complDerFun_mul (x y : AdicCompletion I A') :
    complDerFun I D (x * y) = x * complDerFun I D y + y * complDerFun I D x := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I (n + 1) x)
  obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I (n + 1) y)
  rw [evalₐ_complDerFun I D (r := r * t) (by rw [map_mul, map_mul, hr, ht]), map_add,
    map_mul (AdicCompletion.evalₐ I n), map_mul (AdicCompletion.evalₐ I n),
    evalₐ_complDerFun I D hr.symm, evalₐ_complDerFun I D ht.symm,
    evalₐ_of_succ I hr.symm, evalₐ_of_succ I ht.symm, D.leibniz]
  simp

/- English proof (translation)
Use `AdicCompletion.ext_evalₐ fun n => ?_` and prove the remaining obligations. Rewrite using `[evalₐ_complDerFun I D (r := r) (AlgHom.commutes _ r), AlgHom.commutes]`. Both sides reduce to the same expression.
-/
theorem complDerFun_algebraMap (r : A') :
    complDerFun I D (algebraMap A' _ r) = algebraMap A' _ (D r) := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  rw [evalₐ_complDerFun I D (r := r) (AlgHom.commutes _ r), AlgHom.commutes]
  rfl

def complDer : Derivation k (AdicCompletion I A') (AdicCompletion I A') :=
  Derivation.mk'
    { toFun := complDerFun I D
      map_add' := fun x y => by
        refine AdicCompletion.ext_evalₐ fun n => ?_
        obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I (n + 1) x)
        obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I (n + 1) y)
        rw [evalₐ_complDerFun I D (r := r + t) (by rw [map_add, map_add, hr, ht]), map_add,
          map_add, map_add, evalₐ_complDerFun I D hr.symm, evalₐ_complDerFun I D ht.symm]
      map_smul' := fun c x => by
        have h : algebraMap k (AdicCompletion I A') c = algebraMap A' _ (algebraMap k A' c) := rfl
        rw [Algebra.smul_def, complDerFun_mul, RingHom.id_apply, Algebra.smul_def, h,
          complDerFun_algebraMap, D.map_algebraMap, map_zero, mul_zero, add_zero] }
    (complDerFun_mul I D)

/- English proof (translation)
The claim follows from `evalₐ_complDerFun I D h`.
-/
theorem evalₐ_complDer {x : AdicCompletion I A'} {n : ℕ} {r : A'}
    (h : AdicCompletion.evalₐ I (n + 1) x = Ideal.Quotient.mk _ r) :
    AdicCompletion.evalₐ I n (complDer I D x) = Ideal.Quotient.mk _ (D r) :=
  evalₐ_complDerFun I D h

/- English proof (translation)
The claim follows from `complDerFun_algebraMap I D r`.
-/
theorem complDer_algebraMap (r : A') :
    complDer I D (algebraMap A' _ r) = algebraMap A' _ (D r) := complDerFun_algebraMap I D r

def dualHom (s : A') : A' →+* TrivSqZeroExt (Localization.Away s) (Localization.Away s) where
  toFun r := TrivSqZeroExt.inl (algebraMap A' _ r) + TrivSqZeroExt.inr (algebraMap A' _ (D r))
  map_one' := by ext <;> simp
  map_mul' x y := by
    ext
    · simp
    · simp [D.leibniz, mul_comm, -DualNumber.inr_eq_smul_eps]
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp [-DualNumber.inr_eq_smul_eps]

/- English proof (translation)
The claim follows from `TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (by simpa [dualHom] using IsLocalization.Away.algebraMap_isUnit (S := Localization.Away s) s)`.
-/
theorem isUnit_dualHom (s : A') : IsUnit (dualHom D s s) :=
  TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (by
    simpa [dualHom] using IsLocalization.Away.algebraMap_isUnit (S := Localization.Away s) s)

def dualLift (s : A') :
    Localization.Away s →+* TrivSqZeroExt (Localization.Away s) (Localization.Away s) :=
  IsLocalization.Away.lift s (isUnit_dualHom D s)

/- English proof (translation)
Establish `: (TrivSqZeroExt.fstHom (Localization.Away s) _ _).toRingHom.comp (dualLift D s) = RingHom.id _`. Use `IsLocalization.ringHom_ext (Submonoid.powers s) (RingHom.ext fun r => ?_)` and prove the remaining obligations. Simplify using `[dualLift, dualHom]`. Conclude with `congr($this x)`.
-/
theorem fst_dualLift (s : A') (x : Localization.Away s) : (dualLift D s x).fst = x := by
  have : (TrivSqZeroExt.fstHom (Localization.Away s) _ _).toRingHom.comp (dualLift D s) = RingHom.id _ := by
    refine IsLocalization.ringHom_ext (Submonoid.powers s) (RingHom.ext fun r => ?_)
    simp [dualLift, dualHom]
  exact congr($this x)

/- English proof (translation)
Rewrite using `[map_mul, TrivSqZeroExt.snd_mul, fst_dualLift, fst_dualLift]`. Simplify using `[mul_comm]`.
-/
theorem snd_dualLift_mul (s : A') (x y : Localization.Away s) :
    (dualLift D s (x * y)).snd = x * (dualLift D s y).snd + y * (dualLift D s x).snd := by
  rw [map_mul, TrivSqZeroExt.snd_mul, fst_dualLift, fst_dualLift]
  simp [mul_comm]

/- English proof (translation)
Simplify using `[dualLift, dualHom, -DualNumber.inr_eq_smul_eps]`.
-/
theorem snd_dualLift_algebraMap (s r : A') :
    (dualLift D s (algebraMap A' _ r)).snd = algebraMap A' _ (D r) := by
  simp [dualLift, dualHom, -DualNumber.inr_eq_smul_eps]

def awayDer (s : A') : Derivation k (Localization.Away s) (Localization.Away s) :=
  Derivation.mk'
    { toFun := fun x => (dualLift D s x).snd
      map_add' := fun x y => by rw [map_add, TrivSqZeroExt.snd_add]
      map_smul' := fun c x => by
        rw [Algebra.smul_def, snd_dualLift_mul, RingHom.id_apply, Algebra.smul_def,
          IsScalarTower.algebraMap_apply k A' (Localization.Away s), snd_dualLift_algebraMap,
          D.map_algebraMap, map_zero, mul_zero, add_zero] }
    (snd_dualLift_mul D s)

/- English proof (translation)
The claim follows from `snd_dualLift_algebraMap D s r`.
-/
theorem awayDer_algebraMap (s r : A') :
    awayDer D s (algebraMap A' _ r) = algebraMap A' _ (D r) := snd_dualLift_algebraMap D s r

end General

section Division

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] (e : ℕ) [NeZero e]

/- English proof (translation)
Establish `h2 : (((l : A O K) : K⟦X⟧)) = C (l : K)` using `by simp`. Establish `hl : 0 < ‖(l : K)‖` using `norm_pos_iff.2 (l_ne_zero l)`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨m, hm⟩`. Use `⟨(‖(l : K)‖ ^ m)⁻¹, fun n => ?_⟩` and prove the remaining obligations.

Use `hm n` as an intermediate fact. Rewrite `this` using `[h2, ← map_pow, coeff_C_mul, norm_mul, norm_pow]`. Rewrite using `[← one_div, le_div_iff₀ (pow_pos hl m), mul_comm]`. Conclude with `this`. Introduce and unpack `⟨b, hb⟩`.

Establish `h` using `(tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (norm_l_lt_one (K := K) l)).mul_const b`. Rewrite `h` using `[zero_mul]`. Take `⟨m, hm⟩` from `(h.eventually (gt_mem_nhds zero_lt_one)).exists`. Use `⟨m, fun n => ?_⟩` and prove the remaining obligations. Rewrite using `[h2, ← map_pow, coeff_C_mul, norm_mul, norm_pow]`.

Conclude with `(mul_le_mul_of_nonneg_left (hb n) (pow_pos hl m).le).trans hm.le`.
-/
theorem mem_invL_A_iff {f : K⟦X⟧} : f ∈ invL l (A O K) ↔ ∃ b : ℝ, ∀ n, ‖coeff n f‖ ≤ b := by
  have h2 : (((l : A O K) : K⟦X⟧)) = C (l : K) := by simp
  have hl : 0 < ‖(l : K)‖ := norm_pos_iff.2 (l_ne_zero l)
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨(‖(l : K)‖ ^ m)⁻¹, fun n => ?_⟩
    have := hm n
    rw [h2, ← map_pow, coeff_C_mul, norm_mul, norm_pow] at this
    rw [← one_div, le_div_iff₀ (pow_pos hl m), mul_comm]
    exact this
  · rintro ⟨b, hb⟩
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _)
      (norm_l_lt_one (K := K) l)).mul_const b
    rw [zero_mul] at h
    obtain ⟨m, hm⟩ := (h.eventually (gt_mem_nhds zero_lt_one)).exists
    refine ⟨m, fun n => ?_⟩
    rw [h2, ← map_pow, coeff_C_mul, norm_mul, norm_pow]
    exact (mul_le_mul_of_nonneg_left (hb n) (pow_pos hl m).le).trans hm.le

variable (O K) in

abbrev Rpi : Subalgebra O K⟦X⟧ := R O K l (1 / e)

/- English proof (translation)
The claim follows from `A_le_R l (by have := NeZero.pos e; positivity)`.
-/
theorem A_le_Rpi : A O K ≤ Rpi O K l e :=
  A_le_R l (by have := NeZero.pos e; positivity)

/- English proof (translation)
The claim follows from `invL_le l (A_le_Rpi l e)`.
-/
theorem invL_A_le_Rpi : invL l (A O K) ≤ Rpi O K l e := invL_le l (A_le_Rpi l e)

/- English proof (translation)
The claim follows from `invL_le l (S_le_R l e)`.
-/
theorem invL_S_le_Rpi : invL l (S O K e) ≤ Rpi O K l e := invL_le l (S_le_R l e)

omit [IsUltrametricDist K] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] in
/- English proof (translation)
Rewrite using `[E, add_mul, map_add, coeff_X_pow_mul, ← map_natCast (C : K →+* K⟦X⟧), coeff_C_mul]`.
-/
theorem coeff_E_mul (g : K⟦X⟧) (n : ℕ) :
    coeff (n + e) (E K l e * g) = coeff n g + l * coeff (n + e) g := by
  rw [E, add_mul, map_add, coeff_X_pow_mul, ← map_natCast (C : K →+* K⟦X⟧), coeff_C_mul]

/- English proof (translation)
The claim follows from `tendsto_atTop_mono (fun j => (Nat.le_mul_of_pos_right j (NeZero.pos e)).trans (Nat.le_add_left _ _)) tendsto_id`.
-/
theorem tendsto_add_mul (n : ℕ) : Tendsto (fun j : ℕ => n + j * e) atTop atTop :=
  tendsto_atTop_mono (fun j => (Nat.le_mul_of_pos_right j (NeZero.pos e)).trans
    (Nat.le_add_left _ _)) tendsto_id

/- English proof (translation)
Rewrite using `[norm_mul, norm_pow, norm_neg, ← rad_pow l e, ← pow_mul, pow_add, mul_comm e j]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem norm_term_eq (f : K⟦X⟧) (n j : ℕ) : ‖coeff (n + j * e) f * (-(l : K)) ^ j‖ * rad l (1 / e) ^ n =
    ‖coeff (n + j * e) f‖ * rad l (1 / e) ^ (n + j * e) := by
  rw [norm_mul, norm_pow, norm_neg, ← rad_pow l e, ← pow_mul, pow_add, mul_comm e j]
  ring

/- English proof (translation)
Use extensionality with `n`. Establish `key : ∀ j, coeff n g = coeff (n + j * e) g * (-(l : K)) ^ j` using `fun j => by`. Proceed by induction on `j with`. Consider the case `zero => simp`. Consider the case `succ j ih`.

Use `h (n + j * e)` as an intermediate fact. Rewrite `this` using `[coeff_E_mul]`. Rewrite using `[ih, show n + (j + 1) * e = n + j * e + e by ring]`. Take the linear combination `(-(l : K)) ^ j * this`. Establish `h1` using `(mem_R.1 hg).comp (tendsto_add_mul e n)`.

Establish `h2 : ‖coeff n g‖ * rad l (1 / e) ^ n = 0`. Use `tendsto_nhds_unique tendsto_const_nhds (h1.congr fun j => ?_)` and prove the remaining obligations. Simplify using `only [Function.comp]`. Rewrite using `[← norm_term_eq (K := K) l e, ← key]`. Simplify `h2` using `[(rad_pos l _).ne']`.
-/
theorem eq_zero_of_E_mul {g : K⟦X⟧} (hg : g ∈ Rpi O K l e)
    (h : ∀ n, coeff (n + e) (E K l e * g) = 0) : g = 0 := by
  ext n
  have key : ∀ j, coeff n g = coeff (n + j * e) g * (-(l : K)) ^ j := fun j => by
    induction j with
    | zero => simp
    | succ j ih =>
      have := h (n + j * e)
      rw [coeff_E_mul] at this
      rw [ih, show n + (j + 1) * e = n + j * e + e by ring]
      linear_combination (-(l : K)) ^ j * this
  have h1 := (mem_R.1 hg).comp (tendsto_add_mul e n)
  have h2 : ‖coeff n g‖ * rad l (1 / e) ^ n = 0 := by
    refine tendsto_nhds_unique tendsto_const_nhds (h1.congr fun j => ?_)
    simp only [Function.comp]
    rw [← norm_term_eq (K := K) l e, ← key]
  simpa [(rad_pos l _).ne'] using h2

def tail (f : K⟦X⟧) (n : ℕ) : K := ∑' j : ℕ, coeff (n + j * e) f * (-(l : K)) ^ j

def quotE (f : K⟦X⟧) : K⟦X⟧ := PowerSeries.mk fun n => tail l e f (n + e)

variable [CompleteSpace K]

/- English proof (translation)
Establish `hs : Summable fun j : ℕ => coeff (n + j * e) f * (-(l : K)) ^ j`. Use `NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_` and prove the remaining obligations. Rewrite using `[Nat.cofinite_eq_atTop, tendsto_zero_iff_norm_tendsto_zero]`. Establish `h1` using `((mem_R.1 hf).comp (tendsto_add_mul e n)).mul_const (rad l (1 / e) ^ n)⁻¹`. Rewrite `h1` using `[zero_mul]`.

Use `h1.congr fun j => ?_` and prove the remaining obligations. Simplify using `only [Function.comp]`. Rewrite using `[← norm_term_eq (K := K) l e, mul_inv_cancel_right₀ (pow_pos (rad_pos l _) n).ne']`. Rewrite using `[tail, hs.tsum_eq_zero_add, tail, ← tsum_mul_left, sub_eq_add_neg, ← tsum_neg]`. Use `congr 1`.

Simplify using the standard rewrite rules. Use `tsum_congr fun j => ?_` and prove the remaining obligations. Rewrite using `[show n + (j + 1) * e = n + e + j * e by ring]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem tail_rec {f : K⟦X⟧} (hf : f ∈ Rpi O K l e) (n : ℕ) :
    tail l e f n = coeff n f - l * tail l e f (n + e) := by
  have hs : Summable fun j : ℕ => coeff (n + j * e) f * (-(l : K)) ^ j := by
    refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
    rw [Nat.cofinite_eq_atTop, tendsto_zero_iff_norm_tendsto_zero]
    have h1 := ((mem_R.1 hf).comp (tendsto_add_mul e n)).mul_const (rad l (1 / e) ^ n)⁻¹
    rw [zero_mul] at h1
    refine h1.congr fun j => ?_
    simp only [Function.comp]
    rw [← norm_term_eq (K := K) l e, mul_inv_cancel_right₀ (pow_pos (rad_pos l _) n).ne']
  rw [tail, hs.tsum_eq_zero_add, tail, ← tsum_mul_left, sub_eq_add_neg, ← tsum_neg]
  congr 1
  · simp
  · refine tsum_congr fun j => ?_
    rw [show n + (j + 1) * e = n + e + j * e by ring]
    ring

/- English proof (translation)
Rewrite using `[map_sub, coeff_E_mul, quotE, coeff_mk, coeff_mk, tail_rec l e hf (n + e)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem coeff_sub_E_mul_quotE {f : K⟦X⟧} (hf : f ∈ Rpi O K l e) (n : ℕ) :
    coeff (n + e) (f - E K l e * quotE l e f) = 0 := by
  rw [map_sub, coeff_E_mul, quotE, coeff_mk, coeff_mk, tail_rec l e hf (n + e)]
  ring

omit [CompleteSpace K] in
/- English proof (translation)
Establish `hρ` using `rad_pos l (1 / e)`. Establish `h1 : Tendsto (fun n => ‖tail l e f n‖ * rad l (1 / e) ^ n) atTop (𝓝 0)`. Use `mem_R.1 hf` as an intermediate fact. Rewrite `this`, the goal using `[Metric.tendsto_atTop]`. Introduce `ε hε`.

Take `⟨N, hN⟩` from `this (ε / 2) (half_pos hε)`. Use `⟨N, fun n hn => ?_⟩` and prove the remaining obligations. Rewrite using `[Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]`. Use `lt_of_le_of_lt ?_ (half_lt_self hε)` and prove the remaining obligations. Rewrite using `[← le_div_iff₀ (pow_pos hρ n)]`.

Use `IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) fun j => ?_` and prove the remaining obligations. Rewrite using `[le_div_iff₀ (pow_pos hρ n), norm_term_eq]`. Use `hN (n + j * e) (by omega)` as an intermediate fact. Rewrite `this` using `[Real.dist_eq, sub_zero]`. Conclude with `(le_abs_self _).trans this.le`.

Establish `h2` using `(h1.comp (tendsto_add_atTop_nat e)).mul_const (rad l (1 / e) ^ e)⁻¹`. Rewrite `h2` using `[zero_mul]`. Use `mem_R.2 (h2.congr fun n => ?_)` and prove the remaining obligations. Simplify using `only [Function.comp, quotE, coeff_mk]`. Rewrite using `[pow_add]`.

Clear the denominators using the available nonvanishing facts.
-/
theorem quotE_mem_Rpi {f : K⟦X⟧} (hf : f ∈ Rpi O K l e) : quotE l e f ∈ Rpi O K l e := by
  have hρ := rad_pos l (1 / e)
  have h1 : Tendsto (fun n => ‖tail l e f n‖ * rad l (1 / e) ^ n) atTop (𝓝 0) := by
    have := mem_R.1 hf
    rw [Metric.tendsto_atTop] at this ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := this (ε / 2) (half_pos hε)
    refine ⟨N, fun n hn => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
    refine lt_of_le_of_lt ?_ (half_lt_self hε)
    rw [← le_div_iff₀ (pow_pos hρ n)]
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) fun j => ?_
    rw [le_div_iff₀ (pow_pos hρ n), norm_term_eq]
    have := hN (n + j * e) (by omega)
    rw [Real.dist_eq, sub_zero] at this
    exact (le_abs_self _).trans this.le
  have h2 := (h1.comp (tendsto_add_atTop_nat e)).mul_const (rad l (1 / e) ^ e)⁻¹
  rw [zero_mul] at h2
  refine mem_R.2 (h2.congr fun n => ?_)
  simp only [Function.comp, quotE, coeff_mk]
  rw [pow_add]
  field_simp

omit [CompleteSpace K] [NeZero e] in
/- English proof (translation)
Take `⟨b, hb⟩` from `(mem_invL_A_iff l).1 hf`. Establish `hb0 : 0 ≤ b` using `(norm_nonneg _).trans (hb 0)`. Use `(mem_invL_A_iff l).2 ⟨b, fun n => ?_⟩` and prove the remaining obligations. Rewrite using `[quotE, coeff_mk]`. Use `IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hb0 fun j => ?_` and prove the remaining obligations.

Rewrite using `[norm_mul, norm_pow, norm_neg]`. Conclude with `(mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) (norm_l_lt_one l).le)).trans (hb _)`.
-/
theorem quotE_mem_invL_A {f : K⟦X⟧} (hf : f ∈ invL l (A O K)) : quotE l e f ∈ invL l (A O K) := by
  obtain ⟨b, hb⟩ := (mem_invL_A_iff l).1 hf
  have hb0 : 0 ≤ b := (norm_nonneg _).trans (hb 0)
  refine (mem_invL_A_iff l).2 ⟨b, fun n => ?_⟩
  rw [quotE, coeff_mk]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hb0 fun j => ?_
  rw [norm_mul, norm_pow, norm_neg]
  exact (mul_le_of_le_one_right (norm_nonneg _)
    (pow_le_one₀ (norm_nonneg _) (norm_l_lt_one l).le)).trans (hb _)

/- English proof (translation)
Establish `: Tendsto (fun n => ‖coeff n (f - E K l e * quotE l e f)‖) atTop (𝓝 0)`. Use `tendsto_const_nhds.congr' ?_` and prove the remaining obligations. Use `filter_upwards [eventually_ge_atTop e] with n hn`. Take `⟨m, rfl⟩` from `Nat.exists_eq_add_of_le' hn`. Rewrite using `[coeff_sub_E_mul_quotE l e hf, norm_zero]`.

Take `⟨b, hb⟩` from `this.bddAbove_range`. Conclude with `(mem_invL_A_iff l).2 ⟨b, fun n => hb ⟨n, rfl⟩⟩`.
-/
theorem sub_E_mul_quotE_mem {f : K⟦X⟧} (hf : f ∈ Rpi O K l e) :
    f - E K l e * quotE l e f ∈ invL l (A O K) := by
  have : Tendsto (fun n => ‖coeff n (f - E K l e * quotE l e f)‖) atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop e] with n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
    rw [coeff_sub_E_mul_quotE l e hf, norm_zero]
  obtain ⟨b, hb⟩ := this.bddAbove_range
  exact (mem_invL_A_iff l).2 ⟨b, fun n => hb ⟨n, rfl⟩⟩

/- English proof (translation)
Establish `hR` using `invL_A_le_Rpi l e hE`. Establish `: h - quotE l e (E K l e * h) = 0` using `eq_zero_of_E_mul l e (Subalgebra.sub_mem _ hh (quotE_mem_Rpi l e hR)) fun n => by`. Rewrite using `[mul_sub]`. Conclude with `coeff_sub_E_mul_quotE l e hR n`. Rewrite using `[sub_eq_zero.1 this]`.

Conclude with `quotE_mem_invL_A l e hE`.
-/
theorem mem_invL_A_of_E_mul {h : K⟦X⟧} (hh : h ∈ Rpi O K l e)
    (hE : E K l e * h ∈ invL l (A O K)) : h ∈ invL l (A O K) := by
  have hR := invL_A_le_Rpi l e hE
  have : h - quotE l e (E K l e * h) = 0 :=
    eq_zero_of_E_mul l e (Subalgebra.sub_mem _ hh (quotE_mem_Rpi l e hR)) fun n => by
      rw [mul_sub]; exact coeff_sub_E_mul_quotE l e hR n
  rw [sub_eq_zero.1 this]
  exact quotE_mem_invL_A l e hE

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simpa using hE`. Consider the case `succ m ih`. Use `ih (mem_invL_A_of_E_mul l e (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (E_mem l e _) m) hh) ?_)` and prove the remaining obligations. Rewrite using `[← mul_assoc, ← pow_succ']` and apply the resulting hypothesis.
-/
theorem mem_invL_A_of_E_pow_mul (m : ℕ) {h : K⟦X⟧} (hh : h ∈ Rpi O K l e)
    (hE : E K l e ^ m * h ∈ invL l (A O K)) : h ∈ invL l (A O K) := by
  induction m with
  | zero => simpa using hE
  | succ m ih =>
    refine ih (mem_invL_A_of_E_mul l e
      (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (E_mem l e _) m) hh) ?_)
    rwa [← mul_assoc, ← pow_succ']

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => exact ⟨0, zero_mem _, f, hf, by simp⟩`. Consider the case `succ m ih`. Take `⟨g, hg, h, hh, rfl⟩` from `ih`. Conclude with `⟨g + E K l e ^ m * (h - E K l e * quotE l e h), add_mem hg (mul_mem (pow_mem (E_mem l e _) m) (sub_E_mul_quotE_mem l e hh)), quotE l e h, quotE_mem_Rpi l e hh, by ring⟩`.
-/
theorem exists_div_E_pow (m : ℕ) {f : K⟦X⟧} (hf : f ∈ Rpi O K l e) :
    ∃ g ∈ invL l (A O K), ∃ h ∈ Rpi O K l e, f = g + E K l e ^ m * h := by
  induction m with
  | zero => exact ⟨0, zero_mem _, f, hf, by simp⟩
  | succ m ih =>
    obtain ⟨g, hg, h, hh, rfl⟩ := ih
    exact ⟨g + E K l e ^ m * (h - E K l e * quotE l e h),
      add_mem hg (mul_mem (pow_mem (E_mem l e _) m) (sub_E_mul_quotE_mem l e hh)),
      quotE l e h, quotE_mem_Rpi l e hh, by ring⟩

variable (O K) in

/- English proof (translation)
Take `⟨g, hg, h, hh, hx⟩` from `exists_div_E_pow l e m x.2`. Conclude with `⟨⟨g, hg⟩, ⟨h, hh⟩, Subtype.ext hx⟩`. Use `dvd m g h hx := by`. Establish `hx' : (g : K⟦X⟧) = E K l e ^ m * h` using `congrArg Subtype.val hx`. Conclude with `⟨⟨h, mem_invL_A_of_E_pow_mul l e m h.2 (hx' ▸ g.2)⟩, Subtype.ext hx'⟩`.
-/
theorem sameJets : SameJets
    (Subalgebra.inclusion (invL_A_le_Rpi (O := O) (K := K) l e)).toRingHom
    (EIn l e (invL l (A O K))) where
  div m x := by
    obtain ⟨g, hg, h, hh, hx⟩ := exists_div_E_pow l e m x.2
    exact ⟨⟨g, hg⟩, ⟨h, hh⟩, Subtype.ext hx⟩
  dvd m g h hx := by
    have hx' : (g : K⟦X⟧) = E K l e ^ m * h := congrArg Subtype.val hx
    exact ⟨⟨h, mem_invL_A_of_E_pow_mul l e m h.2 (hx' ▸ g.2)⟩, Subtype.ext hx'⟩

end Division

section Hat

variable (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l e : ℕ)

abbrev idE : Ideal (invL l (A O K)) := Ideal.span {EIn l e (invL l (A O K))}

abbrev Ahat : Type := AdicCompletion (idE O K l e) (invL l (A O K))

abbrev ofAl : invL l (A O K) →+* Ahat O K l e := algebraMap _ _

def ofA : A O K →+* Ahat O K l e := (ofAl O K l e).comp (algebraMap (A O K) (invL l (A O K)))

def Ehat : Ahat O K l e := ofAl O K l e (EIn l e _)

def uhat : Ahat O K l e := ofAl O K l e (uIn _)

abbrev AhatE : Type := Localization.Away (Ehat O K l e)

variable [Fact l.Prime] [NormedAlgebra ℚ_[l] K]

def derAl : Derivation K (invL l (A O K)) (invL l (A O K)) :=
  Derivation.mk'
    { toFun := fun f => ⟨PowerSeries.derivative K f,
        derivative_mem_away _ (fun _ => derivative_mem_A) f.2⟩
      map_add' := fun f g => Subtype.ext (map_add (PowerSeries.derivative K) _ _)
      map_smul' := fun c f => Subtype.ext (by
        change PowerSeries.derivative K (C c * (f : K⟦X⟧)) = C c * PowerSeries.derivative K f
        simp) }
    fun f g => Subtype.ext ((PowerSeries.derivative K).leibniz f g)

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem coe_derAl (f : invL l (A O K)) :
    (derAl O K l f : K⟦X⟧) = PowerSeries.derivative K f := rfl

def dHat : Derivation K (Ahat O K l e) (Ahat O K l e) := complDer _ (derAl O K l)

def dHatE : Derivation K (AhatE O K l e) (AhatE O K l e) := awayDer (dHat O K l e) _

def NHat : Derivation K (Ahat O K l e) (Ahat O K l e) := uhat O K l e • dHat O K l e

def NHatE : Derivation K (AhatE O K l e) (AhatE O K l e) :=
  algebraMap (Ahat O K l e) (AhatE O K l e) (uhat O K l e) • dHatE O K l e

/- English proof (translation)
The claim follows from `awayDer_algebraMap _ _ x`.
-/
theorem dHatE_algebraMap (x : Ahat O K l e) :
    dHatE O K l e (algebraMap _ _ x) = algebraMap _ _ (dHat O K l e x) := awayDer_algebraMap _ _ x

variable [NeZero e] [CompleteSpace K]

def toHat : Rpi O K l e →+* Ahat O K l e := (sameJets O K l e).toCompl

variable {O K} in

/- English proof (translation)
Rewrite using `[toHat, SameJets.evalₐ_toCompl_eq_iff]`. Conclude with `⟨fun ⟨h, hh⟩ => ⟨h, h.2, congrArg Subtype.val hh⟩, fun ⟨h, hh, H⟩ => ⟨⟨h, hh⟩, Subtype.ext H⟩⟩`.
-/
theorem evalₐ_toHat_eq_iff (m : ℕ) (f : Rpi O K l e) (g : invL l (A O K)) :
    AdicCompletion.evalₐ _ m (toHat O K l e f) = Ideal.Quotient.mk _ g ↔
      ∃ h ∈ Rpi O K l e, (f : K⟦X⟧) - g = E K l e ^ m * h := by
  rw [toHat, SameJets.evalₐ_toCompl_eq_iff]
  exact ⟨fun ⟨h, hh⟩ => ⟨h, h.2, congrArg Subtype.val hh⟩,
    fun ⟨h, hh, H⟩ => ⟨⟨h, hh⟩, Subtype.ext H⟩⟩

variable {O K} in
/- English proof (translation)
Rewrite using `[← (sameJets O K l e).toCompl_ι g]`. Conclude with `congrArg _ (Subtype.ext h)`.
-/
theorem toHat_eq_ofAl {f : Rpi O K l e} {g : invL l (A O K)} (h : (f : K⟦X⟧) = g) :
    toHat O K l e f = ofAl O K l e g := by
  rw [← (sameJets O K l e).toCompl_ι g]
  exact congrArg _ (Subtype.ext h)

variable {O K} in

def toHatOf {B : Subalgebra O K⟦X⟧} (h : B ≤ Rpi O K l e) : B →+* Ahat O K l e :=
  (toHat O K l e).comp (Subalgebra.inclusion h).toRingHom

def toHatS : invL l (S O K e) →+* Ahat O K l e := toHatOf l e (invL_S_le_Rpi l e)

variable {e} in

def toHatR {k : ℝ} (hk : k ≤ 1 / e) : R O K l k →+* Ahat O K l e := toHatOf l e (R_mono l hk)

abbrev RpiE : Subalgebra O K⟦X⟧ := invE l e (Rpi O K l e)

/- English proof (translation)
The claim follows from `toHat_eq_ofAl l e rfl`.
-/
theorem toHat_E : toHat O K l e (EIn l e _) = Ehat O K l e := toHat_eq_ofAl l e rfl

def toHatE : RpiE O K l e →+* AhatE O K l e :=
  IsLocalization.Away.lift (EIn l e (Rpi O K l e))
    (g := (algebraMap (Ahat O K l e) (AhatE O K l e)).comp (toHat O K l e))
    (by rw [RingHom.comp_apply, toHat_E]; exact IsLocalization.Away.algebraMap_isUnit _)

variable {O K} in
/- English proof (translation)
Establish `: f = algebraMap (Rpi O K l e) _ g` using `Subtype.ext h`. Rewrite using `[this, toHatE, IsLocalization.Away.lift_eq]`. Both sides reduce to the same expression.
-/
theorem toHatE_eq {f : RpiE O K l e} {g : Rpi O K l e} (h : (f : K⟦X⟧) = g) :
    toHatE O K l e f = algebraMap _ _ (toHat O K l e g) := by
  have : f = algebraMap (Rpi O K l e) _ g := Subtype.ext h
  rw [this, toHatE, IsLocalization.Away.lift_eq]
  rfl

variable {O K} in
/- English proof (translation)
The claim follows from `away_mono h rfl`.
-/
theorem invE_le_RpiE {B : Subalgebra O K⟦X⟧} [HasU B] (h : B ≤ Rpi O K l e) :
    invE l e B ≤ RpiE O K l e := away_mono h rfl

end Hat

end GlobalTheory.BK
