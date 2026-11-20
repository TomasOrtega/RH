import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.NotIsGenericDetRepTwo

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.LFun

namespace GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

namespace CuspSub

variable {π π' : CuspSub E a}

/- English proof (translation)
Take `⟨T, hT⟩` from `h`. Establish `hf : ∀ g y, T.toLinearMap (π.locRep w g y) = π'.locRep w g (T.toLinearMap y)` using `fun g y => hT (.fin _) y`. Prove the components needed by the constructor for the conclusion. Take `⟨x, hx⟩` from `hB.exists_vec`. Establish `h1` using `hx.map T.toLinearMap hf ((map_ne_zero_iff T T.injective).2 hx.1)`.

Conclude with `(Submodule.ne_bot_iff _).2 ⟨_, h1.2.1, h1.1⟩`. Introduce `y hy h0`. Take `⟨x, rfl⟩` from `T.surjective y`. Use `(hB.2 x (GlobalTheory.LGrp.mem_fixed.2 fun k hk => T.injective ?_) fun e => h0 (by rw [e, map_zero])).map T.toLinearMap hf h0` and prove the remaining obligations. Conclude with `(hf k x).trans (GlobalTheory.LGrp.mem_fixed.1 hy k hk)`.
-/
theorem Iso.hasSatGL (h : Iso π π') {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ}
    (hB : HasSatGL w (π.locRep w) B) : HasSatGL w (π'.locRep w) B := by
  obtain ⟨T, hT⟩ := h
  have hf : ∀ g y, T.toLinearMap (π.locRep w g y) = π'.locRep w g (T.toLinearMap y) := fun g y => hT (.fin _) y
  constructor
  · obtain ⟨x, hx⟩ := hB.exists_vec
    have h1 := hx.map T.toLinearMap hf ((map_ne_zero_iff T T.injective).2 hx.1)
    exact (Submodule.ne_bot_iff _).2 ⟨_, h1.2.1, h1.1⟩
  · intro y hy h0
    obtain ⟨x, rfl⟩ := T.surjective y
    refine (hB.2 x (GlobalTheory.LGrp.mem_fixed.2 fun k hk => T.injective ?_) fun e => h0 (by rw [e, map_zero])).map
      T.toLinearMap hf h0
    exact (hf k x).trans (GlobalTheory.LGrp.mem_fixed.1 hy k hk)

variable (π) in

def HasCentChar (ω : HChar E) : Prop := GlobalTheory.SmGL.HasCentralChar π.finPart (ω.1.comp (finId E))

/- English proof (translation)
Take `⟨T, hT⟩` from `h`. Introduce `z y`. Take `⟨x, rfl⟩` from `T.surjective y`. Conclude with `((hT (.fin _) x).symm.trans (congrArg T (hω z x))).trans (map_smul T _ x)`.
-/
theorem Iso.hasCentChar (h : Iso π π') {ω : HChar E} (hω : π.HasCentChar ω) : π'.HasCentChar ω := by
  obtain ⟨T, hT⟩ := h
  intro z y
  obtain ⟨x, rfl⟩ := T.surjective y
  exact ((hT (.fin _) x).symm.trans (congrArg T (hω z x))).trans (map_smul T _ x)

/- English proof (translation)
Introduce `z y`. Take `⟨x, rfl⟩` from `(π.toTwist χ).surjective y`. Use `(π.op_toTwist χ (.fin _) x).trans ?_` and prove the remaining obligations. Establish `h1 : π.op (.fin (GeneralLinearGroup.scalar (Fin a) z)) x = _` using `hω z x`. Establish `h2 : opMul χ (.fin (GeneralLinearGroup.scalar (Fin a) z) : Op E a) = χ.1 (finId E z) ^ a`.

Simplify using `only [opMul, chiDet, MonoidHom.comp_apply, det_finGL]`. Rewrite using `[← map_pow, ← map_pow]`. Use `congr 2`. Use extensionality with `: 1`. Simplify using the standard rewrite rules.

Rewrite using `[h1, h2, opAdd, zero_smul, add_zero, smul_smul, map_smul, mul_comm]`. Simplify using the standard rewrite rules.
-/
theorem HasCentChar.twist {ω : HChar E} (hω : π.HasCentChar ω) (χ : HChar E) :
    (π.twist χ).HasCentChar (ω * χ ^ a) := by
  intro z y
  obtain ⟨x, rfl⟩ := (π.toTwist χ).surjective y
  refine (π.op_toTwist χ (.fin _) x).trans ?_
  have h1 : π.op (.fin (GeneralLinearGroup.scalar (Fin a) z)) x = _ := hω z x
  have h2 : opMul χ (.fin (GeneralLinearGroup.scalar (Fin a) z) : Op E a) = χ.1 (finId E z) ^ a := by
    simp only [opMul, chiDet, MonoidHom.comp_apply, det_finGL]
    rw [← map_pow, ← map_pow]
    congr 2
    ext : 1
    simp
  rw [h1, h2, opAdd, zero_smul, add_zero, smul_smul, map_smul, mul_comm]
  simp

end CuspSub

namespace CG

def HasSat (π : CG E a) (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ) : Prop :=
  Quotient.liftOn π (fun π => HasSatGL w (π.locRep w) B) fun _ _ h =>
    propext ⟨CuspSub.Iso.hasSatGL h, CuspSub.Iso.hasSatGL (Setoid.symm h)⟩

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
@[simp] theorem hasSat_mk (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ) :
    (mk π).HasSat w B ↔ HasSatGL w (π.locRep w) B := Iff.rfl

/- English proof (translation)
Proceed by induction on `π using Quotient.inductionOn`. Conclude with `HasSatGL.unique h h'`.
-/
theorem HasSat.unique {π : CG E a} {w : HeightOneSpectrum (𝓞 E)} {B B' : Multiset ℂˣ} (h : π.HasSat w B)
    (h' : π.HasSat w B') : B = B' := by
  induction π using Quotient.inductionOn
  exact HasSatGL.unique h h'

/- English proof (translation)
Proceed by induction on `π using Quotient.inductionOn`. Conclude with `HasSatGL.card h`.
-/
theorem HasSat.card {π : CG E a} {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ} (h : π.HasSat w B) :
    B.card = a := by
  induction π using Quotient.inductionOn
  exact HasSatGL.card h

def HasCentChar (π : CG E a) (ω : HChar E) : Prop :=
  Quotient.liftOn π (·.HasCentChar ω) fun _ _ h =>
    propext ⟨CuspSub.Iso.hasCentChar h, CuspSub.Iso.hasCentChar (Setoid.symm h)⟩

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
@[simp] theorem hasCentChar_mk (π : CuspSub E a) (ω : HChar E) : (mk π).HasCentChar ω ↔ π.HasCentChar ω := Iff.rfl

/- English proof (translation)
Proceed by induction on `π using Quotient.inductionOn`. Conclude with `CuspSub.HasCentChar.twist h χ`.
-/
theorem HasCentChar.twist {π : CG E a} {ω : HChar E} (h : π.HasCentChar ω) (χ : HChar E) :
    (π.twist χ).HasCentChar (ω * χ ^ a) := by
  induction π using Quotient.inductionOn
  exact CuspSub.HasCentChar.twist h χ

def IsUnitary (π : CG E a) : Prop := ∃ ω : HChar E, ω.IsUnitary ∧ π.HasCentChar ω

/- English proof (translation)
Proceed by induction on `π using Quotient.inductionOn with | _ π => ?_`. Use `Submodule.nontrivial_iff_ne_bot.2 π.ne_bot` as an intermediate fact. Take `⟨x, hx⟩` from `exists_ne (0 : π.V)`. Set `z` to `GeneralLinearGroup.det (locGL E 1 w (oneByOne (atFin w (unif w))))`. Establish `e : ω.1 (finId E z) = ω'.1 (finId E z)` using `Units.ext (smul_left_injective ℂ hx ((h z x).symm.trans (h' z x)))`.

Rewrite `e` using `[finId_det_locGL, det_oneByOne]`. Then use the resulting hypothesis.
-/
theorem HasCentChar.loc_eq {π : CG E a} {ω ω' : HChar E} (h : π.HasCentChar ω) (h' : π.HasCentChar ω')
    (w : HeightOneSpectrum (𝓞 E)) : ω.val w = ω'.val w := by
  induction π using Quotient.inductionOn with | _ π => ?_
  have := Submodule.nontrivial_iff_ne_bot.2 π.ne_bot
  obtain ⟨x, hx⟩ := exists_ne (0 : π.V)
  let z := GeneralLinearGroup.det (locGL E 1 w (oneByOne (atFin w (unif w))))
  have e : ω.1 (finId E z) = ω'.1 (finId E z) := Units.ext (smul_left_injective ℂ hx ((h z x).symm.trans (h' z x)))
  rwa [finId_det_locGL, det_oneByOne] at e

/- English proof (translation)
Introduce `π π' h` and use `by simpa only [← twist_mul, mul_inv_cancel, twist_one] using congrArg (·.twist χ⁻¹) h`.
-/
theorem twist_injective (χ : HChar E) : Function.Injective fun π : CG E a => π.twist χ := fun π π' h => by
  simpa only [← twist_mul, mul_inv_cancel, twist_one] using congrArg (·.twist χ⁻¹) h

/- English proof (translation)
Take `⟨ω, hu, hω⟩` from `h`. Take `⟨ω', hu', hω'⟩` from `h'`. Take `⟨P, hP, hP0⟩` from `Ring.exists_maximal_of_not_isField (RingOfIntegers.not_isField E)`. Set `w : HeightOneSpectrum (𝓞 E)` to `⟨P, hP0.isPrime, hP⟩`. Establish `h1` using `(hω.twist ν).loc_eq (e ▸ hω'.twist ν') w`.

Establish `hp : ∀ ν : HChar E, (ν ^ a).val w = ν.val w ^ a` using `fun ν => MonoidHom.pow_apply ν.1 a _`. Rewrite `h1` using `[HChar.val_mul, HChar.val_mul, hp, hp]`. Establish `h2` using `congrArg (fun u : ℂˣ => ‖(u : ℂ)‖) h1`. Establish `hq : 1 < Ideal.absNorm w.asIdeal` using `NumberField.HeightOneSpectrum.one_lt_absNorm w`. Establish `e1 : ‖((ω.val w : ℂˣ) : ℂ)‖ = 1` using `hu _`.

Establish `e2 : ‖((ω'.val w : ℂˣ) : ℂ)‖ = 1` using `hu' _`. Simplify using `only [Units.val_mul, Units.val_pow_eq_pow_val, norm_mul, norm_pow, e1, e2, one_mul, hν.2.1 w, hν'.2.1 w, Complex.norm_natCast_cpow_of_pos (zero_lt_one.trans hq), Complex.neg_re, Complex.ofReal_re] at h2`. Establish `h3` using `(pow_left_inj₀ (by positivity) (by positivity) (by omega)).1 h2`. Conclude with `neg_injective ((Real.rpow_right_inj (by positivity) (by exact_mod_cast hq.ne')).1 h3)`.
-/
theorem exponent_unique (ha : 1 ≤ a) {π π' : CG E a} (h : π.IsUnitary) (h' : π'.IsUnitary) {ν ν' : HChar E} {s s' : ℝ}
    (hν : ν.IsAbsPow s) (hν' : ν'.IsAbsPow s') (e : π.twist ν = π'.twist ν') : s = s' := by
  obtain ⟨ω, hu, hω⟩ := h
  obtain ⟨ω', hu', hω'⟩ := h'
  obtain ⟨P, hP, hP0⟩ := Ring.exists_maximal_of_not_isField (RingOfIntegers.not_isField E)
  let w : HeightOneSpectrum (𝓞 E) := ⟨P, hP0.isPrime, hP⟩
  have h1 := (hω.twist ν).loc_eq (e ▸ hω'.twist ν') w
  have hp : ∀ ν : HChar E, (ν ^ a).val w = ν.val w ^ a := fun ν => MonoidHom.pow_apply ν.1 a _
  rw [HChar.val_mul, HChar.val_mul, hp, hp] at h1
  have h2 := congrArg (fun u : ℂˣ => ‖(u : ℂ)‖) h1
  have hq : 1 < Ideal.absNorm w.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm w
  have e1 : ‖((ω.val w : ℂˣ) : ℂ)‖ = 1 := hu _
  have e2 : ‖((ω'.val w : ℂˣ) : ℂ)‖ = 1 := hu' _
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, norm_mul, norm_pow, e1, e2, one_mul, hν.2.1 w, hν'.2.1 w,
    Complex.norm_natCast_cpow_of_pos (zero_lt_one.trans hq), Complex.neg_re, Complex.ofReal_re] at h2
  have h3 := (pow_left_inj₀ (by positivity) (by positivity) (by omega)).1 h2
  exact neg_injective ((Real.rpow_right_inj (by positivity) (by exact_mod_cast hq.ne')).1 h3)

/- English proof (translation)
Establish `h : (CuspSub.triv E (le_refl 1)).HasCentChar 1` using `fun z φ => by`. Take `⟨c, e⟩` from `Submodule.mem_span_singleton.1 φ.2`. Use `Subtype.ext ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `act (.fin _) φ.1 = ((1 : ℂˣ) : ℂ) • φ.1`. Rewrite using `[← e, map_smul, act_oneFn]`.

Simplify using `[opTriv]`. Establish `h2` using `h.twist χ`. Rewrite `h2` using `[one_mul, pow_one]`. Then use the resulting hypothesis.
-/
theorem hasCentChar_ofChar (χ : HChar E) : (ofChar χ).HasCentChar χ := by
  have h : (CuspSub.triv E (le_refl 1)).HasCentChar 1 := fun z φ => by
    obtain ⟨c, e⟩ := Submodule.mem_span_singleton.1 φ.2
    refine Subtype.ext ?_
    change act (.fin _) φ.1 = ((1 : ℂˣ) : ℂ) • φ.1
    rw [← e, map_smul, act_oneFn]
    simp [opTriv]
  have h2 := h.twist χ
  rwa [one_mul, pow_one] at h2

/- English proof (translation)
Assemble the required witnesses or components as `⟨χ, h, hasCentChar_ofChar χ⟩`.
-/
theorem isUnitary_ofChar {χ : HChar E} (h : χ.IsUnitary) : (ofChar χ).IsUnitary := ⟨χ, h, hasCentChar_ofChar χ⟩

omit [IsTotallyComplex E] in

/- English proof (translation)
Establish `h0 : Valued.v (x : w.adicCompletion E) ≠ 0` using `by simp`. Establish `e : Valued.v (x : w.adicCompletion E) = WithZero.exp (-Formalism.UG.ordV E w x)`. Rewrite using `[Formalism.UG.ordV, dif_neg h0, neg_neg]`. Conclude with `(WithZero.coe_unzero h0).symm`. Establish `hu : IsUnitAt w (x / atFin w (unif w) ^ Formalism.UG.ordV E w x)`.

Establish `h2 : Valued.v _ = _` using `unif_spec w`. Unfold `IsUnitAt`. Rewrite using `[Units.val_div_eq_div_val, Units.val_zpow_eq_zpow_val, map_div₀, map_zpow₀, h2, e, ← WithZero.exp_zsmul]`. Simplify using the standard rewrite rules. Establish `h3` using `h _ hu`.

Rewrite `h3` using `[map_div, map_zpow, div_eq_one]`. Conclude with `h3`.
-/
theorem loc_eq_zpow {χ : HChar E} {w : HeightOneSpectrum (𝓞 E)} (h : χ.UnrAt w) (x : (w.adicCompletion E)ˣ) :
    χ.loc w x = χ.val w ^ Formalism.UG.ordV E w x := by
  have h0 : Valued.v (x : w.adicCompletion E) ≠ 0 := by simp
  have e : Valued.v (x : w.adicCompletion E) = WithZero.exp (-Formalism.UG.ordV E w x) := by
    rw [Formalism.UG.ordV, dif_neg h0, neg_neg]
    exact (WithZero.coe_unzero h0).symm
  have hu : IsUnitAt w (x / atFin w (unif w) ^ Formalism.UG.ordV E w x) := by
    have h2 : Valued.v _ = _ := unif_spec w
    unfold IsUnitAt
    rw [Units.val_div_eq_div_val, Units.val_zpow_eq_zpow_val, map_div₀, map_zpow₀, h2, e, ← WithZero.exp_zsmul]
    simp
  have h3 := h _ hu
  rw [map_div, map_zpow, div_eq_one] at h3
  exact h3

/- English proof (translation)
Set `π : CuspSub E 1` to `(CuspSub.triv E le_rfl).twist χ`. Establish `hK : ∀ k ∈ KGL w 1, CuspSub.locDet 1 χ w k = 1`. Introduce and unpack `_ ⟨k, rfl⟩`. Use `h _ ?_` and prove the remaining obligations. Establish `e : ((GeneralLinearGroup.det (GeneralLinearGroup.map (Formalism.UG.Ov E w).subtype k) : (w.adicCompletion E)ˣ) : w.adicCompletion E) = _` using `det_map _ k`.

Conclude with `(congrArg Valued.v e).trans <| (Valuation.integer.integers (Valued.v : Valuation (w.adicCompletion E) _)).one_of_isUnit (Units.isUnit _)`. Establish `hop : ∀ g (x : π.V), π.locRep w g x = ((CuspSub.locDet 1 χ w g : ℂˣ) : ℂ) • x` using `fun g x => by`. Rewrite using `[CuspSub.locRep_eq, CuspSub.op_triv_twist, ← CuspSub.chiDet_locGL]`. Simplify using `[opMul, opTriv, opAdd]`. Establish `hs : Formalism.UG.IsSpherical E w (fun _ : Fin 1 => ((χ.val w : ℂˣ) : ℂ)) fun g => ((CuspSub.locDet 1 χ w g : ℂˣ) : ℂ)` using `fun b g k _ hk => by`.

Establish `e : CuspSub.locDet 1 χ w b = _` using `loc_eq_zpow h (GeneralLinearGroup.det b)`. Simplify using `[hK k hk, e, Formalism.UG.chiDelta]`. Establish `hv` using `isSatVecGL_of_isSpherical (α := fun _ => χ.val w) hs fun e => Units.ne_zero _ (congrFun e 1)`. Use `Submodule.nontrivial_iff_ne_bot.2 π.ne_bot` as an intermediate fact. Use `⟨?_, fun x _ h0 => ?_⟩` and prove the remaining obligations.

Take `⟨x, hx⟩` from `exists_ne (0 : π.V)`. Conclude with `(Submodule.ne_bot_iff _).2 ⟨x, GlobalTheory.LGrp.mem_fixed.2 fun k hk => by rw [hop, hK k hk]; simp, hx⟩`. Set `ρ : Representation ℂ (GL (Fin 1) (w.adicCompletion E)) ℂ` to `twRep (Representation.trivial ℂ _ ℂ) (CuspSub.locDet 1 χ w)`. Establish `h1 : IsSatVecGL w ρ 1 {χ.val w}` using `IsSatVecGL.of_map (ρ' := GlobalTheory.PRep.rightReg ℂ _ ℂ) (LinearMap.toSpanSingleton ℂ _ fun g => ((CuspSub.locDet 1 χ w g : ℂˣ) : ℂ)) (fun g y => funext fun x => by`. Express the relevant statement in the definitionally equal form `(_ * y) * _ = y * ((CuspSub.locDet 1 χ w (x * g) : ℂˣ) : ℂ)`.

Rewrite using `[map_mul, Units.val_mul]`. Use the proof step `ring)`. Use the proof step `(fun y y' e => mul_right_cancel₀ (Units.ne_zero _) (congrFun e 1)) (by simpa using hv)`. Simplify `h0)` using `using h1.map (ρ' := π.locRep w) (LinearMap.toSpanSingleton ℂ _ x) (fun g y => by simp [ρ, hop, smul_smul, mul_comm]) (by simpa`.
-/
theorem hasSat_ofChar {χ : HChar E} {w : HeightOneSpectrum (𝓞 E)} (h : χ.UnrAt w) : (ofChar χ).HasSat w {χ.val w} := by
  let π : CuspSub E 1 := (CuspSub.triv E le_rfl).twist χ
  have hK : ∀ k ∈ KGL w 1, CuspSub.locDet 1 χ w k = 1 := by
    rintro _ ⟨k, rfl⟩
    refine h _ ?_
    have e : ((GeneralLinearGroup.det (GeneralLinearGroup.map (Formalism.UG.Ov E w).subtype k) : (w.adicCompletion E)ˣ) :
      w.adicCompletion E) = _ := det_map _ k
    exact (congrArg Valued.v e).trans <| (Valuation.integer.integers (Valued.v : Valuation (w.adicCompletion E) _)).one_of_isUnit (Units.isUnit _)
  have hop : ∀ g (x : π.V), π.locRep w g x = ((CuspSub.locDet 1 χ w g : ℂˣ) : ℂ) • x := fun g x => by
    rw [CuspSub.locRep_eq, CuspSub.op_triv_twist, ← CuspSub.chiDet_locGL]
    simp [opMul, opTriv, opAdd]
  have hs : Formalism.UG.IsSpherical E w (fun _ : Fin 1 => ((χ.val w : ℂˣ) : ℂ))
      fun g => ((CuspSub.locDet 1 χ w g : ℂˣ) : ℂ) := fun b g k _ hk => by
    have e : CuspSub.locDet 1 χ w b = _ := loc_eq_zpow h (GeneralLinearGroup.det b)
    simp [hK k hk, e, Formalism.UG.chiDelta]
  have hv := isSatVecGL_of_isSpherical (α := fun _ => χ.val w) hs fun e => Units.ne_zero _ (congrFun e 1)
  have := Submodule.nontrivial_iff_ne_bot.2 π.ne_bot
  refine ⟨?_, fun x _ h0 => ?_⟩
  · obtain ⟨x, hx⟩ := exists_ne (0 : π.V)
    exact (Submodule.ne_bot_iff _).2 ⟨x, GlobalTheory.LGrp.mem_fixed.2 fun k hk => by rw [hop, hK k hk]; simp, hx⟩
  · let ρ : Representation ℂ (GL (Fin 1) (w.adicCompletion E)) ℂ :=
      twRep (Representation.trivial ℂ _ ℂ) (CuspSub.locDet 1 χ w)
    have h1 : IsSatVecGL w ρ 1 {χ.val w} :=
      IsSatVecGL.of_map (ρ' := GlobalTheory.PRep.rightReg ℂ _ ℂ) (LinearMap.toSpanSingleton ℂ _ fun g => ((CuspSub.locDet 1 χ w g : ℂˣ) : ℂ))
        (fun g y => funext fun x => by
          change (_ * y) * _ = y * ((CuspSub.locDet 1 χ w (x * g) : ℂˣ) : ℂ)
          rw [map_mul, Units.val_mul]; ring)
        (fun y y' e => mul_right_cancel₀ (Units.ne_zero _) (congrFun e 1)) (by simpa using hv)
    simpa using h1.map (ρ' := π.locRep w) (LinearMap.toSpanSingleton ℂ _ x)
      (fun g y => by simp [ρ, hop, smul_smul, mul_comm]) (by simpa using h0)

end CG

end GlobalTheory.CuspRep

namespace GlobalTheory.Published

open GlobalTheory.CuspRep

def JacquetShalikaRigidity : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (ι κ : Type) [Fintype ι] [Fintype κ]
    (m : ι → ℕ) (m' : κ → ℕ) (π : ∀ i, CG E (m i)) (π' : ∀ j, CG E (m' j)),
    (∀ i, 1 ≤ m i) → (∀ j, 1 ≤ m' j) →
    (∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ (B : ι → Multiset ℂˣ) (B' : κ → Multiset ℂˣ),
      (∀ i, (π i).HasSat w (B i)) ∧ (∀ j, (π' j).HasSat w (B' j)) ∧ ∑ i, B i = ∑ j, B' j) →
    ∃ s : ι ≃ κ, ∀ i, (⟨m i, π i⟩ : Σ a, CG E a) = ⟨m' (s i), π' (s i)⟩

def JacquetShalikaBound : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CG E a), π.IsUnitary →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ), π.HasSat w B → ∀ α ∈ B,
      (Ideal.absNorm w.asIdeal : ℝ) ^ (-(1 / 2) : ℝ) < ‖(α : ℂ)‖ ∧ ‖(α : ℂ)‖ < (Ideal.absNorm w.asIdeal : ℝ) ^ (1 / 2 : ℝ)

def JacquetShalika : Prop := JacquetShalikaRigidity ∧ JacquetShalikaBound

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

namespace JacquetShalikaRigidity

/- English proof (translation)
Take `⟨s, hs⟩` from `h E Unit Unit (fun _ => a) (fun _ => a) (fun _ => π) (fun _ => π') (fun _ => ha) (fun _ => ha) (hw.mono fun w ⟨B, h1, h2⟩ => ⟨fun _ => B, fun _ => B, fun _ => h1, fun _ => h2, rfl⟩)`. Conclude with `eq_of_heq (Sigma.mk.inj (hs ())).2`.
-/
theorem strong_multiplicity_one (h : JacquetShalikaRigidity) {a : ℕ} (ha : 1 ≤ a) (π π' : CG E a)
    (hw : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B, π.HasSat w B ∧ π'.HasSat w B) : π = π' := by
  obtain ⟨s, hs⟩ := h E Unit Unit (fun _ => a) (fun _ => a) (fun _ => π) (fun _ => π') (fun _ => ha) (fun _ => ha)
    (hw.mono fun w ⟨B, h1, h2⟩ => ⟨fun _ => B, fun _ => B, fun _ => h1, fun _ => h2, rfl⟩)
  exact eq_of_heq (Sigma.mk.inj (hs ())).2

/- English proof (translation)
Take `⟨s, hs⟩` from `h E (Fin P.length) (Fin Q.length) (fun i => (P.get i).1) (fun j => (Q.get j).1) (fun i => (P.get i).2) (fun j => (Q.get j).2) (fun i => hP _ (List.get_mem _ _)) (fun j => hQ _ (List.get_mem _ _)) (hw.mono fun w ⟨B, h1, h2, h3⟩ => ⟨fun i => B (P.get i), fun j => B (Q.get j), fun i …`. Establish `e : ∀ L : List (Σ a, CG E a), (L : Multiset _) = Finset.univ.val.map L.get` using `fun L => by`. Rewrite using `[Fin.univ_val_map, List.ofFn_get]`. Rewrite using `[← Multiset.coe_eq_coe, e, e, ← Finset.map_univ_equiv s, Finset.map_val, Multiset.map_map]`. Conclude with `Multiset.map_congr rfl fun i _ => hs i`.
-/
theorem perm (h : JacquetShalikaRigidity) (P Q : List (Σ a, CG E a)) (hP : ∀ p ∈ P, 1 ≤ p.1) (hQ : ∀ p ∈ Q, 1 ≤ p.1)
    (hw : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B : (Σ a, CG E a) → Multiset ℂˣ,
      (∀ p ∈ P, p.2.HasSat w (B p)) ∧ (∀ p ∈ Q, p.2.HasSat w (B p)) ∧ (P.map B).sum = (Q.map B).sum) : P.Perm Q := by
  obtain ⟨s, hs⟩ := h E (Fin P.length) (Fin Q.length) (fun i => (P.get i).1) (fun j => (Q.get j).1)
    (fun i => (P.get i).2) (fun j => (Q.get j).2) (fun i => hP _ (List.get_mem _ _)) (fun j => hQ _ (List.get_mem _ _))
    (hw.mono fun w ⟨B, h1, h2, h3⟩ => ⟨fun i => B (P.get i), fun j => B (Q.get j), fun i => h1 _ (List.get_mem _ _),
      fun j => h2 _ (List.get_mem _ _), by simpa [← List.sum_ofFn, List.ofFn_getElem_eq_map] using h3⟩)
  have e : ∀ L : List (Σ a, CG E a), (L : Multiset _) = Finset.univ.val.map L.get := fun L => by
    rw [Fin.univ_val_map, List.ofFn_get]
  rw [← Multiset.coe_eq_coe, e, e, ← Finset.map_univ_equiv s, Finset.map_val, Multiset.map_map]
  exact Multiset.map_congr rfl fun i _ => hs i

/- English proof (translation)
Take `⟨s, hs⟩` from `h E ι κ m m' _ _ hm hm' hw`. Use `⟨s, fun i => ?_⟩` and prove the remaining obligations. Establish `key : ∀ {a b : ℕ} (σ : CG E a) (σ' : CG E b) (x y : ℝ), 1 ≤ a → σ.IsUnitary → σ'.IsUnitary → (⟨a, σ.twist (ν x)⟩ : Σ a, CG E a) = ⟨b, σ'.twist (ν y)⟩ → (⟨a, σ⟩ : Σ a, CG E a) = ⟨b, σ'⟩ ∧ x = y`. Introduce `a b σ σ' x y ha h1 h2 e`. Take `rfl : a = b` from `(Sigma.mk.inj e).1`.

Establish `e'` using `eq_of_heq (Sigma.mk.inj e).2`. Take `rfl` from `CG.exponent_unique ha h1 h2 (hν x) (hν y) e'`. Conclude with `⟨congrArg _ (CG.twist_injective _ e'), rfl⟩`. Conclude with `key _ _ _ _ (hm i) (hu i) (hu' _) (hs i)`.
-/
theorem unitary (h : JacquetShalikaRigidity) {ι κ : Type} [Fintype ι] [Fintype κ] {m : ι → ℕ} {m' : κ → ℕ}
    (π : ∀ i, CG E (m i)) (π' : ∀ j, CG E (m' j)) (hm : ∀ i, 1 ≤ m i) (hm' : ∀ j, 1 ≤ m' j)
    (hu : ∀ i, (π i).IsUnitary) (hu' : ∀ j, (π' j).IsUnitary) (ν : ℝ → HChar E) (hν : ∀ s, (ν s).IsAbsPow s)
    (t : ι → ℝ) (t' : κ → ℝ)
    (hw : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ (B : ι → Multiset ℂˣ) (B' : κ → Multiset ℂˣ),
      (∀ i, ((π i).twist (ν (t i))).HasSat w (B i)) ∧ (∀ j, ((π' j).twist (ν (t' j))).HasSat w (B' j)) ∧
        ∑ i, B i = ∑ j, B' j) :
    ∃ s : ι ≃ κ, ∀ i, (⟨m i, π i⟩ : Σ a, CG E a) = ⟨m' (s i), π' (s i)⟩ ∧ t i = t' (s i) := by
  obtain ⟨s, hs⟩ := h E ι κ m m' _ _ hm hm' hw
  refine ⟨s, fun i => ?_⟩
  have key : ∀ {a b : ℕ} (σ : CG E a) (σ' : CG E b) (x y : ℝ), 1 ≤ a → σ.IsUnitary → σ'.IsUnitary →
      (⟨a, σ.twist (ν x)⟩ : Σ a, CG E a) = ⟨b, σ'.twist (ν y)⟩ → (⟨a, σ⟩ : Σ a, CG E a) = ⟨b, σ'⟩ ∧ x = y := by
    intro a b σ σ' x y ha h1 h2 e
    obtain rfl : a = b := (Sigma.mk.inj e).1
    have e' := eq_of_heq (Sigma.mk.inj e).2
    obtain rfl := CG.exponent_unique ha h1 h2 (hν x) (hν y) e'
    exact ⟨congrArg _ (CG.twist_injective _ e'), rfl⟩
  exact key _ _ _ _ (hm i) (hu i) (hu' _) (hs i)

end JacquetShalikaRigidity

end GlobalTheory.Published
