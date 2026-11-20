import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.BoundedOnFramesIffIntegralOnFrames

open IsLocalRing

namespace GlobalTheory

open IsLocalRing in

/- English proof (translation)
Establish `hzero : ∀ n : ℕ, ∀ a ∈ Ideal.span {((p ^ n : ℕ) : ℤ)}, (Int.castRingHom (V ⧸ I ^ n)) a = 0`. Introduce `n a ha`. Take `⟨k, rfl⟩` from `Ideal.mem_span_singleton'.mp ha`. Establish `h : ((p ^ n : ℕ) : V ⧸ I ^ n) = 0`. Rewrite using `[show ((p ^ n : ℕ) : V ⧸ I ^ n) = Ideal.Quotient.mk _ ((p : V) ^ n) by simp, Ideal.Quotient.eq_zero_iff_mem]`.

Conclude with `Ideal.pow_mem_pow hp n`. Rewrite using `[map_mul, map_natCast, h, mul_zero]`. Set `g : (n : ℕ) → ZMod (p ^ n) →+* V ⧸ I ^ n` to `fun n => (Ideal.Quotient.lift _ (Int.castRingHom _) (hzero n)).comp (Int.quotientSpanNatEquivZMod (p ^ n)).symm.toRingHom`. Use `⟨IsAdicComplete.liftRingHom I (fun n => (g n).comp (PadicInt.toZModPow n)) ?_⟩` and prove the remaining obligations. Introduce `m n hle`.

Establish `hg : (Ideal.Quotient.factorPow I hle).comp (g n) = (g m).comp (ZMod.castHom (pow_dvd_pow p hle) _)` using `Subsingleton.elim _ _`. Use extensionality with `x`. Establish `hx` using `RingHom.congr_fun hg (PadicInt.toZModPow n x)`. Rewrite using `[← PadicInt.zmod_cast_comp_toZModPow m n hle]`. Conclude with `hx`.
-/
theorem _root_.GlobalTheory.nonempty_padicInt_ringHom_of_isAdicComplete {V : Type*} [CommRing V] (I : Ideal V)
    [IsAdicComplete I V] (p : ℕ) [Fact p.Prime] (hp : (p : V) ∈ I) : Nonempty (ℤ_[p] →+* V) := by
  have hzero : ∀ n : ℕ, ∀ a ∈ Ideal.span {((p ^ n : ℕ) : ℤ)}, (Int.castRingHom (V ⧸ I ^ n)) a = 0 := by
    intro n a ha
    obtain ⟨k, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    have h : ((p ^ n : ℕ) : V ⧸ I ^ n) = 0 := by
      rw [show ((p ^ n : ℕ) : V ⧸ I ^ n) = Ideal.Quotient.mk _ ((p : V) ^ n) by simp,
        Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.pow_mem_pow hp n
    rw [map_mul, map_natCast, h, mul_zero]
  let g : (n : ℕ) → ZMod (p ^ n) →+* V ⧸ I ^ n := fun n =>
    (Ideal.Quotient.lift _ (Int.castRingHom _) (hzero n)).comp
      (Int.quotientSpanNatEquivZMod (p ^ n)).symm.toRingHom
  refine ⟨IsAdicComplete.liftRingHom I (fun n => (g n).comp (PadicInt.toZModPow n)) ?_⟩
  intro m n hle
  have hg : (Ideal.Quotient.factorPow I hle).comp (g n) =
      (g m).comp (ZMod.castHom (pow_dvd_pow p hle) _) := Subsingleton.elim _ _
  ext x
  have hx := RingHom.congr_fun hg (PadicInt.toZModPow n x)
  rw [← PadicInt.zmod_cast_comp_toZModPow m n hle]
  exact hx

open IsLocalRing in

/- English proof (translation)
Take `⟨q, hq⟩` from `CharP.exists (ResidueField V)`. Establish `hprime : q.Prime` using `CharP.char_is_prime (ResidueField V) q`. Use `haveI hfact : Fact q.Prime := ⟨hprime⟩`. Establish `hmem : (q : V) ∈ maximalIdeal V`. Rewrite using `[← residue_eq_zero_iff, map_natCast]`.

Conclude with `CharP.cast_eq_zero _ q`. Take `⟨φ⟩` from `_root_.GlobalTheory.nonempty_padicInt_ringHom_of_isAdicComplete (maximalIdeal V) q hmem`. Use `letI : Algebra ℤ_[q] V := φ.toAlgebra`. Use `⟨q, hfact, this, ?_⟩` and prove the remaining obligations. Use `haveI : Finite (V ⧸ maximalIdeal V) := ‹Finite (ResidueField V)›`.

Establish `hne : (q : V) ≠ 0` using `Nat.cast_ne_zero.mpr hprime.ne_zero`. Establish `himage : algebraMap ℤ_[q] V (q : ℤ_[q]) = (q : V)` using `map_natCast _ q`. Use `_root_.GlobalTheory.finite_of_forall_prime_mem hne ?_ ?_ ?_` and prove the remaining obligations. Introduce `P hP hPne`. Establish `hmax : P.IsMaximal` using `hP.isMaximal hPne`.

Rewrite using `[IsLocalRing.eq_maximalIdeal hmax]`. Conclude with `hmem`. Introduce `hbot`. Apply `hne` to reduce the goal to its premises. Rewrite using `[← himage, ← Ideal.mem_bot, ← hbot]`.

Apply `Ideal.mem_map_of_mem` to reduce the goal to its premises. Rewrite using `[PadicInt.maximalIdeal_eq_span_p]`. Conclude with `Ideal.mem_span_singleton_self _`. Apply `ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal V).ne_top` to reduce the goal to its premises. Rewrite using `[Ideal.map_le_iff_le_comap, PadicInt.maximalIdeal_eq_span_p, Ideal.span_le, Set.singleton_subset_iff]`.

Express the relevant statement in the definitionally equal form `algebraMap ℤ_[q] V (q : ℤ_[q]) ∈ maximalIdeal V`. Rewrite using `[himage]`. Conclude with `hmem`.
-/
theorem _root_.GlobalTheory.exists_padicInt_algebra_finite (V : Type*) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V]
    [Finite (ResidueField V)] :
    ∃ (p : ℕ) (_ : Fact p.Prime) (_ : Algebra ℤ_[p] V), Module.Finite ℤ_[p] V := by
  obtain ⟨q, hq⟩ := CharP.exists (ResidueField V)
  have hprime : q.Prime := CharP.char_is_prime (ResidueField V) q
  haveI hfact : Fact q.Prime := ⟨hprime⟩
  have hmem : (q : V) ∈ maximalIdeal V := by
    rw [← residue_eq_zero_iff, map_natCast]
    exact CharP.cast_eq_zero _ q
  obtain ⟨φ⟩ := _root_.GlobalTheory.nonempty_padicInt_ringHom_of_isAdicComplete (maximalIdeal V) q hmem
  letI : Algebra ℤ_[q] V := φ.toAlgebra
  refine ⟨q, hfact, this, ?_⟩
  haveI : Finite (V ⧸ maximalIdeal V) := ‹Finite (ResidueField V)›
  have hne : (q : V) ≠ 0 := Nat.cast_ne_zero.mpr hprime.ne_zero
  have himage : algebraMap ℤ_[q] V (q : ℤ_[q]) = (q : V) := map_natCast _ q
  refine _root_.GlobalTheory.finite_of_forall_prime_mem hne ?_ ?_ ?_
  · intro P hP hPne
    have hmax : P.IsMaximal := hP.isMaximal hPne
    rw [IsLocalRing.eq_maximalIdeal hmax]
    exact hmem
  · intro hbot
    apply hne
    rw [← himage, ← Ideal.mem_bot, ← hbot]
    apply Ideal.mem_map_of_mem
    rw [PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.mem_span_singleton_self _
  · apply ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal V).ne_top
    rw [Ideal.map_le_iff_le_comap, PadicInt.maximalIdeal_eq_span_p, Ideal.span_le,
      Set.singleton_subset_iff]
    change algebraMap ℤ_[q] V (q : ℤ_[q]) ∈ maximalIdeal V
    rw [himage]
    exact hmem

open IsLocalRing in

/- English proof (translation)
Use `haveI : CharZero V := (algebraMap V K).charZero`. Take `⟨p, hfact, _, hfin⟩` from `_root_.GlobalTheory.exists_padicInt_algebra_finite V`. Establish `hp : (p : V) ≠ 0` using `Nat.cast_ne_zero.mpr hfact.out.ne_zero`. Take `⟨L, hL, g, hg⟩` from `_root_.GlobalTheory.exists_injective_algHom_integralClosure V hp`. Set `ψ : V →+* PadicAlgCl p` to `L.val.toRingHom.comp ((integralClosure ℤ_[p] L).val.toRingHom.comp g.toRingHom)`.

Establish `hψ : ∀ v, ψ v = ((g v : L) : PadicAlgCl p)` using `fun v => rfl`. Establish `hψinj : Function.Injective ψ` using `fun a b h => hg (Subtype.ext (Subtype.ext h))`. Set `f : K →+* PadicAlgCl p` to `IsFractionRing.lift hψinj`. Establish `hf : ∀ v, f (algebraMap V K v) = ψ v` using `IsFractionRing.lift_algebraMap hψinj`. Establish `hψZ : ∀ x : ℤ_[p], ψ (algebraMap ℤ_[p] V x) = algebraMap ℤ_[p] (PadicAlgCl p) x`.

Introduce `x`. Rewrite using `[hψ, g.commutes]`. Both sides reduce to the same expression. Set `K₀ : IntermediateField ℚ_[p] (PadicAlgCl p)` to `{ f.fieldRange with algebraMap_mem' := by`. Introduce `r`.

Take `⟨a, b, -, rfl⟩` from `IsFractionRing.div_surjective (A := ℤ_[p]) r`. Rewrite using `[map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, ← hψZ, ← hψZ, ← hf, ← hf, ← map_div₀]`. Conclude with `⟨_, rfl⟩ }`. Establish `hK₀ : ∀ y, y ∈ K₀ ↔ ∃ x, f x = y` using `fun y => Iff.rfl`. Establish `hle : K₀ ≤ L`.

Introduce `y hy`. Take `⟨x, rfl⟩` from `(hK₀ y).mp hy`. Take `⟨a, b, -, rfl⟩` from `IsFractionRing.div_surjective (A := V) x`. Rewrite using `[map_div₀, hf, hf, hψ, hψ]`. Conclude with `div_mem (g a : L).2 (g b : L).2`.

Use `haveI : FiniteDimensional ℚ_[p] K₀ := FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap (IntermediateField.inclusion_injective hle)`. Set `e : K ≃+* K₀` to `RingEquiv.ofBijective (f.codRestrict K₀ fun x => (hK₀ _).mpr ⟨x, rfl⟩) ⟨fun a b h => f.injective (congrArg Subtype.val h), fun y => by`. Take `⟨x, hx⟩` from `(hK₀ y).mp y.2`. Conclude with `⟨x, Subtype.ext hx⟩⟩`. Establish `he : ∀ x, ((e x : K₀) : PadicAlgCl p) = f x` using `fun x => rfl`.

Establish `hint : ∀ v, e (algebraMap V K v) ∈ integralClosure ℤ_[p] K₀`. Introduce `v`. Rewrite using `[_root_.GlobalTheory.mem_integralClosure_padicInt_iff, he, hf, hψ]`. Conclude with `(_root_.GlobalTheory.mem_integralClosure_padicInt_iff L _).mp (g v).2`. Set `φ : V →+* integralClosure ℤ_[p] K₀` to `(e.toRingHom.comp (algebraMap V K)).codRestrict (integralClosure ℤ_[p] K₀) hint`.

Establish `hφ : ∀ v, ((φ v : integralClosure ℤ_[p] K₀) : K₀) = e (algebraMap V K v)` using `fun v => rfl`. Use `haveI : IsLocalHom (g : V →+* integralClosure ℤ_[p] L) := _root_.GlobalTheory.isLocalHom_of_injective_integralClosure g hg`. Establish `hbij : Function.Bijective φ`. Use `⟨fun a b h => IsFractionRing.injective V K (e.injective ?_), fun y => ?_⟩` and prove the remaining obligations. Rewrite using `[← hφ, ← hφ, h]`.

Take `⟨x, hx⟩` from `e.surjective (y : K₀)`. Establish `hy : ‖f x‖ ≤ 1`. Rewrite using `[← he, hx]`. Conclude with `(_root_.GlobalTheory.mem_integralClosure_padicInt_iff K₀ _).mp y.2`. Establish `hpre : ∀ v, algebraMap V K v = x → ∃ w, φ w = y` using `fun v hv => ⟨v, Subtype.ext (by rw [hφ, hv, hx])⟩`.

Distinguish the cases in `hx0 : x = 0`. Conclude with `hpre 0 (by rw [map_zero, hx0])`. Break down `ValuationRing.isInteger_or_isInteger V x with ⟨v, hv⟩ | ⟨v, hv⟩` into its components or cases. Conclude with `hpre v hv`. Distinguish the cases in `hu : IsUnit v`.

Use `hpre (↑hu.unit⁻¹) ?_` and prove the remaining obligations. Rewrite using `[map_units_inv, IsUnit.unit_spec, hv, inv_inv]`. It suffices to derive a contradiction. Establish `hgv : g v ∈ maximalIdeal (integralClosure ℤ_[p] L)`. Rewrite using `[mem_maximalIdeal, mem_nonunits_iff]`.

Conclude with `fun h => hu (isUnit_of_map_unit (g : V →+* integralClosure ℤ_[p] L) v h)`. Establish `hlt : ‖ψ v‖ < 1`. Rewrite using `[hψ]`. Conclude with `(_root_.GlobalTheory.mem_maximalIdeal_integralClosure_iff L _).mp hgv`. Establish `hone : f x * ψ v = 1`.

Rewrite using `[← hf, hv, ← map_mul, mul_inv_cancel₀ hx0, map_one]`. Establish `h1 : ‖f x * ψ v‖ < 1`. Rewrite using `[norm_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite `h1` using `[hone, norm_one]`.

Conclude with `lt_irrefl _ h1`. Conclude with `⟨p, hfact, K₀, e, RingEquiv.ofBijective φ hbij, inferInstance, fun x => rfl⟩`.
-/
theorem _root_.GlobalTheory.exists_ringEquiv_integralClosure_padicInt (V K : Type*) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [Field K] [CharZero K]
    [Algebra V K] [IsFractionRing V K] [Finite (ResidueField V)] :
    ∃ (p : ℕ) (_ : Fact p.Prime) (K₀ : IntermediateField ℚ_[p] (PadicAlgCl p)) (e : K ≃+* K₀)
      (e₀ : V ≃+* integralClosure ℤ_[p] K₀), FiniteDimensional ℚ_[p] K₀ ∧
      ∀ x, e (algebraMap V K x) = ((e₀ x : integralClosure ℤ_[p] K₀) : K₀) := by
  haveI : CharZero V := (algebraMap V K).charZero
  obtain ⟨p, hfact, _, hfin⟩ := _root_.GlobalTheory.exists_padicInt_algebra_finite V
  have hp : (p : V) ≠ 0 := Nat.cast_ne_zero.mpr hfact.out.ne_zero
  obtain ⟨L, hL, g, hg⟩ := _root_.GlobalTheory.exists_injective_algHom_integralClosure V hp
  let ψ : V →+* PadicAlgCl p :=
    L.val.toRingHom.comp ((integralClosure ℤ_[p] L).val.toRingHom.comp g.toRingHom)
  have hψ : ∀ v, ψ v = ((g v : L) : PadicAlgCl p) := fun v => rfl
  have hψinj : Function.Injective ψ := fun a b h => hg (Subtype.ext (Subtype.ext h))
  let f : K →+* PadicAlgCl p := IsFractionRing.lift hψinj
  have hf : ∀ v, f (algebraMap V K v) = ψ v := IsFractionRing.lift_algebraMap hψinj
  have hψZ : ∀ x : ℤ_[p], ψ (algebraMap ℤ_[p] V x) = algebraMap ℤ_[p] (PadicAlgCl p) x := by
    intro x
    rw [hψ, g.commutes]
    rfl
  let K₀ : IntermediateField ℚ_[p] (PadicAlgCl p) :=
    { f.fieldRange with
      algebraMap_mem' := by
        intro r
        obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := ℤ_[p]) r
        rw [map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
          ← hψZ, ← hψZ, ← hf, ← hf, ← map_div₀]
        exact ⟨_, rfl⟩ }
  have hK₀ : ∀ y, y ∈ K₀ ↔ ∃ x, f x = y := fun y => Iff.rfl
  have hle : K₀ ≤ L := by
    intro y hy
    obtain ⟨x, rfl⟩ := (hK₀ y).mp hy
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := V) x
    rw [map_div₀, hf, hf, hψ, hψ]
    exact div_mem (g a : L).2 (g b : L).2
  haveI : FiniteDimensional ℚ_[p] K₀ := FiniteDimensional.of_injective
    (IntermediateField.inclusion hle).toLinearMap (IntermediateField.inclusion_injective hle)
  let e : K ≃+* K₀ := RingEquiv.ofBijective (f.codRestrict K₀ fun x => (hK₀ _).mpr ⟨x, rfl⟩)
    ⟨fun a b h => f.injective (congrArg Subtype.val h), fun y => by
      obtain ⟨x, hx⟩ := (hK₀ y).mp y.2
      exact ⟨x, Subtype.ext hx⟩⟩
  have he : ∀ x, ((e x : K₀) : PadicAlgCl p) = f x := fun x => rfl
  have hint : ∀ v, e (algebraMap V K v) ∈ integralClosure ℤ_[p] K₀ := by
    intro v
    rw [_root_.GlobalTheory.mem_integralClosure_padicInt_iff, he, hf, hψ]
    exact (_root_.GlobalTheory.mem_integralClosure_padicInt_iff L _).mp (g v).2
  let φ : V →+* integralClosure ℤ_[p] K₀ :=
    (e.toRingHom.comp (algebraMap V K)).codRestrict (integralClosure ℤ_[p] K₀) hint
  have hφ : ∀ v, ((φ v : integralClosure ℤ_[p] K₀) : K₀) = e (algebraMap V K v) := fun v => rfl
  haveI : IsLocalHom (g : V →+* integralClosure ℤ_[p] L) :=
    _root_.GlobalTheory.isLocalHom_of_injective_integralClosure g hg
  have hbij : Function.Bijective φ := by
    refine ⟨fun a b h => IsFractionRing.injective V K (e.injective ?_), fun y => ?_⟩
    · rw [← hφ, ← hφ, h]
    obtain ⟨x, hx⟩ := e.surjective (y : K₀)
    have hy : ‖f x‖ ≤ 1 := by
      rw [← he, hx]
      exact (_root_.GlobalTheory.mem_integralClosure_padicInt_iff K₀ _).mp y.2
    have hpre : ∀ v, algebraMap V K v = x → ∃ w, φ w = y := fun v hv =>
      ⟨v, Subtype.ext (by rw [hφ, hv, hx])⟩
    by_cases hx0 : x = 0
    · exact hpre 0 (by rw [map_zero, hx0])
    rcases ValuationRing.isInteger_or_isInteger V x with ⟨v, hv⟩ | ⟨v, hv⟩
    · exact hpre v hv
    by_cases hu : IsUnit v
    · refine hpre (↑hu.unit⁻¹) ?_
      rw [map_units_inv, IsUnit.unit_spec, hv, inv_inv]
    · exfalso
      have hgv : g v ∈ maximalIdeal (integralClosure ℤ_[p] L) := by
        rw [mem_maximalIdeal, mem_nonunits_iff]
        exact fun h => hu (isUnit_of_map_unit (g : V →+* integralClosure ℤ_[p] L) v h)
      have hlt : ‖ψ v‖ < 1 := by
        rw [hψ]
        exact (_root_.GlobalTheory.mem_maximalIdeal_integralClosure_iff L _).mp hgv
      have hone : f x * ψ v = 1 := by
        rw [← hf, hv, ← map_mul, mul_inv_cancel₀ hx0, map_one]
      have h1 : ‖f x * ψ v‖ < 1 := by
        rw [norm_mul]
        calc ‖f x‖ * ‖ψ v‖ ≤ 1 * ‖ψ v‖ := mul_le_mul_of_nonneg_right hy (norm_nonneg _)
          _ < 1 := by rw [one_mul]; exact hlt
      rw [hone, norm_one] at h1
      exact lt_irrefl _ h1
  exact ⟨p, hfact, K₀, e, RingEquiv.ofBijective φ hbij, inferInstance, fun x => rfl⟩

open IsLocalRing in
/- English proof (translation)
Use `haveI := _root_.GlobalTheory.isDiscreteValuationRing_integralClosure_padicInt p K`. Use `set O := integralClosure ℤ_[p] K`. Take `⟨π, hπ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Set `nm : O → ℝ` to `fun x => ‖((x : K) : PadicAlgCl p)‖`. Establish `hnm_mul : ∀ x y : O, nm (x * y) = nm x * nm y` using `fun x y => by simp [nm]`.

Establish `hnm_pow : ∀ (x : O) (n : ℕ), nm (x ^ n) = nm x ^ n` using `fun x n => by simp [nm]`. Establish `hnm_le : ∀ x : O, nm x ≤ 1` using `fun x => (_root_.GlobalTheory.mem_integralClosure_padicInt_iff K _).mp x.2`. Establish `hunit : ∀ u : Oˣ, nm u = 1`. Introduce `u`. Establish `h1` using `hnm_mul u ↑u⁻¹`.

Rewrite `h1` using `[Units.mul_inv]`. Establish `h2 : nm 1 = 1` using `by simp [nm]`. Establish `hu` using `hnm_le u`. Establish `hv` using `hnm_le ↑u⁻¹`. Use polynomial arithmetic with `[norm_nonneg ((((u : O) : K)) : PadicAlgCl p), norm_nonneg (((((u⁻¹ : Oˣ) : O) : K)) : PadicAlgCl p)]`.

Establish `hπ0 : π ≠ 0` using `hπ.ne_zero`. Establish `hpos : 0 < nm π`. Simplify using `only [nm, norm_pos_iff, ne_eq, ZeroMemClass.coe_eq_zero]`. Conclude with `hπ0`. Establish `hr : nm π < 1` using `(_root_.GlobalTheory.mem_maximalIdeal_integralClosure_iff K π).mp ((mem_maximalIdeal _).mpr hπ.not_isUnit)`.

Establish `hmax : maximalIdeal O = Ideal.span {π}` using `hπ.maximalIdeal_eq`. Establish `hmem : ∀ (n : ℕ) (x : O), x ∈ maximalIdeal O ^ n ↔ nm x ≤ nm π ^ n`. Introduce `n x`. Rewrite using `[hmax, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨c, rfl⟩`. Rewrite using `[hnm_mul, hnm_pow]`. Conclude with `mul_le_of_le_one_right (pow_nonneg hpos.le n) (hnm_le c)`. Introduce `hx`. Distinguish the cases in `hx0 : x = 0`.

Rewrite using `[hx0]`. Conclude with `dvd_zero _`. Take `⟨k, u, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hπ`. Rewrite `hx` using `[hnm_mul, hunit, one_mul, hnm_pow]`. Establish `hk : n ≤ k` using `(pow_le_pow_iff_right_of_lt_one₀ hpos hr).mp hx`.

Conclude with `Dvd.dvd.mul_left (pow_dvd_pow π hk) _`. Establish `hsmod : ∀ (n : ℕ) (x y : O), x ≡ y [SMOD (maximalIdeal O ^ n • ⊤ : Submodule O O)] ↔ nm (x - y) ≤ nm π ^ n`. Introduce `n x y`. Rewrite using `[SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, hmem]`. Establish `hdist : ∀ x y : O, dist ((x : K) : PadicAlgCl p) ((y : K) : PadicAlgCl p) = nm (x - y)`.

Introduce `x y`. Simplify using `[nm, dist_eq_norm]`. Use `{ haus' := ?_, prec' := ?_ }` and prove the remaining obligations. Introduce `x hx`. Establish `hle : ∀ n : ℕ, nm x ≤ nm π ^ n` using `fun n => by simpa using (hsmod n x 0).mp (hx n)`.

Establish `hlim : Filter.Tendsto (fun n : ℕ => nm π ^ n) Filter.atTop (nhds 0)` using `tendsto_pow_atTop_nhds_zero_of_lt_one hpos.le hr`. Establish `h0 : nm x ≤ 0` using `ge_of_tendsto' hlim hle`. Establish `hx0 : ((x : K) : PadicAlgCl p) = 0` using `norm_le_zero_iff.mp h0`. Conclude with `Subtype.ext (Subtype.ext hx0)`. Introduce `f hf`.

Set `g : ℕ → PadicAlgCl p` to `fun n => ((f n : K) : PadicAlgCl p)`. Establish `hcauchy : CauchySeq g`. Use `cauchySeq_of_le_tendsto_0 (fun N => nm π ^ N) (fun n m N hn hm => ?_) (tendsto_pow_atTop_nhds_zero_of_lt_one hpos.le hr)` and prove the remaining obligations. Rewrite using `[hdist, ← hmem]`. Establish `h1` using `(hmem N _).mpr ((hsmod N _ _).mp (hf hn))`.

Establish `h2` using `(hmem N _).mpr ((hsmod N _ _).mp (hf hm))`. Establish `h3` using `sub_mem h2 h1`. Rewrite `h3` using `[sub_sub_sub_cancel_left]`. Then use the resulting hypothesis. Use `haveI : FiniteDimensional ℚ_[p] (Subalgebra.toSubmodule K.toSubalgebra) := ‹FiniteDimensional ℚ_[p] K›`. Establish `hKc : IsComplete (K : Set (PadicAlgCl p))` using `Submodule.complete_of_finiteDimensional (Subalgebra.toSubmodule K.toSubalgebra)`.

Take `⟨a, haK, hlim⟩` from `cauchySeq_tendsto_of_isComplete hKc (fun n => (f n : K).2) hcauchy`. Establish `ha1 : ‖a‖ ≤ 1` using `le_of_tendsto' hlim.norm fun n => hnm_le (f n)`. Set `L : O` to `⟨⟨a, haK⟩, (_root_.GlobalTheory.mem_integralClosure_padicInt_iff K _).mpr ha1⟩`. Use `⟨L, fun n => (hsmod n _ _).mpr ?_⟩` and prove the remaining obligations. Establish `hlim' : Filter.Tendsto (fun k => ‖g n - g k‖) Filter.atTop (nhds ‖g n - a‖)` using `(tendsto_const_nhds.sub hlim).norm`.

Establish `hbound : ∀ᶠ k in Filter.atTop, ‖g n - g k‖ ≤ nm π ^ n`. Use `Filter.eventually_atTop.mpr ⟨n, fun k hk => ?_⟩` and prove the remaining obligations. Rewrite using `[← dist_eq_norm, hdist]`. Conclude with `(hsmod n _ _).mp (hf hk)`. Establish `hfin` using `le_of_tendsto hlim' hbound`.

Simplify `hfin` using `[nm, g, L]`.
-/
private theorem isAdicComplete_integralClosure_padicInt (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    [IsLocalRing (integralClosure ℤ_[p] K)] :
    IsAdicComplete (maximalIdeal (integralClosure ℤ_[p] K)) (integralClosure ℤ_[p] K) := by
  haveI := _root_.GlobalTheory.isDiscreteValuationRing_integralClosure_padicInt p K
  set O := integralClosure ℤ_[p] K
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  let nm : O → ℝ := fun x => ‖((x : K) : PadicAlgCl p)‖
  have hnm_mul : ∀ x y : O, nm (x * y) = nm x * nm y := fun x y => by simp [nm]
  have hnm_pow : ∀ (x : O) (n : ℕ), nm (x ^ n) = nm x ^ n := fun x n => by simp [nm]
  have hnm_le : ∀ x : O, nm x ≤ 1 := fun x => (_root_.GlobalTheory.mem_integralClosure_padicInt_iff K _).mp x.2
  have hunit : ∀ u : Oˣ, nm u = 1 := by
    intro u
    have h1 := hnm_mul u ↑u⁻¹
    rw [Units.mul_inv] at h1
    have h2 : nm 1 = 1 := by simp [nm]
    have hu := hnm_le u
    have hv := hnm_le ↑u⁻¹
    nlinarith [norm_nonneg ((((u : O) : K)) : PadicAlgCl p),
      norm_nonneg (((((u⁻¹ : Oˣ) : O) : K)) : PadicAlgCl p)]
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have hpos : 0 < nm π := by
    simp only [nm, norm_pos_iff, ne_eq, ZeroMemClass.coe_eq_zero]
    exact hπ0
  have hr : nm π < 1 := (_root_.GlobalTheory.mem_maximalIdeal_integralClosure_iff K π).mp
    ((mem_maximalIdeal _).mpr hπ.not_isUnit)
  have hmax : maximalIdeal O = Ideal.span {π} := hπ.maximalIdeal_eq
  have hmem : ∀ (n : ℕ) (x : O), x ∈ maximalIdeal O ^ n ↔ nm x ≤ nm π ^ n := by
    intro n x
    rw [hmax, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨c, rfl⟩
      rw [hnm_mul, hnm_pow]
      exact mul_le_of_le_one_right (pow_nonneg hpos.le n) (hnm_le c)
    · intro hx
      by_cases hx0 : x = 0
      · rw [hx0]
        exact dvd_zero _
      obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hπ
      rw [hnm_mul, hunit, one_mul, hnm_pow] at hx
      have hk : n ≤ k := (pow_le_pow_iff_right_of_lt_one₀ hpos hr).mp hx
      exact Dvd.dvd.mul_left (pow_dvd_pow π hk) _
  have hsmod : ∀ (n : ℕ) (x y : O),
      x ≡ y [SMOD (maximalIdeal O ^ n • ⊤ : Submodule O O)] ↔ nm (x - y) ≤ nm π ^ n := by
    intro n x y
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, hmem]
  have hdist : ∀ x y : O, dist ((x : K) : PadicAlgCl p) ((y : K) : PadicAlgCl p) = nm (x - y) := by
    intro x y
    simp [nm, dist_eq_norm]
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    have hle : ∀ n : ℕ, nm x ≤ nm π ^ n := fun n => by simpa using (hsmod n x 0).mp (hx n)
    have hlim : Filter.Tendsto (fun n : ℕ => nm π ^ n) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hpos.le hr
    have h0 : nm x ≤ 0 := ge_of_tendsto' hlim hle
    have hx0 : ((x : K) : PadicAlgCl p) = 0 := norm_le_zero_iff.mp h0
    exact Subtype.ext (Subtype.ext hx0)
  · intro f hf
    let g : ℕ → PadicAlgCl p := fun n => ((f n : K) : PadicAlgCl p)
    have hcauchy : CauchySeq g := by
      refine cauchySeq_of_le_tendsto_0 (fun N => nm π ^ N) (fun n m N hn hm => ?_)
        (tendsto_pow_atTop_nhds_zero_of_lt_one hpos.le hr)
      rw [hdist, ← hmem]
      have h1 := (hmem N _).mpr ((hsmod N _ _).mp (hf hn))
      have h2 := (hmem N _).mpr ((hsmod N _ _).mp (hf hm))
      have h3 := sub_mem h2 h1
      rwa [sub_sub_sub_cancel_left] at h3
    haveI : FiniteDimensional ℚ_[p] (Subalgebra.toSubmodule K.toSubalgebra) :=
      ‹FiniteDimensional ℚ_[p] K›
    have hKc : IsComplete (K : Set (PadicAlgCl p)) :=
      Submodule.complete_of_finiteDimensional (Subalgebra.toSubmodule K.toSubalgebra)
    obtain ⟨a, haK, hlim⟩ := cauchySeq_tendsto_of_isComplete hKc (fun n => (f n : K).2) hcauchy
    have ha1 : ‖a‖ ≤ 1 := le_of_tendsto' hlim.norm fun n => hnm_le (f n)
    let L : O := ⟨⟨a, haK⟩, (_root_.GlobalTheory.mem_integralClosure_padicInt_iff K _).mpr ha1⟩
    refine ⟨L, fun n => (hsmod n _ _).mpr ?_⟩
    have hlim' : Filter.Tendsto (fun k => ‖g n - g k‖) Filter.atTop (nhds ‖g n - a‖) :=
      (tendsto_const_nhds.sub hlim).norm
    have hbound : ∀ᶠ k in Filter.atTop, ‖g n - g k‖ ≤ nm π ^ n := by
      refine Filter.eventually_atTop.mpr ⟨n, fun k hk => ?_⟩
      rw [← dist_eq_norm, hdist]
      exact (hsmod n _ _).mp (hf hk)
    have hfin := le_of_tendsto hlim' hbound
    simpa [nm, g, L] using hfin

open IsLocalRing in

/- English proof (translation)
Use `⟨fun V K _ _ _ _ _ _ _ _ hres => ?_, fun p _ K₀ K' h hK' => ?_⟩` and prove the remaining obligations. Use `haveI := hres`. Conclude with `_root_.GlobalTheory.exists_ringEquiv_integralClosure_padicInt V K`. Use `haveI := hK'`. Use `⟨_root_.GlobalTheory.isDiscreteValuationRing_integralClosure_padicInt p K', _root_.GlobalTheory.isFractionRing_integralClosure_padicInt p K', isAdicComplete_integralClosure_padicInt p K', ?_⟩` and prove the remaining obligations.

Set `F` to `((IntermediateField.inclusion h).restrictScalars ℤ_[p]).mapIntegralClosure`. Establish `hF : Function.Injective F` using `_root_.GlobalTheory.mapIntegralClosure_padicInt_injective _`. Use `⟨(F : integralClosure ℤ_[p] K₀ →+* integralClosure ℤ_[p] K'), ?_, _root_.GlobalTheory.isLocalHom_of_injective_integralClosure F hF, fun x => rfl⟩` and prove the remaining obligations. Use `haveI := _root_.GlobalTheory.finite_integralClosure_padicInt p K'`. Use `RingHom.Finite.of_comp_finite (f := algebraMap ℤ_[p] (integralClosure ℤ_[p] K₀)) ?_` and prove the remaining obligations.

Rewrite using `[AlgHom.comp_algebraMap]`. Conclude with `RingHom.finite_algebraMap.mpr inferInstance`.
-/
theorem _root_.GlobalTheory.completeDVR_eq_integralClosure_padicInt :
    (∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K], Finite (ResidueField V) → ∃ (p : ℕ) (_ : Fact p.Prime) (K₀ : IntermediateField ℚ_[p] (PadicAlgCl p)) (e : K ≃+* K₀) (e₀ : V ≃+* integralClosure ℤ_[p] K₀), FiniteDimensional ℚ_[p] K₀ ∧ ∀ x, e (algebraMap V K x) = ((e₀ x : integralClosure ℤ_[p] K₀) : K₀)) ∧ ∀ (p : ℕ) [Fact p.Prime] (K₀ K' : IntermediateField ℚ_[p] (PadicAlgCl p)) (h : K₀ ≤ K'), FiniteDimensional ℚ_[p] K' → IsDiscreteValuationRing (integralClosure ℤ_[p] K') ∧ IsFractionRing (integralClosure ℤ_[p] K') K' ∧ (∀ [IsLocalRing (integralClosure ℤ_[p] K')], IsAdicComplete (maximalIdeal (integralClosure ℤ_[p] K')) (integralClosure ℤ_[p] K')) ∧ ∃ f : integralClosure ℤ_[p] K₀ →+* integralClosure ℤ_[p] K', f.Finite ∧ IsLocalHom f ∧ ∀ x, ((f x : integralClosure ℤ_[p] K') : K') = IntermediateField.inclusion h x := by
  refine ⟨fun V K _ _ _ _ _ _ _ _ hres => ?_, fun p _ K₀ K' h hK' => ?_⟩
  · haveI := hres
    exact _root_.GlobalTheory.exists_ringEquiv_integralClosure_padicInt V K
  · haveI := hK'
    refine ⟨_root_.GlobalTheory.isDiscreteValuationRing_integralClosure_padicInt p K',
      _root_.GlobalTheory.isFractionRing_integralClosure_padicInt p K',
      isAdicComplete_integralClosure_padicInt p K', ?_⟩
    let F := ((IntermediateField.inclusion h).restrictScalars ℤ_[p]).mapIntegralClosure
    have hF : Function.Injective F := _root_.GlobalTheory.mapIntegralClosure_padicInt_injective _
    refine ⟨(F : integralClosure ℤ_[p] K₀ →+* integralClosure ℤ_[p] K'), ?_,
      _root_.GlobalTheory.isLocalHom_of_injective_integralClosure F hF, fun x => rfl⟩
    haveI := _root_.GlobalTheory.finite_integralClosure_padicInt p K'
    refine RingHom.Finite.of_comp_finite (f := algebraMap ℤ_[p] (integralClosure ℤ_[p] K₀)) ?_
    rw [AlgHom.comp_algebraMap]
    exact RingHom.finite_algebraMap.mpr inferInstance

end GlobalTheory
