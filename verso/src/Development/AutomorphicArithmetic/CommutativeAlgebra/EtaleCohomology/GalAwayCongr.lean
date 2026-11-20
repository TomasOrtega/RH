import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.AbsInvOf
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.PhiGalCris
import Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.PeriodRingUnits.DieudonneManinBasisModification
import GroundTheory.PAdicHodge.ACrisBdRInj

open CrystallineSemistableComparison UpperTheory.Ru.crystallineComparison

namespace UpperTheory.Ru.crystallineComparison.PBIota

open GroundTheory.PAdicHodge DeRhamPotentiallySemistable.DRPst

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
The claim follows from `RingHom.ext fun x => congrFun (eq_galCp_of_continuous τ (galCp σ) (continuous_galCp σ) fun y => by rw [galCp_coe, h]) x`.
-/
private theorem galCp_congr {K L : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (σ : PadicAlgCl l ≃ₐ[K] PadicAlgCl l) (τ : PadicAlgCl l ≃ₐ[L] PadicAlgCl l)
    (h : ∀ y, σ y = τ y) : (galCp σ : ℂ_[l] →+* ℂ_[l]) = galCp τ :=
  RingHom.ext fun x => congrFun (eq_galCp_of_continuous τ (galCp σ) (continuous_galCp σ)
    fun y => by rw [galCp_coe, h]) x

/- English proof (translation)
The claim follows from `AInf.map_congr (galCp_congr σ τ h) _ _`.
-/
private theorem galMap_congr {K L : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (σ : PadicAlgCl l ≃ₐ[K] PadicAlgCl l) (τ : PadicAlgCl l ≃ₐ[L] PadicAlgCl l)
    (h : ∀ y, σ y = τ y) : AInf.galMap σ = AInf.galMap τ :=
  AInf.map_congr (galCp_congr σ τ h) _ _

/- English proof (translation)
The claim follows from `IsLocalization.ringHom_ext (Submonoid.powers ((l : ℕ) : AInf ℂ_[l] l)) (RingHom.ext fun x => by rw [RingHom.comp_apply, RingHom.comp_apply, ACris.galAway_algebraMap, ACris.galAway_algebraMap, AInf.gal_smul_def, AInf.gal_smul_def, galMap_congr σ τ h])`.
-/
private theorem galAway_congr {K L : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (σ : PadicAlgCl l ≃ₐ[K] PadicAlgCl l) (τ : PadicAlgCl l ≃ₐ[L] PadicAlgCl l)
    (h : ∀ y, σ y = τ y) : ACris.galAway σ = ACris.galAway τ :=
  IsLocalization.ringHom_ext (Submonoid.powers ((l : ℕ) : AInf ℂ_[l] l)) (RingHom.ext fun x => by
    rw [RingHom.comp_apply, RingHom.comp_apply, ACris.galAway_algebraMap, ACris.galAway_algebraMap,
      AInf.gal_smul_def, AInf.gal_smul_def, galMap_congr σ τ h])

/- English proof (translation)
Establish `e : ACris.galZero σ = ACris.galZero τ` using `RingHom.ext fun y => Subtype.ext (by`. Rewrite using `[ACris.coe_galZero, ACris.coe_galZero, galAway_congr σ τ h])`. Rewrite using `[ACris.galCris, ACris.galCris, e]`.
-/
private theorem galCris_congr {K L : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (σ : PadicAlgCl l ≃ₐ[K] PadicAlgCl l) (τ : PadicAlgCl l ≃ₐ[L] PadicAlgCl l)
    (h : ∀ y, σ y = τ y) : ACris.galCris σ = ACris.galCris τ := by
  have e : ACris.galZero σ = ACris.galZero τ := RingHom.ext fun y => Subtype.ext (by
    rw [ACris.coe_galZero, ACris.coe_galZero, galAway_congr σ τ h])
  rw [ACris.galCris, ACris.galCris, e]

/- English proof (translation)
The claim follows from `(IsFractionRing.injective (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l)).comp ACris.iota_injective`.
-/
private theorem iC_injective : Function.Injective (iC l) :=
  (IsFractionRing.injective (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l)).comp ACris.iota_injective

/- English proof (translation)
Establish `e : galA g = ACris.galCris (Formalism.Per6.toBot g.1)` using `galCris_congr _ _ fun _ => rfl`. Rewrite using `[e]`. Conclude with `PositivityTheory.LocInh.GaloisCommutant.cD_galCris g.1 a`.
-/
private theorem iC_galA {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (g : K.fixingSubgroup)
    (a : Acris l) : iC l (galA g a) = Formalism.Per6.σD g.1 (iC l a) := by
  have e : galA g = ACris.galCris (Formalism.Per6.toBot g.1) :=
    galCris_congr _ _ fun _ => rfl
  rw [e]
  exact PositivityTheory.LocInh.GaloisCommutant.cD_galCris g.1 a

/- English proof (translation)
Express the relevant statement in the definitionally equal form `algebraMap _ _ (ACris.iota ℂ_[l] l _) = algebraMap _ _ (algebraMap ℚ_[l] _ _)`. Conclude with `congrArg _ (ACris.iota_padicInt z)`.
-/
private theorem iC_zA (z : ℤ_[l]) : iC l (zA l z) = qQ l z := by
  change algebraMap _ _ (ACris.iota ℂ_[l] l _) = algebraMap _ _ (algebraMap ℚ_[l] _ _)
  exact congrArg _ (ACris.iota_padicInt z)

/- English proof (translation)
Use `letI : Algebra A C := c.toAlgebra`. Establish `hc : ∀ a, algebraMap A C a = c a` using `fun _ => rfl`. Use `haveI : IsLocalization (Submonoid.powers t) C := { map_units := by`. Introduce and unpack `⟨_, r, rfl⟩`. Rewrite using `[hc, map_pow]`.

Conclude with `hu.pow r`. Use `surj := fun x => by`. Take `⟨r, a, h⟩` from `loc x`. Use `⟨⟨a, ⟨t ^ r, r, rfl⟩⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `x * algebraMap A C (t ^ r) = algebraMap A C a`.

Rewrite using `[hc, hc, map_pow, mul_comm, h]`. Use `exists_of_eq := fun {x y} h => by`. Rewrite `h` using `[hc, hc]`. Take `⟨r, hr⟩` from `ker (x - y) (by rw [map_sub, h, sub_self])`. Use `⟨⟨t ^ r, r, rfl⟩, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `t ^ r * x = t ^ r * y`. Rewrite `hr` using `[mul_sub, sub_eq_zero]`. Conclude with `hr }`. Establish `hm : ∀ y : Submonoid.powers t, IsUnit (i y)`. Introduce and unpack `⟨_, r, rfl⟩`.

Express the relevant statement in the definitionally equal form `IsUnit (i (t ^ r))`. Rewrite using `[map_pow]`. Conclude with `(IsUnit.mk0 _ ht).pow r`. Set `ι : C →+* E` to `IsLocalization.lift (M := Submonoid.powers t) hm`. Establish `hι : ∀ a, ι (c a) = i a` using `fun a => IsLocalization.lift_eq (M := Submonoid.powers t) hm a`.

Use `⟨ι, (injective_iff_map_eq_zero ι).2 fun x hx => ?_, hι⟩` and prove the remaining obligations. Take `⟨r, a, h⟩` from `loc x`. Establish `h1 : i a = 0` using `by rw [← hι, ← h, map_mul, hx, mul_zero]`. Establish `h2 : a = 0` using `hi (by rw [h1, map_zero])`. Rewrite `h` using `[h2, map_zero]`.

Conclude with `(hu.pow r).mul_right_eq_zero.1 h`.
-/
private theorem exists_lift {A C E : Type} [CommRing A] [CommRing C] [Field E] (t : A) (c : A →+* C)
    (i : A →+* E) (hu : IsUnit (c t)) (loc : ∀ x : C, ∃ (r : ℕ) (a : A), c t ^ r * x = c a)
    (ker : ∀ a : A, c a = 0 → ∃ r : ℕ, t ^ r * a = 0) (hi : Function.Injective i) (ht : i t ≠ 0) :
    ∃ ι : C →+* E, Function.Injective ι ∧ ∀ a, ι (c a) = i a := by
  letI : Algebra A C := c.toAlgebra
  have hc : ∀ a, algebraMap A C a = c a := fun _ => rfl
  haveI : IsLocalization (Submonoid.powers t) C :=
    { map_units := by
        rintro ⟨_, r, rfl⟩
        rw [hc, map_pow]
        exact hu.pow r
      surj := fun x => by
        obtain ⟨r, a, h⟩ := loc x
        refine ⟨⟨a, ⟨t ^ r, r, rfl⟩⟩, ?_⟩
        change x * algebraMap A C (t ^ r) = algebraMap A C a
        rw [hc, hc, map_pow, mul_comm, h]
      exists_of_eq := fun {x y} h => by
        rw [hc, hc] at h
        obtain ⟨r, hr⟩ := ker (x - y) (by rw [map_sub, h, sub_self])
        refine ⟨⟨t ^ r, r, rfl⟩, ?_⟩
        change t ^ r * x = t ^ r * y
        rw [mul_sub, sub_eq_zero] at hr
        exact hr }
  have hm : ∀ y : Submonoid.powers t, IsUnit (i y) := by
    rintro ⟨_, r, rfl⟩
    change IsUnit (i (t ^ r))
    rw [map_pow]
    exact (IsUnit.mk0 _ ht).pow r
  let ι : C →+* E := IsLocalization.lift (M := Submonoid.powers t) hm
  have hι : ∀ a, ι (c a) = i a := fun a => IsLocalization.lift_eq (M := Submonoid.powers t) hm a
  refine ⟨ι, (injective_iff_map_eq_zero ι).2 fun x hx => ?_, hι⟩
  obtain ⟨r, a, h⟩ := loc x
  have h1 : i a = 0 := by rw [← hι, ← h, map_mul, hx, mul_zero]
  have h2 : a = 0 := hi (by rw [h1, map_zero])
  rw [h2, map_zero] at h
  exact (hu.pow r).mul_right_eq_zero.1 h

/- English proof (translation)
Take `⟨r, a, h⟩` from `loc x`. Establish `h1 : d (i t) ^ r * ι (s x) = d (i a)`. Use `congrArg (fun y => ι (s y)) h` as an intermediate fact. Simplify using `only [map_mul, map_pow, hs, hι, hd] at this`. Conclude with `this`.

Establish `h2 : i t ^ r * ι x = i a`. Use `congrArg ι h` as an intermediate fact. Simplify using `only [map_mul, map_pow, hι] at this`. Conclude with `this`. Rewrite `h1` using `[← h2, map_mul, map_pow]`.

Conclude with `mul_left_cancel₀ (pow_ne_zero _ ((map_ne_zero d).2 ht)) h1`.
-/
private theorem lift_comm {A C E : Type} [CommRing A] [CommRing C] [Field E] (t : A) (c : A →+* C)
    (i : A →+* E) (loc : ∀ x : C, ∃ (r : ℕ) (a : A), c t ^ r * x = c a) (ht : i t ≠ 0)
    (ι : C →+* E) (hι : ∀ a, ι (c a) = i a) (s : C →+* C) (u : A →+* A) (d : E →+* E)
    (hs : ∀ a, s (c a) = c (u a)) (hd : ∀ a, i (u a) = d (i a)) (x : C) : ι (s x) = d (ι x) := by
  obtain ⟨r, a, h⟩ := loc x
  have h1 : d (i t) ^ r * ι (s x) = d (i a) := by
    have := congrArg (fun y => ι (s y)) h
    simp only [map_mul, map_pow, hs, hι, hd] at this
    exact this
  have h2 : i t ^ r * ι x = i a := by
    have := congrArg ι h
    simp only [map_mul, map_pow, hι] at this
    exact this
  rw [← h2, map_mul, map_pow] at h1
  exact mul_left_cancel₀ (pow_ne_zero _ ((map_ne_zero d).2 ht)) h1

/- English proof (translation)
The claim follows from `IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[l]) (RingHom.ext h)`.
-/
private theorem q_ext {E : Type} [Field E] (f q : ℚ_[l] →+* E)
    (h : ∀ z : ℤ_[l], f (z : ℚ_[l]) = q (z : ℚ_[l])) : f = q :=
  IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[l]) (RingHom.ext h)

end UpperTheory.Ru.crystallineComparison.PBIota

open UpperTheory.Ru.crystallineComparison.PBIota in
/- English proof (translation)
Introduce `l _ K B₀`. Establish `ht0 : DeRhamPotentiallySemistable.DRPst.iC l (tA l) ≠ 0` using `(period_ring_base.isUnit_image_period l).ne_zero`. Take `⟨ι, hinj, hι⟩` from `exists_lift (tA l) B₀.c (DeRhamPotentiallySemistable.DRPst.iC l) B₀.t_unit B₀.loc B₀.ker iC_injective ht0`. Use `⟨ι, hinj, hι, fun z => ?_, fun g x => ?_⟩` and prove the remaining obligations. Conclude with `RingHom.congr_fun (q_ext (ι.comp (algebraMap ℚ_[l] B₀.C)) (DeRhamPotentiallySemistable.DRPst.qQ l) fun z => (congrArg ι (B₀.z_c z)).trans ((hι _).trans (iC_zA z))) z`.

Conclude with `lift_comm (tA l) B₀.c (DeRhamPotentiallySemistable.DRPst.iC l) B₀.loc ht0 ι hι (B₀.σ g : B₀.C →+* B₀.C) (galA g) (Formalism.Per6.σD g.1 : Formalism.Per6.BdR l ≃+* Formalism.Per6.BdR l).toRingHom (B₀.σ_c g) (iC_galA g) x`.
-/
theorem UpperTheory.Ru.crystallineComparison.pbIota :
    ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (B₀ : PB l K), ∃ ι : B₀.C →+* (per l K).B, Function.Injective ι ∧ (∀ a, ι (B₀.c a) = (per l K).i a) ∧ (∀ z, ι (algebraMap ℚ_[l] B₀.C z) = (per l K).q z) ∧ ∀ g x, ι (B₀.σ g x) = (per l K).σ g (ι x) := by
  intro l _ K B₀
  have ht0 : DeRhamPotentiallySemistable.DRPst.iC l (tA l) ≠ 0 := (period_ring_base.isUnit_image_period l).ne_zero
  obtain ⟨ι, hinj, hι⟩ := exists_lift (tA l) B₀.c (DeRhamPotentiallySemistable.DRPst.iC l) B₀.t_unit B₀.loc B₀.ker
    iC_injective ht0
  refine ⟨ι, hinj, hι, fun z => ?_, fun g x => ?_⟩
  · exact RingHom.congr_fun (q_ext (ι.comp (algebraMap ℚ_[l] B₀.C)) (DeRhamPotentiallySemistable.DRPst.qQ l) fun z =>
      (congrArg ι (B₀.z_c z)).trans ((hι _).trans (iC_zA z))) z
  · exact lift_comm (tA l) B₀.c (DeRhamPotentiallySemistable.DRPst.iC l) B₀.loc ht0 ι hι (B₀.σ g : B₀.C →+* B₀.C)
      (galA g) (Formalism.Per6.σD g.1 : Formalism.Per6.BdR l ≃+* Formalism.Per6.BdR l).toRingHom (B₀.σ_c g) (iC_galA g) x
