import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SUnitsNumberFieldFg
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

noncomputable section

namespace GlobalTheory.QNorm

/- English proof (translation)
Establish `hv : v.asIdeal ∈ nonZeroDivisors (Ideal (𝓞 F))` using `mem_nonZeroDivisors_of_ne_zero v.ne_bot`. Use `set h := Fintype.card (ClassGroup (𝓞 F)) with hh`. Establish `hpos : h ≠ 0` using `Fintype.card_ne_zero`. Establish `h1 : ClassGroup.mk0 ⟨v.asIdeal ^ h, pow_mem hv h⟩ = 1`. Establish `: (⟨v.asIdeal ^ h, pow_mem hv h⟩ : nonZeroDivisors (Ideal (𝓞 F))) = ⟨v.asIdeal, hv⟩ ^ h` using `rfl`.

Rewrite using `[this, map_pow, pow_card_eq_one]`. Take `⟨a, ha⟩` from `(ClassGroup.mk0_eq_one_iff _).1 h1`. Establish `ha' : v.asIdeal ^ h = Ideal.span {a}` using `ha`. Use `⟨a, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `rfl`.

Establish `: v.asIdeal ^ h = ⊥` using `by rw [ha']; simp`. Conclude with `pow_ne_zero h v.ne_bot this`. Conclude with `Ideal.pow_le_self hpos (ha' ▸ Ideal.mem_span_singleton_self a)`. Introduce `w hw haw`. Establish `hle : v.asIdeal ^ h ≤ w.asIdeal`.

Rewrite using `[ha']`. Conclude with `(Ideal.span_singleton_le_iff_mem _).2 haw`. Use `w.isPrime` as an intermediate fact. Establish `h2 : v.asIdeal ≤ w.asIdeal` using `Ideal.IsPrime.le_of_pow_le hle`. Conclude with `hw (HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top h2).symm)`.
-/
theorem exists_mem_only (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ a : 𝓞 F, a ≠ 0 ∧ a ∈ v.asIdeal ∧
      ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → a ∉ w.asIdeal := by
  classical
  have hv : v.asIdeal ∈ nonZeroDivisors (Ideal (𝓞 F)) :=
    mem_nonZeroDivisors_of_ne_zero v.ne_bot
  set h := Fintype.card (ClassGroup (𝓞 F)) with hh
  have hpos : h ≠ 0 := Fintype.card_ne_zero
  have h1 : ClassGroup.mk0 ⟨v.asIdeal ^ h, pow_mem hv h⟩ = 1 := by
    have : (⟨v.asIdeal ^ h, pow_mem hv h⟩ : nonZeroDivisors (Ideal (𝓞 F))) =
        ⟨v.asIdeal, hv⟩ ^ h := rfl
    rw [this, map_pow, pow_card_eq_one]
  obtain ⟨a, ha⟩ := (ClassGroup.mk0_eq_one_iff _).1 h1
  have ha' : v.asIdeal ^ h = Ideal.span {a} := ha
  refine ⟨a, ?_, ?_, ?_⟩
  · rintro rfl
    have : v.asIdeal ^ h = ⊥ := by rw [ha']; simp
    exact pow_ne_zero h v.ne_bot this
  · exact Ideal.pow_le_self hpos (ha' ▸ Ideal.mem_span_singleton_self a)
  · intro w hw haw
    have hle : v.asIdeal ^ h ≤ w.asIdeal := by
      rw [ha']; exact (Ideal.span_singleton_le_iff_mem _).2 haw
    have := w.isPrime
    have h2 : v.asIdeal ≤ w.asIdeal := Ideal.IsPrime.le_of_pow_le hle
    exact hw (HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top h2).symm)

/- English proof (translation)
Introduce `F _ _ S`. Establish `hunit : ∀ (u : (𝓞 F)ˣ) (v : HeightOneSpectrum (𝓞 F)), v.valuation F (algebraMap (𝓞 F) F u) = 1`. Introduce `u v`. Rewrite using `[HeightOneSpectrum.valuation_eq_one_iff_notMem]`. Introduce `hu`.

Conclude with `v.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hu u.isUnit)`. Set `f0 : (𝓞 F)ˣ →* sUnits F S` to `(Units.map (algebraMap (𝓞 F) F).toMonoidHom).codRestrict _ (fun u => (mem_sUnits F S _).2 fun v _ => hunit u v)`. Set `f : Additive (𝓞 F)ˣ →ₗ[ℤ] Additive (sUnits F S)` to `(MonoidHom.toAdditive f0).toIntLinearMap`. Set `g0 : Additive (sUnits F S) →+ (S → ℤ)` to `AddMonoidHom.mk' (fun x v => WithZero.log ((v : HeightOneSpectrum (𝓞 F)).valuation F (((Additive.toMul x : sUnits F S) : Fˣ) : F))) (by`. Introduce `a b`.

Use function extensionality and compare the values at `v`. Simplify using `only [toMul_add, Subgroup.coe_mul, Units.val_mul, map_mul, Pi.add_apply]`. Conclude with `WithZero.log_mul (by simp) (by simp))`. Set `g` to `g0.toIntLinearMap`. Establish `hker : LinearMap.ker g = LinearMap.range f`.

Apply `le_antisymm` to reduce the goal to its premises. Introduce `x hx set y : Fˣ := ((Additive.toMul x : sUnits F S) : Fˣ) with hy`. Establish `hall : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F (y : F) = 1`. Introduce `v`. Distinguish the cases in `hv : v ∈ S`.

Establish `h : WithZero.log (v.valuation F (y : F)) = 0` using `congrFun (LinearMap.mem_ker.1 hx) ⟨v, hv⟩`. Establish `hne : v.valuation F (y : F) ≠ 0` using `by simp`. Rewrite using `[← WithZero.exp_log hne, h, WithZero.exp_zero]`. Conclude with `(mem_sUnits F S _).1 (Additive.toMul x).2 v hv`. Take `⟨a, ha⟩` from `HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F (y : F) (fun v => (hall v).le)`.

Take `⟨b, hb⟩` from `HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F (y : F)⁻¹ (fun v => by rw [map_inv₀, hall v, inv_one])`. Establish `hab : a * b = 1`. Apply `IsFractionRing.injective (𝓞 F) F` to reduce the goal to its premises. Rewrite using `[map_mul, ha, hb, map_one, mul_inv_cancel₀ y.ne_zero]`. Use `⟨Additive.ofMul (Units.mkOfMulEqOne a b hab), ?_⟩` and prove the remaining obligations.

Apply `Additive.toMul.injective` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Conclude with `ha`. Introduce and unpack `_ ⟨u, rfl⟩`.

Rewrite using `[LinearMap.mem_ker]`. Use function extensionality and compare the values at `v`. Express the relevant statement in the definitionally equal form `WithZero.log ((v : HeightOneSpectrum (𝓞 F)).valuation F (algebraMap (𝓞 F) F (Additive.toMul u : (𝓞 F)ˣ))) = 0`. Rewrite using `[hunit, WithZero.log_one]`. Establish `hinj : Function.Injective f`.

Introduce `a b hab`. Apply `Additive.toMul.injective` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Apply `IsFractionRing.injective (𝓞 F) F` to reduce the goal to its premises. Conclude with `congrArg (fun x : Additive (sUnits F S) => (((Additive.toMul x : sUnits F S) : Fˣ) : F)) hab`.

Establish `hfin : Module.Finite ℤ (Additive (sUnits F S))` using `Module.Finite.iff_addGroup_fg.2 (GroupFG.iff_add_fg.1 (sUnits_fg F S))`. Establish `hrange : Module.finrank ℤ (LinearMap.range g) = S.card`. Apply `le_antisymm` to reduce the goal to its premises. Use `(Submodule.finrank_le _).trans ?_` and prove the remaining obligations. Simplify using the standard rewrite rules.

Establish `key : ∀ v : S, ∃ c : ℤ, c ≠ 0 ∧ Pi.single v c ∈ LinearMap.range g`. Introduce `v`. Take `⟨a, ha0, hav, haw⟩` from `exists_mem_only F v`. Establish `ha0' : algebraMap (𝓞 F) F a ≠ 0` using `by simpa using ha0`. Establish `hw : ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → w.valuation F (algebraMap (𝓞 F) F a) = 1` using `fun w hw => (HeightOneSpectrum.valuation_eq_one_iff_notMem w).2 (haw w hw)`.

Use `⟨WithZero.log ((v : HeightOneSpectrum (𝓞 F)).valuation F (algebraMap (𝓞 F) F a)), ?_, Additive.ofMul ⟨Units.mk0 _ ha0', (mem_sUnits F S _).2 fun w hwS => hw w (fun e => hwS (e ▸ v.2))⟩, ?_⟩` and prove the remaining obligations. Introduce `h0`. Establish `hne : (v : HeightOneSpectrum (𝓞 F)).valuation F (algebraMap (𝓞 F) F a) ≠ 0`. Simplify using `using ha0`. Establish `h1 : (v : HeightOneSpectrum (𝓞 F)).valuation F (algebraMap (𝓞 F) F a) = 1`.

Rewrite using `[← WithZero.exp_log hne, h0, WithZero.exp_zero]`. Conclude with `(HeightOneSpectrum.valuation_eq_one_iff_notMem _).1 h1 hav`. Use function extensionality and compare the values at `w`. Express the relevant statement in the definitionally equal form `WithZero.log ((w : HeightOneSpectrum (𝓞 F)).valuation F (algebraMap (𝓞 F) F a)) = _`. Distinguish the cases in `hwv : w = v`.

Substitute `hwv` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[Pi.single_eq_of_ne hwv, hw w (fun e => hwv (Subtype.ext e)), WithZero.log_one]`. Use `choose c hc0 hc using key`. Establish `hli : LinearIndependent ℤ (fun v : S => (⟨Pi.single v (c v), hc v⟩ : LinearMap.range g))` using `LinearIndependent.of_comp (LinearMap.range g).subtype (Pi.linearIndependent_single_of_ne_zero hc0)`.

Simplify using `using hli.fintype_card_le_finrank`. Establish `h1` using `Submodule.finrank_quotient_add_finrank (LinearMap.ker g)`. Rewrite `h1` using `[g.quotKerEquivRange.finrank_eq, hrange, hker, LinearMap.finrank_range_of_inj hinj, NumberField.Units.finrank_eq, NumberField.Units.rank]`. Establish `h2 : 0 < Fintype.card (InfinitePlace F)` using `Fintype.card_pos`. Use linear arithmetic over natural numbers and integers.
-/
theorem sUnits_rank :
    ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))),
      Module.finrank ℤ (Additive (sUnits F S)) + 1 = S.card + Fintype.card (InfinitePlace F) := by
  intro F _ _ S
  classical
  have hunit : ∀ (u : (𝓞 F)ˣ) (v : HeightOneSpectrum (𝓞 F)),
      v.valuation F (algebraMap (𝓞 F) F u) = 1 := by
    intro u v
    rw [HeightOneSpectrum.valuation_eq_one_iff_notMem]
    intro hu
    exact v.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hu u.isUnit)
  let f0 : (𝓞 F)ˣ →* sUnits F S :=
    (Units.map (algebraMap (𝓞 F) F).toMonoidHom).codRestrict _
      (fun u => (mem_sUnits F S _).2 fun v _ => hunit u v)
  let f : Additive (𝓞 F)ˣ →ₗ[ℤ] Additive (sUnits F S) :=
    (MonoidHom.toAdditive f0).toIntLinearMap
  let g0 : Additive (sUnits F S) →+ (S → ℤ) :=
    AddMonoidHom.mk' (fun x v => WithZero.log
      ((v : HeightOneSpectrum (𝓞 F)).valuation F (((Additive.toMul x : sUnits F S) : Fˣ) : F))) (by
      intro a b
      funext v
      simp only [toMul_add, Subgroup.coe_mul, Units.val_mul, map_mul, Pi.add_apply]
      exact WithZero.log_mul (by simp) (by simp))
  let g := g0.toIntLinearMap
  have hker : LinearMap.ker g = LinearMap.range f := by
    apply le_antisymm
    · intro x hx
      set y : Fˣ := ((Additive.toMul x : sUnits F S) : Fˣ) with hy
      have hall : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F (y : F) = 1 := by
        intro v
        by_cases hv : v ∈ S
        · have h : WithZero.log (v.valuation F (y : F)) = 0 :=
            congrFun (LinearMap.mem_ker.1 hx) ⟨v, hv⟩
          have hne : v.valuation F (y : F) ≠ 0 := by simp
          rw [← WithZero.exp_log hne, h, WithZero.exp_zero]
        · exact (mem_sUnits F S _).1 (Additive.toMul x).2 v hv
      obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F (y : F)
        (fun v => (hall v).le)
      obtain ⟨b, hb⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F (y : F)⁻¹
        (fun v => by rw [map_inv₀, hall v, inv_one])
      have hab : a * b = 1 := by
        apply IsFractionRing.injective (𝓞 F) F
        rw [map_mul, ha, hb, map_one, mul_inv_cancel₀ y.ne_zero]
      refine ⟨Additive.ofMul (Units.mkOfMulEqOne a b hab), ?_⟩
      apply Additive.toMul.injective
      apply Subtype.ext
      apply Units.ext
      exact ha
    · rintro _ ⟨u, rfl⟩
      rw [LinearMap.mem_ker]
      funext v
      change WithZero.log ((v : HeightOneSpectrum (𝓞 F)).valuation F
        (algebraMap (𝓞 F) F (Additive.toMul u : (𝓞 F)ˣ))) = 0
      rw [hunit, WithZero.log_one]
  have hinj : Function.Injective f := by
    intro a b hab
    apply Additive.toMul.injective
    apply Units.ext
    apply IsFractionRing.injective (𝓞 F) F
    exact congrArg (fun x : Additive (sUnits F S) => (((Additive.toMul x : sUnits F S) : Fˣ) : F)) hab
  have hfin : Module.Finite ℤ (Additive (sUnits F S)) :=
    Module.Finite.iff_addGroup_fg.2 (GroupFG.iff_add_fg.1 (sUnits_fg F S))
  have hrange : Module.finrank ℤ (LinearMap.range g) = S.card := by
    apply le_antisymm
    · refine (Submodule.finrank_le _).trans ?_
      simp
    · have key : ∀ v : S, ∃ c : ℤ, c ≠ 0 ∧ Pi.single v c ∈ LinearMap.range g := by
        intro v
        obtain ⟨a, ha0, hav, haw⟩ := exists_mem_only F v
        have ha0' : algebraMap (𝓞 F) F a ≠ 0 := by simpa using ha0
        have hw : ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v →
            w.valuation F (algebraMap (𝓞 F) F a) = 1 := fun w hw =>
          (HeightOneSpectrum.valuation_eq_one_iff_notMem w).2 (haw w hw)
        refine ⟨WithZero.log ((v : HeightOneSpectrum (𝓞 F)).valuation F (algebraMap (𝓞 F) F a)),
          ?_, Additive.ofMul ⟨Units.mk0 _ ha0', (mem_sUnits F S _).2 fun w hwS =>
            hw w (fun e => hwS (e ▸ v.2))⟩, ?_⟩
        · intro h0
          have hne : (v : HeightOneSpectrum (𝓞 F)).valuation F (algebraMap (𝓞 F) F a) ≠ 0 := by
            simpa using ha0
          have h1 : (v : HeightOneSpectrum (𝓞 F)).valuation F (algebraMap (𝓞 F) F a) = 1 := by
            rw [← WithZero.exp_log hne, h0, WithZero.exp_zero]
          exact (HeightOneSpectrum.valuation_eq_one_iff_notMem _).1 h1 hav
        · funext w
          change WithZero.log ((w : HeightOneSpectrum (𝓞 F)).valuation F
            (algebraMap (𝓞 F) F a)) = _
          by_cases hwv : w = v
          · subst hwv; simp
          · rw [Pi.single_eq_of_ne hwv, hw w (fun e => hwv (Subtype.ext e)), WithZero.log_one]
      choose c hc0 hc using key
      have hli : LinearIndependent ℤ (fun v : S => (⟨Pi.single v (c v), hc v⟩ : LinearMap.range g)) :=
        LinearIndependent.of_comp (LinearMap.range g).subtype
          (Pi.linearIndependent_single_of_ne_zero hc0)
      simpa using hli.fintype_card_le_finrank
  have h1 := Submodule.finrank_quotient_add_finrank (LinearMap.ker g)
  rw [g.quotKerEquivRange.finrank_eq, hrange, hker, LinearMap.finrank_range_of_inj hinj,
    NumberField.Units.finrank_eq, NumberField.Units.rank] at h1
  have h2 : 0 < Fintype.card (InfinitePlace F) := Fintype.card_pos
  omega

end GlobalTheory.QNorm

end
