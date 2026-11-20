import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNoetherianRingAdicCompletionOfNoetherian

open IsLocalRing UpperTheory.V.Alg

/- English proof (translation)
Rewrite using `[← Submodule.restrictScalars_mem A, ← Ideal.smul_top_eq_map, AdicCompletion.pow_smul_top_eq_ker_eval fg]`. Both sides reduce to the same expression.
-/
private theorem mem_pow_iff {A : Type} [CommRing A] (I : Ideal A) (fg : I.FG) (n : ℕ) (y : AdicCompletion I A) :
    y ∈ (I ^ n).map (algebraMap A (AdicCompletion I A)) ↔ AdicCompletion.eval I A n y = 0 := by
  rw [← Submodule.restrictScalars_mem A, ← Ideal.smul_top_eq_map, AdicCompletion.pow_smul_top_eq_ker_eval fg]
  rfl

/- English proof (translation)
Take `⟨z, hz⟩` from `Submodule.Quotient.mk_surjective _ (AdicCompletion.eval I A n y)`. Use `⟨z, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_pow_iff I fg]`. Express the relevant statement in the definitionally equal form `AdicCompletion.eval I A n (y - AdicCompletion.of I A z) = 0`. Rewrite using `[map_sub, AdicCompletion.eval_of, Submodule.mkQ_apply, hz, sub_self]`.
-/
private theorem dense {A : Type} [CommRing A] (I : Ideal A) (fg : I.FG) (n : ℕ) (y : AdicCompletion I A) :
    ∃ z : A, y - algebraMap A (AdicCompletion I A) z ∈ (I ^ n).map (algebraMap A (AdicCompletion I A)) := by
  obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval I A n y)
  refine ⟨z, ?_⟩
  rw [mem_pow_iff I fg]
  change AdicCompletion.eval I A n (y - AdicCompletion.of I A z) = 0
  rw [map_sub, AdicCompletion.eval_of, Submodule.mkQ_apply, hz, sub_self]

/- English proof (translation)
Establish `hle : ∀ n, I ^ n ≤ (J ^ n).comap g` using `fun n => (Ideal.pow_right_mono hg n).trans (Ideal.le_comap_pow _ n)`. Use `⟨IsAdicComplete.liftRingHom J (fun n => (Ideal.quotientMap (J ^ n) g (hle n)).comp (AdicCompletion.evalₐ I n : AdicCompletion I A →+* A ⧸ I ^ n)) (fun {m n} hmn => RingHom.ext fun y => ?_), fun z => ?_⟩` and prove the remaining obligations. Proceed by induction on `y using AdicCompletion.induction_on with | _ s => ?_`. Simplify using `only [RingHom.comp_apply, RingHom.coe_coe, AdicCompletion.evalₐ_mk, Ideal.quotientMap_mk]`. Conclude with `congrArg (Ideal.quotientMap (J ^ m) g (hle m)) (AdicCompletion.Ideal.mk_eq_mk I hmn s)`.

Use `IsHausdorff.eq_iff_smodEq (I := J) |>.2 fun n => ?_` and prove the remaining obligations. Rewrite using `[SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq, IsAdicComplete.mk_liftRingHom]`. Use `show Ideal.quotientMap (J ^ n) g (hle n) (AdicCompletion.evalₐ I n (AdicCompletion.of I A z)) = _`. Rewrite using `[AdicCompletion.evalₐ_of, Ideal.quotientMap_mk]`.
-/
private theorem lift_ex {A R : Type} [CommRing A] [CommRing R] (I : Ideal A) (J : Ideal R) [IsAdicComplete J R]
    (g : A →+* R) (hg : I ≤ J.comap g) :
    ∃ h : AdicCompletion I A →+* R, ∀ z, h (algebraMap A _ z) = g z := by
  have hle : ∀ n, I ^ n ≤ (J ^ n).comap g := fun n => (Ideal.pow_right_mono hg n).trans (Ideal.le_comap_pow _ n)
  refine ⟨IsAdicComplete.liftRingHom J
    (fun n => (Ideal.quotientMap (J ^ n) g (hle n)).comp (AdicCompletion.evalₐ I n : AdicCompletion I A →+* A ⧸ I ^ n))
    (fun {m n} hmn => RingHom.ext fun y => ?_), fun z => ?_⟩
  · induction y using AdicCompletion.induction_on with | _ s => ?_
    simp only [RingHom.comp_apply, RingHom.coe_coe, AdicCompletion.evalₐ_mk, Ideal.quotientMap_mk]
    exact congrArg (Ideal.quotientMap (J ^ m) g (hle m)) (AdicCompletion.Ideal.mk_eq_mk I hmn s)
  · refine IsHausdorff.eq_iff_smodEq (I := J) |>.2 fun n => ?_
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq, IsAdicComplete.mk_liftRingHom]
    show Ideal.quotientMap (J ^ n) g (hle n) (AdicCompletion.evalₐ I n (AdicCompletion.of I A z)) = _
    rw [AdicCompletion.evalₐ_of, Ideal.quotientMap_mk]

/- English proof (translation)
Establish `hx : ∀ z : A, ∃ c : Λ, z - algebraMap Λ A c ∈ RingHom.ker x` using `fun z => by`. Take `⟨c, hc⟩` from `residue_surjective (x z)`. Conclude with `⟨c, by rw [RingHom.mem_ker, map_sub, AlgHom.commutes, ← hc]; exact sub_self _⟩`. Establish `hs : Function.Surjective x` using `fun y => by`. Take `⟨c, rfl⟩` from `residue_surjective y`.

Conclude with `⟨algebraMap Λ A c, x.commutes c⟩`. Use `set I : Ideal A := RingHom.ker x with hI`. Use `haveI : I.IsMaximal := RingHom.ker_isMaximal_of_surjective x hs`. Establish `fg : I.FG` using `I.fg_of_isNoetherianRing`. Set `R` to `AdicCompletion I A`.

Use `haveI hmax := AdicCompletion.isMaximal_map_of_le I I le_rfl fg`. Use `haveI hc := AdicCompletion.isAdicComplete_self I fg`. Use `haveI : IsLocalRing R := isLocalRing_of_isAdicComplete_maximal (I.map (algebraMap A R))`. Use `haveI : IsNoetherianRing R := GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion _ _`. Establish `hm : maximalIdeal R = I.map (algebraMap A R)` using `(eq_maximalIdeal hmax).symm`.

Set `f : A →ₐ[Λ] R` to `IsScalarTower.toAlgHom Λ A R`. Establish `hf : ∀ z, f z = algebraMap A R z` using `fun _ => rfl`. Establish `hIm : ∀ z ∈ I, f z ∈ maximalIdeal R` using `fun z hz => hm ▸ Ideal.mem_map_of_mem _ hz`. Use `haveI hco : IsCO Λ R := { complete := hm ▸ hc isLocalHom := ⟨fun c hu => by`. Assume the negation of the conclusion as `hn`.

Establish `h0 : algebraMap Λ A c ∈ I`. Rewrite using `[RingHom.mem_ker, AlgHom.commutes]`. Conclude with `(residue_eq_zero_iff c).2 hn`. Establish `h1` using `hIm _ h0`. Rewrite `h1` using `[AlgHom.commutes]`.

Conclude with `h1 hu⟩`. Use `res_surj := fun y => by`. Take `⟨z, hz⟩` from `dense I fg 1 y`. Take `⟨c, hc⟩` from `hx z`. Use `⟨c, ?_⟩` and prove the remaining obligations.

Rewrite `hz` using `[pow_one, ← hm, ← hf]`. Establish `h1` using `add_mem hz (hIm _ hc)`. Rewrite using `[map_sub, AlgHom.commutes, sub_add_sub_cancel] at h1 }` and apply the resulting hypothesis. Use `⟨R, inferInstance, inferInstance, hco, f, RingHom.flat_algebraMap_iff.2 (AdicCompletion.flat_of_isNoetherian I), AlgHom.ext fun z => ?_, fun R' _ _ _ g hg => ?_⟩` and prove the remaining obligations. Take `⟨c, hc⟩` from `hx z`.

Establish `h1` using `(res_eq_zero_iff Λ R _).2 (hIm _ hc)`. Rewrite `hc` using `[RingHom.mem_ker, map_sub, AlgHom.commutes, sub_eq_zero]`. Rewrite `h1` using `[map_sub, AlgHom.commutes, map_sub, AlgHom.commutes, sub_eq_zero]`. Conclude with `h1.trans hc.symm`. Establish `hgI : I ≤ (maximalIdeal R').comap (g : A →+* R')` using `fun z hz => (res_eq_zero_iff Λ R' _).1 ((AlgHom.congr_fun hg z).trans hz)`.

Take `⟨h, hh⟩` from `lift_ex I (maximalIdeal R') (g : A →+* R') hgI`. Establish `uniq : ∀ h₁ h₂ : R →ₐ[Λ] R', h₁.comp f = g → h₂.comp f = g → h₁ = h₂` using `fun h₁ h₂ e₁ e₂ => by`. Use `AlgHom.ext fun y => IsHausdorff.eq_iff_smodEq (I := maximalIdeal R') |>.2 fun n => ?_` and prove the remaining obligations. Take `⟨z, hz⟩` from `dense I fg n y`. Establish `k : ∀ φ : R →ₐ[Λ] R', φ.comp f = g → φ y - g z ∈ maximalIdeal R' ^ n` using `fun φ e => by`.

Establish `hle : (I ^ n).map (algebraMap A R) ≤ (maximalIdeal R' ^ n).comap (φ : R →+* R')`. Rewrite using `[Ideal.map_le_iff_le_comap, Ideal.comap_comap]`. Establish `e' : (φ : R →+* R').comp (algebraMap A R) = (g : A →+* R')` using `RingHom.ext fun w => AlgHom.congr_fun e w`. Rewrite using `[e']`. Conclude with `(Ideal.pow_right_mono hgI n).trans (Ideal.le_comap_pow _ n)`.

Establish `h1 : φ (y - f z) ∈ maximalIdeal R' ^ n` using `hle hz`. Rewrite `h1` using `[map_sub, ← AlgHom.comp_apply φ f, e]`. Then use the resulting hypothesis. Rewrite using `[SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]`. Simplify using `using sub_mem (k h₁ e₁) (k h₂ e₂)`. Set `h' : R →ₐ[Λ] R'` to `{ h with commutes' := fun c => (hh (algebraMap Λ A c)).trans (g.commutes c) }`.

Establish `e : h'.comp f = g` using `AlgHom.ext hh`. Conclude with `⟨h', e, fun h₁ e₁ => uniq _ _ e₁ e⟩`.
-/
theorem UpperTheory.V.Ws.cmplPt {Λ A : Type} [CommRing Λ] [IsLocalRing Λ] [CommRing A] [Algebra Λ A] [IsNoetherianRing A]
    (x : A →ₐ[Λ] ResidueField Λ) :
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra Λ R) (_ : IsCO Λ R) (f : A →ₐ[Λ] R),
      (f : A →+* R).Flat ∧ (res Λ R).comp f = x ∧
      ∀ (R' : Type) [CommRing R'] [Algebra Λ R'] [IsCO Λ R'] (g : A →ₐ[Λ] R'), (res Λ R').comp g = x →
        ∃! h : R →ₐ[Λ] R', h.comp f = g := by
  have hx : ∀ z : A, ∃ c : Λ, z - algebraMap Λ A c ∈ RingHom.ker x := fun z => by
    obtain ⟨c, hc⟩ := residue_surjective (x z)
    exact ⟨c, by rw [RingHom.mem_ker, map_sub, AlgHom.commutes, ← hc]; exact sub_self _⟩
  have hs : Function.Surjective x := fun y => by
    obtain ⟨c, rfl⟩ := residue_surjective y
    exact ⟨algebraMap Λ A c, x.commutes c⟩
  set I : Ideal A := RingHom.ker x with hI
  haveI : I.IsMaximal := RingHom.ker_isMaximal_of_surjective x hs
  have fg : I.FG := I.fg_of_isNoetherianRing
  let R := AdicCompletion I A
  haveI hmax := AdicCompletion.isMaximal_map_of_le I I le_rfl fg
  haveI hc := AdicCompletion.isAdicComplete_self I fg
  haveI : IsLocalRing R := isLocalRing_of_isAdicComplete_maximal (I.map (algebraMap A R))
  haveI : IsNoetherianRing R := GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion _ _
  have hm : maximalIdeal R = I.map (algebraMap A R) := (eq_maximalIdeal hmax).symm
  let f : A →ₐ[Λ] R := IsScalarTower.toAlgHom Λ A R
  have hf : ∀ z, f z = algebraMap A R z := fun _ => rfl
  have hIm : ∀ z ∈ I, f z ∈ maximalIdeal R := fun z hz => hm ▸ Ideal.mem_map_of_mem _ hz
  haveI hco : IsCO Λ R :=
    { complete := hm ▸ hc
      isLocalHom := ⟨fun c hu => by
        by_contra hn
        have h0 : algebraMap Λ A c ∈ I := by
          rw [RingHom.mem_ker, AlgHom.commutes]
          exact (residue_eq_zero_iff c).2 hn
        have h1 := hIm _ h0
        rw [AlgHom.commutes] at h1
        exact h1 hu⟩
      res_surj := fun y => by
        obtain ⟨z, hz⟩ := dense I fg 1 y
        obtain ⟨c, hc⟩ := hx z
        refine ⟨c, ?_⟩
        rw [pow_one, ← hm, ← hf] at hz
        have h1 := add_mem hz (hIm _ hc)
        rwa [map_sub, AlgHom.commutes, sub_add_sub_cancel] at h1 }
  refine ⟨R, inferInstance, inferInstance, hco, f,
    RingHom.flat_algebraMap_iff.2 (AdicCompletion.flat_of_isNoetherian I), AlgHom.ext fun z => ?_, fun R' _ _ _ g hg => ?_⟩
  · obtain ⟨c, hc⟩ := hx z
    have h1 := (res_eq_zero_iff Λ R _).2 (hIm _ hc)
    rw [RingHom.mem_ker, map_sub, AlgHom.commutes, sub_eq_zero] at hc
    rw [map_sub, AlgHom.commutes, map_sub, AlgHom.commutes, sub_eq_zero] at h1
    exact h1.trans hc.symm
  · have hgI : I ≤ (maximalIdeal R').comap (g : A →+* R') := fun z hz =>
      (res_eq_zero_iff Λ R' _).1 ((AlgHom.congr_fun hg z).trans hz)
    obtain ⟨h, hh⟩ := lift_ex I (maximalIdeal R') (g : A →+* R') hgI
    have uniq : ∀ h₁ h₂ : R →ₐ[Λ] R', h₁.comp f = g → h₂.comp f = g → h₁ = h₂ := fun h₁ h₂ e₁ e₂ => by
      refine AlgHom.ext fun y => IsHausdorff.eq_iff_smodEq (I := maximalIdeal R') |>.2 fun n => ?_
      obtain ⟨z, hz⟩ := dense I fg n y
      have k : ∀ φ : R →ₐ[Λ] R', φ.comp f = g → φ y - g z ∈ maximalIdeal R' ^ n := fun φ e => by
        have hle : (I ^ n).map (algebraMap A R) ≤ (maximalIdeal R' ^ n).comap (φ : R →+* R') := by
          rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap]
          have e' : (φ : R →+* R').comp (algebraMap A R) = (g : A →+* R') := RingHom.ext fun w => AlgHom.congr_fun e w
          rw [e']
          exact (Ideal.pow_right_mono hgI n).trans (Ideal.le_comap_pow _ n)
        have h1 : φ (y - f z) ∈ maximalIdeal R' ^ n := hle hz
        rwa [map_sub, ← AlgHom.comp_apply φ f, e] at h1
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
      simpa using sub_mem (k h₁ e₁) (k h₂ e₂)
    let h' : R →ₐ[Λ] R' := { h with commutes' := fun c => (hh (algebraMap Λ A c)).trans (g.commutes c) }
    have e : h'.comp f = g := AlgHom.ext hh
    exact ⟨h', e, fun h₁ e₁ => uniq _ _ e₁ e⟩
