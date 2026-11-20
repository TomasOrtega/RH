import Development.EtaleCohomology.EtaleSheaves.TwistTensorRestriction

noncomputable section

namespace LateralTheory.E.BaerFlatZModCriterion

open TensorProduct

section General

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/- English proof (translation)
Set `f : R →ₗ[R] R` to `LinearMap.toSpanSingleton R R b`. Establish `hker : LinearMap.ker f ≤ LinearMap.ker (LinearMap.toSpanSingleton R M m)`. Introduce `x hx`. Simplify using `only [LinearMap.mem_ker, f, LinearMap.toSpanSingleton_apply, smul_eq_mul] at hx ⊢`. Take `⟨s, rfl⟩` from `hab x (by rw [mul_comm]; exact hx)`.

Rewrite using `[mul_comm, mul_smul, hm, smul_zero]`. Set `g : LinearMap.range f →ₗ[R] M` to `(LinearMap.ker f).liftQ (LinearMap.toSpanSingleton R M m) hker ∘ₗ f.quotKerEquivRange.symm.toLinearMap`. Take `⟨g', hg'⟩` from `hB (LinearMap.range f) g`. Use `⟨g' 1, ?_⟩` and prove the remaining obligations. Establish `h1 : f 1 = b` using `by simp [f]`.

Establish `hmem : b ∈ LinearMap.range f` using `⟨1, h1⟩`. Use `hg' b hmem` as an intermediate fact. Establish `hg : g ⟨b, hmem⟩ = m`. Establish `e : (⟨b, hmem⟩ : LinearMap.range f) = ⟨f 1, LinearMap.mem_range_self f 1⟩` using `Subtype.ext h1.symm`. Rewrite using `[e]`.

Simplify using `only [g, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearMap.quotKerEquivRange_symm_apply_image]`. Rewrite using `[Submodule.mkQ_apply, Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply, one_smul]`. Rewrite using `[← hg, ← this, ← map_smul, smul_eq_mul, mul_one]`.
-/
theorem exists_eq_smul_of_baer (hB : Module.Baer R M) {a b : R}
    (hab : ∀ r, b * r = 0 → ∃ s, r = a * s) {m : M} (hm : a • m = 0) : ∃ m' : M, m = b • m' := by
  let f : R →ₗ[R] R := LinearMap.toSpanSingleton R R b
  have hker : LinearMap.ker f ≤ LinearMap.ker (LinearMap.toSpanSingleton R M m) := by
    intro x hx
    simp only [LinearMap.mem_ker, f, LinearMap.toSpanSingleton_apply, smul_eq_mul] at hx ⊢
    obtain ⟨s, rfl⟩ := hab x (by rw [mul_comm]; exact hx)
    rw [mul_comm, mul_smul, hm, smul_zero]
  let g : LinearMap.range f →ₗ[R] M :=
    (LinearMap.ker f).liftQ (LinearMap.toSpanSingleton R M m) hker ∘ₗ f.quotKerEquivRange.symm.toLinearMap
  obtain ⟨g', hg'⟩ := hB (LinearMap.range f) g
  refine ⟨g' 1, ?_⟩
  have h1 : f 1 = b := by simp [f]
  have hmem : b ∈ LinearMap.range f := ⟨1, h1⟩
  have := hg' b hmem
  have hg : g ⟨b, hmem⟩ = m := by
    have e : (⟨b, hmem⟩ : LinearMap.range f) = ⟨f 1, LinearMap.mem_range_self f 1⟩ := Subtype.ext h1.symm
    rw [e]
    simp only [g, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearMap.quotKerEquivRange_symm_apply_image]
    rw [Submodule.mkQ_apply, Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply, one_smul]
  rw [← hg, ← this, ← map_smul, smul_eq_mul, mul_one]

/- English proof (translation)
Rewrite using `[Module.Flat.iff_lift_lsmul_comp_subtype_injective]`. Introduce `I _`. Take `⟨a, ha⟩` from `Submodule.IsPrincipal.principal I`. Establish `haI : a ∈ I` using `by rw [ha]; exact Submodule.mem_span_singleton_self a`. Establish `pure : ∀ x : I ⊗[R] M, ∃ m : M, x = (⟨a, haI⟩ : I) ⊗ₜ m`.

Introduce `x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, by rw [tmul_zero]⟩`. Consider the case `tmul y n`. Take `⟨c, hc⟩` from `Submodule.mem_span_singleton.mp (by rw [← ha]; exact y.2)`.

Use `⟨c • n, ?_⟩` and prove the remaining obligations. Rewrite using `[← smul_tmul]`. Use `congr 1`. Conclude with `Subtype.ext hc.symm`. Consider the case `add x y hx hy`.

Take `⟨m1, rfl⟩` from `hx`. Take `⟨m2, rfl⟩` from `hy`. Conclude with `⟨m1 + m2, by rw [tmul_add]⟩`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`.

Take `⟨m, rfl⟩` from `pure x`. Simplify using `only [lift.tmul, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype, LinearMap.lsmul_apply] at hx`. Take `⟨b, hab, hb⟩` from `hA a`. Take `⟨m', rfl⟩` from `exists_eq_smul_of_baer hB hb hx`. Rewrite using `[← smul_tmul]`.

Establish `: b • (⟨a, haI⟩ : I) = 0` using `Subtype.ext (by simp [smul_eq_mul, mul_comm, hab])`. Rewrite using `[this, zero_tmul]`.
-/
theorem flat_of_baer [IsPrincipalIdealRing R]
    (hA : ∀ a : R, ∃ b, a * b = 0 ∧ ∀ r, b * r = 0 → ∃ s, r = a * s) (hB : Module.Baer R M) :
    Module.Flat R M := by
  rw [Module.Flat.iff_lift_lsmul_comp_subtype_injective]
  intro I _
  obtain ⟨a, ha⟩ := Submodule.IsPrincipal.principal I
  have haI : a ∈ I := by rw [ha]; exact Submodule.mem_span_singleton_self a
  have pure : ∀ x : I ⊗[R] M, ∃ m : M, x = (⟨a, haI⟩ : I) ⊗ₜ m := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, by rw [tmul_zero]⟩
    | tmul y n =>
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (by rw [← ha]; exact y.2)
      refine ⟨c • n, ?_⟩
      rw [← smul_tmul]
      congr 1
      exact Subtype.ext hc.symm
    | add x y hx hy =>
      obtain ⟨m1, rfl⟩ := hx
      obtain ⟨m2, rfl⟩ := hy
      exact ⟨m1 + m2, by rw [tmul_add]⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨m, rfl⟩ := pure x
  simp only [lift.tmul, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
    LinearMap.lsmul_apply] at hx
  obtain ⟨b, hab, hb⟩ := hA a
  obtain ⟨m', rfl⟩ := exists_eq_smul_of_baer hB hb hx
  rw [← smul_tmul]
  have : b • (⟨a, haI⟩ : I) = 0 := Subtype.ext (by simp [smul_eq_mul, mul_comm, hab])
  rw [this, zero_tmul]

end General

section ZModPart

/- English proof (translation)
Take `⟨n, hn⟩ : ∃ n, n = a.val` from `⟨_, rfl⟩`. Take `⟨g, hg⟩ : ∃ g, g = Nat.gcd n q` from `⟨_, rfl⟩`. Establish `hq : 0 < q` using `NeZero.pos q`. Establish `hg0 : 0 < g` using `hg ▸ Nat.gcd_pos_of_pos_right _ hq`. Establish `hgq : g ∣ q` using `hg ▸ Nat.gcd_dvd_right n q`.

Establish `hgn : g ∣ n` using `hg ▸ Nat.gcd_dvd_left n q`. Establish `hqg : 0 < q / g` using `Nat.div_pos (Nat.le_of_dvd hq hgq) hg0`. Establish `ha : a = (n : ZMod q)` using `by rw [hn, ZMod.natCast_zmod_val]`. Use `⟨((q / g : ℕ) : ZMod q), ?_, ?_⟩` and prove the remaining obligations. Take `⟨k, hk⟩` from `hgn`.

Rewrite using `[ha, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]`. Use `⟨k, ?_⟩` and prove the remaining obligations. Rewrite using `[hk, mul_comm g k, mul_assoc, Nat.mul_div_cancel' hgq, mul_comm]`. Introduce `r hr`. Establish `hr' : q ∣ (q / g) * r.val`.

Rewrite using `[← ZMod.natCast_eq_zero_iff, Nat.cast_mul, ZMod.natCast_zmod_val]`. Conclude with `hr`. Establish `hdiv : g ∣ r.val`. Establish `h2 : (q / g) * g ∣ (q / g) * r.val` using `by rw [Nat.div_mul_cancel hgq]; exact hr'`. Conclude with `Nat.dvd_of_mul_dvd_mul_left hqg h2`.

Take `⟨t, ht⟩` from `hdiv`. Establish `hz` using `Nat.gcd_eq_gcd_ab n q`. Establish `hgz : (g : ZMod q) = a * (Nat.gcdA n q : ZMod q)`. Use `congrArg (Int.cast : ℤ → ZMod q) hz` as an intermediate fact. Move the coercions through the operations in `at this`.

Rewrite `this` using `[ZMod.natCast_self, zero_mul, add_zero, ← hg]`. Rewrite using `[this, ha]`. Use `⟨(Nat.gcdA n q : ZMod q) * (t : ZMod q), ?_⟩` and prove the remaining obligations. Rewrite using `[← ZMod.natCast_zmod_val r, ht, Nat.cast_mul, hgz, mul_assoc]`.
-/
theorem zmod_ann (q : ℕ) [NeZero q] (a : ZMod q) :
    ∃ b : ZMod q, a * b = 0 ∧ ∀ r : ZMod q, b * r = 0 → ∃ s, r = a * s := by
  obtain ⟨n, hn⟩ : ∃ n, n = a.val := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g, g = Nat.gcd n q := ⟨_, rfl⟩
  have hq : 0 < q := NeZero.pos q
  have hg0 : 0 < g := hg ▸ Nat.gcd_pos_of_pos_right _ hq
  have hgq : g ∣ q := hg ▸ Nat.gcd_dvd_right n q
  have hgn : g ∣ n := hg ▸ Nat.gcd_dvd_left n q
  have hqg : 0 < q / g := Nat.div_pos (Nat.le_of_dvd hq hgq) hg0
  have ha : a = (n : ZMod q) := by rw [hn, ZMod.natCast_zmod_val]
  refine ⟨((q / g : ℕ) : ZMod q), ?_, ?_⟩
  · obtain ⟨k, hk⟩ := hgn
    rw [ha, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
    refine ⟨k, ?_⟩
    rw [hk, mul_comm g k, mul_assoc, Nat.mul_div_cancel' hgq, mul_comm]
  · intro r hr
    have hr' : q ∣ (q / g) * r.val := by
      rw [← ZMod.natCast_eq_zero_iff, Nat.cast_mul, ZMod.natCast_zmod_val]
      exact hr
    have hdiv : g ∣ r.val := by
      have h2 : (q / g) * g ∣ (q / g) * r.val := by rw [Nat.div_mul_cancel hgq]; exact hr'
      exact Nat.dvd_of_mul_dvd_mul_left hqg h2
    obtain ⟨t, ht⟩ := hdiv
    have hz := Nat.gcd_eq_gcd_ab n q
    have hgz : (g : ZMod q) = a * (Nat.gcdA n q : ZMod q) := by
      have := congrArg (Int.cast : ℤ → ZMod q) hz
      push_cast at this
      rw [ZMod.natCast_self, zero_mul, add_zero, ← hg] at this
      rw [this, ha]
    refine ⟨(Nat.gcdA n q : ZMod q) * (t : ZMod q), ?_⟩
    rw [← ZMod.natCast_zmod_val r, ht, Nat.cast_mul, hgz, mul_assoc]

end ZModPart

end LateralTheory.E.BaerFlatZModCriterion

open LateralTheory.E.ZModFlatnessFromBaerCriterion LateralTheory.E.BaerFlatZModCriterion in
/- English proof (translation)
Introduce `q _ M _ _ hinj`. Establish `: IsPrincipalIdealRing (ZMod q)` using `IsPrincipalIdealRing.of_surjective (Int.castRingHom (ZMod q)) ZMod.intCast_surjective`. Establish `: IsPrincipalIdealRing (ULift.{1} (ZMod q))` using `IsPrincipalIdealRing.of_surjective (ULift.ringEquiv (R := ZMod q)).symm (ULift.ringEquiv (R := ZMod q)).symm.surjective`. Use `flat_of_baer (fun a => ?_) (Module.Baer.of_injective hinj)` and prove the remaining obligations. Take `⟨b, hab, hb⟩` from `zmod_ann q a.down`.

Use `⟨ULift.up b, ULift.ext _ _ hab, fun r hr => ?_⟩` and prove the remaining obligations. Take `⟨s, hs⟩` from `hb r.down (congrArg ULift.down hr)`. Conclude with `⟨ULift.up s, ULift.ext _ _ hs⟩`.
-/
theorem LateralTheory.E.ZModFlatnessFromBaerCriterion.LeafInjFlatZMod_of : LeafInjFlatZMod := by
  intro q _ M _ _ hinj
  have : IsPrincipalIdealRing (ZMod q) :=
    IsPrincipalIdealRing.of_surjective (Int.castRingHom (ZMod q)) ZMod.intCast_surjective
  have : IsPrincipalIdealRing (ULift.{1} (ZMod q)) :=
    IsPrincipalIdealRing.of_surjective (ULift.ringEquiv (R := ZMod q)).symm
      (ULift.ringEquiv (R := ZMod q)).symm.surjective
  refine flat_of_baer (fun a => ?_) (Module.Baer.of_injective hinj)
  obtain ⟨b, hab, hb⟩ := zmod_ann q a.down
  refine ⟨ULift.up b, ULift.ext _ _ hab, fun r hr => ?_⟩
  obtain ⟨s, hs⟩ := hb r.down (congrArg ULift.down hr)
  exact ⟨ULift.up s, ULift.ext _ _ hs⟩
