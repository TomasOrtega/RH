import Development.EtaleCohomology.TateTwists.EtaleKInjectiveExtensionAlongQuasiIsoFromSingle

namespace LateralTheory.EtaleFoundations.QFFlat

universe u v

open TensorProduct

/- English proof (translation)
Establish `hq : 0 < q` using `Nat.pos_of_ne_zero (NeZero.ne q)`. Use `set n := a.val with hn`. Use `set g := Nat.gcd n q with hg`. Establish `hgq : g ∣ q` using `Nat.gcd_dvd_right n q`. Establish `hgn : g ∣ n` using `Nat.gcd_dvd_left n q`.

Establish `hgpos : 0 < g` using `Nat.gcd_pos_of_pos_right n hq`. Establish `ha : (n : ZMod q) = a` using `ZMod.natCast_zmod_val a`. Use `⟨((q / g : ℕ) : ZMod q), ?_, fun r hr => ?_⟩` and prove the remaining obligations. Rewrite using `[← ha, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]`. Take `⟨t, ht⟩` from `hgn`.

Use `⟨t, ?_⟩` and prove the remaining obligations. Rewrite using `[ht, ← mul_assoc, Nat.div_mul_cancel hgq]`. Establish `hr' : (r.val : ZMod q) = r` using `ZMod.natCast_zmod_val r`. Rewrite `hr` using `[← hr', ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]`. Establish `hqg : 0 < q / g` using `Nat.div_pos (Nat.le_of_dvd hq hgq) hgpos`.

Establish `hdiv : g ∣ r.val`. Establish `h1 : g * (q / g) ∣ r.val * (q / g)` using `by rwa [Nat.mul_div_cancel' hgq]`. Conclude with `Nat.dvd_of_mul_dvd_mul_right hqg h1`. Take `⟨j, hj⟩` from `hdiv`. Establish `hbez : ((g : ℤ) : ZMod q) = (n : ZMod q) * ((Nat.gcdA n q : ℤ) : ZMod q)`.

Rewrite using `[hg, Nat.gcd_eq_gcd_ab n q]`. Use `push_cast`. Simplify using the standard rewrite rules. Use `⟨((Nat.gcdA n q : ℤ) : ZMod q) * (j : ZMod q), ?_⟩` and prove the remaining obligations. Rewrite using `[← hr', hj, ← ha]`.

Move the coercions through the operations in `at hbez ⊢`. Rewrite using `[hbez]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem zmod_P (q : ℕ) [NeZero q] (a : ZMod q) :
    ∃ b : ZMod q, b * a = 0 ∧ ∀ r : ZMod q, r * b = 0 → ∃ c, c * a = r := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  set n := a.val with hn
  set g := Nat.gcd n q with hg
  have hgq : g ∣ q := Nat.gcd_dvd_right n q
  have hgn : g ∣ n := Nat.gcd_dvd_left n q
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_right n hq
  have ha : (n : ZMod q) = a := ZMod.natCast_zmod_val a
  refine ⟨((q / g : ℕ) : ZMod q), ?_, fun r hr => ?_⟩
  · rw [← ha, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
    obtain ⟨t, ht⟩ := hgn
    refine ⟨t, ?_⟩
    rw [ht, ← mul_assoc, Nat.div_mul_cancel hgq]
  · have hr' : (r.val : ZMod q) = r := ZMod.natCast_zmod_val r
    rw [← hr', ← Nat.cast_mul, ZMod.natCast_eq_zero_iff] at hr
    have hqg : 0 < q / g := Nat.div_pos (Nat.le_of_dvd hq hgq) hgpos
    have hdiv : g ∣ r.val := by
      have h1 : g * (q / g) ∣ r.val * (q / g) := by rwa [Nat.mul_div_cancel' hgq]
      exact Nat.dvd_of_mul_dvd_mul_right hqg h1
    obtain ⟨j, hj⟩ := hdiv
    have hbez : ((g : ℤ) : ZMod q) = (n : ZMod q) * ((Nat.gcdA n q : ℤ) : ZMod q) := by
      rw [hg, Nat.gcd_eq_gcd_ab n q]
      push_cast
      simp
    refine ⟨((Nat.gcdA n q : ℤ) : ZMod q) * (j : ZMod q), ?_⟩
    rw [← hr', hj, ← ha]
    push_cast at hbez ⊢
    rw [hbez]
    ring

/- English proof (translation)
Take `⟨b, hb, h⟩` from `zmod_P q a.down`. Use `⟨ULift.up b, ULift.ext _ _ hb, fun r hr => ?_⟩` and prove the remaining obligations. Take `⟨c, hc⟩` from `h r.down (congrArg ULift.down hr)`. Conclude with `⟨ULift.up c, ULift.ext _ _ hc⟩`.
-/
theorem ulift_P (q : ℕ) [NeZero q] (a : ULift.{1} (ZMod q)) :
    ∃ b : ULift.{1} (ZMod q), b * a = 0 ∧ ∀ r : ULift.{1} (ZMod q), r * b = 0 → ∃ c, c * a = r := by
  obtain ⟨b, hb, h⟩ := zmod_P q a.down
  refine ⟨ULift.up b, ULift.ext _ _ hb, fun r hr => ?_⟩
  obtain ⟨c, hc⟩ := h r.down (congrArg ULift.down hr)
  exact ⟨ULift.up c, ULift.ext _ _ hc⟩

/- English proof (translation)
Take `⟨b, hba, hb⟩` from `hP a`. Establish `wd : ∀ c c' : R, c * b = c' * b → c • m = c' • m`. Introduce `c c' hcc`. Take `⟨e, he⟩` from `hb (c - c') (by rw [sub_mul, hcc, sub_self])`. Rewrite using `[← sub_eq_zero, ← sub_smul, ← he, mul_smul, h, smul_zero]`.

Establish `hc : ∀ x : Ideal.span {b}, (Ideal.mem_span_singleton'.1 x.2).choose * b = x` using `fun x => (Ideal.mem_span_singleton'.1 x.2).choose_spec`. Set `g : Ideal.span {b} →ₗ[R] M` to `{ toFun := fun x => (Ideal.mem_span_singleton'.1 x.2).choose • m map_add' := fun x y => by`. Rewrite using `[← add_smul]`. Apply `wd` to reduce the goal to its premises. Rewrite using `[add_mul, hc, hc, hc, Submodule.coe_add]`.

Use the proof step `map_smul' := fun r x => by`. Rewrite using `[RingHom.id_apply, ← mul_smul]`. Apply `wd` to reduce the goal to its premises. Rewrite using `[mul_assoc, hc, hc, Submodule.coe_smul, smul_eq_mul] }`. Take `⟨G, hG⟩` from `Module.Baer.of_injective hM (Ideal.span {b}) g`.

Use `⟨b, G 1, hba, ?_⟩` and prove the remaining obligations. Establish `hbm : b ∈ Ideal.span {b}` using `Ideal.subset_span rfl`. Rewrite using `[← map_smul, smul_eq_mul, mul_one, hG b hbm]`. Express the relevant statement in the definitionally equal form `m = (Ideal.mem_span_singleton'.1 hbm).choose • m`. Use `conv_lhs => rw [← one_smul R m]`.

Apply `wd` to reduce the goal to its premises. Rewrite using `[hc ⟨b, hbm⟩, one_mul]`.
-/
theorem key {R : Type u} {M : Type v} [CommRing R] [Small.{v} R] [AddCommGroup M] [Module R M] (hM : Module.Injective R M)
    (hP : ∀ a : R, ∃ b : R, b * a = 0 ∧ ∀ r : R, r * b = 0 → ∃ c, c * a = r)
    (a : R) (m : M) (h : a • m = 0) : ∃ (b : R) (m' : M), b * a = 0 ∧ m = b • m' := by
  obtain ⟨b, hba, hb⟩ := hP a
  have wd : ∀ c c' : R, c * b = c' * b → c • m = c' • m := by
    intro c c' hcc
    obtain ⟨e, he⟩ := hb (c - c') (by rw [sub_mul, hcc, sub_self])
    rw [← sub_eq_zero, ← sub_smul, ← he, mul_smul, h, smul_zero]
  have hc : ∀ x : Ideal.span {b}, (Ideal.mem_span_singleton'.1 x.2).choose * b = x :=
    fun x => (Ideal.mem_span_singleton'.1 x.2).choose_spec
  let g : Ideal.span {b} →ₗ[R] M :=
    { toFun := fun x => (Ideal.mem_span_singleton'.1 x.2).choose • m
      map_add' := fun x y => by
        rw [← add_smul]
        apply wd
        rw [add_mul, hc, hc, hc, Submodule.coe_add]
      map_smul' := fun r x => by
        rw [RingHom.id_apply, ← mul_smul]
        apply wd
        rw [mul_assoc, hc, hc, Submodule.coe_smul, smul_eq_mul] }
  obtain ⟨G, hG⟩ := Module.Baer.of_injective hM (Ideal.span {b}) g
  refine ⟨b, G 1, hba, ?_⟩
  have hbm : b ∈ Ideal.span {b} := Ideal.subset_span rfl
  rw [← map_smul, smul_eq_mul, mul_one, hG b hbm]
  change m = (Ideal.mem_span_singleton'.1 hbm).choose • m
  conv_lhs => rw [← one_smul R m]
  apply wd
  rw [hc ⟨b, hbm⟩, one_mul]

/- English proof (translation)
Rewrite using `[Module.Flat.iff_lift_lsmul_comp_subtype_injective]`. Introduce `I _`. Take `⟨a, ha⟩` from `Submodule.IsPrincipal.principal I`. Establish `mem : a ∈ I` using `by rw [ha]; exact Submodule.mem_span_singleton_self a`. Establish `hrep : ∀ t : I ⊗[R] M, ∃ m : M, t = (⟨a, mem⟩ : I) ⊗ₜ m`.

Introduce `t`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `tmul x n`. Establish `hx : (x : R) ∈ Submodule.span R {a}` using `ha ▸ x.2`.

Take `⟨c, hc⟩` from `Submodule.mem_span_singleton.1 hx`. Use `⟨c • n, ?_⟩` and prove the remaining obligations. Rewrite using `[← smul_tmul]`. Use `congr 1`. Use `ext`.

Simplify using the standard rewrite rules. Rewrite using `[← hc, smul_eq_mul]`. Consider the case `add x y hx hy`. Take `⟨mx, rfl⟩` from `hx`. Take `⟨my, rfl⟩` from `hy`.

Conclude with `⟨mx + my, by rw [tmul_add]⟩`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `t ht`. Take `⟨m, rfl⟩` from `hrep t`. Establish `ham : a • m = 0` using `by simpa using ht`.

Take `⟨b, m', hba, rfl⟩` from `key hM hP a m ham`. Rewrite using `[← smul_tmul]`. Establish `h0 : b • (⟨a, mem⟩ : I) = 0` using `Subtype.ext (by simp [hba])`. Rewrite using `[h0, zero_tmul]`.
-/
theorem flat_of {R : Type u} {M : Type v} [CommRing R] [Small.{v} R] [IsPrincipalIdealRing R] [AddCommGroup M] [Module R M]
    (hM : Module.Injective R M)
    (hP : ∀ a : R, ∃ b : R, b * a = 0 ∧ ∀ r : R, r * b = 0 → ∃ c, c * a = r) : Module.Flat R M := by
  rw [Module.Flat.iff_lift_lsmul_comp_subtype_injective]
  intro I _
  obtain ⟨a, ha⟩ := Submodule.IsPrincipal.principal I
  have mem : a ∈ I := by rw [ha]; exact Submodule.mem_span_singleton_self a
  have hrep : ∀ t : I ⊗[R] M, ∃ m : M, t = (⟨a, mem⟩ : I) ⊗ₜ m := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul x n =>
      have hx : (x : R) ∈ Submodule.span R {a} := ha ▸ x.2
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hx
      refine ⟨c • n, ?_⟩
      rw [← smul_tmul]
      congr 1
      ext
      simp
      rw [← hc, smul_eq_mul]
    | add x y hx hy =>
      obtain ⟨mx, rfl⟩ := hx
      obtain ⟨my, rfl⟩ := hy
      exact ⟨mx + my, by rw [tmul_add]⟩
  rw [injective_iff_map_eq_zero]
  intro t ht
  obtain ⟨m, rfl⟩ := hrep t
  have ham : a • m = 0 := by simpa using ht
  obtain ⟨b, m', hba, rfl⟩ := key hM hP a m ham
  rw [← smul_tmul]
  have h0 : b • (⟨a, mem⟩ : I) = 0 := Subtype.ext (by simp [hba])
  rw [h0, zero_tmul]

end LateralTheory.EtaleFoundations.QFFlat

/- English proof (translation)
Introduce `q _ N _ _ hN`. Establish `: IsPrincipalIdealRing (ZMod q)` using `IsPrincipalIdealRing.of_surjective (Int.castRingHom (ZMod q)) ZMod.intCast_surjective`. Establish `: IsPrincipalIdealRing (ULift.{1} (ZMod q))` using `IsPrincipalIdealRing.of_surjective (ULift.ringEquiv (R := ZMod q)).symm (ULift.ringEquiv (R := ZMod q)).symm.surjective`. Conclude with `LateralTheory.EtaleFoundations.QFFlat.flat_of hN (LateralTheory.EtaleFoundations.QFFlat.ulift_P q)`.
-/
theorem LateralTheory.EtaleFoundations.zmod_injective_module_flat_holds : LateralTheory.EtaleFoundations.ZModInjectiveModuleFlat := by
  intro q _ N _ _ hN
  have : IsPrincipalIdealRing (ZMod q) :=
    IsPrincipalIdealRing.of_surjective (Int.castRingHom (ZMod q)) ZMod.intCast_surjective
  have : IsPrincipalIdealRing (ULift.{1} (ZMod q)) :=
    IsPrincipalIdealRing.of_surjective (ULift.ringEquiv (R := ZMod q)).symm
      (ULift.ringEquiv (R := ZMod q)).symm.surjective
  exact LateralTheory.EtaleFoundations.QFFlat.flat_of hN (LateralTheory.EtaleFoundations.QFFlat.ulift_P q)
