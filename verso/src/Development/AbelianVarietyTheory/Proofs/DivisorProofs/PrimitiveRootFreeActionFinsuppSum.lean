import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecEqZeroOfLoc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveRootPowUnitSubProdProperties
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.KummerSplit

noncomputable section

namespace GlobalTheory.EtC.FreeActSum

def rootUnit {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) : Aˣ :=
  Units.ofPowEqOne ζ.1 q ((GlobalTheory.EtC.PrimBasic.prim_basic q A).1 ζ) (NeZero.ne q)

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma rootUnit_val {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) :
    ((rootUnit ζ : Aˣ) : A) = ζ.1 := rfl

/- English proof (translation)
Rewrite using `[orderOf_eq_iff (NeZero.pos q)]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `ext`. Simplify using `[rootUnit_val, (GlobalTheory.EtC.PrimBasic.prim_basic q A).1 ζ]`. Introduce `m hmq hm0 h1`.

Establish `hne : ¬ m ≡ 0 [MOD q]`. Introduce `h`. Use `(Nat.modEq_zero_iff_dvd).1 h` as an intermediate fact. Conclude with `absurd (Nat.le_of_dvd hm0 this) (not_le.2 hmq)`. Establish `hu` using `(GlobalTheory.EtC.PrimBasic.prim_basic q A).2.2.1 ζ m 0 hne`.

Establish `h1' : ζ.1 ^ m = 1`. Use `congrArg (fun u : Aˣ => (u : A)) h1` as an intermediate fact. Simplify `this` using `[rootUnit_val]`. Rewrite `hu` using `[h1', pow_zero, sub_self]`. Conclude with `not_isUnit_zero hu`.
-/
lemma orderOf_rootUnit {q : ℕ} [NeZero q] {A : Type} [CommRing A] [Nontrivial A] (ζ : Prim q A) :
    orderOf (rootUnit ζ) = q := by
  rw [orderOf_eq_iff (NeZero.pos q)]
  refine ⟨?_, ?_⟩
  · ext; simp [rootUnit_val, (GlobalTheory.EtC.PrimBasic.prim_basic q A).1 ζ]
  · intro m hmq hm0 h1
    have hne : ¬ m ≡ 0 [MOD q] := by
      intro h
      have := (Nat.modEq_zero_iff_dvd).1 h
      exact absurd (Nat.le_of_dvd hm0 this) (not_le.2 hmq)
    have hu := (GlobalTheory.EtC.PrimBasic.prim_basic q A).2.2.1 ζ m 0 hne
    have h1' : ζ.1 ^ m = 1 := by
      have := congrArg (fun u : Aˣ => (u : A)) h1
      simpa [rootUnit_val] using this
    rw [h1', pow_zero, sub_self] at hu
    exact not_isUnit_zero hu

abbrev H {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) : Subgroup Aˣ :=
  Subgroup.zpowers (rootUnit ζ)

/- English proof (translation)
Rewrite using `[← QuotientGroup.eq]`. Simplify using the standard rewrite rules.
-/
lemma mem_H {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) (u : Aˣ) :
    ((QuotientGroup.mk u : Aˣ ⧸ H ζ).out)⁻¹ * u ∈ H ζ := by
  rw [← QuotientGroup.eq]
  simp

def expo {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) (u : Aˣ) : ℤ :=
  Classical.choose (Subgroup.mem_zpowers_iff.1 (mem_H ζ u))

/- English proof (translation)
The claim follows from `Classical.choose_spec (Subgroup.mem_zpowers_iff.1 (mem_H ζ u))`.
-/
lemma expo_spec {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) (u : Aˣ) :
    rootUnit ζ ^ expo ζ u = ((QuotientGroup.mk u : Aˣ ⧸ H ζ).out)⁻¹ * u :=
  Classical.choose_spec (Subgroup.mem_zpowers_iff.1 (mem_H ζ u))

def tau {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) (u : Aˣ) : ZMod q :=
  (expo ζ u : ZMod q)

/- English proof (translation)
Establish `hcls : (QuotientGroup.mk (rootUnit ζ ^ n * u) : Aˣ ⧸ H ζ) = QuotientGroup.mk u`. Rewrite using `[QuotientGroup.eq]`. Establish `: (rootUnit ζ ^ n * u)⁻¹ * u = (rootUnit ζ ^ n)⁻¹`. Rewrite using `[mul_inv_rev, mul_comm u⁻¹, mul_assoc, inv_mul_cancel, mul_one]`. Rewrite using `[this]`.

Conclude with `Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _)`. Establish `h1` using `expo_spec ζ (rootUnit ζ ^ n * u)`. Establish `h2` using `expo_spec ζ u`. Rewrite `h1` using `[hcls]`. Use `set r := ((QuotientGroup.mk u : Aˣ ⧸ H ζ).out)`.

Establish `key : rootUnit ζ ^ (expo ζ (rootUnit ζ ^ n * u) - (n : ℤ) - expo ζ u) = 1`. Rewrite using `[zpow_sub, zpow_sub, h1, h2, zpow_natCast]`. Simplify using `[mul_comm, mul_left_comm, mul_assoc]`. Rewrite `key` using `[← orderOf_dvd_iff_zpow_eq_one, orderOf_rootUnit]`. Unfold `tau`.

Use `(ZMod.intCast_zmod_eq_zero_iff_dvd _ q).2 key` as an intermediate fact. Move the coercions through the operations in `at this`. Take the linear combination `this`.
-/
lemma tau_mul {q : ℕ} [NeZero q] {A : Type} [CommRing A] [Nontrivial A] (ζ : Prim q A) (u : Aˣ) (n : ℕ) :
    tau ζ (rootUnit ζ ^ n * u) = tau ζ u + n := by
  have hcls : (QuotientGroup.mk (rootUnit ζ ^ n * u) : Aˣ ⧸ H ζ) = QuotientGroup.mk u := by
    rw [QuotientGroup.eq]
    have : (rootUnit ζ ^ n * u)⁻¹ * u = (rootUnit ζ ^ n)⁻¹ := by
      rw [mul_inv_rev, mul_comm u⁻¹, mul_assoc, inv_mul_cancel, mul_one]
    rw [this]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _)
  have h1 := expo_spec ζ (rootUnit ζ ^ n * u)
  have h2 := expo_spec ζ u
  rw [hcls] at h1
  set r := ((QuotientGroup.mk u : Aˣ ⧸ H ζ).out)
  have key : rootUnit ζ ^ (expo ζ (rootUnit ζ ^ n * u) - (n : ℤ) - expo ζ u) = 1 := by
    rw [zpow_sub, zpow_sub, h1, h2, zpow_natCast]
    simp [mul_comm, mul_left_comm, mul_assoc]
  rw [← orderOf_dvd_iff_zpow_eq_one, orderOf_rootUnit] at key
  unfold tau
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).2 key
  push_cast at this
  linear_combination this

end GlobalTheory.EtC.FreeActSum

namespace GlobalTheory.EtC.FreeActSum

/- English proof (translation)
Introduce `q _ A _ _ ζ ι s c a v w hw hsum`. Set `T : (Aˣ →₀ ULift.{1} (ZMod q)) →+ ZMod q` to `Finsupp.liftAddHom (fun u => (AddMonoidHom.mulRight (tau ζ u)).comp (AddEquiv.ulift.toAddMonoidHom))`. Establish `hT` using `congrArg T hsum`. Rewrite `hT` using `[map_sum, map_zero]`. Rewrite using `[← hT]`.

Use `Finset.sum_congr rfl (fun i hi => ?_)` and prove the remaining obligations. Establish `hwu : w i = rootUnit ζ ^ a i * v i` using `by ext; simp [rootUnit_val, hw i hi]`. Simplify using `only [T, map_sub, Finsupp.liftAddHom_apply_single, AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_mulRight]`. Rewrite using `[hwu, tau_mul]`. Use `show (c i).down * (a i : ZMod q) = (c i).down * (tau ζ (v i) + a i) - (c i).down * tau ζ (v i)`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem free_act_sum : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] [Nontrivial A] (ζ : Prim q A) (ι : Type) (s : Finset ι) (c : ι → ULift.{1} (ZMod q)) (a : ι → ℕ) (v w : ι → Aˣ), (∀ i ∈ s, (w i : A) = ζ.1 ^ a i * v i) → (∑ i ∈ s, (Finsupp.single (w i) (c i) - Finsupp.single (v i) (c i))) = 0 → ∑ i ∈ s, (c i).down * (a i : ZMod q) = 0 := by
  intro q _ A _ _ ζ ι s c a v w hw hsum
  let T : (Aˣ →₀ ULift.{1} (ZMod q)) →+ ZMod q :=
    Finsupp.liftAddHom (fun u => (AddMonoidHom.mulRight (tau ζ u)).comp (AddEquiv.ulift.toAddMonoidHom))
  have hT := congrArg T hsum
  rw [map_sum, map_zero] at hT
  rw [← hT]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hwu : w i = rootUnit ζ ^ a i * v i := by
    ext; simp [rootUnit_val, hw i hi]
  simp only [T, map_sub, Finsupp.liftAddHom_apply_single, AddMonoidHom.coe_comp, Function.comp_apply,
    AddMonoidHom.coe_mulRight]
  rw [hwu, tau_mul]
  show (c i).down * (a i : ZMod q) = (c i).down * (tau ζ (v i) + a i) - (c i).down * tau ζ (v i)
  ring

end GlobalTheory.EtC.FreeActSum
