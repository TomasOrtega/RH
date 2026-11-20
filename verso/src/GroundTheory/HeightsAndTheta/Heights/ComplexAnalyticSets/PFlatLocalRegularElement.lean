import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFlatLocalRegularElement
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing TensorProduct
open scoped Pointwise

section Flat

variable {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]

/- English proof (translation)
Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul i m => simpa using Submodule.smul_mem_smul i.2 Submodule.mem_top`. Consider the case `add s t hs ht => rw [map_add, map_add]`. Conclude with `add_mem hs ht`.
-/
theorem lid_rTensor_subtype_mem_smul_top (I : Ideal A) (t : I ⊗[A] M) :
    TensorProduct.lid A M (I.subtype.rTensor M t) ∈ I • (⊤ : Submodule A M) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul i m => simpa using Submodule.smul_mem_smul i.2 Submodule.mem_top
  | add s t hs ht => rw [map_add, map_add]; exact add_mem hs ht

/- English proof (translation)
Use `Submodule.smul_induction_on hx (fun a ha m _ => ⟨⟨a, ha⟩ ⊗ₜ m, by simp⟩) ?_` and prove the remaining obligations. Introduce and unpack `x x' ⟨s, rfl⟩ ⟨s', rfl⟩`. Conclude with `⟨s + s', by rw [map_add, map_add]⟩`.
-/
theorem exists_lid_rTensor_subtype_eq (I : Ideal A) {x : M} (hx : x ∈ I • (⊤ : Submodule A M)) :
    ∃ t : I ⊗[A] M, TensorProduct.lid A M (I.subtype.rTensor M t) = x := by
  refine Submodule.smul_induction_on hx (fun a ha m _ => ⟨⟨a, ha⟩ ⊗ₜ m, by simp⟩) ?_
  rintro x x' ⟨s, rfl⟩ ⟨s', rfl⟩
  exact ⟨s + s', by rw [map_add, map_add]⟩

/- English proof (translation)
Use `set g : A →ₗ[A] A ⧸ J := J.mkQ ∘ₗ LinearMap.mulRight A a`. Establish `hex` using `Module.Flat.rTensor_exact M (LinearMap.exact_subtype_ker_map g)`. Establish `h0 : g.rTensor M ((1 : A) ⊗ₜ v) = 0`. Apply `(TensorProduct.quotTensorEquivQuotSMul M J).injective` to reduce the goal to its premises. Rewrite using `[map_zero, LinearMap.rTensor_tmul]`.

Establish `: g 1 = Ideal.Quotient.mk J a` using `by simp [g, Ideal.Quotient.mk_eq_mk]`. Rewrite using `[this, TensorProduct.quotTensorEquivQuotSMul_mk_tmul, Submodule.Quotient.mk_eq_zero]`. Conclude with `hv`. Take `⟨t, ht⟩` from `(hex ((1 : A) ⊗ₜ v)).mp h0`. Use `lid_rTensor_subtype_mem_smul_top (LinearMap.ker g) t` as an intermediate fact.

Rewrite `this` using `[ht, TensorProduct.lid_tmul, one_smul]`. Then use the resulting hypothesis.
-/
theorem mem_colon_smul_top_of_flat [Module.Flat A M] (J : Ideal A) (a : A) {v : M}
    (hv : a • v ∈ J • (⊤ : Submodule A M)) :
    v ∈ LinearMap.ker (J.mkQ ∘ₗ LinearMap.mulRight A a) • (⊤ : Submodule A M) := by
  set g : A →ₗ[A] A ⧸ J := J.mkQ ∘ₗ LinearMap.mulRight A a
  have hex := Module.Flat.rTensor_exact M (LinearMap.exact_subtype_ker_map g)
  have h0 : g.rTensor M ((1 : A) ⊗ₜ v) = 0 := by
    apply (TensorProduct.quotTensorEquivQuotSMul M J).injective
    rw [map_zero, LinearMap.rTensor_tmul]
    have : g 1 = Ideal.Quotient.mk J a := by simp [g, Ideal.Quotient.mk_eq_mk]
    rw [this, TensorProduct.quotTensorEquivQuotSMul_mk_tmul, Submodule.Quotient.mk_eq_zero]
    exact hv
  obtain ⟨t, ht⟩ := (hex ((1 : A) ⊗ₜ v)).mp h0
  have := lid_rTensor_subtype_mem_smul_top (LinearMap.ker g) t
  rwa [ht, TensorProduct.lid_tmul, one_smul] at this

end Flat

/- English proof (translation)
Establish `hkJ : m ^ Nat.find h ≤ J` using `Nat.find_spec h`. Establish `hk0 : Nat.find h ≠ 0`. Introduce `h0`. Apply `hJ` to reduce the goal to its premises. Rewrite `hkJ` using `[h0, pow_zero, Ideal.one_eq_top]`.

Conclude with `top_le_iff.mp hkJ`. Take `⟨a, ha, haJ⟩` from `SetLike.not_le_iff_exists.mp (Nat.find_min h (Nat.sub_lt (Nat.pos_of_ne_zero hk0) one_pos))`. Use `⟨a, haJ, fun r hr => hkJ ?_⟩` and prove the remaining obligations. Establish `: r * a ∈ m ^ (1 + (Nat.find h - 1))`. Rewrite using `[pow_add, pow_one]`.

Conclude with `Ideal.mul_mem_mul hr ha`. Rewrite `this` using `[Nat.add_sub_cancel' (Nat.pos_of_ne_zero hk0)]`. Then use the resulting hypothesis.
-/
theorem exists_not_mem_forall_mul_mem {R : Type} [CommRing R] (m J : Ideal R) (hJ : J ≠ ⊤)
    (h : ∃ n, m ^ n ≤ J) : ∃ a ∉ J, ∀ r ∈ m, r * a ∈ J := by
  classical
  have hkJ : m ^ Nat.find h ≤ J := Nat.find_spec h
  have hk0 : Nat.find h ≠ 0 := by
    intro h0
    apply hJ
    rw [h0, pow_zero, Ideal.one_eq_top] at hkJ
    exact top_le_iff.mp hkJ
  obtain ⟨a, ha, haJ⟩ := SetLike.not_le_iff_exists.mp
    (Nat.find_min h (Nat.sub_lt (Nat.pos_of_ne_zero hk0) one_pos))
  refine ⟨a, haJ, fun r hr => hkJ ?_⟩
  have : r * a ∈ m ^ (1 + (Nat.find h - 1)) := by
    rw [pow_add, pow_one]
    exact Ideal.mul_mem_mul hr ha
  rwa [Nat.add_sub_cancel' (Nat.pos_of_ne_zero hk0)] at this

section Local

variable {A B M : Type} [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]

/- English proof (translation)
Rewrite using `[← Submodule.restrictScalars_mem A (I.map (algebraMap A B) • (⊤ : Submodule B M)) x, Ideal.smul_restrictScalars, Submodule.restrictScalars_top]`.
-/
theorem mem_smul_top_iff_mem_map_smul_top (I : Ideal A) (x : M) :
    x ∈ I • (⊤ : Submodule A M) ↔ x ∈ I.map (algebraMap A B) • (⊤ : Submodule B M) := by
  rw [← Submodule.restrictScalars_mem A (I.map (algebraMap A B) • (⊤ : Submodule B M)) x,
    Ideal.smul_restrictScalars, Submodule.restrictScalars_top]

/- English proof (translation)
Rewrite `hx`, the goal using `[mem_smul_top_iff_mem_map_smul_top (B := B)]`. Conclude with `Submodule.smul_mem _ y hx`.
-/
theorem smul_mem_smul_top_of_mem (I : Ideal A) (y : B) {x : M}
    (hx : x ∈ I • (⊤ : Submodule A M)) : y • x ∈ I • (⊤ : Submodule A M) := by
  rw [mem_smul_top_iff_mem_map_smul_top (B := B)] at hx ⊢
  exact Submodule.smul_mem _ y hx

variable [IsNoetherianRing A] [IsLocalRing A] [Module.Flat A M]

/- English proof (translation)
Proceed by induction on `J using WellFoundedGT.induction with`. Consider the case `_ J ih`. Introduce `hpow z hz`. Distinguish the cases in `hJ : J = ⊤`. Substitute `hJ` using the available equality.

Rewrite using `[Submodule.top_smul]`. Conclude with `Submodule.mem_top`. Take `⟨a, haJ, hma⟩` from `exists_not_mem_forall_mul_mem (maximalIdeal A) J hJ hpow`. Establish `hlt : J < J ⊔ Ideal.span {a}` using `lt_of_le_of_ne le_sup_left fun h => haJ (h ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self a))`. Establish `hz'` using `ih _ hlt (hpow.imp fun n hn => hn.trans le_sup_left) z (Submodule.smul_mono_left le_sup_left hz)`.

Rewrite `hz'` using `[Submodule.sup_smul, Submodule.mem_sup]`. Take `⟨w, hw, v, hv, rfl⟩` from `hz'`. Rewrite `hv` using `[Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]`. Take `⟨u, -, rfl⟩` from `hv`. Establish `hyw` using `smul_mem_smul_top_of_mem J y hw`.

Establish `hau : a • (y • u) ∈ J • (⊤ : Submodule A M)`. Rewrite using `[smul_comm]`. Establish `: y • (a • u) = y • (w + a • u) - y • w` using `by rw [smul_add]; abel`. Rewrite using `[this]`. Conclude with `sub_mem hz hyw`.

Establish `hK : LinearMap.ker (J.mkQ ∘ₗ LinearMap.mulRight A a) ≤ maximalIdeal A`. Introduce `r hr`. Simplify using `only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, LinearMap.mulRight_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hr`. Assume the negation of the conclusion as `hrm`. Rewrite `hrm` using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]`.

Take `⟨r', rfl⟩` from `hrm`. Apply `haJ` to reduce the goal to its premises. Use `J.mul_mem_left (↑r'⁻¹ : A) hr` as an intermediate fact. Rewrite `this` using `[← mul_assoc, Units.inv_mul, one_mul]`. Then use the resulting hypothesis. Establish `hu` using `h0 u (Submodule.smul_mono_left hK (mem_colon_smul_top_of_flat J a hau))`.

Use `add_mem hw ?_` and prove the remaining obligations. Use `Submodule.smul_induction_on hu (fun r hr m _ => ?_) (fun x x' hx hx' => ?_)` and prove the remaining obligations. Rewrite using `[smul_smul, mul_comm]`. Conclude with `Submodule.smul_mem_smul (hma r hr) Submodule.mem_top`. Rewrite using `[smul_add]`.

Conclude with `add_mem hx hx'`.
-/
theorem smul_regular_mod_of_pow_le (y : B)
    (h0 : ∀ u : M, y • u ∈ maximalIdeal A • (⊤ : Submodule A M) →
      u ∈ maximalIdeal A • (⊤ : Submodule A M)) (J : Ideal A) :
    (∃ n, maximalIdeal A ^ n ≤ J) →
      ∀ z : M, y • z ∈ J • (⊤ : Submodule A M) → z ∈ J • (⊤ : Submodule A M) := by
  induction J using WellFoundedGT.induction with
  | _ J ih =>
  intro hpow z hz
  by_cases hJ : J = ⊤
  · subst hJ
    rw [Submodule.top_smul]
    exact Submodule.mem_top
  obtain ⟨a, haJ, hma⟩ := exists_not_mem_forall_mul_mem (maximalIdeal A) J hJ hpow
  have hlt : J < J ⊔ Ideal.span {a} :=
    lt_of_le_of_ne le_sup_left fun h =>
      haJ (h ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self a))
  have hz' := ih _ hlt (hpow.imp fun n hn => hn.trans le_sup_left) z
    (Submodule.smul_mono_left le_sup_left hz)
  rw [Submodule.sup_smul, Submodule.mem_sup] at hz'
  obtain ⟨w, hw, v, hv, rfl⟩ := hz'
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hv
  obtain ⟨u, -, rfl⟩ := hv
  have hyw := smul_mem_smul_top_of_mem J y hw
  have hau : a • (y • u) ∈ J • (⊤ : Submodule A M) := by
    rw [smul_comm]
    have : y • (a • u) = y • (w + a • u) - y • w := by rw [smul_add]; abel
    rw [this]
    exact sub_mem hz hyw
  have hK : LinearMap.ker (J.mkQ ∘ₗ LinearMap.mulRight A a) ≤ maximalIdeal A := by
    intro r hr
    simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.mulRight_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hr
    by_contra hrm
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hrm
    obtain ⟨r', rfl⟩ := hrm
    apply haJ
    have := J.mul_mem_left (↑r'⁻¹ : A) hr
    rwa [← mul_assoc, Units.inv_mul, one_mul] at this
  have hu := h0 u (Submodule.smul_mono_left hK (mem_colon_smul_top_of_flat J a hau))
  refine add_mem hw ?_
  refine Submodule.smul_induction_on hu (fun r hr m _ => ?_) (fun x x' hx hx' => ?_)
  · rw [smul_smul, mul_comm]
    exact Submodule.smul_mem_smul (hma r hr) Submodule.mem_top
  · rw [smul_add]
    exact add_mem hx hx'

variable [IsNoetherianRing B] [IsLocalRing B] [IsLocalHom (algebraMap A B)] [Module.Finite B M]

/- English proof (translation)
Use `set P : Submodule B M := I.map (algebraMap A B) • ⊤`. Establish `hle : (maximalIdeal A).map (algebraMap A B) ≤ Ideal.jacobson ⊥` using `(IsLocalRing.map_maximalIdeal_le _).trans (IsLocalRing.maximalIdeal_le_jacobson _)`. Establish `hK` using `Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (M := M ⧸ P) _ hle`. Rewrite using `[mem_smul_top_iff_mem_map_smul_top (B := B), ← Submodule.Quotient.mk_eq_zero P]`. Establish `hmem : Submodule.Quotient.mk (p` using `P) z ∈ (⨅ i : ℕ, ((maximalIdeal A).map (algebraMap A B)) ^ i • (⊤ : Submodule B (M ⧸ P))) := by`.

Rewrite using `[Submodule.mem_iInf]`. Introduce `n`. Establish `hn` using `smul_regular_mod_of_pow_le y h0 (I ⊔ maximalIdeal A ^ n) ⟨n, le_sup_right⟩ z (Submodule.smul_mono_left le_sup_left hz)`. Rewrite `hn` using `[Submodule.sup_smul, Submodule.mem_sup]`. Take `⟨w, hw, v, hv, rfl⟩` from `hn`.

Rewrite `hw`, `hv` using `[mem_smul_top_iff_mem_map_smul_top (B := B)]`. Rewrite `hv` using `[Ideal.map_pow]`. Rewrite using `[Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero P).mpr hw, zero_add]`. Establish `hmap : (((maximalIdeal A).map (algebraMap A B)) ^ n • (⊤ : Submodule B M)).map P.mkQ ≤ ((maximalIdeal A).map (algebraMap A B)) ^ n • ⊤`. Rewrite using `[Submodule.map_smul'']`.

Conclude with `Submodule.smul_mono le_rfl le_top`. Conclude with `hmap (Submodule.mem_map_of_mem hv)`. Rewrite `hmem` using `[hK]`. Conclude with `(Submodule.mem_bot B).mp hmem`.
-/
theorem smul_regular_mod_ideal (y : B)
    (h0 : ∀ u : M, y • u ∈ maximalIdeal A • (⊤ : Submodule A M) →
      u ∈ maximalIdeal A • (⊤ : Submodule A M)) (I : Ideal A) (z : M)
    (hz : y • z ∈ I • (⊤ : Submodule A M)) : z ∈ I • (⊤ : Submodule A M) := by
  set P : Submodule B M := I.map (algebraMap A B) • ⊤
  have hle : (maximalIdeal A).map (algebraMap A B) ≤ Ideal.jacobson ⊥ :=
    (IsLocalRing.map_maximalIdeal_le _).trans (IsLocalRing.maximalIdeal_le_jacobson _)
  have hK := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (M := M ⧸ P) _ hle
  rw [mem_smul_top_iff_mem_map_smul_top (B := B), ← Submodule.Quotient.mk_eq_zero P]
  have hmem : Submodule.Quotient.mk (p := P) z ∈
      (⨅ i : ℕ, ((maximalIdeal A).map (algebraMap A B)) ^ i • (⊤ : Submodule B (M ⧸ P))) := by
    rw [Submodule.mem_iInf]
    intro n
    have hn := smul_regular_mod_of_pow_le y h0 (I ⊔ maximalIdeal A ^ n) ⟨n, le_sup_right⟩ z
      (Submodule.smul_mono_left le_sup_left hz)
    rw [Submodule.sup_smul, Submodule.mem_sup] at hn
    obtain ⟨w, hw, v, hv, rfl⟩ := hn
    rw [mem_smul_top_iff_mem_map_smul_top (B := B)] at hw hv
    rw [Ideal.map_pow] at hv
    rw [Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero P).mpr hw, zero_add]
    have hmap : (((maximalIdeal A).map (algebraMap A B)) ^ n • (⊤ : Submodule B M)).map P.mkQ ≤
        ((maximalIdeal A).map (algebraMap A B)) ^ n • ⊤ := by
      rw [Submodule.map_smul'']
      exact Submodule.smul_mono le_rfl le_top
    exact hmap (Submodule.mem_map_of_mem hv)
  rw [hK] at hmem
  exact (Submodule.mem_bot B).mp hmem

end Local

/- English proof (translation)
Introduce `A B _ _ _ _ _ _ _ hloc M _ _ _ _ _ _ y _ hreg`. Establish `h0 : ∀ u : M, y • u ∈ maximalIdeal A • (⊤ : Submodule A M) → u ∈ maximalIdeal A • (⊤ : Submodule A M)`. Introduce `u hu`. Rewrite `hu`, the goal using `[mem_smul_top_iff_mem_map_smul_top (B := B), ← Submodule.Quotient.mk_eq_zero]`. Use `hreg ?_` and prove the remaining obligations.

Use `show y • Submodule.Quotient.mk u = y • (0 : M ⧸ _)`. Rewrite using `[smul_zero, ← Submodule.Quotient.mk_smul, hu]`. Establish `hR` using `smul_regular_mod_ideal (B := B) y h0`. Use `⟨fun a b hab => ?_, ?_⟩` and prove the remaining obligations. Establish `hab' : y • a = y • b` using `hab`.

Establish `h` using `hR ⊥ (a - b) (by rw [Submodule.bot_smul, Submodule.mem_bot, smul_sub, hab', sub_self])`. Rewrite `h` using `[Submodule.bot_smul, Submodule.mem_bot]`. Conclude with `sub_eq_zero.mp h`. Rewrite using `[Module.Flat.iff_rTensor_injective']`. Introduce `I`.

Set `π : M →ₗ[A] QuotSMulTop y M` to `(Submodule.mkQ (y • (⊤ : Submodule B M))).restrictScalars A`. Set `Y : M →ₗ[A] M` to `(LinearMap.lsmul B M y).restrictScalars A`. Set `μM : I ⊗[A] M →ₗ[A] M` to `TensorProduct.lid A M ∘ₗ I.subtype.rTensor M`. Set `μN : I ⊗[A] QuotSMulTop y M →ₗ[A] QuotSMulTop y M` to `TensorProduct.lid A (QuotSMulTop y M) ∘ₗ I.subtype.rTensor (QuotSMulTop y M)`. Establish `hμM : Function.Injective μM` using `(TensorProduct.lid A M).injective.comp (Module.Flat.rTensor_preserves_injective_linearMap I.subtype Subtype.val_injective)`.

Establish `natπ : μN ∘ₗ π.lTensor I = π ∘ₗ μM` using `TensorProduct.ext' fun i m => by simp [μN, μM, π]`. Establish `natY : μM ∘ₗ Y.lTensor I = Y ∘ₗ μM` using `TensorProduct.ext' fun i m => by simp [μM, Y, smul_comm (i : A) y m]`. Establish `hπY : π ∘ₗ Y = 0` using `LinearMap.ext fun m => (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.smul_mem_pointwise_smul m y ⊤ Submodule.mem_top)`. Use `Function.Injective.of_comp (f := TensorProduct.lid A (QuotSMulTop y M)) ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Function.Injective μN`.

Rewrite using `[injective_iff_map_eq_zero]`. Introduce `t ht`. Establish `hπs : Function.Surjective π` using `Submodule.mkQ_surjective (y • (⊤ : Submodule B M))`. Take `⟨s, rfl⟩` from `LinearMap.lTensor_surjective I hπs t`. Establish `h1 : π (μM s) = 0`.

Rewrite using `[← LinearMap.comp_apply π μM, ← natπ, LinearMap.comp_apply]`. Conclude with `ht`. Establish `h2 : μM s ∈ y • (⊤ : Submodule B M)` using `(Submodule.Quotient.mk_eq_zero _).mp h1`. Take `⟨z, -, hz⟩` from `(Submodule.mem_smul_pointwise_iff_exists _ _ _).mp h2`. Establish `h3 : y • z ∈ I • (⊤ : Submodule A M)` using `hz ▸ lid_rTensor_subtype_mem_smul_top I s`.

Take `⟨s', hs'⟩` from `exists_lid_rTensor_subtype_eq I (hR I z h3)`. Establish `h4 : s = Y.lTensor I s'`. Apply `hμM` to reduce the goal to its premises. Rewrite using `[← LinearMap.comp_apply μM (Y.lTensor I), natY, LinearMap.comp_apply]`. Express the relevant statement in the definitionally equal form `μM s = y • μM s'`.

Rewrite using `[show μM s' = z from hs', hz]`. Rewrite using `[h4, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hπY, LinearMap.lTensor_zero, LinearMap.zero_apply]`.
-/
theorem FlatLocalRegularElement.proof : FlatLocalRegularElement.Statement := by
  intro A B _ _ _ _ _ _ _ hloc M _ _ _ _ _ _ y _ hreg
  have h0 : ∀ u : M, y • u ∈ maximalIdeal A • (⊤ : Submodule A M) →
      u ∈ maximalIdeal A • (⊤ : Submodule A M) := by
    intro u hu
    rw [mem_smul_top_iff_mem_map_smul_top (B := B), ← Submodule.Quotient.mk_eq_zero] at hu ⊢
    refine hreg ?_
    show y • Submodule.Quotient.mk u = y • (0 : M ⧸ _)
    rw [smul_zero, ← Submodule.Quotient.mk_smul, hu]
  have hR := smul_regular_mod_ideal (B := B) y h0
  refine ⟨fun a b hab => ?_, ?_⟩
  · have hab' : y • a = y • b := hab
    have h := hR ⊥ (a - b) (by rw [Submodule.bot_smul, Submodule.mem_bot, smul_sub, hab', sub_self])
    rw [Submodule.bot_smul, Submodule.mem_bot] at h
    exact sub_eq_zero.mp h
  · rw [Module.Flat.iff_rTensor_injective']
    intro I
    let π : M →ₗ[A] QuotSMulTop y M := (Submodule.mkQ (y • (⊤ : Submodule B M))).restrictScalars A
    let Y : M →ₗ[A] M := (LinearMap.lsmul B M y).restrictScalars A
    let μM : I ⊗[A] M →ₗ[A] M := TensorProduct.lid A M ∘ₗ I.subtype.rTensor M
    let μN : I ⊗[A] QuotSMulTop y M →ₗ[A] QuotSMulTop y M :=
      TensorProduct.lid A (QuotSMulTop y M) ∘ₗ I.subtype.rTensor (QuotSMulTop y M)
    have hμM : Function.Injective μM :=
      (TensorProduct.lid A M).injective.comp
        (Module.Flat.rTensor_preserves_injective_linearMap I.subtype Subtype.val_injective)
    have natπ : μN ∘ₗ π.lTensor I = π ∘ₗ μM :=
      TensorProduct.ext' fun i m => by simp [μN, μM, π]
    have natY : μM ∘ₗ Y.lTensor I = Y ∘ₗ μM :=
      TensorProduct.ext' fun i m => by simp [μM, Y, smul_comm (i : A) y m]
    have hπY : π ∘ₗ Y = 0 := LinearMap.ext fun m =>
      (Submodule.Quotient.mk_eq_zero _).mpr
        (Submodule.smul_mem_pointwise_smul m y ⊤ Submodule.mem_top)
    refine Function.Injective.of_comp (f := TensorProduct.lid A (QuotSMulTop y M)) ?_
    change Function.Injective μN
    rw [injective_iff_map_eq_zero]
    intro t ht
    have hπs : Function.Surjective π := Submodule.mkQ_surjective (y • (⊤ : Submodule B M))
    obtain ⟨s, rfl⟩ := LinearMap.lTensor_surjective I hπs t
    have h1 : π (μM s) = 0 := by
      rw [← LinearMap.comp_apply π μM, ← natπ, LinearMap.comp_apply]
      exact ht
    have h2 : μM s ∈ y • (⊤ : Submodule B M) := (Submodule.Quotient.mk_eq_zero _).mp h1
    obtain ⟨z, -, hz⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp h2
    have h3 : y • z ∈ I • (⊤ : Submodule A M) := hz ▸ lid_rTensor_subtype_mem_smul_top I s
    obtain ⟨s', hs'⟩ := exists_lid_rTensor_subtype_eq I (hR I z h3)
    have h4 : s = Y.lTensor I s' := by
      apply hμM
      rw [← LinearMap.comp_apply μM (Y.lTensor I), natY, LinearMap.comp_apply]
      change μM s = y • μM s'
      rw [show μM s' = z from hs', hz]
    rw [h4, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hπY, LinearMap.lTensor_zero,
      LinearMap.zero_apply]

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
