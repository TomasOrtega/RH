import Mathlib
import Formalism.CharacterColumnKernels.StatementRho
open Formalism.NG

namespace GlobalTheory.HomLen

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/- English proof (translation)
Assume the negation of the conclusion as `h`. Rewrite `h` using `[← ne_eq, Module.length_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian]`. Take `⟨_, h2⟩` from `h`. Use `haveI : IsArtinianRing O := h2`. Conclude with `IsDiscreteValuationRing.not_a_field O (IsLocalRing.isField_iff_maximalIdeal_eq.1 (IsArtinianRing.isField_of_isDomain O))`.
-/
theorem length_self_eq_top : Module.length O O = ⊤ := by
  by_contra h
  rw [← ne_eq, Module.length_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian] at h
  obtain ⟨_, h2⟩ := h
  haveI : IsArtinianRing O := h2
  exact IsDiscreteValuationRing.not_a_field O
    (IsLocalRing.isField_iff_maximalIdeal_eq.1 (IsArtinianRing.isField_of_isDomain O))

/- English proof (translation)
Distinguish the cases in `hx : x = 0`. Substitute `hx` using the available equality. Establish `e : (O ⧸ Ideal.span {(0 : O)}) ≃ₗ[O] O` using `Submodule.quotEquivOfEqBot _ (by simp)`. Rewrite using `[e.length_eq, length_self_eq_top]`. Conclude with `le_top`.

Use `set K := FractionRing O`. Establish `hxK : algebraMap O K x ≠ 0`. Simplify using `using (IsFractionRing.injective O K).ne hx`. Use `set c : K := (algebraMap O K x)⁻¹ with hc`. Set `g0 : O →ₗ[O] KO O` to `(Submodule.mkQ (1 : Submodule O K)) ∘ₗ LinearMap.toSpanSingleton O K c`.

Establish `hg0 : ∀ y, g0 y ∈ LinearMap.ker (x • LinearMap.id : KO O →ₗ[O] KO O)`. Introduce `y`. Simplify using `only [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply, g0, LinearMap.coe_comp, Function.comp_apply, LinearMap.toSpanSingleton_apply, Submodule.mkQ_apply]`. Rewrite using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_one]`. Use `⟨y, ?_⟩` and prove the remaining obligations.

Rewrite using `[smul_smul, Algebra.smul_def, hc, map_mul, mul_right_comm, mul_inv_cancel₀ hxK, one_mul]`. Set `g : O →ₗ[O] LinearMap.ker (x • LinearMap.id : KO O →ₗ[O] KO O)` to `g0.codRestrict _ hg0`. Establish `hgs : Function.Surjective g`. Introduce and unpack `⟨t, ht⟩`. Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ t`.

Rewrite `ht` using `[LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_one]`. Take `⟨y, hy⟩` from `ht`. Use `⟨y, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [g, g0, LinearMap.codRestrict_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.toSpanSingleton_apply, Submodule.mkQ_apply]`.

Use `congr 1`. Rewrite using `[Algebra.smul_def, hy, Algebra.smul_def, hc, mul_comm _ z, mul_assoc, mul_inv_cancel₀ hxK, mul_one]`. Establish `hker : Ideal.span {x} ≤ LinearMap.ker g`. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker]`. Apply `Subtype.ext` to reduce the goal to its premises.

Simplify using `only [g, g0, LinearMap.codRestrict_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.toSpanSingleton_apply, Submodule.mkQ_apply, ZeroMemClass.coe_zero]`. Rewrite using `[Submodule.Quotient.mk_eq_zero, Submodule.mem_one]`. Use `⟨1, ?_⟩` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, hc, mul_inv_cancel₀ hxK, map_one]`. Establish `hqs : Function.Surjective ((Ideal.span {x}).liftQ g hker)`.

Introduce `t`. Take `⟨y, rfl⟩` from `hgs t`. Conclude with `⟨Submodule.Quotient.mk y, rfl⟩`. Conclude with `Module.length_le_of_surjective _ hqs`.
-/
theorem length_ker_smul_le (x : O) :
    Module.length O (LinearMap.ker (x • LinearMap.id : KO O →ₗ[O] KO O)) ≤
      Module.length O (O ⧸ Ideal.span {x}) := by
  by_cases hx : x = 0
  · subst hx
    have e : (O ⧸ Ideal.span {(0 : O)}) ≃ₗ[O] O :=
      Submodule.quotEquivOfEqBot _ (by simp)
    rw [e.length_eq, length_self_eq_top]
    exact le_top
  set K := FractionRing O
  have hxK : algebraMap O K x ≠ 0 := by
    simpa using (IsFractionRing.injective O K).ne hx
  set c : K := (algebraMap O K x)⁻¹ with hc
  let g0 : O →ₗ[O] KO O := (Submodule.mkQ (1 : Submodule O K)) ∘ₗ LinearMap.toSpanSingleton O K c
  have hg0 : ∀ y, g0 y ∈ LinearMap.ker (x • LinearMap.id : KO O →ₗ[O] KO O) := by
    intro y
    simp only [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply, g0,
      LinearMap.coe_comp, Function.comp_apply, LinearMap.toSpanSingleton_apply,
      Submodule.mkQ_apply]
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_one]
    refine ⟨y, ?_⟩
    rw [smul_smul, Algebra.smul_def, hc, map_mul, mul_right_comm, mul_inv_cancel₀ hxK, one_mul]
  let g : O →ₗ[O] LinearMap.ker (x • LinearMap.id : KO O →ₗ[O] KO O) := g0.codRestrict _ hg0
  have hgs : Function.Surjective g := by
    rintro ⟨t, ht⟩
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ t
    rw [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero, Submodule.mem_one] at ht
    obtain ⟨y, hy⟩ := ht
    refine ⟨y, ?_⟩
    apply Subtype.ext
    simp only [g, g0, LinearMap.codRestrict_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.toSpanSingleton_apply, Submodule.mkQ_apply]
    congr 1
    rw [Algebra.smul_def, hy, Algebra.smul_def, hc, mul_comm _ z, mul_assoc, mul_inv_cancel₀ hxK,
      mul_one]
  have hker : Ideal.span {x} ≤ LinearMap.ker g := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker]
    apply Subtype.ext
    simp only [g, g0, LinearMap.codRestrict_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.toSpanSingleton_apply, Submodule.mkQ_apply, ZeroMemClass.coe_zero]
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_one]
    refine ⟨1, ?_⟩
    rw [Algebra.smul_def, hc, mul_inv_cancel₀ hxK, map_one]
  have hqs : Function.Surjective ((Ideal.span {x}).liftQ g hker) := by
    intro t
    obtain ⟨y, rfl⟩ := hgs t
    exact ⟨Submodule.Quotient.mk y, rfl⟩
  exact Module.length_le_of_surjective _ hqs

end GlobalTheory.HomLen

namespace GlobalTheory.HomLen

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/- English proof (translation)
Introduce `f g hfg`. Use extensionality with `⟨b, hb⟩`. Take `⟨k, rfl⟩` from `AddSubgroup.mem_zmultiples_iff.mp hb`. Establish `: (⟨k • a, hb⟩ : AddSubgroup.zmultiples a) = k • ⟨a, AddSubgroup.mem_zmultiples a⟩` using `rfl`. Simplify using `only at hfg`.

Rewrite using `[this, map_zsmul, map_zsmul, hfg]`.
-/
theorem evalGen_injective {A M : Type} [AddCommGroup A] [AddCommGroup M] (a : A) :
    Function.Injective (fun f : (AddSubgroup.zmultiples a) →+ M =>
      f ⟨a, AddSubgroup.mem_zmultiples a⟩) := by
  intro f g hfg
  ext ⟨b, hb⟩
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hb
  have : (⟨k • a, hb⟩ : AddSubgroup.zmultiples a) = k • ⟨a, AddSubgroup.mem_zmultiples a⟩ := rfl
  simp only at hfg
  rw [this, map_zsmul, map_zsmul, hfg]

def evalGen {A M : Type} [AddCommGroup A] [AddCommGroup M] [Module O M] (a : A) :
    ((AddSubgroup.zmultiples a) →+ M) →ₗ[O] M where
  toFun f := f ⟨a, AddSubgroup.mem_zmultiples a⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/- English proof (translation)
Establish `hkill : ∀ f : (AddSubgroup.zmultiples a) →+ M, p • f ⟨a, AddSubgroup.mem_zmultiples a⟩ = 0`. Introduce `f`. Rewrite using `[← map_nsmul]`. Establish `: p • (⟨a, AddSubgroup.mem_zmultiples a⟩ : AddSubgroup.zmultiples a) = 0`. Apply `Subtype.ext` to reduce the goal to its premises.

Simplify using `[← ha, addOrderOf_nsmul_eq_zero]`. Rewrite using `[this, map_zero]`. Use `split_ifs with hpl`. Substitute `hpl` using the available equality. Set `T` to `LinearMap.ker ((p : O) • LinearMap.id : KO O →ₗ[O] KO O)`.

Establish `hT : ∀ f, (eM.toLinearMap ∘ₗ evalGen (O` using `O) (M := M) a) f ∈ T := by`. Introduce `f`. Simplify using `only [T, LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, evalGen, LinearMap.coe_mk, AddHom.coe_mk]`. Rewrite using `[← map_smul, Nat.cast_smul_eq_nsmul, hkill, map_zero]`. Set `v` to `(eM.toLinearMap ∘ₗ evalGen (O := O) (M := M) a).codRestrict T hT`.

Establish `hv : Function.Injective v`. Introduce `f g hfg`. Apply `evalGen_injective a` to reduce the goal to its premises. Use `congrArg Subtype.val hfg` as an intermediate fact. Simplify `this` using `[v, evalGen]`.

Conclude with `(Module.length_le_of_injective v hv).trans (length_ker_smul_le _)`. Establish `hunit : IsUnit (p : O)`. Establish `h1 : IsUnit (p : ℤ_[l])`. Rewrite using `[PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]`. Conclude with `(Nat.coprime_primes (Fact.out) (Fact.out)).2 (Ne.symm hpl)`.

Simplify using `using h1.map (algebraMap ℤ_[l] O)`. Use `haveI : Subsingleton ((AddSubgroup.zmultiples a) →+ M) := by`. Prove the components needed by the constructor for the conclusion. Introduce `f g`. Apply `evalGen_injective a` to reduce the goal to its premises.

Simplify using `only`. Establish `hf` using `hkill f`. Establish `hg` using `hkill g`. Rewrite `hf`, `hg` using `[← Nat.cast_smul_eq_nsmul O]`. Rewrite using `[hunit.smul_eq_zero.1 hf, hunit.smul_eq_zero.1 hg]`.

Rewrite using `[Module.length_eq_zero]`.
-/
theorem length_cyclic_le (l : ℕ) [Fact l.Prime] [Algebra ℤ_[l] O] {M : Type} [AddCommGroup M]
    [Module O M] (eM : M ≃ₗ[O] KO O) {A : Type} [AddCommGroup A] (a : A) (p : ℕ)
    [Fact p.Prime] (ha : addOrderOf a = p) :
    Module.length O ((AddSubgroup.zmultiples a) →+ M) ≤
      if p = l then Module.length O (O ⧸ Ideal.span {(l : O)}) else 0 := by
  have hkill : ∀ f : (AddSubgroup.zmultiples a) →+ M, p • f ⟨a, AddSubgroup.mem_zmultiples a⟩ = 0 := by
    intro f
    rw [← map_nsmul]
    have : p • (⟨a, AddSubgroup.mem_zmultiples a⟩ : AddSubgroup.zmultiples a) = 0 := by
      apply Subtype.ext
      simp [← ha, addOrderOf_nsmul_eq_zero]
    rw [this, map_zero]
  split_ifs with hpl
  · subst hpl
    let T := LinearMap.ker ((p : O) • LinearMap.id : KO O →ₗ[O] KO O)
    have hT : ∀ f, (eM.toLinearMap ∘ₗ evalGen (O := O) (M := M) a) f ∈ T := by
      intro f
      simp only [T, LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply, LinearMap.coe_comp,
        Function.comp_apply, LinearEquiv.coe_coe, evalGen, LinearMap.coe_mk, AddHom.coe_mk]
      rw [← map_smul, Nat.cast_smul_eq_nsmul, hkill, map_zero]
    let v := (eM.toLinearMap ∘ₗ evalGen (O := O) (M := M) a).codRestrict T hT
    have hv : Function.Injective v := by
      intro f g hfg
      apply evalGen_injective a
      have := congrArg Subtype.val hfg
      simpa [v, evalGen] using this
    exact (Module.length_le_of_injective v hv).trans (length_ker_smul_le _)
  · have hunit : IsUnit (p : O) := by
      have h1 : IsUnit (p : ℤ_[l]) := by
        rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
        exact (Nat.coprime_primes (Fact.out) (Fact.out)).2 (Ne.symm hpl)
      simpa using h1.map (algebraMap ℤ_[l] O)
    haveI : Subsingleton ((AddSubgroup.zmultiples a) →+ M) := by
      constructor
      intro f g
      apply evalGen_injective a
      simp only
      have hf := hkill f
      have hg := hkill g
      rw [← Nat.cast_smul_eq_nsmul O] at hf hg
      rw [hunit.smul_eq_zero.1 hf, hunit.smul_eq_zero.1 hg]
    rw [Module.length_eq_zero]

end GlobalTheory.HomLen

namespace GlobalTheory.HomLen

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

def restr {A M : Type} [AddCommGroup A] [AddCommGroup M] [Module O M] (B : AddSubgroup A) :
    (A →+ M) →ₗ[O] (B →+ M) where
  toFun f := f.comp B.subtype
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def pull {A M : Type} [AddCommGroup A] [AddCommGroup M] [Module O M] (B : AddSubgroup A) :
    (A ⧸ B →+ M) →ₗ[O] (A →+ M) where
  toFun g := g.comp (QuotientAddGroup.mk' B)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/- English proof (translation)
Establish `hpull : Function.Injective (pull (O` using `O) (M := M) B) := by`. Introduce `g h hgh`. Use extensionality with `x`. Conclude with `DFunLike.congr_fun hgh x`. Establish `hex : Function.Exact (pull (O` using `O) (M := M) B) (restr (O := O) (M := M) B).rangeRestrict := by`.

Rewrite using `[LinearMap.exact_iff, LinearMap.ker_rangeRestrict]`. Use extensionality with `f`. Rewrite using `[LinearMap.mem_ker, LinearMap.mem_range]`. Prove the components needed by the constructor for the conclusion. Introduce `hf`.

Establish `hle : B ≤ f.ker`. Introduce `b hb`. Use `DFunLike.congr_fun hf ⟨b, hb⟩` as an intermediate fact. Simplify `this` using `[restr]`. Conclude with `⟨QuotientAddGroup.lift B f hle, by ext x; rfl⟩`.

Introduce and unpack `⟨g, rfl⟩`. Use extensionality with `b`. Use `show g (QuotientAddGroup.mk (b : A)) = 0`. Rewrite using `[(QuotientAddGroup.eq_zero_iff _).2 b.2, map_zero]`. Rewrite using `[Module.length_eq_add_of_exact _ _ hpull (restr B).surjective_rangeRestrict hex]`.

Use `gcongr`. Conclude with `Module.length_le_of_injective (LinearMap.range (restr (O := O) (M := M) B)).subtype (Submodule.subtype_injective _)`.
-/
theorem length_le_add {A M : Type} [AddCommGroup A] [AddCommGroup M] [Module O M]
    (B : AddSubgroup A) :
    Module.length O (A →+ M) ≤ Module.length O (A ⧸ B →+ M) + Module.length O (B →+ M) := by
  have hpull : Function.Injective (pull (O := O) (M := M) B) := by
    intro g h hgh
    ext x
    exact DFunLike.congr_fun hgh x
  have hex : Function.Exact (pull (O := O) (M := M) B) (restr (O := O) (M := M) B).rangeRestrict := by
    rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict]
    ext f
    rw [LinearMap.mem_ker, LinearMap.mem_range]
    constructor
    · intro hf
      have hle : B ≤ f.ker := by
        intro b hb
        have := DFunLike.congr_fun hf ⟨b, hb⟩
        simpa [restr] using this
      exact ⟨QuotientAddGroup.lift B f hle, by ext x; rfl⟩
    · rintro ⟨g, rfl⟩
      ext b
      show g (QuotientAddGroup.mk (b : A)) = 0
      rw [(QuotientAddGroup.eq_zero_iff _).2 b.2, map_zero]
  rw [Module.length_eq_add_of_exact _ _ hpull (restr B).surjective_rangeRestrict hex]
  gcongr
  exact Module.length_le_of_injective (LinearMap.range (restr (O := O) (M := M) B)).subtype
    (Submodule.subtype_injective _)

/- English proof (translation)
Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `A _ _ hn`. Distinguish the cases in `h1 : n = 1`. Use `haveI : Subsingleton A := by`.

Conclude with `(Nat.card_eq_one_iff_unique.1 (hn.trans h1)).1`. Use `haveI : Subsingleton (A →+ M) := ⟨fun f g => by ext x; rw [Subsingleton.elim x 0, map_zero, map_zero]⟩`. Rewrite using `[Module.length_eq_zero]`. Simplify using the standard rewrite rules. Take `⟨p, hp, hpn⟩` from `Nat.exists_prime_and_dvd h1`.

Use `haveI := Fact.mk hp`. Take `⟨a, ha⟩` from `exists_prime_addOrderOf_dvd_card' (G := A) p (hn ▸ hpn)`. Use `set B := AddSubgroup.zmultiples a`. Establish `hcard` using `AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup B`. Rewrite `hcard` using `[Nat.card_zmultiples, ha, hn]`.

Establish `hn0 : n ≠ 0` using `by rw [← hn]; exact Nat.card_pos.ne'`. Establish `hq0 : Nat.card (A ⧸ B) ≠ 0`. Introduce and unpack `h`. Rewrite `hcard` using `[h, zero_mul]`. Conclude with `hn0 hcard`.

Establish `hlt : Nat.card (A ⧸ B) < n`. Rewrite using `[hcard]`. Conclude with `lt_mul_of_one_lt_right (Nat.pos_of_ne_zero hq0) hp.one_lt`. Establish `ihq` using `ih _ hlt (A ⧸ B) rfl`. Establish `hB` using `length_cyclic_le l eM a p ha`.

Establish `hv : padicValNat l n = padicValNat l (Nat.card (A ⧸ B)) + (if p = l then 1 else 0)`. Rewrite using `[hcard, padicValNat.mul hq0 hp.ne_zero]`. Use `congr 1`. Use `split_ifs with h`. Substitute `h` using the available equality.

Conclude with `padicValNat_self`. Conclude with `padicValNat_primes (Ne.symm h)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hv]`. Apply the tactic sequence `split_ifs <;> simp [mul_add]`.
-/
theorem length_addMonoidHom_le_of_card_eq (l : ℕ) [Fact l.Prime] [Algebra ℤ_[l] O] {M : Type} [AddCommGroup M]
    [Module O M] (eM : M ≃ₗ[O] KO O) (n : ℕ) :
    ∀ (A : Type) [AddCommGroup A] [Finite A], Nat.card A = n →
      Module.length O (A →+ M) ≤
        Module.length O (O ⧸ Ideal.span {(l : O)}) * (padicValNat l n : ℕ∞) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A _ _ hn
  by_cases h1 : n = 1
  · haveI : Subsingleton A := by
      exact (Nat.card_eq_one_iff_unique.1 (hn.trans h1)).1
    haveI : Subsingleton (A →+ M) :=
      ⟨fun f g => by ext x; rw [Subsingleton.elim x 0, map_zero, map_zero]⟩
    rw [Module.length_eq_zero]
    simp
  obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd h1
  haveI := Fact.mk hp
  obtain ⟨a, ha⟩ := exists_prime_addOrderOf_dvd_card' (G := A) p (hn ▸ hpn)
  set B := AddSubgroup.zmultiples a
  have hcard := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup B
  rw [Nat.card_zmultiples, ha, hn] at hcard
  have hn0 : n ≠ 0 := by rw [← hn]; exact Nat.card_pos.ne'
  have hq0 : Nat.card (A ⧸ B) ≠ 0 := by
    rintro h; rw [h, zero_mul] at hcard; exact hn0 hcard
  have hlt : Nat.card (A ⧸ B) < n := by
    rw [hcard]; exact lt_mul_of_one_lt_right (Nat.pos_of_ne_zero hq0) hp.one_lt
  have ihq := ih _ hlt (A ⧸ B) rfl
  have hB := length_cyclic_le l eM a p ha
  have hv : padicValNat l n = padicValNat l (Nat.card (A ⧸ B)) + (if p = l then 1 else 0) := by
    rw [hcard, padicValNat.mul hq0 hp.ne_zero]
    congr 1
    split_ifs with h
    · subst h; exact padicValNat_self
    · exact padicValNat_primes (Ne.symm h)
  calc Module.length O (A →+ M)
      ≤ Module.length O (A ⧸ B →+ M) + Module.length O (B →+ M) := length_le_add B
    _ ≤ Module.length O (O ⧸ Ideal.span {(l : O)}) * (padicValNat l (Nat.card (A ⧸ B)) : ℕ∞) +
          (if p = l then Module.length O (O ⧸ Ideal.span {(l : O)}) else 0) := add_le_add ihq hB
    _ = Module.length O (O ⧸ Ideal.span {(l : O)}) * (padicValNat l n : ℕ∞) := by
      rw [hv]
      split_ifs <;> simp [mul_add]

/- English proof (translation)
Introduce `l _ O _ _ _ _ M _ _ eM A _ _`. Conclude with `length_addMonoidHom_le_of_card_eq l eM _ A rfl`.
-/
theorem length_addMonoidHom_le : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O]
    [Algebra ℤ_[l] O] (M : Type) [AddCommGroup M] [Module O M] (eM : M ≃ₗ[O] KO O)
    (A : Type) [AddCommGroup A] [Finite A],
    Module.length O (A →+ M) ≤
      Module.length O (O ⧸ Ideal.span {(l : O)}) * (padicValNat l (Nat.card A) : ℕ∞) := by
  intro l _ O _ _ _ _ M _ _ eM A _ _
  exact length_addMonoidHom_le_of_card_eq l eM _ A rfl

end GlobalTheory.HomLen
