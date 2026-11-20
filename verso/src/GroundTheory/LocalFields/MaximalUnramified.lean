import Mathlib
import GroundTheory.LocalFields.Interface
import GroundTheory.LocalFields.FiniteExtension
import GroundTheory.LocalFields.Uniqueness
import GroundTheory.LocalFields.Integers
import GroundTheory.LocalFields.UnitsPowers
import GroundTheory.LocalFields.UnramifiedRootsOfUnity
import GroundTheory.LocalFields.UnramifiedGalois
import GroundTheory.LocalFields.UnramifiedExistence
import GroundTheory.LocalFields.AbstractLocalReciprocity.ProfiniteInteger
import GroundTheory.LocalFields.AbstractLocalReciprocity.ExistsEqNsmulOfProjEqZero
import GroundTheory.LocalFields.AbstractLocalReciprocity.Frobenius
import GroundTheory.LocalFields.AbstractLocalReciprocity.Valuation

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel IntermediateField GroundTheory.LocalField.Abstract GroundTheory.LocalField.Abstract.ProfiniteInteger

section Roots

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih => rw [pow_succ', AlgEquiv.mul_apply, ih, map_pow, h, ← pow_mul, ← pow_succ']`.
-/
theorem algEquiv_pow_apply_of_apply_eq_pow {L : Type*} [Field L] [Algebra K L] {τ : L ≃ₐ[K] L}
    {x : L} {q : ℕ} (h : τ x = x ^ q) (k : ℕ) : (τ ^ k) x = x ^ q ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', AlgEquiv.mul_apply, ih, map_pow, h, ← pow_mul, ← pow_succ']

/- English proof (translation)
The claim follows from `Nat.one_lt_pow hn (one_lt_card_residueField K)`.
-/
theorem one_lt_card_residueField_pow {n : ℕ} (hn : n ≠ 0) : 1 < Nat.card 𝓀[K] ^ n :=
  Nat.one_lt_pow hn (one_lt_card_residueField K)

/- English proof (translation)
Take `⟨hE, hEn⟩` from `isUnramifiedSubextension_adjoin hn hζ`. Use `hE.1` as an intermediate fact. Set `` to `(finiteExtensionStructure K K⟮ζ⟯).rel`. Set `` to `(finiteExtensionStructure K K⟮ζ⟯).top`. Use `finiteExtensionStructure_isNonarchimedeanLocalField K K⟮ζ⟯` as an intermediate fact.

Use `finiteExtensionStructure_valuativeExtension K K⟮ζ⟯` as an intermediate fact. Establish `h` using `hE.ramificationIndex_eq_one`. Establish `hζ' : IsPrimitiveRoot (AdjoinSimple.gen K ζ) (Nat.card 𝓀[K] ^ n - 1)` using `hζ.of_map_of_injective (f := K⟮ζ⟯.val) Subtype.val_injective`. Use `⟨frobenius K K⟮ζ⟯ h, frobenius_apply_of_pow_eq_one h (natCast_card_pow_sub_one_ne_zero hn) hζ'.pow_eq_one, ?_, zpowers_frobenius K _ h⟩` and prove the remaining obligations. Rewrite using `[orderOf_frobenius, hEn]`.
-/
theorem exists_frobenius_adjoin {n : ℕ} (hn : n ≠ 0) {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ n - 1)) :
    ∃ τ : K⟮ζ⟯ ≃ₐ[K] K⟮ζ⟯, τ (AdjoinSimple.gen K ζ) = AdjoinSimple.gen K ζ ^ Nat.card 𝓀[K] ∧
      orderOf τ = n ∧ Subgroup.zpowers τ = ⊤ := by
  obtain ⟨hE, hEn⟩ := isUnramifiedSubextension_adjoin hn hζ
  have := hE.1
  let := (finiteExtensionStructure K K⟮ζ⟯).rel
  let := (finiteExtensionStructure K K⟮ζ⟯).top
  have := finiteExtensionStructure_isNonarchimedeanLocalField K K⟮ζ⟯
  have := finiteExtensionStructure_valuativeExtension K K⟮ζ⟯
  have h := hE.ramificationIndex_eq_one
  have hζ' : IsPrimitiveRoot (AdjoinSimple.gen K ζ) (Nat.card 𝓀[K] ^ n - 1) :=
    hζ.of_map_of_injective (f := K⟮ζ⟯.val) Subtype.val_injective
  refine ⟨frobenius K K⟮ζ⟯ h, frobenius_apply_of_pow_eq_one h
    (natCast_card_pow_sub_one_ne_zero hn) hζ'.pow_eq_one, ?_, zpowers_frobenius K _ h⟩
  rw [orderOf_frobenius, hEn]

/- English proof (translation)
Take `⟨hE, -⟩` from `isUnramifiedSubextension_adjoin hn hζ`. Use `hE.1` as an intermediate fact. Use `hE.isGalois` as an intermediate fact. Take `⟨τ, hτ, -, htop⟩` from `exists_frobenius_adjoin hn hζ`. Establish `hmem : σ.restrictNormal K⟮ζ⟯ ∈ Subgroup.zpowers τ` using `htop ▸ Subgroup.mem_top _`.

Take `⟨a, ha⟩` from `mem_powers_iff_mem_zpowers.2 hmem`. Use `⟨a, ?_⟩` and prove the remaining obligations. Establish `h1` using `AlgEquiv.restrictNormal_commutes σ K⟮ζ⟯ (AdjoinSimple.gen K ζ)`. Rewrite `h1` using `[← ha, algEquiv_pow_apply_of_apply_eq_pow hτ]`. Simplify using `using h1.symm`.
-/
theorem exists_apply_eq_pow_pow {n : ℕ} (hn : n ≠ 0) {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ n - 1)) (σ : Ω ≃ₐ[K] Ω) :
    ∃ a : ℕ, σ ζ = ζ ^ Nat.card 𝓀[K] ^ a := by
  obtain ⟨hE, -⟩ := isUnramifiedSubextension_adjoin hn hζ
  have := hE.1
  have := hE.isGalois
  obtain ⟨τ, hτ, -, htop⟩ := exists_frobenius_adjoin hn hζ
  have hmem : σ.restrictNormal K⟮ζ⟯ ∈ Subgroup.zpowers τ := htop ▸ Subgroup.mem_top _
  obtain ⟨a, ha⟩ := mem_powers_iff_mem_zpowers.2 hmem
  refine ⟨a, ?_⟩
  have h1 := AlgEquiv.restrictNormal_commutes σ K⟮ζ⟯ (AdjoinSimple.gen K ζ)
  rw [← ha, algEquiv_pow_apply_of_apply_eq_pow hτ] at h1
  simpa using h1.symm

/- English proof (translation)
Take `⟨hE, -⟩` from `isUnramifiedSubextension_adjoin hn hζ`. Use `hE.1` as an intermediate fact. Take `⟨τ, hτ, hord, -⟩` from `exists_frobenius_adjoin hn hζ`. Rewrite using `[← hord, ← pow_eq_pow_iff_modEq]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Establish `h' : (τ ^ a) (AdjoinSimple.gen K ζ) = (τ ^ b) (AdjoinSimple.gen K ζ)`. Rewrite using `[algEquiv_pow_apply_of_apply_eq_pow hτ, algEquiv_pow_apply_of_apply_eq_pow hτ]`. Conclude with `Subtype.ext (by simpa using h)`. Establish `h1 : (τ ^ b)⁻¹ * τ ^ a = 1`.

Use `algEquiv_eq_one_of_apply_eq (adjoin_gen_eq_top ζ) ?_` and prove the remaining obligations. Rewrite using `[AlgEquiv.mul_apply, h', ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]`. Conclude with `(inv_mul_eq_one.mp h1).symm`. Introduce `h`. Use `congrArg (fun ρ : K⟮ζ⟯ ≃ₐ[K] K⟮ζ⟯ ↦ ((ρ (AdjoinSimple.gen K ζ) : K⟮ζ⟯) : Ω)) h` as an intermediate fact.

Simplify `this` using `[algEquiv_pow_apply_of_apply_eq_pow hτ]`.
-/
theorem pow_pow_eq_pow_pow_iff {n : ℕ} (hn : n ≠ 0) {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ n - 1)) (a b : ℕ) :
    ζ ^ Nat.card 𝓀[K] ^ a = ζ ^ Nat.card 𝓀[K] ^ b ↔ a ≡ b [MOD n] := by
  obtain ⟨hE, -⟩ := isUnramifiedSubextension_adjoin hn hζ
  have := hE.1
  obtain ⟨τ, hτ, hord, -⟩ := exists_frobenius_adjoin hn hζ
  rw [← hord, ← pow_eq_pow_iff_modEq]
  constructor
  · intro h
    have h' : (τ ^ a) (AdjoinSimple.gen K ζ) = (τ ^ b) (AdjoinSimple.gen K ζ) := by
      rw [algEquiv_pow_apply_of_apply_eq_pow hτ, algEquiv_pow_apply_of_apply_eq_pow hτ]
      exact Subtype.ext (by simpa using h)
    have h1 : (τ ^ b)⁻¹ * τ ^ a = 1 := by
      refine algEquiv_eq_one_of_apply_eq (adjoin_gen_eq_top ζ) ?_
      rw [AlgEquiv.mul_apply, h', ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
    exact (inv_mul_eq_one.mp h1).symm
  · intro h
    have := congrArg (fun ρ : K⟮ζ⟯ ≃ₐ[K] K⟮ζ⟯ ↦ ((ρ (AdjoinSimple.gen K ζ) : K⟮ζ⟯) : Ω)) h
    simpa [algEquiv_pow_apply_of_apply_eq_pow hτ] using this

/- English proof (translation)
Establish `: NeZero (Nat.card 𝓀[K] ^ n - 1)` using `⟨by have := one_lt_card_residueField_pow (K := K) hn; omega⟩`. Take `⟨i, -, rfl⟩` from `hζ.eq_pow_of_pow_eq_one hξ`. Rewrite using `[map_pow, ha, ← pow_mul, ← pow_mul, mul_comm]`.
-/
theorem apply_eq_pow_pow_of_pow_eq_one {n : ℕ} (hn : n ≠ 0) {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ n - 1)) {σ : Ω ≃ₐ[K] Ω} {a : ℕ}
    (ha : σ ζ = ζ ^ Nat.card 𝓀[K] ^ a) {ξ : Ω} (hξ : ξ ^ (Nat.card 𝓀[K] ^ n - 1) = 1) :
    σ ξ = ξ ^ Nat.card 𝓀[K] ^ a := by
  have : NeZero (Nat.card 𝓀[K] ^ n - 1) := ⟨by have := one_lt_card_residueField_pow (K := K) hn; omega⟩
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hξ
  rw [map_pow, ha, ← pow_mul, ← pow_mul, mul_comm]

variable (K Ω) in

class HasUnramifiedRoots : Prop where
  exists_isPrimitiveRoot : ∀ n : ℕ, n ≠ 0 → ∃ ζ : Ω, IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ n - 1)

instance hasUnramifiedRoots_of_isSepClosed [IsSepClosed Ω] : HasUnramifiedRoots K Ω :=
  ⟨fun _ hn ↦ exists_isPrimitiveRoot_card_pow_sub_one (K := K) hn⟩

variable (K Ω) in

def unramifiedRoots : Set Ω :=
  {ξ | ∃ n : ℕ, n ≠ 0 ∧ ξ ^ (Nat.card 𝓀[K] ^ n - 1) = 1}

omit [Algebra K Ω] in

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨n, hn, hξ⟩`. Conclude with `⟨_, natCast_card_pow_sub_one_ne_zero hn, hξ⟩`. Introduce and unpack `⟨m, hm, hξ⟩`. Establish `hm0 : m ≠ 0` using `by rintro rfl; simp at hm`.

Use `Fintype.ofFinite 𝓀[K]` as an intermediate fact. Take `⟨p, hp⟩` from `CharP.exists 𝓀[K]`. Take `⟨k, hprime, hcard⟩` from `FiniteField.card 𝓀[K] p`. Establish `hpm : ¬ p ∣ m` using `fun h ↦ hm ((CharP.cast_eq_zero_iff 𝓀[K] p m).2 h)`. Establish `hcop : Nat.Coprime (Nat.card 𝓀[K]) m`.

Rewrite using `[Nat.card_eq_fintype_card, hcard]`. Conclude with `Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hprime).2 hpm)`. Establish `hdvd : m ∣ Nat.card 𝓀[K] ^ m.totient - 1` using `(Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ Nat.card_pos)).1 (Nat.ModEq.pow_totient hcop).symm`. Use `⟨m.totient, (Nat.totient_pos.2 (Nat.pos_of_ne_zero hm0)).ne', ?_⟩` and prove the remaining obligations. Take `⟨c, hc⟩` from `hdvd`.

Rewrite using `[hc, pow_mul, hξ, one_pow]`.
-/
theorem mem_unramifiedRoots_iff {ξ : Ω} :
    ξ ∈ unramifiedRoots K Ω ↔ ∃ m : ℕ, (m : 𝓀[K]) ≠ 0 ∧ ξ ^ m = 1 := by
  constructor
  · rintro ⟨n, hn, hξ⟩
    exact ⟨_, natCast_card_pow_sub_one_ne_zero hn, hξ⟩
  · rintro ⟨m, hm, hξ⟩
    have hm0 : m ≠ 0 := by rintro rfl; simp at hm
    have := Fintype.ofFinite 𝓀[K]
    obtain ⟨p, hp⟩ := CharP.exists 𝓀[K]
    obtain ⟨k, hprime, hcard⟩ := FiniteField.card 𝓀[K] p
    have hpm : ¬ p ∣ m := fun h ↦ hm ((CharP.cast_eq_zero_iff 𝓀[K] p m).2 h)
    have hcop : Nat.Coprime (Nat.card 𝓀[K]) m := by
      rw [Nat.card_eq_fintype_card, hcard]
      exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hprime).2 hpm)
    have hdvd : m ∣ Nat.card 𝓀[K] ^ m.totient - 1 :=
      (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ Nat.card_pos)).1 (Nat.ModEq.pow_totient hcop).symm
    refine ⟨m.totient, (Nat.totient_pos.2 (Nat.pos_of_ne_zero hm0)).ne', ?_⟩
    obtain ⟨c, hc⟩ := hdvd
    rw [hc, pow_mul, hξ, one_pow]

variable (K) in
open Classical in

def unramifiedCoord (σ : Ω ≃ₐ[K] Ω) (n : ℕ+) : ZMod n :=
  if h : ∃ a : ZMod n, ∀ ξ : Ω, ξ ^ (Nat.card 𝓀[K] ^ (n : ℕ) - 1) = 1 →
      σ ξ = ξ ^ Nat.card 𝓀[K] ^ a.val then h.choose else 0

/- English proof (translation)
Establish `hn : (n : ℕ) ≠ 0` using `n.ne_zero`. Take `⟨a₀, ha₀⟩` from `exists_apply_eq_pow_pow hn hζ σ`. Establish `hex : ∃ c : ZMod n, ∀ ξ : Ω, ξ ^ (Nat.card 𝓀[K] ^ (n : ℕ) - 1) = 1 → σ ξ = ξ ^ Nat.card 𝓀[K] ^ c.val`. Use `⟨a₀, fun ξ hξ ↦ apply_eq_pow_pow_of_pow_eq_one hn hζ ?_ hξ⟩` and prove the remaining obligations. Rewrite using `[ha₀, pow_pow_eq_pow_pow_iff hn hζ, ZMod.val_natCast]`.

Conclude with `(Nat.mod_modEq a₀ n).symm`. Establish `hc : unramifiedCoord K σ n = hex.choose` using `dif_pos hex`. Rewrite using `[hc, hex.choose_spec ζ hζ.pow_eq_one, pow_pow_eq_pow_pow_iff hn hζ, ← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val]`. Conclude with `eq_comm`.
-/
theorem natCast_eq_unramifiedCoord_iff {n : ℕ+} {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ (n : ℕ) - 1)) (σ : Ω ≃ₐ[K] Ω) (a : ℕ) :
    (a : ZMod n) = unramifiedCoord K σ n ↔ σ ζ = ζ ^ Nat.card 𝓀[K] ^ a := by
  have hn : (n : ℕ) ≠ 0 := n.ne_zero
  obtain ⟨a₀, ha₀⟩ := exists_apply_eq_pow_pow hn hζ σ
  have hex : ∃ c : ZMod n, ∀ ξ : Ω, ξ ^ (Nat.card 𝓀[K] ^ (n : ℕ) - 1) = 1 →
      σ ξ = ξ ^ Nat.card 𝓀[K] ^ c.val := by
    refine ⟨a₀, fun ξ hξ ↦ apply_eq_pow_pow_of_pow_eq_one hn hζ ?_ hξ⟩
    rw [ha₀, pow_pow_eq_pow_pow_iff hn hζ, ZMod.val_natCast]
    exact (Nat.mod_modEq a₀ n).symm
  have hc : unramifiedCoord K σ n = hex.choose := dif_pos hex
  rw [hc, hex.choose_spec ζ hζ.pow_eq_one, pow_pow_eq_pow_pow_iff hn hζ,
    ← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val]
  exact eq_comm

/- English proof (translation)
The claim follows from `(natCast_eq_unramifiedCoord_iff hζ σ _).1 (ZMod.natCast_zmod_val _)`.
-/
theorem apply_eq_pow_pow_unramifiedCoord {n : ℕ+} {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ (n : ℕ) - 1)) (σ : Ω ≃ₐ[K] Ω) :
    σ ζ = ζ ^ Nat.card 𝓀[K] ^ (unramifiedCoord K σ n).val :=
  (natCast_eq_unramifiedCoord_iff hζ σ _).1 (ZMod.natCast_zmod_val _)

variable [HasUnramifiedRoots K Ω]

/- English proof (translation)
Take `⟨ζ, hζ⟩` from `HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) n n.ne_zero`. Rewrite using `[natCast_eq_unramifiedCoord_iff hζ]`. Conclude with `⟨fun h ξ hξ ↦ apply_eq_pow_pow_of_pow_eq_one n.ne_zero hζ h hξ, fun h ↦ h ζ hζ.pow_eq_one⟩`.
-/
theorem natCast_eq_unramifiedCoord_iff_forall (σ : Ω ≃ₐ[K] Ω) (n : ℕ+) (a : ℕ) :
    (a : ZMod n) = unramifiedCoord K σ n ↔
      ∀ ξ : Ω, ξ ^ (Nat.card 𝓀[K] ^ (n : ℕ) - 1) = 1 → σ ξ = ξ ^ Nat.card 𝓀[K] ^ a := by
  obtain ⟨ζ, hζ⟩ := HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) n n.ne_zero
  rw [natCast_eq_unramifiedCoord_iff hζ]
  exact ⟨fun h ξ hξ ↦ apply_eq_pow_pow_of_pow_eq_one n.ne_zero hζ h hξ, fun h ↦ h ζ hζ.pow_eq_one⟩

/- English proof (translation)
Rewrite using `[← (natCast_eq_unramifiedCoord_iff_forall 1 n 0).2 (fun ξ _ ↦ by simp), Nat.cast_zero]`.
-/
theorem unramifiedCoord_one (n : ℕ+) : unramifiedCoord K (1 : Ω ≃ₐ[K] Ω) n = 0 := by
  rw [← (natCast_eq_unramifiedCoord_iff_forall 1 n 0).2 (fun ξ _ ↦ by simp), Nat.cast_zero]

/- English proof (translation)
Take `⟨ζ, hζ⟩` from `HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) n n.ne_zero`. Establish `h` using `(natCast_eq_unramifiedCoord_iff hζ (σ * τ) ((unramifiedCoord K σ n).val + (unramifiedCoord K τ n).val)).2 (by`. Rewrite using `[AlgEquiv.mul_apply, apply_eq_pow_pow_unramifiedCoord hζ τ, map_pow, apply_eq_pow_pow_unramifiedCoord hζ σ, ← pow_mul, ← pow_add])`. Rewrite using `[← h, Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]`.
-/
theorem unramifiedCoord_mul (σ τ : Ω ≃ₐ[K] Ω) (n : ℕ+) :
    unramifiedCoord K (σ * τ) n = unramifiedCoord K σ n + unramifiedCoord K τ n := by
  obtain ⟨ζ, hζ⟩ := HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) n n.ne_zero
  have h := (natCast_eq_unramifiedCoord_iff hζ (σ * τ)
    ((unramifiedCoord K σ n).val + (unramifiedCoord K τ n).val)).2 (by
      rw [AlgEquiv.mul_apply, apply_eq_pow_pow_unramifiedCoord hζ τ, map_pow,
        apply_eq_pow_pow_unramifiedCoord hζ σ, ← pow_mul, ← pow_add])
  rw [← h, Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]

/- English proof (translation)
Take `⟨ζ, hζ⟩` from `HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) n n.ne_zero`. Take `⟨ξ, hξ⟩` from `HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) m m.ne_zero`. Establish `hdvd : Nat.card 𝓀[K] ^ (m : ℕ) - 1 ∣ Nat.card 𝓀[K] ^ (n : ℕ) - 1`. Take `⟨k, hk⟩` from `h`. Rewrite using `[hk, pow_mul]`.

Simplify `Nat.sub_dvd_pow_sub_pow (Nat.card 𝓀[K] ^ (m : ℕ)) 1 k` using `[one_pow]`. Establish `hξn : ξ ^ (Nat.card 𝓀[K] ^ (n : ℕ) - 1) = 1`. Take `⟨c, hc⟩` from `hdvd`. Rewrite using `[hc, pow_mul, hξ.pow_eq_one, one_pow]`. Establish `key` using `apply_eq_pow_pow_of_pow_eq_one n.ne_zero hζ (apply_eq_pow_pow_unramifiedCoord hζ σ) hξn`.

Rewrite using `[ZMod.castHom_apply, ZMod.cast_eq_val]`. Conclude with `(natCast_eq_unramifiedCoord_iff hξ σ _).2 key`.
-/
theorem castHom_unramifiedCoord (σ : Ω ≃ₐ[K] Ω) {m n : ℕ+} (h : (m : ℕ) ∣ n) :
    ZMod.castHom h (ZMod m) (unramifiedCoord K σ n) = unramifiedCoord K σ m := by
  obtain ⟨ζ, hζ⟩ := HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) n n.ne_zero
  obtain ⟨ξ, hξ⟩ := HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) m m.ne_zero
  have hdvd : Nat.card 𝓀[K] ^ (m : ℕ) - 1 ∣ Nat.card 𝓀[K] ^ (n : ℕ) - 1 := by
    obtain ⟨k, hk⟩ := h
    rw [hk, pow_mul]
    simpa [one_pow] using Nat.sub_dvd_pow_sub_pow (Nat.card 𝓀[K] ^ (m : ℕ)) 1 k
  have hξn : ξ ^ (Nat.card 𝓀[K] ^ (n : ℕ) - 1) = 1 := by
    obtain ⟨c, hc⟩ := hdvd
    rw [hc, pow_mul, hξ.pow_eq_one, one_pow]
  have key := apply_eq_pow_pow_of_pow_eq_one n.ne_zero hζ
    (apply_eq_pow_pow_unramifiedCoord hζ σ) hξn
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]
  exact (natCast_eq_unramifiedCoord_iff hξ σ _).2 key

end Roots

section Degree

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [HasUnramifiedRoots K Ω]

variable (K Ω) in

def unramifiedDegree : (Ω ≃ₐ[K] Ω) →* Multiplicative ℤ̂ where
  toFun σ := Multiplicative.ofAdd ⟨fun n ↦ unramifiedCoord K σ n,
    mem_profiniteIntegers.2 fun _ _ h ↦ castHom_unramifiedCoord σ h⟩
  map_one' := by
    show Multiplicative.ofAdd _ = Multiplicative.ofAdd 0
    congr 1
    ext n
    show unramifiedCoord K 1 n = proj n 0
    rw [map_zero, unramifiedCoord_one]
  map_mul' σ τ := by
    show Multiplicative.ofAdd _ = Multiplicative.ofAdd (_ + _)
    congr 1
    ext n
    show unramifiedCoord K (σ * τ) n = proj n (_ + _)
    rw [map_add, unramifiedCoord_mul]
    rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem proj_toAdd_unramifiedDegree (σ : Ω ≃ₐ[K] Ω) (n : ℕ+) :
    proj n (Multiplicative.toAdd (unramifiedDegree K Ω σ)) = unramifiedCoord K σ n :=
  rfl

/- English proof (translation)
The claim follows from `Multiplicative.toAdd.injective (ProfiniteInteger.ext h)`.
-/
theorem multiplicative_ext {x y : Multiplicative ℤ̂}
    (h : ∀ n, proj n (Multiplicative.toAdd x) = proj n (Multiplicative.toAdd y)) : x = y :=
  Multiplicative.toAdd.injective (ProfiniteInteger.ext h)

/- English proof (translation)
Establish `h0 : unramifiedCoord K τ n = 0`. Rewrite using `[← (natCast_eq_unramifiedCoord_iff hζ τ 0).2 (by simpa using hτ), Nat.cast_zero]`. Rewrite using `[unramifiedCoord_mul, h0, add_zero]`.
-/
theorem unramifiedCoord_mul_of_apply_eq (σ : Ω ≃ₐ[K] Ω) {τ : Ω ≃ₐ[K] Ω} {n : ℕ+} {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ (n : ℕ) - 1)) (hτ : τ ζ = ζ) :
    unramifiedCoord K (σ * τ) n = unramifiedCoord K σ n := by
  have h0 : unramifiedCoord K τ n = 0 := by
    rw [← (natCast_eq_unramifiedCoord_iff hζ τ 0).2 (by simpa using hτ), Nat.cast_zero]
  rw [unramifiedCoord_mul, h0, add_zero]

/- English proof (translation)
Take `⟨ζ, hζ⟩` from `HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) n n.ne_zero`. Establish `hfin : FiniteDimensional K K⟮ζ⟯` using `(isUnramifiedSubextension_adjoin n.ne_zero hζ).1.1`. Use `((IsLocallyConstant.iff_eventually_eq _).2 fun σ ↦ ?_).continuous` and prove the remaining obligations. Use `open scoped Pointwise in`. Establish `hU : σ • (K⟮ζ⟯.fixingSubgroup : Set (Ω ≃ₐ[K] Ω)) ∈ nhds σ` using `(K⟮ζ⟯.fixingSubgroup_isOpen.smul σ).mem_nhds ⟨1, one_mem _, by simp⟩`.

Use `filter_upwards [hU] with ρ hρ`. Take `⟨τ, hτ, rfl⟩` from `hρ`. Conclude with `unramifiedCoord_mul_of_apply_eq σ hζ ((IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ ζ (mem_adjoin_simple_self K ζ))`.
-/
theorem continuous_unramifiedCoord (n : ℕ+) :
    Continuous fun σ : Ω ≃ₐ[K] Ω ↦ unramifiedCoord K σ n := by
  obtain ⟨ζ, hζ⟩ := HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) n n.ne_zero
  have hfin : FiniteDimensional K K⟮ζ⟯ := (isUnramifiedSubextension_adjoin n.ne_zero hζ).1.1
  refine ((IsLocallyConstant.iff_eventually_eq _).2 fun σ ↦ ?_).continuous
  open scoped Pointwise in
  have hU : σ • (K⟮ζ⟯.fixingSubgroup : Set (Ω ≃ₐ[K] Ω)) ∈ nhds σ :=
    (K⟮ζ⟯.fixingSubgroup_isOpen.smul σ).mem_nhds ⟨1, one_mem _, by simp⟩
  filter_upwards [hU] with ρ hρ
  obtain ⟨τ, hτ, rfl⟩ := hρ
  exact unramifiedCoord_mul_of_apply_eq σ hζ
    ((IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ ζ (mem_adjoin_simple_self K ζ))

/- English proof (translation)
The claim follows from `continuous_ofAdd.comp (Continuous.subtype_mk (continuous_pi fun n ↦ continuous_unramifiedCoord n) _)`.
-/
theorem continuous_unramifiedDegree : Continuous (unramifiedDegree K Ω) :=
  continuous_ofAdd.comp (Continuous.subtype_mk (continuous_pi fun n ↦ continuous_unramifiedCoord n) _)

/- English proof (translation)
Take `⟨ζ, hζ⟩` from `HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) n n.ne_zero`. Take `⟨hE, -⟩` from `isUnramifiedSubextension_adjoin n.ne_zero hζ`. Use `hE.1` as an intermediate fact. Take `⟨τ, hτ, -, -⟩` from `exists_frobenius_adjoin n.ne_zero hζ`. Use `⟨(τ ^ c.val).liftNormal Ω, ?_⟩` and prove the remaining obligations.

Establish `h1` using `AlgEquiv.liftNormal_commutes (τ ^ c.val) Ω (AdjoinSimple.gen K ζ)`. Rewrite `h1` using `[algEquiv_pow_apply_of_apply_eq_pow hτ]`. Establish `h2` using `(natCast_eq_unramifiedCoord_iff hζ ((τ ^ c.val).liftNormal Ω) c.val).2 (by simpa using h1)`. Rewrite using `[← h2, ZMod.natCast_zmod_val]`.
-/
theorem exists_unramifiedCoord_eq [Normal K Ω] (n : ℕ+) (c : ZMod n) :
    ∃ σ : Ω ≃ₐ[K] Ω, unramifiedCoord K σ n = c := by
  obtain ⟨ζ, hζ⟩ := HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) n n.ne_zero
  obtain ⟨hE, -⟩ := isUnramifiedSubextension_adjoin n.ne_zero hζ
  have := hE.1
  obtain ⟨τ, hτ, -, -⟩ := exists_frobenius_adjoin n.ne_zero hζ
  refine ⟨(τ ^ c.val).liftNormal Ω, ?_⟩
  have h1 := AlgEquiv.liftNormal_commutes (τ ^ c.val) Ω (AdjoinSimple.gen K ζ)
  rw [algEquiv_pow_apply_of_apply_eq_pow hτ] at h1
  have h2 := (natCast_eq_unramifiedCoord_iff hζ ((τ ^ c.val).liftNormal Ω) c.val).2
    (by simpa using h1)
  rw [← h2, ZMod.natCast_zmod_val]

/- English proof (translation)
Introduce `x`. Set `N : ℕ → ℕ+` to `fun k ↦ ⟨(k + 1).factorial, Nat.factorial_pos _⟩`. Set `S : ℕ → Set (Ω ≃ₐ[K] Ω)` to `fun k ↦ {σ | unramifiedCoord K σ (N k) = proj (N k) (Multiplicative.toAdd x)}`. Establish `hS : ∀ k, IsClosed (S k)` using `fun k ↦ isClosed_eq (continuous_unramifiedCoord _) continuous_const`. Establish `hdvd : ∀ k, (N k : ℕ) ∣ N (k + 1)` using `fun k ↦ Nat.factorial_dvd_factorial (by omega)`.

Establish `hmono : ∀ k, S (k + 1) ⊆ S k`. Introduce `k σ hσ`. Simplify using `only [S, Set.mem_ofPred_eq] at hσ ⊢`. Rewrite using `[← castHom_unramifiedCoord σ (hdvd k), hσ, castHom_proj]`. Establish `hne : ∀ k, (S k).Nonempty` using `fun k ↦ exists_unramifiedCoord_eq _ _`.

Take `⟨σ, hσ⟩` from `IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S hmono hne (hS 0).isCompact hS`. Rewrite `hσ` using `[Set.mem_iInter]`. Use `⟨σ, multiplicative_ext fun n ↦ ?_⟩` and prove the remaining obligations. Establish `hn : (n : ℕ) ∣ N ((n : ℕ) - 1)` using `by show (n : ℕ) ∣ ((n : ℕ) - 1 + 1).factorial`. Rewrite using `[Nat.sub_add_cancel n.pos]`.

Conclude with `Nat.dvd_factorial n.pos le_rfl`. Rewrite using `[proj_toAdd_unramifiedDegree, ← castHom_unramifiedCoord σ hn, hσ _, castHom_proj]`.
-/
theorem unramifiedDegree_surjective [IsGalois K Ω] : Function.Surjective (unramifiedDegree K Ω) := by
  intro x
  let N : ℕ → ℕ+ := fun k ↦ ⟨(k + 1).factorial, Nat.factorial_pos _⟩
  let S : ℕ → Set (Ω ≃ₐ[K] Ω) := fun k ↦
    {σ | unramifiedCoord K σ (N k) = proj (N k) (Multiplicative.toAdd x)}
  have hS : ∀ k, IsClosed (S k) := fun k ↦
    isClosed_eq (continuous_unramifiedCoord _) continuous_const
  have hdvd : ∀ k, (N k : ℕ) ∣ N (k + 1) := fun k ↦ Nat.factorial_dvd_factorial (by omega)
  have hmono : ∀ k, S (k + 1) ⊆ S k := by
    intro k σ hσ
    simp only [S, Set.mem_ofPred_eq] at hσ ⊢
    rw [← castHom_unramifiedCoord σ (hdvd k), hσ, castHom_proj]
  have hne : ∀ k, (S k).Nonempty := fun k ↦ exists_unramifiedCoord_eq _ _
  obtain ⟨σ, hσ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S hmono hne
    (hS 0).isCompact hS
  rw [Set.mem_iInter] at hσ
  refine ⟨σ, multiplicative_ext fun n ↦ ?_⟩
  have hn : (n : ℕ) ∣ N ((n : ℕ) - 1) := by
    show (n : ℕ) ∣ ((n : ℕ) - 1 + 1).factorial
    rw [Nat.sub_add_cancel n.pos]
    exact Nat.dvd_factorial n.pos le_rfl
  rw [proj_toAdd_unramifiedDegree, ← castHom_unramifiedCoord σ hn, hσ _, castHom_proj]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `h ξ ⟨n, hn, hξ⟩`. Establish `hc : unramifiedCoord K σ ⟨n, Nat.pos_of_ne_zero hn⟩ = a`. Use `congrArg (fun y ↦ proj ⟨n, Nat.pos_of_ne_zero hn⟩ (Multiplicative.toAdd y)) h` as an intermediate fact. Use `this.trans ?_` and prove the remaining obligations.

Rewrite using `[toAdd_ofAdd, map_natCast]`. Conclude with `(natCast_eq_unramifiedCoord_iff_forall σ ⟨n, Nat.pos_of_ne_zero hn⟩ a).1 hc.symm ξ hξ`. Introduce `h`. Use `multiplicative_ext fun n ↦ ?_` and prove the remaining obligations. Rewrite using `[proj_toAdd_unramifiedDegree, toAdd_ofAdd, map_natCast]`.

Conclude with `((natCast_eq_unramifiedCoord_iff_forall σ n a).2 fun ξ hξ ↦ h ξ ⟨n, n.ne_zero, hξ⟩).symm`.
-/
theorem unramifiedDegree_eq_ofAdd_natCast_iff (σ : Ω ≃ₐ[K] Ω) (a : ℕ) :
    unramifiedDegree K Ω σ = Multiplicative.ofAdd (a : ℤ̂) ↔
      ∀ ξ ∈ unramifiedRoots K Ω, σ ξ = ξ ^ Nat.card 𝓀[K] ^ a := by
  constructor
  · rintro h ξ ⟨n, hn, hξ⟩
    have hc : unramifiedCoord K σ ⟨n, Nat.pos_of_ne_zero hn⟩ = a := by
      have := congrArg (fun y ↦ proj ⟨n, Nat.pos_of_ne_zero hn⟩ (Multiplicative.toAdd y)) h
      refine this.trans ?_
      rw [toAdd_ofAdd, map_natCast]
    exact (natCast_eq_unramifiedCoord_iff_forall σ ⟨n, Nat.pos_of_ne_zero hn⟩ a).1 hc.symm ξ hξ
  · intro h
    refine multiplicative_ext fun n ↦ ?_
    rw [proj_toAdd_unramifiedDegree, toAdd_ofAdd, map_natCast]
    exact ((natCast_eq_unramifiedCoord_iff_forall σ n a).2
      fun ξ hξ ↦ h ξ ⟨n, n.ne_zero, hξ⟩).symm

/- English proof (translation)
Use `unramifiedDegree_eq_ofAdd_natCast_iff σ 0` as an intermediate fact. Simplify using `only [Nat.cast_zero, ofAdd_zero, pow_zero, pow_one] at this`. Conclude with `this`.
-/
theorem unramifiedDegree_eq_one_iff (σ : Ω ≃ₐ[K] Ω) :
    unramifiedDegree K Ω σ = 1 ↔ ∀ ξ ∈ unramifiedRoots K Ω, σ ξ = ξ := by
  have := unramifiedDegree_eq_ofAdd_natCast_iff σ 0
  simp only [Nat.cast_zero, ofAdd_zero, pow_zero, pow_one] at this
  exact this

/- English proof (translation)
Use `unramifiedDegree_eq_ofAdd_natCast_iff σ 1` as an intermediate fact. Simplify using `only [Nat.cast_one, pow_one] at this`. Conclude with `this`.
-/
theorem unramifiedDegree_eq_ofAdd_one_iff (σ : Ω ≃ₐ[K] Ω) :
    unramifiedDegree K Ω σ = Multiplicative.ofAdd 1 ↔
      ∀ ξ ∈ unramifiedRoots K Ω, σ ξ = ξ ^ Nat.card 𝓀[K] := by
  have := unramifiedDegree_eq_ofAdd_natCast_iff σ 1
  simp only [Nat.cast_one, pow_one] at this
  exact this

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [HasUnramifiedRoots K Ω] in

/- English proof (translation)
Rewrite using `[← Subgroup.zpowers_le, ← le_iff_le, adjoin_le_iff]`. Use `⟨fun h x hx ↦ (mem_fixedField_iff _ _).1 (h hx) σ (Subgroup.mem_zpowers σ), fun h x hx ↦ ?_⟩` and prove the remaining obligations. Use `(mem_fixedField_iff _ _).2 fun τ hτ ↦ ?_` and prove the remaining obligations. Establish `hσ : σ ∈ MulAction.stabilizer (Ω ≃ₐ[K] Ω) x` using `h x hx`. Conclude with `(Subgroup.zpowers_le.2 hσ) hτ`.
-/
theorem mem_fixingSubgroup_adjoin_iff {S : Set Ω} {σ : Ω ≃ₐ[K] Ω} :
    σ ∈ (adjoin K S).fixingSubgroup ↔ ∀ x ∈ S, σ x = x := by
  rw [← Subgroup.zpowers_le, ← le_iff_le, adjoin_le_iff]
  refine ⟨fun h x hx ↦ (mem_fixedField_iff _ _).1 (h hx) σ (Subgroup.mem_zpowers σ), fun h x hx ↦ ?_⟩
  refine (mem_fixedField_iff _ _).2 fun τ hτ ↦ ?_
  have hσ : σ ∈ MulAction.stabilizer (Ω ≃ₐ[K] Ω) x := h x hx
  exact (Subgroup.zpowers_le.2 hσ) hτ

end Degree

section MaximalUnramified

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

/- English proof (translation)
Take `⟨k, rfl⟩` from `h`. Rewrite using `[pow_mul]`. Simplify `Nat.sub_dvd_pow_sub_pow (q ^ m) 1 k` using `[one_pow]`.
-/
theorem pow_sub_one_dvd_pow_sub_one (q : ℕ) {m n : ℕ} (h : m ∣ n) : q ^ m - 1 ∣ q ^ n - 1 := by
  obtain ⟨k, rfl⟩ := h
  rw [pow_mul]
  simpa [one_pow] using Nat.sub_dvd_pow_sub_pow (q ^ m) 1 k

variable (K Ω) in

def maximalUnramifiedExtension : IntermediateField K Ω :=
  ⨆ E : {E : IntermediateField K Ω // IsUnramifiedSubextension E}, E.1

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

/- English proof (translation)
The claim follows from `le_iSup (fun E : {E : IntermediateField K Ω // IsUnramifiedSubextension E} ↦ E.1) ⟨E, hE⟩`.
-/
theorem IsUnramifiedSubextension.le_maximalUnramifiedExtension {E : IntermediateField K Ω}
    (hE : IsUnramifiedSubextension E) : E ≤ maximalUnramifiedExtension K Ω :=
  le_iSup (fun E : {E : IntermediateField K Ω // IsUnramifiedSubextension E} ↦ E.1) ⟨E, hE⟩

/- English proof (translation)
The claim follows from `(isUnramifiedSubextension_adjoin hn hζ).1.le_maximalUnramifiedExtension`.
-/
theorem adjoin_le_maximalUnramifiedExtension {n : ℕ} (hn : n ≠ 0) {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ n - 1)) : K⟮ζ⟯ ≤ maximalUnramifiedExtension K Ω :=
  (isUnramifiedSubextension_adjoin hn hζ).1.le_maximalUnramifiedExtension

instance normal_maximalUnramifiedExtension : Normal K (maximalUnramifiedExtension K Ω) := by
  have : ∀ E : {E : IntermediateField K Ω // IsUnramifiedSubextension E}, Normal K E.1 :=
    fun E ↦ E.2.isGalois.to_normal
  unfold maximalUnramifiedExtension
  infer_instance

instance isGalois_maximalUnramifiedExtension [Algebra.IsSeparable K Ω] :
    IsGalois K (maximalUnramifiedExtension K Ω) :=
  have := Algebra.isSeparable_tower_bot_of_isSeparable K (maximalUnramifiedExtension K Ω) Ω
  isGalois_iff.2 ⟨this, inferInstance⟩

variable [HasUnramifiedRoots K Ω]

/- English proof (translation)
Use `hE.1` as an intermediate fact. Establish `hm : Module.finrank K E ≠ 0` using `Module.finrank_pos.ne'`. Take `⟨ξ, hξ⟩` from `HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) _ hm`. Rewrite using `[hE.eq_adjoin rfl hm hξ, adjoin_simple_le_iff]`. Establish `hξn : ξ ^ (Nat.card 𝓀[K] ^ n - 1) = 1`.

Take `⟨c, hc⟩` from `pow_sub_one_dvd_pow_sub_one (Nat.card 𝓀[K]) hdvd`. Rewrite using `[hc, pow_mul, hξ.pow_eq_one, one_pow]`. Establish `: NeZero (Nat.card 𝓀[K] ^ n - 1)` using `⟨by have := one_lt_card_residueField_pow (K := K) hn; omega⟩`. Take `⟨i, -, rfl⟩` from `hζ.eq_pow_of_pow_eq_one hξn`. Conclude with `pow_mem (mem_adjoin_simple_self K ζ) i`.
-/
theorem IsUnramifiedSubextension.le_adjoin {E : IntermediateField K Ω}
    (hE : IsUnramifiedSubextension E) {n : ℕ} (hn : n ≠ 0) (hdvd : Module.finrank K E ∣ n) {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ n - 1)) : E ≤ K⟮ζ⟯ := by
  have := hE.1
  have hm : Module.finrank K E ≠ 0 := Module.finrank_pos.ne'
  obtain ⟨ξ, hξ⟩ := HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) _ hm
  rw [hE.eq_adjoin rfl hm hξ, adjoin_simple_le_iff]
  have hξn : ξ ^ (Nat.card 𝓀[K] ^ n - 1) = 1 := by
    obtain ⟨c, hc⟩ := pow_sub_one_dvd_pow_sub_one (Nat.card 𝓀[K]) hdvd
    rw [hc, pow_mul, hξ.pow_eq_one, one_pow]
  have : NeZero (Nat.card 𝓀[K] ^ n - 1) :=
    ⟨by have := one_lt_card_residueField_pow (K := K) hn; omega⟩
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hξn
  exact pow_mem (mem_adjoin_simple_self K ζ) i

/- English proof (translation)
Introduce and unpack `⟨E₁, h₁⟩ ⟨E₂, h₂⟩`. Use `h₁.1` as an intermediate fact. Use `h₂.1` as an intermediate fact. Establish `hn : Module.finrank K E₁ * Module.finrank K E₂ ≠ 0` using `mul_ne_zero Module.finrank_pos.ne' Module.finrank_pos.ne'`. Take `⟨ζ, hζ⟩` from `HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) _ hn`.

Conclude with `⟨⟨K⟮ζ⟯, (isUnramifiedSubextension_adjoin hn hζ).1⟩, h₁.le_adjoin hn (dvd_mul_right _ _) hζ, h₂.le_adjoin hn (dvd_mul_left _ _) hζ⟩`.
-/
theorem directed_isUnramifiedSubextension :
    Directed (· ≤ ·) (fun E : {E : IntermediateField K Ω // IsUnramifiedSubextension E} ↦ E.1) := by
  rintro ⟨E₁, h₁⟩ ⟨E₂, h₂⟩
  have := h₁.1
  have := h₂.1
  have hn : Module.finrank K E₁ * Module.finrank K E₂ ≠ 0 :=
    mul_ne_zero Module.finrank_pos.ne' Module.finrank_pos.ne'
  obtain ⟨ζ, hζ⟩ := HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) _ hn
  exact ⟨⟨K⟮ζ⟯, (isUnramifiedSubextension_adjoin hn hζ).1⟩,
    h₁.le_adjoin hn (dvd_mul_right _ _) hζ, h₂.le_adjoin hn (dvd_mul_left _ _) hζ⟩

/- English proof (translation)
Establish `: Nonempty {E : IntermediateField K Ω // IsUnramifiedSubextension E}`. Take `⟨ζ, hζ⟩` from `HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) 1 one_ne_zero`. Conclude with `⟨⟨K⟮ζ⟯, (isUnramifiedSubextension_adjoin one_ne_zero hζ).1⟩⟩`. Conclude with `coe_iSup_of_directed directed_isUnramifiedSubextension`.
-/
theorem coe_maximalUnramifiedExtension : (maximalUnramifiedExtension K Ω : Set Ω) =
    ⋃ E : {E : IntermediateField K Ω // IsUnramifiedSubextension E}, (E.1 : Set Ω) := by
  have : Nonempty {E : IntermediateField K Ω // IsUnramifiedSubextension E} := by
    obtain ⟨ζ, hζ⟩ := HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) 1 one_ne_zero
    exact ⟨⟨K⟮ζ⟯, (isUnramifiedSubextension_adjoin one_ne_zero hζ).1⟩⟩
  exact coe_iSup_of_directed directed_isUnramifiedSubextension

/- English proof (translation)
Rewrite using `[← SetLike.mem_coe, coe_maximalUnramifiedExtension, Set.mem_iUnion]`. Conclude with `⟨fun ⟨E, h⟩ ↦ ⟨E.1, E.2, h⟩, fun ⟨E, hE, h⟩ ↦ ⟨⟨E, hE⟩, h⟩⟩`.
-/
theorem mem_maximalUnramifiedExtension_iff {x : Ω} :
    x ∈ maximalUnramifiedExtension K Ω ↔ ∃ E : IntermediateField K Ω, IsUnramifiedSubextension E ∧ x ∈ E := by
  rw [← SetLike.mem_coe, coe_maximalUnramifiedExtension, Set.mem_iUnion]
  exact ⟨fun ⟨E, h⟩ ↦ ⟨E.1, E.2, h⟩, fun ⟨E, hE, h⟩ ↦ ⟨⟨E, hE⟩, h⟩⟩

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Use `iSup_le fun E ↦ ?_` and prove the remaining obligations. Use `E.2.1` as an intermediate fact. Establish `hn : Module.finrank K E.1 ≠ 0` using `Module.finrank_pos.ne'`. Take `⟨ζ, hζ⟩` from `HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) _ hn`.

Rewrite using `[E.2.eq_adjoin rfl hn hζ, adjoin_simple_le_iff]`. Conclude with `subset_adjoin K _ ⟨_, hn, hζ.pow_eq_one⟩`. Rewrite using `[adjoin_le_iff]`. Introduce and unpack `ξ ⟨n, hn, hξ⟩`. Take `⟨ζ, hζ⟩` from `HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) n hn`.

Establish `: NeZero (Nat.card 𝓀[K] ^ n - 1)` using `⟨by have := one_lt_card_residueField_pow (K := K) hn; omega⟩`. Take `⟨i, -, rfl⟩` from `hζ.eq_pow_of_pow_eq_one hξ`. Conclude with `adjoin_le_maximalUnramifiedExtension hn hζ (pow_mem (mem_adjoin_simple_self K ζ) i)`.
-/
theorem maximalUnramifiedExtension_eq_adjoin :
    maximalUnramifiedExtension K Ω = adjoin K (unramifiedRoots K Ω) := by
  apply le_antisymm
  · refine iSup_le fun E ↦ ?_
    have := E.2.1
    have hn : Module.finrank K E.1 ≠ 0 := Module.finrank_pos.ne'
    obtain ⟨ζ, hζ⟩ := HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) _ hn
    rw [E.2.eq_adjoin rfl hn hζ, adjoin_simple_le_iff]
    exact subset_adjoin K _ ⟨_, hn, hζ.pow_eq_one⟩
  · rw [adjoin_le_iff]
    rintro ξ ⟨n, hn, hξ⟩
    obtain ⟨ζ, hζ⟩ := HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) n hn
    have : NeZero (Nat.card 𝓀[K] ^ n - 1) :=
      ⟨by have := one_lt_card_residueField_pow (K := K) hn; omega⟩
    obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hξ
    exact adjoin_le_maximalUnramifiedExtension hn hζ (pow_mem (mem_adjoin_simple_self K ζ) i)

/- English proof (translation)
Rewrite using `[maximalUnramifiedExtension_eq_adjoin]`. Conclude with `subset_adjoin K _`.
-/
theorem unramifiedRoots_subset_maximalUnramifiedExtension :
    unramifiedRoots K Ω ⊆ maximalUnramifiedExtension K Ω := by
  rw [maximalUnramifiedExtension_eq_adjoin]
  exact subset_adjoin K _

instance hasUnramifiedRoots_maximalUnramifiedExtension : HasUnramifiedRoots K (maximalUnramifiedExtension K Ω) :=
  ⟨fun n hn ↦ by
    obtain ⟨ζ, hζ⟩ := HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) n hn
    exact ⟨⟨ζ, unramifiedRoots_subset_maximalUnramifiedExtension ⟨n, hn, hζ.pow_eq_one⟩⟩,
      hζ.of_map_of_injective (f := (maximalUnramifiedExtension K Ω).val) Subtype.val_injective⟩⟩

/- English proof (translation)
Use extensionality with `σ`. Rewrite using `[MonoidHom.mem_ker, unramifiedDegree_eq_one_iff, maximalUnramifiedExtension_eq_adjoin, mem_fixingSubgroup_adjoin_iff]`.
-/
theorem ker_unramifiedDegree :
    (unramifiedDegree K Ω).ker = (maximalUnramifiedExtension K Ω).fixingSubgroup := by
  ext σ
  rw [MonoidHom.mem_ker, unramifiedDegree_eq_one_iff, maximalUnramifiedExtension_eq_adjoin,
    mem_fixingSubgroup_adjoin_iff]

/- English proof (translation)
Use `multiplicative_ext fun n ↦ ?_` and prove the remaining obligations. Rewrite using `[proj_toAdd_unramifiedDegree, proj_toAdd_unramifiedDegree]`. Take `⟨ζ, hζ⟩` from `HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) n n.ne_zero`. Establish `hζE : ζ ∈ maximalUnramifiedExtension K Ω` using `unramifiedRoots_subset_maximalUnramifiedExtension ⟨n, n.ne_zero, hζ.pow_eq_one⟩`. Establish `hζ' : IsPrimitiveRoot (⟨ζ, hζE⟩ : maximalUnramifiedExtension K Ω) (Nat.card 𝓀[K] ^ (n : ℕ) - 1)` using `hζ.of_map_of_injective (f := (maximalUnramifiedExtension K Ω).val) Subtype.val_injective`.

Rewrite using `[← (natCast_eq_unramifiedCoord_iff hζ' _ (unramifiedCoord K σ n).val).2 ?_, ZMod.natCast_zmod_val]`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `h1` using `AlgEquiv.restrictNormal_commutes σ (maximalUnramifiedExtension K Ω) ⟨ζ, hζE⟩`. Simplify using `only [IntermediateField.algebraMap_apply] at h1`. Rewrite using `[h1]`.

Simplify using `using apply_eq_pow_pow_unramifiedCoord hζ σ`.
-/
theorem unramifiedDegree_restrictNormal (σ : Ω ≃ₐ[K] Ω) :
    unramifiedDegree K (maximalUnramifiedExtension K Ω) (σ.restrictNormal (maximalUnramifiedExtension K Ω)) =
      unramifiedDegree K Ω σ := by
  refine multiplicative_ext fun n ↦ ?_
  rw [proj_toAdd_unramifiedDegree, proj_toAdd_unramifiedDegree]
  obtain ⟨ζ, hζ⟩ := HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) n n.ne_zero
  have hζE : ζ ∈ maximalUnramifiedExtension K Ω :=
    unramifiedRoots_subset_maximalUnramifiedExtension ⟨n, n.ne_zero, hζ.pow_eq_one⟩
  have hζ' : IsPrimitiveRoot (⟨ζ, hζE⟩ : maximalUnramifiedExtension K Ω) (Nat.card 𝓀[K] ^ (n : ℕ) - 1) :=
    hζ.of_map_of_injective (f := (maximalUnramifiedExtension K Ω).val) Subtype.val_injective
  rw [← (natCast_eq_unramifiedCoord_iff hζ' _ (unramifiedCoord K σ n).val).2 ?_,
    ZMod.natCast_zmod_val]
  apply Subtype.ext
  have h1 := AlgEquiv.restrictNormal_commutes σ (maximalUnramifiedExtension K Ω) ⟨ζ, hζE⟩
  simp only [IntermediateField.algebraMap_apply] at h1
  rw [h1]
  simpa using apply_eq_pow_pow_unramifiedCoord hζ σ

variable [IsGalois K Ω]

/- English proof (translation)
Introduce `x`. Take `⟨σ, rfl⟩` from `unramifiedDegree_surjective (K := K) (Ω := Ω) x`. Conclude with `⟨_, unramifiedDegree_restrictNormal σ⟩`.
-/
theorem unramifiedDegree_maximalUnramifiedExtension_surjective :
    Function.Surjective (unramifiedDegree K (maximalUnramifiedExtension K Ω)) := by
  intro x
  obtain ⟨σ, rfl⟩ := unramifiedDegree_surjective (K := K) (Ω := Ω) x
  exact ⟨_, unramifiedDegree_restrictNormal σ⟩

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_one]`. Introduce `ρ hρ`. Take `⟨σ, rfl⟩` from `AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := maximalUnramifiedExtension K Ω) (E := Ω) ρ`. Establish `hσ : σ ∈ (unramifiedDegree K Ω).ker`. Rewrite using `[MonoidHom.mem_ker, ← unramifiedDegree_restrictNormal]`.

Conclude with `hρ`. Rewrite `hσ` using `[ker_unramifiedDegree, ← IntermediateField.restrictNormalHom_ker]`. Conclude with `MonoidHom.mem_ker.1 hσ`.
-/
theorem unramifiedDegree_maximalUnramifiedExtension_injective :
    Function.Injective (unramifiedDegree K (maximalUnramifiedExtension K Ω)) := by
  rw [injective_iff_map_eq_one]
  intro ρ hρ
  obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K)
    (K₁ := maximalUnramifiedExtension K Ω) (E := Ω) ρ
  have hσ : σ ∈ (unramifiedDegree K Ω).ker := by
    rw [MonoidHom.mem_ker, ← unramifiedDegree_restrictNormal]
    exact hρ
  rw [ker_unramifiedDegree, ← IntermediateField.restrictNormalHom_ker] at hσ
  exact MonoidHom.mem_ker.1 hσ

variable (K Ω) in

def maximalUnramifiedExtensionGaloisEquiv :
    (maximalUnramifiedExtension K Ω ≃ₐ[K] maximalUnramifiedExtension K Ω) ≃ₜ* Multiplicative ℤ̂ :=
  let e : (maximalUnramifiedExtension K Ω ≃ₐ[K] maximalUnramifiedExtension K Ω) ≃* Multiplicative ℤ̂ :=
    MulEquiv.ofBijective (unramifiedDegree K (maximalUnramifiedExtension K Ω))
      ⟨unramifiedDegree_maximalUnramifiedExtension_injective, unramifiedDegree_maximalUnramifiedExtension_surjective⟩
  { e with
    continuous_toFun := continuous_unramifiedDegree
    continuous_invFun :=
      (Continuous.homeoOfEquivCompactToT2 (f := e.toEquiv) continuous_unramifiedDegree).symm.continuous }

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem maximalUnramifiedExtensionGaloisEquiv_apply (ρ : maximalUnramifiedExtension K Ω ≃ₐ[K] maximalUnramifiedExtension K Ω) :
    maximalUnramifiedExtensionGaloisEquiv K Ω ρ = unramifiedDegree K (maximalUnramifiedExtension K Ω) ρ :=
  rfl

variable (K Ω) in

def maximalUnramifiedExtensionFrobenius : maximalUnramifiedExtension K Ω ≃ₐ[K] maximalUnramifiedExtension K Ω :=
  (maximalUnramifiedExtensionGaloisEquiv K Ω).symm (Multiplicative.ofAdd 1)

/- English proof (translation)
The claim follows from `(maximalUnramifiedExtensionGaloisEquiv K Ω).apply_symm_apply _`.
-/
theorem unramifiedDegree_maximalUnramifiedExtensionFrobenius :
    unramifiedDegree K (maximalUnramifiedExtension K Ω) (maximalUnramifiedExtensionFrobenius K Ω) =
      Multiplicative.ofAdd 1 :=
  (maximalUnramifiedExtensionGaloisEquiv K Ω).apply_symm_apply _

/- English proof (translation)
Rewrite using `[← unramifiedDegree_eq_ofAdd_one_iff, ← unramifiedDegree_maximalUnramifiedExtensionFrobenius (K := K) (Ω := Ω)]`. Conclude with `unramifiedDegree_maximalUnramifiedExtension_injective.eq_iff.symm`.
-/
theorem eq_maximalUnramifiedExtensionFrobenius_iff (ρ : maximalUnramifiedExtension K Ω ≃ₐ[K] maximalUnramifiedExtension K Ω) :
    ρ = maximalUnramifiedExtensionFrobenius K Ω ↔
      ∀ ξ ∈ unramifiedRoots K (maximalUnramifiedExtension K Ω), ρ ξ = ξ ^ Nat.card 𝓀[K] := by
  rw [← unramifiedDegree_eq_ofAdd_one_iff,
    ← unramifiedDegree_maximalUnramifiedExtensionFrobenius (K := K) (Ω := Ω)]
  exact unramifiedDegree_maximalUnramifiedExtension_injective.eq_iff.symm

/- English proof (translation)
The claim follows from `(eq_maximalUnramifiedExtensionFrobenius_iff _).1 rfl ξ hξ`.
-/
theorem maximalUnramifiedExtensionFrobenius_apply {ξ : maximalUnramifiedExtension K Ω}
    (hξ : ξ ∈ unramifiedRoots K (maximalUnramifiedExtension K Ω)) :
    maximalUnramifiedExtensionFrobenius K Ω ξ = ξ ^ Nat.card 𝓀[K] :=
  (eq_maximalUnramifiedExtensionFrobenius_iff _).1 rfl ξ hξ

/- English proof (translation)
The claim follows from `maximalUnramifiedExtensionFrobenius_apply (mem_unramifiedRoots_iff.2 ⟨m, hm, hξ⟩)`.
-/
theorem maximalUnramifiedExtensionFrobenius_apply_of_pow_eq_one {ξ : maximalUnramifiedExtension K Ω} {m : ℕ}
    (hm : (m : 𝓀[K]) ≠ 0) (hξ : ξ ^ m = 1) :
    maximalUnramifiedExtensionFrobenius K Ω ξ = ξ ^ Nat.card 𝓀[K] :=
  maximalUnramifiedExtensionFrobenius_apply (mem_unramifiedRoots_iff.2 ⟨m, hm, hξ⟩)

/- English proof (translation)
Rewrite using `[← unramifiedDegree_restrictNormal, ← unramifiedDegree_maximalUnramifiedExtensionFrobenius (K := K) (Ω := Ω)]`. Conclude with `unramifiedDegree_maximalUnramifiedExtension_injective.eq_iff.symm`.
-/
theorem restrictNormal_eq_maximalUnramifiedExtensionFrobenius_iff (σ : Ω ≃ₐ[K] Ω) :
    σ.restrictNormal (maximalUnramifiedExtension K Ω) = maximalUnramifiedExtensionFrobenius K Ω ↔
      unramifiedDegree K Ω σ = Multiplicative.ofAdd 1 := by
  rw [← unramifiedDegree_restrictNormal, ← unramifiedDegree_maximalUnramifiedExtensionFrobenius (K := K) (Ω := Ω)]
  exact unramifiedDegree_maximalUnramifiedExtension_injective.eq_iff.symm

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [HasUnramifiedRoots K Ω]
  [IsGalois K Ω] in

/- English proof (translation)
Establish `h : (Subgroup.zpowers (Multiplicative.ofAdd (1 : ℤ̂)) : Set (Multiplicative ℤ̂)) = Multiplicative.ofAdd '' Set.range (Int.cast : ℤ → ℤ̂)`. Use extensionality with `y`. Simplify using `only [SetLike.mem_coe, Subgroup.mem_zpowers_iff, Set.mem_image, Set.mem_range]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨k, rfl⟩`.

Conclude with `⟨k, ⟨k, rfl⟩, by rw [← ofAdd_zsmul, zsmul_one]⟩`. Introduce and unpack `⟨_, ⟨k, rfl⟩, rfl⟩`. Conclude with `⟨k, by rw [← ofAdd_zsmul, zsmul_one]⟩`. Rewrite using `[h]`. Conclude with `Multiplicative.ofAdd.surjective.denseRange.dense_image continuous_ofAdd denseRange_intCast`.
-/
theorem dense_zpowers_ofAdd_one :
    Dense (Subgroup.zpowers (Multiplicative.ofAdd (1 : ℤ̂)) : Set (Multiplicative ℤ̂)) := by
  have h : (Subgroup.zpowers (Multiplicative.ofAdd (1 : ℤ̂)) : Set (Multiplicative ℤ̂)) =
      Multiplicative.ofAdd '' Set.range (Int.cast : ℤ → ℤ̂) := by
    ext y
    simp only [SetLike.mem_coe, Subgroup.mem_zpowers_iff, Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k, ⟨k, rfl⟩, by rw [← ofAdd_zsmul, zsmul_one]⟩
    · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
      exact ⟨k, by rw [← ofAdd_zsmul, zsmul_one]⟩
  rw [h]
  exact Multiplicative.ofAdd.surjective.denseRange.dense_image continuous_ofAdd denseRange_intCast

/- English proof (translation)
Establish `h : (Subgroup.zpowers (maximalUnramifiedExtensionFrobenius K Ω) : Set (maximalUnramifiedExtension K Ω ≃ₐ[K] maximalUnramifiedExtension K Ω)) = (maximalUnramifiedExtensionGaloisEquiv K Ω).symm '' (Subgroup.zpowers (Multiplicative.ofAdd (1 : ℤ̂)) : Set (Multiplicative ℤ̂))`. Use extensionality with `ρ`. Simplify using `only [SetLike.mem_coe, Subgroup.mem_zpowers_iff, Set.mem_image]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨k, rfl⟩`.

Conclude with `⟨_, ⟨k, rfl⟩, by rw [map_zpow]; rfl⟩`. Introduce and unpack `⟨_, ⟨k, rfl⟩, rfl⟩`. Conclude with `⟨k, by rw [map_zpow]; rfl⟩`. Rewrite using `[h]`. Conclude with `(maximalUnramifiedExtensionGaloisEquiv K Ω).symm.surjective.denseRange.dense_image (maximalUnramifiedExtensionGaloisEquiv K Ω).symm.continuous dense_zpowers_ofAdd_one`.
-/
theorem dense_zpowers_maximalUnramifiedExtensionFrobenius :
    Dense (Subgroup.zpowers (maximalUnramifiedExtensionFrobenius K Ω) :
      Set (maximalUnramifiedExtension K Ω ≃ₐ[K] maximalUnramifiedExtension K Ω)) := by
  have h : (Subgroup.zpowers (maximalUnramifiedExtensionFrobenius K Ω) :
      Set (maximalUnramifiedExtension K Ω ≃ₐ[K] maximalUnramifiedExtension K Ω)) =
      (maximalUnramifiedExtensionGaloisEquiv K Ω).symm ''
        (Subgroup.zpowers (Multiplicative.ofAdd (1 : ℤ̂)) : Set (Multiplicative ℤ̂)) := by
    ext ρ
    simp only [SetLike.mem_coe, Subgroup.mem_zpowers_iff, Set.mem_image]
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨_, ⟨k, rfl⟩, by rw [map_zpow]; rfl⟩
    · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
      exact ⟨k, by rw [map_zpow]; rfl⟩
  rw [h]
  exact (maximalUnramifiedExtensionGaloisEquiv K Ω).symm.surjective.denseRange.dense_image
    (maximalUnramifiedExtensionGaloisEquiv K Ω).symm.continuous dense_zpowers_ofAdd_one

/- English proof (translation)
The claim follows from `SetLike.coe_injective (by rw [Subgroup.topologicalClosure_coe, dense_zpowers_maximalUnramifiedExtensionFrobenius.closure_eq, Subgroup.coe_top])`.
-/
theorem topologicalClosure_zpowers_maximalUnramifiedExtensionFrobenius :
    (Subgroup.zpowers (maximalUnramifiedExtensionFrobenius K Ω)).topologicalClosure = ⊤ :=
  SetLike.coe_injective (by
    rw [Subgroup.topologicalClosure_coe, dense_zpowers_maximalUnramifiedExtensionFrobenius.closure_eq,
      Subgroup.coe_top])

end MaximalUnramified

section SeparableClosure

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω]

instance hasUnramifiedRoots_of_isSepClosure [IsSepClosure K Ω] : HasUnramifiedRoots K Ω :=
  have := IsSepClosure.sep_closed K (K := Ω)
  inferInstance

/- English proof (translation)
Assemble the required witnesses or components as `⟨continuous_unramifiedDegree, unramifiedDegree_surjective, ker_unramifiedDegree⟩`.
-/
theorem unramifiedDegree_spec [IsSepClosure K Ω] :
    Continuous (unramifiedDegree K Ω) ∧ Function.Surjective (unramifiedDegree K Ω) ∧
      (unramifiedDegree K Ω).ker = (maximalUnramifiedExtension K Ω).fixingSubgroup :=
  ⟨continuous_unramifiedDegree, unramifiedDegree_surjective, ker_unramifiedDegree⟩

end SeparableClosure

section Finite

section Card

variable (K M : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [Algebra K M] [ValuativeExtension K M] [FiniteDimensional K M]

/- English proof (translation)
Use `Fintype.ofFinite 𝓀[K]` as an intermediate fact. Use `Fintype.ofFinite 𝓀[M]` as an intermediate fact. Rewrite using `[residueDegree_eq_finrank, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := 𝓀[K]) (V := 𝓀[M])]`.
-/
theorem card_residueField_eq_pow_residueDegree :
    Nat.card 𝓀[M] = Nat.card 𝓀[K] ^ residueDegree K M := by
  have := Fintype.ofFinite 𝓀[K]
  have := Fintype.ofFinite 𝓀[M]
  rw [residueDegree_eq_finrank, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Module.card_eq_pow_finrank (K := 𝓀[K]) (V := 𝓀[M])]

end Card

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosed Ω]
  (L : IntermediateField K Ω) [FiniteDimensional K L]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L]

/- English proof (translation)
Establish `hQ` using `card_residueField_eq_pow_residueDegree K L`. Establish `key : ((residueDegree K L * (unramifiedCoord L (fixingSubgroupEquiv L σ) n).val : ℕ) : ZMod n) = unramifiedCoord K (σ : Ω ≃ₐ[K] Ω) n`. Rewrite using `[natCast_eq_unramifiedCoord_iff_forall]`. Introduce `ξ hξ`. Establish `hξ' : ξ ^ (Nat.card 𝓀[L] ^ (n : ℕ) - 1) = 1`.

Rewrite using `[hQ, ← pow_mul]`. Take `⟨c, hc⟩` from `pow_sub_one_dvd_pow_sub_one (Nat.card 𝓀[K]) (dvd_mul_left (n : ℕ) (residueDegree K L))`. Rewrite using `[hc, pow_mul, hξ, one_pow]`. Establish `h` using `(natCast_eq_unramifiedCoord_iff_forall (K := L) (fixingSubgroupEquiv L σ) n (unramifiedCoord L (fixingSubgroupEquiv L σ) n).val).1 (ZMod.natCast_zmod_val _) ξ hξ'`. Rewrite `h` using `[hQ, ← pow_mul]`.

Conclude with `h`. Rewrite using `[← key, Nat.cast_mul, ZMod.natCast_zmod_val]`.
-/
theorem unramifiedCoord_fixingSubgroup (σ : L.fixingSubgroup) (n : ℕ+) :
    unramifiedCoord K (σ : Ω ≃ₐ[K] Ω) n =
      (residueDegree K L : ZMod n) * unramifiedCoord L (fixingSubgroupEquiv L σ) n := by
  have hQ := card_residueField_eq_pow_residueDegree K L
  have key : ((residueDegree K L * (unramifiedCoord L (fixingSubgroupEquiv L σ) n).val : ℕ) :
      ZMod n) = unramifiedCoord K (σ : Ω ≃ₐ[K] Ω) n := by
    rw [natCast_eq_unramifiedCoord_iff_forall]
    intro ξ hξ
    have hξ' : ξ ^ (Nat.card 𝓀[L] ^ (n : ℕ) - 1) = 1 := by
      rw [hQ, ← pow_mul]
      obtain ⟨c, hc⟩ := pow_sub_one_dvd_pow_sub_one (Nat.card 𝓀[K])
        (dvd_mul_left (n : ℕ) (residueDegree K L))
      rw [hc, pow_mul, hξ, one_pow]
    have h := (natCast_eq_unramifiedCoord_iff_forall (K := L) (fixingSubgroupEquiv L σ) n
      (unramifiedCoord L (fixingSubgroupEquiv L σ) n).val).1 (ZMod.natCast_zmod_val _) ξ hξ'
    rw [hQ, ← pow_mul] at h
    exact h
  rw [← key, Nat.cast_mul, ZMod.natCast_zmod_val]

/- English proof (translation)
Use `multiplicative_ext fun n ↦ ?_` and prove the remaining obligations. Rewrite using `[proj_toAdd_unramifiedDegree, toAdd_pow, map_nsmul, proj_toAdd_unramifiedDegree, nsmul_eq_mul, unramifiedCoord_fixingSubgroup]`.
-/
theorem unramifiedDegree_fixingSubgroup (σ : L.fixingSubgroup) :
    unramifiedDegree K Ω σ = unramifiedDegree L Ω (fixingSubgroupEquiv L σ) ^ residueDegree K L := by
  refine multiplicative_ext fun n ↦ ?_
  rw [proj_toAdd_unramifiedDegree, toAdd_pow, map_nsmul, proj_toAdd_unramifiedDegree, nsmul_eq_mul,
    unramifiedCoord_fixingSubgroup]

variable [IsGalois K Ω]

/- English proof (translation)
Use `IsGalois.tower_top_of_isGalois K L Ω` as an intermediate fact. Use extensionality with `x`. Simplify using `only [Subgroup.mem_map, MonoidHom.mem_range, powMonoidHom_apply]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨σ, hσ, rfl⟩`.

Conclude with `⟨_, (unramifiedDegree_fixingSubgroup L ⟨σ, hσ⟩).symm⟩`. Introduce and unpack `⟨y, rfl⟩`. Take `⟨τ, rfl⟩` from `unramifiedDegree_surjective (K := L) (Ω := Ω) y`. Take `⟨σ, rfl⟩` from `(fixingSubgroupEquiv L).surjective τ`. Conclude with `⟨σ, σ.2, (unramifiedDegree_fixingSubgroup L σ)⟩`.
-/
theorem map_unramifiedDegree_fixingSubgroup :
    L.fixingSubgroup.map (unramifiedDegree K Ω) =
      (powMonoidHom (residueDegree K L) : Multiplicative ℤ̂ →* Multiplicative ℤ̂).range := by
  have := IsGalois.tower_top_of_isGalois K L Ω
  ext x
  simp only [Subgroup.mem_map, MonoidHom.mem_range, powMonoidHom_apply]
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨_, (unramifiedDegree_fixingSubgroup L ⟨σ, hσ⟩).symm⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨τ, rfl⟩ := unramifiedDegree_surjective (K := L) (Ω := Ω) y
    obtain ⟨σ, rfl⟩ := (fixingSubgroupEquiv L).surjective τ
    exact ⟨σ, σ.2, (unramifiedDegree_fixingSubgroup L σ)⟩

/- English proof (translation)
Rewrite using `[inertiaDegree, map_unramifiedDegree_fixingSubgroup, ProfiniteInteger.index_range_powMonoidHom (residueDegree_pos K L).ne']`.
-/
theorem inertiaDegree_unramifiedDegree_fixingSubgroup :
    inertiaDegree (unramifiedDegree K Ω) L.fixingSubgroup = residueDegree K L := by
  rw [inertiaDegree, map_unramifiedDegree_fixingSubgroup,
    ProfiniteInteger.index_range_powMonoidHom (residueDegree_pos K L).ne']

end Finite

end GroundTheory.LocalField
