import Mathlib
import GroundTheory.ProfiniteCohomology.KummerBasic
import GroundTheory.ProfiniteCohomology.KummerFinite

namespace GroundTheory.ProfCoh

open Polynomial IntermediateField

section Generated

variable {K : Type*} [Field K] {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n]
variable {L : Type*} [Field L] [Algebra K L]

omit [NeZero n] [HasEnoughRootsOfUnity K n] in

/- English proof (translation)
Establish `hle : adjoin K T ≤ fixedField (Subgroup.zpowers σ)`. Rewrite using `[adjoin_le_iff]`. Introduce `α hα`. Rewrite using `[SetLike.mem_coe, mem_fixedField_iff]`. Introduce `f hf`.

Establish `hσ : σ ∈ MulAction.stabilizer Gal(L/K) α`. Rewrite using `[MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]`. Conclude with `h α hα`. Establish `hf'` using `(Subgroup.zpowers_le.mpr hσ) hf`. Rewrite `hf'` using `[MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]`.

Conclude with `hf'`. Rewrite `hle` using `[hT]`. Use extensionality with `x`. Establish `hx` using `hle (IntermediateField.mem_top (x := x))`. Rewrite `hx` using `[mem_fixedField_iff]`.

Rewrite using `[AlgEquiv.one_apply]`. Conclude with `hx σ (Subgroup.mem_zpowers σ)`.
-/
lemma eq_one_of_forall_mem_fixed {T : Set L} (hT : adjoin K T = ⊤) {σ : Gal(L/K)}
    (h : ∀ α ∈ T, σ α = α) : σ = 1 := by
  have hle : adjoin K T ≤ fixedField (Subgroup.zpowers σ) := by
    rw [adjoin_le_iff]
    intro α hα
    rw [SetLike.mem_coe, mem_fixedField_iff]
    intro f hf
    have hσ : σ ∈ MulAction.stabilizer Gal(L/K) α := by
      rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
      exact h α hα
    have hf' := (Subgroup.zpowers_le.mpr hσ) hf
    rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def] at hf'
    exact hf'
  rw [hT] at hle
  ext x
  have hx := hle (IntermediateField.mem_top (x := x))
  rw [mem_fixedField_iff] at hx
  rw [AlgEquiv.one_apply]
  exact hx σ (Subgroup.mem_zpowers σ)

/- English proof (translation)
Take `⟨d, hd⟩` from `mem_unitsPow.mp (QuotientGroup.eq.mp h)`. Establish `hβ0 : β ≠ 0` using `ne_zero_of_pow_eq_algebraMap hβ`. Establish `hd0 : algebraMap K L (d : K) ≠ 0` using `(map_ne_zero (algebraMap K L)).mpr d.ne_zero`. Establish `hb : (b : K) = (a : K) * (d : K) ^ n`. Establish `h1 : (d : K) ^ n = (a : K)⁻¹ * (b : K)`.

Simplify `congrArg Units.val hd` using `only [Units.val_pow_eq_pow_val, Units.val_mul, Units.val_inv_eq_inv_val]`. Rewrite using `[h1, ← mul_assoc, mul_inv_cancel₀ a.ne_zero, one_mul]`. Establish `hq : (α * algebraMap K L (d : K) / β) ^ n = 1`. Rewrite using `[div_pow, mul_pow, hα, hβ, hb, map_mul, map_pow]`. Conclude with `div_self (mul_ne_zero ((map_ne_zero (algebraMap K L)).mpr a.ne_zero) (pow_ne_zero _ hd0))`.

Take `⟨η, hη⟩` from `exists_algebraMap_eq_of_pow_eq_one (K := K) hq`. Use `⟨((η : Kˣ) : K) / d, ?_⟩` and prove the remaining obligations. Rewrite using `[map_div₀, hη]`. Clear the denominators using the available nonvanishing facts.
-/
lemma exists_eq_algebraMap_mul {a b : Kˣ} (h : (a : UnitsModPow K n) = b) {α β : L}
    (hα : α ^ n = algebraMap K L a) (hβ : β ^ n = algebraMap K L b) :
    ∃ c : K, α = algebraMap K L c * β := by
  obtain ⟨d, hd⟩ := mem_unitsPow.mp (QuotientGroup.eq.mp h)
  have hβ0 : β ≠ 0 := ne_zero_of_pow_eq_algebraMap hβ
  have hd0 : algebraMap K L (d : K) ≠ 0 := (map_ne_zero (algebraMap K L)).mpr d.ne_zero
  have hb : (b : K) = (a : K) * (d : K) ^ n := by
    have h1 : (d : K) ^ n = (a : K)⁻¹ * (b : K) := by
      simpa only [Units.val_pow_eq_pow_val, Units.val_mul, Units.val_inv_eq_inv_val]
        using congrArg Units.val hd
    rw [h1, ← mul_assoc, mul_inv_cancel₀ a.ne_zero, one_mul]
  have hq : (α * algebraMap K L (d : K) / β) ^ n = 1 := by
    rw [div_pow, mul_pow, hα, hβ, hb, map_mul, map_pow]
    exact div_self (mul_ne_zero ((map_ne_zero (algebraMap K L)).mpr a.ne_zero) (pow_ne_zero _ hd0))
  obtain ⟨η, hη⟩ := exists_algebraMap_eq_of_pow_eq_one (K := K) hq
  refine ⟨((η : Kˣ) : K) / d, ?_⟩
  rw [map_div₀, hη]
  field_simp

variable (K n L)

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_one]`. Introduce `σ hσ`. Apply `eq_one_of_forall_mem_fixed hT` to reduce the goal to its premises. Introduce `α hα`. Take `⟨a, ha⟩` from `hTn α hα`.

Establish `hx : (a : UnitsModPow K n) ∈ kummerGroup K n L` using `mk_mem_kummerGroup.mpr ⟨α, ha⟩`. Conclude with `(kummerPairing_eq_one_iff σ ⟨_, hx⟩ rfl ha).mp (DFunLike.congr_fun hσ ⟨_, hx⟩)`.
-/
theorem kummerPairingLeft_injective_of_adjoin_eq_top {T : Set L} (hT : adjoin K T = ⊤)
    (hTn : ∀ α ∈ T, ∃ a : Kˣ, α ^ n = algebraMap K L a) :
    Function.Injective (kummerPairingLeft K n L) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  apply eq_one_of_forall_mem_fixed hT
  intro α hα
  obtain ⟨a, ha⟩ := hTn α hα
  have hx : (a : UnitsModPow K n) ∈ kummerGroup K n L := mk_mem_kummerGroup.mpr ⟨α, ha⟩
  exact (kummerPairing_eq_one_iff σ ⟨_, hx⟩ rfl ha).mp (DFunLike.congr_fun hσ ⟨_, hx⟩)

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨fun σ τ => kummerPairingLeft_injective_of_adjoin_eq_top K n L hT hTn (by rw [map_mul, map_mul, mul_comm])⟩⟩`.
-/
theorem isMulCommutative_of_adjoin_eq_top {T : Set L} (hT : adjoin K T = ⊤)
    (hTn : ∀ α ∈ T, ∃ a : Kˣ, α ^ n = algebraMap K L a) :
    IsMulCommutative Gal(L/K) :=
  ⟨⟨fun σ τ => kummerPairingLeft_injective_of_adjoin_eq_top K n L hT hTn (by
    rw [map_mul, map_mul, mul_comm])⟩⟩

/- English proof (translation)
Use `Monoid.exponent_dvd_of_forall_pow_eq_one fun σ => kummerPairingLeft_injective_of_adjoin_eq_top K n L hT hTn ?_` and prove the remaining obligations. Rewrite using `[map_pow, map_one]`. Use extensionality with `x`. Use `(mem_rootsOfUnity n _).mp (kummerPairingLeft K n L σ x).2` as an intermediate fact. Simplify using `only [MonoidHom.pow_apply, MonoidHom.one_apply]`.

Conclude with `congrArg Units.val (by rw [SubmonoidClass.coe_pow, this, OneMemClass.coe_one])`.
-/
theorem exponent_dvd_of_adjoin_eq_top {T : Set L} (hT : adjoin K T = ⊤)
    (hTn : ∀ α ∈ T, ∃ a : Kˣ, α ^ n = algebraMap K L a) :
    Monoid.exponent Gal(L/K) ∣ n := by
  refine Monoid.exponent_dvd_of_forall_pow_eq_one fun σ =>
    kummerPairingLeft_injective_of_adjoin_eq_top K n L hT hTn ?_
  rw [map_pow, map_one]
  ext x
  have := (mem_rootsOfUnity n _).mp (kummerPairingLeft K n L σ x).2
  simp only [MonoidHom.pow_apply, MonoidHom.one_apply]
  exact congrArg Units.val (by rw [SubmonoidClass.coe_pow, this, OneMemClass.coe_one])

/- English proof (translation)
Establish `hTn : ∀ α ∈ T, ∃ a : Kˣ, α ^ n = algebraMap K L a` using `fun α hα =>`. Set `⟨a, _, h⟩` to `hTΔ α hα`. Use the proof step `⟨a, h⟩`. Establish `: IsMulCommutative Gal(L/K)` using `isMulCommutative_of_adjoin_eq_top K n L hT hTn`. Establish `hexp` using `exponent_dvd_of_adjoin_eq_top K n L hT hTn`.

Use `kummerGroup_finite K n L` as an intermediate fact. Set `H : Subgroup (kummerGroup K n L)` to `Δ.comap (kummerGroup K n L).subtype`. Use `finite_monoidHom_rootsOfUnity (K := K) (n := n) H` as an intermediate fact. Set `res : Gal(L/K) → (H →* rootsOfUnity n K)` to `fun σ => (kummerPairingLeft K n L σ).comp H.subtype`. Establish `hres : Function.Injective res`.

Introduce `σ τ hστ`. Establish `hfix : ∀ α ∈ T, (τ⁻¹ * σ) α = α`. Introduce `α hα`. Take `⟨a, haΔ, ha⟩` from `hTΔ α hα`. Establish `hx : (a : UnitsModPow K n) ∈ kummerGroup K n L` using `mk_mem_kummerGroup.mpr ⟨α, ha⟩`.

Establish `hxH : (⟨_, hx⟩ : kummerGroup K n L) ∈ H` using `haΔ`. Establish `h1` using `DFunLike.congr_fun hστ ⟨_, hxH⟩`. Simplify using `only [res, MonoidHom.comp_apply, Subgroup.coe_subtype, kummerPairingLeft_apply] at h1`. Rewrite using `[AlgEquiv.mul_apply, kummerPairing_spec σ ⟨_, hx⟩ rfl ha, h1, ← kummerPairing_spec τ ⟨_, hx⟩ rfl ha, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]`. Conclude with `(inv_mul_eq_one.mp (eq_one_of_forall_mem_fixed hT hfix)).symm`.

Establish `hH : Nat.card H = Nat.card (kummerGroup K n L)`. Apply `le_antisymm (Nat.card_le_card_of_injective _ Subtype.val_injective)` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[card_kummerGroup K n L hexp, IsGalois.card_aut_eq_finrank]`. Use `_ ≤ Nat.card (H →* rootsOfUnity n K) := Nat.card_le_card_of_injective _ hres`.

Use `_ = Nat.card H := card_monoidHom_rootsOfUnity H fun x => Subtype.ext (kummerGroup_pow_eq_one K n L x.1)`. Establish `htop` using `Subgroup.eq_top_of_card_eq H hH`. Introduce `x hx`. Establish `: (⟨x, hx⟩ : kummerGroup K n L) ∈ H` using `htop ▸ Subgroup.mem_top _`. Conclude with `this`.
-/
theorem kummerGroup_le_of_adjoin_eq_top [FiniteDimensional K L] [IsGalois K L] {T : Set L}
    (hT : adjoin K T = ⊤) (Δ : Subgroup (UnitsModPow K n))
    (hTΔ : ∀ α ∈ T, ∃ a : Kˣ, (a : UnitsModPow K n) ∈ Δ ∧ α ^ n = algebraMap K L a) :
    kummerGroup K n L ≤ Δ := by
  have hTn : ∀ α ∈ T, ∃ a : Kˣ, α ^ n = algebraMap K L a := fun α hα =>
    let ⟨a, _, h⟩ := hTΔ α hα; ⟨a, h⟩
  have : IsMulCommutative Gal(L/K) := isMulCommutative_of_adjoin_eq_top K n L hT hTn
  have hexp := exponent_dvd_of_adjoin_eq_top K n L hT hTn
  have := kummerGroup_finite K n L
  let H : Subgroup (kummerGroup K n L) := Δ.comap (kummerGroup K n L).subtype
  have := finite_monoidHom_rootsOfUnity (K := K) (n := n) H

  let res : Gal(L/K) → (H →* rootsOfUnity n K) := fun σ => (kummerPairingLeft K n L σ).comp H.subtype
  have hres : Function.Injective res := by
    intro σ τ hστ
    have hfix : ∀ α ∈ T, (τ⁻¹ * σ) α = α := by
      intro α hα
      obtain ⟨a, haΔ, ha⟩ := hTΔ α hα
      have hx : (a : UnitsModPow K n) ∈ kummerGroup K n L := mk_mem_kummerGroup.mpr ⟨α, ha⟩
      have hxH : (⟨_, hx⟩ : kummerGroup K n L) ∈ H := haΔ
      have h1 := DFunLike.congr_fun hστ ⟨_, hxH⟩
      simp only [res, MonoidHom.comp_apply, Subgroup.coe_subtype, kummerPairingLeft_apply] at h1
      rw [AlgEquiv.mul_apply, kummerPairing_spec σ ⟨_, hx⟩ rfl ha, h1,
        ← kummerPairing_spec τ ⟨_, hx⟩ rfl ha, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
    exact (inv_mul_eq_one.mp (eq_one_of_forall_mem_fixed hT hfix)).symm
  have hH : Nat.card H = Nat.card (kummerGroup K n L) := by
    apply le_antisymm (Nat.card_le_card_of_injective _ Subtype.val_injective)
    calc Nat.card (kummerGroup K n L) = Nat.card Gal(L/K) := by
          rw [card_kummerGroup K n L hexp, IsGalois.card_aut_eq_finrank]
      _ ≤ Nat.card (H →* rootsOfUnity n K) := Nat.card_le_card_of_injective _ hres
      _ = Nat.card H := card_monoidHom_rootsOfUnity H fun x =>
          Subtype.ext (kummerGroup_pow_eq_one K n L x.1)
  have htop := Subgroup.eq_top_of_card_eq H hH
  intro x hx
  have : (⟨x, hx⟩ : kummerGroup K n L) ∈ H := htop ▸ Subgroup.mem_top _
  exact this

end Generated

section Galois

variable {K : Type*} [Field K] {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n]
variable {Ω : Type*} [Field Ω] [Algebra K Ω]

/- English proof (translation)
Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot K n`. Establish `hnK : (n : K) ≠ 0` using `(hζ.neZero').out`. Set `a : T → Kˣ` to `fun α => (hT α α.2).choose`. Establish `ha : ∀ α : T, (α : Ω) ^ n = algebraMap K Ω (a α)` using `fun α => (hT α α.2).choose_spec`. Set `p : T → K[X]` to `fun α => X ^ n - C (a α : K)`.

Establish `hp0 : ∀ α, p α ≠ 0` using `fun α => X_pow_sub_C_ne_zero (NeZero.pos n) _`. Establish `hsep : ∀ α, (p α).Separable` using `fun α => separable_X_pow_sub_C _ hnK (a α).ne_zero`. Establish `hsplit : ∀ α : T, ((p α).map (algebraMap K Ω)).Splits`. Introduce `α`. Simplify using `only [p, Polynomial.map_sub, Polynomial.map_pow, map_X, map_C]`.

Conclude with `X_pow_sub_C_splits_of_isPrimitiveRoot (hζ.map_of_injective (algebraMap K Ω).injective) (ha α)`. Establish `hgal : ∀ α : T, IsGalois K (adjoin K ((p α).rootSet Ω))` using `fun α => haveI := adjoin_rootSet_isSplittingField (hsplit α) IsGalois.of_separable_splitting_field (hsep α)`. Establish `heq : adjoin K T = ⨆ α : T, adjoin K ((p α).rootSet Ω)`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[adjoin_le_iff]`.

Introduce `α hα`. Apply `le_iSup (fun β : T => adjoin K ((p β).rootSet Ω)) ⟨α, hα⟩` to reduce the goal to its premises. Apply `subset_adjoin` to reduce the goal to its premises. Rewrite using `[mem_rootSet]`. Use `⟨hp0 _, ?_⟩` and prove the remaining obligations.

Simplify using `[p, ha ⟨α, hα⟩]`. Use `iSup_le fun α => ?_` and prove the remaining obligations. Rewrite using `[adjoin_le_iff]`. Introduce `γ hγ`. Rewrite `hγ` using `[mem_rootSet]`.

Establish `hγn : γ ^ n = algebraMap K Ω (a α)`. Use `hγ.2` as an intermediate fact. Simplify using `only [p, map_sub, map_pow, aeval_X, aeval_C] at this`. Conclude with `sub_eq_zero.mp this`. Take `⟨c, hc⟩` from `exists_eq_algebraMap_mul (K := K) rfl hγn (ha α)`.

Rewrite using `[SetLike.mem_coe, hc]`. Conclude with `mul_mem (IntermediateField.algebraMap_mem _ _) (subset_adjoin _ _ α.2)`. Establish `: ∀ α : T, Normal K (adjoin K ((p α).rootSet Ω))` using `fun α => (hgal α).to_normal`. Establish `: ∀ α : T, Algebra.IsSeparable K (adjoin K ((p α).rootSet Ω))` using `fun α => (hgal α).to_isSeparable`. Rewrite using `[heq]`.

Prove the components needed by the constructor for the conclusion.
-/
theorem isGalois_adjoin_nthRoots {T : Set Ω} (hT : ∀ α ∈ T, ∃ a : Kˣ, α ^ n = algebraMap K Ω a) :
    IsGalois K (adjoin K T) := by
  classical
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K n
  have hnK : (n : K) ≠ 0 := (hζ.neZero').out
  let a : T → Kˣ := fun α => (hT α α.2).choose
  have ha : ∀ α : T, (α : Ω) ^ n = algebraMap K Ω (a α) := fun α => (hT α α.2).choose_spec
  let p : T → K[X] := fun α => X ^ n - C (a α : K)
  have hp0 : ∀ α, p α ≠ 0 := fun α => X_pow_sub_C_ne_zero (NeZero.pos n) _
  have hsep : ∀ α, (p α).Separable := fun α => separable_X_pow_sub_C _ hnK (a α).ne_zero
  have hsplit : ∀ α : T, ((p α).map (algebraMap K Ω)).Splits := by
    intro α
    simp only [p, Polynomial.map_sub, Polynomial.map_pow, map_X, map_C]
    exact X_pow_sub_C_splits_of_isPrimitiveRoot
      (hζ.map_of_injective (algebraMap K Ω).injective) (ha α)
  have hgal : ∀ α : T, IsGalois K (adjoin K ((p α).rootSet Ω)) := fun α =>
    haveI := adjoin_rootSet_isSplittingField (hsplit α)
    IsGalois.of_separable_splitting_field (hsep α)
  have heq : adjoin K T = ⨆ α : T, adjoin K ((p α).rootSet Ω) := by
    apply le_antisymm
    · rw [adjoin_le_iff]
      intro α hα
      apply le_iSup (fun β : T => adjoin K ((p β).rootSet Ω)) ⟨α, hα⟩
      apply subset_adjoin
      rw [mem_rootSet]
      refine ⟨hp0 _, ?_⟩
      simp [p, ha ⟨α, hα⟩]
    · refine iSup_le fun α => ?_
      rw [adjoin_le_iff]
      intro γ hγ
      rw [mem_rootSet] at hγ
      have hγn : γ ^ n = algebraMap K Ω (a α) := by
        have := hγ.2
        simp only [p, map_sub, map_pow, aeval_X, aeval_C] at this
        exact sub_eq_zero.mp this
      obtain ⟨c, hc⟩ := exists_eq_algebraMap_mul (K := K) rfl hγn (ha α)
      rw [SetLike.mem_coe, hc]
      exact mul_mem (IntermediateField.algebraMap_mem _ _) (subset_adjoin _ _ α.2)
  have : ∀ α : T, Normal K (adjoin K ((p α).rootSet Ω)) := fun α => (hgal α).to_normal
  have : ∀ α : T, Algebra.IsSeparable K (adjoin K ((p α).rootSet Ω)) :=
    fun α => (hgal α).to_isSeparable
  rw [heq]
  constructor

end Galois

section Correspondence

variable (K : Type*) [Field K] (n : ℕ) [NeZero n] [HasEnoughRootsOfUnity K n]
variable (Ω : Type*) [Field Ω] [Algebra K Ω]

omit [NeZero n] [HasEnoughRootsOfUnity K n] in

/- English proof (translation)
Rewrite using `[← Subtype.val_inj, IntermediateField.coe_pow]`. Both sides reduce to the same expression.
-/
lemma pow_eq_algebraMap_iff (E : IntermediateField K Ω) (x : E) (a : K) :
    x ^ n = algebraMap K E a ↔ (x : Ω) ^ n = algebraMap K Ω a := by
  rw [← Subtype.val_inj, IntermediateField.coe_pow]
  rfl

omit [NeZero n] [HasEnoughRootsOfUnity K n] in

/- English proof (translation)
Apply `IntermediateField.map_injective (adjoin K S).val` to reduce the goal to its premises. Rewrite using `[adjoin_map, ← AlgHom.fieldRange_eq_map, IntermediateField.fieldRange_val]`. Use `congr 1`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `hy`. Introduce `hx`. Conclude with `⟨⟨x, subset_adjoin K S hx⟩, hx, rfl⟩`.
-/
lemma adjoin_preimage_eq_top (S : Set Ω) :
    adjoin K (((↑) : adjoin K S → Ω) ⁻¹' S) = ⊤ := by
  apply IntermediateField.map_injective (adjoin K S).val
  rw [adjoin_map, ← AlgHom.fieldRange_eq_map, IntermediateField.fieldRange_val]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, subset_adjoin K S hx⟩, hx, rfl⟩

omit [NeZero n] [HasEnoughRootsOfUnity K n] in

/- English proof (translation)
Apply `adjoin.mono` to reduce the goal to its premises. Introduce and unpack `α ⟨a, ha, hα⟩`. Conclude with `⟨a, h ha, hα⟩`.
-/
lemma kummerField_mono {Δ Δ' : Subgroup (UnitsModPow K n)} (h : Δ ≤ Δ') :
    kummerField K n Ω Δ ≤ kummerField K n Ω Δ' := by
  apply adjoin.mono
  rintro α ⟨a, ha, hα⟩
  exact ⟨a, h ha, hα⟩

omit [NeZero n] [HasEnoughRootsOfUnity K n] in

/- English proof (translation)
Introduce `y hy`. Proceed by induction on `y using QuotientGroup.induction_on with`. Consider the case `H b`. Take `⟨β, hβ⟩` from `mk_mem_kummerGroup.mp hy`. Use `mk_mem_kummerGroup.mpr ⟨⟨β, h β.2⟩, ?_⟩` and prove the remaining obligations.

Rewrite `hβ`, the goal using `[pow_eq_algebraMap_iff]`. Conclude with `hβ`.
-/
lemma kummerGroup_mono {E E' : IntermediateField K Ω} (h : E ≤ E') :
    kummerGroup K n E ≤ kummerGroup K n E' := by
  intro y hy
  induction y using QuotientGroup.induction_on with
  | H b =>
    obtain ⟨β, hβ⟩ := mk_mem_kummerGroup.mp hy
    refine mk_mem_kummerGroup.mpr ⟨⟨β, h β.2⟩, ?_⟩
    rw [pow_eq_algebraMap_iff] at hβ ⊢
    exact hβ

omit [NeZero n] [HasEnoughRootsOfUnity K n] in
/- English proof (translation)
Unfold `kummerField`. Rewrite using `[← adjoin_preimage_eq_top K Ω]`. Use `congr 1`. Use extensionality with `x`. Simplify using `only [Set.mem_ofPred_eq, Set.mem_preimage, pow_eq_algebraMap_iff]`.
-/
lemma kummerField_generators (Δ : Subgroup (UnitsModPow K n)) :
    adjoin K {x : kummerField K n Ω Δ |
      ∃ a : Kˣ, (a : UnitsModPow K n) ∈ Δ ∧ x ^ n = algebraMap K _ a} = ⊤ := by
  unfold kummerField
  rw [← adjoin_preimage_eq_top K Ω]
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, pow_eq_algebraMap_iff]

/- English proof (translation)
The claim follows from `isGalois_adjoin_nthRoots fun _ ⟨a, _, h⟩ => ⟨a, h⟩`.
-/
theorem kummerField_isGalois (Δ : Subgroup (UnitsModPow K n)) :
    IsGalois K (kummerField K n Ω Δ) :=
  isGalois_adjoin_nthRoots fun _ ⟨a, _, h⟩ => ⟨a, h⟩

/- English proof (translation)
The claim follows from `isMulCommutative_of_adjoin_eq_top K n _ (kummerField_generators K n Ω Δ) fun _ ⟨a, _, h⟩ => ⟨a, h⟩`.
-/
theorem kummerField_isMulCommutative (Δ : Subgroup (UnitsModPow K n)) :
    IsMulCommutative Gal(kummerField K n Ω Δ/K) :=
  isMulCommutative_of_adjoin_eq_top K n _ (kummerField_generators K n Ω Δ)
    fun _ ⟨a, _, h⟩ => ⟨a, h⟩

/- English proof (translation)
The claim follows from `exponent_dvd_of_adjoin_eq_top K n _ (kummerField_generators K n Ω Δ) fun _ ⟨a, _, h⟩ => ⟨a, h⟩`.
-/
theorem kummerField_exponent_dvd (Δ : Subgroup (UnitsModPow K n)) :
    Monoid.exponent Gal(kummerField K n Ω Δ/K) ∣ n :=
  exponent_dvd_of_adjoin_eq_top K n _ (kummerField_generators K n Ω Δ)
    fun _ ⟨a, _, h⟩ => ⟨a, h⟩

omit [HasEnoughRootsOfUnity K n] in
/- English proof (translation)
Assemble the required witnesses or components as `⟨X ^ n - C a, monic_X_pow_sub_C _ (NeZero.ne n), by simp [hα]⟩`.
-/
lemma isIntegral_of_pow_eq_algebraMap {α : Ω} {a : K} (hα : α ^ n = algebraMap K Ω a) :
    IsIntegral K α :=
  ⟨X ^ n - C a, monic_X_pow_sub_C _ (NeZero.ne n), by simp [hα]⟩

/- English proof (translation)
Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot K n`. Establish `hnΩ : ((n : ℕ) : Ω) ≠ 0`. Rewrite using `[← map_natCast (algebraMap K Ω)]`. Conclude with `(map_ne_zero (algebraMap K Ω)).mpr (hζ.neZero').out`. Take `⟨α, hα⟩` from `IsSepClosed.exists_root (X ^ n - C (algebraMap K Ω a)) (by rw [degree_X_pow_sub_C (NeZero.pos n)]; exact_mod_cast NeZero.ne n) (separable_X_pow_sub_C _ hnΩ ((map_ne_zero (algebraMap K Ω)).mpr a.ne_zero))`.

Use `⟨α, ?_⟩` and prove the remaining obligations. Simplify `hα` using `[sub_eq_zero]`.
-/
lemma exists_pow_eq_algebraMap [IsSepClosed Ω] (a : Kˣ) : ∃ α : Ω, α ^ n = algebraMap K Ω a := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K n
  have hnΩ : ((n : ℕ) : Ω) ≠ 0 := by
    rw [← map_natCast (algebraMap K Ω)]
    exact (map_ne_zero (algebraMap K Ω)).mpr (hζ.neZero').out
  obtain ⟨α, hα⟩ := IsSepClosed.exists_root (X ^ n - C (algebraMap K Ω a))
    (by rw [degree_X_pow_sub_C (NeZero.pos n)]; exact_mod_cast NeZero.ne n)
    (separable_X_pow_sub_C _ hnΩ ((map_ne_zero (algebraMap K Ω)).mpr a.ne_zero))
  refine ⟨α, ?_⟩
  simpa [sub_eq_zero] using hα

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce `y hy`. Proceed by induction on `y using QuotientGroup.induction_on with`. Consider the case `H b`. Take `⟨β, hβ⟩` from `mk_mem_kummerGroup.mp hy`.

Rewrite `hβ` using `[pow_eq_algebraMap_iff]`. Take `⟨T, hTS, hβT⟩` from `exists_finset_of_mem_adjoin β.2`. Establish `hTn : ∀ α ∈ (T : Set Ω), ∃ a : Kˣ, (a : UnitsModPow K n) ∈ Δ ∧ α ^ n = algebraMap K Ω a` using `fun α hα => hTS hα`. Establish `: FiniteDimensional K (adjoin K (T : Set Ω))` using `finiteDimensional_adjoin fun α hα =>`. Set `⟨_, _, h⟩` to `hTn α hα`.

Use `isIntegral_of_pow_eq_algebraMap K n Ω h`. Establish `: IsGalois K (adjoin K (T : Set Ω))` using `isGalois_adjoin_nthRoots fun α hα => let ⟨a, _, h⟩ := hTn α hα`. Use the proof step `⟨a, h⟩`. Establish `hle` using `kummerGroup_le_of_adjoin_eq_top K n (adjoin K (T : Set Ω)) (adjoin_preimage_eq_top K Ω _) Δ (fun α hα => by`. Take `⟨a, haΔ, ha⟩` from `hTn α hα`.

Conclude with `⟨a, haΔ, (pow_eq_algebraMap_iff K n Ω _ α a).mpr ha⟩)`. Apply `hle` to reduce the goal to its premises. Conclude with `mk_mem_kummerGroup.mpr ⟨⟨β, hβT⟩, (pow_eq_algebraMap_iff K n Ω _ _ _).mpr hβ⟩`. Introduce `y hy`. Proceed by induction on `y using QuotientGroup.induction_on with`.

Consider the case `H b`. Take `⟨α, hα⟩` from `exists_pow_eq_algebraMap K n Ω b`. Conclude with `mk_mem_kummerGroup.mpr ⟨⟨α, subset_adjoin _ _ ⟨b, hy, hα⟩⟩, (pow_eq_algebraMap_iff K n Ω _ _ _).mpr hα⟩`.
-/
theorem kummerGroup_kummerField [IsSepClosed Ω] (Δ : Subgroup (UnitsModPow K n)) :
    kummerGroup K n (kummerField K n Ω Δ) = Δ := by
  apply le_antisymm
  · intro y hy
    induction y using QuotientGroup.induction_on with
    | H b =>
      obtain ⟨β, hβ⟩ := mk_mem_kummerGroup.mp hy
      rw [pow_eq_algebraMap_iff] at hβ
      obtain ⟨T, hTS, hβT⟩ := exists_finset_of_mem_adjoin β.2
      have hTn : ∀ α ∈ (T : Set Ω), ∃ a : Kˣ, (a : UnitsModPow K n) ∈ Δ ∧
          α ^ n = algebraMap K Ω a := fun α hα => hTS hα
      have : FiniteDimensional K (adjoin K (T : Set Ω)) :=
        finiteDimensional_adjoin fun α hα =>
          let ⟨_, _, h⟩ := hTn α hα; isIntegral_of_pow_eq_algebraMap K n Ω h
      have : IsGalois K (adjoin K (T : Set Ω)) :=
        isGalois_adjoin_nthRoots fun α hα => let ⟨a, _, h⟩ := hTn α hα; ⟨a, h⟩
      have hle := kummerGroup_le_of_adjoin_eq_top K n (adjoin K (T : Set Ω))
        (adjoin_preimage_eq_top K Ω _) Δ (fun α hα => by
          obtain ⟨a, haΔ, ha⟩ := hTn α hα
          exact ⟨a, haΔ, (pow_eq_algebraMap_iff K n Ω _ α a).mpr ha⟩)
      apply hle
      exact mk_mem_kummerGroup.mpr ⟨⟨β, hβT⟩, (pow_eq_algebraMap_iff K n Ω _ _ _).mpr hβ⟩
  · intro y hy
    induction y using QuotientGroup.induction_on with
    | H b =>
      obtain ⟨α, hα⟩ := exists_pow_eq_algebraMap K n Ω b
      exact mk_mem_kummerGroup.mpr ⟨⟨α, subset_adjoin _ _ ⟨b, hy, hα⟩⟩,
        (pow_eq_algebraMap_iff K n Ω _ _ _).mpr hα⟩

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[kummerField, adjoin_le_iff]`. Introduce and unpack `α ⟨a, ha, hα⟩`. Take `⟨β, hβ⟩` from `mk_mem_kummerGroup.mp ha`. Rewrite `hβ` using `[pow_eq_algebraMap_iff]`.

Take `⟨c, hc⟩` from `exists_eq_algebraMap_mul (K := K) rfl hα hβ`. Rewrite using `[SetLike.mem_coe, hc]`. Conclude with `mul_mem (IntermediateField.algebraMap_mem _ _) β.2`. Introduce `x hx set x' : E := ⟨x, hx⟩ set p := minpoly K x'`. Set `F : IntermediateField K E` to `adjoin K (p.rootSet E)`.

Establish `: p.IsSplittingField K F` using `adjoin_rootSet_isSplittingField (Normal.splits inferInstance x')`. Establish `: IsGalois K F` using `IsGalois.of_separable_splitting_field (Algebra.IsSeparable.isSeparable K x')`. Establish `: FiniteDimensional K F` using `IsSplittingField.finiteDimensional F p`. Establish `hxF : x' ∈ F` using `subset_adjoin _ _ (by`. Rewrite using `[mem_rootSet]`.

Conclude with `⟨minpoly.ne_zero (Algebra.IsIntegral.isIntegral x'), minpoly.aeval K x'⟩)`. Establish `hsurj` using `AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := F) (E := E)`. Establish `: IsMulCommutative Gal(F/K)` using `⟨⟨fun σ τ => by`. Take `⟨σ', rfl⟩` from `hsurj σ`. Take `⟨τ', rfl⟩` from `hsurj τ`.

Rewrite using `[← map_mul, ← map_mul, (IsMulCommutative.is_comm (M := Gal(E/K))).comm σ' τ']⟩⟩`. Establish `hexpF : Monoid.exponent Gal(F/K) ∣ n`. Use `Monoid.exponent_dvd_of_forall_pow_eq_one fun σ => ?_` and prove the remaining obligations. Take `⟨σ', rfl⟩` from `hsurj σ`. Rewrite using `[← map_pow, Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hexp σ', map_one]`.

Establish `htop` using `adjoin_nthRoots_eq_top K n F hexpF`. Set `φ : F →ₐ[K] Ω` to `E.val.comp F.val`. Establish `hmap : (⊤ : IntermediateField K F).map φ ≤ kummerField K n Ω (kummerGroup K n E)`. Rewrite using `[← htop, adjoin_map, kummerField, adjoin_le_iff]`. Introduce and unpack `_ ⟨γ, ⟨hγ0, b, hb⟩, rfl⟩`.

Establish `hb0 : b ≠ 0`. Introduce and unpack `rfl`. Rewrite `hb` using `[map_zero]`. Conclude with `pow_ne_zero n hγ0 hb.symm`. Use `subset_adjoin _ _ ⟨Units.mk0 b hb0, ?_, ?_⟩` and prove the remaining obligations.

Use `mk_mem_kummerGroup.mpr ⟨F.val γ, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_pow, ← hb, AlgHom.commutes]`. Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `(φ γ) ^ n = algebraMap K Ω b`. Rewrite using `[← map_pow, ← hb, AlgHom.commutes]`.

Conclude with `hmap ((IntermediateField.map_mem_map _ φ).mpr (IntermediateField.mem_top (x := ⟨x', hxF⟩)))`.
-/
theorem kummerField_kummerGroup_eq (E : IntermediateField K Ω) [IsGalois K E]
    [IsMulCommutative Gal(E/K)] (hexp : Monoid.exponent Gal(E/K) ∣ n) :
    kummerField K n Ω (kummerGroup K n E) = E := by
  apply le_antisymm
  · rw [kummerField, adjoin_le_iff]
    rintro α ⟨a, ha, hα⟩
    obtain ⟨β, hβ⟩ := mk_mem_kummerGroup.mp ha
    rw [pow_eq_algebraMap_iff] at hβ
    obtain ⟨c, hc⟩ := exists_eq_algebraMap_mul (K := K) rfl hα hβ
    rw [SetLike.mem_coe, hc]
    exact mul_mem (IntermediateField.algebraMap_mem _ _) β.2
  · intro x hx
    set x' : E := ⟨x, hx⟩
    set p := minpoly K x'
    let F : IntermediateField K E := adjoin K (p.rootSet E)
    have : p.IsSplittingField K F := adjoin_rootSet_isSplittingField (Normal.splits inferInstance x')
    have : IsGalois K F :=
      IsGalois.of_separable_splitting_field (Algebra.IsSeparable.isSeparable K x')
    have : FiniteDimensional K F := IsSplittingField.finiteDimensional F p
    have hxF : x' ∈ F := subset_adjoin _ _ (by
      rw [mem_rootSet]
      exact ⟨minpoly.ne_zero (Algebra.IsIntegral.isIntegral x'), minpoly.aeval K x'⟩)

    have hsurj := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := F) (E := E)
    have : IsMulCommutative Gal(F/K) := ⟨⟨fun σ τ => by
      obtain ⟨σ', rfl⟩ := hsurj σ
      obtain ⟨τ', rfl⟩ := hsurj τ
      rw [← map_mul, ← map_mul, (IsMulCommutative.is_comm (M := Gal(E/K))).comm σ' τ']⟩⟩
    have hexpF : Monoid.exponent Gal(F/K) ∣ n := by
      refine Monoid.exponent_dvd_of_forall_pow_eq_one fun σ => ?_
      obtain ⟨σ', rfl⟩ := hsurj σ
      rw [← map_pow, Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hexp σ', map_one]
    have htop := adjoin_nthRoots_eq_top K n F hexpF

    let φ : F →ₐ[K] Ω := E.val.comp F.val
    have hmap : (⊤ : IntermediateField K F).map φ ≤ kummerField K n Ω (kummerGroup K n E) := by
      rw [← htop, adjoin_map, kummerField, adjoin_le_iff]
      rintro _ ⟨γ, ⟨hγ0, b, hb⟩, rfl⟩
      have hb0 : b ≠ 0 := by
        rintro rfl
        rw [map_zero] at hb
        exact pow_ne_zero n hγ0 hb.symm
      refine subset_adjoin _ _ ⟨Units.mk0 b hb0, ?_, ?_⟩
      · refine mk_mem_kummerGroup.mpr ⟨F.val γ, ?_⟩
        rw [← map_pow, ← hb, AlgHom.commutes]
        rfl
      · change (φ γ) ^ n = algebraMap K Ω b
        rw [← map_pow, ← hb, AlgHom.commutes]
    exact hmap ((IntermediateField.map_mem_map _ φ).mpr (IntermediateField.mem_top (x := ⟨x', hxF⟩)))

/- English proof (translation)
Use `choose r hr using fun x : Δ => exists_pow_eq_algebraMap K n Ω (x : UnitsModPow K n).out`. Use `⟨r, fun x => ⟨_, QuotientGroup.out_eq' _, hr x⟩, le_antisymm ?_ ?_⟩` and prove the remaining obligations. Rewrite using `[kummerField, adjoin_le_iff]`. Introduce and unpack `α ⟨a, ha, hα⟩`. Take `⟨c, hc⟩` from `exists_eq_algebraMap_mul (K := K) (QuotientGroup.out_eq' (a : UnitsModPow K n)).symm hα (hr ⟨_, ha⟩)`.

Rewrite using `[SetLike.mem_coe, hc]`. Conclude with `mul_mem (IntermediateField.algebraMap_mem _ _) (subset_adjoin _ _ ⟨_, rfl⟩)`. Rewrite using `[kummerField, adjoin_le_iff]`. Introduce and unpack `_ ⟨x, rfl⟩`. Use `subset_adjoin _ _ ⟨(x : UnitsModPow K n).out, ?_, hr x⟩` and prove the remaining obligations.

Rewrite using `[QuotientGroup.out_eq']`. Conclude with `x.2`.
-/
lemma exists_finite_generators_kummerField [IsSepClosed Ω] (Δ : Subgroup (UnitsModPow K n)) :
    ∃ r : Δ → Ω, (∀ x : Δ, ∃ a : Kˣ, (a : UnitsModPow K n) = x ∧ r x ^ n = algebraMap K Ω a) ∧
      kummerField K n Ω Δ = adjoin K (Set.range r) := by
  choose r hr using fun x : Δ => exists_pow_eq_algebraMap K n Ω (x : UnitsModPow K n).out
  refine ⟨r, fun x => ⟨_, QuotientGroup.out_eq' _, hr x⟩, le_antisymm ?_ ?_⟩
  · rw [kummerField, adjoin_le_iff]
    rintro α ⟨a, ha, hα⟩
    obtain ⟨c, hc⟩ := exists_eq_algebraMap_mul (K := K)
      (QuotientGroup.out_eq' (a : UnitsModPow K n)).symm hα (hr ⟨_, ha⟩)
    rw [SetLike.mem_coe, hc]
    exact mul_mem (IntermediateField.algebraMap_mem _ _) (subset_adjoin _ _ ⟨_, rfl⟩)
  · rw [kummerField, adjoin_le_iff]
    rintro _ ⟨x, rfl⟩
    refine subset_adjoin _ _ ⟨(x : UnitsModPow K n).out, ?_, hr x⟩
    rw [QuotientGroup.out_eq']
    exact x.2

/- English proof (translation)
Take `⟨r, hr, heq⟩` from `exists_finite_generators_kummerField K n Ω Δ`. Rewrite using `[heq]`. Conclude with `finiteDimensional_adjoin fun α ⟨x, hx⟩ => by`. Take `⟨a, -, ha⟩` from `hr x`. Conclude with `isIntegral_of_pow_eq_algebraMap K n Ω (hx ▸ ha)`.
-/
theorem finiteDimensional_kummerField [IsSepClosed Ω] (Δ : Subgroup (UnitsModPow K n))
    [Finite Δ] : FiniteDimensional K (kummerField K n Ω Δ) := by
  obtain ⟨r, hr, heq⟩ := exists_finite_generators_kummerField K n Ω Δ
  rw [heq]
  exact finiteDimensional_adjoin fun α ⟨x, hx⟩ => by
    obtain ⟨a, -, ha⟩ := hr x
    exact isIntegral_of_pow_eq_algebraMap K n Ω (hx ▸ ha)

/- English proof (translation)
Use `finiteDimensional_kummerField K n Ω Δ` as an intermediate fact. Use `kummerField_isGalois K n Ω Δ` as an intermediate fact. Use `kummerField_isMulCommutative K n Ω Δ` as an intermediate fact. Rewrite using `[← card_kummerGroup K n _ (kummerField_exponent_dvd K n Ω Δ), kummerGroup_kummerField]`.
-/
theorem finrank_kummerField [IsSepClosed Ω] (Δ : Subgroup (UnitsModPow K n)) [Finite Δ] :
    Module.finrank K (kummerField K n Ω Δ) = Nat.card Δ := by
  have := finiteDimensional_kummerField K n Ω Δ
  have := kummerField_isGalois K n Ω Δ
  have := kummerField_isMulCommutative K n Ω Δ
  rw [← card_kummerGroup K n _ (kummerField_exponent_dvd K n Ω Δ), kummerGroup_kummerField]

noncomputable def kummerCorrespondence [IsSepClosed Ω] :
    Subgroup (UnitsModPow K n) ≃o {E : IntermediateField K Ω //
      IsGalois K E ∧ IsMulCommutative Gal(E/K) ∧ Monoid.exponent Gal(E/K) ∣ n} where
  toFun Δ := ⟨kummerField K n Ω Δ, kummerField_isGalois K n Ω Δ,
    kummerField_isMulCommutative K n Ω Δ, kummerField_exponent_dvd K n Ω Δ⟩
  invFun E := kummerGroup K n E.1
  left_inv Δ := kummerGroup_kummerField K n Ω Δ
  right_inv := by
    rintro ⟨E, h1, h2, h3⟩
    exact Subtype.ext (kummerField_kummerGroup_eq K n Ω E h3)
  map_rel_iff' {Δ Δ'} := by
    constructor
    · intro h
      have h' : kummerField K n Ω Δ ≤ kummerField K n Ω Δ' := h
      rw [← kummerGroup_kummerField K n Ω Δ, ← kummerGroup_kummerField K n Ω Δ']
      exact kummerGroup_mono K n Ω h'
    · intro h
      exact kummerField_mono K n Ω h

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] lemma kummerCorrespondence_apply [IsSepClosed Ω] (Δ : Subgroup (UnitsModPow K n)) :
    (kummerCorrespondence K n Ω Δ : IntermediateField K Ω) = kummerField K n Ω Δ := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] lemma kummerCorrespondence_symm_apply [IsSepClosed Ω]
    (E : {E : IntermediateField K Ω //
      IsGalois K E ∧ IsMulCommutative Gal(E/K) ∧ Monoid.exponent Gal(E/K) ∣ n}) :
    (kummerCorrespondence K n Ω).symm E = kummerGroup K n E.1 := rfl

end Correspondence

end GroundTheory.ProfCoh
