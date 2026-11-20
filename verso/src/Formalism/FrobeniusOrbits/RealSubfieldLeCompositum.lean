import Mathlib
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Galois
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.ConjReal
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.RealCyclotomicSubfield
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.FrobMulInertia

open NumberField IntermediateField

noncomputable section

namespace Formalism.FrobeniusOrbits

open Formalism.TwoAdicCyclotomicDecomposition

section Hcl

variable {e : ℕ}

/- English proof (translation)
Unfold `hcl`. Rewrite using `[QuotientGroup.eq, Subgroup.mem_zpowers_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨k, hk⟩`. Break down `Int.even_or_odd k with hk2 | hk2` into its components or cases.

Use `left`. Rewrite `hk` using `[hk2.neg_one_zpow]`. Conclude with `inv_mul_eq_one.mp hk.symm`. Use `right`. Rewrite `hk` using `[hk2.neg_one_zpow]`.

Establish `hv : v = u * -1` using `inv_mul_eq_iff_eq_mul.mp hk.symm`. Rewrite using `[hv, mul_neg_one, neg_neg]`. Introduce and unpack `(rfl | rfl)`. Conclude with `⟨0, by simp⟩`. Conclude with `⟨1, by simp⟩`.
-/
theorem hcl_eq_hcl_iff (u v : (ZMod (2 ^ (e + 2)))ˣ) :
    hcl e u = hcl e v ↔ u = v ∨ u = -v := by
  unfold hcl
  rw [QuotientGroup.eq, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, hk⟩
    rcases Int.even_or_odd k with hk2 | hk2
    · left
      rw [hk2.neg_one_zpow] at hk
      exact inv_mul_eq_one.mp hk.symm
    · right
      rw [hk2.neg_one_zpow] at hk
      have hv : v = u * -1 := inv_mul_eq_iff_eq_mul.mp hk.symm
      rw [hv, mul_neg_one, neg_neg]
  · rintro (rfl | rfl)
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩

/- English proof (translation)
Unfold `hcl`. Rewrite using `[QuotientGroup.eq, Subgroup.mem_zpowers_iff]`. Conclude with `⟨1, by simp⟩`.
-/
theorem hcl_neg (u : (ZMod (2 ^ (e + 2)))ˣ) : hcl e (-u) = hcl e u := by
  unfold hcl
  rw [QuotientGroup.eq, Subgroup.mem_zpowers_iff]
  exact ⟨1, by simp⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem hcl_one : hcl e (1 : (ZMod (2 ^ (e + 2)))ˣ) = 1 := rfl

/- English proof (translation)
Rewrite using `[hcl_neg, hcl_one]`.
-/
theorem hcl_neg_one : hcl e (-1 : (ZMod (2 ^ (e + 2)))ˣ) = 1 := by
  rw [hcl_neg, hcl_one]

end Hcl

section Subfields

variable {L : Type*} [Field L] [Algebra ℚ L] {ζ a b : L}

end Subfields

section Signs

variable {e : ℕ} {L : Type*} [Field L] [Algebra ℚ L] {ζ a b : L}

/- English proof (translation)
Unfold `Formalism.TwoAdicCyclotomicDecomposition.sgn`. Distinguish the cases in `hx : σ x = x`. Rewrite using `[if_pos hx]`. Conclude with `iff_of_true rfl hx`. Rewrite using `[if_neg hx]`.

Conclude with `iff_of_false (by decide) hx`.
-/
private lemma sgn_eq_one_iff_apply_eq {M : Type*} [Field M] [Algebra ℚ M] (σ : M ≃ₐ[ℚ] M) (x : M) :
    Formalism.TwoAdicCyclotomicDecomposition.sgn σ x = 1 ↔ σ x = x := by
  unfold Formalism.TwoAdicCyclotomicDecomposition.sgn
  by_cases hx : σ x = x
  · rw [if_pos hx]
    exact iff_of_true rfl hx
  · rw [if_neg hx]
    exact iff_of_false (by decide) hx

/- English proof (translation)
Unfold `galE Psi`. Rewrite using `[MonoidHom.mem_ker]`. Conclude with `sgn_eq_one_iff_apply_eq σ (bE ζ a b)`.
-/
theorem galE_mem_Psi_iff (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) :
    galE e ζ a b σ ∈ Psi e ↔ σ (bE ζ a b) = bE ζ a b := by
  unfold galE Psi
  rw [MonoidHom.mem_ker]
  exact sgn_eq_one_iff_apply_eq σ (bE ζ a b)

end Signs

section Layer

variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}

/- English proof (translation)
The claim follows from `Galois.isGalois_hostE hqd h`.
-/
theorem hostE_isGalois (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) :
    IsGalois ℚ (hostE ζ a b) :=
  Galois.isGalois_hostE hqd h

/- English proof (translation)
The claim follows from `Galois.finrank_cmField hqd h`.
-/
theorem finrank_cmField (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) :
    Module.finrank ℚ (hostE ζ a b) = 2 ^ (e + 2) :=
  Galois.finrank_cmField hqd h

/- English proof (translation)
The claim follows from `(hostGalois e q d hqd L ζ a b h).2.2.1 σ τ`.
-/
theorem galE_mul (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b)
    (σ τ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) :
    galE e ζ a b (σ * τ) = galE e ζ a b σ * galE e ζ a b τ :=
  (hostGalois e q d hqd L ζ a b h).2.2.1 σ τ

/- English proof (translation)
The claim follows from `(hostGalois e q d hqd L ζ a b h).2.2.2`.
-/
theorem galE_bijective (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) :
    Function.Bijective (galE e ζ a b) :=
  (hostGalois e q d hqd L ζ a b h).2.2.2

def galEquiv (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) :
    (hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) ≃* GG e :=
  MulEquiv.ofBijective (MonoidHom.mk' (galE e ζ a b) (galE_mul hqd h)) (galE_bijective hqd h)

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem galEquiv_apply (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b)
    (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) : galEquiv hqd h σ = galE e ζ a b σ := rfl

/- English proof (translation)
Simplify using `using map_one (galEquiv hqd h)`.
-/
theorem galE_one (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) :
    galE e ζ a b (1 : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) = 1 := by
  simpa using map_one (galEquiv hqd h)

/- English proof (translation)
Simplify using `using map_inv (galEquiv hqd h) σ`.
-/
theorem galE_inv (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b)
    (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) : galE e ζ a b σ⁻¹ = (galE e ζ a b σ)⁻¹ := by
  simpa using map_inv (galEquiv hqd h) σ

/- English proof (translation)
Simplify using `using map_pow (galEquiv hqd h) σ k`.
-/
theorem galE_pow (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b)
    (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (k : ℕ) : galE e ζ a b (σ ^ k) = galE e ζ a b σ ^ k := by
  simpa using map_pow (galEquiv hqd h) σ k

/- English proof (translation)
The claim follows from `(galE_bijective hqd h).1`.
-/
theorem galE_injective (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) :
    Function.Injective (galE e ζ a b) := (galE_bijective hqd h).1

/- English proof (translation)
The claim follows from `(galE_bijective hqd h).2 g`.
-/
theorem exists_galE_eq (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) (g : GG e) :
    ∃ σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b, galE e ζ a b σ = g := (galE_bijective hqd h).2 g

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hs`. Conclude with `galE_injective hqd h (hs.trans (galE_one hqd h).symm)`. Introduce and unpack `rfl`. Conclude with `galE_one hqd h`.
-/
theorem galE_eq_one_iff (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b)
    (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) : galE e ζ a b σ = 1 ↔ σ = 1 := by
  constructor
  · intro hs
    exact galE_injective hqd h (hs.trans (galE_one hqd h).symm)
  · rintro rfl
    exact galE_one hqd h

/- English proof (translation)
The claim follows from `Galois.exists_lift hqd h σ`.
-/
theorem galE_exists_lift (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b)
    (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) :
    ∃ τ : L ≃ₐ[ℚ] L, ∀ x : hostE ζ a b, ((σ x : hostE ζ a b) : L) = τ x :=
  Galois.exists_lift hqd h σ

/- English proof (translation)
Rewrite using `[hcl_eq_hcl_iff]`. Establish `hz : ζ ≠ 0` using `hζ.ne_zero (pow_ne_zero _ two_ne_zero)`. Establish `hx2 : ζ ^ (u : ZMod (2 ^ (e + 2))).val * ζ⁻¹ ^ (u : ZMod (2 ^ (e + 2))).val = 1`. Rewrite using `[← mul_pow, mul_inv_cancel₀ hz, one_pow]`. Establish `hy2 : ζ ^ (v : ZMod (2 ^ (e + 2))).val * ζ⁻¹ ^ (v : ZMod (2 ^ (e + 2))).val = 1`.

Rewrite using `[← mul_pow, mul_inv_cancel₀ hz, one_pow]`. Establish `key : (ζ ^ (u : ZMod (2 ^ (e + 2))).val - ζ ^ (v : ZMod (2 ^ (e + 2))).val) * (ζ ^ (u : ZMod (2 ^ (e + 2))).val * ζ ^ (v : ZMod (2 ^ (e + 2))).val - 1) = 0`. Take the linear combination `(ζ ^ (u : ZMod (2 ^ (e + 2))).val * ζ ^ (v : ZMod (2 ^ (e + 2))).val) * huv - ζ ^ (v : ZMod (2 ^ (e + 2))).val * hx2 + ζ ^ (u : ZMod (2 ^ (e + 2))).val * hy2`. Break down `mul_eq_zero.1 key with h1 | h1` into its components or cases. Use `left`.

Establish `h3` using `sub_eq_zero.1 h1`. Establish `hij` using `hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h3`. Conclude with `Units.ext (ZMod.val_injective _ hij)`. Use `right`. Establish `h3 : ζ ^ ((u : ZMod (2 ^ (e + 2))).val + (v : ZMod (2 ^ (e + 2))).val) = 1`.

Rewrite using `[pow_add]`. Conclude with `sub_eq_zero.1 h1`. Establish `h4` using `(hζ.pow_eq_one_iff_dvd _).1 h3`. Establish `h5` using `(CharP.cast_eq_zero_iff (ZMod (2 ^ (e + 2))) (2 ^ (e + 2)) _).2 h4`. Move the coercions through the operations in `at h5`.

Simplify using `only [ZMod.natCast_val, ZMod.cast_id', id] at h5`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_neg]`. Conclude with `eq_neg_of_add_eq_zero_left h5`.
-/
private lemma hcl_eq_of_pow_add_inv_pow_eq {M : Type} [Field M] {e : ℕ} {ζ : M} (hζ : IsPrimitiveRoot ζ (2 ^ (e + 2)))
    (u v : (ZMod (2 ^ (e + 2)))ˣ)
    (huv : ζ ^ (u : ZMod (2 ^ (e + 2))).val + ζ⁻¹ ^ (u : ZMod (2 ^ (e + 2))).val =
      ζ ^ (v : ZMod (2 ^ (e + 2))).val + ζ⁻¹ ^ (v : ZMod (2 ^ (e + 2))).val) :
    hcl e u = hcl e v := by
  rw [hcl_eq_hcl_iff]
  have hz : ζ ≠ 0 := hζ.ne_zero (pow_ne_zero _ two_ne_zero)
  have hx2 : ζ ^ (u : ZMod (2 ^ (e + 2))).val * ζ⁻¹ ^ (u : ZMod (2 ^ (e + 2))).val = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hz, one_pow]
  have hy2 : ζ ^ (v : ZMod (2 ^ (e + 2))).val * ζ⁻¹ ^ (v : ZMod (2 ^ (e + 2))).val = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hz, one_pow]
  have key : (ζ ^ (u : ZMod (2 ^ (e + 2))).val - ζ ^ (v : ZMod (2 ^ (e + 2))).val) *
      (ζ ^ (u : ZMod (2 ^ (e + 2))).val * ζ ^ (v : ZMod (2 ^ (e + 2))).val - 1) = 0 := by
    linear_combination (ζ ^ (u : ZMod (2 ^ (e + 2))).val * ζ ^ (v : ZMod (2 ^ (e + 2))).val) * huv -
      ζ ^ (v : ZMod (2 ^ (e + 2))).val * hx2 + ζ ^ (u : ZMod (2 ^ (e + 2))).val * hy2
  rcases mul_eq_zero.1 key with h1 | h1
  · left
    have h3 := sub_eq_zero.1 h1
    have hij := hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h3
    exact Units.ext (ZMod.val_injective _ hij)
  · right
    have h3 : ζ ^ ((u : ZMod (2 ^ (e + 2))).val + (v : ZMod (2 ^ (e + 2))).val) = 1 := by
      rw [pow_add]
      exact sub_eq_zero.1 h1
    have h4 := (hζ.pow_eq_one_iff_dvd _).1 h3
    have h5 := (CharP.cast_eq_zero_iff (ZMod (2 ^ (e + 2))) (2 ^ (e + 2)) _).2 h4
    push_cast at h5
    simp only [ZMod.natCast_val, ZMod.cast_id', id] at h5
    apply Units.ext
    rw [Units.val_neg]
    exact eq_neg_of_add_eq_zero_left h5

/- English proof (translation)
Establish `hd : 2 ^ (e + 2) ∣ (-x).val + x.val`. Rewrite using `[← CharP.cast_eq_zero_iff (ZMod (2 ^ (e + 2))) (2 ^ (e + 2))]`. Use `push_cast`. Simplify using `only [ZMod.natCast_val, ZMod.cast_id', id]`. Conclude with `neg_add_cancel x`.

Establish `h1 : ζ ^ ((-x).val + x.val) = 1` using `(hζ.pow_eq_one_iff_dvd _).2 hd`. Rewrite `h1` using `[pow_add]`. Rewrite using `[inv_pow]`. Conclude with `eq_inv_of_mul_eq_one_left h1`.
-/
private lemma zpow_neg_val_eq_inv_pow_val_of_isPrimitiveRoot {M : Type} [Field M] {e : ℕ} {ζ : M} (hζ : IsPrimitiveRoot ζ (2 ^ (e + 2)))
    (x : ZMod (2 ^ (e + 2))) : ζ ^ (-x).val = ζ⁻¹ ^ x.val := by
  have hd : 2 ^ (e + 2) ∣ (-x).val + x.val := by
    rw [← CharP.cast_eq_zero_iff (ZMod (2 ^ (e + 2))) (2 ^ (e + 2))]
    push_cast
    simp only [ZMod.natCast_val, ZMod.cast_id', id]
    exact neg_add_cancel x
  have h1 : ζ ^ ((-x).val + x.val) = 1 := (hζ.pow_eq_one_iff_dvd _).2 hd
  rw [pow_add] at h1
  rw [inv_pow]
  exact eq_inv_of_mul_eq_one_left h1

/- English proof (translation)
Establish `hs : ∀ (x : hostE ζ a b) (y : L), (x : L) = y → Formalism.TwoAdicCyclotomicDecomposition.sgn σ x = Formalism.TwoAdicCyclotomicDecomposition.sgn τ y`. Introduce `x y hxy`. Establish `hiff : σ x = x ↔ τ y = y`. Rewrite using `[Subtype.ext_iff, hστ, hxy]`. Unfold `Formalism.TwoAdicCyclotomicDecomposition.sgn`.

Distinguish the cases in `h1 : σ x = x`. Rewrite using `[if_pos h1, if_pos (hiff.1 h1)]`. Rewrite using `[if_neg h1, if_neg (fun h2 => h1 (hiff.2 h2))]`. Establish `hθ : ((σ (thE ζ a b) : hostE ζ a b) : L) = ζ ^ ((h.1.autToPow ℚ τ : (ZMod (2 ^ (e + 2)))ˣ) : ZMod (2 ^ (e + 2))).val + ζ⁻¹ ^ ((h.1.autToPow ℚ τ : (ZMod (2 ^ (e + 2)))ˣ) : ZMod (2 ^ (e + 2))).val`. Rewrite using `[hστ]`.

Use `show τ (ζ + ζ⁻¹) = _`. Rewrite using `[map_add, map_inv₀, ← h.1.autToPow_spec ℚ τ, inv_pow]`. Unfold `galE galMap`. Simplify using `only`. Rewrite using `[hs (aE ζ a b) a rfl, hs (bE ζ a b) b rfl]`.

Use `congr 1`. Unfold `hPart`. Establish `hex : ∃ u : (ZMod (2 ^ (e + 2)))ˣ, ((σ (thE ζ a b) : hostE ζ a b) : L) = ζ ^ (u : ZMod (2 ^ (e + 2))).val + ζ⁻¹ ^ (u : ZMod (2 ^ (e + 2))).val` using `⟨_, hθ⟩`. Rewrite using `[dif_pos hex]`. Conclude with `hcl_eq_of_pow_add_inv_pow_eq h.1 _ _ ((Classical.choose_spec hex).symm.trans hθ)`.
-/
theorem galE_of_lift (h : IsLayer (e + 2) q d ζ a b) {σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b}
    {τ : L ≃ₐ[ℚ] L} (hστ : ∀ x : hostE ζ a b, ((σ x : hostE ζ a b) : L) = τ x) :
    galE e ζ a b σ =
      (((galMap h.1 a b τ).2.1, (galMap h.1 a b τ).2.2), hcl e (galMap h.1 a b τ).1) := by
  have hs : ∀ (x : hostE ζ a b) (y : L), (x : L) = y → Formalism.TwoAdicCyclotomicDecomposition.sgn σ x = Formalism.TwoAdicCyclotomicDecomposition.sgn τ y := by
    intro x y hxy
    have hiff : σ x = x ↔ τ y = y := by
      rw [Subtype.ext_iff, hστ, hxy]
    unfold Formalism.TwoAdicCyclotomicDecomposition.sgn
    by_cases h1 : σ x = x
    · rw [if_pos h1, if_pos (hiff.1 h1)]
    · rw [if_neg h1, if_neg (fun h2 => h1 (hiff.2 h2))]
  have hθ : ((σ (thE ζ a b) : hostE ζ a b) : L) =
      ζ ^ ((h.1.autToPow ℚ τ : (ZMod (2 ^ (e + 2)))ˣ) : ZMod (2 ^ (e + 2))).val +
        ζ⁻¹ ^ ((h.1.autToPow ℚ τ : (ZMod (2 ^ (e + 2)))ˣ) : ZMod (2 ^ (e + 2))).val := by
    rw [hστ]
    show τ (ζ + ζ⁻¹) = _
    rw [map_add, map_inv₀, ← h.1.autToPow_spec ℚ τ, inv_pow]
  unfold galE galMap
  dsimp only
  rw [hs (aE ζ a b) a rfl, hs (bE ζ a b) b rfl]
  congr 1
  unfold hPart
  have hex : ∃ u : (ZMod (2 ^ (e + 2)))ˣ, ((σ (thE ζ a b) : hostE ζ a b) : L) =
      ζ ^ (u : ZMod (2 ^ (e + 2))).val + ζ⁻¹ ^ (u : ZMod (2 ^ (e + 2))).val := ⟨_, hθ⟩
  rw [dif_pos hex]
  exact hcl_eq_of_pow_add_inv_pow_eq h.1 _ _ ((Classical.choose_spec hex).symm.trans hθ)

/- English proof (translation)
Establish `ha : (aE ζ a b) ^ 2 = -((q : ℕ) : hostE ζ a b)`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[aE, h.2.1]`. Establish `hs : (σ (aE ζ a b)) ^ 2 = (aE ζ a b) ^ 2`. Rewrite using `[← map_pow, ha, map_neg, map_natCast]`.

Establish `hor : σ (aE ζ a b) = aE ζ a b ∨ σ (aE ζ a b) = -aE ζ a b` using `sq_eq_sq_iff_eq_or_eq_neg.mp hs`. Unfold `galE`. Simplify using `only`. Unfold `Formalism.TwoAdicCyclotomicDecomposition.sgn`. Distinguish the cases in `hx : σ (aE ζ a b) = aE ζ a b`.

Rewrite using `[if_pos hx, hx]`. Simplify using `[aE]`. Rewrite using `[if_neg hx]`. Break down `hor with h1 | h1` into its components or cases. Conclude with `absurd h1 hx`.

Rewrite using `[h1]`. Simplify using `[aE]`.
-/
theorem galE_aE (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b)
    (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) :
    ((σ (aE ζ a b) : hostE ζ a b) : L) = ((((galE e ζ a b σ).1.1 : ℤˣ) : ℤ) : L) * a := by
  have ha : (aE ζ a b) ^ 2 = -((q : ℕ) : hostE ζ a b) := by
    apply Subtype.ext
    simp [aE, h.2.1]
  have hs : (σ (aE ζ a b)) ^ 2 = (aE ζ a b) ^ 2 := by
    rw [← map_pow, ha, map_neg, map_natCast]
  have hor : σ (aE ζ a b) = aE ζ a b ∨ σ (aE ζ a b) = -aE ζ a b :=
    sq_eq_sq_iff_eq_or_eq_neg.mp hs
  unfold galE
  dsimp only
  unfold Formalism.TwoAdicCyclotomicDecomposition.sgn
  by_cases hx : σ (aE ζ a b) = aE ζ a b
  · rw [if_pos hx, hx]
    simp [aE]
  · rw [if_neg hx]
    rcases hor with h1 | h1
    · exact absurd h1 hx
    · rw [h1]
      simp [aE]

/- English proof (translation)
Establish `ha : (bE ζ a b) ^ 2 = -((d : ℕ) : hostE ζ a b)`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[bE, h.2.2.1]`. Establish `hs : (σ (bE ζ a b)) ^ 2 = (bE ζ a b) ^ 2`. Rewrite using `[← map_pow, ha, map_neg, map_natCast]`.

Establish `hor : σ (bE ζ a b) = bE ζ a b ∨ σ (bE ζ a b) = -bE ζ a b` using `sq_eq_sq_iff_eq_or_eq_neg.mp hs`. Unfold `galE`. Simplify using `only`. Unfold `Formalism.TwoAdicCyclotomicDecomposition.sgn`. Distinguish the cases in `hx : σ (bE ζ a b) = bE ζ a b`.

Rewrite using `[if_pos hx, hx]`. Simplify using `[bE]`. Rewrite using `[if_neg hx]`. Break down `hor with h1 | h1` into its components or cases. Conclude with `absurd h1 hx`.

Rewrite using `[h1]`. Simplify using `[bE]`.
-/
theorem galE_bE (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b)
    (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) :
    ((σ (bE ζ a b) : hostE ζ a b) : L) = ((((galE e ζ a b σ).1.2 : ℤˣ) : ℤ) : L) * b := by
  have ha : (bE ζ a b) ^ 2 = -((d : ℕ) : hostE ζ a b) := by
    apply Subtype.ext
    simp [bE, h.2.2.1]
  have hs : (σ (bE ζ a b)) ^ 2 = (bE ζ a b) ^ 2 := by
    rw [← map_pow, ha, map_neg, map_natCast]
  have hor : σ (bE ζ a b) = bE ζ a b ∨ σ (bE ζ a b) = -bE ζ a b :=
    sq_eq_sq_iff_eq_or_eq_neg.mp hs
  unfold galE
  dsimp only
  unfold Formalism.TwoAdicCyclotomicDecomposition.sgn
  by_cases hx : σ (bE ζ a b) = bE ζ a b
  · rw [if_pos hx, hx]
    simp [bE]
  · rw [if_neg hx]
    rcases hor with h1 | h1
    · exact absurd h1 hx
    · rw [h1]
      simp [bE]

/- English proof (translation)
Take `⟨τ, hτ⟩` from `galE_exists_lift hqd h σ`. Establish `hθ : ((σ (thE ζ a b) : hostE ζ a b) : L) = ζ ^ ((h.1.autToPow ℚ τ : (ZMod (2 ^ (e + 2)))ˣ) : ZMod (2 ^ (e + 2))).val + ζ⁻¹ ^ ((h.1.autToPow ℚ τ : (ZMod (2 ^ (e + 2)))ˣ) : ZMod (2 ^ (e + 2))).val`. Rewrite using `[hτ]`. Use `show τ (ζ + ζ⁻¹) = _`. Rewrite using `[map_add, map_inv₀, ← h.1.autToPow_spec ℚ τ, inv_pow]`.

Rewrite using `[galE_of_lift h hτ]`. Unfold `galMap`. Simplify using `only`. Rewrite using `[hθ]`. Prove the components needed by the constructor for the conclusion.

Introduce `hk`. Break down `(hcl_eq_hcl_iff _ _).1 hk with h1 | h1` into its components or cases. Rewrite using `[h1]`. Rewrite using `[h1, Units.val_neg, zpow_neg_val_eq_inv_pow_val_of_isPrimitiveRoot h.1, zpow_neg_val_eq_inv_pow_val_of_isPrimitiveRoot h.1.inv, inv_inv, add_comm]`. Introduce `hk`.

Conclude with `hcl_eq_of_pow_add_inv_pow_eq h.1 _ _ hk`.
-/
theorem galE_snd_eq_hcl_iff (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b)
    (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (u : (ZMod (2 ^ (e + 2)))ˣ) :
    (galE e ζ a b σ).2 = hcl e u ↔
      ((σ (thE ζ a b) : hostE ζ a b) : L) =
        ζ ^ (u : ZMod (2 ^ (e + 2))).val + ζ⁻¹ ^ (u : ZMod (2 ^ (e + 2))).val := by
  obtain ⟨τ, hτ⟩ := galE_exists_lift hqd h σ
  have hθ : ((σ (thE ζ a b) : hostE ζ a b) : L) =
      ζ ^ ((h.1.autToPow ℚ τ : (ZMod (2 ^ (e + 2)))ˣ) : ZMod (2 ^ (e + 2))).val +
        ζ⁻¹ ^ ((h.1.autToPow ℚ τ : (ZMod (2 ^ (e + 2)))ˣ) : ZMod (2 ^ (e + 2))).val := by
    rw [hτ]
    show τ (ζ + ζ⁻¹) = _
    rw [map_add, map_inv₀, ← h.1.autToPow_spec ℚ τ, inv_pow]
  rw [galE_of_lift h hτ]
  unfold galMap
  dsimp only
  rw [hθ]
  constructor
  · intro hk
    rcases (hcl_eq_hcl_iff _ _).1 hk with h1 | h1
    · rw [h1]
    · rw [h1, Units.val_neg, zpow_neg_val_eq_inv_pow_val_of_isPrimitiveRoot h.1, zpow_neg_val_eq_inv_pow_val_of_isPrimitiveRoot h.1.inv, inv_inv, add_comm]
  · intro hk
    exact hcl_eq_of_pow_add_inv_pow_eq h.1 _ _ hk

def conjE (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b :=
  (galEquiv hqd h).symm (cc e)

/- English proof (translation)
Rewrite using `[← galEquiv_apply hqd h]`. Conclude with `(galEquiv hqd h).apply_symm_apply (cc e)`.
-/
theorem galE_conjE (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) :
    galE e ζ a b (conjE hqd h) = cc e := by
  rw [← galEquiv_apply hqd h]
  exact (galEquiv hqd h).apply_symm_apply (cc e)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl`. Conclude with `galE_conjE hqd h`. Introduce `hs`. Conclude with `galE_injective hqd h (hs.trans (galE_conjE hqd h).symm)`.
-/
theorem eq_conjE_iff (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b)
    (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) : σ = conjE hqd h ↔ galE e ζ a b σ = cc e := by
  constructor
  · rintro rfl
    exact galE_conjE hqd h
  · intro hs
    exact galE_injective hqd h (hs.trans (galE_conjE hqd h).symm)

/- English proof (translation)
The claim follows from `((hostConj_of hostGalois hostGalSpec e q d hqd L ζ a b h).2 φ (conjE hqd h)).2 (galE_conjE hqd h) x`.
-/
theorem conjE_apply (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b)
    (φ : hostE ζ a b →+* ℂ) (x : hostE ζ a b) :
    φ (conjE hqd h x) = starRingEnd ℂ (φ x) :=
  ((hostConj_of hostGalois hostGalSpec e q d hqd L ζ a b h).2 φ (conjE hqd h)).2
    (galE_conjE hqd h) x

/- English proof (translation)
Rewrite using `[← eq_conjE_iff hqd h]`. Prove the components needed by the constructor for the conclusion. Introduce `hσ`. Conclude with `AlgEquiv.ext fun x => φ.injective (by rw [hσ, conjE_apply hqd h])`. Introduce and unpack `rfl x`.

Conclude with `conjE_apply hqd h φ x`.
-/
theorem isConj_iff_galE (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b)
    (φ : hostE ζ a b →+* ℂ) (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) :
    (∀ x, φ (σ x) = starRingEnd ℂ (φ x)) ↔ galE e ζ a b σ = cc e := by
  rw [← eq_conjE_iff hqd h]
  constructor
  · intro hσ
    exact AlgEquiv.ext fun x => φ.injective (by rw [hσ, conjE_apply hqd h])
  · rintro rfl x
    exact conjE_apply hqd h φ x

/- English proof (translation)
The claim follows from `(hostConj_of hostGalois hostGalSpec e q d hqd L ζ a b h).1`.
-/
theorem isCMField_hostE (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) :
    IsCMField (hostE ζ a b) :=
  (hostConj_of hostGalois hostGalSpec e q d hqd L ζ a b h).1

/- English proof (translation)
The claim follows from `hostReal_of hostGalois hostGalSpec (hostConj_of hostGalois hostGalSpec) e q d hqd L ζ a b h`.
-/
theorem hostReal_at (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) :
    Module.finrank ℚ (hostF ζ a b) = 2 ^ (e + 1) ∧
    ∀ x : hostE ζ a b,
      (x ∈ hostF ζ a b ↔
        ∀ σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b, galE e ζ a b σ = cc e → σ x = x) ∧
      (x ∈ hostF ζ a b ↔ (x : L) ∈ ℚ⟮a * b, ζ + ζ⁻¹⟯) :=
  hostReal_of hostGalois hostGalSpec (hostConj_of hostGalois hostGalSpec) e q d hqd L ζ a b h

/- English proof (translation)
The claim follows from `(hostReal_at hqd h).1`.
-/
theorem finrank_hostF (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) :
    Module.finrank ℚ (hostF ζ a b) = 2 ^ (e + 1) := (hostReal_at hqd h).1

/- English proof (translation)
Rewrite using `[((hostReal_at hqd h).2 x).1]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Conclude with `hx _ (galE_conjE hqd h)`. Introduce `hx σ hσ`.

Rewrite using `[(eq_conjE_iff hqd h σ).2 hσ]`. Conclude with `hx`.
-/
theorem conjE_mem_hostF_iff (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b)
    (x : hostE ζ a b) : x ∈ hostF ζ a b ↔ conjE hqd h x = x := by
  rw [((hostReal_at hqd h).2 x).1]
  constructor
  · intro hx
    exact hx _ (galE_conjE hqd h)
  · intro hx σ hσ
    rw [(eq_conjE_iff hqd h σ).2 hσ]
    exact hx

/- English proof (translation)
The claim follows from `((hostReal_at hqd h).2 x).2`.
-/
theorem mem_hostF_iff_adjoin (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b)
    (x : hostE ζ a b) : x ∈ hostF ζ a b ↔ (x : L) ∈ ℚ⟮a * b, ζ + ζ⁻¹⟯ := ((hostReal_at hqd h).2 x).2

end Layer

end Formalism.FrobeniusOrbits
