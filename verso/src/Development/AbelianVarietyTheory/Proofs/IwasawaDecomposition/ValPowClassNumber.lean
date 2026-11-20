import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameHeckeCharacterValueViaPowerGenerator
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeNormOfKummer
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.ChiVal

/- English proof (translation)
Take `⟨γ, h0, hγ⟩` from `GlobalTheory.Mem.FieldsEx.exists_gen v.asIdeal v.ne_bot`. Establish `h1 : (γ : L) ≠ 0` using `by exact_mod_cast h0`. Establish `h2` using `GlobalTheory.Mem.ValPow.inf_mul_val_pow L ξ ∅ (fun w _ => hu w) (fun w hw => absurd hw (Finset.notMem_empty w)) v (Finset.notMem_empty v) (classNumber L) (Units.mk0 _ h1) (by rw [← FractionalIdeal.coeIdeal_pow, hγ, FractionalIdeal.coeIdeal_span_singleton]; rfl) (fun w hw => absur …`. Rewrite `h2` using `[hi, one_mul]`. Then use the resulting hypothesis.
-/
theorem val_pow_classNumber {L : Type} [Field L] [NumberField L] (ξ : HChar L) (hu : ∀ v, ξ.UnrAt v) (hi : ∀ k, ξ.inf k = 1)
    (v : HeightOneSpectrum (𝓞 L)) : ξ.val v ^ classNumber L = 1 := by
  obtain ⟨γ, h0, hγ⟩ := GlobalTheory.Mem.FieldsEx.exists_gen v.asIdeal v.ne_bot
  have h1 : (γ : L) ≠ 0 := by exact_mod_cast h0
  have h2 := GlobalTheory.Mem.ValPow.inf_mul_val_pow L ξ ∅ (fun w _ => hu w) (fun w hw => absurd hw (Finset.notMem_empty w)) v
    (Finset.notMem_empty v) (classNumber L) (Units.mk0 _ h1)
    (by rw [← FractionalIdeal.coeIdeal_pow, hγ, FractionalIdeal.coeIdeal_span_singleton]; rfl)
    (fun w hw => absurd hw (Finset.notMem_empty w))
  rwa [hi, one_mul] at h2

/- English proof (translation)
Establish `: NeZero n` using `⟨hn⟩`. Take `⟨i, -, rfl⟩` from `(Complex.isPrimitiveRoot_exp n hn).eq_pow_of_pow_eq_one hx`. Conclude with `pow_mem hM i`.
-/
theorem mem_of_pow_eq_one (M : Subfield ℂ) {n : ℕ} (hn : n ≠ 0)
    (hM : Complex.exp (2 * Real.pi * Complex.I / (n : ℕ)) ∈ M) {x : ℂ} (hx : x ^ n = 1) : x ∈ M := by
  have : NeZero n := ⟨hn⟩
  obtain ⟨i, -, rfl⟩ := (Complex.isPrimitiveRoot_exp n hn).eq_pow_of_pow_eq_one hx
  exact pow_mem hM i

/- English proof (translation)
Establish `h0 : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0`. Rewrite using `[Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]`. Conclude with `v.ne_bot`. Establish `h1 : (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(((1 / 2 : ℝ)) : ℂ))) ^ 2 * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) = 1`. Rewrite using `[sq, ← Complex.cpow_add _ _ h0, show -(((1 / 2 : ℝ)) : ℂ) + -(((1 / 2 : ℝ)) : ℂ) = -1 by push_cast; ring, Complex.cpow_neg_one, inv_mul_cancel₀ h0]`.

Unfold `HChar.valTw`. Rewrite using `[mul_pow, mul_assoc, h1, mul_one, sq]`.
-/
theorem val_sq_eq {L : Type} [Field L] [NumberField L] (η : HChar L) (v : HeightOneSpectrum (𝓞 L)) :
    ((η.val v : ℂˣ) : ℂ) * ((η.val v : ℂˣ) : ℂ) = η.valTw (1 / 2) v ^ 2 * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) := by
  have h0 : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  have h1 : (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(((1 / 2 : ℝ)) : ℂ))) ^ 2 * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) = 1 := by
    rw [sq, ← Complex.cpow_add _ _ h0, show -(((1 / 2 : ℝ)) : ℂ) + -(((1 / 2 : ℝ)) : ℂ) = -1 by push_cast; ring,
      Complex.cpow_neg_one, inv_mul_cancel₀ h0]
  unfold HChar.valTw
  rw [mul_pow, mul_assoc, h1, mul_one, sq]

/- English proof (translation)
Unfold `chiId`. Use `finprod_induction (fun u : ℂˣ => (u : ℂ) ∈ M) (one_mem M) (fun a b ha hb => mul_mem ha hb) fun w => ?_` and prove the remaining obligations. Rewrite using `[Units.val_pow_eq_pow_val]`. Conclude with `pow_mem (h w) _`.
-/
theorem chiId_mem {L : Type} [Field L] [NumberField L] (χ : HChar L) (M : Subfield ℂ)
    (h : ∀ w, ((χ.val w : ℂˣ) : ℂ) ∈ M) (𝔞 : Submodule (𝓞 L) L) : chiId χ 𝔞 ∈ M := by
  unfold chiId
  refine finprod_induction (fun u : ℂˣ => (u : ℂ) ∈ M) (one_mem M) (fun a b ha hb => mul_mem ha hb) fun w => ?_
  rw [Units.val_pow_eq_pow_val]
  exact pow_mem (h w) _

/- English proof (translation)
Introduce `B X I h`. Establish `key : ∀ w, ((I.C.chiPsi.val w : ℂˣ) : ℂ) ∈ B.embLL.fieldRange`. Introduce `w`. Establish `hc` using `I.C.isEta.sq_chiPsi.div_cls I.C.isChi`. Establish `h1` using `val_pow_classNumber _ hc.unr hc.inf w`.

Take `⟨z, -, hz⟩` from `B.roots_Ks' (classNumber B.host.E) (by simp)`. Establish `h2 : (((I.C.chiPsi * (I.C.eta * I.C.eta)⁻¹).val w : ℂˣ) : ℂ) ∈ B.embLL.fieldRange` using `mem_of_pow_eq_one B.embLL.fieldRange (classNumber_ne_zero B.host.E) ⟨z, hz⟩ (by rw [← Units.val_pow_eq_pow_val, h1, Units.val_one])`. Establish `h3 : I.C.eta.valTw (1 / 2) w ∈ B.embLL.fieldRange` using `⟨_, h.ch_tied.etaVal w⟩`. Establish `h4 : I.C.chiPsi.val w = (I.C.chiPsi * (I.C.eta * I.C.eta)⁻¹).val w * (I.C.eta.val w * I.C.eta.val w)`. Rewrite using `[HChar.val_mul, HChar.val_inv, HChar.val_mul, inv_mul_cancel_right]`.

Rewrite using `[h4, Units.val_mul, Units.val_mul (I.C.eta.val w), val_sq_eq]`. Conclude with `mul_mem h2 (mul_mem (pow_mem h3 2) (natCast_mem _ _))`. Conclude with `⟨key, fun 𝔞 => chiId_mem _ _ key 𝔞⟩`.
-/
theorem chi_values : ∀ (B : Base) (X : PreX B.toPre) (I : ColIn B X), I.Ok →
    (∀ w, ∃ k : B.LL, B.embLL k = ((I.C.chiPsi.val w : ℂˣ) : ℂ)) ∧ ∀ 𝔞, ∃ k : B.LL, B.embLL k = I.chi 𝔞 := by
  intro B X I h
  have key : ∀ w, ((I.C.chiPsi.val w : ℂˣ) : ℂ) ∈ B.embLL.fieldRange := by
    intro w
    have hc := I.C.isEta.sq_chiPsi.div_cls I.C.isChi
    have h1 := val_pow_classNumber _ hc.unr hc.inf w
    obtain ⟨z, -, hz⟩ := B.roots_Ks' (classNumber B.host.E) (by simp)
    have h2 : (((I.C.chiPsi * (I.C.eta * I.C.eta)⁻¹).val w : ℂˣ) : ℂ) ∈ B.embLL.fieldRange :=
      mem_of_pow_eq_one B.embLL.fieldRange (classNumber_ne_zero B.host.E) ⟨z, hz⟩
        (by rw [← Units.val_pow_eq_pow_val, h1, Units.val_one])
    have h3 : I.C.eta.valTw (1 / 2) w ∈ B.embLL.fieldRange := ⟨_, h.ch_tied.etaVal w⟩
    have h4 : I.C.chiPsi.val w = (I.C.chiPsi * (I.C.eta * I.C.eta)⁻¹).val w * (I.C.eta.val w * I.C.eta.val w) := by
      rw [HChar.val_mul, HChar.val_inv, HChar.val_mul, inv_mul_cancel_right]
    rw [h4, Units.val_mul, Units.val_mul (I.C.eta.val w), val_sq_eq]
    exact mul_mem h2 (mul_mem (pow_mem h3 2) (natCast_mem _ _))
  exact ⟨key, fun 𝔞 => chiId_mem _ _ key 𝔞⟩

end GlobalTheory.Mem.ChiVal

end
