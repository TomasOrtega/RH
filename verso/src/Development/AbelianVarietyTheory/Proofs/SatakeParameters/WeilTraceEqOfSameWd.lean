import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.LocalGlobalAboveL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TraceRMulPowEqZero
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.WdTrace

open Polynomial IsNilpotent

section Lin

variable {K n : Type*} [Field K] [CharZero K] [Fintype n] [DecidableEq n]

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.TraceExpSmul.trace_mul_exp_smul`. Consider the case `exact _root_.GlobalTheory.TraceExpSmul.trace_mul_exp_smul`. Consider the case `(apply _root_.GlobalTheory.TraceExpSmul.trace_mul_exp_smul <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.TraceExpSmul.trace_mul_exp_smul <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.TraceExpSmul.trace_mul_exp_smul <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.TraceExpSmul.trace_mul_exp_smul ..)`.
-/
theorem trace_mul_exp {R N : Matrix n n K} (hN : IsNilpotent N) {d : K}
    (hd : N * R = d • (R * N)) (s : K) : (R * exp (s • N)).trace = R.trace := by
  first
  | exact @_root_.GlobalTheory.TraceExpSmul.trace_mul_exp_smul
  | exact _root_.GlobalTheory.TraceExpSmul.trace_mul_exp_smul
  | (apply _root_.GlobalTheory.TraceExpSmul.trace_mul_exp_smul <;> assumption)
  | (intros; apply _root_.GlobalTheory.TraceExpSmul.trace_mul_exp_smul <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TraceExpSmul.trace_mul_exp_smul <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TraceExpSmul.trace_mul_exp_smul ..)

end Lin

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
variable {l : ℕ} [Fact l.Prime] {n : Type} [Fintype n] [DecidableEq n]

/- English proof (translation)
Use `set M : Matrix n n (Qbar l) := (r g).val * N * (r g)⁻¹.val with hM`. Establish `hM' : (r g).val * N = M * (r g).val` using `by rw [hM, Units.inv_mul_cancel_right]`. Establish `hMn : IsNilpotent M`. Take `⟨k, hk⟩` from `hN.1`. Conclude with `⟨k, by rw [hM, Units.conj_pow, hk, mul_zero, zero_mul]⟩`.

Take `⟨h1, U, hU, H⟩` from `hN`. Establish `hcm : ∀ a b : Ine (F` using `E) A, ineConj g⁻¹ (a * b) = ineConj g⁻¹ a * ineConj g⁻¹ b := fun a b => Subtype.ext (by simp [mul_assoc])`. Set `V : Subgroup (Ine (F` to `E) A) := { carrier := {σ | σ ∈ U ∧ ineConj g⁻¹ σ ∈ U} mul_mem' := fun {a b} ha hb => ⟨U.mul_mem ha.1 hb.1, by`. Rewrite using `[hcm]`. Conclude with `U.mul_mem ha.2 hb.2⟩`.

Use the proof step `one_mem' := ⟨U.one_mem, by`. Establish `: ineConj g⁻¹ (1 : Ine (F` using `E) A) = 1 := Subtype.ext (by simp)`. Rewrite using `[this]`. Conclude with `U.one_mem⟩`. Use the proof step `inv_mem' := fun {a} ha => ⟨U.inv_mem ha.1, by`.

Establish `: ineConj g⁻¹ a⁻¹ = (ineConj g⁻¹ a)⁻¹` using `Subtype.ext (by simp [mul_assoc])`. Rewrite using `[this]`. Conclude with `U.inv_mem ha.2⟩ }`. Establish `hV : IsOpen (V : Set (Ine (F` using `E) A)) := hU.inter (hU.preimage (continuous_ineConj g⁻¹))`. Take `⟨σ, hσ, h0⟩` from `ht.exists_tval_ne_zero hV`.

Use `set τ := ineConj g⁻¹ σ with hτ`. Establish `hpow : ∀ k : ℕ, ineConj g⁻¹ (σ ^ k) = τ ^ k`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => exact Subtype.ext (by simp)`.

Consider the case `succ k ih => rw [_root_.pow_succ, hcm, ih, _root_.pow_succ]`. Establish `hconj : ∀ k : ℕ, (((σ ^ k : Ine (F` using `E) A)) : G E Ω) = (g : G E Ω) * ((τ ^ k : Ine (F := E) A) : G E Ω) * (g : G E Ω)⁻¹ := by`. Introduce `k`. Rewrite using `[← hpow, coe_ineConj]`. Simplify using `[mul_assoc]`.

Establish `key : ∀ k : ℕ, exp (((k : Qbar l) * tval t σ) • N) = exp (((k : Qbar l) * tval t σ) • ((tval t τ / tval t σ) • M))`. Introduce `k`. Establish `e1 : (r ((σ ^ k : Ine (F` using `E) A) : G E Ω) : Matrix n n (Qbar l)) = exp (tval t (τ ^ k) • M) := by`. Rewrite using `[hconj, map_mul, map_mul, Units.val_mul, Units.val_mul, H _ (pow_mem hσ.2 k), semiconj_exp (h1.smul (tval t (τ ^ k))) (hMn.smul (tval t (τ ^ k))) (by rw [Matrix.mul_smul, Matrix.smul_mul, hM']), map_inv, mul_assoc, Units.mul_inv, mul_one]`. Establish `e2` using `H _ (pow_mem hσ.1 k)`.

Rewrite `e2` using `[e1, tval_pow, tval_pow]`. Establish `hs : (k : Qbar l) * tval t σ * (tval t τ / tval t σ) = k * tval t τ`. Clear the denominators using the available nonvanishing facts. Rewrite using `[smul_smul, hs]`. Conclude with `e2.symm`.

Establish `hNM : N = (tval t τ / tval t σ) • M` using `eq_of_exp_smul_eq h1 (hMn.smul _) h0 key`. Use `⟨tval t τ / tval t σ, ?_⟩` and prove the remaining obligations. Use `conv_lhs => rw [hNM]`. Rewrite using `[Matrix.smul_mul, ← hM']`.
-/
theorem exists_mul_eq_smul {t : Ine (F := E) A →* Multiplicative ℤ_[l]} (ht : IsTameChar t)
    {r : G E Ω →* GL n (Qbar l)} {N : Matrix n n (Qbar l)} (hN : IsMonodromy t r N)
    (g : Weil h) : ∃ d : Qbar l,
      N * (r (g : G E Ω) : Matrix n n (Qbar l)) = d • ((r (g : G E Ω) : Matrix n n (Qbar l)) * N) := by
  set M : Matrix n n (Qbar l) := (r g).val * N * (r g)⁻¹.val with hM
  have hM' : (r g).val * N = M * (r g).val := by rw [hM, Units.inv_mul_cancel_right]
  have hMn : IsNilpotent M := by
    obtain ⟨k, hk⟩ := hN.1
    exact ⟨k, by rw [hM, Units.conj_pow, hk, mul_zero, zero_mul]⟩
  obtain ⟨h1, U, hU, H⟩ := hN
  have hcm : ∀ a b : Ine (F := E) A, ineConj g⁻¹ (a * b) = ineConj g⁻¹ a * ineConj g⁻¹ b :=
    fun a b => Subtype.ext (by simp [mul_assoc])
  let V : Subgroup (Ine (F := E) A) :=
    { carrier := {σ | σ ∈ U ∧ ineConj g⁻¹ σ ∈ U}
      mul_mem' := fun {a b} ha hb => ⟨U.mul_mem ha.1 hb.1, by
        rw [hcm]; exact U.mul_mem ha.2 hb.2⟩
      one_mem' := ⟨U.one_mem, by
        have : ineConj g⁻¹ (1 : Ine (F := E) A) = 1 := Subtype.ext (by simp)
        rw [this]; exact U.one_mem⟩
      inv_mem' := fun {a} ha => ⟨U.inv_mem ha.1, by
        have : ineConj g⁻¹ a⁻¹ = (ineConj g⁻¹ a)⁻¹ := Subtype.ext (by simp [mul_assoc])
        rw [this]; exact U.inv_mem ha.2⟩ }
  have hV : IsOpen (V : Set (Ine (F := E) A)) := hU.inter (hU.preimage (continuous_ineConj g⁻¹))
  obtain ⟨σ, hσ, h0⟩ := ht.exists_tval_ne_zero hV
  set τ := ineConj g⁻¹ σ with hτ
  have hpow : ∀ k : ℕ, ineConj g⁻¹ (σ ^ k) = τ ^ k := by
    intro k
    induction k with
    | zero => exact Subtype.ext (by simp)
    | succ k ih => rw [_root_.pow_succ, hcm, ih, _root_.pow_succ]
  have hconj : ∀ k : ℕ, (((σ ^ k : Ine (F := E) A)) : G E Ω) =
      (g : G E Ω) * ((τ ^ k : Ine (F := E) A) : G E Ω) * (g : G E Ω)⁻¹ := by
    intro k
    rw [← hpow, coe_ineConj]
    simp [mul_assoc]
  have key : ∀ k : ℕ, exp (((k : Qbar l) * tval t σ) • N) =
      exp (((k : Qbar l) * tval t σ) • ((tval t τ / tval t σ) • M)) := by
    intro k
    have e1 : (r ((σ ^ k : Ine (F := E) A) : G E Ω) : Matrix n n (Qbar l)) =
        exp (tval t (τ ^ k) • M) := by
      rw [hconj, map_mul, map_mul, Units.val_mul, Units.val_mul, H _ (pow_mem hσ.2 k),
        semiconj_exp (h1.smul (tval t (τ ^ k))) (hMn.smul (tval t (τ ^ k)))
          (by rw [Matrix.mul_smul, Matrix.smul_mul, hM']), map_inv, mul_assoc, Units.mul_inv,
        mul_one]
    have e2 := H _ (pow_mem hσ.1 k)
    rw [e1, tval_pow, tval_pow] at e2
    have hs : (k : Qbar l) * tval t σ * (tval t τ / tval t σ) = k * tval t τ := by
      field_simp
    rw [smul_smul, hs]
    exact e2.symm
  have hNM : N = (tval t τ / tval t σ) • M := eq_of_exp_smul_eq h1 (hMn.smul _) h0 key
  refine ⟨tval t τ / tval t σ, ?_⟩
  conv_lhs => rw [hNM]
  rw [Matrix.smul_mul, ← hM']

/- English proof (translation)
Take `⟨d, hd⟩` from `exists_mul_eq_smul ht hN g`. Conclude with `trace_mul_exp hN.1 hd _`.
-/
theorem trace_wdMat {t : Ine (F := E) A →* Multiplicative ℤ_[l]} (ht : IsTameChar t)
    {r : G E Ω →* GL n (Qbar l)} {N : Matrix n n (Qbar l)} (hN : IsMonodromy t r N) {φ : Weil h}
    (hφ : deg φ = 1) (g : Weil h) :
    (wdMat t hφ r N g).trace = (r (g : G E Ω) : Matrix n n (Qbar l)).trace := by
  obtain ⟨d, hd⟩ := exists_mul_eq_smul ht hN g
  exact trace_mul_exp hN.1 hd _

/- English proof (translation)
Take `⟨t, ht, φ, hφ, N, b, hN, hb, rfl⟩` from `hx`. Conclude with `⟨wdMat t hφ r N g, by rw [WD.charPol_mk, hb.charpoly_eq, charpoly_toEndC], trace_wdMat ht hN hφ g⟩`.
-/
theorem exists_charPol_trace {ι : Qbar l ≃+* ℂ} {r : G E Ω →* GL n (Qbar l)} {x : WD h}
    (hx : IsWDOf ι r x) (g : Weil h) : ∃ M : Matrix n n (Qbar l),
      x.charPol g = M.charpoly.map ι.toRingHom ∧
        M.trace = (r (g : G E Ω) : Matrix n n (Qbar l)).trace := by
  obtain ⟨t, ht, φ, hφ, N, b, hN, hb, rfl⟩ := hx
  exact ⟨wdMat t hφ r N g, by rw [WD.charPol_mk, hb.charpoly_eq, charpoly_toEndC],
    trace_wdMat ht hN hφ g⟩

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ l _ ι a r r' w A h x hx hx' σ`. Take `⟨M, hM, hMt⟩` from `exists_charPol_trace hx σ`. Take `⟨M', hM', hMt'⟩` from `exists_charPol_trace hx' σ`. Rewrite using `[← hMt, ← hMt']`. Establish `hc : M.charpoly = M'.charpoly` using `Polynomial.map_injective _ ι.injective (hM.symm.trans hM')`.

Break down `isEmpty_or_nonempty (Fin a) with hE | hE` into its components or cases. Simplify using `[Matrix.trace]`. Rewrite using `[Matrix.trace_eq_neg_charpoly_coeff, Matrix.trace_eq_neg_charpoly_coeff, hc]`.
-/
theorem trace_eq_of_isWDOf : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (r r' : G E Ω →* GL (Fin a) (Qbar l)) (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (x : WD h), IsWDOf ι r x → IsWDOf ι r' x → ∀ σ : Weil h, (r (σ : G E Ω)).val.trace = (r' (σ : G E Ω)).val.trace := by
  intro E Ω _ _ _ _ _ l _ ι a r r' w A h x hx hx' σ
  obtain ⟨M, hM, hMt⟩ := exists_charPol_trace hx σ
  obtain ⟨M', hM', hMt'⟩ := exists_charPol_trace hx' σ
  rw [← hMt, ← hMt']
  have hc : M.charpoly = M'.charpoly := Polynomial.map_injective _ ι.injective (hM.symm.trans hM')
  rcases isEmpty_or_nonempty (Fin a) with hE | hE
  · simp [Matrix.trace]
  · rw [Matrix.trace_eq_neg_charpoly_coeff, Matrix.trace_eq_neg_charpoly_coeff, hc]

end GlobalTheory.WdTrace
