import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.FibPOfDual

noncomputable section

namespace PI.OmVd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory PI.OmLocU
  Topology Filter
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

/- English proof (translation)
Take `⟨h0, hπ, hint⟩` from `unif_spec v ϖ hϖ`. Establish `hev : ∀ i, ∀ᶠ k in atTop, ϖ ^ k • d i ∈ OEv (E` using `E) v := by`. Introduce `i`. Establish `ht : Tendsto (fun k : ℕ => ϖ ^ k • d i) atTop (𝓝 0)`. Use `hπ.smul_const (d i)` as an intermediate fact.

Simplify using `using this`. Conclude with `ht ((isOpen_oEv (E := E) v).mem_nhds (oEv_zero v))`. Take `⟨N, hN⟩` from `(Filter.eventually_all.2 hev).exists`. Establish `key : ∀ m : ℕ, (∀ i, sc (E` using `E) v (ϖ ^ m) * d i ∈ OEv (E := E) v) → ∀ i, d i ∈ OEv (E := E) v := by`. Introduce `m`.

Proceed by induction on `m with`. Consider the case `zero`. Introduce `h i`. Simplify `h i` using `[sc_one]`. Consider the case `succ m ih`.

Introduce `h`. Apply `ih` to reduce the goal to its premises. Introduce `i`. Establish `hS : ∑ j, A i j * (sc (E` using `E) v (ϖ ^ (m + 1)) * d j) = sc (E := E) v (ϖ ^ m) * sc (E := E) v ϖ * ∑ j, A i j * d j := by`. Rewrite using `[Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[pow_succ, ← sc_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `e : sc (E` using `E) v (ϖ ^ m) * d i = sc (E := E) v (ϖ ^ m) * (d i + sc (E := E) v ϖ * ∑ j, A i j * d j) - ∑ j, A i j * (sc (E := E) v (ϖ ^ (m + 1)) * d j) := by`. Rewrite using `[hS]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, sub_eq_add_neg]`. Conclude with `oEv_add v (sc_mul_mem_oEv v (pow_mem hint m) (hu i)) (oEv_neg v (oEv_sum v _ _ fun j _ => oEv_mul v (hA i j) (h j)))`. Conclude with `key N fun i => by rw [← smul_eq_sc]; exact hN i`.
-/
theorem near_int {a : ℕ} (ϖ : Fv F v) (hϖ : IsUnif v ϖ) (A : Fin a → Fin a → Fv F v ⊗[F] E)
    (hA : ∀ i j, A i j ∈ OEv (E := E) v) (d : Fin a → Fv F v ⊗[F] E)
    (hu : ∀ i, d i + sc (E := E) v ϖ * ∑ j, A i j * d j ∈ OEv (E := E) v) : ∀ i, d i ∈ OEv (E := E) v := by
  obtain ⟨h0, hπ, hint⟩ := unif_spec v ϖ hϖ
  have hev : ∀ i, ∀ᶠ k in atTop, ϖ ^ k • d i ∈ OEv (E := E) v := by
    intro i
    have ht : Tendsto (fun k : ℕ => ϖ ^ k • d i) atTop (𝓝 0) := by
      have := hπ.smul_const (d i)
      simpa using this
    exact ht ((isOpen_oEv (E := E) v).mem_nhds (oEv_zero v))
  obtain ⟨N, hN⟩ := (Filter.eventually_all.2 hev).exists
  have key : ∀ m : ℕ, (∀ i, sc (E := E) v (ϖ ^ m) * d i ∈ OEv (E := E) v) → ∀ i, d i ∈ OEv (E := E) v := by
    intro m
    induction m with
    | zero =>
      intro h i
      simpa [sc_one] using h i
    | succ m ih =>
      intro h
      apply ih
      intro i
      have hS : ∑ j, A i j * (sc (E := E) v (ϖ ^ (m + 1)) * d j) =
          sc (E := E) v (ϖ ^ m) * sc (E := E) v ϖ * ∑ j, A i j * d j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [pow_succ, ← sc_mul]
        ring
      have e : sc (E := E) v (ϖ ^ m) * d i = sc (E := E) v (ϖ ^ m) * (d i + sc (E := E) v ϖ * ∑ j, A i j * d j) -
          ∑ j, A i j * (sc (E := E) v (ϖ ^ (m + 1)) * d j) := by
        rw [hS]
        ring
      rw [e, sub_eq_add_neg]
      exact oEv_add v (sc_mul_mem_oEv v (pow_mem hint m) (hu i))
        (oEv_neg v (oEv_sum v _ _ fun j _ => oEv_mul v (hA i j) (h j)))
  exact key N fun i => by rw [← smul_eq_sc]; exact hN i

/- English proof (translation)
Introduce `hS hL hSD hUn ϖ hϖ X hX Z hZ`. Take `⟨h0, -, hint⟩` from `unif_spec v ϖ hϖ`. Take `⟨P, hP, rfl⟩` from `(PI.VolStabSW.mem_smulSub _ _ _).1 hZ`. Take `⟨W, hW, hd⟩` from `hD hS hSD hUn hL X hX`. Establish `hPs : ϖ ^ (0 + 1) • P ∈ lamS v Λ a` using `lamS_smul v Λ (pow_mem hint _) hP`.

Use `⟨fun i => (latLoc (E := E) v Λ).add_mem (hX.1 i) (hPs i), fun c hc => ?_⟩` and prove the remaining obligations. Establish `hsm : ∀ j i, hR (Fv F v) σ J (W j) ((ϖ ^ (0 + 1) • P) i) = sc (E` using `E) v ϖ * hR (Fv F v) σ J (W j) (P i) := by`. Introduce `j i`. Use `hR_smul_smul σ J v 1 (ϖ ^ (0 + 1)) (W j) (P i)` as an intermediate fact. Rewrite `this` using `[one_smul, one_mul, zero_add, pow_one]`.

Rewrite using `[zero_add, pow_one]`. Conclude with `this`. Establish `hpair : ∀ j, hR (Fv F v) σ J (W j) (∑ i, c i • (X + ϖ ^ (0 + 1) • P) i) = c j + sc (E` using `E) v ϖ * ∑ i, hR (Fv F v) σ J (W j) (P i) * c i := by`. Introduce `j`. Rewrite using `[hR_sum_smul_right]`.

Establish `h1 : ∀ i, c i * hR (Fv F v) σ J (W j) ((X + ϖ ^ (0 + 1) • P) i) = c i * (if i = j then 1 else 0) + sc (E` using `E) v ϖ * (hR (Fv F v) σ J (W j) (P i) * c i) := by`. Introduce `i`. Rewrite using `[Pi.add_apply, hR_add_right, (hd i j).2, hsm j i]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_add_distrib, ← Finset.mul_sum]`.

Simplify using `[mul_ite]`. Conclude with `near_int v ϖ hϖ (fun j i => hR (Fv F v) σ J (W j) (P i)) (fun j i => hR_mem_oEv σ J v Λ hSD (hW j) (hP i)) c (fun j => by rw [← hpair j]; exact hR_mem_oEv σ J v Λ hSD (hW j) hc)`.
-/
theorem primCos_of (a : ℕ) (hD : PrimDual σ J ψ v Λ a) : PrimCos σ J ψ v Λ a := by
  intro hS hL hSD hUn ϖ hϖ X hX Z hZ
  obtain ⟨h0, -, hint⟩ := unif_spec v ϖ hϖ
  obtain ⟨P, hP, rfl⟩ := (PI.VolStabSW.mem_smulSub _ _ _).1 hZ
  obtain ⟨W, hW, hd⟩ := hD hS hSD hUn hL X hX
  have hPs : ϖ ^ (0 + 1) • P ∈ lamS v Λ a := lamS_smul v Λ (pow_mem hint _) hP
  refine ⟨fun i => (latLoc (E := E) v Λ).add_mem (hX.1 i) (hPs i), fun c hc => ?_⟩
  have hsm : ∀ j i, hR (Fv F v) σ J (W j) ((ϖ ^ (0 + 1) • P) i) = sc (E := E) v ϖ * hR (Fv F v) σ J (W j) (P i) := by
    intro j i
    have := hR_smul_smul σ J v 1 (ϖ ^ (0 + 1)) (W j) (P i)
    rw [one_smul, one_mul, zero_add, pow_one] at this
    rw [zero_add, pow_one]
    exact this
  have hpair : ∀ j, hR (Fv F v) σ J (W j) (∑ i, c i • (X + ϖ ^ (0 + 1) • P) i) =
      c j + sc (E := E) v ϖ * ∑ i, hR (Fv F v) σ J (W j) (P i) * c i := by
    intro j
    rw [hR_sum_smul_right]
    have h1 : ∀ i, c i * hR (Fv F v) σ J (W j) ((X + ϖ ^ (0 + 1) • P) i) =
        c i * (if i = j then 1 else 0) + sc (E := E) v ϖ * (hR (Fv F v) σ J (W j) (P i) * c i) := by
      intro i
      rw [Pi.add_apply, hR_add_right, (hd i j).2, hsm j i]
      ring
    rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_add_distrib, ← Finset.mul_sum]
    simp [mul_ite]
  exact near_int v ϖ hϖ (fun j i => hR (Fv F v) σ J (W j) (P i))
    (fun j i => hR_mem_oEv σ J v Λ hSD (hW j) (hP i)) c
    (fun j => by rw [← hpair j]; exact hR_mem_oEv σ J v Λ hSD (hW j) hc)

end PI.OmVd
