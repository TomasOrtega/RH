import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.HermitianBasisBelowSecond

noncomputable section

namespace PI.OmLocU.SdB

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU PI.VolStabSW
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

/- English proof (translation)
Establish `h` using `oEv_basis (E := E) v`. Rewrite `h` using `[hfin]`. Conclude with `h`.
-/
theorem oEv_basis2 (hfin : Module.finrank F E = 2) : ∃ β : Fin 2 → Fv F v ⊗[F] E, LinearIndependent (Fv F v) β ∧
    ∀ x, x ∈ OEv (E := E) v ↔ ∃ c : Fin 2 → v.adicCompletionIntegers F, x = ∑ i, (c i : Fv F v) • β i := by
  have h := oEv_basis (E := E) v
  rw [hfin] at h
  exact h

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => rw [smul_zero, map_zero, smul_zero]`. Consider the case `tmul a b => simp [sigR, TensorProduct.smul_tmul']`. Consider the case `add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]`.
-/
theorem sigR_smulF (c : Fv F v) (x : Fv F v ⊗[F] E) : sigR (Fv F v) σ (c • x) = c • sigR (Fv F v) σ x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul a b => simp [sigR, TensorProduct.smul_tmul']
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

/- English proof (translation)
Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `c hc p`. Establish `hent : ∀ i j, ((∑ p, c p • hb σ v hinv β p : HermR (Fv F v) σ a) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j = 0`. Introduce `i j`. Rewrite using `[hc]`.

Both sides reduce to the same expression. Establish `hβ2` using `Fintype.linearIndependent_iff.1 hβ`. Take `⟨i, j⟩` from `p`. Break down `lt_trichotomy i j with h | rfl | h` into its components or cases. Establish `h1` using `hent i j`.

Rewrite `h1` using `[sum_lt σ v hinv β c h]`. Establish `h0` using `hβ2 ![c (i, j), c (j, i)] (by simpa [Fin.sum_univ_two] using h1)`. Simplify using `using h0 0`. Establish `h1` using `hent i i`. Rewrite `h1` using `[sum_diag σ v hinv β c i, b_sc_eq]`.

Conclude with `(map_eq_zero_iff _ (algebraMap (Fv F v) (Fv F v ⊗[F] E)).injective).1 h1`. Establish `h1` using `hent j i`. Rewrite `h1` using `[sum_lt σ v hinv β c h]`. Establish `h0` using `hβ2 ![c (j, i), c (i, j)] (by simpa [Fin.sum_univ_two] using h1)`. Simplify using `using h0 1`.
-/
theorem hb_li {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (β : Fin 2 → Fv F v ⊗[F] E) (hβ : LinearIndependent (Fv F v) β) :
    LinearIndependent (Fv F v) (hb σ v hinv β (a := a)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc p
  have hent : ∀ i j, ((∑ p, c p • hb σ v hinv β p : HermR (Fv F v) σ a) :
      Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j = 0 := by
    intro i j
    rw [hc]
    rfl
  have hβ2 := Fintype.linearIndependent_iff.1 hβ
  obtain ⟨i, j⟩ := p
  rcases lt_trichotomy i j with h | rfl | h
  · have h1 := hent i j
    rw [sum_lt σ v hinv β c h] at h1
    have h0 := hβ2 ![c (i, j), c (j, i)] (by simpa [Fin.sum_univ_two] using h1)
    simpa using h0 0
  · have h1 := hent i i
    rw [sum_diag σ v hinv β c i, b_sc_eq] at h1
    exact (map_eq_zero_iff _ (algebraMap (Fv F v) (Fv F v ⊗[F] E)).injective).1 h1
  · have h1 := hent j i
    rw [sum_lt σ v hinv β c h] at h1
    have h0 := hβ2 ![c (j, i), c (i, j)] (by simpa [Fin.sum_univ_two] using h1)
    simpa using h0 1

/- English proof (translation)
Establish `hinv` using `b_sig_sig σ hcm`. Establish `hnt` using `b_sig_nt σ hcm`. Establish `hfin` using `hcm.2.2.1`. Use `set r : Fv F v := algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) t with hr`. Establish `hsc : sc (E` using `E) v r = t := by`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[b_sc_eq, hr, map_mul, trace_v v σ hinv hnt hfin, hf]`. Use `_ = algebraMap (Fv F v) (Fv F v ⊗[F] E) (algebraMap F (Fv F v) (1 / 2) * 2) * t := by`. Rewrite using `[map_mul, map_ofNat, mul_assoc, two_mul]`. Use `_ = t := by rw [half_two, map_one, one_mul]`.

Use `⟨r, b_int_of_sc v (hsc ▸ ht), hsc.symm⟩` and prove the remaining obligations.
-/
theorem fix_int' (hcm : IsCMExt F E σ) {t : Fv F v ⊗[F] E} (ht : t ∈ OEv (E := E) v)
    (hf : sigR (Fv F v) σ t = t) : ∃ r ∈ v.adicCompletionIntegers F, t = sc (E := E) v r := by
  have hinv := b_sig_sig σ hcm
  have hnt := b_sig_nt σ hcm
  have hfin := hcm.2.2.1
  set r : Fv F v := algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) t with hr
  have hsc : sc (E := E) v r = t := by
    calc sc (E := E) v r
        = algebraMap (Fv F v) (Fv F v ⊗[F] E) (algebraMap F (Fv F v) (1 / 2)) * (t + t) := by
          rw [b_sc_eq, hr, map_mul, trace_v v σ hinv hnt hfin, hf]
      _ = algebraMap (Fv F v) (Fv F v ⊗[F] E) (algebraMap F (Fv F v) (1 / 2) * 2) * t := by
          rw [map_mul, map_ofNat, mul_assoc, two_mul]
      _ = t := by rw [half_two, map_one, one_mul]
  refine ⟨r, b_int_of_sc v (hsc ▸ ht), hsc.symm⟩

/- English proof (translation)
Establish `hinv` using `b_sig_sig σ hcm`. Prove the components needed by the constructor for the conclusion. Introduce `hT`. Establish `hT' : ∀ i j, (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j ∈ OEv (E` using `E) v := hT`. Establish `hH : ∀ i j, sigR (Fv F v) σ ((T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) j i) = (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j` using `fun i j => T.2 i j`.

Use `choose d hd using fun i j => (hβ _).1 (hT' i j)`. Use `choose r hr hrT using fun i => fix_int' σ v hcm (hT' i i) (hH i i)`. Use `⟨fun p => if p.1 < p.2 then d p.1 p.2 0 else if p.2 < p.1 then d p.2 p.1 1 else ⟨r p.1, hr p.1⟩, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Use extensionality with `i j`.

Break down `lt_trichotomy i j with h | rfl | h` into its components or cases. Rewrite using `[sum_lt σ v hinv β _ h, hd i j, Fin.sum_univ_two]`. Simplify using `[h, not_lt.2 h.le]`. Rewrite using `[sum_diag σ v hinv β _ i, hrT i]`. Simplify using the standard rewrite rules.

Rewrite using `[sum_gt σ v hinv β _ h, ← hH i j, hd j i, Fin.sum_univ_two, map_add, sigR_smulF, sigR_smulF, add_comm]`. Simplify using `[h, not_lt.2 h.le]`. Introduce and unpack `⟨c, rfl⟩`. Introduce `i j`. Break down `lt_trichotomy i j with h | rfl | h` into its components or cases.

Rewrite using `[sum_lt σ v hinv β _ h]`. Conclude with `(hβ _).2 ⟨![c (i, j), c (j, i)], by simp [Fin.sum_univ_two]⟩`. Rewrite using `[sum_diag σ v hinv β _ i]`. Conclude with `b_sc_mem v (c (i, i)).2`. Rewrite using `[sum_gt σ v hinv β _ h]`.

Establish `hm` using `b_sigR_mem v σ ((hβ ((c (j, i) : Fv F v) • β 0 + (c (i, j) : Fv F v) • β 1)).2 ⟨![c (j, i), c (i, j)], by simp [Fin.sum_univ_two]⟩)`. Rewrite `hm` using `[map_add, sigR_smulF, sigR_smulF, add_comm]`. Then use the resulting hypothesis.
-/
theorem hb_mem {a : ℕ} (hcm : IsCMExt F E σ) (β : Fin 2 → Fv F v ⊗[F] E)
    (hβ : ∀ x, x ∈ OEv (E := E) v ↔ ∃ c : Fin 2 → v.adicCompletionIntegers F, x = ∑ i, (c i : Fv F v) • β i)
    (T : HermR (Fv F v) σ a) :
    T ∈ HO σ v a ↔ ∃ c : Fin a × Fin a → v.adicCompletionIntegers F,
      T = ∑ p, (c p : Fv F v) • hb σ v (b_sig_sig σ hcm) β p := by
  have hinv := b_sig_sig σ hcm
  constructor
  · intro hT
    have hT' : ∀ i j, (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j ∈ OEv (E := E) v := hT
    have hH : ∀ i j, sigR (Fv F v) σ ((T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) j i) =
        (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j := fun i j => T.2 i j
    choose d hd using fun i j => (hβ _).1 (hT' i j)
    choose r hr hrT using fun i => fix_int' σ v hcm (hT' i i) (hH i i)
    refine ⟨fun p => if p.1 < p.2 then d p.1 p.2 0 else if p.2 < p.1 then d p.2 p.1 1 else ⟨r p.1, hr p.1⟩, ?_⟩
    apply Subtype.ext
    ext i j
    rcases lt_trichotomy i j with h | rfl | h
    · rw [sum_lt σ v hinv β _ h, hd i j, Fin.sum_univ_two]
      simp [h, not_lt.2 h.le]
    · rw [sum_diag σ v hinv β _ i, hrT i]
      simp
    · rw [sum_gt σ v hinv β _ h, ← hH i j, hd j i, Fin.sum_univ_two, map_add, sigR_smulF, sigR_smulF, add_comm]
      simp [h, not_lt.2 h.le]
  · rintro ⟨c, rfl⟩
    intro i j
    rcases lt_trichotomy i j with h | rfl | h
    · rw [sum_lt σ v hinv β _ h]
      exact (hβ _).2 ⟨![c (i, j), c (j, i)], by simp [Fin.sum_univ_two]⟩
    · rw [sum_diag σ v hinv β _ i]
      exact b_sc_mem v (c (i, i)).2
    · rw [sum_gt σ v hinv β _ h]
      have hm := b_sigR_mem v σ ((hβ ((c (j, i) : Fv F v) • β 0 + (c (i, j) : Fv F v) • β 1)).2
        ⟨![c (j, i), c (i, j)], by simp [Fin.sum_univ_two]⟩)
      rwa [map_add, sigR_smulF, sigR_smulF, add_comm] at hm

/- English proof (translation)
Introduce `_ ϖ hϖ`. Establish `hcm` using `hS.1`. Take `⟨β, hli, hβ⟩` from `oEv_basis2 v hcm.2.2.1`. Rewrite using `[genIdx v (HO σ v a) (hb σ v (b_sig_sig σ hcm) β) (hb_li σ v (b_sig_sig σ hcm) β hli) (hb_mem σ v hcm β hβ) ϖ hϖ, qv, Fintype.card_prod, Fintype.card_fin]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem idxPiH_std (a : ℕ) (hS : StdHyp σ J ψ) : IdxPiH σ v a := by
  intro _ ϖ hϖ
  have hcm := hS.1
  obtain ⟨β, hli, hβ⟩ := oEv_basis2 v hcm.2.2.1
  rw [genIdx v (HO σ v a) (hb σ v (b_sig_sig σ hcm) β) (hb_li σ v (b_sig_sig σ hcm) β hli)
    (hb_mem σ v hcm β hβ) ϖ hϖ, qv, Fintype.card_prod, Fintype.card_fin]
  push_cast
  ring

end PI.OmLocU.SdB
