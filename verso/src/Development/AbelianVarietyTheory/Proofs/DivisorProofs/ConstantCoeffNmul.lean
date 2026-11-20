import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.QLogDefect

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q]

/- English proof (translation)
Introduce `α` and use `⟨0, N.zero_mem, by simp⟩`.
-/
theorem in_zero {σ : Type} (N : Ideal B) : In N (0 : MvPowerSeries σ Q) :=
  fun α => ⟨0, N.zero_mem, by simp⟩

/- English proof (translation)
Introduce `α` and use `by obtain ⟨a, ha, hfa⟩ := hf α obtain ⟨b, hb, hgb⟩ := hg α exact ⟨a - b, N.sub_mem ha hb, by rw [map_sub, hfa, hgb, map_sub]⟩`.
-/
theorem in_sub {σ : Type} {N : Ideal B} {f g : MvPowerSeries σ Q} (hf : In N f) (hg : In N g) :
    In N (f - g) := fun α => by
  obtain ⟨a, ha, hfa⟩ := hf α
  obtain ⟨b, hb, hgb⟩ := hg α
  exact ⟨a - b, N.sub_mem ha hb, by rw [map_sub, hfa, hgb, map_sub]⟩

/- English proof (translation)
Use `choose c hcN hc using hg`. Use `set G : MvPowerSeries σ B := fun α => c α with hG`. Establish `hgG : g = map (algebraMap B Q) G`. Use extensionality with `α`. Rewrite using `[coeff_map, hc α]`.

Both sides reduce to the same expression. Establish `hsu : HasSubst u` using `hasSubst_of_constantCoeff_zero hu`. Establish `key : subst (up Q u) g = map (algebraMap B Q) (subst u G)`. Rewrite using `[map_subst hsu, hgG]`. Both sides reduce to the same expression.

Introduce `e`. Use `⟨coeff e (subst u G), ?_, by rw [key, coeff_map]⟩` and prove the remaining obligations. Rewrite using `[coeff_subst hsu]`. Use `finsum_induction (fun x => x ∈ N) N.zero_mem (fun x y hx hy => N.add_mem hx hy) ?_` and prove the remaining obligations. Introduce `d`.

Rewrite using `[smul_eq_mul]`. Conclude with `N.mul_mem_right _ (hcN d)`.
-/
theorem in_subst {σ τ : Type} [Finite σ] {N : Ideal B} {g : MvPowerSeries σ Q}
    (u : σ → MvPowerSeries τ B) (hu : ∀ i, constantCoeff (u i) = 0) (hg : In N g) :
    In N (subst (up Q u) g) := by
  choose c hcN hc using hg
  set G : MvPowerSeries σ B := fun α => c α with hG
  have hgG : g = map (algebraMap B Q) G := by
    ext α; rw [coeff_map, hc α]; rfl
  have hsu : HasSubst u := hasSubst_of_constantCoeff_zero hu
  have key : subst (up Q u) g = map (algebraMap B Q) (subst u G) := by
    rw [map_subst hsu, hgG]; rfl
  intro e
  refine ⟨coeff e (subst u G), ?_, by rw [key, coeff_map]⟩
  rw [coeff_subst hsu]
  refine finsum_induction (fun x => x ∈ N) N.zero_mem (fun x y hx hy => N.add_mem hx hy) ?_
  intro d
  rw [smul_eq_mul]
  exact N.mul_mem_right _ (hcN d)

variable {d : ℕ}

/- English proof (translation)
Unfold `nmul`. Rewrite using `[Function.iterate_succ_apply']`.
-/
theorem nmul_succ {R : Type} [CommRing R] (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (n : ℕ) :
    nmul μ (n + 1) = op μ (nmul μ n) fun i => X i := by
  unfold nmul; rw [Function.iterate_succ_apply']

/- English proof (translation)
Proceed by induction on `n generalizing i with`. Consider the case `zero => simp [nmul]`. Consider the case `succ n ih`. Rewrite using `[nmul_succ]`. Establish `h0 : ∀ j, constantCoeff (Sum.elim (nmul μ n) (fun i => (X i : MvPowerSeries (Fin d) R)) j) = 0`.

Introduce and unpack `(j | j)`. Conclude with `ih j`. Simplify using the standard rewrite rules. Conclude with `constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero h0) h0 (hμ i)`.
-/
theorem constantCoeff_nmul {R : Type} [CommRing R] {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
    (hμ : ∀ i, constantCoeff (μ i) = 0) (n : ℕ) (i : Fin d) : constantCoeff (nmul μ n i) = 0 := by
  induction n generalizing i with
  | zero => simp [nmul]
  | succ n ih =>
    rw [nmul_succ]
    have h0 : ∀ j, constantCoeff (Sum.elim (nmul μ n) (fun i => (X i : MvPowerSeries (Fin d) R)) j) = 0 := by
      rintro (j | j)
      · exact ih j
      · simp
    exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero h0) h0 (hμ i)

/- English proof (translation)
Use function extensionality and compare the values at `i`. Establish `h0 : ∀ j, constantCoeff (Sum.elim (nmul μ n) (fun i => (X i : MvPowerSeries (Fin d) B)) j) = 0`. Introduce and unpack `(j | j)`. Conclude with `constantCoeff_nmul hμ n j`. Simplify using the standard rewrite rules.

Rewrite using `[nmul_succ]`. Simplify using `only [up, op, at2]`. Rewrite using `[map_subst (hasSubst_of_constantCoeff_zero h0)]`. Use `congr 1`. Use function extensionality and compare the values at `j`.

Break down `j with j | j` into its components or cases. Both sides reduce to the same expression. Simplify using the standard rewrite rules.
-/
theorem up_nmul_succ (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B)
    (hμ : ∀ i, constantCoeff (μ i) = 0) (n : ℕ) :
    up Q (nmul μ (n + 1)) = op (up Q μ) (up Q (nmul μ n)) fun i => X i := by
  funext i
  have h0 : ∀ j, constantCoeff (Sum.elim (nmul μ n) (fun i => (X i : MvPowerSeries (Fin d) B)) j) = 0 := by
    rintro (j | j)
    · exact constantCoeff_nmul hμ n j
    · simp
  rw [nmul_succ]
  simp only [up, op, at2]
  rw [map_subst (hasSubst_of_constantCoeff_zero h0)]
  congr 1
  funext j
  rcases j with j | j
  · rfl
  · simp

/- English proof (translation)
Establish `hU : ∀ j, constantCoeff (up Q (nmul μ n) j) = 0`. Introduce `j`. Simplify using `only [up]`. Rewrite using `[← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, constantCoeff_nmul hμ n j, map_zero]`. Establish `hE : ∀ j, constantCoeff (Sum.elim (up Q (nmul μ n)) (fun i => (X i : MvPowerSeries (Fin d) Q)) j) = 0`.

Introduce and unpack `(j | j)`. Conclude with `hU j`. Simplify using the standard rewrite rules. Establish `hM : ∀ j, constantCoeff (up Q μ j) = 0`. Introduce `j`.

Simplify using `only [up]`. Rewrite using `[← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, hμ j, map_zero]`. Establish `hsE` using `hasSubst_of_constantCoeff_zero hE`. Establish `hsM` using `hasSubst_of_constantCoeff_zero hM`. Establish `hsL : HasSubst (fun i => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) Q))` using `hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _`.

Establish `hsR : HasSubst (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) Q))` using `hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _`. Establish `e1 : subst (Sum.elim (up Q (nmul μ n)) fun i => (X i : MvPowerSeries (Fin d) Q)) (subst (up Q μ) f) = subst (up Q (nmul μ (n + 1))) f`. Rewrite using `[subst_comp_subst_apply hsM hsE, up_nmul_succ μ hμ n]`. Both sides reduce to the same expression. Establish `e2 : subst (Sum.elim (up Q (nmul μ n)) fun i => (X i : MvPowerSeries (Fin d) Q)) (inL f) = subst (up Q (nmul μ n)) f`.

Unfold `inL`. Rewrite using `[subst_comp_subst_apply hsL hsE]`. Use `congr 1`. Use function extensionality and compare the values at `j`. Rewrite using `[subst_X hsE]`.

Both sides reduce to the same expression. Establish `e3 : subst (Sum.elim (up Q (nmul μ n)) fun i => (X i : MvPowerSeries (Fin d) Q)) (inR f) = f`. Unfold `inR`. Rewrite using `[subst_comp_subst_apply hsR hsE]`. Establish `: (fun j => subst (Sum.elim (up Q (nmul μ n)) fun i => (X i : MvPowerSeries (Fin d) Q)) (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) Q)) = fun j => X j`.

Use function extensionality and compare the values at `j`. Rewrite using `[subst_X hsE]`. Both sides reduce to the same expression. Rewrite using `[this, subst_self]`. Both sides reduce to the same expression.

Establish `hc : subst (Sum.elim (up Q (nmul μ n)) fun i => (X i : MvPowerSeries (Fin d) Q)) (cob1 (up Q μ) f) = subst (up Q (nmul μ (n + 1))) f - subst (up Q (nmul μ n)) f - f`. Unfold `cob1`. Rewrite using `[← coe_substAlgHom hsE, map_sub, map_sub, coe_substAlgHom, e1, e2, e3]`. Rewrite using `[hc]`. Unfold `defect`.

Use `push_cast`. Rewrite using `[add_smul, one_smul]`. Normalize the expressions using the abelian group laws.
-/
theorem defect_succ (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B)
    (hμ : ∀ i, constantCoeff (μ i) = 0) (n : ℕ) (f : MvPowerSeries (Fin d) Q) :
    defect μ (n + 1) f = defect μ n f -
      subst (Sum.elim (up Q (nmul μ n)) fun i => (X i : MvPowerSeries (Fin d) Q)) (cob1 (up Q μ) f) := by
  have hU : ∀ j, constantCoeff (up Q (nmul μ n) j) = 0 := by
    intro j
    simp only [up]
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      constantCoeff_nmul hμ n j, map_zero]
  have hE : ∀ j, constantCoeff (Sum.elim (up Q (nmul μ n)) (fun i => (X i : MvPowerSeries (Fin d) Q)) j) = 0 := by
    rintro (j | j)
    · exact hU j
    · simp
  have hM : ∀ j, constantCoeff (up Q μ j) = 0 := by
    intro j
    simp only [up]
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, hμ j, map_zero]
  have hsE := hasSubst_of_constantCoeff_zero hE
  have hsM := hasSubst_of_constantCoeff_zero hM
  have hsL : HasSubst (fun i => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) Q)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have hsR : HasSubst (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) Q)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have e1 : subst (Sum.elim (up Q (nmul μ n)) fun i => (X i : MvPowerSeries (Fin d) Q)) (subst (up Q μ) f)
      = subst (up Q (nmul μ (n + 1))) f := by
    rw [subst_comp_subst_apply hsM hsE, up_nmul_succ μ hμ n]; rfl
  have e2 : subst (Sum.elim (up Q (nmul μ n)) fun i => (X i : MvPowerSeries (Fin d) Q)) (inL f)
      = subst (up Q (nmul μ n)) f := by
    unfold inL
    rw [subst_comp_subst_apply hsL hsE]
    congr 1; funext j; rw [subst_X hsE]; rfl
  have e3 : subst (Sum.elim (up Q (nmul μ n)) fun i => (X i : MvPowerSeries (Fin d) Q)) (inR f) = f := by
    unfold inR
    rw [subst_comp_subst_apply hsR hsE]
    have : (fun j => subst (Sum.elim (up Q (nmul μ n)) fun i => (X i : MvPowerSeries (Fin d) Q))
        (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) Q)) = fun j => X j := by
      funext j; rw [subst_X hsE]; rfl
    rw [this, subst_self]; rfl
  have hc : subst (Sum.elim (up Q (nmul μ n)) fun i => (X i : MvPowerSeries (Fin d) Q)) (cob1 (up Q μ) f)
      = subst (up Q (nmul μ (n + 1))) f - subst (up Q (nmul μ n)) f - f := by
    unfold cob1
    rw [← coe_substAlgHom hsE, map_sub, map_sub, coe_substAlgHom, e1, e2, e3]
  rw [hc]
  unfold defect
  push_cast
  rw [add_smul, one_smul]
  abel

/- English proof (translation)
Introduce `p _ B O Q _ _ _ _ θ _ d μ hμ N f hf n`. Use `⟨?_, constantCoeff_nmul hμ.const n⟩` and prove the remaining obligations. Proceed by induction on `n with`. Consider the case `zero`. Establish `h0 : up Q (nmul μ 0) = 0` using `by funext i; simp [up, nmul]`.

Simplify using `only [defect, h0, Nat.cast_zero, zero_smul, zero_sub]`. Rewrite using `[subst_zero_of_constantCoeff_zero hf.1, neg_zero]`. Conclude with `in_zero N`. Consider the case `succ n ih`. Rewrite using `[defect_succ μ hμ.const n f]`.

Use `in_sub ih ?_` and prove the remaining obligations. Establish `hv : ∀ j, constantCoeff (Sum.elim (nmul μ n) (fun i => (X i : MvPowerSeries (Fin d) B)) j) = 0`. Introduce and unpack `(j | j)`. Conclude with `constantCoeff_nmul hμ.const n j`. Simplify using the standard rewrite rules.

Establish `: (Sum.elim (up Q (nmul μ n)) fun i => (X i : MvPowerSeries (Fin d) Q)) = up Q (Sum.elim (nmul μ n) fun i => (X i : MvPowerSeries (Fin d) B))`. Use function extensionality and compare the values at `j`. Break down `j with j | j` into its components or cases. Both sides reduce to the same expression. Simplify using `[up]`.

Rewrite using `[this]`. Conclude with `in_subst _ hv hf.2.2`.
-/
theorem main : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (N : Ideal B) (f : MvPowerSeries (Fin d) Q), QL μ N f → ∀ n, In N (defect μ n f) ∧ ∀ i, constantCoeff (nmul μ n i) = 0 := by
  intro p _ B O Q _ _ _ _ θ _ d μ hμ N f hf n
  refine ⟨?_, constantCoeff_nmul hμ.const n⟩
  induction n with
  | zero =>
    have h0 : up Q (nmul μ 0) = 0 := by funext i; simp [up, nmul]
    simp only [defect, h0, Nat.cast_zero, zero_smul, zero_sub]
    rw [subst_zero_of_constantCoeff_zero hf.1, neg_zero]
    exact in_zero N
  | succ n ih =>
    rw [defect_succ μ hμ.const n f]
    refine in_sub ih ?_
    have hv : ∀ j, constantCoeff (Sum.elim (nmul μ n) (fun i => (X i : MvPowerSeries (Fin d) B)) j) = 0 := by
      rintro (j | j)
      · exact constantCoeff_nmul hμ.const n j
      · simp
    have : (Sum.elim (up Q (nmul μ n)) fun i => (X i : MvPowerSeries (Fin d) Q)) =
        up Q (Sum.elim (nmul μ n) fun i => (X i : MvPowerSeries (Fin d) B)) := by
      funext j; rcases j with j | j
      · rfl
      · simp [up]
    rw [this]
    exact in_subst _ hv hf.2.2

end GlobalTheory.QLogDefect
