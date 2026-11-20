import Mathlib
import Formalism.LocalToGlobal.Columns.KOneCharacterTrivialNearOne
import Formalism.LocalToGlobal.Columns.ChainInstY
import Formalism.LocalToGlobal.Columns.XtSumSingle
import Formalism.LocalToGlobal.Columns.LastRowColLevSym
import Formalism.LocalToGlobal.Columns.ChainTopLawB
import Formalism.LocalToGlobal.Columns.ChainLawPhiTop
import Formalism.LocalToGlobal.Columns.ChainTopLawTw
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.TopLawQ

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker NumberField IsDedekindDomain Classical

noncomputable section

namespace GlobalTheory

open Module Matrix

section FtY

variable {X : Fields} {Pr : Primes X} {R : Ranks}

/- English proof (translation)
Establish `hqn` using `intAt_qpow3 (X := X) w.1`. Establish `hq1 : (qOf w.1 : X.E) ≠ 0` using `by exact_mod_cast (qOf_pos w.1).ne'`. Establish `hq0 : (qOf w.1 : X.E) ^ cst.M ≠ 0` using `pow_ne_zero _ hq1`. Establish `hδM : ∀ i : Fin n, IntAt w.1 ((qOf w.1 : X.E) ^ cst.M * δ (Pi.single i 1))` using `fun i => by`. Establish `e : (qOf w.1 : X.E) ^ cst.M * δ (Pi.single i 1) = (qOf w.1 : X.E) ^ (2 * cst.M) * ((((qOf w.1 : X.E) ^ cst.M)⁻¹) * δ (Pi.single i 1))`.

Rewrite using `[show 2 * cst.M = cst.M + cst.M by ring, pow_add]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`. Conclude with `(hqn _).mul (hδ i)`. Establish `hiff : (∀ i : Fin n, IntAt w.1 ((qOf w.1 : X.E) ^ cst.M * (η + δ) (Pi.single i 1))) ↔ ∀ i : Fin n, IntAt w.1 ((qOf w.1 : X.E) ^ cst.M * η (Pi.single i 1))`.

Prove the components needed by the constructor for the conclusion. Introduce `h i`. Use `ciIntAt_sub (h i) (hδM i)` as an intermediate fact. Rewrite `this` using `[LinearMap.add_apply, mul_add, add_sub_cancel_right]`. Then use the resulting hypothesis. Introduce `h i`.

Rewrite using `[LinearMap.add_apply, mul_add]`. Conclude with `(h i).add (hδM i)`. Unfold `ftY`. Rewrite using `[if_neg hw, if_neg hw]`. Distinguish the cases in `hI : ∀ i : Fin n, IntAt w.1 ((qOf w.1 : X.E) ^ cst.M * η (Pi.single i 1))`.

Rewrite using `[if_pos (hiff.2 hI), if_pos hI]`. Establish `heps : IntAt w.1 ((epsSg : ℤ) : X.E)`. Establish `: ((epsSg : ℤ) : X.E) = -1` using `by simp [epsSg]`. Rewrite using `[this]`. Conclude with `intAt_neg_kernel_local_factors (by simpa using intAt_natCast_kernel_local_factors w.1 1)`.

Establish `h1 : IntAt w.1 (δ y)`. Use `intAt_linear_form_on_std w.1 ((((qOf w.1 : X.E) ^ cst.M)⁻¹) • δ) (fun j => by` as an intermediate fact. Rewrite using `[LinearMap.smul_apply, smul_eq_mul]`. Conclude with `hδ j) hq`. Rewrite `this` using `[LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hq0, one_mul]`.

Conclude with `this`. Establish `h2 : IntAt w.1 ((qOf w.1 : X.E) ^ cst.M * ((qOf w.1 : X.E) ^ cst.M * η y))`. Establish `hL : ∀ v ∈ stdAt X.E n w.1, IntAt w.1 ((qOf w.1 : X.E) ^ cst.M * η v)`. Introduce `v hv`. Use `intAt_linear_form_on_std w.1 (((qOf w.1 : X.E) ^ cst.M) • η) (fun j => by` as an intermediate fact.

Rewrite using `[LinearMap.smul_apply, smul_eq_mul]`. Conclude with `hI j) hv`. Rewrite `this` using `[LinearMap.smul_apply, smul_eq_mul]`. Then use the resulting hypothesis. Use `hL _ hq` as an intermediate fact. Rewrite `this` using `[map_smul, smul_eq_mul]`. Then use the resulting hypothesis.

Take `⟨k, hk'⟩ : ∃ k, cst.D w = k + (cst.M + cst.M)` from `⟨cst.D w - 2 * cst.M, by omega⟩`. Establish `hqD : ∀ a : X.E, IntAt w.1 ((qOf w.1 : X.E) ^ cst.M * ((qOf w.1 : X.E) ^ cst.M * a)) → IntAt w.1 ((qOf w.1 : X.E) ^ cst.D w * a)`. Introduce `a ha`. Establish `e' : (qOf w.1 : X.E) ^ cst.D w * a = (qOf w.1 : X.E) ^ k * ((qOf w.1 : X.E) ^ cst.M * ((qOf w.1 : X.E) ^ cst.M * a))`. Rewrite using `[hk', pow_add, pow_add]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e']`. Conclude with `(hqn k).mul ha`. Rewrite using `[LinearMap.add_apply, mul_add, hcst.psi_add w _ _ ?_ ?_, hcst.psi_int w _ (IntAt.mul heps h1), mul_one]`. Use `hqD _ ?_` and prove the remaining obligations.

Establish `e' : (qOf w.1 : X.E) ^ cst.M * ((qOf w.1 : X.E) ^ cst.M * (((epsSg : ℤ) : X.E) * η y)) = ((epsSg : ℤ) : X.E) * ((qOf w.1 : X.E) ^ cst.M * ((qOf w.1 : X.E) ^ cst.M * η y))` using `by ring`. Rewrite using `[e']`. Conclude with `heps.mul h2`. Conclude with `hqD _ ((hqn _).mul ((hqn _).mul (heps.mul h1)))`. Rewrite using `[if_neg (mt hiff.1 hI), if_neg hI]`.
-/
theorem ftY_pert_qM (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
    (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))
    (hcst : cst.Ok) (w : rowSG Pr sel mu) (hw : w.1 ∉ Pr.vGs) (hD : 2 * cst.M ≤ cst.D w) {n : ℕ}
    (η δ : Sp X.E n →ₗ[X.E] X.E) (y : Sp X.E n)
    (hδ : ∀ i : Fin n, IntAt w.1 (((qOf w.1 : X.E) ^ cst.M)⁻¹ * δ (Pi.single i 1)))
    (hq : ((qOf w.1 : X.E) ^ cst.M) • y ∈ stdAt X.E n w.1) :
    ftY sel mu cst w (η + δ) y = ftY sel mu cst w η y := by
  have hqn := intAt_qpow3 (X := X) w.1
  have hq1 : (qOf w.1 : X.E) ≠ 0 := by exact_mod_cast (qOf_pos w.1).ne'
  have hq0 : (qOf w.1 : X.E) ^ cst.M ≠ 0 := pow_ne_zero _ hq1
  have hδM : ∀ i : Fin n, IntAt w.1 ((qOf w.1 : X.E) ^ cst.M * δ (Pi.single i 1)) := fun i => by
    have e : (qOf w.1 : X.E) ^ cst.M * δ (Pi.single i 1) =
        (qOf w.1 : X.E) ^ (2 * cst.M) * ((((qOf w.1 : X.E) ^ cst.M)⁻¹) * δ (Pi.single i 1)) := by
      rw [show 2 * cst.M = cst.M + cst.M by ring, pow_add]
      field_simp
    rw [e]
    exact (hqn _).mul (hδ i)
  have hiff : (∀ i : Fin n, IntAt w.1 ((qOf w.1 : X.E) ^ cst.M * (η + δ) (Pi.single i 1))) ↔
      ∀ i : Fin n, IntAt w.1 ((qOf w.1 : X.E) ^ cst.M * η (Pi.single i 1)) := by
    constructor
    · intro h i
      have := ciIntAt_sub (h i) (hδM i)
      rwa [LinearMap.add_apply, mul_add, add_sub_cancel_right] at this
    · intro h i
      rw [LinearMap.add_apply, mul_add]
      exact (h i).add (hδM i)
  unfold ftY
  rw [if_neg hw, if_neg hw]
  by_cases hI : ∀ i : Fin n, IntAt w.1 ((qOf w.1 : X.E) ^ cst.M * η (Pi.single i 1))
  · rw [if_pos (hiff.2 hI), if_pos hI]
    have heps : IntAt w.1 ((epsSg : ℤ) : X.E) := by
      have : ((epsSg : ℤ) : X.E) = -1 := by simp [epsSg]
      rw [this]
      exact intAt_neg_kernel_local_factors (by simpa using intAt_natCast_kernel_local_factors w.1 1)

    have h1 : IntAt w.1 (δ y) := by
      have := intAt_linear_form_on_std w.1 ((((qOf w.1 : X.E) ^ cst.M)⁻¹) • δ) (fun j => by
        rw [LinearMap.smul_apply, smul_eq_mul]
        exact hδ j) hq
      rw [LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hq0, one_mul] at this
      exact this
    have h2 : IntAt w.1 ((qOf w.1 : X.E) ^ cst.M * ((qOf w.1 : X.E) ^ cst.M * η y)) := by
      have hL : ∀ v ∈ stdAt X.E n w.1, IntAt w.1 ((qOf w.1 : X.E) ^ cst.M * η v) := by
        intro v hv
        have := intAt_linear_form_on_std w.1 (((qOf w.1 : X.E) ^ cst.M) • η) (fun j => by
          rw [LinearMap.smul_apply, smul_eq_mul]
          exact hI j) hv
        rwa [LinearMap.smul_apply, smul_eq_mul] at this
      have := hL _ hq
      rwa [map_smul, smul_eq_mul] at this
    obtain ⟨k, hk'⟩ : ∃ k, cst.D w = k + (cst.M + cst.M) := ⟨cst.D w - 2 * cst.M, by omega⟩
    have hqD : ∀ a : X.E, IntAt w.1 ((qOf w.1 : X.E) ^ cst.M * ((qOf w.1 : X.E) ^ cst.M * a)) →
        IntAt w.1 ((qOf w.1 : X.E) ^ cst.D w * a) := by
      intro a ha
      have e' : (qOf w.1 : X.E) ^ cst.D w * a = (qOf w.1 : X.E) ^ k * ((qOf w.1 : X.E) ^ cst.M * ((qOf w.1 : X.E) ^ cst.M * a)) := by
        rw [hk', pow_add, pow_add]
        ring
      rw [e']
      exact (hqn k).mul ha
    rw [LinearMap.add_apply, mul_add, hcst.psi_add w _ _ ?_ ?_, hcst.psi_int w _ (IntAt.mul heps h1), mul_one]
    · refine hqD _ ?_
      have e' : (qOf w.1 : X.E) ^ cst.M * ((qOf w.1 : X.E) ^ cst.M * (((epsSg : ℤ) : X.E) * η y)) =
          ((epsSg : ℤ) : X.E) * ((qOf w.1 : X.E) ^ cst.M * ((qOf w.1 : X.E) ^ cst.M * η y)) := by ring
      rw [e']
      exact heps.mul h2
    · exact hqD _ ((hqn _).mul ((hqn _).mul (heps.mul h1)))
  · rw [if_neg (mt hiff.1 hI), if_neg hI]

end FtY

section Core

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

/- English proof (translation)
Take `⟨hgI, hgB, hgD⟩` from `hg`. Establish `hI : ∀ i j, IntAt P (g (Pi.single j 1) i)` using `fun i j => (ciMem_stdAt P _).1 ((hgI _).2 (ciSingle_mem j)) i`. Establish `hqn : ∀ k : ℕ, IntAt P ((q : E) ^ k)` using `fun k => by`. Establish `h` using `IntAt.coe P (((q : ℕ) : 𝓞 E) ^ k)`. Rewrite `h` using `[map_pow, map_natCast]`. Then use the resulting hypothesis.

Establish `hsplit : ∀ i, g v i = ∑ j : Fin (N - 1), g (Pi.single ⟨j.1, by omega⟩ 1) i * v ⟨j.1, by omega⟩ + g (Pi.single ⟨N - 1, by omega⟩ 1) i * v ⟨N - 1, by omega⟩` using `fun i => by`. Rewrite using `[residue_linearEquiv_apply_eq_sum g v i, tlq_sum_split hN]`. Establish `hlastcol : ∀ i : Fin N, i.1 < N - 1 → IntAt P (g (Pi.single ⟨N - 1, by omega⟩ 1) i * v ⟨N - 1, by omega⟩ / (q : E))` using `fun i hi => by`. Apply the tactic sequence `have hb := hgB i ⟨N - 1, by omega⟩ (by first | omega | (simp; done) | (simp; omega))`. Establish `e : g (Pi.single ⟨N - 1, by omega⟩ 1) i * v ⟨N - 1, by omega⟩ / (q : E) = (q : E) ^ (cc - M - 1) * ((((q : E) ^ cc)⁻¹ * g (Pi.single ⟨N - 1, by omega⟩ 1) i) * ((q : E) ^ M * v ⟨N - 1, by omega⟩))`.

Establish `h1 : (q : E) ^ cc = (q : E) ^ (cc - M - 1) * (q : E) ^ M * (q : E)`. Rewrite using `[← pow_add, ← pow_succ, show cc - M - 1 + M + 1 = cc by omega]`. Rewrite using `[h1]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`.

Conclude with `(hqn _).mul (hb.mul hvL)`. Use `⟨fun i hi => ?_, ?_⟩` and prove the remaining obligations. Establish `hfirst : IntAt P (∑ j : Fin (N - 1), g (Pi.single ⟨j.1, by omega⟩ 1) i * v ⟨j.1, by omega⟩)` using `ciIntAt_sum _ _ fun j _ => (hI _ _).mul (hvX _ j.2)`. Establish `hl` using `hlastcol i hi`. Establish `hlI : IntAt P (g (Pi.single ⟨N - 1, by omega⟩ 1) i * v ⟨N - 1, by omega⟩)`.

Establish `e : g (Pi.single ⟨N - 1, by omega⟩ 1) i * v ⟨N - 1, by omega⟩ = (q : E) * (g (Pi.single ⟨N - 1, by omega⟩ 1) i * v ⟨N - 1, by omega⟩ / (q : E))` using `by field_simp`. Rewrite using `[e]`. Conclude with `(hqn 1 |>.mul hl |> fun h => by simpa using h)`. Use `⟨by rw [hsplit]; exact hfirst.add hlI, ?_⟩` and prove the remaining obligations. Rewrite using `[hsplit, reduction_add hfirst hlI]`.

Establish `hz : redP P (g (Pi.single ⟨N - 1, by omega⟩ 1) i * v ⟨N - 1, by omega⟩) = 0`. Establish `e : g (Pi.single ⟨N - 1, by omega⟩ 1) i * v ⟨N - 1, by omega⟩ = (q : E) * (g (Pi.single ⟨N - 1, by omega⟩ 1) i * v ⟨N - 1, by omega⟩ / (q : E))` using `by field_simp`. Rewrite using `[e, reduction_mul (by simpa using hqn 1) hl, redP_natCast_eq_zero hq, zero_mul]`. Rewrite using `[hz, add_zero, redP_sum _ _ fun j _ => (hI _ _).mul (hvX _ j.2)]`. Conclude with `Finset.sum_congr rfl fun j _ => reduction_mul (hI _ _) (hvX _ j.2)`.

Rewrite using `[hsplit]`. Establish `e : ∑ j : Fin (N - 1), g (Pi.single ⟨j.1, by omega⟩ 1) ⟨N - 1, by omega⟩ * v ⟨j.1, by omega⟩ + g (Pi.single ⟨N - 1, by omega⟩ 1) ⟨N - 1, by omega⟩ * v ⟨N - 1, by omega⟩ - v ⟨N - 1, by omega⟩ = ∑ j : Fin (N - 1), g (Pi.single ⟨j.1, by omega⟩ 1) ⟨N - 1, by omega⟩ * v ⟨j.1, by omega …` using `by ring`. Rewrite using `[e, mul_add, Finset.mul_sum]`. Use `(ciIntAt_sum _ _ fun j _ => ?_).add ?_` and prove the remaining obligations. Apply the tactic sequence `have hc := hgB ⟨N - 1, by omega⟩ ⟨j.1, by omega⟩ (by first | omega | (simp; done) | (simp; omega))`.

Establish `e2 : ((q : E) ^ M)⁻¹ * (g (Pi.single ⟨j.1, by omega⟩ 1) ⟨N - 1, by omega⟩ * v ⟨j.1, by omega⟩) = (q : E) ^ (cc - M) * ((((q : E) ^ cc)⁻¹ * g (Pi.single ⟨j.1, by omega⟩ 1) ⟨N - 1, by omega⟩) * v ⟨j.1, by omega⟩)`. Establish `h1 : (q : E) ^ cc = (q : E) ^ (cc - M) * (q : E) ^ M` using `by rw [← pow_add, show cc - M + M = cc by omega]`. Rewrite using `[h1]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e2]`.

Conclude with `(hqn _).mul (hc.mul (hvX _ j.2))`. Apply the tactic sequence `have hd := hgD ⟨N - 1, by omega⟩ (by first | omega | (simp; done) | (simp; omega))`. Establish `e2 : ((q : E) ^ M)⁻¹ * ((g (Pi.single ⟨N - 1, by omega⟩ 1) ⟨N - 1, by omega⟩ - 1) * v ⟨N - 1, by omega⟩) = (q : E) ^ (cc - 2 * M) * ((((q : E) ^ cc)⁻¹ * (g (Pi.single ⟨N - 1, by omega⟩ 1) ⟨N - 1, by omega⟩ - 1)) * ((q : E) ^ M * v ⟨N - 1, by omega⟩))`. Establish `h1 : (q : E) ^ cc = (q : E) ^ (cc - 2 * M) * (q : E) ^ M * (q : E) ^ M`. Rewrite using `[← pow_add, ← pow_add, show cc - 2 * M + M + M = cc by omega]`.

Rewrite using `[h1]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e2]`. Conclude with `(hqn _).mul (hd.mul hvL)`.
-/
theorem vector_moved_by_K1Depth_twiceM_integrality (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hq0 : (q : E) ≠ 0) {N M cc : ℕ} (hN : 1 ≤ N) (hM : 1 ≤ M)
    (hMc : 2 * M ≤ cc)
    {g : Sp E N ≃ₗ[E] Sp E N} (hg : IsKOneType P q cc g) (v : Sp E N)
    (hvX : ∀ i : Fin N, i.1 < N - 1 → IntAt P (v i)) (hvL : IntAt P ((q : E) ^ M * v ⟨N - 1, by omega⟩)) :
    (∀ i : Fin N, i.1 < N - 1 → IntAt P (g v i) ∧
      redP P (g v i) = ∑ j : Fin (N - 1), redP P (g (Pi.single ⟨j.1, by omega⟩ 1) i) * redP P (v ⟨j.1, by omega⟩)) ∧
    IntAt P ((((q : E) ^ M)⁻¹) * (g v ⟨N - 1, by omega⟩ - v ⟨N - 1, by omega⟩)) := by
  obtain ⟨hgI, hgB, hgD⟩ := hg
  have hI : ∀ i j, IntAt P (g (Pi.single j 1) i) := fun i j => (ciMem_stdAt P _).1 ((hgI _).2 (ciSingle_mem j)) i
  have hqn : ∀ k : ℕ, IntAt P ((q : E) ^ k) := fun k => by
    have h := IntAt.coe P (((q : ℕ) : 𝓞 E) ^ k)
    rwa [map_pow, map_natCast] at h
  have hsplit : ∀ i, g v i = ∑ j : Fin (N - 1), g (Pi.single ⟨j.1, by omega⟩ 1) i * v ⟨j.1, by omega⟩ +
      g (Pi.single ⟨N - 1, by omega⟩ 1) i * v ⟨N - 1, by omega⟩ := fun i => by
    rw [residue_linearEquiv_apply_eq_sum g v i, tlq_sum_split hN]
  have hlastcol : ∀ i : Fin N, i.1 < N - 1 →
      IntAt P (g (Pi.single ⟨N - 1, by omega⟩ 1) i * v ⟨N - 1, by omega⟩ / (q : E)) := fun i hi => by
    have hb := hgB i ⟨N - 1, by omega⟩ (by first | omega | (simp; done) | (simp; omega))
    have e : g (Pi.single ⟨N - 1, by omega⟩ 1) i * v ⟨N - 1, by omega⟩ / (q : E) =
        (q : E) ^ (cc - M - 1) * ((((q : E) ^ cc)⁻¹ * g (Pi.single ⟨N - 1, by omega⟩ 1) i) * ((q : E) ^ M * v ⟨N - 1, by omega⟩)) := by
      have h1 : (q : E) ^ cc = (q : E) ^ (cc - M - 1) * (q : E) ^ M * (q : E) := by
        rw [← pow_add, ← pow_succ, show cc - M - 1 + M + 1 = cc by omega]
      rw [h1]
      field_simp
    rw [e]
    exact (hqn _).mul (hb.mul hvL)
  refine ⟨fun i hi => ?_, ?_⟩
  · have hfirst : IntAt P (∑ j : Fin (N - 1), g (Pi.single ⟨j.1, by omega⟩ 1) i * v ⟨j.1, by omega⟩) :=
      ciIntAt_sum _ _ fun j _ => (hI _ _).mul (hvX _ j.2)
    have hl := hlastcol i hi
    have hlI : IntAt P (g (Pi.single ⟨N - 1, by omega⟩ 1) i * v ⟨N - 1, by omega⟩) := by
      have e : g (Pi.single ⟨N - 1, by omega⟩ 1) i * v ⟨N - 1, by omega⟩ =
          (q : E) * (g (Pi.single ⟨N - 1, by omega⟩ 1) i * v ⟨N - 1, by omega⟩ / (q : E)) := by field_simp
      rw [e]
      exact (hqn 1 |>.mul hl |> fun h => by simpa using h)
    refine ⟨by rw [hsplit]; exact hfirst.add hlI, ?_⟩
    rw [hsplit, reduction_add hfirst hlI]
    have hz : redP P (g (Pi.single ⟨N - 1, by omega⟩ 1) i * v ⟨N - 1, by omega⟩) = 0 := by
      have e : g (Pi.single ⟨N - 1, by omega⟩ 1) i * v ⟨N - 1, by omega⟩ =
          (q : E) * (g (Pi.single ⟨N - 1, by omega⟩ 1) i * v ⟨N - 1, by omega⟩ / (q : E)) := by field_simp
      rw [e, reduction_mul (by simpa using hqn 1) hl, redP_natCast_eq_zero hq, zero_mul]
    rw [hz, add_zero, redP_sum _ _ fun j _ => (hI _ _).mul (hvX _ j.2)]
    exact Finset.sum_congr rfl fun j _ => reduction_mul (hI _ _) (hvX _ j.2)
  · rw [hsplit]
    have e : ∑ j : Fin (N - 1), g (Pi.single ⟨j.1, by omega⟩ 1) ⟨N - 1, by omega⟩ * v ⟨j.1, by omega⟩ +
          g (Pi.single ⟨N - 1, by omega⟩ 1) ⟨N - 1, by omega⟩ * v ⟨N - 1, by omega⟩ - v ⟨N - 1, by omega⟩ =
        ∑ j : Fin (N - 1), g (Pi.single ⟨j.1, by omega⟩ 1) ⟨N - 1, by omega⟩ * v ⟨j.1, by omega⟩ +
          (g (Pi.single ⟨N - 1, by omega⟩ 1) ⟨N - 1, by omega⟩ - 1) * v ⟨N - 1, by omega⟩ := by ring
    rw [e, mul_add, Finset.mul_sum]
    refine (ciIntAt_sum _ _ fun j _ => ?_).add ?_
    · have hc := hgB ⟨N - 1, by omega⟩ ⟨j.1, by omega⟩ (by first | omega | (simp; done) | (simp; omega))
      have e2 : ((q : E) ^ M)⁻¹ * (g (Pi.single ⟨j.1, by omega⟩ 1) ⟨N - 1, by omega⟩ * v ⟨j.1, by omega⟩) =
          (q : E) ^ (cc - M) * ((((q : E) ^ cc)⁻¹ * g (Pi.single ⟨j.1, by omega⟩ 1) ⟨N - 1, by omega⟩) * v ⟨j.1, by omega⟩) := by
        have h1 : (q : E) ^ cc = (q : E) ^ (cc - M) * (q : E) ^ M := by rw [← pow_add, show cc - M + M = cc by omega]
        rw [h1]
        field_simp
      rw [e2]
      exact (hqn _).mul (hc.mul (hvX _ j.2))
    · have hd := hgD ⟨N - 1, by omega⟩ (by first | omega | (simp; done) | (simp; omega))
      have e2 : ((q : E) ^ M)⁻¹ * ((g (Pi.single ⟨N - 1, by omega⟩ 1) ⟨N - 1, by omega⟩ - 1) * v ⟨N - 1, by omega⟩) =
          (q : E) ^ (cc - 2 * M) * ((((q : E) ^ cc)⁻¹ * (g (Pi.single ⟨N - 1, by omega⟩ 1) ⟨N - 1, by omega⟩ - 1)) *
            ((q : E) ^ M * v ⟨N - 1, by omega⟩)) := by
        have h1 : (q : E) ^ cc = (q : E) ^ (cc - 2 * M) * (q : E) ^ M * (q : E) ^ M := by
          rw [← pow_add, ← pow_add, show cc - 2 * M + M + M = cc by omega]
        rw [h1]
        field_simp
      rw [e2]
      exact (hqn _).mul (hd.mul hvL)

/- English proof (translation)
Establish `hlast : N - 1 < N` using `by omega`. Establish `hat : ∀ v : Sp E N, atNL E N (N - 1) v = v ⟨N - 1, hlast⟩` using `fun v => by`. Unfold `atNL`. Rewrite using `[dif_pos hlast]`. Both sides reduce to the same expression.

Establish `hqn : ∀ k : ℕ, IntAt P ((q : E) ^ k)` using `fun k => by`. Establish `h` using `IntAt.coe P (((q : ℕ) : 𝓞 E) ^ k)`. Rewrite `h` using `[map_pow, map_natCast]`. Then use the resulting hypothesis. Set `S : HomE E n' N → Prop` to `fun z => (∀ s (i : Fin N), i.1 < N - 1 → IntAt P (z (Pi.single s 1) i)) ∧ ∀ s, IntAt P ((q : E) ^ M * z (Pi.single s 1) ⟨N - 1, hlast⟩)`. Establish `hstab : ∀ (h : Sp E N ≃ₗ[E] Sp E N), IsKOneType P q cc h → ∀ z, S z → S (h.toLinearMap ∘ₗ z)`.

Introduce `h hh z hz`. Use `⟨fun s i hi => ((vector_moved_by_K1Depth_twiceM_integrality hq hq0 hN hM hMc hh _ (hz.1 s) (hz.2 s)).1 i hi).1, fun s => ?_⟩` and prove the remaining obligations. Establish `h2` using `(vector_moved_by_K1Depth_twiceM_integrality hq hq0 hN hM hMc hh _ (hz.1 s) (hz.2 s)).2`. Establish `e : (q : E) ^ M * (h.toLinearMap ∘ₗ z) (Pi.single s 1) ⟨N - 1, hlast⟩ = (q : E) ^ M * z (Pi.single s 1) ⟨N - 1, hlast⟩ + (q : E) ^ (2 * M) * ((((q : E) ^ M)⁻¹) * (h (z (Pi.single s 1)) ⟨N - 1, hlast⟩ - z (Pi.single s 1) ⟨N - 1, hlast⟩))`. Establish `hqM : (q : E) ^ M ≠ 0` using `pow_ne_zero _ hq0`.

Use `show (q : E) ^ M * h (z (Pi.single s 1)) ⟨N - 1, hlast⟩ = _`. Rewrite using `[two_mul, pow_add]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Conclude with `(hz.2 s).add ((hqn _).mul h2)`. Establish `hprX : ∀ (x : HomE E n' N) s (l : Fin ((N - 1) + 0)), (prXpG E N ∘ₗ x) (Pi.single s 1) l = x (Pi.single s 1) ⟨l.1, by omega⟩` using `fun _ _ _ => rfl`. Establish `hZ : ∀ z, ¬ S z → Φ (prXpG E N ∘ₗ z) * T (atNL E N (N - 1) ∘ₗ z) = 0 ∧ Φ (κ.toLinearMap ∘ₗ prXpG E N ∘ₗ z) * T (atNL E N (N - 1) ∘ₗ z) = 0`. Introduce `z hz`. Establish `hT0 : T (atNL E N (N - 1) ∘ₗ z) ≠ 0 → ∀ s, IntAt P ((q : E) ^ M * z (Pi.single s 1) ⟨N - 1, hlast⟩)` using `fun h s => by`.

Use `hTs _ h s` as an intermediate fact. Rewrite `this` using `[LinearMap.comp_apply, hat]`. Then use the resulting hypothesis. Prove the components needed by the constructor for the conclusion. Assume the negation of the conclusion as `hne`. Take `⟨h1, h2⟩` from `mul_ne_zero_iff.1 hne`.

Apply `hz` to reduce the goal to its premises. Use `⟨fun s i hi => ?_, hT0 h2⟩` and prove the remaining obligations. Use `hΦs _ h1 s ⟨i.1, by omega⟩` as an intermediate fact. Rewrite `this` using `[hprX]`. Then use the resulting hypothesis. Assume the negation of the conclusion as `hne`.

Take `⟨h1, h2⟩` from `mul_ne_zero_iff.1 hne`. Apply `hz` to reduce the goal to its premises. Use `⟨fun s i hi => ?_, hT0 h2⟩` and prove the remaining obligations. Establish `hk` using `hΦs _ h1 s`. Establish `hmem : κ ((prXpG E N ∘ₗ z) (Pi.single s 1)) ∈ stdAt E ((N - 1) + 0) P` using `(ciMem_stdAt P _).2 fun l => hk l`.

Use `(ciMem_stdAt P _).1 ((hκ _).1 hmem) ⟨i.1, by omega⟩` as an intermediate fact. Rewrite `this` using `[hprX]`. Then use the resulting hypothesis. Distinguish the cases in `hS : S z`. Establish `hδ : ∀ s, IntAt P (((q : E) ^ M)⁻¹ * ((atNL E N (N - 1) ∘ₗ g.toLinearMap ∘ₗ z) - (atNL E N (N - 1) ∘ₗ z)) (Pi.single s 1))` using `fun s => by`. Establish `h2` using `(vector_moved_by_K1Depth_twiceM_integrality hq hq0 hN hM hMc hg _ (hS.1 s) (hS.2 s)).2`.

Simplify using `only [LinearMap.sub_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, hat]`. Conclude with `h2`. Establish `eT : T (atNL E N (N - 1) ∘ₗ g.toLinearMap ∘ₗ z) = T (atNL E N (N - 1) ∘ₗ z)`. Use `hTp (atNL E N (N - 1) ∘ₗ z) _ hδ` as an intermediate fact. Rewrite `this` using `[add_sub_cancel]`. Then use the resulting hypothesis.

Rewrite using `[eT]`. Use `congr 1`. Use `hΦr _ _ (fun s l => ?_) (fun s l => ?_) ?_` and prove the remaining obligations. Rewrite using `[hprX]`. Conclude with `((vector_moved_by_K1Depth_twiceM_integrality hq hq0 hN hM hMc hg _ (hS.1 s) (hS.2 s)).1 _ l.2).1`.

Establish `hmem : (prXpG E N ∘ₗ z) (Pi.single s 1) ∈ stdAt E ((N - 1) + 0) P` using `(ciMem_stdAt P _).2 fun l => by rw [hprX]; exact hS.1 s _ l.2`. Conclude with `(ciMem_stdAt P _).1 ((hκ _).2 hmem) l`. Use extensionality with `l s show redP P ((prXpG E N ∘ₗ g.toLinearMap ∘ₗ z) (Pi.single s 1) l) = redP P ((κ.toLinearMap ∘ₗ prXpG E N ∘ₗ z) (Pi.single s 1) l)`. Rewrite using `[hprX]`. Establish `h1` using `((vector_moved_by_K1Depth_twiceM_integrality hq hq0 hN hM hMc hg _ (hS.1 s) (hS.2 s)).1 ⟨l.1, by omega⟩ l.2).2`.

Establish `hmem : (prXpG E N ∘ₗ z) (Pi.single s 1) ∈ stdAt E ((N - 1) + 0) P` using `(ciMem_stdAt P _).2 fun l => by rw [hprX]; exact hS.1 s _ l.2`. Establish `h2` using `congrFun (hκr _ hmem) l`. Use `show _ = redV P (κ ((prXpG E N ∘ₗ z) (Pi.single s 1))) l`. Rewrite using `[h2]`. Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe]`.

Rewrite using `[h1]`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.of_apply]`. Both sides reduce to the same expression. Establish `hSg : ¬ S (g.toLinearMap ∘ₗ z)` using `fun h => hS (by`. Use `hstab g.symm hg' _ h` as an intermediate fact.

Establish `e : g.symm.toLinearMap ∘ₗ g.toLinearMap ∘ₗ z = z`. Use extensionality with `v`. Simplify using the standard rewrite rules. Rewrite using `[e] at this)` and apply the resulting hypothesis. Rewrite using `[(hZ _ hSg).1, (hZ _ hS).2]`.
-/
theorem residueClassProduct_invariant_K1Depth_twiceM (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hq0 : (q : E) ≠ 0) {n' N M cc : ℕ} (hN : 1 ≤ N) (hM : 1 ≤ M)
    (hMc : 2 * M ≤ cc)
    (Φ : HomE E n' ((N - 1) + 0) → K) (hΦs : ∀ x, Φ x ≠ 0 → ∀ s l, IntAt P (x (Pi.single s 1) l))
    (hΦr : ∀ x x', (∀ s l, IntAt P (x (Pi.single s 1) l)) → (∀ s l, IntAt P (x' (Pi.single s 1) l)) → redMQ P x = redMQ P x' → Φ x = Φ x')
    (T : (Sp E n' →ₗ[E] E) → K) (hTs : ∀ η, T η ≠ 0 → ∀ i, IntAt P ((q : E) ^ M * η (Pi.single i 1)))
    (hTp : ∀ η δ, (∀ i, IntAt P (((q : E) ^ M)⁻¹ * δ (Pi.single i 1))) → T (η + δ) = T η)
    (g : Sp E N ≃ₗ[E] Sp E N) (hg : IsKOneType P q cc g) (hg' : IsKOneType P q cc g.symm)
    (κ : Sp E ((N - 1) + 0) ≃ₗ[E] Sp E ((N - 1) + 0)) (hκ : κ ∈ GLint E ((N - 1) + 0) P)
    (hκr : ∀ v ∈ stdAt E ((N - 1) + 0) P, redV P (κ v) =
      (Matrix.of fun (i j : Fin ((N - 1) + 0)) => redP P (g (Pi.single ⟨j.1, by omega⟩ 1) ⟨i.1, by omega⟩)).mulVec (redV P v))
    (z : HomE E n' N) :
    Φ (prXpG E N ∘ₗ g.toLinearMap ∘ₗ z) * T (atNL E N (N - 1) ∘ₗ g.toLinearMap ∘ₗ z) =
      Φ (κ.toLinearMap ∘ₗ prXpG E N ∘ₗ z) * T (atNL E N (N - 1) ∘ₗ z) := by
  have hlast : N - 1 < N := by omega
  have hat : ∀ v : Sp E N, atNL E N (N - 1) v = v ⟨N - 1, hlast⟩ := fun v => by
    unfold atNL
    rw [dif_pos hlast]
    rfl
  have hqn : ∀ k : ℕ, IntAt P ((q : E) ^ k) := fun k => by
    have h := IntAt.coe P (((q : ℕ) : 𝓞 E) ^ k)
    rwa [map_pow, map_natCast] at h
  let S : HomE E n' N → Prop := fun z => (∀ s (i : Fin N), i.1 < N - 1 → IntAt P (z (Pi.single s 1) i)) ∧
    ∀ s, IntAt P ((q : E) ^ M * z (Pi.single s 1) ⟨N - 1, hlast⟩)
  have hstab : ∀ (h : Sp E N ≃ₗ[E] Sp E N), IsKOneType P q cc h → ∀ z, S z → S (h.toLinearMap ∘ₗ z) := by
    intro h hh z hz
    refine ⟨fun s i hi => ((vector_moved_by_K1Depth_twiceM_integrality hq hq0 hN hM hMc hh _ (hz.1 s) (hz.2 s)).1 i hi).1, fun s => ?_⟩
    have h2 := (vector_moved_by_K1Depth_twiceM_integrality hq hq0 hN hM hMc hh _ (hz.1 s) (hz.2 s)).2
    have e : (q : E) ^ M * (h.toLinearMap ∘ₗ z) (Pi.single s 1) ⟨N - 1, hlast⟩ =
        (q : E) ^ M * z (Pi.single s 1) ⟨N - 1, hlast⟩ +
          (q : E) ^ (2 * M) * ((((q : E) ^ M)⁻¹) * (h (z (Pi.single s 1)) ⟨N - 1, hlast⟩ - z (Pi.single s 1) ⟨N - 1, hlast⟩)) := by
      have hqM : (q : E) ^ M ≠ 0 := pow_ne_zero _ hq0
      show (q : E) ^ M * h (z (Pi.single s 1)) ⟨N - 1, hlast⟩ = _
      rw [two_mul, pow_add]
      field_simp
      ring
    rw [e]
    exact (hz.2 s).add ((hqn _).mul h2)
  have hprX : ∀ (x : HomE E n' N) s (l : Fin ((N - 1) + 0)), (prXpG E N ∘ₗ x) (Pi.single s 1) l = x (Pi.single s 1) ⟨l.1, by omega⟩ :=
    fun _ _ _ => rfl
  have hZ : ∀ z, ¬ S z → Φ (prXpG E N ∘ₗ z) * T (atNL E N (N - 1) ∘ₗ z) = 0 ∧
      Φ (κ.toLinearMap ∘ₗ prXpG E N ∘ₗ z) * T (atNL E N (N - 1) ∘ₗ z) = 0 := by
    intro z hz
    have hT0 : T (atNL E N (N - 1) ∘ₗ z) ≠ 0 → ∀ s, IntAt P ((q : E) ^ M * z (Pi.single s 1) ⟨N - 1, hlast⟩) := fun h s => by
      have := hTs _ h s
      rwa [LinearMap.comp_apply, hat] at this
    constructor
    · by_contra hne
      obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 hne
      apply hz
      refine ⟨fun s i hi => ?_, hT0 h2⟩
      have := hΦs _ h1 s ⟨i.1, by omega⟩
      rwa [hprX] at this
    · by_contra hne
      obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 hne
      apply hz
      refine ⟨fun s i hi => ?_, hT0 h2⟩
      have hk := hΦs _ h1 s
      have hmem : κ ((prXpG E N ∘ₗ z) (Pi.single s 1)) ∈ stdAt E ((N - 1) + 0) P := (ciMem_stdAt P _).2 fun l => hk l
      have := (ciMem_stdAt P _).1 ((hκ _).1 hmem) ⟨i.1, by omega⟩
      rwa [hprX] at this
  by_cases hS : S z
  · have hδ : ∀ s, IntAt P (((q : E) ^ M)⁻¹ *
        ((atNL E N (N - 1) ∘ₗ g.toLinearMap ∘ₗ z) - (atNL E N (N - 1) ∘ₗ z)) (Pi.single s 1)) := fun s => by
      have h2 := (vector_moved_by_K1Depth_twiceM_integrality hq hq0 hN hM hMc hg _ (hS.1 s) (hS.2 s)).2
      simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, hat]
      exact h2
    have eT : T (atNL E N (N - 1) ∘ₗ g.toLinearMap ∘ₗ z) = T (atNL E N (N - 1) ∘ₗ z) := by
      have := hTp (atNL E N (N - 1) ∘ₗ z) _ hδ
      rwa [add_sub_cancel] at this
    rw [eT]
    congr 1
    refine hΦr _ _ (fun s l => ?_) (fun s l => ?_) ?_
    · rw [hprX]
      exact ((vector_moved_by_K1Depth_twiceM_integrality hq hq0 hN hM hMc hg _ (hS.1 s) (hS.2 s)).1 _ l.2).1
    · have hmem : (prXpG E N ∘ₗ z) (Pi.single s 1) ∈ stdAt E ((N - 1) + 0) P :=
        (ciMem_stdAt P _).2 fun l => by rw [hprX]; exact hS.1 s _ l.2
      exact (ciMem_stdAt P _).1 ((hκ _).2 hmem) l
    · ext l s
      show redP P ((prXpG E N ∘ₗ g.toLinearMap ∘ₗ z) (Pi.single s 1) l) = redP P ((κ.toLinearMap ∘ₗ prXpG E N ∘ₗ z) (Pi.single s 1) l)
      rw [hprX]
      have h1 := ((vector_moved_by_K1Depth_twiceM_integrality hq hq0 hN hM hMc hg _ (hS.1 s) (hS.2 s)).1 ⟨l.1, by omega⟩ l.2).2
      have hmem : (prXpG E N ∘ₗ z) (Pi.single s 1) ∈ stdAt E ((N - 1) + 0) P :=
        (ciMem_stdAt P _).2 fun l => by rw [hprX]; exact hS.1 s _ l.2
      have h2 := congrFun (hκr _ hmem) l
      show _ = redV P (κ ((prXpG E N ∘ₗ z) (Pi.single s 1))) l
      rw [h2]
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [h1]
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
      rfl
  · have hSg : ¬ S (g.toLinearMap ∘ₗ z) := fun h => hS (by
      have := hstab g.symm hg' _ h
      have e : g.symm.toLinearMap ∘ₗ g.toLinearMap ∘ₗ z = z := by
        ext v
        simp
      rwa [e] at this)
    rw [(hZ _ hSg).1, (hZ _ hS).2]

end Core

section Main

/- English proof (translation)
Use extensionality with `l s`. Use `show redP P ((Pi.single s (1 : E) : Sp E n) l) = (1 : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal)) l s`. Distinguish the cases in `h : l = s`. Substitute `h` using the available equality. Rewrite using `[Pi.single_eq_same, Matrix.one_apply_eq, redP_one]`.

Rewrite using `[Pi.single_eq_of_ne h, Matrix.one_apply_ne h, redP_zero]`.
-/
theorem redMQ_idEquiv {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) :
    redMQ P ((1 : Sp E n ≃ₗ[E] Sp E n) : Sp E n ≃ₗ[E] Sp E n).toLinearMap = 1 := by
  ext l s
  show redP P ((Pi.single s (1 : E) : Sp E n) l) = (1 : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal)) l s
  by_cases h : l = s
  · subst h
    rw [Pi.single_eq_same, Matrix.one_apply_eq, redP_one]
  · rw [Pi.single_eq_of_ne h, Matrix.one_apply_ne h, redP_zero]

/- English proof (translation)
Unfold `xiZ`. Rewrite using `[dif_pos isUnit_one]`. Simplify using the standard rewrite rules.
-/
theorem xiZ_one' {k K : Type} [CommRing k] [Field K] (ξ : kˣ →* Kˣ) : xiZ ξ (1 : k) = 1 := by
  unfold xiZ
  rw [dif_pos isUnit_one]
  simp

end Main

set_option maxHeartbeats 4000000 in

/- English proof (translation)
Introduce `X Pr R Ch sel S mu cst m2 w hw κ' hc' y y₁ hm hcst hu hD2 hMc hq1`. Establish `hwQ : w.1 ∈ QE sel (mu : Chr X.F X.E X.K)` using `(Finset.mem_union.mp w.2).resolve_left hw`. Establish `hqm : ((qOf w.1 : ℕ) : 𝓞 X.E) ∈ w.1.asIdeal` using `qOf_memB w.1`. Establish `hq0` using `ciQ_ne_zero hu`. Establish `hM1 : 1 ≤ cst.M` using `hcst.M_pos`.

Establish `hcc : 1 ≤ twTopDepth R` using `by unfold twTopDepth; omega`. Establish `hNpos` using `R.N_pos (m2 + 1 + 1)`. Establish `hN : R.N (m2 + 1 + 1) = (R.N (m2 + 1 + 1) - 1) + 1` using `by omega`. Establish `hNm : R.N (m2 + 1 + 1) = R.N R.m` using `by rw [hm]`. Establish `hn' : R.N (m2 + 1) = R.r + (m2 + 1) * R.t` using `rank_midQ (R := R) hm`.

Establish `hr' : R.r ≤ R.N (m2 + 1)` using `by rw [hn']; exact Nat.le_add_right _ _`. Establish `hnA : R.N (m2 + 1 + 1) - 1 + 0 = R.r + R.m * R.t` using `by rw [hNm, Nat.add_zero]; exact rank_X'_eq R`. Establish `hrA : R.r ≤ R.N (m2 + 1 + 1) - 1 + 0` using `by rw [hnA]; exact Nat.le_add_right _ _`. Establish `hc0 : cOf R (m2 + 1) = 0` using `cOf_topB hm`. Use `set ξ := resChar (mu : Chr X.F X.E X.K) w.1 with hξ`.

Set `g : ↥(GLint X.E (R.N (m2 + 1 + 1)) w.1)` to `κ'⁻¹`. Establish `hK : IsKOneType w.1 (qOf w.1) (twTopDepth R) (g : Sp X.E (R.N (m2 + 1 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1 + 1)))` using `isKOneType_of_mem_kOne w.1 g hc'`. Establish `hK' : IsKOneType w.1 (qOf w.1) (twTopDepth R) (g : Sp X.E (R.N (m2 + 1 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1 + 1))).symm` using `isKOneType_symm_of_mem_kOne w.1 g hc'`. Take `⟨⟨hAA, hAA'⟩, ⟨-, hdetAi⟩, hD⟩` from `kOneType_block_matrix hqm hq0 hN hcc _ hK hK'`. Use `set A : Matrix (Fin (R.N (m2 + 1 + 1) - 1 + 0)) (Fin (R.N (m2 + 1 + 1) - 1 + 0)) (𝓞 X.E ⧸ w.1.asIdeal) := Matrix.of fun i j => redP w.1 ((g : Sp X.E (R.N (m2 + 1 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1 + 1))) (Pi.single ⟨j.1, by omega⟩ 1) ⟨i.1, by omega⟩) with hAdef`.

Use `set Ai : Matrix (Fin (R.N (m2 + 1 + 1) - 1 + 0)) (Fin (R.N (m2 + 1 + 1) - 1 + 0)) (𝓞 X.E ⧸ w.1.asIdeal) := Matrix.of fun i j => redP w.1 ((g : Sp X.E (R.N (m2 + 1 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1 + 1))).symm (Pi.single ⟨j.1, by omega⟩ 1) ⟨i.1, by omega⟩) with hAidef`. Set `AG : GL (Fin (R.N (m2 + 1 + 1) - 1 + 0)) (𝓞 X.E ⧸ w.1.asIdeal)` to `⟨A, Ai, hAA', hAA⟩`. Establish `hLLz : LLz R.r (redMQ w.1 (g : Sp X.E (R.N (m2 + 1 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1 + 1))).toLinearMap)` using `jq_LLz (n := R.N (m2 + 1 + 1)) (c := 0) (g := (g : Sp X.E (R.N (m2 + 1 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1 + 1)))) (rr := (g : Sp X.E (R.N (m2 + 1 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1 + 1)))) hqm hq0 hc'.1 (fun x => by rw [tlq_inX_zero, tlq_inX_zero])`. Establish `hLLzi : LLz R.r (redMQ w.1 (g : Sp X.E (R.N (m2 + 1 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1 + 1))).symm.toLinearMap)` using `jq_LLz (n := R.N (m2 + 1 + 1)) (c := 0) (g := (g : Sp X.E (R.N (m2 + 1 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1 + 1))).symm) (rr := (g : Sp X.E (R.N (m2 + 1 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1 + 1))).symm) hqm hq0 ((twK1H w.1 _ _ _).inv_mem hc').1 (fun x => by rw [tlq_inX_zero, tlq_inX_ze …`. Establish `lA : LLz R.r A` using `fun i j hi hj => hLLz ⟨i.1, by omega⟩ ⟨j.1, by omega⟩ hi hj`.

Establish `lAi : LLz R.r Ai` using `fun i j hi hj => hLLzi ⟨i.1, by omega⟩ ⟨j.1, by omega⟩ hi hj`. Take `⟨γ, hγI, hγ, -⟩` from `ctl_lift (P := w.1) AG`. Establish `hrA' : R.r ≤ R.N (m2 + 1 + 1) - 1` using `hrA`. Establish `hs2 : rhoT Ch sel mu (m2 + 1) w (LinearEquiv.det κ'.1 : X.Eˣ) = xiZ ξ Ai.det`. Unfold `rhoT`.

Rewrite using `[if_neg hw, unitV_eq, redP_detEquiv w.1 κ'.2]`. Conclude with `congrArg (xiZ ξ) hdetAi`. Establish `hnD : R.N (m2 + 1 + 1) = R.r + (R.m * R.t + 1)` using `by omega`. Establish `hl1 : (((twTt (R` using `R) sel mu (m2 + 1 + 1) ⟨w.1, hwQ⟩).lam ⟨κ'⁻¹, hc'⟩ : X.Kˣ) : X.K) = (xiZ ξ (A.submatrix (brI hnA) (brI hnA)).det)⁻¹ := by show LocE.lamQB ξ R.r (R.N (m2 + 1 + 1)) (g : Sp X.E (R.N (m2 + 1 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1 + 1))).toLinearMap = _`. Establish `e` using `lamQB_eq (P := w.1) ξ (kj := R.r) (r := R.r) (n := R.N (m2 + 1 + 1)) (c := 0) (d := R.m * R.t + 1) rfl hnD g.2 (rr := (g : Sp X.E (R.N (m2 + 1 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1 + 1)))) (fun x => by rw [tlq_inX_zero, tlq_inX_zero])`.

Rewrite using `[e, hD R.r (R.m * R.t) hnA]`. Establish `hf : (1 : Sp X.E (R.N (m2 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1))) ∈ GLint X.E (R.N (m2 + 1)) w.1` using `Subgroup.one_mem _`. Establish `hf1` using `redMQ_idEquiv w.1 (R.N (m2 + 1))`. Establish `l1 : LLz R.r (1 : Matrix (Fin (R.N (m2 + 1))) (Fin (R.N (m2 + 1))) (𝓞 X.E ⧸ w.1.asIdeal))` using `fun i j hi hj => Matrix.one_apply_ne (fun h => by rw [h] at hi; omega)`. Establish `hcore` using `residueClassProduct_invariant_K1Depth_twiceM (E := X.E) (K := X.K) (P := w.1) (q := qOf w.1) hqm hq0 (n' := R.N (m2 + 1)) (N := R.N (m2 + 1 + 1)) (M := cst.M) (cc := twTopDepth R) (by omega) hM1 hMc (fun x => PhiTopG Ch mu cst.sharp (m2 + 1) (m2 + 1 + 1) (R.N (m2 + 1 + 1)) w.1 (x …`.

Unfold `PhiTopG at h`. Apply the tactic sequence `(try rw [if_neg hw] at h)`. Conclude with `tlq_phiQ_supp hqm hu ξ hc0 hr' hrA' x h)`. Use the proof step `(fun x x' hx hx' hred => by show PhiTopG Ch mu cst.sharp (m2 + 1) (m2 + 1 + 1) (R.N (m2 + 1 + 1)) w.1 _ = PhiTopG Ch mu cst.sharp (m2 + 1) (m2 + 1 + 1) (R.N (m2 + 1 + 1)) w.1 _`. Unfold `PhiTopG`.

Rewrite using `[if_neg hw]`. Conclude with `tlq_phiQ_red hqm hu ξ hc0 hr' hrA' x x' hx hx' hred)`. Use the proof step `(fun η => ftY sel mu cst w η y₁)`. Use the proof step `(fun η h => by`. Unfold `ftY at h`.

Rewrite `h` using `[if_neg hw]`. Use `split_ifs at h with hI`. Conclude with `hI`. Conclude with `absurd rfl h)`. Use the proof step `(fun η δ hδ' => ftY_pert_qM sel mu cst hcst w hw hD2 η δ y₁ hδ' hq1)`.

Use the proof step `(g : Sp X.E (R.N (m2 + 1 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1 + 1))) hK hK' γ hγI hγ y`. Establish `hphi : PhiTopG Ch mu cst.sharp (m2 + 1) (m2 + 1 + 1) (R.N (m2 + 1 + 1)) w.1 ((γ.toLinearMap ∘ₗ prXpG X.E (R.N (m2 + 1 + 1)) ∘ₗ y) ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) = xiZ ξ (A.submatrix (Fin.castLE hrA') (Fin.castLE hrA')).det * xiZ ξ ((redMQ w.1 (1 : Sp …`. Unfold `PhiTopG`. Rewrite using `[if_neg hw]`. Conclude with `phiQ_law hqm hu ξ R.k R.r (cOf R (m2 + 1)) (R.N (m2 + 1)) (R.N (m2 + 1 + 1) - 1) hc0 hr' hrA' hf hγI A Ai 1 hγ lA lAi (hf1 ▸ l1) l1 hAA (by rw [hf1, mul_one]) (prXpG X.E (R.N (m2 + 1 + 1)) ∘ₗ y)`.

Establish `hS` using `scal_law ξ hnA hn' hrA hr' A Ai 1 1 lA l1 hAA (mul_one 1)`. Establish `hbrI : Function.Injective (brI (r` using `R.r) hn') := fun a b h => Fin.ext (by`. Use `congrArg Fin.val h` as an intermediate fact. Simplify using `only [brI] at this`. Use the proof step `omega)`.

Rewrite `hS` using `[Matrix.submatrix_one _ (Fin.castLE_injective hr'), Matrix.submatrix_one _ hbrI]`. Simplify using `only [Matrix.det_one, xiZ_one', one_mul, mul_one] at hS`. Unfold `topDat`. Establish `e1 : PhiTopG Ch mu cst.sharp (m2 + 1) (m2 + 1 + 1) (R.N (m2 + 1 + 1)) w.1 (prXpG X.E (R.N (m2 + 1 + 1)) ∘ₗ (κ'.1.symm.toLinearMap ∘ₗ y) ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) * ftY sel mu cst w (atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ (κ'.1.sym …` using `hcore`. Rewrite using `[e1, hs2, hl1, hphi, hf1, Matrix.submatrix_one _ (Fin.castLE_injective hr'), Matrix.det_one, xiZ_one', mul_one, ← hS]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem lastStepDatumLaw_K1Depth_twiceM : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) {m2 : ℕ} (w : rowSG Pr sel mu) (hw : w.1 ∉ Pr.vGs) (κ' : ↥(GLint X.E (R.N (m2 + 1 + 1)) w.1)) (hc' : κ'⁻¹ ∈ (twTt (R := R) sel mu (m2 + 1 + 1) ⟨w.1, (Finset.mem_union.mp w.2).resolve_left hw⟩).H) (y : HomE X.E (R.N (m2 + 1)) (R.N (m2 + 1 + 1))) (y₁ : Sp X.E (R.N (m2 + 1))), R.m = m2 + 2 → cst.Ok → ((qOf w.1 : ℕ) : 𝓞 X.E) ∉ w.1.asIdeal ^ 2 → 2 * cst.M ≤ cst.D w → 2 * cst.M ≤ twTopDepth R → ((qOf w.1 : X.E) ^ cst.M) • y₁ ∈ stdAt X.E (R.N (m2 + 1)) w.1 → rhoT Ch sel mu (m2 + 1) w (LinearEquiv.det κ'.1 : X.Eˣ) * topDat Ch sel mu cst (m2 + 1) w (κ'.1.symm.toLinearMap ∘ₗ y) y₁ = (((twTt (R := R) sel mu (m2 + 1 + 1) ⟨w.1, (Finset.mem_union.mp w.2).resolve_left hw⟩).lam ⟨κ'⁻¹, hc'⟩ : X.Kˣ) : X.K) * topDat Ch sel mu cst (m2 + 1) w y y₁ := by
  intro X Pr R Ch sel S mu cst m2 w hw κ' hc' y y₁ hm hcst hu hD2 hMc hq1
  have hwQ : w.1 ∈ QE sel (mu : Chr X.F X.E X.K) := (Finset.mem_union.mp w.2).resolve_left hw
  have hqm : ((qOf w.1 : ℕ) : 𝓞 X.E) ∈ w.1.asIdeal := qOf_memB w.1
  have hq0 := ciQ_ne_zero hu
  have hM1 : 1 ≤ cst.M := hcst.M_pos
  have hcc : 1 ≤ twTopDepth R := by unfold twTopDepth; omega
  have hNpos := R.N_pos (m2 + 1 + 1)
  have hN : R.N (m2 + 1 + 1) = (R.N (m2 + 1 + 1) - 1) + 1 := by omega
  have hNm : R.N (m2 + 1 + 1) = R.N R.m := by rw [hm]
  have hn' : R.N (m2 + 1) = R.r + (m2 + 1) * R.t := rank_midQ (R := R) hm
  have hr' : R.r ≤ R.N (m2 + 1) := by rw [hn']; exact Nat.le_add_right _ _
  have hnA : R.N (m2 + 1 + 1) - 1 + 0 = R.r + R.m * R.t := by rw [hNm, Nat.add_zero]; exact rank_X'_eq R
  have hrA : R.r ≤ R.N (m2 + 1 + 1) - 1 + 0 := by rw [hnA]; exact Nat.le_add_right _ _
  have hc0 : cOf R (m2 + 1) = 0 := cOf_topB hm
  set ξ := resChar (mu : Chr X.F X.E X.K) w.1 with hξ
  let g : ↥(GLint X.E (R.N (m2 + 1 + 1)) w.1) := κ'⁻¹
  have hK : IsKOneType w.1 (qOf w.1) (twTopDepth R) (g : Sp X.E (R.N (m2 + 1 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1 + 1))) := isKOneType_of_mem_kOne w.1 g hc'
  have hK' : IsKOneType w.1 (qOf w.1) (twTopDepth R) (g : Sp X.E (R.N (m2 + 1 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1 + 1))).symm :=
    isKOneType_symm_of_mem_kOne w.1 g hc'
  obtain ⟨⟨hAA, hAA'⟩, ⟨-, hdetAi⟩, hD⟩ := kOneType_block_matrix hqm hq0 hN hcc _ hK hK'
  set A : Matrix (Fin (R.N (m2 + 1 + 1) - 1 + 0)) (Fin (R.N (m2 + 1 + 1) - 1 + 0)) (𝓞 X.E ⧸ w.1.asIdeal) :=
    Matrix.of fun i j => redP w.1 ((g : Sp X.E (R.N (m2 + 1 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1 + 1))) (Pi.single ⟨j.1, by omega⟩ 1) ⟨i.1, by omega⟩)
    with hAdef
  set Ai : Matrix (Fin (R.N (m2 + 1 + 1) - 1 + 0)) (Fin (R.N (m2 + 1 + 1) - 1 + 0)) (𝓞 X.E ⧸ w.1.asIdeal) :=
    Matrix.of fun i j => redP w.1 ((g : Sp X.E (R.N (m2 + 1 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1 + 1))).symm (Pi.single ⟨j.1, by omega⟩ 1) ⟨i.1, by omega⟩)
    with hAidef
  let AG : GL (Fin (R.N (m2 + 1 + 1) - 1 + 0)) (𝓞 X.E ⧸ w.1.asIdeal) := ⟨A, Ai, hAA', hAA⟩
  have hLLz : LLz R.r (redMQ w.1 (g : Sp X.E (R.N (m2 + 1 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1 + 1))).toLinearMap) :=
    jq_LLz (n := R.N (m2 + 1 + 1)) (c := 0) (g := (g : Sp X.E (R.N (m2 + 1 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1 + 1))))
      (rr := (g : Sp X.E (R.N (m2 + 1 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1 + 1)))) hqm hq0 hc'.1 (fun x => by rw [tlq_inX_zero, tlq_inX_zero])
  have hLLzi : LLz R.r (redMQ w.1 (g : Sp X.E (R.N (m2 + 1 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1 + 1))).symm.toLinearMap) :=
    jq_LLz (n := R.N (m2 + 1 + 1)) (c := 0) (g := (g : Sp X.E (R.N (m2 + 1 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1 + 1))).symm)
      (rr := (g : Sp X.E (R.N (m2 + 1 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1 + 1))).symm) hqm hq0
      ((twK1H w.1 _ _ _).inv_mem hc').1 (fun x => by rw [tlq_inX_zero, tlq_inX_zero])
  have lA : LLz R.r A := fun i j hi hj => hLLz ⟨i.1, by omega⟩ ⟨j.1, by omega⟩ hi hj
  have lAi : LLz R.r Ai := fun i j hi hj => hLLzi ⟨i.1, by omega⟩ ⟨j.1, by omega⟩ hi hj
  obtain ⟨γ, hγI, hγ, -⟩ := ctl_lift (P := w.1) AG
  have hrA' : R.r ≤ R.N (m2 + 1 + 1) - 1 := hrA
  have hs2 : rhoT Ch sel mu (m2 + 1) w (LinearEquiv.det κ'.1 : X.Eˣ) = xiZ ξ Ai.det := by
    unfold rhoT
    rw [if_neg hw, unitV_eq, redP_detEquiv w.1 κ'.2]
    exact congrArg (xiZ ξ) hdetAi
  have hnD : R.N (m2 + 1 + 1) = R.r + (R.m * R.t + 1) := by omega
  have hl1 : (((twTt (R := R) sel mu (m2 + 1 + 1) ⟨w.1, hwQ⟩).lam ⟨κ'⁻¹, hc'⟩ : X.Kˣ) : X.K) =
      (xiZ ξ (A.submatrix (brI hnA) (brI hnA)).det)⁻¹ := by
    show LocE.lamQB ξ R.r (R.N (m2 + 1 + 1)) (g : Sp X.E (R.N (m2 + 1 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1 + 1))).toLinearMap = _
    have e := lamQB_eq (P := w.1) ξ (kj := R.r) (r := R.r) (n := R.N (m2 + 1 + 1)) (c := 0) (d := R.m * R.t + 1) rfl hnD g.2
      (rr := (g : Sp X.E (R.N (m2 + 1 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1 + 1)))) (fun x => by rw [tlq_inX_zero, tlq_inX_zero])
    rw [e, hD R.r (R.m * R.t) hnA]

  have hf : (1 : Sp X.E (R.N (m2 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1))) ∈ GLint X.E (R.N (m2 + 1)) w.1 := Subgroup.one_mem _
  have hf1 := redMQ_idEquiv w.1 (R.N (m2 + 1))
  have l1 : LLz R.r (1 : Matrix (Fin (R.N (m2 + 1))) (Fin (R.N (m2 + 1))) (𝓞 X.E ⧸ w.1.asIdeal)) := fun i j hi hj =>
    Matrix.one_apply_ne (fun h => by rw [h] at hi; omega)
  have hcore := residueClassProduct_invariant_K1Depth_twiceM (E := X.E) (K := X.K) (P := w.1) (q := qOf w.1) hqm hq0 (n' := R.N (m2 + 1)) (N := R.N (m2 + 1 + 1))
    (M := cst.M) (cc := twTopDepth R) (by omega) hM1 hMc
    (fun x => PhiTopG Ch mu cst.sharp (m2 + 1) (m2 + 1 + 1) (R.N (m2 + 1 + 1)) w.1 (x ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))))
    (fun x h => by
      unfold PhiTopG at h
      (try rw [if_neg hw] at h)
      exact tlq_phiQ_supp hqm hu ξ hc0 hr' hrA' x h)
    (fun x x' hx hx' hred => by
      show PhiTopG Ch mu cst.sharp (m2 + 1) (m2 + 1 + 1) (R.N (m2 + 1 + 1)) w.1 _ = PhiTopG Ch mu cst.sharp (m2 + 1) (m2 + 1 + 1) (R.N (m2 + 1 + 1)) w.1 _
      unfold PhiTopG
      rw [if_neg hw]
      exact tlq_phiQ_red hqm hu ξ hc0 hr' hrA' x x' hx hx' hred)
    (fun η => ftY sel mu cst w η y₁)
    (fun η h => by
      unfold ftY at h
      rw [if_neg hw] at h
      split_ifs at h with hI
      · exact hI
      · exact absurd rfl h)
    (fun η δ hδ' => ftY_pert_qM sel mu cst hcst w hw hD2 η δ y₁ hδ' hq1)
    (g : Sp X.E (R.N (m2 + 1 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1 + 1))) hK hK' γ hγI hγ y
  have hphi : PhiTopG Ch mu cst.sharp (m2 + 1) (m2 + 1 + 1) (R.N (m2 + 1 + 1)) w.1
      ((γ.toLinearMap ∘ₗ prXpG X.E (R.N (m2 + 1 + 1)) ∘ₗ y) ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) =
      xiZ ξ (A.submatrix (Fin.castLE hrA') (Fin.castLE hrA')).det *
        xiZ ξ ((redMQ w.1 (1 : Sp X.E (R.N (m2 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1))).toLinearMap).submatrix (Fin.castLE hr') (Fin.castLE hr')).det *
        PhiTopG Ch mu cst.sharp (m2 + 1) (m2 + 1 + 1) (R.N (m2 + 1 + 1)) w.1
          (prXpG X.E (R.N (m2 + 1 + 1)) ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) := by
    unfold PhiTopG
    rw [if_neg hw]
    exact phiQ_law hqm hu ξ R.k R.r (cOf R (m2 + 1)) (R.N (m2 + 1)) (R.N (m2 + 1 + 1) - 1) hc0 hr' hrA' hf hγI A Ai
      1 hγ lA lAi (hf1 ▸ l1) l1 hAA (by rw [hf1, mul_one]) (prXpG X.E (R.N (m2 + 1 + 1)) ∘ₗ y)
  have hS := scal_law ξ hnA hn' hrA hr' A Ai 1 1 lA l1 hAA (mul_one 1)
  have hbrI : Function.Injective (brI (r := R.r) hn') := fun a b h => Fin.ext (by
    have := congrArg Fin.val h
    simp only [brI] at this
    omega)
  rw [Matrix.submatrix_one _ (Fin.castLE_injective hr'), Matrix.submatrix_one _ hbrI] at hS
  simp only [Matrix.det_one, xiZ_one', one_mul, mul_one] at hS
  unfold topDat
  have e1 : PhiTopG Ch mu cst.sharp (m2 + 1) (m2 + 1 + 1) (R.N (m2 + 1 + 1)) w.1
        (prXpG X.E (R.N (m2 + 1 + 1)) ∘ₗ (κ'.1.symm.toLinearMap ∘ₗ y) ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) *
      ftY sel mu cst w (atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ (κ'.1.symm.toLinearMap ∘ₗ y)) y₁ =
      PhiTopG Ch mu cst.sharp (m2 + 1) (m2 + 1 + 1) (R.N (m2 + 1 + 1)) w.1
        ((γ.toLinearMap ∘ₗ prXpG X.E (R.N (m2 + 1 + 1)) ∘ₗ y) ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) *
      ftY sel mu cst w (atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ y) y₁ :=
    hcore
  rw [e1, hs2, hl1, hphi, hf1, Matrix.submatrix_one _ (Fin.castLE_injective hr'), Matrix.det_one, xiZ_one', mul_one, ← hS]
  ring

end GlobalTheory
