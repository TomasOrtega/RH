import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.GL3.PLinkThIndep
import Formalism.LocalToGlobal.GlobalTheory.GL3.PLinkThU

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.DN

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Matrix

variable (D : D7)

def vol {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) : IdE D :=
  Submodule.span (𝓞 D.host.E)
    {x | ∃ U : Matrix (Fin N) (Fin N) D.host.E, (∀ j, (fun i => U i j) ∈ L) ∧ x = U.det}

/- English proof (translation)
Use function extensionality and compare the values at `i`. Use `first`. Consider the case `rfl`. Consider the case `simp [Matrix.mulVec, Matrix.mul_apply, dotProduct]`.
-/
theorem mulVec_col {N : ℕ} (A U : Matrix (Fin N) (Fin N) D.host.E) (j : Fin N) :
    A *ᵥ (fun i => U i j) = fun i => (A * U) i j := by
  funext i
  first
  | rfl
  | simp [Matrix.mulVec, Matrix.mul_apply, dotProduct]

/- English proof (translation)
Unfold `detId vol`. Rewrite using `[Submodule.span_mul_span]`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, ⟨A, hA, rfl⟩, y, ⟨U, hU, rfl⟩, rfl⟩`. Use `Submodule.subset_span ⟨A * U, fun j => ?_, (Matrix.det_mul A U).symm⟩` and prove the remaining obligations.

Establish `h` using `hA _ (hU j)`. Rewrite `h` using `[mulVec_col]`. Then use the resulting hypothesis.
-/
theorem detId_mul_vol_le {N : ℕ} (L L' : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) :
    detId D L L' * vol D L ≤ vol D L' := by
  unfold detId vol
  rw [Submodule.span_mul_span]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨x, ⟨A, hA, rfl⟩, y, ⟨U, hU, rfl⟩, rfl⟩
  refine Submodule.subset_span ⟨A * U, fun j => ?_, (Matrix.det_mul A U).symm⟩
  have h := hA _ (hU j)
  rwa [mulVec_col] at h

/- English proof (translation)
Introduce `x hx`. Establish `hx' : D.host.conj x ∈ Submodule.span (𝓞 D.host.E) S` using `hx`. Establish `key : ∀ y ∈ Submodule.span (𝓞 D.host.E) S, D.host.conj y ∈ Submodule.span (𝓞 D.host.E) (D.host.conj '' S)`. Introduce `y hy`. Proceed by induction on `hy using Submodule.span_induction with`.

Consider the case `mem z hz => exact Submodule.subset_span ⟨z, hz, rfl⟩`. Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => rw [map_add]`. Conclude with `Submodule.add_mem _ ha hb`. Consider the case `smul r a _ ha => rw [CU.conj_smul]`.

Conclude with `Submodule.smul_mem _ _ ha`. Establish `h` using `key _ hx'`. Rewrite `h` using `[Formalism.HC.HostRaw.conj_conj]`. Then use the resulting hypothesis.
-/
theorem cS_span_le (S : Set D.host.E) :
    CU.cS D (Submodule.span (𝓞 D.host.E) S) ≤ Submodule.span (𝓞 D.host.E) (D.host.conj '' S) := by
  intro x hx
  have hx' : D.host.conj x ∈ Submodule.span (𝓞 D.host.E) S := hx
  have key : ∀ y ∈ Submodule.span (𝓞 D.host.E) S,
      D.host.conj y ∈ Submodule.span (𝓞 D.host.E) (D.host.conj '' S) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz => exact Submodule.subset_span ⟨z, hz, rfl⟩
    | zero => simp
    | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | smul r a _ ha => rw [CU.conj_smul]; exact Submodule.smul_mem _ _ ha
  have h := key _ hx'
  rwa [Formalism.HC.HostRaw.conj_conj] at h

/- English proof (translation)
Use extensionality with `x`. Use `show D.host.conj (D.host.conj x) ∈ 𝔞 ↔ x ∈ 𝔞`. Rewrite using `[Formalism.HC.HostRaw.conj_conj]`.
-/
theorem cS_cS (𝔞 : IdE D) : CU.cS D (CU.cS D 𝔞) = 𝔞 := by
  ext x
  show D.host.conj (D.host.conj x) ∈ 𝔞 ↔ x ∈ 𝔞
  rw [Formalism.HC.HostRaw.conj_conj]

/- English proof (translation)
Set `_` to `D.host.cmStar`. Use `(mul_le_mul' (le_refl _) (cS_span_le D _)).trans ?_` and prove the remaining obligations. Unfold `vol detId`. Rewrite using `[Submodule.span_mul_span, Submodule.span_le]`. Introduce and unpack `_ ⟨_, ⟨V, hV, rfl⟩, _, ⟨_, ⟨W, hW, rfl⟩, rfl⟩, rfl⟩`.

Use `Submodule.subset_span ⟨V * Wᴴ, fun x hx => ?_, ?_⟩` and prove the remaining obligations. Establish `hc : ∀ i, ∃ r : 𝓞 D.host.E, algebraMap _ _ r = (Wᴴ *ᵥ x) i`. Introduce `i`. Take `⟨r, hr⟩` from `hL x hx _ (hW i)`. Use `⟨r, hr.trans ?_⟩` and prove the remaining obligations.

Simplify using `[stdH, Matrix.mulVec, dotProduct, conjTranspose_apply]`. Use `choose r hr using hc`. Establish `e : (V * Wᴴ) *ᵥ x = ∑ i, r i • (fun k => V k i)`. Rewrite using `[← mulVec_mulVec]`. Use function extensionality and compare the values at `k`.

Simplify using `only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, Algebra.smul_def]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hr i, mul_comm]`. Both sides reduce to the same expression. Rewrite using `[e]`.

Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hV i)`. Rewrite using `[det_mul, det_conjTranspose, CU.star_conj]`.
-/
theorem vol_mul_cS_le {N : ℕ} (L L' : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (hL : letI := D.host.cmStar; ∀ x ∈ L, ∀ w ∈ L,
      stdH D.host.E N w x ∈ (algebraMap (𝓞 D.host.E) D.host.E).range) :
    vol D L' * CU.cS D (vol D L) ≤ detId D L L' := by
  let _ := D.host.cmStar
  refine (mul_le_mul' (le_refl _) (cS_span_le D _)).trans ?_
  unfold vol detId
  rw [Submodule.span_mul_span, Submodule.span_le]
  rintro _ ⟨_, ⟨V, hV, rfl⟩, _, ⟨_, ⟨W, hW, rfl⟩, rfl⟩, rfl⟩
  refine Submodule.subset_span ⟨V * Wᴴ, fun x hx => ?_, ?_⟩
  · have hc : ∀ i, ∃ r : 𝓞 D.host.E, algebraMap _ _ r = (Wᴴ *ᵥ x) i := by
      intro i
      obtain ⟨r, hr⟩ := hL x hx _ (hW i)
      refine ⟨r, hr.trans ?_⟩
      simp [stdH, Matrix.mulVec, dotProduct, conjTranspose_apply]
    choose r hr using hc
    have e : (V * Wᴴ) *ᵥ x = ∑ i, r i • (fun k => V k i) := by
      rw [← mulVec_mulVec]
      funext k
      simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, Algebra.smul_def]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hr i, mul_comm]
      rfl
    rw [e]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hV i)
  · rw [det_mul, det_conjTranspose, CU.star_conj]

/- English proof (translation)
Set `_` to `D.host.cmStar`. Use `(mul_le_mul' (le_refl _) (cS_span_le D _)).trans ?_` and prove the remaining obligations. Unfold `vol`. Rewrite using `[Submodule.span_mul_span, Submodule.span_le]`. Introduce and unpack `_ ⟨_, ⟨V, hV, rfl⟩, _, ⟨_, ⟨W, hW, rfl⟩, rfl⟩, rfl⟩`.

Establish `hc : ∀ i j, ∃ r : 𝓞 D.host.E, algebraMap _ _ r = (Wᴴ * V) i j`. Introduce `i j`. Take `⟨r, hr⟩` from `hL _ (hV j) _ (hW i)`. Use `⟨r, hr.trans ?_⟩` and prove the remaining obligations. Simplify using `[stdH, Matrix.mul_apply, conjTranspose_apply]`.

Use `choose r hr using hc`. Establish `e : Wᴴ * V = (Matrix.of r).map (algebraMap (𝓞 D.host.E) D.host.E)`. Use extensionality with `i j`. Simplify using `[hr]`. Use `show _ ∈ (1 : IdE D)`.

Rewrite using `[Submodule.mem_one, ← CU.star_conj, ← det_conjTranspose]`. Use `⟨(Matrix.of r).det, ?_⟩` and prove the remaining obligations. Establish `h2 : algebraMap (𝓞 D.host.E) D.host.E (Matrix.of r).det = (Wᴴ * V).det`. Rewrite using `[e, RingHom.map_det]`. Both sides reduce to the same expression.

Rewrite using `[h2, det_mul]`. Conclude with `mul_comm _ _`.
-/
theorem vol_mul_cS_le_one {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (hL : letI := D.host.cmStar; ∀ x ∈ L, ∀ w ∈ L,
      stdH D.host.E N w x ∈ (algebraMap (𝓞 D.host.E) D.host.E).range) :
    vol D L * CU.cS D (vol D L) ≤ 1 := by
  let _ := D.host.cmStar
  refine (mul_le_mul' (le_refl _) (cS_span_le D _)).trans ?_
  unfold vol
  rw [Submodule.span_mul_span, Submodule.span_le]
  rintro _ ⟨_, ⟨V, hV, rfl⟩, _, ⟨_, ⟨W, hW, rfl⟩, rfl⟩, rfl⟩
  have hc : ∀ i j, ∃ r : 𝓞 D.host.E, algebraMap _ _ r = (Wᴴ * V) i j := by
    intro i j
    obtain ⟨r, hr⟩ := hL _ (hV j) _ (hW i)
    refine ⟨r, hr.trans ?_⟩
    simp [stdH, Matrix.mul_apply, conjTranspose_apply]
  choose r hr using hc
  have e : Wᴴ * V = (Matrix.of r).map (algebraMap (𝓞 D.host.E) D.host.E) := by
    ext i j; simp [hr]
  show _ ∈ (1 : IdE D)
  rw [Submodule.mem_one, ← CU.star_conj, ← det_conjTranspose]
  refine ⟨(Matrix.of r).det, ?_⟩
  have h2 : algebraMap (𝓞 D.host.E) D.host.E (Matrix.of r).det = (Wᴴ * V).det := by
    rw [e, RingHom.map_det]; rfl
  rw [h2, det_mul]
  exact mul_comm _ _

/- English proof (translation)
Introduce `x hx w hw`. Conclude with `(hL.2.2 x).1 hx w hw`.
-/
theorem sd_int {N : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    (hL : letI := D.host.cmStar; IsSDLat D.host.E N L) :
    letI := D.host.cmStar; ∀ x ∈ L, ∀ w ∈ L,
      stdH D.host.E N w x ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
  intro x hx w hw
  exact (hL.2.2 x).1 hx w hw

def UnitDisc (D : D7) : Prop :=
  let _ := D.host.cmStar
  ∀ N (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)), IsSDLat D.host.E N L →
    1 ≤ vol D L * CU.cS D (vol D L)

/- English proof (translation)
Introduce `N L L' _ hL hL'`. Establish `mulc : ∀ 𝔞 𝔟 : IdE D, CU.cS D 𝔞 * CU.cS D 𝔟 ≤ CU.cS D (𝔞 * 𝔟)`. Introduce `𝔞 𝔟`. Use `Submodule.mul_le.2 fun x hx y hy => ?_` and prove the remaining obligations. Use `show D.host.conj (x * y) ∈ 𝔞 * 𝔟`.

Rewrite using `[map_mul]`. Conclude with `Submodule.mul_mem_mul hx hy`. Establish `mono : ∀ 𝔞 𝔟 : IdE D, 𝔞 ≤ 𝔟 → CU.cS D 𝔞 ≤ CU.cS D 𝔟` using `fun 𝔞 𝔟 h x hx => h hx`. Establish `mm : ∀ a b c d : IdE D, a ≤ b → c ≤ d → a * c ≤ b * d` using `fun a b c d h h' => Submodule.mul_le.2 fun x hx y hy => Submodule.mul_mem_mul (h hx) (h' hy)`. Establish `h1 : 1 ≤ vol D L * CU.cS D (vol D L)` using `hU N L hL`.

Establish `h1' : 1 ≤ vol D L' * CU.cS D (vol D L')` using `hU N L' hL'`. Establish `h2 : vol D L' * CU.cS D (vol D L') ≤ 1` using `vol_mul_cS_le_one D L' (sd_int D hL')`. Establish `h3 : vol D L' * CU.cS D (vol D L) ≤ detId D L L'` using `vol_mul_cS_le D L L' (sd_int D hL)`. Establish `h4 : detId D L L' * vol D L ≤ vol D L'` using `detId_mul_vol_le D L L'`. Use `⟨CU.cS D (detId D L L'), fun x => Iff.rfl, le_antisymm ?_ ?_⟩` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[cS_cS]`. Use `_ ≤ (vol D L' * CU.cS D (vol D L)) * CU.cS D (vol D L' * CU.cS D (vol D L)) := mm _ _ _ _ le_rfl (mulc _ _)`. Use `_ ≤ detId D L L' * CU.cS D (detId D L L') := mm _ _ _ _ h3 (mono _ _ h3)`.
-/
theorem determinant_norm_one_of_unit_disc (hU : UnitDisc D) : DetIdealsKernelNormOne D := by
  intro N L L' _ hL hL'
  have mulc : ∀ 𝔞 𝔟 : IdE D, CU.cS D 𝔞 * CU.cS D 𝔟 ≤ CU.cS D (𝔞 * 𝔟) := by
    intro 𝔞 𝔟
    refine Submodule.mul_le.2 fun x hx y hy => ?_
    show D.host.conj (x * y) ∈ 𝔞 * 𝔟
    rw [map_mul]
    exact Submodule.mul_mem_mul hx hy
  have mono : ∀ 𝔞 𝔟 : IdE D, 𝔞 ≤ 𝔟 → CU.cS D 𝔞 ≤ CU.cS D 𝔟 := fun 𝔞 𝔟 h x hx => h hx
  have mm : ∀ a b c d : IdE D, a ≤ b → c ≤ d → a * c ≤ b * d := fun a b c d h h' =>
    Submodule.mul_le.2 fun x hx y hy => Submodule.mul_mem_mul (h hx) (h' hy)
  have h1 : 1 ≤ vol D L * CU.cS D (vol D L) := hU N L hL
  have h1' : 1 ≤ vol D L' * CU.cS D (vol D L') := hU N L' hL'
  have h2 : vol D L' * CU.cS D (vol D L') ≤ 1 := vol_mul_cS_le_one D L' (sd_int D hL')
  have h3 : vol D L' * CU.cS D (vol D L) ≤ detId D L L' := vol_mul_cS_le D L L' (sd_int D hL)
  have h4 : detId D L L' * vol D L ≤ vol D L' := detId_mul_vol_le D L L'
  refine ⟨CU.cS D (detId D L L'), fun x => Iff.rfl, le_antisymm ?_ ?_⟩
  · calc detId D L L' * CU.cS D (detId D L L')
          = detId D L L' * CU.cS D (detId D L L') * 1 := (mul_one _).symm
      _ ≤ detId D L L' * CU.cS D (detId D L L') * (vol D L * CU.cS D (vol D L)) :=
          mm _ _ _ _ le_rfl h1
      _ = (detId D L L' * vol D L) * (CU.cS D (detId D L L') * CU.cS D (vol D L)) := by ring
      _ ≤ vol D L' * CU.cS D (detId D L L' * vol D L) := mm _ _ _ _ h4 (mulc _ _)
      _ ≤ vol D L' * CU.cS D (vol D L') := mm _ _ _ _ le_rfl (mono _ _ h4)
      _ ≤ 1 := h2
  · calc (1 : IdE D) = 1 * 1 := (mul_one _).symm
      _ ≤ (vol D L' * CU.cS D (vol D L')) * (vol D L * CU.cS D (vol D L)) :=
          mm _ _ _ _ h1' h1
      _ = (vol D L' * CU.cS D (vol D L)) * (CU.cS D (vol D L') * vol D L) := by ring
      _ = (vol D L' * CU.cS D (vol D L)) * (CU.cS D (vol D L') * CU.cS D (CU.cS D (vol D L))) := by
          rw [cS_cS]
      _ ≤ (vol D L' * CU.cS D (vol D L)) * CU.cS D (vol D L' * CU.cS D (vol D L)) :=
          mm _ _ _ _ le_rfl (mulc _ _)
      _ ≤ detId D L L' * CU.cS D (detId D L L') := mm _ _ _ _ h3 (mono _ _ h3)

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.DN

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.DN

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Matrix

variable (D : D7)

/- English proof (translation)
Set `_` to `D.host.cmStar`. Use `Submodule.subset_span ⟨(adjugate U)ᴴ * diagonal t, fun i => ?_, ?_⟩` and prove the remaining obligations. Use `(hL.2.2 _).2 fun x hx => ?_` and prove the remaining obligations. Establish `hdet : (U.updateCol i x).det ∈ vol D L`. Use `Submodule.subset_span ⟨U.updateCol i x, fun j => ?_, rfl⟩` and prove the remaining obligations.

Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Use `hx using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`. Simplify using the standard rewrite rules.

Use `hU j using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`. Simplify using `[hj]`. Establish `hb : star (U.updateCol i x).det ∈ CU.cS D (vol D L)`. Rewrite using `[CU.mem_cS, ← CU.star_conj, star_star]`.

Conclude with `hdet`. Take `⟨r, hr⟩` from `Submodule.mem_one.mp (ht i _ hb)`. Use `⟨r, hr.trans ?_⟩` and prove the remaining obligations. Rewrite using `[← cramer_apply, cramer_eq_adjugate_mulVec]`. Simplify using `only [stdH, Matrix.mulVec, dotProduct, star_sum, star_mul, mul_diagonal, conjTranspose_apply, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[det_mul, det_diagonal, det_conjTranspose, det_adjugate, Fintype.card_fin, star_pow, CU.star_conj]`.
-/
theorem adj_step {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (hL : letI := D.host.cmStar; IsSDLat D.host.E N L)
    (U : Matrix (Fin N) (Fin N) D.host.E) (hU : ∀ j, (fun i => U i j) ∈ L) (t : Fin N → D.host.E)
    (ht : ∀ i, ∀ b ∈ CU.cS D (vol D L), t i * b ∈ (1 : IdE D)) :
    D.host.conj U.det ^ (N - 1) * ∏ i, t i ∈ vol D L := by
  let _ := D.host.cmStar
  refine Submodule.subset_span ⟨(adjugate U)ᴴ * diagonal t, fun i => ?_, ?_⟩
  · refine (hL.2.2 _).2 fun x hx => ?_
    have hdet : (U.updateCol i x).det ∈ vol D L := by
      refine Submodule.subset_span ⟨U.updateCol i x, fun j => ?_, rfl⟩
      by_cases hj : j = i
      · subst hj; convert hx using 1; funext k; simp
      · convert hU j using 1; funext k; simp [hj]
    have hb : star (U.updateCol i x).det ∈ CU.cS D (vol D L) := by
      rw [CU.mem_cS, ← CU.star_conj, star_star]; exact hdet
    obtain ⟨r, hr⟩ := Submodule.mem_one.mp (ht i _ hb)
    refine ⟨r, hr.trans ?_⟩
    rw [← cramer_apply, cramer_eq_adjugate_mulVec]
    simp only [stdH, Matrix.mulVec, dotProduct, star_sum, star_mul, mul_diagonal,
      conjTranspose_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  · rw [det_mul, det_diagonal, det_conjTranspose, det_adjugate, Fintype.card_fin, star_pow,
      CU.star_conj]

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.DN

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.DN

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Matrix nonZeroDivisors

open FractionalIdeal in

/- English proof (translation)
Establish `mmR : ∀ A B C : FractionalIdeal R⁰ K, A ≤ B → A * C ≤ B * C`. Introduce `A B C h`. Rewrite using `[← FractionalIdeal.coe_le_coe, FractionalIdeal.coe_mul, FractionalIdeal.coe_mul]`. Conclude with `Submodule.mul_le.2 fun x hx y hy => Submodule.mul_mem_mul (FractionalIdeal.coe_le_coe.2 h hx) hy`. Establish `hJle : Submodule.span R ((fun s => s ^ k) '' S) ≤ ((I ^ k : FractionalIdeal R⁰ K) : Submodule R K)`.

Rewrite using `[FractionalIdeal.coe_pow, Submodule.span_le]`. Introduce and unpack `_ ⟨s, hs, rfl⟩`. Establish `hsI : s ∈ (I : Submodule R K)`. Rewrite using `[hIS]`. Conclude with `Submodule.subset_span hs`.

Use `first`. Consider the case `exact Submodule.pow_mem_pow hsI k`. Consider the case `exact Submodule.pow_mem_pow _ hsI k`. Set `J : FractionalIdeal R⁰ K` to `⟨_, FractionalIdeal.isFractional_of_le hJle⟩`. Establish `hJ : (J : Submodule R K) = Submodule.span R ((fun s => s ^ k) '' S)` using `rfl`.

Rewrite using `[← hJ, ← FractionalIdeal.coe_pow, FractionalIdeal.coe_le_coe]`. Establish `hIk : I ^ k ≠ 0` using `pow_ne_zero _ hI`. Establish `hJIk : J ≤ I ^ k` using `hJle`. Establish `hC1 : J * (I ^ k)⁻¹ ≤ 1`. Combine the equalities or inequalities in the displayed calculation.

Distinguish the cases in `h1 : J * (I ^ k)⁻¹ = 1`. Use `le_of_eq ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. It suffices to derive a contradiction. Take `⟨𝔠, h𝔠⟩` from `FractionalIdeal.le_one_iff_exists_coeIdeal.1 hC1`.

Establish `h𝔠top : 𝔠 ≠ ⊤`. Introduce and unpack `rfl`. Apply `h1` to reduce the goal to its premises. Rewrite using `[← h𝔠, FractionalIdeal.coeIdeal_top]`. Take `⟨P, hPmax, hcP⟩` from `Ideal.exists_le_maximal 𝔠 h𝔠top`.

Use `haveI := hPmax.isPrime`. Establish `key : ∀ s ∈ S, FractionalIdeal.spanSingleton R⁰ s ≤ (P : FractionalIdeal R⁰ K) * I`. Introduce `s hs`. Establish `hsI : FractionalIdeal.spanSingleton R⁰ s ≤ I`. Rewrite using `[FractionalIdeal.spanSingleton_le_iff_mem, ← FractionalIdeal.mem_coe, hIS]`.

Conclude with `Submodule.subset_span hs`. Establish `hA1 : FractionalIdeal.spanSingleton R⁰ s * I⁻¹ ≤ 1`. Combine the equalities or inequalities in the displayed calculation. Take `⟨a, ha⟩` from `FractionalIdeal.le_one_iff_exists_coeIdeal.1 hA1`. Establish `hak : a ^ k ≤ P`.

Establish `h2 : ((a ^ k : Ideal R) : FractionalIdeal R⁰ K) ≤ (𝔠 : FractionalIdeal R⁰ K)`. Rewrite using `[FractionalIdeal.coeIdeal_pow, ha, h𝔠, mul_pow, FractionalIdeal.spanSingleton_pow, inv_pow]`. Use `mmR _ _ _ ?_` and prove the remaining obligations. Rewrite using `[FractionalIdeal.spanSingleton_le_iff_mem, ← FractionalIdeal.mem_coe]`. Conclude with `Submodule.subset_span ⟨s, hs, rfl⟩`.

Conclude with `le_trans ((FractionalIdeal.coeIdeal_le_coeIdeal K).1 h2) hcP`. Establish `haP : a ≤ P` using `by first`. Consider the case `exact Ideal.IsPrime.le_of_pow_le hak`. Consider the case `exact hPmax.isPrime.le_of_pow_le hak`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[mul_assoc, inv_mul_cancel₀ hI, mul_one]`. Use `_ = (a : FractionalIdeal R⁰ K) * I := by rw [ha]`. Use `_ ≤ (P : FractionalIdeal R⁰ K) * I := mmR _ _ _ ((FractionalIdeal.coeIdeal_le_coeIdeal K).2 haP)`. Establish `hIle : I ≤ (P : FractionalIdeal R⁰ K) * I`. Rewrite using `[← FractionalIdeal.coe_le_coe, hIS, Submodule.span_le]`.

Introduce `s hs`. Conclude with `FractionalIdeal.spanSingleton_le_iff_mem.1 (key s hs)`. Establish `hPI : (P : FractionalIdeal R⁰ K) * I ≤ I`. Combine the equalities or inequalities in the displayed calculation. Establish `heq : (P : FractionalIdeal R⁰ K) * I = 1 * I`.

Rewrite using `[one_mul]`. Conclude with `le_antisymm hPI hIle`. Establish `hP1 : (P : FractionalIdeal R⁰ K) = 1` using `mul_right_cancel₀ hI heq`. Rewrite `hP1` using `[FractionalIdeal.coeIdeal_eq_one]`. Conclude with `hPmax.ne_top (hP1.trans Ideal.one_eq_top)`.
-/
theorem spanPow {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (I : FractionalIdeal R⁰ K) (hI : I ≠ 0) (S : Set K)
    (hIS : (I : Submodule R K) = Submodule.span R S) (k : ℕ) :
    (I : Submodule R K) ^ k ≤ Submodule.span R ((fun s => s ^ k) '' S) := by
  have mmR : ∀ A B C : FractionalIdeal R⁰ K, A ≤ B → A * C ≤ B * C := by
    intro A B C h
    rw [← FractionalIdeal.coe_le_coe, FractionalIdeal.coe_mul, FractionalIdeal.coe_mul]
    exact Submodule.mul_le.2 fun x hx y hy =>
      Submodule.mul_mem_mul (FractionalIdeal.coe_le_coe.2 h hx) hy
  have hJle : Submodule.span R ((fun s => s ^ k) '' S) ≤
      ((I ^ k : FractionalIdeal R⁰ K) : Submodule R K) := by
    rw [FractionalIdeal.coe_pow, Submodule.span_le]
    rintro _ ⟨s, hs, rfl⟩
    have hsI : s ∈ (I : Submodule R K) := by
      rw [hIS]
      exact Submodule.subset_span hs
    first
    | exact Submodule.pow_mem_pow hsI k
    | exact Submodule.pow_mem_pow _ hsI k
  let J : FractionalIdeal R⁰ K := ⟨_, FractionalIdeal.isFractional_of_le hJle⟩
  have hJ : (J : Submodule R K) = Submodule.span R ((fun s => s ^ k) '' S) := rfl
  rw [← hJ, ← FractionalIdeal.coe_pow, FractionalIdeal.coe_le_coe]
  have hIk : I ^ k ≠ 0 := pow_ne_zero _ hI
  have hJIk : J ≤ I ^ k := hJle
  have hC1 : J * (I ^ k)⁻¹ ≤ 1 := by
    calc J * (I ^ k)⁻¹ ≤ I ^ k * (I ^ k)⁻¹ := mmR _ _ _ hJIk
      _ = 1 := mul_inv_cancel₀ hIk
  by_cases h1 : J * (I ^ k)⁻¹ = 1
  · refine le_of_eq ?_
    calc I ^ k = J * (I ^ k)⁻¹ * I ^ k := by rw [h1, one_mul]
      _ = J := by rw [mul_assoc, inv_mul_cancel₀ hIk, mul_one]
  · exfalso
    obtain ⟨𝔠, h𝔠⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 hC1
    have h𝔠top : 𝔠 ≠ ⊤ := by
      rintro rfl
      apply h1
      rw [← h𝔠, FractionalIdeal.coeIdeal_top]
    obtain ⟨P, hPmax, hcP⟩ := Ideal.exists_le_maximal 𝔠 h𝔠top
    haveI := hPmax.isPrime
    have key : ∀ s ∈ S, FractionalIdeal.spanSingleton R⁰ s ≤ (P : FractionalIdeal R⁰ K) * I := by
      intro s hs
      have hsI : FractionalIdeal.spanSingleton R⁰ s ≤ I := by
        rw [FractionalIdeal.spanSingleton_le_iff_mem, ← FractionalIdeal.mem_coe, hIS]
        exact Submodule.subset_span hs
      have hA1 : FractionalIdeal.spanSingleton R⁰ s * I⁻¹ ≤ 1 := by
        calc FractionalIdeal.spanSingleton R⁰ s * I⁻¹ ≤ I * I⁻¹ := mmR _ _ _ hsI
          _ = 1 := mul_inv_cancel₀ hI
      obtain ⟨a, ha⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 hA1
      have hak : a ^ k ≤ P := by
        have h2 : ((a ^ k : Ideal R) : FractionalIdeal R⁰ K) ≤ (𝔠 : FractionalIdeal R⁰ K) := by
          rw [FractionalIdeal.coeIdeal_pow, ha, h𝔠, mul_pow, FractionalIdeal.spanSingleton_pow,
            inv_pow]
          refine mmR _ _ _ ?_
          rw [FractionalIdeal.spanSingleton_le_iff_mem, ← FractionalIdeal.mem_coe]
          exact Submodule.subset_span ⟨s, hs, rfl⟩
        exact le_trans ((FractionalIdeal.coeIdeal_le_coeIdeal K).1 h2) hcP
      have haP : a ≤ P := by
        first
        | exact Ideal.IsPrime.le_of_pow_le hak
        | exact hPmax.isPrime.le_of_pow_le hak
      calc FractionalIdeal.spanSingleton R⁰ s
            = FractionalIdeal.spanSingleton R⁰ s * I⁻¹ * I := by
              rw [mul_assoc, inv_mul_cancel₀ hI, mul_one]
        _ = (a : FractionalIdeal R⁰ K) * I := by rw [ha]
        _ ≤ (P : FractionalIdeal R⁰ K) * I :=
            mmR _ _ _ ((FractionalIdeal.coeIdeal_le_coeIdeal K).2 haP)
    have hIle : I ≤ (P : FractionalIdeal R⁰ K) * I := by
      rw [← FractionalIdeal.coe_le_coe, hIS, Submodule.span_le]
      intro s hs
      exact FractionalIdeal.spanSingleton_le_iff_mem.1 (key s hs)
    have hPI : (P : FractionalIdeal R⁰ K) * I ≤ I := by
      calc (P : FractionalIdeal R⁰ K) * I ≤ 1 * I := mmR _ _ _ FractionalIdeal.coeIdeal_le_one
        _ = I := one_mul _
    have heq : (P : FractionalIdeal R⁰ K) * I = 1 * I := by
      rw [one_mul]
      exact le_antisymm hPI hIle
    have hP1 : (P : FractionalIdeal R⁰ K) = 1 := mul_right_cancel₀ hI heq
    rw [FractionalIdeal.coeIdeal_eq_one] at hP1
    exact hPmax.ne_top (hP1.trans Ideal.one_eq_top)

variable (D : D7)

/- English proof (translation)
Use `le_antisymm (cS_span_le D S) ?_` and prove the remaining obligations. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨s, hs, rfl⟩`. Use `show D.host.conj (D.host.conj s) ∈ Submodule.span (𝓞 D.host.E) S`. Rewrite using `[Formalism.HC.HostRaw.conj_conj]`.

Conclude with `Submodule.subset_span hs`.
-/
theorem cS_span (S : Set D.host.E) :
    CU.cS D (Submodule.span (𝓞 D.host.E) S) = Submodule.span (𝓞 D.host.E) (D.host.conj '' S) := by
  refine le_antisymm (cS_span_le D S) ?_
  refine Submodule.span_le.2 ?_
  rintro _ ⟨s, hs, rfl⟩
  show D.host.conj (D.host.conj s) ∈ Submodule.span (𝓞 D.host.E) S
  rw [Formalism.HC.HostRaw.conj_conj]
  exact Submodule.subset_span hs

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.DN

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.DN

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Matrix nonZeroDivisors FractionalIdeal

variable (D : D7)

/- English proof (translation)
Introduce `N L hL`. Break down `Nat.eq_zero_or_pos N with rfl | hN` into its components or cases. Establish `h1 : (1 : D.host.E) ∈ vol D L` using `Submodule.subset_span ⟨1, fun j => j.elim0, Matrix.det_one.symm⟩`. Establish `h2 : (1 : D.host.E) ∈ CU.cS D (vol D L)` using `by show D.host.conj 1 ∈ vol D L`. Rewrite using `[map_one]`.

Conclude with `h1`. Rewrite using `[Submodule.one_le]`. Simplify using `using Submodule.mul_mem_mul h1 h2`. Take `⟨n, rfl⟩ : ∃ n, N = n + 1` from `⟨N - 1, by omega⟩`. Choose the witnesses or unpack the hypotheses as in `⟨U0, hU0, hdet⟩ : ∃ U : Matrix (Fin (n + 1)) (Fin (n + 1)) D.host.E, (∀ j, (fun i => U i j) ∈ L) ∧ U.det ≠ 0 := by`.

Take `⟨b, hbL, hbspan, hbli⟩` from `exists_linearIndependent D.host.E (L : Set (Fin (n + 1) → D.host.E))`. Establish `hsp : ⊤ ≤ Submodule.span D.host.E (Set.range ((↑) : b → (Fin (n + 1) → D.host.E)))`. Rewrite using `[Subtype.range_coe, hbspan]`. Conclude with `hL.2.1.ge`. Set `B` to `Module.Basis.mk hbli hsp`.

Set `e` to `B.indexEquiv (Pi.basisFun D.host.E (Fin (n + 1)))`. Set `B'` to `B.reindex e`. Use `⟨fun i j => B' j i, fun j => ?_, ?_⟩` and prove the remaining obligations. Establish `hBj : B' j = ((e.symm j : b) : Fin (n + 1) → D.host.E)`. Simplify using `[B', B, Module.Basis.reindex_apply, Module.Basis.mk_apply]`.

Use `show B' j ∈ L`. Rewrite using `[hBj]`. Conclude with `hbL (e.symm j).2`. Establish `h` using `(Pi.basisFun D.host.E (Fin (n + 1))).isUnit_det B'`. Rewrite `h` using `[Module.Basis.det_apply]`.

Establish `hm : (Pi.basisFun D.host.E (Fin (n + 1))).toMatrix B' = fun i j => B' j i`. Use extensionality with `i j`. Simplify using `[Module.Basis.toMatrix_apply]`. Rewrite `h` using `[hm]`. Conclude with `h.ne_zero`.

Establish `hfrac : IsFractional (𝓞 D.host.E)⁰ (CU.cS D (vol D L))`. Take `⟨x, y, hy, hxy⟩` from `IsFractionRing.div_surjective (A := 𝓞 D.host.E) U0.det`. Establish `hd0 : U0.det ∈ vol D L` using `Submodule.subset_span ⟨U0, hU0, rfl⟩`. Establish `hx0 : x ≠ 0`. Introduce and unpack `rfl`.

Rewrite `hxy` using `[map_zero, zero_div]`. Conclude with `hdet hxy.symm`. Establish `hyne : algebraMap (𝓞 D.host.E) D.host.E y ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy`. Use `⟨x, mem_nonZeroDivisors_of_ne_zero hx0, fun c hc => ?_⟩` and prove the remaining obligations. Establish `hdc : U0.det * c ∈ (1 : IdE D)` using `vol_mul_cS_le_one D L (sd_int D hL) (Submodule.mul_mem_mul hd0 hc)`.

Take `⟨r, hr⟩` from `Submodule.mem_one.1 hdc`. Use `⟨y * r, ?_⟩` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, map_mul, hr, ← hxy]`. Clear the denominators using the available nonvanishing facts. Set `I'F : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E` to `⟨CU.cS D (vol D L), hfrac⟩`.

Establish `hne : I'F ≠ 0`. Introduce `h0`. Establish `hm : D.host.conj U0.det ∈ (I'F : Submodule (𝓞 D.host.E) D.host.E)` using `by show D.host.conj (D.host.conj U0.det) ∈ vol D L`. Rewrite using `[Formalism.HC.HostRaw.conj_conj]`. Conclude with `Submodule.subset_span ⟨U0, hU0, rfl⟩`.

Rewrite `hm` using `[h0, FractionalIdeal.coe_zero, Submodule.mem_bot]`. Conclude with `hdet (by simpa using hm)`. Establish `hI' : (I'F : Submodule (𝓞 D.host.E) D.host.E) = Submodule.span (𝓞 D.host.E) (D.host.conj '' {x | ∃ U : Matrix (Fin (n + 1)) (Fin (n + 1)) D.host.E, (∀ j, (fun i => U i j) ∈ L) ∧ x = U.det})` using `cS_span D _`. Establish `hinv : ∀ t ∈ ((I'F⁻¹ : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Submodule (𝓞 D.host.E) D.host.E), ∀ c ∈ CU.cS D (vol D L), t * c ∈ (1 : IdE D)`. Introduce `t ht c hc`.

Establish `h` using `(FractionalIdeal.mem_inv_iff hne).1 (FractionalIdeal.mem_coe.1 ht) c (FractionalIdeal.mem_coe.1 (show c ∈ (I'F : Submodule (𝓞 D.host.E) D.host.E) from hc))`. Establish `h2` using `FractionalIdeal.mem_coe.2 h`. Rewrite `h2` using `[FractionalIdeal.coe_one]`. Then use the resulting hypothesis. Establish `hclaim : ∀ U : Matrix (Fin (n + 1)) (Fin (n + 1)) D.host.E, (∀ j, (fun i => U i j) ∈ L) → ∀ x ∈ ((I'F⁻¹ : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Submodule (𝓞 D.host.E) D.host.E) ^ (n + 1), D.host.conj U.det ^ (n + 1 - 1) * x ∈ vol D L`. Introduce `U hU x hx`.

Rewrite `hx` using `[Submodule.pow_eq_span_pow_set]`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨f, rfl⟩` from `Set.mem_pow.1 hy`. Rewrite using `[List.prod_ofFn]`.

Conclude with `adj_step D L hL U hU (fun i => (f i : D.host.E)) (fun i => hinv _ (f i).2)`. Consider the case `zero => rw [mul_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add a b _ _ ha hb => rw [mul_add]`. Conclude with `Submodule.add_mem _ ha hb`.

Consider the case `smul r a _ ha => rw [mul_smul_comm]`. Conclude with `Submodule.smul_mem _ r ha`. Establish `hA` using `spanPow I'F hne _ hI' (n + 1 - 1)`. Establish `hC : (I'F : Submodule (𝓞 D.host.E) D.host.E) ^ (n + 1 - 1) * ((I'F⁻¹ : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Submodule (𝓞 D.host.E) D.host.E) ^ (n + 1) ≤ vol D L`. Use `Submodule.mul_le.2 fun x hx y hy => ?_` and prove the remaining obligations.

Establish `hx'` using `hA hx`. Use `clear hx`. Proceed by induction on `hx' using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨s, ⟨d, ⟨U, hU, rfl⟩, rfl⟩, rfl⟩` from `hz`.

Conclude with `hclaim U hU y hy`. Consider the case `zero => rw [zero_mul]`. Conclude with `Submodule.zero_mem _`. Consider the case `add a b _ _ ha hb => rw [add_mul]`. Conclude with `Submodule.add_mem _ ha hb`.

Consider the case `smul r a _ ha => rw [smul_mul_assoc]`. Conclude with `Submodule.smul_mem _ r ha`. Establish `hD : ((I'F⁻¹ : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Submodule (𝓞 D.host.E) D.host.E) ≤ vol D L`. Establish `heq : I'F ^ (n + 1 - 1) * I'F⁻¹ ^ (n + 1) = I'F⁻¹`. Rewrite using `[Nat.add_sub_cancel, pow_succ, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hne, one_pow, one_mul]`.

Rewrite using `[← heq, FractionalIdeal.coe_mul, FractionalIdeal.coe_pow, FractionalIdeal.coe_pow]`. Conclude with `hC`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[inv_mul_cancel₀ hne, FractionalIdeal.coe_one]`. Use `_ = ((I'F⁻¹ : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Submodule (𝓞 D.host.E) D.host.E) * (I'F : Submodule (𝓞 D.host.E) D.host.E) := FractionalIdeal.coe_mul _ _`.

Use `_ ≤ vol D L * CU.cS D (vol D L) := Submodule.mul_le.2 fun x hx y hy => Submodule.mul_mem_mul (hD hx) hy`.
-/
theorem unitDisc : UnitDisc D := by
  intro N L hL
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have h1 : (1 : D.host.E) ∈ vol D L :=
      Submodule.subset_span ⟨1, fun j => j.elim0, Matrix.det_one.symm⟩
    have h2 : (1 : D.host.E) ∈ CU.cS D (vol D L) := by
      show D.host.conj 1 ∈ vol D L
      rw [map_one]
      exact h1
    rw [Submodule.one_le]
    simpa using Submodule.mul_mem_mul h1 h2
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  obtain ⟨U0, hU0, hdet⟩ : ∃ U : Matrix (Fin (n + 1)) (Fin (n + 1)) D.host.E,
      (∀ j, (fun i => U i j) ∈ L) ∧ U.det ≠ 0 := by
    obtain ⟨b, hbL, hbspan, hbli⟩ := exists_linearIndependent D.host.E (L : Set (Fin (n + 1) → D.host.E))
    have hsp : ⊤ ≤ Submodule.span D.host.E (Set.range ((↑) : b → (Fin (n + 1) → D.host.E))) := by
      rw [Subtype.range_coe, hbspan]
      exact hL.2.1.ge
    let B := Module.Basis.mk hbli hsp
    let e := B.indexEquiv (Pi.basisFun D.host.E (Fin (n + 1)))
    let B' := B.reindex e
    refine ⟨fun i j => B' j i, fun j => ?_, ?_⟩
    · have hBj : B' j = ((e.symm j : b) : Fin (n + 1) → D.host.E) := by
        simp [B', B, Module.Basis.reindex_apply, Module.Basis.mk_apply]
      show B' j ∈ L
      rw [hBj]
      exact hbL (e.symm j).2
    · have h := (Pi.basisFun D.host.E (Fin (n + 1))).isUnit_det B'
      rw [Module.Basis.det_apply] at h
      have hm : (Pi.basisFun D.host.E (Fin (n + 1))).toMatrix B' = fun i j => B' j i := by
        ext i j
        simp [Module.Basis.toMatrix_apply]
      rw [hm] at h
      exact h.ne_zero
  have hfrac : IsFractional (𝓞 D.host.E)⁰ (CU.cS D (vol D L)) := by
    obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := 𝓞 D.host.E) U0.det
    have hd0 : U0.det ∈ vol D L := Submodule.subset_span ⟨U0, hU0, rfl⟩
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [map_zero, zero_div] at hxy
      exact hdet hxy.symm
    have hyne : algebraMap (𝓞 D.host.E) D.host.E y ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
    refine ⟨x, mem_nonZeroDivisors_of_ne_zero hx0, fun c hc => ?_⟩
    have hdc : U0.det * c ∈ (1 : IdE D) :=
      vol_mul_cS_le_one D L (sd_int D hL) (Submodule.mul_mem_mul hd0 hc)
    obtain ⟨r, hr⟩ := Submodule.mem_one.1 hdc
    refine ⟨y * r, ?_⟩
    rw [Algebra.smul_def, map_mul, hr, ← hxy]
    field_simp
  let I'F : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E := ⟨CU.cS D (vol D L), hfrac⟩
  have hne : I'F ≠ 0 := by
    intro h0
    have hm : D.host.conj U0.det ∈ (I'F : Submodule (𝓞 D.host.E) D.host.E) := by
      show D.host.conj (D.host.conj U0.det) ∈ vol D L
      rw [Formalism.HC.HostRaw.conj_conj]
      exact Submodule.subset_span ⟨U0, hU0, rfl⟩
    rw [h0, FractionalIdeal.coe_zero, Submodule.mem_bot] at hm
    exact hdet (by simpa using hm)
  have hI' : (I'F : Submodule (𝓞 D.host.E) D.host.E) =
      Submodule.span (𝓞 D.host.E) (D.host.conj '' {x | ∃ U : Matrix (Fin (n + 1)) (Fin (n + 1)) D.host.E, (∀ j, (fun i => U i j) ∈ L) ∧ x = U.det}) := cS_span D _
  have hinv : ∀ t ∈ ((I'F⁻¹ : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Submodule (𝓞 D.host.E) D.host.E),
      ∀ c ∈ CU.cS D (vol D L), t * c ∈ (1 : IdE D) := by
    intro t ht c hc
    have h := (FractionalIdeal.mem_inv_iff hne).1 (FractionalIdeal.mem_coe.1 ht) c
      (FractionalIdeal.mem_coe.1 (show c ∈ (I'F : Submodule (𝓞 D.host.E) D.host.E) from hc))
    have h2 := FractionalIdeal.mem_coe.2 h
    rwa [FractionalIdeal.coe_one] at h2
  have hclaim : ∀ U : Matrix (Fin (n + 1)) (Fin (n + 1)) D.host.E, (∀ j, (fun i => U i j) ∈ L) →
      ∀ x ∈ ((I'F⁻¹ : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Submodule (𝓞 D.host.E) D.host.E) ^ (n + 1),
      D.host.conj U.det ^ (n + 1 - 1) * x ∈ vol D L := by
    intro U hU x hx
    rw [Submodule.pow_eq_span_pow_set] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨f, rfl⟩ := Set.mem_pow.1 hy
      rw [List.prod_ofFn]
      exact adj_step D L hL U hU (fun i => (f i : D.host.E)) (fun i => hinv _ (f i).2)
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [mul_add]; exact Submodule.add_mem _ ha hb
    | smul r a _ ha => rw [mul_smul_comm]; exact Submodule.smul_mem _ r ha
  have hA := spanPow I'F hne _ hI' (n + 1 - 1)
  have hC : (I'F : Submodule (𝓞 D.host.E) D.host.E) ^ (n + 1 - 1) *
      ((I'F⁻¹ : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Submodule (𝓞 D.host.E) D.host.E) ^ (n + 1)
        ≤ vol D L := by
    refine Submodule.mul_le.2 fun x hx y hy => ?_
    have hx' := hA hx
    clear hx
    induction hx' using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨s, ⟨d, ⟨U, hU, rfl⟩, rfl⟩, rfl⟩ := hz
      exact hclaim U hU y hy
    | zero => rw [zero_mul]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [add_mul]; exact Submodule.add_mem _ ha hb
    | smul r a _ ha => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r ha
  have hD : ((I'F⁻¹ : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Submodule (𝓞 D.host.E) D.host.E)
      ≤ vol D L := by
    have heq : I'F ^ (n + 1 - 1) * I'F⁻¹ ^ (n + 1) = I'F⁻¹ := by
      rw [Nat.add_sub_cancel, pow_succ, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hne, one_pow,
        one_mul]
    rw [← heq, FractionalIdeal.coe_mul, FractionalIdeal.coe_pow, FractionalIdeal.coe_pow]
    exact hC
  calc (1 : IdE D)
        = ((I'F⁻¹ * I'F : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Submodule (𝓞 D.host.E) D.host.E) := by
          rw [inv_mul_cancel₀ hne, FractionalIdeal.coe_one]
    _ = ((I'F⁻¹ : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Submodule (𝓞 D.host.E) D.host.E) *
          (I'F : Submodule (𝓞 D.host.E) D.host.E) := FractionalIdeal.coe_mul _ _
    _ ≤ vol D L * CU.cS D (vol D L) :=
        Submodule.mul_le.2 fun x hx y hy => Submodule.mul_mem_mul (hD hx) hy

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.DN

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric

/- English proof (translation)
The claim follows from `DN.determinant_norm_one_of_unit_disc D (DN.unitDisc D)`.
-/
theorem relative_determinant_norm_one (D : D7) : DetIdealsKernelNormOne D := DN.determinant_norm_one_of_unit_disc D (DN.unitDisc D)

/- English proof (translation)
The claim follows from `chi_unit_of_det_norm_one D (relative_determinant_norm_one D) χ hχ`.
-/
theorem character_unit_on_determinant (D : D7) (χ : IdE D → ℂ) (hχ : IsChi D χ) : ChiUnitDet D χ :=
  chi_unit_of_det_norm_one D (relative_determinant_norm_one D) χ hχ

/- English proof (translation)
The claim follows from `theta_norm_indep_of_det_norm_one hI relative_determinant_norm_one`.
-/
theorem LinkThIndep_of_IopIso
    (hI : ∀ D : D7, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
      IopIso D (tor0 D cc δ)) :
    LinkThIndep :=
  theta_norm_indep_of_det_norm_one hI relative_determinant_norm_one

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

end
