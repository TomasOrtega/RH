import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EichlerIsometry
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.EichlerUnip
open GlobalTheory.HL.Eichler

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

/- English proof (translation)
The claim follows from `Submodule.span_mono (Set.image_mono fun _ hi => lt_of_lt_of_le hi h)`.
-/
theorem spanTo_mono (g : Fin (r + 1) → S.V) {a b : ℕ} (h : a ≤ b) : S.spanTo g a ≤ S.spanTo g b :=
  Submodule.span_mono (Set.image_mono fun _ hi => lt_of_lt_of_le hi h)

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨i, h, rfl⟩`.
-/
theorem mem_spanTo (g : Fin (r + 1) → S.V) {a : ℕ} (i : Fin (r + 1)) (h : (i : ℕ) < a) :
    g i ∈ S.spanTo g a := Submodule.subset_span ⟨i, h, rfl⟩

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx => obtain ⟨i, hi, rfl⟩ := hx`. Conclude with `h i hi`. Consider the case `zero => simp [hf]`. Consider the case `add a b _ _ ha hb => rw [hf_add_l, ha, hb, add_zero]`.

Consider the case `smul c a _ ha => rw [hf_smul_l, ha, mul_zero]`.
-/
theorem hf_spanTo (g : Fin (r + 1) → S.V) {a : ℕ} (y : S.V)
    (h : ∀ i : Fin (r + 1), (i : ℕ) < a → hf L S.Hm (g i) y = 0) {x : S.V} (hx : x ∈ S.spanTo g a) :
    hf L S.Hm x y = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨i, hi, rfl⟩ := hx; exact h i hi
  | zero => simp [hf]
  | add a b _ _ ha hb => rw [hf_add_l, ha, hb, add_zero]
  | smul c a _ ha => rw [hf_smul_l, ha, mul_zero]

/- English proof (translation)
Rewrite using `[← hf_cj L S.herm.1, h, map_zero]`.
-/
theorem hf_symm0 {x y : S.V} (h : hf L S.Hm x y = 0) : hf L S.Hm y x = 0 := by
  rw [← hf_cj L S.herm.1, h, map_zero]

/- English proof (translation)
Use `⟨fun v => ⟨fun hv => ?_, fun hv => ?_⟩, h1⟩` and prove the remaining obligations. Establish `h3` using `A.add_mem (hBA (h2 _ hv)) hv`. Establish `h4 : n⁻¹ (n v) = v` using `n.symm_apply_apply v`. Rewrite `h3` using `[h4]`. Simplify using `using h3`.

Simplify using `using A.add_mem (hBA (h1 _ hv)) hv`.
-/
theorem mem_unipOn {N : ℕ} {A B : Submodule E (Fin N → E)} (hBA : B ≤ A)
    (n : (Fin N → E) ≃ₗ[E] (Fin N → E)) (h1 : ∀ v ∈ A, n v - v ∈ B) (h2 : ∀ v ∈ A, n⁻¹ v - v ∈ B) :
    n ∈ unipOn A B := by
  refine ⟨fun v => ⟨fun hv => ?_, fun hv => ?_⟩, h1⟩
  · have h3 := A.add_mem (hBA (h2 _ hv)) hv
    have h4 : n⁻¹ (n v) = v := n.symm_apply_apply v
    rw [h4] at h3
    simpa using h3
  · simpa using A.add_mem (hBA (h1 _ hv)) hv

end

/- English proof (translation)
Introduce `F _ _ _ _ _ E _ _ _ L r k S g gs hg j x u s hx hu hs`. Establish `hgram : ∀ a b : Fin (r + 1), (b : ℕ) < r → hf L S.Hm (g a) (g b) = 0`. Introduce `a b hb`. Establish `hb' : b ≠ Fin.last r` using `fun h => by simp [h] at hb`. Break down `hg with ⟨rfl, -⟩ | ⟨rfl, -⟩` into its components or cases.

Rewrite using `[S.gram]`. Simplify using `[hb']`. Rewrite using `[S.gram']`. Simplify using `[hb']`. Establish `hdual : ∀ a i, hf L S.Hm (g a) (gs i) = if a = i.castSucc then 1 else 0`.

Introduce `a i`. Break down `hg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩` into its components or cases. Conclude with `S.dual a i`. Conclude with `S.dual' a i`. Establish `hjr : (j : ℕ) + 1 ≤ r` using `j.2`.

Establish `hgX : ∀ a, ∀ y ∈ S.spanTo g r, hf L S.Hm (g a) y = 0` using `fun a y hy => hf_symm0 S (hf_spanTo S g _ (fun i hi => hf_symm0 S (hgram a i hi)) hy)`. Establish `hXX : ∀ {c : ℕ}, ∀ v ∈ S.spanTo g c, v ∈ perp L S.Hm (S.spanTo g r)` using `fun v hv y hy => hf_spanTo S g y (fun i _ => hgX i y hy) hv`. Establish `hxr : x ∈ S.spanTo g r` using `spanTo_mono S g hjr hx`. Establish `hE : ∀ (u : S.V) (s : E), ∀ v ∈ perp L S.Hm (S.spanTo g r), eich L S.Hm x u s v - v = hf L S.Hm v u • x`. Introduce `u s v hv`.

Simplify using `only [eich, hv x hxr]`. Use `module`. Establish `hfl : ∀ u ∈ perp L S.Hm (S.spanTo g (j + 1)), ∀ (s : E) (i : ℕ), ∀ v ∈ S.spanTo g (i + 1), eich L S.Hm x u s v - v ∈ S.spanTo g i`. Introduce `u hu s i v hv`. Rewrite using `[hE u s v (hXX v hv)]`.

Break down `le_or_gt i j with h | h` into its components or cases. Rewrite using `[hf_symm0 S (hu v (spanTo_mono S g (by omega) hv)), zero_smul]`. Conclude with `Submodule.zero_mem _`. Conclude with `Submodule.smul_mem _ _ (spanTo_mono S g h hx)`. Apply the tactic sequence `obtain ⟨n, hn, h1, h2⟩ := eichler_isometry L S.Hm S.herm x u s (hXX x hx x hxr) (hu x hx) hs`.

Use `⟨n, ⟨⟨hn, ?_⟩, ?_⟩, h1, h2, ?_, ?_⟩` and prove the remaining obligations. Use `Subgroup.mem_iInf.2 fun i => ?_` and prove the remaining obligations. Use `mem_unipOn (spanTo_mono S g (by omega)) n (fun v hv => ?_) (fun v hv => ?_)` and prove the remaining obligations. Rewrite using `[h1]`. Conclude with `hfl u hu s i v hv`.

Rewrite using `[h2]`. Conclude with `hfl _ (Submodule.neg_mem _ hu) _ i v hv`. Use `mem_unipOn (fun v hv => hXX v hv) n (fun v hv => ?_) (fun v hv => ?_)` and prove the remaining obligations. Rewrite using `[h1, hE _ _ v hv]`. Conclude with `Submodule.smul_mem _ _ hxr`.

Rewrite using `[h2, hE _ _ v hv]`. Conclude with `Submodule.smul_mem _ _ hxr`. Introduce `v hv`. Use `hE u s v (hXX v hv)` as an intermediate fact. Rewrite `this` using `[hf_symm0 S (hu v hv), zero_smul, sub_eq_zero]`.

Rewrite using `[h1, this]`. Introduce and unpack `m ⟨⟨-, hm1⟩, hm2⟩ replace hm1 := Subgroup.mem_iInf.1 hm1`. Establish `hm : m (g j.succ) - g j.succ ∈ S.spanTo g (j + 1)`. Break down `hjr.lt_or_eq with h | h` into its components or cases. Conclude with `(hm1 ⟨j + 1, h⟩).2 _ (mem_spanTo S g _ (by simp))`.

Use `hm2.2 (g j.succ) (hgX _)` as an intermediate fact. Conclude with `spanTo_mono S g h.ge this`. Establish `hmu : hf L S.Hm (m (g j.succ)) u = hf L S.Hm (g j.succ) u`. Use `hf_symm0 S (hu _ hm)` as an intermediate fact. Rewrite `this` using `[hf_sub_l, sub_eq_zero]`. Then use the resulting hypothesis.

Establish `hc : ∀ i : Fin r, S.coef g gs n i = hf L S.Hm x (gs i) * hf L S.Hm (g i.succ) u`. Introduce `i`. Establish `h3` using `hE u s (g i.succ) (hgX _)`. Rewrite `h3` using `[sub_eq_iff_eq_add, ← h1]`. Establish `h4 : i.succ ≠ i.castSucc` using `(Fin.castSucc_lt_succ).ne'`.

Simplify using `only [Frames.coef, Frames.h]`. Rewrite using `[h3, hf_add_l, hf_smul_l, hdual, if_neg h4]`. Expand and normalize the polynomial expressions, which then agree. Establish `hsum : ∑ i, S.coef g gs n i = S.h x (gs j) * S.h (m (g j.succ)) u`. Simplify using `only [Frames.h]`.

Rewrite using `[Finset.sum_eq_single j, hc, hmu]`. Introduce `i _ hij`. Rewrite using `[hc]`. Break down `lt_or_gt_of_ne hij with h | h` into its components or cases. Establish `h' : (i : ℕ) < j` using `h`.

Rewrite using `[hf_symm0 S (hu _ (mem_spanTo S g i.succ (by simp; omega))), mul_zero]`. Establish `h' : (j : ℕ) < i` using `h`. Rewrite using `[hf_spanTo S g (gs i) (fun a ha => ?_) hx, zero_mul]`. Rewrite using `[hdual, if_neg]`. Introduce and unpack `rfl`.

Simplify using `at ha`. Use linear arithmetic over natural numbers and integers. Simplify using the standard rewrite rules. Simplify using `only [Frames.psiOf, hsum]`.
-/
theorem eichler_mem_unip : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (g : Fin (r + 1) → S.V) (gs : Fin r → S.V), (g = S.f ∧ gs = S.es) ∨ (g = S.f' ∧ gs = S.es') → ∀ (j : Fin r) (x u : S.V) (s : E), x ∈ S.spanTo g (j + 1) → u ∈ perp L S.Hm (S.spanTo g (j + 1)) → s + L.cj s = S.h u u → ∃ n ∈ S.Nof g, (∀ v, n v = eich L S.Hm x u s v) ∧ (∀ v, n⁻¹ v = eich L S.Hm x (-u) (L.cj s) v) ∧ (∀ v ∈ S.spanTo g (j + 1), n v = v) ∧ ∀ m ∈ S.Nof g, S.psiOf g gs n = L.psi0 (algebraMap F E S.th⁻¹ * (S.h x (gs j) * S.h (m (g j.succ)) u)) := by
  intro F _ _ _ _ _ E _ _ _ L r k S g gs hg j x u s hx hu hs
  have hgram : ∀ a b : Fin (r + 1), (b : ℕ) < r → hf L S.Hm (g a) (g b) = 0 := by
    intro a b hb
    have hb' : b ≠ Fin.last r := fun h => by simp [h] at hb
    rcases hg with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · rw [S.gram]; simp [hb']
    · rw [S.gram']; simp [hb']
  have hdual : ∀ a i, hf L S.Hm (g a) (gs i) = if a = i.castSucc then 1 else 0 := by
    intro a i
    rcases hg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact S.dual a i
    · exact S.dual' a i
  have hjr : (j : ℕ) + 1 ≤ r := j.2
  have hgX : ∀ a, ∀ y ∈ S.spanTo g r, hf L S.Hm (g a) y = 0 := fun a y hy =>
    hf_symm0 S (hf_spanTo S g _ (fun i hi => hf_symm0 S (hgram a i hi)) hy)
  have hXX : ∀ {c : ℕ}, ∀ v ∈ S.spanTo g c, v ∈ perp L S.Hm (S.spanTo g r) := fun v hv y hy =>
    hf_spanTo S g y (fun i _ => hgX i y hy) hv
  have hxr : x ∈ S.spanTo g r := spanTo_mono S g hjr hx
  have hE : ∀ (u : S.V) (s : E), ∀ v ∈ perp L S.Hm (S.spanTo g r),
      eich L S.Hm x u s v - v = hf L S.Hm v u • x := by
    intro u s v hv
    simp only [eich, hv x hxr]
    module
  have hfl : ∀ u ∈ perp L S.Hm (S.spanTo g (j + 1)), ∀ (s : E) (i : ℕ), ∀ v ∈ S.spanTo g (i + 1),
      eich L S.Hm x u s v - v ∈ S.spanTo g i := by
    intro u hu s i v hv
    rw [hE u s v (hXX v hv)]
    rcases le_or_gt i j with h | h
    · rw [hf_symm0 S (hu v (spanTo_mono S g (by omega) hv)), zero_smul]
      exact Submodule.zero_mem _
    · exact Submodule.smul_mem _ _ (spanTo_mono S g h hx)
  obtain ⟨n, hn, h1, h2⟩ := eichler_isometry L S.Hm S.herm x u s (hXX x hx x hxr) (hu x hx) hs
  refine ⟨n, ⟨⟨hn, ?_⟩, ?_⟩, h1, h2, ?_, ?_⟩
  · refine Subgroup.mem_iInf.2 fun i => ?_
    refine mem_unipOn (spanTo_mono S g (by omega)) n (fun v hv => ?_) (fun v hv => ?_)
    · rw [h1]; exact hfl u hu s i v hv
    · rw [h2]; exact hfl _ (Submodule.neg_mem _ hu) _ i v hv
  · refine mem_unipOn (fun v hv => hXX v hv) n (fun v hv => ?_) (fun v hv => ?_)
    · rw [h1, hE _ _ v hv]; exact Submodule.smul_mem _ _ hxr
    · rw [h2, hE _ _ v hv]; exact Submodule.smul_mem _ _ hxr
  · intro v hv
    have := hE u s v (hXX v hv)
    rw [hf_symm0 S (hu v hv), zero_smul, sub_eq_zero] at this
    rw [h1, this]
  · rintro m ⟨⟨-, hm1⟩, hm2⟩
    replace hm1 := Subgroup.mem_iInf.1 hm1
    have hm : m (g j.succ) - g j.succ ∈ S.spanTo g (j + 1) := by
      rcases hjr.lt_or_eq with h | h
      · exact (hm1 ⟨j + 1, h⟩).2 _ (mem_spanTo S g _ (by simp))
      · have := hm2.2 (g j.succ) (hgX _)
        exact spanTo_mono S g h.ge this
    have hmu : hf L S.Hm (m (g j.succ)) u = hf L S.Hm (g j.succ) u := by
      have := hf_symm0 S (hu _ hm)
      rwa [hf_sub_l, sub_eq_zero] at this
    have hc : ∀ i : Fin r, S.coef g gs n i = hf L S.Hm x (gs i) * hf L S.Hm (g i.succ) u := by
      intro i
      have h3 := hE u s (g i.succ) (hgX _)
      rw [sub_eq_iff_eq_add, ← h1] at h3
      have h4 : i.succ ≠ i.castSucc := (Fin.castSucc_lt_succ).ne'
      simp only [Frames.coef, Frames.h]
      rw [h3, hf_add_l, hf_smul_l, hdual, if_neg h4]
      ring
    have hsum : ∑ i, S.coef g gs n i = S.h x (gs j) * S.h (m (g j.succ)) u := by
      simp only [Frames.h]
      rw [Finset.sum_eq_single j, hc, hmu]
      · intro i _ hij
        rw [hc]
        rcases lt_or_gt_of_ne hij with h | h
        · have h' : (i : ℕ) < j := h
          rw [hf_symm0 S (hu _ (mem_spanTo S g i.succ (by simp; omega))), mul_zero]
        · have h' : (j : ℕ) < i := h
          rw [hf_spanTo S g (gs i) (fun a ha => ?_) hx, zero_mul]
          rw [hdual, if_neg]
          rintro rfl
          simp at ha
          omega
      · simp
    simp only [Frames.psiOf, hsum]

end GlobalTheory.HL.EichlerUnip
