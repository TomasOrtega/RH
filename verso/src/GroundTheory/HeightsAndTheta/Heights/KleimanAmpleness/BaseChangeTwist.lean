import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.BaseChangeObj
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistAlg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial Kleiman

open scoped Pointwise

noncomputable section

variable {S : Type*} [CommRing S] {O : Type*} [CommRing O] [Algebra S O] {Ω : Type*} [Field Ω]
  [Algebra S Ω] [Algebra O Ω] [IsScalarTower S O Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

omit [Algebra S Ω] [Algebra O Ω] [IsScalarTower S O Ω] in

/- English proof (translation)
Proceed by induction on `hs using Submonoid.closure_induction with`. Consider the case `mem a ha`. Take `⟨i, hi, rfl⟩` from `ha`. Rewrite using `[map_X]`. Conclude with `Submonoid.subset_closure ⟨i, hi, rfl⟩`.

Consider the case `one => rw [map_one]`. Conclude with `one_mem _`. Consider the case `mul a b _ _ ha hb => rw [map_mul]`. Conclude with `mul_mem ha hb`.
-/
theorem map_mem_monos_baseChange {I : Finset (Fin (N + 1))} {s : Poly S N} (hs : s ∈ monos I) :
    map (algebraMap S O) s ∈ monos (S := O) I := by
  induction hs using Submonoid.closure_induction with
  | mem a ha =>
    obtain ⟨i, hi, rfl⟩ := ha
    rw [map_X]
    exact Submonoid.subset_closure ⟨i, hi, rfl⟩
  | one => rw [map_one]; exact one_mem _
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb

/- English proof (translation)
Take `⟨f, s, e, hs, hf, hse, rfl⟩` from `ha`. Conclude with `⟨map (algebraMap S O) f, map (algebraMap S O) s, e, map_mem_monos_baseChange hs, hf.map _, hse.map _, by rw [aeval_map_algebraMap, aeval_map_algebraMap]⟩`.
-/
theorem mem_chartRing_baseChange {I : Chart x} {a : Ω} (ha : a ∈ chartRing S x I) :
    a ∈ chartRing O x I := by
  obtain ⟨f, s, e, hs, hf, hse, rfl⟩ := ha
  exact ⟨map (algebraMap S O) f, map (algebraMap S O) s, e, map_mem_monos_baseChange hs, hf.map _,
    hse.map _, by rw [aeval_map_algebraMap, aeval_map_algebraMap]⟩

/- English proof (translation)
Establish `: a • y = (⟨(a : Ω), mem_chartRing_baseChange a.2⟩ : chartRing O x I) • y`. Rewrite using `[chartRing_smul_def, chartRing_smul_def]`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ hy`.
-/
theorem smul_mem_span_baseChange {I : Chart x} (P : Set Ω) (a : chartRing S x I) {y : Ω}
    (hy : y ∈ Submodule.span (chartRing O x I) P) : a • y ∈ Submodule.span (chartRing O x I) P := by
  have : a • y = (⟨(a : Ω), mem_chartRing_baseChange a.2⟩ : chartRing O x I) • y := by
    rw [chartRing_smul_def, chartRing_smul_def]
  rw [this]
  exact Submodule.smul_mem _ _ hy

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Use `Submodule.span_le.mpr fun y hy => ?_` and prove the remaining obligations. Use `Submodule.span_induction (p := fun y _ => y ∈ Submodule.span (chartRing O x I) P) ?_ ?_ ?_ ?_ hy` and prove the remaining obligations. Introduce `z hz`. Conclude with `Submodule.subset_span hz`.

Conclude with `Submodule.zero_mem _`. Introduce `a b _ _ ha hb`. Conclude with `Submodule.add_mem _ ha hb`. Introduce `a z _ hz`. Conclude with `smul_mem_span_baseChange P a hz`.

Conclude with `Submodule.span_mono Submodule.subset_span`.
-/
theorem span_baseChange_span (I : Chart x) (P : Set Ω) :
    Submodule.span (chartRing O x I) (Submodule.span (chartRing S x I) P : Set Ω) =
      Submodule.span (chartRing O x I) P := by
  apply le_antisymm
  · refine Submodule.span_le.mpr fun y hy => ?_
    refine Submodule.span_induction
      (p := fun y _ => y ∈ Submodule.span (chartRing O x I) P) ?_ ?_ ?_ ?_ hy
    · intro z hz; exact Submodule.subset_span hz
    · exact Submodule.zero_mem _
    · intro a b _ _ ha hb; exact Submodule.add_mem _ ha hb
    · intro a z _ hz; exact smul_mem_span_baseChange P a hz
  · exact Submodule.span_mono Submodule.subset_span

/- English proof (translation)
Use `SubSystem.ext_sub fun I => ?_` and prove the remaining obligations. Take `⟨i, hi⟩` from `I.2.1`. Express the relevant statement in the definitionally equal form `Submodule.span (chartRing O x I) (twistMod S x c I : Set Ω) = twistMod O x c I`. Rewrite using `[twistMod_eq_span c I hi, twistMod_eq_span c I hi, span_baseChange_span]`.
-/
theorem baseChange_twistSys (c : ℤ) : (twistSys S x c).baseChange O = twistSys O x c := by
  refine SubSystem.ext_sub fun I => ?_
  obtain ⟨i, hi⟩ := I.2.1
  change Submodule.span (chartRing O x I) (twistMod S x c I : Set Ω) = twistMod O x c I
  rw [twistMod_eq_span c I hi, twistMod_eq_span c I hi, span_baseChange_span]

omit [Algebra S O] [IsScalarTower S O Ω] in

/- English proof (translation)
Use `SubSystem.ext_sub fun I => ?_` and prove the remaining obligations. Rewrite using `[SubSystem.twist_sub_eq_mul_of_line]`. Express the relevant statement in the definitionally equal form `Submodule.span (chartRing O x I) ((Q.twist R).sub I : Set Ω) = Submodule.span (chartRing O x I) (R.sub I : Set Ω) * Submodule.span (chartRing O x I) (Q.sub I : Set Ω)`. Rewrite using `[SubSystem.twist_sub_eq_mul_of_line, Submodule.span_mul_span]`. Apply `le_antisymm` to reduce the goal to its premises.

Use `Submodule.span_le.mpr fun y hy => ?_` and prove the remaining obligations. Use `Submodule.mul_induction_on (C := fun y => y ∈ Submodule.span (chartRing O x I) ((R.sub I : Set Ω) * (Q.sub I : Set Ω))) hy ?_ ?_` and prove the remaining obligations. Introduce `r hr q hq`. Conclude with `Submodule.subset_span (Set.mul_mem_mul hr hq)`. Introduce `a b ha hb`.

Conclude with `Submodule.add_mem _ ha hb`. Use `Submodule.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨r, hr, q, hq, rfl⟩`. Conclude with `Submodule.subset_span (Submodule.mul_mem_mul hr hq)`.
-/
theorem baseChange_twist (Q R : SubSystem S x Ω) :
    (Q.twist R).baseChange O = (Q.baseChange O).twist (R.baseChange O) := by
  refine SubSystem.ext_sub fun I => ?_
  rw [SubSystem.twist_sub_eq_mul_of_line]
  change Submodule.span (chartRing O x I) ((Q.twist R).sub I : Set Ω) =
    Submodule.span (chartRing O x I) (R.sub I : Set Ω) * Submodule.span (chartRing O x I) (Q.sub I : Set Ω)
  rw [SubSystem.twist_sub_eq_mul_of_line, Submodule.span_mul_span]
  apply le_antisymm
  · refine Submodule.span_le.mpr fun y hy => ?_
    refine Submodule.mul_induction_on (C := fun y =>
      y ∈ Submodule.span (chartRing O x I) ((R.sub I : Set Ω) * (Q.sub I : Set Ω))) hy ?_ ?_
    · intro r hr q hq
      exact Submodule.subset_span (Set.mul_mem_mul hr hq)
    · intro a b ha hb; exact Submodule.add_mem _ ha hb
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨r, hr, q, hq, rfl⟩
    exact Submodule.subset_span (Submodule.mul_mem_mul hr hq)

/- English proof (translation)
Establish `key : ∀ (l : List (Fin n)) (F : SubSystem S x Ω), l.foldl (fun G i => G.twist ((L i).baseChange O)) (F.baseChange O) = (l.foldl (fun G i => G.twist (L i)) F).baseChange O`. Introduce `l`. Proceed by induction on `l with`. Consider the case `nil => intro F`. Both sides reduce to the same expression.

Consider the case `cons a l ih`. Introduce `F`. Rewrite using `[List.foldl_cons, List.foldl_cons, ← baseChange_twist, ih]`. Unfold `tensorSub`. Rewrite using `[← baseChange_twistSys (S := S) (O := O) 0]`.

Conclude with `key _ _`.
-/
theorem baseChange_tensorSub {n : ℕ} (L : Fin n → SubSystem S x Ω) (T : Finset (Fin n)) :
    tensorSub (fun i => (L i).baseChange O) T = (tensorSub L T).baseChange O := by
  have key : ∀ (l : List (Fin n)) (F : SubSystem S x Ω),
      l.foldl (fun G i => G.twist ((L i).baseChange O)) (F.baseChange O) =
        (l.foldl (fun G i => G.twist (L i)) F).baseChange O := by
    intro l
    induction l with
    | nil => intro F; rfl
    | cons a l ih =>
      intro F
      rw [List.foldl_cons, List.foldl_cons, ← baseChange_twist, ih]
  unfold tensorSub
  rw [← baseChange_twistSys (S := S) (O := O) 0]
  exact key _ _

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
