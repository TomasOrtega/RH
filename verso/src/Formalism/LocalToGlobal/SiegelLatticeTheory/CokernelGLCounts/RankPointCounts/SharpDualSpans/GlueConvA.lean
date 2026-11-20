import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SharpDualSpans.GlueEtaPf

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Matrix

namespace PI.LocCntLat.GC

open PI.LocCntLat.GE

section Lin

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

/- English proof (translation)
Rewrite using `[H.h_herm, H.h_zero_left, map_zero]`.
-/
theorem h_zero_right' (H : HermSp M V) (x : V) : H.h x 0 = 0 := by
  rw [H.h_herm, H.h_zero_left, map_zero]

/- English proof (translation)
Rewrite using `[H.h_herm, H.h_smul_left, map_mul, ← H.h_herm y x]`.
-/
theorem h_smul_right' (H : HermSp M V) (a : E) (x y : V) : H.h x (a • y) = M.L.cj a * H.h x y := by
  rw [H.h_herm, H.h_smul_left, map_mul, ← H.h_herm y x]

/- English proof (translation)
Rewrite `hx`, the goal using `[L.O_def]`. Conclude with `hx.map (L.cj.toAlgHom.restrictScalars 𝒪[F])`.
-/
theorem cj_mem_O (L : LocE F E) {x : E} (hx : x ∈ L.O) : L.cj x ∈ L.O := by
  rw [L.O_def] at hx ⊢
  exact hx.map (L.cj.toAlgHom.restrictScalars 𝒪[F])

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Simplify using `[H.h_zero_left]`. Introduce `a s ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha, H.h_add_left, H.h_smul_left, ih]`.
-/
private theorem hermSp_h_finset_sum_smul_left (H : HermSp M V) {κ : Type} (s : Finset κ) (d : κ → E) (g : κ → V) (y : V) :
    H.h (∑ k ∈ s, d k • g k) y = ∑ k ∈ s, d k * H.h (g k) y := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [H.h_zero_left]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, H.h_add_left, H.h_smul_left, ih]

/- English proof (translation)
Rewrite using `[hermSp_h_finset_sum_smul_left]`. Simplify using `only [Matrix.mulVec, dotProduct, HermSp.gram, Matrix.of_apply]`. Conclude with `Finset.sum_congr rfl fun k _ => mul_comm _ _`.
-/
theorem gram_mulVec (H : HermSp M V) (g : ι → V) (d : ι → E) (i : ι) :
    H.h (∑ k, d k • g k) (g i) = ((H.gram g) *ᵥ d) i := by
  rw [hermSp_h_finset_sum_smul_left]
  simp only [Matrix.mulVec, dotProduct, HermSp.gram, Matrix.of_apply]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/- English proof (translation)
Use `⟨∑ k, ((H.gram g)⁻¹ *ᵥ Pi.single j 1) k • g k, ?_, fun i => ?_⟩` and prove the remaining obligations. Conclude with `Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)`. Rewrite using `[gram_mulVec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hG, Matrix.one_mulVec, Pi.single_apply]`.
-/
theorem exists_dual (H : HermSp M V) (g : ι → V) (hG : IsUnit (H.gram g).det) (j : ι) :
    ∃ u ∈ Submodule.span E (Set.range g), ∀ i, H.h u (g i) = if i = j then 1 else 0 := by
  refine ⟨∑ k, ((H.gram g)⁻¹ *ᵥ Pi.single j 1) k • g k, ?_, fun i => ?_⟩
  · exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · rw [gram_mulVec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hG, Matrix.one_mulVec, Pi.single_apply]

/- English proof (translation)
Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `c hc`. Establish `h0 : H.gram g *ᵥ c = 0`. Use function extensionality and compare the values at `i`. Use `gram_mulVec H g c i` as an intermediate fact.

Rewrite `this` using `[hc, H.h_zero_left]`. Simplify using `using this.symm`. Establish `hc0 : c = 0`. Rewrite using `[← Matrix.one_mulVec c, ← Matrix.nonsing_inv_mul _ hG, ← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]`. Introduce `i`.

Rewrite using `[hc0]`. Both sides reduce to the same expression.
-/
theorem linIndep_of_gram (H : HermSp M V) (g : ι → V) (hG : IsUnit (H.gram g).det) :
    LinearIndependent E g := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have h0 : H.gram g *ᵥ c = 0 := by
    funext i
    have := gram_mulVec H g c i
    rw [hc, H.h_zero_left] at this
    simpa using this.symm
  have hc0 : c = 0 := by
    rw [← Matrix.one_mulVec c, ← Matrix.nonsing_inv_mul _ hG, ← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]
  intro i
  rw [hc0]
  rfl

/- English proof (translation)
Rewrite using `[H.h_herm, H.h_add_left, map_add, ← H.h_herm, ← H.h_herm]`.
-/
private theorem hermSp_h_add_right (H : HermSp M V) (w x y : V) : H.h w (x + y) = H.h w x + H.h w y := by
  rw [H.h_herm, H.h_add_left, map_add, ← H.h_herm, ← H.h_herm]

end Lin

section Dual

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

/- English proof (translation)
Use `show u ∈ Submodule.span E (Set.range (H.MMfam t)) ∧ ∀ m ∈ MMo H t, H.h u m ∈ M.L.O`. Use `⟨hu, fun m hm => ?_⟩` and prove the remaining obligations. Proceed by induction on `hm using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨i, rfl⟩` from `hx`.

Rewrite using `[hu' i]`. Use `split_ifs`. Conclude with `M.L.O.one_mem`. Conclude with `M.L.O.zero_mem`. Consider the case `zero => rw [h_zero_right']`.

Conclude with `M.L.O.zero_mem`. Consider the case `add x y _ _ hx hy => rw [hermSp_h_add_right]`. Conclude with `M.L.O.add_mem hx hy`. Consider the case `smul c x _ hx => rw [Subring.smul_def, h_smul_right']`. Conclude with `M.L.O.mul_mem (cj_mem_O _ c.2) hx`.
-/
theorem dual_mem_sharp (H : HermSp M V) {r : ℕ} (t : Term V M r) {u : V}
    (hu : u ∈ Submodule.span E (Set.range (H.MMfam t))) (j : Fin (r + 1) ⊕ Fin (r + 1))
    (hu' : ∀ i, H.h u (H.MMfam t i) = if i = j then 1 else 0) : u ∈ MMsharp H t := by
  show u ∈ Submodule.span E (Set.range (H.MMfam t)) ∧ ∀ m ∈ MMo H t, H.h u m ∈ M.L.O
  refine ⟨hu, fun m hm => ?_⟩
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    rw [hu' i]
    split_ifs
    · exact M.L.O.one_mem
    · exact M.L.O.zero_mem
  | zero => rw [h_zero_right']; exact M.L.O.zero_mem
  | add x y _ _ hx hy => rw [hermSp_h_add_right]; exact M.L.O.add_mem hx hy
  | smul c x _ hx => rw [Subring.smul_def, h_smul_right']; exact M.L.O.mul_mem (cj_mem_O _ c.2) hx

/- English proof (translation)
Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun E).1 hm`. Establish `hc : ∀ j, c j ∈ M.L.O`. Introduce `j`. Take `⟨u, hu, hu'⟩` from `exists_dual H (H.MMfam t) hG j`. Establish `h1` using `hd u (dual_mem_sharp H t hu j hu')`.

Establish `h2 : H.h (∑ i, c i • H.MMfam t i) u = c j`. Rewrite using `[hermSp_h_finset_sum_smul_left, Finset.sum_eq_single j]`. Rewrite using `[H.h_herm u, hu' j, if_pos rfl, map_one, mul_one]`. Introduce `i _ hij`. Rewrite using `[H.h_herm u, hu' i, if_neg hij, map_zero, mul_zero]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ j) h`. Rewrite `h1` using `[h2]`. Then use the resulting hypothesis. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Conclude with `Submodule.smul_mem (MMo H t) (⟨c i, hc i⟩ : M.L.O) (Submodule.subset_span ⟨i, rfl⟩)`.
-/
theorem mem_MMo_of_dual (H : HermSp M V) {r : ℕ} (t : Term V M r) (hG : IsUnit (H.gram (H.MMfam t)).det)
    {m : V} (hm : m ∈ Submodule.span E (Set.range (H.MMfam t)))
    (hd : ∀ u ∈ MMsharp H t, H.h m u ∈ M.L.O) : m ∈ MMo H t := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hm
  have hc : ∀ j, c j ∈ M.L.O := by
    intro j
    obtain ⟨u, hu, hu'⟩ := exists_dual H (H.MMfam t) hG j
    have h1 := hd u (dual_mem_sharp H t hu j hu')
    have h2 : H.h (∑ i, c i • H.MMfam t i) u = c j := by
      rw [hermSp_h_finset_sum_smul_left, Finset.sum_eq_single j]
      · rw [H.h_herm u, hu' j, if_pos rfl, map_one, mul_one]
      · intro i _ hij
        rw [H.h_herm u, hu' i, if_neg hij, map_zero, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ j) h
    rwa [h2] at h1
  refine Submodule.sum_mem _ fun i _ => ?_
  exact Submodule.smul_mem (MMo H t) (⟨c i, hc i⟩ : M.L.O) (Submodule.subset_span ⟨i, rfl⟩)

/- English proof (translation)
Introduce `x hx`. Establish `hx' : x ∈ Submodule.span E (Set.range (H.MMfam t)) ∧ ∀ m ∈ MMo H t, H.h x m ∈ M.L.O` using `hx`. Establish `hy : ∀ i, H.h (∑ j, H.h x (H.MMfam t j) • u j) (H.MMfam t i) = H.h x (H.MMfam t i)`. Introduce `i`. Rewrite using `[hermSp_h_finset_sum_smul_left, Finset.sum_eq_single i]`.

Rewrite using `[hu' i i, if_pos rfl, mul_one]`. Introduce `j _ hji`. Rewrite using `[hu' j i, if_neg (Ne.symm hji), mul_zero]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ i) h`.

Establish `hmem : x - ∑ j, H.h x (H.MMfam t j) • u j ∈ Submodule.span E (Set.range (H.MMfam t))` using `Submodule.sub_mem _ hx'.1 (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hu j))`. Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun E).1 hmem`. Establish `h0 : H.gram (H.MMfam t) *ᵥ c = 0`. Use function extensionality and compare the values at `i`. Use `gram_mulVec H (H.MMfam t) c i` as an intermediate fact.

Rewrite `this` using `[hc, sub_eq_add_neg, ← neg_one_smul E, H.h_add_left, H.h_smul_left, hy i]`. Simplify using `using this.symm`. Establish `hc0 : c = 0`. Rewrite using `[← Matrix.one_mulVec c, ← Matrix.nonsing_inv_mul _ hG, ← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]`. Establish `hxy : x = ∑ j, H.h x (H.MMfam t j) • u j`.

Rewrite using `[← sub_eq_zero, ← hc, hc0]`. Simplify using the standard rewrite rules. Use `show x ∈ Submodule.span M.L.O (Set.range u)`. Rewrite using `[hxy]`. Use `Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations.

Conclude with `Submodule.smul_mem _ (⟨_, hx'.2 _ (Submodule.subset_span ⟨j, rfl⟩)⟩ : M.L.O) (Submodule.subset_span ⟨j, rfl⟩)`.
-/
theorem sharp_le_span_dual (H : HermSp M V) {r : ℕ} (t : Term V M r) (hG : IsUnit (H.gram (H.MMfam t)).det)
    (u : Fin (r + 1) ⊕ Fin (r + 1) → V) (hu : ∀ j, u j ∈ Submodule.span E (Set.range (H.MMfam t)))
    (hu' : ∀ j i, H.h (u j) (H.MMfam t i) = if i = j then 1 else 0) :
    (MMsharp H t : Set V) ⊆ Submodule.span M.L.O (Set.range u) := by
  intro x hx
  have hx' : x ∈ Submodule.span E (Set.range (H.MMfam t)) ∧ ∀ m ∈ MMo H t, H.h x m ∈ M.L.O := hx
  have hy : ∀ i, H.h (∑ j, H.h x (H.MMfam t j) • u j) (H.MMfam t i) = H.h x (H.MMfam t i) := by
    intro i
    rw [hermSp_h_finset_sum_smul_left, Finset.sum_eq_single i]
    · rw [hu' i i, if_pos rfl, mul_one]
    · intro j _ hji
      rw [hu' j i, if_neg (Ne.symm hji), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hmem : x - ∑ j, H.h x (H.MMfam t j) • u j ∈ Submodule.span E (Set.range (H.MMfam t)) :=
    Submodule.sub_mem _ hx'.1 (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hu j))
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hmem
  have h0 : H.gram (H.MMfam t) *ᵥ c = 0 := by
    funext i
    have := gram_mulVec H (H.MMfam t) c i
    rw [hc, sub_eq_add_neg, ← neg_one_smul E, H.h_add_left, H.h_smul_left, hy i] at this
    simpa using this.symm
  have hc0 : c = 0 := by
    rw [← Matrix.one_mulVec c, ← Matrix.nonsing_inv_mul _ hG, ← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]
  have hxy : x = ∑ j, H.h x (H.MMfam t j) • u j := by
    rw [← sub_eq_zero, ← hc, hc0]
    simp
  show x ∈ Submodule.span M.L.O (Set.range u)
  rw [hxy]
  refine Submodule.sum_mem _ fun j _ => ?_
  exact Submodule.smul_mem _ (⟨_, hx'.2 _ (Submodule.subset_span ⟨j, rfl⟩)⟩ : M.L.O)
    (Submodule.subset_span ⟨j, rfl⟩)

end Dual

end PI.LocCntLat.GC
