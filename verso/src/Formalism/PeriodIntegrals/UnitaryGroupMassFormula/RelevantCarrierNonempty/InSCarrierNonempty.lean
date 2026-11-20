import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.FourParts

noncomputable section

open scoped Classical

namespace PI.UnitaryGroupMassFormula.InSRelevantW

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.FourParts

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

/- English proof (translation)
The claim follows from `Submodule.span_mono (Set.image_mono fun i hi => lt_of_lt_of_le hi h)`.
-/
theorem xa_mono {T : E} (G : FlagG S r T) {a b : ℕ} (h : a ≤ b) : G.Xa a ≤ G.Xa b := Submodule.span_mono (Set.image_mono fun i hi => lt_of_lt_of_le hi h)

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨i, Nat.lt_succ_self _, rfl⟩`.
-/
theorem e_mem_xa {T : E} (G : FlagG S r T) (i : Fin r) : G.e i ∈ G.Xa (i.val + 1) := Submodule.subset_span ⟨i, Nat.lt_succ_self _, rfl⟩

/- English proof (translation)
Establish `hset : {i : Fin r | i.1 < r} = Set.univ` using `Set.eq_univ_of_forall fun i => i.2`. Unfold `FlagG.Xa FlagG.X`. Rewrite using `[hset, Set.image_univ]`.
-/
theorem xa_r {T : E} (G : FlagG S r T) : G.Xa r = G.X := by
  have hset : {i : Fin r | i.1 < r} = Set.univ := Set.eq_univ_of_forall fun i => i.2
  unfold FlagG.Xa FlagG.X
  rw [hset, Set.image_univ]

/- English proof (translation)
Introduce `x hx`. Unfold `FlagG.X at hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨a, rfl⟩` from `hy`.

Conclude with `G.z_orth a`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => simp [hx, hy]`. Consider the case `smul c x _ hx => simp [hx]`.
-/
theorem z_mem_perp {T : E} (G : FlagG S r T) : G.z ∈ perpS S G.X := by
  intro x hx
  unfold FlagG.X at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, rfl⟩ := hy
    exact G.z_orth a
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul c x _ hx => simp [hx]

/- English proof (translation)
Establish `hw'` using `hw`. Unfold `FlagG.Xa at hw'`. Take `⟨l, hl, hlw⟩` from `(Finsupp.mem_span_image_iff_linearCombination E).mp hw'`. Establish `hmem : c • G.e i + w ∈ Submodule.span E (Set.range G.e)` using `Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)) (Submodule.span_mono (Set.image_subset_range _ _) hw')`. Unfold `FlagG.coefX`.

Rewrite using `[dif_pos hmem]`. Establish `hrepr : G.e_indep.repr ⟨c • G.e i + w, hmem⟩ = Finsupp.single i c + l`. Apply `G.e_indep.repr_eq` to reduce the goal to its premises. Rewrite using `[map_add, Finsupp.linearCombination_single, hlw]`. Rewrite using `[hrepr, Finsupp.add_apply, Finsupp.single_eq_same]`.

Establish `hli : l i = 0`. Assume the negation of the conclusion as `hne`. Establish `h1` using `(Finsupp.mem_supported _ _).mp hl (Finsupp.mem_support_iff.mpr hne)`. Conclude with `lt_irrefl (i.1) h1`. Rewrite using `[hli, add_zero]`.
-/
theorem coefX_single_add {T : E} (G : FlagG S r T) (i : Fin r) (c : E) {w : S.V}
    (hw : w ∈ G.Xa i.val) : G.coefX (c • G.e i + w) i = c := by
  classical
  have hw' := hw
  unfold FlagG.Xa at hw'
  obtain ⟨l, hl, hlw⟩ := (Finsupp.mem_span_image_iff_linearCombination E).mp hw'
  have hmem : c • G.e i + w ∈ Submodule.span E (Set.range G.e) :=
    Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
      (Submodule.span_mono (Set.image_subset_range _ _) hw')
  unfold FlagG.coefX
  rw [dif_pos hmem]
  have hrepr : G.e_indep.repr ⟨c • G.e i + w, hmem⟩ = Finsupp.single i c + l := by
    apply G.e_indep.repr_eq
    rw [map_add, Finsupp.linearCombination_single, hlw]
  rw [hrepr, Finsupp.add_apply, Finsupp.single_eq_same]
  have hli : l i = 0 := by
    by_contra hne
    have h1 := (Finsupp.mem_supported _ _).mp hl (Finsupp.mem_support_iff.mpr hne)
    exact lt_irrefl (i.1) h1
  rw [hli, add_zero]

/- English proof (translation)
Establish `hset : G.e '' {j : Fin r | j.1 < i.1 + 1} = insert (G.e i) (G.e '' {j | j.1 < i.1})`. Rewrite using `[← Set.image_insert_eq]`. Use `congr 1`. Use extensionality with `j`. Simplify using `only [Set.mem_insert_iff, Set.mem_setOf_eq, Fin.ext_iff]`.

Use linear arithmetic over natural numbers and integers. Unfold `FlagG.Xa at hv ⊢`. Rewrite `hv` using `[hset, Submodule.mem_span_insert]`. Conclude with `hv`.
-/
theorem xa_succ_decomp {T : E} (G : FlagG S r T) (i : Fin r) {v : S.V} (hv : v ∈ G.Xa (i.val + 1)) :
    ∃ c : E, ∃ w ∈ G.Xa i.val, v = c • G.e i + w := by
  have hset : G.e '' {j : Fin r | j.1 < i.1 + 1} = insert (G.e i) (G.e '' {j | j.1 < i.1}) := by
    rw [← Set.image_insert_eq]
    congr 1
    ext j
    simp only [Set.mem_insert_iff, Set.mem_setOf_eq, Fin.ext_iff]
    omega
  unfold FlagG.Xa at hv ⊢
  rw [hset, Submodule.mem_span_insert] at hv
  exact hv

/- English proof (translation)
Take `⟨c, w, hw, rfl⟩` from `xa_succ_decomp G i ha`. Rewrite using `[add_assoc, coefX_single_add G i c (Submodule.add_mem _ hw hb), coefX_single_add G i c hw]`.
-/
theorem coefX_add_low {T : E} (G : FlagG S r T) (i : Fin r) {a b : S.V} (ha : a ∈ G.Xa (i.val + 1))
    (hb : b ∈ G.Xa i.val) : G.coefX (a + b) i = G.coefX a i := by
  obtain ⟨c, w, hw, rfl⟩ := xa_succ_decomp G i ha
  rw [add_assoc, coefX_single_add G i c (Submodule.add_mem _ hw hb), coefX_single_add G i c hw]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Rewrite using `[FlagG.Xa, Submodule.span_le]`. Introduce and unpack `_ ⟨j, hj, rfl⟩`. Conclude with `absurd hj (Nat.not_lt_zero _)`.

Consider the case `succ k ih`. Rewrite using `[FlagG.Xa, Submodule.span_le]`. Introduce and unpack `_ ⟨j, hj, rfl⟩`. Establish `hj' : j.1 ≤ k` using `Nat.lt_succ_iff.mp hj`. Establish `h1 : G'.e j ∈ G'.Xa (k + 1)` using `Submodule.subset_span ⟨j, hj, rfl⟩`.

Establish `h2 : G'.e j - G.e j ∈ G'.Xa (k + 1)` using `xa_mono G' (Nat.le_succ k) (ih (xa_mono G hj' (h j)))`. Establish `h3` using `Submodule.sub_mem _ h1 h2`. Rewrite `h3` using `[sub_sub_cancel]`. Conclude with `h3`.
-/
theorem xa_le_of {T T' : E} {G : FlagG S r T} {G' : FlagG S r T'}
    (h : ∀ a : Fin r, G'.e a - G.e a ∈ G.Xa a.val) (k : ℕ) : G.Xa k ≤ G'.Xa k := by
  induction k with
  | zero =>
    rw [FlagG.Xa, Submodule.span_le]
    rintro _ ⟨j, hj, rfl⟩
    exact absurd hj (Nat.not_lt_zero _)
  | succ k ih =>
    rw [FlagG.Xa, Submodule.span_le]
    rintro _ ⟨j, hj, rfl⟩
    have hj' : j.1 ≤ k := Nat.lt_succ_iff.mp hj
    have h1 : G'.e j ∈ G'.Xa (k + 1) := Submodule.subset_span ⟨j, hj, rfl⟩
    have h2 : G'.e j - G.e j ∈ G'.Xa (k + 1) :=
      xa_mono G' (Nat.le_succ k) (ih (xa_mono G hj' (h j)))
    have h3 := Submodule.sub_mem _ h1 h2
    rw [sub_sub_cancel] at h3
    exact h3

/- English proof (translation)
Take `⟨c, w, hw, rfl⟩` from `xa_succ_decomp G i hv`. Establish `hle` using `xa_le_of h i.val`. Establish `h1 : c • G.e i + w = c • G'.e i + (w - c • (G'.e i - G.e i))`. Rewrite using `[smul_sub]`. Normalize the expressions using the abelian group laws.

Rewrite using `[coefX_single_add G i c hw, h1, coefX_single_add G' i c (hle (Submodule.sub_mem _ hw (Submodule.smul_mem _ _ (h i))))]`.
-/
theorem coefX_eq_of {T T' : E} {G : FlagG S r T} {G' : FlagG S r T'}
    (h : ∀ a : Fin r, G'.e a - G.e a ∈ G.Xa a.val) (i : Fin r) {v : S.V} (hv : v ∈ G.Xa (i.val + 1)) :
    G'.coefX v i = G.coefX v i := by
  obtain ⟨c, w, hw, rfl⟩ := xa_succ_decomp G i hv
  have hle := xa_le_of h i.val
  have h1 : c • G.e i + w = c • G'.e i + (w - c • (G'.e i - G.e i)) := by
    rw [smul_sub]
    abel
  rw [coefX_single_add G i c hw, h1,
    coefX_single_add G' i c (hle (Submodule.sub_mem _ hw (Submodule.smul_mem _ _ (h i))))]

/- English proof (translation)
Take `⟨_, hflag, hperp⟩` from `hY`. Distinguish the cases in `hi : i.val + 1 < r`. Establish `hfv : G.fvec i.succ = G.e ⟨i.val + 1, hi⟩`. Unfold `FlagG.fvec`. Establish `h0 : i.succ = Fin.castSucc ⟨i.val + 1, hi⟩` using `Fin.ext rfl`.

Rewrite using `[h0, Fin.snoc_castSucc]`. Rewrite using `[hfv]`. Establish `h1` using `hflag (i.val + 2) (by omega) (by omega) _ (e_mem_xa G ⟨i.val + 1, hi⟩)`. Simplify using `using h1`. Establish `hir : i.val + 1 = r` using `by omega`.

Establish `hfv : G.fvec i.succ = G.z`. Unfold `FlagG.fvec`. Establish `h0 : i.succ = Fin.last r` using `Fin.ext (by simp [hir])`. Rewrite using `[h0, Fin.snoc_last]`. Rewrite using `[hfv, hir, xa_r]`.

Conclude with `hperp _ (z_mem_perp G)`.
-/
theorem fvec_succ_image_mem {T : E} {G : FlagG S r T} {Y : S.V →ₗ[E] S.V} (hY : Y ∈ G.LieN) (i : Fin r) :
    Y (G.fvec i.succ) ∈ G.Xa (i.val + 1) := by
  obtain ⟨_, hflag, hperp⟩ := hY
  by_cases hi : i.val + 1 < r
  · have hfv : G.fvec i.succ = G.e ⟨i.val + 1, hi⟩ := by
      unfold FlagG.fvec
      have h0 : i.succ = Fin.castSucc ⟨i.val + 1, hi⟩ := Fin.ext rfl
      rw [h0, Fin.snoc_castSucc]
    rw [hfv]
    have h1 := hflag (i.val + 2) (by omega) (by omega) _ (e_mem_xa G ⟨i.val + 1, hi⟩)
    simpa using h1
  · have hir : i.val + 1 = r := by omega
    have hfv : G.fvec i.succ = G.z := by
      unfold FlagG.fvec
      have h0 : i.succ = Fin.last r := Fin.ext (by simp [hir])
      rw [h0, Fin.snoc_last]
    rw [hfv, hir, xa_r]
    exact hperp _ (z_mem_perp G)

/- English proof (translation)
Take `⟨hU, hflag, hperp⟩` from `hY`. Establish `he : ∀ a : Fin r, G'.e a - G.e a ∈ G.Xa a.val`. Introduce `a`. Establish `h1` using `h a.castSucc`. Simplify `h1` using `[FlagG.fvec, Fin.snoc_castSucc]`.

Unfold `FlagG.ell`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `h1 : Y (G.fvec i.succ) ∈ G.Xa (i.val + 1)` using `fvec_succ_image_mem ⟨hU, hflag, hperp⟩ i`. Establish `h2 : Y (G'.fvec i.succ - G.fvec i.succ) ∈ G.Xa i.val`. Establish `h0` using `hflag (i.val + 1) (by omega) (by omega) _ (h i.succ)`.

Simplify using `using h0`. Establish `h3 : Y (G'.fvec i.succ) = Y (G.fvec i.succ) + Y (G'.fvec i.succ - G.fvec i.succ)`. Rewrite using `[map_sub]`. Normalize the expressions using the abelian group laws. Rewrite using `[h3, coefX_eq_of he i (Submodule.add_mem _ h1 (xa_mono G (Nat.le_succ _) h2)), coefX_add_low G i h1 h2]`.
-/
theorem ell_eq_of {T T' : E} {G : FlagG S r T} {G' : FlagG S r T'}
    (h : ∀ i : Fin (r + 1), G'.fvec i - G.fvec i ∈ G.Xa i.val) {Y : S.V →ₗ[E] S.V} (hY : Y ∈ G.LieN) :
    G'.ell Y = G.ell Y := by
  obtain ⟨hU, hflag, hperp⟩ := hY
  have he : ∀ a : Fin r, G'.e a - G.e a ∈ G.Xa a.val := by
    intro a
    have h1 := h a.castSucc
    simpa [FlagG.fvec, Fin.snoc_castSucc] using h1
  unfold FlagG.ell
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : Y (G.fvec i.succ) ∈ G.Xa (i.val + 1) := fvec_succ_image_mem ⟨hU, hflag, hperp⟩ i
  have h2 : Y (G'.fvec i.succ - G.fvec i.succ) ∈ G.Xa i.val := by
    have h0 := hflag (i.val + 1) (by omega) (by omega) _ (h i.succ)
    simpa using h0
  have h3 : Y (G'.fvec i.succ) = Y (G.fvec i.succ) + Y (G'.fvec i.succ - G.fvec i.succ) := by
    rw [map_sub]
    abel
  rw [h3, coefX_eq_of he i (Submodule.add_mem _ h1 (xa_mono G (Nat.le_succ _) h2)),
    coefX_add_low G i h1 h2]

/- English proof (translation)
Introduce `Y hY`. Establish `hfv : ∀ i : Fin (r + 1), F'.fl.fvec i - F.fl.fvec i ∈ F.fl.Xa i.val`. Introduce `i`. Use `Fin.lastCases ?_ (fun a => ?_) i` and prove the remaining obligations. Simplify using `only [FlagG.fvec, Fin.snoc_last, Fin.val_last]`.

Rewrite using `[Xflag_r]`. Conclude with `h.2`. Simplify using `only [FlagG.fvec, Fin.snoc_castSucc, Fin.coe_castSucc]`. Conclude with `h.1 a`. Unfold `FlagG.dpsi`.

Rewrite using `[ell_eq_of hfv hY.1]`.
-/
theorem relevant_of_inSF (K : Type) [Field K] [Algebra K E] {T T' : E} {F : LFlag S r T}
    {F' : LFlag S r T'} (h : InSF F F') : Relevant K F.fl F'.fl := by
  intro Y hY
  have hfv : ∀ i : Fin (r + 1), F'.fl.fvec i - F.fl.fvec i ∈ F.fl.Xa i.val := by
    intro i
    refine Fin.lastCases ?_ (fun a => ?_) i
    · simp only [FlagG.fvec, Fin.snoc_last, Fin.val_last]
      rw [Xflag_r]
      exact h.2
    · simp only [FlagG.fvec, Fin.snoc_castSucc, Fin.coe_castSucc]
      exact h.1 a
  unfold FlagG.dpsi
  rw [ell_eq_of hfv hY.1]

end Gen

section D7

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Introduce `F0 Λ hΛ x hx`. Conclude with `relevant_of_inSF _ hx`.
-/
theorem termInSRel_main (D : D7) (u u' : D.what₂.Word) : TermInSRel D u u' := by
  intro F0 Λ hΛ x hx
  exact relevant_of_inSF _ hx

end D7

end PI.UnitaryGroupMassFormula.InSRelevantW
