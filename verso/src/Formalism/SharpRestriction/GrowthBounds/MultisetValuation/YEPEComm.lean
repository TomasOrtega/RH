import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.AofUpdate

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] {X : Sys p}

def yE (hL : LinD X) (v : X.Pl) : Module.End X.G.Kf (X.Fm 0) :=
  { toFun := X.yv v, map_add' := hL.yv_add v, map_smul' := fun a F => hL.yv_smul v a F }

def PE (hL : LinD X) (vs : List X.Pl) : Module.End X.G.Kf (X.Fm 0) := (vs.map (yE hL)).prod

/- English proof (translation)
The claim follows from `LinearMap.ext fun F => hL.yv_comm v v' F`.
-/
theorem yE_comm (hL : LinD X) (v v' : X.Pl) : Commute (yE hL v) (yE hL v') :=
  LinearMap.ext fun F => hL.yv_comm v v' F

/- English proof (translation)
Apply `Commute.list_prod_right` to reduce the goal to its premises. Introduce `y hy`. Take `⟨w, _, rfl⟩` from `List.mem_map.1 hy`. Conclude with `yE_comm hL v w`.
-/
theorem yE_PE_comm (hL : LinD X) (v : X.Pl) (ws : List X.Pl) : Commute (yE hL v) (PE hL ws) := by
  apply Commute.list_prod_right
  intro y hy
  obtain ⟨w, _, rfl⟩ := List.mem_map.1 hy
  exact yE_comm hL v w

/- English proof (translation)
Apply `Commute.list_prod_left` to reduce the goal to its premises. Introduce `x hx`. Take `⟨v, _, rfl⟩` from `List.mem_map.1 hx`. Conclude with `yE_PE_comm hL v ws`.
-/
theorem PE_comm (hL : LinD X) (vs ws : List X.Pl) : Commute (PE hL vs) (PE hL ws) := by
  apply Commute.list_prod_left
  intro x hx
  obtain ⟨v, _, rfl⟩ := List.mem_map.1 hx
  exact yE_PE_comm hL v ws

/- English proof (translation)
Simplify using `[PE]`.
-/
theorem PE_cons (hL : LinD X) (v : X.Pl) (vs : List X.Pl) : PE hL (v :: vs) = yE hL v * PE hL vs := by
  simp [PE]

/- English proof (translation)
Simplify using `[PE]`.
-/
theorem PE_append (hL : LinD X) (vs ws : List X.Pl) : PE hL (vs ++ ws) = PE hL vs * PE hL ws := by
  simp [PE]

/- English proof (translation)
Apply `List.Perm.prod_eq' (h.map _)` to reduce the goal to its premises. Apply `List.pairwise_of_forall_mem_list` to reduce the goal to its premises. Introduce `a ha b hb`. Take `⟨v, _, rfl⟩` from `List.mem_map.1 ha`. Take `⟨w, _, rfl⟩` from `List.mem_map.1 hb`.

Conclude with `yE_comm hL v w`.
-/
theorem PE_perm (hL : LinD X) {vs ws : List X.Pl} (h : vs.Perm ws) : PE hL vs = PE hL ws := by
  apply List.Perm.prod_eq' (h.map _)
  apply List.pairwise_of_forall_mem_list
  intro a ha b hb
  obtain ⟨v, _, rfl⟩ := List.mem_map.1 ha
  obtain ⟨w, _, rfl⟩ := List.mem_map.1 hb
  exact yE_comm hL v w

/- English proof (translation)
Proceed by induction on `vs with`. Consider the case `nil => intro F hF`. Simplify `hF` using `[PE]`. Consider the case `cons v vs ih`. Introduce `F hF`.

Rewrite using `[PE_cons]`. Conclude with `hy v _ (ih F hF)`.
-/
theorem PE_mem (hL : LinD X) {S : Set (X.Fm 0)} (hy : ∀ v, ∀ F ∈ S, X.yv v F ∈ S) (vs : List X.Pl) :
    ∀ F ∈ S, PE hL vs F ∈ S := by
  induction vs with
  | nil => intro F hF; simpa [PE] using hF
  | cons v vs ih =>
    intro F hF
    rw [PE_cons]
    exact hy v _ (ih F hF)

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => intro F hF`. Simplify using `using hF`. Consider the case `succ n ih`. Introduce `F hF`.

Rewrite using `[pow_succ']`. Conclude with `PE_mem hL hy vs _ (ih F hF)`.
-/
theorem PE_pow_mem (hL : LinD X) {S : Set (X.Fm 0)} (hy : ∀ v, ∀ F ∈ S, X.yv v F ∈ S) (vs : List X.Pl) (n : ℕ) :
    ∀ F ∈ S, (PE hL vs ^ n) F ∈ S := by
  induction n with
  | zero => intro F hF; simpa using hF
  | succ n ih =>
    intro F hF
    rw [pow_succ']
    exact PE_mem hL hy vs _ (ih F hF)

/- English proof (translation)
Proceed by induction on `vs with`. Consider the case `nil => simp [PE]`. Consider the case `cons v vs ih`. Rewrite using `[PE_cons, (yE_PE_comm hL v vs).mul_pow, List.foldr_cons, ih, Module.End.mul_apply, Module.End.pow_apply (yE hL v)]`. Both sides reduce to the same expression.
-/
theorem fold_eq (hL : LinD X) (n : ℕ) (vs : List X.Pl) (z : X.Fm 0) :
    vs.foldr (fun v F' => (X.yv v)^[n] F') z = (PE hL vs ^ n) z := by
  induction vs with
  | nil => simp [PE]
  | cons v vs ih =>
    rw [PE_cons, (yE_PE_comm hL v vs).mul_pow, List.foldr_cons, ih, Module.End.mul_apply,
      Module.End.pow_apply (yE hL v)]
    rfl

/- English proof (translation)
Introduce `F hF`. Unfold `Sys.FQ at hF ⊢`. Proceed by induction on `hF using Submodule.span_induction with`. Consider the case `zero`. Use `hL.yv_smul v 0 0` as an intermediate fact.

Simplify using `only [zero_smul] at this`. Rewrite using `[this]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy' => rw [hL.yv_add]`. Conclude with `Submodule.add_mem _ hx hy'`.

Consider the case `smul c x _ hx => rw [hL.yv_smul]`. Conclude with `Submodule.smul_mem _ _ hx`. Consider the case `mem x hx => exact Submodule.subset_span (hy v x hx)`.
-/
theorem yv_FQ (hL : LinD X) (hy : ∀ v, ∀ F ∈ X.Int 0, X.yv v F ∈ X.Int 0) (v : X.Pl) :
    ∀ F ∈ X.FQ 0, X.yv v F ∈ X.FQ 0 := by
  intro F hF
  unfold Sys.FQ at hF ⊢
  induction hF using Submodule.span_induction with
  | zero =>
    have := hL.yv_smul v 0 0
    simp only [zero_smul] at this
    rw [this]; exact Submodule.zero_mem _
  | add x y _ _ hx hy' => rw [hL.yv_add]; exact Submodule.add_mem _ hx hy'
  | smul c x _ hx => rw [hL.yv_smul]; exact Submodule.smul_mem _ _ hx
  | mem x hx => exact Submodule.subset_span (hy v x hx)

variable (X)

def PrS (j : ℕ) (vs : List X.Pl) : ℤ :=
  ∑ v, if v ∈ vs then PrZ X.t X.G.P.r (X.G.P.lam0 v) (X.w v) j else 0

variable {X}

/- English proof (translation)
Unfold `PrS`. Establish `: PrZ X.t X.G.P.r (X.G.P.lam0 v) (X.w v) j = ∑ v', if v' = v then PrZ X.t X.G.P.r (X.G.P.lam0 v') (X.w v') j else 0`. Rewrite using `[Finset.sum_ite_eq' univ v]`. Simplify using the standard rewrite rules. Rewrite using `[this, ← Finset.sum_add_distrib]`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `v' _`. Distinguish the cases in `h : v' = v`. Substitute `h` using the available equality. Simplify using `[hv]`.

Simplify using `[h]`.
-/
theorem PrS_cons (j : ℕ) (v : X.Pl) (vs : List X.Pl) (hv : v ∉ vs) :
    PrS X j (v :: vs) = PrS X j vs + PrZ X.t X.G.P.r (X.G.P.lam0 v) (X.w v) j := by
  unfold PrS
  have : PrZ X.t X.G.P.r (X.G.P.lam0 v) (X.w v) j =
      ∑ v', if v' = v then PrZ X.t X.G.P.r (X.G.P.lam0 v') (X.w v') j else 0 := by
    rw [Finset.sum_ite_eq' univ v]
    simp
  rw [this, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v' _
  by_cases h : v' = v
  · subst h
    simp [hv]
  · simp [h]

/- English proof (translation)
Proceed by induction on `vs with`. Consider the case `nil => simp [ZL, PrS, PE]`. Consider the case `cons v vs ih`. Rewrite `hnd` using `[List.nodup_cons]`. Use `show X.Zop v (u v) (m v) (j + 1) (ZL X u m (j + 1) vs (X.chainK (j + 1) F)) = _`.

Rewrite using `[ih hnd.2, Zop_smul hL, hCi v _ (PE_mem hL (S := (X.FQ 0 : Set (X.Fm 0))) hyQ vs F hF), smul_smul, ← zpow_add₀ hp, PrS_cons _ _ _ hnd.1, PE_cons]`. Both sides reduce to the same expression.
-/
theorem ZL_chain (hp : (p : X.G.Kf) ≠ 0) (hL : LinD X) (u m : X.Pl → ℕ → X.G.Kf) (j : ℕ)
    (hCi : ∀ v, ∀ F ∈ X.FQ 0, X.Zop v (u v) (m v) (j + 1) (X.chainK (j + 1) F) =
      ((p : X.G.Kf) ^ (PrZ X.t X.G.P.r (X.G.P.lam0 v) (X.w v) (j + 1))) • X.chainK (j + 1) (X.yv v F))
    (hyQ : ∀ v, ∀ F ∈ X.FQ 0, X.yv v F ∈ X.FQ 0) (vs : List X.Pl) (hnd : vs.Nodup) (F : X.Fm 0) (hF : F ∈ X.FQ 0) :
    ZL X u m (j + 1) vs (X.chainK (j + 1) F) =
      ((p : X.G.Kf) ^ (PrS X (j + 1) vs)) • X.chainK (j + 1) (PE hL vs F) := by
  induction vs with
  | nil => simp [ZL, PrS, PE]
  | cons v vs ih =>
    rw [List.nodup_cons] at hnd
    show X.Zop v (u v) (m v) (j + 1) (ZL X u m (j + 1) vs (X.chainK (j + 1) F)) = _
    rw [ih hnd.2, Zop_smul hL, hCi v _ (PE_mem hL (S := (X.FQ 0 : Set (X.Fm 0))) hyQ vs F hF), smul_smul,
      ← zpow_add₀ hp, PrS_cons _ _ _ hnd.1, PE_cons]
    rfl

/- English proof (translation)
The claim follows from `(vGeK_iff X).2 ⟨1, by simp⟩`.
-/
theorem vGeK_vsc (g : ℝ) : X.vGeK (X.vsc g) g := (vGeK_iff X).2 ⟨1, by simp⟩

def bbJ (X : Sys p) (Lv : List X.Pl) (Gn G0n : X.Pl → ℕ → ℝ) (Q : ℕ → X.Pl → Bool) (j : ℕ) : ℝ :=
  ∑ v, (if v ∈ Lv.filter (Q j) then Gn v (j + 1) else G0n v (j + 1)) - X.dG j -
        (PrS X (j + 1) (Lv.filter (Q j)) : ℝ)

/- English proof (translation)
Introduce `m'`. Proceed by induction on `m' with`. Consider the case `zero`. Introduce `_ F1 hF1`. Simplify using `only [pow_zero, Finset.range_zero, Finset.sum_empty]`.

Conclude with `(vGe_zero_iff X).2 hF1`. Consider the case `succ m' ih`. Introduce `hm F1 hF1`. Establish `hj : m' < X.mm` using `hm`. Use `set B := Lv.filter (Q m') with hB`.

Use `set C := Lv.filter (fun x => !Q m' x) with hC`. Establish `e1 : PE hL Lv = PE hL B * PE hL C`. Rewrite using `[← PE_append]`. Conclude with `(PE_perm hL (List.filter_append_perm (Q m') Lv)).symm`. Establish `e2 : PE hL Lv ^ (m' + 1) = PE hL B * (PE hL Lv ^ m' * PE hL C)`.

Establish `e0 : PE hL Lv ^ (m' + 1) = (PE hL B * PE hL C) * PE hL Lv ^ m'` using `by rw [pow_succ', ← e1]`. Rewrite using `[e0, mul_assoc, ((PE_comm hL C Lv).pow_right m').eq]`. Establish `hF1' : PE hL C F1 ∈ X.Int 0` using `PE_mem hL (S := (X.Int 0 : Set (X.Fm 0))) hy C F1 hF1`. Use `set W := (PE hL Lv ^ m') (PE hL C F1) with hW`. Establish `hWi : W ∈ X.Int 0` using `PE_pow_mem hL (S := (X.Int 0 : Set (X.Fm 0))) hy Lv m' _ hF1'`.

Establish `hWQ : W ∈ X.FQ 0` using `Submodule.subset_span hWi`. Establish `hBnd : B.Nodup` using `hnd.filter _`. Establish `e3` using `ZL_chain hp hL u m m' (fun v => hCi v m' hj) (yv_FQ hL hy) B hBnd W hWQ`. Establish `e4 : X.chainK (m' + 1) ((PE hL Lv ^ (m' + 1)) F1) = ((p : X.G.Kf) ^ (-(PrS X (m' + 1) B))) • ZL X u m (m' + 1) B (X.chainK (m' + 1) W)`. Rewrite using `[e3, smul_smul, ← zpow_add₀ hp, neg_add_cancel, zpow_zero, one_smul, e2]`.

Both sides reduce to the same expression. Take `⟨G', hG', hG'e⟩` from `(vGe_iff X).1 (ih (le_of_lt hj) _ hF1')`. Establish `e5 : X.chainK (m' + 1) W = X.vsc (∑ j ∈ range m', bbJ X Lv Gn G0n Q j) • X.Kz m' G'` using `by show X.Kz m' (X.chainK m' W) = _`. Rewrite using `[← hG'e, map_smul]`. Rewrite using `[e4, e5, ZL_smul hL]`.

Establish `hb` using `ZL_bound hfr hL hF hE u m m' hj hu (fun v => hc0 v m' hj) (fun v => hcr v m' hj) B hBnd (fun v => if v ∈ B then Gn v (m' + 1) else G0n v (m' + 1)) (fun v hv => by simp only [hv, if_true]; exact h1 v (List.mem_of_mem_filter hv) m' hj) (fun v hv => by simp only [hv, if_false]; exac …`. Establish `h3` using `vGe_smul X hfr (vGeK_ppow X hfr (-(PrS X (m' + 1) B))) (vGe_smul X hfr (vGeK_vsc (∑ j ∈ range m', bbJ X Lv Gn G0n Q j)) hb)`. Rewrite using `[Finset.sum_range_succ]`. Use `vGe_mono X hfr (le_of_eq ?_) h3` and prove the remaining obligations. Use `conv_lhs => rw [bbJ]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem main_ind {Y : Pend X} (hfr : IsFractionRing X.G.O X.G.Kf) (hp : (p : X.G.Kf) ≠ 0) (hL : LinD X)
    (hF : FormB X Y) (hE : EntCondition X Y) (u m : X.Pl → ℕ → X.G.Kf)
    (hu : ∀ v, ∀ l ∈ Icc 1 X.mm, X.vEqK (u v l) 0)
    (hc0 : ∀ v, ∀ j < X.mm, ∀ l ≤ X.G.P.r, X.vGeK (X.cl v (m v) (j + 1) l) 0)
    (hcr : ∀ v, ∀ j < X.mm, X.vGeK (X.cl v (m v) (j + 1) X.G.P.r) (X.alEven v))
    (hCi : ∀ v, ∀ j < X.mm, ∀ F ∈ X.FQ 0, X.Zop v (u v) (m v) (j + 1) (X.chainK (j + 1) F) =
      ((p : X.G.Kf) ^ (PrZ X.t X.G.P.r (X.G.P.lam0 v) (X.w v) (j + 1))) • X.chainK (j + 1) (X.yv v F))
    (hy : ∀ v, ∀ F ∈ X.Int 0, X.yv v F ∈ X.Int 0)
    (Lv : List X.Pl) (hnd : Lv.Nodup) (Gn G0n : X.Pl → ℕ → ℝ) (Q : ℕ → X.Pl → Bool)
    (h1 : ∀ v ∈ Lv, ∀ j < X.mm, Gn v (j + 1) ≤ X.gv v (j + 1))
    (h2 : ∀ v, ∀ j < X.mm, Y.LowAt j v (G0n v (j + 1))) :
    ∀ m' ≤ X.mm, ∀ F1 ∈ X.Int 0, X.vGe m' (X.chainK m' ((PE hL Lv ^ m') F1))
      (∑ j ∈ range m', bbJ X Lv Gn G0n Q j) := by
  intro m'
  induction m' with
  | zero =>
    intro _ F1 hF1
    simp only [pow_zero, Finset.range_zero, Finset.sum_empty]
    exact (vGe_zero_iff X).2 hF1
  | succ m' ih =>
    intro hm F1 hF1
    have hj : m' < X.mm := hm
    set B := Lv.filter (Q m') with hB
    set C := Lv.filter (fun x => !Q m' x) with hC
    have e1 : PE hL Lv = PE hL B * PE hL C := by
      rw [← PE_append]
      exact (PE_perm hL (List.filter_append_perm (Q m') Lv)).symm
    have e2 : PE hL Lv ^ (m' + 1) = PE hL B * (PE hL Lv ^ m' * PE hL C) := by
      have e0 : PE hL Lv ^ (m' + 1) = (PE hL B * PE hL C) * PE hL Lv ^ m' := by rw [pow_succ', ← e1]
      rw [e0, mul_assoc, ((PE_comm hL C Lv).pow_right m').eq]
    have hF1' : PE hL C F1 ∈ X.Int 0 := PE_mem hL (S := (X.Int 0 : Set (X.Fm 0))) hy C F1 hF1
    set W := (PE hL Lv ^ m') (PE hL C F1) with hW
    have hWi : W ∈ X.Int 0 := PE_pow_mem hL (S := (X.Int 0 : Set (X.Fm 0))) hy Lv m' _ hF1'
    have hWQ : W ∈ X.FQ 0 := Submodule.subset_span hWi
    have hBnd : B.Nodup := hnd.filter _
    have e3 := ZL_chain hp hL u m m' (fun v => hCi v m' hj) (yv_FQ hL hy) B hBnd W hWQ
    have e4 : X.chainK (m' + 1) ((PE hL Lv ^ (m' + 1)) F1) =
        ((p : X.G.Kf) ^ (-(PrS X (m' + 1) B))) • ZL X u m (m' + 1) B (X.chainK (m' + 1) W) := by
      rw [e3, smul_smul, ← zpow_add₀ hp, neg_add_cancel, zpow_zero, one_smul, e2]
      rfl
    obtain ⟨G', hG', hG'e⟩ := (vGe_iff X).1 (ih (le_of_lt hj) _ hF1')
    have e5 : X.chainK (m' + 1) W = X.vsc (∑ j ∈ range m', bbJ X Lv Gn G0n Q j) • X.Kz m' G' := by
      show X.Kz m' (X.chainK m' W) = _
      rw [← hG'e, map_smul]
    rw [e4, e5, ZL_smul hL]
    have hb := ZL_bound hfr hL hF hE u m m' hj hu (fun v => hc0 v m' hj) (fun v => hcr v m' hj) B hBnd
      (fun v => if v ∈ B then Gn v (m' + 1) else G0n v (m' + 1))
      (fun v hv => by simp only [hv, if_true]; exact h1 v (List.mem_of_mem_filter hv) m' hj)
      (fun v hv => by simp only [hv, if_false]; exact h2 v m' hj) G' hG'
    have h3 := vGe_smul X hfr (vGeK_ppow X hfr (-(PrS X (m' + 1) B))) (vGe_smul X hfr (vGeK_vsc (∑ j ∈ range m', bbJ X Lv Gn G0n Q j)) hb)
    rw [Finset.sum_range_succ]
    refine vGe_mono X hfr (le_of_eq ?_) h3
    conv_lhs => rw [bbJ]
    push_cast
    ring

end Formalism.MainNotions.FormalGroupSystem.Pf
