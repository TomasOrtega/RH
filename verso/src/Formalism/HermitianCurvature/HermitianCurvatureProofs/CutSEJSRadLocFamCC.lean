import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEJSRadLocCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.JfBetaAdjCOfLemmaBNorm

open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE.FamCC

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.JFxG

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/- English proof (translation)
Introduce `j`. Proceed by induction on `j with`. Consider the case `zero`. Introduce `bs p hp`. Establish `hm : ContDiff ℝ ∞ (fun p : ℂ × ((Fin 0 → Mat k r) × Mat k r) => (p.1, p.2.2))` using `contDiff_fst.prodMk (contDiff_snd.comp contDiff_snd)`.

Conclude with `(hf.contDiffAt (hU.mem_nhds hp)).comp p hm.contDiffAt`. Consider the case `succ j ih`. Introduce `bs p hp`. Establish `hsh : ContDiff ℝ ∞ (fun q : (ℂ × ((Fin (j + 1) → Mat k r) × Mat k r)) × Mat k r => (q.1.1, ((fun i : Fin j => q.1.2.1 i.succ), q.2)))` using `(contDiff_fst.comp contDiff_fst).prodMk ((contDiff_pi.2 fun (i : Fin j) => (contDiff_apply ℝ (Mat k r) i.succ).comp (contDiff_fst.comp (contDiff_snd.comp contDiff_fst))).prodMk contDiff_snd)`. Establish `h1 : ContDiffAt ℝ ∞ (Function.uncurry fun (q : ℂ × ((Fin (j + 1) → Mat k r) × Mat k r)) (g : Mat k r) => Phi (fun x => f (q.1, x)) j (fun i => bs i.succ) ((fun i => q.2.1 i.succ), g)) (p, p.2.2)` using `ContDiffAt.comp (g := fun q : ℂ × ((Fin j → Mat k r) × Mat k r) => Phi (fun x => f (q.1, x)) j (fun i => bs i.succ) q.2) (p, p.2.2) (ih (fun i => bs i.succ) (p.1, ((fun i => p.2.1 i.succ), p.2.2)) hp) hsh.contDiffAt`.

Establish `h2` using `ContDiffAt.fderiv h1 (contDiffAt_snd.comp p contDiffAt_snd) top_add_one_le`. Establish `h3 : ContDiff ℝ ∞ (fun q : ℂ × ((Fin (j + 1) → Mat k r) × Mat k r) => vf (bs 0) (q.2.1 0) q.2.2)` using `vf_contDiff (bs 0) ((contDiff_apply ℝ (Mat k r) 0).comp (contDiff_fst.comp contDiff_snd)) (contDiff_snd.comp contDiff_snd)`. Conclude with `h2.clm_apply h3.contDiffAt`.
-/
theorem phiP_contDiffAt (f : ℂ × Mat k r → E) {U : Set (ℂ × Mat k r)} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) :
    ∀ (j : ℕ) (bs : Fin j → Bool) (p : ℂ × ((Fin j → Mat k r) × Mat k r)), (p.1, p.2.2) ∈ U →
      ContDiffAt ℝ ∞ (fun p : ℂ × ((Fin j → Mat k r) × Mat k r) => Phi (fun x => f (p.1, x)) j bs p.2) p := by
  intro j
  induction j with
  | zero =>
    intro bs p hp
    have hm : ContDiff ℝ ∞ (fun p : ℂ × ((Fin 0 → Mat k r) × Mat k r) => (p.1, p.2.2)) :=
      contDiff_fst.prodMk (contDiff_snd.comp contDiff_snd)
    exact (hf.contDiffAt (hU.mem_nhds hp)).comp p hm.contDiffAt
  | succ j ih =>
    intro bs p hp
    have hsh : ContDiff ℝ ∞ (fun q : (ℂ × ((Fin (j + 1) → Mat k r) × Mat k r)) × Mat k r =>
        (q.1.1, ((fun i : Fin j => q.1.2.1 i.succ), q.2))) :=
      (contDiff_fst.comp contDiff_fst).prodMk
        ((contDiff_pi.2 fun (i : Fin j) =>
          (contDiff_apply ℝ (Mat k r) i.succ).comp (contDiff_fst.comp (contDiff_snd.comp contDiff_fst))).prodMk
          contDiff_snd)
    have h1 : ContDiffAt ℝ ∞ (Function.uncurry fun (q : ℂ × ((Fin (j + 1) → Mat k r) × Mat k r)) (g : Mat k r) =>
        Phi (fun x => f (q.1, x)) j (fun i => bs i.succ) ((fun i => q.2.1 i.succ), g)) (p, p.2.2) :=
      ContDiffAt.comp (g := fun q : ℂ × ((Fin j → Mat k r) × Mat k r) =>
        Phi (fun x => f (q.1, x)) j (fun i => bs i.succ) q.2) (p, p.2.2)
        (ih (fun i => bs i.succ) (p.1, ((fun i => p.2.1 i.succ), p.2.2)) hp) hsh.contDiffAt
    have h2 := ContDiffAt.fderiv h1 (contDiffAt_snd.comp p contDiffAt_snd) top_add_one_le
    have h3 : ContDiff ℝ ∞ (fun q : ℂ × ((Fin (j + 1) → Mat k r) × Mat k r) => vf (bs 0) (q.2.1 0) q.2.2) :=
      vf_contDiff (bs 0) ((contDiff_apply ℝ (Mat k r) 0).comp (contDiff_fst.comp contDiff_snd))
        (contDiff_snd.comp contDiff_snd)
    exact h2.clm_apply h3.contDiffAt

/- English proof (translation)
Take `⟨ε, hε, hball⟩` from `Metric.isOpen_iff.1 hU p₀ hp₀`. Establish `hsub : Metric.closedBall p₀ (ε / 2) ⊆ U` using `(Metric.closedBall_subset_ball (by linarith)).trans hball`. Establish `hb : ∀ (j : ℕ) (bs : Fin j → Bool), ∃ c : ℝ, ∀ q ∈ Metric.closedBall p₀.1 (ε / 2) ×ˢ ((Set.pi Set.univ fun _ : Fin j => Box k r) ×ˢ Metric.closedBall p₀.2 (ε / 2)), ‖Phi (fun x => f (q.1, x)) j bs q.2‖ ≤ c`. Introduce `j bs`. Establish `hK : IsCompact (Metric.closedBall p₀.1 (ε / 2) ×ˢ ((Set.pi Set.univ fun _ : Fin j => Box k r) ×ˢ Metric.closedBall p₀.2 (ε / 2)))` using `(isCompact_closedBall _ _).prod ((isCompact_univ_pi fun _ => box_compact).prod (isCompact_closedBall _ _))`.

Use `hK.exists_bound_of_continuousOn fun q hq => ?_` and prove the remaining obligations. Establish `hqU : (q.1, q.2.2) ∈ U`. Apply `hsub` to reduce the goal to its premises. Rewrite using `[Metric.mem_closedBall, Prod.dist_eq]`. Conclude with `max_le (Metric.mem_closedBall.1 hq.1) (Metric.mem_closedBall.1 hq.2.2)`.

Conclude with `(phiP_contDiffAt f hU hf j bs q hqU).continuousAt.continuousWithinAt`. Use `choose c hcb using hb`. Use `⟨Metric.closedBall p₀ (ε / 2), Metric.closedBall_mem_nhds p₀ (by linarith), ∑ j : Fin (m + 1), ∑ bs : Fin j → Bool, |c j bs|, by positivity, ?_⟩` and prove the remaining obligations. Introduce `p hp hpG j hj bs Xs hL hB`. Establish `hpU : p ∈ U` using `hsub hp`.

Establish `hUt : IsOpen {x : Mat k r | (p.1, x) ∈ U}` using `hU.preimage (continuous_const.prodMk continuous_id)`. Establish `hft : ContDiffOn ℝ ∞ (fun x => f (p.1, x)) {x : Mat k r | (p.1, x) ∈ U}` using `hf.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun x hx => hx)`. Establish `hmem : p.2 ∈ {x : Mat k r | (p.1, x) ∈ U}` using `hpU`. Rewrite using `[W_eq_phi hUt hft (fun x hx hxG => hGf (p.1, x) hx hxG) j bs Xs hL p.2 hmem hpG]`. Establish `hpd : dist p p₀ ≤ ε / 2` using `Metric.mem_closedBall.1 hp`.

Rewrite `hpd` using `[Prod.dist_eq]`. Establish `hq : (p.1, (Xs, p.2)) ∈ Metric.closedBall p₀.1 (ε / 2) ×ˢ ((Set.pi Set.univ fun _ : Fin j => Box k r) ×ˢ Metric.closedBall p₀.2 (ε / 2))` using `⟨Metric.mem_closedBall.2 ((le_max_left _ _).trans hpd), fun i _ => hB i, Metric.mem_closedBall.2 ((le_max_right _ _).trans hpd)⟩`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem local_boundP {G : ℂ → Mat k r → E} (f : ℂ × Mat k r → E) {U : Set (ℂ × Mat k r)} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (hGf : ∀ p ∈ U, p.2 ∈ GV k r → G p.1 p.2 = f p) (m : ℕ) {p₀ : ℂ × Mat k r}
    (hp₀ : p₀ ∈ U) :
    ∃ V ∈ 𝓝 p₀, ∃ c : ℝ, 0 ≤ c ∧ ∀ p ∈ V, p.2 ∈ GV k r → ∀ (j : ℕ), j ≤ m → ∀ (bs : Fin j → Bool)
      (Xs : Fin j → Mat k r), (∀ i, inLie k r (Xs i)) → (∀ i, Xs i ∈ Box k r) →
        ‖W (List.ofFn fun i => (bs i, Xs i)) (G p.1) p.2‖ ≤ c := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU p₀ hp₀
  have hsub : Metric.closedBall p₀ (ε / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hb : ∀ (j : ℕ) (bs : Fin j → Bool), ∃ c : ℝ, ∀ q ∈ Metric.closedBall p₀.1 (ε / 2) ×ˢ
      ((Set.pi Set.univ fun _ : Fin j => Box k r) ×ˢ Metric.closedBall p₀.2 (ε / 2)),
      ‖Phi (fun x => f (q.1, x)) j bs q.2‖ ≤ c := by
    intro j bs
    have hK : IsCompact (Metric.closedBall p₀.1 (ε / 2) ×ˢ
        ((Set.pi Set.univ fun _ : Fin j => Box k r) ×ˢ Metric.closedBall p₀.2 (ε / 2))) :=
      (isCompact_closedBall _ _).prod ((isCompact_univ_pi fun _ => box_compact).prod (isCompact_closedBall _ _))
    refine hK.exists_bound_of_continuousOn fun q hq => ?_
    have hqU : (q.1, q.2.2) ∈ U := by
      apply hsub
      rw [Metric.mem_closedBall, Prod.dist_eq]
      exact max_le (Metric.mem_closedBall.1 hq.1) (Metric.mem_closedBall.1 hq.2.2)
    exact (phiP_contDiffAt f hU hf j bs q hqU).continuousAt.continuousWithinAt
  choose c hcb using hb
  refine ⟨Metric.closedBall p₀ (ε / 2), Metric.closedBall_mem_nhds p₀ (by linarith),
    ∑ j : Fin (m + 1), ∑ bs : Fin j → Bool, |c j bs|, by positivity, ?_⟩
  intro p hp hpG j hj bs Xs hL hB
  have hpU : p ∈ U := hsub hp
  have hUt : IsOpen {x : Mat k r | (p.1, x) ∈ U} :=
    hU.preimage (continuous_const.prodMk continuous_id)
  have hft : ContDiffOn ℝ ∞ (fun x => f (p.1, x)) {x : Mat k r | (p.1, x) ∈ U} :=
    hf.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun x hx => hx)
  have hmem : p.2 ∈ {x : Mat k r | (p.1, x) ∈ U} := hpU
  rw [W_eq_phi hUt hft (fun x hx hxG => hGf (p.1, x) hx hxG) j bs Xs hL p.2 hmem hpG]
  have hpd : dist p p₀ ≤ ε / 2 := Metric.mem_closedBall.1 hp
  rw [Prod.dist_eq] at hpd
  have hq : (p.1, (Xs, p.2)) ∈ Metric.closedBall p₀.1 (ε / 2) ×ˢ
      ((Set.pi Set.univ fun _ : Fin j => Box k r) ×ˢ Metric.closedBall p₀.2 (ε / 2)) :=
    ⟨Metric.mem_closedBall.2 ((le_max_left _ _).trans hpd), fun i _ => hB i,
      Metric.mem_closedBall.2 ((le_max_right _ _).trans hpd)⟩
  calc ‖Phi (fun x => f (p.1, x)) j bs (Xs, p.2)‖ ≤ |c j bs| := (hcb j bs _ hq).trans (le_abs_self _)
    _ = |c (⟨j, by omega⟩ : Fin (m + 1)) bs| := rfl
    _ ≤ ∑ bs' : Fin (⟨j, by omega⟩ : Fin (m + 1)) → Bool, |c (⟨j, by omega⟩ : Fin (m + 1)) bs'| :=
        Finset.single_le_sum (f := fun bs' => |c (⟨j, by omega⟩ : Fin (m + 1)) bs'|) (fun _ _ => abs_nonneg _)
          (Finset.mem_univ bs)
    _ ≤ ∑ j' : Fin (m + 1), ∑ bs' : Fin j' → Bool, |c j' bs'| :=
        Finset.single_le_sum (f := fun j' : Fin (m + 1) => ∑ bs' : Fin j' → Bool, |c j' bs'|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ _)

/- English proof (translation)
Establish `hS : IsCompact (K ×ˢ (C ∩ GV k r))` using `hK.prod (hC.inter_right B5.GV_closed)`. Establish `hl : ∀ p ∈ K ×ˢ (C ∩ GV k r), ∃ V, V ∈ 𝓝 p ∧ ∃ c : ℝ, 0 ≤ c ∧ ∀ q ∈ V, q.2 ∈ GV k r → ∀ (j : ℕ), j ≤ m → ∀ (bs : Fin j → Bool) (Xs : Fin j → Mat k r), (∀ i, inLie k r (Xs i)) → (∀ i, Xs i ∈ Box k r) → ‖W (List.ofFn fun i => (bs i, Xs i)) (G q.1) q.2‖ ≤ c` using `fun p hp => by`. Take `⟨U, f, hU, hpU, hf, hGf⟩` from `hloc p.1 hp.1 p.2 hp.2.2`. Take `⟨V, hV, c, hc0, hc⟩` from `local_boundP f hU hf hGf m (p₀ := (p.1, p.2)) hpU`. Conclude with `⟨V, hV, c, hc0, hc⟩`.

Use `choose! V hV c hc0 hc using hl`. Take `⟨s, hsS, hcov⟩` from `hS.elim_nhds_subcover V hV`. Establish `hsum0 : 0 ≤ ∑ x ∈ s, c x` using `Finset.sum_nonneg fun y hy => hc0 y (hsS y hy)`. Establish `hcW : ∀ t ∈ K, ∀ g ∈ C ∩ GV k r, ∀ (j : ℕ), j ≤ m → ∀ (bs : Fin j → Bool) (Xs : Fin j → Mat k r), (∀ i, inLie k r (Xs i)) → (∀ i, Xs i ∈ Box k r) → ‖W (List.ofFn fun i => (bs i, Xs i)) (G t) g‖ ≤ ∑ x ∈ s, c x`. Introduce `t ht g hg j hj bs Xs hL hB`.

Take `⟨x, hxs, hgx⟩` from `Set.mem_iUnion₂.1 (hcov (show (t, g) ∈ K ×ˢ (C ∩ GV k r) from ⟨ht, hg⟩))`. Conclude with `(hc x (hsS x hxs) (t, g) hgx hg.2 j hj bs Xs hL hB).trans (Finset.single_le_sum (fun y hy => hc0 y (hsS y hy)) hxs)`. Take `⟨cg, hcg⟩` from `(hC.inter_right B5.GV_closed).exists_bound_of_continuousOn (f := fun g : Mat k r => gN g ^ A) fun g hg => ((B6.gN_continuous.continuousAt).rpow_const (Or.inl (B6.gN_pos hg.2).ne')).continuousWithinAt`. Use `⟨|cg| * ∑ x ∈ s, c x, fun t ht => ⟨B5.ckOn_mono le_top (hck t ht), ?_⟩⟩` and prove the remaining obligations. Introduce `u v hu hv hlen g hg`.

Rewrite using `[dLR_eq]`. Establish `hmemlr : ∀ y ∈ lr u v, unitLie k r y.2`. Introduce `y hy`. Simplify using `only [lr, List.mem_append, List.mem_map] at hy`. Break down `hy with ⟨X, hX, rfl⟩ | ⟨X, hX, rfl⟩` into its components or cases.

Conclude with `hu X hX`. Conclude with `hv X hX`. Distinguish the cases in `hgC : g ∈ C`. Establish `hw : lr u v = List.ofFn fun i : Fin (lr u v).length => ((lr u v)[i].1, (lr u v)[i].2)`. Simplify using the standard rewrite rules.

Establish `hlen' : (lr u v).length ≤ m` using `by simp [lr]; omega`. Establish `hb` using `hcW t ht g ⟨hgC, hg⟩ _ hlen' (fun i => (lr u v)[i].1) (fun i => (lr u v)[i].2) (fun i => (hmemlr _ (List.getElem_mem _)).1) (fun i => mem_box (hmemlr _ (List.getElem_mem _)).2)`. Rewrite `hb` using `[← hw]`. Establish `hg1 : gN g ^ A ≤ |cg|`. Use `hcg g ⟨hgC, hg⟩` as an intermediate fact.

Rewrite `this` using `[Real.norm_eq_abs]`. Conclude with `(le_abs_self _).trans (this.trans (le_abs_self _))`. Conclude with `mul_le_mul hg1 hb (norm_nonneg _) (abs_nonneg _)`. Establish `h0` using `W_local_zero hC.isClosed.isOpen_compl (fun x hx _ => by by_contra h; exact hx (hsupp t ht x h)) (lr u v) (fun y hy => (hmemlr y hy).1) g hgC hg`. Rewrite using `[h0, norm_zero, mul_zero]`.

Check the signs of the components of the expression.
-/
theorem ccle_unif {G : ℂ → Mat k r → E} {K : Set ℂ} (hK : IsCompact K) {C : Set (Mat k r)} (hC : IsCompact C)
    (hloc : ∀ t ∈ K, ∀ γ ∈ GV k r, ∃ (U : Set (ℂ × Mat k r)) (f : ℂ × Mat k r → E), IsOpen U ∧ (t, γ) ∈ U ∧
      ContDiffOn ℝ ∞ f U ∧ ∀ p ∈ U, p.2 ∈ GV k r → G p.1 p.2 = f p)
    (hck : ∀ t ∈ K, CkOn ⊤ (GV k r) (G t))
    (hsupp : ∀ t ∈ K, ∀ γ, G t γ ≠ 0 → γ ∈ C) (A : ℝ) (m : ℕ) :
    ∃ c : ℝ, ∀ t ∈ K, CCle A m (G t) c := by
  classical
  have hS : IsCompact (K ×ˢ (C ∩ GV k r)) := hK.prod (hC.inter_right B5.GV_closed)
  have hl : ∀ p ∈ K ×ˢ (C ∩ GV k r), ∃ V, V ∈ 𝓝 p ∧ ∃ c : ℝ, 0 ≤ c ∧ ∀ q ∈ V, q.2 ∈ GV k r → ∀ (j : ℕ), j ≤ m →
      ∀ (bs : Fin j → Bool) (Xs : Fin j → Mat k r), (∀ i, inLie k r (Xs i)) → (∀ i, Xs i ∈ Box k r) →
        ‖W (List.ofFn fun i => (bs i, Xs i)) (G q.1) q.2‖ ≤ c := fun p hp => by
    obtain ⟨U, f, hU, hpU, hf, hGf⟩ := hloc p.1 hp.1 p.2 hp.2.2
    obtain ⟨V, hV, c, hc0, hc⟩ := local_boundP f hU hf hGf m (p₀ := (p.1, p.2)) hpU
    exact ⟨V, hV, c, hc0, hc⟩
  choose! V hV c hc0 hc using hl
  obtain ⟨s, hsS, hcov⟩ := hS.elim_nhds_subcover V hV
  have hsum0 : 0 ≤ ∑ x ∈ s, c x := Finset.sum_nonneg fun y hy => hc0 y (hsS y hy)
  have hcW : ∀ t ∈ K, ∀ g ∈ C ∩ GV k r, ∀ (j : ℕ), j ≤ m → ∀ (bs : Fin j → Bool) (Xs : Fin j → Mat k r),
      (∀ i, inLie k r (Xs i)) → (∀ i, Xs i ∈ Box k r) →
        ‖W (List.ofFn fun i => (bs i, Xs i)) (G t) g‖ ≤ ∑ x ∈ s, c x := by
    intro t ht g hg j hj bs Xs hL hB
    obtain ⟨x, hxs, hgx⟩ := Set.mem_iUnion₂.1 (hcov (show (t, g) ∈ K ×ˢ (C ∩ GV k r) from ⟨ht, hg⟩))
    exact (hc x (hsS x hxs) (t, g) hgx hg.2 j hj bs Xs hL hB).trans
      (Finset.single_le_sum (fun y hy => hc0 y (hsS y hy)) hxs)
  obtain ⟨cg, hcg⟩ := (hC.inter_right B5.GV_closed).exists_bound_of_continuousOn
    (f := fun g : Mat k r => gN g ^ A)
    fun g hg => ((B6.gN_continuous.continuousAt).rpow_const (Or.inl (B6.gN_pos hg.2).ne')).continuousWithinAt
  refine ⟨|cg| * ∑ x ∈ s, c x, fun t ht => ⟨B5.ckOn_mono le_top (hck t ht), ?_⟩⟩
  intro u v hu hv hlen g hg
  rw [dLR_eq]
  have hmemlr : ∀ y ∈ lr u v, unitLie k r y.2 := by
    intro y hy
    simp only [lr, List.mem_append, List.mem_map] at hy
    rcases hy with ⟨X, hX, rfl⟩ | ⟨X, hX, rfl⟩
    · exact hu X hX
    · exact hv X hX
  by_cases hgC : g ∈ C
  · have hw : lr u v = List.ofFn fun i : Fin (lr u v).length => ((lr u v)[i].1, (lr u v)[i].2) := by
      simp
    have hlen' : (lr u v).length ≤ m := by simp [lr]; omega
    have hb := hcW t ht g ⟨hgC, hg⟩ _ hlen' (fun i => (lr u v)[i].1) (fun i => (lr u v)[i].2)
      (fun i => (hmemlr _ (List.getElem_mem _)).1) (fun i => mem_box (hmemlr _ (List.getElem_mem _)).2)
    rw [← hw] at hb
    have hg1 : gN g ^ A ≤ |cg| := by
      have := hcg g ⟨hgC, hg⟩
      rw [Real.norm_eq_abs] at this
      exact (le_abs_self _).trans (this.trans (le_abs_self _))
    exact mul_le_mul hg1 hb (norm_nonneg _) (abs_nonneg _)
  · have h0 := W_local_zero hC.isClosed.isOpen_compl
      (fun x hx _ => by by_contra h; exact hx (hsupp t ht x h)) (lr u v)
      (fun y hy => (hmemlr y hy).1) g hgC hg
    rw [h0, norm_zero, mul_zero]
    positivity

end Formalism.FourierDecayAlt.P.CutSE.FamCC

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Introduce `Wp Wq _ _ _ _ _ _ P T j G hG K hK hK0 A m`. Take `⟨hG1, hG2⟩` from `hG`. Take `⟨C, hC, ε, hε, hCε⟩` from `hG2 K hK hK0`. Establish `hck : ∀ t ∈ K, B.CkOn ⊤ (B.GV P.k (P.r - (j + 1))) (G t)`. Introduce `t ht γ₀ hγ₀`.

Take `⟨U, f, hU, hmem, hf, hfe⟩` from `hG1 t (hK0 t ht) γ₀ hγ₀`. Establish `hcm : Continuous (fun γ : B.Mat P.k (P.r - (j + 1)) => (t, γ))` using `continuous_const.prodMk continuous_id`. Use `⟨(fun γ => (t, γ)) ⁻¹' U, fun γ => f (t, γ), hU.preimage hcm, hmem, ?_, ?_⟩` and prove the remaining obligations. Conclude with `hf.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun γ hγ => hγ)`. Introduce `γ hγ hγG`.

Conclude with `hfe (t, γ) hγ hγG`. Conclude with `FamCC.ccle_unif hK hC (fun t ht γ hγ => hG1 t (hK0 t ht) γ hγ) hck (fun t ht γ h => (hCε t ht γ h).1) A m`.
-/
theorem family_uniform_compact_convergence : FamCCUnif := by
  intro Wp Wq _ _ _ _ _ _ P T j G hG K hK hK0 A m
  obtain ⟨hG1, hG2⟩ := hG
  obtain ⟨C, hC, ε, hε, hCε⟩ := hG2 K hK hK0
  have hck : ∀ t ∈ K, B.CkOn ⊤ (B.GV P.k (P.r - (j + 1))) (G t) := by
    intro t ht γ₀ hγ₀
    obtain ⟨U, f, hU, hmem, hf, hfe⟩ := hG1 t (hK0 t ht) γ₀ hγ₀
    have hcm : Continuous (fun γ : B.Mat P.k (P.r - (j + 1)) => (t, γ)) :=
      continuous_const.prodMk continuous_id
    refine ⟨(fun γ => (t, γ)) ⁻¹' U, fun γ => f (t, γ), hU.preimage hcm, hmem, ?_, ?_⟩
    · exact hf.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun γ hγ => hγ)
    · intro γ hγ hγG
      exact hfe (t, γ) hγ hγG
  exact FamCC.ccle_unif hK hC (fun t ht γ hγ => hG1 t (hK0 t ht) γ hγ) hck
    (fun t ht γ h => (hCε t ht γ h).1) A m

end Formalism.FourierDecayAlt.P.CutSE
