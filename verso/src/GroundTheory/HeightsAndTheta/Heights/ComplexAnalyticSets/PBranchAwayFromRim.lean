import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchAwayFromRim
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalModelExists
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalModelProper
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchLift
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalLocallyIrreducible
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchContainsNormalPoint
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Filter Topology

/- English proof (translation)
Introduce `n k J u p x m γ hJ hdim hu hcov hdisj b`. Take `⟨N, hN, hcovN⟩` from `hcov`. Take `⟨M⟩` from `hex n J hJ`. Use `set Z' := zeroSetIn M.ideal with hZ'`. Establish `hcontν : Continuous (firstCoords : (Fin n ⊕ Fin M.m → ℂ) → Fin n → ℂ)` using `continuous_pi fun i => continuous_apply _`.

Establish `hZc : IsClosed Z'`. Establish `hZ'eq : Z' = ⋂ q ∈ M.ideal, {z | eval z q = 0}` using `by ext z; simp [Z', zeroSetIn]`. Rewrite using `[hZ'eq]`. Conclude with `isClosed_biInter fun q _ => isClosed_eq (MvPolynomial.continuous_eval q) continuous_const`. Establish `hνZ : ∀ w ∈ Z', firstCoords w ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet J`.

Introduce `w hw q hq`. Establish `hq' : rename Sum.inl q ∈ M.ideal` using `by rw [← M.comap_eq] at hq; exact hq`. Use `hw _ hq'` as an intermediate fact. Rewrite `this` using `[eval_rename]`. Then use the resulting hypothesis. Use `choose Γ hΓd hΓZ hΓopen using fun c => hlift n k J p M (γ c) hJ hdim`.

Establish `hΓinj : ∀ c, Set.InjOn (Γ c) (Metric.ball 0 (γ c).radius)`. Introduce `c s hs t ht hst`. Apply `(γ c).injOn hs ht` to reduce the goal to its premises. Rewrite using `[← (hΓZ c s hs).2, ← (hΓZ c t ht).2, hst]`. Use `choose O hOo hOeq using fun c => hΓopen c (Metric.ball 0 (γ c).radius) subset_rfl Metric.isOpen_ball`.

Use `choose a bd hbJ hab using M.birational`. Use `set g : MvPolynomial (Fin n) ℂ := GroundTheory.Heights₂.Heights.linForm u * ∏ i, bd i with hg`. Establish `hgJ : g ∉ J`. Use `hJ` as an intermediate fact. Introduce `hgm`.

Break down `hJ.mem_or_mem hgm with h1 | h2` into its components or cases. Conclude with `hu h1`. Take `⟨i, -, hi⟩` from `Ideal.IsPrime.prod_mem_iff.mp h2`. Conclude with `hbJ i hi`. Use `set h : MvPolynomial (Fin n ⊕ Fin M.m) ℂ := rename Sum.inl g with hh_def`.

Establish `hh : h ∉ M.ideal`. Introduce `hm`. Apply `hgJ` to reduce the goal to its premises. Rewrite using `[← M.comap_eq]`. Conclude with `hm`.

Establish `heval : ∀ w : Fin n ⊕ Fin M.m → ℂ, eval w h = GroundTheory.Heights₂.Heights.linEval u (firstCoords w) * ∏ i, eval (firstCoords w) (bd i)`. Introduce `w`. Simplify using `only [h, g, eval_rename, map_mul, map_prod]`. Use `congr 1`. Simplify using `[GroundTheory.Heights₂.Heights.linForm, GroundTheory.Heights₂.Heights.linEval, firstCoords, Function.comp_def]`.

Establish `hinj : ∀ w ∈ Z', ∀ w' ∈ Z', firstCoords w = firstCoords w' → eval w h ≠ 0 → w = w'`. Introduce `w hw w' hw' hνw hne`. Rewrite `hne` using `[heval]`. Establish `hb : ∀ i, eval (firstCoords w) (bd i) ≠ 0` using `fun i hi => hne (by rw [Finset.prod_eq_zero (Finset.mem_univ i) hi, mul_zero])`. Use function extensionality and compare the values at `s`.

Break down `s with j | i` into its components or cases. Conclude with `congrFun hνw j`. Establish `e1` using `hw _ (hab i)`. Establish `e2` using `hw' _ (hab i)`. Simplify using `only [map_sub, map_mul, eval_rename, eval_X] at e1 e2`.

Establish `c1 : w ∘ Sum.inl = firstCoords w` using `rfl`. Establish `c2 : w' ∘ Sum.inl = firstCoords w` using `by rw [hνw]; rfl`. Rewrite `e1` using `[c1]`. Rewrite `e2` using `[c2]`. Apply `mul_left_cancel₀ (hb i)` to reduce the goal to its premises.

Take the linear combination `e1 - e2`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Use `set r := (γ b).radius with hr`. Establish `hseq : ∀ j : ℕ, ∃ τ ∈ Metric.ball (0 : Fin k → ℂ) r, (γ b).toFun τ ∈ Metric.ball x (1 / ((j : ℝ) + 1)) ∧ r - 1 / ((j : ℝ) + 1) < ‖τ‖`.

Introduce `j`. Establish `hpos : (0 : ℝ) < 1 / ((j : ℝ) + 1)` using `by positivity`. Conclude with `hcon _ hpos _ (by linarith)`. Use `choose τ hτr hτx hτn using hseq`. Establish `hmem : ∀ j, Γ b (τ j) ∈ {w | w ∈ Z' ∧ firstCoords w ∈ Metric.closedBall x 1}`.

Introduce `j`. Use `⟨(hΓZ b (τ j) (hτr j)).1, ?_⟩` and prove the remaining obligations. Rewrite using `[(hΓZ b (τ j) (hτr j)).2, Metric.mem_closedBall]`. Establish `h1` using `Metric.mem_ball.mp (hτx j)`. Establish `h2 : 1 / ((j : ℝ) + 1) ≤ 1`.

Rewrite using `[div_le_one (by positivity)]`. Combine the linear relations using `[(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨xh, hxcl, φ, hφ, hlim⟩` from `tendsto_subseq_of_bounded (hprop n J M _ Metric.isBounded_closedBall) hmem`. Establish `hlim' : Tendsto (fun j => Γ b (τ (φ j))) atTop (𝓝 xh)` using `hlim`.

Establish `hxZ : xh ∈ Z'` using `hZc.closure_subset_iff.mpr (fun w hw => hw.1) hxcl`. Establish `h1j : Tendsto (fun j => 1 / ((φ j : ℝ) + 1)) atTop (𝓝 0)` using `tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop`. Establish `hγlim : Tendsto (fun j => (γ b).toFun (τ (φ j))) atTop (𝓝 x)`. Rewrite using `[tendsto_iff_dist_tendsto_zero]`. Conclude with `squeeze_zero (fun j => dist_nonneg) (fun j => (Metric.mem_ball.mp (hτx (φ j))).le) h1j`.

Establish `hνx : firstCoords xh = x`. Use `tendsto_nhds_unique ((hcontν.tendsto xh).comp hlim') ?_` and prove the remaining obligations. Use `hγlim.congr fun j => ?_` and prove the remaining obligations. Conclude with `((hΓZ b _ (hτr _)).2).symm`. Establish `hUN : firstCoords ⁻¹' N ∈ 𝓝 xh` using `hcontν.continuousAt.preimage_mem_nhds (by rw [hνx]; exact hN)`.

Take `⟨B, hBo, hxB, hBU, hpre, hdense⟩` from `hirr (Fin n ⊕ Fin M.m) M.ideal h xh M.isPrime M.isIntegrallyClosed hh hxZ _ hUN`. Use `set P := (Z' ∩ B) \ {z | eval z h = 0} with hP`. Establish `hPcov : ∀ q ∈ P, ∃ c, q ∈ Γ c '' Metric.ball 0 (γ c).radius`. Introduce and unpack `q ⟨⟨hqZ, hqB⟩, hqh⟩`. Take `⟨c, hc⟩` from `Set.mem_iUnion.mp (hcovN ⟨hνZ q hqZ, hBU hqB⟩)`.

Take `⟨t, ht, hteq⟩` from `hc`. Use `⟨c, t, ht, ?_⟩` and prove the remaining obligations. Establish `hν : firstCoords (Γ c t) = firstCoords q` using `by rw [(hΓZ c t ht).2, hteq]`. Use `hinj _ (hΓZ c t ht).1 q hqZ hν ?_` and prove the remaining obligations. Rewrite using `[heval, hν, ← heval]`.

Conclude with `hqh`. Establish `hPdisj : ∀ q ∈ P, ∀ c c', c ≠ c' → q ∈ Γ c '' Metric.ball 0 (γ c).radius → q ∉ Γ c' '' Metric.ball 0 (γ c').radius`. Introduce and unpack `q ⟨-, hqh⟩ c c' hcc' ⟨t, ht, rfl⟩ ⟨t', ht', hteq⟩`. Establish `h1 : firstCoords (Γ c t) ∈ (γ c).image` using `⟨t, ht, ((hΓZ c t ht).2).symm⟩`. Establish `h2 : firstCoords (Γ c t) ∈ (γ c').image` using `⟨t', ht', by rw [← (hΓZ c' t' ht').2, hteq]⟩`.

Establish `h3` using `hdisj c c' hcc' ⟨h1, h2⟩`. Apply `hqh` to reduce the goal to its premises. Use `show eval (Γ c t) h = 0`. Rewrite using `[heval]`. Rewrite using `[show GroundTheory.Heights₂.Heights.linEval u (firstCoords (Γ c t)) = 0 from h3, zero_mul]`.

Establish `hPsub : P ⊆ Γ b '' Metric.ball 0 r`. Establish `hsplit` using `isPreconnected_iff_subset_of_disjoint.mp hpre (O b) (⋃ c ∈ {c | c ≠ b}, O c) (hOo b) (isOpen_biUnion fun c _ => hOo c) ?_ ?_`. Break down `hsplit with hs | hs` into its components or cases. Introduce `q hq`. Rewrite using `[hOeq b]`.

Conclude with `⟨hq.1.1, hs hq⟩`. It suffices to derive a contradiction. Take `⟨j, hjB⟩` from `(hlim'.eventually (hBo.mem_nhds hxB)).exists`. Establish `hw0 : Γ b (τ (φ j)) ∈ Γ b '' Metric.ball 0 r` using `⟨_, hτr _, rfl⟩`. Establish `hw0O : Γ b (τ (φ j)) ∈ O b`.

Use `hw0` as an intermediate fact. Rewrite `this` using `[hOeq b]`. Conclude with `this.2`. Establish `hw0P` using `hdense ⟨(hΓZ b _ (hτr _)).1, hjB⟩`. Take `⟨q, hqO, hqP⟩` from `mem_closure_iff.mp hw0P (O b) (hOo b) hw0O`.

Take `⟨c, hc, hqc⟩` from `Set.mem_iUnion₂.mp (hs hqP)`. Establish `hqb : q ∈ Γ b '' Metric.ball 0 r` using `by rw [hOeq b]; exact ⟨hqP.1.1, hqO⟩`. Establish `hqc' : q ∈ Γ c '' Metric.ball 0 (γ c).radius` using `by rw [hOeq c]; exact ⟨hqP.1.1, hqc⟩`. Conclude with `hPdisj q hqP b c (Ne.symm hc) hqb hqc'`. Introduce `q hq`.

Take `⟨c, hc⟩` from `hPcov q hq`. Rewrite `hc` using `[hOeq c]`. Distinguish the cases in `hcb : c = b`. Substitute `hcb` using the available equality. Conclude with `Or.inl hc.2`.

Conclude with `Or.inr (Set.mem_biUnion hcb hc.2)`. Use extensionality with `q`. Simplify using `only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]`. Introduce `hqP hqb hqv`. Take `⟨c, hc, hqc⟩` from `Set.mem_iUnion₂.mp hqv`.

Establish `h1 : q ∈ Γ b '' Metric.ball 0 r` using `by rw [hOeq b]; exact ⟨hqP.1.1, hqb⟩`. Establish `h2 : q ∈ Γ c '' Metric.ball 0 (γ c).radius` using `by rw [hOeq c]; exact ⟨hqP.1.1, hqc⟩`. Conclude with `hPdisj q hqP b c (Ne.symm hc) h1 h2`. Take `⟨σ0, hσ0, hσx⟩` from `hext (Fin n ⊕ Fin M.m) M.ideal h xh k r (Γ b) B M.isPrime M.isIntegrallyClosed hh hxZ (hΓd b) (hΓinj b) (fun t ht => (hΓZ b t ht).1) (hBo.mem_nhds hxB) hPsub`. Establish `hσ0' : ‖σ0‖ < r` using `mem_ball_zero_iff.mp hσ0`.

Use `set δ := (r - ‖σ0‖) / 2 with hδ`. Establish `hδpos : 0 < δ` using `by rw [hδ]; linarith`. Establish `hVsub : Metric.ball σ0 δ ⊆ Metric.ball 0 r`. Introduce `t ht`. Rewrite using `[mem_ball_zero_iff]`.

Establish `h1 : ‖t‖ ≤ ‖σ0‖ + dist t σ0`. Rewrite using `[dist_eq_norm]`. Combine the equalities or inequalities in the displayed calculation. Establish `h2` using `Metric.mem_ball.mp ht`. Combine the linear equalities and inequalities to obtain the conclusion.

Take `⟨O', hO'o, hO'eq⟩` from `hΓopen b (Metric.ball σ0 δ) hVsub Metric.isOpen_ball`. Establish `hxO' : xh ∈ O'`. Establish `: xh ∈ Γ b '' Metric.ball σ0 δ` using `⟨σ0, Metric.mem_ball_self hδpos, hσx⟩`. Rewrite `this` using `[hO'eq]`. Conclude with `this.2`.

Take `⟨j, hjO, hjδ⟩` from `((hlim'.eventually (hO'o.mem_nhds hxO')).and (h1j.eventually (gt_mem_nhds hδpos))).exists`. Establish `hjV : Γ b (τ (φ j)) ∈ Γ b '' Metric.ball σ0 δ`. Rewrite using `[hO'eq]`. Conclude with `⟨(hΓZ b _ (hτr _)).1, hjO⟩`. Take `⟨t, ht, hteq⟩` from `hjV`.

Establish `htτ : t = τ (φ j)` using `hΓinj b (hVsub ht) (hτr _) hteq`. Establish `hn1 : ‖τ (φ j)‖ < ‖σ0‖ + δ`. Rewrite using `[← htτ]`. Establish `h2` using `Metric.mem_ball.mp ht`. Rewrite `h2` using `[dist_eq_norm]`.

Combine the equalities or inequalities in the displayed calculation. Establish `hn2` using `hτn (φ j)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem BranchAwayFromRim.proof (hex : NormalModelExists.Statement)
    (hprop : NormalModelProper.Statement) (hlift : BranchLift.Statement)
    (hirr : NormalLocallyIrreducible.Statement) (hext : BranchContainsNormalPoint.Statement) :
    BranchAwayFromRim.Statement := by
  intro n k J u p x m γ hJ hdim hu hcov hdisj b
  obtain ⟨N, hN, hcovN⟩ := hcov
  obtain ⟨M⟩ := hex n J hJ
  set Z' := zeroSetIn M.ideal with hZ'
  have hcontν : Continuous (firstCoords : (Fin n ⊕ Fin M.m → ℂ) → Fin n → ℂ) :=
    continuous_pi fun i => continuous_apply _
  have hZc : IsClosed Z' := by
    have hZ'eq : Z' = ⋂ q ∈ M.ideal, {z | eval z q = 0} := by ext z; simp [Z', zeroSetIn]
    rw [hZ'eq]
    exact isClosed_biInter fun q _ => isClosed_eq (MvPolynomial.continuous_eval q) continuous_const
  have hνZ : ∀ w ∈ Z', firstCoords w ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet J := by
    intro w hw q hq
    have hq' : rename Sum.inl q ∈ M.ideal := by rw [← M.comap_eq] at hq; exact hq
    have := hw _ hq'
    rwa [eval_rename] at this

  choose Γ hΓd hΓZ hΓopen using fun c => hlift n k J p M (γ c) hJ hdim
  have hΓinj : ∀ c, Set.InjOn (Γ c) (Metric.ball 0 (γ c).radius) := by
    intro c s hs t ht hst
    apply (γ c).injOn hs ht
    rw [← (hΓZ c s hs).2, ← (hΓZ c t ht).2, hst]
  choose O hOo hOeq using fun c => hΓopen c (Metric.ball 0 (γ c).radius) subset_rfl Metric.isOpen_ball

  choose a bd hbJ hab using M.birational
  set g : MvPolynomial (Fin n) ℂ := GroundTheory.Heights₂.Heights.linForm u * ∏ i, bd i with hg
  have hgJ : g ∉ J := by
    have := hJ
    intro hgm
    rcases hJ.mem_or_mem hgm with h1 | h2
    · exact hu h1
    · obtain ⟨i, -, hi⟩ := Ideal.IsPrime.prod_mem_iff.mp h2
      exact hbJ i hi
  set h : MvPolynomial (Fin n ⊕ Fin M.m) ℂ := rename Sum.inl g with hh_def
  have hh : h ∉ M.ideal := by
    intro hm
    apply hgJ
    rw [← M.comap_eq]
    exact hm
  have heval : ∀ w : Fin n ⊕ Fin M.m → ℂ,
      eval w h = GroundTheory.Heights₂.Heights.linEval u (firstCoords w) *
        ∏ i, eval (firstCoords w) (bd i) := by
    intro w
    simp only [h, g, eval_rename, map_mul, map_prod]
    congr 1
    simp [GroundTheory.Heights₂.Heights.linForm, GroundTheory.Heights₂.Heights.linEval, firstCoords, Function.comp_def]
  have hinj : ∀ w ∈ Z', ∀ w' ∈ Z', firstCoords w = firstCoords w' → eval w h ≠ 0 → w = w' := by
    intro w hw w' hw' hνw hne
    rw [heval] at hne
    have hb : ∀ i, eval (firstCoords w) (bd i) ≠ 0 := fun i hi =>
      hne (by rw [Finset.prod_eq_zero (Finset.mem_univ i) hi, mul_zero])
    funext s
    rcases s with j | i
    · exact congrFun hνw j
    · have e1 := hw _ (hab i)
      have e2 := hw' _ (hab i)
      simp only [map_sub, map_mul, eval_rename, eval_X] at e1 e2
      have c1 : w ∘ Sum.inl = firstCoords w := rfl
      have c2 : w' ∘ Sum.inl = firstCoords w := by rw [hνw]; rfl
      rw [c1] at e1
      rw [c2] at e2
      apply mul_left_cancel₀ (hb i)
      linear_combination e1 - e2

  by_contra hcon
  push Not at hcon
  set r := (γ b).radius with hr
  have hseq : ∀ j : ℕ, ∃ τ ∈ Metric.ball (0 : Fin k → ℂ) r,
      (γ b).toFun τ ∈ Metric.ball x (1 / ((j : ℝ) + 1)) ∧ r - 1 / ((j : ℝ) + 1) < ‖τ‖ := by
    intro j
    have hpos : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
    exact hcon _ hpos _ (by linarith)
  choose τ hτr hτx hτn using hseq
  have hmem : ∀ j, Γ b (τ j) ∈ {w | w ∈ Z' ∧ firstCoords w ∈ Metric.closedBall x 1} := by
    intro j
    refine ⟨(hΓZ b (τ j) (hτr j)).1, ?_⟩
    rw [(hΓZ b (τ j) (hτr j)).2, Metric.mem_closedBall]
    have h1 := Metric.mem_ball.mp (hτx j)
    have h2 : 1 / ((j : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    linarith
  obtain ⟨xh, hxcl, φ, hφ, hlim⟩ :=
    tendsto_subseq_of_bounded (hprop n J M _ Metric.isBounded_closedBall) hmem
  have hlim' : Tendsto (fun j => Γ b (τ (φ j))) atTop (𝓝 xh) := hlim
  have hxZ : xh ∈ Z' := hZc.closure_subset_iff.mpr (fun w hw => hw.1) hxcl
  have h1j : Tendsto (fun j => 1 / ((φ j : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
  have hγlim : Tendsto (fun j => (γ b).toFun (τ (φ j))) atTop (𝓝 x) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun j => dist_nonneg) (fun j => (Metric.mem_ball.mp (hτx (φ j))).le) h1j
  have hνx : firstCoords xh = x := by
    refine tendsto_nhds_unique ((hcontν.tendsto xh).comp hlim') ?_
    refine hγlim.congr fun j => ?_
    exact ((hΓZ b _ (hτr _)).2).symm

  have hUN : firstCoords ⁻¹' N ∈ 𝓝 xh :=
    hcontν.continuousAt.preimage_mem_nhds (by rw [hνx]; exact hN)
  obtain ⟨B, hBo, hxB, hBU, hpre, hdense⟩ :=
    hirr (Fin n ⊕ Fin M.m) M.ideal h xh M.isPrime M.isIntegrallyClosed hh hxZ _ hUN
  set P := (Z' ∩ B) \ {z | eval z h = 0} with hP

  have hPcov : ∀ q ∈ P, ∃ c, q ∈ Γ c '' Metric.ball 0 (γ c).radius := by
    rintro q ⟨⟨hqZ, hqB⟩, hqh⟩
    obtain ⟨c, hc⟩ := Set.mem_iUnion.mp (hcovN ⟨hνZ q hqZ, hBU hqB⟩)
    obtain ⟨t, ht, hteq⟩ := hc
    refine ⟨c, t, ht, ?_⟩
    have hν : firstCoords (Γ c t) = firstCoords q := by rw [(hΓZ c t ht).2, hteq]
    refine hinj _ (hΓZ c t ht).1 q hqZ hν ?_
    rw [heval, hν, ← heval]
    exact hqh
  have hPdisj : ∀ q ∈ P, ∀ c c', c ≠ c' → q ∈ Γ c '' Metric.ball 0 (γ c).radius →
      q ∉ Γ c' '' Metric.ball 0 (γ c').radius := by
    rintro q ⟨-, hqh⟩ c c' hcc' ⟨t, ht, rfl⟩ ⟨t', ht', hteq⟩
    have h1 : firstCoords (Γ c t) ∈ (γ c).image := ⟨t, ht, ((hΓZ c t ht).2).symm⟩
    have h2 : firstCoords (Γ c t) ∈ (γ c').image :=
      ⟨t', ht', by rw [← (hΓZ c' t' ht').2, hteq]⟩
    have h3 := hdisj c c' hcc' ⟨h1, h2⟩
    apply hqh
    show eval (Γ c t) h = 0
    rw [heval]
    rw [show GroundTheory.Heights₂.Heights.linEval u (firstCoords (Γ c t)) = 0 from h3, zero_mul]

  have hPsub : P ⊆ Γ b '' Metric.ball 0 r := by
    have hsplit := isPreconnected_iff_subset_of_disjoint.mp hpre (O b) (⋃ c ∈ {c | c ≠ b}, O c)
      (hOo b) (isOpen_biUnion fun c _ => hOo c) ?_ ?_
    · rcases hsplit with hs | hs
      · intro q hq
        rw [hOeq b]
        exact ⟨hq.1.1, hs hq⟩
      · exfalso
        obtain ⟨j, hjB⟩ := (hlim'.eventually (hBo.mem_nhds hxB)).exists
        have hw0 : Γ b (τ (φ j)) ∈ Γ b '' Metric.ball 0 r := ⟨_, hτr _, rfl⟩
        have hw0O : Γ b (τ (φ j)) ∈ O b := by
          have := hw0
          rw [hOeq b] at this
          exact this.2
        have hw0P := hdense ⟨(hΓZ b _ (hτr _)).1, hjB⟩
        obtain ⟨q, hqO, hqP⟩ := mem_closure_iff.mp hw0P (O b) (hOo b) hw0O
        obtain ⟨c, hc, hqc⟩ := Set.mem_iUnion₂.mp (hs hqP)
        have hqb : q ∈ Γ b '' Metric.ball 0 r := by rw [hOeq b]; exact ⟨hqP.1.1, hqO⟩
        have hqc' : q ∈ Γ c '' Metric.ball 0 (γ c).radius := by rw [hOeq c]; exact ⟨hqP.1.1, hqc⟩
        exact hPdisj q hqP b c (Ne.symm hc) hqb hqc'
    · intro q hq
      obtain ⟨c, hc⟩ := hPcov q hq
      rw [hOeq c] at hc
      by_cases hcb : c = b
      · subst hcb
        exact Or.inl hc.2
      · exact Or.inr (Set.mem_biUnion hcb hc.2)
    · ext q
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      intro hqP hqb hqv
      obtain ⟨c, hc, hqc⟩ := Set.mem_iUnion₂.mp hqv
      have h1 : q ∈ Γ b '' Metric.ball 0 r := by rw [hOeq b]; exact ⟨hqP.1.1, hqb⟩
      have h2 : q ∈ Γ c '' Metric.ball 0 (γ c).radius := by rw [hOeq c]; exact ⟨hqP.1.1, hqc⟩
      exact hPdisj q hqP b c (Ne.symm hc) h1 h2

  obtain ⟨σ0, hσ0, hσx⟩ := hext (Fin n ⊕ Fin M.m) M.ideal h xh k r (Γ b) B M.isPrime
    M.isIntegrallyClosed hh hxZ (hΓd b) (hΓinj b) (fun t ht => (hΓZ b t ht).1)
    (hBo.mem_nhds hxB) hPsub

  have hσ0' : ‖σ0‖ < r := mem_ball_zero_iff.mp hσ0
  set δ := (r - ‖σ0‖) / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have hVsub : Metric.ball σ0 δ ⊆ Metric.ball 0 r := by
    intro t ht
    rw [mem_ball_zero_iff]
    have h1 : ‖t‖ ≤ ‖σ0‖ + dist t σ0 := by
      rw [dist_eq_norm]
      calc ‖t‖ = ‖σ0 + (t - σ0)‖ := by rw [add_sub_cancel]
        _ ≤ ‖σ0‖ + ‖t - σ0‖ := norm_add_le _ _
    have h2 := Metric.mem_ball.mp ht
    linarith
  obtain ⟨O', hO'o, hO'eq⟩ := hΓopen b (Metric.ball σ0 δ) hVsub Metric.isOpen_ball
  have hxO' : xh ∈ O' := by
    have : xh ∈ Γ b '' Metric.ball σ0 δ := ⟨σ0, Metric.mem_ball_self hδpos, hσx⟩
    rw [hO'eq] at this
    exact this.2
  obtain ⟨j, hjO, hjδ⟩ :=
    ((hlim'.eventually (hO'o.mem_nhds hxO')).and (h1j.eventually (gt_mem_nhds hδpos))).exists
  have hjV : Γ b (τ (φ j)) ∈ Γ b '' Metric.ball σ0 δ := by
    rw [hO'eq]
    exact ⟨(hΓZ b _ (hτr _)).1, hjO⟩
  obtain ⟨t, ht, hteq⟩ := hjV
  have htτ : t = τ (φ j) := hΓinj b (hVsub ht) (hτr _) hteq
  have hn1 : ‖τ (φ j)‖ < ‖σ0‖ + δ := by
    rw [← htτ]
    have h2 := Metric.mem_ball.mp ht
    rw [dist_eq_norm] at h2
    calc ‖t‖ = ‖σ0 + (t - σ0)‖ := by rw [add_sub_cancel]
      _ ≤ ‖σ0‖ + ‖t - σ0‖ := norm_add_le _ _
      _ < ‖σ0‖ + δ := by linarith
  have hn2 := hτn (φ j)
  linarith

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
