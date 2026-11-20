import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BasePartFlagPt
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LiftToLogResolutionAnalytic
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Dens

def hline {Ψ : Type} {N : ℕ} (h₀ : Ψ → Matrix (Fin N) (Fin N) ℂ) (s : ℂ) (τ' : Ψ) : Matrix (Fin N) (Fin N) ℂ :=
  (1 - s) • h₀ τ' + s • (1 : Matrix (Fin N) (Fin N) ℂ)

/- English proof (translation)
Set `Q : Matrix κ κ (Polynomial ℂ)` to `fun a b => (1 - Polynomial.X) * Polynomial.C (A a b) + Polynomial.X * Polynomial.C (B a b)`. Establish `ev : ∀ s : ℂ, Q.det.eval s = ((1 - s) • A + s • B).det`. Introduce `s`. Use `RingHom.map_det (Polynomial.evalRingHom s) Q` as an intermediate fact. Rewrite `this` using `[Polynomial.coe_evalRingHom]`.

Rewrite using `[this]`. Use `congr 1`. Use extensionality with `a b`. Use `show Polynomial.eval s (Q a b) = _`. Simplify using `[Q]`.

Conclude with `mul_comm _ _`. Establish `hne : Q.det ≠ 0`. Introduce `h0`. Use `ev 1` as an intermediate fact. Rewrite `this` using `[h0]`.

Simplify using `at this`. Conclude with `hB this.symm`. Use `(Q.det.roots.toFinset.finite_toSet).subset ?_` and prove the remaining obligations. Introduce `s hs`. Simplify using `only [Finset.mem_coe, Multiset.mem_toFinset]`.

Rewrite using `[Polynomial.mem_roots hne, Polynomial.IsRoot.def, ev]`. Conclude with `hs`.
-/
theorem finite_det_line {κ : Type} [Fintype κ] [DecidableEq κ] (A B : Matrix κ κ ℂ) (hB : B.det ≠ 0) :
    {s : ℂ | ((1 - s) • A + s • B).det = 0}.Finite := by
  let Q : Matrix κ κ (Polynomial ℂ) := fun a b =>
    (1 - Polynomial.X) * Polynomial.C (A a b) + Polynomial.X * Polynomial.C (B a b)
  have ev : ∀ s : ℂ, Q.det.eval s = ((1 - s) • A + s • B).det := by
    intro s
    have := RingHom.map_det (Polynomial.evalRingHom s) Q
    rw [Polynomial.coe_evalRingHom] at this
    rw [this]
    congr 1
    ext a b
    show Polynomial.eval s (Q a b) = _
    simp [Q]
    exact mul_comm _ _
  have hne : Q.det ≠ 0 := by
    intro h0
    have := ev 1
    rw [h0] at this
    simp at this
    exact hB this.symm
  refine (Q.det.roots.toFinset.finite_toSet).subset ?_
  intro s hs
  simp only [Finset.mem_coe, Multiset.mem_toFinset]
  rw [Polynomial.mem_roots hne, Polynomial.IsRoot.def, ev]
  exact hs

/- English proof (translation)
Simplify using `[minorIJ]`.
-/
theorem minorIJ_self {N : ℕ} (h : Matrix (Fin N) (Fin N) ℂ) (I : Finset (Fin N)) :
    minorIJ h I I = (h.submatrix (I.orderEmbOfFin rfl) (I.orderEmbOfFin rfl)).det := by
  simp [minorIJ]

/- English proof (translation)
Rewrite using `[Matrix.det_of_lowerTriangular]`. Simplify using `[hT.1]`. Introduce `a b hab`. Conclude with `hT.2 _ _ ((I.orderEmbOfFin rfl).strictMono hab)`.
-/
theorem det_submatrix_lowerUni {N : ℕ} {T : Matrix (Fin N) (Fin N) ℂ} (hT : IsLowerUni T) (I : Finset (Fin N)) :
    (T.submatrix (I.orderEmbOfFin rfl) (I.orderEmbOfFin rfl)).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · simp [hT.1]
  · intro a b hab
    exact hT.2 _ _ ((I.orderEmbOfFin rfl).strictMono hab)

/- English proof (translation)
Use `(finite_det_line (A.submatrix (I.orderEmbOfFin rfl) (I.orderEmbOfFin rfl)) _ hB).subset ?_` and prove the remaining obligations. Introduce `s hs`. Simplify using `only [Set.mem_setOf_eq, minorIJ_self] at hs ⊢`. Rewrite using `[← hs]`. Both sides reduce to the same expression.
-/
theorem finite_minor_line {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℂ) (I : Finset (Fin N))
    (hB : (B.submatrix (I.orderEmbOfFin rfl) (I.orderEmbOfFin rfl)).det ≠ 0) :
    {s : ℂ | minorIJ ((1 - s) • A + s • B) I I = 0}.Finite := by
  refine (finite_det_line (A.submatrix (I.orderEmbOfFin rfl) (I.orderEmbOfFin rfl)) _ hB).subset ?_
  intro s hs
  simp only [Set.mem_setOf_eq, minorIJ_self] at hs ⊢
  rw [← hs]
  rfl

/- English proof (translation)
Set `bad : Set ℂ` to `⋃ τ' : Ψ, ⋃ i : Fin N, ({s | minorIJ (hline h₀ s τ') (J i) (J i) = 0} ∪ {s | minorIJ (hline h₀ s τ' * T τ') (J i) (J i) = 0})`. Establish `hfin : bad.Finite`. Use `Set.finite_iUnion fun τ' => Set.finite_iUnion fun i => Set.Finite.union ?_ ?_` and prove the remaining obligations. Use `finite_minor_line (h₀ τ') 1 (J i) ?_` and prove the remaining obligations. Rewrite using `[Matrix.submatrix_one _ ((J i).orderEmbOfFin rfl).injective, Matrix.det_one]`.

Conclude with `one_ne_zero`. Establish `e : ∀ s : ℂ, hline h₀ s τ' * T τ' = (1 - s) • (h₀ τ' * T τ') + s • T τ'`. Introduce `s`. Simplify using `[hline, add_mul]`. Simplify using `only [e]`.

Use `finite_minor_line (h₀ τ' * T τ') (T τ') (J i) ?_` and prove the remaining obligations. Rewrite using `[det_submatrix_lowerUni (hT τ')]`. Conclude with `one_ne_zero`. Establish `hd : Dense badᶜ` using `hfin.countable.dense_compl ℝ`. Take `⟨s, hs, hsb⟩` from `hd.inter_open_nonempty (Metric.ball 0 ε) Metric.isOpen_ball ⟨0, Metric.mem_ball_self hε⟩`.

Use `⟨s, by simpa using hs, fun τ' i => ?_⟩` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion. Introduce `h0`. Conclude with `hsb (Set.mem_iUnion.2 ⟨τ', Set.mem_iUnion.2 ⟨i, Or.inl h0⟩⟩)`. Introduce `h0`.

Conclude with `hsb (Set.mem_iUnion.2 ⟨τ', Set.mem_iUnion.2 ⟨i, Or.inr h0⟩⟩)`.
-/
theorem exists_good_param {Ψ : Type} [Fintype Ψ] {N : ℕ} (h₀ T : Ψ → Matrix (Fin N) (Fin N) ℂ)
    (hT : ∀ τ', IsLowerUni (T τ')) (J : Fin N → Finset (Fin N)) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : ℂ, ‖s‖ < ε ∧ ∀ (τ' : Ψ) (i : Fin N), minorIJ (hline h₀ s τ') (J i) (J i) ≠ 0 ∧
      minorIJ (hline h₀ s τ' * T τ') (J i) (J i) ≠ 0 := by
  let bad : Set ℂ := ⋃ τ' : Ψ, ⋃ i : Fin N,
    ({s | minorIJ (hline h₀ s τ') (J i) (J i) = 0} ∪ {s | minorIJ (hline h₀ s τ' * T τ') (J i) (J i) = 0})
  have hfin : bad.Finite := by
    refine Set.finite_iUnion fun τ' => Set.finite_iUnion fun i => Set.Finite.union ?_ ?_
    · refine finite_minor_line (h₀ τ') 1 (J i) ?_
      rw [Matrix.submatrix_one _ ((J i).orderEmbOfFin rfl).injective, Matrix.det_one]
      exact one_ne_zero
    · have e : ∀ s : ℂ, hline h₀ s τ' * T τ' = (1 - s) • (h₀ τ' * T τ') + s • T τ' := by
        intro s
        simp [hline, add_mul]
      simp only [e]
      refine finite_minor_line (h₀ τ' * T τ') (T τ') (J i) ?_
      rw [det_submatrix_lowerUni (hT τ')]
      exact one_ne_zero
  have hd : Dense badᶜ := hfin.countable.dense_compl ℝ
  obtain ⟨s, hs, hsb⟩ := hd.inter_open_nonempty (Metric.ball 0 ε) Metric.isOpen_ball
    ⟨0, Metric.mem_ball_self hε⟩
  refine ⟨s, by simpa using hs, fun τ' i => ?_⟩
  constructor
  · intro h0
    exact hsb (Set.mem_iUnion.2 ⟨τ', Set.mem_iUnion.2 ⟨i, Or.inl h0⟩⟩)
  · intro h0
    exact hsb (Set.mem_iUnion.2 ⟨τ', Set.mem_iUnion.2 ⟨i, Or.inr h0⟩⟩)

/- English proof (translation)
Take `⟨x, hx⟩` from `hne`. Take `⟨ψ, -, hxψ, hsub, σ, -, -, u, -, hu, hs⟩` from `BM.snc x`. Establish `hop : IsOpen (ψ '' (ψ.source ∩ O))` using `ψ.isOpen_image_source_inter hO`. Establish `hD : Dense (Set.pi Set.univ fun _ : Fin n => ({0}ᶜ : Set ℂ))` using `dense_pi _ fun _ _ => dense_compl_singleton 0`. Take `⟨w, ⟨p, ⟨hp, hpO⟩, rfl⟩, hw⟩` from `hD.inter_open_nonempty _ hop ⟨ψ x, x, ⟨hxψ, hx⟩, rfl⟩`.

Use `⟨p, hpO, fun hb => ?_⟩` and prove the remaining obligations. Establish `hpp : BM.s p p = 0` using `hb`. Establish `hsec` using `BM.sec.2 x p p ⟨hsub hp, BM.L.mem_U p⟩`. Rewrite `hsec` using `[hpp, norm_zero, zero_mul]`. Establish `hz : BM.s x p = 0`.

Use `(mul_eq_zero.1 hsec).resolve_right (Real.exp_pos _).ne'` as an intermediate fact. Simplify using `using this`. Rewrite `hz` using `[hs p hp]`. Break down `mul_eq_zero.1 hz with h | h` into its components or cases. Conclude with `hu p hp h`.

Take `⟨k, -, hk⟩` from `Finset.prod_eq_zero_iff.1 h`. Consider the cases of `hσ : σ k with`. Consider the case `none => simp [hσ] at hk`. Consider the case `some i`. Simplify using `only [hσ] at hk`.

Apply the tactic sequence `exact hw i (Set.mem_univ i) (by first | exact pow_eq_zero hk | exact eq_zero_of_pow_eq_zero hk)`.
-/
theorem exists_off_bdry {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]
    {y : (Σ k, ι k) → Φ} {Ψ : Type} {N j : ℕ} {M : FlagModel y Ψ N j} {n : ℕ} (BM : BaseMetric M n)
    {O : Set BM.Rb.X} (hO : IsOpen O) (hne : O.Nonempty) : ∃ p ∈ O, p ∉ bdry BM.s := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨ψ, -, hxψ, hsub, σ, -, -, u, -, hu, hs⟩ := BM.snc x
  have hop : IsOpen (ψ '' (ψ.source ∩ O)) := ψ.isOpen_image_source_inter hO
  have hD : Dense (Set.pi Set.univ fun _ : Fin n => ({0}ᶜ : Set ℂ)) :=
    dense_pi _ fun _ _ => dense_compl_singleton 0
  obtain ⟨w, ⟨p, ⟨hp, hpO⟩, rfl⟩, hw⟩ := hD.inter_open_nonempty _ hop ⟨ψ x, x, ⟨hxψ, hx⟩, rfl⟩
  refine ⟨p, hpO, fun hb => ?_⟩
  have hpp : BM.s p p = 0 := hb
  have hsec := BM.sec.2 x p p ⟨hsub hp, BM.L.mem_U p⟩
  rw [hpp, norm_zero, zero_mul] at hsec
  have hz : BM.s x p = 0 := by
    have := (mul_eq_zero.1 hsec).resolve_right (Real.exp_pos _).ne'
    simpa using this
  rw [hs p hp] at hz
  rcases mul_eq_zero.1 hz with h | h
  · exact hu p hp h
  · obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.1 h
    cases hσ : σ k with
    | none => simp [hσ] at hk
    | some i =>
      simp only [hσ] at hk
      exact hw i (Set.mem_univ i) (by first | exact pow_eq_zero hk | exact eq_zero_of_pow_eq_zero hk)

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Dens

open GlobalTheory.CompanionTheory.Ar.PB.WSq.Dens in

/- English proof (translation)
Introduce `K _ ι _ Φ _ y Ψ _ _ N j M n BM K' _ ι' _ P' J' e R' hJ l vec T hT hAn hMem x b hb h₀ hh₀ hx V hV hxV`. Substitute `hJ` using the available equality. Take `⟨kb, hkb⟩` from `BM.Rb.A.cover b`. Establish `hnot : ∀ z, z ∉ mcPts (⊤ : Ideal (MRing ι'))`. Introduce `z hz`.

Use `hz.2 1 trivial` as an intermediate fact. Simplify using `at this`. Set `tl : (Fin (n + 1) → ℂ) →L[ℂ] (Fin n → ℂ)` to `ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj i.succ`. Establish `htl : ∀ u, tl u = Fin.tail u` using `fun u => rfl`. Set `c` to `BM.Rb.A.chart kb`.

Set `bp : (Fin (n + 1) → ℂ) → BM.Rb.X` to `fun u => c.symm (Fin.tail u)`. Set `hh : Ψ → (Fin (n + 1) → ℂ) → Matrix (Fin N) (Fin N) ℂ` to `fun τ' u => hline h₀ (u 0) τ'`. Set `V₀ : Set (Fin (n + 1) → ℂ)` to `{u | Fin.tail u ∈ c.target ∧ bp u ∈ BM.O l ∧ ∀ τ', (hh τ' u).det ≠ 0}`. Establish `hc0 : Continuous fun u : Fin (n + 1) → ℂ => u 0` using `continuous_apply 0`. Establish `hV₀ : IsOpen V₀`.

Establish `h1 : IsOpen (tl ⁻¹' (c.target ∩ c.symm ⁻¹' BM.O l))` using `(c.isOpen_inter_preimage_symm (BM.O_open l)).preimage tl.continuous`. Establish `h2 : IsOpen (⋂ τ' : Ψ, {u : Fin (n + 1) → ℂ | (hh τ' u).det ≠ 0})`. Use `isOpen_iInter_of_finite fun τ' => ?_` and prove the remaining obligations. Establish `hcm : Continuous fun u : Fin (n + 1) → ℂ => hh τ' u`. Use `continuous_matrix fun r s => ?_` and prove the remaining obligations.

Use `show Continuous fun u : Fin (n + 1) → ℂ => ((1 - u 0) • h₀ τ' + u 0 • (1 : Matrix (Fin N) (Fin N) ℂ)) r s`. Simplify using `only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]`. Use `fun_prop`. Conclude with `isOpen_ne_fun hcm.matrix_det continuous_const`. Use `h1.inter h2 using 1` and compare the differences between its conclusion and the goal.

Use extensionality with `u`. Simplify using `only [V₀, bp, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_iInter, htl, and_assoc]`. Establish `hbpc : ContinuousOn bp V₀`. Use `c.continuousOn_symm.comp tl.continuous.continuousOn fun u hu => hu.1` and prove the remaining obligations. Establish `hchart : ∀ k, AnalyticOnNhd ℂ (BM.Rb.A.chart k ∘ bp) (V₀ ∩ bp ⁻¹' (BM.Rb.A.chart k).source)`.

Introduce `k u hu`. Conclude with `AnalyticAt.comp (g := BM.Rb.A.chart k ∘ c.symm) (f := tl) (BM.Rb.A.holo kb k _ ⟨hu.1.1, hu.2⟩) (tl.analyticAt u)`. Establish `hentries : ∀ τ' r s, AnalyticOnNhd ℂ (fun u => hh τ' u r s) V₀`. Introduce `τ' r s u _`. Establish `hp : AnalyticAt ℂ (fun u : Fin (n + 1) → ℂ => u 0) u` using `(ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 1) => ℂ) 0).analyticAt u`.

Use `show AnalyticAt ℂ (fun u : Fin (n + 1) → ℂ => ((1 - u 0) • h₀ τ' + u 0 • (1 : Matrix (Fin N) (Fin N) ℂ)) r s) u`. Simplify using `only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]`. Conclude with `((analyticAt_const.sub hp).mul analyticAt_const).add (hp.mul analyticAt_const)`. Establish `hbd : ∀ u ∈ V₀, ∀ τ', IsBlockDiag j (hh τ' u) ∧ (hh τ' u).det ≠ 0`. Introduce `u hu τ'`.

Use `⟨fun r s hrs => ?_, hu.2.2 τ'⟩` and prove the remaining obligations. Establish `hne : r ≠ s`. Introduce and unpack `rfl`. Conclude with `hrs Iff.rfl`. Use `show ((1 - u 0) • h₀ τ' + u 0 • (1 : Matrix (Fin N) (Fin N) ℂ)) r s = 0`.

Simplify using `[Matrix.add_apply, Matrix.smul_apply, (hh₀ τ').1 r s hrs, Matrix.one_apply_ne hne]`. Set `μ : (Fin (n + 1) → ℂ) → (Σ k, ι' k) → ℂ` to `fun u => vec (bp u) fun τ' => hh τ' u`. Establish `hμ : ∀ q, AnalyticOnNhd ℂ (fun u => μ u q) V₀` using `hAn (n + 1) V₀ bp hh hV₀ hbpc hchart (fun u hu => hu.2.1) hentries hbd`. Establish `hex : ∀ u, ∃ z : R'.X, u ∈ V₀ → SameOrbit (R'.lift z z) (μ u)`. Introduce `u`.

Distinguish the cases in `hu : u ∈ V₀`. Take `⟨z, hz⟩` from `R'.surj (μ u) (hMem (bp u) hu.2.1 _ (hbd u hu)) (hnot _)`. Conclude with `⟨z, fun _ => hz⟩`. Conclude with `⟨x, fun h => absurd h hu⟩`. Use `choose g hg using hex`.

Establish `hgc : ContinuousOn g V₀` using `(HoloLift.holo_of_analytic_lift K' ι' P' ⊤ e (n + 1) R' rfl V₀ μ g hV₀ hμ hg).1`. Set `u₀ : Fin (n + 1) → ℂ` to `Fin.cons 0 (c b)`. Establish `ht₀ : Fin.tail u₀ = c b` using `Fin.tail_cons _ _`. Establish `hz₀ : u₀ 0 = 0` using `Fin.cons_zero _ _`. Establish `hb₀ : bp u₀ = b` using `by show c.symm (Fin.tail u₀) = b`.

Rewrite using `[ht₀]`. Conclude with `c.left_inv hkb`. Establish `hhh₀ : (fun τ' => hh τ' u₀) = h₀`. Use function extensionality and compare the values at `τ'`. Use `show hline h₀ (u₀ 0) τ' = h₀ τ'`.

Rewrite using `[hz₀]`. Simplify using `[hline]`. Establish `hu₀ : u₀ ∈ V₀`. Use `⟨?_, ?_, fun τ' => ?_⟩` and prove the remaining obligations. Rewrite using `[ht₀]`.

Conclude with `c.map_source hkb`. Rewrite using `[hb₀]`. Conclude with `hb`. Establish `: hh τ' u₀ = h₀ τ'` using `congrFun hhh₀ τ'`. Rewrite using `[this]`.

Conclude with `(hh₀ τ').2`. Establish `hgx : g u₀ = x`. Use `R'.inj _ _ (hnot _) (orbit_trans (hg u₀ hu₀) ?_)` and prove the remaining obligations. Establish `: μ u₀ = vec b h₀` using `by show vec (bp u₀) (fun τ' => hh τ' u₀) = _`. Rewrite using `[hb₀, hhh₀]`.

Rewrite using `[this]`. Conclude with `orbit_symm hx`. Establish `hW : IsOpen (V₀ ∩ g ⁻¹' V)` using `hgc.isOpen_inter_preimage hV₀ hV`. Take `⟨ε, hε, hball⟩` from `Metric.isOpen_iff.1 hW u₀ ⟨hu₀, by show g u₀ ∈ V`. Rewrite using `[hgx]`.

Conclude with `hxV⟩`. Establish `hO' : IsOpen (c.source ∩ c ⁻¹' Metric.ball (c b) ε)` using `c.isOpen_inter_preimage Metric.isOpen_ball`. Take `⟨p, ⟨hps, hpb⟩, hpoff⟩` from `exists_off_bdry BM hO' ⟨b, hkb, Metric.mem_ball_self hε⟩`. Take `⟨s, hs, hgood⟩` from `exists_good_param h₀ T hT (fun i => stepCols N j i) hε`. Set `u : Fin (n + 1) → ℂ` to `Fin.cons s (c p)`.

Establish `htu : Fin.tail u = c p` using `Fin.tail_cons _ _`. Establish `hzu : u 0 = s` using `Fin.cons_zero _ _`. Establish `hbu : bp u = p` using `by show c.symm (Fin.tail u) = p`. Rewrite using `[htu]`. Conclude with `c.left_inv hps`.

Establish `hmem : u ∈ Metric.ball u₀ ε`. Use `Metric.mem_ball.2 ((dist_pi_lt_iff hε).2 fun i => ?_)` and prove the remaining obligations. Use `Fin.cases ?_ (fun i => ?_) i` and prove the remaining obligations. Rewrite using `[hzu, hz₀, dist_zero_right]`. Conclude with `hs`.

Establish `h1 : u i.succ = c p i` using `Fin.cons_succ _ _ _`. Establish `h2 : u₀ i.succ = c b i` using `Fin.cons_succ _ _ _`. Rewrite using `[h1, h2]`. Conclude with `lt_of_le_of_lt (dist_le_pi_dist _ _ i) (Metric.mem_ball.1 hpb)`. Take `⟨huV, hugV⟩` from `hball hmem`.

Use `⟨g u, hugV, p, ⟨hbu ▸ huV.2.1, hpoff⟩, fun τ' => hh τ' u, hbd u huV, ?_, ?_⟩` and prove the remaining obligations. Use `hg u huV` as an intermediate fact. Rewrite using `[show μ u = vec p (fun τ' => hh τ' u) from by show vec (bp u) _ = _`. Rewrite `this` using `[hbu]]`. Conclude with `this`.

Introduce `τ' i _`. Use `hgood τ' i` as an intermediate fact. Rewrite `this` using `[← hzu]`. Conclude with `this`.
-/
theorem GlobalTheory.CompanionTheory.Ar.PB.WSq.Dens.dens_core : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (P' J' : Ideal (MRing ι')) (e : ℕ) (R' : AnLogRes P' J' e), J' = ⊤ → ∀ (l : Fin BM.q) (vec : BM.Rb.X → (Ψ → Matrix (Fin N) (Fin N) ℂ) → (Σ k, ι' k) → ℂ) (T : Ψ → Matrix (Fin N) (Fin N) ℂ), (∀ τ', IsLowerUni (T τ')) → (∀ (m : ℕ) (V : Set (Fin m → ℂ)) (bp : (Fin m → ℂ) → BM.Rb.X) (hh : Ψ → (Fin m → ℂ) → Matrix (Fin N) (Fin N) ℂ), IsOpen V → ContinuousOn bp V → (∀ k, AnalyticOnNhd ℂ (BM.Rb.A.chart k ∘ bp) (V ∩ bp ⁻¹' (BM.Rb.A.chart k).source)) → (∀ u ∈ V, bp u ∈ BM.O l) → (∀ τ' r s, AnalyticOnNhd ℂ (fun u => hh τ' u r s) V) → (∀ u ∈ V, ∀ τ', IsBlockDiag j (hh τ' u) ∧ (hh τ' u).det ≠ 0) → ∀ q, AnalyticOnNhd ℂ (fun u => vec (bp u) (fun τ' => hh τ' u) q) V) → (∀ b ∈ BM.O l, ∀ h : Ψ → Matrix (Fin N) (Fin N) ℂ, (∀ τ', IsBlockDiag j (h τ') ∧ (h τ').det ≠ 0) → vec b h ∈ mcPts P') → ∀ (x : R'.X), ∀ b ∈ BM.O l, ∀ h₀ : Ψ → Matrix (Fin N) (Fin N) ℂ, (∀ τ', IsBlockDiag j (h₀ τ') ∧ (h₀ τ').det ≠ 0) → SameOrbit (R'.lift x x) (vec b h₀) → ∀ V, IsOpen V → x ∈ V → ∃ x' ∈ V, ∃ b' ∈ BM.O l \ bdry BM.s, ∃ h' : Ψ → Matrix (Fin N) (Fin N) ℂ, (∀ τ', IsBlockDiag j (h' τ') ∧ (h' τ').det ≠ 0) ∧ SameOrbit (R'.lift x' x') (vec b' h') ∧ ∀ (τ' : Ψ) (i : Fin N), IsProperStep N j i → minorIJ (h' τ') (stepCols N j i) (stepCols N j i) ≠ 0 ∧ minorIJ (h' τ' * T τ') (stepCols N j i) (stepCols N j i) ≠ 0 := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM K' _ ι' _ P' J' e R' hJ l vec T hT hAn hMem x b hb h₀ hh₀ hx V hV hxV
  subst hJ
  obtain ⟨kb, hkb⟩ := BM.Rb.A.cover b
  have hnot : ∀ z, z ∉ mcPts (⊤ : Ideal (MRing ι')) := by
    intro z hz
    have := hz.2 1 trivial
    simp at this
  let tl : (Fin (n + 1) → ℂ) →L[ℂ] (Fin n → ℂ) :=
    ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj i.succ
  have htl : ∀ u, tl u = Fin.tail u := fun u => rfl
  let c := BM.Rb.A.chart kb
  let bp : (Fin (n + 1) → ℂ) → BM.Rb.X := fun u => c.symm (Fin.tail u)
  let hh : Ψ → (Fin (n + 1) → ℂ) → Matrix (Fin N) (Fin N) ℂ := fun τ' u => hline h₀ (u 0) τ'
  let V₀ : Set (Fin (n + 1) → ℂ) := {u | Fin.tail u ∈ c.target ∧ bp u ∈ BM.O l ∧ ∀ τ', (hh τ' u).det ≠ 0}
  have hc0 : Continuous fun u : Fin (n + 1) → ℂ => u 0 := continuous_apply 0
  have hV₀ : IsOpen V₀ := by
    have h1 : IsOpen (tl ⁻¹' (c.target ∩ c.symm ⁻¹' BM.O l)) :=
      (c.isOpen_inter_preimage_symm (BM.O_open l)).preimage tl.continuous
    have h2 : IsOpen (⋂ τ' : Ψ, {u : Fin (n + 1) → ℂ | (hh τ' u).det ≠ 0}) := by
      refine isOpen_iInter_of_finite fun τ' => ?_
      have hcm : Continuous fun u : Fin (n + 1) → ℂ => hh τ' u := by
        refine continuous_matrix fun r s => ?_
        show Continuous fun u : Fin (n + 1) → ℂ => ((1 - u 0) • h₀ τ' + u 0 • (1 : Matrix (Fin N) (Fin N) ℂ)) r s
        simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
        fun_prop
      exact isOpen_ne_fun hcm.matrix_det continuous_const
    convert h1.inter h2 using 1
    ext u
    simp only [V₀, bp, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_iInter, htl, and_assoc]
  have hbpc : ContinuousOn bp V₀ := by
    refine c.continuousOn_symm.comp tl.continuous.continuousOn fun u hu => hu.1
  have hchart : ∀ k, AnalyticOnNhd ℂ (BM.Rb.A.chart k ∘ bp) (V₀ ∩ bp ⁻¹' (BM.Rb.A.chart k).source) := by
    intro k u hu
    exact AnalyticAt.comp (g := BM.Rb.A.chart k ∘ c.symm) (f := tl)
      (BM.Rb.A.holo kb k _ ⟨hu.1.1, hu.2⟩) (tl.analyticAt u)
  have hentries : ∀ τ' r s, AnalyticOnNhd ℂ (fun u => hh τ' u r s) V₀ := by
    intro τ' r s u _
    have hp : AnalyticAt ℂ (fun u : Fin (n + 1) → ℂ => u 0) u :=
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 1) => ℂ) 0).analyticAt u
    show AnalyticAt ℂ (fun u : Fin (n + 1) → ℂ => ((1 - u 0) • h₀ τ' + u 0 • (1 : Matrix (Fin N) (Fin N) ℂ)) r s) u
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    exact ((analyticAt_const.sub hp).mul analyticAt_const).add (hp.mul analyticAt_const)
  have hbd : ∀ u ∈ V₀, ∀ τ', IsBlockDiag j (hh τ' u) ∧ (hh τ' u).det ≠ 0 := by
    intro u hu τ'
    refine ⟨fun r s hrs => ?_, hu.2.2 τ'⟩
    have hne : r ≠ s := by
      rintro rfl
      exact hrs Iff.rfl
    show ((1 - u 0) • h₀ τ' + u 0 • (1 : Matrix (Fin N) (Fin N) ℂ)) r s = 0
    simp [Matrix.add_apply, Matrix.smul_apply, (hh₀ τ').1 r s hrs, Matrix.one_apply_ne hne]
  let μ : (Fin (n + 1) → ℂ) → (Σ k, ι' k) → ℂ := fun u => vec (bp u) fun τ' => hh τ' u
  have hμ : ∀ q, AnalyticOnNhd ℂ (fun u => μ u q) V₀ :=
    hAn (n + 1) V₀ bp hh hV₀ hbpc hchart (fun u hu => hu.2.1) hentries hbd
  have hex : ∀ u, ∃ z : R'.X, u ∈ V₀ → SameOrbit (R'.lift z z) (μ u) := by
    intro u
    by_cases hu : u ∈ V₀
    · obtain ⟨z, hz⟩ := R'.surj (μ u) (hMem (bp u) hu.2.1 _ (hbd u hu)) (hnot _)
      exact ⟨z, fun _ => hz⟩
    · exact ⟨x, fun h => absurd h hu⟩
  choose g hg using hex
  have hgc : ContinuousOn g V₀ :=
    (HoloLift.holo_of_analytic_lift K' ι' P' ⊤ e (n + 1) R' rfl V₀ μ g hV₀ hμ hg).1
  let u₀ : Fin (n + 1) → ℂ := Fin.cons 0 (c b)
  have ht₀ : Fin.tail u₀ = c b := Fin.tail_cons _ _
  have hz₀ : u₀ 0 = 0 := Fin.cons_zero _ _
  have hb₀ : bp u₀ = b := by
    show c.symm (Fin.tail u₀) = b
    rw [ht₀]
    exact c.left_inv hkb
  have hhh₀ : (fun τ' => hh τ' u₀) = h₀ := by
    funext τ'
    show hline h₀ (u₀ 0) τ' = h₀ τ'
    rw [hz₀]
    simp [hline]
  have hu₀ : u₀ ∈ V₀ := by
    refine ⟨?_, ?_, fun τ' => ?_⟩
    · rw [ht₀]
      exact c.map_source hkb
    · rw [hb₀]
      exact hb
    · have : hh τ' u₀ = h₀ τ' := congrFun hhh₀ τ'
      rw [this]
      exact (hh₀ τ').2
  have hgx : g u₀ = x := by
    refine R'.inj _ _ (hnot _) (orbit_trans (hg u₀ hu₀) ?_)
    have : μ u₀ = vec b h₀ := by
      show vec (bp u₀) (fun τ' => hh τ' u₀) = _
      rw [hb₀, hhh₀]
    rw [this]
    exact orbit_symm hx
  have hW : IsOpen (V₀ ∩ g ⁻¹' V) := hgc.isOpen_inter_preimage hV₀ hV
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hW u₀ ⟨hu₀, by
    show g u₀ ∈ V
    rw [hgx]
    exact hxV⟩
  have hO' : IsOpen (c.source ∩ c ⁻¹' Metric.ball (c b) ε) := c.isOpen_inter_preimage Metric.isOpen_ball
  obtain ⟨p, ⟨hps, hpb⟩, hpoff⟩ := exists_off_bdry BM hO' ⟨b, hkb, Metric.mem_ball_self hε⟩
  obtain ⟨s, hs, hgood⟩ := exists_good_param h₀ T hT (fun i => stepCols N j i) hε
  let u : Fin (n + 1) → ℂ := Fin.cons s (c p)
  have htu : Fin.tail u = c p := Fin.tail_cons _ _
  have hzu : u 0 = s := Fin.cons_zero _ _
  have hbu : bp u = p := by
    show c.symm (Fin.tail u) = p
    rw [htu]
    exact c.left_inv hps
  have hmem : u ∈ Metric.ball u₀ ε := by
    refine Metric.mem_ball.2 ((dist_pi_lt_iff hε).2 fun i => ?_)
    refine Fin.cases ?_ (fun i => ?_) i
    · rw [hzu, hz₀, dist_zero_right]
      exact hs
    · have h1 : u i.succ = c p i := Fin.cons_succ _ _ _
      have h2 : u₀ i.succ = c b i := Fin.cons_succ _ _ _
      rw [h1, h2]
      exact lt_of_le_of_lt (dist_le_pi_dist _ _ i) (Metric.mem_ball.1 hpb)
  obtain ⟨huV, hugV⟩ := hball hmem
  refine ⟨g u, hugV, p, ⟨hbu ▸ huV.2.1, hpoff⟩, fun τ' => hh τ' u, hbd u huV, ?_, ?_⟩
  · have := hg u huV
    rw [show μ u = vec p (fun τ' => hh τ' u) from by
      show vec (bp u) _ = _
      rw [hbu]] at this
    exact this
  · intro τ' i _
    have := hgood τ' i
    rw [← hzu] at this
    exact this
