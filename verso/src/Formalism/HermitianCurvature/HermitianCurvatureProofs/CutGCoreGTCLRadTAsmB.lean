import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCLRadTAsmA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.RadTA

noncomputable section

open Classical

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
  {z z' : Fin (2 * r + k + 1) → ℂ} {μs : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
  {π : Q.Mx k r → (Wp →L[ℂ] Wp)} {π' : Q.Mx k r → (Wq →L[ℂ] Wq)}
  {Pr : (Wq →L[ℂ] Wp) →ₗ[ℂ] (Wq →L[ℂ] Wp)}

/- English proof (translation)
Take `⟨hk, hz, hz', hT, hT', hsec, -, -, -, -⟩` from `hB`. Take `⟨h0, -, he⟩` from `Ψ.2`. Use function extensionality and compare the values at `g`. Distinguish the cases in `hg : g ∈ Q.Glev k r (Fin.last r) ∧ 0 < Q.GGl k r z z' g`. Take `⟨hgG, hG'⟩` from `hg`.

Establish `hζq : Tz k r z * Tz k r z' < Complex.normSq (Q.zetaL k r z z' (Fin.last r) g)`. Establish `h1` using `hG'`. Unfold `Q.GGl at h1`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨a, ha, b, hb, hgeq⟩` from `Formalism.FourierDecayAlt.P.NFRadRedA.decomp hk hz hz' hT hT' hsec hgG hG'`.

Generalize the expression as in `Q.zetaL k r z z' (Fin.last r) g = ζ at hζq hgeq`. Establish `hq : (c, ζ) ∈ NF.QR k r z z'` using `⟨hc, hζq⟩`. Establish `hq' : (c', ζ) ∈ NF.QR k r z z'` using `⟨hc', hζq⟩`. Establish `e1` using `he (c, NF.muZ k r μs ζ) (Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' hsec hq) a ha b hb`. Establish `e2` using `he (c', NF.muZ k r μs ζ) (Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' hsec hq') a ha b hb`.

Establish `e3` using `h ζ`. Rewrite `e3` using `[radR_apply _ hq, radR_apply _ hq']`. Simplify using `only at e1 e2 e3`. Rewrite using `[hgeq, e1, e2, e3]`. Establish `n1 : (c, g) ∉ Q.DomR k r z z'` using `fun hx => hg ⟨hx.2.1, hx.2.2⟩`.

Establish `n2 : (c', g) ∉ Q.DomR k r z z'` using `fun hx => hg ⟨hx.2.1, hx.2.2⟩`. Conclude with `(h0 (c, g) n1).trans (h0 (c', g) n2).symm`.
-/
theorem fn_eq_of_radR (hB : NF.RadBase k r z z' μs π π') (Ψ : Q.RadSp k r z z' π π') {c c' : Fin r → ℂ}
    (hc : c ∈ OmX r) (hc' : c' ∈ OmX r)
    (h : ∀ ζ, NF.radR k r z z' μs (Ψ : Q.Fn k r (Wq →L[ℂ] Wp)) (c, ζ) =
      NF.radR k r z z' μs (Ψ : Q.Fn k r (Wq →L[ℂ] Wp)) (c', ζ)) :
    (Ψ : Q.Fn k r (Wq →L[ℂ] Wp)) c = (Ψ : Q.Fn k r (Wq →L[ℂ] Wp)) c' := by
  obtain ⟨hk, hz, hz', hT, hT', hsec, -, -, -, -⟩ := hB
  obtain ⟨h0, -, he⟩ := Ψ.2
  funext g
  by_cases hg : g ∈ Q.Glev k r (Fin.last r) ∧ 0 < Q.GGl k r z z' g
  · obtain ⟨hgG, hG'⟩ := hg
    have hζq : Tz k r z * Tz k r z' < Complex.normSq (Q.zetaL k r z z' (Fin.last r) g) := by
      have h1 := hG'
      unfold Q.GGl at h1
      linarith
    obtain ⟨a, ha, b, hb, hgeq⟩ := Formalism.FourierDecayAlt.P.NFRadRedA.decomp hk hz hz' hT hT' hsec hgG hG'
    generalize Q.zetaL k r z z' (Fin.last r) g = ζ at hζq hgeq
    have hq : (c, ζ) ∈ NF.QR k r z z' := ⟨hc, hζq⟩
    have hq' : (c', ζ) ∈ NF.QR k r z z' := ⟨hc', hζq⟩
    have e1 := he (c, NF.muZ k r μs ζ) (Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' hsec hq) a ha b hb
    have e2 := he (c', NF.muZ k r μs ζ) (Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' hsec hq') a ha b hb
    have e3 := h ζ
    rw [radR_apply _ hq, radR_apply _ hq'] at e3
    dsimp only at e1 e2 e3
    rw [hgeq, e1, e2, e3]
  · have n1 : (c, g) ∉ Q.DomR k r z z' := fun hx => hg ⟨hx.2.1, hx.2.2⟩
    have n2 : (c', g) ∉ Q.DomR k r z z' := fun hx => hg ⟨hx.2.1, hx.2.2⟩
    exact (h0 (c, g) n1).trans (h0 (c', g) n2).symm

/- English proof (translation)
Take `⟨-, hz, hz', -, -, hsec, -, -, -, -⟩` from `hB`. Establish `hq : (c, ζ) ∈ NF.QR k r z z'` using `⟨hc, hζ⟩`. Establish `hq' : (c', ζ) ∈ NF.QR k r z z'` using `⟨hc', hζ⟩`. Rewrite using `[radR_apply _ hq, radR_apply _ hq', X.t_apply Y a b Ψ _ (Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' hsec hq), X.t_apply Y a b Ψ _ (Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' hsec hq')]`. Simplify using `only`.

Rewrite using `[h]`.
-/
theorem t_slice (hB : NF.RadBase k r z z' μs π π') (X : Q.ActualOps k r z z' π π') (Y : ℂ) (a b : Fin 2)
    (Ψ : Q.RadSp k r z z' π π') {c c' : Fin r → ℂ} (hc : c ∈ OmX r) (hc' : c' ∈ OmX r)
    (h : (Ψ : Q.Fn k r (Wq →L[ℂ] Wp)) c = (Ψ : Q.Fn k r (Wq →L[ℂ] Wp)) c') {ζ : ℂ} (hζ : ζ ∈ Ann z z') :
    NF.radR k r z z' μs ((X.t Y a b Ψ : Q.RadSp k r z z' π π') : Q.Fn k r (Wq →L[ℂ] Wp)) (c, ζ) =
      NF.radR k r z z' μs ((X.t Y a b Ψ : Q.RadSp k r z z' π π') : Q.Fn k r (Wq →L[ℂ] Wp)) (c', ζ) := by
  obtain ⟨-, hz, hz', -, -, hsec, -, -, -, -⟩ := hB
  have hq : (c, ζ) ∈ NF.QR k r z z' := ⟨hc, hζ⟩
  have hq' : (c', ζ) ∈ NF.QR k r z z' := ⟨hc', hζ⟩
  rw [radR_apply _ hq, radR_apply _ hq', X.t_apply Y a b Ψ _ (Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' hsec hq),
    X.t_apply Y a b Ψ _ (Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' hsec hq')]
  dsimp only
  rw [h]

def pw (j : ℕ) (s : Fin j → Fin 2) (ζ0 : ℂ) (X : Wq →L[ℂ] Wp) : ℂ → (Wq →L[ℂ] Wp) :=
  fun ζ => (((j.factorial : ℝ)⁻¹ * ∏ i, crd (s i) (ζ - ζ0)) • X)

/- English proof (translation)
The claim follows from `(contDiff_const.mul (contDiff_prod fun i _ => (crd (s i)).contDiff.comp (contDiff_id.sub contDiff_const))).smul contDiff_const`.
-/
theorem pw_smooth (j : ℕ) (s : Fin j → Fin 2) (ζ0 : ℂ) (X : Wq →L[ℂ] Wp) : ContDiff ℝ ∞ (pw j s ζ0 X) :=
  (contDiff_const.mul (contDiff_prod fun i _ => (crd (s i)).contDiff.comp (contDiff_id.sub contDiff_const))).smul
    contDiff_const

def wt (j : ℕ) (s : Fin j → Fin 2) (t : Finset (Fin j)) (X : Wq →L[ℂ] Wp) : ℂ → (Wq →L[ℂ] Wp) :=
  fun ζ => (((j.factorial : ℝ)⁻¹ * ∏ i ∈ Finset.univ \ t, crd (s i) ζ) • X)

/- English proof (translation)
The claim follows from `(contDiff_const.mul (contDiff_prod fun i _ => (crd (s i)).contDiff)).smul contDiff_const`.
-/
theorem wt_smooth (j : ℕ) (s : Fin j → Fin 2) (t : Finset (Fin j)) (X : Wq →L[ℂ] Wp) : ContDiff ℝ ∞ (wt j s t X) :=
  (contDiff_const.mul (contDiff_prod fun i _ => (crd (s i)).contDiff)).smul contDiff_const

/- English proof (translation)
Use function extensionality and compare the values at `ζ`. Establish `hp : ∏ i, crd (s i) (ζ - ζ0) = ∏ i, (-crd (s i) ζ0 + crd (s i) ζ)`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_sub]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [pw, wt, hp, Finset.prod_add, Finset.mul_sum, Finset.sum_smul, smul_smul]`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pw_expand (j : ℕ) (s : Fin j → Fin 2) (ζ0 : ℂ) (X : Wq →L[ℂ] Wp) :
    pw j s ζ0 X = fun ζ => ∑ t ∈ (Finset.univ : Finset (Fin j)).powerset,
      (∏ i ∈ t, -crd (s i) ζ0) • wt j s t X ζ := by
  funext ζ
  have hp : ∏ i, crd (s i) (ζ - ζ0) = ∏ i, (-crd (s i) ζ0 + crd (s i) ζ) := by
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_sub]
    ring
  simp only [pw, wt, hp, Finset.prod_add, Finset.mul_sum, Finset.sum_smul, smul_smul]
  refine Finset.sum_congr rfl fun t _ => ?_
  congr 1
  ring

variable (z z' μs π π' Pr) in

def Bsl (T : Module.End ℂ (Q.RadSp k r z z' π π')) (c0 : Fin r → ℂ) (j : ℕ) (s : Fin j → Fin 2) (ζ0 : ℂ) :
    (Wq →L[ℂ] Wp) →L[ℝ] (Wq →L[ℂ] Wp) :=
  if hG : Gd z z' μs π π' Pr then
    LinearMap.toContinuousLinearMap
      { toFun := fun X => VV z z' μs π π' Pr T c0 (pw j s ζ0 X) ζ0
        map_add' := fun X X' => by
          have e : pw j s ζ0 (X + X') = fun ζ => pw j s ζ0 X ζ + pw j s ζ0 X' ζ := by
            funext ζ
            simp only [pw, smul_add]
          rw [e, VV_add hG (pw_smooth j s ζ0 X) (pw_smooth j s ζ0 X')]
        map_smul' := fun c X => by
          have e : pw j s ζ0 (c • X) = fun ζ => c • pw j s ζ0 X ζ := by
            funext ζ
            simp only [pw]
            rw [smul_comm]
          rw [e, VV_smulR hG (pw_smooth j s ζ0 X)]
          rfl }
  else 0

variable {T : Module.End ℂ (Q.RadSp k r z z' π π')} {c0 : Fin r → ℂ}

/- English proof (translation)
Unfold `Bsl`. Rewrite using `[dif_pos hG]`. Both sides reduce to the same expression.
-/
theorem Bsl_apply (hG : Gd z z' μs π π' Pr) (j : ℕ) (s : Fin j → Fin 2) (ζ0 : ℂ) (X : Wq →L[ℂ] Wp) :
    Bsl z z' μs π π' Pr T c0 j s ζ0 X = VV z z' μs π π' Pr T c0 (pw j s ζ0 X) ζ0 := by
  unfold Bsl
  rw [dif_pos hG]
  rfl

/- English proof (translation)
Rewrite using `[contDiffOn_clm_apply]`. Introduce `X`. Establish `key : ∀ ζ0, Bsl z z' μs π π' Pr T c0 j s ζ0 X = ∑ t ∈ (Finset.univ : Finset (Fin j)).powerset, (∏ i ∈ t, -crd (s i) ζ0) • VV z z' μs π π' Pr T c0 (wt j s t X) ζ0`. Introduce `ζ0`. Rewrite using `[Bsl_apply hG, pw_expand, VV_sum hG _ _ (fun t => (wt_smooth j s t X).const_smul _)]`.

Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Conclude with `VV_smulR hG (wt_smooth j s t X) _ ζ0`. Use `(ContDiffOn.sum fun t _ => ?_).congr fun ζ0 _ => key ζ0` and prove the remaining obligations. Conclude with `(contDiff_prod fun i _ => (crd (s i)).contDiff.neg).contDiffOn.smul (VV_smooth hG hc0)`.
-/
theorem Bsl_smooth (hG : Gd z z' μs π π' Pr) (hc0 : c0 ∈ OmX r) (j : ℕ) (s : Fin j → Fin 2) :
    ContDiffOn ℝ ∞ (fun ζ0 => Bsl z z' μs π π' Pr T c0 j s ζ0) (Ann z z') := by
  rw [contDiffOn_clm_apply]
  intro X
  have key : ∀ ζ0, Bsl z z' μs π π' Pr T c0 j s ζ0 X = ∑ t ∈ (Finset.univ : Finset (Fin j)).powerset,
      (∏ i ∈ t, -crd (s i) ζ0) • VV z z' μs π π' Pr T c0 (wt j s t X) ζ0 := by
    intro ζ0
    rw [Bsl_apply hG, pw_expand, VV_sum hG _ _ (fun t => (wt_smooth j s t X).const_smul _)]
    refine Finset.sum_congr rfl fun t _ => ?_
    exact VV_smulR hG (wt_smooth j s t X) _ ζ0
  refine (ContDiffOn.sum fun t _ => ?_).congr fun ζ0 _ => key ζ0
  exact (contDiff_prod fun i _ => (crd (s i)).contDiff.neg).contDiffOn.smul (VV_smooth hG hc0)

variable (z z' μs π π' Pr T c0) in

def AA (j : ℕ) (ζ0 : ℂ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin j => ℂ) (Wq →L[ℂ] Wp) →L[ℝ] (Wq →L[ℂ] Wp) :=
  ∑ s : Fin j → Fin 2, (Bsl z z' μs π π' Pr T c0 j s ζ0).comp
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => ℂ) (Wq →L[ℂ] Wp) (fun i => e2 (s i)))

/- English proof (translation)
Establish `e : (fun ζ => ((j.factorial : ℝ)⁻¹) • m (fun _ => ζ - ζ0)) = fun ζ => ∑ s : Fin j → Fin 2, pw j s ζ0 (m (fun i => e2 (s i))) ζ`. Use function extensionality and compare the values at `ζ`. Rewrite using `[ml_expand m (ζ - ζ0), Finset.smul_sum]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Simplify using `only [pw, smul_smul]`.

Rewrite using `[e, VV_sum hG _ _ (fun s => pw_smooth j s ζ0 _)]`. Unfold `AA`. Rewrite using `[ContinuousLinearMap.sum_apply]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[ContinuousLinearMap.comp_apply, ContinuousMultilinearMap.apply_apply, Bsl_apply hG]`.
-/
theorem AA_apply (hG : Gd z z' μs π π' Pr) (j : ℕ) (ζ0 : ℂ)
    (m : ContinuousMultilinearMap ℝ (fun _ : Fin j => ℂ) (Wq →L[ℂ] Wp)) :
    AA z z' μs π π' Pr T c0 j ζ0 m =
      VV z z' μs π π' Pr T c0 (fun ζ => ((j.factorial : ℝ)⁻¹) • m (fun _ => ζ - ζ0)) ζ0 := by
  have e : (fun ζ => ((j.factorial : ℝ)⁻¹) • m (fun _ => ζ - ζ0)) =
      fun ζ => ∑ s : Fin j → Fin 2, pw j s ζ0 (m (fun i => e2 (s i))) ζ := by
    funext ζ
    rw [ml_expand m (ζ - ζ0), Finset.smul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [pw, smul_smul]
  rw [e, VV_sum hG _ _ (fun s => pw_smooth j s ζ0 _)]
  unfold AA
  rw [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousMultilinearMap.apply_apply, Bsl_apply hG]

/- English proof (translation)
Establish `e : AA z z' μs π π' Pr T c0 j = fun ζ0 => ∑ s : Fin j → Fin 2, (Bsl z z' μs π π' Pr T c0 j s ζ0).comp (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => ℂ) (Wq →L[ℂ] Wp) (fun i => e2 (s i)))` using `rfl`. Rewrite using `[e]`. Conclude with `ContDiffOn.sum fun s _ => (Bsl_smooth hG hc0 j s).clm_comp contDiffOn_const`.
-/
theorem AA_smooth (hG : Gd z z' μs π π' Pr) (hc0 : c0 ∈ OmX r) (j : ℕ) :
    ContDiffOn ℝ ∞ (AA z z' μs π π' Pr T c0 j) (Ann z z') := by
  have e : AA z z' μs π π' Pr T c0 j = fun ζ0 => ∑ s : Fin j → Fin 2, (Bsl z z' μs π π' Pr T c0 j s ζ0).comp
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => ℂ) (Wq →L[ℂ] Wp) (fun i => e2 (s i))) := rfl
  rw [e]
  exact ContDiffOn.sum fun s _ => (Bsl_smooth hG hc0 j s).clm_comp contDiffOn_const

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.RadTA
