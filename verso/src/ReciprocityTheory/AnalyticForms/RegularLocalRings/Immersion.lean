import ReciprocityTheory.AnalyticForms.RegularLocalRings.ExistsAtlas

namespace ReciprocityTheory.AnForm.R

open MvPolynomial ReciprocityTheory.AnForm.M Topology Filter

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Establish `hy0t : A.chart j x ∈ (A.chart j).target` using `(A.chart j).map_source hj`. Establish `hsy0 : (A.chart j).symm (A.chart j x) = x` using `(A.chart j).left_inv hj`. Use `set f : (Fin e → ℂ) → (Σ k, ι k) → ℂ := fun y => affCoord p (fun q => eval (R.coord i ((A.chart j).symm y)) (R.lift i q)) with hfdef`. Take `⟨O, hO, hxO, -, q, F, hOF⟩` from `R.inv i x hx hxD p hp`. Take `⟨ψ, hψc, hxψ, hψs, hψ⟩` from `hA.2 i x hx (R.sncAt i x hx).r (R.sncAt i x hx).span_eq O hO hxO`.

Use `set r := (R.sncAt i x hx).r with hr`. Establish `hw0 : f (A.chart j x) = affCoord p (fun q => eval (R.coord i x) (R.lift i q))`. Simplify using `only [f, hsy0]`. Establish `hqw0 : eval (f (A.chart j x)) q ≠ 0` using `by rw [hw0]; exact (hOF x hxO).2.1`. Set `H : ((Σ k, ι k) → ℂ) → Fin (R.amb i) → ℂ` to `fun w l => eval w (F l) / eval w q`.

Set `G : ((Σ k, ι k) → ℂ) → Fin e → ℂ` to `fun w => (A.chart j ∘ ψ.symm) (evalFam r (H w))`. Establish `hHx : ∀ y ∈ O, H (affCoord p fun q => eval (R.coord i y) (R.lift i q)) = R.coord i y`. Introduce `y hy`. Use function extensionality and compare the values at `l`. Simplify using `only [H]`.

Rewrite using `[div_eq_iff (hOF y hy).2.1]`. Conclude with `((hOF y hy).2.2 l).symm`. Establish `hH0 : H (f (A.chart j x)) = R.coord i x` using `by rw [hw0]; exact hHx x hxO`. Establish `hHan : AnalyticAt ℂ H (f (A.chart j x))`. Rewrite using `[analyticAt_pi_iff]`.

Introduce `l`. Conclude with `(AnalyticOnNhd.eval_mvPolynomial (F l) _ (Set.mem_univ _)).div (AnalyticOnNhd.eval_mvPolynomial q _ (Set.mem_univ _)) hqw0`. Establish `hEan : AnalyticAt ℂ (evalFam r) (H (f (A.chart j x)))`. Rewrite using `[analyticAt_pi_iff]`. Introduce `l`.

Conclude with `AnalyticOnNhd.eval_mvPolynomial (r l) _ (Set.mem_univ _)`. Establish `hTan : AnalyticAt ℂ (A.chart j ∘ ψ.symm) (evalFam r (H (f (A.chart j x))))`. Rewrite using `[hH0, ← hψ x hxψ]`. Use `(hψc j).2 (ψ x) ⟨ψ.map_source hxψ, ?_⟩` and prove the remaining obligations. Use `show ψ.symm (ψ x) ∈ (A.chart j).source`.

Rewrite using `[ψ.left_inv hxψ]`. Conclude with `hj`. Establish `hGd : DifferentiableAt ℂ G (f (A.chart j x))` using `DifferentiableAt.comp (g := A.chart j ∘ ψ.symm) (f := evalFam r ∘ H) (f (A.chart j x)) hTan.differentiableAt (DifferentiableAt.comp (f (A.chart j x)) hEan.differentiableAt hHan.differentiableAt)`. Establish `hfd : DifferentiableAt ℂ f (A.chart j x)`. Rewrite using `[differentiableAt_pi]`.

Introduce `q'`. Establish `hmem : A.chart j x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' R.src i` using `⟨hy0t, by show (A.chart j).symm (A.chart j x) ∈ R.src i; rw [hsy0]; exact hx⟩`. Establish `h1` using `hA.1 i (R.lift i q') j (A.chart j x) hmem`. Establish `h2` using `hA.1 i (R.lift i ⟨q'.1, p q'.1⟩) j (A.chart j x) hmem`. Establish `hne : ((fun y => eval (R.coord i y) (R.lift i ⟨q'.1, p q'.1⟩)) ∘ (A.chart j).symm) (A.chart j x) ≠ 0`.

Simplify using `only [Function.comp, hsy0]`. Conclude with `hp q'.1`. Conclude with `(h1.div h2 hne).differentiableAt`. Establish `hev : (G ∘ f) =ᶠ[𝓝 (A.chart j x)] id`. Establish `h1 : ∀ᶠ y in 𝓝 (A.chart j x), y ∈ (A.chart j).target` using `(A.chart j).open_target.mem_nhds hy0t`.

Establish `h2 : ∀ᶠ y in 𝓝 (A.chart j x), (A.chart j).symm y ∈ ψ.source` using `((A.chart j).continuousAt_symm hy0t).preimage_mem_nhds (ψ.open_source.mem_nhds (by rw [hsy0]; exact hxψ))`. Use `filter_upwards [h1, h2] with y hy1 hy2`. Establish `hy'O : (A.chart j).symm y ∈ O` using `(hψs hy2).1`. Use `show (A.chart j) (ψ.symm (evalFam r (H (f y)))) = y`. Establish `hfy : f y = affCoord p (fun q => eval (R.coord i ((A.chart j).symm y)) (R.lift i q))` using `rfl`.

Rewrite using `[hfy, hHx _ hy'O, ← hψ _ hy2, ψ.left_inv hy2, (A.chart j).right_inv hy1]`. Establish `hcomp` using `hGd.hasFDerivAt.comp (A.chart j x) hfd.hasFDerivAt`. Establish `huniq` using `hcomp.unique ((hasFDerivAt_id (A.chart j x)).congr_of_eventuallyEq hev)`. Rewrite using `[LinearMap.ker_eq_bot']`. Introduce `v hv`.

Use `congrArg (fun L : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ) => L v) huniq` as an intermediate fact. Simplify using `only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at this`. Establish `hv' : fderiv ℂ f (A.chart j x) v = 0` using `hv`. Rewrite using `[← this, hv', map_zero]`.
-/
theorem AlgRes.fderiv_affCoord_ker_eq_bot {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ}
    (R : AlgRes ι P D e) (A : FinHolAtlas e R.M) (hA : R.IsGoodAtlas A) (i : Fin R.n)
    (x : R.M) (hx : x ∈ R.src i) (hxD : (fun q => eval (R.coord i x) (R.lift i q)) ∉ conePts D)
    (p : (k : K) → ι k) (hp : ∀ k, eval (R.coord i x) (R.lift i ⟨k, p k⟩) ≠ 0)
    (j : Fin A.n) (hj : x ∈ (A.chart j).source) :
    (fderiv ℂ (fun y => affCoord p (fun q => eval (R.coord i ((A.chart j).symm y)) (R.lift i q)))
      (A.chart j x)).ker = ⊥ := by
  classical
  have hy0t : A.chart j x ∈ (A.chart j).target := (A.chart j).map_source hj
  have hsy0 : (A.chart j).symm (A.chart j x) = x := (A.chart j).left_inv hj
  set f : (Fin e → ℂ) → (Σ k, ι k) → ℂ :=
    fun y => affCoord p (fun q => eval (R.coord i ((A.chart j).symm y)) (R.lift i q)) with hfdef
  obtain ⟨O, hO, hxO, -, q, F, hOF⟩ := R.inv i x hx hxD p hp
  obtain ⟨ψ, hψc, hxψ, hψs, hψ⟩ :=
    hA.2 i x hx (R.sncAt i x hx).r (R.sncAt i x hx).span_eq O hO hxO
  set r := (R.sncAt i x hx).r with hr
  have hw0 : f (A.chart j x) = affCoord p (fun q => eval (R.coord i x) (R.lift i q)) := by
    simp only [f, hsy0]
  have hqw0 : eval (f (A.chart j x)) q ≠ 0 := by rw [hw0]; exact (hOF x hxO).2.1
  let H : ((Σ k, ι k) → ℂ) → Fin (R.amb i) → ℂ := fun w l => eval w (F l) / eval w q
  let G : ((Σ k, ι k) → ℂ) → Fin e → ℂ := fun w => (A.chart j ∘ ψ.symm) (evalFam r (H w))
  have hHx : ∀ y ∈ O, H (affCoord p fun q => eval (R.coord i y) (R.lift i q)) = R.coord i y := by
    intro y hy; funext l; simp only [H]; rw [div_eq_iff (hOF y hy).2.1]; exact ((hOF y hy).2.2 l).symm
  have hH0 : H (f (A.chart j x)) = R.coord i x := by rw [hw0]; exact hHx x hxO
  have hHan : AnalyticAt ℂ H (f (A.chart j x)) := by
    rw [analyticAt_pi_iff]; intro l
    exact (AnalyticOnNhd.eval_mvPolynomial (F l) _ (Set.mem_univ _)).div
      (AnalyticOnNhd.eval_mvPolynomial q _ (Set.mem_univ _)) hqw0
  have hEan : AnalyticAt ℂ (evalFam r) (H (f (A.chart j x))) := by
    rw [analyticAt_pi_iff]; intro l
    exact AnalyticOnNhd.eval_mvPolynomial (r l) _ (Set.mem_univ _)
  have hTan : AnalyticAt ℂ (A.chart j ∘ ψ.symm) (evalFam r (H (f (A.chart j x)))) := by
    rw [hH0, ← hψ x hxψ]
    refine (hψc j).2 (ψ x) ⟨ψ.map_source hxψ, ?_⟩
    show ψ.symm (ψ x) ∈ (A.chart j).source
    rw [ψ.left_inv hxψ]; exact hj
  have hGd : DifferentiableAt ℂ G (f (A.chart j x)) :=
    DifferentiableAt.comp (g := A.chart j ∘ ψ.symm) (f := evalFam r ∘ H) (f (A.chart j x))
      hTan.differentiableAt
      (DifferentiableAt.comp (f (A.chart j x)) hEan.differentiableAt hHan.differentiableAt)
  have hfd : DifferentiableAt ℂ f (A.chart j x) := by
    rw [differentiableAt_pi]; intro q'
    have hmem : A.chart j x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' R.src i :=
      ⟨hy0t, by show (A.chart j).symm (A.chart j x) ∈ R.src i; rw [hsy0]; exact hx⟩
    have h1 := hA.1 i (R.lift i q') j (A.chart j x) hmem
    have h2 := hA.1 i (R.lift i ⟨q'.1, p q'.1⟩) j (A.chart j x) hmem
    have hne : ((fun y => eval (R.coord i y) (R.lift i ⟨q'.1, p q'.1⟩)) ∘ (A.chart j).symm)
        (A.chart j x) ≠ 0 := by
      simp only [Function.comp, hsy0]; exact hp q'.1
    exact (h1.div h2 hne).differentiableAt
  have hev : (G ∘ f) =ᶠ[𝓝 (A.chart j x)] id := by
    have h1 : ∀ᶠ y in 𝓝 (A.chart j x), y ∈ (A.chart j).target :=
      (A.chart j).open_target.mem_nhds hy0t
    have h2 : ∀ᶠ y in 𝓝 (A.chart j x), (A.chart j).symm y ∈ ψ.source :=
      ((A.chart j).continuousAt_symm hy0t).preimage_mem_nhds
        (ψ.open_source.mem_nhds (by rw [hsy0]; exact hxψ))
    filter_upwards [h1, h2] with y hy1 hy2
    have hy'O : (A.chart j).symm y ∈ O := (hψs hy2).1
    show (A.chart j) (ψ.symm (evalFam r (H (f y)))) = y
    have hfy : f y = affCoord p (fun q => eval (R.coord i ((A.chart j).symm y)) (R.lift i q)) := rfl
    rw [hfy, hHx _ hy'O, ← hψ _ hy2, ψ.left_inv hy2, (A.chart j).right_inv hy1]
  have hcomp := hGd.hasFDerivAt.comp (A.chart j x) hfd.hasFDerivAt
  have huniq := hcomp.unique ((hasFDerivAt_id (A.chart j x)).congr_of_eventuallyEq hev)
  rw [LinearMap.ker_eq_bot']
  intro v hv
  have := congrArg (fun L : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ) => L v) huniq
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at this
  have hv' : fderiv ℂ f (A.chart j x) v = 0 := hv
  rw [← this, hv', map_zero]

end ReciprocityTheory.AnForm.R
