import ReciprocityTheory.AnalyticForms.RegularLocalRings.IsOpenAlt
import ReciprocityTheory.AnalyticForms.RegularLocalRings.AnChart
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun

namespace ReciprocityTheory.AnForm.R

open MvPolynomial ReciprocityTheory.AnForm.M Topology Filter

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ}

/- English proof (translation)
Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C a`. Simplify using `only [eval_C]`. Conclude with `analyticAt_const`. Consider the case `add p q hp hq`.

Simplify using `only [map_add]`. Conclude with `hp.add hq`. Consider the case `mul_X p l hp`. Simplify using `only [map_mul, eval_X]`. Conclude with `hp.mul (hf l)`.
-/
theorem analyticAt_eval_of_pi {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {σ : Type*}
    {f : E → σ → ℂ} {z : E} (hf : ∀ l, AnalyticAt ℂ (f · l) z) (p : MvPolynomial σ ℂ) :
    AnalyticAt ℂ (fun x => eval (f x) p) z := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [eval_C]
    exact analyticAt_const
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  | mul_X p l hp =>
    simp only [map_mul, eval_X]
    exact hp.mul (hf l)

def AlgRes.GoodChart (R : AlgRes ι P D e) (ψ : OpenPartialHomeomorph R.M (Fin e → ℂ)) : Prop :=
  ∃ i, ψ.source ⊆ R.src i ∧
    (∃ r : Fin e → MvPolynomial (Fin (R.amb i)) ℂ, ∀ y ∈ ψ.source, ψ y = evalFam r (R.coord i y)) ∧
    ∃ g : (Fin e → ℂ) → Fin (R.amb i) → ℂ, AnalyticOnNhd ℂ g ψ.target ∧
      ∀ w ∈ ψ.target, R.coord i (ψ.symm w) = g w

/- English proof (translation)
Establish `hwS : ψ.symm w ∈ ψ.source` using `ψ.map_target hw`. Establish `hxi : ψ.symm w ∈ R.src i` using `hs hwS`. Take `⟨q, F, hq0, hqF⟩` from `R.trans i j (ψ.symm w) ⟨hxi, hwj⟩`. Establish `hgw : AnalyticAt ℂ g w` using `hg w hw`. Establish `hga : ∀ l, AnalyticAt ℂ (g · l) w` using `fun l => ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (R.amb i) => ℂ) l).analyticAt (g w)).comp hgw`.

Establish `hFa : ∀ l, AnalyticAt ℂ (fun w' => eval (g w') (F l)) w` using `fun l => analyticAt_eval_of_pi hga (F l)`. Establish `hqa : AnalyticAt ℂ (fun w' => eval (g w') q) w` using `analyticAt_eval_of_pi hga q`. Establish `hq0' : eval (g w) q ≠ 0`. Rewrite using `[← hgc w hw]`. Conclude with `hq0`.

Establish `hA : AnalyticAt ℂ (fun w' => eval (fun l => eval (g w') (F l) / eval (g w') q) h) w` using `analyticAt_eval_of_pi (f := fun w' l => eval (g w') (F l) / eval (g w') q) (fun l => (hFa l).div hqa hq0') h`. Use `hA.congr ?_` and prove the remaining obligations. Establish `ht : ψ.target ∈ 𝓝 w` using `ψ.open_target.mem_nhds hw`. Establish `hj : ∀ᶠ w' in 𝓝 w, ψ.symm w' ∈ R.src j` using `(ψ.continuousAt_symm hw).preimage_mem_nhds ((R.isOpen_alt_bis j).mem_nhds hwj)`. Establish `hqne : ∀ᶠ w' in 𝓝 w, eval (g w') q ≠ 0` using `hqa.continuousAt.eventually_ne hq0'`.

Use `filter_upwards [ht, hj, hqne] with w' h1 h2 h3`. Establish `hsrc : ψ.symm w' ∈ R.src i` using `hs (ψ.map_target h1)`. Establish `hcw : R.coord i (ψ.symm w') = g w'` using `hgc w' h1`. Establish `hfun : (fun l => eval (g w') (F l) / eval (g w') q) = R.coord j (ψ.symm w')`. Use function extensionality and compare the values at `l`.

Establish `hl` using `hqF (ψ.symm w') ⟨hsrc, h2⟩ (by rw [hcw]; exact h3) l`. Rewrite `hl` using `[hcw]`. Rewrite using `[div_eq_iff h3]`. Conclude with `hl.symm`. Conclude with `congrArg (fun v => eval v h) hfun`.
-/
theorem AlgRes.analyticAt_coord_symm (R : AlgRes ι P D e)
    {ψ : OpenPartialHomeomorph R.M (Fin e → ℂ)} {i : Fin R.n} (hs : ψ.source ⊆ R.src i)
    {g : (Fin e → ℂ) → Fin (R.amb i) → ℂ} (hg : AnalyticOnNhd ℂ g ψ.target)
    (hgc : ∀ w ∈ ψ.target, R.coord i (ψ.symm w) = g w)
    (j : Fin R.n) (h : MvPolynomial (Fin (R.amb j)) ℂ) {w : Fin e → ℂ} (hw : w ∈ ψ.target)
    (hwj : ψ.symm w ∈ R.src j) :
    AnalyticAt ℂ (fun w => eval (R.coord j (ψ.symm w)) h) w := by
  have hwS : ψ.symm w ∈ ψ.source := ψ.map_target hw
  have hxi : ψ.symm w ∈ R.src i := hs hwS
  obtain ⟨q, F, hq0, hqF⟩ := R.trans i j (ψ.symm w) ⟨hxi, hwj⟩
  have hgw : AnalyticAt ℂ g w := hg w hw
  have hga : ∀ l, AnalyticAt ℂ (g · l) w := fun l =>
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (R.amb i) => ℂ) l).analyticAt (g w)).comp hgw
  have hFa : ∀ l, AnalyticAt ℂ (fun w' => eval (g w') (F l)) w := fun l =>
    analyticAt_eval_of_pi hga (F l)
  have hqa : AnalyticAt ℂ (fun w' => eval (g w') q) w := analyticAt_eval_of_pi hga q
  have hq0' : eval (g w) q ≠ 0 := by
    rw [← hgc w hw]
    exact hq0
  have hA : AnalyticAt ℂ (fun w' => eval (fun l => eval (g w') (F l) / eval (g w') q) h) w :=
    analyticAt_eval_of_pi (f := fun w' l => eval (g w') (F l) / eval (g w') q)
      (fun l => (hFa l).div hqa hq0') h
  refine hA.congr ?_
  have ht : ψ.target ∈ 𝓝 w := ψ.open_target.mem_nhds hw
  have hj : ∀ᶠ w' in 𝓝 w, ψ.symm w' ∈ R.src j :=
    (ψ.continuousAt_symm hw).preimage_mem_nhds ((R.isOpen_alt_bis j).mem_nhds hwj)
  have hqne : ∀ᶠ w' in 𝓝 w, eval (g w') q ≠ 0 := hqa.continuousAt.eventually_ne hq0'
  filter_upwards [ht, hj, hqne] with w' h1 h2 h3
  have hsrc : ψ.symm w' ∈ R.src i := hs (ψ.map_target h1)
  have hcw : R.coord i (ψ.symm w') = g w' := hgc w' h1
  have hfun : (fun l => eval (g w') (F l) / eval (g w') q) = R.coord j (ψ.symm w') := by
    funext l
    have hl := hqF (ψ.symm w') ⟨hsrc, h2⟩ (by rw [hcw]; exact h3) l
    rw [hcw] at hl
    rw [div_eq_iff h3]
    exact hl.symm
  exact congrArg (fun v => eval v h) hfun

/- English proof (translation)
Take `⟨i, hsi, -, g, hg, hgc⟩` from `hψ`. Introduce and unpack `w ⟨hw, hwS⟩`. Establish `hwS' : ψ.symm w ∈ S` using `hwS`. Establish `hev : (fun w' => evalFam r (R.coord j (ψ.symm w'))) =ᶠ[𝓝 w] (f ∘ ψ.symm)`. Establish `hS' : ∀ᶠ w' in 𝓝 w, ψ.symm w' ∈ S` using `(ψ.continuousAt_symm hw).preimage_mem_nhds (hS.mem_nhds hwS')`.

Use `filter_upwards [hS'] with w' h1`. Conclude with `(hf _ h1).symm`. Use `AnalyticAt.congr ?_ hev` and prove the remaining obligations. Rewrite using `[analyticAt_pi_iff]`. Introduce `l`.

Conclude with `R.analyticAt_coord_symm hsi hg hgc j (r l) hw (hSj hwS')`.
-/
theorem AlgRes.analyticOnNhd_comp_symm (R : AlgRes ι P D e)
    {ψ : OpenPartialHomeomorph R.M (Fin e → ℂ)} (hψ : R.GoodChart ψ) {m : ℕ}
    (f : R.M → Fin m → ℂ) (S : Set R.M) (hS : IsOpen S) (j : Fin R.n) (hSj : S ⊆ R.src j)
    (r : Fin m → MvPolynomial (Fin (R.amb j)) ℂ) (hf : ∀ y ∈ S, f y = evalFam r (R.coord j y)) :
    AnalyticOnNhd ℂ (f ∘ ψ.symm) (ψ.target ∩ ψ.symm ⁻¹' S) := by
  obtain ⟨i, hsi, -, g, hg, hgc⟩ := hψ
  rintro w ⟨hw, hwS⟩
  have hwS' : ψ.symm w ∈ S := hwS
  have hev : (fun w' => evalFam r (R.coord j (ψ.symm w'))) =ᶠ[𝓝 w] (f ∘ ψ.symm) := by
    have hS' : ∀ᶠ w' in 𝓝 w, ψ.symm w' ∈ S :=
      (ψ.continuousAt_symm hw).preimage_mem_nhds (hS.mem_nhds hwS')
    filter_upwards [hS'] with w' h1
    exact (hf _ h1).symm
  refine AnalyticAt.congr ?_ hev
  rw [analyticAt_pi_iff]
  intro l
  exact R.analyticAt_coord_symm hsi hg hgc j (r l) hw (hSj hwS')

/- English proof (translation)
Use `R.regular i x hx` as an intermediate fact. Take `⟨U, V, g, hU, hpU, hV, hg, hbij, hrg⟩` from `exists_holo_coords (R.ideal i) (R.coord i x) e (R.dim i x hx) r hr`. Establish `hcont : ContinuousOn (R.coord i) (R.src i)`. Rewrite using `[continuousOn_iff_continuous_domRestrict]`. Conclude with `(R.isEmbedding i).continuous`.

Establish `hinj : Set.InjOn (R.coord i) (R.src i)` using `fun a ha b hb hab => congrArg Subtype.val ((R.isEmbedding i).injective (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) hab)`. Establish `hev : Continuous (evalFam r)` using `continuous_pi fun l => MvPolynomial.continuous_eval (p := r l)`. Establish `hzero : ∀ y ∈ R.src i, R.coord i y ∈ zeroSet (R.ideal i)`. Introduce `y hy`. Establish `: R.coord i y ∈ R.coord i '' R.src i` using `⟨y, hy, rfl⟩`.

Rewrite `this` using `[R.image i]`. Conclude with `this`. Establish `hex : ∀ w ∈ V, ∃ y ∈ R.src i, R.coord i y = g w`. Introduce `w hw`. Establish `h1 : g w ∈ zeroSet (R.ideal i)` using `(hbij.mapsTo hw).2`.

Establish `hmem : g w ∈ R.coord i '' R.src i` using `by rw [R.image i]; exact h1`. Take `⟨y, hy, hyw⟩` from `hmem`. Conclude with `⟨y, hy, hyw⟩`. Set `inv : (Fin e → ℂ) → R.M` to `fun w => if h : ∃ y ∈ R.src i, R.coord i y = g w then h.choose else x`. Establish `hinv : ∀ w ∈ V, inv w ∈ R.src i ∧ R.coord i (inv w) = g w`.

Introduce `w hw`. Establish `h` using `hex w hw`. Simplify using `only [inv, dif_pos h]`. Conclude with `h.choose_spec`. Establish `hback : ∀ y ∈ R.src i, R.coord i y ∈ U → g (evalFam r (R.coord i y)) = R.coord i y`.

Introduce `y hy hyU`. Take `⟨w, hw, hgw⟩` from `hbij.surjOn ⟨hyU, hzero y hy⟩`. Rewrite using `[← hgw, hrg w hw]`. Set `S : Set R.M` to `R.src i ∩ R.coord i ⁻¹' (U ∩ evalFam r ⁻¹' V)`. Establish `hSo : IsOpen S` using `hcont.isOpen_inter_preimage (R.isOpen_alt_bis i) (hU.inter (hV.preimage hev))`.

Establish `hmapT : ∀ w ∈ V, inv w ∈ S`. Introduce `w hw`. Take `⟨h1, h2⟩` from `hinv w hw`. Use `⟨h1, ?_⟩` and prove the remaining obligations. Use `show R.coord i (inv w) ∈ U ∩ evalFam r ⁻¹' V`.

Rewrite using `[h2]`. Use `⟨(hbij.mapsTo hw).1, ?_⟩` and prove the remaining obligations. Use `show evalFam r (g w) ∈ V`. Rewrite using `[hrg w hw]`. Conclude with `hw`.

Establish `hcinv : ContinuousOn inv V`. Rewrite using `[continuousOn_iff_continuous_domRestrict]`. Set `f : V → R.src i` to `fun w => ⟨inv w, (hinv w w.2).1⟩`. Establish `hf : Continuous f`. Rewrite using `[(R.isEmbedding i).continuous_iff]`.

Establish `: ((fun y : R.src i => R.coord i y) ∘ f) = fun w : V => g w`. Use function extensionality and compare the values at `fun w => (hinv w w.2).2`. Rewrite using `[this]`. Conclude with `hg.continuousOn.domRestrict`. Conclude with `continuous_subtype_val.comp hf`.

Set `ψ0 : OpenPartialHomeomorph R.M (Fin e → ℂ)` to `{ toFun := fun y => evalFam r (R.coord i y) invFun := inv source := S target := V map_source' := fun y hy => hy.2.2 map_target' := fun w hw => hmapT w hw left_inv' := fun y hy => by`. Take `⟨h1, h2⟩` from `hinv _ hy.2.2`. Conclude with `hinj h1 hy.1 (h2.trans (hback y hy.1 hy.2.1))`. Use the proof step `right_inv' := fun w hw => by`. Take `⟨-, h2⟩` from `hinv w hw`.

Use `show evalFam r (R.coord i (inv w)) = w`. Rewrite using `[h2, hrg w hw]`. Use `open_source := hSo`. Use `open_target := hV`. Use `continuousOn_toFun := (hev.comp_continuousOn hcont).mono fun y hy => hy.1`.

Use `continuousOn_invFun := hcinv }`. Establish `hxS : x ∈ S`. Take `⟨w, hw, hgw⟩` from `hbij.surjOn ⟨hpU, hzero x hx⟩`. Use `⟨hx, hpU, ?_⟩` and prove the remaining obligations. Use `show evalFam r (R.coord i x) ∈ V`.

Rewrite using `[← hgw, hrg w hw]`. Conclude with `hw`. Use `⟨ψ0.restrOpen O hO, ⟨i, fun y hy => hy.1.1, ⟨r, fun y _ => rfl⟩, g, hg.mono fun w hw => hw.1, fun w hw => (hinv w hw.1).2⟩, ⟨hxS, hxO⟩, fun y hy => ⟨hy.2, hy.1.1⟩, fun y _ => rfl⟩` and prove the remaining obligations.
-/
theorem AlgRes.exists_goodChart (R : AlgRes ι P D e) (i : Fin R.n) (x : R.M) (hx : x ∈ R.src i)
    (r : Fin e → MvPolynomial (Fin (R.amb i)) ℂ)
    (hr : Ideal.span (Set.range fun l => algebraMap _ (locRing (R.ideal i) (R.coord i x)) (r l)) =
      Ideal.map (algebraMap _ (locRing (R.ideal i) (R.coord i x))) (ptIdeal (R.coord i x)))
    (O : Set R.M) (hO : IsOpen O) (hxO : x ∈ O) :
    ∃ ψ : OpenPartialHomeomorph R.M (Fin e → ℂ), R.GoodChart ψ ∧ x ∈ ψ.source ∧
      ψ.source ⊆ O ∩ R.src i ∧ ∀ y ∈ ψ.source, ψ y = evalFam r (R.coord i y) := by
  have := R.regular i x hx
  obtain ⟨U, V, g, hU, hpU, hV, hg, hbij, hrg⟩ :=
    exists_holo_coords (R.ideal i) (R.coord i x) e (R.dim i x hx) r hr
  have hcont : ContinuousOn (R.coord i) (R.src i) := by
    rw [continuousOn_iff_continuous_domRestrict]; exact (R.isEmbedding i).continuous
  have hinj : Set.InjOn (R.coord i) (R.src i) := fun a ha b hb hab =>
    congrArg Subtype.val ((R.isEmbedding i).injective (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) hab)
  have hev : Continuous (evalFam r) := continuous_pi fun l => MvPolynomial.continuous_eval (p := r l)
  have hzero : ∀ y ∈ R.src i, R.coord i y ∈ zeroSet (R.ideal i) := by
    intro y hy
    have : R.coord i y ∈ R.coord i '' R.src i := ⟨y, hy, rfl⟩
    rw [R.image i] at this
    exact this
  have hex : ∀ w ∈ V, ∃ y ∈ R.src i, R.coord i y = g w := by
    intro w hw
    have h1 : g w ∈ zeroSet (R.ideal i) := (hbij.mapsTo hw).2
    have hmem : g w ∈ R.coord i '' R.src i := by rw [R.image i]; exact h1
    obtain ⟨y, hy, hyw⟩ := hmem
    exact ⟨y, hy, hyw⟩
  classical
  let inv : (Fin e → ℂ) → R.M := fun w =>
    if h : ∃ y ∈ R.src i, R.coord i y = g w then h.choose else x
  have hinv : ∀ w ∈ V, inv w ∈ R.src i ∧ R.coord i (inv w) = g w := by
    intro w hw
    have h := hex w hw
    simp only [inv, dif_pos h]
    exact h.choose_spec
  have hback : ∀ y ∈ R.src i, R.coord i y ∈ U → g (evalFam r (R.coord i y)) = R.coord i y := by
    intro y hy hyU
    obtain ⟨w, hw, hgw⟩ := hbij.surjOn ⟨hyU, hzero y hy⟩
    rw [← hgw, hrg w hw]
  let S : Set R.M := R.src i ∩ R.coord i ⁻¹' (U ∩ evalFam r ⁻¹' V)
  have hSo : IsOpen S := hcont.isOpen_inter_preimage (R.isOpen_alt_bis i) (hU.inter (hV.preimage hev))
  have hmapT : ∀ w ∈ V, inv w ∈ S := by
    intro w hw
    obtain ⟨h1, h2⟩ := hinv w hw
    refine ⟨h1, ?_⟩
    show R.coord i (inv w) ∈ U ∩ evalFam r ⁻¹' V
    rw [h2]
    refine ⟨(hbij.mapsTo hw).1, ?_⟩
    show evalFam r (g w) ∈ V
    rw [hrg w hw]
    exact hw
  have hcinv : ContinuousOn inv V := by
    rw [continuousOn_iff_continuous_domRestrict]
    let f : V → R.src i := fun w => ⟨inv w, (hinv w w.2).1⟩
    have hf : Continuous f := by
      rw [(R.isEmbedding i).continuous_iff]
      have : ((fun y : R.src i => R.coord i y) ∘ f) = fun w : V => g w :=
        funext fun w => (hinv w w.2).2
      rw [this]
      exact hg.continuousOn.domRestrict
    exact continuous_subtype_val.comp hf
  let ψ0 : OpenPartialHomeomorph R.M (Fin e → ℂ) :=
    { toFun := fun y => evalFam r (R.coord i y)
      invFun := inv
      source := S
      target := V
      map_source' := fun y hy => hy.2.2
      map_target' := fun w hw => hmapT w hw
      left_inv' := fun y hy => by
        obtain ⟨h1, h2⟩ := hinv _ hy.2.2
        exact hinj h1 hy.1 (h2.trans (hback y hy.1 hy.2.1))
      right_inv' := fun w hw => by
        obtain ⟨-, h2⟩ := hinv w hw
        show evalFam r (R.coord i (inv w)) = w
        rw [h2, hrg w hw]
      open_source := hSo
      open_target := hV
      continuousOn_toFun := (hev.comp_continuousOn hcont).mono fun y hy => hy.1
      continuousOn_invFun := hcinv }
  have hxS : x ∈ S := by
    obtain ⟨w, hw, hgw⟩ := hbij.surjOn ⟨hpU, hzero x hx⟩
    refine ⟨hx, hpU, ?_⟩
    show evalFam r (R.coord i x) ∈ V
    rw [← hgw, hrg w hw]
    exact hw
  refine ⟨ψ0.restrOpen O hO, ⟨i, fun y hy => hy.1.1, ⟨r, fun y _ => rfl⟩, g,
    hg.mono fun w hw => hw.1, fun w hw => (hinv w hw.1).2⟩, ⟨hxS, hxO⟩,
    fun y hy => ⟨hy.2, hy.1.1⟩, fun y _ => rfl⟩

end ReciprocityTheory.AnForm.R
