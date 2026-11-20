import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.PerDeriv
open UpperTheory.V.Sd.Eis

open NumberField MeasureTheory GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Sd in
/- English proof (translation)
Use `Continuous.units_map _ ?_` and prove the remaining obligations. Establish `hs : Continuous (TR.sInf F : TR.Rinf F → Ad F)` using `(TR.continuous_infEq F).prodMk continuous_const`. Conclude with `continuous_const.sub continuous_const |>.add (continuous_id.matrix_map hs)`.
-/
private theorem ct_cont_infGL (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ) :
    Continuous (TR.infGL F a) := by
  refine Continuous.units_map _ ?_
  have hs : Continuous (TR.sInf F : TR.Rinf F → Ad F) := (TR.continuous_infEq F).prodMk continuous_const
  exact continuous_const.sub continuous_const |>.add (continuous_id.matrix_map hs)

open NumberField MeasureTheory GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Sd in
/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;>`. Simplify using `[aff, ratGL, Matrix.mul_apply, Fin.sum_univ_succ, add_comm]`.
-/
private theorem ct_aff_add (F : Type) [Field F] [NumberField F] (y : F) (x : Ad F) :
    (aff 1 (algebraMap F (Ad F) y + x) : GA F 2) = ratGL F 2 (aff 1 y) * aff 1 x := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [aff, ratGL, Matrix.mul_apply, Fin.sum_univ_succ, add_comm]

open NumberField MeasureTheory GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Sd in
/- English proof (translation)
Set `S : TR.Sm F a → Subgroup (GL (Fin a) (Af F))` to `fun ψ => { carrier := {k | TR.finRep F a k ψ = ψ} one_mem' := by simp mul_mem' := fun {x y} hx hy => by`. Simplify using `only [Set.mem_setOf_eq] at *`. Rewrite using `[map_mul, Module.End.mul_apply, hy, hx]`. Use the proof step `inv_mem' := fun {x} hx => by`. Simplify using `only [Set.mem_setOf_eq] at *`.

Use `conv_lhs => rw [← hx]`. Rewrite using `[← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }`. Use `Subgroup.isOpen_mono (H₁ := S φ) (H₂ := S (TR.lie F a X φ)) (fun k hk => ?_) h` and prove the remaining obligations. Establish `hk' : TR.rt F a (finGL F a k) φ = φ` using `hk`. Establish `e` using `LinearMap.congr_fun (TR.lie_rt_fin X k) φ`.

Rewrite `e` using `[Module.End.mul_apply, Module.End.mul_apply, hk']`. Conclude with `e.symm`.
-/
private theorem ct_level (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ) (φ : TR.Sm F a) (X : TR.Lie F a)
    (h : IsOpen {k | TR.finRep F a k φ = φ}) : IsOpen {k | TR.finRep F a k (TR.lie F a X φ) = TR.lie F a X φ} := by
  let S : TR.Sm F a → Subgroup (GL (Fin a) (Af F)) := fun ψ =>
    { carrier := {k | TR.finRep F a k ψ = ψ}
      one_mem' := by simp
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq] at *
        rw [map_mul, Module.End.mul_apply, hy, hx]
      inv_mem' := fun {x} hx => by
        simp only [Set.mem_setOf_eq] at *
        conv_lhs => rw [← hx]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  refine Subgroup.isOpen_mono (H₁ := S φ) (H₂ := S (TR.lie F a X φ)) (fun k hk => ?_) h
  have hk' : TR.rt F a (finGL F a k) φ = φ := hk
  have e := LinearMap.congr_fun (TR.lie_rt_fin X k) φ
  rw [Module.End.mul_apply, Module.End.mul_apply, hk'] at e
  exact e.symm

open NumberField MeasureTheory GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Sd in
/- English proof (translation)
Introduce `hS hM hD hB F _ _ _ _ _ μ _ D hF φ hl ho X`. Establish `hl' : ∀ γ g, (TR.lie F 2 X φ).1 (ratGL F 2 γ * g) = (TR.lie F 2 X φ).1 g`. Introduce `γ g`. Establish `e : TR.chart φ.1 (ratGL F 2 γ * g) = TR.chart φ.1 g`. Use function extensionality and compare the values at `x`.

Simplify using `only [TR.chart, mul_assoc, hl]`. Simplify using `only [TR.lie_apply, TR.lieD, e]`. Establish `hc' : Continuous (TR.lie F 2 X φ).1` using `hS F 2 _ (ct_level F 2 φ X ho)`. Establish `hc : Continuous φ.1` using `hS F 2 _ ho`. Use `⟨⟨hl', hc'⟩, fun c hcc hmul hder g => ?_⟩` and prove the remaining obligations.

Take `⟨i1, i2, i3, i4, hco, hu, hx⟩` from `hB F`. Establish `h0 : c 0 = 1`. Use `hmul 0 0` as an intermediate fact. Rewrite `this` using `[add_zero]`. Conclude with `left_eq_mul.1 this`.

Establish `hfin` using `(hM (NA F) (ratN F 2 1) hco μ D hF).1`. Establish `hcont : Continuous fun p : NA F × ℝ => (unip p.1 : GA F 2) * (g * TR.infGL F 2 (c p.2))` using `(hu.comp continuous_fst).mul (continuous_const.mul ((ct_cont_infGL F 2).comp (hcc.comp continuous_snd)))`. Establish `hper : ∀ ψ : GA F 2 → ℂ, (∀ γ g, ψ (ratGL F 2 γ * g) = ψ g) → ∀ γ ∈ ratN F 2 1, ∀ (x : NA F) (h : GA F 2), ψ (unip (γ + x) * h) = ψ (unip x * h)`. Introduce and unpack `ψ hψ _ ⟨y, rfl⟩ x h`. Rewrite using `[hx, hx x]`.

Use `Eq.trans ?_ (hψ (aff 1 (y ⟨(0, 1), by decide⟩)) _)` and prove the remaining obligations. Rewrite using `[← mul_assoc, ← ct_aff_add]`. Both sides reduce to the same expression. Establish `key` using `hD (NA F) (ratN F 2 1) hco μ D hfin (fun x t => φ.1 (unip x * (g * TR.infGL F 2 (c t)))) (fun x t => (TR.lie F 2 X φ).1 (unip x * (g * TR.infGL F 2 (c t)))) (hc.comp hcont) (hc'.comp hcont) (fun γ hγ x => funext fun t => hper _ hl γ hγ x _) (fun γ hγ x => funext fun t => hper _ h …`. Establish `h1` using `TR.hasDerivAt_curve φ (unip x * (g * TR.infGL F 2 (c t))) c X h0 hder`.

Establish `h2 : HasDerivAt (fun s : ℝ => s - t) 1 t` using `(hasDerivAt_id t).sub_const t`. Establish `h3` using `HasDerivAt.scomp_of_eq t h1 h2 (sub_self t).symm`. Rewrite `h3` using `[one_smul]`. Use `h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)` and prove the remaining obligations. Simplify using `only [Function.comp_apply, mul_assoc, ← map_mul, ← hmul, add_sub_cancel])`.

Simplify `key` using `only [cterm, h0, map_one, mul_one]`.
-/
theorem UpperTheory.constant_term_automorphy :
    UpperTheory.V.Sd.Eis.SmCont → UpperTheory.V.Sd.Eis.PerMean → UpperTheory.V.Sd.Eis.PerDeriv → UpperTheory.V.Sd.Eis.BlockTop → UpperTheory.V.Sd.Eis.CtLie := by
  intro hS hM hD hB F _ _ _ _ _ μ _ D hF φ hl ho X
  have hl' : ∀ γ g, (TR.lie F 2 X φ).1 (ratGL F 2 γ * g) = (TR.lie F 2 X φ).1 g := by
    intro γ g
    have e : TR.chart φ.1 (ratGL F 2 γ * g) = TR.chart φ.1 g := by
      funext x
      simp only [TR.chart, mul_assoc, hl]
    simp only [TR.lie_apply, TR.lieD, e]
  have hc' : Continuous (TR.lie F 2 X φ).1 := hS F 2 _ (ct_level F 2 φ X ho)
  have hc : Continuous φ.1 := hS F 2 _ ho
  refine ⟨⟨hl', hc'⟩, fun c hcc hmul hder g => ?_⟩
  obtain ⟨i1, i2, i3, i4, hco, hu, hx⟩ := hB F
  have h0 : c 0 = 1 := by
    have := hmul 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have hfin := (hM (NA F) (ratN F 2 1) hco μ D hF).1
  have hcont : Continuous fun p : NA F × ℝ => (unip p.1 : GA F 2) * (g * TR.infGL F 2 (c p.2)) :=
    (hu.comp continuous_fst).mul (continuous_const.mul ((ct_cont_infGL F 2).comp (hcc.comp continuous_snd)))
  have hper : ∀ ψ : GA F 2 → ℂ, (∀ γ g, ψ (ratGL F 2 γ * g) = ψ g) → ∀ γ ∈ ratN F 2 1, ∀ (x : NA F) (h : GA F 2),
      ψ (unip (γ + x) * h) = ψ (unip x * h) := by
    rintro ψ hψ _ ⟨y, rfl⟩ x h
    rw [hx, hx x]
    refine Eq.trans ?_ (hψ (aff 1 (y ⟨(0, 1), by decide⟩)) _)
    rw [← mul_assoc, ← ct_aff_add]
    rfl
  have key := hD (NA F) (ratN F 2 1) hco μ D hfin
    (fun x t => φ.1 (unip x * (g * TR.infGL F 2 (c t))))
    (fun x t => (TR.lie F 2 X φ).1 (unip x * (g * TR.infGL F 2 (c t))))
    (hc.comp hcont) (hc'.comp hcont)
    (fun γ hγ x => funext fun t => hper _ hl γ hγ x _)
    (fun γ hγ x => funext fun t => hper _ hl' γ hγ x _)
    (fun x t => by
      have h1 := TR.hasDerivAt_curve φ (unip x * (g * TR.infGL F 2 (c t))) c X h0 hder
      have h2 : HasDerivAt (fun s : ℝ => s - t) 1 t := (hasDerivAt_id t).sub_const t
      have h3 := HasDerivAt.scomp_of_eq t h1 h2 (sub_self t).symm
      rw [one_smul] at h3
      refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
      simp only [Function.comp_apply, mul_assoc, ← map_mul, ← hmul, add_sub_cancel])
  simpa only [cterm, h0, map_one, mul_one] using key
