import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CcARatioZero
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.FmFormBAddLeft
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CoefOfEmb
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DataGenSubIrred

set_option autoImplicit false

noncomputable section

open Finset MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

/- English proof (translation)
Establish `hσ` using `rreg_isURepOn ε`. Establish `hD : IsDerivedOn ε (rreg ε) (smD ε (rreg ε)) (smE ε (rreg ε))` using `isDerivedOn_smE hσ`. Establish `hU` using `isInfUnitary_of_isDerivedOn hσ hD`. Establish `hV` using `datumV_isKIrrHW hP hv₀`. Establish `hV'` using `datumV_isKIrrHW hP' hv₀'`.

Establish `hc` using `datumV_casimir hP v₀`. Establish `hc'` using `datumV_casimir hP' v₀'`. Establish `hVK` using `datumV_kStable hP v₀`. Establish `hVK'` using `datumV_kStable hP' v₀'`. Establish `hinn : ∀ x : L2 ε, inner ℂ x x = ((‖x‖ ^ 2 : ℝ) : ℂ)` using `fun x => by`.

Rewrite using `[inner_self_eq_norm_sq_to_K]`. Use `norm_cast`. Establish `hPB` using `eigenProj_formB dual hσ hD hgap hV hc hVK hW (poleF dual lam s) hPG.1 hPz hP1 hP0`. Establish `hιinj : ∀ x ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀'), ∀ y ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀'), ι x = ι y → x = y` using `fun x hx y hy h => sub_eq_zero.1 (hι.2.1 _ (Submodule.sub_mem _ hx hy) (by rw [map_sub, h, sub_self]))`. Establish `hPι : ∀ x ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀'), P (ι x) = ι x` using `fun x hx => hP1 _ (hι.1 x hx) (hιe x hx)`.

Set `b : smD ε (rreg ε) →ₗ⋆[ℂ] smD ε (rreg ε) →ₗ[ℂ] ℂ` to `LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun x y => formB ε (ι x) (ι y)) (fun x x' y => by simp only [map_add, fm_formB_add_left]) (fun a x y => by simp only [map_smul, formB_smul_left, smul_eq_mul]) (fun x y y' => by simp only [map_add, formB_add_right]) (fun a x y => by …`. Establish `hb : ∀ x y, b x y = formB ε (ι x) (ι y)` using `fun _ _ => rfl`. Take `⟨c, hcb⟩` from `data_form_scalar hgap' hσ hD hV' hc' hVK' b (fun a a' x hx y hy => by`. Rewrite using `[hb, hb, hι.2.2.1 a a' x hx, hι.2.2.1 a' a y hy]`. Conclude with `fm_formB_tensF dual hU a a' _ _)`.

Use the proof step `(fun k hk x hx y hy x' hx' y' hy' hxx hyy => by`. Rewrite using `[hb, hb]`. Establish `h1` using `hι.2.2.2 k hk x hx x' hx' hxx`. Establish `h2` using `hι.2.2.2 k hk y hy y' hy' hyy`. Use `fm_formBH_kDiag dual hσ hk (fun c => ((ι x c : smD ε (rreg ε)) : L2 ε)) (fun c => ((ι y c : smD ε (rreg ε)) : L2 ε))` as an intermediate fact.

Rewrite `this` using `[← h1, ← h2]`. Conclude with `this)`. Take `⟨w, hwV, hw0, -⟩` from `hV'.2.2.2`. Establish `hwM : w ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀')` using `rorth_le_genSub hwV`. Establish `hwH : ((w : smD ε (rreg ε)) : L2 ε) ≠ 0` using `fun h => hw0 (Subtype.ext h)`.

Establish `hcre : c = (c.re : ℂ)`. Establish `h1` using `hcb w hwM w hwM`. Establish `h2 : starRingEnd ℂ (b w w) = b w w` using `by rw [hb]; exact formB_conj _ _`. Rewrite `h2` using `[h1, map_mul, inner_conj_symm]`. Establish `hww : inner ℂ ((w : smD ε (rreg ε)) : L2 ε) ((w : smD ε (rreg ε)) : L2 ε) ≠ 0` using `inner_self_ne_zero.2 hwH`.

Conclude with `(Complex.conj_eq_iff_re.1 (mul_right_cancel₀ hww h2)).symm`. Establish `hform : ∀ x ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀'), ∀ y ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀'), formB ε (ι x) (ι y) = (c.re : ℂ) * inner ℂ ((x : smD ε (rreg ε)) : L2 ε) ((y : smD ε (rreg ε)) : L2 ε)`. Introduce `x hx y hy`. Rewrite using `[← hb, hcb x hx y hy, ← hcre]`. Establish `hqex : ∀ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)), ∃ x ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀'), P f = ι x` using `fun f hf => hιs _ (hPG.1 f hf) (hPz f hf)`.

Set `q : (Fin n → smD ε (rreg ε)) → smD ε (rreg ε)` to `fun f => if h : ∃ x ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀'), P f = ι x then h.choose else 0`. Establish `hq : ∀ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)), q f ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀') ∧ P f = ι (q f)`. Introduce `f hf`. Establish `h` using `hqex f hf`. Establish `e : q f = h.choose` using `dif_pos h`.

Rewrite using `[e]`. Conclude with `h.choose_spec`. Use `⟨c.re, q, ?_, hform, hq, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `h0`. Establish `hιw : ι w ≠ 0` using `fun h => hw0 (hι.2.1 w hwM h)`.

Take `⟨c0, hc0⟩` from `Function.ne_iff.1 hιw`. Set `G : Fin n → smD ε (rreg ε)` to `fun c => (if ε c then (1 : ℂ) else -1) • ι w c`. Establish `hG : G ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀))` using `tset_mem.2 fun c => Submodule.smul_mem _ _ (tset_mem.1 (hι.1 w hwM) c)`. Establish `e1 : formB ε (ι w) G = ((∑ c, ‖((ι w c : smD ε (rreg ε)) : L2 ε)‖ ^ 2 : ℝ) : ℂ)`. Simplify using `only [formB, G, Submodule.coe_smul, inner_smul_right, Complex.ofReal_sum]`.

Use `sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[hinn]`. Apply the tactic sequence `split_ifs <;> ring`. Establish `hpos : 0 < ∑ c, ‖((ι w c : smD ε (rreg ε)) : L2 ε)‖ ^ 2`. Use `Finset.sum_pos' (fun c _ => sq_nonneg _) ⟨c0, mem_univ _, ?_⟩` and prove the remaining obligations.

Establish `: ((ι w c0 : smD ε (rreg ε)) : L2 ε) ≠ 0` using `fun h => hc0 (Subtype.ext h)`. Conclude with `pow_pos (norm_pos_iff.2 this) 2`. Take `⟨y, hy, hPy⟩` from `hqex G hG`. Establish `e2 : formB ε (ι w) G = 0`. Rewrite using `[← hPι w hwM, hPB _ (hι.1 w hwM) G hG, hPy, hform w hwM y hy, h0]`.

Simplify using the standard rewrite rules. Rewrite `e2` using `[e1]`. Conclude with `absurd (Complex.ofReal_eq_zero.1 e2) hpos.ne'`. Introduce `a b' f hf`. Establish `hf'` using `tensSub_stable dual a b' f hf`.

Take `⟨h1, h2⟩` from `hq _ hf'`. Take `⟨h3, h4⟩` from `hq f hf`. Use `hιinj _ h1 _ (tset_genSub_E _ _ a b' h3) ?_` and prove the remaining obligations. Rewrite using `[← h2, hPG.2.1 a b' f hf, h4, hι.2.2.1 a b' _ h3]`. Introduce `f hf`.

Take `⟨h1, h2⟩` from `hq f hf`. Rewrite using `[h2, hform _ h1 _ h1, hinn]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Introduce `f hf f' hf' g hg`.

Take `⟨hq1, hq2⟩` from `hq f hf`. Take `⟨hq1', hq2'⟩` from `hq f' hf'`. Set `F : Fin n → smD ε (rreg ε)` to `fun c => (if ε c then (1 : ℂ) else -1) • f' c`. Establish `hz : ∀ y ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀'), inner ℂ ((c.re : ℂ) • q f') y = ∑ c, inner ℂ (F c) (ι y c)`. Introduce `y hy`.

Establish `e1 : ∑ c, inner ℂ (F c) (ι y c) = formB ε f' (ι y)`. Simplify using `only [formB, F, Submodule.coe_inner, inner_smul_left, fm_sgn_star]`. Rewrite using `[e1, ← hPι y hy, ← hPB f' hf' (ι y) (hι.1 y hy), hq2', hform _ hq1' _ hy, Submodule.coe_inner, Submodule.coe_smul, inner_smul_left, Complex.conj_ofReal]`. Establish `key` using `coefE_all dual hσ hD hV.1 hV.2.1 hc hV'.1 hV'.2.1 hc' hι.1 hι.2.2.1 F ((c.re : ℂ) • q f') hz g hg (q f) hq1`. Establish `hTG : ∀ w : Fin n → L2 ε, tensGrp dual (rreg ε) g w = coefTG dual (rreg ε) g w`.

Apply the tactic sequence `intro w; funext c; cases dual <;> rfl`. Rewrite using `[hq2, hTG]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[key, Submodule.coe_smul, inner_smul_left, Complex.conj_ofReal]`.
-/
theorem form_cc (dual : Bool) {ε : Fin n → Bool} {lam lam' : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
    {T' : S7.KType ε (lowK ε lam')} {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)}
    {Ψ' : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V)} {v₀ : T.V} {v₀' : T'.V}
    (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
    (hgap' : StdGap ε lam') (hP' : IsPsiFor ε lam' T' Ψ') (hv₀' : v₀' ≠ 0)
    (hW : ∀ v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), ∀ w ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀),
      MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
        inner ℂ ((w : smD ε (rreg ε)) : L2 ε) (rreg ε (Formalism.MainNotions.S.umat g) ((v : smD ε (rreg ε)) : L2 ε))) 2 (Formalism.REAL.muG ε))
    (s : Fin n) {ι : smD ε (rreg ε) →ₗ[ℂ] (Fin n → smD ε (rreg ε))}
    (hι : IsGKEmb dual ε (rreg ε) (smE ε (rreg ε)) (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀))
      (genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀')) ι)
    (hιe : ∀ x ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀'), eeF dual (smE ε (rreg ε)) (ι x) = poleF dual lam s • ι x)
    (hιs : ∀ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)),
      eeF dual (smE ε (rreg ε)) f = poleF dual lam s • f → ∃ x ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀'), f = ι x)
    {P : Module.End ℂ (Fin n → smD ε (rreg ε))}
    (hPG : IsGKEndo dual ε (rreg ε) (smE ε (rreg ε)) (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)) P)
    (hPz : ∀ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)),
      eeF dual (smE ε (rreg ε)) (P f) = poleF dual lam s • P f)
    (hP1 : ∀ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)),
      eeF dual (smE ε (rreg ε)) f = poleF dual lam s • f → P f = f)
    (hP0 : ∀ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)), ∀ z' : ℂ, z' ≠ poleF dual lam s →
      eeF dual (smE ε (rreg ε)) f = z' • f → P f = 0) :
    ∃ (ka : ℝ) (q : (Fin n → smD ε (rreg ε)) → smD ε (rreg ε)), ka ≠ 0 ∧
      (∀ x ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀'), ∀ y ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀'),
        formB ε (ι x) (ι y) = ka * inner ℂ ((x : smD ε (rreg ε)) : L2 ε) ((y : smD ε (rreg ε)) : L2 ε)) ∧
      (∀ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)),
        q f ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀') ∧ P f = ι (q f)) ∧
      (∀ a b, ∀ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)),
        q (tensF dual (smE ε (rreg ε)) a b f) = smE ε (rreg ε) a b (q f)) ∧
      (∀ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)),
        ((ka * ‖((q f : smD ε (rreg ε)) : L2 ε)‖ ^ 2 : ℝ) : ℂ) = formB ε (P f) (P f)) ∧
      ∀ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)), ∀ f' ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)),
        ∀ g ∈ UJset ε,
          ∑ c, (if ε c then (1 : ℂ) else -1) * inner ℂ ((f' c : smD ε (rreg ε)) : L2 ε)
              (tensGrp dual (rreg ε) g (fun d => ((P f d : smD ε (rreg ε)) : L2 ε)) c) =
            ka * inner ℂ ((q f' : smD ε (rreg ε)) : L2 ε) (rreg ε g ((q f : smD ε (rreg ε)) : L2 ε)) := by

  classical
  have hσ := rreg_isURepOn ε
  have hD : IsDerivedOn ε (rreg ε) (smD ε (rreg ε)) (smE ε (rreg ε)) := isDerivedOn_smE hσ
  have hU := isInfUnitary_of_isDerivedOn hσ hD
  have hV := datumV_isKIrrHW hP hv₀
  have hV' := datumV_isKIrrHW hP' hv₀'
  have hc := datumV_casimir hP v₀
  have hc' := datumV_casimir hP' v₀'
  have hVK := datumV_kStable hP v₀
  have hVK' := datumV_kStable hP' v₀'
  have hinn : ∀ x : L2 ε, inner ℂ x x = ((‖x‖ ^ 2 : ℝ) : ℂ) := fun x => by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  have hPB := eigenProj_formB dual hσ hD hgap hV hc hVK hW (poleF dual lam s) hPG.1 hPz hP1 hP0
  have hιinj : ∀ x ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀'), ∀ y ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀'),
      ι x = ι y → x = y := fun x hx y hy h =>
    sub_eq_zero.1 (hι.2.1 _ (Submodule.sub_mem _ hx hy) (by rw [map_sub, h, sub_self]))
  have hPι : ∀ x ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀'), P (ι x) = ι x := fun x hx => hP1 _ (hι.1 x hx) (hιe x hx)

  let b : smD ε (rreg ε) →ₗ⋆[ℂ] smD ε (rreg ε) →ₗ[ℂ] ℂ :=
    LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun x y => formB ε (ι x) (ι y))
      (fun x x' y => by simp only [map_add, fm_formB_add_left])
      (fun a x y => by simp only [map_smul, formB_smul_left, smul_eq_mul])
      (fun x y y' => by simp only [map_add, formB_add_right])
      (fun a x y => by simp only [map_smul, formB_smul_right, RingHom.id_apply, smul_eq_mul])
  have hb : ∀ x y, b x y = formB ε (ι x) (ι y) := fun _ _ => rfl
  obtain ⟨c, hcb⟩ := data_form_scalar hgap' hσ hD hV' hc' hVK' b
    (fun a a' x hx y hy => by
      rw [hb, hb, hι.2.2.1 a a' x hx, hι.2.2.1 a' a y hy]
      exact fm_formB_tensF dual hU a a' _ _)
    (fun k hk x hx y hy x' hx' y' hy' hxx hyy => by
      rw [hb, hb]
      have h1 := hι.2.2.2 k hk x hx x' hx' hxx
      have h2 := hι.2.2.2 k hk y hy y' hy' hyy
      have := fm_formBH_kDiag dual hσ hk (fun c => ((ι x c : smD ε (rreg ε)) : L2 ε))
        (fun c => ((ι y c : smD ε (rreg ε)) : L2 ε))
      rw [← h1, ← h2] at this
      exact this)
  obtain ⟨w, hwV, hw0, -⟩ := hV'.2.2.2
  have hwM : w ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀') := rorth_le_genSub hwV
  have hwH : ((w : smD ε (rreg ε)) : L2 ε) ≠ 0 := fun h => hw0 (Subtype.ext h)
  have hcre : c = (c.re : ℂ) := by
    have h1 := hcb w hwM w hwM
    have h2 : starRingEnd ℂ (b w w) = b w w := by rw [hb]; exact formB_conj _ _
    rw [h1, map_mul, inner_conj_symm] at h2
    have hww : inner ℂ ((w : smD ε (rreg ε)) : L2 ε) ((w : smD ε (rreg ε)) : L2 ε) ≠ 0 := inner_self_ne_zero.2 hwH
    exact (Complex.conj_eq_iff_re.1 (mul_right_cancel₀ hww h2)).symm
  have hform : ∀ x ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀'), ∀ y ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀'),
      formB ε (ι x) (ι y) = (c.re : ℂ) * inner ℂ ((x : smD ε (rreg ε)) : L2 ε) ((y : smD ε (rreg ε)) : L2 ε) := by
    intro x hx y hy
    rw [← hb, hcb x hx y hy, ← hcre]

  have hqex : ∀ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)),
      ∃ x ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀'), P f = ι x := fun f hf => hιs _ (hPG.1 f hf) (hPz f hf)
  let q : (Fin n → smD ε (rreg ε)) → smD ε (rreg ε) := fun f =>
    if h : ∃ x ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀'), P f = ι x then h.choose else 0
  have hq : ∀ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)),
      q f ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀') ∧ P f = ι (q f) := by
    intro f hf
    have h := hqex f hf
    have e : q f = h.choose := dif_pos h
    rw [e]
    exact h.choose_spec
  refine ⟨c.re, q, ?_, hform, hq, ?_, ?_, ?_⟩
  ·
    intro h0
    have hιw : ι w ≠ 0 := fun h => hw0 (hι.2.1 w hwM h)
    obtain ⟨c0, hc0⟩ := Function.ne_iff.1 hιw
    let G : Fin n → smD ε (rreg ε) := fun c => (if ε c then (1 : ℂ) else -1) • ι w c
    have hG : G ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)) :=
      tset_mem.2 fun c => Submodule.smul_mem _ _ (tset_mem.1 (hι.1 w hwM) c)
    have e1 : formB ε (ι w) G = ((∑ c, ‖((ι w c : smD ε (rreg ε)) : L2 ε)‖ ^ 2 : ℝ) : ℂ) := by
      simp only [formB, G, Submodule.coe_smul, inner_smul_right, Complex.ofReal_sum]
      refine sum_congr rfl fun c _ => ?_
      rw [hinn]
      split_ifs <;> ring
    have hpos : 0 < ∑ c, ‖((ι w c : smD ε (rreg ε)) : L2 ε)‖ ^ 2 := by
      refine Finset.sum_pos' (fun c _ => sq_nonneg _) ⟨c0, mem_univ _, ?_⟩
      have : ((ι w c0 : smD ε (rreg ε)) : L2 ε) ≠ 0 := fun h => hc0 (Subtype.ext h)
      exact pow_pos (norm_pos_iff.2 this) 2
    obtain ⟨y, hy, hPy⟩ := hqex G hG
    have e2 : formB ε (ι w) G = 0 := by
      rw [← hPι w hwM, hPB _ (hι.1 w hwM) G hG, hPy, hform w hwM y hy, h0]
      simp
    rw [e1] at e2
    exact absurd (Complex.ofReal_eq_zero.1 e2) hpos.ne'
  ·
    intro a b' f hf
    have hf' := tensSub_stable dual a b' f hf
    obtain ⟨h1, h2⟩ := hq _ hf'
    obtain ⟨h3, h4⟩ := hq f hf
    refine hιinj _ h1 _ (tset_genSub_E _ _ a b' h3) ?_
    rw [← h2, hPG.2.1 a b' f hf, h4, hι.2.2.1 a b' _ h3]
  ·
    intro f hf
    obtain ⟨h1, h2⟩ := hq f hf
    rw [h2, hform _ h1 _ h1, hinn]
    push_cast
    ring
  ·
    intro f hf f' hf' g hg
    obtain ⟨hq1, hq2⟩ := hq f hf
    obtain ⟨hq1', hq2'⟩ := hq f' hf'
    let F : Fin n → smD ε (rreg ε) := fun c => (if ε c then (1 : ℂ) else -1) • f' c
    have hz : ∀ y ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀'),
        inner ℂ ((c.re : ℂ) • q f') y = ∑ c, inner ℂ (F c) (ι y c) := by
      intro y hy
      have e1 : ∑ c, inner ℂ (F c) (ι y c) = formB ε f' (ι y) := by
        simp only [formB, F, Submodule.coe_inner, inner_smul_left, fm_sgn_star]
      rw [e1, ← hPι y hy, ← hPB f' hf' (ι y) (hι.1 y hy), hq2', hform _ hq1' _ hy,
        Submodule.coe_inner, Submodule.coe_smul, inner_smul_left, Complex.conj_ofReal]
    have key := coefE_all dual hσ hD hV.1 hV.2.1 hc hV'.1 hV'.2.1 hc' hι.1 hι.2.2.1 F ((c.re : ℂ) • q f') hz g hg
      (q f) hq1
    have hTG : ∀ w : Fin n → L2 ε, tensGrp dual (rreg ε) g w = coefTG dual (rreg ε) g w := by
      intro w; funext c; cases dual <;> rfl
    rw [hq2, hTG]
    calc ∑ c, (if ε c then (1 : ℂ) else -1) * inner ℂ ((f' c : smD ε (rreg ε)) : L2 ε)
          (coefTG dual (rreg ε) g (fun d => ((ι (q f) d : smD ε (rreg ε)) : L2 ε)) c)
        = ∑ c, inner ℂ ((F c : smD ε (rreg ε)) : L2 ε)
          (coefTG dual (rreg ε) g (fun d => ((ι (q f) d : smD ε (rreg ε)) : L2 ε)) c) :=
          sum_congr rfl fun c _ => by simp only [F, Submodule.coe_smul, inner_smul_left, fm_sgn_star]
      _ = _ := by
          rw [key, Submodule.coe_smul, inner_smul_left, Complex.conj_ofReal]

end ReciprocityTheory.ChartRestriction.DS
