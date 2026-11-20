import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.LandauLocalOf

open Complex Filter Topology

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

/- English proof (translation)
Establish `hne : ∀ ρ' ∈ Zb.erase ρ, (ρ - ρ') ^ m ρ' ≠ 0` using `fun ρ' h' => pow_ne_zero _ (sub_ne_zero.2 fun e => (Finset.ne_of_mem_erase h') e.symm)`. Establish `hgD : DifferentiableOn ℂ (fun z => (∏ ρ' ∈ Zb.erase ρ, (z - ρ') ^ m ρ') * h z) S` using `(DifferentiableOn.fun_finset_prod fun ρ' _ => (differentiableOn_id.sub_const ρ').pow _).mul hh`. Establish `hgA` using `hgD.analyticAt (hS.mem_nhds hρS)`. Establish `hg0 : (∏ ρ' ∈ Zb.erase ρ, (ρ - ρ') ^ m ρ') * h ρ ≠ 0` using `mul_ne_zero (Finset.prod_ne_zero_iff.2 hne) hhρ`. Establish `heq : ∀ z ∈ S, f z = (z - ρ) ^ m ρ * ((∏ ρ' ∈ Zb.erase ρ, (z - ρ') ^ m ρ') * h z)`.

Introduce `z hz`. Rewrite using `[hfac z hz, ← Finset.mul_prod_erase Zb (fun ρ' => (z - ρ') ^ m ρ') hρ, mul_assoc]`. Establish `hfA : AnalyticAt ℂ f ρ` using `(((analyticAt_id.sub analyticAt_const).pow (m ρ)).mul hgA).congr (Filter.eventually_of_mem (hS.mem_nhds hρS) fun z hz => (heq z hz).symm)`. Establish `hord : analyticOrderAt f ρ = (m ρ : ℕ∞)`. Rewrite using `[hfA.analyticOrderAt_eq_natCast]`.

Conclude with `⟨_, hgA, hg0, Filter.eventually_of_mem (hS.mem_nhds hρS) fun z hz => by rw [heq z hz, smul_eq_mul]⟩`. Simplify using `[analyticOrderNatAt, hord]`.
-/
theorem exr_ord (f h : ℂ → ℂ) (Zb : Finset ℂ) (m : ℂ → ℕ) (S : Set ℂ) (hS : IsOpen S)
    (hh : DifferentiableOn ℂ h S) (hfac : ∀ z ∈ S, f z = (∏ ρ ∈ Zb, (z - ρ) ^ m ρ) * h z)
    (ρ : ℂ) (hρ : ρ ∈ Zb) (hρS : ρ ∈ S) (hhρ : h ρ ≠ 0) : analyticOrderNatAt f ρ = m ρ := by
  classical
  have hne : ∀ ρ' ∈ Zb.erase ρ, (ρ - ρ') ^ m ρ' ≠ 0 := fun ρ' h' =>
    pow_ne_zero _ (sub_ne_zero.2 fun e => (Finset.ne_of_mem_erase h') e.symm)
  have hgD : DifferentiableOn ℂ (fun z => (∏ ρ' ∈ Zb.erase ρ, (z - ρ') ^ m ρ') * h z) S :=
    (DifferentiableOn.fun_finset_prod fun ρ' _ => (differentiableOn_id.sub_const ρ').pow _).mul hh
  have hgA := hgD.analyticAt (hS.mem_nhds hρS)
  have hg0 : (∏ ρ' ∈ Zb.erase ρ, (ρ - ρ') ^ m ρ') * h ρ ≠ 0 :=
    mul_ne_zero (Finset.prod_ne_zero_iff.2 hne) hhρ
  have heq : ∀ z ∈ S, f z = (z - ρ) ^ m ρ * ((∏ ρ' ∈ Zb.erase ρ, (z - ρ') ^ m ρ') * h z) := by
    intro z hz
    rw [hfac z hz, ← Finset.mul_prod_erase Zb (fun ρ' => (z - ρ') ^ m ρ') hρ, mul_assoc]
  have hfA : AnalyticAt ℂ f ρ :=
    (((analyticAt_id.sub analyticAt_const).pow (m ρ)).mul hgA).congr
      (Filter.eventually_of_mem (hS.mem_nhds hρS) fun z hz => (heq z hz).symm)
  have hord : analyticOrderAt f ρ = (m ρ : ℕ∞) := by
    rw [hfA.analyticOrderAt_eq_natCast]
    exact ⟨_, hgA, hg0, Filter.eventually_of_mem (hS.mem_nhds hρS) fun z hz => by rw [heq z hz, smul_eq_mul]⟩
  simp [analyticOrderNatAt, hord]

/- English proof (translation)
Establish `hPd : ∀ s : Finset ℂ, w ∉ s → HasDerivAt (fun z => ∏ ρ ∈ s, (z - ρ) ^ m ρ) ((∏ ρ ∈ s, (w - ρ) ^ m ρ) * ∑ ρ ∈ s, (m ρ : ℂ) / (w - ρ)) w`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => intro _`. Simplify using `using hasDerivAt_const w (1 : ℂ)`.

Consider the case `insert a s ha ih`. Introduce `hw`. Establish `hwa : w - a ≠ 0` using `sub_ne_zero.2 fun e => hw (e ▸ Finset.mem_insert_self a s)`. Establish `ih'` using `ih fun e => hw (Finset.mem_insert_of_mem e)`. Establish `hm` using `(((hasDerivAt_id' w).sub_const a).pow (m a)).mul ih'`.

Simplify using `only [Finset.prod_insert ha, Finset.sum_insert ha]`. Use `hm.congr_deriv ?_` and prove the remaining obligations. Simplify using `only [Pi.pow_apply]`. Break down `Nat.eq_zero_or_pos (m a) with h0 | hpos` into its components or cases. Rewrite using `[h0]`.

Simplify using the standard rewrite rules. Take `⟨k, hk⟩ : ∃ k, m a = k + 1` from `⟨m a - 1, by omega⟩`. Rewrite using `[hk, Nat.add_sub_cancel]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Establish `hPne : (∏ ρ ∈ Zb, (w - ρ) ^ m ρ) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun ρ hρ => pow_ne_zero _ (sub_ne_zero.2 fun e => hwZ (e ▸ hρ))`. Establish `hhd : HasDerivAt h (deriv h w) w` using `(hh.differentiableAt (hS.mem_nhds hwS)).hasDerivAt`. Establish `hprod` using `(hPd Zb hwZ).mul hhd`. Establish `hev : f =ᶠ[𝓝 w] fun z => (∏ ρ ∈ Zb, (z - ρ) ^ m ρ) * h z` using `Filter.eventually_of_mem (hS.mem_nhds hwS) hfac`.

Establish `hd : deriv f w = _` using `hev.deriv_eq.trans hprod.deriv`. Rewrite using `[hd, hfac w hwS]`. Clear the denominators using the available nonvanishing facts.
-/
theorem exr_logDeriv (f h : ℂ → ℂ) (Zb : Finset ℂ) (m : ℂ → ℕ) (S : Set ℂ) (hS : IsOpen S)
    (hh : DifferentiableOn ℂ h S) (hfac : ∀ z ∈ S, f z = (∏ ρ ∈ Zb, (z - ρ) ^ m ρ) * h z)
    (w : ℂ) (hwS : w ∈ S) (hwZ : w ∉ Zb) (hhw : h w ≠ 0) :
    deriv f w / f w = (∑ ρ ∈ Zb, (m ρ : ℂ) / (w - ρ)) + deriv h w / h w := by
  classical
  have hPd : ∀ s : Finset ℂ, w ∉ s → HasDerivAt (fun z => ∏ ρ ∈ s, (z - ρ) ^ m ρ)
      ((∏ ρ ∈ s, (w - ρ) ^ m ρ) * ∑ ρ ∈ s, (m ρ : ℂ) / (w - ρ)) w := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; simpa using hasDerivAt_const w (1 : ℂ)
    | insert a s ha ih =>
      intro hw
      have hwa : w - a ≠ 0 := sub_ne_zero.2 fun e => hw (e ▸ Finset.mem_insert_self a s)
      have ih' := ih fun e => hw (Finset.mem_insert_of_mem e)
      have hm := (((hasDerivAt_id' w).sub_const a).pow (m a)).mul ih'
      simp only [Finset.prod_insert ha, Finset.sum_insert ha]
      refine hm.congr_deriv ?_
      simp only [Pi.pow_apply]
      rcases Nat.eq_zero_or_pos (m a) with h0 | hpos
      · rw [h0]; simp
      · obtain ⟨k, hk⟩ : ∃ k, m a = k + 1 := ⟨m a - 1, by omega⟩
        rw [hk, Nat.add_sub_cancel]
        push_cast
        field_simp
        ring
  have hPne : (∏ ρ ∈ Zb, (w - ρ) ^ m ρ) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun ρ hρ => pow_ne_zero _ (sub_ne_zero.2 fun e => hwZ (e ▸ hρ))
  have hhd : HasDerivAt h (deriv h w) w := (hh.differentiableAt (hS.mem_nhds hwS)).hasDerivAt
  have hprod := (hPd Zb hwZ).mul hhd
  have hev : f =ᶠ[𝓝 w] fun z => (∏ ρ ∈ Zb, (z - ρ) ^ m ρ) * h z :=
    Filter.eventually_of_mem (hS.mem_nhds hwS) hfac
  have hd : deriv f w = _ := hev.deriv_eq.trans hprod.deriv
  rw [hd, hfac w hwS]
  field_simp

/- English proof (translation)
Establish `hρ1' : 1 - ρ ≠ 0` using `fun e => hρ1 (by linear_combination -e)`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exr_term (m e c w ρ y : ℂ) (hw : w ≠ 0) (hw1 : w - 1 ≠ 0) (hwρ : w - ρ ≠ 0)
    (hρ : ρ ≠ 0) (hρ1 : ρ - 1 ≠ 0) :
    -(m / (w - ρ)) * (e / w / (w - 1)) + m / (1 - ρ) * y / (w - 1) - (-m * (c / (ρ * (ρ - 1)))) / (w - ρ)
      + m / (ρ - 1) * ((e / w - c / ρ) / (w - ρ) - (e / w - y) / (w - 1)) = 0 := by
  have hρ1' : 1 - ρ ≠ 0 := fun e => hρ1 (by linear_combination -e)
  field_simp
  ring

end Formalism.HermitianLattices.Ext.PrimesInProgressions
