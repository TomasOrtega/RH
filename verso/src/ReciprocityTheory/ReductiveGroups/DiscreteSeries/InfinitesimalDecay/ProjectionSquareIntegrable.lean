import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.FormBSelfLe
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.FormCc
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.ConsumerB

set_option autoImplicit false

noncomputable section

open Finset MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.DecInf

variable {n : ℕ}

/- English proof (translation)
Introduce `s t h`. Establish `h' : lam s + (1 - (n : ℝ)) / 2 = lam t + (1 - (n : ℝ)) / 2`. Use `h` as an intermediate fact. Simplify using `only [poleF, cond_false, poleV] at this`. Conclude with `this` after adjusting the coercions.

Conclude with `hlam.injective (by linarith)`.
-/
theorem poles_injective {lam : Fin n → ℝ} (hlam : StrictAnti lam) : Function.Injective (poleF false lam) := by
  intro s t h
  have h' : lam s + (1 - (n : ℝ)) / 2 = lam t + (1 - (n : ℝ)) / 2 := by
    have := h
    simp only [poleF, cond_false, poleV] at this
    exact_mod_cast this
  exact hlam.injective (by linarith)

/- English proof (translation)
Establish `hσ` using `rreg_isURepOn ε`. Establish `hD` using `isDerivedOn_smE hσ`. Establish `hV` using `datumV_isKIrrHW hP hv₀`. Establish `hc` using `datumV_casimir hP v₀`. Establish `hVK` using `datumV_kStable hP v₀`.

Establish `hsm : ∀ v : smD ε (rreg ε), IsSmoothVecU ε (rreg ε) (v : L2 ε)` using `fun v => (mem_smD_iff ε (rreg ε) (v : L2 ε)).1 v.2`. Take `⟨B, hdec, -⟩` from `ee_decomp false hσ hD hgap hV hc hVK hW`. Take `⟨hpole, -⟩` from `pole_match false hσ hD hsm hgap hV hc hVK hW hG`. Establish `hinj : Set.InjOn (poleF false lam) (Finset.univ : Finset (Fin n))` using `(poles_injective hgap.1).injOn`. Use `set a := poleF false lam with ha`.

Use `set EE := eeF false (smE ε (rreg ε)) with hEE`. Use `set S := tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)) with hS`. Set `P : Fin n → Module.End ℂ (Fin n → smD ε (rreg ε))` to `fun s => Polynomial.aeval EE (Lagrange.basis Finset.univ a s)`. Establish `hPe : ∀ s (e : Fin n → smD ε (rreg ε)) (z : ℂ), EE e = z • e → P s e = (Lagrange.basis Finset.univ a s).eval z • e` using `fun s e z he => dc_aeval_eigen he _`. Establish `hLval : ∀ s t, (Lagrange.basis Finset.univ a s).eval (a t) = if s = t then 1 else 0`.

Introduce `s t`. Use `split_ifs with hst`. Substitute `hst` using the available equality. Conclude with `Lagrange.eval_basis_self hinj (Finset.mem_univ _)`. Conclude with `Lagrange.eval_basis_of_ne hst (Finset.mem_univ _)`.

Establish `hterm : ∀ s, ∀ e ∈ S, ∀ z : ℂ, EE e = z • e → EE (P s e) = a s • P s e`. Introduce `s e he z hz`. Distinguish the cases in `h0 : e = 0`. Substitute `h0` using the available equality. Simplify using the standard rewrite rules.

Take `⟨t, rfl⟩` from `hpole z e he h0 hz`. Rewrite using `[hPe s e _ hz, hLval s t]`. Use `split_ifs with hst`. Substitute `hst` using the available equality. Rewrite using `[one_smul, hz]`.

Simplify using the standard rewrite rules. Establish `hsum1 : ∀ e ∈ S, ∀ z : ℂ, EE e = z • e → ∑ s, P s e = e`. Introduce `e he z hz`. Distinguish the cases in `h0 : e = 0`. Substitute `h0` using the available equality.

Simplify using the standard rewrite rules. Take `⟨t, rfl⟩` from `hpole z e he h0 hz`. Establish `hne : (Finset.univ : Finset (Fin n)).Nonempty` using `⟨t, Finset.mem_univ _⟩`. Establish `h1 : ∑ s, (Lagrange.basis Finset.univ a s).eval (a t) = 1`. Rewrite using `[← Polynomial.eval_finsetSum, Lagrange.sum_basis hinj hne, Polynomial.eval_one]`.

Combine the equalities or inequalities in the displayed calculation. Use `⟨P, fun s => dc_isGKEndo_aeval (isGKEndo_eeF hσ hD _ false) _, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `s f hf`. Take `⟨fb, hfb, hfe⟩` from `hdec f hf`. Rewrite using `[hfe, map_sum, map_sum, Finset.smul_sum]`.

Conclude with `Finset.sum_congr rfl fun b _ => hterm s _ (hfb b).1 _ (hfb b).2`. Introduce `s f _ hf`. Rewrite using `[hPe s f _ hf, Lagrange.eval_basis_self hinj (Finset.mem_univ _), one_smul]`. Introduce `s f hf z' hz' hfz`. Distinguish the cases in `h0 : f = 0`.

Substitute `h0` using the available equality. Simplify using the standard rewrite rules. Take `⟨t, rfl⟩` from `hpole z' f hf h0 hfz`. Establish `hts : s ≠ t` using `fun h => hz' (by rw [h])`. Rewrite using `[hPe s f _ hfz, hLval s t, if_neg hts, zero_smul]`.

Introduce `f hf`. Take `⟨fb, hfb, hfe⟩` from `hdec f hf`. Use `conv_lhs => rw [hfe]`. Rewrite using `[hfe]`. Simplify using `only [map_sum]`.

Rewrite using `[Finset.sum_comm]`. Conclude with `(Finset.sum_congr rfl fun b _ => hsum1 _ (hfb b).1 _ (hfb b).2).symm`. Introduce `s j`. Take `⟨C, hC⟩` from `NT_poly_le false (smE ε (rreg ε)) (Lagrange.basis Finset.univ a s) j`. Establish `hdeg : (Lagrange.basis Finset.univ a s).natDegree = n - 1`.

Rewrite using `[Lagrange.natDegree_basis hinj (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]`. Use `⟨C, fun f _ => ?_⟩` and prove the remaining obligations. Use `hC f` as an intermediate fact. Rewrite `this` using `[hdeg]`. Conclude with `this`.
-/
theorem projection_square_integrable {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : S7.IsHCParam lam) {T : S7.KType ε (lowK ε lam)}
    {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}
    (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
    (hW : ∀ v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), ∀ w ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀),
      MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
        inner ℂ ((w : smD ε (rreg ε)) : L2 ε) (rreg ε (Formalism.MainNotions.S.umat g) ((v : smD ε (rreg ε)) : L2 ε))) 2 (Formalism.REAL.muG ε))
    (hG : HasGelfandChar (smE ε (rreg ε)) lam (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀))) :
    ∃ P : Fin n → Module.End ℂ (Fin n → smD ε (rreg ε)),
      (∀ s, IsGKEndo false ε (rreg ε) (smE ε (rreg ε)) (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)) (P s)) ∧
      (∀ s, ∀ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)),
        eeF false (smE ε (rreg ε)) (P s f) = poleF false lam s • P s f) ∧
      (∀ s, ∀ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)),
        eeF false (smE ε (rreg ε)) f = poleF false lam s • f → P s f = f) ∧
      (∀ s, ∀ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)), ∀ z' : ℂ, z' ≠ poleF false lam s →
        eeF false (smE ε (rreg ε)) f = z' • f → P s f = 0) ∧
      (∀ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)), f = ∑ s, P s f) ∧
      ∀ s (j : ℕ), ∃ C : ℝ, ∀ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)),
        NT (smE ε (rreg ε)) j (P s f) ≤ C * NT (smE ε (rreg ε)) (j + (n - 1)) f := by
  classical
  have hσ := rreg_isURepOn ε
  have hD := isDerivedOn_smE hσ
  have hV := datumV_isKIrrHW hP hv₀
  have hc := datumV_casimir hP v₀
  have hVK := datumV_kStable hP v₀
  have hsm : ∀ v : smD ε (rreg ε), IsSmoothVecU ε (rreg ε) (v : L2 ε) := fun v =>
    (mem_smD_iff ε (rreg ε) (v : L2 ε)).1 v.2
  obtain ⟨B, hdec, -⟩ := ee_decomp false hσ hD hgap hV hc hVK hW
  obtain ⟨hpole, -⟩ := pole_match false hσ hD hsm hgap hV hc hVK hW hG
  have hinj : Set.InjOn (poleF false lam) (Finset.univ : Finset (Fin n)) :=
    (poles_injective hgap.1).injOn
  set a := poleF false lam with ha
  set EE := eeF false (smE ε (rreg ε)) with hEE
  set S := tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)) with hS
  let P : Fin n → Module.End ℂ (Fin n → smD ε (rreg ε)) := fun s =>
    Polynomial.aeval EE (Lagrange.basis Finset.univ a s)
  have hPe : ∀ s (e : Fin n → smD ε (rreg ε)) (z : ℂ), EE e = z • e →
      P s e = (Lagrange.basis Finset.univ a s).eval z • e := fun s e z he => dc_aeval_eigen he _
  have hLval : ∀ s t, (Lagrange.basis Finset.univ a s).eval (a t) = if s = t then 1 else 0 := by
    intro s t
    split_ifs with hst
    · subst hst; exact Lagrange.eval_basis_self hinj (Finset.mem_univ _)
    · exact Lagrange.eval_basis_of_ne hst (Finset.mem_univ _)

  have hterm : ∀ s, ∀ e ∈ S, ∀ z : ℂ, EE e = z • e → EE (P s e) = a s • P s e := by
    intro s e he z hz
    by_cases h0 : e = 0
    · subst h0; simp
    obtain ⟨t, rfl⟩ := hpole z e he h0 hz
    rw [hPe s e _ hz, hLval s t]
    split_ifs with hst
    · subst hst; rw [one_smul, hz]
    · simp
  have hsum1 : ∀ e ∈ S, ∀ z : ℂ, EE e = z • e → ∑ s, P s e = e := by
    intro e he z hz
    by_cases h0 : e = 0
    · subst h0; simp
    obtain ⟨t, rfl⟩ := hpole z e he h0 hz
    have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨t, Finset.mem_univ _⟩
    have h1 : ∑ s, (Lagrange.basis Finset.univ a s).eval (a t) = 1 := by
      rw [← Polynomial.eval_finsetSum, Lagrange.sum_basis hinj hne, Polynomial.eval_one]
    calc ∑ s, P s e = ∑ s, (Lagrange.basis Finset.univ a s).eval (a t) • e :=
          Finset.sum_congr rfl fun s _ => hPe s e _ hz
      _ = e := by rw [← Finset.sum_smul, h1, one_smul]
  refine ⟨P, fun s => dc_isGKEndo_aeval (isGKEndo_eeF hσ hD _ false) _, ?_, ?_, ?_, ?_, ?_⟩
  · intro s f hf
    obtain ⟨fb, hfb, hfe⟩ := hdec f hf
    rw [hfe, map_sum, map_sum, Finset.smul_sum]
    exact Finset.sum_congr rfl fun b _ => hterm s _ (hfb b).1 _ (hfb b).2
  · intro s f _ hf
    rw [hPe s f _ hf, Lagrange.eval_basis_self hinj (Finset.mem_univ _), one_smul]
  · intro s f hf z' hz' hfz
    by_cases h0 : f = 0
    · subst h0; simp
    obtain ⟨t, rfl⟩ := hpole z' f hf h0 hfz
    have hts : s ≠ t := fun h => hz' (by rw [h])
    rw [hPe s f _ hfz, hLval s t, if_neg hts, zero_smul]
  · intro f hf
    obtain ⟨fb, hfb, hfe⟩ := hdec f hf
    conv_lhs => rw [hfe]
    rw [hfe]
    simp only [map_sum]
    rw [Finset.sum_comm]
    exact (Finset.sum_congr rfl fun b _ => hsum1 _ (hfb b).1 _ (hfb b).2).symm
  · intro s j
    obtain ⟨C, hC⟩ := NT_poly_le false (smE ε (rreg ε)) (Lagrange.basis Finset.univ a s) j
    have hdeg : (Lagrange.basis Finset.univ a s).natDegree = n - 1 := by
      rw [Lagrange.natDegree_basis hinj (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    refine ⟨C, fun f _ => ?_⟩
    have := hC f
    rw [hdeg] at this
    exact this

end ReciprocityTheory.ChartRestriction.DS.DecInf
