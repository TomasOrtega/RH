import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EulerOperatorInjectiveEigenvectorStatement
open scoped InnerProductSpace BigOperators

namespace GlobalTheory

/- English proof (translation)
Introduce `Γ _ K ι _ c H _ _ _ a B s e he hK hidem horth haK ha1 hfac hB hB1 hBK hs hs1 hloc hstep`. Use `haveI : CompleteSpace H := FiniteDimensional.complete ℂ H`. Establish `aK : ∀ g : Γ, a ((QuotientGroup.mk g : Γ ⧸ K).out) = a g`. Introduce `g`. Take `⟨k, hk⟩` from `QuotientGroup.mk_out_eq_mul K g`.

Rewrite using `[hk]`. Conclude with `haK g k k.2`. Establish `BK : ∀ g : Γ, B ((QuotientGroup.mk g : Γ ⧸ K).out) = B g`. Introduce `g`. Take `⟨k, hk⟩` from `QuotientGroup.mk_out_eq_mul K g`.

Rewrite using `[hk]`. Conclude with `hBK g k k.2`. Establish `acv : ∀ v (g : Γ), a (c v ((QuotientGroup.mk g : Γ ⧸ K.comap (c v)).out)) = a (c v g)`. Introduce `v g`. Take `⟨k, hk⟩` from `QuotientGroup.mk_out_eq_mul (K.comap (c v)) g`.

Rewrite using `[hk, map_mul]`. Conclude with `haK _ _ k.2`. Establish `cv1 : ∀ v, c v ((QuotientGroup.mk 1 : Γ ⧸ K.comap (c v)).out) ∈ K`. Introduce `v`. Take `⟨k, hk⟩` from `QuotientGroup.mk_out_eq_mul (K.comap (c v)) (1 : Γ)`.

Rewrite using `[hk, one_mul]`. Conclude with `k.2`. Set `x0 : ∀ v, Γ ⧸ K.comap (c v)` to `fun v => QuotientGroup.mk 1`. Set `a' : ∀ v, Γ ⧸ K.comap (c v) → ℂ` to `fun v x => a (c v x.out)`. Set `Z : ι → (H →L[ℂ] H)` to `fun v => ∑' x : Γ ⧸ K.comap (c v), a (c v x.out) • B (c v x.out)`.

Set `B' : (∀ v, Γ ⧸ K.comap (c v)) → (H →L[ℂ] H)` to `fun f => if h : {w | f w ≠ (QuotientGroup.mk 1 : Γ ⧸ K.comap (c w))}.Finite then B ((e.symm ⟨f, h⟩).out) else B 1`. Establish `B'eval : ∀ (f : ∀ v, Γ ⧸ K.comap (c v)) (g : Γ), (∀ w, f w = (QuotientGroup.mk g : Γ ⧸ K.comap (c w))) → B' f = B g`. Introduce `f g hf`. Establish `hfeq : f = (e (QuotientGroup.mk g)).1` using `funext fun w => (hf w).trans (he g w).symm`. Substitute `hfeq` using the available equality.

Simplify using `only [B', dif_pos (e (QuotientGroup.mk g)).2, Subtype.coe_eta, Equiv.symm_apply_apply]`. Conclude with `BK g`. Establish `h1 : ∀ v, a' v (x0 v) = 1`. Introduce `v`. Use `show a (c v ((QuotientGroup.mk 1 : Γ ⧸ K.comap (c v)).out)) = 1`.

Rewrite using `[acv, map_one, ha1]`. Establish `hfin : ∀ v (C : Finset (Γ ⧸ K.comap (c v))), x0 v ∉ C → ∑ x ∈ C, ‖a' v x‖ ≤ s v`. Introduce `v C hC`. Establish `eqcl : ∀ x y : Γ ⧸ K.comap (c v), (c v x.out)⁻¹ * c v y.out ∈ K → x = y`. Introduce `x y hxy`.

Establish `hm : x.out⁻¹ * y.out ∈ K.comap (c v)`. Rewrite using `[Subgroup.mem_comap, map_mul, map_inv]`. Conclude with `hxy`. Use `(QuotientGroup.eq (s := K.comap (c v))).mpr hm` as an intermediate fact. Simplify `this` using `only [QuotientGroup.out_eq']`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_image]`. Introduce `x _ y _ hxy`. Apply `eqcl` to reduce the goal to its premises. Establish `hxy' : c v x.out = c v y.out` using `hxy`.

Rewrite using `[hxy', inv_mul_cancel]`. Conclude with `K.one_mem`. Use `_ ≤ s v := by`. Apply `hloc` to reduce the goal to its premises. Introduce `g hg`.

Take `⟨x, hx, rfl⟩` from `Finset.mem_image.mp hg`. Use `⟨hidem v _, fun hmem => hC ?_⟩` and prove the remaining obligations. Establish `: x = x0 v`. Apply `eqcl` to reduce the goal to its premises. Conclude with `K.mul_mem (K.inv_mem hmem) (cv1 v)`.

Rewrite using `[← this]`. Conclude with `hx`. Introduce `g hg g' hg' hgg`. Take `⟨x, hx, rfl⟩` from `Finset.mem_image.mp hg`. Take `⟨y, hy, rfl⟩` from `Finset.mem_image.mp hg'`.

Rewrite using `[eqcl x y hgg]`. Establish `hnorm : ∀ f, ‖B' f‖ ≤ 1`. Introduce `f`. Simplify using `only [B']`. Use `split_ifs`.

Conclude with `hB _`. Conclude with `hB 1`. Establish `hx0 : B' x0 = 1`. Rewrite using `[B'eval x0 1 (fun w => rfl), hB1]`. Establish `hrec : ∀ v (f : ∀ v, Γ ⧸ K.comap (c v)), {w | f w ≠ x0 w}.Finite → f v = x0 v → HasSum (fun x => a' v x • B' (Function.update f v x)) (B' f * Z v)`.

Introduce `v f hf hv`. Use `set γ' : Γ := (e.symm ⟨f, hf⟩).out with hγ'`. Establish `hfγ' : ∀ w, f w = (QuotientGroup.mk γ' : Γ ⧸ K.comap (c w))`. Introduce `w`. Establish `h2 : e (QuotientGroup.mk γ') = ⟨f, hf⟩`.

Rewrite using `[hγ', QuotientGroup.out_eq', Equiv.apply_symm_apply]`. Establish `h3` using `congrArg (fun p => p.1 w) h2`. Simplify using `only at h3`. Rewrite using `[← h3, he]`. Use `set γ : Γ := γ' * (c v γ')⁻¹ with hγ`.

Establish `hcγ : c v γ = 1`. Rewrite using `[hγ, map_mul, map_inv, hidem, mul_inv_cancel]`. Establish `key : ∀ x : Γ ⧸ K.comap (c v), B' (Function.update f v x) = B (γ * c v x.out)`. Introduce `x`. Apply `B'eval` to reduce the goal to its premises.

Introduce `w`. Break down `eq_or_ne w v with rfl | hw` into its components or cases. Rewrite using `[Function.update_self]`. Use `((QuotientGroup.eq (s := K.comap (c w))).mpr ?_).trans (QuotientGroup.out_eq' x) |>.symm` and prove the remaining obligations. Rewrite using `[Subgroup.mem_comap]`.

Simplify using `only [mul_inv_rev, map_mul, map_inv, hidem, hcγ, inv_one, mul_one, inv_mul_cancel]`. Conclude with `K.one_mem`. Rewrite using `[Function.update_of_ne hw, hfγ' w, QuotientGroup.eq, Subgroup.mem_comap]`. Simplify using `only [hγ, mul_inv_rev, inv_inv, map_mul, map_inv, horth v w _ hw.symm, inv_one, mul_one, one_mul, inv_mul_cancel]`. Conclude with `K.one_mem`.

Establish `hupd : Function.update f v (x0 v) = f`. Rewrite using `[← hv]`. Conclude with `Function.update_eq_self v f`. Establish `hBf : B' f = B γ`. Rewrite using `[← hupd, key, hBK _ _ (cv1 v)]`.

Rewrite using `[hBf]`. Use `hstep v γ` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `x`. Rewrite using `[key]`.

Take `⟨W, hW, hinj, -⟩` from `GlobalTheory.T.eulerOperator_injective_eigenvector ι (fun v => Γ ⧸ K.comap (c v)) x0 H a' s B' Z h1 hs hs1 hfin hnorm hx0 hrec`. Use `⟨W, hinj, fun x y => ?_⟩` and prove the remaining obligations. Establish `hW'` using `(Equiv.hasSum_iff e).mpr hW`. Establish `hfun : ((fun f : {f : ∀ v, Γ ⧸ K.comap (c v) // {w | f w ≠ x0 w}.Finite} => (∏ᶠ v, a' v (f.1 v)) • B' f.1) ∘ e) = fun q => a q.out • B q.out`. Use function extensionality and compare the values at `q`.

Establish `hq : ∀ v, (e q).1 v = (QuotientGroup.mk q.out : Γ ⧸ K.comap (c v))`. Introduce `v`. Use `conv_lhs => rw [← QuotientGroup.out_eq' q]`. Conclude with `he _ v`. Simplify using `only [Function.comp]`.

Rewrite using `[B'eval _ q.out hq]`. Use `congr 1`. Rewrite using `[hfac q.out]`. Conclude with `finprod_congr fun v => by simp only [a']; rw [hq v]; exact acv v q.out`. Rewrite `hW'` using `[hfun]`.

Use `hW'.mapL ((innerSL ℂ x).comp (ContinuousLinearMap.apply ℂ H y))` as an intermediate fact. Simplify `this` using `[inner_smul_right]`.
-/
theorem hasSum_inner_quotient_eulerProduct_injective : ∀ (Γ : Type) [Group Γ] (K : Subgroup Γ) (ι : Type) [DecidableEq ι] (c : ι → Γ →* Γ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (a : Γ → ℂ) (B : Γ → (H →L[ℂ] H)) (s : ι → ℝ) (e : Γ ⧸ K ≃ {f : ∀ v, Γ ⧸ K.comap (c v) // {w | f w ≠ (QuotientGroup.mk 1 : Γ ⧸ K.comap (c w))}.Finite}), (∀ (g : Γ) v, (e (QuotientGroup.mk g)).1 v = (QuotientGroup.mk g : Γ ⧸ K.comap (c v))) → (∀ g, g ∈ K ↔ ∀ v, c v g ∈ K) → (∀ v g, c v (c v g) = c v g) → (∀ v w g, v ≠ w → c w (c v g) = 1) → (∀ g k, k ∈ K → a (g * k) = a g) → a 1 = 1 → (∀ g, a g = ∏ᶠ v, a (c v g)) → (∀ g, ‖B g‖ ≤ 1) → B 1 = 1 → (∀ g k, k ∈ K → B (g * k) = B g) → Summable s → (∀ v, s v < 1) → (∀ v (C : Finset Γ), (∀ g ∈ C, c v g = g ∧ g ∉ K) → (∀ g ∈ C, ∀ g' ∈ C, g⁻¹ * g' ∈ K → g = g') → ∑ g ∈ C, ‖a g‖ ≤ s v) → (∀ v γ, HasSum (fun x : Γ ⧸ K.comap (c v) => a (c v (Quotient.out x)) • B (γ * c v (Quotient.out x))) (B γ * ∑' x : Γ ⧸ K.comap (c v), a (c v (Quotient.out x)) • B (c v (Quotient.out x)))) → ∃ W : H →L[ℂ] H, Function.Injective W ∧ ∀ x y, HasSum (fun q : Γ ⧸ K => a (Quotient.out q) * ⟪x, B (Quotient.out q) y⟫_ℂ) ⟪x, W y⟫_ℂ := by
  intro Γ _ K ι _ c H _ _ _ a B s e he hK hidem horth haK ha1 hfac hB hB1 hBK hs hs1 hloc hstep
  classical
  haveI : CompleteSpace H := FiniteDimensional.complete ℂ H

  have aK : ∀ g : Γ, a ((QuotientGroup.mk g : Γ ⧸ K).out) = a g := by
    intro g
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K g
    rw [hk]; exact haK g k k.2
  have BK : ∀ g : Γ, B ((QuotientGroup.mk g : Γ ⧸ K).out) = B g := by
    intro g
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K g
    rw [hk]; exact hBK g k k.2
  have acv : ∀ v (g : Γ), a (c v ((QuotientGroup.mk g : Γ ⧸ K.comap (c v)).out)) = a (c v g) := by
    intro v g
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (K.comap (c v)) g
    rw [hk, map_mul]; exact haK _ _ k.2
  have cv1 : ∀ v, c v ((QuotientGroup.mk 1 : Γ ⧸ K.comap (c v)).out) ∈ K := by
    intro v
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (K.comap (c v)) (1 : Γ)
    rw [hk, one_mul]; exact k.2
  let x0 : ∀ v, Γ ⧸ K.comap (c v) := fun v => QuotientGroup.mk 1
  let a' : ∀ v, Γ ⧸ K.comap (c v) → ℂ := fun v x => a (c v x.out)
  let Z : ι → (H →L[ℂ] H) := fun v => ∑' x : Γ ⧸ K.comap (c v), a (c v x.out) • B (c v x.out)
  let B' : (∀ v, Γ ⧸ K.comap (c v)) → (H →L[ℂ] H) := fun f =>
    if h : {w | f w ≠ (QuotientGroup.mk 1 : Γ ⧸ K.comap (c w))}.Finite then B ((e.symm ⟨f, h⟩).out) else B 1
  have B'eval : ∀ (f : ∀ v, Γ ⧸ K.comap (c v)) (g : Γ),
      (∀ w, f w = (QuotientGroup.mk g : Γ ⧸ K.comap (c w))) → B' f = B g := by
    intro f g hf
    have hfeq : f = (e (QuotientGroup.mk g)).1 := funext fun w => (hf w).trans (he g w).symm
    subst hfeq
    simp only [B', dif_pos (e (QuotientGroup.mk g)).2, Subtype.coe_eta, Equiv.symm_apply_apply]
    exact BK g
  have h1 : ∀ v, a' v (x0 v) = 1 := by
    intro v
    show a (c v ((QuotientGroup.mk 1 : Γ ⧸ K.comap (c v)).out)) = 1
    rw [acv, map_one, ha1]
  have hfin : ∀ v (C : Finset (Γ ⧸ K.comap (c v))), x0 v ∉ C → ∑ x ∈ C, ‖a' v x‖ ≤ s v := by
    intro v C hC
    have eqcl : ∀ x y : Γ ⧸ K.comap (c v), (c v x.out)⁻¹ * c v y.out ∈ K → x = y := by
      intro x y hxy
      have hm : x.out⁻¹ * y.out ∈ K.comap (c v) := by
        rw [Subgroup.mem_comap, map_mul, map_inv]; exact hxy
      have := (QuotientGroup.eq (s := K.comap (c v))).mpr hm
      simpa only [QuotientGroup.out_eq'] using this
    calc ∑ x ∈ C, ‖a' v x‖ = ∑ g ∈ C.image (fun x => c v x.out), ‖a g‖ := by
          rw [Finset.sum_image]
          intro x _ y _ hxy
          apply eqcl
          have hxy' : c v x.out = c v y.out := hxy
          rw [hxy', inv_mul_cancel]; exact K.one_mem
      _ ≤ s v := by
          apply hloc
          · intro g hg
            obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hg
            refine ⟨hidem v _, fun hmem => hC ?_⟩
            have : x = x0 v := by
              apply eqcl
              exact K.mul_mem (K.inv_mem hmem) (cv1 v)
            rw [← this]; exact hx
          · intro g hg g' hg' hgg
            obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hg
            obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hg'
            rw [eqcl x y hgg]
  have hnorm : ∀ f, ‖B' f‖ ≤ 1 := by
    intro f
    simp only [B']
    split_ifs
    · exact hB _
    · exact hB 1
  have hx0 : B' x0 = 1 := by
    rw [B'eval x0 1 (fun w => rfl), hB1]
  have hrec : ∀ v (f : ∀ v, Γ ⧸ K.comap (c v)), {w | f w ≠ x0 w}.Finite → f v = x0 v →
      HasSum (fun x => a' v x • B' (Function.update f v x)) (B' f * Z v) := by
    intro v f hf hv
    set γ' : Γ := (e.symm ⟨f, hf⟩).out with hγ'
    have hfγ' : ∀ w, f w = (QuotientGroup.mk γ' : Γ ⧸ K.comap (c w)) := by
      intro w
      have h2 : e (QuotientGroup.mk γ') = ⟨f, hf⟩ := by
        rw [hγ', QuotientGroup.out_eq', Equiv.apply_symm_apply]
      have h3 := congrArg (fun p => p.1 w) h2
      simp only at h3
      rw [← h3, he]
    set γ : Γ := γ' * (c v γ')⁻¹ with hγ
    have hcγ : c v γ = 1 := by
      rw [hγ, map_mul, map_inv, hidem, mul_inv_cancel]
    have key : ∀ x : Γ ⧸ K.comap (c v), B' (Function.update f v x) = B (γ * c v x.out) := by
      intro x
      apply B'eval
      intro w
      rcases eq_or_ne w v with rfl | hw
      · rw [Function.update_self]
        refine ((QuotientGroup.eq (s := K.comap (c w))).mpr ?_).trans (QuotientGroup.out_eq' x) |>.symm
        rw [Subgroup.mem_comap]
        simp only [mul_inv_rev, map_mul, map_inv, hidem, hcγ, inv_one, mul_one, inv_mul_cancel]
        exact K.one_mem
      · rw [Function.update_of_ne hw, hfγ' w, QuotientGroup.eq, Subgroup.mem_comap]
        simp only [hγ, mul_inv_rev, inv_inv, map_mul, map_inv, horth v w _ hw.symm, inv_one, mul_one,
          one_mul, inv_mul_cancel]
        exact K.one_mem
    have hupd : Function.update f v (x0 v) = f := by
      rw [← hv]; exact Function.update_eq_self v f
    have hBf : B' f = B γ := by
      rw [← hupd, key, hBK _ _ (cv1 v)]
    rw [hBf]
    have := hstep v γ
    convert this using 1
    funext x
    rw [key]
  obtain ⟨W, hW, hinj, -⟩ := GlobalTheory.T.eulerOperator_injective_eigenvector ι (fun v => Γ ⧸ K.comap (c v)) x0 H a' s B' Z h1 hs hs1 hfin
    hnorm hx0 hrec
  refine ⟨W, hinj, fun x y => ?_⟩
  have hW' := (Equiv.hasSum_iff e).mpr hW
  have hfun : ((fun f : {f : ∀ v, Γ ⧸ K.comap (c v) // {w | f w ≠ x0 w}.Finite} =>
      (∏ᶠ v, a' v (f.1 v)) • B' f.1) ∘ e) = fun q => a q.out • B q.out := by
    funext q
    have hq : ∀ v, (e q).1 v = (QuotientGroup.mk q.out : Γ ⧸ K.comap (c v)) := by
      intro v
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      exact he _ v
    simp only [Function.comp]
    rw [B'eval _ q.out hq]
    congr 1
    rw [hfac q.out]
    exact finprod_congr fun v => by simp only [a']; rw [hq v]; exact acv v q.out
  rw [hfun] at hW'
  have := hW'.mapL ((innerSL ℂ x).comp (ContinuousLinearMap.apply ℂ H y))
  simpa [inner_smul_right] using this

end GlobalTheory
