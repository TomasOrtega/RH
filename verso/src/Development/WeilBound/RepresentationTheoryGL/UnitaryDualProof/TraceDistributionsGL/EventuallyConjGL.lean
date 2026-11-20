import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TraceDistributionsGL.PhiIndep
import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.LeviTransposeDistributions.BoundOneTwo

noncomputable section

open Matrix Topology Filter GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi GlobalTheory.BZMir

namespace PositivityTheory.RgUd.AB.Pf

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

namespace Near

/- English proof (translation)
Simplify using `only [cj, _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc]`.
-/
theorem cj_mul (g h : GL (Fin (n + 1)) k) (x : Mx k n) : cj (g * h) x = cj g (cj h x) := by
  simp only [cj, _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc]

/- English proof (translation)
Simplify using `only [cj, ← Matrix.mul_assoc]`. Rewrite using `[Matrix.mul_assoc _ _ (g : Mx k n)]`. Simplify using `[← Units.val_mul, Matrix.mul_assoc]`.
-/
theorem inv_cj (g : GL (Fin (n + 1)) k) (x : Mx k n) :
    ((g⁻¹ : GL (Fin (n + 1)) k) : Mx k n) * cj g x * (g : Mx k n) = x := by
  simp only [cj, ← Matrix.mul_assoc]
  rw [Matrix.mul_assoc _ _ (g : Mx k n)]
  simp [← Units.val_mul, Matrix.mul_assoc]

/- English proof (translation)
Take `⟨hlc, hcs⟩` from `hf`. Apply `hcs.eventually_forall_of_forall_eventually` to reduce the goal to its premises. Introduce `y _`. Establish `hc : Continuous fun z : (Mx k n × Mx k n) × Mx k n => z.1.1 * z.2 * z.1.2` using `((continuous_fst.fst).matrix_mul continuous_snd).matrix_mul continuous_fst.snd`. Establish `h1` using `(hlc.comp_continuous hc).eventually_eq (((1 : Mx k n), (1 : Mx k n)), y)`.

Establish `h2` using `(hlc.comp_continuous continuous_snd).eventually_eq (((1 : Mx k n), (1 : Mx k n)), y)`. Use `filter_upwards [h1, h2] with z hz1 hz2`. Simplify using `only [Function.comp_apply] at hz1 hz2`. Rewrite using `[hz1, hz2]`. Simplify using the standard rewrite rules.
-/
theorem eventually_conj {f : Mx k n → ℂ} (hf : f ∈ SB (Mx k n)) :
    ∀ᶠ AB : Mx k n × Mx k n in 𝓝 (1, 1), ∀ y ∈ tsupport f, f (AB.1 * y * AB.2) = f y := by
  obtain ⟨hlc, hcs⟩ := hf
  apply hcs.eventually_forall_of_forall_eventually
  intro y _
  have hc : Continuous fun z : (Mx k n × Mx k n) × Mx k n => z.1.1 * z.2 * z.1.2 :=
    ((continuous_fst.fst).matrix_mul continuous_snd).matrix_mul continuous_fst.snd
  have h1 := (hlc.comp_continuous hc).eventually_eq (((1 : Mx k n), (1 : Mx k n)), y)
  have h2 := (hlc.comp_continuous continuous_snd).eventually_eq (((1 : Mx k n), (1 : Mx k n)), y)
  filter_upwards [h1, h2] with z hz1 hz2
  simp only [Function.comp_apply] at hz1 hz2
  rw [hz1, hz2]
  simp

def rE (w : Vc k n) : Mx k n := vecMulVec (eN k n) (w - eN k n)

/- English proof (translation)
Unfold `rE`. Rewrite using `[Matrix.vecMulVec_mul_vecMulVec]`. Establish `hd : (w - eN k n) ⬝ᵥ eN k n = w (Fin.last n) - 1`. Simplify using `[eN, dotProduct_single]`. Rewrite using `[hd]`.

Use extensionality with `i j`. Simplify using `only [vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rE_mul (w : Vc k n) : rE w * rE w = (w (Fin.last n) - 1) • rE w := by
  unfold rE
  rw [Matrix.vecMulVec_mul_vecMulVec]
  have hd : (w - eN k n) ⬝ᵥ eN k n = w (Fin.last n) - 1 := by
    simp [eN, dotProduct_single]
  rw [hd]
  ext i j
  simp only [vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply]
  ring

def sw (w : Vc k n) (hw : w (Fin.last n) ≠ 0) : GL (Fin (n + 1)) k :=
  ⟨1 + rE w, 1 - (w (Fin.last n))⁻¹ • rE w, by
    have hc : (w (Fin.last n))⁻¹ * (w (Fin.last n) - 1) = 1 - (w (Fin.last n))⁻¹ := by
      rw [mul_sub, inv_mul_cancel₀ hw, mul_one]
    rw [add_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, rE_mul,
      smul_smul, hc, sub_smul, one_smul]
    abel, by
    have hc : (w (Fin.last n))⁻¹ * (w (Fin.last n) - 1) = 1 - (w (Fin.last n))⁻¹ := by
      rw [mul_sub, inv_mul_cancel₀ hw, mul_one]
    rw [sub_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_add, Matrix.mul_one, rE_mul, smul_add, smul_smul, hc,
      sub_smul, one_smul]
    abel⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sw_val (w : Vc k n) (hw : w (Fin.last n) ≠ 0) : ((sw w hw : GL (Fin (n + 1)) k) : Mx k n) = 1 + rE w := rfl

/- English proof (translation)
Rewrite using `[sw_val]`. Distinguish the cases in `h : j = Fin.last n`. Substitute `h` using the available equality. Simplify using `[rE, eN, vecMulVec]`. Establish `h' : Fin.last n ≠ j` using `fun e => h e.symm`.

Simplify using `[rE, eN, vecMulVec, Matrix.one_apply, h, h']`.
-/
theorem sw_last (w : Vc k n) (hw : w (Fin.last n) ≠ 0) (j : Fin (n + 1)) :
    ((sw w hw : GL (Fin (n + 1)) k) : Mx k n) (Fin.last n) j = w j := by
  rw [sw_val]
  by_cases h : j = Fin.last n
  · subst h
    simp [rE, eN, vecMulVec]
  · have h' : Fin.last n ≠ j := fun e => h e.symm
    simp [rE, eN, vecMulVec, Matrix.one_apply, h, h']

end Near

/- English proof (translation)
Introduce `x`. Distinguish the cases in `hx : x ∈ tsupport f`. Conclude with `h1 x hx`. Establish `hx0 : f x = 0` using `image_eq_zero_of_notMem_tsupport hx`. Rewrite using `[hx0]`.

Assume the negation of the conclusion as `hne`. Establish `hy : cj g x ∈ tsupport f` using `subset_tsupport f hne`. Use `h2 _ hy` as an intermediate fact. Rewrite `this` using `[Near.inv_cj]`. Conclude with `hne (this.symm.trans hx0)`.
-/
private theorem conj_of_pair_lemma {f : Mx k n → ℂ} (g : GL (Fin (n + 1)) k)
    (h1 : ∀ y ∈ tsupport f, f ((g : Mx k n) * y * ((g⁻¹ : GL (Fin (n + 1)) k) : Mx k n)) = f y)
    (h2 : ∀ y ∈ tsupport f, f (((g⁻¹ : GL (Fin (n + 1)) k) : Mx k n) * y * (g : Mx k n)) = f y) :
    ∀ x, f (cj g x) = f x := by
  intro x
  by_cases hx : x ∈ tsupport f
  · exact h1 x hx
  · have hx0 : f x = 0 := image_eq_zero_of_notMem_tsupport hx
    rw [hx0]
    by_contra hne
    have hy : cj g x ∈ tsupport f := subset_tsupport f hne
    have := h2 _ hy
    rw [Near.inv_cj] at this
    exact hne (this.symm.trans hx0)

/- English proof (translation)
Establish `hr : Continuous (fun w : Vc k n => Near.rE w)`. Use `continuous_matrix fun i j => ?_` and prove the remaining obligations. Simplify using `only [Near.rE, vecMulVec_apply]`. Conclude with `continuous_const.mul (((continuous_apply j).sub continuous_const))`. Establish `h0 : Near.rE (eN k n) = 0` using `by simp [Near.rE]`.

Establish `hi : Tendsto (fun w : Vc k n => (w (Fin.last n))⁻¹) (𝓝 (eN k n)) (𝓝 ((eN k n (Fin.last n))⁻¹))` using `((continuous_apply (Fin.last n)).tendsto _).inv₀ (by simp [eN])`. Establish `hA : Tendsto (fun w : Vc k n => (1 : Mx k n) - (w (Fin.last n))⁻¹ • Near.rE w) (𝓝 (eN k n)) (𝓝 1)`. Use `(tendsto_const_nhds (x := (1 : Mx k n))).sub (hi.smul (hr.tendsto (eN k n)))` as an intermediate fact. Simplify `this` using `[h0]`. Establish `hB : Tendsto (fun w : Vc k n => (1 : Mx k n) + Near.rE w) (𝓝 (eN k n)) (𝓝 1)`.

Use `(tendsto_const_nhds (x := (1 : Mx k n))).add (hr.tendsto (eN k n))` as an intermediate fact. Simplify `this` using `[h0]`. Establish `hS` using `Near.eventually_conj hf`. Use `filter_upwards [(hA.prodMk_nhds hB).eventually hS, (hB.prodMk_nhds hA).eventually hS] with w h1 h2 hw`. Establish `eA : (((Near.sw w hw)⁻¹ : GL (Fin (n + 1)) k) : Mx k n) = 1 - (w (Fin.last n))⁻¹ • Near.rE w` using `rfl`.

Establish `eB : (((Near.sw w hw)⁻¹⁻¹ : GL (Fin (n + 1)) k) : Mx k n) = 1 + Near.rE w`. Rewrite using `[inv_inv]`. Conclude with `Near.sw_val w hw`. Apply `conj_of_pair_lemma` to reduce the goal to its premises. Introduce `y hy`.

Rewrite using `[eA, eB]`. Conclude with `h1 y hy`. Introduce `y hy`. Rewrite using `[eA, eB]`. Conclude with `h2 y hy`.
-/
private theorem near_lemma_2 {f : Mx k n → ℂ} (hf : f ∈ SB (Mx k n)) :
    ∀ᶠ w : Vc k n in 𝓝 (eN k n), ∀ hw : w (Fin.last n) ≠ 0,
      ∀ x, f (cj (Near.sw w hw)⁻¹ x) = f x := by
  have hr : Continuous (fun w : Vc k n => Near.rE w) := by
    refine continuous_matrix fun i j => ?_
    simp only [Near.rE, vecMulVec_apply]
    exact continuous_const.mul (((continuous_apply j).sub continuous_const))
  have h0 : Near.rE (eN k n) = 0 := by simp [Near.rE]
  have hi : Tendsto (fun w : Vc k n => (w (Fin.last n))⁻¹) (𝓝 (eN k n))
      (𝓝 ((eN k n (Fin.last n))⁻¹)) :=
    ((continuous_apply (Fin.last n)).tendsto _).inv₀ (by simp [eN])
  have hA : Tendsto (fun w : Vc k n => (1 : Mx k n) - (w (Fin.last n))⁻¹ • Near.rE w) (𝓝 (eN k n)) (𝓝 1) := by
    have := (tendsto_const_nhds (x := (1 : Mx k n))).sub (hi.smul (hr.tendsto (eN k n)))
    simpa [h0] using this
  have hB : Tendsto (fun w : Vc k n => (1 : Mx k n) + Near.rE w) (𝓝 (eN k n)) (𝓝 1) := by
    have := (tendsto_const_nhds (x := (1 : Mx k n))).add (hr.tendsto (eN k n))
    simpa [h0] using this
  have hS := Near.eventually_conj hf
  filter_upwards [(hA.prodMk_nhds hB).eventually hS, (hB.prodMk_nhds hA).eventually hS] with w h1 h2 hw
  have eA : (((Near.sw w hw)⁻¹ : GL (Fin (n + 1)) k) : Mx k n) = 1 - (w (Fin.last n))⁻¹ • Near.rE w := rfl
  have eB : (((Near.sw w hw)⁻¹⁻¹ : GL (Fin (n + 1)) k) : Mx k n) = 1 + Near.rE w := by
    rw [inv_inv]; exact Near.sw_val w hw
  apply conj_of_pair_lemma
  · intro y hy
    rw [eA, eB]
    exact h1 y hy
  · intro y hy
    rw [eA, eB]
    exact h2 y hy

open Near in
/- English proof (translation)
Introduce `n Λ hΛ f₀ hf₀`. Establish `hne : ∀ᶠ w : Vc k n in 𝓝 (eN k n), w (Fin.last n) ≠ 0` using `((continuous_apply (Fin.last n)).tendsto (eN k n)).eventually_ne (by simp [eN])`. Establish `hev` using `hne.and (near_lemma_2 hf₀)`. Establish `ht : Tendsto (fun v : Vc k n => eN k n + v) (𝓝 0) (𝓝 (eN k n))`. Simplify using `using (continuous_add_left (eN k n)).tendsto (0 : Vc k n)`.

Establish `hU` using `ht.eventually hev`. Take `⟨t, htU⟩` from `exists_box_subset hU`. Use `⟨t, fun s hst => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `w`. Distinguish the cases in `hw : w - eN k n ∈ box (Fin (n + 1)) s`.

Establish `hP` using `htU (hst hw)`. Simplify using `only [Set.mem_setOf_eq, add_sub_cancel] at hP`. Take `⟨hl, hc⟩` from `hP`. Establish `hw0 : w ≠ 0`. Introduce `h`.

Apply `hl` to reduce the goal to its premises. Simplify using `[h]`. Establish `hmem : w ∈ {w : Vc k n | w - eN k n ∈ box (Fin (n + 1)) s}` using `hw`. Rewrite using `[Set.indicator_of_mem hmem]`. Simplify using `only [phi, if_neg hw0, Set.indicator_of_mem hmem, Pi.one_apply, mul_one]`.

Establish `hex : ∃ s : GL (Fin (n + 1)) k, ∀ j, (s : Mx k n) (Fin.last n) j = w j` using `⟨sw w hl, sw_last w hl⟩`. Establish `hsec : ∀ j, ((sec w : GL (Fin (n + 1)) k) : Mx k n) (Fin.last n) j = w j`. Simplify using `only [sec, dif_pos hex]`. Conclude with `hex.choose_spec`. Establish `hrow : ∀ M : Mx k n, eLast k n ᵥ* M = M (Fin.last n)`.

Introduce `M`. Use extensionality with `j`. Simplify using `[eLast, vecMul, dotProduct, Pi.single_apply]`. Use `set p := sec w * (sw w hl)⁻¹ with hpdef`. Establish `hp : p ∈ Mir k n` using `by show eLast k n ᵥ* ((p : GL (Fin (n + 1)) k) : Mx k n) = eLast k n`.

Establish `e1 : eLast k n ᵥ* ((sec w : GL (Fin (n + 1)) k) : Mx k n) = eLast k n ᵥ* ((sw w hl : GL (Fin (n + 1)) k) : Mx k n)`. Rewrite using `[hrow, hrow]`. Use function extensionality and compare the values at `j`. Rewrite using `[hsec j, sw_last w hl j]`. Rewrite using `[hpdef, Units.val_mul, ← Matrix.vecMul_vecMul, e1, Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]`.

Establish `hsecp : sec w = p * sw w hl` using `by simp [hpdef]`. Establish `hfun : (fun x : Mx k n => f₀ (cj (sec w)⁻¹ x)) = f₀ ∘ cj p⁻¹`. Use function extensionality and compare the values at `x`. Rewrite using `[hsecp, _root_.mul_inv_rev, cj_mul, Function.comp_apply]`. Conclude with `hc hl _`.

Rewrite using `[hfun]`. Conclude with `hΛ p⁻¹ (inv_mem hp) f₀ hf₀`. Establish `hmem : w ∉ {w : Vc k n | w - eN k n ∈ box (Fin (n + 1)) s}` using `hw`. Rewrite using `[Set.indicator_of_notMem hmem]`. Simplify using `only [phi, Set.indicator_of_notMem hmem, mul_zero]`.

Use `split_ifs`. Both sides reduce to the same expression. Conclude with `map_zero Λ`.
-/
theorem phiNear : PhiNear k := by
  intro n Λ hΛ f₀ hf₀
  have hne : ∀ᶠ w : Vc k n in 𝓝 (eN k n), w (Fin.last n) ≠ 0 :=
    ((continuous_apply (Fin.last n)).tendsto (eN k n)).eventually_ne (by simp [eN])
  have hev := hne.and (near_lemma_2 hf₀)
  have ht : Tendsto (fun v : Vc k n => eN k n + v) (𝓝 0) (𝓝 (eN k n)) := by
    simpa using (continuous_add_left (eN k n)).tendsto (0 : Vc k n)
  have hU := ht.eventually hev
  obtain ⟨t, htU⟩ := exists_box_subset hU
  refine ⟨t, fun s hst => ?_⟩
  funext w
  by_cases hw : w - eN k n ∈ box (Fin (n + 1)) s
  · have hP := htU (hst hw)
    simp only [Set.mem_setOf_eq, add_sub_cancel] at hP
    obtain ⟨hl, hc⟩ := hP
    have hw0 : w ≠ 0 := by
      intro h
      apply hl
      simp [h]
    have hmem : w ∈ {w : Vc k n | w - eN k n ∈ box (Fin (n + 1)) s} := hw
    rw [Set.indicator_of_mem hmem]
    simp only [phi, if_neg hw0, Set.indicator_of_mem hmem, Pi.one_apply, mul_one]
    have hex : ∃ s : GL (Fin (n + 1)) k, ∀ j, (s : Mx k n) (Fin.last n) j = w j :=
      ⟨sw w hl, sw_last w hl⟩
    have hsec : ∀ j, ((sec w : GL (Fin (n + 1)) k) : Mx k n) (Fin.last n) j = w j := by
      simp only [sec, dif_pos hex]
      exact hex.choose_spec
    have hrow : ∀ M : Mx k n, eLast k n ᵥ* M = M (Fin.last n) := by
      intro M
      ext j
      simp [eLast, vecMul, dotProduct, Pi.single_apply]
    set p := sec w * (sw w hl)⁻¹ with hpdef
    have hp : p ∈ Mir k n := by
      show eLast k n ᵥ* ((p : GL (Fin (n + 1)) k) : Mx k n) = eLast k n
      have e1 : eLast k n ᵥ* ((sec w : GL (Fin (n + 1)) k) : Mx k n)
          = eLast k n ᵥ* ((sw w hl : GL (Fin (n + 1)) k) : Mx k n) := by
        rw [hrow, hrow]
        funext j
        rw [hsec j, sw_last w hl j]
      rw [hpdef, Units.val_mul, ← Matrix.vecMul_vecMul, e1, Matrix.vecMul_vecMul, ← Units.val_mul,
        mul_inv_cancel, Units.val_one, Matrix.vecMul_one]
    have hsecp : sec w = p * sw w hl := by simp [hpdef]
    have hfun : (fun x : Mx k n => f₀ (cj (sec w)⁻¹ x)) = f₀ ∘ cj p⁻¹ := by
      funext x
      rw [hsecp, _root_.mul_inv_rev, cj_mul, Function.comp_apply]
      exact hc hl _
    rw [hfun]
    exact hΛ p⁻¹ (inv_mem hp) f₀ hf₀
  · have hmem : w ∉ {w : Vc k n | w - eN k n ∈ box (Fin (n + 1)) s} := hw
    rw [Set.indicator_of_notMem hmem]
    simp only [phi, Set.indicator_of_notMem hmem, mul_zero]
    split_ifs
    · rfl
    · exact map_zero Λ

end PositivityTheory.RgUd.AB.Pf
