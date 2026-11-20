import Mathlib
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChart
import ReciprocityTheory.AnalyticForms.RegularLocalRings.AnChartA

namespace ReciprocityTheory.AnForm.R

open MvPolynomial

noncomputable section

variable {n : ℕ}

def zeroSet (K : Ideal (MvPolynomial (Fin n) ℂ)) : Set (Fin n → ℂ) :=
  {y | ∀ h ∈ K, eval y h = 0}

def evalFam {e : ℕ} (r : Fin e → MvPolynomial (Fin n) ℂ) (y : Fin n → ℂ) : Fin e → ℂ :=
  fun i => eval y (r i)

/- English proof (translation)
Take `⟨hen, F, hFK, -, hh, hhp, hcut⟩` from `exists_jacobian_cut K p e he`. Set `Ψ : (Fin n → ℂ) → (Fin e → ℂ) × (Fin (n - e) → ℂ)` to `fun y => (evalFam r y, fun k => eval y (F k))`. Establish `hΨ : ∀ y, Ψ y = (evalFam r y, fun k => eval y (F k))` using `fun y => rfl`. Set `Lr : (Fin n → ℂ) →L[ℂ] (Fin e → ℂ)` to `ContinuousLinearMap.pi fun i => ∑ j, eval p (pderiv j (r i)) • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) j`. Set `LF : (Fin n → ℂ) →L[ℂ] (Fin (n - e) → ℂ)` to `ContinuousLinearMap.pi fun k => ∑ j, eval p (pderiv j (F k)) • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) j`.

Set `Lm : (Fin n → ℂ) →L[ℂ] (Fin e → ℂ) × (Fin (n - e) → ℂ)` to `Lr.prod LF`. Establish `hΨd : HasFDerivAt Ψ Lm p` using `(hasFDerivAt_pi.2 fun i => ReciprocityTheory.AnForm.hasFDerivAt_mvPolynomial_eval (r i) p).prodMk (hasFDerivAt_pi.2 fun k => ReciprocityTheory.AnForm.hasFDerivAt_mvPolynomial_eval (F k) p)`. Establish `hΨan : AnalyticAt ℂ Ψ p`. Use `AnalyticAt.prod ?_ ?_` and prove the remaining obligations. Rewrite using `[analyticAt_pi_iff]`.

Introduce `i`. Conclude with `analyticOnNhd_eval_univ (r i) p (Set.mem_univ _)`. Rewrite using `[analyticAt_pi_iff]`. Introduce `k`. Conclude with `analyticOnNhd_eval_univ (F k) p (Set.mem_univ _)`.

Establish `hstrict : HasStrictFDerivAt Ψ Lm p`. Use `hΨan.hasStrictFDerivAt` as an intermediate fact. Rewrite `this` using `[hΨd.fderiv]`. Then use the resulting hypothesis. Establish `hinj : Function.Injective Lm`. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce `v hv`. Use `eq_zero_of_grad K p r hr F hFK hh hhp hcut v (fun i => ?_) (fun k => ?_)` and prove the remaining obligations. Use `congrFun (congrArg Prod.fst hv) i` as an intermediate fact. Simplify `this` using `[Lm, Lr]`. Use `congrFun (congrArg Prod.snd hv) k` as an intermediate fact.

Simplify `this` using `[Lm, LF]`. Establish `hsurjL : Function.Surjective Lm`. Establish `hdim : Module.finrank ℂ (Fin n → ℂ) = Module.finrank ℂ ((Fin e → ℂ) × (Fin (n - e) → ℂ))`. Simplify using `[Module.finrank_prod]`. Use linear arithmetic over natural numbers and integers.

Conclude with `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim (f := (Lm : (Fin n → ℂ) →ₗ[ℂ] (Fin e → ℂ) × (Fin (n - e) → ℂ)))).mp hinj`. Set `Le` to `ContinuousLinearEquiv.ofBijective Lm (LinearMap.ker_eq_bot.mpr hinj) (LinearMap.range_eq_top.mpr hsurjL)`. Establish `hLe : (Le : (Fin n → ℂ) →L[ℂ] (Fin e → ℂ) × (Fin (n - e) → ℂ)) = Lm` using `ContinuousLinearEquiv.coe_ofBijective _ _ _`. Establish `hφ : HasStrictFDerivAt Ψ (Le : (Fin n → ℂ) →L[ℂ] (Fin e → ℂ) × (Fin (n - e) → ℂ)) p`. Rewrite using `[hLe]`.

Conclude with `hstrict`. Set `Φ` to `hφ.toOpenPartialHomeomorph Ψ`. Establish `hΦ : ∀ x, Φ x = Ψ x` using `fun x => rfl`. Establish `hpS : p ∈ Φ.source` using `hφ.mem_toOpenPartialHomeomorph_source`. Establish `hsymm : AnalyticAt ℂ Φ.symm (Φ p)` using `Φ.analyticAt_symm' (i := Le) hpS hΨan hφ.hasFDerivAt.fderiv`.

Take `⟨s, hs, hsan⟩` from `hsymm.exists_mem_nhds_analyticOnNhd`. Take `⟨T0, hT0s, hT0o, hT0p⟩` from `mem_nhds_iff.mp hs`. Establish `hHo : IsOpen {y : Fin n → ℂ | eval y hh ≠ 0}` using `isOpen_ne_fun (MvPolynomial.continuous_eval hh) continuous_const`. Use `set O : Set (Fin n → ℂ) := (Φ.source ∩ {y | eval y hh ≠ 0}) ∩ Φ ⁻¹' T0 with hOdef`. Establish `hO : IsOpen O` using `(Φ.continuousOn.mono Set.inter_subset_left).isOpen_inter_preimage (Φ.open_source.inter hHo) hT0o`.

Use `set T : Set ((Fin e → ℂ) × (Fin (n - e) → ℂ)) := Φ.target ∩ Φ.symm ⁻¹' O with hTdef`. Establish `hT : IsOpen T` using `Φ.continuousOn_symm.isOpen_inter_preimage Φ.open_target hO`. Establish `hzs : ∀ y, eval y hh ≠ 0 → (∀ k, eval y (F k) = 0) → y ∈ zeroSet K`. Introduce `y hy hFy k hk`. Establish `hspan : Ideal.span (Set.range F) ≤ RingHom.ker (eval y)`.

Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `RingHom.mem_ker.mpr (hFy i)`. Establish `h1` using `RingHom.mem_ker.mp (hspan (hcut k hk))`. Rewrite `h1` using `[map_mul]`.

Conclude with `(mul_eq_zero.mp h1).resolve_left hy`. Use `⟨O, {w | (w, (0 : Fin (n - e) → ℂ)) ∈ T}, fun w => Φ.symm (w, 0), hO, ⟨⟨hpS, hhp⟩, hT0p⟩, hT.preimage (continuous_id.prodMk continuous_const), ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `w hw`. Establish `hw1 : (w, (0 : Fin (n - e) → ℂ)) ∈ s`. Establish `h2` using `hw.2.2`.

Rewrite `h2` using `[Set.mem_preimage, Φ.right_inv hw.1]`. Conclude with `hT0s h2`. Establish `h1 : AnalyticAt ℂ (fun w : Fin e → ℂ => (w, (0 : Fin (n - e) → ℂ))) w` using `analyticAt_id.prod analyticAt_const`. Conclude with `AnalyticAt.comp (f := fun w : Fin e → ℂ => (w, (0 : Fin (n - e) → ℂ))) (hsan _ hw1) h1`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `w hw`. Use `⟨hw.2, hzs _ hw.2.1.2 fun k => ?_⟩` and prove the remaining obligations. Use `congrFun (congrArg Prod.snd (Φ.right_inv hw.1)) k` as an intermediate fact. Rewrite `this` using `[hΦ, hΨ]`. Then use the resulting hypothesis. Introduce `w hw w' hw' h`.

Establish `h2 : Φ (Φ.symm (w, 0)) = Φ (Φ.symm (w', 0))`. Simplify using `only at h`. Rewrite using `[h]`. Rewrite `h2` using `[Φ.right_inv hw.1, Φ.right_inv hw'.1]`. Conclude with `congrArg Prod.fst h2`.

Introduce and unpack `y ⟨hyO, hyK⟩`. Establish `hy : Φ y = (evalFam r y, 0)`. Rewrite using `[hΦ, hΨ]`. Use `congr 1`. Use function extensionality and compare the values at `k`.

Conclude with `hyK _ (hFK k)`. Use `⟨evalFam r y, ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← hy]`. Conclude with `Φ.map_source hyO.1.1`. Use `show Φ.symm (evalFam r y, 0) ∈ O`.

Rewrite using `[← hy, Φ.left_inv hyO.1.1]`. Conclude with `hyO`. Use `show Φ.symm (evalFam r y, 0) = y`. Rewrite using `[← hy]`. Conclude with `Φ.left_inv hyO.1.1`.

Introduce `w hw`. Use `congrArg Prod.fst (Φ.right_inv hw.1)` as an intermediate fact. Rewrite `this` using `[hΦ, hΨ]`. Then use the resulting hypothesis.
-/
theorem exists_holo_coords (K : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ) (e : ℕ)
    [IsRegularLocalRing (locRing K p)] (he : ringKrullDim (locRing K p) = e)
    (r : Fin e → MvPolynomial (Fin n) ℂ)
    (hr : Ideal.span (Set.range fun i => algebraMap (MvPolynomial (Fin n) ℂ) (locRing K p) (r i)) =
      Ideal.map (algebraMap (MvPolynomial (Fin n) ℂ) (locRing K p)) (ptIdeal p)) :
    ∃ (U : Set (Fin n → ℂ)) (V : Set (Fin e → ℂ)) (g : (Fin e → ℂ) → (Fin n → ℂ)),
      IsOpen U ∧ p ∈ U ∧ IsOpen V ∧ AnalyticOnNhd ℂ g V ∧
      Set.BijOn g V (U ∩ zeroSet K) ∧ ∀ w ∈ V, evalFam r (g w) = w := by
  classical
  obtain ⟨hen, F, hFK, -, hh, hhp, hcut⟩ := exists_jacobian_cut K p e he
  let Ψ : (Fin n → ℂ) → (Fin e → ℂ) × (Fin (n - e) → ℂ) :=
    fun y => (evalFam r y, fun k => eval y (F k))
  have hΨ : ∀ y, Ψ y = (evalFam r y, fun k => eval y (F k)) := fun y => rfl
  let Lr : (Fin n → ℂ) →L[ℂ] (Fin e → ℂ) := ContinuousLinearMap.pi fun i =>
    ∑ j, eval p (pderiv j (r i)) • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) j
  let LF : (Fin n → ℂ) →L[ℂ] (Fin (n - e) → ℂ) := ContinuousLinearMap.pi fun k =>
    ∑ j, eval p (pderiv j (F k)) • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) j
  let Lm : (Fin n → ℂ) →L[ℂ] (Fin e → ℂ) × (Fin (n - e) → ℂ) := Lr.prod LF
  have hΨd : HasFDerivAt Ψ Lm p :=
    (hasFDerivAt_pi.2 fun i => ReciprocityTheory.AnForm.hasFDerivAt_mvPolynomial_eval (r i) p).prodMk
      (hasFDerivAt_pi.2 fun k => ReciprocityTheory.AnForm.hasFDerivAt_mvPolynomial_eval (F k) p)
  have hΨan : AnalyticAt ℂ Ψ p := by
    refine AnalyticAt.prod ?_ ?_
    · rw [analyticAt_pi_iff]; intro i; exact analyticOnNhd_eval_univ (r i) p (Set.mem_univ _)
    · rw [analyticAt_pi_iff]; intro k; exact analyticOnNhd_eval_univ (F k) p (Set.mem_univ _)
  have hstrict : HasStrictFDerivAt Ψ Lm p := by
    have := hΨan.hasStrictFDerivAt; rwa [hΨd.fderiv] at this
  have hinj : Function.Injective Lm := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    refine eq_zero_of_grad K p r hr F hFK hh hhp hcut v (fun i => ?_) (fun k => ?_)
    · have := congrFun (congrArg Prod.fst hv) i; simpa [Lm, Lr] using this
    · have := congrFun (congrArg Prod.snd hv) k; simpa [Lm, LF] using this
  have hsurjL : Function.Surjective Lm := by
    have hdim : Module.finrank ℂ (Fin n → ℂ) =
        Module.finrank ℂ ((Fin e → ℂ) × (Fin (n - e) → ℂ)) := by
      simp [Module.finrank_prod]; omega
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
      (f := (Lm : (Fin n → ℂ) →ₗ[ℂ] (Fin e → ℂ) × (Fin (n - e) → ℂ)))).mp hinj
  let Le := ContinuousLinearEquiv.ofBijective Lm (LinearMap.ker_eq_bot.mpr hinj)
    (LinearMap.range_eq_top.mpr hsurjL)
  have hLe : (Le : (Fin n → ℂ) →L[ℂ] (Fin e → ℂ) × (Fin (n - e) → ℂ)) = Lm :=
    ContinuousLinearEquiv.coe_ofBijective _ _ _
  have hφ : HasStrictFDerivAt Ψ (Le : (Fin n → ℂ) →L[ℂ] (Fin e → ℂ) × (Fin (n - e) → ℂ)) p := by
    rw [hLe]; exact hstrict
  let Φ := hφ.toOpenPartialHomeomorph Ψ
  have hΦ : ∀ x, Φ x = Ψ x := fun x => rfl
  have hpS : p ∈ Φ.source := hφ.mem_toOpenPartialHomeomorph_source
  have hsymm : AnalyticAt ℂ Φ.symm (Φ p) :=
    Φ.analyticAt_symm' (i := Le) hpS hΨan hφ.hasFDerivAt.fderiv
  obtain ⟨s, hs, hsan⟩ := hsymm.exists_mem_nhds_analyticOnNhd
  obtain ⟨T0, hT0s, hT0o, hT0p⟩ := mem_nhds_iff.mp hs
  have hHo : IsOpen {y : Fin n → ℂ | eval y hh ≠ 0} :=
    isOpen_ne_fun (MvPolynomial.continuous_eval hh) continuous_const
  set O : Set (Fin n → ℂ) := (Φ.source ∩ {y | eval y hh ≠ 0}) ∩ Φ ⁻¹' T0 with hOdef
  have hO : IsOpen O := (Φ.continuousOn.mono Set.inter_subset_left).isOpen_inter_preimage
    (Φ.open_source.inter hHo) hT0o
  set T : Set ((Fin e → ℂ) × (Fin (n - e) → ℂ)) := Φ.target ∩ Φ.symm ⁻¹' O with hTdef
  have hT : IsOpen T := Φ.continuousOn_symm.isOpen_inter_preimage Φ.open_target hO

  have hzs : ∀ y, eval y hh ≠ 0 → (∀ k, eval y (F k) = 0) → y ∈ zeroSet K := by
    intro y hy hFy k hk
    have hspan : Ideal.span (Set.range F) ≤ RingHom.ker (eval y) := by
      rw [Ideal.span_le]; rintro _ ⟨i, rfl⟩; exact RingHom.mem_ker.mpr (hFy i)
    have h1 := RingHom.mem_ker.mp (hspan (hcut k hk))
    rw [map_mul] at h1
    exact (mul_eq_zero.mp h1).resolve_left hy
  refine ⟨O, {w | (w, (0 : Fin (n - e) → ℂ)) ∈ T}, fun w => Φ.symm (w, 0), hO,
    ⟨⟨hpS, hhp⟩, hT0p⟩, hT.preimage (continuous_id.prodMk continuous_const), ?_, ?_, ?_⟩
  · intro w hw
    have hw1 : (w, (0 : Fin (n - e) → ℂ)) ∈ s := by
      have h2 := hw.2.2
      rw [Set.mem_preimage, Φ.right_inv hw.1] at h2
      exact hT0s h2
    have h1 : AnalyticAt ℂ (fun w : Fin e → ℂ => (w, (0 : Fin (n - e) → ℂ))) w :=
      analyticAt_id.prod analyticAt_const
    exact AnalyticAt.comp (f := fun w : Fin e → ℂ => (w, (0 : Fin (n - e) → ℂ))) (hsan _ hw1) h1
  · refine ⟨?_, ?_, ?_⟩
    · intro w hw
      refine ⟨hw.2, hzs _ hw.2.1.2 fun k => ?_⟩
      have := congrFun (congrArg Prod.snd (Φ.right_inv hw.1)) k
      rwa [hΦ, hΨ] at this
    · intro w hw w' hw' h
      have h2 : Φ (Φ.symm (w, 0)) = Φ (Φ.symm (w', 0)) := by
        simp only at h; rw [h]
      rw [Φ.right_inv hw.1, Φ.right_inv hw'.1] at h2
      exact congrArg Prod.fst h2
    · rintro y ⟨hyO, hyK⟩
      have hy : Φ y = (evalFam r y, 0) := by
        rw [hΦ, hΨ]; congr 1; funext k; exact hyK _ (hFK k)
      refine ⟨evalFam r y, ⟨?_, ?_⟩, ?_⟩
      · rw [← hy]; exact Φ.map_source hyO.1.1
      · show Φ.symm (evalFam r y, 0) ∈ O
        rw [← hy, Φ.left_inv hyO.1.1]; exact hyO
      · show Φ.symm (evalFam r y, 0) = y
        rw [← hy]; exact Φ.left_inv hyO.1.1
  · intro w hw
    have := congrArg Prod.fst (Φ.right_inv hw.1)
    rwa [hΦ, hΨ] at this

end

end ReciprocityTheory.AnForm.R
