import ReciprocityTheory.AnalyticForms.AnalyticCharts.ExistsAnalyticGraphChartMvPolynomial
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsSmoothPts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.LemCone

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

/- English proof (translation)
The claim follows from `(ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : n => ℂ) j).analyticAt z`.
-/
theorem gbap_analyticAt_apply {n : Type} [Fintype n] (j : n) (z : n → ℂ) :
    AnalyticAt ℂ (fun z : n → ℂ => z j) z :=
  (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : n => ℂ) j).analyticAt z

/- English proof (translation)
Use function extensionality and compare the values at `j`. Break down `Fin.eq_self_or_eq_succAbove k j with rfl | ⟨i, rfl⟩` into its components or cases. Simplify using `[hk]`. Simplify using `[hb]`.
-/
theorem gbap_insertNth_eq {D : ℕ} (k : Fin (D + 1)) (a : ℂ) (b : Fin D → ℂ) (w : Fin (D + 1) → ℂ)
    (hk : w k = a) (hb : ∀ i, w (k.succAbove i) = b i) : Fin.insertNth k a b = w := by
  funext j
  rcases Fin.eq_self_or_eq_succAbove k j with rfl | ⟨i, rfl⟩
  · simp [hk]
  · simp [hb]

/- English proof (translation)
Establish `hF0 : ∀ i, eval p (F i) = 0` using `(hZ p hp0 hph).1 hp`. Take `⟨σ, U, V, g, hU, hpU, hV, hg, hbij, hproj⟩` from `ReciprocityTheory.AnForm.exists_analytic_graph_chart_mvPolynomial F p hF0 hjac`. Take `⟨π, hπ⟩ : ∃ π : (Fin (D + 1 + c) → ℂ) → Fin (D + 1) → ℂ, π = fun z i => z (σ (Fin.castAdd c i))` from `⟨_, rfl⟩`. Establish `hπa : ∀ z i, π z i = z (σ (Fin.castAdd c i))` using `fun z i => by rw [hπ]`. Establish `hπs : ∀ (t : ℂ) z, π (t • z) = t • π z` using `fun t z => by`.

Use function extensionality and compare the values at `i`. Simplify using `[hπa]`. Establish `hπg : ∀ w ∈ V, π (g w) = w` using `fun w hw => by`. Rewrite using `[hπ]`. Conclude with `hproj w hw`.

Establish `hπan : ∀ j z, AnalyticAt ℂ (fun z => π z j) z` using `fun j z => by`. Rewrite using `[hπ]`. Conclude with `gbap_analyticAt_apply _ z`. Establish `htgt : ∀ z, z ≠ 0 → z ∈ Z → z ∈ U → eval z h ≠ 0 → ∃ w ∈ V, g w = z ∧ w = π z`. Introduce `z hz0 hzZ hzU hzh`.

Take `⟨w, hw, hgw⟩` from `hbij.surjOn ⟨hzU, (hZ z hz0 hzh).1 hzZ⟩`. Conclude with `⟨w, hw, hgw, by rw [← hgw, hπg w hw]⟩`. Take `⟨w₀, hw₀V, hgw₀, hw₀⟩` from `htgt p hp0 hp hpU hph`. Establish `hπp : π p ≠ 0`. Introduce `hπ0`.

Establish `hWo : IsOpen (U ∩ {z | eval z h ≠ 0} ∩ {z | z ≠ 0})` using `(hU.inter (isOpen_ne_fun (MvPolynomial.continuous_eval h) continuous_const)).inter isOpen_ne`. Establish `hc : ContinuousAt (fun t : ℂ => t • p) 1` using `(continuous_id.smul continuous_const).continuousAt`. Establish `hev : ∀ᶠ t in nhds (1 : ℂ), t • p ∈ U ∩ {z | eval z h ≠ 0} ∩ {z | z ≠ 0}` using `hc.preimage_mem_nhds (by rw [one_smul]; exact hWo.mem_nhds ⟨⟨hpU, hph⟩, hp0⟩)`. Take `⟨t, ⟨⟨htU, hth⟩, htp0⟩, ht1⟩` from `((hev.filter_mono nhdsWithin_le_nhds).and (self_mem_nhdsWithin (s := ({1}ᶜ : Set ℂ)))).exists`. Establish `ht0 : t ≠ 0`.

Introduce and unpack `rfl`. Conclude with `htp0 (zero_smul ℂ p)`. Take `⟨w, hwV, hgw, hw⟩` from `htgt (t • p) htp0 (hZc p hp t ht0) htU hth`. Establish `hw0 : w = w₀`. Rewrite using `[hw, hw₀, hπs, hπ0, smul_zero]`.

Establish `htp : t • p = p` using `by rw [← hgw, hw0, hgw₀]`. Establish `: (t - 1) • p = 0` using `by rw [sub_smul, one_smul, htp, sub_self]`. Break down `smul_eq_zero.1 this with h1 | h1` into its components or cases. Conclude with `ht1 (sub_eq_zero.1 h1)`. Conclude with `hp0 h1`.

Take `⟨k, hk⟩` from `Function.ne_iff.1 hπp`. Use `set a := π p k with ha_def`. Establish `ha : a ≠ 0` using `hk`. Take `⟨W, hW⟩ : ∃ W : (Fin D → ℂ) → Fin (D + 1) → ℂ, W = fun y => Fin.insertNth k a (fun i => π p (k.succAbove i) + y i)` from `⟨_, rfl⟩`. Establish `hWk : ∀ y, W y k = a` using `fun y => by rw [hW]; simp`.

Establish `hWs : ∀ y i, W y (k.succAbove i) = π p (k.succAbove i) + y i` using `fun y i => by`. Rewrite using `[hW]`. Simplify using the standard rewrite rules. Establish `hW0 : W 0 = π p`. Rewrite using `[hW]`.

Conclude with `gbap_insertNth_eq k a _ (π p) rfl (fun i => by simp)`. Establish `hWan : ∀ y, AnalyticAt ℂ W y`. Introduce `y`. Rewrite using `[hW]`. Use `analyticAt_pi_iff.2 fun j => ?_` and prove the remaining obligations.

Break down `Fin.eq_self_or_eq_succAbove k j with rfl | ⟨i, rfl⟩` into its components or cases. Simplify using `only [Fin.insertNth_apply_same]`. Conclude with `analyticAt_const`. Simplify using `only [Fin.insertNth_apply_succAbove]`. Conclude with `analyticAt_const.add (gbap_analyticAt_apply i y)`.

Establish `hWc : Continuous W` using `continuous_iff_continuousAt.2 fun y => (hWan y).continuousAt`. Establish `hGo : IsOpen (V ∩ g ⁻¹' {z | eval z h ≠ 0})` using `hg.continuousOn.isOpen_inter_preimage hV (isOpen_ne_fun (MvPolynomial.continuous_eval h) continuous_const)`. Establish `h0G : (0 : Fin D → ℂ) ∈ W ⁻¹' (V ∩ g ⁻¹' {z | eval z h ≠ 0})`. Simplify using `only [Set.mem_preimage, Set.mem_inter_iff, hW0, ← hw₀]`. Conclude with `⟨hw₀V, by rw [Set.mem_ofPred_eq, hgw₀]; exact hph⟩`.

Take `⟨ρ₀, hρ₀, hball⟩` from `Metric.isOpen_iff.1 (hGo.preimage hWc) 0 h0G`. Establish `hyV : ∀ y ∈ Metric.ball (0 : Fin D → ℂ) ρ₀, W y ∈ V ∧ eval (g (W y)) h ≠ 0` using `fun y hy => hball hy`. Establish `hγmem : ∀ y ∈ Metric.ball (0 : Fin D → ℂ) ρ₀, g (W y) ∈ U ∧ ∀ i, eval (g (W y)) (F i) = 0` using `fun y hy => hbij.mapsTo (hyV y hy).1`. Establish `hπγ : ∀ y ∈ Metric.ball (0 : Fin D → ℂ) ρ₀, π (g (W y)) = W y` using `fun y hy => hπg _ (hyV y hy).1`. Establish `hγ0 : ∀ y ∈ Metric.ball (0 : Fin D → ℂ) ρ₀, g (W y) ≠ 0`.

Introduce `y hy h0`. Use `congrFun (hπγ y hy) k` as an intermediate fact. Rewrite `this` using `[h0, hWk, hπa]`. Conclude with `ha (by simpa using this.symm)`. Establish `hγZ : ∀ y ∈ Metric.ball (0 : Fin D → ℂ) ρ₀, g (W y) ∈ Z` using `fun y hy => (hZ _ (hγ0 y hy) (hyV y hy).2).2 (hγmem y hy).2`.

Take `⟨q, hq⟩ : ∃ q : (Fin (D + 1 + c) → ℂ) → Fin D → ℂ, q = fun z i => π z (k.succAbove i) * a / π z k - π p (k.succAbove i)` from `⟨_, rfl⟩`. Establish `hqa : ∀ z i, q z i = π z (k.succAbove i) * a / π z k - π p (k.succAbove i)` using `fun z i => by rw [hq]`. Take `⟨ν, hν⟩ : ∃ ν : (Fin (D + 1 + c) → ℂ) → Fin (D + 1 + c) → ℂ, ν = fun z => (a / π z k) • z` from `⟨_, rfl⟩`. Establish `hνa : ∀ z, ν z = (a / π z k) • z` using `fun z => by rw [hν]`. Use `set A : Set (Fin (D + 1 + c) → ℂ) := {z | π z k ≠ 0} with hA`.

Establish `hAo : IsOpen A` using `isOpen_ne_fun (continuous_iff_continuousAt.2 fun z => (hπan k z).continuousAt) continuous_const`. Establish `hqan : ∀ z ∈ A, AnalyticAt ℂ q z`. Introduce `z hz`. Rewrite using `[hq]`. Use `analyticAt_pi_iff.2 fun i => ?_` and prove the remaining obligations.

Conclude with `(((hπan _ z).mul analyticAt_const).div (hπan k z) hz).sub analyticAt_const`. Establish `hνan : ∀ z ∈ A, AnalyticAt ℂ ν z`. Introduce `z hz`. Rewrite using `[hν]`. Use `analyticAt_pi_iff.2 fun j => ?_` and prove the remaining obligations.

Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Conclude with `(analyticAt_const.div (hπan k z) hz).mul (gbap_analyticAt_apply j z)`. Use `set O : Set (Fin (D + 1 + c) → ℂ) := A ∩ ν ⁻¹' (U ∩ {z | eval z h ≠ 0}) ∩ q ⁻¹' Metric.ball 0 ρ₀ with hO`. Establish `hOo : IsOpen O`. Establish `h1 : IsOpen (A ∩ ν ⁻¹' (U ∩ {z | eval z h ≠ 0}))` using `ContinuousOn.isOpen_inter_preimage (show ContinuousOn ν A from fun z hz => (hνan z hz).continuousAt.continuousWithinAt) hAo (hU.inter (isOpen_ne_fun (MvPolynomial.continuous_eval h) continuous_const))`.

Conclude with `ContinuousOn.isOpen_inter_preimage (show ContinuousOn q (A ∩ ν ⁻¹' (U ∩ {z | eval z h ≠ 0})) from fun z hz => (hqan z hz.1).continuousAt.continuousWithinAt) h1 Metric.isOpen_ball`. Establish `hπks : ∀ z (t : ℂ), π (t • z) k = t * π z k` using `fun z t => by rw [hπs]; rfl`. Establish `hνs : ∀ z (t : ℂ), t ≠ 0 → π z k ≠ 0 → ν (t • z) = ν z`. Introduce `z t ht hz`. Rewrite using `[hνa, hνa, hπks, smul_smul]`.

Use `congr 1`. Clear the denominators using the available nonvanishing facts. Establish `hqs : ∀ z (t : ℂ), t ≠ 0 → π z k ≠ 0 → q (t • z) = q z`. Introduce `z t ht hz`. Use function extensionality and compare the values at `i`.

Rewrite using `[hqa, hqa, hπs]`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts. Establish `hqγ : ∀ y ∈ Metric.ball (0 : Fin D → ℂ) ρ₀, q (g (W y)) = y`.

Introduce `y hy`. Use function extensionality and compare the values at `i`. Rewrite using `[hqa, hπγ y hy, hWk, hWs]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Use `⟨ρ₀, fun y => g (W y), hρ₀, ?_, hγZ, ⟨O, q, hOo, fun z hz => hqan z hz.1.1, ?_, ?_, hqγ⟩, ?_⟩` and prove the remaining obligations. Introduce `y hy`. Conclude with `(hg _ (hyV y hy).1).comp (hWan y)`. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨⟨⟨hzA, hzU, hzh⟩, hzq⟩, hzZ⟩`. Establish `hzA' : π z k ≠ 0` using `hzA`. Establish `hc : a / π z k ≠ 0` using `div_ne_zero ha hzA'`. Establish `hνZ : ν z ∈ Z` using `by rw [hνa]; exact hZc z hzZ _ hc`. Establish `hν0 : ν z ≠ 0`.

Introduce `h0`. Use `hπks z (a / π z k)` as an intermediate fact. Rewrite `this` using `[← hνa, h0]`. Rewrite `this` using `[hπa]`. Simplify using `only [Pi.zero_apply] at this`.

Clear denominators, using `at this` for the nonvanishing conditions. Conclude with `ha this.symm`. Take `⟨w, hwV, hgw, hw⟩` from `htgt (ν z) hν0 hνZ hzU hzh`. Establish `hWq : W (q z) = π (ν z)`. Rewrite using `[hW]`.

Apply `gbap_insertNth_eq` to reduce the goal to its premises. Rewrite using `[hνa, hπks]`. Clear the denominators using the available nonvanishing facts. Introduce `i`. Rewrite using `[hνa, hπs, hqa]`.

Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Use `⟨q z, hzq, π z k / a, div_ne_zero hzA' ha, ?_⟩` and prove the remaining obligations. Simplify using `only`.

Rewrite using `[hWq, ← hw, hgw, hνa, smul_smul]`. Rewrite using `[div_mul_div_comm, mul_comm (π z k) a, div_self (mul_ne_zero ha hzA'), one_smul]`. Introduce and unpack `⟨y, hy, t, ht, rfl⟩`. Establish `hwk : π (g (W y)) k = a` using `by rw [hπγ y hy, hWk]`. Establish `hwk0 : π (g (W y)) k ≠ 0` using `by rw [hwk]; exact ha`.

Establish `hνw : ν (t • g (W y)) = g (W y)`. Rewrite using `[hνs _ _ ht hwk0, hνa, hwk, div_self ha, one_smul]`. Use `⟨⟨⟨?_, ?_⟩, ?_⟩, hZc _ (hγZ y hy) t ht⟩` and prove the remaining obligations. Use `show π (t • g (W y)) k ≠ 0`. Rewrite using `[hπks]`.

Conclude with `mul_ne_zero ht hwk0`. Simplify using `only [Set.mem_preimage, hνw]`. Conclude with `⟨(hγmem y hy).1, (hyV y hy).2⟩`. Simplify using `only [Set.mem_preimage]`. Rewrite using `[hqs _ _ ht hwk0, hqγ y hy]`.

Conclude with `hy`. Introduce `z hz t ht`. Establish `hzA : π z k ≠ 0` using `hz.1.1`. Use `⟨⟨⟨?_, ?_⟩, ?_⟩, hqs z t ht hzA⟩` and prove the remaining obligations. Use `show π (t • z) k ≠ 0`.

Rewrite using `[hπks]`. Conclude with `mul_ne_zero ht hzA`. Simplify using `only [Set.mem_preimage]`. Rewrite using `[hνs z t ht hzA]`. Conclude with `hz.1.2`.

Simplify using `only [Set.mem_preimage]`. Rewrite using `[hqs z t ht hzA]`. Conclude with `hz.2`. Simplify using `only`. Rewrite using `[hW0, ← hw₀, hgw₀]`.
-/
theorem gbap_param_of_cut {D c : ℕ} (Z : Set (Fin (D + 1 + c) → ℂ))
    (hZc : ∀ z ∈ Z, ∀ t : ℂ, t ≠ 0 → t • z ∈ Z)
    (F : Fin c → MvPolynomial (Fin (D + 1 + c)) ℂ) (h : MvPolynomial (Fin (D + 1 + c)) ℂ)
    (hZ : ∀ z, z ≠ 0 → eval z h ≠ 0 → (z ∈ Z ↔ ∀ i, eval z (F i) = 0))
    (p : Fin (D + 1 + c) → ℂ) (hp : p ∈ Z) (hp0 : p ≠ 0) (hph : eval p h ≠ 0)
    (hjac : Function.Surjective (fun v : Fin (D + 1 + c) → ℂ =>
      fun i => ∑ j, eval p (pderiv j (F i)) * v j)) :
    ∃ (ρ₀ : ℝ) (γ : (Fin D → ℂ) → Fin (D + 1 + c) → ℂ), 0 < ρ₀ ∧
      AnalyticOnNhd ℂ γ (Metric.ball 0 ρ₀) ∧ (∀ y ∈ Metric.ball (0 : Fin D → ℂ) ρ₀, γ y ∈ Z) ∧
      (∃ (O : Set (Fin (D + 1 + c) → ℂ)) (q : (Fin (D + 1 + c) → ℂ) → Fin D → ℂ), IsOpen O ∧
        AnalyticOnNhd ℂ q O ∧ O ∩ Z = coneOver (Metric.ball 0 ρ₀) γ ∧
        (∀ z ∈ O, ∀ t : ℂ, t ≠ 0 → t • z ∈ O ∧ q (t • z) = q z) ∧
        ∀ y ∈ Metric.ball 0 ρ₀, q (γ y) = y) ∧ γ 0 = p := by
  classical
  have hF0 : ∀ i, eval p (F i) = 0 := (hZ p hp0 hph).1 hp
  obtain ⟨σ, U, V, g, hU, hpU, hV, hg, hbij, hproj⟩ :=
    ReciprocityTheory.AnForm.exists_analytic_graph_chart_mvPolynomial F p hF0 hjac
  obtain ⟨π, hπ⟩ : ∃ π : (Fin (D + 1 + c) → ℂ) → Fin (D + 1) → ℂ,
      π = fun z i => z (σ (Fin.castAdd c i)) := ⟨_, rfl⟩
  have hπa : ∀ z i, π z i = z (σ (Fin.castAdd c i)) := fun z i => by rw [hπ]
  have hπs : ∀ (t : ℂ) z, π (t • z) = t • π z := fun t z => by
    funext i
    simp [hπa]
  have hπg : ∀ w ∈ V, π (g w) = w := fun w hw => by
    rw [hπ]
    exact hproj w hw
  have hπan : ∀ j z, AnalyticAt ℂ (fun z => π z j) z := fun j z => by
    rw [hπ]
    exact gbap_analyticAt_apply _ z
  have htgt : ∀ z, z ≠ 0 → z ∈ Z → z ∈ U → eval z h ≠ 0 → ∃ w ∈ V, g w = z ∧ w = π z := by
    intro z hz0 hzZ hzU hzh
    obtain ⟨w, hw, hgw⟩ := hbij.surjOn ⟨hzU, (hZ z hz0 hzh).1 hzZ⟩
    exact ⟨w, hw, hgw, by rw [← hgw, hπg w hw]⟩
  obtain ⟨w₀, hw₀V, hgw₀, hw₀⟩ := htgt p hp0 hp hpU hph
  have hπp : π p ≠ 0 := by
    intro hπ0
    have hWo : IsOpen (U ∩ {z | eval z h ≠ 0} ∩ {z | z ≠ 0}) :=
      (hU.inter (isOpen_ne_fun (MvPolynomial.continuous_eval h) continuous_const)).inter
        isOpen_ne
    have hc : ContinuousAt (fun t : ℂ => t • p) 1 :=
      (continuous_id.smul continuous_const).continuousAt
    have hev : ∀ᶠ t in nhds (1 : ℂ), t • p ∈ U ∩ {z | eval z h ≠ 0} ∩ {z | z ≠ 0} :=
      hc.preimage_mem_nhds (by rw [one_smul]; exact hWo.mem_nhds ⟨⟨hpU, hph⟩, hp0⟩)
    obtain ⟨t, ⟨⟨htU, hth⟩, htp0⟩, ht1⟩ :=
      ((hev.filter_mono nhdsWithin_le_nhds).and (self_mem_nhdsWithin (s := ({1}ᶜ : Set ℂ)))).exists
    have ht0 : t ≠ 0 := by
      rintro rfl
      exact htp0 (zero_smul ℂ p)
    obtain ⟨w, hwV, hgw, hw⟩ := htgt (t • p) htp0 (hZc p hp t ht0) htU hth
    have hw0 : w = w₀ := by
      rw [hw, hw₀, hπs, hπ0, smul_zero]
    have htp : t • p = p := by rw [← hgw, hw0, hgw₀]
    have : (t - 1) • p = 0 := by rw [sub_smul, one_smul, htp, sub_self]
    rcases smul_eq_zero.1 this with h1 | h1
    · exact ht1 (sub_eq_zero.1 h1)
    · exact hp0 h1
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hπp
  set a := π p k with ha_def
  have ha : a ≠ 0 := hk
  obtain ⟨W, hW⟩ : ∃ W : (Fin D → ℂ) → Fin (D + 1) → ℂ,
      W = fun y => Fin.insertNth k a (fun i => π p (k.succAbove i) + y i) := ⟨_, rfl⟩
  have hWk : ∀ y, W y k = a := fun y => by rw [hW]; simp
  have hWs : ∀ y i, W y (k.succAbove i) = π p (k.succAbove i) + y i := fun y i => by
    rw [hW]; simp
  have hW0 : W 0 = π p := by
    rw [hW]
    exact gbap_insertNth_eq k a _ (π p) rfl (fun i => by simp)
  have hWan : ∀ y, AnalyticAt ℂ W y := by
    intro y
    rw [hW]
    refine analyticAt_pi_iff.2 fun j => ?_
    rcases Fin.eq_self_or_eq_succAbove k j with rfl | ⟨i, rfl⟩
    · simp only [Fin.insertNth_apply_same]
      exact analyticAt_const
    · simp only [Fin.insertNth_apply_succAbove]
      exact analyticAt_const.add (gbap_analyticAt_apply i y)
  have hWc : Continuous W := continuous_iff_continuousAt.2 fun y => (hWan y).continuousAt
  have hGo : IsOpen (V ∩ g ⁻¹' {z | eval z h ≠ 0}) :=
    hg.continuousOn.isOpen_inter_preimage hV
      (isOpen_ne_fun (MvPolynomial.continuous_eval h) continuous_const)
  have h0G : (0 : Fin D → ℂ) ∈ W ⁻¹' (V ∩ g ⁻¹' {z | eval z h ≠ 0}) := by
    simp only [Set.mem_preimage, Set.mem_inter_iff, hW0, ← hw₀]
    exact ⟨hw₀V, by rw [Set.mem_ofPred_eq, hgw₀]; exact hph⟩
  obtain ⟨ρ₀, hρ₀, hball⟩ := Metric.isOpen_iff.1 (hGo.preimage hWc) 0 h0G
  have hyV : ∀ y ∈ Metric.ball (0 : Fin D → ℂ) ρ₀, W y ∈ V ∧ eval (g (W y)) h ≠ 0 :=
    fun y hy => hball hy
  have hγmem : ∀ y ∈ Metric.ball (0 : Fin D → ℂ) ρ₀,
      g (W y) ∈ U ∧ ∀ i, eval (g (W y)) (F i) = 0 := fun y hy => hbij.mapsTo (hyV y hy).1
  have hπγ : ∀ y ∈ Metric.ball (0 : Fin D → ℂ) ρ₀, π (g (W y)) = W y := fun y hy =>
    hπg _ (hyV y hy).1
  have hγ0 : ∀ y ∈ Metric.ball (0 : Fin D → ℂ) ρ₀, g (W y) ≠ 0 := by
    intro y hy h0
    have := congrFun (hπγ y hy) k
    rw [h0, hWk, hπa] at this
    exact ha (by simpa using this.symm)
  have hγZ : ∀ y ∈ Metric.ball (0 : Fin D → ℂ) ρ₀, g (W y) ∈ Z := fun y hy =>
    (hZ _ (hγ0 y hy) (hyV y hy).2).2 (hγmem y hy).2
  obtain ⟨q, hq⟩ : ∃ q : (Fin (D + 1 + c) → ℂ) → Fin D → ℂ,
      q = fun z i => π z (k.succAbove i) * a / π z k - π p (k.succAbove i) := ⟨_, rfl⟩
  have hqa : ∀ z i, q z i = π z (k.succAbove i) * a / π z k - π p (k.succAbove i) :=
    fun z i => by rw [hq]
  obtain ⟨ν, hν⟩ : ∃ ν : (Fin (D + 1 + c) → ℂ) → Fin (D + 1 + c) → ℂ,
      ν = fun z => (a / π z k) • z := ⟨_, rfl⟩
  have hνa : ∀ z, ν z = (a / π z k) • z := fun z => by rw [hν]
  set A : Set (Fin (D + 1 + c) → ℂ) := {z | π z k ≠ 0} with hA
  have hAo : IsOpen A :=
    isOpen_ne_fun (continuous_iff_continuousAt.2 fun z => (hπan k z).continuousAt) continuous_const
  have hqan : ∀ z ∈ A, AnalyticAt ℂ q z := by
    intro z hz
    rw [hq]
    refine analyticAt_pi_iff.2 fun i => ?_
    exact (((hπan _ z).mul analyticAt_const).div (hπan k z) hz).sub analyticAt_const
  have hνan : ∀ z ∈ A, AnalyticAt ℂ ν z := by
    intro z hz
    rw [hν]
    refine analyticAt_pi_iff.2 fun j => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    exact (analyticAt_const.div (hπan k z) hz).mul (gbap_analyticAt_apply j z)
  set O : Set (Fin (D + 1 + c) → ℂ) :=
    A ∩ ν ⁻¹' (U ∩ {z | eval z h ≠ 0}) ∩ q ⁻¹' Metric.ball 0 ρ₀ with hO
  have hOo : IsOpen O := by
    have h1 : IsOpen (A ∩ ν ⁻¹' (U ∩ {z | eval z h ≠ 0})) :=
      ContinuousOn.isOpen_inter_preimage (show ContinuousOn ν A from fun z hz => (hνan z hz).continuousAt.continuousWithinAt)
        hAo (hU.inter (isOpen_ne_fun (MvPolynomial.continuous_eval h) continuous_const))
    exact ContinuousOn.isOpen_inter_preimage (show ContinuousOn q (A ∩ ν ⁻¹' (U ∩ {z | eval z h ≠ 0})) from
      fun z hz => (hqan z hz.1).continuousAt.continuousWithinAt) h1
      Metric.isOpen_ball
  have hπks : ∀ z (t : ℂ), π (t • z) k = t * π z k := fun z t => by rw [hπs]; rfl
  have hνs : ∀ z (t : ℂ), t ≠ 0 → π z k ≠ 0 → ν (t • z) = ν z := by
    intro z t ht hz
    rw [hνa, hνa, hπks, smul_smul]
    congr 1
    field_simp
  have hqs : ∀ z (t : ℂ), t ≠ 0 → π z k ≠ 0 → q (t • z) = q z := by
    intro z t ht hz
    funext i
    rw [hqa, hqa, hπs]
    simp only [Pi.smul_apply, smul_eq_mul]
    congr 1
    field_simp
  have hqγ : ∀ y ∈ Metric.ball (0 : Fin D → ℂ) ρ₀, q (g (W y)) = y := by
    intro y hy
    funext i
    rw [hqa, hπγ y hy, hWk, hWs]
    field_simp
    ring
  refine ⟨ρ₀, fun y => g (W y), hρ₀, ?_, hγZ, ⟨O, q, hOo, fun z hz => hqan z hz.1.1, ?_, ?_, hqγ⟩, ?_⟩
  · intro y hy
    exact (hg _ (hyV y hy).1).comp (hWan y)
  · ext z
    constructor
    · rintro ⟨⟨⟨hzA, hzU, hzh⟩, hzq⟩, hzZ⟩
      have hzA' : π z k ≠ 0 := hzA
      have hc : a / π z k ≠ 0 := div_ne_zero ha hzA'
      have hνZ : ν z ∈ Z := by rw [hνa]; exact hZc z hzZ _ hc
      have hν0 : ν z ≠ 0 := by
        intro h0
        have := hπks z (a / π z k)
        rw [← hνa, h0] at this
        rw [hπa] at this
        simp only [Pi.zero_apply] at this
        field_simp at this
        exact ha this.symm
      obtain ⟨w, hwV, hgw, hw⟩ := htgt (ν z) hν0 hνZ hzU hzh
      have hWq : W (q z) = π (ν z) := by
        rw [hW]
        apply gbap_insertNth_eq
        · rw [hνa, hπks]
          field_simp
        · intro i
          rw [hνa, hπs, hqa]
          simp only [Pi.smul_apply, smul_eq_mul]
          field_simp
          ring
      refine ⟨q z, hzq, π z k / a, div_ne_zero hzA' ha, ?_⟩
      simp only
      rw [hWq, ← hw, hgw, hνa, smul_smul]
      rw [div_mul_div_comm, mul_comm (π z k) a, div_self (mul_ne_zero ha hzA'), one_smul]
    · rintro ⟨y, hy, t, ht, rfl⟩
      have hwk : π (g (W y)) k = a := by rw [hπγ y hy, hWk]
      have hwk0 : π (g (W y)) k ≠ 0 := by rw [hwk]; exact ha
      have hνw : ν (t • g (W y)) = g (W y) := by
        rw [hνs _ _ ht hwk0, hνa, hwk, div_self ha, one_smul]
      refine ⟨⟨⟨?_, ?_⟩, ?_⟩, hZc _ (hγZ y hy) t ht⟩
      · show π (t • g (W y)) k ≠ 0
        rw [hπks]
        exact mul_ne_zero ht hwk0
      · simp only [Set.mem_preimage, hνw]
        exact ⟨(hγmem y hy).1, (hyV y hy).2⟩
      · simp only [Set.mem_preimage]
        rw [hqs _ _ ht hwk0, hqγ y hy]
        exact hy
  · intro z hz t ht
    have hzA : π z k ≠ 0 := hz.1.1
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, hqs z t ht hzA⟩
    · show π (t • z) k ≠ 0
      rw [hπks]
      exact mul_ne_zero ht hzA
    · simp only [Set.mem_preimage]
      rw [hνs z t ht hzA]
      exact hz.1.2
    · simp only [Set.mem_preimage]
      rw [hqs z t ht hzA]
      exact hz.2
  · simp only
    rw [hW0, ← hw₀, hgw₀]

section Pts

variable {Ω : Type} [Field Ω] [CharZero Ω]

/- English proof (translation)
Rewrite using `[eval_eq, eval_eq, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun d hd => ?_` and prove the remaining obligations. Establish `hdeg : d.degree = n`. Assume the negation of the conclusion as `h`. Conclude with `(mem_support_iff.mp hd) (hφ.coeff_eq_zero h)`.

Simplify using `only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]`. Establish `hs : d.degree = ∑ i ∈ d.support, d i` using `rfl`. Rewrite using `[← hdeg, hs]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gbap_eval_smul {ι : Type*} {φ : MvPolynomial ι ℂ} {n : ℕ}
    (hφ : φ.IsHomogeneous n) (c : ℂ) (z : ι → ℂ) :
    eval (c • z) φ = c ^ n * eval z φ := by
  classical
  rw [eval_eq, eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : d.degree = n := by
    by_contra h
    exact (mem_support_iff.mp hd) (hφ.coeff_eq_zero h)
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]
  have hs : d.degree = ∑ i ∈ d.support, d i := rfl
  rw [← hdeg, hs]
  ring

/- English proof (translation)
Use `⟨smul_ne_zero hc hz.1, fun f hf => ?_⟩` and prove the remaining obligations. Establish `hH` using `coordIdeal_isHomogIdeal ℤ x`. Rewrite using `[← sum_homogeneousComponent f, map_sum, map_sum]`. Use `Finset.sum_eq_zero fun d _ => ?_` and prove the remaining obligations. Rewrite using `[gbap_eval_smul ((homogeneousComponent_isHomogeneous d f).map _), hz.2 _ (hH f hf d), mul_zero]`.
-/
theorem gbap_smul_mem_pts {J : Type} [Fintype J] (x : J → Ω) {z : J → ℂ}
    (hz : z ∈ pts (coordIdeal ℤ x)) {c : ℂ} (hc : c ≠ 0) : c • z ∈ pts (coordIdeal ℤ x) := by
  refine ⟨smul_ne_zero hc hz.1, fun f hf => ?_⟩
  have hH := coordIdeal_isHomogIdeal ℤ x
  rw [← sum_homogeneousComponent f, map_sum, map_sum]
  refine Finset.sum_eq_zero fun d _ => ?_
  rw [gbap_eval_smul ((homogeneousComponent_isHomogeneous d f).map _),
    hz.2 _ (hH f hf d), mul_zero]

/- English proof (translation)
Establish `hZ : IsClosed {z : J → ℂ | ∀ f ∈ P, eval z (map (Int.castRingHom ℂ) f) = 0}`. Establish `: {z : J → ℂ | ∀ f ∈ P, eval z (map (Int.castRingHom ℂ) f) = 0} = ⋂ f ∈ P, {z : J → ℂ | eval z (map (Int.castRingHom ℂ) f) = 0}`. Use extensionality with `z`. Simplify using the standard rewrite rules. Rewrite using `[this]`.

Conclude with `isClosed_biInter fun f _ => isClosed_eq (MvPolynomial.continuous_eval _) continuous_const`. Establish `: pts P ∩ Metric.sphere (0 : J → ℂ) 1 = {z : J → ℂ | ∀ f ∈ P, eval z (map (Int.castRingHom ℂ) f) = 0} ∩ Metric.sphere 0 1`. Use extensionality with `z`. Simplify using `only [pts, conePts, Set.mem_inter_iff, Set.mem_ofPred_eq, mem_sphere_zero_iff_norm]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨⟨_, h⟩, h1⟩`. Conclude with `⟨h, h1⟩`. Introduce and unpack `⟨h, h1⟩`. Use `⟨⟨fun h0 => ?_, h⟩, h1⟩` and prove the remaining obligations. Rewrite `h1` using `[h0, norm_zero]`.

Conclude with `zero_ne_one h1`. Rewrite using `[this]`. Conclude with `(isCompact_sphere 0 1).inter_left hZ`.
-/
theorem gbap_isCompact_pts_sphere {J : Type} [Fintype J] (P : Ideal (MvPolynomial J ℤ)) :
    IsCompact (pts P ∩ Metric.sphere (0 : J → ℂ) 1) := by
  have hZ : IsClosed {z : J → ℂ | ∀ f ∈ P, eval z (map (Int.castRingHom ℂ) f) = 0} := by
    have : {z : J → ℂ | ∀ f ∈ P, eval z (map (Int.castRingHom ℂ) f) = 0} =
        ⋂ f ∈ P, {z : J → ℂ | eval z (map (Int.castRingHom ℂ) f) = 0} := by
      ext z
      simp
    rw [this]
    exact isClosed_biInter fun f _ => isClosed_eq (MvPolynomial.continuous_eval _) continuous_const
  have : pts P ∩ Metric.sphere (0 : J → ℂ) 1 =
      {z : J → ℂ | ∀ f ∈ P, eval z (map (Int.castRingHom ℂ) f) = 0} ∩ Metric.sphere 0 1 := by
    ext z
    simp only [pts, conePts, Set.mem_inter_iff, Set.mem_ofPred_eq, mem_sphere_zero_iff_norm]
    constructor
    · rintro ⟨⟨_, h⟩, h1⟩
      exact ⟨h, h1⟩
    · rintro ⟨h, h1⟩
      refine ⟨⟨fun h0 => ?_, h⟩, h1⟩
      rw [h0, norm_zero] at h1
      exact zero_ne_one h1
  rw [this]
  exact (isCompact_sphere 0 1).inter_left hZ

end Pts

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
