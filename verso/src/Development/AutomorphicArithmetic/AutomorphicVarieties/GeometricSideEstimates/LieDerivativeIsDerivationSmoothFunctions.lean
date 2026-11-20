import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.ThStmt
open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep

section

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [Pi.mul_apply, chart]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
private theorem chart_prod (f f' : GA E a → ℂ) (g : GA E a) :
    chart (f * f') g = chart f g * chart f' g := by
  funext x
  simp only [Pi.mul_apply, chart]
  split_ifs <;> simp

/- English proof (translation)
Introduce `g`. Rewrite using `[chart_prod]`. Conclude with `(h g).mul (h' g)`.
-/
private theorem sm_prod_mem {f f' : GA E a → ℂ} (h : f ∈ Sm E a) (h' : f' ∈ Sm E a) : f * f' ∈ Sm E a := by
  intro g
  rw [chart_prod]
  exact (h g).mul (h' g)

/- English proof (translation)
Use function extensionality and compare the values at `g`. Establish `v : ∀ u : GA E a → ℂ, chart u g (oneL E a) = u g` using `fun u => by`. Simplify using `using chart_val u g 1`. Simplify using `only [lieD, Pi.add_apply, Pi.mul_apply]`. Rewrite using `[chart_prod, fderiv_mul (differentiableAt_chart h g) (differentiableAt_chart h' g), v, v]`.

Simplify using `[mul_comm]`.
-/
private theorem leibniz (X : Lie E a) {f f' : GA E a → ℂ} (h : f ∈ Sm E a) (h' : f' ∈ Sm E a) :
    lieD X (f * f') = f * lieD X f' + lieD X f * f' := by
  funext g
  have v : ∀ u : GA E a → ℂ, chart u g (oneL E a) = u g := fun u => by
    simpa using chart_val u g 1
  simp only [lieD, Pi.add_apply, Pi.mul_apply]
  rw [chart_prod, fderiv_mul (differentiableAt_chart h g) (differentiableAt_chart h' g), v, v]
  simp [mul_comm]

/- English proof (translation)
Unfold `chart`. Rewrite using `[dif_pos (show IsUnit (Matrix.of x) from hx)]`. Both sides reduce to the same expression.
-/
private theorem const_ev (c : ℂ) (g : GA E a) {x : Lie E a} (hx : x ∈ invSet E a) :
    chart (algebraMap ℂ (GA E a → ℂ) c) g x = c := by
  unfold chart
  rw [dif_pos (show IsUnit (Matrix.of x) from hx)]
  rfl

/- English proof (translation)
Introduce `g` and use `contDiffOn_const.congr fun _ hx => const_ev c g hx`.
-/
private theorem const_mem (c : ℂ) : algebraMap ℂ (GA E a → ℂ) c ∈ Sm E a := fun g =>
  contDiffOn_const.congr fun _ hx => const_ev c g hx

/- English proof (translation)
Use function extensionality and compare the values at `g`. Establish `e : chart (algebraMap ℂ (GA E a → ℂ) c) g =ᶠ[nhds (oneL E a)] fun _ => c`. Establish `h1 : oneL E a ∈ invSet E a` using `isUnit_one`. Use `filter_upwards [isOpen_invSet.mem_nhds h1] with x hx using const_ev c g hx`. Rewrite using `[lieD, e.fderiv_eq]`.

Simplify using the standard rewrite rules.
-/
private theorem lie_const (X : Lie E a) (c : ℂ) : lieD X (algebraMap ℂ (GA E a → ℂ) c) = 0 := by
  funext g
  have e : chart (algebraMap ℂ (GA E a → ℂ) c) g =ᶠ[nhds (oneL E a)] fun _ => c := by
    have h1 : oneL E a ∈ invSet E a := isUnit_one
    filter_upwards [isOpen_invSet.mem_nhds h1] with x hx using const_ev c g hx
  rw [lieD, e.fderiv_eq]
  simp

end

/- English proof (translation)
Introduce `E _ _ _ a S hS`. Establish `key : ∀ f ∈ Algebra.adjoin ℂ S, (∃ C : ℝ, ∀ g, ‖f g‖ ≤ C) ∧ f ∈ Sm E a ∧ ∀ X : Lie E a, lieD X f ∈ Algebra.adjoin ℂ S`. Introduce `f hf`. Proceed by induction on `hf using Algebra.adjoin_induction with`. Consider the case `mem f hf`.

Take `⟨hb, φ, rfl, hX⟩` from `hS f hf`. Conclude with `⟨hb, φ.2, hX⟩`. Consider the case `algebraMap c`. Conclude with `⟨⟨‖c‖, fun g => by simp⟩, const_mem c, fun X => by rw [lie_const]; exact zero_mem _⟩`. Consider the case `add f f' _ _ h h'`.

Take `⟨⟨C, hC⟩, hs, hX⟩` from `h`. Take `⟨⟨C', hC'⟩, hs', hX'⟩` from `h'`. Use `⟨⟨C + C', fun g => (norm_add_le _ _).trans (add_le_add (hC g) (hC' g))⟩, add_mem hs hs', fun X => ?_⟩` and prove the remaining obligations. Establish `e : lieD X (f + f') = lieD X f + lieD X f'` using `congrArg Subtype.val ((lie E a X).map_add (⟨f, hs⟩ : Sm E a) (⟨f', hs'⟩ : Sm E a))`. Rewrite using `[e]`.

Conclude with `add_mem (hX X) (hX' X)`. Consider the case `mul f f' hf hf' h h'`. Take `⟨⟨C, hC⟩, hs, hX⟩` from `h`. Take `⟨⟨C', hC'⟩, hs', hX'⟩` from `h'`. Use `⟨⟨C * C', fun g => (norm_mul_le _ _).trans (mul_le_mul (hC g) (hC' g) (norm_nonneg _) ((norm_nonneg _).trans (hC g)))⟩, sm_prod_mem hs hs', fun X => ?_⟩` and prove the remaining obligations.

Rewrite using `[leibniz X hs hs']`. Conclude with `add_mem (mul_mem hf (hX' X)) (mul_mem (hX X) hf')`. Establish `main : ∀ ψ : Sm E a, (∀ X, (lie E a X ψ).1 ∈ Algebra.adjoin ℂ S) → BddDer ψ`. Introduce `ψ hψ`. Establish `h : ∀ (l : List (Lie E a)) (X : Lie E a), (((X :: l).map (lie E a)).prod ψ).1 ∈ Algebra.adjoin ℂ S`.

Introduce `l`. Proceed by induction on `l with`. Consider the case `nil => intro X`. Simplify using `using hψ X`. Consider the case `cons Y l ih`.

Introduce `X`. Rewrite using `[List.map_cons, List.prod_cons]`. Conclude with `(key _ (ih Y)).2.2 X`. Conclude with `fun X l => (key _ (h l X)).1`. Conclude with `⟨fun f hf => ⟨⟨f, (key f hf).2.1⟩, rfl, main _ (key f hf).2.2⟩, main⟩`.
-/
theorem UpperTheory.lieDerivative_isDerivation_smoothFunctions :
    BddAlg := by
  intro E _ _ _ a S hS
  have key : ∀ f ∈ Algebra.adjoin ℂ S, (∃ C : ℝ, ∀ g, ‖f g‖ ≤ C) ∧ f ∈ Sm E a ∧
      ∀ X : Lie E a, lieD X f ∈ Algebra.adjoin ℂ S := by
    intro f hf
    induction hf using Algebra.adjoin_induction with
    | mem f hf =>
      obtain ⟨hb, φ, rfl, hX⟩ := hS f hf
      exact ⟨hb, φ.2, hX⟩
    | algebraMap c =>
      exact ⟨⟨‖c‖, fun g => by simp⟩, const_mem c, fun X => by rw [lie_const]; exact zero_mem _⟩
    | add f f' _ _ h h' =>
      obtain ⟨⟨C, hC⟩, hs, hX⟩ := h
      obtain ⟨⟨C', hC'⟩, hs', hX'⟩ := h'
      refine ⟨⟨C + C', fun g => (norm_add_le _ _).trans (add_le_add (hC g) (hC' g))⟩, add_mem hs hs', fun X => ?_⟩
      have e : lieD X (f + f') = lieD X f + lieD X f' :=
        congrArg Subtype.val ((lie E a X).map_add (⟨f, hs⟩ : Sm E a) (⟨f', hs'⟩ : Sm E a))
      rw [e]
      exact add_mem (hX X) (hX' X)
    | mul f f' hf hf' h h' =>
      obtain ⟨⟨C, hC⟩, hs, hX⟩ := h
      obtain ⟨⟨C', hC'⟩, hs', hX'⟩ := h'
      refine ⟨⟨C * C', fun g => (norm_mul_le _ _).trans
        (mul_le_mul (hC g) (hC' g) (norm_nonneg _) ((norm_nonneg _).trans (hC g)))⟩, sm_prod_mem hs hs', fun X => ?_⟩
      rw [leibniz X hs hs']
      exact add_mem (mul_mem hf (hX' X)) (mul_mem (hX X) hf')
  have main : ∀ ψ : Sm E a, (∀ X, (lie E a X ψ).1 ∈ Algebra.adjoin ℂ S) → BddDer ψ := by
    intro ψ hψ
    have h : ∀ (l : List (Lie E a)) (X : Lie E a),
        (((X :: l).map (lie E a)).prod ψ).1 ∈ Algebra.adjoin ℂ S := by
      intro l
      induction l with
      | nil => intro X; simpa using hψ X
      | cons Y l ih =>
        intro X
        rw [List.map_cons, List.prod_cons]
        exact (key _ (ih Y)).2.2 X
    exact fun X l => (key _ (h l X)).1
  exact ⟨fun f hf => ⟨⟨f, (key f hf).2.1⟩, rfl, main _ (key f hf).2.2⟩, main⟩
