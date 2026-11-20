import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SndFDerivAddSndFDerivIEqZeroOfHarmonicAtLine
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KaRuleK
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

namespace GlobalTheory

/- English proof (translation)
Use `choose! φ hφA hφ using h`. Establish `hinj : Set.InjOn φ A` using `fun f hf k hk hfk => by rw [hφ f hf, hφ k hk, hfk]`. Establish `himg : A.image φ = A`. Use `Finset.eq_of_subset_of_card_le (fun y hy => ?_) ?_` and prove the remaining obligations. Take `⟨f, hf, rfl⟩` from `Finset.mem_image.1 hy`.

Conclude with `hφA f hf`. Rewrite using `[Finset.card_image_of_injOn hinj]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem prod_comp_eq_of_finite_family {S : Type} (A : Finset (S → ℂ)) (a : S → S)
    (h : ∀ f ∈ A, ∃ f' ∈ A, f = f' ∘ a) (w : ℂ) (x : S) :
    ∏ f ∈ A, (w - f (a x)) = ∏ f ∈ A, (w - f x) := by
  classical
  choose! φ hφA hφ using h
  have hinj : Set.InjOn φ A := fun f hf k hk hfk => by rw [hφ f hf, hφ k hk, hfk]
  have himg : A.image φ = A := by
    refine Finset.eq_of_subset_of_card_le (fun y hy => ?_) ?_
    · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hy
      exact hφA f hf
    · rw [Finset.card_image_of_injOn hinj]
  calc ∏ f ∈ A, (w - f (a x)) = ∏ f ∈ A.image φ, (w - f (a x)) := by rw [himg]
    _ = ∏ f ∈ A, (w - φ f (a x)) := Finset.prod_image hinj
    _ = ∏ f ∈ A, (w - f x) :=
        Finset.prod_congr rfl (fun f hf => congrArg (w - ·) (congrFun (hφ f hf) x).symm)

/- English proof (translation)
Proceed by induction on `A using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert j B hj ih`. Simplify using `only [Finset.prod_insert hj]`. Conclude with `(h j (Finset.mem_insert_self j B)).mul (ih fun k hk => h k (Finset.mem_insert_of_mem hk))`.
-/
theorem differentiableOn_finite_prod {K E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {s : Set E} (A : Finset K) {f : K → E → ℂ} (h : ∀ i ∈ A, DifferentiableOn ℂ (f i) s) :
    DifferentiableOn ℂ (fun x => ∏ i ∈ A, f i x) s := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | insert j B hj ih =>
    simp only [Finset.prod_insert hj]
    exact (h j (Finset.mem_insert_self j B)).mul (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

/- English proof (translation)
Introduce `hPh g I _ F hg hF h i`. Establish `: Fintype I` using `Fintype.ofFinite I`. Set `S` to `ReciprocityTheory.PTheta.SiegelH (Fin g)`. Establish `hmem : ∀ τ ∈ S, τ.IsSymm ∧ (τ.map Complex.im).PosDef` using `fun τ hτ => hτ`. Set `G : I → (S → ℂ)` to `fun j τ => F j τ`.

Set `A : Finset (S → ℂ)` to `Finset.univ.image G`. Establish `hGA : ∀ j, G j ∈ A` using `fun j => Finset.mem_image_of_mem _ (Finset.mem_univ _)`. Establish `hA : ∀ f ∈ A, ∃ j, G j = f` using `fun f hf => by simpa [A] using hf`. Establish `: Nonempty I` using `⟨i⟩`. Use `choose! rep hrep using hA`.

Establish `heval : ∀ f ∈ A, ∀ τ (hτ : τ ∈ S), F (rep f) τ = f ⟨τ, hτ⟩` using `fun f hf τ hτ => congrFun (hrep f hf) ⟨τ, hτ⟩`. Establish `hsym : ∀ τ ∈ S, Key.phSym τ = τ`. Introduce `τ hτ`. Establish `ht : Matrix.transpose τ = τ` using `(hmem τ hτ).1.eq`. Simplify using `only [Key.phSym, ht]`.

Use extensionality with `p q`. Simplify using `only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hholo : ∀ w : ℂ, Key.IsHoloSiegel g (fun τ => ∏ f ∈ A, (w - F (rep f) τ))`. Introduce `w`.

Conclude with `differentiableOn_finite_prod A (f := fun f x => w - F (rep f) (Key.phSym (Matrix.of x))) (fun f _ => (differentiableOn_const w).sub (hF (rep f)))`. Establish `hinv : ∀ w : ℂ, Key.IsSpInvariant g (fun τ => ∏ f ∈ A, (w - F (rep f) τ))`. Introduce `w gm hgm τ hτ`. Use `choose J hJ using h gm hgm`. Set `act : S → S` to `fun σ => ⟨Key.Chi.spAct gm σ, Key.Chi.spAct_mem hgm σ.2⟩`.

Establish `hfam : ∀ f ∈ A, ∃ f' ∈ A, f = f' ∘ act`. Introduce `f hf`. Use `⟨G (J (rep f)), hGA _, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `σ`. Conclude with `(congrFun (hrep f hf) σ).symm.trans (hJ (rep f) σ.1 σ.2)`.

Establish `hstep` using `prod_comp_eq_of_finite_family A act hfam w ⟨τ, hτ⟩`. Establish `hact : Key.phAct gm τ = Key.Chi.spAct gm τ` using `rfl`. Use `show ∏ f ∈ A, (w - F (rep f) (Key.phAct gm τ)) = ∏ f ∈ A, (w - F (rep f) τ)`. Combine the equalities or inequalities in the displayed calculation. Distinguish the cases in `hne : S.Nonempty`.

Use `swap`. Conclude with `⟨0, fun τ hτ => (hne ⟨τ, hτ⟩).elim⟩`. Take `⟨τ0, hτ0⟩` from `hne`. Use `⟨F i τ0, fun τ hτ => ?_⟩` and prove the remaining obligations. Establish `hval : ∀ τ ∈ S, F i τ ∈ ((A.image (fun f => F (rep f) τ0) : Finset ℂ) : Set ℂ)`.

Introduce `τ hτ`. Take `⟨c, hc⟩` from `hPh g hg _ (hholo (F i τ)) (hinv (F i τ))`. Establish `h0 : ∏ f ∈ A, (F i τ - F (rep f) τ) = 0`. Apply `Finset.prod_eq_zero (hGA i)` to reduce the goal to its premises. Rewrite using `[heval _ (hGA i) τ hτ]`.

Conclude with `sub_self _`. Establish `h1 : ∏ f ∈ A, (F i τ - F (rep f) τ0) = 0` using `(hc τ0 hτ0).trans ((hc τ hτ).symm.trans h0)`. Take `⟨f, hf, hz⟩` from `Finset.prod_eq_zero_iff.1 h1`. Conclude with `Finset.mem_coe.2 (Finset.mem_image.2 ⟨f, hf, (sub_eq_zero.1 hz).symm⟩)`. Establish `hcont : ContinuousOn (F i) S`.

Establish `hc0` using `(hF i).continuousOn`. Use `(hc0.mono (fun σ hσ => ?_)).congr (fun σ hσ => ?_)` and prove the remaining obligations. Use `show Key.phSym σ ∈ S`. Rewrite using `[hsym σ hσ]`. Conclude with `hσ`.

Use `show F i σ = F i (Key.phSym σ)`. Rewrite using `[hsym σ hσ]`. Establish `hconv : Convex ℝ S`. Introduce `x hx y hy s t hs ht hst`. Take `⟨hx1, hx2⟩` from `hmem x hx`.

Take `⟨hy1, hy2⟩` from `hmem y hy`. Express the relevant statement in the definitionally equal form `Matrix.IsSymm (s • x + t • y) ∧ ((s • x + t • y).map Complex.im).PosDef`. Use `⟨(hx1.smul s).add (hy1.smul t), ?_⟩` and prove the remaining obligations. Establish `hm : (s • x + t • y).map Complex.im = s • x.map Complex.im + t • y.map Complex.im`. Use extensionality with `p q`.

Simplify using the standard rewrite rules. Rewrite using `[hm]`. Break down `hs.lt_or_eq with hs' | hs'` into its components or cases. Conclude with `(hx2.smul hs').add_posSemidef (hy2.posSemidef.smul ht)`. Substitute `hs'` using the available equality.

Rewrite `hst` using `[zero_add]`. Substitute `hst` using the available equality. Simplify using `using hy2`. Conclude with `hconv.isPreconnected.constant_of_mapsTo DiscreteTopology.isDiscrete hcont (fun σ hσ => hval σ hσ) hτ hτ0`.
-/
theorem const_of_finite_family_spAct :
    Key.PhHoloStatement → ∀ (g : ℕ) (I : Type) [Finite I] (F : I → Matrix (Fin g) (Fin g) ℂ → ℂ), 2 ≤ g → (∀ i, Key.IsHoloSiegel g (F i)) → (∀ sp ∈ Matrix.symplecticGroup (Fin g) ℤ, ∀ i, ∃ j, ∀ τ ∈ ReciprocityTheory.PTheta.SiegelH (Fin g), F i τ = F j (Key.Chi.spAct sp τ)) → ∀ i, ∃ c, ∀ τ ∈ ReciprocityTheory.PTheta.SiegelH (Fin g), F i τ = c := by
  intro hPh g I _ F hg hF h i
  classical
  have : Fintype I := Fintype.ofFinite I
  let S := ReciprocityTheory.PTheta.SiegelH (Fin g)
  have hmem : ∀ τ ∈ S, τ.IsSymm ∧ (τ.map Complex.im).PosDef := fun τ hτ => hτ
  let G : I → (S → ℂ) := fun j τ => F j τ
  let A : Finset (S → ℂ) := Finset.univ.image G
  have hGA : ∀ j, G j ∈ A := fun j => Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have hA : ∀ f ∈ A, ∃ j, G j = f := fun f hf => by simpa [A] using hf
  have : Nonempty I := ⟨i⟩
  choose! rep hrep using hA
  have heval : ∀ f ∈ A, ∀ τ (hτ : τ ∈ S), F (rep f) τ = f ⟨τ, hτ⟩ :=
    fun f hf τ hτ => congrFun (hrep f hf) ⟨τ, hτ⟩
  have hsym : ∀ τ ∈ S, Key.phSym τ = τ := by
    intro τ hτ
    have ht : Matrix.transpose τ = τ := (hmem τ hτ).1.eq
    simp only [Key.phSym, ht]
    ext p q
    simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
    ring
  have hholo : ∀ w : ℂ, Key.IsHoloSiegel g (fun τ => ∏ f ∈ A, (w - F (rep f) τ)) := by
    intro w
    exact differentiableOn_finite_prod A
      (f := fun f x => w - F (rep f) (Key.phSym (Matrix.of x)))
      (fun f _ => (differentiableOn_const w).sub (hF (rep f)))
  have hinv : ∀ w : ℂ, Key.IsSpInvariant g (fun τ => ∏ f ∈ A, (w - F (rep f) τ)) := by
    intro w gm hgm τ hτ
    choose J hJ using h gm hgm
    let act : S → S := fun σ => ⟨Key.Chi.spAct gm σ, Key.Chi.spAct_mem hgm σ.2⟩
    have hfam : ∀ f ∈ A, ∃ f' ∈ A, f = f' ∘ act := by
      intro f hf
      refine ⟨G (J (rep f)), hGA _, ?_⟩
      funext σ
      exact (congrFun (hrep f hf) σ).symm.trans (hJ (rep f) σ.1 σ.2)
    have hstep := prod_comp_eq_of_finite_family A act hfam w ⟨τ, hτ⟩
    have hact : Key.phAct gm τ = Key.Chi.spAct gm τ := rfl
    show ∏ f ∈ A, (w - F (rep f) (Key.phAct gm τ)) = ∏ f ∈ A, (w - F (rep f) τ)
    calc ∏ f ∈ A, (w - F (rep f) (Key.phAct gm τ)) = ∏ f ∈ A, (w - f (act ⟨τ, hτ⟩)) :=
          Finset.prod_congr rfl (fun f hf => by rw [hact, heval f hf _ (Key.Chi.spAct_mem hgm hτ)])
      _ = ∏ f ∈ A, (w - f ⟨τ, hτ⟩) := hstep
      _ = ∏ f ∈ A, (w - F (rep f) τ) :=
          Finset.prod_congr rfl (fun f hf => by rw [heval f hf τ hτ])
  by_cases hne : S.Nonempty
  swap
  · exact ⟨0, fun τ hτ => (hne ⟨τ, hτ⟩).elim⟩
  obtain ⟨τ0, hτ0⟩ := hne
  refine ⟨F i τ0, fun τ hτ => ?_⟩
  have hval : ∀ τ ∈ S, F i τ ∈ ((A.image (fun f => F (rep f) τ0) : Finset ℂ) : Set ℂ) := by
    intro τ hτ
    obtain ⟨c, hc⟩ := hPh g hg _ (hholo (F i τ)) (hinv (F i τ))
    have h0 : ∏ f ∈ A, (F i τ - F (rep f) τ) = 0 := by
      apply Finset.prod_eq_zero (hGA i)
      rw [heval _ (hGA i) τ hτ]
      exact sub_self _
    have h1 : ∏ f ∈ A, (F i τ - F (rep f) τ0) = 0 := (hc τ0 hτ0).trans ((hc τ hτ).symm.trans h0)
    obtain ⟨f, hf, hz⟩ := Finset.prod_eq_zero_iff.1 h1
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨f, hf, (sub_eq_zero.1 hz).symm⟩)
  have hcont : ContinuousOn (F i) S := by
    have hc0 := (hF i).continuousOn
    refine (hc0.mono (fun σ hσ => ?_)).congr (fun σ hσ => ?_)
    · show Key.phSym σ ∈ S
      rw [hsym σ hσ]
      exact hσ
    · show F i σ = F i (Key.phSym σ)
      rw [hsym σ hσ]
  have hconv : Convex ℝ S := by
    intro x hx y hy s t hs ht hst
    obtain ⟨hx1, hx2⟩ := hmem x hx
    obtain ⟨hy1, hy2⟩ := hmem y hy
    change Matrix.IsSymm (s • x + t • y) ∧ ((s • x + t • y).map Complex.im).PosDef
    refine ⟨(hx1.smul s).add (hy1.smul t), ?_⟩
    have hm : (s • x + t • y).map Complex.im = s • x.map Complex.im + t • y.map Complex.im := by
      ext p q
      simp
    rw [hm]
    rcases hs.lt_or_eq with hs' | hs'
    · exact (hx2.smul hs').add_posSemidef (hy2.posSemidef.smul ht)
    · subst hs'
      rw [zero_add] at hst
      subst hst
      simpa using hy2
  exact hconv.isPreconnected.constant_of_mapsTo DiscreteTopology.isDiscrete hcont
    (fun σ hσ => hval σ hσ) hτ hτ0

end GlobalTheory
