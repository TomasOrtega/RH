import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeilChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatMatTransposeMulGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LengthLetters
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelPresentingDivisor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ScaleZeroComp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNormalModelOverProjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorBundleResult

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.HtGen GlobalTheory.TrivFlag GlobalTheory.WholeFlag GlobalTheory.HalfGeo
open Formalism.MainNotions.DIV.Cons (intO)
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EqHalf.LineCover

section Flags

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)} {F : Type} [Field F] [NumberField F] {ε : F ≃+* c.F}
  (C : GlobalTheory.ShFam.FlagCpt Z ε)

/- English proof (translation)
Establish `hp : ∏ x : Letter Dw, dg C y x.1 x.2 ^ expo Dw (Finsupp.single (a, R, .inr k) 1) x = dg C y x₀.1 x₀.2`. Rewrite using `[Finset.prod_eq_single x₀ (fun x _ hx => by`. Rewrite using `[expo_single, if_neg (by rw [h]; exact fun e => hx (Option.some.inj e).symm), zpow_zero]) (by simp),`. Use the proof step `expo_single, if_pos h, zpow_one]`. Establish `h₁ : (divOf C (expo Dw (Finsupp.single (a, R, .inr k) 1))).IsEqn y (∏ x : Letter Dw, dg C y x.1 x.2 ^ expo Dw (Finsupp.single (a, R, .inr k) 1) x)` using `isEqn_sum _ y fun x => ((fr_spec C y).2 x.1 x.2).zsmul _`.

Rewrite `h₁` using `[hp]`. Rewrite using `[mul_comm, genAt]`. Simplify `(Base.isEqn_eqn _ y).iff_unitAt.1 h₁` using `[div_eq_mul_inv]`.
-/
theorem unitAt_letter (a : ℕ → Bool) (R : Option ℝ) (k : ℕ) (x₀ : Letter Dw) (h : letterOf Dw (.inr k) = some x₀)
    (y : C.Y.X) :
    UnitAt y (genAt (divOf C (expo Dw (Finsupp.single (a, R, .inr k) 1))) y * (dg C y x₀.1 x₀.2 : C.Y.Fn)) := by
  have hp : ∏ x : Letter Dw, dg C y x.1 x.2 ^ expo Dw (Finsupp.single (a, R, .inr k) 1) x = dg C y x₀.1 x₀.2 := by
    rw [Finset.prod_eq_single x₀ (fun x _ hx => by
      rw [expo_single, if_neg (by rw [h]; exact fun e => hx (Option.some.inj e).symm), zpow_zero]) (by simp),
      expo_single, if_pos h, zpow_one]
  have h₁ : (divOf C (expo Dw (Finsupp.single (a, R, .inr k) 1))).IsEqn y
      (∏ x : Letter Dw, dg C y x.1 x.2 ^ expo Dw (Finsupp.single (a, R, .inr k) 1) x) :=
    isEqn_sum _ y fun x => ((fr_spec C y).2 x.1 x.2).zsmul _
  rw [hp] at h₁
  rw [mul_comm, genAt]
  simpa [div_eq_mul_inv] using (Base.isEqn_eqn _ y).iff_unitAt.1 h₁

end Flags

/- English proof (translation)
Introduce `D O T R p c`. Take `⟨hX, hN, M₀, ρ₀, hM, hρ⟩` from `GlobalTheory.ModelOver.exists_normal_model D.what₂.LL (O.Φ.C c).Y (𝓞 O.κ.c.F) (RingOfIntegers.mapRingEquiv O.κ.e) O.s.T.Z.X O.s.T.Z.s ((O.Φ.C c).π ≫ GlobalTheory.Toroidal.genι O.s.T.Z) O.s.T.Z.proj (by`. Rewrite using `[← (O.Φ.C c).π_str]`. Simplify using `only [Category.assoc]`. Rewrite using `[Limits.pullback.condition_assoc, ← Spec.map_comp, ← Spec.map_comp]`.

Use the proof step `rfl)`. Establish `hT : {q | ArIn.ind T q = true}.Finite` using `T.finite_toSet.subset fun q hq => by simpa [ArIn.ind] using hq`. Set `g` to `D.R.f * O.N`. Set `w₁ : Fin g → (Sym D.host.E →₀ ℤ)` to `fun i => wholeSym (ArIn.ind T) (some R) (Sum.inl i : Fin g ⊕ Fin g)`. Set `w₂ : Fin g → (Sym D.host.E →₀ ℤ)` to `fun i => GlobalTheory.ConstLat.eigSym O.S.Dw (ArIn.ind T) (some R) (Sum.inl i : Fin g ⊕ Fin g)`.

Establish `hlt (i : Fin g) : (i : ℕ) < (letters O.S.Dw).length` using `(GlobalTheory.EqHalf.length_letters O).symm ▸ i.2`. Establish `hw : ∀ k, ∀ b ∈ (Fin.append w₁ w₂ k).support, {q | b.1 q = true}.Finite`. Introduce `k`. Use `Fin.addCases (fun i => ?_) (fun i => ?_) k` and prove the remaining obligations. Rewrite using `[Fin.append_left]`.

Introduce `b hb`. Rewrite using `[Finset.mem_singleton.1 (Finsupp.support_single_subset hb)]`. Conclude with `hT`. Rewrite using `[Fin.append_right]`. Introduce `b hb`.

Establish `e : w₂ i = _` using `GlobalTheory.ConstLat.eigAt_of_lt O.S.Dw (ArIn.ind T) (some R) 1 (hlt i)`. Rewrite `hb` using `[e]`. Rewrite using `[Finset.mem_singleton.1 (Finsupp.support_single_subset hb)]`. Conclude with `hT`. Take `⟨V₀, m, hm, hV₀⟩` from `GlobalTheory.HalfGeo.bundleSt D.what₂.LL (O.Φ.C c).Y (g + g) (fun k => divOf (O.Φ.C c) (expo O.S.Dw (Fin.append w₁ w₂ k))) (fun k => lgOf (O.Φ.C c) (Fin.append w₁ w₂ k)) ⟨M₀, hM⟩ fun k => fromModel_lgOf (O.Φ.C c) GlobalTheory.ShFam.Pad.HTBound.htBound hX M₀ ρ₀ hM hρ _ (hw k)`.

Use `⟨V₀, fun V a b e₀ e₁ e₂ e₃ => ?_⟩` and prove the remaining obligations. Take `⟨L, hL⟩` from `hV₀ V a b e₀ e₁ e₂ e₃`. Establish `hu (i : Fin g) (y : (O.Φ.C c).Y.X) : UnitAt y (genAt (divOf (O.Φ.C c) (expo O.S.Dw (w₁ i))) y * (GlobalTheory.EqHalf.dgOf O c y i : (O.Φ.C c).Y.Fn))` using `unitAt_letter (O.Φ.C c) (ArIn.ind T) (some R) i (GlobalTheory.EqHalf.letterAt O i) (List.getElem?_eq_getElem (hlt i)) y`. Use `⟨⟨hu, fun i => L (Fin.castAdd g i), m, hm, fun i => ⟨(hL _).1, ?_⟩⟩, ⟨fun i y => ?_, fun i => L (Fin.natAdd g i), m, hm, fun i => ⟨(hL _).1, ?_⟩⟩⟩` and prove the remaining obligations. Establish `h` using `(hL (Fin.castAdd g i)).2 p`.

Simplify using `only [Fin.append_left] at h`. Conclude with `h`. Establish `h` using `hu i y`. Rewrite `h` using `[← GlobalTheory.ConstLat.expo_eigSym O.S.Dw (ArIn.ind T) (some R) (Sum.inl i : Fin g ⊕ Fin g)]`. Conclude with `h`.

Establish `h` using `(hL (Fin.natAdd g i)).2 p`. Simplify using `only [Fin.append_right] at h`. Conclude with `h`.
-/
theorem exists_cover : ∀ (D : D7) (O : Setup D) (T : Finset ℕ) (R : ℝ) (p : ℕ) (c : O.s.Comp),
    ∃ V₀ : Cover (O.Φ.C c).Y, ∀ (V : Cover (O.Φ.C c).Y) (a : V.X ⟶ V₀.X) (b : V.G ⟶ V₀.G), a ≫ V₀.p = V.p →
      V.j ≫ a = b ≫ V₀.j → b ≫ V₀.π = V.π → b (genericPoint V.G) = genericPoint V₀.G →
      GlobalTheory.ConstLat.LineBase V (GlobalTheory.EqHalf.dgOf O c) (GlobalTheory.EqHalf.wholeA O c T R) p ∧
        GlobalTheory.ConstLat.LineBase V (GlobalTheory.EqHalf.dgOf O c) (GlobalTheory.EqHalf.eigA O c T R) p := by
  intro D O T R p c
  obtain ⟨hX, hN, M₀, ρ₀, hM, hρ⟩ := GlobalTheory.ModelOver.exists_normal_model D.what₂.LL (O.Φ.C c).Y (𝓞 O.κ.c.F) (RingOfIntegers.mapRingEquiv O.κ.e)
    O.s.T.Z.X O.s.T.Z.s ((O.Φ.C c).π ≫ GlobalTheory.Toroidal.genι O.s.T.Z) O.s.T.Z.proj (by
      rw [← (O.Φ.C c).π_str]
      simp only [Category.assoc]
      rw [Limits.pullback.condition_assoc, ← Spec.map_comp, ← Spec.map_comp]
      rfl)
  have hT : {q | ArIn.ind T q = true}.Finite := T.finite_toSet.subset fun q hq => by simpa [ArIn.ind] using hq
  let g := D.R.f * O.N
  let w₁ : Fin g → (Sym D.host.E →₀ ℤ) := fun i => wholeSym (ArIn.ind T) (some R) (Sum.inl i : Fin g ⊕ Fin g)
  let w₂ : Fin g → (Sym D.host.E →₀ ℤ) := fun i =>
    GlobalTheory.ConstLat.eigSym O.S.Dw (ArIn.ind T) (some R) (Sum.inl i : Fin g ⊕ Fin g)
  have hlt (i : Fin g) : (i : ℕ) < (letters O.S.Dw).length := (GlobalTheory.EqHalf.length_letters O).symm ▸ i.2
  have hw : ∀ k, ∀ b ∈ (Fin.append w₁ w₂ k).support, {q | b.1 q = true}.Finite := by
    intro k
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · rw [Fin.append_left]
      intro b hb
      rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hb)]
      exact hT
    · rw [Fin.append_right]
      intro b hb
      have e : w₂ i = _ := GlobalTheory.ConstLat.eigAt_of_lt O.S.Dw (ArIn.ind T) (some R) 1 (hlt i)
      rw [e] at hb
      rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hb)]
      exact hT
  obtain ⟨V₀, m, hm, hV₀⟩ := GlobalTheory.HalfGeo.bundleSt D.what₂.LL (O.Φ.C c).Y (g + g)
    (fun k => divOf (O.Φ.C c) (expo O.S.Dw (Fin.append w₁ w₂ k))) (fun k => lgOf (O.Φ.C c) (Fin.append w₁ w₂ k)) ⟨M₀, hM⟩
    fun k => fromModel_lgOf (O.Φ.C c) GlobalTheory.ShFam.Pad.HTBound.htBound hX M₀ ρ₀ hM hρ _ (hw k)
  refine ⟨V₀, fun V a b e₀ e₁ e₂ e₃ => ?_⟩
  obtain ⟨L, hL⟩ := hV₀ V a b e₀ e₁ e₂ e₃
  have hu (i : Fin g) (y : (O.Φ.C c).Y.X) :
      UnitAt y (genAt (divOf (O.Φ.C c) (expo O.S.Dw (w₁ i))) y * (GlobalTheory.EqHalf.dgOf O c y i : (O.Φ.C c).Y.Fn)) :=
    unitAt_letter (O.Φ.C c) (ArIn.ind T) (some R) i (GlobalTheory.EqHalf.letterAt O i) (List.getElem?_eq_getElem (hlt i)) y
  refine ⟨⟨hu, fun i => L (Fin.castAdd g i), m, hm, fun i => ⟨(hL _).1, ?_⟩⟩,
    ⟨fun i y => ?_, fun i => L (Fin.natAdd g i), m, hm, fun i => ⟨(hL _).1, ?_⟩⟩⟩
  · have h := (hL (Fin.castAdd g i)).2 p
    simp only [Fin.append_left] at h
    exact h
  · have h := hu i y
    rw [← GlobalTheory.ConstLat.expo_eigSym O.S.Dw (ArIn.ind T) (some R) (Sum.inl i : Fin g ⊕ Fin g)] at h
    exact h
  · have h := (hL (Fin.natAdd g i)).2 p
    simp only [Fin.append_right] at h
    exact h

end GlobalTheory.EqHalf.LineCover

end
