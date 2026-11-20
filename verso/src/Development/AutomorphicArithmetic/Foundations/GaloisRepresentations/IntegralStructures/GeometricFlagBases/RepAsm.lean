import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FlagBasis

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N

namespace UpperTheory.Gal.Int.Geo

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ l _ H θ hnice`. Take `⟨hsm, hproj, hfet⟩` from `hnice`. Establish `hlE : (l : E) ≠ 0` using `Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime l).ne_zero`. Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective`. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E`.

Establish `hlΩ : (l : Ω) ≠ 0` using `Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime l).ne_zero`. Use `haveI : Smooth H.q := hsm`. Establish `hsm' : Smooth (pullback.snd H.q (Spec.map (CommRingCat.ofHom (algebraMap E Ω))))` using `inferInstance`. Establish `hproj'` using `h9.1 E Ω (algebraMap E Ω) H.q hproj`. Use `haveI hfin : FiniteDimensional ℚ_[l] (Htot l (sch.obj (H.geomZ Ω))) := h6 l Ω hlΩ _ hsm' hproj'`.

Set `U` to `piece l H Ω (Qbar l) θ`. Set `a : Gal(Ω/E) → _` to `fun σ => galV l H Ω (Qbar l) σ`. Establish `ha1 : a 1 = LinearMap.id`. Simplify using `only [a, galV, GlobalTheory.GalV.galTot_one, LinearMap.baseChange_id]`. Establish `hamul : ∀ g h, a (g * h) = a g ∘ₗ a h`.

Introduce `g h`. Simplify using `only [a, galV, GlobalTheory.GalV.galTot_mul, LinearMap.baseChange_comp]`. Establish `hU : ∀ g, ∀ x ∈ U, a g x ∈ U` using `fun g x hx => h5 l E hlE H hfet Ω (Qbar l) θ g x hx`. Set `b` to `Module.finBasis (Qbar l) U`. Take `⟨ρ₀, hmat, hμ⟩` from `h3 (Gal(Ω/E)) (Qbar l) _ a ha1 hamul U hU _ b`.

Establish `hM : IsMat l H Ω (Qbar l) θ ρ₀` using `⟨b, hmat⟩`. Take `⟨P, ρ, hgr, hss⟩` from `h1 (Gal(Ω/E)) (Qbar l) _ ρ₀`. Establish `hM'` using `h4 l E H Ω (Qbar l) θ _ ρ₀ P hM`. Establish `hT` using `h8 l E Ω hlE H.q (h9.2 E H.q hproj)`. Establish `hcont0 : ∀ i j, Continuous fun g => (ρ₀ g).val i j`.

Introduce `i j`. Take `⟨μ, hμij⟩` from `hμ i j`. Establish `hE` using `h7 (Gal(Ω/E)) ℚ_[l] (Qbar l) (continuous_algebraMap ℚ_[l] (Qbar l)) _ (galTot l Ω H.q) hT (b j : _) μ`. Use `hE.congr fun g => ?_` and prove the remaining obligations. Rewrite using `[hμij g]`.

Both sides reduce to the same expression. Use `⟨_, ρ, ?_, hss, cj P ρ₀, hM', hgr⟩` and prove the remaining obligations. Take `⟨c, hc⟩` from `hgr`. Use `(h2 _ (Qbar l) _ ρ).2 fun i j => ?_` and prove the remaining obligations. Establish `hfun : (fun g => (ρ g).val i j) = fun g => if c i = c j then (cj P ρ₀ g).val i j else 0`.

Use function extensionality and compare the values at `fun g => (hc g).2 i j`. Rewrite using `[hfun]`. Use `split_ifs`. Simplify using `only [cj_apply, Units.val_mul, Matrix.mul_apply]`. Use `continuous_finset_sum _ fun x _ => ?_` and prove the remaining obligations.

Use `Continuous.mul ?_ continuous_const` and prove the remaining obligations. Use `continuous_finset_sum _ fun y _ => ?_` and prove the remaining obligations. Conclude with `continuous_const.mul (hcont0 y x)`. Conclude with `continuous_const`.
-/
theorem repEx_of (h1 : GrEx) (h2 : ContGL) (h3 : MatEx) (h4 : MatConj) (h5 : PieceStab) (h6 : HtotFin) (h7 : ExtCont)
    (h8 : TotCont) (h9 : KunnethLefschetz.ProjBC) : RepEx := by
  intro E Ω _ _ _ _ _ l _ H θ hnice
  obtain ⟨hsm, hproj, hfet⟩ := hnice
  have hlE : (l : E) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime l).ne_zero
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have hlΩ : (l : Ω) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime l).ne_zero
  haveI : Smooth H.q := hsm
  have hsm' : Smooth (pullback.snd H.q (Spec.map (CommRingCat.ofHom (algebraMap E Ω)))) := inferInstance
  have hproj' := h9.1 E Ω (algebraMap E Ω) H.q hproj
  haveI hfin : FiniteDimensional ℚ_[l] (Htot l (sch.obj (H.geomZ Ω))) := h6 l Ω hlΩ _ hsm' hproj'
  let U := piece l H Ω (Qbar l) θ
  let a : Gal(Ω/E) → _ := fun σ => galV l H Ω (Qbar l) σ
  have ha1 : a 1 = LinearMap.id := by
    simp only [a, galV, GlobalTheory.GalV.galTot_one, LinearMap.baseChange_id]
  have hamul : ∀ g h, a (g * h) = a g ∘ₗ a h := by
    intro g h
    simp only [a, galV, GlobalTheory.GalV.galTot_mul, LinearMap.baseChange_comp]
  have hU : ∀ g, ∀ x ∈ U, a g x ∈ U := fun g x hx => h5 l E hlE H hfet Ω (Qbar l) θ g x hx
  let b := Module.finBasis (Qbar l) U
  obtain ⟨ρ₀, hmat, hμ⟩ := h3 (Gal(Ω/E)) (Qbar l) _ a ha1 hamul U hU _ b
  have hM : IsMat l H Ω (Qbar l) θ ρ₀ := ⟨b, hmat⟩
  obtain ⟨P, ρ, hgr, hss⟩ := h1 (Gal(Ω/E)) (Qbar l) _ ρ₀
  have hM' := h4 l E H Ω (Qbar l) θ _ ρ₀ P hM
  have hT := h8 l E Ω hlE H.q (h9.2 E H.q hproj)
  have hcont0 : ∀ i j, Continuous fun g => (ρ₀ g).val i j := by
    intro i j
    obtain ⟨μ, hμij⟩ := hμ i j
    have hE := h7 (Gal(Ω/E)) ℚ_[l] (Qbar l) (continuous_algebraMap ℚ_[l] (Qbar l)) _
      (galTot l Ω H.q) hT (b j : _) μ
    refine hE.congr fun g => ?_
    rw [hμij g]
    rfl
  refine ⟨_, ρ, ?_, hss, cj P ρ₀, hM', hgr⟩
  obtain ⟨c, hc⟩ := hgr
  refine (h2 _ (Qbar l) _ ρ).2 fun i j => ?_
  have hfun : (fun g => (ρ g).val i j) = fun g => if c i = c j then (cj P ρ₀ g).val i j else 0 :=
    funext fun g => (hc g).2 i j
  rw [hfun]
  split_ifs
  · simp only [cj_apply, Units.val_mul, Matrix.mul_apply]
    refine continuous_finset_sum _ fun x _ => ?_
    refine Continuous.mul ?_ continuous_const
    refine continuous_finset_sum _ fun y _ => ?_
    exact continuous_const.mul (hcont0 y x)
  · exact continuous_const

end UpperTheory.Gal.Int.Geo

end
