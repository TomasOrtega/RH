import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.ExpNegGlue
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRightHaarMeasure

noncomputable section

open NumberField IsDedekindDomain MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep.CuspidalL2GL

namespace PositivityTheory.Rg.Rs.JGapGlue

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def locRep (V : Submodule ℂ (Sm E a)) (hs : IsStable V) (w : HeightOneSpectrum (𝓞 E)) :
    Representation ℂ (GL (Fin a) (w.adicCompletion E)) V where
  toFun g := (finRep E a (locGL E a w g)).restrict fun ψ hψ => hs (.fin (locGL E a w g)) ψ hψ
  map_one' := by
    ext ψ
    simp
  map_mul' g h := by
    ext ψ
    simp only [map_mul]
    rfl

def pairing {X W : Type} [AddCommGroup X] [Module ℂ X] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (F : X →ₗ[ℂ] W) : X →ₗ[ℂ] X →ₗ⋆[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun x y => inner ℂ (F y) (F x))
    (fun x x' y => by simp only [map_add, inner_add_right])
    (fun c x y => by simp only [map_smul, inner_smul_right, smul_eq_mul, RingHom.id_apply])
    (fun x y y' => by simp only [map_add, inner_add_left])
    (fun c x y => by simp only [map_smul, inner_smul_left, smul_eq_mul])

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pairing_apply {X W : Type} [AddCommGroup X] [Module ℂ X] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (F : X →ₗ[ℂ] W) (x y : X) : pairing F x y = inner ℂ (F y) (F x) := rfl

/- English proof (translation)
Introduce `E _ _ _ N V hV w B hB z hz`. Take `⟨⟨φ, hφV, hsat⟩, -⟩` from `hB`. Establish `hcard : B.card = N` using `hsat.2.2.1`. Consider the cases of `N with`. Consider the case `zero`.

Rewrite `hcard` using `[Multiset.card_eq_zero]`. Substitute `hcard` using the available equality. Simplify using the standard rewrite rules. Consider the case `succ n`. Take `⟨μ, h1, h2⟩` from `GlobalTheory.CompanionTheory.AdelicHaar.exists_haar_rightInvariant E (n + 1)`.

Establish `hm : ∀ ψ ∈ V, MemL2Quotient (latticeGL E (n + 1)) μ ψ.1` using `fun ψ hψ => memL2_of_isAutForm (hV.aut ψ hψ) (hV.sqInt ψ hψ)`. Establish `hi : Function.Injective (toL2ₗ μ V hm)` using `toL2ₗ_injective hm fun ψ hψ => ContAut.continuous_of_isOpen_stab E _ ψ (hV.aut ψ hψ).level`. Use `set F := toL2ₗ μ V hm with hF`. Set `ρ` to `locRep V hV.stable w`. Establish `hρ : ∀ g (y : V), F (ρ g y) = R (latticeGL E (n + 1)) μ (finGL E (n + 1) (locGL E (n + 1) w g)) (F y)` using `fun g y => (R_toL2ₗ hm y (hV.stable (.fin (locGL E (n + 1) w g)) y.1 y.2)).symm`.

Establish `hsatV : GlobalTheory.LFun.IsSatVecGL w ρ ⟨φ, hφV⟩ B` using `GlobalTheory.LFun.IsSatVecGL.of_map V.subtype (fun g y => rfl) Subtype.val_injective hsat`. Establish `herm : ∀ x y, pairing F y x = starRingEnd ℂ (pairing F x y)` using `fun x y => by`. Rewrite using `[pairing_apply, pairing_apply, inner_conj_symm]`. Establish `pos : ∀ x, x ≠ 0 → 0 < (pairing F x x).re` using `fun x hx => by`. Rewrite using `[pairing_apply]`.

Establish `h0 : F x ≠ 0` using `fun h => hx (hi (h.trans (map_zero F).symm))`. Establish `hn : 0 < ‖F x‖` using `norm_pos_iff.2 h0`. Establish `e` using `inner_self_eq_norm_sq (𝕜 := ℂ) (F x)`. Express the relevant statement in the definitionally equal form `0 < RCLike.re (inner ℂ (F x) (F x))`. Rewrite using `[e]`.

Check the signs of the components of the expression. Establish `unit : ∀ g x y, pairing F (ρ g x) (ρ g y) = pairing F x y` using `fun g x y => by`. Rewrite using `[pairing_apply, pairing_apply, hρ, hρ]`. Set `I : L2 (latticeGL E (n + 1)) μ →ₗᵢ[ℂ] L2 (latticeGL E (n + 1)) μ` to `{ toLinearMap := (R (latticeGL E (n + 1)) μ (finGL E (n + 1) (locGL E (n + 1) w g))).toLinearMap norm_map' := norm_R _ }`. Conclude with `I.inner_map_map (F y) (F x)`.

Take `⟨k, _, _, Γ, _, red, ρ', t, v, hk, hD, hE⟩` from `hL E w n V ρ (pairing F) ⟨φ, hφV⟩ B herm pos unit hsatV`. Establish `h0 : (0 : ℂ) ∉ B.map fun b : ℂˣ => (b : ℂ)`. Simplify using the standard rewrite rules. Use `hG k n V Γ (pairing F) red ρ' t v _ hD hE h0 z (by rw [hk]; exact_mod_cast hz)` as an intermediate fact. Rewrite `this` using `[hk]`.

Conclude with `this` after adjusting the coercions.
-/
theorem gap (hL : LatOf) (hG : GapAbs) : Gap := by
  intro E _ _ _ N V hV w B hB z hz
  obtain ⟨⟨φ, hφV, hsat⟩, -⟩ := hB
  have hcard : B.card = N := hsat.2.2.1
  cases N with
  | zero =>
    rw [Multiset.card_eq_zero] at hcard
    subst hcard
    simp
  | succ n =>
    obtain ⟨μ, h1, h2⟩ := GlobalTheory.CompanionTheory.AdelicHaar.exists_haar_rightInvariant E (n + 1)
    have hm : ∀ ψ ∈ V, MemL2Quotient (latticeGL E (n + 1)) μ ψ.1 := fun ψ hψ =>
      memL2_of_isAutForm (hV.aut ψ hψ) (hV.sqInt ψ hψ)
    have hi : Function.Injective (toL2ₗ μ V hm) :=
      toL2ₗ_injective hm fun ψ hψ => ContAut.continuous_of_isOpen_stab E _ ψ (hV.aut ψ hψ).level
    set F := toL2ₗ μ V hm with hF
    let ρ := locRep V hV.stable w
    have hρ : ∀ g (y : V), F (ρ g y) = R (latticeGL E (n + 1)) μ (finGL E (n + 1) (locGL E (n + 1) w g)) (F y) :=
      fun g y => (R_toL2ₗ hm y (hV.stable (.fin (locGL E (n + 1) w g)) y.1 y.2)).symm
    have hsatV : GlobalTheory.LFun.IsSatVecGL w ρ ⟨φ, hφV⟩ B :=
      GlobalTheory.LFun.IsSatVecGL.of_map V.subtype (fun g y => rfl) Subtype.val_injective hsat
    have herm : ∀ x y, pairing F y x = starRingEnd ℂ (pairing F x y) := fun x y => by
      rw [pairing_apply, pairing_apply, inner_conj_symm]
    have pos : ∀ x, x ≠ 0 → 0 < (pairing F x x).re := fun x hx => by
      rw [pairing_apply]
      have h0 : F x ≠ 0 := fun h => hx (hi (h.trans (map_zero F).symm))
      have hn : 0 < ‖F x‖ := norm_pos_iff.2 h0
      have e := inner_self_eq_norm_sq (𝕜 := ℂ) (F x)
      change 0 < RCLike.re (inner ℂ (F x) (F x))
      rw [e]
      positivity
    have unit : ∀ g x y, pairing F (ρ g x) (ρ g y) = pairing F x y := fun g x y => by
      rw [pairing_apply, pairing_apply, hρ, hρ]
      let I : L2 (latticeGL E (n + 1)) μ →ₗᵢ[ℂ] L2 (latticeGL E (n + 1)) μ :=
        { toLinearMap := (R (latticeGL E (n + 1)) μ (finGL E (n + 1) (locGL E (n + 1) w g))).toLinearMap
          norm_map' := norm_R _ }
      exact I.inner_map_map (F y) (F x)
    obtain ⟨k, _, _, Γ, _, red, ρ', t, v, hk, hD, hE⟩ := hL E w n V ρ (pairing F) ⟨φ, hφV⟩ B herm pos unit hsatV
    have h0 : (0 : ℂ) ∉ B.map fun b : ℂˣ => (b : ℂ) := by
      simp
    have := hG k n V Γ (pairing F) red ρ' t v _ hD hE h0 z (by rw [hk]; exact_mod_cast hz)
    rw [hk] at this
    exact_mod_cast this

end PositivityTheory.Rg.Rs.JGapGlue

namespace PositivityTheory.Rg.Rs

/- English proof (translation)
The claim follows from `JGapGlue.gap`.
-/
theorem gapGlue_holds : GapGlue := JGapGlue.gap

end PositivityTheory.Rg.Rs
