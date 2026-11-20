import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingOpSub
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTwistSections
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatV

/- English proof (translation)
Introduce `X L hL Ω _ _ x g k σ ω hv i hi`. Use `set z := IsLocalRing.closedPoint Ω`. Establish `hxz : x z ∈ L.U i` using `hi (show z ∈ (⊤ : (Sp Ω).Opens) from trivial)`. Take `⟨J, hJ, hJi⟩` from `exists_good L hL z (K := PUnit) (fun _ => x ≫ 𝟙 X) (fun _ => i) (fun _ _ _ => rfl) (fun _ => hxz)`. Establish `h` using `hv (Sp Ω) (𝟙 _) z J hJ`.

Establish `e1 : J ((𝟙 (Sp Ω) ≫ x) ≫ 𝟙 X) = i` using `by simpa using hJi PUnit.unit`. Establish `e2 : J (𝟙 (Sp Ω) ≫ x ≫ 𝟙 X) = i` using `by simpa using hJi PUnit.unit`. Rewrite `h` using `[sval_of σ (𝟙 _ ≫ x) z J (fun _ => i) (fun _ => e1), val_of g (𝟙 _) z J (fun _ => i) (fun _ => e2), Category.id_comp]`. Establish `m1 : (𝟙 (Sp Ω)) z ∈ (⊤ : (Sp Ω).Opens)` using `trivial`. Establish `a1 : valR x _ (σ.f fun _ => i) = (stalkClosedPointIso (CommRingCat.of Ω)).hom.hom (gs x z _ (σ.f fun _ => i))` using `GlobalTheory.ZH.ThetaData.valR_eq_gs x _ (Set.mem_iInter.2 fun _ => hxz) _`.

Establish `mG : (𝟙 (Sp Ω)) z ∈ LB.wchart L (fun _ : PUnit => x ≫ 𝟙 X) (fun _ => i)` using `Set.mem_iInter.2 fun _ => hxz`. Establish `a2 : valR (𝟙 (Sp Ω)) _ (g.s fun _ => i).val = (stalkClosedPointIso (CommRingCat.of Ω)).hom.hom (gs (𝟙 (Sp Ω)) z _ (g.s fun _ => i).val)` using `GlobalTheory.ZH.ThetaData.valR_eq_gs (𝟙 _) _ mG _`. Establish `a3 : gs (𝟙 (Sp Ω)) z _ (g.s fun _ => i).val = (gm (𝟙 (Sp Ω)) z _ (g.s fun _ => i)).val` using `gs_unit _ _ _ mG _`. Establish `hω : (stalkClosedPointIso (CommRingCat.of Ω)).hom.hom (gs (𝟙 (Sp Ω)) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom ω)) = ω`. Rewrite using `[← GlobalTheory.ZH.ThetaData.valR_eq_gs (𝟙 _) ⊤ m1, GlobalTheory.ZH.CrdCalc.valR_eq _ _ le_rfl]`.

Simplify using `[GlobalTheory.ZH.CrdCalc.valHom, Scheme.Hom.appLE]`. Rewrite using `[a1, a2, a3]`. Establish `h'` using `congrArg (stalkClosedPointIso (CommRingCat.of Ω)).hom.hom h`. Rewrite `h'` using `[map_mul, hω, Units.val_pow_eq_pow_val, map_pow]`. Conclude with `h'`.
-/
theorem valR_of_isValue : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (Ω : Type) [CommRing Ω] [IsLocalRing Ω] (x : Sp Ω ⟶ X) (g : GlobalTheory.RayEv.Transport.Frame L (x ≫ 𝟙 X)) (k : ℕ) (σ : SecM (𝟙 X) L k) (ω : Ω), IsValue (𝟙 X) L x g k σ ω → ∀ i, ⊤ ≤ x ⁻¹ᵁ L.U i → valR x _ (σ.f fun _ => i) = ω * (valR (𝟙 (Sp Ω)) _ (g.s fun _ => i).val) ^ k := by
  intro X L hL Ω _ _ x g k σ ω hv i hi
  set z := IsLocalRing.closedPoint Ω
  have hxz : x z ∈ L.U i := hi (show z ∈ (⊤ : (Sp Ω).Opens) from trivial)
  obtain ⟨J, hJ, hJi⟩ := exists_good L hL z (K := PUnit) (fun _ => x ≫ 𝟙 X) (fun _ => i) (fun _ _ _ => rfl)
    (fun _ => hxz)
  have h := hv (Sp Ω) (𝟙 _) z J hJ
  have e1 : J ((𝟙 (Sp Ω) ≫ x) ≫ 𝟙 X) = i := by simpa using hJi PUnit.unit
  have e2 : J (𝟙 (Sp Ω) ≫ x ≫ 𝟙 X) = i := by simpa using hJi PUnit.unit
  rw [sval_of σ (𝟙 _ ≫ x) z J (fun _ => i) (fun _ => e1), val_of g (𝟙 _) z J (fun _ => i) (fun _ => e2),
    Category.id_comp] at h
  have m1 : (𝟙 (Sp Ω)) z ∈ (⊤ : (Sp Ω).Opens) := trivial
  have a1 : valR x _ (σ.f fun _ => i) =
      (stalkClosedPointIso (CommRingCat.of Ω)).hom.hom (gs x z _ (σ.f fun _ => i)) :=
    GlobalTheory.ZH.ThetaData.valR_eq_gs x _ (Set.mem_iInter.2 fun _ => hxz) _
  have mG : (𝟙 (Sp Ω)) z ∈ LB.wchart L (fun _ : PUnit => x ≫ 𝟙 X) (fun _ => i) := Set.mem_iInter.2 fun _ => hxz
  have a2 : valR (𝟙 (Sp Ω)) _ (g.s fun _ => i).val =
      (stalkClosedPointIso (CommRingCat.of Ω)).hom.hom (gs (𝟙 (Sp Ω)) z _ (g.s fun _ => i).val) :=
    GlobalTheory.ZH.ThetaData.valR_eq_gs (𝟙 _) _ mG _
  have a3 : gs (𝟙 (Sp Ω)) z _ (g.s fun _ => i).val = (gm (𝟙 (Sp Ω)) z _ (g.s fun _ => i)).val :=
    gs_unit _ _ _ mG _
  have hω : (stalkClosedPointIso (CommRingCat.of Ω)).hom.hom (gs (𝟙 (Sp Ω)) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom ω)) = ω := by
    rw [← GlobalTheory.ZH.ThetaData.valR_eq_gs (𝟙 _) ⊤ m1, GlobalTheory.ZH.CrdCalc.valR_eq _ _ le_rfl]
    simp [GlobalTheory.ZH.CrdCalc.valHom, Scheme.Hom.appLE]
  rw [a1, a2, a3]
  have h' := congrArg (stalkClosedPointIso (CommRingCat.of Ω)).hom.hom h
  rw [map_mul, hω, Units.val_pow_eq_pow_val, map_pow] at h'
  exact h'

end GlobalTheory.HeatV
