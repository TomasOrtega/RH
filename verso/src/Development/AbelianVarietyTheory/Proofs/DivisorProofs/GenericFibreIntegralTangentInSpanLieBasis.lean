import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCoord
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLetterIntegralInIntegralEigenbasis
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCdvrCompletionIntegralIff
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLieBasisIffIsUnitDet
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.Frames
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory GlobalTheory.CM GlobalTheory.LamT
namespace GlobalTheory.PtDeg.LieModel

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem isGrpPullback_self {S : Scheme.{0}} (G : Over S) [GrpObj G] : IsGrpPullback G G (𝟙 S) (𝟙 G.left) := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  exact (mul_left_congr (G := G) (Category.comp_id T.hom) x₀ y₀ x y (hx.trans (Category.comp_id _))
    (hy.trans (Category.comp_id _))).trans (Category.comp_id _).symm

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem dualMap_id (R : Type) [CommRing R] : dualMap (RingHom.id R) = RingHom.id (DualNumber R) := by
  apply RingHom.ext
  intro x
  ext <;> simp [dualMap]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem spMap_dualMap_id (R : Type) [CommRing R] : spMap (dualMap (RingHom.id R)) = 𝟙 _ := by
  rw [dualMap_id]; exact Spec.map_id _

/- English proof (translation)
Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
theorem spMap_comp_two {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem spMap_id' (R : Type) [CommRing R] : spMap (RingHom.id R) = 𝟙 _ := Spec.map_id _

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem generic_coords_in_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (K : Type) [Field K] [NumberField K] (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (T : CDVR) (iK : K →+* T.Fr) (ρV : 𝓞 K →+* T.V), (algebraMap T.V T.Fr).comp ρV = iK.comp (algebraMap (𝓞 K) K) → ∀ (G : GlobalTheory.CM.PAT H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (n : SABMap G.t B.t (spMap ρV)) (n' : SABMap t' t₀ (spMap iK)) (m2' : SABMap t' G.t (spMap (algebraMap T.V T.Fr))), m2'.φ ≫ n.φ = n'.φ ≫ m2.φ → ∀ (v' : Fin F.P₀.g → (epsR T.Fr ⟶ t'.G)), IsLieBasis v' → (∀ k, (v' k).left ≫ n'.φ ≫ m2.φ = spMap (Formalism.L2.Pj.dualMap iK) ≫ (F.v k).left ≫ F.φ) → ∀ (vV : Fin F.P₀.g → (epsR T.V ⟶ G.t.G)) (M : Fin F.P₀.g → Fin F.P₀.g → K), IsLieBasis vV → (∀ k, ∃ w : epsR K ⟶ F.P₀.A, IsLieComb (M k) F.v w ∧ spMap (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)) ≫ (vV k).left ≫ n.φ = spMap (Formalism.L2.Pj.dualMap iK) ≫ w.left ≫ F.φ) → ∀ (ub : epsOver T.V T.V ⟶ G.t.G) (u'' : Sp (DualNumber T.Fr) ⟶ t'.G.left), IsTan ub → u'' ≫ m2'.φ = spMap (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)) ≫ ub.left → ∃ (a : Fin F.P₀.g → T.V) (w'' : epsR T.Fr ⟶ t'.G), w''.left = u'' ∧ IsLieComb (∑ k, algebraMap T.V T.Fr (a k) • fun l => iK (M k l)) v' w'' := by
  intro E _ _ _ H K _ _ B t₀ m2 F T iK ρV hρV G t' n n' m2' h2 v' hv' hv'φ vV M hvV hM ub u'' hub hu''

  let ub' : epsR T.V ⟶ G.t.G := Over.homMk ub.left (Over.w ub)
  have hub' : IsTangent ub' := by
    unfold IsTangent
    refine hub.trans ?_
    have e : (1 : ptOver T.V T.V ⟶ G.t.G) = toUnit _ ≫ η[G.t.G] := rfl
    rw [e, Over.comp_left]
    have e2 : (toUnit (ptOver T.V T.V)).left = 𝟙 (Sp T.V) := by
      have := Over.w (toUnit (ptOver T.V T.V))
      exact ((Category.comp_id _).symm.trans this).trans (Spec.map_id _)
    rw [e2]
    exact Category.id_comp _
  obtain ⟨a, ha, -⟩ := hvV.2 ub' hub'

  have hw'' : u'' ≫ t'.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) := by
    apply spMap_frac_cancel (V := T.V)
    rw [Category.assoc, ← m2'.cart.1.w, ← Category.assoc, hu'', Category.assoc, Over.w ub]
    show spMap (dualMap (algebraMap T.V T.Fr)) ≫ spMap (algebraMap T.V (DualNumber T.V)) = _
    exact (spMap_comp_two _ _).trans ((congrArg spMap (dualMap_alg _)).trans (spMap_comp_two _ _).symm)

  have hsq : ∀ k, (spMap (dualMap (algebraMap T.V T.Fr)) ≫ (vV k).left) ≫ G.t.G.hom =
      spMap (algebraMap T.Fr (DualNumber T.Fr)) ≫ spMap (algebraMap T.V T.Fr) := fun k => by
    rw [Category.assoc, Over.w (vV k)]
    exact (spMap_comp_two _ _).trans ((congrArg spMap (dualMap_alg _)).trans (spMap_comp_two _ _).symm)
  let g : Fin F.P₀.g → (epsR T.Fr ⟶ t'.G) := fun k =>
    Over.homMk (m2'.cart.1.lift _ _ (hsq k)) (m2'.cart.1.lift_snd _ _ _)
  have hg1 : ∀ k, (g k).left ≫ m2'.φ = spMap (dualMap (algebraMap T.V T.Fr)) ≫ (vV k).left :=
    fun k => m2'.cart.1.lift_fst _ _ _
  have hB : IsGrpPullback t'.G B.t.G (spMap iK ≫ spMap (algebraMap (𝓞 K) K)) (n'.φ ≫ m2.φ) :=
    n'.cart.comp m2.cart
  have hT' := LieComb.lieComb_algebra T.Fr t'.G _ v' hv'.1
  have hgk : ∀ k, IsLieComb (fun l => iK (M k l)) v' (g k) := by
    intro k
    obtain ⟨wk, hwk, hwkeq⟩ := hM k
    obtain ⟨w₁, hw₁, -⟩ := hT'.1 (fun l => iK (M k l))
    have hf : spMap (RingHom.id T.Fr) ≫ (spMap iK ≫ spMap (algebraMap (𝓞 K) K)) =
        spMap iK ≫ spMap (algebraMap (𝓞 K) K) := by rw [spMap_id', Category.id_comp]
    have hm := LetterInt.comb_match hB F.fib.2.1 (RingHom.id T.Fr) iK hf
      (fun i => by rw [spMap_dualMap_id, Category.id_comp]; exact hv'φ i) (fun _ => rfl) hw₁ hwk
    rw [spMap_dualMap_id, Category.id_comp] at hm
    have he : w₁ = g k := by
      refine Over.OverMorphism.ext (hB.1.hom_ext ?_ ((Over.w w₁).trans (Over.w (g k)).symm))
      rw [hm, ← hwkeq, ← h2, ← Category.assoc (g k).left, hg1, Category.assoc]
    exact he ▸ hw₁

  have hgt : ∀ k, IsTangent (g k) := fun k => hT'.2.1 _ _ (hgk k)
  obtain ⟨w, hw, -⟩ := (LieComb.lieComb_algebra T.Fr t'.G _ g hgt).1 (fun k => algebraMap T.V T.Fr (a k))
  have hcomb := hT'.2.2.1 _ (fun k l => iK (M k l)) g _ w hgk hw
  have hf2 : spMap (algebraMap T.V T.Fr) ≫ 𝟙 (Sp T.V) = spMap (RingHom.id T.Fr) ≫ spMap (algebraMap T.V T.Fr) := by
    rw [spMap_id', Category.id_comp, Category.comp_id]
  have hm2 := LetterInt.comb_match (isGrpPullback_self G.t.G) m2'.cart (algebraMap T.V T.Fr) (RingHom.id T.Fr) hf2
    (v₁ := vV) (v₂ := g) (fun i => by rw [spMap_dualMap_id, Category.id_comp, Category.comp_id, hg1])
    (c₁ := a) (c₂ := fun k => algebraMap T.V T.Fr (a k)) (fun _ => rfl) ha hw
  rw [spMap_dualMap_id, Category.id_comp, Category.comp_id] at hm2
  have hleft : w.left = u'' := by
    refine m2'.cart.1.hom_ext ?_ ((Over.w w).trans hw''.symm)
    rw [← hm2, hu'']
    rfl
  exact ⟨a, w, hleft, hcomb⟩

end GlobalTheory.PtDeg.LieModel
