import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.EtaleCohomology.TateTwists.EtaleTateTwistTensorIsoOfGeneratorMapIso

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace LateralTheory.EtaleFoundations.TensExPf
open LateralTheory.EtaleFoundations.TwMulPf
open scoped TensorProduct DirectSum

variable {R : Type} [CommRing R]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sec_map_zero {F G : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.map (0 : F ⟶ G) x = 0 := by
  rfl

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem sec_zero_of_isZero {Z : Shv R} (hZ : IsZero Z) {U : Scheme.{0}} (y : Sec Z U) : y = 0 := by
  have h : Sec.map (𝟙 Z) y = Sec.map 0 y := by rw [hZ.eq_of_src (𝟙 Z) 0]
  rw [sec_map_id, sec_map_zero] at h
  exact h

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem isZero_sglX (F : Shv R) {w : ℤ} (hw : w ≠ 0) : IsZero ((sgl F).X w) :=
  HomologicalComplex.isZero_single_obj_X _ _ _ _ hw

/- English proof (translation)
Consider separately whether the proposition holds or fails. A detailed English derivation is pending.
-/
theorem sgl_d (F : Shv R) (a : ℤ) : (sgl F).d a (a + 1) = 0 := by
  by_cases ha : a = 0
  · exact (isZero_sglX F (by omega)).eq_of_tgt _ _
  · exact (isZero_sglX F ha).eq_of_src _ _

def eIso (K : Cx R) (w : ℤ) (h : w = 0) : K.X w ≅ (sgl (K.X 0)).X w :=
  K.XIsoOfEq h ≪≫ (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0 (K.X 0) w h).symm

def e (K : Cx R) (w : ℤ) : K.X w ⟶ (sgl (K.X 0)).X w :=
  if h : w = 0 then (eIso K w h).hom else 0

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem e_pos (K : Cx R) {w : ℤ} (h : w = 0) : e K w = (eIso K w h).hom := dif_pos h

def μ {A B : Shv R} {K : Cx R} (τ : Pair (sgl A) (sgl B) K) : Pair (sgl A) (sgl B) (sgl (K.X 0)) where
  mul U s t w h := (τ.mul U s t w h).compr₂ (secL (e K w) U)
  nat g s t w h a b := by
    change Sec.res g (Sec.map (e K w) _) = Sec.map (e K w) _
    rw [sec_res_map, τ.nat]
  leibniz U s t w h a b := by
    change Sec.map ((sgl (K.X 0)).d w (w + 1)) _ =
      Sec.map (e K (w + 1)) (τ.mul U (s + 1) t (w + 1) _ (Sec.map ((sgl A).d s (s + 1)) a) b) +
        s.negOnePow • Sec.map (e K (w + 1)) (τ.mul U s (t + 1) (w + 1) _ a (Sec.map ((sgl B).d t (t + 1)) b))
    simp only [sgl_d, sec_map_zero, map_zero, LinearMap.zero_apply, smul_zero, add_zero]

/- English proof (translation)
Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.
-/
theorem μ_lift {A B : Shv R} {K : Cx R} (τ : Pair (sgl A) (sgl B) K) (U : Scheme.{0}) (w : ℤ)
    (x : Tens (sgl A) (sgl B) U w) : (μ τ).lift U w x = Sec.map (e K w) (τ.lift U w x) := by
  classical
  change _ = secL (e K w) U (τ.lift U w x)
  rw [← LinearMap.comp_apply]
  congr 1
  refine DirectSum.linearMap_ext _ fun p => TensorProduct.ext' fun a b => ?_
  simp [Pair.lift, μ]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem tens_summand_zero {A B : Shv R} {a b : ℤ} (hab : a ≠ 0 ∨ b ≠ 0) {U : Scheme.{0}}
    (z : Sec ((sgl A).X a) U ⊗[ULift.{1} R] Sec ((sgl B).X b) U) : z = 0 := by
  refine TensorProduct.induction_on z rfl (fun u v => ?_) (fun x y hx hy => by rw [hx, hy, add_zero])
  rcases hab with h | h
  · rw [sec_zero_of_isZero (isZero_sglX A h) u, TensorProduct.zero_tmul]
  · rw [sec_zero_of_isZero (isZero_sglX B h) v, TensorProduct.tmul_zero]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction.

Use linear arithmetic over natural numbers and integers. A detailed English derivation is pending.
-/
theorem tens_zero {A B : Shv R} {U : Scheme.{0}} {w : ℤ} (hw : w ≠ 0) (x : Tens (sgl A) (sgl B) U w) : x = 0 := by
  refine DirectSum.ext fun p => ?_
  rw [DirectSum.zero_apply]
  refine tens_summand_zero ?_ _
  have := p.2
  by_contra hc
  push Not at hc
  omega

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Reduce the conclusion to the remaining proof obligations. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem μ_isTensor {A B : Shv R} {K : Cx R} (τ : Pair (sgl A) (sgl B) K) (hτ : τ.IsTensor) :
    (μ τ).IsTensor := by
  refine ⟨fun U w y => ?_, fun U w x hx => ?_⟩
  · by_cases hw : w = 0
    · refine loc_mono (hτ.1 U w (Sec.map (eIso K w hw).inv y)) fun V g ⟨x, hx⟩ => ⟨x, ?_⟩
      rw [μ_lift, hx, ← sec_res_map, e_pos K hw, sec_map_comp, Iso.inv_hom_id, sec_map_id]
    · refine ⟨⊤, Scheme.etaleTopology.top_mem U, fun V g _ => ⟨0, ?_⟩⟩
      rw [map_zero]
      exact (sec_zero_of_isZero (isZero_sglX _ hw) _).symm
  · by_cases hw : w = 0
    · refine hτ.2 U w x ?_
      rw [μ_lift, e_pos K hw] at hx
      have := congrArg (Sec.map (eIso K w hw).inv) hx
      rw [sec_map_comp, Iso.hom_inv_id, sec_map_id] at this
      rw [this]
      exact map_zero _
    · obtain rfl := tens_zero hw x
      exact ⟨⊤, Scheme.etaleTopology.top_mem U, fun _ _ _ => map_zero _⟩

end LateralTheory.EtaleFoundations.TensExPf

open LateralTheory.EtaleFoundations.TensExPf in
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem LateralTheory.EtaleFoundations.etale_tate_twist_multiplication_tensor_exists_of_complex_tensor_exists
    (hex : ∀ (R : Type) [CommRing R] (I J : Cx R), ∃ (K : Cx R) (τ : Pair I J K), τ.IsTensor) :
    LateralTheory.EtaleFoundations.EtaleTateTwistTensorPairingExists := by
  intro q _ i j
  obtain ⟨K, τ, hτ⟩ := hex (ZMod q) (sgl (tw q i)) (sgl (tw q j))
  exact ⟨K.X 0, μ τ, μ_isTensor τ hτ⟩
