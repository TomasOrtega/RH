import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDerivAt0OfIsPullback
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HolDifferentiableAt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.VerticalDeriv

open GlobalTheory.FibreDeriv

variable {g : ℕ} {X Z : Scheme.{0}}

/- English proof (translation)
Rewrite `H`, `H'` using `[isDerivAt0_iff]`. Take `⟨U, hU, hxU, -⟩` from `exists_isAffineOpen_mem_and_subset (X := Z) (U := ⊤) (x := e 0 (default : PrimeSpectrum ℂ)) trivial`. Establish `h0 : ⊤ ≤ e 0 ⁻¹ᵁ U` using `(top_le_preimage_iff_mem _ U).2 hxU`. Establish `h` using `(top_le_preimage_eps v _ H.1 U).2 h0`. Establish `h'` using `(top_le_preimage_eps v' _ H'.1 U).2 h0`.

Conclude with `TangentOrigin.ext_evalPt hU h h' (RingHom.ext fun f => (H.2 U h f).trans (H'.2 U h' f).symm)`.
-/
theorem isDerivAt0_unique {e : (Fin g → ℂ) → (Sp ℂ ⟶ Z)} {w : Fin g → ℂ} {v v' : Sp (DualNumber ℂ) ⟶ Z}
    (H : IsDerivAt0 e w v) (H' : IsDerivAt0 e w v') : v = v' := by
  rw [isDerivAt0_iff] at H H'
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := Z) (U := ⊤)
    (x := e 0 (default : PrimeSpectrum ℂ)) trivial
  have h0 : ⊤ ≤ e 0 ⁻¹ᵁ U := (top_le_preimage_iff_mem _ U).2 hxU
  have h := (top_le_preimage_eps v _ H.1 U).2 h0
  have h' := (top_le_preimage_eps v' _ H'.1 U).2 h0
  exact TangentOrigin.ext_evalPt hU h h' (RingHom.ext fun f => (H.2 U h f).trans (H'.2 U h' f).symm)

/- English proof (translation)
Take `⟨U, hU, hxU, -⟩` from `exists_isAffineOpen_mem_and_subset (X := Z) (U := ⊤) (x := e 0 (default : PrimeSpectrum ℂ)) trivial`. Establish `h0 : ⊤ ≤ e 0 ⁻¹ᵁ U` using `(top_le_preimage_iff_mem _ U).2 hxU`. Establish `hd` using `LocalLift.hol_differentiableAt hol (Set.mem_univ _) h0`. Set `J : Γ(Z, U) →+* DualNumber ℂ` to `{ toFun := fun f => jet w (fun z => valAt' (e z) U f) map_one' := by`. Establish `: (fun z => valAt' (e z) U 1) =ᶠ[nhds 0] fun _ => 1` using `by filter_upwards [LocalLift.hol_eventually_mem hol (Set.mem_univ _) h0] with z hz`.

Conclude with `valAt'_one _ hz.2`. Rewrite using `[jet_congr w this, jet_const, map_one]`. Use the proof step `map_zero' := by`. Simplify using `only [valAt'_zero]`. Rewrite using `[jet_const, map_zero]`.

Use the proof step `map_add' := fun f f' => by`. Simplify using `only [valAt'_add]`. Conclude with `jet_add w (hd f) (hd f')`. Use the proof step `map_mul' := fun f f' => by`. Simplify using `only [valAt'_mul]`.

Conclude with `jet_mul w (hd f) (hd f') }`. Take `⟨v, hv, hve⟩` from `TangentOrigin.exists_evalPt_eq hU J`. Use `⟨v, isDerivAt0_of_affine ?_ hU hv fun a => ⟨hd a, DFunLike.congr_fun hve a⟩⟩` and prove the remaining obligations. Use `TangentOrigin.ext_evalPt hU ((TangentOrigin.top_le_preimage_iff v U).1 hv) h0 (RingHom.ext fun f => ?_)` and prove the remaining obligations. Use `(TangentOrigin.evalPt_spMap_comp TangentOrigin.fstC v U hv _ f).trans ?_` and prove the remaining obligations.

Rewrite using `[hve, ← TangentOrigin.valAt'_eq_evalPt]`. Conclude with `fst_jet w (fun z => valAt' (e z) U f)`.
-/
theorem exists_isDerivAt0 {e : (Fin g → ℂ) → (Sp ℂ ⟶ Z)} (hol : IsHolTo Set.univ e) (w : Fin g → ℂ) :
    ∃ v : Sp (DualNumber ℂ) ⟶ Z, IsDerivAt0 e w v := by
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := Z) (U := ⊤)
    (x := e 0 (default : PrimeSpectrum ℂ)) trivial
  have h0 : ⊤ ≤ e 0 ⁻¹ᵁ U := (top_le_preimage_iff_mem _ U).2 hxU
  have hd := LocalLift.hol_differentiableAt hol (Set.mem_univ _) h0
  let J : Γ(Z, U) →+* DualNumber ℂ :=
    { toFun := fun f => jet w (fun z => valAt' (e z) U f)
      map_one' := by
        have : (fun z => valAt' (e z) U 1) =ᶠ[nhds 0] fun _ => 1 := by
          filter_upwards [LocalLift.hol_eventually_mem hol (Set.mem_univ _) h0] with z hz
          exact valAt'_one _ hz.2
        rw [jet_congr w this, jet_const, map_one]
      map_zero' := by
        simp only [valAt'_zero]
        rw [jet_const, map_zero]
      map_add' := fun f f' => by
        simp only [valAt'_add]
        exact jet_add w (hd f) (hd f')
      map_mul' := fun f f' => by
        simp only [valAt'_mul]
        exact jet_mul w (hd f) (hd f') }
  obtain ⟨v, hv, hve⟩ := TangentOrigin.exists_evalPt_eq hU J
  refine ⟨v, isDerivAt0_of_affine ?_ hU hv fun a => ⟨hd a, DFunLike.congr_fun hve a⟩⟩
  refine TangentOrigin.ext_evalPt hU ((TangentOrigin.top_le_preimage_iff v U).1 hv) h0 (RingHom.ext fun f => ?_)
  refine (TangentOrigin.evalPt_spMap_comp TangentOrigin.fstC v U hv _ f).trans ?_
  rw [hve, ← TangentOrigin.valAt'_eq_evalPt]
  exact fst_jet w (fun z => valAt' (e z) U f)

/- English proof (translation)
Establish `h1` using `isDerivAt0_comp H p`. Simplify using `only [he] at h1`. Conclude with `isDerivAt0_unique h1 (LocalLift.isDerivAt0_const (fun _ => x) w fun U f _ => by simp)`.
-/
theorem isDerivAt0_vertical (p : Z ⟶ X) (x : Sp ℂ ⟶ X) {e : (Fin g → ℂ) → (Sp ℂ ⟶ Z)} (he : ∀ z, e z ≫ p = x)
    {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ Z} (H : IsDerivAt0 e w v) :
    v ≫ p = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ x := by
  have h1 := isDerivAt0_comp H p
  simp only [he] at h1
  exact isDerivAt0_unique h1 (LocalLift.isDerivAt0_const (fun _ => x) w fun U f _ => by simp)

/- English proof (translation)
Rewrite using `[fderiv_pi fun i => LocalLift.hol_differentiableAt hol (Set.mem_univ _) h0 (t i)]`. Conclude with `H.2 U h (t i)`.
-/
theorem isDerivAt0_snd {e : (Fin g → ℂ) → (Sp ℂ ⟶ Z)} (hol : IsHolTo Set.univ e) {U : Z.Opens} {n : ℕ}
    (t : Fin n → Γ(Z, U)) (h0 : ⊤ ≤ e 0 ⁻¹ᵁ U) {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ Z}
    (H : IsDerivAt0 e w v) (h : ⊤ ≤ v ⁻¹ᵁ U) (i : Fin n) :
    (TangentOrigin.evalPt v U h (t i)).snd = fderiv ℂ (fun z i => valAt' (e z) U (t i)) 0 w i := by
  rw [fderiv_pi fun i => LocalLift.hol_differentiableAt hol (Set.mem_univ _) h0 (t i)]
  exact H.2 U h (t i)

/- English proof (translation)
Use `set T := fderiv ℂ (fun z i => valAt' (e z) U (t i)) 0 with hT`. Establish `key : ∀ (v : Sp (DualNumber ℂ) ⟶ Z) (h : ⊤ ≤ v ⁻¹ᵁ U), v ≫ p = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ x → spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = e 0 → ∀ w, (IsDerivAt0 e w v ↔ T w = fun i => (TangentOrigin.evalPt v U h (t i)).snd)`. Introduce `v h hv hv0 w`. Use `⟨fun H => funext fun i => (isDerivAt0_snd hol t h0 H h i).symm, fun H => ?_⟩` and prove the remaining obligations. Take `⟨v', H'⟩` from `exists_isDerivAt0 hol w`.

Establish `h'` using `(top_le_preimage_eps v' _ H'.1 U).2 h0`. Rewrite using `[hun v v' h h' (hv.trans (isDerivAt0_vertical p x he H').symm) (hv0.trans H'.1.symm) fun i => ?_]`. Conclude with `H'`. Use `TrivSqZeroExt.ext ((fst_evEps v _ hv0 U h _).trans (fst_evEps v' _ H'.1 U h' _).symm) ?_` and prove the remaining obligations. Rewrite using `[isDerivAt0_snd hol t h0 H' h' i]`.

Conclude with `(congrFun H i).symm`. Prove the components needed by the constructor for the conclusion. Introduce `H w w' hw`. Take `⟨v, Hv⟩` from `exists_isDerivAt0 hol w`. Establish `h` using `(top_le_preimage_eps v _ Hv.1 U).2 h0`.

Establish `hv` using `isDerivAt0_vertical p x he Hv`. Conclude with `(H v hv Hv.1).unique Hv ((key v h hv Hv.1 w').2 (hw.symm.trans ((key v h hv Hv.1 w).1 Hv)))`. Introduce `H v hv hv0`. Establish `h` using `(top_le_preimage_eps v _ hv0 U).2 h0`. Simplify using `only [key v h hv hv0]`.

Establish `hs : Function.Surjective T` using `(LinearMap.injective_iff_surjective (f := T.toLinearMap)).1 H`. Conclude with `(Function.bijective_iff_existsUnique T).1 ⟨H, hs⟩ _`.
-/
theorem bijective_iff_injective (p : Z ⟶ X) (x : Sp ℂ ⟶ X) {e : (Fin g → ℂ) → (Sp ℂ ⟶ Z)} (he : ∀ z, e z ≫ p = x)
    (hol : IsHolTo Set.univ e) (U : Z.Opens) (t : Fin g → Γ(Z, U)) (h0 : ⊤ ≤ e 0 ⁻¹ᵁ U)
    (hun : ∀ (v v' : Sp (DualNumber ℂ) ⟶ Z) (h : ⊤ ≤ v ⁻¹ᵁ U) (h' : ⊤ ≤ v' ⁻¹ᵁ U), v ≫ p = v' ≫ p →
      spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v' →
      (∀ i, TangentOrigin.evalPt v U h (t i) = TangentOrigin.evalPt v' U h' (t i)) → v = v') :
    (∀ v : Sp (DualNumber ℂ) ⟶ Z, v ≫ p = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ x →
      spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = e 0 → ∃! w, IsDerivAt0 e w v) ↔
      Function.Injective (fderiv ℂ (fun z i => valAt' (e z) U (t i)) 0) := by
  set T := fderiv ℂ (fun z i => valAt' (e z) U (t i)) 0 with hT
  have key : ∀ (v : Sp (DualNumber ℂ) ⟶ Z) (h : ⊤ ≤ v ⁻¹ᵁ U), v ≫ p = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ x →
      spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = e 0 → ∀ w,
      (IsDerivAt0 e w v ↔ T w = fun i => (TangentOrigin.evalPt v U h (t i)).snd) := by
    intro v h hv hv0 w
    refine ⟨fun H => funext fun i => (isDerivAt0_snd hol t h0 H h i).symm, fun H => ?_⟩
    obtain ⟨v', H'⟩ := exists_isDerivAt0 hol w
    have h' := (top_le_preimage_eps v' _ H'.1 U).2 h0
    rw [hun v v' h h' (hv.trans (isDerivAt0_vertical p x he H').symm) (hv0.trans H'.1.symm) fun i => ?_]
    · exact H'
    · refine TrivSqZeroExt.ext ((fst_evEps v _ hv0 U h _).trans (fst_evEps v' _ H'.1 U h' _).symm) ?_
      rw [isDerivAt0_snd hol t h0 H' h' i]
      exact (congrFun H i).symm
  constructor
  · intro H w w' hw
    obtain ⟨v, Hv⟩ := exists_isDerivAt0 hol w
    have h := (top_le_preimage_eps v _ Hv.1 U).2 h0
    have hv := isDerivAt0_vertical p x he Hv
    exact (H v hv Hv.1).unique Hv ((key v h hv Hv.1 w').2 (hw.symm.trans ((key v h hv Hv.1 w).1 Hv)))
  · intro H v hv hv0
    have h := (top_le_preimage_eps v _ hv0 U).2 h0
    simp only [key v h hv hv0]
    have hs : Function.Surjective T := (LinearMap.injective_iff_surjective (f := T.toLinearMap)).1 H
    exact (Function.bijective_iff_existsUnique T).1 ⟨H, hs⟩ _

end GlobalTheory.VerticalDeriv

namespace GlobalTheory

open VerticalDeriv in

/- English proof (translation)
Introduce `X G x g e hol`. Establish `he : ∀ z, (show Sp ℂ ⟶ G.left from (e z).left) ≫ G.hom = x` using `fun z => Over.w (e z)`. Use `⟨fun w => ?_, fun U t h0 hun => ?_⟩` and prove the remaining obligations. Take `⟨v, Hv⟩` from `exists_isDerivAt0 hol w`. Conclude with `⟨Over.homMk v (isDerivAt0_vertical G.hom x he Hv), Hv, fun v' Hv' => Over.OverMorphism.ext (isDerivAt0_unique Hv' Hv)⟩`.

Use `Iff.trans ?_ (bijective_iff_injective G.hom x he hol U t h0 hun)` and prove the remaining obligations. Conclude with `⟨fun H v hv hv0 => H (Over.homMk v hv) hv0, fun H v hv0 => H v.left (Over.w v) hv0⟩`.
-/
theorem vertical_derivative_in_coordinates :
    ∀ (X : Scheme.{0}) (G : Over X) (x : Sp ℂ ⟶ X) (g : ℕ) (e : (Fin g → ℂ) → (Over.mk x ⟶ G)), IsHolTo Set.univ (fun z => (e z).left) → (∀ w, ∃! v : epsPt x ⟶ G, IsDerivAt0 (fun z => (e z).left) w v.left) ∧ ∀ (U : G.left.Opens) (t : Fin g → Γ(G.left, U)), ⊤ ≤ (show Sp ℂ ⟶ G.left from (e 0).left) ⁻¹ᵁ U → (∀ (v v' : Sp (DualNumber ℂ) ⟶ G.left) (h : ⊤ ≤ v ⁻¹ᵁ U) (h' : ⊤ ≤ v' ⁻¹ᵁ U), v ≫ G.hom = v' ≫ G.hom → spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v' → (∀ i, GlobalTheory.TangentOrigin.evalPt v U h (t i) = GlobalTheory.TangentOrigin.evalPt v' U h' (t i)) → v = v') → ((∀ v : epsPt x ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left → ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left) ↔ Function.Injective (fderiv ℂ (fun z i => valAt' (e z).left U (t i)) 0)) := by
  intro X G x g e hol
  have he : ∀ z, (show Sp ℂ ⟶ G.left from (e z).left) ≫ G.hom = x := fun z => Over.w (e z)
  refine ⟨fun w => ?_, fun U t h0 hun => ?_⟩
  · obtain ⟨v, Hv⟩ := exists_isDerivAt0 hol w
    exact ⟨Over.homMk v (isDerivAt0_vertical G.hom x he Hv), Hv,
      fun v' Hv' => Over.OverMorphism.ext (isDerivAt0_unique Hv' Hv)⟩
  · refine Iff.trans ?_ (bijective_iff_injective G.hom x he hol U t h0 hun)
    exact ⟨fun H v hv hv0 => H (Over.homMk v hv) hv0, fun H v hv0 => H v.left (Over.w v) hv0⟩

end GlobalTheory
