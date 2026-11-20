import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKummerBoundaryEtaleCohomologyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeZeroSectionClassPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyCoefficientMapFunctorialAdditiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleDescentPicardGroupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveMultiplicativeGroupSectionsUnits
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.KumSurj

/- English proof (translation)
Unfold `unitSec`. Conclude with `map_add ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).app (op U)).hom (ULift.up (Additive.ofMul u)) (ULift.up (Additive.ofMul v))`.
-/
theorem unitSec_mul' {U : Scheme.{0}} (u v : (Γ(U, ⊤))ˣ) : unitSec (u * v) = unitSec u + unitSec v := by
  unfold unitSec
  exact map_add ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).app (op U)).hom
    (ULift.up (Additive.ofMul u)) (ULift.up (Additive.ofMul v))

/- English proof (translation)
Take `⟨y, hy⟩` from `(GlobalTheory.EtC.GmSec.gm_sec_bijective U).2 b`. Conclude with `⟨Additive.toMul y.down, hy⟩`.
-/
theorem unitSec_surj {U : Scheme.{0}} (b : Sec Gm U) : ∃ u : (Γ(U, ⊤))ˣ, unitSec u = b := by
  obtain ⟨y, hy⟩ := (GlobalTheory.EtC.GmSec.gm_sec_bijective U).2 b
  exact ⟨Additive.toMul y.down, hy⟩

/- English proof (translation)
Introduce `U ⟨x⟩`. Establish `h1 : IsUnit (q : Γ(Spec (CommRingCat.of A), ⊤))`. Simplify using `using hq.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom`. Simplify using `using h1.map (show U ⟶ Spec (CommRingCat.of A) from x).appTop.hom`.
-/
theorem inv_sp (q : ℕ) (A : Type) [CommRing A] (hq : IsUnit (q : A)) : Inv q (sp A) := by
  intro U ⟨x⟩
  have h1 : IsUnit (q : Γ(Spec (CommRingCat.of A), ⊤)) := by
    simpa using hq.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  simpa using h1.map (show U ⟶ Spec (CommRingCat.of A) from x).appTop.hom

end GlobalTheory.EtC.KumSurj

open GlobalTheory.EtC.KumSurj in

/- English proof (translation)
Introduce `q _ A _ hq hp x`. Take `⟨κ, -, bd, -, hex, ⟨s, hs⟩, -⟩` from `GlobalTheory.T.exists_kummer_boundary_etale_cohomology q`. Establish `hE : Inv q (sp A)` using `inv_sp q A hq`. Establish `hqX : IsUnit (q : Γ(Spec (CommRingCat.of A), ⊤))`. Simplify using `using hq.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom`.

Take `⟨_, h2, h3⟩` from `hex (sp A) hE 0`. Take `⟨_, _, _, hpc, _⟩` from `GlobalTheory.T.hypercohomologyCoefficientMap_functorial_additive ℤ ((chains ℤ).obj (sp A)) (0 + 1)`. Take `⟨hpid, _⟩` from `GlobalTheory.T.hypercohomologyCoefficientMap_functorial_additive ℤ ((chains ℤ).obj (sp A)) (0 + 1)`. Use `set y := HK.post ℤ ((chains ℤ).obj (sp A)) κ (0 + 1) (restrH (Int.castRingHom (ZMod q)) (sp A) (tw q 1) (0 + 1) x) with hy`. Establish `hqy : (q : ℤ) • y = 0`.

Use `(h3 y).2 ⟨x, rfl⟩` as an intermediate fact. Rewrite `this` using `[hpc, hpid]`. Conclude with `this`. Establish `hy0 : y = 0`. Take `⟨e⟩` from `GlobalTheory.T.etale_descent_picard_group A`.

Establish `h1 : (q : ℤ) • e y = 0` using `by rw [← map_zsmul, hqy, map_zero]`. Establish `h2' : (Additive.toMul (e y)) ^ q = 1`. Use `congrArg Additive.toMul h1` as an intermediate fact. Rewrite `this` using `[natCast_zsmul, toMul_nsmul]`. Conclude with `this`.

Use `hp _ h2'` as an intermediate fact. Apply `e.injective` to reduce the goal to its premises. Rewrite using `[map_zero]`. Conclude with `congrArg Additive.ofMul this`. Take `⟨g, hg⟩` from `(h2 x).1 hy0`.

Take `⟨-, hbij, hadd, -, -⟩` from `GlobalTheory.T.degreeZeroSectionClass_properties ℤ Gm (Spec (CommRingCat.of A))`. Take `⟨b, rfl⟩` from `hbij.2 g`. Take `⟨u, rfl⟩` from `unitSec_surj b`. Establish `hsu` using `hs _ u hqX`. Break down `Int.units_eq_one_or s with rfl | rfl` into its components or cases.

Conclude with `⟨u, by rw [← hg, hsu, one_smul]⟩`. Use `⟨u⁻¹, ?_⟩` and prove the remaining obligations. Establish `hsi` using `hs _ u⁻¹ hqX`. Establish `hsum : bd (sch.obj (Spec (CommRingCat.of A))) 0 (secClass Gm (unitSec u⁻¹)) + bd (sch.obj (Spec (CommRingCat.of A))) 0 (secClass Gm (unitSec u)) = 0`. Rewrite using `[← map_add, ← hadd, ← unitSec_mul', inv_mul_cancel]`.

Establish `h0 : unitSec (1 : (Γ(Spec (CommRingCat.of A), ⊤))ˣ) = 0`. Use `unitSec_mul' (1 : (Γ(Spec (CommRingCat.of A), ⊤))ˣ) 1` as an intermediate fact. Rewrite `this` using `[mul_one]`. Conclude with `(left_eq_add.1 this)`. Establish `h00 : secClass Gm (0 : Sec Gm (Spec (CommRingCat.of A))) = 0`.

Use `hadd 0 0` as an intermediate fact. Rewrite `this` using `[add_zero]`. Conclude with `left_eq_add.1 this`. Rewrite using `[h0, h00, map_zero]`. Rewrite `hsum` using `[hsi, hsu, Units.neg_smul, Units.neg_smul, one_smul, one_smul]`.

Rewrite using `[← hg, hsu, Units.neg_smul, one_smul]`. Rewrite `hsum` using `[← neg_add]`. Conclude with `eq_neg_of_add_eq_zero_left (neg_eq_zero.1 hsum)`.
-/
theorem GlobalTheory.EtC.kum_surjective : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], IsUnit (q : A) → (∀ c : CommRing.Pic A, c ^ q = 1 → c = 1) → ∀ x : Ht q (sp A) 1 1, ∃ u : (Γ(Spec (CommRingCat.of A), ⊤))ˣ, kum q u = x := by
  intro q _ A _ hq hp x
  obtain ⟨κ, -, bd, -, hex, ⟨s, hs⟩, -⟩ := GlobalTheory.T.exists_kummer_boundary_etale_cohomology q
  have hE : Inv q (sp A) := inv_sp q A hq
  have hqX : IsUnit (q : Γ(Spec (CommRingCat.of A), ⊤)) := by
    simpa using hq.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  obtain ⟨_, h2, h3⟩ := hex (sp A) hE 0
  obtain ⟨_, _, _, hpc, _⟩ := GlobalTheory.T.hypercohomologyCoefficientMap_functorial_additive ℤ ((chains ℤ).obj (sp A)) (0 + 1)
  obtain ⟨hpid, _⟩ := GlobalTheory.T.hypercohomologyCoefficientMap_functorial_additive ℤ ((chains ℤ).obj (sp A)) (0 + 1)
  set y := HK.post ℤ ((chains ℤ).obj (sp A)) κ (0 + 1) (restrH (Int.castRingHom (ZMod q)) (sp A) (tw q 1) (0 + 1) x) with hy
  have hqy : (q : ℤ) • y = 0 := by
    have := (h3 y).2 ⟨x, rfl⟩
    rw [hpc, hpid] at this
    exact this
  have hy0 : y = 0 := by
    obtain ⟨e⟩ := GlobalTheory.T.etale_descent_picard_group A
    have h1 : (q : ℤ) • e y = 0 := by rw [← map_zsmul, hqy, map_zero]
    have h2' : (Additive.toMul (e y)) ^ q = 1 := by
      have := congrArg Additive.toMul h1
      rw [natCast_zsmul, toMul_nsmul] at this
      exact this
    have := hp _ h2'
    apply e.injective
    rw [map_zero]
    exact congrArg Additive.ofMul this
  obtain ⟨g, hg⟩ := (h2 x).1 hy0
  obtain ⟨-, hbij, hadd, -, -⟩ := GlobalTheory.T.degreeZeroSectionClass_properties ℤ Gm (Spec (CommRingCat.of A))
  obtain ⟨b, rfl⟩ := hbij.2 g
  obtain ⟨u, rfl⟩ := unitSec_surj b
  have hsu := hs _ u hqX
  rcases Int.units_eq_one_or s with rfl | rfl
  · exact ⟨u, by rw [← hg, hsu, one_smul]⟩
  · refine ⟨u⁻¹, ?_⟩
    have hsi := hs _ u⁻¹ hqX
    have hsum : bd (sch.obj (Spec (CommRingCat.of A))) 0 (secClass Gm (unitSec u⁻¹)) +
        bd (sch.obj (Spec (CommRingCat.of A))) 0 (secClass Gm (unitSec u)) = 0 := by
      rw [← map_add, ← hadd, ← unitSec_mul', inv_mul_cancel]
      have h0 : unitSec (1 : (Γ(Spec (CommRingCat.of A), ⊤))ˣ) = 0 := by
        have := unitSec_mul' (1 : (Γ(Spec (CommRingCat.of A), ⊤))ˣ) 1
        rw [mul_one] at this
        exact (left_eq_add.1 this)
      have h00 : secClass Gm (0 : Sec Gm (Spec (CommRingCat.of A))) = 0 := by
        have := hadd 0 0
        rw [add_zero] at this
        exact left_eq_add.1 this
      rw [h0, h00, map_zero]
    rw [hsi, hsu, Units.neg_smul, Units.neg_smul, one_smul, one_smul] at hsum
    rw [← hg, hsu, Units.neg_smul, one_smul]
    rw [← neg_add] at hsum
    exact eq_neg_of_add_eq_zero_left (neg_eq_zero.1 hsum)
