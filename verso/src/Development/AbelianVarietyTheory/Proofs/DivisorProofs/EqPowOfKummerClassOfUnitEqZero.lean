import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKummerBoundaryEtaleCohomologyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeZeroSectionClassPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveMultiplicativeGroupSectionsUnits
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.KumZero

/- English proof (translation)
Simplify using `using h.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom`.
-/
theorem isUnit_top {A : Type} [CommRing A] {q : ℕ} (h : IsUnit (q : A)) :
    IsUnit (q : Γ(Spec (CommRingCat.of A), ⊤)) := by
  simpa using h.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom

/- English proof (translation)
Introduce and unpack `U ⟨x⟩`. Establish `x' : U ⟶ X` using `x`. Simplify using `using hX.map x'.appTop.hom`.
-/
theorem inv_sch {q : ℕ} {X : Scheme.{0}} (hX : IsUnit (q : Γ(X, ⊤))) : Inv q (sch.obj X) := by
  rintro U ⟨x⟩
  have x' : U ⟶ X := x
  simpa using hX.map x'.appTop.hom

/- English proof (translation)
Introduce `a b h`. Use `(GlobalTheory.EtC.GmSec.gm_sec_bijective X).1 h` as an intermediate fact. Simplify using `using congrArg (fun z => Additive.toMul z.down) this`.
-/
theorem unitSec_injective {X : Scheme.{0}} : Function.Injective (unitSec (U := X)) := by
  intro a b h
  have := (GlobalTheory.EtC.GmSec.gm_sec_bijective X).1 h
  simpa using congrArg (fun z => Additive.toMul z.down) this

/- English proof (translation)
Take `⟨w, hw⟩` from `(GlobalTheory.EtC.GmSec.gm_sec_bijective X).2 b`. Conclude with `⟨Additive.toMul w.down, hw⟩`.
-/
theorem unitSec_surjective {X : Scheme.{0}} (b : Sec Gm X) : ∃ v, unitSec v = b := by
  obtain ⟨w, hw⟩ := (GlobalTheory.EtC.GmSec.gm_sec_bijective X).2 b
  exact ⟨Additive.toMul w.down, hw⟩

/- English proof (translation)
Establish `h : (n • φ).hom = n • φ.hom` using `(sheafToPresheaf _ _).map_zsmul (X := F) (Y := G) (f := φ) (r := n)`. Unfold `Sec.map`. Rewrite using `[h, NatTrans.app_zsmul, ModuleCat.hom_zsmul, LinearMap.smul_apply]`.
-/
theorem sec_map_zsmul {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) (n : ℤ) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (n • φ) x = n • Sec.map φ x := by
  have h : (n • φ).hom = n • φ.hom := (sheafToPresheaf _ _).map_zsmul (X := F) (Y := G) (f := φ) (r := n)
  unfold Sec.map
  rw [h, NatTrans.app_zsmul, ModuleCat.hom_zsmul, LinearMap.smul_apply]

/- English proof (translation)
Unfold `unitSec ofRings.sec`. Use `(map_zsmul (ModuleCat.Hom.hom ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).app (op X))) (n : ℤ) (show (Scheme.Γ ⋙ unitsF).obj (op X) from ⟨Additive.ofMul v⟩)).symm.trans ?_` and prove the remaining obligations. Use `congr 1`.
-/
theorem smul_unitSec (n : ℕ) {X : Scheme.{0}} (v : (Γ(X, ⊤))ˣ) : (n : ℤ) • unitSec v = unitSec (v ^ n) := by
  unfold unitSec ofRings.sec
  refine (map_zsmul (ModuleCat.Hom.hom ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).app (op X))) (n : ℤ)
    (show (Scheme.Γ ⋙ unitsF).obj (op X) from ⟨Additive.ofMul v⟩)).symm.trans ?_
  congr 1

/- English proof (translation)
Rewrite using `[sec_map_zsmul, ← smul_unitSec]`. Both sides reduce to the same expression.
-/
theorem map_q_unitSec (q : ℕ) {X : Scheme.{0}} (v : (Γ(X, ⊤))ˣ) :
    Sec.map ((q : ℤ) • 𝟙 Gm) (unitSec v) = unitSec (v ^ q) := by
  rw [sec_map_zsmul, ← smul_unitSec]
  rfl

/- English proof (translation)
Introduce `q _ A _ hq u hu`. Establish `hX` using `isUnit_top hq`. Take `⟨κ, -, bd, -, hex, ⟨s, hs⟩, -⟩` from `GlobalTheory.T.exists_kummer_boundary_etale_cohomology q`. Establish `h1 : bd (sch.obj (Spec (CommRingCat.of A))) 0 (secClass Gm (unitSec u)) = 0`. Rewrite using `[hs _ u hX, hu, smul_zero]`.

Take `⟨y, hy⟩` from `((hex _ (inv_sch hX) 0).1 _).1 h1`. Establish `hsc` using `GlobalTheory.T.degreeZeroSectionClass_properties ℤ Gm (Spec (CommRingCat.of A))`. Take `⟨b, rfl⟩` from `hsc.2.1.2 y`. Rewrite `hy` using `[hsc.2.2.2.2]`. Establish `hb` using `hsc.2.1.1 hy`.

Take `⟨v, rfl⟩` from `unitSec_surjective b`. Rewrite `hb` using `[map_q_unitSec]`. Conclude with `⟨v, (unitSec_injective hb).symm⟩`.
-/
theorem _root_.GlobalTheory.EtC.eq_pow_of_kum_eq_zero : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], IsUnit (q : A) →
    ∀ u : (Γ(Spec (CommRingCat.of A), ⊤))ˣ, kum q u = 0 → ∃ v, u = v ^ q := by
  intro q _ A _ hq u hu
  have hX := isUnit_top hq
  obtain ⟨κ, -, bd, -, hex, ⟨s, hs⟩, -⟩ := GlobalTheory.T.exists_kummer_boundary_etale_cohomology q
  have h1 : bd (sch.obj (Spec (CommRingCat.of A))) 0 (secClass Gm (unitSec u)) = 0 := by
    rw [hs _ u hX, hu, smul_zero]
  obtain ⟨y, hy⟩ := ((hex _ (inv_sch hX) 0).1 _).1 h1
  have hsc := GlobalTheory.T.degreeZeroSectionClass_properties ℤ Gm (Spec (CommRingCat.of A))
  obtain ⟨b, rfl⟩ := hsc.2.1.2 y
  rw [hsc.2.2.2.2] at hy
  have hb := hsc.2.1.1 hy
  obtain ⟨v, rfl⟩ := unitSec_surjective b
  rw [map_q_unitSec] at hb
  exact ⟨v, (unitSec_injective hb).symm⟩

end GlobalTheory.EtC.KumZero
