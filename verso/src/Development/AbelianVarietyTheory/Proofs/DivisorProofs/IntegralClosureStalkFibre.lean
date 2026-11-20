import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeOfRingOnEqNonunitsAtPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelAffinePointEqOfInverseMemIffStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFractionRingOnOfMemModelLocalRingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingOnPreimageIntegralOfFiniteModelMapStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.Poinc.FinPts
open GlobalTheory.Points RatModel

section Helpers
variable {o₁ Ω₁ o₂ Ω₂ : Type} [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂]
  [Algebra Ω₁ Ω₂] {M₁ : RatModel o₁ Ω₁} {M₂ : RatModel o₂ Ω₂} {q : M₂.Z ⟶ M₁.Z}

/- English proof (translation)
Use `(valR_comp M₂.pt q U a).symm.trans ?_` and prove the remaining obligations. Rewrite using `[hg]`. Conclude with `valR_spMap_comp _ M₁.pt U (M₁.top_le_preimage_pt hU) a`.
-/
theorem valF_app (hg : M₂.pt ≫ q = spMap (algebraMap Ω₁ Ω₂) ≫ M₁.pt) {U : M₁.Z.Opens}
    (hU : (U : Set M₁.Z).Nonempty) (a : Γ(M₁.Z, U)) :
    valF M₂.pt (q ⁻¹ᵁ U) ((q.app U).hom a) = algebraMap Ω₁ Ω₂ (valF M₁.pt U a) := by
  refine (valR_comp M₂.pt q U a).symm.trans ?_
  rw [hg]
  exact valR_spMap_comp _ M₁.pt U (M₁.top_le_preimage_pt hU) a

/- English proof (translation)
Take `⟨U, a, hz, rfl⟩` from `hx`. Conclude with `⟨q ⁻¹ᵁ U, (q.app U).hom a, hz, valF_app hg ⟨_, hz⟩ a⟩`.
-/
theorem map_mem_O (hg : M₂.pt ≫ q = spMap (algebraMap Ω₁ Ω₂) ≫ M₁.pt) {z : M₂.Z} {x : Ω₁}
    (hx : x ∈ M₁.O (q z)) : algebraMap Ω₁ Ω₂ x ∈ M₂.O z := by
  obtain ⟨U, a, hz, rfl⟩ := hx
  exact ⟨q ⁻¹ᵁ U, (q.app U).hom a, hz, valF_app hg ⟨_, hz⟩ a⟩

/- English proof (translation)
Take `⟨U, a, hz, rfl⟩` from `hx`. Establish `e` using `valF_app hg ⟨_, hz⟩ a`. Establish `hz' : z ∈ q ⁻¹ᵁ U` using `hz`. Establish `hu : IsUnit (⟨valF M₂.pt (q ⁻¹ᵁ U) ((q.app U).hom a), valF_mem_O hz' _⟩ : M₂.O z)` using `(isUnit_O_iff _).2 ⟨show valF M₂.pt (q ⁻¹ᵁ U) ((q.app U).hom a) ≠ 0 by rw [e]; exact (map_ne_zero _).2 h0, show (valF M₂.pt (q ⁻¹ᵁ U) ((q.app U).hom a))⁻¹ ∈ M₂.O z by rw [e]; exact h⟩`. Rewrite `hu` using `[isUnit_valF_iff hz', ← Scheme.preimage_basicOpen]`.

Conclude with `((isUnit_O_iff _).1 ((isUnit_valF_iff hz a).2 hu)).2`.
-/
theorem inv_mem_O_of_map (hg : M₂.pt ≫ q = spMap (algebraMap Ω₁ Ω₂) ≫ M₁.pt) {z : M₂.Z} {x : Ω₁}
    (hx : x ∈ M₁.O (q z)) (h0 : x ≠ 0) (h : (algebraMap Ω₁ Ω₂ x)⁻¹ ∈ M₂.O z) : x⁻¹ ∈ M₁.O (q z) := by
  obtain ⟨U, a, hz, rfl⟩ := hx
  have e := valF_app hg ⟨_, hz⟩ a
  have hz' : z ∈ q ⁻¹ᵁ U := hz
  have hu : IsUnit (⟨valF M₂.pt (q ⁻¹ᵁ U) ((q.app U).hom a), valF_mem_O hz' _⟩ : M₂.O z) :=
    (isUnit_O_iff _).2 ⟨show valF M₂.pt (q ⁻¹ᵁ U) ((q.app U).hom a) ≠ 0 by rw [e]; exact (map_ne_zero _).2 h0,
      show (valF M₂.pt (q ⁻¹ᵁ U) ((q.app U).hom a))⁻¹ ∈ M₂.O z by rw [e]; exact h⟩
  rw [isUnit_valF_iff hz', ← Scheme.preimage_basicOpen] at hu
  exact ((isUnit_O_iff _).1 ((isUnit_valF_iff hz a).2 hu)).2

/- English proof (translation)
Rewrite using `[← map_inv₀]`. Conclude with `map_mem_O hg h`.
-/
theorem map_inv_mem_O (hg : M₂.pt ≫ q = spMap (algebraMap Ω₁ Ω₂) ≫ M₁.pt) {z : M₂.Z} {x : Ω₁}
    (h : x⁻¹ ∈ M₁.O (q z)) : (algebraMap Ω₁ Ω₂ x)⁻¹ ∈ M₂.O z := by
  rw [← map_inv₀]; exact map_mem_O hg h

end Helpers

section Main
variable {o₁ Ω₁ o₂ Ω₂ : Type} [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂]
  [Algebra Ω₁ Ω₂] {M₁ : RatModel o₁ Ω₁} {M₂ : RatModel o₂ Ω₂} {q : M₂.Z ⟶ M₁.Z} {z₁ : M₁.Z}
  [Algebra (M₁.Z.presheaf.stalk z₁) Ω₂]

/- English proof (translation)
Establish `hl : f.map (algebraMap Ω₁ Ω₂) ∈ Polynomial.lifts (algebraMap (M₁.Z.presheaf.stalk z₁) Ω₂)`. Rewrite using `[Polynomial.lifts_iff_coeff_lifts]`. Introduce `n`. Rewrite using `[Polynomial.coeff_map]`. Take `⟨x, hx⟩` from `(M₁.stalkEquiv z₁).surjective ⟨_, hc n⟩`.

Conclude with `⟨x, by rw [halg, ← coe_stalkEquiv, hx]⟩`. Take `⟨g, hgm, -, hmon⟩` from `Polynomial.lifts_and_natDegree_eq_and_monic hl (hf.map _)`. Use `⟨g, hmon, ?_⟩` and prove the remaining obligations. Rewrite using `[← Polynomial.eval_map, hgm, Polynomial.eval_map, h0]`.
-/
theorem isIntegral_of_poly (halg : ∀ x, algebraMap (M₁.Z.presheaf.stalk z₁) Ω₂ x = algebraMap Ω₁ Ω₂ (M₁.stalkHom z₁ x))
    {b : Ω₂} (f : Polynomial Ω₁) (hf : f.Monic) (hc : ∀ i, f.coeff i ∈ M₁.O z₁)
    (h0 : f.eval₂ (algebraMap Ω₁ Ω₂) b = 0) : IsIntegral (M₁.Z.presheaf.stalk z₁) b := by
  have hl : f.map (algebraMap Ω₁ Ω₂) ∈ Polynomial.lifts (algebraMap (M₁.Z.presheaf.stalk z₁) Ω₂) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [Polynomial.coeff_map]
    obtain ⟨x, hx⟩ := (M₁.stalkEquiv z₁).surjective ⟨_, hc n⟩
    exact ⟨x, by rw [halg, ← coe_stalkEquiv, hx]⟩
  obtain ⟨g, hgm, -, hmon⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl (hf.map _)
  refine ⟨g, hmon, ?_⟩
  rw [← Polynomial.eval_map, hgm, Polynomial.eval_map, h0]

/- English proof (translation)
Take `⟨s, hs⟩` from `(M₁.stalkEquiv z₁).surjective ⟨x, hx⟩`. Establish `: algebraMap Ω₁ Ω₂ x = algebraMap (M₁.Z.presheaf.stalk z₁) Ω₂ s`. Rewrite using `[halg, ← coe_stalkEquiv, hs]`. Rewrite using `[this]`. Conclude with `isIntegral_algebraMap`.
-/
theorem isIntegral_map_O (halg : ∀ x, algebraMap (M₁.Z.presheaf.stalk z₁) Ω₂ x = algebraMap Ω₁ Ω₂ (M₁.stalkHom z₁ x))
    {x : Ω₁} (hx : x ∈ M₁.O z₁) : IsIntegral (M₁.Z.presheaf.stalk z₁) (algebraMap Ω₁ Ω₂ x) := by
  obtain ⟨s, hs⟩ := (M₁.stalkEquiv z₁).surjective ⟨x, hx⟩
  have : algebraMap Ω₁ Ω₂ x = algebraMap (M₁.Z.presheaf.stalk z₁) Ω₂ s := by
    rw [halg, ← coe_stalkEquiv, hs]
  rw [this]
  exact isIntegral_algebraMap

/- English proof (translation)
Use `⟨M₂.pt (IsLocalRing.closedPoint Ω₂), ?_⟩` and prove the remaining obligations. Use `show (M₂.pt ≫ q) (IsLocalRing.closedPoint Ω₂) ∈ U`. Rewrite using `[hg]`. Conclude with `M₁.top_le_preimage_pt hU (x := spMap (algebraMap Ω₁ Ω₂) (IsLocalRing.closedPoint Ω₂)) trivial`.
-/
theorem preimage_nonempty (hg : M₂.pt ≫ q = spMap (algebraMap Ω₁ Ω₂) ≫ M₁.pt) {U : M₁.Z.Opens}
    (hU : (U : Set M₁.Z).Nonempty) : ((q ⁻¹ᵁ U : M₂.Z.Opens) : Set M₂.Z).Nonempty := by
  refine ⟨M₂.pt (IsLocalRing.closedPoint Ω₂), ?_⟩
  show (M₂.pt ≫ q) (IsLocalRing.closedPoint Ω₂) ∈ U
  rw [hg]
  exact M₁.top_le_preimage_pt hU (x := spMap (algebraMap Ω₁ Ω₂) (IsLocalRing.closedPoint Ω₂)) trivial

/- English proof (translation)
The claim follows from `mem_ringOn.2 fun z hz => map_mem_O hg (mem_ringOn.1 ha (q z) hz)`.
-/
theorem map_mem_ringOn (hg : M₂.pt ≫ q = spMap (algebraMap Ω₁ Ω₂) ≫ M₁.pt) {U : M₁.Z.Opens} {a : Ω₁}
    (ha : a ∈ M₁.ringOn (U : Set M₁.Z)) :
    algebraMap Ω₁ Ω₂ a ∈ M₂.ringOn ((q ⁻¹ᵁ U : M₂.Z.Opens) : Set M₂.Z) :=
  mem_ringOn.2 fun z hz => map_mem_O hg (mem_ringOn.1 ha (q z) hz)

def pIdeal {U : Set M₁.Z} (hz : z₁ ∈ U) : Ideal (M₁.ringOn U) :=
  (IsLocalRing.maximalIdeal (M₁.O z₁)).comap (Subalgebra.inclusion (ringOn_le_O hz)).toRingHom

/- English proof (translation)
Rewrite using `[pIdeal, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_O_iff]`. Both sides reduce to the same expression.
-/
theorem mem_pIdeal {U : Set M₁.Z} (hz : z₁ ∈ U) (a : M₁.ringOn U) :
    a ∈ pIdeal hz ↔ ¬ ((a : Ω₁) ≠ 0 ∧ (a : Ω₁)⁻¹ ∈ M₁.O z₁) := by
  rw [pIdeal, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_O_iff]
  rfl

instance isPrime_pIdeal {U : Set M₁.Z} (hz : z₁ ∈ U) : (pIdeal hz).IsPrime :=
  Ideal.comap_isPrime _ _

/- English proof (translation)
Use `letI : Algebra (M₁.ringOn (U : Set M₁.Z)) (M₂.ringOn ((q ⁻¹ᵁ U : M₂.Z.Opens) : Set M₂.Z)) := ((algebraMap Ω₁ Ω₂).restrict _ _ fun _ ha => map_mem_ringOn hg ha).toAlgebra`. Use `⟨fun c => ?_⟩` and prove the remaining obligations. Take `⟨f, hf, hc, h0⟩` from `GlobalTheory.T.ringOn_preimage_integral_of_finite_model_map _ _ _ _ M₁ M₂ q hF hg U hU hne c c.2`. Establish `hl : f ∈ Polynomial.lifts (M₁.ringOn (U : Set M₁.Z)).val.toRingHom`. Rewrite using `[Polynomial.lifts_iff_coeff_lifts]`.

Conclude with `fun n => ⟨⟨_, hc n⟩, rfl⟩`. Take `⟨g, hgm, -, hmon⟩` from `Polynomial.lifts_and_natDegree_eq_and_monic hl hf`. Use `⟨g, hmon, Subtype.ext ?_⟩` and prove the remaining obligations. Rewrite `h0` using `[← hgm, Polynomial.eval₂_map]`. Establish `e` using `Polynomial.hom_eval₂ g (algebraMap _ _) (M₂.ringOn ((q ⁻¹ᵁ U : M₂.Z.Opens) : Set M₂.Z)).val.toRingHom c`.

Rewrite using `[Subalgebra.coe_zero]`. Conclude with `e.trans (Eq.trans (by congr 1) h0)`.
-/
theorem isIntegral_ringOn (hF : IsFinite q) (hg : M₂.pt ≫ q = spMap (algebraMap Ω₁ Ω₂) ≫ M₁.pt) {U : M₁.Z.Opens}
    (hU : IsAffineOpen U) (hne : (U : Set M₁.Z).Nonempty) :
    letI : Algebra (M₁.ringOn (U : Set M₁.Z)) (M₂.ringOn ((q ⁻¹ᵁ U : M₂.Z.Opens) : Set M₂.Z)) :=
      ((algebraMap Ω₁ Ω₂).restrict _ _ fun _ ha => map_mem_ringOn hg ha).toAlgebra
    Algebra.IsIntegral (M₁.ringOn (U : Set M₁.Z)) (M₂.ringOn ((q ⁻¹ᵁ U : M₂.Z.Opens) : Set M₂.Z)) := by
  letI : Algebra (M₁.ringOn (U : Set M₁.Z)) (M₂.ringOn ((q ⁻¹ᵁ U : M₂.Z.Opens) : Set M₂.Z)) :=
    ((algebraMap Ω₁ Ω₂).restrict _ _ fun _ ha => map_mem_ringOn hg ha).toAlgebra
  refine ⟨fun c => ?_⟩
  obtain ⟨f, hf, hc, h0⟩ := GlobalTheory.T.ringOn_preimage_integral_of_finite_model_map _ _ _ _ M₁ M₂ q hF hg U hU hne c c.2
  have hl : f ∈ Polynomial.lifts (M₁.ringOn (U : Set M₁.Z)).val.toRingHom := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    exact fun n => ⟨⟨_, hc n⟩, rfl⟩
  obtain ⟨g, hgm, -, hmon⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl hf
  refine ⟨g, hmon, Subtype.ext ?_⟩
  rw [← hgm, Polynomial.eval₂_map] at h0
  have e := Polynomial.hom_eval₂ g (algebraMap _ _) (M₂.ringOn ((q ⁻¹ᵁ U : M₂.Z.Opens) : Set M₂.Z)).val.toRingHom c
  rw [Subalgebra.coe_zero]
  exact e.trans (Eq.trans (by congr 1) h0)

end Main

section Claim1
variable {o₁ Ω₁ o₂ Ω₂ : Type} [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂]
  [Algebra Ω₁ Ω₂] {M₁ : RatModel o₁ Ω₁} {M₂ : RatModel o₂ Ω₂} {q : M₂.Z ⟶ M₁.Z} {z₁ : M₁.Z}
  [Algebra (M₁.Z.presheaf.stalk z₁) Ω₂]

/- English proof (translation)
Use `haveI := isIntegrallyClosed_O hN z'`. Use `letI : Algebra (M₁.Z.presheaf.stalk z₁) (M₂.O z') := (((algebraMap Ω₁ Ω₂).comp (M₁.stalkHom z₁)).codRestrict (M₂.O z') fun x => map_mem_O hg (by rw [hz']; exact (M₁.stalkEquiv z₁ x).2)).toAlgebra`. Use `haveI : IsScalarTower (M₁.Z.presheaf.stalk z₁) (M₂.O z') Ω₂ := IsScalarTower.of_algebraMap_eq fun x => halg x`. Take `⟨y, hy⟩` from `IsIntegrallyClosed.isIntegral_iff.1 (hb.tower_top (A := M₂.O z'))`. Conclude with `hy ▸ y.2`.
-/
theorem mem_O_of_isIntegral (hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M₂.Z) (hg : M₂.pt ≫ q = spMap (algebraMap Ω₁ Ω₂) ≫ M₁.pt)
    (halg : ∀ x, algebraMap (M₁.Z.presheaf.stalk z₁) Ω₂ x = algebraMap Ω₁ Ω₂ (M₁.stalkHom z₁ x)) {b : Ω₂}
    (hb : IsIntegral (M₁.Z.presheaf.stalk z₁) b) {z' : M₂.Z} (hz' : q z' = z₁) : b ∈ M₂.O z' := by
  haveI := isIntegrallyClosed_O hN z'
  letI : Algebra (M₁.Z.presheaf.stalk z₁) (M₂.O z') :=
    (((algebraMap Ω₁ Ω₂).comp (M₁.stalkHom z₁)).codRestrict (M₂.O z') fun x =>
      map_mem_O hg (by rw [hz']; exact (M₁.stalkEquiv z₁ x).2)).toAlgebra
  haveI : IsScalarTower (M₁.Z.presheaf.stalk z₁) (M₂.O z') Ω₂ :=
    IsScalarTower.of_algebraMap_eq fun x => halg x
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 (hb.tower_top (A := M₂.O z'))
  exact hy ▸ y.2

/- English proof (translation)
Use `haveI := hF`. Take `⟨U, hU, hz, -⟩` from `exists_isAffineOpen_mem_and_subset (U := (⊤ : M₁.Z.Opens)) (x := z₁) trivial`. Establish `hne : (U : Set M₁.Z).Nonempty` using `⟨z₁, hz⟩`. Establish `hU₂ : IsAffineOpen (q ⁻¹ᵁ U)` using `hU.preimage q`. Establish `hne₂` using `preimage_nonempty hg hne`.

Use `letI : Algebra (M₁.ringOn (U : Set M₁.Z)) (M₂.ringOn ((q ⁻¹ᵁ U : M₂.Z.Opens) : Set M₂.Z)) := ((algebraMap Ω₁ Ω₂).restrict _ _ fun _ ha => map_mem_ringOn hg ha).toAlgebra`. Use `haveI := isIntegral_ringOn hF hg hU hne`. Establish `hcoe : ∀ x : M₁.ringOn (U : Set M₁.Z), ((algebraMap (M₁.ringOn (U : Set M₁.Z)) (M₂.ringOn ((q ⁻¹ᵁ U : M₂.Z.Opens) : Set M₂.Z)) x : _) : Ω₂) = algebraMap Ω₁ Ω₂ x` using `fun _ => rfl`. Set `I : Ideal (M₂.ringOn ((q ⁻¹ᵁ U : M₂.Z.Opens) : Set M₂.Z))` to `{ carrier := {c | (c : Ω₂) * b ∈ M₂.ringOn ((q ⁻¹ᵁ U : M₂.Z.Opens) : Set M₂.Z)} add_mem' := fun {c d} hc hd => by`. Simplify using `only [Set.mem_setOf_eq, Subalgebra.coe_add, add_mul] at *`.

Conclude with `add_mem hc hd`. Use the proof step `zero_mem' := by`. Simplify using `only [Set.mem_setOf_eq, ZeroMemClass.coe_zero, zero_mul]`. Conclude with `zero_mem _`. Use the proof step `smul_mem' := fun c d hd => by`.

Simplify using `only [Set.mem_setOf_eq, smul_eq_mul, Subalgebra.coe_mul, mul_assoc] at *`. Conclude with `mul_mem c.2 hd }`. Establish `hz' : z₁ ∈ (U : Set M₁.Z)` using `hz`. Distinguish the cases in `hc : I.comap (algebraMap (M₁.ringOn (U : Set M₁.Z)) (M₂.ringOn ((q ⁻¹ᵁ U : M₂.Z.Opens) : Set M₂.Z))) ≤ pIdeal hz'`. It suffices to derive a contradiction.

Take `⟨Q, hIQ, hQ, hQp⟩` from `Ideal.exists_ideal_over_prime_of_isIntegral (pIdeal hz') I hc`. Take `⟨w, hwU, hwQ⟩` from `GlobalTheory.T.prime_of_ringOn_eq_nonunits_at_point _ _ M₂ _ hU₂ hne₂ Q hQ`. Establish `hqw : q w = z₁`. Use `GlobalTheory.T.model_affine_point_eq_of_inverse_mem_iff _ _ M₁ U hU (q w) z₁ hwU hz fun a ha ha0 => ?_` and prove the remaining obligations. Establish `h1 : a ∈ M₁.O (q w)` using `mem_ringOn.1 ha (q w) hwU`.

Establish `h2 : (⟨a, ha⟩ : M₁.ringOn (U : Set M₁.Z)) ∈ pIdeal hz' ↔ ¬ (a⁻¹ ∈ M₁.O z₁)`. Rewrite using `[mem_pIdeal]`. Simplify using `[ha0]`. Establish `h3 : (⟨a, ha⟩ : M₁.ringOn (U : Set M₁.Z)) ∈ pIdeal hz' ↔ ¬ ((algebraMap Ω₁ Ω₂ a)⁻¹ ∈ M₂.O w)`. Rewrite using `[← hQp, Ideal.mem_comap, hwQ, hcoe]`.

Simplify using `[ha0]`. Establish `h4 : a⁻¹ ∈ M₁.O (q w) ↔ (algebraMap Ω₁ Ω₂ a)⁻¹ ∈ M₂.O w` using `⟨map_inv_mem_O hg, inv_mem_O_of_map hg h1 ha0⟩`. Rewrite using `[h4, ← not_not (a := (algebraMap Ω₁ Ω₂ a)⁻¹ ∈ M₂.O w), ← h3, h2, not_not]`. Take `⟨c, hc', d, hd, hd0, hdinv, hbcd⟩` from `GlobalTheory.T.exists_fraction_ringOn_of_mem_modelLocalRing _ _ M₂ _ hU₂ w hwU b (hb w hqw)`. Establish `hdI : (⟨d, hd⟩ : M₂.ringOn ((q ⁻¹ᵁ U : M₂.Z.Opens) : Set M₂.Z)) ∈ I` using `by show d * b ∈ M₂.ringOn ((q ⁻¹ᵁ U : M₂.Z.Opens) : Set M₂.Z)`.

Rewrite using `[hbcd, mul_div_cancel₀ _ hd0]`. Conclude with `hc'`. Use `(hwQ ⟨d, hd⟩).1 (hIQ hdI)` as an intermediate fact. Simplify using `[hd0, hdinv] at this`. Rewrite `hc` using `[SetLike.not_le_iff_exists]`.

Take `⟨s, hsI, hsp⟩` from `hc`. Rewrite `hsp` using `[mem_pIdeal, not_not]`. Establish `hsI' : algebraMap Ω₁ Ω₂ s * b ∈ M₂.ringOn ((q ⁻¹ᵁ U : M₂.Z.Opens) : Set M₂.Z)` using `hsI`. Establish `h1 : IsIntegral (M₁.Z.presheaf.stalk z₁) (algebraMap Ω₁ Ω₂ s * b)`. Take `⟨f, hf, hcf, h0⟩` from `GlobalTheory.T.ringOn_preimage_integral_of_finite_model_map _ _ _ _ M₁ M₂ q hF hg U hU hne _ hsI'`.

Conclude with `isIntegral_of_poly halg f hf (fun i => ringOn_le_O hz' (hcf i)) h0`. Establish `h2` using `isIntegral_map_O halg hsp.2`. Establish `e : b = algebraMap Ω₁ Ω₂ (s : Ω₁)⁻¹ * (algebraMap Ω₁ Ω₂ s * b)`. Rewrite using `[← mul_assoc, ← map_mul, inv_mul_cancel₀ hsp.1, map_one, one_mul]`. Rewrite using `[e]`.

Conclude with `h2.mul h1`.
-/
theorem isIntegral_of_mem_O (hF : IsFinite q) (hg : M₂.pt ≫ q = spMap (algebraMap Ω₁ Ω₂) ≫ M₁.pt)
    (halg : ∀ x, algebraMap (M₁.Z.presheaf.stalk z₁) Ω₂ x = algebraMap Ω₁ Ω₂ (M₁.stalkHom z₁ x)) {b : Ω₂}
    (hb : ∀ z' : M₂.Z, q z' = z₁ → b ∈ M₂.O z') : IsIntegral (M₁.Z.presheaf.stalk z₁) b := by
  haveI := hF
  obtain ⟨U, hU, hz, -⟩ := exists_isAffineOpen_mem_and_subset (U := (⊤ : M₁.Z.Opens)) (x := z₁) trivial
  have hne : (U : Set M₁.Z).Nonempty := ⟨z₁, hz⟩
  have hU₂ : IsAffineOpen (q ⁻¹ᵁ U) := hU.preimage q
  have hne₂ := preimage_nonempty hg hne
  letI : Algebra (M₁.ringOn (U : Set M₁.Z)) (M₂.ringOn ((q ⁻¹ᵁ U : M₂.Z.Opens) : Set M₂.Z)) :=
    ((algebraMap Ω₁ Ω₂).restrict _ _ fun _ ha => map_mem_ringOn hg ha).toAlgebra
  haveI := isIntegral_ringOn hF hg hU hne
  have hcoe : ∀ x : M₁.ringOn (U : Set M₁.Z),
      ((algebraMap (M₁.ringOn (U : Set M₁.Z)) (M₂.ringOn ((q ⁻¹ᵁ U : M₂.Z.Opens) : Set M₂.Z)) x : _) : Ω₂) =
        algebraMap Ω₁ Ω₂ x := fun _ => rfl
  let I : Ideal (M₂.ringOn ((q ⁻¹ᵁ U : M₂.Z.Opens) : Set M₂.Z)) :=
    { carrier := {c | (c : Ω₂) * b ∈ M₂.ringOn ((q ⁻¹ᵁ U : M₂.Z.Opens) : Set M₂.Z)}
      add_mem' := fun {c d} hc hd => by
        simp only [Set.mem_setOf_eq, Subalgebra.coe_add, add_mul] at *
        exact add_mem hc hd
      zero_mem' := by
        simp only [Set.mem_setOf_eq, ZeroMemClass.coe_zero, zero_mul]
        exact zero_mem _
      smul_mem' := fun c d hd => by
        simp only [Set.mem_setOf_eq, smul_eq_mul, Subalgebra.coe_mul, mul_assoc] at *
        exact mul_mem c.2 hd }
  have hz' : z₁ ∈ (U : Set M₁.Z) := hz
  by_cases hc : I.comap (algebraMap (M₁.ringOn (U : Set M₁.Z))
      (M₂.ringOn ((q ⁻¹ᵁ U : M₂.Z.Opens) : Set M₂.Z))) ≤ pIdeal hz'
  · exfalso
    obtain ⟨Q, hIQ, hQ, hQp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (pIdeal hz') I hc
    obtain ⟨w, hwU, hwQ⟩ := GlobalTheory.T.prime_of_ringOn_eq_nonunits_at_point _ _ M₂ _ hU₂ hne₂ Q hQ
    have hqw : q w = z₁ := by
      refine GlobalTheory.T.model_affine_point_eq_of_inverse_mem_iff _ _ M₁ U hU (q w) z₁ hwU hz fun a ha ha0 => ?_
      have h1 : a ∈ M₁.O (q w) := mem_ringOn.1 ha (q w) hwU
      have h2 : (⟨a, ha⟩ : M₁.ringOn (U : Set M₁.Z)) ∈ pIdeal hz' ↔ ¬ (a⁻¹ ∈ M₁.O z₁) := by
        rw [mem_pIdeal]; simp [ha0]
      have h3 : (⟨a, ha⟩ : M₁.ringOn (U : Set M₁.Z)) ∈ pIdeal hz' ↔
          ¬ ((algebraMap Ω₁ Ω₂ a)⁻¹ ∈ M₂.O w) := by
        rw [← hQp, Ideal.mem_comap, hwQ, hcoe]
        simp [ha0]
      have h4 : a⁻¹ ∈ M₁.O (q w) ↔ (algebraMap Ω₁ Ω₂ a)⁻¹ ∈ M₂.O w :=
        ⟨map_inv_mem_O hg, inv_mem_O_of_map hg h1 ha0⟩
      rw [h4, ← not_not (a := (algebraMap Ω₁ Ω₂ a)⁻¹ ∈ M₂.O w), ← h3, h2, not_not]
    obtain ⟨c, hc', d, hd, hd0, hdinv, hbcd⟩ := GlobalTheory.T.exists_fraction_ringOn_of_mem_modelLocalRing _ _ M₂ _ hU₂ w hwU b (hb w hqw)
    have hdI : (⟨d, hd⟩ : M₂.ringOn ((q ⁻¹ᵁ U : M₂.Z.Opens) : Set M₂.Z)) ∈ I := by
      show d * b ∈ M₂.ringOn ((q ⁻¹ᵁ U : M₂.Z.Opens) : Set M₂.Z)
      rw [hbcd, mul_div_cancel₀ _ hd0]; exact hc'
    have := (hwQ ⟨d, hd⟩).1 (hIQ hdI)
    simp [hd0, hdinv] at this
  · rw [SetLike.not_le_iff_exists] at hc
    obtain ⟨s, hsI, hsp⟩ := hc
    rw [mem_pIdeal, not_not] at hsp
    have hsI' : algebraMap Ω₁ Ω₂ s * b ∈ M₂.ringOn ((q ⁻¹ᵁ U : M₂.Z.Opens) : Set M₂.Z) := hsI
    have h1 : IsIntegral (M₁.Z.presheaf.stalk z₁) (algebraMap Ω₁ Ω₂ s * b) := by
      obtain ⟨f, hf, hcf, h0⟩ := GlobalTheory.T.ringOn_preimage_integral_of_finite_model_map _ _ _ _ M₁ M₂ q hF hg U hU hne _ hsI'
      exact isIntegral_of_poly halg f hf (fun i => ringOn_le_O hz' (hcf i)) h0
    have h2 := isIntegral_map_O halg hsp.2
    have e : b = algebraMap Ω₁ Ω₂ (s : Ω₁)⁻¹ * (algebraMap Ω₁ Ω₂ s * b) := by
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hsp.1, map_one, one_mul]
    rw [e]; exact h2.mul h1

end Claim1

section Claim2
variable {o₁ Ω₁ o₂ Ω₂ : Type} [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂]
  [Algebra Ω₁ Ω₂] {M₁ : RatModel o₁ Ω₁} {M₂ : RatModel o₂ Ω₂} {q : M₂.Z ⟶ M₁.Z} {z₁ : M₁.Z}
  [Algebra (M₁.Z.presheaf.stalk z₁) Ω₂]

/- English proof (translation)
Take `⟨f, hf, hcf, h0⟩` from `GlobalTheory.T.ringOn_preimage_integral_of_finite_model_map _ _ _ _ M₁ M₂ q hF hg U hU ⟨z₁, hz⟩ c hc`. Conclude with `isIntegral_of_poly halg f hf (fun i => ringOn_le_O (U := (U : Set M₁.Z)) hz (hcf i)) h0`.
-/
theorem isIntegral_of_mem_ringOn (hF : IsFinite q) (hg : M₂.pt ≫ q = spMap (algebraMap Ω₁ Ω₂) ≫ M₁.pt)
    (halg : ∀ x, algebraMap (M₁.Z.presheaf.stalk z₁) Ω₂ x = algebraMap Ω₁ Ω₂ (M₁.stalkHom z₁ x))
    {U : M₁.Z.Opens} (hU : IsAffineOpen U) (hz : z₁ ∈ U) {c : Ω₂}
    (hc : c ∈ M₂.ringOn ((q ⁻¹ᵁ U : M₂.Z.Opens) : Set M₂.Z)) : IsIntegral (M₁.Z.presheaf.stalk z₁) c := by
  obtain ⟨f, hf, hcf, h0⟩ := GlobalTheory.T.ringOn_preimage_integral_of_finite_model_map _ _ _ _ M₁ M₂ q hF hg U hU ⟨z₁, hz⟩ c hc
  exact isIntegral_of_poly halg f hf (fun i => ringOn_le_O (U := (U : Set M₁.Z)) hz (hcf i)) h0

/- English proof (translation)
Use `haveI := hF`. Take `⟨U, hU, hz, -⟩` from `exists_isAffineOpen_mem_and_subset (U := (⊤ : M₁.Z.Opens)) (x := z₁) trivial`. Establish `hne : (U : Set M₁.Z).Nonempty` using `⟨z₁, hz⟩`. Establish `hU₂ : IsAffineOpen (q ⁻¹ᵁ U)` using `hU.preimage q`. Establish `hne₂` using `preimage_nonempty hg hne`.

Establish `hz' : z₁ ∈ (U : Set M₁.Z)` using `hz`. Set `ψ : M₂.ringOn ((q ⁻¹ᵁ U : M₂.Z.Opens) : Set M₂.Z) →+* integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂` to `(RingHom.id Ω₂).restrict _ _ fun c hc => (mem_integralClosure_iff _ _).2 (isIntegral_of_mem_ringOn hF hg halg hU hz hc)`. Use `haveI : (𝔷.comap ψ).IsPrime := Ideal.comap_isPrime _ _`. Take `⟨z₂, hz₂U, hz₂Q⟩` from `GlobalTheory.T.prime_of_ringOn_eq_nonunits_at_point _ _ M₂ _ hU₂ hne₂ (𝔷.comap ψ) inferInstance`. Establish `hQ : ∀ (c : Ω₂) (hc : c ∈ M₂.ringOn ((q ⁻¹ᵁ U : M₂.Z.Opens) : Set M₂.Z)), ψ ⟨c, hc⟩ ∈ 𝔷 ↔ (c = 0 ∨ c⁻¹ ∉ M₂.O z₂)` using `fun c hc => Ideal.mem_comap.symm.trans (hz₂Q ⟨c, hc⟩)`.

Establish `fwd : ∀ b : integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, b ∈ 𝔷 → ((b : Ω₂) = 0 ∨ (b : Ω₂)⁻¹ ∉ M₂.O z₂)`. Introduce `b hb`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Take `⟨hb0, hbinv⟩` from `hcon`.

Take `⟨c, hc, d, hd, hd0, hdinv, hcd⟩` from `GlobalTheory.T.exists_fraction_ringOn_of_mem_modelLocalRing _ _ M₂ _ hU₂ z₂ hz₂U _ hbinv`. Establish `e : ψ ⟨d, hd⟩ = ψ ⟨c, hc⟩ * b`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show d = c * (b : Ω₂)`. Rewrite `hcd` using `[eq_div_iff hd0]`.

Rewrite using `[← hcd, mul_comm ((b : Ω₂)⁻¹), mul_assoc, inv_mul_cancel₀ hb0, mul_one]`. Use `(hQ d hd).1 (e ▸ 𝔷.mul_mem_left _ hb)` as an intermediate fact. Simplify using `[hd0, hdinv] at this`. Establish `hq : q z₂ = z₁`. Use `GlobalTheory.T.model_affine_point_eq_of_inverse_mem_iff _ _ M₁ U hU (q z₂) z₁ hz₂U hz fun a ha ha0 => ?_` and prove the remaining obligations.

Establish `h1 : a ∈ M₁.O (q z₂)` using `mem_ringOn.1 ha (q z₂) hz₂U`. Establish `h4 : a⁻¹ ∈ M₁.O (q z₂) ↔ (algebraMap Ω₁ Ω₂ a)⁻¹ ∈ M₂.O z₂` using `⟨map_inv_mem_O hg, inv_mem_O_of_map hg h1 ha0⟩`. Establish `hm` using `map_mem_ringOn hg (q := q) ha`. Establish `h3 : ψ ⟨_, hm⟩ ∈ 𝔷 ↔ (algebraMap Ω₁ Ω₂ a)⁻¹ ∉ M₂.O z₂`. Rewrite using `[hQ]`.

Simplify using `[ha0]`. Establish `h5 : ψ ⟨_, hm⟩ ∈ 𝔷 ↔ a⁻¹ ∉ M₁.O z₁`. Prove the components needed by the constructor for the conclusion. Introduce `hin hinv`. Apply `h𝔷.ne_top` to reduce the goal to its premises.

Use `Ideal.eq_top_of_isUnit_mem _ hin ?_` and prove the remaining obligations. Use `IsUnit.of_mul_eq_one ⟨algebraMap Ω₁ Ω₂ a⁻¹, (mem_integralClosure_iff _ _).2 (isIntegral_map_O halg hinv)⟩ ?_` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Use `show algebraMap Ω₁ Ω₂ a * algebraMap Ω₁ Ω₂ a⁻¹ = 1`. Rewrite using `[← map_mul, mul_inv_cancel₀ ha0, map_one]`.

Introduce `hinv haveI : Algebra.IsIntegral (M₁.Z.presheaf.stalk z₁) (integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂) := ⟨fun x => integralClosure.isIntegral x⟩`. Establish `hm1` using `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := M₁.Z.presheaf.stalk z₁) 𝔷`. Establish `hm2` using `IsLocalRing.eq_maximalIdeal hm1`. Use `set s := (M₁.stalkEquiv z₁).symm ⟨a, ringOn_le_O hz' ha⟩ with hs`. Establish `hs1 : s ∈ IsLocalRing.maximalIdeal (M₁.Z.presheaf.stalk z₁)`.

Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Introduce `hu`. Use `(MulEquiv.isUnit_map (M₁.stalkEquiv z₁)).2 hu` as an intermediate fact. Rewrite `this` using `[hs, RingEquiv.apply_symm_apply, isUnit_O_iff]`. Conclude with `hinv this.2`.

Rewrite `hs1` using `[← hm2, Ideal.mem_comap]`. Establish `e : ψ ⟨_, hm⟩ = algebraMap _ _ s` using `Subtype.ext (by show algebraMap Ω₁ Ω₂ a = algebraMap (M₁.Z.presheaf.stalk z₁) Ω₂ s`. Rewrite using `[halg, ← coe_stalkEquiv, hs, RingEquiv.apply_symm_apply])`. Rewrite using `[e]`. Conclude with `hs1`.

Rewrite using `[h4, ← not_not (a := (algebraMap Ω₁ Ω₂ a)⁻¹ ∈ M₂.O z₂), ← h3, h5, not_not]`. Use `⟨z₂, hq, fun b => ⟨fwd b, fun hb => ?_⟩⟩` and prove the remaining obligations. Set `ι : integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂ →+* M₂.O z₂` to `(RingHom.id Ω₂).restrict _ _ fun c hc => mem_O_of_isIntegral hN hg halg ((mem_integralClosure_iff _ _).1 hc) hq`. Establish `hle : 𝔷 ≤ (IsLocalRing.maximalIdeal (M₂.O z₂)).comap ι`. Introduce `c hc`.

Rewrite using `[Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_O_iff]`. Introduce and unpack `⟨h0, hinv⟩`. Break down `fwd c hc with h | h` into its components or cases. Conclude with `h0 h`. Conclude with `h hinv`.

Establish `heq` using `h𝔷.eq_of_le (Ideal.comap_ne_top _ (IsLocalRing.maximalIdeal.isMaximal _).ne_top) hle`. Rewrite using `[heq, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_O_iff]`. Introduce and unpack `⟨h0, hinv⟩`. Break down `hb with h | h` into its components or cases. Conclude with `h0 h`.

Conclude with `h hinv`.
-/
theorem maximal_point (hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M₂.Z) (hF : IsFinite q)
    (hg : M₂.pt ≫ q = spMap (algebraMap Ω₁ Ω₂) ≫ M₁.pt)
    (halg : ∀ x, algebraMap (M₁.Z.presheaf.stalk z₁) Ω₂ x = algebraMap Ω₁ Ω₂ (M₁.stalkHom z₁ x))
    (𝔷 : Ideal (integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂)) (h𝔷 : 𝔷.IsMaximal) :
    ∃ z₂ : M₂.Z, q z₂ = z₁ ∧ ∀ b : integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂,
      b ∈ 𝔷 ↔ ((b : Ω₂) = 0 ∨ (b : Ω₂)⁻¹ ∉ M₂.O z₂) := by
  haveI := hF
  obtain ⟨U, hU, hz, -⟩ := exists_isAffineOpen_mem_and_subset (U := (⊤ : M₁.Z.Opens)) (x := z₁) trivial
  have hne : (U : Set M₁.Z).Nonempty := ⟨z₁, hz⟩
  have hU₂ : IsAffineOpen (q ⁻¹ᵁ U) := hU.preimage q
  have hne₂ := preimage_nonempty hg hne
  have hz' : z₁ ∈ (U : Set M₁.Z) := hz
  let ψ : M₂.ringOn ((q ⁻¹ᵁ U : M₂.Z.Opens) : Set M₂.Z) →+* integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂ :=
    (RingHom.id Ω₂).restrict _ _ fun c hc =>
      (mem_integralClosure_iff _ _).2 (isIntegral_of_mem_ringOn hF hg halg hU hz hc)
  haveI : (𝔷.comap ψ).IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨z₂, hz₂U, hz₂Q⟩ := GlobalTheory.T.prime_of_ringOn_eq_nonunits_at_point _ _ M₂ _ hU₂ hne₂ (𝔷.comap ψ) inferInstance
  have hQ : ∀ (c : Ω₂) (hc : c ∈ M₂.ringOn ((q ⁻¹ᵁ U : M₂.Z.Opens) : Set M₂.Z)),
      ψ ⟨c, hc⟩ ∈ 𝔷 ↔ (c = 0 ∨ c⁻¹ ∉ M₂.O z₂) :=
    fun c hc => Ideal.mem_comap.symm.trans (hz₂Q ⟨c, hc⟩)
  have fwd : ∀ b : integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, b ∈ 𝔷 →
      ((b : Ω₂) = 0 ∨ (b : Ω₂)⁻¹ ∉ M₂.O z₂) := by
    intro b hb
    by_contra hcon
    push_neg at hcon
    obtain ⟨hb0, hbinv⟩ := hcon
    obtain ⟨c, hc, d, hd, hd0, hdinv, hcd⟩ := GlobalTheory.T.exists_fraction_ringOn_of_mem_modelLocalRing _ _ M₂ _ hU₂ z₂ hz₂U _ hbinv
    have e : ψ ⟨d, hd⟩ = ψ ⟨c, hc⟩ * b := by
      apply Subtype.ext
      show d = c * (b : Ω₂)
      rw [eq_div_iff hd0] at hcd
      rw [← hcd, mul_comm ((b : Ω₂)⁻¹), mul_assoc, inv_mul_cancel₀ hb0, mul_one]
    have := (hQ d hd).1 (e ▸ 𝔷.mul_mem_left _ hb)
    simp [hd0, hdinv] at this
  have hq : q z₂ = z₁ := by
    refine GlobalTheory.T.model_affine_point_eq_of_inverse_mem_iff _ _ M₁ U hU (q z₂) z₁ hz₂U hz fun a ha ha0 => ?_
    have h1 : a ∈ M₁.O (q z₂) := mem_ringOn.1 ha (q z₂) hz₂U
    have h4 : a⁻¹ ∈ M₁.O (q z₂) ↔ (algebraMap Ω₁ Ω₂ a)⁻¹ ∈ M₂.O z₂ :=
      ⟨map_inv_mem_O hg, inv_mem_O_of_map hg h1 ha0⟩
    have hm := map_mem_ringOn hg (q := q) ha
    have h3 : ψ ⟨_, hm⟩ ∈ 𝔷 ↔ (algebraMap Ω₁ Ω₂ a)⁻¹ ∉ M₂.O z₂ := by
      rw [hQ]; simp [ha0]
    have h5 : ψ ⟨_, hm⟩ ∈ 𝔷 ↔ a⁻¹ ∉ M₁.O z₁ := by
      constructor
      · intro hin hinv
        apply h𝔷.ne_top
        refine Ideal.eq_top_of_isUnit_mem _ hin ?_
        refine IsUnit.of_mul_eq_one ⟨algebraMap Ω₁ Ω₂ a⁻¹,
          (mem_integralClosure_iff _ _).2 (isIntegral_map_O halg hinv)⟩ ?_
        apply Subtype.ext
        show algebraMap Ω₁ Ω₂ a * algebraMap Ω₁ Ω₂ a⁻¹ = 1
        rw [← map_mul, mul_inv_cancel₀ ha0, map_one]
      · intro hinv
        haveI : Algebra.IsIntegral (M₁.Z.presheaf.stalk z₁) (integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂) :=
          ⟨fun x => integralClosure.isIntegral x⟩
        have hm1 := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := M₁.Z.presheaf.stalk z₁) 𝔷
        have hm2 := IsLocalRing.eq_maximalIdeal hm1
        set s := (M₁.stalkEquiv z₁).symm ⟨a, ringOn_le_O hz' ha⟩ with hs
        have hs1 : s ∈ IsLocalRing.maximalIdeal (M₁.Z.presheaf.stalk z₁) := by
          rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
          intro hu
          have := (MulEquiv.isUnit_map (M₁.stalkEquiv z₁)).2 hu
          rw [hs, RingEquiv.apply_symm_apply, isUnit_O_iff] at this
          exact hinv this.2
        rw [← hm2, Ideal.mem_comap] at hs1
        have e : ψ ⟨_, hm⟩ = algebraMap _ _ s := Subtype.ext (by
          show algebraMap Ω₁ Ω₂ a = algebraMap (M₁.Z.presheaf.stalk z₁) Ω₂ s
          rw [halg, ← coe_stalkEquiv, hs, RingEquiv.apply_symm_apply])
        rw [e]; exact hs1
    rw [h4, ← not_not (a := (algebraMap Ω₁ Ω₂ a)⁻¹ ∈ M₂.O z₂), ← h3, h5, not_not]
  refine ⟨z₂, hq, fun b => ⟨fwd b, fun hb => ?_⟩⟩
  let ι : integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂ →+* M₂.O z₂ :=
    (RingHom.id Ω₂).restrict _ _ fun c hc =>
      mem_O_of_isIntegral hN hg halg ((mem_integralClosure_iff _ _).1 hc) hq
  have hle : 𝔷 ≤ (IsLocalRing.maximalIdeal (M₂.O z₂)).comap ι := by
    intro c hc
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_O_iff]
    rintro ⟨h0, hinv⟩
    rcases fwd c hc with h | h
    · exact h0 h
    · exact h hinv
  have heq := h𝔷.eq_of_le (Ideal.comap_ne_top _ (IsLocalRing.maximalIdeal.isMaximal _).ne_top) hle
  rw [heq, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_O_iff]
  rintro ⟨h0, hinv⟩
  rcases hb with h | h
  · exact h0 h
  · exact h hinv

/- English proof (translation)
Use `haveI := hF`. Take `⟨U, hU, hz, -⟩` from `exists_isAffineOpen_mem_and_subset (U := (⊤ : M₁.Z.Opens)) (x := z₁) trivial`. Use `GlobalTheory.T.model_affine_point_eq_of_inverse_mem_iff _ _ M₂ _ (hU.preimage q) z₂ z₂' (show q z₂ ∈ U by rw [h₂]; exact hz) (show q z₂' ∈ U by rw [h₂']; exact hz) fun a ha _ => h ⟨a, (mem_integralClosure_iff _ _).2 (isIntegral_of_mem_ringOn hF hg halg hU hz ha)⟩` and prove the remaining obligations.
-/
theorem point_unique (hF : IsFinite q) (hg : M₂.pt ≫ q = spMap (algebraMap Ω₁ Ω₂) ≫ M₁.pt)
    (halg : ∀ x, algebraMap (M₁.Z.presheaf.stalk z₁) Ω₂ x = algebraMap Ω₁ Ω₂ (M₁.stalkHom z₁ x))
    {z₂ z₂' : M₂.Z} (h₂ : q z₂ = z₁) (h₂' : q z₂' = z₁)
    (h : ∀ b : integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, (b : Ω₂)⁻¹ ∈ M₂.O z₂ ↔ (b : Ω₂)⁻¹ ∈ M₂.O z₂') :
    z₂ = z₂' := by
  haveI := hF
  obtain ⟨U, hU, hz, -⟩ := exists_isAffineOpen_mem_and_subset (U := (⊤ : M₁.Z.Opens)) (x := z₁) trivial
  refine GlobalTheory.T.model_affine_point_eq_of_inverse_mem_iff _ _ M₂ _ (hU.preimage q) z₂ z₂' (show q z₂ ∈ U by rw [h₂]; exact hz)
    (show q z₂' ∈ U by rw [h₂']; exact hz) fun a ha _ => h ⟨a, (mem_integralClosure_iff _ _).2
      (isIntegral_of_mem_ringOn hF hg halg hU hz ha)⟩

end Claim2

section Claim4
variable {o₁ Ω₁ o₂ Ω₂ : Type} [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂]
  [Algebra Ω₁ Ω₂] {M₁ : RatModel o₁ Ω₁} {M₂ : RatModel o₂ Ω₂} {q : M₂.Z ⟶ M₁.Z} {z₁ : M₁.Z}
  [Algebra (M₁.Z.presheaf.stalk z₁) Ω₂]

/- English proof (translation)
Use `letI : Algebra (M₁.Z.presheaf.stalk z₁) (PadicAlgCl p) := (e.comp (algebraMap (M₁.Z.presheaf.stalk z₁) (integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂))).toAlgebra`. Set `eA : integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂ →ₐ[M₁.Z.presheaf.stalk z₁] PadicAlgCl p` to `{ e with commutes' := fun _ => rfl }`. Establish `h1 : IsIntegral (M₁.Z.presheaf.stalk z₁) (e b)` using `(integralClosure.isIntegral b).map eA`. Use `letI : Algebra (M₁.Z.presheaf.stalk z₁) (OO p) := ((e.comp (algebraMap (M₁.Z.presheaf.stalk z₁) (integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂))).codRestrict (OO p) fun a => by show e (algebraMap _ _ a) ∈ OO p`. Rewrite using `[he, mem_OO_iff]`.

Conclude with `norm_val_le_one hy₁ (M₁.stalkEquiv z₁ a).2).toAlgebra`. Use `haveI : IsScalarTower (M₁.Z.presheaf.stalk z₁) (OO p) (PadicAlgCl p) := IsScalarTower.of_algebraMap_eq fun _ => rfl`. Take `⟨y, hy⟩` from `IsIntegrallyClosed.isIntegral_iff.1 (h1.tower_top (A := OO p))`. Conclude with `hy ▸ y.2`.
-/
theorem mem_OO_of_ext (halg : ∀ x, algebraMap (M₁.Z.presheaf.stalk z₁) Ω₂ x = algebraMap Ω₁ Ω₂ (M₁.stalkHom z₁ x))
    (p : ℕ) [Fact p.Prime] (y₁ : Sp (OO p) ⟶ M₁.Z) (hy₁ : y₁ (cPt p) = z₁)
    (e : integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂ →+* PadicAlgCl p)
    (he : ∀ a, e (algebraMap (M₁.Z.presheaf.stalk z₁) _ a) = M₁.val (gPt p ≫ y₁) (M₁.stalkHom z₁ a))
    (b : integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂) : e b ∈ OO p := by
  letI : Algebra (M₁.Z.presheaf.stalk z₁) (PadicAlgCl p) :=
    (e.comp (algebraMap (M₁.Z.presheaf.stalk z₁) (integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂))).toAlgebra
  let eA : integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂ →ₐ[M₁.Z.presheaf.stalk z₁] PadicAlgCl p :=
    { e with commutes' := fun _ => rfl }
  have h1 : IsIntegral (M₁.Z.presheaf.stalk z₁) (e b) := (integralClosure.isIntegral b).map eA
  letI : Algebra (M₁.Z.presheaf.stalk z₁) (OO p) :=
    ((e.comp (algebraMap (M₁.Z.presheaf.stalk z₁) (integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂))).codRestrict
      (OO p) fun a => by
        show e (algebraMap _ _ a) ∈ OO p
        rw [he, mem_OO_iff]
        exact norm_val_le_one hy₁ (M₁.stalkEquiv z₁ a).2).toAlgebra
  haveI : IsScalarTower (M₁.Z.presheaf.stalk z₁) (OO p) (PadicAlgCl p) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 (h1.tower_top (A := OO p))
  exact hy ▸ y.2

/- English proof (translation)
Use `haveI := hF`. Take `⟨U, hU, hz, -⟩` from `exists_isAffineOpen_mem_and_subset (U := (⊤ : M₁.Z.Opens)) (x := z₁) trivial`. Establish `hne : (U : Set M₁.Z).Nonempty` using `⟨z₁, hz⟩`. Establish `hU₂ : IsAffineOpen (q ⁻¹ᵁ U)` using `hU.preimage q`. Establish `hne₂` using `preimage_nonempty hg hne`.

Set `ψ : M₂.ringOn ((q ⁻¹ᵁ U : M₂.Z.Opens) : Set M₂.Z) →+* integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂` to `(RingHom.id Ω₂).restrict _ _ fun c hc => (mem_integralClosure_iff _ _).2 (isIntegral_of_mem_ringOn hF hg halg hU hz hc)`. Set `e₀ : M₂.ringOn ((q ⁻¹ᵁ U : M₂.Z.Opens) : Set M₂.Z) →+* OO p` to `(e.comp ψ).codRestrict (OO p) fun c => mem_OO_of_ext halg p y₁ hy₁ e he (ψ c)`. Set `φ : Γ(M₂.Z, q ⁻¹ᵁ U) ⟶ CommRingCat.of (OO p)` to `CommRingCat.ofHom (e₀.comp (M₂.sectionsEquiv _ hne₂).toRingHom)`. Set `y : Sp (OO p) ⟶ M₂.Z` to `Spec.map φ ≫ hU₂.fromSpec`. Establish `hyU : ⊤ ≤ y ⁻¹ᵁ (q ⁻¹ᵁ U)` using `le_preimage_specMap_fromSpec hU₂ φ`.

Establish `hyv : ∀ f, valR y (q ⁻¹ᵁ U) f = φ.hom f` using `fun f => by`. Rewrite using `[valR_eq y _ hyU, valMap_specMap_fromSpec]`. Establish `hr : Set.range (gPt p ≫ y) ⊆ ((q ⁻¹ᵁ U : M₂.Z.Opens) : Set M₂.Z)` using `(top_le_preimage_iff _ _).1 (le_preimage_comp _ y hyU (le_preimage_top _))`. Establish `hval : ∀ c (hc : c ∈ M₂.ringOn ((q ⁻¹ᵁ U : M₂.Z.Opens) : Set M₂.Z)), M₂.val (gPt p ≫ y) c = e (ψ ⟨c, hc⟩)`. Introduce `c hc`.

Take `⟨f, rfl⟩` from `(mem_ringOn_iff_exists hne₂).1 hc`. Rewrite using `[val_valF hr f, valF_eq_valR, valR_spMap_comp _ y _ hyU, hyv]`. Use `show e (ψ (M₂.sectionsEquiv _ hne₂ f)) = e (ψ ⟨_, hc⟩)`. Use `congr 2`. Conclude with `Subtype.ext (coe_sectionsEquiv _ hne₂ f)`.

Establish `hy₁U : ⊤ ≤ y₁ ⁻¹ᵁ U` using `(le_preimage_iff y₁ U).2 (hy₁ ▸ hz)`. Establish `hr₁ : Set.range (gPt p ≫ y₁) ⊆ (U : Set M₁.Z)` using `(top_le_preimage_iff _ _).1 (le_preimage_comp _ y₁ hy₁U (le_preimage_top _))`. Establish `hyq : y ≫ q = y₁`. Use `ext_of_valR hU (le_preimage_comp y q le_rfl hyU) hy₁U fun f => ?_` and prove the remaining obligations. Rewrite using `[valR_comp, hyv]`.

Apply `Subtype.ext` to reduce the goal to its premises. Establish `h1 : ((φ.hom ((q.app U).hom f) : OO p) : PadicAlgCl p) = e (algebraMap _ _ (M₁.Z.presheaf.germ U z₁ hz f))` using `by show e (ψ (M₂.sectionsEquiv _ hne₂ ((q.app U).hom f))) = _`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show (M₂.sectionsEquiv _ hne₂ ((q.app U).hom f) : Ω₂) = algebraMap (M₁.Z.presheaf.stalk z₁) Ω₂ (M₁.Z.presheaf.germ U z₁ hz f)`.

Rewrite using `[coe_sectionsEquiv, valF_app hg hne, halg, stalkHom_germ]`. Rewrite using `[h1, he, stalkHom_germ, val_valF hr₁ f, valF_eq_valR, valR_spMap_comp _ y₁ U hy₁U]`. Both sides reduce to the same expression. Use `⟨y, hyq, fun b => ?_⟩` and prove the remaining obligations. Establish `hq2 : q (y (cPt p)) = z₁`.

Rewrite using `[← hy₁, ← hyq]`. Both sides reduce to the same expression. Establish `hz₂U : y (cPt p) ∈ q ⁻¹ᵁ U` using `(le_preimage_iff y _).1 hyU`. Establish `hb2 : (b : Ω₂) ∈ M₂.O (y (cPt p))` using `mem_O_of_isIntegral hN hg halg ((mem_integralClosure_iff _ _).1 b.2) hq2`. Take `⟨c, hc, d, hd, hd0, hdinv, hbcd⟩` from `GlobalTheory.T.exists_fraction_ringOn_of_mem_modelLocalRing _ _ M₂ _ hU₂ _ hz₂U _ hb2`.

Establish `hspec : ∀ w, (gPt p ≫ y) w ⤳ y (cPt p)` using `gPt_specializes rfl`. Establish `hdO : d ∈ M₂.O (y (cPt p))` using `mem_ringOn.1 hd _ hz₂U`. Establish `hbd : (b : Ω₂) * d = c` using `by rw [hbcd, div_mul_cancel₀ _ hd0]`. Establish `hv1 : M₂.val (gPt p ≫ y) c = M₂.val (gPt p ≫ y) b * M₂.val (gPt p ≫ y) d`. Rewrite using `[← hbd]`.

Conclude with `RatModel.val_mul hspec hb2 hdO`. Establish `hv2 : M₂.val (gPt p ≫ y) d ≠ 0`. Introduce `h0`. Use `RatModel.val_mul hspec hdO hdinv` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel₀ hd0, RatModel.val_one, h0, zero_mul]`.

Conclude with `one_ne_zero this`. Establish `he1 : e (ψ ⟨c, hc⟩) = e b * e (ψ ⟨d, hd⟩)`. Rewrite using `[← map_mul]`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises.

Use `show c = (b : Ω₂) * d`. Conclude with `hbd.symm`. Rewrite `hv1` using `[hval c hc, hval d hd]`. Conclude with `mul_right_cancel₀ (by rw [← hval d hd]; exact hv2) (he1.symm.trans hv1)`.
-/
theorem lift_point (hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M₂.Z) (hF : IsFinite q)
    (hg : M₂.pt ≫ q = spMap (algebraMap Ω₁ Ω₂) ≫ M₁.pt)
    (halg : ∀ x, algebraMap (M₁.Z.presheaf.stalk z₁) Ω₂ x = algebraMap Ω₁ Ω₂ (M₁.stalkHom z₁ x))
    (p : ℕ) [Fact p.Prime] (y₁ : Sp (OO p) ⟶ M₁.Z) (hy₁ : y₁ (cPt p) = z₁)
    (e : integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂ →+* PadicAlgCl p)
    (he : ∀ a, e (algebraMap (M₁.Z.presheaf.stalk z₁) _ a) = M₁.val (gPt p ≫ y₁) (M₁.stalkHom z₁ a)) :
    ∃ y : Sp (OO p) ⟶ M₂.Z, y ≫ q = y₁ ∧ ∀ b, e b = M₂.val (gPt p ≫ y) (b : Ω₂) := by
  haveI := hF
  obtain ⟨U, hU, hz, -⟩ := exists_isAffineOpen_mem_and_subset (U := (⊤ : M₁.Z.Opens)) (x := z₁) trivial
  have hne : (U : Set M₁.Z).Nonempty := ⟨z₁, hz⟩
  have hU₂ : IsAffineOpen (q ⁻¹ᵁ U) := hU.preimage q
  have hne₂ := preimage_nonempty hg hne
  let ψ : M₂.ringOn ((q ⁻¹ᵁ U : M₂.Z.Opens) : Set M₂.Z) →+* integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂ :=
    (RingHom.id Ω₂).restrict _ _ fun c hc =>
      (mem_integralClosure_iff _ _).2 (isIntegral_of_mem_ringOn hF hg halg hU hz hc)
  let e₀ : M₂.ringOn ((q ⁻¹ᵁ U : M₂.Z.Opens) : Set M₂.Z) →+* OO p :=
    (e.comp ψ).codRestrict (OO p) fun c => mem_OO_of_ext halg p y₁ hy₁ e he (ψ c)
  let φ : Γ(M₂.Z, q ⁻¹ᵁ U) ⟶ CommRingCat.of (OO p) :=
    CommRingCat.ofHom (e₀.comp (M₂.sectionsEquiv _ hne₂).toRingHom)
  let y : Sp (OO p) ⟶ M₂.Z := Spec.map φ ≫ hU₂.fromSpec
  have hyU : ⊤ ≤ y ⁻¹ᵁ (q ⁻¹ᵁ U) := le_preimage_specMap_fromSpec hU₂ φ
  have hyv : ∀ f, valR y (q ⁻¹ᵁ U) f = φ.hom f := fun f => by
    rw [valR_eq y _ hyU, valMap_specMap_fromSpec]
  have hr : Set.range (gPt p ≫ y) ⊆ ((q ⁻¹ᵁ U : M₂.Z.Opens) : Set M₂.Z) :=
    (top_le_preimage_iff _ _).1 (le_preimage_comp _ y hyU (le_preimage_top _))
  have hval : ∀ c (hc : c ∈ M₂.ringOn ((q ⁻¹ᵁ U : M₂.Z.Opens) : Set M₂.Z)),
      M₂.val (gPt p ≫ y) c = e (ψ ⟨c, hc⟩) := by
    intro c hc
    obtain ⟨f, rfl⟩ := (mem_ringOn_iff_exists hne₂).1 hc
    rw [val_valF hr f, valF_eq_valR, valR_spMap_comp _ y _ hyU, hyv]
    show e (ψ (M₂.sectionsEquiv _ hne₂ f)) = e (ψ ⟨_, hc⟩)
    congr 2
    exact Subtype.ext (coe_sectionsEquiv _ hne₂ f)
  have hy₁U : ⊤ ≤ y₁ ⁻¹ᵁ U := (le_preimage_iff y₁ U).2 (hy₁ ▸ hz)
  have hr₁ : Set.range (gPt p ≫ y₁) ⊆ (U : Set M₁.Z) :=
    (top_le_preimage_iff _ _).1 (le_preimage_comp _ y₁ hy₁U (le_preimage_top _))
  have hyq : y ≫ q = y₁ := by
    refine ext_of_valR hU (le_preimage_comp y q le_rfl hyU) hy₁U fun f => ?_
    rw [valR_comp, hyv]
    apply Subtype.ext
    have h1 : ((φ.hom ((q.app U).hom f) : OO p) : PadicAlgCl p) =
        e (algebraMap _ _ (M₁.Z.presheaf.germ U z₁ hz f)) := by
      show e (ψ (M₂.sectionsEquiv _ hne₂ ((q.app U).hom f))) = _
      congr 1
      apply Subtype.ext
      show (M₂.sectionsEquiv _ hne₂ ((q.app U).hom f) : Ω₂) =
        algebraMap (M₁.Z.presheaf.stalk z₁) Ω₂ (M₁.Z.presheaf.germ U z₁ hz f)
      rw [coe_sectionsEquiv, valF_app hg hne, halg, stalkHom_germ]
    rw [h1, he, stalkHom_germ, val_valF hr₁ f, valF_eq_valR, valR_spMap_comp _ y₁ U hy₁U]
    rfl
  refine ⟨y, hyq, fun b => ?_⟩
  have hq2 : q (y (cPt p)) = z₁ := by
    rw [← hy₁, ← hyq]
    rfl
  have hz₂U : y (cPt p) ∈ q ⁻¹ᵁ U := (le_preimage_iff y _).1 hyU
  have hb2 : (b : Ω₂) ∈ M₂.O (y (cPt p)) :=
    mem_O_of_isIntegral hN hg halg ((mem_integralClosure_iff _ _).1 b.2) hq2
  obtain ⟨c, hc, d, hd, hd0, hdinv, hbcd⟩ := GlobalTheory.T.exists_fraction_ringOn_of_mem_modelLocalRing _ _ M₂ _ hU₂ _ hz₂U _ hb2
  have hspec : ∀ w, (gPt p ≫ y) w ⤳ y (cPt p) := gPt_specializes rfl
  have hdO : d ∈ M₂.O (y (cPt p)) := mem_ringOn.1 hd _ hz₂U
  have hbd : (b : Ω₂) * d = c := by rw [hbcd, div_mul_cancel₀ _ hd0]
  have hv1 : M₂.val (gPt p ≫ y) c = M₂.val (gPt p ≫ y) b * M₂.val (gPt p ≫ y) d := by
    rw [← hbd]; exact RatModel.val_mul hspec hb2 hdO
  have hv2 : M₂.val (gPt p ≫ y) d ≠ 0 := by
    intro h0
    have := RatModel.val_mul hspec hdO hdinv
    rw [mul_inv_cancel₀ hd0, RatModel.val_one, h0, zero_mul] at this
    exact one_ne_zero this
  have he1 : e (ψ ⟨c, hc⟩) = e b * e (ψ ⟨d, hd⟩) := by
    rw [← map_mul]
    congr 1
    apply Subtype.ext
    show c = (b : Ω₂) * d
    exact hbd.symm
  rw [hval c hc, hval d hd] at hv1
  exact mul_right_cancel₀ (by rw [← hval d hd]; exact hv2) (he1.symm.trans hv1)

end Claim4

end GlobalTheory.Poinc.FinPts

end

open GlobalTheory.Poinc.FinPts in

/- English proof (translation)
Introduce `o₁ Ω₁ o₂ Ω₂ _ _ _ _ _ _ _ M₁ M₂ q hN hF hg z₁`. Use `letI : Algebra (M₁.Z.presheaf.stalk z₁) Ω₂ := ((algebraMap Ω₁ Ω₂).comp (M₁.stalkHom z₁)).toAlgebra`. Establish `halg : ∀ x, algebraMap (M₁.Z.presheaf.stalk z₁) Ω₂ x = algebraMap Ω₁ Ω₂ (M₁.stalkHom z₁ x)` using `fun _ => rfl`. Conclude with `⟨fun b => (mem_integralClosure_iff _ _).trans ⟨fun hb z' hz' => mem_O_of_isIntegral hN hg halg hb hz', isIntegral_of_mem_O hF hg halg⟩, fun 𝔷 h𝔷 => maximal_point hN hF hg halg 𝔷 h𝔷, fun z₂ z₂' h₂ h₂' h => point_unique hF hg halg h₂ h₂' h, fun p _ y₁ hy₁ e he => lift_point hN hF h …`.
-/
theorem GlobalTheory.Poinc.integralClosure_stalk_fibre : ∀ (o₁ Ω₁ o₂ Ω₂ : Type) [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] [Algebra Ω₁ Ω₂] (M₁ : RatModel o₁ Ω₁) (M₂ : RatModel o₂ Ω₂) (q : M₂.Z ⟶ M₁.Z), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M₂.Z → IsFinite q → M₂.pt ≫ q = spMap (algebraMap Ω₁ Ω₂) ≫ M₁.pt → ∀ z₁ : M₁.Z, letI : Algebra (M₁.Z.presheaf.stalk z₁) Ω₂ := ((algebraMap Ω₁ Ω₂).comp (M₁.stalkHom z₁)).toAlgebra; (∀ b : Ω₂, b ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂ ↔ ∀ z' : M₂.Z, q z' = z₁ → b ∈ M₂.O z') ∧ (∀ 𝔷 : Ideal (integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂), 𝔷.IsMaximal → ∃ z₂ : M₂.Z, q z₂ = z₁ ∧ ∀ b : integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, b ∈ 𝔷 ↔ ((b : Ω₂) = 0 ∨ (b : Ω₂)⁻¹ ∉ M₂.O z₂)) ∧ (∀ z₂ z₂' : M₂.Z, q z₂ = z₁ → q z₂' = z₁ → (∀ b : integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, (b : Ω₂)⁻¹ ∈ M₂.O z₂ ↔ (b : Ω₂)⁻¹ ∈ M₂.O z₂') → z₂ = z₂') ∧ ∀ (p : ℕ) [Fact p.Prime] (y₁ : Sp (OO p) ⟶ M₁.Z), y₁ (cPt p) = z₁ → ∀ e : integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂ →+* PadicAlgCl p, (∀ a, e (algebraMap (M₁.Z.presheaf.stalk z₁) _ a) = M₁.val (gPt p ≫ y₁) (M₁.stalkHom z₁ a)) → ∃ y : Sp (OO p) ⟶ M₂.Z, y ≫ q = y₁ ∧ ∀ b, e b = M₂.val (gPt p ≫ y) (b : Ω₂) := by
  intro o₁ Ω₁ o₂ Ω₂ _ _ _ _ _ _ _ M₁ M₂ q hN hF hg z₁
  letI : Algebra (M₁.Z.presheaf.stalk z₁) Ω₂ := ((algebraMap Ω₁ Ω₂).comp (M₁.stalkHom z₁)).toAlgebra
  have halg : ∀ x, algebraMap (M₁.Z.presheaf.stalk z₁) Ω₂ x = algebraMap Ω₁ Ω₂ (M₁.stalkHom z₁ x) := fun _ => rfl
  exact ⟨fun b => (mem_integralClosure_iff _ _).trans
      ⟨fun hb z' hz' => mem_O_of_isIntegral hN hg halg hb hz', isIntegral_of_mem_O hF hg halg⟩,
    fun 𝔷 h𝔷 => maximal_point hN hF hg halg 𝔷 h𝔷,
    fun z₂ z₂' h₂ h₂' h => point_unique hF hg halg h₂ h₂' h,
    fun p _ y₁ hy₁ e he => lift_point hN hF hg halg p y₁ hy₁ e he⟩
