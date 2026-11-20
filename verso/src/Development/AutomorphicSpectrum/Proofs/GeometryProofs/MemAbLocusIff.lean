import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSmoothHermTrivLine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Chg

/- English proof (translation)
Introduce `hf`. Apply `hf` to reduce the goal to its premises. Establish `hs : genMap ξ ⟨centre z, h⟩ (r : X.presheaf.stalk (centre z)) = (r : Ω)` using `map_natCast _ r`. Establish `hz : (Scheme.stalkClosedPointTo z).hom (r : X.presheaf.stalk (centre z)) = (r : ℂ)` using `map_natCast _ r`. Establish `hu : IsUnit (r : X.presheaf.stalk (centre z))` using `CxVal.isUnit _ (by`.

Rewrite using `[hz]`. Conclude with `hr.ne_zero)` after adjusting the coercions. Use `⟨Nat.cast_ne_zero.2 hr.ne_zero, ⟨_, hs⟩, ?_⟩` and prove the remaining obligations. Take `⟨u, hu'⟩` from `hu`. Use `⟨(u⁻¹ : (X.presheaf.stalk (centre z))ˣ).val, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_units_inv, hu', hs]`.
-/
theorem not_inFibre {X : Scheme.{0}} {Ω : Type} [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (z : Spec (CommRingCat.of ℂ) ⟶ X) (h : genPt ξ ⤳ centre z) {r : ℕ} (hr : r.Prime) :
    ¬ InFibre ξ r ⟨centre z, h⟩ := by
  intro hf
  apply hf
  have hs : genMap ξ ⟨centre z, h⟩ (r : X.presheaf.stalk (centre z)) = (r : Ω) := map_natCast _ r
  have hz : (Scheme.stalkClosedPointTo z).hom (r : X.presheaf.stalk (centre z)) = (r : ℂ) := map_natCast _ r
  have hu : IsUnit (r : X.presheaf.stalk (centre z)) := CxVal.isUnit _ (by
    rw [hz]; exact_mod_cast hr.ne_zero)
  refine ⟨Nat.cast_ne_zero.2 hr.ne_zero, ⟨_, hs⟩, ?_⟩
  obtain ⟨u, hu'⟩ := hu
  refine ⟨(u⁻¹ : (X.presheaf.stalk (centre z))ˣ).val, ?_⟩
  rw [map_units_inv, hu', hs]

section Cover

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {S₀ S : Finset ℕ} {Ω₀ Ω : Type} [Field Ω₀] [Field Ω] {K₀ K : Type} [Fintype K₀] [Fintype K]
  {J₀ : K₀ → Type} {J : K → Type} {y₀ : (Σ k, J₀ k) → Ω₀} {y : (Σ k, J k) → Ω}

/- English proof (translation)
Substitute `e` using the available equality. Both sides reduce to the same expression.
-/
theorem sabMap_cast_φ {S₁ S₂ : Scheme.{0}} {t₁ : SAB H S₁} {t₂ : SAB H S₂} {f f' : S₁ ⟶ S₂} (e : f = f')
    (m : SABMap t₁ t₂ f) : (e ▸ m : SABMap t₁ t₂ f').φ = m.φ := by
  subst e
  rfl

/- English proof (translation)
Take `⟨m, e⟩` from `sabCancel pullCubCancel E H _ _ _ Y.t 𝔐₀.t 𝔐.t 𝔐₀.f h 𝔐₀.m (hf ▸ 𝔐.m)`. Conclude with `⟨m, by rw [← e, sabMap_cast_φ]⟩`.
-/
theorem exists_sabMap (𝔐₀ : HodgeCpt Y S₀ y₀) (𝔐 : HodgeCpt Y S y) (h : 𝔐.X ⟶ 𝔐₀.X) (hf : 𝔐.f = h ≫ 𝔐₀.f) :
    ∃ m : SABMap 𝔐.t 𝔐₀.t h, 𝔐.m.φ = m.φ ≫ 𝔐₀.m.φ := by
  obtain ⟨m, e⟩ := sabCancel pullCubCancel E H _ _ _ Y.t 𝔐₀.t 𝔐.t 𝔐₀.f h 𝔐₀.m (hf ▸ 𝔐.m)
  exact ⟨m, by rw [← e, sabMap_cast_φ]⟩

/- English proof (translation)
Take `⟨m, -⟩` from `exists_sabMap 𝔐₀ 𝔐 h hf`. Establish `hp : IsPullback m.φ 𝔐.t.G.hom 𝔐₀.t.G.hom h` using `m.cart.1`. Conclude with `(abLocus_pullback abLocusOne 𝔐₀.t.semi hp x).symm`.
-/
theorem mem_abLocus_iff (𝔐₀ : HodgeCpt Y S₀ y₀) (𝔐 : HodgeCpt Y S y) (h : 𝔐.X ⟶ 𝔐₀.X) (hf : 𝔐.f = h ≫ 𝔐₀.f)
    (x : 𝔐.X) : x ∈ abLocus 𝔐.t.G ↔ h x ∈ abLocus 𝔐₀.t.G := by
  obtain ⟨m, -⟩ := exists_sabMap 𝔐₀ 𝔐 h hf
  have hp : IsPullback m.φ 𝔐.t.G.hom 𝔐₀.t.G.hom h := m.cart.1
  exact (abLocus_pullback abLocusOne 𝔐₀.t.semi hp x).symm

end Cover

section Maps

/- English proof (translation)
Simplify using `[spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`.
-/
theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

/- English proof (translation)
Apply the tactic sequence `ext x <;> simp [dualMap]`.
-/
theorem dualMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    dualMap (g.comp f) = (dualMap g).comp (dualMap f) := by
  ext x <;> simp [dualMap]

/- English proof (translation)
Use `letI := f.toAlgebra`. Use `letI := g.toAlgebra`. Use `letI := (g.comp f).toAlgebra`. Use `haveI : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq fun _ => rfl`. Conclude with `(Module.finrank_mul_finrank A B C).symm`.
-/
theorem finrank_comp' {A B C : Type} [Field A] [Field B] [Field C] (f : A →+* B) (g : B →+* C) :
    (letI := (g.comp f).toAlgebra; Module.finrank A C) =
      (letI := f.toAlgebra; Module.finrank A B) * (letI := g.toAlgebra; Module.finrank B C) := by
  letI := f.toAlgebra
  letI := g.toAlgebra
  letI := (g.comp f).toAlgebra
  haveI : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact (Module.finrank_mul_finrank A B C).symm

/- English proof (translation)
Take `⟨c, hc, rfl⟩` from `ho`. Use `⟨fun k => ?_, fun k a ha => ?_⟩` and prove the remaining obligations. Take `⟨a, ha⟩` from `hw.1 k`. Conclude with `⟨a, IsUnit.mk0 _ (mul_ne_zero (hc k) ha.ne_zero)⟩`. Establish `ha' : IsUnit (w ⟨k, a⟩)` using `IsUnit.mk0 _ fun h0 => ha.ne_zero (by simp [h0])`.

Take `⟨h1, h2⟩` from `hw.2 k a ha'`. Use `⟨h1, fun b => ?_⟩` and prove the remaining obligations. Take `⟨r, hr, e⟩` from `h2 b`. Conclude with `⟨r, hr, by simp only [e]; ring⟩`.
-/
theorem coordsAt_orbit {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {K : Type} [Fintype K]
    {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω} {z : Spec (CommRingCat.of ℂ) ⟶ X}
    {w w' : (Σ k, J k) → ℂ} (hw : CoordsAt ξ y z w) (ho : SameOrbit w' w) : CoordsAt ξ y z w' := by
  obtain ⟨c, hc, rfl⟩ := ho
  refine ⟨fun k => ?_, fun k a ha => ?_⟩
  · obtain ⟨a, ha⟩ := hw.1 k
    exact ⟨a, IsUnit.mk0 _ (mul_ne_zero (hc k) ha.ne_zero)⟩
  · have ha' : IsUnit (w ⟨k, a⟩) := IsUnit.mk0 _ fun h0 => ha.ne_zero (by simp [h0])
    obtain ⟨h1, h2⟩ := hw.2 k a ha'
    refine ⟨h1, fun b => ?_⟩
    obtain ⟨r, hr, e⟩ := h2 b
    exact ⟨r, hr, by simp only [e]; ring⟩

end Maps

section Orbit

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

/- English proof (translation)
Take `⟨c, hc, rfl⟩` from `hw`. Rewrite using `[log_h_smul A hc hz, log_h_smul B hc hz, hab]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem log_sub_orbit {A B : HermLine J} (hab : A.a = B.a) {w z : (Σ k, J k) → ℂ} (hw : SameOrbit w z)
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log (A.h w) - Real.log (B.h w) = Real.log (A.h z) - Real.log (B.h z) := by
  obtain ⟨c, hc, rfl⟩ := hw
  rw [log_h_smul A hc hz, log_h_smul B hc hz, hab]
  ring

/- English proof (translation)
Take `⟨c, hc, rfl⟩` from `hw`. Simplify using `only [log_h_smul _ hc hz, Finset.sum_add_distrib]`. Establish `: ∑ k, (A.a k : ℝ) * Real.log ‖c k‖ = -∑ x ∈ s, ∑ k, ((B x).a k : ℝ) * Real.log ‖c k‖`. Rewrite using `[Finset.sum_comm, ← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[hab, ← Finset.sum_mul, ← neg_mul]`. Simplify using `[Finset.sum_apply]`. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem log_sum_orbit {X : Type} (s : Finset X) {A : HermLine J} {B : X → HermLine J}
    (hab : A.a = -∑ x ∈ s, (B x).a) {w z : (Σ k, J k) → ℂ} (hw : SameOrbit w z)
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log (A.h w) + ∑ x ∈ s, Real.log ((B x).h w) = Real.log (A.h z) + ∑ x ∈ s, Real.log ((B x).h z) := by
  obtain ⟨c, hc, rfl⟩ := hw
  simp only [log_h_smul _ hc hz, Finset.sum_add_distrib]
  have : ∑ k, (A.a k : ℝ) * Real.log ‖c k‖ = -∑ x ∈ s, ∑ k, ((B x).a k : ℝ) * Real.log ‖c k‖ := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hab, ← Finset.sum_mul, ← neg_mul]
    simp [Finset.sum_apply]
  rw [this]
  ring

/- English proof (translation)
Use function extensionality and compare the values at `k`. Distinguish the cases in `hk : ∃ a, κ a = k`. Take `⟨a, rfl⟩` from `hk`. Simplify using `[pullDeg, hκ.extend_apply, Finset.sum_apply]`. Simplify using `[pullDeg, Function.extend_apply' _ _ _ hk, Finset.sum_apply]`.
-/
theorem pullDeg_neg_sum {K₀ : Type} {X : Type} {κ : K₀ → K} (hκ : Function.Injective κ) (s : Finset X) (f : X → K₀ → ℤ) :
    pullDeg κ (-∑ x ∈ s, f x) = -∑ x ∈ s, pullDeg κ (f x) := by
  funext k
  by_cases hk : ∃ a, κ a = k
  · obtain ⟨a, rfl⟩ := hk
    simp [pullDeg, hκ.extend_apply, Finset.sum_apply]
  · simp [pullDeg, Function.extend_apply' _ _ _ hk, Finset.sum_apply]

/- English proof (translation)
The claim follows from `Real.log_mul ((pullHerm hv A).pos z hz).ne' (T.pos z hz).ne'`.
-/
theorem log_tensor_pull {K₀ : Type} [Fintype K₀] {J₀ : K₀ → Type} [∀ k, Fintype (J₀ k)] {κ : K₀ → K}
    {v : (Σ k, J₀ k) → Σ k, J k} (hv : IsBlockMap κ v) (A : HermLine J₀) (T : HermLine J) {z : (Σ k, J k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log (((pullHerm hv A).tensor T).h z) = Real.log (A.h fun p => z (v p)) + Real.log (T.h z) :=
  Real.log_mul ((pullHerm hv A).pos z hz).ne' (T.pos z hz).ne'

end Orbit

end GlobalTheory.CompanionTheory.Ar.Chg
