import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PtExt

/- English proof (translation)
Establish `h' : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ U` using `fun p _ ↦ h (Set.mem_univ _)`. Unfold `evU`. Rewrite using `[dif_pos h', dif_pos h]`. Unfold `GlobalTheory.Cris.evalAt`. Rewrite using `[← Scheme.Hom.appLE_comp_appLE (spMap φ) x U ⊤ ⊤ h le_rfl]`.

Establish `e` using `congrArg (fun k => k.hom (x.appLE U ⊤ h a)) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))`. Simplify using `only [RingHom.comp_apply, CommRingCat.comp_apply] at e ⊢`. Conclude with `e`.
-/
theorem evalSectionAtPointOrZero_specMap_comp (Y : Scheme.{0}) (D D' : Type) [CommRing D] [CommRing D'] (φ : D →+* D') (x : Sp D ⟶ Y) (U : Y.Opens) (a : Γ(Y, U)) (h : ⊤ ≤ x ⁻¹ᵁ U) : evU (spMap φ ≫ x) U a = φ (evU x U a) := by
  have h' : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ U := fun p _ ↦ h (Set.mem_univ _)
  unfold evU
  rw [dif_pos h', dif_pos h]
  unfold GlobalTheory.Cris.evalAt
  rw [← Scheme.Hom.appLE_comp_appLE (spMap φ) x U ⊤ ⊤ h le_rfl]
  have e := congrArg (fun k => k.hom (x.appLE U ⊤ h a)) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))
  simp only [RingHom.comp_apply, CommRingCat.comp_apply] at e ⊢
  exact e

/- English proof (translation)
Establish `hU : ⊤ ≤ x ⁻¹ᵁ U` using `hV.trans (fun p hp ↦ h hp)`. Unfold `evU`. Rewrite using `[dif_pos hV, dif_pos hU]`. Unfold `GlobalTheory.Cris.evalAt`. Establish `e` using `congrArg (fun k => k.hom a) (Scheme.Hom.map_appLE x hV (homOfLE h).op)`.

Simplify using `only [RingHom.comp_apply, CommRingCat.comp_apply] at e ⊢`. Rewrite using `[e]`.
-/
theorem evalSectionAtPointOrZero_restriction (Y : Scheme.{0}) (D : Type) [CommRing D] (x : Sp D ⟶ Y) (U V : Y.Opens) (h : V ≤ U) (a : Γ(Y, U)) (hV : ⊤ ≤ x ⁻¹ᵁ V) : evU x V ((Y.presheaf.map (homOfLE h).op).hom a) = evU x U a := by
  have hU : ⊤ ≤ x ⁻¹ᵁ U := hV.trans (fun p hp ↦ h hp)
  unfold evU
  rw [dif_pos hV, dif_pos hU]
  unfold GlobalTheory.Cris.evalAt
  have e := congrArg (fun k => k.hom a) (Scheme.Hom.map_appLE x hV (homOfLE h).op)
  simp only [RingHom.comp_apply, CommRingCat.comp_apply] at e ⊢
  rw [e]

/- English proof (translation)
Take `⟨v, hv⟩` from `hu.map (TrivSqZeroExt.fstHom D D D)`. Take `⟨v', hv'⟩` from `hu'.map (TrivSqZeroExt.fstHom D D D)`. Simplify using `only [TrivSqZeroExt.fstHom_apply] at hv hv'`. Unfold `dl`. Rewrite using `[TrivSqZeroExt.fst_mul, DualNumber.snd_mul, ← hv, ← hv', ← Units.val_mul, Ring.inverse_unit, Ring.inverse_unit, Ring.inverse_unit]`.

Rewrite using `[mul_inv_rev, Units.val_mul]`. Establish `a1 : (v : D) * ↑v⁻¹ = 1` using `Units.mul_inv v`. Establish `a2 : (v' : D) * ↑v'⁻¹ = 1` using `Units.mul_inv v'`. Take the linear combination `(u'.snd * ↑v'⁻¹) * a1 + (u.snd * ↑v⁻¹) * a2`.
-/
theorem dualNumberSndMulInverseFst_mul_units (D : Type) [CommRing D] (u u' : DualNumber D) (hu : IsUnit u) (hu' : IsUnit u') : dl (u * u') = dl u + dl u' := by
  obtain ⟨v, hv⟩ := hu.map (TrivSqZeroExt.fstHom D D D)
  obtain ⟨v', hv'⟩ := hu'.map (TrivSqZeroExt.fstHom D D D)
  simp only [TrivSqZeroExt.fstHom_apply] at hv hv'
  unfold dl
  rw [TrivSqZeroExt.fst_mul, DualNumber.snd_mul, ← hv, ← hv', ← Units.val_mul, Ring.inverse_unit, Ring.inverse_unit, Ring.inverse_unit]
  rw [mul_inv_rev, Units.val_mul]
  have a1 : (v : D) * ↑v⁻¹ = 1 := Units.mul_inv v
  have a2 : (v' : D) * ↑v'⁻¹ = 1 := Units.mul_inv v'
  linear_combination (u'.snd * ↑v'⁻¹) * a1 + (u.snd * ↑v⁻¹) * a2

/- English proof (translation)
Establish `h1 : (epsHom φ u).fst = φ u.fst`. Simplify using `[epsHom, DualNumber.lift_apply_apply]`. Establish `h2 : (epsHom φ u).snd = φ u.snd`. Simplify using `[epsHom, DualNumber.lift_apply_apply]`. Use `⟨h1, h2, fun hu ↦ ?_⟩` and prove the remaining obligations.

Take `⟨v, hv⟩` from `hu.map (TrivSqZeroExt.fstHom D D D)`. Simplify using `only [TrivSqZeroExt.fstHom_apply] at hv`. Unfold `dl`. Rewrite using `[h1, h2, ← hv, Ring.inverse_unit, map_mul]`. Establish `: φ (v : D) = ((Units.map (φ : D →* D') v : D'ˣ) : D')` using `rfl`.

Rewrite using `[this, Ring.inverse_unit]`. Both sides reduce to the same expression.
-/
theorem dualNumberAlgHomMap_fst_snd_logDerivative (R D D' : Type) [CommRing R] [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (u : DualNumber D) : (epsHom φ u).fst = φ u.fst ∧ (epsHom φ u).snd = φ u.snd ∧ (IsUnit u → dl (epsHom φ u) = φ (dl u)) := by
  have h1 : (epsHom φ u).fst = φ u.fst := by
    simp [epsHom, DualNumber.lift_apply_apply]
  have h2 : (epsHom φ u).snd = φ u.snd := by
    simp [epsHom, DualNumber.lift_apply_apply]
  refine ⟨h1, h2, fun hu ↦ ?_⟩
  obtain ⟨v, hv⟩ := hu.map (TrivSqZeroExt.fstHom D D D)
  simp only [TrivSqZeroExt.fstHom_apply] at hv
  unfold dl
  rw [h1, h2, ← hv, Ring.inverse_unit, map_mul]
  have : φ (v : D) = ((Units.map (φ : D →* D') v : D'ˣ) : D') := rfl
  rw [this, Ring.inverse_unit]
  rfl
/- English proof (translation)
Unfold `evU`. Distinguish the cases in `h : ⊤ ≤ x ⁻¹ᵁ (q ⁻¹ᵁ U)`. Establish `h' : ⊤ ≤ (x ≫ q) ⁻¹ᵁ U` using `h`. Rewrite using `[dif_pos h, dif_pos h']`. Unfold `GlobalTheory.Cris.evalAt`.

Simplify using `only [RingHom.comp_apply]`. Rewrite using `[Scheme.Hom.comp_appLE, CommRingCat.comp_apply]`. Establish `h' : ¬ ⊤ ≤ (x ≫ q) ⁻¹ᵁ U` using `h`. Rewrite using `[dif_neg h, dif_neg h']`.
-/
theorem evalSectionAtPointOrZero_schemeHom_app (Y Z : Scheme.{0}) (D : Type) [CommRing D] (x : Sp D ⟶ Y) (q : Y ⟶ Z) (U : Z.Opens) (a : Γ(Z, U)) : evU x (q ⁻¹ᵁ U) ((q.app U).hom a) = evU (x ≫ q) U a := by
  unfold evU
  by_cases h : ⊤ ≤ x ⁻¹ᵁ (q ⁻¹ᵁ U)
  · have h' : ⊤ ≤ (x ≫ q) ⁻¹ᵁ U := h
    rw [dif_pos h, dif_pos h']
    unfold GlobalTheory.Cris.evalAt
    simp only [RingHom.comp_apply]
    rw [Scheme.Hom.comp_appLE, CommRingCat.comp_apply]
  · have h' : ¬ ⊤ ≤ (x ≫ q) ⁻¹ᵁ U := h
    rw [dif_neg h, dif_neg h']

/- English proof (translation)
Introduce `p _`. Set `q : Sp D` to `PrimeSpectrum.comap (TrivSqZeroExt.inlHom D D) p`. Establish `hq : (spMap (TrivSqZeroExt.fstHom D D D).toRingHom) q = p`. Apply `PrimeSpectrum.ext` to reduce the goal to its premises. Use extensionality with `z`.

Express the relevant statement in the definitionally equal form `z ∈ (PrimeSpectrum.comap ((TrivSqZeroExt.fstHom D D D).toRingHom) q).asIdeal ↔ z ∈ p.asIdeal`. Simplify using `only [q, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]`. Establish `heps : (DualNumber.eps : DualNumber D) ∈ p.asIdeal` using `p.isPrime.mem_of_pow_mem 2 (by rw [pow_two, DualNumber.eps_mul_eps]; exact p.asIdeal.zero_mem)`. Establish `hz : z = TrivSqZeroExt.inl z.fst + TrivSqZeroExt.inl z.snd * DualNumber.eps`. Apply the tactic sequence `ext <;> simp`.

Prove the components needed by the constructor for the conclusion. Introduce `hm`. Rewrite using `[hz]`. Conclude with `p.asIdeal.add_mem hm (p.asIdeal.mul_mem_left _ heps)`. Introduce `hm`.

Establish `: TrivSqZeroExt.inl z.fst = z - TrivSqZeroExt.inl z.snd * DualNumber.eps`. Apply the tactic sequence `rw [hz]; ext <;> simp`. Express the relevant statement in the definitionally equal form `TrivSqZeroExt.inl z.fst ∈ p.asIdeal`. Rewrite using `[this]`. Conclude with `p.asIdeal.sub_mem hm (p.asIdeal.mul_mem_left _ heps)`.

Use `h (Set.mem_univ q)` as an intermediate fact. Rewrite using `[← hq]`. Conclude with `this`.
-/
theorem dualNumberPoint_preimage_top_of_reduction (Y : Scheme.{0}) (D : Type) [CommRing D] (y : Sp (DualNumber D) ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ (spMap (TrivSqZeroExt.fstHom D D D).toRingHom ≫ y) ⁻¹ᵁ U) : ⊤ ≤ y ⁻¹ᵁ U := by
  intro p _
  let q : Sp D := PrimeSpectrum.comap (TrivSqZeroExt.inlHom D D) p
  have hq : (spMap (TrivSqZeroExt.fstHom D D D).toRingHom) q = p := by
    apply PrimeSpectrum.ext
    ext z
    change z ∈ (PrimeSpectrum.comap ((TrivSqZeroExt.fstHom D D D).toRingHom) q).asIdeal ↔ z ∈ p.asIdeal
    simp only [q, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
    have heps : (DualNumber.eps : DualNumber D) ∈ p.asIdeal :=
      p.isPrime.mem_of_pow_mem 2 (by rw [pow_two, DualNumber.eps_mul_eps]; exact p.asIdeal.zero_mem)
    have hz : z = TrivSqZeroExt.inl z.fst + TrivSqZeroExt.inl z.snd * DualNumber.eps := by
      ext <;> simp
    constructor
    · intro hm
      rw [hz]
      exact p.asIdeal.add_mem hm (p.asIdeal.mul_mem_left _ heps)
    · intro hm
      have : TrivSqZeroExt.inl z.fst = z - TrivSqZeroExt.inl z.snd * DualNumber.eps := by
        rw [hz]; ext <;> simp
      change TrivSqZeroExt.inl z.fst ∈ p.asIdeal
      rw [this]
      exact p.asIdeal.sub_mem hm (p.asIdeal.mul_mem_left _ heps)
  have := h (Set.mem_univ q)
  rw [← hq]
  exact this

/- English proof (translation)
Assemble the required witnesses or components as `⟨evalSectionAtPointOrZero_specMap_comp, evalSectionAtPointOrZero_restriction, evalSectionAtPointOrZero_schemeHom_app, dualNumberSndMulInverseFst_mul_units, dualNumberAlgHomMap_fst_snd_logDerivative, dualNumberPoint_preimage_top_of_reduction⟩`.
-/
theorem evU_dl_rules : (∀ (Y : Scheme.{0}) (D D' : Type) [CommRing D] [CommRing D'] (φ : D →+* D') (x : Sp D ⟶ Y) (U : Y.Opens) (a : Γ(Y, U)), ⊤ ≤ x ⁻¹ᵁ U → evU (spMap φ ≫ x) U a = φ (evU x U a)) ∧ (∀ (Y : Scheme.{0}) (D : Type) [CommRing D] (x : Sp D ⟶ Y) (U V : Y.Opens) (h : V ≤ U) (a : Γ(Y, U)), ⊤ ≤ x ⁻¹ᵁ V → evU x V ((Y.presheaf.map (homOfLE h).op).hom a) = evU x U a) ∧ (∀ (Y Z : Scheme.{0}) (D : Type) [CommRing D] (x : Sp D ⟶ Y) (q : Y ⟶ Z) (U : Z.Opens) (a : Γ(Z, U)), evU x (q ⁻¹ᵁ U) ((q.app U).hom a) = evU (x ≫ q) U a) ∧ (∀ (D : Type) [CommRing D] (u u' : DualNumber D), IsUnit u → IsUnit u' → dl (u * u') = dl u + dl u') ∧ (∀ (R D D' : Type) [CommRing R] [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (u : DualNumber D), (epsHom φ u).fst = φ u.fst ∧ (epsHom φ u).snd = φ u.snd ∧ (IsUnit u → dl (epsHom φ u) = φ (dl u))) ∧ ∀ (Y : Scheme.{0}) (D : Type) [CommRing D] (y : Sp (DualNumber D) ⟶ Y) (U : Y.Opens), ⊤ ≤ (spMap (TrivSqZeroExt.fstHom D D D).toRingHom ≫ y) ⁻¹ᵁ U → ⊤ ≤ y ⁻¹ᵁ U :=
  ⟨evalSectionAtPointOrZero_specMap_comp, evalSectionAtPointOrZero_restriction, evalSectionAtPointOrZero_schemeHom_app, dualNumberSndMulInverseFst_mul_units, dualNumberAlgHomMap_fst_snd_logDerivative, dualNumberPoint_preimage_top_of_reduction⟩

end GlobalTheory.PtExt
