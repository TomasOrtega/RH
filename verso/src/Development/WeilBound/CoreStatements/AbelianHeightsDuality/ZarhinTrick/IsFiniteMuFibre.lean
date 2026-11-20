import Mathlib
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.IsPolarisationOfRelAmple
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.FibAmpleD
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CubeTrivialAndFiniteFlatSurjectiveMulAbelianScheStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianSchemeNsmulSurjectiveStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.PrwZar.Z2

/- English proof (translation)
Use `h.comm; infer_instance smooth := by have := h.smooth; show Smooth (pullback.snd A.hom f); infer_instance proper := by have := h.proper; show IsProper (pullback.snd A.hom f); infer_instance geomConnected := by` as an intermediate fact. Use `h.geomConnected` as an intermediate fact. Use `show GeometricallyConnected (pullback.snd A.hom f)`. Use `infer_instance`.
-/
theorem isAbelianScheme_pb {S S' : Scheme.{0}} (f : S' ⟶ S) (A : Over S) [GrpObj A]
    (h : IsAbelianScheme A) : IsAbelianScheme ((Over.pullback f).obj A) where
  comm := by have := h.comm; infer_instance
  smooth := by have := h.smooth; show Smooth (pullback.snd A.hom f); infer_instance
  proper := by have := h.proper; show IsProper (pullback.snd A.hom f); infer_instance
  geomConnected := by
    have := h.geomConnected; show GeometricallyConnected (pullback.snd A.hom f); infer_instance

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => rw [pow_zero, pow_zero]`. Conclude with `CategoryTheory.Functor.map_one _`. Consider the case `succ n ih => rw [pow_succ, pow_succ, CategoryTheory.Functor.map_mul, ih, CategoryTheory.Functor.map_id]`.
-/
theorem pb_map_id_pow {S S' : Scheme.{0}} (f : S' ⟶ S) (B : Over S) [GrpObj B] (m : ℕ) :
    (Over.pullback f).map (𝟙 B ^ m) = 𝟙 ((Over.pullback f).obj B) ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero]; exact CategoryTheory.Functor.map_one _
  | succ n ih => rw [pow_succ, pow_succ, CategoryTheory.Functor.map_mul, ih, CategoryTheory.Functor.map_id]

/- English proof (translation)
Use `hA.comm` as an intermediate fact. Use `hA.proper` as an intermediate fact. Use `hB.proper` as an intermediate fact. Establish `hfin : IsFinite ((𝟙 As) ^ m : As ⟶ As).left` using `((GlobalTheory.T.cube_trivial_and_finite_flat_surjective_mul_abelianScheme Ω As L (L.pull (fst As As).left) hA hL ha (LB.isLB_pull hL _)).2 m hm).1`. Establish `hsB : Surjective ((𝟙 Bs) ^ m : Bs ⟶ Bs).left` using `GlobalTheory.T.abelianScheme_nsmul_surjective Ω Bs hB m (by omega)`.

Establish `hsA : Surjective ((𝟙 As) ^ m : As ⟶ As).left` using `GlobalTheory.T.abelianScheme_nsmul_surjective Ω As hA m (by omega)`. Establish `e₁ : ls.left ≫ mus.left = ((𝟙 As) ^ m : As ⟶ As).left` using `by rw [← Over.comp_left, h₁]`. Establish `e₂ : mus.left ≫ ls.left = ((𝟙 Bs) ^ m : Bs ⟶ Bs).left` using `by rw [← Over.comp_left, h₂]`. Establish `hsl : Surjective ls.left`. Establish `: Surjective (mus.left ≫ ls.left)` using `by rw [e₂]; exact hsB`.

Conclude with `AlgebraicGeometry.Surjective.of_comp (f := mus.left) (g := ls.left)`. Establish `hsm : Surjective mus.left`. Establish `: Surjective (ls.left ≫ mus.left)` using `by rw [e₁]; exact hsA`. Conclude with `AlgebraicGeometry.Surjective.of_comp (f := ls.left) (g := mus.left)`. Establish `hpm : IsProper mus.left`.

Establish `: IsProper (mus.left ≫ As.hom)` using `by rw [Over.w]; infer_instance`. Conclude with `IsProper.of_comp _ As.hom`. Establish `hfl : IsFinite ls.left`. Establish `: IsFinite (ls.left ≫ mus.left)` using `by rw [e₁]; exact hfin`. Conclude with `MorphismProperty.of_postcomp (W := @IsFinite) (W' := @IsSeparated) ls.left mus.left inferInstance this`.

Establish `hqm : LocallyQuasiFinite mus.left`. Rewrite using `[locallyQuasiFinite_iff_finite_preimage_singleton]`. Introduce `a`. Establish `hq : LocallyQuasiFinite (ls.left ≫ mus.left)` using `by rw [e₁]; infer_instance`. Establish `h0 : ((ls.left ≫ mus.left) ⁻¹' {a}).Finite` using `(locallyQuasiFinite_iff_finite_preimage_singleton.1 hq) a`.

Use `(h0.image ls.left).subset ?_` and prove the remaining obligations. Introduce `x hx`. Take `⟨y, rfl⟩` from `hsl.surj x`. Use `⟨y, ?_, rfl⟩` and prove the remaining obligations. Simplify using `using hx`.

Conclude with `⟨hfl, hsl, IsFinite.of_isProper_of_locallyQuasiFinite mus.left, hsm⟩`.
-/
theorem fin_surj_core {Ω : Type} [Field Ω] {As Bs : Over (Sp Ω)} [GrpObj As] [GrpObj Bs]
    (hA : IsAbelianScheme As) (hB : IsAbelianScheme Bs) (ls : As ⟶ Bs) (mus : Bs ⟶ As) (m : ℕ) (hm : 1 ≤ m)
    (h₁ : ls ≫ mus = 𝟙 As ^ m) (h₂ : mus ≫ ls = 𝟙 Bs ^ m) {L : LB As.left} (hL : L.IsLB)
    (ha : Out.RelAmple As L) :
    IsFinite ls.left ∧ Surjective ls.left ∧ IsFinite mus.left ∧ Surjective mus.left := by
  have := hA.comm
  have := hA.proper
  have := hB.proper
  have hfin : IsFinite ((𝟙 As) ^ m : As ⟶ As).left :=
    ((GlobalTheory.T.cube_trivial_and_finite_flat_surjective_mul_abelianScheme Ω As L (L.pull (fst As As).left) hA hL ha (LB.isLB_pull hL _)).2 m hm).1
  have hsB : Surjective ((𝟙 Bs) ^ m : Bs ⟶ Bs).left := GlobalTheory.T.abelianScheme_nsmul_surjective Ω Bs hB m (by omega)
  have hsA : Surjective ((𝟙 As) ^ m : As ⟶ As).left := GlobalTheory.T.abelianScheme_nsmul_surjective Ω As hA m (by omega)
  have e₁ : ls.left ≫ mus.left = ((𝟙 As) ^ m : As ⟶ As).left := by rw [← Over.comp_left, h₁]
  have e₂ : mus.left ≫ ls.left = ((𝟙 Bs) ^ m : Bs ⟶ Bs).left := by rw [← Over.comp_left, h₂]
  have hsl : Surjective ls.left := by
    have : Surjective (mus.left ≫ ls.left) := by rw [e₂]; exact hsB
    exact AlgebraicGeometry.Surjective.of_comp (f := mus.left) (g := ls.left)
  have hsm : Surjective mus.left := by
    have : Surjective (ls.left ≫ mus.left) := by rw [e₁]; exact hsA
    exact AlgebraicGeometry.Surjective.of_comp (f := ls.left) (g := mus.left)
  have hpm : IsProper mus.left := by
    have : IsProper (mus.left ≫ As.hom) := by rw [Over.w]; infer_instance
    exact IsProper.of_comp _ As.hom
  have hfl : IsFinite ls.left := by
    have : IsFinite (ls.left ≫ mus.left) := by rw [e₁]; exact hfin
    exact MorphismProperty.of_postcomp (W := @IsFinite) (W' := @IsSeparated) ls.left mus.left inferInstance this
  have hqm : LocallyQuasiFinite mus.left := by
    rw [locallyQuasiFinite_iff_finite_preimage_singleton]
    intro a
    have hq : LocallyQuasiFinite (ls.left ≫ mus.left) := by rw [e₁]; infer_instance
    have h0 : ((ls.left ≫ mus.left) ⁻¹' {a}).Finite :=
      (locallyQuasiFinite_iff_finite_preimage_singleton.1 hq) a
    refine (h0.image ls.left).subset ?_
    intro x hx
    obtain ⟨y, rfl⟩ := hsl.surj x
    refine ⟨y, ?_, rfl⟩
    simpa using hx
  exact ⟨hfl, hsl, IsFinite.of_isProper_of_locallyQuasiFinite mus.left, hsm⟩

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]

variable {Ω : Type} [Field Ω] [IsAlgClosed Ω]

/- English proof (translation)
Establish `e₁ : (Over.pullback s).map l ≫ (Over.pullback s).map mu = 𝟙 ((Over.pullback s).obj A) ^ m`. Rewrite using `[← Functor.map_comp, h₁, pb_map_id_pow]`. Establish `e₂ : (Over.pullback s).map mu ≫ (Over.pullback s).map l = 𝟙 ((Over.pullback s).obj B) ^ m`. Rewrite using `[← Functor.map_comp, h₂, pb_map_id_pow]`. Conclude with `(fin_surj_core (isAbelianScheme_pb s A hA) (isAbelianScheme_pb s B hB) _ _ m hm e₁ e₂ hL ha).2.2.1`.
-/
theorem isFinite_mu_fibre (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) (g : ℕ)
    (hgA : SmoothOfRelativeDimension g A.hom) (hgB : SmoothOfRelativeDimension g B.hom) (l : A ⟶ B) [IsMonHom l]
    (mu : B ⟶ A) [IsMonHom mu] (m : ℕ) (hm : 1 ≤ m) (h₁ : l ≫ mu = 𝟙 A ^ m) (h₂ : mu ≫ l = 𝟙 B ^ m)
    (s : Sp Ω ⟶ S) (L : LB ((Over.pullback s).obj A).left) (hL : L.IsLB)
    (ha : Out.RelAmple ((Over.pullback s).obj A) L) : IsFinite ((Over.pullback s).map mu).left := by
  have e₁ : (Over.pullback s).map l ≫ (Over.pullback s).map mu = 𝟙 ((Over.pullback s).obj A) ^ m := by
    rw [← Functor.map_comp, h₁, pb_map_id_pow]
  have e₂ : (Over.pullback s).map mu ≫ (Over.pullback s).map l = 𝟙 ((Over.pullback s).obj B) ^ m := by
    rw [← Functor.map_comp, h₂, pb_map_id_pow]
  exact (fin_surj_core (isAbelianScheme_pb s A hA) (isAbelianScheme_pb s B hB) _ _ m hm e₁ e₂ hL ha).2.2.1

end PositivityTheory.PrwZar.Z2
