import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueCentreFunctionFieldPlaceCurveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePlacesCentreOutsideOpenStatement

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef

/- English proof (translation)
Take `⟨y, hy⟩` from `x.denseRange.exists_mem_open V.isOpen hV`. Introduce `z _`. Establish `: z = y` using `Subsingleton.elim _ _`. Substitute `this` using the available equality. Conclude with `hy`.
-/
theorem top_le_preimage_of_isDominant {K : Type} [Field K] {C : Scheme.{0}} (x : Sp K ⟶ C) [IsDominant x]
    (V : C.Opens) (hV : (V : Set C).Nonempty) : ⊤ ≤ x ⁻¹ᵁ V := by
  obtain ⟨y, hy⟩ := x.denseRange.exists_mem_open V.isOpen hV
  intro z _
  have : z = y := Subsingleton.elim _ _
  subst this
  exact hy

/- English proof (translation)
Introduce `z _`. Establish `hs : z ⤳ IsLocalRing.closedPoint R` using `(PrimeSpectrum.le_iff_specializes _ _).1 (IsLocalRing.le_maximalIdeal z.2.ne_top)`. Conclude with `(hs.map b.continuous).mem_open V.isOpen h`.
-/
theorem top_le_preimage_of_closedPoint {R : Type} [CommRing R] [IsLocalRing R] {C : Scheme.{0}} (b : Sp R ⟶ C)
    (V : C.Opens) (h : b (IsLocalRing.closedPoint R) ∈ V) : ⊤ ≤ b ⁻¹ᵁ V := by
  intro z _
  have hs : z ⤳ IsLocalRing.closedPoint R :=
    (PrimeSpectrum.le_iff_specializes _ _).1 (IsLocalRing.le_maximalIdeal z.2.ne_top)
  exact (hs.map b.continuous).mem_open V.isOpen h

/- English proof (translation)
Use `set M := (ht.basis (inf_le_right : V₀ ⊓ V ≤ V)).toMatrix (hs.basis (inf_le_left : V₀ ⊓ V ≤ V₀)) with hM`. Use `⟨⟨b, V, t, V₀ ⊓ V, inf_le_left, inf_le_right, hx, M, hb, hbV, ht, fun j => ?_, rfl⟩, ?_⟩` and prove the remaining obligations. Use `(ht.basis (inf_le_right : V₀ ⊓ V ≤ V)).sum_repr (hs.basis (inf_le_left : V₀ ⊓ V ≤ V₀) j)` as an intermediate fact. Simplify using `only [IsFrame.basis_apply] at this`. Rewrite using `[hM]`.

Simplify using `only [Module.Basis.toMatrix_apply, IsFrame.basis_apply]`. Conclude with `this.symm`. Establish `hu : IsUnit M.det`. Use `Module.Basis.toMatrix_mul_toMatrix_flip (ht.basis (inf_le_right : V₀ ⊓ V ≤ V)) (hs.basis (inf_le_left : V₀ ⊓ V ≤ V₀))` as an intermediate fact. Conclude with `isUnit_iff_exists_inv.2 ⟨_, by rw [← Matrix.det_mul, this, Matrix.det_one]⟩`.

Use `(hu.map (evAt x hx)).ne_zero` as an intermediate fact. Rewrite `this` using `[RingHom.map_det]`. Then use the resulting hypothesis.
-/
theorem locFrame_of_frames {k K : Type} [Field k] [Field K] [Algebra k K] {C : Scheme.{0}} (x : Sp K ⟶ C)
    {W : C.Modules} {r : ℕ} {V₀ V : C.Opens} {s : Fin r → Γ(W, V₀)} {t : Fin r → Γ(W, V)}
    (hs : IsFrame s) (ht : IsFrame t) (v : Place k K) (b : Sp v.O ⟶ C) (hb : spMap v.O.subtype ≫ b = x)
    (hbV : ⊤ ≤ b ⁻¹ᵁ V) (hx : ⊤ ≤ x ⁻¹ᵁ (V₀ ⊓ V)) :
    LocFrame x s v (((ht.basis (inf_le_right : V₀ ⊓ V ≤ V)).toMatrix
        (hs.basis (inf_le_left : V₀ ⊓ V ≤ V₀))).map (evAt x hx)) ∧
      (((ht.basis (inf_le_right : V₀ ⊓ V ≤ V)).toMatrix
        (hs.basis (inf_le_left : V₀ ⊓ V ≤ V₀))).map (evAt x hx)).det ≠ 0 := by
  set M := (ht.basis (inf_le_right : V₀ ⊓ V ≤ V)).toMatrix (hs.basis (inf_le_left : V₀ ⊓ V ≤ V₀)) with hM
  refine ⟨⟨b, V, t, V₀ ⊓ V, inf_le_left, inf_le_right, hx, M, hb, hbV, ht, fun j => ?_, rfl⟩, ?_⟩
  · have := (ht.basis (inf_le_right : V₀ ⊓ V ≤ V)).sum_repr (hs.basis (inf_le_left : V₀ ⊓ V ≤ V₀) j)
    simp only [IsFrame.basis_apply] at this
    rw [hM]
    simp only [Module.Basis.toMatrix_apply, IsFrame.basis_apply]
    exact this.symm
  · have hu : IsUnit M.det := by
      have := Module.Basis.toMatrix_mul_toMatrix_flip (ht.basis (inf_le_right : V₀ ⊓ V ≤ V))
        (hs.basis (inf_le_left : V₀ ⊓ V ≤ V₀))
      exact isUnit_iff_exists_inv.2 ⟨_, by rw [← Matrix.det_mul, this, Matrix.det_one]⟩
    have := (hu.map (evAt x hx)).ne_zero
    rwa [RingHom.map_det] at this

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun i j => by by_cases h : i = j <;> simp [Matrix.one_apply, h], by simp⟩`.
-/
theorem unimod_one' {k F : Type} [Field k] [Field F] [Algebra k F] {n : ℕ} (v : Place k F) :
    Unimod v (1 : Matrix (Fin n) (Fin n) F) :=
  ⟨fun i j => by by_cases h : i = j <;> simp [Matrix.one_apply, h], by simp⟩

/- English proof (translation)
Introduce `k K _ _ _ _ _ C _ x hx W r hW`. Use `haveI : IsDominant x := hx.2.1.1`. Establish `hxx : spMap (algebraMap K K) ≫ x = x`. Express the relevant statement in the definitionally equal form `spMap (RingHom.id K) ≫ x = x`. Conclude with `(congrArg (· ≫ x) (Spec.map_id _)).trans (Category.id_comp x)`.

Take `⟨V₀, s, hη, hs⟩` from `hW (x (IsLocalRing.closedPoint K))`. Establish `hV₀ : (V₀ : Set C).Nonempty` using `⟨_, hη⟩`. Establish `hcen : ∀ v : Place k K, ∃ b : Sp v.O ⟶ C, spMap v.O.subtype ≫ b = x` using `fun v => by`. Take `⟨b, hb, -⟩` from `GlobalTheory.T.existsUnique_centre_functionFieldPlace_curve k K K C x hx v`. Conclude with `⟨b, hb.trans hxx⟩`.

Use `choose b hb using hcen`. Establish `key : ∀ v, ∃ gv : Matrix (Fin r) (Fin r) K, LocFrame x s v gv ∧ gv.det ≠ 0 ∧ (⊤ ≤ b v ⁻¹ᵁ V₀ → gv = 1)`. Introduce `v`. Distinguish the cases in `hv : ⊤ ≤ b v ⁻¹ᵁ V₀`. Establish `hx' : ⊤ ≤ x ⁻¹ᵁ (V₀ ⊓ V₀)`.

Rewrite using `[inf_idem]`. Conclude with `top_le_preimage_of_isDominant x V₀ hV₀`. Take `⟨h1, h2⟩` from `locFrame_of_frames x hs hs v (b v) (hb v) hv hx'`. Use `⟨_, h1, h2, fun _ => ?_⟩` and prove the remaining obligations. Rewrite using `[Module.Basis.toMatrix_self]`.

Simplify using the standard rewrite rules. Take `⟨V, t, hc, ht⟩` from `hW (b v (IsLocalRing.closedPoint v.O))`. Establish `hbV` using `top_le_preimage_of_closedPoint (b v) V hc`. Establish `hx' : ⊤ ≤ x ⁻¹ᵁ (V₀ ⊓ V)` using `fun z hz => ⟨top_le_preimage_of_isDominant x V₀ hV₀ hz, top_le_preimage_of_isDominant x V ⟨_, hc⟩ hz⟩`. Take `⟨h1, h2⟩` from `locFrame_of_frames x hs ht v (b v) (hb v) hbV hx'`.

Conclude with `⟨_, h1, h2, fun h => absurd h hv⟩`. Use `choose g hg1 hg2 hg3 using key`. Use `⟨V₀, s, g, hV₀, hs, ⟨hg2, ?_⟩, hg1⟩` and prove the remaining obligations. Use `(GlobalTheory.T.finite_places_centre_outside_open k K K C x hx V₀ hV₀).subset fun v hv => ⟨b v, (hb v).trans hxx.symm, fun h => hv ?_⟩` and prove the remaining obligations. Rewrite using `[hg3 v h]`.

Conclude with `unimod_one' v`.
-/
theorem exists_frame_locFrames : ∀ (k K : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  ∀ (W : C.Modules) (r : ℕ), IsVB W r → ∃ (V₀ : C.Opens) (s : Fin r → Γ(W, V₀)) (g : Place k K → Matrix (Fin r) (Fin r) K), (V₀ : Set C).Nonempty ∧ IsFrame s ∧ admitted g ∧ ∀ v, LocFrame x s v (g v) := by
  intro k K _ _ _ _ _ C _ x hx W r hW
  haveI : IsDominant x := hx.2.1.1
  have hxx : spMap (algebraMap K K) ≫ x = x := by
    change spMap (RingHom.id K) ≫ x = x
    exact (congrArg (· ≫ x) (Spec.map_id _)).trans (Category.id_comp x)
  obtain ⟨V₀, s, hη, hs⟩ := hW (x (IsLocalRing.closedPoint K))
  have hV₀ : (V₀ : Set C).Nonempty := ⟨_, hη⟩
  have hcen : ∀ v : Place k K, ∃ b : Sp v.O ⟶ C, spMap v.O.subtype ≫ b = x := fun v => by
    obtain ⟨b, hb, -⟩ := GlobalTheory.T.existsUnique_centre_functionFieldPlace_curve k K K C x hx v
    exact ⟨b, hb.trans hxx⟩
  choose b hb using hcen
  have key : ∀ v, ∃ gv : Matrix (Fin r) (Fin r) K,
      LocFrame x s v gv ∧ gv.det ≠ 0 ∧ (⊤ ≤ b v ⁻¹ᵁ V₀ → gv = 1) := by
    intro v
    by_cases hv : ⊤ ≤ b v ⁻¹ᵁ V₀
    · have hx' : ⊤ ≤ x ⁻¹ᵁ (V₀ ⊓ V₀) := by
        rw [inf_idem]; exact top_le_preimage_of_isDominant x V₀ hV₀
      obtain ⟨h1, h2⟩ := locFrame_of_frames x hs hs v (b v) (hb v) hv hx'
      refine ⟨_, h1, h2, fun _ => ?_⟩
      rw [Module.Basis.toMatrix_self]
      simp
    · obtain ⟨V, t, hc, ht⟩ := hW (b v (IsLocalRing.closedPoint v.O))
      have hbV := top_le_preimage_of_closedPoint (b v) V hc
      have hx' : ⊤ ≤ x ⁻¹ᵁ (V₀ ⊓ V) := fun z hz =>
        ⟨top_le_preimage_of_isDominant x V₀ hV₀ hz, top_le_preimage_of_isDominant x V ⟨_, hc⟩ hz⟩
      obtain ⟨h1, h2⟩ := locFrame_of_frames x hs ht v (b v) (hb v) hbV hx'
      exact ⟨_, h1, h2, fun h => absurd h hv⟩
  choose g hg1 hg2 hg3 using key
  refine ⟨V₀, s, g, hV₀, hs, ⟨hg2, ?_⟩, hg1⟩
  refine (GlobalTheory.T.finite_places_centre_outside_open k K K C x hx V₀ hV₀).subset fun v hv => ⟨b v, (hb v).trans hxx.symm, fun h => hv ?_⟩
  rw [hg3 v h]
  exact unimod_one' v

end GlobalTheory.Nef
