import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.ResClosed
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.AllHolds
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PGenBasic

noncomputable section
open CategoryTheory Limits AlgebraicGeometry UpperTheory.Gal.TranscendenceTraces

namespace UpperTheory.Gal.Mod

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Check the elementary cases of the proposition. A detailed English derivation is pending.
-/
private theorem mem_basicOpen_of_ne {p : ℕ} {Y : Scheme.{0}} (Ω : Type) [Field Ω]
    (x : gp Ω ⟶ Y) (hp : (p : Ω) ≠ 0) : pt x ∈ Y.basicOpen (p : Γ(Y, ⊤)) := by
  have hu : IsUnit ((p : ℕ) : Γ(gp Ω, ⊤)) := by
    have h1 : IsUnit ((p : ℕ) : Ω) := isUnit_iff_ne_zero.mpr hp
    have h2 := h1.map (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom
    simpa using h2
  have h3 : (gp Ω).basicOpen (x.appTop (p : Γ(Y, ⊤))) = ⊤ := by
    rw [map_natCast]
    exact Scheme.basicOpen_of_isUnit _ hu
  have h4 : IsLocalRing.closedPoint Ω ∈ x ⁻¹ᵁ Y.basicOpen (p : Γ(Y, ⊤)) := by
    rw [Scheme.preimage_basicOpen_top, h3]
    trivial
  exact h4

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Establish an intermediate fact. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components.

Establish an intermediate fact. Substitute using the available equality. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem nwtOne : NwtOne := by
  intro p Y T hL _
  obtain ⟨_, _, _, _, _, _, _, hMB, _, _, hWN, _, hNF, _, _⟩ := all_holds.1
  haveI := T.fin
  have hN : IsNwt T.p (nwt T.p) := hWN T.p hL
  refine ⟨hN.1, ?_⟩
  intro Ω _ _ z hp
  haveI := T.et
  have hD : Dense {s | GenPt ((Y.basicOpen (p : Γ(Y, ⊤))).ι s)} := by
    have hs : {s | GenPt ((Y.basicOpen (p : Γ(Y, ⊤))).ι s)} =
        {s | GenPt s} := by
      ext s
      exact genBasic_of.2.1 (Y.basicOpen (p : Γ(Y, ⊤))).ι s
    rw [hs]
    exact genBasic_of.1 _
  have hc := hNF (T.p ⁻¹ᵁ Y.basicOpen (p : Γ(Y, ⊤))).ι (T.p ∣_ Y.basicOpen (p : Γ(Y, ⊤))) T.p
    (Y.basicOpen (p : Γ(Y, ⊤))).ι (isPullback_morphismRestrict T.p _).flip hN hD
  rw [hMB.2.2 (T.p ∣_ Y.basicOpen (p : Γ(Y, ⊤)))] at hc
  have hmem : pt (z ≫ T.p) ∈ Y.basicOpen (p : Γ(Y, ⊤)) := mem_basicOpen_of_ne Ω (z ≫ T.p) hp
  have hr : Set.range z ⊆ Set.range (T.p ⁻¹ᵁ Y.basicOpen (p : Γ(Y, ⊤))).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨q, rfl⟩
    have hq : q = IsLocalRing.closedPoint Ω := Subsingleton.elim _ _
    subst hq
    exact hmem
  have hz := IsOpenImmersion.lift_fac (T.p ⁻¹ᵁ Y.basicOpen (p : Γ(Y, ⊤))).ι z hr
  have h5 := congrArg (fun w : Wt _ => w Ω (IsOpenImmersion.lift _ z hr)) hc
  simp only [Wt.comap, hz] at h5
  rw [h5]
  rfl

end UpperTheory.Gal.Mod

end
