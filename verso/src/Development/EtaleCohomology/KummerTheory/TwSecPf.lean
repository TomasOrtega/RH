import Development.EtaleCohomology.KummerTheory.TwSecPfGamma

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory

def PrimTors : Prop := ∀ (q : ℕ) [NeZero q] (B : Type) [CommRing B], SH B → IsUnit (q : B) →
  Nonempty (Prim q B) ∧ ∀ (i : ℤ) (ζ : Prim q B), Function.Bijective fun t : ZMod q =>
    (ULift.up t : ULift.{1} (ZMod q)) • (Submodule.Quotient.mk (Finsupp.single ζ (1 : ULift.{1} (ZMod q))) :
      (Prim q B →₀ ULift.{1} (ZMod q)) ⧸ twRel q i B)

def SecSH : Prop := ∀ (A : Type) [CommRing A], SH A → ∀ (R : Type) [CommRing R]
  (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)), Function.Bijective (ofRings.sec M (Spec (CommRingCat.of A)))

/- English proof (translation)
Introduce `q _ A _ hA hq`. Establish `hB` using `SHGamma_holds A hA`. Establish `hqB : IsUnit (q : Γ(Spec (CommRingCat.of A), ⊤))`. Simplify using `using hq.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom`. Take `⟨hne, hbij⟩` from `h1 q _ hB hqB`.

Use `⟨hne, fun i ζ => ?_⟩` and prove the remaining obligations. Establish `key : (fun t : ZMod q => (ULift.up t : ULift.{1} (ZMod q)) • twGen i ζ) = ofRings.sec (twF q i) (Spec (CommRingCat.of A)) ∘ (fun t : ZMod q => (ULift.up t : ULift.{1} (ZMod q)) • (Submodule.Quotient.mk (Finsupp.single ζ (1 : ULift.{1} (ZMod q))) : (Prim q _ →₀ ULift.{1} (ZMod q)) …`. Use function extensionality and compare the values at `t`. Simplify using `only [twGen, ofRings.sec]`. Conclude with `(map_smul _ _ _).symm`.

Rewrite using `[key]`. Conclude with `(h2 A hA (ZMod q) (twF q i)).comp (hbij i ζ)`.
-/
theorem TwSec_of (h1 : PrimTors) (h2 : SecSH) : TwSec := by
  intro q _ A _ hA hq
  have hB := SHGamma_holds A hA
  have hqB : IsUnit (q : Γ(Spec (CommRingCat.of A), ⊤)) := by
    simpa using hq.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  obtain ⟨hne, hbij⟩ := h1 q _ hB hqB
  refine ⟨hne, fun i ζ => ?_⟩
  have key : (fun t : ZMod q => (ULift.up t : ULift.{1} (ZMod q)) • twGen i ζ) =
      ofRings.sec (twF q i) (Spec (CommRingCat.of A)) ∘ (fun t : ZMod q =>
        (ULift.up t : ULift.{1} (ZMod q)) • (Submodule.Quotient.mk (Finsupp.single ζ (1 : ULift.{1} (ZMod q))) :
          (Prim q _ →₀ ULift.{1} (ZMod q)) ⧸ twRel q i _)) := by
    funext t
    simp only [twGen, ofRings.sec]
    exact (map_smul _ _ _).symm
  rw [key]
  exact (h2 A hA (ZMod q) (twF q i)).comp (hbij i ζ)

end LateralTheory.KummerTheory
