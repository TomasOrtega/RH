import Development.EtaleCohomology.EtaleSheaves.LCIsoPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.TateTwistZeroAugmentationBijective

def Aug : Prop := ∀ q : ℕ, ∃ φ : ∀ T : Scheme.{0}, Sec (tw q 0) T →+ LocallyConstant T (ZMod q),
  (∀ {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec (tw q 0) U), φ V (Sec.res g x) = (φ U x).comap g.base.hom) ∧
  ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), φ U (twGen 0 ζ) = 1

def AugBij : Prop := ∀ (q : ℕ) (φ : ∀ T : Scheme.{0}, Sec (tw q 0) T →+ LocallyConstant T (ZMod q)),
  (∀ {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec (tw q 0) U), φ V (Sec.res g x) = (φ U x).comap g.base.hom) →
  (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), φ U (twGen 0 ζ) = 1) →
  ∀ T : Scheme.{0}, IsUnit (q : Γ(T, ⊤)) → Function.Bijective (φ T)

/- English proof (translation)
Introduce `q`. Take `⟨φ, hnat, hgen⟩` from `hA q`. Establish `hb` using `hB q φ hnat hgen`. Use `⟨fun T hT => (AddEquiv.ofBijective (φ T) (hb T hT)).symm, ?_⟩` and prove the remaining obligations. Introduce `V U g hV hU a`.

Apply `(hb V hV).1` to reduce the goal to its premises. Establish `h1 : ∀ (T : Scheme.{0}) (hT : IsUnit (q : Γ(T, ⊤))) (b : LocallyConstant T (ZMod q)), φ T ((AddEquiv.ofBijective (φ T) (hb T hT)).symm b) = b` using `fun T hT b => (AddEquiv.ofBijective (φ T) (hb T hT)).apply_symm_apply b`. Rewrite using `[hnat, h1 U hU, h1 V hV]`.
-/
theorem Tw0_of (hA : Aug) (hB : AugBij) : LateralTheory.E.LCIsoPf.Tw0 := by
  intro q
  obtain ⟨φ, hnat, hgen⟩ := hA q
  have hb := hB q φ hnat hgen
  refine ⟨fun T hT => (AddEquiv.ofBijective (φ T) (hb T hT)).symm, ?_⟩
  intro V U g hV hU a
  apply (hb V hV).1
  have h1 : ∀ (T : Scheme.{0}) (hT : IsUnit (q : Γ(T, ⊤))) (b : LocallyConstant T (ZMod q)),
      φ T ((AddEquiv.ofBijective (φ T) (hb T hT)).symm b) = b := fun T hT b =>
    (AddEquiv.ofBijective (φ T) (hb T hT)).apply_symm_apply b
  rw [hnat, h1 U hU, h1 V hV]

end LateralTheory.E.TateTwistZeroAugmentationBijective
