import Development.EtaleCohomology.KummerTheory.BockCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.TwExtPf

/- English proof (translation)
Take `⟨S, hS, hP⟩` from `h`. Conclude with `Sheaf.isSeparated M U S hS x y (fun V g hg => hP _ g hg)`.
-/
theorem sep {M : Shv ℤ} {U : Scheme.{0}} (x y : Sec M U)
    (h : Loc U fun V g => Sec.res g x = Sec.res g y) : x = y := by
  obtain ⟨S, hS, hP⟩ := h
  exact Sheaf.isSeparated M U S hS x y (fun V g hg => hP _ g hg)

/- English proof (translation)
Introduce `Q _ i M φ ψ h`. Use `(hM ℤ φ).2.2.2 ψ fun U a => ?_` and prove the remaining obligations. Take `⟨S, hS, hP⟩` from `(hT Q i).1 U a`. Use `sep _ _ ⟨S, hS, fun V g hg => ?_⟩` and prove the remaining obligations. Establish `nφ : Sec.res g (Sec.map φ a) = Sec.map φ (Sec.res g a)` using `congrArg (fun f => (ModuleCat.Hom.hom f) a) (φ.hom.naturality g.op).symm`.

Establish `nψ : Sec.res g (Sec.map ψ a) = Sec.map ψ (Sec.res g a)` using `congrArg (fun f => (ModuleCat.Hom.hom f) a) (ψ.hom.naturality g.op).symm`. Use `show Sec.res g (Sec.map φ a) = Sec.res g (Sec.map ψ a)`. Rewrite using `[nφ, nψ]`. Establish `ha : Sec.res g a = 0 ∨ ∃ (ζ : Prim Q Γ(V, ⊤)) (c : ℕ), (Sec.res g a : Sec (LateralTheory.KummerTheory.BockCut.TZ Q i) V) = c • LateralTheory.KummerTheory.BockCut.genZ i ζ` using `hP V g hg`. Break down `ha with h0 | ⟨ζ, c, hc⟩` into its components or cases.

Establish `e : (Sec.res g a : Sec (LateralTheory.KummerTheory.BockCut.TZ Q i) V) = 0` using `h0`. Rewrite using `[e]`. Simplify using `only [Sec.map, map_zero]`. Rewrite using `[hc]`. Establish `hh` using `h V ζ`.

Simplify using `only [Sec.map] at hh ⊢`. Rewrite using `[map_nsmul, map_nsmul, hh]`.
-/
theorem TwExt_of (hT : LateralTheory.EtaleFoundations.EtaleTateTwistSectionsLocallyGenerated) (hM : LateralTheory.EtaleFoundations.EtaleSheafMonoEpiSectionCriteria) :
    LateralTheory.KummerTheory.BockCut.TwExt := by
  intro Q _ i M φ ψ h
  refine (hM ℤ φ).2.2.2 ψ fun U a => ?_
  obtain ⟨S, hS, hP⟩ := (hT Q i).1 U a
  refine sep _ _ ⟨S, hS, fun V g hg => ?_⟩
  have nφ : Sec.res g (Sec.map φ a) = Sec.map φ (Sec.res g a) :=
    congrArg (fun f => (ModuleCat.Hom.hom f) a) (φ.hom.naturality g.op).symm
  have nψ : Sec.res g (Sec.map ψ a) = Sec.map ψ (Sec.res g a) :=
    congrArg (fun f => (ModuleCat.Hom.hom f) a) (ψ.hom.naturality g.op).symm
  show Sec.res g (Sec.map φ a) = Sec.res g (Sec.map ψ a)
  rw [nφ, nψ]
  have ha : Sec.res g a = 0 ∨ ∃ (ζ : Prim Q Γ(V, ⊤)) (c : ℕ), (Sec.res g a : Sec (LateralTheory.KummerTheory.BockCut.TZ Q i) V) = c • LateralTheory.KummerTheory.BockCut.genZ i ζ := hP V g hg
  rcases ha with h0 | ⟨ζ, c, hc⟩
  · have e : (Sec.res g a : Sec (LateralTheory.KummerTheory.BockCut.TZ Q i) V) = 0 := h0
    rw [e]; simp only [Sec.map, map_zero]
  · rw [hc]; have hh := h V ζ; simp only [Sec.map] at hh ⊢; rw [map_nsmul, map_nsmul, hh]

end LateralTheory.KummerTheory.TwExtPf
