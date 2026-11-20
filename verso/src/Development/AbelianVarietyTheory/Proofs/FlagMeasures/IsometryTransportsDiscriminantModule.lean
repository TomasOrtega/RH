import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HbApply
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Introduce `K V V' _ _ _ _ _ _ _ _ _ _ _ h h' e he L I hI hQ`. Establish `hL : GlobalTheory.Mass.IsIntLat h L`. Use `GlobalTheory.Mass.Transp.intLat_img e.symm (GlobalTheory.Mass.Transp.symm_isom e he) _ hI` as an intermediate fact. Rewrite `this` using `[GlobalTheory.Mass.Transp.img_symm_img]`. Then use the resulting hypothesis. Use `⟨hL, ?_⟩` and prove the remaining obligations.

Take `⟨q⟩` from `hQ`. Use `set D := Formalism.HermitianLatticesTheory.dual h L with hDdef`. Use `set D' := Formalism.HermitianLatticesTheory.dual h' (GlobalTheory.Mass.Transp.img e L) with hD'def`. Establish `hD : D' = GlobalTheory.Mass.Transp.img e D` using `GlobalTheory.Mass.Transp.dual_img e he L`. Establish `hmem : ∀ x : V, x ∈ D → e x ∈ D'`.

Introduce `x hx`. Rewrite using `[hD, GlobalTheory.Mass.Transp.mem_img]`. Simplify using `using hx`. Establish `hmem' : ∀ y : V', y ∈ D' → e.symm y ∈ D`. Introduce `y hy`.

Rewrite `hy` using `[hD, GlobalTheory.Mass.Transp.mem_img]`. Conclude with `hy`. Set `f : D ≃ₗ[𝓞 K] D'` to `{ toFun := fun x => ⟨e x, hmem x x.2⟩ invFun := fun y => ⟨e.symm y, hmem' y y.2⟩ map_add' := fun x y => by ext; simp map_smul' := fun r x => by`. Use `ext`. Simplify using `only [SetLike.val_smul, RingHom.id_apply]`.

Conclude with `(e.toLinearMap.restrictScalars (𝓞 K)).map_smul r x`. Use `left_inv := fun x => by ext; simp`. Use `right_inv := fun y => by ext; simp }`. Establish `hf : (L.comap D.subtype).map (f : D →ₗ[𝓞 K] D') = (GlobalTheory.Mass.Transp.img e L).comap D'.subtype`. Use extensionality with `⟨y, hy⟩`.

Simplify using `only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]`. Rewrite using `[GlobalTheory.Mass.Transp.mem_img]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨x, hx⟩, hxL, hxy⟩`. Establish `: (f ⟨x, hx⟩ : V') = y` using `congrArg Subtype.val hxy`.

Simplify using `only [f, LinearEquiv.coe_mk] at this`. Rewrite using `[← this]`. Simplify using `using hxL`. Introduce `hyL`. Use `⟨⟨e.symm y, hmem' y hy⟩, hyL, ?_⟩` and prove the remaining obligations.

Use `ext`. Simplify using `[f]`. Conclude with `⟨(Submodule.Quotient.equiv _ _ f hf).trans q⟩`.
-/
theorem GlobalTheory.Mass.Transp.discModule_transport : ∀ (K V V' : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] (h : V →ₗ⋆[K] V →ₗ[K] K) (h' : V' →ₗ⋆[K] V' →ₗ[K] K) (e : V ≃ₗ[K] V'), (∀ x y, h' (e x) (e y) = h x y) → ∀ (L : Submodule (𝓞 K) V) (I : Ideal (𝓞 K)), GlobalTheory.Mass.IsIntLat h' (GlobalTheory.Mass.Transp.img e L) → Nonempty ((↥(Formalism.HermitianLatticesTheory.dual h' (GlobalTheory.Mass.Transp.img e L)) ⧸ (GlobalTheory.Mass.Transp.img e L).comap (Formalism.HermitianLatticesTheory.dual h' (GlobalTheory.Mass.Transp.img e L)).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ I)) → GlobalTheory.Mass.IsIntLat h L ∧ Nonempty ((↥(Formalism.HermitianLatticesTheory.dual h L) ⧸ L.comap (Formalism.HermitianLatticesTheory.dual h L).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ I)) := by
  intro K V V' _ _ _ _ _ _ _ _ _ _ _ h h' e he L I hI hQ
  have hL : GlobalTheory.Mass.IsIntLat h L := by
    have := GlobalTheory.Mass.Transp.intLat_img e.symm (GlobalTheory.Mass.Transp.symm_isom e he) _ hI
    rwa [GlobalTheory.Mass.Transp.img_symm_img] at this
  refine ⟨hL, ?_⟩
  obtain ⟨q⟩ := hQ
  set D := Formalism.HermitianLatticesTheory.dual h L with hDdef
  set D' := Formalism.HermitianLatticesTheory.dual h' (GlobalTheory.Mass.Transp.img e L) with hD'def
  have hD : D' = GlobalTheory.Mass.Transp.img e D := GlobalTheory.Mass.Transp.dual_img e he L
  have hmem : ∀ x : V, x ∈ D → e x ∈ D' := by
    intro x hx; rw [hD, GlobalTheory.Mass.Transp.mem_img]; simpa using hx
  have hmem' : ∀ y : V', y ∈ D' → e.symm y ∈ D := by
    intro y hy; rw [hD, GlobalTheory.Mass.Transp.mem_img] at hy; exact hy
  let f : D ≃ₗ[𝓞 K] D' :=
    { toFun := fun x => ⟨e x, hmem x x.2⟩
      invFun := fun y => ⟨e.symm y, hmem' y y.2⟩
      map_add' := fun x y => by ext; simp
      map_smul' := fun r x => by
        ext
        simp only [SetLike.val_smul, RingHom.id_apply]
        exact (e.toLinearMap.restrictScalars (𝓞 K)).map_smul r x
      left_inv := fun x => by ext; simp
      right_inv := fun y => by ext; simp }
  have hf : (L.comap D.subtype).map (f : D →ₗ[𝓞 K] D') = (GlobalTheory.Mass.Transp.img e L).comap D'.subtype := by
    ext ⟨y, hy⟩
    simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
    rw [GlobalTheory.Mass.Transp.mem_img]
    constructor
    · rintro ⟨⟨x, hx⟩, hxL, hxy⟩
      have : (f ⟨x, hx⟩ : V') = y := congrArg Subtype.val hxy
      simp only [f, LinearEquiv.coe_mk] at this
      rw [← this]; simpa using hxL
    · intro hyL
      refine ⟨⟨e.symm y, hmem' y hy⟩, hyL, ?_⟩
      ext; simp [f]
  exact ⟨(Submodule.Quotient.equiv _ _ f hf).trans q⟩
