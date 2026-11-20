import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitriangularFramesGramEqCellPointStatement
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.SiegelMassRatios.GramJoint
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WittExtensionTheorem
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocOver.WittFrames

/- English proof (translation)
Use extensionality with `a b`. Establish `h1` using `congrFun (congrFun h a) b`. Simplify using `only [ZhatOM] at h1`. Conclude with `((isUnit_one.neg).pow (r - b.val)).mul_left_cancel h1`.
-/
theorem zhatOM_injective {K : Type*} [CommRing K] {r : ℕ} {Z Z' : Matrix (Fin (r + 1)) (Fin (r + 1)) K}
    (h : ZhatOM Z = ZhatOM Z') : Z = Z' := by
  ext a b
  have h1 := congrFun (congrFun h a) b
  simp only [ZhatOM] at h1
  exact ((isUnit_one.neg).pow (r - b.val)).mul_left_cancel h1

/- English proof (translation)
Take `⟨A, ⟨hA1, hA2⟩, hc⟩` from `h`. Establish `hbt : A.BlockTriangular id` using `fun i j hij => hA1 i j hij`. Establish `hdet : A.det = 1`. Rewrite using `[Matrix.det_of_isUpperTriangular hbt]`. Simplify using `[hA2]`.

Establish `hu : IsUnit A.det` using `by rw [hdet]; exact isUnit_one`. Take `⟨hB1, hB2⟩` from `inv_unitri A hA1 hA2`. Establish `hc' : ∀ b, g b = ∑ a, A a b • f a` using `hc`. Use `⟨A⁻¹, ⟨hB1, hB2⟩, fun b => ?_⟩` and prove the remaining obligations. Use `show f b = ∑ a, A⁻¹ a b • g a`.

Establish `hm` using `Matrix.mul_nonsing_inv A hu`. Repeatedly rewrite using `[hc', Finset.smul_sum, smul_smul]`. Rewrite using `[Finset.sum_comm]`. Establish `: ∀ c, ∑ a, (A⁻¹ a b * A c a) • f c = (A * A⁻¹) c b • f c`. Introduce `c`.

Rewrite using `[← Finset.sum_smul, Matrix.mul_apply]`. Use `congr 1`. Conclude with `Finset.sum_congr rfl (fun a _ => mul_comm _ _)`. Repeatedly rewrite using `[this, hm, Matrix.one_apply, ite_smul, one_smul, zero_smul]`. Simplify using the standard rewrite rules.
-/
theorem tri_symm {E W : Type} [Field E] [AddCommGroup W] [Module E W] {n : ℕ} {f g : Fin n → W}
    (h : Tri E f g) : Tri E g f := by
  obtain ⟨A, ⟨hA1, hA2⟩, hc⟩ := h
  have hbt : A.BlockTriangular id := fun i j hij => hA1 i j hij
  have hdet : A.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular hbt]; simp [hA2]
  have hu : IsUnit A.det := by rw [hdet]; exact isUnit_one
  obtain ⟨hB1, hB2⟩ := inv_unitri A hA1 hA2
  have hc' : ∀ b, g b = ∑ a, A a b • f a := hc
  refine ⟨A⁻¹, ⟨hB1, hB2⟩, fun b => ?_⟩
  show f b = ∑ a, A⁻¹ a b • g a
  have hm := Matrix.mul_nonsing_inv A hu
  simp_rw [hc', Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  have : ∀ c, ∑ a, (A⁻¹ a b * A c a) • f c = (A * A⁻¹) c b • f c := by
    intro c
    rw [← Finset.sum_smul, Matrix.mul_apply]
    congr 1
    exact Finset.sum_congr rfl (fun a _ => mul_comm _ _)
  simp_rw [this, hm, Matrix.one_apply, ite_smul, one_smul, zero_smul]
  simp

/- English proof (translation)
Take `⟨A, hA, hc⟩` from `h`. Establish `hc' : ∀ b, g b = ∑ a, A a b • f a` using `hc`. Use `⟨A, hA, fun b => ?_⟩` and prove the remaining obligations. Use `show γ (g b) = ∑ a, A a b • γ (f a)`. Rewrite using `[hc' b, map_sum]`.

Simplify using `[map_smul]`.
-/
theorem tri_map {E W : Type} [Field E] [AddCommGroup W] [Module E W] {n : ℕ} {f g : Fin n → W}
    (γ : W →ₗ[E] W) (h : Tri E f g) : Tri E (fun a => γ (f a)) (fun a => γ (g a)) := by
  obtain ⟨A, hA, hc⟩ := h
  have hc' : ∀ b, g b = ∑ a, A a b • f a := hc
  refine ⟨A, hA, fun b => ?_⟩
  show γ (g b) = ∑ a, A a b • γ (f a)
  rw [hc' b, map_sum]
  simp [map_smul]

/- English proof (translation)
Set `U` to `Submodule.span K (Set.range v)`. Set `bU : Module.Basis ι K U` to `Module.Basis.span hv`. Establish `hbU : ∀ i, (bU i : V) = v i` using `fun i => congrArg Subtype.val (Module.Basis.span_apply hv i)`. Set `f : U →ₗ[K] V` to `bU.constr K v'`. Establish `hf : ∀ i, f (bU i) = v' i` using `fun i => by simp [f, Module.Basis.constr_basis]`.

Establish `hfe : f = Finsupp.linearCombination K v' ∘ₗ bU.repr.toLinearMap`. Use `bU.ext (fun i => ?_)` and prove the remaining obligations. Rewrite using `[hf]`. Simplify using the standard rewrite rules. Establish `hinj : Function.Injective f`.

Rewrite using `[hfe, LinearMap.coe_comp]`. Conclude with `Function.Injective.comp hv' bU.repr.injective`. Establish `hiso : ∀ x y : U, B (f x) (f y) = B x y`. Establish `: (B.comp f).compl₂ f = (B.comp U.subtype).compl₂ U.subtype`. Use `LinearMap.ext_basis bU bU (fun i j => ?_)` and prove the remaining obligations.

Simplify using `only [LinearMap.compl₂_apply, LinearMap.comp_apply, Submodule.subtype_apply, hf, hbU]`. Conclude with `(hg i j).symm`. Introduce `x y`. Use `LinearMap.congr_fun₂ this x y` as an intermediate fact. Simplify using `using this`.

Take `⟨g, hg1, hg2⟩` from `hW K V B hs hn U f hinj hiso`. Conclude with `⟨g, hg1, fun i => by rw [← hbU i, hg2, hf]⟩`.
-/
theorem exists_isom_of_gram (hW : PI.WittExtension) {K V : Type} [Field K] [StarRing K] [CharZero K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (B : V →ₗ⋆[K] V →ₗ[K] K) (hs : ∀ x y, star (B x y) = B y x) (hn : ∀ x, (∀ y, B x y = 0) → x = 0)
    {ι : Type} (v v' : ι → V) (hv : LinearIndependent K v) (hv' : LinearIndependent K v')
    (hg : ∀ i j, B (v i) (v j) = B (v' i) (v' j)) :
    ∃ g : V ≃ₗ[K] V, (∀ x y, B (g x) (g y) = B x y) ∧ ∀ i, g (v i) = v' i := by
  let U := Submodule.span K (Set.range v)
  let bU : Module.Basis ι K U := Module.Basis.span hv
  have hbU : ∀ i, (bU i : V) = v i := fun i => congrArg Subtype.val (Module.Basis.span_apply hv i)
  let f : U →ₗ[K] V := bU.constr K v'
  have hf : ∀ i, f (bU i) = v' i := fun i => by simp [f, Module.Basis.constr_basis]
  have hfe : f = Finsupp.linearCombination K v' ∘ₗ bU.repr.toLinearMap := by
    refine bU.ext (fun i => ?_)
    rw [hf]; simp
  have hinj : Function.Injective f := by
    rw [hfe, LinearMap.coe_comp]
    exact Function.Injective.comp hv' bU.repr.injective
  have hiso : ∀ x y : U, B (f x) (f y) = B x y := by
    have : (B.comp f).compl₂ f = (B.comp U.subtype).compl₂ U.subtype := by
      refine LinearMap.ext_basis bU bU (fun i j => ?_)
      simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, Submodule.subtype_apply, hf, hbU]
      exact (hg i j).symm
    intro x y
    have := LinearMap.congr_fun₂ this x y
    simpa using this
  obtain ⟨g, hg1, hg2⟩ := hW K V B hs hn U f hinj hiso
  exact ⟨g, hg1, fun i => by rw [← hbU i, hg2, hf]⟩

end GlobalTheory.LocOver.WittFrames

namespace GlobalTheory.LocOver

open GlobalTheory.LocOver.WittFrames Formalism.L2.SG.GramJoint in

/- English proof (translation)
Introduce `D T T' F F00 F' F'0 w hT hT' hG hcell hpt`. Take `⟨⟨Fb, Fb', h1, h2, hb⟩, hall⟩` from `GlobalTheory.T.exists_unitriangular_frames_gram_eq_cell_point D F F' w hT hT' hcell`. Establish `hGb : Gval Fb Fb' = Gval F F'` using `(hall Fb Fb' h1 h2).2`. Establish `hZ : ZhatL Fb Fb' = ZhatL F00 F'0` using `zhatOM_injective (hb.trans hpt.symm)`. Establish `hG0 : Gval F00 F'0 = Gval Fb Fb'` using `by show Gmat (Zhat F00.fl F'0.fl) T T' = Gmat (Zhat Fb.fl Fb'.fl) T T'`.

Conclude with `congrArg (fun Z => Gmat Z T T') hZ.symm`. Use `⟨hG0.trans hGb, ?_⟩` and prove the remaining obligations. Establish `hGb0 : Gflag Fb.fl Fb'.fl ≠ 0` using `by rw [← hGb] at hG; exact hG`. Establish `hG00 : Gflag F00.fl F'0.fl ≠ 0`. Use `hG0.trans hGb` as an intermediate fact.

Rewrite `hG` using `[← this]`. Conclude with `hG`. Establish `hli` using `(gramIndep D.host.E (VS D) D.R.rS T T' Fb.fl Fb'.fl hGb0).1`. Establish `hli'` using `(gramIndep D.host.E (VS D) D.R.rS T T' F00.fl F'0.fl hG00).1`. Establish `hgram : ∀ i j, (VS D).hT (pairVec Fb.fl Fb'.fl i) (pairVec Fb.fl Fb'.fl j) = (VS D).hT (pairVec F00.fl F'0.fl i) (pairVec F00.fl F'0.fl j)`.

Introduce `i j`. Establish `e` using `congrFun (congrFun (gramBlocks D.host.E (VS D) D.R.rS T T' Fb.fl Fb'.fl) i) j`. Establish `e'` using `congrFun (congrFun (gramBlocks D.host.E (VS D) D.R.rS T T' F00.fl F'0.fl) i) j`. Establish `hZ' : Zhat Fb.fl Fb'.fl = Zhat F00.fl F'0.fl` using `hZ`. Rewrite `e` using `[hZ']`.

Conclude with `e.trans e'.symm`. Establish `hs : ∀ x y, star ((VS D).hT x y) = (VS D).hT y x` using `fun x y => (VS D).herm.eq x y`. Establish `hn : ∀ x, (∀ y, (VS D).hT x y = 0) → x = 0` using `fun x hx => (VS D).nondeg.1 x hx`. Take `⟨γ, hγ, hγv⟩` from `exists_isom_of_gram witt_extension_theorem (VS D).hT hs hn _ _ hli hli' hgram`. Use `⟨γ, fun x y => hγ x y, ?_, ?_⟩` and prove the remaining obligations.

Use `tri_map (γ : (VS D).V →ₗ[D.host.E] (VS D).V) h1` as an intermediate fact. Establish `e : (fun a => (γ : (VS D).V →ₗ[D.host.E] (VS D).V) (frame Fb a)) = frame F00`. Use function extensionality and compare the values at `fun a => hγv (Sum.inl a)`. Rewrite `this` using `[e]`. Conclude with `tri_symm this`.

Use `tri_map (γ : (VS D).V →ₗ[D.host.E] (VS D).V) h2` as an intermediate fact. Establish `e : (fun a => (γ : (VS D).V →ₗ[D.host.E] (VS D).V) (frame Fb' a)) = frame F'0`. Use function extensionality and compare the values at `fun a => hγv (Sum.inr a)`. Rewrite `this` using `[e]`. Conclude with `tri_symm this`.
-/
theorem witt_frames_at_point : ∀ (D : D7) {T T' : D.host.E} (F F00 : LFlag (VS D) D.R.rS T)
    (F' F'0 : LFlag (VS D) D.R.rS T') (w : Point D.host.E (D.R.rS + 1)), T ≠ 0 → T' ≠ 0 → Gval F F' ≠ 0 →
    IsInCell (ZhatOM (ZhatL F F')) w → ZhatOM (ZhatL F00 F'0) = ptMat w →
    Gval F00 F'0 = Gval F F' ∧ ∃ γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT,
      Tri D.host.E (frame F00) (fun a => γ (frame F a)) ∧ Tri D.host.E (frame F'0) (fun a => γ (frame F' a)) := by
  intro D T T' F F00 F' F'0 w hT hT' hG hcell hpt
  obtain ⟨⟨Fb, Fb', h1, h2, hb⟩, hall⟩ := GlobalTheory.T.exists_unitriangular_frames_gram_eq_cell_point D F F' w hT hT' hcell
  have hGb : Gval Fb Fb' = Gval F F' := (hall Fb Fb' h1 h2).2
  have hZ : ZhatL Fb Fb' = ZhatL F00 F'0 := zhatOM_injective (hb.trans hpt.symm)
  have hG0 : Gval F00 F'0 = Gval Fb Fb' := by
    show Gmat (Zhat F00.fl F'0.fl) T T' = Gmat (Zhat Fb.fl Fb'.fl) T T'
    exact congrArg (fun Z => Gmat Z T T') hZ.symm
  refine ⟨hG0.trans hGb, ?_⟩
  have hGb0 : Gflag Fb.fl Fb'.fl ≠ 0 := by rw [← hGb] at hG; exact hG
  have hG00 : Gflag F00.fl F'0.fl ≠ 0 := by
    have := hG0.trans hGb; rw [← this] at hG; exact hG
  have hli := (gramIndep D.host.E (VS D) D.R.rS T T' Fb.fl Fb'.fl hGb0).1
  have hli' := (gramIndep D.host.E (VS D) D.R.rS T T' F00.fl F'0.fl hG00).1
  have hgram : ∀ i j, (VS D).hT (pairVec Fb.fl Fb'.fl i) (pairVec Fb.fl Fb'.fl j) =
      (VS D).hT (pairVec F00.fl F'0.fl i) (pairVec F00.fl F'0.fl j) := by
    intro i j
    have e := congrFun (congrFun (gramBlocks D.host.E (VS D) D.R.rS T T' Fb.fl Fb'.fl) i) j
    have e' := congrFun (congrFun (gramBlocks D.host.E (VS D) D.R.rS T T' F00.fl F'0.fl) i) j
    have hZ' : Zhat Fb.fl Fb'.fl = Zhat F00.fl F'0.fl := hZ
    rw [hZ'] at e
    exact e.trans e'.symm
  have hs : ∀ x y, star ((VS D).hT x y) = (VS D).hT y x := fun x y => (VS D).herm.eq x y
  have hn : ∀ x, (∀ y, (VS D).hT x y = 0) → x = 0 := fun x hx => (VS D).nondeg.1 x hx
  obtain ⟨γ, hγ, hγv⟩ := exists_isom_of_gram witt_extension_theorem (VS D).hT hs hn _ _ hli hli' hgram
  refine ⟨γ, fun x y => hγ x y, ?_, ?_⟩
  · have := tri_map (γ : (VS D).V →ₗ[D.host.E] (VS D).V) h1
    have e : (fun a => (γ : (VS D).V →ₗ[D.host.E] (VS D).V) (frame Fb a)) = frame F00 :=
      funext fun a => hγv (Sum.inl a)
    rw [e] at this
    exact tri_symm this
  · have := tri_map (γ : (VS D).V →ₗ[D.host.E] (VS D).V) h2
    have e : (fun a => (γ : (VS D).V →ₗ[D.host.E] (VS D).V) (frame Fb' a)) = frame F'0 :=
      funext fun a => hγv (Sum.inr a)
    rw [e] at this
    exact tri_symm this

end GlobalTheory.LocOver
