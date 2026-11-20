import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfCurveDegreesNonneg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfSurjectivePullback
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibPullback
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.TrueGeo
open scoped ENNReal Classical
open Limits

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CurveReduce

/- English proof (translation)
Introduce `k _ _ X X' p p' hp hp' ρ hρ r _ Z i _ _ _ hd`. Take `⟨N, j, _, hj⟩` from `hp`. Use `isProper_str k N` as an intermediate fact. Establish `: IsProper p` using `hj ▸ inferInstance`. Take `⟨N', j', _, hj'⟩` from `hp'`.

Use `isProper_str k N'` as an intermediate fact. Establish `: IsProper p'` using `hj' ▸ inferInstance`. Establish `: IsFinite (spMap (Int.castRingHom k))`. Rewrite using `[spMap, IsFinite.SpecMap_iff]`. Conclude with `(RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance`.

Establish `: IsProper (ρ ≫ p)` using `by rw [hρ]; infer_instance`. Establish `: IsProper ρ` using `.of_comp ρ p`. Set `t` to `p ≫ spMap (Int.castRingHom k)`. Set `g` to `i ≫ ρ`. Establish `: IsProper (g ≫ t)` using `by simp only [g, t]; infer_instance`.

Establish `: IsProper g` using `.of_comp g t`. Establish `hcls : ∀ L : LB X, ∀ hL : L.IsLB, topSelfIntersection (ZMod r) ((L.pull ρ).pull i) 1 = topSelfIntersection (ZMod r) (L.pull g) 1` using `fun L hL => by`. Establish `e : cls ((L.pull ρ).pull i) (pull_isLB (pull_isLB hL ρ) i) = cls (L.pull g) (pull_isLB hL g)`. Use `(cls_pull (pull_isLB hL ρ) i _).trans ?_` and prove the remaining obligations. Use `Eq.trans ?_ (cls_pull hL g _).symm` and prove the remaining obligations.

Use `(congrArg (pull i) (cls_pull hL ρ _)).trans ?_` and prove the remaining obligations. Conclude with `(pull_comp i ρ (cls L hL)).symm`. Conclude with `topSelf_congr (ZMod r) (pull_isLB (pull_isLB hL ρ) i) (pull_isLB hL g) ((cls_eq_iff _ _).1 e) 1`. Establish `hW : IsProper (strHom (ZMod r) Z)` using `ArInt.isProper_strHom (ZMod r) (g ≫ t)`. Establish `: CompactSpace Z` using `QuasiCompact.compactSpace_of_compactSpace (strHom (ZMod r) Z)`.

Use `isNoetherian_of_locallyOfFiniteType_field (strHom (ZMod r) Z)` as an intermediate fact. Distinguish the cases in `hc : ∀ z, g z = g (genericPoint Z)`. Use `left`. Introduce `L hL`. Rewrite using `[hcls L hL]`.

Conclude with `ArInt.topSelf_pull_eq_zero_of_const (ZMod r) hL g _ hc`. Use `right`. Use `push_neg at hc`. Take `⟨x₀, hx₀⟩` from `hc`. Set `φ : Z ⟶ g.image` to `g.toImage`.

Establish `e : φ ≫ g.imageι = g` using `g.toImage_imageι`. Establish `: IsProper (φ ≫ g.imageι)` using `by rw [e]; infer_instance`. Establish `: IsProper φ` using `.of_comp φ g.imageι`. Establish `hne : φ x₀ ≠ φ (genericPoint Z)` using `fun h => hx₀ (by`. Rewrite using `[← e, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, h])`.

Establish `: LocallyQuasiFinite φ` using `ProperCurve.locallyQuasiFinite_of_ne hd φ hne`. Establish `: IsFinite φ` using `IsFinite.of_isProper_of_locallyQuasiFinite φ`. Establish `hdense : DenseRange φ` using `g.toImage.denseRange`. Establish `hsurj : Function.Surjective φ`. Rewrite using `[← Set.range_eq_univ, ← φ.isClosedMap.isClosed_range.closure_eq]`.

Conclude with `hdense.closure_range`. Establish `hgen : φ (genericPoint Z) = genericPoint g.image`. Establish `h₁` using `(genericPoint_spec Z).image φ.continuous`. Rewrite `h₁` using `[Set.image_univ, hdense.closure_range]`. Conclude with `h₁.eq (genericPoint_spec _)`.

Establish `hdZ : topologicalKrullDim g.image = 1`. Conclude with `le_antisymm ((PosBaseChange.dim_le_of_isClosedMap φ.isClosedMap hsurj).trans hd.le) (ArInt.one_le_dim (genericPoint_specializes (φ x₀)) fun h => hne (h.symm.trans hgen.symm))`. Establish `hinj` using `ArInt.appTop_injective_of_denseRange φ hdense`. Establish `: CharP Γ(Z, ⊤) r` using `charP_of_injective_algebraMap (algebraMap (ZMod r) Γ(Z, ⊤)).injective r`. Establish `: CharP Γ(g.image, ⊤) r` using `φ.appTop.hom.charP hinj r`.

Use `letI inst : Algebra (ZMod r) Γ(g.image, ⊤) := ZMod.algebra _ r`. Establish `hf (a : ZMod r) : φ.appTop (algebraMap (ZMod r) Γ(g.image, ⊤) a) = algebraMap (ZMod r) Γ(Z, ⊤) a` using `RingHom.congr_fun (RingHom.ext_zmod (φ.appTop.hom.comp (algebraMap (ZMod r) Γ(g.image, ⊤))) (algebraMap (ZMod r) Γ(Z, ⊤))) a`. Establish `: IsProper (g.imageι ≫ t)` using `inferInstance`. Establish `hZ : IsProper (strHom (ZMod r) g.image)` using `ArInt.isProper_strHom (ZMod r) (g.imageι ≫ t)`. Establish `hproj : IsProjOver (strHom (ZMod r) g.image)` using `ProperCurve.isProjOver_of_isProper _ hdZ`.

Use `⟨φ.residueDegree (genericPoint Z), g.image, g.imageι, inferInstance, inferInstance, inst, hdZ, fun L hL => ?_⟩` and prove the remaining obligations. Establish `hN` using `pull_isLB hL g.imageι`. Establish `h₁` using `GlobalTheory.ProjFin.interNumOn_eq_residueDegree_mul (ZMod r) g.image Z φ hproj hdZ hgen (L.pull g.imageι) hN`. Establish `h₂` using `interNumOn_eq_interNum_pull (k := ZMod r) (L := ![L.pull g.imageι]) hf (fun i => by fin_cases i; exact hN)`. Establish `h₃ : topSelfIntersection (ZMod r) (L.pull g) 1 = interNum (ZMod r) (structureModule Z) fun i => (![L.pull g.imageι] i).pull φ`.

Use `interNum_congr_cls _ _ (fun _ => pull_isLB hL g) (fun i => by fin_cases i; exact pull_isLB hN φ) fun i => ?_` and prove the remaining obligations. Use `fin_cases i`. Use `(cls_pull hL g _).trans ?_` and prove the remaining obligations. Use `Eq.trans ?_ (cls_pull hN φ _).symm` and prove the remaining obligations. Conclude with `(congrArg (fun f => pull f (cls L hL)) e.symm).trans (pull_comp φ g.imageι _)`.

Establish `h₄ : interNum (ZMod r) (structureModule g.image) ![L.pull g.imageι] = topSelfIntersection (ZMod r) (L.pull g.imageι) 1`. Use `congrArg _ (funext fun j => ?_)` and prove the remaining obligations. Use `fin_cases j`. Both sides reduce to the same expression. Rewrite using `[hcls L hL, h₃, ← h₂, h₁, h₄]`.
-/
theorem contracted_or_multiple : ∀ (k : Type) [CommRing k] [Module.Finite ℤ k] (X X' : Scheme.{0}) (p : X ⟶ Sp k) (p' : X' ⟶ Sp k),
  IsProjOver p → IsProjOver p' → ∀ (ρ : X' ⟶ X), ρ ≫ p = p' → ∀ (r : ℕ) [Fact r.Prime]
  (Z : Scheme.{0}) (i : Z ⟶ X') [IsClosedImmersion i] [IsIntegral Z] [Algebra (ZMod r) Γ(Z, ⊤)],
  topologicalKrullDim Z = 1 →
    (∀ L : LB X, L.IsLB → topSelfIntersection (ZMod r) ((L.pull ρ).pull i) 1 = 0) ∨
    ∃ (m : ℕ) (Z' : Scheme.{0}) (i' : Z' ⟶ X) (_ : IsClosedImmersion i') (_ : IsIntegral Z')
      (_ : Algebra (ZMod r) Γ(Z', ⊤)), topologicalKrullDim Z' = 1 ∧
      ∀ L : LB X, L.IsLB → topSelfIntersection (ZMod r) ((L.pull ρ).pull i) 1 = (m : ℤ) * topSelfIntersection (ZMod r) (L.pull i') 1 := by
  intro k _ _ X X' p p' hp hp' ρ hρ r _ Z i _ _ _ hd
  obtain ⟨N, j, _, hj⟩ := hp
  have := isProper_str k N
  have : IsProper p := hj ▸ inferInstance
  obtain ⟨N', j', _, hj'⟩ := hp'
  have := isProper_str k N'
  have : IsProper p' := hj' ▸ inferInstance
  have : IsFinite (spMap (Int.castRingHom k)) := by
    rw [spMap, IsFinite.SpecMap_iff]
    exact (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
  have : IsProper (ρ ≫ p) := by rw [hρ]; infer_instance
  have : IsProper ρ := .of_comp ρ p
  let t := p ≫ spMap (Int.castRingHom k)
  let g := i ≫ ρ
  have : IsProper (g ≫ t) := by simp only [g, t]; infer_instance
  have : IsProper g := .of_comp g t
  have hcls : ∀ L : LB X, ∀ hL : L.IsLB,
      topSelfIntersection (ZMod r) ((L.pull ρ).pull i) 1 = topSelfIntersection (ZMod r) (L.pull g) 1 := fun L hL => by
    have e : cls ((L.pull ρ).pull i) (pull_isLB (pull_isLB hL ρ) i) = cls (L.pull g) (pull_isLB hL g) := by
      refine (cls_pull (pull_isLB hL ρ) i _).trans ?_
      refine Eq.trans ?_ (cls_pull hL g _).symm
      refine (congrArg (pull i) (cls_pull hL ρ _)).trans ?_
      exact (pull_comp i ρ (cls L hL)).symm
    exact topSelf_congr (ZMod r) (pull_isLB (pull_isLB hL ρ) i) (pull_isLB hL g) ((cls_eq_iff _ _).1 e) 1
  have hW : IsProper (strHom (ZMod r) Z) := ArInt.isProper_strHom (ZMod r) (g ≫ t)
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace (strHom (ZMod r) Z)
  have := isNoetherian_of_locallyOfFiniteType_field (strHom (ZMod r) Z)
  by_cases hc : ∀ z, g z = g (genericPoint Z)
  · left
    intro L hL
    rw [hcls L hL]
    exact ArInt.topSelf_pull_eq_zero_of_const (ZMod r) hL g _ hc
  right
  push_neg at hc
  obtain ⟨x₀, hx₀⟩ := hc
  let φ : Z ⟶ g.image := g.toImage
  have e : φ ≫ g.imageι = g := g.toImage_imageι
  have : IsProper (φ ≫ g.imageι) := by rw [e]; infer_instance
  have : IsProper φ := .of_comp φ g.imageι
  have hne : φ x₀ ≠ φ (genericPoint Z) := fun h => hx₀ (by
    rw [← e, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, h])
  have : LocallyQuasiFinite φ := ProperCurve.locallyQuasiFinite_of_ne hd φ hne
  have : IsFinite φ := IsFinite.of_isProper_of_locallyQuasiFinite φ
  have hdense : DenseRange φ := g.toImage.denseRange
  have hsurj : Function.Surjective φ := by
    rw [← Set.range_eq_univ, ← φ.isClosedMap.isClosed_range.closure_eq]
    exact hdense.closure_range
  have hgen : φ (genericPoint Z) = genericPoint g.image := by
    have h₁ := (genericPoint_spec Z).image φ.continuous
    rw [Set.image_univ, hdense.closure_range] at h₁
    exact h₁.eq (genericPoint_spec _)
  have hdZ : topologicalKrullDim g.image = 1 := by
    exact le_antisymm ((PosBaseChange.dim_le_of_isClosedMap φ.isClosedMap hsurj).trans hd.le)
      (ArInt.one_le_dim (genericPoint_specializes (φ x₀)) fun h => hne (h.symm.trans hgen.symm))
  have hinj := ArInt.appTop_injective_of_denseRange φ hdense
  have : CharP Γ(Z, ⊤) r := charP_of_injective_algebraMap (algebraMap (ZMod r) Γ(Z, ⊤)).injective r
  have : CharP Γ(g.image, ⊤) r := φ.appTop.hom.charP hinj r
  letI inst : Algebra (ZMod r) Γ(g.image, ⊤) := ZMod.algebra _ r
  have hf (a : ZMod r) : φ.appTop (algebraMap (ZMod r) Γ(g.image, ⊤) a) = algebraMap (ZMod r) Γ(Z, ⊤) a :=
    RingHom.congr_fun (RingHom.ext_zmod (φ.appTop.hom.comp (algebraMap (ZMod r) Γ(g.image, ⊤)))
      (algebraMap (ZMod r) Γ(Z, ⊤))) a
  have : IsProper (g.imageι ≫ t) := inferInstance
  have hZ : IsProper (strHom (ZMod r) g.image) := ArInt.isProper_strHom (ZMod r) (g.imageι ≫ t)
  have hproj : IsProjOver (strHom (ZMod r) g.image) := ProperCurve.isProjOver_of_isProper _ hdZ
  refine ⟨φ.residueDegree (genericPoint Z), g.image, g.imageι, inferInstance, inferInstance, inst, hdZ,
    fun L hL => ?_⟩
  have hN := pull_isLB hL g.imageι
  have h₁ := GlobalTheory.ProjFin.interNumOn_eq_residueDegree_mul (ZMod r) g.image Z φ hproj hdZ hgen (L.pull g.imageι) hN
  have h₂ := interNumOn_eq_interNum_pull (k := ZMod r) (L := ![L.pull g.imageι]) hf
    (fun i => by fin_cases i; exact hN)
  have h₃ : topSelfIntersection (ZMod r) (L.pull g) 1 =
      interNum (ZMod r) (structureModule Z) fun i => (![L.pull g.imageι] i).pull φ := by
    refine interNum_congr_cls _ _ (fun _ => pull_isLB hL g) (fun i => by fin_cases i; exact pull_isLB hN φ) fun i => ?_
    fin_cases i
    refine (cls_pull hL g _).trans ?_
    refine Eq.trans ?_ (cls_pull hN φ _).symm
    exact (congrArg (fun f => pull f (cls L hL)) e.symm).trans (pull_comp φ g.imageι _)
  have h₄ : interNum (ZMod r) (structureModule g.image) ![L.pull g.imageι] =
      topSelfIntersection (ZMod r) (L.pull g.imageι) 1 := by
    refine congrArg _ (funext fun j => ?_)
    fin_cases j
    rfl
  rw [hcls L hL, h₃, ← h₂, h₁, h₄]

end GlobalTheory.CurveReduce
