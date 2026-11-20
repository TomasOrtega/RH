import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefSetNonemptyOfNonneg
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.LocM.FJ
open GlobalTheory.Toroidal
open GlobalTheory.ArcQ (Wit LieImg)

namespace GlobalTheory.LocM.FJ

/- English proof (translation)
Establish `hr : Set.range (x ≫ Z.π) ⊆ Set.range (Y Z.i).j`. Introduce and unpack `_ ⟨q, rfl⟩`. Establish `h1 : x q ∈ ((Z.U a).1 : Set Z.X)`. Rewrite using `[← hx, Scheme.Hom.comp_apply]`. Use `(Z.U a).2.range_fromSpec` as an intermediate fact.

Rewrite using `[← this]`. Conclude with `⟨_, rfl⟩`. Establish `h2 : x q ∈ Z.opn` using `Z.cover ▸ Set.mem_iUnion.2 ⟨a, h1⟩`. Conclude with `h2`. Take `⟨f, y, hy, hyj⟩` from `Cht.exists_pt_of_range (Y := Y) Z.i k (x ≫ Z.π) hr`.

Establish `e₁ : spMap (f.comp (Z.i.c.V W).subtype) = spMap ((φ.comp (Z.alg a)).comp (Z.i.c.V W).subtype)`. Rewrite using `[spMap_comp, ← hy, Category.assoc, ← (Y Z.i).j_s, ← Category.assoc, hyj, Category.assoc, Z.π_s, ← hx, Category.assoc, Z.alg_s, ← spMap_comp]`. Establish `e₂ : f.comp (Z.i.c.V W).subtype = (φ.comp (Z.alg a)).comp (Z.i.c.V W).subtype` using `congrArg CommRingCat.Hom.hom (Spec.map_injective e₁)`. Establish `hf : f = φ.comp (Z.alg a)` using `IsLocalization.ringHom_ext (nonZeroDivisors (Z.i.c.V W)) e₂`. Conclude with `⟨y, hf ▸ hy, hyj⟩`.
-/
theorem exists_pt_of_flagAt {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W}
    {i₀ : Idx H p} (Z : Mdl Y i₀) {k : Type} [Field k] (x : Sp k ⟶ Z.X) (a : Fin Z.m)
    (φ : Γ(Z.X, (Z.U a).1) →+* k) (hx : spMap φ ≫ Z.chart a = x) :
    ∃ y : Sp k ⟶ (Xo Z.i.l).XF Z.i.c, y ≫ pullback.snd _ _ = spMap (φ.comp (Z.alg a)) ∧ y ≫ (Y Z.i).j = x ≫ Z.π := by
  have hr : Set.range (x ≫ Z.π) ⊆ Set.range (Y Z.i).j := by
    rintro _ ⟨q, rfl⟩
    have h1 : x q ∈ ((Z.U a).1 : Set Z.X) := by
      rw [← hx, Scheme.Hom.comp_apply]
      have := (Z.U a).2.range_fromSpec
      rw [← this]
      exact ⟨_, rfl⟩
    have h2 : x q ∈ Z.opn := Z.cover ▸ Set.mem_iUnion.2 ⟨a, h1⟩
    exact h2
  obtain ⟨f, y, hy, hyj⟩ := Cht.exists_pt_of_range (Y := Y) Z.i k (x ≫ Z.π) hr
  have e₁ : spMap (f.comp (Z.i.c.V W).subtype) = spMap ((φ.comp (Z.alg a)).comp (Z.i.c.V W).subtype) := by
    rw [spMap_comp, ← hy, Category.assoc, ← (Y Z.i).j_s, ← Category.assoc, hyj, Category.assoc, Z.π_s, ← hx,
      Category.assoc, Z.alg_s, ← spMap_comp]
  have e₂ : f.comp (Z.i.c.V W).subtype = (φ.comp (Z.alg a)).comp (Z.i.c.V W).subtype :=
    congrArg CommRingCat.Hom.hom (Spec.map_injective e₁)
  have hf : f = φ.comp (Z.alg a) :=
    IsLocalization.ringHom_ext (nonZeroDivisors (Z.i.c.V W)) e₂
  exact ⟨y, hf ▸ hy, hyj⟩

/- English proof (translation)
Introduce `E _ _ _ H Dw Xo p W Y i₀ Z k _ x x' v hπ hx hx'`. Take `⟨a, φ, hφ, hfr, -⟩` from `id hx`. Take `⟨y, hy, hyj⟩` from `exists_pt_of_flagAt Z x a φ hφ`. Establish `hfr' : IsFrame (Y Z.i).t (φ.comp (Z.alg a)) (y ≫ (Y Z.i).j) v` using `hyj ▸ hfr`. Conclude with `(Z.bij k _ y hy v hfr').unique ⟨hyj.symm, hx⟩ ⟨hπ ▸ hyj.symm, hx'⟩`.
-/
theorem eq_of_flagAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z : Mdl Y i₀) (k : Type) [Field k] (x x' : Sp k ⟶ Z.X) (v : Vecs Dw (Y Z.i).t k), x ≫ Z.π = x' ≫ Z.π → Z.FlagAt x v → Z.FlagAt x' v → x = x' := by
  intro E _ _ _ H Dw Xo p W Y i₀ Z k _ x x' v hπ hx hx'
  obtain ⟨a, φ, hφ, hfr, -⟩ := id hx
  obtain ⟨y, hy, hyj⟩ := exists_pt_of_flagAt Z x a φ hφ
  have hfr' : IsFrame (Y Z.i).t (φ.comp (Z.alg a)) (y ≫ (Y Z.i).j) v := hyj ▸ hfr
  exact (Z.bij k _ y hy v hfr').unique ⟨hyj.symm, hx⟩ ⟨hπ ▸ hyj.symm, hx'⟩

end GlobalTheory.LocM.FJ
