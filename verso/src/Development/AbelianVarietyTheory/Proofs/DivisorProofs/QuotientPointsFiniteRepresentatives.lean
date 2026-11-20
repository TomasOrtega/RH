import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramSub
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiUnitOnOfFixedOverUnramifiedExtension
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
namespace GlobalTheory.Mum

/- English proof (translation)
Introduce `R _ _ D hB F _ _ k hk hfin`. Use `letI := GlobalTheory.TorusExt.gtGroup D F`. Distinguish the cases in `hne : Nonempty (QkPt D F k)`. Use `swap`. Conclude with `⟨∅, Set.finite_empty, fun p => (hne ⟨p⟩).elim⟩`.

Set `K : AddSubgroup D.X` to `(nsmulAddMonoidHom (α := D.X) k).range`. Use `haveI : K.FiniteIndex := ⟨by`. Simplify using `only [K, AddSubgroup.index_range_nsmul]`. Conclude with `pow_ne_zero _ hk⟩`. Use `haveI : Finite (D.X ⧸ K) := AddSubgroup.finite_quotient_of_finiteIndex`.

Set `Q : QkPt D F k → D.X ⧸ K` to `fun p => (p.y : D.X ⧸ K)`. Set `bp : D.X ⧸ K → QkPt D F k` to `Function.invFun Q`. Establish `hbp : ∀ p, Q (bp (Q p)) = Q p` using `fun p => Function.invFun_eq ⟨p, rfl⟩`. Establish `hz : ∀ p, ∃ z : D.X, k • z = -(bp (Q p)).y + p.y`. Introduce `p`.

Establish `h` using `QuotientAddGroup.eq.mp (hbp p)`. Take `⟨z, hz⟩` from `AddMonoidHom.mem_range.mp h`. Conclude with `⟨z, by simpa using hz⟩`. Set `zOf : QkPt D F k → D.X` to `fun p => (hz p).choose`. Establish `hzOf : ∀ p, k • zOf p = -(bp (Q p)).y + p.y` using `fun p => (hz p).choose_spec`.

Set `δ : QkPt D F k → GtPtF D F` to `fun p => p.g - (bp (Q p)).g - GlobalTheory.TorusExt.iota hB F (zOf p)`. Establish `hδk : ∀ p, k • δ p = 0`. Introduce `p`. Simplify using `only [δ, smul_sub, GlobalTheory.TorusExt.qk_nsmul hB, ← map_nsmul, hzOf]`. Rewrite using `[map_add, map_neg]`.

Normalize the expressions using the abelian group laws. Establish `hδb : ∀ p, (δ p).b ^ k = 1`. Introduce `p`. Rewrite using `[← GlobalTheory.TorusExt.nsmul_b, hδk p, GlobalTheory.TorusExt.zero_b]`. Set `Φ : QkPt D F k → (D.X ⧸ K) × {x : TF (R` to `R) F ⟶ D.P.A // x ^ k = 1} := fun p => (Q p, ⟨(δ p).b, hδb p⟩)`.

Set `rep : (D.X ⧸ K) × {x : TF (R` to `R) F ⟶ D.P.A // x ^ k = 1} → QkPt D F k := Function.invFun Φ`. Establish `hrep : ∀ p, Φ (rep (Φ p)) = Φ p` using `fun p => Function.invFun_eq ⟨p, rfl⟩`. Use `⟨Set.range (rep ∘ Φ), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Set.range_comp]`. Conclude with `(Set.toFinite _).image _`.

Introduce `p`. Use `set p' := rep (Φ p) with hp'`. Establish `h1 : Q p' = Q p` using `congrArg Prod.fst (hrep p)`. Establish `h2 : (δ p').b = (δ p).b` using `congrArg (fun x => x.2.1) (hrep p)`. Use `⟨p', ⟨p, rfl⟩, zOf p - zOf p', δ p - δ p', ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[sub_eq_add_neg, GlobalTheory.TorusExt.add_b, GlobalTheory.TorusExt.neg_b, h2, mul_inv_cancel]`. Rewrite using `[smul_sub, hδk, hδk, sub_zero]`. Establish `hb : bp (Q p') = bp (Q p)` using `by rw [h1]`. Simplify using `only [δ, hb, map_sub]`. Normalize the expressions using the abelian group laws.
-/
theorem qkPt_finite_reps : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (hB : D.TauBimult) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), k ≠ 0 → Finite {x : TF (R := R) F ⟶ D.P.A // x ^ k = 1} → ∃ Rep : Set (QkPt D F k), Rep.Finite ∧ ∀ p : QkPt D F k, ∃ p' ∈ Rep, ∃ (z : D.X) (t : GtPtF D F), t.b = 1 ∧ (letI := GlobalTheory.TorusExt.gtGroup D F; k • t = 0 ∧ p.g = p'.g + GlobalTheory.TorusExt.iota hB F z + t) := by
  intro R _ _ D hB F _ _ k hk hfin
  letI := GlobalTheory.TorusExt.gtGroup D F
  classical
  by_cases hne : Nonempty (QkPt D F k)
  swap
  · exact ⟨∅, Set.finite_empty, fun p => (hne ⟨p⟩).elim⟩
  let K : AddSubgroup D.X := (nsmulAddMonoidHom (α := D.X) k).range
  haveI : K.FiniteIndex := ⟨by
    simp only [K, AddSubgroup.index_range_nsmul]; exact pow_ne_zero _ hk⟩
  haveI : Finite (D.X ⧸ K) := AddSubgroup.finite_quotient_of_finiteIndex
  let Q : QkPt D F k → D.X ⧸ K := fun p => (p.y : D.X ⧸ K)
  let bp : D.X ⧸ K → QkPt D F k := Function.invFun Q
  have hbp : ∀ p, Q (bp (Q p)) = Q p := fun p => Function.invFun_eq ⟨p, rfl⟩
  have hz : ∀ p, ∃ z : D.X, k • z = -(bp (Q p)).y + p.y := by
    intro p
    have h := QuotientAddGroup.eq.mp (hbp p)
    obtain ⟨z, hz⟩ := AddMonoidHom.mem_range.mp h
    exact ⟨z, by simpa using hz⟩
  let zOf : QkPt D F k → D.X := fun p => (hz p).choose
  have hzOf : ∀ p, k • zOf p = -(bp (Q p)).y + p.y := fun p => (hz p).choose_spec
  let δ : QkPt D F k → GtPtF D F := fun p =>
    p.g - (bp (Q p)).g - GlobalTheory.TorusExt.iota hB F (zOf p)
  have hδk : ∀ p, k • δ p = 0 := by
    intro p
    simp only [δ, smul_sub, GlobalTheory.TorusExt.qk_nsmul hB, ← map_nsmul, hzOf]
    rw [map_add, map_neg]; abel
  have hδb : ∀ p, (δ p).b ^ k = 1 := by
    intro p
    rw [← GlobalTheory.TorusExt.nsmul_b, hδk p, GlobalTheory.TorusExt.zero_b]
  let Φ : QkPt D F k → (D.X ⧸ K) × {x : TF (R := R) F ⟶ D.P.A // x ^ k = 1} :=
    fun p => (Q p, ⟨(δ p).b, hδb p⟩)
  let rep : (D.X ⧸ K) × {x : TF (R := R) F ⟶ D.P.A // x ^ k = 1} → QkPt D F k :=
    Function.invFun Φ
  have hrep : ∀ p, Φ (rep (Φ p)) = Φ p := fun p => Function.invFun_eq ⟨p, rfl⟩
  refine ⟨Set.range (rep ∘ Φ), ?_, ?_⟩
  · rw [Set.range_comp]; exact (Set.toFinite _).image _
  intro p
  set p' := rep (Φ p) with hp'
  have h1 : Q p' = Q p := congrArg Prod.fst (hrep p)
  have h2 : (δ p').b = (δ p).b := congrArg (fun x => x.2.1) (hrep p)
  refine ⟨p', ⟨p, rfl⟩, zOf p - zOf p', δ p - δ p', ?_, ?_, ?_⟩
  · rw [sub_eq_add_neg, GlobalTheory.TorusExt.add_b, GlobalTheory.TorusExt.neg_b, h2, mul_inv_cancel]
  · rw [smul_sub, hδk, hδk, sub_zero]
  · have hb : bp (Q p') = bp (Q p) := by rw [h1]
    simp only [δ, hb, map_sub]
    abel

end GlobalTheory.Mum
