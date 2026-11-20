import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentedBundleSectionsRationalFunctionsDict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianRepresentativeIntegerCombinationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddGroupFGLineBundleSectionsArithmeticVarietyStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HSNef.PairFG

/- English proof (translation)
Take `⟨ρ, hρ, hu, -⟩` from `hM`. Take `⟨e, he⟩` from `RepDict.exists_quot M.isLB hρ`. Establish `hcov {B : LB X} (hB : B.IsLB) (x : X) : ∃ c, x ∈ B.U c` using `Opens.mem_iSup.1 (hB.cover.ge (Opens.mem_top _))`. Take `⟨c₀, h₀⟩` from `hcov M.isLB (genericPoint X)`. Establish `hρ₀` using `(ρ c₀).ne_zero`.

Set `φ : M.B.Sec →+ X.functionField` to `{ toFun := e map_zero' := by`. Use `mul_right_cancel₀ hρ₀ ?_` and prove the remaining obligations. Rewrite using `[he 0 c₀ h₀, zero_mul]`. Conclude with `map_zero _`. Use the proof step `map_add' := fun u v => by`.

Use `mul_right_cancel₀ hρ₀ ?_` and prove the remaining obligations. Rewrite using `[he (u + v) c₀ h₀, add_mul, he u c₀ h₀, he v c₀ h₀]`. Conclude with `map_add _ _ _ }`. Establish `hl (f : X.functionField) c i j : P.loc a b f i j * ((ρ c : X.functionField) / P.loc a b 1 i j) = f * ρ c`. Use `(P.r i).ne_zero` as an intermediate fact.

Use `(P.r' j).ne_zero` as an intermediate fact. Simplify using `only [Pair.loc]`. Clear the denominators using the available nonvanishing facts. Establish `hl' (f : X.functionField) c i j : P.loc a b f i j = f * ρ c * ((ρ c : X.functionField) / P.loc a b 1 i j)⁻¹`. Use `(P.r i).ne_zero` as an intermediate fact.

Use `(P.r' j).ne_zero` as an intermediate fact. Use `(ρ c).ne_zero` as an intermediate fact. Simplify using `only [Pair.loc]`. Clear the denominators using the available nonvanishing facts. Use `⟨φ, le_antisymm ?_ fun f hf => ?_⟩` and prove the remaining obligations.

Introduce and unpack `_ ⟨u, rfl⟩ x i j hi hj`. Take `⟨c, hc⟩` from `hcov M.isLB x`. Express the relevant statement in the definitionally equal form `RegAt x (P.loc a b (e u) i j)`. Rewrite using `[hl' _ c, he u c (gen_mem hc)]`. Conclude with `(regAt_fnOf hc _ _).mul (hu x c i j hc hi hj).inv.regAt`.

Take `⟨u, hu'⟩` from `RepDict.exists_sec hρ (f := f) fun c x hc => by`. Take `⟨i, hi⟩` from `hcov P.L.isLB x`. Take `⟨j, hj⟩` from `hcov P.A.isLB x`. Rewrite using `[← hl f c i j]`. Conclude with `(hf x i j hi hj).mul (hu x c i j hc hi hj).regAt`.

Conclude with `⟨u, mul_right_cancel₀ hρ₀ ((he u c₀ h₀).trans (hu' c₀ h₀))⟩`.
-/
theorem exists_hom {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} (P : Pair p) (a b : ℤ)
    (M : HermLB p) (hM : P.Rep a b M) :
    ∃ φ : M.B.Sec →+ X.functionField, φ.range = P.H a b := by
  obtain ⟨ρ, hρ, hu, -⟩ := hM
  obtain ⟨e, he⟩ := RepDict.exists_quot M.isLB hρ
  have hcov {B : LB X} (hB : B.IsLB) (x : X) : ∃ c, x ∈ B.U c :=
    Opens.mem_iSup.1 (hB.cover.ge (Opens.mem_top _))
  obtain ⟨c₀, h₀⟩ := hcov M.isLB (genericPoint X)
  have hρ₀ := (ρ c₀).ne_zero
  let φ : M.B.Sec →+ X.functionField :=
    { toFun := e
      map_zero' := by
        refine mul_right_cancel₀ hρ₀ ?_
        rw [he 0 c₀ h₀, zero_mul]
        exact map_zero _
      map_add' := fun u v => by
        refine mul_right_cancel₀ hρ₀ ?_
        rw [he (u + v) c₀ h₀, add_mul, he u c₀ h₀, he v c₀ h₀]
        exact map_add _ _ _ }
  have hl (f : X.functionField) c i j :
      P.loc a b f i j * ((ρ c : X.functionField) / P.loc a b 1 i j) = f * ρ c := by
    have := (P.r i).ne_zero
    have := (P.r' j).ne_zero
    simp only [Pair.loc]
    field_simp
  have hl' (f : X.functionField) c i j :
      P.loc a b f i j = f * ρ c * ((ρ c : X.functionField) / P.loc a b 1 i j)⁻¹ := by
    have := (P.r i).ne_zero
    have := (P.r' j).ne_zero
    have := (ρ c).ne_zero
    simp only [Pair.loc]
    field_simp
  refine ⟨φ, le_antisymm ?_ fun f hf => ?_⟩
  · rintro _ ⟨u, rfl⟩ x i j hi hj
    obtain ⟨c, hc⟩ := hcov M.isLB x
    change RegAt x (P.loc a b (e u) i j)
    rw [hl' _ c, he u c (gen_mem hc)]
    exact (regAt_fnOf hc _ _).mul (hu x c i j hc hi hj).inv.regAt
  · obtain ⟨u, hu'⟩ := RepDict.exists_sec hρ (f := f) fun c x hc => by
      obtain ⟨i, hi⟩ := hcov P.L.isLB x
      obtain ⟨j, hj⟩ := hcov P.A.isLB x
      rw [← hl f c i j]
      exact (hf x i j hi hj).mul (hu x c i j hc hi hj).regAt
    exact ⟨u, mul_right_cancel₀ hρ₀ ((he u c₀ h₀).trans (hu' c₀ h₀))⟩

/- English proof (translation)
Introduce `k _ X _ p D hX P a b`. Take `⟨M, hM⟩` from `GlobalTheory.T.exists_hermitianRepresentative_integerCombination k X p P a b`. Take `⟨φ, hφ⟩` from `exists_hom P a b M hM`. Use `GlobalTheory.T.addGroupFG_lineBundleSections_arithmeticVariety k X p D hX M.B M.isLB` as an intermediate fact. Rewrite using `[← hφ, AddMonoidHom.range_eq_map]`.

Take `⟨S, hS⟩` from `this.out`. Conclude with `⟨S.image φ, by rw [Finset.coe_image, ← AddMonoidHom.map_closure, hS]⟩`.
-/
theorem h_fg : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
    ∀ (P : Pair p) (a b : ℤ), (P.H a b).FG := by
  intro k _ X _ p D hX P a b
  obtain ⟨M, hM⟩ := GlobalTheory.T.exists_hermitianRepresentative_integerCombination k X p P a b
  obtain ⟨φ, hφ⟩ := exists_hom P a b M hM
  have := GlobalTheory.T.addGroupFG_lineBundleSections_arithmeticVariety k X p D hX M.B M.isLB
  rw [← hφ, AddMonoidHom.range_eq_map]
  classical
  obtain ⟨S, hS⟩ := this.out
  exact ⟨S.image φ, by rw [Finset.coe_image, ← AddMonoidHom.map_closure, hS]⟩

end GlobalTheory.HSNef.PairFG
