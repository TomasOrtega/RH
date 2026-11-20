import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.FlatModel

/- English proof (translation)
Introduce `E _ _ _ H Dw l' Xo' c' W Y p _ n _ hl yb yy P π ψ hP`. Take `⟨h1, h2, h3, h4, h5, h6⟩` from `hP`. Take `⟨β₀, hβ₀⟩ : ∃ β₀ : KA l' →+* ℂ_[p], yy ≫ (pullback.fst _ _ ≫ Xo'.s) = spMap β₀` from `⟨(Spec.preimage (yy ≫ (pullback.fst _ _ ≫ Xo'.s))).hom, by simp [spMap]⟩`. Take `⟨-, I, -, hI, -⟩` from `Y.oF.geom ℂ_[p] yy β₀ hβ₀`. Take `⟨e, he⟩` from `GlobalTheory.LiePull.exists_pushEquiv h4 (Over.mk (𝟙 _)) yy (Category.id_comp _).symm`.

Establish `hact : ∀ o : 𝓞 E, (P.oA.act o).left ≫ ψ = ψ ≫ (Y.oF.t.act.act o).left`. Introduce `o`. Apply `Y.m.cart.1.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, Category.assoc, h5, Y.m.act o, ← Category.assoc ψ, h5, ← Category.assoc, P.gen_act o, Category.assoc, Category.assoc, h3 o]`. Rewrite using `[Category.assoc, Category.assoc, Over.w (Y.oF.t.act.act o), h4.1.w, ← Category.assoc, Over.w]`.

Establish `hlin : ∀ (x : Over.mk (𝟙 (Sp ℂ_[p])) ⟶ P.A.A) (o : 𝓞 E), e (x ≫ P.oA.act o) = e x ≫ Y.oF.t.act.act o`. Introduce `x o`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[he, Over.comp_left, Over.comp_left, he, Category.assoc, Category.assoc, hact]`. Establish `hsymm : ∀ y : Over.mk yy ⟶ Y.oF.t.G, (e.symm y).left ≫ ψ = y.left` using `fun y => by`.

Rewrite using `[← he, MulEquiv.apply_symm_apply]`. Establish `hweil : ∀ (g : Sp ℂ_[p] ⟶ Xo'.XF c'), 𝟙 _ ≫ yy = g → ∀ (k : ℤ) (x y : Over.mk (𝟙 (Sp ℂ_[p])) ⟶ P.A.A) (x₀ y₀ : Over.mk g ⟶ Y.oF.t.G) (c : (Γ(Sp ℂ_[p], ⊤))ˣ), x₀.left = x.left ≫ ψ → y₀.left = y.left ≫ ψ → (Out.WeilIs P.A.A P.A.L k x y c ↔ Out.WeilIs Y.oF.t.G Y.oF.t.PP.L k x₀ y₀ c)`. Introduce and unpack `g rfl k x y x₀ y₀ c hx hy`. Conclude with `GlobalTheory.weilIs_grpPullback_of_comm _ _ Y.oF.t.G P.A.A yy ψ Y.oF.t.PP.L P.A.L Y.oF.t.PP.isLB P.A.isLB h4 h6 (Over.mk (𝟙 _)) k x y x₀ y₀ c hx hy`. Establish `onto : ∀ k, 0 < k → ∀ x : Over.mk (𝟙 (Sp ℂ_[p])) ⟶ P.A.A, x ^ k = 1 ↔ ∃ a, e.symm (I.ev k a) = x`.

Introduce `k hk x`. Rewrite using `[← e.injective.eq_iff, map_pow, map_one, I.onto k hk]`. Simplify using `only [MulEquiv.symm_apply_eq]`. Use `⟨fun k a => e.symm (I.ev k a), I.ζ, I.ζ_prim, I.ζ_pow, ?_, ?_, onto, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `k a b`.

Simplify using `only [I.add, map_mul]`. Introduce `k o a`. Apply `e.injective` to reduce the goal to its premises. Rewrite using `[hlin, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]`. Conclude with `I.lin k o a`.

Introduce `k m hk hm a`. Simplify using `only [← map_pow, I.tower k m hk hm a]`. Introduce `k hk a b`. Establish `hza : (e.symm (I.ev k a)) ^ k = 1` using `(onto k hk _).2 ⟨a, rfl⟩`. Establish `hzb : (e.symm (I.ev k b)) ^ k = 1` using `(onto k hk _).2 ⟨b, rfl⟩`.

Use `((GlobalTheory.HTLat.weilIs_iff (A := P.A) (Nat.one_le_iff_ne_zero.2 hk.ne') hza hzb _).1 ?_).symm` and prove the remaining obligations. Rewrite using `[hweil yy (Category.id_comp yy) _ _ _ (I.ev k a) (I.ev k b) _ (hsymm _).symm (hsymm _).symm]`. Conclude with `I.isom k hk a b`. Introduce `a`. Rewrite using `[hsymm, ← hl, ← hI a, Over.comp_left]`.

Use `congr 1`.
-/
theorem tateIso_transport_ptOn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l' : Level H) (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (p : ℕ) [Fact p.Prime] (n : ℕ) [StarRing (𝓞 E)], l'.A = p ^ n →
    ∀ (yb : Sp 𝓞_ℂ_[p] ⟶ Y.X) (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (P : PtP E p) (π : P.G.left ⟶ Y.t.G.left)
      (ψ : P.A.A.left ⟶ Y.oF.t.G.left), PtOn Y yb yy P π ψ →
    ∃ (ev : ℕ → Dw.La → (Over.mk (𝟙 (Sp ℂ_[p])) ⟶ P.A.A)) (ζ : ℕ → ℂ_[p]ˣ),
      (∀ k, 0 < k → IsPrimitiveRoot (ζ k) k) ∧ (∀ k m, 0 < k → 0 < m → ζ (k * m) ^ m = ζ k) ∧
      (∀ k a b, ev k (a + b) = ev k a * ev k b) ∧ (∀ k (o : 𝓞 E) a, ev k (o • a) = ev k a ≫ P.oA.act o) ∧
      (∀ k, 0 < k → ∀ x, x ^ k = 1 ↔ ∃ a, ev k a = x) ∧
      (∀ k m, 0 < k → 0 < m → ∀ a, ev (k * m) a ^ m = ev k a) ∧
      (∀ k, 0 < k → ∀ a b, weil P.A k (ev k a) (ev k b) = ζ k ^ Dw.EF a b) ∧
      ∀ a, (ev (p ^ n) a).left ≫ ψ = yy ≫ (Y.oF.etaA a).left := by
  intro E _ _ _ H Dw l' Xo' c' W Y p _ n _ hl yb yy P π ψ hP
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hP
  obtain ⟨β₀, hβ₀⟩ : ∃ β₀ : KA l' →+* ℂ_[p], yy ≫ (pullback.fst _ _ ≫ Xo'.s) = spMap β₀ :=
    ⟨(Spec.preimage (yy ≫ (pullback.fst _ _ ≫ Xo'.s))).hom, by simp [spMap]⟩
  obtain ⟨-, I, -, hI, -⟩ := Y.oF.geom ℂ_[p] yy β₀ hβ₀
  obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv h4 (Over.mk (𝟙 _)) yy (Category.id_comp _).symm
  have hact : ∀ o : 𝓞 E, (P.oA.act o).left ≫ ψ = ψ ≫ (Y.oF.t.act.act o).left := by
    intro o
    apply Y.m.cart.1.hom_ext
    · rw [Category.assoc, Category.assoc, h5, Y.m.act o, ← Category.assoc ψ, h5, ← Category.assoc, P.gen_act o,
        Category.assoc, Category.assoc, h3 o]
    · rw [Category.assoc, Category.assoc, Over.w (Y.oF.t.act.act o), h4.1.w, ← Category.assoc, Over.w]
  have hlin : ∀ (x : Over.mk (𝟙 (Sp ℂ_[p])) ⟶ P.A.A) (o : 𝓞 E), e (x ≫ P.oA.act o) = e x ≫ Y.oF.t.act.act o := by
    intro x o
    apply Over.OverMorphism.ext
    rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, Category.assoc, hact]
  have hsymm : ∀ y : Over.mk yy ⟶ Y.oF.t.G, (e.symm y).left ≫ ψ = y.left := fun y => by
    rw [← he, MulEquiv.apply_symm_apply]
  have hweil : ∀ (g : Sp ℂ_[p] ⟶ Xo'.XF c'), 𝟙 _ ≫ yy = g → ∀ (k : ℤ) (x y : Over.mk (𝟙 (Sp ℂ_[p])) ⟶ P.A.A)
      (x₀ y₀ : Over.mk g ⟶ Y.oF.t.G) (c : (Γ(Sp ℂ_[p], ⊤))ˣ), x₀.left = x.left ≫ ψ → y₀.left = y.left ≫ ψ →
      (Out.WeilIs P.A.A P.A.L k x y c ↔ Out.WeilIs Y.oF.t.G Y.oF.t.PP.L k x₀ y₀ c) := by
    rintro g rfl k x y x₀ y₀ c hx hy
    exact GlobalTheory.weilIs_grpPullback_of_comm _ _ Y.oF.t.G P.A.A yy ψ Y.oF.t.PP.L P.A.L Y.oF.t.PP.isLB P.A.isLB h4 h6
      (Over.mk (𝟙 _)) k x y x₀ y₀ c hx hy
  have onto : ∀ k, 0 < k → ∀ x : Over.mk (𝟙 (Sp ℂ_[p])) ⟶ P.A.A, x ^ k = 1 ↔ ∃ a, e.symm (I.ev k a) = x := by
    intro k hk x
    rw [← e.injective.eq_iff, map_pow, map_one, I.onto k hk]
    simp only [MulEquiv.symm_apply_eq]
  refine ⟨fun k a => e.symm (I.ev k a), I.ζ, I.ζ_prim, I.ζ_pow, ?_, ?_, onto, ?_, ?_, ?_⟩
  · intro k a b
    simp only [I.add, map_mul]
  · intro k o a
    apply e.injective
    rw [hlin, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    exact I.lin k o a
  · intro k m hk hm a
    simp only [← map_pow, I.tower k m hk hm a]
  · intro k hk a b
    have hza : (e.symm (I.ev k a)) ^ k = 1 := (onto k hk _).2 ⟨a, rfl⟩
    have hzb : (e.symm (I.ev k b)) ^ k = 1 := (onto k hk _).2 ⟨b, rfl⟩
    refine ((GlobalTheory.HTLat.weilIs_iff (A := P.A) (Nat.one_le_iff_ne_zero.2 hk.ne') hza hzb _).1 ?_).symm
    rw [hweil yy (Category.id_comp yy) _ _ _ (I.ev k a) (I.ev k b) _ (hsymm _).symm (hsymm _).symm]
    exact I.isom k hk a b
  · intro a
    rw [hsymm, ← hl, ← hI a, Over.comp_left]
    congr 1

end GlobalTheory.FlatModel
