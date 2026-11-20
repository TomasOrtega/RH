import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactZeroSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoToBidualOfLocalFrames
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

open GlobalTheory.PDiv

namespace GlobalTheory.SqZeroPt

/- English proof (translation)
Introduce `p O _ G A _ t hlin hpt v hv h n w`. Use `haveI : IsCentralScalar O (ModPow p O n) := ⟨fun r m => by`. Take `⟨x, rfl⟩` from `Ideal.Quotient.mk_surjective m`. Express the relevant statement in the definitionally equal form `(Submodule.Quotient.mk (MulOpposite.op r • x) : ModPow p O n) = Submodule.Quotient.mk (r • x)`. Rewrite using `[op_smul_eq_smul]⟩`.

Set `mk : O →ₗ[O] ModPow p O n` to `(Ideal.Quotient.mkₐ O _).toLinearMap`. Set `v' : TM O (ModPow p O n) ⟶ A` to `GlobalTheory.GrpTangent.sqZeroMap mk ≫ v`. Establish `hsq : ∀ l : O →ₗ[O] ModPow p O n, GlobalTheory.GrpTangent.sqZeroMap l = spOver (TrivSqZeroExt.map l)` using `fun _ => rfl`. Establish `hsc : ∀ c : O, GlobalTheory.GrpTangent.epsScale c = spOver (TrivSqZeroExt.map (c • (LinearMap.id : O →ₗ[O] O)))` using `fun _ => rfl`. Establish `hpow : v' ^ p ^ n = 1`.

Establish `h0 : mk ∘ₗ (((p ^ n : ℕ) : O) • (LinearMap.id : O →ₗ[O] O)) = mk ∘ₗ ((0 : O) • (LinearMap.id : O →ₗ[O] O))`. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Establish `hz : mk ((p ^ n : ℕ) : O) = 0`. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk (Ideal.span {(p : O) ^ n}) ((p ^ n : ℕ) : O) = 0`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem, Nat.cast_pow]`.

Conclude with `Ideal.mem_span_singleton_self _`. Express the relevant statement in the definitionally equal form `mk (((p ^ n : ℕ) : O) • x) = mk ((0 : O) • x)`. Rewrite using `[zero_smul, map_zero, smul_eq_mul, mul_comm, ← smul_eq_mul, map_smul, hz, smul_zero]`. Establish `e1 : GlobalTheory.GrpTangent.sqZeroMap mk ≫ GlobalTheory.GrpTangent.epsScale ((p ^ n : ℕ) : O) = GlobalTheory.GrpTangent.sqZeroMap mk ≫ GlobalTheory.GrpTangent.epsScale 0`. Rewrite using `[hsq, hsc, hsc, spOver_comp, spOver_comp, ← TrivSqZeroExt.map_comp_map, ← TrivSqZeroExt.map_comp_map, h0]`.

Express the relevant statement in the definitionally equal form `(GlobalTheory.GrpTangent.sqZeroMap mk ≫ v) ^ p ^ n = 1`. Rewrite using `[← MonObj.comp_pow, GlobalTheory.GrpTangent.pow_eq_epsScale_comp hv, ← Category.assoc, e1, Category.assoc, GlobalTheory.GrpTangent.epsScale_zero_comp hv, MonObj.comp_one]`. Take `⟨φ, hφv⟩` from `t.surj n (TrivSqZeroExt O (ModPow p O n)) v' hpow`. Establish `hone : spOver (TrivSqZeroExt.fstHom O O O) ≫ v = 1`. Establish `h2` using `congrArg Over.Hom.left h`.

Simplify using `only [Over.comp_left] at h2`. Use `ext1`. Simplify using `only [Over.comp_left]`. Express the relevant statement in the definitionally equal form `(zeroSec O O).left ≫ v.left = _`. Rewrite using `[h2]`.

Establish `hu : (toUnit (Over.mk (spMap (algebraMap O O)))).left = 𝟙 (Sp O)`. Rewrite using `[Over.toUnit_left]`. Conclude with `Spec.map_id _`. Express the relevant statement in the definitionally equal form `_ = (toUnit (Over.mk (spMap (algebraMap O O)))).left ≫ η[A].left`. Use `erw [hu]`.

Conclude with `(Category.id_comp _).symm`. Establish `hφ : (TrivSqZeroExt.fstHom O O (ModPow p O n)).comp φ = Bialgebra.counitAlgHom O (G.A n)`. Establish `e : (TrivSqZeroExt.fstHom O O (ModPow p O n)).comp (TrivSqZeroExt.map mk) = TrivSqZeroExt.fstHom O O O` using `by ext; simp`. Establish `h1 : spOver ((TrivSqZeroExt.fstHom O O (ModPow p O n)).comp φ) ≫ t.y n = 1`. Rewrite using `[← spOver_comp, Category.assoc, hφv]`.

Express the relevant statement in the definitionally equal form `spOver _ ≫ GlobalTheory.GrpTangent.sqZeroMap mk ≫ v = 1`. Rewrite using `[hsq, ← Category.assoc, spOver_comp, e, hone]`. Conclude with `AlgHom.ext fun a => ((t.eq_one_iff n _).1 h1 a).trans (by simp)`. Set `q` to `Ideal.Quotient.mk (Ideal.span {(p : O) ^ n})`. Apply the tactic sequence `let κ : TrivSqZeroExt O (ModPow p O n) →ₐ[O] DualNumber (ModPow p O n) := { toFun := fun z => TrivSqZeroExt.inl (q z.fst) + TrivSqZeroExt.inr z.snd map_one' := by ext <;> simp map_mul' := fun x y => by`.

Use `ext`. Simplify using the standard rewrite rules. Simplify using `only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr]`. Simplify using `[Algebra.smul_def, q, mul_comm]`. Apply the tactic sequence `map_zero' := by ext <;> simp`.

Apply the tactic sequence `map_add' := fun x y => by ext <;> simp [q]`. Apply the tactic sequence `commutes' := fun r => by ext <;> simp [q, TrivSqZeroExt.algebraMap_eq_inl', Ideal.Quotient.algebraMap_eq] }`. Establish `key : κ.comp (TrivSqZeroExt.map mk) = epsTo O (ModPow p O n)`. Apply the tactic sequence `ext <;> simp [κ, q, mk]`. Establish `htan : t.tanPt hv n = κ.comp φ`.

Use `t.inj n _ _ _ ?_` and prove the remaining obligations. Rewrite using `[t.tanPt_y hv n, ← spOver_comp, Category.assoc, hφv]`. Express the relevant statement in the definitionally equal form `_ = spOver κ ≫ GlobalTheory.GrpTangent.sqZeroMap mk ≫ v`. Rewrite using `[hsq, ← Category.assoc, spOver_comp, key]`. Establish `hder : t.tanDer hv n = GlobalTheory.AugCot.sqZeroEquiv (Bialgebra.counitAlgHom O (G.A n)) (ModPow p O n) ⟨φ, hφ⟩` using `GlobalTheory.AugCot.hom_ext fun a => by`.

Express the relevant statement in the definitionally equal form `t.tanDer hv n (dUnit O a) = _`. Rewrite using `[t.tanDer_d hv n, GlobalTheory.AugCot.sqZeroEquiv_d, htan]`. Simplify using `[κ]`. Establish `h' : zeroSec O (ModPow p O n) ≫ GlobalTheory.GrpTangent.sqZeroMap mk ≫ v = η[A]` using `by have e := zeroSec_spOver_y t n φ hφ; rw [hφv] at e; exact e`. Establish `hc : ∀ (z z' : TM O (ModPow p O n) ⟶ A) (e : z = z') (hz : zeroSec O (ModPow p O n) ≫ z = η[A]) (hz' : zeroSec O (ModPow p O n) ≫ z' = η[A]), Phi z hz w = Phi z' hz' w`.

Introduce `z z' e hz hz'`. Substitute `e` using the available equality. Both sides reduce to the same expression. Rewrite using `[hder, ← hpt (ModPow p O n) n φ hφ w, hc _ _ hφv _ h']`. Conclude with `hlin O (ModPow p O n) mk v h h' w`.
-/
theorem tanDer_cn : ∀ (p : ℕ) (O : Type) [CommRing O] (G : GlobalTheory.PDivGroup p O) (A : Over (Sp O)) [GrpObj A] (t : G.TorsionTower A), (∀ (M N : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M] [AddCommGroup N] [Module O N] [Module Oᵐᵒᵖ N] [IsCentralScalar O N] (l : M →ₗ[O] N) (z : TM O M ⟶ A) (h : zeroSec O M ≫ z = η[A]) (h' : zeroSec O N ≫ (GlobalTheory.GrpTangent.sqZeroMap l ≫ z) = η[A]) (w : Wmod A), Phi (GlobalTheory.GrpTangent.sqZeroMap l ≫ z) h' w = l (Phi z h w)) → (∀ (M : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M] (n : ℕ) (φ : G.A n →ₐ[O] TrivSqZeroExt O M) (hφ : (TrivSqZeroExt.fstHom O O M).comp φ = Bialgebra.counitAlgHom O (G.A n)) (w : Wmod A), Phi (spOver φ ≫ t.y n) (zeroSec_spOver_y t n φ hφ) w = GlobalTheory.AugCot.sqZeroEquiv (Bialgebra.counitAlgHom O (G.A n)) M ⟨φ, hφ⟩ (cn t n w)) → ∀ (v : epsR O ⟶ A) (hv : IsTangent v) (h : zeroSec O O ≫ v = η[A]) (n : ℕ) (w : Wmod A), t.tanDer hv n (cn t n w) = Ideal.Quotient.mk _ (Phi v h w) := by
  intro p O _ G A _ t hlin hpt v hv h n w
  haveI : IsCentralScalar O (ModPow p O n) := ⟨fun r m => by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective m
    change (Submodule.Quotient.mk (MulOpposite.op r • x) : ModPow p O n) =
      Submodule.Quotient.mk (r • x)
    rw [op_smul_eq_smul]⟩
  let mk : O →ₗ[O] ModPow p O n := (Ideal.Quotient.mkₐ O _).toLinearMap
  let v' : TM O (ModPow p O n) ⟶ A := GlobalTheory.GrpTangent.sqZeroMap mk ≫ v
  have hsq : ∀ l : O →ₗ[O] ModPow p O n,
      GlobalTheory.GrpTangent.sqZeroMap l = spOver (TrivSqZeroExt.map l) := fun _ => rfl
  have hsc : ∀ c : O, GlobalTheory.GrpTangent.epsScale c =
      spOver (TrivSqZeroExt.map (c • (LinearMap.id : O →ₗ[O] O))) := fun _ => rfl
  have hpow : v' ^ p ^ n = 1 := by
    have h0 : mk ∘ₗ (((p ^ n : ℕ) : O) • (LinearMap.id : O →ₗ[O] O)) =
        mk ∘ₗ ((0 : O) • (LinearMap.id : O →ₗ[O] O)) := by
      refine LinearMap.ext fun x => ?_
      have hz : mk ((p ^ n : ℕ) : O) = 0 := by
        change Ideal.Quotient.mk (Ideal.span {(p : O) ^ n}) ((p ^ n : ℕ) : O) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem, Nat.cast_pow]
        exact Ideal.mem_span_singleton_self _
      change mk (((p ^ n : ℕ) : O) • x) = mk ((0 : O) • x)
      rw [zero_smul, map_zero, smul_eq_mul, mul_comm, ← smul_eq_mul, map_smul, hz, smul_zero]
    have e1 : GlobalTheory.GrpTangent.sqZeroMap mk ≫ GlobalTheory.GrpTangent.epsScale ((p ^ n : ℕ) : O) =
        GlobalTheory.GrpTangent.sqZeroMap mk ≫ GlobalTheory.GrpTangent.epsScale 0 := by
      rw [hsq, hsc, hsc, spOver_comp, spOver_comp, ← TrivSqZeroExt.map_comp_map,
        ← TrivSqZeroExt.map_comp_map, h0]
    change (GlobalTheory.GrpTangent.sqZeroMap mk ≫ v) ^ p ^ n = 1
    rw [← MonObj.comp_pow, GlobalTheory.GrpTangent.pow_eq_epsScale_comp hv, ← Category.assoc, e1,
      Category.assoc, GlobalTheory.GrpTangent.epsScale_zero_comp hv, MonObj.comp_one]
  obtain ⟨φ, hφv⟩ := t.surj n (TrivSqZeroExt O (ModPow p O n)) v' hpow
  have hone : spOver (TrivSqZeroExt.fstHom O O O) ≫ v = 1 := by
    have h2 := congrArg Over.Hom.left h
    simp only [Over.comp_left] at h2
    ext1
    simp only [Over.comp_left]
    change (zeroSec O O).left ≫ v.left = _
    rw [h2]
    have hu : (toUnit (Over.mk (spMap (algebraMap O O)))).left = 𝟙 (Sp O) := by
      rw [Over.toUnit_left]; exact Spec.map_id _
    change _ = (toUnit (Over.mk (spMap (algebraMap O O)))).left ≫ η[A].left
    erw [hu]
    exact (Category.id_comp _).symm
  have hφ : (TrivSqZeroExt.fstHom O O (ModPow p O n)).comp φ =
      Bialgebra.counitAlgHom O (G.A n) := by
    have e : (TrivSqZeroExt.fstHom O O (ModPow p O n)).comp (TrivSqZeroExt.map mk) =
        TrivSqZeroExt.fstHom O O O := by
      ext; simp
    have h1 : spOver ((TrivSqZeroExt.fstHom O O (ModPow p O n)).comp φ) ≫ t.y n = 1 := by
      rw [← spOver_comp, Category.assoc, hφv]
      change spOver _ ≫ GlobalTheory.GrpTangent.sqZeroMap mk ≫ v = 1
      rw [hsq, ← Category.assoc, spOver_comp, e, hone]
    exact AlgHom.ext fun a => ((t.eq_one_iff n _).1 h1 a).trans (by simp)
  let q := Ideal.Quotient.mk (Ideal.span {(p : O) ^ n})
  let κ : TrivSqZeroExt O (ModPow p O n) →ₐ[O] DualNumber (ModPow p O n) :=
    { toFun := fun z => TrivSqZeroExt.inl (q z.fst) + TrivSqZeroExt.inr z.snd
      map_one' := by ext <;> simp
      map_mul' := fun x y => by
        ext
        · simp
        · simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr]
          simp [Algebra.smul_def, q, mul_comm]
      map_zero' := by ext <;> simp
      map_add' := fun x y => by ext <;> simp [q]
      commutes' := fun r => by ext <;> simp [q, TrivSqZeroExt.algebraMap_eq_inl', Ideal.Quotient.algebraMap_eq] }
  have key : κ.comp (TrivSqZeroExt.map mk) = epsTo O (ModPow p O n) := by
    ext <;> simp [κ, q, mk]
  have htan : t.tanPt hv n = κ.comp φ := by
    refine t.inj n _ _ _ ?_
    rw [t.tanPt_y hv n, ← spOver_comp, Category.assoc, hφv]
    change _ = spOver κ ≫ GlobalTheory.GrpTangent.sqZeroMap mk ≫ v
    rw [hsq, ← Category.assoc, spOver_comp, key]
  have hder : t.tanDer hv n =
      GlobalTheory.AugCot.sqZeroEquiv (Bialgebra.counitAlgHom O (G.A n)) (ModPow p O n) ⟨φ, hφ⟩ :=
    GlobalTheory.AugCot.hom_ext fun a => by
      change t.tanDer hv n (dUnit O a) = _
      rw [t.tanDer_d hv n, GlobalTheory.AugCot.sqZeroEquiv_d, htan]
      simp [κ]
  have h' : zeroSec O (ModPow p O n) ≫ GlobalTheory.GrpTangent.sqZeroMap mk ≫ v = η[A] :=
    by have e := zeroSec_spOver_y t n φ hφ; rw [hφv] at e; exact e
  have hc : ∀ (z z' : TM O (ModPow p O n) ⟶ A) (e : z = z') (hz : zeroSec O (ModPow p O n) ≫ z = η[A])
      (hz' : zeroSec O (ModPow p O n) ≫ z' = η[A]), Phi z hz w = Phi z' hz' w := by
    intro z z' e hz hz'; subst e; rfl
  rw [hder, ← hpt (ModPow p O n) n φ hφ w, hc _ _ hφv _ h']
  exact hlin O (ModPow p O n) mk v h h' w

end GlobalTheory.SqZeroPt
