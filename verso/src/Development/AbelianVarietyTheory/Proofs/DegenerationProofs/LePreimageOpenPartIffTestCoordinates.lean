import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNeZeroOfLe
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsMaximalComapMaximalIdealOO
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SpanRowsClassZeroEqInvariantStatement
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.TestCrit

/- English proof (translation)
Establish `hn' : b * n.map (algebraMap O K) = 1` using `mul_eq_one_comm.1 hn`. Establish `hb : ∀ i i', ∑ j, b i j * algebraMap O K (n j i') = (1 : Matrix J J K) i i'` using `fun i i' => by`. Rewrite using `[← hn', Matrix.mul_apply]`. Both sides reduce to the same expression. Establish `hsum : ∀ i, ∑ j, φ (A i j) * (n.map φ).mulVec w j = ∑ i', φ ((A * n) i i') * w i'` using `fun i => by`.

Simplify using `only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.map_apply, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul, _root_.mul_assoc]`. Conclude with `Finset.sum_comm`. Establish `hA : ∀ i i', algebraMap O K ((A * n) i i') = ∑ j, algebraMap O K (A i j) * algebraMap O K (n j i')` using `fun i i' => by simp only [Matrix.mul_apply, map_sum, map_mul]`. Simplify using `only [hsum]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨i, hi⟩`. Take `⟨i', -, hi'⟩` from `Finset.exists_ne_zero_of_sum_ne_zero hi`. Use `⟨i', ?_, right_ne_zero_of_mul hi'⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hI`. Establish `h0 : ∀ a ∈ Submodule.span O (b '' I), ∑ j, a j * algebraMap O K (n j i') = 0`.

Introduce `a ha`. Proceed by induction on `ha using Submodule.span_induction with`. Consider the case `mem _ h`. Take `⟨i₀, hi₀, rfl⟩` from `h`. Rewrite using `[hb, Matrix.one_apply_ne]`.

Introduce and unpack `rfl`. Conclude with `hI hi₀`. Consider the case `zero => simp`. Consider the case `add a a' _ _ ha ha' => simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, ha, ha', add_zero]`. Consider the case `smul c a _ ha`.

Simplify using `only [Pi.smul_apply, smul_mul_assoc]`. Rewrite using `[← Finset.smul_sum, ha, smul_zero]`. Establish `h1` using `h0 (fun j => algebraMap O K (A i j)) (hs ▸ Submodule.subset_span ⟨i, rfl⟩)`. Rewrite `h1` using `[← hA, map_eq_zero_iff _ hinj]`. Conclude with `hi' (by rw [h1, map_zero, zero_mul])`.

Introduce and unpack `⟨i, hI, hw⟩`. Assume the negation of the conclusion as `hz`. Use `push_neg at hz`. Establish `hm : b i ∈ Submodule.span O (Set.range fun i j => algebraMap O K (A i j))` using `hs ▸ Submodule.subset_span ⟨i, hI, rfl⟩`. Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun O).1 hm`.

Establish `h1 : ∀ i', (1 : Matrix J J O) i i' = ∑ a, c a * (A * n) a i'` using `fun i' => hinj (by`. Establish `: algebraMap O K ((1 : Matrix J J O) i i') = (1 : Matrix J J K) i i'`. Simplify using `only [Matrix.one_apply, apply_ite (algebraMap O K), map_one, map_zero]`. Establish `hc' : ∀ j, b i j = ∑ a, algebraMap O K (c a) * algebraMap O K (A a j)` using `fun j => by`. Rewrite using `[← hc]`.

Simplify using `only [Finset.sum_apply, Pi.smul_apply]`. Simplify using `only [Algebra.smul_def]`. Rewrite using `[this, ← hb, map_sum]`. Simplify using `only [map_mul, hA, hc', Finset.sum_mul, Finset.mul_sum, _root_.mul_assoc]`. Conclude with `Finset.sum_comm)`.

Apply `hw` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Simplify using `[Matrix.one_apply, apply_ite φ]`. Use `_ = ∑ a, φ (c a) * ∑ i', φ ((A * n) a i') * w i' := by`. Simplify using `only [h1, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum, _root_.mul_assoc]`.

Conclude with `Finset.sum_comm`. Use `_ = 0 := by simp only [hz, mul_zero, Finset.sum_const_zero]`.
-/
theorem exists_ne_zero_iff {O K k J : Type} [CommRing O] [Field K] [Algebra O K] [Field k] [Fintype J]
    [DecidableEq J] (hinj : Function.Injective (algebraMap O K)) (φ : O →+* k) (n A : Matrix J J O)
    (b : Matrix J J K) (hn : n.map (algebraMap O K) * b = 1) (I : Set J)
    (hs : Submodule.span O (b '' I) = Submodule.span O (Set.range fun i j => algebraMap O K (A i j)))
    (w : J → k) :
    (∃ i, ∑ j, φ (A i j) * (n.map φ).mulVec w j ≠ 0) ↔ ∃ i, i ∈ I ∧ w i ≠ 0 := by
  have hn' : b * n.map (algebraMap O K) = 1 := mul_eq_one_comm.1 hn
  have hb : ∀ i i', ∑ j, b i j * algebraMap O K (n j i') = (1 : Matrix J J K) i i' := fun i i' => by
    rw [← hn', Matrix.mul_apply]
    rfl
  have hsum : ∀ i, ∑ j, φ (A i j) * (n.map φ).mulVec w j = ∑ i', φ ((A * n) i i') * w i' := fun i => by
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.map_apply, map_sum, map_mul,
      Finset.mul_sum, Finset.sum_mul, _root_.mul_assoc]
    exact Finset.sum_comm
  have hA : ∀ i i', algebraMap O K ((A * n) i i') = ∑ j, algebraMap O K (A i j) * algebraMap O K (n j i') :=
    fun i i' => by simp only [Matrix.mul_apply, map_sum, map_mul]
  simp only [hsum]
  constructor
  · rintro ⟨i, hi⟩
    obtain ⟨i', -, hi'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hi
    refine ⟨i', ?_, right_ne_zero_of_mul hi'⟩
    by_contra hI
    have h0 : ∀ a ∈ Submodule.span O (b '' I), ∑ j, a j * algebraMap O K (n j i') = 0 := by
      intro a ha
      induction ha using Submodule.span_induction with
      | mem _ h =>
        obtain ⟨i₀, hi₀, rfl⟩ := h
        rw [hb, Matrix.one_apply_ne]
        rintro rfl
        exact hI hi₀
      | zero => simp
      | add a a' _ _ ha ha' => simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, ha, ha', add_zero]
      | smul c a _ ha =>
        simp only [Pi.smul_apply, smul_mul_assoc]
        rw [← Finset.smul_sum, ha, smul_zero]
    have h1 := h0 (fun j => algebraMap O K (A i j)) (hs ▸ Submodule.subset_span ⟨i, rfl⟩)
    rw [← hA, map_eq_zero_iff _ hinj] at h1
    exact hi' (by rw [h1, map_zero, zero_mul])
  · rintro ⟨i, hI, hw⟩
    by_contra hz
    push_neg at hz
    have hm : b i ∈ Submodule.span O (Set.range fun i j => algebraMap O K (A i j)) :=
      hs ▸ Submodule.subset_span ⟨i, hI, rfl⟩
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 hm
    have h1 : ∀ i', (1 : Matrix J J O) i i' = ∑ a, c a * (A * n) a i' := fun i' => hinj (by
      have : algebraMap O K ((1 : Matrix J J O) i i') = (1 : Matrix J J K) i i' := by
        simp only [Matrix.one_apply, apply_ite (algebraMap O K), map_one, map_zero]
      have hc' : ∀ j, b i j = ∑ a, algebraMap O K (c a) * algebraMap O K (A a j) := fun j => by
        rw [← hc]
        simp only [Finset.sum_apply, Pi.smul_apply]
        simp only [Algebra.smul_def]
      rw [this, ← hb, map_sum]
      simp only [map_mul, hA, hc', Finset.sum_mul, Finset.mul_sum, _root_.mul_assoc]
      exact Finset.sum_comm)
    apply hw
    calc w i = ∑ i', φ ((1 : Matrix J J O) i i') * w i' := by
          simp [Matrix.one_apply, apply_ite φ]
      _ = ∑ a, φ (c a) * ∑ i', φ ((A * n) a i') * w i' := by
          simp only [h1, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum, _root_.mul_assoc]
          exact Finset.sum_comm
      _ = 0 := by simp only [hz, mul_zero, Finset.sum_const_zero]

/- English proof (translation)
Introduce `o Ω _ _ _ hA S ρ M U₀ EE hB Q p _ y y₀ t c tm _ x w hx hw`. Use `hA.ft` as an intermediate fact. Take `⟨ψ, hψ⟩ : ∃ ψ : o →+* OO p, y ≫ M.s = spMap ψ` from `⟨(Spec.preimage (y ≫ M.s)).hom, (Spec.map_preimage _).symm⟩`. Establish `hg : (gPt p ≫ y) ≫ M.s = spMap ((OO p).subtype.comp ψ)`. Rewrite using `[Category.assoc, hψ, ← Spec.map_comp]`.

Both sides reduce to the same expression. Establish `hy₀ : ∀ a : o, y₀ (algebraMap o S.R a) = (ψ a : PadicAlgCl p)` using `fun a => (c.at_ _).trans (RatModel.val_algebraMap hg a)`. Establish `hgy : gPt p ≫ y = (spMap (algebraMap (FractionRing t.u.V) (PadicAlgCl p)) ≫ c.yK) ≫ U₀.ι`. Use `(congrArg (gPt p ≫ ·) c.fac.symm).trans ?_` and prove the remaining obligations. Use `beta_reduce`.

Rewrite using `[Category.assoc, c.yK_fac, ← Category.assoc, ← Category.assoc, ← Spec.map_comp]`. Use `congr 1`. Conclude with `Spec.map_comp (CommRingCat.ofHom (algebraMap t.u.V (FractionRing t.u.V))) (CommRingCat.ofHom (algebraMap (FractionRing t.u.V) (PadicAlgCl p)))`. Establish `hU : Set.range (gPt p ≫ y) ⊆ U₀`. Rewrite using `[hgy]`.

Introduce and unpack `_ ⟨a, rfl⟩`. Conclude with `((spMap (algebraMap (FractionRing t.u.V) (PadicAlgCl p)) ≫ c.yK) a).2`. Establish `hcen : M.Cen U₀ (y (cPt p)) y` using `⟨rfl, hU⟩`. Establish `hcl` using `GlobalTheory.ZH.isClosed_centre o Ω M U₀ _ p y hcen`. Take `⟨hker, -, hspan⟩` from `GlobalTheory.T.span_rows_classZero_eq_invariant o Ω S ρ p y₀ t fun a => by`.

Rewrite using `[hy₀]`. Conclude with `(mem_OO_iff _).1 (ψ a).2`. Establish `hT : S.TT M (y (cPt p)) = S.perp t.l.yy.ker`. Rewrite using `[ThetaSys.TT, hB.atTest _ p y y₀ t.τ hcen c.at_, hker]`. Establish `hW : ⊤ ≤ y ⁻¹ᵁ Q.W tm.l` using `(CrdCalc.top_le_iff y _).2 tm.mem`.

Establish `hrange : Set.range ((x ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι) ≫ Q.P.hom) = {y (cPt p)}`. Rewrite using `[Category.assoc, hx, RatModel.range_eq_singleton _ (IsLocalRing.closedPoint _)]`. Use `congr 1`. Conclude with `congrArg y (IsLocalRing.comap_closedPoint (IsLocalRing.residue (OO p)))`. Establish `hs : (x ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι) ≫ Q.P.hom ≫ M.s = spMap ((IsLocalRing.residue (OO p)).comp ψ)`.

Rewrite using `[← Category.assoc, Category.assoc x, hx, Category.assoc, hψ, ← Spec.map_comp]`. Both sides reduce to the same expression. Establish `hcrd` using `Q.rel tm.l _ x _ hw`. Rewrite using `[OpenPart.le_preimage_G_iff o Ω S ρ M U₀ EE hB Q _ _ _ _ _ hrange (Or.inl hcl) hs hcrd, hT, hx, Matrix.mulVec_mulVec]`. Use `set C : Matrix S.J S.J (OO p) := (Q.c tm.l).map (valR y (Q.W tm.l)) with hC`.

Establish `hn : (Q.c tm.l).map (valR (rPt p ≫ y) (Q.W tm.l)) * (tm.m.map fun a => IsLocalRing.residue (OO p) (t.u.j a)) = (C * tm.m.map t.u.j).map (IsLocalRing.residue (OO p))`. Rewrite using `[Matrix.map_mul]`. Use `congr 1`. Use extensionality with `i j`. Conclude with `(CrdCalc.valR_spMap _ y _ hW).2 _`.

Rewrite using `[hn]`. Take `⟨hWg, hvg⟩` from `CrdCalc.valR_spMap (OO p).subtype y _ hW`. Establish `hWg' : Set.range (gPt p ≫ y) ⊆ Q.W tm.l` using `(top_le_preimage_iff _ _).1 hWg`. Use `set ξ := (gPt p ≫ y) (IsLocalRing.closedPoint _) with hξ`. Establish `hr : Set.range (gPt p ≫ y) = {ξ}` using `RatModel.range_eq_singleton _ _`.

Establish `hξW : ξ ∈ Q.W tm.l` using `hWg' ⟨_, rfl⟩`. Establish `hξU : ξ ∈ U₀` using `hU ⟨_, rfl⟩`. Establish `hBm : ∀ i j, Q.B tm.l i j ∈ M.O ξ` using `fun i => by`. Establish `h1 : Q.B tm.l i ∈ EE.E ξ`. Rewrite using `[Q.basis _ _ hξW]`.

Conclude with `Submodule.subset_span ⟨i, rfl⟩`. Rewrite `h1` using `[hB.ee.1 ξ hξU]`. Conclude with `(RatModel.Lat.mem_const_iff M).1 h1`. Establish `hinv : C.map (algebraMap (OO p) (PadicAlgCl p)) * (Q.B tm.l).map (M.val (gPt p ≫ y)) = 1`. Set `c' : Matrix S.J S.J (M.O ξ)` to `fun i j => ⟨_, RatModel.valF_mem_O hξW (Q.c tm.l i j)⟩`.

Set `B' : Matrix S.J S.J (M.O ξ)` to `fun i j => ⟨_, hBm i j⟩`. Establish `h1 : c' * B' = 1`. Apply `Matrix.map_injective (f := (M.O ξ).val.toRingHom) Subtype.val_injective` to reduce the goal to its premises. Use `beta_reduce`. Rewrite using `[Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]`.

Conclude with `Q.c_inv tm.l`. Establish `h2` using `congrArg (fun N => N.map (RatModel.valHom _ _ hr)) h1`. Use `beta_reduce at h2`. Rewrite `h2` using `[Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]`. Rewrite using `[← h2]`.

Use `congr 1`. Use extensionality with `i j`. Conclude with `((RatModel.val_valF hWg' _).trans (hvg _)).symm`. Use `exists_ne_zero_iff Subtype.val_injective (IsLocalRing.residue (OO p)) _ (fun i j => ψ (S.proj (S.perp t.l.yy.ker) 0 j i)) (t.b.map (algebraMap _ (PadicAlgCl p))) ?_ {i | t.cls i = 0} ?_ w` and prove the remaining obligations. Rewrite using `[Matrix.map_mul, Matrix.mul_assoc, ← hinv, tm.m_eq]`.

Both sides reduce to the same expression. Rewrite using `[hspan]`. Simplify using `only [hy₀]`. Both sides reduce to the same expression.
-/
theorem le_preimage_G_iff_test : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (t : ρ.GeoTest p y₀) (c : Q.Fac y t.u) (tm : Q.TMap t c), S.Big → ∀ (x : Sp (kb p) ⟶ (Q.P.hom ⁻¹ᵁ Q.W tm.l).toScheme) (w : S.J → kb p), x ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι ≫ Q.P.hom = rPt p ≫ y → Crd (Q.O1.pull (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι) (Q.σ tm.l) x ((tm.m.map fun a => IsLocalRing.residue (OO p) (t.u.j a)).mulVec w) → (⊤ ≤ (x ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι) ⁻¹ᵁ Q.G ↔ ∃ i, t.cls i = 0 ∧ w i ≠ 0) := by
  intro o Ω _ _ _ hA S ρ M U₀ EE hB Q p _ y y₀ t c tm _ x w hx hw
  have := hA.ft
  obtain ⟨ψ, hψ⟩ : ∃ ψ : o →+* OO p, y ≫ M.s = spMap ψ :=
    ⟨(Spec.preimage (y ≫ M.s)).hom, (Spec.map_preimage _).symm⟩
  have hg : (gPt p ≫ y) ≫ M.s = spMap ((OO p).subtype.comp ψ) := by
    rw [Category.assoc, hψ, ← Spec.map_comp]
    rfl
  have hy₀ : ∀ a : o, y₀ (algebraMap o S.R a) = (ψ a : PadicAlgCl p) := fun a =>
    (c.at_ _).trans (RatModel.val_algebraMap hg a)
  have hgy : gPt p ≫ y = (spMap (algebraMap (FractionRing t.u.V) (PadicAlgCl p)) ≫ c.yK) ≫ U₀.ι := by
    refine (congrArg (gPt p ≫ ·) c.fac.symm).trans ?_
    beta_reduce
    rw [Category.assoc, c.yK_fac, ← Category.assoc, ← Category.assoc, ← Spec.map_comp]
    congr 1
    exact Spec.map_comp (CommRingCat.ofHom (algebraMap t.u.V (FractionRing t.u.V)))
      (CommRingCat.ofHom (algebraMap (FractionRing t.u.V) (PadicAlgCl p)))
  have hU : Set.range (gPt p ≫ y) ⊆ U₀ := by
    rw [hgy]
    rintro _ ⟨a, rfl⟩
    exact ((spMap (algebraMap (FractionRing t.u.V) (PadicAlgCl p)) ≫ c.yK) a).2
  have hcen : M.Cen U₀ (y (cPt p)) y := ⟨rfl, hU⟩
  have hcl := GlobalTheory.ZH.isClosed_centre o Ω M U₀ _ p y hcen
  obtain ⟨hker, -, hspan⟩ := GlobalTheory.T.span_rows_classZero_eq_invariant o Ω S ρ p y₀ t fun a => by
    rw [hy₀]
    exact (mem_OO_iff _).1 (ψ a).2
  have hT : S.TT M (y (cPt p)) = S.perp t.l.yy.ker := by
    rw [ThetaSys.TT, hB.atTest _ p y y₀ t.τ hcen c.at_, hker]
  have hW : ⊤ ≤ y ⁻¹ᵁ Q.W tm.l := (CrdCalc.top_le_iff y _).2 tm.mem
  have hrange : Set.range ((x ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι) ≫ Q.P.hom) = {y (cPt p)} := by
    rw [Category.assoc, hx, RatModel.range_eq_singleton _ (IsLocalRing.closedPoint _)]
    congr 1
    exact congrArg y (IsLocalRing.comap_closedPoint (IsLocalRing.residue (OO p)))
  have hs : (x ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι) ≫ Q.P.hom ≫ M.s =
      spMap ((IsLocalRing.residue (OO p)).comp ψ) := by
    rw [← Category.assoc, Category.assoc x, hx, Category.assoc, hψ, ← Spec.map_comp]
    rfl
  have hcrd := Q.rel tm.l _ x _ hw
  rw [OpenPart.le_preimage_G_iff o Ω S ρ M U₀ EE hB Q _ _ _ _ _ hrange (Or.inl hcl) hs hcrd, hT, hx,
    Matrix.mulVec_mulVec]
  set C : Matrix S.J S.J (OO p) := (Q.c tm.l).map (valR y (Q.W tm.l)) with hC
  have hn : (Q.c tm.l).map (valR (rPt p ≫ y) (Q.W tm.l)) *
      (tm.m.map fun a => IsLocalRing.residue (OO p) (t.u.j a)) =
      (C * tm.m.map t.u.j).map (IsLocalRing.residue (OO p)) := by
    rw [Matrix.map_mul]
    congr 1
    ext i j
    exact (CrdCalc.valR_spMap _ y _ hW).2 _
  rw [hn]
  obtain ⟨hWg, hvg⟩ := CrdCalc.valR_spMap (OO p).subtype y _ hW
  have hWg' : Set.range (gPt p ≫ y) ⊆ Q.W tm.l := (top_le_preimage_iff _ _).1 hWg
  set ξ := (gPt p ≫ y) (IsLocalRing.closedPoint _) with hξ
  have hr : Set.range (gPt p ≫ y) = {ξ} := RatModel.range_eq_singleton _ _
  have hξW : ξ ∈ Q.W tm.l := hWg' ⟨_, rfl⟩
  have hξU : ξ ∈ U₀ := hU ⟨_, rfl⟩
  have hBm : ∀ i j, Q.B tm.l i j ∈ M.O ξ := fun i => by
    have h1 : Q.B tm.l i ∈ EE.E ξ := by
      rw [Q.basis _ _ hξW]
      exact Submodule.subset_span ⟨i, rfl⟩
    rw [hB.ee.1 ξ hξU] at h1
    exact (RatModel.Lat.mem_const_iff M).1 h1
  have hinv : C.map (algebraMap (OO p) (PadicAlgCl p)) * (Q.B tm.l).map (M.val (gPt p ≫ y)) = 1 := by
    let c' : Matrix S.J S.J (M.O ξ) := fun i j => ⟨_, RatModel.valF_mem_O hξW (Q.c tm.l i j)⟩
    let B' : Matrix S.J S.J (M.O ξ) := fun i j => ⟨_, hBm i j⟩
    have h1 : c' * B' = 1 := by
      apply Matrix.map_injective (f := (M.O ξ).val.toRingHom) Subtype.val_injective
      beta_reduce
      rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
      exact Q.c_inv tm.l
    have h2 := congrArg (fun N => N.map (RatModel.valHom _ _ hr)) h1
    beta_reduce at h2
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h2
    rw [← h2]
    congr 1
    ext i j
    exact ((RatModel.val_valF hWg' _).trans (hvg _)).symm
  refine exists_ne_zero_iff Subtype.val_injective (IsLocalRing.residue (OO p)) _
    (fun i j => ψ (S.proj (S.perp t.l.yy.ker) 0 j i)) (t.b.map (algebraMap _ (PadicAlgCl p))) ?_
    {i | t.cls i = 0} ?_ w
  · rw [Matrix.map_mul, Matrix.mul_assoc, ← hinv, tm.m_eq]
    rfl
  · rw [hspan]
    simp only [hy₀]
    rfl

end GlobalTheory.ZH.TestCrit
