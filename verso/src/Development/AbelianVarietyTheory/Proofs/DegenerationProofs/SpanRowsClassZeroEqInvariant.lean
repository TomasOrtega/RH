import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAdaptedBasisTestLattice

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.WeightZero

/- English proof (translation)
Assume the negation of the conclusion as `h0`. Establish `h1 : {x | ¬ 0 < q x}.Finite` using `Filter.eventually_cofinite.1 (hq.eventually_gt_atTop 0)`. Use `Set.infinite_of_injective_forall_mem (f := fun n : ℤ => n • α) (smul_left_injective ℤ h0) (fun n => ?_) h1` and prove the remaining obligations. Rewrite using `[Set.mem_setOf_eq, q.map_smul, not_lt]`. Conclude with `smul_nonpos_of_nonneg_of_nonpos (mul_self_nonneg n) h`.
-/
theorem eq_zero_of_q_nonpos {X : Type} [AddCommGroup X] [Module.Free ℤ X] (q : QuadraticMap ℤ X ℝ)
    (hq : Filter.Tendsto q Filter.cofinite Filter.atTop) {α : X} (h : q α ≤ 0) : α = 0 := by
  by_contra h0
  have h1 : {x | ¬ 0 < q x}.Finite := Filter.eventually_cofinite.1 (hq.eventually_gt_atTop 0)
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℤ => n • α) (smul_left_injective ℤ h0)
    (fun n => ?_) h1
  rw [Set.mem_setOf_eq, q.map_smul, not_lt]
  exact smul_nonpos_of_nonneg_of_nonpos (mul_self_nonneg n) h

/- English proof (translation)
Substitute `h` using the available equality. Rewrite using `[show c = c' from AddMonoidHom.ext fun t => hc t.1 t.2 t.2]`.
-/
theorem proj_congr {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω)
    {T T' : AddSubgroup S.Gam} (h : T = T') (c : T →+ ZMod S.N) (c' : T' →+ ZMod S.N)
    (hc : ∀ t ht ht', c ⟨t, ht⟩ = c' ⟨t, ht'⟩) : S.proj T c = S.proj T' c' := by
  subst h
  rw [show c = c' from AddMonoidHom.ext fun t => hc t.1 t.2 t.2]

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[AddMonoidHom.nsmul_apply]`. Simplify using the standard rewrite rules.
-/
theorem nsmul_char {T : Type} [AddCommGroup T] (N : ℕ) (c : T →+ ZMod N) : N • c = 0 := by
  ext x
  rw [AddMonoidHom.nsmul_apply]
  simp

/- English proof (translation)
Rewrite using `[map_add, map_nsmul, nsmul_char, add_zero]`.
-/
theorem map_add_nsmul {X T : Type} [AddCommGroup X] [AddCommGroup T] (N : ℕ) (w : X →+ (T →+ ZMod N)) (β m : X) :
    w (β + N • m) = w β := by
  rw [map_add, map_nsmul, nsmul_char, add_zero]

/- English proof (translation)
Establish `: IsDomain o` using `hA.inj.isDomain`. Use `FreeNear.finite_char S (S.perp τ.yy.ker)` as an intermediate fact. Use `Fintype.ofFinite (S.perp τ.yy.ker →+ ZMod S.N)` as an intermediate fact. Take `⟨hmul, -⟩` from `FreeNear.proj_orthogonal S _ τ.isoFree`. Establish `hz : ∀ α, (∀ v, τ.q α ≤ τ.q (α + S.N • v)) → 0 = τ.wt α → α = 0` using `fun α hα h => by`.

Establish `h3` using `TestBasis.q_le_of_wt_eq τ hα (β := 0) (by rw [map_zero, h])`. Rewrite `h3` using `[map_zero]`. Conclude with `eq_zero_of_q_nonpos _ τ.pos h3`. Set `φ : o →+* PadicAlgCl p` to `y₀.comp (algebraMap o S.R)`. Take `⟨Q, hQd⟩ : ∃ Q : (S.perp τ.yy.ker →+ ZMod S.N) → Matrix S.J S.J (PadicAlgCl p), ∀ c j i, y₀ (algebraMap o S.R (S.proj _ c j i)) = Q c j i` from `⟨fun c => (S.proj _ c).map φ, fun _ _ _ => rfl⟩`.

Establish `hQe : ∀ c, Q c = φ.mapMatrix (S.proj _ c)` using `fun c => Matrix.ext fun j i => (hQd c j i).symm`. Establish `hQ : ∀ c, Q 0 * Q c = if 0 = c then Q 0 else 0` using `fun c => by`. Rewrite using `[hQe, hQe, ← map_mul, hmul]`. Use `split_ifs`. Both sides reduce to the same expression.

Conclude with `map_zero _`. Take `⟨L, hL⟩ : ∃ L : (S.J → PadicAlgCl p) →ₗ[OO p] (S.J → PadicAlgCl p), ∀ v, L v = (Q 0).mulVec v` from `⟨(Q 0).mulVecLin.restrictScalars (OO p), fun _ => rfl⟩`. Establish `hcol : ∀ c i, L (fun j => Q c j i) = fun j => (Q 0 * Q c) j i` using `fun c i => hL _`. Establish `hb' : ∀ i, (Q (τ.wt (a i))).mulVec (b i) = b i` using `fun i => by`. Rewrite using `[hQe]`.

Conclude with `hb i`. Simplify using `only [hQd]`. Establish `h1 : τ.E.map L ≤ Submodule.span (OO p) (Set.range fun i j => Q 0 j i)`. Rewrite using `[ThetaSys.Test.E, Submodule.map_span, Submodule.span_le]`. Introduce and unpack `_ ⟨_, ⟨α, l, i, hα, hl, rfl⟩, rfl⟩`.

Simplify using `only [hQd]`. Establish `h2 : L (fun j => l * Q (τ.wt α) j i) = l • fun j => (Q 0 * Q (τ.wt α)) j i`. Rewrite using `[← hcol, hL, hL, ← Matrix.mulVec_smul]`. Both sides reduce to the same expression. Rewrite using `[h2, hQ]`.

Use `split_ifs with h`. Rewrite `hl` using `[hz α hα h, map_zero, zero_div, Real.exp_zero]`. Conclude with `Submodule.smul_mem _ (⟨l, (mem_OO_iff _).2 hl⟩ : OO p) (Submodule.subset_span ⟨i, rfl⟩)`. Rewrite using `[show (fun j => (0 : Matrix S.J S.J (PadicAlgCl p)) j i) = 0 from rfl, smul_zero]`. Conclude with `Submodule.zero_mem _`.

Establish `h2 : τ.E.map L ≤ Submodule.span (OO p) (b '' {i | a i = 0})`. Rewrite using `[hE, Submodule.map_span, Submodule.span_le]`. Introduce and unpack `_ ⟨_, ⟨i, rfl⟩, rfl⟩`. Distinguish the cases in `h : 0 = τ.wt (a i)`. Rewrite using `[hL, h, hb']`.

Conclude with `Submodule.subset_span ⟨i, hz _ (ha i) h, rfl⟩`. Rewrite using `[hL, ← hb', Matrix.mulVec_mulVec, hQ, if_neg h, Matrix.zero_mulVec]`. Conclude with `Submodule.zero_mem _`. Use `le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨i, hi, rfl⟩`.

Use `h1 ⟨b i, hE ▸ Submodule.subset_span ⟨i, rfl⟩, ?_⟩` and prove the remaining obligations. Use `hb' i` as an intermediate fact. Rewrite `this` using `[show a i = 0 from hi, map_zero]`. Rewrite using `[hL, this]`. Introduce and unpack `_ ⟨i, rfl⟩`.

Use `h2 ⟨fun j => Q 0 j i, Submodule.subset_span ⟨0, 1, i, fun v => ?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[map_zero] by_contra! h`. Rewrite `h` using `[eq_zero_of_q_nonpos _ τ.pos h.le, map_zero]`. Conclude with `lt_irrefl _ h`. Simplify using the standard rewrite rules.

Use function extensionality and compare the values at `j`. Rewrite using `[map_zero, _root_.one_mul, hQd]`. Rewrite using `[hcol, hQ, if_pos rfl]`.
-/
theorem span_eq_of_test {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [hA : ArithBase o Ω] {S : ThetaSys o Ω}
    {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (τ : S.Test p y₀) (b : S.J → S.J → PadicAlgCl p)
    (a : S.J → τ.X) (ha : ∀ i v, τ.q (a i) ≤ τ.q (a i + S.N • v))
    (hE : τ.E = Submodule.span (OO p) (Set.range b))
    (hb : ∀ i, ((S.proj _ (τ.wt (a i))).map fun x => y₀ (algebraMap o S.R x)).mulVec (b i) = b i) :
    Submodule.span (OO p) (b '' {i | a i = 0}) =
      Submodule.span (OO p) (Set.range fun i j => y₀ (algebraMap o S.R (S.proj (S.perp τ.yy.ker) 0 j i))) := by
  have : IsDomain o := hA.inj.isDomain
  have := FreeNear.finite_char S (S.perp τ.yy.ker)
  have := Fintype.ofFinite (S.perp τ.yy.ker →+ ZMod S.N)
  obtain ⟨hmul, -⟩ := FreeNear.proj_orthogonal S _ τ.isoFree
  have hz : ∀ α, (∀ v, τ.q α ≤ τ.q (α + S.N • v)) → 0 = τ.wt α → α = 0 := fun α hα h => by
    have h3 := TestBasis.q_le_of_wt_eq τ hα (β := 0) (by rw [map_zero, h])
    rw [map_zero] at h3
    exact eq_zero_of_q_nonpos _ τ.pos h3
  let φ : o →+* PadicAlgCl p := y₀.comp (algebraMap o S.R)
  obtain ⟨Q, hQd⟩ : ∃ Q : (S.perp τ.yy.ker →+ ZMod S.N) → Matrix S.J S.J (PadicAlgCl p),
    ∀ c j i, y₀ (algebraMap o S.R (S.proj _ c j i)) = Q c j i := ⟨fun c => (S.proj _ c).map φ, fun _ _ _ => rfl⟩
  have hQe : ∀ c, Q c = φ.mapMatrix (S.proj _ c) := fun c => Matrix.ext fun j i => (hQd c j i).symm
  have hQ : ∀ c, Q 0 * Q c = if 0 = c then Q 0 else 0 := fun c => by
    rw [hQe, hQe, ← map_mul, hmul]
    split_ifs
    · rfl
    · exact map_zero _
  obtain ⟨L, hL⟩ : ∃ L : (S.J → PadicAlgCl p) →ₗ[OO p] (S.J → PadicAlgCl p), ∀ v, L v = (Q 0).mulVec v :=
    ⟨(Q 0).mulVecLin.restrictScalars (OO p), fun _ => rfl⟩
  have hcol : ∀ c i, L (fun j => Q c j i) = fun j => (Q 0 * Q c) j i := fun c i => hL _
  have hb' : ∀ i, (Q (τ.wt (a i))).mulVec (b i) = b i := fun i => by
    rw [hQe]
    exact hb i
  simp only [hQd]
  have h1 : τ.E.map L ≤ Submodule.span (OO p) (Set.range fun i j => Q 0 j i) := by
    rw [ThetaSys.Test.E, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨α, l, i, hα, hl, rfl⟩, rfl⟩
    simp only [hQd]
    have h2 : L (fun j => l * Q (τ.wt α) j i) = l • fun j => (Q 0 * Q (τ.wt α)) j i := by
      rw [← hcol, hL, hL, ← Matrix.mulVec_smul]
      rfl
    rw [h2, hQ]
    split_ifs with h
    · rw [hz α hα h, map_zero, zero_div, Real.exp_zero] at hl
      exact Submodule.smul_mem _ (⟨l, (mem_OO_iff _).2 hl⟩ : OO p) (Submodule.subset_span ⟨i, rfl⟩)
    · rw [show (fun j => (0 : Matrix S.J S.J (PadicAlgCl p)) j i) = 0 from rfl, smul_zero]
      exact Submodule.zero_mem _
  have h2 : τ.E.map L ≤ Submodule.span (OO p) (b '' {i | a i = 0}) := by
    rw [hE, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    by_cases h : 0 = τ.wt (a i)
    · rw [hL, h, hb']
      exact Submodule.subset_span ⟨i, hz _ (ha i) h, rfl⟩
    · rw [hL, ← hb', Matrix.mulVec_mulVec, hQ, if_neg h, Matrix.zero_mulVec]
      exact Submodule.zero_mem _
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨i, hi, rfl⟩
    refine h1 ⟨b i, hE ▸ Submodule.subset_span ⟨i, rfl⟩, ?_⟩
    have := hb' i
    rw [show a i = 0 from hi, map_zero] at this
    rw [hL, this]
  · rintro _ ⟨i, rfl⟩
    refine h2 ⟨fun j => Q 0 j i, Submodule.subset_span ⟨0, 1, i, fun v => ?_, ?_, ?_⟩, ?_⟩
    · rw [map_zero]
      by_contra! h
      rw [eq_zero_of_q_nonpos _ τ.pos h.le, map_zero] at h
      exact lt_irrefl _ h
    · simp
    · funext j
      rw [map_zero, _root_.one_mul, hQd]
    · rw [hcol, hQ, if_pos rfl]

/- English proof (translation)
Establish `h3 : q' (f (f.symm y)) ≤ q' (f (f.symm y + N • f.symm (e v)))` using `h (f.symm (e v))`. Simplify `h3` using `[hq]`.
-/
theorem short_transfer {X Y Z : Type} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z] (e : X ≃+ Y) (f : Z ≃+ Y)
    (q : QuadraticMap ℤ X ℝ) (q' : QuadraticMap ℤ Y ℝ) (hq : ∀ α, q α = q' (e α)) {N : ℕ} {y : Y}
    (h : Short (q'.comp f.toIntLinearEquiv.toLinearMap) N (f.symm y)) (v : X) :
    q (e.symm y) ≤ q (e.symm y + N • v) := by
  have h3 : q' (f (f.symm y)) ≤ q' (f (f.symm y + N • f.symm (e v))) := h (f.symm (e v))
  simpa [hq] using h3

end GlobalTheory.ZH.WeightZero

namespace GlobalTheory.ZH

open WeightZero in

/- English proof (translation)
Introduce `o Ω _ _ _ hA S ρ p _ y₀ t _`. Take `⟨e, hq, hy⟩` from `t.mt`. Establish `hker : t.τ.yy.ker = t.l.yy.ker`. Use extensionality with `a`. Use `hy a 0` as an intermediate fact.

Rewrite `this` using `[map_zero]`. Conclude with `this`. Establish `hwt : ∀ α x h h', t.τ.wt α ⟨x, h⟩ = t.l.wt (e α) ⟨x, h'⟩` using `fun α x h h' => by`. Take `⟨a, ha⟩` from `t.τ.yy_onto (QuotientAddGroup.mk α)`. Rewrite using `[t.τ.wt_eq a α ha, t.l.wt_eq a _ ((hy a α).1 ha)]`.

Establish `hz : ∀ α, t.l.wt (e α) = 0 → ∃ v, α = S.N • v` using `fun α h => TestBasis.exists_nsmul_of_wt_eq_zero t.τ α (AddMonoidHom.ext fun x => by`. Rewrite using `[hwt α x.1 x.2 (hker ▸ x.2), h]`. Use the proof step `rfl)`. Establish `hcl : ∀ α β, t.l.wt α = t.l.wt β ↔ ∃ m, α = β + S.N • m` using `fun α β => by`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Take `⟨v, hv⟩` from `hz (e.symm (α - β)) (by rw [e.apply_symm_apply, map_sub, h, sub_self])`. Use `⟨e v, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_nsmul, ← hv, e.apply_symm_apply, add_sub_cancel]`. Introduce and unpack `⟨m, rfl⟩`.

Conclude with `map_add_nsmul _ _ _ _`. Use `⟨hker, hcl, ?_⟩` and prove the remaining obligations. Establish `h1` using `span_eq_of_test t.τ (t.b.map (algebraMap _ (PadicAlgCl p))) (fun i => e.symm (t.cls i)) (fun i => short_transfer e t.mod.xe _ _ hq (t.mod.good.short i)) t.span (fun i => by`. Establish `h3 : S.proj _ (t.τ.wt (e.symm (t.cls i))) = S.proj _ (t.l.wt (t.cls i))` using `proj_congr S (congrArg S.perp hker) _ _ fun x h h' => (hwt _ x h h').trans (by rw [e.apply_symm_apply])`. Rewrite using `[h3]`.

Conclude with `t.wt i)`. Establish `h2 : {i | e.symm (t.cls i) = 0} = {i | t.cls i = 0}` using `Set.ext fun i => e.symm.map_eq_zero_iff`. Establish `h3 : S.proj (S.perp t.τ.yy.ker) 0 = S.proj (S.perp t.l.yy.ker) 0` using `proj_congr S (congrArg S.perp hker) _ _ fun _ _ _ => rfl`. Rewrite `h1` using `[h2, h3]`. Conclude with `h1`.
-/
theorem span_rows_class_zero : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (t : ρ.GeoTest p y₀), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → t.τ.yy.ker = t.l.yy.ker ∧ (∀ α β, t.l.wt α = t.l.wt β ↔ ∃ m, α = β + S.N • m) ∧ Submodule.span (OO p) ((t.b.map (algebraMap _ (PadicAlgCl p))) '' {i | t.cls i = 0}) = Submodule.span (OO p) (Set.range fun i j => y₀ (algebraMap o S.R (S.proj (S.perp t.l.yy.ker) 0 j i))) := by
  intro o Ω _ _ _ hA S ρ p _ y₀ t _
  obtain ⟨e, hq, hy⟩ := t.mt
  have hker : t.τ.yy.ker = t.l.yy.ker := by
    ext a
    have := hy a 0
    rw [map_zero] at this
    exact this
  have hwt : ∀ α x h h', t.τ.wt α ⟨x, h⟩ = t.l.wt (e α) ⟨x, h'⟩ := fun α x h h' => by
    obtain ⟨a, ha⟩ := t.τ.yy_onto (QuotientAddGroup.mk α)
    rw [t.τ.wt_eq a α ha, t.l.wt_eq a _ ((hy a α).1 ha)]
  have hz : ∀ α, t.l.wt (e α) = 0 → ∃ v, α = S.N • v := fun α h =>
    TestBasis.exists_nsmul_of_wt_eq_zero t.τ α (AddMonoidHom.ext fun x => by
      rw [hwt α x.1 x.2 (hker ▸ x.2), h]
      rfl)
  have hcl : ∀ α β, t.l.wt α = t.l.wt β ↔ ∃ m, α = β + S.N • m := fun α β => by
    constructor
    · intro h
      obtain ⟨v, hv⟩ := hz (e.symm (α - β)) (by rw [e.apply_symm_apply, map_sub, h, sub_self])
      refine ⟨e v, ?_⟩
      rw [← map_nsmul, ← hv, e.apply_symm_apply, add_sub_cancel]
    · rintro ⟨m, rfl⟩
      exact map_add_nsmul _ _ _ _
  refine ⟨hker, hcl, ?_⟩
  have h1 := span_eq_of_test t.τ (t.b.map (algebraMap _ (PadicAlgCl p))) (fun i => e.symm (t.cls i))
    (fun i => short_transfer e t.mod.xe _ _ hq (t.mod.good.short i)) t.span
    (fun i => by
      have h3 : S.proj _ (t.τ.wt (e.symm (t.cls i))) = S.proj _ (t.l.wt (t.cls i)) :=
        proj_congr S (congrArg S.perp hker) _ _ fun x h h' =>
          (hwt _ x h h').trans (by rw [e.apply_symm_apply])
      rw [h3]
      exact t.wt i)
  have h2 : {i | e.symm (t.cls i) = 0} = {i | t.cls i = 0} := Set.ext fun i => e.symm.map_eq_zero_iff
  have h3 : S.proj (S.perp t.τ.yy.ker) 0 = S.proj (S.perp t.l.yy.ker) 0 :=
    proj_congr S (congrArg S.perp hker) _ _ fun _ _ _ => rfl
  rw [h2, h3] at h1
  exact h1

end GlobalTheory.ZH
