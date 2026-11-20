import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParIndJacPlacing
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel Matrix
open scoped TensorProduct

namespace GlobalTheory.SmGL.MultiIrr

section Stages

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {s : ℕ} {m : Fin (s + 1) → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  {b n : Type} [Fintype b] [DecidableEq b] [Fintype n] [DecidableEq n]
  {V W U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U]

/- English proof (translation)
Set `π` to `(leviTwo k (m 0) b).symm.toMonoidHom.comp (leviProj k (two e'))`. Set `j` to `((emb₂ k e').comp (MonoidHom.inr _ _)).codRestrict (parab k (two e')) fun _ => leviEmb_mem_parab k _ _`. Establish `hπ2 : ∀ (q : parab k (two e')) (x y : b), ((π q).2).val x y = (q : GL n k).val (e' (.inr x)) (e' (.inr y))` using `fun _ _ _ => rfl`. Establish `hπ1 : ∀ (q : parab k (two e')) (x y : m 0), ((π q).1).val x y = (q : GL n k).val (e' (.inl x)) (e' (.inl y))` using `fun _ _ _ => rfl`. Use `smInd_stages (P' := parab k ψ) (fun g hg => ?_) π j ?_ (fun x => ?_) (fun q => ?_) SplitFlip.isCompact_KO (fun x => ?_) ((deltaHalf k _).comp (leviTwo k _ _).toMonoidHom) ?_ σ₀ _ _ κ (fun q h1' h2 x => ?_) _ fun q x => rfl` and prove the remaining obligations.

Use `(mem_parab_two k).2 fun y x => ?_` and prove the remaining obligations. Take `⟨⟨i, u⟩, rfl⟩` from `ψ.surjective y`. Rewrite using `[h1, h0]`. Conclude with `mem_parab_iff.1 hg i.succ 0 u x (Fin.succ_pos _)`. Conclude with `(continuous_leviEmb k _).comp ((continuous_leviTwo k).comp (Continuous.prodMk_right 1))`.

Conclude with `(leviTwo k _ _).symm_apply_eq.2 (leviProj_leviEmb k _ _)`. Rewrite using `[mem_parab_iff, mem_parab_iff]`. Use `⟨fun hq x y u v hxy => ?_, fun hq x y u v hxy => ?_⟩` and prove the remaining obligations. Rewrite using `[hπ2, h1, h1]`. Conclude with `hq x.succ y.succ u v (Fin.succ_lt_succ_iff.2 hxy)`.

Proceed by induction on `x using Fin.cases with`. Consider the case `zero => exact absurd hxy (Fin.not_lt_zero _)`. Consider the case `succ x`. Proceed by induction on `y using Fin.cases with`. Consider the case `zero`.

Use `(mem_parab_two k).1 q.2 (ψ ⟨x, u⟩) v` as an intermediate fact. Rewrite `this` using `[h1, h0]`. Then use the resulting hypothesis. Consider the case `succ y`. Use `hq x y u v (Fin.succ_lt_succ_iff.1 hxy)` as an intermediate fact. Rewrite `this` using `[hπ2, h1, h1]`. Then use the resulting hypothesis.

Conclude with `exists_parab_mul _ x`. Establish `h1' : IsSmoothChar (((deltaHalf k _).comp (leviTwo k (m 0) b).toMonoidHom).comp (MonoidHom.inr _ _))` using `((isSmoothChar_deltaHalf k).comp _ (continuous_leviTwo k)).comp _ (Continuous.prodMk_right 1) filter_upwards [h1'.mem_nhds (one_mem _)] with u hu`. Conclude with `MonoidHom.mem_ker.1 hu`. Set `g` to `leviProj k e ⟨q, h1'⟩`. Establish `e1 : (π q).1 = g 0` using `Units.ext (Matrix.ext fun x y => by`.

Rewrite using `[hπ1, h0, h0]`. Use the proof step `rfl)`. Establish `e2 : leviProj k _ ⟨(π q).2, h2⟩ = fun i : Fin s => g i.succ` using `funext fun i => Units.ext (Matrix.ext fun x y => by show ((π q).2).val (ψ ⟨i, x⟩) (ψ ⟨i, y⟩) = _`. Rewrite using `[hπ2, h1, h1]`. Use the proof step `rfl)`.

Establish `e3 : GeneralLinearGroup.det (π q).2 = ∏ i : Fin s, GeneralLinearGroup.det (g i.succ)`. Use `det_parab k _ ⟨(π q).2, h2⟩` as an intermediate fact. Rewrite `this` using `[e2]`. Then use the resulting hypothesis. Establish `e4 : deltaHalf k m g = deltaHalf k _ (leviTwo k _ _ (π q)) * deltaHalf k (fun i : Fin s => m i.succ) fun i => g i.succ`. Rewrite using `[deltaHalf_two, deltaHalf_apply, deltaHalf_apply, Fin.prod_univ_succ, e1, e3, map_prod, modExp_zero, mul_assoc, ← Finset.prod_mul_distrib, Fintype.card_congr ψ]`.

Use `congrArg₂ _ (by simp) (Finset.prod_congr rfl fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[modExp_succ, ← MonoidHom.mul_apply, ← absPow_add]`. Use `congr 2`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Use `show (deltaHalf k m g : ℂ) • σ g (κ x) = (deltaHalf k _ (leviTwo k _ _ (π q)) : ℂ) • κ (TensorProduct.map (σ₀ (π q).1) ((deltaHalf k _ (leviProj k _ ⟨(π q).2, h2⟩) : ℂ) • ρ (leviProj k _ ⟨(π q).2, h2⟩)) x)`. Rewrite using `[h, e4, e2, e1, TensorProduct.map_smul_right, LinearMap.smul_apply, map_smul, smul_smul, Units.val_mul]`.
-/
theorem ind₂_parInd_equiv_placed (e : (Σ i, m i) ≃ n) (e' : m 0 ⊕ b ≃ n) (ψ : (Σ i : Fin s, m i.succ) ≃ b)
    (h0 : ∀ x, e' (.inl x) = e ⟨0, x⟩) (h1 : ∀ i x, e' (.inr (ψ ⟨i, x⟩)) = e ⟨i.succ, x⟩)
    (σ₀ : Representation ℂ (GL (m 0) k) V)
    (ρ : Representation ℂ (Levi k fun i : Fin s => m i.succ) W) (σ : Representation ℂ (Levi k m) U)
    (κ : V ⊗[ℂ] W ≃ₗ[ℂ] U)
    (h : ∀ g x, σ g (κ x) = κ (TensorProduct.map (σ₀ (g 0)) (ρ fun i => g i.succ) x)) :
    Nonempty ((ind₂ e' (extTensor σ₀ (parInd ψ ρ))).Equiv (parInd e σ)) := by
  let π := (leviTwo k (m 0) b).symm.toMonoidHom.comp (leviProj k (two e'))
  let j := ((emb₂ k e').comp (MonoidHom.inr _ _)).codRestrict (parab k (two e'))
    fun _ => leviEmb_mem_parab k _ _
  have hπ2 : ∀ (q : parab k (two e')) (x y : b), ((π q).2).val x y = (q : GL n k).val (e' (.inr x)) (e' (.inr y)) :=
    fun _ _ _ => rfl
  have hπ1 : ∀ (q : parab k (two e')) (x y : m 0), ((π q).1).val x y = (q : GL n k).val (e' (.inl x)) (e' (.inl y)) :=
    fun _ _ _ => rfl
  refine smInd_stages (P' := parab k ψ) (fun g hg => ?_) π j ?_
    (fun x => ?_) (fun q => ?_) SplitFlip.isCompact_KO (fun x => ?_)
    ((deltaHalf k _).comp (leviTwo k _ _).toMonoidHom) ?_ σ₀ _ _ κ (fun q h1' h2 x => ?_) _ fun q x => rfl
  · refine (mem_parab_two k).2 fun y x => ?_
    obtain ⟨⟨i, u⟩, rfl⟩ := ψ.surjective y
    rw [h1, h0]
    exact mem_parab_iff.1 hg i.succ 0 u x (Fin.succ_pos _)
  · exact (continuous_leviEmb k _).comp ((continuous_leviTwo k).comp (Continuous.prodMk_right 1))
  · exact (leviTwo k _ _).symm_apply_eq.2 (leviProj_leviEmb k _ _)
  · rw [mem_parab_iff, mem_parab_iff]
    refine ⟨fun hq x y u v hxy => ?_, fun hq x y u v hxy => ?_⟩
    · rw [hπ2, h1, h1]
      exact hq x.succ y.succ u v (Fin.succ_lt_succ_iff.2 hxy)
    · induction x using Fin.cases with
      | zero => exact absurd hxy (Fin.not_lt_zero _)
      | succ x =>
        induction y using Fin.cases with
        | zero =>
          have := (mem_parab_two k).1 q.2 (ψ ⟨x, u⟩) v
          rwa [h1, h0] at this
        | succ y =>
          have := hq x y u v (Fin.succ_lt_succ_iff.1 hxy)
          rwa [hπ2, h1, h1] at this
  · exact exists_parab_mul _ x
  · have h1' : IsSmoothChar (((deltaHalf k _).comp
        (leviTwo k (m 0) b).toMonoidHom).comp (MonoidHom.inr _ _)) :=
      ((isSmoothChar_deltaHalf k).comp _ (continuous_leviTwo k)).comp _ (Continuous.prodMk_right 1)
    filter_upwards [h1'.mem_nhds (one_mem _)] with u hu
    exact MonoidHom.mem_ker.1 hu
  · let g := leviProj k e ⟨q, h1'⟩
    have e1 : (π q).1 = g 0 := Units.ext (Matrix.ext fun x y => by
      rw [hπ1, h0, h0]; rfl)
    have e2 : leviProj k _ ⟨(π q).2, h2⟩ = fun i : Fin s => g i.succ := funext fun i => Units.ext (Matrix.ext fun x y => by
      show ((π q).2).val (ψ ⟨i, x⟩) (ψ ⟨i, y⟩) = _
      rw [hπ2, h1, h1]; rfl)
    have e3 : GeneralLinearGroup.det (π q).2 = ∏ i : Fin s, GeneralLinearGroup.det (g i.succ) := by
      have := det_parab k _ ⟨(π q).2, h2⟩
      rwa [e2] at this
    have e4 : deltaHalf k m g = deltaHalf k _ (leviTwo k _ _ (π q)) *
        deltaHalf k (fun i : Fin s => m i.succ) fun i => g i.succ := by
      rw [deltaHalf_two, deltaHalf_apply, deltaHalf_apply, Fin.prod_univ_succ, e1, e3, map_prod, modExp_zero,
        mul_assoc, ← Finset.prod_mul_distrib, Fintype.card_congr ψ]
      refine congrArg₂ _ (by simp) (Finset.prod_congr rfl fun i _ => ?_)
      rw [modExp_succ, ← MonoidHom.mul_apply, ← absPow_add]
      congr 2
      push_cast
      ring
    show (deltaHalf k m g : ℂ) • σ g (κ x) = (deltaHalf k _ (leviTwo k _ _ (π q)) : ℂ) •
      κ (TensorProduct.map (σ₀ (π q).1) ((deltaHalf k _ (leviProj k _ ⟨(π q).2, h2⟩) : ℂ) •
        ρ (leviProj k _ ⟨(π q).2, h2⟩)) x)
    rw [h, e4, e2, e1, TensorProduct.map_smul_right, LinearMap.smul_apply, map_smul, smul_smul, Units.val_mul]

/- English proof (translation)
Use `ind₂_parInd_equiv_placed (m := fun i => Fin (d i)) (stdBlocks d hd) (stdSum rfl) (stdBlocks (fun i : Fin s => d i.succ) rfl) (fun x => Fin.ext ?_) (fun i x => Fin.ext ?_) (σ 0) _ _ (tensorCons X) fun g x => ?_` and prove the remaining obligations. Simplify using `[stdBlocks_val]`. Rewrite using `[stdSum_inr, stdBlocks_val, stdBlocks_val]`. Simplify using `[Fin.sum_univ_succ, add_assoc]`. Proceed by induction on `x with`.

Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Consider the case `tmul v w`. Proceed by induction on `w using PiTensorProduct.induction_on with`. Consider the case `add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]`.

Consider the case `smul_tprod c y`. Simplify using `only [TensorProduct.tmul_smul, map_smul, TensorProduct.map_tmul, piTensor_tprod, tensorCons_tmul]`. Use `congr 2`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `induction i using Fin.cases <;> rfl`.
-/
theorem nonempty_prod₂_equiv_multiProd_succ (d : Fin (s + 1) → ℕ)
    (hd : ∑ i, d i = d 0 + ∑ i : Fin s, d i.succ) {X : Fin (s + 1) → Type} [∀ i, AddCommGroup (X i)]
    [∀ i, Module ℂ (X i)] (σ : ∀ i, Representation ℂ (GL (Fin (d i)) k) (X i)) :
    Nonempty ((prod₂ (σ 0) (multiProd (stdBlocks (fun i : Fin s => d i.succ) rfl)
      fun i : Fin s => σ i.succ)).Equiv (multiProd (stdBlocks d hd) σ)) := by
  refine ind₂_parInd_equiv_placed (m := fun i => Fin (d i)) (stdBlocks d hd) (stdSum rfl)
    (stdBlocks (fun i : Fin s => d i.succ) rfl) (fun x => Fin.ext ?_) (fun i x => Fin.ext ?_) (σ 0) _ _
    (tensorCons X) fun g x => ?_
  · simp [stdBlocks_val]
  · rw [stdSum_inr, stdBlocks_val, stdBlocks_val]
    simp [Fin.sum_univ_succ, add_assoc]
  · induction x with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul v w =>
      induction w using PiTensorProduct.induction_on with
      | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
      | smul_tprod c y =>
        simp only [TensorProduct.tmul_smul, map_smul, TensorProduct.map_tmul, piTensor_tprod, tensorCons_tmul]
        congr 2
        funext i
        induction i using Fin.cases <;> rfl

end Stages

end GlobalTheory.SmGL.MultiIrr

namespace GlobalTheory.LocGL.SupportRing

open GlobalTheory.SmGL.MultiIrr GlobalTheory.JHMult

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/- English proof (translation)
Take `⟨m, c⟩` from `x`. Distinguish the cases in `hm : m = n`. Substitute `hm` using the available equality. Rewrite using `[clsGL_apply, cls_apply]`. Conclude with `Int.natCast_nonneg _`.

Rewrite using `[clsGL, Finsupp.mapDomain_notin_range]`. Introduce and unpack `⟨c', h'⟩`. Conclude with `hm (congrArg Sigma.fst h').symm`.
-/
theorem clsGL_nonneg {n : ℕ} (π : Representation ℂ (GL (Fin n) k) V) (h : HasFiniteLength π) (x : IrrGL k) :
    0 ≤ clsGL π h x := by
  obtain ⟨m, c⟩ := x
  by_cases hm : m = n
  · subst hm
    rw [clsGL_apply, cls_apply]
    exact Int.natCast_nonneg _
  · rw [clsGL, Finsupp.mapDomain_notin_range]
    rintro ⟨c', h'⟩
    exact hm (congrArg Sigma.fst h').symm

/- English proof (translation)
Take `⟨n, c⟩` from `x`. Conclude with `(clsGL_irr c.rep h).trans (by rw [IrrCl.cl_rep])`.
-/
theorem clsGL_rep (x : IrrGL k) (h : HasFiniteLength x.rep) : clsGL x.rep h = Finsupp.single x 1 := by
  obtain ⟨n, c⟩ := x
  exact (clsGL_irr c.rep h).trans (by rw [IrrCl.cl_rep])

/- English proof (translation)
Take `⟨r, h1, h2⟩` from `cls_apply_cl B hB ⟨V, π, hs, hi⟩`. Establish `h3 : clsGL B hB (IrrGL.of π hs hi) = r` using `(clsGL_apply B hB _).trans h2`. Establish `h4 : r ≠ 0` using `fun e => jhMult_ne_zero_iff.2 h (by rw [show jhMult π B = _ from h1, e]; rfl)`. Rewrite using `[h3]`. Conclude with `Nat.pos_of_ne_zero h4` after adjusting the coercions.
-/
theorem clsGL_of_pos {N : ℕ} {B : Representation ℂ (GL (Fin N) k) W} (hB : HasFiniteLength B)
    {π : Representation ℂ (GL (Fin N) k) V} (hs : IsSmooth π) (hi : π.IsIrreducible) (h : IsSubquotient π B) :
    0 < clsGL B hB (IrrGL.of π hs hi) := by
  obtain ⟨r, h1, h2⟩ := cls_apply_cl B hB ⟨V, π, hs, hi⟩
  have h3 : clsGL B hB (IrrGL.of π hs hi) = r := (clsGL_apply B hB _).trans h2
  have h4 : r ≠ 0 := fun e => jhMult_ne_zero_iff.2 h (by rw [show jhMult π B = _ from h1, e]; rfl)
  rw [h3]
  exact_mod_cast Nat.pos_of_ne_zero h4

/- English proof (translation)
Take `⟨r, h1, h2⟩` from `cls_apply_cl B hB ⟨V, π, hs, hi⟩`. Establish `h3 : clsGL B hB (IrrGL.of π hs hi) = r` using `(clsGL_apply B hB _).trans h2`. Use `jhMult_ne_zero_iff.1 fun e => h ?_` and prove the remaining obligations. Establish `h5 : (r : ℕ∞) = 0` using `h1.symm.trans e`. Rewrite using `[h3]`.

Conclude with `h5` after adjusting the coercions.
-/
theorem isSubquotient_of_clsGL_ne {N : ℕ} {B : Representation ℂ (GL (Fin N) k) W} (hB : HasFiniteLength B)
    {π : Representation ℂ (GL (Fin N) k) V} (hs : IsSmooth π) (hi : π.IsIrreducible)
    (h : clsGL B hB (IrrGL.of π hs hi) ≠ 0) : IsSubquotient π B := by
  obtain ⟨r, h1, h2⟩ := cls_apply_cl B hB ⟨V, π, hs, hi⟩
  have h3 : clsGL B hB (IrrGL.of π hs hi) = r := (clsGL_apply B hB _).trans h2
  refine jhMult_ne_zero_iff.1 fun e => h ?_
  have h5 : (r : ℕ∞) = 0 := h1.symm.trans e
  rw [h3]
  exact_mod_cast h5

variable {A : Type 1} [CommRing A]

def bas (Ψ : GrothGL k ≃+ A) (x : IrrGL k) : A := Ψ (Finsupp.single x 1)

def Pos (Ψ : GrothGL k ≃+ A) (a : A) : Prop := ∀ x, 0 ≤ Ψ.symm a x

def pc (Ψ : GrothGL k ≃+ A) (s : Multiset (IrrGL k)) : A := (s.map (bas Ψ)).prod

variable {Ψ : GrothGL k ≃+ A}

/- English proof (translation)
Introduce `x` and use `by simp`.
-/
theorem pos_zero : Pos Ψ 0 := fun x => by simp

/- English proof (translation)
Introduce `x` and use `by rw [map_add, Finsupp.add_apply] exact add_nonneg (ha x) (hb x)`.
-/
theorem Pos.add {a b : A} (ha : Pos Ψ a) (hb : Pos Ψ b) : Pos Ψ (a + b) := fun x => by
  rw [map_add, Finsupp.add_apply]
  exact add_nonneg (ha x) (hb x)

/- English proof (translation)
Introduce `x` and use `by rw [map_zsmul, Finsupp.smul_apply, smul_eq_mul] exact mul_nonneg hc (ha x)`.
-/
theorem Pos.zsmul {a : A} (ha : Pos Ψ a) {c : ℤ} (hc : 0 ≤ c) : Pos Ψ (c • a) := fun x => by
  rw [map_zsmul, Finsupp.smul_apply, smul_eq_mul]
  exact mul_nonneg hc (ha x)

/- English proof (translation)
Proceed by induction on `t using Finset.induction_on with`. Consider the case `empty => simpa using pos_zero`. Consider the case `insert a t ha ih`. Rewrite using `[Finset.sum_insert ha]`. Conclude with `(h a (Finset.mem_insert_self a t)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))`.
-/
theorem pos_sum {ι : Type*} (t : Finset ι) {f : ι → A} (h : ∀ i ∈ t, Pos Ψ (f i)) : Pos Ψ (∑ i ∈ t, f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using pos_zero
  | insert a t ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a t)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/- English proof (translation)
Introduce `x` and use `by rw [Ψ.symm_apply_apply] exact clsGL_nonneg π h x`.
-/
theorem pos_cls {n : ℕ} (π : Representation ℂ (GL (Fin n) k) V) (h : HasFiniteLength π) :
    Pos Ψ (Ψ (clsGL π h)) := fun x => by
  rw [Ψ.symm_apply_apply]
  exact clsGL_nonneg π h x

/- English proof (translation)
Rewrite using `[clsGL_rep, bas]`.
-/
theorem bas_eq (x : IrrGL k) (h : HasFiniteLength x.rep) : bas Ψ x = Ψ (clsGL x.rep h) := by
  rw [clsGL_rep, bas]

/- English proof (translation)
Rewrite using `[bas_eq x x.2.rep.hasFiniteLength]`. Conclude with `pos_cls _ _`.
-/
theorem pos_bas (x : IrrGL k) : Pos Ψ (bas Ψ x) := by
  rw [bas_eq x x.2.rep.hasFiniteLength]
  exact pos_cls _ _

/- English proof (translation)
Use `conv_lhs => rw [← Ψ.apply_symm_apply a, ← Finsupp.sum_single (Ψ.symm a)]`. Rewrite using `[Finsupp.sum, map_sum]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[bas, ← map_zsmul, Finsupp.smul_single_one]`.
-/
theorem eq_sum_bas (a : A) : a = ∑ x ∈ (Ψ.symm a).support, (Ψ.symm a x) • bas Ψ x := by
  conv_lhs => rw [← Ψ.apply_symm_apply a, ← Finsupp.sum_single (Ψ.symm a)]
  rw [Finsupp.sum, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [bas, ← map_zsmul, Finsupp.smul_single_one]

/- English proof (translation)
Take `⟨h, e⟩` from `hΨ.2 _ _ _ _ x.rep y.rep x.2.rep.hasFiniteLength y.2.rep.hasFiniteLength x.2.rep.smooth y.2.rep.smooth`. Rewrite using `[bas_eq x x.2.rep.hasFiniteLength, bas_eq y y.2.rep.hasFiniteLength, ← e]`. Conclude with `pos_cls _ _`.
-/
theorem pos_bas_mul (hΨ : IsProductIso k Ψ) (x y : IrrGL k) : Pos Ψ (bas Ψ x * bas Ψ y) := by
  obtain ⟨h, e⟩ := hΨ.2 _ _ _ _ x.rep y.rep x.2.rep.hasFiniteLength y.2.rep.hasFiniteLength x.2.rep.smooth y.2.rep.smooth
  rw [bas_eq x x.2.rep.hasFiniteLength, bas_eq y y.2.rep.hasFiniteLength, ← e]
  exact pos_cls _ _

/- English proof (translation)
Rewrite using `[eq_sum_bas (Ψ := Ψ) a, eq_sum_bas (Ψ := Ψ) b, Finset.sum_mul_sum]`. Use `pos_sum _ fun x _ => pos_sum _ fun y _ => ?_` and prove the remaining obligations. Rewrite using `[smul_mul_smul_comm]`. Conclude with `(pos_bas_mul hΨ x y).zsmul (mul_nonneg (ha x) (hb y))`.
-/
theorem Pos.mul (hΨ : IsProductIso k Ψ) {a b : A} (ha : Pos Ψ a) (hb : Pos Ψ b) : Pos Ψ (a * b) := by
  rw [eq_sum_bas (Ψ := Ψ) a, eq_sum_bas (Ψ := Ψ) b, Finset.sum_mul_sum]
  refine pos_sum _ fun x _ => pos_sum _ fun y _ => ?_
  rw [smul_mul_smul_comm]
  exact (pos_bas_mul hΨ x y).zsmul (mul_nonneg (ha x) (hb y))

/- English proof (translation)
Rewrite using `[← hΨ.1]`. Conclude with `pos_bas _`.
-/
theorem pos_one (hΨ : IsProductIso k Ψ) : Pos Ψ (1 : A) := by
  rw [← hΨ.1]
  exact pos_bas _

/- English proof (translation)
Simplify using `using ha.add h`.
-/
theorem pos_of_sub {a b : A} (ha : Pos Ψ a) (h : Pos Ψ (b - a)) : Pos Ψ b := by
  simpa using ha.add h

/- English proof (translation)
Establish `e : a' * b' - a * b = (a' - a) * b' + a * (b' - b)` using `by ring`. Rewrite using `[e]`. Conclude with `(h1.mul hΨ hb').add (ha.mul hΨ h2)`.
-/
theorem pos_mul_sub (hΨ : IsProductIso k Ψ) {a a' b b' : A} (ha : Pos Ψ a) (hb' : Pos Ψ b')
    (h1 : Pos Ψ (a' - a)) (h2 : Pos Ψ (b' - b)) : Pos Ψ (a' * b' - a * b) := by
  have e : a' * b' - a * b = (a' - a) * b' + a * (b' - b) := by ring
  rw [e]
  exact (h1.mul hΨ hb').add (ha.mul hΨ h2)

/- English proof (translation)
Proceed by induction on `t using Finset.induction_on with`. Consider the case `empty => simpa using ⟨pos_one hΨ, pos_zero⟩`. Consider the case `insert a t ha ih`. Rewrite using `[Finset.prod_insert ha, Finset.prod_insert ha]`. Conclude with `⟨(hf a).mul hΨ ih.1, pos_mul_sub hΨ (hf a) (pos_of_sub ih.1 ih.2) (h a) ih.2⟩`.
-/
theorem pos_prod_sub (hΨ : IsProductIso k Ψ) {ι : Type*} (t : Finset ι) {f g : ι → A} (hf : ∀ i, Pos Ψ (f i))
    (h : ∀ i, Pos Ψ (g i - f i)) :
    Pos Ψ (∏ i ∈ t, f i) ∧ Pos Ψ (∏ i ∈ t, g i - ∏ i ∈ t, f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using ⟨pos_one hΨ, pos_zero⟩
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact ⟨(hf a).mul hΨ ih.1, pos_mul_sub hΨ (hf a) (pos_of_sub ih.1 ih.2) (h a) ih.2⟩

/- English proof (translation)
Simplify using `[pc]`.
-/
@[simp] theorem pc_zero : pc Ψ 0 = 1 := by simp [pc]

/- English proof (translation)
Simplify using `[pc]`.
-/
theorem pc_add (s t : Multiset (IrrGL k)) : pc Ψ (s + t) = pc Ψ s * pc Ψ t := by simp [pc]

/- English proof (translation)
Proceed by induction on `u using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a u ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, pc_add, ih]`.
-/
theorem pc_sum {ι : Type*} (u : Finset ι) (t : ι → Multiset (IrrGL k)) :
    pc Ψ (∑ i ∈ u, t i) = ∏ i ∈ u, pc Ψ (t i) := by
  classical
  induction u using Finset.induction_on with
  | empty => simp
  | insert a u ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, pc_add, ih]

/- English proof (translation)
Simplify using `only [pc, Multiset.map_map]`. Both sides reduce to the same expression.
-/
theorem pc_map {h : ℕ} (x : Fin h → IrrGL k) : pc Ψ (Finset.univ.val.map x) = ∏ a, bas Ψ (x a) := by
  simp only [pc, Multiset.map_map]
  rfl

end GlobalTheory.LocGL.SupportRing

namespace GlobalTheory.LocGL.SupportRing

open GlobalTheory.SmGL.MultiIrr GlobalTheory.JHMult

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {A : Type 1} [CommRing A] {Ψ : GrothGL k ≃+ A}

/- English proof (translation)
Use `haveI : Subsingleton (GL (Fin 0) k) := ⟨fun _ _ => Units.ext (Subsingleton.elim _ _)⟩`. Set `κ : IndSp e (piTensor σ) ≃ₗ[ℂ] ⨂[ℂ] i, X i` to `LinearEquiv.ofBijective (ev _ 1) ⟨fun f g h => Subtype.ext (Subtype.ext (funext fun x => by rw [Subsingleton.elim x 1]; exact h)), fun v => ⟨⟨⟨fun _ => v, fun p _ => by rw [Subsingleton.elim p 1, map_one]; rfl⟩, mem_smooth_of_eventually _ (.of_forall fun _ _ => rfl)⟩, rfl⟩⟩`. Use `⟨.mk (κ.trans (PiTensorProduct.isEmptyEquiv _)) fun g => ?_⟩` and prove the remaining obligations. Rewrite using `[Subsingleton.elim g 1]`. Simplify using `only [map_one]`.

Conclude with `LinearMap.ext fun _ => rfl`.
-/
theorem nonempty_equiv_unit {d : Fin 0 → ℕ} (e : (Σ i, Fin (d i)) ≃ Fin 0) {X : Fin 0 → Type}
    [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)] (σ : ∀ i, Representation ℂ (GL (Fin (d i)) k) (X i)) :
    Nonempty ((multiProd e σ).Equiv (IrrRep.det (k := k) (Fin 0) 1 isSmoothChar_one).ρ) := by
  haveI : Subsingleton (GL (Fin 0) k) := ⟨fun _ _ => Units.ext (Subsingleton.elim _ _)⟩
  let κ : IndSp e (piTensor σ) ≃ₗ[ℂ] ⨂[ℂ] i, X i := LinearEquiv.ofBijective (ev _ 1) ⟨fun f g h =>
    Subtype.ext (Subtype.ext (funext fun x => by rw [Subsingleton.elim x 1]; exact h)), fun v =>
    ⟨⟨⟨fun _ => v, fun p _ => by rw [Subsingleton.elim p 1, map_one]; rfl⟩,
      mem_smooth_of_eventually _ (.of_forall fun _ _ => rfl)⟩, rfl⟩⟩
  refine ⟨.mk (κ.trans (PiTensorProduct.isEmptyEquiv _)) fun g => ?_⟩
  rw [Subsingleton.elim g 1]
  simp only [map_one]
  exact LinearMap.ext fun _ => rfl

/- English proof (translation)
Proceed by induction on `h with`. Consider the case `zero`. Introduce `d X _ _ N hd σ hs hf`. Take `rfl : N = 0` from `by simpa using hd.symm`. Set `ι : IrrRep (GL (Fin 0) k)` to `⟨_, multiProd (stdBlocks d hd) σ, isSmooth_parInd _ _, isIrreducible_multiProd_zero _ σ⟩`.

Use `⟨ι.hasFiniteLength, ?_⟩` and prove the remaining obligations. Take `⟨φ⟩` from `nonempty_equiv_unit (stdBlocks d hd) σ`. Establish `h1 : ι.cl = (IrrRep.det (k` using `k) (Fin 0) 1 isSmoothChar_one).cl := IrrRep.cl_eq_iff.2 ⟨φ⟩`. Establish `h2 : clsGL ι.ρ ι.hasFiniteLength = GrothGL.unit k`. Rewrite using `[clsGL_irr, h1]`.

Both sides reduce to the same expression. Simplify using `using (congrArg Ψ h2).trans hΨ.1`. Consider the case `succ h ih`. Introduce `d X _ _ N hd σ hs hf`. Take `rfl : N = d 0 + ∑ i : Fin h, d i.succ` from `hd.symm.trans (Fin.sum_univ_succ d)`.

Take `⟨hT, eT⟩` from `ih (d := fun i => d i.succ) (X := fun i => X i.succ) rfl (fun i => σ i.succ) (fun i => hs i.succ) (fun i => hf i.succ)`. Take `⟨hP, eP⟩` from `hΨ.2 _ _ _ _ (σ 0) _ (hf 0) hT (hs 0) (isSmooth_parInd _ _)`. Take `⟨E⟩` from `nonempty_prod₂_equiv_multiProd_succ d hd σ`. Establish `hQ` using `hP.of_equiv E`. Use `⟨hQ, ?_⟩` and prove the remaining obligations.

Rewrite using `[← clsGL_congr E hP hQ, eP, eT, Fin.prod_univ_succ]`.
-/
theorem multiProd_cls (hΨ : IsProductIso k Ψ) {h : ℕ} : ∀ {d : Fin h → ℕ} {X : Fin h → Type}
    [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)] {N : ℕ} (hd : ∑ i, d i = N)
    (σ : ∀ i, Representation ℂ (GL (Fin (d i)) k) (X i)) (hs : ∀ i, IsSmooth (σ i))
    (hf : ∀ i, HasFiniteLength (σ i)),
    ∃ hp : HasFiniteLength (multiProd (stdBlocks d hd) σ),
      Ψ (clsGL (multiProd (stdBlocks d hd) σ) hp) = ∏ i, Ψ (clsGL (σ i) (hf i)) := by
  induction h with
  | zero =>
    intro d X _ _ N hd σ hs hf
    obtain rfl : N = 0 := by simpa using hd.symm
    let ι : IrrRep (GL (Fin 0) k) := ⟨_, multiProd (stdBlocks d hd) σ, isSmooth_parInd _ _,
      isIrreducible_multiProd_zero _ σ⟩
    refine ⟨ι.hasFiniteLength, ?_⟩
    obtain ⟨φ⟩ := nonempty_equiv_unit (stdBlocks d hd) σ
    have h1 : ι.cl = (IrrRep.det (k := k) (Fin 0) 1 isSmoothChar_one).cl := IrrRep.cl_eq_iff.2 ⟨φ⟩
    have h2 : clsGL ι.ρ ι.hasFiniteLength = GrothGL.unit k := by
      rw [clsGL_irr, h1]
      rfl
    simpa using (congrArg Ψ h2).trans hΨ.1
  | succ h ih =>
    intro d X _ _ N hd σ hs hf
    obtain rfl : N = d 0 + ∑ i : Fin h, d i.succ := hd.symm.trans (Fin.sum_univ_succ d)
    obtain ⟨hT, eT⟩ := ih (d := fun i => d i.succ) (X := fun i => X i.succ) rfl (fun i => σ i.succ)
      (fun i => hs i.succ) (fun i => hf i.succ)
    obtain ⟨hP, eP⟩ := hΨ.2 _ _ _ _ (σ 0) _ (hf 0) hT (hs 0) (isSmooth_parInd _ _)
    obtain ⟨E⟩ := nonempty_prod₂_equiv_multiProd_succ d hd σ
    have hQ := hP.of_equiv E
    refine ⟨hQ, ?_⟩
    rw [← clsGL_congr E hP hQ, eP, eT, Fin.prod_univ_succ]

/- English proof (translation)
Take `⟨hp, e⟩` from `multiProd_cls hΨ hd (fun a => (x a).rep) (fun a => (x a).2.rep.smooth) (fun a => (x a).2.rep.hasFiniteLength)`. Conclude with `⟨hp, e.trans (Finset.prod_congr rfl fun a _ => (bas_eq _ _).symm)⟩`.
-/
theorem prodIrr_cls (hΨ : IsProductIso k Ψ) {h N : ℕ} (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N) :
    ∃ hp : HasFiniteLength (prodIrr x hd), Ψ (clsGL (prodIrr x hd) hp) = ∏ a, bas Ψ (x a) := by
  obtain ⟨hp, e⟩ := multiProd_cls hΨ hd (fun a => (x a).rep) (fun a => (x a).2.rep.smooth)
    (fun a => (x a).2.rep.hasFiniteLength)
  exact ⟨hp, e.trans (Finset.prod_congr rfl fun a _ => (bas_eq _ _).symm)⟩

/- English proof (translation)
Take `⟨c, x, rfl, -, -, e, hsub⟩` from `h`. Establish `hd : ∑ a, (x a).1 = N` using `by simpa using Fintype.card_congr e`. Take `⟨hp, ep⟩` from `prodIrr_cls hΨ x hd`. Take `⟨φ⟩` from `(GlobalTheory.SmGL.Placing.parInd_jac_placing k _ _ _ e (stdBlocks (fun a => (x a).1) hd) _).1 (piTensor fun a => (x a).rep)`. Establish `h1 : IsSubquotient π (prodIrr x hd)` using `hsub.trans (.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective)`.

Establish `h2` using `clsGL_of_pos hp hs hi h1`. Introduce `y`. Rewrite using `[pc_map, ← ep, map_sub, Ψ.symm_apply_apply, bas, Ψ.symm_apply_apply, Finsupp.sub_apply]`. Establish `h0` using `clsGL_nonneg _ hp y`. Distinguish the cases in `hy : IrrGL.of π hs hi = y`.

Substitute `hy` using the available equality. Rewrite using `[Finsupp.single_eq_same]`. Use linear arithmetic over natural numbers and integers. Establish `hz : (Finsupp.single (IrrGL.of π hs hi) (1 : ℤ)) y = 0` using `by classical`. Conclude with `(Finsupp.single_apply).trans (if_neg hy)`.

Establish `hg : ∀ a b : ℤ, 0 ≤ a → b = 0 → 0 ≤ a - b` using `fun a b h e => by omega`. Conclude with `hg _ _ h0 hz`.
-/
theorem pos_pc_sub (hΨ : IsProductIso k Ψ) {N : ℕ} {π : Representation ℂ (GL (Fin N) k) V}
    {s : Multiset (IrrGL k)} (h : HasSupport π s) (hs : IsSmooth π) (hi : π.IsIrreducible) :
    Pos Ψ (pc Ψ s - bas Ψ (IrrGL.of π hs hi)) := by
  obtain ⟨c, x, rfl, -, -, e, hsub⟩ := h
  have hd : ∑ a, (x a).1 = N := by simpa using Fintype.card_congr e
  obtain ⟨hp, ep⟩ := prodIrr_cls hΨ x hd
  obtain ⟨φ⟩ := (GlobalTheory.SmGL.Placing.parInd_jac_placing k _ _ _ e (stdBlocks (fun a => (x a).1) hd) _).1
    (piTensor fun a => (x a).rep)
  have h1 : IsSubquotient π (prodIrr x hd) :=
    hsub.trans (.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective)
  have h2 := clsGL_of_pos hp hs hi h1
  intro y
  rw [pc_map, ← ep, map_sub, Ψ.symm_apply_apply, bas, Ψ.symm_apply_apply, Finsupp.sub_apply]
  have h0 := clsGL_nonneg _ hp y
  by_cases hy : IrrGL.of π hs hi = y
  · subst hy
    rw [Finsupp.single_eq_same]
    omega
  · have hz : (Finsupp.single (IrrGL.of π hs hi) (1 : ℤ)) y = 0 := by
      classical
      exact (Finsupp.single_apply).trans (if_neg hy)
    have hg : ∀ a b : ℤ, 0 ≤ a → b = 0 → 0 ≤ a - b := fun a b h e => by omega
    exact hg _ _ h0 hz

/- English proof (translation)
Take `⟨c, x, rfl⟩ : ∃ (c : ℕ) (x : Fin c → IrrGL k), Finset.univ.val.map x = s` from `⟨s.toList.length, s.toList.get, by`. Rewrite using `[Fin.univ_val_map, List.ofFn_get, Multiset.coe_toList]⟩`. Take `⟨hp, ep⟩` from `prodIrr_cls hΨ x rfl`. Rewrite `h` using `[pc_map, ← ep, Ψ.symm_apply_apply]`. Establish `hN : N = ∑ a, (x a).1`.

Assume the negation of the conclusion as `hne`. Use `h ?_` and prove the remaining obligations. Rewrite using `[clsGL, Finsupp.mapDomain_notin_range]`. Introduce and unpack `⟨c', h'⟩`. Conclude with `hne (congrArg Sigma.fst h').symm`.

Substitute `hN` using the available equality. Conclude with `hasSupport_of_isSubquotient hi (fun a => hc _ (Multiset.mem_map_of_mem _ (Finset.mem_univ a))) (isSubquotient_of_clsGL_ne hp hs hi h)`.
-/
theorem hasSupport_of_coef_ne (hΨ : IsProductIso k Ψ) {N : ℕ} {π : Representation ℂ (GL (Fin N) k) V}
    {s : Multiset (IrrGL k)} (hc : ∀ y ∈ s, y.IsCusp) (hs : IsSmooth π) (hi : π.IsIrreducible)
    (h : Ψ.symm (pc Ψ s) (IrrGL.of π hs hi) ≠ 0) : HasSupport π s := by
  obtain ⟨c, x, rfl⟩ : ∃ (c : ℕ) (x : Fin c → IrrGL k), Finset.univ.val.map x = s :=
    ⟨s.toList.length, s.toList.get, by
      rw [Fin.univ_val_map, List.ofFn_get, Multiset.coe_toList]⟩
  obtain ⟨hp, ep⟩ := prodIrr_cls hΨ x rfl
  rw [pc_map, ← ep, Ψ.symm_apply_apply] at h
  have hN : N = ∑ a, (x a).1 := by
    by_contra hne
    refine h ?_
    rw [clsGL, Finsupp.mapDomain_notin_range]
    rintro ⟨c', h'⟩
    exact hne (congrArg Sigma.fst h').symm
  subst hN
  exact hasSupport_of_isSubquotient hi (fun a => hc _ (Multiset.mem_map_of_mem _ (Finset.mem_univ a)))
    (isSubquotient_of_clsGL_ne hp hs hi h)

/- English proof (translation)
Establish `hs : IsSmooth π` using `h.isSmooth (isSmooth_prodIrr y hd)`. Take `⟨hp, ep⟩` from `prodIrr_cls hΨ y hd`. Establish `h1 : ∀ a, Pos Ψ (pc Ψ (t a) - bas Ψ (y a))` using `fun a => by`. Use `pos_pc_sub (Ψ := Ψ) hΨ (ht a) (y a).2.rep.smooth (y a).2.rep.irr` as an intermediate fact. Rewrite `this` using `[IrrGL.of_rep]`. Then use the resulting hypothesis.

Establish `h2` using `(pos_prod_sub hΨ Finset.univ (fun a => pos_bas (y a)) h1).2`. Rewrite `h2` using `[← pc_sum, ← ep]`. Use `hasSupport_of_coef_ne hΨ (fun z hz => ?_) hs hi (ne_of_gt ?_)` and prove the remaining obligations. Take `⟨a, -, ha⟩` from `Multiset.mem_sum.1 hz`. Conclude with `(ht a).isCusp ha`.

Establish `h3` using `h2 (IrrGL.of π hs hi)`. Rewrite `h3` using `[map_sub, Ψ.symm_apply_apply, Finsupp.sub_apply]`. Establish `h4` using `clsGL_of_pos hp hs hi h`. Use linear arithmetic over natural numbers and integers.
-/
theorem hasSupport_of_isSubquotient_prodIrr (hΨ : IsProductIso k Ψ) {c N : ℕ} {y : Fin c → IrrGL k}
    {hd : ∑ a, (y a).1 = N} {t : Fin c → Multiset (IrrGL k)} (ht : ∀ a, HasSupport (y a).rep (t a))
    {π : Representation ℂ (GL (Fin N) k) V} (hi : π.IsIrreducible) (h : IsSubquotient π (prodIrr y hd)) :
    HasSupport π (∑ a, t a) := by
  have hs : IsSmooth π := h.isSmooth (isSmooth_prodIrr y hd)
  obtain ⟨hp, ep⟩ := prodIrr_cls hΨ y hd
  have h1 : ∀ a, Pos Ψ (pc Ψ (t a) - bas Ψ (y a)) := fun a => by
    have := pos_pc_sub (Ψ := Ψ) hΨ (ht a) (y a).2.rep.smooth (y a).2.rep.irr
    rwa [IrrGL.of_rep] at this
  have h2 := (pos_prod_sub hΨ Finset.univ (fun a => pos_bas (y a)) h1).2
  rw [← pc_sum, ← ep] at h2
  refine hasSupport_of_coef_ne hΨ (fun z hz => ?_) hs hi (ne_of_gt ?_)
  · obtain ⟨a, -, ha⟩ := Multiset.mem_sum.1 hz
    exact (ht a).isCusp ha
  · have h3 := h2 (IrrGL.of π hs hi)
    rw [map_sub, Ψ.symm_apply_apply, Finsupp.sub_apply] at h3
    have h4 := clsGL_of_pos hp hs hi h
    omega

/- English proof (translation)
Take `⟨Z, Ψ, hS, hΨ, hX⟩` from `hZ k`. Set `Q : MvPolynomial (Segment k) ℤ → Prop` to `fun p => Pos Ψ p ∧ ∃ s : Multiset (IrrGL k), (∀ y ∈ s, y.IsCusp) ∧ Pos Ψ (pc Ψ s - p)`. Establish `q1 : Q 1` using `⟨pos_one hΨ, 0, by simp, by simpa using pos_zero⟩`. Establish `qm : ∀ p q, Q p → Q q → Q (p * q)`. Introduce and unpack `p q ⟨a1, s, a2, a3⟩ ⟨b1, t, b2, b3⟩`.

Use `⟨a1.mul hΨ b1, s + t, fun y hy => ?_, ?_⟩` and prove the remaining obligations. Break down `Multiset.mem_add.1 hy with h | h` into its components or cases. Conclude with `a2 y h`. Conclude with `b2 y h`. Rewrite using `[pc_add]`.

Conclude with `pos_mul_sub hΨ a1 (pos_of_sub b1 b3) a3 b3`. Establish `qX : ∀ Δ, Q (MvPolynomial.X Δ)` using `fun Δ => by`. Establish `hd : ∑ a, (Δ.term a).1 = Δ.len * Δ.d` using `Δ.sum_term_fst`. Set `σ` to `Δ.start.rep`. Establish `hσ : σ.cl = Δ.start` using `Δ.start.cl_rep`.

Set `e` to `stdBlocks (fun a => (Δ.term a).1) hd`. Take `⟨φ, hφ⟩` from `((hS Δ σ hσ e (Z Δ).rep).1).1 (Z Δ).cl_rep`. Establish `h1 : IsSubquotient (Z Δ).rep.ρ (prodIrr Δ.term hd)` using `(IsSubquotient.of_injective φ hφ).trans (.of_injective (segProdEquiv Δ hd).toIntertwiningMap (segProdEquiv Δ hd).toLinearEquiv.injective)`. Establish `h2 : HasSupport (Z Δ).rep.ρ Δ.ms` using `hasSupport_of_isSubquotient (Z Δ).rep.irr Δ.isCusp_term h1`. Establish `h3` using `pos_pc_sub (Ψ := Ψ) hΨ h2 (Z Δ).rep.smooth (Z Δ).rep.irr`.

Establish `h4 : bas Ψ (IrrGL.of (Z Δ).rep.ρ (Z Δ).rep.smooth (Z Δ).rep.irr) = MvPolynomial.X Δ`. Rewrite using `[← hX Δ, bas]`. Conclude with `congrArg (fun y => Ψ (Finsupp.single y 1)) (congrArg (Sigma.mk _) (Z Δ).cl_rep)`. Rewrite `h3` using `[h4]`. Conclude with `⟨h4 ▸ pos_bas _, Δ.ms, fun y hy => (h2.isCusp hy), h3⟩`.

Establish `qp : ∀ Δ (n : ℕ), Q (MvPolynomial.X Δ ^ n)` using `fun Δ n => by`. Proceed by induction on `n with`. Consider the case `zero => simpa using q1`. Consider the case `succ n ih => rw [pow_succ]`. Conclude with `qm _ _ ih (qX Δ)`.

Establish `qmon : ∀ m : Segment k →₀ ℕ, Q (MvPolynomial.monomial m 1)` using `fun m => by`. Rewrite using `[MvPolynomial.monomial_eq, map_one, one_mul, Finsupp.prod]`. Conclude with `Finset.prod_induction _ Q qm q1 fun Δ _ => qp Δ _`. Use `set P := Ψ (Finsupp.single x 1) with hP`. Establish `h1 : ∃ m, Ψ.symm (MvPolynomial.monomial m 1) x ≠ 0`.

Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Establish `h2 : Finsupp.single x (1 : ℤ) = Ψ.symm P` using `(Ψ.symm_apply_apply _).symm`. Establish `h3 : Ψ.symm P x = 0`. Rewrite using `[MvPolynomial.as_sum P, map_sum, Finsupp.finset_sum_apply]`.

Use `Finset.sum_eq_zero fun m _ => ?_` and prove the remaining obligations. Establish `h4 : MvPolynomial.monomial m (MvPolynomial.coeff m P) = (MvPolynomial.coeff m P) • MvPolynomial.monomial m (1 : ℤ)`. Rewrite using `[MvPolynomial.smul_monomial, smul_eq_mul, mul_one]`. Rewrite using `[h4, map_zsmul, Finsupp.smul_apply, hne m, smul_zero]`. Rewrite `h3` using `[← h2, Finsupp.single_eq_same]`.

Conclude with `one_ne_zero h3`. Take `⟨m, hm⟩` from `h1`. Take `⟨a1, s, a2, a3⟩` from `qmon m`. Use `⟨s, hasSupport_of_coef_ne hΨ a2 x.2.rep.smooth x.2.rep.irr ?_⟩` and prove the remaining obligations. Establish `h5` using `a3 x`.

Establish `h6` using `a1 x`. Rewrite `h5` using `[map_sub, Finsupp.sub_apply]`. Rewrite using `[show IrrGL.of x.rep x.2.rep.smooth x.2.rep.irr = x from IrrGL.of_rep x]`. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_hasSupport (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing) (x : IrrGL k) :
    ∃ s, HasSupport x.rep s := by
  obtain ⟨Z, Ψ, hS, hΨ, hX⟩ := hZ k
  let Q : MvPolynomial (Segment k) ℤ → Prop := fun p =>
    Pos Ψ p ∧ ∃ s : Multiset (IrrGL k), (∀ y ∈ s, y.IsCusp) ∧ Pos Ψ (pc Ψ s - p)
  have q1 : Q 1 := ⟨pos_one hΨ, 0, by simp, by simpa using pos_zero⟩
  have qm : ∀ p q, Q p → Q q → Q (p * q) := by
    rintro p q ⟨a1, s, a2, a3⟩ ⟨b1, t, b2, b3⟩
    refine ⟨a1.mul hΨ b1, s + t, fun y hy => ?_, ?_⟩
    · rcases Multiset.mem_add.1 hy with h | h
      · exact a2 y h
      · exact b2 y h
    · rw [pc_add]
      exact pos_mul_sub hΨ a1 (pos_of_sub b1 b3) a3 b3
  have qX : ∀ Δ, Q (MvPolynomial.X Δ) := fun Δ => by
    have hd : ∑ a, (Δ.term a).1 = Δ.len * Δ.d := Δ.sum_term_fst
    let σ := Δ.start.rep
    have hσ : σ.cl = Δ.start := Δ.start.cl_rep
    let e := stdBlocks (fun a => (Δ.term a).1) hd
    obtain ⟨φ, hφ⟩ := ((hS Δ σ hσ e (Z Δ).rep).1).1 (Z Δ).cl_rep
    have h1 : IsSubquotient (Z Δ).rep.ρ (prodIrr Δ.term hd) :=
      (IsSubquotient.of_injective φ hφ).trans
        (.of_injective (segProdEquiv Δ hd).toIntertwiningMap (segProdEquiv Δ hd).toLinearEquiv.injective)
    have h2 : HasSupport (Z Δ).rep.ρ Δ.ms := hasSupport_of_isSubquotient (Z Δ).rep.irr Δ.isCusp_term h1
    have h3 := pos_pc_sub (Ψ := Ψ) hΨ h2 (Z Δ).rep.smooth (Z Δ).rep.irr
    have h4 : bas Ψ (IrrGL.of (Z Δ).rep.ρ (Z Δ).rep.smooth (Z Δ).rep.irr) = MvPolynomial.X Δ := by
      rw [← hX Δ, bas]
      exact congrArg (fun y => Ψ (Finsupp.single y 1)) (congrArg (Sigma.mk _) (Z Δ).cl_rep)
    rw [h4] at h3
    exact ⟨h4 ▸ pos_bas _, Δ.ms, fun y hy => (h2.isCusp hy), h3⟩
  have qp : ∀ Δ (n : ℕ), Q (MvPolynomial.X Δ ^ n) := fun Δ n => by
    induction n with
    | zero => simpa using q1
    | succ n ih => rw [pow_succ]; exact qm _ _ ih (qX Δ)
  have qmon : ∀ m : Segment k →₀ ℕ, Q (MvPolynomial.monomial m 1) := fun m => by
    rw [MvPolynomial.monomial_eq, map_one, one_mul, Finsupp.prod]
    exact Finset.prod_induction _ Q qm q1 fun Δ _ => qp Δ _
  set P := Ψ (Finsupp.single x 1) with hP
  have h1 : ∃ m, Ψ.symm (MvPolynomial.monomial m 1) x ≠ 0 := by
    by_contra hne
    push_neg at hne
    have h2 : Finsupp.single x (1 : ℤ) = Ψ.symm P := (Ψ.symm_apply_apply _).symm
    have h3 : Ψ.symm P x = 0 := by
      rw [MvPolynomial.as_sum P, map_sum, Finsupp.finset_sum_apply]
      refine Finset.sum_eq_zero fun m _ => ?_
      have h4 : MvPolynomial.monomial m (MvPolynomial.coeff m P) =
          (MvPolynomial.coeff m P) • MvPolynomial.monomial m (1 : ℤ) := by
        rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
      rw [h4, map_zsmul, Finsupp.smul_apply, hne m, smul_zero]
    rw [← h2, Finsupp.single_eq_same] at h3
    exact one_ne_zero h3
  obtain ⟨m, hm⟩ := h1
  obtain ⟨a1, s, a2, a3⟩ := qmon m
  refine ⟨s, hasSupport_of_coef_ne hΨ a2 x.2.rep.smooth x.2.rep.irr ?_⟩
  have h5 := a3 x
  have h6 := a1 x
  rw [map_sub, Finsupp.sub_apply] at h5
  rw [show IrrGL.of x.rep x.2.rep.smooth x.2.rep.irr = x from IrrGL.of_rep x]
  omega

end GlobalTheory.LocGL.SupportRing

namespace GlobalTheory.LocGL.SupportRing

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V : Type} [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
The claim follows from `(h.tw _ (isSmoothChar_absPow e)).of_equiv (x.twEquiv _ _)`.
-/
theorem hasSupport_nu {x : IrrGL k} {s : Multiset (IrrGL k)} (h : HasSupport x.rep s) (e : ℂ) :
    HasSupport (x.nu e).rep (s.map fun y => y.nu e) :=
  (h.tw _ (isSmoothChar_absPow e)).of_equiv (x.twEquiv _ _)

/- English proof (translation)
Take `⟨Z, Ψ, -, hΨ, -⟩` from `hZ k`. Take `⟨hd, hc⟩` from `h`. Conclude with `hasSupport_of_isSubquotient_prodIrr hΨ (y := spehFactor x d) (t := fun j => s.map fun y => y.nu (((d : ℂ) - 1) / 2 - (j : ℕ))) (fun j => hasSupport_nu hs (((d : ℂ) - 1) / 2 - (j : ℕ))) hc.1 hc.isSubquotient`.
-/
theorem hasSupport_speh (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing) {x : IrrGL k} {d N : ℕ}
    {π : Representation ℂ (GL (Fin N) k) V} (h : IsSpeh x d π) {s : Multiset (IrrGL k)} (hs : HasSupport x.rep s) :
    HasSupport π (∑ j : Fin d, s.map fun y => y.nu (((d : ℂ) - 1) / 2 - (j : ℕ))) := by
  obtain ⟨Z, Ψ, -, hΨ, -⟩ := hZ k
  obtain ⟨hd, hc⟩ := h
  exact hasSupport_of_isSubquotient_prodIrr hΨ (y := spehFactor x d)
    (t := fun j => s.map fun y => y.nu (((d : ℂ) - 1) / 2 - (j : ℕ))) (fun j => hasSupport_nu hs (((d : ℂ) - 1) / 2 - (j : ℕ))) hc.1 hc.isSubquotient

/- English proof (translation)
Take `⟨Z, Ψ, -, hΨ, -⟩` from `hZ k`. Set `φ` to `prodIrrEquiv hd σ hs hi`. Conclude with `hasSupport_of_isSubquotient_prodIrr hΨ (y := fun a => IrrGL.of (σ a) (hs a) (hi a)) (fun a => (ht a).of_equiv (IrrGL.equivOf (σ a) (hs a) (hi a))) hI (.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective)`.
-/
theorem hasSupport_multiProd (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing) {c N : ℕ} {d : Fin c → ℕ}
    (hd : ∑ a, d a = N) {X : Fin c → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    (σ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)) (hs : ∀ a, IsSmooth (σ a))
    (hi : ∀ a, (σ a).IsIrreducible) {t : Fin c → Multiset (IrrGL k)} (ht : ∀ a, HasSupport (σ a) (t a))
    (hI : (multiProd (stdBlocks d hd) σ).IsIrreducible) :
    HasSupport (multiProd (stdBlocks d hd) σ) (∑ a, t a) := by
  obtain ⟨Z, Ψ, -, hΨ, -⟩ := hZ k
  let φ := prodIrrEquiv hd σ hs hi
  exact hasSupport_of_isSubquotient_prodIrr hΨ (y := fun a => IrrGL.of (σ a) (hs a) (hi a))
    (fun a => (ht a).of_equiv (IrrGL.equivOf (σ a) (hs a) (hi a))) hI
    (.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective)

end GlobalTheory.LocGL.SupportRing
