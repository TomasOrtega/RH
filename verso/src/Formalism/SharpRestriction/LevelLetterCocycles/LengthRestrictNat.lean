import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangeMapMemLattice

noncomputable section

open Classical TensorProduct

namespace Formalism.MainNotions.UnusedSlot80.BCW

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions

section Len

variable {O O' : Type} [CommRing O] [CommRing O'] [Algebra O O'] [IsLocalRing O']

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `M _ _ _ _ h`. Establish `hs : Subsingleton M` using `Module.length_eq_zero_iff.1 (by simpa using h)`. Rewrite using `[Module.length_eq_zero_iff.2 hs]`.

Simplify using the standard rewrite rules. Consider the case `succ n ih`. Introduce `M _ _ _ _ h`. Establish `hfin : IsFiniteLength O' M` using `Module.length_ne_top_iff.1 (by rw [h]; exact ENat.natCast_ne_top _)`. Take `⟨_, hA⟩` from `isFiniteLength_iff_isNoetherian_isArtinian.1 hfin`.

Establish `hnt : Nontrivial M`. Assume the negation of the conclusion as `hc`. Rewrite `hc` using `[not_nontrivial_iff_subsingleton]`. Rewrite `h` using `[Module.length_eq_zero_iff.2 hc]`. Conclude with `absurd h (by norm_cast)`.

Establish `hne : ({N : Submodule O' M | N ≠ ⊥} : Set _).Nonempty` using `⟨⊤, top_ne_bot⟩`. Take `⟨N, hN0, hmin⟩` from `IsArtinian.set_has_minimal _ hne`. Establish `hat : IsAtom N` using `⟨hN0, fun I hI => by`. Assume the negation of the conclusion as `hI0`. Conclude with `hmin I hI0 hI⟩`.

Use `haveI hS : IsSimpleModule O' N := isSimpleModule_iff_isAtom.2 hat`. Take `⟨I, hI, ⟨e⟩⟩` from `isSimpleModule_iff_quot_maximal.1 hS`. Establish `hIm` using `IsLocalRing.eq_maximalIdeal hI`. Substitute `hIm` using the available equality. Establish `hNO : Module.length O N = Module.length O (O' ⧸ IsLocalRing.maximalIdeal O')` using `(e.restrictScalars O).length_eq`.

Establish `hN1 : Module.length O' N = 1` using `Module.length_eq_one_iff.2 hS`. Establish `ex'` using `Module.length_eq_add_of_exact N.subtype N.mkQ (Submodule.injective_subtype N) (Submodule.mkQ_surjective N) (LinearMap.exact_subtype_mkQ N)`. Establish `ex` using `Module.length_eq_add_of_exact (N.subtype.restrictScalars O) (N.mkQ.restrictScalars O) (Submodule.injective_subtype N) (Submodule.mkQ_surjective N) (LinearMap.exact_subtype_mkQ N)`. Establish `hQ : Module.length O' (M ⧸ N) = n`. Rewrite `ex'` using `[h, hN1]`.

Consider the cases of `hL : Module.length O' (M ⧸ N) using ENat.recTopCoe with`. Consider the case `top => rw [hL] at ex'`. Simplify using `at ex'`. Consider the case `coe m`. Rewrite `ex'` using `[hL]`.

Establish `: n + 1 = 1 + m` using `by exact_mod_cast ex'`. Use `congr 1`. Use linear arithmetic over natural numbers and integers. Establish `hQO` using `ih (M ⧸ N) hQ`. Rewrite using `[ex, hNO, hQO]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem length_restrict_nat (n : ℕ) : ∀ (M : Type) [AddCommGroup M] [Module O' M] [Module O M]
    [IsScalarTower O O' M], Module.length O' M = n →
    Module.length O M = Module.length O (O' ⧸ IsLocalRing.maximalIdeal O') * n := by
  induction n with
  | zero =>
    intro M _ _ _ _ h
    have hs : Subsingleton M := Module.length_eq_zero_iff.1 (by simpa using h)
    rw [Module.length_eq_zero_iff.2 hs]
    simp
  | succ n ih =>
    intro M _ _ _ _ h
    have hfin : IsFiniteLength O' M :=
      Module.length_ne_top_iff.1 (by rw [h]; exact ENat.natCast_ne_top _)
    obtain ⟨_, hA⟩ := isFiniteLength_iff_isNoetherian_isArtinian.1 hfin
    have hnt : Nontrivial M := by
      by_contra hc
      rw [not_nontrivial_iff_subsingleton] at hc
      rw [Module.length_eq_zero_iff.2 hc] at h
      exact absurd h (by norm_cast)
    have hne : ({N : Submodule O' M | N ≠ ⊥} : Set _).Nonempty := ⟨⊤, top_ne_bot⟩
    obtain ⟨N, hN0, hmin⟩ := IsArtinian.set_has_minimal _ hne
    have hat : IsAtom N := ⟨hN0, fun I hI => by
      by_contra hI0
      exact hmin I hI0 hI⟩
    haveI hS : IsSimpleModule O' N := isSimpleModule_iff_isAtom.2 hat
    obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.1 hS
    have hIm := IsLocalRing.eq_maximalIdeal hI
    subst hIm
    have hNO : Module.length O N = Module.length O (O' ⧸ IsLocalRing.maximalIdeal O') :=
      (e.restrictScalars O).length_eq
    have hN1 : Module.length O' N = 1 := Module.length_eq_one_iff.2 hS
    have ex' := Module.length_eq_add_of_exact N.subtype N.mkQ (Submodule.injective_subtype N)
      (Submodule.mkQ_surjective N) (LinearMap.exact_subtype_mkQ N)
    have ex := Module.length_eq_add_of_exact (N.subtype.restrictScalars O) (N.mkQ.restrictScalars O)
      (Submodule.injective_subtype N) (Submodule.mkQ_surjective N) (LinearMap.exact_subtype_mkQ N)
    have hQ : Module.length O' (M ⧸ N) = n := by
      rw [h, hN1] at ex'
      cases hL : Module.length O' (M ⧸ N) using ENat.recTopCoe with
      | top => rw [hL] at ex'; simp at ex'
      | coe m =>
        rw [hL] at ex'
        have : n + 1 = 1 + m := by exact_mod_cast ex'
        congr 1; omega
    have hQO := ih (M ⧸ N) hQ
    rw [ex, hNO, hQO]
    push_cast
    ring

/- English proof (translation)
Set `P : Submodule O' O'` to `Ideal.span {algebraMap O O' a}`. Set `Q : Submodule O (ι → O)` to `Submodule.pi Set.univ fun _ => Ideal.span {a}`. Establish `hPQ : (P.restrictScalars O).map (bO.equivFun : O' →ₗ[O] (ι → O)) = Q`. Use extensionality with `y`. Simplify using `only [Submodule.mem_map, Submodule.restrictScalars_mem, Q, Submodule.mem_pi, Set.mem_univ, true_implies, P, Ideal.mem_span_singleton']`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, ⟨z, rfl⟩, rfl⟩ i`. Use `⟨bO.equivFun z i, ?_⟩` and prove the remaining obligations. Establish `: z * algebraMap O O' a = a • z` using `by rw [Algebra.smul_def, mul_comm]`. Rewrite using `[this, LinearEquiv.coe_coe, map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]`.

Introduce `hy choose w hw using hy`. Use `⟨bO.equivFun.symm w * algebraMap O O' a, ⟨_, rfl⟩, ?_⟩` and prove the remaining obligations. Establish `: bO.equivFun.symm w * algebraMap O O' a = a • bO.equivFun.symm w`. Rewrite using `[Algebra.smul_def, mul_comm]`. Rewrite using `[this, LinearEquiv.coe_coe, map_smul, LinearEquiv.apply_symm_apply]`.

Use function extensionality and compare the values at `i`. Rewrite using `[Pi.smul_apply, smul_eq_mul, ← hw i, mul_comm]`. Establish `e1 : (O' ⧸ P.restrictScalars O) ≃ₗ[O] (O' ⧸ P)` using `Submodule.Quotient.restrictScalarsEquiv O P`. Establish `e2 : (O' ⧸ P.restrictScalars O) ≃ₗ[O] ((ι → O) ⧸ Q)` using `Submodule.Quotient.equiv _ _ bO.equivFun hPQ`. Establish `e3 : ((ι → O) ⧸ Q) ≃ₗ[O] (ι → O ⧸ Ideal.span {a})` using `Submodule.quotientPi _`.

Establish `h1` using `(e1.symm.trans (e2.trans e3)).length_eq`. Rewrite `h1` using `[Module.length_pi, ENat.card_eq_coe_fintype_card]`. Conclude with `h1`.
-/
theorem length_quot_free {ι : Type} [Fintype ι] (bO : Module.Basis ι O O') (a : O) :
    Module.length O (O' ⧸ Ideal.span {algebraMap O O' a}) =
      Fintype.card ι * Module.length O (O ⧸ Ideal.span {a}) := by
  let P : Submodule O' O' := Ideal.span {algebraMap O O' a}
  let Q : Submodule O (ι → O) := Submodule.pi Set.univ fun _ => Ideal.span {a}
  have hPQ : (P.restrictScalars O).map (bO.equivFun : O' →ₗ[O] (ι → O)) = Q := by
    ext y
    simp only [Submodule.mem_map, Submodule.restrictScalars_mem, Q, Submodule.mem_pi,
      Set.mem_univ, true_implies, P, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨x, ⟨z, rfl⟩, rfl⟩ i
      refine ⟨bO.equivFun z i, ?_⟩
      have : z * algebraMap O O' a = a • z := by rw [Algebra.smul_def, mul_comm]
      rw [this, LinearEquiv.coe_coe, map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]
    · intro hy
      choose w hw using hy
      refine ⟨bO.equivFun.symm w * algebraMap O O' a, ⟨_, rfl⟩, ?_⟩
      have : bO.equivFun.symm w * algebraMap O O' a = a • bO.equivFun.symm w := by
        rw [Algebra.smul_def, mul_comm]
      rw [this, LinearEquiv.coe_coe, map_smul, LinearEquiv.apply_symm_apply]
      funext i
      rw [Pi.smul_apply, smul_eq_mul, ← hw i, mul_comm]
  have e1 : (O' ⧸ P.restrictScalars O) ≃ₗ[O] (O' ⧸ P) := Submodule.Quotient.restrictScalarsEquiv O P
  have e2 : (O' ⧸ P.restrictScalars O) ≃ₗ[O] ((ι → O) ⧸ Q) :=
    Submodule.Quotient.equiv _ _ bO.equivFun hPQ
  have e3 : ((ι → O) ⧸ Q) ≃ₗ[O] (ι → O ⧸ Ideal.span {a}) := Submodule.quotientPi _
  have h1 := (e1.symm.trans (e2.trans e3)).length_eq
  rw [Module.length_pi, ENat.card_eq_coe_fintype_card] at h1
  exact h1

end Len

/- English proof (translation)
Take `⟨k, rfl⟩` from `ENat.ne_top_iff_exists.1 hK`. Establish `hn0 : (n : ℕ∞) ≠ 0` using `by exact_mod_cast hn.ne'`. Break down `Nat.eq_zero_or_pos k' with h0 | hpos` into its components or cases. Substitute `h0` using the available equality. Establish `hm : mm' = 0`.

Establish `h` using `hx`. Simplify using `at h`. Conclude with `h` after adjusting the coercions. Substitute `hm` using the available equality. Simplify using `only [Nat.cast_zero, mul_zero, nonpos_iff_eq_zero, mul_eq_zero] at A B`.

Establish `hL : Lq = 0` using `A.resolve_left hn0`. Establish `hk0 : (k : ℕ∞) = 0` using `(mul_eq_zero.1 B.symm).resolve_left hn0`. Use `⟨0, 0, by rw [hL]; rfl, by rw [hk0]; rfl, by simp⟩` and prove the remaining obligations. Establish `hf : f ≠ ⊤`. Introduce `hft`.

Rewrite `B` using `[hft, ENat.top_mul (by exact_mod_cast hpos.ne')]`. Conclude with `ENat.coe_ne_top _ (by exact_mod_cast B.symm)`. Take `⟨f0, rfl⟩` from `ENat.ne_top_iff_exists.1 hf`. Establish `hL : Lq ≠ ⊤`. Introduce `hLt`.

Rewrite `A` using `[hLt, ENat.mul_top hn0]`. Conclude with `ENat.coe_ne_top _ (top_le_iff.1 (by exact_mod_cast A))`. Take `⟨mm, rfl⟩` from `ENat.ne_top_iff_exists.1 hL`. Establish `A' : n * mm ≤ f0 * mm'` using `by exact_mod_cast A`. Establish `B' : f0 * k' = n * k` using `by exact_mod_cast B`.

Use `⟨mm, k, rfl, rfl, ?_⟩` and prove the remaining obligations. Establish `A'' : (n : ℝ) * mm ≤ f0 * mm'` using `by exact_mod_cast A'`. Establish `B'' : (f0 : ℝ) * k' = n * k` using `by exact_mod_cast B'`. Establish `hn' : (0 : ℝ) < n` using `by exact_mod_cast hn`. Establish `: (n : ℝ) * mm ≤ n * (x * k)`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `le_of_mul_le_mul_left this hn'`.
-/
theorem col_arith (n mm' k' : ℕ) (f Lq K : ℕ∞) (x : ℝ) (hn : 0 < n) (hK : K ≠ ⊤)
    (A : (n : ℕ∞) * Lq ≤ f * mm') (B : f * k' = n * K) (hx : (mm' : ℝ) ≤ x * k') :
    ∃ mm k : ℕ, Lq = mm ∧ K = k ∧ (mm : ℝ) ≤ x * k := by
  obtain ⟨k, rfl⟩ := ENat.ne_top_iff_exists.1 hK
  have hn0 : (n : ℕ∞) ≠ 0 := by exact_mod_cast hn.ne'
  rcases Nat.eq_zero_or_pos k' with h0 | hpos
  · subst h0
    have hm : mm' = 0 := by
      have h := hx
      simp at h
      exact_mod_cast h
    subst hm
    simp only [Nat.cast_zero, mul_zero, nonpos_iff_eq_zero, mul_eq_zero] at A B
    have hL : Lq = 0 := A.resolve_left hn0
    have hk0 : (k : ℕ∞) = 0 := (mul_eq_zero.1 B.symm).resolve_left hn0
    refine ⟨0, 0, by rw [hL]; rfl, by rw [hk0]; rfl, by simp⟩
  · have hf : f ≠ ⊤ := by
      intro hft
      rw [hft, ENat.top_mul (by exact_mod_cast hpos.ne')] at B
      exact ENat.coe_ne_top _ (by exact_mod_cast B.symm)
    obtain ⟨f0, rfl⟩ := ENat.ne_top_iff_exists.1 hf
    have hL : Lq ≠ ⊤ := by
      intro hLt
      rw [hLt, ENat.mul_top hn0] at A
      exact ENat.coe_ne_top _ (top_le_iff.1 (by exact_mod_cast A))
    obtain ⟨mm, rfl⟩ := ENat.ne_top_iff_exists.1 hL
    have A' : n * mm ≤ f0 * mm' := by exact_mod_cast A
    have B' : f0 * k' = n * k := by exact_mod_cast B
    refine ⟨mm, k, rfl, rfl, ?_⟩
    have A'' : (n : ℝ) * mm ≤ f0 * mm' := by exact_mod_cast A'
    have B'' : (f0 : ℝ) * k' = n * k := by exact_mod_cast B'
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have : (n : ℝ) * mm ≤ n * (x * k) :=
      calc (n : ℝ) * mm ≤ f0 * mm' := A''
        _ ≤ f0 * (x * k') := mul_le_mul_of_nonneg_left hx (by positivity)
        _ = x * (f0 * k') := by ring
        _ = n * (x * k) := by rw [B'']; ring
    exact le_of_mul_le_mul_left this hn'

section Proj

variable {G : Type} [Group G] {LL LL' : Type} [Field LL] [Field LL'] [Algebra LL LL']

def prj (φ : LL' →ₗ[LL] LL) (V : Type) [AddCommGroup V] [Module LL V] : LL' ⊗[LL] V →ₗ[LL] V :=
  (TensorProduct.lid LL V).toLinearMap ∘ₗ LinearMap.rTensor V φ

/- English proof (translation)
Simplify using `[prj]`.
-/
theorem prj_tmul (φ : LL' →ₗ[LL] LL) {V : Type} [AddCommGroup V] [Module LL V] (a : LL') (v : V) :
    prj φ V (a ⊗ₜ[LL] v) = φ a • v := by
  simp [prj]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a v => rw [bρ_tmul, prj_tmul, prj_tmul, map_smul]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]`.
-/
theorem prj_bρ (φ : LL' →ₗ[LL] LL) {V : Type} [AddCommGroup V] [Module LL V]
    (ρ : Representation LL G V) (g : G) (x : LL' ⊗[LL] V) :
    prj φ V (bρ LL' ρ g x) = ρ g (prj φ V x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a v => rw [bρ_tmul, prj_tmul, prj_tmul, map_smul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a v => simp [bf, prj_tmul]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]`.
-/
theorem prj_bf (φ : LL' →ₗ[LL] LL) {V V₂ : Type} [AddCommGroup V] [Module LL V] [AddCommGroup V₂]
    [Module LL V₂] (f : V →ₗ[LL] V₂) (x : LL' ⊗[LL] V) :
    prj φ V₂ (bf (LL' := LL') f x) = f (prj φ V x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a v => simp [bf, prj_tmul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

end Proj

section Coord

variable {LL LL' O O' : Type} [Field LL] [Field LL'] [Algebra LL LL'] [CommRing O] [Algebra O LL]
  [CommRing O'] [Algebra O' LL'] [Algebra O O'] [Algebra O LL'] [IsScalarTower O O' LL']
  [IsScalarTower O LL LL'] {ι : Type} [Fintype ι]

/- English proof (translation)
Establish `e : algebraMap O' LL' o = bL.equivFun.symm (fun i => algebraMap O LL (bO.repr o i))`. Rewrite using `[Module.Basis.equivFun_symm_apply]`. Use `conv_lhs => rw [← bO.sum_repr o]`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[hb, Algebra.smul_def, map_mul, Algebra.smul_def, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]`. Rewrite using `[e, Module.Basis.coord_apply, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]`.
-/
theorem coord_alg (bO : Module.Basis ι O O') (bL : Module.Basis ι LL LL')
    (hb : ∀ i, bL i = algebraMap O' LL' (bO i)) (o : O') (k : ι) :
    bL.coord k (algebraMap O' LL' o) = algebraMap O LL (bO.repr o k) := by
  have e : algebraMap O' LL' o = bL.equivFun.symm (fun i => algebraMap O LL (bO.repr o i)) := by
    rw [Module.Basis.equivFun_symm_apply]
    conv_lhs => rw [← bO.sum_repr o]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hb, Algebra.smul_def, map_mul, Algebra.smul_def, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply]
  rw [e, Module.Basis.coord_apply, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]

/- English proof (translation)
Rewrite using `[Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]`.
-/
theorem coord_basis (bL : Module.Basis ι LL LL') (i k : ι) :
    bL.coord k (bL i) = if i = k then 1 else 0 := by
  rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]

/- English proof (translation)
It suffices to establish `h : ∀ c : O', prj (bL.coord k) V (c • x) ∈ T by simpa using h 1`. Use `Submodule.span_induction (fun y hy => ?_) (fun c => by simp) (fun a b _ _ ha hb c => ?_) (fun c a _ ha c' => ?_) hx` and prove the remaining obligations. Take `⟨t, rfl⟩` from `hy`. Introduce `c`. Rewrite using `[TensorProduct.smul_tmul', prj_tmul, Algebra.smul_def, mul_one, coord_alg bO bL hb, algebraMap_smul]`.

Conclude with `T.smul_mem _ t.2`. Rewrite using `[smul_add, map_add]`. Conclude with `T.add_mem (ha c) (hb c)`. Rewrite using `[smul_smul]`. Conclude with `ha _`.
-/
theorem prj_bT (bO : Module.Basis ι O O') (bL : Module.Basis ι LL LL')
    (hb : ∀ i, bL i = algebraMap O' LL' (bO i)) (k : ι) {V : Type} [AddCommGroup V] [Module LL V]
    [Module O V] [IsScalarTower O LL V] (T : Submodule O V) (x : LL' ⊗[LL] V)
    (hx : x ∈ bT (LL' := LL') (O' := O') T) : prj (bL.coord k) V x ∈ T := by
  suffices h : ∀ c : O', prj (bL.coord k) V (c • x) ∈ T by simpa using h 1
  refine Submodule.span_induction (fun y hy => ?_) (fun c => by simp) (fun a b _ _ ha hb c => ?_)
    (fun c a _ ha c' => ?_) hx
  · obtain ⟨t, rfl⟩ := hy
    intro c
    rw [TensorProduct.smul_tmul', prj_tmul, Algebra.smul_def, mul_one, coord_alg bO bL hb,
      algebraMap_smul]
    exact T.smul_mem _ t.2
  · rw [smul_add, map_add]; exact T.add_mem (ha c) (hb c)
  · rw [smul_smul]; exact ha _

/- English proof (translation)
Rewrite using `[TensorProduct.smul_tmul', prj_tmul, Algebra.smul_def, mul_one, ← hb, coord_basis]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem prj_smul_one (bO : Module.Basis ι O O') (bL : Module.Basis ι LL LL')
    (hb : ∀ i, bL i = algebraMap O' LL' (bO i)) {V : Type} [AddCommGroup V] [Module LL V]
    (i k : ι) (v : V) :
    prj (bL.coord k) V ((bO i) • ((1 : LL') ⊗ₜ[LL] v)) = if i = k then v else 0 := by
  rw [TensorProduct.smul_tmul', prj_tmul, Algebra.smul_def, mul_one, ← hb, coord_basis]
  split_ifs <;> simp

end Coord

section Gen

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL LL' : Type} [Field LL] [Field LL']
    [Algebra Qp LL] [Algebra Qp LL'] [Algebra LL LL'] [IsScalarTower Qp LL LL']
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

variable (LL') in

def mJ : V ⊗[Qp] B →ₗ[Qp] (LL' ⊗[LL] V) ⊗[Qp] B :=
  TensorProduct.map ((TensorProduct.mk LL LL' V 1).restrictScalars Qp) LinearMap.id

def mP (φ : LL' →ₗ[LL] LL) : (LL' ⊗[LL] V) ⊗[Qp] B →ₗ[Qp] V ⊗[Qp] B :=
  TensorProduct.map ((prj φ V).restrictScalars Qp) LinearMap.id

/- English proof (translation)
Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v b => simp [mJ, actVB, bρ_tmul]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]`.
-/
theorem mJ_act (ρ : Representation LL G V) (g : G) (y : V ⊗[Qp] B) :
    mJ (B := B) LL' (actVB PD ρ g y) = actVB PD (bρ LL' ρ) g (mJ LL' y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [mJ, actVB, bρ_tmul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

/- English proof (translation)
Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v b => simp [mP, actVB, prj_bρ]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]`.
-/
theorem mapPoint_act (φ : LL' →ₗ[LL] LL) (ρ : Representation LL G V) (g : G) (y : (LL' ⊗[LL] V) ⊗[Qp] B) :
    mP (B := B) φ (actVB PD (bρ LL' ρ) g y) = actVB PD ρ g (mP φ y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [mP, actVB, prj_bρ]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

/- English proof (translation)
Establish `h1` using `congrArg (mJ (LL := LL) (B := B) LL') h`. Rewrite `h1` using `[map_sub, mJ_act]`. Conclude with `h1`.
-/
theorem mJ_eq (ρ : Representation LL G V) (g : G) (v : V) (x : V ⊗[Qp] B)
    (h : v ⊗ₜ[Qp] (1 : B) = actVB PD ρ g x - x) :
    ((1 : LL') ⊗ₜ[LL] v) ⊗ₜ[Qp] (1 : B) =
      actVB PD (bρ LL' ρ) g (mJ (LL := LL) (B := B) LL' x) - mJ (LL := LL) (B := B) LL' x := by
  have h1 := congrArg (mJ (LL := LL) (B := B) LL') h
  rw [map_sub, mJ_act] at h1
  exact h1

/- English proof (translation)
Establish `h1` using `congrArg (mP (B := B) φ) h`. Rewrite `h1` using `[map_sub, mapPoint_act]`. Conclude with `h1`.
-/
theorem mP_eq (φ : LL' →ₗ[LL] LL) (ρ : Representation LL G V) (g : G) (u : LL' ⊗[LL] V)
    (x : (LL' ⊗[LL] V) ⊗[Qp] B) (h : u ⊗ₜ[Qp] (1 : B) = actVB PD (bρ LL' ρ) g x - x) :
    prj φ V u ⊗ₜ[Qp] (1 : B) = actVB PD ρ g (mP φ x) - mP φ x := by
  have h1 := congrArg (mP (B := B) φ) h
  rw [map_sub, mapPoint_act] at h1
  exact h1

/- English proof (translation)
Rewrite using `[map_add, prj_bρ]`.
-/
theorem prj_coc (φ : LL' →ₗ[LL] LL) (ρ : Representation LL G V) (g : G) (a b : LL' ⊗[LL] V) :
    prj φ V (a + bρ LL' ρ g b) = prj φ V a + ρ g (prj φ V b) := by
  rw [map_add, prj_bρ]

/- English proof (translation)
Rewrite using `[map_add, map_sub, prj_bf, prj_bρ]`.
-/
theorem core_eq (φ : LL' →ₗ[LL] LL) {V₂ : Type} [AddCommGroup V₂] [Module LL V₂] (f : V →ₗ[LL] V₂)
    (ρ₂ : Representation LL G V₂) (g : G) (a : LL' ⊗[LL] V) (t : LL' ⊗[LL] V₂) :
    prj φ V₂ (bf (LL' := LL') f a + (bρ LL' ρ₂ g t - t)) =
      f (prj φ V a) + (ρ₂ g (prj φ V₂ t) - prj φ V₂ t) := by
  rw [map_add, map_sub, prj_bf, prj_bρ]

/- English proof (translation)
Simplify using `[bf, bρ_tmul, TensorProduct.tmul_add, TensorProduct.tmul_sub]`.
-/
theorem jp_eq {V₂ : Type} [AddCommGroup V₂] [Module LL V₂] (f : V →ₗ[LL] V₂)
    (ρ₂ : Representation LL G V₂) (g : G) (a : V) (t : V₂) :
    bf (LL' := LL') f ((1 : LL') ⊗ₜ[LL] a) +
        (bρ LL' ρ₂ g ((1 : LL') ⊗ₜ[LL] t) - (1 : LL') ⊗ₜ[LL] t) =
      (1 : LL') ⊗ₜ[LL] (f a + (ρ₂ g t - t)) := by
  simp [bf, bρ_tmul, TensorProduct.tmul_add, TensorProduct.tmul_sub]

end Gen

section Coc

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL LL' O O' : Type} [Field LL] [Field LL']
    [Algebra Qp LL] [Algebra Qp LL'] [Algebra LL LL'] [IsScalarTower Qp LL LL']
    [TopologicalSpace LL] [TopologicalSpace LL'] [IsTopologicalRing LL'] [CommRing O] [IsDomain O]
    [Algebra O LL] [IsFractionRing O LL] [CommRing O'] [Algebra O' LL'] [Algebra O O'] [Algebra O LL']
    [IsScalarTower O O' LL'] [IsScalarTower O LL LL']

variable (hc : Continuous (algebraMap LL LL')) (hO' : Function.Injective (algebraMap O' LL'))

def jp (T : LocLat G Qp LL O) (c : G → T.V) : G → (bLoc (O' := O') hc hO' T).V :=
  fun g => ((1 : LL') ⊗ₜ[LL] c g : LL' ⊗[LL] T.V)

def jv (T : LocLat G Qp LL O) (v : T.V) : (bLoc (O' := O') hc hO' T).V := (1 : LL') ⊗ₜ[LL] v

/- English proof (translation)
Use `letI : TopologicalSpace (LL' ⊗[LL] T.V) := bTop (LL := LL) (LL' := LL') T.V`. Use `haveI : IsModuleTopology LL' (LL' ⊗[LL] T.V) := bIsMod (LL := LL) (LL' := LL') T.V`. Use `haveI : ContinuousAdd (LL' ⊗[LL] T.V) := IsModuleTopology.toContinuousAdd LL' _`. Use `haveI : ContinuousSMul LL' (LL' ⊗[LL] T.V) := IsModuleTopology.toContinuousSMul LL' _`. Use `haveI : ContinuousSMul LL (LL' ⊗[LL] T.V) := contSMul_of hc _`.

Conclude with `IsModuleTopology.continuous_of_linearMap (TensorProduct.mk LL LL' T.V 1)`.
-/
theorem cont_j (T : LocLat G Qp LL O) : Continuous (jv (O' := O') hc hO' T) := by
  letI : TopologicalSpace (LL' ⊗[LL] T.V) := bTop (LL := LL) (LL' := LL') T.V
  haveI : IsModuleTopology LL' (LL' ⊗[LL] T.V) := bIsMod (LL := LL) (LL' := LL') T.V
  haveI : ContinuousAdd (LL' ⊗[LL] T.V) := IsModuleTopology.toContinuousAdd LL' _
  haveI : ContinuousSMul LL' (LL' ⊗[LL] T.V) := IsModuleTopology.toContinuousSMul LL' _
  haveI : ContinuousSMul LL (LL' ⊗[LL] T.V) := contSMul_of hc _
  exact IsModuleTopology.continuous_of_linearMap (TensorProduct.mk LL LL' T.V 1)

/- English proof (translation)
Take `⟨⟨⟨hcont, hcoc⟩, hT⟩, _, x, hx⟩` from `h`. Establish `hC : Continuous (jp (O'` using `O') hc hO' T c) := (cont_j hc hO' T).comp hcont`. Establish `hK : ∀ g h, jp (O'` using `O') hc hO' T c (g * h) = jp (O' := O') hc hO' T c g + (bLoc (O' := O') hc hO' T).ρ g (jp (O' := O') hc hO' T c h) := by`. Introduce `g h`. Use `show (1 : LL') ⊗ₜ[LL] c (g * h) = (1 : LL') ⊗ₜ[LL] c g + bρ LL' T.ρ g ((1 : LL') ⊗ₜ[LL] c h)`.

Rewrite using `[hcoc, TensorProduct.tmul_add, bρ_tmul]`. Establish `hM : ∀ g, jp (O'` using `O') hc hO' T c g ∈ (bLoc (O' := O') hc hO' T).L.T := by`. Introduce `g`. Use `show ((1 : LL') ⊗ₜ[LL] c g : LL' ⊗[LL] T.V) ∈ bT (LL' := LL') (O' := O') T.L.T`. Conclude with `Submodule.subset_span ⟨⟨c g, hT g (Set.mem_univ g)⟩, rfl⟩`.

Conclude with `⟨⟨⟨hC, hK⟩, fun g _ => hM g⟩, ⟨hC, hK⟩, mJ (B := B) LL' x, fun g => mJ_eq PD T.ρ g (c g) x (hx g)⟩`.
-/
theorem jp_mem (T : LocLat G Qp LL O) (c : G → T.V) (h : c ∈ latticeFiniteCocycles PD T.L) :
    jp (O' := O') hc hO' T c ∈ latticeFiniteCocycles PD (bLoc (O' := O') hc hO' T).L := by
  obtain ⟨⟨⟨hcont, hcoc⟩, hT⟩, _, x, hx⟩ := h
  have hC : Continuous (jp (O' := O') hc hO' T c) := (cont_j hc hO' T).comp hcont
  have hK : ∀ g h, jp (O' := O') hc hO' T c (g * h) =
      jp (O' := O') hc hO' T c g + (bLoc (O' := O') hc hO' T).ρ g (jp (O' := O') hc hO' T c h) := by
    intro g h
    show (1 : LL') ⊗ₜ[LL] c (g * h) = (1 : LL') ⊗ₜ[LL] c g + bρ LL' T.ρ g ((1 : LL') ⊗ₜ[LL] c h)
    rw [hcoc, TensorProduct.tmul_add, bρ_tmul]
  have hM : ∀ g, jp (O' := O') hc hO' T c g ∈ (bLoc (O' := O') hc hO' T).L.T := by
    intro g
    show ((1 : LL') ⊗ₜ[LL] c g : LL' ⊗[LL] T.V) ∈ bT (LL' := LL') (O' := O') T.L.T
    exact Submodule.subset_span ⟨⟨c g, hT g (Set.mem_univ g)⟩, rfl⟩
  exact ⟨⟨⟨hC, hK⟩, fun g _ => hM g⟩, ⟨hC, hK⟩,
    mJ (B := B) LL' x, fun g => mJ_eq PD T.ρ g (c g) x (hx g)⟩

variable {ι : Type} [Fintype ι] (bO : Module.Basis ι O O') (bL : Module.Basis ι LL LL')
    (hb : ∀ i, bL i = algebraMap O' LL' (bO i)) (hlin : ∀ φ : LL' →ₗ[LL] LL, Continuous φ)

include hlin in
/- English proof (translation)
Use `letI : TopologicalSpace (LL' ⊗[LL] T.V) := bTop (LL := LL) (LL' := LL') T.V`. Use `haveI : IsModuleTopology LL' (LL' ⊗[LL] T.V) := bIsMod (LL := LL) (LL' := LL') T.V`. Use `haveI : ContinuousSMul LL T.V := IsModuleTopology.toContinuousSMul LL T.V`. Set `e` to `Module.finBasis LL T.V`. Set `e'` to `Algebra.TensorProduct.basis LL' e`.

Establish `key : ∀ x : LL' ⊗[LL] T.V, prj φ T.V x = ∑ j, φ (e'.coord j x) • e j`. Introduce `x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a v`.

Rewrite using `[prj_tmul]`. Establish `h1 : ∀ j, φ (e'.coord j (a ⊗ₜ[LL] v)) = e.repr v j * φ a`. Introduce `j`. Rewrite using `[Module.Basis.coord_apply, Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Finset.smul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[h1 j, mul_comm, mul_smul]`. Consider the case `add x y hx hy`. Rewrite using `[map_add, hx, hy, ← Finset.sum_add_distrib]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_add, map_add, add_smul]`. Establish `hcj : ∀ j, Continuous (fun x : LL' ⊗[LL] T.V => e'.coord j x)` using `fun j => IsModuleTopology.continuous_of_linearMap (e'.coord j)`. Establish `: (fun x : LL' ⊗[LL] T.V => prj φ T.V x) = fun x => ∑ j, φ (e'.coord j x) • e j` using `funext key`. Use `show Continuous (fun x : LL' ⊗[LL] T.V => prj φ T.V x)`.

Rewrite using `[this]`. Conclude with `continuous_finsetSum _ fun j _ => ((hlin φ).comp (hcj j)).smul continuous_const`.
-/
theorem cont_prj (T : LocLat G Qp LL O) (φ : LL' →ₗ[LL] LL) :
    Continuous (fun x : (bLoc (O' := O') hc hO' T).V => prj φ T.V x) := by
  letI : TopologicalSpace (LL' ⊗[LL] T.V) := bTop (LL := LL) (LL' := LL') T.V
  haveI : IsModuleTopology LL' (LL' ⊗[LL] T.V) := bIsMod (LL := LL) (LL' := LL') T.V
  haveI : ContinuousSMul LL T.V := IsModuleTopology.toContinuousSMul LL T.V
  let e := Module.finBasis LL T.V
  let e' := Algebra.TensorProduct.basis LL' e
  have key : ∀ x : LL' ⊗[LL] T.V, prj φ T.V x = ∑ j, φ (e'.coord j x) • e j := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a v =>
      rw [prj_tmul]
      have h1 : ∀ j, φ (e'.coord j (a ⊗ₜ[LL] v)) = e.repr v j * φ a := by
        intro j
        rw [Module.Basis.coord_apply, Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply,
          Finsupp.mapRange_apply, smul_eq_mul, mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul]
      calc φ a • v = φ a • ∑ j, e.repr v j • e j := by rw [e.sum_repr]
        _ = ∑ j, φ (e'.coord j (a ⊗ₜ[LL] v)) • e j := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [h1 j, mul_comm, mul_smul]
    | add x y hx hy =>
      rw [map_add, hx, hy, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_add, map_add, add_smul]
  have hcj : ∀ j, Continuous (fun x : LL' ⊗[LL] T.V => e'.coord j x) := fun j =>
    IsModuleTopology.continuous_of_linearMap (e'.coord j)
  have : (fun x : LL' ⊗[LL] T.V => prj φ T.V x) = fun x => ∑ j, φ (e'.coord j x) • e j := funext key
  show Continuous (fun x : LL' ⊗[LL] T.V => prj φ T.V x)
  rw [this]
  exact continuous_finsetSum _ fun j _ => ((hlin φ).comp (hcj j)).smul continuous_const

include hb hlin in
/- English proof (translation)
Take `⟨⟨⟨hcont, hcoc⟩, hT⟩, _, x, hx⟩` from `h`. Establish `hC : Continuous (fun g => prj (bL.coord k) T.V (d g))` using `(cont_prj hc hO' hlin T (bL.coord k)).comp hcont`. Establish `hK : ∀ g h, prj (bL.coord k) T.V (d (g * h)) = prj (bL.coord k) T.V (d g) + T.ρ g (prj (bL.coord k) T.V (d h))`. Introduce `g h`. Conclude with `(congrArg (prj (bL.coord k) T.V) (hcoc g h)).trans (prj_coc _ T.ρ g (d g) (d h))`.

Conclude with `⟨⟨⟨hC, hK⟩, fun g _ => prj_bT bO bL hb k T.L.T (d g) (hT g (Set.mem_univ g))⟩, ⟨hC, hK⟩, mP (B := B) (bL.coord k) x, fun g => mP_eq PD (bL.coord k) T.ρ g (d g) x (hx g)⟩`.
-/
theorem prj_mem (T : LocLat G Qp LL O) (k : ι) (d : G → (bLoc (O' := O') hc hO' T).V)
    (h : d ∈ latticeFiniteCocycles PD (bLoc (O' := O') hc hO' T).L) :
    (fun g => prj (bL.coord k) T.V (d g)) ∈ latticeFiniteCocycles PD T.L := by
  obtain ⟨⟨⟨hcont, hcoc⟩, hT⟩, _, x, hx⟩ := h
  have hC : Continuous (fun g => prj (bL.coord k) T.V (d g)) :=
    (cont_prj hc hO' hlin T (bL.coord k)).comp hcont
  have hK : ∀ g h, prj (bL.coord k) T.V (d (g * h)) =
      prj (bL.coord k) T.V (d g) + T.ρ g (prj (bL.coord k) T.V (d h)) := by
    intro g h
    exact (congrArg (prj (bL.coord k) T.V) (hcoc g h)).trans (prj_coc _ T.ρ g (d g) (d h))
  exact ⟨⟨⟨hC, hK⟩, fun g _ => prj_bT bO bL hb k T.L.T (d g) (hT g (Set.mem_univ g))⟩, ⟨hC, hK⟩,
    mP (B := B) (bL.coord k) x, fun g => mP_eq PD (bL.coord k) T.ρ g (d g) x (hx g)⟩

end Coc

/- English proof (translation)
Rewrite using `[map_sum]`. Repeatedly rewrite using `[prj_smul_one bO bL hb]`. Simplify using the standard rewrite rules.
-/
theorem sum_eq {LL LL' O O' : Type} [Field LL] [Field LL'] [Algebra LL LL'] [CommRing O]
    [Algebra O LL] [CommRing O'] [Algebra O' LL'] [Algebra O O'] [Algebra O LL']
    [IsScalarTower O O' LL'] [IsScalarTower O LL LL'] {ι : Type} [Fintype ι]
    (bO : Module.Basis ι O O') (bL : Module.Basis ι LL LL')
    (hb : ∀ i, bL i = algebraMap O' LL' (bO i)) {V : Type} [AddCommGroup V] [Module LL V]
    (c : ι → V) (k : ι) :
    prj (bL.coord k) V (∑ i, bO i • ((1 : LL') ⊗ₜ[LL] c i)) = c k := by
  rw [map_sum]
  simp_rw [prj_smul_one bO bL hb]
  simp

section Desc

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL LL' O O' : Type} [Field LL] [Field LL']
    [Algebra Qp LL] [Algebra Qp LL'] [Algebra LL LL'] [IsScalarTower Qp LL LL']
    [TopologicalSpace LL] [TopologicalSpace LL'] [IsTopologicalRing LL'] [CommRing O] [IsDomain O]
    [Algebra O LL] [IsFractionRing O LL] [CommRing O'] [Algebra O' LL'] [Algebra O O'] [Algebra O LL']
    [IsScalarTower O O' LL'] [IsScalarTower O LL LL']

variable (hc : Continuous (algebraMap LL LL')) (hO' : Function.Injective (algebraMap O' LL'))
    {ι : Type} [Fintype ι] (bO : Module.Basis ι O O') (bL : Module.Basis ι LL LL')
    (hb : ∀ i, bL i = algebraMap O' LL' (bO i)) (hlin : ∀ φ : LL' →ₗ[LL] LL, Continuous φ)

include hb hlin in

/- English proof (translation)
Take `⟨y, hy, z, hz, hyz⟩` from `Submodule.mem_sup.1 h`. Take `⟨d, hd, rfl⟩` from `Submodule.mem_map.1 hy`. Take `⟨t, ht, rfl⟩` from `Submodule.mem_map.1 hz`. Use `Submodule.mem_sup.2 ⟨F.post (fun g => prj (bL.coord k) T₁.V (d g)), Submodule.mem_map_of_mem (prj_mem PD hc hO' bO bL hb hlin T₁ k d hd), (cob T₂.ρ).restrictScalars O (prj (bL.coord k) T₂.V t), ⟨_, prj_bT bO bL hb k T₂.L.T t ht, rfl⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `g`.

Establish `e1` using `congrFun hyz g`. Rewrite `e1` using `[Pi.add_apply, Finset.sum_apply]`. Simplify using `only [Pi.smul_apply] at e1`. Establish `e2` using `congrArg (prj (bL.coord k) T₂.V) e1`. Use `show F.f (prj (bL.coord k) T₁.V (d g)) + (T₂.ρ g (prj (bL.coord k) T₂.V t) - prj (bL.coord k) T₂.V t) = c k g`.

Conclude with `(core_eq (bL.coord k) F.f T₂.ρ g (d g) t).symm.trans (e2.trans (sum_eq bO bL hb (fun i => c i g) k))`.
-/
theorem core (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (c : ι → G → T₂.V)
    (h : (∑ i, bO i • jp (O' := O') hc hO' T₂ (c i)) ∈ (bHom (O' := O') hc hO' F).ImF PD) (k : ι) :
    c k ∈ F.ImF PD := by
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 h
  obtain ⟨d, hd, rfl⟩ := Submodule.mem_map.1 hy
  obtain ⟨t, ht, rfl⟩ := Submodule.mem_map.1 hz
  refine Submodule.mem_sup.2 ⟨F.post (fun g => prj (bL.coord k) T₁.V (d g)),
    Submodule.mem_map_of_mem (prj_mem PD hc hO' bO bL hb hlin T₁ k d hd),
    (cob T₂.ρ).restrictScalars O (prj (bL.coord k) T₂.V t),
    ⟨_, prj_bT bO bL hb k T₂.L.T t ht, rfl⟩, ?_⟩
  funext g
  have e1 := congrFun hyz g
  rw [Pi.add_apply, Finset.sum_apply] at e1
  simp only [Pi.smul_apply] at e1
  have e2 := congrArg (prj (bL.coord k) T₂.V) e1
  show F.f (prj (bL.coord k) T₁.V (d g)) +
      (T₂.ρ g (prj (bL.coord k) T₂.V t) - prj (bL.coord k) T₂.V t) = c k g
  exact (core_eq (bL.coord k) F.f T₂.ρ g (d g) t).symm.trans
    (e2.trans (sum_eq bO bL hb (fun i => c i g) k))

/- English proof (translation)
Use function extensionality and compare the values at `g`. Use `show ((1 : LL') ⊗ₜ[LL] (0 : T.V) : LL' ⊗[LL] T.V) = 0`. Rewrite using `[TensorProduct.tmul_zero]`.
-/
theorem jp_zero (T : LocLat G Qp LL O) : jp (O' := O') hc hO' T 0 = 0 := by
  funext g
  show ((1 : LL') ⊗ₜ[LL] (0 : T.V) : LL' ⊗[LL] T.V) = 0
  rw [TensorProduct.tmul_zero]

/- English proof (translation)
Use function extensionality and compare the values at `g`. Use `show ((1 : LL') ⊗ₜ[LL] (a • c g) : LL' ⊗[LL] T.V) = (algebraMap O O' a) • ((1 : LL') ⊗ₜ[LL] c g)`. Rewrite using `[one_tmul_smul (O' := O')]`.
-/
theorem jp_smul (T : LocLat G Qp LL O) (a : O) (c : G → T.V) :
    jp (O' := O') hc hO' T (a • c) = (algebraMap O O' a) • jp (O' := O') hc hO' T c := by
  funext g
  show ((1 : LL') ⊗ₜ[LL] (a • c g) : LL' ⊗[LL] T.V) = (algebraMap O O' a) • ((1 : LL') ⊗ₜ[LL] c g)
  rw [one_tmul_smul (O' := O')]

/- English proof (translation)
Use `haveI : Nontrivial O' := by`. Use `⟨⟨0, 1, fun h0 => ?_⟩⟩` and prove the remaining obligations. Establish `h1` using `congrArg (algebraMap O' LL') h0`. Rewrite `h1` using `[map_zero, map_one]`. Conclude with `zero_ne_one h1`.

Conclude with `bO.index_nonempty`.
-/
theorem index_nonempty_of (bO : Module.Basis ι O O') (hO' : Function.Injective (algebraMap O' LL')) :
    Nonempty ι := by
  haveI : Nontrivial O' := by
    refine ⟨⟨0, 1, fun h0 => ?_⟩⟩
    have h1 := congrArg (algebraMap O' LL') h0
    rw [map_zero, map_one] at h1
    exact zero_ne_one h1
  exact bO.index_nonempty

include hb hlin in

/- English proof (translation)
Introduce `c hc2`. Take `⟨k⟩` from `index_nonempty_of (LL' := LL') bO hO'`. Establish `h1` using `h _ (jp_mem PD hc hO' T₂ c hc2)`. Establish `hs : (∑ i, bO i • jp (O'` using `O') hc hO' T₂ (if i = k then ((PD.p : O) ^ e) • c else 0)) = bO k • (((PD.p : O') ^ e) • jp (O' := O') hc hO' T₂ c) := by`. Rewrite using `[Finset.sum_eq_single k (fun i _ hik => by rw [if_neg hik, jp_zero, smul_zero]) (fun hk => absurd (Finset.mem_univ k) hk), if_pos rfl, jp_smul, map_pow, map_natCast]`.

Establish `h2` using `core PD hc hO' bO bL hb hlin T₁ T₂ F (fun i => if i = k then ((PD.p : O) ^ e) • c else 0) (by rw [hs]; exact Submodule.smul_mem _ _ h1) k`. Simplify using `using h2`.
-/
theorem descLift (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (e : ℕ)
    (h : (bHom (O' := O') hc hO' F).LiftF PD e) : F.LiftF PD e := by
  intro c hc2
  obtain ⟨k⟩ := index_nonempty_of (LL' := LL') bO hO'
  have h1 := h _ (jp_mem PD hc hO' T₂ c hc2)
  have hs : (∑ i, bO i • jp (O' := O') hc hO' T₂ (if i = k then ((PD.p : O) ^ e) • c else 0)) =
      bO k • (((PD.p : O') ^ e) • jp (O' := O') hc hO' T₂ c) := by
    rw [Finset.sum_eq_single k (fun i _ hik => by rw [if_neg hik, jp_zero, smul_zero])
      (fun hk => absurd (Finset.mem_univ k) hk), if_pos rfl, jp_smul, map_pow, map_natCast]
  have h2 := core PD hc hO' bO bL hb hlin T₁ T₂ F
    (fun i => if i = k then ((PD.p : O) ^ e) • c else 0) (by rw [hs]; exact Submodule.smul_mem _ _ h1) k
  simpa using h2

include hb hlin in

/- English proof (translation)
Take `⟨y, hy, z, hz, rfl⟩` from `Submodule.mem_sup.1 h`. Take `⟨d, hd, rfl⟩` from `Submodule.mem_map.1 hy`. Take `⟨t, ht, rfl⟩` from `Submodule.mem_map.1 hz`. Establish `hm : jv (O'` using `O') hc hO' T₂ t ∈ (bLoc (O' := O') hc hO' T₂).L.T := by show ((1 : LL') ⊗ₜ[LL] t : LL' ⊗[LL] T₂.V) ∈ bT (LL' := LL') (O' := O') T₂.L.T`. Conclude with `Submodule.subset_span ⟨⟨t, ht⟩, rfl⟩`.

Use `Submodule.mem_sup.2 ⟨(bHom (O' := O') hc hO' F).post (jp (O' := O') hc hO' T₁ d), Submodule.mem_map_of_mem (jp_mem PD hc hO' T₁ d hd), (cob (bLoc (O' := O') hc hO' T₂).ρ).restrictScalars O' (jv (O' := O') hc hO' T₂ t), ⟨_, hm, rfl⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `g`. Conclude with `jp_eq F.f T₂.ρ g (d g) t`.
-/
theorem jp_ImF (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (c : G → T₂.V) (h : c ∈ F.ImF PD) :
    jp (O' := O') hc hO' T₂ c ∈ (bHom (O' := O') hc hO' F).ImF PD := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 h
  obtain ⟨d, hd, rfl⟩ := Submodule.mem_map.1 hy
  obtain ⟨t, ht, rfl⟩ := Submodule.mem_map.1 hz
  have hm : jv (O' := O') hc hO' T₂ t ∈ (bLoc (O' := O') hc hO' T₂).L.T := by
    show ((1 : LL') ⊗ₜ[LL] t : LL' ⊗[LL] T₂.V) ∈ bT (LL' := LL') (O' := O') T₂.L.T
    exact Submodule.subset_span ⟨⟨t, ht⟩, rfl⟩
  refine Submodule.mem_sup.2 ⟨(bHom (O' := O') hc hO' F).post (jp (O' := O') hc hO' T₁ d),
    Submodule.mem_map_of_mem (jp_mem PD hc hO' T₁ d hd),
    (cob (bLoc (O' := O') hc hO' T₂).ρ).restrictScalars O' (jv (O' := O') hc hO' T₂ t), ⟨_, hm, rfl⟩, ?_⟩
  funext g
  exact jp_eq F.f T₂.ρ g (d g) t

/- English proof (translation)
Use function extensionality and compare the values at `g`. Use `show ((1 : LL') ⊗ₜ[LL] (a g + b g) : LL' ⊗[LL] T.V) = (1 : LL') ⊗ₜ[LL] a g + (1 : LL') ⊗ₜ[LL] b g`. Rewrite using `[TensorProduct.tmul_add]`.
-/
theorem jp_add (T : LocLat G Qp LL O) (a b : G → T.V) :
    jp (O' := O') hc hO' T (a + b) = jp (O' := O') hc hO' T a + jp (O' := O') hc hO' T b := by
  funext g
  show ((1 : LL') ⊗ₜ[LL] (a g + b g) : LL' ⊗[LL] T.V) = (1 : LL') ⊗ₜ[LL] a g + (1 : LL') ⊗ₜ[LL] b g
  rw [TensorProduct.tmul_add]

include hb hlin in

/- English proof (translation)
Take `⟨mm', k', hcol', hk', hx⟩` from `h`. Set `Z` to `latticeFiniteCocycles PD T₂.L`. Set `Z'` to `latticeFiniteCocycles PD (bLoc (O' := O') hc hO' T₂).L`. Set `N` to `(F.ImF PD).comap Z.subtype`. Set `N'` to `((bHom (O' := O') hc hO' F).ImF PD).comap Z'.subtype`.

Use `letI : Module O (Z' ⧸ N') := Module.compHom _ (algebraMap O O')`. Use `haveI : IsScalarTower O O' (Z' ⧸ N') := ⟨fun a b q => by show (a • b) • q = algebraMap O O' a • (b • q)`. Rewrite using `[Algebra.smul_def, mul_smul]⟩`. Establish `hjZ : ∀ z : Z, jp (O'` using `O') hc hO' T₂ z ∈ Z' := fun z => jp_mem PD hc hO' T₂ z z.2`. Set `jZ : Z →ₗ[O] (Z' ⧸ N')` to `{ toFun := fun z => N'.mkQ ⟨jp (O' := O') hc hO' T₂ z, hjZ z⟩ map_add' := fun a b => by`.

Rewrite using `[← map_add]`. Use `congr 1`. Use `ext1`. Conclude with `jp_add hc hO' T₂ a b`. Use the proof step `map_smul' := fun a z => by show N'.mkQ ⟨_, hjZ (a • z)⟩ = algebraMap O O' a • N'.mkQ ⟨_, hjZ z⟩`.

Rewrite using `[← map_smul]`. Use `congr 1`. Use `ext1`. Conclude with `jp_smul hc hO' T₂ a z }`. Set `ψ : (ι → Z) →ₗ[O] (Z' ⧸ N')` to `{ toFun := fun q => ∑ i, bO i • jZ (q i) map_add' := fun q r => by`.

Simplify using `only [Pi.add_apply, map_add, smul_add, Finset.sum_add_distrib]`. Use the proof step `map_smul' := fun a q => by`. Simplify using `only [Pi.smul_apply, map_smul, RingHom.id_apply]`. Rewrite using `[Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Use `show bO i • (algebraMap O O' a • jZ (q i)) = algebraMap O O' a • (bO i • jZ (q i))`. Rewrite using `[smul_smul, smul_smul, mul_comm] }`. Establish `hψ : ∀ q, ψ q = N'.mkQ (∑ i, bO i • (⟨jp (O'` using `O') hc hO' T₂ (q i), hjZ (q i)⟩ : Z')) := by`. Introduce `q`. Rewrite using `[map_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul]`. Both sides reduce to the same expression. Establish `hker : LinearMap.ker ψ = Submodule.pi Set.univ fun _ => N`. Use extensionality with `q`.

Simplify using `only [LinearMap.mem_ker, Submodule.mem_pi, Set.mem_univ, true_implies]`. Prove the components needed by the constructor for the conclusion. Introduce `h0 k`. Rewrite `h0` using `[hψ, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Establish `h1 : (∑ i, bO i • jp (O'` using `O') hc hO' T₂ (q i)) ∈ (bHom (O' := O') hc hO' F).ImF PD := by`.

Use `h0` as an intermediate fact. Simplify using `only [N', Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sum, Submodule.coe_smul] at this`. Conclude with `this`. Conclude with `core PD hc hO' bO bL hb hlin T₁ T₂ F (fun i => (q i : G → T₂.V)) h1 k`. Introduce `hq`.

Rewrite using `[hψ, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Use `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Conclude with `jp_ImF PD hc hO' bO bL hb hlin T₁ T₂ F _ (hq i)`. Establish `e0 : ((ι → Z) ⧸ LinearMap.ker ψ) ≃ₗ[O] ((ι → Z) ⧸ Submodule.pi Set.univ fun _ => N)` using `Submodule.quotEquivOfEq _ _ hker`. Establish `e2 : ((ι → Z) ⧸ Submodule.pi Set.univ fun _ => N) ≃ₗ[O] (ι → Z ⧸ N)` using `Submodule.quotientPi _`.

Establish `hA1 : Module.length O (ι → Z ⧸ N) = Module.length O (LinearMap.range ψ)` using `((e2.symm.trans e0.symm).trans ψ.quotKerEquivRange).length_eq`. Establish `hA2` using `Module.length_le_of_injective (LinearMap.range ψ).subtype Subtype.val_injective`. Rewrite `hA2` using `[← hA1, Module.length_pi, ENat.card_eq_coe_fintype_card]`. Establish `hA3 : Module.length O (Z' ⧸ N') = Module.length O (O' ⧸ IsLocalRing.maximalIdeal O') * mm'` using `length_restrict_nat (O := O) mm' (Z' ⧸ N') hcol'`. Establish `hB1 : Module.length O (O' ⧸ Ideal.span {((PD.p : ℕ) : O')}) = Module.length O (O' ⧸ IsLocalRing.maximalIdeal O') * k'` using `length_restrict_nat (O := O) k' _ hk'`.

Establish `hB2` using `length_quot_free (O' := O') bO ((PD.p : ℕ) : O)`. Rewrite `hB2` using `[map_natCast]`. Rewrite `hB1` using `[hB2]`. Rewrite `hA2` using `[hA3]`. Take `⟨mm, k, h1, h2, h3⟩` from `col_arith (Fintype.card ι) mm' k' (Module.length O (O' ⧸ IsLocalRing.maximalIdeal O')) (Module.length O (Z ⧸ N)) (lenOl PD (O := O)) x (Fintype.card_pos_iff.2 (index_nonempty_of (LL' := LL') bO hO')) hk hA2 hB1.symm hx`.

Conclude with `⟨mm, k, h1, h2, h3⟩`.
-/
theorem descCol [IsLocalRing O'] (hk : lenOl PD (O := O) ≠ ⊤) (T₁ T₂ : LocLat G Qp LL O)
    (F : LatHom T₁.L T₂.L) (x : ℝ) (h : Formalism.MainNotions.TruncatedSeriesCountingBounds.ColLeR PD (bHom (O' := O') hc hO' F) x) :
    Formalism.MainNotions.TruncatedSeriesCountingBounds.ColLeR PD F x := by
  obtain ⟨mm', k', hcol', hk', hx⟩ := h
  let Z := latticeFiniteCocycles PD T₂.L
  let Z' := latticeFiniteCocycles PD (bLoc (O' := O') hc hO' T₂).L
  let N := (F.ImF PD).comap Z.subtype
  let N' := ((bHom (O' := O') hc hO' F).ImF PD).comap Z'.subtype
  letI : Module O (Z' ⧸ N') := Module.compHom _ (algebraMap O O')
  haveI : IsScalarTower O O' (Z' ⧸ N') := ⟨fun a b q => by
    show (a • b) • q = algebraMap O O' a • (b • q)
    rw [Algebra.smul_def, mul_smul]⟩
  have hjZ : ∀ z : Z, jp (O' := O') hc hO' T₂ z ∈ Z' := fun z => jp_mem PD hc hO' T₂ z z.2
  let jZ : Z →ₗ[O] (Z' ⧸ N') :=
    { toFun := fun z => N'.mkQ ⟨jp (O' := O') hc hO' T₂ z, hjZ z⟩
      map_add' := fun a b => by
        rw [← map_add]
        congr 1
        ext1
        exact jp_add hc hO' T₂ a b
      map_smul' := fun a z => by
        show N'.mkQ ⟨_, hjZ (a • z)⟩ = algebraMap O O' a • N'.mkQ ⟨_, hjZ z⟩
        rw [← map_smul]
        congr 1
        ext1
        exact jp_smul hc hO' T₂ a z }
  let ψ : (ι → Z) →ₗ[O] (Z' ⧸ N') :=
    { toFun := fun q => ∑ i, bO i • jZ (q i)
      map_add' := fun q r => by
        simp only [Pi.add_apply, map_add, smul_add, Finset.sum_add_distrib]
      map_smul' := fun a q => by
        simp only [Pi.smul_apply, map_smul, RingHom.id_apply]
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        show bO i • (algebraMap O O' a • jZ (q i)) = algebraMap O O' a • (bO i • jZ (q i))
        rw [smul_smul, smul_smul, mul_comm] }
  have hψ : ∀ q, ψ q = N'.mkQ (∑ i, bO i • (⟨jp (O' := O') hc hO' T₂ (q i), hjZ (q i)⟩ : Z')) := by
    intro q
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]
    rfl
  have hker : LinearMap.ker ψ = Submodule.pi Set.univ fun _ => N := by
    ext q
    simp only [LinearMap.mem_ker, Submodule.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro h0 k
      rw [hψ, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0
      have h1 : (∑ i, bO i • jp (O' := O') hc hO' T₂ (q i)) ∈ (bHom (O' := O') hc hO' F).ImF PD := by
        have := h0
        simp only [N', Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sum,
          Submodule.coe_smul] at this
        exact this
      exact core PD hc hO' bO bL hb hlin T₁ T₂ F (fun i => (q i : G → T₂.V)) h1 k
    · intro hq
      rw [hψ, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
      exact jp_ImF PD hc hO' bO bL hb hlin T₁ T₂ F _ (hq i)
  have e0 : ((ι → Z) ⧸ LinearMap.ker ψ) ≃ₗ[O] ((ι → Z) ⧸ Submodule.pi Set.univ fun _ => N) :=
    Submodule.quotEquivOfEq _ _ hker
  have e2 : ((ι → Z) ⧸ Submodule.pi Set.univ fun _ => N) ≃ₗ[O] (ι → Z ⧸ N) := Submodule.quotientPi _
  have hA1 : Module.length O (ι → Z ⧸ N) = Module.length O (LinearMap.range ψ) :=
    ((e2.symm.trans e0.symm).trans ψ.quotKerEquivRange).length_eq
  have hA2 := Module.length_le_of_injective (LinearMap.range ψ).subtype Subtype.val_injective
  rw [← hA1, Module.length_pi, ENat.card_eq_coe_fintype_card] at hA2
  have hA3 : Module.length O (Z' ⧸ N') =
      Module.length O (O' ⧸ IsLocalRing.maximalIdeal O') * mm' :=
    length_restrict_nat (O := O) mm' (Z' ⧸ N') hcol'
  have hB1 : Module.length O (O' ⧸ Ideal.span {((PD.p : ℕ) : O')}) =
      Module.length O (O' ⧸ IsLocalRing.maximalIdeal O') * k' :=
    length_restrict_nat (O := O) k' _ hk'
  have hB2 := length_quot_free (O' := O') bO ((PD.p : ℕ) : O)
  rw [map_natCast] at hB2
  rw [hB2] at hB1
  rw [hA3] at hA2
  obtain ⟨mm, k, h1, h2, h3⟩ := col_arith (Fintype.card ι) mm' k'
    (Module.length O (O' ⧸ IsLocalRing.maximalIdeal O')) (Module.length O (Z ⧸ N))
    (lenOl PD (O := O)) x (Fintype.card_pos_iff.2 (index_nonempty_of (LL' := LL') bO hO')) hk hA2
    hB1.symm hx
  exact ⟨mm, k, h1, h2, h3⟩

include hb hlin in

/- English proof (translation)
Introduce `T₁ T₂ F _ _ _ e h` and use `descLift PD hc hO' bO bL hb hlin T₁ T₂ F e h`.
-/
theorem descLift_at : ∀ (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L), Formalism.MainNotions.WachCoordinates.CrysLat PD T₁ →
    Formalism.MainNotions.WachCoordinates.CrysLat PD T₂ → F.Onto → ∀ e, (bHom (O' := O') hc hO' F).LiftF PD e → F.LiftF PD e :=
  fun T₁ T₂ F _ _ _ e h => descLift PD hc hO' bO bL hb hlin T₁ T₂ F e h

include hb hlin in

/- English proof (translation)
Introduce `T₁ T₂ F _ _ _ x h` and use `descCol PD hc hO' bO bL hb hlin hk T₁ T₂ F x h`.
-/
theorem descCol_at [IsLocalRing O'] (hk : lenOl PD (O := O) ≠ ⊤) :
    ∀ (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L), Formalism.MainNotions.WachCoordinates.CrysLat PD T₁ →
    Formalism.MainNotions.WachCoordinates.CrysLat PD T₂ → F.Onto → ∀ x, Formalism.MainNotions.TruncatedSeriesCountingBounds.ColLeR PD (bHom (O' := O') hc hO' F) x →
      Formalism.MainNotions.TruncatedSeriesCountingBounds.ColLeR PD F x :=
  fun T₁ T₂ F _ _ _ x h => descCol PD hc hO' bO bL hb hlin hk T₁ T₂ F x h

end Desc

end Formalism.MainNotions.UnusedSlot80.BCW
