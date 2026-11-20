import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLatticesComplete

set_option autoImplicit false

namespace GlobalTheory.BadPt

namespace TwoLagr

open Module

variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {K : Type} [Field K] [Algebra R K]
  [IsFractionRing R K] {H : Type*} [AddCommGroup H] [Module K H] [Module R H] [IsScalarTower R K H]
  [Module.Finite K H] {β : LinearMap.BilinForm K H}

/- English proof (translation)
The claim follows from `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (Subspace.dual_finrank_eq (K := K) (V := H)).symm).1 hβ`.
-/
theorem surj (hβ : Function.Injective β) : Function.Surjective β :=
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (Subspace.dual_finrank_eq (K := K) (V := H)).symm).1 hβ

/- English proof (translation)
Establish `hnd : β.Nondegenerate`. Use `⟨fun x hx => hβ (by ext y; simp [hx y]), fun y hy => hβ ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Rewrite using `[hs, hy x]`. Simplify using the standard rewrite rules.

Establish `e : β.orthogonal F = F`. Use extensionality with `s`. Rewrite using `[LinearMap.BilinForm.mem_orthogonal_iff, hF s]`. Use `forall₂_congr fun w _ => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `β w s = 0 ↔ _`.

Rewrite using `[hs, neg_eq_zero]`. Establish `h` using `LinearMap.BilinForm.finrank_orthogonal hnd F`. Rewrite `h` using `[e]`. Use `F.finrank_le` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem two_mul_finrank (hβ : Function.Injective β) (hs : ∀ s w, β s w = - β w s) {F : Submodule K H}
    (hF : IsLagr β F) : finrank K F + finrank K F = finrank K H := by
  have hnd : β.Nondegenerate := by
    refine ⟨fun x hx => hβ (by ext y; simp [hx y]), fun y hy => hβ ?_⟩
    ext x
    rw [hs, hy x]; simp
  have e : β.orthogonal F = F := by
    ext s
    rw [LinearMap.BilinForm.mem_orthogonal_iff, hF s]
    refine forall₂_congr fun w _ => ?_
    change β w s = 0 ↔ _
    rw [hs, neg_eq_zero]
  have h := LinearMap.BilinForm.finrank_orthogonal hnd F
  rw [e] at h
  have := F.finrank_le
  omega

omit [IsDomain R] [IsDiscreteValuationRing R] [Module.Finite K H] in
/- English proof (translation)
Take `⟨a, ha, h⟩` from `FractionalIdeal.isFractional_of_fg (S := nonZeroDivisors R) (hΛ.map (φ.restrictScalars R))`. Use `⟨a, ha, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨y, hy⟩` from `h (φ x) ⟨x, hx, rfl⟩`. Conclude with `Submodule.mem_one.2 ⟨y, hy⟩`.
-/
theorem exists_denom {Λ : Submodule R H} (hΛ : Λ.FG) (φ : H →ₗ[K] K) :
    ∃ a ∈ nonZeroDivisors R, ∀ x ∈ Λ, a • φ x ∈ (1 : Submodule R K) := by
  obtain ⟨a, ha, h⟩ := FractionalIdeal.isFractional_of_fg (S := nonZeroDivisors R) (hΛ.map (φ.restrictScalars R))
  refine ⟨a, ha, fun x hx => ?_⟩
  obtain ⟨y, hy⟩ := h (φ x) ⟨x, hx, rfl⟩
  exact Submodule.mem_one.2 ⟨y, hy⟩

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Take `⟨φ, hφ, hker⟩` from `Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)`. Take `⟨s, rfl⟩` from `surj hβ φ`. Establish `h0 : ∀ x ∈ Λ, β s x = 0` using `fun x hx => hker (Submodule.subset_span hx)`. Establish `hsF : s ∈ F`.

Rewrite using `[hF s]`. Introduce `w hw`. Assume the negation of the conclusion as `hsw`. Take `⟨a, ha, hh⟩` from `exists_denom hΛ (β.flip w)`. Take `⟨π, hπ⟩` from `IsDiscreteValuationRing.exists_irreducible R`.

Establish `ha0 : algebraMap R K a ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ha`. Establish `hπ0 : algebraMap R K π ≠ 0` using `by simpa using hπ.ne_zero`. Establish `hm : ((algebraMap R K a * algebraMap R K π * β s w)⁻¹ • s) ∈ Λ ⊔ F.restrictScalars R`. Rewrite using `[h.2, LinearMap.BilinForm.mem_dualSubmodule]`. Introduce `y hy`.

Simplify using `[h0 y hy.1]`. Take `⟨x, hx, f, hf, e⟩` from `Submodule.mem_sup.1 hm`. Take `⟨y, hy⟩` from `Submodule.mem_one.1 (hh x hx)`. Establish `e2` using `congrArg (fun z => β z w) e`. Simplify using `only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, (hF f).1 hf w hw, add_zero, smul_eq_mul] at e2`.

Rewrite `hy` using `[LinearMap.BilinForm.flip_apply, e2, Algebra.smul_def]`. Use `hπ.not_isUnit (IsUnit.of_mul_eq_one y (IsFractionRing.injective R K ?_))` and prove the remaining obligations. Rewrite using `[map_mul, hy, map_one]`. Clear the denominators using the available nonvanishing facts. Apply `hφ` to reduce the goal to its premises.

Use extensionality with `x`. Take `⟨a, ha, hh⟩` from `exists_denom hΛ (β x)`. Establish `hm : a • x ∈ Λ ⊔ F.restrictScalars R`. Rewrite using `[h.2, LinearMap.BilinForm.mem_dualSubmodule]`. Introduce `y hy`.

Use `hh y hy.1` as an intermediate fact. Rewrite using `[← algebraMap_smul K a x, map_smul, LinearMap.smul_apply, algebraMap_smul]` and apply the resulting hypothesis. Take `⟨y, hy, f, hf, e⟩` from `Submodule.mem_sup.1 hm`. Establish `e2` using `congrArg (β s) e`. Rewrite `e2` using `[map_add, h0 y hy, (hF s).1 hsF f hf, add_zero, ← algebraMap_smul K a x, map_smul, smul_eq_mul]`.

Conclude with `(mul_eq_zero.1 e2.symm).resolve_left (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ha)`.
-/
theorem span_eq_top (hβ : Function.Injective β) {F : Submodule K H} (hF : IsLagr β F)
    {Λ : Submodule R H} (hΛ : Λ.FG) (h : IsAdapted β F (Λ ⊓ F.restrictScalars R) Λ) :
    Submodule.span K (Λ : Set H) = ⊤ := by
  by_contra hne
  obtain ⟨φ, hφ, hker⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  obtain ⟨s, rfl⟩ := surj hβ φ
  have h0 : ∀ x ∈ Λ, β s x = 0 := fun x hx => hker (Submodule.subset_span hx)
  have hsF : s ∈ F := by
    rw [hF s]
    intro w hw
    by_contra hsw
    obtain ⟨a, ha, hh⟩ := exists_denom hΛ (β.flip w)
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
    have ha0 : algebraMap R K a ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ha
    have hπ0 : algebraMap R K π ≠ 0 := by simpa using hπ.ne_zero
    have hm : ((algebraMap R K a * algebraMap R K π * β s w)⁻¹ • s) ∈ Λ ⊔ F.restrictScalars R := by
      rw [h.2, LinearMap.BilinForm.mem_dualSubmodule]
      intro y hy
      simp [h0 y hy.1]
    obtain ⟨x, hx, f, hf, e⟩ := Submodule.mem_sup.1 hm
    obtain ⟨y, hy⟩ := Submodule.mem_one.1 (hh x hx)
    have e2 := congrArg (fun z => β z w) e
    simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, (hF f).1 hf w hw, add_zero,
      smul_eq_mul] at e2
    rw [LinearMap.BilinForm.flip_apply, e2, Algebra.smul_def] at hy
    refine hπ.not_isUnit (IsUnit.of_mul_eq_one y (IsFractionRing.injective R K ?_))
    rw [map_mul, hy, map_one]
    field_simp
  apply hφ
  ext x
  obtain ⟨a, ha, hh⟩ := exists_denom hΛ (β x)
  have hm : a • x ∈ Λ ⊔ F.restrictScalars R := by
    rw [h.2, LinearMap.BilinForm.mem_dualSubmodule]
    intro y hy
    have := hh y hy.1
    rwa [← algebraMap_smul K a x, map_smul, LinearMap.smul_apply, algebraMap_smul]
  obtain ⟨y, hy, f, hf, e⟩ := Submodule.mem_sup.1 hm
  have e2 := congrArg (β s) e
  rw [map_add, h0 y hy, (hF s).1 hsF f hf, add_zero, ← algebraMap_smul K a x, map_smul, smul_eq_mul] at e2
  exact (mul_eq_zero.1 e2.symm).resolve_left (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ha)

omit [Module.Finite K H] in
/- English proof (translation)
Use `haveI : Submodule.IsLattice K Λ := ⟨hΛ, hsp⟩`. Use `haveI : Module.Finite R Λ := Module.Finite.iff_fg.2 hΛ`. Use `haveI : Module.IsTorsionFree R H := .trans_faithfulSMul R K H`. Set `N : Submodule R Λ` to `(F.restrictScalars R).comap Λ.subtype`. Use `haveI : Module.IsTorsionFree R (Λ ⧸ N) := by`.

Use `Module.IsTorsionFree.of_smul_eq_zero fun r x hx => ?_` and prove the remaining obligations. Take `⟨x, rfl⟩` from `N.mkQ_surjective x`. Rewrite `hx` using `[← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Rewrite using `[Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Distinguish the cases in `hr : r = 0`.

Conclude with `Or.inl hr`. Use `right`. Establish `hx' : algebraMap R K r • (x : H) ∈ F` using `by rw [algebraMap_smul]; exact hx`. Conclude with `(F.smul_mem_iff (by simpa using hr)).1 hx'`. Set `bN` to `Module.finBasis R N`.

Set `bQ` to `Module.finBasis R (Λ ⧸ N)`. Use `⟨_, _, (bN.sumQuot bQ).extendOfIsLattice K, ?_, ?_⟩` and prove the remaining obligations. Use `congrArg (Submodule.map Λ.subtype) (bN.sumQuot bQ).span_eq` as an intermediate fact. Rewrite `this` using `[Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp]`. Use `this.symm.trans ?_` and prove the remaining obligations.

Use `congr 2`. Use extensionality with `i`. Simplify using the standard rewrite rules. Apply `le_antisymm` to reduce the goal to its premises. Introduce `x hx`.

Establish `hx' : x ∈ Submodule.span K (Λ : Set H)` using `hsp ▸ trivial`. Take `⟨r, hr⟩` from `multiple_mem_span_of_mem_localization_span (nonZeroDivisors R) K _ x hx'`. Rewrite `hr` using `[Submodule.span_eq, Submonoid.smul_def]`. Establish `hr0 : algebraMap R K r ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors r.2`. Establish `hN : (⟨_, hr⟩ : Λ) ∈ N` using `(F.restrictScalars R).smul_mem _ hx`.

Establish `e` using `congrArg (fun z : N => ((z : Λ) : H)) (bN.sum_repr ⟨_, hN⟩)`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul] at e`. Rewrite using `[← Submodule.smul_mem_iff _ hr0, algebraMap_smul, ← e]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← algebraMap_smul K]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, by simp⟩)`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Establish `: ((bN i : Λ) : H) ∈ F` using `(bN i).2`. Simplify using `using this`.
-/
theorem exists_basis_adapted_lattice_subspace (F : Submodule K H) {Λ : Submodule R H} (hΛ : Λ.FG)
    (hsp : Submodule.span K (Λ : Set H) = ⊤) :
    ∃ (a c : ℕ) (e : Basis (Fin a ⊕ Fin c) K H), Λ = Submodule.span R (Set.range e) ∧
      F = Submodule.span K (Set.range fun i => e (Sum.inl i)) := by
  haveI : Submodule.IsLattice K Λ := ⟨hΛ, hsp⟩
  haveI : Module.Finite R Λ := Module.Finite.iff_fg.2 hΛ
  haveI : Module.IsTorsionFree R H := .trans_faithfulSMul R K H
  let N : Submodule R Λ := (F.restrictScalars R).comap Λ.subtype
  haveI : Module.IsTorsionFree R (Λ ⧸ N) := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun r x hx => ?_
    obtain ⟨x, rfl⟩ := N.mkQ_surjective x
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hx
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    by_cases hr : r = 0
    · exact Or.inl hr
    · right
      have hx' : algebraMap R K r • (x : H) ∈ F := by rw [algebraMap_smul]; exact hx
      exact (F.smul_mem_iff (by simpa using hr)).1 hx'
  let bN := Module.finBasis R N
  let bQ := Module.finBasis R (Λ ⧸ N)
  refine ⟨_, _, (bN.sumQuot bQ).extendOfIsLattice K, ?_, ?_⟩
  · have := congrArg (Submodule.map Λ.subtype) (bN.sumQuot bQ).span_eq
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at this
    refine this.symm.trans ?_
    congr 2
    ext i
    simp
  · apply le_antisymm
    · intro x hx
      have hx' : x ∈ Submodule.span K (Λ : Set H) := hsp ▸ trivial
      obtain ⟨r, hr⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors R) K _ x hx'
      rw [Submodule.span_eq, Submonoid.smul_def] at hr
      have hr0 : algebraMap R K r ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors r.2
      have hN : (⟨_, hr⟩ : Λ) ∈ N := (F.restrictScalars R).smul_mem _ hx
      have e := congrArg (fun z : N => ((z : Λ) : H)) (bN.sum_repr ⟨_, hN⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at e
      rw [← Submodule.smul_mem_iff _ hr0, algebraMap_smul, ← e]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [← algebraMap_smul K]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, by simp⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      have : ((bN i : Λ) : H) ∈ F := (bN i).2
      simpa using this

/- English proof (translation)
Take `⟨a, c, e, h₁, h₂⟩` from `exists_basis_adapted_lattice_subspace F hΛ hsp`. Establish `ha : finrank K F = a`. Rewrite using `[h₂]`. Conclude with `(finrank_span_eq_card (e.linearIndependent.comp _ Sum.inl_injective)).trans (Fintype.card_fin a)`. Establish `hc : finrank K H = a + c` using `by simp [finrank_eq_card_basis e]`.

Use `two_mul_finrank hβ hs hF` as an intermediate fact. Take `rfl : a = n` from `by omega`. Take `rfl : c = a` from `by omega`. Conclude with `⟨e, h₁, h₂⟩`.
-/
theorem exists_basis (hβ : Function.Injective β) (hs : ∀ s w, β s w = - β w s) {F : Submodule K H}
    (hF : IsLagr β F) {Λ : Submodule R H} (hΛ : Λ.FG) (hsp : Submodule.span K (Λ : Set H) = ⊤) {n : ℕ}
    (hn : n + n = finrank K H) :
    ∃ e : Basis (Fin n ⊕ Fin n) K H, Λ = Submodule.span R (Set.range e) ∧
      F = Submodule.span K (Set.range fun i => e (Sum.inl i)) := by
  obtain ⟨a, c, e, h₁, h₂⟩ := exists_basis_adapted_lattice_subspace F hΛ hsp
  have ha : finrank K F = a := by
    rw [h₂]
    exact (finrank_span_eq_card (e.linearIndependent.comp _ Sum.inl_injective)).trans (Fintype.card_fin a)
  have hc : finrank K H = a + c := by simp [finrank_eq_card_basis e]
  have := two_mul_finrank hβ hs hF
  obtain rfl : a = n := by omega
  obtain rfl : c = a := by omega
  exact ⟨e, h₁, h₂⟩

noncomputable def blk {n : ℕ} (β : LinearMap.BilinForm K H) (e : Basis (Fin n ⊕ Fin n) K H) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => β (e (Sum.inr i)) (e (Sum.inl j))

omit [Module.Finite K H] in
/- English proof (translation)
Rewrite using `[← Matrix.det_permute']`. Establish `: (LinearMap.BilinForm.toMatrix e β).submatrix id (Equiv.sumComm (Fin n) (Fin n)) = Matrix.fromBlocks (-(blk β e).transpose) 0 (Matrix.of fun i j => β (e (Sum.inr i)) (e (Sum.inr j))) (blk β e)`. Use extensionality with `(i | i) (j | j)`. Simplify `hs _ _` using `[blk, LinearMap.BilinForm.toMatrix_apply]`. Simplify `h0 _ _` using `[blk, LinearMap.BilinForm.toMatrix_apply]`.

Simplify using `[LinearMap.BilinForm.toMatrix_apply]`. Simplify using `[blk, LinearMap.BilinForm.toMatrix_apply]`. Rewrite using `[this, Matrix.det_fromBlocks_zero₁₂, Matrix.det_neg, Matrix.det_transpose, Fintype.card_fin]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem det_gram (hs : ∀ s w, β s w = - β w s) {n : ℕ} (e : Basis (Fin n ⊕ Fin n) K H)
    (h0 : ∀ i j, β (e (Sum.inl i)) (e (Sum.inl j)) = 0) :
    ((Equiv.Perm.sign (Equiv.sumComm (Fin n) (Fin n)) : ℤ) : K) * (LinearMap.BilinForm.toMatrix e β).det =
      (-1) ^ n * (blk β e).det ^ 2 := by
  rw [← Matrix.det_permute']
  have : (LinearMap.BilinForm.toMatrix e β).submatrix id (Equiv.sumComm (Fin n) (Fin n)) =
      Matrix.fromBlocks (-(blk β e).transpose) 0 (Matrix.of fun i j => β (e (Sum.inr i)) (e (Sum.inr j))) (blk β e) := by
    ext (i | i) (j | j)
    · simpa [blk, LinearMap.BilinForm.toMatrix_apply] using hs _ _
    · simpa [blk, LinearMap.BilinForm.toMatrix_apply] using h0 _ _
    · simp [LinearMap.BilinForm.toMatrix_apply]
    · simp [blk, LinearMap.BilinForm.toMatrix_apply]
  rw [this, Matrix.det_fromBlocks_zero₁₂, Matrix.det_neg, Matrix.det_transpose, Fintype.card_fin]
  ring

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
/- English proof (translation)
Use `choose f hf using fun i j => Submodule.mem_one.1 (h i j)`. Establish `: A = (Matrix.of f).map (algebraMap R K)` using `by ext i j; simp [hf]`. Conclude with `⟨Matrix.of f, this, by rw [RingHom.map_det, this]; rfl⟩`.
-/
theorem det_mem {ι : Type} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι K}
    (h : ∀ i j, A i j ∈ (1 : Submodule R K)) : ∃ A₀ : Matrix ι ι R, A = A₀.map (algebraMap R K) ∧
      A.det = algebraMap R K A₀.det := by
  choose f hf using fun i j => Submodule.mem_one.1 (h i j)
  have : A = (Matrix.of f).map (algebraMap R K) := by ext i j; simp [hf]
  exact ⟨Matrix.of f, this, by rw [RingHom.map_det, this]; rfl⟩

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] [Module.Finite K H] in
/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x h`. Take `⟨j, rfl⟩` from `h`. Rewrite using `[e.repr_self, Finsupp.single_apply]`. Use `split_ifs`.

Conclude with `Submodule.mem_one.2 ⟨1, map_one _⟩`. Conclude with `zero_mem _`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `add_mem hx hy`.

Consider the case `smul r x _ hx`. Rewrite using `[← algebraMap_smul K r x, map_smul, Finsupp.smul_apply, algebraMap_smul]`. Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem repr_mem {ι : Type} (e : Basis ι K H) {x : H} (hx : x ∈ Submodule.span R (Set.range e)) (i : ι) :
    e.repr x i ∈ (1 : Submodule R K) := by
  classical
  induction hx using Submodule.span_induction with
  | mem x h =>
    obtain ⟨j, rfl⟩ := h
    rw [e.repr_self, Finsupp.single_apply]
    split_ifs
    · exact Submodule.mem_one.2 ⟨1, map_one _⟩
    · exact zero_mem _
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r x _ hx =>
    rw [← algebraMap_smul K r x, map_smul, Finsupp.smul_apply, algebraMap_smul]
    exact Submodule.smul_mem _ _ hx

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
/- English proof (translation)
Establish `key : ∀ j : Fin n, ∃ x ∈ Λ, ∀ k, β x (e (Sum.inl k)) = e.coord (Sum.inl j) (e (Sum.inl k))`. Introduce `j`. Take `⟨s, hs⟩` from `surj hβ (e.coord (Sum.inl j))`. Establish `hm : s ∈ Λ ⊔ F.restrictScalars R`. Rewrite using `[h.2, LinearMap.BilinForm.mem_dualSubmodule]`.

Introduce `y hy`. Rewrite using `[hs]`. Conclude with `repr_mem e (h₁ ▸ hy.1) _`. Take `⟨x, hx, f, hf, rfl⟩` from `Submodule.mem_sup.1 hm`. Use `⟨x, hx, fun k => ?_⟩` and prove the remaining obligations.

Rewrite using `[← hs, map_add, LinearMap.add_apply, (hF f).1 hf _ (h₂ k), add_zero]`. Use `choose x hx hk using key`. Take `⟨A, -, hA⟩` from `det_mem (R := R) (A := Matrix.of fun j i => e.repr (x j) (Sum.inr i)) fun j i => repr_mem e (h₁ ▸ hx j) _`. Use `⟨A.det, ?_⟩` and prove the remaining obligations. Rewrite using `[← hA, ← Matrix.det_mul, ← Matrix.det_one (n := Fin n)]`.

Use `congr 1`. Use extensionality with `j k`. Use `hk j k` as an intermediate fact. Rewrite `this` using `[← e.sum_repr (x j)]`. Simplify using `only [map_sum, map_add, map_smul, Fintype.sum_sum_type, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, (hF _).1 (h₂ _) _ (h₂ _), smul_zero, Finset.sum_const_zero, zero_add] at this`.

Simplify using `only [Matrix.mul_apply, blk, Matrix.of_apply, ← smul_eq_mul]`. Rewrite using `[this]`. Simplify using `[Finsupp.single_apply, Matrix.one_apply, eq_comm]`.
-/
theorem exists_inv (hβ : Function.Injective β) {F : Submodule K H} (hF : IsLagr β F) {Λ : Submodule R H}
    (h : IsAdapted β F (Λ ⊓ F.restrictScalars R) Λ) {n : ℕ} (e : Basis (Fin n ⊕ Fin n) K H)
    (h₁ : Λ = Submodule.span R (Set.range e)) (h₂ : ∀ i, e (Sum.inl i) ∈ F) :
    ∃ z : R, algebraMap R K z * (blk β e).det = 1 := by
  have key : ∀ j : Fin n, ∃ x ∈ Λ, ∀ k, β x (e (Sum.inl k)) = e.coord (Sum.inl j) (e (Sum.inl k)) := by
    intro j
    obtain ⟨s, hs⟩ := surj hβ (e.coord (Sum.inl j))
    have hm : s ∈ Λ ⊔ F.restrictScalars R := by
      rw [h.2, LinearMap.BilinForm.mem_dualSubmodule]
      intro y hy
      rw [hs]
      exact repr_mem e (h₁ ▸ hy.1) _
    obtain ⟨x, hx, f, hf, rfl⟩ := Submodule.mem_sup.1 hm
    refine ⟨x, hx, fun k => ?_⟩
    rw [← hs, map_add, LinearMap.add_apply, (hF f).1 hf _ (h₂ k), add_zero]
  choose x hx hk using key
  obtain ⟨A, -, hA⟩ := det_mem (R := R) (A := Matrix.of fun j i => e.repr (x j) (Sum.inr i))
    fun j i => repr_mem e (h₁ ▸ hx j) _
  refine ⟨A.det, ?_⟩
  rw [← hA, ← Matrix.det_mul, ← Matrix.det_one (n := Fin n)]
  congr 1
  ext j k
  have := hk j k
  rw [← e.sum_repr (x j)] at this
  simp only [map_sum, map_add, map_smul, Fintype.sum_sum_type, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, (hF _).1 (h₂ _) _ (h₂ _), smul_zero, Finset.sum_const_zero, zero_add] at this
  simp only [Matrix.mul_apply, blk, Matrix.of_apply, ← smul_eq_mul]
  rw [this]
  simp [Finsupp.single_apply, Matrix.one_apply, eq_comm]

/- English proof (translation)
Use `⟨rfl, le_antisymm (sup_le hle fun c hc => ?_) fun s hsd => ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.BilinForm.mem_dualSubmodule]`. Introduce `y hy`. Rewrite using `[(hC c).1 hc y hy.2]`. Conclude with `zero_mem _`.

Establish `hsp` using `span_eq_top hβ hF hΛ h`. Establish `hn` using `two_mul_finrank hβ hs hF`. Generalize the expression as in `finrank K F = n at hn`. Take `⟨e, e₁, e₂⟩` from `exists_basis hβ hs hF hΛ hsp hn`. Take `⟨g, g₁, g₂⟩` from `exists_basis hβ hs hC hΛ hsp hn`.

Establish `eF : ∀ i, e (Sum.inl i) ∈ F` using `fun i => e₂.ge (Submodule.subset_span ⟨i, rfl⟩)`. Establish `gC : ∀ i, g (Sum.inl i) ∈ C` using `fun i => g₂.ge (Submodule.subset_span ⟨i, rfl⟩)`. Establish `eΛ : ∀ i, e i ∈ Λ` using `fun i => e₁.ge (Submodule.subset_span ⟨i, rfl⟩)`. Establish `gΛ : ∀ i, g i ∈ Λ` using `fun i => g₁.ge (Submodule.subset_span ⟨i, rfl⟩)`. Take `⟨z, hz⟩` from `exists_inv hβ hF h e e₁ eF`.

Establish `de` using `det_gram hs e fun i j => (hF _).1 (eF i) _ (eF j)`. Establish `dg` using `det_gram hs g fun i j => (hC _).1 (gC i) _ (gC j)`. Take `⟨Q, -, hQ⟩` from `det_mem (R := R) (A := g.toMatrix e) fun i j => repr_mem g (g₁ ▸ eΛ j) i`. Take `⟨Y, hY, hY'⟩` from `det_mem (R := R) (A := blk β g) fun i j => (LinearMap.BilinForm.mem_dualSubmodule β).1 (hle (gΛ _)) _ ⟨gΛ _, gC j⟩`. Establish `hd` using `congrArg Matrix.det (LinearMap.BilinForm.toMatrix_mul_basis_toMatrix g e β)`.

Rewrite `hd` using `[Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hQ]`. Establish `hu : IsUnit Y.det`. Use `IsUnit.of_mul_eq_one (Y.det * z ^ 2 * Q.det ^ 2) (IsFractionRing.injective R K ?_)` and prove the remaining obligations. Simplify using `only [map_mul, map_pow, map_one]`. Rewrite using `[← hY']`.

Establish `hm : ((-1 : K) ^ n) ≠ 0` using `pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)`. Apply `mul_left_cancel₀ hm` to reduce the goal to its premises. Rewrite `de` using `[← hd]`. Take the linear combination `(-(algebraMap R K z ^ 2 * algebraMap R K Q.det ^ 2)) * dg + (algebraMap R K z ^ 2) * de + (-1) ^ n * (algebraMap R K z * (blk β e).det + 1) * hz`. Use `choose v hv using fun k => Submodule.mem_one.1 ((LinearMap.BilinForm.mem_dualSubmodule β).1 hsd (g (Sum.inl k)) ⟨gΛ _, gC k⟩)`.

Set `c : Fin n → R` to `Matrix.vecMul v Y⁻¹`. Establish `hc : Matrix.vecMul c Y = v`. Rewrite using `[Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hu, Matrix.vecMul_one]`. Use `Submodule.mem_sup.2 ⟨∑ i, c i • g (Sum.inr i), Submodule.sum_mem _ fun i _ => Λ.smul_mem _ (gΛ _), s - ∑ i, c i • g (Sum.inr i), ?_, by abel⟩` and prove the remaining obligations. Use `(hC _).2 fun w hw => ?_` and prove the remaining obligations.

Establish `: C ≤ LinearMap.ker (β (s - ∑ i, c i • g (Sum.inr i)))`. Use `g₂.le.trans (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨k, rfl⟩`. Establish `hYe : ∀ i, β (g (Sum.inr i)) (g (Sum.inl k)) = algebraMap R K (Y i k)` using `fun i => congrFun (congrFun hY i) k`. Simplify using `only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_sum, LinearMap.sub_apply, LinearMap.sum_apply, ← algebraMap_smul K (c _), map_smul, LinearMap.smul_apply, hYe, ← hv k, ← hc, smul_eq_mul]`.

Simplify using `[Matrix.vecMul, dotProduct]`. Conclude with `this hw`.
-/
theorem adapted (hβ : Function.Injective β) (hs : ∀ s w, β s w = - β w s) {F C : Submodule K H}
    (hF : IsLagr β F) (hC : IsLagr β C) {Λ : Submodule R H} (hΛ : Λ.FG)
    (h : IsAdapted β F (Λ ⊓ F.restrictScalars R) Λ) (hle : Λ ≤ β.dualSubmodule (Λ ⊓ C.restrictScalars R)) :
    IsAdapted β C (Λ ⊓ C.restrictScalars R) Λ := by
  refine ⟨rfl, le_antisymm (sup_le hle fun c hc => ?_) fun s hsd => ?_⟩
  · rw [LinearMap.BilinForm.mem_dualSubmodule]
    intro y hy
    rw [(hC c).1 hc y hy.2]
    exact zero_mem _
  have hsp := span_eq_top hβ hF hΛ h
  have hn := two_mul_finrank hβ hs hF
  generalize finrank K F = n at hn
  obtain ⟨e, e₁, e₂⟩ := exists_basis hβ hs hF hΛ hsp hn
  obtain ⟨g, g₁, g₂⟩ := exists_basis hβ hs hC hΛ hsp hn
  have eF : ∀ i, e (Sum.inl i) ∈ F := fun i => e₂.ge (Submodule.subset_span ⟨i, rfl⟩)
  have gC : ∀ i, g (Sum.inl i) ∈ C := fun i => g₂.ge (Submodule.subset_span ⟨i, rfl⟩)
  have eΛ : ∀ i, e i ∈ Λ := fun i => e₁.ge (Submodule.subset_span ⟨i, rfl⟩)
  have gΛ : ∀ i, g i ∈ Λ := fun i => g₁.ge (Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨z, hz⟩ := exists_inv hβ hF h e e₁ eF
  have de := det_gram hs e fun i j => (hF _).1 (eF i) _ (eF j)
  have dg := det_gram hs g fun i j => (hC _).1 (gC i) _ (gC j)
  obtain ⟨Q, -, hQ⟩ := det_mem (R := R) (A := g.toMatrix e) fun i j => repr_mem g (g₁ ▸ eΛ j) i
  obtain ⟨Y, hY, hY'⟩ := det_mem (R := R) (A := blk β g) fun i j =>
    (LinearMap.BilinForm.mem_dualSubmodule β).1 (hle (gΛ _)) _ ⟨gΛ _, gC j⟩
  have hd := congrArg Matrix.det (LinearMap.BilinForm.toMatrix_mul_basis_toMatrix g e β)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hQ] at hd
  have hu : IsUnit Y.det := by
    refine IsUnit.of_mul_eq_one (Y.det * z ^ 2 * Q.det ^ 2) (IsFractionRing.injective R K ?_)
    simp only [map_mul, map_pow, map_one]
    rw [← hY']
    have hm : ((-1 : K) ^ n) ≠ 0 := pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)
    apply mul_left_cancel₀ hm
    rw [← hd] at de
    linear_combination (-(algebraMap R K z ^ 2 * algebraMap R K Q.det ^ 2)) * dg + (algebraMap R K z ^ 2) * de +
      (-1) ^ n * (algebraMap R K z * (blk β e).det + 1) * hz
  choose v hv using fun k => Submodule.mem_one.1
    ((LinearMap.BilinForm.mem_dualSubmodule β).1 hsd (g (Sum.inl k)) ⟨gΛ _, gC k⟩)
  let c : Fin n → R := Matrix.vecMul v Y⁻¹
  have hc : Matrix.vecMul c Y = v := by
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hu, Matrix.vecMul_one]
  refine Submodule.mem_sup.2 ⟨∑ i, c i • g (Sum.inr i), Submodule.sum_mem _ fun i _ => Λ.smul_mem _ (gΛ _),
    s - ∑ i, c i • g (Sum.inr i), ?_, by abel⟩
  refine (hC _).2 fun w hw => ?_
  have : C ≤ LinearMap.ker (β (s - ∑ i, c i • g (Sum.inr i))) := by
    refine g₂.le.trans (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    have hYe : ∀ i, β (g (Sum.inr i)) (g (Sum.inl k)) = algebraMap R K (Y i k) := fun i => congrFun (congrFun hY i) k
    simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_sum, LinearMap.sub_apply, LinearMap.sum_apply,
      ← algebraMap_smul K (c _), map_smul, LinearMap.smul_apply, hYe, ← hv k, ← hc, smul_eq_mul]
    simp [Matrix.vecMul, dotProduct]
  exact this hw

end TwoLagr

/- English proof (translation)
Introduce `_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hβ hs hF hC hΛ h hle` and use `TwoLagr.adapted hβ hs hF hC hΛ h hle`.
-/
theorem isAdapted_of_le_dualSubmodule : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] (H : Type 1) [AddCommGroup H] [Module K H] [Module R H] [IsScalarTower R K H] [Module.Finite K H] (β : LinearMap.BilinForm K H) (F C : Submodule K H) (Λ : Submodule R H), Function.Injective β → (∀ s w, β s w = - β w s) → IsLagr β F → IsLagr β C → Λ.FG → IsAdapted β F (Λ ⊓ F.restrictScalars R) Λ → Λ ≤ β.dualSubmodule (Λ ⊓ C.restrictScalars R) → IsAdapted β C (Λ ⊓ C.restrictScalars R) Λ :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hβ hs hF hC hΛ h hle => TwoLagr.adapted hβ hs hF hC hΛ h hle

end GlobalTheory.BadPt
