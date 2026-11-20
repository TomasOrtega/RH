import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.MultiplicationKernelIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreEig
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsSaturatedSubmoduleIffExistsIsComplOfValuationR
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module

namespace GlobalTheory.LenMap

/- English proof (translation)
Use `⟨fun r hr x y hxy => ?_⟩` and prove the remaining obligations. Establish `hr0 : r ≠ 0` using `hr.ne_zero`. Establish `h1 : r • ((x : M) - y) = 0`. Use `congrArg Subtype.val hxy` as an intermediate fact. Simplify using `only [SetLike.val_smul] at this`.

Rewrite using `[smul_sub, this, sub_self]`. Conclude with `Subtype.ext (sub_eq_zero.1 (h r _ hr0 h1))`.
-/
theorem isTorsionFree_submodule {R : Type*} [CommRing R] [IsDomain R] {M : Type*} [AddCommGroup M]
    [Module R M] (h : ∀ (c : R) (x : M), c ≠ 0 → c • x = 0 → x = 0) (N : Submodule R M) :
    Module.IsTorsionFree R N := by
  refine ⟨fun r hr x y hxy => ?_⟩
  have hr0 : r ≠ 0 := hr.ne_zero
  have h1 : r • ((x : M) - y) = 0 := by
    have := congrArg Subtype.val hxy
    simp only [SetLike.val_smul] at this
    rw [smul_sub, this, sub_self]
  exact Subtype.ext (sub_eq_zero.1 (h r _ hr0 h1))

/- English proof (translation)
Set `w : ι ⊕ κ → M` to `Sum.elim (fun i => (d i : M)) σ`. Establish `hwZ : ∀ k, w k ∈ Z`. Introduce and unpack `(i | j)`. Conclude with `(Submodule.mem_inf.1 (d i).2).1`. Conclude with `hσZ j`.

Set `u : ι ⊕ κ → Z` to `fun k => ⟨w k, hwZ k⟩`. Establish `hdf : ∀ i, f (d i : M) = 0` using `fun i => LinearMap.mem_ker.1 (Submodule.mem_inf.1 (d i).2).2`. Establish `hdli : LinearIndependent R (fun i => (d i : M))` using `d.linearIndependent.map' (Z ⊓ LinearMap.ker f).subtype (Submodule.ker_subtype _)`. Establish `heli : LinearIndependent R (fun j => (e j : M'))` using `e.linearIndependent.map' (Z.map f).subtype (Submodule.ker_subtype _)`. Establish `hli : LinearIndependent R u`.

Apply `LinearIndependent.of_comp Z.subtype` to reduce the goal to its premises. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg`. Establish `hg' : ∑ i, g (Sum.inl i) • (d i : M) + ∑ j, g (Sum.inr j) • σ j = 0`. Simplify `hg` using `[Fintype.sum_sum_type, u, w]`.

Establish `h2 : ∑ j, g (Sum.inr j) • (e j : M') = 0`. Use `congrArg f hg'` as an intermediate fact. Simplify `this` using `[map_add, map_sum, map_smul, hdf, hσf]`. Establish `hr : ∀ j, g (Sum.inr j) = 0` using `Fintype.linearIndependent_iff.1 heli _ h2`. Establish `h1 : ∑ i, g (Sum.inl i) • (d i : M) = 0` using `by simpa [hr] using hg'`.

Establish `hl : ∀ i, g (Sum.inl i) = 0` using `Fintype.linearIndependent_iff.1 hdli _ h1`. Introduce and unpack `(i | j)`. Conclude with `hl i`. Conclude with `hr j`. Establish `hsp : ⊤ ≤ Submodule.span R (Set.range u)`.

Introduce and unpack `⟨z, hz⟩ -`. Rewrite using `[Submodule.mem_span_range_iff_exists_fun]`. Establish `hfz : f z ∈ Z.map f` using `Submodule.mem_map_of_mem hz`. Set `bb` to `e.repr ⟨f z, hfz⟩`. Establish `hy : (∑ j, bb j • (e j : M')) = f z`.

Establish `h0` using `congrArg Subtype.val (e.sum_repr ⟨f z, hfz⟩)`. Rewrite `h0` using `[Submodule.coe_sum]`. Simplify `h0` using `only [Submodule.coe_smul]`. Establish `hk : z - ∑ j, bb j • σ j ∈ Z ⊓ LinearMap.ker f`. Use `Submodule.mem_inf.2 ⟨Z.sub_mem hz (Z.sum_mem fun j _ => Z.smul_mem _ (hσZ j)), ?_⟩` and prove the remaining obligations.

Rewrite using `[LinearMap.mem_ker, map_sub, map_sum]`. Simplify using `only [map_smul, hσf]`. Rewrite using `[hy, sub_self]`. Establish `hkk` using `congrArg Subtype.val (d.sum_repr ⟨_, hk⟩)`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul] at hkk`.

Use `⟨Sum.elim (d.repr ⟨_, hk⟩) bb, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[Fintype.sum_sum_type, Submodule.coe_add, Submodule.coe_sum, Submodule.coe_sum]`. Simplify using `only [Submodule.coe_smul, Sum.elim_inl, Sum.elim_inr, u, w]`. Rewrite using `[hkk, sub_add_cancel]`.

Conclude with `⟨Basis.mk hli hsp, fun k => by simp [u, w]⟩`.
-/
theorem exists_basis_sum {R : Type*} [CommRing R] {M M' : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] (f : M →ₗ[R] M') (Z : Submodule R M) {ι κ : Type*}
    [Fintype ι] [Fintype κ] (d : Basis ι R ↥(Z ⊓ LinearMap.ker f)) (e : Basis κ R ↥(Z.map f))
    (σ : κ → M) (hσZ : ∀ j, σ j ∈ Z) (hσf : ∀ j, f (σ j) = e j) :
    ∃ b : Basis (ι ⊕ κ) R Z, ∀ k, (b k : M) = Sum.elim (fun i => (d i : M)) σ k := by
  classical
  let w : ι ⊕ κ → M := Sum.elim (fun i => (d i : M)) σ
  have hwZ : ∀ k, w k ∈ Z := by
    rintro (i | j)
    · exact (Submodule.mem_inf.1 (d i).2).1
    · exact hσZ j
  let u : ι ⊕ κ → Z := fun k => ⟨w k, hwZ k⟩
  have hdf : ∀ i, f (d i : M) = 0 := fun i => LinearMap.mem_ker.1 (Submodule.mem_inf.1 (d i).2).2
  have hdli : LinearIndependent R (fun i => (d i : M)) :=
    d.linearIndependent.map' (Z ⊓ LinearMap.ker f).subtype (Submodule.ker_subtype _)
  have heli : LinearIndependent R (fun j => (e j : M')) :=
    e.linearIndependent.map' (Z.map f).subtype (Submodule.ker_subtype _)
  have hli : LinearIndependent R u := by
    apply LinearIndependent.of_comp Z.subtype
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hg' : ∑ i, g (Sum.inl i) • (d i : M) + ∑ j, g (Sum.inr j) • σ j = 0 := by
      simpa [Fintype.sum_sum_type, u, w] using hg
    have h2 : ∑ j, g (Sum.inr j) • (e j : M') = 0 := by
      have := congrArg f hg'
      simpa [map_add, map_sum, map_smul, hdf, hσf] using this
    have hr : ∀ j, g (Sum.inr j) = 0 := Fintype.linearIndependent_iff.1 heli _ h2
    have h1 : ∑ i, g (Sum.inl i) • (d i : M) = 0 := by simpa [hr] using hg'
    have hl : ∀ i, g (Sum.inl i) = 0 := Fintype.linearIndependent_iff.1 hdli _ h1
    rintro (i | j)
    · exact hl i
    · exact hr j
  have hsp : ⊤ ≤ Submodule.span R (Set.range u) := by
    rintro ⟨z, hz⟩ -
    rw [Submodule.mem_span_range_iff_exists_fun]
    have hfz : f z ∈ Z.map f := Submodule.mem_map_of_mem hz
    let bb := e.repr ⟨f z, hfz⟩
    have hy : (∑ j, bb j • (e j : M')) = f z := by
      have h0 := congrArg Subtype.val (e.sum_repr ⟨f z, hfz⟩)
      rw [Submodule.coe_sum] at h0
      simpa only [Submodule.coe_smul] using h0
    have hk : z - ∑ j, bb j • σ j ∈ Z ⊓ LinearMap.ker f := by
      refine Submodule.mem_inf.2 ⟨Z.sub_mem hz (Z.sum_mem fun j _ => Z.smul_mem _ (hσZ j)), ?_⟩
      rw [LinearMap.mem_ker, map_sub, map_sum]
      simp only [map_smul, hσf]
      rw [hy, sub_self]
    have hkk := congrArg Subtype.val (d.sum_repr ⟨_, hk⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hkk
    refine ⟨Sum.elim (d.repr ⟨_, hk⟩) bb, ?_⟩
    apply Subtype.ext
    rw [Fintype.sum_sum_type, Submodule.coe_add, Submodule.coe_sum, Submodule.coe_sum]
    simp only [Submodule.coe_smul, Sum.elim_inl, Sum.elim_inr, u, w]
    rw [hkk, sub_add_cancel]
  exact ⟨Basis.mk hli hsp, fun k => by simp [u, w]⟩

end GlobalTheory.LenMap

namespace GlobalTheory.LenMap

variable {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {M : Type} [AddCommGroup M]
  [Module (Int0 v) M]

/- English proof (translation)
Establish `key : ∀ (b : Basis ι (Int0 v) X) (b' : Basis ι (Int0 v) X') (A : Matrix ι ι (Int0 v)), (∀ k, (b' k : M) = ∑ i, A i k • (b i : M)) → LinearMap.toMatrix b' b (Submodule.inclusion hle) = A`. Introduce `b b' A hA`. Use extensionality with `i k`. Establish `: Submodule.inclusion hle (b' k) = ∑ i, A i k • b i`. Apply `Subtype.ext` to reduce the goal to its premises.

Simplify using `using hA k`. Rewrite using `[LinearMap.toMatrix_apply, this]`. Simplify using `[Finsupp.single_apply]`. Establish `hAB : A = b.toMatrix c * B * c'.toMatrix b'`. Rewrite using `[← key b b' A hA, ← key c c' B hB, basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix]`.

Establish `u1 : IsUnit (b.toMatrix c).det`. Use `letI := b.invertibleToMatrix c`. Conclude with `Matrix.isUnit_det_of_invertible _`. Establish `u2 : IsUnit (c'.toMatrix b').det`. Use `letI := c'.invertibleToMatrix b'`.

Conclude with `Matrix.isUnit_det_of_invertible _`. Rewrite using `[hAB, Matrix.det_mul, Matrix.det_mul, Subring.coe_mul, Subring.coe_mul, v.map_mul, v.map_mul, v_unit v u1, v_unit v u2, zero_add, add_zero]`.
-/
theorem val_det_eq {ι : Type} [Fintype ι] [DecidableEq ι] {X' X : Submodule (Int0 v) M}
    (hle : X' ≤ X) (b c : Basis ι (Int0 v) X) (b' c' : Basis ι (Int0 v) X')
    (A B : Matrix ι ι (Int0 v)) (hA : ∀ k, (b' k : M) = ∑ i, A i k • (b i : M))
    (hB : ∀ k, (c' k : M) = ∑ i, B i k • (c i : M)) : v (A.det : C) = v (B.det : C) := by
  have key : ∀ (b : Basis ι (Int0 v) X) (b' : Basis ι (Int0 v) X')
      (A : Matrix ι ι (Int0 v)), (∀ k, (b' k : M) = ∑ i, A i k • (b i : M)) →
      LinearMap.toMatrix b' b (Submodule.inclusion hle) = A := by
    intro b b' A hA
    ext i k
    have : Submodule.inclusion hle (b' k) = ∑ i, A i k • b i := by
      apply Subtype.ext
      simpa using hA k
    rw [LinearMap.toMatrix_apply, this]
    simp [Finsupp.single_apply]
  have hAB : A = b.toMatrix c * B * c'.toMatrix b' := by
    rw [← key b b' A hA, ← key c c' B hB, basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix]
  have u1 : IsUnit (b.toMatrix c).det := by
    letI := b.invertibleToMatrix c
    exact Matrix.isUnit_det_of_invertible _
  have u2 : IsUnit (c'.toMatrix b').det := by
    letI := c'.invertibleToMatrix b'
    exact Matrix.isUnit_det_of_invertible _
  rw [hAB, Matrix.det_mul, Matrix.det_mul, Subring.coe_mul, Subring.coe_mul, v.map_mul,
    v.map_mul, v_unit v u1, v_unit v u2, zero_add, add_zero]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨n, c, c', B, hB, hr⟩`. Set `e` to `b.indexEquiv c`. Rewrite using `[← hr, ← Matrix.det_reindex_self e.symm B]`. Use `val_det_eq v hle b (c.reindex e.symm) b' (c'.reindex e.symm) A _ hA fun k => ?_` and prove the remaining obligations.

Simplify using `only [Basis.reindex_apply, Equiv.symm_symm, Matrix.reindex_apply, Matrix.submatrix_apply]`. Rewrite using `[hB]`. Conclude with `(Equiv.sum_comp e (fun i => B i (e k) • (c i : M))).symm`. Introduce `h`. Set `e` to `Fintype.equivFin ι`.

Use `⟨Fintype.card ι, b.reindex e, b'.reindex e, Matrix.reindex e e A, fun k => ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [Basis.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_apply]`. Rewrite using `[hA]`. Conclude with `(Equiv.sum_comp e.symm (fun i => A i (e.symm k) • (b i : M))).symm`. Rewrite using `[Matrix.det_reindex_self]`.

Conclude with `h`.
-/
theorem relLen_iff_of_basis {ι : Type} [Fintype ι] [DecidableEq ι] {X' X : Submodule (Int0 v) M}
    (hle : X' ≤ X) (b : Basis ι (Int0 v) X) (b' : Basis ι (Int0 v) X')
    (A : Matrix ι ι (Int0 v)) (hA : ∀ k, (b' k : M) = ∑ i, A i k • (b i : M)) (r : ℝ) :
    RelLen v X' X r ↔ v (A.det : C) = r := by
  constructor
  · rintro ⟨n, c, c', B, hB, hr⟩
    let e := b.indexEquiv c
    rw [← hr, ← Matrix.det_reindex_self e.symm B]
    refine val_det_eq v hle b (c.reindex e.symm) b' (c'.reindex e.symm) A _ hA fun k => ?_
    simp only [Basis.reindex_apply, Equiv.symm_symm, Matrix.reindex_apply, Matrix.submatrix_apply]
    rw [hB]
    exact (Equiv.sum_comp e (fun i => B i (e k) • (c i : M))).symm
  · intro h
    let e := Fintype.equivFin ι
    refine ⟨Fintype.card ι, b.reindex e, b'.reindex e, Matrix.reindex e e A, fun k => ?_, ?_⟩
    · simp only [Basis.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
      rw [hA]
      exact (Equiv.sum_comp e.symm (fun i => A i (e.symm k) • (b i : M))).symm
    · rw [Matrix.det_reindex_self]; exact h

/- English proof (translation)
Take `⟨n, c, c', -, -, -⟩` from `h`. Rewrite using `[Fintype.card_congr (b.indexEquiv c), Fintype.card_congr (b'.indexEquiv c')]`.
-/
theorem card_eq_of_relLen {ι ι' : Type} [Fintype ι] [Fintype ι'] {X' X : Submodule (Int0 v) M}
    {r : ℝ} (h : RelLen v X' X r) (b : Basis ι (Int0 v) X) (b' : Basis ι' (Int0 v) X') :
    Fintype.card ι = Fintype.card ι' := by
  obtain ⟨n, c, c', -, -, -⟩ := h
  rw [Fintype.card_congr (b.indexEquiv c), Fintype.card_congr (b'.indexEquiv c')]

end GlobalTheory.LenMap

namespace GlobalTheory.LenMap

/- English proof (translation)
Introduce `C _ v M M' _ _ _ _ htM htM' f X' X hle hker hX hX' r`. Use `haveI := isTorsionFree_submodule htM' (X.map f)`. Use `haveI := isTorsionFree_submodule htM' (X'.map f)`. Use `haveI := isTorsionFree_submodule htM (X ⊓ LinearMap.ker f)`. Use `haveI : Module.Finite (Int0 v) (X.map f) := Module.Finite.map X f`.

Use `haveI : Module.Finite (Int0 v) (X'.map f) := Module.Finite.map X' f`. Use `haveI := GlobalTheory.free_of_finite_of_isTorsionFree_of_valuationRing (Int0 v) (X.map f)`. Use `haveI := GlobalTheory.free_of_finite_of_isTorsionFree_of_valuationRing (Int0 v) (X'.map f)`. Set `g : X →ₗ[Int0 v] X.map f` to `f.submoduleMap X`. Establish `hg : Function.Surjective g` using `f.submoduleMap_surjective X`.

Use `haveI : Module.FinitePresentation (Int0 v) (X.map f) := Module.finitePresentation_of_projective _ _`. Establish `hfg : (LinearMap.ker g).FG` using `Module.FinitePresentation.fg_ker g hg`. Establish `hK : (LinearMap.ker g).map X.subtype = X ⊓ LinearMap.ker f`. Use extensionality with `x`. Simplify using `only [Submodule.mem_map, LinearMap.mem_ker, Submodule.mem_inf, Submodule.subtype_apply]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Use `⟨y.2, ?_⟩` and prove the remaining obligations. Use `congrArg Subtype.val hy` as an intermediate fact. Simplify `this` using `[g]`.

Introduce and unpack `⟨hx, hfx⟩`. Conclude with `⟨⟨x, hx⟩, Subtype.ext (by simpa [g] using hfx), rfl⟩`. Use `haveI : Module.Finite (Int0 v) ↥(X ⊓ LinearMap.ker f) := by`. Rewrite using `[Module.Finite.iff_fg, ← hK]`. Conclude with `hfg.map _`.

Use `haveI := GlobalTheory.free_of_finite_of_isTorsionFree_of_valuationRing (Int0 v) ↥(X ⊓ LinearMap.ker f)`. Establish `hK' : X' ⊓ LinearMap.ker f = X ⊓ LinearMap.ker f` using `le_antisymm (inf_le_inf_right _ hle) (le_inf hker inf_le_right)`. Take `⟨q, ⟨d⟩⟩ : ∃ q : ℕ, Nonempty (Basis (Fin q) (Int0 v) ↥(X ⊓ LinearMap.ker f))` from `⟨_, ⟨Module.finBasis _ _⟩⟩`. Take `⟨p, ⟨c⟩⟩ : ∃ p : ℕ, Nonempty (Basis (Fin p) (Int0 v) ↥(X.map f))` from `⟨_, ⟨Module.finBasis _ _⟩⟩`. Take `⟨p', ⟨c'⟩⟩ : ∃ p : ℕ, Nonempty (Basis (Fin p) (Int0 v) ↥(X'.map f))` from `⟨_, ⟨Module.finBasis _ _⟩⟩`.

Set `d' : Basis (Fin q) (Int0 v) ↥(X' ⊓ LinearMap.ker f)` to `d.map (LinearEquiv.ofEq _ _ hK'.symm)`. Establish `hd' : ∀ i, (d' i : M) = d i` using `fun i => rfl`. Establish `hdf : ∀ i, f (d i : M) = 0` using `fun i => LinearMap.mem_ker.1 (Submodule.mem_inf.1 (d i).2).2`. Use `choose σ hσX hσf using fun j => Submodule.mem_map.1 (c j).2`. Use `choose σ' hσX' hσf' using fun j => Submodule.mem_map.1 (c' j).2`.

Take `⟨b, hb⟩` from `exists_basis_sum f X d c σ hσX hσf`. Take `⟨b', hb'⟩` from `exists_basis_sum f X' d' c' σ' hσX' hσf'`. Distinguish the cases in `hp : p = p'`. Substitute `hp` using the available equality. Set `A : Matrix (Fin q ⊕ Fin p) (Fin q ⊕ Fin p) (Int0 v)` to `Matrix.of fun i k => b.repr (Submodule.inclusion hle (b' k)) i`.

Establish `hA : ∀ k, (b' k : M) = ∑ i, A i k • (b i : M)`. Introduce `k`. Establish `h0` using `congrArg Subtype.val (b.sum_repr (Submodule.inclusion hle (b' k)))`. Rewrite `h0` using `[Submodule.coe_sum]`. Simplify `h0.symm` using `only [Submodule.coe_smul, Submodule.coe_inclusion, A, Matrix.of_apply]`.

Rewrite using `[relLen_iff_of_basis v hle b b' A hA]`. Set `B` to `A.toBlocks₂₂`. Establish `hB : ∀ k, (c' k : M') = ∑ j, B j k • (c j : M')`. Introduce `k`. Establish `h1` using `congrArg f (hA (Sum.inr k))`.

Rewrite `h1` using `[hb', Sum.elim_inr, hσf', map_sum, Fintype.sum_sum_type]`. Simplify `h1` using `[hb, hdf, hσf, B, Matrix.toBlocks₂₂]`. Rewrite using `[relLen_iff_of_basis v (Submodule.map_mono hle) c c' B hB]`. Establish `hinl : ∀ i, Submodule.inclusion hle (b' (Sum.inl i)) = b (Sum.inl i)`. Introduce `i`.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[Submodule.coe_inclusion, hb, hb', Sum.elim_inl, Sum.elim_inl, hd']`. Establish `h11 : A.toBlocks₁₁ = 1`. Use extensionality with `i k`. Simplify using `[A, Matrix.toBlocks₁₁, hinl, Finsupp.single_apply, Matrix.one_apply, eq_comm]`.

Establish `h21 : A.toBlocks₂₁ = 0`. Use extensionality with `i k`. Simplify using `[A, Matrix.toBlocks₂₁, hinl, Finsupp.single_apply]`. Establish `hdet : A.det = B.det` using `by conv_lhs => rw [← Matrix.fromBlocks_toBlocks A, h11, h21]`. Rewrite using `[Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul]`.

Rewrite using `[hdet]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `card_eq_of_relLen v h b b'` as an intermediate fact. Simplify using `only [Fintype.card_sum, Fintype.card_fin] at this`.

Use linear arithmetic over natural numbers and integers. Introduce `h`. Use `card_eq_of_relLen v h c c'` as an intermediate fact. Simplify using `only [Fintype.card_fin] at this`. Conclude with `absurd this hp`.
-/
theorem relLen_map_iff : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (M M' : Type) [AddCommGroup M] [Module (Int0 v) M] [AddCommGroup M'] [Module (Int0 v) M'], (∀ (c : Int0 v) (x : M), c ≠ 0 → c • x = 0 → x = 0) → (∀ (c : Int0 v) (x : M'), c ≠ 0 → c • x = 0 → x = 0) → ∀ (f : M →ₗ[Int0 v] M') (X' X : Submodule (Int0 v) M), X' ≤ X → X ⊓ LinearMap.ker f ≤ X' → Module.Finite (Int0 v) X → Module.Finite (Int0 v) X' → ∀ r : ℝ, (RelLen v X' X r ↔ RelLen v (X'.map f) (X.map f) r) := by
  intro C _ v M M' _ _ _ _ htM htM' f X' X hle hker hX hX' r
  classical
  haveI := isTorsionFree_submodule htM' (X.map f)
  haveI := isTorsionFree_submodule htM' (X'.map f)
  haveI := isTorsionFree_submodule htM (X ⊓ LinearMap.ker f)
  haveI : Module.Finite (Int0 v) (X.map f) := Module.Finite.map X f
  haveI : Module.Finite (Int0 v) (X'.map f) := Module.Finite.map X' f
  haveI := GlobalTheory.free_of_finite_of_isTorsionFree_of_valuationRing (Int0 v) (X.map f)
  haveI := GlobalTheory.free_of_finite_of_isTorsionFree_of_valuationRing (Int0 v) (X'.map f)
  let g : X →ₗ[Int0 v] X.map f := f.submoduleMap X
  have hg : Function.Surjective g := f.submoduleMap_surjective X
  haveI : Module.FinitePresentation (Int0 v) (X.map f) := Module.finitePresentation_of_projective _ _
  have hfg : (LinearMap.ker g).FG := Module.FinitePresentation.fg_ker g hg
  have hK : (LinearMap.ker g).map X.subtype = X ⊓ LinearMap.ker f := by
    ext x
    simp only [Submodule.mem_map, LinearMap.mem_ker, Submodule.mem_inf, Submodule.subtype_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, ?_⟩
      have := congrArg Subtype.val hy
      simpa [g] using this
    · rintro ⟨hx, hfx⟩
      exact ⟨⟨x, hx⟩, Subtype.ext (by simpa [g] using hfx), rfl⟩
  haveI : Module.Finite (Int0 v) ↥(X ⊓ LinearMap.ker f) := by
    rw [Module.Finite.iff_fg, ← hK]
    exact hfg.map _
  haveI := GlobalTheory.free_of_finite_of_isTorsionFree_of_valuationRing (Int0 v) ↥(X ⊓ LinearMap.ker f)
  have hK' : X' ⊓ LinearMap.ker f = X ⊓ LinearMap.ker f :=
    le_antisymm (inf_le_inf_right _ hle) (le_inf hker inf_le_right)
  obtain ⟨q, ⟨d⟩⟩ : ∃ q : ℕ, Nonempty (Basis (Fin q) (Int0 v) ↥(X ⊓ LinearMap.ker f)) :=
    ⟨_, ⟨Module.finBasis _ _⟩⟩
  obtain ⟨p, ⟨c⟩⟩ : ∃ p : ℕ, Nonempty (Basis (Fin p) (Int0 v) ↥(X.map f)) :=
    ⟨_, ⟨Module.finBasis _ _⟩⟩
  obtain ⟨p', ⟨c'⟩⟩ : ∃ p : ℕ, Nonempty (Basis (Fin p) (Int0 v) ↥(X'.map f)) :=
    ⟨_, ⟨Module.finBasis _ _⟩⟩
  let d' : Basis (Fin q) (Int0 v) ↥(X' ⊓ LinearMap.ker f) := d.map (LinearEquiv.ofEq _ _ hK'.symm)
  have hd' : ∀ i, (d' i : M) = d i := fun i => rfl
  have hdf : ∀ i, f (d i : M) = 0 := fun i => LinearMap.mem_ker.1 (Submodule.mem_inf.1 (d i).2).2
  choose σ hσX hσf using fun j => Submodule.mem_map.1 (c j).2
  choose σ' hσX' hσf' using fun j => Submodule.mem_map.1 (c' j).2
  obtain ⟨b, hb⟩ := exists_basis_sum f X d c σ hσX hσf
  obtain ⟨b', hb'⟩ := exists_basis_sum f X' d' c' σ' hσX' hσf'
  by_cases hp : p = p'
  · subst hp
    let A : Matrix (Fin q ⊕ Fin p) (Fin q ⊕ Fin p) (Int0 v) :=
      Matrix.of fun i k => b.repr (Submodule.inclusion hle (b' k)) i
    have hA : ∀ k, (b' k : M) = ∑ i, A i k • (b i : M) := by
      intro k
      have h0 := congrArg Subtype.val (b.sum_repr (Submodule.inclusion hle (b' k)))
      rw [Submodule.coe_sum] at h0
      simpa only [Submodule.coe_smul, Submodule.coe_inclusion, A, Matrix.of_apply] using h0.symm
    rw [relLen_iff_of_basis v hle b b' A hA]
    let B := A.toBlocks₂₂
    have hB : ∀ k, (c' k : M') = ∑ j, B j k • (c j : M') := by
      intro k
      have h1 := congrArg f (hA (Sum.inr k))
      rw [hb', Sum.elim_inr, hσf', map_sum, Fintype.sum_sum_type] at h1
      simpa [hb, hdf, hσf, B, Matrix.toBlocks₂₂] using h1
    rw [relLen_iff_of_basis v (Submodule.map_mono hle) c c' B hB]
    have hinl : ∀ i, Submodule.inclusion hle (b' (Sum.inl i)) = b (Sum.inl i) := by
      intro i
      apply Subtype.ext
      rw [Submodule.coe_inclusion, hb, hb', Sum.elim_inl, Sum.elim_inl, hd']
    have h11 : A.toBlocks₁₁ = 1 := by
      ext i k
      simp [A, Matrix.toBlocks₁₁, hinl, Finsupp.single_apply, Matrix.one_apply, eq_comm]
    have h21 : A.toBlocks₂₁ = 0 := by
      ext i k
      simp [A, Matrix.toBlocks₂₁, hinl, Finsupp.single_apply]
    have hdet : A.det = B.det := by
      conv_lhs => rw [← Matrix.fromBlocks_toBlocks A, h11, h21]
      rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul]
    rw [hdet]
  · constructor
    · intro h
      have := card_eq_of_relLen v h b b'
      simp only [Fintype.card_sum, Fintype.card_fin] at this
      omega
    · intro h
      have := card_eq_of_relLen v h c c'
      simp only [Fintype.card_fin] at this
      exact absurd this hp

end GlobalTheory.LenMap
