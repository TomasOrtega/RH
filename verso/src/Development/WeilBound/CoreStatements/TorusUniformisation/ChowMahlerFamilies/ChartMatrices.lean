import Mathlib
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.IsDerAt0
import Development.WeilBound.CoreStatements.HodgeTatePoints.IsFractionRingOfIntegers
import Development.WeilBound.CoreStatements.HodgeTatePoints.FreeOfFg
import Development.WeilBound.CoreStatements.HodgeTatePoints.GdChart
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct
open scoped Matrix

noncomputable section

namespace PositivityTheory.Xgn.TestGroupPoint

section Pt

variable {C O : Type} [Field C] [CommRing O] [Algebra O C] {E : Type} [Field E] [NumberField E]
  {c : E ≃+* E} {κ : O} {N : ℕ}
  {V Ω' : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]
  [AddCommGroup Ω'] [Module C Ω'] [Module O Ω'] [IsScalarTower O C Ω']

/- English proof (translation)
Establish `h` using `P.alt (x + y)`. Simplify using `only [map_add, LinearMap.add_apply, P.alt, zero_add, add_zero] at h`. Take the linear combination `h`.
-/
theorem pt_swap (P : HTPoint C O c κ N V Ω') (x y : V) : P.e x y = -P.e y x := by
  have h := P.alt (x + y)
  simp only [map_add, LinearMap.add_apply, P.alt, zero_add, add_zero] at h
  linear_combination h

/- English proof (translation)
The claim follows from `PositivityTheory.HtPt.Gd.tate_single P m.1 _`.
-/
theorem pt_tate (P : HTPoint C O c κ N V Ω') (m : Ix E N) :
    P.tate (dl m) = P.ρ (RingOfIntegers.basis E m.2) (P.t m.1) :=
  PositivityTheory.HtPt.Gd.tate_single P m.1 _

/- English proof (translation)
Use `haveI : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)`. Use `haveI := PositivityTheory.HtPt.Gb.isFractionRing_of_integers hv`. Use `haveI := P.om_lat`. Establish `hinj` using `hv.hom_inj`. Establish `hsp : ⊤ ≤ Submodule.span C (Set.range fun q : Ix E N => P.ρ (RingOfIntegers.basis E q.2) (P.t q.1))`.

Rewrite using `[← Submodule.span_span_of_tower O C, ← P.free.2.2, P.free.2.1]`. Set `B : Basis (Ix E N) C V` to `Basis.mk P.free.1 hsp`. Establish `hBt : ∀ m, P.tate (dl m) = B m` using `fun m => by rw [pt_tate, Basis.mk_apply]`. Establish `hT : P.T = Submodule.span O (Set.range B)` using `by rw [Basis.coe_mk, ← P.free.2.2]`. Establish `hB : ∀ q, B q ∈ P.T` using `fun q => by`.

Rewrite using `[hT]`. Conclude with `Submodule.subset_span ⟨q, rfl⟩`. Use `haveI : FiniteDimensional C V := Module.Finite.of_basis B`. Establish `hnd : ∀ x, (∀ y, P.e x y = 0) → x = 0` using `fun x hx => P.nondeg x fun y => by rw [pt_swap, hx, neg_zero]`. Establish `hei : Function.Injective (P.e : V →ₗ[C] Module.Dual C V)`.

Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Conclude with `hnd x fun y => by rw [hx]; rfl`. Establish `hes` using `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (Subspace.dual_finrank_eq).symm).1 hei`. Establish `hE : ∀ m m', ∃ r : O, algebraMap O C r = P.e (B m) (B m')` using `fun m m' => by`.

Use `hB m'` as an intermediate fact. Rewrite `this` using `[← P.perfect]`. Conclude with `this _ (hB m)`. Use `choose Eg hEg using hE`. Use `choose w hw using fun m => hes (B.coord m)`.

Establish `hwT : ∀ m, w m ∈ P.T` using `fun m => by`. Rewrite using `[← P.perfect]`. Introduce `x hx`. Rewrite using `[pt_swap, hw]`. Use `neg_mem ?_` and prove the remaining obligations.

Rewrite `hx` using `[hT]`. Take `⟨a, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun O).1 hx`. Use `⟨a m, ?_⟩` and prove the remaining obligations. Simplify using `only [map_sum, LinearMap.map_smul_of_tower, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]`. Rewrite using `[Finset.sum_eq_single m (fun b _ hb => by simp [hb]) (by simp)]`.

Simplify using `[Algebra.smul_def]`. Use `choose Ei hEi using fun m => (Submodule.mem_span_range_iff_exists_fun O).1 (hT ▸ hwT m)`. Set `bC` to `bo.extendOfIsLattice C`. Establish `hbC : ∀ (y : P.om) k, bC.repr (y : Ω') k = algebraMap O C (bo.repr y k)` using `fun y k => by`. Establish `e : (y : Ω') = ∑ j, algebraMap O C (bo.repr y j) • bC j`.

Use `congrArg Subtype.val (bo.sum_repr y)` as an intermediate fact. Rewrite `this` using `[Submodule.coe_sum]`. Rewrite using `[← this]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[algebraMap_smul, Submodule.coe_smul, Basis.extendOfIsLattice_apply]`.

Rewrite using `[e, bC.repr_sum_self]`. Set `Hm : Matrix (Fin g) (Ix E N) O` to `fun k m => bo.repr ⟨P.ht (B m), P.ht_mem _ (hB m)⟩ k`. Establish `hHm : ∀ k m, algebraMap O C (Hm k m) = bC.repr (P.ht (B m)) k` using `fun k m => (hbC ⟨_, P.ht_mem _ (hB m)⟩ k).symm`. Use `⟨Hm, Matrix.of Eg, ?_, ?_, ⟨Matrix.of Ei, ?_, ?_⟩, fun m m' => by rw [hBt, hBt]; exact hEg m m', fun m => ⟨by rw [hBt]; exact P.ht_mem _ (hB m), fun k => by simp only [Hm, hBt]⟩⟩` and prove the remaining obligations. Establish `hsurj : LinearMap.range P.ht = ⊤`.

Rewrite using `[eq_top_iff, ← bC.span_eq, Submodule.span_le]`. Introduce and unpack `_ ⟨k, rfl⟩`. Take `⟨x, -, hx⟩` from `P.κ_mem _ (bo k).2`. Use `⟨(algebraMap O C κ)⁻¹ • x, ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul, hx, ← algebraMap_smul C κ, inv_smul_smul₀ P.κ_ne]`.

Conclude with `(Basis.extendOfIsLattice_apply C bo k).symm`. Establish `h1` using `LinearMap.finrank_range_add_finrank_ker P.ht`. Rewrite `h1` using `[hsurj, finrank_top, finrank_eq_card_basis bC, finrank_eq_card_basis B, Fintype.card_fin]`. Establish `horth : LinearMap.BilinForm.orthogonal P.e (LinearMap.ker P.ht) = LinearMap.ker P.ht`. Use extensionality with `x`.

Rewrite using `[LinearMap.BilinForm.mem_orthogonal_iff, LinearMap.mem_ker, P.lagr]`. Use `forall_congr' fun y => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.mem_ker]`. Use `imp_congr_right fun _ => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `P.e y x = 0 ↔ _`.

Rewrite using `[pt_swap P y x, neg_eq_zero]`. Establish `h2` using `LinearMap.BilinForm.finrank_orthogonal (B := P.e) ⟨hnd, P.nondeg⟩ (LinearMap.ker P.ht)`. Rewrite `h2` using `[horth, finrank_eq_card_basis B]`. Use linear arithmetic over natural numbers and integers. Use extensionality with `m m'`.

Apply `hinj` to reduce the goal to its premises. Simplify using `only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.of_apply, map_neg, hEg]`. Conclude with `pt_swap P _ _`. Use extensionality with `m m'`. Apply `hinj` to reduce the goal to its premises.

Establish `h` using `congrArg (fun f : Module.Dual C V => f (B m')) (hw m)`. Simplify using `only [← hEi m, map_sum, LinearMap.sum_apply, LinearMap.map_smul_of_tower, LinearMap.smul_apply, Basis.coord_apply, Basis.repr_self, ← hEg] at h`. Rewrite using `[Matrix.mul_apply, map_sum]`. Simplify using `only [Matrix.of_apply, map_mul, ← Algebra.smul_def]`. Rewrite using `[h, Matrix.one_apply, Finsupp.single_apply]`.

Distinguish the cases in `hm : m = m'`. Simplify using `[hm]`. Simplify using `[hm, Ne.symm hm]`. Use extensionality with `k k'`. Apply `hinj` to reduce the goal to its premises.

Set `x : V` to `∑ m, algebraMap O C (Hm k m) • w m`. Establish `hx : P.e x = (bC.coord k) ∘ₗ P.ht`. Use `B.ext fun m => ?_` and prove the remaining obligations. Simplify using `only [x, map_sum, map_smul, hw, LinearMap.sum_apply, LinearMap.smul_apply, Basis.coord_apply, Basis.repr_self, LinearMap.comp_apply, Finsupp.single_apply]`. Rewrite using `[Finset.sum_eq_single m (fun b _ hb => by simp [Ne.symm hb]) (by simp)]`.

Simplify using `[hHm]`. Establish `h0 : P.ht x = 0` using `(P.lagr x).2 fun y hy => by rw [hx, LinearMap.comp_apply, hy, map_zero]`. Establish `h1` using `congrArg (fun z => bC.repr z k') h0`. Simplify using `only [x, ← hEi, map_sum, map_smul, LinearMap.map_smul_of_tower, Finsupp.coe_finset_sum, Finset.sum_apply, map_zero, Finsupp.coe_zero, Pi.zero_apply] at h1`. Rewrite using `[Matrix.zero_apply, map_zero, ← h1]`.

Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, map_sum, map_mul, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Simplify using `only [Finsupp.smul_apply, Finsupp.coe_finset_sum, Finset.sum_apply, smul_eq_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m' _ => ?_` and prove the remaining obligations.

Rewrite using `[hHm k' m', ← algebraMap_smul C (Ei m m'), map_smul, Finsupp.smul_apply, smul_eq_mul, mul_assoc]`.
-/
theorem pt_matrices {v : Valuation C NNReal} (hv : v.Integers O) (P : HTPoint C O c κ N V Ω') {g : ℕ}
    (bo : Basis (Fin g) O P.om) :
    ∃ (Hm : Matrix (Fin g) (Ix E N) O) (Eg : Matrix (Ix E N) (Ix E N) O),
      Fintype.card (Ix E N) = g + g ∧ Egᵀ = -Eg ∧
      (∃ Ei : Matrix (Ix E N) (Ix E N) O, Ei * Eg = 1 ∧ Hm * Ei * Hmᵀ = 0) ∧
      (∀ m m', algebraMap O C (Eg m m') = P.e (P.tate (dl m)) (P.tate (dl m'))) ∧
      ∀ m, ∃ h : P.ht (P.tate (dl m)) ∈ P.om, ∀ k, Hm k m = bo.repr ⟨_, h⟩ k := by
  classical
  haveI : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  haveI := PositivityTheory.HtPt.Gb.isFractionRing_of_integers hv
  haveI := P.om_lat
  have hinj := hv.hom_inj
  have hsp : ⊤ ≤ Submodule.span C (Set.range fun q : Ix E N =>
      P.ρ (RingOfIntegers.basis E q.2) (P.t q.1)) := by
    rw [← Submodule.span_span_of_tower O C, ← P.free.2.2, P.free.2.1]
  let B : Basis (Ix E N) C V := Basis.mk P.free.1 hsp
  have hBt : ∀ m, P.tate (dl m) = B m := fun m => by rw [pt_tate, Basis.mk_apply]
  have hT : P.T = Submodule.span O (Set.range B) := by rw [Basis.coe_mk, ← P.free.2.2]
  have hB : ∀ q, B q ∈ P.T := fun q => by
    rw [hT]
    exact Submodule.subset_span ⟨q, rfl⟩
  haveI : FiniteDimensional C V := Module.Finite.of_basis B
  have hnd : ∀ x, (∀ y, P.e x y = 0) → x = 0 := fun x hx =>
    P.nondeg x fun y => by rw [pt_swap, hx, neg_zero]
  have hei : Function.Injective (P.e : V →ₗ[C] Module.Dual C V) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    exact hnd x fun y => by rw [hx]; rfl
  have hes := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (Subspace.dual_finrank_eq).symm).1 hei
  have hE : ∀ m m', ∃ r : O, algebraMap O C r = P.e (B m) (B m') := fun m m' => by
    have := hB m'
    rw [← P.perfect] at this
    exact this _ (hB m)
  choose Eg hEg using hE
  choose w hw using fun m => hes (B.coord m)
  have hwT : ∀ m, w m ∈ P.T := fun m => by
    rw [← P.perfect]
    intro x hx
    rw [pt_swap, hw]
    refine neg_mem ?_
    rw [hT] at hx
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 hx
    refine ⟨a m, ?_⟩
    simp only [map_sum, LinearMap.map_smul_of_tower, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
    rw [Finset.sum_eq_single m (fun b _ hb => by simp [hb]) (by simp)]
    simp [Algebra.smul_def]
  choose Ei hEi using fun m => (Submodule.mem_span_range_iff_exists_fun O).1 (hT ▸ hwT m)
  let bC := bo.extendOfIsLattice C
  have hbC : ∀ (y : P.om) k, bC.repr (y : Ω') k = algebraMap O C (bo.repr y k) := fun y k => by
    have e : (y : Ω') = ∑ j, algebraMap O C (bo.repr y j) • bC j := by
      have := congrArg Subtype.val (bo.sum_repr y)
      rw [Submodule.coe_sum] at this
      rw [← this]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [algebraMap_smul, Submodule.coe_smul, Basis.extendOfIsLattice_apply]
    rw [e, bC.repr_sum_self]
  let Hm : Matrix (Fin g) (Ix E N) O := fun k m => bo.repr ⟨P.ht (B m), P.ht_mem _ (hB m)⟩ k
  have hHm : ∀ k m, algebraMap O C (Hm k m) = bC.repr (P.ht (B m)) k := fun k m =>
    (hbC ⟨_, P.ht_mem _ (hB m)⟩ k).symm
  refine ⟨Hm, Matrix.of Eg, ?_, ?_, ⟨Matrix.of Ei, ?_, ?_⟩, fun m m' => by rw [hBt, hBt]; exact hEg m m',
    fun m => ⟨by rw [hBt]; exact P.ht_mem _ (hB m), fun k => by simp only [Hm, hBt]⟩⟩
  · have hsurj : LinearMap.range P.ht = ⊤ := by
      rw [eq_top_iff, ← bC.span_eq, Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      obtain ⟨x, -, hx⟩ := P.κ_mem _ (bo k).2
      refine ⟨(algebraMap O C κ)⁻¹ • x, ?_⟩
      rw [map_smul, hx, ← algebraMap_smul C κ, inv_smul_smul₀ P.κ_ne]
      exact (Basis.extendOfIsLattice_apply C bo k).symm
    have h1 := LinearMap.finrank_range_add_finrank_ker P.ht
    rw [hsurj, finrank_top, finrank_eq_card_basis bC, finrank_eq_card_basis B, Fintype.card_fin] at h1
    have horth : LinearMap.BilinForm.orthogonal P.e (LinearMap.ker P.ht) = LinearMap.ker P.ht := by
      ext x
      rw [LinearMap.BilinForm.mem_orthogonal_iff, LinearMap.mem_ker, P.lagr]
      refine forall_congr' fun y => ?_
      rw [LinearMap.mem_ker]
      refine imp_congr_right fun _ => ?_
      change P.e y x = 0 ↔ _
      rw [pt_swap P y x, neg_eq_zero]
    have h2 := LinearMap.BilinForm.finrank_orthogonal (B := P.e) ⟨hnd, P.nondeg⟩ (LinearMap.ker P.ht)
    rw [horth, finrank_eq_card_basis B] at h2
    omega
  · ext m m'
    apply hinj
    simp only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.of_apply, map_neg, hEg]
    exact pt_swap P _ _
  · ext m m'
    apply hinj
    have h := congrArg (fun f : Module.Dual C V => f (B m')) (hw m)
    simp only [← hEi m, map_sum, LinearMap.sum_apply, LinearMap.map_smul_of_tower, LinearMap.smul_apply,
      Basis.coord_apply, Basis.repr_self, ← hEg] at h
    rw [Matrix.mul_apply, map_sum]
    simp only [Matrix.of_apply, map_mul, ← Algebra.smul_def]
    rw [h, Matrix.one_apply, Finsupp.single_apply]
    by_cases hm : m = m'
    · simp [hm]
    · simp [hm, Ne.symm hm]
  · ext k k'
    apply hinj
    let x : V := ∑ m, algebraMap O C (Hm k m) • w m
    have hx : P.e x = (bC.coord k) ∘ₗ P.ht := by
      refine B.ext fun m => ?_
      simp only [x, map_sum, map_smul, hw, LinearMap.sum_apply, LinearMap.smul_apply, Basis.coord_apply,
        Basis.repr_self, LinearMap.comp_apply, Finsupp.single_apply]
      rw [Finset.sum_eq_single m (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
      simp [hHm]
    have h0 : P.ht x = 0 := (P.lagr x).2 fun y hy => by rw [hx, LinearMap.comp_apply, hy, map_zero]
    have h1 := congrArg (fun z => bC.repr z k') h0
    simp only [x, ← hEi, map_sum, map_smul, LinearMap.map_smul_of_tower, Finsupp.coe_finset_sum, Finset.sum_apply,
      map_zero, Finsupp.coe_zero, Pi.zero_apply] at h1
    rw [Matrix.zero_apply, map_zero, ← h1]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, map_sum, map_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [Finsupp.smul_apply, Finsupp.coe_finset_sum, Finset.sum_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m' _ => ?_
    rw [hHm k' m', ← algebraMap_smul C (Ei m m'), map_smul, Finsupp.smul_apply, smul_eq_mul, mul_assoc]

end Pt

/- English proof (translation)
Use `haveI : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)`. Use `haveI := PositivityTheory.HtPt.Gd.free_of_fg hv P.om P.om_lat.fg`. Use `haveI : Module.Finite O P.om := Module.Finite.iff_fg.2 P.om_lat.fg`. Set `bo` to `Module.finBasis O P.om`. Establish `hmem : ∀ u, ι₀ u ∈ P.om` using `fun u => by`.

Rewrite using `[← hr.span_eq]`. Conclude with `Submodule.subset_span ⟨u, rfl⟩`. Set `ι₁ : D.om →ₛₗ[algebraMap A O] P.om` to `ι₀.codRestrict P.om hmem`. Set `io : D.om →ₛₗ[algebraMap A O] (Fin _ → O)` to `bo.equivFun.toLinearMap.comp ι₁`. Establish `hio : ∀ u k, io u k = bo.repr ⟨ι₀ u, hmem u⟩ k` using `fun _ _ => rfl`.

Take `⟨Hm, Eg, h1, h2, h3, h4, h5⟩` from `pt_matrices hv P bo`. Take `⟨j, hj, hjr, hjι⟩` from `PositivityTheory.HtPt.Gb.bc_iso A K Ω D.om C v O hv Ω' P.om ι₀ D.om_lat D.om_proj P.om_lat hr.span_eq hr.rank_eq`. Establish `hpR : ∀ z : O, (p : O) ^ R * z ∈ Ideal.span {(p : O)}` using `fun z => Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) _ hR)`. Use `⟨_, io, Hm, Eg, ?_, fun f => ?_, h1, h2, h3, fun m m' => ?_, fun m k => ?_⟩` and prove the remaining obligations. Establish `h6 : Submodule.span O (Set.range ι₁) = ⊤`.

Apply `Submodule.map_injective_of_injective P.om.injective_subtype` to reduce the goal to its premises. Rewrite using `[Submodule.map_span, ← Set.range_comp, Submodule.map_top, Submodule.range_subtype]`. Conclude with `hr.span_eq`. Establish `: Set.range io = bo.equivFun.toLinearMap '' Set.range ι₁`. Rewrite using `[← Set.range_comp]`.

Both sides reduce to the same expression. Rewrite using `[this, ← Submodule.map_span, h6, Submodule.map_top, LinearEquiv.range]`. Take `⟨jf, hjf, -⟩` from `PositivityTheory.HtPt.Gb.exists_lift f`. Set `e : (O ⊗[A] D.om) ≃ₗ[O] P.om` to `(LinearEquiv.ofInjective j hj).trans (LinearEquiv.ofEq _ _ hjr)`. Establish `he : ∀ u, e (1 ⊗ₜ u) = ⟨ι₀ u, hmem u⟩` using `fun u => Subtype.ext (hjι u)`.

Use `⟨Fintype.linearCombination C fun k => jf (e.symm (bo k)), fun u => ?_⟩` and prove the remaining obligations. Rewrite using `[Fintype.linearCombination_apply, ← hjf, ← e.symm_apply_apply (1 ⊗ₜ u), he]`. Use `conv_rhs => rw [← bo.sum_repr ⟨ι₀ u, hmem u⟩]`. Simplify using `only [map_sum, map_smul, hio, algebraMap_smul]`. Take `⟨z, hz⟩` from `hr.e_eq (dl m) (dl m')`.

Rewrite using `[hv.hom_inj ((h4 m m').trans hz), add_sub_cancel_left]`. Conclude with `hpR z`. Take `⟨h, hk⟩` from `h5 m`. Take `⟨y, hy, hz⟩` from `hr.ht_eq (dl m)`. Establish `: (⟨ι₀ ⟨D.h (dl m), D.h_mem _⟩, hmem _⟩ : P.om) = ⟨_, h⟩ + (p : O) ^ R • ⟨y, hy⟩`.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[Submodule.coe_add, Submodule.coe_smul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]`. Conclude with `hz`. Rewrite using `[hk, hio, this, map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, sub_add_cancel_left]`. Conclude with `neg_mem (hpR _)`.
-/
theorem chart_matrices {A K : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
    {E : Type} [Field E] [NumberField E] {c : E ≃+* E} {p R N : ℕ} (hR : 1 ≤ R)
    {Ω : Type} [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω)
    {C O : Type} [Field C] [CommRing O] [Algebra O C] [Algebra A O] {κ : O}
    {V Ω' : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]
    [AddCommGroup Ω'] [Module C Ω'] [Module O Ω'] [IsScalarTower O C Ω']
    {v : Valuation C NNReal} (hv : v.Integers O) (P : HTPoint C O c κ N V Ω')
    (ι₀ : D.om →ₛₗ[algebraMap A O] Ω') (hr : D.ReducesTo (algebraMap A O) P ι₀) :
    ∃ (g : ℕ) (io : D.om →ₛₗ[algebraMap A O] (Fin g → O)) (Hm : Matrix (Fin g) (Ix E N) O)
      (Eg : Matrix (Ix E N) (Ix E N) O),
      Submodule.span O (Set.range io) = ⊤ ∧
      (∀ f : D.om →ₛₗ[algebraMap A O] C, ∃ ev : (Fin g → C) →ₗ[C] C,
        ∀ u, ev (fun k => algebraMap O C (io u k)) = f u) ∧
      Fintype.card (Ix E N) = g + g ∧ Egᵀ = -Eg ∧
      (∃ Ei : Matrix (Ix E N) (Ix E N) O, Ei * Eg = 1 ∧ Hm * Ei * Hmᵀ = 0) ∧
      (∀ m m', Eg m m' - ((D.e (dl m) (dl m')).val : O) ∈ Ideal.span {(p : O)}) ∧
      ∀ m k, Hm k m - io ⟨D.h (dl m), D.h_mem _⟩ k ∈ Ideal.span {(p : O)} := by
  classical
  haveI : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  haveI := PositivityTheory.HtPt.Gd.free_of_fg hv P.om P.om_lat.fg
  haveI : Module.Finite O P.om := Module.Finite.iff_fg.2 P.om_lat.fg
  let bo := Module.finBasis O P.om
  have hmem : ∀ u, ι₀ u ∈ P.om := fun u => by
    rw [← hr.span_eq]
    exact Submodule.subset_span ⟨u, rfl⟩
  let ι₁ : D.om →ₛₗ[algebraMap A O] P.om := ι₀.codRestrict P.om hmem
  let io : D.om →ₛₗ[algebraMap A O] (Fin _ → O) := bo.equivFun.toLinearMap.comp ι₁
  have hio : ∀ u k, io u k = bo.repr ⟨ι₀ u, hmem u⟩ k := fun _ _ => rfl
  obtain ⟨Hm, Eg, h1, h2, h3, h4, h5⟩ := pt_matrices hv P bo
  obtain ⟨j, hj, hjr, hjι⟩ := PositivityTheory.HtPt.Gb.bc_iso A K Ω D.om C v O hv Ω' P.om ι₀ D.om_lat D.om_proj P.om_lat
    hr.span_eq hr.rank_eq
  have hpR : ∀ z : O, (p : O) ^ R * z ∈ Ideal.span {(p : O)} := fun z =>
    Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) _ hR)
  refine ⟨_, io, Hm, Eg, ?_, fun f => ?_, h1, h2, h3, fun m m' => ?_, fun m k => ?_⟩
  · have h6 : Submodule.span O (Set.range ι₁) = ⊤ := by
      apply Submodule.map_injective_of_injective P.om.injective_subtype
      rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, Submodule.range_subtype]
      exact hr.span_eq
    have : Set.range io = bo.equivFun.toLinearMap '' Set.range ι₁ := by
      rw [← Set.range_comp]; rfl
    rw [this, ← Submodule.map_span, h6, Submodule.map_top, LinearEquiv.range]
  · obtain ⟨jf, hjf, -⟩ := PositivityTheory.HtPt.Gb.exists_lift f
    let e : (O ⊗[A] D.om) ≃ₗ[O] P.om := (LinearEquiv.ofInjective j hj).trans (LinearEquiv.ofEq _ _ hjr)
    have he : ∀ u, e (1 ⊗ₜ u) = ⟨ι₀ u, hmem u⟩ := fun u => Subtype.ext (hjι u)
    refine ⟨Fintype.linearCombination C fun k => jf (e.symm (bo k)), fun u => ?_⟩
    rw [Fintype.linearCombination_apply, ← hjf, ← e.symm_apply_apply (1 ⊗ₜ u), he]
    conv_rhs => rw [← bo.sum_repr ⟨ι₀ u, hmem u⟩]
    simp only [map_sum, map_smul, hio, algebraMap_smul]
  · obtain ⟨z, hz⟩ := hr.e_eq (dl m) (dl m')
    rw [hv.hom_inj ((h4 m m').trans hz), add_sub_cancel_left]
    exact hpR z
  · obtain ⟨h, hk⟩ := h5 m
    obtain ⟨y, hy, hz⟩ := hr.ht_eq (dl m)
    have : (⟨ι₀ ⟨D.h (dl m), D.h_mem _⟩, hmem _⟩ : P.om) = ⟨_, h⟩ + (p : O) ^ R • ⟨y, hy⟩ := by
      apply Subtype.ext
      rw [Submodule.coe_add, Submodule.coe_smul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
      exact hz
    rw [hk, hio, this, map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, sub_add_cancel_left]
    exact neg_mem (hpR _)

end PositivityTheory.Xgn.TestGroupPoint
