import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermLat
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommensurableCosetUnionContentBiUnionStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TupleJacobianRightMulIsometryStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MatrixCongruentOneModUniformizerPowGroupAndOrbitStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.ThickSplit

/- English proof (translation)
Establish `hidx : N.relIndex H * (N ⊔ H).index = N.index`. Rewrite using `[← Subgroup.relIndex_sup_left H N]`. Conclude with `Subgroup.relIndex_mul_index le_sup_left`. Establish `hJ : (N ⊔ H).index ≠ 0`. Introduce `h`.

Rewrite `hidx` using `[h, mul_zero]`. Conclude with `hN hidx.symm`. Use `haveI : (N ⊔ H).FiniteIndex := ⟨hJ⟩`. Use `haveI : Fintype (Γ ⧸ (N ⊔ H)) := Fintype.ofFinite _`. Establish `hU : (⋃ a, S a) = ⋃ q ∈ (Finset.univ : Finset (Γ ⧸ (N ⊔ H))), S q.out`.

Use extensionality with `w`. Simplify using `only [Set.mem_iUnion, Finset.mem_univ, exists_true_left]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha⟩`. Use `⟨(a : Γ ⧸ (N ⊔ H)), ?_⟩` and prove the remaining obligations.

Rewrite using `[heq _ a (QuotientGroup.eq.1 (QuotientGroup.out_eq' _))]`. Conclude with `ha`. Introduce and unpack `⟨q, hq⟩`. Conclude with `⟨_, hq⟩`. Rewrite using `[hU, (GlobalTheory.T.commensurableCosetUnionContent_biUnion W0 Finset.univ (fun q : Γ ⧸ (N ⊔ H) => S q.out) (fun q _ => hco _)).2]`.

Simplify using `only [hc, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`. Rewrite using `[← hidx, Subgroup.index, Nat.card_eq_fintype_card]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Introduce `q _ r _ hqr`.

Assume the negation of the conclusion as `h`. Apply `hqr` to reduce the goal to its premises. Use `QuotientGroup.eq.2 (hdis _ _ h)` as an intermediate fact. Rewrite `this` using `[QuotientGroup.out_eq', QuotientGroup.out_eq']`. Then use the resulting hypothesis.
-/
theorem cont_iUnion_cosets {W : Type} [AddCommGroup W] (W0 : AddSubgroup W) {Γ : Type} [Group Γ]
    (N H : Subgroup Γ) [N.Normal] (hN : N.index ≠ 0) (S : Γ → Set W) (c : ℝ)
    (hco : ∀ a, IsCO W0 (S a)) (hc : ∀ a, cont W0 (S a) = c)
    (heq : ∀ a b, a⁻¹ * b ∈ N ⊔ H → S a = S b)
    (hdis : ∀ a b, ¬ Disjoint (S a) (S b) → a⁻¹ * b ∈ N ⊔ H) :
    cont W0 (⋃ a, S a) * (N.relIndex H : ℝ) = (N.index : ℝ) * c := by
  have hidx : N.relIndex H * (N ⊔ H).index = N.index := by
    rw [← Subgroup.relIndex_sup_left H N]
    exact Subgroup.relIndex_mul_index le_sup_left
  have hJ : (N ⊔ H).index ≠ 0 := by
    intro h
    rw [h, mul_zero] at hidx
    exact hN hidx.symm
  haveI : (N ⊔ H).FiniteIndex := ⟨hJ⟩
  haveI : Fintype (Γ ⧸ (N ⊔ H)) := Fintype.ofFinite _
  have hU : (⋃ a, S a) = ⋃ q ∈ (Finset.univ : Finset (Γ ⧸ (N ⊔ H))), S q.out := by
    ext w
    simp only [Set.mem_iUnion, Finset.mem_univ, exists_true_left]
    constructor
    · rintro ⟨a, ha⟩
      refine ⟨(a : Γ ⧸ (N ⊔ H)), ?_⟩
      rw [heq _ a (QuotientGroup.eq.1 (QuotientGroup.out_eq' _))]
      exact ha
    · rintro ⟨q, hq⟩
      exact ⟨_, hq⟩
  rw [hU, (GlobalTheory.T.commensurableCosetUnionContent_biUnion W0 Finset.univ (fun q : Γ ⧸ (N ⊔ H) => S q.out) (fun q _ => hco _)).2]
  · simp only [hc, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← hidx, Subgroup.index, Nat.card_eq_fintype_card]
    push_cast
    ring
  · intro q _ r _ hqr
    by_contra h
    apply hqr
    have := QuotientGroup.eq.2 (hdis _ _ h)
    rwa [QuotientGroup.out_eq', QuotientGroup.out_eq'] at this

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

/- English proof (translation)
Use function extensionality and compare the values at `j`. Simplify using `only [rmul, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm]`.
-/
theorem rmul_rmul {n m : ℕ} (x : Fin m → Fin n → E) (A B : Matrix (Fin m) (Fin m) E) :
    rmul (rmul x A) B = rmul x (A * B) := by
  funext j
  simp only [rmul, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm]

/- English proof (translation)
Use function extensionality and compare the values at `j`. Simplify using `[rmul, Matrix.one_apply]`.
-/
theorem rmul_one {n m : ℕ} (x : Fin m → Fin n → E) : rmul x 1 = x := by
  funext j
  simp [rmul, Matrix.one_apply]

/- English proof (translation)
Use function extensionality and compare the values at `j`. Simplify using `[rmul]`.
-/
theorem map_rmul {n m : ℕ} (g : (Fin n → E) ≃ₗ[E] (Fin n → E)) (x : Fin m → Fin n → E)
    (A : Matrix (Fin m) (Fin m) E) : (fun a => g (rmul x A a)) = rmul (fun a => g (x a)) A := by
  funext j
  simp [rmul]

/- English proof (translation)
Simplify using `only [hf, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Fintype.sum_prod_type_right]`.

Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Use `_ = _ := by`. Rewrite using `[Finset.sum_comm, Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[Fintype.sum_prod_type]`.
-/
theorem hf_sum_sum (L : LocE F E) {n m : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (x : Fin m → Fin n → E) (u v : Fin m → E) :
    hf L Hm (∑ i, u i • x i) (∑ j, v j • x j) = ∑ i, ∑ j, u i * L.cj (v j) * hf L Hm (x i) (x j) := by
  simp only [hf, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.sum_mul,
    Finset.mul_sum]
  calc _ = ∑ p : Fin n × Fin n, ∑ q : Fin m × Fin m,
        u q.1 * L.cj (v q.2) * (x q.1 p.1 * Hm p.1 p.2 * L.cj (x q.2 p.2)) := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
        rw [Fintype.sum_prod_type_right]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
        ring
    _ = _ := by
        rw [Finset.sum_comm, Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
        rw [Fintype.sum_prod_type]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [gramT, rmul, Matrix.of_apply, hf_sum_sum, Matrix.mul_apply, cT, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gramT_rmul (L : LocE F E) {n m : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (x : Fin m → Fin n → E) (A : Matrix (Fin m) (Fin m) E) :
    gramT L Hm (rmul x A) = cT L A * gramT L Hm x * A := by
  ext a b
  simp only [gramT, rmul, Matrix.of_apply, hf_sum_sum, Matrix.mul_apply, cT, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, _, h3⟩`. Use `⟨h1, fun a => ?_⟩` and prove the remaining obligations. Use `h3 (x a) (Submodule.subset_span ⟨a, rfl⟩)` as an intermediate fact. Conclude with `sub_eq_zero.1 ((Submodule.mem_bot E).1 this)`.

Introduce and unpack `⟨h1, h2⟩`. Establish `key : ∀ v ∈ Submodule.span E (Set.range x), g v = v`. Introduce `v hv`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem v hv => obtain ⟨a, rfl⟩ := hv`.

Conclude with `h2 a`. Consider the case `zero => simp`. Consider the case `add u v _ _ hu hv => rw [map_add, hu, hv]`. Consider the case `smul c v _ hv => rw [map_smul, hv]`. Use `⟨h1, fun v => ⟨fun hv => ?_, fun hv => by rw [key v hv]; exact hv⟩, fun v hv => ?_⟩` and prove the remaining obligations.

Use `g.injective (key _ hv)` as an intermediate fact. Rewrite `hv` using `[this]`. Then use the resulting hypothesis. Rewrite using `[key v hv, sub_self]`. Conclude with `Submodule.zero_mem _`.
-/
theorem mem_fixG (L : LocE F E) {n m : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (x : Fin m → Fin n → E) (g : (Fin n → E) ≃ₗ[E] (Fin n → E)) :
    g ∈ fixG L Hm (Submodule.span E (Set.range x)) ↔ g ∈ isomG L Hm ∧ ∀ a, g (x a) = x a := by
  constructor
  · rintro ⟨h1, _, h3⟩
    refine ⟨h1, fun a => ?_⟩
    have := h3 (x a) (Submodule.subset_span ⟨a, rfl⟩)
    exact sub_eq_zero.1 ((Submodule.mem_bot E).1 this)
  · rintro ⟨h1, h2⟩
    have key : ∀ v ∈ Submodule.span E (Set.range x), g v = v := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem v hv => obtain ⟨a, rfl⟩ := hv; exact h2 a
      | zero => simp
      | add u v _ _ hu hv => rw [map_add, hu, hv]
      | smul c v _ hv => rw [map_smul, hv]
    refine ⟨h1, fun v => ⟨fun hv => ?_, fun hv => by rw [key v hv]; exact hv⟩, fun v hv => ?_⟩
    · have := g.injective (key _ hv)
      rwa [this] at hv
    · rw [key v hv, sub_self]
      exact Submodule.zero_mem _
end

end GlobalTheory.HL.ThickSplit

open GlobalTheory.HL.ThickSplit in

/- English proof (translation)
Introduce `F _ _ _ _ _ E _ _ _ L ϖ hϖ n Hm hH Λs hΛ m x _ K K' hK hK' hnorm hidx i hi hstab hco`. Take `⟨-, hgrp, -⟩` from `GlobalTheory.T.matrixCongruentOneModUniformizerPow_group_and_orbits L ϖ hϖ m i hi`. Apply the tactic sequence `have hjac := (GlobalTheory.T.tuple_jacobian_rightMul_isometry L ϖ hϖ Hm hH Λs hΛ m).2`. Establish `hconj : ∀ a ∈ K, ∀ k ∈ K', a * k * a⁻¹ ∈ K'`. Introduce `a ha k hk`.

Rewrite using `[← hnorm a ha]`. Conclude with `Subgroup.smul_mem_pointwise_smul k (MulAut.conj a) K' hk`. Use `haveI : (K'.subgroupOf K).Normal := ⟨fun k hk a => hconj a a.2 k hk⟩`. Use `set Fx := fixG L Hm (Submodule.span E (Set.range x)) with hFx`. Establish `hsub : ∀ a b : K, a⁻¹ * b ∈ K'.subgroupOf K ⊔ Fx.subgroupOf K → (fun x c => (b : (Fin n → E) ≃ₗ[E] (Fin n → E)) (x c)) '' thick L ϖ (torb K' x) i ⊆ (fun x c => (a : (Fin n → E) ≃ₗ[E] (Fin n → E)) (x c)) '' thick L ϖ (torb K' x) i`.

Introduce `a b hab`. Take `⟨k, hk, h, hh, hkh⟩` from `Subgroup.mem_sup_of_normal_left.1 hab`. Establish `hb : b = a * (k * h)` using `by rw [hkh]; group`. Establish `hhx` using `((mem_fixG L Hm x h).1 hh).2`. Introduce and unpack `_ ⟨_, ⟨_, ⟨k1, hk1, rfl⟩, A, hA, rfl⟩, rfl⟩`.

Use `⟨_, ⟨_, ⟨k * (h * k1 * (h : (Fin n → E) ≃ₗ[E] (Fin n → E))⁻¹), K'.mul_mem hk (hconj h h.2 k1 hk1), rfl⟩, A, hA, rfl⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [map_rmul]`. Use `congr 1`. Use function extensionality and compare the values at `c`. Establish `: ((h : (Fin n → E) ≃ₗ[E] (Fin n → E))⁻¹) (x c) = x c` using `by conv_lhs => rw [← hhx c]`.

Conclude with `LinearEquiv.symm_apply_apply _ _`. Rewrite using `[hb]`. Simplify using `only [Subgroup.coe_mul, LinearEquiv.mul_apply, this]`. Establish `main` using `cont_iUnion_cosets (tupLat L Λs m) (K'.subgroupOf K) (Fx.subgroupOf K) hidx (fun a : K => (fun x c => (a : (Fin n → E) ≃ₗ[E] (Fin n → E)) (x c)) '' thick L ϖ (torb K' x) i) (cont (tupLat L Λs m) (thick L ϖ (torb K' x) i)) (fun a => (hjac a (hK a.2) _ hco).1) (fun a => (hjac a (hK …`. Establish `hU : thick L ϖ (torb K x) i = ⋃ a : K, (fun x c => (a : (Fin n → E) ≃ₗ[E] (Fin n → E)) (x c)) '' thick L ϖ (torb K' x) i`.

Use extensionality with `w`. Simplify using `only [Set.mem_iUnion]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨a, ha, rfl⟩, A, hA, rfl⟩`. Conclude with `⟨⟨a, ha⟩, _, ⟨x, ⟨1, K'.one_mem, rfl⟩, A, hA, rfl⟩, map_rmul a x A⟩`.

Introduce and unpack `⟨a, _, ⟨_, ⟨k, hk, rfl⟩, A, hA, rfl⟩, rfl⟩`. Conclude with `⟨_, ⟨a * k, K.mul_mem a.2 (hK' hk), rfl⟩, A, hA, map_rmul _ _ A⟩`. Establish `hI : (K'.subgroupOf K).relIndex (Fx.subgroupOf K) = (Fx ⊓ K').relIndex (Fx ⊓ K)`. Rewrite using `[← Subgroup.inf_subgroupOf_right Fx K, Subgroup.relIndex_subgroupOf inf_le_right, ← Subgroup.inf_relIndex_right K' (Fx ⊓ K)]`. Use `congr 1`.

Rewrite using `[inf_comm, inf_assoc, inf_eq_right.2 hK']`. Rewrite using `[hU, ← hI]`. Conclude with `main`. Introduce `a b hab`. Take `⟨w, ⟨_, ⟨_, ⟨k, hk, rfl⟩, A, hA, rfl⟩, rfl⟩, ⟨_, ⟨_, ⟨k', hk', rfl⟩, A', hA', rfl⟩, hw⟩⟩` from `Set.not_disjoint_iff.1 hab`.

Take `⟨-, hdet, -, hinv, -, -⟩` from `hgrp A' hA'`. Establish `hB : A * A'⁻¹ ∈ congK L ϖ m i` using `(hgrp A hA).2.2.2.2.1 _ hinv`. Use `set g : (Fin n → E) ≃ₗ[E] (Fin n → E) := k⁻¹ * (a : (Fin n → E) ≃ₗ[E] (Fin n → E))⁻¹ * b * k' with hg`. Establish `hgK : g ∈ K` using `K.mul_mem (K.mul_mem (K.mul_mem (K.inv_mem (hK' hk)) (K.inv_mem a.2)) b.2) (hK' hk')`. Establish `h1 : rmul (fun c => g (x c)) A' = rmul x A`.

Rewrite using `[← map_rmul]`. Use function extensionality and compare the values at `c`. Establish `h2` using `congrFun hw c`. Establish `h3` using `congrFun (map_rmul k' x A') c`. Establish `h4` using `congrFun (map_rmul k x A) c`.

Simplify using `only at h2 h3 h4`. Rewrite `h2` using `[← h3, ← h4]`. Rewrite using `[hg]`. Simplify using `only [LinearEquiv.mul_apply]`. Rewrite using `[h2]`.

Simplify using `[LinearEquiv.coe_inv]`. Establish `h2 : (fun c => g (x c)) = rmul x (A * A'⁻¹)`. Rewrite using `[← rmul_rmul, ← h1, rmul_rmul, Matrix.mul_nonsing_inv _ hdet, rmul_one]`. Establish `h3 : cT L (A * A'⁻¹) * gramT L Hm x * (A * A'⁻¹) = gramT L Hm x`. Rewrite using `[← gramT_rmul, ← h2]`.

Use extensionality with `c d`. Conclude with `hK hgK _ _`. Take `⟨k'', hk'', h4⟩` from `hstab x ⟨1, K'.one_mem, rfl⟩ _ hB h3`. Rewrite `h4` using `[← h2]`. Establish `hfix : k''⁻¹ * g ∈ Fx`.

Use `(mem_fixG L Hm x _).2 ⟨hK (K.mul_mem (K.inv_mem (hK' hk'')) hgK), fun c => ?_⟩` and prove the remaining obligations. Rewrite using `[LinearEquiv.mul_apply, congrFun h4 c]`. Conclude with `LinearEquiv.symm_apply_apply _ _`. Establish `hmem : ∀ u (hu : u ∈ K'), (⟨u, hK' hu⟩ : K) ∈ K'.subgroupOf K ⊔ Fx.subgroupOf K` using `fun u hu => Subgroup.mem_sup_left hu`. Establish `hmem' : (⟨k''⁻¹ * g, K.mul_mem (K.inv_mem (hK' hk'')) hgK⟩ : K) ∈ K'.subgroupOf K ⊔ Fx.subgroupOf K` using `Subgroup.mem_sup_right hfix`.

Establish `hfin` using `Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hmem k hk) (hmem k'' hk'')) hmem') (Subgroup.inv_mem _ (hmem k' hk'))`. Use `hfin using 1` and compare the differences between its conclusion and the goal. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [Subgroup.coe_mul, Subgroup.coe_inv, hg]`. Use `group`.
-/
theorem GlobalTheory.HL.cont_thick_torb_normal : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ Λs, IsSD L Hm Λs → ∀ (m : ℕ) (x : Fin m → Fin n → E), IsUnit (gramT L Hm x).det → ∀ K K' : Subgroup ((Fin n → E) ≃ₗ[E] (Fin n → E)), K ≤ isomG L Hm → K' ≤ K → (∀ a ∈ K, MulAut.conj a • K' = K') → K'.relIndex K ≠ 0 → ∀ i : ℕ, 1 ≤ i → (∀ y ∈ torb K' x, ∀ A ∈ congK L ϖ m i, cT L A * gramT L Hm x * A = gramT L Hm x → rmul y A ∈ torb K' x) → IsCO (tupLat L Λs m) (thick L ϖ (torb K' x) i) → cont (tupLat L Λs m) (thick L ϖ (torb K x) i) * ((fixG L Hm (Submodule.span E (Set.range x)) ⊓ K').relIndex (fixG L Hm (Submodule.span E (Set.range x)) ⊓ K) : ℝ) = (K'.relIndex K : ℝ) * cont (tupLat L Λs m) (thick L ϖ (torb K' x) i) := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ n Hm hH Λs hΛ m x _ K K' hK hK' hnorm hidx i hi hstab hco
  obtain ⟨-, hgrp, -⟩ := GlobalTheory.T.matrixCongruentOneModUniformizerPow_group_and_orbits L ϖ hϖ m i hi
  have hjac := (GlobalTheory.T.tuple_jacobian_rightMul_isometry L ϖ hϖ Hm hH Λs hΛ m).2
  have hconj : ∀ a ∈ K, ∀ k ∈ K', a * k * a⁻¹ ∈ K' := by
    intro a ha k hk
    rw [← hnorm a ha]
    exact Subgroup.smul_mem_pointwise_smul k (MulAut.conj a) K' hk
  haveI : (K'.subgroupOf K).Normal :=
    ⟨fun k hk a => hconj a a.2 k hk⟩
  set Fx := fixG L Hm (Submodule.span E (Set.range x)) with hFx
  have hsub : ∀ a b : K, a⁻¹ * b ∈ K'.subgroupOf K ⊔ Fx.subgroupOf K →
      (fun x c => (b : (Fin n → E) ≃ₗ[E] (Fin n → E)) (x c)) '' thick L ϖ (torb K' x) i ⊆
      (fun x c => (a : (Fin n → E) ≃ₗ[E] (Fin n → E)) (x c)) '' thick L ϖ (torb K' x) i := by
    intro a b hab
    obtain ⟨k, hk, h, hh, hkh⟩ := Subgroup.mem_sup_of_normal_left.1 hab
    have hb : b = a * (k * h) := by rw [hkh]; group
    have hhx := ((mem_fixG L Hm x h).1 hh).2
    rintro _ ⟨_, ⟨_, ⟨k1, hk1, rfl⟩, A, hA, rfl⟩, rfl⟩
    refine ⟨_, ⟨_, ⟨k * (h * k1 * (h : (Fin n → E) ≃ₗ[E] (Fin n → E))⁻¹),
      K'.mul_mem hk (hconj h h.2 k1 hk1), rfl⟩, A, hA, rfl⟩, ?_⟩
    simp only [map_rmul]
    congr 1
    funext c
    have : ((h : (Fin n → E) ≃ₗ[E] (Fin n → E))⁻¹) (x c) = x c := by
      conv_lhs => rw [← hhx c]
      exact LinearEquiv.symm_apply_apply _ _
    rw [hb]
    simp only [Subgroup.coe_mul, LinearEquiv.mul_apply, this]
  have main := cont_iUnion_cosets (tupLat L Λs m) (K'.subgroupOf K) (Fx.subgroupOf K) hidx
    (fun a : K => (fun x c => (a : (Fin n → E) ≃ₗ[E] (Fin n → E)) (x c)) '' thick L ϖ (torb K' x) i)
    (cont (tupLat L Λs m) (thick L ϖ (torb K' x) i))
    (fun a => (hjac a (hK a.2) _ hco).1) (fun a => (hjac a (hK a.2) _ hco).2)
    (fun a b hab => Set.Subset.antisymm
      (hsub b a (by simpa using Subgroup.inv_mem _ hab)) (hsub a b hab)) ?_
  · have hU : thick L ϖ (torb K x) i = ⋃ a : K, (fun x c => (a : (Fin n → E) ≃ₗ[E] (Fin n → E)) (x c)) ''
        thick L ϖ (torb K' x) i := by
      ext w
      simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨_, ⟨a, ha, rfl⟩, A, hA, rfl⟩
        exact ⟨⟨a, ha⟩, _, ⟨x, ⟨1, K'.one_mem, rfl⟩, A, hA, rfl⟩, map_rmul a x A⟩
      · rintro ⟨a, _, ⟨_, ⟨k, hk, rfl⟩, A, hA, rfl⟩, rfl⟩
        exact ⟨_, ⟨a * k, K.mul_mem a.2 (hK' hk), rfl⟩, A, hA, map_rmul _ _ A⟩
    have hI : (K'.subgroupOf K).relIndex (Fx.subgroupOf K) = (Fx ⊓ K').relIndex (Fx ⊓ K) := by
      rw [← Subgroup.inf_subgroupOf_right Fx K, Subgroup.relIndex_subgroupOf inf_le_right,
        ← Subgroup.inf_relIndex_right K' (Fx ⊓ K)]
      congr 1
      rw [inf_comm, inf_assoc, inf_eq_right.2 hK']
    rw [hU, ← hI]
    exact main
  · intro a b hab
    obtain ⟨w, ⟨_, ⟨_, ⟨k, hk, rfl⟩, A, hA, rfl⟩, rfl⟩, ⟨_, ⟨_, ⟨k', hk', rfl⟩, A', hA', rfl⟩, hw⟩⟩ :=
      Set.not_disjoint_iff.1 hab
    obtain ⟨-, hdet, -, hinv, -, -⟩ := hgrp A' hA'
    have hB : A * A'⁻¹ ∈ congK L ϖ m i := (hgrp A hA).2.2.2.2.1 _ hinv
    set g : (Fin n → E) ≃ₗ[E] (Fin n → E) := k⁻¹ * (a : (Fin n → E) ≃ₗ[E] (Fin n → E))⁻¹ * b * k' with hg
    have hgK : g ∈ K := K.mul_mem (K.mul_mem (K.mul_mem (K.inv_mem (hK' hk)) (K.inv_mem a.2)) b.2) (hK' hk')
    have h1 : rmul (fun c => g (x c)) A' = rmul x A := by
      rw [← map_rmul]
      funext c
      have h2 := congrFun hw c
      have h3 := congrFun (map_rmul k' x A') c
      have h4 := congrFun (map_rmul k x A) c
      simp only at h2 h3 h4
      rw [← h3, ← h4] at h2
      rw [hg]
      simp only [LinearEquiv.mul_apply]
      rw [h2]
      simp [LinearEquiv.coe_inv]
    have h2 : (fun c => g (x c)) = rmul x (A * A'⁻¹) := by
      rw [← rmul_rmul, ← h1, rmul_rmul, Matrix.mul_nonsing_inv _ hdet, rmul_one]
    have h3 : cT L (A * A'⁻¹) * gramT L Hm x * (A * A'⁻¹) = gramT L Hm x := by
      rw [← gramT_rmul, ← h2]
      ext c d
      exact hK hgK _ _
    obtain ⟨k'', hk'', h4⟩ := hstab x ⟨1, K'.one_mem, rfl⟩ _ hB h3
    rw [← h2] at h4
    have hfix : k''⁻¹ * g ∈ Fx := by
      refine (mem_fixG L Hm x _).2 ⟨hK (K.mul_mem (K.inv_mem (hK' hk'')) hgK), fun c => ?_⟩
      rw [LinearEquiv.mul_apply, congrFun h4 c]
      exact LinearEquiv.symm_apply_apply _ _
    have hmem : ∀ u (hu : u ∈ K'), (⟨u, hK' hu⟩ : K) ∈ K'.subgroupOf K ⊔ Fx.subgroupOf K :=
      fun u hu => Subgroup.mem_sup_left hu
    have hmem' : (⟨k''⁻¹ * g, K.mul_mem (K.inv_mem (hK' hk'')) hgK⟩ : K) ∈
        K'.subgroupOf K ⊔ Fx.subgroupOf K := Subgroup.mem_sup_right hfix
    have hfin := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hmem k hk) (hmem k'' hk''))
      hmem') (Subgroup.inv_mem _ (hmem k' hk'))
    convert hfin using 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hg]
    group
