import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermLat
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommensurableCosetUnionContentBiUnionStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TupleJacobianRightMulIsometryStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianMatrixCongruenceContentJacobianStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MatrixCongruentOneModUniformizerPowGroupAndOrbitStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.ThickLevel

/- English proof (translation)
Establish `: (C.addSubgroupOf B).FiniteIndex` using `⟨h⟩`. Set `f : B ⧸ C.addSubgroupOf B →+ W ⧸ C` to `QuotientAddGroup.map _ _ B.subtype le_rfl`. Establish `hfin : (Set.range f).Finite` using `Set.finite_range _`. Use `(hT.biUnion (t := fun q => (fun z => (QuotientAddGroup.mk q.out : W ⧸ C) + z) '' Set.range f) (fun q _ => hfin.image _)).subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`.

Use `Set.mem_biUnion (x := (QuotientAddGroup.mk x : W ⧸ B)) ⟨x, hx, rfl⟩ ?_` and prove the remaining obligations. Establish `hb : -(QuotientAddGroup.mk x : W ⧸ B).out + x ∈ B`. Rewrite using `[← QuotientAddGroup.eq]`. Simplify using the standard rewrite rules. Use `⟨_, ⟨QuotientAddGroup.mk ⟨_, hb⟩, rfl⟩, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `(QuotientAddGroup.mk _ : W ⧸ C) + QuotientAddGroup.mk (-(QuotientAddGroup.mk x : W ⧸ B).out + x) = _`. Rewrite using `[← QuotientAddGroup.mk_add, add_neg_cancel_left]`.
-/
theorem finite_image_of_le {W : Type} [AddCommGroup W] (B C : AddSubgroup W) (h : C.relIndex B ≠ 0)
    (T : Set W) (hT : ((QuotientAddGroup.mk : W → W ⧸ B) '' T).Finite) :
    ((QuotientAddGroup.mk : W → W ⧸ C) '' T).Finite := by
  have : (C.addSubgroupOf B).FiniteIndex := ⟨h⟩
  let f : B ⧸ C.addSubgroupOf B →+ W ⧸ C := QuotientAddGroup.map _ _ B.subtype le_rfl
  have hfin : (Set.range f).Finite := Set.finite_range _
  refine (hT.biUnion (t := fun q => (fun z => (QuotientAddGroup.mk q.out : W ⧸ C) + z) '' Set.range f)
    (fun q _ => hfin.image _)).subset ?_
  rintro _ ⟨x, hx, rfl⟩
  refine Set.mem_biUnion (x := (QuotientAddGroup.mk x : W ⧸ B)) ⟨x, hx, rfl⟩ ?_
  have hb : -(QuotientAddGroup.mk x : W ⧸ B).out + x ∈ B := by
    rw [← QuotientAddGroup.eq]; simp
  refine ⟨_, ⟨QuotientAddGroup.mk ⟨_, hb⟩, rfl⟩, ?_⟩
  change (QuotientAddGroup.mk _ : W ⧸ C) + QuotientAddGroup.mk (-(QuotientAddGroup.mk x : W ⧸ B).out + x) = _
  rw [← QuotientAddGroup.mk_add, add_neg_cancel_left]

/- English proof (translation)
Take `⟨A, hA1, hA2, hA3, -⟩` from `hS`. Take `⟨B, hB1, hB2, hB3, hB4⟩` from `hT`. Use `⟨A ⊓ B, AddSubgroup.relIndex_inf_ne_zero hA1 hB1, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `h`. Conclude with `hA2 (AddSubgroup.relIndex_eq_zero_of_le_right inf_le_left h)`.

Introduce and unpack `x ⟨hx, hx'⟩ a ⟨ha, hb⟩`. Use `⟨hB3 x hx a hb, fun h => hx' ?_⟩` and prove the remaining obligations. Simplify using `using hA3 _ h (-a) (A.neg_mem ha)`. Use `(finite_image_of_le B (A ⊓ B) ?_ T hB4).subset (Set.image_mono Set.diff_subset)` and prove the remaining obligations. Rewrite using `[AddSubgroup.inf_relIndex_right]`.

Conclude with `AddSubgroup.relIndex_ne_zero_trans hA1 hB2`.
-/
theorem isCO_diff {W : Type} [AddCommGroup W] (W0 : AddSubgroup W) {S T : Set W}
    (hS : IsCO W0 S) (hT : IsCO W0 T) : IsCO W0 (T \ S) := by
  obtain ⟨A, hA1, hA2, hA3, -⟩ := hS
  obtain ⟨B, hB1, hB2, hB3, hB4⟩ := hT
  refine ⟨A ⊓ B, AddSubgroup.relIndex_inf_ne_zero hA1 hB1, ?_, ?_, ?_⟩
  · intro h
    exact hA2 (AddSubgroup.relIndex_eq_zero_of_le_right inf_le_left h)
  · rintro x ⟨hx, hx'⟩ a ⟨ha, hb⟩
    refine ⟨hB3 x hx a hb, fun h => hx' ?_⟩
    simpa using hA3 _ h (-a) (A.neg_mem ha)
  · refine (finite_image_of_le B (A ⊓ B) ?_ T hB4).subset (Set.image_mono Set.diff_subset)
    rw [AddSubgroup.inf_relIndex_right]
    exact AddSubgroup.relIndex_ne_zero_trans hA1 hB2

/- English proof (translation)
Unfold `cont relVol`. Use `split_ifs`. Check the signs of the components of the expression. Conclude with `le_rfl`.
-/
theorem cont_nonneg {W : Type} [AddCommGroup W] (W0 : AddSubgroup W) (S : Set W) : 0 ≤ cont W0 S := by
  unfold cont relVol
  split_ifs
  · positivity
  · exact le_rfl

/- English proof (translation)
Establish `h1` using `(GlobalTheory.T.commensurableCosetUnionContent_biUnion W0 (Finset.univ : Finset Bool) (fun b => if b then S else T \ S) (by rintro (_ | _) _`. Simplify using `using isCO_diff W0 hS hT`. Simplify using `using hS)).2`. Use the proof step `(by rintro (_ | _) _ (_ | _) _ hne`. Conclude with `absurd rfl hne`.

Simplify using `using Set.disjoint_sdiff_left`. Simplify using `using Set.disjoint_sdiff_right`. Conclude with `absurd rfl hne)`. Establish `h2 : (⋃ i ∈ (Finset.univ : Finset Bool), if i then S else T \ S) = T`. Use extensionality with `x`.

Simplify using `only [Finset.mem_univ, Set.iUnion_true, Set.mem_iUnion, Bool.exists_bool]`. Simplify using `only [Bool.false_eq_true, if_false, if_true, Set.mem_diff]`. Use `@h x` as an intermediate fact. The claim follows by propositional logic. Rewrite `h1` using `[h2]`.

Simplify using `at h1`. Use `cont_nonneg W0 (T \ S)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem cont_mono {W : Type} [AddCommGroup W] (W0 : AddSubgroup W) {S T : Set W}
    (hS : IsCO W0 S) (hT : IsCO W0 T) (h : S ⊆ T) : cont W0 S ≤ cont W0 T := by
  have h1 := (GlobalTheory.T.commensurableCosetUnionContent_biUnion W0 (Finset.univ : Finset Bool) (fun b => if b then S else T \ S)
    (by rintro (_ | _) _
        · simpa using isCO_diff W0 hS hT
        · simpa using hS)).2
    (by rintro (_ | _) _ (_ | _) _ hne
        · exact absurd rfl hne
        · simpa using Set.disjoint_sdiff_left
        · simpa using Set.disjoint_sdiff_right
        · exact absurd rfl hne)
  have h2 : (⋃ i ∈ (Finset.univ : Finset Bool), if i then S else T \ S) = T := by
    ext x
    simp only [Finset.mem_univ, Set.iUnion_true, Set.mem_iUnion, Bool.exists_bool]
    simp only [Bool.false_eq_true, if_false, if_true, Set.mem_diff]
    have := @h x
    tauto
  rw [h2] at h1
  simp at h1
  have := cont_nonneg W0 (T \ S)
  linarith

/- English proof (translation)
Assume the negation of the conclusion as `hinf`. Take `⟨N, hN⟩` from `exists_nat_gt (cont W0 T / c)`. Take `⟨s, hs, hcard⟩` from `Set.Infinite.exists_subset_card_eq hinf N`. Take `⟨h3, h4⟩` from `GlobalTheory.T.commensurableCosetUnionContent_biUnion W0 s (fun p => p) (fun p hp => (h1 p (hs hp)).1)`. Establish `h5` using `h4 (fun p hp q hq => h2 p (hs hp) q (hs hq))`.

Rewrite `h5` using `[Finset.sum_congr rfl (fun p hp => (h1 p (hs hp)).2.1), Finset.sum_const, hcard, nsmul_eq_mul]`. Establish `h6` using `cont_mono W0 h3 hT (Set.iUnion₂_subset fun p hp => (h1 p (hs hp)).2.2)`. Rewrite `hN` using `[div_lt_iff₀ hc]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem finite_pieces {W : Type} [AddCommGroup W] (W0 : AddSubgroup W) {T : Set W} (hT : IsCO W0 T)
    (P : Set (Set W)) (c : ℝ) (hc : 0 < c) (h1 : ∀ p ∈ P, IsCO W0 p ∧ cont W0 p = c ∧ p ⊆ T)
    (h2 : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → Disjoint p q) : P.Finite := by
  by_contra hinf
  obtain ⟨N, hN⟩ := exists_nat_gt (cont W0 T / c)
  obtain ⟨s, hs, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf N
  obtain ⟨h3, h4⟩ := GlobalTheory.T.commensurableCosetUnionContent_biUnion W0 s (fun p => p) (fun p hp => (h1 p (hs hp)).1)
  have h5 := h4 (fun p hp q hq => h2 p (hs hp) q (hs hq))
  rw [Finset.sum_congr rfl (fun p hp => (h1 p (hs hp)).2.1), Finset.sum_const, hcard, nsmul_eq_mul] at h5
  have h6 := cont_mono W0 h3 hT (Set.iUnion₂_subset fun p hp => (h1 p (hs hp)).2.2)
  rw [div_lt_iff₀ hc] at hN
  linarith

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[cT, Matrix.mul_apply, map_sum, mul_comm]`.
-/
theorem cT_mul (L : LocE F E) {m : ℕ} (A B : Matrix (Fin m) (Fin m) E) :
    cT L (A * B) = cT L B * cT L A := by
  ext i j
  simp [cT, Matrix.mul_apply, map_sum, mul_comm]

/- English proof (translation)
Use function extensionality and compare the values at `j`. Simplify using `only [rmul, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]`. Rewrite using `[Finset.sum_comm]`. Simplify using `[mul_comm]`.
-/
theorem rmul_rmul {n m : ℕ} (x : Fin m → Fin n → E) (A B : Matrix (Fin m) (Fin m) E) :
    rmul (rmul x A) B = rmul x (A * B) := by
  funext j
  simp only [rmul, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]
  simp [mul_comm]

/- English proof (translation)
Establish `h1 : ∀ (y : Fin n → E) (b : Fin m), hf L Hm (rmul x A b) y = ∑ l, hf L Hm (x l) y * A l b`. Introduce `y b`. Simplify using `only [hf, rmul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]`. Rewrite using `[Finset.sum_congr rfl fun i _ => Finset.sum_comm, Finset.sum_comm]`. Use `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree. Establish `h2 : ∀ (y : Fin n → E) (a : Fin m), hf L Hm y (rmul x A a) = ∑ k, L.cj (A k a) * hf L Hm y (x k)`. Introduce `y b`. Simplify using `only [hf, rmul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, map_sum, map_mul]`. Rewrite using `[Finset.sum_congr rfl fun i _ => Finset.sum_comm, Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Use extensionality with `a b`. Simplify using `only [gramT, Matrix.mul_apply, Matrix.of_apply, cT, h1, h2]`.
-/
theorem gramT_rmul (L : LocE F E) {n m : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (x : Fin m → Fin n → E)
    (A : Matrix (Fin m) (Fin m) E) : gramT L Hm (rmul x A) = cT L A * gramT L Hm x * A := by
  have h1 : ∀ (y : Fin n → E) (b : Fin m), hf L Hm (rmul x A b) y = ∑ l, hf L Hm (x l) y * A l b := by
    intro y b
    simp only [hf, rmul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    rw [Finset.sum_congr rfl fun i _ => Finset.sum_comm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    ring
  have h2 : ∀ (y : Fin n → E) (a : Fin m), hf L Hm y (rmul x A a) = ∑ k, L.cj (A k a) * hf L Hm y (x k) := by
    intro y b
    simp only [hf, rmul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, map_sum, map_mul]
    rw [Finset.sum_congr rfl fun i _ => Finset.sum_comm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    ring
  ext a b
  simp only [gramT, Matrix.mul_apply, Matrix.of_apply, cT, h1, h2]
end

/- English proof (translation)
Introduce `F _ _ _ _ _ E _ _ _ L ϖ hϖ n Hm hH Λ hΛ m Γ hΓ hΓu Ω hΩ i i' hi hii hst hco`. Take `⟨h1, hK, hO⟩` from `GlobalTheory.T.matrixCongruentOneModUniformizerPow_group_and_orbits L ϖ hϖ m i hi`. Take `⟨h1', hK', hO'⟩` from `GlobalTheory.T.matrixCongruentOneModUniformizerPow_group_and_orbits L ϖ hϖ m i' (hi.trans hii)`. Take `⟨hOco, -⟩` from `hO Γ hΓ hΓu`. Take `⟨hOco', hpos⟩` from `hO' Γ hΓ hΓu`.

Establish `hsub : ∀ B ∈ congK L ϖ m i', B ∈ congK L ϖ m i` using `fun B hB => ((hK 1 h1).2.2.2.2.2 i' hii B hB).2`. Establish `hu : ∀ A ∈ congK L ϖ m i, IsUnit A.det` using `fun A hA => (hK A hA).2.1`. Establish `hmul : ∀ A ∈ congK L ϖ m i, ∀ B ∈ congK L ϖ m i, A * B ∈ congK L ϖ m i` using `fun A hA => (hK A hA).2.2.2.2.1`. Establish `hmul' : ∀ A ∈ congK L ϖ m i', ∀ B ∈ congK L ϖ m i', A * B ∈ congK L ϖ m i'` using `fun A hA => (hK' A hA).2.2.2.2.1`. Establish `hinv : ∀ A ∈ congK L ϖ m i, A⁻¹ ∈ congK L ϖ m i` using `fun A hA => (hK A hA).2.2.2.1`.

Establish `hinv' : ∀ A ∈ congK L ϖ m i', A⁻¹ ∈ congK L ϖ m i'` using `fun A hA => (hK' A hA).2.2.2.1`. Establish `hnorm : ∀ A ∈ congK L ϖ m i, ∀ B ∈ congK L ϖ m i', A⁻¹ * B * A ∈ congK L ϖ m i'` using `fun A hA B hB => ((hK A hA).2.2.2.2.2 i' hii B hB).1`. Set `act : Matrix (Fin m) (Fin m) E → Matrix (Fin m) (Fin m) E → Matrix (Fin m) (Fin m) E` to `fun A X => cT L A * X * A`. Establish `act_mul : ∀ A B X, act B (act A X) = act (A * B) X`. Introduce `A B X`.

Simplify using `only [act, cT_mul, Matrix.mul_assoc]`. Set `P : Matrix (Fin m) (Fin m) E → Set (Matrix (Fin m) (Fin m) E)` to `fun a => act a '' horb L ϖ Γ i'`. Establish `memP : ∀ a X, X ∈ P a ↔ ∃ B ∈ congK L ϖ m i', X = act (B * a) Γ`. Introduce `a X`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨_, ⟨B, hB, rfl⟩, rfl⟩`. Conclude with `⟨B, hB, act_mul B a Γ⟩`. Introduce and unpack `⟨B, hB, rfl⟩`. Conclude with `⟨_, ⟨B, hB, rfl⟩, act_mul B a Γ⟩`. Establish `hPle : ∀ a ∈ congK L ϖ m i, ∀ b ∈ congK L ϖ m i, ∀ X ∈ P a, X ∈ P b → P a ⊆ P b`.

Introduce `a ha b hb X hXa hXb Y hY`. Take `⟨B, hB, hXB⟩` from `(memP _ _).1 hXa`. Take `⟨C, hC, hXC⟩` from `(memP _ _).1 hXb`. Take `⟨D, hD, rfl⟩` from `(memP _ _).1 hY`. Establish `hk : a⁻¹ * (B⁻¹ * D) * a ∈ congK L ϖ m i'` using `hnorm a ha _ (hmul' _ (hinv' B hB) D hD)`.

Use `set k := a⁻¹ * (B⁻¹ * D) * a with hkdef`. Establish `hk2` using `hnorm _ (hinv b hb) k hk`. Rewrite `hk2` using `[Matrix.nonsing_inv_nonsing_inv b (hu b hb)]`. Use `(memP _ _).2 ⟨C * (b * k * b⁻¹), hmul' _ hC _ hk2, ?_⟩` and prove the remaining obligations. Establish `e1 : D * a = B * a * k`.

Rewrite using `[hkdef]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[Matrix.mul_nonsing_inv_cancel_left a _ (hu a ha), Matrix.mul_nonsing_inv_cancel_left B _ (hu B (hsub B hB))]`. Establish `e2 : C * (b * k * b⁻¹) * b = C * b * k`. Simplify using `only [Matrix.mul_assoc]`.

Rewrite using `[Matrix.nonsing_inv_mul b (hu b hb), Matrix.mul_one]`. Rewrite using `[e1, e2, ← act_mul (B * a), ← act_mul (C * b), ← hXB, ← hXC]`. Set `S : Set (Set (Matrix (Fin m) (Fin m) E))` to `P '' congK L ϖ m i`. Establish `hdisj : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Disjoint p q`. Introduce and unpack `_ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hne`.

Rewrite using `[Set.disjoint_left]`. Introduce `X hXa hXb`. Conclude with `hne (Set.Subset.antisymm (hPle a ha b hb X hXa hXb) (hPle b hb a ha X hXb hXa))`. Establish `hS : ∀ p ∈ S, IsCO (hermLat L m) p ∧ cont (hermLat L m) p = cont (hermLat L m) (horb L ϖ Γ i') ∧ p ⊆ horb L ϖ Γ i`. Introduce and unpack `_ ⟨a, ha, rfl⟩`.

Take `⟨j1, j2⟩` from `(GlobalTheory.T.hermitianMatrix_congruence_content_jacobian L ϖ hϖ m a (hu a ha)).2 _ hOco'`. Rewrite `j2` using `[(hK a ha).2.2.1]`. Use `⟨j1, by simpa using j2, fun X hX => ?_⟩` and prove the remaining obligations. Take `⟨B, hB, rfl⟩` from `(memP _ _).1 hX`. Conclude with `⟨B * a, hmul _ (hsub B hB) a ha, rfl⟩`.

Establish `hfin : S.Finite` using `finite_pieces _ hOco S _ hpos hS hdisj`. Establish `hself : ∀ a, act a Γ ∈ P a` using `fun a => (memP _ _).2 ⟨1, h1', by rw [Matrix.one_mul]⟩`. Establish `hU1 : (⋃ p ∈ hfin.toFinset, p) = horb L ϖ Γ i`. Apply `Set.Subset.antisymm` to reduce the goal to its premises. Conclude with `Set.iUnion₂_subset fun p hp => (hS p (hfin.mem_toFinset.1 hp)).2.2`.

Introduce and unpack `_ ⟨A, hA, rfl⟩`. Conclude with `Set.mem_iUnion₂.2 ⟨P A, hfin.mem_toFinset.2 ⟨A, hA, rfl⟩, hself A⟩`. Establish `hc1` using `(GlobalTheory.T.commensurableCosetUnionContent_biUnion (hermLat L m) hfin.toFinset (fun p => p) (fun p hp => (hS p (hfin.mem_toFinset.1 hp)).1)).2 (fun p hp q hq => hdisj p (hfin.mem_toFinset.1 hp) q (hfin.mem_toFinset.1 hq))`. Rewrite `hc1` using `[hU1, Finset.sum_congr rfl (fun p hp => (hS p (hfin.mem_toFinset.1 hp)).2.1), Finset.sum_const, nsmul_eq_mul]`. Establish `hrep : ∀ p : Set (Matrix (Fin m) (Fin m) E), ∃ a, p ∈ S → a ∈ congK L ϖ m i ∧ P a = p`.

Introduce `p`. Distinguish the cases in `hp : p ∈ S`. Take `⟨a, ha, h⟩` from `hp`. Conclude with `⟨a, fun _ => ⟨ha, h⟩⟩`. Conclude with `⟨1, fun h => absurd h hp⟩`.

Use `choose r hr using hrep`. Set `T : Set (Matrix (Fin m) (Fin m) E) → Set (Fin m → Fin n → E)` to `fun p => (fun x => rmul x (r p)) '' thick L ϖ Ω i'`. Establish `hT : ∀ p ∈ S, IsCO (tupLat L Λ m) (T p) ∧ cont (tupLat L Λ m) (T p) = cont (tupLat L Λ m) (thick L ϖ Ω i')`. Introduce `p hp`. Establish `ha` using `(hr p hp).1`.

Apply the tactic sequence `obtain ⟨j1, j2⟩ := (GlobalTheory.T.tuple_jacobian_rightMul_isometry L ϖ hϖ Hm hH Λ hΛ m).1 _ (hu _ ha) _ hco`. Rewrite `j2` using `[(hK _ ha).2.2.1]`. Conclude with `⟨j1, by simpa using j2⟩`. Establish `hgram : ∀ p ∈ S, ∀ x ∈ T p, gramT L Hm x ∈ p`. Introduce and unpack `p hp _ ⟨_, ⟨y, hy, B, hB, rfl⟩, rfl⟩`.

Establish `: act (B * r p) Γ ∈ P (r p)` using `(memP _ _).2 ⟨B, hB, rfl⟩`. Rewrite `this` using `[(hr p hp).2]`. Simplify using `only [rmul_rmul, gramT_rmul, hΩ y hy]`. Conclude with `this`. Establish `hU2 : (⋃ p ∈ hfin.toFinset, T p) = thick L ϖ Ω i`.

Apply `Set.Subset.antisymm` to reduce the goal to its premises. Use `Set.iUnion₂_subset fun p hp => ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨_, ⟨y, hy, B, hB, rfl⟩, rfl⟩`. Conclude with `⟨y, hy, B * r p, hmul _ (hsub B hB) _ (hr p (hfin.mem_toFinset.1 hp)).1, rmul_rmul _ _ _⟩`. Introduce and unpack `_ ⟨y, hy, A, hA, rfl⟩`.

Establish `hp : P A ∈ S` using `⟨A, hA, rfl⟩`. Use `Set.mem_iUnion₂.2 ⟨P A, hfin.mem_toFinset.2 hp, ?_⟩` and prove the remaining obligations. Take `⟨ha, hPa⟩` from `hr _ hp`. Establish `h3` using `hself A`. Rewrite `h3` using `[← hPa]`.

Take `⟨B, hB, h4⟩` from `(memP _ _).1 h3`. Establish `hBa` using `hmul _ (hsub B hB) _ ha`. Establish `h5 : act (A * (B * r (P A))⁻¹) Γ = Γ`. Rewrite using `[← act_mul, h4, act_mul, Matrix.mul_nonsing_inv _ (hu _ hBa)]`. Establish `: cT L (1 : Matrix (Fin m) (Fin m) E) = 1`.

Use extensionality with `a b`. Simplify using `only [cT, Matrix.one_apply, eq_comm]`. Apply the tactic sequence `split_ifs <;> simp`. Simplify using `only [act, this, Matrix.one_mul, Matrix.mul_one]`. Use `⟨_, ⟨_, hst y hy _ (hmul _ hA _ (hinv _ hBa)) h5, B, hB, rfl⟩, ?_⟩` and prove the remaining obligations.

Simplify using `only [rmul_rmul]`. Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hu _ hBa), Matrix.mul_one]`. Establish `hc2` using `(GlobalTheory.T.commensurableCosetUnionContent_biUnion (tupLat L Λ m) hfin.toFinset T (fun p hp => (hT p (hfin.mem_toFinset.1 hp)).1)).2 (fun p hp q hq hne => by`. Establish `hp'` using `hfin.mem_toFinset.1 hp`. Establish `hq'` using `hfin.mem_toFinset.1 hq`.

Rewrite using `[Set.disjoint_left]`. Introduce `x hxp hxq`. Conclude with `Set.disjoint_left.1 (hdisj p hp' q hq' hne) (hgram p hp' x hxp) (hgram q hq' x hxq))`. Rewrite `hc2` using `[hU2, Finset.sum_congr rfl (fun p hp => (hT p (hfin.mem_toFinset.1 hp)).2), Finset.sum_const, nsmul_eq_mul]`. Rewrite using `[hc1, hc2]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ Λs, IsSD L Hm Λs → ∀ (m : ℕ) (Γ : Matrix (Fin m) (Fin m) E), IsHerm L Γ → IsUnit Γ.det → ∀ (Ω : Set (Fin m → Fin n → E)), (∀ y ∈ Ω, gramT L Hm y = Γ) → ∀ i i' : ℕ, 1 ≤ i → i ≤ i' → (∀ y ∈ Ω, ∀ A ∈ congK L ϖ m i, cT L A * Γ * A = Γ → rmul y A ∈ Ω) → IsCO (tupLat L Λs m) (thick L ϖ Ω i') → cont (tupLat L Λs m) (thick L ϖ Ω i) * cont (hermLat L m) (horb L ϖ Γ i') = cont (tupLat L Λs m) (thick L ϖ Ω i') * cont (hermLat L m) (horb L ϖ Γ i) := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ n Hm hH Λ hΛ m Γ hΓ hΓu Ω hΩ i i' hi hii hst hco
  obtain ⟨h1, hK, hO⟩ := GlobalTheory.T.matrixCongruentOneModUniformizerPow_group_and_orbits L ϖ hϖ m i hi
  obtain ⟨h1', hK', hO'⟩ := GlobalTheory.T.matrixCongruentOneModUniformizerPow_group_and_orbits L ϖ hϖ m i' (hi.trans hii)
  obtain ⟨hOco, -⟩ := hO Γ hΓ hΓu
  obtain ⟨hOco', hpos⟩ := hO' Γ hΓ hΓu
  have hsub : ∀ B ∈ congK L ϖ m i', B ∈ congK L ϖ m i := fun B hB =>
    ((hK 1 h1).2.2.2.2.2 i' hii B hB).2
  have hu : ∀ A ∈ congK L ϖ m i, IsUnit A.det := fun A hA => (hK A hA).2.1
  have hmul : ∀ A ∈ congK L ϖ m i, ∀ B ∈ congK L ϖ m i, A * B ∈ congK L ϖ m i :=
    fun A hA => (hK A hA).2.2.2.2.1
  have hmul' : ∀ A ∈ congK L ϖ m i', ∀ B ∈ congK L ϖ m i', A * B ∈ congK L ϖ m i' :=
    fun A hA => (hK' A hA).2.2.2.2.1
  have hinv : ∀ A ∈ congK L ϖ m i, A⁻¹ ∈ congK L ϖ m i := fun A hA => (hK A hA).2.2.2.1
  have hinv' : ∀ A ∈ congK L ϖ m i', A⁻¹ ∈ congK L ϖ m i' := fun A hA => (hK' A hA).2.2.2.1
  have hnorm : ∀ A ∈ congK L ϖ m i, ∀ B ∈ congK L ϖ m i', A⁻¹ * B * A ∈ congK L ϖ m i' :=
    fun A hA B hB => ((hK A hA).2.2.2.2.2 i' hii B hB).1

  let act : Matrix (Fin m) (Fin m) E → Matrix (Fin m) (Fin m) E → Matrix (Fin m) (Fin m) E :=
    fun A X => cT L A * X * A
  have act_mul : ∀ A B X, act B (act A X) = act (A * B) X := by
    intro A B X
    simp only [act, cT_mul, Matrix.mul_assoc]
  let P : Matrix (Fin m) (Fin m) E → Set (Matrix (Fin m) (Fin m) E) :=
    fun a => act a '' horb L ϖ Γ i'
  have memP : ∀ a X, X ∈ P a ↔ ∃ B ∈ congK L ϖ m i', X = act (B * a) Γ := by
    intro a X
    constructor
    · rintro ⟨_, ⟨B, hB, rfl⟩, rfl⟩
      exact ⟨B, hB, act_mul B a Γ⟩
    · rintro ⟨B, hB, rfl⟩
      exact ⟨_, ⟨B, hB, rfl⟩, act_mul B a Γ⟩
  have hPle : ∀ a ∈ congK L ϖ m i, ∀ b ∈ congK L ϖ m i, ∀ X ∈ P a, X ∈ P b → P a ⊆ P b := by
    intro a ha b hb X hXa hXb Y hY
    obtain ⟨B, hB, hXB⟩ := (memP _ _).1 hXa
    obtain ⟨C, hC, hXC⟩ := (memP _ _).1 hXb
    obtain ⟨D, hD, rfl⟩ := (memP _ _).1 hY
    have hk : a⁻¹ * (B⁻¹ * D) * a ∈ congK L ϖ m i' := hnorm a ha _ (hmul' _ (hinv' B hB) D hD)
    set k := a⁻¹ * (B⁻¹ * D) * a with hkdef
    have hk2 := hnorm _ (hinv b hb) k hk
    rw [Matrix.nonsing_inv_nonsing_inv b (hu b hb)] at hk2
    refine (memP _ _).2 ⟨C * (b * k * b⁻¹), hmul' _ hC _ hk2, ?_⟩
    have e1 : D * a = B * a * k := by
      rw [hkdef]
      simp only [Matrix.mul_assoc]
      rw [Matrix.mul_nonsing_inv_cancel_left a _ (hu a ha),
        Matrix.mul_nonsing_inv_cancel_left B _ (hu B (hsub B hB))]
    have e2 : C * (b * k * b⁻¹) * b = C * b * k := by
      simp only [Matrix.mul_assoc]
      rw [Matrix.nonsing_inv_mul b (hu b hb), Matrix.mul_one]
    rw [e1, e2, ← act_mul (B * a), ← act_mul (C * b), ← hXB, ← hXC]
  let S : Set (Set (Matrix (Fin m) (Fin m) E)) := P '' congK L ϖ m i
  have hdisj : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Disjoint p q := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hne
    rw [Set.disjoint_left]
    intro X hXa hXb
    exact hne (Set.Subset.antisymm (hPle a ha b hb X hXa hXb) (hPle b hb a ha X hXb hXa))
  have hS : ∀ p ∈ S, IsCO (hermLat L m) p ∧ cont (hermLat L m) p = cont (hermLat L m) (horb L ϖ Γ i') ∧
      p ⊆ horb L ϖ Γ i := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨j1, j2⟩ := (GlobalTheory.T.hermitianMatrix_congruence_content_jacobian L ϖ hϖ m a (hu a ha)).2 _ hOco'
    rw [(hK a ha).2.2.1] at j2
    refine ⟨j1, by simpa using j2, fun X hX => ?_⟩
    obtain ⟨B, hB, rfl⟩ := (memP _ _).1 hX
    exact ⟨B * a, hmul _ (hsub B hB) a ha, rfl⟩
  have hfin : S.Finite := finite_pieces _ hOco S _ hpos hS hdisj
  have hself : ∀ a, act a Γ ∈ P a := fun a => (memP _ _).2 ⟨1, h1', by rw [Matrix.one_mul]⟩
  have hU1 : (⋃ p ∈ hfin.toFinset, p) = horb L ϖ Γ i := by
    apply Set.Subset.antisymm
    · exact Set.iUnion₂_subset fun p hp => (hS p (hfin.mem_toFinset.1 hp)).2.2
    · rintro _ ⟨A, hA, rfl⟩
      exact Set.mem_iUnion₂.2 ⟨P A, hfin.mem_toFinset.2 ⟨A, hA, rfl⟩, hself A⟩
  have hc1 := (GlobalTheory.T.commensurableCosetUnionContent_biUnion (hermLat L m) hfin.toFinset (fun p => p)
    (fun p hp => (hS p (hfin.mem_toFinset.1 hp)).1)).2
    (fun p hp q hq => hdisj p (hfin.mem_toFinset.1 hp) q (hfin.mem_toFinset.1 hq))
  rw [hU1, Finset.sum_congr rfl (fun p hp => (hS p (hfin.mem_toFinset.1 hp)).2.1), Finset.sum_const,
    nsmul_eq_mul] at hc1

  have hrep : ∀ p : Set (Matrix (Fin m) (Fin m) E), ∃ a, p ∈ S → a ∈ congK L ϖ m i ∧ P a = p := by
    intro p
    by_cases hp : p ∈ S
    · obtain ⟨a, ha, h⟩ := hp
      exact ⟨a, fun _ => ⟨ha, h⟩⟩
    · exact ⟨1, fun h => absurd h hp⟩
  choose r hr using hrep
  let T : Set (Matrix (Fin m) (Fin m) E) → Set (Fin m → Fin n → E) :=
    fun p => (fun x => rmul x (r p)) '' thick L ϖ Ω i'
  have hT : ∀ p ∈ S, IsCO (tupLat L Λ m) (T p) ∧
      cont (tupLat L Λ m) (T p) = cont (tupLat L Λ m) (thick L ϖ Ω i') := by
    intro p hp
    have ha := (hr p hp).1
    obtain ⟨j1, j2⟩ := (GlobalTheory.T.tuple_jacobian_rightMul_isometry L ϖ hϖ Hm hH Λ hΛ m).1 _ (hu _ ha) _ hco
    rw [(hK _ ha).2.2.1] at j2
    exact ⟨j1, by simpa using j2⟩
  have hgram : ∀ p ∈ S, ∀ x ∈ T p, gramT L Hm x ∈ p := by
    rintro p hp _ ⟨_, ⟨y, hy, B, hB, rfl⟩, rfl⟩
    have : act (B * r p) Γ ∈ P (r p) := (memP _ _).2 ⟨B, hB, rfl⟩
    rw [(hr p hp).2] at this
    simp only [rmul_rmul, gramT_rmul, hΩ y hy]
    exact this
  have hU2 : (⋃ p ∈ hfin.toFinset, T p) = thick L ϖ Ω i := by
    apply Set.Subset.antisymm
    · refine Set.iUnion₂_subset fun p hp => ?_
      rintro _ ⟨_, ⟨y, hy, B, hB, rfl⟩, rfl⟩
      exact ⟨y, hy, B * r p, hmul _ (hsub B hB) _ (hr p (hfin.mem_toFinset.1 hp)).1, rmul_rmul _ _ _⟩
    · rintro _ ⟨y, hy, A, hA, rfl⟩
      have hp : P A ∈ S := ⟨A, hA, rfl⟩
      refine Set.mem_iUnion₂.2 ⟨P A, hfin.mem_toFinset.2 hp, ?_⟩
      obtain ⟨ha, hPa⟩ := hr _ hp
      have h3 := hself A
      rw [← hPa] at h3
      obtain ⟨B, hB, h4⟩ := (memP _ _).1 h3
      have hBa := hmul _ (hsub B hB) _ ha
      have h5 : act (A * (B * r (P A))⁻¹) Γ = Γ := by
        rw [← act_mul, h4, act_mul, Matrix.mul_nonsing_inv _ (hu _ hBa)]
        have : cT L (1 : Matrix (Fin m) (Fin m) E) = 1 := by
          ext a b
          simp only [cT, Matrix.one_apply, eq_comm]
          split_ifs <;> simp
        simp only [act, this, Matrix.one_mul, Matrix.mul_one]
      refine ⟨_, ⟨_, hst y hy _ (hmul _ hA _ (hinv _ hBa)) h5, B, hB, rfl⟩, ?_⟩
      simp only [rmul_rmul]
      rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hu _ hBa), Matrix.mul_one]
  have hc2 := (GlobalTheory.T.commensurableCosetUnionContent_biUnion (tupLat L Λ m) hfin.toFinset T
    (fun p hp => (hT p (hfin.mem_toFinset.1 hp)).1)).2
    (fun p hp q hq hne => by
      have hp' := hfin.mem_toFinset.1 hp
      have hq' := hfin.mem_toFinset.1 hq
      rw [Set.disjoint_left]
      intro x hxp hxq
      exact Set.disjoint_left.1 (hdisj p hp' q hq' hne) (hgram p hp' x hxp) (hgram q hq' x hxq))
  rw [hU2, Finset.sum_congr rfl (fun p hp => (hT p (hfin.mem_toFinset.1 hp)).2), Finset.sum_const,
    nsmul_eq_mul] at hc2
  rw [hc1, hc2]
  ring

end GlobalTheory.ThickLevel
