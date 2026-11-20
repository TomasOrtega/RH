import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermLat
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardPrimitiveTuplesHermitianGramModUniformizerStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthonormalBasisAndOneOrbit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommensurableCosetUnionContentIndependentNonnegStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelIndexTupleLatticeHermitianLatticeUniformizerStatement

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.PrimVol

/- English proof (translation)
Use `set Fb : W' ⧸ H → Set (W ⧸ T) := fun c => (QuotientAddGroup.mk : W → W ⧸ T) '' {z | Pr z ∧ (QuotientAddGroup.mk (g z) : W' ⧸ H) = c} with hFb`. Establish `hF : ∀ c ∈ hfin.toFinset, (Fb c).Finite ∧ Q ≤ 2 * ((Fb c).ncard : ℝ) ∧ ((Fb c).ncard : ℝ) ≤ 2 * Q`. Introduce `c hc`. Take `⟨G, hG, rfl⟩` from `(Set.Finite.mem_toFinset _).1 hc`. Use `hfib G hG` as an intermediate fact.

Simplify using `only [hFb, QuotientAddGroup.eq_iff_sub_mem]`. Conclude with `this`. Establish `hU : (QuotientAddGroup.mk : W → W ⧸ T) '' {z | Pr z ∧ g z ∈ B} = ⋃ c ∈ hfin.toFinset, Fb c`. Use extensionality with `q`. Simplify using `only [Set.mem_iUnion, Set.Finite.mem_toFinset, hFb]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, ⟨h1, h2⟩, rfl⟩`. Conclude with `⟨_, ⟨_, h2, rfl⟩, z, ⟨h1, rfl⟩, rfl⟩`. Introduce and unpack `⟨c, ⟨G, hG, rfl⟩, z, ⟨h1, h2⟩, rfl⟩`. Use `⟨z, ⟨h1, ?_⟩, rfl⟩` and prove the remaining obligations.

Use `hB G hG _ (QuotientAddGroup.eq_iff_sub_mem.1 h2)` as an intermediate fact. Simplify using `using this`. Establish `hD : (hfin.toFinset : Set (W' ⧸ H)).PairwiseDisjoint Fb`. Introduce `c _ c' _ hne`. Use `Set.disjoint_left.2 ?_` and prove the remaining obligations.

Introduce and unpack `q ⟨z, ⟨h1, rfl⟩, rfl⟩ ⟨z', ⟨h1', rfl⟩, h3⟩`. Conclude with `hne (QuotientAddGroup.eq_iff_sub_mem.2 (hg z z' h1 h1' (QuotientAddGroup.eq_iff_sub_mem.1 h3.symm)))`. Establish `hC : (⋃ c ∈ hfin.toFinset, Fb c).ncard = ∑ c ∈ hfin.toFinset, (Fb c).ncard`. Use `Set.Finite.ncard_biUnion (hfin.toFinset.finite_toSet) (fun c hc => (hF c hc).1) hD` as an intermediate fact. Rewrite `this` using `[finsum_mem_coe_finset]`.

Conclude with `this`. Rewrite using `[hU, hC, Set.ncard_eq_toFinset_card _ hfin]`. Use `⟨Set.Finite.biUnion hfin.toFinset.finite_toSet (fun c hc => (hF c hc).1), ?_, ?_⟩` and prove the remaining obligations. Use `push_cast`. Rewrite using `[Finset.mul_sum]`.

Use `Finset.card_nsmul_le_sum hfin.toFinset (fun c => 2 * ((Fb c).ncard : ℝ)) Q (fun c hc => (hF c hc).2.1)` as an intermediate fact. Simplify using `using this`. Use `push_cast`. Use `Finset.sum_le_card_nsmul hfin.toFinset (fun c => ((Fb c).ncard : ℝ)) (2 * Q) (fun c hc => (hF c hc).2.2)` as an intermediate fact. Rewrite `this` using `[nsmul_eq_mul]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem count_fibres {W W' : Type} [AddCommGroup W] [AddCommGroup W'] (T : AddSubgroup W)
    (H : AddSubgroup W') (Pr : W → Prop) (g : W → W') (B : Set W') (Q : ℝ)
    (hB : ∀ x ∈ B, ∀ a ∈ H, x + a ∈ B)
    (hfin : ((QuotientAddGroup.mk : W' → W' ⧸ H) '' B).Finite)
    (hg : ∀ z z', Pr z → Pr z' → z - z' ∈ T → g z - g z' ∈ H)
    (hfib : ∀ G ∈ B, ((QuotientAddGroup.mk : W → W ⧸ T) '' {z | Pr z ∧ g z - G ∈ H}).Finite ∧
      Q ≤ 2 * (((QuotientAddGroup.mk : W → W ⧸ T) '' {z | Pr z ∧ g z - G ∈ H}).ncard : ℝ) ∧
      (((QuotientAddGroup.mk : W → W ⧸ T) '' {z | Pr z ∧ g z - G ∈ H}).ncard : ℝ) ≤ 2 * Q) :
    ((QuotientAddGroup.mk : W → W ⧸ T) '' {z | Pr z ∧ g z ∈ B}).Finite ∧
      (((QuotientAddGroup.mk : W' → W' ⧸ H) '' B).ncard : ℝ) * Q ≤
        2 * (((QuotientAddGroup.mk : W → W ⧸ T) '' {z | Pr z ∧ g z ∈ B}).ncard : ℝ) ∧
      (((QuotientAddGroup.mk : W → W ⧸ T) '' {z | Pr z ∧ g z ∈ B}).ncard : ℝ) ≤
        2 * ((((QuotientAddGroup.mk : W' → W' ⧸ H) '' B).ncard : ℝ) * Q) := by
  set Fb : W' ⧸ H → Set (W ⧸ T) := fun c =>
    (QuotientAddGroup.mk : W → W ⧸ T) '' {z | Pr z ∧ (QuotientAddGroup.mk (g z) : W' ⧸ H) = c} with hFb
  have hF : ∀ c ∈ hfin.toFinset, (Fb c).Finite ∧ Q ≤ 2 * ((Fb c).ncard : ℝ) ∧
      ((Fb c).ncard : ℝ) ≤ 2 * Q := by
    intro c hc
    obtain ⟨G, hG, rfl⟩ := (Set.Finite.mem_toFinset _).1 hc
    have := hfib G hG
    simp only [hFb, QuotientAddGroup.eq_iff_sub_mem]
    exact this
  have hU : (QuotientAddGroup.mk : W → W ⧸ T) '' {z | Pr z ∧ g z ∈ B} = ⋃ c ∈ hfin.toFinset, Fb c := by
    ext q
    simp only [Set.mem_iUnion, Set.Finite.mem_toFinset, hFb]
    constructor
    · rintro ⟨z, ⟨h1, h2⟩, rfl⟩
      exact ⟨_, ⟨_, h2, rfl⟩, z, ⟨h1, rfl⟩, rfl⟩
    · rintro ⟨c, ⟨G, hG, rfl⟩, z, ⟨h1, h2⟩, rfl⟩
      refine ⟨z, ⟨h1, ?_⟩, rfl⟩
      have := hB G hG _ (QuotientAddGroup.eq_iff_sub_mem.1 h2)
      simpa using this
  have hD : (hfin.toFinset : Set (W' ⧸ H)).PairwiseDisjoint Fb := by
    intro c _ c' _ hne
    refine Set.disjoint_left.2 ?_
    rintro q ⟨z, ⟨h1, rfl⟩, rfl⟩ ⟨z', ⟨h1', rfl⟩, h3⟩
    exact hne (QuotientAddGroup.eq_iff_sub_mem.2
      (hg z z' h1 h1' (QuotientAddGroup.eq_iff_sub_mem.1 h3.symm)))
  have hC : (⋃ c ∈ hfin.toFinset, Fb c).ncard = ∑ c ∈ hfin.toFinset, (Fb c).ncard := by
    have := Set.Finite.ncard_biUnion (hfin.toFinset.finite_toSet) (fun c hc => (hF c hc).1) hD
    rw [finsum_mem_coe_finset] at this
    exact this
  rw [hU, hC, Set.ncard_eq_toFinset_card _ hfin]
  refine ⟨Set.Finite.biUnion hfin.toFinset.finite_toSet (fun c hc => (hF c hc).1), ?_, ?_⟩
  · push_cast
    rw [Finset.mul_sum]
    have := Finset.card_nsmul_le_sum hfin.toFinset (fun c => 2 * ((Fb c).ncard : ℝ)) Q
      (fun c hc => (hF c hc).2.1)
    simpa using this
  · push_cast
    have := Finset.sum_le_card_nsmul hfin.toFinset (fun c => ((Fb c).ncard : ℝ)) (2 * Q)
      (fun c hc => (hF c hc).2.2)
    rw [nsmul_eq_mul] at this
    linarith

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E)

/- English proof (translation)
Simplify using `[hf, add_mul, Finset.sum_add_distrib]`.
-/
theorem form_add_left {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (x y z : Fin n → E) :
    hf L Hm (x + y) z = hf L Hm x z + hf L Hm y z := by
  simp [hf, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `[hf, mul_add, Finset.sum_add_distrib]`.
-/
theorem form_add_right {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (x y z : Fin n → E) :
    hf L Hm x (y + z) = hf L Hm x y + hf L Hm x z := by
  simp [hf, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `[hf, Finset.mul_sum, mul_assoc]`.
-/
theorem form_smul_left {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (c : E) (x z : Fin n → E) :
    hf L Hm (c • x) z = c * hf L Hm x z := by
  simp [hf, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Simplify using `only [hf, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring` and prove the remaining obligations.
-/
theorem form_smul_right {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (c : E) (x z : Fin n → E) :
    hf L Hm x (c • z) = L.cj c * hf L Hm x z := by
  simp only [hf, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Proceed by induction on `(Finset.univ : Finset (Fin k)) using Finset.induction_on with`. Consider the case `empty => simp [hf]`. Consider the case `insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, form_add_left, ih, form_smul_left]`.
-/
theorem form_sum_left {n k : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (c : Fin k → E)
    (v : Fin k → Fin n → E) (z : Fin n → E) :
    hf L Hm (∑ i, c i • v i) z = ∑ i, c i * hf L Hm (v i) z := by
  induction (Finset.univ : Finset (Fin k)) using Finset.induction_on with
  | empty => simp [hf]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, form_add_left, ih, form_smul_left]

/- English proof (translation)
Proceed by induction on `(Finset.univ : Finset (Fin k)) using Finset.induction_on with`. Consider the case `empty => simp [hf]`. Consider the case `insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, form_add_right, ih, form_smul_right]`.
-/
theorem form_sum_right {n k : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (c : Fin k → E)
    (v : Fin k → Fin n → E) (z : Fin n → E) :
    hf L Hm z (∑ i, c i • v i) = ∑ i, L.cj (c i) * hf L Hm z (v i) := by
  induction (Finset.univ : Finset (Fin k)) using Finset.induction_on with
  | empty => simp [hf]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, form_add_right, ih, form_smul_right]

/- English proof (translation)
Establish `h' : ∀ i j, L.cj (Hm i j) = Hm j i` using `fun i j => congrFun (congrFun h j) i`. Simplify using `only [hf, map_sum, map_mul, L.cj_cj, h']`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring` and prove the remaining obligations.
-/
theorem form_conj {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E} (h : IsHerm L Hm) (x y : Fin n → E) :
    L.cj (hf L Hm x y) = hf L Hm y x := by
  have h' : ∀ i j, L.cj (Hm i j) = Hm j i := fun i j => congrFun (congrFun h j) i
  simp only [hf, map_sum, map_mul, L.cj_cj, h']
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Use `⟨fun h => ?_, fun h => AddSubgroup.subset_closure h⟩` and prove the remaining obligations. Proceed by induction on `h using AddSubgroup.closure_induction with`. Consider the case `mem x hx => exact hx`. Consider the case `zero => exact ⟨by ext i j; simp [cT], fun i j => L.O.zero_mem⟩`. Consider the case `add x y _ _ hx hy`.

Use `⟨?_, fun i j => L.O.add_mem (hx.2 i j) (hy.2 i j)⟩` and prove the remaining obligations. Use extensionality with `i j`. Establish `h1` using `congrFun (congrFun hx.1 i) j`. Establish `h2` using `congrFun (congrFun hy.1 i) j`. Simplify using `only [cT] at h1 h2`.

Simplify using `[cT, h1, h2]`. Consider the case `neg x _ hx`. Use `⟨?_, fun i j => L.O.neg_mem (hx.2 i j)⟩` and prove the remaining obligations. Use extensionality with `i j`. Establish `h1` using `congrFun (congrFun hx.1 i) j`.

Simplify using `only [cT] at h1`. Simplify using `[cT, h1]`.
-/
theorem mem_hermLat {m : ℕ} (X : Matrix (Fin m) (Fin m) E) :
    X ∈ hermLat L m ↔ IsHerm L X ∧ IsIntM L X := by
  refine ⟨fun h => ?_, fun h => AddSubgroup.subset_closure h⟩
  induction h using AddSubgroup.closure_induction with
  | mem x hx => exact hx
  | zero => exact ⟨by ext i j; simp [cT], fun i j => L.O.zero_mem⟩
  | add x y _ _ hx hy =>
    refine ⟨?_, fun i j => L.O.add_mem (hx.2 i j) (hy.2 i j)⟩
    ext i j
    have h1 := congrFun (congrFun hx.1 i) j
    have h2 := congrFun (congrFun hy.1 i) j
    simp only [cT] at h1 h2
    simp [cT, h1, h2]
  | neg x _ hx =>
    refine ⟨?_, fun i j => L.O.neg_mem (hx.2 i j)⟩
    ext i j
    have h1 := congrFun (congrFun hx.1 i) j
    simp only [cT] at h1
    simp [cT, h1]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨Y, hY, rfl⟩`. Take `⟨h1, h2⟩` from `(mem_hermLat L Y).1 hY`. Use `⟨?_, fun a b => ⟨Y a b, h2 a b, by simp⟩⟩` and prove the remaining obligations. Use extensionality with `i j`.

Establish `h1` using `congrFun (congrFun h1 i) j`. Simplify using `only [cT] at h1`. Simplify using `[cT, h1, hc]`. Introduce and unpack `⟨h1, h2⟩ choose c hc1 hc2 using h2`. Use `⟨Matrix.of c, (mem_hermLat L _).2 ⟨?_, hc1⟩, ?_⟩` and prove the remaining obligations.

Use extensionality with `i j`. Establish `h1` using `congrFun (congrFun h1 i) j`. Simplify using `only [cT, hc2, map_mul, hc] at h1`. Conclude with `hp.mul_left_cancel h1`. Use extensionality with `i j`.

Simplify using `[hc2]`.
-/
theorem mem_mul_herm {m : ℕ} {p : E} (hp : IsUnit p) (hc : L.cj p = p) (X : Matrix (Fin m) (Fin m) E) :
    X ∈ (hermLat L m).map (DistribMulAction.toAddMonoidHom _ p) ↔
      IsHerm L X ∧ ∀ a b, ∃ c ∈ L.O, X a b = p * c := by
  constructor
  · rintro ⟨Y, hY, rfl⟩
    obtain ⟨h1, h2⟩ := (mem_hermLat L Y).1 hY
    refine ⟨?_, fun a b => ⟨Y a b, h2 a b, by simp⟩⟩
    ext i j
    have h1 := congrFun (congrFun h1 i) j
    simp only [cT] at h1
    simp [cT, h1, hc]
  · rintro ⟨h1, h2⟩
    choose c hc1 hc2 using h2
    refine ⟨Matrix.of c, (mem_hermLat L _).2 ⟨?_, hc1⟩, ?_⟩
    · ext i j
      have h1 := congrFun (congrFun h1 i) j
      simp only [cT, hc2, map_mul, hc] at h1
      exact hp.mul_left_cancel h1
    · ext i j
      simp [hc2]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, hw, rfl⟩`. Conclude with `⟨w, fun a => hw a trivial, rfl⟩`. Introduce and unpack `⟨w, hw, rfl⟩`. Conclude with `⟨w, fun a _ => hw a, rfl⟩`.
-/
theorem mem_mul_tup {n m : ℕ} (Λ : Submodule L.O (Fin n → E)) (p : E) (t : Fin m → Fin n → E) :
    t ∈ (tupLat L Λ m).map (DistribMulAction.toAddMonoidHom _ p) ↔
      ∃ w : Fin m → Fin n → E, (∀ a, w a ∈ Λ) ∧ t = p • w := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, fun a => hw a trivial, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, fun a _ => hw a, rfl⟩

/- English proof (translation)
The claim follows from `Λ.smul_mem (⟨c, hc⟩ : L.O) hv`.
-/
theorem smul_mem_lat {n : ℕ} {Λ : Submodule L.O (Fin n → E)} {c : E} (hc : c ∈ L.O) {v : Fin n → E}
    (hv : v ∈ Λ) : c • v ∈ Λ := Λ.smul_mem (⟨c, hc⟩ : L.O) hv

/- English proof (translation)
Take `⟨hz, y, hy, hzy⟩` from `hz`. Use `⟨fun a => Λ.add_mem (hz a) (smul_mem_lat L hp (hw a)), ?_⟩` and prove the remaining obligations. Set `C : Matrix (Fin m) (Fin m) L.O` to `Matrix.of fun a b => ⟨hf L Hm (w a) (y b), (hΛ.2 _).2 (hy b) _ (hw a)⟩`. Set `p' : L.O` to `⟨p, hp⟩`. Establish `hdet : IsUnit (1 + p' • C).det`.

Choose the witnesses or unpack the hypotheses as in `⟨c, hc⟩ : ∃ c : L.O, (1 + p' • C).det = 1 + p' * c := by`. Rewrite using `[Matrix.det_one_add_smul, sq, ← mul_assoc, add_assoc, ← add_mul, mul_comm _ p']`. Conclude with `⟨_, rfl⟩`. Take `⟨u, hu1, hu2⟩` from `hu c c.2`. Rewrite using `[hc]`.

Conclude with `IsUnit.of_mul_eq_one (⟨u, hu1⟩ : L.O) (Subtype.ext hu2)`. Use `set M := (1 + p' • C) with hM`. Establish `hMv : ∀ a b, hf L Hm ((z + p • w) a) (y b) = (M a b : E)`. Introduce `a b`. Simplify using `only [Pi.add_apply, Pi.smul_apply, form_add_left, form_smul_left, hzy, hM, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, C, p', Matrix.of_apply]`.

Apply the tactic sequence `split_ifs <;> simp`. Use `⟨fun b => ∑ c, L.cj (M⁻¹ c b : E) • y c, fun b => Λ.sum_mem fun c _ => smul_mem_lat L (hcj _ (M⁻¹ c b).2) (hy c), fun a b => ?_⟩` and prove the remaining obligations. Rewrite using `[form_sum_right]`. Simplify using `only [L.cj_cj, hMv]`. Establish `h1` using `congrArg (fun X : Matrix (Fin m) (Fin m) L.O => (X a b : E)) (Matrix.mul_nonsing_inv M hdet)`.

Simplify using `only [Matrix.mul_apply, Matrix.one_apply] at h1`. Move the coercions through the operations in `at h1`. Simplify using `only [mul_comm ((M⁻¹ _ _ : L.O) : E)]`. Rewrite using `[h1]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem prim_add {n m : ℕ} {Hm : Matrix (Fin n) (Fin n) E} {Λ : Submodule L.O (Fin n → E)}
    (hΛ : IsSD L Hm Λ) (hcj : ∀ x ∈ L.O, L.cj x ∈ L.O) {p : E} (hp : p ∈ L.O)
    (hu : ∀ c ∈ L.O, ∃ u ∈ L.O, (1 + p * c) * u = 1) {z w : Fin m → Fin n → E}
    (hz : IsPrimT L Hm Λ z) (hw : ∀ a, w a ∈ Λ) : IsPrimT L Hm Λ (z + p • w) := by
  obtain ⟨hz, y, hy, hzy⟩ := hz
  refine ⟨fun a => Λ.add_mem (hz a) (smul_mem_lat L hp (hw a)), ?_⟩
  let C : Matrix (Fin m) (Fin m) L.O := Matrix.of fun a b => ⟨hf L Hm (w a) (y b), (hΛ.2 _).2 (hy b) _ (hw a)⟩
  let p' : L.O := ⟨p, hp⟩
  have hdet : IsUnit (1 + p' • C).det := by
    obtain ⟨c, hc⟩ : ∃ c : L.O, (1 + p' • C).det = 1 + p' * c := by
      rw [Matrix.det_one_add_smul, sq, ← mul_assoc, add_assoc, ← add_mul, mul_comm _ p']
      exact ⟨_, rfl⟩
    obtain ⟨u, hu1, hu2⟩ := hu c c.2
    rw [hc]
    exact IsUnit.of_mul_eq_one (⟨u, hu1⟩ : L.O) (Subtype.ext hu2)
  set M := (1 + p' • C) with hM
  have hMv : ∀ a b, hf L Hm ((z + p • w) a) (y b) = (M a b : E) := by
    intro a b
    simp only [Pi.add_apply, Pi.smul_apply, form_add_left, form_smul_left, hzy, hM, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, C, p', Matrix.of_apply]
    split_ifs <;> simp
  refine ⟨fun b => ∑ c, L.cj (M⁻¹ c b : E) • y c, fun b => Λ.sum_mem fun c _ =>
    smul_mem_lat L (hcj _ (M⁻¹ c b).2) (hy c), fun a b => ?_⟩
  rw [form_sum_right]
  simp only [L.cj_cj, hMv]
  have h1 := congrArg (fun X : Matrix (Fin m) (Fin m) L.O => (X a b : E)) (Matrix.mul_nonsing_inv M hdet)
  simp only [Matrix.mul_apply, Matrix.one_apply] at h1
  push_cast at h1
  simp only [mul_comm ((M⁻¹ _ _ : L.O) : E)]
  rw [h1]
  split_ifs <;> simp

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[cT, gramT, form_conj L h]`.
-/
theorem gram_herm {n m : ℕ} {Hm : Matrix (Fin n) (Fin n) E} (h : IsHerm L Hm) (z : Fin m → Fin n → E) :
    IsHerm L (gramT L Hm z) := by
  ext i j
  simp [cT, gramT, form_conj L h]

/- English proof (translation)
Use extensionality with `i j`. Establish `h1` using `congrFun (congrFun hX i) j`. Establish `h2` using `congrFun (congrFun hY i) j`. Simplify using `only [cT] at h1 h2`. Simplify using `[cT, h1, h2]`.
-/
theorem herm_sub {m : ℕ} {X Y : Matrix (Fin m) (Fin m) E} (hX : IsHerm L X) (hY : IsHerm L Y) :
    IsHerm L (X - Y) := by
  ext i j
  have h1 := congrFun (congrFun hX i) j
  have h2 := congrFun (congrFun hY i) j
  simp only [cT] at h1 h2
  simp [cT, h1, h2]

/- English proof (translation)
Establish `hi : ∀ x ∈ Λ, ∀ y ∈ Λ, hf L Hm x y ∈ L.O` using `fun x hx y hy => (hΛ.2 _).2 hy _ hx`. Use `(mem_mul_herm L hp' hc _).2 ⟨herm_sub L (gram_herm L h _) (gram_herm L h _), fun a b => ?_⟩` and prove the remaining obligations. Use `⟨hf L Hm (z b) (w a) + hf L Hm (w b) (z a) + p * hf L Hm (w b) (w a), L.O.add_mem (L.O.add_mem (hi _ (hz b) _ (hw a)) (hi _ (hw b) _ (hz a))) (L.O.mul_mem hp (hi _ (hw b) _ (hw a))), ?_⟩` and prove the remaining obligations. Simplify using `only [gramT, Matrix.sub_apply, Matrix.of_apply, Pi.add_apply, Pi.smul_apply, form_add_left, form_add_right, form_smul_left, form_smul_right, hc]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gram_add {n m : ℕ} {Hm : Matrix (Fin n) (Fin n) E} (h : IsHerm L Hm)
    {Λ : Submodule L.O (Fin n → E)} (hΛ : IsSD L Hm Λ) {p : E} (hp : p ∈ L.O) (hp' : IsUnit p)
    (hc : L.cj p = p) {z w : Fin m → Fin n → E} (hz : ∀ a, z a ∈ Λ) (hw : ∀ a, w a ∈ Λ) :
    gramT L Hm (z + p • w) - gramT L Hm z ∈ (hermLat L m).map (DistribMulAction.toAddMonoidHom _ p) := by
  have hi : ∀ x ∈ Λ, ∀ y ∈ Λ, hf L Hm x y ∈ L.O := fun x hx y hy => (hΛ.2 _).2 hy _ hx
  refine (mem_mul_herm L hp' hc _).2 ⟨herm_sub L (gram_herm L h _) (gram_herm L h _), fun a b => ?_⟩
  refine ⟨hf L Hm (z b) (w a) + hf L Hm (w b) (z a) + p * hf L Hm (w b) (w a),
    L.O.add_mem (L.O.add_mem (hi _ (hz b) _ (hw a)) (hi _ (hw b) _ (hz a)))
      (L.O.mul_mem hp (hi _ (hw b) _ (hw a))), ?_⟩
  simp only [gramT, Matrix.sub_apply, Matrix.of_apply, Pi.add_apply, Pi.smul_apply, form_add_left,
    form_add_right, form_smul_left, form_smul_right, hc]
  ring

/- English proof (translation)
Establish `hi : ∀ x ∈ Λ, ∀ y ∈ Λ, hf L Hm x y ∈ L.O` using `fun x hx y hy => (hΛ.2 _).2 hy _ hx`. Establish `hbm : ∀ i, b i ∈ Λ` using `fun i => hbΛ ▸ Submodule.subset_span ⟨i, rfl⟩`. Set `φ : (Fin n → E) → (Fin n → E)` to `fun x => ∑ i, x i • b i`. Establish `hφb : ∀ x i, hf L Hm (φ x) (b i) = x i`. Introduce `x i`.

Simplify using `[φ, form_sum_left, hb]`. Establish `hφ : ∀ x y, hf L Hm (φ x) (φ y) = hf L 1 x y`. Introduce `x y`. Rewrite using `[show φ y = ∑ i, y i • b i from rfl, form_sum_right]`. Simplify using `only [hφb]`.

Simplify using `[hf, Matrix.one_apply, mul_comm]`. Establish `hφm : ∀ x, (∀ i, x i ∈ L.O) → φ x ∈ Λ` using `fun x hx => Λ.sum_mem fun i _ => smul_mem_lat L (hx i) (hbm i)`. Establish `hφs : ∀ v ∈ Λ, ∃ x, (∀ i, x i ∈ L.O) ∧ φ x = v`. Introduce `v hv`. Rewrite `hv` using `[hbΛ, Submodule.mem_span_range_iff_exists_fun]`.

Take `⟨c, rfl⟩` from `hv`. Conclude with `⟨fun i => c i, fun i => (c i).2, rfl⟩`. Establish `hφa : ∀ x y, φ (x + p • y) = φ x + p • φ y`. Introduce `x y`. Simplify using `[φ, add_smul, Finset.sum_add_distrib, Finset.smul_sum, mul_smul]`.

Establish `hSf : S.Finite`. Use `(Set.Finite.pi' (fun _ : Fin m => Set.Finite.pi' (fun _ : Fin n => R.finite_toSet))).subset ?_` and prove the remaining obligations. Introduce `x hx`. Rewrite `hx` using `[hS]`. Conclude with `hx.1`.

Establish `hUS : U = (fun x => QuotientAddGroup.mk (fun a => φ (x a))) '' S`. Rewrite using `[hU, hS]`. Use extensionality with `q`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, ⟨hz, hzG⟩, rfl⟩ choose x0 hx0 hx0z using fun a => hφs (z a) (hz.1 a) choose x hxR c hcO hxc using fun a i => (hR' (x0 a i) (hx0 a i)).exists`.

Establish `hxz : (fun a => φ (x a)) = z + p • fun a => φ (-c a)`. Use function extensionality and compare the values at `a`. Simplify using `only [Pi.add_apply, Pi.smul_apply]`. Rewrite using `[← hx0z a, ← hφa]`. Use `congr 1`.

Use function extensionality and compare the values at `i`. Simplify using `only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]`. Take the linear combination `-hxc a i`. Establish `hw : ∀ a, φ (-c a) ∈ Λ` using `fun a => hφm _ fun i => L.O.neg_mem (hcO a i)`. Take `⟨-, y, hy, hxy⟩` from `hxz ▸ prim_add L hΛ hcj hp hu hz hw`.

Establish `hg` using `AddSubgroup.add_mem _ (gram_add L h hΛ hp hp' hc hz.1 hw) hzG`. Rewrite `hg` using `[sub_add_sub_cancel, ← hxz]`. Use `choose y0 hy0 hy0y using fun a => hφs (y a) (hy a)`. Use `⟨x, ⟨hxR, ⟨y0, hy0, fun a a' => ?_⟩, fun a a' => ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← hφ, hy0y]`.

Conclude with `hxy a a'`. Rewrite using `[← hφ]`. Conclude with `((mem_mul_herm L hp' hc _).1 hg).2 a a'`. Use `QuotientAddGroup.eq_iff_sub_mem.2 ((mem_mul_tup L Λ p _).2 ⟨_, hw, ?_⟩)` and prove the remaining obligations. Rewrite using `[hxz, add_sub_cancel_left]`.

Introduce and unpack `⟨x, ⟨hxR, ⟨y, hy, hxy⟩, hxG⟩, rfl⟩`. Use `⟨_, ⟨⟨fun a => hφm _ fun i => hR _ (hxR a i), fun a => φ (y a), fun a => hφm _ (hy a), fun a a' => ?_⟩, (mem_mul_herm L hp' hc _).2 ⟨herm_sub L (gram_herm L h _) hG, fun a a' => ?_⟩⟩, rfl⟩` and prove the remaining obligations. Rewrite using `[hφ]`. Conclude with `hxy a a'`. Use `hxG a a'` as an intermediate fact.

Rewrite `this` using `[← hφ]`. Conclude with `this`. Rewrite using `[hUS]`. Use `⟨hSf.image _, Set.InjOn.ncard_image ?_⟩` and prove the remaining obligations. Introduce `x hx x' hx' hxx`.

Rewrite `hx`, `hx'` using `[hS]`. Take `⟨w, hw, hw'⟩` from `(mem_mul_tup L Λ p _).1 (QuotientAddGroup.eq_iff_sub_mem.1 hxx)`. Use function extensionality and compare the values at `a i`. Establish `h1 : φ (x a) = φ (x' a) + p • w a`. Use `congrFun hw' a` as an intermediate fact.

Simplify using `only [Pi.sub_apply, Pi.smul_apply] at this`. Rewrite using `[← this]`. Normalize the expressions using the abelian group laws. Establish `h2 : x a i - x' a i = p * hf L Hm (w a) (b i)`. Rewrite using `[← hφb (x a) i, h1, form_add_left, form_smul_left, hφb]`.

Expand and normalize the polynomial expressions, which then agree. Conclude with `(hR' (x a i) (hR _ (hx.1 a i))).unique ⟨hx.1 a i, 0, L.O.zero_mem, by simp⟩ ⟨hx'.1 a i, _, hi _ (hw a) _ (hbm i), h2⟩`.
-/
theorem fibre_card {n m : ℕ} {Hm : Matrix (Fin n) (Fin n) E} (h : IsHerm L Hm)
    {Λ : Submodule L.O (Fin n → E)} (hΛ : IsSD L Hm Λ) (hcj : ∀ x ∈ L.O, L.cj x ∈ L.O)
    {p : E} (hp : p ∈ L.O) (hp' : IsUnit p) (hc : L.cj p = p)
    (hu : ∀ c ∈ L.O, ∃ u ∈ L.O, (1 + p * c) * u = 1)
    (b : Fin n → Fin n → E) (hb : ∀ i j, hf L Hm (b i) (b j) = if i = j then 1 else 0)
    (hbΛ : Λ = Submodule.span L.O (Set.range b)) (R : Finset E) (hR : ∀ u ∈ R, u ∈ L.O)
    (hR' : ∀ u ∈ L.O, ∃! w, w ∈ R ∧ ∃ c ∈ L.O, u - w = p * c)
    {G : Matrix (Fin m) (Fin m) E} (hG : IsHerm L G) (S : Set (Fin m → Fin n → E))
    (hS : S = {x : Fin m → Fin n → E | (∀ a i, x a i ∈ R) ∧
      (∃ y : Fin m → Fin n → E, (∀ a i, y a i ∈ L.O) ∧
        ∀ a b, hf L 1 (x a) (y b) = if a = b then 1 else 0) ∧
      ∀ a b, ∃ c ∈ L.O, hf L 1 (x b) (x a) - G a b = p * c})
    (U : Set ((Fin m → Fin n → E) ⧸ (tupLat L Λ m).map (DistribMulAction.toAddMonoidHom _ p)))
    (hU : U = QuotientAddGroup.mk '' {z | IsPrimT L Hm Λ z ∧
      gramT L Hm z - G ∈ (hermLat L m).map (DistribMulAction.toAddMonoidHom _ p)}) :
    U.Finite ∧ U.ncard = S.ncard := by
  have hi : ∀ x ∈ Λ, ∀ y ∈ Λ, hf L Hm x y ∈ L.O := fun x hx y hy => (hΛ.2 _).2 hy _ hx
  have hbm : ∀ i, b i ∈ Λ := fun i => hbΛ ▸ Submodule.subset_span ⟨i, rfl⟩
  let φ : (Fin n → E) → (Fin n → E) := fun x => ∑ i, x i • b i
  have hφb : ∀ x i, hf L Hm (φ x) (b i) = x i := by
    intro x i
    simp [φ, form_sum_left, hb]
  have hφ : ∀ x y, hf L Hm (φ x) (φ y) = hf L 1 x y := by
    intro x y
    rw [show φ y = ∑ i, y i • b i from rfl, form_sum_right]
    simp only [hφb]
    simp [hf, Matrix.one_apply, mul_comm]
  have hφm : ∀ x, (∀ i, x i ∈ L.O) → φ x ∈ Λ := fun x hx =>
    Λ.sum_mem fun i _ => smul_mem_lat L (hx i) (hbm i)
  have hφs : ∀ v ∈ Λ, ∃ x, (∀ i, x i ∈ L.O) ∧ φ x = v := by
    intro v hv
    rw [hbΛ, Submodule.mem_span_range_iff_exists_fun] at hv
    obtain ⟨c, rfl⟩ := hv
    exact ⟨fun i => c i, fun i => (c i).2, rfl⟩
  have hφa : ∀ x y, φ (x + p • y) = φ x + p • φ y := by
    intro x y
    simp [φ, add_smul, Finset.sum_add_distrib, Finset.smul_sum, mul_smul]
  have hSf : S.Finite := by
    refine (Set.Finite.pi' (fun _ : Fin m => Set.Finite.pi' (fun _ : Fin n => R.finite_toSet))).subset ?_
    intro x hx
    rw [hS] at hx
    exact hx.1
  have hUS : U = (fun x => QuotientAddGroup.mk (fun a => φ (x a))) '' S := by
    rw [hU, hS]
    ext q
    constructor
    · rintro ⟨z, ⟨hz, hzG⟩, rfl⟩
      choose x0 hx0 hx0z using fun a => hφs (z a) (hz.1 a)
      choose x hxR c hcO hxc using fun a i => (hR' (x0 a i) (hx0 a i)).exists
      have hxz : (fun a => φ (x a)) = z + p • fun a => φ (-c a) := by
        funext a
        simp only [Pi.add_apply, Pi.smul_apply]
        rw [← hx0z a, ← hφa]
        congr 1
        funext i
        simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
        linear_combination -hxc a i
      have hw : ∀ a, φ (-c a) ∈ Λ := fun a => hφm _ fun i => L.O.neg_mem (hcO a i)
      obtain ⟨-, y, hy, hxy⟩ := hxz ▸ prim_add L hΛ hcj hp hu hz hw
      have hg := AddSubgroup.add_mem _ (gram_add L h hΛ hp hp' hc hz.1 hw) hzG
      rw [sub_add_sub_cancel, ← hxz] at hg
      choose y0 hy0 hy0y using fun a => hφs (y a) (hy a)
      refine ⟨x, ⟨hxR, ⟨y0, hy0, fun a a' => ?_⟩, fun a a' => ?_⟩, ?_⟩
      · rw [← hφ, hy0y]; exact hxy a a'
      · rw [← hφ]; exact ((mem_mul_herm L hp' hc _).1 hg).2 a a'
      · refine QuotientAddGroup.eq_iff_sub_mem.2 ((mem_mul_tup L Λ p _).2 ⟨_, hw, ?_⟩)
        rw [hxz, add_sub_cancel_left]
    · rintro ⟨x, ⟨hxR, ⟨y, hy, hxy⟩, hxG⟩, rfl⟩
      refine ⟨_, ⟨⟨fun a => hφm _ fun i => hR _ (hxR a i), fun a => φ (y a), fun a => hφm _ (hy a),
        fun a a' => ?_⟩, (mem_mul_herm L hp' hc _).2 ⟨herm_sub L (gram_herm L h _) hG,
        fun a a' => ?_⟩⟩, rfl⟩
      · rw [hφ]; exact hxy a a'
      · have := hxG a a'
        rw [← hφ] at this
        exact this
  rw [hUS]
  refine ⟨hSf.image _, Set.InjOn.ncard_image ?_⟩
  intro x hx x' hx' hxx
  rw [hS] at hx hx'
  obtain ⟨w, hw, hw'⟩ := (mem_mul_tup L Λ p _).1 (QuotientAddGroup.eq_iff_sub_mem.1 hxx)
  funext a i
  have h1 : φ (x a) = φ (x' a) + p • w a := by
    have := congrFun hw' a
    simp only [Pi.sub_apply, Pi.smul_apply] at this
    rw [← this]; abel
  have h2 : x a i - x' a i = p * hf L Hm (w a) (b i) := by
    rw [← hφb (x a) i, h1, form_add_left, form_smul_left, hφb]; ring
  exact (hR' (x a i) (hR _ (hx.1 a i))).unique ⟨hx.1 a i, 0, L.O.zero_mem, by simp⟩
    ⟨hx'.1 a i, _, hi _ (hw a) _ (hbm i), h2⟩

/- English proof (translation)
Establish `hs : {y : L.O | (y : E) = p} = {(⟨p, hp⟩ : L.O)}`. Use extensionality with `y`. Simplify using `[Subtype.ext_iff]`. Rewrite `hfin` using `[hs]`. Use `set I : Ideal L.O := Ideal.span {(⟨p, hp⟩ : L.O)} with hI`.

Use `haveI : Finite (L.O ⧸ I) := Nat.finite_of_card_ne_zero hfin`. Use `haveI := Fintype.ofFinite (L.O ⧸ I)`. Use `choose s hs using Ideal.Quotient.mk_surjective (I := I)`. Establish `key : ∀ (u : L.O) (q : L.O ⧸ I), (∃ c ∈ L.O, (u : E) - s q = p * c) ↔ q = Ideal.Quotient.mk I u`. Introduce `u q`.

Use `conv_rhs => rw [← hs q, eq_comm, Ideal.Quotient.eq, hI, Ideal.mem_span_singleton]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, hc, h⟩`. Conclude with `⟨⟨c, hc⟩, Subtype.ext h⟩`. Introduce and unpack `⟨c, h⟩`.

Conclude with `⟨c, c.2, congrArg Subtype.val h⟩`. Use `⟨Finset.univ.image fun q => (s q : E), ?_, fun u hu => ?_⟩` and prove the remaining obligations. Introduce `u hu`. Take `⟨q, -, rfl⟩` from `Finset.mem_image.1 hu`. Conclude with `(s q).2`.

Use `⟨s (Ideal.Quotient.mk I ⟨u, hu⟩), ⟨Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, (key ⟨u, hu⟩ _).2 rfl⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `w ⟨hw, hc⟩`. Take `⟨q, -, rfl⟩` from `Finset.mem_image.1 hw`. Rewrite using `[(key ⟨u, hu⟩ q).1 hc]`.
-/
theorem exists_residues {p : E} (hp : p ∈ L.O)
    (hfin : Nat.card (L.O ⧸ (Ideal.span {y : L.O | (y : E) = p})) ≠ 0) :
    ∃ R : Finset E, (∀ u ∈ R, u ∈ L.O) ∧ ∀ u ∈ L.O, ∃! w, w ∈ R ∧ ∃ c ∈ L.O, u - w = p * c := by
  have hs : {y : L.O | (y : E) = p} = {(⟨p, hp⟩ : L.O)} := by
    ext y; simp [Subtype.ext_iff]
  rw [hs] at hfin
  set I : Ideal L.O := Ideal.span {(⟨p, hp⟩ : L.O)} with hI
  haveI : Finite (L.O ⧸ I) := Nat.finite_of_card_ne_zero hfin
  haveI := Fintype.ofFinite (L.O ⧸ I)
  choose s hs using Ideal.Quotient.mk_surjective (I := I)
  have key : ∀ (u : L.O) (q : L.O ⧸ I), (∃ c ∈ L.O, (u : E) - s q = p * c) ↔ q = Ideal.Quotient.mk I u := by
    intro u q
    conv_rhs => rw [← hs q, eq_comm, Ideal.Quotient.eq, hI, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨c, hc, h⟩
      exact ⟨⟨c, hc⟩, Subtype.ext h⟩
    · rintro ⟨c, h⟩
      exact ⟨c, c.2, congrArg Subtype.val h⟩
  refine ⟨Finset.univ.image fun q => (s q : E), ?_, fun u hu => ?_⟩
  · intro u hu
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hu
    exact (s q).2
  · refine ⟨s (Ideal.Quotient.mk I ⟨u, hu⟩), ⟨Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩,
      (key ⟨u, hu⟩ _).2 rfl⟩, ?_⟩
    rintro w ⟨hw, hc⟩
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hw
    rw [(key ⟨u, hu⟩ q).1 hc]

/- English proof (translation)
Take `⟨-, h2, -, -, h5, -⟩` from `GlobalTheory.UnramOrder.order_facts L ϖ hϖ`. Introduce `c hc`. Take `⟨hcc, ⟨t, ht⟩, s, hs⟩` from `h2 c hc`. Establish `hnu : ¬ IsUnit (ϖ ^ j * (t + ϖ ^ j * s))` using `fun h => hϖ.not_isUnit ((isUnit_pow_iff (by omega)).1 (isUnit_of_mul_isUnit_left h))`. Establish `hun : IsUnit (1 + ϖ ^ j * (t + ϖ ^ j * s))`.

Use `IsLocalRing.isUnit_or_isUnit_one_sub_self (-(ϖ ^ j * (t + ϖ ^ j * s)))` as an intermediate fact. Rewrite `this` using `[sub_neg_eq_add, IsUnit.neg_iff]`. Conclude with `this.resolve_left hnu`. Take `⟨v, hv⟩` from `hun.exists_right_inv`. Establish `hv'` using `congrArg (fun x : 𝒪[F] => algebraMap F E (x : F)) hv`.

Simplify using `only [Subring.coe_mul, Subring.coe_add, Subring.coe_one, map_mul, map_add, map_one, SubmonoidClass.coe_pow] at hv'`. Establish `hp : algebraMap F E ((ϖ : F) ^ j) ∈ L.O` using `(h5 _).2 (ϖ ^ j).2`. Use `⟨(1 + algebraMap F E ((ϖ : F) ^ j) * L.cj c) * algebraMap F E v, L.O.mul_mem (L.O.add_mem L.O.one_mem (L.O.mul_mem hp hcc)) ((h5 _).2 v.2), ?_⟩` and prove the remaining obligations. Rewrite `hv'` using `[← ht, ← hs]`. Take the linear combination `hv'`.
-/
theorem one_add_unit [IsNonarchimedeanLocalField F] [CharZero F] (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ)
    {j : ℕ} (hj : 1 ≤ j) :
    ∀ c ∈ L.O, ∃ u ∈ L.O, (1 + algebraMap F E ((ϖ : F) ^ j) * c) * u = 1 := by
  obtain ⟨-, h2, -, -, h5, -⟩ := GlobalTheory.UnramOrder.order_facts L ϖ hϖ
  intro c hc
  obtain ⟨hcc, ⟨t, ht⟩, s, hs⟩ := h2 c hc
  have hnu : ¬ IsUnit (ϖ ^ j * (t + ϖ ^ j * s)) := fun h =>
    hϖ.not_isUnit ((isUnit_pow_iff (by omega)).1 (isUnit_of_mul_isUnit_left h))
  have hun : IsUnit (1 + ϖ ^ j * (t + ϖ ^ j * s)) := by
    have := IsLocalRing.isUnit_or_isUnit_one_sub_self (-(ϖ ^ j * (t + ϖ ^ j * s)))
    rw [sub_neg_eq_add, IsUnit.neg_iff] at this
    exact this.resolve_left hnu
  obtain ⟨v, hv⟩ := hun.exists_right_inv
  have hv' := congrArg (fun x : 𝒪[F] => algebraMap F E (x : F)) hv
  simp only [Subring.coe_mul, Subring.coe_add, Subring.coe_one, map_mul, map_add, map_one,
    SubmonoidClass.coe_pow] at hv'
  have hp : algebraMap F E ((ϖ : F) ^ j) ∈ L.O := (h5 _).2 (ϖ ^ j).2
  refine ⟨(1 + algebraMap F E ((ϖ : F) ^ j) * L.cj c) * algebraMap F E v,
    L.O.mul_mem (L.O.add_mem L.O.one_mem (L.O.mul_mem hp hcc)) ((h5 _).2 v.2), ?_⟩
  rw [← ht, ← hs] at hv'
  linear_combination hv'

/- English proof (translation)
Take `⟨-, -, -, -, h5, -⟩` from `GlobalTheory.UnramOrder.order_facts L ϖ hϖ`. Use `set d := A.relIndex (hermLat L m) with hd`. Establish `hd0 : (d : 𝒪[F]) ≠ 0` using `Nat.cast_ne_zero.2 hA`. Take `⟨k, u, hk⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd0 hϖ`. Use `⟨k + 1, by omega, ?_⟩` and prove the remaining obligations.

Introduce and unpack `_ ⟨X, hX, rfl⟩`. Take `⟨h1, h2⟩` from `(mem_hermLat L X).1 hX`. Set `r : 𝒪[F]` to `ϖ * (u⁻¹ : (𝒪[F])ˣ)`. Establish `hr : ϖ ^ (k + 1) = d * r`. Rewrite using `[hk]`.

Simplify using `only [r]`. Take the linear combination `(-(ϖ ^ (k + 1))) * u.mul_inv`. Establish `hr'` using `congrArg (fun x : 𝒪[F] => algebraMap F E (x : F)) hr`. Simplify using `only [Subring.coe_mul, map_mul, SubmonoidClass.coe_pow, Subring.coe_natCast, map_natCast] at hr'`. Establish `hY : algebraMap F E (r : F) • X ∈ hermLat L m`.

Use `(mem_hermLat L _).2 ⟨?_, fun a b => L.O.mul_mem ((h5 _).2 r.2) (h2 a b)⟩` and prove the remaining obligations. Use extensionality with `i j`. Establish `h1` using `congrFun (congrFun h1 i) j`. Simplify using `only [cT] at h1`. Simplify using `[cT, h1]`.

Use `AddSubgroup.nsmul_relIndex_mem A hY` as an intermediate fact. Rewrite `this` using `[← hd, ← Nat.cast_smul_eq_nsmul E, smul_smul, ← hr']`. Conclude with `this`.
-/
theorem exists_level [IsNonarchimedeanLocalField F] [CharZero F] (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ)
    {m : ℕ} (A : AddSubgroup (Matrix (Fin m) (Fin m) E)) (hA : A.relIndex (hermLat L m) ≠ 0) :
    ∃ j, 1 ≤ j ∧ (hermLat L m).map
      (DistribMulAction.toAddMonoidHom _ (algebraMap F E ((ϖ : F) ^ j))) ≤ A := by
  obtain ⟨-, -, -, -, h5, -⟩ := GlobalTheory.UnramOrder.order_facts L ϖ hϖ
  set d := A.relIndex (hermLat L m) with hd
  have hd0 : (d : 𝒪[F]) ≠ 0 := Nat.cast_ne_zero.2 hA
  obtain ⟨k, u, hk⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd0 hϖ
  refine ⟨k + 1, by omega, ?_⟩
  rintro _ ⟨X, hX, rfl⟩
  obtain ⟨h1, h2⟩ := (mem_hermLat L X).1 hX
  let r : 𝒪[F] := ϖ * (u⁻¹ : (𝒪[F])ˣ)
  have hr : ϖ ^ (k + 1) = d * r := by
    rw [hk]
    simp only [r]
    linear_combination (-(ϖ ^ (k + 1))) * u.mul_inv
  have hr' := congrArg (fun x : 𝒪[F] => algebraMap F E (x : F)) hr
  simp only [Subring.coe_mul, map_mul, SubmonoidClass.coe_pow, Subring.coe_natCast, map_natCast] at hr'
  have hY : algebraMap F E (r : F) • X ∈ hermLat L m := by
    refine (mem_hermLat L _).2 ⟨?_, fun a b => L.O.mul_mem ((h5 _).2 r.2) (h2 a b)⟩
    ext i j
    have h1 := congrFun (congrFun h1 i) j
    simp only [cT] at h1
    simp [cT, h1]
  have := AddSubgroup.nsmul_relIndex_mem A hY
  rw [← hd, ← Nat.cast_smul_eq_nsmul E, smul_smul, ← hr'] at this
  exact this

/- English proof (translation)
Introduce `F _ _ _ _ _ E _ _ _ L ϖ hϖ n Hm hHm Λ hΛ m hmn B hB ⟨A, hA⟩`. Take `⟨-, h2, -, -, h5, h6, h7, -⟩` from `GlobalTheory.UnramOrder.order_facts L ϖ hϖ`. Establish `hcj : ∀ x ∈ L.O, L.cj x ∈ L.O` using `fun x hx => (h2 x hx).1`. Take `⟨j, hj, hjA⟩` from `exists_level L ϖ hϖ A hA.1`. Take `⟨hT, hH⟩` from `GlobalTheory.T.relIndex_tupleLattice_hermitianLattice_uniformizer L ϖ hϖ Hm hHm Λ hΛ m j`.

Take `⟨b, hb, hbΛ⟩` from `(GlobalTheory.HL.SelfDual.orthonormal_basis_and_one_orbit L Hm hHm).1 Λ hΛ`. Establish `hu` using `one_add_unit L ϖ hϖ hj`. Establish `hq : resQ ϖ ≠ 0` using `by omega`. Establish `hp : algebraMap F E ((ϖ : F) ^ j) ∈ L.O` using `(h5 _).2 (ϖ ^ j).2`. Establish `hp' : IsUnit (algebraMap F E ((ϖ : F) ^ j))` using `(IsUnit.mk0 _ (pow_ne_zero _ (fun h => hϖ.ne_zero (Subtype.ext h)))).map _`.

Establish `hc : L.cj (algebraMap F E ((ϖ : F) ^ j)) = algebraMap F E ((ϖ : F) ^ j)` using `L.cj.commutes _`. Take `⟨R, hR, hR'⟩` from `exists_residues L hp (by rw [h6]; exact pow_ne_zero _ hq)`. Establish `hD` using `fun G hG hG' => GlobalTheory.T.card_primitive_tuples_hermitian_gram_mod_uniformizer L ϖ hϖ n m j hmn hj G hG hG' R hR hR' _ rfl`. Generalize the expression as in `algebraMap F E ((ϖ : F) ^ j) = p at *`. Establish `hHle : (hermLat L m).map (DistribMulAction.toAddMonoidHom _ p) ≤ hermLat L m`.

Introduce `X hX`. Take `⟨h1, h3⟩` from `(mem_mul_herm L hp' hc _).1 hX`. Use `(mem_hermLat L _).2 ⟨h1, fun a a' => ?_⟩` and prove the remaining obligations. Take `⟨c, hc, hc'⟩` from `h3 a a'`. Conclude with `hc' ▸ L.O.mul_mem hp hc`.

Establish `hTle : (tupLat L Λ m).map (DistribMulAction.toAddMonoidHom _ p) ≤ tupLat L Λ m`. Introduce `t ht`. Take `⟨w, hw, rfl⟩` from `(mem_mul_tup L Λ p _).1 ht`. Conclude with `fun a _ => smul_mem_lat L hp (hw a)`. Establish `hH0 : ((hermLat L m).map (DistribMulAction.toAddMonoidHom _ p)).relIndex (hermLat L m) ≠ 0`.

Rewrite using `[hH]`. Conclude with `pow_ne_zero _ hq`. Establish `hGH : GoodSub (hermLat L m) ((hermLat L m).map (DistribMulAction.toAddMonoidHom _ p)) B`. Use `(GlobalTheory.T.commensurableCosetUnionContent_independent_nonneg _ B).2.1 A _ hA hjA ?_` and prove the remaining obligations. Conclude with `AddSubgroup.relIndex_ne_zero_trans hH0 hA.2.1`.

Establish `hg : ∀ z z', IsPrimT L Hm Λ z → IsPrimT L Hm Λ z' → z - z' ∈ (tupLat L Λ m).map (DistribMulAction.toAddMonoidHom _ p) → gramT L Hm z - gramT L Hm z' ∈ (hermLat L m).map (DistribMulAction.toAddMonoidHom _ p)`. Introduce `z z' _ hz' hzz`. Take `⟨w, hw, hw'⟩` from `(mem_mul_tup L Λ p _).1 hzz`. Rewrite `hw'` using `[sub_eq_iff_eq_add']`. Rewrite using `[hw']`.

Conclude with `gram_add L hHm.1 hΛ hp hp' hc hz'.1 hw`. Take `⟨c1, c2, c3⟩` from `count_fibres ((tupLat L Λ m).map (DistribMulAction.toAddMonoidHom _ p)) ((hermLat L m).map (DistribMulAction.toAddMonoidHom _ p)) (IsPrimT L Hm Λ) (gramT L Hm) B ((resQ ϖ : ℝ) ^ (j * (2 * n * m - m ^ 2))) hGH.2.2.1 hGH.2.2.2 hg (by`. Introduce `G hG`. Take `⟨g1, g2⟩` from `(mem_hermLat L G).1 (hB G hG)`. Take `⟨f1, f2⟩` from `fibre_card L hHm.1 hΛ hcj hp hp' hc hu b hb hbΛ R hR hR' g1 _ rfl _ rfl`.

Rewrite using `[f2]`. Conclude with `⟨f1, hD G g1 g2⟩)`. Establish `hGT : GoodSub (tupLat L Λ m) ((tupLat L Λ m).map (DistribMulAction.toAddMonoidHom _ p)) {z : Fin m → Fin n → E | IsPrimT L Hm Λ z ∧ gramT L Hm z ∈ B}`. Use `⟨by rw [hT]; exact pow_ne_zero _ hq, by rw [AddSubgroup.relIndex_eq_one.2 hTle]; exact one_ne_zero, ?_, c1⟩` and prove the remaining obligations. Introduce and unpack `z ⟨hz, hzB⟩ t ht`.

Take `⟨w, hw, rfl⟩` from `(mem_mul_tup L Λ p _).1 ht`. Use `⟨prim_add L hΛ hcj hp hu hz hw, ?_⟩` and prove the remaining obligations. Simplify using `using hGH.2.2.1 _ hzB _ (gram_add L hHm.1 hΛ hp hp' hc hz.1 hw)`. Use `⟨⟨_, hGT⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[(GlobalTheory.T.commensurableCosetUnionContent_independent_nonneg _ _).1 _ hGT, (GlobalTheory.T.commensurableCosetUnionContent_independent_nonneg _ _).1 _ hGH, relVol, relVol, hT, hH, AddSubgroup.relIndex_eq_one.2 hTle, AddSubgroup.relIndex_eq_one.2 hHle]`.

Establish `he : 2 * n * m * j = j * (2 * n * m - m ^ 2) + m ^ 2 * j`. Establish `: m ^ 2 ≤ 2 * n * m` using `by nlinarith`. Rewrite using `[mul_comm (m ^ 2) j, ← mul_add, Nat.sub_add_cancel this, mul_comm]`. Rewrite using `[he]`. Use `push_cast`.

Rewrite using `[pow_add]`. Establish `hq' : (0 : ℝ) < resQ ϖ` using `by exact_mod_cast Nat.pos_of_ne_zero hq`. Establish `q1` using `pow_pos hq' (j * (2 * n * m - m ^ 2))`. Establish `q2` using `pow_pos hq' (m ^ 2 * j)`. Generalize the expression as in `(resQ ϖ : ℝ) ^ (j * (2 * n * m - m ^ 2)) = Q at *`.

Generalize the expression as in `(resQ ϖ : ℝ) ^ (m ^ 2 * j) = Q' at *`. Prove the components needed by the constructor for the conclusion. Clear the denominators using the available nonvanishing facts. Combine the linear equalities and inequalities to obtain the conclusion. Clear the denominators using the available nonvanishing facts.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem cont_primitive_tuples : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ Λs, IsSD L Hm Λs → ∀ m : ℕ, 2 * m + 3 ≤ n → ∀ B : Set (Matrix (Fin m) (Fin m) E), (∀ X ∈ B, X ∈ hermLat L m) → IsCO (hermLat L m) B → IsCO (tupLat L Λs m) {z : Fin m → Fin n → E | IsPrimT L Hm Λs z ∧ gramT L Hm z ∈ B} ∧ cont (hermLat L m) B ≤ 2 * cont (tupLat L Λs m) {z : Fin m → Fin n → E | IsPrimT L Hm Λs z ∧ gramT L Hm z ∈ B} ∧ cont (tupLat L Λs m) {z : Fin m → Fin n → E | IsPrimT L Hm Λs z ∧ gramT L Hm z ∈ B} ≤ 2 * cont (hermLat L m) B := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ n Hm hHm Λ hΛ m hmn B hB ⟨A, hA⟩
  obtain ⟨-, h2, -, -, h5, h6, h7, -⟩ := GlobalTheory.UnramOrder.order_facts L ϖ hϖ
  have hcj : ∀ x ∈ L.O, L.cj x ∈ L.O := fun x hx => (h2 x hx).1
  obtain ⟨j, hj, hjA⟩ := exists_level L ϖ hϖ A hA.1
  obtain ⟨hT, hH⟩ := GlobalTheory.T.relIndex_tupleLattice_hermitianLattice_uniformizer L ϖ hϖ Hm hHm Λ hΛ m j
  obtain ⟨b, hb, hbΛ⟩ := (GlobalTheory.HL.SelfDual.orthonormal_basis_and_one_orbit L Hm hHm).1 Λ hΛ
  have hu := one_add_unit L ϖ hϖ hj
  have hq : resQ ϖ ≠ 0 := by omega
  have hp : algebraMap F E ((ϖ : F) ^ j) ∈ L.O := (h5 _).2 (ϖ ^ j).2
  have hp' : IsUnit (algebraMap F E ((ϖ : F) ^ j)) :=
    (IsUnit.mk0 _ (pow_ne_zero _ (fun h => hϖ.ne_zero (Subtype.ext h)))).map _
  have hc : L.cj (algebraMap F E ((ϖ : F) ^ j)) = algebraMap F E ((ϖ : F) ^ j) := L.cj.commutes _
  obtain ⟨R, hR, hR'⟩ := exists_residues L hp (by rw [h6]; exact pow_ne_zero _ hq)
  have hD := fun G hG hG' => GlobalTheory.T.card_primitive_tuples_hermitian_gram_mod_uniformizer L ϖ hϖ n m j hmn hj G hG hG' R hR hR' _ rfl
  generalize algebraMap F E ((ϖ : F) ^ j) = p at *
  have hHle : (hermLat L m).map (DistribMulAction.toAddMonoidHom _ p) ≤ hermLat L m := by
    intro X hX
    obtain ⟨h1, h3⟩ := (mem_mul_herm L hp' hc _).1 hX
    refine (mem_hermLat L _).2 ⟨h1, fun a a' => ?_⟩
    obtain ⟨c, hc, hc'⟩ := h3 a a'
    exact hc' ▸ L.O.mul_mem hp hc
  have hTle : (tupLat L Λ m).map (DistribMulAction.toAddMonoidHom _ p) ≤ tupLat L Λ m := by
    intro t ht
    obtain ⟨w, hw, rfl⟩ := (mem_mul_tup L Λ p _).1 ht
    exact fun a _ => smul_mem_lat L hp (hw a)
  have hH0 : ((hermLat L m).map (DistribMulAction.toAddMonoidHom _ p)).relIndex (hermLat L m) ≠ 0 := by
    rw [hH]; exact pow_ne_zero _ hq
  have hGH : GoodSub (hermLat L m) ((hermLat L m).map (DistribMulAction.toAddMonoidHom _ p)) B := by
    refine (GlobalTheory.T.commensurableCosetUnionContent_independent_nonneg _ B).2.1 A _ hA hjA ?_
    exact AddSubgroup.relIndex_ne_zero_trans hH0 hA.2.1
  have hg : ∀ z z', IsPrimT L Hm Λ z → IsPrimT L Hm Λ z' →
      z - z' ∈ (tupLat L Λ m).map (DistribMulAction.toAddMonoidHom _ p) →
      gramT L Hm z - gramT L Hm z' ∈ (hermLat L m).map (DistribMulAction.toAddMonoidHom _ p) := by
    intro z z' _ hz' hzz
    obtain ⟨w, hw, hw'⟩ := (mem_mul_tup L Λ p _).1 hzz
    rw [sub_eq_iff_eq_add'] at hw'
    rw [hw']
    exact gram_add L hHm.1 hΛ hp hp' hc hz'.1 hw
  obtain ⟨c1, c2, c3⟩ := count_fibres ((tupLat L Λ m).map (DistribMulAction.toAddMonoidHom _ p))
    ((hermLat L m).map (DistribMulAction.toAddMonoidHom _ p)) (IsPrimT L Hm Λ) (gramT L Hm) B
    ((resQ ϖ : ℝ) ^ (j * (2 * n * m - m ^ 2))) hGH.2.2.1 hGH.2.2.2 hg (by
      intro G hG
      obtain ⟨g1, g2⟩ := (mem_hermLat L G).1 (hB G hG)
      obtain ⟨f1, f2⟩ := fibre_card L hHm.1 hΛ hcj hp hp' hc hu b hb hbΛ R hR hR' g1 _ rfl _ rfl
      rw [f2]
      exact ⟨f1, hD G g1 g2⟩)
  have hGT : GoodSub (tupLat L Λ m) ((tupLat L Λ m).map (DistribMulAction.toAddMonoidHom _ p))
      {z : Fin m → Fin n → E | IsPrimT L Hm Λ z ∧ gramT L Hm z ∈ B} := by
    refine ⟨by rw [hT]; exact pow_ne_zero _ hq,
      by rw [AddSubgroup.relIndex_eq_one.2 hTle]; exact one_ne_zero, ?_, c1⟩
    rintro z ⟨hz, hzB⟩ t ht
    obtain ⟨w, hw, rfl⟩ := (mem_mul_tup L Λ p _).1 ht
    refine ⟨prim_add L hΛ hcj hp hu hz hw, ?_⟩
    simpa using hGH.2.2.1 _ hzB _ (gram_add L hHm.1 hΛ hp hp' hc hz.1 hw)
  refine ⟨⟨_, hGT⟩, ?_⟩
  rw [(GlobalTheory.T.commensurableCosetUnionContent_independent_nonneg _ _).1 _ hGT, (GlobalTheory.T.commensurableCosetUnionContent_independent_nonneg _ _).1 _ hGH, relVol, relVol, hT, hH,
    AddSubgroup.relIndex_eq_one.2 hTle, AddSubgroup.relIndex_eq_one.2 hHle]
  have he : 2 * n * m * j = j * (2 * n * m - m ^ 2) + m ^ 2 * j := by
    have : m ^ 2 ≤ 2 * n * m := by nlinarith
    rw [mul_comm (m ^ 2) j, ← mul_add, Nat.sub_add_cancel this, mul_comm]
  rw [he]
  push_cast
  rw [pow_add]
  have hq' : (0 : ℝ) < resQ ϖ := by exact_mod_cast Nat.pos_of_ne_zero hq
  have q1 := pow_pos hq' (j * (2 * n * m - m ^ 2))
  have q2 := pow_pos hq' (m ^ 2 * j)
  generalize (resQ ϖ : ℝ) ^ (j * (2 * n * m - m ^ 2)) = Q at *
  generalize (resQ ϖ : ℝ) ^ (m ^ 2 * j) = Q' at *
  constructor
  · field_simp
    linarith
  · field_simp
    linarith

end GlobalTheory.HL.PrimVol
