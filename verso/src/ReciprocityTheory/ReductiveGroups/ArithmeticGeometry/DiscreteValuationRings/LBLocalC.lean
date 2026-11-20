import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.WchartLePreimage
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

/- English proof (translation)
Rewrite using `[res_res']`. Use `ext`. Simplify using `[res]`.
-/
lemma res_of_le_of_le {X : Scheme.{0}} {U Z : X.Opens} (h : Z ≤ U) (h' : U ≤ Z) (x : Γ(X, U)ˣ) :
    res h' (res h x) = x := by
  rw [res_res']
  ext
  simp [res]

def gw {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (ψ : K → (Y ⟶ X)) (ε : K → ℤ) (j j' : K → L.ι) :
    Γ(Y, LB.wchart L ψ j ⊓ LB.wchart L ψ j')ˣ :=
  ∏ k, (res (le_inf (inf_le_left.trans (LB.wchart_le L ψ j k)) (inf_le_right.trans (LB.wchart_le L ψ j' k)) :
      LB.wchart L ψ j ⊓ LB.wchart L ψ j' ≤ ψ k ⁻¹ᵁ (L.U (j k) ⊓ L.U (j' k)))
    (pullU (ψ k) _ (L.g (j k) (j' k)))) ^ (ε k)

def IsGenW {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (ψ : K → (Y ⟶ X)) (ε : K → ℤ)
    (s : ∀ j : K → L.ι, Γ(Y, LB.wchart L ψ j)ˣ) : Prop :=
  ∀ j j' : K → L.ι, res (inf_le_left : LB.wchart L ψ j ⊓ LB.wchart L ψ j' ≤ LB.wchart L ψ j) (s j) =
    gw L ψ ε j j' * res (inf_le_right : LB.wchart L ψ j ⊓ LB.wchart L ψ j' ≤ LB.wchart L ψ j') (s j')

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
lemma isGen_iff_isGenW {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (ψ : K → (Y ⟶ X)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L ψ ε)) : t.IsGen ↔ IsGenW L ψ ε t.s := Iff.rfl

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Rewrite using `[pullU_res, res_res', pullU_comp]`. Both sides reduce to the same expression.
-/
private lemma res_pullU_comp_factor_through_open {X Y Z : Scheme.{0}} (h : Z ⟶ Y) (φ : Y ⟶ X) {U : X.Opens} {W : Y.Opens}
    {T : Z.Opens} (hb : W ≤ φ ⁻¹ᵁ U) (ha : T ≤ (h ≫ φ) ⁻¹ᵁ U) (hW : T ≤ h ⁻¹ᵁ W) (g : Γ(X, U)ˣ) :
    res ha (pullU (h ≫ φ) U g) = res hW (pullU h W (res hb (pullU φ U g))) := by
  rw [pullU_res, res_res', pullU_comp]
  rfl

/- English proof (translation)
Simplify using `only [gw, map_prod, map_zpow]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Use `congr 1`. Use `beta_reduce`. Conclude with `res_pullU_comp_factor_through_open (U := L.U (j k) ⊓ L.U (j' k)) (W := LB.wchart L φ j ⊓ LB.wchart L φ j') h (φ k) _ _ hW (L.g (j k) (j' k))`.
-/
lemma gw_pull {X Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X))
    (ε : K → ℤ) (h : Z ⟶ Y) (j j' : K → L.ι)
    (hW : LB.wchart L (fun k => h ≫ φ k) j ⊓ LB.wchart L (fun k => h ≫ φ k) j' ≤
      h ⁻¹ᵁ (LB.wchart L φ j ⊓ LB.wchart L φ j')) :
    gw L (fun k => h ≫ φ k) ε j j' = res hW (pullU h _ (gw L φ ε j j')) := by
  simp only [gw, map_prod, map_zpow]
  refine Finset.prod_congr rfl fun k _ => ?_
  congr 1
  beta_reduce
  exact res_pullU_comp_factor_through_open (U := L.U (j k) ⊓ L.U (j' k)) (W := LB.wchart L φ j ⊓ LB.wchart L φ j') h (φ k) _ _ hW
    (L.g (j k) (j' k))

/- English proof (translation)
Use `eq_top_iff.2 fun x _ => ?_` and prove the remaining obligations. Conclude with `(IsLocalRing.specializes_closedPoint (R := V) x).mem_open U.isOpen hU`.
-/
lemma eq_top_of_closedPoint_mem {V : Type} [CommRing V] [IsLocalRing V] (U : (Spec (CommRingCat.of V)).Opens)
    (hU : (IsLocalRing.closedPoint V : Spec (CommRingCat.of V)) ∈ U) : U = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  exact (IsLocalRing.specializes_closedPoint (R := V) x).mem_open U.isOpen hU

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨i₀, hi₀⟩ : ∃ i, (IsLocalRing.closedPoint V : Spec (CommRingCat.of V)) ∈ M.U i := by`. Establish `: (IsLocalRing.closedPoint V : Spec (CommRingCat.of V)) ∈ (⊤ : (Spec (CommRingCat.of V)).Opens)` using `trivial`. Rewrite `this` using `[← hM.cover]`. Conclude with `TopologicalSpace.Opens.mem_iSup.1 this`. Establish `htop` using `eq_top_of_closedPoint_mem _ hi₀`.

Establish `hto : ∀ W : (Spec (CommRingCat.of V)).Opens, W ≤ M.U i₀` using `fun W => by`. Rewrite using `[htop]`. Conclude with `le_top`. Use `⟨⟨fun i => res (le_inf le_rfl (hto _) : M.U i ≤ M.U i ⊓ M.U i₀) (M.g i i₀)⟩, fun i j => ?_⟩` and prove the remaining obligations. Establish `hc` using `congrArg (res (le_inf le_rfl (hto _) : M.U i ⊓ M.U j ≤ M.U i ⊓ M.U j ⊓ M.U i₀)) (hM.cocycle i j i₀)`.

Simplify using `only [map_mul, res_res'] at hc`. Simplify using `only [res_res']`. Rewrite using `[← hc]`. Use `congr 1`.
-/
theorem exists_gen_of_isLB_local {V : Type} [CommRing V] [IsLocalRing V]
    (M : LB (Spec (CommRingCat.of V))) (hM : M.IsLB) : ∃ e : M.Gen, e.IsGen := by
  obtain ⟨i₀, hi₀⟩ : ∃ i, (IsLocalRing.closedPoint V : Spec (CommRingCat.of V)) ∈ M.U i := by
    have : (IsLocalRing.closedPoint V : Spec (CommRingCat.of V)) ∈
        (⊤ : (Spec (CommRingCat.of V)).Opens) := trivial
    rw [← hM.cover] at this
    exact TopologicalSpace.Opens.mem_iSup.1 this
  have htop := eq_top_of_closedPoint_mem _ hi₀
  have hto : ∀ W : (Spec (CommRingCat.of V)).Opens, W ≤ M.U i₀ := fun W => by
    rw [htop]
    exact le_top
  refine ⟨⟨fun i => res (le_inf le_rfl (hto _) : M.U i ≤ M.U i ⊓ M.U i₀) (M.g i i₀)⟩, fun i j => ?_⟩
  have hc := congrArg (res (le_inf le_rfl (hto _) : M.U i ⊓ M.U j ≤ M.U i ⊓ M.U j ⊓ M.U i₀))
    (hM.cocycle i j i₀)
  simp only [map_mul, res_res'] at hc
  simp only [res_res']
  rw [← hc]
  congr 1

/- English proof (translation)
Use `ext`. Simplify using `[res]`.
-/
private lemma res_self_discrete_valuation_rings {Y : Scheme.{0}} {U : Y.Opens} (h : U ≤ U) (x : Γ(Y, U)ˣ) :
    res h x = x := by
  ext
  simp [res]

/- English proof (translation)
Establish `hfw : LB.wchart L ψ j ≤ LB.wchart L ψ j ⊓ LB.wchart L ψ j₀` using `le_inf le_rfl (by rw [htop]; exact le_top)`. Establish `e1` using `congrArg (res hfw) (hs j j₀)`. Establish `e2` using `congrArg (res hfw) (hs' j j₀)`. Simplify using `only [map_mul, res_res', res_self_discrete_valuation_rings] at e1 e2`. Rewrite using `[map_div, e1, e2, mul_comm (res _ _) (res _ (s' j₀)), ← mul_assoc, div_mul_cancel, mul_comm]`.
-/
lemma gen_div_const {Y : Scheme.{0}} {X : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (ψ : K → (Y ⟶ X))
    (ε : K → ℤ) (s s' : ∀ j : K → L.ι, Γ(Y, LB.wchart L ψ j)ˣ) (hs : IsGenW L ψ ε s) (hs' : IsGenW L ψ ε s')
    (j₀ : K → L.ι) (htop : LB.wchart L ψ j₀ = ⊤) (j : K → L.ι) :
    s j = res (by rw [htop]; exact le_top : LB.wchart L ψ j ≤ LB.wchart L ψ j₀) (s j₀ / s' j₀) * s' j := by
  have hfw : LB.wchart L ψ j ≤ LB.wchart L ψ j ⊓ LB.wchart L ψ j₀ :=
    le_inf le_rfl (by rw [htop]; exact le_top)
  have e1 := congrArg (res hfw) (hs j j₀)
  have e2 := congrArg (res hfw) (hs' j j₀)
  simp only [map_mul, res_res', res_self_discrete_valuation_rings] at e1 e2
  rw [map_div, e1, e2, mul_comm (res _ _) (res _ (s' j₀)), ← mul_assoc, div_mul_cancel, mul_comm]

/- English proof (translation)
The claim follows from `exists_gen_of_isLB_local _ (linComb_isLB (L := L) (φ := φ) (ε := ε) hL)`.
-/
theorem exists_gen_of_local {V : Type} [CommRing V] [IsLocalRing V] {X : Scheme.{0}} (L : LB X) (hL : L.IsLB)
    {K : Type} [Fintype K] (φ : K → (Spec (CommRingCat.of V) ⟶ X)) (ε : K → ℤ) :
    ∃ e : LB.Gen (LB.LinComb L φ ε), e.IsGen := exists_gen_of_isLB_local _ (linComb_isLB (L := L) (φ := φ) (ε := ε) hL)

/- English proof (translation)
Establish `hc : ∀ k, ∃ i, (φ k).base (IsLocalRing.closedPoint V) ∈ L.U i`. Introduce `k`. Establish `: (φ k).base (IsLocalRing.closedPoint V) ∈ (⊤ : X.Opens)` using `trivial`. Rewrite `this` using `[← hL.cover]`. Conclude with `TopologicalSpace.Opens.mem_iSup.1 this`.

Use `choose j₀ hj₀ using hc`. Conclude with `⟨j₀, eq_top_of_closedPoint_mem _ (Set.mem_iInter.2 fun k => hj₀ k)⟩`.
-/
lemma exists_chart_top {V : Type} [CommRing V] [IsLocalRing V] {X : Scheme.{0}} (L : LB X) (hL : L.IsLB)
    {K : Type} [Fintype K] (φ : K → (Spec (CommRingCat.of V) ⟶ X)) (ε : K → ℤ) :
    ∃ j₀ : K → L.ι, LB.wchart L φ j₀ = ⊤ := by
  have hc : ∀ k, ∃ i, (φ k).base (IsLocalRing.closedPoint V) ∈ L.U i := by
    intro k
    have : (φ k).base (IsLocalRing.closedPoint V) ∈ (⊤ : X.Opens) := trivial
    rw [← hL.cover] at this
    exact TopologicalSpace.Opens.mem_iSup.1 this
  choose j₀ hj₀ using hc
  exact ⟨j₀, eq_top_of_closedPoint_mem _ (Set.mem_iInter.2 fun k => hj₀ k)⟩

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}

/- English proof (translation)
Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := V) c`. Establish `hb0 : b ≠ 0` using `nonZeroDivisors.ne_zero hb`. Establish `ha0 : a ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hc`.

Take `⟨k, u, hu⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ`. Take `⟨l, u', hu'⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ`. Establish `hϖ0 : algebraMap V (FractionRing V) ϖ ≠ 0`. Rewrite using `[Ne, IsFractionRing.to_map_eq_zero_iff]`. Conclude with `hϖ.ne_zero`.

Establish `hu'0 : algebraMap V (FractionRing V) (u' : V) ≠ 0`. Rewrite using `[Ne, IsFractionRing.to_map_eq_zero_iff]`. Conclude with `u'.ne_zero`. Use `⟨(k : ℤ) - l, u * u'⁻¹, ?_⟩` and prove the remaining obligations. Rewrite using `[hu, hu', zpow_sub₀ hϖ0]`.

Simplify using `only [Units.val_mul, map_mul, map_pow, map_units_inv, zpow_natCast]`. Clear the denominators using the available nonvanishing facts.
-/
lemma hasVal_of_ne_zero (hϖ : Irreducible ϖ) {c : FractionRing V} (hc : c ≠ 0) : ∃ n, HasVal ϖ c n := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := V) c
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at hc
  obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
  obtain ⟨l, u', hu'⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
  have hϖ0 : algebraMap V (FractionRing V) ϖ ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]
    exact hϖ.ne_zero
  have hu'0 : algebraMap V (FractionRing V) (u' : V) ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]
    exact u'.ne_zero
  refine ⟨(k : ℤ) - l, u * u'⁻¹, ?_⟩
  rw [hu, hu', zpow_sub₀ hϖ0]
  simp only [Units.val_mul, map_mul, map_pow, map_units_inv, zpow_natCast]
  field_simp

/- English proof (translation)
Take `⟨u, hu⟩` from `hn`. Take `⟨u', hu'⟩` from `hm`. Establish `hA0 : algebraMap V (FractionRing V) ϖ ≠ 0`. Rewrite using `[Ne, IsFractionRing.to_map_eq_zero_iff]`. Conclude with `hϖ.ne_zero`.

Establish `hU0 : algebraMap V (FractionRing V) (u : V) ≠ 0`. Rewrite using `[Ne, IsFractionRing.to_map_eq_zero_iff]`. Conclude with `u.ne_zero`. Establish `e : algebraMap V (FractionRing V) ϖ ^ n * algebraMap V (FractionRing V) (u : V) = algebraMap V (FractionRing V) ϖ ^ m * algebraMap V (FractionRing V) (u' : V)` using `hu.symm.trans hu'`. Take `⟨d, hd⟩` from `Int.eq_ofNat_of_zero_le (sub_nonneg.2 h)`.

Establish `h1 : algebraMap V (FractionRing V) ϖ ^ d = algebraMap V (FractionRing V) ((u' * u⁻¹ : Vˣ) : V)`. Rewrite using `[← zpow_natCast, ← hd, zpow_sub₀ hA0, Units.val_mul, map_mul, map_units_inv, div_eq_iff (zpow_ne_zero _ hA0)]`. Clear the denominators using the available nonvanishing facts. Take the linear combination `e`. Rewrite `h1` using `[← map_pow]`.

Establish `h2` using `IsFractionRing.injective V (FractionRing V) h1`. Establish `hunit : IsUnit (ϖ ^ d)`. Rewrite using `[h2]`. Conclude with `Units.isUnit _`. Establish `hd0 : d = 0`.

Assume the negation of the conclusion as `hd0`. Conclude with `hϖ.not_isUnit ((isUnit_pow_iff hd0).1 hunit)`. Use linear arithmetic over natural numbers and integers.
-/
private lemma hasVal_eq_of_hasVal_of_le (hϖ : Irreducible ϖ) {c : FractionRing V} {n m : ℤ}
    (hn : HasVal ϖ c n) (hm : HasVal ϖ c m) (h : m ≤ n) : n = m := by
  obtain ⟨u, hu⟩ := hn
  obtain ⟨u', hu'⟩ := hm
  have hA0 : algebraMap V (FractionRing V) ϖ ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]
    exact hϖ.ne_zero
  have hU0 : algebraMap V (FractionRing V) (u : V) ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]
    exact u.ne_zero
  have e : algebraMap V (FractionRing V) ϖ ^ n * algebraMap V (FractionRing V) (u : V) =
      algebraMap V (FractionRing V) ϖ ^ m * algebraMap V (FractionRing V) (u' : V) :=
    hu.symm.trans hu'
  obtain ⟨d, hd⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.2 h)
  have h1 : algebraMap V (FractionRing V) ϖ ^ d =
      algebraMap V (FractionRing V) ((u' * u⁻¹ : Vˣ) : V) := by
    rw [← zpow_natCast, ← hd, zpow_sub₀ hA0, Units.val_mul, map_mul, map_units_inv,
      div_eq_iff (zpow_ne_zero _ hA0)]
    field_simp
    linear_combination e
  rw [← map_pow] at h1
  have h2 := IsFractionRing.injective V (FractionRing V) h1
  have hunit : IsUnit (ϖ ^ d) := by
    rw [h2]
    exact Units.isUnit _
  have hd0 : d = 0 := by
    by_contra hd0
    exact hϖ.not_isUnit ((isUnit_pow_iff hd0).1 hunit)
  omega

/- English proof (translation)
Break down `le_total m n with h | h` into its components or cases. Conclude with `hasVal_eq_of_hasVal_of_le hϖ hn hm h`. Conclude with `(hasVal_eq_of_hasVal_of_le hϖ hm hn h).symm`.
-/
lemma hasVal_unique (hϖ : Irreducible ϖ) {c : FractionRing V} {n m : ℤ} (hn : HasVal ϖ c n)
    (hm : HasVal ϖ c m) : n = m := by
  rcases le_total m n with h | h
  · exact hasVal_eq_of_hasVal_of_le hϖ hn hm h
  · exact (hasVal_eq_of_hasVal_of_le hϖ hm hn h).symm

/- English proof (translation)
Take `⟨u, hu⟩` from `hn`. Use `⟨u * v, ?_⟩` and prove the remaining obligations. Rewrite using `[hu, Units.val_mul, map_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma hasVal_mul_unit {c : FractionRing V} {n : ℤ} (hn : HasVal ϖ c n) (v : Vˣ) :
    HasVal ϖ (c * algebraMap V (FractionRing V) (v : V)) n := by
  obtain ⟨u, hu⟩ := hn
  refine ⟨u * v, ?_⟩
  rw [hu, Units.val_mul, map_mul]
  ring

/- English proof (translation)
Take `⟨e, he, c, hc, h⟩` from `hn`. Use `⟨e, he, c, hc, fun j => ?_⟩` and prove the remaining obligations. Take `⟨y, hy⟩ : ∃ y : Γ(Spec (CommRingCat.of (FractionRing V)), LB.wchart L φ' j)ˣ, y = t.s j` from `⟨_, rfl⟩`. Establish `hj` using `h j`. Rewrite `hj`, the goal using `[← hy]`.

Use `⟨y * (res (wchart_le_preimage L (jK V) φ φ' hφ j) (pullU (jK V) _ (e.s j)))⁻¹, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_mul, hj] first`. Consider the case `exact Units.mul_inv_cancel_right _ _`. Consider the case `simp`. Conclude with `(inv_mul_cancel_right _ _).symm`.
-/
lemma genHasVal_units {X : Scheme.{0}} (L : LB X) {Ix : Type} [Fintype Ix]
    (φ : Ix → (Spec (CommRingCat.of V) ⟶ X)) (φ' : Ix → (Spec (CommRingCat.of (FractionRing V)) ⟶ X))
    (hφ : ∀ k, φ' k = jK V ≫ φ k) (ε : Ix → ℤ) (t : LB.Gen (LB.LinComb L φ' ε)) {n : ℤ}
    (hn : GenHasVal ϖ L φ φ' hφ ε t n) :
    ∃ e : LB.Gen (LB.LinComb L φ ε), e.IsGen ∧ ∃ c : FractionRing V, HasVal ϖ c n ∧
      ∀ j : Ix → L.ι, ∃ C : Γ(Spec (CommRingCat.of (FractionRing V)), LB.wchart L φ' j)ˣ,
        C.val = resTop _ (scal (𝟙 (Spec (CommRingCat.of (FractionRing V)))) c) ∧
        (t.s j : Γ(Spec (CommRingCat.of (FractionRing V)), LB.wchart L φ' j)ˣ) =
          C * res (wchart_le_preimage L (jK V) φ φ' hφ j) (pullU (jK V) _ (e.s j)) := by
  obtain ⟨e, he, c, hc, h⟩ := hn
  refine ⟨e, he, c, hc, fun j => ?_⟩
  obtain ⟨y, hy⟩ : ∃ y : Γ(Spec (CommRingCat.of (FractionRing V)), LB.wchart L φ' j)ˣ, y = t.s j :=
    ⟨_, rfl⟩
  have hj := h j
  rw [← hy] at hj ⊢
  refine ⟨y * (res (wchart_le_preimage L (jK V) φ φ' hφ j) (pullU (jK V) _ (e.s j)))⁻¹, ?_, ?_⟩
  · rw [Units.val_mul, hj]
    first
      | exact Units.mul_inv_cancel_right _ _
      | simp
  · exact (inv_mul_cancel_right _ _).symm

/- English proof (translation)
Establish `h1 : (0 : R) = 1`. Use `C.isUnit` as an intermediate fact. Rewrite `this` using `[h]`. Conclude with `isUnit_zero_iff.1 this`. Use `haveI := subsingleton_of_zero_eq_one h1`.

Conclude with `Subsingleton.elim a b`.
-/
lemma eq_of_unit_zero {R : Type*} [CommRing R] (C : Rˣ) (h : C.val = 0) (a b : R) : a = b := by
  have h1 : (0 : R) = 1 := by
    have := C.isUnit
    rw [h] at this
    exact isUnit_zero_iff.1 this
  haveI := subsingleton_of_zero_eq_one h1
  exact Subsingleton.elim a b

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Take `⟨e, he, c, hc, hte⟩` from `hn`. Establish `hV : (⊤ : (Spec (CommRingCat.of V)).Opens) ≤ LB.wchart L φ j₀` using `htop ▸ le_rfl`. Use `set E : Γ(Spec (CommRingCat.of V), ⊤)ˣ := res hV (e.s j₀) with hE`. Use `set eV : Vˣ := Units.map (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom.toMonoidHom E with heV`. Use `⟨c, hc, eV, ?_⟩` and prove the remaining obligations.

Establish `h1` using `congrArg ((Spec (CommRingCat.of (FractionRing V))).presheaf.map (homOfLE hK).op).hom (hte j₀)`. Use `erw [map_mul] at h1`. Establish `hA : ((Spec (CommRingCat.of (FractionRing V))).presheaf.map (homOfLE hK).op).hom (t.s j₀).val = (res hK (t.s j₀)).val` using `rfl`. Rewrite `h1` using `[hA]`. Rewrite using `[h1]`.

Use `erw [map_mul]`. Use `congr 1`. Simplify using `only [resTop, scal, Scheme.Hom.id_appTop, ← CommRingCat.comp_apply, ← Functor.map_comp]`. Establish `: (homOfLE (le_top : LB.wchart L (fun k => jK V ≫ φ k) j₀ ≤ ⊤)).op ≫ (homOfLE hK).op = 𝟙 (Opposite.op (⊤ : (Spec (CommRingCat.of (FractionRing V))).Opens))` using `Subsingleton.elim _ _`. Rewrite using `[Category.id_comp, ← Functor.map_comp]`.

Use `erw [this, CategoryTheory.Functor.map_id]`. Simplify using the standard rewrite rules. Simplify using `only [res, pullU, Units.coe_map, MonoidHom.coe_coe, heV, hE, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]`. Establish `hnat` using `congrArg (fun f => (CommRingCat.Hom.hom f) (((Spec (CommRingCat.of V)).presheaf.map (homOfLE hV).op).hom (e.s j₀).val)) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap V (FractionRing V))))`. Simplify using `only [CommRingCat.comp_apply, CommRingCat.hom_ofHom] at hnat`.

Use `erw [← hnat]`. Rewrite using `[CommRingCat.comp_apply]`. Use `congr 1`.
-/
lemma genHasVal_top {X : Scheme.{0}} (L : LB X) {Ix : Type} [Fintype Ix]
    (φ : Ix → (Spec (CommRingCat.of V) ⟶ X)) (ε : Ix → ℤ) (t : LB.Gen (LB.LinComb L (fun k => jK V ≫ φ k) ε)) {n : ℤ}
    (hn : GenHasVal ϖ L φ (fun k => jK V ≫ φ k) (fun _ => rfl) ε t n) (j₀ : Ix → L.ι)
    (htop : LB.wchart L φ j₀ = ⊤) (hK : (⊤ : (Spec (CommRingCat.of (FractionRing V))).Opens) ≤
      LB.wchart L (fun k => jK V ≫ φ k) j₀) :
    ∃ c : FractionRing V, HasVal ϖ c n ∧ ∃ eV : Vˣ,
      (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).hom.hom (res hK (t.s j₀)).val =
        c * algebraMap V (FractionRing V) (eV : V) := by
  obtain ⟨e, he, c, hc, hte⟩ := hn
  have hV : (⊤ : (Spec (CommRingCat.of V)).Opens) ≤ LB.wchart L φ j₀ := htop ▸ le_rfl
  set E : Γ(Spec (CommRingCat.of V), ⊤)ˣ := res hV (e.s j₀) with hE
  set eV : Vˣ := Units.map (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom.toMonoidHom E with heV
  refine ⟨c, hc, eV, ?_⟩
  have h1 := congrArg ((Spec (CommRingCat.of (FractionRing V))).presheaf.map (homOfLE hK).op).hom (hte j₀)
  erw [map_mul] at h1
  have hA : ((Spec (CommRingCat.of (FractionRing V))).presheaf.map (homOfLE hK).op).hom (t.s j₀).val =
      (res hK (t.s j₀)).val := rfl
  rw [hA] at h1
  rw [h1]
  erw [map_mul]
  congr 1
  · simp only [resTop, scal, Scheme.Hom.id_appTop, ← CommRingCat.comp_apply, ← Functor.map_comp]
    have : (homOfLE (le_top : LB.wchart L (fun k => jK V ≫ φ k) j₀ ≤ ⊤)).op ≫ (homOfLE hK).op =
        𝟙 (Opposite.op (⊤ : (Spec (CommRingCat.of (FractionRing V))).Opens)) := Subsingleton.elim _ _
    rw [Category.id_comp, ← Functor.map_comp]
    erw [this, CategoryTheory.Functor.map_id]
    simp
  · simp only [res, pullU, Units.coe_map, MonoidHom.coe_coe, heV, hE, RingHom.toMonoidHom_eq_coe,
      MonoidHom.coe_coe]
    have hnat := congrArg (fun f => (CommRingCat.Hom.hom f)
        (((Spec (CommRingCat.of V)).presheaf.map (homOfLE hV).op).hom (e.s j₀).val))
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap V (FractionRing V))))
    simp only [CommRingCat.comp_apply, CommRingCat.hom_ofHom] at hnat
    erw [← hnat]
    rw [CommRingCat.comp_apply]
    congr 1

omit [IsDiscreteValuationRing V] in

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Establish `hinj : Function.Injective (algebraMap V (FractionRing V))` using `IsFractionRing.injective V _`. Establish `: DenseRange (PrimeSpectrum.comap (algebraMap V (FractionRing V)))` using `(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by`. Rewrite using `[(RingHom.injective_iff_ker_eq_bot _).1 hinj]`. Conclude with `bot_le)`.

Conclude with `this`.
-/
theorem isDominant_jK : IsDominant (jK V) := by
  constructor
  have hinj : Function.Injective (algebraMap V (FractionRing V)) := IsFractionRing.injective V _
  have : DenseRange (PrimeSpectrum.comap (algebraMap V (FractionRing V))) :=
    (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 hinj]
      exact bot_le)
  exact this

end ReciprocityTheory.ChartRestriction.G.DVR
