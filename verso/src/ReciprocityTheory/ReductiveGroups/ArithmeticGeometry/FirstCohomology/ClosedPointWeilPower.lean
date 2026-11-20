import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.OneCHyp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.H1.ClosedPointWeilPower

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi

section Grp

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {T : Over S}

/- English proof (translation)
Use `haveI := hf`. Conclude with `MonObj.one_comp f`.
-/
lemma one_comp_hom (f : A ⟶ A) (hf : IsMonHom f) : (1 : T ⟶ A) ≫ f = 1 := by
  haveI := hf
  exact MonObj.one_comp f

/- English proof (translation)
Introduce `n hn`. Proceed by induction on `n with`. Consider the case `zero => omega`. Consider the case `succ n ih`. Break down `Nat.eq_zero_or_pos n with rfl | hpos` into its components or cases.

Simplify using `[ρ.map_one]`. Rewrite using `[Nat.cast_succ, ρ.map_add, ρ.map_one, padd, ← Category.assoc, CartesianMonoidalCategory.comp_lift, Category.comp_id, ih hpos, pow_succ, Hom.mul_def]`.
-/
lemma comp_act_nat {O : Type} [Ring O] (ρ : RingAct A O) (x : T ⟶ A) :
    ∀ n : ℕ, 1 ≤ n → x ≫ ρ.act (n : O) = x ^ n := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp [ρ.map_one]
    · rw [Nat.cast_succ, ρ.map_add, ρ.map_one, padd, ← Category.assoc,
        CartesianMonoidalCategory.comp_lift, Category.comp_id, ih hpos, pow_succ, Hom.mul_def]

end Grp

section Weil

/- English proof (translation)
Take `⟨H1, H2, -, -⟩` from `hW S P k T`. Take `⟨c, hc, -⟩` from `H1 1 y (one_pow k) hy`. Establish `hcc : WeilIs P.A P.L k 1 y (c * c)` using `by simpa using H2 1 1 y c c hc hc`. Establish `huniq` using `(H1 1 y (one_pow k) hy).unique hc hcc`. Establish `hc1 : c = 1` using `mul_left_cancel (huniq.symm.trans (mul_one c).symm)`.

Rewrite using `[← hc1]`. Conclude with `hc`.
-/
lemma weil_one_left (hW : WeilSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) (k : ℕ)
    {T : Over S} (y : T ⟶ P.A) (hy : y ^ k = 1) : WeilIs P.A P.L k 1 y 1 := by
  obtain ⟨H1, H2, -, -⟩ := hW S P k T
  obtain ⟨c, hc, -⟩ := H1 1 y (one_pow k) hy
  have hcc : WeilIs P.A P.L k 1 y (c * c) := by simpa using H2 1 1 y c c hc hc
  have huniq := (H1 1 y (one_pow k) hy).unique hc hcc

  have hc1 : c = 1 := mul_left_cancel (huniq.symm.trans (mul_one c).symm)
  rw [← hc1]
  exact hc

/- English proof (translation)
Establish `hpow : ∀ n : ℕ, WeilIs P.A P.L k (x ^ n) y (c ^ n)`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simpa using weil_one_left hW P k y hy`. Consider the case `succ n ih`.

Rewrite using `[pow_succ, pow_succ]`. Conclude with `(hW S P k T).2.1 _ _ _ _ _ ih hc`. Establish `h1` using `hpow k`. Rewrite `h1` using `[hx]`. Conclude with `((hW S P k T).1 1 y (one_pow k) hy).unique h1 (weil_one_left hW P k y hy)`.
-/
lemma weil_pow_eq_one (hW : WeilSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) (k : ℕ)
    {T : Over S} (x y : T ⟶ P.A) (hx : x ^ k = 1) (hy : y ^ k = 1) (c : Γ(T.left, ⊤)ˣ)
    (hc : WeilIs P.A P.L k x y c) : c ^ k = 1 := by
  have hpow : ∀ n : ℕ, WeilIs P.A P.L k (x ^ n) y (c ^ n) := by
    intro n
    induction n with
    | zero => simpa using weil_one_left hW P k y hy
    | succ n ih =>
      rw [pow_succ, pow_succ]
      exact (hW S P k T).2.1 _ _ _ _ _ ih hc
  have h1 := hpow k
  rw [hx] at h1
  exact ((hW S P k T).1 1 y (one_pow k) hy).unique h1 (weil_one_left hW P k y hy)

/- English proof (translation)
The claim follows from `((hW S P k T).1 x y hx hy).unique hc hc'`.
-/
lemma weil_unique (hW : WeilSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) (k : ℕ)
    {T : Over S} (x y : T ⟶ P.A) (hx : x ^ k = 1) (hy : y ^ k = 1) (c c' : Γ(T.left, ⊤)ˣ)
    (hc : WeilIs P.A P.L k x y c) (hc' : WeilIs P.A P.L k x y c') : c = c' :=
  ((hW S P k T).1 x y hx hy).unique hc hc'

end Weil

section Gen

open ReciprocityTheory.ChartRestriction.G.DVR TopologicalSpace

/- English proof (translation)
Take `rfl : U = Z` from `le_antisymm h' h`. Establish `h1 : homOfLE h = 𝟙 U` using `rfl`. Establish `h2 : homOfLE h' = 𝟙 U` using `rfl`. Use `ext`. Simplify using `[res, h1, h2]`.
-/
lemma res_le_le {X : Scheme.{0}} {U Z : X.Opens} (h : Z ≤ U) (h' : U ≤ Z) (x : Γ(X, U)ˣ) :
    res h' (res h x) = x := by
  obtain rfl : U = Z := le_antisymm h' h
  have h1 : homOfLE h = 𝟙 U := rfl
  have h2 : homOfLE h' = 𝟙 U := rfl
  ext
  simp [res, h1, h2]

/- English proof (translation)
Use `eq_top_iff.mpr fun y _ => ?_` and prove the remaining obligations. Conclude with `(IsLocalRing.specializes_closedPoint (R := V) y).mem_open U.isOpen hU`.
-/
lemma top_of_closedPoint {V : Type} [CommRing V] [IsLocalRing V] (U : (Spec (CommRingCat.of V)).Opens)
    (hU : (IsLocalRing.closedPoint V : Spec (CommRingCat.of V)) ∈ U) : U = ⊤ := by
  refine eq_top_iff.mpr fun y _ => ?_
  exact (IsLocalRing.specializes_closedPoint (R := V) y).mem_open U.isOpen hU

/- English proof (translation)
Establish `hp : (IsLocalRing.closedPoint V : Spec (CommRingCat.of V)) ∈ ⨆ i, M.U i`. Rewrite using `[hM.cover]`. Conclude with `TopologicalSpace.Opens.mem_top _`. Take `⟨i0, hi0⟩` from `TopologicalSpace.Opens.mem_iSup.mp hp`. Establish `htop : M.U i0 = ⊤` using `top_of_closedPoint (M.U i0) hi0`.

Establish `hle : ∀ W : (Spec (CommRingCat.of V)).Opens, W ≤ M.U i0` using `fun W => by`. Rewrite using `[htop]`. Conclude with `le_top`. Establish `hid : ∀ {W : (Spec (CommRingCat.of V)).Opens} (h0 : W ≤ W) (z : Γ(Spec (CommRingCat.of V), W)ˣ), res h0 z = z`. Introduce `W h0 z`.

Establish `h1 : homOfLE h0 = 𝟙 W` using `rfl`. Use `ext`. Simplify using `[res, h1]`. Use `⟨⟨fun i => res (le_inf le_rfl (hle _) : M.U i ≤ M.U i ⊓ M.U i0) (M.g i i0)⟩, ?_⟩` and prove the remaining obligations. Introduce `i j`.

Establish `hc` using `hM.cocycle i j i0`. Establish `h' : M.U i ⊓ M.U j ≤ M.U i ⊓ M.U j ⊓ M.U i0` using `le_inf le_rfl (hle _)`. Establish `hc'` using `congrArg (fun z => res h' z) hc`. Simplify using `only [map_mul, res_res', hid] at hc'`. Simplify using `only [res_res']`.

Conclude with `hc'.symm`.
-/
theorem gen_local {V : Type} [CommRing V] [IsLocalRing V]
    (M : LB (Spec (CommRingCat.of V))) (hM : M.IsLB) : ∃ e : M.Gen, e.IsGen := by

  have hp : (IsLocalRing.closedPoint V : Spec (CommRingCat.of V)) ∈ ⨆ i, M.U i := by
    rw [hM.cover]
    exact TopologicalSpace.Opens.mem_top _
  obtain ⟨i0, hi0⟩ := TopologicalSpace.Opens.mem_iSup.mp hp
  have htop : M.U i0 = ⊤ := top_of_closedPoint (M.U i0) hi0
  have hle : ∀ W : (Spec (CommRingCat.of V)).Opens, W ≤ M.U i0 := fun W => by
    rw [htop]
    exact le_top
  have hid : ∀ {W : (Spec (CommRingCat.of V)).Opens} (h0 : W ≤ W) (z : Γ(Spec (CommRingCat.of V), W)ˣ), res h0 z = z := by
    intro W h0 z
    have h1 : homOfLE h0 = 𝟙 W := rfl
    ext
    simp [res, h1]

  refine ⟨⟨fun i => res (le_inf le_rfl (hle _) : M.U i ≤ M.U i ⊓ M.U i0) (M.g i i0)⟩, ?_⟩
  intro i j
  have hc := hM.cocycle i j i0
  have h' : M.U i ⊓ M.U j ≤ M.U i ⊓ M.U j ⊓ M.U i0 := le_inf le_rfl (hle _)
  have hc' := congrArg (fun z => res h' z) hc
  simp only [map_mul, res_res', hid] at hc'
  simp only [res_res']
  exact hc'.symm

/- English proof (translation)
The claim follows from `gen_local _ (by first | exact linComb_isLB | exact linComb_isLB hL | exact linComb_isLB (hL := hL) | exact linComb_isLB hL φ ε | exact linComb_isLB L hL φ ε | exact linComb_isLB (L := L) (φ := φ) (ε := ε) hL | exact linComb_isLB L φ ε hL)`.
-/
theorem gen_local_linComb {V : Type} [CommRing V] [IsLocalRing V] {X : Scheme.{0}} (L : LB X)
    (hL : L.IsLB) {K : Type} [Fintype K] (φ : K → (Spec (CommRingCat.of V) ⟶ X)) (ε : K → ℤ) :
    ∃ e : LB.Gen (LB.LinComb L φ ε), e.IsGen :=
  gen_local _ (by
    first
      | exact linComb_isLB
      | exact linComb_isLB hL
      | exact linComb_isLB (hL := hL)
      | exact linComb_isLB hL φ ε
      | exact linComb_isLB L hL φ ε
      | exact linComb_isLB (L := L) (φ := φ) (ε := ε) hL
      | exact linComb_isLB L φ ε hL)

end Gen

end ReciprocityTheory.ChartRestriction.G.H1.ClosedPointWeilPower
