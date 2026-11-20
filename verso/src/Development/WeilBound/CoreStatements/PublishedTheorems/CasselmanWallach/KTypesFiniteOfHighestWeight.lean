import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.SmoothSeminormAndSobolevBounds
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirAlgebra.MulMulSubMulMulEqAdd

noncomputable section

open ReciprocityTheory.ChartRestriction.DS (casimirK IsGlRep IsInfUnitary IsKHWVec IsKStableSub adjSign)
open scoped InnerProductSpace

namespace PositivityTheory.CW.HighestWeightKernel

variable {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {E : Fin n → Fin n → Module.End ℂ V}

/- English proof (translation)
Use `hU b a x y` as an intermediate fact. Simplify `this` using `[adjSign, h.symm]`.
-/
theorem inner_compact (hU : IsInfUnitary ε E) {a b : Fin n} (h : ε a = ε b) (x y : V) :
    ⟪E b a x, y⟫_ℂ = ⟪x, E a b y⟫_ℂ := by
  have := hU b a x y
  simpa [adjSign, h.symm] using this

/- English proof (translation)
Use `choose S hSfin hSmem hSk using hL`. Set `bW` to `Module.finBasis ℂ W`. Set `Y : Submodule ℂ V` to `⨆ i, S (bW i : V)`. Use `haveI : ∀ i, FiniteDimensional ℂ (S (bW i : V)) := fun i => hSfin _`. Use `⟨Y, Submodule.finite_iSup _, ?_, ?_⟩` and prove the remaining obligations.

Introduce `a b hab v hv`. Use `Submodule.iSup_induction (fun i => S (bW i : V)) (motive := fun x => E a b x ∈ Y) hv ?_ ?_ ?_` and prove the remaining obligations. Introduce `i x hx`. Conclude with `(le_iSup (fun i => S (bW i : V)) i) (hSk _ a b hab x hx)`. Simplify using the standard rewrite rules.

Introduce `x y hx hy`. Rewrite using `[map_add]`. Conclude with `add_mem hx hy`. Introduce `w hw`. Establish `hrep` using `bW.sum_repr ⟨w, hw⟩`.

Establish `hw' : w = ∑ i, (bW.repr ⟨w, hw⟩ i) • (bW i : V)`. Use `congrArg Subtype.val hrep` as an intermediate fact. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul] at this`. Conclude with `this.symm`. Rewrite using `[hw']`.

Use `Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ ?_)` and prove the remaining obligations. Conclude with `(le_iSup (fun i => S (bW i : V)) i) (hSmem _)`.
-/
theorem exists_hull (hL : LocFin ε E) (W : Submodule ℂ V) [FiniteDimensional ℂ W] :
    ∃ Y : Submodule ℂ V, FiniteDimensional ℂ Y ∧ IsKStableSub ε E Y ∧ W ≤ Y := by
  classical
  choose S hSfin hSmem hSk using hL
  let bW := Module.finBasis ℂ W
  let Y : Submodule ℂ V := ⨆ i, S (bW i : V)
  haveI : ∀ i, FiniteDimensional ℂ (S (bW i : V)) := fun i => hSfin _
  refine ⟨Y, Submodule.finite_iSup _, ?_, ?_⟩
  · intro a b hab v hv
    refine Submodule.iSup_induction (fun i => S (bW i : V)) (motive := fun x => E a b x ∈ Y) hv ?_ ?_ ?_
    · intro i x hx
      exact (le_iSup (fun i => S (bW i : V)) i) (hSk _ a b hab x hx)
    · simp
    · intro x y hx hy
      rw [map_add]
      exact add_mem hx hy
  · intro w hw
    have hrep := bW.sum_repr ⟨w, hw⟩
    have hw' : w = ∑ i, (bW.repr ⟨w, hw⟩ i) • (bW i : V) := by
      have := congrArg Subtype.val hrep
      simp only [Submodule.coe_sum, Submodule.coe_smul] at this
      exact this.symm
    rw [hw']
    refine Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ ?_)
    exact (le_iSup (fun i => S (bW i : V)) i) (hSmem _)

/- English proof (translation)
Simplify using `only [ReciprocityTheory.ChartRestriction.DS.casimirK, LinearMap.sum_apply, Module.End.mul_apply, inner_sum]`. Use `push_cast`. Use `Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b hb => ?_))` and prove the remaining obligations. Establish `hba : ε b = ε a` using `(Finset.mem_filter.1 hb).2`. Rewrite using `[← inner_compact hU hba.symm, inner_self_eq_norm_sq_to_K]`.

Use `first`. Consider the case `rfl`. Consider the case `simp`. Consider the case `norm_cast`.
-/
theorem inner_casimirK (hU : IsInfUnitary ε E) (w : V) :
    ⟪w, casimirK ε E w⟫_ℂ =
      ((∑ a, ∑ b ∈ Finset.univ.filter (fun b => ε b = ε a), ‖E b a w‖ ^ 2 : ℝ) : ℂ) := by
  simp only [ReciprocityTheory.ChartRestriction.DS.casimirK, LinearMap.sum_apply, Module.End.mul_apply, inner_sum]
  push_cast
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b hb => ?_))
  have hba : ε b = ε a := (Finset.mem_filter.1 hb).2
  rw [← inner_compact hU hba.symm, inner_self_eq_norm_sq_to_K]
  first
    | rfl
    | simp
    | norm_cast

/- English proof (translation)
Simplify using `[LinearMap.mem_ker, sub_eq_zero]`.
-/
theorem mem_ker_iff (μ : ℝ) (x : V) :
    x ∈ LinearMap.ker (casimirK ε E - (μ : ℂ) • (1 : Module.End ℂ V)) ↔ casimirK ε E x = (μ : ℂ) • x := by
  simp [LinearMap.mem_ker, sub_eq_zero]

/- English proof (translation)
Establish `h1` using `inner_casimirK hU w`. Rewrite `h1` using `[hwμ, inner_smul_right, inner_self_eq_norm_sq_to_K]`. Establish `h2 : μ * ‖w‖ ^ 2 = ∑ a, ∑ b ∈ Finset.univ.filter (fun b => ε b = ε a), ‖E b a w‖ ^ 2`. Apply `Complex.ofReal_injective` to reduce the goal to its premises. Rewrite using `[Complex.ofReal_mul, Complex.ofReal_pow]`.

Conclude with `h1`. Establish `h3 : ∑ a, Λ a ^ 2 * ‖w‖ ^ 2 ≤ ∑ a, ∑ b ∈ Finset.univ.filter (fun b => ε b = ε a), ‖E b a w‖ ^ 2`. Use `Finset.sum_le_sum (fun a _ => ?_)` and prove the remaining obligations. Establish `hmem : a ∈ Finset.univ.filter (fun b => ε b = ε a)` using `by simp`. Establish `hle` using `Finset.single_le_sum (f := fun b => ‖E b a w‖ ^ 2) (fun b _ => by positivity) hmem`.

Establish `hEa : ‖E a a w‖ ^ 2 = Λ a ^ 2 * ‖w‖ ^ 2`. Rewrite using `[hkw.1 a, norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hpos : 0 < ‖w‖ ^ 2` using `by positivity`. Rewrite `h3` using `[← Finset.sum_mul]`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem sq_le_of_khw (hU : IsInfUnitary ε E) {w : V} (hw0 : w ≠ 0) {μ : ℝ} (hwμ : casimirK ε E w = (μ : ℂ) • w)
    {Λ : Fin n → ℝ} (hkw : IsKHWVec ε E Λ w) : (∑ a, Λ a ^ 2) ≤ μ := by
  have h1 := inner_casimirK hU w
  rw [hwμ, inner_smul_right, inner_self_eq_norm_sq_to_K] at h1
  have h2 : μ * ‖w‖ ^ 2 = ∑ a, ∑ b ∈ Finset.univ.filter (fun b => ε b = ε a), ‖E b a w‖ ^ 2 := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_mul, Complex.ofReal_pow]
    exact h1
  have h3 : ∑ a, Λ a ^ 2 * ‖w‖ ^ 2 ≤ ∑ a, ∑ b ∈ Finset.univ.filter (fun b => ε b = ε a), ‖E b a w‖ ^ 2 := by
    refine Finset.sum_le_sum (fun a _ => ?_)
    have hmem : a ∈ Finset.univ.filter (fun b => ε b = ε a) := by simp
    have hle := Finset.single_le_sum (f := fun b => ‖E b a w‖ ^ 2) (fun b _ => by positivity) hmem
    have hEa : ‖E a a w‖ ^ 2 = Λ a ^ 2 * ‖w‖ ^ 2 := by
      rw [hkw.1 a, norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    linarith
  have hpos : 0 < ‖w‖ ^ 2 := by positivity
  rw [← Finset.sum_mul] at h3
  nlinarith

/- English proof (translation)
Establish `key : ∀ k : ℕ, ∀ Z : Submodule ℂ V, FiniteDimensional ℂ Z → Module.finrank ℂ Z = k → IsKStableSub ε E Z → (∀ z ∈ Z, casimirK ε E z = (μ : ℂ) • z) → Z ≤ Y`. Introduce `k`. Proceed by induction on `k using Nat.strong_induction_on with`. Consider the case `_ k ih`. Introduce `Z hZf hZk hZs hZc`.

Distinguish the cases in `hZ0 : Z = ⊥`. Rewrite using `[hZ0]`. Conclude with `bot_le`. Take `⟨w, Λ, hwZ, hw0, hkw⟩` from `h3 Z hZf hZs hZ0`. Establish `hΛ : ∀ a, ∃ z : ℤ, Λ a = z` using `fun a => hint w a (Λ a) hw0 (hkw.1 a)`.

Use `choose Λz hΛz using hΛ`. Establish `hkw' : IsKHWVec ε E (fun a => ((Λz a : ℤ) : ℝ)) w`. Establish `: Λ = fun a => ((Λz a : ℤ) : ℝ)` using `funext hΛz`. Rewrite using `[← this]`. Conclude with `hkw`.

Establish `hsq : (∑ a, ((Λz a : ℤ) : ℝ) ^ 2) ≤ μ` using `sq_le_of_khw hU hw0 (hZc w hwZ) hkw'`. Establish `hwY : w ∈ Y` using `hY w Λz hkw' hsq`. Set `Kw : Submodule ℂ V` to `sInf {T | w ∈ T ∧ IsKStableSub ε E T}`. Establish `hKwS : IsKStableSub ε E Kw`. Introduce `a b hab x hx`.

Rewrite `hx`, the goal using `[Submodule.mem_sInf]`. Introduce `T hT`. Conclude with `hT.2 a b hab x (hx T hT)`. Establish `hwKw : w ∈ Kw` using `Submodule.mem_sInf.2 (fun T hT => hT.1)`. Establish `hKwZ : Kw ≤ Z` using `sInf_le ⟨hwZ, hZs⟩`.

Establish `hKwY : Kw ≤ Y` using `sInf_le ⟨hwY, hYk⟩`. Use `haveI : FiniteDimensional ℂ Kw := Submodule.finiteDimensional_of_le hKwZ`. Establish `hZ'lt : Kwᗮ ⊓ Z < Z`. Use `lt_of_le_of_ne inf_le_right (fun h => ?_)` and prove the remaining obligations. Establish `hwZ' : w ∈ Kwᗮ ⊓ Z`.

Rewrite using `[h]`. Conclude with `hwZ`. Establish `h0 : ⟪w, w⟫_ℂ = 0` using `Submodule.inner_right_of_mem_orthogonal hwKw hwZ'.1`. Conclude with `hw0 (inner_self_eq_zero.1 h0)`. Use `haveI : FiniteDimensional ℂ (Kwᗮ ⊓ Z : Submodule ℂ V) := Submodule.finiteDimensional_of_le inf_le_right`.

Establish `hZ'k : IsKStableSub ε E (Kwᗮ ⊓ Z)`. Introduce `a b hab x hx`. Use `⟨?_, hZs a b hab x hx.2⟩` and prove the remaining obligations. Use `show E a b x ∈ Kwᗮ`. Rewrite using `[Submodule.mem_orthogonal]`.

Introduce `u hu`. Rewrite using `[← inner_compact hU hab]`. Conclude with `Submodule.inner_right_of_mem_orthogonal (hKwS b a hab.symm u hu) hx.1`. Establish `hlt : Module.finrank ℂ (Kwᗮ ⊓ Z : Submodule ℂ V) < k` using `hZk ▸ Submodule.finrank_lt_finrank_of_lt hZ'lt`. Establish `hZ'le : Kwᗮ ⊓ Z ≤ Y` using `ih _ hlt _ inferInstance rfl hZ'k (fun z hz => hZc z hz.2)`.

Establish `hsplit : Kw ⊔ Kwᗮ ⊓ Z = Z` using `Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hKwZ`. Rewrite using `[← hsplit]`. Conclude with `sup_le hKwY hZ'le`. Take `⟨S, hSf, hvS, hSk⟩` from `hL v`. Use `haveI : FiniteDimensional ℂ S := hSf`.

Set `Z : Submodule ℂ V` to `S ⊓ LinearMap.ker (casimirK ε E - (μ : ℂ) • (1 : Module.End ℂ V))`. Establish `hZk : IsKStableSub ε E Z`. Introduce `a b hab x hx`. Use `⟨hSk a b hab x hx.1, ?_⟩` and prove the remaining obligations. Establish `hx2` using `(mem_ker_iff μ x).1 hx.2`.

Use `(mem_ker_iff μ _).2 ?_` and prove the remaining obligations. Establish `hc` using `ReciprocityTheory.ChartRestriction.DS.casimirK_comm ε hgl a b hab`. Use `congrArg (fun U : Module.End ℂ V => U x) hc` as an intermediate fact. Simplify using `only [Module.End.mul_apply] at this`. Rewrite using `[this, hx2, map_smul]`.

Conclude with `key _ Z (Submodule.finiteDimensional_of_le inf_le_left) rfl hZk (fun z hz => (mem_ker_iff μ z).1 hz.2) ⟨hvS, (mem_ker_iff μ v).2 hv⟩`.
-/
theorem mem_of_eig (hgl : IsGlRep E) (hU : IsInfUnitary ε E) (hL : LocFin ε E)
    (h3 : ∀ S : Submodule ℂ V, FiniteDimensional ℂ S → IsKStableSub ε E S → S ≠ ⊥ →
      ∃ (w : V) (μ : Fin n → ℝ), w ∈ S ∧ w ≠ 0 ∧ IsKHWVec ε E μ w)
    (hint : ∀ (v : V) (a : Fin n) (x : ℝ), v ≠ 0 → E a a v = (x : ℂ) • v → ∃ z : ℤ, x = z)
    {Y : Submodule ℂ V} (hYk : IsKStableSub ε E Y) {μ : ℝ}
    (hY : ∀ (w : V) (Λ : Fin n → ℤ), IsKHWVec ε E (fun a => ((Λ a : ℤ) : ℝ)) w →
      (∑ a, ((Λ a : ℤ) : ℝ) ^ 2) ≤ μ → w ∈ Y)
    {v : V} (hv : Eig ε E μ v) : v ∈ Y := by
  classical
  have key : ∀ k : ℕ, ∀ Z : Submodule ℂ V, FiniteDimensional ℂ Z → Module.finrank ℂ Z = k →
      IsKStableSub ε E Z → (∀ z ∈ Z, casimirK ε E z = (μ : ℂ) • z) → Z ≤ Y := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro Z hZf hZk hZs hZc
      by_cases hZ0 : Z = ⊥
      · rw [hZ0]
        exact bot_le
      obtain ⟨w, Λ, hwZ, hw0, hkw⟩ := h3 Z hZf hZs hZ0
      have hΛ : ∀ a, ∃ z : ℤ, Λ a = z := fun a => hint w a (Λ a) hw0 (hkw.1 a)
      choose Λz hΛz using hΛ
      have hkw' : IsKHWVec ε E (fun a => ((Λz a : ℤ) : ℝ)) w := by
        have : Λ = fun a => ((Λz a : ℤ) : ℝ) := funext hΛz
        rw [← this]
        exact hkw
      have hsq : (∑ a, ((Λz a : ℤ) : ℝ) ^ 2) ≤ μ := sq_le_of_khw hU hw0 (hZc w hwZ) hkw'
      have hwY : w ∈ Y := hY w Λz hkw' hsq
      let Kw : Submodule ℂ V := sInf {T | w ∈ T ∧ IsKStableSub ε E T}
      have hKwS : IsKStableSub ε E Kw := by
        intro a b hab x hx
        rw [Submodule.mem_sInf] at hx ⊢
        intro T hT
        exact hT.2 a b hab x (hx T hT)
      have hwKw : w ∈ Kw := Submodule.mem_sInf.2 (fun T hT => hT.1)
      have hKwZ : Kw ≤ Z := sInf_le ⟨hwZ, hZs⟩
      have hKwY : Kw ≤ Y := sInf_le ⟨hwY, hYk⟩
      haveI : FiniteDimensional ℂ Kw := Submodule.finiteDimensional_of_le hKwZ
      have hZ'lt : Kwᗮ ⊓ Z < Z := by
        refine lt_of_le_of_ne inf_le_right (fun h => ?_)
        have hwZ' : w ∈ Kwᗮ ⊓ Z := by
          rw [h]
          exact hwZ
        have h0 : ⟪w, w⟫_ℂ = 0 := Submodule.inner_right_of_mem_orthogonal hwKw hwZ'.1
        exact hw0 (inner_self_eq_zero.1 h0)
      haveI : FiniteDimensional ℂ (Kwᗮ ⊓ Z : Submodule ℂ V) :=
        Submodule.finiteDimensional_of_le inf_le_right
      have hZ'k : IsKStableSub ε E (Kwᗮ ⊓ Z) := by
        intro a b hab x hx
        refine ⟨?_, hZs a b hab x hx.2⟩
        show E a b x ∈ Kwᗮ
        rw [Submodule.mem_orthogonal]
        intro u hu
        rw [← inner_compact hU hab]
        exact Submodule.inner_right_of_mem_orthogonal (hKwS b a hab.symm u hu) hx.1
      have hlt : Module.finrank ℂ (Kwᗮ ⊓ Z : Submodule ℂ V) < k :=
        hZk ▸ Submodule.finrank_lt_finrank_of_lt hZ'lt
      have hZ'le : Kwᗮ ⊓ Z ≤ Y :=
        ih _ hlt _ inferInstance rfl hZ'k (fun z hz => hZc z hz.2)
      have hsplit : Kw ⊔ Kwᗮ ⊓ Z = Z :=
        Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hKwZ
      rw [← hsplit]
      exact sup_le hKwY hZ'le
  obtain ⟨S, hSf, hvS, hSk⟩ := hL v
  haveI : FiniteDimensional ℂ S := hSf
  let Z : Submodule ℂ V := S ⊓ LinearMap.ker (casimirK ε E - (μ : ℂ) • (1 : Module.End ℂ V))
  have hZk : IsKStableSub ε E Z := by
    intro a b hab x hx
    refine ⟨hSk a b hab x hx.1, ?_⟩
    have hx2 := (mem_ker_iff μ x).1 hx.2
    refine (mem_ker_iff μ _).2 ?_
    have hc := ReciprocityTheory.ChartRestriction.DS.casimirK_comm ε hgl a b hab
    have := congrArg (fun U : Module.End ℂ V => U x) hc
    simp only [Module.End.mul_apply] at this
    rw [this, hx2, map_smul]
  exact key _ Z (Submodule.finiteDimensional_of_le inf_le_left) rfl hZk
    (fun z hz => (mem_ker_iff μ z).1 hz.2) ⟨hvS, (mem_ker_iff μ v).2 hv⟩

end PositivityTheory.CW.HighestWeightKernel

namespace PositivityTheory.CW

open PositivityTheory.CW.HighestWeightKernel

/- English proof (translation)
Introduce `n ε V _ _ E hgl hU hL hfinHW hint R`. Set `F : Set (Fin n → ℤ)` to `{Λ | (∑ a, ((Λ a : ℤ) : ℝ) ^ 2) ≤ R}`. Establish `hFfin : F.Finite`. Use `(Set.Finite.pi (t := fun _ => Set.Icc (-⌈R⌉) ⌈R⌉) (fun _ => Set.finite_Icc _ _)).subset ?_` and prove the remaining obligations. Introduce `Λ hΛ a _`.

Establish `hsq : ((Λ a : ℤ) : ℝ) ^ 2 ≤ R`. Use `le_trans ?_ hΛ` and prove the remaining obligations. Conclude with `Finset.single_le_sum (f := fun b => ((Λ b : ℤ) : ℝ) ^ 2) (fun b _ => by positivity) (Finset.mem_univ a)`. Establish `h1 : ((Λ a : ℤ) : ℝ) ≤ ((Λ a : ℤ) : ℝ) ^ 2` using `by exact_mod_cast Int.le_self_sq (Λ a)`. Establish `h2 : (-(Λ a : ℤ) : ℝ) ≤ ((Λ a : ℤ) : ℝ) ^ 2`.

Use `Int.le_self_sq (-(Λ a))` as an intermediate fact. Rewrite `this` using `[neg_sq]`. Conclude with `this` after adjusting the coercions. Establish `hc` using `Int.le_ceil R`. Prove the components needed by the constructor for the conclusion.

Establish `: (-(⌈R⌉ : ℤ) : ℝ) ≤ ((Λ a : ℤ) : ℝ)` using `by linarith`. Conclude with `this` after adjusting the coercions. Establish `: ((Λ a : ℤ) : ℝ) ≤ ((⌈R⌉ : ℤ) : ℝ)` using `by linarith`. Conclude with `this` after adjusting the coercions. Use `haveI : Finite F := hFfin.to_subtype`.

Set `W0 : Submodule ℂ V` to `⨆ Λ : F, Submodule.span ℂ {w | IsKHWVec ε E (fun a => ((Λ.1 a : ℤ) : ℝ)) w}`. Use `haveI : ∀ Λ : F, FiniteDimensional ℂ (Submodule.span ℂ {w | IsKHWVec ε E (fun a => ((Λ.1 a : ℤ) : ℝ)) w}) := fun Λ => hfinHW _`. Use `haveI : FiniteDimensional ℂ W0 := Submodule.finite_iSup _`. Take `⟨Y, hYf, hYk, hWY⟩` from `exists_hull hL W0`. Use `haveI : FiniteDimensional ℂ Y := hYf`.

Use `Submodule.finiteDimensional_of_le (S₂ := Y) ?_` and prove the remaining obligations. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `v ⟨μ, hμR, hv⟩`. Use `mem_of_eig hgl hU hL (h n ε V E hgl hU) hint hYk (μ := μ) ?_ hv` and prove the remaining obligations. Introduce `w Λ hkw hsq`.

Establish `hΛF : Λ ∈ F` using `le_trans hsq hμR`. Conclude with `hWY ((le_iSup (fun Λ : F => Submodule.span ℂ {w | IsKHWVec ε E (fun a => ((Λ.1 a : ℤ) : ℝ)) w}) ⟨Λ, hΛF⟩) (Submodule.subset_span hkw))`.
-/
theorem k_types_finite_of_highest_weight (h : KStableHighestWeightVector) : KTypesBoundedFinite := by
  classical
  intro n ε V _ _ E hgl hU hL hfinHW hint R
  let F : Set (Fin n → ℤ) := {Λ | (∑ a, ((Λ a : ℤ) : ℝ) ^ 2) ≤ R}
  have hFfin : F.Finite := by
    refine (Set.Finite.pi (t := fun _ => Set.Icc (-⌈R⌉) ⌈R⌉) (fun _ => Set.finite_Icc _ _)).subset ?_
    intro Λ hΛ a _
    have hsq : ((Λ a : ℤ) : ℝ) ^ 2 ≤ R := by
      refine le_trans ?_ hΛ
      exact Finset.single_le_sum (f := fun b => ((Λ b : ℤ) : ℝ) ^ 2) (fun b _ => by positivity)
        (Finset.mem_univ a)
    have h1 : ((Λ a : ℤ) : ℝ) ≤ ((Λ a : ℤ) : ℝ) ^ 2 := by exact_mod_cast Int.le_self_sq (Λ a)
    have h2 : (-(Λ a : ℤ) : ℝ) ≤ ((Λ a : ℤ) : ℝ) ^ 2 := by
      have := Int.le_self_sq (-(Λ a))
      rw [neg_sq] at this
      exact_mod_cast this
    have hc := Int.le_ceil R
    constructor
    · have : (-(⌈R⌉ : ℤ) : ℝ) ≤ ((Λ a : ℤ) : ℝ) := by linarith
      exact_mod_cast this
    · have : ((Λ a : ℤ) : ℝ) ≤ ((⌈R⌉ : ℤ) : ℝ) := by linarith
      exact_mod_cast this
  haveI : Finite F := hFfin.to_subtype
  let W0 : Submodule ℂ V :=
    ⨆ Λ : F, Submodule.span ℂ {w | IsKHWVec ε E (fun a => ((Λ.1 a : ℤ) : ℝ)) w}
  haveI : ∀ Λ : F, FiniteDimensional ℂ
      (Submodule.span ℂ {w | IsKHWVec ε E (fun a => ((Λ.1 a : ℤ) : ℝ)) w}) := fun Λ => hfinHW _
  haveI : FiniteDimensional ℂ W0 := Submodule.finite_iSup _
  obtain ⟨Y, hYf, hYk, hWY⟩ := exists_hull hL W0
  haveI : FiniteDimensional ℂ Y := hYf
  refine Submodule.finiteDimensional_of_le (S₂ := Y) ?_
  refine Submodule.span_le.2 ?_
  rintro v ⟨μ, hμR, hv⟩
  refine mem_of_eig hgl hU hL (h n ε V E hgl hU) hint hYk (μ := μ) ?_ hv
  intro w Λ hkw hsq
  have hΛF : Λ ∈ F := le_trans hsq hμR
  exact hWY ((le_iSup (fun Λ : F => Submodule.span ℂ
    {w | IsKHWVec ε E (fun a => ((Λ.1 a : ℤ) : ℝ)) w}) ⟨Λ, hΛF⟩) (Submodule.subset_span hkw))

end PositivityTheory.CW

end
