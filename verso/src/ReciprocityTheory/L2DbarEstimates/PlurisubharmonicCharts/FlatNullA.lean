import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.ContinuousOnSec
import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.ImportsAlt
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth

namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas Set
open scoped ContDiff ENNReal

noncomputable section

universe u

section Hom

variable {n : ℕ} (De : MvPolynomial (Fin n) ℂ)

def fnHom (a : ℂ) (b : Fin n → ℂ) : ℂ :=
  ∑ m ∈ De.support, MvPolynomial.coeff m De *
    (a ^ (De.totalDegree + 1 - ∑ k, m k) * ∏ k, b k ^ m k)

/- English proof (translation)
Establish `h` using `MvPolynomial.le_totalDegree hm`. Use `first`. Consider the case `(rwa [Finsupp.sum_fintype _ _ (fun _ => rfl)] at h)`. Consider the case `(simpa [Finsupp.degree, Finsupp.sum_fintype] using h)`. Consider the case `(rwa [Finsupp.degree_eq_sum] at h)`.
-/
theorem fn_sum_le_totalDegree {m : Fin n →₀ ℕ} (hm : m ∈ De.support) :
    ∑ k, m k ≤ De.totalDegree := by
  have h := MvPolynomial.le_totalDegree hm
  first
    | (rwa [Finsupp.sum_fintype _ _ (fun _ => rfl)] at h)
    | (simpa [Finsupp.degree, Finsupp.sum_fintype] using h)
    | (rwa [Finsupp.degree_eq_sum] at h)

/- English proof (translation)
Unfold `fnHom`. Rewrite using `[MvPolynomial.eval_eq', Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations. Establish `hle` using `fn_sum_le_totalDegree De hm`. Establish `hsplit : a ^ (De.totalDegree + 1) = a ^ (De.totalDegree + 1 - ∑ k, m k) * a ^ (∑ k, m k)`.

Rewrite using `[← pow_add]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers. Establish `key : (∏ k, (b k / a) ^ m k) * a ^ (∑ k, m k) = ∏ k, b k ^ m k`. Rewrite using `[← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]`.

Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[div_pow, div_mul_cancel₀ _ (pow_ne_zero _ ha)]`. Rewrite using `[hsplit, ← key]`. The two sides agree by associativity and commutativity.
-/
theorem fn_hom_of_ne {a : ℂ} (ha : a ≠ 0) (b : Fin n → ℂ) :
    fnHom De a b = a ^ (De.totalDegree + 1) * MvPolynomial.eval (fun k => b k / a) De := by
  unfold fnHom
  rw [MvPolynomial.eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hle := fn_sum_le_totalDegree De hm
  have hsplit : a ^ (De.totalDegree + 1) = a ^ (De.totalDegree + 1 - ∑ k, m k) * a ^ (∑ k, m k) := by
    rw [← pow_add]
    congr 1
    omega
  have key : (∏ k, (b k / a) ^ m k) * a ^ (∑ k, m k) = ∏ k, b k ^ m k := by
    rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ ha)]
  rw [hsplit, ← key]
  ac_rfl

/- English proof (translation)
Unfold `fnHom`. Use `Finset.sum_eq_zero fun m hm => ?_` and prove the remaining obligations. Establish `hle` using `fn_sum_le_totalDegree De hm`. Rewrite using `[zero_pow (by omega), zero_mul, mul_zero]`.
-/
@[simp] theorem fn_hom_zero (b : Fin n → ℂ) : fnHom De 0 b = 0 := by
  unfold fnHom
  refine Finset.sum_eq_zero fun m hm => ?_
  have hle := fn_sum_le_totalDegree De hm
  rw [zero_pow (by omega), zero_mul, mul_zero]

/- English proof (translation)
Use `first`. Consider the case `exact DifferentiableOn.finset_prod (fun k _ => h k)`. Consider the case `exact DifferentiableOn.fun_finset_prod (fun k _ => h k)`. Consider the case `(classical`. Proceed by induction on `u using Finset.induction_on with`.

Consider the case `empty => simp [differentiableOn_const]`. Consider the case `insert k u hk ih`. Simplify using `only [Finset.prod_insert hk]`. Conclude with `(h _).mul ih)`.
-/
theorem fn_diffOn_prod {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {S : Set E}
    (u : Finset (Fin n)) (f : Fin n → E → ℂ) (h : ∀ k, DifferentiableOn ℂ (f k) S) :
    DifferentiableOn ℂ (fun x => ∏ k ∈ u, f k x) S := by
  first
    | exact DifferentiableOn.finset_prod (fun k _ => h k)
    | exact DifferentiableOn.fun_finset_prod (fun k _ => h k)
    | (classical
       induction u using Finset.induction_on with
       | empty => simp [differentiableOn_const]
       | insert k u hk ih =>
         simp only [Finset.prod_insert hk]
         exact (h _).mul ih)

/- English proof (translation)
Unfold `fnHom`. Establish `hterm : ∀ m ∈ De.support, DifferentiableOn ℂ (fun x => MvPolynomial.coeff m De * (a x ^ (De.totalDegree + 1 - ∑ k, m k) * ∏ k, (fun k => b k x) k ^ m k)) S` using `fun m _ => ((ha.pow _).mul (fn_diffOn_prod Finset.univ (fun k x => b k x ^ m k) (fun k => (hb k).pow _))).const_mul _`. Use `first`. Consider the case `exact DifferentiableOn.fun_sum hterm`. Consider the case `exact DifferentiableOn.sum hterm`.

Consider the case `(have e : (fun x => ∑ m ∈ De.support, MvPolynomial.coeff m De * (a x ^ (De.totalDegree + 1 - ∑ k, m k) * ∏ k, (fun k => b k x) k ^ m k)) = ∑ m ∈ De.support, fun x => MvPolynomial.coeff m De * (a x ^ (De.totalDegree + 1 - ∑ k, m k) * ∏ k, (fun k => b k x) k ^ m k) := by`. Use extensionality with `x`. Simplify using `[Finset.sum_apply]`. Rewrite using `[e]`. Conclude with `DifferentiableOn.sum hterm)`.
-/
theorem fn_diffOn_hom {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {S : Set E}
    {a : E → ℂ} {b : Fin n → E → ℂ} (ha : DifferentiableOn ℂ a S)
    (hb : ∀ k, DifferentiableOn ℂ (b k) S) :
    DifferentiableOn ℂ (fun x => fnHom De (a x) (fun k => b k x)) S := by
  unfold fnHom
  have hterm : ∀ m ∈ De.support, DifferentiableOn ℂ (fun x => MvPolynomial.coeff m De *
      (a x ^ (De.totalDegree + 1 - ∑ k, m k) * ∏ k, (fun k => b k x) k ^ m k)) S := fun m _ =>
    ((ha.pow _).mul (fn_diffOn_prod Finset.univ (fun k x => b k x ^ m k) (fun k => (hb k).pow _))).const_mul _
  first
    | exact DifferentiableOn.fun_sum hterm
    | exact DifferentiableOn.sum hterm
    | (have e : (fun x => ∑ m ∈ De.support, MvPolynomial.coeff m De *
          (a x ^ (De.totalDegree + 1 - ∑ k, m k) * ∏ k, (fun k => b k x) k ^ m k)) =
          ∑ m ∈ De.support, fun x => MvPolynomial.coeff m De *
          (a x ^ (De.totalDegree + 1 - ∑ k, m k) * ∏ k, (fun k => b k x) k ^ m k) := by
         ext x; simp [Finset.sum_apply]
       rw [e]
       exact DifferentiableOn.sum hterm)

/- English proof (translation)
Establish `hF : ∀ p : MvPolynomial (Fin n) ℂ, Differentiable ℂ (fun v : V n => MvPolynomial.eval (fun k => v k) p)`. Introduce `p`. Proceed by induction on `p using MvPolynomial.induction_on`. Use `next a =>`. Simplify using `only [MvPolynomial.eval_C]`.

Conclude with `differentiable_const a`. Use `next p q hp hq =>`. Simplify using `only [map_add]`. Conclude with `hp.add hq`. Use `next p i hp =>`.

Simplify using `only [map_mul, MvPolynomial.eval_X]`. Establish `hi : Differentiable ℂ (fun v : V n => v i)` using `by fun_prop`. Conclude with `hp.mul hi`. Establish `hEq` using `ReciprocityTheory.L2DbarEstimates.C.ident n Set.univ (fun v : V n => MvPolynomial.eval (fun k => v k) De) v0 isOpen_univ convex_univ (hF De).differentiableOn (Set.mem_univ _) h`. Apply `MvPolynomial.funext` to reduce the goal to its premises.

Introduce `x`. Use `hEq (Set.mem_univ (WithLp.toLp 2 x))` as an intermediate fact. Simplify using `using this`.
-/
theorem fn_eq_zero_of_eval {v0 : V n}
    (h : ∀ᶠ v in 𝓝 v0, MvPolynomial.eval (fun k => v k) De = 0) : De = 0 := by
  have hF : ∀ p : MvPolynomial (Fin n) ℂ,
      Differentiable ℂ (fun v : V n => MvPolynomial.eval (fun k => v k) p) := by
    intro p
    induction p using MvPolynomial.induction_on
    next a =>
      simp only [MvPolynomial.eval_C]
      exact differentiable_const a
    next p q hp hq =>
      simp only [map_add]
      exact hp.add hq
    next p i hp =>
      simp only [map_mul, MvPolynomial.eval_X]
      have hi : Differentiable ℂ (fun v : V n => v i) := by fun_prop
      exact hp.mul hi
  have hEq := ReciprocityTheory.L2DbarEstimates.C.ident n Set.univ (fun v : V n => MvPolynomial.eval (fun k => v k) De) v0
    isOpen_univ convex_univ (hF De).differentiableOn (Set.mem_univ _) h
  apply MvPolynomial.funext
  intro x
  have := hEq (Set.mem_univ (WithLp.toLp 2 x))
  simpa using this

end Hom

variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ}
  {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ}

/- English proof (translation)
Take `⟨-, htr⟩ : A.IsSecOn L Set.univ w0` from `hD.isSection_denom`. Establish `hg` using `A.g_ne L (A.pick y) i y (A.mem_pick y) hy`. Rewrite using `[htr (A.pick y) i y trivial (A.mem_pick y) hy]`. Conclude with `⟨fun h1 h2 => h1 (by rw [h2, mul_zero]), fun h1 => mul_ne_zero hg h1⟩`.
-/
theorem denominator_ne_zero_pick_iff (hD : A.D0 L w w0 s) {i : ι} {y : Y} (hy : y ∈ (A.chart i).source) :
    w0 (A.pick y) y ≠ 0 ↔ w0 i y ≠ 0 := by
  obtain ⟨-, htr⟩ : A.IsSecOn L Set.univ w0 := hD.isSection_denom
  have hg := A.g_ne L (A.pick y) i y (A.mem_pick y) hy
  rw [htr (A.pick y) i y trivial (A.mem_pick y) hy]
  exact ⟨fun h1 h2 => h1 (by rw [h2, mul_zero]), fun h1 => mul_ne_zero hg h1⟩

/- English proof (translation)
Take `⟨-, htr0⟩ : A.IsSecOn L Set.univ w0` from `hD.isSection_denom`. Establish `hg` using `A.g_ne L (A.pick y) i y (A.mem_pick y) hy`. Unfold `zmap`. Use `congr 1`. Use function extensionality and compare the values at `k`.

Take `⟨-, htrk⟩ : A.IsSecOn L Set.univ (s k)` from `hD.sec_s k`. Rewrite using `[htrk (A.pick y) i y trivial (A.mem_pick y) hy, htr0 (A.pick y) i y trivial (A.mem_pick y) hy, mul_div_mul_left _ _ hg]`.
-/
theorem fn_zmap_eq (hD : A.D0 L w w0 s) {i : ι} {y : Y} (hy : y ∈ (A.chart i).source) :
    A.zmap w0 s y = WithLp.toLp 2 (fun k => s k i y / w0 i y) := by
  obtain ⟨-, htr0⟩ : A.IsSecOn L Set.univ w0 := hD.isSection_denom
  have hg := A.g_ne L (A.pick y) i y (A.mem_pick y) hy
  unfold zmap
  congr 1
  funext k
  obtain ⟨-, htrk⟩ : A.IsSecOn L Set.univ (s k) := hD.sec_s k
  rw [htrk (A.pick y) i y trivial (A.mem_pick y) hy, htr0 (A.pick y) i y trivial (A.mem_pick y) hy,
    mul_div_mul_left _ _ hg]

/- English proof (translation)
Distinguish the cases in `h0 : w0 i y = 0`. Rewrite using `[h0, fn_hom_zero]`. Prove the components needed by the constructor for the conclusion. Introduce `hm`. Take `⟨h1, -⟩` from `hm`.

Conclude with `absurd ((denominator_ne_zero_pick_iff A hD hy).1 h1) (by simp [h0])`. Introduce `h`. Conclude with `absurd rfl h`. Rewrite using `[fn_hom_of_ne De h0]`. Establish `hz` using `fn_zmap_eq A hD hy`.

Simplify using `only [Mset, Set.mem_setOf_eq, hz]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨-, h2⟩`. Conclude with `mul_ne_zero (pow_ne_zero _ h0) (by simpa using h2)`. Introduce `h2`.

Conclude with `⟨(denominator_ne_zero_pick_iff A hD hy).2 h0, by simpa using right_ne_zero_of_mul h2⟩`.
-/
theorem fn_mem_Mset_iff (hD : A.D0 L w w0 s) {i : ι} {y : Y} (hy : y ∈ (A.chart i).source) :
    y ∈ A.Mset w0 s De ↔ fnHom De (w0 i y) (fun k => s k i y) ≠ 0 := by
  by_cases h0 : w0 i y = 0
  · rw [h0, fn_hom_zero]
    constructor
    · intro hm
      obtain ⟨h1, -⟩ := hm
      exact absurd ((denominator_ne_zero_pick_iff A hD hy).1 h1) (by simp [h0])
    · intro h
      exact absurd rfl h
  · rw [fn_hom_of_ne De h0]
    have hz := fn_zmap_eq A hD hy
    simp only [Mset, Set.mem_setOf_eq, hz]
    constructor
    · rintro ⟨-, h2⟩
      exact mul_ne_zero (pow_ne_zero _ h0) (by simpa using h2)
    · intro h2
      exact ⟨(denominator_ne_zero_pick_iff A hD hy).2 h0, by simpa using right_ne_zero_of_mul h2⟩

def fnG (w0 : ι → Y → ℂ) (s : Fin n → ι → Y → ℂ) (De : MvPolynomial (Fin n) ℂ) (i : ι)
    (v : V n) : ℂ :=
  fnHom De (w0 i ((A.chart i).symm v)) (fun k => s k i ((A.chart i).symm v))

/- English proof (translation)
Take `⟨h0, -⟩ : A.IsSecOn L Set.univ w0` from `hD.isSection_denom`. Establish `hw : DifferentiableOn ℂ (fun v => w0 i ((A.chart i).symm v)) (A.chart i).target`. Use `h0 i` as an intermediate fact. Rewrite `this` using `[Set.preimage_univ, Set.inter_univ]`. Then use the resulting hypothesis. Establish `hs : ∀ k, DifferentiableOn ℂ (fun v => s k i ((A.chart i).symm v)) (A.chart i).target`.

Introduce `k`. Take `⟨hk, -⟩ : A.IsSecOn L Set.univ (s k)` from `hD.sec_s k`. Use `hk i` as an intermediate fact. Rewrite `this` using `[Set.preimage_univ, Set.inter_univ]`. Then use the resulting hypothesis. Conclude with `fn_diffOn_hom De hw hs`.
-/
theorem fn_diffG (hD : A.D0 L w w0 s) (i : ι) :
    DifferentiableOn ℂ (fnG A w0 s De i) (A.chart i).target := by
  obtain ⟨h0, -⟩ : A.IsSecOn L Set.univ w0 := hD.isSection_denom
  have hw : DifferentiableOn ℂ (fun v => w0 i ((A.chart i).symm v)) (A.chart i).target := by
    have := h0 i
    rwa [Set.preimage_univ, Set.inter_univ] at this
  have hs : ∀ k, DifferentiableOn ℂ (fun v => s k i ((A.chart i).symm v)) (A.chart i).target := by
    intro k
    obtain ⟨hk, -⟩ : A.IsSecOn L Set.univ (s k) := hD.sec_s k
    have := hk i
    rwa [Set.preimage_univ, Set.inter_univ] at this
  exact fn_diffOn_hom De hw hs

/- English proof (translation)
The claim follows from `(fn_mem_Mset_iff A hD ((A.chart i).map_target hv)).symm`.
-/
theorem fn_G_ne_iff (hD : A.D0 L w w0 s) {i : ι} {v : V n} (hv : v ∈ (A.chart i).target) :
    fnG A w0 s De i v ≠ 0 ↔ (A.chart i).symm v ∈ A.Mset w0 s De := (fn_mem_Mset_iff A hD ((A.chart i).map_target hv)).symm

/- English proof (translation)
Introduce `H`. Apply `hF.De_ne` to reduce the goal to its premises. Use `set i := A.pick P with hi`. Establish `hPs : P ∈ (A.chart i).source` using `A.mem_pick P`. Use `set c := A.chart i P with hc`.

Establish `hct : c ∈ (A.chart i).target` using `(A.chart i).map_source hPs`. Establish `hsymm : (A.chart i).symm c = P` using `(A.chart i).left_inv hPs`. Take `⟨h0, -⟩ : A.IsSecOn L Set.univ w0` from `hD.isSection_denom`. Establish `hw : DifferentiableOn ℂ (fun v => w0 i ((A.chart i).symm v)) (A.chart i).target`. Use `h0 i` as an intermediate fact.

Rewrite `this` using `[Set.preimage_univ, Set.inter_univ]`. Then use the resulting hypothesis. Establish `hs : ∀ k, DifferentiableOn ℂ (fun v => s k i ((A.chart i).symm v)) (A.chart i).target`. Introduce `k`. Take `⟨hk, -⟩ : A.IsSecOn L Set.univ (s k)` from `hD.sec_s k`. Use `hk i` as an intermediate fact.

Rewrite `this` using `[Set.preimage_univ, Set.inter_univ]`. Then use the resulting hypothesis. Establish `hw0P : w0 i P ≠ 0` using `hD.w0_ne P hP`. Set `U` to `(A.chart i).target ∩ (fun v => w0 i ((A.chart i).symm v)) ⁻¹' {0}ᶜ`. Establish `hUo : IsOpen U` using `hw.continuousOn.isOpen_inter_preimage (A.chart i).open_target isOpen_compl_singleton`. Establish `hcU : c ∈ U` using `⟨hct, by show w0 i ((A.chart i).symm c) ≠ 0`.

Rewrite using `[hsymm]`. Conclude with `hw0P⟩`. Establish `hcd : ContDiffOn ℂ ∞ (A.zLoc w0 s i) U`. Rewrite using `[contDiffOn_piLp]`. Introduce `k`.

Establish `hk : DifferentiableOn ℂ (fun v => s k i ((A.chart i).symm v) / w0 i ((A.chart i).symm v)) U`. Establish `hne : ∀ v ∈ U, w0 i ((A.chart i).symm v) ≠ 0` using `fun v hv => hv.2`. Introduce `v hv`. Establish `h1 : DifferentiableWithinAt ℂ (fun v => s k i ((A.chart i).symm v)) U v` using `((hs k).mono Set.inter_subset_left) v hv`. Establish `h2 : DifferentiableWithinAt ℂ (fun v => w0 i ((A.chart i).symm v)) U v` using `(hw.mono Set.inter_subset_left) v hv`.

Establish `h3 : DifferentiableWithinAt ℂ (fun v => s k i ((A.chart i).symm v) * (w0 i ((A.chart i).symm v))⁻¹) U v` using `h1.mul (h2.inv (hne v hv))`. Simplify `h3` using `only [div_eq_mul_inv]`. Conclude with `contDiffOn_of_differentiableOn n _ U hUo hk`. Establish `hcda : ContDiffAt ℂ ∞ (A.zLoc w0 s i) c` using `hcd.contDiffAt (hUo.mem_nhds hcU)`. Establish `hstr : HasStrictFDerivAt (A.zLoc w0 s i) (fderiv ℂ (A.zLoc w0 s i) c) c` using `by first`.

Consider the case `exact hcda.hasStrictFDerivAt (by simp)`. Consider the case `exact hcda.hasStrictFDerivAt (by norm_num)`. Consider the case `exact hcda.hasStrictFDerivAt (by exact_mod_cast le_top)`. Establish `hdet : LinearMap.det (fderiv ℂ (A.zLoc w0 s i) c : V n →ₗ[ℂ] V n) ≠ 0` using `hD.coord P hP`. Set `e : V n ≃L[ℂ] V n` to `(LinearMap.equivOfDetNeZero (fderiv ℂ (A.zLoc w0 s i) c : V n →ₗ[ℂ] V n) hdet).toContinuousLinearEquiv`.

Establish `hstrict : HasStrictFDerivAt (A.zLoc w0 s i) (e : V n →L[ℂ] V n) c` using `hstr.congr_fderiv (by ext v; rfl)`. Establish `H2 : ∀ᶠ v in 𝓝 c, (A.chart i).symm v ∉ A.Mset w0 s De`. Establish `hm` using `(A.chart i).symm_map_nhds_eq hPs`. Rewrite `H` using `[← hm]`. Conclude with `H`.

Establish `H3 : ∀ᶠ v in 𝓝 c, MvPolynomial.eval (fun k => (A.zLoc w0 s i v) k) De = 0` using `by filter_upwards [H2, hUo.mem_nhds hcU] with v hv hvU`. Establish `hvs : (A.chart i).symm v ∈ (A.chart i).source` using `(A.chart i).map_target hvU.1`. Establish `hw0v : w0 i ((A.chart i).symm v) ≠ 0` using `hvU.2`. Establish `h1` using `(fn_mem_Mset_iff A hD hvs).not.mp hv`. Rewrite `h1` using `[not_not, fn_hom_of_ne De hw0v]`.

Establish `h2` using `(mul_eq_zero.mp h1).resolve_left (pow_ne_zero _ hw0v)`. Simplify `h2` using `[WeightedAtlas.zLoc]`. Establish `H4 : ∀ᶠ z in 𝓝 (A.zLoc w0 s i c), MvPolynomial.eval (fun k => z k) De = 0`. Rewrite using `[← hstrict.map_nhds_eq_of_equiv]`. Conclude with `H3`.

Conclude with `fn_eq_zero_of_eval De H4`.
-/
theorem fn_not_ev (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De) {P : Y} (hP : P ∈ A.zeroSet s) :
    ¬ ∀ᶠ y in 𝓝 P, y ∉ A.Mset w0 s De := by
  intro H
  apply hF.De_ne
  set i := A.pick P with hi
  have hPs : P ∈ (A.chart i).source := A.mem_pick P
  set c := A.chart i P with hc
  have hct : c ∈ (A.chart i).target := (A.chart i).map_source hPs
  have hsymm : (A.chart i).symm c = P := (A.chart i).left_inv hPs
  obtain ⟨h0, -⟩ : A.IsSecOn L Set.univ w0 := hD.isSection_denom
  have hw : DifferentiableOn ℂ (fun v => w0 i ((A.chart i).symm v)) (A.chart i).target := by
    have := h0 i
    rwa [Set.preimage_univ, Set.inter_univ] at this
  have hs : ∀ k, DifferentiableOn ℂ (fun v => s k i ((A.chart i).symm v)) (A.chart i).target := by
    intro k
    obtain ⟨hk, -⟩ : A.IsSecOn L Set.univ (s k) := hD.sec_s k
    have := hk i
    rwa [Set.preimage_univ, Set.inter_univ] at this
  have hw0P : w0 i P ≠ 0 := hD.w0_ne P hP
  let U := (A.chart i).target ∩ (fun v => w0 i ((A.chart i).symm v)) ⁻¹' {0}ᶜ
  have hUo : IsOpen U := hw.continuousOn.isOpen_inter_preimage (A.chart i).open_target isOpen_compl_singleton
  have hcU : c ∈ U := ⟨hct, by
    show w0 i ((A.chart i).symm c) ≠ 0
    rw [hsymm]; exact hw0P⟩
  have hcd : ContDiffOn ℂ ∞ (A.zLoc w0 s i) U := by
    rw [contDiffOn_piLp]
    intro k
    have hk : DifferentiableOn ℂ (fun v => s k i ((A.chart i).symm v) / w0 i ((A.chart i).symm v)) U := by
      have hne : ∀ v ∈ U, w0 i ((A.chart i).symm v) ≠ 0 := fun v hv => hv.2
      intro v hv
      have h1 : DifferentiableWithinAt ℂ (fun v => s k i ((A.chart i).symm v)) U v :=
        ((hs k).mono Set.inter_subset_left) v hv
      have h2 : DifferentiableWithinAt ℂ (fun v => w0 i ((A.chart i).symm v)) U v :=
        (hw.mono Set.inter_subset_left) v hv
      have h3 : DifferentiableWithinAt ℂ
          (fun v => s k i ((A.chart i).symm v) * (w0 i ((A.chart i).symm v))⁻¹) U v :=
        h1.mul (h2.inv (hne v hv))
      simpa only [div_eq_mul_inv] using h3
    exact contDiffOn_of_differentiableOn n _ U hUo hk
  have hcda : ContDiffAt ℂ ∞ (A.zLoc w0 s i) c := hcd.contDiffAt (hUo.mem_nhds hcU)
  have hstr : HasStrictFDerivAt (A.zLoc w0 s i) (fderiv ℂ (A.zLoc w0 s i) c) c := by
    first
    | exact hcda.hasStrictFDerivAt (by simp)
    | exact hcda.hasStrictFDerivAt (by norm_num)
    | exact hcda.hasStrictFDerivAt (by exact_mod_cast le_top)
  have hdet : LinearMap.det (fderiv ℂ (A.zLoc w0 s i) c : V n →ₗ[ℂ] V n) ≠ 0 := hD.coord P hP
  let e : V n ≃L[ℂ] V n :=
    (LinearMap.equivOfDetNeZero (fderiv ℂ (A.zLoc w0 s i) c : V n →ₗ[ℂ] V n) hdet).toContinuousLinearEquiv
  have hstrict : HasStrictFDerivAt (A.zLoc w0 s i) (e : V n →L[ℂ] V n) c :=
    hstr.congr_fderiv (by ext v; rfl)
  have H2 : ∀ᶠ v in 𝓝 c, (A.chart i).symm v ∉ A.Mset w0 s De := by
    have hm := (A.chart i).symm_map_nhds_eq hPs
    rw [← hm] at H
    exact H
  have H3 : ∀ᶠ v in 𝓝 c, MvPolynomial.eval (fun k => (A.zLoc w0 s i v) k) De = 0 := by
    filter_upwards [H2, hUo.mem_nhds hcU] with v hv hvU
    have hvs : (A.chart i).symm v ∈ (A.chart i).source := (A.chart i).map_target hvU.1
    have hw0v : w0 i ((A.chart i).symm v) ≠ 0 := hvU.2
    have h1 := (fn_mem_Mset_iff A hD hvs).not.mp hv
    rw [not_not, fn_hom_of_ne De hw0v] at h1
    have h2 := (mul_eq_zero.mp h1).resolve_left (pow_ne_zero _ hw0v)
    simpa [WeightedAtlas.zLoc] using h2
  have H4 : ∀ᶠ z in 𝓝 (A.zLoc w0 s i c), MvPolynomial.eval (fun k => z k) De = 0 := by
    rw [← hstrict.map_nhds_eq_of_equiv]
    exact H3
  exact fn_eq_zero_of_eval De H4

/- English proof (translation)
Establish `key : interior (A.Mset w0 s De)ᶜ = ∅`. Establish `hWc : IsClosed (interior (A.Mset w0 s De)ᶜ)`. Rewrite using `[← closure_subset_iff_isClosed]`. Introduce `y hy`. Establish `hys : y ∈ (A.chart (A.pick y)).source` using `A.mem_pick y`.

Establish `hv : A.chart (A.pick y) y ∈ (A.chart (A.pick y)).target` using `(A.chart _).map_source hys`. Take `⟨r, hr, hB⟩` from `Metric.isOpen_iff.1 (A.chart (A.pick y)).open_target _ hv`. Establish `hNo : IsOpen ((A.chart (A.pick y)).source ∩ A.chart (A.pick y) ⁻¹' Metric.ball (A.chart (A.pick y) y) r)` using `(A.chart _).continuousOn.isOpen_inter_preimage (A.chart _).open_source Metric.isOpen_ball`. Establish `hyN : y ∈ (A.chart (A.pick y)).source ∩ A.chart (A.pick y) ⁻¹' Metric.ball (A.chart (A.pick y) y) r` using `⟨hys, Metric.mem_ball_self hr⟩`. Take `⟨y', hy'N, hy'W⟩` from `mem_closure_iff.1 hy _ hNo hyN`.

Establish `hv'B` using `hy'N.2`. Establish `hev : fnG A w0 s De (A.pick y) =ᶠ[𝓝 (A.chart (A.pick y) y')] 0`. Establish `ht` using `((A.chart (A.pick y)).continuousAt_symm (hB hv'B)).tendsto`. Rewrite `ht` using `[(A.chart _).left_inv hy'N.1]`. Establish `h1` using `ht.eventually (isOpen_interior.mem_nhds hy'W)`.

Use `filter_upwards [h1, (A.chart _).open_target.mem_nhds (hB hv'B)] with v hv1 hv2`. Use `(fn_G_ne_iff A hD (De := De) hv2).not.2 (interior_subset hv1)` as an intermediate fact. Simplify using `using this`. Establish `hz` using `C.ident n _ _ _ Metric.isOpen_ball (convex_ball _ _) ((fn_diffG A hD (De := De) (A.pick y)).mono hB) hv'B hev`. Use `mem_interior_iff_mem_nhds.2 (Filter.mem_of_superset (hNo.mem_nhds hyN) fun x hx => ?_)` and prove the remaining obligations.

Establish `h2` using `hz hx.2`. Use `(fn_G_ne_iff A hD (De := De) ((A.chart _).map_source hx.1)).not.1 (by simpa using h2)` as an intermediate fact. Rewrite `this` using `[(A.chart _).left_inv hx.1]`. Then use the resulting hypothesis. Assume the negation of the conclusion as `hne`. Take `⟨y, hy⟩` from `nonempty_iff_ne_empty.2 hne`.

Take `⟨P, hP, hPc⟩` from `hD.meets y`. Establish `hPW` using `(IsClopen.connectedComponent_subset ⟨hWc, isOpen_interior⟩ hy) hPc`. Conclude with `fn_not_ev A hD hF hP (mem_interior_iff_mem_nhds.1 hPW)`. Use `interior_eq_empty_iff_dense_compl.1 key` as an intermediate fact. Rewrite `this` using `[compl_compl]`. Then use the resulting hypothesis.
-/
theorem fn_dense (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De) : Dense (A.Mset w0 s De) := by
  have key : interior (A.Mset w0 s De)ᶜ = ∅ := by
    have hWc : IsClosed (interior (A.Mset w0 s De)ᶜ) := by
      rw [← closure_subset_iff_isClosed]
      intro y hy
      have hys : y ∈ (A.chart (A.pick y)).source := A.mem_pick y
      have hv : A.chart (A.pick y) y ∈ (A.chart (A.pick y)).target := (A.chart _).map_source hys
      obtain ⟨r, hr, hB⟩ := Metric.isOpen_iff.1 (A.chart (A.pick y)).open_target _ hv
      have hNo : IsOpen ((A.chart (A.pick y)).source ∩ A.chart (A.pick y) ⁻¹'
          Metric.ball (A.chart (A.pick y) y) r) :=
        (A.chart _).continuousOn.isOpen_inter_preimage (A.chart _).open_source Metric.isOpen_ball
      have hyN : y ∈ (A.chart (A.pick y)).source ∩ A.chart (A.pick y) ⁻¹'
          Metric.ball (A.chart (A.pick y) y) r := ⟨hys, Metric.mem_ball_self hr⟩
      obtain ⟨y', hy'N, hy'W⟩ := mem_closure_iff.1 hy _ hNo hyN
      have hv'B := hy'N.2
      have hev : fnG A w0 s De (A.pick y) =ᶠ[𝓝 (A.chart (A.pick y) y')] 0 := by
        have ht := ((A.chart (A.pick y)).continuousAt_symm (hB hv'B)).tendsto
        rw [(A.chart _).left_inv hy'N.1] at ht
        have h1 := ht.eventually (isOpen_interior.mem_nhds hy'W)
        filter_upwards [h1, (A.chart _).open_target.mem_nhds (hB hv'B)] with v hv1 hv2
        have := (fn_G_ne_iff A hD (De := De) hv2).not.2 (interior_subset hv1)
        simpa using this
      have hz := C.ident n _ _ _ Metric.isOpen_ball (convex_ball _ _)
        ((fn_diffG A hD (De := De) (A.pick y)).mono hB) hv'B hev
      refine mem_interior_iff_mem_nhds.2 (Filter.mem_of_superset (hNo.mem_nhds hyN) fun x hx => ?_)
      have h2 := hz hx.2
      have := (fn_G_ne_iff A hD (De := De) ((A.chart _).map_source hx.1)).not.1 (by simpa using h2)
      rwa [(A.chart _).left_inv hx.1] at this
    by_contra hne
    obtain ⟨y, hy⟩ := nonempty_iff_ne_empty.2 hne
    obtain ⟨P, hP, hPc⟩ := hD.meets y
    have hPW := (IsClopen.connectedComponent_subset ⟨hWc, isOpen_interior⟩ hy) hPc
    exact fn_not_ev A hD hF hP (mem_interior_iff_mem_nhds.1 hPW)
  have := interior_eq_empty_iff_dense_compl.1 key
  rwa [compl_compl] at this

end

end ReciprocityTheory.L2DbarEstimates.Y
