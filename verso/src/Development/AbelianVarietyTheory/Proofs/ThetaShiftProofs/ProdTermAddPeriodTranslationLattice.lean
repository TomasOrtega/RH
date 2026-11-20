import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.DegeneratingToriPeriodMapEqBaseOfYEqZero
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HasSumLocallyUniformlyOnTerm
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FormalThetaSumShiftPeriodDiv

noncomputable section

open Filter Topology

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)

/- English proof (translation)
The claim follows from `| 0, f, _ => ⟨Summable.of_finite, by simp⟩ | n + 1, f, hf => by obtain ⟨h1, h2⟩ := summable_norm_pi_prod_and_tsum n (fun i => f i.succ) fun i => hf i.succ let e : X × (Fin n → X) ≃ (Fin (n + 1) → X) := Fin.consEquiv fun _ => X have he : ∀ p : X × (Fin n → X), ∏ i, f i (e p i) = f …`.
-/
theorem summable_norm_pi_prod_and_tsum {R X : Type} [NormedField R] [CompleteSpace R] :
    ∀ (n : ℕ) (f : Fin n → X → R), (∀ i, Summable fun x => ‖f i x‖) →
      (Summable fun m : Fin n → X => ‖∏ i, f i (m i)‖) ∧ ∑' m : Fin n → X, ∏ i, f i (m i) = ∏ i, ∑' x, f i x
  | 0, f, _ => ⟨Summable.of_finite, by simp⟩
  | n + 1, f, hf => by
    obtain ⟨h1, h2⟩ := summable_norm_pi_prod_and_tsum n (fun i => f i.succ) fun i => hf i.succ
    let e : X × (Fin n → X) ≃ (Fin (n + 1) → X) := Fin.consEquiv fun _ => X
    have he : ∀ p : X × (Fin n → X), ∏ i, f i (e p i) = f 0 p.1 * ∏ i, f i.succ (p.2 i) := fun p => by
      rw [Fin.prod_univ_succ]; rfl
    refine ⟨e.summable_iff.1 ?_, ?_⟩
    · simpa only [Function.comp_def, he] using (hf 0).mul_norm h1
    · rw [← e.tsum_eq, Fin.prod_univ_succ, ← h2, tsum_mul_tsum_of_summable_norm (hf 0) h1]
      exact tsum_congr he

/- English proof (translation)
Assume the negation of the conclusion as `h`. Establish `h1 : Differentiable ℂ fun t : ℂ => f (p + t • (q - p))` using `hf.comp (by fun_prop)`. Establish `h2 : Differentiable ℂ fun t : ℂ => g (p + t • (q - p))` using `hg.comp (by fun_prop)`. Break down `AnalyticOnNhd.eq_zero_or_eq_zero_of_mul_eq_zero (U := Set.univ) (h1.differentiableOn.analyticOnNhd isOpen_univ) (h2.differentiableOn.analyticOnNhd isOpen_univ) (fun t _ => by` into its components or cases. Assume the negation of the conclusion as `h3`.

Conclude with `h ⟨_, mul_ne_zero_iff.1 h3⟩) isPreconnected_univ with h4 | h4`. Conclude with `hp (by simpa using h4 0 trivial)`. Conclude with `hq (by simpa using h4 1 trivial)`.
-/
theorem exists_ne_zero_and_ne_zero {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : E → ℂ}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) {p q : E} (hp : f p ≠ 0) (hq : g q ≠ 0) :
    ∃ x, f x ≠ 0 ∧ g x ≠ 0 := by
  by_contra h
  have h1 : Differentiable ℂ fun t : ℂ => f (p + t • (q - p)) := hf.comp (by fun_prop)
  have h2 : Differentiable ℂ fun t : ℂ => g (p + t • (q - p)) := hg.comp (by fun_prop)
  rcases AnalyticOnNhd.eq_zero_or_eq_zero_of_mul_eq_zero (U := Set.univ)
    (h1.differentiableOn.analyticOnNhd isOpen_univ) (h2.differentiableOn.analyticOnNhd isOpen_univ)
    (fun t _ => by
      by_contra h3
      exact h ⟨_, mul_ne_zero_iff.1 h3⟩) isPreconnected_univ with h4 | h4
  · exact hp (by simpa using h4 0 trivial)
  · exact hq (by simpa using h4 1 trivial)

namespace AnArc

variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)

/- English proof (translation)
Simplify using `only [eTwoPi, Finset.mul_sum, Complex.exp_sum]`.
-/
theorem e_sum {ι : Type} (s : Finset ι) (f : ι → ℂ) : eTwoPi (∑ i ∈ s, f i) = ∏ i ∈ s, eTwoPi (f i) := by
  simp only [eTwoPi, Finset.mul_sum, Complex.exp_sum]

variable {n : ℕ} (th : (Fin A.gB → ℂ) → ℂ) (w : ℂ) (a : Fin n → A.V)

def prodTerm (m : Fin n → A.X) (v : A.V) : ℂ :=
  ∏ i, A.term 1 0 th (m i) (v + a i) * eTwoPi (w * A.exponent 1 0 (m i))

def prodCoeff (α : A.X) (z : Fin A.gB → ℂ) : ℂ :=
  ∑' m : {m : Fin n → A.X // ∑ i, m i = α}, A.prodTerm th w a m (0, z)

/- English proof (translation)
Rewrite using `[map_sum, e_sum, prodTerm, prodTerm, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [term, Prod.fst_add, Prod.snd_add, AddMonoidHom.add_apply, zero_add, one_smul, e_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem prodTerm_eq_mul_char (m : Fin n → A.X) (v : A.V) :
    A.prodTerm th w a m v = A.prodTerm th w a m (0, v.2) * eTwoPi (v.1 (∑ i, m i)) := by
  rw [map_sum, e_sum, prodTerm, prodTerm, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [term, Prod.fst_add, Prod.snd_add, AddMonoidHom.add_apply, zero_add, one_smul, e_add]
  ring

variable {a} in

/- English proof (translation)
Establish `h1 : ∏ i, eTwoPi ((a i).1 y) = 1`. Rewrite using `[← e_sum, ← AddMonoidHom.finset_sum_apply, ← Prod.fst_sum, ha]`. Simplify using the standard rewrite rules. Establish `h2 : ∀ i, A.term 1 0 th (m i + y) (v + a i) * eTwoPi (w * A.exponent 1 0 (m i + y)) = eTwoPi ((a i).1 y) * ((A.psi y * eTwoPi (v.1 y) * eTwoPi (w * A.q y)) * (A.term 1 0 th (m i) (v + A.Pw w (La.mk y 0 0) + a i) * eTwoPi (w * A.exponent 1 0 (m i))))` using `fun i => by`. Rewrite using `[← term_add_Pw_y, add_right_comm v, Prod.fst_add, AddMonoidHom.add_apply, e_add]`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [prodTerm, h2]`. Rewrite using `[Finset.prod_mul_distrib, h1, one_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`.
-/
theorem prodTerm_add_Pw_y (ha : ∑ i, a i = 0) (m : Fin n → A.X) (y : A.X) (v : A.V) :
    A.prodTerm th w a (fun i => m i + y) v =
      (A.psi y * eTwoPi (v.1 y) * eTwoPi (w * A.q y)) ^ n * A.prodTerm th w a m (v + A.Pw w (La.mk y 0 0)) := by
  have h1 : ∏ i, eTwoPi ((a i).1 y) = 1 := by
    rw [← e_sum, ← AddMonoidHom.finset_sum_apply, ← Prod.fst_sum, ha]; simp
  have h2 : ∀ i, A.term 1 0 th (m i + y) (v + a i) * eTwoPi (w * A.exponent 1 0 (m i + y)) =
      eTwoPi ((a i).1 y) * ((A.psi y * eTwoPi (v.1 y) * eTwoPi (w * A.q y)) *
        (A.term 1 0 th (m i) (v + A.Pw w (La.mk y 0 0) + a i) * eTwoPi (w * A.exponent 1 0 (m i)))) := fun i => by
    rw [← term_add_Pw_y, add_right_comm v, Prod.fst_add, AddMonoidHom.add_apply, e_add]
    ring
  simp only [prodTerm, h2]
  rw [Finset.prod_mul_distrib, h1, one_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

variable {a th} in

/- English proof (translation)
Establish `h0 : ∀ s : Finset (Fin n), ∑ i ∈ s, A.H (a i).2 l = A.H (∑ i ∈ s, (a i).2) l` using `fun s => by`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, H_add_left, ih]`. Establish `h1 : ∏ i, Complex.exp (Real.pi * A.H (a i).2 l) = 1`.

Rewrite using `[← Complex.exp_sum, ← Finset.mul_sum, h0, ← Prod.snd_sum, ha]`. Simplify using the standard rewrite rules. Establish `h2 : ∀ i, A.term 1 0 th (m i) (v + A.P0 (La.mk 0 0 l) + a i) * eTwoPi (w * A.exponent 1 0 (m i)) = Complex.exp (Real.pi * A.H (a i).2 l) * (A.ah l v.2 * (A.term 1 0 th (m i) (v + a i) * eTwoPi (w * A.exponent 1 0 (m i))))` using `fun i => by`. Establish `h3` using `A.term_add_P0_l h (m i) l (v + a i)`. Express the relevant statement in the definitionally equal form `_ = A.ah l (v.2 + (a i).2) ^ 1 * _ at h3`.

Rewrite using `[add_right_comm v, h3, ah_add]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [prodTerm, h2]`. Rewrite using `[Finset.prod_mul_distrib, h1, one_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`.
-/
theorem prodTerm_add_periodTranslation_lattice (h : th ∈ A.Theta 1 0) (ha : ∑ i, a i = 0) (m : Fin n → A.X) (l : A.abelian₂) (v : A.V) :
    A.prodTerm th w a m (v + A.P0 (La.mk 0 0 l)) = A.ah l v.2 ^ n * A.prodTerm th w a m v := by
  have h0 : ∀ s : Finset (Fin n), ∑ i ∈ s, A.H (a i).2 l = A.H (∑ i ∈ s, (a i).2) l := fun s => by
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, H_add_left, ih]
  have h1 : ∏ i, Complex.exp (Real.pi * A.H (a i).2 l) = 1 := by
    rw [← Complex.exp_sum, ← Finset.mul_sum, h0, ← Prod.snd_sum, ha]; simp
  have h2 : ∀ i, A.term 1 0 th (m i) (v + A.P0 (La.mk 0 0 l) + a i) * eTwoPi (w * A.exponent 1 0 (m i)) =
      Complex.exp (Real.pi * A.H (a i).2 l) * (A.ah l v.2 *
        (A.term 1 0 th (m i) (v + a i) * eTwoPi (w * A.exponent 1 0 (m i)))) := fun i => by
    have h3 := A.term_add_P0_l h (m i) l (v + a i)
    change _ = A.ah l (v.2 + (a i).2) ^ 1 * _ at h3
    rw [add_right_comm v, h3, ah_add]
    ring
  simp only [prodTerm, h2]
  rw [Finset.prod_mul_distrib, h1, one_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

variable {a} in

/- English proof (translation)
Set `e : {m : Fin n → A.X // ∑ i, m i = α} ≃ {m : Fin n → A.X // ∑ i, m i = α + n • μ}` to `(Equiv.addRight fun _ : Fin n => μ).subtypeEquiv fun m => by`. Simplify using `[Finset.sum_add_distrib]`. Rewrite using `[← e.tsum_eq, term, prodCoeff, ← tsum_mul_left, ← tsum_mul_right]`. Use `tsum_congr fun m => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ = A.prodTerm th w a (fun i => m.1 i + μ) v`.

Rewrite using `[A.prodTerm_add_Pw_y th w ha, A.prodTerm_eq_mul_char th w a m (v + _), m.2]`. Establish `h1 : (v + A.Pw w (La.mk μ 0 0)).2 = v.2 + A.ct μ` using `by simp`. Establish `h2 : (v + A.Pw w (La.mk μ 0 0)).1 α = v.1 α + A.T μ α + w * A.be μ α`. Rewrite using `[Prod.fst_add, AddMonoidHom.add_apply, Pw_fst_apply]`. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree. Establish `h3 : v.1 (α + n • μ) = v.1 α + n * v.1 μ` using `by simp`. Establish `h4 : w * A.exponent n α μ = n * (w * A.q μ) + w * A.be μ α` using `by simp [exponent]; ring`. Rewrite using `[h1, h2, h3, h4]`. Simplify using `only [e_add, e_nat_mul, mul_pow]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem term_prodCoeff (ha : ∑ i, a i = 0) (α μ : A.X) (v : A.V) :
    A.term n α (A.prodCoeff th w a α) μ v * eTwoPi (w * A.exponent n α μ) =
      ∑' m : {m : Fin n → A.X // ∑ i, m i = α + n • μ}, A.prodTerm th w a m v := by
  let e : {m : Fin n → A.X // ∑ i, m i = α} ≃ {m : Fin n → A.X // ∑ i, m i = α + n • μ} :=
    (Equiv.addRight fun _ : Fin n => μ).subtypeEquiv fun m => by
      simp [Finset.sum_add_distrib]
  rw [← e.tsum_eq, term, prodCoeff, ← tsum_mul_left, ← tsum_mul_right]
  refine tsum_congr fun m => ?_
  change _ = A.prodTerm th w a (fun i => m.1 i + μ) v
  rw [A.prodTerm_add_Pw_y th w ha, A.prodTerm_eq_mul_char th w a m (v + _), m.2]
  have h1 : (v + A.Pw w (La.mk μ 0 0)).2 = v.2 + A.ct μ := by simp
  have h2 : (v + A.Pw w (La.mk μ 0 0)).1 α = v.1 α + A.T μ α + w * A.be μ α := by
    rw [Prod.fst_add, AddMonoidHom.add_apply, Pw_fst_apply]; simp; ring
  have h3 : v.1 (α + n • μ) = v.1 α + n * v.1 μ := by simp
  have h4 : w * A.exponent n α μ = n * (w * A.q μ) + w * A.be μ α := by simp [exponent]; ring
  rw [h1, h2, h3, h4]
  simp only [e_add, e_nat_mul, mul_pow]
  ring

variable {A th w} {T₀ : ℝ} (hT : A.IsConvLine T₀) (h : th ∈ A.Theta 1 0) (hw : T₀ < w.im)
include hT h hw

/- English proof (translation)
Take `⟨h1, h2⟩` from `summable_norm_pi_prod_and_tsum n (fun i μ => A.term 1 0 th μ (v + a i) * eTwoPi (w * A.exponent 1 0 μ)) fun i => summable_norm_term hT one_ne_zero h hw (v + a i)`. Conclude with `h2 ▸ h1.of_norm.hasSum`.
-/
theorem hasSum_prodTerm (v : A.V) :
    HasSum (fun m => A.prodTerm th w a m v) (∏ i, A.Sum 1 0 th w (v + a i)) := by
  obtain ⟨h1, h2⟩ := summable_norm_pi_prod_and_tsum n
    (fun i μ => A.term 1 0 th μ (v + a i) * eTwoPi (w * A.exponent 1 0 μ))
    fun i => summable_norm_term hT one_ne_zero h hw (v + a i)
  exact h2 ▸ h1.of_norm.hasSum

/- English proof (translation)
Use `choose t ht u hu hb using fun i => locally_normal_right hT one_ne_zero h hw (v + a i)`. Use `⟨⋂ i, (fun v' => v' + a i) ⁻¹' t i, iInter_mem.2 fun i => (continuous_add_right (a i)).continuousAt (ht i), fun m => ∏ i, u i (m i), (summable_norm_pi_prod_and_tsum n u fun i => (hu i).norm).1.of_norm, fun m v' hv' => ?_⟩` and prove the remaining obligations. Rewrite using `[prodTerm, norm_prod]`. Conclude with `Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => hb i _ _ (Set.mem_iInter.1 hv' i)`.
-/
theorem locally_normal_prodTerm (v : A.V) :
    ∃ t ∈ 𝓝 v, ∃ u : (Fin n → A.X) → ℝ, Summable u ∧ ∀ m, ∀ v' ∈ t, ‖A.prodTerm th w a m v'‖ ≤ u m := by
  choose t ht u hu hb using fun i => locally_normal_right hT one_ne_zero h hw (v + a i)
  refine ⟨⋂ i, (fun v' => v' + a i) ⁻¹' t i, iInter_mem.2 fun i =>
    (continuous_add_right (a i)).continuousAt (ht i), fun m => ∏ i, u i (m i),
    (summable_norm_pi_prod_and_tsum n u fun i => (hu i).norm).1.of_norm, fun m v' hv' => ?_⟩
  rw [prodTerm, norm_prod]
  exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => hb i _ _ (Set.mem_iInter.1 hv' i)

variable {a}

/- English proof (translation)
Use `⟨differentiableOn_univ.1 (SCV.differentiableOn_tsum_of_locally_normal (F := fun (m : {m : Fin n → A.X // ∑ i, m i = α}) z => A.prodTerm th w a m (0, z)) isOpen_univ (fun m => Differentiable.differentiableOn ?_) fun z _ => ?_), fun l z => ?_⟩` and prove the remaining obligations. Use `fun z => (HasFDerivAt.finsetProd (𝕜 := ℂ) (g := fun i z => A.term 1 0 th (m.1 i) (((0, z) : A.V) + a i) * eTwoPi (w * A.exponent 1 0 (m.1 i))) fun i _ => (Differentiable.mul_const ?_ _ z).hasFDerivAt).differentiableAt` and prove the remaining obligations. Conclude with `(A.differentiable_term 1 0 h.1 (m.1 i)).comp (f := fun z => ((0, z) : A.V) + a i) (by fun_prop)`. Take `⟨t, ht, u, hu, hb⟩` from `locally_normal_prodTerm a hT h hw (0, z)`. Conclude with `⟨_, (Continuous.prodMk_right 0).continuousAt ht, _, hu.subtype _, fun m z' hz' => hb m _ hz'⟩`.

Rewrite using `[prodCoeff, prodCoeff, ← tsum_mul_left]`. Use `tsum_congr fun m => ?_` and prove the remaining obligations. Establish `h1` using `A.prodTerm_add_periodTranslation_lattice w h ha m l (0, z)`. Establish `h2 : (((0, z) : A.V) + A.P0 (La.mk 0 0 l)).2 = z + l` using `by simp`. Establish `h3 : (((0, z) : A.V) + A.P0 (La.mk 0 0 l)).1 α = -(A.H (A.ct α) l / (2 * Complex.I))`.

Rewrite using `[Prod.fst_add, AddMonoidHom.add_apply, degeneratingTori_basePeriodMap_fst_apply]`. Simplify using the standard rewrite rules. Establish `h4 : Complex.exp (-(Real.pi * A.H (A.ct α) l)) * Complex.exp (Real.pi * A.H (A.ct α) l) = 1`. Rewrite using `[← Complex.exp_add]`. Simplify using the standard rewrite rules.

Rewrite `h1` using `[A.prodTerm_eq_mul_char, m.2, h2, h3, e_neg_div]`. Take the linear combination `Complex.exp (Real.pi * A.H (A.ct α) l) * h1 - A.prodTerm th w a m (0, z + l) * h4`.
-/
theorem prodCoeff_mem_Theta (ha : ∑ i, a i = 0) (α : A.X) : A.prodCoeff th w a α ∈ A.Theta n α := by
  refine ⟨differentiableOn_univ.1 (SCV.differentiableOn_tsum_of_locally_normal
    (F := fun (m : {m : Fin n → A.X // ∑ i, m i = α}) z => A.prodTerm th w a m (0, z)) isOpen_univ
    (fun m => Differentiable.differentiableOn ?_) fun z _ => ?_), fun l z => ?_⟩
  · refine fun z => (HasFDerivAt.finsetProd (𝕜 := ℂ) (g := fun i z => A.term 1 0 th (m.1 i) (((0, z) : A.V) + a i) *
      eTwoPi (w * A.exponent 1 0 (m.1 i))) fun i _ => (Differentiable.mul_const ?_ _ z).hasFDerivAt).differentiableAt
    exact (A.differentiable_term 1 0 h.1 (m.1 i)).comp (f := fun z => ((0, z) : A.V) + a i) (by fun_prop)
  · obtain ⟨t, ht, u, hu, hb⟩ := locally_normal_prodTerm a hT h hw (0, z)
    exact ⟨_, (Continuous.prodMk_right 0).continuousAt ht, _, hu.subtype _, fun m z' hz' => hb m _ hz'⟩
  · rw [prodCoeff, prodCoeff, ← tsum_mul_left]
    refine tsum_congr fun m => ?_
    have h1 := A.prodTerm_add_periodTranslation_lattice w h ha m l (0, z)
    have h2 : (((0, z) : A.V) + A.P0 (La.mk 0 0 l)).2 = z + l := by simp
    have h3 : (((0, z) : A.V) + A.P0 (La.mk 0 0 l)).1 α = -(A.H (A.ct α) l / (2 * Complex.I)) := by
      rw [Prod.fst_add, AddMonoidHom.add_apply, degeneratingTori_basePeriodMap_fst_apply]; simp
    have h4 : Complex.exp (-(Real.pi * A.H (A.ct α) l)) * Complex.exp (Real.pi * A.H (A.ct α) l) = 1 := by
      rw [← Complex.exp_add]; simp
    rw [A.prodTerm_eq_mul_char, m.2, h2, h3, e_neg_div] at h1
    linear_combination Complex.exp (Real.pi * A.H (A.ct α) l) * h1 - A.prodTerm th w a m (0, z + l) * h4

/- English proof (translation)
Establish `h1` using `((hasSum_prodTerm a hT h hw v).tsum_fiberwise fun m => ∑ i, m i).tsum_fiberwise (QuotientAddGroup.mk (s := (nsmulAddMonoidHom n : A.X →+ A.X).range))`. Use `(congrArg (HasSum · _) (funext fun c => ?_)).mpr h1` and prove the remaining obligations. Set `e : A.X ≃ (QuotientAddGroup.mk (s` to `(nsmulAddMonoidHom n : A.X →+ A.X).range)) ⁻¹' {c} := Equiv.ofBijective (fun μ => ⟨c.out + n • μ, by`. Rewrite using `[Set.mem_preimage, Set.mem_singleton_iff, QuotientAddGroup.mk_add_of_mem _ (show n • μ ∈ (nsmulAddMonoidHom n : A.X →+ A.X).range from ⟨μ, rfl⟩), QuotientAddGroup.out_eq']⟩) ⟨fun μ ν hμ => by`. Establish `h2 : n • μ = n • ν` using `add_left_cancel (congrArg Subtype.val hμ)`.

Establish `h3 : (n : ℤ) • μ = (n : ℤ) • ν` using `by simpa using h2`. Conclude with `smul_right_injective A.X (Int.natCast_ne_zero.2 hn) h3, fun χ => by`. Establish `h2 : (QuotientAddGroup.mk c.out : A.X ⧸ (nsmulAddMonoidHom n : A.X →+ A.X).range) = QuotientAddGroup.mk χ.1` using `(QuotientAddGroup.out_eq' c).trans χ.2.symm`. Take `⟨μ, hμ⟩` from `QuotientAddGroup.eq.1 h2`. Use `⟨μ, Subtype.ext ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `c.out + nsmulAddMonoidHom n μ = χ.1`. Rewrite using `[hμ]`. Use the proof step `abel⟩`. Rewrite using `[← e.tsum_eq]`. Conclude with `tsum_congr fun μ => A.term_prodCoeff th w ha c.out μ v`.
-/
theorem hasSum_Sum_prodCoeff (hn : n ≠ 0) (ha : ∑ i, a i = 0) (v : A.V) :
    HasSum (fun c : A.X ⧸ (nsmulAddMonoidHom n : A.X →+ A.X).range =>
      A.Sum n c.out (A.prodCoeff th w a c.out) w v) (∏ i, A.Sum 1 0 th w (v + a i)) := by
  have h1 := ((hasSum_prodTerm a hT h hw v).tsum_fiberwise fun m => ∑ i, m i).tsum_fiberwise
    (QuotientAddGroup.mk (s := (nsmulAddMonoidHom n : A.X →+ A.X).range))
  refine (congrArg (HasSum · _) (funext fun c => ?_)).mpr h1
  let e : A.X ≃ (QuotientAddGroup.mk (s := (nsmulAddMonoidHom n : A.X →+ A.X).range)) ⁻¹' {c} :=
    Equiv.ofBijective (fun μ => ⟨c.out + n • μ, by
      rw [Set.mem_preimage, Set.mem_singleton_iff, QuotientAddGroup.mk_add_of_mem _
        (show n • μ ∈ (nsmulAddMonoidHom n : A.X →+ A.X).range from ⟨μ, rfl⟩),
        QuotientAddGroup.out_eq']⟩) ⟨fun μ ν hμ => by
      have h2 : n • μ = n • ν := add_left_cancel (congrArg Subtype.val hμ)
      have h3 : (n : ℤ) • μ = (n : ℤ) • ν := by simpa using h2
      exact smul_right_injective A.X (Int.natCast_ne_zero.2 hn) h3, fun χ => by
      have h2 : (QuotientAddGroup.mk c.out : A.X ⧸ (nsmulAddMonoidHom n : A.X →+ A.X).range) =
        QuotientAddGroup.mk χ.1 := (QuotientAddGroup.out_eq' c).trans χ.2.symm
      obtain ⟨μ, hμ⟩ := QuotientAddGroup.eq.1 h2
      refine ⟨μ, Subtype.ext ?_⟩
      change c.out + nsmulAddMonoidHom n μ = χ.1
      rw [hμ]; abel⟩
  rw [← e.tsum_eq]
  exact tsum_congr fun μ => A.term_prodCoeff th w ha c.out μ v

/- English proof (translation)
Assume the negation of the conclusion as `h0`. Use `push_neg at h0`. Establish `h1` using `hasSum_Sum_prodCoeff hT h hw hn ha v`. Simplify using `only [h0 _ _ (prodCoeff_mem_Theta hT h hw ha _)] at h1`. Conclude with `hv (h1.unique hasSum_zero)`.
-/
theorem exists_Sum_ne_zero_of_prod_ne_zero (hn : n ≠ 0) (ha : ∑ i, a i = 0) {v : A.V}
    (hv : ∏ i, A.Sum 1 0 th w (v + a i) ≠ 0) : ∃ α, ∃ th' ∈ A.Theta n α, A.Sum n α th' w v ≠ 0 := by
  by_contra h0
  push_neg at h0
  have h1 := hasSum_Sum_prodCoeff hT h hw hn ha v
  simp only [h0 _ _ (prodCoeff_mem_Theta hT h hw ha _)] at h1
  exact hv (h1.unique hasSum_zero)

/- English proof (translation)
Take `⟨k, rfl⟩ : ∃ k, j = k + 1` from `⟨j - 1, by omega⟩`. Establish `hk : (k : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 (by omega)`. Take `⟨p, hp⟩` from `A.exists_Sum_ne_zero one_ne_zero 0 h0 fun z => summable_term hT one_ne_zero h hw (0, z)`. Establish `hS` using `differentiable_Sum hT one_ne_zero h hw`. Take `⟨x, hx1, hx2⟩` from `exists_ne_zero_and_ne_zero (f := fun x => A.Sum 1 0 th w (v + x)) (g := fun x => A.Sum 1 0 th w (v + -((k : ℂ) • x))) (hS.comp (by fun_prop)) (hS.comp (by fun_prop)) (p := p - v) (q := (k : ℂ)⁻¹ • (v - p)) (by simpa using hp) (by simpa [smul_smul, hk] using hp)`.

Use `⟨Fin.cons (-((k : ℂ) • x)) fun _ => x, ?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[Fin.sum_univ_succ]`. Simplify using `[Nat.cast_smul_eq_nsmul]`. Conclude with `Fin.cases hx2 (fun _ => hx1) i`.
-/
theorem exists_translates_ne_zero (h0 : th ≠ 0) {j : ℕ} (hj : 2 ≤ j) (v : A.V) :
    ∃ a : Fin j → A.V, ∑ i, a i = 0 ∧ ∀ i, A.Sum 1 0 th w (v + a i) ≠ 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have hk : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  obtain ⟨p, hp⟩ := A.exists_Sum_ne_zero one_ne_zero 0 h0 fun z => summable_term hT one_ne_zero h hw (0, z)
  have hS := differentiable_Sum hT one_ne_zero h hw
  obtain ⟨x, hx1, hx2⟩ := exists_ne_zero_and_ne_zero (f := fun x => A.Sum 1 0 th w (v + x))
    (g := fun x => A.Sum 1 0 th w (v + -((k : ℂ) • x))) (hS.comp (by fun_prop)) (hS.comp (by fun_prop))
    (p := p - v) (q := (k : ℂ)⁻¹ • (v - p)) (by simpa using hp) (by simpa [smul_smul, hk] using hp)
  refine ⟨Fin.cons (-((k : ℂ) • x)) fun _ => x, ?_, fun i => ?_⟩
  · rw [Fin.sum_univ_succ]; simp [Nat.cast_smul_eq_nsmul]
  · exact Fin.cases hx2 (fun _ => hx1) i

omit hT h hw in

/- English proof (translation)
Take `⟨a, ha, hv⟩` from `exists_translates_ne_zero hT h hw h0 hj v`. Conclude with `exists_Sum_ne_zero_of_prod_ne_zero hT h hw (by omega) ha (Finset.prod_ne_zero_iff.2 fun i _ => hv i)`.
-/
theorem exists_Sum_ne_zero_at (A : AnArc O) {T₀ : ℝ} (hT : A.IsConvLine T₀) {th₁ : (Fin A.gB → ℂ) → ℂ}
    (h : th₁ ∈ A.Theta 1 0) (h0 : th₁ ≠ 0) {w : ℂ} (hw : T₀ < w.im) {j : ℕ} (hj : 2 ≤ j) (v : A.V) :
    ∃ α, ∃ th ∈ A.Theta j α, A.Sum j α th w v ≠ 0 := by
  obtain ⟨a, ha, hv⟩ := exists_translates_ne_zero hT h hw h0 hj v
  exact exists_Sum_ne_zero_of_prod_ne_zero hT h hw (by omega) ha (Finset.prod_ne_zero_iff.2 fun i _ => hv i)

/- English proof (translation)
The claim follows from `exists_Sum_ne_zero_at _ ((tate_isConvLine_iff τ₀ _).2 le_rfl) (tate_one_mem_Theta τ₀ 1 _) one_ne_zero hw le_rfl v`.
-/
example (τ₀ w : ℂ) (hw : -τ₀.im / 2 < w.im) (v : (tate τ₀).V) :
    ∃ α, ∃ th ∈ (tate τ₀).Theta 2 α, (tate τ₀).Sum 2 α th w v ≠ 0 :=
  exists_Sum_ne_zero_at _ ((tate_isConvLine_iff τ₀ _).2 le_rfl) (tate_one_mem_Theta τ₀ 1 _) one_ne_zero hw le_rfl v

end AnArc

end GlobalTheory
