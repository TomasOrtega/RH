import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrdGeOfForall
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CongruentTupleUnimodularImageOrLarge
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedLatticeQuadraticSumGeDiagonal

noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Poinc

namespace GlobalTheory.Poinc.leadingTermLemmas

/- English proof (translation)
Establish `hex : ∃ n : ℕ, ∃ x, x ≠ 0 ∧ β x x = n` using `⟨(β x₀ x₀).toNat, x₀, hx₀, (Int.toNat_of_nonneg (hpos x₀ hx₀).le).symm⟩`. Take `⟨x, hx, hxn⟩` from `Nat.find_spec hex`. Use `⟨x, hx, fun x' hx' => ?_⟩` and prove the remaining obligations. Rewrite using `[hxn, ← Int.toNat_of_nonneg (hpos x' hx').le]`. Conclude with `Nat.find_min' hex ⟨x', hx', (Int.toNat_of_nonneg (hpos x' hx').le).symm⟩` after adjusting the coercions.
-/
theorem leastVal {X : Type} [AddCommGroup X] (β : LinearMap.BilinForm ℤ X) (hpos : ∀ x, x ≠ 0 → 0 < β x x) {x₀ : X}
    (hx₀ : x₀ ≠ 0) : ∃ x, x ≠ 0 ∧ ∀ x', x' ≠ 0 → β x x ≤ β x' x' := by
  classical
  have hex : ∃ n : ℕ, ∃ x, x ≠ 0 ∧ β x x = n :=
    ⟨(β x₀ x₀).toNat, x₀, hx₀, (Int.toNat_of_nonneg (hpos x₀ hx₀).le).symm⟩
  obtain ⟨x, hx, hxn⟩ := Nat.find_spec hex
  refine ⟨x, hx, fun x' hx' => ?_⟩
  rw [hxn, ← Int.toNat_of_nonneg (hpos x' hx').le]
  exact_mod_cast Nat.find_min' hex ⟨x', hx', (Int.toNat_of_nonneg (hpos x' hx').le).symm⟩

/- English proof (translation)
Introduce `x`. Establish `hx : x ∈ Submodule.span ℤ (Set.range a)` using `hspan ▸ Submodule.mem_top`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy => obtain ⟨i, rfl⟩ := hy`. Conclude with `h i`.

Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `add y z _ _ hy hz`. Take `⟨w, hw⟩` from `hy`. Take `⟨w', hw'⟩` from `hz`. Conclude with `⟨w + w', by rw [map_add, hw, hw', smul_add]; abel⟩`.

Consider the case `smul n y _ hy`. Take `⟨w, hw⟩` from `hy`. Conclude with `⟨n • w, by rw [map_zsmul, hw, smul_add, smul_comm]⟩`.
-/
theorem congMod_of_span {X ι : Type} [AddCommGroup X] (N : ℕ) (g : X →+ X) (a : ι → X)
    (hspan : Submodule.span ℤ (Set.range a) = ⊤) (h : ∀ i, CongMod N (g (a i)) (a i)) : ∀ x, CongMod N (g x) x := by
  intro x
  have hx : x ∈ Submodule.span ℤ (Set.range a) := hspan ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨i, rfl⟩ := hy; exact h i
  | zero => exact ⟨0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨w, hw⟩ := hy; obtain ⟨w', hw'⟩ := hz
    exact ⟨w + w', by rw [map_add, hw, hw', smul_add]; abel⟩
  | smul n y _ hy =>
    obtain ⟨w, hw⟩ := hy
    exact ⟨n • w, by rw [map_zsmul, hw, smul_add, smul_comm]⟩

/- English proof (translation)
Take `⟨hk1, ε, hε⟩` from `hk`. Use `⟨fun c x => ?_, ε, ?_⟩` and prove the remaining obligations. Take `⟨w, hw⟩` from `h1 c x`. Take `⟨w', hw'⟩` from `hk1 c (g x)`. Use `⟨k w + w', ?_⟩` and prove the remaining obligations.

Simplify using `only [LinearMap.comp_apply]`. Rewrite using `[hw, map_add, map_nsmul, hw', smul_add]`. Normalize the expressions using the abelian group laws. Rewrite using `[← LinearMap.comp_assoc, LinearMap.det_comp]`. Take `⟨u, hu⟩` from `hε`.

Take `⟨v, hv⟩` from `h2`. Establish `e1 : LinearMap.det (ε.toLinearMap ∘ₗ k) = N * u + 1` using `by linarith`. Establish `e2 : LinearMap.det g = N * v + 1` using `by linarith`. Rewrite using `[e1, e2]`. Conclude with `⟨u * (N * v + 1) + v, by ring⟩`.
-/
theorem unimod_comp (O : Type) [CommRing O] {X₀ X : Type} [AddCommGroup X₀] [Module O X₀] [AddCommGroup X] [Module O X]
    {N : ℕ} {k : X₀ →ₗ[ℤ] X} (hk : IsUnimodMod O N k) {g : X₀ →ₗ[ℤ] X₀}
    (h1 : ∀ (c : O) x, CongMod N (g (c • x)) (c • g x)) (h2 : (N : ℤ) ∣ LinearMap.det g - 1) :
    IsUnimodMod O N (k ∘ₗ g) := by
  obtain ⟨hk1, ε, hε⟩ := hk
  refine ⟨fun c x => ?_, ε, ?_⟩
  · obtain ⟨w, hw⟩ := h1 c x
    obtain ⟨w', hw'⟩ := hk1 c (g x)
    refine ⟨k w + w', ?_⟩
    simp only [LinearMap.comp_apply]
    rw [hw, map_add, map_nsmul, hw', smul_add]; abel
  · rw [← LinearMap.comp_assoc, LinearMap.det_comp]
    obtain ⟨u, hu⟩ := hε
    obtain ⟨v, hv⟩ := h2
    have e1 : LinearMap.det (ε.toLinearMap ∘ₗ k) = N * u + 1 := by linarith
    have e2 : LinearMap.det g = N * v + 1 := by linarith
    rw [e1, e2]
    exact ⟨u * (N * v + 1) + v, by ring⟩

/- English proof (translation)
Simplify using `only [lin, qW, LinearMap.sum_apply, Finset.mul_sum]`. Use `symm`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun _ _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun _ _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`.
-/
theorem lin_sum {s l : ℕ} (W : Matrix (Fin s) (Fin s) ℤ) {X ι : Type} [AddCommGroup X] [Fintype ι]
    (a : Fin l × Fin s → X) (δ : ι → LinearMap.BilinForm ℤ X) : lin W a (∑ i, δ i) = ∑ i, lin W a (δ i) := by
  simp only [lin, qW, LinearMap.sum_apply, Finset.mul_sum]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.sum_comm]

/- English proof (translation)
Simplify using `only [lin, qW, LinearMap.smul_apply, Finset.mul_sum, smul_eq_mul]`. Use `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lin_smul {s l : ℕ} (W : Matrix (Fin s) (Fin s) ℤ) {X : Type} [AddCommGroup X]
    (a : Fin l × Fin s → X) (M : ℤ) (δ : LinearMap.BilinForm ℤ X) : lin W a (M • δ) = M * lin W a δ := by
  simp only [lin, qW, LinearMap.smul_apply, Finset.mul_sum, smul_eq_mul]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

/- English proof (translation)
Simplify using `only [mono]`. Rewrite using `[Finset.prod_comm]`. Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_pow_eq_pow_sum]`. Use `congr 1`.

Establish `h0 : 0 ≤ lin W a (δ j)` using `Finset.sum_nonneg fun i _ => h j _`. Apply `Int.natCast_inj.1` to reduce the goal to its premises. Rewrite using `[Int.toNat_of_nonneg h0, lin, Nat.cast_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => Int.toNat_of_nonneg (h j _)`.
-/
theorem prod_mono {s l m : ℕ} (W : Matrix (Fin s) (Fin s) ℤ) {X V : Type} [AddCommGroup X] [CommRing V] (t : Fin m → V)
    (δ : Fin m → LinearMap.BilinForm ℤ X) (h : ∀ i y, 0 ≤ qW W (δ i) y) (a : Fin l × Fin s → X) :
    ∏ i, mono W t δ (fun v => a (i, v)) = ∏ j, t j ^ (lin W a (δ j)).toNat := by
  simp only [mono]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  have h0 : 0 ≤ lin W a (δ j) := Finset.sum_nonneg fun i _ => h j _
  apply Int.natCast_inj.1
  rw [Int.toNat_of_nonneg h0, lin, Nat.cast_sum]
  exact Finset.sum_congr rfl fun i _ => Int.toNat_of_nonneg (h j _)

/- English proof (translation)
Rewrite using `[← Finset.prod_pow_eq_pow_sum]`. Conclude with `Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (ht i) _`.
-/
theorem prod_pow_mem {V ι : Type} [CommRing V] (I : Ideal V) (t : ι → V) (ht : ∀ i, t i ∈ I) (n : ι → ℕ) (S : Finset ι) :
    ∏ i ∈ S, t i ^ n i ∈ I ^ (∑ i ∈ S, n i) := by
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (ht i) _

/- English proof (translation)
Establish `e : ∏ i, t i ^ n' i = (∏ i, t i ^ n i) * ∏ i, t i ^ (n' i - n i)`. Rewrite using `[← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_congr rfl fun i _ => by rw [← pow_add, Nat.add_sub_cancel' (h i)]`. Rewrite using `[e]`. Use `Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) ?_` and prove the remaining obligations.

Use `Ideal.mem_of_dvd _ ((dvd_pow_self (t j) (Nat.sub_ne_zero_of_lt hj)).trans (Finset.dvd_prod_of_mem (fun i => t i ^ (n' i - n i)) (Finset.mem_univ j))) ?_` and prove the remaining obligations. Conclude with `Ideal.subset_span ⟨j, rfl⟩`.
-/
theorem prod_pow_mem_mul {V ι : Type} [CommRing V] [Fintype ι] (t : ι → V) (n n' : ι → ℕ) (h : ∀ i, n i ≤ n' i)
    (j : ι) (hj : n j < n' j) :
    ∏ i, t i ^ n' i ∈ Ideal.span {∏ i, t i ^ n i} * Ideal.span (Set.range t) := by
  classical
  have e : ∏ i, t i ^ n' i = (∏ i, t i ^ n i) * ∏ i, t i ^ (n' i - n i) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by rw [← pow_add, Nat.add_sub_cancel' (h i)]
  rw [e]
  refine Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) ?_
  refine Ideal.mem_of_dvd _ ((dvd_pow_self (t j) (Nat.sub_ne_zero_of_lt hj)).trans
    (Finset.dvd_prod_of_mem (fun i => t i ^ (n' i - n i)) (Finset.mem_univ j))) ?_
  exact Ideal.subset_span ⟨j, rfl⟩

/- English proof (translation)
Use `haveI : IsDiscreteValuationRing V := { not_a_field' := fun h => ht0 (by rw [h] at ht; exact ht) }`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible V`. Take `⟨n, hn⟩` from `IsDiscreteValuationRing.associated_pow_irreducible (pow_ne_zero b ht0) hϖ`. Use `⟨n, ?_⟩` and prove the remaining obligations. Rewrite using `[hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_le_span_singleton]`.

Conclude with `hn.dvd`.
-/
theorem pow_le_span {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] [IsPrincipalIdealRing V] {t : V}
    (ht : t ∈ maximalIdeal V) (ht0 : t ≠ 0) (b : ℕ) : ∃ j, maximalIdeal V ^ j ≤ Ideal.span {t ^ b} := by
  haveI : IsDiscreteValuationRing V :=
    { not_a_field' := fun h => ht0 (by rw [h] at ht; exact ht) }
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible (pow_ne_zero b ht0) hϖ
  refine ⟨n, ?_⟩
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_le_span_singleton]
  exact hn.dvd

end GlobalTheory.Poinc.leadingTermLemmas

open GlobalTheory.Poinc.leadingTermLemmas in

/- English proof (translation)
Introduce `O _ _ bar hB q φ hφ s W hW N₁ A _ _ Φ y₀ γ M hM hδ d l a hD c e`. Take `⟨cW, hcW0, hcW⟩` from `GlobalTheory.Poinc.QWDom.qW_ge s W hW`. Take `⟨C, hC⟩` from `Φ.lam`. Establish `hq : ∀ y i μ, 0 ≤ qW W (Φ.δ y i) μ` using `fun y i μ => by`. Establish `h1` using `hcW (Φ.X y) (Φ.δ y i) (Φ.bal y i).1 (Φ.nonneg y i) μ`.

Establish `h2 : (0 : ℝ) ≤ ((∑ u, Φ.δ y i (μ u) (μ u) : ℤ) : ℝ)`. Conclude with `Finset.sum_nonneg fun u _ => Φ.nonneg y i _` after adjusting the coercions. Conclude with `(mul_nonneg hcW0.le h2).trans h1` after adjusting the coercions. Establish `hl : ∀ y i (μ : Fin l × Fin s → Φ.X y), 0 ≤ lin W μ (Φ.δ y i)` using `fun y i μ => Finset.sum_nonneg fun _ _ => hq y i _`. Take `⟨K, hK⟩ : ∃ K : ℝ, K = max ((C * e : ℕ) / cW) (e / cW)` from `⟨_, rfl⟩`.

Establish `hK1 : ((C * e : ℕ) : ℝ) ≤ cW * K`. Rewrite using `[← div_le_iff₀' hcW0, hK]`. Conclude with `le_max_left _ _`. Establish `hK2 : (e : ℝ) ≤ cW * K`. Rewrite using `[← div_le_iff₀' hcW0, hK]`.

Conclude with `le_max_right _ _`. Take `⟨N₀, hN₀⟩` from `GlobalTheory.Poinc.dichotomy O bar hB (Φ.X y₀) (Fin l × Fin s) a hD.span K`. Take `⟨N, hNN₀, hN₁N, k, hkid, hk, hfour⟩` from `Φ.four y₀ N₀`. Take `⟨f, hf⟩` from `hfour l a c e`. Establish `hterm : ∀ y (β : LinearMap.BilinForm ℤ (Φ.X y)), β ∈ balForms bar (Φ.X y) → (∀ x, 0 ≤ β x x) → ∀ (lam : ℝ), 0 ≤ lam → (∀ x, x ≠ 0 → lam ≤ β x x) → ∀ μ ∈ orbit O N₁ N (k y) a, (∃ g : Φ.X y₀ ≃ₗ[O] Φ.X y, ∀ iu, g (a iu) = μ iu) ∨ cW * K * lam ≤ (lin W μ β : ℤ)`.

Introduce `y β hβ hnn lam hlam0 hlam μ hμ`. Take `⟨g, g1, g2, -, g4⟩` from `hμ`. Break down `hN₀ N hNN₀ (Φ.X y) β hβ hnn lam hlam0 hlam (k y ∘ₗ g) μ (unimod_comp O (hk y) g1 g2) (fun i => g4 i) with h | hbig` into its components or cases. Conclude with `Or.inl h`. Use `right`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_assoc]`. Conclude with `mul_le_mul_of_nonneg_left hbig hcW0.le`. Use `_ = ∑ i, cW * ((∑ u, β (μ (i, u)) (μ (i, u)) : ℤ) : ℝ) := by push_cast; rw [Fintype.sum_prod_type, Finset.mul_sum]`. Use `_ ≤ ∑ i, ((qW W β fun u => μ (i, u) : ℤ) : ℝ) := Finset.sum_le_sum fun i _ => hcW (Φ.X y) β hβ.1 hnn _`.

Use `_ = _ := by rw [lin, Int.cast_sum]`. Establish `hT : ∀ y (μ : Fin l × Fin s → Φ.X y), ∏ i, Φ.u y (fun v => μ (i, v)) (c i) * mono W (Φ.t y) (Φ.δ y) (fun v => μ (i, v)) = Φ.coefT y μ c * ∏ j, Φ.t y j ^ (lin W μ (Φ.δ y j)).toNat` using `fun y μ => by`. Rewrite using `[Finset.prod_mul_distrib, prod_mono W _ _ (hq y)]`. Both sides reduce to the same expression. Use `⟨f, Φ.ordGe_of_forall fun y hP hm i b hb => ?_, ?_⟩` and prove the remaining obligations.

Establish `hsub : ∀ i' : Fin (Φ.m y), i' = i` using `fun i' => Fin.ext (by have := i'.2; have := i.2; omega)`. Distinguish the cases in `hXy : Subsingleton (Φ.X y)`. Establish `h0 : φ.evalZ (Φ.δ y i) = 0` using `φ.eval_of_subsingleton _`. Establish `hb0 : b = 0`. Conclude with `Nat.le_zero.1 (hb 0 (by rw [h0]; simp))`.

Use `Ideal.mem_sup_left ?_` and prove the remaining obligations. Simplify using `[hb0]`. Rewrite `hXy` using `[not_subsingleton_iff_nontrivial]`. Take `⟨x₁, hx₁⟩` from `exists_ne (0 : Φ.X y)`. Establish `hpos : ∀ x, x ≠ 0 → 0 < Φ.δ y i x x` using `fun x hx => by`.

Take `⟨i', hi'⟩` from `Φ.pos y x hx`. Rewrite `hi'` using `[hsub i']`. Then use the resulting hypothesis. Take `⟨x, hx, hxmin⟩` from `leastVal (Φ.δ y i) hpos hx₁`. Establish `hlam0 : (0 : ℝ) ≤ Φ.δ y i x x` using `by exact_mod_cast (hpos x hx).le`. Take `⟨h₂, hh₂, hC₂⟩` from `hC y hm i x hx`.

Take `⟨j, hj⟩` from `pow_le_span (Φ.t_mem y i).1 (Φ.t_mem y i).2 b`. Take `⟨S, hSo, -, hSa⟩` from `hf y j`. Rewrite `hSa` using `[Ideal.map_pow]`. Establish `hSa'` using `sup_le_sup_right hj _ hSa`. Rewrite using `[← sub_add_cancel (Φ.ev y f) _]`.

Use `Ideal.add_mem _ hSa' (Ideal.sum_mem _ fun μ hμ => ?_)` and prove the remaining obligations. Rewrite using `[hT, Fintype.prod_eq_single i (fun i' hi' => absurd (hsub i') hi')]`. Use `Ideal.mul_mem_left _ _ ?_` and prove the remaining obligations. Break down `hterm y _ (Φ.bal y i) (Φ.nonneg y i) _ hlam0 (fun x' hx' => by exact_mod_cast hxmin x' hx') μ (hSo hμ) with ⟨g, hg⟩ | hbig` into its components or cases. Use `Ideal.mem_sup_left (Ideal.mem_span_singleton.2 (pow_dvd_pow _ ?_))` and prove the remaining obligations.

Use `hD.le (pull g.toLinearMap (Φ.δ y i)) (pull_mem _ (Φ.bal y i)) (fun x => Φ.nonneg y i _)` as an intermediate fact. Rewrite `this` using `[evalZ_pull φ g.surjective]`. Establish `e1 : lin W a (pull g.toLinearMap (Φ.δ y i)) = lin W μ (Φ.δ y i)`. Simplify using `only [lin, qW, ← hg]`. Simplify using the standard rewrite rules.

Rewrite `this` using `[e1]`. Use `hb _ (this.trans (le_of_eq ?_))` and prove the remaining obligations. Conclude with `(Int.toNat_of_nonneg (hl y i μ)).symm` after adjusting the coercions. Use `Ideal.mem_sup_right (Ideal.mem_of_dvd _ ?_ (Ideal.pow_mem_pow (Ideal.mem_map_of_mem _ hh₂) e))` and prove the remaining obligations. Use `(pow_dvd_pow_of_dvd hC₂ e).trans ?_` and prove the remaining obligations.

Rewrite using `[← pow_mul]`. Use `pow_dvd_pow _ ?_` and prove the remaining obligations. Establish `h3 : ((C * e : ℕ) : ℝ) * (Φ.δ y i x x : ℝ) ≤ (lin W μ (Φ.δ y i) : ℤ)` using `(mul_le_mul_of_nonneg_right hK1 hlam0).trans hbig`. Establish `h4 : ((C * e : ℕ) : ℤ) * Φ.δ y i x x ≤ lin W μ (Φ.δ y i)` using `by exact_mod_cast h3`. Apply `Int.ofNat_le.1` to reduce the goal to its premises.

Rewrite using `[Int.toNat_of_nonneg (hl y i μ)]`. Move the coercions through the operations in `at h4 ⊢`. Rewrite using `[Int.toNat_of_nonneg (hpos x hx).le]`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨S, hSo, hSout, hSa⟩` from `hf y₀ (max e ((∑ i, lin W a (Φ.δ y₀ i)).toNat + 1))`.

Establish `haorb : a ∈ orbit O N₁ N (k y₀) a` using `⟨LinearMap.id, fun c x => ⟨0, by simp⟩, by simp, fun x => ⟨0, by simp⟩, fun i => ⟨0, by simp [hkid]⟩⟩`. Establish `haS : a ∈ S`. Assume the negation of the conclusion as `hn`. Use `hSout a haorb hn` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Establish `hrem : maximalIdeal (Φ.V y₀) ^ (max e ((∑ i, lin W a (Φ.δ y₀ i)).toNat + 1)) ⊔ (maximalIdeal A ^ e).map (Φ.ev y₀) ≤ maximalIdeal (Φ.V y₀) ^ e`. Use `sup_le (Ideal.pow_le_pow_right (le_max_left _ _)) ?_` and prove the remaining obligations. Rewrite using `[Ideal.map_pow]`. Use `haveI := Φ.ev_loc y₀`. Conclude with `Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 fun x hx => map_nonunit _ _ hx) e`.

Establish `hmT : Φ.monoT y₀ a = ∏ j, Φ.t y₀ j ^ (lin W a (Φ.δ y₀ j)).toNat` using `prod_mono W _ _ (hq y₀) a`. Establish `hSa'` using `hrem hSa`. Simplify using `only [hT] at hSa'`. Rewrite `hSa'` using `[← Finset.add_sum_erase S _ haS, ← hmT, ← sub_sub]`. Unfold `VSys.Leads`.

Rewrite using `[← sub_add_cancel (Φ.ev y₀ f - Φ.coefT y₀ a c * Φ.monoT y₀ a) _]`. Use `Ideal.add_mem _ (Ideal.mem_sup_right hSa') (Ideal.sum_mem _ fun μ hμ => Ideal.mul_mem_left _ _ ?_)` and prove the remaining obligations. Establish `hμa` using `Finset.ne_of_mem_erase hμ`. Establish `hμo` using `hSo (Finset.mem_of_mem_erase hμ)`. Establish `hnn : ∀ x, 0 ≤ (∑ i, Φ.δ y₀ i) x x` using `fun x => by`.

Simplify using `only [LinearMap.sum_apply]`. Conclude with `Finset.sum_nonneg fun i _ => Φ.nonneg y₀ i x`. Break down `hterm y₀ (∑ i, Φ.δ y₀ i) (sum_mem fun i _ => Φ.bal y₀ i) hnn 1 zero_le_one (fun x hx => by` into its components or cases. Take `⟨i, hi⟩` from `Φ.pos y₀ x hx`. Establish `h1 : Φ.δ y₀ i x x ≤ (∑ i, Φ.δ y₀ i) x x`.

Simplify using `only [LinearMap.sum_apply]`. Conclude with `Finset.single_le_sum (f := fun i => Φ.δ y₀ i x x) (fun i _ => Φ.nonneg y₀ i x) (Finset.mem_univ i)`. Conclude with `(show (1 : ℤ) ≤ _ by omega)) μ hμo with ⟨g, hg⟩ | hbig` after adjusting the coercions. Take `⟨γ', -, -, h3, h4⟩` from `hμo`. Establish `hcong : ∀ x, CongMod N₁ (g x) x`.

Use `congMod_of_span N₁ g.toLinearMap.toAddMonoidHom a hD.span fun i => ?_` and prove the remaining obligations. Take `⟨t, ht⟩` from `hN₁N`. Take `⟨w, hw⟩` from `h4 i`. Take `⟨w', hw'⟩` from `h3 (a i)`. Use `⟨w' + t • w, ?_⟩` and prove the remaining obligations.

Use `show g (a i) = _`. Rewrite using `[hg, hw, hkid, LinearMap.id_apply, hw', ht, mul_smul, smul_add]`. Normalize the expressions using the abelian group laws. Establish `hμe : (fun i => g (a i)) = μ` using `funext hg`. Establish `hne : ∃ x, g x ≠ x`.

Assume the negation of the conclusion as `hh`. Use `push_neg at hh`. Conclude with `hμa (funext fun i => by rw [← hg, hh])`. Take `⟨j, hj⟩` from `hD.strict g hcong hne`. Establish `hmin` using `hD.min g hcong`.

Rewrite `hj`, `hmin` using `[hμe]`. Establish `hM' : (0 : ℤ) < M` using `by exact_mod_cast hM`. Use `Ideal.mem_sup_left ?_` and prove the remaining obligations. Rewrite using `[hmT]`. Use `prod_pow_mem_mul _ _ _ (fun i => Int.toNat_le_toNat ?_) j ?_` and prove the remaining obligations.

Rewrite using `[hδ, lin_smul, lin_smul]`. Conclude with `mul_le_mul_of_nonneg_left (hmin i) hM'.le`. Establish `h5 : lin W a (Φ.δ y₀ j) < lin W μ (Φ.δ y₀ j)`. Rewrite using `[hδ, lin_smul, lin_smul]`. Conclude with `mul_lt_mul_of_pos_left hj hM'`.

Use `hl y₀ j a` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `Ideal.mem_sup_right (Ideal.pow_le_pow_right ?_ (prod_pow_mem _ _ (fun i => (Φ.t_mem y₀ i).1) _ Finset.univ))` and prove the remaining obligations. Rewrite `hbig` using `[mul_one, lin_sum]`. Establish `h4 : (e : ℤ) ≤ ∑ i, lin W μ (Φ.δ y₀ i)` using `by exact_mod_cast hK2.trans hbig`.

Apply `Int.ofNat_le.1` to reduce the goal to its premises. Rewrite using `[Nat.cast_sum]`. Conclude with `h4.trans (le_of_eq (Finset.sum_congr rfl fun i _ => (Int.toNat_of_nonneg (hl y₀ i μ)).symm))`.
-/
theorem GlobalTheory.Poinc.approx_of_vsys : ∀ (O : Type) [CommRing O] [Module.Finite ℤ O] (bar : O → O), BddAct bar → ∀ (q : ℕ) (φ : InvFun O), IsPolFan bar q φ → ∀ (s : ℕ) (W : Matrix (Fin s) (Fin s) ℤ), PosW W → ∀ (N₁ : ℕ) (A : Type) [CommRing A] [IsLocalRing A] (Φ : VSys bar q W N₁ A) (y₀ : Φ.Y) (γ : Fin (Φ.m y₀) → LinearMap.BilinForm ℤ (Φ.X y₀)) (M : ℕ), 1 ≤ M → (∀ i, Φ.δ y₀ i = (M : ℤ) • γ i) → ∀ (d l : ℕ) (a : Fin l × Fin s → Φ.X y₀), Dominant bar φ d N₁ W γ a → ∀ (c : Fin l → Φ.Q) (e : ℕ), ∃ f : A, Φ.OrdGe φ d e f ∧ Φ.Leads y₀ a c e f := by
  classical
  intro O _ _ bar hB q φ hφ s W hW N₁ A _ _ Φ y₀ γ M hM hδ d l a hD c e
  obtain ⟨cW, hcW0, hcW⟩ := GlobalTheory.Poinc.QWDom.qW_ge s W hW
  obtain ⟨C, hC⟩ := Φ.lam
  have hq : ∀ y i μ, 0 ≤ qW W (Φ.δ y i) μ := fun y i μ => by
    have h1 := hcW (Φ.X y) (Φ.δ y i) (Φ.bal y i).1 (Φ.nonneg y i) μ
    have h2 : (0 : ℝ) ≤ ((∑ u, Φ.δ y i (μ u) (μ u) : ℤ) : ℝ) := by
      exact_mod_cast Finset.sum_nonneg fun u _ => Φ.nonneg y i _
    exact_mod_cast (mul_nonneg hcW0.le h2).trans h1
  have hl : ∀ y i (μ : Fin l × Fin s → Φ.X y), 0 ≤ lin W μ (Φ.δ y i) := fun y i μ =>
    Finset.sum_nonneg fun _ _ => hq y i _
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = max ((C * e : ℕ) / cW) (e / cW) := ⟨_, rfl⟩
  have hK1 : ((C * e : ℕ) : ℝ) ≤ cW * K := by
    rw [← div_le_iff₀' hcW0, hK]; exact le_max_left _ _
  have hK2 : (e : ℝ) ≤ cW * K := by
    rw [← div_le_iff₀' hcW0, hK]; exact le_max_right _ _
  obtain ⟨N₀, hN₀⟩ := GlobalTheory.Poinc.dichotomy O bar hB (Φ.X y₀) (Fin l × Fin s) a hD.span K
  obtain ⟨N, hNN₀, hN₁N, k, hkid, hk, hfour⟩ := Φ.four y₀ N₀
  obtain ⟨f, hf⟩ := hfour l a c e
  have hterm : ∀ y (β : LinearMap.BilinForm ℤ (Φ.X y)), β ∈ balForms bar (Φ.X y) → (∀ x, 0 ≤ β x x) →
      ∀ (lam : ℝ), 0 ≤ lam → (∀ x, x ≠ 0 → lam ≤ β x x) → ∀ μ ∈ orbit O N₁ N (k y) a,
      (∃ g : Φ.X y₀ ≃ₗ[O] Φ.X y, ∀ iu, g (a iu) = μ iu) ∨ cW * K * lam ≤ (lin W μ β : ℤ) := by
    intro y β hβ hnn lam hlam0 hlam μ hμ
    obtain ⟨g, g1, g2, -, g4⟩ := hμ
    rcases hN₀ N hNN₀ (Φ.X y) β hβ hnn lam hlam0 hlam (k y ∘ₗ g) μ (unimod_comp O (hk y) g1 g2)
      (fun i => g4 i) with h | hbig
    · exact Or.inl h
    · right
      calc cW * K * lam ≤ cW * ((∑ iu, β (μ iu) (μ iu) : ℤ) : ℝ) := by
            rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hbig hcW0.le
        _ = ∑ i, cW * ((∑ u, β (μ (i, u)) (μ (i, u)) : ℤ) : ℝ) := by
            push_cast; rw [Fintype.sum_prod_type, Finset.mul_sum]
        _ ≤ ∑ i, ((qW W β fun u => μ (i, u) : ℤ) : ℝ) := Finset.sum_le_sum fun i _ => hcW (Φ.X y) β hβ.1 hnn _
        _ = _ := by rw [lin, Int.cast_sum]
  have hT : ∀ y (μ : Fin l × Fin s → Φ.X y),
      ∏ i, Φ.u y (fun v => μ (i, v)) (c i) * mono W (Φ.t y) (Φ.δ y) (fun v => μ (i, v)) =
        Φ.coefT y μ c * ∏ j, Φ.t y j ^ (lin W μ (Φ.δ y j)).toNat := fun y μ => by
    rw [Finset.prod_mul_distrib, prod_mono W _ _ (hq y)]; rfl
  refine ⟨f, Φ.ordGe_of_forall fun y hP hm i b hb => ?_, ?_⟩
  · have hsub : ∀ i' : Fin (Φ.m y), i' = i := fun i' => Fin.ext (by have := i'.2; have := i.2; omega)
    by_cases hXy : Subsingleton (Φ.X y)
    · have h0 : φ.evalZ (Φ.δ y i) = 0 := φ.eval_of_subsingleton _
      have hb0 : b = 0 := by
        exact Nat.le_zero.1 (hb 0 (by rw [h0]; simp))
      refine Ideal.mem_sup_left ?_
      simp [hb0]
    rw [not_subsingleton_iff_nontrivial] at hXy
    obtain ⟨x₁, hx₁⟩ := exists_ne (0 : Φ.X y)
    have hpos : ∀ x, x ≠ 0 → 0 < Φ.δ y i x x := fun x hx => by
      obtain ⟨i', hi'⟩ := Φ.pos y x hx
      rwa [hsub i'] at hi'
    obtain ⟨x, hx, hxmin⟩ := leastVal (Φ.δ y i) hpos hx₁
    have hlam0 : (0 : ℝ) ≤ Φ.δ y i x x := by exact_mod_cast (hpos x hx).le
    obtain ⟨h₂, hh₂, hC₂⟩ := hC y hm i x hx
    obtain ⟨j, hj⟩ := pow_le_span (Φ.t_mem y i).1 (Φ.t_mem y i).2 b
    obtain ⟨S, hSo, -, hSa⟩ := hf y j
    rw [Ideal.map_pow] at hSa
    have hSa' := sup_le_sup_right hj _ hSa
    rw [← sub_add_cancel (Φ.ev y f) _]
    refine Ideal.add_mem _ hSa' (Ideal.sum_mem _ fun μ hμ => ?_)
    rw [hT, Fintype.prod_eq_single i (fun i' hi' => absurd (hsub i') hi')]
    refine Ideal.mul_mem_left _ _ ?_
    rcases hterm y _ (Φ.bal y i) (Φ.nonneg y i) _ hlam0 (fun x' hx' => by exact_mod_cast hxmin x' hx') μ (hSo hμ) with
      ⟨g, hg⟩ | hbig
    · refine Ideal.mem_sup_left (Ideal.mem_span_singleton.2 (pow_dvd_pow _ ?_))
      have := hD.le (pull g.toLinearMap (Φ.δ y i)) (pull_mem _ (Φ.bal y i)) (fun x => Φ.nonneg y i _)
      rw [evalZ_pull φ g.surjective] at this
      have e1 : lin W a (pull g.toLinearMap (Φ.δ y i)) = lin W μ (Φ.δ y i) := by
        simp only [lin, qW, ← hg]; simp
      rw [e1] at this
      refine hb _ (this.trans (le_of_eq ?_))
      exact_mod_cast (Int.toNat_of_nonneg (hl y i μ)).symm
    · refine Ideal.mem_sup_right (Ideal.mem_of_dvd _ ?_ (Ideal.pow_mem_pow (Ideal.mem_map_of_mem _ hh₂) e))
      refine (pow_dvd_pow_of_dvd hC₂ e).trans ?_
      rw [← pow_mul]
      refine pow_dvd_pow _ ?_
      have h3 : ((C * e : ℕ) : ℝ) * (Φ.δ y i x x : ℝ) ≤ (lin W μ (Φ.δ y i) : ℤ) :=
        (mul_le_mul_of_nonneg_right hK1 hlam0).trans hbig
      have h4 : ((C * e : ℕ) : ℤ) * Φ.δ y i x x ≤ lin W μ (Φ.δ y i) := by exact_mod_cast h3
      apply Int.ofNat_le.1
      rw [Int.toNat_of_nonneg (hl y i μ)]
      push_cast at h4 ⊢
      rw [Int.toNat_of_nonneg (hpos x hx).le]
      linarith
  · obtain ⟨S, hSo, hSout, hSa⟩ := hf y₀ (max e ((∑ i, lin W a (Φ.δ y₀ i)).toNat + 1))
    have haorb : a ∈ orbit O N₁ N (k y₀) a :=
      ⟨LinearMap.id, fun c x => ⟨0, by simp⟩, by simp, fun x => ⟨0, by simp⟩, fun i => ⟨0, by simp [hkid]⟩⟩
    have haS : a ∈ S := by
      by_contra hn
      have := hSout a haorb hn
      omega
    have hrem : maximalIdeal (Φ.V y₀) ^ (max e ((∑ i, lin W a (Φ.δ y₀ i)).toNat + 1)) ⊔
        (maximalIdeal A ^ e).map (Φ.ev y₀) ≤ maximalIdeal (Φ.V y₀) ^ e := by
      refine sup_le (Ideal.pow_le_pow_right (le_max_left _ _)) ?_
      rw [Ideal.map_pow]
      haveI := Φ.ev_loc y₀
      exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 fun x hx => map_nonunit _ _ hx) e
    have hmT : Φ.monoT y₀ a = ∏ j, Φ.t y₀ j ^ (lin W a (Φ.δ y₀ j)).toNat := prod_mono W _ _ (hq y₀) a
    have hSa' := hrem hSa
    simp only [hT] at hSa'
    rw [← Finset.add_sum_erase S _ haS, ← hmT, ← sub_sub] at hSa'
    unfold VSys.Leads
    rw [← sub_add_cancel (Φ.ev y₀ f - Φ.coefT y₀ a c * Φ.monoT y₀ a) _]
    refine Ideal.add_mem _ (Ideal.mem_sup_right hSa') (Ideal.sum_mem _ fun μ hμ => Ideal.mul_mem_left _ _ ?_)
    have hμa := Finset.ne_of_mem_erase hμ
    have hμo := hSo (Finset.mem_of_mem_erase hμ)
    have hnn : ∀ x, 0 ≤ (∑ i, Φ.δ y₀ i) x x := fun x => by
      simp only [LinearMap.sum_apply]; exact Finset.sum_nonneg fun i _ => Φ.nonneg y₀ i x
    rcases hterm y₀ (∑ i, Φ.δ y₀ i) (sum_mem fun i _ => Φ.bal y₀ i) hnn 1 zero_le_one (fun x hx => by
        obtain ⟨i, hi⟩ := Φ.pos y₀ x hx
        have h1 : Φ.δ y₀ i x x ≤ (∑ i, Φ.δ y₀ i) x x := by
          simp only [LinearMap.sum_apply]
          exact Finset.single_le_sum (f := fun i => Φ.δ y₀ i x x) (fun i _ => Φ.nonneg y₀ i x) (Finset.mem_univ i)
        exact_mod_cast (show (1 : ℤ) ≤ _ by omega)) μ hμo with ⟨g, hg⟩ | hbig
    · obtain ⟨γ', -, -, h3, h4⟩ := hμo
      have hcong : ∀ x, CongMod N₁ (g x) x := by
        refine congMod_of_span N₁ g.toLinearMap.toAddMonoidHom a hD.span fun i => ?_
        obtain ⟨t, ht⟩ := hN₁N
        obtain ⟨w, hw⟩ := h4 i
        obtain ⟨w', hw'⟩ := h3 (a i)
        refine ⟨w' + t • w, ?_⟩
        show g (a i) = _
        rw [hg, hw, hkid, LinearMap.id_apply, hw', ht, mul_smul, smul_add]
        abel
      have hμe : (fun i => g (a i)) = μ := funext hg
      have hne : ∃ x, g x ≠ x := by
        by_contra hh
        push_neg at hh
        exact hμa (funext fun i => by rw [← hg, hh])
      obtain ⟨j, hj⟩ := hD.strict g hcong hne
      have hmin := hD.min g hcong
      rw [hμe] at hj hmin
      have hM' : (0 : ℤ) < M := by exact_mod_cast hM
      refine Ideal.mem_sup_left ?_
      rw [hmT]
      refine prod_pow_mem_mul _ _ _ (fun i => Int.toNat_le_toNat ?_) j ?_
      · rw [hδ, lin_smul, lin_smul]
        exact mul_le_mul_of_nonneg_left (hmin i) hM'.le
      · have h5 : lin W a (Φ.δ y₀ j) < lin W μ (Φ.δ y₀ j) := by
          rw [hδ, lin_smul, lin_smul]
          exact mul_lt_mul_of_pos_left hj hM'
        have := hl y₀ j a
        omega
    · refine Ideal.mem_sup_right (Ideal.pow_le_pow_right ?_
        (prod_pow_mem _ _ (fun i => (Φ.t_mem y₀ i).1) _ Finset.univ))
      rw [mul_one, lin_sum] at hbig
      have h4 : (e : ℤ) ≤ ∑ i, lin W μ (Φ.δ y₀ i) := by exact_mod_cast hK2.trans hbig
      apply Int.ofNat_le.1
      rw [Nat.cast_sum]
      exact h4.trans (le_of_eq (Finset.sum_congr rfl fun i _ => (Int.toNat_of_nonneg (hl y₀ i μ)).symm))
