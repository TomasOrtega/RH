import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBirationalCoordinates
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace BirationalCoordinates

section Scale

variable {κ : Type} [Fintype κ] {Ω Ω'' : Type} [Field Ω] [Field Ω'']
  (j : Ω'' →+* Ω) {μ : Ω} (hμ : μ ≠ 0) {x : Ix κ → Ω} {y : Ix κ → Ω''} (hx : ∀ p, x p = μ * j (y p))
include hμ hx

omit [Fintype κ] in

/- English proof (translation)
Set `φ : MvPolynomial Unit Ω →ₐ[Ω] MvPolynomial Unit Ω` to `aeval fun k => C μ * X k`. Set `ψ : MvPolynomial Unit Ω →ₐ[Ω] MvPolynomial Unit Ω` to `aeval fun k => C μ⁻¹ * X k`. Establish `hψφ : ∀ q, ψ (φ q) = q`. Establish `h : ψ.comp φ = AlgHom.id Ω _`. Use `MvPolynomial.algHom_ext fun k => ?_` and prove the remaining obligations.

Simplify using `only [AlgHom.comp_apply, AlgHom.id_apply, φ, ψ, aeval_X, map_mul, algHom_C, algebraMap_eq]`. Rewrite using `[← mul_assoc, ← C_mul, mul_inv_cancel₀ hμ, C_1, one_mul]`. Introduce `q`. Conclude with `AlgHom.congr_fun h q`. Establish `hcomp : (mConeMap (ι` using `GlobalTheory κ) x).toRingHom = (φ.toRingHom.comp (MvPolynomial.map j)).comp (mConeMap (ι := GlobalTheory κ) y).toRingHom := by`.

Use `MvPolynomial.ringHom_ext (fun n => by simp) (fun p => ?_)` and prove the remaining obligations. Simplify using `only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, mConeMap, aeval_X, map_mul, map_C, map_X, φ, algHom_C, algebraMap_eq, hx p, ]`. Expand and normalize the polynomial expressions, which then agree. Use extensionality with `f`. Simplify using `only [mCoordIdeal, RingHom.mem_ker]`.

Establish `hf : mConeMap (ι` using `GlobalTheory κ) x f = φ (MvPolynomial.map j (mConeMap (ι := GlobalTheory κ) y f)) := congrArg (fun F : MRing (GlobalTheory κ) →+* MvPolynomial Unit Ω => F f) hcomp`. Rewrite using `[hf]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[h, map_zero, map_zero]`.

Introduce `h`. Establish `h1 : MvPolynomial.map j (mConeMap (ι` using `GlobalTheory κ) y f) = 0 := by`. Rewrite using `[← hψφ (MvPolynomial.map j _), h, map_zero]`. Conclude with `MvPolynomial.map_injective j j.injective (by rw [h1, map_zero])`.
-/
theorem mCoordIdeal_eq : mCoordIdeal (ι := GlobalTheory κ) y = mCoordIdeal (ι := GlobalTheory κ) x := by
  let φ : MvPolynomial Unit Ω →ₐ[Ω] MvPolynomial Unit Ω := aeval fun k => C μ * X k
  let ψ : MvPolynomial Unit Ω →ₐ[Ω] MvPolynomial Unit Ω := aeval fun k => C μ⁻¹ * X k
  have hψφ : ∀ q, ψ (φ q) = q := by
    have h : ψ.comp φ = AlgHom.id Ω _ := by
      refine MvPolynomial.algHom_ext fun k => ?_
      simp only [AlgHom.comp_apply, AlgHom.id_apply, φ, ψ, aeval_X, map_mul, algHom_C, algebraMap_eq]
      rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ hμ, C_1, one_mul]
    intro q
    exact AlgHom.congr_fun h q
  have hcomp : (mConeMap (ι := GlobalTheory κ) x).toRingHom =
      (φ.toRingHom.comp (MvPolynomial.map j)).comp (mConeMap (ι := GlobalTheory κ) y).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun n => by simp) (fun p => ?_)
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      mConeMap, aeval_X, map_mul, map_C, map_X, φ, algHom_C, algebraMap_eq, hx p, ]
    ring
  ext f
  simp only [mCoordIdeal, RingHom.mem_ker]
  have hf : mConeMap (ι := GlobalTheory κ) x f = φ (MvPolynomial.map j (mConeMap (ι := GlobalTheory κ) y f)) :=
    congrArg (fun F : MRing (GlobalTheory κ) →+* MvPolynomial Unit Ω => F f) hcomp
  rw [hf]
  constructor
  · intro h
    rw [h, map_zero, map_zero]
  · intro h
    have h1 : MvPolynomial.map j (mConeMap (ι := GlobalTheory κ) y f) = 0 := by
      rw [← hψφ (MvPolynomial.map j _), h, map_zero]
    exact MvPolynomial.map_injective j j.injective (by rw [h1, map_zero])

omit hμ in

/- English proof (translation)
Establish `hsum : ∀ m ∈ g.support, ∑ p ∈ m.support, m p = d ()`. Introduce `m hm`. Rewrite using `[Finset.sum_subset (Finset.subset_univ m.support) (fun p _ hp => by simpa using hp), Fintype.sum_sigma]`. Simplify using `using hg m hm ()`. Establish `hjx : j (aeval y g) = aeval (fun p => j (y p)) g`.

Rewrite using `[← RingHom.toIntAlgHom_apply, comp_aeval_apply]`. Both sides reduce to the same expression. Rewrite using `[hjx, show x = fun p => μ * j (y p) from funext hx]`. Use `conv_lhs => rw [g.as_sum]`. Use `conv_rhs => rw [g.as_sum]`.

Rewrite using `[map_sum, map_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations. Rewrite using `[aeval_monomial, aeval_monomial, Finsupp.prod, Finsupp.prod]`. Simplify using `only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hsum m hm]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem aeval_homog {g : MRing (GlobalTheory κ)} {d : Unit → ℕ} (hg : IsMultiHomog g d) :
    aeval x g = μ ^ d () * j (aeval y g) := by
  have hsum : ∀ m ∈ g.support, ∑ p ∈ m.support, m p = d () := by
    intro m hm
    rw [Finset.sum_subset (Finset.subset_univ m.support) (fun p _ hp => by simpa using hp),
      Fintype.sum_sigma]
    simpa using hg m hm ()
  have hjx : j (aeval y g) = aeval (fun p => j (y p)) g := by
    rw [← RingHom.toIntAlgHom_apply, comp_aeval_apply]
    rfl
  rw [hjx, show x = fun p => μ * j (y p) from funext hx]
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [aeval_monomial, aeval_monomial, Finsupp.prod, Finsupp.prod]
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hsum m hm]
  ring

omit [Fintype κ] in

/- English proof (translation)
Rewrite using `[chartRingZ, chartRingZ, AlgHom.map_adjoin, ← Set.range_comp]`. Use `congr 2`. Use function extensionality and compare the values at `p`. Simplify using `only [Function.comp_apply, RingHom.toIntAlgHom_apply, map_div₀, hx, mul_div_mul_left _ _ hμ]`.
-/
theorem chartRingZ_eq (c' : Unit → κ) :
    chartRingZ (ι := GlobalTheory κ) x c' = (chartRingZ (ι := GlobalTheory κ) y c').map j.toIntAlgHom := by
  rw [chartRingZ, chartRingZ, AlgHom.map_adjoin, ← Set.range_comp]
  congr 2
  funext p
  simp only [Function.comp_apply, RingHom.toIntAlgHom_apply, map_div₀, hx, mul_div_mul_left _ _ hμ]

omit [Fintype κ] in

/- English proof (translation)
Establish `hne : ∀ c' : Unit → κ, (∀ k, x ⟨k, c' k⟩ ≠ 0) ↔ (∀ k, y ⟨k, c' k⟩ ≠ 0)` using `fun c' => forall_congr' fun k => by rw [hx, mul_ne_zero_iff, map_ne_zero]; exact and_iff_right hμ`. Establish `hval : ∀ c' : Unit → κ, μ ^ ((τ : ℤ) * a ()) * j s' * ∏ k, x ⟨k, c' k⟩ ^ (-((τ : ℤ) * a k)) = j (s' * ∏ k, y ⟨k, c' k⟩ ^ (-((τ : ℤ) * a k)))`. Introduce `c'`. Simplify using `only [Fintype.prod_unique, hx, map_mul, map_zpow₀, mul_zpow]`. Establish `h1 : μ ^ ((τ : ℤ) * a ()) * μ ^ (-((τ : ℤ) * a default)) = 1`.

Rewrite using `[← zpow_add₀ hμ]`. Simplify using the standard rewrite rules. Take the linear combination `(j s' * j (y ⟨default, c' default⟩) ^ (-((τ : ℤ) * a default))) * h1`. Express the relevant statement in the definitionally equal form `(∀ c' : Unit → κ, _ → _) ↔ (∀ c' : Unit → κ, _ → _)`. Use `forall_congr' fun c' => ?_` and prove the remaining obligations.

Rewrite using `[hne c', hval c', chartRingZ_eq j hμ hx c', Subalgebra.mem_map]`. Use `imp_congr_right fun _ => ⟨fun ⟨t, ht, he⟩ => ?_, fun h => ⟨_, h, rfl⟩⟩` and prove the remaining obligations. Rewrite `he` using `[RingHom.toIntAlgHom_apply]`. Rewrite `ht` using `[j.injective he]`. Then use the resulting hypothesis.
-/
theorem mem_chartLat_iff (a : Unit → ℤ) (τ : ℕ) (s' : Ω'') :
    μ ^ ((τ : ℤ) * a ()) * j s' ∈ chartLat (ι := GlobalTheory κ) x a τ ↔ s' ∈ chartLat (ι := GlobalTheory κ) y a τ := by
  have hne : ∀ c' : Unit → κ, (∀ k, x ⟨k, c' k⟩ ≠ 0) ↔ (∀ k, y ⟨k, c' k⟩ ≠ 0) := fun c' =>
    forall_congr' fun k => by rw [hx, mul_ne_zero_iff, map_ne_zero]; exact and_iff_right hμ
  have hval : ∀ c' : Unit → κ, μ ^ ((τ : ℤ) * a ()) * j s' * ∏ k, x ⟨k, c' k⟩ ^ (-((τ : ℤ) * a k)) =
      j (s' * ∏ k, y ⟨k, c' k⟩ ^ (-((τ : ℤ) * a k))) := by
    intro c'
    simp only [Fintype.prod_unique, hx, map_mul, map_zpow₀, mul_zpow]
    have h1 : μ ^ ((τ : ℤ) * a ()) * μ ^ (-((τ : ℤ) * a default)) = 1 := by
      rw [← zpow_add₀ hμ]
      simp
    linear_combination (j s' * j (y ⟨default, c' default⟩) ^ (-((τ : ℤ) * a default))) * h1
  change (∀ c' : Unit → κ, _ → _) ↔ (∀ c' : Unit → κ, _ → _)
  refine forall_congr' fun c' => ?_
  rw [hne c', hval c', chartRingZ_eq j hμ hx c', Subalgebra.mem_map]
  refine imp_congr_right fun _ => ⟨fun ⟨t, ht, he⟩ => ?_, fun h => ⟨_, h, rfl⟩⟩
  rw [RingHom.toIntAlgHom_apply] at he
  rwa [j.injective he] at ht

omit [Fintype κ] in

/- English proof (translation)
Establish `h` using `hs (fun _ => c) (fun _ => hc)`. Simplify using `only [Fintype.prod_unique] at h`. Rewrite `h` using `[chartRingZ_eq j hμ hx, Subalgebra.mem_map]`. Take `⟨t, -, ht⟩` from `h`. Rewrite `ht` using `[RingHom.toIntAlgHom_apply]`.

Establish `hyc : y ⟨(), c⟩ ≠ 0` using `fun h0 => hc (by rw [hx, h0, map_zero, mul_zero])`. Use `⟨t * y ⟨(), c⟩ ^ ((τ : ℤ) * a ()), ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, ht, map_zpow₀]`. Express the relevant statement in the definitionally equal form `μ ^ ((τ : ℤ) * a ()) * (s * x ⟨(), c⟩ ^ (-((τ : ℤ) * a ())) * j (y ⟨(), c⟩) ^ ((τ : ℤ) * a ())) = s`. Rewrite using `[hx, mul_zpow, zpow_neg]`.

Establish `h1 : μ ^ ((τ : ℤ) * a ()) ≠ 0` using `zpow_ne_zero _ hμ`. Establish `h2 : j (y ⟨(), c⟩) ^ ((τ : ℤ) * a ()) ≠ 0` using `zpow_ne_zero _ (map_ne_zero j |>.2 hyc)`. Clear the denominators using the available nonvanishing facts. Rewrite using `[zpow_neg, inv_mul_cancel_right₀ h2]`.
-/
theorem exists_of_mem_chartLat {c : κ} (hc : x ⟨(), c⟩ ≠ 0) (a : Unit → ℤ) (τ : ℕ) {s : Ω}
    (hs : s ∈ chartLat (ι := GlobalTheory κ) x a τ) : ∃ s' : Ω'', μ ^ ((τ : ℤ) * a ()) * j s' = s := by
  have h := hs (fun _ => c) (fun _ => hc)
  simp only [Fintype.prod_unique] at h
  rw [chartRingZ_eq j hμ hx, Subalgebra.mem_map] at h
  obtain ⟨t, -, ht⟩ := h
  rw [RingHom.toIntAlgHom_apply] at ht
  have hyc : y ⟨(), c⟩ ≠ 0 := fun h0 => hc (by rw [hx, h0, map_zero, mul_zero])
  refine ⟨t * y ⟨(), c⟩ ^ ((τ : ℤ) * a ()), ?_⟩
  rw [map_mul, ht, map_zpow₀]
  change μ ^ ((τ : ℤ) * a ()) * (s * x ⟨(), c⟩ ^ (-((τ : ℤ) * a ())) * j (y ⟨(), c⟩) ^ ((τ : ℤ) * a ())) = s
  rw [hx, mul_zpow, zpow_neg]
  have h1 : μ ^ ((τ : ℤ) * a ()) ≠ 0 := zpow_ne_zero _ hμ
  have h2 : j (y ⟨(), c⟩) ^ ((τ : ℤ) * a ()) ≠ 0 := zpow_ne_zero _ (map_ne_zero j |>.2 hyc)
  field_simp
  rw [zpow_neg, inv_mul_cancel_right₀ h2]

/- English proof (translation)
Rewrite using `[aeval_homog j hx hg, aeval_homog j hx hh, ← zpow_natCast, ← zpow_natCast, hd (), add_comm, zpow_add₀ hμ, mul_assoc, mul_assoc]`. Establish `hm : μ ^ ((τ : ℤ) * A.a ()) * μ ^ ((dh () : ℕ) : ℤ) ≠ 0` using `mul_ne_zero (zpow_ne_zero _ hμ) (zpow_ne_zero _ hμ)`. Rewrite using `[show μ ^ ((τ : ℤ) * A.a ()) * (j s' * (μ ^ ((dh () : ℕ) : ℤ) * j (aeval y h))) = μ ^ ((τ : ℤ) * A.a ()) * μ ^ ((dh () : ℕ) : ℤ) * j (s' * aeval y h) by rw [map_mul]; ring, ← mul_assoc, mul_right_inj' hm]`. Conclude with `j.injective.eq_iff`.
-/
theorem rep_iff (A : HermLine (GlobalTheory κ)) (τ : ℕ) (s' : Ω'') {dg dh : Unit → ℕ} {g h : MRing (GlobalTheory κ)}
    (hg : IsMultiHomog g dg) (hh : IsMultiHomog h dh) (hd : ∀ k, (dg k : ℤ) = dh k + τ * A.a k) :
    aeval x g = μ ^ ((τ : ℤ) * A.a ()) * j s' * aeval x h ↔ aeval y g = s' * aeval y h := by
  rw [aeval_homog j hx hg, aeval_homog j hx hh, ← zpow_natCast, ← zpow_natCast, hd (), add_comm,
    zpow_add₀ hμ, mul_assoc, mul_assoc]
  have hm : μ ^ ((τ : ℤ) * A.a ()) * μ ^ ((dh () : ℕ) : ℤ) ≠ 0 := mul_ne_zero (zpow_ne_zero _ hμ) (zpow_ne_zero _ hμ)
  rw [show μ ^ ((τ : ℤ) * A.a ()) * (j s' * (μ ^ ((dh () : ℕ) : ℤ) * j (aeval y h))) =
      μ ^ ((τ : ℤ) * A.a ()) * μ ^ ((dh () : ℕ) : ℤ) * j (s' * aeval y h) by rw [map_mul]; ring,
    ← mul_assoc, mul_right_inj' hm]
  exact j.injective.eq_iff

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `H dg dh g h z hg hh hd he hz`. Conclude with `H dg dh g h z hg hh hd ((rep_iff j hμ hx A τ s' hg hh hd).2 he) hz`. Introduce `H dg dh g h z hg hh hd he hz`. Conclude with `H dg dh g h z hg hh hd ((rep_iff j hμ hx A τ s' hg hh hd).1 he) hz`.
-/
theorem isSmallH_iff (P : Ideal (MRing (GlobalTheory κ))) (A : HermLine (GlobalTheory κ)) (τ : ℕ) (s' : Ω'') :
    IsSmallH P x A τ (μ ^ ((τ : ℤ) * A.a ()) * j s') ↔ IsSmallH P y A τ s' := by
  constructor
  · intro H dg dh g h z hg hh hd he hz
    exact H dg dh g h z hg hh hd ((rep_iff j hμ hx A τ s' hg hh hd).2 he) hz
  · intro H dg dh g h z hg hh hd he hz
    exact H dg dh g h z hg hh hd ((rep_iff j hμ hx A τ s' hg hh hd).1 he) hz

/- English proof (translation)
Rewrite using `[mCoordIdeal_eq j hμ hx]`. Use `set P := mCoordIdeal (ι := GlobalTheory κ) x`. Unfold `smallSectionCount`. Use `congr 2`. Set `F : {s : chartLat (ι` to `GlobalTheory κ) y A.a τ // IsSmallH P y A τ (s : Ω'')} → {s : chartLat (ι := GlobalTheory κ) x A.a τ // IsSmallH P x A τ (s : Ω)} := fun s => ⟨⟨μ ^ ((τ : ℤ) * A.a ()) * j s.1.1, (mem_chartLat_iff j hμ hx A.a τ _).2 s.1.2⟩, (isSmallH_iff j hμ hx P A τ _).2 s.2⟩`.

Use `Nat.card_congr (Equiv.ofBijective F ⟨fun s t hst => ?_, fun s => ?_⟩)` and prove the remaining obligations. Establish `h1 : μ ^ ((τ : ℤ) * A.a ()) * j s.1.1 = μ ^ ((τ : ℤ) * A.a ()) * j t.1.1` using `congrArg (fun u : {s : chartLat (ι := GlobalTheory κ) x A.a τ // IsSmallH P x A τ (s : Ω)} => (u.1 : Ω)) hst`. Conclude with `Subtype.ext (Subtype.ext (j.injective (mul_left_cancel₀ (zpow_ne_zero _ hμ) h1)))`. Take `⟨s', hs'⟩` from `exists_of_mem_chartLat j hμ hx hc A.a τ s.1.2`. Establish `hm : s' ∈ chartLat (ι` using `GlobalTheory κ) y A.a τ := (mem_chartLat_iff j hμ hx A.a τ s').1 (hs' ▸ s.1.2)`.

Establish `hsm : IsSmallH P y A τ s'` using `(isSmallH_iff j hμ hx P A τ s').1 (hs' ▸ s.2)`. Conclude with `⟨⟨⟨s', hm⟩, hsm⟩, Subtype.ext (Subtype.ext hs')⟩`.
-/
theorem smallSectionCount_eq_of_birational {c : κ} (hc : x ⟨(), c⟩ ≠ 0) (A : HermLine (GlobalTheory κ)) (τ : ℕ) :
    smallSectionCount (IsSmallH (mCoordIdeal (ι := GlobalTheory κ) y) y A) (chartLat (ι := GlobalTheory κ) y A.a) τ =
      smallSectionCount (IsSmallH (mCoordIdeal (ι := GlobalTheory κ) x) x A) (chartLat (ι := GlobalTheory κ) x A.a) τ := by
  rw [mCoordIdeal_eq j hμ hx]
  set P := mCoordIdeal (ι := GlobalTheory κ) x
  unfold smallSectionCount
  congr 2
  let F : {s : chartLat (ι := GlobalTheory κ) y A.a τ // IsSmallH P y A τ (s : Ω'')} →
      {s : chartLat (ι := GlobalTheory κ) x A.a τ // IsSmallH P x A τ (s : Ω)} := fun s =>
    ⟨⟨μ ^ ((τ : ℤ) * A.a ()) * j s.1.1, (mem_chartLat_iff j hμ hx A.a τ _).2 s.1.2⟩,
      (isSmallH_iff j hμ hx P A τ _).2 s.2⟩
  refine Nat.card_congr (Equiv.ofBijective F ⟨fun s t hst => ?_, fun s => ?_⟩)
  · have h1 : μ ^ ((τ : ℤ) * A.a ()) * j s.1.1 = μ ^ ((τ : ℤ) * A.a ()) * j t.1.1 :=
      congrArg (fun u : {s : chartLat (ι := GlobalTheory κ) x A.a τ // IsSmallH P x A τ (s : Ω)} => (u.1 : Ω)) hst
    exact Subtype.ext (Subtype.ext (j.injective (mul_left_cancel₀ (zpow_ne_zero _ hμ) h1)))
  · obtain ⟨s', hs'⟩ := exists_of_mem_chartLat j hμ hx hc A.a τ s.1.2
    have hm : s' ∈ chartLat (ι := GlobalTheory κ) y A.a τ := (mem_chartLat_iff j hμ hx A.a τ s').1 (hs' ▸ s.1.2)
    have hsm : IsSmallH P y A τ s' := (isSmallH_iff j hμ hx P A τ s').1 (hs' ▸ s.2)
    exact ⟨⟨⟨s', hm⟩, hsm⟩, Subtype.ext (Subtype.ext hs')⟩

end Scale

end BirationalCoordinates

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
