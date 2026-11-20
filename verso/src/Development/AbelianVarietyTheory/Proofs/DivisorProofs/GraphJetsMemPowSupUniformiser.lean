import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToQMemMaximalIdealIff
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GraphLocal

/- English proof (translation)
Establish `key : ∀ x : κ ⊗[ℂ] κ', x - 1 ⊗ₜ Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ') x ∈ Ideal.span {x | ∃ f : κ, x = f ⊗ₜ[ℂ] (1 : κ') - 1 ⊗ₜ ρ f}`. Introduce `x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul f g`.

Establish `e : f ⊗ₜ[ℂ] g - 1 ⊗ₜ Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ') (f ⊗ₜ g) = (f ⊗ₜ[ℂ] (1 : κ') - 1 ⊗ₜ ρ f) * (1 ⊗ₜ g)`. Simplify using `[Algebra.TensorProduct.productMap_apply_tmul, sub_mul, Algebra.TensorProduct.tmul_mul_tmul]`. Rewrite using `[e]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨f, rfl⟩)`. Consider the case `add x y hx hy`.

Establish `e : x + y - 1 ⊗ₜ Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ') (x + y) = (x - 1 ⊗ₜ Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ') x) + (y - 1 ⊗ₜ Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ') y)`. Rewrite using `[map_add, TensorProduct.tmul_add]`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Conclude with `add_mem hx hy`.

Introduce `x hx`. Establish `h` using `key x`. Rewrite `h` using `[RingHom.mem_ker.1 hx, TensorProduct.tmul_zero, sub_zero]`. Then use the resulting hypothesis.
-/
theorem ker_productMap_le_span {κ κ' : Type} [Field κ] [Field κ'] [Algebra ℂ κ] [Algebra ℂ κ']
    (ρ : κ →ₐ[ℂ] κ') :
    RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ')) ≤
      Ideal.span {x | ∃ f : κ, x = f ⊗ₜ[ℂ] (1 : κ') - 1 ⊗ₜ ρ f} := by
  have key : ∀ x : κ ⊗[ℂ] κ',
      x - 1 ⊗ₜ Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ') x ∈
        Ideal.span {x | ∃ f : κ, x = f ⊗ₜ[ℂ] (1 : κ') - 1 ⊗ₜ ρ f} := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul f g =>
      have e : f ⊗ₜ[ℂ] g - 1 ⊗ₜ Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ') (f ⊗ₜ g) =
          (f ⊗ₜ[ℂ] (1 : κ') - 1 ⊗ₜ ρ f) * (1 ⊗ₜ g) := by
        simp [Algebra.TensorProduct.productMap_apply_tmul, sub_mul,
          Algebra.TensorProduct.tmul_mul_tmul]
      rw [e]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨f, rfl⟩)
    | add x y hx hy =>
      have e : x + y - 1 ⊗ₜ Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ') (x + y) =
          (x - 1 ⊗ₜ Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ') x) +
            (y - 1 ⊗ₜ Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ') y) := by
        rw [map_add, TensorProduct.tmul_add]
        abel
      rw [e]
      exact add_mem hx hy
  intro x hx
  have h := key x
  rwa [RingHom.mem_ker.1 hx, TensorProduct.tmul_zero, sub_zero] at h

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `K κ κ' _ _ _ _ _ _ R π ρ E 𝔭 _ t hle ht hπC hC hfrac hR hord M l a b w hw hx`. Set `T` to `tens (κ' := κ') (placeAlg E)`. Set `I : Ideal T` to `𝔭 ^ M ⊔ Ideal.span {⟨(t : K) ⊗ₜ 1, tmul_mem t.2 1⟩}`. Set `q : T →ₐ[ℂ] T ⧸ I` to `Ideal.Quotient.mkₐ ℂ I`. Establish `hq0 : ∀ y : T, q y = 0 ↔ y ∈ I` using `fun y => by`.

Rewrite using `[Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]`. Set `jL : placeAlg E →ₐ[ℂ] T` to `(tensEquiv (κ' := κ') (placeAlg E)).toAlgHom.comp Algebra.TensorProduct.includeLeft`. Set `jR : κ' →ₐ[ℂ] T` to `(tensEquiv (κ' := κ') (placeAlg E)).toAlgHom.comp Algebra.TensorProduct.includeRight`. Establish `hjL : ∀ e, (jL e : K ⊗[ℂ] κ') = (e : K) ⊗ₜ 1` using `fun e => by`. Simplify using `[jL, tensMap]`.

Establish `hjR : ∀ c, (jR c : K ⊗[ℂ] κ') = 1 ⊗ₜ c` using `fun c => by`. Simplify using `[jR, tensMap]`. Set `ι : R →+* placeAlg E` to `{ toFun := fun r => ⟨r, hR _ r.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl, map_add' := fun _ _ => rfl }`. Establish `hι : ∀ r : R, ((ι r : placeAlg E) : K) = r` using `fun _ => rfl`. Establish `hg : ∀ r : R, jL (ι r) - jR (ρ (π r)) ∈ 𝔭` using `fun r => by`.

Establish `e : ((jL (ι r) - jR (ρ (π r)) : T) : K ⊗[ℂ] κ') = (r : K) ⊗ₜ 1 - 1 ⊗ₜ ρ (π r)`. Rewrite using `[Subalgebra.coe_sub, hjL (ι r), hjR (ρ (π r))]`. Both sides reduce to the same expression. Conclude with `hle (Ideal.subset_span (Or.inr ⟨r, e⟩))`. Establish `hk : ∀ r : R, π r = 0 → q (jL (ι r)) = 0`.

Introduce `r hr`. Rewrite using `[hq0]`. Apply `Ideal.mem_sup_right` to reduce the goal to its premises. Distinguish the cases in `h0 : (r : K) = 0`. Establish `e : jL (ι r) = 0` using `Subtype.ext (by simp [hjL, hι, h0])`.

Rewrite using `[e]`. Conclude with `zero_mem _`. Establish `hpos` using `(hord r h0).1 hr`. Establish `hnu : ¬ IsUnit (⟨r, hR _ r.2⟩ : E.ring)` using `fun hu => by`. Establish `h1` using `E.ord_eq_zero hu`.

Simplify using `only at h1`. Use linear arithmetic over natural numbers and integers. Establish `hm : (⟨r, hR _ r.2⟩ : E.ring) ∈ Ideal.span {t}`. Rewrite using `[← (IsDiscreteValuationRing.irreducible_iff_uniformizer t).1 ht]`. Conclude with `hnu`.

Take `⟨u, hu⟩` from `Ideal.mem_span_singleton'.1 hm`. Rewrite using `[Ideal.mem_span_singleton']`. Use `⟨jL ⟨u, u.2⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Establish `hu' : (u : K) * t = r` using `congrArg Subtype.val hu`. Simplify using `only [Subalgebra.coe_mul, hjL, hι, Algebra.TensorProduct.tmul_mul_tmul, mul_one, hu']`.

Establish `hu : ∀ r : R, π r ≠ 0 → IsUnit (q (jL (ι r)))`. Introduce `r hr`. Establish `hρ : IsUnit (q (jR (ρ (π r))))` using `((isUnit_iff_ne_zero.2 ((map_ne_zero ρ).2 hr)).map jR).map q`. Establish `hn : IsNilpotent (q (jL (ι r) - jR (ρ (π r))))` using `⟨M, by rw [← map_pow, hq0]; exact Ideal.mem_sup_left (Ideal.pow_mem_pow (hg r) M)⟩`. Establish `h` using `IsNilpotent.isUnit_add_left_of_commute hn hρ (Commute.all _ _)`.

Rewrite `h` using `[map_sub, add_sub_cancel]`. Then use the resulting hypothesis. Set `φ : R →+* T ⧸ I` to `(q : T →+* T ⧸ I).comp ((jL : placeAlg E →+* T).comp ι)`. Establish `hφ : ∀ r, φ r = q (jL (ι r))` using `fun _ => rfl`. Establish `hker : RingHom.ker π.rangeRestrict ≤ RingHom.ker φ` using `fun r hr => by`. Rewrite `hr`, the goal using `[RingHom.mem_ker]`.

Conclude with `hk r (congrArg Subtype.val hr)`. Set `ψ : π.range →+* T ⧸ I` to `π.rangeRestrict.liftOfRightInverse (Function.surjInv π.rangeRestrict_surjective) (Function.rightInverse_surjInv _) ⟨φ, hker⟩`. Establish `hψ : ∀ r, ψ (π.rangeRestrict r) = q (jL (ι r))` using `fun r => RingHom.liftOfRightInverse_comp_apply _ _ _ _ r`. Use `haveI : IsFractionRing π.range κ := by`. Use `⟨fun y => ?_, fun z => ?_, fun {x y} h => ⟨1, by simpa using Subtype.ext h⟩⟩` and prove the remaining obligations.

Use `isUnit_iff_ne_zero.2 fun h => nonZeroDivisors.coe_ne_zero y (Subtype.ext h)` and prove the remaining obligations. Take `⟨c, d, hd, e⟩` from `hfrac z`. Conclude with `⟨(π.rangeRestrict c, ⟨π.rangeRestrict d, mem_nonZeroDivisors_of_ne_zero fun h => hd (congrArg Subtype.val h)⟩), e⟩`. Establish `hunit : ∀ y : nonZeroDivisors π.range, IsUnit (ψ y)`. Introduce and unpack `⟨⟨v, d, rfl⟩, hy⟩`.

Establish `hd : π d ≠ 0` using `fun h => nonZeroDivisors.coe_ne_zero ⟨_, hy⟩ (Subtype.ext h)`. Conclude with `(hψ d).symm ▸ hu d hd`. Set `θ₀ : κ →+* T ⧸ I` to `IsLocalization.lift (M := nonZeroDivisors π.range) hunit`. Establish `hθ₀ : ∀ r, θ₀ (π r) = q (jL (ι r))` using `fun r => (IsLocalization.lift_eq (M := nonZeroDivisors π.range) hunit (π.rangeRestrict r)).trans (hψ r)`. Set `θ₀A : κ →ₐ[ℂ] T ⧸ I` to `{ θ₀ with commutes' := fun c => by`.

Establish `e1 : algebraMap ℂ κ c = π ⟨algebraMap ℂ K c, hC c⟩` using `(hπC c (hC c)).symm`. Establish `e2 : ι ⟨algebraMap ℂ K c, hC c⟩ = algebraMap ℂ (placeAlg E) c` using `Subtype.ext rfl`. Express the relevant statement in the definitionally equal form `θ₀ (algebraMap ℂ κ c) = _`. Rewrite using `[e1, hθ₀, e2, AlgHom.commutes, AlgHom.commutes] }`. Set `θ : κ ⊗[ℂ] κ' →ₐ[ℂ] T ⧸ I` to `Algebra.TensorProduct.productMap θ₀A (q.comp jR)`.

Establish `hθt : ∀ f c, θ (f ⊗ₜ c) = θ₀ f * q (jR c)` using `fun f c => Algebra.TensorProduct.productMap_apply_tmul _ _ _ _`. Establish `hwx : θ (∑ i, π (a i) ⊗ₜ[ℂ] b i) = q w`. Establish `ew : w = ∑ i, jL (ι (a i)) * jR (b i)`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hw]`.

Simplify using `only [AddSubmonoidClass.coe_finset_sum, Subalgebra.coe_mul, hjL, hjR, hι, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]`. Rewrite using `[ew, map_sum, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hθt, hθ₀, map_mul]`. Establish `hgen : Ideal.map θ (RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ'))) ≤ Ideal.map q 𝔭`.

Use `(Ideal.map_mono (ker_productMap_le_span ρ)).trans ?_` and prove the remaining obligations. Rewrite using `[Ideal.map_span, Ideal.span_le]`. Introduce and unpack `_ ⟨_, ⟨f, rfl⟩, rfl⟩`. Take `⟨c, d, hd, e⟩` from `hfrac f`. Establish `hfd : θ₀ f * q (jL (ι d)) = q (jL (ι c))` using `by rw [← hθ₀, ← hθ₀, ← map_mul, e]`.

Use `set u := θ (f ⊗ₜ 1 - 1 ⊗ₜ ρ f) with hu_def`. Establish `hu1 : u = θ₀ f - q (jR (ρ f))`. Rewrite using `[hu_def, map_sub, hθt, hθt]`. Simplify using `only [map_one, mul_one, one_mul]`. Establish `h2 : u * q (jL (ι d)) = q (jL (ι c) - jR (ρ (π c))) - q (jR (ρ f)) * q (jL (ι d) - jR (ρ (π d)))`.

Rewrite using `[hu1, sub_mul, hfd, ← e, map_mul ρ, map_mul jR, map_sub q (jL (ι c)), map_sub q (jL (ι d)), map_mul q]`. Rewrite using `[mul_sub, sub_sub_sub_cancel_right]`. Establish `h3 : u * q (jL (ι d)) ∈ Ideal.map q 𝔭`. Rewrite using `[h2]`. Conclude with `sub_mem (Ideal.mem_map_of_mem q (hg c)) (Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem q (hg d)))`.

Take `⟨v, hv⟩` from `(hu d hd).exists_right_inv`. Establish `h4 : u = u * q (jL (ι d)) * v` using `by rw [mul_assoc, hv, mul_one]`. Rewrite using `[SetLike.mem_coe, h4]`. Conclude with `Ideal.mul_mem_right _ _ h3`. Establish `hbot : Ideal.map q 𝔭 ^ M = ⊥`.

Rewrite using `[← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker]`. Introduce `y hy`. Rewrite using `[RingHom.mem_ker]`. Conclude with `(hq0 y).2 (Ideal.mem_sup_left hy)`. Establish `h1` using `Ideal.mem_map_of_mem θ hx`.

Rewrite `h1` using `[Ideal.map_pow]`. Establish `h2` using `Ideal.pow_right_mono hgen M h1`. Rewrite `h2` using `[hbot, Ideal.mem_bot]`. Conclude with `(hq0 w).1 (hwx.symm.trans h2)`.
-/
theorem jets_mem_pow_sup : ∀ {K κ κ' : Type} [Field K] [Field κ] [Field κ'] [Algebra ℂ K] [Algebra ℂ κ] [Algebra ℂ κ']
    (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ') (E : Place (algebraMap ℂ K))
    (𝔭 : Ideal (tens (κ' := κ') (placeAlg E))) [𝔭.IsPrime] (t : E.ring),
  graphIdeal E R π ρ ≤ 𝔭 → Irreducible t →
  (∀ a (h : algebraMap ℂ K a ∈ R), π ⟨algebraMap ℂ K a, h⟩ = algebraMap ℂ κ a) →
  (∀ a, algebraMap ℂ K a ∈ R) → (∀ f : κ, ∃ a b : R, π b ≠ 0 ∧ f * π b = π a) →
  E.Contains R → (∀ r : R, (r : K) ≠ 0 → (π r = 0 ↔ 0 < E.ord r)) →
  ∀ (M l : ℕ) (a : Fin l → R) (b : Fin l → κ') (w : tens (κ' := κ') (placeAlg E)),
    (w : K ⊗[ℂ] κ') = ∑ i, (a i : K) ⊗ₜ b i →
    ∑ i, π (a i) ⊗ₜ[ℂ] b i ∈ (RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ'))) ^ M →
    w ∈ 𝔭 ^ M ⊔ Ideal.span {⟨(t : K) ⊗ₜ 1, tmul_mem t.2 1⟩} := by

  intro K κ κ' _ _ _ _ _ _ R π ρ E 𝔭 _ t hle ht hπC hC hfrac hR hord M l a b w hw hx
  let T := tens (κ' := κ') (placeAlg E)
  let I : Ideal T := 𝔭 ^ M ⊔ Ideal.span {⟨(t : K) ⊗ₜ 1, tmul_mem t.2 1⟩}
  let q : T →ₐ[ℂ] T ⧸ I := Ideal.Quotient.mkₐ ℂ I
  have hq0 : ∀ y : T, q y = 0 ↔ y ∈ I := fun y => by
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
  let jL : placeAlg E →ₐ[ℂ] T :=
    (tensEquiv (κ' := κ') (placeAlg E)).toAlgHom.comp Algebra.TensorProduct.includeLeft
  let jR : κ' →ₐ[ℂ] T :=
    (tensEquiv (κ' := κ') (placeAlg E)).toAlgHom.comp Algebra.TensorProduct.includeRight
  have hjL : ∀ e, (jL e : K ⊗[ℂ] κ') = (e : K) ⊗ₜ 1 := fun e => by
    simp [jL, tensMap]
  have hjR : ∀ c, (jR c : K ⊗[ℂ] κ') = 1 ⊗ₜ c := fun c => by
    simp [jR, tensMap]
  let ι : R →+* placeAlg E :=
    { toFun := fun r => ⟨r, hR _ r.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
      map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hι : ∀ r : R, ((ι r : placeAlg E) : K) = r := fun _ => rfl

  have hg : ∀ r : R, jL (ι r) - jR (ρ (π r)) ∈ 𝔭 := fun r => by
    have e : ((jL (ι r) - jR (ρ (π r)) : T) : K ⊗[ℂ] κ') = (r : K) ⊗ₜ 1 - 1 ⊗ₜ ρ (π r) := by
      rw [Subalgebra.coe_sub, hjL (ι r), hjR (ρ (π r))]
      rfl
    exact hle (Ideal.subset_span (Or.inr ⟨r, e⟩))

  have hk : ∀ r : R, π r = 0 → q (jL (ι r)) = 0 := by
    intro r hr
    rw [hq0]
    apply Ideal.mem_sup_right
    by_cases h0 : (r : K) = 0
    · have e : jL (ι r) = 0 := Subtype.ext (by simp [hjL, hι, h0])
      rw [e]
      exact zero_mem _
    have hpos := (hord r h0).1 hr
    have hnu : ¬ IsUnit (⟨r, hR _ r.2⟩ : E.ring) := fun hu => by
      have h1 := E.ord_eq_zero hu
      simp only at h1
      omega
    have hm : (⟨r, hR _ r.2⟩ : E.ring) ∈ Ideal.span {t} := by
      rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer t).1 ht]
      exact hnu
    obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.1 hm
    rw [Ideal.mem_span_singleton']
    refine ⟨jL ⟨u, u.2⟩, Subtype.ext ?_⟩
    have hu' : (u : K) * t = r := congrArg Subtype.val hu
    simp only [Subalgebra.coe_mul, hjL, hι, Algebra.TensorProduct.tmul_mul_tmul, mul_one, hu']

  have hu : ∀ r : R, π r ≠ 0 → IsUnit (q (jL (ι r))) := by
    intro r hr
    have hρ : IsUnit (q (jR (ρ (π r)))) :=
      ((isUnit_iff_ne_zero.2 ((map_ne_zero ρ).2 hr)).map jR).map q
    have hn : IsNilpotent (q (jL (ι r) - jR (ρ (π r)))) :=
      ⟨M, by rw [← map_pow, hq0]; exact Ideal.mem_sup_left (Ideal.pow_mem_pow (hg r) M)⟩
    have h := IsNilpotent.isUnit_add_left_of_commute hn hρ (Commute.all _ _)
    rwa [map_sub, add_sub_cancel] at h

  let φ : R →+* T ⧸ I := (q : T →+* T ⧸ I).comp ((jL : placeAlg E →+* T).comp ι)
  have hφ : ∀ r, φ r = q (jL (ι r)) := fun _ => rfl
  have hker : RingHom.ker π.rangeRestrict ≤ RingHom.ker φ := fun r hr => by
    rw [RingHom.mem_ker] at hr ⊢
    exact hk r (congrArg Subtype.val hr)
  let ψ : π.range →+* T ⧸ I :=
    π.rangeRestrict.liftOfRightInverse (Function.surjInv π.rangeRestrict_surjective)
      (Function.rightInverse_surjInv _) ⟨φ, hker⟩
  have hψ : ∀ r, ψ (π.rangeRestrict r) = q (jL (ι r)) := fun r =>
    RingHom.liftOfRightInverse_comp_apply _ _ _ _ r
  haveI : IsFractionRing π.range κ := by
    refine ⟨fun y => ?_, fun z => ?_, fun {x y} h => ⟨1, by simpa using Subtype.ext h⟩⟩
    · refine isUnit_iff_ne_zero.2 fun h => nonZeroDivisors.coe_ne_zero y (Subtype.ext h)
    · obtain ⟨c, d, hd, e⟩ := hfrac z
      exact ⟨(π.rangeRestrict c, ⟨π.rangeRestrict d, mem_nonZeroDivisors_of_ne_zero
        fun h => hd (congrArg Subtype.val h)⟩), e⟩
  have hunit : ∀ y : nonZeroDivisors π.range, IsUnit (ψ y) := by
    rintro ⟨⟨v, d, rfl⟩, hy⟩
    have hd : π d ≠ 0 := fun h => nonZeroDivisors.coe_ne_zero ⟨_, hy⟩ (Subtype.ext h)
    exact (hψ d).symm ▸ hu d hd
  let θ₀ : κ →+* T ⧸ I := IsLocalization.lift (M := nonZeroDivisors π.range) hunit
  have hθ₀ : ∀ r, θ₀ (π r) = q (jL (ι r)) := fun r =>
    (IsLocalization.lift_eq (M := nonZeroDivisors π.range) hunit (π.rangeRestrict r)).trans (hψ r)

  let θ₀A : κ →ₐ[ℂ] T ⧸ I :=
    { θ₀ with
      commutes' := fun c => by
        have e1 : algebraMap ℂ κ c = π ⟨algebraMap ℂ K c, hC c⟩ := (hπC c (hC c)).symm
        have e2 : ι ⟨algebraMap ℂ K c, hC c⟩ = algebraMap ℂ (placeAlg E) c := Subtype.ext rfl
        change θ₀ (algebraMap ℂ κ c) = _
        rw [e1, hθ₀, e2, AlgHom.commutes, AlgHom.commutes] }
  let θ : κ ⊗[ℂ] κ' →ₐ[ℂ] T ⧸ I := Algebra.TensorProduct.productMap θ₀A (q.comp jR)
  have hθt : ∀ f c, θ (f ⊗ₜ c) = θ₀ f * q (jR c) := fun f c =>
    Algebra.TensorProduct.productMap_apply_tmul _ _ _ _

  have hwx : θ (∑ i, π (a i) ⊗ₜ[ℂ] b i) = q w := by
    have ew : w = ∑ i, jL (ι (a i)) * jR (b i) := by
      apply Subtype.ext
      rw [hw]
      simp only [AddSubmonoidClass.coe_finset_sum, Subalgebra.coe_mul, hjL, hjR, hι,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [ew, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hθt, hθ₀, map_mul]

  have hgen : Ideal.map θ (RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ'))) ≤
      Ideal.map q 𝔭 := by
    refine (Ideal.map_mono (ker_productMap_le_span ρ)).trans ?_
    rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨f, rfl⟩, rfl⟩
    obtain ⟨c, d, hd, e⟩ := hfrac f
    have hfd : θ₀ f * q (jL (ι d)) = q (jL (ι c)) := by rw [← hθ₀, ← hθ₀, ← map_mul, e]
    set u := θ (f ⊗ₜ 1 - 1 ⊗ₜ ρ f) with hu_def
    have hu1 : u = θ₀ f - q (jR (ρ f)) := by
      rw [hu_def, map_sub, hθt, hθt]
      simp only [map_one, mul_one, one_mul]
    have h2 : u * q (jL (ι d)) =
        q (jL (ι c) - jR (ρ (π c))) - q (jR (ρ f)) * q (jL (ι d) - jR (ρ (π d))) := by
      rw [hu1, sub_mul, hfd, ← e, map_mul ρ, map_mul jR, map_sub q (jL (ι c)), map_sub q (jL (ι d)),
        map_mul q]
      rw [mul_sub, sub_sub_sub_cancel_right]
    have h3 : u * q (jL (ι d)) ∈ Ideal.map q 𝔭 := by
      rw [h2]
      exact sub_mem (Ideal.mem_map_of_mem q (hg c))
        (Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem q (hg d)))
    obtain ⟨v, hv⟩ := (hu d hd).exists_right_inv
    have h4 : u = u * q (jL (ι d)) * v := by rw [mul_assoc, hv, mul_one]
    rw [SetLike.mem_coe, h4]
    exact Ideal.mul_mem_right _ _ h3
  have hbot : Ideal.map q 𝔭 ^ M = ⊥ := by
    rw [← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker]
    intro y hy
    rw [RingHom.mem_ker]
    exact (hq0 y).2 (Ideal.mem_sup_left hy)
  have h1 := Ideal.mem_map_of_mem θ hx
  rw [Ideal.map_pow] at h1
  have h2 := Ideal.pow_right_mono hgen M h1
  rw [hbot, Ideal.mem_bot] at h2
  exact (hq0 w).1 (hwx.symm.trans h2)

end GlobalTheory.GraphLocal
