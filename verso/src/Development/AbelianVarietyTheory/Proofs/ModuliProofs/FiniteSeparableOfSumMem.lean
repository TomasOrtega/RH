import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory.TameResidue

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Establish `hf : Function.Injective (fun σ : K ≃ₐ[k] K => (σ : K →* K))` using `fun σ τ hστ => AlgEquiv.ext fun x => DFunLike.congr_fun hστ x`. Establish `hli` using `(linearIndependent_monoidHom K K).comp _ hf`. Establish `hfib : ∀ σ ∈ Finset.univ.image φ, (Finset.univ.filter fun g => φ g = σ).card = Nat.card φ.ker`.

Introduce `σ hσ`. Take `⟨g0, -, rfl⟩` from `Finset.mem_image.1 hσ`. Rewrite using `[MonoidHom.card_fiber_eq_of_mem_range φ ⟨g0, rfl⟩ ⟨1, rfl⟩, map_one, ← Nat.card_eq_finsetCard]`. Conclude with `Nat.card_congr (Equiv.subtypeEquivRight fun g => by simp [MonoidHom.mem_ker])`. Establish `hsum : ∀ w : K, ∑ g, φ g w = ∑ σ ∈ Finset.univ.image φ, (Nat.card φ.ker : K) * σ w`.

Introduce `w`. Rewrite using `[← Finset.sum_fiberwise_of_maps_to (g := φ) (t := Finset.univ.image φ) (fun g _ => Finset.mem_image_of_mem φ (Finset.mem_univ g))]`. Use `Finset.sum_congr rfl fun σ hσ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_congr rfl (fun g hg => by rw [(Finset.mem_filter.1 hg).2]), Finset.sum_const, hfib σ hσ, nsmul_eq_mul]`. Use `h (linearIndependent_iff'.1 hli (Finset.univ.image φ) (fun _ => (Nat.card φ.ker : K)) ?_ (φ 1) (Finset.mem_image_of_mem _ (Finset.mem_univ 1)))` and prove the remaining obligations.

Use function extensionality and compare the values at `w`. Establish `hw` using `hcon w`. Rewrite `hw` using `[hsum w]`. Simplify `hw` using `[Finset.sum_apply]`.
-/
theorem exists_sum_ne_zero {D k K : Type} [Group D] [Fintype D] [Field k] [Field K] [Algebra k K]
    (φ : D →* (K ≃ₐ[k] K)) (h : (Nat.card φ.ker : K) ≠ 0) : ∃ w : K, ∑ g, φ g w ≠ 0 := by
  classical
  by_contra hcon
  push_neg at hcon
  have hf : Function.Injective (fun σ : K ≃ₐ[k] K => (σ : K →* K)) :=
    fun σ τ hστ => AlgEquiv.ext fun x => DFunLike.congr_fun hστ x
  have hli := (linearIndependent_monoidHom K K).comp _ hf
  have hfib : ∀ σ ∈ Finset.univ.image φ,
      (Finset.univ.filter fun g => φ g = σ).card = Nat.card φ.ker := by
    intro σ hσ
    obtain ⟨g0, -, rfl⟩ := Finset.mem_image.1 hσ
    rw [MonoidHom.card_fiber_eq_of_mem_range φ ⟨g0, rfl⟩ ⟨1, rfl⟩, map_one,
      ← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun g => by simp [MonoidHom.mem_ker])
  have hsum : ∀ w : K, ∑ g, φ g w = ∑ σ ∈ Finset.univ.image φ, (Nat.card φ.ker : K) * σ w := by
    intro w
    rw [← Finset.sum_fiberwise_of_maps_to (g := φ) (t := Finset.univ.image φ)
      (fun g _ => Finset.mem_image_of_mem φ (Finset.mem_univ g))]
    refine Finset.sum_congr rfl fun σ hσ => ?_
    rw [Finset.sum_congr rfl (fun g hg => by rw [(Finset.mem_filter.1 hg).2]), Finset.sum_const,
      hfib σ hσ, nsmul_eq_mul]
  refine h (linearIndependent_iff'.1 hli (Finset.univ.image φ) (fun _ => (Nat.card φ.ker : K)) ?_ (φ 1)
    (Finset.mem_image_of_mem _ (Finset.mem_univ 1)))
  funext w
  have hw := hcon w
  rw [hsum w] at hw
  simpa [Finset.sum_apply] using hw

/- English proof (translation)
Take `⟨w, hw⟩` from `exists_sum_ne_zero φ h`. Take `⟨c, hc⟩` from `hT w`. Establish `hcw : algebraMap k K c ≠ 0` using `by rw [hc]; exact hw`. Establish `hfix : ∀ y : K, (∀ g : D, φ g y = y) → ∃ c' : k, algebraMap k K c' = y`. Introduce `y hy`.

Take `⟨c', hc'⟩` from `hT (y * w)`. Use `⟨c' / c, ?_⟩` and prove the remaining obligations. Rewrite using `[map_div₀, hc', div_eq_iff hcw, hc]`. Simplify using `only [map_mul, hy, Finset.mul_sum]`. Use `letI : MulSemiringAction D K := MulSemiringAction.compHom K φ`.

Establish `hF : ∀ x : FixedPoints.subfield D K, ∃ c' : k, algebraMap k K c' = x` using `fun x => hfix x fun g => x.2 g`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Set `b` to `Module.finBasis (FixedPoints.subfield D K) K`. Use `⟨⟨Finset.univ.image b, eq_top_iff.2 fun x _ => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[← b.sum_repr x]`.

Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Take `⟨c', hc'⟩` from `hF (b.repr x i)`. Establish `he : b.repr x i • b i = c' • b i`. Rewrite using `[Algebra.smul_def, Algebra.smul_def, hc']`. Both sides reduce to the same expression.

Rewrite using `[he]`. Conclude with `Submodule.smul_mem _ c' (Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem b (Finset.mem_univ i))))`. Use `⟨fun x => ?_⟩` and prove the remaining obligations. Establish `hsF : (minpoly (FixedPoints.subfield D K) x).Separable` using `Algebra.IsSeparable.isSeparable (FixedPoints.subfield D K) x`. Establish `hl : (minpoly (FixedPoints.subfield D K) x).map (algebraMap (FixedPoints.subfield D K) K) ∈ Polynomial.lifts (algebraMap k K)`.

Rewrite using `[Polynomial.lifts_iff_coeff_lifts]`. Introduce `n`. Rewrite using `[Polynomial.coeff_map]`. Take `⟨c', hc'⟩` from `hF ((minpoly (FixedPoints.subfield D K) x).coeff n)`. Conclude with `⟨c', hc'⟩`.

Take `⟨pk, hpk⟩` from `Polynomial.mem_lifts _ |>.1 hl`. Establish `hsep : pk.Separable`. Rewrite using `[← Polynomial.separable_map (algebraMap k K), hpk, Polynomial.separable_map]`. Conclude with `hsF`. Establish `hx : Polynomial.aeval x pk = 0`.

Rewrite using `[Polynomial.aeval_def, ← Polynomial.eval_map, hpk, Polynomial.eval_map, ← Polynomial.aeval_def, minpoly.aeval]`. Conclude with `hsep.of_dvd (minpoly.dvd k x hx)`.
-/
theorem finite_separable_of_sum_mem {D k K : Type} [Group D] [Fintype D] [Field k] [Field K]
    [Algebra k K] (φ : D →* (K ≃ₐ[k] K)) (h : (Nat.card φ.ker : K) ≠ 0)
    (hT : ∀ x : K, ∃ c : k, algebraMap k K c = ∑ g, φ g x) :
    FiniteDimensional k K ∧ Algebra.IsSeparable k K := by
  classical
  obtain ⟨w, hw⟩ := exists_sum_ne_zero φ h
  obtain ⟨c, hc⟩ := hT w
  have hcw : algebraMap k K c ≠ 0 := by rw [hc]; exact hw
  have hfix : ∀ y : K, (∀ g : D, φ g y = y) → ∃ c' : k, algebraMap k K c' = y := by
    intro y hy
    obtain ⟨c', hc'⟩ := hT (y * w)
    refine ⟨c' / c, ?_⟩
    rw [map_div₀, hc', div_eq_iff hcw, hc]
    simp only [map_mul, hy, Finset.mul_sum]
  letI : MulSemiringAction D K := MulSemiringAction.compHom K φ
  have hF : ∀ x : FixedPoints.subfield D K, ∃ c' : k, algebraMap k K c' = x :=
    fun x => hfix x fun g => x.2 g
  refine ⟨?_, ?_⟩
  · let b := Module.finBasis (FixedPoints.subfield D K) K
    refine ⟨⟨Finset.univ.image b, eq_top_iff.2 fun x _ => ?_⟩⟩
    rw [← b.sum_repr x]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨c', hc'⟩ := hF (b.repr x i)
    have he : b.repr x i • b i = c' • b i := by
      rw [Algebra.smul_def, Algebra.smul_def, hc']
      rfl
    rw [he]
    exact Submodule.smul_mem _ c' (Submodule.subset_span
      (Finset.mem_coe.2 (Finset.mem_image_of_mem b (Finset.mem_univ i))))
  · refine ⟨fun x => ?_⟩
    have hsF : (minpoly (FixedPoints.subfield D K) x).Separable :=
      Algebra.IsSeparable.isSeparable (FixedPoints.subfield D K) x
    have hl : (minpoly (FixedPoints.subfield D K) x).map
        (algebraMap (FixedPoints.subfield D K) K) ∈ Polynomial.lifts (algebraMap k K) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      rw [Polynomial.coeff_map]
      obtain ⟨c', hc'⟩ := hF ((minpoly (FixedPoints.subfield D K) x).coeff n)
      exact ⟨c', hc'⟩
    obtain ⟨pk, hpk⟩ := Polynomial.mem_lifts _ |>.1 hl
    have hsep : pk.Separable := by
      rw [← Polynomial.separable_map (algebraMap k K), hpk, Polynomial.separable_map]
      exact hsF
    have hx : Polynomial.aeval x pk = 0 := by
      rw [Polynomial.aeval_def, ← Polynomial.eval_map, hpk, Polynomial.eval_map,
        ← Polynomial.aeval_def, minpoly.aeval]
    exact hsep.of_dvd (minpoly.dvd k x hx)

/- English proof (translation)
Establish `hpow : ∀ h : Γ, h ^ (Nat.card Γ - 1) = h⁻¹` using `fun h => eq_inv_of_mul_eq_one_left (by rw [← pow_succ, Nat.sub_add_cancel Nat.card_pos, pow_card_eq_one'])`. Establish `hex : ∀ g : Γ, ∃ a : B, a ∉ q ∧ (g • q ≠ q → g • a ∈ q)`. Introduce `g`. Distinguish the cases in `hg : g • q = q`. Conclude with `⟨1, (Ideal.ne_top_iff_one q).1 (Ideal.IsPrime.ne_top inferInstance), fun h => absurd hg h⟩`.

Assume the negation of the conclusion as `hcon`. Apply `hg` to reduce the goal to its premises. Establish `h1 : ∀ a : B, g • a ∈ q → a ∈ q` using `fun a ha =>`. Assume the negation of the conclusion as `fun hn => hcon ⟨a, hn, fun _ => ha⟩`. Establish `h2 : ∀ x ∈ q, g⁻¹ • x ∈ q` using `fun x hx => h1 _ (by rwa [smul_inv_smul])`.

Establish `h3 : ∀ m : ℕ, ∀ x ∈ q, (g⁻¹) ^ m • x ∈ q`. Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => intro x hx`. Rewrite using `[pow_zero, one_smul]` and apply the resulting hypothesis.

Consider the case `succ m ih => intro x hx`. Rewrite using `[pow_succ', mul_smul]`. Conclude with `h2 _ (ih x hx)`. Establish `h5 : ∀ x ∈ q, g • x ∈ q` using `fun x hx => by`. Use `h3 (Nat.card Γ - 1) x hx` as an intermediate fact.

Rewrite `this` using `[hpow, inv_inv]`. Then use the resulting hypothesis. Apply `Ideal.ext` to reduce the goal to its premises. Introduce `x`. Rewrite using `[Ideal.mem_pointwise_smul_iff_inv_smul_mem]`. Conclude with `⟨fun hx => by simpa using h5 _ hx, h2 x⟩`.

Use `choose a ha using hex`. Use `haveI := Fintype.ofFinite Γ`. Use `⟨∏ g, a g, ?_, fun g hg => ?_⟩` and prove the remaining obligations. Conclude with `prod_mem (S := q.primeCompl) fun g _ => (ha g).1`. Rewrite using `[Finset.smul_prod']`.

Conclude with `q.mem_of_dvd (Finset.dvd_prod_of_mem (fun i => g • a i) (Finset.mem_univ g)) ((ha g).2 hg)`.
-/
theorem exists_not_mem_smul_mem {Γ B : Type} [Group Γ] [Finite Γ] [CommRing B]
    [MulSemiringAction Γ B] (q : Ideal B) [q.IsPrime] :
    ∃ y : B, y ∉ q ∧ ∀ g : Γ, g • q ≠ q → g • y ∈ q := by
  classical
  have hpow : ∀ h : Γ, h ^ (Nat.card Γ - 1) = h⁻¹ := fun h =>
    eq_inv_of_mul_eq_one_left (by rw [← pow_succ, Nat.sub_add_cancel Nat.card_pos, pow_card_eq_one'])
  have hex : ∀ g : Γ, ∃ a : B, a ∉ q ∧ (g • q ≠ q → g • a ∈ q) := by
    intro g
    by_cases hg : g • q = q
    · exact ⟨1, (Ideal.ne_top_iff_one q).1 (Ideal.IsPrime.ne_top inferInstance),
        fun h => absurd hg h⟩
    · by_contra hcon
      apply hg
      have h1 : ∀ a : B, g • a ∈ q → a ∈ q := fun a ha =>
        by_contra fun hn => hcon ⟨a, hn, fun _ => ha⟩
      have h2 : ∀ x ∈ q, g⁻¹ • x ∈ q := fun x hx => h1 _ (by rwa [smul_inv_smul])
      have h3 : ∀ m : ℕ, ∀ x ∈ q, (g⁻¹) ^ m • x ∈ q := by
        intro m
        induction m with
        | zero => intro x hx; rwa [pow_zero, one_smul]
        | succ m ih => intro x hx; rw [pow_succ', mul_smul]; exact h2 _ (ih x hx)
      have h5 : ∀ x ∈ q, g • x ∈ q := fun x hx => by
        have := h3 (Nat.card Γ - 1) x hx
        rwa [hpow, inv_inv] at this
      apply Ideal.ext
      intro x
      rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
      exact ⟨fun hx => by simpa using h5 _ hx, h2 x⟩
  choose a ha using hex
  haveI := Fintype.ofFinite Γ
  refine ⟨∏ g, a g, ?_, fun g hg => ?_⟩
  · exact prod_mem (S := q.primeCompl) fun g _ => (ha g).1
  · rw [Finset.smul_prod']
    exact q.mem_of_dvd (Finset.dvd_prod_of_mem (fun i => g • a i) (Finset.mem_univ g)) ((ha g).2 hg)

/- English proof (translation)
Introduce `Γ _ _ A B _ _ _ _ _ _ q _ k K _ _ _ _ _ _ _ hcomp hin`. Use `haveI := Fintype.ofFinite Γ`. Use `letI : Algebra (A ⧸ q.under A) K := ((algebraMap k K).comp (algebraMap (A ⧸ q.under A) k)).toAlgebra`. Use `haveI : IsScalarTower (A ⧸ q.under A) k K := IsScalarTower.of_algebraMap_eq fun _ => rfl`. Use `haveI : IsScalarTower (A ⧸ q.under A) (B ⧸ q) K := IsScalarTower.of_algebraMap_eq fun x => by`.

Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Conclude with `hcomp a`. Set `ψ` to `Ideal.Quotient.stabilizerHom q (q.under A) Γ`. Set `φ : MulAction.stabilizer Γ q →* (K ≃ₐ[k] K)` to `(IsFractionRing.fieldEquivOfAlgEquivHom k K).comp ψ`. Establish `hφ : ∀ (g : MulAction.stabilizer Γ q) (u : B ⧸ q), φ g (algebraMap (B ⧸ q) K u) = algebraMap (B ⧸ q) K (ψ g u)` using `fun g u => by`.

Simplify using `[φ, IsFractionRing.fieldEquivOfAlgEquivHom, IsFractionRing.fieldEquivOfAlgEquiv_algebraMap]`. Establish `hψ : ∀ (g : MulAction.stabilizer Γ q) (b : B), ψ g (Ideal.Quotient.mk q b) = Ideal.Quotient.mk q ((g : Γ) • b)` using `fun g b => by first`. Consider the case `rfl`. Consider the case `simp [ψ, Ideal.Quotient.stabilizerHom]`. Establish `hι : ∀ u : B ⧸ q, u ≠ 0 → algebraMap (B ⧸ q) K u ≠ 0` using `fun u hu h0 => hu (IsFractionRing.injective (B ⧸ q) K (h0.trans (map_zero _).symm))`.

Establish `hsplit : ∀ F : Γ → K, (∀ g : Γ, g ∉ MulAction.stabilizer Γ q → F g = 0) → ∑ g, F g = ∑ g : MulAction.stabilizer Γ q, F g`. Introduce `F hF`. Establish `hs` using `Finset.sum_subset (Finset.subset_univ (Finset.univ.map (Function.Embedding.subtype (· ∈ MulAction.stabilizer Γ q)))) (f := F) (fun g _ hg => hF g fun hs => hg (Finset.mem_map.2 ⟨⟨g, hs⟩, Finset.mem_univ _, rfl⟩))`. Rewrite using `[← hs, Finset.sum_map]`. Both sides reduce to the same expression.

Establish `hle : q.inertia Γ ≤ MulAction.stabilizer Γ q`. Introduce `g hg`. Establish `hg' : g⁻¹ ∈ q.inertia Γ` using `inv_mem hg`. Rewrite using `[MulAction.mem_stabilizer_iff]`. Apply `Ideal.ext` to reduce the goal to its premises.

Introduce `x`. Rewrite using `[Ideal.mem_pointwise_smul_iff_inv_smul_mem]`. Establish `hx : g⁻¹ • x - x ∈ q` using `hg' x`. Prove the components needed by the constructor for the conclusion. Introduce `h1`.

Simplify using `using q.sub_mem h1 hx`. Introduce `h1`. Simplify using `using q.add_mem hx h1`. Establish `hmem : ∀ g : MulAction.stabilizer Γ q, g ∈ φ.ker ↔ (g : Γ) ∈ q.inertia Γ`. Introduce `g`.

Rewrite using `[MonoidHom.mem_ker]`. Prove the components needed by the constructor for the conclusion. Introduce `h x`. Use `congrArg (fun e : K ≃ₐ[k] K => e (algebraMap (B ⧸ q) K (Ideal.Quotient.mk q x))) h` as an intermediate fact. Simplify using `only [hφ, hψ, AlgEquiv.one_apply] at this`.

Conclude with `Ideal.Quotient.eq.1 (IsFractionRing.injective (B ⧸ q) K this)`. Introduce `h`. Use extensionality with `z`. Take `⟨u, v, -, rfl⟩` from `IsFractionRing.div_surjective (A := B ⧸ q) z`. Take `⟨u, rfl⟩` from `Ideal.Quotient.mk_surjective u`.

Take `⟨v, rfl⟩` from `Ideal.Quotient.mk_surjective v`. Simplify using `only [map_div₀, hφ, hψ, AlgEquiv.one_apply]`. Rewrite using `[Ideal.Quotient.eq.2 (h u), Ideal.Quotient.eq.2 (h v)]`. Establish `hcardeq : Nat.card φ.ker = Nat.card (q.inertia Γ)` using `Nat.card_congr { toFun := fun g => ⟨((g.1 : MulAction.stabilizer Γ q) : Γ), (hmem g.1).1 g.2⟩ invFun := fun h => ⟨⟨h.1, hle h.2⟩, (hmem ⟨h.1, hle h.2⟩).2 h.2⟩ left_inv := fun g => rfl right_inv := fun h => rfl }`. Establish `hkerK : ((Nat.card φ.ker : ℕ) : K) ≠ 0`.

Rewrite using `[hcardeq]`. Introduce `h0`. Apply `hin` to reduce the goal to its premises. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem]`. Apply `IsFractionRing.injective (B ⧸ q) K` to reduce the goal to its premises.

Simplify using `using h0`. Take `⟨y, hyq, hy⟩` from `exists_not_mem_smul_mem (Γ := Γ) q`. Establish `hB : ∀ u : B ⧸ q, ∃ c : k, algebraMap k K c = ∑ g, φ g (algebraMap (B ⧸ q) K u * algebraMap (B ⧸ q) K (Ideal.Quotient.mk q y))`. Introduce `u`. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective u`.

Take `⟨a, ha⟩` from `Algebra.IsInvariant.isInvariant (A := A) (G := Γ) (∑ g : Γ, g • (b * y)) (fun h => by`. Rewrite using `[Finset.smul_sum]`. Conclude with `Fintype.sum_equiv (Equiv.mulLeft h) _ _ (fun g => by simp [mul_smul]))`. Use `⟨algebraMap (A ⧸ q.under A) k (Ideal.Quotient.mk _ a), ?_⟩` and prove the remaining obligations. Rewrite using `[hcomp, ha, map_sum, map_sum]`.

Simplify using `only [← map_mul, hφ, hψ]`. Use `hsplit (fun g => algebraMap (B ⧸ q) K (Ideal.Quotient.mk q (g • (b * y)))) (fun g hg => ?_)` and prove the remaining obligations. Establish `hne : g • q ≠ q` using `fun h => hg (MulAction.mem_stabilizer_iff.2 h)`. Use `show algebraMap (B ⧸ q) K (Ideal.Quotient.mk q (g • (b * y))) = 0`. Rewrite using `[smul_mul', Ideal.Quotient.eq_zero_iff_mem.2 (q.mul_mem_left _ (hy g hne)), map_zero]`.

Establish `hTinv : ∀ (x : K) (h : MulAction.stabilizer Γ q), φ h (∑ g, φ g x) = ∑ g, φ g x`. Introduce `x h`. Rewrite using `[map_sum]`. Conclude with `Fintype.sum_equiv (Equiv.mulLeft h) _ _ (fun g => by simp [map_mul, AlgEquiv.mul_apply])`. Establish `hTlin : ∀ z x : K, (∀ g, φ g z = z) → ∑ g, φ g (z * x) = z * ∑ g, φ g x`.

Introduce `z x hz`. Simplify using `only [map_mul, hz, Finset.mul_sum]`. Take `⟨w0, hw0⟩` from `exists_sum_ne_zero φ hkerK`. Establish `hyq' : algebraMap (B ⧸ q) K (Ideal.Quotient.mk q y) ≠ 0` using `hι _ (fun h0 => hyq (Ideal.Quotient.eq_zero_iff_mem.1 h0))`. Establish `hfixk : ∀ z : K, (∀ g, φ g z = z) → ∃ c : k, algebraMap k K c = z`.

Introduce `z hz`. Take `⟨u, v, hv, huv⟩` from `IsFractionRing.div_surjective (A := B ⧸ q) z`. Establish `hv0 : algebraMap (B ⧸ q) K v ≠ 0` using `hι _ (nonZeroDivisors.ne_zero hv)`. Use `set c0 := algebraMap (B ⧸ q) K v * algebraMap (B ⧸ q) K (Ideal.Quotient.mk q y) with hc0def`. Establish `hc0 : c0 ≠ 0` using `mul_ne_zero hv0 hyq'`.

Establish `ht : ∃ t : B ⧸ q, ∑ g, φ g (c0 * algebraMap (B ⧸ q) K t) ≠ 0`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Apply `hw0` to reduce the goal to its premises. Take `⟨t1, t2, ht2, hdiv⟩` from `IsFractionRing.div_surjective (A := B ⧸ q) (w0 / c0)`.

Establish `ht20 : t2 ≠ 0` using `nonZeroDivisors.ne_zero ht2`. Use `set M' := ∏ g ∈ Finset.univ.erase (1 : MulAction.stabilizer Γ q), ψ g t2 with hM'`. Establish `hM : ∏ g, ψ g t2 = t2 * M'`. Rewrite using `[← Finset.mul_prod_erase Finset.univ (fun g => ψ g t2) (Finset.mem_univ 1), map_one]`. Both sides reduce to the same expression.

Establish `hMinv : ∀ h, φ h (algebraMap (B ⧸ q) K (∏ g, ψ g t2)) = algebraMap (B ⧸ q) K (∏ g, ψ g t2)`. Introduce `h`. Rewrite using `[hφ, map_prod]`. Use `congr 1`. Conclude with `Fintype.prod_equiv (Equiv.mulLeft h) _ _ (fun g => by simp [map_mul, AlgEquiv.mul_apply])`.

Establish `hM0 : ∏ g, ψ g t2 ≠ 0` using `Finset.prod_ne_zero_iff.2 fun g _ h0 => ht20 ((ψ g).injective (h0.trans (map_zero _).symm))`. Establish `hdiv' : algebraMap (B ⧸ q) K t1 * c0 = w0 * algebraMap (B ⧸ q) K t2`. Rewrite `hdiv` using `[div_eq_div_iff (hι _ ht20) hc0]`. Conclude with `hdiv`. Establish `hw : w0 * algebraMap (B ⧸ q) K (∏ g, ψ g t2) = c0 * algebraMap (B ⧸ q) K (t1 * M')`.

Rewrite using `[hM, map_mul, map_mul]`. Take the linear combination `(-(algebraMap (B ⧸ q) K M')) * hdiv'`. Establish `h1 : algebraMap (B ⧸ q) K (∏ g, ψ g t2) * ∑ g, φ g w0 = 0`. Rewrite using `[← hTlin _ w0 hMinv, mul_comm, hw]`. Conclude with `hcon _`.

Conclude with `(mul_eq_zero.1 h1).resolve_left (hι _ hM0)`. Take `⟨t, ht⟩` from `ht`. Take `⟨c1, hc1⟩` from `hB (u * t)`. Take `⟨c2, hc2⟩` from `hB (v * t)`. Use `⟨c1 / c2, ?_⟩` and prove the remaining obligations.

Establish `e2 : ∑ g, φ g (c0 * algebraMap (B ⧸ q) K t) = algebraMap k K c2`. Rewrite using `[hc2, map_mul]`. Use `Finset.sum_congr rfl fun g _ => congrArg (φ g) ?_` and prove the remaining obligations. Rewrite using `[hc0def]`. Expand and normalize the polynomial expressions, which then agree.

Establish `e1 : ∑ g, φ g (z * (c0 * algebraMap (B ⧸ q) K t)) = algebraMap k K c1`. Rewrite using `[hc1, map_mul]`. Use `Finset.sum_congr rfl fun g _ => congrArg (φ g) ?_` and prove the remaining obligations. Rewrite using `[hc0def, ← huv, div_mul_eq_mul_div, div_eq_iff hv0]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `e1` using `[hTlin z _ hz, e2]`. Establish `hc2ne : algebraMap k K c2 ≠ 0` using `by rw [← e2]; exact ht`. Rewrite using `[map_div₀, ← e1, mul_div_assoc, div_self hc2ne, _root_.mul_one]`. Conclude with `finite_separable_of_sum_mem φ hkerK (fun x => hfixk _ (hTinv x))`.
-/
theorem residue_finite_separable : ∀ (Γ : Type) [Group Γ] [Finite Γ] (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [MulSemiringAction Γ B] [SMulCommClass Γ A B] [Algebra.IsInvariant A B Γ] (q : Ideal B) [q.IsPrime] (k K : Type) [Field k] [Field K] [Algebra (A ⧸ q.under A) k] [IsFractionRing (A ⧸ q.under A) k] [Algebra (B ⧸ q) K] [IsFractionRing (B ⧸ q) K] [Algebra k K], (∀ a : A, algebraMap k K (algebraMap (A ⧸ q.under A) k (Ideal.Quotient.mk _ a)) = algebraMap (B ⧸ q) K (Ideal.Quotient.mk q (algebraMap A B a))) → (Nat.card (q.inertia Γ) : B) ∉ q → FiniteDimensional k K ∧ Algebra.IsSeparable k K := by
  intro Γ _ _ A B _ _ _ _ _ _ q _ k K _ _ _ _ _ _ _ hcomp hin
  classical
  haveI := Fintype.ofFinite Γ
  letI : Algebra (A ⧸ q.under A) K :=
    ((algebraMap k K).comp (algebraMap (A ⧸ q.under A) k)).toAlgebra
  haveI : IsScalarTower (A ⧸ q.under A) k K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower (A ⧸ q.under A) (B ⧸ q) K := IsScalarTower.of_algebraMap_eq fun x => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact hcomp a
  let ψ := Ideal.Quotient.stabilizerHom q (q.under A) Γ
  let φ : MulAction.stabilizer Γ q →* (K ≃ₐ[k] K) :=
    (IsFractionRing.fieldEquivOfAlgEquivHom k K).comp ψ
  have hφ : ∀ (g : MulAction.stabilizer Γ q) (u : B ⧸ q),
      φ g (algebraMap (B ⧸ q) K u) = algebraMap (B ⧸ q) K (ψ g u) := fun g u => by
    simp [φ, IsFractionRing.fieldEquivOfAlgEquivHom, IsFractionRing.fieldEquivOfAlgEquiv_algebraMap]
  have hψ : ∀ (g : MulAction.stabilizer Γ q) (b : B),
      ψ g (Ideal.Quotient.mk q b) = Ideal.Quotient.mk q ((g : Γ) • b) := fun g b => by
    first
      | rfl
      | simp [ψ, Ideal.Quotient.stabilizerHom]
  have hι : ∀ u : B ⧸ q, u ≠ 0 → algebraMap (B ⧸ q) K u ≠ 0 := fun u hu h0 =>
    hu (IsFractionRing.injective (B ⧸ q) K (h0.trans (map_zero _).symm))
  have hsplit : ∀ F : Γ → K, (∀ g : Γ, g ∉ MulAction.stabilizer Γ q → F g = 0) →
      ∑ g, F g = ∑ g : MulAction.stabilizer Γ q, F g := by
    intro F hF
    have hs := Finset.sum_subset (Finset.subset_univ
      (Finset.univ.map (Function.Embedding.subtype (· ∈ MulAction.stabilizer Γ q)))) (f := F)
      (fun g _ hg => hF g fun hs => hg (Finset.mem_map.2 ⟨⟨g, hs⟩, Finset.mem_univ _, rfl⟩))
    rw [← hs, Finset.sum_map]
    rfl
  have hle : q.inertia Γ ≤ MulAction.stabilizer Γ q := by
    intro g hg
    have hg' : g⁻¹ ∈ q.inertia Γ := inv_mem hg
    rw [MulAction.mem_stabilizer_iff]
    apply Ideal.ext
    intro x
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
    have hx : g⁻¹ • x - x ∈ q := hg' x
    constructor
    · intro h1; simpa using q.sub_mem h1 hx
    · intro h1; simpa using q.add_mem hx h1
  have hmem : ∀ g : MulAction.stabilizer Γ q, g ∈ φ.ker ↔ (g : Γ) ∈ q.inertia Γ := by
    intro g
    rw [MonoidHom.mem_ker]
    constructor
    · intro h x
      have := congrArg (fun e : K ≃ₐ[k] K => e (algebraMap (B ⧸ q) K (Ideal.Quotient.mk q x))) h
      simp only [hφ, hψ, AlgEquiv.one_apply] at this
      exact Ideal.Quotient.eq.1 (IsFractionRing.injective (B ⧸ q) K this)
    · intro h
      ext z
      obtain ⟨u, v, -, rfl⟩ := IsFractionRing.div_surjective (A := B ⧸ q) z
      obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective u
      obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective v
      simp only [map_div₀, hφ, hψ, AlgEquiv.one_apply]
      rw [Ideal.Quotient.eq.2 (h u), Ideal.Quotient.eq.2 (h v)]
  have hcardeq : Nat.card φ.ker = Nat.card (q.inertia Γ) :=
    Nat.card_congr
      { toFun := fun g => ⟨((g.1 : MulAction.stabilizer Γ q) : Γ), (hmem g.1).1 g.2⟩
        invFun := fun h => ⟨⟨h.1, hle h.2⟩, (hmem ⟨h.1, hle h.2⟩).2 h.2⟩
        left_inv := fun g => rfl
        right_inv := fun h => rfl }
  have hkerK : ((Nat.card φ.ker : ℕ) : K) ≠ 0 := by
    rw [hcardeq]
    intro h0
    apply hin
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    apply IsFractionRing.injective (B ⧸ q) K
    simpa using h0
  obtain ⟨y, hyq, hy⟩ := exists_not_mem_smul_mem (Γ := Γ) q
  have hB : ∀ u : B ⧸ q, ∃ c : k, algebraMap k K c =
      ∑ g, φ g (algebraMap (B ⧸ q) K u * algebraMap (B ⧸ q) K (Ideal.Quotient.mk q y)) := by
    intro u
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective u
    obtain ⟨a, ha⟩ := Algebra.IsInvariant.isInvariant (A := A) (G := Γ) (∑ g : Γ, g • (b * y))
      (fun h => by
        rw [Finset.smul_sum]
        exact Fintype.sum_equiv (Equiv.mulLeft h) _ _ (fun g => by simp [mul_smul]))
    refine ⟨algebraMap (A ⧸ q.under A) k (Ideal.Quotient.mk _ a), ?_⟩
    rw [hcomp, ha, map_sum, map_sum]
    simp only [← map_mul, hφ, hψ]
    refine hsplit (fun g => algebraMap (B ⧸ q) K (Ideal.Quotient.mk q (g • (b * y)))) (fun g hg => ?_)
    have hne : g • q ≠ q := fun h => hg (MulAction.mem_stabilizer_iff.2 h)
    show algebraMap (B ⧸ q) K (Ideal.Quotient.mk q (g • (b * y))) = 0
    rw [smul_mul', Ideal.Quotient.eq_zero_iff_mem.2 (q.mul_mem_left _ (hy g hne)), map_zero]
  have hTinv : ∀ (x : K) (h : MulAction.stabilizer Γ q), φ h (∑ g, φ g x) = ∑ g, φ g x := by
    intro x h
    rw [map_sum]
    exact Fintype.sum_equiv (Equiv.mulLeft h) _ _ (fun g => by simp [map_mul, AlgEquiv.mul_apply])
  have hTlin : ∀ z x : K, (∀ g, φ g z = z) → ∑ g, φ g (z * x) = z * ∑ g, φ g x := by
    intro z x hz
    simp only [map_mul, hz, Finset.mul_sum]
  obtain ⟨w0, hw0⟩ := exists_sum_ne_zero φ hkerK
  have hyq' : algebraMap (B ⧸ q) K (Ideal.Quotient.mk q y) ≠ 0 :=
    hι _ (fun h0 => hyq (Ideal.Quotient.eq_zero_iff_mem.1 h0))
  have hfixk : ∀ z : K, (∀ g, φ g z = z) → ∃ c : k, algebraMap k K c = z := by
    intro z hz
    obtain ⟨u, v, hv, huv⟩ := IsFractionRing.div_surjective (A := B ⧸ q) z
    have hv0 : algebraMap (B ⧸ q) K v ≠ 0 := hι _ (nonZeroDivisors.ne_zero hv)
    set c0 := algebraMap (B ⧸ q) K v * algebraMap (B ⧸ q) K (Ideal.Quotient.mk q y) with hc0def
    have hc0 : c0 ≠ 0 := mul_ne_zero hv0 hyq'
    have ht : ∃ t : B ⧸ q, ∑ g, φ g (c0 * algebraMap (B ⧸ q) K t) ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      apply hw0
      obtain ⟨t1, t2, ht2, hdiv⟩ := IsFractionRing.div_surjective (A := B ⧸ q) (w0 / c0)
      have ht20 : t2 ≠ 0 := nonZeroDivisors.ne_zero ht2
      set M' := ∏ g ∈ Finset.univ.erase (1 : MulAction.stabilizer Γ q), ψ g t2 with hM'
      have hM : ∏ g, ψ g t2 = t2 * M' := by
        rw [← Finset.mul_prod_erase Finset.univ (fun g => ψ g t2) (Finset.mem_univ 1), map_one]
        rfl
      have hMinv : ∀ h, φ h (algebraMap (B ⧸ q) K (∏ g, ψ g t2)) =
          algebraMap (B ⧸ q) K (∏ g, ψ g t2) := by
        intro h
        rw [hφ, map_prod]
        congr 1
        exact Fintype.prod_equiv (Equiv.mulLeft h) _ _ (fun g => by simp [map_mul, AlgEquiv.mul_apply])
      have hM0 : ∏ g, ψ g t2 ≠ 0 := Finset.prod_ne_zero_iff.2 fun g _ h0 =>
        ht20 ((ψ g).injective (h0.trans (map_zero _).symm))
      have hdiv' : algebraMap (B ⧸ q) K t1 * c0 = w0 * algebraMap (B ⧸ q) K t2 := by
        rw [div_eq_div_iff (hι _ ht20) hc0] at hdiv
        exact hdiv
      have hw : w0 * algebraMap (B ⧸ q) K (∏ g, ψ g t2) = c0 * algebraMap (B ⧸ q) K (t1 * M') := by
        rw [hM, map_mul, map_mul]
        linear_combination (-(algebraMap (B ⧸ q) K M')) * hdiv'
      have h1 : algebraMap (B ⧸ q) K (∏ g, ψ g t2) * ∑ g, φ g w0 = 0 := by
        rw [← hTlin _ w0 hMinv, mul_comm, hw]
        exact hcon _
      exact (mul_eq_zero.1 h1).resolve_left (hι _ hM0)
    obtain ⟨t, ht⟩ := ht
    obtain ⟨c1, hc1⟩ := hB (u * t)
    obtain ⟨c2, hc2⟩ := hB (v * t)
    refine ⟨c1 / c2, ?_⟩
    have e2 : ∑ g, φ g (c0 * algebraMap (B ⧸ q) K t) = algebraMap k K c2 := by
      rw [hc2, map_mul]
      refine Finset.sum_congr rfl fun g _ => congrArg (φ g) ?_
      rw [hc0def]
      ring
    have e1 : ∑ g, φ g (z * (c0 * algebraMap (B ⧸ q) K t)) = algebraMap k K c1 := by
      rw [hc1, map_mul]
      refine Finset.sum_congr rfl fun g _ => congrArg (φ g) ?_
      rw [hc0def, ← huv, div_mul_eq_mul_div, div_eq_iff hv0]
      ring
    rw [hTlin z _ hz, e2] at e1
    have hc2ne : algebraMap k K c2 ≠ 0 := by rw [← e2]; exact ht
    rw [map_div₀, ← e1, mul_div_assoc, div_self hc2ne, _root_.mul_one]
  exact finite_separable_of_sum_mem φ hkerK (fun x => hfixk _ (hTinv x))

end GlobalTheory.TameResidue
