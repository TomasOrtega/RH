import Development.WeilBound.CoreStatements.FlagImmersions.FibSandwich
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.WedgeLatticeGeneratorStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsCombTangentIffLinearSumStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenFrameIffEigenspaceBasisStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormPrimitiveRootPrimePowSubOnePadicComplexStatement
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AlternatingMapSumSmulEqDetSmul

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl

namespace RootFieldNumerics.RF.Loc

/- English proof (translation)
Set `f : (Fin n → V) →ₗ[V] W` to `Fintype.linearCombination V x`. Establish `hf : ∀ u, f u = ∑ i, u i • x i` using `fun u => Fintype.linearCombination_apply V x u`. Establish `hfr : LinearMap.range f = Submodule.span V (Set.range x)` using `Fintype.range_linearCombination V x`. Set `N : Submodule V (Fin n → V)` to `Λ.comap f`. Establish `hcN : ∀ u : Fin n → V, c • u ∈ N` using `fun u => by`.

Express the relevant statement in the definitionally equal form `f (c • u) ∈ Λ`. Rewrite using `[map_smul]`. Conclude with `h₂ _ (hfr ▸ ⟨u, rfl⟩)`. Set `g : (Fin n → V) →ₗ[V] N` to `LinearMap.codRestrict N (c • LinearMap.id) hcN`. Establish `hg : Function.Injective g` using `fun u u' h => by`.

Establish `: c • u = c • u'` using `congrArg Subtype.val h`. Conclude with `smul_right_injective _ hc this`. Establish `hr : Module.finrank V N = n`. Use `le_antisymm ((Submodule.finrank_le N).trans (by simp)) ?_` and prove the remaining obligations. Simplify using `using LinearMap.finrank_le_finrank_of_injective hg`.

Set `b` to `Module.finBasisOfFinrankEq V N hr`. Use `⟨Matrix.of fun k i => (b k : Fin n → V) i, Matrix.of fun i k => b.repr (g (Pi.single i 1)) k, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `i i'`. Establish `h` using `congrArg (fun u : N => (u : Fin n → V) i') (b.sum_repr (g (Pi.single i 1)))`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h`.

Rewrite using `[Matrix.mul_apply]`. Simplify using `only [Matrix.of_apply]`. Rewrite using `[h]`. Simplify using `[g, Matrix.one_apply, Pi.single_apply, eq_comm]`. Establish `e : (fun k => ∑ i, (Matrix.of fun k i => (b k : Fin n → V) i) k i • x i) = fun k => f (b k)`.

Use function extensionality and compare the values at `fun k => (hf _).symm`. Rewrite using `[e]`. Use `le_antisymm (Submodule.span_le.2 ?_) fun w hw => ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨k, rfl⟩`. Conclude with `(b k).2`.

Take `⟨u, rfl⟩ : w ∈ LinearMap.range f` from `hfr ▸ h₁ hw`. Establish `hu : u ∈ N` using `hw`. Establish `h` using `congrArg (fun t : N => f t) (b.sum_repr ⟨u, hu⟩)`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul] at h`. Rewrite using `[← h]`.

Conclude with `Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)`.
-/
theorem exists_basis {V L W : Type} [CommRing V] [IsDomain V] [IsPrincipalIdealRing V] [Field L] [Algebra V L]
    [IsFractionRing V L] [AddCommGroup W] [Module L W] [Module V W] [IsScalarTower V L W] {n : ℕ} (x : Fin n → W)
    (Λ : Submodule V W) {c : V} (hc : c ≠ 0) (h₁ : Λ ≤ Submodule.span V (Set.range x))
    (h₂ : ∀ w ∈ Submodule.span V (Set.range x), c • w ∈ Λ) :
    ∃ P Q : Matrix (Fin n) (Fin n) V, Q * P = c • (1 : Matrix (Fin n) (Fin n) V) ∧
      Submodule.span V (Set.range fun k => ∑ i, P k i • x i) = Λ := by
  classical
  let f : (Fin n → V) →ₗ[V] W := Fintype.linearCombination V x
  have hf : ∀ u, f u = ∑ i, u i • x i := fun u => Fintype.linearCombination_apply V x u
  have hfr : LinearMap.range f = Submodule.span V (Set.range x) := Fintype.range_linearCombination V x
  let N : Submodule V (Fin n → V) := Λ.comap f
  have hcN : ∀ u : Fin n → V, c • u ∈ N := fun u => by
    change f (c • u) ∈ Λ
    rw [map_smul]
    exact h₂ _ (hfr ▸ ⟨u, rfl⟩)
  let g : (Fin n → V) →ₗ[V] N := LinearMap.codRestrict N (c • LinearMap.id) hcN
  have hg : Function.Injective g := fun u u' h => by
    have : c • u = c • u' := congrArg Subtype.val h
    exact smul_right_injective _ hc this
  have hr : Module.finrank V N = n := by
    refine le_antisymm ((Submodule.finrank_le N).trans (by simp)) ?_
    simpa using LinearMap.finrank_le_finrank_of_injective hg
  let b := Module.finBasisOfFinrankEq V N hr
  refine ⟨Matrix.of fun k i => (b k : Fin n → V) i, Matrix.of fun i k => b.repr (g (Pi.single i 1)) k, ?_, ?_⟩
  · ext i i'
    have h := congrArg (fun u : N => (u : Fin n → V) i') (b.sum_repr (g (Pi.single i 1)))
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply]
    rw [h]
    simp [g, Matrix.one_apply, Pi.single_apply, eq_comm]
  · have e : (fun k => ∑ i, (Matrix.of fun k i => (b k : Fin n → V) i) k i • x i) = fun k => f (b k) :=
      funext fun k => (hf _).symm
    rw [e]
    refine le_antisymm (Submodule.span_le.2 ?_) fun w hw => ?_
    · rintro _ ⟨k, rfl⟩
      exact (b k).2
    · obtain ⟨u, rfl⟩ : w ∈ LinearMap.range f := hfr ▸ h₁ hw
      have hu : u ∈ N := hw
      have h := congrArg (fun t : N => f t) (b.sum_repr ⟨u, hu⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul] at h
      rw [← h]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

/- English proof (translation)
Establish `e : j Q.det * j P.det = j c ^ n`. Rewrite using `[← map_mul, ← Matrix.det_mul, h, Matrix.det_smul, Matrix.det_one, mul_one, map_pow, Fintype.card_fin]`. Establish `h0 : j Q.det * j P.det ≠ 0` using `e ▸ pow_ne_zero _ hc`. Establish `hP` using `right_ne_zero_of_mul h0`. Establish `hQ` using `left_ne_zero_of_mul h0`.

Establish `e2 : Real.log ‖j Q.det‖ + Real.log ‖j P.det‖ = n * Real.log ‖j c‖`. Rewrite using `[← Real.log_mul (norm_ne_zero_iff.2 hQ) (norm_ne_zero_iff.2 hP), ← norm_mul, e, norm_pow, Real.log_pow]`. Establish `a1` using `Real.log_nonpos (norm_nonneg _) (hj Q.det)`. Establish `a2` using `Real.log_nonpos (norm_nonneg _) (hj P.det)`. Conclude with `⟨hP, by linarith, a2⟩`.
-/
theorem log_det_bounds {V A : Type} [CommRing V] [NormedField A] (j : V →+* A) (hj : ∀ a, ‖j a‖ ≤ 1) {n : ℕ}
    {P Q : Matrix (Fin n) (Fin n) V} {c : V} (hc : j c ≠ 0) (h : Q * P = c • (1 : Matrix (Fin n) (Fin n) V)) :
    j P.det ≠ 0 ∧ n * Real.log ‖j c‖ ≤ Real.log ‖j P.det‖ ∧ Real.log ‖j P.det‖ ≤ 0 := by
  have e : j Q.det * j P.det = j c ^ n := by
    rw [← map_mul, ← Matrix.det_mul, h, Matrix.det_smul, Matrix.det_one, mul_one, map_pow, Fintype.card_fin]
  have h0 : j Q.det * j P.det ≠ 0 := e ▸ pow_ne_zero _ hc
  have hP := right_ne_zero_of_mul h0
  have hQ := left_ne_zero_of_mul h0
  have e2 : Real.log ‖j Q.det‖ + Real.log ‖j P.det‖ = n * Real.log ‖j c‖ := by
    rw [← Real.log_mul (norm_ne_zero_iff.2 hQ) (norm_ne_zero_iff.2 hP), ← norm_mul, e, norm_pow, Real.log_pow]
  have a1 := Real.log_nonpos (norm_nonneg _) (hj Q.det)
  have a2 := Real.log_nonpos (norm_nonneg _) (hj P.det)
  exact ⟨hP, by linarith, a2⟩

section Ev

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {R : Type} [CommRing R] [IsLocalRing R]

/- English proof (translation)
Set `e : X.presheaf.stalk (centre z) ≃+* regAt ξ ⟨centre z, h⟩` to `RingEquiv.ofBijective (genMap ξ ⟨centre z, h⟩).rangeRestrict ⟨fun a b hab => hξ.inj ⟨centre z, h⟩ (congrArg Subtype.val hab), RingHom.rangeRestrict_surjective _⟩`. Use `⟨(Scheme.stalkClosedPointTo z).hom.comp e.symm.toRingHom, fun a => ⟨h, e.symm a, ?_, rfl⟩⟩` and prove the remaining obligations. Conclude with `congrArg Subtype.val (e.apply_symm_apply a)`.
-/
theorem exists_ev (hξ : IsCptGen ξ) (z : Spec (CommRingCat.of R) ⟶ X) (h : genPt ξ ⤳ centre z) :
    ∃ ev : regAt ξ ⟨centre z, h⟩ →+* R, ∀ a : regAt ξ ⟨centre z, h⟩, ValAt ξ z a (ev a) := by
  let e : X.presheaf.stalk (centre z) ≃+* regAt ξ ⟨centre z, h⟩ :=
    RingEquiv.ofBijective (genMap ξ ⟨centre z, h⟩).rangeRestrict
      ⟨fun a b hab => hξ.inj ⟨centre z, h⟩ (congrArg Subtype.val hab), RingHom.rangeRestrict_surjective _⟩
  refine ⟨(Scheme.stalkClosedPointTo z).hom.comp e.symm.toRingHom, fun a => ⟨h, e.symm a, ?_, rfl⟩⟩
  exact congrArg Subtype.val (e.apply_symm_apply a)

end Ev

/- English proof (translation)
Rewrite using `[← PadicComplex.coe_natCast (p := p), PadicComplex.norm_extends (p := p), ← PadicAlgCl.valuation_coe (p := p), PadicAlgCl.valuation_p]`. Simplify using the standard rewrite rules.
-/
theorem norm_p (p : Nat.Primes) : ‖((p : ℕ) : ℂ_[p])‖ = ((p : ℕ) : ℝ)⁻¹ := by
  rw [← PadicComplex.coe_natCast (p := p), PadicComplex.norm_extends (p := p), ← PadicAlgCl.valuation_coe (p := p),
    PadicAlgCl.valuation_p]
  simp

/- English proof (translation)
Rewrite using `[norm_p]`. Conclude with `inv_lt_one_of_one_lt₀ (by exact_mod_cast p.2.one_lt)`.
-/
theorem norm_p_lt_one (p : Nat.Primes) : ‖((p : ℕ) : ℂ_[p])‖ < 1 := by
  rw [norm_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast p.2.one_lt)

/- English proof (translation)
Establish `hp : (p : ℕ).Prime` using `p.2`. Establish `hp1 : (1 : ℝ) < (p : ℕ)` using `by exact_mod_cast hp.one_lt`. Establish `key : ‖f ⟨κ, hκ⟩‖ = ((p : ℕ) : ℝ) ^ (-cP p)`. Unfold `HT.IsCp at h`. Unfold `cP`.

Use `split_ifs at h ⊢ with h2`. Establish `e : (⟨κ, hκ⟩ : R) = ((p : ℕ) : R) ^ 2` using `Subtype.ext (by`. Establish `e0 : κ = (((p : ℕ) : ℕ) : Ω) ^ 2` using `by rw [h, h2]; norm_num`. Simplify using `using e0)`. Establish `hn` using `norm_p p`.

Rewrite using `[e, map_pow, map_natCast, norm_pow, hn, Real.rpow_neg (by positivity), inv_pow]`. Evaluate the numerical expressions. Take `⟨ζ, hζ, rfl⟩` from `h`. Establish `hζR : ζ ∈ R` using `by simpa using R.add_mem hκ R.one_mem`. Establish `hs : ∑ i ∈ Finset.range p, (⟨ζ, hζR⟩ : R) ^ i = 0` using `Subtype.ext (by`.

Simplify using `using hζ.geom_sum_eq_zero hp.one_lt)`. Establish `hs' : ∑ i ∈ Finset.range p, f ⟨ζ, hζR⟩ ^ i = 0`. Use `congrArg f hs` as an intermediate fact. Rewrite `this` using `[map_sum, map_zero]`. Simplify using `only [map_pow] at this`.

Conclude with `this`. Establish `h1 : f ⟨ζ, hζR⟩ ≠ 1` using `fun h1 => by`. Rewrite `hs'` using `[h1]`. Simplify using `at hs'`. Conclude with `hp.ne_zero hs'`.

Establish `hpow : f ⟨ζ, hζR⟩ ^ (p : ℕ) = 1`. Use `mul_geom_sum (f ⟨ζ, hζR⟩) p` as an intermediate fact. Rewrite `this` using `[hs', mul_zero]`. Conclude with `(sub_eq_zero.1 this.symm)`. Establish `hprim : IsPrimitiveRoot (f ⟨ζ, hζR⟩) ((p : ℕ) ^ 1)`.

Rewrite using `[pow_one]`. Use `IsPrimitiveRoot.orderOf (f ⟨ζ, hζR⟩)` as an intermediate fact. Rewrite `this` using `[orderOf_eq_prime hpow h1]`. Then use the resulting hypothesis. Establish `e : f ⟨ζ - 1, hκ⟩ = f ⟨ζ, hζR⟩ - 1`. Rewrite using `[← map_one f, ← map_sub]`.

Both sides reduce to the same expression. Rewrite using `[e, GlobalTheory.T.norm_primitiveRoot_primePow_sub_one_padicComplex p 1 le_rfl _ hprim]`. Use `congr 1`. Simplify using `[neg_div]`. Establish `hpos : 0 < ‖f ⟨κ, hκ⟩‖` using `key ▸ Real.rpow_pos_of_pos (by positivity) _`.

Conclude with `⟨norm_pos_iff.1 hpos, by rw [key, Real.log_rpow (by positivity)]; ring⟩`.
-/
theorem log_norm_cp {Ω : Type} [Field Ω] (R : Subring Ω) (p : Nat.Primes) (f : R →+* ℂ_[p]) {κ : Ω} (hκ : κ ∈ R)
    (h : HT.IsCp p κ) : f ⟨κ, hκ⟩ ≠ 0 ∧ Real.log ‖f ⟨κ, hκ⟩‖ = -(cP p * Real.log (p : ℕ)) := by
  have hp : (p : ℕ).Prime := p.2
  have hp1 : (1 : ℝ) < (p : ℕ) := by exact_mod_cast hp.one_lt
  have key : ‖f ⟨κ, hκ⟩‖ = ((p : ℕ) : ℝ) ^ (-cP p) := by
    unfold HT.IsCp at h
    unfold cP
    split_ifs at h ⊢ with h2
    · have e : (⟨κ, hκ⟩ : R) = ((p : ℕ) : R) ^ 2 := Subtype.ext (by
        have e0 : κ = (((p : ℕ) : ℕ) : Ω) ^ 2 := by rw [h, h2]; norm_num
        simpa using e0)
      have hn := norm_p p
      rw [e, map_pow, map_natCast, norm_pow, hn, Real.rpow_neg (by positivity), inv_pow]
      norm_num
    · obtain ⟨ζ, hζ, rfl⟩ := h
      have hζR : ζ ∈ R := by simpa using R.add_mem hκ R.one_mem
      have hs : ∑ i ∈ Finset.range p, (⟨ζ, hζR⟩ : R) ^ i = 0 := Subtype.ext (by
        simpa using hζ.geom_sum_eq_zero hp.one_lt)
      have hs' : ∑ i ∈ Finset.range p, f ⟨ζ, hζR⟩ ^ i = 0 := by
        have := congrArg f hs
        rw [map_sum, map_zero] at this
        simp only [map_pow] at this
        exact this
      have h1 : f ⟨ζ, hζR⟩ ≠ 1 := fun h1 => by
        rw [h1] at hs'
        simp at hs'
        exact hp.ne_zero hs'
      have hpow : f ⟨ζ, hζR⟩ ^ (p : ℕ) = 1 := by
        have := mul_geom_sum (f ⟨ζ, hζR⟩) p
        rw [hs', mul_zero] at this
        exact (sub_eq_zero.1 this.symm)
      have hprim : IsPrimitiveRoot (f ⟨ζ, hζR⟩) ((p : ℕ) ^ 1) := by
        rw [pow_one]
        have := IsPrimitiveRoot.orderOf (f ⟨ζ, hζR⟩)
        rwa [orderOf_eq_prime hpow h1] at this
      have e : f ⟨ζ - 1, hκ⟩ = f ⟨ζ, hζR⟩ - 1 := by
        rw [← map_one f, ← map_sub]; rfl
      rw [e, GlobalTheory.T.norm_primitiveRoot_primePow_sub_one_padicComplex p 1 le_rfl _ hprim]
      congr 1
      simp [neg_div]
  have hpos : 0 < ‖f ⟨κ, hκ⟩‖ := key ▸ Real.rpow_pos_of_pos (by positivity) _
  exact ⟨norm_pos_iff.1 hpos, by rw [key, Real.log_rpow (by positivity)]; ring⟩

section Line

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type} [AddCommGroup E] [Module Ω E]

/- English proof (translation)
Establish `e : ∀ u : Fin n → E, flagStep Ω u n = Submodule.span Ω (Set.range u)` using `fun u => by`. Unfold `flagStep`. Use `congr 1`. Use extensionality with `w`. Simplify using the standard rewrite rules.

Establish `hm : ∀ i, ∃ t : Fin n → Ω, ∑ k, t k • b k = b₀ i` using `fun i => by`. Establish `: b₀ i ∈ Submodule.span Ω (Set.range b)`. Rewrite using `[← e, h, e]`. Conclude with `Submodule.subset_span ⟨i, rfl⟩`. Conclude with `(Submodule.mem_span_range_iff_exists_fun _).1 this`.

Use `choose t ht using hm`. Use `⟨(Matrix.of t).det, ?_⟩` and prove the remaining obligations. Rewrite using `[← GlobalTheory.alternating_map_sum_smul_eq_det_smul (exteriorPower.ιMulti Ω n (M := E)) (Matrix.of t) b]`. Use `congr 1`. Conclude with `funext fun i => (ht i).symm`.
-/
theorem wedge_of_span {n : ℕ} (b b₀ : Fin n → E) (h : flagStep Ω b n = flagStep Ω b₀ n) :
    ∃ α : Ω, exteriorPower.ιMulti Ω n b₀ = α • exteriorPower.ιMulti Ω n b := by
  have e : ∀ u : Fin n → E, flagStep Ω u n = Submodule.span Ω (Set.range u) := fun u => by
    unfold flagStep
    congr 1
    ext w
    simp
  have hm : ∀ i, ∃ t : Fin n → Ω, ∑ k, t k • b k = b₀ i := fun i => by
    have : b₀ i ∈ Submodule.span Ω (Set.range b) := by
      rw [← e, h, e]; exact Submodule.subset_span ⟨i, rfl⟩
    exact (Submodule.mem_span_range_iff_exists_fun _).1 this
  choose t ht using hm
  refine ⟨(Matrix.of t).det, ?_⟩
  rw [← GlobalTheory.alternating_map_sum_smul_eq_det_smul (exteriorPower.ιMulti Ω n (M := E)) (Matrix.of t) b]
  congr 1
  exact funext fun i => (ht i).symm

/- English proof (translation)
Take `⟨wp, np⟩` from `GlobalTheory.T.wedge_lattice_generator X Ω ξ E A p bp x hp`. Take `⟨wq, nq⟩` from `GlobalTheory.T.wedge_lattice_generator X Ω ξ E B q bq x hq`. Establish `hL : lineLat A B p q a b x = Submodule.span (regAt ξ x) {β / α}`. Use `le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨f, ⟨α', β', hα', hβ', h1, h2, h3⟩, rfl⟩`.

Establish `m1 : α' • a ∈ Submodule.span (regAt ξ x) {exteriorPower.ιMulti Ω p bp}`. Rewrite using `[← wp, h1]`. Conclude with `Submodule.mem_span_singleton_self _`. Establish `m2 : exteriorPower.ιMulti Ω q bq ∈ Submodule.span (regAt ξ x) {β' • b}`. Rewrite using `[← h2, wq]`.

Conclude with `Submodule.mem_span_singleton_self _`. Take `⟨u, hu⟩` from `Submodule.mem_span_singleton.1 m1`. Take `⟨u', hu'⟩` from `Submodule.mem_span_singleton.1 m2`. Establish `e1 : (u : Ω) = α' * α` using `smul_left_injective Ω np (by`. Express the relevant statement in the definitionally equal form `(u : Ω) • _ = (α' * α) • _`.

Rewrite using `[← smul_smul, ← ea]`. Conclude with `hu)`. Establish `e2 : (u' : Ω) * β' * β = 1` using `smul_left_injective Ω nq (by`. Express the relevant statement in the definitionally equal form `((u' : Ω) * β' * β) • _ = (1 : Ω) • _`. Rewrite using `[← smul_smul, ← smul_smul, ← eb, one_smul]`.

Conclude with `hu')`. Use `Submodule.mem_span_singleton.2 ⟨u * u', ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((u : Ω) * u') * (β / α) = f⁻¹`. Establish `e3 : f = β' / α'` using `eq_div_of_mul_eq hα' h3`. Establish `e4 : (u' : Ω) = 1 / (β' * β)` using `eq_div_of_mul_eq (mul_ne_zero hβ' hβ) (by rw [← mul_assoc]; exact e2)`.

Rewrite using `[e1, e3, e4]`. Clear the denominators using the available nonvanishing facts. Introduce and unpack `_ rfl`. Use `Submodule.subset_span ⟨α / β, ⟨α⁻¹, β⁻¹, inv_ne_zero hα, inv_ne_zero hβ, ?_, ?_, ?_⟩, (inv_div _ _).symm⟩` and prove the remaining obligations. Rewrite using `[wp, ea, smul_smul, inv_mul_cancel₀ hα, one_smul]`.

Rewrite using `[wq, eb, smul_smul, inv_mul_cancel₀ hβ, one_smul]`. Clear the denominators using the available nonvanishing facts. Take `⟨e, c, he, h1, h2, h3⟩` from `h`. Establish `m1 : e ∈ Submodule.span (regAt ξ x) {β / α}`. Rewrite using `[← hL, h1]`.

Conclude with `Submodule.mem_span_singleton_self _`. Establish `m2 : β / α ∈ Submodule.span (regAt ξ x) {e}`. Rewrite using `[← h1, hL]`. Conclude with `Submodule.mem_span_singleton_self _`. Take `⟨u, hu⟩` from `Submodule.mem_span_singleton.1 m1`.

Take `⟨u', hu'⟩` from `Submodule.mem_span_singleton.1 m2`. Establish `hu1 : (u : Ω) * (β / α) = e` using `hu`. Establish `hu2 : (u' : Ω) * e = β / α` using `hu'`. Establish `huu : (u : Ω) * u' = 1` using `mul_right_cancel₀ he (by rw [mul_assoc, hu2, hu1, one_mul])`. Establish `hunit : unitAt ξ x (u : Ω)` using `⟨left_ne_zero_of_mul_eq_one huu, u.2, by rw [← eq_inv_of_mul_eq_one_right huu]; exact u'.2⟩`.

Establish `e5 : σ * α / β = c * u`. Rewrite using `[h2, smul_eq_mul, ← hu1]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e5, mul_pow, mul_div_right_comm]`. Conclude with `ZUnit.mul h3 (ZUnit.pow hunit m)`.
-/
theorem coeff_order {A B : Lat ξ E} {p q : ℕ} {a : ⋀[Ω]^p E} {b : ⋀[Ω]^q E} {x : Cpt ξ} {bp : Fin p → E}
    {bq : Fin q → E} (hp : A.IsFrameAt bp x) (hq : B.IsFrameAt bq x) {α β : Ω} (hα : α ≠ 0) (hβ : β ≠ 0)
    (ea : a = α • exteriorPower.ιMulti Ω p bp) (eb : b = β • exteriorPower.ιMulti Ω q bq) {σ ϖ : Ω} {m : ℕ} {k : ℤ}
    (h : OrderAt (lineLat A B p q a b) σ ϖ m k x) : unitAt ξ x ((σ * α / β) ^ m / ϖ ^ k) := by
  obtain ⟨wp, np⟩ := GlobalTheory.T.wedge_lattice_generator X Ω ξ E A p bp x hp
  obtain ⟨wq, nq⟩ := GlobalTheory.T.wedge_lattice_generator X Ω ξ E B q bq x hq
  have hL : lineLat A B p q a b x = Submodule.span (regAt ξ x) {β / α} := by
    refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨f, ⟨α', β', hα', hβ', h1, h2, h3⟩, rfl⟩
      have m1 : α' • a ∈ Submodule.span (regAt ξ x) {exteriorPower.ιMulti Ω p bp} := by
        rw [← wp, h1]; exact Submodule.mem_span_singleton_self _
      have m2 : exteriorPower.ιMulti Ω q bq ∈ Submodule.span (regAt ξ x) {β' • b} := by
        rw [← h2, wq]; exact Submodule.mem_span_singleton_self _
      obtain ⟨u, hu⟩ := Submodule.mem_span_singleton.1 m1
      obtain ⟨u', hu'⟩ := Submodule.mem_span_singleton.1 m2
      have e1 : (u : Ω) = α' * α := smul_left_injective Ω np (by
        change (u : Ω) • _ = (α' * α) • _
        rw [← smul_smul, ← ea]; exact hu)
      have e2 : (u' : Ω) * β' * β = 1 := smul_left_injective Ω nq (by
        change ((u' : Ω) * β' * β) • _ = (1 : Ω) • _
        rw [← smul_smul, ← smul_smul, ← eb, one_smul]; exact hu')
      refine Submodule.mem_span_singleton.2 ⟨u * u', ?_⟩
      change ((u : Ω) * u') * (β / α) = f⁻¹
      have e3 : f = β' / α' := eq_div_of_mul_eq hα' h3
      have e4 : (u' : Ω) = 1 / (β' * β) := eq_div_of_mul_eq (mul_ne_zero hβ' hβ) (by rw [← mul_assoc]; exact e2)
      rw [e1, e3, e4]
      field_simp
    · rintro _ rfl
      refine Submodule.subset_span ⟨α / β, ⟨α⁻¹, β⁻¹, inv_ne_zero hα, inv_ne_zero hβ, ?_, ?_, ?_⟩, (inv_div _ _).symm⟩
      · rw [wp, ea, smul_smul, inv_mul_cancel₀ hα, one_smul]
      · rw [wq, eb, smul_smul, inv_mul_cancel₀ hβ, one_smul]
      · field_simp
  obtain ⟨e, c, he, h1, h2, h3⟩ := h
  have m1 : e ∈ Submodule.span (regAt ξ x) {β / α} := by
    rw [← hL, h1]; exact Submodule.mem_span_singleton_self _
  have m2 : β / α ∈ Submodule.span (regAt ξ x) {e} := by
    rw [← h1, hL]; exact Submodule.mem_span_singleton_self _
  obtain ⟨u, hu⟩ := Submodule.mem_span_singleton.1 m1
  obtain ⟨u', hu'⟩ := Submodule.mem_span_singleton.1 m2
  have hu1 : (u : Ω) * (β / α) = e := hu
  have hu2 : (u' : Ω) * e = β / α := hu'
  have huu : (u : Ω) * u' = 1 := mul_right_cancel₀ he (by rw [mul_assoc, hu2, hu1, one_mul])
  have hunit : unitAt ξ x (u : Ω) :=
    ⟨left_ne_zero_of_mul_eq_one huu, u.2, by rw [← eq_inv_of_mul_eq_one_right huu]; exact u'.2⟩
  have e5 : σ * α / β = c * u := by
    rw [h2, smul_eq_mul, ← hu1]
    field_simp
  rw [e5, mul_pow, mul_div_right_comm]
  exact ZUnit.mul h3 (ZUnit.pow hunit m)

end Line

end RootFieldNumerics.RF.Loc
