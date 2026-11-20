import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.MassIntegralStmt

noncomputable section

open NumberField

namespace Formalism.MainNotions.Gaps.MI

/- English proof (translation)
Proceed by induction on `t with`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `succ t ih`. Take `⟨P, hP⟩` from `ih`. Use `⟨P + t • (1 : A) + P * X, ?_⟩` and prove the remaining obligations.

Rewrite using `[pow_succ, hP, succ_nsmul]`. Simplify using `only [mul_add, add_mul, mul_one, one_mul, smul_mul_assoc, mul_smul_comm, mul_assoc]`. Normalize the expressions using the abelian group laws.
-/
theorem one_add_pow_expand {A : Type*} [Ring A] (X : A) (t : ℕ) :
    ∃ P : A, (1 + X) ^ t = 1 + t • X + X * X * P := by
  induction t with
  | zero => exact ⟨0, by simp⟩
  | succ t ih =>
    obtain ⟨P, hP⟩ := ih
    refine ⟨P + t • (1 : A) + P * X, ?_⟩
    rw [pow_succ, hP, succ_nsmul]
    simp only [mul_add, add_mul, mul_one, one_mul, smul_mul_assoc, mul_smul_comm, mul_assoc]
    abel

/- English proof (translation)
Use `set X : Matrix n n R := C - 1 with hX`. Establish `hCX : C = 1 + X` using `by rw [hX]; abel`. Use `set I : Ideal R := Ideal.span (Set.range fun p : n × n => X p.1 p.2) with hI`. Establish `hmem : ∀ i j, X i j ∈ I` using `fun i j => Ideal.subset_span ⟨(i, j), rfl⟩`. Take `⟨P, hP⟩` from `one_add_pow_expand X t`.

Rewrite `hP` using `[← hCX, hC]`. Establish `h0 : t • X + X * X * P = 0`. Establish `: (1 : Matrix n n R) + (t • X + X * X * P) = 1 + 0`. Rewrite using `[add_zero, ← add_assoc]`. Conclude with `hP.symm`.

Conclude with `add_left_cancel this`. Establish `hXX : ∀ i j, (X * X) i j ∈ I * I`. Introduce `i j`. Rewrite using `[Matrix.mul_apply]`. Conclude with `Ideal.sum_mem _ fun l _ => Ideal.mul_mem_mul (hmem i l) (hmem l j)`.

Establish `hXXP : ∀ i j, (X * X * P) i j ∈ I * I`. Introduce `i j`. Rewrite using `[Matrix.mul_apply]`. Conclude with `Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (hXX i l)`. Establish `hle : I ≤ I • I`.

Rewrite using `[hI, Ideal.span_le, ← hI]`. Introduce and unpack `_ ⟨p, rfl⟩`. Take `⟨u, hu⟩` from `ht`. Establish `h1 : (t : R) * X p.1 p.2 = - (X * X * P) p.1 p.2`. Use `congrFun (congrFun h0 p.1) p.2` as an intermediate fact.

Rewrite `this` using `[Matrix.add_apply, Matrix.smul_apply, nsmul_eq_mul, Matrix.zero_apply]`. Take the linear combination `this`. Establish `h2 : X p.1 p.2 = (↑u⁻¹ : R) * (- (X * X * P) p.1 p.2)`. Rewrite using `[← h1, ← hu, ← mul_assoc, Units.inv_mul, one_mul]`. Use `show X p.1 p.2 ∈ I * I`.

Rewrite using `[h2]`. Conclude with `Ideal.mul_mem_left _ _ (neg_mem (hXXP _ _))`. Establish `hIj : I ≤ Ideal.jacobson ⊥`. Rewrite using `[hI, Ideal.span_le]`. Introduce and unpack `_ ⟨p, rfl⟩`.

Conclude with `hmod p.1 p.2`. Establish `hfg : I.FG` using `Submodule.fg_span (Set.finite_range _)`. Establish `hbot : I = ⊥` using `Submodule.eq_bot_of_le_smul_of_le_jacobson_bot I I hfg hle hIj`. Establish `hX0 : X = 0`. Use extensionality with `i j`.

Use `hmem i j` as an intermediate fact. Rewrite `this` using `[hbot]`. Simplify using `using this`. Rewrite using `[hCX, hX0, add_zero]`.
-/
theorem mat_eq_one {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
    (C : Matrix n n R) (t : ℕ) (ht : IsUnit (t : R)) (hC : C ^ t = 1)
    (hmod : ∀ i j, (C - 1) i j ∈ Ideal.jacobson (⊥ : Ideal R)) : C = 1 := by
  set X : Matrix n n R := C - 1 with hX
  have hCX : C = 1 + X := by rw [hX]; abel
  set I : Ideal R := Ideal.span (Set.range fun p : n × n => X p.1 p.2) with hI
  have hmem : ∀ i j, X i j ∈ I := fun i j => Ideal.subset_span ⟨(i, j), rfl⟩
  obtain ⟨P, hP⟩ := one_add_pow_expand X t
  rw [← hCX, hC] at hP
  have h0 : t • X + X * X * P = 0 := by
    have : (1 : Matrix n n R) + (t • X + X * X * P) = 1 + 0 := by
      rw [add_zero, ← add_assoc]; exact hP.symm
    exact add_left_cancel this
  have hXX : ∀ i j, (X * X) i j ∈ I * I := by
    intro i j
    rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_mul (hmem i l) (hmem l j)
  have hXXP : ∀ i j, (X * X * P) i j ∈ I * I := by
    intro i j
    rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (hXX i l)
  have hle : I ≤ I • I := by
    rw [hI, Ideal.span_le, ← hI]
    rintro _ ⟨p, rfl⟩
    obtain ⟨u, hu⟩ := ht
    have h1 : (t : R) * X p.1 p.2 = - (X * X * P) p.1 p.2 := by
      have := congrFun (congrFun h0 p.1) p.2
      rw [Matrix.add_apply, Matrix.smul_apply, nsmul_eq_mul, Matrix.zero_apply] at this
      linear_combination this
    have h2 : X p.1 p.2 = (↑u⁻¹ : R) * (- (X * X * P) p.1 p.2) := by
      rw [← h1, ← hu, ← mul_assoc, Units.inv_mul, one_mul]
    show X p.1 p.2 ∈ I * I
    rw [h2]
    exact Ideal.mul_mem_left _ _ (neg_mem (hXXP _ _))
  have hIj : I ≤ Ideal.jacobson ⊥ := by
    rw [hI, Ideal.span_le]
    rintro _ ⟨p, rfl⟩
    exact hmod p.1 p.2
  have hfg : I.FG := Submodule.fg_span (Set.finite_range _)
  have hbot : I = ⊥ := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot I I hfg hle hIj
  have hX0 : X = 0 := by
    ext i j
    have := hmem i j
    rw [hbot] at this
    simpa using this
  rw [hCX, hX0, add_zero]

/- English proof (translation)
Establish `: Fact g.Prime` using `⟨hg⟩`. Set `f : G →* Module.End R L` to `{ toFun := fun a => ((a : (Fin k → K) ≃ₗ[K] (Fin k → K)).toLinearMap.restrictScalars R).restrict (hG a a.2) map_one' := by ext x; rfl map_mul' := fun a b => by ext x; rfl }`. Establish `hfin : Module.finrank R L = k`. Rewrite using `[Submodule.IsLattice.finrank_of_pi K L, Fintype.card_fin]`. Set `b : Module.Basis (Fin k) R L` to `Module.finBasisOfFinrankEq R L hfin`.

Set `T : G →* Matrix (Fin k) (Fin k) R` to `((LinearMap.toMatrixAlgEquiv b : Module.End R L ≃ₐ[R] Matrix (Fin k) (Fin k) R) : Module.End R L →* Matrix (Fin k) (Fin k) R).comp f`. Set `Tφ : G →* Matrix (Fin k) (Fin k) (ZMod g)` to `((φ.mapMatrix : Matrix (Fin k) (Fin k) R →+* Matrix (Fin k) (Fin k) (ZMod g)) : Matrix (Fin k) (Fin k) R →* Matrix (Fin k) (Fin k) (ZMod g)).comp T`. Establish `hTinj : ∀ c : G, T c = 1 → c = 1`. Introduce `c hc`. Establish `h1 : f c = 1`.

Establish `: (LinearMap.toMatrixAlgEquiv b) (f c) = (LinearMap.toMatrixAlgEquiv b) 1`. Rewrite using `[map_one]`. Conclude with `hc`. Conclude with `(LinearMap.toMatrixAlgEquiv b).injective this`. Establish `h2 : ∀ x ∈ L, (c : (Fin k → K) ≃ₗ[K] (Fin k → K)) x = x`.

Introduce `x hx`. Use `congrArg (fun e : Module.End R L => ((e ⟨x, hx⟩ : L) : Fin k → K)) h1` as an intermediate fact. Conclude with `this`. Establish `h3 : (c : (Fin k → K) ≃ₗ[K] (Fin k → K)).toLinearMap = LinearMap.id` using `LinearMap.ext_on (Submodule.IsLattice.span_eq_top (M := L)) (fun x hx => h2 x hx)`. Apply `Subtype.ext` to reduce the goal to its premises.

Apply `LinearEquiv.toLinearMap_injective` to reduce the goal to its premises. Conclude with `h3`. Use `⟨Tφ.toHomUnits, ?_⟩` and prove the remaining obligations. Introduce and unpack `a ⟨n, hn, han⟩ ⟨N, hN⟩`. Establish `han' : a ^ n = 1` using `by simpa [Function.IsPeriodicPt, Function.IsFixedPt] using han`.

Take `⟨s, t, htg, hnt⟩` from `Nat.exists_eq_pow_mul_and_not_dvd hn.ne' g hg.ne_one`. Use `⟨N + s, hTinj _ ?_⟩` and prove the remaining obligations. Establish `htu : IsUnit ((t : ℕ) : R)`. Apply `hφ` to reduce the goal to its premises. Rewrite using `[map_natCast]`.

Introduce `h0`. Conclude with `htg ((ZMod.natCast_eq_zero_iff t g).1 h0)`. Apply `mat_eq_one _ t htu` to reduce the goal to its premises. Rewrite using `[← map_pow, ← pow_mul, pow_add, mul_assoc, ← hnt, mul_comm, pow_mul, han', one_pow, map_one]`. Introduce `i j`.

Establish `h1 : Tφ (a ^ g ^ (N + s)) = 1`. Establish `h2 : Tφ a ^ (g ^ N) = 1`. Use `congrArg (fun u : GL (Fin k) (ZMod g) => (u : Matrix (Fin k) (Fin k) (ZMod g))) hN` as an intermediate fact. Simplify using `using this`. Rewrite using `[pow_add, pow_mul, map_pow, map_pow, h2, one_pow]`.

Establish `h3 : φ ((T (a ^ g ^ (N + s)) - 1) i j) = 0`. Use `congrFun (congrFun h1 i) j` as an intermediate fact. Establish `h4 : φ (T (a ^ g ^ (N + s)) i j) = (1 : Matrix (Fin k) (Fin k) (ZMod g)) i j` using `this`. Rewrite using `[Matrix.sub_apply, map_sub, h4]`. Distinguish the cases in `hij : i = j`.

Substitute `hij` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Matrix.one_apply_ne hij]`. Rewrite using `[IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Introduce `hu`.

Use `hu.map φ` as an intermediate fact. Rewrite `this` using `[h3]`. Conclude with `not_isUnit_zero this`.
-/
theorem red_local {R K : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [IsLocalRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] (k g : ℕ) (hg : g.Prime)
    (φ : R →+* ZMod g) (hφ : ∀ x, φ x ≠ 0 → IsUnit x)
    (L : Submodule R (Fin k → K)) [Submodule.IsLattice K L]
    (G : Subgroup ((Fin k → K) ≃ₗ[K] (Fin k → K)))
    (hG : ∀ a ∈ G, ∀ x ∈ L, a x ∈ L) :
    ∃ ρ : G →* GL (Fin k) (ZMod g), ∀ a : G, IsOfFinOrder a →
      (∃ N : ℕ, ρ a ^ (g ^ N) = 1) → ∃ N : ℕ, a ^ (g ^ N) = 1 := by
  have : Fact g.Prime := ⟨hg⟩
  let f : G →* Module.End R L :=
    { toFun := fun a =>
        ((a : (Fin k → K) ≃ₗ[K] (Fin k → K)).toLinearMap.restrictScalars R).restrict (hG a a.2)
      map_one' := by ext x; rfl
      map_mul' := fun a b => by ext x; rfl }
  have hfin : Module.finrank R L = k := by
    rw [Submodule.IsLattice.finrank_of_pi K L, Fintype.card_fin]
  let b : Module.Basis (Fin k) R L := Module.finBasisOfFinrankEq R L hfin
  let T : G →* Matrix (Fin k) (Fin k) R :=
    ((LinearMap.toMatrixAlgEquiv b : Module.End R L ≃ₐ[R] Matrix (Fin k) (Fin k) R) :
      Module.End R L →* Matrix (Fin k) (Fin k) R).comp f
  let Tφ : G →* Matrix (Fin k) (Fin k) (ZMod g) :=
    ((φ.mapMatrix : Matrix (Fin k) (Fin k) R →+* Matrix (Fin k) (Fin k) (ZMod g)) :
      Matrix (Fin k) (Fin k) R →* Matrix (Fin k) (Fin k) (ZMod g)).comp T
  have hTinj : ∀ c : G, T c = 1 → c = 1 := by
    intro c hc
    have h1 : f c = 1 := by
      have : (LinearMap.toMatrixAlgEquiv b) (f c) = (LinearMap.toMatrixAlgEquiv b) 1 := by
        rw [map_one]; exact hc
      exact (LinearMap.toMatrixAlgEquiv b).injective this
    have h2 : ∀ x ∈ L, (c : (Fin k → K) ≃ₗ[K] (Fin k → K)) x = x := by
      intro x hx
      have := congrArg (fun e : Module.End R L => ((e ⟨x, hx⟩ : L) : Fin k → K)) h1
      exact this
    have h3 : (c : (Fin k → K) ≃ₗ[K] (Fin k → K)).toLinearMap = LinearMap.id :=
      LinearMap.ext_on (Submodule.IsLattice.span_eq_top (M := L)) (fun x hx => h2 x hx)
    apply Subtype.ext
    apply LinearEquiv.toLinearMap_injective
    exact h3
  refine ⟨Tφ.toHomUnits, ?_⟩
  rintro a ⟨n, hn, han⟩ ⟨N, hN⟩
  have han' : a ^ n = 1 := by simpa [Function.IsPeriodicPt, Function.IsFixedPt] using han
  obtain ⟨s, t, htg, hnt⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' g hg.ne_one
  refine ⟨N + s, hTinj _ ?_⟩
  have htu : IsUnit ((t : ℕ) : R) := by
    apply hφ
    rw [map_natCast]
    intro h0
    exact htg ((ZMod.natCast_eq_zero_iff t g).1 h0)
  apply mat_eq_one _ t htu
  · rw [← map_pow, ← pow_mul, pow_add, mul_assoc, ← hnt, mul_comm, pow_mul, han', one_pow, map_one]
  · intro i j
    have h1 : Tφ (a ^ g ^ (N + s)) = 1 := by
      have h2 : Tφ a ^ (g ^ N) = 1 := by
        have := congrArg (fun u : GL (Fin k) (ZMod g) => (u : Matrix (Fin k) (Fin k) (ZMod g))) hN
        simpa using this
      rw [pow_add, pow_mul, map_pow, map_pow, h2, one_pow]
    have h3 : φ ((T (a ^ g ^ (N + s)) - 1) i j) = 0 := by
      have := congrFun (congrFun h1 i) j
      have h4 : φ (T (a ^ g ^ (N + s)) i j) = (1 : Matrix (Fin k) (Fin k) (ZMod g)) i j := this
      rw [Matrix.sub_apply, map_sub, h4]
      by_cases hij : i = j
      · subst hij; simp
      · simp [Matrix.one_apply_ne hij]
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff]
    intro hu
    have := hu.map φ
    rw [h3] at this
    exact not_isUnit_zero this

/- English proof (translation)
Introduce `E _ _ k g hg v hv he M hM G hG _`. Take `⟨e⟩` from `he`. Establish `hvbot : v ≠ ⊥`. Introduce `h`. Apply `NumberField.RingOfIntegers.not_isField E` to reduce the goal to its premises.

Rewrite using `[Ring.isField_iff_maximal_bot]`. Conclude with `h ▸ hv`. Establish `hS : v.primeCompl ≤ nonZeroDivisors (𝓞 E)` using `Ideal.primeCompl_le_nonZeroDivisors v`. Set `R : Subalgebra (𝓞 E) E` to `Localization.subalgebra.ofField E v.primeCompl hS`. Establish `hloc : IsLocalization.AtPrime R v` using `Localization.subalgebra.isLocalization_ofField E v.primeCompl hS`.

Establish `hlr : IsLocalRing R` using `IsLocalization.AtPrime.isLocalRing R v`. Establish `hdvr : IsDiscreteValuationRing R` using `IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 E) hvbot R`. Set `φ : R →+* ZMod g` to `((e : (𝓞 E ⧸ v) →+* ZMod g).comp ((IsLocalization.AtPrime.equivQuotMaximalIdeal v R).symm : (R ⧸ IsLocalRing.maximalIdeal R) →+* (𝓞 E ⧸ v))).comp (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R))`. Establish `hφ : ∀ x, φ x ≠ 0 → IsUnit x`. Introduce `x hx`.

Assume the negation of the conclusion as `hnu`. Apply `hx` to reduce the goal to its premises. Establish `h0 : Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) x = 0` using `Ideal.Quotient.eq_zero_iff_mem.2 ((IsLocalRing.mem_maximalIdeal x).2 hnu)`. Simplify using `[φ, h0]`. Set `L : Submodule R (Fin k → E)` to `Submodule.span R (M : Set (Fin k → E))`.

Establish `hL : Submodule.IsLattice E L` using `{ fg := by`. Take `⟨s, hs⟩` from `hM.fg`. Use `⟨s, ?_⟩` and prove the remaining obligations. Rewrite using `[← Submodule.span_span_of_tower (𝓞 E) R (s : Set (Fin k → E)), hs]`. Use `span_eq_top := by`.

Rewrite using `[Submodule.span_span_of_tower R E (M : Set (Fin k → E))]`. Conclude with `hM.span_eq_top }`. Establish `hGL : ∀ a ∈ G, ∀ x ∈ L, a x ∈ L`. Introduce `a ha`. Establish `: L ≤ L.comap (a.toLinearMap.restrictScalars R)` using `Submodule.span_le.2 fun x hx => Submodule.subset_span (hG a ha x hx)`.

Conclude with `fun x hx => this hx`. Conclude with `red_local k g hg φ hφ L G hGL`.
-/
theorem redHomGen : RedHomGen := by
  intro E _ _ k g hg v hv he M hM G hG _
  obtain ⟨e⟩ := he
  have hvbot : v ≠ ⊥ := by
    intro h
    apply NumberField.RingOfIntegers.not_isField E
    rw [Ring.isField_iff_maximal_bot]
    exact h ▸ hv
  have hS : v.primeCompl ≤ nonZeroDivisors (𝓞 E) := Ideal.primeCompl_le_nonZeroDivisors v
  let R : Subalgebra (𝓞 E) E := Localization.subalgebra.ofField E v.primeCompl hS
  have hloc : IsLocalization.AtPrime R v :=
    Localization.subalgebra.isLocalization_ofField E v.primeCompl hS
  have hlr : IsLocalRing R := IsLocalization.AtPrime.isLocalRing R v
  have hdvr : IsDiscreteValuationRing R :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 E) hvbot R
  let φ : R →+* ZMod g :=
    ((e : (𝓞 E ⧸ v) →+* ZMod g).comp
      ((IsLocalization.AtPrime.equivQuotMaximalIdeal v R).symm :
        (R ⧸ IsLocalRing.maximalIdeal R) →+* (𝓞 E ⧸ v))).comp
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R))
  have hφ : ∀ x, φ x ≠ 0 → IsUnit x := by
    intro x hx
    by_contra hnu
    apply hx
    have h0 : Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) x = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 ((IsLocalRing.mem_maximalIdeal x).2 hnu)
    simp [φ, h0]
  let L : Submodule R (Fin k → E) := Submodule.span R (M : Set (Fin k → E))
  have hL : Submodule.IsLattice E L :=
    { fg := by
        obtain ⟨s, hs⟩ := hM.fg
        refine ⟨s, ?_⟩
        rw [← Submodule.span_span_of_tower (𝓞 E) R (s : Set (Fin k → E)), hs]
      span_eq_top := by
        rw [Submodule.span_span_of_tower R E (M : Set (Fin k → E))]
        exact hM.span_eq_top }
  have hGL : ∀ a ∈ G, ∀ x ∈ L, a x ∈ L := by
    intro a ha
    have : L ≤ L.comap (a.toLinearMap.restrictScalars R) :=
      Submodule.span_le.2 fun x hx => Submodule.subset_span (hG a ha x hx)
    exact fun x hx => this hx
  exact red_local k g hg φ hφ L G hGL

end Formalism.MainNotions.Gaps.MI
