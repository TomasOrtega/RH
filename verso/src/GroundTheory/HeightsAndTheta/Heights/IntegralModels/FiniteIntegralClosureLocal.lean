import Mathlib
set_option maxSynthPendingDepth 1

open scoped nonZeroDivisors

namespace GroundTheory.Heights₂.Heights.Model

/- English proof (translation)
Use `choose! r hr N hN hx using h`. Use `set s : Set A := r '' {𝔪 | 𝔪.IsMaximal}`. Establish `hs : Ideal.span s = ⊤`. Assume the negation of the conclusion as `hne`. Take `⟨𝔪, h𝔪, hle⟩` from `Ideal.exists_le_maximal _ hne`.

Conclude with `hr 𝔪 h𝔪 (hle (Ideal.subset_span ⟨𝔪, h𝔪, rfl⟩))`. Take `⟨t, hts, ht⟩` from `(Ideal.span_eq_top_iff_finite s).mp hs`. Establish `hmt : ∀ a ∈ t, ∃ 𝔪 : Ideal A, 𝔪.IsMaximal ∧ r 𝔪 = a` using `fun a ha => hts ha`. Use `choose! m hm hrm using hmt`. Set `P : Submodule A M` to `⨆ a ∈ t, N (m a)`.

Establish `hP : P.FG` using `Submodule.fg_biSup t _ fun a ha => hN (m a) (hm a ha)`. It suffices to establish `hPt : P = ⊤ from ⟨hPt ▸ hP⟩`. Rewrite using `[eq_top_iff]`. Introduce and unpack `x -`. Use `Submodule.mem_of_span_eq_top_of_smul_pow_mem P (t : Set A) ht x ?_` and prove the remaining obligations.

Introduce and unpack `⟨a, ha⟩`. Take `⟨n, hn⟩` from `hx (m a) (hm a ha) x`. Use `⟨n, ?_⟩` and prove the remaining obligations. Establish `hle : N (m a) ≤ P` using `le_iSup₂ (f := fun a (_ : a ∈ t) => N (m a)) a ha`. Use `show a ^ n • x ∈ P`.

Rewrite using `[← hrm a ha]`. Conclude with `hle hn`.
-/
theorem module_finite_of_forall_isMaximal {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (h : ∀ 𝔪 : Ideal A, 𝔪.IsMaximal →
      ∃ r ∉ 𝔪, ∃ N : Submodule A M, N.FG ∧ ∀ x : M, ∃ n : ℕ, r ^ n • x ∈ N) :
    Module.Finite A M := by
  classical
  choose! r hr N hN hx using h
  set s : Set A := r '' {𝔪 | 𝔪.IsMaximal}
  have hs : Ideal.span s = ⊤ := by
    by_contra hne
    obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal _ hne
    exact hr 𝔪 h𝔪 (hle (Ideal.subset_span ⟨𝔪, h𝔪, rfl⟩))
  obtain ⟨t, hts, ht⟩ := (Ideal.span_eq_top_iff_finite s).mp hs
  have hmt : ∀ a ∈ t, ∃ 𝔪 : Ideal A, 𝔪.IsMaximal ∧ r 𝔪 = a := fun a ha => hts ha
  choose! m hm hrm using hmt
  let P : Submodule A M := ⨆ a ∈ t, N (m a)
  have hP : P.FG := Submodule.fg_biSup t _ fun a ha => hN (m a) (hm a ha)
  suffices hPt : P = ⊤ from ⟨hPt ▸ hP⟩
  rw [eq_top_iff]
  rintro x -
  refine Submodule.mem_of_span_eq_top_of_smul_pow_mem P (t : Set A) ht x ?_
  rintro ⟨a, ha⟩
  obtain ⟨n, hn⟩ := hx (m a) (hm a ha) x
  refine ⟨n, ?_⟩
  have hle : N (m a) ≤ P := le_iSup₂ (f := fun a (_ : a ∈ t) => N (m a)) a ha
  show a ^ n • x ∈ P
  rw [← hrm a ha]
  exact hle hn

/- English proof (translation)
Use `set C := MvPolynomial (Fin d) ℤ`. Establish `hZ` using `Algebra.ZariskisMainProperty.of_finiteType_of_weaklyQuasiFiniteAt (R := C) 𝔪`. Take `⟨r, hr𝔪, hrint, hm⟩` from `Algebra.zariskisMainProperty_iff.mp hZ`. Use `choose m hm using hm`. Set `_ : Algebra C K` to `((algebraMap A K).comp (algebraMap C A)).toAlgebra`.

Establish `: IsScalarTower C A K` using `IsScalarTower.of_algebraMap_eq' rfl`. Establish `hinjCK : Function.Injective (algebraMap C K)` using `(IsFractionRing.injective A K).comp hinj`. Establish `: FaithfulSMul C K` using `(faithfulSMul_iff_algebraMap_injective C K).mpr hinjCK`. Set `_ : Algebra (FractionRing C) K` to `FractionRing.liftAlgebra C K`. Establish `hr0 : algebraMap A K r ≠ 0`.

Rewrite using `[map_ne_zero_iff _ (IsFractionRing.injective A K)]`. Conclude with `fun h => hr𝔪 (h ▸ 𝔪.zero_mem)`. Establish `hintK : ∀ a : A, IsIntegral C a → IsIntegral (FractionRing C) (algebraMap A K a)` using `fun a ha => (ha.map (IsScalarTower.toAlgHom C A K)).tower_top`. Establish `: FiniteDimensional (FractionRing C) K`. Take `⟨t, ht⟩` from `Algebra.FiniteType.out (R := C) (A := A)`.

Set `T : Set K` to `insert (algebraMap A K r) ((fun x => algebraMap A K (r ^ m x * x)) '' t)`. Establish `hTint : ∀ z ∈ T, IsIntegral (FractionRing C) z`. Introduce and unpack `z (rfl | ⟨x, -, rfl⟩)`. Conclude with `hintK r hrint`. Conclude with `hintK _ (hm x)`.

Establish `: Finite T` using `((t.finite_toSet.image _).insert _).to_subtype`. Establish `hfd` using `IntermediateField.finiteDimensional_adjoin hTint`. Establish `htop : IntermediateField.adjoin (FractionRing C) T = ⊤`. Rewrite using `[eq_top_iff]`. Introduce and unpack `z -`.

Establish `hA : ∀ a : A, algebraMap A K a ∈ IntermediateField.adjoin (FractionRing C) T`. Introduce `a`. Establish `ha : a ∈ Algebra.adjoin C (t : Set A)` using `ht ▸ Algebra.mem_top`. Proceed by induction on `ha using Algebra.adjoin_induction with`. Consider the case `mem x hx`.

Establish `hr' : algebraMap A K r ∈ IntermediateField.adjoin (FractionRing C) T` using `IntermediateField.subset_adjoin _ _ (Set.mem_insert _ _)`. Establish `hx' : algebraMap A K (r ^ m x * x) ∈ IntermediateField.adjoin (FractionRing C) T` using `IntermediateField.subset_adjoin _ _ (Set.mem_insert_of_mem _ ⟨x, hx, rfl⟩)`. Establish `: algebraMap A K x = algebraMap A K (r ^ m x * x) / algebraMap A K r ^ m x`. Rewrite using `[map_mul, map_pow, mul_div_cancel_left₀ _ (pow_ne_zero _ hr0)]`. Rewrite using `[this]`.

Conclude with `div_mem hx' (pow_mem hr' _)`. Consider the case `algebraMap c`. Rewrite using `[← IsScalarTower.algebraMap_apply C A K, IsScalarTower.algebraMap_apply C (FractionRing C) K]`. Conclude with `IntermediateField.algebraMap_mem _ _`. Consider the case `add x y _ _ hx hy => rw [map_add]`.

Conclude with `add_mem hx hy`. Consider the case `mul x y _ _ hx hy => rw [map_mul]`. Conclude with `mul_mem hx hy`. Take `⟨a, b, -, rfl⟩` from `IsFractionRing.div_surjective (A := A) z`. Conclude with `div_mem (hA a) (hA b)`.

Rewrite `hfd` using `[htop]`. Conclude with `(IntermediateField.topEquiv (F := FractionRing C) (E := K)).toLinearEquiv.finiteDimensional`. Establish `: CharZero (FractionRing C)` using `charZero_of_injective_algebraMap (IsFractionRing.injective C (FractionRing C))`. Establish `: Algebra.IsSeparable (FractionRing C) K` using `Algebra.IsSeparable.of_integral _ _`. Establish `: Module.Finite C (integralClosure C K)` using `IsIntegralClosure.finite C (FractionRing C) K (integralClosure C K)`.

Take `⟨g, hg⟩` from `(Module.Finite.fg_top : (⊤ : Submodule C (integralClosure C K)).FG)`. Set `ι : integralClosure C K → integralClosure A K` to `fun y => ⟨y.1, y.2.tower_top⟩`. Set `N : Submodule A (integralClosure A K)` to `Submodule.span A (ι '' g)`. Establish `hN : ∀ y : integralClosure C K, ι y ∈ N`. Introduce `y`.

Establish `hy : y ∈ Submodule.span C (g : Set (integralClosure C K))` using `hg ▸ Submodule.mem_top`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩`. Consider the case `zero => exact N.zero_mem`. Consider the case `add y z _ _ hy hz`.

Establish `: ι (y + z) = ι y + ι z` using `rfl`. Rewrite using `[this]`. Conclude with `N.add_mem hy hz`. Consider the case `smul c y _ hy`. Establish `: ι (c • y) = algebraMap C A c • ι y`.

Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `c • (y : K) = algebraMap C A c • (y : K)`. Rewrite using `[Algebra.smul_def, Algebra.smul_def, ← IsScalarTower.algebraMap_apply]`. Rewrite using `[this]`. Conclude with `N.smul_mem _ hy`.

Use `⟨r, hr𝔪, N, Submodule.fg_span (g.finite_toSet.image ι), fun x => ?_⟩` and prove the remaining obligations. Take `⟨P, hPm, hPx⟩` from `x.2`. Use `set D := P.natDegree`. Use `set M := (Finset.range (D + 1)).sup fun i => m (P.coeff i)`. Set `A₀` to `integralClosure C A`.

Establish `hcoeff : ∀ i, IsIntegral C ((P.scaleRoots (r ^ M)).coeff i)`. Introduce `i`. Rewrite using `[Polynomial.coeff_scaleRoots]`. Break down `lt_trichotomy i D with hi | hi | hi` into its components or cases. Establish `hmi : m (P.coeff i) ≤ M` using `Finset.le_sup (f := fun i => m (P.coeff i)) (Finset.mem_range.mpr (by omega))`.

Take `⟨k, hk⟩ : ∃ k, D - i = k + 1` from `⟨D - i - 1, by omega⟩`. Establish `: P.coeff i * (r ^ M) ^ (D - i) = (r ^ m (P.coeff i) * P.coeff i) * (r ^ (M - m (P.coeff i)) * (r ^ M) ^ k)`. Rewrite using `[hk, pow_succ]`. Rewrite using `[show (r ^ M) = r ^ m (P.coeff i) * r ^ (M - m (P.coeff i)) by`. Rewrite using `[← pow_add, Nat.add_sub_cancel' hmi]]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `(hm _).mul ((hrint.pow _).mul ((hrint.pow _).pow _))`. Rewrite using `[hi, Nat.sub_self, pow_zero, mul_one, ← Polynomial.leadingCoeff, hPm.leadingCoeff]`. Conclude with `isIntegral_one`.

Rewrite using `[Polynomial.coeff_eq_zero_of_natDegree_lt hi, zero_mul]`. Conclude with `isIntegral_zero`. Establish `hlifts : P.scaleRoots (r ^ M) ∈ Polynomial.lifts (algebraMap A₀ A)`. Rewrite using `[Polynomial.lifts_iff_coeff_lifts]`. Introduce `i`.

Conclude with `⟨⟨_, hcoeff i⟩, rfl⟩`. Establish `hmonic : (P.scaleRoots (r ^ M)).Monic`. Rewrite using `[Polynomial.Monic, Polynomial.leadingCoeff, Polynomial.natDegree_scaleRoots, Polynomial.coeff_scaleRoots_natDegree, hPm.leadingCoeff]`. Take `⟨Q, hQ, -, hQm⟩` from `Polynomial.lifts_and_degree_eq_and_monic hlifts hmonic`. Establish `hint : IsIntegral C (algebraMap A K (r ^ M) * (x : K))`.

Establish `h0 : Polynomial.aeval (algebraMap A K (r ^ M) * (x : K)) (P.scaleRoots (r ^ M)) = 0` using `Polynomial.scaleRoots_aeval_eq_zero (by rw [Polynomial.aeval_def]; exact hPx)`. Establish `h1 : IsIntegral A₀ (algebraMap A K (r ^ M) * (x : K))`. Use `⟨Q, hQm, ?_⟩` and prove the remaining obligations. Rewrite using `[← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap A, hQ]`. Conclude with `h0`.

Conclude with `isIntegral_trans (R := C) (A := A₀) _ h1`. Use `⟨M, ?_⟩` and prove the remaining obligations. Establish `: r ^ M • x = ι ⟨_, hint⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `r ^ M • (x : K) = _`.

Rewrite using `[Algebra.smul_def]`. Rewrite using `[this]`. Conclude with `hN _`.
-/
theorem exists_pow_smul_mem_of_weaklyQuasiFiniteAt
    (A : Type*) [CommRing A] [IsDomain A] [CharZero A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (d : ℕ) [Algebra (MvPolynomial (Fin d) ℤ) A]
    (hinj : Function.Injective (algebraMap (MvPolynomial (Fin d) ℤ) A))
    [Algebra.FiniteType (MvPolynomial (Fin d) ℤ) A]
    (𝔪 : Ideal A) [𝔪.IsPrime] [Algebra.WeaklyQuasiFiniteAt (MvPolynomial (Fin d) ℤ) 𝔪] :
    ∃ r ∉ 𝔪, ∃ N : Submodule A (integralClosure A K), N.FG ∧
      ∀ x : integralClosure A K, ∃ n : ℕ, r ^ n • x ∈ N := by
  classical
  set C := MvPolynomial (Fin d) ℤ
  have hZ := Algebra.ZariskisMainProperty.of_finiteType_of_weaklyQuasiFiniteAt (R := C) 𝔪
  obtain ⟨r, hr𝔪, hrint, hm⟩ := Algebra.zariskisMainProperty_iff.mp hZ
  choose m hm using hm
  let _ : Algebra C K := ((algebraMap A K).comp (algebraMap C A)).toAlgebra
  have : IsScalarTower C A K := IsScalarTower.of_algebraMap_eq' rfl
  have hinjCK : Function.Injective (algebraMap C K) := (IsFractionRing.injective A K).comp hinj
  have : FaithfulSMul C K := (faithfulSMul_iff_algebraMap_injective C K).mpr hinjCK
  let _ : Algebra (FractionRing C) K := FractionRing.liftAlgebra C K
  have hr0 : algebraMap A K r ≠ 0 := by
    rw [map_ne_zero_iff _ (IsFractionRing.injective A K)]
    exact fun h => hr𝔪 (h ▸ 𝔪.zero_mem)
  have hintK : ∀ a : A, IsIntegral C a → IsIntegral (FractionRing C) (algebraMap A K a) :=
    fun a ha => (ha.map (IsScalarTower.toAlgHom C A K)).tower_top
  have : FiniteDimensional (FractionRing C) K := by
    obtain ⟨t, ht⟩ := Algebra.FiniteType.out (R := C) (A := A)
    let T : Set K := insert (algebraMap A K r) ((fun x => algebraMap A K (r ^ m x * x)) '' t)
    have hTint : ∀ z ∈ T, IsIntegral (FractionRing C) z := by
      rintro z (rfl | ⟨x, -, rfl⟩)
      · exact hintK r hrint
      · exact hintK _ (hm x)
    have : Finite T := ((t.finite_toSet.image _).insert _).to_subtype
    have hfd := IntermediateField.finiteDimensional_adjoin hTint
    have htop : IntermediateField.adjoin (FractionRing C) T = ⊤ := by
      rw [eq_top_iff]
      rintro z -
      have hA : ∀ a : A, algebraMap A K a ∈ IntermediateField.adjoin (FractionRing C) T := by
        intro a
        have ha : a ∈ Algebra.adjoin C (t : Set A) := ht ▸ Algebra.mem_top
        induction ha using Algebra.adjoin_induction with
        | mem x hx =>
          have hr' : algebraMap A K r ∈ IntermediateField.adjoin (FractionRing C) T :=
            IntermediateField.subset_adjoin _ _ (Set.mem_insert _ _)
          have hx' : algebraMap A K (r ^ m x * x) ∈ IntermediateField.adjoin (FractionRing C) T :=
            IntermediateField.subset_adjoin _ _ (Set.mem_insert_of_mem _ ⟨x, hx, rfl⟩)
          have : algebraMap A K x = algebraMap A K (r ^ m x * x) / algebraMap A K r ^ m x := by
            rw [map_mul, map_pow, mul_div_cancel_left₀ _ (pow_ne_zero _ hr0)]
          rw [this]
          exact div_mem hx' (pow_mem hr' _)
        | algebraMap c =>
          rw [← IsScalarTower.algebraMap_apply C A K, IsScalarTower.algebraMap_apply C (FractionRing C) K]
          exact IntermediateField.algebraMap_mem _ _
        | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
        | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
      obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := A) z
      exact div_mem (hA a) (hA b)
    rw [htop] at hfd
    exact (IntermediateField.topEquiv (F := FractionRing C) (E := K)).toLinearEquiv.finiteDimensional
  have : CharZero (FractionRing C) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective C (FractionRing C))
  have : Algebra.IsSeparable (FractionRing C) K := Algebra.IsSeparable.of_integral _ _
  have : Module.Finite C (integralClosure C K) :=
    IsIntegralClosure.finite C (FractionRing C) K (integralClosure C K)
  obtain ⟨g, hg⟩ := (Module.Finite.fg_top : (⊤ : Submodule C (integralClosure C K)).FG)
  let ι : integralClosure C K → integralClosure A K := fun y => ⟨y.1, y.2.tower_top⟩
  let N : Submodule A (integralClosure A K) := Submodule.span A (ι '' g)
  have hN : ∀ y : integralClosure C K, ι y ∈ N := by
    intro y
    have hy : y ∈ Submodule.span C (g : Set (integralClosure C K)) := hg ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => exact N.zero_mem
    | add y z _ _ hy hz =>
      have : ι (y + z) = ι y + ι z := rfl
      rw [this]; exact N.add_mem hy hz
    | smul c y _ hy =>
      have : ι (c • y) = algebraMap C A c • ι y := by
        apply Subtype.ext
        change c • (y : K) = algebraMap C A c • (y : K)
        rw [Algebra.smul_def, Algebra.smul_def, ← IsScalarTower.algebraMap_apply]
      rw [this]; exact N.smul_mem _ hy
  refine ⟨r, hr𝔪, N, Submodule.fg_span (g.finite_toSet.image ι), fun x => ?_⟩
  obtain ⟨P, hPm, hPx⟩ := x.2
  set D := P.natDegree
  set M := (Finset.range (D + 1)).sup fun i => m (P.coeff i)
  let A₀ := integralClosure C A
  have hcoeff : ∀ i, IsIntegral C ((P.scaleRoots (r ^ M)).coeff i) := by
    intro i
    rw [Polynomial.coeff_scaleRoots]
    rcases lt_trichotomy i D with hi | hi | hi
    · have hmi : m (P.coeff i) ≤ M :=
        Finset.le_sup (f := fun i => m (P.coeff i)) (Finset.mem_range.mpr (by omega))
      obtain ⟨k, hk⟩ : ∃ k, D - i = k + 1 := ⟨D - i - 1, by omega⟩
      have : P.coeff i * (r ^ M) ^ (D - i) =
          (r ^ m (P.coeff i) * P.coeff i) * (r ^ (M - m (P.coeff i)) * (r ^ M) ^ k) := by
        rw [hk, pow_succ]
        rw [show (r ^ M) = r ^ m (P.coeff i) * r ^ (M - m (P.coeff i)) by
          rw [← pow_add, Nat.add_sub_cancel' hmi]]
        ring
      rw [this]
      exact (hm _).mul ((hrint.pow _).mul ((hrint.pow _).pow _))
    · rw [hi, Nat.sub_self, pow_zero, mul_one, ← Polynomial.leadingCoeff, hPm.leadingCoeff]
      exact isIntegral_one
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hi, zero_mul]
      exact isIntegral_zero
  have hlifts : P.scaleRoots (r ^ M) ∈ Polynomial.lifts (algebraMap A₀ A) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    exact ⟨⟨_, hcoeff i⟩, rfl⟩
  have hmonic : (P.scaleRoots (r ^ M)).Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff, Polynomial.natDegree_scaleRoots,
      Polynomial.coeff_scaleRoots_natDegree, hPm.leadingCoeff]
  obtain ⟨Q, hQ, -, hQm⟩ := Polynomial.lifts_and_degree_eq_and_monic hlifts hmonic
  have hint : IsIntegral C (algebraMap A K (r ^ M) * (x : K)) := by
    have h0 : Polynomial.aeval (algebraMap A K (r ^ M) * (x : K)) (P.scaleRoots (r ^ M)) = 0 :=
      Polynomial.scaleRoots_aeval_eq_zero (by rw [Polynomial.aeval_def]; exact hPx)
    have h1 : IsIntegral A₀ (algebraMap A K (r ^ M) * (x : K)) := by
      refine ⟨Q, hQm, ?_⟩
      rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap A, hQ]
      exact h0
    exact isIntegral_trans (R := C) (A := A₀) _ h1
  refine ⟨M, ?_⟩
  have : r ^ M • x = ι ⟨_, hint⟩ := by
    apply Subtype.ext
    change r ^ M • (x : K) = _
    rw [Algebra.smul_def]
  rw [this]
  exact hN _

end GroundTheory.Heights₂.Heights.Model
