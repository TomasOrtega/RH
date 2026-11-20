import Development.EtaleCohomology.EtaleSheaves.LChartPf

noncomputable section

namespace LateralTheory.E.LIdemLiftPf

open Polynomial

def IdemLiftFin (A : Type) [CommRing A] (I : Ideal A) : Prop :=
  ∀ (B : Type) [CommRing B] [Algebra A B] [Module.Finite A B]
    (ε : B ⧸ I.map (algebraMap A B)), IsIdempotentElem ε →
    ∃ e : B, IsIdempotentElem e ∧ Ideal.Quotient.mk _ e = ε

def FactLift (A : Type) [CommRing A] (I : Ideal A) : Prop :=
  ∀ (g : A[X]), g.Monic → ∀ n m : ℕ, g.map (Ideal.Quotient.mk I) = X ^ n * (X - 1) ^ m →
    ∃ P Q : A[X], P.Monic ∧ Q.Monic ∧ g = P * Q ∧
      P.map (Ideal.Quotient.mk I) = X ^ n ∧ Q.map (Ideal.Quotient.mk I) = (X - 1) ^ m

def LFact : Prop := ∀ (A : Type) [CommRing A] (I : Ideal A) [HenselianRing A I], FactLift A I

def LFinOfFact : Prop := ∀ (A : Type) [CommRing A] (I : Ideal A), I ≤ Ideal.jacobson ⊥ →
  FactLift A I → IdemLiftFin A I

def LRed : Prop := ∀ (A : Type) [CommRing A] (I : Ideal A), IdemLiftFin A I →
  LateralTheory.E.LChartPf.IdemLiftInt A I

/- English proof (translation)
Establish `hx : x * x = x * (x + y)` using `by rw [mul_add, hxy, add_zero]`. Establish `h1 : (x + y) * (hu.unit⁻¹ : Bˣ) = 1` using `hu.mul_val_inv`. Unfold `IsIdempotentElem`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem idem_of_mul_eq_zero {B : Type} [CommRing B] (x y : B) (hxy : x * y = 0) (hu : IsUnit (x + y)) :
    IsIdempotentElem (x * hu.unit⁻¹) := by
  have hx : x * x = x * (x + y) := by rw [mul_add, hxy, add_zero]
  have h1 : (x + y) * (hu.unit⁻¹ : Bˣ) = 1 := hu.mul_val_inv
  unfold IsIdempotentElem
  calc x * ↑hu.unit⁻¹ * (x * ↑hu.unit⁻¹) = x * x * (↑hu.unit⁻¹ * ↑hu.unit⁻¹) := by ring
    _ = x * ((x + y) * ↑hu.unit⁻¹) * ↑hu.unit⁻¹ := by rw [hx]; ring
    _ = x * ↑hu.unit⁻¹ := by rw [h1, mul_one]

/- English proof (translation)
Introduce `A _ I hfin B _ _ _ ε hε`. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective ε`. Establish `hb : b * b - b ∈ I.map (algebraMap A B)`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hε.eq, sub_self]`. Rewrite `hb` using `[Ideal.map, Submodule.mem_span_set']`.

Take `⟨n, f, g, hfg⟩` from `hb`. Use `choose a ha hag using fun i => (g i).2`. Set `C : Subalgebra A B` to `Algebra.adjoin A (insert b (Set.range f))`. Establish `hC : Module.Finite A C`. Use `Algebra.finite_adjoin_of_finite_of_isIntegral (R := A) (s := insert b (Set.range f)) ((Set.finite_range f).insert b) (fun x _ => Algebra.IsIntegral.isIntegral x)` as an intermediate fact.

Conclude with `this`. Establish `hbC : b ∈ C` using `Algebra.subset_adjoin (Set.mem_insert _ _)`. Establish `hfC : ∀ i, f i ∈ C` using `fun i => Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨i, rfl⟩)`. Set `bC : C` to `⟨b, hbC⟩`. Establish `hmem : bC * bC - bC ∈ I.map (algebraMap A C)`.

Establish `: bC * bC - bC = ∑ i, (⟨f i, hfC i⟩ : C) * algebraMap A C (a i)`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [bC, Subalgebra.coe_sub, Subalgebra.coe_mul, ← hfg, smul_eq_mul]`. Use `push_cast`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[← hag i]`. Rewrite using `[this]`. Conclude with `Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (ha i))`. Establish `hidC : IsIdempotentElem (Ideal.Quotient.mk (I.map (algebraMap A C)) bC)`. Unfold `IsIdempotentElem`.

Rewrite using `[← map_mul, Ideal.Quotient.eq]`. Conclude with `hmem`. Take `⟨e, he, hee⟩` from `hfin C _ hidC`. Use `⟨(e : B), ?_, ?_⟩` and prove the remaining obligations. Unfold `IsIdempotentElem`.

Conclude with `congrArg Subtype.val he.eq`. Rewrite `hee`, the goal using `[Ideal.Quotient.eq]`. Use `Ideal.mem_map_of_mem (C.val : C →ₐ[A] B).toRingHom hee` as an intermediate fact. Rewrite `this` using `[Ideal.map_map]`. Simplify `this` using `[bC]`.
-/
theorem lRed : LRed := by
  intro A _ I hfin B _ _ _ ε hε
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective ε
  have hb : b * b - b ∈ I.map (algebraMap A B) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hε.eq, sub_self]
  rw [Ideal.map, Submodule.mem_span_set'] at hb
  obtain ⟨n, f, g, hfg⟩ := hb
  choose a ha hag using fun i => (g i).2
  let C : Subalgebra A B := Algebra.adjoin A (insert b (Set.range f))
  have hC : Module.Finite A C := by
    have := Algebra.finite_adjoin_of_finite_of_isIntegral (R := A) (s := insert b (Set.range f))
      ((Set.finite_range f).insert b) (fun x _ => Algebra.IsIntegral.isIntegral x)
    exact this
  have hbC : b ∈ C := Algebra.subset_adjoin (Set.mem_insert _ _)
  have hfC : ∀ i, f i ∈ C := fun i => Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨i, rfl⟩)
  let bC : C := ⟨b, hbC⟩
  have hmem : bC * bC - bC ∈ I.map (algebraMap A C) := by
    have : bC * bC - bC = ∑ i, (⟨f i, hfC i⟩ : C) * algebraMap A C (a i) := by
      apply Subtype.ext
      simp only [bC, Subalgebra.coe_sub, Subalgebra.coe_mul, ← hfg, smul_eq_mul]
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hag i]
    rw [this]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (ha i))
  have hidC : IsIdempotentElem (Ideal.Quotient.mk (I.map (algebraMap A C)) bC) := by
    unfold IsIdempotentElem
    rw [← map_mul, Ideal.Quotient.eq]; exact hmem
  obtain ⟨e, he, hee⟩ := hfin C _ hidC
  refine ⟨(e : B), ?_, ?_⟩
  · unfold IsIdempotentElem; exact congrArg Subtype.val he.eq
  · rw [Ideal.Quotient.eq] at hee ⊢
    have := Ideal.mem_map_of_mem (C.val : C →ₐ[A] B).toRingHom hee
    rw [Ideal.map_map] at this
    simpa [bC] using this

/- English proof (translation)
Set `φ : Module.End A B` to `LinearMap.mulLeft A (b * b - b)`. Establish `hφ : LinearMap.range φ ≤ I • (⊤ : Submodule A B)`. Introduce and unpack `_ ⟨y, rfl⟩`. Rewrite using `[Ideal.smul_top_eq_map]`. Conclude with `Ideal.mul_mem_right _ _ hb`.

Take `⟨p, hpm, -, hpc, hpφ⟩` from `LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero A φ I hφ`. Establish `hp0 : aeval (b * b - b) p = 0`. Establish `hφ' : φ = Algebra.lmul A B (b * b - b)` using `rfl`. Rewrite `hpφ` using `[hφ', Polynomial.aeval_algHom_apply]`. Simplify using `using congrArg (fun ψ : Module.End A B => ψ 1) hpφ`.

Establish `hpmap : p.map (Ideal.Quotient.mk I) = X ^ p.natDegree`. Use extensionality with `k`. Rewrite using `[coeff_map, coeff_X_pow]`. Use `split_ifs with hk`. Substitute `hk` using the available equality.

Rewrite using `[hpm.coeff_natDegree, map_one]`. Break down `lt_or_gt_of_ne hk with h | h` into its components or cases. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `Ideal.pow_le_self (by omega) (hpc k)`. Rewrite using `[coeff_eq_zero_of_natDegree_lt h, map_zero]`.

Break down `subsingleton_or_nontrivial A with hA | hA` into its components or cases. Establish `h10 : (1 : B) = 0` using `by rw [← map_one (algebraMap A B), Subsingleton.elim (1 : A) 0, map_zero]`. Establish `: Subsingleton B` using `subsingleton_of_zero_eq_one h10.symm`. Establish `h10' : (1 : A ⧸ I) = 0` using `by rw [← map_one (Ideal.Quotient.mk I), Subsingleton.elim (1 : A) 0, map_zero]`. Establish `: Subsingleton (A ⧸ I)` using `subsingleton_of_zero_eq_one h10'.symm`.

Conclude with `⟨p, 0, hpm, Subsingleton.elim _ _, Subsingleton.elim _ _⟩`. Establish `hqm : (X * X - X : A[X]).Monic`. Rewrite using `[show (X * X - X : A[X]) = X ^ 2 - X by ring]`. Conclude with `monic_X_pow_sub (by rw [degree_X]; exact_mod_cast (by norm_num : 1 < 2))`. Establish `hq : (X * X - X : A[X]).natDegree = 2`.

Rewrite using `[show (X * X - X : A[X]) = X ^ 2 - X by ring]`. Use `compute_degree!`. Use `⟨p.comp (X * X - X) * (X * X - X), p.natDegree, (hpm.comp hqm (by omega)).mul hqm, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, aeval_comp]`. Simplify using `[hp0]`.

Simplify using `only [Polynomial.map_mul, map_comp, hpmap, X_pow_comp, Polynomial.map_sub, map_X]`. Rewrite using `[show (X * X - X : (A ⧸ I)[X]) = X * (X - 1) by ring, mul_pow]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_monic_of_idem_mod {A : Type} [CommRing A] (I : Ideal A) (B : Type) [CommRing B] [Algebra A B]
    [Module.Finite A B] (b : B) (hb : b * b - b ∈ I.map (algebraMap A B)) :
    ∃ (g : A[X]) (d : ℕ), g.Monic ∧ aeval b g = 0 ∧
      g.map (Ideal.Quotient.mk I) = X ^ (d + 1) * (X - 1) ^ (d + 1) := by
  let φ : Module.End A B := LinearMap.mulLeft A (b * b - b)
  have hφ : LinearMap.range φ ≤ I • (⊤ : Submodule A B) := by
    rintro _ ⟨y, rfl⟩
    rw [Ideal.smul_top_eq_map]
    exact Ideal.mul_mem_right _ _ hb
  obtain ⟨p, hpm, -, hpc, hpφ⟩ :=
    LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero A φ I hφ
  have hp0 : aeval (b * b - b) p = 0 := by
    have hφ' : φ = Algebra.lmul A B (b * b - b) := rfl
    rw [hφ', Polynomial.aeval_algHom_apply] at hpφ
    simpa using congrArg (fun ψ : Module.End A B => ψ 1) hpφ
  have hpmap : p.map (Ideal.Quotient.mk I) = X ^ p.natDegree := by
    ext k
    rw [coeff_map, coeff_X_pow]
    split_ifs with hk
    · subst hk; rw [hpm.coeff_natDegree, map_one]
    · rcases lt_or_gt_of_ne hk with h | h
      · rw [Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.pow_le_self (by omega) (hpc k)
      · rw [coeff_eq_zero_of_natDegree_lt h, map_zero]
  rcases subsingleton_or_nontrivial A with hA | hA
  · have h10 : (1 : B) = 0 := by rw [← map_one (algebraMap A B), Subsingleton.elim (1 : A) 0, map_zero]
    have : Subsingleton B := subsingleton_of_zero_eq_one h10.symm
    have h10' : (1 : A ⧸ I) = 0 := by rw [← map_one (Ideal.Quotient.mk I), Subsingleton.elim (1 : A) 0, map_zero]
    have : Subsingleton (A ⧸ I) := subsingleton_of_zero_eq_one h10'.symm
    exact ⟨p, 0, hpm, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  have hqm : (X * X - X : A[X]).Monic := by
    rw [show (X * X - X : A[X]) = X ^ 2 - X by ring]
    exact monic_X_pow_sub (by rw [degree_X]; exact_mod_cast (by norm_num : 1 < 2))
  have hq : (X * X - X : A[X]).natDegree = 2 := by
    rw [show (X * X - X : A[X]) = X ^ 2 - X by ring]
    compute_degree!
  refine ⟨p.comp (X * X - X) * (X * X - X), p.natDegree, (hpm.comp hqm (by omega)).mul hqm, ?_, ?_⟩
  · rw [map_mul, aeval_comp]; simp [hp0]
  · simp only [Polynomial.map_mul, map_comp, hpmap, X_pow_comp, Polynomial.map_sub, map_X]
    rw [show (X * X - X : (A ⧸ I)[X]) = X * (X - 1) by ring, mul_pow]
    ring

/- English proof (translation)
Establish `h1 : f - f' ∈ Ideal.map (C : A →+* A[X]) I`. Rewrite using `[← Ideal.mk_ker (I := I), ← Polynomial.ker_mapRingHom, RingHom.mem_ker, map_sub]`. Simplify using `only [coe_mapRingHom, h, sub_self]`. Establish `h2` using `Ideal.mem_map_of_mem (aeval b).toRingHom h1`. Rewrite `h2` using `[Ideal.map_map]`.

Establish `h3 : (aeval b).toRingHom.comp (C : A →+* A[X]) = algebraMap A B` using `by ext; simp`. Rewrite `h2` using `[h3]`. Simplify using `using h2`.
-/
theorem aeval_sub_mem_of_map_eq {A : Type} [CommRing A] (I : Ideal A) {B : Type} [CommRing B] [Algebra A B]
    (f f' : A[X]) (h : f.map (Ideal.Quotient.mk I) = f'.map (Ideal.Quotient.mk I)) (b : B) :
    aeval b f - aeval b f' ∈ I.map (algebraMap A B) := by
  have h1 : f - f' ∈ Ideal.map (C : A →+* A[X]) I := by
    rw [← Ideal.mk_ker (I := I), ← Polynomial.ker_mapRingHom, RingHom.mem_ker, map_sub]
    simp only [coe_mapRingHom, h, sub_self]
  have h2 := Ideal.mem_map_of_mem (aeval b).toRingHom h1
  rw [Ideal.map_map] at h2
  have h3 : (aeval b).toRingHom.comp (C : A →+* A[X]) = algebraMap A B := by ext; simp
  rw [h3] at h2
  simpa using h2

/- English proof (translation)
Establish `key : (⊤ : Submodule A B) ≤ (Ideal.span {s}).restrictScalars A`. Use `Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hI ?_` and prove the remaining obligations. Introduce `y _`. Establish `hy : y = s * y - (s - 1) * y` using `by ring`. Rewrite using `[hy]`.

Use `Submodule.sub_mem_sup (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)) ?_` and prove the remaining obligations. Rewrite using `[Ideal.smul_top_eq_map]`. Conclude with `Ideal.mul_mem_right _ _ hs`. Establish `h1 : (1 : B) ∈ Ideal.span {s}` using `key Submodule.mem_top`. Rewrite `h1` using `[Ideal.mem_span_singleton]`.

Conclude with `isUnit_of_dvd_one h1`.
-/
theorem isUnit_one_add_of_finite {A : Type} [CommRing A] (I : Ideal A) (hI : I ≤ Ideal.jacobson ⊥)
    {B : Type} [CommRing B] [Algebra A B] [Module.Finite A B] (s : B)
    (hs : s - 1 ∈ I.map (algebraMap A B)) : IsUnit s := by
  have key : (⊤ : Submodule A B) ≤ (Ideal.span {s}).restrictScalars A := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hI ?_
    intro y _
    have hy : y = s * y - (s - 1) * y := by ring
    rw [hy]
    refine Submodule.sub_mem_sup (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)) ?_
    rw [Ideal.smul_top_eq_map]
    exact Ideal.mul_mem_right _ _ hs
  have h1 : (1 : B) ∈ Ideal.span {s} := key Submodule.mem_top
  rw [Ideal.mem_span_singleton] at h1
  exact isUnit_of_dvd_one h1

/- English proof (translation)
Introduce `A _ I hI hF B _ _ _ ε hε`. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective ε`. Use `set π := Ideal.Quotient.mk (I.map (algebraMap A B))`. Establish `hb : b * b - b ∈ I.map (algebraMap A B)`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hε.eq, sub_self]`.

Take `⟨g, d, hgm, hgb, hgmap⟩` from `exists_monic_of_idem_mod I B b hb`. Take `⟨P, Q, -, -, hPQ, hP, hQ⟩` from `hF g hgm _ _ hgmap`. Establish `hcop : IsCoprime (X ^ (d + 1) : (A ⧸ I)[X]) ((X - 1) ^ (d + 1))` using `(show IsCoprime (X : (A ⧸ I)[X]) (X - 1) from ⟨1, -1, by ring⟩).pow`. Take `⟨u0, v0, huv0⟩` from `hcop`. Take `⟨u, rfl⟩` from `Polynomial.map_surjective _ Ideal.Quotient.mk_surjective u0`.

Take `⟨v, rfl⟩` from `Polynomial.map_surjective _ Ideal.Quotient.mk_surjective v0`. Establish `hπ : ∀ f f' : A[X], f.map (Ideal.Quotient.mk I) = f'.map (Ideal.Quotient.mk I) → π (aeval b f) = π (aeval b f')` using `fun f f' h => Ideal.Quotient.eq.2 (aeval_sub_mem_of_map_eq I f f' h b)`. Establish `hPb : π (aeval b P) = π b ^ (d + 1)`. Rewrite using `[hπ P (X ^ (d + 1)) (by rw [hP]; simp)]; simp`. Establish `hQb : π (aeval b Q) = (π b - 1) ^ (d + 1)`.

Rewrite using `[hπ Q ((X - 1) ^ (d + 1)) (by rw [hQ]; simp)]; simp`. Establish `hUb : π (aeval b (u * P)) + π (aeval b (v * Q)) = 1`. Rewrite using `[← map_add, ← map_add, hπ (u * P + v * Q) 1 (by simp [Polynomial.map_add, Polynomial.map_mul, hP, hQ, huv0])]`. Simplify using the standard rewrite rules. Use `set x := aeval b (u * P)`.

Use `set y := aeval b (v * Q)`. Establish `hxy : x * y = 0`. Simplify using `only [x, y, ← map_mul]`. Rewrite using `[show u * P * (v * Q) = u * v * g by rw [hPQ]; ring, map_mul, hgb, mul_zero]`. Establish `hs : (x + y) - 1 ∈ I.map (algebraMap A B)`.

Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_add, hUb, map_one, sub_self]`. Establish `hu` using `isUnit_one_add_of_finite I hI (x + y) hs`. Use `⟨x * hu.unit⁻¹, idem_of_mul_eq_zero x y hxy hu, ?_⟩` and prove the remaining obligations. Establish `hinv : π (hu.unit⁻¹ : Bˣ) = 1`. Establish `h1 : π (x + y) * π (hu.unit⁻¹ : Bˣ) = 1` using `by rw [← map_mul, hu.mul_val_inv, map_one]`.

Rewrite `h1` using `[map_add, hUb, one_mul]`. Then use the resulting hypothesis. Establish `he : π b * π b = π b` using `hε.eq`. Establish `hx : π x = π b`. Establish `e1 : π x * (1 - π b) = 0`. Simplify using `only [x, map_mul, hPb]`.

Rewrite using `[pow_succ, mul_assoc, mul_assoc, mul_sub, mul_one, he, sub_self, mul_zero, mul_zero]`. Establish `e2 : π y * π b = 0`. Simplify using `only [y, map_mul, hQb]`. Rewrite using `[pow_succ, mul_assoc, mul_assoc, sub_mul, he, one_mul, sub_self, mul_zero, mul_zero]`. Establish `e3 : π x = π x * π b` using `by linear_combination e1`.

Rewrite using `[e3]`. Take the linear combination `(π b) * hUb - e2`. Rewrite using `[map_mul, hinv, mul_one, hx]`.
-/
theorem lFinOfFact : LFinOfFact := by
  intro A _ I hI hF B _ _ _ ε hε
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective ε
  set π := Ideal.Quotient.mk (I.map (algebraMap A B))
  have hb : b * b - b ∈ I.map (algebraMap A B) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hε.eq, sub_self]
  obtain ⟨g, d, hgm, hgb, hgmap⟩ := exists_monic_of_idem_mod I B b hb
  obtain ⟨P, Q, -, -, hPQ, hP, hQ⟩ := hF g hgm _ _ hgmap
  have hcop : IsCoprime (X ^ (d + 1) : (A ⧸ I)[X]) ((X - 1) ^ (d + 1)) :=
    (show IsCoprime (X : (A ⧸ I)[X]) (X - 1) from ⟨1, -1, by ring⟩).pow
  obtain ⟨u0, v0, huv0⟩ := hcop
  obtain ⟨u, rfl⟩ := Polynomial.map_surjective _ Ideal.Quotient.mk_surjective u0
  obtain ⟨v, rfl⟩ := Polynomial.map_surjective _ Ideal.Quotient.mk_surjective v0
  have hπ : ∀ f f' : A[X], f.map (Ideal.Quotient.mk I) = f'.map (Ideal.Quotient.mk I) →
      π (aeval b f) = π (aeval b f') := fun f f' h =>
    Ideal.Quotient.eq.2 (aeval_sub_mem_of_map_eq I f f' h b)
  have hPb : π (aeval b P) = π b ^ (d + 1) := by
    rw [hπ P (X ^ (d + 1)) (by rw [hP]; simp)]; simp
  have hQb : π (aeval b Q) = (π b - 1) ^ (d + 1) := by
    rw [hπ Q ((X - 1) ^ (d + 1)) (by rw [hQ]; simp)]; simp
  have hUb : π (aeval b (u * P)) + π (aeval b (v * Q)) = 1 := by
    rw [← map_add, ← map_add, hπ (u * P + v * Q) 1 (by simp [Polynomial.map_add, Polynomial.map_mul, hP, hQ, huv0])]
    simp
  set x := aeval b (u * P)
  set y := aeval b (v * Q)
  have hxy : x * y = 0 := by
    simp only [x, y, ← map_mul]
    rw [show u * P * (v * Q) = u * v * g by rw [hPQ]; ring, map_mul, hgb, mul_zero]
  have hs : (x + y) - 1 ∈ I.map (algebraMap A B) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_add, hUb, map_one, sub_self]
  have hu := isUnit_one_add_of_finite I hI (x + y) hs
  refine ⟨x * hu.unit⁻¹, idem_of_mul_eq_zero x y hxy hu, ?_⟩
  have hinv : π (hu.unit⁻¹ : Bˣ) = 1 := by
    have h1 : π (x + y) * π (hu.unit⁻¹ : Bˣ) = 1 := by rw [← map_mul, hu.mul_val_inv, map_one]
    rwa [map_add, hUb, one_mul] at h1
  have he : π b * π b = π b := hε.eq
  have hx : π x = π b := by
    have e1 : π x * (1 - π b) = 0 := by
      simp only [x, map_mul, hPb]
      rw [pow_succ, mul_assoc, mul_assoc, mul_sub, mul_one, he, sub_self, mul_zero, mul_zero]
    have e2 : π y * π b = 0 := by
      simp only [y, map_mul, hQb]
      rw [pow_succ, mul_assoc, mul_assoc, sub_mul, he, one_mul, sub_self, mul_zero, mul_zero]
    have e3 : π x = π x * π b := by linear_combination e1
    rw [e3]; linear_combination (π b) * hUb - e2
  rw [map_mul, hinv, mul_one, hx]

/- English proof (translation)
Introduce `A _ I _`. Conclude with `lRed A I (lFinOfFact A I HenselianRing.jac (h1 A I))`.
-/
theorem LIdemLift_of (h1 : LFact) : LateralTheory.E.LChartPf.LIdemLift := by
  intro A _ I _
  exact lRed A I (lFinOfFact A I HenselianRing.jac (h1 A I))

end LateralTheory.E.LIdemLiftPf
