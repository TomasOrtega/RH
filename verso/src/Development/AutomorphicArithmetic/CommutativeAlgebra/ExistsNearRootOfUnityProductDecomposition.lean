import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.GoodRoot
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsFactorizationNearRootOfUnityHenselian
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsTwoChartAdjoinRootLaurent
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsMonicLaurentPolynomialNearRootOfUnity
import Development.AutomorphicArithmetic.CommutativeAlgebra.RootsOfUnityLiftModNilpotentUnique

noncomputable section
open IsLocalRing UpperTheory.Et

/- English proof (translation)
Simplify using `[mm, Algebra.top_toSubmodule, Ideal.smul_top_eq_map]`.
-/
private lemma mem_mm_top_iff {A D : Type} [CommRing A] [IsLocalRing A] [CommRing D] [Algebra A D] (x : D) :
    x ∈ mm (⊤ : Subalgebra A D) ↔ x ∈ (maximalIdeal A).map (algebraMap A D) := by
  simp [mm, Algebra.top_toSubmodule, Ideal.smul_top_eq_map]

/- English proof (translation)
Unfold `mm at hx ⊢`. Conclude with `Submodule.smul_induction_on (p := fun z => ψ z ∈ maximalIdeal A • Subalgebra.toSubmodule B) hx (fun r hr y hy => by`. Rewrite using `[AlgHom.map_smul_of_tower]`. Conclude with `Submodule.smul_mem_smul hr (h y hy))`. Use the proof step `(fun a b ha hb => by`.

Rewrite using `[map_add]`. Conclude with `add_mem ha hb)`.
-/
private lemma mm_map {A E D : Type} [CommRing A] [IsLocalRing A] [CommRing E] [Algebra A E] [CommRing D] [Algebra A D]
    (ψ : E →ₐ[A] D) (B₀ : Subalgebra A E) (B : Subalgebra A D) (h : ∀ x ∈ B₀, ψ x ∈ B) {x : E}
    (hx : x ∈ mm B₀) : ψ x ∈ mm B := by
  unfold mm at hx ⊢
  exact Submodule.smul_induction_on (p := fun z => ψ z ∈ maximalIdeal A • Subalgebra.toSubmodule B) hx
    (fun r hr y hy => by
      rw [AlgHom.map_smul_of_tower]
      exact Submodule.smul_mem_smul hr (h y hy))
    (fun a b ha hb => by
      rw [map_add]
      exact add_mem ha hb)

/- English proof (translation)
Introduce `x hx`. Conclude with `(Algebra.adjoin_le (S := B.comap ψ) h) hx`.
-/
private lemma adjoin_map {A E D : Type} [CommRing A] [CommRing E] [Algebra A E] [CommRing D] [Algebra A D]
    (ψ : E →ₐ[A] D) (S : Set E) (B : Subalgebra A D) (h : ∀ x ∈ S, ψ x ∈ B) :
    ∀ x ∈ Algebra.adjoin A S, ψ x ∈ B := by
  intro x hx
  exact (Algebra.adjoin_le (S := B.comap ψ) h) hx

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `p hp hdeg hx`. Rewrite `hx` using `[Polynomial.eq_one_of_monic_natDegree_zero hp hdeg]`.

Simplify using `at hx`. Consider the case `succ n ih`. Introduce `p hp hdeg hx`. Take `⟨a, ha⟩` from `h p hp (by omega)`. Establish `hfac` using `(Polynomial.mul_divByMonic_eq_iff_isRoot (p := p) (a := a)).mpr ha`.

Establish `hmX : (Polynomial.X - Polynomial.C a).Monic` using `Polynomial.monic_X_sub_C a`. Establish `hp' : ((Polynomial.X - Polynomial.C a) * (p /ₘ (Polynomial.X - Polynomial.C a))).Monic`. Rewrite using `[hfac]`. Conclude with `hp`. Establish `hmq : (p /ₘ (Polynomial.X - Polynomial.C a)).Monic` using `hmX.of_mul_monic_left hp'`.

Establish `hdq : (p /ₘ (Polynomial.X - Polynomial.C a)).natDegree = n`. Use `hmX.natDegree_mul hmq` as an intermediate fact. Rewrite `this` using `[hfac, hdeg, Polynomial.natDegree_X_sub_C]`. Use linear arithmetic over natural numbers and integers. Rewrite `hx` using `[← hfac, Polynomial.eval₂_mul]`.

Break down `mul_eq_zero.mp hx with h1 | h1` into its components or cases. Use `⟨a, ?_⟩` and prove the remaining obligations. Simplify using `[sub_eq_zero] at h1`. Conclude with `h1.symm`. Conclude with `ih _ hmq hdq h1`.
-/
private lemma root_mem {S K : Type} [CommRing S] [Nontrivial S] [CommRing K] [IsDomain K] (f : S →+* K)
    (h : ∀ p : Polynomial S, p.Monic → 0 < p.natDegree → ∃ a, p.eval a = 0) (x : K) :
    ∀ (n : ℕ) (p : Polynomial S), p.Monic → p.natDegree = n → p.eval₂ f x = 0 → ∃ a : S, f a = x := by
  intro n
  induction n with
  | zero =>
    intro p hp hdeg hx
    rw [Polynomial.eq_one_of_monic_natDegree_zero hp hdeg] at hx
    simp at hx
  | succ n ih =>
    intro p hp hdeg hx
    obtain ⟨a, ha⟩ := h p hp (by omega)
    have hfac := (Polynomial.mul_divByMonic_eq_iff_isRoot (p := p) (a := a)).mpr ha
    have hmX : (Polynomial.X - Polynomial.C a).Monic := Polynomial.monic_X_sub_C a
    have hp' : ((Polynomial.X - Polynomial.C a) * (p /ₘ (Polynomial.X - Polynomial.C a))).Monic := by
      rw [hfac]
      exact hp
    have hmq : (p /ₘ (Polynomial.X - Polynomial.C a)).Monic := hmX.of_mul_monic_left hp'
    have hdq : (p /ₘ (Polynomial.X - Polynomial.C a)).natDegree = n := by
      have := hmX.natDegree_mul hmq
      rw [hfac, hdeg, Polynomial.natDegree_X_sub_C] at this
      omega
    rw [← hfac, Polynomial.eval₂_mul] at hx
    rcases mul_eq_zero.mp hx with h1 | h1
    · refine ⟨a, ?_⟩
      simp [sub_eq_zero] at h1
      exact h1.symm
    · exact ih _ hmq hdq h1

/- English proof (translation)
Distinguish the cases in `hb : b = 0`. Substitute `hb` using the available equality. Use `⟨1, one_mem _, one_pow _, ?_⟩` and prove the remaining obligations. Simplify using `[zero_pow hq.ne', pow_eq_zero_iff hq.ne'] at h`. Simplify using `[h]`.

Establish `hinj` using `IsFractionRing.injective D (FractionRing D)`. Establish `hbK : algebraMap D (FractionRing D) b ≠ 0` using `(map_ne_zero_iff _ hinj).mpr hb`. Establish `hbq : algebraMap D (FractionRing D) (b ^ q) ≠ 0` using `(map_ne_zero_iff _ hinj).mpr (pow_ne_zero q hb)`. Take `⟨η, hη⟩` from `root_mem ((algebraMap D (FractionRing D)).comp C.val.toRingHom) hC (algebraMap D (FractionRing D) a / algebraMap D (FractionRing D) b) q (Polynomial.X ^ q - Polynomial.C 1) (Polynomial.monic_X_pow_sub_C 1 hq.ne') (Polynomial.natDegree_X_pow_sub_C) (by simp [div_pow, ← map_pow, h, …`. Establish `hη' : algebraMap D (FractionRing D) (η : D) = algebraMap D (FractionRing D) a / algebraMap D (FractionRing D) b` using `hη`.

Use `⟨η, η.2, ?_, ?_⟩` and prove the remaining obligations. Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_pow, map_one, hη', div_pow, ← map_pow, ← map_pow, h, div_self hbq]`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_mul, hη', div_mul_cancel₀ _ hbK]`.
-/
private lemma unity_ratio {A D : Type} [CommRing A] [CommRing D] [IsDomain D] [Algebra A D]
    (C : Subalgebra A D) (hC : Roots C) (q : ℕ) (hq : 0 < q) (a b : D) (h : a ^ q = b ^ q) :
    ∃ η ∈ C, η ^ q = 1 ∧ a = η * b := by
  by_cases hb : b = 0
  · subst hb
    refine ⟨1, one_mem _, one_pow _, ?_⟩
    simp [zero_pow hq.ne', pow_eq_zero_iff hq.ne'] at h
    simp [h]
  · have hinj := IsFractionRing.injective D (FractionRing D)
    have hbK : algebraMap D (FractionRing D) b ≠ 0 := (map_ne_zero_iff _ hinj).mpr hb
    have hbq : algebraMap D (FractionRing D) (b ^ q) ≠ 0 := (map_ne_zero_iff _ hinj).mpr (pow_ne_zero q hb)
    obtain ⟨η, hη⟩ := root_mem ((algebraMap D (FractionRing D)).comp C.val.toRingHom) hC
      (algebraMap D (FractionRing D) a / algebraMap D (FractionRing D) b) q
      (Polynomial.X ^ q - Polynomial.C 1) (Polynomial.monic_X_pow_sub_C 1 hq.ne')
      (Polynomial.natDegree_X_pow_sub_C)
      (by simp [div_pow, ← map_pow, h, div_self hbq])
    have hη' : algebraMap D (FractionRing D) (η : D) = algebraMap D (FractionRing D) a / algebraMap D (FractionRing D) b := hη
    refine ⟨η, η.2, ?_, ?_⟩
    · apply hinj
      rw [map_pow, map_one, hη', div_pow, ← map_pow, ← map_pow, h, div_self hbq]
    · apply hinj
      rw [map_mul, hη', div_mul_cancel₀ _ hbK]

/- English proof (translation)
Take `⟨a, ha⟩` from `hS (Polynomial.X ^ q - Polynomial.C ⟨c, hc⟩) (Polynomial.monic_X_pow_sub_C _ hq.ne') (by rw [Polynomial.natDegree_X_pow_sub_C]; exact hq)`. Use `⟨a, a.2, ?_⟩` and prove the remaining obligations. Simplify using `only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at ha`. Use `congrArg Subtype.val (sub_eq_zero.mp ha)` as an intermediate fact. Simplify using `using this`.
-/
private lemma qth_root {A D : Type} [CommRing A] [CommRing D] [IsDomain D] [Algebra A D]
    (S : Subalgebra A D) (hS : Roots S) (q : ℕ) (hq : 0 < q) (c : D) (hc : c ∈ S) :
    ∃ u ∈ S, u ^ q = c := by
  obtain ⟨a, ha⟩ := hS (Polynomial.X ^ q - Polynomial.C ⟨c, hc⟩) (Polynomial.monic_X_pow_sub_C _ hq.ne')
    (by rw [Polynomial.natDegree_X_pow_sub_C]; exact hq)
  refine ⟨a, a.2, ?_⟩
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at ha
  have := congrArg Subtype.val (sub_eq_zero.mp ha)
  simpa using this

/- English proof (translation)
Establish `key : (AdjoinRoot.root P ^ q - 1) ^ n = -((P - (Polynomial.X ^ q - 1) ^ n).eval₂ (AdjoinRoot.of P) (AdjoinRoot.root P))`. Simplify using `[Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_one, AdjoinRoot.eval₂_root]`. Rewrite using `[key, Polynomial.eval₂_eq_sum_range]`. Use `neg_mem (sum_mem fun i _ => ?_)` and prove the remaining obligations. Apply `Ideal.mul_mem_right` to reduce the goal to its premises.

Establish `hm` using `Ideal.mem_map_of_mem (AdjoinRoot.of P) (hP i)`. Rewrite `hm` using `[Ideal.map_map, ← AdjoinRoot.algebraMap_eq, ← IsScalarTower.algebraMap_eq]`. Then use the resulting hypothesis.
-/
private lemma pow_root_mem {A : Type} [CommRing A] [IsLocalRing A] (P : Polynomial (LaurentPolynomial A))
    (q n : ℕ)
    (hP : ∀ i, (P - (Polynomial.X ^ q - 1) ^ n).coeff i ∈ (maximalIdeal A).map (algebraMap A (LaurentPolynomial A))) :
    (AdjoinRoot.root P ^ q - 1) ^ n ∈ (maximalIdeal A).map (algebraMap A (AdjoinRoot P)) := by
  have key : (AdjoinRoot.root P ^ q - 1) ^ n =
      -((P - (Polynomial.X ^ q - 1) ^ n).eval₂ (AdjoinRoot.of P) (AdjoinRoot.root P)) := by
    simp [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_one, AdjoinRoot.eval₂_root]
  rw [key, Polynomial.eval₂_eq_sum_range]
  refine neg_mem (sum_mem fun i _ => ?_)
  apply Ideal.mul_mem_right
  have hm := Ideal.mem_map_of_mem (AdjoinRoot.of P) (hP i)
  rwa [Ideal.map_map, ← AdjoinRoot.algebraMap_eq, ← IsScalarTower.algebraMap_eq] at hm

/- English proof (translation)
The claim follows from `AdjoinRoot.liftAlgHom_of P φ w h z`.
-/
private theorem adjoinRoot_liftAlgHom_of_laurent {A D : Type} [CommRing A] [CommRing D] [Algebra A D]
    {P : Polynomial (LaurentPolynomial A)} (φ : LaurentPolynomial A →ₐ[A] D) (w : D)
    (h : Polynomial.eval₂ φ.toRingHom w P = 0) (z : LaurentPolynomial A) :
    AdjoinRoot.liftAlgHom P φ w h (AdjoinRoot.of P z) = φ z :=
  AdjoinRoot.liftAlgHom_of P φ w h z

/- English proof (translation)
Introduce `A D _ _ _ _ _ T hInt hB hC q hq w hw`. Establish `hq0 : 0 < q`. Break down `Nat.eq_zero_or_pos q with h0 | h0` into its components or cases. Substitute `h0` using the available equality. Simplify using `at hq`.

Conclude with `h0`. Establish `hmono : ∀ (S : Subalgebra A D) (x : D), x ∈ mm S → x ∈ mm (⊤ : Subalgebra A D)` using `fun S x hx => mm_map (AlgHom.id A D) S ⊤ (fun _ _ => Algebra.mem_top) hx`. Take `⟨φ, P, n, hφt, hφs, hPm, hPw, hPc⟩` from `UpperTheory.exists_monic_laurent_polynomial_near_root_of_unity A D T hInt q hq0 w hw`. Take `⟨kB, hkB⟩` from `T.locB w`. Take `⟨kC, hkC⟩` from `T.locC w`.

Take `⟨k, hk, T', hFin, hCoord, ht', hs', hB', hC'⟩` from `UpperTheory.exists_twoChart_adjoinRoot_laurent A P hPm (max kB kC)`. Set `ψ : AdjoinRoot P →ₐ[A] D` to `AdjoinRoot.liftAlgHom P φ w hPw`. Establish `hψr : ψ (AdjoinRoot.root P) = w` using `AdjoinRoot.liftAlgHom_root _ _ _ _`. Establish `hψt : ψ T'.t = T.t`. Rewrite using `[ht']`.

Conclude with `(adjoinRoot_liftAlgHom_of_laurent φ w hPw _).trans hφt`. Establish `hψs : ψ T'.s = T.s`. Rewrite using `[hs']`. Conclude with `(adjoinRoot_liftAlgHom_of_laurent φ w hPw _).trans hφs`. Establish `hψB : ∀ x ∈ T'.B, ψ x ∈ T.B`.

Rewrite using `[hB']`. Apply `adjoin_map` to reduce the goal to its premises. Introduce `x hx`. Simplify using `only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx`. Break down `hx with rfl | rfl` into its components or cases.

Rewrite using `[hψt]`. Conclude with `T.tB`. Rewrite using `[map_mul, map_pow, hψt, hψr]`. Establish `e : T.t ^ k * w = T.t ^ (k - kB) * (T.t ^ kB * w)`. Rewrite using `[← mul_assoc, ← pow_add, Nat.sub_add_cancel (le_trans (le_max_left _ _) hk)]`.

Rewrite using `[e]`. Conclude with `mul_mem (pow_mem T.tB _) hkB`. Establish `hψC : ∀ x ∈ T'.C, ψ x ∈ T.C`. Rewrite using `[hC']`. Apply `adjoin_map` to reduce the goal to its premises.

Introduce `x hx`. Simplify using `only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx`. Break down `hx with rfl | rfl` into its components or cases. Rewrite using `[hψs]`. Conclude with `T.sC`.

Rewrite using `[map_mul, map_pow, hψs, hψr]`. Establish `e : T.s ^ k * w = T.s ^ (k - kC) * (T.s ^ kC * w)`. Rewrite using `[← mul_assoc, ← pow_add, Nat.sub_add_cancel (le_trans (le_max_right _ _) hk)]`. Rewrite using `[e]`. Conclude with `mul_mem (pow_mem T.sC _) hkC`.

Establish `hqS : IsUnit ((q : AdjoinRoot P ⧸ (maximalIdeal A).map (algebraMap A (AdjoinRoot P))))`. Use `hq.map ((Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A (AdjoinRoot P)))).comp (algebraMap A (AdjoinRoot P)))` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis. Establish `hnil : IsNilpotent ((Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A (AdjoinRoot P))) (AdjoinRoot.root P)) ^ q - 1)`. Use `⟨n, ?_⟩` and prove the remaining obligations.

Rewrite using `[← map_pow, ← map_one (Ideal.Quotient.mk _), ← map_sub, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `pow_root_mem P q n hPc`. Take `⟨y, hyq, hynil⟩` from `(UpperTheory.roots_of_unity_lift_mod_nilpotent_unique _ q hqS).1 _ hnil`. Take `⟨ω, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Establish `hω : ω ^ q - 1 ∈ mm (⊤ : Subalgebra A (AdjoinRoot P))`.

Rewrite using `[mem_mm_top_iff, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_one, hyq, sub_self]`. Take `⟨g', hg'B, g, hgC, μ, hg'1, hg1, hμ, hgg⟩` from `UpperTheory.exists_factorization_near_root_of_unity_henselian A (AdjoinRoot P) T' hFin hCoord q hq ω hω`. Establish `hG' : ψ g' ∈ T.B` using `hψB g' hg'B`. Establish `hG : ψ g ∈ T.C` using `hψC g hgC`. Establish `hG'1 : ψ g' - 1 ∈ mm T.B`.

Use `mm_map ψ T'.B T.B hψB hg'1` as an intermediate fact. Rewrite `this` using `[map_sub, map_one]`. Then use the resulting hypothesis. Establish `hG1 : ψ g - 1 ∈ mm T.C`. Use `mm_map ψ T'.C T.C hψC hg1` as an intermediate fact. Rewrite `this` using `[map_sub, map_one]`. Then use the resulting hypothesis.

Establish `hM : ψ μ - ψ ω ∈ mm (⊤ : Subalgebra A D)`. Use `mm_map ψ ⊤ ⊤ (fun _ _ => Algebra.mem_top) hμ` as an intermediate fact. Rewrite `this` using `[map_sub]`. Then use the resulting hypothesis. Establish `hGG : ψ g * ψ g' = (ψ μ) ^ q`. Rewrite using `[← map_mul, hgg, map_pow]`.

Take `⟨u, hu, huq⟩` from `qth_root T.B hB q hq0 (ψ g') hG'`. Take `⟨v, hv, hvq⟩` from `qth_root T.C hC q hq0 (ψ g) hG`. Take `⟨η, hη, hηq, hηe⟩` from `unity_ratio T.C hC q hq0 (ψ μ) (u * v) (by rw [mul_pow, huq, hvq, ← hGG, mul_comm])`. Use `⟨u, hu, η * v, mul_mem hη hv, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[huq]`.

Conclude with `hG'1`. Rewrite using `[mul_pow, hηq, one_mul, hvq]`. Conclude with `hG1`. Establish `hμe : u * (η * v) = ψ μ`. Rewrite using `[hηe]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hμe]`. Establish `hqD : IsUnit ((q : D ⧸ (maximalIdeal A).map (algebraMap A D)))`. Use `hq.map ((Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A D))).comp (algebraMap A D))` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis.

Establish `toQ : ∀ x : D, x ∈ mm (⊤ : Subalgebra A D) → Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A D)) x = 0`. Introduce `x hx`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem, ← mem_mm_top_iff]`. Conclude with `hx`. Rewrite using `[mem_mm_top_iff, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]`.

Apply `(UpperTheory.roots_of_unity_lift_mod_nilpotent_unique _ q hqD).2` to reduce the goal to its premises. Use `toQ _ hw` as an intermediate fact. Rewrite `this` using `[map_sub, map_pow, map_one, sub_eq_zero]`. Then use the resulting hypothesis. Establish `e1` using `toQ _ (hmono _ _ hG1)`. Establish `e2` using `toQ _ (hmono _ _ hG'1)`.

Rewrite `e1`, `e2` using `[map_sub, map_one, sub_eq_zero]`. Rewrite using `[← map_pow, ← hGG, map_mul, e1, e2, one_mul]`. Take `⟨N, hN⟩` from `hynil`. Use `⟨N, ?_⟩` and prove the remaining obligations. Establish `h1 : (AdjoinRoot.root P - ω) ^ N ∈ (maximalIdeal A).map (algebraMap A (AdjoinRoot P))`.

Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_pow, map_sub]`. Conclude with `hN`. Establish `h2 : ψ ((AdjoinRoot.root P - ω) ^ N) ∈ (maximalIdeal A).map (algebraMap A D)`. Use `Ideal.mem_map_of_mem (ψ : AdjoinRoot P →+* D) h1` as an intermediate fact. Rewrite `this` using `[Ideal.map_map, AlgHom.comp_algebraMap]`. Then use the resulting hypothesis.

Establish `h3 : Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A D)) (ψ μ) = Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A D)) (ψ ω)`. Rewrite using `[← sub_eq_zero, ← map_sub]`. Conclude with `toQ _ hM`. Rewrite using `[h3, ← map_sub, ← map_pow, Ideal.Quotient.eq_zero_iff_mem, ← hψr, ← map_sub, ← map_pow]`. Conclude with `h2`.
-/
theorem UpperTheory.exists_near_root_of_unity_product_decomposition :
    ∀ (A D : Type) [CommRing A] [HenselianLocalRing A] [CommRing D] [Algebra A D] [IsDomain D] (T : TC A D), T.Int → Roots T.B → Roots T.C → ∀ (q : ℕ), IsUnit (q : A) → ∀ w : D, w ^ q - 1 ∈ mm (⊤ : Subalgebra A D) →
      ∃ u ∈ T.B, ∃ v ∈ T.C, u ^ q - 1 ∈ mm T.B ∧ v ^ q - 1 ∈ mm T.C ∧ w - u * v ∈ mm (⊤ : Subalgebra A D) := by
  intro A D _ _ _ _ _ T hInt hB hC q hq w hw
  have hq0 : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h0 | h0
    · subst h0
      simp at hq
    · exact h0
  have hmono : ∀ (S : Subalgebra A D) (x : D), x ∈ mm S → x ∈ mm (⊤ : Subalgebra A D) :=
    fun S x hx => mm_map (AlgHom.id A D) S ⊤ (fun _ _ => Algebra.mem_top) hx
  obtain ⟨φ, P, n, hφt, hφs, hPm, hPw, hPc⟩ := UpperTheory.exists_monic_laurent_polynomial_near_root_of_unity A D T hInt q hq0 w hw
  obtain ⟨kB, hkB⟩ := T.locB w
  obtain ⟨kC, hkC⟩ := T.locC w
  obtain ⟨k, hk, T', hFin, hCoord, ht', hs', hB', hC'⟩ := UpperTheory.exists_twoChart_adjoinRoot_laurent A P hPm (max kB kC)
  let ψ : AdjoinRoot P →ₐ[A] D := AdjoinRoot.liftAlgHom P φ w hPw
  have hψr : ψ (AdjoinRoot.root P) = w := AdjoinRoot.liftAlgHom_root _ _ _ _
  have hψt : ψ T'.t = T.t := by
    rw [ht']
    exact (adjoinRoot_liftAlgHom_of_laurent φ w hPw _).trans hφt
  have hψs : ψ T'.s = T.s := by
    rw [hs']
    exact (adjoinRoot_liftAlgHom_of_laurent φ w hPw _).trans hφs
  have hψB : ∀ x ∈ T'.B, ψ x ∈ T.B := by
    rw [hB']
    apply adjoin_map
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · rw [hψt]
      exact T.tB
    · rw [map_mul, map_pow, hψt, hψr]
      have e : T.t ^ k * w = T.t ^ (k - kB) * (T.t ^ kB * w) := by
        rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel (le_trans (le_max_left _ _) hk)]
      rw [e]
      exact mul_mem (pow_mem T.tB _) hkB
  have hψC : ∀ x ∈ T'.C, ψ x ∈ T.C := by
    rw [hC']
    apply adjoin_map
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · rw [hψs]
      exact T.sC
    · rw [map_mul, map_pow, hψs, hψr]
      have e : T.s ^ k * w = T.s ^ (k - kC) * (T.s ^ kC * w) := by
        rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel (le_trans (le_max_right _ _) hk)]
      rw [e]
      exact mul_mem (pow_mem T.sC _) hkC
  have hqS : IsUnit ((q : AdjoinRoot P ⧸ (maximalIdeal A).map (algebraMap A (AdjoinRoot P)))) := by
    have := hq.map ((Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A (AdjoinRoot P)))).comp
      (algebraMap A (AdjoinRoot P)))
    rwa [map_natCast] at this
  have hnil : IsNilpotent ((Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A (AdjoinRoot P)))
      (AdjoinRoot.root P)) ^ q - 1) := by
    refine ⟨n, ?_⟩
    rw [← map_pow, ← map_one (Ideal.Quotient.mk _), ← map_sub, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact pow_root_mem P q n hPc
  obtain ⟨y, hyq, hynil⟩ := (UpperTheory.roots_of_unity_lift_mod_nilpotent_unique _ q hqS).1 _ hnil
  obtain ⟨ω, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hω : ω ^ q - 1 ∈ mm (⊤ : Subalgebra A (AdjoinRoot P)) := by
    rw [mem_mm_top_iff, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_one, hyq, sub_self]
  obtain ⟨g', hg'B, g, hgC, μ, hg'1, hg1, hμ, hgg⟩ := UpperTheory.exists_factorization_near_root_of_unity_henselian A (AdjoinRoot P) T' hFin hCoord q hq ω hω
  have hG' : ψ g' ∈ T.B := hψB g' hg'B
  have hG : ψ g ∈ T.C := hψC g hgC
  have hG'1 : ψ g' - 1 ∈ mm T.B := by
    have := mm_map ψ T'.B T.B hψB hg'1
    rwa [map_sub, map_one] at this
  have hG1 : ψ g - 1 ∈ mm T.C := by
    have := mm_map ψ T'.C T.C hψC hg1
    rwa [map_sub, map_one] at this
  have hM : ψ μ - ψ ω ∈ mm (⊤ : Subalgebra A D) := by
    have := mm_map ψ ⊤ ⊤ (fun _ _ => Algebra.mem_top) hμ
    rwa [map_sub] at this
  have hGG : ψ g * ψ g' = (ψ μ) ^ q := by
    rw [← map_mul, hgg, map_pow]
  obtain ⟨u, hu, huq⟩ := qth_root T.B hB q hq0 (ψ g') hG'
  obtain ⟨v, hv, hvq⟩ := qth_root T.C hC q hq0 (ψ g) hG
  obtain ⟨η, hη, hηq, hηe⟩ := unity_ratio T.C hC q hq0 (ψ μ) (u * v)
    (by rw [mul_pow, huq, hvq, ← hGG, mul_comm])
  refine ⟨u, hu, η * v, mul_mem hη hv, ?_, ?_, ?_⟩
  · rw [huq]
    exact hG'1
  · rw [mul_pow, hηq, one_mul, hvq]
    exact hG1
  have hμe : u * (η * v) = ψ μ := by
    rw [hηe]
    ring
  rw [hμe]
  have hqD : IsUnit ((q : D ⧸ (maximalIdeal A).map (algebraMap A D))) := by
    have := hq.map ((Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A D))).comp (algebraMap A D))
    rwa [map_natCast] at this
  have toQ : ∀ x : D, x ∈ mm (⊤ : Subalgebra A D) →
      Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A D)) x = 0 := by
    intro x hx
    rw [Ideal.Quotient.eq_zero_iff_mem, ← mem_mm_top_iff]
    exact hx
  rw [mem_mm_top_iff, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
  apply (UpperTheory.roots_of_unity_lift_mod_nilpotent_unique _ q hqD).2
  · have := toQ _ hw
    rwa [map_sub, map_pow, map_one, sub_eq_zero] at this
  · have e1 := toQ _ (hmono _ _ hG1)
    have e2 := toQ _ (hmono _ _ hG'1)
    rw [map_sub, map_one, sub_eq_zero] at e1 e2
    rw [← map_pow, ← hGG, map_mul, e1, e2, one_mul]
  · obtain ⟨N, hN⟩ := hynil
    refine ⟨N, ?_⟩
    have h1 : (AdjoinRoot.root P - ω) ^ N ∈ (maximalIdeal A).map (algebraMap A (AdjoinRoot P)) := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_pow, map_sub]
      exact hN
    have h2 : ψ ((AdjoinRoot.root P - ω) ^ N) ∈ (maximalIdeal A).map (algebraMap A D) := by
      have := Ideal.mem_map_of_mem (ψ : AdjoinRoot P →+* D) h1
      rwa [Ideal.map_map, AlgHom.comp_algebraMap] at this
    have h3 : Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A D)) (ψ μ) =
        Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A D)) (ψ ω) := by
      rw [← sub_eq_zero, ← map_sub]
      exact toQ _ hM
    rw [h3, ← map_sub, ← map_pow, Ideal.Quotient.eq_zero_iff_mem, ← hψr, ← map_sub, ← map_pow]
    exact h2

end
