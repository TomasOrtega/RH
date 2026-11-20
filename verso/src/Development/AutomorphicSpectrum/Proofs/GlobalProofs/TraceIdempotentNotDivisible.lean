import Mathlib

namespace GlobalTheory.CompanionTheory.IdemTrace

/- English proof (translation)
Use `set f : (Fin g → O) →ₗ[O] (Fin g → O) := Matrix.toLin' P with hf`. Establish `hidem : IsIdempotentElem f`. Unfold `IsIdempotentElem`. Rewrite using `[hf, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, h]`. Establish `hff : ∀ z, f (f z) = f z` using `fun z => by`.

Rewrite using `[← Module.End.mul_apply, hidem.eq]`. Establish `hproj` using `(LinearMap.isProj_range_iff_isIdempotentElem f).mpr hidem`. Establish `hPr : Module.Projective O (LinearMap.range f)` using `Module.Projective.of_split (LinearMap.range f).subtype f.rangeRestrict (LinearMap.ext fun y => Subtype.ext (by`. Take `⟨z, hz⟩` from `y.2`. Simplify using `only [LinearMap.comp_apply, Submodule.coe_subtype, LinearMap.id_apply]`.

Rewrite using `[← hz]`. Conclude with `hff z))`. Set `sK : (Fin g → O) →ₗ[O] LinearMap.ker f` to `(LinearMap.id - f).codRestrict (LinearMap.ker f) (fun y => by`. Rewrite using `[LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, map_sub, hff, sub_self])`. Establish `hsK : sK.comp (LinearMap.ker f).subtype = LinearMap.id` using `LinearMap.ext fun y => Subtype.ext (by`.

Establish `hy : f y = 0` using `y.2`. Simplify using `[sK, hy])`. Establish `hPk : Module.Projective O (LinearMap.ker f)` using `Module.Projective.of_split (LinearMap.ker f).subtype sK hsK`. Establish `hFk : Module.Finite O (LinearMap.ker f)` using `Module.Finite.of_surjective sK (fun y => ⟨y, by`. Conclude with `LinearMap.congr_fun hsK y⟩)`.

Establish `: Module.Free O (LinearMap.range f)` using `Module.free_of_flat_of_isLocalRing`. Establish `: Module.Free O (LinearMap.ker f)` using `Module.free_of_flat_of_isLocalRing`. Establish `htr` using `hproj.trace`. Use `⟨Module.finrank O (LinearMap.range f), ?_, ?_, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← Matrix.trace_toLin'_eq, ← hf, htr]`. Introduce `h0`. Establish `hs : Subsingleton (LinearMap.range f)` using `(Module.finrank_eq_zero_iff_of_free O _).mp h0`. Establish `hbot : LinearMap.range f = ⊥` using `Submodule.subsingleton_iff_eq_bot.mp hs`. Rewrite `hbot` using `[LinearMap.range_eq_bot, hf]`.

Conclude with `Matrix.toLin'.injective (by rw [hbot, map_zero])`.
-/
theorem exists_nat_trace_of_idem {O : Type} [CommRing O] [IsLocalRing O] {g : ℕ}
    (P : Matrix (Fin g) (Fin g) O) (h : P * P = P) :
    ∃ r : ℕ, r ≤ g ∧ Matrix.trace P = (r : O) ∧ (r = 0 → P = 0) := by
  classical
  set f : (Fin g → O) →ₗ[O] (Fin g → O) := Matrix.toLin' P with hf
  have hidem : IsIdempotentElem f := by
    unfold IsIdempotentElem
    rw [hf, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, h]
  have hff : ∀ z, f (f z) = f z := fun z => by
    rw [← Module.End.mul_apply, hidem.eq]
  have hproj := (LinearMap.isProj_range_iff_isIdempotentElem f).mpr hidem
  have hPr : Module.Projective O (LinearMap.range f) :=
    Module.Projective.of_split (LinearMap.range f).subtype f.rangeRestrict
      (LinearMap.ext fun y => Subtype.ext (by
        obtain ⟨z, hz⟩ := y.2
        simp only [LinearMap.comp_apply, Submodule.coe_subtype, LinearMap.id_apply]
        rw [← hz]
        exact hff z))
  let sK : (Fin g → O) →ₗ[O] LinearMap.ker f :=
    (LinearMap.id - f).codRestrict (LinearMap.ker f) (fun y => by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, map_sub, hff, sub_self])
  have hsK : sK.comp (LinearMap.ker f).subtype = LinearMap.id :=
    LinearMap.ext fun y => Subtype.ext (by
      have hy : f y = 0 := y.2
      simp [sK, hy])
  have hPk : Module.Projective O (LinearMap.ker f) :=
    Module.Projective.of_split (LinearMap.ker f).subtype sK hsK
  have hFk : Module.Finite O (LinearMap.ker f) :=
    Module.Finite.of_surjective sK (fun y => ⟨y, by
      exact LinearMap.congr_fun hsK y⟩)
  have : Module.Free O (LinearMap.range f) := Module.free_of_flat_of_isLocalRing
  have : Module.Free O (LinearMap.ker f) := Module.free_of_flat_of_isLocalRing
  have htr := hproj.trace
  refine ⟨Module.finrank O (LinearMap.range f), ?_, ?_, ?_⟩
  · calc Module.finrank O (LinearMap.range f) ≤ Module.finrank O (Fin g → O) :=
          Submodule.finrank_le _
      _ = g := Module.finrank_fin_fun O
  · rw [← Matrix.trace_toLin'_eq, ← hf, htr]
  · intro h0
    have hs : Subsingleton (LinearMap.range f) := (Module.finrank_eq_zero_iff_of_free O _).mp h0
    have hbot : LinearMap.range f = ⊥ := Submodule.subsingleton_iff_eq_bot.mp hs
    rw [LinearMap.range_eq_bot, hf] at hbot
    exact Matrix.toLin'.injective (by rw [hbot, map_zero])

/- English proof (translation)
Establish `: Fact (1 < p ^ m)` using `⟨Nat.one_lt_pow hm.ne' hp.out.one_lt⟩`. Use `IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hcon0`. Establish `hcon` using `not_or.mp hcon0`. Set `φ` to `ZMod.castHom (dvd_pow_self p hm.ne') (ZMod p)`.

Establish `key : ∀ b : ZMod (p ^ m), ¬ IsUnit b → φ b = 0`. Introduce `b hb`. Rewrite `hb`, the goal using `[← ZMod.natCast_zmod_val b]`. Rewrite `hb` using `[ZMod.isUnit_iff_coprime, Nat.coprime_pow_right_iff hm, Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp.out, not_not]`. Rewrite using `[map_natCast, ZMod.natCast_eq_zero_iff]`.

Conclude with `hb`. Establish `h1` using `congrArg φ (add_sub_cancel a 1)`. Rewrite `h1` using `[map_add, key a hcon.1, key _ hcon.2, add_zero, map_one]`. Conclude with `zero_ne_one h1`.
-/
private lemma isLocalRing_zmod_prime_pow (p m : ℕ) [hp : Fact p.Prime] (hm : 0 < m) :
    IsLocalRing (ZMod (p ^ m)) := by
  have : Fact (1 < p ^ m) := ⟨Nat.one_lt_pow hm.ne' hp.out.one_lt⟩
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  by_contra hcon0
  have hcon := not_or.mp hcon0
  let φ := ZMod.castHom (dvd_pow_self p hm.ne') (ZMod p)
  have key : ∀ b : ZMod (p ^ m), ¬ IsUnit b → φ b = 0 := by
    intro b hb
    rw [← ZMod.natCast_zmod_val b] at hb ⊢
    rw [ZMod.isUnit_iff_coprime, Nat.coprime_pow_right_iff hm, Nat.coprime_comm,
      Nat.Prime.coprime_iff_not_dvd hp.out, not_not] at hb
    rw [map_natCast, ZMod.natCast_eq_zero_iff]
    exact hb
  have h1 := congrArg φ (add_sub_cancel a 1)
  rw [map_add, key a hcon.1, key _ hcon.2, add_zero, map_one] at h1
  exact zero_ne_one h1

/- English proof (translation)
Introduce `B _ _ _ x p m hp hrank hidem hnot hdvd`. Break down `Nat.eq_zero_or_pos m with rfl | hm` into its components or cases. Apply `hnot` to reduce the goal to its premises. Simplify using the standard rewrite rules. Establish `: Fact p.Prime` using `⟨hp⟩`.

Use `isLocalRing_zmod_prime_pow p m hm` as an intermediate fact. Set `b` to `Module.finBasis ℤ B`. Set `M` to `Algebra.leftMulMatrix b x`. Set `φ` to `Int.castRingHom (ZMod (p ^ m))`. Set `P` to `φ.mapMatrix M`.

Establish `hpm : (((p : ℤ) ^ m : ℤ) : ZMod (p ^ m)) = 0`. Use `push_cast`. Conclude with `ZMod.natCast_self (p ^ m)` after adjusting the coercions. Take `⟨y, hy⟩` from `Ideal.mem_span_singleton'.mp hidem`. Establish `hz : y * (p : B) ^ m = ((p : ℤ) ^ m) • y`.

Rewrite using `[zsmul_eq_mul, Int.cast_pow, Int.cast_natCast, mul_comm]`. Establish `hP : P * P = P`. Establish `hMM : M * M - M = ((p : ℤ) ^ m) • Algebra.leftMulMatrix b y`. Rewrite using `[← map_zsmul, ← hz, hy, map_sub, map_mul]`. Rewrite using `[← sub_eq_zero]`.

Use `show φ.mapMatrix M * φ.mapMatrix M - φ.mapMatrix M = 0`. Rewrite using `[← map_mul, ← map_sub, hMM, map_zsmul, ← Int.cast_smul_eq_zsmul (ZMod (p ^ m)), hpm, zero_smul]`. Take `⟨r, hr, htr, hr0⟩` from `exists_nat_trace_of_idem P hP`. Establish `htrace : ((Algebra.trace ℤ B x : ℤ) : ZMod (p ^ m)) = P.trace`. Rewrite using `[Algebra.trace_eq_matrix_trace b x]`.

Simplify using `[P, M, φ, Matrix.trace, Matrix.diag]`. Take `⟨k, hk⟩` from `hdvd`. Establish `hr_zero : (r : ZMod (p ^ m)) = 0`. Rewrite using `[← htr, ← htrace, hk, Int.cast_mul, hpm, zero_mul]`. Rewrite `hr_zero` using `[ZMod.natCast_eq_zero_iff]`.

Establish `hr' : r = 0` using `Nat.eq_zero_of_dvd_of_lt hr_zero (by omega)`. Establish `hP0` using `hr0 hr'`. Establish `hent : ∀ i j, ((p : ℤ) ^ m) ∣ M i j`. Introduce `i j`. Establish `h1 : φ (M i j) = 0`.

Use `congrFun (congrFun hP0 i) j` as an intermediate fact. Simplify `this` using `[P]`. Establish `h2` using `(ZMod.intCast_zmod_eq_zero_iff_dvd (M i j) (p ^ m)).mp h1`. Conclude with `h2` after adjusting the coercions. Apply `hnot` to reduce the goal to its premises.

Establish `hxb : ∀ j, x * b j ∈ Ideal.span {((p : B)) ^ m}`. Introduce `j`. Rewrite using `[← b.sum_repr (x * b j)]`. Use `Ideal.sum_mem _ (fun i _ => ?_)` and prove the remaining obligations. Establish `hM : b.repr (x * b j) i = M i j` using `(Algebra.leftMulMatrix_eq_repr_mul b x i j).symm`.

Take `⟨c, hc⟩` from `hent i j`. Rewrite using `[hM, hc, Ideal.mem_span_singleton]`. Use `⟨c • b i, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_smul, zsmul_eq_mul, Int.cast_pow, Int.cast_natCast]`. Rewrite using `[← mul_one x, ← b.sum_repr 1, Finset.mul_sum]`.

Use `Ideal.sum_mem _ (fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[mul_smul_comm]`. Conclude with `Submodule.smul_of_tower_mem _ _ (hxb j)`.
-/
theorem not_dvd_trace : ∀ (B : Type) [CommRing B] [Module.Free ℤ B] [Module.Finite ℤ B] (x : B)
    (p m : ℕ), p.Prime → Module.finrank ℤ B < p ^ m →
    x * x - x ∈ Ideal.span {((p : B)) ^ m} → x ∉ Ideal.span {((p : B)) ^ m} →
    ¬ ((p : ℤ) ^ m ∣ Algebra.trace ℤ B x) := by
  intro B _ _ _ x p m hp hrank hidem hnot hdvd
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · apply hnot
    simp
  have : Fact p.Prime := ⟨hp⟩
  have := isLocalRing_zmod_prime_pow p m hm
  classical
  let b := Module.finBasis ℤ B
  let M := Algebra.leftMulMatrix b x
  let φ := Int.castRingHom (ZMod (p ^ m))
  let P := φ.mapMatrix M
  have hpm : (((p : ℤ) ^ m : ℤ) : ZMod (p ^ m)) = 0 := by
    push_cast
    exact_mod_cast ZMod.natCast_self (p ^ m)
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hidem
  have hz : y * (p : B) ^ m = ((p : ℤ) ^ m) • y := by
    rw [zsmul_eq_mul, Int.cast_pow, Int.cast_natCast, mul_comm]
  have hP : P * P = P := by
    have hMM : M * M - M = ((p : ℤ) ^ m) • Algebra.leftMulMatrix b y := by
      rw [← map_zsmul, ← hz, hy, map_sub, map_mul]
    rw [← sub_eq_zero]
    show φ.mapMatrix M * φ.mapMatrix M - φ.mapMatrix M = 0
    rw [← map_mul, ← map_sub, hMM, map_zsmul, ← Int.cast_smul_eq_zsmul (ZMod (p ^ m)), hpm,
      zero_smul]
  obtain ⟨r, hr, htr, hr0⟩ := exists_nat_trace_of_idem P hP
  have htrace : ((Algebra.trace ℤ B x : ℤ) : ZMod (p ^ m)) = P.trace := by
    rw [Algebra.trace_eq_matrix_trace b x]
    simp [P, M, φ, Matrix.trace, Matrix.diag]
  obtain ⟨k, hk⟩ := hdvd
  have hr_zero : (r : ZMod (p ^ m)) = 0 := by
    rw [← htr, ← htrace, hk, Int.cast_mul, hpm, zero_mul]
  rw [ZMod.natCast_eq_zero_iff] at hr_zero
  have hr' : r = 0 := Nat.eq_zero_of_dvd_of_lt hr_zero (by omega)
  have hP0 := hr0 hr'
  have hent : ∀ i j, ((p : ℤ) ^ m) ∣ M i j := by
    intro i j
    have h1 : φ (M i j) = 0 := by
      have := congrFun (congrFun hP0 i) j
      simpa [P] using this
    have h2 := (ZMod.intCast_zmod_eq_zero_iff_dvd (M i j) (p ^ m)).mp h1
    exact_mod_cast h2
  apply hnot
  have hxb : ∀ j, x * b j ∈ Ideal.span {((p : B)) ^ m} := by
    intro j
    rw [← b.sum_repr (x * b j)]
    refine Ideal.sum_mem _ (fun i _ => ?_)
    have hM : b.repr (x * b j) i = M i j := (Algebra.leftMulMatrix_eq_repr_mul b x i j).symm
    obtain ⟨c, hc⟩ := hent i j
    rw [hM, hc, Ideal.mem_span_singleton]
    refine ⟨c • b i, ?_⟩
    rw [mul_smul, zsmul_eq_mul, Int.cast_pow, Int.cast_natCast]
  rw [← mul_one x, ← b.sum_repr 1, Finset.mul_sum]
  refine Ideal.sum_mem _ (fun j _ => ?_)
  rw [mul_smul_comm]
  exact Submodule.smul_of_tower_mem _ _ (hxb j)

end GlobalTheory.CompanionTheory.IdemTrace
