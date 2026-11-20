import Mathlib

namespace GlobalTheory

open CommRing

/- English proof (translation)
Establish `h1 : (1 : B') ∈ ((I⁻¹ : (Submodule B B')ˣ) : Submodule B B') * (I : Submodule B B')`. Rewrite using `[← Units.val_mul, inv_mul_cancel, Units.val_one]`. Conclude with `Submodule.one_le.mp le_rfl`. Establish `key : ∀ y ∈ ((I⁻¹ : (Submodule B B')ˣ) : Submodule B B') * (I : Submodule B B'), ((n : B') * x) * y ∈ (I : Submodule B B')`. Introduce `y hy`.

Use `Submodule.mul_induction_on hy (fun j _ i hi => ?_) (fun y z hy hz => ?_)` and prove the remaining obligations. Take `⟨b, hb⟩` from `hn (x * j)`. Establish `: (n : B') * x * (j * i) = b • i`. Rewrite using `[Algebra.smul_def, hb]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ b hi`. Rewrite using `[mul_add]`. Conclude with `Submodule.add_mem _ hy hz`. Simplify using `using key 1 h1`.
-/
theorem natCast_mul_mem_units_submodule {B B' : Type} [CommRing B] [CommRing B'] [Algebra B B']
    (n : ℕ) (hn : ∀ b' : B', (n : B') * b' ∈ (algebraMap B B').range)
    (I : (Submodule B B')ˣ) (x : B') : (n : B') * x ∈ (I : Submodule B B') := by
  have h1 : (1 : B') ∈ ((I⁻¹ : (Submodule B B')ˣ) : Submodule B B') * (I : Submodule B B') := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    exact Submodule.one_le.mp le_rfl
  have key : ∀ y ∈ ((I⁻¹ : (Submodule B B')ˣ) : Submodule B B') * (I : Submodule B B'),
      ((n : B') * x) * y ∈ (I : Submodule B B') := by
    intro y hy
    refine Submodule.mul_induction_on hy (fun j _ i hi => ?_) (fun y z hy hz => ?_)
    · obtain ⟨b, hb⟩ := hn (x * j)
      have : (n : B') * x * (j * i) = b • i := by
        rw [Algebra.smul_def, hb]; ring
      rw [this]; exact Submodule.smul_mem _ b hi
    · rw [mul_add]; exact Submodule.add_mem _ hy hz
  simpa using key 1 h1

/- English proof (translation)
Use `set C : Submodule ℤ B' := (Ideal.span {(n : ℤ)}) • (⊤ : Submodule ℤ B') with hCdef`. Use `haveI : NeZero n := ⟨hn0⟩`. Use `haveI : Finite (ℤ ⧸ Ideal.span {(n : ℤ)}) := Finite.of_equiv _ (Int.quotientSpanNatEquivZMod n).symm.toEquiv`. Use `haveI : Finite (B' ⧸ C) := Submodule.finite_quotient_smul _ Module.Finite.fg_top`. Use `haveI : Finite (Submodule ℤ (B' ⧸ C)) := Finite.of_injective (fun N => (N : Set (B' ⧸ C))) SetLike.coe_injective`.

Establish `hC : ∀ I : (Submodule B B')ˣ, C ≤ (I : Submodule B B').restrictScalars ℤ`. Introduce `I`. Use `Submodule.smul_le.mpr fun r hr x _ => ?_` and prove the remaining obligations. Take `⟨k, rfl⟩` from `Ideal.mem_span_singleton'.mp hr`. Establish `: (k * n : ℤ) • x = (n : B') * (k • x)`.

Rewrite using `[zsmul_eq_mul, zsmul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Submodule.restrictScalars_mem, this]`. Conclude with `natCast_mul_mem_units_submodule n hn I _`.

Set `f : (Submodule B B')ˣ → Submodule ℤ (B' ⧸ C)` to `fun I => Submodule.map C.mkQ ((I : Submodule B B').restrictScalars ℤ)`. Use `Finite.of_injective f fun I J h => ?_` and prove the remaining obligations. Establish `hIJ : (I : Submodule B B').restrictScalars ℤ = (J : Submodule B B').restrictScalars ℤ`. Use `congrArg (Submodule.comap C.mkQ) h` as an intermediate fact. Simplify using `only [f, Submodule.comap_map_mkQ] at this`.

Rewrite `this` using `[sup_eq_right.mpr (hC I), sup_eq_right.mpr (hC J)]`. Then use the resulting hypothesis. Conclude with `Units.ext (Submodule.restrictScalars_injective ℤ _ _ hIJ)`.
-/
theorem finite_units_submodule {B B' : Type} [CommRing B] [CommRing B'] [Algebra B B']
    [Module.Finite ℤ B'] (n : ℕ) (hn0 : n ≠ 0)
    (hn : ∀ b' : B', (n : B') * b' ∈ (algebraMap B B').range) :
    Finite (Submodule B B')ˣ := by
  set C : Submodule ℤ B' := (Ideal.span {(n : ℤ)}) • (⊤ : Submodule ℤ B') with hCdef
  haveI : NeZero n := ⟨hn0⟩
  haveI : Finite (ℤ ⧸ Ideal.span {(n : ℤ)}) :=
    Finite.of_equiv _ (Int.quotientSpanNatEquivZMod n).symm.toEquiv
  haveI : Finite (B' ⧸ C) := Submodule.finite_quotient_smul _ Module.Finite.fg_top
  haveI : Finite (Submodule ℤ (B' ⧸ C)) :=
    Finite.of_injective (fun N => (N : Set (B' ⧸ C))) SetLike.coe_injective
  have hC : ∀ I : (Submodule B B')ˣ, C ≤ (I : Submodule B B').restrictScalars ℤ := by
    intro I
    refine Submodule.smul_le.mpr fun r hr x _ => ?_
    obtain ⟨k, rfl⟩ := Ideal.mem_span_singleton'.mp hr
    have : (k * n : ℤ) • x = (n : B') * (k • x) := by
      rw [zsmul_eq_mul, zsmul_eq_mul]; push_cast; ring
    rw [Submodule.restrictScalars_mem, this]
    exact natCast_mul_mem_units_submodule n hn I _
  let f : (Submodule B B')ˣ → Submodule ℤ (B' ⧸ C) := fun I =>
    Submodule.map C.mkQ ((I : Submodule B B').restrictScalars ℤ)
  refine Finite.of_injective f fun I J h => ?_
  have hIJ : (I : Submodule B B').restrictScalars ℤ = (J : Submodule B B').restrictScalars ℤ := by
    have := congrArg (Submodule.comap C.mkQ) h
    simp only [f, Submodule.comap_map_mkQ] at this
    rwa [sup_eq_right.mpr (hC I), sup_eq_right.mpr (hC J)] at this
  exact Units.ext (Submodule.restrictScalars_injective ℤ _ _ hIJ)

/- English proof (translation)
Introduce `B B' _ _ _ φ n hφ hn0 hn M hM`. Use `letI : Algebra B B' := φ.toAlgebra`. Use `haveI : FaithfulSMul B B' := (faithfulSMul_iff_algebraMap_injective B B').mpr hφ`. Use `haveI := finite_units_submodule (B := B) (B' := B') n hn0 (fun b' => hn b')`. Take `⟨k, hk, hpow⟩` from `hM.exists_pow_eq_one`.

Establish `e : CommRing.Pic.mapRingHom φ = CommRing.Pic.mapAlgebra B B'` using `CommRing.Pic.mapRingHom_algebraMap`. Establish `hmem : M ^ k ∈ CommRing.relPic B B'`. Rewrite using `[CommRing.relPic, MonoidHom.mem_ker, map_pow, ← e]`. Conclude with `hpow`. Rewrite `hmem` using `[← Submodule.range_unitsToPic]`.

Take `⟨I, hI⟩` from `hmem`. Establish `hfo : IsOfFinOrder (M ^ k)`. Rewrite using `[← hI]`. Conclude with `(Submodule.unitsToPic B B').isOfFinOrder (isOfFinOrder_of_finite I)`. Take `⟨m, hm, hm1⟩` from `hfo.exists_pow_eq_one`.

Conclude with `isOfFinOrder_iff_pow_eq_one.mpr ⟨k * m, Nat.mul_pos hk hm, by rw [pow_mul]; exact hm1⟩`.
-/
theorem isOfFinOrder_of_isOfFinOrder_mapRingHom : ∀ (B B' : Type) [CommRing B] [CommRing B']
    [Module.Finite ℤ B'] (φ : B →+* B') (n : ℕ), Function.Injective φ → n ≠ 0 →
    (∀ b' : B', (n : B') * b' ∈ φ.range) → ∀ M : CommRing.Pic B,
    IsOfFinOrder (CommRing.Pic.mapRingHom φ M) → IsOfFinOrder M := by
  intro B B' _ _ _ φ n hφ hn0 hn M hM
  letI : Algebra B B' := φ.toAlgebra
  haveI : FaithfulSMul B B' := (faithfulSMul_iff_algebraMap_injective B B').mpr hφ
  haveI := finite_units_submodule (B := B) (B' := B') n hn0 (fun b' => hn b')
  obtain ⟨k, hk, hpow⟩ := hM.exists_pow_eq_one
  have e : CommRing.Pic.mapRingHom φ = CommRing.Pic.mapAlgebra B B' :=
    CommRing.Pic.mapRingHom_algebraMap
  have hmem : M ^ k ∈ CommRing.relPic B B' := by
    rw [CommRing.relPic, MonoidHom.mem_ker, map_pow, ← e]; exact hpow
  rw [← Submodule.range_unitsToPic] at hmem
  obtain ⟨I, hI⟩ := hmem
  have hfo : IsOfFinOrder (M ^ k) := by
    rw [← hI]; exact (Submodule.unitsToPic B B').isOfFinOrder (isOfFinOrder_of_finite I)
  obtain ⟨m, hm, hm1⟩ := hfo.exists_pow_eq_one
  exact isOfFinOrder_iff_pow_eq_one.mpr ⟨k * m, Nat.mul_pos hk hm, by rw [pow_mul]; exact hm1⟩

end GlobalTheory
