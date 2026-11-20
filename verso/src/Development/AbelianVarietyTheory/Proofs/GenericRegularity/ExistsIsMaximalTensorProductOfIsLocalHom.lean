import Mathlib

open TensorProduct

namespace GlobalTheory

/- English proof (translation)
Rewrite using `[Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]`. Introduce and unpack `m ⟨⟨r, hr⟩, hm⟩`. Rewrite using `[Submodule.mem_bot]`. Establish `hr0 : r ≠ 0` using `nonZeroDivisors.ne_zero hr`. Establish `hmul : algebraMap O A r * m = 0` using `by rw [← Algebra.smul_def]; exact hm`.

Conclude with `(mul_eq_zero.mp hmul).resolve_left ((map_ne_zero_iff _ h).mpr hr0)`.
-/
theorem flat_of_injective_algebraMap_of_isDomain (O A : Type*) [CommRing O] [IsDomain O]
    [IsPrincipalIdealRing O] [CommRing A] [IsDomain A] [Algebra O A]
    (h : Function.Injective (algebraMap O A)) : Module.Flat O A := by
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
  rintro m ⟨⟨r, hr⟩, hm⟩
  rw [Submodule.mem_bot]
  have hr0 : r ≠ 0 := nonZeroDivisors.ne_zero hr
  have hmul : algebraMap O A r * m = 0 := by rw [← Algebra.smul_def]; exact hm
  exact (mul_eq_zero.mp hmul).resolve_left ((map_ne_zero_iff _ h).mpr hr0)

/- English proof (translation)
Establish `hinj : Function.Injective (LinearMap.lTensor A (LinearMap.mulRight O b))` using `Module.Flat.lTensor_preserves_injective_linearMap _ (mul_left_injective₀ hb)`. Establish `key : ∀ x : A ⊗[O] B, LinearMap.lTensor A (LinearMap.mulRight O b) x = x * (1 ⊗ₜ[O] b)`. Introduce `x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul a c => simp [Algebra.TensorProduct.tmul_mul_tmul]`. Consider the case `add x y hx hy => rw [map_add, hx, hy, add_mul]`. Rewrite using `[mem_nonZeroDivisors_iff_right]`. Introduce `x hx`. Conclude with `hinj (by rw [key, map_zero, hx])`.
-/
theorem one_tmul_mem_nonZeroDivisors_of_flat (O A B : Type*) [CommRing O] [CommRing A]
    [CommRing B] [IsDomain B] [Algebra O A] [Algebra O B] [Module.Flat O A] {b : B} (hb : b ≠ 0) :
    ((1 : A) ⊗ₜ[O] b) ∈ nonZeroDivisors (A ⊗[O] B) := by
  have hinj : Function.Injective (LinearMap.lTensor A (LinearMap.mulRight O b)) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ (mul_left_injective₀ hb)
  have key : ∀ x : A ⊗[O] B, LinearMap.lTensor A (LinearMap.mulRight O b) x = x * (1 ⊗ₜ[O] b) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a c => simp [Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy => rw [map_add, hx, hy, add_mul]
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  exact hinj (by rw [key, map_zero, hx])

/- English proof (translation)
Establish `hinj : Function.Injective (LinearMap.rTensor B (LinearMap.mulRight O a))` using `Module.Flat.rTensor_preserves_injective_linearMap _ (mul_left_injective₀ ha)`. Establish `key : ∀ x : A ⊗[O] B, LinearMap.rTensor B (LinearMap.mulRight O a) x = x * (a ⊗ₜ[O] (1 : B))`. Introduce `x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul c d => simp [Algebra.TensorProduct.tmul_mul_tmul]`. Consider the case `add x y hx hy => rw [map_add, hx, hy, add_mul]`. Rewrite using `[mem_nonZeroDivisors_iff_right]`. Introduce `x hx`. Conclude with `hinj (by rw [key, map_zero, hx])`.
-/
theorem tmul_one_mem_nonZeroDivisors_of_flat (O A B : Type*) [CommRing O] [CommRing A]
    [CommRing B] [IsDomain A] [Algebra O A] [Algebra O B] [Module.Flat O B] {a : A} (ha : a ≠ 0) :
    (a ⊗ₜ[O] (1 : B)) ∈ nonZeroDivisors (A ⊗[O] B) := by
  have hinj : Function.Injective (LinearMap.rTensor B (LinearMap.mulRight O a)) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (mul_left_injective₀ ha)
  have key : ∀ x : A ⊗[O] B, LinearMap.rTensor B (LinearMap.mulRight O a) x = x * (a ⊗ₜ[O] (1 : B)) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c d => simp [Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy => rw [map_add, hx, hy, add_mul]
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  exact hinj (by rw [key, map_zero, hx])

/- English proof (translation)
Take `⟨N, hN, hIN⟩` from `Ideal.exists_le_maximal I hI`. Establish `hle : IsLocalRing.maximalIdeal O ≤ N.comap (algebraMap O B)` using `Ideal.map_le_iff_le_comap.mp (hm.trans hIN)`. Use `letI : Algebra (IsLocalRing.ResidueField O) (B ⧸ N) := Ideal.Quotient.algebraQuotientOfLEComap hle`. Use `haveI : IsScalarTower O (IsLocalRing.ResidueField O) (B ⧸ N) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)`. Use `haveI : Nontrivial (IsLocalRing.ResidueField O' ⊗[IsLocalRing.ResidueField O] (B ⧸ N)) := Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain _ _ _ (RingHom.injective (algebraMap (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O'))) (RingHom.injective (alg …`.

Set `f : O' →ₐ[O] IsLocalRing.ResidueField O' ⊗[IsLocalRing.ResidueField O] (B ⧸ N)` to `(Algebra.TensorProduct.includeLeft).comp (IsScalarTower.toAlgHom O O' (IsLocalRing.ResidueField O'))`. Set `g : B →ₐ[O] IsLocalRing.ResidueField O' ⊗[IsLocalRing.ResidueField O] (B ⧸ N)` to `((Algebra.TensorProduct.includeRight).restrictScalars O).comp (IsScalarTower.toAlgHom O B (B ⧸ N))`. Set `ψ` to `Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)`. Take `⟨M, hM, hkM⟩` from `Ideal.exists_le_maximal (RingHom.ker ψ.toRingHom) (RingHom.ker_ne_top _)`. Use `⟨M, hM, fun a ha => hkM ?_, fun b hb => hkM ?_⟩` and prove the remaining obligations.

Rewrite using `[RingHom.mem_ker]`. Establish `h0 : IsLocalRing.residue O' a = 0` using `(IsLocalRing.residue_eq_zero_iff a).mpr ha`. Simplify using `[ψ, f, g, Algebra.TensorProduct.lift_tmul, h0]`. Rewrite using `[RingHom.mem_ker]`. Establish `h0 : Ideal.Quotient.mk N b = 0` using `Ideal.Quotient.eq_zero_iff_mem.mpr (hIN hb)`.

Simplify using `[ψ, f, g, Algebra.TensorProduct.lift_tmul, h0]`.
-/
theorem exists_isMaximal_tensorProduct_of_isLocalHom (O O' B : Type*) [CommRing O] [IsLocalRing O]
    [CommRing O'] [IsLocalRing O'] [Algebra O O'] [IsLocalHom (algebraMap O O')]
    [CommRing B] [Algebra O B] (I : Ideal B) (hI : I ≠ ⊤)
    (hm : Ideal.map (algebraMap O B) (IsLocalRing.maximalIdeal O) ≤ I) :
    ∃ M : Ideal (O' ⊗[O] B), M.IsMaximal ∧
      (∀ a ∈ IsLocalRing.maximalIdeal O', a ⊗ₜ[O] (1 : B) ∈ M) ∧
      ∀ b ∈ I, (1 : O') ⊗ₜ[O] b ∈ M := by
  obtain ⟨N, hN, hIN⟩ := Ideal.exists_le_maximal I hI
  have hle : IsLocalRing.maximalIdeal O ≤ N.comap (algebraMap O B) :=
    Ideal.map_le_iff_le_comap.mp (hm.trans hIN)
  letI : Algebra (IsLocalRing.ResidueField O) (B ⧸ N) :=
    Ideal.Quotient.algebraQuotientOfLEComap hle
  haveI : IsScalarTower O (IsLocalRing.ResidueField O) (B ⧸ N) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Nontrivial (IsLocalRing.ResidueField O' ⊗[IsLocalRing.ResidueField O] (B ⧸ N)) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain _ _ _
      (RingHom.injective (algebraMap (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O'))) (RingHom.injective (algebraMap (IsLocalRing.ResidueField O) (B ⧸ N)))
  let f : O' →ₐ[O] IsLocalRing.ResidueField O' ⊗[IsLocalRing.ResidueField O] (B ⧸ N) :=
    (Algebra.TensorProduct.includeLeft).comp (IsScalarTower.toAlgHom O O' (IsLocalRing.ResidueField O'))
  let g : B →ₐ[O] IsLocalRing.ResidueField O' ⊗[IsLocalRing.ResidueField O] (B ⧸ N) :=
    ((Algebra.TensorProduct.includeRight).restrictScalars O).comp (IsScalarTower.toAlgHom O B (B ⧸ N))
  let ψ := Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)
  obtain ⟨M, hM, hkM⟩ := Ideal.exists_le_maximal (RingHom.ker ψ.toRingHom) (RingHom.ker_ne_top _)
  refine ⟨M, hM, fun a ha => hkM ?_, fun b hb => hkM ?_⟩
  · rw [RingHom.mem_ker]
    have h0 : IsLocalRing.residue O' a = 0 :=
      (IsLocalRing.residue_eq_zero_iff a).mpr ha
    simp [ψ, f, g, Algebra.TensorProduct.lift_tmul, h0]
  · rw [RingHom.mem_ker]
    have h0 : Ideal.Quotient.mk N b = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (hIN hb)
    simp [ψ, f, g, Algebra.TensorProduct.lift_tmul, h0]

/- English proof (translation)
Introduce `H O O' _ _ _ _ _ _ _ _ _ _ hOO' B _ _ _ _ hOB I hI hmI e he`. Use `haveI : Module.Flat O O' := flat_of_injective_algebraMap_of_isDomain O O' hOO'`. Use `haveI : Module.Flat O B := flat_of_injective_algebraMap_of_isDomain O B hOB`. Take `⟨M, hM, hM1, hM2⟩` from `exists_isMaximal_tensorProduct_of_isLocalHom O O' B I hI hmI`. Take `⟨P, hPmin, hPM⟩` from `Ideal.exists_minimalPrimes_le (bot_le : (⊥ : Ideal (O' ⊗[O] B)) ≤ M)`.

Use `haveI : P.IsPrime := hPmin.isPrime`. Use `haveI : IsDomain (O' ⊗[O] B ⧸ P) := Ideal.Quotient.isDomain P`. Establish `hinj : Function.Injective (algebraMap O' (O' ⊗[O] B ⧸ P))`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `a ha`.

Assume the negation of the conclusion as `ha0`. Establish `ha' : Ideal.Quotient.mk P (a ⊗ₜ[O] (1 : B)) = 0` using `ha`. Conclude with `notMem_nonZeroDivisors_of_mem_mem_minimalPrimes (Ideal.Quotient.eq_zero_iff_mem.mp ha') hPmin (tmul_one_mem_nonZeroDivisors_of_flat O O' B ha0)`. Use `haveI : Module.Flat O' (O' ⊗[O] B ⧸ P) := flat_of_injective_algebraMap_of_isDomain _ _ hinj`. Use `haveI : Algebra.FiniteType O' (O' ⊗[O] B ⧸ P) := Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ O' P) (Ideal.Quotient.mkₐ_surjective O' P)`.

Establish `hM' : (M.map (Ideal.Quotient.mk P)).IsMaximal`. Use `(Ideal.map_eq_top_or_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective hM).resolve_left ?_` and prove the remaining obligations. Introduce `htop`. Establish `h1 : (1 : O' ⊗[O] B ⧸ P) ∈ M.map (Ideal.Quotient.mk P)` using `by rw [htop]; exact Submodule.mem_top`. Take `⟨m, hm, hm1⟩` from `(Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp h1`.

Establish `hmP : m - 1 ∈ P` using `Ideal.Quotient.eq.mp (by rw [hm1, map_one])`. Conclude with `hM.ne_top ((Ideal.eq_top_iff_one _).mpr (by simpa using M.sub_mem hm (hPM hmP)))`. Establish `hmap : Ideal.map (algebraMap O' (O' ⊗[O] B ⧸ P)) (IsLocalRing.maximalIdeal O') ≤ M.map (Ideal.Quotient.mk P)` using `Ideal.map_le_iff_le_comap.mpr fun a ha => Ideal.mem_map_of_mem (Ideal.Quotient.mk P) (hM1 a ha)`. Establish `he' : Ideal.Quotient.mk P ((1 : O') ⊗ₜ[O] e) ≠ 0`. Introduce `h0`.

Conclude with `notMem_nonZeroDivisors_of_mem_mem_minimalPrimes (Ideal.Quotient.eq_zero_iff_mem.mp h0) hPmin (one_tmul_mem_nonZeroDivisors_of_flat O O' B he)`. Take `⟨V, i₁, i₂, i₃, i₄, i₅, φ, hφe, hφM⟩` from `H O' (O' ⊗[O] B ⧸ P) (M.map (Ideal.Quotient.mk P)) hM' hmap _ he'`. Use `⟨V, i₁, i₂, i₃, i₄, i₅, φ.toRingHom.comp ((Ideal.Quotient.mk P).comp (Algebra.TensorProduct.includeRight : B →ₐ[O] O' ⊗[O] B).toRingHom), ?_, hφe, ?_⟩` and prove the remaining obligations. Use extensionality with `o`. Establish `h1 : (Algebra.TensorProduct.includeRight : B →ₐ[O] O' ⊗[O] B) (algebraMap O B o) = algebraMap O' (O' ⊗[O] B) (algebraMap O O' o)`.

Rewrite using `[AlgHom.commutes, IsScalarTower.algebraMap_apply O O' (O' ⊗[O] B)]`. Simplify using `only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, h1]`. Conclude with `φ.commutes _`. Introduce `x hx`. Conclude with `hφM _ (Ideal.mem_map_of_mem (Ideal.Quotient.mk P) (hM2 x hx))`.
-/
theorem exists_integral_point_of_complete_case :
    (∀ (O B : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [CharZero O] [CommRing B] [IsDomain B] [Algebra O B] [Algebra.FiniteType O B] [Module.Flat O B] (M : Ideal B), M.IsMaximal → Ideal.map (algebraMap O B) (IsLocalRing.maximalIdeal O) ≤ M → ∀ e : B, e ≠ 0 → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Algebra O V) (_ : Module.Finite O V) (φ : B →ₐ[O] V), φ e ≠ 0 ∧ ∀ x ∈ M, φ x ∈ IsLocalRing.maximalIdeal V) → ∀ (O O' : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [IsAdicComplete (IsLocalRing.maximalIdeal O') O'] [CharZero O'] [Algebra O O'] [IsLocalHom (algebraMap O O')], Function.Injective (algebraMap O O') → ∀ (B : Type) [CommRing B] [IsDomain B] [Algebra O B] [Algebra.FiniteType O B], Function.Injective (algebraMap O B) → ∀ I : Ideal B, I ≠ ⊤ → Ideal.map (algebraMap O B) (IsLocalRing.maximalIdeal O) ≤ I → ∀ e : B, e ≠ 0 → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Algebra O' V) (_ : Module.Finite O' V) (φ : B →+* V), φ.comp (algebraMap O B) = (algebraMap O' V).comp (algebraMap O O') ∧ φ e ≠ 0 ∧ ∀ x ∈ I, φ x ∈ IsLocalRing.maximalIdeal V := by
  intro H O O' _ _ _ _ _ _ _ _ _ _ hOO' B _ _ _ _ hOB I hI hmI e he
  haveI : Module.Flat O O' := flat_of_injective_algebraMap_of_isDomain O O' hOO'
  haveI : Module.Flat O B := flat_of_injective_algebraMap_of_isDomain O B hOB
  obtain ⟨M, hM, hM1, hM2⟩ := exists_isMaximal_tensorProduct_of_isLocalHom O O' B I hI hmI
  obtain ⟨P, hPmin, hPM⟩ := Ideal.exists_minimalPrimes_le (bot_le : (⊥ : Ideal (O' ⊗[O] B)) ≤ M)
  haveI : P.IsPrime := hPmin.isPrime
  haveI : IsDomain (O' ⊗[O] B ⧸ P) := Ideal.Quotient.isDomain P
  have hinj : Function.Injective (algebraMap O' (O' ⊗[O] B ⧸ P)) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra ha0
    have ha' : Ideal.Quotient.mk P (a ⊗ₜ[O] (1 : B)) = 0 := ha
    exact notMem_nonZeroDivisors_of_mem_mem_minimalPrimes (Ideal.Quotient.eq_zero_iff_mem.mp ha')
      hPmin (tmul_one_mem_nonZeroDivisors_of_flat O O' B ha0)
  haveI : Module.Flat O' (O' ⊗[O] B ⧸ P) := flat_of_injective_algebraMap_of_isDomain _ _ hinj
  haveI : Algebra.FiniteType O' (O' ⊗[O] B ⧸ P) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ O' P)
      (Ideal.Quotient.mkₐ_surjective O' P)
  have hM' : (M.map (Ideal.Quotient.mk P)).IsMaximal := by
    refine (Ideal.map_eq_top_or_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective hM).resolve_left ?_
    intro htop
    have h1 : (1 : O' ⊗[O] B ⧸ P) ∈ M.map (Ideal.Quotient.mk P) := by rw [htop]; exact Submodule.mem_top
    obtain ⟨m, hm, hm1⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp h1
    have hmP : m - 1 ∈ P := Ideal.Quotient.eq.mp (by rw [hm1, map_one])
    exact hM.ne_top ((Ideal.eq_top_iff_one _).mpr (by simpa using M.sub_mem hm (hPM hmP)))
  have hmap : Ideal.map (algebraMap O' (O' ⊗[O] B ⧸ P)) (IsLocalRing.maximalIdeal O') ≤
      M.map (Ideal.Quotient.mk P) :=
    Ideal.map_le_iff_le_comap.mpr fun a ha => Ideal.mem_map_of_mem (Ideal.Quotient.mk P) (hM1 a ha)
  have he' : Ideal.Quotient.mk P ((1 : O') ⊗ₜ[O] e) ≠ 0 := by
    intro h0
    exact notMem_nonZeroDivisors_of_mem_mem_minimalPrimes (Ideal.Quotient.eq_zero_iff_mem.mp h0)
      hPmin (one_tmul_mem_nonZeroDivisors_of_flat O O' B he)
  obtain ⟨V, i₁, i₂, i₃, i₄, i₅, φ, hφe, hφM⟩ :=
    H O' (O' ⊗[O] B ⧸ P) (M.map (Ideal.Quotient.mk P)) hM' hmap _ he'
  refine ⟨V, i₁, i₂, i₃, i₄, i₅,
    φ.toRingHom.comp ((Ideal.Quotient.mk P).comp
      (Algebra.TensorProduct.includeRight : B →ₐ[O] O' ⊗[O] B).toRingHom), ?_, hφe, ?_⟩
  · ext o
    have h1 : (Algebra.TensorProduct.includeRight : B →ₐ[O] O' ⊗[O] B) (algebraMap O B o) =
        algebraMap O' (O' ⊗[O] B) (algebraMap O O' o) := by
      rw [AlgHom.commutes, IsScalarTower.algebraMap_apply O O' (O' ⊗[O] B)]
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, h1]
    exact φ.commutes _
  · intro x hx
    exact hφM _ (Ideal.mem_map_of_mem (Ideal.Quotient.mk P) (hM2 x hx))

end GlobalTheory
