import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrincipalCongruenceFixedVectorsLeSmoothVectors
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantOrbit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixRegular

noncomputable section

namespace GlobalTheory.DepthZeroCusp

open GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.GLp.Supp GlobalTheory.SerSys GlobalTheory.OppRad GlobalTheory.PRep
open scoped Classical

/- English proof (translation)
Take `⟨b, hb, hs, hl⟩` from `exists_linearIndependent ℂ (Set.range u)`. Distinguish the cases in `hf : b.Finite`. Set `W` to `Submodule.span ℂ b haveI : FiniteDimensional ℂ W := FiniteDimensional.span_of_finite ℂ hf`. Establish `hm : ∀ m, u m ∈ W` using `fun m => hs.ge (Submodule.subset_span ⟨m, rfl⟩)`. Set `β` to `Module.finBasis ℂ W`.

Establish `: ∀ m, ∃ i, β.coord i ⟨u m, hm m⟩ ≠ 0` using `fun m => by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `hu m (congrArg Subtype.val (β.forall_coord_eq_zero_iff.1 h))`. Use `choose i hi using this`.

Take `⟨j, hj⟩` from `Finite.exists_infinite_fiber i`. Take `⟨l, hl⟩` from `LinearMap.exists_extend (β.coord j)`. Use `⟨l, (Set.infinite_coe_iff.1 hj).mono fun m (h : i m = j) => ?_⟩` and prove the remaining obligations. Use `LinearMap.congr_fun hl ⟨u m, hm m⟩` as an intermediate fact. Conclude with `fun e => hi m (h ▸ this.symm.trans e)`.

Take `⟨l, hl⟩` from `Module.exists_dual_forall_apply_eq_one (K := ℂ) (s := b) (v := id) hl`. Use `⟨l, Set.Infinite.of_image u (Set.Infinite.mono (fun x hx => ?_) hf)⟩` and prove the remaining obligations. Take `⟨m, rfl⟩` from `hb hx`. Conclude with `⟨m, by simpa using (hl _ hx).trans_ne one_ne_zero, rfl⟩`.
-/
theorem exists_dual_frequently {M : Type} [AddCommGroup M] [Module ℂ M] (u : ℕ → M) (hu : ∀ m, u m ≠ 0) :
    ∃ l : Module.Dual ℂ M, {m | l (u m) ≠ 0}.Infinite := by
  obtain ⟨b, hb, hs, hl⟩ := exists_linearIndependent ℂ (Set.range u)
  by_cases hf : b.Finite
  · let W := Submodule.span ℂ b
    haveI : FiniteDimensional ℂ W := FiniteDimensional.span_of_finite ℂ hf
    have hm : ∀ m, u m ∈ W := fun m => hs.ge (Submodule.subset_span ⟨m, rfl⟩)
    let β := Module.finBasis ℂ W
    have : ∀ m, ∃ i, β.coord i ⟨u m, hm m⟩ ≠ 0 := fun m => by
      by_contra h
      push Not at h
      exact hu m (congrArg Subtype.val (β.forall_coord_eq_zero_iff.1 h))
    choose i hi using this
    obtain ⟨j, hj⟩ := Finite.exists_infinite_fiber i
    obtain ⟨l, hl⟩ := LinearMap.exists_extend (β.coord j)
    refine ⟨l, (Set.infinite_coe_iff.1 hj).mono fun m (h : i m = j) => ?_⟩
    have := LinearMap.congr_fun hl ⟨u m, hm m⟩
    exact fun e => hi m (h ▸ this.symm.trans e)
  · obtain ⟨l, hl⟩ := Module.exists_dual_forall_apply_eq_one (K := ℂ) (s := b) (v := id) hl
    refine ⟨l, Set.Infinite.of_image u (Set.Infinite.mono (fun x hx => ?_) hf)⟩
    obtain ⟨m, rfl⟩ := hb hx
    exact ⟨m, by simpa using (hl _ hx).trans_ne one_ne_zero, rfl⟩

variable {g : ℕ} [Fact g.Prime] {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

local notation "φ" => RingHom.mapMatrix (m := Fin n) (PadicInt.toZMod (p := g))
local notation "ι" => RingHom.mapMatrix (m := Fin n) (algebraMap ℤ_[g] ℚ_[g])

variable (g n) in

def KOne : Subgroup (GL (Fin n) ℚ_[g]) := (red g n).ker.map (inc g n)

/- English proof (translation)
Use `haveI : CompactSpace (Matrix (Fin n) (Fin n) ℤ_[g]) := inferInstanceAs (CompactSpace (Fin n → Fin n → ℤ_[g]))`. Establish `hc : Continuous (inc g n)` using `Units.continuous_map (continuous_id.matrix_map continuous_subtype_val)`. Use `(Subgroup.isClosed_of_isOpen _ ?_).isCompact.image hc` and prove the remaining obligations. Establish `ho : IsOpen {x : GL (Fin n) ℤ_[g] | ∀ i j, ‖(x.val - 1) i j‖ < 1}`. Simplify using `only [Set.setOf_forall]`.

Use `isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => isOpen_lt ?_ continuous_const` and prove the remaining obligations. Conclude with `((Units.continuous_val.sub continuous_const).matrix_elem i j).norm`. Use `Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset (ho.mem_nhds (by simp)) fun x hx => ?_)` and prove the remaining obligations. Establish `: φ (x.val - 1) = 0`. Use extensionality with `i j`.

Establish `: (x.val - 1) i j ∈ RingHom.ker (PadicInt.toZMod (p` using `g)) := by`. Rewrite using `[PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]`. Conclude with `hx i j`. Conclude with `this`. Rewrite `this` using `[map_sub, map_one, sub_eq_zero]`.

Conclude with `Units.ext this`.
-/
theorem isCompact_KOne : IsCompact (KOne g n : Set (GL (Fin n) ℚ_[g])) := by
  haveI : CompactSpace (Matrix (Fin n) (Fin n) ℤ_[g]) := inferInstanceAs (CompactSpace (Fin n → Fin n → ℤ_[g]))
  have hc : Continuous (inc g n) :=
    Units.continuous_map (continuous_id.matrix_map continuous_subtype_val)
  refine (Subgroup.isClosed_of_isOpen _ ?_).isCompact.image hc
  have ho : IsOpen {x : GL (Fin n) ℤ_[g] | ∀ i j, ‖(x.val - 1) i j‖ < 1} := by
    simp only [Set.setOf_forall]
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => isOpen_lt ?_ continuous_const
    exact ((Units.continuous_val.sub continuous_const).matrix_elem i j).norm
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset (ho.mem_nhds (by simp)) fun x hx => ?_)
  have : φ (x.val - 1) = 0 := by
    ext i j
    have : (x.val - 1) i j ∈ RingHom.ker (PadicInt.toZMod (p := g)) := by
      rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]
      exact hx i j
    exact this
  rw [map_sub, map_one, sub_eq_zero] at this
  exact Units.ext this

/- English proof (translation)
Establish `hdet : IsUnit A.det`. Assume the negation of the conclusion as `h'`. Establish `h1 : A.det ∈ IsLocalRing.maximalIdeal ℤ_[g]` using `h'`. Rewrite `h1` using `[← PadicInt.ker_toZMod, RingHom.mem_ker, RingHom.map_det, h]`. Conclude with `(Matrix.isUnits_det_units u).ne_zero h1`.

Conclude with `⟨((Matrix.isUnit_iff_isUnit_det _).2 hdet).unit, rfl, Units.ext h⟩`.
-/
theorem exists_unit (A : Matrix (Fin n) (Fin n) ℤ_[g]) (u : Gn g n) (h : φ A = u.val) :
    ∃ k : GL (Fin n) ℤ_[g], k.val = A ∧ red g n k = u := by
  have hdet : IsUnit A.det := by
    by_contra h'
    have h1 : A.det ∈ IsLocalRing.maximalIdeal ℤ_[g] := h'
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker, RingHom.map_det, h] at h1
    exact (Matrix.isUnits_det_units u).ne_zero h1
  exact ⟨((Matrix.isUnit_iff_isUnit_det _).2 hdet).unit, rfl, Units.ext h⟩

/- English proof (translation)
Establish `: ∀ i j, ∃ c, c * (g : ℤ_[g]) = N i j` using `fun i j => by`. Establish `: N i j ∈ RingHom.ker (PadicInt.toZMod (p` using `g)) := congrFun (congrFun h i) j`. Rewrite `this` using `[PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton']`. Then use the resulting hypothesis. Use `choose M hM using this`. Use `⟨Matrix.of M, ?_⟩` and prove the remaining obligations.

Use extensionality with `i j`. Rewrite using `[← nsmul_eq_mul, Matrix.smul_apply, nsmul_eq_mul, Matrix.of_apply, ← hM, mul_comm]`.
-/
theorem exists_div {N : Matrix (Fin n) (Fin n) ℤ_[g]} (h : φ N = 0) :
    ∃ M : Matrix (Fin n) (Fin n) ℤ_[g], N = (g : Matrix (Fin n) (Fin n) ℤ_[g]) * M := by
  have : ∀ i j, ∃ c, c * (g : ℤ_[g]) = N i j := fun i j => by
    have : N i j ∈ RingHom.ker (PadicInt.toZMod (p := g)) := congrFun (congrFun h i) j
    rwa [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at this
  choose M hM using this
  refine ⟨Matrix.of M, ?_⟩
  ext i j
  rw [← nsmul_eq_mul, Matrix.smul_apply, nsmul_eq_mul, Matrix.of_apply, ← hM, mul_comm]

/- English proof (translation)
Rewrite using `[map_natCast, ← nsmul_one, ← Nat.cast_smul_eq_nsmul (ZMod g), ZMod.natCast_self, zero_smul]`.
-/
theorem red_nat : φ (g : Matrix (Fin n) (Fin n) ℤ_[g]) = 0 := by
  rw [map_natCast, ← nsmul_one, ← Nat.cast_smul_eq_nsmul (ZMod g), ZMod.natCast_self, zero_smul]

/- English proof (translation)
Establish `h1 : P * (1 - P) = 0` using `by rw [mul_sub, h, mul_one, sub_self]`. Establish `h2 : (1 - P) * P = 0` using `by rw [sub_mul, h, one_mul, sub_self]`. Establish `h3 : (1 - P) * (1 - P) = 1 - P` using `by rw [sub_mul, h1, one_mul, sub_zero]`. Simplify using `only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, h, h1, h2, h3, smul_zero, add_zero, zero_add, smul_smul, mul_comm]`.
-/
theorem idem_mul {A R : Type} [CommRing A] [Ring R] [Algebra A R] {P : R} (h : P * P = P) (s t : A) :
    (P + s • (1 - P)) * (P + t • (1 - P)) = P + (s * t) • (1 - P) := by
  have h1 : P * (1 - P) = 0 := by rw [mul_sub, h, mul_one, sub_self]
  have h2 : (1 - P) * P = 0 := by rw [sub_mul, h, one_mul, sub_self]
  have h3 : (1 - P) * (1 - P) = 1 - P := by rw [sub_mul, h1, one_mul, sub_zero]
  simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, h, h1, h2, h3, smul_zero, add_zero, zero_add, smul_smul,
    mul_comm]

variable {P : Matrix (Fin n) (Fin n) ℤ_[g]}

def dd (hP : P * P = P) (m : ℕ) : GL (Fin n) ℚ_[g] :=
  have h : ι P * ι P = ι P := by rw [← map_mul, hP]
  have h0 : (g : ℚ_[g]) ^ m ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : g.Prime).ne_zero)
  ⟨ι P + (g : ℚ_[g]) ^ m • (1 - ι P), ι P + ((g : ℚ_[g]) ^ m)⁻¹ • (1 - ι P),
    by rw [idem_mul h, mul_inv_cancel₀ h0, one_smul, add_sub_cancel],
    by rw [idem_mul h, inv_mul_cancel₀ h0, one_smul, add_sub_cancel]⟩

/- English proof (translation)
Rewrite using `[map_add, map_nsmul, map_sub, map_one, ← Nat.cast_smul_eq_nsmul ℚ_[g], Nat.cast_pow]`. Both sides reduce to the same expression.
-/
theorem dd_val (hP : P * P = P) (m : ℕ) : (dd hP m).val = ι (P + g ^ m • (1 - P)) := by
  rw [map_add, map_nsmul, map_sub, map_one, ← Nat.cast_smul_eq_nsmul ℚ_[g], Nat.cast_pow]
  rfl

/- English proof (translation)
The claim follows from `Units.ext (by rw [dd_val, pow_zero, one_smul, add_sub_cancel, map_one, Units.val_one])`.
-/
theorem dd_zero (hP : P * P = P) : dd hP 0 = 1 :=
  Units.ext (by rw [dd_val, pow_zero, one_smul, add_sub_cancel, map_one, Units.val_one])

/- English proof (translation)
The claim follows from `Units.ext ((congrArg (fun s => ι P + s • (1 - ι P)) (pow_add _ _ _)).trans (idem_mul (by rw [← map_mul, hP]) _ _).symm)`.
-/
theorem dd_succ (hP : P * P = P) (m : ℕ) : dd hP (m + 1) = dd hP m * dd hP 1 :=
  Units.ext ((congrArg (fun s => ι P + s • (1 - ι P)) (pow_add _ _ _)).trans
    (idem_mul (by rw [← map_mul, hP]) _ _).symm)

/- English proof (translation)
Establish `hp : φ P * φ P = φ P` using `by rw [← map_mul, hP]`. Take `⟨x, hx⟩ : ∃ x, φ k.val = 1 + φ P * (x * (1 - φ P))` from `⟨(red g n k).val - 1, by rw [hk.2, hk.1, add_sub_cancel]; rfl⟩`. Establish `hp' : ∀ r, φ P * (φ P * r) = φ P * r` using `fun r => by rw [← mul_assoc, hp]`. Take `⟨M, hM⟩` from `exists_div (N := (1 - P) * k.val * P) (by`. Rewrite using `[map_mul, map_mul, map_sub, map_one, hx]`.

Simplify using `only [mul_add, add_mul, mul_sub, sub_mul, mul_assoc, hp, hp', mul_one, one_mul, sub_self, add_zero])`. Establish `hx2 : (1 - φ P) * (φ M * φ P) * ((1 - φ P) * (φ M * φ P)) = 0`. Simplify using `only [mul_add, add_mul, mul_sub, sub_mul, mul_assoc, hp, hp', mul_one, one_mul, sub_self, add_zero]`. Take `⟨k', h1, h2⟩` from `exists_unit (P * k.val * P + (1 - P) * k.val * (1 - P) + (g : Matrix (Fin n) (Fin n) ℤ_[g]) * (P * k.val * (1 - P)) + (1 - P) * (M * P)) (un _ hx2) (by`. Simplify using `only [map_add, map_mul, map_sub, map_one, red_nat, hx, un_val, zero_mul]`.

Simplify using `only [mul_add, add_mul, mul_sub, sub_mul, mul_assoc, hp, hp', mul_one, one_mul, sub_self, add_zero]`. Use the proof step `abel)`. Use `⟨k', h2 ▸ un_mem _ ?_ ?_, Units.ext ?_⟩` and prove the remaining obligations. Simplify using `only [mul_sub, sub_mul, mul_assoc, hp, hp', mul_one, one_mul, sub_self, sub_zero]`. Simplify using `only [mul_assoc, hp]`.

Express the relevant statement in the definitionally equal form `(dd hP 1).val * ι k'.val = ι k.val * (dd hP 1).val`. Rewrite using `[dd_val, ← map_mul, ← map_mul, h1]`. Use `congr 1`. Establish `hP' : ∀ r, P * (P * r) = P * r` using `fun r => by rw [← mul_assoc, hP]`. Establish `hM' : g • ((1 - P) * (M * P)) = (1 - P) * k.val * P`.

Rewrite using `[← mul_smul_comm, ← smul_mul_assoc, nsmul_eq_mul, ← hM]`. Simplify using `only [mul_sub, sub_mul, mul_assoc, hP, hP', mul_one, one_mul, sub_self, sub_zero]`. Establish `e : (P + g • (1 - P)) * ((1 - P) * (M * P)) = g • ((1 - P) * (M * P))`. Simplify using `only [mul_add, add_mul, mul_sub, sub_mul, mul_assoc, hP, hP', mul_one, one_mul, sub_self, sub_zero, smul_mul_assoc, zero_add, smul_zero, add_zero, add_sub_cancel_left]`. Rewrite using `[pow_one, ← nsmul_eq_mul, mul_add _ _ ((1 - P) * _), e, hM']`.

Simplify using `only [mul_add, add_mul, mul_sub, sub_mul, mul_assoc, hP, hP', mul_one, one_mul, sub_self, sub_zero, smul_mul_assoc, mul_smul_comm, zero_add, add_zero, smul_zero, smul_sub, smul_add]`. Normalize the expressions using the abelian group laws.
-/
theorem conj_up (hP : P * P = P) {k : GL (Fin n) ℤ_[g]} (hk : red g n k ∈ U (φ P) (1 - φ P)) :
    ∃ k', red g n k' ∈ U (1 - φ P) (φ P) ∧ dd hP 1 * inc g n k' = inc g n k * dd hP 1 := by
  have hp : φ P * φ P = φ P := by rw [← map_mul, hP]
  obtain ⟨x, hx⟩ : ∃ x, φ k.val = 1 + φ P * (x * (1 - φ P)) :=
    ⟨(red g n k).val - 1, by rw [hk.2, hk.1, add_sub_cancel]; rfl⟩
  have hp' : ∀ r, φ P * (φ P * r) = φ P * r := fun r => by rw [← mul_assoc, hp]
  obtain ⟨M, hM⟩ := exists_div (N := (1 - P) * k.val * P) (by
    rw [map_mul, map_mul, map_sub, map_one, hx]
    simp only [mul_add, add_mul, mul_sub, sub_mul, mul_assoc, hp, hp', mul_one, one_mul, sub_self, add_zero])
  have hx2 : (1 - φ P) * (φ M * φ P) * ((1 - φ P) * (φ M * φ P)) = 0 := by
    simp only [mul_add, add_mul, mul_sub, sub_mul, mul_assoc, hp, hp', mul_one, one_mul, sub_self, add_zero]
  obtain ⟨k', h1, h2⟩ := exists_unit (P * k.val * P + (1 - P) * k.val * (1 - P) +
    (g : Matrix (Fin n) (Fin n) ℤ_[g]) * (P * k.val * (1 - P)) + (1 - P) * (M * P)) (un _ hx2) (by
      simp only [map_add, map_mul, map_sub, map_one, red_nat, hx, un_val, zero_mul]
      simp only [mul_add, add_mul, mul_sub, sub_mul, mul_assoc, hp, hp', mul_one, one_mul, sub_self, add_zero]
      abel)
  refine ⟨k', h2 ▸ un_mem _ ?_ ?_, Units.ext ?_⟩
  · simp only [mul_sub, sub_mul, mul_assoc, hp, hp', mul_one, one_mul, sub_self, sub_zero]
  · simp only [mul_assoc, hp]
  · change (dd hP 1).val * ι k'.val = ι k.val * (dd hP 1).val
    rw [dd_val, ← map_mul, ← map_mul, h1]
    congr 1
    have hP' : ∀ r, P * (P * r) = P * r := fun r => by rw [← mul_assoc, hP]
    have hM' : g • ((1 - P) * (M * P)) = (1 - P) * k.val * P := by
      rw [← mul_smul_comm, ← smul_mul_assoc, nsmul_eq_mul, ← hM]
      simp only [mul_sub, sub_mul, mul_assoc, hP, hP', mul_one, one_mul, sub_self, sub_zero]
    have e : (P + g • (1 - P)) * ((1 - P) * (M * P)) = g • ((1 - P) * (M * P)) := by
      simp only [mul_add, add_mul, mul_sub, sub_mul, mul_assoc, hP, hP', mul_one, one_mul, sub_self, sub_zero,
        smul_mul_assoc, zero_add, smul_zero, add_zero, add_sub_cancel_left]
    rw [pow_one, ← nsmul_eq_mul, mul_add _ _ ((1 - P) * _), e, hM']
    simp only [mul_add, add_mul, mul_sub, sub_mul, mul_assoc, hP, hP', mul_one, one_mul, sub_self, sub_zero,
        smul_mul_assoc, mul_smul_comm, zero_add, add_zero, smul_zero, smul_sub, smul_add]
    abel

/- English proof (translation)
Take `⟨y, rfl⟩` from `red_surjective g n u`. Establish `hP' : ∀ r, P * (P * r) = P * r` using `fun r => by rw [← mul_assoc, hP]`. Take `⟨k, h1, h2⟩` from `exists_unit (1 + (1 - P) * ((y.val - 1) * P)) (red g n y) (by`. Simplify using `only [map_add, map_mul, map_sub, map_one]`. Express the relevant statement in the definitionally equal form `1 + _ * (((red g n y).val - 1) * _) = _`.

Rewrite using `[hu.2, hu.1, add_sub_cancel])`. Take `⟨k', h3, h4⟩` from `exists_unit (1 + (g : Matrix (Fin n) (Fin n) ℤ_[g]) ^ (m + 1) * ((1 - P) * ((y.val - 1) * P))) 1 (by simp only [map_add, map_mul, map_pow, red_nat, map_one, pow_succ, mul_zero, zero_mul, add_zero, Units.val_one])`. Use `⟨k, k', h2, h4, Units.ext ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(dd hP _).val * ι k.val = ι k'.val * (dd hP _).val`. Rewrite using `[dd_val, ← map_mul, ← map_mul, h1, h3]`.

Use `congr 1`. Generalize the expression as in `y.val - 1 = z`. Rewrite using `[← Nat.cast_pow, ← nsmul_eq_mul]`. Simplify using `only [mul_add, add_mul, mul_sub, sub_mul, mul_assoc, hP, hP', mul_one, one_mul, sub_self, sub_zero, smul_mul_assoc, mul_smul_comm, zero_add, add_zero, smul_zero, smul_sub, smul_add]`. Normalize the expressions using the abelian group laws.
-/
theorem conj_down (hP : P * P = P) {u : Gn g n} (hu : u ∈ U (1 - φ P) (φ P)) (m : ℕ) :
    ∃ k k', red g n k = u ∧ red g n k' = 1 ∧ dd hP (m + 1) * inc g n k = inc g n k' * dd hP (m + 1) := by
  obtain ⟨y, rfl⟩ := red_surjective g n u
  have hP' : ∀ r, P * (P * r) = P * r := fun r => by rw [← mul_assoc, hP]
  obtain ⟨k, h1, h2⟩ := exists_unit (1 + (1 - P) * ((y.val - 1) * P)) (red g n y) (by
    simp only [map_add, map_mul, map_sub, map_one]
    change 1 + _ * (((red g n y).val - 1) * _) = _
    rw [hu.2, hu.1, add_sub_cancel])
  obtain ⟨k', h3, h4⟩ := exists_unit (1 + (g : Matrix (Fin n) (Fin n) ℤ_[g]) ^ (m + 1) * ((1 - P) * ((y.val - 1) * P)))
    1 (by simp only [map_add, map_mul, map_pow, red_nat, map_one, pow_succ, mul_zero, zero_mul, add_zero, Units.val_one])
  refine ⟨k, k', h2, h4, Units.ext ?_⟩
  change (dd hP _).val * ι k.val = ι k'.val * (dd hP _).val
  rw [dd_val, ← map_mul, ← map_mul, h1, h3]
  congr 1
  generalize y.val - 1 = z
  rw [← Nat.cast_pow, ← nsmul_eq_mul]
  simp only [mul_add, add_mul, mul_sub, sub_mul, mul_assoc, hP, hP', mul_one, one_mul,
    sub_self, sub_zero, smul_mul_assoc, mul_smul_comm, zero_add, add_zero, smul_zero, smul_sub, smul_add]
  abel

/- English proof (translation)
Establish `hp : φ P * φ P = φ P` using `by rw [← map_mul, hP]`. Proceed by induction on `m with`. Consider the case `zero`. Introduce `v _ h`. Use `Subtype.ext (IwahoriInj.eq_zero_of_fixed hπ isCompact_KOne (IwahoriInj.mem_fixed.2 ?_) (by simpa [dd_zero] using h))` and prove the remaining obligations.

Introduce and unpack `_ ⟨k, hk, rfl⟩`. Conclude with `(mem_principalCongruenceFixedVectors_iff π _).1 v.2 k hk`. Consider the case `succ m ih`. Introduce `v hv h`. Use `set t := S (repK π) (U (1 - φ P) (φ P)) v with ht`.

Establish `k1 : ∀ k, red g n k ∈ U (φ P) (1 - φ P) → π (inc g n k) (π (dd hP 1) t) = π (dd hP 1) t` using `fun k hk => by`. Take `⟨k', h1, h2⟩` from `conj_up hP hk`. Rewrite using `[← Module.End.mul_apply, ← map_mul, ← h2, map_mul, Module.End.mul_apply, ← repK_red, ht, S_left h1]`. Establish `k2` using `ih ⟨π (dd hP 1) t, (mem_principalCongruenceFixedVectors_iff π _).2 fun k hk => k1 k (hk ▸ one_mem _)⟩ (fun u hu => by`. Take `⟨k, rfl⟩` from `red_surjective g n u`.

Conclude with `Subtype.ext ((repK_red π k _).trans (k1 k hu))) (by`. Use `haveI := Fintype.ofFinite (U (1 - φ P) (φ P))`. Express the relevant statement in the definitionally equal form `π (dd hP m) (π (dd hP 1) t) ∈ _`. Rewrite using `[← Module.End.mul_apply, ← map_mul, ← dd_succ, ht, S_apply, Submodule.coe_sum, map_sum]`. Use `Submodule.sum_mem _ fun u _ => ?_` and prove the remaining obligations.

Take `⟨k, k', h1, h2, h3⟩` from `conj_down hP u.2 m`. Rewrite using `[← h1, repK_red, ← Module.End.mul_apply, ← map_mul, h3, map_mul, Module.End.mul_apply]`. Conclude with `IwahoriInj.apply_mem_twKer (H := KOne g n) ⟨k', h2, rfl⟩ h)`. Establish `k3 : t = 0`. Use `congrArg (fun w : fixK1 π => π (dd hP 1)⁻¹ w) k2` as an intermediate fact.

Simplify using `only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel] at this`. Conclude with `Subtype.ext (by simpa using this)`. Conclude with `oppInj matrix_regular hp (by simp only [mul_sub, sub_mul, hp, mul_one, one_mul, sub_self, sub_zero]) (by rw [mul_sub, hp, mul_one, sub_self]) (by rw [sub_mul, hp, one_mul, sub_self]) v hv k3`.
-/
theorem eq_zero_of_mem_twKer {π : Representation ℂ (GL (Fin n) ℚ_[g]) V} (hπ : IsSmooth π) (hP : P * P = P) (m : ℕ) :
    ∀ v : fixK1 π, (∀ u ∈ U (φ P) (1 - φ P), repK π u v = v) → π (dd hP m) v ∈ twKer π (KOne g n) 1 → v = 0 := by
  have hp : φ P * φ P = φ P := by rw [← map_mul, hP]
  induction m with
  | zero =>
    intro v _ h
    refine Subtype.ext (IwahoriInj.eq_zero_of_fixed hπ isCompact_KOne (IwahoriInj.mem_fixed.2 ?_)
      (by simpa [dd_zero] using h))
    rintro _ ⟨k, hk, rfl⟩
    exact (mem_principalCongruenceFixedVectors_iff π _).1 v.2 k hk
  | succ m ih =>
    intro v hv h
    set t := S (repK π) (U (1 - φ P) (φ P)) v with ht
    have k1 : ∀ k, red g n k ∈ U (φ P) (1 - φ P) → π (inc g n k) (π (dd hP 1) t) = π (dd hP 1) t := fun k hk => by
      obtain ⟨k', h1, h2⟩ := conj_up hP hk
      rw [← Module.End.mul_apply, ← map_mul, ← h2, map_mul, Module.End.mul_apply, ← repK_red, ht, S_left h1]
    have k2 := ih ⟨π (dd hP 1) t, (mem_principalCongruenceFixedVectors_iff π _).2 fun k hk => k1 k (hk ▸ one_mem _)⟩ (fun u hu => by
      obtain ⟨k, rfl⟩ := red_surjective g n u
      exact Subtype.ext ((repK_red π k _).trans (k1 k hu))) (by
      haveI := Fintype.ofFinite (U (1 - φ P) (φ P))
      change π (dd hP m) (π (dd hP 1) t) ∈ _
      rw [← Module.End.mul_apply, ← map_mul, ← dd_succ, ht, S_apply, Submodule.coe_sum, map_sum]
      refine Submodule.sum_mem _ fun u _ => ?_
      obtain ⟨k, k', h1, h2, h3⟩ := conj_down hP u.2 m
      rw [← h1, repK_red, ← Module.End.mul_apply, ← map_mul, h3, map_mul, Module.End.mul_apply]
      exact IwahoriInj.apply_mem_twKer (H := KOne g n) ⟨k', h2, rfl⟩ h)
    have k3 : t = 0 := by
      have := congrArg (fun w : fixK1 π => π (dd hP 1)⁻¹ w) k2
      simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel] at this
      exact Subtype.ext (by simpa using this)
    exact oppInj matrix_regular hp (by simp only [mul_sub, sub_mul, hp, mul_one, one_mul, sub_self, sub_zero])
      (by rw [mul_sub, hp, mul_one, sub_self]) (by rw [sub_mul, hp, one_mul, sub_self]) v hv k3

/- English proof (translation)
Set `E : Matrix (Fin n) (Fin n) ℚ_[g]` to `Matrix.single i j 1`. Establish `hE : E * E = 0` using `Matrix.single_mul_single_of_ne _ _ _ _ hij.symm _`. Set `f : GL (Fin n) ℚ_[g] → ℝ` to `fun x => ‖(x⁻¹ * un E hE * x).val i j‖`. Establish `hf : Continuous f` using `((Units.continuous_val.comp (by fun_prop)).matrix_elem i j).norm`. Take `⟨B, hB⟩` from `(hC.image hf).bddAbove`.

Establish `hd : ∀ m, f (dd hP m) = (g : ℝ) ^ m` using `fun m => by`. Establish `e : ((dd hP m)⁻¹ * un E hE * dd hP m).val = 1 + ((g : ℚ_[g]) ^ m)⁻¹ • E`. Rewrite using `[Units.val_mul, Units.val_mul, un_val, mul_add, add_mul, mul_one, Units.inv_mul]`. Express the relevant statement in the definitionally equal form `_ + (ι P + ((g : ℚ_[g]) ^ m)⁻¹ • (1 - ι P)) * E * (ι P + (g : ℚ_[g]) ^ m • (1 - ι P)) = _`. Simplify using `only [E, mul_add, add_mul, mul_sub, sub_mul, h1, h2, mul_one, one_mul, sub_self, sub_zero, smul_mul_assoc, mul_smul_comm, zero_add, add_zero, smul_zero]`.

Simplify using `only [f, e]`. Simplify using `[E, Matrix.one_apply_ne hij]`. Establish `h1 : (1 : ℝ) < g` using `by exact_mod_cast (Fact.out : g.Prime).one_lt`. Take `⟨N, hN⟩` from `pow_unbounded_of_one_lt B h1`. Use `(Set.finite_lt_nat N).subset ?_` and prove the remaining obligations.

Introduce and unpack `m ⟨z, hz, c, hc, e⟩`. Establish `: f (dd hP m) = f c`. Simplify using `only [f, e]`. Rewrite using `[mul_inv_rev, mul_assoc, mul_assoc, ← mul_assoc _ z, Subgroup.mem_center_iff.1 hz, mul_assoc, inv_mul_cancel_left, mul_assoc]`. Conclude with `(pow_lt_pow_iff_right₀ h1).1 ((hd m ▸ this ▸ hB ⟨c, hc, rfl⟩).trans_lt hN)`.
-/
theorem finite_of_compact (hP : P * P = P) {i j : Fin n} (hij : i ≠ j)
    (h1 : ι P * Matrix.single i j 1 = 0) (h2 : Matrix.single i j 1 * ι P = Matrix.single i j 1)
    {C : Set (GL (Fin n) ℚ_[g])} (hC : IsCompact C) :
    {m | ∃ z ∈ Subgroup.center (GL (Fin n) ℚ_[g]), ∃ c ∈ C, dd hP m = z * c}.Finite := by
  let E : Matrix (Fin n) (Fin n) ℚ_[g] := Matrix.single i j 1
  have hE : E * E = 0 := Matrix.single_mul_single_of_ne _ _ _ _ hij.symm _
  let f : GL (Fin n) ℚ_[g] → ℝ := fun x => ‖(x⁻¹ * un E hE * x).val i j‖
  have hf : Continuous f := ((Units.continuous_val.comp (by fun_prop)).matrix_elem i j).norm
  obtain ⟨B, hB⟩ := (hC.image hf).bddAbove
  have hd : ∀ m, f (dd hP m) = (g : ℝ) ^ m := fun m => by
    have e : ((dd hP m)⁻¹ * un E hE * dd hP m).val = 1 + ((g : ℚ_[g]) ^ m)⁻¹ • E := by
      rw [Units.val_mul, Units.val_mul, un_val, mul_add, add_mul, mul_one, Units.inv_mul]
      change _ + (ι P + ((g : ℚ_[g]) ^ m)⁻¹ • (1 - ι P)) * E * (ι P + (g : ℚ_[g]) ^ m • (1 - ι P)) = _
      simp only [E, mul_add, add_mul, mul_sub, sub_mul, h1, h2, mul_one, one_mul,
        sub_self, sub_zero, smul_mul_assoc, mul_smul_comm, zero_add, add_zero, smul_zero]
    simp only [f, e]
    simp [E, Matrix.one_apply_ne hij]
  have h1 : (1 : ℝ) < g := by exact_mod_cast (Fact.out : g.Prime).one_lt
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt B h1
  refine (Set.finite_lt_nat N).subset ?_
  rintro m ⟨z, hz, c, hc, e⟩
  have : f (dd hP m) = f c := by
    simp only [f, e]
    rw [mul_inv_rev, mul_assoc, mul_assoc, ← mul_assoc _ z, Subgroup.mem_center_iff.1 hz, mul_assoc,
      inv_mul_cancel_left, mul_assoc]
  exact (pow_lt_pow_iff_right₀ h1).1 ((hd m ▸ this ▸ hB ⟨c, hc, rfl⟩).trans_lt hN)

/- English proof (translation)
Use `(FiniteGL.isCuspidal_iff_twoBlocks _).2 fun a h0 ha v hv => ?_` and prove the remaining obligations. Set `P : Matrix (Fin n) (Fin n) ℤ_[g]` to `Matrix.diagonal fun i => if (i : ℕ) < a then 1 else 0`. Establish `hP : P * P = P`. Simplify using `only [P, Matrix.diagonal_mul_diagonal]`. Use `congr 1`.

Use function extensionality and compare the values at `i`. Apply the tactic sequence `split_ifs <;> simp`. Establish `hmap : ∀ {A : Type} [CommRing A] (f : ℤ_[g] →+* A), f.mapMatrix P = Matrix.diagonal fun i : Fin n => if (i : ℕ) < a then 1 else 0` using `fun f => by`. Use extensionality with `i j`. Simplify using `[P, Matrix.diagonal_apply, apply_ite f]`.

Establish `hv' : ∀ u ∈ U (φ P) (1 - φ P), repK π u v = v` using `fun u hu => hv u fun i j hij => by`. Establish `a1` using `congrFun (congrFun hu.1 i) j`. Establish `a2` using `congrFun (congrFun hu.2 i) j`. Rewrite `a1` using `[hmap, Matrix.diagonal_mul]`. Rewrite `a2` using `[hmap, mul_sub, mul_one, Matrix.sub_apply, Matrix.mul_diagonal]`.

Simplify using `only [FiniteGL.twoBlocks] at hij`. Distinguish the cases in `hi : (i : ℕ) < a`. Distinguish the cases in `hj : (j : ℕ) < a`. Rewrite using `[← a2, if_pos hj, mul_one, sub_self]`. Simplify using `[hi, hj] at hij`.

Rewrite using `[← a1, if_neg hi, zero_mul]`. Assume the negation of the conclusion as `hne`. Take `⟨l, hl⟩` from `exists_dual_frequently (fun m => (twKer π (KOne g n) 1).mkQ (π (dd hP m) v)) fun m h => hne (eq_zero_of_mem_twKer hπ.1 hP m v hv' ((Submodule.Quotient.mk_eq_zero _).1 h))`. Take `⟨C, hC, h⟩` from `hπ.2 v (l ∘ₗ (twKer π (KOne g n) 1).mkQ) (TameGen.principalCongruenceFixedVectors_le_smoothVectors _ ((mem_principalCongruenceFixedVectors_iff _ _).2 fun k hk => by`. Use `LinearMap.ext fun w => congrArg l ((Submodule.Quotient.eq _).2 ?_)` and prove the remaining obligations.

Conclude with `IwahoriInj.sub_mem_twKer (inv_mem (show inc g n k ∈ KOne g n from ⟨k, hk, rfl⟩)) w))`. Use `hl ((finite_of_compact hP (i := ⟨a, ha⟩) (j := ⟨0, h0.trans ha⟩) (by simp; omega) ?_ ?_ hC).subset fun m hm => h _ hm)` and prove the remaining obligations. Use extensionality with `i j`. Rewrite using `[hmap, Matrix.diagonal_mul, Matrix.single_apply]`. Apply the tactic sequence `split_ifs with c1 c2 <;> simp`.

Rewrite `c1` using `[← c2.1]`. Simplify using `at c1`. Use extensionality with `i j`. Rewrite using `[hmap, Matrix.mul_diagonal, Matrix.single_apply]`. Apply the tactic sequence `split_ifs with c1 c2 <;> simp`.

Rewrite `c2` using `[← c1.2]`. Conclude with `c2 h0`.
-/
theorem isCuspidal_repK {π : Representation ℂ (GL (Fin n) ℚ_[g]) V} (hπ : IsSupercuspidal π) :
    FiniteGL.IsCuspidal (repK π) := by
  refine (FiniteGL.isCuspidal_iff_twoBlocks _).2 fun a h0 ha v hv => ?_
  let P : Matrix (Fin n) (Fin n) ℤ_[g] := Matrix.diagonal fun i => if (i : ℕ) < a then 1 else 0
  have hP : P * P = P := by
    simp only [P, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    split_ifs <;> simp
  have hmap : ∀ {A : Type} [CommRing A] (f : ℤ_[g] →+* A),
      f.mapMatrix P = Matrix.diagonal fun i : Fin n => if (i : ℕ) < a then 1 else 0 := fun f => by
    ext i j
    simp [P, Matrix.diagonal_apply, apply_ite f]
  have hv' : ∀ u ∈ U (φ P) (1 - φ P), repK π u v = v := fun u hu => hv u fun i j hij => by
    have a1 := congrFun (congrFun hu.1 i) j
    have a2 := congrFun (congrFun hu.2 i) j
    rw [hmap, Matrix.diagonal_mul] at a1
    rw [hmap, mul_sub, mul_one, Matrix.sub_apply, Matrix.mul_diagonal] at a2
    simp only [FiniteGL.twoBlocks] at hij
    by_cases hi : (i : ℕ) < a
    · by_cases hj : (j : ℕ) < a
      · rw [← a2, if_pos hj, mul_one, sub_self]
      · simp [hi, hj] at hij
    · rw [← a1, if_neg hi, zero_mul]
  by_contra hne
  obtain ⟨l, hl⟩ := exists_dual_frequently (fun m => (twKer π (KOne g n) 1).mkQ (π (dd hP m) v)) fun m h =>
    hne (eq_zero_of_mem_twKer hπ.1 hP m v hv' ((Submodule.Quotient.mk_eq_zero _).1 h))
  obtain ⟨C, hC, h⟩ := hπ.2 v (l ∘ₗ (twKer π (KOne g n) 1).mkQ) (TameGen.principalCongruenceFixedVectors_le_smoothVectors _ ((mem_principalCongruenceFixedVectors_iff _ _).2 fun k hk => by
    refine LinearMap.ext fun w => congrArg l ((Submodule.Quotient.eq _).2 ?_)
    exact IwahoriInj.sub_mem_twKer (inv_mem (show inc g n k ∈ KOne g n from ⟨k, hk, rfl⟩)) w))
  refine hl ((finite_of_compact hP (i := ⟨a, ha⟩) (j := ⟨0, h0.trans ha⟩) (by simp; omega) ?_ ?_ hC).subset
    fun m hm => h _ hm)
  · ext i j
    rw [hmap, Matrix.diagonal_mul, Matrix.single_apply]
    split_ifs with c1 c2 <;> simp
    rw [← c2.1] at c1
    simp at c1
  · ext i j
    rw [hmap, Matrix.mul_diagonal, Matrix.single_apply]
    split_ifs with c1 c2 <;> simp
    rw [← c1.2] at c2
    exact c2 h0

/- English proof (translation)
Introduce `_ _ _ h _` and use `isCuspidal_repK h.2.2`.
-/
theorem depthZeroCuspidal : ∀ (g : ℕ) [Fact g.Prime], TameGen.DepthZeroCuspidal g :=
  fun _ _ _ h _ => isCuspidal_repK h.2.2

end GlobalTheory.DepthZeroCusp
