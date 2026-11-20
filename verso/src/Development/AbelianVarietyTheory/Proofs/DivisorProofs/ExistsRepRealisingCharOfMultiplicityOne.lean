import Mathlib
import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharTraceMulIdempotent
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.AsAlgebraHomSurjectiveOfFinrankIntertwiningMapEq
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.FiniteGroupFunctionPairingCharacterEqFinrankInte
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.FiniteGroupFunctionPairingSelfIrreducibleAlgClos

open GlobalTheory.FinGL Formalism.L2.DIV Module

noncomputable section

namespace GlobalTheory.MultOneRealised

variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]

def leftReg (K G : Type) [Field K] [Group G] : Representation K G (MonoidAlgebra K G) where
  toFun g := LinearMap.mulLeft K (MonoidAlgebra.single g 1)
  map_one' := by rw [← MonoidAlgebra.one_def]; exact LinearMap.mulLeft_one K _
  map_mul' a b := by
    refine LinearMap.ext fun v => ?_
    simp [← mul_assoc, MonoidAlgebra.single_mul_single]

open Module in
variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G] in
/- English proof (translation)
Use `haveI : Nontrivial (ρ.IntertwiningMap ρ) := Module.nontrivial_of_finrank_eq_succ h1`. Take `⟨c, hc⟩` from `(finrank_eq_one_iff_of_nonzero' (1 : ρ.IntertwiningMap ρ) one_ne_zero).1 h1 ⟨T, fun g => hT g⟩`. Establish `hT' : T = c • 1`. Use `congrArg Representation.IntertwiningMap.toLinearMap hc` as an intermediate fact. Rewrite `this` using `[Representation.IntertwiningMap.toLinearMap_smul]`.

Establish `h' : c • (1 : Module.End L (Fin n → L)) = T` using `this`. Conclude with `h'.symm`. Substitute `hT'` using the available equality. Simplify using `[LinearMap.trace_one, mul_comm, smul_smul]`.
-/
private lemma natCast_smul_eq_trace_smul_one_of_commute {L G : Type} [Field L] [Group G] {n : ℕ}
    (ρ : Representation L G (Fin n → L)) (h1 : Module.finrank L (ρ.IntertwiningMap ρ) = 1)
    (T : Module.End L (Fin n → L)) (hT : ∀ g, T * ρ g = ρ g * T) :
    (n : L) • T = LinearMap.trace L _ T • 1 := by
  haveI : Nontrivial (ρ.IntertwiningMap ρ) := Module.nontrivial_of_finrank_eq_succ h1
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : ρ.IntertwiningMap ρ) one_ne_zero).1 h1
    ⟨T, fun g => hT g⟩
  have hT' : T = c • 1 := by
    have := congrArg Representation.IntertwiningMap.toLinearMap hc
    rw [Representation.IntertwiningMap.toLinearMap_smul] at this
    have h' : c • (1 : Module.End L (Fin n → L)) = T := this
    exact h'.symm
  subst hT'
  simp [LinearMap.trace_one, mul_comm, smul_smul]

open Module in
variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G] in
/- English proof (translation)
Use `set T : Module.End L (Fin n → L) := ∑ x : G, ρ x * ρ b * ρ x⁻¹ with hTdef`. Establish `hT : ∀ g, T * ρ g = ρ g * T`. Introduce `g`. Rewrite using `[hTdef, Finset.sum_mul, Finset.mul_sum]`. Use `Fintype.sum_equiv (Equiv.mulLeft g⁻¹) _ _ fun x => ?_` and prove the remaining obligations.

Simplify using `only [Equiv.coe_mulLeft, ← map_mul, mul_inv_rev, inv_inv, ← mul_assoc, mul_inv_cancel, one_mul]`. Establish `key` using `natCast_smul_eq_trace_smul_one_of_commute ρ h1 T hT`. Establish `htr : LinearMap.trace L _ T = Fintype.card G * LinearMap.trace L _ (ρ b)`. Establish `hx : ∀ x : G, LinearMap.trace L _ (ρ x * ρ b * ρ x⁻¹) = LinearMap.trace L _ (ρ b)`. Introduce `x`.

Rewrite using `[LinearMap.trace_mul_comm, ← mul_assoc, ← map_mul, ← map_mul, inv_mul_cancel, one_mul]`. Rewrite using `[hTdef, map_sum]`. Simplify using `[hx]`. Use `congrArg (fun S => LinearMap.trace L _ (ρ a * S)) key` as an intermediate fact. Simplify using `only [mul_smul_comm, map_smul, mul_one, smul_eq_mul] at this`.

Rewrite `this` using `[htr]`. Rewrite using `[← this, hTdef]`. Simplify using `only [Finset.mul_sum, map_sum, map_mul, mul_assoc]`.
-/
private lemma natCast_mul_sum_trace_conj_eq_mul_trace {L G : Type} [Field L] [Group G] [Fintype G] {n : ℕ}
    (ρ : Representation L G (Fin n → L)) (h1 : Module.finrank L (ρ.IntertwiningMap ρ) = 1)
    (a b : G) :
    (n : L) * ∑ x : G, LinearMap.trace L _ (ρ (a * (x * b * x⁻¹))) =
      Fintype.card G * LinearMap.trace L _ (ρ b) * LinearMap.trace L _ (ρ a) := by
  set T : Module.End L (Fin n → L) := ∑ x : G, ρ x * ρ b * ρ x⁻¹ with hTdef
  have hT : ∀ g, T * ρ g = ρ g * T := by
    intro g
    rw [hTdef, Finset.sum_mul, Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft g⁻¹) _ _ fun x => ?_
    simp only [Equiv.coe_mulLeft, ← map_mul, mul_inv_rev, inv_inv, ← mul_assoc, mul_inv_cancel, one_mul]
  have key := natCast_smul_eq_trace_smul_one_of_commute ρ h1 T hT
  have htr : LinearMap.trace L _ T = Fintype.card G * LinearMap.trace L _ (ρ b) := by
    have hx : ∀ x : G, LinearMap.trace L _ (ρ x * ρ b * ρ x⁻¹) = LinearMap.trace L _ (ρ b) := by
      intro x
      rw [LinearMap.trace_mul_comm, ← mul_assoc, ← map_mul, ← map_mul, inv_mul_cancel, one_mul]
    rw [hTdef, map_sum]
    simp [hx]
  have := congrArg (fun S => LinearMap.trace L _ (ρ a * S)) key
  simp only [mul_smul_comm, map_smul, mul_one, smul_eq_mul] at this
  rw [htr] at this
  rw [← this, hTdef]
  simp only [Finset.mul_sum, map_sum, map_mul, mul_assoc]

open Module in
variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G] in
/- English proof (translation)
Rewrite using `[map_mul ρ (g * y), map_mul ρ g, LinearMap.trace_mul_comm L (ρ g * ρ y) (ρ g⁻¹), ← mul_assoc, ← map_mul ρ g⁻¹ g, inv_mul_cancel, map_one, one_mul]`.
-/
private lemma trace_rep_conj_eq {L G : Type} [Field L] [Group G] {V : Type} [AddCommGroup V] [Module L V]
    (ρ : Representation L G V) (g y : G) :
    LinearMap.trace L V (ρ (g * y * g⁻¹)) = LinearMap.trace L V (ρ y) := by
  rw [map_mul ρ (g * y), map_mul ρ g, LinearMap.trace_mul_comm L (ρ g * ρ y) (ρ g⁻¹), ← mul_assoc,
    ← map_mul ρ g⁻¹ g, inv_mul_cancel, map_one, one_mul]

open Module in
variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G] in
/- English proof (translation)
Use `set Z : Module.End L (Fin n → L) := ∑ y : G, LinearMap.trace L _ (ρ y⁻¹) • ρ y with hZdef`. Establish `hZ : ∀ g, Z * ρ g = ρ g * Z`. Introduce `g`. Rewrite using `[hZdef, Finset.sum_mul, Finset.mul_sum]`. Use `symm`.

Use `Fintype.sum_equiv ((MulAut.conj g).toEquiv) _ _ fun y => ?_` and prove the remaining obligations. Simplify using `only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, mul_inv_rev, inv_inv, smul_mul_assoc, mul_smul_comm, ← map_mul]`. Rewrite using `[← mul_assoc g, trace_rep_conj_eq, inv_mul_cancel_right]`. Establish `key` using `natCast_smul_eq_trace_smul_one_of_commute ρ h1 Z hZ`. Establish `htr : LinearMap.trace L _ Z = Fintype.card G`.

Rewrite using `[hZdef, map_sum, ← hpair]`. Simplify using the standard rewrite rules. Use `congrArg (fun S => LinearMap.trace L _ (S * ρ b)) key` as an intermediate fact. Simplify using `only [smul_mul_assoc, map_smul, one_mul, smul_eq_mul, htr] at this`. Rewrite using `[← this, hZdef, Finset.sum_mul, map_sum]`.

Simplify using `[map_mul, smul_mul_assoc]`.
-/
private lemma natCast_mul_sum_trace_inv_mul_trace_mul_eq {L G : Type} [Field L] [Group G] [Fintype G] {n : ℕ}
    (ρ : Representation L G (Fin n → L)) (h1 : Module.finrank L (ρ.IntertwiningMap ρ) = 1)
    (hpair : ∑ y : G, LinearMap.trace L _ (ρ y⁻¹) * LinearMap.trace L _ (ρ y) = Fintype.card G)
    (b : G) :
    (n : L) * ∑ y : G, LinearMap.trace L _ (ρ y⁻¹) * LinearMap.trace L _ (ρ (y * b)) =
      Fintype.card G * LinearMap.trace L _ (ρ b) := by
  set Z : Module.End L (Fin n → L) := ∑ y : G, LinearMap.trace L _ (ρ y⁻¹) • ρ y with hZdef
  have hZ : ∀ g, Z * ρ g = ρ g * Z := by
    intro g
    rw [hZdef, Finset.sum_mul, Finset.mul_sum]
    symm
    refine Fintype.sum_equiv ((MulAut.conj g).toEquiv) _ _ fun y => ?_
    simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, mul_inv_rev,
      inv_inv, smul_mul_assoc, mul_smul_comm, ← map_mul]
    rw [← mul_assoc g, trace_rep_conj_eq, inv_mul_cancel_right]
  have key := natCast_smul_eq_trace_smul_one_of_commute ρ h1 Z hZ
  have htr : LinearMap.trace L _ Z = Fintype.card G := by
    rw [hZdef, map_sum, ← hpair]
    simp
  have := congrArg (fun S => LinearMap.trace L _ (S * ρ b)) key
  simp only [smul_mul_assoc, map_smul, one_mul, smul_eq_mul, htr] at this
  rw [← this, hZdef, Finset.sum_mul, map_sum]
  simp [map_mul, smul_mul_assoc]

open Module in
variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G] in
/- English proof (translation)
Rewrite using `[LinearMap.trace_eq_matrix_trace K (MonoidAlgebra.basis G K), Matrix.trace]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.diag_apply, LinearMap.toMatrix_apply, MonoidAlgebra.basis_apply]`. Simplify using `only [_root_.GlobalTheory.MultOneRealised.leftReg, MonoidHom.coe_mk, OneHom.coe_mk, Module.End.mul_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply, ← mul_assoc, MonoidAlgebra.single_mul_single, mul_one]`. Simplify using `[MonoidAlgebra.basis, MonoidAlgebra.single_mul_apply, mul_assoc]`.
-/
private lemma trace_leftReg_mul_mulRight_eq_sum_coeff {K G : Type} [Field K] [Group G] [Fintype G]
    (f : MonoidAlgebra K G) (t : G) :
    LinearMap.trace K _ (_root_.GlobalTheory.MultOneRealised.leftReg K G t * LinearMap.mulRight K f) =
      ∑ x : G, f.coeff (x⁻¹ * t⁻¹ * x) := by
  classical
  rw [LinearMap.trace_eq_matrix_trace K (MonoidAlgebra.basis G K), Matrix.trace]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, MonoidAlgebra.basis_apply]
  simp only [_root_.GlobalTheory.MultOneRealised.leftReg, MonoidHom.coe_mk, OneHom.coe_mk, Module.End.mul_apply,
    LinearMap.mulLeft_apply, LinearMap.mulRight_apply, ← mul_assoc, MonoidAlgebra.single_mul_single, mul_one]
  simp [MonoidAlgebra.basis, MonoidAlgebra.single_mul_apply, mul_assoc]

open Module in
variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G] in

/- English proof (translation)
Introduce `K _ _ G _ _ χ hχ P _ ψ hsum`. Take `⟨n₀, ρ, hirr, hch⟩` from `hχ`. Use `haveI : CharZero (AlgebraicClosure K) := charZero_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective`. Establish `hch' : ∀ g, LinearMap.trace (AlgebraicClosure K) _ (ρ g) = algebraMap K (AlgebraicClosure K) (χ g)` using `hch`. Establish `hirrc : _root_.GlobalTheory.BI.IsIrrChar (AlgebraicClosure K) (AlgebraicClosure K) (fun g => algebraMap K (AlgebraicClosure K) (χ g))` using `⟨n₀, ρ, hirr, fun g => by rw [hch g]; rfl⟩`.

Establish `hp1` using `_root_.GlobalTheory.BI.pair_self_of_isIrrChar_algClosed _ G _ hirrc`. Establish `hp2` using `_root_.GlobalTheory.BI.pair_character_eq_finrank (AlgebraicClosure K) (AlgebraicClosure K) G _ _ ρ ρ`. Establish `hfun : (fun g => algebraMap (AlgebraicClosure K) (AlgebraicClosure K) (ρ.character g)) = fun g => algebraMap K (AlgebraicClosure K) (χ g)`. Use function extensionality and compare the values at `g`. Rewrite using `[hch g]`.

Both sides reduce to the same expression. Rewrite `hp2` using `[hfun, hp1]`. Establish `h1 : Module.finrank (AlgebraicClosure K) (ρ.IntertwiningMap ρ) = 1`. Conclude with `hp2.symm` after adjusting the coercions. Establish `hpair : ∑ y : G, LinearMap.trace (AlgebraicClosure K) _ (ρ y⁻¹) * LinearMap.trace (AlgebraicClosure K) _ (ρ y) = Fintype.card G`.

Use `hp1` as an intermediate fact. Unfold `_root_.GlobalTheory.BI.pair at this`. Rewrite `this` using `[finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card, inv_mul_eq_one₀ (Nat.cast_ne_zero.2 Fintype.card_ne_zero)]`. Rewrite using `[this]`. Conclude with `Finset.sum_congr rfl fun y _ => by rw [hch', hch', mul_comm]`.

Establish `hn : algebraMap K (AlgebraicClosure K) (χ 1) = n₀`. Rewrite using `[← hch', map_one, LinearMap.trace_one, Module.finrank_fin_fun]`. Establish `hAv : ∀ a b : G, (n₀ : AlgebraicClosure K) * ∑ x : G, algebraMap K (AlgebraicClosure K) (χ (a * (x * b * x⁻¹))) = Fintype.card G * algebraMap K (AlgebraicClosure K) (χ b) * algebraMap K (AlgebraicClosure K) (χ a)`. Introduce `a b`. Use `natCast_mul_sum_trace_conj_eq_mul_trace ρ h1 a b` as an intermediate fact.

Simplify `this` using `only [hch']`. Establish `hO : ∀ b : G, (n₀ : AlgebraicClosure K) * ∑ y : G, algebraMap K (AlgebraicClosure K) (χ y⁻¹) * algebraMap K (AlgebraicClosure K) (χ (y * b)) = Fintype.card G * algebraMap K (AlgebraicClosure K) (χ b)`. Introduce `b`. Use `natCast_mul_sum_trace_inv_mul_trace_mul_eq ρ h1 hpair b` as an intermediate fact. Simplify `this` using `only [hch']`.

Establish `hcl : ∀ g y : G, algebraMap K (AlgebraicClosure K) (χ (g * y * g⁻¹)) = algebraMap K (AlgebraicClosure K) (χ y)`. Introduce `g y`. Rewrite using `[← hch', ← hch', trace_rep_conj_eq]`. Establish `hn0 : (n₀ : AlgebraicClosure K) ≠ 0`. Take `⟨hnt, -⟩` from `_root_.GlobalTheory.asAlgebraHom_surjective_of_finrank_intertwiningMap_eq_one _ G _ ρ h1`.

Break down `Nat.eq_zero_or_pos n₀ with h0 | h0` into its components or cases. Substitute `h0` using the available equality. Conclude with `absurd hnt (not_nontrivial_iff_subsingleton.2 inferInstance)`. Conclude with `Nat.cast_ne_zero.2 h0.ne'`. Set `c : G → K` to `fun g => χ 1 / (Fintype.card G * Fintype.card P) * ∑ h : P, (((ψ h)⁻¹ : Kˣ) : K) * χ (h * g⁻¹)`.

Set `f : MonoidAlgebra K G` to `MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm c)`. Establish `hf : ∀ x, f.coeff x = c x` using `fun x => by simp [f]`. Establish `hP : (Fintype.card P : AlgebraicClosure K) ≠ 0` using `Nat.cast_ne_zero.2 Fintype.card_ne_zero`. Establish `hG : (Fintype.card G : AlgebraicClosure K) ≠ 0` using `Nat.cast_ne_zero.2 Fintype.card_ne_zero`. Use `set ι := algebraMap K (AlgebraicClosure K) with hι`.

Establish `hsum' : ∑ h : P, ι (χ h) * ι (((ψ h)⁻¹ : Kˣ) : K) = Fintype.card P`. Use `congrArg ι hsum` as an intermediate fact. Simplify `this` using `only [map_sum, map_mul, map_natCast]`. Establish `hψ : ∀ a b : P, ι (((ψ (a * b))⁻¹ : Kˣ) : K) = ι (((ψ a)⁻¹ : Kˣ) : K) * ι (((ψ b)⁻¹ : Kˣ) : K)`. Introduce `a b`.

Rewrite using `[map_mul, mul_inv, Units.val_mul, map_mul]`. Establish `hcyc : ∀ a b : G, ι (χ (a * b)) = ι (χ (b * a))`. Introduce `a b`. Rewrite using `[← hcl a (b * a)]`. Use `congr 2`.

Use `group`. Establish `hidem : f * f = f`. Use `MonoidAlgebra.ext (Finsupp.ext fun g => ?_)` and prove the remaining obligations. Rewrite using `[MonoidAlgebra.mul_apply_left, Finsupp.sum_fintype _ _ (by simp)]`. Simplify using `only [hf]`.

Apply `ι.injective` to reduce the goal to its premises. Establish `hinner : ∀ h k : G, ∑ y : G, ι (χ (h * y⁻¹)) * ι (χ (k * (y⁻¹ * g)⁻¹)) = Fintype.card G * ι (χ (h * k * g⁻¹)) / n₀`. Introduce `h k`. Rewrite using `[eq_div_iff hn0, ← hO (h * k * g⁻¹), mul_comm]`. Use `congr 1`.

Use `Fintype.sum_equiv (Equiv.mulRight h⁻¹) _ _ fun y => ?_` and prove the remaining obligations. Simplify using `only [Equiv.coe_mulRight]`. Rewrite using `[show k * (y⁻¹ * g)⁻¹ = k * g⁻¹ * y by group, hcyc (k * g⁻¹) y, show (y * h⁻¹)⁻¹ = h * y⁻¹ by group, show y * h⁻¹ * (h * k * g⁻¹) = y * (k * g⁻¹) by group]`. Simplify using `only [c, map_sum, map_mul, map_div₀, map_natCast, hn]`. Use `set A : AlgebraicClosure K := (n₀ : AlgebraicClosure K) / (Fintype.card G * Fintype.card P) with hA`.

Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun y _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun h _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum, Finset.mul_sum]`.

Conclude with `Finset.sum_congr rfl fun k _ => by ring`. Use `_ = ∑ h : P, ∑ k : P, A * A * (ι (((ψ h)⁻¹ : Kˣ) : K) * ι (((ψ k)⁻¹ : Kˣ) : K)) * (Fintype.card G * ι (χ (h * k * g⁻¹)) / n₀) := by`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun h _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.mul_sum, hinner]`. Use `_ = ∑ h : P, ∑ m : P, A * A * ι (((ψ m)⁻¹ : Kˣ) : K) * (Fintype.card G * ι (χ (m * g⁻¹)) / n₀) := by`. Use `Finset.sum_congr rfl fun h _ => ?_` and prove the remaining obligations. Use `Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun k => ?_` and prove the remaining obligations.

Simplify using `only [Equiv.coe_mulLeft, hψ, Subgroup.coe_mul, mul_assoc]`. Use `_ = A * ∑ m : P, ι (((ψ m)⁻¹ : Kˣ) : K) * ι (χ (m * g⁻¹)) := by`. Rewrite using `[Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.mul_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[hA]`.

Clear the denominators using the available nonvanishing facts. Establish `hI2 : ∀ t : G, ∑ x : G, c (x⁻¹ * t⁻¹ * x) = χ t`. Introduce `t`. Apply `ι.injective` to reduce the goal to its premises. Establish `hx : ∀ h : G, ∑ x : G, ι (χ (h * (x⁻¹ * t⁻¹ * x)⁻¹)) = Fintype.card G * ι (χ t) * ι (χ h) / n₀`.

Introduce `h`. Rewrite using `[eq_div_iff hn0, ← hAv h t, mul_comm]`. Use `congr 1`. Conclude with `Fintype.sum_equiv (Equiv.inv G) _ _ fun x => by simp [mul_assoc]`. Simplify using `only [c, map_sum, map_mul, map_div₀, map_natCast, hn]`.

Rewrite using `[← Finset.mul_sum, Finset.sum_comm]`. Repeatedly rewrite using `[← Finset.mul_sum, hx]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun h _ => by ring`.

Use `_ = ι (χ t) := by`. Rewrite using `[hsum']`. Clear the denominators using the available nonvanishing facts. Set `e : Module.End K (MonoidAlgebra K G)` to `LinearMap.mulRight K f`. Establish `he : e * e = e`.

Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Simplify using `[e, mul_assoc, hidem]`. Establish `hcomm : ∀ t, _root_.GlobalTheory.MultOneRealised.leftReg K G t * e = e * _root_.GlobalTheory.MultOneRealised.leftReg K G t`. Introduce `t`. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations.

Simplify using `[e, _root_.GlobalTheory.MultOneRealised.leftReg, mul_assoc]`. Take `⟨n, τ, hτ⟩` from `_root_.GlobalTheory.BI.isChar_trace_mul_idempotent K G _ (_root_.GlobalTheory.MultOneRealised.leftReg K G) e he hcomm`. Establish `htr : ∀ g, LinearMap.trace K (Fin n → K) (τ g) = χ g`. Introduce `g`. Use `hτ g` as an intermediate fact.

Simplify using `only [e] at this`. Rewrite `this` using `[trace_leftReg_mul_mulRight_eq_sum_coeff]`. Simplify using `only [hf, hI2, Algebra.algebraMap_self, RingHom.id_apply] at this`. Conclude with `this.symm`. Establish `hτ1 : Module.finrank K (τ.IntertwiningMap τ) = 1`.

Establish `hq` using `_root_.GlobalTheory.BI.pair_character_eq_finrank K (AlgebraicClosure K) G _ _ τ τ`. Establish `hfun' : (fun g => algebraMap K (AlgebraicClosure K) (τ.character g)) = fun g => algebraMap K (AlgebraicClosure K) (χ g)`. Use function extensionality and compare the values at `g`. Rewrite using `[show τ.character g = χ g from htr g]`. Rewrite `hq` using `[hfun', hp1]`.

Conclude with `hq.symm` after adjusting the coercions. Take `⟨hnt, hsurj⟩` from `_root_.GlobalTheory.asAlgebraHom_surjective_of_finrank_intertwiningMap_eq_one K G _ τ hτ1`. Use `⟨n, τ, ?_, hsurj, htr⟩` and prove the remaining obligations. Break down `Nat.eq_zero_or_pos n with h0 | h0` into its components or cases. Substitute `h0` using the available equality.

Conclude with `absurd hnt (not_nontrivial_iff_subsingleton.2 inferInstance)`. Conclude with `h0`.
-/
theorem _root_.GlobalTheory.MultOneRealised.exists_rep_of_mult_one : ∀ (K : Type) [Field K] [CharZero K] (G : Type) [Group G] [Fintype G] (χ : G → K), _root_.Formalism.L2.DIV.IsAbsIrrChar χ → ∀ (P : Subgroup G) [Fintype P] (ψ : P →* Kˣ), ∑ h : P, χ (h : G) * (((ψ h)⁻¹ : Kˣ) : K) = (Fintype.card P : K) → ∃ (n : ℕ) (τ : Representation K G (Fin n → K)), 0 < n ∧ Function.Surjective τ.asAlgebraHom ∧ ∀ g, LinearMap.trace K (Fin n → K) (τ g) = χ g := by
  intro K _ _ G _ _ χ hχ P _ ψ hsum
  classical
  obtain ⟨n₀, ρ, hirr, hch⟩ := hχ
  haveI : CharZero (AlgebraicClosure K) :=
    charZero_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective
  have hch' : ∀ g, LinearMap.trace (AlgebraicClosure K) _ (ρ g) =
      algebraMap K (AlgebraicClosure K) (χ g) := hch
  have hirrc : _root_.GlobalTheory.BI.IsIrrChar (AlgebraicClosure K) (AlgebraicClosure K)
      (fun g => algebraMap K (AlgebraicClosure K) (χ g)) :=
    ⟨n₀, ρ, hirr, fun g => by rw [hch g]; rfl⟩
  have hp1 := _root_.GlobalTheory.BI.pair_self_of_isIrrChar_algClosed _ G _ hirrc
  have hp2 := _root_.GlobalTheory.BI.pair_character_eq_finrank (AlgebraicClosure K)
    (AlgebraicClosure K) G _ _ ρ ρ
  have hfun : (fun g => algebraMap (AlgebraicClosure K) (AlgebraicClosure K) (ρ.character g)) =
      fun g => algebraMap K (AlgebraicClosure K) (χ g) := by
    funext g; rw [hch g]; rfl
  rw [hfun, hp1] at hp2
  have h1 : Module.finrank (AlgebraicClosure K) (ρ.IntertwiningMap ρ) = 1 := by
    exact_mod_cast hp2.symm
  have hpair : ∑ y : G, LinearMap.trace (AlgebraicClosure K) _ (ρ y⁻¹) *
      LinearMap.trace (AlgebraicClosure K) _ (ρ y) = Fintype.card G := by
    have := hp1
    unfold _root_.GlobalTheory.BI.pair at this
    rw [finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card,
      inv_mul_eq_one₀ (Nat.cast_ne_zero.2 Fintype.card_ne_zero)] at this
    rw [this]
    exact Finset.sum_congr rfl fun y _ => by rw [hch', hch', mul_comm]
  have hn : algebraMap K (AlgebraicClosure K) (χ 1) = n₀ := by
    rw [← hch', map_one, LinearMap.trace_one, Module.finrank_fin_fun]
  have hAv : ∀ a b : G, (n₀ : AlgebraicClosure K) *
      ∑ x : G, algebraMap K (AlgebraicClosure K) (χ (a * (x * b * x⁻¹))) =
      Fintype.card G * algebraMap K (AlgebraicClosure K) (χ b) *
        algebraMap K (AlgebraicClosure K) (χ a) := by
    intro a b
    have := natCast_mul_sum_trace_conj_eq_mul_trace ρ h1 a b
    simpa only [hch'] using this
  have hO : ∀ b : G, (n₀ : AlgebraicClosure K) * ∑ y : G, algebraMap K (AlgebraicClosure K) (χ y⁻¹) *
      algebraMap K (AlgebraicClosure K) (χ (y * b)) =
      Fintype.card G * algebraMap K (AlgebraicClosure K) (χ b) := by
    intro b
    have := natCast_mul_sum_trace_inv_mul_trace_mul_eq ρ h1 hpair b
    simpa only [hch'] using this
  have hcl : ∀ g y : G, algebraMap K (AlgebraicClosure K) (χ (g * y * g⁻¹)) =
      algebraMap K (AlgebraicClosure K) (χ y) := by
    intro g y; rw [← hch', ← hch', trace_rep_conj_eq]
  have hn0 : (n₀ : AlgebraicClosure K) ≠ 0 := by
    obtain ⟨hnt, -⟩ := _root_.GlobalTheory.asAlgebraHom_surjective_of_finrank_intertwiningMap_eq_one _ G _ ρ h1
    rcases Nat.eq_zero_or_pos n₀ with h0 | h0
    · subst h0
      exact absurd hnt (not_nontrivial_iff_subsingleton.2 inferInstance)
    · exact Nat.cast_ne_zero.2 h0.ne'
  let c : G → K := fun g => χ 1 / (Fintype.card G * Fintype.card P) *
    ∑ h : P, (((ψ h)⁻¹ : Kˣ) : K) * χ (h * g⁻¹)
  let f : MonoidAlgebra K G := MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm c)
  have hf : ∀ x, f.coeff x = c x := fun x => by simp [f]
  have hP : (Fintype.card P : AlgebraicClosure K) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hG : (Fintype.card G : AlgebraicClosure K) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  set ι := algebraMap K (AlgebraicClosure K) with hι
  have hsum' : ∑ h : P, ι (χ h) * ι (((ψ h)⁻¹ : Kˣ) : K) = Fintype.card P := by
    have := congrArg ι hsum
    simpa only [map_sum, map_mul, map_natCast] using this
  have hψ : ∀ a b : P, ι (((ψ (a * b))⁻¹ : Kˣ) : K) =
      ι (((ψ a)⁻¹ : Kˣ) : K) * ι (((ψ b)⁻¹ : Kˣ) : K) := by
    intro a b; rw [map_mul, mul_inv, Units.val_mul, map_mul]
  have hcyc : ∀ a b : G, ι (χ (a * b)) = ι (χ (b * a)) := by
    intro a b; rw [← hcl a (b * a)]; congr 2; group
  have hidem : f * f = f := by
    refine MonoidAlgebra.ext (Finsupp.ext fun g => ?_)
    rw [MonoidAlgebra.mul_apply_left, Finsupp.sum_fintype _ _ (by simp)]
    simp only [hf]
    apply ι.injective
    have hinner : ∀ h k : G, ∑ y : G, ι (χ (h * y⁻¹)) * ι (χ (k * (y⁻¹ * g)⁻¹)) =
        Fintype.card G * ι (χ (h * k * g⁻¹)) / n₀ := by
      intro h k
      rw [eq_div_iff hn0, ← hO (h * k * g⁻¹), mul_comm]
      congr 1
      refine Fintype.sum_equiv (Equiv.mulRight h⁻¹) _ _ fun y => ?_
      simp only [Equiv.coe_mulRight]
      rw [show k * (y⁻¹ * g)⁻¹ = k * g⁻¹ * y by group, hcyc (k * g⁻¹) y,
        show (y * h⁻¹)⁻¹ = h * y⁻¹ by group, show y * h⁻¹ * (h * k * g⁻¹) = y * (k * g⁻¹) by group]
    simp only [c, map_sum, map_mul, map_div₀, map_natCast, hn]
    set A : AlgebraicClosure K := (n₀ : AlgebraicClosure K) / (Fintype.card G * Fintype.card P) with hA
    calc ∑ y : G, (A * ∑ h : P, ι (((ψ h)⁻¹ : Kˣ) : K) * ι (χ (h * y⁻¹))) *
          (A * ∑ k : P, ι (((ψ k)⁻¹ : Kˣ) : K) * ι (χ (k * (y⁻¹ * g)⁻¹)))
        = ∑ y : G, ∑ h : P, ∑ k : P, A * A * (ι (((ψ h)⁻¹ : Kˣ) : K) * ι (((ψ k)⁻¹ : Kˣ) : K)) *
            (ι (χ (h * y⁻¹)) * ι (χ (k * (y⁻¹ * g)⁻¹))) := by
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun h _ => ?_
          rw [Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
      _ = ∑ h : P, ∑ k : P, A * A * (ι (((ψ h)⁻¹ : Kˣ) : K) * ι (((ψ k)⁻¹ : Kˣ) : K)) *
            (Fintype.card G * ι (χ (h * k * g⁻¹)) / n₀) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun h _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [← Finset.mul_sum, hinner]
      _ = ∑ h : P, ∑ m : P, A * A * ι (((ψ m)⁻¹ : Kˣ) : K) *
            (Fintype.card G * ι (χ (m * g⁻¹)) / n₀) := by
          refine Finset.sum_congr rfl fun h _ => ?_
          refine Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun k => ?_
          simp only [Equiv.coe_mulLeft, hψ, Subgroup.coe_mul, mul_assoc]
      _ = A * ∑ m : P, ι (((ψ m)⁻¹ : Kˣ) : K) * ι (χ (m * g⁻¹)) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [hA]
          field_simp
  have hI2 : ∀ t : G, ∑ x : G, c (x⁻¹ * t⁻¹ * x) = χ t := by
    intro t
    apply ι.injective
    have hx : ∀ h : G, ∑ x : G, ι (χ (h * (x⁻¹ * t⁻¹ * x)⁻¹)) =
        Fintype.card G * ι (χ t) * ι (χ h) / n₀ := by
      intro h
      rw [eq_div_iff hn0, ← hAv h t, mul_comm]
      congr 1
      exact Fintype.sum_equiv (Equiv.inv G) _ _ fun x => by simp [mul_assoc]
    simp only [c, map_sum, map_mul, map_div₀, map_natCast, hn]
    rw [← Finset.mul_sum, Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hx]
    calc (n₀ : AlgebraicClosure K) / (Fintype.card G * Fintype.card P) *
          ∑ h : P, ι (((ψ h)⁻¹ : Kˣ) : K) * (Fintype.card G * ι (χ t) * ι (χ h) / n₀)
        = (n₀ : AlgebraicClosure K) / (Fintype.card G * Fintype.card P) *
          (Fintype.card G * ι (χ t) / n₀ * ∑ h : P, ι (χ h) * ι (((ψ h)⁻¹ : Kˣ) : K)) := by
          simp only [Finset.mul_sum]
          exact Finset.sum_congr rfl fun h _ => by ring
      _ = ι (χ t) := by
          rw [hsum']
          field_simp
  let e : Module.End K (MonoidAlgebra K G) := LinearMap.mulRight K f
  have he : e * e = e := by
    refine LinearMap.ext fun x => ?_
    simp [e, mul_assoc, hidem]
  have hcomm : ∀ t, _root_.GlobalTheory.MultOneRealised.leftReg K G t * e = e * _root_.GlobalTheory.MultOneRealised.leftReg K G t := by
    intro t
    refine LinearMap.ext fun x => ?_
    simp [e, _root_.GlobalTheory.MultOneRealised.leftReg, mul_assoc]
  obtain ⟨n, τ, hτ⟩ := _root_.GlobalTheory.BI.isChar_trace_mul_idempotent K G _ (_root_.GlobalTheory.MultOneRealised.leftReg K G) e he hcomm
  have htr : ∀ g, LinearMap.trace K (Fin n → K) (τ g) = χ g := by
    intro g
    have := hτ g
    dsimp only [e] at this
    rw [trace_leftReg_mul_mulRight_eq_sum_coeff] at this
    simp only [hf, hI2, Algebra.algebraMap_self, RingHom.id_apply] at this
    exact this.symm
  have hτ1 : Module.finrank K (τ.IntertwiningMap τ) = 1 := by
    have hq := _root_.GlobalTheory.BI.pair_character_eq_finrank K (AlgebraicClosure K)
      G _ _ τ τ
    have hfun' : (fun g => algebraMap K (AlgebraicClosure K) (τ.character g)) =
        fun g => algebraMap K (AlgebraicClosure K) (χ g) := by
      funext g; rw [show τ.character g = χ g from htr g]
    rw [hfun', hp1] at hq
    exact_mod_cast hq.symm
  obtain ⟨hnt, hsurj⟩ := _root_.GlobalTheory.asAlgebraHom_surjective_of_finrank_intertwiningMap_eq_one K G _ τ hτ1
  refine ⟨n, τ, ?_, hsurj, htr⟩
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0
    exact absurd hnt (not_nontrivial_iff_subsingleton.2 inferInstance)
  · exact h0

end GlobalTheory.MultOneRealised
