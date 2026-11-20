import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSubLtOneOfFix
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisOfSubmodule
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Hilbert90MatrixCoboundaryCharPFiniteLevelStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWittVectorTraceOneFiniteLevelStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvariantMatrixLiftOfAdicCompleteStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrysOfSplitStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodDataComparisonStatement

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct GlobalTheory.UnramifiedCrys GlobalTheory.Cyc
open scoped Topology

namespace GlobalTheory.UnramifiedRep

section Witt

variable {p : ℕ} [hp : Fact p.Prime] {G : Type} [Group G] {R : Type} [CommRing R] (ρ : G →* (R ≃+* R))

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun a ha g y hy => by have h : ρ g⁻¹ y ^ p ^ m = ρ g⁻¹ y := by rw [← map_pow, hy] rw [map_mul, map_mul, RingAut.mul_apply, RingAut.mul_apply, ha _ h, ← RingAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, RingAut.one_apply]⟩`.
-/
theorem normal_fixer (p m : ℕ) : (fixer ρ p m).Normal := ⟨fun a ha g y hy => by
  have h : ρ g⁻¹ y ^ p ^ m = ρ g⁻¹ y := by rw [← map_pow, hy]
  rw [map_mul, map_mul, RingAut.mul_apply, RingAut.mul_apply, ha _ h, ← RingAut.mul_apply, ← map_mul,
    mul_inv_cancel, map_one, RingAut.one_apply]⟩

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [IsDomain R] [CharP R p]

omit [CharP R p] in

/- English proof (translation)
Take `⟨⟨m, hm⟩, hmU⟩` from `hU.isClosed_compl.isCompact.elim_directed_family_closed (fun m : {m : ℕ // 0 < m} => (fixer ρ p m.1 : Set G)) (fun m => Subgroup.isClosed_of_isOpen _ (isOpen_fixer ρ hopen m.2)) (by`. Rewrite using `[← Set.disjoint_iff_inter_eq_empty, Set.disjoint_left]`. Introduce `g hg hg'`. Conclude with `hg (hJU g fun m hm => Set.mem_iInter.1 hg' ⟨m, hm⟩))`. Use the proof step `(by`.

Introduce `a b`. Use `⟨⟨a.1 * b.1, Nat.mul_pos a.2 b.2⟩, fun g hg y hy => hg y (pow_pow_mul hy _), fun g hg y hy => hg y ?_⟩` and prove the remaining obligations. Use `pow_pow_mul hy a.1` as an intermediate fact. Rewrite using `[mul_comm] at this)` and apply the resulting hypothesis. Use `⟨m, hm, fun g hg => ?_⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hc`. Conclude with `Set.disjoint_left.1 (Set.disjoint_iff_inter_eq_empty.2 hmU) hc hg`.
-/
theorem exists_fixer_subset
    (hopen : ∀ (y : R) (m : ℕ), 0 < m → y ^ p ^ m = y → ∀ᶠ g in 𝓝 (1 : G), ρ g y = y)
    (U : Set G) (hU : IsOpen U) (hJU : ∀ g, (∀ m, 0 < m → g ∈ fixer ρ p m) → g ∈ U) :
    ∃ m, 0 < m ∧ ∀ g ∈ fixer ρ p m, g ∈ U := by
  obtain ⟨⟨m, hm⟩, hmU⟩ := hU.isClosed_compl.isCompact.elim_directed_family_closed
    (fun m : {m : ℕ // 0 < m} => (fixer ρ p m.1 : Set G))
    (fun m => Subgroup.isClosed_of_isOpen _ (isOpen_fixer ρ hopen m.2))
    (by
      rw [← Set.disjoint_iff_inter_eq_empty, Set.disjoint_left]
      intro g hg hg'
      exact hg (hJU g fun m hm => Set.mem_iInter.1 hg' ⟨m, hm⟩))
    (by
      intro a b
      refine ⟨⟨a.1 * b.1, Nat.mul_pos a.2 b.2⟩, fun g hg y hy => hg y (pow_pow_mul hy _),
        fun g hg y hy => hg y ?_⟩
      have := pow_pow_mul hy a.1
      rwa [mul_comm] at this)
  refine ⟨m, hm, fun g hg => ?_⟩
  by_contra hc
  exact Set.disjoint_left.1 (Set.disjoint_iff_inter_eq_empty.2 hmU) hc hg

omit [CharP R p] in

/- English proof (translation)
Establish `hpos : (0 : ℝ) < (p : ℝ) ^ (-(k : ℤ))`. Use `hp.out.pos` as an intermediate fact. Check the signs of the components of the expression. Take `⟨m, hm, h⟩` from `exists_fixer_subset ρ hopen (⋂ i, ⋂ j, {g | ‖(M g - 1) i j‖ < (p : ℝ) ^ (-(k : ℤ))}) (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => isOpen_lt ((hM.sub continuous_const).matrix_elem i j).norm continuous_const) (fun g hg => Set.mem_iInter.2 fun i => Set.mem_iInt …`. Express the relevant statement in the definitionally equal form `‖(M g - 1) i j‖ < _`.

Rewrite using `[hJ g hg, sub_self, Matrix.zero_apply, norm_zero]`. Conclude with `hpos)`. Use `⟨m, hm, fun g hg i j => ?_⟩` and prove the remaining obligations. Establish `h1` using `Set.mem_iInter.1 (Set.mem_iInter.1 (h g hg) i) j`. Conclude with `Ideal.mem_span_singleton.1 ((PadicInt.norm_le_pow_iff_mem_span_pow _ _).1 (le_of_lt h1))`.
-/
theorem exists_fixer_dvd
    (hopen : ∀ (y : R) (m : ℕ), 0 < m → y ^ p ^ m = y → ∀ᶠ g in 𝓝 (1 : G), ρ g y = y)
    {r : ℕ} (M : G → Matrix (Fin r) (Fin r) ℤ_[p]) (hM : Continuous M)
    (hJ : ∀ g, (∀ m, 0 < m → g ∈ fixer ρ p m) → M g = 1) (k : ℕ) :
    ∃ m, 0 < m ∧ ∀ g ∈ fixer ρ p m, ∀ i j, (p : ℤ_[p]) ^ k ∣ (M g - 1) i j := by
  have hpos : (0 : ℝ) < (p : ℝ) ^ (-(k : ℤ)) := by
    have := hp.out.pos
    positivity
  obtain ⟨m, hm, h⟩ := exists_fixer_subset ρ hopen
    (⋂ i, ⋂ j, {g | ‖(M g - 1) i j‖ < (p : ℝ) ^ (-(k : ℤ))})
    (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      isOpen_lt ((hM.sub continuous_const).matrix_elem i j).norm continuous_const)
    (fun g hg => Set.mem_iInter.2 fun i => Set.mem_iInter.2 fun j => by
      change ‖(M g - 1) i j‖ < _
      rw [hJ g hg, sub_self, Matrix.zero_apply, norm_zero]
      exact hpos)
  refine ⟨m, hm, fun g hg i j => ?_⟩
  have h1 := Set.mem_iInter.1 (Set.mem_iInter.1 (h g hg) i) j
  exact Ideal.mem_span_singleton.1 ((PadicInt.norm_le_pow_iff_mem_span_pow _ _).1 (le_of_lt h1))

variable [PerfectRing R p]

omit [IsDomain R] in
/- English proof (translation)
Rewrite using `[← Ideal.mem_span_singleton, WittVector.mem_span_p_iff_coeff_zero_eq_zero]`. Both sides reduce to the same expression.
-/
theorem dvd_iff_constantCoeff (x : WittVector p R) :
    (p : WittVector p R) ∣ x ↔ WittVector.constantCoeff x = 0 := by
  rw [← Ideal.mem_span_singleton, WittVector.mem_span_p_iff_coeff_zero_eq_zero]
  rfl

omit [IsDomain R] in

/- English proof (translation)
Take `⟨y, hy⟩` from `hx.exists_right_inv`. Use `WittVector.isAdicCompleteIdealSpanP (p := p) (k := R)` as an intermediate fact. Establish `h1 : x * WittVector.teichmuller p y - 1 ∈ Ideal.span {(p : WittVector p R)}`. Rewrite using `[Ideal.mem_span_singleton, dvd_iff_constantCoeff, map_sub, map_mul, map_one, sub_eq_zero, ← hy]`. Both sides reduce to the same expression.

Establish `h2` using `Ideal.mem_jacobson_bot.1 (IsAdicComplete.le_jacobson_bot _ h1) 1`. Rewrite `h2` using `[mul_one, sub_add_cancel]`. Conclude with `isUnit_of_mul_isUnit_left h2`.
-/
theorem isUnit_of_constantCoeff (x : WittVector p R) (hx : IsUnit (WittVector.constantCoeff x)) :
    IsUnit x := by
  obtain ⟨y, hy⟩ := hx.exists_right_inv
  have := WittVector.isAdicCompleteIdealSpanP (p := p) (k := R)
  have h1 : x * WittVector.teichmuller p y - 1 ∈ Ideal.span {(p : WittVector p R)} := by
    rw [Ideal.mem_span_singleton, dvd_iff_constantCoeff, map_sub, map_mul, map_one, sub_eq_zero, ← hy]
    rfl
  have h2 := Ideal.mem_jacobson_bot.1 (IsAdicComplete.le_jacobson_bot _ h1) 1
  rw [mul_one, sub_add_cancel] at h2
  exact isUnit_of_mul_isUnit_left h2

/- English proof (translation)
Establish `hfin : ∀ m, 0 < m → Finite (G ⧸ fixer ρ p m)` using `fun m hm => Subgroup.quotient_finite_of_isOpen _ (isOpen_fixer ρ hopen hm)`. Set `c : WittVector p R →+* R` to `WittVector.constantCoeff`. Establish `hc : ∀ g x, c (WittVector.map (ρ g).toRingHom x) = ρ g (c x)` using `fun g x => rfl`. Establish `hz : ∀ z : ℤ_[p], c (zlW p R z) ^ p = c (zlW p R z)` using `fun z => by`. Use `congrArg c (map_zlW p (frobenius R p) z)` as an intermediate fact.

Conclude with `this`. Take `⟨m, hm, h1⟩` from `exists_fixer_dvd ρ hopen M hM hJ 1`. Take `⟨W₁, hW₁, hW₁m, hW₁g⟩` from `GlobalTheory.T.exists_unit_matrix_coboundary_of_fixed_frobenius_pow p G R ρ m hm (hfin m hm) r ((c.comp (zlW p R)).mapMatrix.toMonoidHom.comp M) (fun g h i j => by`. Express the relevant statement in the definitionally equal form `ρ g (c (zlW p R (M h i j))) = c (zlW p R (M h i j))`. Rewrite using `[← hc, map_zlW])`.

Use the proof step `(fun h i j => by`. Use `pow_pow_mul (p := p) (a := 1) (y := c (zlW p R (M h i j))) (by rw [pow_one, hz]) m` as an intermediate fact. Rewrite using `[one_mul] at this)` and apply the resulting hypothesis. Use the proof step `(fun g hg => by`. Express the relevant statement in the definitionally equal form `(c.comp (zlW p R)).mapMatrix (M g) = 1`.

Rewrite using `[← sub_eq_zero, ← map_one (c.comp (zlW p R)).mapMatrix, ← map_sub]`. Use extensionality with `i j`. Take `⟨z, hz⟩` from `h1 g hg i j`. Express the relevant statement in the definitionally equal form `(c.comp (zlW p R)) ((M g - 1) i j) = 0`. Rewrite using `[hz, map_mul, pow_one, map_natCast, CharP.cast_eq_zero, zero_mul])`.

Establish `hct : ∀ y : R, c (WittVector.teichmuller p y) = y` using `fun y => rfl`. Take `⟨W, hW, hWg⟩` from `GlobalTheory.T.exists_invariant_matrix_lift_of_adic_complete G (WittVector p R) p WittVector.isAdicCompleteIdealSpanP (fun g => WittVector.map (ρ g).toRingHom) (wittMap_mul ρ) (fun g => map_natCast _ _) r ((zlW p R).mapMatrix.toMonoidHom.comp M) (fun g h i j => map_zlW p _ _) {N …`. Introduce and unpack `_ ⟨m, hm, rfl⟩`. Conclude with `⟨normal_fixer ρ p m, hfin m hm, GlobalTheory.T.exists_wittVector_trace_one_finiteLevel p G R ρ m hm (hfin m hm)⟩)`. Use the proof step `(by`.

Introduce and unpack `_ ⟨a, ha, rfl⟩ k`. Take `⟨b, hb, h⟩` from `exists_fixer_dvd ρ hopen M hM hJ k`. Use `⟨_, ⟨a * b, Nat.mul_pos ha hb, rfl⟩, fun g hg y hy => hg y (pow_pow_mul hy _), fun g hg i j => ?_⟩` and prove the remaining obligations. Establish `h2` using `map_dvd (zlW p R) (h g (fun y hy => hg y (by`. Use `pow_pow_mul hy a` as an intermediate fact.

Rewrite using `[mul_comm] at this)) i j)` and apply the resulting hypothesis. Rewrite `h2` using `[map_pow, map_natCast]`. Establish `h3 : (zlW p R).mapMatrix (M g - 1) = (zlW p R).mapMatrix (M g) - 1`. Rewrite using `[map_sub, map_one]`. Conclude with `(congrFun (congrFun h3 i) j) ▸ h2)`.

Use the proof step `(W₁.map (WittVector.teichmuller p))`. Use the proof step `⟨_, ⟨m, hm, rfl⟩, fun g hg => by`. Use extensionality with `i j : 1`. Simplify using `only [Matrix.map_apply, WittVector.map_teichmuller]`. Conclude with `congrArg _ (hg _ (hW₁m i j))⟩`.

Use the proof step `(fun g i j => by`. Rewrite using `[dvd_iff_constantCoeff]`. Use `congrFun (congrFun (hW₁g g) i) j` as an intermediate fact. Rewrite using `[Matrix.sub_apply, map_sub, sub_eq_zero, Matrix.mul_apply, map_sum]`. Rewrite `this` using `[Matrix.mul_apply]`.

Simplify using `only [map_mul]`. Conclude with `this)`. Use `⟨W, isUnit_of_constantCoeff _ ?_, hWg⟩` and prove the remaining obligations. Establish `h4 : c.mapMatrix W = W₁`. Use extensionality with `i j`.

Use `(dvd_iff_constantCoeff _).1 (hW i j)` as an intermediate fact. Rewrite `this` using `[Matrix.sub_apply, map_sub, sub_eq_zero]`. Conclude with `this`. Express the relevant statement in the definitionally equal form `IsUnit (c W.det)`. Rewrite using `[RingHom.map_det, h4]`.

Conclude with `hW₁`.
-/
theorem exists_witt_matrix
    (hopen : ∀ (y : R) (m : ℕ), 0 < m → y ^ p ^ m = y → ∀ᶠ g in 𝓝 (1 : G), ρ g y = y)
    {r : ℕ} (M : G →* Matrix (Fin r) (Fin r) ℤ_[p]) (hM : Continuous M)
    (hJ : ∀ g, (∀ m, 0 < m → g ∈ fixer ρ p m) → M g = 1) :
    ∃ W : Matrix (Fin r) (Fin r) (WittVector p R), IsUnit W.det ∧
      ∀ g, (M g).map (zlW p R) * W.map (WittVector.map (ρ g).toRingHom) = W := by
  have hfin : ∀ m, 0 < m → Finite (G ⧸ fixer ρ p m) := fun m hm =>
    Subgroup.quotient_finite_of_isOpen _ (isOpen_fixer ρ hopen hm)
  let c : WittVector p R →+* R := WittVector.constantCoeff
  have hc : ∀ g x, c (WittVector.map (ρ g).toRingHom x) = ρ g (c x) := fun g x => rfl
  have hz : ∀ z : ℤ_[p], c (zlW p R z) ^ p = c (zlW p R z) := fun z => by
    have := congrArg c (map_zlW p (frobenius R p) z)
    exact this
  obtain ⟨m, hm, h1⟩ := exists_fixer_dvd ρ hopen M hM hJ 1
  obtain ⟨W₁, hW₁, hW₁m, hW₁g⟩ := GlobalTheory.T.exists_unit_matrix_coboundary_of_fixed_frobenius_pow p G R ρ m hm (hfin m hm) r
    ((c.comp (zlW p R)).mapMatrix.toMonoidHom.comp M)
    (fun g h i j => by
      change ρ g (c (zlW p R (M h i j))) = c (zlW p R (M h i j))
      rw [← hc, map_zlW])
    (fun h i j => by
      have := pow_pow_mul (p := p) (a := 1) (y := c (zlW p R (M h i j))) (by rw [pow_one, hz]) m
      rwa [one_mul] at this)
    (fun g hg => by
      change (c.comp (zlW p R)).mapMatrix (M g) = 1
      rw [← sub_eq_zero, ← map_one (c.comp (zlW p R)).mapMatrix, ← map_sub]
      ext i j
      obtain ⟨z, hz⟩ := h1 g hg i j
      change (c.comp (zlW p R)) ((M g - 1) i j) = 0
      rw [hz, map_mul, pow_one, map_natCast, CharP.cast_eq_zero, zero_mul])
  have hct : ∀ y : R, c (WittVector.teichmuller p y) = y := fun y => rfl
  obtain ⟨W, hW, hWg⟩ := GlobalTheory.T.exists_invariant_matrix_lift_of_adic_complete G (WittVector p R) p WittVector.isAdicCompleteIdealSpanP
    (fun g => WittVector.map (ρ g).toRingHom) (wittMap_mul ρ) (fun g => map_natCast _ _) r
    ((zlW p R).mapMatrix.toMonoidHom.comp M) (fun g h i j => map_zlW p _ _)
    {N | ∃ m, 0 < m ∧ N = fixer ρ p m}
    (by
      rintro _ ⟨m, hm, rfl⟩
      exact ⟨normal_fixer ρ p m, hfin m hm, GlobalTheory.T.exists_wittVector_trace_one_finiteLevel p G R ρ m hm (hfin m hm)⟩)
    (by
      rintro _ ⟨a, ha, rfl⟩ k
      obtain ⟨b, hb, h⟩ := exists_fixer_dvd ρ hopen M hM hJ k
      refine ⟨_, ⟨a * b, Nat.mul_pos ha hb, rfl⟩, fun g hg y hy => hg y (pow_pow_mul hy _),
        fun g hg i j => ?_⟩
      have h2 := map_dvd (zlW p R) (h g (fun y hy => hg y (by
        have := pow_pow_mul hy a
        rwa [mul_comm] at this)) i j)
      rw [map_pow, map_natCast] at h2
      have h3 : (zlW p R).mapMatrix (M g - 1) = (zlW p R).mapMatrix (M g) - 1 := by
        rw [map_sub, map_one]
      exact (congrFun (congrFun h3 i) j) ▸ h2)
    (W₁.map (WittVector.teichmuller p))
    ⟨_, ⟨m, hm, rfl⟩, fun g hg => by
      ext i j : 1
      simp only [Matrix.map_apply, WittVector.map_teichmuller]
      exact congrArg _ (hg _ (hW₁m i j))⟩
    (fun g i j => by
      rw [dvd_iff_constantCoeff]
      have := congrFun (congrFun (hW₁g g) i) j
      rw [Matrix.sub_apply, map_sub, sub_eq_zero, Matrix.mul_apply, map_sum]
      rw [Matrix.mul_apply] at this
      simp only [map_mul]
      exact this)
  refine ⟨W, isUnit_of_constantCoeff _ ?_, hWg⟩
  have h4 : c.mapMatrix W = W₁ := by
    ext i j
    have := (dvd_iff_constantCoeff _).1 (hW i j)
    rw [Matrix.sub_apply, map_sub, sub_eq_zero] at this
    exact this
  change IsUnit (c W.det)
  rw [RingHom.map_det, h4]
  exact hW₁

end Witt

/- English proof (translation)
Use `⟨{ toFun := fun g => Matrix.of fun i j => ⟨e.repr (ρ g (e j)) i, hint g i j⟩ map_one' := ?_ map_mul' := fun g h => ?_ }, fun _ _ _ => rfl⟩` and prove the remaining obligations. Use extensionality with `i j`. Apply `PadicInt.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `e.repr (ρ 1 (e j)) i = _`. Rewrite using `[map_one, Module.End.one_apply, e.repr_self, Finsupp.single_apply, Matrix.one_apply]`.

Distinguish the cases in `h : i = j`. Rewrite using `[if_pos h, if_pos h.symm, PadicInt.coe_one]`. Rewrite using `[if_neg h, if_neg (Ne.symm h), PadicInt.coe_zero]`. Use extensionality with `i j`. Apply `PadicInt.ext` to reduce the goal to its premises.

Rewrite using `[Matrix.mul_apply, PadicInt.coe_sum]`. Simplify using `only [PadicInt.coe_mul]`. Express the relevant statement in the definitionally equal form `e.repr (ρ (g * h) (e j)) i = ∑ k, e.repr (ρ g (e k)) i * e.repr (ρ h (e j)) k`. Rewrite using `[map_mul, Module.End.mul_apply]`. Use `conv_lhs => rw [← e.sum_repr (ρ h (e j))]`.

Establish `: ∀ (a : ℚ_[l]) v, ρ g (a • v) = a • ρ g v` using `fun a v => (ρ g).map_smul_of_tower _ _`. Simplify using `only [map_sum, this, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, mul_comm]`.
-/
theorem exists_matrixHom {l : ℕ} [Fact l.Prime] {G : Type} [Group G] {L V : Type} [Field L] [Algebra ℚ_[l] L]
    [AddCommGroup V] [Module L V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] L V] (ρ : Representation L G V)
    {n : ℕ} (e : Module.Basis (Fin n) ℚ_[l] V) (hint : ∀ g i j, ‖e.repr (ρ g (e j)) i‖ ≤ 1) :
    ∃ M : G →* Matrix (Fin n) (Fin n) ℤ_[l], ∀ g i j, ((M g i j : ℤ_[l]) : ℚ_[l]) = e.repr (ρ g (e j)) i := by
  refine ⟨{ toFun := fun g => Matrix.of fun i j => ⟨e.repr (ρ g (e j)) i, hint g i j⟩
            map_one' := ?_
            map_mul' := fun g h => ?_ }, fun _ _ _ => rfl⟩
  · ext i j
    apply PadicInt.ext
    change e.repr (ρ 1 (e j)) i = _
    rw [map_one, Module.End.one_apply, e.repr_self, Finsupp.single_apply, Matrix.one_apply]
    by_cases h : i = j
    · rw [if_pos h, if_pos h.symm, PadicInt.coe_one]
    · rw [if_neg h, if_neg (Ne.symm h), PadicInt.coe_zero]
  · ext i j
    apply PadicInt.ext
    rw [Matrix.mul_apply, PadicInt.coe_sum]
    simp only [PadicInt.coe_mul]
    change e.repr (ρ (g * h) (e j)) i = ∑ k, e.repr (ρ g (e k)) i * e.repr (ρ h (e j)) k
    rw [map_mul, Module.End.mul_apply]
    conv_lhs => rw [← e.sum_repr (ρ h (e j))]
    have : ∀ (a : ℚ_[l]) v, ρ g (a • v) = a • ρ g v := fun a v => (ρ g).map_smul_of_tower _ _
    simp only [map_sum, this, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
      smul_eq_mul, mul_comm]

/- English proof (translation)
Use extensionality with `i j`. Use `congrArg f (congrFun (congrFun h i) j)` as an intermediate fact. Rewrite `this` using `[Matrix.mul_apply, map_sum]`. Simplify using `only [map_mul, hM, Matrix.map_apply, hs] at this`. Conclude with `this`.
-/
theorem map_mul_map_eq {A A' : Type} [CommRing A] [CommRing A'] (f : A →+* A') {n : ℕ}
    {M W : Matrix (Fin n) (Fin n) A} {M' : Matrix (Fin n) (Fin n) A'} {s : A → A} {s' : A' → A'}
    (h : M * W.map s = W) (hM : ∀ i j, f (M i j) = M' i j) (hs : ∀ a, f (s a) = s' (f a)) :
    M' * (W.map f).map s' = W.map f := by
  ext i j
  have := congrArg f (congrFun (congrFun h i) j)
  rw [Matrix.mul_apply, map_sum] at this
  simp only [map_mul, hM, Matrix.map_apply, hs] at this
  exact this

/- English proof (translation)
Introduce `l _ P AI Ti K LL T hI`. Use `compactSpace_GK K` as an intermediate fact. Use `LL.2` as an intermediate fact. Take `⟨n, e, he, hcont, -⟩` from `GlobalTheory.Cyc.LatBasis.exists_basis l (GK K) LL T`. Establish `hint : ∀ g i j, ‖e.repr (T.ρ g (e j)) i‖ ≤ 1` using `fun g i j => (he _).1 (T.L.stable g _ ((he _).2 fun k => by`.

Rewrite using `[e.repr_self, Finsupp.single_apply]`. Apply the tactic sequence `split_ifs <;> simp)) i`. Take `⟨M, hM⟩` from `exists_matrixHom T.ρ e hint`. Take `⟨W, hW, hWg⟩` from `exists_witt_matrix (p := l) (AI.actT.comp (GK K).subtype) (fun y m hm hy => (continuous_subtype_val.tendsto (1 : ↥(GK K))).eventually (eventually_actT_eq AI y m hm hy)) M (continuous_pi fun i => continuous_pi fun j => continuous_induced_rng.2 (by`. Establish `h` using `(continuous_apply i).comp (hcont.comp (T.cont (e j)))`.

Conclude with `h.congr fun g => (hM g i j).symm))`. Use the proof step `(fun g hg => by`. Establish `h` using `hI g (Subgroup.subset_closure fun x hx => norm_sub_lt_one_of_fix AI g (fun m hm y hy => hg m hm y hy) x hx)`. Rewrite using `[← map_one M]`. Use extensionality with `i j`.

Apply `PadicInt.ext` to reduce the goal to its premises. Rewrite using `[hM, hM, h, map_one, Module.End.one_apply])`. Establish `hB : ∀ g, (Matrix.of fun i j => algebraMap ℚ_[l] P.R.B (e.repr (T.ρ g (e j)) i)) * (AI.ιA.mapMatrix W).map ((P.PD K).actB g) = AI.ιA.mapMatrix W` using `fun g => by conv_rhs => rw [← hWg g, map_mul]`. Use `congr 1`. Use extensionality with `i j`.

Rewrite using `[Matrix.of_apply, ← hM]`. Conclude with `(ιA_zlW AI Ti (M g i j)).symm`. Use extensionality with `i j`. Conclude with `(P.PD_actB K g _).trans (AI.ιA_act g _).symm`. Use `⟨GlobalTheory.T.isCrys_of_split_alt (P.PD K) T.ρ e (AI.ιA.mapMatrix W) ?_ hB, ?_⟩` and prove the remaining obligations.

Rewrite using `[← RingHom.map_det]`. Conclude with `hW.map _`. Set `f : Ainf l →+* P.R.BdR` to `((P.PD K).ι : P.R.B →+* P.R.BdR).comp AI.ιA`. Establish `hf : ∀ a, f a ∈ (P.PD K).Fil 0` using `fun a => by`. Express the relevant statement in the definitionally equal form `(P.PD K).ι (AI.ιA a) ∈ _`.

Rewrite using `[P.PD_ι]`. Conclude with `AI.ainf_image_mem_filtration_zero K a`. Use `GlobalTheory.T.period_data_comparison (P.PD K) T.ρ e (f.mapMatrix W) (f.mapMatrix W⁻¹) ?_ (fun i j => hf _) (fun i j => hf _) fun g => ?_` and prove the remaining obligations. Rewrite using `[← map_mul, Matrix.mul_nonsing_inv _ hW, map_one]`. Establish `hι : ∀ c : ℚ_[l], ((P.PD K).ι : P.R.B →+* P.R.BdR) (algebraMap ℚ_[l] P.R.B c) = algebraMap ℚ_[l] P.R.BdR c` using `fun c => (P.PD_ι K _).trans (P.ιB.commutes c)`.

Conclude with `map_mul_map_eq ((P.PD K).ι : P.R.B →+* P.R.BdR) (hB g) (fun i j => hι _) ((P.PD K).ι_comm g)`.
-/
theorem isCrys_and_jump_eq_zero : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), (∀ g ∈ IK K, ∀ x, T.ρ g x = x) → IsCrys (P.PD K) T.ρ ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), IsJumpV (P.PD K) T.ρ τ a → a = 0 := by
  intro l _ P AI Ti K LL T hI
  have := compactSpace_GK K
  have := LL.2
  obtain ⟨n, e, he, hcont, -⟩ := GlobalTheory.Cyc.LatBasis.exists_basis l (GK K) LL T
  have hint : ∀ g i j, ‖e.repr (T.ρ g (e j)) i‖ ≤ 1 := fun g i j =>
    (he _).1 (T.L.stable g _ ((he _).2 fun k => by
      rw [e.repr_self, Finsupp.single_apply]
      split_ifs <;> simp)) i
  obtain ⟨M, hM⟩ := exists_matrixHom T.ρ e hint
  obtain ⟨W, hW, hWg⟩ := exists_witt_matrix (p := l) (AI.actT.comp (GK K).subtype)
    (fun y m hm hy => (continuous_subtype_val.tendsto (1 : ↥(GK K))).eventually
      (eventually_actT_eq AI y m hm hy)) M
    (continuous_pi fun i => continuous_pi fun j => continuous_induced_rng.2 (by
      have h := (continuous_apply i).comp (hcont.comp (T.cont (e j)))
      exact h.congr fun g => (hM g i j).symm))
    (fun g hg => by
      have h := hI g (Subgroup.subset_closure fun x hx =>
        norm_sub_lt_one_of_fix AI g (fun m hm y hy => hg m hm y hy) x hx)
      rw [← map_one M]
      ext i j
      apply PadicInt.ext
      rw [hM, hM, h, map_one, Module.End.one_apply])
  have hB : ∀ g, (Matrix.of fun i j => algebraMap ℚ_[l] P.R.B (e.repr (T.ρ g (e j)) i)) *
      (AI.ιA.mapMatrix W).map ((P.PD K).actB g) = AI.ιA.mapMatrix W := fun g => by
    conv_rhs => rw [← hWg g, map_mul]
    congr 1
    · ext i j
      rw [Matrix.of_apply, ← hM]
      exact (ιA_zlW AI Ti (M g i j)).symm
    · ext i j
      exact (P.PD_actB K g _).trans (AI.ιA_act g _).symm
  refine ⟨GlobalTheory.T.isCrys_of_split_alt (P.PD K) T.ρ e (AI.ιA.mapMatrix W) ?_ hB, ?_⟩
  · rw [← RingHom.map_det]
    exact hW.map _
  · let f : Ainf l →+* P.R.BdR := ((P.PD K).ι : P.R.B →+* P.R.BdR).comp AI.ιA
    have hf : ∀ a, f a ∈ (P.PD K).Fil 0 := fun a => by
      change (P.PD K).ι (AI.ιA a) ∈ _
      rw [P.PD_ι]
      exact AI.ainf_image_mem_filtration_zero K a
    refine GlobalTheory.T.period_data_comparison (P.PD K) T.ρ e (f.mapMatrix W) (f.mapMatrix W⁻¹) ?_ (fun i j => hf _) (fun i j => hf _)
      fun g => ?_
    · rw [← map_mul, Matrix.mul_nonsing_inv _ hW, map_one]
    · have hι : ∀ c : ℚ_[l], ((P.PD K).ι : P.R.B →+* P.R.BdR) (algebraMap ℚ_[l] P.R.B c) =
          algebraMap ℚ_[l] P.R.BdR c := fun c => (P.PD_ι K _).trans (P.ιB.commutes c)
      exact map_mul_map_eq ((P.PD K).ι : P.R.B →+* P.R.BdR) (hB g) (fun i j => hι _)
        ((P.PD K).ι_comm g)

end GlobalTheory.UnramifiedRep
