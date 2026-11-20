import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.DualStdModelField
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualArithVar
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField DualArithmeticVariety

noncomputable section

namespace StandardModelDualRank

variable {K : Type} [Field K] {i : ℕ}

abbrev gen (K : Type) [Field K] (i : ℕ) (j : Fin i) : ProjField K i :=
  algebraMap (MvPolynomial (Fin i) K) (ProjField K i) (X j)

def embK (K : Type) [Field K] (i : ℕ) : K →+* dualStdModelField K i :=
  (dualStdModelEmb K i).comp (algebraMap K (ProjField K i))

def u (K : Type) [Field K] (i : ℕ) (j : Fin i) : dualStdModelField K i :=
  dualStdModelEmb K i (gen K i j) * dualStdModelS K i * dualStdModelT K i

def psiA (K : Type) [Field K] (i : ℕ) :
    MvPolynomial (Fin i) K →+* MvPolynomial Unit (MvPolynomial Unit (ProjField K i)) :=
  eval₂Hom (((C : MvPolynomial Unit (ProjField K i) →+* _).comp C).comp (algebraMap K (ProjField K i)))
    fun j => C (C (gen K i j)) * C (X ()) * X ()

def psi (K : Type) [Field K] (i : ℕ) : MvPolynomial (Fin i) K →+* dualStdModelField K i :=
  (algebraMap _ _).comp (psiA K i)

def psiZ (K : Type) [Field K] (i : ℕ) : MvPolynomial (Fin i) ℤ →+* dualStdModelField K i :=
  (psi K i).comp (MvPolynomial.map (Int.castRingHom K))

/- English proof (translation)
Set `ev : MvPolynomial Unit (MvPolynomial Unit (ProjField K i)) →+* ProjField K i` to `eval₂Hom (MvPolynomial.eval fun _ => (1 : ProjField K i)) fun _ => 1`. Establish `h : ev.comp (psiA K i) = algebraMap (MvPolynomial (Fin i) K) (ProjField K i)`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `k`. Simplify using `only [ev, psiA, RingHom.comp_apply, eval₂Hom_C, eval_C]`.

Rewrite using `[← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]`. Introduce `j`. Simplify using `[ev, psiA]`. Introduce `p q hpq`. Apply `IsFractionRing.injective (MvPolynomial (Fin i) K) (ProjField K i)` to reduce the goal to its premises.

Rewrite using `[← h, RingHom.comp_apply, RingHom.comp_apply, hpq]`.
-/
theorem psiA_injective : Function.Injective (psiA K i) := by
  let ev : MvPolynomial Unit (MvPolynomial Unit (ProjField K i)) →+* ProjField K i :=
    eval₂Hom (MvPolynomial.eval fun _ => (1 : ProjField K i)) fun _ => 1
  have h : ev.comp (psiA K i) = algebraMap (MvPolynomial (Fin i) K) (ProjField K i) := by
    apply MvPolynomial.ringHom_ext
    · intro k
      simp only [ev, psiA, RingHom.comp_apply, eval₂Hom_C, eval_C]
      rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
    · intro j
      simp [ev, psiA]
  intro p q hpq
  apply IsFractionRing.injective (MvPolynomial (Fin i) K) (ProjField K i)
  rw [← h, RingHom.comp_apply, RingHom.comp_apply, hpq]

/- English proof (translation)
Rewrite using `[psi, RingHom.coe_comp]`. Conclude with `(IsFractionRing.injective (MvPolynomial Unit (MvPolynomial Unit (ProjField K i))) (dualStdModelField K i)).comp psiA_injective`.
-/
theorem psi_injective : Function.Injective (psi K i) := by
  rw [psi, RingHom.coe_comp]
  exact (IsFractionRing.injective (MvPolynomial Unit (MvPolynomial Unit (ProjField K i)))
    (dualStdModelField K i)).comp psiA_injective

/- English proof (translation)
Simplify using `[psi, psiA, u, dualStdModelEmb, dualStdModelS, dualStdModelT]`.
-/
theorem psi_X (j : Fin i) : psi K i (X j) = u K i j := by
  simp [psi, psiA, u, dualStdModelEmb, dualStdModelS, dualStdModelT]

/- English proof (translation)
Simplify using `[psi, psiA, embK, dualStdModelEmb]`.
-/
theorem psi_C (k : K) : psi K i (C k) = embK K i k := by
  simp [psi, psiA, embK, dualStdModelEmb]

/- English proof (translation)
The claim follows from `(Subring.closure_le).mpr (by rintro _ ⟨j, rfl⟩; exact ⟨X j, by simp [psiZ, psi_X]⟩)`.
-/
theorem closure_le : Subring.closure (Set.range (u K i)) ≤ (psiZ K i).range :=
  (Subring.closure_le).mpr (by rintro _ ⟨j, rfl⟩; exact ⟨X j, by simp [psiZ, psi_X]⟩)

/- English proof (translation)
Take `⟨y, hy, z, hz, rfl⟩` from `Subfield.mem_closure_iff.mp hf`. Distinguish the cases in `h0 : z = 0`. Conclude with `⟨1, one_mem _, one_ne_zero, by simp [h0]⟩`. Use `⟨z, closure_le hz, h0, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_div_cancel₀ y h0]`.

Conclude with `closure_le hy`.
-/
theorem exists_den {f : dualStdModelField K i} (hf : f ∈ Subfield.closure (Set.range (u K i))) :
    ∃ d ∈ (psiZ K i).range, d ≠ 0 ∧ d * f ∈ (psiZ K i).range := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Subfield.mem_closure_iff.mp hf
  by_cases h0 : z = 0
  · exact ⟨1, one_mem _, one_ne_zero, by simp [h0]⟩
  · refine ⟨z, closure_le hz, h0, ?_⟩
    rw [mul_div_cancel₀ y h0]
    exact closure_le hy

/- English proof (translation)
Use `choose d hd hd0 hdf using fun k => exists_den (hf k)`. Use `⟨∏ k, d k, prod_mem fun k _ => hd k, Finset.prod_ne_zero_iff.mpr fun k _ => hd0 k, fun k => ?_⟩` and prove the remaining obligations. Rewrite using `[← Finset.mul_prod_erase Finset.univ d (Finset.mem_univ k), mul_comm (d k), mul_assoc]`. Conclude with `mul_mem (prod_mem fun l _ => hd l) (hdf k)`.
-/
theorem exists_den_fin {n : ℕ} (f : Fin n → dualStdModelField K i)
    (hf : ∀ k, f k ∈ Subfield.closure (Set.range (u K i))) :
    ∃ D ∈ (psiZ K i).range, D ≠ 0 ∧ ∀ k, D * f k ∈ (psiZ K i).range := by
  classical
  choose d hd hd0 hdf using fun k => exists_den (hf k)
  refine ⟨∏ k, d k, prod_mem fun k _ => hd k, Finset.prod_ne_zero_iff.mpr fun k _ => hd0 k, fun k => ?_⟩
  rw [← Finset.mul_prod_erase Finset.univ d (Finset.mem_univ k), mul_comm (d k), mul_assoc]
  exact mul_mem (prod_mem fun l _ => hd l) (hdf k)

variable [NumberField K]

/- English proof (translation)
Establish `h' : ∑ k, C (B k) * MvPolynomial.map (Int.castRingHom K) (q k) = 0`. Apply `psi_injective` to reduce the goal to its premises. Rewrite using `[map_sum, map_zero]`. Simplify `h` using `[psiZ, psi_C]`. Establish `hB : LinearIndependent ℤ B` using `B.linearIndependent.restrict_scalars' ℤ`.

Introduce `k`. Use extensionality with `m`. Establish `hm` using `congrArg (coeff m) h'`. Rewrite `hm` using `[coeff_sum, coeff_zero]`. Simplify using `only [coeff_C_mul, coeff_map, eq_intCast] at hm`.

Use `Fintype.linearIndependent_iff.mp hB (fun k => coeff m (q k)) (by simpa [zsmul_eq_mul, mul_comm] using hm) k` as an intermediate fact. Simplify using `using this`.
-/
theorem indep_int {n : ℕ} (B : Module.Basis (Fin n) ℚ K) (q : Fin n → MvPolynomial (Fin i) ℤ)
    (h : ∑ k, embK K i (B k) * psiZ K i (q k) = 0) : ∀ k, q k = 0 := by
  have h' : ∑ k, C (B k) * MvPolynomial.map (Int.castRingHom K) (q k) = 0 := by
    apply psi_injective
    rw [map_sum, map_zero]
    simpa [psiZ, psi_C] using h
  have hB : LinearIndependent ℤ B := B.linearIndependent.restrict_scalars' ℤ
  intro k
  ext m
  have hm := congrArg (coeff m) h'
  rw [coeff_sum, coeff_zero] at hm
  simp only [coeff_C_mul, coeff_map, eq_intCast] at hm
  have := Fintype.linearIndependent_iff.mp hB (fun k => coeff m (q k)) (by simpa [zsmul_eq_mul, mul_comm] using hm) k
  simpa using this

/- English proof (translation)
Take `⟨S, hS⟩` from `F.fg`. Take `⟨N, hN, hint⟩` from `exists_integral_multiples ℤ ℚ (S.image fun g => v ⬝ᵥ g)`. Use `⟨N, hN, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite `hx` using `[← hS]`. Proceed by induction on `hx using Submodule.span_induction with`.

Consider the case `mem g hg`. Establish `hg'` using `hint _ (Finset.mem_image_of_mem _ hg)`. Rewrite using `[smul_dotProduct, Int.cast_smul_eq_zsmul]`. Conclude with `RingHom.mem_range.mpr ((IsIntegralClosure.isIntegral_iff (A := 𝓞 K)).mp hg')`. Consider the case `zero => exact ⟨0, by simp⟩`.

Consider the case `add x y _ _ hx hy`. Take `⟨a, ha⟩` from `hx`. Take `⟨c, hc⟩` from `hy`. Conclude with `⟨a + c, by rw [dotProduct_add, map_add, ha, hc]⟩`. Consider the case `smul r x _ hx`.

Take `⟨a, ha⟩` from `hx`. Use `⟨r * a, ?_⟩` and prove the remaining obligations. Rewrite using `[dotProduct_smul, map_mul, ha]`. Both sides reduce to the same expression.
-/
theorem exists_int_smul_mem (F : HermLattice K i) (v : Fin i → K) :
    ∃ N : ℤ, N ≠ 0 ∧ (N : K) • v ∈ dualLattice F := by
  classical
  obtain ⟨S, hS⟩ := F.fg
  obtain ⟨N, hN, hint⟩ := exists_integral_multiples ℤ ℚ (S.image fun g => v ⬝ᵥ g)
  refine ⟨N, hN, fun x hx => ?_⟩
  rw [← hS] at hx
  induction hx using Submodule.span_induction with
  | mem g hg =>
    have hg' := hint _ (Finset.mem_image_of_mem _ hg)
    rw [smul_dotProduct, Int.cast_smul_eq_zsmul]
    exact RingHom.mem_range.mpr ((IsIntegralClosure.isIntegral_iff (A := 𝓞 K)).mp hg')
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨c, hc⟩ := hy
    exact ⟨a + c, by rw [dotProduct_add, map_add, ha, hc]⟩
  | smul r x _ hx =>
    obtain ⟨a, ha⟩ := hx
    refine ⟨r * a, ?_⟩
    rw [dotProduct_smul, map_mul, ha]
    rfl

variable {T : Type}

def w (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) (t : T) : dualStdModelField K i :=
  dualStdModelEmb K i (dualLatticeCoord b ⟨(), t⟩) * dualStdModelS K i * dualStdModelT K i

omit [NumberField K] in
/- English proof (translation)
Rewrite using `[dualStdModelS]`. Conclude with `(map_ne_zero_iff _ (IsFractionRing.injective (MvPolynomial Unit (MvPolynomial Unit (ProjField K i))) (dualStdModelField K i))).mpr (by simp [X_ne_zero])`.
-/
theorem S_ne_zero : dualStdModelS K i ≠ 0 := by
  rw [dualStdModelS]
  exact (map_ne_zero_iff _ (IsFractionRing.injective (MvPolynomial Unit (MvPolynomial Unit (ProjField K i)))
    (dualStdModelField K i))).mpr (by simp [X_ne_zero])

omit [NumberField K] in
/- English proof (translation)
Rewrite using `[dualStdModelT]`. Conclude with `(map_ne_zero_iff _ (IsFractionRing.injective (MvPolynomial Unit (MvPolynomial Unit (ProjField K i))) (dualStdModelField K i))).mpr (X_ne_zero _)`.
-/
theorem T_ne_zero : dualStdModelT K i ≠ 0 := by
  rw [dualStdModelT]
  exact (map_ne_zero_iff _ (IsFractionRing.injective (MvPolynomial Unit (MvPolynomial Unit (ProjField K i)))
    (dualStdModelField K i))).mpr (X_ne_zero _)

/- English proof (translation)
Rewrite using `[map_ne_zero_iff _ (dualStdModelEmb K i).injective, dualLatticeCoord_eq]`. Conclude with `evalForm_ne_zero fun h => b.ne_zero t ((Submodule.coe_eq_zero).mp h)`.
-/
theorem coord_ne_zero (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) (t : T) :
    dualStdModelEmb K i (dualLatticeCoord b ⟨(), t⟩) ≠ 0 := by
  rw [map_ne_zero_iff _ (dualStdModelEmb K i).injective, dualLatticeCoord_eq]
  exact evalForm_ne_zero fun h => b.ne_zero t ((Submodule.coe_eq_zero).mp h)

/- English proof (translation)
The claim follows from `mul_ne_zero (mul_ne_zero (coord_ne_zero b t) S_ne_zero) T_ne_zero`.
-/
theorem w_ne_zero (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) (t : T) : w b t ≠ 0 :=
  mul_ne_zero (mul_ne_zero (coord_ne_zero b t) S_ne_zero) T_ne_zero

/- English proof (translation)
Simplify using `only [w, u, dualLatticeCoord, map_sum, map_mul, Finset.sum_mul, embK, RingHom.comp_apply]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply, mul_assoc, mul_assoc, mul_assoc]`.
-/
theorem w_eq (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) (t : T) :
    w b t = ∑ j, embK K i ((b t : Fin i → K) j) * u K i j := by
  simp only [w, u, dualLatticeCoord, map_sum, map_mul, Finset.sum_mul, embK, RingHom.comp_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply, mul_assoc, mul_assoc, mul_assoc]

/- English proof (translation)
Take `⟨N, hN, hmem⟩` from `exists_int_smul_mem (HermLattice.standard K i) (a • (b c : Fin i → K))`. Take `⟨φ, hφ⟩ : ∃ φ : dualLattice (HermLattice.standard K i), (φ : Fin i → K) = (N : K) • a • (b c : Fin i → K)` from `⟨⟨_, hmem⟩, rfl⟩`. Use `⟨N, hN, fun t => b.repr φ t, ?_⟩` and prove the remaining obligations. Establish `hrepr` using `congrArg (fun ψ : dualLattice (HermLattice.standard K i) => evalForm i (ψ : Fin i → K)) (b.sum_repr φ)`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_zsmul, hφ, map_smul] at hrepr`.

Simplify using `only [← dualLatticeCoord_eq b, zsmul_eq_mul, Algebra.smul_def, map_intCast] at hrepr`. Establish `h2` using `congrArg (fun y => dualStdModelEmb K i y * dualStdModelS K i * dualStdModelT K i) hrepr`. Simplify using `only [map_sum, map_mul, map_intCast, Finset.sum_mul] at h2`. Simplify using `only [w, embK, RingHom.comp_apply, mul_assoc] at h2 ⊢`. Rewrite using `[h2]`.
-/
theorem exists_int_comb [Fintype T] (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) (c : T) (a : K) :
    ∃ N : ℤ, N ≠ 0 ∧ ∃ n : T → ℤ, ∑ t, (n t : dualStdModelField K i) * w b t = (N : _) * embK K i a * w b c := by
  obtain ⟨N, hN, hmem⟩ := exists_int_smul_mem (HermLattice.standard K i) (a • (b c : Fin i → K))
  obtain ⟨φ, hφ⟩ : ∃ φ : dualLattice (HermLattice.standard K i),
      (φ : Fin i → K) = (N : K) • a • (b c : Fin i → K) := ⟨⟨_, hmem⟩, rfl⟩
  refine ⟨N, hN, fun t => b.repr φ t, ?_⟩
  have hrepr := congrArg (fun ψ : dualLattice (HermLattice.standard K i) => evalForm i (ψ : Fin i → K))
    (b.sum_repr φ)
  simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_zsmul, hφ, map_smul] at hrepr
  simp only [← dualLatticeCoord_eq b, zsmul_eq_mul, Algebra.smul_def, map_intCast] at hrepr
  have h2 := congrArg (fun y => dualStdModelEmb K i y * dualStdModelS K i * dualStdModelT K i) hrepr
  simp only [map_sum, map_mul, map_intCast, Finset.sum_mul] at h2
  simp only [w, embK, RingHom.comp_apply, mul_assoc] at h2 ⊢
  rw [h2]

/- English proof (translation)
Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg`. Establish `hf : ∀ k, algebraMap Φ₀ _ (g k) ∈ Subfield.closure (Set.range (u K i))` using `fun k => by`. Rewrite using `[← hΦ]`. Conclude with `RingHom.mem_fieldRange.mpr ⟨g k, rfl⟩`.

Take `⟨D, -, hD0, hD⟩` from `exists_den_fin _ hf`. Use `choose q hq using fun k => RingHom.mem_range.mp (hD k)`. Simplify using `only [Algebra.smul_def] at hg`. Establish `hsum : ∑ k, embK K i (B k) * psiZ K i (q k) = 0`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun k _ => by rw [hq]; ring`. Use `_ = 0 := by rw [hg, mul_zero]`. Establish `h0` using `indep_int B q hsum`. Introduce `k`.

Establish `hk : D * algebraMap Φ₀ (dualStdModelField K i) (g k) = 0` using `by rw [← hq, h0, map_zero]`. Conclude with `(algebraMap Φ₀ (dualStdModelField K i)).injective (((mul_eq_zero.mp hk).resolve_left hD0).trans (map_zero _).symm)`.
-/
theorem linIndep {n : ℕ} (B : Module.Basis (Fin n) ℚ K) (Φ₀ : Type) [Field Φ₀]
    [Algebra Φ₀ (dualStdModelField K i)]
    (hΦ : (algebraMap Φ₀ (dualStdModelField K i)).fieldRange = Subfield.closure (Set.range (u K i))) :
    LinearIndependent Φ₀ fun k => embK K i (B k) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hf : ∀ k, algebraMap Φ₀ _ (g k) ∈ Subfield.closure (Set.range (u K i)) := fun k => by
    rw [← hΦ]; exact RingHom.mem_fieldRange.mpr ⟨g k, rfl⟩
  obtain ⟨D, -, hD0, hD⟩ := exists_den_fin _ hf
  choose q hq using fun k => RingHom.mem_range.mp (hD k)
  simp only [Algebra.smul_def] at hg
  have hsum : ∑ k, embK K i (B k) * psiZ K i (q k) = 0 := by
    calc ∑ k, embK K i (B k) * psiZ K i (q k)
        = D * ∑ k, algebraMap Φ₀ _ (g k) * embK K i (B k) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by rw [hq]; ring
      _ = 0 := by rw [hg, mul_zero]
  have h0 := indep_int B q hsum
  intro k
  have hk : D * algebraMap Φ₀ (dualStdModelField K i) (g k) = 0 := by rw [← hq, h0, map_zero]
  exact (algebraMap Φ₀ (dualStdModelField K i)).injective
    (((mul_eq_zero.mp hk).resolve_left hD0).trans (map_zero _).symm)

/- English proof (translation)
Establish `hq : ∀ q : ℚ, (q : dualStdModelField K i) = algebraMap Φ₀ _ ((q.num : Φ₀) / (q.den : Φ₀))` using `fun q => by`. Rewrite using `[map_div₀, map_intCast, map_natCast, Rat.cast_def]`. Rewrite using `[Algebra.adjoin_eq_span, show Submonoid.closure (Set.range (embK K i)) = (embK K i).range.toSubmonoid from Submonoid.closure_eq (embK K i).range.toSubmonoid]`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨a, rfl⟩`. Rewrite using `[← B.sum_repr a, map_sum]`. Use `Submodule.sum_mem _ fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Rat.smul_def, map_mul, map_ratCast, hq, ← Algebra.smul_def]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)`.

Conclude with `Submodule.span_mono (by rintro _ ⟨k, rfl⟩; exact ⟨B k, rfl⟩)`.
-/
theorem adjoin_embK_eq_span {n : ℕ} (B : Module.Basis (Fin n) ℚ K) (Φ₀ : Type) [Field Φ₀]
    [Algebra Φ₀ (dualStdModelField K i)] :
    Subalgebra.toSubmodule (Algebra.adjoin Φ₀ (Set.range (embK K i))) =
      Submodule.span Φ₀ (Set.range fun k => embK K i (B k)) := by
  have hq : ∀ q : ℚ, (q : dualStdModelField K i) = algebraMap Φ₀ _ ((q.num : Φ₀) / (q.den : Φ₀)) := fun q => by
    rw [map_div₀, map_intCast, map_natCast, Rat.cast_def]
  rw [Algebra.adjoin_eq_span, show Submonoid.closure (Set.range (embK K i)) = (embK K i).range.toSubmonoid from
    Submonoid.closure_eq (embK K i).range.toSubmonoid]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    rw [← B.sum_repr a, map_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [Rat.smul_def, map_mul, map_ratCast, hq, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · exact Submodule.span_mono (by rintro _ ⟨k, rfl⟩; exact ⟨B k, rfl⟩)

end StandardModelDualRank

end

end GroundTheory.Heights₂.Heights
