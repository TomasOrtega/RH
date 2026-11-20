import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPosGramFormIntegralLatticeProperties

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

noncomputable section

namespace GlobalTheory.HilbertThetaSeries.DualLevel

def trD (F : Type) [Field F] [NumberField F] : AddSubgroup F :=
  (Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 F) F)).toAddSubgroup

def intG (F : Type) [Field F] [NumberField F] : AddSubgroup F := (1 : Submodule (𝓞 F) F).toAddSubgroup

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Use `show x ∈ (1 : Submodule (𝓞 F) F) ↔ _`. Rewrite using `[Submodule.mem_one]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩`. Conclude with `RingOfIntegers.isIntegral_coe y`.

Introduce `h`. Conclude with `⟨⟨x, h⟩, rfl⟩`.
-/
theorem mem_intG {x : F} : x ∈ intG F ↔ IsIntegral ℤ x := by
  show x ∈ (1 : Submodule (𝓞 F) F) ↔ _
  rw [Submodule.mem_one]
  constructor
  · rintro ⟨y, rfl⟩
    exact RingOfIntegers.isIntegral_coe y
  · intro h
    exact ⟨⟨x, h⟩, rfl⟩

/- English proof (translation)
Use `show x ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 F) F) ↔ _`. Rewrite using `[Submodule.mem_traceDual]`. Prove the components needed by the constructor for the conclusion. Introduce `h o ho`. Take `⟨n, hn⟩` from `h o (mem_intG.2 ho)`.

Conclude with `⟨n, by rw [← Algebra.traceForm_apply, ← hn, eq_intCast]⟩`. Introduce `h a ha`. Take `⟨n, hn⟩` from `h a (mem_intG.1 ha)`. Conclude with `⟨n, by rw [Algebra.traceForm_apply, hn, eq_intCast]⟩`.
-/
theorem mem_trD {x : F} : x ∈ trD F ↔ ∀ o : F, IsIntegral ℤ o → ∃ n : ℤ, Algebra.trace ℚ F (x * o) = n := by
  show x ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 F) F) ↔ _
  rw [Submodule.mem_traceDual]
  constructor
  · intro h o ho
    obtain ⟨n, hn⟩ := h o (mem_intG.2 ho)
    exact ⟨n, by rw [← Algebra.traceForm_apply, ← hn, eq_intCast]⟩
  · intro h a ha
    obtain ⟨n, hn⟩ := h a (mem_intG.1 ha)
    exact ⟨n, by rw [Algebra.traceForm_apply, hn, eq_intCast]⟩

/- English proof (translation)
Introduce `_ hx` and use `Submodule.one_le_traceDual_one hx`.
-/
theorem intG_le_trD : intG F ≤ trD F := fun _ hx => Submodule.one_le_traceDual_one hx

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[← Submodule.span_int_eq_addSubgroupClosure, Submodule.mem_toAddSubgroup, mem_span_integralBasis, RingHom.mem_range]`. Use `show x ∈ (1 : Submodule (𝓞 F) F) ↔ _`. Rewrite using `[Submodule.mem_one]`.
-/
theorem intG_eq_closure : intG F = AddSubgroup.closure (Set.range (integralBasis F)) := by
  ext x
  rw [← Submodule.span_int_eq_addSubgroupClosure, Submodule.mem_toAddSubgroup, mem_span_integralBasis,
    RingHom.mem_range]
  show x ∈ (1 : Submodule (𝓞 F) F) ↔ _
  rw [Submodule.mem_one]

open scoped Classical in
/- English proof (translation)
Establish `h` using `Submodule.traceDual_span_of_basis ℤ (1 : Submodule (𝓞 F) F) (integralBasis F) (by`. Use extensionality with `x`. Rewrite using `[Submodule.restrictScalars_mem, Submodule.mem_one, mem_span_integralBasis, RingHom.mem_range])`. Use extensionality with `x`. Rewrite using `[← Submodule.span_int_eq_addSubgroupClosure, ← h]`.

Both sides reduce to the same expression.
-/
theorem trD_eq_closure : trD F = AddSubgroup.closure (Set.range (integralBasis F).traceDual) := by
  have h := Submodule.traceDual_span_of_basis ℤ (1 : Submodule (𝓞 F) F) (integralBasis F) (by
    ext x
    rw [Submodule.restrictScalars_mem, Submodule.mem_one, mem_span_integralBasis, RingHom.mem_range])
  ext x
  rw [← Submodule.span_int_eq_addSubgroupClosure, ← h]
  rfl

/- English proof (translation)
Establish `h` using `AddSubgroup.relIndex_eq_abs_det (intG F) (trD F) intG_le_trD (integralBasis F) (integralBasis F).traceDual intG_eq_closure trD_eq_closure`. Establish `hdet : (integralBasis F).traceDual.det (integralBasis F) = (discr F : ℚ)`. Rewrite using `[coe_discr, Algebra.discr_def, Module.Basis.det_apply]`. Use `congr 1`. Use extensionality with `i j`.

Rewrite using `[Module.Basis.toMatrix_apply, Module.Basis.traceDual_repr_apply, Algebra.traceMatrix_apply, Algebra.traceForm_apply, Algebra.traceForm_apply, mul_comm]`. Apply `Nat.cast_injective (R := ℚ)` to reduce the goal to its premises. Rewrite using `[h, hdet, Nat.cast_natAbs, Int.cast_abs]`.
-/
theorem relIndex_intG_trD : (intG F).relIndex (trD F) = (discr F).natAbs := by
  classical
  have h := AddSubgroup.relIndex_eq_abs_det (intG F) (trD F) intG_le_trD (integralBasis F)
    (integralBasis F).traceDual intG_eq_closure trD_eq_closure
  have hdet : (integralBasis F).traceDual.det (integralBasis F) = (discr F : ℚ) := by
    rw [coe_discr, Algebra.discr_def, Module.Basis.det_apply]
    congr 1
    ext i j
    rw [Module.Basis.toMatrix_apply, Module.Basis.traceDual_repr_apply, Algebra.traceMatrix_apply,
      Algebra.traceForm_apply, Algebra.traceForm_apply, mul_comm]
  apply Nat.cast_injective (R := ℚ)
  rw [h, hdet, Nat.cast_natAbs, Int.cast_abs]

/- English proof (translation)
Rewrite using `[← mem_intG, intG_eq_closure, ← Submodule.span_int_eq_addSubgroupClosure, Submodule.mem_toAddSubgroup]`. Rewrite using `[← (integralBasis F).sum_repr b]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Take `⟨n, hn⟩` from `h ((integralBasis F).traceDual i) (by`. Rewrite using `[trD_eq_closure]`.

Conclude with `AddSubgroup.subset_closure ⟨i, rfl⟩)`. Establish `hc : (integralBasis F).repr b i = n` using `by conv_lhs => rw [← (integralBasis F).traceDual_traceDual]`. Rewrite using `[Module.Basis.traceDual_repr_apply, Algebra.traceForm_apply, mul_comm, hn]`. Rewrite using `[hc, Int.cast_smul_eq_zsmul]`. Conclude with `Submodule.smul_mem _ n (Submodule.subset_span ⟨i, rfl⟩)`.
-/
theorem isIntegral_of_dual {b : F} (h : ∀ x ∈ trD F, ∃ n : ℤ, Algebra.trace ℚ F (x * b) = n) :
    IsIntegral ℤ b := by
  classical
  rw [← mem_intG, intG_eq_closure, ← Submodule.span_int_eq_addSubgroupClosure, Submodule.mem_toAddSubgroup]
  rw [← (integralBasis F).sum_repr b]
  refine Submodule.sum_mem _ fun i _ => ?_
  obtain ⟨n, hn⟩ := h ((integralBasis F).traceDual i) (by
    rw [trD_eq_closure]
    exact AddSubgroup.subset_closure ⟨i, rfl⟩)
  have hc : (integralBasis F).repr b i = n := by
    conv_lhs => rw [← (integralBasis F).traceDual_traceDual]
    rw [Module.Basis.traceDual_repr_apply, Algebra.traceForm_apply, mul_comm, hn]
  rw [hc, Int.cast_smul_eq_zsmul]
  exact Submodule.smul_mem _ n (Submodule.subset_span ⟨i, rfl⟩)

/- English proof (translation)
Establish `h1 : (d : F) ∈ IsLocalization.coeSubmodule F (differentIdeal ℤ (𝓞 F))` using `Submodule.mem_map_of_mem hd`. Rewrite `h1` using `[coeSubmodule_differentIdeal (A := ℤ) (K := ℚ) (L := F) (B := 𝓞 F)]`. Conclude with `mem_intG.1 (Submodule.mem_div_iff_forall_mul_mem.1 h1 w hw)`.
-/
theorem isIntegral_mul_of_mem_different {d : 𝓞 F} (hd : d ∈ differentIdeal ℤ (𝓞 F)) {w : F} (hw : w ∈ trD F) :
    IsIntegral ℤ ((d : F) * w) := by
  have h1 : (d : F) ∈ IsLocalization.coeSubmodule F (differentIdeal ℤ (𝓞 F)) :=
    Submodule.mem_map_of_mem hd
  rw [coeSubmodule_differentIdeal (A := ℤ) (K := ℚ) (L := F) (B := 𝓞 F)] at h1
  exact mem_intG.1 (Submodule.mem_div_iff_forall_mul_mem.1 h1 w hw)

/- English proof (translation)
Rewrite `hw`, the goal using `[mem_trD]`. Introduce `o ho`. Take `⟨n, hn⟩` from `hw (a * o) (ha.mul ho)`. Conclude with `⟨n, by rw [← hn]; congr 1; ring⟩`.
-/
theorem mul_mem_trD {a w : F} (ha : IsIntegral ℤ a) (hw : w ∈ trD F) : a * w ∈ trD F := by
  rw [mem_trD] at hw ⊢
  intro o ho
  obtain ⟨n, hn⟩ := hw (a * o) (ha.mul ho)
  exact ⟨n, by rw [← hn]; congr 1; ring⟩

variable {κ : Type} [Fintype κ] [DecidableEq κ]

/- English proof (translation)
Unfold `LL`. Rewrite using `[AddSubgroup.mem_pi]`. Simplify using `only [Set.mem_univ, true_implies]`. Both sides reduce to the same expression.
-/
theorem mem_LL {x : κ → F} : x ∈ LL F κ ↔ ∀ i, IsIntegral ℤ (x i) := by
  unfold LL
  rw [AddSubgroup.mem_pi]
  simp only [Set.mem_univ, true_implies]
  rfl

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[mem_LL, AddSubgroup.mem_pi]`. Simplify using `[mem_intG]`.
-/
theorem LL_eq_pi : LL F κ = AddSubgroup.pi Set.univ fun _ => intG F := by
  ext x
  rw [mem_LL, AddSubgroup.mem_pi]
  simp [mem_intG]

/- English proof (translation)
Rewrite `hx`, the goal using `[mem_LL]`. Introduce `i`. Simplify `ha.mul (hx i)` using `[Pi.smul_apply, smul_eq_mul]`.
-/
theorem smul_mem_LL {a : F} (ha : IsIntegral ℤ a) {x : κ → F} (hx : x ∈ LL F κ) : a • x ∈ LL F κ := by
  rw [mem_LL] at hx ⊢
  intro i
  simpa [Pi.smul_apply, smul_eq_mul] using ha.mul (hx i)

/- English proof (translation)
Unfold `BF`. Rewrite using `[Matrix.dotProduct_mulVec]`.
-/
theorem BF_eq_vecMul (G : Matrix κ κ ℤ) (y l : κ → F) :
    BF G y l = (y ᵥ* G.map (Int.cast : ℤ → F)) ⬝ᵥ l := by
  unfold BF
  rw [Matrix.dotProduct_mulVec]

/- English proof (translation)
Use `show (∀ l ∈ LL F κ, ∃ n : ℤ, Algebra.trace ℚ F (BF G y l) = n) ↔ _`. Prove the components needed by the constructor for the conclusion. Introduce `h j`. Rewrite using `[mem_trD]`. Introduce `o ho`.

Take `⟨n, hn⟩` from `h (Pi.single j o) (by`. Rewrite using `[mem_LL]`. Introduce `i`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality.

Simplify using `using ho`. Simplify using `only [Pi.single_apply, hij, if_false]`. Conclude with `isIntegral_zero)`. Use `⟨n, ?_⟩` and prove the remaining obligations. Rewrite using `[← hn, BF_eq_vecMul, dotProduct_single]`.

Introduce `h l hl`. Rewrite `hl` using `[mem_LL]`. Establish `hc : ∀ i, ∃ n : ℤ, Algebra.trace ℚ F ((y ᵥ* G.map (Int.cast : ℤ → F)) i * l i) = n` using `fun i => mem_trD.1 (h i) (l i) (hl i)`. Use `choose n hn using hc`. Use `⟨∑ i, n i, ?_⟩` and prove the remaining obligations.

Rewrite using `[BF_eq_vecMul, dotProduct, map_sum, Int.cast_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => hn i`.
-/
theorem mem_dualL_iff (G : Matrix κ κ ℤ) (y : κ → F) :
    y ∈ dualL F G ↔ ∀ j, (y ᵥ* G.map (Int.cast : ℤ → F)) j ∈ trD F := by
  show (∀ l ∈ LL F κ, ∃ n : ℤ, Algebra.trace ℚ F (BF G y l) = n) ↔ _
  constructor
  · intro h j
    rw [mem_trD]
    intro o ho
    obtain ⟨n, hn⟩ := h (Pi.single j o) (by
      rw [mem_LL]
      intro i
      by_cases hij : i = j
      · subst hij
        simpa using ho
      · simp only [Pi.single_apply, hij, if_false]
        exact isIntegral_zero)
    refine ⟨n, ?_⟩
    rw [← hn, BF_eq_vecMul, dotProduct_single]
  · intro h l hl
    rw [mem_LL] at hl
    have hc : ∀ i, ∃ n : ℤ, Algebra.trace ℚ F ((y ᵥ* G.map (Int.cast : ℤ → F)) i * l i) = n :=
      fun i => mem_trD.1 (h i) (l i) (hl i)
    choose n hn using hc
    refine ⟨∑ i, n i, ?_⟩
    rw [BF_eq_vecMul, dotProduct, map_sum, Int.cast_sum]
    exact Finset.sum_congr rfl fun i _ => hn i

end GlobalTheory.HilbertThetaSeries.DualLevel
end

noncomputable section
namespace GlobalTheory.HilbertThetaSeries.DualLevel

open scoped Classical in
/- English proof (translation)
Use extensionality with `x`. Rewrite using `[← Submodule.span_int_eq_addSubgroupClosure, Submodule.mem_toAddSubgroup, Module.Basis.mem_span_iff_repr_mem, LL_eq_pi, AddSubgroup.mem_pi]`. Repeatedly rewrite using `[intG_eq_closure, ← Submodule.span_int_eq_addSubgroupClosure, Submodule.mem_toAddSubgroup, Module.Basis.mem_span_iff_repr_mem, Pi.basis_repr]`. Simplify using `[Sigma.forall]`.
-/
theorem LL_eq_closure (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [DecidableEq κ] :
    LL F κ = AddSubgroup.closure (Set.range (Pi.basis fun _ : κ => integralBasis F)) := by
  ext x
  rw [← Submodule.span_int_eq_addSubgroupClosure, Submodule.mem_toAddSubgroup,
    Module.Basis.mem_span_iff_repr_mem, LL_eq_pi, AddSubgroup.mem_pi]
  simp_rw [intG_eq_closure, ← Submodule.span_int_eq_addSubgroupClosure, Submodule.mem_toAddSubgroup,
    Module.Basis.mem_span_iff_repr_mem, Pi.basis_repr]
  simp [Sigma.forall]

/- English proof (translation)
The claim follows from `(Int.cast_det G).symm`.
-/
theorem det_map_cast {F : Type} [Field F] {κ : Type} [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ) :
    (G.map (Int.cast : ℤ → F)).det = (G.det : F) := (Int.cast_det G).symm

/- English proof (translation)
Introduce and unpack `_ ⟨x, hx, rfl⟩`. Rewrite `hx` using `[SetLike.mem_coe, mem_LL]`. Rewrite using `[mem_LL]`. Introduce `j`. Establish `hx' : ∀ i, x i ∈ integralClosure ℤ F` using `hx`.

Use `show (x ᵥ* G.map (Int.cast : ℤ → F)) j ∈ integralClosure ℤ F`. Simplify using `only [Matrix.vecMul, dotProduct, Matrix.map_apply]`. Conclude with `Subalgebra.sum_mem _ fun i _ => Subalgebra.mul_mem _ (hx' i) (Subalgebra.intCast_mem _ _)`.
-/
theorem map_LL_le {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ) :
    (LL F κ).map (Matrix.vecMulLinear (G.map (Int.cast : ℤ → F))).toAddMonoidHom ≤ LL F κ := by
  rintro _ ⟨x, hx, rfl⟩
  rw [SetLike.mem_coe, mem_LL] at hx
  rw [mem_LL]
  intro j
  have hx' : ∀ i, x i ∈ integralClosure ℤ F := hx
  show (x ᵥ* G.map (Int.cast : ℤ → F)) j ∈ integralClosure ℤ F
  simp only [Matrix.vecMul, dotProduct, Matrix.map_apply]
  exact Subalgebra.sum_mem _ fun i _ => Subalgebra.mul_mem _ (hx' i) (Subalgebra.intCast_mem _ _)

/- English proof (translation)
Introduce `F _ _ κ _ _ G hG`. Set `B` to `Pi.basis fun _ : κ => integralBasis F`. Set `fF : (κ → F) →ₗ[F] (κ → F)` to `Matrix.vecMulLinear (G.map (Int.cast : ℤ → F))`. Set `fQ : (κ → F) →ₗ[ℚ] (κ → F)` to `fF.restrictScalars ℚ`. Establish `hdetF : LinearMap.det fF = (G.det : F)`.

Establish `hT : fF = Matrix.toLin' (G.map (Int.cast : ℤ → F))ᵀ` using `LinearMap.ext fun v => (Matrix.mulVec_transpose _ _).symm`. Rewrite using `[hT, LinearMap.det_toLin', Matrix.det_transpose, det_map_cast]`. Establish `hdetQ : LinearMap.det fQ = (G.det : ℚ) ^ Module.finrank ℚ F`. Rewrite using `[LinearMap.det_restrictScalars, hdetF, ← map_intCast (algebraMap ℚ F), Algebra.norm_algebraMap]`. Establish `hne : LinearMap.det fQ ≠ 0`.

Rewrite using `[hdetQ]`. Conclude with `pow_ne_zero _ (Int.cast_ne_zero.2 hG)`. Set `e` to `LinearMap.equivOfDetNeZero fQ hne`. Establish `hfun : ⇑(B.map e) = ⇑fQ ∘ ⇑B`. Use function extensionality and compare the values at `i`.

Both sides reduce to the same expression. Establish `h1 : (LL F κ).map (Matrix.vecMulLinear (G.map (Int.cast : ℤ → F))).toAddMonoidHom = AddSubgroup.closure (Set.range (B.map e))`. Rewrite using `[LL_eq_closure, AddMonoidHom.map_closure, ← Set.range_comp, hfun]`. Both sides reduce to the same expression. Establish `h` using `AddSubgroup.relIndex_eq_abs_det _ _ (map_LL_le G) (B.map e) B h1 (LL_eq_closure F κ)`.

Establish `hd : B.det (B.map e) = (G.det : ℚ) ^ Module.finrank ℚ F`. Rewrite using `[hfun, Module.Basis.det_comp, Module.Basis.det_self, mul_one, hdetQ]`. Apply `Nat.cast_injective (R := ℚ)` to reduce the goal to its premises. Rewrite using `[h, hd, abs_pow, Nat.cast_pow, Nat.cast_natAbs, Int.cast_abs]`.
-/
theorem relIndex_map_LL : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ), G.det ≠ 0 → ((LL F κ).map (Matrix.vecMulLinear (G.map (Int.cast : ℤ → F))).toAddMonoidHom).relIndex (LL F κ) = G.det.natAbs ^ Module.finrank ℚ F := by
  intro F _ _ κ _ _ G hG
  classical
  let B := Pi.basis fun _ : κ => integralBasis F
  let fF : (κ → F) →ₗ[F] (κ → F) := Matrix.vecMulLinear (G.map (Int.cast : ℤ → F))
  let fQ : (κ → F) →ₗ[ℚ] (κ → F) := fF.restrictScalars ℚ
  have hdetF : LinearMap.det fF = (G.det : F) := by
    have hT : fF = Matrix.toLin' (G.map (Int.cast : ℤ → F))ᵀ :=
      LinearMap.ext fun v => (Matrix.mulVec_transpose _ _).symm
    rw [hT, LinearMap.det_toLin', Matrix.det_transpose, det_map_cast]
  have hdetQ : LinearMap.det fQ = (G.det : ℚ) ^ Module.finrank ℚ F := by
    rw [LinearMap.det_restrictScalars, hdetF, ← map_intCast (algebraMap ℚ F), Algebra.norm_algebraMap]
  have hne : LinearMap.det fQ ≠ 0 := by
    rw [hdetQ]
    exact pow_ne_zero _ (Int.cast_ne_zero.2 hG)
  let e := LinearMap.equivOfDetNeZero fQ hne
  have hfun : ⇑(B.map e) = ⇑fQ ∘ ⇑B := by
    funext i
    rfl
  have h1 : (LL F κ).map (Matrix.vecMulLinear (G.map (Int.cast : ℤ → F))).toAddMonoidHom =
      AddSubgroup.closure (Set.range (B.map e)) := by
    rw [LL_eq_closure, AddMonoidHom.map_closure, ← Set.range_comp, hfun]
    rfl
  have h := AddSubgroup.relIndex_eq_abs_det _ _ (map_LL_le G) (B.map e) B h1 (LL_eq_closure F κ)
  have hd : B.det (B.map e) = (G.det : ℚ) ^ Module.finrank ℚ F := by
    rw [hfun, Module.Basis.det_comp, Module.Basis.det_self, mul_one, hdetQ]
  apply Nat.cast_injective (R := ℚ)
  rw [h, hd, abs_pow, Nat.cast_pow, Nat.cast_natAbs, Int.cast_abs]

end GlobalTheory.HilbertThetaSeries.DualLevel
end

noncomputable section
namespace GlobalTheory.HilbertThetaSeries.DualLevel
variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] [DecidableEq κ]

/- English proof (translation)
Set `f : (ι → L) →+ (ι → G)` to `AddMonoidHom.compLeft L.subtype ι`. Establish `hr : f.range = AddSubgroup.pi Set.univ fun _ : ι => L`. Use extensionality with `x`. Simplify using `only [AddMonoidHom.mem_range, AddSubgroup.mem_pi, Set.mem_univ, true_implies]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨y, rfl⟩ i`. Conclude with `(y i).2`. Introduce `hx`. Conclude with `⟨fun i => ⟨x i, hx i⟩, rfl⟩`. Establish `hc : (AddSubgroup.pi Set.univ fun _ : ι => L').comap f = AddSubgroup.pi Set.univ fun _ : ι => L'.comap L.subtype`.

Use extensionality with `x`. Simplify using `only [AddSubgroup.mem_comap, AddSubgroup.mem_pi, Set.mem_univ, true_implies]`. Both sides reduce to the same expression. Rewrite using `[← hr, ← AddSubgroup.index_comap, hc, AddSubgroup.index_pi, Finset.prod_const, Finset.card_univ, AddSubgroup.index_comap, AddSubgroup.range_subtype]`.
-/
theorem relIndex_pi_const {ι G : Type} [Fintype ι] [AddCommGroup G] (L L' : AddSubgroup G) :
    (AddSubgroup.pi Set.univ fun _ : ι => L').relIndex (AddSubgroup.pi Set.univ fun _ : ι => L) =
      L'.relIndex L ^ Fintype.card ι := by
  let f : (ι → L) →+ (ι → G) := AddMonoidHom.compLeft L.subtype ι
  have hr : f.range = AddSubgroup.pi Set.univ fun _ : ι => L := by
    ext x
    simp only [AddMonoidHom.mem_range, AddSubgroup.mem_pi, Set.mem_univ, true_implies]
    constructor
    · rintro ⟨y, rfl⟩ i
      exact (y i).2
    · intro hx
      exact ⟨fun i => ⟨x i, hx i⟩, rfl⟩
  have hc : (AddSubgroup.pi Set.univ fun _ : ι => L').comap f =
      AddSubgroup.pi Set.univ fun _ : ι => L'.comap L.subtype := by
    ext x
    simp only [AddSubgroup.mem_comap, AddSubgroup.mem_pi, Set.mem_univ, true_implies]
    rfl
  rw [← hr, ← AddSubgroup.index_comap, hc, AddSubgroup.index_pi, Finset.prod_const, Finset.card_univ,
    AddSubgroup.index_comap, AddSubgroup.range_subtype]

/- English proof (translation)
Take `⟨hpd, -⟩` from `hG`. Establish `h` using `hpd.det_pos`. Rewrite `h` using `[← Int.cast_det]`. Conclude with `h` after adjusting the coercions.
-/
theorem det_pos_of_evenPos {G : Matrix κ κ ℤ} (hG : EvenPos G) : 0 < G.det := by
  obtain ⟨hpd, -⟩ := hG
  have h := hpd.det_pos
  rw [← Int.cast_det] at h
  exact_mod_cast h

/- English proof (translation)
Establish `hadj : G.adjugate.map (Int.cast : ℤ → F) = (G.map (Int.cast : ℤ → F)).adjugate` using `(Int.castRingHom F).map_adjugate G`. Rewrite using `[hadj, Matrix.vecMul_vecMul, Matrix.mul_adjugate, det_map_cast, Matrix.vecMul_smul, Matrix.vecMul_one]`.
-/
private theorem det_smul_eq_vecMul_adjugate (G : Matrix κ κ ℤ) (y : κ → F) :
    (G.det : F) • y = (y ᵥ* G.map (Int.cast : ℤ → F)) ᵥ* G.adjugate.map (Int.cast : ℤ → F) := by
  have hadj : G.adjugate.map (Int.cast : ℤ → F) = (G.map (Int.cast : ℤ → F)).adjugate :=
    (Int.castRingHom F).map_adjugate G
  rw [hadj, Matrix.vecMul_vecMul, Matrix.mul_adjugate, det_map_cast, Matrix.vecMul_smul,
    Matrix.vecMul_one]

/- English proof (translation)
Rewrite `hx`, `hz` using `[mem_LL]`. Establish `hx' : ∀ i, x i ∈ integralClosure ℤ F` using `hx`. Establish `hz' : ∀ i, z i ∈ integralClosure ℤ F` using `hz`. Use `show BF G x z ∈ integralClosure ℤ F`. Unfold `BF`.

Simplify using `only [dotProduct, Matrix.mulVec, Matrix.map_apply]`. Conclude with `Subalgebra.sum_mem _ fun i _ => Subalgebra.mul_mem _ (hx' i) (Subalgebra.sum_mem _ fun j _ => Subalgebra.mul_mem _ (Subalgebra.intCast_mem _ _) (hz' j))`.
-/
private theorem bf_isIntegral_of_mem_LL (G : Matrix κ κ ℤ) {x z : κ → F} (hx : x ∈ LL F κ)
    (hz : z ∈ LL F κ) : IsIntegral ℤ (BF G x z) := by
  rw [mem_LL] at hx hz
  have hx' : ∀ i, x i ∈ integralClosure ℤ F := hx
  have hz' : ∀ i, z i ∈ integralClosure ℤ F := hz
  show BF G x z ∈ integralClosure ℤ F
  unfold BF
  simp only [dotProduct, Matrix.mulVec, Matrix.map_apply]
  exact Subalgebra.sum_mem _ fun i _ => Subalgebra.mul_mem _ (hx' i)
    (Subalgebra.sum_mem _ fun j _ => Subalgebra.mul_mem _ (Subalgebra.intCast_mem _ _) (hz' j))

/- English proof (translation)
Establish `hv` using `(mem_dualL_iff G y).1 hy`. Rewrite using `[mem_LL]`. Introduce `j`. Establish `he : ((c * (G.det : F)) • y) j = ∑ i, (c * (y ᵥ* G.map (Int.cast : ℤ → F)) i) * (G.adjugate i j : F)`. Rewrite using `[mul_smul, det_smul_eq_vecMul_adjugate]`.

Simplify using `only [Pi.smul_apply, smul_eq_mul, Matrix.vecMul, dotProduct, Matrix.map_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]`. Rewrite using `[he]`. Use `show (∑ i, (c * (y ᵥ* G.map (Int.cast : ℤ → F)) i) * (G.adjugate i j : F)) ∈ integralClosure ℤ F`. Conclude with `Subalgebra.sum_mem _ fun i _ => Subalgebra.mul_mem _ (hc _ (hv i)) (Subalgebra.intCast_mem _ _)`.
-/
private theorem mul_det_smul_mem_LL_of_mem_dualL (G : Matrix κ κ ℤ) {y : κ → F} (hy : y ∈ dualL F G) {c : F}
    (hc : ∀ w ∈ trD F, IsIntegral ℤ (c * w)) : (c * (G.det : F)) • y ∈ LL F κ := by
  have hv := (mem_dualL_iff G y).1 hy
  rw [mem_LL]
  intro j
  have he : ((c * (G.det : F)) • y) j =
      ∑ i, (c * (y ᵥ* G.map (Int.cast : ℤ → F)) i) * (G.adjugate i j : F) := by
    rw [mul_smul, det_smul_eq_vecMul_adjugate]
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.vecMul, dotProduct, Matrix.map_apply, Finset.mul_sum,
      Finset.sum_mul, mul_assoc]
  rw [he]
  show (∑ i, (c * (y ᵥ* G.map (Int.cast : ℤ → F)) i) * (G.adjugate i j : F)) ∈ integralClosure ℤ F
  exact Subalgebra.sum_mem _ fun i _ => Subalgebra.mul_mem _ (hc _ (hv i)) (Subalgebra.intCast_mem _ _)

/- English proof (translation)
Take `⟨h, -⟩` from `hG`. Establish `hs : Gᵀ = G`. Use extensionality with `i j`. Use `congrFun (congrFun h.isHermitian.eq i) j` as an intermediate fact. Simplify using `only [Matrix.conjTranspose_apply, Matrix.map_apply, star_trivial] at this`.

Rewrite using `[Matrix.transpose_apply]`. Conclude with `this` after adjusting the coercions. Rewrite using `[← Matrix.transpose_map, hs]`.
-/
private theorem map_intCast_transpose_of_evenPos (G : Matrix κ κ ℤ) (hG : EvenPos G) :
    (G.map (Int.cast : ℤ → F))ᵀ = G.map (Int.cast : ℤ → F) := by
  obtain ⟨h, -⟩ := hG
  have hs : Gᵀ = G := by
    ext i j
    have := congrFun (congrFun h.isHermitian.eq i) j
    simp only [Matrix.conjTranspose_apply, Matrix.map_apply, star_trivial] at this
    rw [Matrix.transpose_apply]
    exact_mod_cast this
  rw [← Matrix.transpose_map, hs]

set_option maxHeartbeats 800000 in

/- English proof (translation)
Introduce `F _ _ κ _ _ G hG`. Establish `hdet : G.det ≠ 0` using `(det_pos_of_evenPos hG).ne'`. Establish `hunit : IsUnit (G.map (Int.cast : ℤ → F)).det`. Rewrite using `[det_map_cast]`. Conclude with `isUnit_iff_ne_zero.2 (Int.cast_ne_zero.2 hdet)`.

Establish `hsym` using `map_intCast_transpose_of_evenPos (F := F) G hG`. Use `⟨?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `y hy d hd`. Rewrite using `[mul_comm]`. Conclude with `mul_det_smul_mem_LL_of_mem_dualL G hy fun w hw => isIntegral_mul_of_mem_different hd hw`.

Establish `hm0 : discr F * G.det ≠ 0` using `mul_ne_zero (discr_ne_zero F) hdet`. Use `⟨2 * (discr F * G.det).natAbs ^ 2, by positivity, fun y hy => ?_⟩` and prove the remaining obligations. Establish `hD : ∀ w ∈ trD F, IsIntegral ℤ ((discr F : F) * w)`. Introduce `w hw`. Use `isIntegral_mul_of_mem_different (discr_mem_differentIdeal F (𝓞 F)) hw` as an intermediate fact.

Simplify using `using this`. Establish `h1` using `mul_det_smul_mem_LL_of_mem_dualL G hy hD`. Establish `hs : ((discr F * G.det).natAbs : F) = ((discr F * G.det).sign : F) * ((discr F : F) * (G.det : F))`. Establish `h2 : ((discr F * G.det).natAbs : ℤ) = (discr F * G.det) * (discr F * G.det).sign` using `(Int.mul_sign_self _).symm`. Establish `h3 : (((discr F * G.det).natAbs : ℕ) : F) = (((discr F * G.det).natAbs : ℤ) : F)` using `(Int.cast_natCast _).symm`.

Rewrite using `[h3, h2, Int.cast_mul, Int.cast_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hu : ((discr F * G.det).natAbs : F) • y ∈ LL F κ`. Rewrite using `[hs, mul_smul]`. Conclude with `smul_mem_LL (Subalgebra.intCast_mem (integralClosure ℤ F) _) h1`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `he : ((2 * (discr F * G.det).natAbs ^ 2 : ℕ) : F) • y = ((2 * (discr F * G.det).natAbs : ℕ) : F) • (((discr F * G.det).natAbs : F) • y)`. Rewrite using `[← mul_smul]`. Use `push_cast`. Put the polynomial expressions in normal form.

Rewrite using `[he]`. Conclude with `smul_mem_LL (Subalgebra.natCast_mem (integralClosure ℤ F) _) hu`. Establish `hq : ((2 * (discr F * G.det).natAbs ^ 2 : ℕ) : F) * QF G y = BF G (((discr F * G.det).natAbs : F) • y) (((discr F * G.det).natAbs : F) • y)`. Unfold `QF BF`. Rewrite using `[Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]`.

Establish `h2 : (2 : F) ≠ 0` using `two_ne_zero`. Rewrite using `[mul_div_assoc', div_eq_iff h2]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hq]`.

Conclude with `bf_isIntegral_of_mem_LL G hu hu`. Introduce `y hy`. Rewrite using `[mem_LL]`. Introduce `j`. Apply `isIntegral_of_dual` to reduce the goal to its premises.

Introduce `x hx`. Establish `hGν : G.map (Int.cast : ℤ → F) *ᵥ ((G.map (Int.cast : ℤ → F))⁻¹ *ᵥ Pi.single j x) = Pi.single j x`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec]`. Establish `hνmem : (G.map (Int.cast : ℤ → F))⁻¹ *ᵥ Pi.single j x ∈ dualL F G`. Rewrite using `[mem_dualL_iff]`.

Introduce `i`. Rewrite using `[← Matrix.mulVec_transpose, hsym, hGν]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using `using hx`.

Simplify using `only [Pi.single_apply, hij, if_false]`. Conclude with `zero_mem _`. Take `⟨n, hn⟩` from `hy _ hνmem`. Use `⟨n, ?_⟩` and prove the remaining obligations. Rewrite using `[← hn]`.

Unfold `BF`. Rewrite using `[hGν, dotProduct_single, mul_comm]`. Introduce `a y ha hy`. Rewrite `hy`, the goal using `[mem_dualL_iff]`. Introduce `j`.

Rewrite using `[Matrix.smul_vecMul, Pi.smul_apply, smul_eq_mul]`. Conclude with `mul_mem_trD ha (hy j)`. Establish `hisU : IsUnit (G.map (Int.cast : ℤ → F))` using `(Matrix.isUnit_iff_isUnit_det _).2 hunit`. Establish `hinj : Function.Injective (Matrix.vecMulLinear (G.map (Int.cast : ℤ → F))).toAddMonoidHom` using `Matrix.vecMul_injective_iff_isUnit.2 hisU`. Establish `hsurj : Function.Surjective (Matrix.vecMulLinear (G.map (Int.cast : ℤ → F))).toAddMonoidHom` using `Matrix.vecMul_surjective_iff_isUnit.2 hisU`.

Establish `hdual : dualL F G = (AddSubgroup.pi Set.univ fun _ : κ => trD F).comap (Matrix.vecMulLinear (G.map (Int.cast : ℤ → F))).toAddMonoidHom`. Use extensionality with `y`. Rewrite using `[mem_dualL_iff, AddSubgroup.mem_comap, AddSubgroup.mem_pi]`. Simplify using `only [Set.mem_univ, true_implies]`. Both sides reduce to the same expression.

Establish `hkey : (LL F κ).relIndex (dualL F G) = ((LL F κ).map (Matrix.vecMulLinear (G.map (Int.cast : ℤ → F))).toAddMonoidHom).relIndex (AddSubgroup.pi Set.univ fun _ : κ => trD F)`. Rewrite using `[hdual]`. Use `conv_lhs => rw [← AddSubgroup.comap_map_eq_self_of_injective hinj (LL F κ)]`. Rewrite using `[AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective hsurj]`. Establish `hLP : LL F κ ≤ AddSubgroup.pi Set.univ fun _ : κ => trD F`.

Rewrite using `[LL_eq_pi]`. Introduce `x hx`. Rewrite `hx`, the goal using `[AddSubgroup.mem_pi]`. Conclude with `fun i hi => intG_le_trD (hx i hi)`. Rewrite using `[hkey, ← AddSubgroup.relIndex_mul_relIndex _ _ _ (map_LL_le G) hLP, relIndex_map_LL F κ G hdet, LL_eq_pi, relIndex_pi_const, relIndex_intG_trD]`.

Establish `hpos` using `det_pos_of_evenPos hG`. Use `push_cast`. Rewrite using `[abs_of_pos hpos]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dual_level_index : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ), EvenPos G → (∀ y : κ → F, y ∈ dualL F G → ∀ d : 𝓞 F, d ∈ differentIdeal ℤ (𝓞 F) → ((G.det : F) * d) • y ∈ LL F κ) ∧ (∃ N : ℕ, 0 < N ∧ ∀ y ∈ dualL F G, (N : F) • y ∈ LL F κ ∧ IsIntegral ℤ ((N : F) * QF G y)) ∧ (∀ y : κ → F, (∀ ν ∈ dualL F G, ∃ n : ℤ, Algebra.trace ℚ F (BF G y ν) = n) → y ∈ LL F κ) ∧ (∀ (a : F) (y : κ → F), IsIntegral ℤ a → y ∈ dualL F G → a • y ∈ dualL F G) ∧ ((LL F κ).relIndex (dualL F G) : ℤ) = ((discr F).natAbs : ℤ) ^ Fintype.card κ * G.det ^ Module.finrank ℚ F := by
  intro F _ _ κ _ _ G hG
  have hdet : G.det ≠ 0 := (det_pos_of_evenPos hG).ne'
  have hunit : IsUnit (G.map (Int.cast : ℤ → F)).det := by
    rw [det_map_cast]
    exact isUnit_iff_ne_zero.2 (Int.cast_ne_zero.2 hdet)
  have hsym := map_intCast_transpose_of_evenPos (F := F) G hG
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro y hy d hd
    rw [mul_comm]
    exact mul_det_smul_mem_LL_of_mem_dualL G hy fun w hw => isIntegral_mul_of_mem_different hd hw
  · have hm0 : discr F * G.det ≠ 0 := mul_ne_zero (discr_ne_zero F) hdet
    refine ⟨2 * (discr F * G.det).natAbs ^ 2, by positivity, fun y hy => ?_⟩
    have hD : ∀ w ∈ trD F, IsIntegral ℤ ((discr F : F) * w) := by
      intro w hw
      have := isIntegral_mul_of_mem_different (discr_mem_differentIdeal F (𝓞 F)) hw
      simpa using this
    have h1 := mul_det_smul_mem_LL_of_mem_dualL G hy hD
    have hs : ((discr F * G.det).natAbs : F) =
        ((discr F * G.det).sign : F) * ((discr F : F) * (G.det : F)) := by
      have h2 : ((discr F * G.det).natAbs : ℤ) = (discr F * G.det) * (discr F * G.det).sign :=
        (Int.mul_sign_self _).symm
      have h3 : (((discr F * G.det).natAbs : ℕ) : F) = (((discr F * G.det).natAbs : ℤ) : F) :=
        (Int.cast_natCast _).symm
      rw [h3, h2, Int.cast_mul, Int.cast_mul]
      ring
    have hu : ((discr F * G.det).natAbs : F) • y ∈ LL F κ := by
      rw [hs, mul_smul]
      exact smul_mem_LL (Subalgebra.intCast_mem (integralClosure ℤ F) _) h1
    refine ⟨?_, ?_⟩
    · have he : ((2 * (discr F * G.det).natAbs ^ 2 : ℕ) : F) • y =
          ((2 * (discr F * G.det).natAbs : ℕ) : F) • (((discr F * G.det).natAbs : F) • y) := by
        rw [← mul_smul]
        push_cast
        ring_nf
      rw [he]
      exact smul_mem_LL (Subalgebra.natCast_mem (integralClosure ℤ F) _) hu
    · have hq : ((2 * (discr F * G.det).natAbs ^ 2 : ℕ) : F) * QF G y =
          BF G (((discr F * G.det).natAbs : F) • y) (((discr F * G.det).natAbs : F) • y) := by
        unfold QF BF
        rw [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
        have h2 : (2 : F) ≠ 0 := two_ne_zero
        rw [mul_div_assoc', div_eq_iff h2]
        push_cast
        ring
      rw [hq]
      exact bf_isIntegral_of_mem_LL G hu hu
  · intro y hy
    rw [mem_LL]
    intro j
    apply isIntegral_of_dual
    intro x hx
    have hGν : G.map (Int.cast : ℤ → F) *ᵥ ((G.map (Int.cast : ℤ → F))⁻¹ *ᵥ Pi.single j x) =
        Pi.single j x := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec]
    have hνmem : (G.map (Int.cast : ℤ → F))⁻¹ *ᵥ Pi.single j x ∈ dualL F G := by
      rw [mem_dualL_iff]
      intro i
      rw [← Matrix.mulVec_transpose, hsym, hGν]
      by_cases hij : i = j
      · subst hij
        simpa using hx
      · simp only [Pi.single_apply, hij, if_false]
        exact zero_mem _
    obtain ⟨n, hn⟩ := hy _ hνmem
    refine ⟨n, ?_⟩
    rw [← hn]
    unfold BF
    rw [hGν, dotProduct_single, mul_comm]
  · intro a y ha hy
    rw [mem_dualL_iff] at hy ⊢
    intro j
    rw [Matrix.smul_vecMul, Pi.smul_apply, smul_eq_mul]
    exact mul_mem_trD ha (hy j)
  · have hisU : IsUnit (G.map (Int.cast : ℤ → F)) := (Matrix.isUnit_iff_isUnit_det _).2 hunit
    have hinj : Function.Injective (Matrix.vecMulLinear (G.map (Int.cast : ℤ → F))).toAddMonoidHom :=
      Matrix.vecMul_injective_iff_isUnit.2 hisU
    have hsurj : Function.Surjective (Matrix.vecMulLinear (G.map (Int.cast : ℤ → F))).toAddMonoidHom :=
      Matrix.vecMul_surjective_iff_isUnit.2 hisU
    have hdual : dualL F G = (AddSubgroup.pi Set.univ fun _ : κ => trD F).comap
        (Matrix.vecMulLinear (G.map (Int.cast : ℤ → F))).toAddMonoidHom := by
      ext y
      rw [mem_dualL_iff, AddSubgroup.mem_comap, AddSubgroup.mem_pi]
      simp only [Set.mem_univ, true_implies]
      rfl
    have hkey : (LL F κ).relIndex (dualL F G) =
        ((LL F κ).map (Matrix.vecMulLinear (G.map (Int.cast : ℤ → F))).toAddMonoidHom).relIndex
          (AddSubgroup.pi Set.univ fun _ : κ => trD F) := by
      rw [hdual]
      conv_lhs => rw [← AddSubgroup.comap_map_eq_self_of_injective hinj (LL F κ)]
      rw [AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective hsurj]
    have hLP : LL F κ ≤ AddSubgroup.pi Set.univ fun _ : κ => trD F := by
      rw [LL_eq_pi]
      intro x hx
      rw [AddSubgroup.mem_pi] at hx ⊢
      exact fun i hi => intG_le_trD (hx i hi)
    rw [hkey, ← AddSubgroup.relIndex_mul_relIndex _ _ _ (map_LL_le G) hLP, relIndex_map_LL F κ G hdet,
      LL_eq_pi, relIndex_pi_const, relIndex_intG_trD]
    have hpos := det_pos_of_evenPos hG
    push_cast
    rw [abs_of_pos hpos]
    ring

end GlobalTheory.HilbertThetaSeries.DualLevel

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.HilbertThetaSeries.DualLevel.dual_level_index | exact GlobalTheory.HilbertThetaSeries.DualLevel.dual_level_index | (intros; apply GlobalTheory.HilbertThetaSeries.DualLevel.dual_level_index <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.dualLattice_index_eq_discr_pow_mul_det_pow : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ), EvenPos G → (∀ y : κ → F, y ∈ dualL F G → ∀ d : 𝓞 F, d ∈ differentIdeal ℤ (𝓞 F) → ((G.det : F) * d) • y ∈ LL F κ) ∧ (∃ N : ℕ, 0 < N ∧ ∀ y ∈ dualL F G, (N : F) • y ∈ LL F κ ∧ IsIntegral ℤ ((N : F) * QF G y)) ∧ (∀ y : κ → F, (∀ ν ∈ dualL F G, ∃ n : ℤ, Algebra.trace ℚ F (BF G y ν) = n) → y ∈ LL F κ) ∧ (∀ (a : F) (y : κ → F), IsIntegral ℤ a → y ∈ dualL F G → a • y ∈ dualL F G) ∧ ((LL F κ).relIndex (dualL F G) : ℤ) = ((discr F).natAbs : ℤ) ^ Fintype.card κ * G.det ^ Module.finrank ℚ F := by
  first | exact @GlobalTheory.HilbertThetaSeries.DualLevel.dual_level_index | exact GlobalTheory.HilbertThetaSeries.DualLevel.dual_level_index | (intros; apply GlobalTheory.HilbertThetaSeries.DualLevel.dual_level_index <;> assumption)
