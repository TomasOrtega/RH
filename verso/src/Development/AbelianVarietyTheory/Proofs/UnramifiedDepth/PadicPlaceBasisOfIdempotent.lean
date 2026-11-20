import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.LengthDegreeAbelianVariety
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.SquarefreeMapMinpolyInt
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

/- English proof (translation)
Establish `key : ∀ z : B, ∃ ε : B, σ ε = σ z ∧ ∀ a, j a * ε = σ (j a) • ε`. Introduce `z`. Establish `hz : z ∈ (⨆ τ : OE →+* C, ⨅ a : OE, Module.End.eigenspace (((Algebra.lmul C B).toRingHom.comp j) a) (τ a))`. Rewrite using `[hsup]`. Discharge the goal by the elementary cases of `trivial`.

Proceed by induction on `hz using Submodule.iSup_induction' with`. Consider the case `mem τ x hx`. Establish `hx' : ∀ a, j a * x = τ a • x` using `fun a => by`. Use `(Submodule.mem_iInf _).1 hx a` as an intermediate fact. Rewrite `this` using `[Module.End.mem_eigenspace_iff]`.

Conclude with `this`. Distinguish the cases in `h0 : σ x = 0`. Conclude with `⟨0, by simp [h0], by simp⟩`. Use `⟨x, rfl, fun a => ?_⟩` and prove the remaining obligations. Establish `h1` using `congrArg σ (hx' a)`.

Rewrite `h1` using `[map_mul, map_smul, smul_eq_mul]`. Rewrite using `[hx' a, mul_right_cancel₀ h0 h1]`. Consider the case `zero => exact ⟨0, rfl, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨a, ha, ha'⟩` from `hx`.

Take `⟨b, hb, hb'⟩` from `hy`. Conclude with `⟨a + b, by simp [ha, hb], fun c => by rw [mul_add, smul_add, ha', hb']⟩`. Take `⟨ε, h1, h2⟩` from `key 1`. Use `⟨ε, by simpa using h1, fun z => ?_⟩` and prove the remaining obligations. Establish `hz : z ∈ Submodule.span C (Set.range j)` using `by rw [hj]; trivial`.

Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem x hx => obtain ⟨a, rfl⟩ := hx`. Conclude with `h2 a`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [add_mul, hx, hy, map_add, add_smul]`.

Consider the case `smul c x _ hx => rw [smul_mul_assoc, hx, map_smul, smul_eq_mul, mul_smul]`.
-/
private theorem exists_eps {C B OE : Type} [Field C] [CommRing B] [Algebra C B] [CommRing OE]
    (σ : B →ₐ[C] C) (j : OE →+* B) (hj : Submodule.span C (Set.range j) = ⊤)
    (hsup : (⨆ τ : OE →+* C, ⨅ a : OE,
      Module.End.eigenspace (((Algebra.lmul C B).toRingHom.comp j) a) (τ a)) = ⊤) :
    ∃ ε : B, σ ε = 1 ∧ ∀ z, z * ε = σ z • ε := by
  have key : ∀ z : B, ∃ ε : B, σ ε = σ z ∧ ∀ a, j a * ε = σ (j a) • ε := by
    intro z
    have hz : z ∈ (⨆ τ : OE →+* C, ⨅ a : OE,
      Module.End.eigenspace (((Algebra.lmul C B).toRingHom.comp j) a) (τ a)) := by
      rw [hsup]; trivial
    induction hz using Submodule.iSup_induction' with
    | mem τ x hx =>
      have hx' : ∀ a, j a * x = τ a • x := fun a => by
        have := (Submodule.mem_iInf _).1 hx a
        rw [Module.End.mem_eigenspace_iff] at this
        exact this
      by_cases h0 : σ x = 0
      · exact ⟨0, by simp [h0], by simp⟩
      · refine ⟨x, rfl, fun a => ?_⟩
        have h1 := congrArg σ (hx' a)
        rw [map_mul, map_smul, smul_eq_mul] at h1
        rw [hx' a, mul_right_cancel₀ h0 h1]
    | zero => exact ⟨0, rfl, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, ha'⟩ := hx
      obtain ⟨b, hb, hb'⟩ := hy
      exact ⟨a + b, by simp [ha, hb], fun c => by rw [mul_add, smul_add, ha', hb']⟩
  obtain ⟨ε, h1, h2⟩ := key 1
  refine ⟨ε, by simpa using h1, fun z => ?_⟩
  have hz : z ∈ Submodule.span C (Set.range j) := by rw [hj]; trivial
  induction hz using Submodule.span_induction with
  | mem x hx => obtain ⟨a, rfl⟩ := hx; exact h2 a
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul, hx, hy, map_add, add_smul]
  | smul c x _ hx => rw [smul_mul_assoc, hx, map_smul, smul_eq_mul, mul_smul]

/- English proof (translation)
Take `⟨ε, h1, h2⟩` from `exists_eps σ j hj hsup`. Establish `hεe : ε * e = ε` using `by rw [mul_comm, h2, he, one_smul]`. Take `⟨t, ht⟩` from `(Submodule.mem_span_range_iff_exists_fun C).1 (hb ε)`. Rewrite `ht` using `[hεe]`. Establish `hmul : ∀ (z : B) (x : κ → C), ρ z *ᵥ (ρ ε *ᵥ x) = σ z • (ρ ε *ᵥ x)` using `fun z x => by`.

Rewrite using `[Matrix.mulVec_mulVec, ← map_mul, h2, map_smul, Matrix.smul_mulVec]`. Establish `hmul' : ∀ (z : B) (x : κ → C), ρ ε *ᵥ (ρ z *ᵥ x) = σ z • (ρ ε *ᵥ x)` using `fun z x => by`. Rewrite using `[Matrix.mulVec_mulVec, ← map_mul, mul_comm, h2, map_smul, Matrix.smul_mulVec]`. Establish `hli' : LinearIndependent C (fun l : H => ρ ε *ᵥ y l)`. Rewrite `hli`, the goal using `[Fintype.linearIndependent_iff]`.

Introduce `c hc l`. Establish `h3` using `hli (fun q => c q.2 * t q.1) (by`. Rewrite using `[← hc, Fintype.sum_prod_type_right]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[← ht, map_sum, Matrix.sum_mulVec, Finset.smul_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, Matrix.smul_mulVec, mul_smul])`. Assume the negation of the conclusion as `hl`. Establish `h4 : ∀ i, t i = 0` using `fun i => (mul_eq_zero.1 (h3 (i, l))).resolve_left hl`. Establish `h5 : ε = 0` using `by rw [← ht]; simp [h4]`.

Rewrite `h1` using `[h5, map_zero]`. Conclude with `zero_ne_one h1`. Establish `hE : (⨅ a : OE, Module.End.eigenspace (Matrix.toLin' (ρ (j a))) (σ (j a))) = Submodule.span C (Set.range fun l : H => ρ ε *ᵥ y l)`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `x hx`.

Establish `hx' : ∀ a, ρ (j a) *ᵥ x = σ (j a) • x` using `fun a => by`. Use `(Submodule.mem_iInf _).1 hx a` as an intermediate fact. Rewrite `this` using `[Module.End.mem_eigenspace_iff]`. Simplify using `using this`. Establish `hx2 : ∀ z, ρ z *ᵥ x = σ z • x` using `fun z => by`.

Establish `hz : z ∈ Submodule.span C (Set.range j)` using `by rw [hj]; trivial`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem x hx => obtain ⟨a, rfl⟩ := hx`. Conclude with `hx' a`. Consider the case `zero => simp`.

Consider the case `add x y _ _ hx hy => rw [map_add, Matrix.add_mulVec, hx, hy, map_add, add_smul]`. Consider the case `smul c x _ hx => rw [map_smul, Matrix.smul_mulVec, hx, map_smul, smul_eq_mul, mul_smul]`. Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun C).1 (hsp x)`. Establish `: x = ρ ε *ᵥ (ρ e *ᵥ x)` using `by rw [hx2 e, he, one_smul, hx2, h1, one_smul]`. Rewrite using `[this, ← hc, Matrix.mulVec_sum]`.

Use `Submodule.sum_mem _ fun q _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_smul, hmul']`. Conclude with `Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨q.2, rfl⟩))`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨l, rfl⟩`.

Use `(Submodule.mem_iInf _).2 fun a => ?_` and prove the remaining obligations. Rewrite using `[Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]`. Conclude with `hmul _ _`. Rewrite using `[hE, finrank_span_eq_card hli']`.
-/
private theorem core {C B OE κ I H : Type} [Field C] [CommRing B] [Algebra C B] [CommRing OE]
    [Fintype κ] [DecidableEq κ] [Fintype I] [Fintype H]
    (σ : B →ₐ[C] C) (j : OE →+* B) (hj : Submodule.span C (Set.range j) = ⊤)
    (hsup : (⨆ τ : OE →+* C, ⨅ a : OE,
      Module.End.eigenspace (((Algebra.lmul C B).toRingHom.comp j) a) (τ a)) = ⊤)
    (ρ : B →ₐ[C] Matrix κ κ C) (e : B) (he : σ e = 1) (b : I → B)
    (hb : ∀ z, z * e ∈ Submodule.span C (Set.range b)) (y : H → κ → C)
    (hli : LinearIndependent C (fun q : I × H => ρ (b q.1) *ᵥ y q.2))
    (hsp : ∀ x, ρ e *ᵥ x ∈ Submodule.span C (Set.range fun q : I × H => ρ (b q.1) *ᵥ y q.2)) :
    Module.finrank C ↥(⨅ a : OE, Module.End.eigenspace (Matrix.toLin' (ρ (j a))) (σ (j a))) =
      Fintype.card H := by
  obtain ⟨ε, h1, h2⟩ := exists_eps σ j hj hsup
  have hεe : ε * e = ε := by rw [mul_comm, h2, he, one_smul]
  obtain ⟨t, ht⟩ := (Submodule.mem_span_range_iff_exists_fun C).1 (hb ε)
  rw [hεe] at ht
  have hmul : ∀ (z : B) (x : κ → C), ρ z *ᵥ (ρ ε *ᵥ x) = σ z • (ρ ε *ᵥ x) := fun z x => by
    rw [Matrix.mulVec_mulVec, ← map_mul, h2, map_smul, Matrix.smul_mulVec]
  have hmul' : ∀ (z : B) (x : κ → C), ρ ε *ᵥ (ρ z *ᵥ x) = σ z • (ρ ε *ᵥ x) := fun z x => by
    rw [Matrix.mulVec_mulVec, ← map_mul, mul_comm, h2, map_smul, Matrix.smul_mulVec]
  have hli' : LinearIndependent C (fun l : H => ρ ε *ᵥ y l) := by
    rw [Fintype.linearIndependent_iff] at hli ⊢
    intro c hc l
    have h3 := hli (fun q => c q.2 * t q.1) (by
      rw [← hc, Fintype.sum_prod_type_right]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [← ht, map_sum, Matrix.sum_mulVec, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, Matrix.smul_mulVec, mul_smul])
    by_contra hl
    have h4 : ∀ i, t i = 0 := fun i => (mul_eq_zero.1 (h3 (i, l))).resolve_left hl
    have h5 : ε = 0 := by rw [← ht]; simp [h4]
    rw [h5, map_zero] at h1
    exact zero_ne_one h1
  have hE : (⨅ a : OE, Module.End.eigenspace (Matrix.toLin' (ρ (j a))) (σ (j a))) =
      Submodule.span C (Set.range fun l : H => ρ ε *ᵥ y l) := by
    apply le_antisymm
    · intro x hx
      have hx' : ∀ a, ρ (j a) *ᵥ x = σ (j a) • x := fun a => by
        have := (Submodule.mem_iInf _).1 hx a
        rw [Module.End.mem_eigenspace_iff] at this
        simpa using this
      have hx2 : ∀ z, ρ z *ᵥ x = σ z • x := fun z => by
        have hz : z ∈ Submodule.span C (Set.range j) := by rw [hj]; trivial
        induction hz using Submodule.span_induction with
        | mem x hx => obtain ⟨a, rfl⟩ := hx; exact hx' a
        | zero => simp
        | add x y _ _ hx hy => rw [map_add, Matrix.add_mulVec, hx, hy, map_add, add_smul]
        | smul c x _ hx => rw [map_smul, Matrix.smul_mulVec, hx, map_smul, smul_eq_mul, mul_smul]
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun C).1 (hsp x)
      have : x = ρ ε *ᵥ (ρ e *ᵥ x) := by rw [hx2 e, he, one_smul, hx2, h1, one_smul]
      rw [this, ← hc, Matrix.mulVec_sum]
      refine Submodule.sum_mem _ fun q _ => ?_
      rw [Matrix.mulVec_smul, hmul']
      exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨q.2, rfl⟩))
    · rw [Submodule.span_le]
      rintro _ ⟨l, rfl⟩
      refine (Submodule.mem_iInf _).2 fun a => ?_
      rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
      exact hmul _ _
  rw [hE, finrank_span_eq_card hli']

/- English proof (translation)
Introduce `p _ C _ _ _ v O _ _ _ _ _ _ OE _ _ _ _ _ w b κ _ _ ρ h y hli hsp τ hτ`. Use `letI : Algebra ℤ_[p] C := ((algebraMap O C).comp (algebraMap ℤ_[p] O)).toAlgebra`. Use `haveI : IsScalarTower ℤ_[p] O C := IsScalarTower.of_algebraMap_eq fun _ => rfl`. Establish `hinj : Function.Injective (algebraMap ℤ_[p] C)`. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce `x hx`. Assume the negation of the conclusion as `h0`. Rewrite `hx` using `[PadicInt.unitCoeff_spec h0, map_mul, map_pow, map_natCast]`. Break down `mul_eq_zero.1 hx with h1 | h1` into its components or cases. Conclude with `((PadicInt.unitCoeff h0).isUnit.map (algebraMap ℤ_[p] C)).ne_zero h1`.

Conclude with `(Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) (pow_eq_zero_iff'.1 h1).1`. Use `haveI : FaithfulSMul ℤ_[p] C := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj`. Set `σ : (C ⊗[ℤ_[p]] (ℤ_[p] ⊗[ℤ] OE)) →ₐ[C] C` to `Algebra.TensorProduct.lift (AlgHom.id C C) ((IsScalarTower.toAlgHom ℤ_[p] O C).comp (tauExt τ)) (fun _ _ => Commute.all _ _)`. Set `ρB : (C ⊗[ℤ_[p]] (ℤ_[p] ⊗[ℤ] OE)) →ₐ[C] Matrix κ κ C` to `Algebra.TensorProduct.lift (Algebra.ofId C (Matrix κ κ C)) ((Algebra.ofId ℤ_[p] C).mapMatrix.comp ρ) (fun _ _ => Algebra.commutes _ _)`. Set `j : OE →+* (C ⊗[ℤ_[p]] (ℤ_[p] ⊗[ℤ] OE))` to `(Algebra.TensorProduct.includeRight (R := ℤ_[p]) (A := C) (B := ℤ_[p] ⊗[ℤ] OE)).toRingHom.comp (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℤ_[p]) (B := OE)).toRingHom`.

Establish `hj : ∀ a, j a = 1 ⊗ₜ (1 ⊗ₜ a)` using `fun a => rfl`. Establish `hσ : ∀ a, σ (1 ⊗ₜ a) = algebraMap O C (tauExt τ a)` using `fun a => by simp [σ]`. Establish `hρ : ∀ a, ρB (1 ⊗ₜ a) = (ρ a).map (algebraMap ℤ_[p] C)` using `fun a => by`. Use `(Algebra.TensorProduct.lift_tmul _ _ _ _ _).trans ?_` and prove the remaining obligations. Rewrite using `[map_one, _root_.one_mul]`.

Both sides reduce to the same expression. Establish `hmv : ∀ a x, ρB (1 ⊗ₜ a) *ᵥ (algebraMap ℤ_[p] C ∘ x) = algebraMap ℤ_[p] C ∘ (ρ a *ᵥ x)`. Introduce `a x`. Use function extensionality and compare the values at `i`. Rewrite using `[hρ]`.

Conclude with `(RingHom.map_mulVec _ _ _ _).symm`. Establish `hs : ∀ (c : C) (r : ℤ_[p]) (a : ℤ_[p] ⊗[ℤ] OE), (c ⊗ₜ[ℤ_[p]] (r • a)) = (r • c) • ((1 : C) ⊗ₜ[ℤ_[p]] a)` using `fun c r a => by`. Rewrite using `[← TensorProduct.smul_tmul, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]`. Establish `H` using `core (I := Fin w.n) (H := Fin h) σ j ?_ ((GlobalTheory.order_rep_diagonalisable C OE).2 _ _).2 ρB (1 ⊗ₜ w.e) (by rw [hσ, show tauExt τ w.e = 1 from hτ, map_one]) (fun i => 1 ⊗ₜ (b i : ℤ_[p] ⊗[ℤ] OE)) ?_ (fun l => algebraMap ℤ_[p] C ∘ y l) ?_ ?_`. Rewrite `H` using `[Fintype.card_fin]`.

Establish `h1 : ∀ a, ρB (j a) = ((ρ (1 ⊗ₜ[ℤ] a)).map (algebraMap ℤ_[p] O)).map (algebraMap O C)`. Introduce `a`. Rewrite using `[hj, hρ, Matrix.map_map]`. Both sides reduce to the same expression. Establish `h2 : ∀ a, σ (j a) = ((algebraMap O C).comp τ) a`.

Introduce `a`. Rewrite using `[hj, hσ]`. Simplify using `[tauExt]`. Establish `h3 : (⨅ a : OE, Module.End.eigenspace (Matrix.toLin' (ρB (j a))) (σ (j a))) = ⨅ a : OE, Module.End.eigenspace (Matrix.toLin' (((ρ (1 ⊗ₜ[ℤ] a)).map (algebraMap ℤ_[p] O)).map (algebraMap O C))) (((algebraMap O C).comp τ) a)` using `iInf_congr fun a => by rw [h1, h2]`. Rewrite `H` using `[h3]`.

Conclude with `H`. Rewrite using `[eq_top_iff]`. Introduce and unpack `z -`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => exact Submodule.zero_mem _`.

Consider the case `add x y hx hy => exact Submodule.add_mem _ hx hy`. Consider the case `tmul c a`. Proceed by induction on `a using TensorProduct.induction_on with`. Consider the case `zero => rw [TensorProduct.tmul_zero]`. Conclude with `Submodule.zero_mem _`.

Consider the case `add x y hx hy => rw [TensorProduct.tmul_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `tmul r a`. Establish `: r ⊗ₜ[ℤ] a = r • ((1 : ℤ_[p]) ⊗ₜ[ℤ] a)`. Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]`.

Rewrite using `[this, hs]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)`. Introduce `z`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => rw [zero_mul]`.

Conclude with `Submodule.zero_mem _`. Consider the case `add x y hx hy => rw [add_mul]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `tmul c a`. Establish `h1` using `congrArg Subtype.val (b.sum_repr ⟨w.e * a, a, rfl⟩)`.

Simplify using `only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul] at h1`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, mul_comm a, ← h1, TensorProduct.tmul_sum]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hs]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`.

Simplify using `only [hmv]`. Conclude with `linearIndependent_algebraMap_comp_iff.2 hli`. Introduce `x`. Simplify using `only [hmv]`. Rewrite using `[← Finset.univ_sum_single x, Matrix.mulVec_sum]`.

Use `Submodule.sum_mem _ fun k _ => ?_` and prove the remaining obligations. Establish `h1 : (Pi.single k (x k) : κ → C) = x k • (algebraMap ℤ_[p] C ∘ (Pi.single k 1 : κ → ℤ_[p]))`. Use function extensionality and compare the values at `i`. Distinguish the cases in `hi : i = k`. Substitute `hi` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[hi]`. Rewrite using `[h1, Matrix.mulVec_smul, hmv]`. Use `Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Establish `h2 : ρ w.e *ᵥ (Pi.single k 1 : κ → ℤ_[p]) ∈ LinearMap.range (Matrix.mulVecLin (ρ w.e))` using `⟨_, rfl⟩`.

Rewrite `h2` using `[← hsp]`. Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun _).1 h2`. Use `(Submodule.mem_span_range_iff_exists_fun _).2 ⟨fun q => algebraMap ℤ_[p] C (c q), ?_⟩` and prove the remaining obligations. Rewrite using `[← hc]`. Use function extensionality and compare the values at `i`.

Simplify using `only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, map_sum, map_mul]`.
-/
theorem eigDim_eq_of_basis : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] (w : PlaceU p OE) (b : Module.Basis (Fin w.n) ℤ_[p] (LinearMap.range (LinearMap.mulLeft ℤ_[p] w.e))) (κ : Type) [Fintype κ] [DecidableEq κ] (ρ : (ℤ_[p] ⊗[ℤ] OE) →ₐ[ℤ_[p]] Matrix κ κ ℤ_[p]) (h : ℕ) (y : Fin h → κ → ℤ_[p]), LinearIndependent ℤ_[p] (fun q : Fin w.n × Fin h => ρ (b q.1 : ℤ_[p] ⊗[ℤ] OE) *ᵥ y q.2) → Submodule.span ℤ_[p] (Set.range fun q : Fin w.n × Fin h => ρ (b q.1 : ℤ_[p] ⊗[ℤ] OE) *ᵥ y q.2) = LinearMap.range (Matrix.mulVecLin (ρ w.e)) → ∀ τ ∈ Emb (O := O) w.e, eigDim C (fun a : OE => (ρ (1 ⊗ₜ[ℤ] a)).map (algebraMap ℤ_[p] O)) ((algebraMap O C).comp τ) = h := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ OE _ _ _ _ _ w b κ _ _ ρ h y hli hsp τ hτ
  letI : Algebra ℤ_[p] C := ((algebraMap O C).comp (algebraMap ℤ_[p] O)).toAlgebra
  haveI : IsScalarTower ℤ_[p] O C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hinj : Function.Injective (algebraMap ℤ_[p] C) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra h0
    rw [PadicInt.unitCoeff_spec h0, map_mul, map_pow, map_natCast] at hx
    rcases mul_eq_zero.1 hx with h1 | h1
    · exact ((PadicInt.unitCoeff h0).isUnit.map (algebraMap ℤ_[p] C)).ne_zero h1
    · exact (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) (pow_eq_zero_iff'.1 h1).1
  haveI : FaithfulSMul ℤ_[p] C := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  let σ : (C ⊗[ℤ_[p]] (ℤ_[p] ⊗[ℤ] OE)) →ₐ[C] C := Algebra.TensorProduct.lift (AlgHom.id C C)
    ((IsScalarTower.toAlgHom ℤ_[p] O C).comp (tauExt τ)) (fun _ _ => Commute.all _ _)
  let ρB : (C ⊗[ℤ_[p]] (ℤ_[p] ⊗[ℤ] OE)) →ₐ[C] Matrix κ κ C :=
    Algebra.TensorProduct.lift (Algebra.ofId C (Matrix κ κ C))
    ((Algebra.ofId ℤ_[p] C).mapMatrix.comp ρ) (fun _ _ => Algebra.commutes _ _)
  let j : OE →+* (C ⊗[ℤ_[p]] (ℤ_[p] ⊗[ℤ] OE)) :=
    (Algebra.TensorProduct.includeRight (R := ℤ_[p]) (A := C) (B := ℤ_[p] ⊗[ℤ] OE)).toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℤ_[p]) (B := OE)).toRingHom
  have hj : ∀ a, j a = 1 ⊗ₜ (1 ⊗ₜ a) := fun a => rfl
  have hσ : ∀ a, σ (1 ⊗ₜ a) = algebraMap O C (tauExt τ a) := fun a => by simp [σ]
  have hρ : ∀ a, ρB (1 ⊗ₜ a) = (ρ a).map (algebraMap ℤ_[p] C) := fun a => by
    refine (Algebra.TensorProduct.lift_tmul _ _ _ _ _).trans ?_
    rw [map_one, _root_.one_mul]
    rfl
  have hmv : ∀ a x, ρB (1 ⊗ₜ a) *ᵥ (algebraMap ℤ_[p] C ∘ x) = algebraMap ℤ_[p] C ∘ (ρ a *ᵥ x) := by
    intro a x
    funext i
    rw [hρ]
    exact (RingHom.map_mulVec _ _ _ _).symm
  have hs : ∀ (c : C) (r : ℤ_[p]) (a : ℤ_[p] ⊗[ℤ] OE),
      (c ⊗ₜ[ℤ_[p]] (r • a)) = (r • c) • ((1 : C) ⊗ₜ[ℤ_[p]] a) := fun c r a => by
    rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
  have H := core (I := Fin w.n) (H := Fin h) σ j ?_ ((GlobalTheory.order_rep_diagonalisable C OE).2 _ _).2 ρB (1 ⊗ₜ w.e)
    (by rw [hσ, show tauExt τ w.e = 1 from hτ, map_one])
    (fun i => 1 ⊗ₜ (b i : ℤ_[p] ⊗[ℤ] OE)) ?_ (fun l => algebraMap ℤ_[p] C ∘ y l) ?_ ?_
  · rw [Fintype.card_fin] at H
    have h1 : ∀ a, ρB (j a) = ((ρ (1 ⊗ₜ[ℤ] a)).map (algebraMap ℤ_[p] O)).map (algebraMap O C) := by
      intro a
      rw [hj, hρ, Matrix.map_map]
      rfl
    have h2 : ∀ a, σ (j a) = ((algebraMap O C).comp τ) a := by
      intro a
      rw [hj, hσ]
      simp [tauExt]
    have h3 : (⨅ a : OE, Module.End.eigenspace (Matrix.toLin' (ρB (j a))) (σ (j a))) = ⨅ a : OE,
        Module.End.eigenspace (Matrix.toLin' (((ρ (1 ⊗ₜ[ℤ] a)).map (algebraMap ℤ_[p] O)).map (algebraMap O C)))
          (((algebraMap O C).comp τ) a) := iInf_congr fun a => by rw [h1, h2]
    rw [h3] at H
    exact H
  · rw [eq_top_iff]
    rintro z -
    induction z using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | add x y hx hy => exact Submodule.add_mem _ hx hy
    | tmul c a =>
      induction a using TensorProduct.induction_on with
      | zero => rw [TensorProduct.tmul_zero]; exact Submodule.zero_mem _
      | add x y hx hy => rw [TensorProduct.tmul_add]; exact Submodule.add_mem _ hx hy
      | tmul r a =>
        have : r ⊗ₜ[ℤ] a = r • ((1 : ℤ_[p]) ⊗ₜ[ℤ] a) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
        rw [this, hs]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  · intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [zero_mul]; exact Submodule.zero_mem _
    | add x y hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
    | tmul c a =>
      have h1 := congrArg Subtype.val (b.sum_repr ⟨w.e * a, a, rfl⟩)
      simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul] at h1
      rw [Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, mul_comm a, ← h1, TensorProduct.tmul_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [hs]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · simp only [hmv]
    exact linearIndependent_algebraMap_comp_iff.2 hli
  · intro x
    simp only [hmv]
    rw [← Finset.univ_sum_single x, Matrix.mulVec_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    have h1 : (Pi.single k (x k) : κ → C) = x k • (algebraMap ℤ_[p] C ∘ (Pi.single k 1 : κ → ℤ_[p])) := by
      funext i
      by_cases hi : i = k
      · subst hi; simp
      · simp [hi]
    rw [h1, Matrix.mulVec_smul, hmv]
    refine Submodule.smul_mem _ _ ?_
    have h2 : ρ w.e *ᵥ (Pi.single k 1 : κ → ℤ_[p]) ∈ LinearMap.range (Matrix.mulVecLin (ρ w.e)) := ⟨_, rfl⟩
    rw [← hsp] at h2
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 h2
    refine (Submodule.mem_span_range_iff_exists_fun _).2 ⟨fun q => algebraMap ℤ_[p] C (c q), ?_⟩
    rw [← hc]
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, map_sum, map_mul]

end GlobalTheory.ChF
