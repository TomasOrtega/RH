import Mathlib

noncomputable section
open Matrix Module

namespace GlobalTheory.StableLattice

/- English proof (translation)
Set `f : O →+* K` to `algebraMap O K`. Establish `h' : ∀ g i j, ∃ x : O, f x = ((φ g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j` using `fun g i j => RingHom.mem_range.1 (h g i j)`. Use `choose c hc using h'`. Set `M : Γ → Matrix (Fin n) (Fin n) O` to `fun g => Matrix.of fun i j => c g i j`. Establish `hmi : Function.Injective (f.mapMatrix : Matrix (Fin n) (Fin n) O →+* Matrix (Fin n) (Fin n) K)` using `fun A B hAB => Matrix.ext fun i j => hinj (by simpa using congrFun (congrFun hAB i) j)`.

Establish `hM : ∀ g, f.mapMatrix (M g) = ((φ g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)` using `fun g => Matrix.ext fun i j => hc g i j`. Set `ρ : Γ →* GL (Fin n) O` to `{ toFun := fun g => ⟨M g, M g⁻¹, hmi (by rw [map_mul, hM, hM, map_one, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]), hmi (by rw [map_mul, hM, hM, map_one, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one])⟩ map_one' := Units.ext (hmi (by …`. Rewrite using `[map_mul, hM, hM, hM, map_mul, Units.val_mul])) }`. Conclude with `⟨ρ, fun g => Units.ext (hM g)⟩`.
-/
theorem lift_of_integral {O K : Type} [CommRing O] [Field K] [Algebra O K]
    (hinj : Function.Injective (algebraMap O K)) {Γ : Type} [Group Γ] {n : ℕ}
    (φ : Γ →* GL (Fin n) K)
    (h : ∀ g i j, ((φ g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j ∈ (algebraMap O K).range) :
    ∃ r : Γ →* GL (Fin n) O, ∀ g, Matrix.GeneralLinearGroup.map (algebraMap O K) (r g) = φ g := by
  classical
  let f : O →+* K := algebraMap O K
  have h' : ∀ g i j, ∃ x : O, f x = ((φ g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j :=
    fun g i j => RingHom.mem_range.1 (h g i j)
  choose c hc using h'
  let M : Γ → Matrix (Fin n) (Fin n) O := fun g => Matrix.of fun i j => c g i j
  have hmi : Function.Injective (f.mapMatrix : Matrix (Fin n) (Fin n) O →+* Matrix (Fin n) (Fin n) K) :=
    fun A B hAB => Matrix.ext fun i j => hinj (by simpa using congrFun (congrFun hAB i) j)
  have hM : ∀ g, f.mapMatrix (M g) = ((φ g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    fun g => Matrix.ext fun i j => hc g i j
  let ρ : Γ →* GL (Fin n) O :=
    { toFun := fun g => ⟨M g, M g⁻¹,
        hmi (by rw [map_mul, hM, hM, map_one, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]),
        hmi (by rw [map_mul, hM, hM, map_one, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one])⟩
      map_one' := Units.ext (hmi (by rw [hM, map_one, Units.val_one, Units.val_one, map_one]))
      map_mul' := fun g h => Units.ext (hmi (by
        show f.mapMatrix (M (g * h)) = f.mapMatrix (M g * M h)
        rw [map_mul, hM, hM, hM, map_mul, Units.val_mul])) }
  exact ⟨ρ, fun g => Units.ext (hM g)⟩

/- English proof (translation)
Set `K` to `FractionRing O`. Set `S : Γ → Matrix (Fin n) (Fin n) K` to `fun g => ((σ g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)`. Set `gen : T × Fin n → (Fin n → K)` to `fun p => S p.1 *ᵥ Pi.single p.2 1`. Set `M : Submodule O (Fin n → K)` to `Submodule.span O (Set.range gen)`. Establish `hA : ∀ t (ht : t ∈ T), ∀ w : Fin n → K, (∀ k, w k ∈ (algebraMap O K).range) → S t *ᵥ w ∈ M`.

Introduce `t ht w hw`. Use `choose u hu using fun k => RingHom.mem_range.1 (hw k)`. Establish `: S t *ᵥ w = ∑ k, u k • gen (⟨t, ht⟩, k)`. Use extensionality with `a`. Simplify using `only [gen, Matrix.mulVec_single_one]`.

Simplify using `only [Finset.sum_apply, Pi.smul_apply, Matrix.transpose_apply, Matrix.col_apply, Algebra.smul_def, Matrix.mulVec, dotProduct, ← hu]`. Conclude with `Finset.sum_congr rfl fun k _ => mul_comm _ _`. Rewrite using `[this]`. Conclude with `Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)`. Establish `he : ∀ i, (Pi.single i 1 : Fin n → K) ∈ M`.

Introduce `i`. Take `⟨t, ht, hU⟩` from `hT 1`. Establish `h1 : S t * S (t⁻¹ * 1) = 1`. Simplify using `only [S]`. Rewrite using `[← Units.val_mul, ← map_mul, mul_one, mul_inv_cancel, map_one, Units.val_one]`.

Establish `: (Pi.single i 1 : Fin n → K) = S t *ᵥ (S (t⁻¹ * 1) *ᵥ Pi.single i 1)`. Rewrite using `[Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]`. Rewrite using `[this]`. Use `hA t ht _ fun k => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_single_one]`.

Conclude with `hU k i`. Establish `hstab : ∀ g, ∀ x ∈ M, S g *ᵥ x ∈ M`. Introduce `g`. Set `A : (Fin n → K) →ₗ[O] (Fin n → K)` to `(Matrix.toLin' (S g)).restrictScalars O`. Establish `hle : M.map A ≤ M`.

Rewrite using `[Submodule.map_span_le]`. Introduce and unpack `_ ⟨⟨⟨t, ht⟩, i⟩, rfl⟩`. Take `⟨t', ht', hU⟩` from `hT (g * t)`. Establish `h1 : S g * S t = S t' * S (t'⁻¹ * (g * t))`. Simplify using `only [S]`.

Rewrite using `[← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, mul_inv_cancel_left]`. Use `show S g *ᵥ (S t *ᵥ Pi.single i 1) ∈ M`. Rewrite using `[Matrix.mulVec_mulVec, h1, ← Matrix.mulVec_mulVec]`. Use `hA t' ht' _ fun k => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_single_one]`.

Conclude with `hU k i`. Introduce `x hx`. Conclude with `hle ⟨x, hx, rfl⟩`. Use `haveI : Module.Finite O M := Module.Finite.span_of_finite (R := O) (Set.finite_range gen)`. Use `haveI : Module.Free O M := Module.free_of_finite_type_torsion_free'`.

Set `ι` to `Module.Free.ChooseBasisIndex O M`. Set `b : Basis ι O M` to `Module.Free.chooseBasis O M`. Set `v : ι → (Fin n → K)` to `fun i => (b i : Fin n → K)`. Establish `hcoord : ∀ x (hx : x ∈ M), x = ∑ i, algebraMap O K (b.repr ⟨x, hx⟩ i) • v i`. Introduce `x hx`.

Use `congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)` as an intermediate fact. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul_of_tower] at this`. Simplify using `only [algebraMap_smul, v]`. Conclude with `this.symm`. Establish `hli : LinearIndependent K v` using `(LinearIndependent.iff_fractionRing O K).1 (b.linearIndependent.map' M.subtype M.ker_subtype)`.

Establish `hsp : ⊤ ≤ Submodule.span K (Set.range v)`. Rewrite using `[← (Pi.basisFun K (Fin n)).span_eq, Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Rewrite using `[Pi.basisFun_apply, hcoord _ (he i)]`. Conclude with `Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)`.

Set `bK : Basis ι K (Fin n → K)` to `Basis.mk hli hsp`. Establish `hrep : ∀ x (hx : x ∈ M) k, bK.repr x k = algebraMap O K (b.repr ⟨x, hx⟩ k)`. Introduce `x hx k`. Establish `h1 : x = bK.equivFun.symm (fun i => algebraMap O K (b.repr ⟨x, hx⟩ i))`. Rewrite using `[Basis.equivFun_symm_apply]`.

Simplify using `only [bK, Basis.coe_mk]`. Conclude with `hcoord x hx`. Rewrite using `[← Basis.equivFun_apply]`. Use `conv_lhs => rw [h1]`. Rewrite using `[LinearEquiv.apply_symm_apply]`.

Establish `hcard : Fintype.card ι = n` using `(Module.finrank_eq_card_basis bK).symm.trans (Module.finrank_fin_fun K)`. Set `e : ι ≃ Fin n` to `Fintype.equivFinOfCardEq hcard`. Set `bK' : Basis (Fin n) K (Fin n → K)` to `bK.reindex e`. Set `E` to `Pi.basisFun K (Fin n)`. Set `Pu : GL (Fin n) K` to `⟨E.toMatrix bK', bK'.toMatrix E, E.toMatrix_mul_toMatrix_flip bK', bK'.toMatrix_mul_toMatrix_flip E⟩`.

Use `⟨Pu, fun g i j => ?_⟩` and prove the remaining obligations. Establish `hmat : ((Pu⁻¹ * σ g * Pu : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = LinearMap.toMatrix bK' bK' (Matrix.toLin' (S g))`. Rewrite using `[← basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix (b := bK') (c := bK') (b' := E) (c' := E), LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']`. Simplify using `only [Units.val_mul]`. Both sides reduce to the same expression.

Establish `hmem : S g *ᵥ bK' j ∈ M`. Use `hstab g _ ?_` and prove the remaining obligations. Simplify using `only [bK', Basis.reindex_apply, bK, Basis.coe_mk, v]`. Conclude with `(b _).2`. Rewrite using `[hmat, LinearMap.toMatrix_apply, Matrix.toLin'_apply, Basis.repr_reindex_apply, hrep _ hmem]`.

Conclude with `⟨_, rfl⟩`.
-/
theorem exists_conj_integral {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
    {Γ : Type} [Group Γ] {n : ℕ} (σ : Γ →* GL (Fin n) (FractionRing O)) (T : Finset Γ)
    (hT : ∀ x : Γ, ∃ t ∈ T, ∀ i j, ((σ (t⁻¹ * x) : GL (Fin n) (FractionRing O)) :
      Matrix (Fin n) (Fin n) (FractionRing O)) i j ∈ (algebraMap O (FractionRing O)).range) :
    ∃ P : GL (Fin n) (FractionRing O), ∀ g i j,
      ((P⁻¹ * σ g * P : GL (Fin n) (FractionRing O)) : Matrix (Fin n) (Fin n) (FractionRing O)) i j
        ∈ (algebraMap O (FractionRing O)).range := by
  classical
  let K := FractionRing O
  let S : Γ → Matrix (Fin n) (Fin n) K := fun g => ((σ g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  let gen : T × Fin n → (Fin n → K) := fun p => S p.1 *ᵥ Pi.single p.2 1
  let M : Submodule O (Fin n → K) := Submodule.span O (Set.range gen)
  have hA : ∀ t (ht : t ∈ T), ∀ w : Fin n → K, (∀ k, w k ∈ (algebraMap O K).range) → S t *ᵥ w ∈ M := by
    intro t ht w hw
    choose u hu using fun k => RingHom.mem_range.1 (hw k)
    have : S t *ᵥ w = ∑ k, u k • gen (⟨t, ht⟩, k) := by
      ext a
      simp only [gen, Matrix.mulVec_single_one]
      simp only [Finset.sum_apply, Pi.smul_apply, Matrix.transpose_apply, Matrix.col_apply, Algebra.smul_def,
        Matrix.mulVec, dotProduct, ← hu]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    rw [this]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  have he : ∀ i, (Pi.single i 1 : Fin n → K) ∈ M := by
    intro i
    obtain ⟨t, ht, hU⟩ := hT 1
    have h1 : S t * S (t⁻¹ * 1) = 1 := by
      simp only [S]
      rw [← Units.val_mul, ← map_mul, mul_one, mul_inv_cancel, map_one, Units.val_one]
    have : (Pi.single i 1 : Fin n → K) = S t *ᵥ (S (t⁻¹ * 1) *ᵥ Pi.single i 1) := by
      rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
    rw [this]
    refine hA t ht _ fun k => ?_
    rw [Matrix.mulVec_single_one]
    exact hU k i
  have hstab : ∀ g, ∀ x ∈ M, S g *ᵥ x ∈ M := by
    intro g
    let A : (Fin n → K) →ₗ[O] (Fin n → K) := (Matrix.toLin' (S g)).restrictScalars O
    have hle : M.map A ≤ M := by
      rw [Submodule.map_span_le]
      rintro _ ⟨⟨⟨t, ht⟩, i⟩, rfl⟩
      obtain ⟨t', ht', hU⟩ := hT (g * t)
      have h1 : S g * S t = S t' * S (t'⁻¹ * (g * t)) := by
        simp only [S]
        rw [← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, mul_inv_cancel_left]
      show S g *ᵥ (S t *ᵥ Pi.single i 1) ∈ M
      rw [Matrix.mulVec_mulVec, h1, ← Matrix.mulVec_mulVec]
      refine hA t' ht' _ fun k => ?_
      rw [Matrix.mulVec_single_one]
      exact hU k i
    intro x hx
    exact hle ⟨x, hx, rfl⟩
  haveI : Module.Finite O M := Module.Finite.span_of_finite (R := O) (Set.finite_range gen)
  haveI : Module.Free O M := Module.free_of_finite_type_torsion_free'
  let ι := Module.Free.ChooseBasisIndex O M
  let b : Basis ι O M := Module.Free.chooseBasis O M
  let v : ι → (Fin n → K) := fun i => (b i : Fin n → K)
  have hcoord : ∀ x (hx : x ∈ M), x = ∑ i, algebraMap O K (b.repr ⟨x, hx⟩ i) • v i := by
    intro x hx
    have := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower] at this
    simp only [algebraMap_smul, v]
    exact this.symm
  have hli : LinearIndependent K v :=
    (LinearIndependent.iff_fractionRing O K).1 (b.linearIndependent.map' M.subtype M.ker_subtype)
  have hsp : ⊤ ≤ Submodule.span K (Set.range v) := by
    rw [← (Pi.basisFun K (Fin n)).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [Pi.basisFun_apply, hcoord _ (he i)]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  let bK : Basis ι K (Fin n → K) := Basis.mk hli hsp
  have hrep : ∀ x (hx : x ∈ M) k, bK.repr x k = algebraMap O K (b.repr ⟨x, hx⟩ k) := by
    intro x hx k
    have h1 : x = bK.equivFun.symm (fun i => algebraMap O K (b.repr ⟨x, hx⟩ i)) := by
      rw [Basis.equivFun_symm_apply]
      simp only [bK, Basis.coe_mk]
      exact hcoord x hx
    rw [← Basis.equivFun_apply]
    conv_lhs => rw [h1]
    rw [LinearEquiv.apply_symm_apply]
  have hcard : Fintype.card ι = n :=
    (Module.finrank_eq_card_basis bK).symm.trans (Module.finrank_fin_fun K)
  let e : ι ≃ Fin n := Fintype.equivFinOfCardEq hcard
  let bK' : Basis (Fin n) K (Fin n → K) := bK.reindex e
  let E := Pi.basisFun K (Fin n)
  let Pu : GL (Fin n) K := ⟨E.toMatrix bK', bK'.toMatrix E, E.toMatrix_mul_toMatrix_flip bK',
    bK'.toMatrix_mul_toMatrix_flip E⟩
  refine ⟨Pu, fun g i j => ?_⟩
  have hmat : ((Pu⁻¹ * σ g * Pu : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      LinearMap.toMatrix bK' bK' (Matrix.toLin' (S g)) := by
    rw [← basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix (b := bK') (c := bK') (b' := E) (c' := E),
      LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']
    simp only [Units.val_mul]
    rfl
  have hmem : S g *ᵥ bK' j ∈ M := by
    refine hstab g _ ?_
    simp only [bK', Basis.reindex_apply, bK, Basis.coe_mk, v]
    exact (b _).2
  rw [hmat, LinearMap.toMatrix_apply, Matrix.toLin'_apply, Basis.repr_reindex_apply, hrep _ hmem]
  exact ⟨_, rfl⟩

end GlobalTheory.StableLattice
