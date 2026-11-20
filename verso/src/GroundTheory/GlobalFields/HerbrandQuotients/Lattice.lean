import Mathlib
import GroundTheory.TateCohomology.HerbrandAbstract
import GroundTheory.GlobalFields.HerbrandQuotients.Cyclic
import GroundTheory.GlobalFields.HerbrandQuotients.RationalForm

namespace GroundTheory.Global

open GroundTheory.GroupCoh
open scoped TensorProduct

/- English proof (translation)
Establish `: Module.Finite ℤ (B ⧸ S)` using `Module.Finite.of_surjective (QuotientAddGroup.mk' S).toIntLinearMap (QuotientAddGroup.mk'_surjective _)`. Apply `Module.finite_of_fg_torsion` to reduce the goal to its premises. Introduce `y`. Take `⟨x, rfl⟩` from `QuotientAddGroup.mk'_surjective S y`. Use `⟨⟨n, mem_nonZeroDivisors_of_ne_zero hn⟩, ?_⟩` and prove the remaining obligations.

Use `show n • (QuotientAddGroup.mk' S x) = 0`. Rewrite using `[← map_zsmul, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]`. Conclude with `h x`.
-/
theorem finite_quotient_of_smul_mem {B : Type*} [AddCommGroup B] [Module.Finite ℤ B]
    (S : AddSubgroup B) {n : ℤ} (hn : n ≠ 0) (h : ∀ y, n • y ∈ S) : Finite (B ⧸ S) := by
  have : Module.Finite ℤ (B ⧸ S) :=
    Module.Finite.of_surjective (QuotientAddGroup.mk' S).toIntLinearMap
      (QuotientAddGroup.mk'_surjective _)
  apply Module.finite_of_fg_torsion
  intro y
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective S y
  refine ⟨⟨n, mem_nonZeroDivisors_of_ne_zero hn⟩, ?_⟩
  show n • (QuotientAddGroup.mk' S x) = 0
  rw [← map_zsmul, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
  exact h x

variable {G M M' : Type*} [Group G] [AddCommGroup M] [AddCommGroup M']

/- English proof (translation)
The claim follows from `herbrandQuotient_eq_of_injective_of_finite (fA := cycSub ρ σ) (gA := normHom ρ) (fB := cycSub ρ' σ) (gB := normHom ρ') hφ (fun a => by rw [cycSub_apply, cycSub_apply, map_sub, hcomm]) (fun a => by rw [normHom_apply, normHom_apply, map_sum]; simp only [hcomm]) (cycSub_normHom ρ' σ …`.
-/
theorem cyclicHerbrand_eq_of_injective [Fintype G] (ρ : Representation ℤ G M)
    (ρ' : Representation ℤ G M') (σ : G) (φ : M →+ M') (hφ : Function.Injective φ)
    [Finite (M' ⧸ φ.range)] (hcomm : ∀ g x, φ (ρ g x) = ρ' g (φ x)) :
    cyclicHerbrand ρ σ = cyclicHerbrand ρ' σ :=
  herbrandQuotient_eq_of_injective_of_finite (fA := cycSub ρ σ) (gA := normHom ρ)
    (fB := cycSub ρ' σ) (gB := normHom ρ') hφ
    (fun a => by rw [cycSub_apply, cycSub_apply, map_sub, hcomm])
    (fun a => by rw [normHom_apply, normHom_apply, map_sum]; simp only [hcomm])
    (cycSub_normHom ρ' σ) (normHom_cycSub ρ' σ)

/- English proof (translation)
Set `bR` to `Algebra.TensorProduct.basis ℝ b`. Set `bR'` to `Algebra.TensorProduct.basis ℝ b'`. Set `A : G → Matrix ι ι ℤ` to `fun g => LinearMap.toMatrix b b (ρ g)`. Set `A' : G → Matrix ι ι ℤ` to `fun g => LinearMap.toMatrix b' b' (ρ' g)`. Set `P : Matrix ι ι ℝ` to `LinearMap.toMatrix bR bR' e.toLinearMap`.

Establish `hP : P.det ≠ 0`. Establish `hid : e.symm.toLinearMap ∘ₗ e.toLinearMap = LinearMap.id` using `LinearMap.ext fun x => by simp`. Establish `h1` using `congrArg (LinearMap.toMatrix bR bR) hid`. Rewrite `h1` using `[LinearMap.toMatrix_comp bR bR' bR, LinearMap.toMatrix_id]`. Establish `h2` using `congrArg Matrix.det h1`.

Rewrite `h2` using `[Matrix.det_mul, Matrix.det_one]`. Conclude with `right_ne_zero_of_mul_eq_one h2`. Establish `hPA : ∀ g, P * (A g).map (Int.cast : ℤ → ℝ) = (A' g).map (Int.cast : ℤ → ℝ) * P`. Introduce `g`. Establish `hc : e.toLinearMap ∘ₗ (ρ g).baseChange ℝ = (ρ' g).baseChange ℝ ∘ₗ e.toLinearMap` using `LinearMap.ext (he g)`.

Establish `h1` using `congrArg (LinearMap.toMatrix bR bR') hc`. Rewrite `h1` using `[LinearMap.toMatrix_comp bR bR bR', LinearMap.toMatrix_comp bR bR' bR', LinearMap.toMatrix_baseChange, LinearMap.toMatrix_baseChange, algebraMap_int_eq]`. Conclude with `h1`. Take `⟨Q, hQ, hQA⟩` from `exists_rat_intertwiner (fun g => (A g).map (Int.cast : ℤ → ℚ)) (fun g => (A' g).map (Int.cast : ℤ → ℚ)) P hP (fun g => by`. Rewrite using `[Matrix.map_map, Matrix.map_map]`.

Apply the tactic sequence `convert hPA g using 3 <;> ext x <;> simp)`. Take `⟨⟨d, hd⟩, hdQ⟩` from `IsLocalization.exist_integer_multiples (R := ℤ) (M := nonZeroDivisors ℤ) (S := ℚ) Finset.univ (fun p : ι × ι => Q p.1 p.2)`. Establish `hd0 : d ≠ 0` using `nonZeroDivisors.ne_zero hd`. Use `choose D hD using fun a b => RingHom.mem_rangeS.1 (hdQ (a, b) (Finset.mem_univ _))`. Set `Dm : Matrix ι ι ℤ` to `Matrix.of D`.

Establish `hDm : Dm.map (Int.cast : ℤ → ℚ) = (d : ℚ) • Q`. Use extensionality with `a b`. Simplify using `only [Matrix.map_apply, Matrix.smul_apply, Dm, Matrix.of_apply]`. Rewrite using `[← eq_intCast (algebraMap ℤ ℚ), hD a b, zsmul_eq_mul, smul_eq_mul]`. Establish `hdet : Dm.det ≠ 0`.

Establish `h1 : (Dm.det : ℚ) = (d : ℚ) ^ Fintype.card ι * Q.det`. Rewrite using `[Int.cast_det]`. Express the relevant statement in the definitionally equal form `(Dm.map (Int.cast : ℤ → ℚ)).det = _`. Rewrite using `[hDm, Matrix.det_smul]`. Introduce `h0`.

Rewrite `h1` using `[h0, Int.cast_zero]`. Conclude with `mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hd0)) hQ h1.symm`. Establish `hmap : ∀ X Y : Matrix ι ι ℤ, (X * Y).map (Int.cast : ℤ → ℚ) = X.map (Int.cast : ℤ → ℚ) * Y.map (Int.cast : ℤ → ℚ)` using `fun X Y => Matrix.map_mul (f := Int.castRingHom ℚ)`. Establish `hDA : ∀ g, Dm * A g = A' g * Dm`. Introduce `g`.

Apply `Matrix.map_injective (f := (Int.cast : ℤ → ℚ)) Int.cast_injective` to reduce the goal to its premises. Use `show (Dm * A g).map (Int.cast : ℤ → ℚ) = (A' g * Dm).map (Int.cast : ℤ → ℚ)`. Rewrite using `[hmap, hmap, hDm, Matrix.smul_mul, Matrix.mul_smul, hQA g]`. Set `φ : M →ₗ[ℤ] M'` to `Matrix.toLin b b' Dm`. Use `⟨φ, ?_, ⟨Dm.det, hdet, fun y => ?_⟩, fun g x => ?_⟩` and prove the remaining obligations.

Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `x hx`. Establish `h1` using `Matrix.repr_toLin (v₁ := b) (v₂ := b') Dm x`. Rewrite `h1` using `[show Matrix.toLin b b' Dm x = 0 from hx, map_zero]`. Establish `h2` using `Matrix.eq_zero_of_mulVec_eq_zero hdet h1.symm`.

Conclude with `b.repr.map_eq_zero_iff.1 (Finsupp.ext fun i => congrFun h2 i)`. Use `⟨Matrix.toLin b' b Dm.adjugate y, ?_⟩ show (Matrix.toLin b b' Dm ∘ₗ Matrix.toLin b' b Dm.adjugate) y = _` and prove the remaining obligations. Rewrite using `[← Matrix.toLin_mul, Matrix.mul_adjugate, map_smul, Matrix.toLin_one, LinearMap.smul_apply, LinearMap.id_apply]`. Establish `h1 : φ ∘ₗ ρ g = ρ' g ∘ₗ φ`. Apply `(LinearMap.toMatrix b b').injective` to reduce the goal to its premises.

Rewrite using `[LinearMap.toMatrix_comp b b b', LinearMap.toMatrix_comp b b' b', LinearMap.toMatrix_toLin]`. Conclude with `hDA g`. Conclude with `LinearMap.congr_fun h1 x`.
-/
theorem exists_injective_intertwiner_of_basis {ι : Type*} [Fintype ι]
    (ρ : Representation ℤ G M) (ρ' : Representation ℤ G M') (e : ℝ ⊗[ℤ] M ≃ₗ[ℝ] ℝ ⊗[ℤ] M')
    (he : ∀ g x, e ((ρ g).baseChange ℝ x) = (ρ' g).baseChange ℝ (e x))
    (b : Module.Basis ι ℤ M) (b' : Module.Basis ι ℤ M') :
    ∃ φ : M →ₗ[ℤ] M', Function.Injective φ ∧ (∃ n : ℤ, n ≠ 0 ∧ ∀ y, ∃ x, φ x = n • y) ∧
      ∀ g x, φ (ρ g x) = ρ' g (φ x) := by
  classical

  let bR := Algebra.TensorProduct.basis ℝ b
  let bR' := Algebra.TensorProduct.basis ℝ b'
  let A : G → Matrix ι ι ℤ := fun g => LinearMap.toMatrix b b (ρ g)
  let A' : G → Matrix ι ι ℤ := fun g => LinearMap.toMatrix b' b' (ρ' g)
  let P : Matrix ι ι ℝ := LinearMap.toMatrix bR bR' e.toLinearMap
  have hP : P.det ≠ 0 := by
    have hid : e.symm.toLinearMap ∘ₗ e.toLinearMap = LinearMap.id :=
      LinearMap.ext fun x => by simp
    have h1 := congrArg (LinearMap.toMatrix bR bR) hid
    rw [LinearMap.toMatrix_comp bR bR' bR, LinearMap.toMatrix_id] at h1
    have h2 := congrArg Matrix.det h1
    rw [Matrix.det_mul, Matrix.det_one] at h2
    exact right_ne_zero_of_mul_eq_one h2
  have hPA : ∀ g, P * (A g).map (Int.cast : ℤ → ℝ) = (A' g).map (Int.cast : ℤ → ℝ) * P := by
    intro g
    have hc : e.toLinearMap ∘ₗ (ρ g).baseChange ℝ = (ρ' g).baseChange ℝ ∘ₗ e.toLinearMap :=
      LinearMap.ext (he g)
    have h1 := congrArg (LinearMap.toMatrix bR bR') hc
    rw [LinearMap.toMatrix_comp bR bR bR', LinearMap.toMatrix_comp bR bR' bR',
      LinearMap.toMatrix_baseChange, LinearMap.toMatrix_baseChange, algebraMap_int_eq] at h1
    exact h1

  obtain ⟨Q, hQ, hQA⟩ := exists_rat_intertwiner (fun g => (A g).map (Int.cast : ℤ → ℚ))
    (fun g => (A' g).map (Int.cast : ℤ → ℚ)) P hP (fun g => by
      rw [Matrix.map_map, Matrix.map_map]
      convert hPA g using 3 <;> ext x <;> simp)

  obtain ⟨⟨d, hd⟩, hdQ⟩ := IsLocalization.exist_integer_multiples (R := ℤ)
    (M := nonZeroDivisors ℤ) (S := ℚ) Finset.univ (fun p : ι × ι => Q p.1 p.2)
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  choose D hD using fun a b => RingHom.mem_rangeS.1 (hdQ (a, b) (Finset.mem_univ _))
  let Dm : Matrix ι ι ℤ := Matrix.of D
  have hDm : Dm.map (Int.cast : ℤ → ℚ) = (d : ℚ) • Q := by
    ext a b
    simp only [Matrix.map_apply, Matrix.smul_apply, Dm, Matrix.of_apply]
    rw [← eq_intCast (algebraMap ℤ ℚ), hD a b, zsmul_eq_mul, smul_eq_mul]
  have hdet : Dm.det ≠ 0 := by
    have h1 : (Dm.det : ℚ) = (d : ℚ) ^ Fintype.card ι * Q.det := by
      rw [Int.cast_det]
      change (Dm.map (Int.cast : ℤ → ℚ)).det = _
      rw [hDm, Matrix.det_smul]
    intro h0
    rw [h0, Int.cast_zero] at h1
    exact mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hd0)) hQ h1.symm
  have hmap : ∀ X Y : Matrix ι ι ℤ, (X * Y).map (Int.cast : ℤ → ℚ) =
      X.map (Int.cast : ℤ → ℚ) * Y.map (Int.cast : ℤ → ℚ) := fun X Y =>
    Matrix.map_mul (f := Int.castRingHom ℚ)
  have hDA : ∀ g, Dm * A g = A' g * Dm := by
    intro g
    apply Matrix.map_injective (f := (Int.cast : ℤ → ℚ)) Int.cast_injective
    show (Dm * A g).map (Int.cast : ℤ → ℚ) = (A' g * Dm).map (Int.cast : ℤ → ℚ)
    rw [hmap, hmap, hDm, Matrix.smul_mul, Matrix.mul_smul, hQA g]

  let φ : M →ₗ[ℤ] M' := Matrix.toLin b b' Dm
  refine ⟨φ, ?_, ⟨Dm.det, hdet, fun y => ?_⟩, fun g x => ?_⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h1 := Matrix.repr_toLin (v₁ := b) (v₂ := b') Dm x
    rw [show Matrix.toLin b b' Dm x = 0 from hx, map_zero] at h1
    have h2 := Matrix.eq_zero_of_mulVec_eq_zero hdet h1.symm
    exact b.repr.map_eq_zero_iff.1 (Finsupp.ext fun i => congrFun h2 i)
  · refine ⟨Matrix.toLin b' b Dm.adjugate y, ?_⟩
    show (Matrix.toLin b b' Dm ∘ₗ Matrix.toLin b' b Dm.adjugate) y = _
    rw [← Matrix.toLin_mul, Matrix.mul_adjugate, map_smul, Matrix.toLin_one,
      LinearMap.smul_apply, LinearMap.id_apply]
  · have h1 : φ ∘ₗ ρ g = ρ' g ∘ₗ φ := by
      apply (LinearMap.toMatrix b b').injective
      rw [LinearMap.toMatrix_comp b b b', LinearMap.toMatrix_comp b b' b',
        LinearMap.toMatrix_toLin]
      exact hDA g
    exact LinearMap.congr_fun h1 x

variable [Module.Finite ℤ M] [Module.Free ℤ M] [Module.Finite ℤ M'] [Module.Free ℤ M']

/- English proof (translation)
Set `b` to `Module.Free.chooseBasis ℤ M`. Set `b₀` to `Module.Free.chooseBasis ℤ M'`. Establish `h1` using `e.finrank_eq`. Rewrite `h1` using `[Module.finrank_eq_card_basis (Algebra.TensorProduct.basis ℝ b), Module.finrank_eq_card_basis (Algebra.TensorProduct.basis ℝ b₀)]`. Conclude with `exists_injective_intertwiner_of_basis ρ ρ' e he b (b₀.reindex (Fintype.equivOfCardEq h1).symm)`.
-/
theorem exists_injective_intertwiner_of_real_equiv (ρ : Representation ℤ G M)
    (ρ' : Representation ℤ G M') (e : ℝ ⊗[ℤ] M ≃ₗ[ℝ] ℝ ⊗[ℤ] M')
    (he : ∀ g x, e ((ρ g).baseChange ℝ x) = (ρ' g).baseChange ℝ (e x)) :
    ∃ φ : M →ₗ[ℤ] M', Function.Injective φ ∧ (∃ n : ℤ, n ≠ 0 ∧ ∀ y, ∃ x, φ x = n • y) ∧
      ∀ g x, φ (ρ g x) = ρ' g (φ x) := by
  let b := Module.Free.chooseBasis ℤ M
  let b₀ := Module.Free.chooseBasis ℤ M'
  have h1 := e.finrank_eq
  rw [Module.finrank_eq_card_basis (Algebra.TensorProduct.basis ℝ b),
    Module.finrank_eq_card_basis (Algebra.TensorProduct.basis ℝ b₀)] at h1
  exact exists_injective_intertwiner_of_basis ρ ρ' e he b
    (b₀.reindex (Fintype.equivOfCardEq h1).symm)

/- English proof (translation)
Take `⟨φ, hφ, ⟨n, hn, hrange⟩, hcomm⟩` from `exists_injective_intertwiner_of_real_equiv ρ ρ' e he`. Establish `: Finite (M' ⧸ φ.toAddMonoidHom.range)` using `finite_quotient_of_smul_mem _ hn fun y => by`. Take `⟨x, hx⟩` from `hrange y`. Conclude with `⟨x, hx⟩`. Conclude with `cyclicHerbrand_eq_of_injective ρ ρ' σ φ.toAddMonoidHom hφ hcomm`.
-/
theorem cyclicHerbrand_eq_of_real_equiv [Fintype G] (ρ : Representation ℤ G M)
    (ρ' : Representation ℤ G M') (σ : G) (e : ℝ ⊗[ℤ] M ≃ₗ[ℝ] ℝ ⊗[ℤ] M')
    (he : ∀ g x, e ((ρ g).baseChange ℝ x) = (ρ' g).baseChange ℝ (e x)) :
    cyclicHerbrand ρ σ = cyclicHerbrand ρ' σ := by
  obtain ⟨φ, hφ, ⟨n, hn, hrange⟩, hcomm⟩ := exists_injective_intertwiner_of_real_equiv ρ ρ' e he
  have : Finite (M' ⧸ φ.toAddMonoidHom.range) :=
    finite_quotient_of_smul_mem _ hn fun y => by
      obtain ⟨x, hx⟩ := hrange y
      exact ⟨x, hx⟩
  exact cyclicHerbrand_eq_of_injective ρ ρ' σ φ.toAddMonoidHom hφ hcomm

end GroundTheory.Global
