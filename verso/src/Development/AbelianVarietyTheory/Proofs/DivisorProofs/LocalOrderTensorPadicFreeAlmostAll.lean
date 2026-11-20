import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentreCompat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsScalarTowerCenAlgebra
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CycleListPermInvariant

noncomputable section
open scoped TensorProduct
open GlobalTheory.LKInvGood

namespace GlobalTheory.LocMatrix

/- English proof (translation)
Rewrite using `[cenMap_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, Algebra.smul_def]`.
-/
theorem tmul_smul_eq_cenMap_mul {F B : Type} [Field F] [NumberField F] [Ring B] [Algebra F B]
    [Algebra ℚ B] [IsScalarTower ℚ F B] (ℓ : ℕ) [Fact ℓ.Prime] (q : ℚ_[ℓ]) (c : F) (v : B) :
    q ⊗ₜ[ℚ] (c • v) = cenMap ℓ F B (q ⊗ₜ c) * ((1 : ℚ_[ℓ]) ⊗ₜ v) := by
  rw [cenMap_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, Algebra.smul_def]

def combMap {F B : Type} [Field F] [NumberField F] [Ring B] [Algebra F B]
    [Algebra ℚ B] [IsScalarTower ℚ F B] (ℓ : ℕ) [Fact ℓ.Prime] {d : ℕ} (v : Fin d → B) :
    (Fin d → ℚ_[ℓ] ⊗[ℚ] F) →ₗ[ℚ_[ℓ]] ℚ_[ℓ] ⊗[ℚ] B where
  toFun c := ∑ i, cenMap ℓ F B (c i) * ((1 : ℚ_[ℓ]) ⊗ₜ v i)
  map_add' c c' := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' r c := by simp [Finset.smul_sum, smul_mul_assoc]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem combMap_apply {F B : Type} [Field F] [NumberField F] [Ring B] [Algebra F B]
    [Algebra ℚ B] [IsScalarTower ℚ F B] (ℓ : ℕ) [Fact ℓ.Prime] {d : ℕ} (v : Fin d → B)
    (c : Fin d → ℚ_[ℓ] ⊗[ℚ] F) :
    combMap ℓ v c = ∑ i, cenMap ℓ F B (c i) * ((1 : ℚ_[ℓ]) ⊗ₜ v i) := rfl

/- English proof (translation)
Rewrite using `[← LinearMap.range_eq_top, eq_top_iff]`. Introduce and unpack `x -`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => exact zero_mem _`. Consider the case `tmul q b`.

Rewrite using `[← v.sum_repr b, TensorProduct.tmul_sum]`. Use `Submodule.sum_mem _ fun i _ => ⟨Pi.single i (q ⊗ₜ[ℚ] v.repr b i), ?_⟩` and prove the remaining obligations. Rewrite using `[combMap_apply, Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, map_zero, zero_mul]) (by simp), Pi.single_eq_same, ← tmul_smul_eq_cenMap_mul]`. Consider the case `add x y hx hy => exact add_mem hx hy`.
-/
theorem combMap_surjective {F B : Type} [Field F] [NumberField F] [Ring B] [Algebra F B]
    [Algebra ℚ B] [IsScalarTower ℚ F B] (ℓ : ℕ) [Fact ℓ.Prime] {d : ℕ} (v : Module.Basis (Fin d) F B) :
    Function.Surjective (combMap (F := F) ℓ v) := by
  rw [← LinearMap.range_eq_top, eq_top_iff]
  rintro x -
  induction x using TensorProduct.induction_on with
  | zero => exact zero_mem _
  | tmul q b =>
    rw [← v.sum_repr b, TensorProduct.tmul_sum]
    refine Submodule.sum_mem _ fun i _ => ⟨Pi.single i (q ⊗ₜ[ℚ] v.repr b i), ?_⟩
    rw [combMap_apply, Finset.sum_eq_single i
      (fun j _ hj => by rw [Pi.single_eq_of_ne hj, map_zero, zero_mul]) (by simp),
      Pi.single_eq_same, ← tmul_smul_eq_cenMap_mul]
  | add x y hx hy => exact add_mem hx hy

/- English proof (translation)
Use `haveI : FiniteDimensional ℚ B := Module.Finite.trans F B`. Establish `hdim : Module.finrank ℚ_[ℓ] (Fin d → ℚ_[ℓ] ⊗[ℚ] F) = Module.finrank ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] B)`. Rewrite using `[Module.finrank_pi_fintype, Module.finrank_baseChange, Module.finrank_baseChange, ← Module.finrank_mul_finrank ℚ F B, Module.finrank_eq_card_basis v]`. Simplify using `[mul_comm]`. Conclude with `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2 (combMap_surjective ℓ v)`.
-/
theorem combMap_injective {F B : Type} [Field F] [NumberField F] [Ring B] [Algebra F B]
    [Algebra ℚ B] [IsScalarTower ℚ F B] [FiniteDimensional F B] (ℓ : ℕ) [Fact ℓ.Prime] {d : ℕ}
    (v : Module.Basis (Fin d) F B) : Function.Injective (combMap (F := F) ℓ v) := by
  haveI : FiniteDimensional ℚ B := Module.Finite.trans F B
  have hdim : Module.finrank ℚ_[ℓ] (Fin d → ℚ_[ℓ] ⊗[ℚ] F) = Module.finrank ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] B) := by
    rw [Module.finrank_pi_fintype, Module.finrank_baseChange, Module.finrank_baseChange,
      ← Module.finrank_mul_finrank ℚ F B, Module.finrank_eq_card_basis v]
    simp [mul_comm]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2 (combMap_surjective ℓ v)

end GlobalTheory.LocMatrix

namespace GlobalTheory.LocMatrix

/- English proof (translation)
Set `e` to `Module.finBasis F B`. Use `choose m hm hmΛ using hspan`. Set `u : Fin (Module.finrank F B) → Fˣ` to `fun i => Units.mk0 (m (e i) : F) (Nat.cast_ne_zero.2 (hm (e i)).ne')`. Use `⟨e.unitsSMul u, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[Module.Basis.unitsSMul_apply, Units.smul_def]`.

Establish `h : (u i : F) • e i = (m (e i) : B) * e i`. Simplify using `[u, Algebra.smul_def]`. Rewrite using `[h]`. Conclude with `hmΛ _`.
-/
theorem exists_basis_mem {F B : Type} [Field F] [CharZero F] [Ring B] [Algebra F B] [FiniteDimensional F B]
    (Λ : Subring B) (hspan : ∀ b : B, ∃ m : ℕ, 0 < m ∧ (m : B) * b ∈ Λ) :
    ∃ v : Module.Basis (Fin (Module.finrank F B)) F B, ∀ i, v i ∈ Λ := by
  let e := Module.finBasis F B
  choose m hm hmΛ using hspan
  let u : Fin (Module.finrank F B) → Fˣ := fun i =>
    Units.mk0 (m (e i) : F) (Nat.cast_ne_zero.2 (hm (e i)).ne')
  refine ⟨e.unitsSMul u, fun i => ?_⟩
  rw [Module.Basis.unitsSMul_apply, Units.smul_def]
  have h : (u i : F) • e i = (m (e i) : B) * e i := by
    simp [u, Algebra.smul_def]
  rw [h]
  exact hmΛ _

/- English proof (translation)
Take `⟨s, hs⟩` from `hfin.fg_top`. Take `⟨D, hD, hDs⟩` from `GlobalTheory.SepModel.exists_nat_integral (Finset.univ.image fun p : s × ι => v.repr ((p.1 : Λ) : B) p.2)`. Use `⟨D, hD, fun x hx => ?_⟩` and prove the remaining obligations. Set `P : Submodule ℤ Λ` to `{ carrier := {y | ∀ i, IsIntegral ℤ ((D : F) * v.repr (y : B) i)} add_mem' := by`. Introduce `y z hy hz i`.

Simplify using `only [Set.mem_setOf_eq, Subring.coe_add, map_add, Finsupp.add_apply, mul_add] at hy hz ⊢`. Conclude with `(hy i).add (hz i)`. Use the proof step `zero_mem' := by`. Introduce `i`. Simplify using the standard rewrite rules.

Conclude with `isIntegral_zero`. Use the proof step `smul_mem' := by`. Introduce `c y hy i`. Simplify using `only [Set.mem_setOf_eq] at hy ⊢`. Establish `h2 : v.repr ((c • y : Λ) : B) i = (c : F) * v.repr (y : B) i`.

Rewrite using `[show ((c • y : Λ) : B) = c • (y : B) from rfl, map_zsmul, Finsupp.smul_apply, zsmul_eq_mul]`. Establish `hc : IsIntegral ℤ (c : F)`. Simplify using `using (isIntegral_algebraMap (R := ℤ) (A := F) (x := c))`. Rewrite using `[h2, mul_left_comm]`. Conclude with `hc.mul (hy i) }`.

Establish `hsP : (s : Set Λ) ⊆ P` using `fun y hy i => hDs _ (Finset.mem_image.2 ⟨(⟨y, hy⟩, i), Finset.mem_univ _, rfl⟩)`. Establish `hmem : (⟨x, hx⟩ : Λ) ∈ P`. Establish `h` using `Submodule.span_le.mpr hsP`. Rewrite `h` using `[hs]`. Conclude with `h Submodule.mem_top`.

Conclude with `hmem`.
-/
theorem exists_den {F B : Type} [Field F] [NumberField F] [Ring B] [Algebra F B]
    (Λ : Subring B) (hfin : Module.Finite ℤ Λ) {ι : Type} [Fintype ι] (v : Module.Basis ι F B) :
    ∃ D : ℕ, 0 < D ∧ ∀ x ∈ Λ, ∀ i, IsIntegral ℤ ((D : F) * v.repr x i) := by
  classical
  obtain ⟨s, hs⟩ := hfin.fg_top
  obtain ⟨D, hD, hDs⟩ := GlobalTheory.SepModel.exists_nat_integral
    (Finset.univ.image fun p : s × ι => v.repr ((p.1 : Λ) : B) p.2)
  refine ⟨D, hD, fun x hx => ?_⟩
  let P : Submodule ℤ Λ :=
    { carrier := {y | ∀ i, IsIntegral ℤ ((D : F) * v.repr (y : B) i)}
      add_mem' := by
        intro y z hy hz i
        simp only [Set.mem_setOf_eq, Subring.coe_add, map_add, Finsupp.add_apply, mul_add] at hy hz ⊢
        exact (hy i).add (hz i)
      zero_mem' := by
        intro i
        simp
        exact isIntegral_zero
      smul_mem' := by
        intro c y hy i
        simp only [Set.mem_setOf_eq] at hy ⊢
        have h2 : v.repr ((c • y : Λ) : B) i = (c : F) * v.repr (y : B) i := by
          rw [show ((c • y : Λ) : B) = c • (y : B) from rfl, map_zsmul, Finsupp.smul_apply,
            zsmul_eq_mul]
        have hc : IsIntegral ℤ (c : F) := by
          simpa using (isIntegral_algebraMap (R := ℤ) (A := F) (x := c))
        rw [h2, mul_left_comm]
        exact hc.mul (hy i) }
  have hsP : (s : Set Λ) ⊆ P := fun y hy i =>
    hDs _ (Finset.mem_image.2 ⟨(⟨y, hy⟩, i), Finset.mem_univ _, rfl⟩)
  have hmem : (⟨x, hx⟩ : Λ) ∈ P := by
    have h := Submodule.span_le.mpr hsP
    rw [hs] at h
    exact h Submodule.mem_top
  exact hmem

end GlobalTheory.LocMatrix

namespace GlobalTheory.LocMatrix

/- English proof (translation)
Set `S : Submodule ℤ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] B)` to `{ carrier := {z | ∃ c : Fin d → cenOrder ℓ F, z = ∑ i, cenMap ℓ F B (c i) * ((1 : ℚ_[ℓ]) ⊗ₜ v i)} add_mem' := by`. Introduce and unpack `_ _ ⟨c, rfl⟩ ⟨c', rfl⟩`. Conclude with `⟨c + c', by simp [add_mul, Finset.sum_add_distrib]⟩`. Use the proof step `zero_mem' := ⟨0, by simp⟩`. Use the proof step `smul_mem' := by`.

Introduce and unpack `r _ ⟨c, rfl⟩`. Use `⟨r • c, ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.smul_apply, Subalgebra.coe_smul, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← algebraMap_smul ℚ_[ℓ] r ((c i : cenOrder ℓ F) : ℚ_[ℓ] ⊗[ℚ] F), map_smul, smul_mul_assoc, algebraMap_smul] }`.

Establish `gen : ∀ x ∈ Λ, (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] x ∈ S`. Introduce `x hx`. Use `⟨fun i => ⟨_, GlobalTheory.SepModel.tmul_mem_cenOrder ℓ hℓ (hD x hx i)⟩, ?_⟩` and prove the remaining obligations. Use `conv_lhs => rw [← v.sum_repr x, TensorProduct.tmul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Conclude with `tmul_smul_eq_cenMap_mul ℓ 1 _ _`. Establish `hz' : z ∈ Subalgebra.toSubmodule (locOrder ℓ Λ)` using `hz`. Rewrite `hz'` using `[locOrder, Algebra.adjoin_eq_span]`. Establish `hcl : (Submonoid.closure ((fun b : B => (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] b) '' (Λ : Set B)) : Set (ℚ_[ℓ] ⊗[ℚ] B)) ⊆ S`. Introduce `y hy`.

Establish `hy' : y ∈ Λ.toSubmonoid.map (Algebra.TensorProduct.includeRight : B →ₐ[ℚ] ℚ_[ℓ] ⊗[ℚ] B)`. Use `(Submonoid.closure_le.2 ?_) hy` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `⟨x, hx, rfl⟩`. Take `⟨x, hx, rfl⟩` from `hy'`.

Conclude with `gen x hx`. Conclude with `Submodule.span_le.2 hcl hz'`.
-/
theorem exists_coeffs {F B : Type} [Field F] [NumberField F] [Ring B] [Algebra F B]
    [Algebra ℚ B] [IsScalarTower ℚ F B] (ℓ : ℕ) [Fact ℓ.Prime] (Λ : Subring B) {d : ℕ}
    (v : Module.Basis (Fin d) F B) (D : ℕ)
    (hD : ∀ x ∈ Λ, ∀ i, IsIntegral ℤ ((D : F) * v.repr x i)) (hℓ : ¬ ℓ ∣ D)
    (z : ℚ_[ℓ] ⊗[ℚ] B) (hz : z ∈ locOrder ℓ Λ) :
    ∃ c : Fin d → cenOrder ℓ F, z = ∑ i, cenMap ℓ F B (c i) * ((1 : ℚ_[ℓ]) ⊗ₜ v i) := by
  let S : Submodule ℤ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] B) :=
    { carrier := {z | ∃ c : Fin d → cenOrder ℓ F, z = ∑ i, cenMap ℓ F B (c i) * ((1 : ℚ_[ℓ]) ⊗ₜ v i)}
      add_mem' := by
        rintro _ _ ⟨c, rfl⟩ ⟨c', rfl⟩
        exact ⟨c + c', by simp [add_mul, Finset.sum_add_distrib]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro r _ ⟨c, rfl⟩
        refine ⟨r • c, ?_⟩
        simp only [Pi.smul_apply, Subalgebra.coe_smul, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← algebraMap_smul ℚ_[ℓ] r ((c i : cenOrder ℓ F) : ℚ_[ℓ] ⊗[ℚ] F), map_smul, smul_mul_assoc,
          algebraMap_smul] }
  have gen : ∀ x ∈ Λ, (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] x ∈ S := by
    intro x hx
    refine ⟨fun i => ⟨_, GlobalTheory.SepModel.tmul_mem_cenOrder ℓ hℓ (hD x hx i)⟩, ?_⟩
    conv_lhs => rw [← v.sum_repr x, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact tmul_smul_eq_cenMap_mul ℓ 1 _ _
  have hz' : z ∈ Subalgebra.toSubmodule (locOrder ℓ Λ) := hz
  rw [locOrder, Algebra.adjoin_eq_span] at hz'
  have hcl : (Submonoid.closure ((fun b : B => (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] b) '' (Λ : Set B)) :
      Set (ℚ_[ℓ] ⊗[ℚ] B)) ⊆ S := by
    intro y hy
    have hy' : y ∈ Λ.toSubmonoid.map
        (Algebra.TensorProduct.includeRight : B →ₐ[ℚ] ℚ_[ℓ] ⊗[ℚ] B) := by
      refine (Submonoid.closure_le.2 ?_) hy
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    obtain ⟨x, hx, rfl⟩ := hy'
    exact gen x hx
  exact Submodule.span_le.2 hcl hz'

/- English proof (translation)
Introduce `F B _ _ _ _ _ _ _ Λ hΛ hfin hspan`. Take `⟨v, hvΛ⟩` from `exists_basis_mem (F := F) Λ hspan`. Take `⟨D, hD, hDΛ⟩` from `exists_den Λ hfin v`. Use `⟨D, hD, fun ℓ _ hℓ => ?_⟩` and prove the remaining obligations. Use `letI := GlobalTheory.LocMatrix.cenAlgebra ℓ F B Λ hΛ`.

Set `w : Fin (Module.finrank F B) → locOrder ℓ Λ` to `fun i => ⟨(1 : ℚ_[ℓ]) ⊗ₜ v i, Algebra.subset_adjoin ⟨_, hvΛ i, rfl⟩⟩`. Establish `hsmul : ∀ (c : cenOrder ℓ F) (x : locOrder ℓ Λ), ((c • x : locOrder ℓ Λ) : ℚ_[ℓ] ⊗[ℚ] B) = cenMap ℓ F B c * x` using `fun c x => rfl`. Establish `hsum : ∀ c : Fin (Module.finrank F B) → cenOrder ℓ F, ((∑ i, c i • w i : locOrder ℓ Λ) : ℚ_[ℓ] ⊗[ℚ] B) = combMap (F` using `F) ℓ v (fun i => (c i : ℚ_[ℓ] ⊗[ℚ] F)) := by`. Introduce `c`. Rewrite using `[AddSubmonoidClass.coe_finset_sum, combMap_apply]`.

Conclude with `Finset.sum_congr rfl fun i _ => hsmul _ _`. Establish `hli : LinearIndependent (cenOrder ℓ F) w`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg i`. Establish `h0 : combMap (F` using `F) ℓ v (fun i => (g i : ℚ_[ℓ] ⊗[ℚ] F)) = combMap (F := F) ℓ v 0 := by`.

Rewrite using `[← hsum, hg, map_zero]`. Both sides reduce to the same expression. Conclude with `Subtype.ext (congrFun (combMap_injective ℓ v h0) i)`. Establish `hsp : ⊤ ≤ Submodule.span (cenOrder ℓ F) (Set.range w)`. Introduce and unpack `⟨z, hz⟩ -`.

Take `⟨c, hc⟩` from `exists_coeffs ℓ Λ v D hDΛ hℓ z hz`. Rewrite using `[Submodule.mem_span_range_iff_exists_fun]`. Conclude with `⟨c, Subtype.ext ((hsum c).trans hc.symm)⟩`. Use `haveI : Nontrivial (ℚ_[ℓ] ⊗[ℚ] F) := by`. Apply `Module.nontrivial_of_finrank_pos (R := ℚ_[ℓ])` to reduce the goal to its premises.

Rewrite using `[Module.finrank_baseChange]`. Conclude with `Module.finrank_pos`. Set `bas` to `Module.Basis.mk hli hsp`. Conclude with `⟨Module.Free.of_basis bas, by rw [Module.finrank_eq_card_basis bas, Fintype.card_fin]⟩`.
-/
theorem locOrder_free : ∀ (F B : Type) [Field F] [NumberField F] [Ring B] [Algebra F B] [Algebra ℚ B]
    [IsScalarTower ℚ F B] [FiniteDimensional F B] (Λ : Subring B)
    (hΛ : ∀ a : NumberField.RingOfIntegers F, algebraMap F B (a : F) ∈ Λ),
    Module.Finite ℤ Λ → (∀ b : B, ∃ m : ℕ, 0 < m ∧ (m : B) * b ∈ Λ) →
    ∃ N : ℕ, 0 < N ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime], ¬ ℓ ∣ N →
      letI := GlobalTheory.LocMatrix.cenAlgebra ℓ F B Λ hΛ
      Module.Free (cenOrder ℓ F) (locOrder ℓ Λ) ∧
        Module.finrank (cenOrder ℓ F) (locOrder ℓ Λ) = Module.finrank F B := by
  intro F B _ _ _ _ _ _ _ Λ hΛ hfin hspan
  obtain ⟨v, hvΛ⟩ := exists_basis_mem (F := F) Λ hspan
  obtain ⟨D, hD, hDΛ⟩ := exists_den Λ hfin v
  refine ⟨D, hD, fun ℓ _ hℓ => ?_⟩
  letI := GlobalTheory.LocMatrix.cenAlgebra ℓ F B Λ hΛ
  let w : Fin (Module.finrank F B) → locOrder ℓ Λ := fun i =>
    ⟨(1 : ℚ_[ℓ]) ⊗ₜ v i, Algebra.subset_adjoin ⟨_, hvΛ i, rfl⟩⟩
  have hsmul : ∀ (c : cenOrder ℓ F) (x : locOrder ℓ Λ),
      ((c • x : locOrder ℓ Λ) : ℚ_[ℓ] ⊗[ℚ] B) = cenMap ℓ F B c * x := fun c x => rfl
  have hsum : ∀ c : Fin (Module.finrank F B) → cenOrder ℓ F,
      ((∑ i, c i • w i : locOrder ℓ Λ) : ℚ_[ℓ] ⊗[ℚ] B) =
        combMap (F := F) ℓ v (fun i => (c i : ℚ_[ℓ] ⊗[ℚ] F)) := by
    intro c
    rw [AddSubmonoidClass.coe_finset_sum, combMap_apply]
    exact Finset.sum_congr rfl fun i _ => hsmul _ _
  have hli : LinearIndependent (cenOrder ℓ F) w := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h0 : combMap (F := F) ℓ v (fun i => (g i : ℚ_[ℓ] ⊗[ℚ] F)) = combMap (F := F) ℓ v 0 := by
      rw [← hsum, hg, map_zero]
      rfl
    exact Subtype.ext (congrFun (combMap_injective ℓ v h0) i)
  have hsp : ⊤ ≤ Submodule.span (cenOrder ℓ F) (Set.range w) := by
    rintro ⟨z, hz⟩ -
    obtain ⟨c, hc⟩ := exists_coeffs ℓ Λ v D hDΛ hℓ z hz
    rw [Submodule.mem_span_range_iff_exists_fun]
    exact ⟨c, Subtype.ext ((hsum c).trans hc.symm)⟩
  haveI : Nontrivial (ℚ_[ℓ] ⊗[ℚ] F) := by
    apply Module.nontrivial_of_finrank_pos (R := ℚ_[ℓ])
    rw [Module.finrank_baseChange]
    exact Module.finrank_pos
  let bas := Module.Basis.mk hli hsp
  exact ⟨Module.Free.of_basis bas, by rw [Module.finrank_eq_card_basis bas, Fintype.card_fin]⟩

end GlobalTheory.LocMatrix
