import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.Columns.HeckeSp
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotentsStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevSplit

open Formalism.IndefR.Lev Formalism.L2.DIV

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

/- English proof (translation)
The claim follows from `φ.isOfFinOrder (isOfFinOrder_of_finite g)`.
-/
theorem finOrd_hom {G M : Type} [Group G] [Finite G] [Monoid M] (φ : G →* M) (g : G) : IsOfFinOrder (φ g) :=
  φ.isOfFinOrder (isOfFinOrder_of_finite g)

/- English proof (translation)
The claim follows from `Finset.prod_induction f IsOfFinOrder (fun _ _ ha hb => ha.mul hb) IsOfFinOrder.one h`.
-/
theorem finOrd_prod {ι M : Type} [CommMonoid M] (s : Finset ι) (f : ι → M) (h : ∀ i ∈ s, IsOfFinOrder (f i)) :
    IsOfFinOrder (∏ i ∈ s, f i) :=
  Finset.prod_induction f IsOfFinOrder (fun _ _ ha hb => ha.mul hb) IsOfFinOrder.one h

instance finite_kP (PP : Pl E) : Finite (kP PP) := PP.asIdeal.finiteQuotientOfFreeOfNeBot PP.ne_bot

/- English proof (translation)
Unfold `levFn`. Use `IsOfFinOrder.mul (IsOfFinOrder.mul ?_ ?_) ?_` and prove the remaining obligations. Unfold `ext1 split_ifs`. Conclude with `finOrd_hom _ _`. Conclude with `IsOfFinOrder.one`.

Conclude with `finOrd_prod _ _ fun PP _ => finOrd_prod _ _ fun c _ => finOrd_hom _ _`. Conclude with `finOrd_prod _ _ fun PP _ => finOrd_hom _ _`.
-/
theorem levFn_finOrd {LL : Type} [CommRing LL] (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (L : LevDat E LL n)
    (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : IsOfFinOrder (levFn β L x) := by
  unfold levFn
  refine IsOfFinOrder.mul (IsOfFinOrder.mul ?_ ?_) ?_
  · unfold ext1
    split_ifs
    · exact finOrd_hom _ _
    · exact IsOfFinOrder.one
  · exact finOrd_prod _ _ fun PP _ => finOrd_prod _ _ fun c _ => finOrd_hom _ _
  · exact finOrd_prod _ _ fun PP _ => finOrd_hom _ _

/- English proof (translation)
Establish `h1 : rTup β L x = 1`. Use function extensionality and compare the values at `PP`. Use `show upperLeftBlock L.hr (redFn β PP.1 x) = 1`. Rewrite using `[h PP.1 (Or.inl PP.2)]`. Conclude with `blockDiagonalExtendByOnePrimeField_one _ _`.

Unfold `levFn`. Rewrite using `[h1, blockDiagonalExtendByOnePrimeField_one, one_mul, Finset.prod_eq_one, Finset.prod_eq_one, one_mul]`. Introduce `PP hP`. Rewrite using `[h PP (Or.inr hP), dBlk, blockDiagonalExtendByOnePrimeField_one, map_one]`. Introduce `PP hP`.

Use `Finset.prod_eq_one fun c _ => ?_` and prove the remaining obligations. Rewrite using `[h PP (Or.inl hP), dBlk, blockDiagonalExtendByOnePrimeField_one, map_one]`.
-/
theorem levFn_eq_one {LL : Type} [CommRing LL] (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (L : LevDat E LL n)
    (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (h : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → redFn β PP x = 1) :
    levFn β L x = 1 := by
  have h1 : rTup β L x = 1 := by
    funext PP
    show upperLeftBlock L.hr (redFn β PP.1 x) = 1
    rw [h PP.1 (Or.inl PP.2)]; exact blockDiagonalExtendByOnePrimeField_one _ _
  unfold levFn
  rw [h1, blockDiagonalExtendByOnePrimeField_one, one_mul, Finset.prod_eq_one, Finset.prod_eq_one, one_mul]
  · intro PP hP
    rw [h PP (Or.inr hP), dBlk, blockDiagonalExtendByOnePrimeField_one, map_one]
  · intro PP hP
    refine Finset.prod_eq_one fun c _ => ?_
    rw [h PP (Or.inl hP), dBlk, blockDiagonalExtendByOnePrimeField_one, map_one]

/- English proof (translation)
Use `mem_lev.2 ⟨mem_parLev.2 ⟨hU, hS, fun PP hP => ?_, fun PP hP => ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[h PP (Or.inl hP)]`. Conclude with `Subgroup.one_mem _`. Rewrite using `[h PP (Or.inr hP)]`. Conclude with `Subgroup.one_mem _`.

Establish `h1 : rTup β L x = 1`. Use function extensionality and compare the values at `PP`. Use `show upperLeftBlock L.hr (redFn β PP.1 x) = 1`. Rewrite using `[h PP.1 (Or.inl PP.2)]`. Conclude with `blockDiagonalExtendByOnePrimeField_one _ _`.

Rewrite using `[h1]`. Conclude with `Subgroup.one_mem _`.
-/
theorem mem_lev_of_red [StarRing E] {LL : Type} [CommRing LL] (hc : CMData F E) (J : Matrix (Fin n) (Fin n) E)
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (L : LevDat E LL n)
    (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (hU : x ∈ UA hc J) (hS : x ∈ St β)
    (h : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → redFn β PP x = 1) : x ∈ lev hc J β L := by
  refine mem_lev.2 ⟨mem_parLev.2 ⟨hU, hS, fun PP hP => ?_, fun PP hP => ?_⟩, ?_⟩
  · rw [h PP (Or.inl hP)]; exact Subgroup.one_mem _
  · rw [h PP (Or.inr hP)]; exact Subgroup.one_mem _
  · have h1 : rTup β L x = 1 := by
      funext PP
      show upperLeftBlock L.hr (redFn β PP.1 x) = 1
      rw [h PP.1 (Or.inl PP.2)]; exact blockDiagonalExtendByOnePrimeField_one _ _
    rw [h1]; exact Subgroup.one_mem _

/- English proof (translation)
Take `⟨y, rfl⟩` from `hS`. Rewrite using `[redFn_frGL]`. Use `set Y : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) := (intGL F E n y).1 with hY`. Establish `e1 : ((frGL β y : GL (Fin n) _) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = β.1 * Y * (β⁻¹).1` using `rfl`. Establish `e2 : Y - 1 = (β⁻¹).1 * ((frGL β y : GL (Fin n) _).1 - 1) * β.1`.

Rewrite using `[e1, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Units.inv_mul]`. Simplify using `only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]`. Rewrite using `[Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]`. Establish `e3 : (φ : E ⊗[F] Formalism.L2.Herm.Af F) • (Y - 1) = Y - 1`. Rewrite using `[e2, ← Matrix.smul_mul, ← Matrix.mul_smul, hx]`.

Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Establish `e4 : φ * (y.1 - 1) i j = (y.1 - 1) i j`. Apply `Subtype.ext` to reduce the goal to its premises. Use `congrFun (congrFun e3 i) j` as an intermediate fact.

Establish `e5 : (((y.1 - 1) i j : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) = (Y - 1) i j`. Rewrite using `[Matrix.sub_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> rfl`. Rewrite using `[Subring.coe_mul, e5]`. Conclude with `this`.

Establish `e6 : resS F PP ((y.1 - 1) i j) = 0` using `by rw [← e4, map_mul, hφ, zero_mul]`. Use `show resS F PP (y.1 i j) = (1 : Matrix (Fin n) (Fin n) (kP PP)) i j`. Rewrite `e6` using `[Matrix.sub_apply, map_sub, sub_eq_zero]`. Rewrite using `[e6, Matrix.one_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem redFn_eq_one (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (PP : Pl E)
    (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (hS : x ∈ St β) (φ : Formalism.L2.Herm.intAf F E) (hφ : resS F PP φ = 0)
    (hx : (φ : E ⊗[F] Formalism.L2.Herm.Af F) • ((x : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) - 1) =
      (x : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) - 1) : redFn β PP x = 1 := by
  obtain ⟨y, rfl⟩ := hS
  rw [redFn_frGL]
  set Y : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) := (intGL F E n y).1 with hY
  have e1 : ((frGL β y : GL (Fin n) _) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = β.1 * Y * (β⁻¹).1 := rfl
  have e2 : Y - 1 = (β⁻¹).1 * ((frGL β y : GL (Fin n) _).1 - 1) * β.1 := by
    rw [e1, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Units.inv_mul]
    simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  have e3 : (φ : E ⊗[F] Formalism.L2.Herm.Af F) • (Y - 1) = Y - 1 := by
    rw [e2, ← Matrix.smul_mul, ← Matrix.mul_smul, hx]
  apply Units.ext
  ext i j
  have e4 : φ * (y.1 - 1) i j = (y.1 - 1) i j := by
    apply Subtype.ext
    have := congrFun (congrFun e3 i) j
    have e5 : (((y.1 - 1) i j : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) = (Y - 1) i j := by
      rw [Matrix.sub_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> rfl
    rw [Subring.coe_mul, e5]
    exact this
  have e6 : resS F PP ((y.1 - 1) i j) = 0 := by rw [← e4, map_mul, hφ, zero_mul]
  show resS F PP (y.1 i j) = (1 : Matrix (Fin n) (Fin n) (kP PP)) i j
  rw [Matrix.sub_apply, map_sub, sub_eq_zero] at e6
  rw [e6, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

/- English proof (translation)
Establish `key : ∀ x ∈ St β, ∀ y ∈ Formalism.L2.Herm.hatL (F` using `F) Λ, x.1 *ᵥ y ∈ Formalism.L2.Herm.hatL (F := F) Λ := by`. Introduce and unpack `_ ⟨z, rfl⟩ y hy`. Rewrite `hy`, the goal using `[hβ]`. Establish `e1 : ((frGL β z : GL (Fin n) _) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = β.1 * (intGL F E n z).1 * (β⁻¹).1` using `rfl`. Introduce `i`.

Rewrite using `[e1, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, ← Matrix.mulVec_mulVec]`. Use `show ∑ j : Fin n, _ * _ ∈ _`. Conclude with `Subring.sum_mem _ fun j _ => Subring.mul_mem _ (z.1 i j).2 (hy j)`. Establish `key2 : ∀ x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F), (∀ y ∈ Formalism.L2.Herm.hatL (F` using `F) Λ, x.1 *ᵥ y ∈ Formalism.L2.Herm.hatL (F := F) Λ) → ∀ i j, (β⁻¹ * x * β).1 i j ∈ Formalism.L2.Herm.intAf F E := by`. Introduce `x h i j`.

Establish `h1 : β.1 *ᵥ Pi.single j 1 ∈ Formalism.L2.Herm.hatL (F` using `F) Λ := by`. Rewrite using `[hβ]`. Introduce `k`. Rewrite using `[Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Pi.single_apply]`. Use `split_ifs`.

Conclude with `Subring.one_mem _`. Conclude with `Subring.zero_mem _`. Establish `h2` using `(hβ _).1 (h _ h1) i`. Rewrite `h2` using `[Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_single_one]`. Conclude with `h2`.

Prove the components needed by the constructor for the conclusion. Conclude with `fun h => ⟨key x h, key _ ((St β).inv_mem h)⟩`. Introduce and unpack `⟨h1, h2⟩`. Establish `a1` using `key2 x h1`. Establish `a2` using `key2 x⁻¹ h2`.

Set `M : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)` to `fun i j => ⟨_, a1 i j⟩`. Set `M' : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)` to `fun i j => ⟨_, a2 i j⟩`. Establish `hM : (Formalism.L2.Herm.intAf F E).subtype.mapMatrix M = (β⁻¹ * x * β).1` using `rfl`. Establish `hM' : (Formalism.L2.Herm.intAf F E).subtype.mapMatrix M' = (β⁻¹ * x⁻¹ * β).1` using `rfl`. Establish `inj : Function.Injective ((Formalism.L2.Herm.intAf F E).subtype.mapMatrix (m` using `Fin n)) := by`.

Introduce `A B h`. Use extensionality with `i j`. Conclude with `congrFun (congrFun h i) j`. Establish `p1 : M * M' = 1` using `inj (by`. Rewrite using `[map_mul, map_one, hM, hM', ← Units.val_mul]`.

Simplify using `[mul_assoc])`. Establish `p2 : M' * M = 1` using `inj (by`. Rewrite using `[map_mul, map_one, hM, hM', ← Units.val_mul]`. Simplify using `[mul_assoc])`. Use `⟨⟨M, M', p1, p2⟩, ?_⟩` and prove the remaining obligations.

Establish `: intGL F E n ⟨M, M', p1, p2⟩ = β⁻¹ * x * β` using `Units.ext hM`. Use `show β * intGL F E n ⟨M, M', p1, p2⟩ * β⁻¹ = x`. Rewrite using `[this]`. Use `group`.
-/
theorem mem_St_iff (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (Λ : Submodule (𝓞 E) (Fin n → E)) (hβ : IsFrame β Λ)
    (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
    x ∈ St β ↔ (∀ y ∈ Formalism.L2.Herm.hatL (F := F) Λ, x.1 *ᵥ y ∈ Formalism.L2.Herm.hatL (F := F) Λ) ∧
      ∀ y ∈ Formalism.L2.Herm.hatL (F := F) Λ, (x⁻¹).1 *ᵥ y ∈ Formalism.L2.Herm.hatL (F := F) Λ := by
  have key : ∀ x ∈ St β, ∀ y ∈ Formalism.L2.Herm.hatL (F := F) Λ, x.1 *ᵥ y ∈ Formalism.L2.Herm.hatL (F := F) Λ := by
    rintro _ ⟨z, rfl⟩ y hy
    rw [hβ] at hy ⊢
    have e1 : ((frGL β z : GL (Fin n) _) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
      β.1 * (intGL F E n z).1 * (β⁻¹).1 := rfl
    intro i
    rw [e1, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul,
      ← Matrix.mulVec_mulVec]
    show ∑ j : Fin n, _ * _ ∈ _
    exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (z.1 i j).2 (hy j)
  have key2 : ∀ x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F),
      (∀ y ∈ Formalism.L2.Herm.hatL (F := F) Λ, x.1 *ᵥ y ∈ Formalism.L2.Herm.hatL (F := F) Λ) →
      ∀ i j, (β⁻¹ * x * β).1 i j ∈ Formalism.L2.Herm.intAf F E := by
    intro x h i j
    have h1 : β.1 *ᵥ Pi.single j 1 ∈ Formalism.L2.Herm.hatL (F := F) Λ := by
      rw [hβ]
      intro k
      rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Pi.single_apply]
      split_ifs
      · exact Subring.one_mem _
      · exact Subring.zero_mem _
    have h2 := (hβ _).1 (h _ h1) i
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at h2
    exact h2
  constructor
  · exact fun h => ⟨key x h, key _ ((St β).inv_mem h)⟩
  · rintro ⟨h1, h2⟩
    have a1 := key2 x h1
    have a2 := key2 x⁻¹ h2
    let M : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E) := fun i j => ⟨_, a1 i j⟩
    let M' : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E) := fun i j => ⟨_, a2 i j⟩
    have hM : (Formalism.L2.Herm.intAf F E).subtype.mapMatrix M = (β⁻¹ * x * β).1 := rfl
    have hM' : (Formalism.L2.Herm.intAf F E).subtype.mapMatrix M' = (β⁻¹ * x⁻¹ * β).1 := rfl
    have inj : Function.Injective ((Formalism.L2.Herm.intAf F E).subtype.mapMatrix (m := Fin n)) := by
      intro A B h
      ext i j
      exact congrFun (congrFun h i) j
    have p1 : M * M' = 1 := inj (by
      rw [map_mul, map_one, hM, hM', ← Units.val_mul]; simp [mul_assoc])
    have p2 : M' * M = 1 := inj (by
      rw [map_mul, map_one, hM, hM', ← Units.val_mul]; simp [mul_assoc])
    refine ⟨⟨M, M', p1, p2⟩, ?_⟩
    have : intGL F E n ⟨M, M', p1, p2⟩ = β⁻¹ * x * β := Units.ext hM
    show β * intGL F E n ⟨M, M', p1, p2⟩ * β⁻¹ = x
    rw [this]; group

/- English proof (translation)
Introduce `y hy`. Establish `h1 : (M - 1) *ᵥ ((N : R) • y) ∈ H₁`. Rewrite using `[Matrix.sub_mulVec, Matrix.one_mulVec]`. Conclude with `H₁.sub_mem (h _ (h01 y hy)) (h01 y hy)`. Establish `h2` using `H₀.smul_mem (u * u) (h10 _ h1)`.

Establish `e : M *ᵥ y = y + (u * u) • (N : R) • (M - 1) *ᵥ ((N : R) • y)`. Establish `: (M - 1) *ᵥ y = (u * u) • (N : R) • (M - 1) *ᵥ ((N : R) • y)` using `by conv_lhs => rw [← hM, ← hM]`. Rewrite using `[Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.mulVec_smul, Subring.smul_def, smul_smul, smul_smul, smul_smul]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← this, Matrix.sub_mulVec, Matrix.one_mulVec]`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Conclude with `H₀.add_mem hy h2`.
-/
theorem stab_transfer {R : Type} [CommRing R] {S : Subring R} (H₀ H₁ : Submodule S (Fin n → R)) (N : ℕ) (u : S)
    (h01 : ∀ y ∈ H₀, (N : R) • y ∈ H₁) (h10 : ∀ y ∈ H₁, (N : R) • y ∈ H₀) (M : Matrix (Fin n) (Fin n) R)
    (hM : ((u : R) * N) • (M - 1) = M - 1) (h : ∀ y ∈ H₁, M *ᵥ y ∈ H₁) : ∀ y ∈ H₀, M *ᵥ y ∈ H₀ := by
  intro y hy
  have h1 : (M - 1) *ᵥ ((N : R) • y) ∈ H₁ := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    exact H₁.sub_mem (h _ (h01 y hy)) (h01 y hy)
  have h2 := H₀.smul_mem (u * u) (h10 _ h1)
  have e : M *ᵥ y = y + (u * u) • (N : R) • (M - 1) *ᵥ ((N : R) • y) := by
    have : (M - 1) *ᵥ y = (u * u) • (N : R) • (M - 1) *ᵥ ((N : R) • y) := by
      conv_lhs => rw [← hM, ← hM]
      rw [Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.mulVec_smul, Subring.smul_def, smul_smul, smul_smul, smul_smul]
      congr 1
      push_cast; ring
    rw [← this, Matrix.sub_mulVec, Matrix.one_mulVec]; abel
  rw [e]; exact H₀.add_mem hy h2

/- English proof (translation)
Introduce `y hy`. Use `Submodule.span_induction (p := fun y _ => (N : E ⊗[F] Formalism.L2.Herm.Af F) • y ∈ Formalism.L2.Herm.hatL (F := F) Λ') ?_ ?_ ?_ ?_ hy` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Use `Submodule.subset_span ⟨_, h x hx, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Introduce `a b _ _ ha hb`. Rewrite using `[smul_add]`. Conclude with `Submodule.add_mem _ ha hb`.

Introduce `c a _ ha`. Rewrite using `[smul_comm]`. Conclude with `Submodule.smul_mem _ c ha`.
-/
theorem hatL_smul (Λ Λ' : Submodule (𝓞 E) (Fin n → E)) (N : ℕ) (h : ∀ x ∈ Λ, (N : E) • x ∈ Λ') :
    ∀ y ∈ Formalism.L2.Herm.hatL (F := F) Λ, (N : E ⊗[F] Formalism.L2.Herm.Af F) • y ∈ Formalism.L2.Herm.hatL (F := F) Λ' := by
  intro y hy
  refine Submodule.span_induction
    (p := fun y _ => (N : E ⊗[F] Formalism.L2.Herm.Af F) • y ∈ Formalism.L2.Herm.hatL (F := F) Λ') ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨x, hx, rfl⟩
    refine Submodule.subset_span ⟨_, h x hx, ?_⟩
    funext i
    simp
  · simp
  · intro a b _ _ ha hb
    rw [smul_add]; exact Submodule.add_mem _ ha hb
  · intro c a _ ha
    rw [smul_comm]; exact Submodule.smul_mem _ c ha

variable (F E) in

def swp : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E →+* E ⊗[F] Formalism.L2.Herm.Af F :=
  (Algebra.TensorProduct.comm F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) E).toAlgHom.toRingHom

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem swp_tmul (a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) (x : E) :
    swp F E (a ⊗ₜ[F] x) = x ⊗ₜ[F] a := rfl

/- English proof (translation)
The claim follows from `(Algebra.TensorProduct.comm F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) E).bijective`.
-/
theorem swp_bij : Function.Bijective (swp F E) :=
  (Algebra.TensorProduct.comm F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) E).bijective

/- English proof (translation)
The claim follows from `Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)`.
-/
theorem one_tmul_mem {a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F} (ha : a ∈ Formalism.MainNotions.StandardLattice.intAf F) :
    (1 : E) ⊗ₜ[F] a ∈ Formalism.L2.Herm.intAf F E :=
  Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)

/- English proof (translation)
Use `AddSubgroup.closure_induction (p := fun z _ => swp F E z ∈ Formalism.L2.Herm.intAf F E) ?_ ?_ ?_ ?_ hz` and prove the remaining obligations. Introduce and unpack `_ ⟨a, ha, x, rfl⟩`. Establish `: swp F E (a ⊗ₜ[F] (x : E)) = ((oToS F E x : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) * ((1 : E) ⊗ₜ[F] a)`. Rewrite using `[oToS_coe, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]`. Both sides reduce to the same expression.

Rewrite using `[this]`. Conclude with `Subring.mul_mem _ (oToS F E x).2 (one_tmul_mem ha)`. Rewrite using `[map_zero]`. Conclude with `Subring.zero_mem _`. Introduce `a b _ _ ha hb`.

Rewrite using `[map_add]`. Conclude with `Subring.add_mem _ ha hb`. Introduce `a _ ha`. Rewrite using `[map_neg]`. Conclude with `Subring.neg_mem _ ha`.
-/
theorem swp_int {z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E}
    (hz : z ∈ AddSubgroup.closure {y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E |
      ∃ a ∈ Formalism.MainNotions.StandardLattice.intAf F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)}) :
    swp F E z ∈ Formalism.L2.Herm.intAf F E := by
  refine AddSubgroup.closure_induction (p := fun z _ => swp F E z ∈ Formalism.L2.Herm.intAf F E)
    ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨a, ha, x, rfl⟩
    have : swp F E (a ⊗ₜ[F] (x : E)) =
        ((oToS F E x : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) * ((1 : E) ⊗ₜ[F] a) := by
      rw [oToS_coe, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]; rfl
    rw [this]
    exact Subring.mul_mem _ (oToS F E x).2 (one_tmul_mem ha)
  · rw [map_zero]; exact Subring.zero_mem _
  · intro a b _ _ ha hb
    rw [map_add]; exact Subring.add_mem _ ha hb
  · intro a _ ha
    rw [map_neg]; exact Subring.neg_mem _ ha

/- English proof (translation)
Use `set H := Formalism.MainNotions.StandardLattice.latHat F E (Λ : Set (Fin n → E)) with hH`. Prove the components needed by the constructor for the conclusion. Introduce `hy`. Use `AddSubgroup.closure_induction (p := fun y _ => (fun i => swp F E (y i)) ∈ Formalism.L2.Herm.hatL (F := F) Λ) ?_ ?_ ?_ ?_ hy` and prove the remaining obligations. Introduce and unpack `_ ⟨a, ha, x, hx, rfl⟩`.

Establish `h1 : (fun i => Formalism.UG.inclE (F` using `F) (Formalism.L2.Herm.Af F) (x i)) ∈ Formalism.L2.Herm.hatL (F := F) Λ := Submodule.subset_span ⟨x, hx, rfl⟩`. Establish `h2` using `Submodule.smul_mem _ (⟨_, one_tmul_mem ha⟩ : Formalism.L2.Herm.intAf F E) h1`. Use `h2 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Use `show x i ⊗ₜ[F] a = ((1 : E) ⊗ₜ[F] a) * (x i ⊗ₜ[F] 1)`.

Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]`. Simplify using `only [Pi.zero_apply, map_zero]`. Conclude with `Submodule.zero_mem _`. Introduce `a b _ _ ha hb`. Simplify using `only [Pi.add_apply, map_add]`.

Conclude with `Submodule.add_mem _ ha hb`. Introduce `a _ ha`. Simplify using `only [Pi.neg_apply, map_neg]`. Conclude with `Submodule.neg_mem _ ha`. Establish `gen : ∀ (b : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) (_ : b ∈ Formalism.MainNotions.StandardLattice.intAf F) (c : 𝓞 E), ∀ y ∈ H, (b ⊗ₜ[F] (c : E)) • y ∈ H`.

Introduce `b hb c y hy`. Use `AddSubgroup.closure_induction (p := fun y _ => (b ⊗ₜ[F] (c : E)) • y ∈ H) ?_ ?_ ?_ ?_ hy` and prove the remaining obligations. Introduce and unpack `_ ⟨a, ha, x, hx, rfl⟩`. Use `AddSubgroup.subset_closure ⟨b * a, fun w => ?_, c • x, Λ.smul_mem c hx, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul]`.

Conclude with `mul_mem (hb w) (ha w)`. Use function extensionality and compare the values at `i show (b ⊗ₜ[F] (c : E)) * (a ⊗ₜ[F] x i) = _`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul]`. Both sides reduce to the same expression. Rewrite using `[smul_zero]`.

Conclude with `zero_mem _`. Introduce `a a' _ _ ha ha'`. Rewrite using `[smul_add]`. Conclude with `add_mem ha ha'`. Introduce `a _ ha`.

Rewrite using `[smul_neg]`. Conclude with `neg_mem ha`. Establish `one_int : (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) ∈ Formalism.MainNotions.StandardLattice.intAf F` using `fun v => by`. Rewrite using `[map_one]`. Conclude with `one_mem _`.

Establish `stab : ∀ s ∈ Formalism.L2.Herm.intAf F E, ∀ t, swp F E t = s → ∀ y ∈ H, t • y ∈ H`. Introduce `s hs`. Use `Subring.closure_induction (p := fun s _ => ∀ t, swp F E t = s → ∀ y ∈ H, t • y ∈ H) ?_ ?_ ?_ ?_ ?_ ?_ hs` and prove the remaining obligations. Introduce and unpack `_ (⟨⟨_, c, rfl⟩, rfl⟩ | ⟨b, rfl⟩) t ht`. Establish `: t = (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) ⊗ₜ[F] (c : E)` using `swp_bij.1 ht`.

Rewrite using `[this]`. Conclude with `gen 1 one_int c`. Establish `: t = (b : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) ⊗ₜ[F] ((1 : 𝓞 E) : E)` using `swp_bij.1 ht`. Rewrite using `[this]`. Conclude with `gen b b.2 1`.

Introduce `t ht y _`. Establish `: t = 0` using `swp_bij.1 (by rw [ht, map_zero])`. Rewrite using `[this, zero_smul]`. Conclude with `zero_mem _`. Introduce `t ht y hy`.

Establish `: t = 1` using `swp_bij.1 (by rw [ht, map_one])`. Rewrite using `[this, one_smul]`. Conclude with `hy`. Introduce `a b _ _ ha hb t ht y hy`. Take `⟨a', rfl⟩` from `swp_bij.2 a`.

Take `⟨b', rfl⟩` from `swp_bij.2 b`. Establish `: t = a' + b'` using `swp_bij.1 (by rw [ht, map_add])`. Rewrite using `[this, add_smul]`. Conclude with `add_mem (ha _ rfl y hy) (hb _ rfl y hy)`. Introduce `a _ ha t ht y hy`.

Take `⟨a', rfl⟩` from `swp_bij.2 a`. Establish `: t = -a'` using `swp_bij.1 (by rw [ht, map_neg])`. Rewrite using `[this, neg_smul]`. Conclude with `neg_mem (ha _ rfl y hy)`. Introduce `a b _ _ ha hb t ht y hy`.

Take `⟨a', rfl⟩` from `swp_bij.2 a`. Take `⟨b', rfl⟩` from `swp_bij.2 b`. Establish `: t = a' * b'` using `swp_bij.1 (by rw [ht, map_mul])`. Rewrite using `[this, mul_smul]`. Conclude with `ha _ rfl _ (hb _ rfl y hy)`.

Establish `main : ∀ z ∈ Formalism.L2.Herm.hatL (F` using `F) Λ, ∀ y, (fun i => swp F E (y i)) = z → y ∈ H := by`. Introduce `z hz`. Use `Submodule.span_induction (p := fun z _ => ∀ y, (fun i => swp F E (y i)) = z → y ∈ H) ?_ ?_ ?_ ?_ hz` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩ y hy`. Use `AddSubgroup.subset_closure ⟨1, one_int, x, hx, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `i`. Conclude with `swp_bij.1 (congrFun hy i)`. Introduce `y hy`. Establish `: y = 0` using `funext fun i => swp_bij.1 (by rw [congrFun hy i]; simp)`. Rewrite using `[this]`.

Conclude with `zero_mem _`. Introduce `a b _ _ ha hb y hy choose a' ha' using fun i => swp_bij.2 (a i) choose b' hb' using fun i => swp_bij.2 (b i)`. Establish `: y = a' + b'` using `funext fun i => swp_bij.1 (by`. Rewrite using `[congrFun hy i, Pi.add_apply, Pi.add_apply, map_add, ha', hb'])`. Rewrite using `[this]`.

Conclude with `add_mem (ha _ (funext ha')) (hb _ (funext hb'))`. Introduce `c a _ ha y hy choose a' ha' using fun i => swp_bij.2 (a i)`. Take `⟨t, ht⟩` from `swp_bij.2 (c : E ⊗[F] Formalism.L2.Herm.Af F)`. Establish `: y = t • a'` using `funext fun i => swp_bij.1 (by`. Rewrite using `[congrFun hy i, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, map_mul, ha', ht]`.

Use the proof step `rfl)`. Rewrite using `[this]`. Conclude with `stab _ c.2 t ht _ (ha _ (funext ha'))`. Conclude with `fun h => main _ h y rfl`.
-/
theorem latHat_iff (Λ : Submodule (𝓞 E) (Fin n → E))
    (y : Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) :
    y ∈ Formalism.MainNotions.StandardLattice.latHat F E (Λ : Set (Fin n → E)) ↔
      (fun i => swp F E (y i)) ∈ Formalism.L2.Herm.hatL (F := F) Λ := by
  set H := Formalism.MainNotions.StandardLattice.latHat F E (Λ : Set (Fin n → E)) with hH
  constructor
  · intro hy
    refine AddSubgroup.closure_induction
      (p := fun y _ => (fun i => swp F E (y i)) ∈ Formalism.L2.Herm.hatL (F := F) Λ) ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨a, ha, x, hx, rfl⟩
      have h1 : (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x i)) ∈
          Formalism.L2.Herm.hatL (F := F) Λ := Submodule.subset_span ⟨x, hx, rfl⟩
      have h2 := Submodule.smul_mem _ (⟨_, one_tmul_mem ha⟩ : Formalism.L2.Herm.intAf F E) h1
      convert h2 using 1
      funext i
      show x i ⊗ₜ[F] a = ((1 : E) ⊗ₜ[F] a) * (x i ⊗ₜ[F] 1)
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    · simp only [Pi.zero_apply, map_zero]; exact Submodule.zero_mem _
    · intro a b _ _ ha hb
      simp only [Pi.add_apply, map_add]; exact Submodule.add_mem _ ha hb
    · intro a _ ha
      simp only [Pi.neg_apply, map_neg]; exact Submodule.neg_mem _ ha
  · have gen : ∀ (b : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) (_ : b ∈ Formalism.MainNotions.StandardLattice.intAf F) (c : 𝓞 E), ∀ y ∈ H,
        (b ⊗ₜ[F] (c : E)) • y ∈ H := by
      intro b hb c y hy
      refine AddSubgroup.closure_induction (p := fun y _ => (b ⊗ₜ[F] (c : E)) • y ∈ H) ?_ ?_ ?_ ?_ hy
      · rintro _ ⟨a, ha, x, hx, rfl⟩
        refine AddSubgroup.subset_closure ⟨b * a, fun w => ?_, c • x, Λ.smul_mem c hx, ?_⟩
        · rw [map_mul]; exact mul_mem (hb w) (ha w)
        · funext i
          show (b ⊗ₜ[F] (c : E)) * (a ⊗ₜ[F] x i) = _
          rw [Algebra.TensorProduct.tmul_mul_tmul]; rfl
      · rw [smul_zero]; exact zero_mem _
      · intro a a' _ _ ha ha'
        rw [smul_add]; exact add_mem ha ha'
      · intro a _ ha
        rw [smul_neg]; exact neg_mem ha
    have one_int : (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) ∈ Formalism.MainNotions.StandardLattice.intAf F := fun v => by
      rw [map_one]; exact one_mem _
    have stab : ∀ s ∈ Formalism.L2.Herm.intAf F E, ∀ t, swp F E t = s → ∀ y ∈ H, t • y ∈ H := by
      intro s hs
      refine Subring.closure_induction (p := fun s _ => ∀ t, swp F E t = s → ∀ y ∈ H, t • y ∈ H)
        ?_ ?_ ?_ ?_ ?_ ?_ hs
      · rintro _ (⟨⟨_, c, rfl⟩, rfl⟩ | ⟨b, rfl⟩) t ht
        · have : t = (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) ⊗ₜ[F] (c : E) := swp_bij.1 ht
          rw [this]; exact gen 1 one_int c
        · have : t = (b : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) ⊗ₜ[F] ((1 : 𝓞 E) : E) :=
            swp_bij.1 ht
          rw [this]; exact gen b b.2 1
      · intro t ht y _
        have : t = 0 := swp_bij.1 (by rw [ht, map_zero])
        rw [this, zero_smul]; exact zero_mem _
      · intro t ht y hy
        have : t = 1 := swp_bij.1 (by rw [ht, map_one])
        rw [this, one_smul]; exact hy
      · intro a b _ _ ha hb t ht y hy
        obtain ⟨a', rfl⟩ := swp_bij.2 a
        obtain ⟨b', rfl⟩ := swp_bij.2 b
        have : t = a' + b' := swp_bij.1 (by rw [ht, map_add])
        rw [this, add_smul]; exact add_mem (ha _ rfl y hy) (hb _ rfl y hy)
      · intro a _ ha t ht y hy
        obtain ⟨a', rfl⟩ := swp_bij.2 a
        have : t = -a' := swp_bij.1 (by rw [ht, map_neg])
        rw [this, neg_smul]; exact neg_mem (ha _ rfl y hy)
      · intro a b _ _ ha hb t ht y hy
        obtain ⟨a', rfl⟩ := swp_bij.2 a
        obtain ⟨b', rfl⟩ := swp_bij.2 b
        have : t = a' * b' := swp_bij.1 (by rw [ht, map_mul])
        rw [this, mul_smul]; exact ha _ rfl _ (hb _ rfl y hy)
    have main : ∀ z ∈ Formalism.L2.Herm.hatL (F := F) Λ, ∀ y, (fun i => swp F E (y i)) = z → y ∈ H := by
      intro z hz
      refine Submodule.span_induction (p := fun z _ => ∀ y, (fun i => swp F E (y i)) = z → y ∈ H) ?_ ?_ ?_ ?_ hz
      · rintro _ ⟨x, hx, rfl⟩ y hy
        refine AddSubgroup.subset_closure ⟨1, one_int, x, hx, ?_⟩
        funext i
        exact swp_bij.1 (congrFun hy i)
      · intro y hy
        have : y = 0 := funext fun i => swp_bij.1 (by rw [congrFun hy i]; simp)
        rw [this]; exact zero_mem _
      · intro a b _ _ ha hb y hy
        choose a' ha' using fun i => swp_bij.2 (a i)
        choose b' hb' using fun i => swp_bij.2 (b i)
        have : y = a' + b' := funext fun i => swp_bij.1 (by
          rw [congrFun hy i, Pi.add_apply, Pi.add_apply, map_add, ha', hb'])
        rw [this]; exact add_mem (ha _ (funext ha')) (hb _ (funext hb'))
      · intro c a _ ha y hy
        choose a' ha' using fun i => swp_bij.2 (a i)
        obtain ⟨t, ht⟩ := swp_bij.2 (c : E ⊗[F] Formalism.L2.Herm.Af F)
        have : y = t • a' := funext fun i => swp_bij.1 (by
          rw [congrFun hy i, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, map_mul, ha', ht]; rfl)
        rw [this]; exact stab _ c.2 t ht _ (ha _ (funext ha'))
    exact fun h => main _ h y rfl

end General

section Adelic

variable {D : D7}

def finSw (D : D7) : Formalism.L2.Theta.AE D →+* EAf D := (swapAE D).comp (finPart D)

/- English proof (translation)
The claim follows from `swp_int hz`.
-/
theorem swapAE_int {z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E} (hz : z ∈ intAE D) :
    swapAE D z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := swp_int hz

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem finE_val (V : HSp D) (g : GA D V) : (finE V g).1 = (Formalism.L2.Theta.mt V g).map (finSw D) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem finSw_incA (x : D.host.E) :
    finSw D (incA D x) = Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) x := rfl

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a x => rfl`. Consider the case `add a b ha hb => rw [RingHom.map_add, RingHom.map_add, ha, hb, RingHom.map_add, RingHom.map_add]`.
-/
theorem finSw_cA (z : Formalism.L2.Theta.AE D) :
    finSw D (cA D z) = Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) (finSw D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add a b ha hb => rw [RingHom.map_add, RingHom.map_add, ha, hb, RingHom.map_add, RingHom.map_add]

/- English proof (translation)
Establish `h : Formalism.UG.cT (cA D) (Formalism.L2.Theta.mt V g) * V.gram.map (incA D) * Formalism.L2.Theta.mt V g = V.gram.map (incA D)` using `(show HR (AF D.host.F) D.sp.cm.sig V.gram from g).2`. Establish `h2` using `congrArg (fun M => Matrix.map M (finSw D)) h`. Simplify using `only [Matrix.map_mul] at h2`. Use `show Formalism.UG.cT _ (finE V g).1 * _ * (finE V g).1 = _`. Rewrite using `[finE_val]`.

Establish `e1 : (Formalism.UG.cT (cA D) (Formalism.L2.Theta.mt V g)).map (finSw D) = Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) ((Formalism.L2.Theta.mt V g).map (finSw D))`. Use extensionality with `i j`. Conclude with `finSw_cA _`. Rewrite `h2` using `[e1]`. Conclude with `h2`.
-/
theorem finE_mem_UA (V : HSp D) (g : GA D V) : finE V g ∈ UA D.sp.cm V.gram := by
  have h : Formalism.UG.cT (cA D) (Formalism.L2.Theta.mt V g) * V.gram.map (incA D) * Formalism.L2.Theta.mt V g =
      V.gram.map (incA D) := (show HR (AF D.host.F) D.sp.cm.sig V.gram from g).2
  have h2 := congrArg (fun M => Matrix.map M (finSw D)) h
  simp only [Matrix.map_mul] at h2
  show Formalism.UG.cT _ (finE V g).1 * _ * (finE V g).1 = _
  rw [finE_val]
  have e1 : (Formalism.UG.cT (cA D) (Formalism.L2.Theta.mt V g)).map (finSw D) =
      Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) ((Formalism.L2.Theta.mt V g).map (finSw D)) := by
    ext i j
    exact finSw_cA _
  rw [e1] at h2
  exact h2

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨D.sp.cm.sig (y : D.host.E), (y.isIntegral_coe).map ((D.sp.cm.sig : D.host.E →+* D.host.E).toIntAlgHom)⟩, rfl⟩`.
-/
theorem exists_conj (y : 𝓞 D.host.E) : ∃ y' : 𝓞 D.host.E, (y' : D.host.E) = star (y : D.host.E) :=
  ⟨⟨D.sp.cm.sig (y : D.host.E), (y.isIntegral_coe).map ((D.sp.cm.sig : D.host.E →+* D.host.E).toIntAlgHom)⟩, rfl⟩

/- English proof (translation)
Establish `: Formalism.L2.Herm.intAf D.host.F D.host.E ≤ (Formalism.L2.Herm.intAf D.host.F D.host.E).comap (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F))`. Use `Subring.closure_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ (⟨⟨_, c, rfl⟩, rfl⟩ | ⟨b, rfl⟩)`. Take `⟨c', hc'⟩` from `exists_conj c`. Use `Subring.subset_closure (Or.inl ⟨⟨_, c', rfl⟩, ?_⟩)` and prove the remaining obligations.

Use `show (c' : D.host.E) ⊗ₜ[D.host.F] _ = star (c : D.host.E) ⊗ₜ[D.host.F] _`. Rewrite using `[hc']`. Both sides reduce to the same expression. Use `Subring.subset_closure (Or.inr ⟨b, ?_⟩) show _ = D.sp.cm.sig 1 ⊗ₜ[D.host.F] _` and prove the remaining obligations. Rewrite using `[map_one]`.

Both sides reduce to the same expression. Conclude with `this hs`.
-/
theorem sigR_int {s : EAf D} (hs : s ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) s ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  have : Formalism.L2.Herm.intAf D.host.F D.host.E ≤
      (Formalism.L2.Herm.intAf D.host.F D.host.E).comap (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) := by
    refine Subring.closure_le.2 ?_
    rintro _ (⟨⟨_, c, rfl⟩, rfl⟩ | ⟨b, rfl⟩)
    · obtain ⟨c', hc'⟩ := exists_conj c
      refine Subring.subset_closure (Or.inl ⟨⟨_, c', rfl⟩, ?_⟩)
      show (c' : D.host.E) ⊗ₜ[D.host.F] _ = star (c : D.host.E) ⊗ₜ[D.host.F] _
      rw [hc']; rfl
    · refine Subring.subset_closure (Or.inr ⟨b, ?_⟩)
      show _ = D.sp.cm.sig 1 ⊗ₜ[D.host.F] _
      rw [map_one]; rfl
  exact this hs

/- English proof (translation)
Establish `y0 : y ≠ 0` using `fun h0 => h1 (h0 ▸ P.asIdeal.zero_mem)`. Establish `y0' : y' ≠ 0` using `fun h0 => h2 (h0 ▸ P.asIdeal.zero_mem)`. Establish `hm : finSw D (f * incA D ((y : D.host.E)⁻¹)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E`. Break down `h with ⟨⟨_, h⟩, rfl⟩ | ⟨rfl, _, h⟩` into its components or cases. Establish `a1` using `swapAE_int (not_not.1 fun hn => h1 ((h y y0).2 hn))`.

Establish `a2` using `sigR_int (swapAE_int (not_not.1 fun hn => h2 ((h y' y0').2 hn)))`. Rewrite using `[add_mul, RingHom.map_add]`. Use `Subring.add_mem _ a1 ?_` and prove the remaining obligations. Establish `: cA D e * incA D ((y : D.host.E)⁻¹) = cA D (e * incA D ((y' : D.host.E)⁻¹))`. Rewrite using `[map_mul]`.

Use `congr 1`. Use `show _ = incA D (star ((y' : D.host.E)⁻¹))`. Rewrite using `[hy', star_inv₀, star_star]`. Rewrite using `[this, finSw_cA]`. Conclude with `a2`.

Conclude with `swapAE_int (not_not.1 fun hn => h1 ((h y y0).2 hn))`. Use `⟨⟨_, hm⟩, ?_⟩` and prove the remaining obligations. Use `show finSw D (f * incA D ((y : D.host.E)⁻¹)) * finSw D (incA D (y : D.host.E)) = _`. Establish `: (y : D.host.E) ≠ 0` using `by simpa using y0`. Rewrite using `[← map_mul, mul_assoc, ← map_mul, inv_mul_cancel₀ this, map_one, mul_one]`.
-/
theorem idem_div_int {P : HeightOneSpectrum (𝓞 D.host.E)} {e f : Formalism.L2.Theta.AE D} (h : IsPrimeIdem P e f)
    (y y' : 𝓞 D.host.E) (hy' : (y' : D.host.E) = star (y : D.host.E)) (h1 : y ∉ P.asIdeal) (h2 : y' ∉ P.asIdeal) :
    ∃ u : Formalism.L2.Herm.intAf D.host.F D.host.E,
      (u : EAf D) * (oToS D.host.F D.host.E y : Formalism.L2.Herm.intAf D.host.F D.host.E) = finSw D f := by
  have y0 : y ≠ 0 := fun h0 => h1 (h0 ▸ P.asIdeal.zero_mem)
  have y0' : y' ≠ 0 := fun h0 => h2 (h0 ▸ P.asIdeal.zero_mem)
  have hm : finSw D (f * incA D ((y : D.host.E)⁻¹)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    rcases h with ⟨⟨_, h⟩, rfl⟩ | ⟨rfl, _, h⟩
    · have a1 := swapAE_int (not_not.1 fun hn => h1 ((h y y0).2 hn))
      have a2 := sigR_int (swapAE_int (not_not.1 fun hn => h2 ((h y' y0').2 hn)))
      rw [add_mul, RingHom.map_add]
      refine Subring.add_mem _ a1 ?_
      have : cA D e * incA D ((y : D.host.E)⁻¹) = cA D (e * incA D ((y' : D.host.E)⁻¹)) := by
        rw [map_mul]
        congr 1
        show _ = incA D (star ((y' : D.host.E)⁻¹))
        rw [hy', star_inv₀, star_star]
      rw [this, finSw_cA]
      exact a2
    · exact swapAE_int (not_not.1 fun hn => h1 ((h y y0).2 hn))
  refine ⟨⟨_, hm⟩, ?_⟩
  show finSw D (f * incA D ((y : D.host.E)⁻¹)) * finSw D (incA D (y : D.host.E)) = _
  have : (y : D.host.E) ≠ 0 := by simpa using y0
  rw [← map_mul, mul_assoc, ← map_mul, inv_mul_cancel₀ this, map_one, mul_one]

/- English proof (translation)
Establish `hd : ∃ d ∈ PP.asIdeal, d ∉ P.asIdeal`. Assume the negation of the conclusion as `hn`. Use `push Not at hn`. Conclude with `h1 (HeightOneSpectrum.ext (PP.isMaximal.eq_of_le P.isPrime.ne_top hn))`. Take `⟨d, hd, hdP⟩` from `hd`.

Unfold `Formalism.IndefR.Lev.IsConjPl at h2`. Use `push Not at h2`. Take `⟨c, hc, hcP⟩` from `h2`. Take `⟨c', hc'⟩` from `exists_conj c`. Take `⟨d', hd'⟩` from `exists_conj d`.

Establish `hc'P : c' ∉ P.asIdeal` using `fun h => hcP c' h hc'`. Distinguish the cases in `a1 : d' ∈ P.asIdeal`. Distinguish the cases in `a2 : c ∈ P.asIdeal`. Use `⟨c + d, c' + d', add_mem hc hd, ?_, fun h => hdP ?_, fun h => hc'P ?_⟩` and prove the remaining obligations. Use `push_cast`.

Rewrite using `[star_add]`. Conclude with `congrArg₂ (· + ·) hc' hd'`. Simplify using `using sub_mem h a2`. Simplify using `using sub_mem h a1`. Conclude with `⟨c, c', hc, hc', a2, hc'P⟩`.

Conclude with `⟨d, d', hd, hd', hdP, a1⟩`.
-/
theorem exists_sep {P PP : HeightOneSpectrum (𝓞 D.host.E)} (h1 : PP ≠ P) (h2 : ¬ Formalism.IndefR.Lev.IsConjPl PP P) :
    ∃ y y' : 𝓞 D.host.E, y ∈ PP.asIdeal ∧ (y' : D.host.E) = star (y : D.host.E) ∧ y ∉ P.asIdeal ∧ y' ∉ P.asIdeal := by
  have hd : ∃ d ∈ PP.asIdeal, d ∉ P.asIdeal := by
    by_contra hn
    push Not at hn
    exact h1 (HeightOneSpectrum.ext (PP.isMaximal.eq_of_le P.isPrime.ne_top hn))
  obtain ⟨d, hd, hdP⟩ := hd
  unfold Formalism.IndefR.Lev.IsConjPl at h2
  push Not at h2
  obtain ⟨c, hc, hcP⟩ := h2
  obtain ⟨c', hc'⟩ := exists_conj c
  obtain ⟨d', hd'⟩ := exists_conj d
  have hc'P : c' ∉ P.asIdeal := fun h => hcP c' h hc'
  by_cases a1 : d' ∈ P.asIdeal
  · by_cases a2 : c ∈ P.asIdeal
    · refine ⟨c + d, c' + d', add_mem hc hd, ?_, fun h => hdP ?_, fun h => hc'P ?_⟩
      · push_cast; rw [star_add]; exact congrArg₂ (· + ·) hc' hd'
      · simpa using sub_mem h a2
      · simpa using sub_mem h a1
    · exact ⟨c, c', hc, hc', a2, hc'P⟩
  · exact ⟨d, d', hd, hd', hdP, a1⟩

end Adelic

section Main

variable {D : D7}

/- English proof (translation)
Establish `e : M.map ψ - 1 = (M - 1).map ψ`. Rewrite using `[Matrix.map_sub _ (map_sub ψ), Matrix.map_one _ (map_zero ψ) (map_one ψ)]`. Rewrite using `[e]`. Use extensionality with `i j`. Use `show ψ f * ψ ((M - 1) i j) = ψ ((M - 1) i j)`.

Rewrite using `[← map_mul, h]`.
-/
theorem supp_gen {R T : Type} [CommRing R] [CommRing T] {n : ℕ} (ψ : R →+* T) (f : R) (M : Matrix (Fin n) (Fin n) R)
    (h : ∀ i j, f * (M - 1) i j = (M - 1) i j) : ψ f • (M.map ψ - 1) = M.map ψ - 1 := by
  have e : M.map ψ - 1 = (M - 1).map ψ := by
    rw [Matrix.map_sub _ (map_sub ψ), Matrix.map_one _ (map_zero ψ) (map_one ψ)]
  rw [e]
  ext i j
  show ψ f * ψ ((M - 1) i j) = ψ ((M - 1) i j)
  rw [← map_mul, h]

/- English proof (translation)
The claim follows from `supp_gen (finSw D) f _ h`.
-/
theorem supp_fin (V : HSp D) {f : Formalism.L2.Theta.AE D} {g : GA D V} (h : SuppF V f g) :
    finSw D f • ((finE V g).1 - 1) = (finE V g).1 - 1 := supp_gen (finSw D) f _ h

def L0sub (V : HSp D) : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) where
  carrier := L0c D V
  add_mem' := by
    intro a b ha hb
    show ∑ i, (a i + b i) • V.frame i ∈ V.L0
    simp only [add_smul, Finset.sum_add_distrib]
    exact V.L0.add_mem ha hb
  zero_mem' := by
    show ∑ i, (0 : D.host.E) • V.frame i ∈ V.L0
    simp
  smul_mem' := by
    intro c a ha
    show ∑ i, (c • a i) • V.frame i ∈ V.L0
    simp only [smul_assoc, ← Finset.smul_sum]
    exact V.L0.smul_mem c ha

/- English proof (translation)
Establish `e : ∀ (x : GL (Fin n) R) (y : Fin n → R), (fun i => ψ ((x.1 *ᵥ y) i)) = (Formalism.UG.bc ψ x).1 *ᵥ fun i => ψ (y i)` using `fun x y =>`. Use function extensionality and compare the values at `fun i => RingHom.map_mulVec ψ x.1 y i`. Establish `s : ∀ z : Fin n → T, ∃ y : Fin n → R, z = fun i => ψ (y i)` using `fun z => by choose y hy using fun i => hψ (z i)`. Conclude with `⟨y, funext fun i => (hy i).symm⟩`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Prove the components needed by the constructor for the conclusion. Introduce `z hz`. Take `⟨y, rfl⟩` from `s z`. Rewrite using `[← e, ← hAB, ← h, hAB]`.

Conclude with `hz`. Introduce `z hz`. Take `⟨y, rfl⟩` from `s z`. Rewrite using `[← map_inv, ← e, ← hAB, h, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec, hAB]`. Conclude with `hz`.

Introduce and unpack `⟨h1, h2⟩ y`. Rewrite using `[hAB, hAB, e]`. Use `⟨h1 _, fun h => ?_⟩` and prove the remaining obligations. Use `h2 _ h` as an intermediate fact. Rewrite `this` using `[Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]`. Then use the resulting hypothesis.
-/
theorem stab_gen {R T : Type} [CommRing R] [CommRing T] {n : ℕ} (ψ : R →+* T) (hψ : Function.Surjective ψ)
    (A : Set (Fin n → R)) (B : Set (Fin n → T)) (hAB : ∀ y, y ∈ A ↔ (fun i => ψ (y i)) ∈ B) (x : GL (Fin n) R) :
    (∀ y, y ∈ A ↔ x.1 *ᵥ y ∈ A) ↔
      (∀ y ∈ B, (Formalism.UG.bc ψ x).1 *ᵥ y ∈ B) ∧ ∀ y ∈ B, ((Formalism.UG.bc ψ x)⁻¹).1 *ᵥ y ∈ B := by
  have e : ∀ (x : GL (Fin n) R) (y : Fin n → R),
      (fun i => ψ ((x.1 *ᵥ y) i)) = (Formalism.UG.bc ψ x).1 *ᵥ fun i => ψ (y i) := fun x y =>
    funext fun i => RingHom.map_mulVec ψ x.1 y i
  have s : ∀ z : Fin n → T, ∃ y : Fin n → R, z = fun i => ψ (y i) := fun z => by
    choose y hy using fun i => hψ (z i)
    exact ⟨y, funext fun i => (hy i).symm⟩
  constructor
  · intro h
    constructor
    · intro z hz
      obtain ⟨y, rfl⟩ := s z
      rw [← e, ← hAB, ← h, hAB]; exact hz
    · intro z hz
      obtain ⟨y, rfl⟩ := s z
      rw [← map_inv, ← e, ← hAB, h, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec, hAB]; exact hz
  · rintro ⟨h1, h2⟩ y
    rw [hAB, hAB, e]
    refine ⟨h1 _, fun h => ?_⟩
    have := h2 _ h
    rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this

/- English proof (translation)
Use `stab_gen (swp D.host.F D.host.E) swp_bij.2 (Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0sub V : Set (Fin V.rank → D.host.E))) (Formalism.L2.Herm.hatL (F := D.host.F) (L0sub V)) (latHat_iff (L0sub V)) (finHom V g)` as an intermediate fact. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2, _⟩`. Conclude with `⟨h1, this.1 h2⟩`. Introduce and unpack `⟨h1, h2⟩`.

Conclude with `⟨h1, this.2 h2, fun v hv => absurd hv (Finset.notMem_empty v)⟩`.
-/
theorem ksph_iff (V : HSp D) (g : GA D V) : g ∈ KsphC V ∅ ↔ g ∈ GfC V ∧
    (∀ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (L0sub V),
      (finE V g).1 *ᵥ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (L0sub V)) ∧
    ∀ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (L0sub V),
      ((finE V g)⁻¹).1 *ᵥ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (L0sub V) := by
  have := stab_gen (swp D.host.F D.host.E) swp_bij.2
    (Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0sub V : Set (Fin V.rank → D.host.E)))
    (Formalism.L2.Herm.hatL (F := D.host.F) (L0sub V)) (latHat_iff (L0sub V)) (finHom V g)
  constructor
  · rintro ⟨h1, h2, _⟩
    exact ⟨h1, this.1 h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, this.2 h2, fun v hv => absurd hv (Finset.notMem_empty v)⟩

/- English proof (translation)
Establish `e1 : (u : R) • B = (u : R) • 1`. Rewrite using `[← sub_eq_zero, ← smul_sub, ← hB, smul_smul, mul_sub, mul_one, hu, sub_self, zero_smul]`. Establish `e2 : (u : R) • K = (u : R) • A`. Break down `hK with rfl | rfl` into its components or cases. Rewrite using `[← Matrix.mul_smul, e1, Matrix.mul_smul, Matrix.mul_one]`.

Rewrite using `[← Matrix.smul_mul, e1, Matrix.smul_mul, Matrix.one_mul]`. Establish `e3 : A = 1 + (u : R) • (K - 1)`. Rewrite using `[smul_sub, e2, ← smul_sub, hA]`. Normalize the expressions using the abelian group laws. Introduce `y hy`.

Rewrite using `[e3, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]`. Conclude with `H.add_mem hy (H.smul_mem u (H.sub_mem (h y hy) hy))`.
-/
theorem comp_gen {R : Type} [CommRing R] {S : Subring R} {n : ℕ} (H : Submodule S (Fin n → R)) (u : S)
    (hu : (u : R) * u = u) (A B K : Matrix (Fin n) (Fin n) R) (hA : (u : R) • (A - 1) = A - 1)
    (hB : (1 - (u : R)) • (B - 1) = B - 1) (hK : K = A * B ∨ K = B * A) (h : ∀ y ∈ H, K *ᵥ y ∈ H) :
    ∀ y ∈ H, A *ᵥ y ∈ H := by
  have e1 : (u : R) • B = (u : R) • 1 := by
    rw [← sub_eq_zero, ← smul_sub, ← hB, smul_smul, mul_sub, mul_one, hu, sub_self, zero_smul]
  have e2 : (u : R) • K = (u : R) • A := by
    rcases hK with rfl | rfl
    · rw [← Matrix.mul_smul, e1, Matrix.mul_smul, Matrix.mul_one]
    · rw [← Matrix.smul_mul, e1, Matrix.smul_mul, Matrix.one_mul]
  have e3 : A = 1 + (u : R) • (K - 1) := by
    rw [smul_sub, e2, ← smul_sub, hA]; abel
  intro y hy
  rw [e3, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]
  exact H.add_mem hy (H.smul_mem u (H.sub_mem (h y hy) hy))

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Introduce `D V β Λ N L hB`. Take `⟨hfr, -, -, h01, h10⟩` from `hB`. Prove the components needed by the constructor for the conclusion. Introduce `k _`. Take `⟨n, hn, h⟩` from `isOfFinOrder_iff_pow_eq_one.1 (levFn_finOrd β L (finE V k))`.

Use `⟨n, hn, ?_⟩` and prove the remaining obligations. Unfold `levChi`. Rewrite using `[← Units.val_pow_eq_pow_val, h, Units.val_one]`. Introduce `P e f hP hN hPP`. Take `⟨T1, -, T3, -⟩` from `GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V`.

Take `⟨hff, hcf, hG, -⟩` from `T3 P e f hP`. Take `⟨⟨Lf, hLf⟩, hsplit, -⟩` from `T1 f hff hcf`. Take `⟨⟨Lf', hLf'⟩, -, -⟩` from `T1 (1 - f) (by rw [mul_sub, mul_one, sub_mul, one_mul, hff, sub_self, sub_zero]) (by rw [RingHom.map_sub, RingHom.map_one, hcf])`. Establish `hinv : ∀ g, SuppF V f g → SuppF V f g⁻¹` using `fun g hg => (hLf _).1 (Lf.inv_mem ((hLf _).2 hg))`. Establish `hinv' : ∀ g, SuppF V (1 - f) g → SuppF V (1 - f) g⁻¹` using `fun g hg => (hLf' _).1 (Lf'.inv_mem ((hLf' _).2 hg))`.

Take `⟨u, hu⟩` from `idem_div_int hP N N (by simp) hN hN`. Establish `hu' : (u : EAf D) * (N : EAf D) = finSw D f`. Rewrite using `[← hu, map_natCast]`. Both sides reduce to the same expression. Take `⟨φ, hφ⟩ : ∃ φ : Formalism.L2.Herm.intAf D.host.F D.host.E, (φ : EAf D) = finSw D f` from `⟨u * oToS D.host.F D.host.E N, hu⟩`.

Establish `hres : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → resS D.host.F PP φ = 0`. Introduce `PP h`. Take `⟨y, y', hy, hyy, a1, a2⟩` from `exists_sep (hPP PP h).1 (hPP PP h).2`. Take `⟨w, hw⟩` from `idem_div_int hP y y' hyy a1 a2`. Establish `: φ = w * oToS D.host.F D.host.E y` using `Subtype.ext (hφ.trans hw.symm)`.

Rewrite using `[this, RingHom.map_mul, resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 hy, mul_zero]`. Establish `hred : ∀ g, SuppF V f g → finE V g ∈ St β → ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → redFn β PP (finE V g) = 1` using `fun g hg hS PP h => redFn_eq_one β PP _ hS φ (hres PP h) (hφ ▸ supp_fin V hg)`. Establish `hlev : ∀ g, SuppF V f g → finE V g ∈ St β → g ∈ levG V β L` using `fun g hg hS => ⟨hG g hg, mem_lev_of_red _ _ β L _ (finE_mem_UA V g) hS (hred g hg hS)⟩`. Establish `hSt : ∀ g ∈ levG V β L, finE V g ∈ St β` using `fun g hg => parLev_St (lev_le_parLev hg.2)`. Establish `a01` using `hatL_smul (F := D.host.F) (L0sub V) Λ N h01`.

Establish `a10` using `hatL_smul (F := D.host.F) Λ (L0sub V) N h10`. Use `⟨fun g hg => ?_, fun g hg hs => ?_, fun k hk => ?_⟩` and prove the remaining obligations. Establish `s1` using `supp_fin V hg`. Establish `s2` using `supp_fin V (hinv g hg)`. Rewrite `s2` using `[MonoidHom.map_inv]`.

Rewrite `s1`, `s2` using `[← hu']`. Rewrite using `[ksph_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `(mem_St_iff β Λ hfr _).1 (hSt g h)` as an intermediate fact.

Conclude with `⟨hG g hg, stab_transfer _ _ N u a01 a10 _ s1 this.1, stab_transfer _ _ N u a01 a10 _ s2 this.2⟩`. Introduce and unpack `⟨-, h1, h2⟩`. Conclude with `hlev g hg ((mem_St_iff β Λ hfr _).2 ⟨stab_transfer _ _ N u a10 a01 _ s1 h1, stab_transfer _ _ N u a10 a01 _ s2 h2⟩)`. Unfold `levChi`. Rewrite using `[levFn_eq_one β L _ (hred g hs (hSt g hg)), Units.val_one]`.

Take `⟨k₁, k₂, h1, h2, hk12⟩` from `hsplit k`. Establish `hφφ : (φ : EAf D) * φ = φ` using `by rw [hφ, ← RingHom.map_mul, hff]`. Establish `s1` using `supp_fin V h1`. Establish `s1'` using `supp_fin V (hinv _ h1)`. Establish `s2` using `supp_fin V h2`.

Establish `s2'` using `supp_fin V (hinv' _ h2)`. Rewrite `s1'`, `s2'` using `[MonoidHom.map_inv]`. Rewrite `s2`, `s2'` using `[RingHom.map_sub, RingHom.map_one]`. Rewrite `s1`, `s1'`, `s2`, `s2'` using `[← hφ]`. Establish `hk'` using `(mem_St_iff β Λ hfr _).1 (hSt k hk)`.

Establish `ek : finE V k = finE V k₁ * finE V k₂` using `by rw [hk12, MonoidHom.map_mul]`. Establish `m1 : k₁ ∈ levG V β L` using `hlev _ h1 ((mem_St_iff β Λ hfr _).2 ⟨comp_gen _ φ hφφ _ _ _ s1 s2 (Or.inl (by rw [ek, Units.val_mul])) hk'.1, comp_gen _ φ hφφ _ _ _ s1' s2' (Or.inr (by rw [ek, mul_inv_rev, Units.val_mul])) hk'.2⟩)`. Use `⟨k₁, m1, k₂, ?_, h1, h2, hk12⟩` and prove the remaining obligations. Establish `: k₂ = k₁⁻¹ * k` using `by rw [hk12, inv_mul_cancel_left]`. Rewrite using `[this]`.

Conclude with `Subgroup.mul_mem _ (Subgroup.inv_mem _ m1) hk`.
-/
theorem lev_split : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank), Formalism.IndefR.Lev.IsBaseFrame V β Λ N → (∀ k ∈ Formalism.IndefR.Lev.levG V β L, ∃ n : ℕ, 0 < n ∧ Formalism.IndefR.Lev.levChi V β L k ^ n = 1) ∧ ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) e f, IsPrimeIdem P e f → ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → (∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P) → (∀ g, SuppF V f g → (g ∈ Formalism.IndefR.Lev.levG V β L ↔ g ∈ KsphC V ∅)) ∧ (∀ g ∈ Formalism.IndefR.Lev.levG V β L, SuppF V f g → Formalism.IndefR.Lev.levChi V β L g = 1) ∧ ∀ k ∈ Formalism.IndefR.Lev.levG V β L, ∃ k₁ ∈ Formalism.IndefR.Lev.levG V β L, ∃ k₂ ∈ Formalism.IndefR.Lev.levG V β L, SuppF V f k₁ ∧ SuppF V (1 - f) k₂ ∧ k = k₁ * k₂ := by
  intro D V β Λ N L hB
  obtain ⟨hfr, -, -, h01, h10⟩ := hB
  constructor
  · intro k _
    obtain ⟨n, hn, h⟩ := isOfFinOrder_iff_pow_eq_one.1 (levFn_finOrd β L (finE V k))
    refine ⟨n, hn, ?_⟩
    unfold levChi
    rw [← Units.val_pow_eq_pow_val, h, Units.val_one]
  intro P e f hP hN hPP
  obtain ⟨T1, -, T3, -⟩ := GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V
  obtain ⟨hff, hcf, hG, -⟩ := T3 P e f hP
  obtain ⟨⟨Lf, hLf⟩, hsplit, -⟩ := T1 f hff hcf
  obtain ⟨⟨Lf', hLf'⟩, -, -⟩ := T1 (1 - f) (by rw [mul_sub, mul_one, sub_mul, one_mul, hff, sub_self, sub_zero])
    (by rw [RingHom.map_sub, RingHom.map_one, hcf])
  have hinv : ∀ g, SuppF V f g → SuppF V f g⁻¹ := fun g hg => (hLf _).1 (Lf.inv_mem ((hLf _).2 hg))
  have hinv' : ∀ g, SuppF V (1 - f) g → SuppF V (1 - f) g⁻¹ := fun g hg =>
    (hLf' _).1 (Lf'.inv_mem ((hLf' _).2 hg))
  obtain ⟨u, hu⟩ := idem_div_int hP N N (by simp) hN hN
  have hu' : (u : EAf D) * (N : EAf D) = finSw D f := by
    rw [← hu, map_natCast]; rfl
  obtain ⟨φ, hφ⟩ : ∃ φ : Formalism.L2.Herm.intAf D.host.F D.host.E, (φ : EAf D) = finSw D f :=
    ⟨u * oToS D.host.F D.host.E N, hu⟩
  have hres : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → resS D.host.F PP φ = 0 := by
    intro PP h
    obtain ⟨y, y', hy, hyy, a1, a2⟩ := exists_sep (hPP PP h).1 (hPP PP h).2
    obtain ⟨w, hw⟩ := idem_div_int hP y y' hyy a1 a2
    have : φ = w * oToS D.host.F D.host.E y := Subtype.ext (hφ.trans hw.symm)
    rw [this, RingHom.map_mul, resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 hy, mul_zero]
  have hred : ∀ g, SuppF V f g → finE V g ∈ St β → ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → redFn β PP (finE V g) = 1 :=
    fun g hg hS PP h => redFn_eq_one β PP _ hS φ (hres PP h) (hφ ▸ supp_fin V hg)
  have hlev : ∀ g, SuppF V f g → finE V g ∈ St β → g ∈ levG V β L := fun g hg hS =>
    ⟨hG g hg, mem_lev_of_red _ _ β L _ (finE_mem_UA V g) hS (hred g hg hS)⟩
  have hSt : ∀ g ∈ levG V β L, finE V g ∈ St β := fun g hg => parLev_St (lev_le_parLev hg.2)
  have a01 := hatL_smul (F := D.host.F) (L0sub V) Λ N h01
  have a10 := hatL_smul (F := D.host.F) Λ (L0sub V) N h10
  refine ⟨fun g hg => ?_, fun g hg hs => ?_, fun k hk => ?_⟩
  · have s1 := supp_fin V hg
    have s2 := supp_fin V (hinv g hg)
    rw [MonoidHom.map_inv] at s2
    rw [← hu'] at s1 s2
    rw [ksph_iff]
    constructor
    · intro h
      have := (mem_St_iff β Λ hfr _).1 (hSt g h)
      exact ⟨hG g hg, stab_transfer _ _ N u a01 a10 _ s1 this.1, stab_transfer _ _ N u a01 a10 _ s2 this.2⟩
    · rintro ⟨-, h1, h2⟩
      exact hlev g hg ((mem_St_iff β Λ hfr _).2
        ⟨stab_transfer _ _ N u a10 a01 _ s1 h1, stab_transfer _ _ N u a10 a01 _ s2 h2⟩)
  · unfold levChi
    rw [levFn_eq_one β L _ (hred g hs (hSt g hg)), Units.val_one]
  · obtain ⟨k₁, k₂, h1, h2, hk12⟩ := hsplit k
    have hφφ : (φ : EAf D) * φ = φ := by rw [hφ, ← RingHom.map_mul, hff]
    have s1 := supp_fin V h1
    have s1' := supp_fin V (hinv _ h1)
    have s2 := supp_fin V h2
    have s2' := supp_fin V (hinv' _ h2)
    rw [MonoidHom.map_inv] at s1' s2'
    rw [RingHom.map_sub, RingHom.map_one] at s2 s2'
    rw [← hφ] at s1 s1' s2 s2'
    have hk' := (mem_St_iff β Λ hfr _).1 (hSt k hk)
    have ek : finE V k = finE V k₁ * finE V k₂ := by rw [hk12, MonoidHom.map_mul]
    have m1 : k₁ ∈ levG V β L := hlev _ h1 ((mem_St_iff β Λ hfr _).2
      ⟨comp_gen _ φ hφφ _ _ _ s1 s2 (Or.inl (by rw [ek, Units.val_mul])) hk'.1,
       comp_gen _ φ hφφ _ _ _ s1' s2' (Or.inr (by rw [ek, mul_inv_rev, Units.val_mul])) hk'.2⟩)
    refine ⟨k₁, m1, k₂, ?_, h1, h2, hk12⟩
    have : k₂ = k₁⁻¹ * k := by rw [hk12, inv_mul_cancel_left]
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ m1) hk

end Main

end GlobalTheory.LevSplit
