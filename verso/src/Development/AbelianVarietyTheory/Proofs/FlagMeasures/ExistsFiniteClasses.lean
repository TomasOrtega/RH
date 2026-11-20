import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermLat
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NcardImageOfLe
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthonormalBasisAndOneOrbit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEquivOfRetractions
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DualInterSelfDualHermitianLatticeSubspace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsometryNearIdentityCloseTuplesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CongruenceSubgroupLatticeStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MatrixCongruentOneModUniformizerPowGroupAndOrbitStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ThickOrbitSelfDualUnramifiedLatticeStatement

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.TracePart

open GlobalTheory.HL.DualInter GlobalTheory.HL.ContModel

/- English proof (translation)
Set `σ : Setoid S` to `⟨fun a b => r a b, fun a => hr.refl _, fun h => hr.symm h, fun h1 h2 => hr.trans h1 h2⟩`. Establish `hfin : Finite (f '' S)` using `hf`. Establish `: Finite (Quotient σ)`. Use `Finite.of_injective (β := f '' S) (fun q => ⟨f q.out, q.out, q.out.2, rfl⟩) ?_` and prove the remaining obligations. Introduce `q q' hq`.

Use `h _ q.out.2 _ q'.out.2 (congrArg Subtype.val hq)` as an intermediate fact. Rewrite using `[← Quotient.out_eq q, ← Quotient.out_eq q']`. Conclude with `Quotient.sound this`. Use `⟨(Set.finite_range fun q : Quotient σ => (q.out : α)).toFinset, ?_, ?_⟩` and prove the remaining obligations. Introduce `g hg`.

Take `⟨q, rfl⟩` from `(Set.Finite.mem_toFinset _).1 hg`. Conclude with `q.out.2`. Introduce `a ha`. Use `⟨((Quotient.mk σ ⟨a, ha⟩).out : S), ⟨(Set.Finite.mem_toFinset _).2 ⟨_, rfl⟩, Quotient.mk_out (s := σ) ⟨a, ha⟩⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `g ⟨hg, hga⟩`.

Take `⟨q, rfl⟩` from `(Set.Finite.mem_toFinset _).1 hg`. Establish `: q = Quotient.mk σ ⟨a, ha⟩`. Rewrite using `[← Quotient.out_eq q]`. Conclude with `Quotient.sound hga`. Rewrite using `[← this]`.
-/
theorem exists_reps {α β : Type} (S : Set α) (r : α → α → Prop) (hr : Equivalence r) (f : α → β)
    (hf : (f '' S).Finite) (h : ∀ a ∈ S, ∀ b ∈ S, f a = f b → r a b) :
    ∃ s : Finset α, (∀ g ∈ s, g ∈ S) ∧ ∀ a ∈ S, ∃! g, g ∈ s ∧ r g a := by
  let σ : Setoid S := ⟨fun a b => r a b, fun a => hr.refl _, fun h => hr.symm h,
    fun h1 h2 => hr.trans h1 h2⟩
  have hfin : Finite (f '' S) := hf
  have : Finite (Quotient σ) := by
    refine Finite.of_injective (β := f '' S) (fun q => ⟨f q.out, q.out, q.out.2, rfl⟩) ?_
    intro q q' hq
    have := h _ q.out.2 _ q'.out.2 (congrArg Subtype.val hq)
    rw [← Quotient.out_eq q, ← Quotient.out_eq q']
    exact Quotient.sound this
  refine ⟨(Set.finite_range fun q : Quotient σ => (q.out : α)).toFinset, ?_, ?_⟩
  · intro g hg
    obtain ⟨q, rfl⟩ := (Set.Finite.mem_toFinset _).1 hg
    exact q.out.2
  · intro a ha
    refine ⟨((Quotient.mk σ ⟨a, ha⟩).out : S), ⟨(Set.Finite.mem_toFinset _).2 ⟨_, rfl⟩,
      Quotient.mk_out (s := σ) ⟨a, ha⟩⟩, ?_⟩
    rintro g ⟨hg, hga⟩
    obtain ⟨q, rfl⟩ := (Set.Finite.mem_toFinset _).1 hg
    have : q = Quotient.mk σ ⟨a, ha⟩ := by
      rw [← Quotient.out_eq q]
      exact Quotient.sound hga
    rw [← this]

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {n m : ℕ} {Hm : Matrix (Fin n) (Fin n) E}

omit [TopologicalSpace E] in
/- English proof (translation)
Use function extensionality and compare the values at `j`. Simplify using `only [rmul, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by rw [mul_comm]`.
-/
theorem rmul_mul (x : Fin m → Fin n → E) (A B : Matrix (Fin m) (Fin m) E) :
    rmul (rmul x A) B = rmul x (A * B) := by
  funext j
  simp only [rmul, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by rw [mul_comm]

omit [TopologicalSpace E] in
/- English proof (translation)
Use function extensionality and compare the values at `j`. Simplify using `[rmul, Matrix.one_apply, ite_smul]`.
-/
theorem rmul_one (x : Fin m → Fin n → E) : rmul x 1 = x := by
  funext j
  simp [rmul, Matrix.one_apply, ite_smul]

omit [TopologicalSpace E] in
/- English proof (translation)
Use function extensionality and compare the values at `j`. Simplify using `[rmul]`.
-/
theorem map_rmul (g : (Fin n → E) ≃ₗ[E] (Fin n → E)) (x : Fin m → Fin n → E)
    (A : Matrix (Fin m) (Fin m) E) : (fun a => g (rmul x A a)) = rmul (fun a => g (x a)) A := by
  funext j
  simp [rmul]

omit [TopologicalSpace E] in
/- English proof (translation)
Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`.
-/
theorem span_rmul_le (x : Fin m → Fin n → E) (A : Matrix (Fin m) (Fin m) E) :
    Submodule.span E (Set.range (rmul x A)) ≤ Submodule.span E (Set.range x) := by
  rw [Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

omit [TopologicalSpace E] in
/- English proof (translation)
Use `le_antisymm (span_rmul_le _ _) ?_` and prove the remaining obligations. Use `span_rmul_le (rmul x A⁻¹) A` as an intermediate fact. Rewrite `this` using `[rmul_mul, Matrix.nonsing_inv_mul _ hA, rmul_one]`. Then use the resulting hypothesis.
-/
theorem span_rmul_inv (x : Fin m → Fin n → E) {A : Matrix (Fin m) (Fin m) E} (hA : IsUnit A.det) :
    Submodule.span E (Set.range (rmul x A⁻¹)) = Submodule.span E (Set.range x) := by
  refine le_antisymm (span_rmul_le _ _) ?_
  have := span_rmul_le (rmul x A⁻¹) A
  rwa [rmul_mul, Matrix.nonsing_inv_mul _ hA, rmul_one] at this

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[cT, Matrix.mul_apply, mul_comm]`.
-/
theorem cT_mul (A B : Matrix (Fin m) (Fin m) E) : cT L (A * B) = cT L B * cT L A := by
  ext i j
  simp [cT, Matrix.mul_apply, mul_comm]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[cT, Matrix.one_apply, apply_ite L.cj, eq_comm]`.
-/
theorem cT_one : cT L (1 : Matrix (Fin m) (Fin m) E) = 1 := by
  ext i j
  simp [cT, Matrix.one_apply, apply_ite L.cj, eq_comm]

/- English proof (translation)
Use `Matrix.isUnit_det_of_left_inverse (B := cT L A⁻¹) ?_` and prove the remaining obligations. Rewrite using `[← cT_mul, Matrix.mul_nonsing_inv _ hA, cT_one]`.
-/
theorem isUnit_cT {A : Matrix (Fin m) (Fin m) E} (hA : IsUnit A.det) : IsUnit (cT L A).det := by
  refine Matrix.isUnit_det_of_left_inverse (B := cT L A⁻¹) ?_
  rw [← cT_mul, Matrix.mul_nonsing_inv _ hA, cT_one]

/- English proof (translation)
Use extensionality with `a b`. Conclude with `hg _ _`.
-/
theorem gramT_isom {g : (Fin n → E) ≃ₗ[E] (Fin n → E)} (hg : g ∈ isomG L Hm) (x : Fin m → Fin n → E) :
    gramT L Hm (fun a => g (x a)) = gramT L Hm x := by
  ext a b
  exact hg _ _

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, hw, rfl⟩`. Express the relevant statement in the definitionally equal form `g.symm (g w) ∈ Λ`. Rewrite using `[g.symm_apply_apply]` and apply the resulting hypothesis. Introduce `h`.

Conclude with `⟨_, h, g.apply_symm_apply v⟩`.
-/
theorem mem_smul_iff (g : (Fin n → E) ≃ₗ[E] (Fin n → E)) (Λ : Submodule L.O (Fin n → E))
    (v : Fin n → E) : v ∈ g • Λ ↔ g⁻¹ v ∈ Λ := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    change g.symm (g w) ∈ Λ
    rwa [g.symm_apply_apply]
  · intro h
    exact ⟨_, h, g.apply_symm_apply v⟩

/- English proof (translation)
Use `⟨⟨hΛ.1.1.map _, ?_⟩, fun y => ?_⟩` and prove the remaining obligations. Establish `h : ((g • Λ : Submodule L.O (Fin n → E)) : Set (Fin n → E)) = g.toLinearMap '' Λ` using `rfl`. Rewrite using `[h, ← Submodule.map_span, hΛ.1.2, Submodule.map_top, LinearEquiv.range]`. Rewrite using `[mem_smul_iff, ← hΛ.2]`. Establish `hg'` using `(isomG L Hm).inv_mem hg`.

Prove the components needed by the constructor for the conclusion. Introduce `h x hx`. Use `h (g x) ⟨x, hx, rfl⟩` as an intermediate fact. Rewrite `this` using `[← hg' (g x) y]`. Express the relevant statement in the definitionally equal form `hf L Hm (g.symm (g x)) _ ∈ _ at this`.

Rewrite `this` using `[g.symm_apply_apply]`. Then use the resulting hypothesis. Introduce `h x hx`. Rewrite using `[← hg' x y]`. Conclude with `h _ ((mem_smul_iff g Λ x).1 hx)`.
-/
theorem isSD_smul {g : (Fin n → E) ≃ₗ[E] (Fin n → E)} (hg : g ∈ isomG L Hm)
    {Λ : Submodule L.O (Fin n → E)} (hΛ : IsSD L Hm Λ) : IsSD L Hm (g • Λ) := by
  refine ⟨⟨hΛ.1.1.map _, ?_⟩, fun y => ?_⟩
  · have h : ((g • Λ : Submodule L.O (Fin n → E)) : Set (Fin n → E)) = g.toLinearMap '' Λ := rfl
    rw [h, ← Submodule.map_span, hΛ.1.2, Submodule.map_top, LinearEquiv.range]
  · rw [mem_smul_iff, ← hΛ.2]
    have hg' := (isomG L Hm).inv_mem hg
    constructor
    · intro h x hx
      have := h (g x) ⟨x, hx, rfl⟩
      rw [← hg' (g x) y] at this
      change hf L Hm (g.symm (g x)) _ ∈ _ at this
      rwa [g.symm_apply_apply] at this
    · intro h x hx
      rw [← hg' x y]
      exact h _ ((mem_smul_iff g Λ x).1 hx)

/- English proof (translation)
Establish `hg'` using `(isomG L Hm).inv_mem hg`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, y, h2, h3⟩`. Conclude with `⟨fun a => (mem_smul_iff g Λ _).1 (h1 a), fun a => g⁻¹ (y a), fun a => (mem_smul_iff g Λ _).1 (h2 a), fun a b => (hg' _ _).trans (h3 a b)⟩`. Introduce and unpack `⟨h1, y, h2, h3⟩`.

Use `⟨fun a => (mem_smul_iff g Λ _).2 (h1 a), fun a => g (y a), fun a => ⟨_, h2 a, rfl⟩, fun a b => ?_⟩` and prove the remaining obligations. Rewrite using `[← h3 a b, ← hg (g⁻¹ (u a)) (y b)]`. Express the relevant statement in the definitionally equal form `_ = hf L Hm (g (g.symm (u a))) _`. Rewrite using `[g.apply_symm_apply]`.
-/
theorem isPrimT_smul_iff {g : (Fin n → E) ≃ₗ[E] (Fin n → E)} (hg : g ∈ isomG L Hm)
    (Λ : Submodule L.O (Fin n → E)) (u : Fin m → Fin n → E) :
    IsPrimT L Hm (g • Λ) u ↔ IsPrimT L Hm Λ fun a => g⁻¹ (u a) := by
  have hg' := (isomG L Hm).inv_mem hg
  constructor
  · rintro ⟨h1, y, h2, h3⟩
    exact ⟨fun a => (mem_smul_iff g Λ _).1 (h1 a), fun a => g⁻¹ (y a),
      fun a => (mem_smul_iff g Λ _).1 (h2 a), fun a b => (hg' _ _).trans (h3 a b)⟩
  · rintro ⟨h1, y, h2, h3⟩
    refine ⟨fun a => (mem_smul_iff g Λ _).2 (h1 a), fun a => g (y a), fun a => ⟨_, h2 a, rfl⟩,
      fun a b => ?_⟩
    rw [← h3 a b, ← hg (g⁻¹ (u a)) (y b)]
    change _ = hf L Hm (g (g.symm (u a))) _
    rw [g.apply_symm_apply]

/- English proof (translation)
The claim follows from `Λ.sum_mem fun i _ => Λ.smul_mem (⟨C i a, hC i a⟩ : L.O) (hu i)`.
-/
theorem rmul_mem {Λ : Submodule L.O (Fin n → E)} {u : Fin m → Fin n → E} (hu : ∀ a, u a ∈ Λ)
    {C : Matrix (Fin m) (Fin m) E} (hC : IsIntM L C) (a : Fin m) : rmul u C a ∈ Λ :=
  Λ.sum_mem fun i _ => Λ.smul_mem (⟨C i a, hC i a⟩ : L.O) (hu i)

/- English proof (translation)
Simplify using `only [rmul, sum_l, sum_r, smul_l, smul_r, Matrix.mul_apply, cT, Matrix.of_apply, Finset.sum_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring`.
-/
theorem hf_rmul (u y : Fin m → Fin n → E) (C D : Matrix (Fin m) (Fin m) E) (a b : Fin m) :
    hf L Hm (rmul u C a) (rmul y D b)
      = (cT L D * (Matrix.of fun b a => hf L Hm (u a) (y b)) * C : Matrix _ _ E) b a := by
  simp only [rmul, sum_l, sum_r, smul_l, smul_r, Matrix.mul_apply, cT, Matrix.of_apply,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[cT, L.cj_cj]`.
-/
theorem cT_cT (A : Matrix (Fin m) (Fin m) E) : cT L (cT L A) = A := by
  ext i j
  simp [cT, L.cj_cj]

/- English proof (translation)
Take `⟨h1, y, h2, h3⟩` from `hu`. Use `⟨rmul_mem h1 hC, rmul y (cT L D), rmul_mem h2 fun i j => cj_mem L (hD j i), fun a b => ?_⟩` and prove the remaining obligations. Establish `: (Matrix.of fun b a => hf L Hm (u a) (y b)) = 1`. Use extensionality with `b a`. Simplify using `[h3, Matrix.one_apply, eq_comm]`.

Rewrite using `[hf_rmul, this, cT_cT, mul_one, h, Matrix.one_apply]`. Simplify using `[eq_comm]`.
-/
theorem isPrimT_rmul {Λ : Submodule L.O (Fin n → E)} {u : Fin m → Fin n → E}
    (hu : IsPrimT L Hm Λ u) {C D : Matrix (Fin m) (Fin m) E} (hC : IsIntM L C) (hD : IsIntM L D)
    (h : D * C = 1) : IsPrimT L Hm Λ (rmul u C) := by
  obtain ⟨h1, y, h2, h3⟩ := hu
  refine ⟨rmul_mem h1 hC, rmul y (cT L D), rmul_mem h2 fun i j => cj_mem L (hD j i), fun a b => ?_⟩
  have : (Matrix.of fun b a => hf L Hm (u a) (y b)) = 1 := by
    ext b a
    simp [h3, Matrix.one_apply, eq_comm]
  rw [hf_rmul, this, cT_cT, mul_one, h, Matrix.one_apply]
  simp [eq_comm]

/- English proof (translation)
Use `⟨rmul u (cT L (gramT L Hm u)⁻¹), fun a b => ?_⟩` and prove the remaining obligations. Establish `h` using `hf_rmul (L := L) (Hm := Hm) u u 1 (cT L (gramT L Hm u)⁻¹) a b`. Rewrite `h` using `[rmul_one, cT_cT, mul_one]`. Rewrite using `[h]`. Express the relevant statement in the definitionally equal form `((gramT L Hm u)⁻¹ * gramT L Hm u) b a = _`.

Rewrite using `[Matrix.nonsing_inv_mul _ hu, Matrix.one_apply]`. Simplify using `[eq_comm]`.
-/
theorem exists_dual {u : Fin m → Fin n → E} (hu : IsUnit (gramT L Hm u).det) :
    ∃ y : Fin m → Fin n → E, ∀ a b, hf L Hm (u a) (y b) = if a = b then 1 else 0 := by
  refine ⟨rmul u (cT L (gramT L Hm u)⁻¹), fun a b => ?_⟩
  have h := hf_rmul (L := L) (Hm := Hm) u u 1 (cT L (gramT L Hm u)⁻¹) a b
  rw [rmul_one, cT_cT, mul_one] at h
  rw [h]
  change ((gramT L Hm u)⁻¹ * gramT L Hm u) b a = _
  rw [Matrix.nonsing_inv_mul _ hu, Matrix.one_apply]
  simp [eq_comm]

/- English proof (translation)
Simplify using `[sum_l, smul_l, h]`.
-/
theorem hf_comb {u y : Fin m → Fin n → E}
    (h : ∀ a b, hf L Hm (u a) (y b) = if a = b then 1 else 0) (c : Fin m → E) (b : Fin m) :
    hf L Hm (∑ a, c a • u a) (y b) = c b := by
  simp [sum_l, smul_l, h]

variable [IsNonarchimedeanLocalField F] [CharZero F]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `⟨y, hy⟩` from `exists_dual hu`. Establish `hli : LinearIndependent E u`. Rewrite using `[Fintype.linearIndependent_iff]`.

Introduce `c hc b`. Rewrite using `[← hf_comb hy c b, hc]`. Simplify using `[hf]`. Take `⟨-, -, h3, -⟩` from `dual_inter L Hm hH Λ hΛ m u hli`. Establish `key : ∀ b, ∃ a ∈ Λ, y b - a ∈ perp L Hm (Submodule.span E (Set.range u))`.

Introduce `b`. Use `(h3 (y b)).1 fun v hv hv' => ?_` and prove the remaining obligations. Establish `: v ∈ Submodule.span L.O (Set.range u)` using `h ▸ ⟨hv, hv'⟩`. Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun L.O).1 this`. Use `hf_comb hy (fun a => (c a : E)) b` as an intermediate fact.

Express the relevant statement in the definitionally equal form `hf L Hm (∑ a, (c a : E) • u a) (y b) ∈ _`. Rewrite using `[this]`. Conclude with `(c b).2`. Use `choose w hw hw' using key`. Use `⟨fun a => ?_, w, hw, fun a b => ?_⟩` and prove the remaining obligations.

Establish `: u a ∈ Submodule.span L.O (Set.range u)` using `Submodule.subset_span ⟨a, rfl⟩`. Rewrite `this` using `[← h]`. Conclude with `this.1`. Establish `h0 : hf L Hm (y b - w b) (u a) = 0` using `hw' b _ (Submodule.subset_span ⟨a, rfl⟩)`. Establish `h1` using `cj_hf hH (y b - w b) (u a)`.

Rewrite `h1` using `[h0, map_zero, sub_r, eq_comm, sub_eq_zero]`. Rewrite using `[← h1, hy]`. Introduce and unpack `⟨h1, y, h2, h3⟩`. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `v ⟨hv, hv'⟩`.

Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun E).1 hv'`. Use `Submodule.sum_mem _ fun b _ => ?_` and prove the remaining obligations. Establish `hc : c b ∈ L.O`. Rewrite using `[← hf_comb h3 c b]`. Conclude with `(hΛ.2 _).2 (h2 b) _ hv`.

Conclude with `Submodule.smul_mem _ (⟨c b, hc⟩ : L.O) (Submodule.subset_span ⟨b, rfl⟩)`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨a, rfl⟩`. Conclude with `⟨h1 a, Submodule.subset_span ⟨a, rfl⟩⟩`.
-/
theorem trace_iff (hH : IsHermND L Hm) {Λ : Submodule L.O (Fin n → E)} (hΛ : IsSD L Hm Λ)
    {u : Fin m → Fin n → E} (hu : IsUnit (gramT L Hm u).det) :
    Λ ⊓ (Submodule.span E (Set.range u)).restrictScalars L.O = Submodule.span L.O (Set.range u) ↔
      IsPrimT L Hm Λ u := by
  constructor
  · intro h
    obtain ⟨y, hy⟩ := exists_dual hu
    have hli : LinearIndependent E u := by
      rw [Fintype.linearIndependent_iff]
      intro c hc b
      rw [← hf_comb hy c b, hc]
      simp [hf]
    obtain ⟨-, -, h3, -⟩ := dual_inter L Hm hH Λ hΛ m u hli
    have key : ∀ b, ∃ a ∈ Λ, y b - a ∈ perp L Hm (Submodule.span E (Set.range u)) := by
      intro b
      refine (h3 (y b)).1 fun v hv hv' => ?_
      have : v ∈ Submodule.span L.O (Set.range u) := h ▸ ⟨hv, hv'⟩
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun L.O).1 this
      have := hf_comb hy (fun a => (c a : E)) b
      change hf L Hm (∑ a, (c a : E) • u a) (y b) ∈ _
      rw [this]
      exact (c b).2
    choose w hw hw' using key
    refine ⟨fun a => ?_, w, hw, fun a b => ?_⟩
    · have : u a ∈ Submodule.span L.O (Set.range u) := Submodule.subset_span ⟨a, rfl⟩
      rw [← h] at this
      exact this.1
    · have h0 : hf L Hm (y b - w b) (u a) = 0 := hw' b _ (Submodule.subset_span ⟨a, rfl⟩)
      have h1 := cj_hf hH (y b - w b) (u a)
      rw [h0, map_zero, sub_r, eq_comm, sub_eq_zero] at h1
      rw [← h1, hy]
  · rintro ⟨h1, y, h2, h3⟩
    apply le_antisymm
    · rintro v ⟨hv, hv'⟩
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hv'
      refine Submodule.sum_mem _ fun b _ => ?_
      have hc : c b ∈ L.O := by
        rw [← hf_comb h3 c b]
        exact (hΛ.2 _).2 (h2 b) _ hv
      exact Submodule.smul_mem _ (⟨c b, hc⟩ : L.O) (Submodule.subset_span ⟨b, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      exact ⟨h1 a, Submodule.subset_span ⟨a, rfl⟩⟩

omit [CharZero F] in
/- English proof (translation)
The claim follows from `(GlobalTheory.UnramOrder.algebraMap_mem_iff L _).2 (_root_.pow_mem ϖ.2 j)`.
-/
theorem pow_mem (L : LocE F E) (ϖ : 𝒪[F]) (j : ℕ) : algebraMap F E ((ϖ : F) ^ j) ∈ L.O :=
  (GlobalTheory.UnramOrder.algebraMap_mem_iff L _).2 (_root_.pow_mem ϖ.2 j)

omit [CharZero F] in
/- English proof (translation)
Use `L.free` as an intermediate fact. Establish `: Module.Finite F E` using `Module.finite_of_finrank_pos (by rw [L.rank]; omega)`. Establish `hx : IsAlgebraic 𝒪[F] x` using `(IsFractionRing.isAlgebraic_iff 𝒪[F] F E).2 (Algebra.IsAlgebraic.isAlgebraic x)`. Take `⟨d, hd0, hd⟩` from `hx.exists_integral_multiple`. Take `⟨e, u, hu⟩` from `IsDiscreteValuationRing.associated_pow_irreducible hd0 hϖ`.

Use `⟨e, (L.O_def _).2 ?_⟩` and prove the remaining obligations. Establish `h` using `hd.smul (u : 𝒪[F])`. Rewrite `h` using `[smul_smul, mul_comm, hu, Algebra.smul_def]`. Conclude with `h`.
-/
theorem exists_pow_mul_mem (L : LocE F E) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (x : E) :
    ∃ e : ℕ, algebraMap F E ((ϖ : F) ^ e) * x ∈ L.O := by
  have := L.free
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; omega)
  have hx : IsAlgebraic 𝒪[F] x :=
    (IsFractionRing.isAlgebraic_iff 𝒪[F] F E).2 (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨d, hd0, hd⟩ := hx.exists_integral_multiple
  obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hd0 hϖ
  refine ⟨e, (L.O_def _).2 ?_⟩
  have h := hd.smul (u : 𝒪[F])
  rw [smul_smul, mul_comm, hu, Algebra.smul_def] at h
  exact h

omit [CharZero F] in
/- English proof (translation)
Use `choose e he using fun p : Fin m × Fin m => exists_pow_mul_mem L hϖ (A p.1 p.2)`. Use `⟨∑ p, e p, fun i j => ?_⟩` and prove the remaining obligations. Take `⟨k, hk⟩` from `Nat.exists_eq_add_of_le' (Finset.single_le_sum (f := e) (fun _ _ => Nat.zero_le _) (Finset.mem_univ (i, j)))`. Rewrite using `[hk, pow_add, map_mul, Matrix.smul_apply, smul_eq_mul, mul_assoc]`. Conclude with `L.O.mul_mem (pow_mem L ϖ k) (he (i, j))`.
-/
theorem exists_pow_smul_int (L : LocE F E) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ)
    (A : Matrix (Fin m) (Fin m) E) :
    ∃ e : ℕ, IsIntM L (algebraMap F E ((ϖ : F) ^ e) • A) := by
  choose e he using fun p : Fin m × Fin m => exists_pow_mul_mem L hϖ (A p.1 p.2)
  refine ⟨∑ p, e p, fun i j => ?_⟩
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' (Finset.single_le_sum (f := e) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ (i, j)))
  rw [hk, pow_add, map_mul, Matrix.smul_apply, smul_eq_mul, mul_assoc]
  exact L.O.mul_mem (pow_mem L ϖ k) (he (i, j))

omit [IsNonarchimedeanLocalField F] [CharZero F] in
/- English proof (translation)
Introduce `i j` and use `by rw [Matrix.mul_apply] exact L.O.sum_mem fun k _ => L.O.mul_mem (hA i k) (hB k j)`.
-/
theorem isIntM_mul {A B : Matrix (Fin m) (Fin m) E} (hA : IsIntM L A) (hB : IsIntM L B) :
    IsIntM L (A * B) := fun i j => by
  rw [Matrix.mul_apply]
  exact L.O.sum_mem fun k _ => L.O.mul_mem (hA i k) (hB k j)

omit [CharZero F] in

/- English proof (translation)
Take `⟨e, he⟩` from `exists_pow_smul_int L hϖ A`. Take `⟨f, hf⟩` from `exists_pow_smul_int L hϖ A⁻¹`. Use `⟨e + f, fun i hi B hB => ?_⟩` and prove the remaining obligations. Take `⟨k, rfl⟩` from `Nat.exists_eq_add_of_le hi`. Use `choose c hc hc' using hB`.

Establish `hBc : B = 1 + algebraMap F E ((ϖ : F) ^ (e + f + k)) • Matrix.of c`. Use extensionality with `a b`. Rewrite using `[Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, ← hc']`. Expand and normalize the polynomial expressions, which then agree. Establish `: A * B * A⁻¹ = 1 + (algebraMap F E ((ϖ : F) ^ e) • A) * (algebraMap F E ((ϖ : F) ^ k) • Matrix.of c) * (algebraMap F E ((ϖ : F) ^ f) • A⁻¹)`.

Rewrite using `[hBc, mul_add, add_mul, mul_one, Matrix.mul_nonsing_inv _ hA]`. Simplify using `only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, pow_add, map_mul]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`.

Introduce `a b`. Use `L.O.add_mem ?_ (isIntM_mul (isIntM_mul he fun a b => ?_) hf a b)` and prove the remaining obligations. Rewrite using `[Matrix.one_apply]`. Use `split_ifs`. Use `exacts [L.O.one_mem, L.O.zero_mem]`.

Conclude with `L.O.mul_mem (pow_mem L ϖ k) (hc a b)`.
-/
theorem exists_conj_int (L : LocE F E) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ)
    {A : Matrix (Fin m) (Fin m) E} (hA : IsUnit A.det) :
    ∃ i0 : ℕ, ∀ i ≥ i0, ∀ B ∈ congK L ϖ m i, IsIntM L (A * B * A⁻¹) := by
  obtain ⟨e, he⟩ := exists_pow_smul_int L hϖ A
  obtain ⟨f, hf⟩ := exists_pow_smul_int L hϖ A⁻¹
  refine ⟨e + f, fun i hi B hB => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hi
  choose c hc hc' using hB
  have hBc : B = 1 + algebraMap F E ((ϖ : F) ^ (e + f + k)) • Matrix.of c := by
    ext a b
    rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, ← hc']
    ring
  have : A * B * A⁻¹ = 1 + (algebraMap F E ((ϖ : F) ^ e) • A) *
      (algebraMap F E ((ϖ : F) ^ k) • Matrix.of c) * (algebraMap F E ((ϖ : F) ^ f) • A⁻¹) := by
    rw [hBc, mul_add, add_mul, mul_one, Matrix.mul_nonsing_inv _ hA]
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, pow_add, map_mul]
    congr 2
    ring
  rw [this]
  intro a b
  refine L.O.add_mem ?_ (isIntM_mul (isIntM_mul he fun a b => ?_) hf a b)
  · rw [Matrix.one_apply]; split_ifs; exacts [L.O.one_mem, L.O.zero_mem]
  · exact L.O.mul_mem (pow_mem L ϖ k) (hc a b)

/- English proof (translation)
Take `⟨-, -, -, -, -, h6, h7, -⟩` from `GlobalTheory.UnramOrder.order_facts L ϖ hϖ`. Set `p : L.O` to `⟨_, pow_mem L ϖ N⟩`. Establish `hset : {y : L.O | (y : E) = algebraMap F E ((ϖ : F) ^ N)} = {p}`. Use extensionality with `y`. Simplify using `only [Set.mem_setOf_eq, Set.mem_singleton_iff, Subtype.ext_iff]`.

Both sides reduce to the same expression. Establish `h` using `h6 N`. Rewrite `h` using `[hset]`. Establish `: Finite (L.O ⧸ Ideal.span {p})` using `Nat.finite_of_card_ne_zero (by rw [h]; positivity)`. Establish `: Module.Finite L.O Λ` using `Module.Finite.iff_fg.2 hΛ`.

Establish `: Finite (Λ ⧸ (Ideal.span {p} • ⊤ : Submodule L.O Λ))` using `Submodule.finite_quotient_smul _ Module.Finite.fg_top`. Use `⟨Λ ⧸ (Ideal.span {p} • ⊤ : Submodule L.O Λ), this, fun v => if hv : v ∈ Λ then Submodule.Quotient.mk ⟨v, hv⟩ else 0, fun v hv v' hv' hf => ?_⟩` and prove the remaining obligations. Simplify using `only [dif_pos hv, dif_pos hv'] at hf`. Establish `h2` using `(Submodule.Quotient.eq _).1 hf.symm`. Rewrite `h2` using `[Submodule.ideal_span_singleton_smul]`.

Take `⟨w, -, hw⟩` from `h2`. Conclude with `⟨w, w.2, (congrArg Subtype.val hw).symm⟩`.
-/
theorem exists_finite_classes (L : LocE F E) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ)
    {Λ : Submodule L.O (Fin n → E)} (hΛ : Λ.FG) (N : ℕ) :
    ∃ (β : Type) (_ : Finite β) (f : (Fin n → E) → β), ∀ v ∈ Λ, ∀ v' ∈ Λ, f v = f v' →
      ∃ w ∈ Λ, v' - v = algebraMap F E ((ϖ : F) ^ N) • w := by
  obtain ⟨-, -, -, -, -, h6, h7, -⟩ := GlobalTheory.UnramOrder.order_facts L ϖ hϖ
  let p : L.O := ⟨_, pow_mem L ϖ N⟩
  have hset : {y : L.O | (y : E) = algebraMap F E ((ϖ : F) ^ N)} = {p} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, Subtype.ext_iff]
    rfl
  have h := h6 N
  rw [hset] at h
  have : Finite (L.O ⧸ Ideal.span {p}) := Nat.finite_of_card_ne_zero (by rw [h]; positivity)
  have : Module.Finite L.O Λ := Module.Finite.iff_fg.2 hΛ
  have : Finite (Λ ⧸ (Ideal.span {p} • ⊤ : Submodule L.O Λ)) :=
    Submodule.finite_quotient_smul _ Module.Finite.fg_top
  refine ⟨Λ ⧸ (Ideal.span {p} • ⊤ : Submodule L.O Λ), this,
    fun v => if hv : v ∈ Λ then Submodule.Quotient.mk ⟨v, hv⟩ else 0, fun v hv v' hv' hf => ?_⟩
  simp only [dif_pos hv, dif_pos hv'] at hf
  have h2 := (Submodule.Quotient.eq _).1 hf.symm
  rw [Submodule.ideal_span_singleton_smul] at h2
  obtain ⟨w, -, hw⟩ := h2
  exact ⟨w, w.2, (congrArg Subtype.val hw).symm⟩

def Rel (K : Subgroup ((Fin n → E) ≃ₗ[E] (Fin n → E))) (x : Fin m → Fin n → E)
    (g g' : (Fin n → E) ≃ₗ[E] (Fin n → E)) : Prop :=
  (fun a => g'⁻¹ (x a)) ∈ torb K fun a => g⁻¹ (x a)

omit [IsNonarchimedeanLocalField F] [CharZero F] [TopologicalSpace E] in
/- English proof (translation)
Use `⟨fun u => ⟨1, K.one_mem, rfl⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `u _ ⟨k, hk, rfl⟩`. Conclude with `⟨k⁻¹, K.inv_mem hk, funext fun a => (k.symm_apply_apply _).symm⟩`. Introduce and unpack `u _ _ ⟨k, hk, rfl⟩ ⟨l, hl, rfl⟩`. Conclude with `⟨l * k, K.mul_mem hl hk, rfl⟩`.
-/
theorem torb_equiv (K : Subgroup ((Fin n → E) ≃ₗ[E] (Fin n → E))) :
    Equivalence fun u v : Fin m → Fin n → E => v ∈ torb K u := by
  refine ⟨fun u => ⟨1, K.one_mem, rfl⟩, ?_, ?_⟩
  · rintro u _ ⟨k, hk, rfl⟩
    exact ⟨k⁻¹, K.inv_mem hk, funext fun a => (k.symm_apply_apply _).symm⟩
  · rintro u _ _ ⟨k, hk, rfl⟩ ⟨l, hl, rfl⟩
    exact ⟨l * k, K.mul_mem hl hk, rfl⟩

omit [IsNonarchimedeanLocalField F] [CharZero F] [TopologicalSpace E] in
/- English proof (translation)
Assemble the required witnesses or components as `⟨fun _ => (torb_equiv K).refl _, fun h => (torb_equiv K).symm h, fun h h' => (torb_equiv K).trans h h'⟩`.
-/
theorem rel_equiv (K : Subgroup ((Fin n → E) ≃ₗ[E] (Fin n → E))) (x : Fin m → Fin n → E) :
    Equivalence (Rel K x) :=
  ⟨fun _ => (torb_equiv K).refl _, fun h => (torb_equiv K).symm h,
    fun h h' => (torb_equiv K).trans h h'⟩

omit [IsNonarchimedeanLocalField F] [CharZero F] in

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h, ⟨hi, -, hf⟩, he⟩`. Use `⟨g'⁻¹ * h * g, ⟨(isomG L Hm).mul_mem ((isomG L Hm).mul_mem ((isomG L Hm).inv_mem hg') hi) hg, ?_⟩, funext fun a => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(g'⁻¹ * h * g) • Λs = Λs`. Rewrite using `[mul_smul, mul_smul, ← he, inv_smul_smul]`.

Establish `h1 : h (x a) = x a` using `sub_eq_zero.1 (by`. Simplify using `using hf (x a) (Submodule.subset_span ⟨a, rfl⟩))`. Express the relevant statement in the definitionally equal form `_ = g'⁻¹ (h (g (g.symm (x a))))`. Rewrite using `[g.apply_symm_apply, h1]`. Introduce and unpack `⟨k, ⟨hi, hk⟩, he⟩`.

Establish `hk' : k • Λs = Λs` using `hk`. Establish `h1 : ∀ a, (g' * k * g⁻¹) (x a) = x a` using `fun a => by`. Express the relevant statement in the definitionally equal form `g' (k (g⁻¹ (x a))) = _`. Rewrite using `[← congrFun he a]`. Conclude with `g'.apply_symm_apply _`.

Establish `h2 : ∀ v ∈ Submodule.span E (Set.range x), (g' * k * g⁻¹) v = v`. Introduce `v hv`. Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun E).1 hv`. Simplify using `only [map_sum, map_smul, h1]`. Use `⟨g' * k * g⁻¹, ⟨(isomG L Hm).mul_mem ((isomG L Hm).mul_mem hg' hi) ((isomG L Hm).inv_mem hg), fun v => ⟨fun hv => ?_, fun hv => ?_⟩, fun v hv => ?_⟩, ?_⟩` and prove the remaining obligations.

Use `(g' * k * g⁻¹).injective (h2 _ hv)` as an intermediate fact. Rewrite `hv` using `[this]`. Then use the resulting hypothesis. Rewrite using `[h2 v hv]` and apply the resulting hypothesis. Rewrite using `[h2 v hv, sub_self]`. Conclude with `Submodule.zero_mem _`.

Rewrite using `[mul_smul, mul_smul, inv_smul_smul, hk']`.
-/
theorem rel_iff (Λs : Submodule L.O (Fin n → E)) (x : Fin m → Fin n → E)
    {g g' : (Fin n → E) ≃ₗ[E] (Fin n → E)} (hg : g ∈ isomG L Hm) (hg' : g' ∈ isomG L Hm) :
    (∃ h ∈ fixG L Hm (Submodule.span E (Set.range x)), g' • Λs = h • g • Λs) ↔
      Rel (isomG L Hm ⊓ stabL L Λs) x g g' := by
  constructor
  · rintro ⟨h, ⟨hi, -, hf⟩, he⟩
    refine ⟨g'⁻¹ * h * g, ⟨(isomG L Hm).mul_mem ((isomG L Hm).mul_mem ((isomG L Hm).inv_mem hg') hi) hg, ?_⟩, funext fun a => ?_⟩
    · change (g'⁻¹ * h * g) • Λs = Λs
      rw [mul_smul, mul_smul, ← he, inv_smul_smul]
    · have h1 : h (x a) = x a := sub_eq_zero.1 (by
        simpa using hf (x a) (Submodule.subset_span ⟨a, rfl⟩))
      change _ = g'⁻¹ (h (g (g.symm (x a))))
      rw [g.apply_symm_apply, h1]
  · rintro ⟨k, ⟨hi, hk⟩, he⟩
    have hk' : k • Λs = Λs := hk
    have h1 : ∀ a, (g' * k * g⁻¹) (x a) = x a := fun a => by
      change g' (k (g⁻¹ (x a))) = _
      rw [← congrFun he a]
      exact g'.apply_symm_apply _
    have h2 : ∀ v ∈ Submodule.span E (Set.range x), (g' * k * g⁻¹) v = v := by
      intro v hv
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hv
      simp only [map_sum, map_smul, h1]
    refine ⟨g' * k * g⁻¹, ⟨(isomG L Hm).mul_mem ((isomG L Hm).mul_mem hg' hi)
      ((isomG L Hm).inv_mem hg), fun v => ⟨fun hv => ?_, fun hv => ?_⟩,
      fun v hv => ?_⟩, ?_⟩
    · have := (g' * k * g⁻¹).injective (h2 _ hv)
      rwa [this] at hv
    · rwa [h2 v hv]
    · rw [h2 v hv, sub_self]; exact Submodule.zero_mem _
    · rw [mul_smul, mul_smul, inv_smul_smul, hk']

/- English proof (translation)
Introduce `F _ _ _ _ _ E _ _ _ L ϖ hϖ n Hm hH Λs hΛs m x hx A hA`. Establish `hA' : IsUnit (A⁻¹).det` using `Matrix.isUnit_nonsing_inv_det A hA`. Establish `hxp : IsUnit (gramT L Hm (rmul x A⁻¹)).det`. Rewrite using `[gramT_rmul, Matrix.det_mul, Matrix.det_mul]`. Conclude with `((isUnit_cT hA').mul hx).mul hA'`.

Use `set K := isomG L Hm ⊓ stabL L Λs with hK`. Establish `hcong : ∀ g ∈ isomG L Hm, CongId L ϖ Λs 1 g → g ∈ K` using `fun g hg hc => ⟨hg, (GlobalTheory.T.congruence_subgroup_lattice_stabilizer L ϖ hϖ Λs hΛs.1 1).2.1 le_rfl g hc⟩`. Establish `htr : ∀ g ∈ isomG L Hm, ((g • Λs) ⊓ (Submodule.span E (Set.range x)).restrictScalars L.O = Submodule.span L.O (Set.range (rmul x A⁻¹)) ↔ IsPrimT L Hm Λs (rmul (fun a => g⁻¹ (x a)) A⁻¹))`. Introduce `g hg`. Rewrite using `[← span_rmul_inv x hA, trace_iff hH (isSD_smul hg hΛs) hxp, isPrimT_smul_iff hg, map_rmul]`.

Take `⟨N, hN⟩` from `GlobalTheory.T.exists_isometry_near_identity_close_tuples L ϖ hϖ Hm hH Λs hΛs m _ hxp 1`. Take `⟨β, hβ, f, hf⟩` from `exists_finite_classes L hϖ hΛs.1.1 N`. Take `⟨s, hs, hs'⟩` from `exists_reps {g | g ∈ isomG L Hm ∧ IsPrimT L Hm Λs (rmul (fun a => g⁻¹ (x a)) A⁻¹)} (Rel K x) (rel_equiv K x) (fun g a => f (rmul (fun a => g⁻¹ (x a)) A⁻¹ a)) (Set.toFinite _) (by`. Introduce and unpack `g ⟨hg, hp⟩ g' ⟨hg', hp'⟩ he`. Take `⟨k, hk, hc, hkx⟩` from `hN _ _ hp.1 (by rw [← map_rmul, gramT_isom (inv_mem hg)]) (by rw [← map_rmul, gramT_isom (inv_mem hg')]) (fun a => hf _ (hp.1 a) _ (hp'.1 a) (congrFun he a))`.

Use `⟨k, hcong k hk hc, ?_⟩` and prove the remaining obligations. Establish `h1` using `congrArg (fun u => rmul u A) (funext hkx)`. Simplify using `only [map_rmul, rmul_mul, Matrix.nonsing_inv_mul _ hA, rmul_one] at h1`. Conclude with `h1.symm)`. Use `⟨s, fun g hg => ⟨(hs g hg).1, (htr g (hs g hg).1).2 (hs g hg).2⟩, ?_, ?_⟩` and prove the remaining obligations.

Introduce `Λ hΛ hΛ'`. Take `⟨g0, hg0, rfl⟩` from `(GlobalTheory.HL.SelfDual.orthonormal_basis_and_one_orbit L Hm hH).2 Λs Λ hΛs hΛ`. Take `⟨g, ⟨hg, hr⟩, hu⟩` from `hs' g0 ⟨hg0, (htr g0 hg0).1 hΛ'⟩`. Conclude with `⟨g, ⟨hg, (rel_iff Λs x (hs g hg).1 hg0).2 hr⟩, fun g' hg' => hu g' ⟨hg'.1, (rel_iff Λs x (hs g' hg'.1).1 hg0).1 hg'.2⟩⟩`. Take `⟨e, he⟩` from `exists_pow_smul_int L hϖ A`.

Take `⟨i1, hi1, h1⟩` from `GlobalTheory.T.thick_orbit_selfDual_unramified_lattice L ϖ hϖ Hm hH Λs hΛs Λs hΛs m _ hx 1 e`. Take `⟨i2, h2⟩` from `exists_conj_int L hϖ hA`. Use `⟨max i1 i2, fun i hi => ?_⟩` and prove the remaining obligations. Establish `hi1' : i1 ≤ i` using `le_of_max_le_left hi`. Establish `hi2' : i2 ≤ i` using `le_of_max_le_right hi`.

Take `⟨-, hgrp, -⟩` from `GlobalTheory.T.matrixCongruentOneModUniformizerPow_group_and_orbits L ϖ hϖ m i (hi1.trans hi1')`. Establish `hkeep : ∀ z : Fin m → Fin n → E, IsPrimT L Hm Λs (rmul z A⁻¹) → ∀ B ∈ congK L ϖ m i, IsPrimT L Hm Λs (rmul (rmul z B) A⁻¹)`. Introduce `z hz B hB`. Take `⟨-, hBu, -, hBi, -⟩` from `hgrp B hB`. Use `isPrimT_rmul hz (h2 i hi2' B hB) (h2 i hi2' _ hBi) (by` as an intermediate fact.

Simplify using `only [mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hA, Matrix.nonsing_inv_mul_cancel_left _ _ hBu, Matrix.mul_nonsing_inv _ hA])`. Rewrite `this`, the goal using `[rmul_mul]`. Rewrite `this` using `[mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hA]`. Then use the resulting hypothesis. Establish `hgram : ∀ g ∈ s, ∀ y ∈ torb K (fun a => g⁻¹ (x a)), gramT L Hm y = gramT L Hm x`. Introduce and unpack `g hg _ ⟨k, hk, rfl⟩`.

Rewrite using `[gramT_isom hk.1, gramT_isom (inv_mem (hs g hg).1)]`. Prove the components needed by the constructor for the conclusion. Use extensionality with `z`. Simplify using `only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨hz, B, hB, hzB⟩`. Take `⟨-, hBu, -, hBi, -⟩` from `hgrp B hB`. Establish `hg : gramT L Hm (rmul z B⁻¹) = gramT L Hm x`. Rewrite using `[gramT_rmul, hzB, ← mul_assoc, ← mul_assoc, ← cT_mul, Matrix.mul_nonsing_inv _ hBu, cT_one, one_mul, mul_assoc, Matrix.mul_nonsing_inv _ hBu, mul_one]`. Take `⟨g0, hg0, hg0x⟩` from `GlobalTheory.HermTuple.witt_tuples L Hm hH m x (rmul z B⁻¹) (fun a b => (congrFun (congrFun hg b) a).symm) (by rw [← Matrix.det_transpose]; exact hx)`.

Establish `hg0x' : (fun a => g0⁻¹⁻¹ (x a)) = rmul z B⁻¹`. Rewrite using `[inv_inv]`. Conclude with `funext hg0x`. Take `⟨g, ⟨hgs, hr⟩, -⟩` from `hs' g0⁻¹ ⟨inv_mem hg0, by`. Rewrite using `[hg0x']`.

Conclude with `hkeep z hz _ hBi⟩`. Use `⟨g, hgs, rmul z B⁻¹, hg0x' ▸ hr, B, hB, ?_⟩` and prove the remaining obligations. Rewrite using `[rmul_mul, Matrix.nonsing_inv_mul _ hBu, rmul_one]`. Introduce and unpack `⟨g, hg, hz⟩`. Use `⟨?_, gramT_thick L ϖ Hm _ _ i (hgram g hg) z hz⟩` and prove the remaining obligations.

Take `⟨_, ⟨k, hk, rfl⟩, B, hB, rfl⟩` from `hz`. Use `hkeep _ ?_ B hB` and prove the remaining obligations. Establish `hk' : k⁻¹ • Λs = Λs` using `(inv_mem hk.2 : k⁻¹ ∈ stabL L Λs)`. Use `(isPrimT_smul_iff (inv_mem hk.1) Λs _).1 (hk'.symm ▸ (hs g hg).2)` as an intermediate fact. Rewrite `this` using `[inv_inv, map_rmul]`. Then use the resulting hypothesis.

Introduce `g hg g' hg' hne`. Rewrite using `[Set.disjoint_left]`. Introduce and unpack `_ ⟨y, hy, B, hB, rfl⟩ ⟨y', hy', B', hB', hyy⟩`. Take `⟨-, hBu', -, hBi', -⟩` from `hgrp B' hB'`. Establish `hC` using `(hgrp B hB).2.2.2.2.1 _ hBi'`.

Establish `hy2 : y' = rmul y (B * B'⁻¹)`. Rewrite using `[← rmul_mul, hyy, rmul_mul, Matrix.mul_nonsing_inv _ hBu', rmul_one]`. Establish `h3` using `(h1 i hi1' K le_rfl hcong (fun a => g⁻¹ (x a)) (fun a => by`. Use `rmul_mem (hs g hg).2.1 he a` as an intermediate fact. Rewrite `this` using `[rmul_mul, Matrix.mul_smul, Matrix.nonsing_inv_mul _ hA]`.

Simplify `this)` using `[rmul, Matrix.one_apply, ite_smul]`. Use the proof step `(gramT_isom (inv_mem (hs g hg).1) x)).2 y hy _ hC (by`. Establish `h4` using `hgram g' hg' y' hy'`. Rewrite using `[hy2, gramT_rmul, hgram g hg y hy] at h4)` and apply the resulting hypothesis. Rewrite `h3` using `[← hy2]`.

Establish `hr : Rel K x g g'` using `(torb_equiv K).trans h3 ((torb_equiv K).symm hy')`. Conclude with `hne ((hs' g' (hs g' hg')).unique ⟨hg, hr⟩ ⟨hg', (rel_equiv K x).refl _⟩)`.
-/
theorem trace_partition : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ Λs, IsSD L Hm Λs → ∀ (m : ℕ) (x : Fin m → Fin n → E), IsUnit (gramT L Hm x).det → ∀ A : Matrix (Fin m) (Fin m) E, IsUnit A.det → ∃ s : Finset ((Fin n → E) ≃ₗ[E] (Fin n → E)), (∀ g ∈ s, g ∈ isomG L Hm ∧ (g • Λs) ⊓ (Submodule.span E (Set.range x)).restrictScalars L.O = Submodule.span L.O (Set.range (rmul x A⁻¹))) ∧ (∀ Λ, IsSD L Hm Λ → Λ ⊓ (Submodule.span E (Set.range x)).restrictScalars L.O = Submodule.span L.O (Set.range (rmul x A⁻¹)) → ∃! g, g ∈ s ∧ ∃ h ∈ fixG L Hm (Submodule.span E (Set.range x)), Λ = h • g • Λs) ∧ ∃ i0 : ℕ, ∀ i ≥ i0, {z : Fin m → Fin n → E | IsPrimT L Hm Λs (rmul z A⁻¹) ∧ gramT L Hm z ∈ horb L ϖ (gramT L Hm x) i} = (⋃ g ∈ s, thick L ϖ (torb (isomG L Hm ⊓ stabL L Λs) fun a => g⁻¹ (x a)) i) ∧ ∀ g ∈ s, ∀ g' ∈ s, g ≠ g' → Disjoint (thick L ϖ (torb (isomG L Hm ⊓ stabL L Λs) fun a => g⁻¹ (x a)) i) (thick L ϖ (torb (isomG L Hm ⊓ stabL L Λs) fun a => g'⁻¹ (x a)) i) := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ n Hm hH Λs hΛs m x hx A hA
  have hA' : IsUnit (A⁻¹).det := Matrix.isUnit_nonsing_inv_det A hA
  have hxp : IsUnit (gramT L Hm (rmul x A⁻¹)).det := by
    rw [gramT_rmul, Matrix.det_mul, Matrix.det_mul]
    exact ((isUnit_cT hA').mul hx).mul hA'
  set K := isomG L Hm ⊓ stabL L Λs with hK
  have hcong : ∀ g ∈ isomG L Hm, CongId L ϖ Λs 1 g → g ∈ K := fun g hg hc =>
    ⟨hg, (GlobalTheory.T.congruence_subgroup_lattice_stabilizer L ϖ hϖ Λs hΛs.1 1).2.1 le_rfl g hc⟩
  have htr : ∀ g ∈ isomG L Hm, ((g • Λs) ⊓ (Submodule.span E (Set.range x)).restrictScalars L.O =
      Submodule.span L.O (Set.range (rmul x A⁻¹)) ↔
      IsPrimT L Hm Λs (rmul (fun a => g⁻¹ (x a)) A⁻¹)) := by
    intro g hg
    rw [← span_rmul_inv x hA, trace_iff hH (isSD_smul hg hΛs) hxp, isPrimT_smul_iff hg, map_rmul]
  obtain ⟨N, hN⟩ := GlobalTheory.T.exists_isometry_near_identity_close_tuples L ϖ hϖ Hm hH Λs hΛs m _ hxp 1
  obtain ⟨β, hβ, f, hf⟩ := exists_finite_classes L hϖ hΛs.1.1 N
  obtain ⟨s, hs, hs'⟩ := exists_reps
    {g | g ∈ isomG L Hm ∧ IsPrimT L Hm Λs (rmul (fun a => g⁻¹ (x a)) A⁻¹)} (Rel K x) (rel_equiv K x)
    (fun g a => f (rmul (fun a => g⁻¹ (x a)) A⁻¹ a)) (Set.toFinite _) (by
      rintro g ⟨hg, hp⟩ g' ⟨hg', hp'⟩ he
      obtain ⟨k, hk, hc, hkx⟩ := hN _ _ hp.1
        (by rw [← map_rmul, gramT_isom (inv_mem hg)]) (by rw [← map_rmul, gramT_isom (inv_mem hg')])
        (fun a => hf _ (hp.1 a) _ (hp'.1 a) (congrFun he a))
      refine ⟨k, hcong k hk hc, ?_⟩
      have h1 := congrArg (fun u => rmul u A) (funext hkx)
      simp only [map_rmul, rmul_mul, Matrix.nonsing_inv_mul _ hA, rmul_one] at h1
      exact h1.symm)
  refine ⟨s, fun g hg => ⟨(hs g hg).1, (htr g (hs g hg).1).2 (hs g hg).2⟩, ?_, ?_⟩
  · intro Λ hΛ hΛ'
    obtain ⟨g0, hg0, rfl⟩ := (GlobalTheory.HL.SelfDual.orthonormal_basis_and_one_orbit L Hm hH).2 Λs Λ hΛs hΛ
    obtain ⟨g, ⟨hg, hr⟩, hu⟩ := hs' g0 ⟨hg0, (htr g0 hg0).1 hΛ'⟩
    exact ⟨g, ⟨hg, (rel_iff Λs x (hs g hg).1 hg0).2 hr⟩,
      fun g' hg' => hu g' ⟨hg'.1, (rel_iff Λs x (hs g' hg'.1).1 hg0).1 hg'.2⟩⟩
  obtain ⟨e, he⟩ := exists_pow_smul_int L hϖ A
  obtain ⟨i1, hi1, h1⟩ := GlobalTheory.T.thick_orbit_selfDual_unramified_lattice L ϖ hϖ Hm hH Λs hΛs Λs hΛs m _ hx 1 e
  obtain ⟨i2, h2⟩ := exists_conj_int L hϖ hA
  refine ⟨max i1 i2, fun i hi => ?_⟩
  have hi1' : i1 ≤ i := le_of_max_le_left hi
  have hi2' : i2 ≤ i := le_of_max_le_right hi
  obtain ⟨-, hgrp, -⟩ := GlobalTheory.T.matrixCongruentOneModUniformizerPow_group_and_orbits L ϖ hϖ m i (hi1.trans hi1')
  have hkeep : ∀ z : Fin m → Fin n → E, IsPrimT L Hm Λs (rmul z A⁻¹) → ∀ B ∈ congK L ϖ m i,
      IsPrimT L Hm Λs (rmul (rmul z B) A⁻¹) := by
    intro z hz B hB
    obtain ⟨-, hBu, -, hBi, -⟩ := hgrp B hB
    have := isPrimT_rmul hz (h2 i hi2' B hB) (h2 i hi2' _ hBi) (by
      simp only [mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hA,
        Matrix.nonsing_inv_mul_cancel_left _ _ hBu, Matrix.mul_nonsing_inv _ hA])
    rw [rmul_mul] at this ⊢
    rwa [mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hA] at this
  have hgram : ∀ g ∈ s, ∀ y ∈ torb K (fun a => g⁻¹ (x a)), gramT L Hm y = gramT L Hm x := by
    rintro g hg _ ⟨k, hk, rfl⟩
    rw [gramT_isom hk.1, gramT_isom (inv_mem (hs g hg).1)]
  constructor
  · ext z
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨hz, B, hB, hzB⟩
      obtain ⟨-, hBu, -, hBi, -⟩ := hgrp B hB
      have hg : gramT L Hm (rmul z B⁻¹) = gramT L Hm x := by
        rw [gramT_rmul, hzB, ← mul_assoc, ← mul_assoc, ← cT_mul, Matrix.mul_nonsing_inv _ hBu, cT_one,
          one_mul, mul_assoc, Matrix.mul_nonsing_inv _ hBu, mul_one]
      obtain ⟨g0, hg0, hg0x⟩ := GlobalTheory.HermTuple.witt_tuples L Hm hH m x (rmul z B⁻¹)
        (fun a b => (congrFun (congrFun hg b) a).symm)
        (by rw [← Matrix.det_transpose]; exact hx)
      have hg0x' : (fun a => g0⁻¹⁻¹ (x a)) = rmul z B⁻¹ := by
        rw [inv_inv]; exact funext hg0x
      obtain ⟨g, ⟨hgs, hr⟩, -⟩ := hs' g0⁻¹ ⟨inv_mem hg0, by
        rw [hg0x']; exact hkeep z hz _ hBi⟩
      refine ⟨g, hgs, rmul z B⁻¹, hg0x' ▸ hr, B, hB, ?_⟩
      rw [rmul_mul, Matrix.nonsing_inv_mul _ hBu, rmul_one]
    · rintro ⟨g, hg, hz⟩
      refine ⟨?_, gramT_thick L ϖ Hm _ _ i (hgram g hg) z hz⟩
      obtain ⟨_, ⟨k, hk, rfl⟩, B, hB, rfl⟩ := hz
      refine hkeep _ ?_ B hB
      have hk' : k⁻¹ • Λs = Λs := (inv_mem hk.2 : k⁻¹ ∈ stabL L Λs)
      have := (isPrimT_smul_iff (inv_mem hk.1) Λs _).1 (hk'.symm ▸ (hs g hg).2)
      rwa [inv_inv, map_rmul] at this
  · intro g hg g' hg' hne
    rw [Set.disjoint_left]
    rintro _ ⟨y, hy, B, hB, rfl⟩ ⟨y', hy', B', hB', hyy⟩
    obtain ⟨-, hBu', -, hBi', -⟩ := hgrp B' hB'
    have hC := (hgrp B hB).2.2.2.2.1 _ hBi'
    have hy2 : y' = rmul y (B * B'⁻¹) := by
      rw [← rmul_mul, hyy, rmul_mul, Matrix.mul_nonsing_inv _ hBu', rmul_one]
    have h3 := (h1 i hi1' K le_rfl hcong (fun a => g⁻¹ (x a)) (fun a => by
      have := rmul_mem (hs g hg).2.1 he a
      rw [rmul_mul, Matrix.mul_smul, Matrix.nonsing_inv_mul _ hA] at this
      simpa [rmul, Matrix.one_apply, ite_smul] using this)
      (gramT_isom (inv_mem (hs g hg).1) x)).2 y hy _ hC (by
        have h4 := hgram g' hg' y' hy'
        rwa [hy2, gramT_rmul, hgram g hg y hy] at h4)
    rw [← hy2] at h3
    have hr : Rel K x g g' := (torb_equiv K).trans h3 ((torb_equiv K).symm hy')
    exact hne ((hs' g' (hs g' hg')).unique ⟨hg, hr⟩ ⟨hg', (rel_equiv K x).refl _⟩)

end GlobalTheory.HL.TracePart
