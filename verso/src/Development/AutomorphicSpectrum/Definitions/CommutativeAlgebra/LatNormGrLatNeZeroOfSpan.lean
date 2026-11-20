import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LogAbsVpOfNormalised
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.IdemDen

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT

open Module NumberField

section Norms

variable {C : Type} [Field C] (v : Valuation C NNReal) {O : Type} [CommRing O] [Algebra O C]
  {V : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]

def latNorm (L : Submodule O V) (x : V) : NNReal :=
  sInf {r : NNReal | ∃ a : C, v a = r ∧ ∃ y ∈ L, x = a • y}

def latIn (L : Submodule O V) (U : Submodule C V) : Submodule O U :=
  L.comap (U.subtype.restrictScalars O)

def grLat {n : ℕ} (L : Submodule O V) (b : Basis (Fin n) C V) (i : Fin n) : Submodule O C :=
  (L ⊓ (b.flag i.succ).restrictScalars O).map ((b.coord i).restrictScalars O)

def grLog {n : ℕ} (L : Submodule O V) (b : Basis (Fin n) C V) (i : Fin n) : ℝ :=
  Real.log (latNorm v (grLat L b i) (1 : C))

def dualLat {V' : Type} [AddCommGroup V'] [Module C V'] [Module O V'] [IsScalarTower O C V']
    (B : V →ₗ[C] V' →ₗ[C] C) (L : Submodule O V) : Submodule O V' where
  carrier := {y | ∀ x ∈ L, B x y ∈ (algebraMap O C).range}
  zero_mem' := fun x _ => by simpa using (algebraMap O C).range.zero_mem
  add_mem' := fun {a b} ha hb x hx => by
    simpa using (algebraMap O C).range.add_mem (ha x hx) (hb x hx)
  smul_mem' := fun c y hy x hx => by
    obtain ⟨t, ht⟩ := hy x hx
    refine ⟨c * t, ?_⟩
    rw [map_mul, ht, ← IsScalarTower.algebraMap_smul C c y, map_smul, smul_eq_mul]

end Norms

section Eigen

variable {A : Type} [CommRing A] {K : Type} [Field K] [Algebra A K]
  {V : Type} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
  {E : Type} [Field E] [NumberField E]

def eigSp (ρ : 𝓞 E →+* Module.End K V) (σ : E →+* K) : Submodule K V :=
  ⨅ a : 𝓞 E, LinearMap.ker (ρ a - σ (a : E) • (1 : Module.End K V))

def eigSub (ρ : 𝓞 E →+* Module.End K V) (σ : E →+* K) (X : Submodule A V) : Submodule A V :=
  X ⊓ (eigSp ρ σ).restrictScalars A

def dualInt (E : Type) [Field E] [NumberField E] (k : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) : E :=
  (Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate ℚ E) (integralBasis E) k

def eigProj (ρ : 𝓞 E →+* Module.End K V) (σ : E →+* K) : Module.End K V :=
  ∑ k, σ (dualInt E k) • ρ (RingOfIntegers.basis E k)

def eigQuot (ρ : 𝓞 E →+* Module.End K V) (σ : E →+* K) (X : Submodule A V) : Submodule A V :=
  X.map ((eigProj ρ σ).restrictScalars A)

def IsFreeOn (ρ : 𝓞 E →+* Module.End K V) (X : Submodule A V) {N : ℕ} (t : Fin N → V) : Prop :=
  LinearIndependent K (fun q : Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
      ρ (RingOfIntegers.basis E q.2) (t q.1)) ∧
    Submodule.span K (X : Set V) = ⊤ ∧
    X = Submodule.span A (Set.range fun q : Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
      ρ (RingOfIntegers.basis E q.2) (t q.1))

def diffAbs (v : Valuation K NNReal) (σ : E →+* K) : NNReal :=
  ⨆ x : differentIdeal ℤ (𝓞 E), v (σ ((x : 𝓞 E) : E))

end Eigen

namespace LatBasic

section Norms

variable {C : Type} [Field C] (v : Valuation C NNReal) {O : Type} [CommRing O] [Algebra O C]
  {V : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_latIn {L : Submodule O V} {U : Submodule C V} {x : U} :
    x ∈ latIn L U ↔ (x : V) ∈ L := Iff.rfl

/- English proof (translation)
Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `⟨hy, y.2⟩`. Introduce and unpack `⟨h1, h2⟩`.

Conclude with `⟨⟨x, h2⟩, h1, rfl⟩`.
-/
theorem map_latIn (L : Submodule O V) (U : Submodule C V) :
    (latIn L U).map (U.subtype.restrictScalars O) = L ⊓ U.restrictScalars O := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy, y.2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨x, h2⟩, h1, rfl⟩

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_dualLat {V' : Type} [AddCommGroup V'] [Module C V'] [Module O V']
    [IsScalarTower O C V'] {B : V →ₗ[C] V' →ₗ[C] C} {L : Submodule O V} {y : V'} :
    y ∈ dualLat B L ↔ ∀ x ∈ L, B x y ∈ (algebraMap O C).range := Iff.rfl

/- English proof (translation)
Unfold `latNorm GlobalTheory.HTLat.latNorm`. Use `congr 1`. Use extensionality with `r`. Simplify using `only [Set.mem_setOf_eq, GlobalTheory.HTLat.mem_scaleLat]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨a, h, y, hy, e⟩`. Conclude with `⟨a, ⟨y, hy, e.symm⟩, h⟩`. Introduce and unpack `⟨a, ⟨y, hy, e⟩, h⟩`. Conclude with `⟨a, h, y, hy, e.symm⟩`.
-/
theorem latNorm_eq (L : Submodule O V) (x : V) : latNorm v L x = GlobalTheory.HTLat.latNorm v L x := by
  unfold latNorm GlobalTheory.HTLat.latNorm
  congr 1
  ext r
  simp only [Set.mem_setOf_eq, GlobalTheory.HTLat.mem_scaleLat]
  constructor
  · rintro ⟨a, h, y, hy, e⟩; exact ⟨a, ⟨y, hy, e.symm⟩, h⟩
  · rintro ⟨a, ⟨y, hy, e⟩, h⟩; exact ⟨a, h, y, hy, e.symm⟩

omit [Algebra O C] [IsScalarTower O C V] in

/- English proof (translation)
The claim follows from `csInf_le (OrderBot.bddBelow _) ⟨a, rfl, y, hy, rfl⟩`.
-/
theorem latNorm_le {L : Submodule O V} (a : C) {y : V} (hy : y ∈ L) :
    latNorm v L (a • y) ≤ v a :=
  csInf_le (OrderBot.bddBelow _) ⟨a, rfl, y, hy, rfl⟩

/- English proof (translation)
Rewrite using `[latNorm_eq, GlobalTheory.HTLat.latNorm_span_singleton hv hg]`.
-/
theorem latNorm_span (hv : v.Integers O) {g : V} (hg : g ≠ 0) (c : C) :
    latNorm v (Submodule.span O {g}) (c • g) = v c := by
  rw [latNorm_eq, GlobalTheory.HTLat.latNorm_span_singleton hv hg]

/- English proof (translation)
Establish `key : ∀ {a a' : C} {y : V}, a' ≠ 0 → v a ≤ v a' → a' • y ∈ L → a • y ∈ L`. Introduce `a a' y ha' hle hy`. Take `⟨o, ho⟩` from `hv.exists_of_le_one (r := a / a') (by`. Rewrite using `[map_div₀]`. Conclude with `div_le_one_of_le₀ hle zero_le)`.

Use `L.smul_mem o hy` as an intermediate fact. Rewrite `this` using `[← algebraMap_smul C o, ho, smul_smul, div_mul_cancel₀ _ ha']`. Then use the resulting hypothesis. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x h => exact ⟨1, one_ne_zero, by rwa [one_smul]⟩`. Consider the case `zero => exact ⟨1, one_ne_zero, by simp⟩`.

Consider the case `add x y _ _ hx hy`. Take `⟨a, ha, hx⟩` from `hx`. Take `⟨a', ha', hy⟩` from `hy`. Break down `le_total (v a) (v a') with h | h` into its components or cases. Conclude with `⟨a, ha, by rw [smul_add]; exact L.add_mem hx (key ha' h hy)⟩`.

Conclude with `⟨a', ha', by rw [smul_add]; exact L.add_mem (key ha h hx) hy⟩`. Consider the case `smul c x _ hx`. Take `⟨a, ha, hx⟩` from `hx`. Distinguish the cases in `hc : c = 0`. Conclude with `⟨1, one_ne_zero, by simp [hc]⟩`.

Conclude with `⟨a / c, div_ne_zero ha hc, by rwa [smul_smul, div_mul_cancel₀ _ hc]⟩`.
-/
theorem exists_smul_mem (hv : v.Integers O) {L : Submodule O V} {x : V}
    (hx : x ∈ Submodule.span C (L : Set V)) : ∃ a : C, a ≠ 0 ∧ a • x ∈ L := by
  have key : ∀ {a a' : C} {y : V}, a' ≠ 0 → v a ≤ v a' → a' • y ∈ L → a • y ∈ L := by
    intro a a' y ha' hle hy
    obtain ⟨o, ho⟩ := hv.exists_of_le_one (r := a / a') (by
      rw [map_div₀]; exact div_le_one_of_le₀ hle zero_le)
    have := L.smul_mem o hy
    rwa [← algebraMap_smul C o, ho, smul_smul, div_mul_cancel₀ _ ha'] at this
  induction hx using Submodule.span_induction with
  | mem x h => exact ⟨1, one_ne_zero, by rwa [one_smul]⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hx⟩ := hx
    obtain ⟨a', ha', hy⟩ := hy
    rcases le_total (v a) (v a') with h | h
    · exact ⟨a, ha, by rw [smul_add]; exact L.add_mem hx (key ha' h hy)⟩
    · exact ⟨a', ha', by rw [smul_add]; exact L.add_mem (key ha h hx) hy⟩
  | smul c x _ hx =>
    obtain ⟨a, ha, hx⟩ := hx
    by_cases hc : c = 0
    · exact ⟨1, one_ne_zero, by simp [hc]⟩
    · exact ⟨a / c, div_ne_zero ha hc, by rwa [smul_smul, div_mul_cancel₀ _ hc]⟩

/- English proof (translation)
Establish `h1` using `latNorm_span v hv hc c⁻¹`. Rewrite `h1` using `[smul_eq_mul, inv_mul_cancel₀ hc]`. Rewrite using `[grLog, h, h1, map_inv₀, NNReal.coe_inv, Real.log_inv]`.
-/
theorem grLog_of_eq_span (hv : v.Integers O) {n : ℕ} {L : Submodule O V} {b : Basis (Fin n) C V}
    {i : Fin n} {c : C} (hc : c ≠ 0) (h : grLat L b i = Submodule.span O {c}) :
    grLog v L b i = -Real.log (v c) := by
  have h1 := latNorm_span v hv hc c⁻¹
  rw [smul_eq_mul, inv_mul_cancel₀ hc] at h1
  rw [grLog, h, h1, map_inv₀, NNReal.coe_inv, Real.log_inv]

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨x, ⟨hx, -⟩, rfl⟩`. Express the relevant statement in the definitionally equal form `b.coord i x ∈ _`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x h`.

Take `⟨j, rfl⟩` from `h`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hj]`.

Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul a x _ hx`. Rewrite using `[LinearMap.map_smul_of_tower]`.

Conclude with `Submodule.smul_mem _ a hx`. Rewrite using `[Submodule.span_singleton_le_iff_mem]`. Use `⟨c i • b i, ⟨Submodule.subset_span ⟨i, rfl⟩, ?_⟩, by simp⟩` and prove the remaining obligations. Conclude with `Submodule.smul_mem (b.flag i.succ) _ (b.self_mem_flag Fin.castSucc_lt_succ)`.
-/
theorem grLat_diag {n : ℕ} (b : Basis (Fin n) C V) (c : Fin n → C) (i : Fin n) :
    grLat (Submodule.span O (Set.range fun j => c j • b j)) b i = Submodule.span O {c i} := by
  apply le_antisymm
  · rintro _ ⟨x, ⟨hx, -⟩, rfl⟩
    change b.coord i x ∈ _
    induction hx using Submodule.span_induction with
    | mem x h =>
      obtain ⟨j, rfl⟩ := h
      by_cases hj : j = i
      · subst hj; simp
      · simp [hj]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ a hx
  · rw [Submodule.span_singleton_le_iff_mem]
    refine ⟨c i • b i, ⟨Submodule.subset_span ⟨i, rfl⟩, ?_⟩, by simp⟩
    exact Submodule.smul_mem (b.flag i.succ) _ (b.self_mem_flag Fin.castSucc_lt_succ)

/- English proof (translation)
The claim follows from `grLog_of_eq_span v hv hc (grLat_diag b c i)`.
-/
example (hv : v.Integers O) {n : ℕ} (b : Basis (Fin n) C V) (c : Fin n → C) (i : Fin n)
    (hc : c i ≠ 0) :
    grLog v (Submodule.span O (Set.range fun j => c j • b j)) b i = -Real.log (v (c i)) :=
  grLog_of_eq_span v hv hc (grLat_diag b c i)

/- English proof (translation)
Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `⟨o, ho⟩` from `h c (Submodule.mem_span_singleton_self c)`. Use `Submodule.mem_span_singleton.2 ⟨o, ?_⟩` and prove the remaining obligations.

Rewrite using `[Algebra.smul_def, ho]`. Simplify using the standard rewrite rules. Clear the denominators using the available nonvanishing facts. Introduce `h x hx`. Take `⟨o, rfl⟩` from `Submodule.mem_span_singleton.1 h`.

Take `⟨o', rfl⟩` from `Submodule.mem_span_singleton.1 hx`. Use `⟨o' * o, ?_⟩` and prove the remaining obligations. Simplify using `[Algebra.smul_def]`. Clear the denominators using the available nonvanishing facts.
-/
example {c : C} (hc : c ≠ 0) :
    dualLat (LinearMap.mul C C) (Submodule.span O {c}) = Submodule.span O {c⁻¹} := by
  ext y
  constructor
  · intro h
    obtain ⟨o, ho⟩ := h c (Submodule.mem_span_singleton_self c)
    refine Submodule.mem_span_singleton.2 ⟨o, ?_⟩
    rw [Algebra.smul_def, ho]; simp; field_simp
  · intro h x hx
    obtain ⟨o, rfl⟩ := Submodule.mem_span_singleton.1 h
    obtain ⟨o', rfl⟩ := Submodule.mem_span_singleton.1 hx
    refine ⟨o' * o, ?_⟩
    simp [Algebra.smul_def]; field_simp

end Norms

section Eigen

open TensorProduct

variable {A : Type} [CommRing A] {K : Type} [Field K] [Algebra A K]
  {V : Type} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
  {E : Type} [Field E] [NumberField E]

omit [NumberField E] in

/- English proof (translation)
Simplify using `[eigSp, Submodule.mem_iInf, sub_eq_zero]`.
-/
theorem mem_eigSp {ρ : 𝓞 E →+* Module.End K V} {σ : E →+* K} {x : V} :
    x ∈ eigSp ρ σ ↔ ∀ a : 𝓞 E, ρ a x = σ (a : E) • x := by
  simp [eigSp, Submodule.mem_iInf, sub_eq_zero]

omit [NumberField E] in

/- English proof (translation)
Use extensionality with `x`. Simplify using `[eigSp, GlobalTheory.EigenSplit.mem_eigenSub, sub_eq_zero]`.
-/
theorem eigSp_eq (ρ : 𝓞 E →+* Module.End K V) (σ : E →+* K) :
    eigSp ρ σ = GlobalTheory.EigenSplit.eigenSub ρ (σ.comp (algebraMap (𝓞 E) E)) := by
  ext x
  simp [eigSp, GlobalTheory.EigenSplit.mem_eigenSub, sub_eq_zero]

/- English proof (translation)
Use `LinearMap.BilinForm.apply_dualBasis_left (B := Algebra.traceForm ℚ E) (traceForm_nondegenerate ℚ E) (integralBasis E) k j` as an intermediate fact. Rewrite `this` using `[Algebra.traceForm_apply]`. Use `this using 1` and compare the differences between its conclusion and the goal. Both sides reduce to the same expression.
-/
theorem trace_dualInt (k j) :
    Algebra.trace ℚ E (dualInt E k * integralBasis E j) = if j = k then 1 else 0 := by
  classical
  have := LinearMap.BilinForm.apply_dualBasis_left (B := Algebra.traceForm ℚ E)
    (traceForm_nondegenerate ℚ E) (integralBasis E) k j
  rw [Algebra.traceForm_apply] at this
  convert this using 1
  rfl

/- English proof (translation)
Establish `h` using `((Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate ℚ E) (integralBasis E)).sum_repr x`. Simplify using `only [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply] at h`. Conclude with `h.symm`.
-/
theorem expand_dual (x : E) :
    x = ∑ k, Algebra.trace ℚ E (x * integralBasis E k) • dualInt E k := by
  classical
  have h := ((Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate ℚ E)
    (integralBasis E)).sum_repr x
  simp only [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply] at h
  exact h.symm

/- English proof (translation)
Use `conv_rhs => rw [← (RingOfIntegers.basis E).sum_repr a]`. Simplify using `only [map_sum, RingOfIntegers.coe_eq_algebraMap, Finset.mul_sum, map_zsmul, mul_smul_comm, ← integralBasis_apply, trace_dualInt]`. Simplify using the standard rewrite rules.
-/
theorem repr_eq_trace (a : 𝓞 E) (k) :
    (((RingOfIntegers.basis E).repr a k : ℤ) : ℚ) = Algebra.trace ℚ E (dualInt E k * (a : E)) := by
  classical
  conv_rhs => rw [← (RingOfIntegers.basis E).sum_repr a]
  simp only [map_sum, RingOfIntegers.coe_eq_algebraMap, Finset.mul_sum, map_zsmul, mul_smul_comm,
    ← integralBasis_apply, trace_dualInt]
  simp

/- English proof (translation)
Use `haveI : CharZero K := (RingHom.charZero_iff σ.injective).1 inferInstance`. Rewrite using `[mem_eigSp]`. Introduce `a`. Use `set b := RingOfIntegers.basis E`. Establish `e1 : ∀ k, ρ a (ρ (b k) x) = ∑ j, σ ((Algebra.trace ℚ E (dualInt E j * (a : E) * integralBasis E k) : ℚ) : E) • ρ (b j) x`.

Introduce `k`. Rewrite using `[← Module.End.mul_apply, ← map_mul, ← b.sum_repr (a * b k), map_sum, LinearMap.sum_apply]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `repr_eq_trace (a * b k) j` as an intermediate fact. Rewrite using `[map_zsmul, mul_assoc, integralBasis_apply]`.

Rewrite `this` using `[RingOfIntegers.coe_eq_algebraMap, map_mul (algebraMap (𝓞 E) E)]`. Rewrite using `[RingOfIntegers.coe_eq_algebraMap, ← this]`. Simplify using `[Int.cast_smul_eq_zsmul, b]`. Simplify using `only [eigProj, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]`. Express the relevant statement in the definitionally equal form `∑ k, σ (dualInt E k) • ρ a (ρ (b k) x) = _`.

Simplify using `only [e1, Finset.smul_sum, smul_smul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_smul, ← map_mul, mul_comm (a : E), expand_dual (dualInt E j * (a : E)), map_sum]`. Use `congr 1`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← expand_dual, ← map_mul, Rat.smul_def, mul_comm]`.
-/
theorem eigProj_mem (ρ : 𝓞 E →+* Module.End K V) (σ : E →+* K) (x : V) :
    eigProj ρ σ x ∈ eigSp ρ σ := by
  classical
  haveI : CharZero K := (RingHom.charZero_iff σ.injective).1 inferInstance
  rw [mem_eigSp]
  intro a
  set b := RingOfIntegers.basis E
  have e1 : ∀ k, ρ a (ρ (b k) x) =
      ∑ j, σ ((Algebra.trace ℚ E (dualInt E j * (a : E) * integralBasis E k) : ℚ) : E) •
        ρ (b j) x := by
    intro k
    rw [← Module.End.mul_apply, ← map_mul, ← b.sum_repr (a * b k), map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    have := repr_eq_trace (a * b k) j
    rw [map_zsmul, mul_assoc, integralBasis_apply]
    rw [RingOfIntegers.coe_eq_algebraMap, map_mul (algebraMap (𝓞 E) E)] at this
    rw [RingOfIntegers.coe_eq_algebraMap, ← this]
    simp [Int.cast_smul_eq_zsmul, b]
  simp only [eigProj, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
  change ∑ k, σ (dualInt E k) • ρ a (ρ (b k) x) = _
  simp only [e1, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_smul, ← map_mul, mul_comm (a : E), expand_dual (dualInt E j * (a : E)), map_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← expand_dual, ← map_mul, Rat.smul_def, mul_comm]

/- English proof (translation)
Rewrite using `[← sub_eq_zero]`. Apply `(traceForm_nondegenerate ℚ E).1` to reduce the goal to its premises. Introduce `y`. Rewrite using `[Algebra.traceForm_apply, sub_mul, one_mul, map_sub, sub_eq_zero, Finset.sum_mul, map_sum, Algebra.trace_eq_matrix_trace (integralBasis E) y, Matrix.trace]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, mul_assoc, mul_comm _ y]`. Generalize the expression as in `y * integralBasis E k = z`. Use `conv_lhs => rw [← (integralBasis E).sum_repr z]`. Simplify using `only [Finset.mul_sum, map_sum, mul_smul_comm, map_smul, trace_dualInt]`. Simplify using the standard rewrite rules.
-/
theorem sum_dualInt_mul : ∑ k, dualInt E k * integralBasis E k = 1 := by
  classical
  rw [← sub_eq_zero]
  apply (traceForm_nondegenerate ℚ E).1
  intro y
  rw [Algebra.traceForm_apply, sub_mul, one_mul, map_sub, sub_eq_zero, Finset.sum_mul, map_sum,
    Algebra.trace_eq_matrix_trace (integralBasis E) y, Matrix.trace]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, mul_assoc, mul_comm _ y]
  generalize y * integralBasis E k = z
  conv_lhs => rw [← (integralBasis E).sum_repr z]
  simp only [Finset.mul_sum, map_sum, mul_smul_comm, map_smul, trace_dualInt]
  simp

/- English proof (translation)
Rewrite `hx` using `[mem_eigSp]`. Simplify using `only [eigProj, LinearMap.sum_apply, LinearMap.smul_apply, hx, smul_smul]`. Rewrite using `[← Finset.sum_smul]`. Establish `: ∑ k, σ (dualInt E k) * σ ((RingOfIntegers.basis E k : 𝓞 E) : E) = 1`. Rewrite using `[← map_one σ, ← sum_dualInt_mul, map_sum]`.

Simplify using the standard rewrite rules. Rewrite using `[this, one_smul]`.
-/
theorem eigProj_of_mem {ρ : 𝓞 E →+* Module.End K V} {σ : E →+* K} {x : V} (hx : x ∈ eigSp ρ σ) :
    eigProj ρ σ x = x := by
  rw [mem_eigSp] at hx
  simp only [eigProj, LinearMap.sum_apply, LinearMap.smul_apply, hx, smul_smul]
  rw [← Finset.sum_smul]
  have : ∑ k, σ (dualInt E k) * σ ((RingOfIntegers.basis E k : 𝓞 E) : E) = 1 := by
    rw [← map_one σ, ← sum_dualInt_mul, map_sum]
    simp
  rw [this, one_smul]

/- English proof (translation)
Establish `h1` using `eigProj_mem ρ σ x`. Establish `h2 : eigProj ρ σ x ∈ GlobalTheory.EigenSplit.eigenSub ρ χ`. Simplify using `only [eigProj, LinearMap.sum_apply, LinearMap.smul_apply, GlobalTheory.EigenSplit.mem_eigenSub.1 hx]`. Conclude with `Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hx)`. Assume the negation of the conclusion as `hne`.

Use `h (RingHom.ext fun a => ?_)` and prove the remaining obligations. Conclude with `smul_left_injective K hne ((mem_eigSp.1 h1 a).symm.trans (GlobalTheory.EigenSplit.mem_eigenSub.1 h2 a))`.
-/
theorem eigProj_of_eigenSub_ne {ρ : 𝓞 E →+* Module.End K V} {σ : E →+* K} {χ : 𝓞 E →+* K}
    (h : σ.comp (algebraMap (𝓞 E) E) ≠ χ) {x : V} (hx : x ∈ GlobalTheory.EigenSplit.eigenSub ρ χ) :
    eigProj ρ σ x = 0 := by
  have h1 := eigProj_mem ρ σ x
  have h2 : eigProj ρ σ x ∈ GlobalTheory.EigenSplit.eigenSub ρ χ := by
    simp only [eigProj, LinearMap.sum_apply, LinearMap.smul_apply,
      GlobalTheory.EigenSplit.mem_eigenSub.1 hx]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hx)
  by_contra hne
  refine h (RingHom.ext fun a => ?_)
  exact smul_left_injective K hne
    ((mem_eigSp.1 h1 a).symm.trans (GlobalTheory.EigenSplit.mem_eigenSub.1 h2 a))

/- English proof (translation)
The claim follows from `eigProj_of_eigenSub_ne (fun e => h (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) e)) (by rwa [← eigSp_eq])`.
-/
theorem eigProj_of_ne {ρ : 𝓞 E →+* Module.End K V} {σ σ' : E →+* K} (h : σ ≠ σ') {x : V}
    (hx : x ∈ eigSp ρ σ') : eigProj ρ σ x = 0 :=
  eigProj_of_eigenSub_ne (fun e => h (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) e))
    (by rwa [← eigSp_eq])

/- English proof (translation)
Introduce and unpack `_ ⟨x, -, rfl⟩`. Conclude with `eigProj_mem ρ σ x`.
-/
theorem eigQuot_le_eigSp (ρ : 𝓞 E →+* Module.End K V) (σ : E →+* K) (X : Submodule A V) :
    eigQuot ρ σ X ≤ (eigSp ρ σ).restrictScalars A := by
  rintro _ ⟨x, -, rfl⟩
  exact eigProj_mem ρ σ x

def regAct (K : Type) [Field K] (E : Type) [Field E] [NumberField E] :
    𝓞 E →+* Module.End K (K ⊗[ℤ] 𝓞 E) :=
  (Algebra.lmul K (K ⊗[ℤ] 𝓞 E)).toRingHom.comp
    (Algebra.TensorProduct.includeRight (R := ℤ) (A := K) (B := 𝓞 E)).toRingHom

/- English proof (translation)
Simplify using `[regAct, Algebra.TensorProduct.basis_apply]`.
-/
theorem regAct_basis (k) :
    regAct K E (RingOfIntegers.basis E k) 1 =
      Algebra.TensorProduct.basis K (RingOfIntegers.basis E) k := by
  simp [regAct, Algebra.TensorProduct.basis_apply]

/- English proof (translation)
Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [regAct_basis]`. Conclude with `(Algebra.TensorProduct.basis K (RingOfIntegers.basis E)).linearIndependent.comp (fun q : Fin 1 × _ => q.2) (fun p q h => Prod.ext (Subsingleton.elim _ _) h)`. Rewrite using `[Submodule.span_span_of_tower, Basis.span_eq]`. Simplify using `only [regAct_basis]`.

Use `congr 1`. Use extensionality with `x`. Simplify using the standard rewrite rules.
-/
theorem isFreeOn_reg :
    IsFreeOn (A := A) (regAct K E)
      (Submodule.span A (Set.range (Algebra.TensorProduct.basis K (RingOfIntegers.basis E))))
      (fun _ : Fin 1 => 1) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [regAct_basis]
    exact (Algebra.TensorProduct.basis K (RingOfIntegers.basis E)).linearIndependent.comp
      (fun q : Fin 1 × _ => q.2) (fun p q h => Prod.ext (Subsingleton.elim _ _) h)
  · rw [Submodule.span_span_of_tower, Basis.span_eq]
  · simp only [regAct_basis]
    congr 1
    ext x
    simp

/- English proof (translation)
Introduce `h`. Set `φ : K ⊗[ℤ] 𝓞 E →ₐ[K] K` to `Algebra.TensorProduct.lift (AlgHom.id K K) (σ.comp (algebraMap (𝓞 E) E)).toIntAlgHom (fun _ _ => Commute.all _ _)`. Establish `h1` using `congrArg φ h`. Simplify using `only [eigProj, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, regAct_basis, Algebra.TensorProduct.basis_apply, map_zero] at h1`. Establish `h2 : ∑ k, σ (dualInt E k * integralBasis E k) = 0`.

Simplify `h1` using `[φ]`. Rewrite `h2` using `[← map_sum, sum_dualInt_mul, map_one]`. Conclude with `one_ne_zero h2`.
-/
example (σ : E →+* K) : eigProj (regAct K E) σ 1 ≠ 0 := by
  intro h
  let φ : K ⊗[ℤ] 𝓞 E →ₐ[K] K := Algebra.TensorProduct.lift (AlgHom.id K K)
    (σ.comp (algebraMap (𝓞 E) E)).toIntAlgHom (fun _ _ => Commute.all _ _)
  have h1 := congrArg φ h
  simp only [eigProj, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, regAct_basis,
    Algebra.TensorProduct.basis_apply, map_zero] at h1
  have h2 : ∑ k, σ (dualInt E k * integralBasis E k) = 0 := by
    simpa [φ] using h1
  rw [← map_sum, sum_dualInt_mul, map_one] at h2
  exact one_ne_zero h2

omit [NumberField E] in

/- English proof (translation)
The claim follows from `(Valuation.integer.integers v).isIntegral_iff_v_le_one.1 ((map_isIntegral_int σ (RingOfIntegers.isIntegral_coe x)).tower_top)`.
-/
theorem val_le_one (v : Valuation K NNReal) (σ : E →+* K) (x : 𝓞 E) : v (σ (x : E)) ≤ 1 :=
  (Valuation.integer.integers v).isIntegral_iff_v_le_one.1
    ((map_isIntegral_int σ (RingOfIntegers.isIntegral_coe x)).tower_top)

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, by rintro _ ⟨x, rfl⟩; exact val_le_one v σ x⟩`.
-/
theorem bddAbove_diff (v : Valuation K NNReal) (σ : E →+* K) :
    BddAbove (Set.range fun x : differentIdeal ℤ (𝓞 E) => v (σ ((x : 𝓞 E) : E))) :=
  ⟨1, by rintro _ ⟨x, rfl⟩; exact val_le_one v σ x⟩

/- English proof (translation)
The claim follows from `le_ciSup (bddAbove_diff v σ) ⟨x, hx⟩`.
-/
theorem le_diffAbs (v : Valuation K NNReal) (σ : E →+* K) {x : 𝓞 E}
    (hx : x ∈ differentIdeal ℤ (𝓞 E)) : v (σ (x : E)) ≤ diffAbs v σ :=
  le_ciSup (bddAbove_diff v σ) ⟨x, hx⟩

/- English proof (translation)
Take `⟨x, hx, hx0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 E))`. Use `lt_of_lt_of_le ?_ (le_diffAbs v σ hx)` and prove the remaining obligations. Rewrite using `[pos_iff_ne_zero, Valuation.ne_zero_iff, map_ne_zero]`. Conclude with `hx0` after adjusting the coercions.
-/
theorem diffAbs_pos (v : Valuation K NNReal) (σ : E →+* K) : 0 < diffAbs v σ := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 E))
  refine lt_of_lt_of_le ?_ (le_diffAbs v σ hx)
  rw [pos_iff_ne_zero, Valuation.ne_zero_iff, map_ne_zero]
  exact_mod_cast hx0

/- English proof (translation)
Use `le_antisymm (ciSup_le fun x => ?_) (le_diffAbs v σ (h ▸ Ideal.mem_span_singleton_self δ))` and prove the remaining obligations. Take `⟨y, hy⟩` from `Ideal.mem_span_singleton'.1 (h.le x.2)`. Rewrite using `[← hy, RingOfIntegers.coe_eq_algebraMap, map_mul, map_mul, map_mul]`. Conclude with `mul_le_of_le_one_left' (val_le_one v σ y)`.
-/
theorem diffAbs_of_span (v : Valuation K NNReal) (σ : E →+* K) {δ : 𝓞 E}
    (h : differentIdeal ℤ (𝓞 E) = Ideal.span {δ}) : diffAbs v σ = v (σ (δ : E)) := by
  refine le_antisymm (ciSup_le fun x => ?_)
    (le_diffAbs v σ (h ▸ Ideal.mem_span_singleton_self δ))
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 (h.le x.2)
  rw [← hy, RingOfIntegers.coe_eq_algebraMap, map_mul, map_mul, map_mul]
  exact mul_le_of_le_one_left' (val_le_one v σ y)

end Eigen

end LatBasic

end GlobalTheory.CompanionTheory.Ar.HT
