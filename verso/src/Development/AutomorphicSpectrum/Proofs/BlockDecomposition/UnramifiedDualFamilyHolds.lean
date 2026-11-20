import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development

open IsLocalRing

namespace GlobalTheory.CompanionTheory.UnramDual

section Core

variable {A : Type*} [CommRing A] [IsLocalRing A] {ι : Type*} [Fintype ι]

/- English proof (translation)
Set `f : ι → (ResidueField A →* ResidueField A)` to `fun i => (ResidueField.mapEquiv (e i) : ResidueField A ≃+* ResidueField A).toMonoidHom`. Establish `hf : ∀ i x, f i (residue A x) = residue A (e i x)` using `fun i x => rfl`. Establish `hinj : Function.Injective f`. Introduce `i j hij`. Assume the negation of the conclusion as `hne`.

Take `⟨x, hx⟩` from `hd i j hne`. Establish `h1 : residue A (e i x) = residue A (e j x)`. Rewrite using `[← hf, ← hf, hij]`. Establish `h2 : residue A (e i x - e j x) = 0`. Rewrite using `[map_sub, h1, sub_self]`.

Rewrite `h2` using `[residue_eq_zero_iff]`. Conclude with `h2 hx`. Establish `hli` using `(linearIndependent_monoidHom (ResidueField A) (ResidueField A)).comp f hinj`. Use function extensionality and compare the values at `i`. Use `Fintype.linearIndependent_iff.1 hli c ?_ i` and prove the remaining obligations.

Use function extensionality and compare the values at `t`. Take `⟨x, rfl⟩` from `residue_surjective t`. Simplify `hc x` using `[hf]`.
-/
theorem res_indep (e : ι → A ≃+* A) (hd : ∀ i j, i ≠ j → ∃ x, IsUnit (e i x - e j x))
    (c : ι → ResidueField A)
    (hc : ∀ x : A, ∑ i, c i * residue A (e i x) = 0) : c = 0 := by
  classical
  let f : ι → (ResidueField A →* ResidueField A) :=
    fun i => (ResidueField.mapEquiv (e i) : ResidueField A ≃+* ResidueField A).toMonoidHom
  have hf : ∀ i x, f i (residue A x) = residue A (e i x) := fun i x => rfl
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    obtain ⟨x, hx⟩ := hd i j hne
    have h1 : residue A (e i x) = residue A (e j x) := by
      rw [← hf, ← hf, hij]
    have h2 : residue A (e i x - e j x) = 0 := by
      rw [map_sub, h1, sub_self]
    rw [residue_eq_zero_iff] at h2
    exact h2 hx
  have hli := (linearIndependent_monoidHom (ResidueField A) (ResidueField A)).comp f hinj
  funext i
  refine Fintype.linearIndependent_iff.1 hli c ?_ i
  funext t
  obtain ⟨x, rfl⟩ := residue_surjective t
  simpa [hf] using hc x

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Establish `h` using `res_indep e hd (fun _ => 1) (fun x => by`. Establish `: residue A (∑ i, e i x) = 0`. Rewrite using `[residue_eq_zero_iff]`.

Conclude with `hne x`. Simplify `this)` using `[map_sum]`. Conclude with `one_ne_zero (congrFun h (Classical.arbitrary ι))`.
-/
theorem exists_isUnit_sum [Nonempty ι] (e : ι → A ≃+* A)
    (hd : ∀ i j, i ≠ j → ∃ x, IsUnit (e i x - e j x)) : ∃ x, IsUnit (∑ i, e i x) := by
  by_contra hne
  push_neg at hne
  have h := res_indep e hd (fun _ => 1) (fun x => by
    have : residue A (∑ i, e i x) = 0 := by
      rw [residue_eq_zero_iff]; exact hne x
    simpa [map_sum] using this)
  exact one_ne_zero (congrFun h (Classical.arbitrary ι))

/- English proof (translation)
Assume the negation of the conclusion as `hdet`. Use `set M : Matrix ι ι A := Matrix.of fun i j => e j (b i) with hM`. Establish `h0 : ((residue A).mapMatrix M).det = 0`. Rewrite using `[← RingHom.map_det, residue_eq_zero_iff]`. Conclude with `hdet`.

Take `⟨c, hc0, hc⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 h0`. Use `hc0 (res_indep e hd c fun x => ?_)` and prove the remaining obligations. Take `⟨a, ha, rfl⟩` from `hspan x`. Establish `hrow : ∀ i, ∑ j, residue A (e j (b i)) * c j = 0` using `fun i => by`. Simplify `congrFun hc i` using `[Matrix.mulVec, dotProduct, hM]`.

Establish `: ∀ j, c j * residue A (e j (∑ i, a i * b i)) = ∑ i, residue A (a i) * (residue A (e j (b i)) * c j)` using `fun j => by`. Rewrite using `[map_sum, map_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, hS j _ (ha i), map_mul]`. Expand and normalize the polynomial expressions, which then agree.

Repeatedly rewrite using `[this]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.mul_sum, hrow, mul_zero]`.
-/
theorem isUnit_det [DecidableEq ι] (e : ι → A ≃+* A)
    (hd : ∀ i j, i ≠ j → ∃ x, IsUnit (e i x - e j x)) (b : ι → A) (S : Set A)
    (hS : ∀ i, ∀ a ∈ S, e i a = a)
    (hspan : ∀ x, ∃ a : ι → A, (∀ i, a i ∈ S) ∧ x = ∑ i, a i * b i) :
    IsUnit (Matrix.of fun i j => e j (b i)).det := by
  by_contra hdet
  set M : Matrix ι ι A := Matrix.of fun i j => e j (b i) with hM
  have h0 : ((residue A).mapMatrix M).det = 0 := by
    rw [← RingHom.map_det, residue_eq_zero_iff]; exact hdet
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  refine hc0 (res_indep e hd c fun x => ?_)
  obtain ⟨a, ha, rfl⟩ := hspan x
  have hrow : ∀ i, ∑ j, residue A (e j (b i)) * c j = 0 := fun i => by
    simpa [Matrix.mulVec, dotProduct, hM] using congrFun hc i
  have : ∀ j, c j * residue A (e j (∑ i, a i * b i)) =
      ∑ i, residue A (a i) * (residue A (e j (b i)) * c j) := fun j => by
    rw [map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, hS j _ (ha i), map_mul]; ring
  simp_rw [this]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [← Finset.mul_sum, hrow, mul_zero]

end Core

noncomputable section Local

open ValuativeRel PositivityTheory.Rg.Tf.Loc

variable {k E : Type} [Field k] [ValuativeRel k] [Field E] [ValuativeRel E] [Algebra k E]
  [ValuativeExtension k E]

abbrev RO (E : Type) [Field E] [ValuativeRel E] : ValuationSubring E :=
  (valuation E).valuationSubring

/- English proof (translation)
Assemble the required witnesses or components as `⟨Subtype.val_injective, fun x => x.2, fun r hr => ⟨⟨r, hr⟩, rfl⟩⟩`.
-/
theorem ints : (valuation E).Integers (RO E) :=
  ⟨Subtype.val_injective, fun x => x.2, fun r hr => ⟨⟨r, hr⟩, rfl⟩⟩

variable (E) in
/- English proof (translation)
Establish `h1 : (a : k) ≤ᵥ 1`. Rewrite `ha` using `[← map_one (valuation k)]`. Conclude with `(Valuation.Compatible.vle_iff_le (v := valuation k) a 1).2 ha`. Establish `h2 : algebraMap k E a ≤ᵥ algebraMap k E 1` using `(ValuativeExtension.vle_iff_vle a 1).2 h1`. Establish `h3` using `(Valuation.Compatible.vle_iff_le (v := valuation E) _ _).1 h2`.

Simplify using `using h3`.
-/
theorem algebraMap_le_one {a : k} (ha : valuation k a ≤ 1) :
    valuation E (algebraMap k E a) ≤ 1 := by
  have h1 : (a : k) ≤ᵥ 1 := by
    rw [← map_one (valuation k)] at ha
    exact (Valuation.Compatible.vle_iff_le (v := valuation k) a 1).2 ha
  have h2 : algebraMap k E a ≤ᵥ algebraMap k E 1 := (ValuativeExtension.vle_iff_vle a 1).2 h1
  have h3 := (Valuation.Compatible.vle_iff_le (v := valuation E) _ _).1 h2
  simpa using h3

/- English proof (translation)
Set `S : Subalgebra 𝒪[k] E` to `{ carrier := {y | valuation E y ≤ 1} mul_mem' := fun {a c} ha hc => by`. Simplify using `using mul_le_one' ha hc`. Use the proof step `add_mem' := fun {a c} ha hc => show valuation E (a + c) ≤ 1 from (valuation E).map_add_le ha hc`. Use the proof step `algebraMap_mem' := fun r => algebraMap_le_one E (a := (r : k)) r.2 }`. Establish `hfg : (Subalgebra.toSubmodule S).FG`.

Use `⟨Finset.univ.image b, le_antisymm ?_ ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.span_le]`. Introduce `y hy`. Simplify using `only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hy`. Take `⟨i, rfl⟩` from `hy`.

Conclude with `hbi i`. Introduce `y hy`. Establish `hyi` using `(hbr y).1 hy`. Rewrite using `[← b.sum_repr y]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations.

Establish `: (b.repr y i) • b i = (⟨b.repr y i, hyi i⟩ : 𝒪[k]) • b i` using `rfl`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span (by simp))`. Conclude with `IsIntegral.of_mem_of_fg S hfg x hx`.
-/
theorem isIntegral_of_basis {n : Type} [Fintype n] (b : Module.Basis n k E)
    (hbi : ∀ i, b i ∈ intO E) (hbr : ∀ x : E, x ∈ intO E ↔ ∀ i, b.repr x i ∈ intO k)
    {x : E} (hx : valuation E x ≤ 1) : IsIntegral 𝒪[k] x := by
  classical
  let S : Subalgebra 𝒪[k] E :=
    { carrier := {y | valuation E y ≤ 1}
      mul_mem' := fun {a c} ha hc => by
        simpa using mul_le_one' ha hc
      add_mem' := fun {a c} ha hc => show valuation E (a + c) ≤ 1 from (valuation E).map_add_le ha hc
      algebraMap_mem' := fun r => algebraMap_le_one E (a := (r : k)) r.2 }
  have hfg : (Subalgebra.toSubmodule S).FG := by
    refine ⟨Finset.univ.image b, le_antisymm ?_ ?_⟩
    · rw [Submodule.span_le]
      intro y hy
      simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hy
      obtain ⟨i, rfl⟩ := hy
      exact hbi i
    · intro y hy
      have hyi := (hbr y).1 hy
      rw [← b.sum_repr y]
      refine Submodule.sum_mem _ fun i _ => ?_
      have : (b.repr y i) • b i = (⟨b.repr y i, hyi i⟩ : 𝒪[k]) • b i := rfl
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  exact IsIntegral.of_mem_of_fg S hfg x hx

/- English proof (translation)
Establish `h1 : IsIntegral 𝒪[k] (τ x)`. Use `(isIntegral_of_basis b hbi hbr hx).map ((τ : E →ₐ[k] E).restrictScalars 𝒪[k])` as an intermediate fact. Simplify using `using this`. Take `⟨p, hp, hp0⟩` from `h1`. Set `φ : 𝒪[k] →+* RO E` to `{ toFun := fun r => ⟨algebraMap k E r, algebraMap_le_one E (a := (r : k)) r.2⟩ map_one' := by ext; simp map_mul' := fun a c => by ext; simp map_zero' := by ext; simp map_add' := fun a c => by ext; simp }`.

Establish `h2 : IsIntegral (RO E) (τ x)`. Use `⟨p.map φ, hp.map φ, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.eval₂_map]`. Conclude with `hp0`. Conclude with `(ints (E := E)).mem_of_integral h2`.
-/
theorem map_le_one_of_basis {n : Type} [Fintype n] (b : Module.Basis n k E)
    (hbi : ∀ i, b i ∈ intO E) (hbr : ∀ x : E, x ∈ intO E ↔ ∀ i, b.repr x i ∈ intO k)
    (τ : E ≃ₐ[k] E) {x : E} (hx : valuation E x ≤ 1) : valuation E (τ x) ≤ 1 := by
  have h1 : IsIntegral 𝒪[k] (τ x) := by
    have := (isIntegral_of_basis b hbi hbr hx).map ((τ : E →ₐ[k] E).restrictScalars 𝒪[k])
    simpa using this
  obtain ⟨p, hp, hp0⟩ := h1
  let φ : 𝒪[k] →+* RO E :=
    { toFun := fun r => ⟨algebraMap k E r, algebraMap_le_one E (a := (r : k)) r.2⟩
      map_one' := by ext; simp
      map_mul' := fun a c => by ext; simp
      map_zero' := by ext; simp
      map_add' := fun a c => by ext; simp }
  have h2 : IsIntegral (RO E) (τ x) := by
    refine ⟨p.map φ, hp.map φ, ?_⟩
    rw [Polynomial.eval₂_map]
    exact hp0
  exact (ints (E := E)).mem_of_integral h2

def autRO (τ : E ≃ₐ[k] E) (h : ∀ x, valuation E x ≤ 1 → valuation E (τ x) ≤ 1)
    (h' : ∀ x, valuation E x ≤ 1 → valuation E (τ.symm x) ≤ 1) : RO E ≃+* RO E where
  toFun x := ⟨τ x, h _ x.2⟩
  invFun x := ⟨τ.symm x, h' _ x.2⟩
  left_inv x := by ext; simp
  right_inv x := by ext; simp
  map_mul' x y := by ext; simp
  map_add' x y := by ext; simp

end Local

noncomputable section Main

open ValuativeRel PositivityTheory.Rg.Tf.Loc

variable {k E : Type} [Field k] [ValuativeRel k] [Field E] [ValuativeRel E] [Algebra k E]
  [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E]

/- English proof (translation)
Establish `hpos : 0 < Module.finrank k E` using `Module.finrank_pos`. Establish `hσℓ : σ ^ Module.finrank k E = 1`. Rewrite using `[← IsGalois.card_aut_eq_finrank]`. Conclude with `pow_card_eq_one'`. Establish `hpres : ∀ (τ : E ≃ₐ[k] E) (x : E), valuation E x ≤ 1 → valuation E (τ x) ≤ 1` using `fun τ x hx => map_le_one_of_basis b hbi hbr τ hx`.

Set `e : Fin (Module.finrank k E) → RO E ≃+* RO E` to `fun j => autRO (σ ^ (j : ℕ)) (hpres _) (hpres _)`. Establish `he : ∀ j (x : RO E), ((e j x : RO E) : E) = (σ ^ (j : ℕ)) x` using `fun _ _ => rfl`. Establish `hlt : ∀ i j : Fin (Module.finrank k E), i < j → ∃ x, IsUnit (e j x - e i x)`. Introduce `i j hij`. Establish `hij' : (i : ℕ) < j` using `hij`.

Take `⟨y, hy, hy1⟩` from `hres ((j : ℕ) - i) (by omega) (by have := j.2; omega)`. Use `⟨⟨(σ ^ (i : ℕ)).symm y, hpres _ _ hy⟩, (ints (E := E)).isUnit_iff_valuation_eq_one.2 ?_⟩` and prove the remaining obligations. Establish `hj : σ ^ (j : ℕ) = σ ^ ((j : ℕ) - i) * σ ^ (i : ℕ)` using `(pow_sub_mul_pow σ hij'.le).symm`. Establish `: algebraMap (RO E) E (e j ⟨(σ ^ (i : ℕ)).symm y, hpres _ _ hy⟩ - e i ⟨(σ ^ (i : ℕ)).symm y, hpres _ _ hy⟩) = (σ ^ ((j : ℕ) - i)) y - y`. Express the relevant statement in the definitionally equal form `(σ ^ (j : ℕ)) ((σ ^ (i : ℕ)).symm y) - (σ ^ (i : ℕ)) ((σ ^ (i : ℕ)).symm y) = _`.

Rewrite using `[hj, AlgEquiv.mul_apply, AlgEquiv.apply_symm_apply]`. Rewrite using `[this]`. Conclude with `hy1`. Establish `hd : ∀ i j, i ≠ j → ∃ x, IsUnit (e i x - e j x)`. Introduce `i j hij`.

Break down `lt_or_gt_of_ne hij with h | h` into its components or cases. Take `⟨x, hx⟩` from `hlt i j h`. Conclude with `⟨x, by simpa using hx.neg⟩`. Conclude with `hlt j i h`. Use `haveI : Nonempty (Fin (Module.finrank k E)) := ⟨⟨0, hpos⟩⟩`.

Prove the components needed by the constructor for the conclusion. Take `⟨x0, hx0⟩` from `exists_isUnit_sum e hd set c : E := ∑ j ∈ Finset.range (Module.finrank k E), (σ ^ j) (x0 : E) with hc`. Establish `hcv : valuation E c = 1`. Establish `h1` using `(ints (E := E)).isUnit_iff_valuation_eq_one.1 hx0`. Establish `h2 : algebraMap (RO E) E (∑ i, e i x0) = c`.

Rewrite using `[map_sum, hc, ← Fin.sum_univ_eq_sum_range (fun j => (σ ^ j) (x0 : E))]`. Both sides reduce to the same expression. Rewrite `h1` using `[h2]`. Then use the resulting hypothesis. Establish `hc0 : c ≠ 0` using `(Valuation.ne_zero_iff _).1 (by rw [hcv]; exact one_ne_zero)`. Establish `hcσ : σ c = c`.

Establish `h1 : σ c = ∑ j ∈ Finset.range (Module.finrank k E), (σ ^ (j + 1)) (x0 : E)`. Rewrite using `[hc, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[pow_succ']`. Both sides reduce to the same expression.

Establish `h2` using `Finset.sum_range_succ (fun j => (σ ^ j) (x0 : E)) (Module.finrank k E)`. Rewrite `h2` using `[Finset.sum_range_succ']`. Rewrite using `[h1]`. Simplify using `only [hσℓ, pow_zero, AlgEquiv.one_apply] at h2`. Conclude with `add_right_cancel h2`.

Establish `hcj : ∀ j : ℕ, (σ ^ j) c = c`. Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => simp`. Consider the case `succ j ih => rw [pow_succ, AlgEquiv.mul_apply, hcσ, ih]`.

Use `⟨x0 * c⁻¹, ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `valuation E (x0 * c⁻¹) ≤ 1`. Rewrite using `[map_mul, map_inv₀, hcv, inv_one, mul_one]`. Conclude with `x0.2`. Simplify using `only [map_mul, map_inv₀, hcj]`.

Rewrite using `[← Finset.sum_mul, ← hc, mul_inv_cancel₀ hc0]`. Set `B : Fin (Module.finrank k E) → RO E` to `fun i => ⟨b i, hbi i⟩`. Establish `hdet` using `isUnit_det e hd B {a | ∃ c : k, (a : E) = algebraMap k E c} (fun i a ha => by`. Take `⟨c, hc⟩` from `ha`. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[he, hc, AlgEquiv.commutes])`. Use the proof step `(fun x => by`. Use `⟨fun i => ⟨algebraMap k E (b.repr x i), algebraMap_le_one E ((hbr x).1 x.2 i)⟩, fun i => ⟨_, rfl⟩, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Establish `h` using `b.sum_repr (x : E)`.

Simplify using `only [Algebra.smul_def] at h`. Rewrite using `[AddSubmonoidClass.coe_finset_sum]`. Conclude with `h.symm)`. Use `set M : Matrix (Fin (Module.finrank k E)) (Fin (Module.finrank k E)) (RO E) := Matrix.of fun i j => e j (B i) with hM`. Use `⟨fun i => ((M⁻¹ ⟨0, hpos⟩ i : RO E) : E), fun i => b i, fun i => ⟨(M⁻¹ ⟨0, hpos⟩ i).2, hbi i⟩, fun j hj => ?_⟩` and prove the remaining obligations.

Establish `h1` using `congrFun (congrFun (Matrix.nonsing_inv_mul M hdet) ⟨0, hpos⟩) ⟨j, hj⟩`. Rewrite `h1` using `[Matrix.mul_apply]`. Establish `h2` using `congrArg (fun z : RO E => (z : E)) h1`. Simplify using `only [AddSubmonoidClass.coe_finset_sum, MulMemClass.coe_mul] at h2`. Establish `h3 : ∀ i, ((M i ⟨j, hj⟩ : RO E) : E) = (σ ^ j) (b i)` using `fun i => rfl`.

Simplify using `only [h3] at h2`. Rewrite using `[h2, Matrix.one_apply]`. Distinguish the cases in `h0 : j = 0`. Substitute `h0` using the available equality. Simplify using the standard rewrite rules.

Establish `: (⟨0, hpos⟩ : Fin (Module.finrank k E)) ≠ ⟨j, hj⟩`. Introduce `h`. Conclude with `h0 (congrArg Fin.val h).symm`. Simplify using `[h0, this]`.
-/
theorem dual_of_basis (σ : E ≃ₐ[k] E) (b : Module.Basis (Fin (Module.finrank k E)) k E)
    (hbi : ∀ i, b i ∈ intO E) (hbr : ∀ x : E, x ∈ intO E ↔ ∀ i, b.repr x i ∈ intO k)
    (hres : ∀ j : ℕ, 0 < j → j < Module.finrank k E →
      ∃ x : E, x ∈ intO E ∧ valuation E ((σ ^ j) x - x) = 1) :
    (∃ a : E, a ∈ intO E ∧ ∑ j ∈ Finset.range (Module.finrank k E), (σ ^ j) a = 1) ∧
    ∃ x y : Fin (Module.finrank k E) → E, (∀ i, x i ∈ intO E ∧ y i ∈ intO E) ∧
      ∀ j < Module.finrank k E, ∑ i, x i * (σ ^ j) (y i) = if j = 0 then 1 else 0 := by
  classical
  have hpos : 0 < Module.finrank k E := Module.finrank_pos
  have hσℓ : σ ^ Module.finrank k E = 1 := by
    rw [← IsGalois.card_aut_eq_finrank]; exact pow_card_eq_one'
  have hpres : ∀ (τ : E ≃ₐ[k] E) (x : E), valuation E x ≤ 1 → valuation E (τ x) ≤ 1 :=
    fun τ x hx => map_le_one_of_basis b hbi hbr τ hx
  let e : Fin (Module.finrank k E) → RO E ≃+* RO E :=
    fun j => autRO (σ ^ (j : ℕ)) (hpres _) (hpres _)
  have he : ∀ j (x : RO E), ((e j x : RO E) : E) = (σ ^ (j : ℕ)) x := fun _ _ => rfl
  have hlt : ∀ i j : Fin (Module.finrank k E), i < j → ∃ x, IsUnit (e j x - e i x) := by
    intro i j hij
    have hij' : (i : ℕ) < j := hij
    obtain ⟨y, hy, hy1⟩ := hres ((j : ℕ) - i) (by omega) (by have := j.2; omega)
    refine ⟨⟨(σ ^ (i : ℕ)).symm y, hpres _ _ hy⟩, (ints (E := E)).isUnit_iff_valuation_eq_one.2 ?_⟩
    have hj : σ ^ (j : ℕ) = σ ^ ((j : ℕ) - i) * σ ^ (i : ℕ) := (pow_sub_mul_pow σ hij'.le).symm
    have : algebraMap (RO E) E (e j ⟨(σ ^ (i : ℕ)).symm y, hpres _ _ hy⟩ -
        e i ⟨(σ ^ (i : ℕ)).symm y, hpres _ _ hy⟩) = (σ ^ ((j : ℕ) - i)) y - y := by
      change (σ ^ (j : ℕ)) ((σ ^ (i : ℕ)).symm y) - (σ ^ (i : ℕ)) ((σ ^ (i : ℕ)).symm y) = _
      rw [hj, AlgEquiv.mul_apply, AlgEquiv.apply_symm_apply]
    rw [this]; exact hy1
  have hd : ∀ i j, i ≠ j → ∃ x, IsUnit (e i x - e j x) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · obtain ⟨x, hx⟩ := hlt i j h
      exact ⟨x, by simpa using hx.neg⟩
    · exact hlt j i h
  haveI : Nonempty (Fin (Module.finrank k E)) := ⟨⟨0, hpos⟩⟩
  constructor
  · obtain ⟨x0, hx0⟩ := exists_isUnit_sum e hd
    set c : E := ∑ j ∈ Finset.range (Module.finrank k E), (σ ^ j) (x0 : E) with hc
    have hcv : valuation E c = 1 := by
      have h1 := (ints (E := E)).isUnit_iff_valuation_eq_one.1 hx0
      have h2 : algebraMap (RO E) E (∑ i, e i x0) = c := by
        rw [map_sum, hc, ← Fin.sum_univ_eq_sum_range (fun j => (σ ^ j) (x0 : E))]
        rfl
      rwa [h2] at h1
    have hc0 : c ≠ 0 := (Valuation.ne_zero_iff _).1 (by rw [hcv]; exact one_ne_zero)
    have hcσ : σ c = c := by
      have h1 : σ c = ∑ j ∈ Finset.range (Module.finrank k E), (σ ^ (j + 1)) (x0 : E) := by
        rw [hc, map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [pow_succ']; rfl
      have h2 := Finset.sum_range_succ (fun j => (σ ^ j) (x0 : E)) (Module.finrank k E)
      rw [Finset.sum_range_succ'] at h2
      rw [h1]
      simp only [hσℓ, pow_zero, AlgEquiv.one_apply] at h2
      exact add_right_cancel h2
    have hcj : ∀ j : ℕ, (σ ^ j) c = c := by
      intro j
      induction j with
      | zero => simp
      | succ j ih => rw [pow_succ, AlgEquiv.mul_apply, hcσ, ih]
    refine ⟨x0 * c⁻¹, ?_, ?_⟩
    · change valuation E (x0 * c⁻¹) ≤ 1
      rw [map_mul, map_inv₀, hcv, inv_one, mul_one]
      exact x0.2
    · simp only [map_mul, map_inv₀, hcj]
      rw [← Finset.sum_mul, ← hc, mul_inv_cancel₀ hc0]
  · let B : Fin (Module.finrank k E) → RO E := fun i => ⟨b i, hbi i⟩
    have hdet := isUnit_det e hd B {a | ∃ c : k, (a : E) = algebraMap k E c}
      (fun i a ha => by
        obtain ⟨c, hc⟩ := ha
        apply Subtype.ext
        rw [he, hc, AlgEquiv.commutes])
      (fun x => by
        refine ⟨fun i => ⟨algebraMap k E (b.repr x i), algebraMap_le_one E ((hbr x).1 x.2 i)⟩,
          fun i => ⟨_, rfl⟩, ?_⟩
        apply Subtype.ext
        have h := b.sum_repr (x : E)
        simp only [Algebra.smul_def] at h
        rw [AddSubmonoidClass.coe_finset_sum]
        exact h.symm)
    set M : Matrix (Fin (Module.finrank k E)) (Fin (Module.finrank k E)) (RO E) :=
      Matrix.of fun i j => e j (B i) with hM
    refine ⟨fun i => ((M⁻¹ ⟨0, hpos⟩ i : RO E) : E), fun i => b i,
      fun i => ⟨(M⁻¹ ⟨0, hpos⟩ i).2, hbi i⟩, fun j hj => ?_⟩
    have h1 := congrFun (congrFun (Matrix.nonsing_inv_mul M hdet) ⟨0, hpos⟩) ⟨j, hj⟩
    rw [Matrix.mul_apply] at h1
    have h2 := congrArg (fun z : RO E => (z : E)) h1
    simp only [AddSubmonoidClass.coe_finset_sum, MulMemClass.coe_mul] at h2
    have h3 : ∀ i, ((M i ⟨j, hj⟩ : RO E) : E) = (σ ^ j) (b i) := fun i => rfl
    simp only [h3] at h2
    rw [h2, Matrix.one_apply]
    by_cases h0 : j = 0
    · subst h0; simp
    · have : (⟨0, hpos⟩ : Fin (Module.finrank k E)) ≠ ⟨j, hj⟩ := by
        intro h; exact h0 (congrArg Fin.val h).symm
      simp [h0, this]

end Main

/- English proof (translation)
Introduce `hb k E _ _ _ _ _ _ _ _ _ _ _ _ hU σ hσ`. Take `⟨⟨b, hbi, hbr⟩, -, hres⟩` from `hb k E hU σ hσ`. Conclude with `dual_of_basis σ b hbi hbr hres`.
-/
theorem unramified_trace_one_dual_family : PositivityTheory.Rg.Tf.Loc.IntegralBasisUnramified → PositivityTheory.Rg.Tf.Loc.TraceOneIntegralElement := by
  intro hb k E _ _ _ _ _ _ _ _ _ _ _ _ hU σ hσ
  obtain ⟨⟨b, hbi, hbr⟩, -, hres⟩ := hb k E hU σ hσ
  exact dual_of_basis σ b hbi hbr hres

end GlobalTheory.CompanionTheory.UnramDual
