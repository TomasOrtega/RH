import Mathlib
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich

open CompanionTheory.Rg.FlB

noncomputable section

namespace GlobalTheory.CompanionTheory.FrameTorus

variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]

def gens {l : ℕ} (e f : Fin l → V) (W : Submodule L V) : Set V :=
  Set.range e ∪ Set.range f ∪ (W : Set V)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem span_gens {h : V → V → L} {δ : L} {l : ℕ} {e f : Fin l → V} {W : Submodule L V}
    (hF : IsFrame h δ e f W) : Submodule.span L (gens e f W) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨a, b, w, hw, rfl⟩ := hF.2.2.2.2.2 x
  refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) (Submodule.subset_span (Or.inr hw))
  · exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Or.inl (Or.inl ⟨i, rfl⟩)))
  · exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Or.inl (Or.inr ⟨i, rfl⟩)))

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Check the elementary cases of the proposition. Proceed by induction. Treat this case separately.

Treat this case separately. Treat this case separately. Treat this case separately.
-/
theorem gens_induction {h : V → V → L} {δ : L} {l : ℕ} {e f : Fin l → V} {W : Submodule L V}
    (hF : IsFrame h δ e f W) {P : V → Prop} (hg : ∀ x ∈ gens e f W, P x) (h0 : P 0)
    (ha : ∀ x y, P x → P y → P (x + y)) (hm : ∀ (a : L) x, P x → P (a • x)) (x : V) : P x := by
  have hx : x ∈ Submodule.span L (gens e f W) := by
    rw [span_gens hF]
    trivial
  induction hx using Submodule.span_induction with
  | mem x h => exact hg x h
  | zero => exact h0
  | add x y _ _ hx hy => exact ha x y hx hy
  | smul a x _ hx => exact hm a x hx

def pair {s : L →+* L} {h : V → V → L} (hH : IsHerm s h) (x : V) : V →ₗ[L] L where
  toFun := h x
  map_add' := hH.1 x
  map_smul' a y := by simp [hH.2.1]

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem pair_apply {s : L →+* L} {h : V → V → L} (hH : IsHerm s h) (x y : V) :
    pair hH x y = h x y := rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem add_left {s : L →+* L} {h : V → V → L} (hH : IsHerm s h) (x x' y : V) :
    h (x + x') y = h x y + h x' y := by
  rw [hH.2.2.1 y (x + x'), hH.1, map_add, ← hH.2.2.1, ← hH.2.2.1]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem smul_left {s : L →+* L} {h : V → V → L} (hH : IsHerm s h) (a : L) (x y : V) :
    h (a • x) y = s a * h x y := by
  rw [hH.2.2.1 y (a • x), hH.2.1, map_mul, ← hH.2.2.1]

def tor {s : L →+* L} {h : V → V → L} (hH : IsHerm s h) (δ : L) {l : ℕ} (e f : Fin l → V)
    (u : Fin l → L) : V →ₗ[L] V :=
  LinearMap.id + (∑ i, ((u i - 1) * (s δ)⁻¹) • (pair hH (f i)).smulRight (e i)) +
    ∑ i, (((s (u i))⁻¹ - 1) * δ⁻¹) • (pair hH (e i)).smulRight (f i)

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem tor_apply {s : L →+* L} {h : V → V → L} (hH : IsHerm s h) (δ : L) {l : ℕ} (e f : Fin l → V)
    (u : Fin l → L) (x : V) :
    tor hH δ e f u x = x + (∑ i, ((u i - 1) * (s δ)⁻¹) • (h (f i) x • e i)) +
      ∑ i, (((s (u i))⁻¹ - 1) * δ⁻¹) • (h (e i) x • f i) := by
  simp [tor, LinearMap.add_apply, LinearMap.sum_apply]

section Frame

variable {s : L →+* L} {h : V → V → L} {δ : L} {l : ℕ} {e f : Fin l → V} {W : Submodule L V}

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem pair_fe (hH : IsHerm s h) (hF : IsFrame h δ e f W) (i j : Fin l) :
    h (f i) (e j) = if i = j then s δ else 0 := by
  rw [hH.2.2.1 (e j) (f i), hF.2.2.1 j i]
  by_cases hij : i = j
  · simp [hij]
  · simp [hij, Ne.symm hij]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws.
-/
theorem tor_e (hH : IsHerm s h) (hF : IsFrame h δ e f W) (hδ : δ ≠ 0) (u : Fin l → L) (j : Fin l) :
    tor hH δ e f u (e j) = u j • e j := by
  have hs : s δ ≠ 0 := (map_ne_zero s).2 hδ
  rw [tor_apply]
  simp only [pair_fe hH hF, hF.1, zero_smul, smul_zero, Finset.sum_const_zero, add_zero, ite_smul,
    smul_ite, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [smul_smul, mul_assoc, inv_mul_cancel₀ hs, mul_one, sub_smul, one_smul]
  abel

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws.
-/
theorem tor_f (hH : IsHerm s h) (hF : IsFrame h δ e f W) (hδ : δ ≠ 0) (u : Fin l → L) (j : Fin l) :
    tor hH δ e f u (f j) = (s (u j))⁻¹ • f j := by
  rw [tor_apply]
  simp only [hF.2.1, hF.2.2.1, zero_smul, smul_zero, Finset.sum_const_zero, add_zero, ite_smul,
    smul_ite, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [smul_smul, mul_assoc, inv_mul_cancel₀ hδ, mul_one, sub_smul, one_smul]
  abel

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem tor_w (hH : IsHerm s h) (hF : IsFrame h δ e f W) (u : Fin l → L) {w : V} (hw : w ∈ W) :
    tor hH δ e f u w = w := by
  rw [tor_apply]
  simp [(hF.2.2.2.1 w hw _).1, (hF.2.2.2.1 w hw _).2]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules.
-/
theorem tor_inv (hH : IsHerm s h) (hF : IsFrame h δ e f W) (hδ : δ ≠ 0) (u : Fin l → L)
    (hu : ∀ i, u i ≠ 0) :
    (tor hH δ e f u).comp (tor hH δ e f fun i => (u i)⁻¹) = LinearMap.id := by
  refine LinearMap.ext_on (span_gens hF) ?_
  rintro x ((⟨i, rfl⟩ | ⟨i, rfl⟩) | hx)
  · simp [tor_e hH hF hδ, hu i]
  · have : s (u i) ≠ 0 := (map_ne_zero s).2 (hu i)
    simp [tor_e hH hF hδ, tor_f hH hF hδ, this]
  · simp [tor_w hH hF _ hx]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Apply the first step, then apply the next step to every resulting obligation. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails.

Substitute using the available equality. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem tor_iso_gens (hs : ∀ x, s (s x) = x) (hH : IsHerm s h) (hF : IsFrame h δ e f W) (hδ : δ ≠ 0)
    (u : Fin l → L) (hu : ∀ i, u i ≠ 0) {x y : V} (hx : x ∈ gens e f W) (hy : y ∈ gens e f W) :
    h (tor hH δ e f u x) (tor hH δ e f u y) = h x y := by
  have hsu : ∀ i, s (u i) ≠ 0 := fun i => (map_ne_zero s).2 (hu i)
  have hwe : ∀ {w : V}, w ∈ W → ∀ i, h w (e i) = 0 := fun hw i => by
    rw [hH.2.2.1 (e i) _, (hF.2.2.2.1 _ hw i).1, map_zero]
  have hwf : ∀ {w : V}, w ∈ W → ∀ i, h w (f i) = 0 := fun hw i => by
    rw [hH.2.2.1 (f i) _, (hF.2.2.2.1 _ hw i).2, map_zero]
  rcases hx with (⟨i, rfl⟩ | ⟨i, rfl⟩) | hx <;> rcases hy with (⟨j, rfl⟩ | ⟨j, rfl⟩) | hy
  · simp [tor_e hH hF hδ, smul_left hH, hH.2.1, hF.1]
  · rw [tor_e hH hF hδ, tor_f hH hF hδ, smul_left hH, hH.2.1, hF.2.2.1]
    by_cases hij : i = j
    · subst hij
      simp [hsu i]
    · simp [hij]
  · rw [tor_e hH hF hδ, tor_w hH hF u hy, smul_left hH, (hF.2.2.2.1 _ hy i).1, mul_zero]
  · rw [tor_f hH hF hδ, tor_e hH hF hδ, smul_left hH, hH.2.1, pair_fe hH hF]
    by_cases hij : i = j
    · subst hij
      simp [hs, hu i]
    · simp [hij]
  · simp [tor_f hH hF hδ, smul_left hH, hH.2.1, hF.2.1]
  · rw [tor_f hH hF hδ, tor_w hH hF u hy, smul_left hH, (hF.2.2.2.1 _ hy i).2, mul_zero]
  · rw [tor_w hH hF u hx, tor_e hH hF hδ, hH.2.1, hwe hx, mul_zero]
  · rw [tor_w hH hF u hx, tor_f hH hF hδ, hH.2.1, hwf hx, mul_zero]
  · rw [tor_w hH hF u hx, tor_w hH hF u hy]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules.
-/
theorem tor_iso (hs : ∀ x, s (s x) = x) (hH : IsHerm s h) (hF : IsFrame h δ e f W) (hδ : δ ≠ 0)
    (u : Fin l → L) (hu : ∀ i, u i ≠ 0) (x y : V) :
    h (tor hH δ e f u x) (tor hH δ e f u y) = h x y := by
  have hz : ∀ z, h z 0 = 0 := fun z => by simpa using hH.2.1 0 z 0
  have hz' : ∀ z, h 0 z = 0 := fun z => by simpa using smul_left hH 0 0 z
  have step : ∀ g ∈ gens e f W, ∀ y, h (tor hH δ e f u g) (tor hH δ e f u y) = h g y := by
    intro g hg
    refine gens_induction hF (fun y hy => tor_iso_gens hs hH hF hδ u hu hg hy) ?_ ?_ ?_
    · simp [hz]
    · intro y y' hy hy'
      simp only [map_add, hH.1, hy, hy']
    · intro a y hy
      simp only [map_smul, hH.2.1, hy]
  refine gens_induction hF (P := fun x => ∀ y, h (tor hH δ e f u x) (tor hH δ e f u y) = h x y)
    step ?_ ?_ ?_ x y
  · simp [hz']
  · intro x x' hx hx' y
    rw [map_add, add_left hH, hx, hx', add_left hH]
  · intro a x hx y
    simp only [map_smul, smul_left hH, hx]

end Frame

/- English proof (translation)
Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Introduce a local definition for the expression.

Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components.

A detailed English derivation is pending.
-/
theorem stTor : StTor := by
  unfold StTor ForAll
  intro L _ _ _ _ s hs δ hδ V _ _ _ h hH l e f W hF u hu
  have hδ0 : δ ≠ 0 := hδ.1
  have hui : ∀ i, (u i)⁻¹ ≠ 0 := fun i => inv_ne_zero (hu i)
  let t : V ≃ₗ[L] V := LinearEquiv.ofLinear (tor hH δ e f u) (tor hH δ e f fun i => (u i)⁻¹)
    (tor_inv hH hF hδ0 u hu)
    (by simpa using tor_inv hH hF hδ0 (fun i => (u i)⁻¹) hui)
  refine ⟨t, fun x y => tor_iso hs.1 hH hF hδ0 u hu x y, ⟨fun i => tor_e hH hF hδ0 u i,
    fun i => tor_f hH hF hδ0 u i, fun w hw => tor_w hH hF u hw⟩, ?_⟩
  rintro t' ⟨h1, h2, h3⟩
  apply LinearEquiv.toLinearMap_injective
  refine LinearMap.ext_on (span_gens hF) ?_
  rintro x ((⟨i, rfl⟩ | ⟨i, rfl⟩) | hx)
  · exact (h1 i).trans (tor_e hH hF hδ0 u i).symm
  · exact (h2 i).trans (tor_f hH hF hδ0 u i).symm
  · exact (h3 x hx).trans (tor_w hH hF u hx).symm

end GlobalTheory.CompanionTheory.FrameTorus

end
