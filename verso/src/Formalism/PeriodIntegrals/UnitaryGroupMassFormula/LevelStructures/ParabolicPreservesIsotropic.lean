import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.LeviComp

noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
open scoped TensorProduct

section Levi

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {P : Frame E n r} {c : R ⊗[F] E} {T : F}

/- English proof (translation)
Take `⟨d, rfl⟩` from `mem_tensor_span_iff R P.e x hx`. Rewrite using `[map_sum]`. Use `Submodule.sum_mem _ fun b _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul]`. Use `Submodule.smul_mem _ _ ?_` and prove the remaining obligations.

Establish `h1` using `Submodule.span_mono (Set.image_mono (Set.subset_univ _)) (parabolic_unipotent_on_flag P hs b)`. Establish `h2` using `Submodule.add_mem _ h1 (Submodule.subset_span ⟨b, Set.mem_univ _, rfl⟩ : ratV (F := F) R (P.e b) ∈ spanR (F := F) R P.e Set.univ)`. Rewrite `h2` using `[sub_add_cancel]`. Then use the resulting hypothesis.
-/
theorem parabolic_preserves_isotropic {s : HA R σ J} (hs : s ∈ Ssub R σ J P) {x : Fin n → R ⊗[F] E}
    (hx : x ∈ spanR (F := F) R P.e Set.univ) : lin R σ J s x ∈ spanR (F := F) R P.e Set.univ := by
  obtain ⟨d, rfl⟩ := mem_tensor_span_iff R P.e x hx
  rw [map_sum]
  refine Submodule.sum_mem _ fun b _ => ?_
  rw [map_smul]
  refine Submodule.smul_mem _ _ ?_
  have h1 := Submodule.span_mono (Set.image_mono (Set.subset_univ _)) (parabolic_unipotent_on_flag P hs b)
  have h2 := Submodule.add_mem _ h1 (Submodule.subset_span ⟨b, Set.mem_univ _, rfl⟩ :
    ratV (F := F) R (P.e b) ∈ spanR (F := F) R P.e Set.univ)
  rwa [sub_add_cancel] at h2

/- English proof (translation)
Establish `h` using `hs (Fin.last r)`. Establish `e : F0 P (Fin.last r) = P.z` using `by simp [F0]`. Rewrite `h` using `[e]`. Use `(Submodule.span_le.2 ?_) h` and prove the remaining obligations. Introduce and unpack `_ ⟨a, ha, rfl⟩`.

Take `⟨a', rfl⟩` from `Fin.exists_castSucc_eq.2 (Fin.ne_last_of_lt ha)`. Use `show ratV (F := F) R (F0 P (Fin.castSucc a')) ∈ spanR (F := F) R P.e Set.univ`. Establish `e' : F0 P (Fin.castSucc a') = P.e a'` using `by simp [F0]`. Rewrite using `[e']`. Conclude with `Submodule.subset_span ⟨a', Set.mem_univ _, rfl⟩`.
-/
theorem parabolic_fixes_modulo_span {s : HA R σ J} (hs : s ∈ Ssub R σ J P) :
    lin R σ J s (ratV (F := F) R P.z) - ratV (F := F) R P.z ∈ spanR (F := F) R P.e Set.univ := by
  have h := hs (Fin.last r)
  have e : F0 P (Fin.last r) = P.z := by simp [F0]
  rw [e] at h
  refine (Submodule.span_le.2 ?_) h
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨a', rfl⟩ := Fin.exists_castSucc_eq.2 (Fin.ne_last_of_lt ha)
  show ratV (F := F) R (F0 P (Fin.castSucc a')) ∈ spanR (F := F) R P.e Set.univ
  have e' : F0 P (Fin.castSucc a') = P.e a' := by simp [F0]
  rw [e']
  exact Submodule.subset_span ⟨a', Set.mem_univ _, rfl⟩

/- English proof (translation)
Use `X_left hx fun b => ?_` and prove the remaining obligations. Take `⟨d, rfl⟩` from `mem_tensor_span_iff R P.e y hy`. Rewrite using `[hermForm_sum_right_alt]`. Simplify using `[ht.ee]`.
-/
theorem isotropic_span_hermForm_zero (ht : FrameTab (σ := σ) (J := J) P c T) {x y : Fin n → R ⊗[F] E}
    (hx : x ∈ spanR (F := F) R P.e Set.univ) (hy : y ∈ spanR (F := F) R P.e Set.univ) : hR R σ J x y = 0 := by
  refine X_left hx fun b => ?_
  obtain ⟨d, rfl⟩ := mem_tensor_span_iff R P.e y hy
  rw [hermForm_sum_right_alt]
  simp [ht.ee]

/- English proof (translation)
Establish `h1 : ∀ b, hR R σ J (ratV (F` using `F) R (P.e b)) (lin R σ J s a) = 0 := fun b => by`. Rewrite using `[← lin_lin_inv R σ J s (ratV (F := F) R (P.e b)), hR_lin]`. Conclude with `X_left (parabolic_preserves_isotropic hs' (Submodule.subset_span ⟨b, Set.mem_univ _, rfl⟩)) ha.1`. Establish `h3 : hR R σ J (ratV (F` using `F) R P.z) (lin R σ J s a) = 0 := by`. Rewrite using `[← lin_lin_inv R σ J s (ratV (F := F) R P.z), hR_lin]`.

Establish `e : lin R σ J s⁻¹ (ratV (F` using `F) R P.z) = ratV (F := F) R P.z + (lin R σ J s⁻¹ (ratV (F := F) R P.z) - ratV (F := F) R P.z) := by abel`. Rewrite using `[e, hR_add_left, ha.2.2, X_left (parabolic_fixes_modulo_span hs') ha.1, add_zero]`. Rewrite using `[piRest_apply]`. Simplify using `only [h1, h3, zero_smul, Finset.sum_const_zero, add_zero, mul_zero]`. Conclude with `Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, Set.mem_univ _, rfl⟩)`.
-/
theorem parabolic_maps_complement (ht : FrameTab (σ := σ) (J := J) P c T) {s : HA R σ J} (hs' : s⁻¹ ∈ Ssub R σ J P)
    {a : Fin n → R ⊗[F] E} (ha : InW (σ := σ) (J := J) P a) :
    piRest (σ := σ) (J := J) P c (lin R σ J s a) ∈ spanR (F := F) R P.e Set.univ := by
  have h1 : ∀ b, hR R σ J (ratV (F := F) R (P.e b)) (lin R σ J s a) = 0 := fun b => by
    rw [← lin_lin_inv R σ J s (ratV (F := F) R (P.e b)), hR_lin]
    exact X_left (parabolic_preserves_isotropic hs' (Submodule.subset_span ⟨b, Set.mem_univ _, rfl⟩)) ha.1
  have h3 : hR R σ J (ratV (F := F) R P.z) (lin R σ J s a) = 0 := by
    rw [← lin_lin_inv R σ J s (ratV (F := F) R P.z), hR_lin]
    have e : lin R σ J s⁻¹ (ratV (F := F) R P.z) =
        ratV (F := F) R P.z + (lin R σ J s⁻¹ (ratV (F := F) R P.z) - ratV (F := F) R P.z) := by abel
    rw [e, hR_add_left, ha.2.2, X_left (parabolic_fixes_modulo_span hs') ha.1, add_zero]
  rw [piRest_apply]
  simp only [h1, h3, zero_smul, Finset.sum_const_zero, add_zero, mul_zero]
  exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, Set.mem_univ _, rfl⟩)

variable (P c)

def Lh (s : HA R σ J) : (Fin n → R ⊗[F] E) →ₗ[R ⊗[F] E] (Fin n → R ⊗[F] E) :=
  piW (σ := σ) (J := J) P c ∘ₗ lin R σ J s ∘ₗ piW (σ := σ) (J := J) P c + piRest (σ := σ) (J := J) P c

variable {P c}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem Lh_apply (s : HA R σ J) (v : Fin n → R ⊗[F] E) : Lh P c s v =
    piW (σ := σ) (J := J) P c (lin R σ J s (piW (σ := σ) (J := J) P c v)) + piRest (σ := σ) (J := J) P c v := rfl

/- English proof (translation)
Establish `e : piRest (σ` using `σ) (J := J) P c v = v - piW (σ := σ) (J := J) P c v := eq_sub_of_add_eq' (piW_add_rest (σ := σ) (J := J) P c v)`. Rewrite using `[e, map_sub, piW_inW_eq ht (piW_inW ht v), sub_self]`.
-/
theorem piW_piRest (ht : FrameTab (σ := σ) (J := J) P c T) (v : Fin n → R ⊗[F] E) :
    piW (σ := σ) (J := J) P c (piRest (σ := σ) (J := J) P c v) = 0 := by
  have e : piRest (σ := σ) (J := J) P c v = v - piW (σ := σ) (J := J) P c v :=
    eq_sub_of_add_eq' (piW_add_rest (σ := σ) (J := J) P c v)
  rw [e, map_sub, piW_inW_eq ht (piW_inW ht v), sub_self]

/- English proof (translation)
Use `set pu := piW (σ := σ) (J := J) P c u`. Use `set pv := piW (σ := σ) (J := J) P c v`. Establish `hpu` using `piW_inW (c := c) ht u`. Establish `hpv` using `piW_inW (c := c) ht v`. Establish `hmid : hR R σ J (piW (σ` using `σ) (J := J) P c (lin R σ J s pu)) (piW (σ := σ) (J := J) P c (lin R σ J s pv)) = hR R σ J pu pv := by`.

Establish `eA` using `piW_add_rest (σ := σ) (J := J) P c (lin R σ J s pu)`. Establish `eB` using `piW_add_rest (σ := σ) (J := J) P c (lin R σ J s pv)`. Establish `hxa` using `parabolic_maps_complement ht hs' hpu`. Establish `hxb` using `parabolic_maps_complement ht hs' hpv`. Establish `key : hR R σ J (lin R σ J s pu) (lin R σ J s pv) = hR R σ J (piW (σ` using `σ) (J := J) P c (lin R σ J s pu)) (piW (σ := σ) (J := J) P c (lin R σ J s pv)) := by conv_lhs => rw [← eA, ← eB]`.

Rewrite using `[hR_add_left, hermForm_add_right_bis, hermForm_add_right_bis, inW_left ht (piW_inW ht _), inW_right ht (piW_inW ht _), isotropic_span_hermForm_zero ht hxa hxb]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← key, hR_lin]`. Rewrite using `[Lh_apply, Lh_apply, hR_add_left, hermForm_add_right_bis, hermForm_add_right_bis, hmid, inW_left ht (piW_inW ht _), inW_right ht (piW_inW ht _)]`. Use `conv_rhs => rw [← piW_add_rest (σ := σ) (J := J) P c u, ← piW_add_rest (σ := σ) (J := J) P c v]`.

Rewrite using `[hR_add_left, hermForm_add_right_bis, hermForm_add_right_bis, inW_left ht hpu, inW_right ht hpv]`.
-/
theorem Lh_unitary (ht : FrameTab (σ := σ) (J := J) P c T) {s : HA R σ J} (hs' : s⁻¹ ∈ Ssub R σ J P)
    (u v : Fin n → R ⊗[F] E) : hR R σ J (Lh P c s u) (Lh P c s v) = hR R σ J u v := by
  set pu := piW (σ := σ) (J := J) P c u
  set pv := piW (σ := σ) (J := J) P c v
  have hpu := piW_inW (c := c) ht u
  have hpv := piW_inW (c := c) ht v

  have hmid : hR R σ J (piW (σ := σ) (J := J) P c (lin R σ J s pu)) (piW (σ := σ) (J := J) P c (lin R σ J s pv)) =
      hR R σ J pu pv := by
    have eA := piW_add_rest (σ := σ) (J := J) P c (lin R σ J s pu)
    have eB := piW_add_rest (σ := σ) (J := J) P c (lin R σ J s pv)
    have hxa := parabolic_maps_complement ht hs' hpu
    have hxb := parabolic_maps_complement ht hs' hpv
    have key : hR R σ J (lin R σ J s pu) (lin R σ J s pv) =
        hR R σ J (piW (σ := σ) (J := J) P c (lin R σ J s pu)) (piW (σ := σ) (J := J) P c (lin R σ J s pv)) := by
      conv_lhs => rw [← eA, ← eB]
      rw [hR_add_left, hermForm_add_right_bis, hermForm_add_right_bis,
        inW_left ht (piW_inW ht _), inW_right ht (piW_inW ht _), isotropic_span_hermForm_zero ht hxa hxb]
      ring
    rw [← key, hR_lin]
  rw [Lh_apply, Lh_apply, hR_add_left, hermForm_add_right_bis, hermForm_add_right_bis, hmid,
    inW_left ht (piW_inW ht _), inW_right ht (piW_inW ht _)]
  conv_rhs => rw [← piW_add_rest (σ := σ) (J := J) P c u, ← piW_add_rest (σ := σ) (J := J) P c v]
  rw [hR_add_left, hermForm_add_right_bis, hermForm_add_right_bis, inW_left ht hpu, inW_right ht hpv]

/- English proof (translation)
Use `set w := piW (σ := σ) (J := J) P c v`. Establish `hw` using `piW_inW (c := c) ht v`. Use `set p := piW (σ := σ) (J := J) P c (lin R σ J s⁻¹ w)`. Establish `hp` using `piW_inW (c := c) ht (lin R σ J s⁻¹ w)`. Establish `e1 : Lh P c s⁻¹ v = p + piRest (σ` using `σ) (J := J) P c v := rfl`.

Establish `e2 : piW (σ` using `σ) (J := J) P c (p + piRest (σ := σ) (J := J) P c v) = p := by`. Rewrite using `[map_add, piW_inW_eq ht hp, piW_piRest ht, add_zero]`. Establish `e3 : piRest (σ` using `σ) (J := J) P c (p + piRest (σ := σ) (J := J) P c v) = piRest (σ := σ) (J := J) P c v := by`. Use `piW_add_rest (σ := σ) (J := J) P c (p + piRest (σ := σ) (J := J) P c v)` as an intermediate fact. Rewrite `this` using `[e2]`.

Conclude with `add_left_cancel this`. Establish `hs'' : s⁻¹⁻¹ ∈ Ssub R σ J P` using `by rw [inv_inv]; exact hs`. Establish `hx` using `parabolic_maps_complement ht hs'' hw`. Establish `e4 : lin R σ J s p = w - lin R σ J s (piRest (σ` using `σ) (J := J) P c (lin R σ J s⁻¹ w)) := by`. Use `piW_add_rest (σ := σ) (J := J) P c (lin R σ J s⁻¹ w)` as an intermediate fact.

Establish `e5 : p = lin R σ J s⁻¹ w - piRest (σ` using `σ) (J := J) P c (lin R σ J s⁻¹ w) := eq_sub_of_add_eq this`. Rewrite using `[e5, map_sub, lin_lin_inv R σ J s w]`. Rewrite using `[e1, Lh_apply, e2, e3, e4, map_sub, piW_inW_eq ht hw, piW_X ht (parabolic_preserves_isotropic hs hx), sub_zero]`. Conclude with `piW_add_rest (σ := σ) (J := J) P c v`.
-/
theorem Lh_inv (ht : FrameTab (σ := σ) (J := J) P c T) {s : HA R σ J} (hs : s ∈ Ssub R σ J P)
    (hs' : s⁻¹ ∈ Ssub R σ J P) (v : Fin n → R ⊗[F] E) : Lh P c s (Lh P c s⁻¹ v) = v := by
  set w := piW (σ := σ) (J := J) P c v
  have hw := piW_inW (c := c) ht v
  set p := piW (σ := σ) (J := J) P c (lin R σ J s⁻¹ w)
  have hp := piW_inW (c := c) ht (lin R σ J s⁻¹ w)
  have e1 : Lh P c s⁻¹ v = p + piRest (σ := σ) (J := J) P c v := rfl
  have e2 : piW (σ := σ) (J := J) P c (p + piRest (σ := σ) (J := J) P c v) = p := by
    rw [map_add, piW_inW_eq ht hp, piW_piRest ht, add_zero]
  have e3 : piRest (σ := σ) (J := J) P c (p + piRest (σ := σ) (J := J) P c v) = piRest (σ := σ) (J := J) P c v := by
    have := piW_add_rest (σ := σ) (J := J) P c (p + piRest (σ := σ) (J := J) P c v)
    rw [e2] at this
    exact add_left_cancel this
  have hs'' : s⁻¹⁻¹ ∈ Ssub R σ J P := by rw [inv_inv]; exact hs
  have hx := parabolic_maps_complement ht hs'' hw
  have e4 : lin R σ J s p = w - lin R σ J s (piRest (σ := σ) (J := J) P c (lin R σ J s⁻¹ w)) := by
    have := piW_add_rest (σ := σ) (J := J) P c (lin R σ J s⁻¹ w)
    have e5 : p = lin R σ J s⁻¹ w - piRest (σ := σ) (J := J) P c (lin R σ J s⁻¹ w) :=
      eq_sub_of_add_eq this
    rw [e5, map_sub, lin_lin_inv R σ J s w]
  rw [e1, Lh_apply, e2, e3, e4, map_sub, piW_inW_eq ht hw, piW_X ht (parabolic_preserves_isotropic hs hx), sub_zero]
  exact piW_add_rest (σ := σ) (J := J) P c v

end Levi

end MassDataLevelSSteps
