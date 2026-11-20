import Formalism.SharpRestriction.GrowthBounds.TruncatedChains.RestTruncOfNil
import Formalism.SharpRestriction.GrowthBounds.TruncatedChains.PfTrunc

noncomputable section

open Finset

namespace Formalism.MainNotions.G.ExtremalProjector

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory

section Tens

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def zSub (K V : Type*) [Field K] [AddCommGroup V] [Module K V] {n : ℕ} (j : Fin n) : Submodule K (Fin n → V) :=
  LinearMap.ker (LinearMap.proj j : (Fin n → V) →ₗ[K] V)

/- English proof (translation)
Simplify using `[zSub]`.
-/
theorem mem_zSub (j : Fin n) (w : Fin n → V) : w ∈ zSub K V j ↔ w j = 0 := by
  simp [zSub]

/- English proof (translation)
Use `pf_intertw (tensOps E) E (LinearMap.proj a : (Fin n → V) →ₗ[K] V) ⊤ x y (fun _ _ => trivial) (fun w _ => ?_) (fun w => ?_) c T w trivial` and prove the remaining obligations. Rewrite using `[LinearMap.proj_apply, LinearMap.proj_apply, tensOps_apply, if_neg hx.symm, add_zero]`. Rewrite using `[LinearMap.proj_apply, LinearMap.proj_apply, tensOps_apply, if_neg hy.symm, add_zero]`.
-/
theorem ev_pf_ne (E : GLOps n K V) (a x y : Fin n) (hx : x ≠ a) (hy : y ≠ a) (c T : ℕ) (w : Fin n → V) :
    (pf (tensOps E) x y c T w) a = pf E x y c T (w a) := by
  refine pf_intertw (tensOps E) E (LinearMap.proj a : (Fin n → V) →ₗ[K] V) ⊤ x y (fun _ _ => trivial)
    (fun w _ => ?_) (fun w => ?_) c T w trivial
  · rw [LinearMap.proj_apply, LinearMap.proj_apply, tensOps_apply, if_neg hx.symm, add_zero]
  · rw [LinearMap.proj_apply, LinearMap.proj_apply, tensOps_apply, if_neg hy.symm, add_zero]

/- English proof (translation)
Use `pf_intertw (tensOps E) E (LinearMap.proj a : (Fin n → V) →ₗ[K] V) (zSub K V y) a y (fun w hw => ?_) (fun w hw => ?_) (fun w => ?_) c T w ((mem_zSub y w).2 hw)` and prove the remaining obligations. Rewrite `hw`, the goal using `[mem_zSub]`. Rewrite using `[tensOps_apply, if_neg hy, hw, map_zero, add_zero]`. Rewrite `hw` using `[mem_zSub]`. Rewrite using `[LinearMap.proj_apply, LinearMap.proj_apply, tensOps_apply, if_pos rfl, hw, add_zero]`.

Rewrite using `[LinearMap.proj_apply, LinearMap.proj_apply, tensOps_apply, if_neg hy.symm, add_zero]`.
-/
theorem ev_pf_a (E : GLOps n K V) (a y : Fin n) (hy : y ≠ a) (c T : ℕ) (w : Fin n → V) (hw : w y = 0) :
    (pf (tensOps E) a y c T w) a = pf E a y c T (w a) := by
  refine pf_intertw (tensOps E) E (LinearMap.proj a : (Fin n → V) →ₗ[K] V) (zSub K V y) a y (fun w hw => ?_)
    (fun w hw => ?_) (fun w => ?_) c T w ((mem_zSub y w).2 hw)
  · rw [mem_zSub] at hw ⊢
    rw [tensOps_apply, if_neg hy, hw, map_zero, add_zero]
  · rw [mem_zSub] at hw
    rw [LinearMap.proj_apply, LinearMap.proj_apply, tensOps_apply, if_pos rfl, hw, add_zero]
  · rw [LinearMap.proj_apply, LinearMap.proj_apply, tensOps_apply, if_neg hy.symm, add_zero]

/- English proof (translation)
Rewrite using `[← mem_zSub (K := K)]`. Use `pf_mem (tensOps E) (zSub K V j) x y (fun w hw => ?_) (fun w hw => ?_) c T w ((mem_zSub j w).2 hw)` and prove the remaining obligations. Rewrite `hw`, the goal using `[mem_zSub]`. Rewrite using `[tensOps_apply, if_neg hx, hw, map_zero, add_zero]`. Rewrite `hw`, the goal using `[mem_zSub]`.

Rewrite using `[tensOps_apply, if_neg hy, hw, map_zero, add_zero]`.
-/
theorem z_pf (E : GLOps n K V) (j x y : Fin n) (hx : j ≠ x) (hy : j ≠ y) (c T : ℕ) (w : Fin n → V) (hw : w j = 0) :
    (pf (tensOps E) x y c T w) j = 0 := by
  rw [← mem_zSub (K := K)]
  refine pf_mem (tensOps E) (zSub K V j) x y (fun w hw => ?_) (fun w hw => ?_) c T w ((mem_zSub j w).2 hw)
  · rw [mem_zSub] at hw ⊢
    rw [tensOps_apply, if_neg hx, hw, map_zero, add_zero]
  · rw [mem_zSub] at hw ⊢
    rw [tensOps_apply, if_neg hy, hw, map_zero, add_zero]

/- English proof (translation)
Establish `key : ∀ x y : Fin n, (x = b ∨ x = c) → (y = b ∨ y = c) → ∀ w ∈ zSub K V b ⊓ zSub K V c, tensOps E x y w ∈ zSub K V b ⊓ zSub K V c`. Introduce `x y _ hy w hw`. Rewrite `hw`, the goal using `[Submodule.mem_inf, mem_zSub, mem_zSub]`. Establish `hwy : w y = 0` using `by rcases hy with rfl | rfl; exacts [hw.1, hw.2]`. Rewrite using `[tensOps_apply, tensOps_apply, hw.1, hw.2, hwy]`.

Simplify using the standard rewrite rules. Use `pf_mem (tensOps E) (zSub K V b ⊓ zSub K V c) b c (key b c (Or.inl rfl) (Or.inr rfl)) (key c b (Or.inr rfl) (Or.inl rfl)) s T w (by rw [Submodule.mem_inf, mem_zSub, mem_zSub]; exact ⟨hb, hc⟩)` as an intermediate fact. Rewrite `this` using `[Submodule.mem_inf, mem_zSub, mem_zSub]`. Then use the resulting hypothesis.
-/
theorem zz_pf (E : GLOps n K V) (b c : Fin n) (s T : ℕ) (w : Fin n → V) (hb : w b = 0) (hc : w c = 0) :
    (pf (tensOps E) b c s T w) b = 0 ∧ (pf (tensOps E) b c s T w) c = 0 := by
  have key : ∀ x y : Fin n, (x = b ∨ x = c) → (y = b ∨ y = c) → ∀ w ∈ zSub K V b ⊓ zSub K V c,
      tensOps E x y w ∈ zSub K V b ⊓ zSub K V c := by
    intro x y _ hy w hw
    rw [Submodule.mem_inf, mem_zSub, mem_zSub] at hw ⊢
    have hwy : w y = 0 := by rcases hy with rfl | rfl; exacts [hw.1, hw.2]
    rw [tensOps_apply, tensOps_apply, hw.1, hw.2, hwy]
    simp
  have := pf_mem (tensOps E) (zSub K V b ⊓ zSub K V c) b c (key b c (Or.inl rfl) (Or.inr rfl))
    (key c b (Or.inr rfl) (Or.inl rfl)) s T w
    (by rw [Submodule.mem_inf, mem_zSub, mem_zSub]; exact ⟨hb, hc⟩)
  rwa [Submodule.mem_inf, mem_zSub, mem_zSub] at this

end Tens

/- English proof (translation)
Introduce `K V _ _ _ _ _ n E hE a b c hab hac hbc ν s t hs ht T hT x hx`. Establish `hA : IsGLRep (tensOps E)` using `tens_isGLRep hE`. Take `⟨T', hT0, hT2⟩ : ∃ T' : ℕ, T ≤ T' ∧ Module.finrank K (Fin n → V) ≤ T'` from `⟨max T (Module.finrank K (Fin n → V)), le_max_left _ _, le_max_right _ _⟩`. Establish `hT1 : Module.finrank K V ≤ T'` using `hT.trans hT0`. Establish `hw0 : (Pi.single a x : Fin n → V) ∈ weightSp (tensOps E) (ν + Pi.single a 1)` using `tens_single_wt E ν a x hx`.

Establish `e1 : (s : ℤ) = (ν + Pi.single a 1 : Fin n → ℤ) a - (ν + Pi.single a 1 : Fin n → ℤ) b + sg + 1`. Rewrite using `[Pi.add_apply, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hab.symm, hs]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : (t : ℤ) = (ν + Pi.single a 1 : Fin n → ℤ) b - (ν + Pi.single a 1 : Fin n → ℤ) c + ta + 1`.

Rewrite using `[Pi.add_apply, Pi.add_apply, Pi.single_eq_of_ne hab.symm, Pi.single_eq_of_ne hac.symm, ht]`. Expand and normalize the polynomial expressions, which then agree. Establish `key` using `h K (Fin n → V) n (tensOps E) hA a b c hab hac hbc (ν + Pi.single a 1) s t e1 e2 T' hT2 _ hw0`. Establish `key'` using `congrArg (fun w : Fin n → V => w a) key`. Establish `z0b : (Pi.single a x : Fin n → V) b = 0` using `by rw [Pi.single_apply, if_neg hab.symm]`.

Establish `z0c : (Pi.single a x : Fin n → V) c = 0` using `by rw [Pi.single_apply, if_neg hac.symm]`. Establish `z0a : (Pi.single a x : Fin n → V) a = x` using `by rw [Pi.single_apply, if_pos rfl]`. Take `⟨z1b, z1c⟩` from `zz_pf E b c t T' _ z0b z0c`. Establish `z2b` using `z_pf E b a c hab.symm hbc (s + t) T' _ z1b`. Establish `y1c` using `z_pf E c a b hac.symm hbc.symm s T' _ z0c`.

Rewrite `key'` using `[ev_pf_a E a b hab.symm s T' _ z2b, ev_pf_a E a c hac.symm (s + t) T' _ z1c, ev_pf_ne E a b c hab.symm hac.symm t T', ev_pf_ne E a b c hab.symm hac.symm t T', ev_pf_a E a c hac.symm (s + t) T' _ y1c, ev_pf_a E a b hab.symm s T' _ z0b, z0a]`. Rewrite using `[pf_trunc E hE a b hab s T T' hT hT1, pf_trunc E hE a c hac (s + t) T T' hT hT1, pf_trunc E hE b c hbc t T T' hT hT1]`. Conclude with `key'`.
-/
theorem ybat_step (sg ta : ℕ) (h : YBat sg ta) : YBat (sg + 1) ta := by
  intro K V _ _ _ _ _ n E hE a b c hab hac hbc ν s t hs ht T hT x hx
  have hA : IsGLRep (tensOps E) := tens_isGLRep hE
  obtain ⟨T', hT0, hT2⟩ : ∃ T' : ℕ, T ≤ T' ∧ Module.finrank K (Fin n → V) ≤ T' :=
    ⟨max T (Module.finrank K (Fin n → V)), le_max_left _ _, le_max_right _ _⟩
  have hT1 : Module.finrank K V ≤ T' := hT.trans hT0
  have hw0 : (Pi.single a x : Fin n → V) ∈ weightSp (tensOps E) (ν + Pi.single a 1) := tens_single_wt E ν a x hx
  have e1 : (s : ℤ) = (ν + Pi.single a 1 : Fin n → ℤ) a - (ν + Pi.single a 1 : Fin n → ℤ) b + sg + 1 := by
    rw [Pi.add_apply, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hab.symm, hs]
    push_cast
    ring
  have e2 : (t : ℤ) = (ν + Pi.single a 1 : Fin n → ℤ) b - (ν + Pi.single a 1 : Fin n → ℤ) c + ta + 1 := by
    rw [Pi.add_apply, Pi.add_apply, Pi.single_eq_of_ne hab.symm, Pi.single_eq_of_ne hac.symm, ht]
    ring
  have key := h K (Fin n → V) n (tensOps E) hA a b c hab hac hbc (ν + Pi.single a 1) s t e1 e2 T' hT2 _ hw0
  have key' := congrArg (fun w : Fin n → V => w a) key
  have z0b : (Pi.single a x : Fin n → V) b = 0 := by rw [Pi.single_apply, if_neg hab.symm]
  have z0c : (Pi.single a x : Fin n → V) c = 0 := by rw [Pi.single_apply, if_neg hac.symm]
  have z0a : (Pi.single a x : Fin n → V) a = x := by rw [Pi.single_apply, if_pos rfl]
  obtain ⟨z1b, z1c⟩ := zz_pf E b c t T' _ z0b z0c
  have z2b := z_pf E b a c hab.symm hbc (s + t) T' _ z1b
  have y1c := z_pf E c a b hac.symm hbc.symm s T' _ z0c
  rw [ev_pf_a E a b hab.symm s T' _ z2b, ev_pf_a E a c hac.symm (s + t) T' _ z1c,
    ev_pf_ne E a b c hab.symm hac.symm t T', ev_pf_ne E a b c hab.symm hac.symm t T',
    ev_pf_a E a c hac.symm (s + t) T' _ y1c, ev_pf_a E a b hab.symm s T' _ z0b, z0a] at key'
  rw [pf_trunc E hE a b hab s T T' hT hT1, pf_trunc E hE a c hac (s + t) T T' hT hT1,
    pf_trunc E hE b c hbc t T T' hT hT1]
  exact key'

/- English proof (translation)
Establish `h1 : ∀ sg, YBat sg 0`. Introduce `sg`. Proceed by induction on `sg with`. Consider the case `zero => exact base`. Consider the case `succ k ih => exact ybat_step k 0 ih`.

Introduce `sg ta`. Proceed by induction on `ta with`. Consider the case `zero => exact h1 sg`. Consider the case `succ k ih => exact symm _ _ (ybat_step k sg (symm _ _ ih))`.
-/
theorem restYB_of (base : YBat 0 0) (symm : ∀ sg ta, YBat sg ta → YBat ta sg) : RestYB := by
  have h1 : ∀ sg, YBat sg 0 := by
    intro sg
    induction sg with
    | zero => exact base
    | succ k ih => exact ybat_step k 0 ih
  intro sg ta
  induction ta with
  | zero => exact h1 sg
  | succ k ih => exact symm _ _ (ybat_step k sg (symm _ _ ih))

end Formalism.MainNotions.G.ExtremalProjector
