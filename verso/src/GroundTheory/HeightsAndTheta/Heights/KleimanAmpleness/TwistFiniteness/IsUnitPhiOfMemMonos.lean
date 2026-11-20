import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistFiniteness.Graded
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial AddMonoidAlgebra

noncomputable section

universe u w

namespace TwistFin

variable {Ω : Type w} [Field Ω] {N r : ℕ}
variable (x : Fin (N + 1) → Ω) (η : Fin (r + 1) → Ω) (S : Type u) [CommRing S] [Algebra S Ω]
variable (n0 : ℕ) (d0 : Fin n0 → ℤ) (g0 : Fin n0 → Ω)

/- English proof (translation)
Proceed by induction on `hs using Submonoid.closure_induction with`. Consider the case `mem a ha`. Take `⟨i, hi, rfl⟩` from `ha`. Rewrite using `[phi_X]`. Use `isUnit_iff_exists_inv.mpr ⟨single ((-1 : ℤ), (0 : ℤ)) (x i)⁻¹, ?_⟩` and prove the remaining obligations.

Rewrite using `[single_mul_single, mul_inv_cancel₀ (hI i (Finset.mem_coe.mp hi)), AddMonoidAlgebra.one_def]`. Simplify using `only [Prod.mk_add_mk, add_neg_cancel, add_zero]`. Both sides reduce to the same expression. Consider the case `one => rw [map_one]`. Conclude with `isUnit_one`.

Consider the case `mul a b _ _ ha hb => rw [map_mul]`. Conclude with `ha.mul hb`.
-/
theorem isUnit_phi_of_mem_monos {I : Finset (Fin (N + 1))} (hI : ∀ i ∈ I, x i ≠ 0)
    {s : Poly (Sy S r) N} (hs : s ∈ monos I) : IsUnit (phi x η S s) := by
  induction hs using Submonoid.closure_induction with
  | mem a ha =>
    obtain ⟨i, hi, rfl⟩ := ha
    rw [phi_X]
    refine isUnit_iff_exists_inv.mpr ⟨single ((-1 : ℤ), (0 : ℤ)) (x i)⁻¹, ?_⟩
    rw [single_mul_single, mul_inv_cancel₀ (hI i (Finset.mem_coe.mp hi)), AddMonoidAlgebra.one_def]
    simp only [Prod.mk_add_mk, add_neg_cancel, add_zero]
    rfl
  | one => rw [map_one]; exact isUnit_one
  | mul a b _ _ ha hb => rw [map_mul]; exact ha.mul hb

/- English proof (translation)
Rewrite using `[Module.End.isUnit_iff]`. Take `⟨u, hu⟩` from `isUnit_phi_of_mem_monos x η S hI s.2`. Prove the components needed by the constructor for the conclusion. Introduce `a b hab`. Simplify using `only [Module.algebraMap_end_apply] at hab`.

Establish `h1 : phi x η S s * toA x η a = phi x η S s * toA x η b`. Rewrite using `[← toA_smulP, ← toA_smulP, hab]`. Rewrite `h1` using `[← hu]`. Conclude with `(toA x η).injective ((Units.mul_right_inj u).mp h1)`. Introduce `b`.

Use `⟨(toA x η).symm (↑u⁻¹ * toA x η b), ?_⟩` and prove the remaining obligations. Simplify using `only [Module.algebraMap_end_apply]`. Apply `(toA x η).injective` to reduce the goal to its premises. Rewrite using `[toA_smulP, AddEquiv.apply_symm_apply, ← hu, Units.mul_inv_cancel_left]`.
-/
theorem isUnit_end {I : Finset (Fin (N + 1))} (hI : ∀ i ∈ I, x i ≠ 0) (s : monos (S := Sy S r) I) :
    IsUnit (algebraMap (Poly (Sy S r) N) (Module.End (Poly (Sy S r) N) (Amb x η)) s) := by
  rw [Module.End.isUnit_iff]
  obtain ⟨u, hu⟩ := isUnit_phi_of_mem_monos x η S hI s.2
  constructor
  · intro a b hab
    simp only [Module.algebraMap_end_apply] at hab
    have h1 : phi x η S s * toA x η a = phi x η S s * toA x η b := by
      rw [← toA_smulP, ← toA_smulP, hab]
    rw [← hu] at h1
    exact (toA x η).injective ((Units.mul_right_inj u).mp h1)
  · intro b
    refine ⟨(toA x η).symm (↑u⁻¹ * toA x η b), ?_⟩
    simp only [Module.algebraMap_end_apply]
    apply (toA x η).injective
    rw [toA_smulP, AddEquiv.apply_symm_apply, ← hu, Units.mul_inv_cancel_left]

def locL (I : Finset (Fin (N + 1))) (hI : ∀ i ∈ I, x i ≠ 0) :
    LocMod (Sy S r) N (TMod x η S n0 d0 g0) I →ₗ[Poly (Sy S r) N] Amb x η :=
  LocalizedModule.lift _ (TMod x η S n0 d0 g0).subtype (isUnit_end x η S hI)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem locL_mk (I : Finset (Fin (N + 1))) (hI : ∀ i ∈ I, x i ≠ 0) (m : TMod x η S n0 d0 g0)
    (s : monos (S := Sy S r) I) :
    locL x η S n0 d0 g0 I hI
      (LocalizedModule.mk m s : LocalizedModule (monos (S := Sy S r) I) (TMod x η S n0 d0 g0)) =
      (((isUnit_end x η S hI s).unit⁻¹ : (Module.End (Poly (Sy S r) N) (Amb x η))ˣ) :
        Module.End (Poly (Sy S r) N) (Amb x η)) (m : Amb x η) :=
  rfl

/- English proof (translation)
Rewrite using `[← toA_smulP]`. Use `congr 1`. Rewrite using `[locL_mk]`. Use `set e := (isUnit_end x η S hI s).unit`. Establish `hspec : (e : Module.End (Poly (Sy S r) N) (Amb x η)) = algebraMap (Poly (Sy S r) N) (Module.End (Poly (Sy S r) N) (Amb x η)) (s : Poly (Sy S r) N)` using `IsUnit.unit_spec _`.

Establish `h1 : (e : Module.End (Poly (Sy S r) N) (Amb x η)) (((e⁻¹ : (Module.End (Poly (Sy S r) N) (Amb x η))ˣ) : Module.End (Poly (Sy S r) N) (Amb x η)) (m : Amb x η)) = (m : Amb x η)`. Rewrite using `[← Module.End.mul_apply, Units.mul_inv, Module.End.one_apply]`. Rewrite `h1` using `[hspec, Module.algebraMap_end_apply]`. Conclude with `h1`.
-/
theorem phi_mul_locL_mk (I : Finset (Fin (N + 1))) (hI : ∀ i ∈ I, x i ≠ 0) (m : TMod x η S n0 d0 g0)
    (s : monos (S := Sy S r) I) :
    phi x η S s * toA x η (locL x η S n0 d0 g0 I hI
      (LocalizedModule.mk m s : LocalizedModule (monos (S := Sy S r) I) (TMod x η S n0 d0 g0))) =
      toA x η m := by
  rw [← toA_smulP]
  congr 1
  rw [locL_mk]
  set e := (isUnit_end x η S hI s).unit
  have hspec : (e : Module.End (Poly (Sy S r) N) (Amb x η)) =
      algebraMap (Poly (Sy S r) N) (Module.End (Poly (Sy S r) N) (Amb x η)) (s : Poly (Sy S r) N) :=
    IsUnit.unit_spec _
  have h1 : (e : Module.End (Poly (Sy S r) N) (Amb x η))
      (((e⁻¹ : (Module.End (Poly (Sy S r) N) (Amb x η))ˣ) : Module.End (Poly (Sy S r) N) (Amb x η))
        (m : Amb x η)) = (m : Amb x η) := by
    rw [← Module.End.mul_apply, Units.mul_inv, Module.End.one_apply]
  rw [hspec, Module.algebraMap_end_apply] at h1
  exact h1

/- English proof (translation)
Take `⟨u, hu⟩` from `isUnit_phi_of_mem_monos x η S hI s.2`. Apply `(toA x η).injective` to reduce the goal to its premises. Establish `h1` using `phi_mul_locL_mk x η S n0 d0 g0 I hI m s`. Rewrite `h1` using `[← ha, ← hu]`. Conclude with `(Units.mul_right_inj u).mp h1`.
-/
theorem locL_mk_eq (I : Finset (Fin (N + 1))) (hI : ∀ i ∈ I, x i ≠ 0) (m : TMod x η S n0 d0 g0)
    (s : monos (S := Sy S r) I) (a : Amb x η) (ha : phi x η S s * toA x η a = toA x η m) :
    locL x η S n0 d0 g0 I hI
      (LocalizedModule.mk m s : LocalizedModule (monos (S := Sy S r) I) (TMod x η S n0 d0 g0)) = a := by
  obtain ⟨u, hu⟩ := isUnit_phi_of_mem_monos x η S hI s.2
  apply (toA x η).injective
  have h1 := phi_mul_locL_mk x η S n0 d0 g0 I hI m s
  rw [← ha, ← hu] at h1
  exact (Units.mul_right_inj u).mp h1

/- English proof (translation)
Introduce `a b hab`. Express the relevant statement in the definitionally equal form `LocalizedModule (monos (S := Sy S r) I) (TMod x η S n0 d0 g0) at a b`. Proceed by induction on `a using LocalizedModule.induction_on with`. Consider the case `h m s`. Proceed by induction on `b using LocalizedModule.induction_on with`.

Consider the case `h m' s' => show (LocalizedModule.mk m s : LocalizedModule (monos (S := Sy S r) I) (TMod x η S n0 d0 g0)) = LocalizedModule.mk m' s'`. Rewrite using `[LocalizedModule.mk_eq]`. Use `⟨1, ?_⟩` and prove the remaining obligations. Establish `h1` using `phi_mul_locL_mk x η S n0 d0 g0 I hI m s`. Establish `h2` using `phi_mul_locL_mk x η S n0 d0 g0 I hI m' s'`.

Simplify using `only [Submonoid.smul_def, one_smul]`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `(toA x η).injective` to reduce the goal to its premises. Rewrite using `[Submodule.coe_smul, Submodule.coe_smul, toA_smulP, toA_smulP, ← h1, ← h2, hab]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem locL_injective (I : Finset (Fin (N + 1))) (hI : ∀ i ∈ I, x i ≠ 0) :
    Function.Injective (locL x η S n0 d0 g0 I hI) := by
  intro a b hab
  change LocalizedModule (monos (S := Sy S r) I) (TMod x η S n0 d0 g0) at a b
  induction a using LocalizedModule.induction_on with
  | h m s =>
    induction b using LocalizedModule.induction_on with
    | h m' s' =>
      show (LocalizedModule.mk m s : LocalizedModule (monos (S := Sy S r) I) (TMod x η S n0 d0 g0)) =
        LocalizedModule.mk m' s'
      rw [LocalizedModule.mk_eq]
      refine ⟨1, ?_⟩
      have h1 := phi_mul_locL_mk x η S n0 d0 g0 I hI m s
      have h2 := phi_mul_locL_mk x η S n0 d0 g0 I hI m' s'
      simp only [Submonoid.smul_def, one_smul]
      apply Subtype.ext
      apply (toA x η).injective
      rw [Submodule.coe_smul, Submodule.coe_smul, toA_smulP, toA_smulP, ← h1, ← h2, hab]
      ring

/- English proof (translation)
Express the relevant statement in the definitionally equal form `LocalizedModule (monos (S := Sy S r) I) (TMod x η S n0 d0 g0) at z`. Proceed by induction on `z using LocalizedModule.induction_on with`. Consider the case `h m s`. Rewrite using `[locRes_mk]`. Apply `locL_mk_eq` to reduce the goal to its premises.

Conclude with `phi_mul_locL_mk x η S n0 d0 g0 I _ m s`.
-/
theorem locL_locRes {I J : Finset (Fin (N + 1))} (h : I ⊆ J) (hJ : ∀ i ∈ J, x i ≠ 0)
    (z : LocMod (Sy S r) N (TMod x η S n0 d0 g0) I) :
    locL x η S n0 d0 g0 J hJ (locRes h z) = locL x η S n0 d0 g0 I (fun i hi => hJ i (h hi)) z := by
  change LocalizedModule (monos (S := Sy S r) I) (TMod x η S n0 d0 g0) at z
  induction z using LocalizedModule.induction_on with
  | h m s =>
    rw [locRes_mk]
    apply locL_mk_eq
    exact phi_mul_locL_mk x η S n0 d0 g0 I _ m s

/- English proof (translation)
Establish `hkill : ∀ m : TMod x η S n0 d0 g0, (X i : Poly (Sy S r) N) • m = 0`. Introduce `m`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `(toA x η).injective` to reduce the goal to its premises. Rewrite using `[Submodule.coe_smul, toA_smulP, phi_X, hx, single_zero, zero_mul, Submodule.coe_zero, map_zero]`.

Use `⟨fun a b => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `LocalizedModule (monos (S := Sy S r) I) (TMod x η S n0 d0 g0) at a b`. Proceed by induction on `a using LocalizedModule.induction_on with`. Consider the case `h m s`. Proceed by induction on `b using LocalizedModule.induction_on with`.

Consider the case `h m' s' => show (LocalizedModule.mk m s : LocalizedModule (monos (S := Sy S r) I) (TMod x η S n0 d0 g0)) = LocalizedModule.mk m' s'`. Rewrite using `[LocalizedModule.mk_eq]`. Use `⟨⟨X i, X_mem_monos hi⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(X i : Poly (Sy S r) N) • (s' : Poly (Sy S r) N) • m = (X i : Poly (Sy S r) N) • (s : Poly (Sy S r) N) • m'`. Rewrite using `[smul_comm, hkill, smul_zero, smul_comm, hkill, smul_zero]`.
-/
theorem subsingleton_loc {I : Finset (Fin (N + 1))} {i : Fin (N + 1)} (hi : i ∈ I) (hx : x i = 0) :
    Subsingleton (LocMod (Sy S r) N (TMod x η S n0 d0 g0) I) := by
  have hkill : ∀ m : TMod x η S n0 d0 g0, (X i : Poly (Sy S r) N) • m = 0 := by
    intro m
    apply Subtype.ext
    apply (toA x η).injective
    rw [Submodule.coe_smul, toA_smulP, phi_X, hx, single_zero, zero_mul, Submodule.coe_zero, map_zero]
  refine ⟨fun a b => ?_⟩
  change LocalizedModule (monos (S := Sy S r) I) (TMod x η S n0 d0 g0) at a b
  induction a using LocalizedModule.induction_on with
  | h m s =>
    induction b using LocalizedModule.induction_on with
    | h m' s' =>
      show (LocalizedModule.mk m s : LocalizedModule (monos (S := Sy S r) I) (TMod x η S n0 d0 g0)) =
        LocalizedModule.mk m' s'
      rw [LocalizedModule.mk_eq]
      refine ⟨⟨X i, X_mem_monos hi⟩, ?_⟩
      change (X i : Poly (Sy S r) N) • (s' : Poly (Sy S r) N) • m =
        (X i : Poly (Sy S r) N) • (s : Poly (Sy S r) N) • m'
      rw [smul_comm, hkill, smul_zero, smul_comm, hkill, smul_zero]

def idx0 (i : Fin (N + 1)) : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) 0 :=
  ⟨⟨{i}, Finset.singleton_nonempty i, Finset.subset_univ _⟩, Finset.card_singleton i⟩

/- English proof (translation)
Introduce `i hi`. Rewrite using `[Finset.mem_singleton.mp hi]`. Conclude with `hi0`.
-/
theorem mem_chartCell_ne_zero {i0 : Fin (N + 1)} (hi0 : x i0 ≠ 0) : ∀ i ∈ (idx0 i0).1.1, x i ≠ 0 := by
  intro i hi
  rw [Finset.mem_singleton.mp hi]
  exact hi0

def evalIdx (i0 : Fin (N + 1)) (hi0 : x i0 ≠ 0) :
    Cech.cocyDeg (locSys (Sy S r) N (TMod x η S n0 d0 g0)) (degLoc (tgraded x η S n0 d0 g0) 0) locResS 0
      →ₗ[Sy S r] Amb x η where
  toFun z := locL x η S n0 d0 g0 (idx0 i0).1.1 (mem_chartCell_ne_zero x hi0)
    ((z : Cech.Cochain (locSys (Sy S r) N (TMod x η S n0 d0 g0)) 0) (idx0 i0))
  map_add' a b := by
    rw [Submodule.coe_add, Pi.add_apply, map_add]
  map_smul' c z := by
    rw [Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply]
    exact LinearMap.map_smul_of_tower _ _ _

def readChartH0 (i0 : Fin (N + 1)) (hi0 : x i0 ≠ 0) :
    cohom (tgraded x η S n0 d0 g0) 0 0 →ₗ[Sy S r] Amb x η :=
  Submodule.liftQ _ (evalIdx x η S n0 d0 g0 i0 hi0) (by
      intro z hz
      have h0 : (z : Cech.Cochain (locSys (Sy S r) N (TMod x η S n0 d0 g0)) 0) = 0 := by
        simpa [Cech.bdryDeg] using hz
      rw [LinearMap.mem_ker]
      change locL x η S n0 d0 g0 (idx0 i0).1.1 (mem_chartCell_ne_zero x hi0)
        ((z : Cech.Cochain (locSys (Sy S r) N (TMod x η S n0 d0 g0)) 0) (idx0 i0)) = 0
      rw [h0, Pi.zero_apply, map_zero])

/- English proof (translation)
Set `v : ∀ I : StdCell N, LocMod (Sy S r) N (TMod x η S n0 d0 g0) I.1` to `fun I => if hI : ∀ i ∈ I.1, x i ≠ 0 then (ht I hI).choose else 0`. Establish `hv : ∀ (I J : StdCell N) (h : I.1 ⊆ J.1), locResS I J h (v I) = v J`. Introduce `I J h`. Distinguish the cases in `hJ : ∀ i ∈ J.1, x i ≠ 0`. Establish `hI : ∀ i ∈ I.1, x i ≠ 0` using `fun i hi => hJ i (h hi)`.

Apply `locL_injective x η S n0 d0 g0 J.1 hJ` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `locL x η S n0 d0 g0 J.1 hJ (locRes h (v I)) = locL x η S n0 d0 g0 J.1 hJ (v J)`. Rewrite using `[locL_locRes]`. Simplify using `only [v, dif_pos hI, dif_pos hJ]`. Rewrite using `[(ht I hI).choose_spec.2, (ht J hJ).choose_spec.2]`.

Use `push Not at hJ`. Take `⟨i, hi, hx⟩` from `hJ`. Use `subsingleton_loc x η S n0 d0 g0 hi hx` as an intermediate fact. Conclude with `Subsingleton.elim _ _`. Establish `hcoc : (fun I : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) 0 => v I.1) ∈ Cech.cocyDeg (locSys (Sy S r) N (TMod x η S n0 d0 g0)) (degLoc (tgraded x η S n0 d0 g0) 0) locResS 0`.

Use `⟨Cech.d_zero_of_compat v hv, fun I _ => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hI : ∀ i ∈ I.1.1, x i ≠ 0`. Simplify using `only [v, dif_pos hI]`. Conclude with `(ht I.1 hI).choose_spec.1`. Simplify using `only [v, dif_neg hI]`.

Conclude with `zero_mem _`. Use `⟨Submodule.Quotient.mk ⟨_, hcoc⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `evalIdx x η S n0 d0 g0 i0 hi0 ⟨_, hcoc⟩ = t`. Express the relevant statement in the definitionally equal form `locL x η S n0 d0 g0 (idx0 i0).1.1 (mem_chartCell_ne_zero x hi0) (v (idx0 i0).1) = t`. Simplify using `only [v, dif_pos (mem_chartCell_ne_zero x hi0)]`.

Conclude with `(ht _ (mem_chartCell_ne_zero x hi0)).choose_spec.2`.
-/
theorem mem_range_readChartH0 (i0 : Fin (N + 1)) (hi0 : x i0 ≠ 0) (t : Amb x η)
    (ht : ∀ (I : StdCell N) (hI : ∀ i ∈ I.1, x i ≠ 0), ∃ z ∈ degLoc (tgraded x η S n0 d0 g0) 0 I,
      locL x η S n0 d0 g0 I.1 hI z = t) :
    t ∈ LinearMap.range (readChartH0 x η S n0 d0 g0 i0 hi0) := by
  classical
  let v : ∀ I : StdCell N, LocMod (Sy S r) N (TMod x η S n0 d0 g0) I.1 := fun I =>
    if hI : ∀ i ∈ I.1, x i ≠ 0 then (ht I hI).choose else 0
  have hv : ∀ (I J : StdCell N) (h : I.1 ⊆ J.1), locResS I J h (v I) = v J := by
    intro I J h
    by_cases hJ : ∀ i ∈ J.1, x i ≠ 0
    · have hI : ∀ i ∈ I.1, x i ≠ 0 := fun i hi => hJ i (h hi)
      apply locL_injective x η S n0 d0 g0 J.1 hJ
      change locL x η S n0 d0 g0 J.1 hJ (locRes h (v I)) = locL x η S n0 d0 g0 J.1 hJ (v J)
      rw [locL_locRes]
      simp only [v, dif_pos hI, dif_pos hJ]
      rw [(ht I hI).choose_spec.2, (ht J hJ).choose_spec.2]
    · push Not at hJ
      obtain ⟨i, hi, hx⟩ := hJ
      have := subsingleton_loc x η S n0 d0 g0 hi hx
      exact Subsingleton.elim _ _
  have hcoc : (fun I : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) 0 => v I.1) ∈
      Cech.cocyDeg (locSys (Sy S r) N (TMod x η S n0 d0 g0)) (degLoc (tgraded x η S n0 d0 g0) 0)
        locResS 0 := by
    refine ⟨Cech.d_zero_of_compat v hv, fun I _ => ?_⟩
    by_cases hI : ∀ i ∈ I.1.1, x i ≠ 0
    · simp only [v, dif_pos hI]; exact (ht I.1 hI).choose_spec.1
    · simp only [v, dif_neg hI]; exact zero_mem _
  refine ⟨Submodule.Quotient.mk ⟨_, hcoc⟩, ?_⟩
  change evalIdx x η S n0 d0 g0 i0 hi0 ⟨_, hcoc⟩ = t
  change locL x η S n0 d0 g0 (idx0 i0).1.1 (mem_chartCell_ne_zero x hi0) (v (idx0 i0).1) = t
  simp only [v, dif_pos (mem_chartCell_ne_zero x hi0)]
  exact (ht _ (mem_chartCell_ne_zero x hi0)).choose_spec.2

end TwistFin

end

end GroundTheory.Heights₂.Heights.Kleiman
