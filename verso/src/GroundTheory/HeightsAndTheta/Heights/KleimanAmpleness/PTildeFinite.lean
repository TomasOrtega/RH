import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TildeFiniteSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTildeTail
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCechTransport
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section Compare

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

variable (S x) in
open Classical in

def supportRes (I J : StdCell N) (_h : I.1 ⊆ J.1) : ConeLaurent S x →ₗ[S] ConeLaurent S x :=
  if J.1 ⊆ support x then LinearMap.id else 0

/- English proof (translation)
The claim follows from `if_pos hJ`.
-/
theorem supportRes_of_subset {I J : StdCell N} (h : I.1 ⊆ J.1) (hJ : J.1 ⊆ support x) :
    supportRes S x I J h = LinearMap.id := if_pos hJ

/- English proof (translation)
The claim follows from `if_neg hJ`.
-/
theorem supportRes_of_not {I J : StdCell N} (h : I.1 ⊆ J.1) (hJ : ¬ J.1 ⊆ support x) :
    supportRes S x I J h = 0 := if_neg hJ

def toChartIdx {n : ℕ} (K : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) n) (h : K.1.1 ⊆ support x) :
    Cech.Idx (support x) n :=
  ⟨⟨K.1.1, K.1.2.1, h⟩, K.2⟩

def ofChartIdx {n : ℕ} (K : Cech.Idx (support x) n) : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) n :=
  ⟨⟨K.1.1, K.1.2.1, Finset.subset_univ _⟩, K.2⟩

variable (M : FinGradedSub (S := S) (x := x) Ω) (c : ℤ)

def FinGradedSub.cellConeS (I : StdCell N) : LocMod S N M.coneSub I.1 →ₗ[S] ConeLaurent S x :=
  (M.cellCone I).restrictScalars S

/- English proof (translation)
The claim follows from `dif_neg h`.
-/
theorem FinGradedSub.cellCone_of_not {I : StdCell N} (h : ¬ I.1 ⊆ support x) : M.cellCone I = 0 :=
  dif_neg h

/- English proof (translation)
Distinguish the cases in `h : I.1 ⊆ support x`. Express the relevant statement in the definitionally equal form `Function.Injective (M.cellCone I)`. Rewrite using `[M.cellCone_of_subset h]`. Conclude with `locCone_injective M I.1 h`. Choose the witnesses or unpack the hypotheses as in `⟨i, hiI, hi⟩ : ∃ i ∈ I.1, x i = 0 := by`.

Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Conclude with `h fun i hi => (mem_support x).mpr (hne i hi)`. Use `locMod_subsingleton M hiI hi` as an intermediate fact. Conclude with `Function.injective_of_subsingleton _`.
-/
theorem FinGradedSub.cellConeS_injective (I : StdCell N) : Function.Injective (M.cellConeS I) := by
  by_cases h : I.1 ⊆ support x
  · change Function.Injective (M.cellCone I)
    rw [M.cellCone_of_subset h]
    exact locCone_injective M I.1 h
  · obtain ⟨i, hiI, hi⟩ : ∃ i ∈ I.1, x i = 0 := by
      by_contra hne
      push Not at hne
      exact h fun i hi => (mem_support x).mpr (hne i hi)
    have := locMod_subsingleton M hiI hi
    exact Function.injective_of_subsingleton _

/- English proof (translation)
Distinguish the cases in `hJ : J.1 ⊆ support x`. Rewrite using `[supportRes_of_subset h hJ, LinearMap.id_apply]`. Express the relevant statement in the definitionally equal form `M.cellCone J (locRes h m) = M.cellCone I m`. Rewrite using `[M.cellCone_of_subset hJ, M.cellCone_of_subset (h.trans hJ)]`. Conclude with `locCone_locRes M h hJ m`.

Rewrite using `[supportRes_of_not h hJ, LinearMap.zero_apply]`. Express the relevant statement in the definitionally equal form `M.cellCone J _ = 0`. Rewrite using `[M.cellCone_of_not hJ]`. Both sides reduce to the same expression.
-/
theorem FinGradedSub.cellConeS_res (I J : StdCell N) (h : I.1 ⊆ J.1) (m : LocMod S N M.coneSub I.1) :
    M.cellConeS J (locResS I J h m) = supportRes S x I J h (M.cellConeS I m) := by
  by_cases hJ : J.1 ⊆ support x
  · rw [supportRes_of_subset h hJ, LinearMap.id_apply]
    change M.cellCone J (locRes h m) = M.cellCone I m
    rw [M.cellCone_of_subset hJ, M.cellCone_of_subset (h.trans hJ)]
    exact locCone_locRes M h hJ m
  · rw [supportRes_of_not h hJ, LinearMap.zero_apply]
    change M.cellCone J _ = 0
    rw [M.cellCone_of_not hJ]
    rfl

def FinGradedSub.coneDeg (I : StdCell N) : Submodule S (ConeLaurent S x) :=
  (degLoc M.coneGraded c I).map (M.cellConeS I)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hy`. Take `⟨z, hz, rfl⟩` from `Submodule.mem_map.mp hy`. Take `⟨v, hv, hzv⟩` from `locCone_degLoc M c I hI hz`. Use `⟨v, hv, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `M.cellCone I z = _`. Rewrite using `[M.cellCone_of_subset hI]`. Conclude with `hzv`. Introduce and unpack `⟨v, hv, rfl⟩`. Take `⟨z, hz, hzv⟩` from `exists_locCone_eq M c I hI hv`.

Use `Submodule.mem_map.mpr ⟨z, hz, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `M.cellCone I z = _`. Rewrite using `[M.cellCone_of_subset hI]`. Conclude with `hzv`.
-/
theorem FinGradedSub.mem_coneDeg_of_subset {I : StdCell N} (hI : I.1 ⊆ support x) {y : ConeLaurent S x} :
    y ∈ M.coneDeg c I ↔ ∃ v ∈ M.tilde c ⟨I.1, I.2.1, hI⟩, y = coneSingle S x c v := by
  constructor
  · intro hy
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hy
    obtain ⟨v, hv, hzv⟩ := locCone_degLoc M c I hI hz
    refine ⟨v, hv, ?_⟩
    change M.cellCone I z = _
    rw [M.cellCone_of_subset hI]
    exact hzv
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨z, hz, hzv⟩ := exists_locCone_eq M c I hI hv
    refine Submodule.mem_map.mpr ⟨z, hz, ?_⟩
    change M.cellCone I z = _
    rw [M.cellCone_of_subset hI]
    exact hzv

/- English proof (translation)
Take `⟨z, -, rfl⟩` from `Submodule.mem_map.mp hy`. Express the relevant statement in the definitionally equal form `M.cellCone I z = 0`. Rewrite using `[M.cellCone_of_not hI]`. Both sides reduce to the same expression.
-/
theorem FinGradedSub.eq_zero_of_mem_coneDeg {I : StdCell N} (hI : ¬ I.1 ⊆ support x) {y : ConeLaurent S x}
    (hy : y ∈ M.coneDeg c I) : y = 0 := by
  obtain ⟨z, -, rfl⟩ := Submodule.mem_map.mp hy
  change M.cellCone I z = 0
  rw [M.cellCone_of_not hI]
  rfl

def FinGradedSub.tildeCone (I : Chart x) : (M.tildeSys c).sub I →ₗ[S] ConeLaurent S x :=
  (coneSingle S x c).comp
    { toFun := fun y => (y : Ω), map_add' := fun _ _ => rfl,
      map_smul' := fun a y => by rw [RingHom.id_apply]; exact Submodule.coe_smul_of_tower a y }

open Classical in

def FinGradedSub.embedC (n : ℕ) :
    Cech.Cochain (fun I : Chart x => (M.tildeSys c).sub I) n →ₗ[S]
      Cech.Cochain (fun _ : StdCell N => ConeLaurent S x) n where
  toFun s K := if h : K.1.1 ⊆ support x then M.tildeCone c _ (s (toChartIdx K h)) else 0
  map_add' s t := by
    funext K
    by_cases h : K.1.1 ⊆ support x
    · simp only [dif_pos h, Pi.add_apply, map_add]
    · simp only [dif_neg h, Pi.add_apply, add_zero]
  map_smul' a s := by
    funext K
    by_cases h : K.1.1 ⊆ support x
    · simp only [dif_pos h, Pi.smul_apply, map_smul, RingHom.id_apply]
    · simp only [dif_neg h, Pi.smul_apply, smul_zero, RingHom.id_apply]

/- English proof (translation)
Simplify using `only [FinGradedSub.embedC, LinearMap.coe_mk, AddHom.coe_mk]`. Rewrite using `[dif_pos h]`. Both sides reduce to the same expression.
-/
theorem FinGradedSub.embedC_of_subset {n : ℕ} (s : Cech.Cochain (fun I : Chart x => (M.tildeSys c).sub I) n)
    (K : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) n) (h : K.1.1 ⊆ support x) :
    M.embedC c n s K = coneSingle S x c (s (toChartIdx K h) : Ω) := by
  simp only [FinGradedSub.embedC, LinearMap.coe_mk, AddHom.coe_mk]
  rw [dif_pos h]
  rfl

/- English proof (translation)
The claim follows from `M.embedC_of_subset c s K h`.
-/
theorem FinGradedSub.embedC_of_subset' {n : ℕ}
    (s : Cech.Cochain (fun I : Chart x => (M.tildeSys c).sub I) n)
    (K : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) n) (h : K.1.1 ⊆ support x) :
    M.embedC c n s K = M.tildeCone c _ (s (toChartIdx K h)) :=
  M.embedC_of_subset c s K h

/- English proof (translation)
Simplify using `only [FinGradedSub.embedC, LinearMap.coe_mk, AddHom.coe_mk]`. Rewrite using `[dif_neg h]`.
-/
theorem FinGradedSub.embedC_of_not {n : ℕ} (s : Cech.Cochain (fun I : Chart x => (M.tildeSys c).sub I) n)
    (K : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) n) (h : ¬ K.1.1 ⊆ support x) :
    M.embedC c n s K = 0 := by
  simp only [FinGradedSub.embedC, LinearMap.coe_mk, AddHom.coe_mk]
  rw [dif_neg h]

/- English proof (translation)
Use function extensionality and compare the values at `J`. Rewrite using `[Cech.d_apply]`. Distinguish the cases in `hJ : J.1.1 ⊆ support x`. Rewrite using `[M.embedC_of_subset' c _ J hJ, Cech.d_apply, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[map_zsmul, supportRes_of_subset _ hJ, LinearMap.id_apply, M.embedC_of_subset c s _ ((Cech.face_subset J j).trans hJ)]`. Both sides reduce to the same expression. Rewrite using `[M.embedC_of_not c _ J hJ]`. Use `symm`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[supportRes_of_not _ hJ, LinearMap.zero_apply, smul_zero]`.
-/
theorem FinGradedSub.embedC_d (n : ℕ) (s : Cech.Cochain (fun I : Chart x => (M.tildeSys c).sub I) n) :
    M.embedC c (n + 1) (Cech.d _ (M.tildeSys c).res n s) =
      Cech.d (fun _ : StdCell N => ConeLaurent S x) (supportRes S x) n (M.embedC c n s) := by
  funext J
  rw [Cech.d_apply]
  by_cases hJ : J.1.1 ⊆ support x
  · rw [M.embedC_of_subset' c _ J hJ, Cech.d_apply, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, supportRes_of_subset _ hJ, LinearMap.id_apply,
      M.embedC_of_subset c s _ ((Cech.face_subset J j).trans hJ)]
    rfl
  · rw [M.embedC_of_not c _ J hJ]
    symm
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [supportRes_of_not _ hJ, LinearMap.zero_apply, smul_zero]

/- English proof (translation)
Introduce `s t hst`. Use function extensionality and compare the values at `K`. Establish `h` using `congrArg (coeffAt S x c) (congrFun hst (ofChartIdx K))`. Rewrite `h` using `[M.embedC_of_subset c s (ofChartIdx K) K.1.2.2, M.embedC_of_subset c t (ofChartIdx K) K.1.2.2, coeffAt_coneSingle_same, coeffAt_coneSingle_same]`. Conclude with `Subtype.ext h`.
-/
theorem FinGradedSub.embedC_injective (n : ℕ) : Function.Injective (M.embedC c n) := by
  intro s t hst
  funext K
  have h := congrArg (coeffAt S x c) (congrFun hst (ofChartIdx K))
  rw [M.embedC_of_subset c s (ofChartIdx K) K.1.2.2, M.embedC_of_subset c t (ofChartIdx K) K.1.2.2,
    coeffAt_coneSingle_same, coeffAt_coneSingle_same] at h
  exact Subtype.ext h

/- English proof (translation)
Introduce `K _`. Distinguish the cases in `h : K.1.1 ⊆ support x`. Rewrite using `[M.embedC_of_subset c s K h]`. Conclude with `(M.mem_coneDeg_of_subset c h).mpr ⟨_, (s (toChartIdx K h)).2, rfl⟩`. Rewrite using `[M.embedC_of_not c s K h]`.

Conclude with `zero_mem _`.
-/
theorem FinGradedSub.embedC_mem (n : ℕ) (s : Cech.Cochain (fun I : Chart x => (M.tildeSys c).sub I) n) :
    M.embedC c n s ∈ Cech.Cdeg (fun _ : StdCell N => ConeLaurent S x) (M.coneDeg c) n := by
  intro K _
  by_cases h : K.1.1 ⊆ support x
  · rw [M.embedC_of_subset c s K h]
    exact (M.mem_coneDeg_of_subset c h).mpr ⟨_, (s (toChartIdx K h)).2, rfl⟩
  · rw [M.embedC_of_not c s K h]
    exact zero_mem _

/- English proof (translation)
Establish `hv : ∀ K : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) n, ∀ h : K.1.1 ⊆ support x, ∃ v ∈ M.tilde c ⟨K.1.1, K.1.2.1, h⟩, w K = coneSingle S x c v` using `fun K h => (M.mem_coneDeg_of_subset c h).mp (hw K (Set.mem_univ _))`. Establish `key : ∀ K : Cech.Idx (support x) n, coeffAt S x c (w (ofChartIdx K)) ∈ (M.tildeSys c).sub K.1`. Introduce `K`. Take `⟨v, hv', hwv⟩` from `hv (ofChartIdx K) K.1.2.2`. Rewrite using `[hwv, coeffAt_coneSingle_same]`.

Conclude with `hv'`. Use `⟨fun K => ⟨coeffAt S x c (w (ofChartIdx K)), key K⟩, funext fun K => ?_⟩` and prove the remaining obligations. Distinguish the cases in `h : K.1.1 ⊆ support x`. Rewrite using `[M.embedC_of_subset c _ K h]`. Take `⟨v, -, hwv⟩` from `hv K h`.

Express the relevant statement in the definitionally equal form `coneSingle S x c (coeffAt S x c (w K)) = w K`. Rewrite using `[hwv, coeffAt_coneSingle_same]`. Rewrite using `[M.embedC_of_not c _ K h]`. Conclude with `(M.eq_zero_of_mem_coneDeg c h (hw K (Set.mem_univ _))).symm`.
-/
theorem FinGradedSub.exists_embedC_eq (n : ℕ) (w : Cech.Cochain (fun _ : StdCell N => ConeLaurent S x) n)
    (hw : w ∈ Cech.Cdeg (fun _ : StdCell N => ConeLaurent S x) (M.coneDeg c) n) :
    ∃ s, M.embedC c n s = w := by
  have hv : ∀ K : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) n, ∀ h : K.1.1 ⊆ support x,
      ∃ v ∈ M.tilde c ⟨K.1.1, K.1.2.1, h⟩, w K = coneSingle S x c v :=
    fun K h => (M.mem_coneDeg_of_subset c h).mp (hw K (Set.mem_univ _))
  have key : ∀ K : Cech.Idx (support x) n,
      coeffAt S x c (w (ofChartIdx K)) ∈ (M.tildeSys c).sub K.1 := by
    intro K
    obtain ⟨v, hv', hwv⟩ := hv (ofChartIdx K) K.1.2.2
    rw [hwv, coeffAt_coneSingle_same]
    exact hv'
  refine ⟨fun K => ⟨coeffAt S x c (w (ofChartIdx K)), key K⟩, funext fun K => ?_⟩
  by_cases h : K.1.1 ⊆ support x
  · rw [M.embedC_of_subset c _ K h]
    obtain ⟨v, -, hwv⟩ := hv K h
    change coneSingle S x c (coeffAt S x c (w K)) = w K
    rw [hwv, coeffAt_coneSingle_same]
  · rw [M.embedC_of_not c _ K h]
    exact (M.eq_zero_of_mem_coneDeg c h (hw K (Set.mem_univ _))).symm

/- English proof (translation)
Assemble the required witnesses or components as `⟨LinearMap.mem_ker.mpr (by rw [← M.embedC_d, LinearMap.mem_ker.mp hs, map_zero]), M.embedC_mem c n s⟩`.
-/
theorem FinGradedSub.embedC_mem_cocyDeg (n : ℕ) (s : Cech.Cochain (fun I : Chart x => (M.tildeSys c).sub I) n)
    (hs : s ∈ LinearMap.ker (Cech.d _ (M.tildeSys c).res n)) :
    M.embedC c n s ∈ Cech.cocyDeg (fun _ : StdCell N => ConeLaurent S x) (M.coneDeg c) (supportRes S x) n :=
  ⟨LinearMap.mem_ker.mpr (by rw [← M.embedC_d, LinearMap.mem_ker.mp hs, map_zero]), M.embedC_mem c n s⟩

def FinGradedSub.embedH (n : ℕ) :
    (M.tildeSys c).H n →ₗ[S]
      Cech.Hdeg (fun _ : StdCell N => ConeLaurent S x) (M.coneDeg c) (supportRes S x) n :=
  Submodule.mapQ _ _
    ((M.embedC c n).restrict (p := LinearMap.ker (Cech.d _ (M.tildeSys c).res n))
      (q := Cech.cocyDeg (fun _ : StdCell N => ConeLaurent S x) (M.coneDeg c) (supportRes S x) n)
      (M.embedC_mem_cocyDeg c n))
    (by
      intro s hs
      cases n with
      | zero =>
        change (s : Cech.Cochain (fun I : Chart x => (M.tildeSys c).sub I) 0) ∈ (⊥ : Submodule S _) at hs
        rw [Submodule.mem_bot] at hs
        change M.embedC c 0 (s : Cech.Cochain (fun I : Chart x => (M.tildeSys c).sub I) 0) ∈
          (⊥ : Submodule S _)
        rw [hs, map_zero]
        exact zero_mem _
      | succ n =>
        obtain ⟨t, ht⟩ := LinearMap.mem_range.mp hs
        change M.embedC c (n + 1) (s : Cech.Cochain (fun I : Chart x => (M.tildeSys c).sub I) (n + 1)) ∈
          (Cech.Cdeg (fun _ : StdCell N => ConeLaurent S x) (M.coneDeg c) n).map
            (Cech.d (fun _ : StdCell N => ConeLaurent S x) (supportRes S x) n)
        exact Submodule.mem_map.mpr ⟨M.embedC c n t, M.embedC_mem c n t, by rw [← M.embedC_d, ht]; rfl⟩)

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `y hy`. Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ y`. Express the relevant statement in the definitionally equal form `Submodule.Quotient.mk _ = 0 at hy`. Establish `hz` using `(Submodule.Quotient.mk_eq_zero _).mp hy`.

Use `(Submodule.Quotient.mk_eq_zero _).mpr ?_` and prove the remaining obligations. Consider the cases of `n with`. Consider the case `zero`. Express the relevant statement in the definitionally equal form `M.embedC c 0 (z : Cech.Cochain (fun I : Chart x => (M.tildeSys c).sub I) 0) ∈ (⊥ : Submodule S _) at hz`. Express the relevant statement in the definitionally equal form `(z : Cech.Cochain (fun I : Chart x => (M.tildeSys c).sub I) 0) ∈ (⊥ : Submodule S _)`.

Rewrite `hz`, the goal using `[Submodule.mem_bot]`. Conclude with `M.embedC_injective c 0 (hz.trans (map_zero _).symm)`. Consider the case `succ n`. Express the relevant statement in the definitionally equal form `M.embedC c (n + 1) (z : Cech.Cochain (fun I : Chart x => (M.tildeSys c).sub I) (n + 1)) ∈ (Cech.Cdeg (fun _ : StdCell N => ConeLaurent S x) (M.coneDeg c) n).map (Cech.d (fun _ : StdCell N => ConeLaurent S x) (supportRes S x) n) at hz`. Take `⟨w, hw, hwz⟩` from `Submodule.mem_map.mp hz`.

Take `⟨t, rfl⟩` from `M.exists_embedC_eq c n w hw`. Use `LinearMap.mem_range.mpr ⟨t, M.embedC_injective c (n + 1) ?_⟩` and prove the remaining obligations. Rewrite using `[M.embedC_d, hwz]`. Both sides reduce to the same expression.
-/
theorem FinGradedSub.embedH_injective (n : ℕ) : Function.Injective (M.embedH c n) := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  change Submodule.Quotient.mk _ = 0 at hy
  have hz := (Submodule.Quotient.mk_eq_zero _).mp hy
  refine (Submodule.Quotient.mk_eq_zero _).mpr ?_
  cases n with
  | zero =>
    change M.embedC c 0 (z : Cech.Cochain (fun I : Chart x => (M.tildeSys c).sub I) 0) ∈
      (⊥ : Submodule S _) at hz
    change (z : Cech.Cochain (fun I : Chart x => (M.tildeSys c).sub I) 0) ∈ (⊥ : Submodule S _)
    rw [Submodule.mem_bot] at hz ⊢
    exact M.embedC_injective c 0 (hz.trans (map_zero _).symm)
  | succ n =>
    change M.embedC c (n + 1) (z : Cech.Cochain (fun I : Chart x => (M.tildeSys c).sub I) (n + 1)) ∈
      (Cech.Cdeg (fun _ : StdCell N => ConeLaurent S x) (M.coneDeg c) n).map
        (Cech.d (fun _ : StdCell N => ConeLaurent S x) (supportRes S x) n) at hz
    obtain ⟨w, hw, hwz⟩ := Submodule.mem_map.mp hz
    obtain ⟨t, rfl⟩ := M.exists_embedC_eq c n w hw
    refine LinearMap.mem_range.mpr ⟨t, M.embedC_injective c (n + 1) ?_⟩
    rw [M.embedC_d, hwz]
    rfl

end Compare

/- English proof (translation)
Introduce `S _ _ Ω _ _ N x M i c`. Establish `hT` using `Cech.Transport.proof (N + 1) (Finset.univ : Finset (Fin (N + 1))) S (locSys S N M.coneSub) (fun _ : StdCell N => ConeLaurent S x) locResS (supportRes S x) (degLoc M.coneGraded c) (M.coneDeg c) M.cellConeS M.cellConeS_res (fun I _ hm => Submodule.mem_map_of_mem hm) M.cellConeS_inj …`. Establish `: Module.Finite S (Cech.Hdeg (locSys S N M.coneSub) (degLoc M.coneGraded c) locResS i)` using `h S N M.coneSub M.coneGraded M.coneSub_finite i c`. Establish `: Module.Finite S (Cech.Hdeg (fun _ : StdCell N => ConeLaurent S x) (M.coneDeg c) (supportRes S x) i)` using `Module.Finite.of_surjective _ hT.2`. Conclude with `Module.Finite.of_injective (M.embedH c i) (M.embedH_injective c i)`.
-/
theorem TildeFinite.proof (h : SerreFinite.Statement.{u, w}) : TildeFinite.Statement.{u, w} := by
  intro S _ _ Ω _ _ N x M i c
  have hT := Cech.Transport.proof (N + 1) (Finset.univ : Finset (Fin (N + 1))) S (locSys S N M.coneSub)
    (fun _ : StdCell N => ConeLaurent S x) locResS (supportRes S x) (degLoc M.coneGraded c) (M.coneDeg c)
    M.cellConeS M.cellConeS_res (fun I _ hm => Submodule.mem_map_of_mem hm) M.cellConeS_injective
    (fun _ => rfl) i
  have : Module.Finite S (Cech.Hdeg (locSys S N M.coneSub) (degLoc M.coneGraded c) locResS i) :=
    h S N M.coneSub M.coneGraded M.coneSub_finite i c
  have : Module.Finite S
      (Cech.Hdeg (fun _ : StdCell N => ConeLaurent S x) (M.coneDeg c) (supportRes S x) i) :=
    Module.Finite.of_surjective _ hT.2
  exact Module.Finite.of_injective (M.embedH c i) (M.embedH_injective c i)

end

end GroundTheory.Heights₂.Heights.Kleiman
