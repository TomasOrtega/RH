import Development.AbelianVarietyTheory.Definitions.Divisors.CechFam
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSubsingletonCohTwistTensLbPow
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.LogDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LatCech

variable {ι : Type} [LinearOrder ι] {V : Type} [AddCommGroup V]
  (A : Cube.{0} ι ℤ) (φ : ∀ s : Finset ι, A.obj s →+ V)

def toFam (m : ℕ) (x : Cube.Term A m) : Finset ι → V :=
  fun s => if h : s.card = m then φ s (x ⟨s, h⟩) else 0

variable {A φ}

/- English proof (translation)
Apply the tactic sequence `funext s; unfold toFam; split_ifs <;> simp`.
-/
theorem toFam_zero (m : ℕ) : toFam A φ m 0 = 0 := by
  funext s; unfold toFam; split_ifs <;> simp

/- English proof (translation)
The claim follows from `Finset.card_pos.1 (by rw [h]; exact hm)`.
-/
theorem nonempty_of_card {m : ℕ} (hm : 0 < m) {s : Finset ι} (h : s.card = m) : s.Nonempty :=
  Finset.card_pos.1 (by rw [h]; exact hm)

/- English proof (translation)
Use function extensionality and compare the values at `t`. Unfold `DI.delta toFam`. Distinguish the cases in `ht : t.card = m + 1`. Rewrite using `[dif_pos ht, Cube.d_apply, map_sum, ← Finset.sum_coe_sort t]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Establish `hc : (t.erase i.1).card = m` using `by rw [Finset.card_erase_of_mem i.2, ht]; rfl`. Rewrite using `[dif_pos hc, map_zsmul, hres _ _ _ (nonempty_of_card hm hc)]`. Rewrite using `[dif_neg ht]`. Use `Finset.sum_eq_zero fun i hi => ?_` and prove the remaining obligations. Establish `hc : (t.erase i).card ≠ m`.

Use `Finset.card_pos.2 ⟨i, hi⟩` as an intermediate fact. Rewrite using `[Finset.card_erase_of_mem hi]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[dif_neg hc, smul_zero]`.
-/
theorem delta_toFam {m : ℕ} (hm : 0 < m)
    (hres : ∀ (s t : Finset ι) (h : s ⊆ t), s.Nonempty → ∀ x, φ t (Cube.res A h x) = φ s x)
    (x : Cube.Term A m) : DI.delta (toFam A φ m x) = toFam A φ (m + 1) (Cube.d A m x) := by
  funext t
  unfold DI.delta toFam
  by_cases ht : t.card = m + 1
  · rw [dif_pos ht, Cube.d_apply, map_sum, ← Finset.sum_coe_sort t]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hc : (t.erase i.1).card = m := by rw [Finset.card_erase_of_mem i.2, ht]; rfl
    rw [dif_pos hc, map_zsmul, hres _ _ _ (nonempty_of_card hm hc)]
  · rw [dif_neg ht]
    refine Finset.sum_eq_zero fun i hi => ?_
    have hc : (t.erase i).card ≠ m := by
      have := Finset.card_pos.2 ⟨i, hi⟩
      rw [Finset.card_erase_of_mem hi]; omega
    rw [dif_neg hc, smul_zero]

/- English proof (translation)
Use `⟨?_, fun s => ?_, fun s hs => ?_⟩` and prove the remaining obligations. Unfold `toFam; rw [dif_neg (by simp; omega)]`. Unfold `toFam split_ifs with h`. Rewrite using `[← hrange s (nonempty_of_card hm h)]`. Conclude with `AddMonoidHom.mem_range.2 ⟨_, rfl⟩`.

Conclude with `zero_mem _`. Unfold `toFam`. Rewrite using `[dif_neg hs]`.
-/
theorem toFam_inCech {N : Finset ι → AddSubgroup V} {m : ℕ} (hm : 0 < m)
    (hrange : ∀ s, s.Nonempty → (φ s).range = N s) (x : Cube.Term A m) :
    DI.InCech N m (toFam A φ m x) := by
  refine ⟨?_, fun s => ?_, fun s hs => ?_⟩
  · unfold toFam; rw [dif_neg (by simp; omega)]
  · unfold toFam
    split_ifs with h
    · rw [← hrange s (nonempty_of_card hm h)]; exact AddMonoidHom.mem_range.2 ⟨_, rfl⟩
    · exact zero_mem _
  · unfold toFam; rw [dif_neg hs]

/- English proof (translation)
Use function extensionality and compare the values at `s`. Use `congrFun h s.1` as an intermediate fact. Unfold `toFam at this`. Rewrite `this` using `[dif_pos s.2, dif_pos s.2]`. Conclude with `hinj _ (nonempty_of_card hm s.2) this`.
-/
theorem toFam_injective {m : ℕ} (hm : 0 < m) (hinj : ∀ s, s.Nonempty → Function.Injective (φ s))
    {x y : Cube.Term A m} (h : toFam A φ m x = toFam A φ m y) : x = y := by
  funext s
  have := congrFun h s.1
  unfold toFam at this
  rw [dif_pos s.2, dif_pos s.2] at this
  exact hinj _ (nonempty_of_card hm s.2) this

/- English proof (translation)
Establish `hex : ∀ s : {s : Finset ι // s.card = m}, ∃ y, φ s.1 y = c s.1` using `fun s => AddMonoidHom.mem_range.1 (by rw [hrange _ (nonempty_of_card hm s.2)]; exact hc.2.1 s.1)`. Use `choose g hg using hex`. Use `⟨g, funext fun s => ?_⟩` and prove the remaining obligations. Unfold `toFam`. Use `split_ifs with h`.

Conclude with `hg ⟨s, h⟩`. Conclude with `(hc.2.2 s h).symm`.
-/
theorem exists_toFam {N : Finset ι → AddSubgroup V} {m : ℕ} (hm : 0 < m)
    (hrange : ∀ s, s.Nonempty → (φ s).range = N s) {c : Finset ι → V} (hc : DI.InCech N m c) :
    ∃ x : Cube.Term A m, toFam A φ m x = c := by
  have hex : ∀ s : {s : Finset ι // s.card = m}, ∃ y, φ s.1 y = c s.1 := fun s =>
    AddMonoidHom.mem_range.1 (by rw [hrange _ (nonempty_of_card hm s.2)]; exact hc.2.1 s.1)
  choose g hg using hex
  refine ⟨g, funext fun s => ?_⟩
  unfold toFam
  split_ifs with h
  · exact hg ⟨s, h⟩
  · exact (hc.2.2 s h).symm

/- English proof (translation)
Establish `hm1 : 0 < m + 1` using `Nat.succ_pos m`. Prove the components needed by the constructor for the conclusion. Introduce `hex c hc hdc`. Take `⟨x, rfl⟩` from `exists_toFam (A := A) hm1 hrange hc`. Establish `hdx : Cube.d A (m + 1) x = 0` using `toFam_injective (Nat.succ_pos _) hinj (by rw [← delta_toFam hm1 hres, hdc, toFam_zero])`.

Take `⟨y, hy⟩` from `(hex x).1 hdx`. Conclude with `⟨toFam A φ m y, toFam_inCech hm hrange y, by rw [delta_toFam hm hres, hy]⟩`. Introduce `hcz x`. Prove the components needed by the constructor for the conclusion. Introduce `hdx`.

Take `⟨y', hy'c, hy'd⟩` from `hcz (toFam A φ (m + 1) x) (toFam_inCech hm1 hrange x) (by rw [delta_toFam hm1 hres, hdx, toFam_zero])`. Take `⟨y, rfl⟩` from `exists_toFam (A := A) hm hrange hy'c`. Conclude with `⟨y, toFam_injective hm1 hinj (by rw [← delta_toFam hm hres, hy'd])⟩`. Introduce and unpack `⟨y, rfl⟩`. Conclude with `Cube.d_d A m y`.
-/
theorem exact_iff_cechZero {N : Finset ι → AddSubgroup V} {m : ℕ} (hm : 0 < m)
    (hinj : ∀ s, s.Nonempty → Function.Injective (φ s))
    (hrange : ∀ s, s.Nonempty → (φ s).range = N s)
    (hres : ∀ (s t : Finset ι) (h : s ⊆ t), s.Nonempty → ∀ x, φ t (Cube.res A h x) = φ s x) :
    Function.Exact (Cube.d A m) (Cube.d A (m + 1)) ↔ DI.CechZero N m := by
  have hm1 : 0 < m + 1 := Nat.succ_pos m
  constructor
  · intro hex c hc hdc
    obtain ⟨x, rfl⟩ := exists_toFam (A := A) hm1 hrange hc
    have hdx : Cube.d A (m + 1) x = 0 := toFam_injective (Nat.succ_pos _) hinj
      (by rw [← delta_toFam hm1 hres, hdc, toFam_zero])
    obtain ⟨y, hy⟩ := (hex x).1 hdx
    exact ⟨toFam A φ m y, toFam_inCech hm hrange y, by rw [delta_toFam hm hres, hy]⟩
  · intro hcz x
    constructor
    · intro hdx
      obtain ⟨y', hy'c, hy'd⟩ := hcz (toFam A φ (m + 1) x) (toFam_inCech hm1 hrange x)
        (by rw [delta_toFam hm1 hres, hdx, toFam_zero])
      obtain ⟨y, rfl⟩ := exists_toFam (A := A) hm hrange hy'c
      exact ⟨y, toFam_injective hm1 hinj (by rw [← delta_toFam hm hres, hy'd])⟩
    · rintro ⟨y, rfl⟩
      exact Cube.d_d A m y

end GlobalTheory.LatCech

namespace GlobalTheory

/- English proof (translation)
Introduce `X _ hsepX V _ _ M F _ ι _ _ U hL hA hg hc b hb`. Establish `hsep` using `(cech_computes_coh_of_affine_cover.{0, 0, 0} X ℤ).1 (Or.inl hsepX) ι U hA`. Take `⟨e, -⟩` from `((cech_computes_coh_of_affine_cover.{0, 0, 0} X ℤ).2.1 ι U hc hsep).1`. Establish `hO : ∀ s : Finset ι, cechOpen ⊤ U s = inter U s` using `fun s => by`. Simplify using `[cechOpen, inter, Finset.inf_eq_iInf]`.

Establish `hgen : ∀ s : Finset ι, genericPoint X ∈ cechOpen ⊤ U s` using `fun s => by`. Rewrite using `[hO, ← SetLike.mem_coe, inter, Opens.coe_finset_inf]`. Simplify using `[hg]`. Set `φ : ∀ s : Finset ι, (cechCube ℤ F ⊤ U).obj s →+ V` to `fun s => (hL.val (cechOpen ⊤ U s) (hgen s)).comp (sectionsOn.toΓ F (cechOpen ⊤ U s)).toAddMonoidHom`. Establish `hinj : ∀ s : Finset ι, s.Nonempty → Function.Injective (φ s)` using `fun s _ => (hL.inj _ (hgen s)).comp (sectionsOn.toΓ F (cechOpen ⊤ U s)).injective`.

Establish `hrange : ∀ s : Finset ι, s.Nonempty → (φ s).range = latSec M (inter U s)`. Introduce `s _`. Rewrite using `[← hO s, ← hL.range _ (hgen s)]`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨x, rfl⟩`. Conclude with `AddMonoidHom.mem_range.2 ⟨_, rfl⟩`. Introduce and unpack `⟨z, rfl⟩`. Conclude with `AddMonoidHom.mem_range.2 ⟨(sectionsOn.toΓ F (cechOpen ⊤ U s)).symm z, congrArg (hL.val _ (hgen s)) ((sectionsOn.toΓ F (cechOpen ⊤ U s)).apply_symm_apply z)⟩`. Establish `hres : ∀ (s t : Finset ι) (h : s ⊆ t), s.Nonempty → ∀ x, φ t (Cube.res (cechCube ℤ F ⊤ U) h x) = φ s x`.

Introduce `s t h _ x`. Use `show hL.val _ _ (sectionsOn.toΓ F _ (sectionsOn.res ℤ F (cechOpen_anti ⊤ U h) x)) = hL.val _ _ (sectionsOn.toΓ F _ x)`. Conclude with `hL.res (cechOpen ⊤ U s) (cechOpen ⊤ U t) (cechOpen_anti ⊤ U h) (hgen t) (sectionsOn.toΓ F _ x)`. Take `⟨p, rfl⟩ : ∃ p, b = p + 1` from `⟨b - 1, by omega⟩`. Establish `e'` using `e F (p + 1)`.

Rewrite using `[show Subsingleton (coh F (p + 1)) ↔ Subsingleton (cechH ℤ F ⊤ U (p + 1)) from ⟨fun h => haveI := h; e'.injective.subsingleton, fun h => haveI := h; e'.symm.injective.subsingleton⟩, ← ModuleCat.isZero_iff_subsingleton, cechH_def, cech_def, ← HomologicalComplex.exactAt_iff_isZero_ …`. Conclude with `(LatCech.exact_iff_cechZero (φ := φ) (Nat.succ_pos p) hinj hrange hres).symm`.
-/
theorem cechZero_latSec_iff_subsingleton_coh : ∀ (X : Scheme.{0}) [IsIntegral X] [X.IsSeparated]
    {V : Type} [AddCommGroup V] [Module X.functionField V] (M : X → AddSubgroup V) (F : X.Modules)
    [F.IsQuasicoherent] {ι : Type} [Fintype ι] [LinearOrder ι] (U : ι → X.Opens), LatModel M F →
    (∀ i, IsAffineOpen (U i)) → (∀ i, genericPoint X ∈ U i) → ⨆ i, U i = ⊤ → ∀ b : ℕ, 0 < b →
    (DI.CechZero (fun s => latSec M (inter U s)) b ↔ Subsingleton (coh F b)) := by
  intro X _ hsepX V _ _ M F _ ι _ _ U hL hA hg hc b hb
  have hsep := (cech_computes_coh_of_affine_cover.{0, 0, 0} X ℤ).1 (Or.inl hsepX) ι U hA
  obtain ⟨e, -⟩ := ((cech_computes_coh_of_affine_cover.{0, 0, 0} X ℤ).2.1 ι U hc hsep).1
  have hO : ∀ s : Finset ι, cechOpen ⊤ U s = inter U s := fun s => by
    simp [cechOpen, inter, Finset.inf_eq_iInf]
  have hgen : ∀ s : Finset ι, genericPoint X ∈ cechOpen ⊤ U s := fun s => by
    rw [hO, ← SetLike.mem_coe, inter, Opens.coe_finset_inf]
    simp [hg]
  let φ : ∀ s : Finset ι, (cechCube ℤ F ⊤ U).obj s →+ V := fun s =>
    (hL.val (cechOpen ⊤ U s) (hgen s)).comp (sectionsOn.toΓ F (cechOpen ⊤ U s)).toAddMonoidHom
  have hinj : ∀ s : Finset ι, s.Nonempty → Function.Injective (φ s) := fun s _ =>
    (hL.inj _ (hgen s)).comp (sectionsOn.toΓ F (cechOpen ⊤ U s)).injective
  have hrange : ∀ s : Finset ι, s.Nonempty → (φ s).range = latSec M (inter U s) := by
    intro s _
    rw [← hO s, ← hL.range _ (hgen s)]
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact AddMonoidHom.mem_range.2 ⟨_, rfl⟩
    · rintro ⟨z, rfl⟩
      exact AddMonoidHom.mem_range.2 ⟨(sectionsOn.toΓ F (cechOpen ⊤ U s)).symm z,
        congrArg (hL.val _ (hgen s)) ((sectionsOn.toΓ F (cechOpen ⊤ U s)).apply_symm_apply z)⟩
  have hres : ∀ (s t : Finset ι) (h : s ⊆ t), s.Nonempty →
      ∀ x, φ t (Cube.res (cechCube ℤ F ⊤ U) h x) = φ s x := by
    intro s t h _ x
    show hL.val _ _ (sectionsOn.toΓ F _ (sectionsOn.res ℤ F (cechOpen_anti ⊤ U h) x)) =
      hL.val _ _ (sectionsOn.toΓ F _ x)
    exact hL.res (cechOpen ⊤ U s) (cechOpen ⊤ U t) (cechOpen_anti ⊤ U h) (hgen t)
      (sectionsOn.toΓ F _ x)
  obtain ⟨p, rfl⟩ : ∃ p, b = p + 1 := ⟨b - 1, by omega⟩
  have e' := e F (p + 1)
  rw [show Subsingleton (coh F (p + 1)) ↔ Subsingleton (cechH ℤ F ⊤ U (p + 1)) from
    ⟨fun h => haveI := h; e'.injective.subsingleton,
      fun h => haveI := h; e'.symm.injective.subsingleton⟩,
    ← ModuleCat.isZero_iff_subsingleton, cechH_def, cech_def,
    ← HomologicalComplex.exactAt_iff_isZero_homology, cechComplex_exactAt_succ_iff]
  exact (LatCech.exact_iff_cechZero (φ := φ) (Nat.succ_pos p) hinj hrange hres).symm

end GlobalTheory
