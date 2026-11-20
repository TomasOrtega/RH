import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FrobeniusTwistEigen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfScaledAlongPerm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVBAndClsDetOfShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFrameOfBijectiveStalk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrincipalIdealRingStalk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveOfFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOneSubbundleSplitAtPoints

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.IndefiniteRowSideFullHecke.FrobeniusTwistEigen
open GlobalTheory.QCoh (IsFiniteQC stalkLinear)

namespace GlobalTheory.SlopeEigen

variable {k : Type} [Field k] {C : Scheme.{0}} [Algebra k Γ(C, ⊤)] [IsIntegral C]

/- English proof (translation)
The claim follows from `(isVB_of_isTorsionFree_and_isSubbundle_satι k C hC).1 G (hE.isTorsionFree.of_mono i)`.
-/
theorem isVB_of_mono (hC : IsSmoothProjCurve k C) {E G : C.Modules} {r : ℕ} (hE : IsVB E r)
    (i : G ⟶ E) [Mono i] [IsFiniteQC G] : IsVB G (genRank G) :=
  (isVB_of_isTorsionFree_and_isSubbundle_satι k C hC).1 G (hE.isTorsionFree.of_mono i)

/- English proof (translation)
Establish `hP` using `hC.toIsProjCurve`. Use `hP.isNoetherian` as an intermediate fact. Proceed by induction on `r with`. Consider the case `zero`. Introduce `E hE`.

Establish `he : IsFrame (F` using `E) (U := ⊤) (Fin.elim0 : Fin 0 → Γ(E, ⊤)) := by`. Establish `φ : QCoh.freeModule C (Fin 0) ≅ E` using `(isVB_zero_iff.1 (isVB_freeModule_fin C 0)).iso (isVB_zero_iff.1 hE)`. Use `(isFrame_freeFrame C (Fin 0)).map_iso φ.hom` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Rewrite using `[deg_eq_zero_of_isZero k (isVB_zero_iff.1 hE), ← hP.degPic_cls hE.isLB_det, he.cls_det_eq_zero, map_zero]`.

Consider the case `succ r ih`. Introduce `E hE`. Use `hE.isFiniteQC` as an intermediate fact. Take `⟨G, φ, hG, _, -⟩` from `exists_line_subsheaf_split_at_finite k C hP.isProjOver E r hE ∅ Set.finite_empty`. Establish `h₁ : IsVB (sat φ) 1`.

Use `isVB_of_mono hC hE (satι φ)` as an intermediate fact. Rewrite `this` using `[genRank_sat, hG.genRank_eq]`. Then use the resulting hypothesis. Take `⟨s, h₃⟩` from `((isVB_of_isTorsionFree_and_isSubbundle_satι k C hC).2 E G φ).isVB_cokernel`. Choose the witnesses or unpack the hypotheses as in `rfl : s = r := by`. Use `genRank_cokernel (satι φ)` as an intermediate fact.

Rewrite `this` using `[hE.genRank_eq, h₁.genRank_eq, h₃.genRank_eq]`. Use linear arithmetic over natural numbers and integers. Establish `hS : (ShortComplex.mk _ (cokernel.π (satι φ)) (cokernel.condition _)).ShortExact` using `{ exact := ShortComplex.exact_cokernel _ }`. Take `⟨h₂, e⟩` from `VBExt.isVB_and_cls_det_of_shortExact C _ 1 s hS h₁ h₃`. Establish `e'` using `hP.degLB_of_cls_eq_add _ _ _ e`.

Establish `e''` using `hP.deg_cokernel (satι φ)`. Rewrite using `[add_comm s 1]`. Express the relevant statement in the definitionally equal form `degLB k (det E (1 + s)) = degLB k (det (sat φ) 1) + degLB k (det (cokernel (satι φ)) s) at e'`. Rewrite using `[e', h₁.degLB_det_one, ih h₃, e'']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem degLB_det [Infinite k] (hC : IsSmoothProjCurve k C) (r : ℕ) :
    ∀ {E : C.Modules}, IsVB E r → degLB k (det E r) = deg k E := by
  have hP := hC.toIsProjCurve
  have := hP.isNoetherian
  induction r with
  | zero =>
    intro E hE
    have he : IsFrame (F := E) (U := ⊤) (Fin.elim0 : Fin 0 → Γ(E, ⊤)) := by
      have φ : QCoh.freeModule C (Fin 0) ≅ E :=
        (isVB_zero_iff.1 (isVB_freeModule_fin C 0)).iso (isVB_zero_iff.1 hE)
      have := (isFrame_freeFrame C (Fin 0)).map_iso φ.hom
      convert this using 1
    rw [deg_eq_zero_of_isZero k (isVB_zero_iff.1 hE), ← hP.degPic_cls hE.isLB_det,
      he.cls_det_eq_zero, map_zero]
  | succ r ih =>
    intro E hE
    have := hE.isFiniteQC
    obtain ⟨G, φ, hG, _, -⟩ :=
      exists_line_subsheaf_split_at_finite k C hP.isProjOver E r hE ∅ Set.finite_empty
    have h₁ : IsVB (sat φ) 1 := by
      have := isVB_of_mono hC hE (satι φ)
      rwa [genRank_sat, hG.genRank_eq] at this
    obtain ⟨s, h₃⟩ := ((isVB_of_isTorsionFree_and_isSubbundle_satι k C hC).2 E G φ).isVB_cokernel
    obtain rfl : s = r := by
      have := genRank_cokernel (satι φ)
      rw [hE.genRank_eq, h₁.genRank_eq, h₃.genRank_eq] at this
      omega
    have hS : (ShortComplex.mk _ (cokernel.π (satι φ)) (cokernel.condition _)).ShortExact :=
      { exact := ShortComplex.exact_cokernel _ }
    obtain ⟨h₂, e⟩ := VBExt.isVB_and_cls_det_of_shortExact C _ 1 s hS h₁ h₃
    have e' := hP.degLB_of_cls_eq_add _ _ _ e
    have e'' := hP.deg_cokernel (satι φ)
    rw [add_comm s 1]
    change degLB k (det E (1 + s)) = degLB k (det (sat φ) 1) + degLB k (det (cokernel (satι φ)) s)
      at e'
    rw [e', h₁.degLB_det_one, ih h₃, e'']
    ring

/- English proof (translation)
Establish `hP` using `hC.toIsProjCurve`. Rewrite using `[← degLB_det hC r h, ← degLB_det hC r h.dual, ← hP.degPic_cls h.isLB_det, ← map_neg, ← CechPic.cls_dual h.isLB_det (CechPic.isLB_dual h.isLB_det), hP.degPic_cls]`. Conclude with `(degLB_congr (CechPic.isLB_dual h.isLB_det) h.dual.isLB_det h.lbIso_det_dual).symm`.
-/
theorem deg_dual [Infinite k] (hC : IsSmoothProjCurve k C) {E : C.Modules} {r : ℕ}
    (h : IsVB E r) : deg k (dual E) = -deg k E := by
  have hP := hC.toIsProjCurve
  rw [← degLB_det hC r h, ← degLB_det hC r h.dual, ← hP.degPic_cls h.isLB_det, ← map_neg,
    ← CechPic.cls_dual h.isLB_det (CechPic.isLB_dual h.isLB_det), hP.degPic_cls]
  exact (degLB_congr (CechPic.isLB_dual h.isLB_det) h.dual.isLB_det h.lbIso_det_dual).symm

/- English proof (translation)
Establish `hP` using `hC.toIsProjCurve`. Establish `h'` using `Semi.LB.isLB_pull h.isLB_det (frob C p hp)`. Rewrite using `[← degLB_det hC r h, ← degLB_det hC r (h.frobPull p hp), ← hP.degPic_cls h.isLB_det, ← nsmul_eq_mul, ← map_nsmul, ← cls_pull_frob p hp h.isLB_det h', hP.degPic_cls]`. Conclude with `(degLB_congr h' (h.frobPull p hp).isLB_det (h.lbIso_det_pullback _)).symm`.
-/
theorem deg_frobPull [Infinite k] (hC : IsSmoothProjCurve k C) (p : ℕ) [Fact p.Prime]
    (hp : (p : Γ(C, ⊤)) = 0) {E : C.Modules} {r : ℕ} (h : IsVB E r) :
    deg k ((frobPull p hp).obj E) = p * deg k E := by
  have hP := hC.toIsProjCurve
  have h' := Semi.LB.isLB_pull h.isLB_det (frob C p hp)
  rw [← degLB_det hC r h, ← degLB_det hC r (h.frobPull p hp), ← hP.degPic_cls h.isLB_det,
    ← nsmul_eq_mul, ← map_nsmul, ← cls_pull_frob p hp h.isLB_det h', hP.degPic_cls]
  exact (degLB_congr h' (h.frobPull p hp).isLB_det (h.lbIso_det_pullback _)).symm

/- English proof (translation)
Use `Abelian.hasFiniteBiproducts (C := C.Modules)` as an intermediate fact. Establish `hr : genRank (⨁ L) = ∑ j, genRank (L j)`. Establish `hl : ∀ {A B : C.Modules} (φ : ι → (A ⟶ B)), stalkLinear (∑ j, φ j) (genericPoint C) = ∑ j, stalkLinear (φ j) (genericPoint C)` using `fun φ => stalkLinear_finset_sum _ _ _`. Set `e : genStalk (⨁ L) ≃ₗ[C.functionField] ∀ j, genStalk (L j)` to `LinearEquiv.ofLinearMap (LinearMap.pi fun j => stalkLinear (biproduct.π L j) _) (∑ j, stalkLinear (biproduct.ι L j) _ ∘ₗ LinearMap.proj j) (by`. Use `LinearMap.pi_ext' fun i => LinearMap.ext fun t => funext fun j => ?_` and prove the remaining obligations.

Simplify using `only [LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.sum_apply, map_sum, LinearMap.proj_apply, LinearMap.id_apply, LinearMap.single_apply]`. Rewrite using `[Finset.sum_eq_single j (fun i' _ h' => ?_) (by simp), ← LinearMap.comp_apply, ← QCoh.stalkLinear_comp, biproduct.ι_π_self, QCoh.stalkLinear_id, LinearMap.id_apply]`. Rewrite using `[← LinearMap.comp_apply, ← QCoh.stalkLinear_comp, biproduct.ι_π_ne _ h', QCoh.stalkLinear_zero, LinearMap.zero_apply])`. Use the proof step `(by`. Rewrite using `[← QCoh.stalkLinear_id, ← biproduct.total, hl]`.

Use `LinearMap.ext fun t => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.proj_apply, QCoh.stalkLinear_comp])`. Rewrite using `[genRank, e.finrank_eq, Module.finrank_pi_fintype]`. Both sides reduce to the same expression. Rewrite using `[← deg_congr k (biproduct.isoCoproduct L)]`.

Simplify using `only [deg_def]`. Rewrite using `[chi_congr k (biproduct.isoProduct L), chi_pi fun j => hC.finiteCoh _, hr, Finset.sum_sub_distrib, ← Finset.sum_mul, Nat.cast_sum]`.
-/
theorem deg_sigma (hC : IsProjCurve k C) {ι : Type} [Fintype ι] (L : ι → C.Modules)
    [∀ j, IsFiniteQC (L j)] : deg k (∐ L) = ∑ j, deg k (L j) := by
  classical
  have := Abelian.hasFiniteBiproducts (C := C.Modules)
  have hr : genRank (⨁ L) = ∑ j, genRank (L j) := by
    have hl : ∀ {A B : C.Modules} (φ : ι → (A ⟶ B)), stalkLinear (∑ j, φ j) (genericPoint C) =
        ∑ j, stalkLinear (φ j) (genericPoint C) := fun φ => stalkLinear_finset_sum _ _ _
    let e : genStalk (⨁ L) ≃ₗ[C.functionField] ∀ j, genStalk (L j) :=
      LinearEquiv.ofLinearMap (LinearMap.pi fun j => stalkLinear (biproduct.π L j) _)
        (∑ j, stalkLinear (biproduct.ι L j) _ ∘ₗ LinearMap.proj j)
        (by
          refine LinearMap.pi_ext' fun i => LinearMap.ext fun t => funext fun j => ?_
          simp only [LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.sum_apply, map_sum,
            LinearMap.proj_apply, LinearMap.id_apply, LinearMap.single_apply]
          rw [Finset.sum_eq_single j (fun i' _ h' => ?_) (by simp), ← LinearMap.comp_apply,
            ← QCoh.stalkLinear_comp, biproduct.ι_π_self, QCoh.stalkLinear_id, LinearMap.id_apply]
          rw [← LinearMap.comp_apply, ← QCoh.stalkLinear_comp, biproduct.ι_π_ne _ h',
            QCoh.stalkLinear_zero, LinearMap.zero_apply])
        (by
          rw [← QCoh.stalkLinear_id, ← biproduct.total, hl]
          refine LinearMap.ext fun t => ?_
          simp only [LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.sum_apply,
            LinearMap.proj_apply, QCoh.stalkLinear_comp])
    rw [genRank, e.finrank_eq, Module.finrank_pi_fintype]
    rfl
  rw [← deg_congr k (biproduct.isoCoproduct L)]
  simp only [deg_def]
  rw [chi_congr k (biproduct.isoProduct L), chi_pi fun j => hC.finiteCoh _, hr,
    Finset.sum_sub_distrib, ← Finset.sum_mul, Nat.cast_sum]

/- English proof (translation)
Take `⟨i, q, w, hS⟩` from `h`. Establish `: IsFiniteQC (ShortComplex.mk i q w).X₂` using `hH`. Establish `e` using `VB.deg_shortExact (k := k) hS (hC.finiteCoh A) (hC.finiteCoh B)`. Simplify using `only at e`. Conclude with `e`.
-/
theorem deg_of_isExtension (hC : IsProjCurve k C) {A H B : C.Modules} [hA : IsFiniteQC A]
    [hH : IsFiniteQC H] [hB : IsFiniteQC B] (h : IsExtension A H B) :
    deg k H = deg k A + deg k B := by
  obtain ⟨i, q, w, hS⟩ := h
  have : IsFiniteQC (ShortComplex.mk i q w).X₂ := hH
  have e := VB.deg_shortExact (k := k) hS (hC.finiteCoh A) (hC.finiteCoh B)
  dsimp only at e
  exact e

/- English proof (translation)
Establish `hC'` using `hC.toIsProjCurve`. Use `hC'.isNoetherian` as an intermediate fact. Use `hL.dual.isFiniteQC` as an intermediate fact. Use `hL.isIso_toBidual_of_local_frames` as an intermediate fact. Take `⟨s, hQ⟩` from `((isVB_of_isTorsionFree_and_isSubbundle_satι k C hC).2 _ _ j).isVB_cokernel`.

Use `hQ.dual.isFiniteQC` as an intermediate fact. Establish `h₁` using `hC'.deg_le_deg_sat j`. Establish `h₂` using `hC'.deg_cokernel (satι j)`. Establish `h₃` using `hP.deg_le (dualMap (cokernel.π (satι j)) ≫ inv (cartierDualToBidual L))`. Rewrite `h₃` using `[deg_dual hC hQ]`.

Rewrite `h₂` using `[deg_dual hC hL]`. Use linear arithmetic over natural numbers and integers.
-/
theorem deg_le_of_mono_dual [Infinite k] (hC : IsSmoothProjCurve k C) {L K : C.Modules} {g : ℕ}
    (hL : IsVB L g) {P : ℤ} (hP : IsMaxSubDeg k L P) (j : K ⟶ dual L) [Mono j] [IsFiniteQC K] :
    deg k K ≤ -deg k L + P := by
  have hC' := hC.toIsProjCurve
  have := hC'.isNoetherian
  have := hL.dual.isFiniteQC
  have := hL.isIso_toBidual_of_local_frames
  obtain ⟨s, hQ⟩ := ((isVB_of_isTorsionFree_and_isSubbundle_satι k C hC).2 _ _ j).isVB_cokernel
  have := hQ.dual.isFiniteQC
  have h₁ := hC'.deg_le_deg_sat j
  have h₂ := hC'.deg_cokernel (satι j)
  have h₃ := hP.deg_le (dualMap (cokernel.π (satι j)) ≫ inv (cartierDualToBidual L))
  rw [deg_dual hC hQ] at h₃
  rw [deg_dual hC hL] at h₂
  omega

/- English proof (translation)
Introduce `p _ k _ _ _ C _ _ hC L H g hL hH ⟨i, q, w, hS⟩ ⟨v, _⟩ P hP`. Establish `hC'` using `hC.toIsProjCurve`. Use `hC'.isNoetherian` as an intermediate fact. Use `hL.isFiniteQC` as an intermediate fact. Establish `hp` using `natCast_eq_zero C p k`.

Take `⟨G, a, ha, hG⟩` from `hP.exists_isCohSub`. Use `ha.mono` as an intermediate fact. Use `ha.isFiniteQC` as an intermediate fact. Establish `hξ` using `isVB_of_mono hC hL (satι a)`. Establish `hd : deg k (sat a) = P` using `le_antisymm (hP.deg_le (satι a)) (hG ▸ hC'.deg_le_deg_sat a)`.

Use `(SubPull.isSubbundle_pullback C C (frob C p hp) _ _ (satι a) _ hξ ((isVB_of_isTorsionFree_and_isSubbundle_satι k C hC).2 _ _ a)).mono` as an intermediate fact. Use `(hξ.frobPull p hp).isFiniteQC` as an intermediate fact. Set `u : (frobPull p hp).obj (sat a) ⟶ H` to `(frobPull p hp).map (satι a) ≫ v`. Establish `: Mono u` using `mono_comp _ _`. Establish `h₀` using `deg_frobPull hC p hp hξ`.

Establish `h₁` using `hC'.deg_cokernel (kernel.ι (u ≫ q))`. Establish `h₂ : deg k (cokernel (kernel.ι (u ≫ q))) ≤ P` using `hP.deg_le (Abelian.factorThruCoimage (u ≫ q))`. Use `hS.mono_f` as an intermediate fact. Take `⟨j, hj⟩` from `KernelFork.IsLimit.lift' hS.fIsKernel (kernel.ι (u ≫ q) ≫ u) (by simp)`. Establish `: Mono j` using `mono_of_mono_fac hj`.

Establish `h₃` using `deg_le_of_mono_dual hC hL hP j`. Rewrite `h₀` using `[hd]`. Use linear arithmetic over natural numbers and integers.
-/
theorem slopeInequality : SlopeInequality := by
  intro p _ k _ _ _ C _ _ hC L H g hL hH ⟨i, q, w, hS⟩ ⟨v, _⟩ P hP
  have hC' := hC.toIsProjCurve
  have := hC'.isNoetherian
  have := hL.isFiniteQC
  have hp := natCast_eq_zero C p k
  obtain ⟨G, a, ha, hG⟩ := hP.exists_isCohSub
  have := ha.mono
  have := ha.isFiniteQC
  have hξ := isVB_of_mono hC hL (satι a)
  have hd : deg k (sat a) = P :=
    le_antisymm (hP.deg_le (satι a)) (hG ▸ hC'.deg_le_deg_sat a)
  have := (SubPull.isSubbundle_pullback C C (frob C p hp) _ _ (satι a) _ hξ
    ((isVB_of_isTorsionFree_and_isSubbundle_satι k C hC).2 _ _ a)).mono
  have := (hξ.frobPull p hp).isFiniteQC
  let u : (frobPull p hp).obj (sat a) ⟶ H := (frobPull p hp).map (satι a) ≫ v
  have : Mono u := mono_comp _ _
  have h₀ := deg_frobPull hC p hp hξ
  have h₁ := hC'.deg_cokernel (kernel.ι (u ≫ q))
  have h₂ : deg k (cokernel (kernel.ι (u ≫ q))) ≤ P :=
    hP.deg_le (Abelian.factorThruCoimage (u ≫ q))
  have := hS.mono_f
  obtain ⟨j, hj⟩ := KernelFork.IsLimit.lift' hS.fIsKernel (kernel.ι (u ≫ q) ≫ u) (by simp)
  have : Mono j := mono_of_mono_fac hj
  have h₃ := deg_le_of_mono_dual hC hL hP j
  rw [hd] at h₀
  omega

/- English proof (translation)
Introduce `p hp k _ _ _ C _ _ hC ι _ φ c hc L H m n hL hH h₁ h₂`. Establish `hC'` using `hC.toIsProjCurve`. Use `fun τ => (hL τ).isFiniteQC` as an intermediate fact. Use `fun τ => (hL τ).dual.isFiniteQC` as an intermediate fact. Use `fun τ => (hH τ).isFiniteQC` as an intermediate fact.

Use `fun τ => ((hL τ).frobPull p (natCast_eq_zero C p k)).isFiniteQC` as an intermediate fact. Use `fun τ => ((hL τ).dual.frobPull p (natCast_eq_zero C p k)).isFiniteQC` as an intermediate fact. Establish `e₁ (τ : ι) : deg k (H τ) = -deg k (L (c τ)) + deg k (L τ)`. Rewrite using `[deg_of_isExtension hC' (h₁ τ), deg_dual hC (hL _)]`. Establish `e₂ (τ : ι) : deg k (H (φ τ)) = p * deg k (H τ)`.

Rewrite using `[deg_of_isExtension hC' (h₂ τ), deg_frobPull hC p _ (hL τ), deg_frobPull hC p _ (hL _).dual, deg_dual hC (hL _), e₁]`. Expand and normalize the polynomial expressions, which then agree. Establish `e₃` using `GlobalTheory.eq_zero_of_scaled_along_perm ι φ p (fun τ => deg k (H τ)) hp.out.two_le e₂`. Establish `e₄ (τ : ι) : deg k (L τ) = deg k (L (c τ))`. Use `e₁ τ` as an intermediate fact.

Establish `: deg k (H τ) = 0` using `e₃ τ`. Use linear arithmetic over natural numbers and integers. Use `⟨e₃, e₄, fun M ⟨α⟩ Ψ hΨ => ?_⟩` and prove the remaining obligations. Establish `e₅ : ∑ τ ∈ Ψᶜ, deg k (L τ) = ∑ τ ∈ Ψ, deg k (L τ)` using `Finset.sum_nbij' c c (fun τ h => by simpa [hΨ τ] using h) (fun τ h => by simpa using (hΨ τ).1 h) (fun τ _ => hc τ) (fun τ _ => hc τ) fun τ _ => e₄ τ`. Rewrite using `[deg_congr k α, deg_sigma hC', ← Finset.sum_add_sum_compl Ψ, e₅, Finset.sum_congr rfl fun τ _ => deg_dual hC (hL τ), Finset.sum_neg_distrib]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem eigenDegrees : EigenDegrees := by
  intro p hp k _ _ _ C _ _ hC ι _ φ c hc L H m n hL hH h₁ h₂
  classical
  have hC' := hC.toIsProjCurve
  have := fun τ => (hL τ).isFiniteQC
  have := fun τ => (hL τ).dual.isFiniteQC
  have := fun τ => (hH τ).isFiniteQC
  have := fun τ => ((hL τ).frobPull p (natCast_eq_zero C p k)).isFiniteQC
  have := fun τ => ((hL τ).dual.frobPull p (natCast_eq_zero C p k)).isFiniteQC
  have e₁ (τ : ι) : deg k (H τ) = -deg k (L (c τ)) + deg k (L τ) := by
    rw [deg_of_isExtension hC' (h₁ τ), deg_dual hC (hL _)]
  have e₂ (τ : ι) : deg k (H (φ τ)) = p * deg k (H τ) := by
    rw [deg_of_isExtension hC' (h₂ τ), deg_frobPull hC p _ (hL τ),
      deg_frobPull hC p _ (hL _).dual, deg_dual hC (hL _), e₁]
    ring
  have e₃ := GlobalTheory.eq_zero_of_scaled_along_perm ι φ p (fun τ => deg k (H τ)) hp.out.two_le e₂
  have e₄ (τ : ι) : deg k (L τ) = deg k (L (c τ)) := by
    have := e₁ τ
    have : deg k (H τ) = 0 := e₃ τ
    omega
  refine ⟨e₃, e₄, fun M ⟨α⟩ Ψ hΨ => ?_⟩
  have e₅ : ∑ τ ∈ Ψᶜ, deg k (L τ) = ∑ τ ∈ Ψ, deg k (L τ) :=
    Finset.sum_nbij' c c (fun τ h => by simpa [hΨ τ] using h)
      (fun τ h => by simpa using (hΨ τ).1 h) (fun τ _ => hc τ) (fun τ _ => hc τ) fun τ _ => e₄ τ
  rw [deg_congr k α, deg_sigma hC', ← Finset.sum_add_sum_compl Ψ, e₅,
    Finset.sum_congr rfl fun τ _ => deg_dual hC (hL τ), Finset.sum_neg_distrib]
  ring

/- English proof (translation)
Assemble the required witnesses or components as `⟨slopeInequality, eigenDegrees⟩`.
-/
theorem slopeAndEigenDegrees : SlopeAndEigenDegrees := ⟨slopeInequality, eigenDegrees⟩

end GlobalTheory.SlopeEigen
