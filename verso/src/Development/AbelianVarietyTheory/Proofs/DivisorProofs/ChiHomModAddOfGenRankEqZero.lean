import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GenericFiniteMaps
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteCohOfForallModification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EulerCharHomAdditiveShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PushforwardTwistHomDualIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistHomModuleIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PushforwardHomAdjunctionIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenRankPushforwardAmpleTwist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointPreimageGeneric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericRankPushforward
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurfaceAlterationEffectiveCartier
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSubbundleKernelOfLocallyPrincipal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsImagePrincipalOfEffCartier
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointNotMemSupportCokernelOfNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntersectionNumberEqGenericRankMulProjCurve
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowVanishingIdealLeAnnihilator
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportPushforwardSubsetImageOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (toMod)
open GlobalTheory.VB
open GlobalTheory.IndefiniteRowSideFullHecke.GenericFiniteMaps
open GlobalTheory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RRTorsion

def defect (k : Type) [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)] (E : X.Modules) (r : ℕ)
    (G : X.Modules) : ℤ :=
  chi k (homMod (dual E) G) + chi k (homMod E G) - 2 * (r : ℤ) * chi k G

section General

variable {k : Type} [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)]

omit [Field k] [Algebra k Γ(X, ⊤)] in

/- English proof (translation)
Rewrite using `[IsZero.iff_id_eq_zero]`. Use extensionality with `V ψ : 3`. Use `VB.hom_ext fun W hW s => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `homApp ψ hW s = 0`. Break down `h with h | h` into its components or cases.

Establish `e : s = 0`. Establish `: (𝟙 E : E ⟶ E).app W s = (0 : E ⟶ E).app W s` using `by rw [h.eq_of_src (𝟙 E) 0]`. Conclude with `this`. Rewrite using `[e, map_zero]`. Establish `: (𝟙 G : G ⟶ G).app W (homApp ψ hW s) = (0 : G ⟶ G).app W (homApp ψ hW s)`.

Rewrite using `[h.eq_of_src (𝟙 G) 0]`. Conclude with `this`.
-/
theorem isZero_homMod {E G : X.Modules} (h : IsZero E ∨ IsZero G) : IsZero (homMod E G) := by
  rw [IsZero.iff_id_eq_zero]
  ext V ψ : 3
  refine VB.hom_ext fun W hW s => ?_
  change homApp ψ hW s = 0
  rcases h with h | h
  · have e : s = 0 := by
      have : (𝟙 E : E ⟶ E).app W s = (0 : E ⟶ E).app W s := by rw [h.eq_of_src (𝟙 E) 0]
      exact this
    rw [e, map_zero]
  · have : (𝟙 G : G ⟶ G).app W (homApp ψ hW s) = (0 : G ⟶ G).app W (homApp ψ hW s) := by
      rw [h.eq_of_src (𝟙 G) 0]
    exact this

/- English proof (translation)
Rewrite using `[defect, chi_eq_zero_of_isZero k (isZero_homMod (.inr h)), chi_eq_zero_of_isZero k (isZero_homMod (.inr h)), chi_eq_zero_of_isZero k h]`. Simplify using the standard rewrite rules.
-/
theorem defect_of_isZero (E : X.Modules) (r : ℕ) {G : X.Modules} (h : IsZero G) :
    defect k E r G = 0 := by
  rw [defect, chi_eq_zero_of_isZero k (isZero_homMod (.inr h)),
    chi_eq_zero_of_isZero k (isZero_homMod (.inr h)), chi_eq_zero_of_isZero k h]
  simp

/- English proof (translation)
Rewrite using `[defect, chi_eq_zero_of_isZero k (isZero_homMod (.inl (isVB_zero_iff.1 hE.dual))), chi_eq_zero_of_isZero k (isZero_homMod (.inl (isVB_zero_iff.1 hE)))]`. Simplify using the standard rewrite rules.
-/
theorem defect_rank_zero {E : X.Modules} (hE : IsVB E 0) (G : X.Modules) : defect k E 0 G = 0 := by
  rw [defect, chi_eq_zero_of_isZero k (isZero_homMod (.inl (isVB_zero_iff.1 hE.dual))),
    chi_eq_zero_of_isZero k (isZero_homMod (.inl (isVB_zero_iff.1 hE)))]
  simp

/- English proof (translation)
Establish `hfc : ∀ (G : X.Modules), QCoh.IsFiniteQC G → FiniteCoh k G` using `fun G _ => finiteCoh_of_isProjOver (algebraMap_eq_strHom k X) G hp`. Establish `H : ∀ W : X.Modules, IsVB W r → chi k (homMod W S.X₂) = chi k (homMod W S.X₁) + chi k (homMod W S.X₃)` using `fun W hW => HomExact.chi_shortExact_mk k (HomExact.shortExact_homMod hW S hS) (hfc _ (PtNorm.isFiniteQC_homMod hW)) (hfc _ (PtNorm.isFiniteQC_homMod hW))`. Simplify using `only [defect, H _ hE, H _ hE.dual, chi_shortExact hS (hfc _ h₁) (hfc _ h₃)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem defect_shortExact (hp : IsProjOver (strHom k X)) {E : X.Modules} {r : ℕ} (hE : IsVB E r)
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (h₁ : QCoh.IsFiniteQC S.X₁)
    (h₂ : QCoh.IsFiniteQC S.X₂) (h₃ : QCoh.IsFiniteQC S.X₃) :
    defect k E r S.X₂ = defect k E r S.X₁ + defect k E r S.X₃ := by
  have hfc : ∀ (G : X.Modules), QCoh.IsFiniteQC G → FiniteCoh k G := fun G _ =>
    finiteCoh_of_isProjOver (algebraMap_eq_strHom k X) G hp
  have H : ∀ W : X.Modules, IsVB W r →
      chi k (homMod W S.X₂) = chi k (homMod W S.X₁) + chi k (homMod W S.X₃) := fun W hW =>
    HomExact.chi_shortExact_mk k (HomExact.shortExact_homMod hW S hS)
      (hfc _ (PtNorm.isFiniteQC_homMod hW)) (hfc _ (PtNorm.isFiniteQC_homMod hW))
  simp only [defect, H _ hE, H _ hE.dual, chi_shortExact hS (hfc _ h₁) (hfc _ h₃)]
  ring

/- English proof (translation)
Establish `hθ : IsIso (DualPull.theta g E)` using `DualPull.isIso_theta g hE`. Rewrite using `[defect, defect, ← chi_congr k (HomPull.pushHomIso g (dual E) G), ← chi_congr k (HomPull.pushHomIso g E G), chi_pushforward_of_isClosedImmersion hg, chi_pushforward_of_isClosedImmersion hg, chi_pushforward_of_isClosedImmersion hg, chi_congr k (ProjFml.homIsoLeft (@asIso _ _ _ _ ( …`.
-/
theorem defect_pushforward {Y : Scheme.{0}} [Algebra k Γ(Y, ⊤)] (g : Y ⟶ X) [IsClosedImmersion g]
    (hg : ∀ a : k, g.appTop (algebraMap k Γ(X, ⊤) a) = algebraMap k Γ(Y, ⊤) a) {E : X.Modules} {r : ℕ}
    (hE : IsVB E r) (G : Y.Modules) :
    defect k E r ((Scheme.Modules.pushforward g).obj G) =
      defect k ((Scheme.Modules.pullback g).obj E) r G := by
  have hθ : IsIso (DualPull.theta g E) := DualPull.isIso_theta g hE
  rw [defect, defect, ← chi_congr k (HomPull.pushHomIso g (dual E) G),
    ← chi_congr k (HomPull.pushHomIso g E G), chi_pushforward_of_isClosedImmersion hg,
    chi_pushforward_of_isClosedImmersion hg, chi_pushforward_of_isClosedImmersion hg,
    chi_congr k (ProjFml.homIsoLeft (@asIso _ _ _ _ (DualPull.theta g E) hθ) G)]

/- English proof (translation)
Use `hE.isIso_toBidual_of_local_frames` as an intermediate fact. Establish `e : chi k (twist E M) = chi k (twist (dual (dual E)) M)` using `chi_congr k ((twistFunctor M).mapIso (@asIso _ _ _ _ (cartierDualToBidual E) this))`. Rewrite using `[defect, ← chi_congr k (TwistHomMod.iso (dual E) (structureModule X) M), ← chi_congr k (TwistHomMod.iso E (structureModule X) M), e]`. Both sides reduce to the same expression.
-/
theorem defect_twist {E : X.Modules} {r : ℕ} (hE : IsVB E r) (M : LB X) :
    defect k E r (twist (structureModule X) M) =
      chi k (twist E M) + chi k (twist (dual E) M) - 2 * (r : ℤ) * chi k (twist (structureModule X) M) := by
  have := hE.isIso_toBidual_of_local_frames
  have e : chi k (twist E M) = chi k (twist (dual (dual E)) M) :=
    chi_congr k ((twistFunctor M).mapIso (@asIso _ _ _ _ (cartierDualToBidual E) this))
  rw [defect, ← chi_congr k (TwistHomMod.iso (dual E) (structureModule X) M),
    ← chi_congr k (TwistHomMod.iso E (structureModule X) M), e]
  rfl

/- English proof (translation)
Use `(isVB_structureModule X).isFiniteQC` as an intermediate fact. Establish `hv : DiffVanish (1 + 1) (chiPic k (structureModule X))` using `diffVanish_chiPic_of_isProjOver (algebraMap_eq_strHom k X) _ hp (by rw [QCoh.suppDim_structureModule]; exact hd)`. Use `set f := chiPic k (structureModule X) with hf`. Use `set c := CechPic.cls _ h.isLB_det with hc`. Use `set m := CechPic.cls M hM with hm`.

Establish `e : ∀ (W : X.Modules) (hW : IsVB W 1), chi k (twist W M) = f (CechPic.cls _ hW.isLB_det + m)` using `fun W hW => by`. Rewrite using `[hf, ← chiPic_twist, hm, chiPic_cls]`. Conclude with `chi_congr k ((twistFunctor M).mapIso (hW.isoDet ≪≫ (Twist.unitTwistIso _).symm))`. Establish `e₂ : CechPic.cls _ h.dual.isLB_det = -c`. Rewrite using `[← (CechPic.cls_eq_iff (CechPic.isLB_dual h.isLB_det) _).2 h.lbIso_det_dual, CechPic.cls_dual h.isLB_det]`.

Establish `e₅` using `congrFun (hv.multiDiff_eq_zero (g := fun _ : Fin 2 => c) (by simp)) (c + m)`. Rewrite `e₅` using `[multiDiff_const]`. Simplify using `only [Function.iterate_succ, Function.iterate_zero, Function.comp, id, bwdDiff_apply, Pi.zero_apply] at e₅`. Rewrite using `[e N h, e _ h.dual, e₂, ← hc]`. Express the relevant statement in the definitionally equal form `_ = 2 * f m`.

Rewrite `e₅` using `[show c + m - c = m by abel, show m - c = -c + m by abel]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem chi_twist_line (hp : IsProjOver (strHom k X)) (hd : topologicalKrullDim X ≤ 1) {N : X.Modules}
    (h : IsVB N 1) {M : LB X} (hM : M.IsLB) :
    chi k (twist N M) + chi k (twist (dual N) M) = 2 * chi k (twist (structureModule X) M) := by
  have := (isVB_structureModule X).isFiniteQC
  have hv : DiffVanish (1 + 1) (chiPic k (structureModule X)) :=
    diffVanish_chiPic_of_isProjOver (algebraMap_eq_strHom k X) _ hp
      (by rw [QCoh.suppDim_structureModule]; exact hd)
  set f := chiPic k (structureModule X) with hf
  set c := CechPic.cls _ h.isLB_det with hc
  set m := CechPic.cls M hM with hm
  have e : ∀ (W : X.Modules) (hW : IsVB W 1), chi k (twist W M) = f (CechPic.cls _ hW.isLB_det + m) :=
    fun W hW => by
      rw [hf, ← chiPic_twist, hm, chiPic_cls]
      exact chi_congr k ((twistFunctor M).mapIso (hW.isoDet ≪≫ (Twist.unitTwistIso _).symm))
  have e₂ : CechPic.cls _ h.dual.isLB_det = -c := by
    rw [← (CechPic.cls_eq_iff (CechPic.isLB_dual h.isLB_det) _).2 h.lbIso_det_dual,
      CechPic.cls_dual h.isLB_det]
  have e₅ := congrFun (hv.multiDiff_eq_zero (g := fun _ : Fin 2 => c) (by simp)) (c + m)
  rw [multiDiff_const] at e₅
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp, id, bwdDiff_apply,
    Pi.zero_apply] at e₅
  rw [e N h, e _ h.dual, e₂, ← hc]
  change _ = 2 * f m
  rw [show c + m - c = m by abel, show m - c = -c + m by abel] at e₅
  linarith

/- English proof (translation)
Establish `hO : QCoh.IsFiniteQC (structureModule X)` using `(isVB_structureModule X).isFiniteQC`. Establish `hgO : genRank (structureModule X) = 1` using `(isVB_structureModule X).genRank_eq`. Take `⟨hprop, A, hA⟩` from `isProper_and_exists_isAmpleLB_of_isProjOver hp`. Establish `: IsLocallyNoetherian X` using `LocallyOfFiniteType.isLocallyNoetherian (strHom k X)`. Proceed by induction on `n with`.

Consider the case `zero`. Introduce `G hG h0`. Rewrite using `[htor G hG h0]`. Simplify using the standard rewrite rules. Consider the case `succ n ih`.

Introduce `F hF hr`. Take `⟨m, hg, s, hs⟩` from `((hA.eventually_isGloballyGenerated_twist F).and (hA.eventually_exists_mono_cutHom_pow (structureModule X))).exists`. Establish `hN` using `isLB_lbPow hA.isLB m`. Establish `hP` using `Twist.isLB_lbZPow hN (-1)`. Establish `hFN : genRank (twist F (lbPow A m)) ≠ 0` using `by rw [genRank_twist hN]; omega`.

Take `⟨t, ht⟩` from `exists_germ_ne_zero hg hFN`. Establish `hmt` using `mono_sectionHom t ht`. Take `⟨e₁⟩` from `nonempty_twist_twist_iso_of_cls_eq F hN hP (LB.isLB_triv X) (by rw [cls_lbZPow hN (-1) hP, cls_triv]; simp)`. Take `⟨e₂⟩` from `nonempty_twist_iso_of_cls_eq_zero F (LB.isLB_triv X) (cls_triv _)`. Establish `hM : QCoh.IsFiniteQC (twistZ (structureModule X) (lbPow A m) (-1))` using `Twist.isFiniteQC_twist hP`.

Establish `hmg : Mono (Twist.map (lbZPow (lbPow A m) (-1)) (QCoh.sectionHom t))` using `(Twist.mono_map_iff hP _).2 hmt`. Take `⟨M, f, g, hM, hf, hg, hM1⟩ : ∃ (M : X.Modules) (f : M ⟶ structureModule X) (g : M ⟶ F), QCoh.IsFiniteQC M ∧ Mono f ∧ Mono g ∧ genRank M = 1` from `⟨_, cutHom (structureModule X) hN s, Twist.map (lbZPow (lbPow A m) (-1)) (QCoh.sectionHom t) ≫ e₁.hom ≫ e₂.hom, hM, hs, inferInstance, (genRank_twist hP).trans hgO⟩`. Establish `hSf : (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).ShortExact` using `{ exact := ShortComplex.exact_cokernel f }`. Establish `hSg : (ShortComplex.mk g (cokernel.π g) (cokernel.condition g)).ShortExact` using `{ exact := ShortComplex.exact_cokernel g }`. Establish `hCf : QCoh.IsFiniteQC (cokernel f)` using `QCoh.IsFiniteQC.of_epi (cokernel.π f)`.

Establish `hCg : QCoh.IsFiniteQC (cokernel g)` using `QCoh.IsFiniteQC.of_epi (cokernel.π g)`. Establish `rf` using `genRank_shortExact hSf`. Establish `rg` using `genRank_shortExact hSg`. Simplify using `only at rf rg`. Establish `e1` using `defect_shortExact hp hE _ hSf hM hO hCf`.

Establish `e2` using `defect_shortExact hp hE _ hSg hM hF hCg`. Simplify using `only at e1 e2`. Rewrite `e1` using `[htor _ hCf (by omega)]`. Rewrite using `[e2, ih _ hCg (by omega), e1]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem defect_eq_genRank_mul [IsIntegral X] (hp : IsProjOver (strHom k X)) {E : X.Modules} {r : ℕ}
    (hE : IsVB E r)
    (htor : ∀ G : X.Modules, QCoh.IsFiniteQC G → genRank G = 0 → defect k E r G = 0) (n : ℕ) :
    ∀ G : X.Modules, QCoh.IsFiniteQC G → genRank G = n →
      defect k E r G = n * defect k E r (structureModule X) := by
  have hO : QCoh.IsFiniteQC (structureModule X) := (isVB_structureModule X).isFiniteQC
  have hgO : genRank (structureModule X) = 1 := (isVB_structureModule X).genRank_eq
  obtain ⟨hprop, A, hA⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hp
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (strHom k X)
  induction n with
  | zero =>
    intro G hG h0
    rw [htor G hG h0]; simp
  | succ n ih =>
    intro F hF hr
    obtain ⟨m, hg, s, hs⟩ := ((hA.eventually_isGloballyGenerated_twist F).and
      (hA.eventually_exists_mono_cutHom_pow (structureModule X))).exists
    have hN := isLB_lbPow hA.isLB m
    have hP := Twist.isLB_lbZPow hN (-1)
    have hFN : genRank (twist F (lbPow A m)) ≠ 0 := by rw [genRank_twist hN]; omega
    obtain ⟨t, ht⟩ := exists_germ_ne_zero hg hFN
    have hmt := mono_sectionHom t ht
    obtain ⟨e₁⟩ := nonempty_twist_twist_iso_of_cls_eq F hN hP (LB.isLB_triv X)
      (by rw [cls_lbZPow hN (-1) hP, cls_triv]; simp)
    obtain ⟨e₂⟩ := nonempty_twist_iso_of_cls_eq_zero F (LB.isLB_triv X) (cls_triv _)
    have hM : QCoh.IsFiniteQC (twistZ (structureModule X) (lbPow A m) (-1)) :=
      Twist.isFiniteQC_twist hP
    have hmg : Mono (Twist.map (lbZPow (lbPow A m) (-1)) (QCoh.sectionHom t)) :=
      (Twist.mono_map_iff hP _).2 hmt
    obtain ⟨M, f, g, hM, hf, hg, hM1⟩ : ∃ (M : X.Modules) (f : M ⟶ structureModule X) (g : M ⟶ F),
        QCoh.IsFiniteQC M ∧ Mono f ∧ Mono g ∧ genRank M = 1 :=
      ⟨_, cutHom (structureModule X) hN s,
        Twist.map (lbZPow (lbPow A m) (-1)) (QCoh.sectionHom t) ≫ e₁.hom ≫ e₂.hom, hM, hs,
        inferInstance, (genRank_twist hP).trans hgO⟩
    have hSf : (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).ShortExact :=
      { exact := ShortComplex.exact_cokernel f }
    have hSg : (ShortComplex.mk g (cokernel.π g) (cokernel.condition g)).ShortExact :=
      { exact := ShortComplex.exact_cokernel g }
    have hCf : QCoh.IsFiniteQC (cokernel f) := QCoh.IsFiniteQC.of_epi (cokernel.π f)
    have hCg : QCoh.IsFiniteQC (cokernel g) := QCoh.IsFiniteQC.of_epi (cokernel.π g)
    have rf := genRank_shortExact hSf
    have rg := genRank_shortExact hSg
    simp only at rf rg
    have e1 := defect_shortExact hp hE _ hSf hM hO hCf
    have e2 := defect_shortExact hp hE _ hSg hM hF hCg
    simp only at e1 e2
    rw [htor _ hCf (by omega)] at e1
    rw [e2, ih _ hCg (by omega), e1]
    push_cast; ring

/- English proof (translation)
Take `⟨A, hA⟩` from `(isProper_and_exists_isAmpleLB_of_isProjOver hp).2`. Use `hE.dual.isFiniteQC` as an intermediate fact. Take `⟨n, m, ψ, hψ⟩` from `(hA.eventually_exists_epi_sigma (dual E)).exists`. Establish `hM : IsVB (toMod (lbZPow A (-n))) 1` using `isVB_toMod (Twist.isLB_lbZPow hA.isLB (-n))`. Establish `hne : ¬ IsZero (dual E)` using `fun hz => by haveI : Nonempty X := IsIntegral.nonempty`.

Use `hE.dual.rank_unique (isVB_zero_iff.2 hz)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Take `⟨i, hi⟩ : ∃ i, Sigma.ι (fun _ : Fin m => toMod (lbZPow A (-n))) i ≫ ψ ≠ 0` from `by by_contra! h`. Establish `h0 : ψ = 0` using `Sigma.hom_ext _ _ fun i => by simp [h i]`. Substitute `h0` using the available equality.

Conclude with `hne (IsZero.of_epi_zero (∐ fun _ : Fin m => toMod (lbZPow A (-n))) (dual E))`. Use `set χ := Sigma.ι (fun _ : Fin m => toMod (lbZPow A (-n))) i ≫ ψ with hχ`. Use `⟨dual (toMod (lbZPow A (-n))), cartierDualToBidual E ≫ dualMap χ, hM.dual, fun h0 => hi ?_⟩` and prove the remaining obligations. Use `hE.isIso_toBidual_of_local_frames` as an intermediate fact. Use `hE.dual.isIso_toBidual_of_local_frames` as an intermediate fact.

Establish `h1 : dualMap χ = 0`. Rewrite using `[← cancel_epi (cartierDualToBidual E), h0, comp_zero]`. Establish `h2 : χ ≫ cartierDualToBidual (dual E) = 0`. Rewrite using `[toBidual_naturality_dualSheafTranspose, h1, dualMap_zero, comp_zero]`. Rewrite using `[← cancel_mono (cartierDualToBidual (dual E)), h2, zero_comp]`.
-/
theorem exists_hom_line [IsIntegral X] (hp : IsProjOver (strHom k X)) {E : X.Modules} {r : ℕ}
    (hE : IsVB E (r + 1)) : ∃ (L : X.Modules) (φ : E ⟶ L), IsVB L 1 ∧ φ ≠ 0 := by
  obtain ⟨A, hA⟩ := (isProper_and_exists_isAmpleLB_of_isProjOver hp).2
  have := hE.dual.isFiniteQC
  obtain ⟨n, m, ψ, hψ⟩ := (hA.eventually_exists_epi_sigma (dual E)).exists
  have hM : IsVB (toMod (lbZPow A (-n))) 1 := isVB_toMod (Twist.isLB_lbZPow hA.isLB (-n))
  have hne : ¬ IsZero (dual E) := fun hz => by
    haveI : Nonempty X := IsIntegral.nonempty
    have := hE.dual.rank_unique (isVB_zero_iff.2 hz)
    omega
  obtain ⟨i, hi⟩ : ∃ i, Sigma.ι (fun _ : Fin m => toMod (lbZPow A (-n))) i ≫ ψ ≠ 0 := by
    by_contra! h
    have h0 : ψ = 0 := Sigma.hom_ext _ _ fun i => by simp [h i]
    subst h0
    exact hne (IsZero.of_epi_zero (∐ fun _ : Fin m => toMod (lbZPow A (-n))) (dual E))
  set χ := Sigma.ι (fun _ : Fin m => toMod (lbZPow A (-n))) i ≫ ψ with hχ
  refine ⟨dual (toMod (lbZPow A (-n))), cartierDualToBidual E ≫ dualMap χ, hM.dual, fun h0 => hi ?_⟩
  have := hE.isIso_toBidual_of_local_frames
  have := hE.dual.isIso_toBidual_of_local_frames
  have h1 : dualMap χ = 0 := by
    rw [← cancel_epi (cartierDualToBidual E), h0, comp_zero]
  have h2 : χ ≫ cartierDualToBidual (dual E) = 0 := by
    rw [toBidual_naturality_dualSheafTranspose, h1, dualMap_zero, comp_zero]
  rw [← cancel_mono (cartierDualToBidual (dual E)), h2, zero_comp]

/- English proof (translation)
Take `⟨Y, b, hb, hproj, hiso⟩` from `ProjBlowup.exists_blowup (strHom k X) hp J`. Set `V : X.Opens` to `J.support.compl`. Establish `hbV : IsIso (b ∣_ V)` using `hiso V fun _ hx => hx`. Establish `: Nonempty V.toScheme` using `⟨⟨genericPoint X, hJ⟩⟩`. Establish `: IsIntegral V.toScheme` using `isIntegral_of_isOpenImmersion V.ι`.

Establish `: Nonempty (b ⁻¹ᵁ V).toScheme` using `⟨inv (b ∣_ V) (Classical.arbitrary _)⟩`. Establish `: IsIntegral (b ⁻¹ᵁ V).toScheme` using `isIntegral_of_isOpenImmersion (b ∣_ V)`. Establish `hU : (J.comap b).support.compl = b ⁻¹ᵁ V`. Use extensionality with `y`. Conclude with `not_congr (ProjBlowup.mem_support_comap J b y)`.

Establish `hdom : IsSchemeTheoreticallyDominant (b ⁻¹ᵁ V).ι` using `hU ▸ ProjBlowup.isSchemeTheoreticallyDominant_compl_of_effCartier Y _ hb.1`. Establish `: IsNoetherian Y` using `isNoetherian_of_isProjOver hproj`. Establish `: IsIntegral Y`. Establish `: IsReduced Y` using `IsSchemeTheoreticallyDominant.isReduced (b ⁻¹ᵁ V).ι`. Establish `h` using `((IrreducibleSpace.isIrreducible_univ (b ⁻¹ᵁ V).toScheme).image _ (b ⁻¹ᵁ V).ι.continuous.continuousOn).closure`.

Rewrite `h` using `[Set.image_univ, (b ⁻¹ᵁ V).ι.denseRange.closure_range]`. Establish `: IrreducibleSpace Y` using `(irreducibleSpace_def _).2 h`. Conclude with `isIntegral_of_irreducibleSpace_of_isReduced Y`. Establish `hfac : (b ⁻¹ᵁ V).ι ≫ b = b ∣_ V ≫ V.ι` using `(morphismRestrict_ι b V).symm`. Establish `hoi : IsOpenImmersion ((b ⁻¹ᵁ V).ι ≫ b)` using `by rw [hfac]; infer_instance`.

Establish `hg : (b ⁻¹ᵁ V).ι (genericPoint _) = genericPoint Y` using `genericPoint_eq_of_isOpenImmersion _`. Establish `hgen : b (genericPoint Y) = genericPoint X`. Rewrite using `[← hg, ← Scheme.Hom.comp_apply]`. Conclude with `genericPoint_eq_of_isOpenImmersion _`. Use `letI : Algebra k Γ(Y, ⊤) := (b.appTop.hom.comp (algebraMap k Γ(X, ⊤))).toAlgebra`.

Establish `hstr : b ≫ strHom k X = strHom k Y` using `comp_strHom (g := b) fun _ => rfl`. Establish `hprojY : IsProjOver (strHom k Y)` using `hstr ▸ hproj`. Establish `hPX` using `(isProper_and_exists_isAmpleLB_of_isProjOver hp).1`. Establish `hPY` using `(isProper_and_exists_isAmpleLB_of_isProjOver hprojY).1`. Establish `hdim : topologicalKrullDim Y = topologicalKrullDim X` using `OpenDim.topologicalKrullDim_eq_of_isIso_restrict k X Y (strHom k X) (strHom k Y) b inferInstance inferInstance hstr V ⟨genericPoint X, hJ⟩ hbV`.

Establish `hst : IsIso (b.stalkMap (genericPoint Y))`. Establish `h1 : IsIso (((b ⁻¹ᵁ V).ι ≫ b).stalkMap (genericPoint _))` using `inferInstance`. Rewrite `h1` using `[Scheme.Hom.stalkMap_comp]`. Establish `h3 : IsIso (((b ⁻¹ᵁ V).ι).stalkMap (genericPoint (b ⁻¹ᵁ V).toScheme))` using `inferInstance`. Establish `h2 : IsIso (b.stalkMap ((b ⁻¹ᵁ V).ι (genericPoint _)))` using `@IsIso.of_isIso_comp_right _ _ _ _ _ (b.stalkMap ((b ⁻¹ᵁ V).ι (genericPoint _))) (((b ⁻¹ᵁ V).ι).stalkMap (genericPoint _)) h3 h1`.

Conclude with `hg ▸ h2`. Establish `: IsProper (b ≫ strHom k X)` using `hstr ▸ hPY`. Establish `: IsProper b` using `.of_comp b (strHom k X)`. Establish `hfib : ∀ x : Y, b x = genericPoint X → x = genericPoint Y` using `fun x hx => by`. Establish `hxV : x ∈ b ⁻¹ᵁ V` using `show b x ∈ V from hx ▸ hJ`.

Establish `e : ((b ⁻¹ᵁ V).ι ≫ b) ⟨x, hxV⟩ = ((b ⁻¹ᵁ V).ι ≫ b) (genericPoint _)`. Use `(Scheme.Hom.comp_apply _ _ _).trans (.trans ?_ (Scheme.Hom.comp_apply _ _ _).symm)` and prove the remaining obligations. Rewrite using `[hg, hgen]`. Conclude with `hx`. Rewrite using `[← hg, ← ((b ⁻¹ᵁ V).ι ≫ b).isOpenEmbedding.injective e]`.

Both sides reduce to the same expression. Establish `hnbhd : ∀ W : Y.Opens, genericPoint Y ∈ W → ∃ U : X.Opens, genericPoint X ∈ U ∧ b ⁻¹ᵁ U ≤ W`. Introduce `W hW`. Establish `hZ` using `b.isClosedMap _ W.isOpen.isClosed_compl`. Use `⟨⟨_, hZ.isOpen_compl⟩, ?_, ?_⟩` and prove the remaining obligations.

Introduce and unpack `⟨x, hx, hxη⟩`. Conclude with `hx ((hfib x hxη) ▸ hW)`. Introduce `y hy`. Assume the negation of the conclusion as `hyV`. Conclude with `hy ⟨y, hyV, rfl⟩`.

Establish `hs : b (genericPoint Y) ⤳ genericPoint X` using `by rw [hgen]`. Use `⟨Y, _, ‹_›, b, hprojY, hdim, hstr, fun F => ?_, hb.1⟩` and prove the remaining obligations. Rewrite using `[genRank_pushforward_of_generic X Y b hs hnbhd]`. Use `(congrArg (· * genRank F) ?_).trans (one_mul _)` and prove the remaining obligations. Use `PushGenRank.isIso_stalkSpecializes hs hgen` as an intermediate fact.

Use `letI := (X.presheaf.stalkSpecializes hs ≫ b.stalkMap (genericPoint Y)).hom.toAlgebra`. Conclude with `Module.finrank_of_bijective_algebraMap (ConcreteCategory.bijective_of_isIso (X.presheaf.stalkSpecializes hs ≫ b.stalkMap (genericPoint Y)))`.
-/
theorem exists_model [IsIntegral X] (hp : IsProjOver (strHom k X)) (J : X.IdealSheafData)
    (hJ : genericPoint X ∉ J.support) :
    ∃ (Y : Scheme.{0}) (_ : Algebra k Γ(Y, ⊤)) (_ : IsIntegral Y) (ρ : Y ⟶ X),
      IsProjOver (strHom k Y) ∧ topologicalKrullDim Y = topologicalKrullDim X ∧
      ρ ≫ strHom k X = strHom k Y ∧
      (∀ F : Y.Modules, genRank ((Scheme.Modules.pushforward ρ).obj F) = genRank F) ∧
      ReciprocityTheory.AnForm.R.FinalTheorems.EffCartier (J.comap ρ) := by
  obtain ⟨Y, b, hb, hproj, hiso⟩ := ProjBlowup.exists_blowup (strHom k X) hp J
  let V : X.Opens := J.support.compl
  have hbV : IsIso (b ∣_ V) := hiso V fun _ hx => hx
  have : Nonempty V.toScheme := ⟨⟨genericPoint X, hJ⟩⟩
  have : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
  have : Nonempty (b ⁻¹ᵁ V).toScheme := ⟨inv (b ∣_ V) (Classical.arbitrary _)⟩
  have : IsIntegral (b ⁻¹ᵁ V).toScheme := isIntegral_of_isOpenImmersion (b ∣_ V)
  have hU : (J.comap b).support.compl = b ⁻¹ᵁ V := by
    ext y
    exact not_congr (ProjBlowup.mem_support_comap J b y)
  have hdom : IsSchemeTheoreticallyDominant (b ⁻¹ᵁ V).ι :=
    hU ▸ ProjBlowup.isSchemeTheoreticallyDominant_compl_of_effCartier Y _ hb.1
  have : IsNoetherian Y := isNoetherian_of_isProjOver hproj
  have : IsIntegral Y := by
    have : IsReduced Y := IsSchemeTheoreticallyDominant.isReduced (b ⁻¹ᵁ V).ι
    have h := ((IrreducibleSpace.isIrreducible_univ (b ⁻¹ᵁ V).toScheme).image _
      (b ⁻¹ᵁ V).ι.continuous.continuousOn).closure
    rw [Set.image_univ, (b ⁻¹ᵁ V).ι.denseRange.closure_range] at h
    have : IrreducibleSpace Y := (irreducibleSpace_def _).2 h
    exact isIntegral_of_irreducibleSpace_of_isReduced Y
  have hfac : (b ⁻¹ᵁ V).ι ≫ b = b ∣_ V ≫ V.ι := (morphismRestrict_ι b V).symm
  have hoi : IsOpenImmersion ((b ⁻¹ᵁ V).ι ≫ b) := by rw [hfac]; infer_instance
  have hg : (b ⁻¹ᵁ V).ι (genericPoint _) = genericPoint Y := genericPoint_eq_of_isOpenImmersion _
  have hgen : b (genericPoint Y) = genericPoint X := by
    rw [← hg, ← Scheme.Hom.comp_apply]
    exact genericPoint_eq_of_isOpenImmersion _
  letI : Algebra k Γ(Y, ⊤) := (b.appTop.hom.comp (algebraMap k Γ(X, ⊤))).toAlgebra
  have hstr : b ≫ strHom k X = strHom k Y := comp_strHom (g := b) fun _ => rfl
  have hprojY : IsProjOver (strHom k Y) := hstr ▸ hproj
  have hPX := (isProper_and_exists_isAmpleLB_of_isProjOver hp).1
  have hPY := (isProper_and_exists_isAmpleLB_of_isProjOver hprojY).1
  have hdim : topologicalKrullDim Y = topologicalKrullDim X :=
    OpenDim.topologicalKrullDim_eq_of_isIso_restrict k X Y (strHom k X) (strHom k Y) b
      inferInstance inferInstance hstr V ⟨genericPoint X, hJ⟩ hbV
  have hst : IsIso (b.stalkMap (genericPoint Y)) := by
    have h1 : IsIso (((b ⁻¹ᵁ V).ι ≫ b).stalkMap (genericPoint _)) := inferInstance
    rw [Scheme.Hom.stalkMap_comp] at h1
    have h3 : IsIso (((b ⁻¹ᵁ V).ι).stalkMap (genericPoint (b ⁻¹ᵁ V).toScheme)) := inferInstance
    have h2 : IsIso (b.stalkMap ((b ⁻¹ᵁ V).ι (genericPoint _))) :=
      @IsIso.of_isIso_comp_right _ _ _ _ _ (b.stalkMap ((b ⁻¹ᵁ V).ι (genericPoint _)))
        (((b ⁻¹ᵁ V).ι).stalkMap (genericPoint _)) h3 h1
    exact hg ▸ h2
  have : IsProper (b ≫ strHom k X) := hstr ▸ hPY
  have : IsProper b := .of_comp b (strHom k X)
  have hfib : ∀ x : Y, b x = genericPoint X → x = genericPoint Y := fun x hx => by
    have hxV : x ∈ b ⁻¹ᵁ V := show b x ∈ V from hx ▸ hJ
    have e : ((b ⁻¹ᵁ V).ι ≫ b) ⟨x, hxV⟩ = ((b ⁻¹ᵁ V).ι ≫ b) (genericPoint _) := by
      refine (Scheme.Hom.comp_apply _ _ _).trans (.trans ?_ (Scheme.Hom.comp_apply _ _ _).symm)
      rw [hg, hgen]
      exact hx
    rw [← hg, ← ((b ⁻¹ᵁ V).ι ≫ b).isOpenEmbedding.injective e]
    rfl
  have hnbhd : ∀ W : Y.Opens, genericPoint Y ∈ W →
      ∃ U : X.Opens, genericPoint X ∈ U ∧ b ⁻¹ᵁ U ≤ W := by
    intro W hW
    have hZ := b.isClosedMap _ W.isOpen.isClosed_compl
    refine ⟨⟨_, hZ.isOpen_compl⟩, ?_, ?_⟩
    · rintro ⟨x, hx, hxη⟩
      exact hx ((hfib x hxη) ▸ hW)
    · intro y hy
      by_contra hyV
      exact hy ⟨y, hyV, rfl⟩
  have hs : b (genericPoint Y) ⤳ genericPoint X := by rw [hgen]
  refine ⟨Y, _, ‹_›, b, hprojY, hdim, hstr, fun F => ?_, hb.1⟩
  rw [genRank_pushforward_of_generic X Y b hs hnbhd]
  refine (congrArg (· * genRank F) ?_).trans (one_mul _)
  have := PushGenRank.isIso_stalkSpecializes hs hgen
  letI := (X.presheaf.stalkSpecializes hs ≫ b.stalkMap (genericPoint Y)).hom.toAlgebra
  exact Module.finrank_of_bijective_algebraMap
    (ConcreteCategory.bijective_of_isIso (X.presheaf.stalkSpecializes hs ≫ b.stalkMap (genericPoint Y)))

/- English proof (translation)
Establish `hPT` using `(isProper_and_exists_isAmpleLB_of_isProjOver hX).1`. Establish `hPT'` using `(isProper_and_exists_isAmpleLB_of_isProjOver hY).1`. Establish `: IsProper (ρ ≫ strHom k X)` using `hρ ▸ hPT'`. Establish `: IsProper ρ` using `.of_comp ρ (strHom k X)`. Establish `: IsLocallyNoetherian X` using `LocallyOfFiniteType.isLocallyNoetherian (strHom k X)`.

Establish `: CompactSpace X` using `QuasiCompact.compactSpace_of_compactSpace (strHom k X)`. Use `isAffineHom_diagonal_of_isSeparated (strHom k X)` as an intermediate fact. Establish `hπ : ∀ r : k, ρ.appTop (algebraMap k Γ(X, ⊤) r) = algebraMap k Γ(Y, ⊤) r` using `fun r => by`. Rewrite using `[algebraMap_eq_strHom k X, algebraMap_eq_strHom k Y, ← hρ, Scheme.Hom.comp_appTop]`. Both sides reduce to the same expression.

Take `⟨m, D, hD, hc⟩` from `exists_fin_affine_cover (X := X) (V := ⊤) isCompact_univ`. Establish `hD'` using `isAffineOpen_finset_biInf hD`. Establish `hV : ∀ᶠ n : ℕ in atTop, ∀ I : Finset (Fin m), I.Nonempty → ∀ q, 0 < q → Subsingleton (cohOn (twist H (lbPow L n)) (ρ ⁻¹ᵁ (⨅ i ∈ I, D i)) q)` using `eventually_all.2 fun I => eventually_all.2 fun hI => GlobalTheory.ProperFinite.eventually_subsingleton_cohOn ρ hL H (hD' I hI)`. Use `filter_upwards [hV] with n hn`. Use `GlobalTheory.Twist.isFiniteQC_twist (F := H) (isLB_lbPow hL.isLB n)` as an intermediate fact.

Establish `hF` using `GlobalTheory.ProperFinite.isFiniteQC_pushforward ρ hL (twist H (lbPow L n))`. Use `⟨hF, chi_eq_of_linearEquiv k fun p => ?_⟩` and prove the remaining obligations. Conclude with `(GlobalTheory.ProperFinite.nonempty_coh_pushforward_equiv k ρ hπ _ hc hD' hn p).some`.
-/
theorem eventually_chi_pushforward {Y : Scheme.{0}} [Algebra k Γ(Y, ⊤)] (hX : IsProjOver (strHom k X))
    (hY : IsProjOver (strHom k Y)) (ρ : Y ⟶ X) (hρ : ρ ≫ strHom k X = strHom k Y) {L : LB Y}
    (hL : IsAmpleLB L) (H : Y.Modules) (hH : QCoh.IsFiniteQC H) :
    ∀ᶠ n in atTop, QCoh.IsFiniteQC ((Scheme.Modules.pushforward ρ).obj (twist H (lbPow L n))) ∧
      chi k ((Scheme.Modules.pushforward ρ).obj (twist H (lbPow L n))) = chi k (twist H (lbPow L n)) := by
  have hPT := (isProper_and_exists_isAmpleLB_of_isProjOver hX).1
  have hPT' := (isProper_and_exists_isAmpleLB_of_isProjOver hY).1
  have : IsProper (ρ ≫ strHom k X) := hρ ▸ hPT'
  have : IsProper ρ := .of_comp ρ (strHom k X)
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (strHom k X)
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (strHom k X)
  have := isAffineHom_diagonal_of_isSeparated (strHom k X)
  have hπ : ∀ r : k, ρ.appTop (algebraMap k Γ(X, ⊤) r) = algebraMap k Γ(Y, ⊤) r := fun r => by
    rw [algebraMap_eq_strHom k X, algebraMap_eq_strHom k Y, ← hρ, Scheme.Hom.comp_appTop]
    rfl
  obtain ⟨m, D, hD, hc⟩ := exists_fin_affine_cover (X := X) (V := ⊤) isCompact_univ
  have hD' := isAffineOpen_finset_biInf hD
  have hV : ∀ᶠ n : ℕ in atTop, ∀ I : Finset (Fin m), I.Nonempty → ∀ q, 0 < q →
      Subsingleton (cohOn (twist H (lbPow L n)) (ρ ⁻¹ᵁ (⨅ i ∈ I, D i)) q) :=
    eventually_all.2 fun I => eventually_all.2 fun hI =>
      GlobalTheory.ProperFinite.eventually_subsingleton_cohOn ρ hL H (hD' I hI)
  filter_upwards [hV] with n hn
  have := GlobalTheory.Twist.isFiniteQC_twist (F := H) (isLB_lbPow hL.isLB n)
  have hF := GlobalTheory.ProperFinite.isFiniteQC_pushforward ρ hL (twist H (lbPow L n))
  refine ⟨hF, chi_eq_of_linearEquiv k fun p => ?_⟩
  exact (GlobalTheory.ProperFinite.nonempty_coh_pushforward_equiv k ρ hπ _ hc hD' hn p).some

omit [Field k] [Algebra k Γ(X, ⊤)] in

def projIso {Y : Scheme.{0}} (ρ : Y ⟶ X) (W : X.Modules) (M : LB Y) :
    (Scheme.Modules.pushforward ρ).obj (twist (dual ((Scheme.Modules.pullback ρ).obj W)) M) ≅
      homMod W ((Scheme.Modules.pushforward ρ).obj (twist (structureModule Y) M)) :=
  (Scheme.Modules.pushforward ρ).mapIso
      (TwistHomMod.iso ((Scheme.Modules.pullback ρ).obj W) (structureModule Y) M) ≪≫
    HomPull.pushHomIso ρ W (twist (structureModule Y) M)

/- English proof (translation)
Use `chi_shortExact (k := k) (Twist.shortExact_map hM hS) h₁ h₃` as an intermediate fact. Conclude with `this`.
-/
theorem chi_twist_shortExact_mk {F G H : X.Modules} {f : F ⟶ G} {g : G ⟶ H} {w : f ≫ g = 0}
    (hS : (ShortComplex.mk f g w).ShortExact) {M : LB X} (hM : M.IsLB)
    (h₁ : FiniteCoh k (twist F M)) (h₃ : FiniteCoh k (twist H M)) :
    chi k (twist G M) = chi k (twist F M) + chi k (twist H M) := by
  have := chi_shortExact (k := k) (Twist.shortExact_map hM hS) h₁ h₃
  exact this

/- English proof (translation)
Establish `hfc : ∀ {G : X.Modules} {s : ℕ}, IsVB G s → FiniteCoh k (twist G M)` using `fun {G s} h =>`. Use `(h.twist hM).isFiniteQC` as an intermediate fact. Use `finiteCoh_of_isProjOver (algebraMap_eq_strHom k X) _ hp`. Establish `e₁` using `chi_twist_shortExact_mk (k := k) (f := S.f) (g := S.g) (w := S.zero) hS hM (hfc h₁) (hfc h₃)`. Establish `e₂` using `chi_twist_shortExact_mk (k := k) (DualExact.shortExact_dual X S 1 hS h₃) hM (hfc h₃.dual) (hfc h₁.dual)`.

Establish `e₃` using `chi_twist_line hp hd h₃ hM`. Rewrite using `[defect_twist h₂, defect_twist h₁, e₁, e₂]`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem defect_extension (hp : IsProjOver (strHom k X)) (hd : topologicalKrullDim X ≤ 1)
    (S : ShortComplex X.Modules) (hS : S.ShortExact) {r : ℕ} (h₁ : IsVB S.X₁ r)
    (h₂ : IsVB S.X₂ (r + 1)) (h₃ : IsVB S.X₃ 1) {M : LB X} (hM : M.IsLB) :
    defect k S.X₂ (r + 1) (twist (structureModule X) M) =
      defect k S.X₁ r (twist (structureModule X) M) := by
  have hfc : ∀ {G : X.Modules} {s : ℕ}, IsVB G s → FiniteCoh k (twist G M) := fun {G s} h =>
    have := (h.twist hM).isFiniteQC
    finiteCoh_of_isProjOver (algebraMap_eq_strHom k X) _ hp
  have e₁ := chi_twist_shortExact_mk (k := k) (f := S.f) (g := S.g) (w := S.zero) hS hM (hfc h₁)
    (hfc h₃)
  have e₂ := chi_twist_shortExact_mk (k := k) (DualExact.shortExact_dual X S 1 hS h₃) hM
    (hfc h₃.dual) (hfc h₁.dual)
  have e₃ := chi_twist_line hp hd h₃ hM
  rw [defect_twist h₂, defect_twist h₁, e₁, e₂]
  push_cast
  linarith

end General

variable (k : Type) [Field k]

def Holds (r : ℕ) : Prop :=
  ∀ (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k X) → ∀ E : X.Modules, IsVB E r →
    ∀ F : X.Modules, QCoh.IsFiniteQC F → QCoh.suppDim F ≤ 1 → defect k E r F = 0

variable {k}

/- English proof (translation)
Take `⟨L, φ, hL, hφ⟩` from `exists_hom_line hp hE`. Use `hE.isFiniteQC` as an intermediate fact. Use `hL.isFiniteQC` as an intermediate fact. Take `⟨Y, _, _, ρ, hY, hdim, hc, hrk, hC⟩` from `exists_model hp (QCoh.annihilatorSheaf (cokernel φ)) fun h => VB.genericPoint_notMem_support_cokernel_of_ne_zero X E L φ hL hφ ((QCoh.coe_support_annihilatorSheaf _).le h)`. Establish `hdY : topologicalKrullDim Y ≤ 1` using `hdim ▸ hd`.

Take `⟨hsub, hK⟩` from `VB.isSubbundle_kernel_of_locally_principal Y _ _ ((Scheme.Modules.pullback ρ).map φ) r (hE.pullback ρ) (hL.pullback ρ) (VB.exists_image_principal_of_effCartier X Y ρ E L φ _ hE hL hC)`. Set `S : ShortComplex Y.Modules` to `ShortComplex.mk _ _ (cokernel.condition (kernel.ι ((Scheme.Modules.pullback ρ).map φ)))`. Establish `hS : S.ShortExact` using `{ exact := ShortComplex.exact_cokernel _ }`. Take `⟨s, h₃⟩` from `hsub.isVB_cokernel`. Establish `h₁ : IsVB S.X₁ r` using `hK`.

Establish `h₂ : IsVB S.X₂ (r + 1)` using `hE.pullback ρ`. Establish `h₃' : IsVB S.X₃ s` using `h₃`. Establish `hs : s = 1`. Use `h₂.isFiniteQC` as an intermediate fact. Establish `g` using `genRank_shortExact hS`.

Rewrite `g` using `[h₁.genRank_eq, h₂.genRank_eq, h₃'.genRank_eq]`. Use linear arithmetic over natural numbers and integers. Substitute `hs` using the available equality. Take `⟨A, hA⟩` from `(isProper_and_exists_isAmpleLB_of_isProjOver hY).2`. Establish `hE'` using `hE.pullback ρ`.

Establish `hD'` using `hE.dual.pullback ρ`. Take `⟨n, ⟨f₀, c₀⟩, ⟨-, c₁⟩, -, c₂⟩` from `((eventually_chi_pushforward hp hY ρ hc hA _ (isVB_structureModule Y).isFiniteQC).and ((eventually_chi_pushforward hp hY ρ hc hA _ hE'.dual.isFiniteQC).and (eventually_chi_pushforward hp hY ρ hc hA _ hD'.dual.isFiniteQC))).exists`. Establish `hM` using `isLB_lbPow hA.isLB n`. Establish `hO` using `(isVB_structureModule Y).twist hM`. Use `⟨_, f₀, (hrk _).trans hO.genRank_eq, ?_⟩` and prove the remaining obligations.

Establish `e` using `(defect_extension hY hdY S hS h₁ h₂ h₃' hM).trans (ih Y hY _ h₁ _ hO.isFiniteQC ((QCoh.suppDim_le _).trans hdY))`. Establish `hθ : IsIso (DualPull.theta ρ E)` using `DualPull.isIso_theta ρ hE`. Establish `t : ∀ W : Y.Modules, chi k (twist (dual W) (lbPow A n)) = chi k (homMod W (twist (structureModule Y) (lbPow A n)))` using `fun W => chi_congr k (TwistHomMod.iso W (structureModule Y) (lbPow A n))`. Rewrite using `[defect, ← chi_congr k (projIso ρ (dual E) _), ← chi_congr k (projIso ρ E _), c₀, c₁, c₂, t, t, chi_congr k (ProjFml.homIsoLeft (@asIso _ _ _ _ (DualPull.theta ρ E) hθ) _)]`. Conclude with `e`.
-/
theorem exists_defect_eq_zero {r : ℕ} (ih : Holds k r) {X : Scheme.{0}} [Algebra k Γ(X, ⊤)]
    [IsIntegral X] (hp : IsProjOver (strHom k X)) (hd : topologicalKrullDim X ≤ 1) {E : X.Modules}
    (hE : IsVB E (r + 1)) :
    ∃ G : X.Modules, QCoh.IsFiniteQC G ∧ genRank G = 1 ∧ defect k E (r + 1) G = 0 := by
  obtain ⟨L, φ, hL, hφ⟩ := exists_hom_line hp hE
  have := hE.isFiniteQC
  have := hL.isFiniteQC
  obtain ⟨Y, _, _, ρ, hY, hdim, hc, hrk, hC⟩ := exists_model hp (QCoh.annihilatorSheaf (cokernel φ))
    fun h => VB.genericPoint_notMem_support_cokernel_of_ne_zero X E L φ hL hφ
      ((QCoh.coe_support_annihilatorSheaf _).le h)
  have hdY : topologicalKrullDim Y ≤ 1 := hdim ▸ hd
  obtain ⟨hsub, hK⟩ := VB.isSubbundle_kernel_of_locally_principal Y _ _
    ((Scheme.Modules.pullback ρ).map φ) r (hE.pullback ρ) (hL.pullback ρ)
    (VB.exists_image_principal_of_effCartier X Y ρ E L φ _ hE hL hC)
  let S : ShortComplex Y.Modules :=
    ShortComplex.mk _ _ (cokernel.condition (kernel.ι ((Scheme.Modules.pullback ρ).map φ)))
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel _ }
  obtain ⟨s, h₃⟩ := hsub.isVB_cokernel
  have h₁ : IsVB S.X₁ r := hK
  have h₂ : IsVB S.X₂ (r + 1) := hE.pullback ρ
  have h₃' : IsVB S.X₃ s := h₃
  have hs : s = 1 := by
    have := h₂.isFiniteQC
    have g := genRank_shortExact hS
    rw [h₁.genRank_eq, h₂.genRank_eq, h₃'.genRank_eq] at g
    omega
  subst hs
  obtain ⟨A, hA⟩ := (isProper_and_exists_isAmpleLB_of_isProjOver hY).2
  have hE' := hE.pullback ρ
  have hD' := hE.dual.pullback ρ
  obtain ⟨n, ⟨f₀, c₀⟩, ⟨-, c₁⟩, -, c₂⟩ :=
    ((eventually_chi_pushforward hp hY ρ hc hA _ (isVB_structureModule Y).isFiniteQC).and
      ((eventually_chi_pushforward hp hY ρ hc hA _ hE'.dual.isFiniteQC).and
        (eventually_chi_pushforward hp hY ρ hc hA _ hD'.dual.isFiniteQC))).exists
  have hM := isLB_lbPow hA.isLB n
  have hO := (isVB_structureModule Y).twist hM
  refine ⟨_, f₀, (hrk _).trans hO.genRank_eq, ?_⟩
  have e := (defect_extension hY hdY S hS h₁ h₂ h₃' hM).trans
    (ih Y hY _ h₁ _ hO.isFiniteQC ((QCoh.suppDim_le _).trans hdY))
  have hθ : IsIso (DualPull.theta ρ E) := DualPull.isIso_theta ρ hE
  have t : ∀ W : Y.Modules, chi k (twist (dual W) (lbPow A n)) =
      chi k (homMod W (twist (structureModule Y) (lbPow A n))) := fun W =>
    chi_congr k (TwistHomMod.iso W (structureModule Y) (lbPow A n))
  rw [defect, ← chi_congr k (projIso ρ (dual E) _), ← chi_congr k (projIso ρ E _), c₀, c₁, c₂, t, t,
    chi_congr k (ProjFml.homIsoLeft (@asIso _ _ _ _ (DualPull.theta ρ E) hθ) _)]
  exact e

/- English proof (translation)
Introduce `X _ hp E hE F hF`. Establish `: AlgebraicGeometry.IsNoetherian X` using `isNoetherian_of_isProjOver hp`. Take `⟨A, hA⟩` from `(isProper_and_exists_isAmpleLB_of_isProjOver hp).2`. Use `QCoh.devissage X (fun G => QCoh.IsFiniteQC G → QCoh.suppDim G ≤ 1 → defect k E (r + 1) G = 0) (fun G h _ _ => defect_of_isZero E _ h) (fun S hS h₁ h₃ p₁ p₃ h₂ h => ?_) ?_ F hF hF` and prove the remaining obligations. Rewrite `h` using `[QCoh.suppDim_eq_max_of_shortExact hS, max_le_iff]`.

Rewrite using `[defect_shortExact hp hE S hS h₁ h₂ h₃, p₁ h₁ h.1, p₃ h₃ h.2, add_zero]`. Introduce `Z hZ hsmall G hG _ hdim`. Use `haveI := isIntegral_red hZ`. Establish `hAV : IsAmpleLB (A.pull (redι Z))` using `hA.pull_of_isClosedImmersion _`. Establish `hcoh : ∀ H : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme.Modules, QCoh.IsFiniteQC H → QCoh.IsFiniteQC ((Scheme.Modules.pushforward (redι Z)).obj H)` using `fun H _ => ProperFinite.isFiniteQC_pushforward (redι Z) hAV H`.

Establish `hsub` using `support_pushforward_subset_image_of_isClosedImmersion (redι Z)`. Establish `hsubZ` using `fun H => (hsub H).trans ((Set.image_subset_range _ _).trans (range_redι Z).le)`. Break down `(hsubZ G).eq_or_ssubset with he | hlt` into its components or cases. Use `swap`. Conclude with `hsmall _ (hcoh G hG) hlt (hcoh G hG) hdim`.

Establish `hdZ : topologicalKrullDim (Z : Set X) ≤ 1`. Rewrite using `[← he]`. Conclude with `hdim`. Use `letI := algebraΓAlong k (redι Z)`. Establish `hg` using `appTop_algebraMap_along k (redι Z)`.

Establish `hpZ : IsProjOver (strHom k (Scheme.IdealSheafData.vanishingIdeal Z).subscheme)`. Rewrite using `[← comp_strHom hg]`. Conclude with `ProjSpace.isProjOver_comp_of_isClosedImmersion _ hp`. Establish `hE'` using `hE.pullback (redι Z)`. Establish `key` using `defect_eq_genRank_mul hpZ hE' fun H hH h0 => by`.

Rewrite using `[← defect_pushforward (redι Z) hg hE]`. Use `hsmall _ (hcoh H hH) ⟨hsubZ H, fun hle => genRank_eq_zero_iff.1 h0 ?_⟩ (hcoh H hH) ((QCoh.topologicalKrullDim_mono (hsubZ H)).trans hdZ)` and prove the remaining obligations. Take `⟨y, hy, hyη⟩` from `hsub H (hle ((range_redι Z).le ⟨genericPoint _, rfl⟩))`. Rewrite `hy` using `[(redι Z).isClosedEmbedding.injective hyη]`. Then use the resulting hypothesis. Take `⟨G₀, hG₀, hr₀, h₀⟩` from `exists_defect_eq_zero ih hpZ ((topologicalKrullDim_red Z).trans_le hdZ) hE'`.

Establish `e` using `key 1 G₀ hG₀ hr₀`. Rewrite `e` using `[h₀, Nat.cast_one, one_mul]`. Rewrite using `[defect_pushforward (redι Z) hg hE, key _ G hG rfl, ← e, mul_zero]`.
-/
theorem Holds.succ {r : ℕ} (ih : Holds k r) : Holds k (r + 1) := by
  intro X _ hp E hE F hF
  have : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_isProjOver hp
  obtain ⟨A, hA⟩ := (isProper_and_exists_isAmpleLB_of_isProjOver hp).2
  refine QCoh.devissage X (fun G => QCoh.IsFiniteQC G → QCoh.suppDim G ≤ 1 → defect k E (r + 1) G = 0)
    (fun G h _ _ => defect_of_isZero E _ h) (fun S hS h₁ h₃ p₁ p₃ h₂ h => ?_) ?_ F hF hF
  · rw [QCoh.suppDim_eq_max_of_shortExact hS, max_le_iff] at h
    rw [defect_shortExact hp hE S hS h₁ h₂ h₃, p₁ h₁ h.1, p₃ h₃ h.2, add_zero]
  intro Z hZ hsmall G hG _ hdim
  haveI := isIntegral_red hZ
  have hAV : IsAmpleLB (A.pull (redι Z)) := hA.pull_of_isClosedImmersion _
  have hcoh : ∀ H : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme.Modules, QCoh.IsFiniteQC H →
      QCoh.IsFiniteQC ((Scheme.Modules.pushforward (redι Z)).obj H) := fun H _ =>
    ProperFinite.isFiniteQC_pushforward (redι Z) hAV H
  have hsub := support_pushforward_subset_image_of_isClosedImmersion (redι Z)
  have hsubZ := fun H => (hsub H).trans ((Set.image_subset_range _ _).trans (range_redι Z).le)
  rcases (hsubZ G).eq_or_ssubset with he | hlt
  swap
  · exact hsmall _ (hcoh G hG) hlt (hcoh G hG) hdim
  have hdZ : topologicalKrullDim (Z : Set X) ≤ 1 := by
    rw [← he]; exact hdim
  letI := algebraΓAlong k (redι Z)
  have hg := appTop_algebraMap_along k (redι Z)
  have hpZ : IsProjOver (strHom k (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) := by
    rw [← comp_strHom hg]
    exact ProjSpace.isProjOver_comp_of_isClosedImmersion _ hp
  have hE' := hE.pullback (redι Z)
  have key := defect_eq_genRank_mul hpZ hE' fun H hH h0 => by
    rw [← defect_pushforward (redι Z) hg hE]
    refine hsmall _ (hcoh H hH) ⟨hsubZ H, fun hle => genRank_eq_zero_iff.1 h0 ?_⟩
      (hcoh H hH) ((QCoh.topologicalKrullDim_mono (hsubZ H)).trans hdZ)
    obtain ⟨y, hy, hyη⟩ := hsub H (hle ((range_redι Z).le ⟨genericPoint _, rfl⟩))
    rwa [(redι Z).isClosedEmbedding.injective hyη] at hy
  obtain ⟨G₀, hG₀, hr₀, h₀⟩ :=
    exists_defect_eq_zero ih hpZ ((topologicalKrullDim_red Z).trans_le hdZ) hE'
  have e := key 1 G₀ hG₀ hr₀
  rw [h₀, Nat.cast_one, one_mul] at e
  rw [defect_pushforward (redι Z) hg hE, key _ G hG rfl, ← e, mul_zero]

variable (k) in

/- English proof (translation)
Proceed by induction on `r with`. Consider the case `zero => exact fun X _ _ E hE F _ _ => defect_rank_zero hE F`. Consider the case `succ r ih => exact ih.succ`.
-/
theorem intersectionNumber_baseChange (r : ℕ) : Holds k r := by
  induction r with
  | zero => exact fun X _ _ E hE F _ _ => defect_rank_zero hE F
  | succ r ih => exact ih.succ

/- English proof (translation)
Introduce `k _ T _ _ hT E r hE F hF h`. Use `sub_eq_zero.1 (intersectionNumber_baseChange k r T hT.isProjOver E hE F hF ?_)` and prove the remaining obligations. Use `topologicalKrullDim_add_one_le (QCoh.isClosed_support F) isClosed_univ fun x _ => ⟨genericPoint T, trivial, genRank_eq_zero_iff.1 h, genericPoint_specializes x⟩` as an intermediate fact. Establish `e : topologicalKrullDim (Set.univ : Set T) = 2`. Rewrite using `[← hT.dim_eq, ← QCoh.suppDim_structureModule, QCoh.suppDim, QCoh.support_structureModule]`.

Rewrite `this` using `[e]`. Conclude with `ENat.WithBot.add_le_add_one_right_iff.1 (this.trans_eq one_add_one_eq_two.symm)`.
-/
theorem chi_homMod_add_of_genRank_eq_zero : ∀ (k : Type) [Field k] (T : Scheme.{0}) [Algebra k Γ(T, ⊤)] [IsIntegral T], IsProjSurface k T → ∀ (E : T.Modules) (r : ℕ), IsVB E r → ∀ (F : T.Modules), QCoh.IsFiniteQC F → genRank F = 0 → chi k (homMod (dual E) F) + chi k (homMod E F) = 2 * (r : ℤ) * chi k F := by
  intro k _ T _ _ hT E r hE F hF h
  refine sub_eq_zero.1 (intersectionNumber_baseChange k r T hT.isProjOver E hE F hF ?_)
  have := topologicalKrullDim_add_one_le (QCoh.isClosed_support F) isClosed_univ
    fun x _ => ⟨genericPoint T, trivial, genRank_eq_zero_iff.1 h, genericPoint_specializes x⟩
  have e : topologicalKrullDim (Set.univ : Set T) = 2 := by
    rw [← hT.dim_eq, ← QCoh.suppDim_structureModule, QCoh.suppDim, QCoh.support_structureModule]
  rw [e] at this
  exact ENat.WithBot.add_le_add_one_right_iff.1 (this.trans_eq one_add_one_eq_two.symm)

end GlobalTheory.RRTorsion

end

/- English proof (translation)
The claim follows from `GlobalTheory.RRTorsion.chi_homMod_add_of_genRank_eq_zero`.
-/
theorem _root_.GlobalTheory.T.euler_char_dual_torsion_formula : ∀ (k : Type) [Field k] (T : Scheme.{0}) [Algebra k Γ(T, ⊤)] [IsIntegral T], IsProjSurface k T → ∀ (E : T.Modules) (r : ℕ), IsVB E r → ∀ (F : T.Modules), QCoh.IsFiniteQC F → genRank F = 0 → chi k (homMod (dual E) F) + chi k (homMod E F) = 2 * (r : ℤ) * chi k F :=
  GlobalTheory.RRTorsion.chi_homMod_add_of_genRank_eq_zero
