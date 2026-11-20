import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KerDatTuple
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVecMemHatSwap
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaKernelFiniteAdelicLaws
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKORatLeftAndEigenRight
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelVectorMovedByRootsOfUnityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseTupleThetaKernelTameCharacterStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilActionKernelEqBaseOnRealUnitaryPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealPointsActFockVectorsAnyDatumStatement

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound

namespace GlobalTheory.OneKernelSpan

/- English proof (translation)
Introduce `D G _ _ Pl0 T0 A Ks _ _ _ R F hR i Q h h' γ k hk e w hw`. Take `⟨gramR, c0R, c0L, hT, P, hP, rfl⟩` from `hw`. Use `⟨gramR, c0R, c0L, hT, ?_⟩` and prove the remaining obligations. Establish `hst : Formalism.UG.bc (swapAE D) (k : GL (Fin (Vc D i).rank) _) ∈ St (R.βV i)` using `Formalism.L2.DIV.parLev_St hk.1`. Take `⟨γE, hγ, hl⟩` from `GlobalTheory.HLatMove.hLat_rat_mul_stab (Vc D i) (R.βV i) (R.ΛV i) (hR.lev.βV i) γ`.

Rewrite `hP` using `[e, hl (fin (Vc D i) h') k hst, Formalism.L2.Col.nabAtr_gmap, MulEquiv.apply_symm_apply]`. Take `⟨P', hP', rfl⟩` from `hP`. Use `⟨P', hP', ?_⟩` and prove the remaining obligations. Establish `h1` using `(hT.mapL i).1 γ γE hγ P'`. Express the relevant statement in the definitionally equal form `(R.cV i).ρ ((γ : GA D (Vc D i))⁻¹) (c0L i ((rhoVr (labLL D) (lamV D i) γE) P')) = c0L i P'`.

Rewrite using `[h1]`. Express the relevant statement in the definitionally equal form `((R.cV i).ρ ((γ : GA D (Vc D i))⁻¹) * (R.cV i).ρ (γ : GA D (Vc D i))) (c0L i P') = c0L i P'`. Rewrite using `[← map_mul, inv_mul_cancel, map_one]`. Both sides reduce to the same expression.
-/
theorem inCoefLat_move : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (Q : Finset (Pl D.host.E)) (h h' : GA D (Vc D i)) (γ : GQ (Vc D i)) (k : Bridge.Gf (Vc D i)), k ∈ dataLevel R i Q → fin (Vc D i) h = Bridge.ratF (Vc D i) γ * fin (Vc D i) h' * k → ∀ w, InCoefLat R i h w → InCoefLat R i h' ((R.cV i).ρ ((γ : GA D (Vc D i))⁻¹) w) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i Q h h' γ k hk e w hw
  obtain ⟨gramR, c0R, c0L, hT, P, hP, rfl⟩ := hw
  refine ⟨gramR, c0R, c0L, hT, ?_⟩
  have hst : Formalism.UG.bc (swapAE D) (k : GL (Fin (Vc D i).rank) _) ∈ St (R.βV i) := Formalism.L2.DIV.parLev_St hk.1
  obtain ⟨γE, hγ, hl⟩ := GlobalTheory.HLatMove.hLat_rat_mul_stab (Vc D i) (R.βV i) (R.ΛV i) (hR.lev.βV i) γ
  rw [e, hl (fin (Vc D i) h') k hst, Formalism.L2.Col.nabAtr_gmap, MulEquiv.apply_symm_apply] at hP
  obtain ⟨P', hP', rfl⟩ := hP
  refine ⟨P', hP', ?_⟩
  have h1 := (hT.mapL i).1 γ γE hγ P'
  change (R.cV i).ρ ((γ : GA D (Vc D i))⁻¹) (c0L i ((rhoVr (labLL D) (lamV D i) γE) P')) = c0L i P'
  rw [h1]
  change ((R.cV i).ρ ((γ : GA D (Vc D i))⁻¹) * (R.cV i).ρ (γ : GA D (Vc D i))) (c0L i P') = c0L i P'
  rw [← map_mul, inv_mul_cancel, map_one]
  rfl

/- English proof (translation)
Establish `hθ : IsInfFam R.θ` using `hR.models.inf`. Establish `hφ : IsThetaFunO R.ψ (Vc D i) (Wc D i) φ`. Take `⟨⟨hψ, h0⟩, e, -, h⟩` from `hK.vec`. Conclude with `GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hψ hθ h h0.theta`. Conclude with `(GlobalTheory.OrientedHeis.om_pureTensorO D _ _ _ _ _ _ _ hK.weil hθ (fun _ => 1) (fun _ => 1) (R.BV i) _ (cart (R.MW i (sg0 D A))) (cart (R.MW i (sg0 D A))) (onb (R.MW i (sg0 D A))) _ 1 1 (fun τ => by rw [Matrix.mul_one, Matrix.one_mul]) (fun τ => by rw [GlobalTheory.JointHarm.c …`.
-/
theorem pt_theta_of_kerDat {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} (hR : GlobalTheory.Hk3.Core R F)
    {i : Fin D.R.m} {ξ : Formalism.L2.Host.HChar D.host.E} {χ : (AE D)ˣ →* Circle} {ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ}
    {Q : Finset (Pl D.host.E)} {ω : WeilRep D i} {φ : WO (Vc D i) (Wc D i) → ℂ} (hK : KerDat R i ξ χ ξR Q ω φ)
    (P : PolF D (Wc D i).rank (Vc D i).rank) :
    IsThetaFunO R.ψ (Vc D i) (Wc D i)
      (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A))) φ P) := by
  have hθ : IsInfFam R.θ := hR.models.inf
  have hφ : IsThetaFunO R.ψ (Vc D i) (Wc D i) φ := by
    obtain ⟨⟨hψ, h0⟩, e, -, h⟩ := hK.vec
    exact GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hψ hθ h h0.theta
  exact (GlobalTheory.OrientedHeis.om_pureTensorO D _ _ _ _ _ _ _ hK.weil hθ (fun _ => 1) (fun _ => 1) (R.BV i) _
      (cart (R.MW i (sg0 D A))) (cart (R.MW i (sg0 D A))) (onb (R.MW i (sg0 D A))) _ 1 1
      (fun τ => by rw [Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.JointHarm.compAt_mt_one', Matrix.mul_one, Matrix.one_mul]) (fun _ => rfl) (fun _ => rfl) _ hφ P).1

/- English proof (translation)
Introduce `D G _ _ Pl0 T0 A Ks _ _ _ R F hR i ξ χ ξR Q ω φ hK γ hγ h w`. Use function extensionality and compare the values at `v g`. Use `(GlobalTheory.thetaKO_rat_left_and_eigen_right _ _ _ _ _ _ hK.weil _ (pt_theta_of_kerDat hR hK (R.ioP i (PiTensorProduct.tprod ℂ v) w))).1 γ hγ 1 (one_mem _) h g` as an intermediate fact. Rewrite `this` using `[one_mul]`. Conclude with `this`.
-/
theorem series_rat : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (ξ : Formalism.L2.Host.HChar D.host.E) (χ : (AE D)ˣ →* Circle) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (ω : WeilRep D i) (φ : WO (Vc D i) (Wc D i) → ℂ), KerDat R i ξ χ ξR Q ω φ → ∀ γ ∈ GQ (Vc D i), ∀ h w, singleSeries R i ω φ (γ * h) w = singleSeries R i ω φ h w := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i ξ χ ξR Q ω φ hK γ hγ h w
  funext v g
  have := (GlobalTheory.thetaKO_rat_left_and_eigen_right _ _ _ _ _ _ hK.weil _ (pt_theta_of_kerDat hR hK (R.ioP i (PiTensorProduct.tprod ℂ v) w))).1 γ hγ 1 (one_mem _) h g
  rw [one_mul] at this
  exact this

/- English proof (translation)
Introduce `D G _ _ Pl0 T0 A Ks _ _ _ R F hR i ξ χ ξR Q ω φ hK hval κ hκ hk`. Take `⟨h1, -⟩` from `GlobalTheory.T.thetaKernel_vector_moved_by_rootsOfUnity D G Pl0 T0 A Ks R F hR i ξ χ ξR Q ω φ hK hval`. Take `⟨z, n, hn, hz, hzω⟩` from `h1 κ hκ hk`. Use `⟨z, ⟨n, hn, hz⟩, fun h w => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `v g`.

Establish `hom` using `GlobalTheory.FiniteFock.om_pureTensorO_of_finite _ _ _ _ _ _ _ hR.models.inf hK.weil _ _ _ _ _ (pt_theta_of_kerDat hR hK) κ hκ 1 (one_mem _) _ hzω (R.ioP i (PiTensorProduct.tprod ℂ v) w)`. Use `(GlobalTheory.thetaKO_rat_left_and_eigen_right _ _ _ _ _ _ hK.weil _ (pt_theta_of_kerDat hR hK (R.ioP i (PiTensorProduct.tprod ℂ v) w))).2 κ 1 _ hom h g` as an intermediate fact. Rewrite `this` using `[mul_one]`. Conclude with `this`.
-/
theorem series_level : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (ξ : Formalism.L2.Host.HChar D.host.E) (χ : (AE D)ˣ →* Circle) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (ω : WeilRep D i) (φ : WO (Vc D i) (Wc D i) → ℂ), KerDat R i ξ χ ξR Q ω φ → (∀ x, ((ξ.1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → ∀ κ ∈ GfC (Vc D i), fin (Vc D i) κ ∈ dataLevel R i Q → ∃ z : D.what₂.LL, (∃ n : ℕ, 0 < n ∧ z ^ n = 1) ∧ ∀ h w, singleSeries R i ω φ (h * κ) w = D.what₂.embLL z • singleSeries R i ω φ h w := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i ξ χ ξR Q ω φ hK hval κ hκ hk
  obtain ⟨h1, -⟩ := GlobalTheory.T.thetaKernel_vector_moved_by_rootsOfUnity D G Pl0 T0 A Ks R F hR i ξ χ ξR Q ω φ hK hval
  obtain ⟨z, n, hn, hz, hzω⟩ := h1 κ hκ hk
  refine ⟨z, ⟨n, hn, hz⟩, fun h w => ?_⟩
  funext v g
  have hom := GlobalTheory.FiniteFock.om_pureTensorO_of_finite _ _ _ _ _ _ _ hR.models.inf hK.weil _ _ _ _ _
    (pt_theta_of_kerDat hR hK) κ hκ 1 (one_mem _) _ hzω (R.ioP i (PiTensorProduct.tprod ℂ v) w)
  have := (GlobalTheory.thetaKO_rat_left_and_eigen_right _ _ _ _ _ _ hK.weil _ (pt_theta_of_kerDat hR hK (R.ioP i (PiTensorProduct.tprod ℂ v) w))).2 κ 1 _ hom h g
  rw [mul_one] at this
  exact this

/- English proof (translation)
Introduce `D G _ _ Pl0 T0 A Ks _ _ _ R F hR i ξ χ ξR Q ω φ hK h u hu w`. Use function extensionality and compare the values at `v g`. Unfold `singleSeries Datum.thetaKO`. Rewrite using `[show ((h * u, g) : GA D (Vc D i) × GA D (Wc D i)) = (h, g) * (u, 1) from Prod.ext rfl (mul_one g).symm, map_mul, Module.End.mul_apply, GlobalTheory.T.weilAction_kernel_eq_base_on_realUnitaryPoints D G Pl0 T0 A Ks R F hR i ξ χ ξR Q ω φ hK u hu _ (pt_theta_of_kerDat hR hK _), Glob …`.
-/
theorem series_real : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (ξ : Formalism.L2.Host.HChar D.host.E) (χ : (AE D)ˣ →* Circle) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (ω : WeilRep D i) (φ : WO (Vc D i) (Wc D i) → ℂ), KerDat R i ξ χ ξR Q ω φ → ∀ (h u : GA D (Vc D i)), u ∈ GinfC (Vc D i) → ∀ w, singleSeries R i ω φ (h * u) w = singleSeries R i ω φ h ((R.cV i).ρ u w) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i ξ χ ξR Q ω φ hK h u hu w
  funext v g
  unfold singleSeries Datum.thetaKO
  rw [show ((h * u, g) : GA D (Vc D i) × GA D (Wc D i)) = (h, g) * (u, 1) from Prod.ext rfl (mul_one g).symm,
    map_mul, Module.End.mul_apply, GlobalTheory.T.weilAction_kernel_eq_base_on_realUnitaryPoints D G Pl0 T0 A Ks R F hR i ξ χ ξR Q ω φ hK u hu _ (pt_theta_of_kerDat hR hK _),
    GlobalTheory.T.realPoints_act_fock_vectors_any_datum D G Pl0 T0 A Ks R F hR i ξR Q φ hK.vec u hu]

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Introduce `D G _ _ Pl0 T0 A Ks _ _ _ R F hR i v hv hmu hval U ψ ph ω φ hk Cl h hh`. Take `⟨χ, ξR, hK⟩` from `GlobalTheory.T.baseTuple_thetaKernel_tameCharacter D G Pl0 T0 A Ks R F hR i v hv hmu ω φ hk`. Use `le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono (Set.iUnion_subset fun c x hx => ?_))` and prove the remaining obligations. Introduce and unpack `x ⟨g, hg, w, hw, hx⟩`. Take `⟨c, ⟨γA, hγA⟩, k, e⟩` from `hh.2 (fin (Vc D i) g)`.

Take `⟨κ, hκ, hκe⟩` from `GlobalTheory.TraceIncl.KernLaws.exists_finite_lift (Vc D i) (k : Bridge.Gf (Vc D i))`. Take `⟨u, hu_def⟩ : ∃ u : GA D (Vc D i), u = κ⁻¹ * ((h c)⁻¹ * (γA⁻¹ * g))` from `⟨_, rfl⟩`. Establish `e1 : fin (Vc D i) g = fin (Vc D i) (γA * h c * κ)`. Use `e.trans ?_` and prove the remaining obligations. Rewrite using `[← GlobalTheory.TraceIncl.KernLaws.fin_mul, ← GlobalTheory.TraceIncl.KernLaws.fin_mul, hκe]`.

Both sides reduce to the same expression. Establish `e2 : finHom (Vc D i) g = finHom (Vc D i) (γA * h c * κ)` using `congrArg Subtype.val e1`. Establish `hu : u ∈ GinfC (Vc D i)`. Use `MonoidHom.mem_ker.2 ?_` and prove the remaining obligations. Rewrite using `[hu_def, map_mul, map_mul, map_mul, map_inv (finHom (Vc D i)) κ, map_inv (finHom (Vc D i)) (h c), map_inv (finHom (Vc D i)) γA, e2, map_mul, map_mul]`.

Simplify using `only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel]`. Establish `hg' : g = γA * (h c * κ) * u`. Rewrite using `[hu_def]`. Simplify using `only [mul_assoc, mul_inv_cancel_left]`. Take `⟨z, ⟨n, hn, hz⟩, hzl⟩` from `series_level D G Pl0 T0 A Ks R F hR i _ χ ξR _ ω φ hK hval κ hκ (by rw [hκe]; exact k.2)`.

Establish `hρ : (R.cV i).ρ u w = (R.cV i).ρ (γA⁻¹) w`. Establish `hc1` using `(hR.models.cV i).1`. Rewrite using `[hu_def, map_mul, Module.End.mul_apply, hc1 _ (inv_mem hκ), Module.End.one_apply, map_mul, Module.End.mul_apply, hc1 _ (inv_mem (hh.1 c)), Module.End.one_apply, map_mul, Module.End.mul_apply, hc1 _ hg, Module.End.one_apply]`. Establish `key : ∀ v', singleSeries R i ω φ g w v' = D.what₂.embLL z • singleSeries R i ω φ (h c) ((R.cV i).ρ (γA⁻¹) w) v'`. Introduce `v'`.

Establish `h1` using `series_real D G Pl0 T0 A Ks R F hR i _ χ ξR _ ω φ hK (γA * (h c * κ)) u hu w`. Rewrite `h1` using `[← hg']`. Establish `h2` using `series_rat D G Pl0 T0 A Ks R F hR i _ χ ξR _ ω φ hK γA hγA (h c * κ) ((R.cV i).ρ u w)`. Establish `h3` using `hzl (h c) ((R.cV i).ρ u w)`. Rewrite using `[h1, h2, h3, hρ]`.

Both sides reduce to the same expression. Establish `hz0 : z ≠ 0`. Introduce and unpack `rfl`. Rewrite `hz` using `[zero_pow hn.ne']`. Conclude with `zero_ne_one hz`.

Establish `hzI : IsIntegral ℤ z` using `IsIntegral.of_pow hn (by rw [hz]; exact isIntegral_one)`. Establish `hx'' : z⁻¹ • x ∈ seriesAt R i U ψ ph ω φ (h c)`. Use `⟨_, inCoefLat_move D G Pl0 T0 A Ks R F hR i _ g (h c) ⟨γA, hγA⟩ k k.2 e w hw, fun v' => ?_⟩` and prove the remaining obligations. Rewrite using `[adForm_smul]`. Express the relevant statement in the definitionally equal form `D.what₂.embLL z⁻¹ • adForm R i x (fun ρ => v' ρ) = _`.

Rewrite using `[hx v', key v', map_smul, smul_comm ph, smul_smul, ← map_mul, inv_mul_cancel₀ hz0, map_one, one_smul]`. Establish `: x = (⟨z, hzI⟩ : 𝓞 D.what₂.LL) • (z⁻¹ • x)`. Establish `e3 : (⟨z, hzI⟩ : 𝓞 D.what₂.LL) • (z⁻¹ • x) = z • (z⁻¹ • x)` using `rfl`. Rewrite using `[e3, smul_smul, mul_inv_cancel₀ hz0, one_smul]`. Rewrite using `[this]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_iUnion.2 ⟨c, hx''⟩))`. Take `⟨w, hw, hx⟩` from `hx`. Conclude with `⟨h c, hh.1 c, w, hw, hx⟩`.
-/
theorem kernelSpanOverClasses_of : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → ∀ (U : Subgroup G) (ψ : U →* D.what₂.LLˣ) (ph : ℂ), KernelSpanOverClasses R i U ψ ph v (ownAt D v) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i v hv hmu hval U ψ ph ω φ hk Cl h hh
  obtain ⟨χ, ξR, hK⟩ := GlobalTheory.T.baseTuple_thetaKernel_tameCharacter D G Pl0 T0 A Ks R F hR i v hv hmu ω φ hk
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono (Set.iUnion_subset fun c x hx => ?_))
  · rintro x ⟨g, hg, w, hw, hx⟩
    obtain ⟨c, ⟨γA, hγA⟩, k, e⟩ := hh.2 (fin (Vc D i) g)
    obtain ⟨κ, hκ, hκe⟩ := GlobalTheory.TraceIncl.KernLaws.exists_finite_lift (Vc D i) (k : Bridge.Gf (Vc D i))
    obtain ⟨u, hu_def⟩ : ∃ u : GA D (Vc D i), u = κ⁻¹ * ((h c)⁻¹ * (γA⁻¹ * g)) := ⟨_, rfl⟩
    have e1 : fin (Vc D i) g = fin (Vc D i) (γA * h c * κ) := by
      refine e.trans ?_
      rw [← GlobalTheory.TraceIncl.KernLaws.fin_mul, ← GlobalTheory.TraceIncl.KernLaws.fin_mul, hκe]
      rfl
    have e2 : finHom (Vc D i) g = finHom (Vc D i) (γA * h c * κ) := congrArg Subtype.val e1
    have hu : u ∈ GinfC (Vc D i) := by
      refine MonoidHom.mem_ker.2 ?_
      rw [hu_def, map_mul, map_mul, map_mul, map_inv (finHom (Vc D i)) κ, map_inv (finHom (Vc D i)) (h c),
        map_inv (finHom (Vc D i)) γA, e2, map_mul, map_mul]
      simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel]
    have hg' : g = γA * (h c * κ) * u := by
      rw [hu_def]
      simp only [mul_assoc, mul_inv_cancel_left]
    obtain ⟨z, ⟨n, hn, hz⟩, hzl⟩ := series_level D G Pl0 T0 A Ks R F hR i _ χ ξR _ ω φ hK hval κ hκ (by rw [hκe]; exact k.2)
    have hρ : (R.cV i).ρ u w = (R.cV i).ρ (γA⁻¹) w := by
      have hc1 := (hR.models.cV i).1
      rw [hu_def, map_mul, Module.End.mul_apply, hc1 _ (inv_mem hκ), Module.End.one_apply, map_mul, Module.End.mul_apply,
        hc1 _ (inv_mem (hh.1 c)), Module.End.one_apply, map_mul, Module.End.mul_apply, hc1 _ hg, Module.End.one_apply]
    have key : ∀ v', singleSeries R i ω φ g w v' =
        D.what₂.embLL z • singleSeries R i ω φ (h c) ((R.cV i).ρ (γA⁻¹) w) v' := by
      intro v'
      have h1 := series_real D G Pl0 T0 A Ks R F hR i _ χ ξR _ ω φ hK (γA * (h c * κ)) u hu w
      rw [← hg'] at h1
      have h2 := series_rat D G Pl0 T0 A Ks R F hR i _ χ ξR _ ω φ hK γA hγA (h c * κ) ((R.cV i).ρ u w)
      have h3 := hzl (h c) ((R.cV i).ρ u w)
      rw [h1, h2, h3, hρ]
      rfl
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow hn.ne'] at hz
      exact zero_ne_one hz
    have hzI : IsIntegral ℤ z := IsIntegral.of_pow hn (by rw [hz]; exact isIntegral_one)
    have hx'' : z⁻¹ • x ∈ seriesAt R i U ψ ph ω φ (h c) := by
      refine ⟨_, inCoefLat_move D G Pl0 T0 A Ks R F hR i _ g (h c) ⟨γA, hγA⟩ k k.2 e w hw, fun v' => ?_⟩
      rw [adForm_smul]
      change D.what₂.embLL z⁻¹ • adForm R i x (fun ρ => v' ρ) = _
      rw [hx v', key v', map_smul, smul_comm ph, smul_smul, ← map_mul, inv_mul_cancel₀ hz0, map_one, one_smul]
    have : x = (⟨z, hzI⟩ : 𝓞 D.what₂.LL) • (z⁻¹ • x) := by
      have e3 : (⟨z, hzI⟩ : 𝓞 D.what₂.LL) • (z⁻¹ • x) = z • (z⁻¹ • x) := rfl
      rw [e3, smul_smul, mul_inv_cancel₀ hz0, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_iUnion.2 ⟨c, hx''⟩))
  · obtain ⟨w, hw, hx⟩ := hx
    exact ⟨h c, hh.1 c, w, hw, hx⟩

end GlobalTheory.OneKernelSpan

end
