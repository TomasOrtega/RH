import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpOverFstComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SqZeroPointEqOfCotangentFormEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPhiSurjectiveOntoDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteProjectiveCotangentGlobalSectionsGroupSche
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCotangentFrameSmoothGroupScheme
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppLESecEpsZeroEpsFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointsInjectiveOpenNearZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointsSurjectiveOpenNearZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecPropertyOfTorsionBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotangentTorsionMapSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotangentTorsionKernelMultPPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotangentTorsionCompatRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentTorsionPointEvaluationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiePairingEqInvariantDifferentialStatement
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
open GlobalTheory.SqZeroPt
open scoped GlobalTheory.SqZeroPt
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.OpenOmega

/- English proof (translation)
Introduce `p _ R _ _ _ G _ _ hG GG θ hθ`. Use `haveI : Smooth G.hom := hG.smooth`. Use `haveI : IsSeparated G.hom := hG.separated`. Establish `hfr` using `GlobalTheory.ConormalFrame.exists_isFrame_omega R G`. Use `haveI hq : (GlobalTheory.LieVB.omega G).IsQuasicoherent := GlobalTheory.OmegaGlobal.isQuasicoherent_of_frames hfr`.

Take `⟨hfin, hproj⟩` from `GlobalTheory.FramesFGP.finite_projective_wmod R G hfr`. Establish `hinj` using `GlobalTheory.SqZeroPt.eq_of_Phi_eq R G hq`. Establish `hsurjR` using `GlobalTheory.SqZeroPt.exists_phi_eq R G hq`. Establish `hi` using `GlobalTheory.T.torsion_points_injective_open_near_zero p R G GG θ hθ`. Establish `hs` using `GlobalTheory.T.torsion_points_surjective_open_near_zero p R G GG θ hθ`.

Establish `hsp : ∀ n, SpecProp θ n (hs n)` using `fun n => GlobalTheory.T.spec_property_of_torsion_bijective p R G GG θ n (hs n) (hi n)`. Establish `hbij` using `GlobalTheory.OmegaGlobal.toOmega_bijective R G ⟨GlobalTheory.LieVB.tangent_injective R G, GlobalTheory.LieVB.TangentSurj.tangent_surjective R G⟩`. Set `e0 : Wmod G →ₗ[R] Pdiv.omega G` to `{ toFun := GlobalTheory.LieVB.toOmega G map_add' := map_add _ map_smul' := fun a w => GlobalTheory.LieVB.toOmega_smul a w }`. Set `e : Wmod G ≃ₗ[R] Pdiv.omega G` to `LinearEquiv.ofBijective e0 hbij`. Set `c : Pdiv.omega G →ₗ[R] GG.omega` to `{ toFun := fun ω => ⟨fun n => cnθ θ n (hs n) (e.symm ω), fun n => GlobalTheory.T.cotangent_torsion_compat_restriction p R G GG θ n (hs n) (hs (n + 1)) (hsp (n + 1)) _⟩ map_add' := fun a b => Subtype.ext (funext fun n => by simp) map_smul' := fun a b => Subtype.ext (funext fun n = …`.

Use `⟨c, fun n => ⟨?_, fun ω => ?_, fun x ω a ha => ?_⟩⟩` and prove the remaining obligations. Introduce `y`. Take `⟨w, hw⟩` from `GlobalTheory.T.cotangent_torsion_map_surjective p R G GG θ n (hs n) hinj (hsp n) y`. Conclude with `⟨e w, by simp [c, hw]⟩`. Express the relevant statement in the definitionally equal form `cnθ θ n (hs n) (e.symm ω) = 0 ↔ _`.

Prove the components needed by the constructor for the conclusion. Introduce `h0`. Establish `hm` using `GlobalTheory.T.cotangent_torsion_kernel_mult_p_pow p R G GG θ n (hs n) hfin hproj hsurjR (hsp n) _ h0`. Rewrite `hm` using `[Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]`. Take `⟨u, -, hu⟩` from `hm`.

Conclude with `⟨e u, by rw [← map_smul, hu, LinearEquiv.apply_symm_apply]⟩`. Introduce and unpack `⟨w', rfl⟩`. Rewrite using `[map_smul, map_smul]`. Conclude with `GG.pow_smul_cot n _`. Establish `hx : zeroSec R R ≫ x.1 = η[G]` using `Over.OverMorphism.ext (isTangent_lieG x)`.

Express the relevant statement in the definitionally equal form `(θ.pt n _ (tanTors p n x) a).snd = _`. Rewrite using `[GlobalTheory.T.tangent_torsion_point_evaluation p R G GG θ n (hs n) (hsp n) x hx (e.symm ω) a ha, GlobalTheory.T.lie_pairing_eq_invariant_differential R G x hx]`. Establish `: GlobalTheory.LieVB.toOmega G (e.symm ω) = ω` using `e.apply_symm_apply ω`. Rewrite using `[this]`.
-/
theorem GlobalTheory.OpenOmega.exists_isOmega_of_isOpenNearZero : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [IsDomain R] [CharZero R] (G : Over (Sp R)) [GrpObj G]
    [IsCommMonObj G], IsSemiAbelian G → ∀ (GG : PDivGroup p R) (θ : TorsionMap G GG), θ.IsOpenNearZero →
    ∃ c : Pdiv.omega G →ₗ[R] GG.omega, θ.IsOmega c := by
  intro p _ R _ _ _ G _ _ hG GG θ hθ
  haveI : Smooth G.hom := hG.smooth
  haveI : IsSeparated G.hom := hG.separated
  have hfr := GlobalTheory.ConormalFrame.exists_isFrame_omega R G
  haveI hq : (GlobalTheory.LieVB.omega G).IsQuasicoherent := GlobalTheory.OmegaGlobal.isQuasicoherent_of_frames hfr
  obtain ⟨hfin, hproj⟩ := GlobalTheory.FramesFGP.finite_projective_wmod R G hfr
  have hinj := GlobalTheory.SqZeroPt.eq_of_Phi_eq R G hq
  have hsurjR := GlobalTheory.SqZeroPt.exists_phi_eq R G hq
  have hi := GlobalTheory.T.torsion_points_injective_open_near_zero p R G GG θ hθ
  have hs := GlobalTheory.T.torsion_points_surjective_open_near_zero p R G GG θ hθ
  have hsp : ∀ n, SpecProp θ n (hs n) := fun n => GlobalTheory.T.spec_property_of_torsion_bijective p R G GG θ n (hs n) (hi n)
  have hbij := GlobalTheory.OmegaGlobal.toOmega_bijective R G
    ⟨GlobalTheory.LieVB.tangent_injective R G, GlobalTheory.LieVB.TangentSurj.tangent_surjective R G⟩
  let e0 : Wmod G →ₗ[R] Pdiv.omega G :=
    { toFun := GlobalTheory.LieVB.toOmega G
      map_add' := map_add _
      map_smul' := fun a w => GlobalTheory.LieVB.toOmega_smul a w }
  let e : Wmod G ≃ₗ[R] Pdiv.omega G := LinearEquiv.ofBijective e0 hbij
  let c : Pdiv.omega G →ₗ[R] GG.omega :=
    { toFun := fun ω => ⟨fun n => cnθ θ n (hs n) (e.symm ω),
        fun n => GlobalTheory.T.cotangent_torsion_compat_restriction p R G GG θ n (hs n) (hs (n + 1)) (hsp (n + 1)) _⟩
      map_add' := fun a b => Subtype.ext (funext fun n => by simp)
      map_smul' := fun a b => Subtype.ext (funext fun n => by simp) }
  refine ⟨c, fun n => ⟨?_, fun ω => ?_, fun x ω a ha => ?_⟩⟩
  · intro y
    obtain ⟨w, hw⟩ := GlobalTheory.T.cotangent_torsion_map_surjective p R G GG θ n (hs n) hinj (hsp n) y
    exact ⟨e w, by simp [c, hw]⟩
  · change cnθ θ n (hs n) (e.symm ω) = 0 ↔ _
    constructor
    · intro h0
      have hm := GlobalTheory.T.cotangent_torsion_kernel_mult_p_pow p R G GG θ n (hs n) hfin hproj hsurjR (hsp n) _ h0
      rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hm
      obtain ⟨u, -, hu⟩ := hm
      exact ⟨e u, by rw [← map_smul, hu, LinearEquiv.apply_symm_apply]⟩
    · rintro ⟨w', rfl⟩
      rw [map_smul, map_smul]
      exact GG.pow_smul_cot n _
  · have hx : zeroSec R R ≫ x.1 = η[G] := Over.OverMorphism.ext (isTangent_lieG x)
    change (θ.pt n _ (tanTors p n x) a).snd = _
    rw [GlobalTheory.T.tangent_torsion_point_evaluation p R G GG θ n (hs n) (hsp n) x hx (e.symm ω) a ha, GlobalTheory.T.lie_pairing_eq_invariant_differential R G x hx]
    have : GlobalTheory.LieVB.toOmega G (e.symm ω) = ω := e.apply_symm_apply ω
    rw [this]
