import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdlAlongComapEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleTwistNormalisedBlowupNoetherianDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryIntegralCompactificationsExistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCompactificationExistsBoundaryIdealStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeparationNormalizedBlowupUnitaryCompactificatioStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreNormalProjectiveAmpleCharZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormBl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefIntersectionNumberNonnegSubscheme
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

noncomputable section

namespace GlobalTheory.UPoincTop

/- English proof (translation)
Introduce `E _ _ _ H Dw hpq φ hφ hns l Xo c`. Take `⟨C⟩` from `GlobalTheory.T.unitary_integral_compactifications_exist E H Dw hpq l Xo c`. Take `⟨d, J₀, hd, hJ₀, hval₀⟩` from `GlobalTheory.T.unitaryCompactification_exists_boundary_ideal E H Dw hpq φ hφ l Xo c C`. Use `haveI := C.ded`. Use `haveI := C.iF_open`.

Establish `hgen` using `GlobalTheory.T.generic_fibre_normal_projective_ample_charZero C.o c.F C.b C.inj C.Z C.z C.OZ C.proj C.normal C.OZ_lb C.OZ_ample`. Take `⟨hprojZ, hnormZ, hOZlb, hOZamp⟩` from `hgen`. Set `Z` to `pullback C.z (spMap C.b)`. Set `fZ : Z ⟶ C.Z` to `pullback.fst C.z (spMap C.b)`. Set `J : Z.IdealSheafData` to `J₀.comap fZ`.

Set `W : Z.Opens` to `C.iF.opensRange`. Establish `hWset : (W : Set Z) = Set.range C.iF` using `by simp [W]`. Establish `hJ : ∀ x ∈ J.support, x ∉ Set.range C.iF`. Introduce `x hx hxr`. Rewrite `hx` using `[Scheme.IdealSheafData.support_comap]`.

Take `⟨y, rfl⟩` from `hxr`. Conclude with `hJ₀ _ hx ⟨y, rfl⟩`. Establish `hval : UValOn Xo c C.iF φ J d`. Introduce `W' _ _ _ hW ϖ hϖ χ y hy t tK htK hK P be hbe hmono`. Take `⟨n, hn, hid⟩` from `hval₀ W' hW ϖ hϖ (χ ≫ fZ) y (by rw [UCompact.i, ← Category.assoc, hy, Category.assoc]) t tK htK hK P be hbe hmono`.

Conclude with `⟨n, hn, by rw [GlobalTheory.PullAlong.idlAlong_comap_eq]; exact hid⟩`. Take `⟨S, π, BD, hbl, hpS, hprop, hBD, hiso, hdS⟩` from `GlobalTheory.NormBlowupField.exists_normBl c.F Z (pullback.snd C.z (spMap C.b)) hprojZ hnormZ J W (by rw [hWset]; exact C.iF_dense) (fun x hx hxW => hJ x hx (by have h : x ∈ (W : Set Z) := hxW; rwa [hWset] at h))`. Use `haveI := hiso`. Set `A : Xo.XF c ⟶ (π ⁻¹ᵁ W).toScheme` to `C.iF.isoOpensRange.hom ≫ inv (π ∣_ W)`. Set `j : Xo.XF c ⟶ S` to `A ≫ (π ⁻¹ᵁ W).ι`.

Establish `hjπ : j ≫ π = C.iF`. Simplify using `only [j, A, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc]`. Simplify using `[W]`. Establish `hrj : Set.range j = π ⁻¹' Set.range C.iF`. Establish `hA : Function.Surjective A` using `A.surjective`.

Express the relevant statement in the definitionally equal form `Set.range ((π ⁻¹ᵁ W).ι ∘ A) = _`. Rewrite using `[Set.range_comp, hA.range_eq, Set.image_univ, Scheme.Opens.range_ι, ← hWset]`. Both sides reduce to the same expression. Establish `hjo : IsOpenImmersion j` using `inferInstance`. Use `⟨Z, pullback.snd C.z (spMap C.b), C.iF, C.OZ.pull fZ, C.N, d, J, S, π, j, BD, ⟨⟨hprojZ, hnormZ, C.iF_open, C.iF_dense, C.iF_over, hOZlb, hOZamp⟩, ⟨C.N_pos, ?_⟩, ?_, ⟨hd, hJ, hval⟩, ⟨hbl, hpS, hjo, ?_, hjπ, hrj.symm, hBD, ?_⟩, ?_⟩, ?_⟩` and prove the remaining obligations.

Introduce `Y f hf hY`. Establish `h` using `C.omega Y f hf hY`. Conclude with `LBIso.trans (pull_isLB hOZlb f) (pull_isLB C.OZ_lb _) (LB.isLB_linComb hY _ _) (LBIso.symm (GlobalTheory.FibreNef.lbIso_pull_comp C.OZ_lb fZ f)) h`. Introduce `R _ _ _ hR t hP y hy σ hσ`. Take `⟨ξ₀, h₁, h₂⟩` from `C.ext R hR t hP y hy (σ ≫ spMap C.b) (by rw [← Category.assoc, hσ, Category.assoc])`.

Use `⟨pullback.lift ξ₀ σ (by rw [h₂]), ?_, pullback.lift_snd _ _ _⟩` and prove the remaining obligations. Apply `pullback.hom_ext` to reduce the goal to its premises. Simplify using `only [Category.assoc, pullback.lift_fst]`. Conclude with `h₁`. Simplify using `only [Category.assoc, pullback.lift_snd, C.iF_over]`.

Conclude with `hσ`. Rewrite using `[hrj, ← hWset]`. Conclude with `hdS`. Introduce `W' _ _ _ hW ϖ hϖ χ y hy t tK htK hK P be hbe hmono`. Take `⟨n, hn, hid⟩` from `hval W' hW ϖ hϖ (χ ≫ π) y (by rw [← Category.assoc, ← hy, Category.assoc, hjπ]) t tK htK hK P be hbe hmono`.

Conclude with `⟨n, hn, by rw [hBD, GlobalTheory.PullAlong.idlAlong_comap_eq]; exact hid⟩`. Take `⟨S₀, π₀, ν, U, hb, hνπ, hfin, -⟩` from `hbl.2`. Take `⟨T₀, hT⟩` from `GlobalTheory.BlowAmpleNoeth.ample_twist_of_blowup c.F Z S₀ S (pullback.snd C.z (spMap C.b)) J π₀ ν BD hprojZ hb hfin (by rw [hνπ]; exact hBD) (C.OZ.pull fZ) hOZamp`. Use `⟨T₀, fun k hk => ?_⟩` and prove the remaining obligations. Establish `h` using `hT k hk`.

Rewrite `h` using `[hνπ]`. Then use the resulting hypothesis. Conclude with `GlobalTheory.T.separation_normalizedBlowup_unitaryCompactification E H Dw hpq φ hφ hns l Xo c C d J₀ hd hJ₀ hval₀ S π j hbl hprop hjπ hjo hrj.symm`.
-/
theorem uPoinStX_sep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q →
    ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ →
    ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), ∃ (Z : Scheme.{0}) (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z)
      (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) (S : Scheme.{0}) (π : S ⟶ Z) (j : Xo.XF c ⟶ S)
      (BD : EffCartierData S), UPoinOnX Xo c φ zs i OZ N d J π j BD ∧ GlobalTheory.UChart.SepB Xo c φ j := by
  intro E _ _ _ H Dw hpq φ hφ hns l Xo c
  obtain ⟨C⟩ := GlobalTheory.T.unitary_integral_compactifications_exist E H Dw hpq l Xo c
  obtain ⟨d, J₀, hd, hJ₀, hval₀⟩ := GlobalTheory.T.unitaryCompactification_exists_boundary_ideal E H Dw hpq φ hφ l Xo c C
  haveI := C.ded
  haveI := C.iF_open
  have hgen := GlobalTheory.T.generic_fibre_normal_projective_ample_charZero C.o c.F C.b C.inj C.Z C.z C.OZ C.proj C.normal C.OZ_lb C.OZ_ample
  obtain ⟨hprojZ, hnormZ, hOZlb, hOZamp⟩ := hgen
  let Z := pullback C.z (spMap C.b)
  let fZ : Z ⟶ C.Z := pullback.fst C.z (spMap C.b)
  let J : Z.IdealSheafData := J₀.comap fZ
  let W : Z.Opens := C.iF.opensRange
  have hWset : (W : Set Z) = Set.range C.iF := by simp [W]
  have hJ : ∀ x ∈ J.support, x ∉ Set.range C.iF := by
    intro x hx hxr
    rw [Scheme.IdealSheafData.support_comap] at hx
    obtain ⟨y, rfl⟩ := hxr
    exact hJ₀ _ hx ⟨y, rfl⟩
  have hval : UValOn Xo c C.iF φ J d := by
    intro W' _ _ _ hW ϖ hϖ χ y hy t tK htK hK P be hbe hmono
    obtain ⟨n, hn, hid⟩ := hval₀ W' hW ϖ hϖ (χ ≫ fZ) y
      (by rw [UCompact.i, ← Category.assoc, hy, Category.assoc]) t tK htK hK P be hbe hmono
    exact ⟨n, hn, by rw [GlobalTheory.PullAlong.idlAlong_comap_eq]; exact hid⟩
  obtain ⟨S, π, BD, hbl, hpS, hprop, hBD, hiso, hdS⟩ :=
    GlobalTheory.NormBlowupField.exists_normBl c.F Z (pullback.snd C.z (spMap C.b)) hprojZ hnormZ J W (by rw [hWset]; exact C.iF_dense)
      (fun x hx hxW => hJ x hx (by have h : x ∈ (W : Set Z) := hxW; rwa [hWset] at h))
  haveI := hiso
  let A : Xo.XF c ⟶ (π ⁻¹ᵁ W).toScheme := C.iF.isoOpensRange.hom ≫ inv (π ∣_ W)
  let j : Xo.XF c ⟶ S := A ≫ (π ⁻¹ᵁ W).ι
  have hjπ : j ≫ π = C.iF := by
    simp only [j, A, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
    simp [W]
  have hrj : Set.range j = π ⁻¹' Set.range C.iF := by
    have hA : Function.Surjective A := A.surjective
    change Set.range ((π ⁻¹ᵁ W).ι ∘ A) = _
    rw [Set.range_comp, hA.range_eq, Set.image_univ, Scheme.Opens.range_ι, ← hWset]
    rfl
  have hjo : IsOpenImmersion j := inferInstance
  refine ⟨Z, pullback.snd C.z (spMap C.b), C.iF, C.OZ.pull fZ, C.N, d, J, S, π, j, BD, ⟨⟨hprojZ, hnormZ, C.iF_open,
    C.iF_dense, C.iF_over, hOZlb, hOZamp⟩, ⟨C.N_pos, ?_⟩, ?_, ⟨hd, hJ, hval⟩, ⟨hbl, hpS, hjo, ?_, hjπ, hrj.symm, hBD, ?_⟩, ?_⟩, ?_⟩
  · intro Y f hf hY
    have h := C.omega Y f hf hY
    exact LBIso.trans (pull_isLB hOZlb f) (pull_isLB C.OZ_lb _) (LB.isLB_linComb hY _ _)
      (LBIso.symm (GlobalTheory.FibreNef.lbIso_pull_comp C.OZ_lb fZ f)) h
  · intro R _ _ _ hR t hP y hy σ hσ
    obtain ⟨ξ₀, h₁, h₂⟩ := C.ext R hR t hP y hy (σ ≫ spMap C.b) (by rw [← Category.assoc, hσ, Category.assoc])
    refine ⟨pullback.lift ξ₀ σ (by rw [h₂]), ?_, pullback.lift_snd _ _ _⟩
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst]; exact h₁
    · simp only [Category.assoc, pullback.lift_snd, C.iF_over]; exact hσ
  · rw [hrj, ← hWset]; exact hdS
  · intro W' _ _ _ hW ϖ hϖ χ y hy t tK htK hK P be hbe hmono
    obtain ⟨n, hn, hid⟩ := hval W' hW ϖ hϖ (χ ≫ π) y (by rw [← Category.assoc, ← hy, Category.assoc, hjπ])
      t tK htK hK P be hbe hmono
    exact ⟨n, hn, by rw [hBD, GlobalTheory.PullAlong.idlAlong_comap_eq]; exact hid⟩
  · obtain ⟨S₀, π₀, ν, U, hb, hνπ, hfin, -⟩ := hbl.2
    obtain ⟨T₀, hT⟩ := GlobalTheory.BlowAmpleNoeth.ample_twist_of_blowup c.F Z S₀ S (pullback.snd C.z (spMap C.b)) J π₀ ν BD hprojZ hb hfin
      (by rw [hνπ]; exact hBD) (C.OZ.pull fZ) hOZamp
    refine ⟨T₀, fun k hk => ?_⟩
    have h := hT k hk
    rwa [hνπ] at h
  · exact GlobalTheory.T.separation_normalizedBlowup_unitaryCompactification E H Dw hpq φ hφ hns l Xo c C d J₀ hd hJ₀ hval₀ S π j hbl hprop hjπ hjo hrj.symm

/- English proof (translation)
The claim follows from `uPoinStX_sep`.
-/
theorem uStB : GlobalTheory.UChart.UStB := uPoinStX_sep

end GlobalTheory.UPoincTop
