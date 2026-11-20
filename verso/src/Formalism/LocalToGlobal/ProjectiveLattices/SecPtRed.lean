import Formalism.LocalToGlobal.ProjectiveLattices.NormalizedValuationMul
import Formalism.LocalToGlobal.ProjectiveLattices.SecPtOrd

noncomputable section

namespace Formalism.L2.Pj

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Gaps.EtaleWeightGaps NumberField IsDedekindDomain

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

section Ev

variable (Xr : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) {N : ℕ} {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL)
  {K2 : Type} [Field K2] (ev : Rp Xr la N →+* K2) (hu : IsUnit (ev (sec Xr la w 0)))

/- English proof (translation)
The claim follows from `IsLocalization.lift_eq _ r`.
-/
lemma liftEv_alg (r : Rp Xr la N) :
    IsLocalization.Away.lift (sec Xr la w 0) hu (algebraMap (Rp Xr la N) (Lw Xr la w) r) = ev r :=
  IsLocalization.lift_eq _ r

/- English proof (translation)
Use `congrArg (IsLocalization.Away.lift (sec Xr la w 0) hu) (section_mul_inverse_eq_one Xr la w)` as an intermediate fact. Rewrite `this` using `[map_mul, liftEv_alg, map_one]`. Conclude with `eq_inv_of_mul_eq_one_right this`.
-/
lemma liftEv_w0inv :
    IsLocalization.Away.lift (sec Xr la w 0) hu (w0inv Xr la w) = (ev (sec Xr la w 0))⁻¹ := by
  have := congrArg (IsLocalization.Away.lift (sec Xr la w 0) hu) (section_mul_inverse_eq_one Xr la w)
  rw [map_mul, liftEv_alg, map_one] at this
  exact eq_inv_of_mul_eq_one_right this

/- English proof (translation)
Rewrite using `[frac_apply, map_mul, map_pow, liftEv_alg, liftEv_w0inv]`.
-/
lemma liftEv_frac (k : ℕ) (g : Rp Xr la N) :
    IsLocalization.Away.lift (sec Xr la w 0) hu (frac Xr la w k g) = ev g * (ev (sec Xr la w 0))⁻¹ ^ k := by
  rw [frac_apply, map_mul, map_pow, liftEv_alg, liftEv_w0inv]

end Ev

section Std

variable {Xr : PJ D B P j} {la : HeightOneSpectrum (𝓞 B.KO)} {ka wL wF : WeightFamilies.Wt D j} {G : GlobalFamilyData Xr ka wL wF}

/- English proof (translation)
Establish `: Algebra.IsIntegral (Kp Xr la G.N) (OsK Xr la G.w)` using `Algebra.IsIntegral.of_finite _ _`. Conclude with `isUnif_of_field (Kp Xr la G.N) (Op.irreducible_map Xr la G.N (Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible (Xr.Ol la))))`.
-/
theorem isUnif_of_ring (hfd : FiniteDimensional (Kp Xr la G.N) (OsK Xr la G.w)) :
    IsUnif (OsK Xr la G.w) (unifO Xr la G.N) := by
  have : Algebra.IsIntegral (Kp Xr la G.N) (OsK Xr la G.w) := Algebra.IsIntegral.of_finite _ _
  exact isUnif_of_field (Kp Xr la G.N)
    (Op.irreducible_map Xr la G.N (Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible (Xr.Ol la))))

/- English proof (translation)
Use `Kl_charZero Xr la` as an intermediate fact. Conclude with `charZero_of_injective_algebraMap (algebraMap (Xr.Kl la) (Kp Xr la G.N)).injective`.
-/
theorem kp_charZero' : CharZero (Kp Xr la G.N) := by
  have := Kl_charZero Xr la
  exact charZero_of_injective_algebraMap (algebraMap (Xr.Kl la) (Kp Xr la G.N)).injective

/- English proof (translation)
Use `kp_charZero' (la := la) (G := G)` as an intermediate fact. Conclude with `(integralClosure_dvr' (Op Xr la G.N) (Kp Xr la G.N) (OsK Xr la G.w)).2 ζ`.
-/
theorem isDVRAt_of_ring (hfd : FiniteDimensional (Kp Xr la G.N) (OsK Xr la G.w)) (hred : IsReduced (OsK Xr la G.w))
    (ζ : PtsG G la) : IsDVRAt ζ := by
  have := kp_charZero' (la := la) (G := G)
  exact (integralClosure_dvr' (Op Xr la G.N) (Kp Xr la G.N) (OsK Xr la G.w)).2 ζ

/- English proof (translation)
Establish `hK` using `kp_charZero' (la := la) (G := G)`. Establish `hO : CharZero (Op Xr la G.N)` using `(RingHom.charZero_iff (IsFractionRing.injective (Op Xr la G.N) (Kp Xr la G.N))).2 hK`. Use `charZero_of_injective_algebraMap (R := Op Xr la G.N) ?_` and prove the remaining obligations. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `a ha`.

Assume the negation of the conclusion as `ha0`. Take `⟨n, u, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 h.irreducible`. Rewrite `ha` using `[map_mul, map_pow]`. Establish `hb : algebraMap (Op Xr la G.N) (Loc ζ) (unifO Xr la G.N) ≠ 0`. Rewrite using `[IsScalarTower.algebraMap_apply (Op Xr la G.N) ↥(As (Op Xr la G.N) (OsK Xr la G.w)) (Loc ζ)]`.

Introduce `h0`. Conclude with `vL_ne_top ζ (unif_mem_nonZeroDivisors h) ((vL_eq_top_iff ζ _).2 h0)`. Conclude with `(mul_ne_zero ((u.isUnit.map (algebraMap (Op Xr la G.N) (Loc ζ))).ne_zero) (pow_ne_zero n hb)) ha`.
-/
theorem loc_charZero (h : IsUnif (OsK Xr la G.w) (unifO Xr la G.N)) (ζ : PtsG G la) [IsDVRAt ζ] :
    CharZero (Loc ζ) := by
  have hK := kp_charZero' (la := la) (G := G)
  have hO : CharZero (Op Xr la G.N) :=
    (RingHom.charZero_iff (IsFractionRing.injective (Op Xr la G.N) (Kp Xr la G.N))).2 hK
  refine charZero_of_injective_algebraMap (R := Op Xr la G.N) ?_
  rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra ha0
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 h.irreducible
  rw [map_mul, map_pow] at ha
  have hb : algebraMap (Op Xr la G.N) (Loc ζ) (unifO Xr la G.N) ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply (Op Xr la G.N) ↥(As (Op Xr la G.N) (OsK Xr la G.w)) (Loc ζ)]
    intro h0
    exact vL_ne_top ζ (unif_mem_nonZeroDivisors h) ((vL_eq_top_iff ζ _).2 h0)
  exact (mul_ne_zero ((u.isUnit.map (algebraMap (Op Xr la G.N) (Loc ζ))).ne_zero) (pow_ne_zero n hb)) ha

end Std

variable {X : PJ D B P j} {E : PtExt X} {hM : IntAtExt X E}
  {ka wL wF : WeightFamilies.Wt D j} {G : GlobalFamilyData (xplus X E hM) ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)}

/- English proof (translation)
Take `⟨ϖ, hϖ, hιϖ⟩` from `hunr`. Distinguish the cases in `hr : r = 0`. Substitute `hr` using the available equality. Rewrite using `[map_zero, IsDiscreteValuationRing.addVal_zero, IsDiscreteValuationRing.addVal_zero]`. Take `⟨n, u, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr hϖ`.

Rewrite using `[IsDiscreteValuationRing.addVal_def' u hϖ n, map_mul, map_pow]`. Conclude with `IsDiscreteValuationRing.addVal_def' ((u.isUnit.map ι).unit) hιϖ n`.
-/
theorem addVal_map_of_unr {W V : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (ι : W →+* V) (hunr : ∃ ϖ : W, Irreducible ϖ ∧ Irreducible (ι ϖ)) (r : W) :
    IsDiscreteValuationRing.addVal V (ι r) = IsDiscreteValuationRing.addVal W r := by
  obtain ⟨ϖ, hϖ, hιϖ⟩ := hunr
  by_cases hr : r = 0
  · subst hr
    rw [map_zero, IsDiscreteValuationRing.addVal_zero, IsDiscreteValuationRing.addVal_zero]
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr hϖ
  rw [IsDiscreteValuationRing.addVal_def' u hϖ n, map_mul, map_pow]
  exact IsDiscreteValuationRing.addVal_def' ((u.isUnit.map ι).unit) hιϖ n

/- English proof (translation)
Establish `hι : AddValPres ζ ι` using `addVal_map_of_unr ι hunr`. Establish `honS : ∀ i : Fin (WeightFamilies.dimY D j), ev (sec (xplus X E hM) la G.w i.succ) = 0`. Introduce `i`. Establish `h1` using `hdeg (sfr (xplus X E hM) la G.w i.succ)`. Rewrite `h1` using `[(toOsK_eq_zero_iff _ _ _ _).2 (sfr_succ_mem_Jid _ _ _ i), map_zero, coe_sfr, liftEv_frac]`.

Conclude with `(mul_eq_zero.1 h1).resolve_right (pow_ne_zero _ (inv_ne_zero hu.ne_zero))`. Establish `hord : ∀ x : ↥(Frac0 (xplus X E hM) la G.w), toE (ord (unifO (xplus X E hM) la G.N) ζ (toOsK (xplus X E hM) la G.w x)) = nval T.V 1 (IsLocalization.Away.lift (sec (xplus X E hM) la G.w 0) hu (x : Lw (xplus X E hM) la G.w))`. Introduce `x`. Rewrite using `[hdeg x]`. Conclude with `toE_ord_eq T.Fr h hι _`.

Set `sp : SecPt ζ y` to `{ T := T, ep_pos := ep_pos ζ h, ev := ev, hv := hv, onS := honS, s0 := hu, ord := hord }`. Establish `hevW : ∀ (x : ↥(Frac0 (xplus X E hM) la G.w)) (a : ↥(As (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w))), toOsK (xplus X E hM) la G.w x = (a : OsK (xplus X E hM) la G.w) → IsLocalization.Away.lift (sec (xplus X E hM) la G.w 0) hu (x : Lw (xplus X E hM) la G.w) = algebraMa …`. Introduce `x a hxa`. Rewrite using `[hdeg x, hxa]`. Conclude with `phiAt_coe T.Fr h hι a`.

Conclude with `⟨{ toSecPt := sp ι := ι loc := hloc unr := hunr evW := hevW }⟩`.
-/
theorem fromW_of {ζ : PtsG G la} [IsDVRAt ζ] {y : E.Pt' la}
    (h : IsUnif (OsK (xplus X E hM) la G.w) (unifO (xplus X E hM) la G.N))
    (T : CDVR) (ι : Loc ζ →+* T.V) (hloc : IsLocalHom ι) (hunr : ∃ ϖ : Loc ζ, Irreducible ϖ ∧ Irreducible (ι ϖ))
    (ev : Rp (xplus X E hM) la G.N →+* T.Fr) (hu : IsUnit (ev (sec (xplus X E hM) la G.w 0)))
    (hv : ∀ (w : WeightFamilies.Wt D j) (F : B.Cusp j w), E.vAt' la y (X.inc w F) =
      nval T.V (ep (unifO (xplus X E hM) la G.N) ζ) (ev (emb (xplus X E hM) la G.N (X.inc w F))))
    (hdeg : ∀ x : ↥(Frac0 (xplus X E hM) la G.w),
      IsLocalization.Away.lift (sec (xplus X E hM) la G.w 0) hu (x : Lw (xplus X E hM) la G.w) =
        phiAt ζ T.Fr ι h (addVal_map_of_unr ι hunr) (toOsK (xplus X E hM) la G.w x)) :
    Nonempty (FromW ζ y) := by
  have hι : AddValPres ζ ι := addVal_map_of_unr ι hunr
  have honS : ∀ i : Fin (WeightFamilies.dimY D j), ev (sec (xplus X E hM) la G.w i.succ) = 0 := by
    intro i
    have h1 := hdeg (sfr (xplus X E hM) la G.w i.succ)
    rw [(toOsK_eq_zero_iff _ _ _ _).2 (sfr_succ_mem_Jid _ _ _ i), map_zero, coe_sfr, liftEv_frac] at h1
    exact (mul_eq_zero.1 h1).resolve_right (pow_ne_zero _ (inv_ne_zero hu.ne_zero))
  have hord : ∀ x : ↥(Frac0 (xplus X E hM) la G.w),
      toE (ord (unifO (xplus X E hM) la G.N) ζ (toOsK (xplus X E hM) la G.w x)) =
        nval T.V 1 (IsLocalization.Away.lift (sec (xplus X E hM) la G.w 0) hu (x : Lw (xplus X E hM) la G.w)) := by
    intro x
    rw [hdeg x]
    exact toE_ord_eq T.Fr h hι _
  let sp : SecPt ζ y :=
    { T := T, ep_pos := ep_pos ζ h, ev := ev, hv := hv, onS := honS, s0 := hu, ord := hord }
  have hevW : ∀ (x : ↥(Frac0 (xplus X E hM) la G.w))
      (a : ↥(As (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w))),
      toOsK (xplus X E hM) la G.w x = (a : OsK (xplus X E hM) la G.w) →
      IsLocalization.Away.lift (sec (xplus X E hM) la G.w 0) hu (x : Lw (xplus X E hM) la G.w) =
        algebraMap T.V T.Fr (ι (algebraMap _ (Loc ζ) a)) := by
    intro x a hxa
    rw [hdeg x, hxa]
    exact phiAt_coe T.Fr h hι a
  exact ⟨{ toSecPt := sp
           ι := ι
           loc := hloc
           unr := hunr
           evW := hevW }⟩

/- English proof (translation)
Introduce `ζ` and use `(hR ζ).imp fun _ ⟨f⟩ => ⟨f.toSecPt⟩`.
-/
theorem secPtSt_of
    (hR : ∀ ζ : PtsG G la, ∃ y : E.Pt' la, Nonempty (FromW ζ y)) :
    SecPtSt G la :=
  fun ζ => (hR ζ).imp fun _ ⟨f⟩ => ⟨f.toSecPt⟩

end Formalism.L2.Pj
