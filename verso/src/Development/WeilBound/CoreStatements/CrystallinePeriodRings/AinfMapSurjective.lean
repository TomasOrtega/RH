import Mathlib
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.FrobAinfMapFrobenius

noncomputable section

namespace PositivityTheory.LocInh

open GroundTheory.PAdicHodge Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
The claim follows from `galCp_coe (Per6.toBot g) x`.
-/
theorem actC_ext (g : GQ l) (x : Om l) : actC l g (x : ℂ_[l]) = ((g x : Om l) : ℂ_[l]) :=
  galCp_coe (Per6.toBot g) x

/- English proof (translation)
The claim follows from `norm_galCp (Per6.toBot g) y`.
-/
theorem actC_norm (g : GQ l) (y : ℂ_[l]) : ‖actC l g y‖ = ‖y‖ :=
  norm_galCp (Per6.toBot g) y

/- English proof (translation)
Use `⟨(Per6.intEquiv l).symm (integerMap (galCp (Per6.toBot g) : ℂ_[l] →+* ℂ_[l]) (AInf.norm_galCp_toRingHom (Per6.toBot g)) (Per6.intEquiv l y)), rfl, ?_⟩` and prove the remaining obligations. Establish `h1` using `frob_coeff_tiltMap x n y h`. Establish `h2 : PreTilt.coeff n (galT g x) = (Per6.modPEquiv l).symm (modPMap (galCp (Per6.toBot g) : ℂ_[l] →+* ℂ_[l]) (AInf.norm_galCp_toRingHom (Per6.toBot g)) (PreTilt.coeff n (Per6.tiltMap l x)))` using `rfl`. Rewrite using `[h2, h1, modPMap_mk]`. Both sides reduce to the same expression.
-/
theorem galT_coeff (g : GQ l) (x : OCb l) (n : ℕ) (y : OC l)
    (h : PreTilt.coeff n x = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) y) :
    ∃ y' : OC l, (y' : ℂ_[l]) = actC l g (y : ℂ_[l]) ∧
      PreTilt.coeff n (galT g x) = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) y' := by
  refine ⟨(Per6.intEquiv l).symm (integerMap (galCp (Per6.toBot g) : ℂ_[l] →+* ℂ_[l])
    (AInf.norm_galCp_toRingHom (Per6.toBot g)) (Per6.intEquiv l y)), rfl, ?_⟩
  have h1 := frob_coeff_tiltMap x n y h
  have h2 : PreTilt.coeff n (galT g x) = (Per6.modPEquiv l).symm
      (modPMap (galCp (Per6.toBot g) : ℂ_[l] →+* ℂ_[l]) (AInf.norm_galCp_toRingHom (Per6.toBot g))
        (PreTilt.coeff n (Per6.tiltMap l x))) := rfl
  rw [h2, h1, modPMap_mk]
  rfl

/- English proof (translation)
Use `Perfection.ext fun n => ?_` and prove the remaining obligations. Take `⟨y, hy⟩` from `Ideal.Quotient.mk_surjective (PreTilt.coeff n x)`. Take `⟨y₁, h₁, e₁⟩` from `galT_coeff g x n y hy.symm`. Take `⟨y₂, h₂, e₂⟩` from `h n y hy.symm`. Establish `: y₁ = y₂` using `Subtype.ext (h₁.trans h₂.symm)`.

Conclude with `e₁.trans (this ▸ e₂.symm)`.
-/
theorem galT_ext {g : GQ l} {x z : OCb l}
    (h : ∀ (n : ℕ) (y : OC l),
      PreTilt.coeff n x = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) y →
      ∃ y' : OC l, (y' : ℂ_[l]) = actC l g (y : ℂ_[l]) ∧
        PreTilt.coeff n z = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) y') :
    galT g x = z := by
  refine Perfection.ext fun n => ?_
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (PreTilt.coeff n x)
  obtain ⟨y₁, h₁, e₁⟩ := galT_coeff g x n y hy.symm
  obtain ⟨y₂, h₂, e₂⟩ := h n y hy.symm
  have : y₁ = y₂ := Subtype.ext (h₁.trans h₂.symm)
  exact e₁.trans (this ▸ e₂.symm)

/- English proof (translation)
The claim follows from `galT_ext fun _ y hy => ⟨y, by rw [map_one]; rfl, hy⟩`.
-/
theorem galT_one (x : OCb l) : galT (1 : GQ l) x = x :=
  galT_ext fun _ y hy => ⟨y, by rw [map_one]; rfl, hy⟩

/- English proof (translation)
The claim follows from `galT_ext fun n y hy => by obtain ⟨y₁, h₁, e₁⟩ := galT_coeff h x n y hy obtain ⟨y₂, h₂, e₂⟩ := galT_coeff g (galT h x) n y₁ e₁ exact ⟨y₂, by rw [h₂, h₁, map_mul]; rfl, e₂⟩`.
-/
theorem galT_mul (g h : GQ l) (x : OCb l) : galT (g * h) x = galT g (galT h x) :=
  galT_ext fun n y hy => by
    obtain ⟨y₁, h₁, e₁⟩ := galT_coeff h x n y hy
    obtain ⟨y₂, h₂, e₂⟩ := galT_coeff g (galT h x) n y₁ e₁
    exact ⟨y₂, by rw [h₂, h₁, map_mul]; rfl, e₂⟩

/- English proof (translation)
The claim follows from `Subtype.ext rfl`.
-/
theorem ζO_zero : ζO l 0 = 1 :=
  Subtype.ext rfl

/- English proof (translation)
Rewrite using `[ζO, ζO, ← map_pow, rootSeqInt_succ_pow]`.
-/
theorem ζO_succ (n : ℕ) : ζO l (n + 1) ^ l = ζO l n := by
  rw [ζO, ζO, ← map_pow, rootSeqInt_succ_pow]

/- English proof (translation)
Introduce `h` and use `rootSeq_one_ne_one (p := l) (congrArg Subtype.val h)`.
-/
theorem ζO_one : ζO l 1 ≠ 1 := fun h =>
  rootSeq_one_ne_one (p := l) (congrArg Subtype.val h)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem εO_coeff (n : ℕ) :
    PreTilt.coeff n (εO l) = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) (ζO l n) := rfl

/- English proof (translation)
Rewrite using `[frob_aB_apply, ιCD_cB, cD_apply, ACris.iota_algebraMap]`. Both sides reduce to the same expression.
-/
theorem ιCD_aB (a : Ainf l) :
    ιCD l (Per6.aB l a) = algebraMap (Per6.BdRp l) (Per6.BdR l) (Per6.aD l a) := by
  rw [frob_aB_apply, ιCD_cB, cD_apply, ACris.iota_algebraMap]
  rfl

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `w hw`. Take `⟨ξ, hξ, h1⟩` from `IsPerfectoidField.exists_mem_ker_fontaineTheta_isUnit_coeff_one ℂ_[l] l`. Establish `hker` using `IsPerfectoidField.ker_fontaineTheta_eq_span hξ h1`. Establish `hH` using `IsPerfectoidField.isHausdorff_span_of_isUnit_coeff_one hξ h1`.

Use `hH.haus w fun n => ?_` and prove the remaining obligations. Rewrite using `[SModEq.zero, smul_eq_mul, Ideal.mul_top, ← hker, ACris.ker_eq_span_xiGen, Ideal.span_singleton_pow, ← ACris.algebraMap_dvd_iff, map_pow, ← toBDeRhamPlus_mem_span_pow_iff ACris.ker_eq_span_xiGen]`. Establish `: toBDeRhamPlus ↥(normInteger ℂ_[l]) l (algebraMap _ _ w) = 0` using `hw`. Rewrite using `[this]`. Conclude with `Submodule.zero_mem _`.
-/
theorem wittTo_injective : Function.Injective (wittToBDeRhamPlus ↥(normInteger ℂ_[l]) l) := by
  rw [injective_iff_map_eq_zero]
  intro w hw
  obtain ⟨ξ, hξ, h1⟩ := IsPerfectoidField.exists_mem_ker_fontaineTheta_isUnit_coeff_one ℂ_[l] l
  have hker := IsPerfectoidField.ker_fontaineTheta_eq_span hξ h1
  have hH := IsPerfectoidField.isHausdorff_span_of_isUnit_coeff_one hξ h1
  refine hH.haus w fun n => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, ← hker, ACris.ker_eq_span_xiGen,
    Ideal.span_singleton_pow, ← ACris.algebraMap_dvd_iff, map_pow,
    ← toBDeRhamPlus_mem_span_pow_iff ACris.ker_eq_span_xiGen]
  have : toBDeRhamPlus ↥(normInteger ℂ_[l]) l (algebraMap _ _ w) = 0 := hw
  rw [this]
  exact Submodule.zero_mem _

/- English proof (translation)
The claim follows from `WittVector.map_injective _ (tiltEquiv l).injective`.
-/
theorem ainfMap_injective : Function.Injective (Per6.ainfMap l) :=
  WittVector.map_injective _ (tiltEquiv l).injective

/- English proof (translation)
The claim follows from `WittVector.map_surjective _ (tiltEquiv l).surjective`.
-/
theorem ainfMap_surjective : Function.Surjective (Per6.ainfMap l) :=
  WittVector.map_surjective _ (tiltEquiv l).surjective

/- English proof (translation)
Introduce `a b h`. Establish `h1` using `congrArg (ιCD l) h`. Rewrite `h1` using `[ιCD_aB, ιCD_aB]`. Conclude with `ainfMap_injective (wittTo_injective (IsPerfectoidField.algebraMap_bDeRham_injective (K := ℂ_[l]) (p := l) h1))`.
-/
theorem aB_injective : Function.Injective (Per6.aB l) := by
  intro a b h
  have h1 := congrArg (ιCD l) h
  rw [ιCD_aB, ιCD_aB] at h1
  exact ainfMap_injective (wittTo_injective
    (IsPerfectoidField.algebraMap_bDeRham_injective (K := ℂ_[l]) (p := l) h1))

/- English proof (translation)
Establish `h : Per6.ainfMap l (WittVector.map (galT g) a) = Per6.toBot g • Per6.ainfMap l a`. Use `WittVector.ext fun n => ?_` and prove the remaining obligations. Rewrite using `[AInf.gal_smul_coeff]`. Conclude with `tiltMap_tiltInv l _`. Rewrite using `[frob_aB_apply, frob_aB_apply, σB_cB, h, ← ACris.gal_smul_algebraMap, ACris.gal_smul_def]`.
-/
theorem aB_act (g : GQ l) (a : Ainf l) :
    Per6.aB l (WittVector.map (galT g) a) = Per6.σB g (Per6.aB l a) := by
  have h : Per6.ainfMap l (WittVector.map (galT g) a) = Per6.toBot g • Per6.ainfMap l a := by
    refine WittVector.ext fun n => ?_
    rw [AInf.gal_smul_coeff]
    exact tiltMap_tiltInv l _
  rw [frob_aB_apply, frob_aB_apply, σB_cB, h, ← ACris.gal_smul_algebraMap, ACris.gal_smul_def]

/- English proof (translation)
Rewrite using `[ιCD_aB]`. Conclude with `(IsPerfectoidField.mem_fil_zero_iff ℂ_[l] l).2 ⟨_, rfl⟩`.
-/
theorem ιCD_aB_mem_zero (a : Ainf l) : ιCD l (Per6.aB l a) ∈ Per6.FilD l 0 := by
  rw [ιCD_aB]
  exact (IsPerfectoidField.mem_fil_zero_iff ℂ_[l] l).2 ⟨_, rfl⟩

/- English proof (translation)
The claim follows from `tiltMap_tiltInv l _`.
-/
theorem tiltMap_εO : Per6.tiltMap l (εO l) = epsilon l := tiltMap_tiltInv l _

/- English proof (translation)
Rewrite using `[Per6.θD, ← IsPerfectoidField.maximalIdeal_bDeRhamPlus]`. Conclude with `IsPerfectoidField.algebraMap_mem_fil_iff b n`.
-/
theorem fil_nat (b : Per6.BdRp l) (n : ℕ) :
    algebraMap (Per6.BdRp l) (Per6.BdR l) b ∈ Per6.FilD l n ↔ b ∈ RingHom.ker (Per6.θD l) ^ n := by
  rw [Per6.θD, ← IsPerfectoidField.maximalIdeal_bDeRhamPlus]
  exact IsPerfectoidField.algebraMap_mem_fil_iff b n

/- English proof (translation)
The claim follows from `IsPerfectoidField.thetaBDeRhamPlusField_wittToBDeRhamPlus l _`.
-/
theorem θD_aD (a : Ainf l) : Per6.θD l (Per6.aD l a) =
    ((WittVector.fontaineTheta ↥(normInteger ℂ_[l]) l (Per6.ainfMap l a) : normInteger ℂ_[l]) : ℂ_[l]) :=
  IsPerfectoidField.thetaBDeRhamPlusField_wittToBDeRhamPlus l _

/- English proof (translation)
Establish `hξ : Per6.ainfMap l (∑ i ∈ Finset.range l, (WittVector.teichmuller l ((frobeniusEquiv (OCb l) l).symm (εO l))) ^ i) = AInf.xi (K` using `ℂ_[l]) (epsilon l) := by`. Establish `e : Per6.tiltMap l ((frobeniusEquiv (OCb l) l).symm (εO l)) = (frobeniusEquiv (PreTilt ↥(normInteger ℂ_[l]) l) l).symm (epsilon l)`. Apply `(frobeniusEquiv (PreTilt ↥(normInteger ℂ_[l]) l) l).injective` to reduce the goal to its premises. Rewrite using `[RingEquiv.apply_symm_apply, frobeniusEquiv_apply, frobenius_def, ← map_pow, frobeniusEquiv_symm_pow_p, tiltMap_εO]`. Rewrite using `[map_sum, AInf.xi]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_pow, frob_ainfMap_teich, e]`. Establish `h1 : ιCD l (Per6.aB l a) ∈ Per6.FilD l 1 ↔ Per6.ainfMap l a ∈ Ideal.span {AInf.xi (K` using `ℂ_[l]) (epsilon l)} := by`. Rewrite using `[ιCD_aB, ← AInf.ker_fontaineTheta_eq_span_xi untilt_epsilon untilt_frobeniusEquiv_symm_epsilon_ne_one, RingHom.mem_ker]`. Use `(fil_nat (Per6.aD l a) 1).trans ?_` and prove the remaining obligations.

Rewrite using `[pow_one, RingHom.mem_ker, θD_aD]`. Conclude with `⟨fun h => Subtype.ext h, fun h => by rw [h]; rfl⟩`. Rewrite using `[h1, Ideal.mem_span_singleton, ← hξ]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, hc⟩`.

Take `⟨b, rfl⟩` from `ainfMap_surjective c`. Conclude with `⟨b, ainfMap_injective (hc.trans (map_mul _ _ _).symm)⟩`. Introduce and unpack `⟨b, rfl⟩`. Conclude with `⟨Per6.ainfMap l b, map_mul _ _ _⟩`.
-/
theorem ιCD_aB_mem_one (a : Ainf l) : ιCD l (Per6.aB l a) ∈ Per6.FilD l 1 ↔
    ∃ b : Ainf l, a = (∑ i ∈ Finset.range l,
      (WittVector.teichmuller l ((frobeniusEquiv (OCb l) l).symm (εO l))) ^ i) * b := by
  have hξ : Per6.ainfMap l (∑ i ∈ Finset.range l,
      (WittVector.teichmuller l ((frobeniusEquiv (OCb l) l).symm (εO l))) ^ i) =
      AInf.xi (K := ℂ_[l]) (epsilon l) := by
    have e : Per6.tiltMap l ((frobeniusEquiv (OCb l) l).symm (εO l)) =
        (frobeniusEquiv (PreTilt ↥(normInteger ℂ_[l]) l) l).symm (epsilon l) := by
      apply (frobeniusEquiv (PreTilt ↥(normInteger ℂ_[l]) l) l).injective
      rw [RingEquiv.apply_symm_apply, frobeniusEquiv_apply, frobenius_def, ← map_pow,
        frobeniusEquiv_symm_pow_p, tiltMap_εO]
    rw [map_sum, AInf.xi]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_pow, frob_ainfMap_teich, e]
  have h1 : ιCD l (Per6.aB l a) ∈ Per6.FilD l 1 ↔
      Per6.ainfMap l a ∈ Ideal.span {AInf.xi (K := ℂ_[l]) (epsilon l)} := by
    rw [ιCD_aB, ← AInf.ker_fontaineTheta_eq_span_xi untilt_epsilon
      untilt_frobeniusEquiv_symm_epsilon_ne_one, RingHom.mem_ker]
    refine (fil_nat (Per6.aD l a) 1).trans ?_
    rw [pow_one, RingHom.mem_ker, θD_aD]
    exact ⟨fun h => Subtype.ext h, fun h => by rw [h]; rfl⟩
  rw [h1, Ideal.mem_span_singleton, ← hξ]
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨b, rfl⟩ := ainfMap_surjective c
    exact ⟨b, ainfMap_injective (hc.trans (map_mul _ _ _).symm)⟩
  · rintro ⟨b, rfl⟩
    exact ⟨Per6.ainfMap l b, map_mul _ _ _⟩

/- English proof (translation)
Use extensionality with `n`. Simplify using `only [Per6.ainfMap, Per6.zA, IsPerfectoidField.padicIntToWitt, RingHom.comp_apply, WittVector.map_coeff]`. Conclude with `(RingHom.congr_fun (RingHom.ext_zmod ((Per6.tiltMap l).comp (ZMod.castHom (dvd_refl l) _)) (ZMod.castHom (dvd_refl l) _)) _)`.
-/
theorem ainf_zA (z : ℤ_[l]) :
    Per6.ainfMap l (Per6.zA l z) = IsPerfectoidField.padicIntToWitt l z := by
  ext n
  simp only [Per6.ainfMap, Per6.zA, IsPerfectoidField.padicIntToWitt, RingHom.comp_apply,
    WittVector.map_coeff]
  exact (RingHom.congr_fun (RingHom.ext_zmod ((Per6.tiltMap l).comp (ZMod.castHom (dvd_refl l) _))
    (ZMod.castHom (dvd_refl l) _)) _)

/- English proof (translation)
Rewrite using `[frob_qB_coe, Per6.zB, RingHom.comp_apply, frob_aB_apply, ainf_zA]`.
-/
theorem qB_coe (z : ℤ_[l]) : qB l (z : ℚ_[l]) = Per6.zB l z := by
  rw [frob_qB_coe, Per6.zB, RingHom.comp_apply, frob_aB_apply, ainf_zA]

/- English proof (translation)
Rewrite using `[← ιCD_qB, qB_coe, Per6.zB, RingHom.comp_apply, ιCD_aB]`. Both sides reduce to the same expression.
-/
theorem oD_coe (z : ℤ_[l]) : oD l (algebraMap ℚ_[l] (Om l) (z : ℚ_[l])) = Per6.zD l z := by
  rw [← ιCD_qB, qB_coe, Per6.zB, RingHom.comp_apply, ιCD_aB]
  rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨algClToBdR l x, rfl, thetaAlgHom_algClToBdR l x⟩`.
-/
theorem oD_lift (x : Om l) : ∃ y : Per6.BdRp l,
    oD l x = algebraMap (Per6.BdRp l) (Per6.BdR l) y ∧ Per6.θD l y = (x : ℂ_[l]) :=
  ⟨algClToBdR l x, rfl, thetaAlgHom_algClToBdR l x⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `bcris_hom_ext fun x => (h x).trans ((ιCD_cB x).trans (cD_apply x)).symm`. Introduce and unpack `rfl x`. Conclude with `(ιCD_cB x).trans (cD_apply x)`.
-/
theorem isCrisDR_iff (f : Per6.Bcris l →+* Per6.BdR l) : Per6.IsCrisDR l f ↔ f = ιCD l := by
  constructor
  · intro h
    exact bcris_hom_ext fun x => (h x).trans ((ιCD_cB x).trans (cD_apply x)).symm
  · rintro rfl x
    exact (ιCD_cB x).trans (cD_apply x)

/- English proof (translation)
Establish `e : Per6.aD l (WittVector.teichmuller l ε) - 1 = muBdR l (Per6.tiltMap l ε)`. Rewrite using `[muBdR_eq, ← frob_ainfMap_teich]`. Both sides reduce to the same expression. Establish `hm : RingHom.ker (Per6.θD l) = IsLocalRing.maximalIdeal (Per6.BdRp l)` using `(IsPerfectoidField.maximalIdeal_bDeRhamPlus (K := ℂ_[l]) (p := l)).symm`. Unfold `Per6.IsLog`.

Rewrite using `[e]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h1` using `h 1`. Establish `h2` using `h 2`.

Simplify using `only [Finset.Ico_self, Finset.sum_empty, sub_zero, pow_one] at h1`. Establish `h3 : y - muBdR l (Per6.tiltMap l ε) ∈ RingHom.ker (Per6.θD l)`. Establish `h4` using `Ideal.pow_le_self two_ne_zero h2`. Simplify using `using h4`. Establish `h5 : Per6.θD l (muBdR l (Per6.tiltMap l ε)) = 0`.

Rewrite `h1`, `h3` using `[RingHom.mem_ker]`. Rewrite `h3` using `[map_sub, h1, zero_sub, neg_eq_zero]`. Conclude with `h3`. Establish `hε : PreTilt.untilt (Per6.tiltMap l ε) = 1`. Rewrite `h5` using `[← e, map_sub, map_one, θD_aD, frob_ainfMap_teich, WittVector.fontaineTheta_teichmuller, sub_eq_zero]`.

Conclude with `Subtype.ext h5`. Use `⟨hε, sub_eq_zero.1 (IsPerfectoidField.eq_zero_of_forall_mem_maximalIdeal_pow fun n => ?_)⟩` and prove the remaining obligations. Establish `h6` using `h n`. Rewrite `h6` using `[hm]`. Establish `h7` using `sub_mem h6 (fontaineT_sub_sum_mem hε n)`.

Rewrite `h7` using `[sub_sub_sub_cancel_right]`. Then use the resulting hypothesis. Introduce and unpack `⟨hε, rfl⟩ n`. Rewrite using `[hm]`. Conclude with `fontaineT_sub_sum_mem hε n`.
-/
theorem isLog_iff (ε : OCb l) (y : Per6.BdRp l) : Per6.IsLog l ε y ↔
    ∃ h : PreTilt.untilt (Per6.tiltMap l ε) = 1, y = fontaineT (Per6.tiltMap l ε) h := by
  have e : Per6.aD l (WittVector.teichmuller l ε) - 1 = muBdR l (Per6.tiltMap l ε) := by
    rw [muBdR_eq, ← frob_ainfMap_teich]
    rfl
  have hm : RingHom.ker (Per6.θD l) = IsLocalRing.maximalIdeal (Per6.BdRp l) :=
    (IsPerfectoidField.maximalIdeal_bDeRhamPlus (K := ℂ_[l]) (p := l)).symm
  unfold Per6.IsLog
  rw [e]
  constructor
  · intro h
    have h1 := h 1
    have h2 := h 2
    simp only [Finset.Ico_self, Finset.sum_empty, sub_zero, pow_one] at h1
    have h3 : y - muBdR l (Per6.tiltMap l ε) ∈ RingHom.ker (Per6.θD l) := by
      have h4 := Ideal.pow_le_self two_ne_zero h2
      simpa using h4
    have h5 : Per6.θD l (muBdR l (Per6.tiltMap l ε)) = 0 := by
      rw [RingHom.mem_ker] at h1 h3
      rw [map_sub, h1, zero_sub, neg_eq_zero] at h3
      exact h3
    have hε : PreTilt.untilt (Per6.tiltMap l ε) = 1 := by
      rw [← e, map_sub, map_one, θD_aD, frob_ainfMap_teich, WittVector.fontaineTheta_teichmuller,
        sub_eq_zero] at h5
      exact Subtype.ext h5
    refine ⟨hε, sub_eq_zero.1 (IsPerfectoidField.eq_zero_of_forall_mem_maximalIdeal_pow fun n => ?_)⟩
    have h6 := h n
    rw [hm] at h6
    have h7 := sub_mem h6 (fontaineT_sub_sum_mem hε n)
    rwa [sub_sub_sub_cancel_right] at h7
  · rintro ⟨hε, rfl⟩ n
    rw [hm]
    exact fontaineT_sub_sum_mem hε n

/- English proof (translation)
Rewrite using `[isLog_iff]`. Establish `h : ∀ e, e = epsilon l → ∃ h : PreTilt.untilt e = 1, tBdR l = fontaineT e h`. Introduce and unpack `_ rfl`. Conclude with `⟨untilt_epsilon, rfl⟩`. Conclude with `h _ tiltMap_εO`.
-/
theorem isLog_tBdR : Per6.IsLog l (εO l) (tBdR l) := by
  rw [isLog_iff]
  have h : ∀ e, e = epsilon l → ∃ h : PreTilt.untilt e = 1, tBdR l = fontaineT e h := by
    rintro _ rfl
    exact ⟨untilt_epsilon, rfl⟩
  exact h _ tiltMap_εO

end PositivityTheory.LocInh
