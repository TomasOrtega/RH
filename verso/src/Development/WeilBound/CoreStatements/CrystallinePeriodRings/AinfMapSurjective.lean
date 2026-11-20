import Mathlib
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.FrobAinfMapFrobenius

noncomputable section

namespace PositivityTheory.LocInh

open GroundTheory.PAdicHodge Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem actC_ext (g : GQ l) (x : Om l) : actC l g (x : ℂ_[l]) = ((g x : Om l) : ℂ_[l]) :=
  galCp_coe (Per6.toBot g) x

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem actC_norm (g : GQ l) (y : ℂ_[l]) : ‖actC l g y‖ = ‖y‖ :=
  norm_galCp (Per6.toBot g) y

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
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
Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact.

A detailed English derivation is pending.
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
A detailed English derivation is pending.
-/
theorem galT_one (x : OCb l) : galT (1 : GQ l) x = x :=
  galT_ext fun _ y hy => ⟨y, by rw [map_one]; rfl, hy⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem galT_mul (g h : GQ l) (x : OCb l) : galT (g * h) x = galT g (galT h x) :=
  galT_ext fun n y hy => by
    obtain ⟨y₁, h₁, e₁⟩ := galT_coeff h x n y hy
    obtain ⟨y₂, h₂, e₂⟩ := galT_coeff g (galT h x) n y₁ e₁
    exact ⟨y₂, by rw [h₂, h₁, map_mul]; rfl, e₂⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ζO_zero : ζO l 0 = 1 :=
  Subtype.ext rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem ζO_succ (n : ℕ) : ζO l (n + 1) ^ l = ζO l n := by
  rw [ζO, ζO, ← map_pow, rootSeqInt_succ_pow]

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem ζO_one : ζO l 1 ≠ 1 := fun h =>
  rootSeq_one_ne_one (p := l) (congrArg Subtype.val h)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem εO_coeff (n : ℕ) :
    PreTilt.coeff n (εO l) = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) (ζO l n) := rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem ιCD_aB (a : Ainf l) :
    ιCD l (Per6.aB l a) = algebraMap (Per6.BdRp l) (Per6.BdR l) (Per6.aD l a) := by
  rw [frob_aB_apply, ιCD_cB, cD_apply, ACris.iota_algebraMap]
  rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
A detailed English derivation is pending.
-/
theorem ainfMap_injective : Function.Injective (Per6.ainfMap l) :=
  WittVector.map_injective _ (tiltEquiv l).injective

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ainfMap_surjective : Function.Surjective (Per6.ainfMap l) :=
  WittVector.map_surjective _ (tiltEquiv l).surjective

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem aB_injective : Function.Injective (Per6.aB l) := by
  intro a b h
  have h1 := congrArg (ιCD l) h
  rw [ιCD_aB, ιCD_aB] at h1
  exact ainfMap_injective (wittTo_injective
    (IsPerfectoidField.algebraMap_bDeRham_injective (K := ℂ_[l]) (p := l) h1))

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem aB_act (g : GQ l) (a : Ainf l) :
    Per6.aB l (WittVector.map (galT g) a) = Per6.σB g (Per6.aB l a) := by
  have h : Per6.ainfMap l (WittVector.map (galT g) a) = Per6.toBot g • Per6.ainfMap l a := by
    refine WittVector.ext fun n => ?_
    rw [AInf.gal_smul_coeff]
    exact tiltMap_tiltInv l _
  rw [frob_aB_apply, frob_aB_apply, σB_cB, h, ← ACris.gal_smul_algebraMap, ACris.gal_smul_def]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem ιCD_aB_mem_zero (a : Ainf l) : ιCD l (Per6.aB l a) ∈ Per6.FilD l 0 := by
  rw [ιCD_aB]
  exact (IsPerfectoidField.mem_fil_zero_iff ℂ_[l] l).2 ⟨_, rfl⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem tiltMap_εO : Per6.tiltMap l (εO l) = epsilon l := tiltMap_tiltInv l _

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem fil_nat (b : Per6.BdRp l) (n : ℕ) :
    algebraMap (Per6.BdRp l) (Per6.BdR l) b ∈ Per6.FilD l n ↔ b ∈ RingHom.ker (Per6.θD l) ^ n := by
  rw [Per6.θD, ← IsPerfectoidField.maximalIdeal_bDeRhamPlus]
  exact IsPerfectoidField.algebraMap_mem_fil_iff b n

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem θD_aD (a : Ainf l) : Per6.θD l (Per6.aD l a) =
    ((WittVector.fontaineTheta ↥(normInteger ℂ_[l]) l (Per6.ainfMap l a) : normInteger ℂ_[l]) : ℂ_[l]) :=
  IsPerfectoidField.thetaBDeRhamPlusField_wittToBDeRhamPlus l _

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. Assume the hypotheses and unpack their components. Supply the required witnesses or components.
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
By extensionality, compare the relevant components. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem ainf_zA (z : ℤ_[l]) :
    Per6.ainfMap l (Per6.zA l z) = IsPerfectoidField.padicIntToWitt l z := by
  ext n
  simp only [Per6.ainfMap, Per6.zA, IsPerfectoidField.padicIntToWitt, RingHom.comp_apply,
    WittVector.map_coeff]
  exact (RingHom.congr_fun (RingHom.ext_zmod ((Per6.tiltMap l).comp (ZMod.castHom (dvd_refl l) _))
    (ZMod.castHom (dvd_refl l) _)) _)

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem qB_coe (z : ℤ_[l]) : qB l (z : ℚ_[l]) = Per6.zB l z := by
  rw [frob_qB_coe, Per6.zB, RingHom.comp_apply, frob_aB_apply, ainf_zA]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem oD_coe (z : ℤ_[l]) : oD l (algebraMap ℚ_[l] (Om l) (z : ℚ_[l])) = Per6.zD l z := by
  rw [← ιCD_qB, qB_coe, Per6.zB, RingHom.comp_apply, ιCD_aB]
  rfl

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem oD_lift (x : Om l) : ∃ y : Per6.BdRp l,
    oD l x = algebraMap (Per6.BdRp l) (Per6.BdR l) y ∧ Per6.θD l y = (x : ℂ_[l]) :=
  ⟨algClToBdR l x, rfl, thetaAlgHom_algClToBdR l x⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
theorem isCrisDR_iff (f : Per6.Bcris l →+* Per6.BdR l) : Per6.IsCrisDR l f ↔ f = ιCD l := by
  constructor
  · intro h
    exact bcris_hom_ext fun x => (h x).trans ((ιCD_cB x).trans (cD_apply x)).symm
  · rintro rfl x
    exact (ιCD_cB x).trans (cD_apply x)

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Establish an intermediate fact. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Assume the hypotheses and unpack their components.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Assume the hypotheses and unpack their components. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem isLog_tBdR : Per6.IsLog l (εO l) (tBdR l) := by
  rw [isLog_iff]
  have h : ∀ e, e = epsilon l → ∃ h : PreTilt.untilt e = 1, tBdR l = fontaineT e h := by
    rintro _ rfl
    exact ⟨untilt_epsilon, rfl⟩
  exact h _ tiltMap_εO

end PositivityTheory.LocInh
