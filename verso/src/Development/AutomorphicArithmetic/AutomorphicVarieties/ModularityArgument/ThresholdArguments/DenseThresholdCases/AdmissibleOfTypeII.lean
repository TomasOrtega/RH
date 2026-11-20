import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.AdmissibleOfTypeII
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.AutNewformW

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open private cls_eq_one block_form conj_mat eigvec exists_two from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.AdmissibleOfTypeII
open UpperTheory.GalN.V
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3
/- English proof (translation)
Introduce `hC Ω _ _ _ K _ _ _ l hl c N _ e ψ D U g₁ hM r h ι hII hmod`. Take `⟨h11, -, W, hext, hcont, hirr, -, hdet⟩` from `typeII_facts hC D hM h hII`. Take `⟨-, -, -, -, -, -, -, -, -, -, hl1⟩` from `dat_facts D`. Set `ψQ : G ℚ Ω →* (Qbar l)ˣ` to `(Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom).comp (Chr.dirG ℚ Ω ψ)`. Establish `hΨ : ∀ g, D.ΨQ g = cycBar ℚ Ω l g ^ (e : ℤ) * ψQ g` using `fun g => by show Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom (chiO ℚ Ω l c.O g ^ (e : ℤ) * Chr.dirG ℚ Ω ψ g) = _`.

Rewrite using `[map_mul, map_zpow]`. Both sides reduce to the same expression. Establish `hfin : ∀ g, ψQ g ^ Nat.card (ZMod N)ˣ = 1` using `fun g => by show Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom (ψ.toUnitHom (Chr.cls ℚ Ω N g)) ^ _ = 1`. Rewrite using `[← map_pow, ← map_pow, pow_card_eq_one', map_one, map_one]`. Establish `hodd : Odd (discr K).natAbs` using `Nat.coprime_two_right.1 (D.gd.cop.coprime_dvd_right D.gd.N_even.two_dvd)`.

Establish `hkill : ∀ g : G ℚ Ω, (∀ ζ : Ω, ζ ^ (N * (discr K).natAbs) = 1 → g ζ = ζ) → ψQ g = 1 ∧ D.η g = 1` using `fun g hg => by`. Prove the components needed by the constructor for the conclusion. Use `show Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom (ψ.toUnitHom (Chr.cls ℚ Ω N g)) = 1`. Rewrite using `[cls_eq_one N g fun ζ hζ => hg ζ (by rw [pow_mul, hζ, one_pow]), map_one, map_one]`. Rewrite using `[← MonoidHom.mem_ker, D.η_ker]`.

Conclude with `UpperTheory.mem_galOf_quadratic_of_fixes_discr_roots_of_unity Ω K D.gd.quad hodd g fun ζ hζ => hg ζ (by rw [pow_mul', hζ, one_pow])`. Establish `hblk : ∀ g ∈ D.η.ker, (r g).mat = !![W g 0 0, 0, W g 0 1; 0, 1, 0; W g 1 0, 0, W g 1 1]` using `fun g hg => block_form _ _ (hII.1 g hg) (h11 g hg) (hext.1 g hg)`. Use `⟨W, hirr, hmod W hext, ⟨hcont, fun w hw => ?_, fun w hw => ?_⟩, ?_, 1, fun s => ?_⟩` and prove the remaining obligations. Take `⟨A, hA⟩` from `exists_isPlaceOver Ω w`. Establish `hAl : ¬ A.valuation (l : Ω) < 1` using `fun h' => hw (((places ℚ Ω l A).2.2.1 w hA).1 h')`.

Take `⟨M, hMM⟩` from `pt_inertia_away D hM h A hAl`. Establish `h1` using `UpperTheory.diagonal_on_subgroup_of_conjugate (Ine (F := ℚ) A ⊓ D.η.ker) W ψQ M fun g hg => by`. Establish `hc : cycZ ℚ Ω l g = 1` using `(places ℚ Ω l A).2.2.2 hAl hg.1`. Establish `hc' : cycBar ℚ Ω l g = 1`. Rewrite using `[cycBar, MonoidHom.comp_apply, hc, map_one]`.

Rewrite using `[← hblk g hg.2, hMM g hg.1 hg.2, GG.mat, unitaryThreeReflection_left, tor_val, hΨ, hc', _root_.one_zpow, one_mul]`. Use `congr 2`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `fin_cases i <;> simp [wt1]`. Take `⟨χ, hχ, hd⟩` from `UpperTheory.exists_isDiagOn_of_isDiagOn_inf_ker_sign _ _ W ψQ h1`.

Conclude with `⟨A, hA, χ, fun i s hs => hχ i s (hkill s hs).1 (hkill s hs).2, hd⟩`. Take `⟨A, hA⟩` from `exists_isPlaceOver Ω w`. Establish `hAl : A.valuation (l : Ω) < 1` using `((places ℚ Ω l A).2.2.1 w hA).2 hw`. Take `⟨-, M, hup, hdiag⟩` from `pt_inertia_above hC D hM h A hAl`. Take `⟨hIk, s₀, hs₀, hu⟩` from `hl1 A hAl`.

Take `⟨hnorm, hID, -⟩` from `Chr.decCyc Ω l A hl.out hAl`. Establish `hs₀' : (D.ΨQ s₀ : Qbar l) ^ 2 ≠ 1`. Use `(hu.map (algebraMap c.O (PadicAlgCl l))).ne_zero` as an intermediate fact. Rewrite `this` using `[map_sub, map_pow, map_one, sub_ne_zero]`. Conclude with `this`.

Use `set v : Fin 3 → Qbar l := (M⁻¹ : GL (Fin 3) (Qbar l)).val *ᵥ Pi.single 0 1 with hv`. Establish `hv0 : v ≠ 0` using `fun h0 => by`. Use `congrArg (fun x => (M.val *ᵥ x) 0) (hv.symm.trans h0)` as an intermediate fact. Simplify using `only [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec, Matrix.mulVec_zero] at this`. Simplify using `at this`.

Establish `hev : ∀ s ∈ Ine (F` using `ℚ) A, !![W s 0 0, 0, W s 0 1; 0, 1, 0; W s 1 0, 0, W s 1 1] *ᵥ v = (D.ΨQ s : Qbar l) • v := fun s hs => by`. Establish `hr : (r s).right = 1` using `(h.mult s).trans (hIk hs)`. Rewrite using `[← hblk s (hIk hs)]`. Use `eigvec M _ _ ?_ fun i j hij => ?_` and prove the remaining obligations. Rewrite using `[← conj_mat M r s hr, hdiag s hs 0]`.

Simplify using `[GG.mat, tor_val, wt1]`. Rewrite using `[← conj_mat M r s hr]`. Conclude with `hup s (hID hs) (hIk hs) i j hij`. Establish `hv1 : v 1 = 0`. Use `congrFun (hev s₀ hs₀) 1` as an intermediate fact.

Simplify using `[Matrix.mulVec, dotProduct, Fin.sum_univ_three] at this`. Assume the negation of the conclusion as `hne`. Establish `h3 : (D.ΨQ s₀ : Qbar l) = 1` using `(mul_right_cancel₀ hne ((one_mul _).trans this)).symm`. Conclude with `hs₀' (by rw [h3, one_pow])`. Take `⟨κ, hflag, hκ⟩` from `UpperTheory.exists_isFlagOn_of_eigenvector_normal_subgroup (Dec (F := ℚ) A) (Ine (F := ℚ) A) W D.ΨQ ![v 0, v 2] (fun d hd s hs => hnorm.conj_mem' ⟨s, hID hs⟩ hs ⟨d, hd⟩) (fun h0 => hv0 (by`.

Use function extensionality and compare the values at `i`. Use `fin_cases i`. Conclude with `congrFun h0 0`. Conclude with `hv1`. Conclude with `congrFun h0 1))`.

Use the proof step `(fun s hs => by`. Establish `a0` using `congrFun (hev s hs) 0`. Establish `a2` using `congrFun (hev s hs) 2`. Use function extensionality and compare the values at `i`. Use `fin_cases i`.

Simplify `a0` using `[Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two]`. Simplify `a2)` using `[Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two]`. Use the proof step `(fun s hs => by rw [hdet, show D.η s = 1 from hIk hs]; simp)`. Use the proof step `⟨s₀, hs₀, hs₀'⟩`. Establish `hκ' : ∀ i (s : ↥(Dec (F` using `ℚ) A)), (s : G ℚ Ω) ∈ Ine (F := ℚ) A → κ i s = cycBar ℚ Ω l s ^ (![(e : ℤ), -(e : ℤ)] i) * (![ψQ, ψQ⁻¹] i) s := fun i s hs => by fin_cases i`.

Conclude with `(hκ s hs).1.trans (hΨ s)`. Use `(hκ s hs).2.trans ?_` and prove the remaining obligations. Rewrite using `[hΨ, mul_inv, ← _root_.zpow_neg]`. Both sides reduce to the same expression. Use `⟨A, hA, ![ψQ, ψQ⁻¹], κ, fun i s hs => ?_, hflag, hκ', Or.inl fun i j hij => ?_⟩` and prove the remaining obligations.

Apply the tactic sequence `fin_cases i <;> simp [(hkill s hs).1]`. Take `⟨s, hs, hn⟩` from `exists_two D.gd.l_odd A hAl`. Establish `h1` using `DFunLike.congr_fun hij ⟨s, hID hs⟩`. Rewrite `h1` using `[MonoidHom.mul_apply, hκ' i _ hs, hκ' j _ hs]`. Establish `hf : ∀ i, ((![ψQ, ψQ⁻¹] i) s) ^ Nat.card (ZMod N)ˣ = 1` using `fun i => by fin_cases i`.

Conclude with `hfin s`. Use `show (ψQ s)⁻¹ ^ _ = 1`. Rewrite using `[inv_pow, hfin, inv_one]`. Establish `h2` using `congrArg (· ^ Nat.card (ZMod N)ˣ) h1`. Simplify using `only [mul_pow, hf, mul_one] at h2`.

Express the relevant statement in the definitionally equal form `(cycBar ℚ Ω l s ^ _) ^ _ = (cycBar ℚ Ω l s ^ _) ^ _ * cycBar ℚ Ω l s ^ _ at h2`. Rewrite `h2` using `[← mul_pow, ← _root_.zpow_add_one, ← mul_inv_eq_one, ← inv_pow, ← mul_pow, ← _root_.zpow_sub, ← _root_.zpow_natCast, ← _root_.zpow_mul]`. Establish `h3` using `(mul_eq_zero.1 (hn _ h2)).resolve_right (by exact_mod_cast Nat.card_pos.ne')`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp at h3 <;> omega`. Use `⟨N * (discr K).natAbs, Matrix.GeneralLinearGroup.det.comp W, Nat.mul_pos (NeZero.pos N) hodd.pos, fun s hs => Units.ext ?_, by simp⟩` and prove the remaining obligations.

Use `hdet s` as an intermediate fact. Rewrite `this` using `[(hkill s hs).2]`. Simplify using `using this`. Rewrite using `[one_mul, inv_one, mul_one, D.rhoK_apply]`. Conclude with `hblk _ (D.η_ker ▸ galEmb_mem ℚ K Ω s)`.
-/
theorem UpperTheory.GalN.V.adm2B_rhoK_of_typeII_of_modular_extensions :
    CohInp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) {U : D.ULoc} {g₁ : G ℚ Ω}, D.Marked g₁ → ∀ {r : G ℚ Ω →* GG 3 (PadicAlgCl l)} (h : D.IsPt U g₁ r), ∀ (ι : Qbar l ≃+* ℂ),
      TypeII D.η r → (∀ W : G ℚ Ω →* GL (Fin 2) (PadicAlgCl l), D.IsExt r W → _root_.UpperTheory.V.Z.Win.Dn.IsModularA D ι W) →
      _root_.UpperTheory.V.Z.Win.Dn.Adm2B ι e (N * (discr K).natAbs) (D.rhoK r h.mult) := by
  intro hC Ω _ _ _ K _ _ _ l hl c N _ e ψ D U g₁ hM r h ι hII hmod
  obtain ⟨h11, -, W, hext, hcont, hirr, -, hdet⟩ := typeII_facts hC D hM h hII
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hl1⟩ := dat_facts D
  let ψQ : G ℚ Ω →* (Qbar l)ˣ := (Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom).comp (Chr.dirG ℚ Ω ψ)
  have hΨ : ∀ g, D.ΨQ g = cycBar ℚ Ω l g ^ (e : ℤ) * ψQ g := fun g => by
    show Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom (chiO ℚ Ω l c.O g ^ (e : ℤ) * Chr.dirG ℚ Ω ψ g) = _
    rw [map_mul, map_zpow]
    rfl
  have hfin : ∀ g, ψQ g ^ Nat.card (ZMod N)ˣ = 1 := fun g => by
    show Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom (ψ.toUnitHom (Chr.cls ℚ Ω N g)) ^ _ = 1
    rw [← map_pow, ← map_pow, pow_card_eq_one', map_one, map_one]
  have hodd : Odd (discr K).natAbs := Nat.coprime_two_right.1 (D.gd.cop.coprime_dvd_right D.gd.N_even.two_dvd)
  have hkill : ∀ g : G ℚ Ω, (∀ ζ : Ω, ζ ^ (N * (discr K).natAbs) = 1 → g ζ = ζ) → ψQ g = 1 ∧ D.η g = 1 := fun g hg => by
    constructor
    · show Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom (ψ.toUnitHom (Chr.cls ℚ Ω N g)) = 1
      rw [cls_eq_one N g fun ζ hζ => hg ζ (by rw [pow_mul, hζ, one_pow]), map_one, map_one]
    · rw [← MonoidHom.mem_ker, D.η_ker]
      exact UpperTheory.mem_galOf_quadratic_of_fixes_discr_roots_of_unity Ω K D.gd.quad hodd g fun ζ hζ => hg ζ (by rw [pow_mul', hζ, one_pow])
  have hblk : ∀ g ∈ D.η.ker, (r g).mat = !![W g 0 0, 0, W g 0 1; 0, 1, 0; W g 1 0, 0, W g 1 1] := fun g hg =>
    block_form _ _ (hII.1 g hg) (h11 g hg) (hext.1 g hg)
  refine ⟨W, hirr, hmod W hext, ⟨hcont, fun w hw => ?_, fun w hw => ?_⟩, ?_, 1, fun s => ?_⟩
  · obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    have hAl : ¬ A.valuation (l : Ω) < 1 := fun h' => hw (((places ℚ Ω l A).2.2.1 w hA).1 h')
    obtain ⟨M, hMM⟩ := pt_inertia_away D hM h A hAl
    have h1 := UpperTheory.diagonal_on_subgroup_of_conjugate (Ine (F := ℚ) A ⊓ D.η.ker) W ψQ M fun g hg => by
      have hc : cycZ ℚ Ω l g = 1 := (places ℚ Ω l A).2.2.2 hAl hg.1
      have hc' : cycBar ℚ Ω l g = 1 := by
        rw [cycBar, MonoidHom.comp_apply, hc, map_one]
      rw [← hblk g hg.2, hMM g hg.1 hg.2, GG.mat, unitaryThreeReflection_left, tor_val, hΨ, hc', _root_.one_zpow, one_mul]
      congr 2
      funext i
      fin_cases i <;> simp [wt1]
    obtain ⟨χ, hχ, hd⟩ := UpperTheory.exists_isDiagOn_of_isDiagOn_inf_ker_sign _ _ W ψQ h1
    exact ⟨A, hA, χ, fun i s hs => hχ i s (hkill s hs).1 (hkill s hs).2, hd⟩
  · obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    have hAl : A.valuation (l : Ω) < 1 := ((places ℚ Ω l A).2.2.1 w hA).2 hw
    obtain ⟨-, M, hup, hdiag⟩ := pt_inertia_above hC D hM h A hAl
    obtain ⟨hIk, s₀, hs₀, hu⟩ := hl1 A hAl
    obtain ⟨hnorm, hID, -⟩ := Chr.decCyc Ω l A hl.out hAl
    have hs₀' : (D.ΨQ s₀ : Qbar l) ^ 2 ≠ 1 := by
      have := (hu.map (algebraMap c.O (PadicAlgCl l))).ne_zero
      rw [map_sub, map_pow, map_one, sub_ne_zero] at this
      exact this
    set v : Fin 3 → Qbar l := (M⁻¹ : GL (Fin 3) (Qbar l)).val *ᵥ Pi.single 0 1 with hv
    have hv0 : v ≠ 0 := fun h0 => by
      have := congrArg (fun x => (M.val *ᵥ x) 0) (hv.symm.trans h0)
      simp only [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec, Matrix.mulVec_zero] at this
      simp at this
    have hev : ∀ s ∈ Ine (F := ℚ) A,
        !![W s 0 0, 0, W s 0 1; 0, 1, 0; W s 1 0, 0, W s 1 1] *ᵥ v = (D.ΨQ s : Qbar l) • v := fun s hs => by
      have hr : (r s).right = 1 := (h.mult s).trans (hIk hs)
      rw [← hblk s (hIk hs)]
      refine eigvec M _ _ ?_ fun i j hij => ?_
      · rw [← conj_mat M r s hr, hdiag s hs 0]
        simp [GG.mat, tor_val, wt1]
      · rw [← conj_mat M r s hr]
        exact hup s (hID hs) (hIk hs) i j hij
    have hv1 : v 1 = 0 := by
      have := congrFun (hev s₀ hs₀) 1
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at this
      by_contra hne
      have h3 : (D.ΨQ s₀ : Qbar l) = 1 := (mul_right_cancel₀ hne ((one_mul _).trans this)).symm
      exact hs₀' (by rw [h3, one_pow])
    obtain ⟨κ, hflag, hκ⟩ := UpperTheory.exists_isFlagOn_of_eigenvector_normal_subgroup (Dec (F := ℚ) A) (Ine (F := ℚ) A) W D.ΨQ ![v 0, v 2]
      (fun d hd s hs => hnorm.conj_mem' ⟨s, hID hs⟩ hs ⟨d, hd⟩)
      (fun h0 => hv0 (by
        funext i
        fin_cases i
        · exact congrFun h0 0
        · exact hv1
        · exact congrFun h0 1))
      (fun s hs => by
        have a0 := congrFun (hev s hs) 0
        have a2 := congrFun (hev s hs) 2
        funext i
        fin_cases i
        · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two] using a0
        · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two] using a2)
      (fun s hs => by rw [hdet, show D.η s = 1 from hIk hs]; simp)
      ⟨s₀, hs₀, hs₀'⟩
    have hκ' : ∀ i (s : ↥(Dec (F := ℚ) A)), (s : G ℚ Ω) ∈ Ine (F := ℚ) A →
        κ i s = cycBar ℚ Ω l s ^ (![(e : ℤ), -(e : ℤ)] i) * (![ψQ, ψQ⁻¹] i) s := fun i s hs => by
      fin_cases i
      · exact (hκ s hs).1.trans (hΨ s)
      · refine (hκ s hs).2.trans ?_
        rw [hΨ, mul_inv, ← _root_.zpow_neg]
        rfl
    refine ⟨A, hA, ![ψQ, ψQ⁻¹], κ, fun i s hs => ?_, hflag, hκ', Or.inl fun i j hij => ?_⟩
    · fin_cases i <;> simp [(hkill s hs).1]
    · obtain ⟨s, hs, hn⟩ := exists_two D.gd.l_odd A hAl
      have h1 := DFunLike.congr_fun hij ⟨s, hID hs⟩
      rw [MonoidHom.mul_apply, hκ' i _ hs, hκ' j _ hs] at h1
      have hf : ∀ i, ((![ψQ, ψQ⁻¹] i) s) ^ Nat.card (ZMod N)ˣ = 1 := fun i => by
        fin_cases i
        · exact hfin s
        · show (ψQ s)⁻¹ ^ _ = 1
          rw [inv_pow, hfin, inv_one]
      have h2 := congrArg (· ^ Nat.card (ZMod N)ˣ) h1
      simp only [mul_pow, hf, mul_one] at h2
      change (cycBar ℚ Ω l s ^ _) ^ _ = (cycBar ℚ Ω l s ^ _) ^ _ * cycBar ℚ Ω l s ^ _ at h2
      rw [← mul_pow, ← _root_.zpow_add_one, ← mul_inv_eq_one, ← inv_pow, ← mul_pow, ← _root_.zpow_sub, ← _root_.zpow_natCast,
        ← _root_.zpow_mul] at h2
      have h3 := (mul_eq_zero.1 (hn _ h2)).resolve_right (by exact_mod_cast Nat.card_pos.ne')
      fin_cases i <;> fin_cases j <;> simp at h3 <;> omega
  · refine ⟨N * (discr K).natAbs, Matrix.GeneralLinearGroup.det.comp W,
      Nat.mul_pos (NeZero.pos N) hodd.pos, fun s hs => Units.ext ?_, by simp⟩
    have := hdet s
    rw [(hkill s hs).2] at this
    simpa using this
  · rw [one_mul, inv_one, mul_one, D.rhoK_apply]
    exact hblk _ (D.η_ker ▸ galEmb_mem ℚ K Ω s)
end
