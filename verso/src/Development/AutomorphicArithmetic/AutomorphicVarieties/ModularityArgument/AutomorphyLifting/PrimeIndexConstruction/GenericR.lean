import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.MixSeedPAlt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGenericOfIsLocComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsMirabolicWhittakerStageOfIsCuspForm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousOfIsOpenStab

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric GlobalTheory.CuspRep.Generic UpperTheory.V

namespace UpperTheory.V.Z.Win.Birth

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

/- English proof (translation)
Establish `hcont : Continuous φ.1` using `GlobalTheory.SlTwoCusp.continuous_of_isOpen_stab F a φ h.1.level`. Use `⟨hcont, fun γ _ g => h.1.left γ g, ?_, ?_⟩` and prove the remaining obligations. Introduce `k hk y g`. Establish `he : IsEmpty (UnipotentBlockColumnIndex a k k)` using `⟨fun t => by have := t.1.2.isLt; have := t.2; omega⟩`. Establish `hy : y = 0` using `Subsingleton.elim _ _`.

Substitute `hy` using the available equality. Establish `hd : dot (eLast a k) (0 : UnipotentBlockColumnIndex a k k → Ad F) = 0` using `by simp [dot]`. Rewrite using `[hd, AddChar.map_zero_eq_one, one_mul]`. Unfold `blkU`. Rewrite using `[posU_zero, one_mul]`.

Introduce `r hr hra g`. Establish `hra' : r < a` using `by omega`. Establish `hper` using `per_blk (E := F) (r := r) (m := a - 1) hcont (fun c g => h.1.left _ g) g`. Establish `hper2 : Per (ratN F a r) (fun x => φ.1 (blkU (blkIxHomeo r x) * g))` using `⟨hper.1.comp (blkIxHomeo r).continuous, fun γ hγ x => by`. Simplify using `only [map_add]`.

Conclude with `hper.2 _ ((blkIxHomeo_mem r γ).2 hγ) _⟩`. Establish `key` using `GlobalTheory.T.quotientAverage_map_lattice_equiv _ _ (ratN F a r) (ratV F _) (isCoLat_ratV F (BlockIx a r)) (isCoLat_ratV F _) (blkIxHomeo r) (blkIxHomeo_mem r) _ hper`. Rewrite using `[← key]`. Establish `hfun : (fun x => φ.1 (blkU (blkIxHomeo r x) * g)) = fun x => φ.1 (unip x * g)`. Use function extensionality and compare the values at `fun x => by rw [← blkU_comp_equiv]; rfl`.

Rewrite `hper2`, the goal using `[hfun]`. Use `letI : MeasurableSpace (BlockIx a r → Ad F) := borel _`. Use `haveI : BorelSpace (BlockIx a r → Ad F) := ⟨rfl⟩`. Take `⟨μ, 𝓕, hμ, hF, h1⟩` from `GlobalTheory.T.exists_fundamentalDomain_mass_one_cocompactLattice _ (ratN F a r) (isCoLat_ratV F (BlockIx a r))`. Take `⟨-, -, -, hint⟩` from `GlobalTheory.T.setIntegral_fundamentalDomain_eq_mass_mul_average _ _ (isCoLat_ratV F (BlockIx a r)) μ 𝓕 hμ hF _ hper2`.

Establish `hc` using `h.2 r hr hra' μ 𝓕 hμ hF g`. Rewrite `hc` using `[hint, h1]`. Simplify using `only [ENNReal.toReal_one, Complex.ofReal_one, one_mul] at hc`. Conclude with `hc`.
-/
theorem good_of_isCuspFormR (a : ℕ) (ψ : AddChar (Ad F) ℂ) (φ : TR.Sm F a) (h : TR.IsCuspForm φ) :
    Good ψ (a - 1) φ.1 := by
  have hcont : Continuous φ.1 := GlobalTheory.SlTwoCusp.continuous_of_isOpen_stab F a φ h.1.level
  refine ⟨hcont, fun γ _ g => h.1.left γ g, ?_, ?_⟩
  · intro k hk y g
    have he : IsEmpty (UnipotentBlockColumnIndex a k k) := ⟨fun t => by have := t.1.2.isLt; have := t.2; omega⟩
    have hy : y = 0 := Subsingleton.elim _ _
    subst hy
    have hd : dot (eLast a k) (0 : UnipotentBlockColumnIndex a k k → Ad F) = 0 := by simp [dot]
    rw [hd, AddChar.map_zero_eq_one, one_mul]
    unfold blkU
    rw [posU_zero, one_mul]
  · intro r hr hra g
    have hra' : r < a := by omega
    have hper := per_blk (E := F) (r := r) (m := a - 1) hcont (fun c g => h.1.left _ g) g
    have hper2 : Per (ratN F a r) (fun x => φ.1 (blkU (blkIxHomeo r x) * g)) :=
      ⟨hper.1.comp (blkIxHomeo r).continuous, fun γ hγ x => by
        simp only [map_add]
        exact hper.2 _ ((blkIxHomeo_mem r γ).2 hγ) _⟩
    have key := GlobalTheory.T.quotientAverage_map_lattice_equiv _ _ (ratN F a r) (ratV F _) (isCoLat_ratV F (BlockIx a r))
      (isCoLat_ratV F _) (blkIxHomeo r) (blkIxHomeo_mem r) _ hper
    rw [← key]
    have hfun : (fun x => φ.1 (blkU (blkIxHomeo r x) * g)) = fun x => φ.1 (unip x * g) :=
      funext fun x => by rw [← blkU_comp_equiv]; rfl
    rw [hfun] at hper2 ⊢
    letI : MeasurableSpace (BlockIx a r → Ad F) := borel _
    haveI : BorelSpace (BlockIx a r → Ad F) := ⟨rfl⟩
    obtain ⟨μ, 𝓕, hμ, hF, h1⟩ := GlobalTheory.T.exists_fundamentalDomain_mass_one_cocompactLattice _ (ratN F a r) (isCoLat_ratV F (BlockIx a r))
    obtain ⟨-, -, -, hint⟩ := GlobalTheory.T.setIntegral_fundamentalDomain_eq_mass_mul_average _ _ (isCoLat_ratV F (BlockIx a r)) μ 𝓕 hμ hF _ hper2
    have hc := h.2 r hr hra' μ 𝓕 hμ hF g
    rw [hint, h1] at hc
    simp only [ENNReal.toReal_one, Complex.ofReal_one, one_mul] at hc
    exact hc

/- English proof (translation)
Take `⟨gw, hgw⟩ : ∃ gw, gw = GeneralLinearGroup.map (pLoc F w) (GeneralLinearGroup.map (pFin F) g)` from `⟨_, rfl⟩`. Use `⟨g * (finGL F a (locGL F a w gw))⁻¹, gw, by rw [inv_mul_cancel_right], fun u => ?_⟩` and prove the remaining obligations. Establish `hk : GeneralLinearGroup.map (pLoc F w) (GeneralLinearGroup.map (pFin F) (g * (finGL F a (locGL F a w gw))⁻¹)) = 1`. Rewrite using `[map_mul, map_inv, pFin_finGL, map_mul, map_inv, pLoc_locGL, hgw, mul_inv_cancel]`. Generalize the expression as in `g * (finGL F a (locGL F a w gw))⁻¹ = k at hk ⊢`.

Take `⟨y, z, rfl, hz⟩ : ∃ y z, k = TR.infGL F a y * finGL F a z ∧ GeneralLinearGroup.map (pLoc F w) z = 1` from `⟨_, _, (TR.infGL_mul_finGL k).symm, hk⟩`. Rewrite using `[mul_assoc, ← map_mul, LocUniq.comm_locGL w hz u, map_mul, ← mul_assoc, TR.infGL_comm, mul_assoc]`.
-/
private theorem exists_split_locR (a : ℕ) (w : HeightOneSpectrum (𝓞 F)) (g : GA F a) :
    ∃ (h : GA F a) (gw : GL (Fin a) (w.adicCompletion F)),
      g = h * finGL F a (locGL F a w gw) ∧
        ∀ u : GL (Fin a) (w.adicCompletion F),
          h * finGL F a (locGL F a w u) = finGL F a (locGL F a w u) * h := by
  obtain ⟨gw, hgw⟩ : ∃ gw, gw = GeneralLinearGroup.map (pLoc F w) (GeneralLinearGroup.map (pFin F) g) := ⟨_, rfl⟩
  refine ⟨g * (finGL F a (locGL F a w gw))⁻¹, gw, by rw [inv_mul_cancel_right], fun u => ?_⟩
  have hk : GeneralLinearGroup.map (pLoc F w)
      (GeneralLinearGroup.map (pFin F) (g * (finGL F a (locGL F a w gw))⁻¹)) = 1 := by
    rw [map_mul, map_inv, pFin_finGL, map_mul, map_inv, pLoc_locGL, hgw, mul_inv_cancel]
  generalize g * (finGL F a (locGL F a w gw))⁻¹ = k at hk ⊢
  obtain ⟨y, z, rfl, hz⟩ : ∃ y z, k = TR.infGL F a y * finGL F a z ∧ GeneralLinearGroup.map (pLoc F w) z = 1 :=
    ⟨_, _, (TR.infGL_mul_finGL k).symm, hk⟩
  rw [mul_assoc, ← map_mul, LocUniq.comm_locGL w hz u, map_mul, ← mul_assoc, TR.infGL_comm, mul_assoc]

/- English proof (translation)
Establish `hoff : ∀ i j : Fin a, i ≠ j → (finGL F a (locGL F a w u)).val i j = sFin F (sLoc F w (u.val i j))`. Introduce `i j h`. Rewrite using `[finGL, cornerGL_apply_ne_loctri _ _ h, locGL, cornerGL_apply_ne_loctri _ _ h]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i j h`.

Rewrite using `[hoff i j (ne_of_gt h), hlow i j h, map_zero, map_zero]`. Introduce `j`. Conclude with `cornerGL_apply_diag_loctri _ _ (cornerGL_apply_diag_loctri _ _ (hdiag j))`. Rewrite using `[map_sum, map_sum]`. Use `Finset.sum_congr rfl fun p hp => ?_` and prove the remaining obligations.

Establish `hp' : (p.2 : ℕ) = p.1 + 1` using `(Finset.mem_filter.mp hp).2`. Establish `hne : p.1 ≠ p.2`. Introduce `h`. Rewrite `hp'` using `[h]`. Use linear arithmetic over natural numbers and integers.

Conclude with `hoff p.1 p.2 hne`.
-/
private theorem locTri_adelicR (a : ℕ) (w : HeightOneSpectrum (𝓞 F)) (u : GL (Fin a) (w.adicCompletion F))
    (hlow : ∀ i j : Fin a, j < i → u.val i j = 0) (hdiag : ∀ j : Fin a, u.val j j = 1) :
    (∀ i j : Fin a, j < i → (finGL F a (locGL F a w u)).val i j = 0) ∧ (∀ j : Fin a, (finGL F a (locGL F a w u)).val j j = 1) ∧
      ∑ p : Fin a × Fin a with (p.2 : ℕ) = p.1 + 1, (finGL F a (locGL F a w u)).val p.1 p.2 =
        sFin F (sLoc F w (∑ p : Fin a × Fin a with (p.2 : ℕ) = p.1 + 1, u.val p.1 p.2)) := by
  have hoff : ∀ i j : Fin a, i ≠ j → (finGL F a (locGL F a w u)).val i j = sFin F (sLoc F w (u.val i j)) := by
    intro i j h
    rw [finGL, cornerGL_apply_ne_loctri _ _ h, locGL, cornerGL_apply_ne_loctri _ _ h]
  refine ⟨?_, ?_, ?_⟩
  · intro i j h
    rw [hoff i j (ne_of_gt h), hlow i j h, map_zero, map_zero]
  · intro j
    exact cornerGL_apply_diag_loctri _ _ (cornerGL_apply_diag_loctri _ _ (hdiag j))
  · rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp' : (p.2 : ℕ) = p.1 + 1 := (Finset.mem_filter.mp hp).2
    have hne : p.1 ≠ p.2 := by
      intro h; rw [h] at hp'; omega
    exact hoff p.1 p.2 hne

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in

/- English proof (translation)
Take `⟨f, hf0, hf⟩` from `hσ`. Take `⟨ψ, hψ⟩` from `GlobalTheory.T.exists_standardAdelicAddChar F`. Establish `hg : ∀ v, Good ψ (a - 1) (f v).1.1` using `fun v => good_of_isCuspFormR a ψ (f v).1 (P.cusp _ (f v).2)`. Establish `h0 : a - 1 < a ∨ a - 1 = 0` using `by omega`. Choose the witnesses or unpack the hypotheses as in `⟨v₀, hv₀⟩ : ∃ v, f v ≠ 0 := by`.

Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `hf0 (LinearMap.ext h)`. Establish `hv1 : (f v₀).1.1 ≠ 0` using `fun h => hv₀ (Subtype.ext (Subtype.ext h))`. Take `⟨g₀, hg₀⟩` from `Function.ne_iff.1 ((whit_good hψ (a - 1) h0 (hg v₀)).2 hv1)`.

Take `⟨h, gw, e, hc⟩` from `exists_split_locR a w g₀`. Establish `hrt : ∀ u v x, whit ψ (a - 1) (f (σ.ρ u v)).1.1 x = whit ψ (a - 1) (f v).1.1 (x * finGL F a (locGL F a w u))` using `fun u v x => by`. Rewrite using `[hf u v]`. Conclude with `whit_rt _ _ _ _`. Set `l : σ.V →ₗ[ℂ] ℂ` to `{ toFun := fun v => whit ψ (a - 1) (f v).1.1 h map_add' := fun v v' => by`.

Rewrite using `[map_add f]`. Conclude with `congrFun (whit_add hψ (a - 1) h0 (hg v) (hg v')) h`. Use the proof step `map_smul' := fun c v => by`. Rewrite using `[map_smul f]`. Conclude with `congrFun (whit_smul (a - 1) c (f v).1.1) h }`.

Establish `hl : ∀ v, l v = whit ψ (a - 1) (f v).1.1 h` using `fun _ => rfl`. Establish `hne : l (σ.ρ gw v₀) ≠ 0`. Rewrite using `[hl, hrt, ← e]`. Conclude with `hg₀`. Establish `hlaw : ∀ (u : GlobalTheory.SmGL.unipB (w.adicCompletion F) (Fin a)) v, l (σ.ρ u v) = (locPsi hψ w (∑ p : Fin a × Fin a with (p.2 : ℕ) = p.1 + 1, (u : GL (Fin a) (w.adicCompletion F)).val p.1 p.2) : ℂ) * l v`.

Introduce `u v`. Take `⟨u1, u2⟩` from `(GlobalTheory.SmGL.mem_unipB _).1 u.2`. Take `⟨t1, t2, t3⟩` from `locTri_adelicR a w u u1 u2`. Establish `hlw` using `(whit_good hψ (a - 1) h0 (hg v)).1.law`. Use `GlobalTheory.T.whittakerLaw_upperTriangularUnipotent_adelic F a ψ _ (fun k hk => hlw k hk) _ t1 t2 h` as an intermediate fact.

Rewrite using `[hl, hrt, hc, this, t3]`. Both sides reduce to the same expression. Use `⟨locPsi hψ w, ?_, fun h1 => ?_, ?_⟩` and prove the remaining obligations. Use `Continuous.subtype_mk (hψ.cont.comp ?_) _` and prove the remaining obligations. Conclude with `(continuous_const.prodMk continuous_id : Continuous fun x : Af F => ((0, x) : InfiniteAdeleRing F × Af F)).comp (CuspSub.continuous_sLoc w)`.

Take `⟨y, hy⟩` from `hψ.loc w`. Apply `hy` to reduce the goal to its premises. Use `congrArg (fun c : Circle => (c : ℂ)) (DFunLike.congr_fun h1 y)` as an intermediate fact. Simplify `this` using `[coe_locPsi]`. Use `Submodule.Quotient.nontrivial_iff.2 fun htop => hne ?_` and prove the remaining obligations.

Establish `hle : GlobalTheory.PRep.twKer σ.ρ (GlobalTheory.SmGL.unipB (w.adicCompletion F) (Fin a)) (GlobalTheory.LocGL.whitChar (locPsi hψ w) a) ≤ LinearMap.ker l`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨u, v, rfl⟩`. Simplify using `only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_smul, hlaw, smul_eq_mul]`. Conclude with `sub_eq_zero.2 rfl`.

Conclude with `hle (htop ▸ Submodule.mem_top)`.
-/
theorem isGeneric_of_isLocCompR (a : ℕ) (P : TR.CuspSub F a) (w : HeightOneSpectrum (𝓞 F))
    (σ : SmIrr (GL (Fin a) (w.adicCompletion F))) (hσ : P.IsLocComp w σ) : GlobalTheory.LocGL.IsGeneric σ.ρ := by
  obtain ⟨f, hf0, hf⟩ := hσ
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.exists_standardAdelicAddChar F
  have hg : ∀ v, Good ψ (a - 1) (f v).1.1 := fun v => good_of_isCuspFormR a ψ (f v).1 (P.cusp _ (f v).2)
  have h0 : a - 1 < a ∨ a - 1 = 0 := by omega
  obtain ⟨v₀, hv₀⟩ : ∃ v, f v ≠ 0 := by
    by_contra h
    push Not at h
    exact hf0 (LinearMap.ext h)
  have hv1 : (f v₀).1.1 ≠ 0 := fun h => hv₀ (Subtype.ext (Subtype.ext h))
  obtain ⟨g₀, hg₀⟩ := Function.ne_iff.1 ((whit_good hψ (a - 1) h0 (hg v₀)).2 hv1)
  obtain ⟨h, gw, e, hc⟩ := exists_split_locR a w g₀
  have hrt : ∀ u v x, whit ψ (a - 1) (f (σ.ρ u v)).1.1 x =
      whit ψ (a - 1) (f v).1.1 (x * finGL F a (locGL F a w u)) := fun u v x => by
    rw [hf u v]
    exact whit_rt _ _ _ _
  let l : σ.V →ₗ[ℂ] ℂ :=
    { toFun := fun v => whit ψ (a - 1) (f v).1.1 h
      map_add' := fun v v' => by
        rw [map_add f]
        exact congrFun (whit_add hψ (a - 1) h0 (hg v) (hg v')) h
      map_smul' := fun c v => by
        rw [map_smul f]
        exact congrFun (whit_smul (a - 1) c (f v).1.1) h }
  have hl : ∀ v, l v = whit ψ (a - 1) (f v).1.1 h := fun _ => rfl
  have hne : l (σ.ρ gw v₀) ≠ 0 := by
    rw [hl, hrt, ← e]
    exact hg₀
  have hlaw : ∀ (u : GlobalTheory.SmGL.unipB (w.adicCompletion F) (Fin a)) v,
      l (σ.ρ u v) = (locPsi hψ w (∑ p : Fin a × Fin a with (p.2 : ℕ) = p.1 + 1, (u : GL (Fin a) (w.adicCompletion F)).val p.1 p.2) : ℂ) * l v := by
    intro u v
    obtain ⟨u1, u2⟩ := (GlobalTheory.SmGL.mem_unipB _).1 u.2
    obtain ⟨t1, t2, t3⟩ := locTri_adelicR a w u u1 u2
    have hlw := (whit_good hψ (a - 1) h0 (hg v)).1.law
    have := GlobalTheory.T.whittakerLaw_upperTriangularUnipotent_adelic F a ψ _ (fun k hk => hlw k hk) _ t1 t2 h
    rw [hl, hrt, hc, this, t3]
    rfl
  refine ⟨locPsi hψ w, ?_, fun h1 => ?_, ?_⟩
  · refine Continuous.subtype_mk (hψ.cont.comp ?_) _
    exact (continuous_const.prodMk continuous_id : Continuous fun x : Af F => ((0, x) : InfiniteAdeleRing F × Af F)).comp
      (CuspSub.continuous_sLoc w)
  · obtain ⟨y, hy⟩ := hψ.loc w
    apply hy
    have := congrArg (fun c : Circle => (c : ℂ)) (DFunLike.congr_fun h1 y)
    simpa [coe_locPsi] using this
  · refine Submodule.Quotient.nontrivial_iff.2 fun htop => hne ?_
    have hle : GlobalTheory.PRep.twKer σ.ρ (GlobalTheory.SmGL.unipB (w.adicCompletion F) (Fin a)) (GlobalTheory.LocGL.whitChar (locPsi hψ w) a) ≤
        LinearMap.ker l := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨u, v, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_smul, hlaw, smul_eq_mul]
      exact sub_eq_zero.2 rfl
    exact hle (htop ▸ Submodule.mem_top)

end UpperTheory.V.Z.Win.Birth
