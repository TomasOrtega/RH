import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlipBoundOfHyp
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible

section
open GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ArchTens
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.ConjSize ValuativeRel
open Formalism.L2.Host GlobalTheory.StepData
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}
/- English proof (translation)
Establish `e` using `GivenAdm.isEquiv_val w`. Use `set q := Ideal.absNorm w.asIdeal`. Establish `hq : Valued.v ((q : ℕ) : Kw w) ≤ WithZero.exp (-1 : ℤ)`. Establish `hmem : ((q : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal ^ 1` using `by rw [pow_one]; exact Ideal.absNorm_mem w.asIdeal`. Establish `h2 : Valued.v ((q : ℕ) : Kw w) = w.intValuation ((q:ℕ) : 𝓞 D.host.E)`.

Rewrite using `[← map_natCast (algebraMap (𝓞 D.host.E) (Kw w))]`. Conclude with `(IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := D.host.E) w _).trans (IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap _ _)`. Rewrite using `[h2]`. Use `(w.intValuation_le_pow_iff_mem ((q:ℕ) : 𝓞 D.host.E) 1).2 hmem` as an intermediate fact. Simplify using `using this`.

Establish `hu : Valued.v ((unifAt w : (Kw w)ˣ) : Kw w) = WithZero.exp (-1 : ℤ)` using `unif_spec w`. Establish `hx' : Valued.v ((((unifAt w) ^ n : (Kw w)ˣ) : Kw w) * x) ≤ 1`. Use `(e ((((unifAt w) ^ n : (Kw w)ˣ) : Kw w) * x) 1).1 (by rw [map_one]; exact hx)` as an intermediate fact. Rewrite `this` using `[map_one]`. Then use the resulting hypothesis. Establish `hNx : Valued.v (((q ^ n : ℕ) : Kw w) * x) ≤ 1`.

Use `le_trans ?_ hx'` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, Units.val_pow_eq_pow_val, map_pow, Nat.cast_pow, map_pow, hu]`. Use `gcongr`. Establish `hNx2 : valuation (Kw w) (((q ^ n : ℕ) : Kw w) * x) ≤ valuation (Kw w) 1` using `(e (((q ^ n : ℕ) : Kw w) * x) 1).2 (by rw [map_one]; exact hNx)`. Establish `h1 : psiAt W w ((q ^ n) • x) = 1`.

Rewrite using `[nsmul_eq_mul]`. Conclude with `(hc 1).2 (by simp) _ hNx2`. Rewrite using `[← Circle.coe_pow, ← AddChar.map_nsmul_eq_pow, h1, Circle.coe_one]`.
-/
private theorem additive_character_pow_conductor {W : G.Weil} {w : Pl D.host.E} (hc : HasConductor (psiAt W w) 1) (n : ℕ) (x : Kw w)
    (hx : valuation (Kw w) ((((unifAt w) ^ n : (Kw w)ˣ) : Kw w) * x) ≤ 1) :
    (psiAt W w x : ℂ) ^ (Ideal.absNorm w.asIdeal ^ n) = 1 := by
  have e := GivenAdm.isEquiv_val w
  set q := Ideal.absNorm w.asIdeal
  have hq : Valued.v ((q : ℕ) : Kw w) ≤ WithZero.exp (-1 : ℤ) := by
    have hmem : ((q : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal ^ 1 := by rw [pow_one]; exact Ideal.absNorm_mem w.asIdeal
    have h2 : Valued.v ((q : ℕ) : Kw w) = w.intValuation ((q:ℕ) : 𝓞 D.host.E) := by
      rw [← map_natCast (algebraMap (𝓞 D.host.E) (Kw w))]
      exact (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := D.host.E) w _).trans
        (IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap _ _)
    rw [h2]
    have := (w.intValuation_le_pow_iff_mem ((q:ℕ) : 𝓞 D.host.E) 1).2 hmem
    simpa using this
  have hu : Valued.v ((unifAt w : (Kw w)ˣ) : Kw w) = WithZero.exp (-1 : ℤ) := unif_spec w
  have hx' : Valued.v ((((unifAt w) ^ n : (Kw w)ˣ) : Kw w) * x) ≤ 1 := by
    have := (e ((((unifAt w) ^ n : (Kw w)ˣ) : Kw w) * x) 1).1 (by rw [map_one]; exact hx)
    rwa [map_one] at this
  have hNx : Valued.v (((q ^ n : ℕ) : Kw w) * x) ≤ 1 := by
    refine le_trans ?_ hx'
    rw [map_mul, map_mul, Units.val_pow_eq_pow_val, map_pow, Nat.cast_pow, map_pow, hu]
    gcongr
  have hNx2 : valuation (Kw w) (((q ^ n : ℕ) : Kw w) * x) ≤ valuation (Kw w) 1 :=
    (e (((q ^ n : ℕ) : Kw w) * x) 1).2 (by rw [map_one]; exact hNx)
  have h1 : psiAt W w ((q ^ n) • x) = 1 := by
    rw [nsmul_eq_mul]
    exact (hc 1).2 (by simp) _ hNx2
  rw [← Circle.coe_pow, ← AddChar.map_nsmul_eq_pow, h1, Circle.coe_one]
/- English proof (translation)
Take `⟨i, _ | j⟩` from `X`. Rewrite using `[givenLevel, he]`. Break down `i with _ | i` into its components or cases. Take `⟨P, hP, -⟩` from `GivenAdm.exists_types hL hw`. Rewrite using `[GivenAdm.givenLevel_succ (hP _)]`.

Use `le_trans (fun g hg => mem_KOne.2 fun a b => ((GivenAdm.mem_glLatCong.1 hg).2 a b).trans_lt ?_) (TypeDatum.KOne_le _)` and prove the remaining obligations. Rewrite using `[Units.val_pow_eq_pow_val, map_pow]`. Conclude with `pow_lt_one₀ zero_le' (isUnif_unifAt w ▸ uniformizer_lt_one) (by rw [depthAt]; omega)`. Conclude with `fun g hg => (GivenAdm.mem_glLatCong.1 hg).1`.
-/
private theorem congruence_le_given_level {μ₀ : T} (hL : L.Is μ₀) {t : T} {w : Pl D.host.E} (hw : w ∈ locPl G t)
    (he : depthAt G w = cosExp G w) (X : ℕ × ℕ) :
    glLatCong (unifAt w ^ depthAt G w) (GlobalTheory.SplitFlip.stdLat (Kw w) _) ≤ givenLevel G t w X := by
  obtain ⟨i, _ | j⟩ := X
  · rw [givenLevel, he]
  · rcases i with _ | i
    · obtain ⟨P, hP, -⟩ := GivenAdm.exists_types hL hw
      rw [GivenAdm.givenLevel_succ (hP _)]
      refine le_trans (fun g hg => mem_KOne.2 fun a b => ((GivenAdm.mem_glLatCong.1 hg).2 a b).trans_lt ?_)
        (TypeDatum.KOne_le _)
      rw [Units.val_pow_eq_pow_val, map_pow]
      exact pow_lt_one₀ zero_le' (isUnif_unifAt w ▸ uniformizer_lt_one) (by rw [depthAt]; omega)
    · exact fun g hg => (GivenAdm.mem_glLatCong.1 hg).1
/- English proof (translation)
Establish `e1 : (((locGrid G t w).nu i j u : ℂˣ) : ℂ) = ((L.C.mu0 ⟨j, hj⟩).loc w u : ℂ) * ((L.xiH t).loc w u : ℂ) * (((G.ch.chiH (D.R.m - i)).loc w u : ℂ))⁻¹`. Simplify using `only [Grid.nu, locGrid, muBase, dif_pos hj, MonoidHom.div_apply, Units.val_div_eq_div_val, div_eq_mul_inv]`. Simplify using `[HChar.loc]`. Rewrite using `[e1]`. Conclude with `((hmu _ _).mul (hxi _)).mul (hchi _ (by omega) (by omega) _).inv`.
-/
private theorem local_grid_entries_unitary {K : Type} [Field K] {ι τ : K →+* ℂ} (t : T) (w : Pl D.host.E)
    (hmu : ∀ j x, Un ι τ ((L.C.mu0 j).loc w x : ℂ)) (hxi : ∀ x, Un ι τ ((L.xiH t).loc w x : ℂ))
    (hchi : ∀ i, 1 ≤ i → i ≤ D.R.m → ∀ x, Un ι τ ((G.ch.chiH i).loc w x : ℂ))
    {i j : ℕ} (hi : i < D.R.m) (hj : j < D.R.m) (u : (Kw w)ˣ) : Un ι τ ((locGrid G t w).nu i j u : ℂ) := by
  have e1 : (((locGrid G t w).nu i j u : ℂˣ) : ℂ) =
      ((L.C.mu0 ⟨j, hj⟩).loc w u : ℂ) * ((L.xiH t).loc w u : ℂ) * (((G.ch.chiH (D.R.m - i)).loc w u : ℂ))⁻¹ := by
    simp only [Grid.nu, locGrid, muBase, dif_pos hj, MonoidHom.div_apply, Units.val_div_eq_div_val, div_eq_mul_inv]
    simp [HChar.loc]
  rw [e1]
  exact ((hmu _ _).mul (hxi _)).mul (hchi _ (by omega) (by omega) _).inv
/- English proof (translation)
Express the relevant statement in the definitionally equal form `D.R.r + (j + 1) * D.R.t + (i + 1) * sLen D ≤ 2 * bigN D`. Establish `h1 : (j + 1) * D.R.t ≤ D.R.m * D.R.t` using `Nat.mul_le_mul_right _ hj`. Establish `h2 : (i + 1) * sLen D ≤ D.R.m * sLen D` using `Nat.mul_le_mul_right _ hi`. Establish `h3 : 1 * sLen D ≤ D.R.m * sLen D` using `Nat.mul_le_mul_right _ (by omega)`. Establish `h4 : D.R.r ≤ sLen D` using `Nat.le_add_right _ _`.

Unfold `bigN`. Rewrite using `[mul_add D.R.m, mul_add D.R.m]`. Use linear arithmetic over natural numbers and integers.
-/
private theorem local_grid_rank_le (t : T) (w : Pl D.host.E) {i j : ℕ} (hi : i < D.R.m) (hj : j < D.R.m) :
    (locGrid G t w).rank (i + 1, j + 1) ≤ 2 * bigN D := by
  change D.R.r + (j + 1) * D.R.t + (i + 1) * sLen D ≤ 2 * bigN D
  have h1 : (j + 1) * D.R.t ≤ D.R.m * D.R.t := Nat.mul_le_mul_right _ hj
  have h2 : (i + 1) * sLen D ≤ D.R.m * sLen D := Nat.mul_le_mul_right _ hi
  have h3 : 1 * sLen D ≤ D.R.m * sLen D := Nat.mul_le_mul_right _ (by omega)
  have h4 : D.R.r ≤ sLen D := Nat.le_add_right _ _
  unfold bigN
  rw [mul_add D.R.m, mul_add D.R.m]
  omega
end
open Formalism.BasicNotions Formalism.IndefR.Links Formalism.L2.DIV NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.ConjSize in
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw in
/- English proof (translation)
Use `fun _ => ⟨0, fun CF _ => ⟨48, fun ε C hC => ⟨0, ?_⟩⟩⟩` and prove the remaining obligations. Introduce `D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch _ hF σ Φ w₀ z`. Take `⟨w, hw⟩` from `w₀`. Use `haveI : IsCMField D.host.E := D.host.isCMField_hostE`. Establish `hL : R.toLevCh.Is A.μ0` using `hS.core.lev`.

Establish `hde` using `GlobalTheory.FlipIntegrand.pde_ne_q_of_setting hS`. Establish `hc : ∀ P ∈ R.toLevCh.Q A.μ0, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal` using `hch.guard A.μ0`. Establish `hg` using `(Good.locGrid_isGood hL ch.G ch.W A.μ0 hde hc).1 w hw`. Establish `hadm` using `GivenAdm.givenStage_isAdmissible hL ch.S.B A.μ0 Φ hw`. Establish `hm : 0 < D.R.m` using `by have := D.R.two_le_m; omega`.

Establish `h00` using `hg.square 0 hm 0 hm`. Establish `hW : w ∈ ch.G.pl.W0` using `(GivenAdm.mem_locPl.1 hw).resolve_right fun h => (hL.Q_ram A.μ0 w).2 (.inl h) (by rw [hL.xi_base]; exact fun _ _ => rfl)`. Establish `he : depthAt ch.G w = cosExp ch.G w`. Take `⟨h1, h2⟩` from `GivenAdm.under_mem_and_place_above_eq_of_mem hW`. Use `depthAt_w ch.G h1` as an intermediate fact.

Rewrite `this` using `[h2]`. Rewrite using `[this.1, this.2]`. Establish `hmu : ∀ j x, Un D.what₂.embLL σ ((R.toLevCh.C.mu0 j).loc w x : ℂ)` using `fun j x => by`. Take `⟨n, -, hn⟩` from `(R.toLevCh.C.isMu0 j).inf`. Conclude with `UpperTheory.conjSize_heckeChar_local_of_mem_range_embedding _ _ _ _ hn _ _ _ _ (hF.chars.mu0 j w x)`.

Establish `hxi : ∀ x, Un D.what₂.embLL σ ((R.toLevCh.xiH A.μ0).loc w x : ℂ)` using `fun x => by`. Rewrite using `[hL.xi_base]`. Conclude with `Un.one`. Establish `hchi : ∀ i, 1 ≤ i → i ≤ D.R.m → ∀ x, Un D.what₂.embLL σ ((ch.G.ch.chiH i).loc w x : ℂ)` using `fun i a b x => UpperTheory.conjSize_heckeChar_local_of_mem_range_embedding _ _ _ _ (ch.G.ch.inf i a b) _ _ _ _ (hF.chars.chi i a b w x)`. Establish `habs : ∀ u : (Kw w)ˣ, apow u (1 / 2) ∈ Set.range D.what₂.embLL` using `fun u => RingHom.mem_fieldRange.1 (GlobalTheory.TflipField.apow_half_mem D.what₂.embLL.fieldRange w (RingHom.mem_fieldRange.2 (hF.sqrt w (.inr ⟨A.μ0, hw⟩))) u)`.

Establish `hq0 : Ideal.absNorm w.asIdeal ≠ 0` using `fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)`. Establish `hψ` using `fun x hx => (fun h => Un.of_pow_eq_one (τ := σ) (hF.roots A.μ0 w hw _ h) (pow_ne_zero _ hq0) h) (additive_character_pow_conductor (W := ch.W) h00.cond (depthAt ch.G w) x hx)`. Establish `hν : ∀ x ∈ flipOrder D.R.m, (locGrid ch.G A.μ0 w).rank (x.1 + 1, x.2 + 1) ≤ 2 * bigN D ∧ CondLE (unifAt w) (depthAt ch.G w) ((locGrid ch.G A.μ0 w).nu x.1 x.2) ∧ ¬ IsUnram ((locGrid ch.G A.μ0 w).nu x.1 x.2) ∧ ∀ u, Un D.what₂.embLL σ ((locGrid ch.G A.μ0 w).nu x.1 x.2 u : ℂ)`. Introduce `x hx`. Simplify using `only [flipOrder, List.mem_flatMap, List.mem_map, List.mem_range] at hx`.

Take `⟨i, hi, j, hj, rfl⟩` from `hx`. Establish `hs` using `hg.square i hi j hj`. Establish `e` using `(locGrid ch.G A.μ0 w).alpha_div_beta i j`. Conclude with `⟨local_grid_rank_le _ _ hi hj, by rw [← e]; exact hs.condν, by rw [← e]; exact hs.ram, local_grid_entries_unitary _ w hmu hxi hchi hi hj⟩`. Establish `key` using `sz_flips h00.unif h00.cond h00.one_le habs hψ (2 * bigN D) (flipOrder D.R.m) (givenStage A.μ0 w ch.S.B Φ) 1 hν (canFlip_flipOrder _).1 (fun X => ⟨(GivenAdm.givenLevel_open hL hw X).1, (GivenAdm.givenLevel_open hL hw X).2, congruence_le_given_level hL hw he X⟩) hadm.tensor (UpperT …`.

Use `key.mono ?_` and prove the remaining obligations. Rewrite using `[mul_one, (canFlip_flipOrder _).2.1, ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.ResCardPlace.resCard_Kw, he, ← Real.exp_log (pow_pos (by exact_mod_cast Nat.pos_of_ne_zero hq0) _), Real.log_pow, Real.exp_le_exp]`. Establish `h1` using `ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.log_absNorm_le w`. Establish `h2` using `placeSz_nonneg ch.G w`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem _root_.GlobalTheory.T.local_character_power_conductor_bound : _root_.GlobalTheory.FunPr.ThetaLocalInputs → BigC fun _ ch C _ => FlipAt ch C := by
  refine fun _ => ⟨0, fun CF _ => ⟨48, fun ε C hC => ⟨0, ?_⟩⟩⟩
  intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch _ hF σ Φ w₀ z
  obtain ⟨w, hw⟩ := w₀
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  have hL : R.toLevCh.Is A.μ0 := hS.core.lev
  have hde := GlobalTheory.FlipIntegrand.pde_ne_q_of_setting hS
  have hc : ∀ P ∈ R.toLevCh.Q A.μ0, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := hch.guard A.μ0
  have hg := (Good.locGrid_isGood hL ch.G ch.W A.μ0 hde hc).1 w hw
  have hadm := GivenAdm.givenStage_isAdmissible hL ch.S.B A.μ0 Φ hw
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have h00 := hg.square 0 hm 0 hm
  have hW : w ∈ ch.G.pl.W0 := (GivenAdm.mem_locPl.1 hw).resolve_right fun h =>
    (hL.Q_ram A.μ0 w).2 (.inl h) (by rw [hL.xi_base]; exact fun _ _ => rfl)
  have he : depthAt ch.G w = cosExp ch.G w := by
    obtain ⟨h1, h2⟩ := GivenAdm.under_mem_and_place_above_eq_of_mem hW
    have := depthAt_w ch.G h1
    rw [h2] at this
    rw [this.1, this.2]
  have hmu : ∀ j x, Un D.what₂.embLL σ ((R.toLevCh.C.mu0 j).loc w x : ℂ) := fun j x => by
    obtain ⟨n, -, hn⟩ := (R.toLevCh.C.isMu0 j).inf
    exact UpperTheory.conjSize_heckeChar_local_of_mem_range_embedding _ _ _ _ hn _ _ _ _ (hF.chars.mu0 j w x)
  have hxi : ∀ x, Un D.what₂.embLL σ ((R.toLevCh.xiH A.μ0).loc w x : ℂ) := fun x => by
    rw [hL.xi_base]; exact Un.one
  have hchi : ∀ i, 1 ≤ i → i ≤ D.R.m → ∀ x, Un D.what₂.embLL σ ((ch.G.ch.chiH i).loc w x : ℂ) :=
    fun i a b x => UpperTheory.conjSize_heckeChar_local_of_mem_range_embedding _ _ _ _ (ch.G.ch.inf i a b) _ _ _ _ (hF.chars.chi i a b w x)
  have habs : ∀ u : (Kw w)ˣ, apow u (1 / 2) ∈ Set.range D.what₂.embLL := fun u =>
    RingHom.mem_fieldRange.1 (GlobalTheory.TflipField.apow_half_mem D.what₂.embLL.fieldRange w
      (RingHom.mem_fieldRange.2 (hF.sqrt w (.inr ⟨A.μ0, hw⟩))) u)
  have hq0 : Ideal.absNorm w.asIdeal ≠ 0 := fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have hψ := fun x hx => (fun h => Un.of_pow_eq_one (τ := σ) (hF.roots A.μ0 w hw _ h) (pow_ne_zero _ hq0) h)
    (additive_character_pow_conductor (W := ch.W) h00.cond (depthAt ch.G w) x hx)
  have hν : ∀ x ∈ flipOrder D.R.m, (locGrid ch.G A.μ0 w).rank (x.1 + 1, x.2 + 1) ≤ 2 * bigN D ∧
      CondLE (unifAt w) (depthAt ch.G w) ((locGrid ch.G A.μ0 w).nu x.1 x.2) ∧
      ¬ IsUnram ((locGrid ch.G A.μ0 w).nu x.1 x.2) ∧ ∀ u, Un D.what₂.embLL σ ((locGrid ch.G A.μ0 w).nu x.1 x.2 u : ℂ) := by
    intro x hx
    simp only [flipOrder, List.mem_flatMap, List.mem_map, List.mem_range] at hx
    obtain ⟨i, hi, j, hj, rfl⟩ := hx
    have hs := hg.square i hi j hj
    have e := (locGrid ch.G A.μ0 w).alpha_div_beta i j
    exact ⟨local_grid_rank_le _ _ hi hj, by rw [← e]; exact hs.condν, by rw [← e]; exact hs.ram, local_grid_entries_unitary _ w hmu hxi hchi hi hj⟩
  have key := sz_flips h00.unif h00.cond h00.one_le habs hψ (2 * bigN D) (flipOrder D.R.m)
    (givenStage A.μ0 w ch.S.B Φ) 1 hν (canFlip_flipOrder _).1
    (fun X => ⟨(GivenAdm.givenLevel_open hL hw X).1, (GivenAdm.givenLevel_open hL hw X).2, congruence_le_given_level hL hw he X⟩)
    hadm.tensor (UpperTheory.localGrid_tensor_size_le_one_of_unimodular _ _ ch.S.B A.μ0 Φ w hmu hxi) z
  refine key.mono ?_
  rw [mul_one, (canFlip_flipOrder _).2.1, ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.ResCardPlace.resCard_Kw, he,
    ← Real.exp_log (pow_pos (by exact_mod_cast Nat.pos_of_ne_zero hq0) _), Real.log_pow, Real.exp_le_exp]
  have h1 := ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.log_absNorm_le w
  have h2 := placeSz_nonneg ch.G w
  calc _ ≤ ((6 * cosExp ch.G w * (2 * bigN D) ^ 2 * D.R.m ^ 2 : ℕ) : ℝ) *
        (2 * Real.log (Ideal.absNorm (w.under (𝓞 D.host.F)).asIdeal)) := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
    _ = 48 * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * placeSz ch.G w := by rw [placeSz]; push_cast; ring
    _ ≤ _ := by gcongr
end
