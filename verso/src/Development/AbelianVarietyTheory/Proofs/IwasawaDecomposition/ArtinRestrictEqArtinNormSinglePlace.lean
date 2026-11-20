import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocUnitApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsoluteGaloisAbelianizationEqOneOfMemOpenSubgroStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RestrictScalarsHomContinuousKrullStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProdIdeleCharGlobalUnitEqOneStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenIdeleSubgroupContainsCongruenceUnitsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormCloseToOneOfCloseAbovePlaceStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharacterGlobalArtinUnitsTrivialUniformiserPowerStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProdLocalValuesGlobalOverPlacesAboveStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsApproxFinitePlacesNumberFieldTargetStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinsetPlacesOverFinsetPlacesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsTotallyComplexOfAlgebraOfIsTotallyComplexStatement

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat

namespace GlobalTheory.NormCompat

/- English proof (translation)
Establish `hv : w.valuation K c ≠ 0` using `(Valuation.ne_zero_iff _).mpr hc`. Rewrite using `[div_sub_one hc, map_div₀, ← WithZero.exp_log hv, div_le_iff₀ (by simp), ← WithZero.exp_add]`. Use `h.trans (WithZero.exp_le_exp.mpr ?_)` and prove the remaining obligations. Establish `: -(m : ℤ) ≤ WithZero.log (w.valuation K c)` using `by omega`. Use linear arithmetic over natural numbers and integers.
-/
theorem val_div_sub_one_le {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {a c : K}
    (hc : c ≠ 0) {N m : ℕ} (hm : (WithZero.log (w.valuation K c)).natAbs ≤ m)
    (h : w.valuation K (a - c) ≤ WithZero.exp (-((N : ℤ) + m))) :
    w.valuation K (a / c - 1) ≤ WithZero.exp (-(N : ℤ)) := by
  have hv : w.valuation K c ≠ 0 := (Valuation.ne_zero_iff _).mpr hc
  rw [div_sub_one hc, map_div₀, ← WithZero.exp_log hv, div_le_iff₀ (by simp), ← WithZero.exp_add]
  refine h.trans (WithZero.exp_le_exp.mpr ?_)
  have : -(m : ℤ) ≤ WithZero.log (w.valuation K c) := by omega
  omega

/- English proof (translation)
The claim follows from `h.trans (WithZero.exp_le_exp.mpr (by omega))`.
-/
theorem val_le_of_le {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {x : K} {N N' : ℤ}
    (h : w.valuation K x ≤ WithZero.exp (-N)) (hN : N' ≤ N) : w.valuation K x ≤ WithZero.exp (-N') :=
  h.trans (WithZero.exp_le_exp.mpr (by omega))

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ _ K _ _ _ art artK ha haK v W hW hWu y τ hτ`. Use `haveI : IsTotallyComplex K := GlobalTheory.T.isTotallyComplex_of_algebra_of_isTotallyComplex E K`. Use `haveI : IsClosed ((commutator (G E Ω)).topologicalClosure : Set (G E Ω)) := Subgroup.isClosed_topologicalClosure _`. Set `r : G K Ω →* Gab E Ω` to `(toAb E Ω).comp (AlgEquiv.restrictScalarsHom E)`. Establish `hr : Continuous r` using `QuotientGroup.continuous_mk.comp (GlobalTheory.T.continuous_restrictScalarsHom' E Ω K)`.

Set `ρ : Gab K Ω →* Gab E Ω` to `liftAb r hr`. Establish `hρ : ∀ σ : G K Ω, ρ (toAb K Ω σ) = toAb E Ω (σ.restrictScalars E)` using `fun σ => rfl`. Establish `hρc : Continuous ρ` using `continuous_liftAb r hr`. Set `NK : Kˣ →* Eˣ` to `Units.map (Algebra.norm E (S := K))`. Establish `hdE : ∀ k : Eˣ, art (diagUnits E k) = 1` using `fun k => by`.

Establish `hk : diagUnits E k ∈ art.ker`. Rewrite using `[ha.ker]`. Conclude with `Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_left ⟨k, rfl⟩)`. Conclude with `hk`. Establish `hdK : ∀ k : Kˣ, artK (diagUnits K k) = 1` using `fun k => by`.

Establish `hk : diagUnits K k ∈ artK.ker`. Rewrite using `[haK.ker]`. Conclude with `Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_left ⟨k, rfl⟩)`. Conclude with `hk`. Use `show toAb E Ω (τ.restrictScalars E) = art (locUnit E v (NK y))`.

Rewrite using `[← hρ, hτ]`. Express the relevant statement in the definitionally equal form `ρ (artK (locUnit K W y)) = art (locUnit E v (NK y))`. Rewrite using `[← div_eq_one]`. Use `GlobalTheory.T.absoluteGaloisAbelianization_eq_one_of_mem_open_subgroups E Ω _ fun U hU => ?_` and prove the remaining obligations. Set `χ : Gab E Ω →* Gab E Ω ⧸ U` to `QuotientGroup.mk' U`.

It suffices to establish `h : χ (ρ (artK (locUnit K W y))) = χ (art (locUnit E v (NK y))) by`. Establish `h2 : χ (ρ (artK (locUnit K W y)) / art (locUnit E v (NK y))) = 1`. Rewrite using `[map_div, h, div_self']`. Conclude with `(QuotientGroup.eq_one_iff _).mp h2`. Set `ψ1 : Ideles K →* Gab E Ω ⧸ U` to `χ.comp (ρ.comp artK)`.

Set `ψ2 : Ideles E →* Gab E Ω ⧸ U` to `χ.comp art`. Establish `hker1 : (ψ1.ker : Set (Ideles K)) = (ρ.comp artK) ⁻¹' U`. Use extensionality with `x`. Simplify using `[ψ1, χ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]`. Establish `hker2 : (ψ2.ker : Set (Ideles E)) = art ⁻¹' U`.

Use extensionality with `x`. Simplify using `[ψ2, χ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]`. Establish `ho1 : IsOpen (ψ1.ker : Set (Ideles K))`. Rewrite using `[hker1]`. Conclude with `hU.preimage (hρc.comp haK.quot.continuous)`.

Establish `ho2 : IsOpen (ψ2.ker : Set (Ideles E))`. Rewrite using `[hker2]`. Conclude with `hU.preimage ha.quot.continuous`. Take `⟨SE, ME, hvS, hSu, hSc⟩` from `GlobalTheory.T.isOpen_idele_subgroup_contains_congruence_units E ψ2.ker ho2 {v}`. Establish `hvSE : v ∈ SE` using `hvS (Finset.mem_singleton_self v)`.

Take `⟨TSK, hTSK⟩` from `GlobalTheory.T.exists_finset_places_over_finset_places E K SE`. Establish `hWT : W ∈ TSK` using `(hTSK W).mpr ⟨v, hvSE, hW⟩`. Take `⟨MainNotions, MK, hTS, -, hSKc⟩` from `GlobalTheory.T.isOpen_idele_subgroup_contains_congruence_units K ψ1.ker ho1 TSK`. Use `choose M' hM' using fun v' : HeightOneSpectrum (𝓞 E) => GlobalTheory.T.norm_close_to_one_of_close_above_place E K v' ME`. Set `M'' : ℕ` to `SE.sup M'`.

Set `m : ℕ` to `(WithZero.log (W.valuation K (y : K))).natAbs`. Take `⟨a, ha'⟩` from `GlobalTheory.T.exists_approx_finite_places_numberField_target K TSK (fun w => if w = W then (y : K) else 1) (MK + M'' + m + 1)`. Establish `haW : W.valuation K (a - y) ≤ WithZero.exp (-(((MK + M'' + 1 : ℕ) : ℤ) + m))`. Use `ha' W hWT` as an intermediate fact. Rewrite `this` using `[if_pos rfl]`.

Conclude with `val_le_of_le W this (by push_cast; omega)`. Establish `hz : W.valuation K (a / y - 1) ≤ WithZero.exp (-((MK + M'' + 1 : ℕ) : ℤ))` using `val_div_sub_one_le W y.ne_zero le_rfl haW`. Establish `ha0 : a ≠ 0`. Introduce and unpack `rfl`. Rewrite `hz` using `[zero_div, zero_sub, Valuation.map_neg, map_one, ← WithZero.exp_zero, WithZero.exp_le_exp]`.

Use linear arithmetic over natural numbers and integers. Set `au : Kˣ` to `Units.mk0 a ha0`. Set `zu : Kˣ` to `au / y`. Establish `hzu : (zu : K) = a / y` using `by simp [zu, au]`. Establish `hauy : au = y * zu` using `by simp [zu]`.

Establish `F1 : ψ1 (locUnit K W au) = ψ1 (locUnit K W y)`. Establish `hm : locUnit K W zu ∈ ψ1.ker` using `hSKc W (hTS hWT) zu (by`. Rewrite using `[hzu]; exact val_le_of_le W hz (by push_cast; omega))`. Rewrite using `[hauy, map_mul, map_mul, MonoidHom.mem_ker.mp hm, mul_one]`. Establish `F2 : ψ2 (locUnit E v (NK au)) = ψ2 (locUnit E v (NK y))`.

Establish `hm : locUnit E v (NK zu) ∈ ψ2.ker` using `hSc v hvSE (NK zu) (by`. Use `hM' v (zu : K) fun w hw => ?_` and prove the remaining obligations. Rewrite using `[hWu w hw, hzu]`. Conclude with `val_le_of_le W hz (by`. Establish `: M' v ≤ M''` using `Finset.le_sup hvSE`.

Use `push_cast`. Use the proof step `omega))`. Rewrite using `[hauy, map_mul, map_mul, map_mul, MonoidHom.mem_ker.mp hm, mul_one]`. Establish `F3 : ∀ w ∈ TSK, w ≠ W → ψ1 (locUnit K w au) = 1` using `fun w hw hne => by`. Use `ha' w hw` as an intermediate fact.

Rewrite `this` using `[if_neg hne]`. Conclude with `MonoidHom.mem_ker.mp (hSKc w (hTS hw) au (val_le_of_le w this (by push_cast; omega)))`. Establish `F4 : ∀ v' ∈ SE, v' ≠ v → ψ2 (locUnit E v' (NK au)) = 1` using `fun v' hv' hne => by`. Use `MonoidHom.mem_ker.mp (hSc v' hv' (NK au) ?_)` and prove the remaining obligations. Use `hM' v' (au : K) fun w hw => ?_` and prove the remaining obligations.

Establish `hwT : w ∈ TSK` using `(hTSK w).mpr ⟨v', hv', hw⟩`. Establish `hwW : w ≠ W`. Introduce and unpack `rfl`. Conclude with `hne (HeightOneSpectrum.ext (hw.symm.trans hW))`. Use `ha' w hwT` as an intermediate fact.

Rewrite `this` using `[if_neg hwW]`. Conclude with `val_le_of_le w this (by`. Establish `: M' v' ≤ M''` using `Finset.le_sup hv'`. Use `push_cast`. Use the proof step `omega)`.

Establish `hunitE : ∀ v' ∉ SE, ∀ x, IsUnitAt v' x → ψ2 (localIdele E v' x) = 1` using `fun v' hv' x hx => MonoidHom.mem_ker.mp (hSu v' hv' x hx)`. Establish `hchi` using `fun (v' : HeightOneSpectrum (𝓞 E)) (hv' : v' ∉ SE) (w : HeightOneSpectrum (𝓞 K)) (hw : w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v'.asIdeal) => GlobalTheory.T.character_globalArtin_units_trivial_uniformiser_power E Ω K art artK ha haK ρ hρ (Gab E Ω ⧸ U) χ v' w hw (hunitE v' hv')`. Take `⟨TK, TE, hTK1, hTK2, hTE1, hTE2, hprod⟩` from `GlobalTheory.T.prod_localValues_global_over_places_above E K (Gab E Ω ⧸ U) ψ1 ψ2 SE hunitE (fun v' hv' w hw => (hchi v' hv' w hw).1) (fun v' hv' w hw => (hchi v' hv' w hw).2) au`. Establish `hPK : (∏ w ∈ TK, ψ1 (locUnit K w au)) * ψ1 (locUnit K W au) = 1`. Establish `hdisj : Disjoint TK TSK`.

Rewrite using `[Finset.disjoint_left]`. Introduce `w h1 h2`. Take `⟨v', hv', e⟩` from `(hTSK w).mp h2`. Conclude with `hTK1 w h1 v' hv' e`. Establish `h` using `GlobalTheory.T.prod_idele_char_global_unit_eq_one K (Gab E Ω ⧸ U) ψ1 ho1 (fun k => by simp [ψ1, hdK]) au (TK ∪ TSK) fun w hw => by`.

Rewrite `hw` using `[Finset.mem_union, not_or]`. Use `hTK2 w hw.1 fun v' hv' e => hw.2 ((hTSK w).mpr ⟨v', hv', e⟩)` and prove the remaining obligations. Rewrite `h` using `[Finset.prod_union hdisj, Finset.prod_eq_single_of_mem W hWT F3]`. Conclude with `h`. Establish `hPE : (∏ v' ∈ TE, ψ2 (locUnit E v' (NK au))) * ψ2 (locUnit E v (NK au)) = 1`.

Establish `hdisj : Disjoint TE SE`. Rewrite using `[Finset.disjoint_left]`. Introduce `v' h1 h2`. Conclude with `hTE1 v' h1 h2`. Establish `h` using `GlobalTheory.T.prod_idele_char_global_unit_eq_one E (Gab E Ω ⧸ U) ψ2 ho2 (fun k => by simp [ψ2, hdE]) (NK au) (TE ∪ SE) fun v' hv' => by`.

Rewrite `hv'` using `[Finset.mem_union, not_or]`. Conclude with `hTE2 v' hv'.1 hv'.2`. Rewrite `h` using `[Finset.prod_union hdisj, Finset.prod_eq_single_of_mem v hvSE F4]`. Conclude with `h`. Establish `key : ψ1 (locUnit K W au) = ψ2 (locUnit E v (NK au))`.

Rewrite `hPE` using `[← hprod]`. Conclude with `mul_left_cancel (hPK.trans hPE.symm)`. Use `show ψ1 (locUnit K W y) = ψ2 (locUnit E v (NK y))`. Rewrite using `[← F1, key, F2]`.
-/
theorem res_art_eq_art_norm : ∀ (E Ω : Type) [Field E] [NumberField E] [IsTotallyComplex E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (K : IntermediateField E Ω) [FiniteDimensional E K] [NumberField K] [IsAlgClosure K Ω]
    (art : Ideles E →* Gab E Ω) (artK : Ideles K →* Gab K Ω), IsGlobalArtin art → IsGlobalArtin artK →
    ∀ (v : HeightOneSpectrum (𝓞 E)) (W : HeightOneSpectrum (𝓞 K)),
      W.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal →
      (∀ W' : HeightOneSpectrum (𝓞 K), W'.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal → W' = W) →
      ∀ (y : Kˣ) (τ : G K Ω),
        toAb K Ω τ = artK (localIdele K W (Units.map (algebraMap K (W.adicCompletion K)).toMonoidHom y)) →
        toAb E Ω (τ.restrictScalars E) =
          art (localIdele E v (Units.map (algebraMap E (v.adicCompletion E)).toMonoidHom
            (Units.map (Algebra.norm E (S := K)) y))) := by
  intro E Ω _ _ _ _ _ _ K _ _ _ art artK ha haK v W hW hWu y τ hτ
  classical
  haveI : IsTotallyComplex K := GlobalTheory.T.isTotallyComplex_of_algebra_of_isTotallyComplex E K
  haveI : IsClosed ((commutator (G E Ω)).topologicalClosure : Set (G E Ω)) :=
    Subgroup.isClosed_topologicalClosure _
  let r : G K Ω →* Gab E Ω := (toAb E Ω).comp (AlgEquiv.restrictScalarsHom E)
  have hr : Continuous r := QuotientGroup.continuous_mk.comp (GlobalTheory.T.continuous_restrictScalarsHom' E Ω K)
  let ρ : Gab K Ω →* Gab E Ω := liftAb r hr
  have hρ : ∀ σ : G K Ω, ρ (toAb K Ω σ) = toAb E Ω (σ.restrictScalars E) := fun σ => rfl
  have hρc : Continuous ρ := continuous_liftAb r hr
  let NK : Kˣ →* Eˣ := Units.map (Algebra.norm E (S := K))
  have hdE : ∀ k : Eˣ, art (diagUnits E k) = 1 := fun k => by
    have hk : diagUnits E k ∈ art.ker := by
      rw [ha.ker]
      exact Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_left ⟨k, rfl⟩)
    exact hk
  have hdK : ∀ k : Kˣ, artK (diagUnits K k) = 1 := fun k => by
    have hk : diagUnits K k ∈ artK.ker := by
      rw [haK.ker]
      exact Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_left ⟨k, rfl⟩)
    exact hk
  show toAb E Ω (τ.restrictScalars E) = art (locUnit E v (NK y))
  rw [← hρ, hτ]
  change ρ (artK (locUnit K W y)) = art (locUnit E v (NK y))
  rw [← div_eq_one]
  refine GlobalTheory.T.absoluteGaloisAbelianization_eq_one_of_mem_open_subgroups E Ω _ fun U hU => ?_
  let χ : Gab E Ω →* Gab E Ω ⧸ U := QuotientGroup.mk' U
  suffices h : χ (ρ (artK (locUnit K W y))) = χ (art (locUnit E v (NK y))) by
    have h2 : χ (ρ (artK (locUnit K W y)) / art (locUnit E v (NK y))) = 1 := by
      rw [map_div, h, div_self']
    exact (QuotientGroup.eq_one_iff _).mp h2
  let ψ1 : Ideles K →* Gab E Ω ⧸ U := χ.comp (ρ.comp artK)
  let ψ2 : Ideles E →* Gab E Ω ⧸ U := χ.comp art
  have hker1 : (ψ1.ker : Set (Ideles K)) = (ρ.comp artK) ⁻¹' U := by
    ext x; simp [ψ1, χ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  have hker2 : (ψ2.ker : Set (Ideles E)) = art ⁻¹' U := by
    ext x; simp [ψ2, χ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  have ho1 : IsOpen (ψ1.ker : Set (Ideles K)) := by
    rw [hker1]; exact hU.preimage (hρc.comp haK.quot.continuous)
  have ho2 : IsOpen (ψ2.ker : Set (Ideles E)) := by
    rw [hker2]; exact hU.preimage ha.quot.continuous

  obtain ⟨SE, ME, hvS, hSu, hSc⟩ := GlobalTheory.T.isOpen_idele_subgroup_contains_congruence_units E ψ2.ker ho2 {v}
  have hvSE : v ∈ SE := hvS (Finset.mem_singleton_self v)
  obtain ⟨TSK, hTSK⟩ := GlobalTheory.T.exists_finset_places_over_finset_places E K SE
  have hWT : W ∈ TSK := (hTSK W).mpr ⟨v, hvSE, hW⟩
  obtain ⟨MainNotions, MK, hTS, -, hSKc⟩ := GlobalTheory.T.isOpen_idele_subgroup_contains_congruence_units K ψ1.ker ho1 TSK
  choose M' hM' using fun v' : HeightOneSpectrum (𝓞 E) => GlobalTheory.T.norm_close_to_one_of_close_above_place E K v' ME
  let M'' : ℕ := SE.sup M'
  let m : ℕ := (WithZero.log (W.valuation K (y : K))).natAbs
  obtain ⟨a, ha'⟩ := GlobalTheory.T.exists_approx_finite_places_numberField_target K TSK (fun w => if w = W then (y : K) else 1) (MK + M'' + m + 1)
  have haW : W.valuation K (a - y) ≤ WithZero.exp (-(((MK + M'' + 1 : ℕ) : ℤ) + m)) := by
    have := ha' W hWT
    rw [if_pos rfl] at this
    exact val_le_of_le W this (by push_cast; omega)
  have hz : W.valuation K (a / y - 1) ≤ WithZero.exp (-((MK + M'' + 1 : ℕ) : ℤ)) :=
    val_div_sub_one_le W y.ne_zero le_rfl haW
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_div, zero_sub, Valuation.map_neg, map_one, ← WithZero.exp_zero, WithZero.exp_le_exp] at hz
    omega
  let au : Kˣ := Units.mk0 a ha0
  let zu : Kˣ := au / y
  have hzu : (zu : K) = a / y := by simp [zu, au]
  have hauy : au = y * zu := by simp [zu]

  have F1 : ψ1 (locUnit K W au) = ψ1 (locUnit K W y) := by
    have hm : locUnit K W zu ∈ ψ1.ker := hSKc W (hTS hWT) zu (by
      rw [hzu]; exact val_le_of_le W hz (by push_cast; omega))
    rw [hauy, map_mul, map_mul, MonoidHom.mem_ker.mp hm, mul_one]

  have F2 : ψ2 (locUnit E v (NK au)) = ψ2 (locUnit E v (NK y)) := by
    have hm : locUnit E v (NK zu) ∈ ψ2.ker := hSc v hvSE (NK zu) (by
      refine hM' v (zu : K) fun w hw => ?_
      rw [hWu w hw, hzu]
      exact val_le_of_le W hz (by
        have : M' v ≤ M'' := Finset.le_sup hvSE
        push_cast; omega))
    rw [hauy, map_mul, map_mul, map_mul, MonoidHom.mem_ker.mp hm, mul_one]

  have F3 : ∀ w ∈ TSK, w ≠ W → ψ1 (locUnit K w au) = 1 := fun w hw hne => by
    have := ha' w hw
    rw [if_neg hne] at this
    exact MonoidHom.mem_ker.mp (hSKc w (hTS hw) au (val_le_of_le w this (by push_cast; omega)))
  have F4 : ∀ v' ∈ SE, v' ≠ v → ψ2 (locUnit E v' (NK au)) = 1 := fun v' hv' hne => by
    refine MonoidHom.mem_ker.mp (hSc v' hv' (NK au) ?_)
    refine hM' v' (au : K) fun w hw => ?_
    have hwT : w ∈ TSK := (hTSK w).mpr ⟨v', hv', hw⟩
    have hwW : w ≠ W := by
      rintro rfl
      exact hne (HeightOneSpectrum.ext (hw.symm.trans hW))
    have := ha' w hwT
    rw [if_neg hwW] at this
    exact val_le_of_le w this (by
      have : M' v' ≤ M'' := Finset.le_sup hv'
      push_cast; omega)

  have hunitE : ∀ v' ∉ SE, ∀ x, IsUnitAt v' x → ψ2 (localIdele E v' x) = 1 := fun v' hv' x hx =>
    MonoidHom.mem_ker.mp (hSu v' hv' x hx)
  have hchi := fun (v' : HeightOneSpectrum (𝓞 E)) (hv' : v' ∉ SE) (w : HeightOneSpectrum (𝓞 K))
      (hw : w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v'.asIdeal) =>
    GlobalTheory.T.character_globalArtin_units_trivial_uniformiser_power E Ω K art artK ha haK ρ hρ (Gab E Ω ⧸ U) χ v' w hw (hunitE v' hv')
  obtain ⟨TK, TE, hTK1, hTK2, hTE1, hTE2, hprod⟩ := GlobalTheory.T.prod_localValues_global_over_places_above E K (Gab E Ω ⧸ U) ψ1 ψ2 SE hunitE
    (fun v' hv' w hw => (hchi v' hv' w hw).1) (fun v' hv' w hw => (hchi v' hv' w hw).2) au

  have hPK : (∏ w ∈ TK, ψ1 (locUnit K w au)) * ψ1 (locUnit K W au) = 1 := by
    have hdisj : Disjoint TK TSK := by
      rw [Finset.disjoint_left]
      intro w h1 h2
      obtain ⟨v', hv', e⟩ := (hTSK w).mp h2
      exact hTK1 w h1 v' hv' e
    have h := GlobalTheory.T.prod_idele_char_global_unit_eq_one K (Gab E Ω ⧸ U) ψ1 ho1 (fun k => by simp [ψ1, hdK]) au (TK ∪ TSK) fun w hw => by
      rw [Finset.mem_union, not_or] at hw
      refine hTK2 w hw.1 fun v' hv' e => hw.2 ((hTSK w).mpr ⟨v', hv', e⟩)
    rw [Finset.prod_union hdisj, Finset.prod_eq_single_of_mem W hWT F3] at h
    exact h
  have hPE : (∏ v' ∈ TE, ψ2 (locUnit E v' (NK au))) * ψ2 (locUnit E v (NK au)) = 1 := by
    have hdisj : Disjoint TE SE := by
      rw [Finset.disjoint_left]
      intro v' h1 h2
      exact hTE1 v' h1 h2
    have h := GlobalTheory.T.prod_idele_char_global_unit_eq_one E (Gab E Ω ⧸ U) ψ2 ho2 (fun k => by simp [ψ2, hdE]) (NK au) (TE ∪ SE) fun v' hv' => by
      rw [Finset.mem_union, not_or] at hv'
      exact hTE2 v' hv'.1 hv'.2
    rw [Finset.prod_union hdisj, Finset.prod_eq_single_of_mem v hvSE F4] at h
    exact h
  have key : ψ1 (locUnit K W au) = ψ2 (locUnit E v (NK au)) := by
    rw [← hprod] at hPE
    exact mul_left_cancel (hPK.trans hPE.symm)
  show ψ1 (locUnit K W y) = ψ2 (locUnit E v (NK y))
  rw [← F1, key, F2]

end GlobalTheory.NormCompat
