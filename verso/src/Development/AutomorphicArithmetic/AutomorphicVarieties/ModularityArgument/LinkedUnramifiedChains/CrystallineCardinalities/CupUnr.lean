import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CocycleTransportH1fSurjective
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsCrField
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.OpenField
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsIntBasis
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CharFil
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FrobFree
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FrobCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsCrIff

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Topology UpperTheory.V UpperTheory.V.Loc
open TensorProduct Module

/- English proof (translation)
Take `⟨σ, hσ, -⟩` from `frobCyc l`. Take `⟨f, hf, hI, h1⟩` from `frobFree σ hσ (Multiplicative ℤ_[l]) (Multiplicative.ofAdd 1)`. Use `⟨fun s => ((Multiplicative.toAdd (f s) : ℤ_[l]) : ℚ_[l]), σ, ?_, fun s s' => by simp, fun s hs => ?_, fun n hn => ?_⟩` and prove the remaining obligations. Conclude with `continuous_subtype_val.comp (continuous_toAdd.comp hf)`. Simplify using `[hI s hs]`.

Simplify using `[h1, hn.ne']`.
-/
private theorem exists_deg (l : ℕ) [Fact l.Prime] :
    ∃ (d : GQ l → ℚ_[l]) (σ : GQ l), Continuous d ∧ (∀ s s', d (s * s') = d s + d s') ∧
      (∀ s ∈ Iq l, d s = 0) ∧ ∀ n : ℕ, 0 < n → d (σ ^ n) ≠ 0 := by
  obtain ⟨σ, hσ, -⟩ := frobCyc l
  obtain ⟨f, hf, hI, h1⟩ := frobFree σ hσ (Multiplicative ℤ_[l]) (Multiplicative.ofAdd 1)
  refine ⟨fun s => ((Multiplicative.toAdd (f s) : ℤ_[l]) : ℚ_[l]), σ, ?_, fun s s' => by simp, fun s hs => ?_,
    fun n hn => ?_⟩
  · exact continuous_subtype_val.comp (continuous_toAdd.comp hf)
  · simp [hI s hs]
  · simp [h1, hn.ne']

section

variable {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] [TopologicalSpace E] [IsModuleTopology ℚ_[l] E]

omit [FiniteDimensional ℚ_[l] E] [TopologicalSpace E] [IsModuleTopology ℚ_[l] E] in
/- English proof (translation)
Express the relevant statement in the definitionally equal form `algebraMap ℤ_[l] E _ = algebraMap ℚ_[l] E (((PP l).PD K).χ g : ℚ_[l])`. Rewrite using `[(PP l).PD_χ, (cycFacts l l).2.2 g, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] E]`. Both sides reduce to the same expression.
-/
private theorem cyc_val (K : FinExt l) (g : ↥(GK K)) :
    (cycA l l E (g : GQ l) : E) = algebraMap ℚ_[l] E (cycLL ((PP l).PD K) ℚ_[l] g : ℚ_[l]) := by
  change algebraMap ℤ_[l] E _ = algebraMap ℚ_[l] E (((PP l).PD K).χ g : ℚ_[l])
  rw [(PP l).PD_χ, (cycFacts l l).2.2 g, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] E]
  rfl

omit [FiniteDimensional ℚ_[l] E] in
/- English proof (translation)
Establish `h1 : Continuous (algebraMap ℤ_[l] E)`. Rewrite using `[IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] E]`. Conclude with `(IsModuleTopology.continuous_of_linearMap (Algebra.linearMap ℚ_[l] E)).comp continuous_subtype_val`. Conclude with `h1.comp (Units.continuous_val.comp (cycFacts l l).1)`.
-/
private theorem cyc_cont [IsTopologicalRing E] : Continuous fun g : GQ l => (cycA l l E g : E) := by
  have h1 : Continuous (algebraMap ℤ_[l] E) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] E]
    exact (IsModuleTopology.continuous_of_linearMap (Algebra.linearMap ℚ_[l] E)).comp continuous_subtype_val
  exact h1.comp (Units.continuous_val.comp (cycFacts l l).1)

/- English proof (translation)
Use `haveI : ContinuousSMul ℚ_[l] E := IsModuleTopology.toContinuousSMul ℚ_[l] E`. Use `haveI := K.2`. Establish `hφ : IsOpenEmbedding (GK K).subtype` using `(IntermediateField.fixingSubgroup_isOpen K.1).isOpenEmbedding_subtypeVal`. Take `⟨T⟩` from `tiedP l`. Establish `hc : Continuous fun g : ↥(GK K) => (((cycA l l E).comp (GK K).subtype) g : E)` using `cyc_cont.comp continuous_subtype_val`.

Establish `hdR : IsDR ((PP l).PD K) (resCoef ℚ_[l] (chRep ((cycA l l E).comp (GK K).subtype)))` using `(isCrIff K _).2.1 (charFil _ hφ _ hc 1 ⟨⊤, isOpen_univ, fun g _ _ => (zpow_one _).symm⟩).1`. Establish `hρ : ∀ g x, resCoef ℚ_[l] (chRep ((cycA l l E).comp (GK K).subtype)) g x = (cycLL ((PP l).PD K) ℚ_[l] g : ℚ_[l]) • x` using `fun g x => by`. Rewrite using `[Algebra.smul_def, ← cyc_val]`. Both sides reduce to the same expression. Set `b` to `Module.finBasis ℚ_[l] E`.

Establish `hdual : IsDual1 ((PP l).PD K) (resCoef ℚ_[l] (chRep ((cycA l l E).comp (GK K).subtype))) (1 : Representation ℚ_[l] ↥(GK K) E) b.toDual`. Use `⟨fun g x y => ?_, fun x hx => ?_, fun y hy => ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[hρ]`. Simplify using the standard rewrite rules. Conclude with `b.toDual_inj x (LinearMap.ext hx)`.

Conclude with `b.ext_elem fun i => by rw [← b.toDual_apply_right, hy, map_zero, Finsupp.zero_apply]`. Establish `hκ' : κ ∈ Formalism.WeaklyAdmissibleFiltrations.finiteCocycles ((PP l).PD K) (resCoef ℚ_[l] (chRep ((cycA l l E).comp (GK K).subtype)))`. Rewrite using `[← (isCrField K _).2.2]`. Conclude with `hκ`. Establish `hD` using `((hP.bk l (PP l) (AIP l) T K).2.1 E E _ 1 b.toDual (fun x => hc.mul continuous_const) (fun y => continuous_const) hdR hdual).1 κ hκ'.1`.

Establish `hf : ∀ i, ∃ f : ↥(GK K) → ℚ_[l], Continuous f ∧ ∀ s s', f (s * s') = f s + (cycLL ((PP l).PD K) ℚ_[l] s : ℚ_[l]) * f s' - d s' * b.repr (κ s) i`. Introduce `i`. Establish `hz : (fun s => d s • b i) ∈ Formalism.WeaklyAdmissibleFiltrations.finiteCocycles ((PP l).PD K) (1 : Representation ℚ_[l] ↥(GK K) E)`. Rewrite using `[← (isCrField K _).2.2]`. Use `(z1fUnr hP _ hφ (1 : Representation ℚ_[l] ↥(GK K) E) continuous_snd (fun _ _ => rfl) _ ⟨hd.smul continuous_const, fun s s' => ?_⟩).2 fun s hs => ?_` and prove the remaining obligations.

Simplify using `[hadd, add_smul]`. Simplify using `[hI s hs]`. Take `⟨f, hf, h⟩` from `hD.1 hκ' _ hz`. Use `⟨f, hf, fun s s' => ?_⟩` and prove the remaining obligations. Establish `h1 : (cycLL ((PP l).PD K) ℚ_[l] s : ℚ_[l]) * f s' - f (s * s') + f s = b.toDual (κ s) (d s' • b i)` using `congrFun h (s, s')`.

Rewrite `h1` using `[map_smul, b.toDual_apply_left, smul_eq_mul]`. Take the linear combination `-h1`. Use `choose f hf hff using hf`. Use `⟨fun s => ∑ i, f i s • b i, continuous_finset_sum _ fun i _ => (hf i).smul continuous_const, fun s s' => ?_⟩` and prove the remaining obligations. Rewrite using `[cyc_val, ← Algebra.smul_def]`.

Use `conv_rhs => rw [← b.sum_repr (κ s)]`. Simplify using `only [Finset.smul_sum, smul_smul, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← add_smul, ← sub_smul, hff]`.
-/
private theorem gk_case [IsTopologicalRing E] (hP : LocalPublishedTheorems) (K : FinExt l) (κ : ↥(GK K) → E)
    (hκ : κ ∈ UpperTheory.V.Loc.finiteCocycles (GK K).subtype (chRep ((cycA l l E).comp (GK K).subtype)))
    (d : ↥(GK K) → ℚ_[l]) (hd : Continuous d) (hadd : ∀ s s', d (s * s') = d s + d s')
    (hI : ∀ s : ↥(GK K), (s : GQ l) ∈ Iq l → d s = 0) :
    ∃ β : ↥(GK K) → E, Continuous β ∧
      ∀ s s', β (s * s') = β s + (cycA l l E (s : GQ l) : E) * β s' - d s' • κ s := by
  classical
  haveI : ContinuousSMul ℚ_[l] E := IsModuleTopology.toContinuousSMul ℚ_[l] E
  haveI := K.2
  have hφ : IsOpenEmbedding (GK K).subtype :=
    (IntermediateField.fixingSubgroup_isOpen K.1).isOpenEmbedding_subtypeVal
  obtain ⟨T⟩ := tiedP l
  have hc : Continuous fun g : ↥(GK K) => (((cycA l l E).comp (GK K).subtype) g : E) :=
    cyc_cont.comp continuous_subtype_val
  have hdR : IsDR ((PP l).PD K) (resCoef ℚ_[l] (chRep ((cycA l l E).comp (GK K).subtype))) :=
    (isCrIff K _).2.1 (charFil _ hφ _ hc 1 ⟨⊤, isOpen_univ, fun g _ _ => (zpow_one _).symm⟩).1
  have hρ : ∀ g x, resCoef ℚ_[l] (chRep ((cycA l l E).comp (GK K).subtype)) g x =
      (cycLL ((PP l).PD K) ℚ_[l] g : ℚ_[l]) • x := fun g x => by
    rw [Algebra.smul_def, ← cyc_val]
    rfl
  let b := Module.finBasis ℚ_[l] E
  have hdual : IsDual1 ((PP l).PD K) (resCoef ℚ_[l] (chRep ((cycA l l E).comp (GK K).subtype)))
      (1 : Representation ℚ_[l] ↥(GK K) E) b.toDual := by
    refine ⟨fun g x y => ?_, fun x hx => ?_, fun y hy => ?_, rfl⟩
    · rw [hρ]
      simp
    · exact b.toDual_inj x (LinearMap.ext hx)
    · exact b.ext_elem fun i => by rw [← b.toDual_apply_right, hy, map_zero, Finsupp.zero_apply]
  have hκ' : κ ∈ Formalism.WeaklyAdmissibleFiltrations.finiteCocycles ((PP l).PD K) (resCoef ℚ_[l] (chRep ((cycA l l E).comp (GK K).subtype))) := by
    rw [← (isCrField K _).2.2]
    exact hκ
  have hD := ((hP.bk l (PP l) (AIP l) T K).2.1 E E _ 1 b.toDual
    (fun x => hc.mul continuous_const) (fun y => continuous_const) hdR hdual).1 κ hκ'.1
  have hf : ∀ i, ∃ f : ↥(GK K) → ℚ_[l], Continuous f ∧ ∀ s s', f (s * s') =
      f s + (cycLL ((PP l).PD K) ℚ_[l] s : ℚ_[l]) * f s' - d s' * b.repr (κ s) i := by
    intro i
    have hz : (fun s => d s • b i) ∈ Formalism.WeaklyAdmissibleFiltrations.finiteCocycles ((PP l).PD K) (1 : Representation ℚ_[l] ↥(GK K) E) := by
      rw [← (isCrField K _).2.2]
      refine (z1fUnr hP _ hφ (1 : Representation ℚ_[l] ↥(GK K) E) continuous_snd (fun _ _ => rfl) _
        ⟨hd.smul continuous_const, fun s s' => ?_⟩).2 fun s hs => ?_
      · simp [hadd, add_smul]
      · simp [hI s hs]
    obtain ⟨f, hf, h⟩ := hD.1 hκ' _ hz
    refine ⟨f, hf, fun s s' => ?_⟩
    have h1 : (cycLL ((PP l).PD K) ℚ_[l] s : ℚ_[l]) * f s' - f (s * s') + f s =
      b.toDual (κ s) (d s' • b i) := congrFun h (s, s')
    rw [map_smul, b.toDual_apply_left, smul_eq_mul] at h1
    linear_combination -h1
  choose f hf hff using hf
  refine ⟨fun s => ∑ i, f i s • b i, continuous_finset_sum _ fun i _ => (hf i).smul continuous_const,
    fun s s' => ?_⟩
  rw [cyc_val, ← Algebra.smul_def]
  conv_rhs => rw [← b.sum_repr (κ s)]
  simp only [Finset.smul_sum, smul_smul, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← add_smul,
    ← sub_smul, hff]

end

/- English proof (translation)
Introduce `hP l _ G _ _ _ φ hφ E _ _ _ _ _ _ _ _ κ hκ`. Take `⟨K, e, he, he', hφe, -, hind, -⟩` from `openField φ hφ`. Take `⟨d, σ, hd, hadd, hI, hσ⟩` from `exists_deg l`. Establish `hφ1 : ∀ g, ((e g : ↥(GK K)) : GQ l) = φ g` using `fun g => DFunLike.congr_fun hφe g`. Establish `hφ' : ∀ g : ↥(GK K), φ (e.symm g) = g` using `fun g => by rw [← hφ1, e.apply_symm_apply]`.

Take `⟨⟨hκ1, hκ2⟩, x, hx⟩` from `hκ`. Take `⟨β, hβ, hβ'⟩` from `gk_case hP K (κ ∘ e.symm) ⟨⟨hκ1.comp he', fun g h => by`. Use `hκ2 (e.symm g) (e.symm h)` as an intermediate fact. Rewrite `this` using `[← map_mul]`. Use `this.trans ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `_ + (cycA l l E (φ (e.symm g)) : E) * _ = _`. Rewrite using `[hφ']`. Use the proof step `rfl⟩, x, fun g => by`. Use `(hx (e.symm g)).trans ?_` and prove the remaining obligations. Use `congr 2`.

Unfold `actC`. Rewrite using `[hφ']`. Use `congr 1`. Use `LinearMap.ext fun y => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(cycA l l E (φ (e.symm g)) : E) * _ = _`.

Rewrite using `[hφ']`. Use the proof step `rfl⟩ (fun g => d g) (hd.comp continuous_subtype_val) (fun s s' => hadd _ _) (fun s hs => hI _ hs)`. Use `⟨fun s => algebraMap ℚ_[l] E (d (φ s)), β ∘ e, (IsModuleTopology.continuous_of_linearMap (Algebra.linearMap ℚ_[l] E)).comp (hd.comp hφ.continuous), hβ.comp he, fun s s' => by simp [hadd], fun s hs => by simp [hI _ hs], ?_, fun s s' => ?_⟩` and prove the remaining obligations. Use `haveI := K.2`. Take `⟨n, hn, -, s, hs⟩` from `Subgroup.exists_pow_mem_of_index_ne_zero (H := φ.range) (by rw [hind]; exact Module.finrank_pos.ne') σ`.

Conclude with `⟨s, by simpa [hs] using hσ n hn⟩`. Use `hβ' (e s) (e s')` as an intermediate fact. Simplify using `only [hφ1, Function.comp_apply, MulEquiv.symm_apply_apply, ← map_mul] at this`. Rewrite using `[Function.comp_apply, this, Algebra.smul_def, mul_comm (κ s)]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.V.Z.J.cupUnr :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l), IsOpenEmbedding φ → ∀ {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] [TopologicalSpace E] [IsModuleTopology ℚ_[l] E] [IsTopologicalRing E], ∀ κ ∈ UpperTheory.V.Loc.finiteCocycles φ (chRep ((cycA l l E).comp φ)), ∃ u β : G → E, Continuous u ∧ Continuous β ∧ (∀ s s', u (s * s') = u s + u s') ∧ (∀ s, φ s ∈ Iq l → u s = 0) ∧ (∃ s, u s ≠ 0) ∧ ∀ s s', β (s * s') = β s + (cycA l l E (φ s) : E) * β s' - κ s * u s' := by
  intro hP l _ G _ _ _ φ hφ E _ _ _ _ _ _ _ _ κ hκ
  obtain ⟨K, e, he, he', hφe, -, hind, -⟩ := openField φ hφ
  obtain ⟨d, σ, hd, hadd, hI, hσ⟩ := exists_deg l
  have hφ1 : ∀ g, ((e g : ↥(GK K)) : GQ l) = φ g := fun g => DFunLike.congr_fun hφe g
  have hφ' : ∀ g : ↥(GK K), φ (e.symm g) = g := fun g => by rw [← hφ1, e.apply_symm_apply]
  obtain ⟨⟨hκ1, hκ2⟩, x, hx⟩ := hκ
  obtain ⟨β, hβ, hβ'⟩ := gk_case hP K (κ ∘ e.symm) ⟨⟨hκ1.comp he', fun g h => by
      have := hκ2 (e.symm g) (e.symm h)
      rw [← map_mul] at this
      refine this.trans ?_
      change _ + (cycA l l E (φ (e.symm g)) : E) * _ = _
      rw [hφ']
      rfl⟩, x, fun g => by
      refine (hx (e.symm g)).trans ?_
      congr 2
      unfold actC
      rw [hφ']
      congr 1
      refine LinearMap.ext fun y => ?_
      change (cycA l l E (φ (e.symm g)) : E) * _ = _
      rw [hφ']
      rfl⟩ (fun g => d g) (hd.comp continuous_subtype_val) (fun s s' => hadd _ _) (fun s hs => hI _ hs)
  refine ⟨fun s => algebraMap ℚ_[l] E (d (φ s)), β ∘ e,
    (IsModuleTopology.continuous_of_linearMap (Algebra.linearMap ℚ_[l] E)).comp (hd.comp hφ.continuous),
    hβ.comp he, fun s s' => by simp [hadd], fun s hs => by simp [hI _ hs], ?_, fun s s' => ?_⟩
  · haveI := K.2
    obtain ⟨n, hn, -, s, hs⟩ := Subgroup.exists_pow_mem_of_index_ne_zero (H := φ.range)
      (by rw [hind]; exact Module.finrank_pos.ne') σ
    exact ⟨s, by simpa [hs] using hσ n hn⟩
  · have := hβ' (e s) (e s')
    simp only [hφ1, Function.comp_apply, MulEquiv.symm_apply_apply, ← map_mul] at this
    rw [Function.comp_apply, this, Algebra.smul_def, mul_comm (κ s)]
    rfl
