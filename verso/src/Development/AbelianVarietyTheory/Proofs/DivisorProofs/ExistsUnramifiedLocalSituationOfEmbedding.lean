import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.HeightTrivialParameterEqZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsNormSubEqOne
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne

set_option autoImplicit false

noncomputable section

open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace

namespace GlobalTheory.PlaceLetters

variable {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E]

/- English proof (translation)
The claim follows from `GlobalTheory.SplitEmbSep.norm_le_one_of_isIntegral (map_isIntegral_int σ b.isIntegral_coe)`.
-/
theorem norm_emb_le (σ : E →+* Om l) (b : 𝓞 E) : ‖σ (b : E)‖ ≤ 1 :=
  GlobalTheory.SplitEmbSep.norm_le_one_of_isIntegral (map_isIntegral_int σ b.isIntegral_coe)

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `hd` using `GlobalTheory.SplitEmbSep.one_le_norm_intCast (C := Om l) Fact.out GlobalTheory.PlaceBridge.norm_l_lt_one hE`. Set `b` to `integralBasis E`. Establish `e : Module.Free.ChooseBasisIndex ℤ (𝓞 E) ≃ (E →ₐ[ℚ] Om l)` using `Fintype.equivOfCardEq (by rw [AlgHom.card, Module.finrank_eq_card_basis b])`. Establish `hdet` using `Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ (Om l) b e`.

Rewrite `hdet` using `[← coe_discr, map_intCast]`. Use `set M := Algebra.embeddingsMatrixReindex ℚ (Om l) b e with hM`. Establish `hMij : ∀ i j, M i j = (e j).toRingHom ((RingOfIntegers.basis E i : 𝓞 E) : E)`. Introduce `i j`. Simplify using `[hM, b, Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix, integralBasis_apply]`.

Use `set k := e.symm τ.toRatAlgHom with hk`. Use `set k' := e.symm τ'.toRatAlgHom with hk'`. Establish `hkk : k ≠ k'` using `fun h => hne (by`. Use `e.symm.injective h` as an intermediate fact. Conclude with `RingHom.ext fun x => DFunLike.congr_fun this x)`.

Establish `hcol : ∀ i, M i k + (-1 : Om l) • M i k' = τ ((RingOfIntegers.basis E i : 𝓞 E) : E) - τ' ((RingOfIntegers.basis E i : 𝓞 E) : E)`. Introduce `i`. Rewrite using `[hMij, hMij, hk, hk', e.apply_symm_apply, e.apply_symm_apply, neg_one_smul, ← sub_eq_add_neg]`. Both sides reduce to the same expression. Establish `hlt' : ‖M.det‖ < 1`.

Rewrite using `[← Matrix.det_updateCol_add_smul_self M hkk (-1)]`. Use `GlobalTheory.SplitEmbSep.norm_det_lt_one _ (fun i j => ?_) k fun i => ?_` and prove the remaining obligations. Distinguish the cases in `hj : j = k`. Rewrite using `[hj, Matrix.updateCol_self, hcol]`. Conclude with `(hlt _).le`.

Rewrite using `[Matrix.updateCol_ne hj, hMij]`. Conclude with `norm_emb_le _ _`. Rewrite using `[Matrix.updateCol_self, hcol]`. Conclude with `hlt _`. Rewrite `hd` using `[hdet, norm_pow]`.

Conclude with `absurd (hd.trans_lt (pow_lt_one₀ (norm_nonneg _) hlt' two_ne_zero)) (lt_irrefl _)`.
-/
theorem emb_eq_of_congr (hE : ¬ (l : ℤ) ∣ discr E) (τ τ' : E →+* Om l)
    (hlt : ∀ b : 𝓞 E, ‖τ (b : E) - τ' (b : E)‖ < 1) : τ = τ' := by
  classical
  by_contra hne
  have hd := GlobalTheory.SplitEmbSep.one_le_norm_intCast (C := Om l) Fact.out GlobalTheory.PlaceBridge.norm_l_lt_one hE
  let b := integralBasis E
  have e : Module.Free.ChooseBasisIndex ℤ (𝓞 E) ≃ (E →ₐ[ℚ] Om l) :=
    Fintype.equivOfCardEq (by rw [AlgHom.card, Module.finrank_eq_card_basis b])
  have hdet := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ (Om l) b e
  rw [← coe_discr, map_intCast] at hdet
  set M := Algebra.embeddingsMatrixReindex ℚ (Om l) b e with hM
  have hMij : ∀ i j, M i j = (e j).toRingHom ((RingOfIntegers.basis E i : 𝓞 E) : E) := by
    intro i j
    simp [hM, b, Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix, integralBasis_apply]
  set k := e.symm τ.toRatAlgHom with hk
  set k' := e.symm τ'.toRatAlgHom with hk'
  have hkk : k ≠ k' := fun h => hne (by
    have := e.symm.injective h
    exact RingHom.ext fun x => DFunLike.congr_fun this x)
  have hcol : ∀ i, M i k + (-1 : Om l) • M i k' =
      τ ((RingOfIntegers.basis E i : 𝓞 E) : E) - τ' ((RingOfIntegers.basis E i : 𝓞 E) : E) := by
    intro i
    rw [hMij, hMij, hk, hk', e.apply_symm_apply, e.apply_symm_apply, neg_one_smul,
      ← sub_eq_add_neg]
    rfl
  have hlt' : ‖M.det‖ < 1 := by
    rw [← Matrix.det_updateCol_add_smul_self M hkk (-1)]
    refine GlobalTheory.SplitEmbSep.norm_det_lt_one _ (fun i j => ?_) k fun i => ?_
    · by_cases hj : j = k
      · rw [hj, Matrix.updateCol_self, hcol]; exact (hlt _).le
      · rw [Matrix.updateCol_ne hj, hMij]; exact norm_emb_le _ _
    · rw [Matrix.updateCol_self, hcol]; exact hlt _
  rw [hdet, norm_pow] at hd
  exact absurd (hd.trans_lt (pow_lt_one₀ (norm_nonneg _) hlt' two_ne_zero)) (lt_irrefl _)

/- English proof (translation)
Rewrite using `[← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralNorm]`. Establish `h1` using `minpoly.algHom_eq f f.toRingHom.injective x`. Establish `h2` using `minpoly.algHom_eq K.val K.val.toRingHom.injective x`. Conclude with `congrArg spectralValue (h1.trans h2.symm)`.
-/
theorem norm_algHom {K : IntermediateField ℚ_[l] (Om l)} (f : ↥K →ₐ[ℚ_[l]] Om l) (x : ↥K) :
    ‖f x‖ = ‖(x : Om l)‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralNorm]
  have h1 := minpoly.algHom_eq f f.toRingHom.injective x
  have h2 := minpoly.algHom_eq K.val K.val.toRingHom.injective x
  exact congrArg spectralValue (h1.trans h2.symm)

/- English proof (translation)
Rewrite using `[← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralNorm, minpoly.algEquiv_eq]`.
-/
theorem norm_gal (g : GQ l) (x : Om l) : ‖g x‖ = ‖x‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralNorm,
    minpoly.algEquiv_eq]

/- English proof (translation)
Rewrite using `[sub_eq_add_neg]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hx (by rwa [norm_neg]))`.
-/
theorem norm_sub_lt_one {x y : Om l} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) : ‖x - y‖ < 1 := by
  rw [sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hx (by rwa [norm_neg]))

/- English proof (translation)
Break down `lt_or_eq_of_le hx with hlt | heq` into its components or cases. Conclude with `norm_sub_lt_one (by rwa [norm_gal]) hlt`. Take `⟨ζ, m, hm, hζ, hxζ⟩` from `ReciprocityTheory.DiscreteGroups.LocalClassField.exists_teichmuller_bar x heq`. Establish `hm0 : 0 < m` using `Nat.pos_of_ne_zero (by rintro rfl; exact hm (dvd_zero l))`. Establish `h1 : g ζ = ζ` using `hg ζ (IntermediateField.subset_adjoin _ _ ⟨m, hm0, hm, hζ⟩)`.

Establish `h2 : g x - x = g (x - ζ) - (x - ζ)` using `by rw [map_sub, h1]; ring`. Rewrite using `[h2]`. Conclude with `norm_sub_lt_one (by rwa [norm_gal]) hxζ`.
-/
theorem inertia_of_fix (g : GQ l) (hg : ∀ x ∈ MaximalUnramifiedExtension l, g x = x) (x : Om l) (hx : ‖x‖ ≤ 1) : ‖g x - x‖ < 1 := by
  rcases lt_or_eq_of_le hx with hlt | heq
  · exact norm_sub_lt_one (by rwa [norm_gal]) hlt
  · obtain ⟨ζ, m, hm, hζ, hxζ⟩ := ReciprocityTheory.DiscreteGroups.LocalClassField.exists_teichmuller_bar x heq
    have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; exact hm (dvd_zero l))
    have h1 : g ζ = ζ := hg ζ (IntermediateField.subset_adjoin _ _ ⟨m, hm0, hm, hζ⟩)
    have h2 : g x - x = g (x - ζ) - (x - ζ) := by rw [map_sub, h1]; ring
    rw [h2]
    exact norm_sub_lt_one (by rwa [norm_gal]) hxζ

/- English proof (translation)
Establish `: IsGalois ℚ_[l] (Om l)` using `{}`. Rewrite using `[← InfiniteGalois.fixedField_fixingSubgroup (MaximalUnramifiedExtension l), IntermediateField.mem_fixedField_iff]`. Introduce `g hg`. Establish `h` using `emb_eq_of_congr hE ((g : Om l →+* Om l).comp τ) τ fun b => inertia_of_fix g ((IntermediateField.mem_fixingSubgroup_iff _ _).mp hg) _ (norm_emb_le τ b)`. Conclude with `DFunLike.congr_fun h x`.
-/
theorem emb_mem_Kur (hE : ¬ (l : ℤ) ∣ discr E) (τ : E →+* Om l) (x : E) : τ x ∈ MaximalUnramifiedExtension l := by
  have : IsGalois ℚ_[l] (Om l) := {}
  rw [← InfiniteGalois.fixedField_fixingSubgroup (MaximalUnramifiedExtension l), IntermediateField.mem_fixedField_iff]
  intro g hg
  have h := emb_eq_of_congr hE ((g : Om l →+* Om l).comp τ) τ fun b =>
    inertia_of_fix g ((IntermediateField.mem_fixingSubgroup_iff _ _).mp hg) _ (norm_emb_le τ b)
  exact DFunLike.congr_fun h x

/- English proof (translation)
Assemble the required witnesses or components as `⟨f.liftNormal (Om l), fun x => f.liftNormal_commutes (Om l) x⟩`.
-/
theorem exists_extend {K : IntermediateField ℚ_[l] (Om l)} (f : ↥K →ₐ[ℚ_[l]] Om l) :
    ∃ g : Om l →ₐ[ℚ_[l]] Om l, ∀ x : ↥K, g x = f x :=
  ⟨f.liftNormal (Om l), fun x => f.liftNormal_commutes (Om l) x⟩

section Bridge

variable {Ω : Type} [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O]
  [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O)

/- English proof (translation)
Establish `hfin` using `GlobalTheory.PlaceBridge.finiteDimensional_adjoin_range (Bw.j.comp (algebraMap E Ω))`. Establish `hcl` using `Submodule.closed_of_finiteDimensional (𝕜 := ℚ_[l]) (IntermediateField.adjoin ℚ_[l] (Set.range (Bw.j.comp (algebraMap E Ω)))).toSubmodule`. Use `le_trans (fun y hy => ?_) (IntermediateField.adjoin_le_iff.2 (Set.range_subset_iff.2 h))` and prove the remaining obligations. Conclude with `closure_minimal (IntermediateField.subset_adjoin ℚ_[l] _) hcl (Bw.j_dense hy)`.
-/
theorem kw_le (M : IntermediateField ℚ_[l] (Om l)) (h : ∀ x : E, Bw.j (algebraMap E Ω x) ∈ M) : Bw.Kw.1 ≤ M := by
  have hfin := GlobalTheory.PlaceBridge.finiteDimensional_adjoin_range (Bw.j.comp (algebraMap E Ω))
  have hcl := Submodule.closed_of_finiteDimensional (𝕜 := ℚ_[l])
    (IntermediateField.adjoin ℚ_[l] (Set.range (Bw.j.comp (algebraMap E Ω)))).toSubmodule
  refine le_trans (fun y hy => ?_) (IntermediateField.adjoin_le_iff.2 (Set.range_subset_iff.2 h))
  exact closure_minimal (IntermediateField.subset_adjoin ℚ_[l] _) hcl (Bw.j_dense hy)

/- English proof (translation)
The claim follows from `kw_le Bw _ fun x => hL ((g : Om l →+* Om l).comp (Bw.j.comp (algebraMap E Ω))) x`.
-/
theorem kw_le_comap (LL : FinExt l) (hL : ∀ (τ : E →+* Om l) (x : E), τ x ∈ LL.1) (g : Om l →ₐ[ℚ_[l]] Om l) :
    Bw.Kw.1 ≤ LL.1.comap g :=
  kw_le Bw _ fun x => hL ((g : Om l →+* Om l).comp (Bw.j.comp (algebraMap E Ω))) x

/- English proof (translation)
Establish `hK : Bw.Kw.1 ≤ MaximalUnramifiedExtension l` using `kw_le Bw _ fun x => emb_mem_Kur hE (Bw.j.comp (algebraMap E Ω)) x`. Use `⟨hK, hl, le_rfl, fun h => absurd h hl, (le_inf le_rfl hK).trans le_sup_left, fun τ x => ?_⟩` and prove the remaining obligations. Take `⟨g, hg⟩` from `exists_extend τ`. Take `⟨ζ, hζ⟩` from `hζ`. Establish `hζ' : IsPrimitiveRoot (ζ : Om l) l` using `hζ.map_of_injective (f := LL.1.val) Subtype.val_injective`.

Establish `hle : Ks Bw.Kw 1 ≤ LL.1.comap g`. Use `sup_le (inf_le_left.trans (kw_le_comap Bw LL hL g)) (IntermediateField.adjoin_le_iff.2 fun y hy => ?_)` and prove the remaining obligations. Establish `hy' : g y ^ l = 1`. Establish `: y ^ l = 1` using `by simpa using hy`. Rewrite using `[← map_pow, this, map_one]`.

Use `haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩`. Take `⟨i, -, hi⟩` from `hζ'.eq_pow_of_pow_eq_one hy'`. Express the relevant statement in the definitionally equal form `g y ∈ LL.1`. Rewrite using `[← hi]`. Conclude with `pow_mem ζ.2 i`.

Rewrite using `[← hg]`. Conclude with `hle x.2`.
-/
theorem caseA (hl : l ≠ 2) (hE : ¬ (l : ℤ) ∣ discr E) (LL : FinExt l) (hζ : ∃ ζ : ↥LL.1, IsPrimitiveRoot ζ l)
    (hL : ∀ (τ : E →+* Om l) (x : E), τ x ∈ LL.1) : CaseA Bw.Kw LL := by
  have hK : Bw.Kw.1 ≤ MaximalUnramifiedExtension l := kw_le Bw _ fun x => emb_mem_Kur hE (Bw.j.comp (algebraMap E Ω)) x
  refine ⟨hK, hl, le_rfl, fun h => absurd h hl, (le_inf le_rfl hK).trans le_sup_left, fun τ x => ?_⟩
  obtain ⟨g, hg⟩ := exists_extend τ
  obtain ⟨ζ, hζ⟩ := hζ
  have hζ' : IsPrimitiveRoot (ζ : Om l) l := hζ.map_of_injective (f := LL.1.val) Subtype.val_injective
  have hle : Ks Bw.Kw 1 ≤ LL.1.comap g := by
    refine sup_le (inf_le_left.trans (kw_le_comap Bw LL hL g)) (IntermediateField.adjoin_le_iff.2 fun y hy => ?_)
    have hy' : g y ^ l = 1 := by
      have : y ^ l = 1 := by simpa using hy
      rw [← map_pow, this, map_one]
    haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
    obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_pow_eq_one hy'
    change g y ∈ LL.1
    rw [← hi]
    exact pow_mem ζ.2 i
  rw [← hg]
  exact hle x.2

end Bridge

section Letters

variable {Ω : Type} [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O]
  [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) (hK : Bw.Kw.1 ≤ K0 Bw.Kw) {LL : FinExt l}

def toK0 : E →+* ↥(K0 Bw.Kw) :=
  (Bw.j.comp (algebraMap E Ω)).codRestrict (K0 Bw.Kw) fun x => hK (Bw.j_E x)

def embOf (e : ↥(K0 Bw.Kw) →ₐ[ℚ_[l]] ↥LL.1) : E →+* Om l :=
  ((LL.1.val.comp e : ↥(K0 Bw.Kw) →ₐ[ℚ_[l]] Om l) : ↥(K0 Bw.Kw) →+* Om l).comp (toK0 Bw hK)

omit [NumberField E] in

/- English proof (translation)
Introduce `x` and use `congrArg Subtype.val (hτ (toK0 Bw hK x)).symm`.
-/
theorem isInduced_embOf (e : ↥(K0 Bw.Kw) →ₐ[ℚ_[l]] ↥LL.1) (τ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL.1)
    (hτ : ∀ x : ↥(K0 Bw.Kw), τ (algebraMap ↥(K0 Bw.Kw) ↥Bw.Kw.1 x) = e x) :
    GlobalTheory.Pst.IsInduced Bw (embOf Bw hK e) τ := fun x =>
  congrArg Subtype.val (hτ (toK0 Bw hK x)).symm

omit [NumberField E] in

/- English proof (translation)
Introduce `e e' h`. Establish `h1` using `isInduced_embOf Bw hK e (e.comp (IntermediateField.inclusion hK)) fun _ => rfl`. Establish `h2` using `isInduced_embOf Bw hK e' (e'.comp (IntermediateField.inclusion hK)) fun _ => rfl`. Rewrite `h2` using `[← h]`. Establish `h3` using `h1.unique h2`.

Conclude with `AlgHom.ext fun x => DFunLike.congr_fun h3 (algebraMap ↥(K0 Bw.Kw) ↥Bw.Kw.1 x)`.
-/
theorem embOf_injective : Function.Injective (embOf Bw hK (LL := LL)) := by
  intro e e' h
  have h1 := isInduced_embOf Bw hK e (e.comp (IntermediateField.inclusion hK)) fun _ => rfl
  have h2 := isInduced_embOf Bw hK e' (e'.comp (IntermediateField.inclusion hK)) fun _ => rfl
  rw [← h] at h2
  have h3 := h1.unique h2
  exact AlgHom.ext fun x => DFunLike.congr_fun h3 (algebraMap ↥(K0 Bw.Kw) ↥Bw.Kw.1 x)

/- English proof (translation)
Use `emb_eq_of_congr hE _ _ fun b => ?_` and prove the remaining obligations. Establish `h1` using `hσ (embOf Bw hK e) b`. Establish `h2` using `P.PD_σ Bw.Kw (toK0 Bw hK b) (norm_emb_le (Bw.j.comp (algebraMap E Ω)) b)`. Establish `h3` using `norm_algHom (LL.1.val.comp e) ((P.PD Bw.Kw).σ (toK0 Bw hK b) - toK0 Bw hK b ^ l)`. Rewrite `h3` using `[map_sub, map_pow]`.

Establish `h4 : ‖embOf Bw hK (e.comp (P.PD Bw.Kw).σ) b - embOf Bw hK e b ^ l‖ < 1` using `h3.trans_lt h2`. Establish `h5` using `norm_sub_lt_one h4 h1`. Rewrite `h5` using `[sub_sub_sub_cancel_right]`. Then use the resulting hypothesis.
-/
theorem embOf_frob (P : LocPrime l) (hE : ¬ (l : ℤ) ∣ discr E) {σ : Equiv.Perm (E →+* PadicAlgCl l)}
    (hσ : GlobalTheory.ExpFrame.IsFrobPerm σ) (e : ↥(K0 Bw.Kw) →ₐ[ℚ_[l]] ↥LL.1) :
    embOf Bw hK (e.comp (P.PD Bw.Kw).σ) = σ (embOf Bw hK e) := by
  refine emb_eq_of_congr hE _ _ fun b => ?_
  have h1 := hσ (embOf Bw hK e) b
  have h2 := P.PD_σ Bw.Kw (toK0 Bw hK b) (norm_emb_le (Bw.j.comp (algebraMap E Ω)) b)
  have h3 := norm_algHom (LL.1.val.comp e) ((P.PD Bw.Kw).σ (toK0 Bw hK b) - toK0 Bw hK b ^ l)
  rw [map_sub, map_pow] at h3
  have h4 : ‖embOf Bw hK (e.comp (P.PD Bw.Kw).σ) b - embOf Bw hK e b ^ l‖ < 1 := h3.trans_lt h2
  have h5 := norm_sub_lt_one h4 h1
  rwa [sub_sub_sub_cancel_right] at h5

end Letters

/- English proof (translation)
Take `⟨w, A, hA, L0, Bw, hI, hτ⟩` from `GlobalTheory.ExpFrame.Tests.exists_bridge Ω τ`. Use `⟨w, A, hA, { Bw with LL := LL LL_split := fun f x => ?_ eO := RingEquiv.refl _ eO_alg := fun _ => rfl eO_cont := continuous_id eO_symm_cont := continuous_id }, hI, le_rfl, hτ⟩` and prove the remaining obligations. Take `⟨g, hg⟩` from `exists_extend f`. Rewrite using `[← hg]`. Conclude with `kw_le_comap Bw LL hL g x.2`.
-/
theorem exists_bridge_over (Ω : Type) [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (LL : FinExt l)
    (hL : ∀ (τ : E →+* Om l) (x : E), τ x ∈ LL.1) (τ : E →+* Om l) :
    ∃ (w : IsDedekindDomain.HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (_ : Formalism.ConjugateSelfDual.IsPlaceOver A w)
      (Bw : LocBridge l E Ω (ReciprocityTheory.Gal.Dec (F := E) A) ↥(OL LL)), GlobalTheory.Pst.Induces Bw ∧ Bw.LL.1 ≤ LL.1 ∧
        ∀ x, τ x = Bw.j (algebraMap E Ω x) := by
  obtain ⟨w, A, hA, L0, Bw, hI, hτ⟩ := GlobalTheory.ExpFrame.Tests.exists_bridge Ω τ
  refine ⟨w, A, hA, { Bw with
    LL := LL
    LL_split := fun f x => ?_
    eO := RingEquiv.refl _
    eO_alg := fun _ => rfl
    eO_cont := continuous_id
    eO_symm_cont := continuous_id }, hI, le_rfl, hτ⟩
  obtain ⟨g, hg⟩ := exists_extend f
  rw [← hg]
  exact kw_le_comap Bw LL hL g x.2

/- English proof (translation)
Introduce `l _ P AI hT H E Ω _ _ _ _ _ hl hE σ hσ LL hζ hL i₀`. Take `⟨w, A, hA, Bw, hI, hLL, hi₀⟩` from `exists_bridge_over Ω LL hL i₀`. Establish `hC` using `caseA Bw hl hE LL hζ hL`. Establish `hK0 : Bw.Kw.1 ≤ K0 Bw.Kw` using `le_inf le_rfl hC.1`. Establish `hbij` using `(H.W Bw.Kw 1 LL hC.2.2).emb_bij`.

Establish `hembσ` using `(H.W Bw.Kw 1 LL hC.2.2).emb_σ`. Set `emb` to `(H.W Bw.Kw 1 LL hC.2.2).emb`. Establish `hK0L : K0 Bw.Kw ≤ LL.1` using `inf_le_left.trans (kw_le Bw _ fun x => hL (Bw.j.comp (algebraMap E Ω)) x)`. Use `⟨Bw.Kw, hC, (ReciprocityTheory.Gal.Dec (F := E) A).subtype.comp Bw.e.symm.toMonoidHom, fun i => embOf Bw hK0 (emb i), (embOf_injective Bw hK0).comp hbij.1, fun i => ?_, ?_, fun n r J hr => ?_⟩` and prove the remaining obligations. Establish `h` using `hembσ (i - 1)`.

Rewrite `h` using `[sub_add_cancel]`. Conclude with `(congrArg (embOf Bw hK0) h.symm).trans (embOf_frob Bw hK0 P hE hσ (emb i))`. Take `⟨i, hi⟩` from `hbij.2 (IntermediateField.inclusion hK0L)`. Use `⟨i, RingHom.ext fun x => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `embOf Bw hK0 ((H.W Bw.Kw 1 LL hC.2.2).emb i) x = _`.

Rewrite using `[hi, hi₀]`. Both sides reduce to the same expression. Take `⟨hc, hj⟩` from `hr.2 P AI ⟨hT⟩ w A hA _ Bw hI`. Establish `hM : GlobalTheory.Pst.IsModel Bw (((Matrix.GeneralLinearGroup.map (toOm LL)).comp r).comp (ReciprocityTheory.Gal.Dec (F` using `E) A).subtype) LL (Formalism.MainNotions.N.mapRep (algebraMap ↥(OL LL) ↥LL.1) (r.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype)) := ⟨hLL, by ext g a b; rfl⟩`. Use `⟨fun a b => ?_, (hM.isCrysAt_iff P).1 hc, fun i τ hτ a => ?_⟩` and prove the remaining obligations.

Establish `h1 : Continuous fun g : ↥(GK Bw.Kw) => ((Bw.e.symm g : ↥(ReciprocityTheory.Gal.Dec (F` using `E) A)) : Ω ≃ₐ[E] Ω) := continuous_subtype_val.comp Bw.e_symm_cont`. Establish `h2` using `(Units.continuous_val.comp (hr.1.comp h1)).matrix_elem a b`. Conclude with `continuous_induced_rng.2 h2`. Establish `hτ'` using `isInduced_embOf Bw hK0 (emb i) τ hτ`. Conclude with `(GlobalTheory.Pst.IsJumpsAt.count_eq P hM hτ' (hj _ _ _ hτ') a).symm`.
-/
theorem exists_place : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (H : LocHW l P) (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω], l ≠ 2 → ¬ (l : ℤ) ∣ NumberField.discr E → ∀ (σ : Equiv.Perm (E →+* PadicAlgCl l)), GlobalTheory.ExpFrame.IsFrobPerm σ → ∀ LL : FinExt l, (∃ ζ : ↥LL.1, IsPrimitiveRoot ζ l) → (∀ (τ : E →+* PadicAlgCl l) (x : E), τ x ∈ LL.1) → ∀ i₀ : E →+* PadicAlgCl l, ∃ (K : FinExt l) (hA : CaseA K LL) (ι : ↥(GK K) →* (Ω ≃ₐ[E] Ω)) (κ : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → (E →+* PadicAlgCl l)), Function.Injective κ ∧ (∀ i, κ (i - 1) = σ (κ i)) ∧ i₀ ∈ Set.range κ ∧ ∀ (n : ℕ) (r : (Ω ≃ₐ[E] Ω) →* GL (Fin n) ↥(OL LL)) (J : (E →+* PadicAlgCl l) → Multiset ℤ), GlobalTheory.ExpFrame.CrysWith ((Matrix.GeneralLinearGroup.map (toOm LL)).comp r) J → MatGood P (H.W K 1 LL hA.2.2).emb (r.comp ι) (fun i => J (κ i)) := by
  intro l _ P AI hT H E Ω _ _ _ _ _ hl hE σ hσ LL hζ hL i₀
  obtain ⟨w, A, hA, Bw, hI, hLL, hi₀⟩ := exists_bridge_over Ω LL hL i₀
  have hC := caseA Bw hl hE LL hζ hL
  have hK0 : Bw.Kw.1 ≤ K0 Bw.Kw := le_inf le_rfl hC.1
  have hbij := (H.W Bw.Kw 1 LL hC.2.2).emb_bij
  have hembσ := (H.W Bw.Kw 1 LL hC.2.2).emb_σ
  let emb := (H.W Bw.Kw 1 LL hC.2.2).emb
  have hK0L : K0 Bw.Kw ≤ LL.1 := inf_le_left.trans (kw_le Bw _ fun x => hL (Bw.j.comp (algebraMap E Ω)) x)
  refine ⟨Bw.Kw, hC, (ReciprocityTheory.Gal.Dec (F := E) A).subtype.comp Bw.e.symm.toMonoidHom, fun i => embOf Bw hK0 (emb i),
    (embOf_injective Bw hK0).comp hbij.1, fun i => ?_, ?_, fun n r J hr => ?_⟩
  · have h := hembσ (i - 1)
    rw [sub_add_cancel] at h
    exact (congrArg (embOf Bw hK0) h.symm).trans (embOf_frob Bw hK0 P hE hσ (emb i))
  · obtain ⟨i, hi⟩ := hbij.2 (IntermediateField.inclusion hK0L)
    refine ⟨i, RingHom.ext fun x => ?_⟩
    change embOf Bw hK0 ((H.W Bw.Kw 1 LL hC.2.2).emb i) x = _
    rw [hi, hi₀]
    rfl
  · obtain ⟨hc, hj⟩ := hr.2 P AI ⟨hT⟩ w A hA _ Bw hI
    have hM : GlobalTheory.Pst.IsModel Bw (((Matrix.GeneralLinearGroup.map (toOm LL)).comp r).comp
        (ReciprocityTheory.Gal.Dec (F := E) A).subtype) LL
        (Formalism.MainNotions.N.mapRep (algebraMap ↥(OL LL) ↥LL.1) (r.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype)) :=
      ⟨hLL, by ext g a b; rfl⟩
    refine ⟨fun a b => ?_, (hM.isCrysAt_iff P).1 hc, fun i τ hτ a => ?_⟩
    · have h1 : Continuous fun g : ↥(GK Bw.Kw) => ((Bw.e.symm g : ↥(ReciprocityTheory.Gal.Dec (F := E) A)) : Ω ≃ₐ[E] Ω) :=
        continuous_subtype_val.comp Bw.e_symm_cont
      have h2 := (Units.continuous_val.comp (hr.1.comp h1)).matrix_elem a b
      exact continuous_induced_rng.2 h2
    · have hτ' := isInduced_embOf Bw hK0 (emb i) τ hτ
      exact (GlobalTheory.Pst.IsJumpsAt.count_eq P hM hτ' (hj _ _ _ hτ') a).symm

end GlobalTheory.PlaceLetters

end
