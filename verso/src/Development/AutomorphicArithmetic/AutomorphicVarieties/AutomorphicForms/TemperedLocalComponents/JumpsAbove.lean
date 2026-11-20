import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CharFil
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IqBasic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamRepresentationTensorComparison
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamComponentsCrystallineLettersFinrank
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicHodgePropertiesConjInvariant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.CrystallineCharacterRatio
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.GalOfCusp

namespace UpperTheory.V.Af.JumpsAbove

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Use `L.2` as an intermediate fact. Use `K.2` as an intermediate fact. Establish `: IsModuleTopology ℚ_[l] ↥L.1` using `isModuleTopologyOfFiniteDimensional`. Take `⟨T⟩` from `Loc.tiedP l`. Establish `hφ : Topology.IsOpenEmbedding (GK K).subtype` using `(IntermediateField.fixingSubgroup_isOpen K.1).isOpenEmbedding_subtypeVal`.

Establish `h` using `(Loc.charFil (GK K).subtype hφ κ hκ w hw).2`. Establish `hF : ∀ i, Loc.FilT ↥L.1 ↥L.1 i = FilV ((Loc.PP l).PD K) (LL` using `↥L.1) (V := ↥L.1) i := fun i => by`. Establish `: (((Loc.PP l).PD (Loc.botExt l)).Fil i).restrictScalars ℚ_[l] = (((Loc.PP l).PD K).Fil i).restrictScalars ℚ_[l]` using `SetLike.coe_injective ((Loc.PP l).PD_Fil _ _ i)`. Unfold `Loc.FilT FilV`. Rewrite using `[this]`.

Establish `hD : Loc.Ddr (GK K).subtype (Loc.chRep κ) = DdR ((Loc.PP l).PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep κ)`. Unfold `Loc.Ddr DdR`. Use `iInf_congr fun g => ?_` and prove the remaining obligations. Establish `h2 : actVdR ((Loc.PP l).PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep κ) g = Loc.actD (GK K).subtype (Loc.chRep κ) g`. Unfold `actVdR Loc.actD`.

Use `congr 1`. Conclude with `LinearMap.ext fun z => (Loc.PP l).PD_actdR K g z`. Rewrite using `[h2]`. Simplify using `only [Loc.FilD, hF, hD] at h`. Establish `hr` using `(((GlobalTheory.Per.Components.components_finrank l _ _ T K L _ (Formalism.WeaklyAdmissibleFiltrations.charRep κ)).1 τ).2.2 hd).trans (Module.finrank_self _)`.

Establish `hle : DdRE ((Loc.PP l).PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep κ) τ ≤ DdR ((Loc.PP l).PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep κ)` using `inf_le_left`. Establish `h1 : ∀ i, i ≤ -w → Module.finrank ↥L.1 ↥(FildR ((Loc.PP l).PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep κ) τ i) = 1` using `fun i hi => by`. Rewrite using `[FildR, inf_eq_left.2 (hle.trans (inf_eq_left.1 ((h i).1 hi))), hr]`. Establish `h0 : ∀ i, -w < i → Module.finrank ↥L.1 ↥(FildR ((Loc.PP l).PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep κ) τ i) = 0` using `fun i hi => by`. Rewrite using `[FildR, le_bot_iff.1 ((inf_le_inf_right _ hle).trans ((h i).2 hi).le), finrank_bot]`.

Unfold `multV`. Break down `lt_trichotomy a (-w) with ha | ha | ha` into its components or cases. Rewrite using `[h1 a ha.le, h1 (a + 1) ha, if_neg ha.ne]`. Simplify using the standard rewrite rules. Rewrite using `[h1 a ha.le, h0 (a + 1) (by omega), if_pos ha]; simp`.

Rewrite using `[h0 a ha, h0 (a + 1) (by omega), if_neg ha.ne']; simp`.
-/
private theorem char_mult (K L : FinExt l) (κ : ↥(GK K) →* (↥L.1)ˣ) (hκ : Continuous fun g => (κ g : ↥L.1)) (w : ℤ)
    (hw : Loc.HasWeight (GK K).subtype κ w) (hd : IsDR ((Loc.PP l).PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep κ))
    (τ : ↥K.1 →ₐ[ℚ_[l]] ↥L.1) (a : ℤ) : multV ((Loc.PP l).PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep κ) τ a = if a = -w then 1 else 0 := by
  have := L.2
  have := K.2
  have : IsModuleTopology ℚ_[l] ↥L.1 := isModuleTopologyOfFiniteDimensional
  obtain ⟨T⟩ := Loc.tiedP l
  have hφ : Topology.IsOpenEmbedding (GK K).subtype :=
    (IntermediateField.fixingSubgroup_isOpen K.1).isOpenEmbedding_subtypeVal
  have h := (Loc.charFil (GK K).subtype hφ κ hκ w hw).2
  have hF : ∀ i, Loc.FilT ↥L.1 ↥L.1 i = FilV ((Loc.PP l).PD K) (LL := ↥L.1) (V := ↥L.1) i := fun i => by
    have : (((Loc.PP l).PD (Loc.botExt l)).Fil i).restrictScalars ℚ_[l] =
        (((Loc.PP l).PD K).Fil i).restrictScalars ℚ_[l] := SetLike.coe_injective ((Loc.PP l).PD_Fil _ _ i)
    unfold Loc.FilT FilV
    rw [this]
  have hD : Loc.Ddr (GK K).subtype (Loc.chRep κ) = DdR ((Loc.PP l).PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep κ) := by
    unfold Loc.Ddr DdR
    refine iInf_congr fun g => ?_
    have h2 : actVdR ((Loc.PP l).PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep κ) g = Loc.actD (GK K).subtype (Loc.chRep κ) g := by
      unfold actVdR Loc.actD
      congr 1
      exact LinearMap.ext fun z => (Loc.PP l).PD_actdR K g z
    rw [h2]
  simp only [Loc.FilD, hF, hD] at h
  have hr := (((GlobalTheory.Per.Components.components_finrank l _ _ T K L _ (Formalism.WeaklyAdmissibleFiltrations.charRep κ)).1 τ).2.2 hd).trans
    (Module.finrank_self _)
  have hle : DdRE ((Loc.PP l).PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep κ) τ ≤ DdR ((Loc.PP l).PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep κ) := inf_le_left
  have h1 : ∀ i, i ≤ -w → Module.finrank ↥L.1 ↥(FildR ((Loc.PP l).PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep κ) τ i) = 1 := fun i hi => by
    rw [FildR, inf_eq_left.2 (hle.trans (inf_eq_left.1 ((h i).1 hi))), hr]
  have h0 : ∀ i, -w < i → Module.finrank ↥L.1 ↥(FildR ((Loc.PP l).PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep κ) τ i) = 0 := fun i hi => by
    rw [FildR, le_bot_iff.1 ((inf_le_inf_right _ hle).trans ((h i).2 hi).le), finrank_bot]
  unfold multV
  rcases lt_trichotomy a (-w) with ha | ha | ha
  · rw [h1 a ha.le, h1 (a + 1) ha, if_neg ha.ne]; simp
  · rw [h1 a ha.le, h0 (a + 1) (by omega), if_pos ha]; simp
  · rw [h0 a ha, h0 (a + 1) (by omega), if_neg ha.ne']; simp

/- English proof (translation)
Take `⟨T⟩` from `Loc.tiedP l`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `ρ M κ _ _ _ _`. Use `⟨fun i => i.elim0, fun τ a => ?_⟩` and prove the remaining obligations.

Establish `: Subsingleton (TensorProduct ℚ_[l] (Fin 0 → ↥L.1) (Loc.PP l).R.BdR)` using `inferInstance`. Simplify using `[multV, Module.finrank_zero_of_subsingleton]`. Consider the case `succ n ih`. Introduce `ρ M κ hρ hM hκ hd`. Set `ι : ↥L.1 →ₗ[↥L.1] (Fin (n + 1) → ↥L.1)` to `LinearMap.single _ (fun _ => ↥L.1) 0`.

Set `π : (Fin (n + 1) → ↥L.1) →ₗ[↥L.1] (Fin n → ↥L.1)` to `LinearMap.funLeft _ _ Fin.succ`. Set `M' : ↥(GK K) → Matrix (Fin n) (Fin n) ↥L.1` to `fun g => (M g).submatrix Fin.succ Fin.succ`. Establish `hπ : ∀ g x, π (ρ g x) = (M' g).mulVec (π x)` using `fun g x => by`. Use function extensionality and compare the values at `i`. Simplify using `[π, M', hρ, LinearMap.funLeft_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, hM g i.succ 0 (Fin.succ_pos i)]`.

Establish `hs : Function.Surjective π` using `LinearMap.funLeft_surjective_of_injective _ _ _ (Fin.succ_injective n)`. Set `ρ' : Representation ↥L.1 ↥(GK K) (Fin n → ↥L.1)` to `{ toFun := fun g => Matrix.toLin' (M' g) map_one' := LinearMap.ext fun y => by`. Take `⟨x, rfl⟩` from `hs y`. Rewrite using `[Matrix.toLin'_apply, ← hπ, map_one]`. Both sides reduce to the same expression.

Use the proof step `map_mul' := fun g h => LinearMap.ext fun y => by`. Take `⟨x, rfl⟩` from `hs y`. Rewrite using `[Module.End.mul_apply, Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.toLin'_apply, ← hπ, ← hπ, ← hπ, map_mul]`. Use `rfl }`. Take `⟨d0, d2, hm⟩` from `GlobalTheory.Per.ExactMult.exact_hodge_add l _ _ T K L _ (Formalism.WeaklyAdmissibleFiltrations.charRep (κ 0)) _ ρ _ ρ' ι π (fun g x => by`.

Use function extensionality and compare the values at `i`. Rewrite using `[hρ]`. Use `Fin.cases ?_ (fun i => ?_) i` and prove the remaining obligations. Simplify using `[ι, Formalism.WeaklyAdmissibleFiltrations.charRep, hκ]`. Simplify using `[ι, Formalism.WeaklyAdmissibleFiltrations.charRep, hM g i.succ 0 (Fin.succ_pos i)])`.

Use `hπ (fun x y h => by simpa [ι] using congrFun h 0) hs`. Use the proof step `(by`. Use extensionality with `x`. Simplify using `only [LinearMap.mem_range, LinearMap.mem_ker]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨y, rfl⟩`. Use function extensionality and compare the values at `i`. Simplify using `[ι, π, LinearMap.funLeft_apply]`. Introduce `h`. Use `⟨x 0, funext fun i => Fin.cases ?_ (fun i => ?_) i⟩` and prove the remaining obligations.

Simplify using `[ι]`. Simplify `(congrFun h i).symm) hd` using `[ι, π, LinearMap.funLeft_apply]`. Take `⟨e1, e2⟩` from `ih ρ' M' (fun i => κ i.succ) (fun g x => rfl) (fun g i j h => hM g _ _ (Fin.succ_lt_succ_iff.2 h)) (fun g i => hκ g _) d2`. Use `⟨fun i => Fin.cases d0 e1 i, fun τ a => ?_⟩` and prove the remaining obligations. Rewrite using `[(hm τ a).2.1, Fin.sum_univ_succ, e2]`.
-/
private theorem flag_mult (K L : FinExt l) (n : ℕ) : ∀ (ρ : Representation ↥L.1 ↥(GK K) (Fin n → ↥L.1))
    (M : ↥(GK K) → Matrix (Fin n) (Fin n) ↥L.1) (κ : Fin n → ↥(GK K) →* (↥L.1)ˣ),
    (∀ g x, ρ g x = (M g).mulVec x) → (∀ g i j, j < i → M g i j = 0) → (∀ g i, M g i i = κ i g) →
    IsDR ((Loc.PP l).PD K) ρ → (∀ i, IsDR ((Loc.PP l).PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep (κ i))) ∧
      ∀ τ a, multV ((Loc.PP l).PD K) ρ τ a = ∑ i, multV ((Loc.PP l).PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep (κ i)) τ a := by
  obtain ⟨T⟩ := Loc.tiedP l
  induction n with
  | zero =>
    intro ρ M κ _ _ _ _
    refine ⟨fun i => i.elim0, fun τ a => ?_⟩
    have : Subsingleton (TensorProduct ℚ_[l] (Fin 0 → ↥L.1) (Loc.PP l).R.BdR) := inferInstance
    simp [multV, Module.finrank_zero_of_subsingleton]
  | succ n ih =>
    intro ρ M κ hρ hM hκ hd
    let ι : ↥L.1 →ₗ[↥L.1] (Fin (n + 1) → ↥L.1) := LinearMap.single _ (fun _ => ↥L.1) 0
    let π : (Fin (n + 1) → ↥L.1) →ₗ[↥L.1] (Fin n → ↥L.1) := LinearMap.funLeft _ _ Fin.succ
    let M' : ↥(GK K) → Matrix (Fin n) (Fin n) ↥L.1 := fun g => (M g).submatrix Fin.succ Fin.succ
    have hπ : ∀ g x, π (ρ g x) = (M' g).mulVec (π x) := fun g x => by
      funext i
      simp [π, M', hρ, LinearMap.funLeft_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
        hM g i.succ 0 (Fin.succ_pos i)]
    have hs : Function.Surjective π := LinearMap.funLeft_surjective_of_injective _ _ _ (Fin.succ_injective n)
    let ρ' : Representation ↥L.1 ↥(GK K) (Fin n → ↥L.1) :=
      { toFun := fun g => Matrix.toLin' (M' g)
        map_one' := LinearMap.ext fun y => by
          obtain ⟨x, rfl⟩ := hs y
          rw [Matrix.toLin'_apply, ← hπ, map_one]; rfl
        map_mul' := fun g h => LinearMap.ext fun y => by
          obtain ⟨x, rfl⟩ := hs y
          rw [Module.End.mul_apply, Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.toLin'_apply, ← hπ, ← hπ, ← hπ,
            map_mul]; rfl }
    obtain ⟨d0, d2, hm⟩ := GlobalTheory.Per.ExactMult.exact_hodge_add l _ _ T K L _ (Formalism.WeaklyAdmissibleFiltrations.charRep (κ 0)) _ ρ _ ρ' ι π
      (fun g x => by
        funext i
        rw [hρ]
        refine Fin.cases ?_ (fun i => ?_) i
        · simp [ι, Formalism.WeaklyAdmissibleFiltrations.charRep, hκ]
        · simp [ι, Formalism.WeaklyAdmissibleFiltrations.charRep, hM g i.succ 0 (Fin.succ_pos i)])
      hπ (fun x y h => by simpa [ι] using congrFun h 0) hs
      (by
        ext x
        simp only [LinearMap.mem_range, LinearMap.mem_ker]
        constructor
        · rintro ⟨y, rfl⟩
          funext i
          simp [ι, π, LinearMap.funLeft_apply]
        · intro h
          refine ⟨x 0, funext fun i => Fin.cases ?_ (fun i => ?_) i⟩
          · simp [ι]
          · simpa [ι, π, LinearMap.funLeft_apply] using (congrFun h i).symm) hd
    obtain ⟨e1, e2⟩ := ih ρ' M' (fun i => κ i.succ) (fun g x => rfl)
      (fun g i j h => hM g _ _ (Fin.succ_lt_succ_iff.2 h)) (fun g i => hκ g _) d2
    refine ⟨fun i => Fin.cases d0 e1 i, fun τ a => ?_⟩
    rw [(hm τ a).2.1, Fin.sum_univ_succ, e2]

/- English proof (translation)
Establish `: NeZero M` using `⟨by omega⟩`. Take `⟨z, hz⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) M`. Establish `: FiniteDimensional ℚ_[l] ↥(IntermediateField.adjoin ℚ_[l] {z})` using `IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral z)`. Use `⟨(IntermediateField.adjoin ℚ_[l] {z}).fixingSubgroup.comap (GK K).subtype, (IntermediateField.fixingSubgroup_isOpen _).preimage continuous_subtype_val, fun s hs ζ hζ => ?_⟩` and prove the remaining obligations. Take `⟨i, -, rfl⟩` from `hz.eq_pow_of_pow_eq_one hζ`.

Establish `h : (s : GQ l) z = z` using `(IntermediateField.mem_fixingSubgroup_iff _ _).1 hs z (IntermediateField.mem_adjoin_simple_self _ z)`. Rewrite using `[map_pow, h]`.
-/
private theorem exists_open (K : FinExt l) {M : ℕ} (hM : 1 ≤ M) : ∃ U : Subgroup ↥(GK K), IsOpen (U : Set ↥(GK K)) ∧
    ∀ s ∈ U, ∀ ζ : Om l, ζ ^ M = 1 → (s : GQ l) ζ = ζ := by
  have : NeZero M := ⟨by omega⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) M
  have : FiniteDimensional ℚ_[l] ↥(IntermediateField.adjoin ℚ_[l] {z}) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral z)
  refine ⟨(IntermediateField.adjoin ℚ_[l] {z}).fixingSubgroup.comap (GK K).subtype,
    (IntermediateField.fixingSubgroup_isOpen _).preimage continuous_subtype_val, fun s hs ζ hζ => ?_⟩
  obtain ⟨i, -, rfl⟩ := hz.eq_pow_of_pow_eq_one hζ
  have h : (s : GQ l) z = z := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hs z
    (IntermediateField.mem_adjoin_simple_self _ z)
  rw [map_pow, h]

end UpperTheory.V.Af.JumpsAbove

open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.JumpsAbove in
/- English proof (translation)
Introduce and unpack `- F Ω _ _ _ _ _ l _ - n M hM m r hr w A - O _ _ _ Bw hj κ ⟨χ, hχ, ⟨g, hg⟩, hI⟩ τ J hJ`. Take `⟨L, r', hL, hd, τ', -, hc⟩` from `(GlobalTheory.ConjLocal.local_conj l (Loc.PP l) F Ω O _ Bw n _ ((MulAut.conj g).toMonoidHom.comp (r.comp (Dec (F := F) A).subtype)) g (fun _ => rfl)).2.2.2 τ J hJ`. Establish `he : ∀ s i j, ((r' s i j : ↥L.1) : Om l) = (g * r s * g⁻¹ : GL (Fin n) (Om l)) i j` using `fun s i j => congrArg (fun f : ↥(Dec (F := F) A) →* GL (Fin n) (Om l) => (f s : Matrix (Fin n) (Fin n) (Om l)) i j) hL.2`. Establish `hκ : ∀ s i, ((r' s i i : ↥L.1) : Om l) = κ i s` using `fun s i => (he s i i).trans ((hg s).2 i)`. Set `κ' : Fin n → ↥(GK Bw.Kw) →* (↥L.1)ˣ` to `fun i => MonoidHom.toHomUnits { toFun := fun s => r' (Bw.e.symm s) i i map_one' := by simp map_mul' := fun s t => Subtype.ext (by`.

Rewrite using `[IntermediateField.coe_mul, hκ, hκ, hκ, map_mul, map_mul, Units.val_mul]) }`. Establish `hκ' : ∀ i s, ((κ' i s : ↥L.1) : Om l) = κ i (Bw.e.symm s)` using `fun i s => hκ _ _`. Take `⟨d, hm⟩` from `flag_mult Bw.Kw L n (Bw.repE L r') (fun s => r' (Bw.e.symm s)) κ' (fun _ _ => rfl) (fun s i j h => Subtype.ext ((he _ i j).trans ((hg _).1 i j h))) (fun _ _ => rfl) (by rw [IsDR, Module.finrank_fin_fun]; exact hd)`. Take `⟨U, hU, hUζ⟩` from `exists_open Bw.Kw hM`. Establish `hcm : ∀ (s : ↥(GK Bw.Kw)) x, (s : GQ l) (Bw.j x) = Bw.j ((Bw.e.symm s : G F Ω) x)` using `fun s x => by`.

Rewrite using `[← Bw.e_comm, MulEquiv.apply_symm_apply]`. Establish `key : ∀ i a, multV ((Loc.PP l).PD Bw.Kw) (Formalism.WeaklyAdmissibleFiltrations.charRep (κ' i)) τ' a = if a = -m i then 1 else 0` using `fun i a => by`. Use `char_mult Bw.Kw L (κ' i) (continuous_induced_rng.2 ?_) (m i) ⟨U, hU, fun s hs hq => ?_⟩ (d i) τ' a` and prove the remaining obligations. Establish `h1 : Continuous fun s : ↥(GK Bw.Kw) => g * r (Bw.e.symm s) * g⁻¹` using `(continuous_const.mul (hr.comp (continuous_subtype_val.comp Bw.e_symm_cont))).mul continuous_const`. Conclude with `((Units.continuous_val.comp h1).matrix_elem i i).congr fun s => (he _ i i).symm`.

Establish `hine : (Bw.e.symm s : G F Ω) ∈ Ine (F` using `F) A := by`. Use `⟨(Bw.e.symm s).2, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[hj.valuation_lt_one_iff, map_sub, ← hcm]`. Conclude with `((Loc.iqBasic l).2.2.1 _).1 hq _ ((hj x).1 ((A.valuation_le_one_iff x).1 hx))`. Establish `h1 : χ i (Bw.e.symm s) = 1` using `hχ i _ fun ζ hζ => Bw.j.injective (by`.

Rewrite using `[← hcm, hUζ s hs _ (by rw [← map_pow, hζ, map_one])])`. Establish `h2` using `(GlobalTheory.Survey.CrystallineCharacterRatio.chi_eq_cyc (Loc.PP l) Bw.j _ _ (hcm s)).symm.trans ((Loc.cycFacts l l).2.2 s)`. Use `Units.ext (Subtype.ext ?_)` and prove the remaining obligations. Rewrite using `[hκ', hI i _ hine, h1, mul_one, Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val]`. Use `Eq.trans ?_ (map_zpow₀ (algebraMap ↥L.1 (Om l)) _ _).symm` and prove the remaining obligations.

Use `congr 1`. Conclude with `congrArg (algebraMap ℚ_[l] (Om l)) h2`. Use extensionality with `a`. Establish `h` using `hc a`. Rewrite `h` using `[LocBridge.multE, hm]`.

Simplify using `only [key] at h`. Rewrite using `[Multiset.count_map, ← Nat.cast_inj (R := ℤ), h]`. Simplify using `[Finset.card_def]`.
-/
theorem UpperTheory.V.Af.jumpsAbove :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Af.JumpsAbove := by
  rintro - F Ω _ _ _ _ _ l _ - n M hM m r hr w A - O _ _ _ Bw hj κ ⟨χ, hχ, ⟨g, hg⟩, hI⟩ τ J hJ
  obtain ⟨L, r', hL, hd, τ', -, hc⟩ := (GlobalTheory.ConjLocal.local_conj l (Loc.PP l) F Ω O _ Bw n _
    ((MulAut.conj g).toMonoidHom.comp (r.comp (Dec (F := F) A).subtype)) g (fun _ => rfl)).2.2.2 τ J hJ
  have he : ∀ s i j, ((r' s i j : ↥L.1) : Om l) = (g * r s * g⁻¹ : GL (Fin n) (Om l)) i j := fun s i j =>
    congrArg (fun f : ↥(Dec (F := F) A) →* GL (Fin n) (Om l) => (f s : Matrix (Fin n) (Fin n) (Om l)) i j) hL.2
  have hκ : ∀ s i, ((r' s i i : ↥L.1) : Om l) = κ i s := fun s i => (he s i i).trans ((hg s).2 i)
  let κ' : Fin n → ↥(GK Bw.Kw) →* (↥L.1)ˣ := fun i => MonoidHom.toHomUnits
    { toFun := fun s => r' (Bw.e.symm s) i i
      map_one' := by simp
      map_mul' := fun s t => Subtype.ext (by
        rw [IntermediateField.coe_mul, hκ, hκ, hκ, map_mul, map_mul, Units.val_mul]) }
  have hκ' : ∀ i s, ((κ' i s : ↥L.1) : Om l) = κ i (Bw.e.symm s) := fun i s => hκ _ _
  obtain ⟨d, hm⟩ := flag_mult Bw.Kw L n (Bw.repE L r') (fun s => r' (Bw.e.symm s)) κ' (fun _ _ => rfl)
    (fun s i j h => Subtype.ext ((he _ i j).trans ((hg _).1 i j h))) (fun _ _ => rfl)
    (by rw [IsDR, Module.finrank_fin_fun]; exact hd)
  obtain ⟨U, hU, hUζ⟩ := exists_open Bw.Kw hM
  have hcm : ∀ (s : ↥(GK Bw.Kw)) x, (s : GQ l) (Bw.j x) = Bw.j ((Bw.e.symm s : G F Ω) x) := fun s x => by
    rw [← Bw.e_comm, MulEquiv.apply_symm_apply]
  have key : ∀ i a, multV ((Loc.PP l).PD Bw.Kw) (Formalism.WeaklyAdmissibleFiltrations.charRep (κ' i)) τ' a = if a = -m i then 1 else 0 := fun i a => by
    refine char_mult Bw.Kw L (κ' i) (continuous_induced_rng.2 ?_) (m i) ⟨U, hU, fun s hs hq => ?_⟩ (d i) τ' a
    · have h1 : Continuous fun s : ↥(GK Bw.Kw) => g * r (Bw.e.symm s) * g⁻¹ :=
        (continuous_const.mul (hr.comp (continuous_subtype_val.comp Bw.e_symm_cont))).mul continuous_const
      exact ((Units.continuous_val.comp h1).matrix_elem i i).congr fun s => (he _ i i).symm
    · have hine : (Bw.e.symm s : G F Ω) ∈ Ine (F := F) A := by
        refine ⟨(Bw.e.symm s).2, fun x hx => ?_⟩
        rw [hj.valuation_lt_one_iff, map_sub, ← hcm]
        exact ((Loc.iqBasic l).2.2.1 _).1 hq _ ((hj x).1 ((A.valuation_le_one_iff x).1 hx))
      have h1 : χ i (Bw.e.symm s) = 1 := hχ i _ fun ζ hζ => Bw.j.injective (by
        rw [← hcm, hUζ s hs _ (by rw [← map_pow, hζ, map_one])])
      have h2 := (GlobalTheory.Survey.CrystallineCharacterRatio.chi_eq_cyc (Loc.PP l) Bw.j _ _ (hcm s)).symm.trans ((Loc.cycFacts l l).2.2 s)
      refine Units.ext (Subtype.ext ?_)
      rw [hκ', hI i _ hine, h1, mul_one, Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val]
      refine Eq.trans ?_ (map_zpow₀ (algebraMap ↥L.1 (Om l)) _ _).symm
      congr 1
      exact congrArg (algebraMap ℚ_[l] (Om l)) h2
  ext a
  have h := hc a
  rw [LocBridge.multE, hm] at h
  simp only [key] at h
  rw [Multiset.count_map, ← Nat.cast_inj (R := ℤ), h]
  simp [Finset.card_def]
