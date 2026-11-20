import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.LocalComparison.CoeNeTo6
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterDeRham
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasPeriods
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniqueEmbeddingExtension
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLubinTateCharacterUnitaryStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGaloisEmbeddingExtensionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ImportsTer
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeRhamRankLubinTateLineStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaloisCharacterArtinCompatStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsOpenUnitSubgroupKerStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaloisOpenSubgroupLocalUnitsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalCharacterFiniteExtensionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalCharacterInducedTiedStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalCharacterInducedTiedSixStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedCharactersDeRhamJumpZeroStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniqueEmbeddingExtensionStatement
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical

namespace PositivityTheory.SecR.Hladr

def LTPeriods : Prop := ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied6 l P AI) →
    ∀ (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ), IsLTChar K χ →
      Continuous (fun g => (((χ g : (↥K.1)ˣ) : ↥K.1) : Om l)) → HasPeriods P K χ
end PositivityTheory.SecR.Hladr

namespace PositivityTheory.SecR.Hladr
/- English proof (translation)
Apply `MonoidHom.ext` to reduce the goal to its premises. Introduce `g`. Simplify using `[LocBridge.repE, lineRep]`.
-/
theorem repE_eq {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime] {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) (LL' : FinExt l)
    (ψ : ↥(GK Bw.Kw) →* (↥LL'.1)ˣ) :
    Bw.repE LL' ((PositivityTheory.HodgeLocalCharacter.HLC.toGL1 ↥LL'.1).comp (ψ.comp Bw.e.toMonoidHom)) = lineRep ψ := by
  apply MonoidHom.ext
  intro g
  simp [LocBridge.repE, lineRep]

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ l _ P AI hT w A hA O _ _ _ Bw hI art hart LL' hLL j`. Take `⟨χ, hχ, hc, hn⟩` from `GlobalTheory.T.exists_lubin_tate_character_unitary Bw.Kw`. Take `⟨φ, τ, hφc, hφ, hτ, hu⟩` from `GlobalTheory.T.local_galois_embedding_extension w A hA O Bw hI LL' hLL j`. Establish `hper` using `HP P AI hT Bw.Kw χ hχ hc`. Establish `hsplit : ∀ (μ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] Om l) (x : ↥Bw.Kw.1), μ x ∈ LL'.1` using `fun μ x => hLL (Bw.LL_split μ x)`.

Take `⟨hd, hm⟩` from `GlobalTheory.T.de_rham_rank_lubin_tate_line P AI hT Bw.Kw LL' hsplit χ hper τ`. Use `set ψ : ↥(GK Bw.Kw) →* (↥LL'.1)ˣ := (Units.map ((τ : ↥Bw.Kw.1 →+* ↥LL'.1) : ↥Bw.Kw.1 →* ↥LL'.1)).comp χ with hψ`. Establish `hnorm : ∀ x : ↥Bw.Kw.1, ‖((τ x : ↥LL'.1) : Om l)‖ = ‖(x : Om l)‖` using `fun x => GlobalTheory.CompanionTheory.EmbUniq.norm_coe_algHom τ x`. Use `⟨ψ.comp Bw.e.toMonoidHom, ?_, ?_, ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Establish `hc' : Continuous (fun g : ↥(Dec (F` using `E) A) => (((χ (Bw.e g) : (↥Bw.Kw.1)ˣ) : ↥Bw.Kw.1) : Om l)) := hc.comp Bw.e_cont`.

Establish `hc''` using `Metric.continuous_iff'.1 hc'`. Use `Metric.continuous_iff'.2 fun b ε hε => ?_` and prove the remaining obligations. Use `filter_upwards [hc'' b ε hε] with a h2`. Rewrite `h2`, the goal using `[dist_eq_norm]`. Establish `e : (((ψ.comp Bw.e.toMonoidHom) a : (↥LL'.1)ˣ) : ↥LL'.1).1 - (((ψ.comp Bw.e.toMonoidHom) b : (↥LL'.1)ˣ) : ↥LL'.1).1 = ((τ (((χ (Bw.e a) : (↥Bw.Kw.1)ˣ) : ↥Bw.Kw.1) - ((χ (Bw.e b) : (↥Bw.Kw.1)ˣ) : ↥Bw.Kw.1)) : ↥LL'.1) : Om l)`.

Simplify using `[hψ]`. Use `lt_of_eq_of_lt ?_ h2` and prove the remaining obligations. Use `(congrArg norm e).trans ?_` and prove the remaining obligations. Rewrite using `[hnorm]`. Both sides reduce to the same expression.

Introduce `g`. Simplify `(hnorm _).trans (hn (Bw.e g))` using `[hψ]`. Use `show Module.finrank _ ↥(DdR (P.PD Bw.Kw) (Bw.repE LL' _)) = _`. Rewrite using `[repE_eq]`. Conclude with `hd`.

Introduce `τ' a show multV (P.PD Bw.Kw) (Bw.repE LL' _) τ' a = _`. Rewrite using `[repE_eq, hm τ' a]`. Simplify using `only [hu τ']`. Introduce `x σ hx hσ hart'`. Establish `h1` using `GlobalTheory.CompanionTheory.LTLink.link w A hA O Bw hI art hart χ hχ φ hφc hφ x σ hx hσ hart'`.

Take `⟨hxk, hxj⟩` from `hτ (x : w.adicCompletion E)`. Rewrite using `[← hxj]`. Establish `: (χ (Bw.e σ) : ↥Bw.Kw.1) = ⟨φ x, hxk⟩` using `Subtype.ext h1`. Simplify using `[hψ, this]`.
-/
theorem lubinTate_at_embedding (HP : LTPeriods) : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied6 l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O),
      GlobalTheory.Pst.Induces Bw →
    ∀ (art : Ideles E →* Gab E Ω), IsGlobalArtin art →
    ∀ (LL' : FinExt l), Bw.LL.1 ≤ LL'.1 → ∀ (j : {j : w.adicCompletion E →+* Qbar l // Continuous j}),
    ∃ lam : ↥(Dec (F := E) A) →* (↥LL'.1)ˣ,
      Continuous (fun g => ((lam g : ↥LL'.1) : Qbar l)) ∧ (∀ g, ‖((lam g : ↥LL'.1) : Qbar l)‖ = 1) ∧
      PositivityTheory.HodgeLocalCharacter.HLC.IsdRJ Bw P LL' lam
        (fun τ' => if IsInduced Bw (j.1.comp (algebraMap E (w.adicCompletion E))) τ' then -1 else 0) ∧
      ∀ (x : (w.adicCompletion E)ˣ) (σ : ↥(Dec (F := E) A)), IsUnitAt w x → (σ : G E Ω) ∈ Ine (F := E) A →
        art (localIdele E w x) = toAb E Ω σ → ((lam σ : ↥LL'.1) : Qbar l) = j.1 x := by
  intro E Ω _ _ _ _ _ l _ P AI hT w A hA O _ _ _ Bw hI art hart LL' hLL j
  obtain ⟨χ, hχ, hc, hn⟩ := GlobalTheory.T.exists_lubin_tate_character_unitary Bw.Kw
  obtain ⟨φ, τ, hφc, hφ, hτ, hu⟩ := GlobalTheory.T.local_galois_embedding_extension w A hA O Bw hI LL' hLL j
  have hper := HP P AI hT Bw.Kw χ hχ hc
  have hsplit : ∀ (μ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] Om l) (x : ↥Bw.Kw.1), μ x ∈ LL'.1 :=
    fun μ x => hLL (Bw.LL_split μ x)
  obtain ⟨hd, hm⟩ := GlobalTheory.T.de_rham_rank_lubin_tate_line P AI hT Bw.Kw LL' hsplit χ hper τ
  set ψ : ↥(GK Bw.Kw) →* (↥LL'.1)ˣ := (Units.map ((τ : ↥Bw.Kw.1 →+* ↥LL'.1) : ↥Bw.Kw.1 →* ↥LL'.1)).comp χ with hψ
  have hnorm : ∀ x : ↥Bw.Kw.1, ‖((τ x : ↥LL'.1) : Om l)‖ = ‖(x : Om l)‖ := fun x =>
    GlobalTheory.CompanionTheory.EmbUniq.norm_coe_algHom τ x
  refine ⟨ψ.comp Bw.e.toMonoidHom, ?_, ?_, ⟨?_, ?_⟩, ?_⟩
  · have hc' : Continuous (fun g : ↥(Dec (F := E) A) =>
        (((χ (Bw.e g) : (↥Bw.Kw.1)ˣ) : ↥Bw.Kw.1) : Om l)) := hc.comp Bw.e_cont
    have hc'' := Metric.continuous_iff'.1 hc'
    refine Metric.continuous_iff'.2 fun b ε hε => ?_
    filter_upwards [hc'' b ε hε] with a h2
    rw [dist_eq_norm] at h2 ⊢
    have e : (((ψ.comp Bw.e.toMonoidHom) a : (↥LL'.1)ˣ) : ↥LL'.1).1 -
        (((ψ.comp Bw.e.toMonoidHom) b : (↥LL'.1)ˣ) : ↥LL'.1).1 =
        ((τ (((χ (Bw.e a) : (↥Bw.Kw.1)ˣ) : ↥Bw.Kw.1) - ((χ (Bw.e b) : (↥Bw.Kw.1)ˣ) : ↥Bw.Kw.1)) : ↥LL'.1) : Om l) := by
      simp [hψ]
    refine lt_of_eq_of_lt ?_ h2
    refine (congrArg norm e).trans ?_
    rw [hnorm]
    rfl
  · intro g
    simpa [hψ] using (hnorm _).trans (hn (Bw.e g))
  · show Module.finrank _ ↥(DdR (P.PD Bw.Kw) (Bw.repE LL' _)) = _
    rw [repE_eq]; exact hd
  · intro τ' a
    show multV (P.PD Bw.Kw) (Bw.repE LL' _) τ' a = _
    rw [repE_eq, hm τ' a]
    simp only [hu τ']
  · intro x σ hx hσ hart'
    have h1 := GlobalTheory.CompanionTheory.LTLink.link w A hA O Bw hI art hart χ hχ φ hφc hφ x σ hx hσ hart'
    obtain ⟨hxk, hxj⟩ := hτ (x : w.adicCompletion E)
    rw [← hxj]
    have : (χ (Bw.e σ) : ↥Bw.Kw.1) = ⟨φ x, hxk⟩ := Subtype.ext h1
    simp [hψ, this]
end PositivityTheory.SecR.Hladr

namespace PositivityTheory.SecR.Hladr

/- English proof (translation)
Rewrite using `[MonoidHom.finsetProd_apply, Units.coe_prod, map_prod]`. Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[MonoidHom.zpow_apply, Units.val_zpow_eq_zpow_val, map_zpow₀]`.
-/
theorem coe_units_prod_zpow_hlc {ι' G : Type} [Fintype ι'] [Group G] {K L : Type} [Field K] [Field L]
    (f : K →+* L) (lam : ι' → G →* Kˣ) (m : ι' → ℤ) (g : G) :
    f (((∏ j, lam j ^ m j) g : Kˣ) : K) = ∏ j, f ((lam j g : Kˣ) : K) ^ m j := by
  rw [MonoidHom.finsetProd_apply, Units.coe_prod, map_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [MonoidHom.zpow_apply, Units.val_zpow_eq_zpow_val, map_zpow₀]

end PositivityTheory.SecR.Hladr

namespace PositivityTheory.SecR.Hladr

open PositivityTheory.HodgeLocalCharacter.HLC

section Jumps

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime]
  (P : LocPrime l) (AI : LocAinf l P) (hT : Nonempty (LocTied6 l P AI))
  {w : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω} (hA : IsPlaceOver A w)
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O)
  (hI : GlobalTheory.Pst.Induces Bw) (LL' : FinExt l) (hLL : Bw.LL.1 ≤ LL'.1)

include hT hA hI hLL

/- English proof (translation)
Use `GlobalTheory.T.local_character_induced_agree P AI hT w A hA O Bw hI LL' hLL 1 ?_ ?_ ⊤ ?_ ?_` and prove the remaining obligations. Simplify using `only [MonoidHom.one_apply, Units.val_one]`. Conclude with `continuous_const`. Introduce `g`. Simplify using the standard rewrite rules.

Rewrite using `[Subgroup.coe_top]`. Conclude with `isOpen_univ`. Introduce `σ _ _`. Both sides reduce to the same expression.
-/
theorem isdRJ_one_hlc : IsdRJ Bw P LL' 1 0 := by
  refine GlobalTheory.T.local_character_induced_agree P AI hT w A hA O Bw hI LL' hLL 1 ?_ ?_ ⊤ ?_ ?_
  · simp only [MonoidHom.one_apply, Units.val_one]
    exact continuous_const
  · intro g
    simp
  · rw [Subgroup.coe_top]
    exact isOpen_univ
  · intro σ _ _
    rfl

/- English proof (translation)
Use `Int.induction_on k ?_ ?_ ?_` and prove the remaining obligations. Simplify using `using isdRJ_one_hlc P AI hT hA Bw hI LL' hLL`. Introduce `i ih`. Rewrite using `[zpow_add_one, add_smul, one_smul]`. Conclude with `GlobalTheory.T.local_character_induced_tied P AI hT w A hA O Bw hI LL' hLL _ _ _ _ ih h`.

Introduce `i ih`. Rewrite using `[zpow_sub_one, sub_smul, one_smul, sub_eq_add_neg]`. Conclude with `GlobalTheory.T.local_character_induced_tied P AI hT w A hA O Bw hI LL' hLL _ _ _ _ ih (GlobalTheory.T.local_character_induced_tied_six P AI hT w A hA O Bw hI LL' hLL _ _ h)`.
-/
theorem isdRJ_zpow_hlc {ψ : ↥(Dec (F := E) A) →* (↥LL'.1)ˣ} {J : (↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1) → ℤ}
    (h : IsdRJ Bw P LL' ψ J) (k : ℤ) : IsdRJ Bw P LL' (ψ ^ k) (k • J) := by
  refine Int.induction_on k ?_ ?_ ?_
  · simpa using isdRJ_one_hlc P AI hT hA Bw hI LL' hLL
  · intro i ih
    rw [zpow_add_one, add_smul, one_smul]
    exact GlobalTheory.T.local_character_induced_tied P AI hT w A hA O Bw hI LL' hLL _ _ _ _ ih h
  · intro i ih
    rw [zpow_sub_one, sub_smul, one_smul, sub_eq_add_neg]
    exact GlobalTheory.T.local_character_induced_tied P AI hT w A hA O Bw hI LL' hLL _ _ _ _ ih
      (GlobalTheory.T.local_character_induced_tied_six P AI hT w A hA O Bw hI LL' hLL _ _ h)

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using isdRJ_one_hlc P AI hT hA Bw hI LL' hLL`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.prod_insert ha, Finset.sum_insert ha]`. Conclude with `GlobalTheory.T.local_character_induced_tied P AI hT w A hA O Bw hI LL' hLL _ _ _ _ (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))`.
-/
theorem isdRJ_prod_hlc {ι' : Type} (s : Finset ι') (ψ : ι' → (↥(Dec (F := E) A) →* (↥LL'.1)ˣ))
    (J : ι' → (↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1) → ℤ) (h : ∀ i ∈ s, IsdRJ Bw P LL' (ψ i) (J i)) :
    IsdRJ Bw P LL' (∏ i ∈ s, ψ i) (∑ i ∈ s, J i) := by
  induction s using Finset.induction_on with
  | empty => simpa using isdRJ_one_hlc P AI hT hA Bw hI LL' hLL
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact GlobalTheory.T.local_character_induced_tied P AI hT w A hA O Bw hI LL' hLL _ _ _ _ (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end Jumps

end PositivityTheory.SecR.Hladr

namespace PositivityTheory.SecR.Hladr

open PositivityTheory.HodgeLocalCharacter.HLC

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ l _ P AI hT ι art hart χ n μ hχ hμ hL w A hA O _ _ _ Bw hI`. Take `⟨LL', ψ, hLL, hmod, hψμ, hψc, hψn⟩` from `GlobalTheory.T.local_character_finite_extension μ hμ w A hA O Bw`. Establish `: Finite {j : w.adicCompletion E →+* Qbar l // Continuous j}` using `finite_contEmb w`. Establish `: Fintype {j : w.adicCompletion E →+* Qbar l // Continuous j}` using `Fintype.ofFinite _`. Use `choose lam hlc hln hlJ hlx using fun j : {j : w.adicCompletion E →+* Qbar l // Continuous j} => lubinTate_at_embedding HP P AI hT w A hA O Bw hI art hart LL' hLL j`.

Set `nj : {j : w.adicCompletion E →+* Qbar l // Continuous j} → ℤ` to `fun j => n ((ι.toRingHom.comp j.1).comp (algebraMap E (w.adicCompletion E)))`. Set `Jj : {j : w.adicCompletion E →+* Qbar l // Continuous j} → (↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1) → ℤ` to `fun j τ' => if IsInduced Bw (j.1.comp (algebraMap E (w.adicCompletion E))) τ' then -1 else 0`. Set `Λ : ↥(Dec (F` to `E) A) →* (↥LL'.1)ˣ := ∏ j, lam j ^ nj j`. Establish `hΛ : IsdRJ Bw P LL' Λ (∑ j, nj j • Jj j)` using `isdRJ_prod_hlc P AI hT hA Bw hI LL' hLL _ _ _ fun j _ => isdRJ_zpow_hlc P AI hT hA Bw hI LL' hLL (hlJ j) (nj j)`. Establish `hne : ∀ j g, ((lam j g : ↥LL'.1) : Qbar l) ≠ 0` using `fun j g => norm_ne_zero_iff.mp (by rw [hln j g]; exact one_ne_zero)`.

Establish `hΛv : ∀ g, ((Λ g : ↥LL'.1) : Qbar l) = ∏ j, ((lam j g : ↥LL'.1) : Qbar l) ^ nj j` using `fun g => coe_units_prod_zpow_hlc LL'.1.val.toRingHom lam nj g`. Establish `hΛc : Continuous fun g => ((Λ g : ↥LL'.1) : Qbar l)`. Simplify using `only [hΛv]`. Conclude with `continuous_finsetProd _ fun j _ => (hlc j).zpow₀ _ fun g => Or.inl (hne j g)`. Establish `hΛne : ∀ g, ((Λ g : ↥LL'.1) : Qbar l) ≠ 0` using `fun g => by`.

Rewrite using `[hΛv]`. Conclude with `Finset.prod_ne_zero_iff.mpr fun j _ => zpow_ne_zero _ (hne j g)`. Set `φ : ↥(Dec (F` to `E) A) →* (↥LL'.1)ˣ := ψ * Λ⁻¹`. Establish `hφv : ∀ g, ((φ g : ↥LL'.1) : Qbar l) = ((ψ g : ↥LL'.1) : Qbar l) * ((Λ g : ↥LL'.1) : Qbar l)⁻¹`. Introduce `g`.

Simplify using `[φ]`. Establish `hφc : Continuous fun g => ((φ g : ↥LL'.1) : Qbar l)`. Simplify using `only [hφv]`. Conclude with `hψc.mul (hΛc.inv₀ hΛne)`. Establish `hφn : ∀ g, ‖((φ g : ↥LL'.1) : Qbar l)‖ = 1`.

Introduce `g`. Rewrite using `[hφv, norm_mul, norm_inv, hψn, hΛv, norm_prod]`. Simplify using `[norm_zpow, hln]`. Take `⟨U, hUo, hUu, hUχ⟩` from `GlobalTheory.T.exists_open_subgroup_heckeChar_eq_one χ w`. Take `⟨V, hVo, hV⟩` from `GlobalTheory.T.galois_open_subgroup_local_units (l := l) art hart w A hA U hUo hUu`.

Establish `hφ0 : IsdRJ Bw P LL' φ 0`. Use `GlobalTheory.T.local_character_induced_agree P AI hT w A hA O Bw hI LL' hLL φ hφc hφn V hVo ?_` and prove the remaining obligations. Introduce `σ hσV hσI`. Take `⟨x, hxU, hx⟩` from `hV σ hσV hσI`. Establish `h1` using `GlobalTheory.T.galois_character_artin_compat ι art χ n μ hL w x σ hx`.

Rewrite `h1` using `[hUχ x hxU, Units.val_one, map_one, one_mul]`. Establish `h2 : ∀ j, ((lam j σ : ↥LL'.1) : Qbar l) = j.1 x` using `fun j => hlx j x σ (hUu x hxU) hσI hx`. Establish `hψΛ : ((ψ σ : ↥LL'.1) : Qbar l) = ((Λ σ : ↥LL'.1) : Qbar l)`. Rewrite using `[hψμ, h1, hΛv]`. Simplify using `only [h2]`.

Unfold `locPow`. Rewrite using `[finprod_eq_prod_of_fintype]`. Establish `hψΛ' : ψ σ = Λ σ` using `Units.ext (Subtype.ext hψΛ)`. Use `show ψ σ * Λ⁻¹ σ = 1`. Rewrite using `[MonoidHom.inv_apply, hψΛ', mul_inv_cancel]`.

Establish `hψJ : IsdRJ Bw P LL' ψ (0 + ∑ j, nj j • Jj j)`. Use `GlobalTheory.T.local_character_induced_tied P AI hT w A hA O Bw hI LL' hLL φ Λ _ _ hφ0 hΛ` as an intermediate fact. Simplify `this` using `[φ]`. Use `⟨⟨LL', _, hmod, hψJ.1⟩, ?_⟩` and prove the remaining obligations. Introduce `τ LL'' τ'' hτ`.

Set `τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1` to `(LL''.1.val.comp τ'').codRestrict LL'.1.toSubalgebra fun x => hLL (Bw.LL_split _ x)`. Establish `hτ' : IsInduced Bw τ τ'` using `fun x => hτ x`. Use `⟨LL', _, hmod, hψJ.1, τ', hτ', fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[hψJ.2 τ' a]`. Take `⟨j0, hj0, huniq⟩` from `GlobalTheory.T.unique_embedding_extension (l := l) w A hA O Bw hI LL' τ'`.

Establish `hj0E : j0.1.comp (algebraMap E (w.adicCompletion E)) = τ` using `RingHom.ext fun x => (hj0 x).trans (hτ' x).symm`. Establish `hsum : (0 + ∑ j, nj j • Jj j) τ' = -n (ι.toRingHom.comp τ)`. Simplify using `only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, zero_add]`. Rewrite using `[Finset.sum_eq_single j0]`. Simplify using `only [Jj, if_pos hj0, nj, smul_eq_mul, mul_neg, mul_one, ← hj0E, RingHom.comp_assoc]`.

Introduce `b _ hb`. Establish `: ¬ IsInduced Bw (b.1.comp (algebraMap E (w.adicCompletion E))) τ'` using `fun h => hb (huniq b h)`. Simplify using `only [Jj, if_neg this, smul_zero]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ j0) h`.

Rewrite using `[hsum, Multiset.count_singleton]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem field_of_ltPeriods (HP : LTPeriods) : GlobalTheory.Published.HeckeLAdicCharacterDeRham := by
  intro E Ω _ _ _ _ _ l _ P AI hT ι art hart χ n μ hχ hμ hL w A hA O _ _ _ Bw hI
  obtain ⟨LL', ψ, hLL, hmod, hψμ, hψc, hψn⟩ := GlobalTheory.T.local_character_finite_extension μ hμ w A hA O Bw
  have : Finite {j : w.adicCompletion E →+* Qbar l // Continuous j} := finite_contEmb w
  have : Fintype {j : w.adicCompletion E →+* Qbar l // Continuous j} := Fintype.ofFinite _
  choose lam hlc hln hlJ hlx using
    fun j : {j : w.adicCompletion E →+* Qbar l // Continuous j} =>
      lubinTate_at_embedding HP P AI hT w A hA O Bw hI art hart LL' hLL j
  let nj : {j : w.adicCompletion E →+* Qbar l // Continuous j} → ℤ :=
    fun j => n ((ι.toRingHom.comp j.1).comp (algebraMap E (w.adicCompletion E)))
  let Jj : {j : w.adicCompletion E →+* Qbar l // Continuous j} → (↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1) → ℤ :=
    fun j τ' => if IsInduced Bw (j.1.comp (algebraMap E (w.adicCompletion E))) τ' then -1 else 0
  let Λ : ↥(Dec (F := E) A) →* (↥LL'.1)ˣ := ∏ j, lam j ^ nj j
  have hΛ : IsdRJ Bw P LL' Λ (∑ j, nj j • Jj j) :=
    isdRJ_prod_hlc P AI hT hA Bw hI LL' hLL _ _ _ fun j _ =>
      isdRJ_zpow_hlc P AI hT hA Bw hI LL' hLL (hlJ j) (nj j)
  have hne : ∀ j g, ((lam j g : ↥LL'.1) : Qbar l) ≠ 0 := fun j g =>
    norm_ne_zero_iff.mp (by rw [hln j g]; exact one_ne_zero)
  have hΛv : ∀ g, ((Λ g : ↥LL'.1) : Qbar l) = ∏ j, ((lam j g : ↥LL'.1) : Qbar l) ^ nj j := fun g =>
    coe_units_prod_zpow_hlc LL'.1.val.toRingHom lam nj g
  have hΛc : Continuous fun g => ((Λ g : ↥LL'.1) : Qbar l) := by
    simp only [hΛv]
    exact continuous_finsetProd _ fun j _ => (hlc j).zpow₀ _ fun g => Or.inl (hne j g)
  have hΛne : ∀ g, ((Λ g : ↥LL'.1) : Qbar l) ≠ 0 := fun g => by
    rw [hΛv]
    exact Finset.prod_ne_zero_iff.mpr fun j _ => zpow_ne_zero _ (hne j g)
  let φ : ↥(Dec (F := E) A) →* (↥LL'.1)ˣ := ψ * Λ⁻¹
  have hφv : ∀ g, ((φ g : ↥LL'.1) : Qbar l) = ((ψ g : ↥LL'.1) : Qbar l) * ((Λ g : ↥LL'.1) : Qbar l)⁻¹ := by
    intro g
    simp [φ]
  have hφc : Continuous fun g => ((φ g : ↥LL'.1) : Qbar l) := by
    simp only [hφv]
    exact hψc.mul (hΛc.inv₀ hΛne)
  have hφn : ∀ g, ‖((φ g : ↥LL'.1) : Qbar l)‖ = 1 := by
    intro g
    rw [hφv, norm_mul, norm_inv, hψn, hΛv, norm_prod]
    simp [norm_zpow, hln]
  obtain ⟨U, hUo, hUu, hUχ⟩ := GlobalTheory.T.exists_open_subgroup_heckeChar_eq_one χ w
  obtain ⟨V, hVo, hV⟩ := GlobalTheory.T.galois_open_subgroup_local_units (l := l) art hart w A hA U hUo hUu
  have hφ0 : IsdRJ Bw P LL' φ 0 := by
    refine GlobalTheory.T.local_character_induced_agree P AI hT w A hA O Bw hI LL' hLL φ hφc hφn V hVo ?_
    intro σ hσV hσI
    obtain ⟨x, hxU, hx⟩ := hV σ hσV hσI
    have h1 := GlobalTheory.T.galois_character_artin_compat ι art χ n μ hL w x σ hx
    rw [hUχ x hxU, Units.val_one, map_one, one_mul] at h1
    have h2 : ∀ j, ((lam j σ : ↥LL'.1) : Qbar l) = j.1 x := fun j => hlx j x σ (hUu x hxU) hσI hx
    have hψΛ : ((ψ σ : ↥LL'.1) : Qbar l) = ((Λ σ : ↥LL'.1) : Qbar l) := by
      rw [hψμ, h1, hΛv]
      simp only [h2]
      unfold locPow
      rw [finprod_eq_prod_of_fintype]
    have hψΛ' : ψ σ = Λ σ := Units.ext (Subtype.ext hψΛ)
    show ψ σ * Λ⁻¹ σ = 1
    rw [MonoidHom.inv_apply, hψΛ', mul_inv_cancel]
  have hψJ : IsdRJ Bw P LL' ψ (0 + ∑ j, nj j • Jj j) := by
    have := GlobalTheory.T.local_character_induced_tied P AI hT w A hA O Bw hI LL' hLL φ Λ _ _ hφ0 hΛ
    simpa [φ] using this
  refine ⟨⟨LL', _, hmod, hψJ.1⟩, ?_⟩
  intro τ LL'' τ'' hτ
  let τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1 :=
    (LL''.1.val.comp τ'').codRestrict LL'.1.toSubalgebra fun x => hLL (Bw.LL_split _ x)
  have hτ' : IsInduced Bw τ τ' := fun x => hτ x
  refine ⟨LL', _, hmod, hψJ.1, τ', hτ', fun a => ?_⟩
  rw [hψJ.2 τ' a]
  obtain ⟨j0, hj0, huniq⟩ := GlobalTheory.T.unique_embedding_extension (l := l) w A hA O Bw hI LL' τ'
  have hj0E : j0.1.comp (algebraMap E (w.adicCompletion E)) = τ :=
    RingHom.ext fun x => (hj0 x).trans (hτ' x).symm
  have hsum : (0 + ∑ j, nj j • Jj j) τ' = -n (ι.toRingHom.comp τ) := by
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, zero_add]
    rw [Finset.sum_eq_single j0]
    · simp only [Jj, if_pos hj0, nj, smul_eq_mul, mul_neg, mul_one, ← hj0E, RingHom.comp_assoc]
    · intro b _ hb
      have : ¬ IsInduced Bw (b.1.comp (algebraMap E (w.adicCompletion E))) τ' := fun h => hb (huniq b h)
      simp only [Jj, if_neg this, smul_zero]
    · intro h
      exact absurd (Finset.mem_univ j0) h
  rw [hsum, Multiset.count_singleton]
  split_ifs <;> simp
end PositivityTheory.SecR.Hladr
