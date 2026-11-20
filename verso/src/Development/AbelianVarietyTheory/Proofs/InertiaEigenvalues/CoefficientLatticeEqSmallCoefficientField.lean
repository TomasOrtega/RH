import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockOfApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarmonicPolynomialLattices
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

noncomputable section

namespace GlobalTheory.PlaceSmall

section BaseChange

variable {E K₀ K ι : Type} [Field E] [NumberField E] [Field K₀] [NumberField K₀] [Field K] [NumberField K] [Fintype ι]
  {n : ℕ}

/- English proof (translation)
Unfold `nabAtr nabK at hx ⊢`. Rewrite `hx`, the goal using `[Submodule.mem_comap]`. Express the relevant statement in the definitionally equal form `MvPolynomial.map f x.1 ∈ nabP lam fun τ => dualFr (tauLat (fun τ => f.comp (emb τ)) τ M)`. Express the relevant statement in the definitionally equal form `x.1 ∈ nabP lam (fun τ => dualFr (tauLat emb τ M)) at hx`. Use `GlobalTheory.TransLattice.mem_of_forall_mem_locP _ fun w => ?_` and prove the remaining obligations.

Choose the witnesses or unpack the hypotheses as in `⟨w₀, hw₀⟩ : ∃ Q : HeightOneSpectrum (𝓞 K₀), ∀ r : 𝓞 K₀, r ∈ Q.asIdeal ↔ RingOfIntegers.mapRingHom f r ∈ w.asIdeal := by`. Use `⟨⟨w.asIdeal.comap (RingOfIntegers.mapRingHom f), Ideal.comap_isPrime _ _, fun h => ?_⟩, fun _ => Iff.rfl⟩` and prove the remaining obligations. Establish `h1 : ((Ideal.absNorm w.asIdeal : ℕ) : 𝓞 K₀) ∈ w.asIdeal.comap (RingOfIntegers.mapRingHom f)`. Rewrite using `[Ideal.mem_comap, map_natCast]`. Conclude with `Ideal.absNorm_mem _`.

Rewrite `h1` using `[h, Ideal.mem_bot]`. Conclude with `w.ne_bot (Ideal.absNorm_eq_zero_iff.1 (by exact_mod_cast h1))`. Establish `hw : ∀ t : 𝓞 K₀, t ∉ w₀.asIdeal → RingOfIntegers.mapRingHom f t ∉ w.asIdeal` using `fun t ht h => ht ((hw₀ t).2 h)`. Take `⟨hLoc, -, -⟩` from `GlobalTheory.TransLoc.nabDelLoc_free_leVV`. Establish `hT : ∀ τ, Submodule.IsLattice K₀ (tauLat emb τ M)` using `fun τ => tauLatLattice E K₀ ι n emb τ M hM`.

Use `choose C hC using fun τ => basisAtEx K₀ n (tauLat emb τ M) (hT τ) w₀`. Set `B₀ : ι → GL (Fin n) K₀` to `fun τ => inside₂ K₀ n (C τ)`. Establish `hB₀ : ∀ τ, IsBasisAt w₀ (dualFr (tauLat emb τ M)) (B₀ τ)` using `fun τ => GlobalTheory.DualWeylDual.isBasisAt_dualFr w₀ (hT τ).fg (hC τ)`. Establish `hB : ∀ τ, IsBasisAt w (dualFr (tauLat (fun τ => f.comp (emb τ)) τ M)) (Formalism.UG.bc f (B₀ τ))` using `fun τ => GlobalTheory.NabBC.isBasisAt_dualFr_tauLat_comp f emb τ M hM w₀ w hw (C τ) (hC τ)`. Establish `L1` using `(hLoc K ι n lam _ (fun τ => dualFr_tauLat_isLattice (fun τ => f.comp (emb τ)) τ M hM) w _ hB).1`.

Establish `L0` using `(hLoc K₀ ι n lam _ (fun τ => dualFr_tauLat_isLattice emb τ M hM) w₀ B₀ hB₀).1`. Establish `hx0 : x.1 ∈ Formalism.HermitianLatticesTheory.localization₂ w₀.asIdeal (nabP lam fun τ => dualFr (tauLat emb τ M))` using `GlobalTheory.NabBC.mem_localization_of_mem' _ hx`. Rewrite `hx0` using `[L0]`. Take `⟨g, ⟨s, hs, hsg⟩, hg⟩` from `hx0`. Rewrite using `[L1]`.

Use `⟨MvPolynomial.map f g, ⟨RingOfIntegers.mapRingHom f s, hw s hs, ?_⟩, ?_⟩` and prove the remaining obligations. Use `(congrArg (· ∈ nabStd K lam) (GlobalTheory.NabBC.map_smul_int f s g)).mpr ?_` and prove the remaining obligations. Establish `h1` using `(GlobalTheory.StdBaseChange.std_baseChange (𝓞 K) K K₀ ι f (RingOfIntegers.mapRingHom f) (fun r => rfl) n lam).1`. Establish `h2` using `(GlobalTheory.StdBaseChange.std_baseChange (𝓞 K) K K ι (RingHom.id K) (RingHom.id _) (fun r => rfl) n lam).1`. Establish `h3 : MvPolynomial.map f (s • g) ∈ Submodule.span (𝓞 K) (MvPolynomial.map f '' (nabStd K₀ lam : Set (Pol K₀ ι n)))` using `Submodule.subset_span ⟨_, hsg, rfl⟩`.

Rewrite `h3` using `[h1, ← h2]`. Establish `h4 : (MvPolynomial.map (RingHom.id K) '' (nabStd K lam : Set (Pol K ι n))) = (nabStd K lam : Set (Pol K ι n))`. Use extensionality with `y`. Simplify using `[MvPolynomial.map_id]`. Rewrite `h3` using `[h4, Submodule.span_eq]`.

Conclude with `h3`. Express the relevant statement in the definitionally equal form `actP lam (fun τ => Formalism.UG.bc f (B₀ τ)) (MvPolynomial.map f g) = MvPolynomial.map f x.1`. Rewrite using `[← GlobalTheory.ValCmp.use₂]`. Conclude with `congrArg (MvPolynomial.map f) hg`.
-/
theorem map_mem_nabAtr (f : K₀ →+* K) (emb : ι → E →+* K₀) (lam : ι → DomWeight n) (M : Submodule (𝓞 E) (Fin n → E))
    (hM : Submodule.IsLattice E M) {x : VV K₀ lam} (hx : x ∈ nabAtr emb lam M) :
    (⟨MvPolynomial.map f x.1, GlobalTheory.Proof.TensorMapDescent.map_mem_VV f lam _ x.2⟩ : VV K lam) ∈
      nabAtr (fun τ => f.comp (emb τ)) lam M := by
  classical
  unfold nabAtr nabK at hx ⊢
  rw [Submodule.mem_comap] at hx ⊢
  change MvPolynomial.map f x.1 ∈ nabP lam fun τ => dualFr (tauLat (fun τ => f.comp (emb τ)) τ M)
  change x.1 ∈ nabP lam (fun τ => dualFr (tauLat emb τ M)) at hx
  refine GlobalTheory.TransLattice.mem_of_forall_mem_locP _ fun w => ?_
  obtain ⟨w₀, hw₀⟩ : ∃ Q : HeightOneSpectrum (𝓞 K₀),
      ∀ r : 𝓞 K₀, r ∈ Q.asIdeal ↔ RingOfIntegers.mapRingHom f r ∈ w.asIdeal := by
    refine ⟨⟨w.asIdeal.comap (RingOfIntegers.mapRingHom f), Ideal.comap_isPrime _ _, fun h => ?_⟩, fun _ => Iff.rfl⟩
    have h1 : ((Ideal.absNorm w.asIdeal : ℕ) : 𝓞 K₀) ∈ w.asIdeal.comap (RingOfIntegers.mapRingHom f) := by
      rw [Ideal.mem_comap, map_natCast]
      exact Ideal.absNorm_mem _
    rw [h, Ideal.mem_bot] at h1
    exact w.ne_bot (Ideal.absNorm_eq_zero_iff.1 (by exact_mod_cast h1))
  have hw : ∀ t : 𝓞 K₀, t ∉ w₀.asIdeal → RingOfIntegers.mapRingHom f t ∉ w.asIdeal :=
    fun t ht h => ht ((hw₀ t).2 h)
  obtain ⟨hLoc, -, -⟩ := GlobalTheory.TransLoc.nabDelLoc_free_leVV
  have hT : ∀ τ, Submodule.IsLattice K₀ (tauLat emb τ M) := fun τ => tauLatLattice E K₀ ι n emb τ M hM
  choose C hC using fun τ => basisAtEx K₀ n (tauLat emb τ M) (hT τ) w₀
  let B₀ : ι → GL (Fin n) K₀ := fun τ => inside₂ K₀ n (C τ)
  have hB₀ : ∀ τ, IsBasisAt w₀ (dualFr (tauLat emb τ M)) (B₀ τ) := fun τ =>
    GlobalTheory.DualWeylDual.isBasisAt_dualFr w₀ (hT τ).fg (hC τ)
  have hB : ∀ τ, IsBasisAt w (dualFr (tauLat (fun τ => f.comp (emb τ)) τ M)) (Formalism.UG.bc f (B₀ τ)) := fun τ =>
    GlobalTheory.NabBC.isBasisAt_dualFr_tauLat_comp f emb τ M hM w₀ w hw (C τ) (hC τ)
  have L1 := (hLoc K ι n lam _ (fun τ => dualFr_tauLat_isLattice (fun τ => f.comp (emb τ)) τ M hM) w _ hB).1
  have L0 := (hLoc K₀ ι n lam _ (fun τ => dualFr_tauLat_isLattice emb τ M hM) w₀ B₀ hB₀).1
  have hx0 : x.1 ∈ Formalism.HermitianLatticesTheory.localization₂ w₀.asIdeal (nabP lam fun τ => dualFr (tauLat emb τ M)) :=
    GlobalTheory.NabBC.mem_localization_of_mem' _ hx
  rw [L0] at hx0
  obtain ⟨g, ⟨s, hs, hsg⟩, hg⟩ := hx0
  rw [L1]
  refine ⟨MvPolynomial.map f g, ⟨RingOfIntegers.mapRingHom f s, hw s hs, ?_⟩, ?_⟩
  · refine (congrArg (· ∈ nabStd K lam) (GlobalTheory.NabBC.map_smul_int f s g)).mpr ?_
    have h1 := (GlobalTheory.StdBaseChange.std_baseChange (𝓞 K) K K₀ ι f (RingOfIntegers.mapRingHom f) (fun r => rfl) n lam).1
    have h2 := (GlobalTheory.StdBaseChange.std_baseChange (𝓞 K) K K ι (RingHom.id K) (RingHom.id _) (fun r => rfl) n lam).1
    have h3 : MvPolynomial.map f (s • g) ∈ Submodule.span (𝓞 K) (MvPolynomial.map f '' (nabStd K₀ lam : Set (Pol K₀ ι n))) :=
      Submodule.subset_span ⟨_, hsg, rfl⟩
    rw [h1, ← h2] at h3
    have h4 : (MvPolynomial.map (RingHom.id K) '' (nabStd K lam : Set (Pol K ι n))) = (nabStd K lam : Set (Pol K ι n)) := by
      ext y
      simp [MvPolynomial.map_id]
    rw [h4, Submodule.span_eq] at h3
    exact h3
  · change actP lam (fun τ => Formalism.UG.bc f (B₀ τ)) (MvPolynomial.map f g) = MvPolynomial.map f x.1
    rw [← GlobalTheory.ValCmp.use₂]
    exact congrArg (MvPolynomial.map f) hg

end BaseChange

/- English proof (translation)
Use `inf_le_inf_left _ (Submodule.comap_mono (Submodule.span_mono ?_))` and prove the remaining obligations. Introduce and unpack `_ ⟨F, hF, rfl⟩`. Use `⟨_, map_mem_nabAtr f emb w.lam M hM hF, funext fun y => ?_⟩` and prove the remaining obligations. Rewrite using `[coefFn, coefFn, MvPolynomial.eval₂Hom_map_hom]`.
-/
theorem harmLat_le {D : D7} {m n : ℕ} {K₀ K : Type} [Field K₀] [NumberField K₀] [Field K] [NumberField K] (f : K₀ →+* K)
    (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K₀)) (O : Subring ℂ) (w : GlobalTheory.ExportSeries.Weight D n) (B : GLR D n)
    {M : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (hM : Submodule.IsLattice D.host.E M) :
    harmLat (σ.comp f) emb O m w B M ≤ harmLat σ (fun τ => f.comp (emb τ)) O m w B M := by
  refine inf_le_inf_left _ (Submodule.comap_mono (Submodule.span_mono ?_))
  rintro _ ⟨F, hF, rfl⟩
  refine ⟨_, map_mem_nabAtr f emb w.lam M hM hF, funext fun y => ?_⟩
  rw [coefFn, coefFn, MvPolynomial.eval₂Hom_map_hom]

/- English proof (translation)
Introduce `D S T B hB O hO h`. Establish `hm : ∀ τ, B.w.p τ + B.w.q τ ≤ T.rank` using `fun τ => by`. Establish `h1` using `hB.sig τ`. Establish `h2` using `Formalism.BasicNotions.sig_sum _ hB.sigOK (Formalism.BasicNotions.TH.tauE D τ)`. Rewrite `h2` using `[← h1]`.

Conclude with `h2.le`. Establish `hM` using `GlobalTheory.SmallSpan.isLattice_latAt hB.frame h`. Use `le_antisymm (fun P hP => ?_) (harmLat_le D.LL0.val.toRingHom D.what₂.embLL (labLL0 D) O B.w B.F.BS hM)` and prove the remaining obligations. Establish `h1` using `GlobalTheory.SmallSpan.harmLat_le_span D.LL0.val.toRingHom D.what₂.embLL (labLL0 D) O O (fun a => hO ⟨a, rfl⟩) B.w B.F.BS hB.wt hm hM hP`. Rewrite `h1` using `[Submodule.span_eq]`.

Conclude with `h1`.
-/
theorem coefLat_eq_small : ∀ (D : D7) (S T : HSp D) (B : Base S T), B.Good → ∀ O : Subring ℂ, intLL D ≤ O → ∀ h, B.coefLat D.what₂.embLL (labLL D) O h = B.coefLat (embLL0 D) (labLL0 D) O h := by
  intro D S T B hB O hO h
  have hm : ∀ τ, B.w.p τ + B.w.q τ ≤ T.rank := fun τ => by
    have h1 := hB.sig τ
    have h2 := Formalism.BasicNotions.sig_sum _ hB.sigOK (Formalism.BasicNotions.TH.tauE D τ)
    rw [← h1] at h2
    exact h2.le
  have hM := GlobalTheory.SmallSpan.isLattice_latAt hB.frame h
  refine le_antisymm (fun P hP => ?_)
    (harmLat_le D.LL0.val.toRingHom D.what₂.embLL (labLL0 D) O B.w B.F.BS hM)
  have h1 := GlobalTheory.SmallSpan.harmLat_le_span D.LL0.val.toRingHom D.what₂.embLL (labLL0 D) O O (fun a => hO ⟨a, rfl⟩)
    B.w B.F.BS hB.wt hm hM hP
  rw [Submodule.span_eq] at h1
  exact h1

end GlobalTheory.PlaceSmall

end
