import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockOfApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeLowerBlockVectorMultipleKernelTranslate
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicIsometriesObj
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
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

namespace GlobalTheory.CentralTranslate

open GlobalTheory.FreeBlockTwist Matrix
open GlobalTheory.StdFrames (cpt)

variable {D : D7} {S T : HSp D}

/- English proof (translation)
Establish `hβ` using `hF.frS`. Apply the tactic sequence `choose m hm using fun ij : Fin S.rank × Fin S.rank => GlobalTheory.StdFrames.exists_pow_mul_mem (N := N) (((B.F.βS⁻¹).1 * (Formalism.L2.Theta.mt S k).map (toEAf D) * B.F.βS.1) ij.1 ij.2) fun PP hPP => conj_entry (toEAf D) B.F.βS hk (cpt PP) (ha PP hPP) (PP.adicCompletionIntegers …`. Use `⟨Finset.univ.sup m, fun l hl h x hx => ?_⟩` and prove the remaining obligations. Establish `hx' : ((Formalism.UG.bc (Lev.swapAE D) h.1)⁻¹).1 *ᵥ (fun i => eToEAf D (x i)) ∈ Formalism.L2.Herm.hatL (F` using `D.host.F) B.F.ΛS := hx`. Establish `h3` using `(hβ _).1 hx'`.

Establish `h4` using `(hβ _).2 (conj_mulVec _ B.F.βS _ (fun i j => hm (i, j) l ((Finset.le_sup (Finset.mem_univ _)).trans hl)) h3)`. Express the relevant statement in the definitionally equal form `((Formalism.UG.bc (Lev.swapAE D) (h * (finPt S k)⁻¹).1)⁻¹).1 *ᵥ (fun i => eToEAf D ((((N ^ l : ℕ) : 𝓞 D.host.E) • x) i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) B.F.ΛS`. Establish `e1 : (Formalism.UG.bc (Lev.swapAE D) (h * (finPt S k)⁻¹).1)⁻¹ = Formalism.UG.bc (Lev.swapAE D) (finPt S k).1 * (Formalism.UG.bc (Lev.swapAE D) h.1)⁻¹`. Rewrite using `[Subgroup.coe_mul, Subgroup.coe_inv, MonoidHom.map_mul, MonoidHom.map_inv, _root_.mul_inv_rev, inv_inv]`. Establish `e2 : (fun i => eToEAf D ((((N ^ l : ℕ) : 𝓞 D.host.E) • x) i)) = (N ^ l) • fun i => eToEAf D (x i)`.

Use function extensionality and compare the values at `i`. Rewrite using `[Nat.cast_smul_eq_nsmul, Pi.smul_apply, Pi.smul_apply, map_nsmul]`. Rewrite using `[e1, e2, Units.val_mul, mulVec_nsmul]`. Use `h4 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`.

Rewrite using `[Pi.smul_apply, nsmul_eq_mul]`. Both sides reduce to the same expression.
-/
theorem exists_pow_latAt {B : Base S T} (hF : B.F.Good) {a : AE D} {k : GA D S} (hk : SuppAt a S k) {N : ℕ}
    (ha : ∀ PP : Pl D.host.E, (N : 𝓞 D.host.E) ∉ PP.asIdeal → cpt PP (toEAf D (a + cA D a)) = 0) :
    ∃ m : ℕ, ∀ l, m ≤ l → ∀ h : Bridge.Gf S, ∀ x ∈ B.latAt h,
      ((N ^ l : ℕ) : 𝓞 D.host.E) • x ∈ B.latAt (h * (finPt S k)⁻¹) := by
  classical
  have hβ := hF.frS
  choose m hm using fun ij : Fin S.rank × Fin S.rank =>
    GlobalTheory.StdFrames.exists_pow_mul_mem (N := N)
      (((B.F.βS⁻¹).1 * (Formalism.L2.Theta.mt S k).map (toEAf D) * B.F.βS.1) ij.1 ij.2) fun PP hPP =>
      conj_entry (toEAf D) B.F.βS hk (cpt PP) (ha PP hPP) (PP.adicCompletionIntegers D.host.E) (zero_mem _) (one_mem _) ij.1 ij.2
  refine ⟨Finset.univ.sup m, fun l hl h x hx => ?_⟩
  have hx' : ((Formalism.UG.bc (Lev.swapAE D) h.1)⁻¹).1 *ᵥ (fun i => eToEAf D (x i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) B.F.ΛS := hx
  have h3 := (hβ _).1 hx'
  have h4 := (hβ _).2 (conj_mulVec _ B.F.βS _ (fun i j => hm (i, j) l ((Finset.le_sup (Finset.mem_univ _)).trans hl)) h3)
  change ((Formalism.UG.bc (Lev.swapAE D) (h * (finPt S k)⁻¹).1)⁻¹).1 *ᵥ (fun i => eToEAf D ((((N ^ l : ℕ) : 𝓞 D.host.E) • x) i)) ∈
    Formalism.L2.Herm.hatL (F := D.host.F) B.F.ΛS
  have e1 : (Formalism.UG.bc (Lev.swapAE D) (h * (finPt S k)⁻¹).1)⁻¹ =
      Formalism.UG.bc (Lev.swapAE D) (finPt S k).1 * (Formalism.UG.bc (Lev.swapAE D) h.1)⁻¹ := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, MonoidHom.map_mul, MonoidHom.map_inv, _root_.mul_inv_rev, inv_inv]
  have e2 : (fun i => eToEAf D ((((N ^ l : ℕ) : 𝓞 D.host.E) • x) i)) = (N ^ l) • fun i => eToEAf D (x i) := by
    funext i
    rw [Nat.cast_smul_eq_nsmul, Pi.smul_apply, Pi.smul_apply, map_nsmul]
  rw [e1, e2, Units.val_mul, mulVec_nsmul]
  convert h4 using 1
  funext i
  rw [Pi.smul_apply, nsmul_eq_mul]
  rfl

/- English proof (translation)
Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨F, hF, rfl⟩`. Establish `h3 : coefFn σ lam (((N : K) ^ GlobalTheory.NabScale.scaleExp lam • F : VV K lam) : Pol K D.what₂.Tau n) ∈ coefLatFn σ emb O lam M'` using `Submodule.subset_span ⟨_, nabAtr_scale emb lam N hM h1 h2 F hF, rfl⟩`. Establish `h4` using `Submodule.smul_mem _ ((⟨_, hO⟩ : O) ^ GlobalTheory.NabScale.scaleExp lam) h3`. Establish `h0 : (N : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 hN`.

Rewrite using `[SetLike.mem_coe]`. Use `h4 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `x`. Express the relevant statement in the definitionally equal form `_ = ((N : ℂ)⁻¹) ^ GlobalTheory.NabScale.scaleExp lam * coefFn σ lam ((N : K) ^ GlobalTheory.NabScale.scaleExp lam • F.1) x`. Rewrite using `[coefFn, coefFn, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval₂Hom_C, map_pow, map_natCast, inv_pow]`.

Clear the denominators using the available nonvanishing facts.
-/
theorem coefLatFn_le {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K)) (O : Subring ℂ)
    {n : ℕ} (lam : D.what₂.Tau → DomWeight n) {M M' : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {N : ℕ} (hN : N ≠ 0)
    (hO : (N : ℂ)⁻¹ ∈ O) (hM : Submodule.IsLattice D.host.E M) (h1 : ∀ x ∈ M, (N : 𝓞 D.host.E) • x ∈ M')
    (h2 : ∀ x ∈ M', (N : 𝓞 D.host.E) • x ∈ M) : coefLatFn σ emb O lam M ≤ coefLatFn σ emb O lam M' := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨F, hF, rfl⟩
  have h3 : coefFn σ lam (((N : K) ^ GlobalTheory.NabScale.scaleExp lam • F : VV K lam) : Pol K D.what₂.Tau n) ∈ coefLatFn σ emb O lam M' :=
    Submodule.subset_span ⟨_, nabAtr_scale emb lam N hM h1 h2 F hF, rfl⟩
  have h4 := Submodule.smul_mem _ ((⟨_, hO⟩ : O) ^ GlobalTheory.NabScale.scaleExp lam) h3
  have h0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN
  rw [SetLike.mem_coe]
  convert h4 using 1
  funext x
  change _ = ((N : ℂ)⁻¹) ^ GlobalTheory.NabScale.scaleExp lam * coefFn σ lam ((N : K) ^ GlobalTheory.NabScale.scaleExp lam • F.1) x
  rw [coefFn, coefFn, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval₂Hom_C, map_pow, map_natCast, inv_pow]
  field_simp

/- English proof (translation)
Take `⟨m₁, h₁⟩` from `exists_pow_latAt hF hk ha`. Take `⟨m₂, h₂⟩` from `exists_pow_latAt hF (GlobalTheory.SplitLinear.suppAt_inv hk) ha`. Establish `e1` using `h₁ (m₁ + m₂) (Nat.le_add_right _ _) (h * finPt S k)`. Establish `e2` using `h₂ (m₁ + m₂) (Nat.le_add_left _ _) h`. Rewrite `e1` using `[mul_inv_cancel_right]`.

Rewrite `e2` using `[show finPt S k⁻¹ = (finPt S k)⁻¹ from MonoidHom.map_inv _ k, inv_inv]`. Establish `hL : ∀ y : Bridge.Gf S, Submodule.IsLattice D.host.E (B.latAt y)` using `fun y => Formalism.UG.P.global_lattice_isLattice_holds _ _ _ _ (Module.Finite.iff_fg.2 hF.sdS.1.fg) hF.sdS.1.span_eq_top _`. Establish `hO' : ((N ^ (m₁ + m₂) : ℕ) : ℂ)⁻¹ ∈ O`. Rewrite using `[Nat.cast_pow, ← inv_pow]`. Conclude with `pow_mem hO _`.

Establish `e` using `le_antisymm (coefLatFn_le σ emb O B.w.lam (pow_ne_zero _ hN) hO' (hL _) e1 e2) (coefLatFn_le σ emb O B.w.lam (pow_ne_zero _ hN) hO' (hL _) e2 e1)`. Unfold `Base.coefLat harmLat`. Rewrite using `[e]`.
-/
theorem coefLat_mul {B : Base S T} (hF : B.F.Good) {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ)
    (emb : D.what₂.Tau → (D.host.E →+* K)) (O : Subring ℂ) {a : AE D} {k : GA D S} (hk : SuppAt a S k) {N : ℕ} (hN : N ≠ 0)
    (hO : (N : ℂ)⁻¹ ∈ O)
    (ha : ∀ PP : Pl D.host.E, (N : 𝓞 D.host.E) ∉ PP.asIdeal → cpt PP (toEAf D (a + cA D a)) = 0) (h : Bridge.Gf S) :
    B.coefLat σ emb O (h * finPt S k) = B.coefLat σ emb O h := by
  obtain ⟨m₁, h₁⟩ := exists_pow_latAt hF hk ha
  obtain ⟨m₂, h₂⟩ := exists_pow_latAt hF (GlobalTheory.SplitLinear.suppAt_inv hk) ha
  have e1 := h₁ (m₁ + m₂) (Nat.le_add_right _ _) (h * finPt S k)
  have e2 := h₂ (m₁ + m₂) (Nat.le_add_left _ _) h
  rw [mul_inv_cancel_right] at e1
  rw [show finPt S k⁻¹ = (finPt S k)⁻¹ from MonoidHom.map_inv _ k, inv_inv] at e2
  have hL : ∀ y : Bridge.Gf S, Submodule.IsLattice D.host.E (B.latAt y) := fun y =>
    Formalism.UG.P.global_lattice_isLattice_holds _ _ _ _ (Module.Finite.iff_fg.2 hF.sdS.1.fg) hF.sdS.1.span_eq_top _
  have hO' : ((N ^ (m₁ + m₂) : ℕ) : ℂ)⁻¹ ∈ O := by
    rw [Nat.cast_pow, ← inv_pow]
    exact pow_mem hO _
  have e := le_antisymm (coefLatFn_le σ emb O B.w.lam (pow_ne_zero _ hN) hO' (hL _) e1 e2)
    (coefLatFn_le σ emb O B.w.lam (pow_ne_zero _ hN) hO' (hL _) e2 e1)
  unfold Base.coefLat harmLat
  rw [e]

/- English proof (translation)
Rewrite `hf`, the goal using `[Base.mem_formsC]`. Use `⟨fun h => hf.1 _, fun γ h k => ?_⟩` and prove the remaining obligations. Use `hf.2 γ (h * c) k` as an intermediate fact. Rewrite `this` using `[← mul_assoc, mul_assoc _ c, ← hc, ← mul_assoc]`. Conclude with `this`.
-/
theorem translate_mem_formsC {B : Base S T} {ψ : Twist D Circle} {c : Bridge.Gf S} (hc : ∀ g, g * c = c * g)
    {f : Bridge.Gf S → PolF D T.rank S.rank} (hf : f ∈ B.formsC ψ) : (fun h => f (h * c)) ∈ B.formsC ψ := by
  rw [Base.mem_formsC] at hf ⊢
  refine ⟨fun h => hf.1 _, fun γ h k => ?_⟩
  have := hf.2 γ (h * c) k
  rw [← mul_assoc, mul_assoc _ c, ← hc, ← mul_assoc] at this
  exact this

/- English proof (translation)
Introduce `D j B hB ψ K _ _ σ emb O _ Q z hz N hN hQ hO F`. Take `⟨hzc, -, e, he, hsupp⟩` from `hz`. Establish `ha : ∀ PP : Pl D.host.E, (N : 𝓞 D.host.E) ∉ PP.asIdeal → cpt PP (toEAf D (e + cA D e)) = 0` using `fun PP hPP => by`. Rewrite using `[RingHom.map_add, RingHom.map_add, (cpt_sum he PP).2 fun h => hPP (hQ PP h), zero_add, GlobalTheory.StdFrames.toEAf_cA]`. Conclude with `GlobalTheory.StdFrames.cpt_sg_eq_zero ((cpt_sum he _).2 fun h => hPP ((GlobalTheory.StdFrames.natCast_mem_cP PP N).1 (hQ _ h)))`.

Establish `hc : ∀ g : Bridge.Gf (Vc D j), g * finPt (Vc D j) z = finPt (Vc D j) z * g` using `fun g => by`. Take `⟨y, rfl⟩` from `(finHom (Vc D j)).rangeRestrict_surjective g`. Rewrite using `[← MonoidHom.map_mul, ← MonoidHom.map_mul, Subgroup.mem_center_iff.1 hzc y]`. Establish `hc' : ∀ g : Bridge.Gf (Vc D j), g * (finPt (Vc D j) z)⁻¹ = (finPt (Vc D j) z)⁻¹ * g` using `fun g => (Commute.inv_right (hc g)).eq`. Establish `hl` using `coefLat_mul hB.frame σ emb O hsupp hN hO ha`.

Rewrite using `[Base.mem_mtLat, Base.mem_mtLat]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨translate_mem_formsC hc h1, fun h => hl h ▸ h2 _⟩`. Introduce and unpack `⟨h1, h2⟩`.

Use `⟨?_, fun h => ?_⟩` and prove the remaining obligations. Use `translate_mem_formsC hc' h1` as an intermediate fact. Simplify using `only [inv_mul_cancel_right] at this`. Conclude with `this`. Use `h2 (h * (finPt (Vc D j) z)⁻¹)` as an intermediate fact.

Rewrite `this` using `[← hl]`. Simplify using `only [inv_mul_cancel_right] at this`. Conclude with `this`.
-/
theorem mem_mtLat_iff_translate : ∀ (D : D7) (j : Fin D.R.m) (B : Base (Vc D j) (Wc D j)), B.Good → ∀ (ψ : Twist D Circle) (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K)) (O : Subring ℂ), IsCoefRing σ emb O →
  ∀ (Q : Finset (Pl D.host.E)) (z : GA D (Vc D j)), IsCentAt j Q z → ∀ N : ℕ, N ≠ 0 → (∀ P ∈ Q, (N : 𝓞 D.host.E) ∈ P.asIdeal) → (N : ℂ)⁻¹ ∈ O →
  ∀ F : Amb D j, F ∈ B.mtLat σ emb O ψ ↔ (fun h => F (h * finPt (Vc D j) z)) ∈ B.mtLat σ emb O ψ := by
  intro D j B hB ψ K _ _ σ emb O _ Q z hz N hN hQ hO F
  obtain ⟨hzc, -, e, he, hsupp⟩ := hz
  have ha : ∀ PP : Pl D.host.E, (N : 𝓞 D.host.E) ∉ PP.asIdeal → cpt PP (toEAf D (e + cA D e)) = 0 := fun PP hPP => by
    rw [RingHom.map_add, RingHom.map_add, (cpt_sum he PP).2 fun h => hPP (hQ PP h), zero_add, GlobalTheory.StdFrames.toEAf_cA]
    exact GlobalTheory.StdFrames.cpt_sg_eq_zero ((cpt_sum he _).2 fun h => hPP ((GlobalTheory.StdFrames.natCast_mem_cP PP N).1 (hQ _ h)))
  have hc : ∀ g : Bridge.Gf (Vc D j), g * finPt (Vc D j) z = finPt (Vc D j) z * g := fun g => by
    obtain ⟨y, rfl⟩ := (finHom (Vc D j)).rangeRestrict_surjective g
    rw [← MonoidHom.map_mul, ← MonoidHom.map_mul, Subgroup.mem_center_iff.1 hzc y]
  have hc' : ∀ g : Bridge.Gf (Vc D j), g * (finPt (Vc D j) z)⁻¹ = (finPt (Vc D j) z)⁻¹ * g := fun g =>
    (Commute.inv_right (hc g)).eq
  have hl := coefLat_mul hB.frame σ emb O hsupp hN hO ha
  rw [Base.mem_mtLat, Base.mem_mtLat]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨translate_mem_formsC hc h1, fun h => hl h ▸ h2 _⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, fun h => ?_⟩
    · have := translate_mem_formsC hc' h1
      simp only [inv_mul_cancel_right] at this
      exact this
    · have := h2 (h * (finPt (Vc D j) z)⁻¹)
      rw [← hl] at this
      simp only [inv_mul_cancel_right] at this
      exact this

end GlobalTheory.CentralTranslate

end
