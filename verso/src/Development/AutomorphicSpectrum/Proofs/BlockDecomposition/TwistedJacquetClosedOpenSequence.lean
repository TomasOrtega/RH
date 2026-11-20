import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProjectionToTwistedEigenfunctionSupport
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFiniteSupport
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SurjectiveIntertwinerQuotientEquiv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BijectiveIntertwinerSubrepEquiv

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.Glue

open GlobalTheory.CompanionTheory.TwistedAverage GlobalTheory.CompanionTheory.PRep.JacExact

section Eig

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] [TopologicalSpace G] [IsTopologicalGroup G]

/- English proof (translation)
Take `⟨s, t, hst⟩` from `exists_finite_support ρ L χ e he`. Use `haveI : CompactSpace L := isCompact_iff_compactSpace.1 hL`. Take `⟨M, hMo, hMχ, -, hMt⟩` from `exists_open_fixing ρ ρ hρ hρ L χ.ker hχ e t`. Use `haveI : Finite (L ⧸ M) := Subgroup.quotient_finite_of_isOpen M hMo`. Use `haveI : M.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient`.

Set `C : Subgroup L` to `M.normalCore`. Use `haveI : C.Normal := Subgroup.normalCore_normal M`. Use `haveI : C.FiniteIndex := inferInstance`. Use `haveI : Finite (L ⧸ C) := inferInstance`. Use `letI := Fintype.ofFinite (L ⧸ C)`.

Establish `hCM : C ≤ M` using `Subgroup.normalCore_le M`. Set `τ : Representation ℂ L V` to `ρ.comp L.subtype`. Establish `h0 : avg τ χ C e = 0`. Establish `hle : Submodule.span ℂ {y | ∃ n ∈ s, ∃ w ∈ t, y = ρ (n : G) w - ((χ n : ℂˣ) : ℂ) • w} ≤ LinearMap.ker (avg τ χ C)`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations.

Introduce and unpack `y ⟨n, -, w, hw, rfl⟩`. Use `show avg τ χ C (τ n w - ((χ n : ℂˣ) : ℂ) • w) = 0`. Rewrite using `[map_sub, avg_translate τ χ C (hCM.trans hMχ) w (fun m hm => hMt w hw m (hCM hm)) n, map_smul, sub_self]`. Conclude with `hle hst`. Establish `h1 : avg τ χ C e = ((Fintype.card (L ⧸ C) : ℕ) : ℂ) • e`.

Establish `h2 : ∀ q : L ⧸ C, (((χ (Quotient.out q))⁻¹ : ℂˣ) : ℂ) • τ (Quotient.out q) e = e`. Introduce `q`. Use `show (((χ (Quotient.out q))⁻¹ : ℂˣ) : ℂ) • ρ ((Quotient.out q : L) : G) e = e`. Rewrite using `[hev, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]`. Rewrite using `[avg_apply, Finset.sum_congr rfl fun q _ => h2 q]`.

Simplify using `[Finset.card_univ, Nat.cast_smul_eq_nsmul]`. Establish `hc : ((Fintype.card (L ⧸ C) : ℕ) : ℂ) ≠ 0`. Conclude with `Fintype.card_ne_zero` after adjusting the coercions. Rewrite `h1` using `[h0]`. Conclude with `(smul_eq_zero.1 h1.symm).resolve_left hc`.
-/
theorem eq_zero_of_mem_twKer_of_eig (ρ : Representation ℂ G V) (hρ : IsSmooth ρ) {L : Subgroup G}
    (hL : IsCompact (L : Set G)) (χ : L →* ℂˣ) (hχ : IsOpen (χ.ker : Set L)) (e : V)
    (he : e ∈ twKer ρ L χ) (hev : ∀ l : L, ρ (l : G) e = ((χ l : ℂˣ) : ℂ) • e) : e = 0 := by
  classical
  obtain ⟨s, t, hst⟩ := exists_finite_support ρ L χ e he
  haveI : CompactSpace L := isCompact_iff_compactSpace.1 hL
  obtain ⟨M, hMo, hMχ, -, hMt⟩ := exists_open_fixing ρ ρ hρ hρ L χ.ker hχ e t
  haveI : Finite (L ⧸ M) := Subgroup.quotient_finite_of_isOpen M hMo
  haveI : M.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  let C : Subgroup L := M.normalCore
  haveI : C.Normal := Subgroup.normalCore_normal M
  haveI : C.FiniteIndex := inferInstance
  haveI : Finite (L ⧸ C) := inferInstance
  letI := Fintype.ofFinite (L ⧸ C)
  have hCM : C ≤ M := Subgroup.normalCore_le M
  let τ : Representation ℂ L V := ρ.comp L.subtype
  have h0 : avg τ χ C e = 0 := by
    have hle : Submodule.span ℂ {y | ∃ n ∈ s, ∃ w ∈ t, y = ρ (n : G) w - ((χ n : ℂˣ) : ℂ) • w} ≤
        LinearMap.ker (avg τ χ C) := by
      refine Submodule.span_le.2 ?_
      rintro y ⟨n, -, w, hw, rfl⟩
      show avg τ χ C (τ n w - ((χ n : ℂˣ) : ℂ) • w) = 0
      rw [map_sub, avg_translate τ χ C (hCM.trans hMχ) w (fun m hm => hMt w hw m (hCM hm)) n, map_smul,
        sub_self]
    exact hle hst
  have h1 : avg τ χ C e = ((Fintype.card (L ⧸ C) : ℕ) : ℂ) • e := by
    have h2 : ∀ q : L ⧸ C, (((χ (Quotient.out q))⁻¹ : ℂˣ) : ℂ) • τ (Quotient.out q) e = e := by
      intro q
      show (((χ (Quotient.out q))⁻¹ : ℂˣ) : ℂ) • ρ ((Quotient.out q : L) : G) e = e
      rw [hev, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
    rw [avg_apply, Finset.sum_congr rfl fun q _ => h2 q]
    simp [Finset.card_univ, Nat.cast_smul_eq_nsmul]
  have hc : ((Fintype.card (L ⧸ C) : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [h0] at h1
  exact (smul_eq_zero.1 h1.symm).resolve_left hc

/- English proof (translation)
Use `Submodule.span_mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨n, v, rfl⟩`. Conclude with `⟨⟨n, h n.2⟩, v, rfl⟩`.
-/
theorem twKer_mono (ρ : Representation ℂ G V) {U L₁ L₂ : Subgroup G} (θ : U →* ℂˣ) (h₁ : L₁ ≤ U) (h₂ : L₂ ≤ U)
    (h : L₁ ≤ L₂) :
    twKer ρ L₁ (θ.comp (Subgroup.inclusion h₁)) ≤ twKer ρ L₂ (θ.comp (Subgroup.inclusion h₂)) := by
  refine Submodule.span_mono ?_
  rintro _ ⟨n, v, rfl⟩
  exact ⟨⟨n, h n.2⟩, v, rfl⟩

/- English proof (translation)
Use `Submodule.span_mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨n, v, rfl⟩`. Conclude with `⟨⟨n, h n.2⟩, v, rfl⟩`.
-/
theorem twKer_le (ρ : Representation ℂ G V) {U L : Subgroup G} (θ : U →* ℂˣ) (h : L ≤ U) :
    twKer ρ L (θ.comp (Subgroup.inclusion h)) ≤ twKer ρ U θ := by
  refine Submodule.span_mono ?_
  rintro _ ⟨n, v, rfl⟩
  exact ⟨⟨n, h n.2⟩, v, rfl⟩

/- English proof (translation)
Establish `e : ((θ.comp (Subgroup.inclusion h)).ker : Set L) = Subgroup.inclusion h ⁻¹' (θ.ker : Set U)`. Use extensionality with `l`. Simplify using `[MonoidHom.mem_ker]`. Rewrite using `[e]`. Conclude with `hθ.preimage (Continuous.subtype_mk continuous_subtype_val _)`.
-/
theorem isOpen_ker_comp {U L : Subgroup G} (θ : U →* ℂˣ) (hθ : IsOpen (θ.ker : Set U)) (h : L ≤ U) :
    IsOpen ((θ.comp (Subgroup.inclusion h)).ker : Set L) := by
  have e : ((θ.comp (Subgroup.inclusion h)).ker : Set L) = Subgroup.inclusion h ⁻¹' (θ.ker : Set U) := by
    ext l
    simp [MonoidHom.mem_ker]
  rw [e]
  exact hθ.preimage (Continuous.subtype_mk continuous_subtype_val _)

end Eig

/- English proof (translation)
Set `E' : Y →ₗ[ℂ] LinearMap.range j` to `E.codRestrict _ fun y => by`. Take `⟨v, hv⟩` from `h y`. Conclude with `⟨v, hv⟩`. Use `⟨(LinearEquiv.ofInjective j hj).symm.toLinearMap ∘ₗ E', fun y => ?_⟩` and prove the remaining obligations. Use `(LinearEquiv.ofInjective j hj).apply_symm_apply (E' y)` as an intermediate fact.

Conclude with `congrArg Subtype.val this`.
-/
theorem exists_factor {Y V A : Type} [AddCommGroup Y] [Module ℂ Y] [AddCommGroup V] [Module ℂ V] [AddCommGroup A]
    [Module ℂ A] (j : V →ₗ[ℂ] A) (hj : Function.Injective j) (E : Y →ₗ[ℂ] A) (h : ∀ y, ∃ v, j v = E y) :
    ∃ Φ : Y →ₗ[ℂ] V, ∀ y, j (Φ y) = E y := by
  let E' : Y →ₗ[ℂ] LinearMap.range j := E.codRestrict _ fun y => by
    obtain ⟨v, hv⟩ := h y
    exact ⟨v, hv⟩
  refine ⟨(LinearEquiv.ofInjective j hj).symm.toLinearMap ∘ₗ E', fun y => ?_⟩
  have := (LinearEquiv.ofInjective j hj).apply_symm_apply (E' y)
  exact congrArg Subtype.val this

/- English proof (translation)
Take `⟨ΦC, hΦC⟩` from `exists_factor jC hjC EC hCmem`. Set `R : ρ.IntertwiningMap πC` to `⟨ΦC, fun m => LinearMap.ext fun y => by`. Apply `hjC` to reduce the goal to its premises. Use `show jC (ΦC (ρ m y)) = jC (πC m (ΦC y))`. Rewrite using `[hΦC, hjCe, hΦC, ECi]⟩`.

Establish `hRs : Function.Surjective R` using `fun v => by`. Take `⟨y, hy⟩` from `hConto v`. Use `⟨y, hjC ?_⟩` and prove the remaining obligations. Use `show jC (ΦC y) = jC v`. Rewrite using `[hΦC, hy]`.

Take `⟨S, hS, hq⟩` from `GlobalTheory.CompanionTheory.BZRes.KerQuot.exists_subQuot_top_ker_equiv ρ πC R hRs`. Establish `memS : ∀ y, y ∈ S.toSubmodule ↔ EC y = 0`. Introduce `y`. Rewrite using `[hS, LinearMap.mem_ker]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Establish `h' : ΦC y = 0` using `h`. Rewrite using `[← hΦC, h', map_zero]`. Introduce `h`. Use `hjC ?_` and prove the remaining obligations.

Use `show jC (ΦC y) = jC 0`. Rewrite using `[hΦC, h, map_zero]`. Take `⟨Ψ, hΨ⟩` from `exists_factor jO hjO (EO ∘ₗ S.toSubmodule.subtype) (fun y => h1 y.1 ((memS _).1 y.2))`. Use `⟨S, GlobalTheory.CompanionTheory.BZRes.subQuot_bot_equiv_of_bijective ρ πO S Ψ ⟨?_, ?_⟩ ?_, hq⟩` and prove the remaining obligations. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce and unpack `⟨y, hy⟩ h0`. Establish `hO : EO y = 0`. Use `hΨ ⟨y, hy⟩` as an intermediate fact. Rewrite `this` using `[h0, map_zero]`. Conclude with `this.symm`.

Conclude with `Subtype.ext (h2 y ((memS _).1 hy) hO)`. Introduce `v`. Take `⟨y, hy, he⟩` from `h3 v`. Use `⟨⟨y, (memS _).2 hy⟩, hjO ?_⟩` and prove the remaining obligations. Rewrite using `[hΨ]`.

Conclude with `he`. Introduce `m v`. Apply `hjO` to reduce the goal to its premises. Rewrite using `[hΨ, hjOe, hΨ]`. Conclude with `EOi m v.1`.
-/
theorem extension_of_maps {M Y VC VO AC AO : Type} [Group M] [AddCommGroup Y] [Module ℂ Y] [AddCommGroup VC] [Module ℂ VC]
    [AddCommGroup VO] [Module ℂ VO] [AddCommGroup AC] [Module ℂ AC] [AddCommGroup AO] [Module ℂ AO]
    (ρ : Representation ℂ M Y) (πC : Representation ℂ M VC) (πO : Representation ℂ M VO)
    (aC : Representation ℂ M AC) (aO : Representation ℂ M AO)
    (jC : VC →ₗ[ℂ] AC) (jO : VO →ₗ[ℂ] AO) (hjC : Function.Injective jC) (hjO : Function.Injective jO)
    (hjCe : ∀ m v, jC (πC m v) = aC m (jC v)) (hjOe : ∀ m v, jO (πO m v) = aO m (jO v))
    (EC : Y →ₗ[ℂ] AC) (EO : Y →ₗ[ℂ] AO)
    (ECi : ∀ m y, EC (ρ m y) = aC m (EC y)) (EOi : ∀ m y, EO (ρ m y) = aO m (EO y))
    (hCmem : ∀ y, ∃ v, jC v = EC y) (hConto : ∀ v, ∃ y, EC y = jC v)
    (h1 : ∀ y, EC y = 0 → ∃ v, jO v = EO y) (h2 : ∀ y, EC y = 0 → EO y = 0 → y = 0)
    (h3 : ∀ v, ∃ y, EC y = 0 ∧ EO y = jO v) :
    ∃ S : Subrepresentation ρ, Nonempty ((subQuot S ⊥).Equiv πO) ∧ Nonempty ((subQuot ⊤ S).Equiv πC) := by
  obtain ⟨ΦC, hΦC⟩ := exists_factor jC hjC EC hCmem
  let R : ρ.IntertwiningMap πC := ⟨ΦC, fun m => LinearMap.ext fun y => by
    apply hjC
    show jC (ΦC (ρ m y)) = jC (πC m (ΦC y))
    rw [hΦC, hjCe, hΦC, ECi]⟩
  have hRs : Function.Surjective R := fun v => by
    obtain ⟨y, hy⟩ := hConto v
    refine ⟨y, hjC ?_⟩
    show jC (ΦC y) = jC v
    rw [hΦC, hy]
  obtain ⟨S, hS, hq⟩ := GlobalTheory.CompanionTheory.BZRes.KerQuot.exists_subQuot_top_ker_equiv ρ πC R hRs
  have memS : ∀ y, y ∈ S.toSubmodule ↔ EC y = 0 := by
    intro y
    rw [hS, LinearMap.mem_ker]
    constructor
    · intro h
      have h' : ΦC y = 0 := h
      rw [← hΦC, h', map_zero]
    · intro h
      refine hjC ?_
      show jC (ΦC y) = jC 0
      rw [hΦC, h, map_zero]
  obtain ⟨Ψ, hΨ⟩ := exists_factor jO hjO (EO ∘ₗ S.toSubmodule.subtype)
    (fun y => h1 y.1 ((memS _).1 y.2))
  refine ⟨S, GlobalTheory.CompanionTheory.BZRes.subQuot_bot_equiv_of_bijective ρ πO S Ψ ⟨?_, ?_⟩ ?_, hq⟩
  · rw [injective_iff_map_eq_zero]
    rintro ⟨y, hy⟩ h0
    have hO : EO y = 0 := by
      have := hΨ ⟨y, hy⟩
      rw [h0, map_zero] at this
      exact this.symm
    exact Subtype.ext (h2 y ((memS _).1 hy) hO)
  · intro v
    obtain ⟨y, hy, he⟩ := h3 v
    refine ⟨⟨y, (memS _).2 hy⟩, hjO ?_⟩
    rw [hΨ]
    exact he
  · intro m v
    apply hjO
    rw [hΨ, hjOe, hΨ]
    exact EOi m v.1

section Glue

variable {G Z : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup Z] [Module ℂ Z]

def evC (H : Subgroup G) (σ : Representation ℂ H Z) (x : G) : cIndSpace H σ →ₗ[ℂ] Z :=
  GlobalTheory.CompanionTheory.TwAvgInd.evalAt H σ x ∘ₗ (cIndSpace H σ).subtype

/- English proof (translation)
Take `⟨ι, _, r, c, h1, h2⟩` from `GlobalTheory.CompanionTheory.TwAvgInd.exists_finite_average (cInd H σ) (GlobalTheory.CompanionTheory.BZFun.isSmooth_cInd H σ) hL χ hχ f`. Use `⟨_, h1, ?_, h2⟩` and prove the remaining obligations. Introduce `x hx`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`.

Apply `hx` to reduce the goal to its premises. Establish `hz : ∀ i, evC H σ x (twOrbit (cInd H σ) L χ f (r i)) = 0`. Introduce `i`. Establish `: evC H σ x (cInd H σ ((r i : L) : G) f) = 0` using `hcon _ (r i).2`. Simplify using `only [twOrbit, map_smul, this, smul_zero]`.

Establish `: evC H σ x (c • ∑ i, twOrbit (cInd H σ) L χ f (r i)) = 0`. Rewrite using `[map_smul, map_sum, Finset.sum_eq_zero fun i _ => hz i, smul_zero]`. Conclude with `this`.
-/
theorem exists_avg (H : Subgroup G) (σ : Representation ℂ H Z) {L : Subgroup G} (hL : IsCompact (L : Set G))
    (χ : L →* ℂˣ) (hχ : IsOpen (χ.ker : Set L)) (f : cIndSpace H σ) :
    ∃ f' : cIndSpace H σ, f - f' ∈ twKer (cInd H σ) L χ ∧
      (∀ x, f'.1.1.1 x ≠ 0 → ∃ l ∈ L, f.1.1.1 (x * l) ≠ 0) ∧
      ∀ l : L, cInd H σ (l : G) f' = ((χ l : ℂˣ) : ℂ) • f' := by
  obtain ⟨ι, _, r, c, h1, h2⟩ :=
    GlobalTheory.CompanionTheory.TwAvgInd.exists_finite_average (cInd H σ) (GlobalTheory.CompanionTheory.BZFun.isSmooth_cInd H σ) hL χ hχ f
  refine ⟨_, h1, ?_, h2⟩
  intro x hx
  by_contra hcon
  push_neg at hcon
  apply hx
  have hz : ∀ i, evC H σ x (twOrbit (cInd H σ) L χ f (r i)) = 0 := by
    intro i
    have : evC H σ x (cInd H σ ((r i : L) : G) f) = 0 := hcon _ (r i).2
    simp only [twOrbit, map_smul, this, smul_zero]
  have : evC H σ x (c • ∑ i, twOrbit (cInd H σ) L χ f (r i)) = 0 := by
    rw [map_smul, map_sum, Finset.sum_eq_zero fun i _ => hz i, smul_zero]
  exact this

def Good (H : Subgroup G) (σ : Representation ℂ H Z) (U : Subgroup G) (θ : U →* ℂˣ) (f : cIndSpace H σ)
    (A : Set G) : Prop :=
  ∃ L : Subgroup G, L ≤ U ∧ IsCompact (L : Set G) ∧
    ∀ (L' : Subgroup G) (hL' : L' ≤ U), IsCompact (L' : Set G) → L ≤ L' →
      ∀ g : cIndSpace H σ, f - g ∈ twKer (cInd H σ) L' (θ.comp (Subgroup.inclusion hL')) →
        (∀ l : L', cInd H σ (l : G) g = ((θ (Subgroup.inclusion hL' l) : ℂˣ) : ℂ) • g) →
        ∀ x ∈ A, g.1.1.1 x = 0

/- English proof (translation)
Take `⟨L, hL, hLc, gp, h1, -, h3⟩` from `hp`. Establish `hK : IsOpen {k : G | cInd H σ k gp = gp}` using `GlobalTheory.CompanionTheory.BZFun.isSmooth_cInd H σ gp`. Establish `hop : IsOpen ((fun x => p⁻¹ * x) ⁻¹' {k : G | cInd H σ k gp = gp})` using `hK.preimage (by fun_prop)`. Use `⟨_, hop.mem_nhds (by simp), L, hL, hLc, fun L' hL' hL'c hLL' g hg hge ω hω => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`.

Take `⟨h', a1, a2, a3⟩` from `exists_avg H σ hL'c (θ.comp (Subgroup.inclusion hL')) (isOpen_ker_comp θ hθ hL') gp`. Establish `hgh : g - h' = 0`. Use `eq_zero_of_mem_twKer_of_eig (cInd H σ) (GlobalTheory.CompanionTheory.BZFun.isSmooth_cInd H σ) hL'c _ (isOpen_ker_comp θ hθ hL') _ ?_ ?_` and prove the remaining obligations. Establish `e : g - h' = (f - gp) + (gp - h') - (f - g)` using `by abel`. Rewrite using `[e]`.

Conclude with `Submodule.sub_mem _ (Submodule.add_mem _ (twKer_mono _ θ hL hL' hLL' h1) a1) hg`. Introduce `l`. Rewrite using `[map_sub, hge l, a3 l, smul_sub]`. Both sides reduce to the same expression. Take `rfl : g = h'` from `sub_eq_zero.1 hgh`.

Take `⟨l, hl, hne'⟩` from `a2 ω hne`. Apply `hne'` to reduce the goal to its premises. Use `set k : G := p⁻¹ * ω with hk`. Establish `hkK : cInd H σ k gp = gp` using `hω`. Establish `hu : k * l * k⁻¹ ∈ U` using `hUn.conj_mem l (hL' hl) k`.

Establish `e1 : ω * l = p * (k * l * k⁻¹) * k`. Rewrite using `[hk]`. Use `group`. Establish `e2 : gp.1.1.1 (p * (k * l * k⁻¹) * k) = (cInd H σ k gp).1.1.1 (p * (k * l * k⁻¹))` using `rfl`. Rewrite using `[e1, e2, hkK]`.

Conclude with `h3 _ hu`.
-/
theorem good_nhds (H : Subgroup G) (σ : Representation ℂ H Z) (U : Subgroup G) (hUn : U.Normal) (θ : U →* ℂˣ)
    (hθ : IsOpen (θ.ker : Set U)) (f : cIndSpace H σ) (p : G) (hp : AvgVanish H σ U θ f p) :
    ∃ t ∈ 𝓝 p, Good H σ U θ f t := by
  obtain ⟨L, hL, hLc, gp, h1, -, h3⟩ := hp
  have hK : IsOpen {k : G | cInd H σ k gp = gp} := GlobalTheory.CompanionTheory.BZFun.isSmooth_cInd H σ gp
  have hop : IsOpen ((fun x => p⁻¹ * x) ⁻¹' {k : G | cInd H σ k gp = gp}) :=
    hK.preimage (by fun_prop)
  refine ⟨_, hop.mem_nhds (by simp), L, hL, hLc, fun L' hL' hL'c hLL' g hg hge ω hω => ?_⟩
  by_contra hne
  obtain ⟨h', a1, a2, a3⟩ := exists_avg H σ hL'c (θ.comp (Subgroup.inclusion hL'))
    (isOpen_ker_comp θ hθ hL') gp
  have hgh : g - h' = 0 := by
    refine eq_zero_of_mem_twKer_of_eig (cInd H σ) (GlobalTheory.CompanionTheory.BZFun.isSmooth_cInd H σ) hL'c _
      (isOpen_ker_comp θ hθ hL') _ ?_ ?_
    · have e : g - h' = (f - gp) + (gp - h') - (f - g) := by abel
      rw [e]
      exact Submodule.sub_mem _ (Submodule.add_mem _ (twKer_mono _ θ hL hL' hLL' h1) a1) hg
    · intro l
      rw [map_sub, hge l, a3 l, smul_sub]
      rfl
  obtain rfl : g = h' := sub_eq_zero.1 hgh
  obtain ⟨l, hl, hne'⟩ := a2 ω hne
  apply hne'
  set k : G := p⁻¹ * ω with hk
  have hkK : cInd H σ k gp = gp := hω
  have hu : k * l * k⁻¹ ∈ U := hUn.conj_mem l (hL' hl) k
  have e1 : ω * l = p * (k * l * k⁻¹) * k := by
    rw [hk]; group
  have e2 : gp.1.1.1 (p * (k * l * k⁻¹) * k) = (cInd H σ k gp).1.1.1 (p * (k * l * k⁻¹)) := rfl
  rw [e1, e2, hkK]
  exact h3 _ hu

/- English proof (translation)
Take `⟨Ω₀, hΩ₀, hsupp⟩` from `f.2`. Establish `hΩ : IsCompact (Ω₀ ∩ S)` using `hΩ₀.inter_right hS`. Establish `hG : Good H σ U θ f (Ω₀ ∩ S)`. Use `hΩ.induction_on (p := Good H σ U θ f) ?_ ?_ ?_ ?_` and prove the remaining obligations. Use `⟨⊥, bot_le, ?_, fun _ _ _ _ _ _ _ x hx => hx.elim⟩` and prove the remaining obligations.

Rewrite using `[Subgroup.coe_bot]`. Conclude with `isCompact_singleton`. Introduce and unpack `A B hAB ⟨L, hL, hLc, h⟩`. Conclude with `⟨L, hL, hLc, fun L' hL' c hl g a b x hx => h L' hL' c hl g a b x (hAB hx)⟩`. Introduce and unpack `A B ⟨L₁, h₁, c₁, a₁⟩ ⟨L₂, h₂, c₂, a₂⟩`.

Take `⟨L, hL, hLc, l₁, l₂⟩` from `hdir L₁ L₂ h₁ h₂ c₁ c₂`. Use `⟨L, hL, hLc, fun L' hL' c hl g a b x hx => ?_⟩` and prove the remaining obligations. Break down `hx with hx | hx` into its components or cases. Conclude with `a₁ L' hL' c (l₁.trans hl) g a b x hx`. Conclude with `a₂ L' hL' c (l₂.trans hl) g a b x hx`.

Introduce `x hx`. Take `⟨t, ht, hg⟩` from `good_nhds H σ U hUn θ hθ f x (hf x hx.2)`. Conclude with `⟨t, mem_nhdsWithin_of_mem_nhds ht, hg⟩`. Take `⟨L, hL, hLc, hgood⟩` from `hG`. Take `⟨g, h1, h2, h3⟩` from `exists_avg H σ hLc (θ.comp (Subgroup.inclusion hL)) (isOpen_ker_comp θ hθ hL) f`.

Use `⟨g, twKer_le _ θ hL h1, fun x hx => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Take `⟨l, hl, hfl⟩` from `h2 x hne`. Take `⟨h, hh, ω, hω, e⟩` from `hsupp (x * l) hfl`. Establish `hωS : ω ∈ S`.

Establish `: ω = h⁻¹ * (x * l)` using `by rw [e]; group`. Rewrite using `[this]`. Conclude with `hHS _ (inv_mem hh) _ (hSU x hx l (hL hl))`. Establish `hz : g.1.1.1 ω = 0` using `hgood L hL hLc le_rfl g h1 h3 ω ⟨hω, hωS⟩`. Establish `hxl : g.1.1.1 (x * l) = 0`.

Establish `e4 : g.1.1.1 (((⟨h, hh⟩ : H) : G) * ω) = σ ⟨h, hh⟩ (g.1.1.1 ω)` using `g.1.1.2 ⟨h, hh⟩ ω`. Rewrite using `[e]`. Rewrite using `[show g.1.1.1 (h * ω) = _ from e4, hz, map_zero]`. Establish `e5 : g.1.1.1 (x * l) = (cInd H σ ((⟨l, hl⟩ : L) : G) g).1.1.1 x` using `rfl`. Rewrite `hxl` using `[e5, h3 ⟨l, hl⟩]`.

Establish `e7 : ((θ.comp (Subgroup.inclusion hL) ⟨l, hl⟩ : ℂˣ) : ℂ) • g.1.1.1 x = 0` using `hxl`. Conclude with `hne ((smul_eq_zero.1 e7).resolve_left (Units.ne_zero _))`.
-/
theorem glue (H : Subgroup G) (σ : Representation ℂ H Z) (U : Subgroup G) (hUn : U.Normal) (θ : U →* ℂˣ)
    (hθ : IsOpen (θ.ker : Set U))
    (hdir : ∀ L₁ L₂ : Subgroup G, L₁ ≤ U → L₂ ≤ U → IsCompact (L₁ : Set G) → IsCompact (L₂ : Set G) →
      ∃ L : Subgroup G, L ≤ U ∧ IsCompact (L : Set G) ∧ L₁ ≤ L ∧ L₂ ≤ L)
    (S : Set G) (hS : IsClosed S) (hHS : ∀ h ∈ H, ∀ x ∈ S, h * x ∈ S) (hSU : ∀ x ∈ S, ∀ u ∈ U, x * u ∈ S)
    (f : cIndSpace H σ) (hf : ∀ p ∈ S, AvgVanish H σ U θ f p) :
    ∃ g : cIndSpace H σ, f - g ∈ twKer (cInd H σ) U θ ∧ ∀ x ∈ S, g.1.1.1 x = 0 := by
  obtain ⟨Ω₀, hΩ₀, hsupp⟩ := f.2
  have hΩ : IsCompact (Ω₀ ∩ S) := hΩ₀.inter_right hS
  have hG : Good H σ U θ f (Ω₀ ∩ S) := by
    refine hΩ.induction_on (p := Good H σ U θ f) ?_ ?_ ?_ ?_
    · refine ⟨⊥, bot_le, ?_, fun _ _ _ _ _ _ _ x hx => hx.elim⟩
      rw [Subgroup.coe_bot]
      exact isCompact_singleton
    · rintro A B hAB ⟨L, hL, hLc, h⟩
      exact ⟨L, hL, hLc, fun L' hL' c hl g a b x hx => h L' hL' c hl g a b x (hAB hx)⟩
    · rintro A B ⟨L₁, h₁, c₁, a₁⟩ ⟨L₂, h₂, c₂, a₂⟩
      obtain ⟨L, hL, hLc, l₁, l₂⟩ := hdir L₁ L₂ h₁ h₂ c₁ c₂
      refine ⟨L, hL, hLc, fun L' hL' c hl g a b x hx => ?_⟩
      rcases hx with hx | hx
      · exact a₁ L' hL' c (l₁.trans hl) g a b x hx
      · exact a₂ L' hL' c (l₂.trans hl) g a b x hx
    · intro x hx
      obtain ⟨t, ht, hg⟩ := good_nhds H σ U hUn θ hθ f x (hf x hx.2)
      exact ⟨t, mem_nhdsWithin_of_mem_nhds ht, hg⟩
  obtain ⟨L, hL, hLc, hgood⟩ := hG
  obtain ⟨g, h1, h2, h3⟩ := exists_avg H σ hLc (θ.comp (Subgroup.inclusion hL)) (isOpen_ker_comp θ hθ hL) f
  refine ⟨g, twKer_le _ θ hL h1, fun x hx => ?_⟩
  by_contra hne
  obtain ⟨l, hl, hfl⟩ := h2 x hne
  obtain ⟨h, hh, ω, hω, e⟩ := hsupp (x * l) hfl
  have hωS : ω ∈ S := by
    have : ω = h⁻¹ * (x * l) := by rw [e]; group
    rw [this]
    exact hHS _ (inv_mem hh) _ (hSU x hx l (hL hl))
  have hz : g.1.1.1 ω = 0 := hgood L hL hLc le_rfl g h1 h3 ω ⟨hω, hωS⟩
  have hxl : g.1.1.1 (x * l) = 0 := by
    have e4 : g.1.1.1 (((⟨h, hh⟩ : H) : G) * ω) = σ ⟨h, hh⟩ (g.1.1.1 ω) := g.1.1.2 ⟨h, hh⟩ ω
    rw [e]
    rw [show g.1.1.1 (h * ω) = _ from e4, hz, map_zero]
  have e5 : g.1.1.1 (x * l) = (cInd H σ ((⟨l, hl⟩ : L) : G) g).1.1.1 x := rfl
  rw [e5, h3 ⟨l, hl⟩] at hxl
  have e7 : ((θ.comp (Subgroup.inclusion hL) ⟨l, hl⟩ : ℂˣ) : ℂ) • g.1.1.1 x = 0 := hxl
  exact hne ((smul_eq_zero.1 e7).resolve_left (Units.ne_zero _))

end Glue

/- English proof (translation)
Establish `kC : twKer (cInd H σ) U θ ≤ LinearMap.ker eC` using `Submodule.span_le.2 (by`. Introduce and unpack `_ ⟨u, v, rfl⟩`. Use `show eC _ = 0`. Rewrite using `[map_sub, hC1, map_smul, sub_self])`. Establish `kO : twKer (cInd H σ) U θ ≤ LinearMap.ker eO` using `Submodule.span_le.2 (by`.

Introduce and unpack `_ ⟨u, v, rfl⟩`. Use `show eO _ = 0`. Rewrite using `[map_sub, hO1, map_smul, sub_self])`. Establish `ECmk : ∀ f, (twKer (cInd H σ) U θ).liftQ eC kC (Submodule.Quotient.mk f) = eC f` using `fun f => rfl`. Establish `EOmk : ∀ f, (twKer (cInd H σ) U θ).liftQ eO kO (Submodule.Quotient.mk f) = eO f` using `fun f => rfl`.

Use `Glue.extension_of_maps ρ πC πO aC aO jC jO hjC hjO hjCe hjOe ((twKer (cInd H σ) U θ).liftQ eC kC) ((twKer (cInd H σ) U θ).liftQ eO kO) ?_ ?_ ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `m y`. Take `⟨f, rfl⟩` from `Submodule.Quotient.mk_surjective _ y`. Rewrite using `[hρ, map_smul, ECmk, ECmk, hCs]`. Introduce `m y`.

Take `⟨f, rfl⟩` from `Submodule.Quotient.mk_surjective _ y`. Rewrite using `[hρ, map_smul, EOmk, EOmk, hOs]`. Introduce `y`. Take `⟨f, rfl⟩` from `Submodule.Quotient.mk_surjective _ y`. Conclude with `hCmem f`.

Introduce `v`. Take `⟨f, hf⟩` from `hConto v`. Conclude with `⟨Submodule.Quotient.mk f, hf⟩`. Introduce `y hy`. Take `⟨f, rfl⟩` from `Submodule.Quotient.mk_surjective _ y`.

Take `⟨g, hg, hv⟩` from `Glue.glue H σ U hUn θ hθ hdir C hCc hHC hCU f (hlocC f hy)`. Establish `e : (Submodule.Quotient.mk f : TwJacquet (cInd H σ) U θ) = Submodule.Quotient.mk g` using `(Submodule.Quotient.eq _).2 hg`. Take `⟨v, hv'⟩` from `hOmem g hv`. Conclude with `⟨v, by rw [e, EOmk, hv']⟩`. Introduce `y hyC hyO`.

Take `⟨f, rfl⟩` from `Submodule.Quotient.mk_surjective _ y`. Take `⟨g, hg, hv⟩` from `Glue.glue H σ U hUn θ hθ hdir Set.univ isClosed_univ (fun _ _ _ _ => trivial) (fun _ _ _ _ => trivial) f (fun p _ => by`. Distinguish the cases in `hp : p ∈ C`. Conclude with `hlocC f hyC p hp`. Conclude with `hlocO f hyO p hp)`.

Establish `hg0 : g = 0` using `Subtype.ext (Subtype.ext (Subtype.ext (funext fun x => hv x trivial)))`. Rewrite `hg` using `[hg0, sub_zero]`. Conclude with `(Submodule.Quotient.mk_eq_zero _).2 hg`. Introduce `v`. Take `⟨f, hf, he⟩` from `hOonto v`.

Conclude with `⟨Submodule.Quotient.mk f, hCoff f hf, he⟩`.
-/
theorem extension {G M Z VC VO AC AO : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group M]
    [AddCommGroup Z] [Module ℂ Z] [AddCommGroup VC] [Module ℂ VC] [AddCommGroup VO] [Module ℂ VO]
    [AddCommGroup AC] [Module ℂ AC] [AddCommGroup AO] [Module ℂ AO]
    (H : Subgroup G) (σ : Representation ℂ H Z) (U : Subgroup G) (hUn : U.Normal) (θ : U →* ℂˣ)
    (hθ : IsOpen (θ.ker : Set U))
    (hdir : ∀ L₁ L₂ : Subgroup G, L₁ ≤ U → L₂ ≤ U → IsCompact (L₁ : Set G) → IsCompact (L₂ : Set G) →
      ∃ L : Subgroup G, L ≤ U ∧ IsCompact (L : Set G) ∧ L₁ ≤ L ∧ L₂ ≤ L)
    (s : M →* G) (c : M →* ℂˣ) (ρ : Representation ℂ M (TwJacquet (cInd H σ) U θ))
    (hρ : ∀ (m : M) (f : cIndSpace H σ), ρ m (Submodule.Quotient.mk f) =
      ((c m : ℂˣ) : ℂ) • Submodule.Quotient.mk (cInd H σ (s m) f))
    (C : Set G) (hCc : IsClosed C) (hHC : ∀ h ∈ H, ∀ x ∈ C, h * x ∈ C) (hCU : ∀ x ∈ C, ∀ u ∈ U, x * u ∈ C)
    (πC : Representation ℂ M VC) (πO : Representation ℂ M VO)
    (aC : Representation ℂ M AC) (aO : Representation ℂ M AO)
    (jC : VC →ₗ[ℂ] AC) (jO : VO →ₗ[ℂ] AO) (hjC : Function.Injective jC) (hjO : Function.Injective jO)
    (hjCe : ∀ m v, jC (πC m v) = aC m (jC v)) (hjOe : ∀ m v, jO (πO m v) = aO m (jO v))
    (eC : cIndSpace H σ →ₗ[ℂ] AC) (eO : cIndSpace H σ →ₗ[ℂ] AO)
    (hC1 : ∀ (u : U) f, eC (cInd H σ (u : G) f) = ((θ u : ℂˣ) : ℂ) • eC f)
    (hO1 : ∀ (u : U) f, eO (cInd H σ (u : G) f) = ((θ u : ℂˣ) : ℂ) • eO f)
    (hCs : ∀ m f, aC m (eC f) = ((c m : ℂˣ) : ℂ) • eC (cInd H σ (s m) f))
    (hOs : ∀ m f, aO m (eO f) = ((c m : ℂˣ) : ℂ) • eO (cInd H σ (s m) f))
    (hCmem : ∀ f, ∃ v, jC v = eC f)
    (hOmem : ∀ f : cIndSpace H σ, (∀ x ∈ C, (f : smoothPart (ind H σ)).1.1 x = 0) → ∃ v, jO v = eO f)
    (hConto : ∀ v, ∃ f, eC f = jC v)
    (hOonto : ∀ v, ∃ f : cIndSpace H σ, (∀ x ∈ C, (f : smoothPart (ind H σ)).1.1 x = 0) ∧ eO f = jO v)
    (hCoff : ∀ f : cIndSpace H σ, (∀ x ∈ C, (f : smoothPart (ind H σ)).1.1 x = 0) → eC f = 0)
    (hlocC : ∀ f, eC f = 0 → ∀ p ∈ C, AvgVanish H σ U θ f p)
    (hlocO : ∀ f, eO f = 0 → ∀ p, p ∉ C → AvgVanish H σ U θ f p) :
    ∃ S : Subrepresentation ρ, Nonempty ((subQuot S ⊥).Equiv πO) ∧ Nonempty ((subQuot ⊤ S).Equiv πC) := by
  have kC : twKer (cInd H σ) U θ ≤ LinearMap.ker eC := Submodule.span_le.2 (by
    rintro _ ⟨u, v, rfl⟩
    show eC _ = 0
    rw [map_sub, hC1, map_smul, sub_self])
  have kO : twKer (cInd H σ) U θ ≤ LinearMap.ker eO := Submodule.span_le.2 (by
    rintro _ ⟨u, v, rfl⟩
    show eO _ = 0
    rw [map_sub, hO1, map_smul, sub_self])
  have ECmk : ∀ f, (twKer (cInd H σ) U θ).liftQ eC kC (Submodule.Quotient.mk f) = eC f := fun f => rfl
  have EOmk : ∀ f, (twKer (cInd H σ) U θ).liftQ eO kO (Submodule.Quotient.mk f) = eO f := fun f => rfl
  refine Glue.extension_of_maps ρ πC πO aC aO jC jO hjC hjO hjCe hjOe
    ((twKer (cInd H σ) U θ).liftQ eC kC) ((twKer (cInd H σ) U θ).liftQ eO kO) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro m y
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [hρ, map_smul, ECmk, ECmk, hCs]
  · intro m y
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [hρ, map_smul, EOmk, EOmk, hOs]
  · intro y
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact hCmem f
  · intro v
    obtain ⟨f, hf⟩ := hConto v
    exact ⟨Submodule.Quotient.mk f, hf⟩
  · intro y hy
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨g, hg, hv⟩ := Glue.glue H σ U hUn θ hθ hdir C hCc hHC hCU f (hlocC f hy)
    have e : (Submodule.Quotient.mk f : TwJacquet (cInd H σ) U θ) = Submodule.Quotient.mk g :=
      (Submodule.Quotient.eq _).2 hg
    obtain ⟨v, hv'⟩ := hOmem g hv
    exact ⟨v, by rw [e, EOmk, hv']⟩
  · intro y hyC hyO
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨g, hg, hv⟩ := Glue.glue H σ U hUn θ hθ hdir Set.univ isClosed_univ (fun _ _ _ _ => trivial)
      (fun _ _ _ _ => trivial) f (fun p _ => by
        by_cases hp : p ∈ C
        · exact hlocC f hyC p hp
        · exact hlocO f hyO p hp)
    have hg0 : g = 0 := Subtype.ext (Subtype.ext (Subtype.ext (funext fun x => hv x trivial)))
    rw [hg0, sub_zero] at hg
    exact (Submodule.Quotient.mk_eq_zero _).2 hg
  · intro v
    obtain ⟨f, hf, he⟩ := hOonto v
    exact ⟨Submodule.Quotient.mk f, hCoff f hf, he⟩

end GlobalTheory.CompanionTheory.BZPhiPG.Glue
