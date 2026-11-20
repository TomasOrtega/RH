import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureLApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLinePolynomialEquivarianceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftLeftInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivOpSpec

noncomputable section

namespace GlobalTheory.ThetaFibMax

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct

section Fibre

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Use `⟨fun x z hz => ?_, GlobalTheory.TensUniq.pure_mem_schA f φ hSB hstd⟩` and prove the remaining obligations. Establish `hz0 : ∀ v i, evFin F v (z i) = 0` using `fun v i => by`. Establish `h` using `congrFun (hz ((0, 1) : AF F) (map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F))) i`. Establish `h2 : (1 : Af F) * (z i).2 = 0` using `congrArg Prod.snd h`. Rewrite `h2` using `[one_mul]`.

Rewrite using `[evFin, AlgHom.comp_apply]`. Use `map_zero (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v)` and compare the differences between its conclusion and the goal. Conclude with `h2`. Simplify using `only [Pi.add_apply, map_add, hz0, add_zero]`.
-/
theorem rest_pure {κ : Type} [Fintype κ] (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ)
    (hSB : ∀ v, φ v ∈ SB (κ → Fv F v))
    (hstd : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) :
    Rest (evI F) (⇑f) (fun x => ∏ᶠ v, φ v fun i => evFin F v (x i)) := by
  refine ⟨fun x z hz => ?_, GlobalTheory.TensUniq.pure_mem_schA f φ hSB hstd⟩
  have hz0 : ∀ v i, evFin F v (z i) = 0 := fun v i => by
    have h := congrFun (hz ((0, 1) : AF F) (map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F))) i
    have h2 : (1 : Af F) * (z i).2 = 0 := congrArg Prod.snd h
    rw [one_mul] at h2
    rw [evFin, AlgHom.comp_apply]
    convert map_zero (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v)
    exact h2
  simp only [Pi.add_apply, map_add, hz0, add_zero]

/- English proof (translation)
The claim follows from `h _ (rest_pure f φ hSB hstd)`.
-/
theorem hasDerivAt_pure' {κ : Type} [Fintype κ] {T : ℝ → ((κ → AF F) → ℂ) → (κ → AF F) → ℂ} {f f₁ : SInf F κ}
    (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) (hSB : ∀ v, φ v ∈ SB (κ → Fv F v))
    (hstd : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
    (h : ActsD (evI F) T f f₁) :
    ∀ x, HasDerivAt (fun t => T t (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) x) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₁ φ x) 0 :=
  h _ (rest_pure f φ hSB hstd)

/- English proof (translation)
The claim follows from `h _ (rest_pure f φ hSB hstd)`.
-/
theorem acts_pure' {κ : Type} [Fintype κ] {T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ} {f f₁ : SInf F κ}
    (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) (hSB : ∀ v, φ v ∈ SB (κ → Fv F v))
    (hstd : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
    (h : Acts (evI F) T f f₁) : T (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₁ φ :=
  h _ (rest_pure f φ hSB hstd)

end Fibre

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {Y : Spc F E n} {W : Spc F E d}

/- English proof (translation)
The claim follows from `(hφ.2.and hstd).mono fun _ hv => hv.1.trans hv.2`.
-/
theorem good_std {M : Model σ Y W}
    (hstd : ∀ᶠ v in Filter.cofinite, M.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
    {φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ} (hφ : Good M φ) :
    ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 :=
  (hφ.2.and hstd).mono fun _ hv => hv.1.trans hv.2

/- English proof (translation)
Introduce `Φ hΦ`. Proceed by induction on `hΦ using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨f, hf, φ, h1, h2, rfl⟩` from `hy`. Take `⟨f₁, hf₁, hact⟩` from `hP f hf`.

Conclude with `⟨pure f₁ φ, Submodule.subset_span ⟨f₁, hf₁, φ, h1, h2, rfl⟩, hasDerivAt_pure' φ h1 (good_std hstd ⟨h1, h2⟩) hact⟩`. Consider the case `zero => exact ⟨0, zero_mem _, fun x => by simpa using hasDerivAt_const (0 : ℝ) (0 : ℂ)⟩`. Consider the case `add y z _ _ hy hz`. Take `⟨y₁, hy₁, hyd⟩` from `hy`. Take `⟨z₁, hz₁, hzd⟩` from `hz`.

Use `⟨y₁ + z₁, add_mem hy₁ hz₁, fun x => ?_⟩` and prove the remaining obligations. Establish `h2` using `(hyd x).add (hzd x)`. Establish `e : ((fun t => T t y x) + fun t => T t z x) = fun t => T t (y + z) x`. Use function extensionality and compare the values at `t`. Simplify using `[map_add]`.

Rewrite `h2` using `[e]`. Simplify using `using h2`. Consider the case `smul c y _ hy`. Take `⟨y₁, hy₁, hyd⟩` from `hy`. Use `⟨c • y₁, Submodule.smul_mem _ c hy₁, fun x => ?_⟩` and prove the remaining obligations.

Establish `h2` using `(hyd x).const_mul c`. Establish `e : (fun t => c * T t y x) = fun t => T t (c • y) x`. Use function extensionality and compare the values at `t`. Simplify using `[map_smul]`. Rewrite `h2` using `[e]`.

Simplify using `using h2`.
-/
theorem pureSpan_deriv (M : Model σ Y W) (P : Submodule ℂ (SInf F (Fin n × Fin d))) (T : ℝ → Module.End ℂ (Fn F n d))
    (hstd : ∀ᶠ v in Filter.cofinite, M.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
    (hP : ∀ f ∈ P, ∃ f₁ ∈ P, ActsD (evI F) (fun t => T t) f f₁) :
    ∀ Φ ∈ pureSpan M P, ∃ Φ₁ ∈ pureSpan M P, ∀ x, HasDerivAt (fun t => T t Φ x) (Φ₁ x) 0 := by
  intro Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨f, hf, φ, h1, h2, rfl⟩ := hy
    obtain ⟨f₁, hf₁, hact⟩ := hP f hf
    exact ⟨pure f₁ φ, Submodule.subset_span ⟨f₁, hf₁, φ, h1, h2, rfl⟩,
      hasDerivAt_pure' φ h1 (good_std hstd ⟨h1, h2⟩) hact⟩
  | zero => exact ⟨0, zero_mem _, fun x => by simpa using hasDerivAt_const (0 : ℝ) (0 : ℂ)⟩
  | add y z _ _ hy hz =>
    obtain ⟨y₁, hy₁, hyd⟩ := hy
    obtain ⟨z₁, hz₁, hzd⟩ := hz
    refine ⟨y₁ + z₁, add_mem hy₁ hz₁, fun x => ?_⟩
    have h2 := (hyd x).add (hzd x)
    have e : ((fun t => T t y x) + fun t => T t z x) = fun t => T t (y + z) x := by
      funext t; simp [map_add]
    rw [e] at h2
    simpa using h2
  | smul c y _ hy =>
    obtain ⟨y₁, hy₁, hyd⟩ := hy
    refine ⟨c • y₁, Submodule.smul_mem _ c hy₁, fun x => ?_⟩
    have h2 := (hyd x).const_mul c
    have e : (fun t => c * T t y x) = fun t => T t (c • y) x := by
      funext t; simp [map_smul]
    rw [e] at h2
    simpa using h2

/- English proof (translation)
Introduce `Φ hΦ`. Proceed by induction on `hΦ using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨f, hf, φ, h1, h2, rfl⟩` from `hy`. Take `⟨f₁, hf₁, hact⟩` from `hP f hf`.

Rewrite using `[acts_pure' φ h1 (good_std hstd ⟨h1, h2⟩) hact]`. Conclude with `Submodule.subset_span ⟨f₁, hf₁, φ, h1, h2, rfl⟩`. Consider the case `zero => rw [map_zero]`. Conclude with `zero_mem _`. Consider the case `add y z _ _ hy hz => rw [map_add]`.

Conclude with `add_mem hy hz`. Consider the case `smul c y _ hy => rw [map_smul]`. Conclude with `Submodule.smul_mem _ c hy`.
-/
theorem pureSpan_acts (M : Model σ Y W) (P : Submodule ℂ (SInf F (Fin n × Fin d))) (T : Module.End ℂ (Fn F n d))
    (hstd : ∀ᶠ v in Filter.cofinite, M.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
    (hP : ∀ f ∈ P, ∃ f₁ ∈ P, Acts (evI F) T f f₁) :
    ∀ Φ ∈ pureSpan M P, T Φ ∈ pureSpan M P := by
  intro Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨f, hf, φ, h1, h2, rfl⟩ := hy
    obtain ⟨f₁, hf₁, hact⟩ := hP f hf
    rw [acts_pure' φ h1 (good_std hstd ⟨h1, h2⟩) hact]
    exact Submodule.subset_span ⟨f₁, hf₁, φ, h1, h2, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | smul c y _ hy => rw [map_smul]; exact Submodule.smul_mem _ c hy

/- English proof (translation)
Establish `h1 : (1 : UA σ Y.J) ∈ UAt σ Y (evFin F v)`. Introduce `u _`. Use `show u • (mat (1 : UA σ Y.J) - 1) = 0`. Establish `: mat (1 : UA σ Y.J) = 1` using `rfl`. Rewrite using `[this, sub_self, smul_zero]`.

Introduce `Φ hΦ`. Proceed by induction on `hΦ using Submodule.span_induction with`. Consider the case `mem Ψ hΨ`. Take `⟨f, hf, φ, hSB, hev, rfl⟩` from `hΨ`. Establish `hstd : ∀ᶠ w in Filter.cofinite, φ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1` using `(hev.and hP.good.std).mono fun w hw => hw.1.trans hw.2`.

Take `⟨φ₁, ⟨hφ₁, hact⟩, -⟩` from `(hA F E σ B n d Y W M χX χW om r s r' s' hP v).1 1 h1 h hh (φ v) (hSB v)`. Take `⟨ρ, hρ, hρt⟩` from `GlobalTheory.PureFactor.exists_rest_factor v f φ hstd`. Establish `hpure : tens (evFin F v) (φ v) ρ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ`. Rewrite using `[hρt, Function.update_eq_self]`. Establish `hRest : Rest (evFin F v) (φ v) ρ` using `⟨hρ, by rw [hpure]; exact GlobalTheory.TensUniq.pure_mem_schA f φ hSB hstd⟩`.

Establish `hmap : om (1, h) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (Function.update φ v φ₁)`. Rewrite using `[← hpure, hact ρ hRest, hρt]`. Rewrite using `[hmap]`. Use `Submodule.subset_span ⟨f, hf, Function.update φ v φ₁, fun w => ?_, ?_, rfl⟩` and prove the remaining obligations. Distinguish the cases in `hw : w = v`.

Substitute `hw` using the available equality. Rewrite using `[Function.update_self]`. Conclude with `hφ₁`. Rewrite using `[Function.update_of_ne hw]`. Conclude with `hSB w`.

Use `filter_upwards [hev, Filter.eventually_cofinite_ne v] with w hw hne`. Rewrite using `[Function.update_of_ne hne]`. Conclude with `hw`. Consider the case `zero => rw [map_zero]`. Conclude with `zero_mem _`.

Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `add_mem hx hy`. Consider the case `smul c x _ hx => rw [map_smul]`. Conclude with `Submodule.smul_mem _ c hx`.
-/
theorem pureSpan_fin (hA : ActsEx) (B : Base F E) (M : Model σ Y W) {χX χW : Chr F E} {om : Rep σ Y W} {r s r' s' : ℕ}
    (hP : IsPair B M χX χW om r s r' s') (P : Submodule ℂ (SInf F (Fin n × Fin d))) (v : Pl F)
    (h : UA σ W.J) (hh : h ∈ UAt σ W (evFin F v)) : ∀ Φ ∈ pureSpan M P, om (1, h) Φ ∈ pureSpan M P := by
  classical
  have h1 : (1 : UA σ Y.J) ∈ UAt σ Y (evFin F v) := by
    intro u _
    show u • (mat (1 : UA σ Y.J) - 1) = 0
    have : mat (1 : UA σ Y.J) = 1 := rfl
    rw [this, sub_self, smul_zero]
  intro Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem Ψ hΨ =>
    obtain ⟨f, hf, φ, hSB, hev, rfl⟩ := hΨ
    have hstd : ∀ᶠ w in Filter.cofinite, φ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 :=
      (hev.and hP.good.std).mono fun w hw => hw.1.trans hw.2
    obtain ⟨φ₁, ⟨hφ₁, hact⟩, -⟩ := (hA F E σ B n d Y W M χX χW om r s r' s' hP v).1 1 h1 h hh (φ v) (hSB v)
    obtain ⟨ρ, hρ, hρt⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φ hstd
    have hpure : tens (evFin F v) (φ v) ρ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ := by
      rw [hρt, Function.update_eq_self]
    have hRest : Rest (evFin F v) (φ v) ρ := ⟨hρ, by rw [hpure]; exact GlobalTheory.TensUniq.pure_mem_schA f φ hSB hstd⟩
    have hmap : om (1, h) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (Function.update φ v φ₁) := by
      rw [← hpure, hact ρ hRest, hρt]
    rw [hmap]
    refine Submodule.subset_span ⟨f, hf, Function.update φ v φ₁, fun w => ?_, ?_, rfl⟩
    · by_cases hw : w = v
      · subst hw; rw [Function.update_self]; exact hφ₁
      · rw [Function.update_of_ne hw]; exact hSB w
    · filter_upwards [hev, Filter.eventually_cofinite_ne v] with w hw hne
      rw [Function.update_of_ne hne]; exact hw
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Use `choose! g hgS hglt using hcon`. Establish `hcS : ∀ k : ℕ, g^[k] x₀ ∈ S`. Introduce `k`.

Proceed by induction on `k with`. Consider the case `zero => exact hx₀`. Consider the case `succ k ih => rw [Function.iterate_succ_apply']`. Conclude with `hgS _ ih`. Establish `hanti : StrictAnti fun k : ℕ => g^[k] x₀` using `strictAnti_nat_of_succ_lt fun k => by show g^[k + 1] x₀ < g^[k] x₀`.

Rewrite using `[Function.iterate_succ_apply']`. Conclude with `hglt _ (hcS k)`. Establish `hmono : StrictMono fun i : Fin (L + 1) => g^[L - i.1] x₀`. Introduce `i j hij`. Establish `hj` using `j.isLt`.

Establish `hij' : i.1 < j.1` using `hij`. Conclude with `hanti (by omega)`. Use `hL (L + 1) _ hmono fun i => hS _ (hcS _)` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_minimal_of_chain {α : Type} [PartialOrder α] (Θ : α → Prop) (L : ℕ)
    (hL : ∀ (m : ℕ) (c : Fin m → α), StrictMono c → (∀ i, Θ (c i)) → m ≤ L) (S : Set α) (hS : ∀ x ∈ S, Θ x)
    (x₀ : α) (hx₀ : x₀ ∈ S) : ∃ y ∈ S, ∀ z ∈ S, ¬ z < y := by
  by_contra hcon
  push_neg at hcon
  choose! g hgS hglt using hcon
  have hcS : ∀ k : ℕ, g^[k] x₀ ∈ S := by
    intro k
    induction k with
    | zero => exact hx₀
    | succ k ih => rw [Function.iterate_succ_apply']; exact hgS _ ih
  have hanti : StrictAnti fun k : ℕ => g^[k] x₀ :=
    strictAnti_nat_of_succ_lt fun k => by
      show g^[k + 1] x₀ < g^[k] x₀
      rw [Function.iterate_succ_apply']
      exact hglt _ (hcS k)
  have hmono : StrictMono fun i : Fin (L + 1) => g^[L - i.1] x₀ := by
    intro i j hij
    have hj := j.isLt
    have hij' : i.1 < j.1 := hij
    exact hanti (by omega)
  have := hL (L + 1) _ hmono fun i => hS _ (hcS _)
  omega

end GlobalTheory.ThetaFibMax

namespace GlobalTheory.ThetaFibMax

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {Y : Spc F E n} {W : Spc F E d}

set_option synthInstance.maxHeartbeats 400000

section Core

variable (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W) (N : Submodule ℂ (Fn F n d))
  (hN : GlobalTheory.ThetaFac.WStable B om (PolData B M) N)

/- English proof (translation)
Rewrite using `[← LinearMap.map_smul]`. Both sides reduce to the same expression.
-/
theorem smul_mk (A : Module.End ℂ (PolData B M)) (hA : A ∈ ops B om (PolData B M)) (x : PolData B M) :
    (⟨A, Algebra.subset_adjoin hA⟩ : Alg B M om) • (Nr B M om N hN).mkQ x = (Nr B M om N hN).mkQ (A x) := by
  rw [← LinearMap.map_smul]; rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `⟨y.2, hy⟩`. Introduce and unpack `⟨hf, h⟩`. Conclude with `⟨⟨f, hf⟩, h, rfl⟩`.
-/
theorem mem_pre (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) (hφ : Good M φ)
    (T : Submodule (Alg B M om) (PolData B M ⧸ Nr B M om N hN)) (f : SInf F (Fin n × Fin d)) :
    f ∈ ((T.restrictScalars ℂ).comap (iota B M om N hN φ hφ)).map (M.Pol B.ψ B.emb).subtype ↔
      ∃ hf : f ∈ M.Pol B.ψ B.emb, iota B M om N hN φ hφ ⟨f, hf⟩ ∈ T := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hf, h⟩
    exact ⟨⟨f, hf⟩, h, rfl⟩

variable {B M om N hN}

/- English proof (translation)
Establish `hs` using `good_std hstd hφ`. Rewrite using `[iota_apply, smul_mk B M om N hN A hA]`. Break down `hA with ⟨γ, hγ, hex, rfl⟩ | ⟨k, hk, hk', rfl⟩` into its components or cases. Take `⟨f₁, hf₁, hact, -⟩` from `hP3 γ hγ f.1 f.2`. Use `⟨⟨f₁, hf₁⟩, ?_, fun P hP hfP => hP.2.2.2.1 γ hγ f.1 hfP f₁ hact⟩` and prove the remaining obligations.

Rewrite using `[iota_apply]`. Use `congr 1`. Conclude with `Subtype.ext (derivOp_eq hex _ _ (hasDerivAt_pure' φ hφ.1 hs hact))`. Take `⟨f₁, hf₁, hact, -⟩` from `hP4 k hk f.1 f.2`. Use `⟨⟨f₁, hf₁⟩, ?_, fun P hP hfP => hP.2.2.2.2 k hk f.1 hfP f₁ hact⟩` and prove the remaining obligations.

Rewrite using `[iota_apply]`. Use `congr 1`. Conclude with `Subtype.ext (acts_pure' φ hφ.1 hs hact)`.
-/
theorem ops_iota
    (hstd : ∀ᶠ v in Filter.cofinite, M.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
    (hP3 : ∀ γ ∈ Lines σ W, ∀ f ∈ M.Pol B.ψ B.emb, ∃ f₁ ∈ M.Pol B.ψ B.emb,
      ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ ∧ ∀ f₂ : SInf F (Fin n × Fin d),
        ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₂ → f₂ = f₁)
    (hP4 : ∀ k ∈ KInf σ W B.emb, ∀ f ∈ M.Pol B.ψ B.emb, ∃ f₁ ∈ M.Pol B.ψ B.emb,
      Acts (evI F) (om (1, k)) f f₁ ∧ ∀ f₂ : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) f f₂ → f₂ = f₁)
    {φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ} (hφ : Good M φ)
    (A : Module.End ℂ (PolData B M)) (hA : A ∈ ops B om (PolData B M)) (f : M.Pol B.ψ B.emb) :
    ∃ f₁ : M.Pol B.ψ B.emb, (⟨A, Algebra.subset_adjoin hA⟩ : Alg B M om) • iota B M om N hN φ hφ f =
      iota B M om N hN φ hφ f₁ ∧
      ∀ P : Submodule ℂ (SInf F (Fin n × Fin d)), GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om P → f.1 ∈ P → f₁.1 ∈ P := by
  have hs := good_std hstd hφ
  rw [iota_apply, smul_mk B M om N hN A hA]
  rcases hA with ⟨γ, hγ, hex, rfl⟩ | ⟨k, hk, hk', rfl⟩
  · obtain ⟨f₁, hf₁, hact, -⟩ := hP3 γ hγ f.1 f.2
    refine ⟨⟨f₁, hf₁⟩, ?_, fun P hP hfP => hP.2.2.2.1 γ hγ f.1 hfP f₁ hact⟩
    rw [iota_apply]
    congr 1
    exact Subtype.ext (derivOp_eq hex _ _ (hasDerivAt_pure' φ hφ.1 hs hact))
  · obtain ⟨f₁, hf₁, hact, -⟩ := hP4 k hk f.1 f.2
    refine ⟨⟨f₁, hf₁⟩, ?_, fun P hP hfP => hP.2.2.2.2 k hk f.1 hfP f₁ hact⟩
    rw [iota_apply]
    congr 1
    exact Subtype.ext (acts_pure' φ hφ.1 hs hact)

/- English proof (translation)
Use `⟨quotSub _ (Nr B M om N hN) ((P.comap (M.Pol B.ψ B.emb).subtype).map (iota B M om N hN φ hφ)) ?_, fun q => ?_⟩` and prove the remaining obligations. Introduce `A hA x hx`. Take `⟨f, hfP, hfx⟩` from `hx`. Take `⟨f₁, he, hP'⟩` from `ops_iota hstd hP3 hP4 hφ A hA f`. Use `⟨f₁, hP' P hP hfP, ?_⟩` and prove the remaining obligations.

Rewrite using `[← smul_mk B M om N hN A hA x, ← hfx, he]`. Rewrite using `[mem_quotSub]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨f, hf, rfl⟩`. Conclude with `⟨f, hf, rfl⟩`.

Introduce and unpack `⟨f, hf, rfl⟩`. Conclude with `⟨f, hf, rfl⟩`.
-/
theorem exists_img
    (hstd : ∀ᶠ v in Filter.cofinite, M.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
    (hP3 : ∀ γ ∈ Lines σ W, ∀ f ∈ M.Pol B.ψ B.emb, ∃ f₁ ∈ M.Pol B.ψ B.emb,
      ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ ∧ ∀ f₂ : SInf F (Fin n × Fin d),
        ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₂ → f₂ = f₁)
    (hP4 : ∀ k ∈ KInf σ W B.emb, ∀ f ∈ M.Pol B.ψ B.emb, ∃ f₁ ∈ M.Pol B.ψ B.emb,
      Acts (evI F) (om (1, k)) f f₁ ∧ ∀ f₂ : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) f f₂ → f₂ = f₁)
    {φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ} (hφ : Good M φ)
    (P : Submodule ℂ (SInf F (Fin n × Fin d))) (hP : GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om P) :
    ∃ T : Submodule (Alg B M om) (PolData B M ⧸ Nr B M om N hN),
      ∀ q, q ∈ T ↔ ∃ f : M.Pol B.ψ B.emb, f.1 ∈ P ∧ iota B M om N hN φ hφ f = q := by
  refine ⟨quotSub _ (Nr B M om N hN) ((P.comap (M.Pol B.ψ B.emb).subtype).map (iota B M om N hN φ hφ)) ?_,
    fun q => ?_⟩
  · intro A hA x hx
    obtain ⟨f, hfP, hfx⟩ := hx
    obtain ⟨f₁, he, hP'⟩ := ops_iota hstd hP3 hP4 hφ A hA f
    refine ⟨f₁, hP' P hP hfP, ?_⟩
    rw [← smul_mk B M om N hN A hA x, ← hfx, he]
  · rw [mem_quotSub]
    constructor
    · rintro ⟨f, hf, rfl⟩; exact ⟨f, hf, rfl⟩
    · rintro ⟨f, hf, rfl⟩; exact ⟨f, hf, rfl⟩

/- English proof (translation)
Establish `hs` using `good_std hstd hφ`. Establish `h₁` using `hP1 γ hγ f hf f₁ h`. Conclude with `⟨h₁, hNc.lie γ hγ _ (Submodule.subset_span ⟨f, hf, φ, hφ.1, hφ.2, rfl⟩) _ (Submodule.subset_span ⟨f₁, h₁, φ, hφ.1, hφ.2, rfl⟩) (hasDerivAt_pure' φ hφ.1 hs h)⟩`.
-/
theorem coinv_lie
    (hstd : ∀ᶠ v in Filter.cofinite, M.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
    (hP1 : ∀ γ ∈ Lines σ Y, ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
      ActsD (evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) f f₁ → f₁ ∈ M.Pol B.ψ B.emb)
    (hNc : GlobalTheory.ThetaFac.CoinvLe B om (PolData B M) N)
    {φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ} (hφ : Good M φ)
    (γ) (hγ : γ ∈ Lines σ Y) (f) (hf : f ∈ M.Pol B.ψ B.emb) (f₁ : SInf F (Fin n × Fin d))
    (h : ActsD (evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) f f₁) :
    f₁ ∈ M.Pol B.ψ B.emb ∧ pure f₁ φ ∈ N := by
  have hs := good_std hstd hφ
  have h₁ := hP1 γ hγ f hf f₁ h
  exact ⟨h₁, hNc.lie γ hγ _ (Submodule.subset_span ⟨f, hf, φ, hφ.1, hφ.2, rfl⟩) _
    (Submodule.subset_span ⟨f₁, h₁, φ, hφ.1, hφ.2, rfl⟩) (hasDerivAt_pure' φ hφ.1 hs h)⟩

/- English proof (translation)
Establish `hs` using `good_std hstd hφ`. Use `⟨hP2 k hk f hf f₁ h, ?_⟩` and prove the remaining obligations. Establish `e : pure (f₁ - f) φ = om (k, 1) (pure f φ) - pure f φ`. Rewrite using `[acts_pure' φ hφ.1 hs h, ← GlobalTheory.ThetaFacInf.pureL_apply, ← GlobalTheory.ThetaFacInf.pureL_apply, ← GlobalTheory.ThetaFacInf.pureL_apply, map_sub]`. Rewrite using `[e]`.

Conclude with `hNc.cpt k hk _ (Submodule.subset_span ⟨f, hf, φ, hφ.1, hφ.2, rfl⟩)`.
-/
theorem coinv_cpt
    (hstd : ∀ᶠ v in Filter.cofinite, M.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
    (hP2 : ∀ k ∈ KInf σ Y B.emb, ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
      Acts (evI F) (om (k, 1)) f f₁ → f₁ ∈ M.Pol B.ψ B.emb)
    (hNc : GlobalTheory.ThetaFac.CoinvLe B om (PolData B M) N)
    {φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ} (hφ : Good M φ)
    (k) (hk : k ∈ KInf σ Y B.emb) (f) (hf : f ∈ M.Pol B.ψ B.emb) (f₁ : SInf F (Fin n × Fin d))
    (h : Acts (evI F) (om (k, 1)) f f₁) :
    f₁ ∈ M.Pol B.ψ B.emb ∧ pure (f₁ - f) φ ∈ N := by
  have hs := good_std hstd hφ
  refine ⟨hP2 k hk f hf f₁ h, ?_⟩
  have e : pure (f₁ - f) φ = om (k, 1) (pure f φ) - pure f φ := by
    rw [acts_pure' φ hφ.1 hs h, ← GlobalTheory.ThetaFacInf.pureL_apply, ← GlobalTheory.ThetaFacInf.pureL_apply,
      ← GlobalTheory.ThetaFacInf.pureL_apply, map_sub]
  rw [e]
  exact hNc.cpt k hk _ (Submodule.subset_span ⟨f, hf, φ, hφ.1, hφ.2, rfl⟩)

/- English proof (translation)
Establish `hs` using `good_std hstd hφ`. Use `⟨inf_le_left.trans hP₀.1, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `γ hγ f hf f₁ h`. Take `⟨h1, h2⟩` from `coinv_lie hstd hP1 hNc hφ γ hγ f hf f₁ h`. Use `⟨hP₀.2.1 γ hγ f hf f₁ h, (mem_pre B M om N hN φ hφ T f₁).2 ⟨h1, ?_⟩⟩` and prove the remaining obligations.

Rewrite using `[(iota_eq_zero B M om N hN φ hφ ⟨f₁, h1⟩).2 h2]`. Conclude with `zero_mem _`. Introduce `k hk f hf f₁ h`. Take `⟨h1, h2⟩` from `coinv_cpt hstd hP2 hNc hφ k hk f hf f₁ h`. Use `⟨hP₀.2.2.1 k hk f hf f₁ h, (mem_pre B M om N hN φ hφ T (f₁ - f)).2 ⟨sub_mem h1 hf, ?_⟩⟩` and prove the remaining obligations.

Rewrite using `[(iota_eq_zero B M om N hN φ hφ ⟨f₁ - f, sub_mem h1 hf⟩).2 h2]`. Conclude with `zero_mem _`. Introduce `γ hγ f hf f₁ h`. Take `⟨hfP₀, hfpre⟩` from `hf`. Take `⟨hfPol, hfT⟩` from `(mem_pre B M om N hN φ hφ T f).1 hfpre`.

Establish `hf₁P₀` using `hP₀.2.2.2.1 γ hγ f hfP₀ f₁ h`. Establish `hf₁Pol` using `hP₀.1 hf₁P₀`. Use `⟨hf₁P₀, (mem_pre B M om N hN φ hφ T f₁).2 ⟨hf₁Pol, ?_⟩⟩` and prove the remaining obligations. Establish `hA : derivOp (PolData B M) (fun t => om (1, γ (Multiplicative.ofAdd t))) (hexD γ hγ) ∈ ops B om (PolData B M)` using `Or.inl ⟨γ, hγ, hexD γ hγ, rfl⟩`. Establish `e : iota B M om N hN φ hφ ⟨f₁, hf₁Pol⟩ = (⟨_, Algebra.subset_adjoin hA⟩ : Alg B M om) • iota B M om N hN φ hφ ⟨f, hfPol⟩`.

Rewrite using `[iota_apply, iota_apply, smul_mk B M om N hN _ hA]`. Use `congr 1`. Conclude with `Subtype.ext (derivOp_eq (hexD γ hγ) _ _ (hasDerivAt_pure' φ hφ.1 hs h)).symm`. Rewrite using `[e]`. Conclude with `T.smul_mem _ hfT`.

Introduce `k hk f hf f₁ h`. Take `⟨hfP₀, hfpre⟩` from `hf`. Take `⟨hfPol, hfT⟩` from `(mem_pre B M om N hN φ hφ T f).1 hfpre`. Establish `hf₁P₀` using `hP₀.2.2.2.2 k hk f hfP₀ f₁ h`. Establish `hf₁Pol` using `hP₀.1 hf₁P₀`.

Use `⟨hf₁P₀, (mem_pre B M om N hN φ hφ T f₁).2 ⟨hf₁Pol, ?_⟩⟩` and prove the remaining obligations. Establish `hA : (om (1, k)).restrict (hkD k hk) ∈ ops B om (PolData B M)` using `Or.inr ⟨k, hk, hkD k hk, rfl⟩`. Establish `e : iota B M om N hN φ hφ ⟨f₁, hf₁Pol⟩ = (⟨_, Algebra.subset_adjoin hA⟩ : Alg B M om) • iota B M om N hN φ hφ ⟨f, hfPol⟩`. Rewrite using `[iota_apply, iota_apply, smul_mk B M om N hN _ hA]`. Use `congr 1`.

Conclude with `Subtype.ext (acts_pure' φ hφ.1 hs h).symm`. Rewrite using `[e]`. Conclude with `T.smul_mem _ hfT`.
-/
theorem thetaSub_pre
    (hstd : ∀ᶠ v in Filter.cofinite, M.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
    (hP1 : ∀ γ ∈ Lines σ Y, ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
      ActsD (evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) f f₁ → f₁ ∈ M.Pol B.ψ B.emb)
    (hP2 : ∀ k ∈ KInf σ Y B.emb, ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
      Acts (evI F) (om (k, 1)) f f₁ → f₁ ∈ M.Pol B.ψ B.emb)
    (hNc : GlobalTheory.ThetaFac.CoinvLe B om (PolData B M) N)
    (hexD : ∀ γ ∈ Lines σ W, ∀ Φ ∈ PolData B M, ∃ Φ₁ ∈ PolData B M,
      ∀ x, HasDerivAt (fun t => om (1, γ (Multiplicative.ofAdd t)) Φ x) (Φ₁ x) 0)
    (hkD : ∀ k ∈ KInf σ W B.emb, ∀ Φ ∈ PolData B M, om (1, k) Φ ∈ PolData B M)
    {φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ} (hφ : Good M φ)
    (P₀ : Submodule ℂ (SInf F (Fin n × Fin d))) (hP₀ : GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om P₀)
    (T : Submodule (Alg B M om) (PolData B M ⧸ Nr B M om N hN)) :
    GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om
      (P₀ ⊓ ((T.restrictScalars ℂ).comap (iota B M om N hN φ hφ)).map (M.Pol B.ψ B.emb).subtype) := by
  have hs := good_std hstd hφ
  refine ⟨inf_le_left.trans hP₀.1, ?_, ?_, ?_, ?_⟩
  · intro γ hγ f hf f₁ h
    obtain ⟨h1, h2⟩ := coinv_lie hstd hP1 hNc hφ γ hγ f hf f₁ h
    refine ⟨hP₀.2.1 γ hγ f hf f₁ h, (mem_pre B M om N hN φ hφ T f₁).2 ⟨h1, ?_⟩⟩
    rw [(iota_eq_zero B M om N hN φ hφ ⟨f₁, h1⟩).2 h2]
    exact zero_mem _
  · intro k hk f hf f₁ h
    obtain ⟨h1, h2⟩ := coinv_cpt hstd hP2 hNc hφ k hk f hf f₁ h
    refine ⟨hP₀.2.2.1 k hk f hf f₁ h, (mem_pre B M om N hN φ hφ T (f₁ - f)).2 ⟨sub_mem h1 hf, ?_⟩⟩
    rw [(iota_eq_zero B M om N hN φ hφ ⟨f₁ - f, sub_mem h1 hf⟩).2 h2]
    exact zero_mem _
  · intro γ hγ f hf f₁ h
    obtain ⟨hfP₀, hfpre⟩ := hf
    obtain ⟨hfPol, hfT⟩ := (mem_pre B M om N hN φ hφ T f).1 hfpre
    have hf₁P₀ := hP₀.2.2.2.1 γ hγ f hfP₀ f₁ h
    have hf₁Pol := hP₀.1 hf₁P₀
    refine ⟨hf₁P₀, (mem_pre B M om N hN φ hφ T f₁).2 ⟨hf₁Pol, ?_⟩⟩
    have hA : derivOp (PolData B M) (fun t => om (1, γ (Multiplicative.ofAdd t))) (hexD γ hγ) ∈
        ops B om (PolData B M) := Or.inl ⟨γ, hγ, hexD γ hγ, rfl⟩
    have e : iota B M om N hN φ hφ ⟨f₁, hf₁Pol⟩ =
        (⟨_, Algebra.subset_adjoin hA⟩ : Alg B M om) • iota B M om N hN φ hφ ⟨f, hfPol⟩ := by
      rw [iota_apply, iota_apply, smul_mk B M om N hN _ hA]
      congr 1
      exact Subtype.ext (derivOp_eq (hexD γ hγ) _ _ (hasDerivAt_pure' φ hφ.1 hs h)).symm
    rw [e]
    exact T.smul_mem _ hfT
  · intro k hk f hf f₁ h
    obtain ⟨hfP₀, hfpre⟩ := hf
    obtain ⟨hfPol, hfT⟩ := (mem_pre B M om N hN φ hφ T f).1 hfpre
    have hf₁P₀ := hP₀.2.2.2.2 k hk f hfP₀ f₁ h
    have hf₁Pol := hP₀.1 hf₁P₀
    refine ⟨hf₁P₀, (mem_pre B M om N hN φ hφ T f₁).2 ⟨hf₁Pol, ?_⟩⟩
    have hA : (om (1, k)).restrict (hkD k hk) ∈ ops B om (PolData B M) := Or.inr ⟨k, hk, hkD k hk, rfl⟩
    have e : iota B M om N hN φ hφ ⟨f₁, hf₁Pol⟩ =
        (⟨_, Algebra.subset_adjoin hA⟩ : Alg B M om) • iota B M om N hN φ hφ ⟨f, hfPol⟩ := by
      rw [iota_apply, iota_apply, smul_mk B M om N hN _ hA]
      congr 1
      exact Subtype.ext (acts_pure' φ hφ.1 hs h).symm
    rw [e]
    exact T.smul_mem _ hfT

/- English proof (translation)
Apply `Submodule.span_mono` to reduce the goal to its premises. Introduce and unpack `_ ⟨f, hf, φ, h1, h2, rfl⟩`. Conclude with `⟨f, hP hf, φ, h1, h2, rfl⟩`.
-/
theorem pureSpan_le (M : Model σ Y W) (B : Base F E) (P : Submodule ℂ (SInf F (Fin n × Fin d)))
    (hP : P ≤ M.Pol B.ψ B.emb) : pureSpan M P ≤ PolData B M := by
  apply Submodule.span_mono
  rintro _ ⟨f, hf, φ, h1, h2, rfl⟩
  exact ⟨f, hP hf, φ, h1, h2, rfl⟩

/- English proof (translation)
Establish `hPl : P ≤ M.Pol B.ψ B.emb` using `hP.1`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `v h hh Φ hΦ`. Take `⟨a, ha, b, hb, rfl⟩` from `Submodule.mem_sup.1 hΦ`. Rewrite using `[map_add]`.

Conclude with `Submodule.add_mem_sup (hNm.stab.fin v h hh a ha) (hfin v h hh b hb)`. Introduce `γ hγ Φ hΦ Φ₁ _ hder`. Take `⟨a, ha, b, hb, rfl⟩` from `Submodule.mem_sup.1 hΦ`. Take `⟨a₁, ha₁D, ha₁⟩` from `pureSpan_deriv M (M.Pol B.ψ B.emb) (fun t => om (1, γ (Multiplicative.ofAdd t))) hstd (fun f hf => by obtain ⟨f₁, hf₁, hact, -⟩ := hP3 γ hγ f hf; exact ⟨f₁, hf₁, hact⟩) a (hNm.le ha)`. Establish `ha₁N` using `hNm.stab.lie γ hγ a ha a₁ ha₁D ha₁`.

Take `⟨b₁, hb₁, hb₁d⟩` from `pureSpan_deriv M P (fun t => om (1, γ (Multiplicative.ofAdd t))) hstd (fun f hf => by`. Take `⟨f₁, -, hact, -⟩` from `hP3 γ hγ f (hPl hf)`. Conclude with `⟨f₁, hP.2.2.2.1 γ hγ f hf f₁ hact, hact⟩) b hb`. Establish `e : Φ₁ = a₁ + b₁`. Use function extensionality and compare the values at `x`.

Establish `h2` using `(ha₁ x).add (hb₁d x)`. Establish `e2 : ((fun t => om (1, γ (Multiplicative.ofAdd t)) a x) + fun t => om (1, γ (Multiplicative.ofAdd t)) b x) = fun t => om (1, γ (Multiplicative.ofAdd t)) (a + b) x`. Use function extensionality and compare the values at `t`. Simplify using `[map_add]`. Rewrite `h2` using `[e2]`.

Conclude with `(hder x).unique h2`. Rewrite using `[e]`. Conclude with `Submodule.add_mem_sup ha₁N hb₁`. Introduce `k hk Φ hΦ`. Take `⟨a, ha, b, hb, rfl⟩` from `Submodule.mem_sup.1 hΦ`.

Rewrite using `[map_add]`. Use `Submodule.add_mem_sup (hNm.stab.cpt k hk a ha) (pureSpan_acts M P (om (1, k)) hstd (fun f hf => ?_) b hb)` and prove the remaining obligations. Take `⟨f₁, -, hact, -⟩` from `hP4 k hk f (hPl hf)`. Conclude with `⟨f₁, hP.2.2.2.2 k hk f hf f₁ hact, hact⟩`.
-/
theorem sup_wstable
    (hstd : ∀ᶠ v in Filter.cofinite, M.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
    (hP3 : ∀ γ ∈ Lines σ W, ∀ f ∈ M.Pol B.ψ B.emb, ∃ f₁ ∈ M.Pol B.ψ B.emb,
      ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ ∧ ∀ f₂ : SInf F (Fin n × Fin d),
        ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₂ → f₂ = f₁)
    (hP4 : ∀ k ∈ KInf σ W B.emb, ∀ f ∈ M.Pol B.ψ B.emb, ∃ f₁ ∈ M.Pol B.ψ B.emb,
      Acts (evI F) (om (1, k)) f f₁ ∧ ∀ f₂ : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) f f₂ → f₂ = f₁)
    (P : Submodule ℂ (SInf F (Fin n × Fin d))) (hP : GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om P)
    (hfin : ∀ v : Pl F, ∀ h ∈ UAt σ W (evFin F v), ∀ Φ ∈ pureSpan M P, om (1, h) Φ ∈ pureSpan M P)
    (hNm : GlobalTheory.ThetaFac.IsMaxTh B om (PolData B M) N) :
    GlobalTheory.ThetaFac.WStable B om (PolData B M) (N ⊔ pureSpan M P) := by
  have hPl : P ≤ M.Pol B.ψ B.emb := hP.1
  refine ⟨?_, ?_, ?_⟩
  · intro v h hh Φ hΦ
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hΦ
    rw [map_add]
    exact Submodule.add_mem_sup (hNm.stab.fin v h hh a ha) (hfin v h hh b hb)
  · intro γ hγ Φ hΦ Φ₁ _ hder
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hΦ
    obtain ⟨a₁, ha₁D, ha₁⟩ := pureSpan_deriv M (M.Pol B.ψ B.emb) (fun t => om (1, γ (Multiplicative.ofAdd t))) hstd
      (fun f hf => by obtain ⟨f₁, hf₁, hact, -⟩ := hP3 γ hγ f hf; exact ⟨f₁, hf₁, hact⟩) a (hNm.le ha)
    have ha₁N := hNm.stab.lie γ hγ a ha a₁ ha₁D ha₁
    obtain ⟨b₁, hb₁, hb₁d⟩ := pureSpan_deriv M P (fun t => om (1, γ (Multiplicative.ofAdd t))) hstd
      (fun f hf => by
        obtain ⟨f₁, -, hact, -⟩ := hP3 γ hγ f (hPl hf)
        exact ⟨f₁, hP.2.2.2.1 γ hγ f hf f₁ hact, hact⟩) b hb
    have e : Φ₁ = a₁ + b₁ := by
      funext x
      have h2 := (ha₁ x).add (hb₁d x)
      have e2 : ((fun t => om (1, γ (Multiplicative.ofAdd t)) a x) + fun t => om (1, γ (Multiplicative.ofAdd t)) b x) =
          fun t => om (1, γ (Multiplicative.ofAdd t)) (a + b) x := by
        funext t; simp [map_add]
      rw [e2] at h2
      exact (hder x).unique h2
    rw [e]
    exact Submodule.add_mem_sup ha₁N hb₁
  · intro k hk Φ hΦ
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hΦ
    rw [map_add]
    refine Submodule.add_mem_sup (hNm.stab.cpt k hk a ha) (pureSpan_acts M P (om (1, k)) hstd (fun f hf => ?_) b hb)
    obtain ⟨f₁, -, hact, -⟩ := hP4 k hk f (hPl hf)
    exact ⟨f₁, hP.2.2.2.2 k hk f hf f₁ hact, hact⟩

/- English proof (translation)
Proceed by induction on `q using Submodule.Quotient.induction_on with`. Consider the case `H x`. Establish `hx : x.1 ∈ N ⊔ pureSpan M P` using `by rw [hS]; exact x.2`. Take `⟨a, ha, b, hb, hab⟩` from `Submodule.mem_sup.1 hx`. Establish `hbD : b ∈ PolData B M` using `pureSpan_le M B P hPl hb`.

Establish `e : (Submodule.Quotient.mk x : PolData B M ⧸ Nr B M om N hN) = Submodule.Quotient.mk ⟨b, hbD⟩`. Rewrite using `[Submodule.Quotient.eq]`. Use `show x.1 - b ∈ N`. Rewrite using `[← hab, add_sub_cancel_right]`. Conclude with `ha`.

Rewrite using `[e]`. Use `clear e hab ha hx`. Proceed by induction on `hb using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨f, hf, φ, h1, h2, rfl⟩` from `hy`.

Conclude with `Submodule.subset_span ⟨φ, ⟨h1, h2⟩, ⟨f, hPl hf⟩, hf, rfl⟩`. Consider the case `zero`. Establish `: (⟨0, hbD⟩ : PolData B M) = 0` using `rfl`. Rewrite using `[this, Submodule.Quotient.mk_zero]`. Conclude with `zero_mem _`.

Consider the case `add y z hy hz ihy ihz`. Establish `hyD` using `pureSpan_le M B P hPl hy`. Establish `hzD` using `pureSpan_le M B P hPl hz`. Establish `: (⟨y + z, hbD⟩ : PolData B M) = ⟨y, hyD⟩ + ⟨z, hzD⟩` using `rfl`. Rewrite using `[this, Submodule.Quotient.mk_add]`.

Conclude with `add_mem (ihy hyD) (ihz hzD)`. Consider the case `smul c y hy ihy`. Establish `hyD` using `pureSpan_le M B P hPl hy`. Establish `: (⟨c • y, hbD⟩ : PolData B M) = c • ⟨y, hyD⟩` using `rfl`. Rewrite using `[this, Submodule.Quotient.mk_smul]`.

Conclude with `Submodule.smul_of_tower_mem _ c (ihy hyD)`.
-/
theorem span_top (P : Submodule ℂ (SInf F (Fin n × Fin d))) (hPl : P ≤ M.Pol B.ψ B.emb)
    (hS : N ⊔ pureSpan M P = PolData B M) (q : PolData B M ⧸ Nr B M om N hN) :
    q ∈ Submodule.span (Alg B M om) {q | ∃ φ, ∃ hφ : Good M φ, ∃ f : M.Pol B.ψ B.emb, f.1 ∈ P ∧
      iota B M om N hN φ hφ f = q} := by
  induction q using Submodule.Quotient.induction_on with
  | H x =>
  have hx : x.1 ∈ N ⊔ pureSpan M P := by rw [hS]; exact x.2
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hx
  have hbD : b ∈ PolData B M := pureSpan_le M B P hPl hb
  have e : (Submodule.Quotient.mk x : PolData B M ⧸ Nr B M om N hN) = Submodule.Quotient.mk ⟨b, hbD⟩ := by
    rw [Submodule.Quotient.eq]
    show x.1 - b ∈ N
    rw [← hab, add_sub_cancel_right]
    exact ha
  rw [e]
  clear e hab ha hx
  induction hb using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨f, hf, φ, h1, h2, rfl⟩ := hy
    exact Submodule.subset_span ⟨φ, ⟨h1, h2⟩, ⟨f, hPl hf⟩, hf, rfl⟩
  | zero =>
    have : (⟨0, hbD⟩ : PolData B M) = 0 := rfl
    rw [this, Submodule.Quotient.mk_zero]
    exact zero_mem _
  | add y z hy hz ihy ihz =>
    have hyD := pureSpan_le M B P hPl hy
    have hzD := pureSpan_le M B P hPl hz
    have : (⟨y + z, hbD⟩ : PolData B M) = ⟨y, hyD⟩ + ⟨z, hzD⟩ := rfl
    rw [this, Submodule.Quotient.mk_add]
    exact add_mem (ihy hyD) (ihz hzD)
  | smul c y hy ihy =>
    have hyD := pureSpan_le M B P hPl hy
    have : (⟨c • y, hbD⟩ : PolData B M) = c • ⟨y, hyD⟩ := rfl
    rw [this, Submodule.Quotient.mk_smul]
    exact Submodule.smul_of_tower_mem _ c (ihy hyD)

/- English proof (translation)
Use `set hN := hNm.stab`. Establish `hexD : ∀ γ ∈ Lines σ W, ∀ Φ ∈ PolData B M, ∃ Φ₁ ∈ PolData B M, ∀ x, HasDerivAt (fun t => om (1, γ (Multiplicative.ofAdd t)) Φ x) (Φ₁ x) 0` using `fun γ hγ => pureSpan_deriv M (M.Pol B.ψ B.emb) (fun t => om (1, γ (Multiplicative.ofAdd t))) hstd (fun f hf => by obtain ⟨f₁, hf₁, hact, -⟩ := hP3 γ hγ f hf; exact ⟨f₁, hf₁, hact⟩)`. Establish `hkD : ∀ k ∈ KInf σ W B.emb, ∀ Φ ∈ PolData B M, om (1, k) Φ ∈ PolData B M` using `fun k hk => pureSpan_acts M (M.Pol B.ψ B.emb) (om (1, k)) hstd (fun f hf => by obtain ⟨f₁, hf₁, hact, -⟩ := hP4 k hk f hf; exact ⟨f₁, hf₁, hact⟩)`. Establish `hPolT : GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om (M.Pol B.ψ B.emb)`. Use `⟨le_rfl, fun γ hγ f hf f₁ h => hP1 γ hγ f hf f₁ h, fun k hk f hf f₁ h => sub_mem (hP2 k hk f hf f₁ h) hf, fun γ hγ f hf f₁ h => ?_, fun k hk f hf f₁ h => ?_⟩` and prove the remaining obligations.

Take `⟨f₂, hf₂, -, hu⟩` from `hP3 γ hγ f hf`. Rewrite using `[hu f₁ h]`. Conclude with `hf₂`. Take `⟨f₂, hf₂, -, hu⟩` from `hP4 k hk f hf`. Rewrite using `[hu f₁ h]`.

Conclude with `hf₂`. Establish `dich : ∀ P' : Submodule ℂ (SInf F (Fin n × Fin d)), GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om P' → N ⊔ pureSpan M P' = N ∨ N ⊔ pureSpan M P' = PolData B M` using `fun P' hP' => hNm.max _ le_sup_left (sup_le hNm.le (pureSpan_le M B P' hP'.1)) (sup_wstable hstd hP3 hP4 P' hP' (hfin P') hNm)`. Take `⟨L, hL⟩` from `hchain`. Take `⟨Pm, ⟨hPmT, hPmS⟩, hPmin⟩` from `exists_minimal_of_chain (GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om) L hL {P' | GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om P' ∧ N ⊔ pureSpan M P' = PolData B M} (fun _ hx => hx.1) (M.Pol B.ψ B.emb) ⟨hPolT, le_antisymm (sup_le hNm.le le_rfl) le_sup_right⟩`. Establish `hatom : ∀ (φ' : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) (hφ' : Good M φ') (T : Submodule (Alg B M om) (PolData B M ⧸ Nr B M om N hN)), (∀ q, q ∈ T ↔ ∃ f : M.Pol B.ψ B.emb, f.1 ∈ Pm ∧ iota B M om N hN φ' hφ' f = q) → T = ⊥ ∨ IsAtom T`.

Introduce `φ' hφ' T hT`. Distinguish the cases in `hT0 : T = ⊥`. Conclude with `Or.inl hT0`. Use `right`. Use `⟨hT0, fun T' hT' => ?_⟩` and prove the remaining obligations.

Establish `hpreT` using `thetaSub_pre (hN := hN) hstd hP1 hP2 hNm.coinv hexD hkD hφ' Pm hPmT T'`. Use `set pre := Pm ⊓ ((T'.restrictScalars ℂ).comap (iota B M om N hN φ' hφ')).map (M.Pol B.ψ B.emb).subtype with hpre`. Establish `hpre_ne : pre ≠ Pm`. Introduce `he`. Apply `(lt_iff_le_and_ne.1 hT').2` to reduce the goal to its premises.

Use `le_antisymm hT'.le fun q hq => ?_` and prove the remaining obligations. Take `⟨f, hfPm, rfl⟩` from `(hT q).1 hq`. Establish `hf : f.1 ∈ pre` using `by rw [he]; exact hfPm`. Take `⟨hf', hfT'⟩` from `(mem_pre B M om N hN φ' hφ' T' f.1).1 hf.2`. Conclude with `hfT'`.

Establish `hlt : pre < Pm` using `lt_of_le_of_ne inf_le_left hpre_ne`. Establish `hSpre : N ⊔ pureSpan M pre = N` using `(dich pre hpreT).resolve_right fun h => hPmin pre ⟨hpreT, h⟩ hlt`. Rewrite using `[eq_bot_iff]`. Introduce `q hq`. Take `⟨f, hfPm, rfl⟩` from `(hT q).1 (hT'.le hq)`.

Establish `hfpre : f.1 ∈ pre` using `⟨hfPm, (mem_pre B M om N hN φ' hφ' T' f.1).2 ⟨f.2, hq⟩⟩`. Establish `hfN : pure f.1 φ' ∈ N`. Rewrite using `[← hSpre]`. Conclude with `Submodule.mem_sup_right (Submodule.subset_span ⟨f.1, hfpre, φ', hφ'.1, hφ'.2, rfl⟩)`. Rewrite using `[Submodule.mem_bot]`.

Conclude with `(iota_eq_zero B M om N hN φ' hφ' f).2 hfN`. Establish `hss : IsSemisimpleModule (Alg B M om) (PolData B M ⧸ Nr B M om N hN)`. Apply `IsSemisimpleModule.of_sSup_simples_eq_top` to reduce the goal to its premises. Rewrite using `[eq_top_iff]`. Introduce `q _`.

Use `(Submodule.span_le.2 ?_) (span_top (hN := hN) Pm hPmT.1 hPmS q)` and prove the remaining obligations. Introduce and unpack `_ ⟨φ', hφ', f, hfPm, rfl⟩`. Take `⟨T, hT⟩` from `exists_img (hN := hN) hstd hP3 hP4 hφ' Pm hPmT`. Establish `hmem : iota B M om N hN φ' hφ' f ∈ T` using `(hT _).2 ⟨f, hfPm, rfl⟩`. Break down `hatom φ' hφ' T hT with h0 | ha` into its components or cases.

Rewrite `hmem` using `[h0, Submodule.mem_bot]`. Rewrite using `[SetLike.mem_coe, hmem]`. Conclude with `zero_mem _`. Conclude with `Submodule.mem_sSup_of_mem (isSimpleModule_iff_isAtom.2 ha) hmem`. Assume the negation of the conclusion as `hPK`.

Take `⟨f, hfP, hfN⟩` from `SetLike.not_le_iff_exists.1 hPK`. Take `⟨TP, hTP⟩` from `exists_img (hN := hN) hstd hP3 hP4 hφ P hP`. Establish `hTP0 : TP ≠ ⊥`. Introduce `h0`. Apply `hfN` to reduce the goal to its premises.

Establish `h1` using `(hTP _).2 ⟨⟨f, hP.1 hfP⟩, hfP, rfl⟩`. Rewrite `h1` using `[h0, Submodule.mem_bot]`. Conclude with `(iota_eq_zero B M om N hN φ hφ ⟨f, hP.1 hfP⟩).1 h1`. Take `⟨C, hC⟩` from `exists_isCompl TP`. Establish `hP'T` using `thetaSub_pre (hN := hN) hstd hP1 hP2 hNm.coinv hexD hkD hφ (M.Pol B.ψ B.emb) hPolT C`.

Use `set P' := M.Pol B.ψ B.emb ⊓ ((C.restrictScalars ℂ).comap (iota B M om N hN φ hφ)).map (M.Pol B.ψ B.emb).subtype with hP'`. Establish `hP'ne : P' ≠ M.Pol B.ψ B.emb`. Introduce `he`. Apply `hTP0` to reduce the goal to its premises. Rewrite using `[eq_bot_iff]`.

Introduce `q hq`. Take `⟨g, hgP, rfl⟩` from `(hTP q).1 hq`. Establish `hg : g.1 ∈ P'` using `by rw [he]; exact g.2`. Take `⟨_, hgC⟩` from `(mem_pre B M om N hN φ hφ C g.1).1 hg.2`. Rewrite using `[Submodule.mem_bot]`.

Conclude with `Submodule.disjoint_def.1 hC.disjoint _ hq hgC`. Establish `hsup : P ⊔ P' = M.Pol B.ψ B.emb`. Use `le_antisymm (sup_le hP.1 hP'T.1) fun g hg => ?_` and prove the remaining obligations. Establish `htop : iota B M om N hN φ hφ ⟨g, hg⟩ ∈ TP ⊔ C` using `by rw [hC.sup_eq_top]; trivial`. Take `⟨a, ha, c, hc, hac⟩` from `Submodule.mem_sup.1 htop`.

Take `⟨p, hpP, rfl⟩` from `(hTP a).1 ha`. Establish `hgp : g - p.1 ∈ P'`. Use `⟨sub_mem hg p.2, (mem_pre B M om N hN φ hφ C (g - p.1)).2 ⟨sub_mem hg p.2, ?_⟩⟩` and prove the remaining obligations. Establish `e : iota B M om N hN φ hφ ⟨g - p.1, sub_mem hg p.2⟩ = iota B M om N hN φ hφ ⟨g, hg⟩ - iota B M om N hN φ hφ p`. Rewrite using `[← map_sub]`.

Both sides reduce to the same expression. Rewrite using `[e, ← hac, add_sub_cancel_left]`. Conclude with `hc`. Establish `e2 : g = p.1 + (g - p.1)` using `by abel`. Rewrite using `[e2]`.

Conclude with `Submodule.add_mem_sup hpP hgp`. Conclude with `hsum P P' hP hP'T hne hP'ne hsup`.
-/
theorem core
    (hstd : ∀ᶠ v in Filter.cofinite, M.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
    (hP1 : ∀ γ ∈ Lines σ Y, ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
      ActsD (evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) f f₁ → f₁ ∈ M.Pol B.ψ B.emb)
    (hP2 : ∀ k ∈ KInf σ Y B.emb, ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
      Acts (evI F) (om (k, 1)) f f₁ → f₁ ∈ M.Pol B.ψ B.emb)
    (hP3 : ∀ γ ∈ Lines σ W, ∀ f ∈ M.Pol B.ψ B.emb, ∃ f₁ ∈ M.Pol B.ψ B.emb,
      ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ ∧ ∀ f₂ : SInf F (Fin n × Fin d),
        ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₂ → f₂ = f₁)
    (hP4 : ∀ k ∈ KInf σ W B.emb, ∀ f ∈ M.Pol B.ψ B.emb, ∃ f₁ ∈ M.Pol B.ψ B.emb,
      Acts (evI F) (om (1, k)) f f₁ ∧ ∀ f₂ : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) f f₂ → f₂ = f₁)
    (hfin : ∀ P : Submodule ℂ (SInf F (Fin n × Fin d)), ∀ v : Pl F, ∀ h ∈ UAt σ W (evFin F v), ∀ Φ ∈ pureSpan M P,
      om (1, h) Φ ∈ pureSpan M P)
    (hchain : ∃ L : ℕ, ∀ (m : ℕ) (c : Fin m → Submodule ℂ (SInf F (Fin n × Fin d))), StrictMono c →
      (∀ i, GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om (c i)) → m ≤ L)
    (hsum : ∀ P P', GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om P → GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om P' →
      P ≠ M.Pol B.ψ B.emb → P' ≠ M.Pol B.ψ B.emb → P ⊔ P' ≠ M.Pol B.ψ B.emb)
    (hNm : GlobalTheory.ThetaFac.IsMaxTh B om (PolData B M) N)
    {φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ} (hφ : Good M φ)
    (P : Submodule ℂ (SInf F (Fin n × Fin d))) (hP : GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om P)
    (hne : P ≠ M.Pol B.ψ B.emb) : P ≤ N.comap (GlobalTheory.ThetaFacInf.pureL φ) := by
  classical
  set hN := hNm.stab
  have hexD : ∀ γ ∈ Lines σ W, ∀ Φ ∈ PolData B M, ∃ Φ₁ ∈ PolData B M,
      ∀ x, HasDerivAt (fun t => om (1, γ (Multiplicative.ofAdd t)) Φ x) (Φ₁ x) 0 := fun γ hγ =>
    pureSpan_deriv M (M.Pol B.ψ B.emb) (fun t => om (1, γ (Multiplicative.ofAdd t))) hstd
      (fun f hf => by obtain ⟨f₁, hf₁, hact, -⟩ := hP3 γ hγ f hf; exact ⟨f₁, hf₁, hact⟩)
  have hkD : ∀ k ∈ KInf σ W B.emb, ∀ Φ ∈ PolData B M, om (1, k) Φ ∈ PolData B M := fun k hk =>
    pureSpan_acts M (M.Pol B.ψ B.emb) (om (1, k)) hstd
      (fun f hf => by obtain ⟨f₁, hf₁, hact, -⟩ := hP4 k hk f hf; exact ⟨f₁, hf₁, hact⟩)
  have hPolT : GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om (M.Pol B.ψ B.emb) := by
    refine ⟨le_rfl, fun γ hγ f hf f₁ h => hP1 γ hγ f hf f₁ h,
      fun k hk f hf f₁ h => sub_mem (hP2 k hk f hf f₁ h) hf, fun γ hγ f hf f₁ h => ?_, fun k hk f hf f₁ h => ?_⟩
    · obtain ⟨f₂, hf₂, -, hu⟩ := hP3 γ hγ f hf
      rw [hu f₁ h]; exact hf₂
    · obtain ⟨f₂, hf₂, -, hu⟩ := hP4 k hk f hf
      rw [hu f₁ h]; exact hf₂
  have dich : ∀ P' : Submodule ℂ (SInf F (Fin n × Fin d)), GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om P' →
      N ⊔ pureSpan M P' = N ∨ N ⊔ pureSpan M P' = PolData B M := fun P' hP' =>
    hNm.max _ le_sup_left (sup_le hNm.le (pureSpan_le M B P' hP'.1))
      (sup_wstable hstd hP3 hP4 P' hP' (hfin P') hNm)
  obtain ⟨L, hL⟩ := hchain
  obtain ⟨Pm, ⟨hPmT, hPmS⟩, hPmin⟩ := exists_minimal_of_chain (GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om) L hL
    {P' | GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om P' ∧ N ⊔ pureSpan M P' = PolData B M} (fun _ hx => hx.1)
    (M.Pol B.ψ B.emb) ⟨hPolT, le_antisymm (sup_le hNm.le le_rfl) le_sup_right⟩

  have hatom : ∀ (φ' : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) (hφ' : Good M φ')
      (T : Submodule (Alg B M om) (PolData B M ⧸ Nr B M om N hN)),
      (∀ q, q ∈ T ↔ ∃ f : M.Pol B.ψ B.emb, f.1 ∈ Pm ∧ iota B M om N hN φ' hφ' f = q) → T = ⊥ ∨ IsAtom T := by
    intro φ' hφ' T hT
    by_cases hT0 : T = ⊥
    · exact Or.inl hT0
    right
    refine ⟨hT0, fun T' hT' => ?_⟩
    have hpreT := thetaSub_pre (hN := hN) hstd hP1 hP2 hNm.coinv hexD hkD hφ' Pm hPmT T'
    set pre := Pm ⊓ ((T'.restrictScalars ℂ).comap (iota B M om N hN φ' hφ')).map (M.Pol B.ψ B.emb).subtype
      with hpre
    have hpre_ne : pre ≠ Pm := by
      intro he
      apply (lt_iff_le_and_ne.1 hT').2
      refine le_antisymm hT'.le fun q hq => ?_
      obtain ⟨f, hfPm, rfl⟩ := (hT q).1 hq
      have hf : f.1 ∈ pre := by rw [he]; exact hfPm
      obtain ⟨hf', hfT'⟩ := (mem_pre B M om N hN φ' hφ' T' f.1).1 hf.2
      exact hfT'
    have hlt : pre < Pm := lt_of_le_of_ne inf_le_left hpre_ne
    have hSpre : N ⊔ pureSpan M pre = N :=
      (dich pre hpreT).resolve_right fun h => hPmin pre ⟨hpreT, h⟩ hlt
    rw [eq_bot_iff]
    intro q hq
    obtain ⟨f, hfPm, rfl⟩ := (hT q).1 (hT'.le hq)
    have hfpre : f.1 ∈ pre := ⟨hfPm, (mem_pre B M om N hN φ' hφ' T' f.1).2 ⟨f.2, hq⟩⟩
    have hfN : pure f.1 φ' ∈ N := by
      rw [← hSpre]
      exact Submodule.mem_sup_right (Submodule.subset_span ⟨f.1, hfpre, φ', hφ'.1, hφ'.2, rfl⟩)
    rw [Submodule.mem_bot]
    exact (iota_eq_zero B M om N hN φ' hφ' f).2 hfN

  have hss : IsSemisimpleModule (Alg B M om) (PolData B M ⧸ Nr B M om N hN) := by
    apply IsSemisimpleModule.of_sSup_simples_eq_top
    rw [eq_top_iff]
    intro q _
    refine (Submodule.span_le.2 ?_) (span_top (hN := hN) Pm hPmT.1 hPmS q)
    rintro _ ⟨φ', hφ', f, hfPm, rfl⟩
    obtain ⟨T, hT⟩ := exists_img (hN := hN) hstd hP3 hP4 hφ' Pm hPmT
    have hmem : iota B M om N hN φ' hφ' f ∈ T := (hT _).2 ⟨f, hfPm, rfl⟩
    rcases hatom φ' hφ' T hT with h0 | ha
    · rw [h0, Submodule.mem_bot] at hmem
      rw [SetLike.mem_coe, hmem]
      exact zero_mem _
    · exact Submodule.mem_sSup_of_mem (isSimpleModule_iff_isAtom.2 ha) hmem

  by_contra hPK
  obtain ⟨f, hfP, hfN⟩ := SetLike.not_le_iff_exists.1 hPK
  obtain ⟨TP, hTP⟩ := exists_img (hN := hN) hstd hP3 hP4 hφ P hP
  have hTP0 : TP ≠ ⊥ := by
    intro h0
    apply hfN
    have h1 := (hTP _).2 ⟨⟨f, hP.1 hfP⟩, hfP, rfl⟩
    rw [h0, Submodule.mem_bot] at h1
    exact (iota_eq_zero B M om N hN φ hφ ⟨f, hP.1 hfP⟩).1 h1
  obtain ⟨C, hC⟩ := exists_isCompl TP
  have hP'T := thetaSub_pre (hN := hN) hstd hP1 hP2 hNm.coinv hexD hkD hφ (M.Pol B.ψ B.emb) hPolT C
  set P' := M.Pol B.ψ B.emb ⊓ ((C.restrictScalars ℂ).comap (iota B M om N hN φ hφ)).map (M.Pol B.ψ B.emb).subtype
    with hP'
  have hP'ne : P' ≠ M.Pol B.ψ B.emb := by
    intro he
    apply hTP0
    rw [eq_bot_iff]
    intro q hq
    obtain ⟨g, hgP, rfl⟩ := (hTP q).1 hq
    have hg : g.1 ∈ P' := by rw [he]; exact g.2
    obtain ⟨_, hgC⟩ := (mem_pre B M om N hN φ hφ C g.1).1 hg.2
    rw [Submodule.mem_bot]
    exact Submodule.disjoint_def.1 hC.disjoint _ hq hgC
  have hsup : P ⊔ P' = M.Pol B.ψ B.emb := by
    refine le_antisymm (sup_le hP.1 hP'T.1) fun g hg => ?_
    have htop : iota B M om N hN φ hφ ⟨g, hg⟩ ∈ TP ⊔ C := by rw [hC.sup_eq_top]; trivial
    obtain ⟨a, ha, c, hc, hac⟩ := Submodule.mem_sup.1 htop
    obtain ⟨p, hpP, rfl⟩ := (hTP a).1 ha
    have hgp : g - p.1 ∈ P' := by
      refine ⟨sub_mem hg p.2, (mem_pre B M om N hN φ hφ C (g - p.1)).2 ⟨sub_mem hg p.2, ?_⟩⟩
      have e : iota B M om N hN φ hφ ⟨g - p.1, sub_mem hg p.2⟩ =
          iota B M om N hN φ hφ ⟨g, hg⟩ - iota B M om N hN φ hφ p := by
        rw [← map_sub]; rfl
      rw [e, ← hac, add_sub_cancel_left]
      exact hc
    have e2 : g = p.1 + (g - p.1) := by abel
    rw [e2]
    exact Submodule.add_mem_sup hpP hgp
  exact hsum P P' hP hP'T hne hP'ne hsup

end Core

end GlobalTheory.ThetaFibMax

namespace GlobalTheory.ThetaFibMax

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Matrix

/- English proof (translation)
Take `⟨rfl, A, hA⟩` from `h`. Set `A' : Matrix (Fin (r + s)) (Fin (r + s)) ℂ` to `A.submatrix id finSumFinEquiv.symm`. Establish `e : A'ᵀ * M * A'.map star = (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) _ ℂ).submatrix finSumFinEquiv.symm finSumFinEquiv.symm`. Rewrite using `[← hA]`. Both sides reduce to the same expression.

Introduce `h0`. Establish `e2` using `congrArg Matrix.det e`. Rewrite `e2` using `[Matrix.det_mul, Matrix.det_mul, h0, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg]`. Simplify using `at e2`. Conclude with `absurd e2.symm (by simp)`.
-/
theorem det_ne_zero_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨rfl, A, hA⟩ := h
  let A' : Matrix (Fin (r + s)) (Fin (r + s)) ℂ := A.submatrix id finSumFinEquiv.symm
  have e : A'ᵀ * M * A'.map star =
      (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) _ ℂ).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
    rw [← hA]; rfl
  intro h0
  have e2 := congrArg Matrix.det e
  rw [Matrix.det_mul, Matrix.det_mul, h0, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_neg] at e2
  simp at e2
  exact absurd e2.symm (by simp)

/- English proof (translation)
Take `⟨w⟩ : Nonempty (InfinitePlace F)` from `inferInstance`. Establish `hY : Y.J.det ≠ 0` using `fun h0 => det_ne_zero_of_hasSig (h.herm.sig w) (by`. Rewrite using `[← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero])`. Establish `hW : W.J.det ≠ 0` using `fun h0 => det_ne_zero_of_hasSig (h.skew.sig w) (by`. Rewrite using `[Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero, mul_zero])`.

Conclude with `hKP.howeDualityReal F E σ h.base.cm n d Y W M B.ψ χY χW o h.base.std h.herm.herm hY h.skew.skew hW h.resX h.resW h.hX h.hW h.weil B.emb h.herm.cartan h.skew.cartan`.
-/
theorem howe_pair (hKP : KP) {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {B : Base F E} {n d r s r' s' : ℕ} {Y : Spc F E n} {W : Spc F E d} {M : Model σ Y W} {χY χW : Chr F E}
    {o : Rep σ Y W} (h : IsPair B M χY χW o r s r' s') :
    (∃ L : ℕ, ∀ (m : ℕ) (c : Fin m → Submodule ℂ (SInf F (Fin n × Fin d))), StrictMono c →
      (∀ i, GlobalTheory.Published.ThetaSubInf M B.ψ B.emb o (c i)) → m ≤ L) ∧
    ∀ P P', GlobalTheory.Published.ThetaSubInf M B.ψ B.emb o P → GlobalTheory.Published.ThetaSubInf M B.ψ B.emb o P' →
      P ≠ M.Pol B.ψ B.emb → P' ≠ M.Pol B.ψ B.emb → P ⊔ P' ≠ M.Pol B.ψ B.emb := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hY : Y.J.det ≠ 0 := fun h0 => det_ne_zero_of_hasSig (h.herm.sig w) (by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero])
  have hW : W.J.det ≠ 0 := fun h0 => det_ne_zero_of_hasSig (h.skew.sig w) (by
    rw [Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero, mul_zero])
  exact hKP.howeDualityReal F E σ h.base.cm n d Y W M B.ψ χY χW o h.base.std h.herm.herm hY h.skew.skew hW h.resX h.resW
    h.hX h.hW h.weil B.emb h.herm.cartan h.skew.cartan

/- English proof (translation)
Introduce `hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM N hN φ hSB hev P hP _ hne`. Establish `hT` using `hM.triple`. Take `⟨hP1, hP2, hP3, hP4⟩` from `GlobalTheory.T.real_line_polynomial_equivariance hKP F E σ B a a' G X om om' hT`. Establish `hV : IsPair B G.M X.β (X.β / X.α) om (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q)` using `{ base := hT.base, herm := hT.geo.hV, skew := hT.geo.hW, good := hT.geo.hM, hX := hT.chars.heckeβ, hW := GlobalTheory.ThKRatInv.isHecke_div hT.chars.heckeβ hT.chars.heckeα, resX := hT.chars.resβ, resW := GlobalTheory.ThKRatInv.resEtaPow_div hT.chars.resβ hT.chars.resα, weil := hT …`. Take `⟨hchain, hsum⟩` from `howe_pair hKP hV`.

Conclude with `core hT.geo.hM.std hP1 hP2 hP3 hP4 (fun P' v h hh => pureSpan_fin (GlobalTheory.T.theta_action_exists hKP.base) B G.M hV P' v h hh) hchain hsum hN ⟨hSB, hev⟩ P hP hne`.
-/
theorem fibMax : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ N, GlobalTheory.ThetaFac.IsMaxTh B om (GlobalTheory.ThK.PolData B G.M) N → ∀ (φ : ∀ v : Pl F, (Fin a × Fin (a + a') → Fv F v) → ℂ), (∀ v, φ v ∈ SB _) → (∀ᶠ v in Filter.cofinite, φ v = G.M.vac v) → ∀ P : Submodule ℂ (SInf F (Fin a × Fin (a + a'))), GlobalTheory.Published.ThetaSubInf G.M B.ψ B.emb om P → G.M.Pol B.ψ B.emb ⊓ N.comap (GlobalTheory.ThetaFacInf.pureL φ) ≤ P → P ≠ G.M.Pol B.ψ B.emb → P ≤ N.comap (GlobalTheory.ThetaFacInf.pureL φ) := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM N hN φ hSB hev P hP _ hne
  have hT := hM.triple
  obtain ⟨hP1, hP2, hP3, hP4⟩ := GlobalTheory.T.real_line_polynomial_equivariance hKP F E σ B a a' G X om om' hT
  have hV : IsPair B G.M X.β (X.β / X.α) om (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) :=
    { base := hT.base, herm := hT.geo.hV, skew := hT.geo.hW, good := hT.geo.hM, hX := hT.chars.heckeβ,
      hW := GlobalTheory.ThKRatInv.isHecke_div hT.chars.heckeβ hT.chars.heckeα, resX := hT.chars.resβ,
      resW := GlobalTheory.ThKRatInv.resEtaPow_div hT.chars.resβ hT.chars.resα, weil := hT.weil }
  obtain ⟨hchain, hsum⟩ := howe_pair hKP hV
  exact core hT.geo.hM.std hP1 hP2 hP3 hP4
    (fun P' v h hh => pureSpan_fin (GlobalTheory.T.theta_action_exists hKP.base) B G.M hV P' v h hh) hchain hsum hN ⟨hSB, hev⟩ P hP hne

end GlobalTheory.ThetaFibMax

end
