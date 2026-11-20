import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm

namespace GlobalTheory.ProductForm

variable {ι Pr Pi κ : Type} [AddCommGroup Pr] [Module ℂ Pr] [AddCommGroup Pi] [Module ℂ Pi]

/- English proof (translation)
Establish `: (Finsupp.lsum ℂ b) ∘ₗ (Finsupp.mapRange.linearMap (ρ i)) = σ i ∘ₗ Finsupp.lsum ℂ b`. Use `Finsupp.lhom_ext fun k x => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single, Finsupp.lsum_single]`. Conclude with `LinearMap.congr_fun (hb k i) x`. Conclude with `LinearMap.congr_fun this d`.
-/
theorem lsum_mapRange (ρ : ι → Module.End ℂ Pr) (σ : ι → Module.End ℂ Pi)
    (b : κ → Pr →ₗ[ℂ] Pi) (hb : ∀ k i, b k ∘ₗ ρ i = σ i ∘ₗ b k) (i : ι) (d : κ →₀ Pr) :
    Finsupp.lsum ℂ b (Finsupp.mapRange (ρ i) (map_zero _) d) = σ i (Finsupp.lsum ℂ b d) := by
  have : (Finsupp.lsum ℂ b) ∘ₗ (Finsupp.mapRange.linearMap (ρ i)) = σ i ∘ₗ Finsupp.lsum ℂ b := by
    refine Finsupp.lhom_ext fun k x => ?_
    simp only [LinearMap.comp_apply, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single,
      Finsupp.lsum_single]
    exact LinearMap.congr_fun (hb k i) x
  exact LinearMap.congr_fun this d

/- English proof (translation)
It suffices to establish `h : ∀ n, ∀ c : κ →₀ Pr, c.support.card = n → Finsupp.lsum ℂ b c = 0 → c = 0 from fun c hc => h _ c rfl hc`. Introduce `n`. Use `Nat.strong_induction_on n ?_` and prove the remaining obligations. Introduce `n ih c hcard hc`. Assume the negation of the conclusion as `hne`.

Take `⟨k₀, hk₀⟩ : ∃ k, k ∈ c.support` from `Finsupp.support_nonempty_iff.mpr hne`. Use `set s := c.support with hs`. Set `R : Submodule ℂ (κ →₀ Pr)` to `Finsupp.supported Pr ℂ (↑s : Set κ) ⊓ LinearMap.ker (Finsupp.lsum ℂ b)`. Establish `memR : ∀ d, d ∈ R ↔ d.support ⊆ s ∧ Finsupp.lsum ℂ b d = 0`. Introduce `d`.

Simplify using `[R, Finsupp.mem_supported]`. Establish `inj : ∀ d ∈ R, d k₀ = 0 → d = 0`. Introduce `d hd h0`. Rewrite `hd` using `[memR]`. Establish `hsub : d.support ⊆ s.erase k₀`.

Introduce `k hk`. Use `Finset.mem_erase.mpr ⟨?_, hd.1 hk⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Conclude with `(Finsupp.mem_support_iff.mp hk) h0`. Establish `hlt : d.support.card < n`.

Rewrite using `[← hcard]`. Conclude with `lt_of_le_of_lt (Finset.card_le_card hsub) (Finset.card_erase_lt_of_mem hk₀)`. Conclude with `ih _ hlt d rfl hd.2`. Set `π : R →ₗ[ℂ] Pr` to `(Finsupp.lapply k₀) ∘ₗ R.subtype`. Establish `πinj : Function.Injective π`.

Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `d hd`. Conclude with `Subtype.ext (inj d.1 d.2 hd)`. Establish `mapR : ∀ i, ∀ d ∈ R, Finsupp.mapRange (ρ i) (map_zero _) d ∈ R`. Introduce `i d hd`.

Rewrite `hd`, the goal using `[memR]`. Use `⟨fun k hk => hd.1 (Finsupp.support_mapRange hk), ?_⟩` and prove the remaining obligations. Rewrite using `[lsum_mapRange ρ σ b hb, hd.2, map_zero]`. Establish `hcR : c ∈ R` using `(memR c).mpr ⟨subset_refl _, hc⟩`. Establish `hx0 : c k₀ ≠ 0` using `Finsupp.mem_support_iff.mp hk₀`.

Establish `πsurj : Function.Surjective π`. Establish `hinv : ∀ i, ∀ x ∈ LinearMap.range π, ρ i x ∈ LinearMap.range π`. Introduce and unpack `i x ⟨d, rfl⟩`. Conclude with `⟨⟨_, mapR i d.1 d.2⟩, by simp [π]⟩`. Break down `hirr _ hinv with h | h` into its components or cases.

It suffices to derive a contradiction. Establish `: π ⟨c, hcR⟩ ∈ LinearMap.range π` using `⟨_, rfl⟩`. Rewrite `this` using `[h, Submodule.mem_bot]`. Conclude with `hx0 this`. Conclude with `LinearMap.range_eq_top.mp h`.

Set `E` to `LinearEquiv.ofBijective π ⟨πinj, πsurj⟩`. Set `T : κ → Module.End ℂ Pr` to `fun k => (Finsupp.lapply k) ∘ₗ R.subtype ∘ₗ E.symm.toLinearMap`. Establish `hE : ∀ x, ((E.symm x : R) : κ →₀ Pr) k₀ = x` using `fun x => by`. Use `E.apply_symm_apply x` as an intermediate fact. Conclude with `this`.

Establish `hT : ∀ k, ∀ i, T k * ρ i = ρ i * T k`. Introduce `k i`. Use extensionality with `x`. Establish `key : E.symm (ρ i x) = ⟨_, mapR i _ (E.symm x).2⟩`. Rewrite using `[LinearEquiv.symm_apply_eq]`.

Express the relevant statement in the definitionally equal form `ρ i x = (Finsupp.mapRange (ρ i) (map_zero _) ((E.symm x : R) : κ →₀ Pr)) k₀`. Rewrite using `[Finsupp.mapRange_apply, hE]`. Simplify using `[T, key]`. Use `choose a ha using fun k => hschur (T k) (hT k)`. Establish `ha0 : a k₀ = 1`.

Establish `h1 : T k₀ (c k₀) = c k₀` using `hE _`. Rewrite `h1` using `[ha k₀]`. Establish `h2 : a k₀ • c k₀ = c k₀` using `by simpa using h1`. Establish `: (a k₀ - 1) • c k₀ = 0` using `by rw [sub_smul, one_smul, h2, sub_self]`. Break down `smul_eq_zero.mp this with h | h` into its components or cases.

Conclude with `sub_eq_zero.mp h`. Conclude with `absurd h hx0`. Establish `hrel : ∑ k ∈ s, a k • b k = 0`. Use extensionality with `x`. Establish `hd` using `(memR _).mp (E.symm x).2`.

Establish `hsum` using `hd.2`. Rewrite `hsum` using `[Finsupp.lsum_apply, Finsupp.sum_of_support_subset _ hd.1 _ (fun k _ => map_zero _)]`. Establish `hTx : ∀ k, ((E.symm x : R) : κ →₀ Pr) k = a k • x` using `fun k => by`. Use `LinearMap.congr_fun (ha k) x` as an intermediate fact. Simplify `this` using `[T]`.

Simplify using `only [hTx, map_smul] at hsum`. Simplify `hsum` using `[LinearMap.sum_apply]`. Use `linearIndependent_iff'.mp hli s a hrel k₀ hk₀` as an intermediate fact. Rewrite `this` using `[ha0]`. Conclude with `one_ne_zero this`.
-/
theorem eval_injective (ρ : ι → Module.End ℂ Pr) (σ : ι → Module.End ℂ Pi)
    (hirr : ∀ N : Submodule ℂ Pr, (∀ i, ∀ x ∈ N, ρ i x ∈ N) → N = ⊥ ∨ N = ⊤)
    (hschur : ∀ T : Module.End ℂ Pr, (∀ i, T * ρ i = ρ i * T) → ∃ c : ℂ, T = c • 1)
    (b : κ → Pr →ₗ[ℂ] Pi) (hli : LinearIndependent ℂ b) (hb : ∀ k i, b k ∘ₗ ρ i = σ i ∘ₗ b k) :
    ∀ c : κ →₀ Pr, Finsupp.lsum ℂ b c = 0 → c = 0 := by
  classical
  suffices h : ∀ n, ∀ c : κ →₀ Pr, c.support.card = n → Finsupp.lsum ℂ b c = 0 → c = 0 from
    fun c hc => h _ c rfl hc
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih c hcard hc
  by_contra hne
  obtain ⟨k₀, hk₀⟩ : ∃ k, k ∈ c.support := Finsupp.support_nonempty_iff.mpr hne
  set s := c.support with hs
  let R : Submodule ℂ (κ →₀ Pr) :=
    Finsupp.supported Pr ℂ (↑s : Set κ) ⊓ LinearMap.ker (Finsupp.lsum ℂ b)
  have memR : ∀ d, d ∈ R ↔ d.support ⊆ s ∧ Finsupp.lsum ℂ b d = 0 := by
    intro d; simp [R, Finsupp.mem_supported]
  have inj : ∀ d ∈ R, d k₀ = 0 → d = 0 := by
    intro d hd h0
    rw [memR] at hd
    have hsub : d.support ⊆ s.erase k₀ := by
      intro k hk
      refine Finset.mem_erase.mpr ⟨?_, hd.1 hk⟩
      rintro rfl; exact (Finsupp.mem_support_iff.mp hk) h0
    have hlt : d.support.card < n := by
      rw [← hcard]
      exact lt_of_le_of_lt (Finset.card_le_card hsub) (Finset.card_erase_lt_of_mem hk₀)
    exact ih _ hlt d rfl hd.2
  let π : R →ₗ[ℂ] Pr := (Finsupp.lapply k₀) ∘ₗ R.subtype
  have πinj : Function.Injective π := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro d hd
    exact Subtype.ext (inj d.1 d.2 hd)
  have mapR : ∀ i, ∀ d ∈ R, Finsupp.mapRange (ρ i) (map_zero _) d ∈ R := by
    intro i d hd
    rw [memR] at hd ⊢
    refine ⟨fun k hk => hd.1 (Finsupp.support_mapRange hk), ?_⟩
    rw [lsum_mapRange ρ σ b hb, hd.2, map_zero]
  have hcR : c ∈ R := (memR c).mpr ⟨subset_refl _, hc⟩
  have hx0 : c k₀ ≠ 0 := Finsupp.mem_support_iff.mp hk₀
  have πsurj : Function.Surjective π := by
    have hinv : ∀ i, ∀ x ∈ LinearMap.range π, ρ i x ∈ LinearMap.range π := by
      rintro i x ⟨d, rfl⟩
      exact ⟨⟨_, mapR i d.1 d.2⟩, by simp [π]⟩
    rcases hirr _ hinv with h | h
    · exfalso
      have : π ⟨c, hcR⟩ ∈ LinearMap.range π := ⟨_, rfl⟩
      rw [h, Submodule.mem_bot] at this
      exact hx0 this
    · exact LinearMap.range_eq_top.mp h
  let E := LinearEquiv.ofBijective π ⟨πinj, πsurj⟩
  let T : κ → Module.End ℂ Pr := fun k => (Finsupp.lapply k) ∘ₗ R.subtype ∘ₗ E.symm.toLinearMap
  have hE : ∀ x, ((E.symm x : R) : κ →₀ Pr) k₀ = x := fun x => by
    have := E.apply_symm_apply x
    exact this
  have hT : ∀ k, ∀ i, T k * ρ i = ρ i * T k := by
    intro k i
    ext x
    have key : E.symm (ρ i x) = ⟨_, mapR i _ (E.symm x).2⟩ := by
      rw [LinearEquiv.symm_apply_eq]
      change ρ i x = (Finsupp.mapRange (ρ i) (map_zero _) ((E.symm x : R) : κ →₀ Pr)) k₀
      rw [Finsupp.mapRange_apply, hE]
    simp [T, key]
  choose a ha using fun k => hschur (T k) (hT k)
  have ha0 : a k₀ = 1 := by
    have h1 : T k₀ (c k₀) = c k₀ := hE _
    rw [ha k₀] at h1
    have h2 : a k₀ • c k₀ = c k₀ := by simpa using h1
    have : (a k₀ - 1) • c k₀ = 0 := by rw [sub_smul, one_smul, h2, sub_self]
    rcases smul_eq_zero.mp this with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hx0
  have hrel : ∑ k ∈ s, a k • b k = 0 := by
    ext x
    have hd := (memR _).mp (E.symm x).2
    have hsum := hd.2
    rw [Finsupp.lsum_apply, Finsupp.sum_of_support_subset _ hd.1 _ (fun k _ => map_zero _)] at hsum
    have hTx : ∀ k, ((E.symm x : R) : κ →₀ Pr) k = a k • x := fun k => by
      have := LinearMap.congr_fun (ha k) x
      simpa [T] using this
    simp only [hTx, map_smul] at hsum
    simpa [LinearMap.sum_apply] using hsum
  have := linearIndependent_iff'.mp hli s a hrel k₀ hk₀
  rw [ha0] at this
  exact one_ne_zero this

end GlobalTheory.ProductForm

namespace GlobalTheory.ProductForm

variable {ι Pr Pi κ : Type} [AddCommGroup Pr] [Module ℂ Pr] [AddCommGroup Pi] [Module ℂ Pi]
variable {Q V : Type} [AddCommGroup Q] [Module ℂ Q] [AddCommGroup V] [Module ℂ V]

def factorSpace (ρ : ι → Module.End ℂ Pr) (σ : ι → Module.End ℂ Pi) (q : Q →ₗ[ℂ] Pr)
    (β : V →ₗ[ℂ] Q →ₗ[ℂ] Pi) (S : Submodule ℂ V) : Submodule ℂ (Pr →ₗ[ℂ] Pi) where
  carrier := {φ | ∃ f ∈ S, (∀ i, φ ∘ₗ ρ i = σ i ∘ₗ φ) ∧ β f = φ ∘ₗ q}
  zero_mem' := ⟨0, S.zero_mem, fun i => by simp, by simp⟩
  add_mem' := by
    rintro φ ψ ⟨f, hf, hφ, hβ⟩ ⟨g, hg, hψ, hβ'⟩
    refine ⟨f + g, S.add_mem hf hg, fun i => ?_, ?_⟩
    · rw [LinearMap.add_comp, LinearMap.comp_add, hφ, hψ]
    · rw [map_add, hβ, hβ', LinearMap.add_comp]
  smul_mem' := by
    rintro a φ ⟨f, hf, hφ, hβ⟩
    refine ⟨a • f, S.smul_mem a hf, fun i => ?_, ?_⟩
    · rw [LinearMap.smul_comp, LinearMap.comp_smul, hφ]
    · rw [map_smul, hβ, LinearMap.smul_comp]

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_factorSpace {ρ : ι → Module.End ℂ Pr} {σ : ι → Module.End ℂ Pi} {q : Q →ₗ[ℂ] Pr}
    {β : V →ₗ[ℂ] Q →ₗ[ℂ] Pi} {S : Submodule ℂ V} {φ : Pr →ₗ[ℂ] Pi} :
    φ ∈ factorSpace ρ σ q β S ↔ ∃ f ∈ S, (∀ i, φ ∘ₗ ρ i = σ i ∘ₗ φ) ∧ β f = φ ∘ₗ q := Iff.rfl

/- English proof (translation)
Use extensionality with `x`. Take `⟨y, rfl⟩` from `hq x`. Conclude with `LinearMap.congr_fun h y`.
-/
theorem comp_cancel {q : Q →ₗ[ℂ] Pr} (hq : Function.Surjective q) {φ ψ : Pr →ₗ[ℂ] Pi}
    (h : φ ∘ₗ q = ψ ∘ₗ q) : φ = ψ := by
  ext x
  obtain ⟨y, rfl⟩ := hq x
  exact LinearMap.congr_fun h y

def ev (F : Submodule ℂ (Pr →ₗ[ℂ] Pi)) : Pr ⊗[ℂ] F →ₗ[ℂ] Pi :=
  TensorProduct.lift (LinearMap.mk₂ ℂ (fun x (φ : F) => (φ : Pr →ₗ[ℂ] Pi) x)
    (fun _ _ _ => by simp) (fun _ _ _ => by simp) (fun _ _ _ => by simp) (fun _ _ _ => by simp))

/- English proof (translation)
Simplify using `[ev]`.
-/
@[simp] theorem ev_tmul (F : Submodule ℂ (Pr →ₗ[ℂ] Pi)) (x : Pr) (φ : F) :
    ev F (x ⊗ₜ φ) = (φ : Pr →ₗ[ℂ] Pi) x := by
  simp [ev]

/- English proof (translation)
Use `Finsupp.lhom_ext fun k x => ?_` and prove the remaining obligations. Simplify using `[TensorProduct.equivFinsuppOfBasisRight_symm_apply]`.
-/
theorem ev_comp_symm (F : Submodule ℂ (Pr →ₗ[ℂ] Pi)) [DecidableEq κ] (b : Module.Basis κ ℂ F) :
    ev F ∘ₗ (TensorProduct.equivFinsuppOfBasisRight (M := Pr) b).symm.toLinearMap =
      Finsupp.lsum ℂ (fun k => ((b k : F) : Pr →ₗ[ℂ] Pi)) := by
  refine Finsupp.lhom_ext fun k x => ?_
  simp [TensorProduct.equivFinsuppOfBasisRight_symm_apply]

/- English proof (translation)
Rewrite using `[← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]`. Introduce and unpack `y ⟨f, hf, P, rfl⟩`. Take `⟨φ, h1, h2⟩` from `hS f hf`. Use `⟨q P ⊗ₜ ⟨φ, hF ⟨f, hf, h1, h2⟩⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[ev_tmul]`.

Conclude with `(LinearMap.congr_fun h2 P).symm`.
-/
theorem ev_surjective (ρ : ι → Module.End ℂ Pr) (σ : ι → Module.End ℂ Pi) (q : Q →ₗ[ℂ] Pr)
    (β : V →ₗ[ℂ] Q →ₗ[ℂ] Pi) (S : Submodule ℂ V) (F : Submodule ℂ (Pr →ₗ[ℂ] Pi))
    (hF : factorSpace ρ σ q β S ≤ F)
    (hS : ∀ f ∈ S, ∃ φ : Pr →ₗ[ℂ] Pi, (∀ i, φ ∘ₗ ρ i = σ i ∘ₗ φ) ∧ β f = φ ∘ₗ q)
    (hspan : Submodule.span ℂ {y | ∃ f ∈ S, ∃ P, y = β f P} = ⊤) :
    Function.Surjective (ev F) := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]
  rintro y ⟨f, hf, P, rfl⟩
  obtain ⟨φ, h1, h2⟩ := hS f hf
  refine ⟨q P ⊗ₜ ⟨φ, hF ⟨f, hf, h1, h2⟩⟩, ?_⟩
  rw [ev_tmul]
  exact (LinearMap.congr_fun h2 P).symm

/- English proof (translation)
Set `b` to `Module.Basis.ofVectorSpace ℂ F`. Set `E` to `TensorProduct.equivFinsuppOfBasisRight (M := Pr) b`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `t ht`. Establish `hli : LinearIndependent ℂ (fun k => ((b k : F) : Pr →ₗ[ℂ] Pi))` using `b.linearIndependent.map' F.subtype F.ker_subtype`.

Establish `h0 : Finsupp.lsum ℂ (fun k => ((b k : F) : Pr →ₗ[ℂ] Pi)) (E t) = 0`. Rewrite using `[← ev_comp_symm F b, LinearMap.comp_apply, LinearEquiv.coe_coe, E.symm_apply_apply, ht]`. Use `eval_injective ρ σ hirr hschur _ hli (fun k i => hF _ (b k).2 i) (E t) h0` as an intermediate fact. Simplify using `using congrArg E.symm this`.
-/
theorem ev_injective (ρ : ι → Module.End ℂ Pr) (σ : ι → Module.End ℂ Pi)
    (hirr : ∀ N : Submodule ℂ Pr, (∀ i, ∀ x ∈ N, ρ i x ∈ N) → N = ⊥ ∨ N = ⊤)
    (hschur : ∀ T : Module.End ℂ Pr, (∀ i, T * ρ i = ρ i * T) → ∃ c : ℂ, T = c • 1)
    (F : Submodule ℂ (Pr →ₗ[ℂ] Pi)) (hF : ∀ φ ∈ F, ∀ i, φ ∘ₗ ρ i = σ i ∘ₗ φ) :
    Function.Injective (ev F) := by
  classical
  let b := Module.Basis.ofVectorSpace ℂ F
  let E := TensorProduct.equivFinsuppOfBasisRight (M := Pr) b
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro t ht
  have hli : LinearIndependent ℂ (fun k => ((b k : F) : Pr →ₗ[ℂ] Pi)) :=
    b.linearIndependent.map' F.subtype F.ker_subtype
  have h0 : Finsupp.lsum ℂ (fun k => ((b k : F) : Pr →ₗ[ℂ] Pi)) (E t) = 0 := by
    rw [← ev_comp_symm F b, LinearMap.comp_apply, LinearEquiv.coe_coe, E.symm_apply_apply, ht]
  have := eval_injective ρ σ hirr hschur _ hli (fun k i => hF _ (b k).2 i) (E t) h0
  simpa using congrArg E.symm this

end GlobalTheory.ProductForm

namespace GlobalTheory.ProductForm

variable {ι Pr Pi κ : Type} [AddCommGroup Pr] [Module ℂ Pr] [AddCommGroup Pi] [Module ℂ Pi]
variable {Q V Q' V' : Type} [AddCommGroup Q] [Module ℂ Q] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup Q'] [Module ℂ Q'] [AddCommGroup V'] [Module ℂ V']

/- English proof (translation)
Establish `: Finsupp.lsum ℂ v ∘ₗ Finsupp.lmapDomain Pr ℂ some = Finsupp.lsum ℂ (fun k => v (some k))` using `Finsupp.lhom_ext fun k x => by simp`. Conclude with `LinearMap.congr_fun this c`.
-/
theorem lsum_mapDomain_some (v : Option κ → Pr →ₗ[ℂ] Pi) (c : κ →₀ Pr) :
    Finsupp.lsum ℂ v (c.mapDomain some) = Finsupp.lsum ℂ (fun k => v (some k)) c := by
  have : Finsupp.lsum ℂ v ∘ₗ Finsupp.lmapDomain Pr ℂ some = Finsupp.lsum ℂ (fun k => v (some k)) :=
    Finsupp.lhom_ext fun k x => by simp
  exact LinearMap.congr_fun this c

/- English proof (translation)
Introduce `φ hφ`. Assume the negation of the conclusion as `hφ'`. Use `set F' := factorSpace ρ σ q' β' S'`. Set `b` to `Module.Basis.ofVectorSpace ℂ F'`. Set `b' : _ → Pr →ₗ[ℂ] Pi` to `fun k => ((b k : F') : Pr →ₗ[ℂ] Pi)`.

Choose the witnesses or unpack the hypotheses as in `⟨x, hx⟩ : ∃ x, φ x ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hφ' (by rw [show φ = 0 from LinearMap.ext h]; exact F'.zero_mem)`. Take `⟨t, ht⟩` from `ev_surjective ρ σ q' β' S' F' le_rfl hS' hspan' (φ x)`.

Set `E` to `TensorProduct.equivFinsuppOfBasisRight (M := Pr) b`. Establish `hc' : Finsupp.lsum ℂ b' (E t) = φ x`. Rewrite using `[← ev_comp_symm F' b, LinearMap.comp_apply, LinearEquiv.coe_coe, E.symm_apply_apply, ht]`. Set `v : Option _ → Pr →ₗ[ℂ] Pi` to `fun o => o.elim φ b'`. Establish `hspanb : Submodule.span ℂ (Set.range b') = F'`.

Establish `: b' = F'.subtype ∘ b` using `rfl`. Rewrite using `[this, Set.range_comp, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]`. Establish `hli : LinearIndependent ℂ v`. Rewrite using `[linearIndependent_option]`. Use `⟨b.linearIndependent.map' F'.subtype F'.ker_subtype, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `φ ∉ Submodule.span ℂ (Set.range b')`. Rewrite using `[hspanb]`. Conclude with `hφ'`. Establish `hv : ∀ o i, v o ∘ₗ ρ i = σ i ∘ₗ v o`. Introduce and unpack `(_ | k) i`.

Take `⟨f, -, h1, -⟩` from `hφ`. Conclude with `h1 i`. Take `⟨f, -, h1, -⟩` from `(mem_factorSpace.mp (b k).2)`. Conclude with `h1 i`. Establish `hrel : Finsupp.lsum ℂ v (Finsupp.single none x - (E t).mapDomain some) = 0`.

Rewrite using `[map_sub, Finsupp.lsum_single, lsum_mapDomain_some]`. Express the relevant statement in the definitionally equal form `φ x - Finsupp.lsum ℂ b' (E t) = 0`. Rewrite using `[hc', sub_self]`. Establish `h0` using `congrArg (fun c : Option _ →₀ Pr => c none) (eval_injective ρ σ hirr hschur v hli hv _ hrel)`. Simplify using `only [Finsupp.coe_sub, _root_.Pi.sub_apply, Finsupp.single_eq_same, Finsupp.coe_zero, _root_.Pi.zero_apply] at h0`.

Rewrite `h0` using `[Finsupp.mapDomain_notin_range _ _ (by simp), sub_zero]`. Conclude with `hx (by rw [h0, map_zero])`.
-/
theorem factorSpace_le (ρ : ι → Module.End ℂ Pr) (σ : ι → Module.End ℂ Pi)
    (hirr : ∀ N : Submodule ℂ Pr, (∀ i, ∀ x ∈ N, ρ i x ∈ N) → N = ⊥ ∨ N = ⊤)
    (hschur : ∀ T : Module.End ℂ Pr, (∀ i, T * ρ i = ρ i * T) → ∃ c : ℂ, T = c • 1)
    (q : Q →ₗ[ℂ] Pr) (β : V →ₗ[ℂ] Q →ₗ[ℂ] Pi) (S : Submodule ℂ V)
    (q' : Q' →ₗ[ℂ] Pr) (β' : V' →ₗ[ℂ] Q' →ₗ[ℂ] Pi) (S' : Submodule ℂ V')
    (hS' : ∀ f ∈ S', ∃ φ : Pr →ₗ[ℂ] Pi, (∀ i, φ ∘ₗ ρ i = σ i ∘ₗ φ) ∧ β' f = φ ∘ₗ q')
    (hspan' : Submodule.span ℂ {y | ∃ f ∈ S', ∃ P, y = β' f P} = ⊤) :
    factorSpace ρ σ q β S ≤ factorSpace ρ σ q' β' S' := by
  classical
  intro φ hφ
  by_contra hφ'
  set F' := factorSpace ρ σ q' β' S'
  let b := Module.Basis.ofVectorSpace ℂ F'
  let b' : _ → Pr →ₗ[ℂ] Pi := fun k => ((b k : F') : Pr →ₗ[ℂ] Pi)
  obtain ⟨x, hx⟩ : ∃ x, φ x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hφ' (by rw [show φ = 0 from LinearMap.ext h]; exact F'.zero_mem)
  obtain ⟨t, ht⟩ := ev_surjective ρ σ q' β' S' F' le_rfl hS' hspan' (φ x)
  let E := TensorProduct.equivFinsuppOfBasisRight (M := Pr) b
  have hc' : Finsupp.lsum ℂ b' (E t) = φ x := by
    rw [← ev_comp_symm F' b, LinearMap.comp_apply, LinearEquiv.coe_coe, E.symm_apply_apply, ht]
  let v : Option _ → Pr →ₗ[ℂ] Pi := fun o => o.elim φ b'
  have hspanb : Submodule.span ℂ (Set.range b') = F' := by
    have : b' = F'.subtype ∘ b := rfl
    rw [this, Set.range_comp, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]
  have hli : LinearIndependent ℂ v := by
    rw [linearIndependent_option]
    refine ⟨b.linearIndependent.map' F'.subtype F'.ker_subtype, ?_⟩
    change φ ∉ Submodule.span ℂ (Set.range b')
    rw [hspanb]
    exact hφ'
  have hv : ∀ o i, v o ∘ₗ ρ i = σ i ∘ₗ v o := by
    rintro (_ | k) i
    · obtain ⟨f, -, h1, -⟩ := hφ
      exact h1 i
    · obtain ⟨f, -, h1, -⟩ := (mem_factorSpace.mp (b k).2)
      exact h1 i
  have hrel : Finsupp.lsum ℂ v (Finsupp.single none x - (E t).mapDomain some) = 0 := by
    rw [map_sub, Finsupp.lsum_single, lsum_mapDomain_some]
    change φ x - Finsupp.lsum ℂ b' (E t) = 0
    rw [hc', sub_self]
  have h0 := congrArg (fun c : Option _ →₀ Pr => c none)
    (eval_injective ρ σ hirr hschur v hli hv _ hrel)
  simp only [Finsupp.coe_sub, _root_.Pi.sub_apply, Finsupp.single_eq_same, Finsupp.coe_zero,
    _root_.Pi.zero_apply] at h0
  rw [Finsupp.mapDomain_notin_range _ _ (by simp), sub_zero] at h0
  exact hx (by rw [h0, map_zero])

/- English proof (translation)
Establish `hmem : ∀ f : S, ∃ φ ∈ factorSpace ρ σ q β S, β f = φ ∘ₗ q` using `fun f =>`. Set `⟨φ, h1, h2⟩` to `hS f f.2`. Use the proof step `⟨φ, ⟨f, f.2, h1, h2⟩, h2⟩`. Use `choose g hg hgβ using hmem`. Set `r₀ : S →ₗ[ℂ] F` to `{ toFun := fun f => ⟨g f, hF (hg f)⟩ map_add' := fun f f' => by ext1`.

Express the relevant statement in the definitionally equal form `g (f + f') = g f + g f'`. Apply `comp_cancel hq` to reduce the goal to its premises. Rewrite using `[LinearMap.add_comp, ← hgβ, ← hgβ, ← hgβ, Submodule.coe_add, map_add]`. Use the proof step `map_smul' := fun a f => by ext1`. Express the relevant statement in the definitionally equal form `g (a • f) = a • g f`.

Apply `comp_cancel hq` to reduce the goal to its premises. Rewrite using `[LinearMap.smul_comp, ← hgβ, ← hgβ, Submodule.coe_smul, map_smul] }`. Take `⟨r, hr⟩` from `LinearMap.exists_extend r₀`. Use `⟨r, fun f hf => ?_⟩` and prove the remaining obligations. Establish `: r f = r₀ ⟨f, hf⟩` using `LinearMap.congr_fun hr ⟨f, hf⟩`.

Rewrite using `[this]`. Conclude with `(hgβ ⟨f, hf⟩).symm`.
-/
theorem exists_lift (ρ : ι → Module.End ℂ Pr) (σ : ι → Module.End ℂ Pi) (q : Q →ₗ[ℂ] Pr)
    (hq : Function.Surjective q) (β : V →ₗ[ℂ] Q →ₗ[ℂ] Pi) (S : Submodule ℂ V)
    (F : Submodule ℂ (Pr →ₗ[ℂ] Pi)) (hF : factorSpace ρ σ q β S ≤ F)
    (hS : ∀ f ∈ S, ∃ φ : Pr →ₗ[ℂ] Pi, (∀ i, φ ∘ₗ ρ i = σ i ∘ₗ φ) ∧ β f = φ ∘ₗ q) :
    ∃ r : V →ₗ[ℂ] F, ∀ f ∈ S, ((r f : F) : Pr →ₗ[ℂ] Pi) ∘ₗ q = β f := by
  classical
  have hmem : ∀ f : S, ∃ φ ∈ factorSpace ρ σ q β S, β f = φ ∘ₗ q := fun f =>
    let ⟨φ, h1, h2⟩ := hS f f.2
    ⟨φ, ⟨f, f.2, h1, h2⟩, h2⟩
  choose g hg hgβ using hmem
  let r₀ : S →ₗ[ℂ] F :=
    { toFun := fun f => ⟨g f, hF (hg f)⟩
      map_add' := fun f f' => by
        ext1
        change g (f + f') = g f + g f'
        apply comp_cancel hq
        rw [LinearMap.add_comp, ← hgβ, ← hgβ, ← hgβ, Submodule.coe_add, map_add]
      map_smul' := fun a f => by
        ext1
        change g (a • f) = a • g f
        apply comp_cancel hq
        rw [LinearMap.smul_comp, ← hgβ, ← hgβ, Submodule.coe_smul, map_smul] }
  obtain ⟨r, hr⟩ := LinearMap.exists_extend r₀
  refine ⟨r, fun f hf => ?_⟩
  have : r f = r₀ ⟨f, hf⟩ := LinearMap.congr_fun hr ⟨f, hf⟩
  rw [this]
  exact (hgβ ⟨f, hf⟩).symm

end GlobalTheory.ProductForm

/- English proof (translation)
Introduce `ι Pr Pi Q Q' V V' _ _ _ _ _ _ _ _ _ _ _ _ ρ σ q q' β β' S S' hq hq' hirr hschur hS hS' hspan hspan'`. Set `F` to `GlobalTheory.ProductForm.factorSpace ρ σ q β S`. Establish `hle : GlobalTheory.ProductForm.factorSpace ρ σ q' β' S' ≤ F` using `GlobalTheory.ProductForm.factorSpace_le ρ σ hirr hschur q' β' S' q β S hS hspan`. Establish `hge : F ≤ GlobalTheory.ProductForm.factorSpace ρ σ q' β' S'` using `GlobalTheory.ProductForm.factorSpace_le ρ σ hirr hschur q β S q' β' S' hS' hspan'`. Establish `hFeq : ∀ φ ∈ F, ∀ i, φ ∘ₗ ρ i = σ i ∘ₗ φ` using `fun φ hφ i => by`.

Take `⟨f, -, h1, -⟩` from `GlobalTheory.ProductForm.mem_factorSpace.mp hφ`. Conclude with `h1 i`. Take `⟨r, hr⟩` from `GlobalTheory.ProductForm.exists_lift ρ σ q hq β S F le_rfl hS`. Take `⟨r', hr'⟩` from `GlobalTheory.ProductForm.exists_lift ρ σ q' hq' β' S' F hle hS'`. Set `e : Pr ⊗[ℂ] F ≃ₗ[ℂ] Pi` to `LinearEquiv.ofBijective (GlobalTheory.ProductForm.ev F) ⟨GlobalTheory.ProductForm.ev_injective ρ σ hirr hschur F hFeq, GlobalTheory.ProductForm.ev_surjective ρ σ q β S F le_rfl hS hspan⟩`.

Use `⟨ModuleCat.of ℂ F, r, r', e, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x`. Take `⟨f, hf, -, hβ⟩` from `GlobalTheory.ProductForm.mem_factorSpace.mp (x : F).2`. Conclude with `⟨f, hf, Subtype.ext (GlobalTheory.ProductForm.comp_cancel hq ((hr f hf).trans hβ))⟩`. Introduce `x`.

Take `⟨f, hf, -, hβ⟩` from `GlobalTheory.ProductForm.mem_factorSpace.mp (hge (x : F).2)`. Conclude with `⟨f, hf, Subtype.ext (GlobalTheory.ProductForm.comp_cancel hq' ((hr' f hf).trans hβ))⟩`. Introduce `f hf P`. Express the relevant statement in the definitionally equal form `β f P = GlobalTheory.ProductForm.ev F (q P ⊗ₜ r f)`. Rewrite using `[GlobalTheory.ProductForm.ev_tmul, ← hr f hf]`.

Both sides reduce to the same expression. Introduce `f hf P`. Express the relevant statement in the definitionally equal form `β' f P = GlobalTheory.ProductForm.ev F (q' P ⊗ₜ r' f)`. Rewrite using `[GlobalTheory.ProductForm.ev_tmul, ← hr' f hf]`. Both sides reduce to the same expression.
-/
theorem GlobalTheory.SquareLM.productForm : ∀ (ι Pr Pi Q Q' V V' : Type) [AddCommGroup Pr] [Module ℂ Pr] [AddCommGroup Pi] [Module ℂ Pi] [AddCommGroup Q] [Module ℂ Q]
  [AddCommGroup Q'] [Module ℂ Q'] [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
  (ρ : ι → Module.End ℂ Pr) (σ : ι → Module.End ℂ Pi) (q : Q →ₗ[ℂ] Pr) (q' : Q' →ₗ[ℂ] Pr)
  (β : V →ₗ[ℂ] Q →ₗ[ℂ] Pi) (β' : V' →ₗ[ℂ] Q' →ₗ[ℂ] Pi) (S : Submodule ℂ V) (S' : Submodule ℂ V'),
  Function.Surjective q → Function.Surjective q' →
  (∀ N : Submodule ℂ Pr, (∀ i, ∀ x ∈ N, ρ i x ∈ N) → N = ⊥ ∨ N = ⊤) →
  (∀ T : Module.End ℂ Pr, (∀ i, T * ρ i = ρ i * T) → ∃ c : ℂ, T = c • 1) →
  (∀ f ∈ S, ∃ φ : Pr →ₗ[ℂ] Pi, (∀ i, φ ∘ₗ ρ i = σ i ∘ₗ φ) ∧ β f = φ ∘ₗ q) →
  (∀ f ∈ S', ∃ φ : Pr →ₗ[ℂ] Pi, (∀ i, φ ∘ₗ ρ i = σ i ∘ₗ φ) ∧ β' f = φ ∘ₗ q') →
  Submodule.span ℂ {y | ∃ f ∈ S, ∃ P, y = β f P} = ⊤ → Submodule.span ℂ {y | ∃ f ∈ S', ∃ P, y = β' f P} = ⊤ →
  ∃ (Pf : ModuleCat.{0} ℂ) (r : V →ₗ[ℂ] Pf) (r' : V' →ₗ[ℂ] Pf) (e : Pr ⊗[ℂ] Pf ≃ₗ[ℂ] Pi),
    (∀ x, ∃ f ∈ S, r f = x) ∧ (∀ x, ∃ f ∈ S', r' f = x) ∧
    (∀ f ∈ S, ∀ P, β f P = e (q P ⊗ₜ r f)) ∧ ∀ f ∈ S', ∀ P, β' f P = e (q' P ⊗ₜ r' f) := by
  intro ι Pr Pi Q Q' V V' _ _ _ _ _ _ _ _ _ _ _ _ ρ σ q q' β β' S S' hq hq' hirr hschur hS hS'
    hspan hspan'
  classical
  let F := GlobalTheory.ProductForm.factorSpace ρ σ q β S
  have hle : GlobalTheory.ProductForm.factorSpace ρ σ q' β' S' ≤ F :=
    GlobalTheory.ProductForm.factorSpace_le ρ σ hirr hschur q' β' S' q β S hS hspan
  have hge : F ≤ GlobalTheory.ProductForm.factorSpace ρ σ q' β' S' :=
    GlobalTheory.ProductForm.factorSpace_le ρ σ hirr hschur q β S q' β' S' hS' hspan'
  have hFeq : ∀ φ ∈ F, ∀ i, φ ∘ₗ ρ i = σ i ∘ₗ φ := fun φ hφ i => by
    obtain ⟨f, -, h1, -⟩ := GlobalTheory.ProductForm.mem_factorSpace.mp hφ
    exact h1 i
  obtain ⟨r, hr⟩ := GlobalTheory.ProductForm.exists_lift ρ σ q hq β S F le_rfl hS
  obtain ⟨r', hr'⟩ := GlobalTheory.ProductForm.exists_lift ρ σ q' hq' β' S' F hle hS'
  let e : Pr ⊗[ℂ] F ≃ₗ[ℂ] Pi := LinearEquiv.ofBijective (GlobalTheory.ProductForm.ev F)
    ⟨GlobalTheory.ProductForm.ev_injective ρ σ hirr hschur F hFeq,
      GlobalTheory.ProductForm.ev_surjective ρ σ q β S F le_rfl hS hspan⟩
  refine ⟨ModuleCat.of ℂ F, r, r', e, ?_, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨f, hf, -, hβ⟩ := GlobalTheory.ProductForm.mem_factorSpace.mp (x : F).2
    exact ⟨f, hf, Subtype.ext (GlobalTheory.ProductForm.comp_cancel hq ((hr f hf).trans hβ))⟩
  · intro x
    obtain ⟨f, hf, -, hβ⟩ := GlobalTheory.ProductForm.mem_factorSpace.mp (hge (x : F).2)
    exact ⟨f, hf, Subtype.ext (GlobalTheory.ProductForm.comp_cancel hq' ((hr' f hf).trans hβ))⟩
  · intro f hf P
    change β f P = GlobalTheory.ProductForm.ev F (q P ⊗ₜ r f)
    rw [GlobalTheory.ProductForm.ev_tmul, ← hr f hf]
    rfl
  · intro f hf P
    change β' f P = GlobalTheory.ProductForm.ev F (q' P ⊗ₜ r' f)
    rw [GlobalTheory.ProductForm.ev_tmul, ← hr' f hf]
    rfl
