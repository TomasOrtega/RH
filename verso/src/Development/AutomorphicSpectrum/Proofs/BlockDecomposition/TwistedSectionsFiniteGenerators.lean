import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformVanishing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedIdealPowerLeSectionsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedSectionsCauchyLimitStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE.TwLim

/- English proof (translation)
Take `⟨a, rfl⟩` from `hx`. Take `⟨b, rfl⟩` from `hy`. Conclude with `⟨a - b, map_sub _ a b⟩`.
-/
theorem twSecs_sub_mem {X : Scheme.{0}} (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X) (n : ℤ) {P : X.Modules}
    (S : Subobject P) {x y : Γ(GlobalTheory.twistZ P H n, ⊤)} (hx : x ∈ twSecs H n S)
    (hy : y ∈ twSecs H n S) : x - y ∈ twSecs H n S := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a - b, map_sub _ a b⟩

/- English proof (translation)
Introduce and unpack `_ ⟨a, rfl⟩`. Use `⟨(GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (Subobject.ofLE S T h)).app ⊤ a, ?_⟩` and prove the remaining obligations. Rewrite using `[← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, ← GlobalTheory.Twist.map_comp, Subobject.ofLE_arrow]`.
-/
theorem twSecs_mono {X : Scheme.{0}} (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X) (n : ℤ) {P : X.Modules}
    {S T : Subobject P} (h : S ≤ T) : twSecs H n S ⊆ twSecs H n T := by
  rintro _ ⟨a, rfl⟩
  refine ⟨(GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (Subobject.ofLE S T h)).app ⊤ a, ?_⟩
  rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, ← GlobalTheory.Twist.map_comp,
    Subobject.ofLE_arrow]

/- English proof (translation)
The claim follows from `Submodule.zero_mem _`.
-/
theorem zero_mem_twPow {A : Type} [CommRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))]
    (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X) (n : ℤ) (P : X.Modules) (m : ℕ) : (0 : Γ(GlobalTheory.twistZ P H n, ⊤)) ∈ twPow I H n P m :=
  Submodule.zero_mem _

end GlobalTheory.CompanionTheory.GE.TwLim

namespace GlobalTheory.CompanionTheory.GE.TwLim

/- English proof (translation)
The claim follows from `GlobalTheory.T.twisted_ideal_power_le_sections`.
-/
theorem twPow_sub_twSecs : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), GlobalTheory.IsAmpleLB H → ∀ {P : X.Modules}, IsCoherent P → ∀ (n : ℤ) (m : ℕ), twPow I H n P m ⊆ twSecs H n (powSub I P m) := GlobalTheory.T.twisted_ideal_power_le_sections

/- English proof (translation)
The claim follows from `GlobalTheory.T.twisted_sections_cauchy_limit`.
-/
theorem twPow_complete : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A), IsAdicComplete I A → ∀ {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), GlobalTheory.IsAmpleLB H → ∀ {P : X.Modules}, IsCoherent P → ∀ (n : ℤ) (f : ℕ → Γ(GlobalTheory.twistZ P H n, ⊤)), (∀ m, f m - f (m + 1) ∈ twPow I H n P m) → ∃ L : Γ(GlobalTheory.twistZ P H n, ⊤), ∀ m, f m - L ∈ twPow I H n P m := GlobalTheory.T.twisted_sections_cauchy_limit

/- English proof (translation)
The claim follows from `antitone_nat_of_succ_le fun m => (hS.succ m).symm ▸ le_sup_left`.
-/
theorem antitone_closedSys {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}}
    [X.Over (Spec (.of A))] {P : X.Modules} {S : ℕ → Subobject P} (hS : ClosedSys I P S) :
    Antitone S :=
  antitone_nat_of_succ_le fun m => (hS.succ m).symm ▸ le_sup_left

/- English proof (translation)
Introduce `A _ _ I hI X _ _ H hH P hP S hS n hstep`. Use `⟨⋂ e, twSecs H n (S e), fun e => Set.iInter_subset _ e, ?_⟩` and prove the remaining obligations. Introduce `e x hx`. Establish `hpow : ∀ m, twPow I H n P (m + 1) ⊆ twSecs H n (S m)` using `fun m => (twPow_sub_twSecs I H hH hP n (m + 1)).trans (twSecs_mono H n (hS.pow_le m))`. Set `seq : ∀ k : ℕ, {y // y ∈ twSecs H n (S (e + k))}` to `fun k => Nat.rec ⟨x, hx⟩ (fun k y => ⟨(hstep (e + k) y.1 y.2).choose, (hstep (e + k) y.1 y.2).choose_spec.1⟩) k`.

Establish `hseq : ∀ k, (seq k).1 - (seq (k + 1)).1 ∈ twPow I H n P (e + k + 1)` using `fun k => (hstep (e + k) (seq k).1 (seq k).2).choose_spec.2`. Establish `hcg : ∀ a b : ℕ, a = b → (seq a).1 = (seq b).1` using `by rintro _ _ rfl; rfl`. Establish `hs0 : (seq 0).1 = x` using `rfl`. Set `f : ℕ → Γ(GlobalTheory.twistZ P H n, ⊤)` to `fun j => (seq (j - (e + 1))).1`. Establish `hf : ∀ j, f j - f (j + 1) ∈ twPow I H n P j`.

Introduce `j`. Distinguish the cases in `hj : j < e + 1`. Establish `h1 : f j = f (j + 1)` using `hcg _ _ (by omega)`. Rewrite using `[h1, sub_self]`. Conclude with `zero_mem_twPow I H n P j`.

Take `⟨k, rfl⟩ : ∃ k, j = e + 1 + k` from `⟨j - (e + 1), by omega⟩`. Establish `h1 : f (e + 1 + k) = (seq k).1` using `hcg _ _ (by omega)`. Establish `h2 : f (e + 1 + k + 1) = (seq (k + 1)).1` using `hcg _ _ (by omega)`. Rewrite using `[h1, h2]`. Use `hseq k` as an intermediate fact.

Rewrite `this` using `[show e + k + 1 = e + 1 + k by omega]`. Then use the resulting hypothesis. Take `⟨L, hL⟩` from `twPow_complete I hI H hH hP n f hf`. Establish `hk : ∀ k, L ∈ twSecs H n (S (e + k))`. Introduce `k`. Establish `h1 : f (e + k + 1) = (seq k).1` using `hcg _ _ (by omega)`.

Establish `hd : (seq k).1 - L ∈ twSecs H n (S (e + k))` using `h1 ▸ hpow (e + k) (hL (e + k + 1))`. Use `twSecs_sub_mem H n _ (seq k).2 hd` as an intermediate fact. Rewrite `this` using `[sub_sub_cancel]`. Then use the resulting hypothesis. Use `⟨L, Set.mem_iInter.2 fun m => ?_, ?_⟩` and prove the remaining obligations. Break down `le_or_gt e m with hm | hm` into its components or cases.

Take `⟨k, rfl⟩` from `Nat.exists_eq_add_of_le hm`. Conclude with `hk k`. Conclude with `twSecs_mono H n (antitone_closedSys I hS hm.le) (by simpa using hk 0)`. Establish `h1 : f (e + 1) = x` using `(hcg (e + 1 - (e + 1)) 0 (by omega)).trans hs0`. Simplify `hL (e + 1)` using `[h1]`.
-/
theorem exists_compat_limit : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A), IsAdicComplete I A → ∀ {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), GlobalTheory.IsAmpleLB H → ∀ {P : X.Modules}, IsCoherent P → ∀ S : ℕ → Subobject P, ClosedSys I P S → ∀ n : ℤ, (∀ e, ∀ x ∈ twSecs H n (S e), ∃ y ∈ twSecs H n (S (e + 1)), x - y ∈ twPow I H n P (e + 1)) → ∃ W : Set Γ(GlobalTheory.twistZ P H n, ⊤), (∀ e, W ⊆ twSecs H n (S e)) ∧ ∀ e, ∀ x ∈ twSecs H n (S e), ∃ b ∈ W, x - b ∈ twPow I H n P (e + 1) := by
  intro A _ _ I hI X _ _ H hH P hP S hS n hstep
  refine ⟨⋂ e, twSecs H n (S e), fun e => Set.iInter_subset _ e, ?_⟩
  intro e x hx
  have hpow : ∀ m, twPow I H n P (m + 1) ⊆ twSecs H n (S m) := fun m =>
    (twPow_sub_twSecs I H hH hP n (m + 1)).trans (twSecs_mono H n (hS.pow_le m))
  let seq : ∀ k : ℕ, {y // y ∈ twSecs H n (S (e + k))} := fun k =>
    Nat.rec ⟨x, hx⟩ (fun k y => ⟨(hstep (e + k) y.1 y.2).choose, (hstep (e + k) y.1 y.2).choose_spec.1⟩) k
  have hseq : ∀ k, (seq k).1 - (seq (k + 1)).1 ∈ twPow I H n P (e + k + 1) := fun k =>
    (hstep (e + k) (seq k).1 (seq k).2).choose_spec.2
  have hcg : ∀ a b : ℕ, a = b → (seq a).1 = (seq b).1 := by rintro _ _ rfl; rfl
  have hs0 : (seq 0).1 = x := rfl
  let f : ℕ → Γ(GlobalTheory.twistZ P H n, ⊤) := fun j => (seq (j - (e + 1))).1
  have hf : ∀ j, f j - f (j + 1) ∈ twPow I H n P j := by
    intro j
    by_cases hj : j < e + 1
    · have h1 : f j = f (j + 1) := hcg _ _ (by omega)
      rw [h1, sub_self]
      exact zero_mem_twPow I H n P j
    · obtain ⟨k, rfl⟩ : ∃ k, j = e + 1 + k := ⟨j - (e + 1), by omega⟩
      have h1 : f (e + 1 + k) = (seq k).1 := hcg _ _ (by omega)
      have h2 : f (e + 1 + k + 1) = (seq (k + 1)).1 := hcg _ _ (by omega)
      rw [h1, h2]
      have := hseq k
      rwa [show e + k + 1 = e + 1 + k by omega] at this
  obtain ⟨L, hL⟩ := twPow_complete I hI H hH hP n f hf
  have hk : ∀ k, L ∈ twSecs H n (S (e + k)) := by
    intro k
    have h1 : f (e + k + 1) = (seq k).1 := hcg _ _ (by omega)
    have hd : (seq k).1 - L ∈ twSecs H n (S (e + k)) := h1 ▸ hpow (e + k) (hL (e + k + 1))
    have := twSecs_sub_mem H n _ (seq k).2 hd
    rwa [sub_sub_cancel] at this
  refine ⟨L, Set.mem_iInter.2 fun m => ?_, ?_⟩
  · rcases le_or_gt e m with hm | hm
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
      exact hk k
    · exact twSecs_mono H n (antitone_closedSys I hS hm.le) (by simpa using hk 0)
  · have h1 : f (e + 1) = x := (hcg (e + 1 - (e + 1)) 0 (by omega)).trans hs0
    simpa [h1] using hL (e + 1)

end GlobalTheory.CompanionTheory.GE.TwLim
