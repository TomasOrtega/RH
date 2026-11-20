import Mathlib
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Imports
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.SmoothMapsClosureStatement
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.KapBes

variable {k r : ℕ}

/- English proof (translation)
Proceed by induction on `W with`. Consider the case `nil => rfl`. Consider the case `cons X W ih => show PI.UpqRep.dsig (k := k) (r := r) R.σ X (PI.UpqRep.dsigW (k := k) (r := r) R.σ W 0) = 0`. Rewrite using `[ih]`. Simplify using `[PI.UpqRep.dsig]`.
-/
theorem dsigW_zero (R : Rep k r) (W : List (Mx k r)) :
    PI.UpqRep.dsigW (k := k) (r := r) R.σ W (0 : R.H) = 0 := by
  induction W with
  | nil => rfl
  | cons X W ih =>
    show PI.UpqRep.dsig (k := k) (r := r) R.σ X (PI.UpqRep.dsigW (k := k) (r := r) R.σ W 0) = 0
    rw [ih]
    simp [PI.UpqRep.dsig]

/- English proof (translation)
Introduce `_ _` and use `Formalism.FourierDecayAlt.P.DDSmoothness.smooth_zero R'.σ add := by intros; simp smul := by intros; simp cont := fun W _ => ⟨0, [], by simp, fun v _ => by simp [dsigW_zero]⟩`.
-/
theorem smMap_zero (R R' : Rep k r) : SmMap R R' (fun _ => 0) where
  mem := fun _ _ => Formalism.FourierDecayAlt.P.DDSmoothness.smooth_zero R'.σ
  add := by intros; simp
  smul := by intros; simp
  cont := fun W _ => ⟨0, [], by simp, fun v _ => by simp [dsigW_zero]⟩

/- English proof (translation)
Introduce `v hv` and use `by rw [e v hv]; exact h.mem v hv add := fun v hv w hw => by rw [e v hv, e w hw, e _ (Formalism.FourierDecayAlt.P.DDSmoothness.smooth_add hv hw), h.add v hv w hw] smul := fun a v hv => by rw [e v hv, e _ (Formalism.FourierDecayAlt.P.DDSmoothness.smooth_smul a hv), h.smul a v hv] c …`.
-/
theorem smMap_congr {R R' : Rep k r} {T T' : R.H → R'.H} (h : SmMap R R' T)
    (e : ∀ v ∈ R.sm, T' v = T v) : SmMap R R' T' where
  mem := fun v hv => by rw [e v hv]; exact h.mem v hv
  add := fun v hv w hw => by
    rw [e v hv, e w hw, e _ (Formalism.FourierDecayAlt.P.DDSmoothness.smooth_add hv hw), h.add v hv w hw]
  smul := fun a v hv => by
    rw [e v hv, e _ (Formalism.FourierDecayAlt.P.DDSmoothness.smooth_smul a hv), h.smul a v hv]
  cont := fun W hW => by
    obtain ⟨C, Ws, h1, h2⟩ := h.cont W hW
    exact ⟨C, Ws, h1, fun v hv => by
      have := h2 v hv
      simp only at this ⊢
      rw [e v hv]; exact this⟩

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using smMap_zero R R'`. Consider the case `insert i s hi ih`. Simplify using `only [Finset.sum_insert hi]`. Conclude with `hl _ _ _ (hT i) ih`.
-/
theorem smMap_sum {R R' : Rep k r}
    (hl : ∀ (T T' : R.H → R'.H) (a : ℂ), SmMap R R' T → SmMap R R' T' → SmMap R R' (fun v => a • T v + T' v))
    {ι : Type} (s : Finset ι) (a : ι → ℂ) (T : ι → R.H → R'.H) (hT : ∀ i, SmMap R R' (T i)) :
    SmMap R R' (fun v => ∑ i ∈ s, a i • T i v) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using smMap_zero R R'
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact hl _ _ _ (hT i) ih

/- English proof (translation)
Take `⟨h, hh, m, hm, rfl⟩` from `hs`. Establish `h1 : hᴴ * Formalism.QuantumDeterminants.Hpk k r * h = Formalism.QuantumDeterminants.Hpk k r` using `hh.1`. Establish `h2 : mᴴ * Formalism.QuantumDeterminants.Hpk k r * m = Formalism.QuantumDeterminants.Hpk k r` using `hm.1`. Use `show (h * m)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (h * m) = Formalism.QuantumDeterminants.Hpk k r`. Rewrite using `[conjTranspose_mul]`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = _ := by rw [h1, h2]`.
-/
theorem mem_GG_of_mem_Sset {z : Fin (2 * r + k + 1) → ℂ} {s : Mx k r} (hs : s ∈ Formalism.QuantumDeterminants.Sset k r z) :
    s ∈ GG k r := by
  obtain ⟨h, hh, m, hm, rfl⟩ := hs
  have h1 : hᴴ * Formalism.QuantumDeterminants.Hpk k r * h = Formalism.QuantumDeterminants.Hpk k r := hh.1
  have h2 : mᴴ * Formalism.QuantumDeterminants.Hpk k r * m = Formalism.QuantumDeterminants.Hpk k r := hm.1
  show (h * m)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (h * m) = Formalism.QuantumDeterminants.Hpk k r
  rw [conjTranspose_mul]
  calc mᴴ * hᴴ * Formalism.QuantumDeterminants.Hpk k r * (h * m) = mᴴ * (hᴴ * Formalism.QuantumDeterminants.Hpk k r * h) * m := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [h1, h2]

/- English proof (translation)
Unfold `ev`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_smul]`. Both sides reduce to the same expression.
-/
theorem ev_eq {ι : Type} [Fintype ι] (Γ : Matrix ι ι ℂ) (R : Rep k r) (a : ι → ℂ) (x : ι → R.H) :
    ev Γ R a x = ∑ j, (star a ᵥ* Γ) j • x j := by
  unfold ev
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_smul]
  rfl

/- English proof (translation)
Establish `h : star a ᵥ* Aᴴ = star a` using `by rw [← star_mulVec, ha]`. Use `conv_rhs => rw [← hA, ← vecMul_vecMul, ← vecMul_vecMul, h]`.
-/
theorem vecMul_inv {ι : Type} [Fintype ι] (Γ A : Matrix ι ι ℂ) (a : ι → ℂ) (hA : Aᴴ * Γ * A = Γ)
    (ha : A *ᵥ a = a) : (star a ᵥ* Γ) ᵥ* A = star a ᵥ* Γ := by
  have h : star a ᵥ* Aᴴ = star a := by rw [← star_mulVec, ha]
  conv_rhs => rw [← hA, ← vecMul_vecMul, ← vecMul_vecMul, h]

/- English proof (translation)
Introduce `hK k r ι κ _ _ _ _ ρ Γ d R RI io pr ε mu muI Wp _ _ _ _ z π om hR hRI hF hT hom I`. Take `⟨-, -, hlin, hcw⟩` from `GlobalTheory.T.smooth_maps_closure hK k r ε mu (muI I) mu R (RI I) R hR (hRI I) hR`. Take `⟨-, -, hlin', -⟩` from `GlobalTheory.T.smooth_maps_closure hK k r ε (muI I) mu mu (RI I) R R (hRI I) hR hR`. Use `⟨fun lI hl => ?_, fun s hs y hy => ?_, ?_⟩` and prove the remaining obligations. Establish `hP : SmMap R (RI I) (fun v => ∑ c, pr I c (tm R om v c))` using `smMap_congr (smMap_sum hlin Finset.univ om (pr I) (hT.pr_sm I)) (fun v hv => Finset.sum_congr rfl fun c _ => (hT.pr_sm I c).smul (om c) v hv)`.

Take `⟨h1, h2, h3, h4⟩` from `hl`. Use `⟨fun v hv w hw => ?_, fun c v hv => ?_, fun h hh m hm v hv => ?_, hcw Wp _ lI hP h4⟩` and prove the remaining obligations. Use `hP.add v hv w hw` as an intermediate fact. Simplify using `only at this ⊢`. Rewrite using `[this]`.

Conclude with `h1 _ (hP.mem v hv) _ (hP.mem w hw)`. Use `hP.smul c v hv` as an intermediate fact. Simplify using `only at this ⊢`. Rewrite using `[this]`. Conclude with `h2 c _ (hP.mem v hv)`.

Establish `hs : h * m ∈ Formalism.QuantumDeterminants.Sset k r z` using `⟨h, hh, m, hm, rfl⟩`. Establish `e : tm R om (R.σ (h * m) v) = act ρ R (h * m) (tm R om v)`. Use function extensionality and compare the values at `i`. Use `congrFun (hom _ hs) i` as an intermediate fact. Simplify using `only [tm, act, map_smul, smul_smul, ← Finset.sum_smul]`.

Rewrite using `[← this]`. Both sides reduce to the same expression. Establish `e2` using `hT.pr_eq I _ (mem_GG_of_mem_Sset hs) (tm R om v) (fun c => Formalism.FourierDecayAlt.P.DDSmoothness.smooth_smul (om c) hv)`. Simplify using `only`. Rewrite using `[e, e2]`.

Conclude with `h3 h hh m hm _ (hP.mem v hv)`. Establish `hG` using `mem_GG_of_mem_Sset hs`. Rewrite using `[hT.io_eq I s hG y hy, ev_eq, ev_eq]`. Establish `hv` using `vecMul_inv Γ (ρ s) om (hF.2.2.2.2.1 s hG) (hom s hs)`. Simplify using `only [act, map_sum, map_smul, Finset.smul_sum, smul_smul]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_smul, ← congrFun hv j]`. Both sides reduce to the same expression. Conclude with `smMap_congr (smMap_sum hlin' Finset.univ (star om ᵥ* Γ) (io I) (hT.io_sm I)) (fun y _ => ev_eq Γ R om _)`.
-/
theorem main : PI.KFinSmooth → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (om : ι → ℂ), R.IsDG ε mu → (∀ I, (RI I).IsDG ε (muI I)) → IsFRep ρ Γ d → TensRaw ρ R RI io pr → (∀ s ∈ Formalism.QuantumDeterminants.Sset k r z, ρ s *ᵥ om = om) → ∀ I, (∀ lI, IsBes (RI I) z π lI → IsBes R z π (fun v => lI (∑ c, pr I c (tm R om v c)))) ∧ (∀ s ∈ Formalism.QuantumDeterminants.Sset k r z, ∀ y ∈ (RI I).sm, ev Γ R om (fun c => io I c ((RI I).σ s y)) = R.σ s (ev Γ R om (fun c => io I c y))) ∧ SmMap (RI I) R (fun y => ev Γ R om (fun c => io I c y)) := by
  intro hK k r ι κ _ _ _ _ ρ Γ d R RI io pr ε mu muI Wp _ _ _ _ z π om hR hRI hF hT hom I
  obtain ⟨-, -, hlin, hcw⟩ := GlobalTheory.T.smooth_maps_closure hK k r ε mu (muI I) mu R (RI I) R hR (hRI I) hR
  obtain ⟨-, -, hlin', -⟩ := GlobalTheory.T.smooth_maps_closure hK k r ε (muI I) mu mu (RI I) R R (hRI I) hR hR
  refine ⟨fun lI hl => ?_, fun s hs y hy => ?_, ?_⟩
  · have hP : SmMap R (RI I) (fun v => ∑ c, pr I c (tm R om v c)) :=
      smMap_congr (smMap_sum hlin Finset.univ om (pr I) (hT.pr_sm I)) (fun v hv =>
        Finset.sum_congr rfl fun c _ => (hT.pr_sm I c).smul (om c) v hv)
    obtain ⟨h1, h2, h3, h4⟩ := hl
    refine ⟨fun v hv w hw => ?_, fun c v hv => ?_, fun h hh m hm v hv => ?_, hcw Wp _ lI hP h4⟩
    · have := hP.add v hv w hw
      simp only at this ⊢
      rw [this]; exact h1 _ (hP.mem v hv) _ (hP.mem w hw)
    · have := hP.smul c v hv
      simp only at this ⊢
      rw [this]; exact h2 c _ (hP.mem v hv)
    · have hs : h * m ∈ Formalism.QuantumDeterminants.Sset k r z := ⟨h, hh, m, hm, rfl⟩
      have e : tm R om (R.σ (h * m) v) = act ρ R (h * m) (tm R om v) := by
        funext i
        have := congrFun (hom _ hs) i
        simp only [tm, act, map_smul, smul_smul, ← Finset.sum_smul]
        rw [← this]; rfl
      have e2 := hT.pr_eq I _ (mem_GG_of_mem_Sset hs) (tm R om v)
        (fun c => Formalism.FourierDecayAlt.P.DDSmoothness.smooth_smul (om c) hv)
      simp only
      rw [e, e2]
      exact h3 h hh m hm _ (hP.mem v hv)
  · have hG := mem_GG_of_mem_Sset hs
    rw [hT.io_eq I s hG y hy, ev_eq, ev_eq]
    have hv := vecMul_inv Γ (ρ s) om (hF.2.2.2.2.1 s hG) (hom s hs)
    simp only [act, map_sum, map_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_smul, ← congrFun hv j]
    rfl
  · exact smMap_congr (smMap_sum hlin' Finset.univ (star om ᵥ* Γ) (io I) (hT.io_sm I))
      (fun y _ => ev_eq Γ R om _)

end GlobalTheory.KapBes
