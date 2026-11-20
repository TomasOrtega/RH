import Mathlib
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Imports
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.TensForm

/- English proof (translation)
Establish `hs : ∀ (L : List α) v, 0 ≤ (L.map fun a => n a v).sum`. Introduce `L v`. Apply `List.sum_nonneg` to reduce the goal to its premises. Introduce `x hx`. Take `⟨a, -, rfl⟩` from `List.mem_map.1 hx`.

Conclude with `hn a v`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => exact ⟨0, [], le_rfl, by simp, by simp⟩`. Consider the case `insert c s _ ih`. Take `⟨C, L, hC, hL, hb⟩` from `ih`.

Take `⟨C', L', hL', hb'⟩` from `h c`. Use `⟨C + |C'|, L ++ L', by positivity, ?_, ?_⟩` and prove the remaining obligations. Introduce `a ha`. Break down `List.mem_append.1 ha with ha | ha` into its components or cases. Conclude with `hL a ha`.

Conclude with `hL' a ha`. Introduce `d hd v hv`. Rewrite using `[List.map_append, List.sum_append]`. Establish `h1` using `hs L v`. Establish `h2` using `hs L' v`.

Establish `h3` using `abs_nonneg C'`. Establish `h4` using `le_abs_self C'`. Break down `Finset.mem_insert.1 hd with rfl | hd` into its components or cases. Use `hb' v hv` as an intermediate fact. Use polynomial arithmetic with `[mul_nonneg hC h1, mul_nonneg hC h2, mul_nonneg h3 h1, mul_le_mul_of_nonneg_right h4 h2]`.

Use `hb d hd v hv` as an intermediate fact. Use polynomial arithmetic with `[mul_nonneg hC h2, mul_nonneg h3 h1, mul_nonneg h3 h2]`.
-/
theorem common_bound {ι α β : Type} [DecidableEq ι] (P : α → Prop) (S : Set β) (n : α → β → ℝ)
    (hn : ∀ a v, 0 ≤ n a v) (f : ι → β → ℝ)
    (h : ∀ c, ∃ (C : ℝ) (L : List α), (∀ a ∈ L, P a) ∧ ∀ v ∈ S, f c v ≤ C * (L.map fun a => n a v).sum)
    (s : Finset ι) :
    ∃ (C : ℝ) (L : List α), 0 ≤ C ∧ (∀ a ∈ L, P a) ∧
      ∀ c ∈ s, ∀ v ∈ S, f c v ≤ C * (L.map fun a => n a v).sum := by
  have hs : ∀ (L : List α) v, 0 ≤ (L.map fun a => n a v).sum := by
    intro L v
    apply List.sum_nonneg
    intro x hx
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
    exact hn a v
  induction s using Finset.induction_on with
  | empty => exact ⟨0, [], le_rfl, by simp, by simp⟩
  | insert c s _ ih =>
    obtain ⟨C, L, hC, hL, hb⟩ := ih
    obtain ⟨C', L', hL', hb'⟩ := h c
    refine ⟨C + |C'|, L ++ L', by positivity, ?_, ?_⟩
    · intro a ha
      rcases List.mem_append.1 ha with ha | ha
      · exact hL a ha
      · exact hL' a ha
    · intro d hd v hv
      rw [List.map_append, List.sum_append]
      have h1 := hs L v
      have h2 := hs L' v
      have h3 := abs_nonneg C'
      have h4 := le_abs_self C'
      rcases Finset.mem_insert.1 hd with rfl | hd
      · have := hb' v hv
        nlinarith [mul_nonneg hC h1, mul_nonneg hC h2, mul_nonneg h3 h1,
          mul_le_mul_of_nonneg_right h4 h2]
      · have := hb d hd v hv
        nlinarith [mul_nonneg hC h2, mul_nonneg h3 h1, mul_nonneg h3 h2]

variable {k r : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Establish `hiso : ∀ a b, ⟪R.σ g a, R.σ g b⟫_ℂ = ⟪a, b⟫_ℂ` using `(LinearMap.norm_map_iff_inner_map_map ((R.σ g : R.H →L[ℂ] R.H) : R.H →ₗ[ℂ] R.H)).1 hσ`. Use `conv_rhs => rw [← hρ]`. Simplify using `only [hh, act, sum_inner, inner_sum, inner_smul_left, inner_smul_right, hiso, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.mul_sum, Finset.sum_mul]`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun b _ => Finset.sum_comm`. Use `_ = ∑ b, ∑ a, ∑ j, ∑ i, Γ i j * (ρ g j b * ((starRingEnd ℂ) (ρ g i a) * ⟪y a, x b⟫_ℂ)) := by`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun b _ => Finset.sum_comm`.

Use `_ = ∑ a, ∑ b, ∑ j, ∑ i, Γ i j * (ρ g j b * ((starRingEnd ℂ) (ρ g i a) * ⟪y a, x b⟫_ℂ)) := Finset.sum_comm`. Use `_ = _ := by`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[RCLike.star_def]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hh_act (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (R : Rep k r) (g : Mx k r)
    (hρ : (ρ g)ᴴ * Γ * ρ g = Γ) (hσ : ∀ v, ‖R.σ g v‖ = ‖v‖) (x y : ι → R.H) :
    hh Γ R (act ρ R g x) (act ρ R g y) = hh Γ R x y := by
  have hiso : ∀ a b, ⟪R.σ g a, R.σ g b⟫_ℂ = ⟪a, b⟫_ℂ :=
    (LinearMap.norm_map_iff_inner_map_map ((R.σ g : R.H →L[ℂ] R.H) : R.H →ₗ[ℂ] R.H)).1 hσ
  conv_rhs => rw [← hρ]
  simp only [hh, act, sum_inner, inner_sum, inner_smul_left, inner_smul_right, hiso, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Finset.mul_sum, Finset.sum_mul]
  calc _ = ∑ j, ∑ i, ∑ b, ∑ a, Γ i j * (ρ g j b * ((starRingEnd ℂ) (ρ g i a) * ⟪y a, x b⟫_ℂ)) :=
        Finset.sum_comm
    _ = ∑ j, ∑ b, ∑ a, ∑ i, Γ i j * (ρ g j b * ((starRingEnd ℂ) (ρ g i a) * ⟪y a, x b⟫_ℂ)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ b, ∑ a, ∑ j, ∑ i, Γ i j * (ρ g j b * ((starRingEnd ℂ) (ρ g i a) * ⟪y a, x b⟫_ℂ)) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ j, ∑ i, Γ i j * (ρ g j b * ((starRingEnd ℂ) (ρ g i a) * ⟪y a, x b⟫_ℂ)) :=
        Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
          Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
        rw [RCLike.star_def]
        ring

omit [DecidableEq ι] in

/- English proof (translation)
Rewrite using `[hh, Finset.sum_mul]`. Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[Finset.sum_mul]`. Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[norm_mul]`.

Use `mul_le_mul_of_nonneg_left ((norm_inner_le_norm _ _).trans ?_) (norm_nonneg _)` and prove the remaining obligations. Rewrite using `[mul_comm A B]`. Conclude with `mul_le_mul (hy i) (hx j) (norm_nonneg _) ((norm_nonneg _).trans (hy i))`.
-/
theorem norm_hh_le (Γ : Matrix ι ι ℂ) (R : Rep k r) (x y : ι → R.H) (A B : ℝ)
    (hx : ∀ c, ‖x c‖ ≤ A) (hy : ∀ c, ‖y c‖ ≤ B) :
    ‖hh Γ R x y‖ ≤ (∑ i, ∑ j, ‖Γ i j‖) * (A * B) := by
  rw [hh, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ((norm_inner_le_norm _ _).trans ?_) (norm_nonneg _)
  rw [mul_comm A B]
  exact mul_le_mul (hy i) (hx j) (norm_nonneg _) ((norm_nonneg _).trans (hy i))

/- English proof (translation)
Take `⟨C, L, -, hL, hb⟩` from `common_bound (fun W : List (Mx k r) => ∀ X ∈ W, PI.UpqRep.InLieHpk k r X) R.sm (fun W v => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ W v‖) (fun _ _ => norm_nonneg _) (fun c v => ‖T c v‖) (fun c => (hT c).cont [] (by simp)) Finset.univ`. Conclude with `⟨C, L, hL, fun c => hb c (Finset.mem_univ c)⟩`.
-/
theorem family_bound (R R' : Rep k r) (T : ι → R.H → R'.H) (hT : ∀ c, SmMap R R' (T c)) :
    ∃ (C : ℝ) (Ws : List (List (Mx k r))), (∀ W ∈ Ws, ∀ X ∈ W, PI.UpqRep.InLieHpk k r X) ∧
      ∀ c, ∀ v ∈ R.sm, ‖T c v‖ ≤ C * (Ws.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ W v‖).sum := by
  obtain ⟨C, L, -, hL, hb⟩ := common_bound (fun W : List (Mx k r) => ∀ X ∈ W, PI.UpqRep.InLieHpk k r X) R.sm
    (fun W v => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ W v‖) (fun _ _ => norm_nonneg _)
    (fun c v => ‖T c v‖) (fun c => (hT c).cont [] (by simp)) Finset.univ
  exact ⟨C, L, hL, fun c => hb c (Finset.mem_univ c)⟩

/- English proof (translation)
Introduce `_ k r ι κ _ _ _ _ ρ Γ d R RI io pr ε mu muI hR _ hF hT I J`. Use `⟨?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx x' hx' y _`. Simplify using `only [hh, fun c => (hT.io_sm I c).add x hx x' hx', inner_add_right, mul_add, Finset.sum_add_distrib]`. Introduce `a x hx y _`.

Simplify using `only [hh, fun c => (hT.io_sm I c).smul a x hx, inner_smul_right, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring`. Introduce `x _ y hy y' hy'`. Simplify using `only [hh, fun c => (hT.io_sm J c).add y hy y' hy', inner_add_left, mul_add, Finset.sum_add_distrib]`. Introduce `a x _ y hy`.

Simplify using `only [hh, fun c => (hT.io_sm J c).smul a y hy, inner_smul_left, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [RCLike.star_def]; ring`. Introduce `g hg x hx y hy show hh Γ R (fun c => io I c ((RI I).σ g x)) (fun c => io J c ((RI J).σ g y)) = _`. Rewrite using `[hT.io_eq I g hg x hx, hT.io_eq J g hg y hy]`. Conclude with `hh_act ρ Γ R g (hF.2.2.2.2.1 g hg) ((Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.sigma_facts hR.2).2 g hg) _ _`.

Take `⟨C, Ws, hW, hb⟩` from `family_bound (RI I) R (io I) (hT.io_sm I)`. Take `⟨C', Ws', hW', hb'⟩` from `family_bound (RI J) R (io J) (hT.io_sm J)`. Use `⟨(∑ i, ∑ j, ‖Γ i j‖) * C * C', Ws, Ws', ?_, ?_⟩` and prove the remaining obligations. Introduce `W hWm`. Break down `List.mem_append.1 hWm with h | h` into its components or cases.

Conclude with `hW W h`. Conclude with `hW' W h`. Introduce `x hx y hy`. Use `(norm_hh_le Γ R _ _ _ _ (fun c => hb c x hx) (fun c => hb' c y hy)).trans (le_of_eq ?_)` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pulledBack_isInvForm : PI.KFinSmooth → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ), R.IsDG ε mu → (∀ I, (RI I).IsDG ε (muI I)) → IsFRep ρ Γ d → TensRaw ρ R RI io pr → ∀ I J, IsInvForm (RI I) (RI J) (fun y y' => hh Γ R (fun c => io I c y) (fun c => io J c y')) := by
  intro _ k r ι κ _ _ _ _ ρ Γ d R RI io pr ε mu muI hR _ hF hT I J
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx x' hx' y _
    simp only [hh, fun c => (hT.io_sm I c).add x hx x' hx', inner_add_right, mul_add, Finset.sum_add_distrib]
  · intro a x hx y _
    simp only [hh, fun c => (hT.io_sm I c).smul a x hx, inner_smul_right, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  · intro x _ y hy y' hy'
    simp only [hh, fun c => (hT.io_sm J c).add y hy y' hy', inner_add_left, mul_add, Finset.sum_add_distrib]
  · intro a x _ y hy
    simp only [hh, fun c => (hT.io_sm J c).smul a y hy, inner_smul_left, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [RCLike.star_def]; ring
  · intro g hg x hx y hy
    show hh Γ R (fun c => io I c ((RI I).σ g x)) (fun c => io J c ((RI J).σ g y)) = _
    rw [hT.io_eq I g hg x hx, hT.io_eq J g hg y hy]
    exact hh_act ρ Γ R g (hF.2.2.2.2.1 g hg) ((Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.sigma_facts hR.2).2 g hg) _ _
  · obtain ⟨C, Ws, hW, hb⟩ := family_bound (RI I) R (io I) (hT.io_sm I)
    obtain ⟨C', Ws', hW', hb'⟩ := family_bound (RI J) R (io J) (hT.io_sm J)
    refine ⟨(∑ i, ∑ j, ‖Γ i j‖) * C * C', Ws, Ws', ?_, ?_⟩
    · intro W hWm
      rcases List.mem_append.1 hWm with h | h
      · exact hW W h
      · exact hW' W h
    · intro x hx y hy
      refine (norm_hh_le Γ R _ _ _ _ (fun c => hb c x hx) (fun c => hb' c y hy)).trans (le_of_eq ?_)
      ring

end GlobalTheory.TensForm
