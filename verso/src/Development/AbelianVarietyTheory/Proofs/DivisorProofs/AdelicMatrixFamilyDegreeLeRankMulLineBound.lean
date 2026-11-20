import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdmissibleIntegralBasisChangeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldOneVariableTranscendentalFiniteAndEStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdmissibleAdelicMatrixFamilyPullbackExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IwasawaDecompositionAdmissibleFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientLineDegreeLeOfTriangularFamilyStatement

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.Nef

/- English proof (translation)
Introduce `r`. Proceed by induction on `r with`. Consider the case `zero`. Introduce `k F _ _ _ _ _ _ g _ b _`. Establish `: deg g = 0` using `by simp [deg, ord, Matrix.det_isEmpty]`.

Simplify using `[this]`. Consider the case `succ r ih`. Introduce `k F _ _ _ _ _ hF g hg b hb`. Use `set S : Set ℝ := {c | LinesLE g c} with hS`. Establish `hbS : b ∈ S` using `hb`.

Establish `hbdd : BddBelow S`. Use `⟨(degLine (pullAd (id : Place k F → Place k F) g) (Pi.single 0 1) : ℝ), ?_⟩` and prove the remaining obligations. Introduce `c hc`. Establish `hres : IsRes (k` using `k) (F := F) (E := F) (id : Place k F → Place k F) := by`. Introduce `p x`.

Both sides reduce to the same expression. Establish `h1` using `hc F id hres (Pi.single 0 1) (by`. Introduce `h`. Use `congrFun h 0` as an intermediate fact. Simplify using `at this)`.

Simplify `h1` using `[Module.finrank_self]`. Use `set a := sInf S with ha`. Establish `hab : a ≤ b` using `csInf_le hbdd hbS`. Establish `haS : LinesLE g a`. Introduce `E _ _ _ _ _ ρ hρ w hw`.

Establish `hn : (0 : ℝ) < Module.finrank F E` using `by exact_mod_cast Module.finrank_pos`. Establish `: (degLine (pullAd ρ g) w : ℝ) / Module.finrank F E ≤ a`. Use `le_csInf ⟨b, hbS⟩ ?_` and prove the remaining obligations. Introduce `c hc`. Rewrite using `[div_le_iff₀ hn]`.

Conclude with `hc E ρ hρ w hw`. Rewrite `this` using `[div_le_iff₀ hn]`. Then use the resulting hypothesis. Establish `key : ∀ ε : ℝ, 0 < ε → (deg g : ℝ) ≤ (r + 1) * a + r * ε`. Introduce `ε hε`. Establish `hnot : ¬ LinesLE g (a - ε)` using `fun h => by`.

Use `csInf_le hbdd (show a - ε ∈ S from h)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `only [LinesLE, not_forall, not_le] at hnot`. Take `⟨E, _, _, _, _, _, ρ, hρ, x, hx, hlt⟩` from `hnot`. Establish `hn : (0 : ℝ) < Module.finrank F E` using `by exact_mod_cast Module.finrank_pos`.

Take `⟨hGadm, hGdeg, -, hGlines⟩` from `GlobalTheory.T.isAdmissibleAdelicMatrixFamily_pullback_extension k F E hF ρ hρ (r + 1) g hg`. Establish `hE : IsFF k E` using `(GlobalTheory.T.functionFieldOneVariable_transcendental_finite_and_ext k F hF).2 E`. Establish `hLG : LinesLE (pullAd ρ g) (a * Module.finrank F E)` using `hGlines a haS`. Establish `hδle : (degLine (pullAd ρ g) x : ℝ) ≤ a * Module.finrank F E` using `haS E ρ hρ x hx`. Take `⟨h, u, -, -, hzero, hadm', hadmq, hdeg, hsum, hlines⟩` from `GlobalTheory.T.iwasawa_decomposition_admissible_family k E hE r (pullAd ρ g) hGadm x hx`.

Establish `hLq` using `GlobalTheory.T.quotient_line_degree_le_of_triangular_family k E hE r (fun v => u v * pullAd ρ g v * h) hadm' hzero hadmq (a * Module.finrank F E) (hlines _ hLG)`. Rewrite `hLq` using `[hsum]`. Establish `hq` using `ih k E hE _ hadmq _ hLq`. Establish `hdegZ : (Module.finrank F E : ℤ) * deg g = degLine (pullAd ρ g) x + deg (fun v => (u v * pullAd ρ g v * h).submatrix Fin.succ Fin.succ)`. Rewrite using `[← hGdeg, hdeg]`.

Establish `hdegR : (Module.finrank F E : ℝ) * (deg g : ℝ) = (degLine (pullAd ρ g) x : ℝ) + (deg (fun v => (u v * pullAd ρ g v * h).submatrix Fin.succ Fin.succ) : ℝ)`. Conclude with `hdegZ` after adjusting the coercions. Use `set n : ℝ := (Module.finrank F E : ℝ)`. Use `set δ : ℝ := (degLine (pullAd ρ g) x : ℝ)`. Establish `hr : (0 : ℝ) ≤ r` using `Nat.cast_nonneg r`.

Establish `h2 : (r : ℝ) * (a * n - δ) ≤ r * (ε * n)`. Apply `mul_le_mul_of_nonneg_left _ hr` to reduce the goal to its premises. Use the polynomial consequences of the given equalities and inequalities. Establish `h3 : n * (deg g : ℝ) ≤ n * ((r + 1) * a + r * ε)` using `by nlinarith`. Conclude with `le_of_mul_le_mul_left h3 hn`.

Establish `hfin : (deg g : ℝ) ≤ (r + 1) * a`. Use `le_of_forall_pos_le_add fun ε hε => ?_` and prove the remaining obligations. Use `key (ε / (r + 1)) (by positivity)` as an intermediate fact. Establish `hr : (0 : ℝ) ≤ r` using `Nat.cast_nonneg r`. Establish `: (r : ℝ) * (ε / (r + 1)) ≤ ε`.

Rewrite using `[mul_div_assoc']; rw [div_le_iff₀ (by positivity)]; nlinarith`. Combine the linear equalities and inequalities to obtain the conclusion. Use `push_cast`. Use polynomial arithmetic with `[Nat.cast_nonneg (α := ℝ) r]`.
-/
theorem deg_le_rank_mul_of_linesLE : ∀ (r : ℕ) (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F → ∀ g : Place k F → Matrix (Fin r) (Fin r) F, admitted g → ∀ b : ℝ, LinesLE g b → (deg g : ℝ) ≤ r * b := by
  intro r
  induction r with
  | zero =>
    intro k F _ _ _ _ _ _ g _ b _
    have : deg g = 0 := by simp [deg, ord, Matrix.det_isEmpty]
    simp [this]
  | succ r ih =>
    intro k F _ _ _ _ _ hF g hg b hb

    set S : Set ℝ := {c | LinesLE g c} with hS
    have hbS : b ∈ S := hb

    have hbdd : BddBelow S := by
      refine ⟨(degLine (pullAd (id : Place k F → Place k F) g) (Pi.single 0 1) : ℝ), ?_⟩
      intro c hc
      have hres : IsRes (k := k) (F := F) (E := F) (id : Place k F → Place k F) := by
        intro p x; rfl
      have h1 := hc F id hres (Pi.single 0 1) (by
        intro h; have := congrFun h 0; simp at this)
      simpa [Module.finrank_self] using h1
    set a := sInf S with ha
    have hab : a ≤ b := csInf_le hbdd hbS
    have haS : LinesLE g a := by
      intro E _ _ _ _ _ ρ hρ w hw
      have hn : (0 : ℝ) < Module.finrank F E := by exact_mod_cast Module.finrank_pos
      have : (degLine (pullAd ρ g) w : ℝ) / Module.finrank F E ≤ a := by
        refine le_csInf ⟨b, hbS⟩ ?_
        intro c hc
        rw [div_le_iff₀ hn]
        exact hc E ρ hρ w hw
      rwa [div_le_iff₀ hn] at this
    have key : ∀ ε : ℝ, 0 < ε → (deg g : ℝ) ≤ (r + 1) * a + r * ε := by
      intro ε hε
      have hnot : ¬ LinesLE g (a - ε) := fun h => by
        have := csInf_le hbdd (show a - ε ∈ S from h); linarith
      simp only [LinesLE, not_forall, not_le] at hnot
      obtain ⟨E, _, _, _, _, _, ρ, hρ, x, hx, hlt⟩ := hnot
      have hn : (0 : ℝ) < Module.finrank F E := by exact_mod_cast Module.finrank_pos
      obtain ⟨hGadm, hGdeg, -, hGlines⟩ := GlobalTheory.T.isAdmissibleAdelicMatrixFamily_pullback_extension k F E hF ρ hρ (r + 1) g hg
      have hE : IsFF k E := (GlobalTheory.T.functionFieldOneVariable_transcendental_finite_and_ext k F hF).2 E
      have hLG : LinesLE (pullAd ρ g) (a * Module.finrank F E) := hGlines a haS
      have hδle : (degLine (pullAd ρ g) x : ℝ) ≤ a * Module.finrank F E := haS E ρ hρ x hx
      obtain ⟨h, u, -, -, hzero, hadm', hadmq, hdeg, hsum, hlines⟩ :=
        GlobalTheory.T.iwasawa_decomposition_admissible_family k E hE r (pullAd ρ g) hGadm x hx
      have hLq := GlobalTheory.T.quotient_line_degree_le_of_triangular_family k E hE r (fun v => u v * pullAd ρ g v * h) hadm' hzero hadmq
        (a * Module.finrank F E) (hlines _ hLG)
      rw [hsum] at hLq
      have hq := ih k E hE _ hadmq _ hLq
      have hdegZ : (Module.finrank F E : ℤ) * deg g =
          degLine (pullAd ρ g) x + deg (fun v => (u v * pullAd ρ g v * h).submatrix Fin.succ Fin.succ) := by
        rw [← hGdeg, hdeg]
      have hdegR : (Module.finrank F E : ℝ) * (deg g : ℝ) =
          (degLine (pullAd ρ g) x : ℝ) + (deg (fun v => (u v * pullAd ρ g v * h).submatrix Fin.succ Fin.succ) : ℝ) := by
        exact_mod_cast hdegZ
      set n : ℝ := (Module.finrank F E : ℝ)
      set δ : ℝ := (degLine (pullAd ρ g) x : ℝ)
      have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
      have h2 : (r : ℝ) * (a * n - δ) ≤ r * (ε * n) := by
        apply mul_le_mul_of_nonneg_left _ hr; nlinarith
      have h3 : n * (deg g : ℝ) ≤ n * ((r + 1) * a + r * ε) := by nlinarith
      exact le_of_mul_le_mul_left h3 hn
    have hfin : (deg g : ℝ) ≤ (r + 1) * a := by
      refine le_of_forall_pos_le_add fun ε hε => ?_
      have := key (ε / (r + 1)) (by positivity)
      have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
      have : (r : ℝ) * (ε / (r + 1)) ≤ ε := by
        rw [mul_div_assoc']; rw [div_le_iff₀ (by positivity)]; nlinarith
      linarith
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) r]

end GlobalTheory.Nef
