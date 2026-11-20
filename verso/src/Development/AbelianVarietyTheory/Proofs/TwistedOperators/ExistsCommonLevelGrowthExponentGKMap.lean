import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.KTypeExtension
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemKFinOfMemLowT
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSmoothCuspFormFrechetModerateGrowthRepStatement
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KFiniteLeOfGKStableDiscreteSeriesModelStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModerateGrowthSobolevSizeRightTranslatePolyBound
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsKFinDRep
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ConjAtFixedIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
open Classical Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GKUnif

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

def Good (θ : InfFam D) (V : HSp D) (U : Subgroup (GA D V)) (N : ℕ) (φ : GA D V → ℂ) : Prop :=
  (∀ k ∈ U, k ∈ GfC V → ∀ g, φ (g * k) = φ g) ∧ ∀ d, GlobalTheory.Size.growthSob θ V d N φ ≠ ⊤

variable {θ : InfFam D} {U : Subgroup (GA D V)} {N : ℕ} {φ ψ : GA D V → ℂ}

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun k hk hk' g => by simp only [Pi.add_apply, h.1 k hk hk' g, h'.1 k hk hk' g], fun d => ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨h.2 d, h'.2 d⟩) (GlobalTheory.Size.growthSob_add_le hs hs' d N)⟩`.
-/
theorem good_add (hs : φ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V) (hs' : ψ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V)
    (h : Good θ V U N φ) (h' : Good θ V U N ψ) : Good θ V U N (φ + ψ) :=
  ⟨fun k hk hk' g => by simp only [Pi.add_apply, h.1 k hk hk' g, h'.1 k hk hk' g],
    fun d => ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨h.2 d, h'.2 d⟩) (GlobalTheory.Size.growthSob_add_le hs hs' d N)⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun k hk hk' g => by simp only [Pi.smul_apply, h.1 k hk hk' g], fun d => by rw [GlobalTheory.Size.growthSob_smul]; exact ENNReal.mul_ne_top enorm_ne_top (h.2 d)⟩`.
-/
theorem good_smul (c : ℂ) (h : Good θ V U N φ) : Good θ V U N (c • φ) :=
  ⟨fun k hk hk' g => by simp only [Pi.smul_apply, h.1 k hk hk' g],
    fun d => by rw [GlobalTheory.Size.growthSob_smul]; exact ENNReal.mul_ne_top enorm_ne_top (h.2 d)⟩

/- English proof (translation)
Establish `h` using `good_smul (θ := θ) (U := U) (N := N) (φ := 0) 0`. Rewrite `h` using `[zero_smul]`. Use `h ⟨fun _ _ _ _ => rfl, fun d => ?_⟩` and prove the remaining obligations. Establish `e` using `GlobalTheory.Size.growthSob_smul (θ := θ) (V := V) (φ := 0) 0 d N`. Rewrite `e` using `[zero_smul, enorm_zero, zero_mul]`.

Rewrite using `[e]`. Conclude with `ENNReal.zero_ne_top`.
-/
theorem good_zero : Good θ V U N 0 := by
  have h := good_smul (θ := θ) (U := U) (N := N) (φ := 0) 0
  rw [zero_smul] at h
  refine h ⟨fun _ _ _ _ => rfl, fun d => ?_⟩
  have e := GlobalTheory.Size.growthSob_smul (θ := θ) (V := V) (φ := 0) 0 d N
  rw [zero_smul, enorm_zero, zero_mul] at e
  rw [e]; exact ENNReal.zero_ne_top

/- English proof (translation)
Use `⟨fun k hk hk' g => ?_, fun d => ?_⟩` and prove the remaining obligations. Establish `e : rTr V k φ = φ` using `funext (h.1 k hk hk')`. Use `congrFun (GlobalTheory.Size.Rder_rTr_fin (θ := θ) hk' τ X φ) g` as an intermediate fact. Rewrite `this` using `[e]`. Conclude with `this.symm`.

Rewrite using `[← GlobalTheory.SmoothAutCheck.RderC_eq θ V τ hX φ]`. Establish `hB : ∀ a b, ‖X a b‖ₑ ≤ ∑ a', ∑ b', ‖X a' b'‖ₑ` using `fun a b => (Finset.single_le_sum (f := fun b' => ‖X a b'‖ₑ) (fun _ _ => zero_le) (Finset.mem_univ b)).trans (Finset.single_le_sum (f := fun a' => ∑ b', ‖X a' b'‖ₑ) (fun _ _ => zero_le) (Finset.mem_univ a))`. Use `ne_top_of_le_ne_top ?_ (GlobalTheory.Size.Translate.growthSob_RderC_le hθ hs τ hB d N)` and prove the remaining obligations. Use `ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.mul_ne_top ?_ (h.2 (d + 1)))` and prove the remaining obligations. Conclude with `ENNReal.sum_ne_top.2 fun _ _ => ENNReal.sum_ne_top.2 fun _ _ => enorm_ne_top`.
-/
theorem good_Rder (hθ : IsInfFam θ) (hs : φ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V) {τ : D.what₂.Tau}
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) (h : Good θ V U N φ) :
    Good θ V U N (Rder θ V τ X φ) := by
  refine ⟨fun k hk hk' g => ?_, fun d => ?_⟩
  · have e : rTr V k φ = φ := funext (h.1 k hk hk')
    have := congrFun (GlobalTheory.Size.Rder_rTr_fin (θ := θ) hk' τ X φ) g
    rw [e] at this
    exact this.symm
  · rw [← GlobalTheory.SmoothAutCheck.RderC_eq θ V τ hX φ]
    have hB : ∀ a b, ‖X a b‖ₑ ≤ ∑ a', ∑ b', ‖X a' b'‖ₑ := fun a b =>
      (Finset.single_le_sum (f := fun b' => ‖X a b'‖ₑ) (fun _ _ => zero_le) (Finset.mem_univ b)).trans
        (Finset.single_le_sum (f := fun a' => ∑ b', ‖X a' b'‖ₑ) (fun _ _ => zero_le) (Finset.mem_univ a))
    refine ne_top_of_le_ne_top ?_ (GlobalTheory.Size.Translate.growthSob_RderC_le hθ hs τ hB d N)
    refine ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.mul_ne_top ?_ (h.2 (d + 1)))
    exact ENNReal.sum_ne_top.2 fun _ _ => ENNReal.sum_ne_top.2 fun _ _ => enorm_ne_top

/- English proof (translation)
Use `⟨fun k hk hk' g => ?_, fun d => ?_⟩` and prove the remaining obligations. Use `show φ (g * k * h) = φ (g * h)`. Rewrite using `[mul_assoc, ← GlobalTheory.PointAtPlaceHom.comm_of_mem V hh hk', ← mul_assoc, hg.1 k hk hk']`. Take `⟨C, m, hC⟩` from `GlobalTheory.Size.Translate.growthSob_rTr_le D θ hθ V d N`. Conclude with `ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top) (hg.2 d)) (hC h hh φ hs)`.
-/
theorem good_rTr (hθ : IsInfFam θ) (hs : φ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V) {h : GA D V} (hh : h ∈ GinfC V)
    (hg : Good θ V U N φ) : Good θ V U N (rTr V h φ) := by
  refine ⟨fun k hk hk' g => ?_, fun d => ?_⟩
  · show φ (g * k * h) = φ (g * h)
    rw [mul_assoc, ← GlobalTheory.PointAtPlaceHom.comm_of_mem V hh hk', ← mul_assoc, hg.1 k hk hk']
  · obtain ⟨C, m, hC⟩ := GlobalTheory.Size.Translate.growthSob_rTr_le D θ hθ V d N
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top)
      (hg.2 d)) (hC h hh φ hs)

/- English proof (translation)
Establish `hX' : Xᴴ * gramAt D V τ + gramAt D V τ * X = 0` using `hX`. Rewrite `hX'` using `[← M.fr_gram τ]`. Establish `hd` using `(Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)`. Establish `h2 : M.fr τ * (M.fr τ)⁻¹ = 1` using `Matrix.mul_nonsing_inv _ hd`. Establish `hc : ∀ Y : Matrix (Fin V.rank) (Fin V.rank) ℂ, ((M.fr τ)⁻¹)ᴴ * ((M.fr τ)ᴴ * Y) = Y` using `fun Y => by`.

Rewrite using `[← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hd, Matrix.conjTranspose_one, Matrix.one_mul]`. Use `show (M.fr τ * X * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) + Formalism.REAL.Jm (M.ε τ) * (M.fr τ * X * (M.fr τ)⁻¹) = 0`. Establish `e : (M.fr τ * X * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) + Formalism.REAL.Jm (M.ε τ) * (M.fr τ * X * (M.fr τ)⁻¹) = ((M.fr τ)⁻¹)ᴴ * (Xᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) + (M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ * X) * (M.fr τ)⁻¹`. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, h2, Matrix.mul_one, hc]`. Rewrite using `[e, hX', Matrix.mul_zero, Matrix.zero_mul]`.
-/
theorem conj_mem_lieSet (M : DSModel V S) (τ : D.what₂.Tau) {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) : M.fr τ * X * (M.fr τ)⁻¹ ∈ GlobalTheory.SmoothGlob.lieSet (M.ε τ) := by
  have hX' : Xᴴ * gramAt D V τ + gramAt D V τ * X = 0 := hX
  rw [← M.fr_gram τ] at hX'
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have h2 : M.fr τ * (M.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  have hc : ∀ Y : Matrix (Fin V.rank) (Fin V.rank) ℂ, ((M.fr τ)⁻¹)ᴴ * ((M.fr τ)ᴴ * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hd, Matrix.conjTranspose_one,
      Matrix.one_mul]
  show (M.fr τ * X * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) + Formalism.REAL.Jm (M.ε τ) * (M.fr τ * X * (M.fr τ)⁻¹) = 0
  have e : (M.fr τ * X * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) + Formalism.REAL.Jm (M.ε τ) * (M.fr τ * X * (M.fr τ)⁻¹) =
      ((M.fr τ)⁻¹)ᴴ * (Xᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) +
        (M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ * X) * (M.fr τ)⁻¹ := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, h2, Matrix.mul_one, hc]
  rw [e, hX', Matrix.mul_zero, Matrix.zero_mul]

/- English proof (translation)
Use `haveI : CompleteSpace (M.H τ) := (M.ds τ).1`. Establish `hstd` using `GlobalTheory.TypeSum.std_of_isDS hHC (M.ds τ)`. Establish `hd : dRep (M.rep τ) X w = dRep (M.σ τ) (M.fr τ * X * (M.fr τ)⁻¹) w`. Unfold `dRep`. Use `congr 1`.

Use function extensionality and compare the values at `t`. Use `show M.σ τ (M.fr τ * NormedSpace.exp (t • X) * (M.fr τ)⁻¹) w = _`. Rewrite using `[← Matrix.exp_conj _ _ (M.fr_unit τ), Matrix.mul_smul, Matrix.smul_mul]`. Rewrite using `[hd]`. Conclude with `GlobalTheory.TypeSum.isKFin_dRep _ _ _ _ hstd w hw _ (conj_mem_lieSet M τ hX)`.
-/
theorem dRep_mem_kFin (hHC : GlobalTheory.Published.HarishChandraModules) (M : DSModel V S) (τ : D.what₂.Tau)
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) {w : M.H τ}
    (hw : w ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) : dRep (M.rep τ) X w ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ := by
  haveI : CompleteSpace (M.H τ) := (M.ds τ).1
  have hstd := GlobalTheory.TypeSum.std_of_isDS hHC (M.ds τ)
  have hd : dRep (M.rep τ) X w = dRep (M.σ τ) (M.fr τ * X * (M.fr τ)⁻¹) w := by
    unfold dRep
    congr 1
    funext t
    show M.σ τ (M.fr τ * NormedSpace.exp (t • X) * (M.fr τ)⁻¹) w = _
    rw [← Matrix.exp_conj _ _ (M.fr_unit τ), Matrix.mul_smul, Matrix.smul_mul]
  rw [hd]
  exact GlobalTheory.TypeSum.isKFin_dRep _ _ _ _ hstd w hw _ (conj_mem_lieSet M τ hX)

end GlobalTheory.GKUnif

namespace GlobalTheory.GKUnif

/- English proof (translation)
Introduce `hHC D θ hθ V S M J χ μ 𝓕 T₀ hT₀`. Establish `hne : ∀ τ, ∃ w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, w ≠ 0` using `fun τ => by`. Take `⟨x, hx, hx0⟩` from `(Submodule.ne_bot_iff _).1 (GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin_ne_bot M τ)`. Conclude with `⟨⟨x, hx⟩, fun h => hx0 (congrArg Subtype.val h)⟩`. Use `choose u₀ hu₀ using hne`.

Take `⟨U, hU, hUl⟩` from `(hT₀.1 u₀).level`. Take `⟨N, hN⟩` from `GlobalTheory.Size.exists_growthSob_ne_top (hT₀.2.1 u₀) (hT₀.2.2.2.2.1 u₀)`. Establish `hsm : ∀ u, T₀ u ∈ GlobalTheory.Mem.AutSpace.SmFun θ V` using `hT₀.2.1`. It suffices to establish `key : ∀ s : Finset D.what₂.Tau, ∀ u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M, (∀ τ ∉ s, u τ = u₀ τ) → Good θ V U N (T₀ u) from ⟨U, N, hU, fun u => key Finset.univ u (fun τ h => absurd (Finset.mem_univ τ) h)⟩`. Introduce `s`.

Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Introduce `u hu`. Establish `: u = u₀` using `funext fun τ => hu τ (Finset.notMem_empty τ)`. Substitute `this` using the available equality.

Conclude with `⟨hUl, hN⟩`. Consider the case `insert τ s hτ ih`. Introduce `u hu`. Set `Wk : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ)` to `{ carrier := {w | Good θ V U N (T₀ (Function.update u τ w))} add_mem' := fun {a b} ha hb => by show Good θ V U N (T₀ (Function.update u τ (a + b)))`. Rewrite using `[T₀.map_update_add]`.

Conclude with `good_add (hsm _) (hsm _) ha hb`. Use the proof step `zero_mem' := by show Good θ V U N (T₀ (Function.update u τ 0))`. Rewrite using `[T₀.map_update_zero]`. Conclude with `good_zero`. Use the proof step `smul_mem' := fun c a ha => by show Good θ V U N (T₀ (Function.update u τ (c • a)))`.

Rewrite using `[T₀.map_update_smul]`. Conclude with `good_smul c ha }`. Set `W : Submodule ℂ (M.H τ)` to `Wk.map (GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ).subtype`. Establish `hmemW : ∀ y : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, y ∈ Wk → (y : M.H τ) ∈ W` using `fun y hy => ⟨y, hy, rfl⟩`. Establish `hWk : ∀ w ∈ W, ∃ y : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, y ∈ Wk ∧ (y : M.H τ) = w`.

Introduce and unpack `w ⟨y, hy, rfl⟩`. Conclude with `⟨y, hy, rfl⟩`. Establish `hle : W ≤ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ` using `Submodule.map_subtype_le _ _`. Establish `hlie : ∀ X ∈ lieAt V τ, ∀ w ∈ W, dRep (M.rep τ) X w ∈ W`. Introduce `X hX w hw`.

Take `⟨y, hy, rfl⟩` from `hWk w hw`. Set `y' : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ` to `⟨dRep (M.rep τ) X y, dRep_mem_kFin hHC M τ hX y.2⟩`. Use `hmemW y' ?_` and prove the remaining obligations. Establish `e` using `hT₀.2.2.2.2.2.2.2 τ X hX (Function.update u τ y) y' (by simp [y'])`. Rewrite `e` using `[Function.update_idem]`.

Use `show Good θ V U N (T₀ (Function.update u τ y'))`. Rewrite using `[e]`. Conclude with `good_Rder hθ (hsm _) hX hy`. Establish `hK : ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt M τ, ∀ w ∈ W, M.rep τ k w ∈ W`. Introduce `k hk w hw`.

Take `⟨y, hy, rfl⟩` from `hWk w hw`. Set `y' : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ` to `⟨M.rep τ k y, GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.rep_mem_kFin M τ hk y.2⟩`. Use `hmemW y' ?_` and prove the remaining obligations. Establish `e` using `hT₀.2.2.2.2.2.2.1 τ k hk (Function.update u τ y) y' (by simp [y'])`. Rewrite `e` using `[Function.update_idem]`.

Use `show Good θ V U N (T₀ (Function.update u τ y'))`. Rewrite using `[e]`. Conclude with `good_rTr hθ (hsm _) (GlobalTheory.PointAtPlaceHom.atTau_mem V τ k) hy`. Establish `h0 : u₀ τ ∈ Wk` using `by show Good θ V U N (T₀ (Function.update u τ (u₀ τ)))`. Use `ih _ fun τ' h' => ?_` and prove the remaining obligations.

Distinguish the cases in `e : τ' = τ`. Substitute `e` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[Function.update_of_ne e]`. Conclude with `hu τ' (by simp [e, h'])`.

Establish `hWne : W ≠ ⊥` using `fun hb => hu₀ τ (Subtype.ext (by`. Use `hmemW _ h0` as an intermediate fact. Rewrite `this` using `[hb]`. Simplify using `using this))`. Establish `hall` using `GlobalTheory.T.kFinite_le_of_gKStable_discreteSeriesModel hHC D V S M τ W hle hlie hK hWne`.

Take `⟨y, hy, hyu⟩` from `hWk _ (hall (u τ).2)`. Establish `: y = u τ` using `Subtype.ext hyu`. Substitute `this` using the available equality. Establish `e : Function.update u τ (u τ) = u` using `Function.update_eq_self τ u`. Establish `hy' : Good θ V U N (T₀ (Function.update u τ (u τ)))` using `hy`.

Rewrite `hy'` using `[e]`. Then use the resulting hypothesis.
-/
theorem exists_level_exponent : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (θ : InfFam D), IsInfFam θ →
    ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (μ : Measure (GA D V))
    (𝓕 : Set (GA D V)) (T₀ : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KMap M), GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.IsGKMap θ M J χ μ 𝓕 T₀ →
    ∃ (U : Subgroup (GA D V)) (N : ℕ), IsOpen (U : Set (GA D V)) ∧
      ∀ u, (∀ k ∈ U, k ∈ GfC V → ∀ g, T₀ u (g * k) = T₀ u g) ∧ ∀ d, GlobalTheory.Size.growthSob θ V d N (T₀ u) ≠ ⊤ := by
  intro hHC D θ hθ V S M J χ μ 𝓕 T₀ hT₀
  have hne : ∀ τ, ∃ w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, w ≠ 0 := fun τ => by
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 (GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin_ne_bot M τ)
    exact ⟨⟨x, hx⟩, fun h => hx0 (congrArg Subtype.val h)⟩
  choose u₀ hu₀ using hne
  obtain ⟨U, hU, hUl⟩ := (hT₀.1 u₀).level
  obtain ⟨N, hN⟩ := GlobalTheory.Size.exists_growthSob_ne_top (hT₀.2.1 u₀) (hT₀.2.2.2.2.1 u₀)
  have hsm : ∀ u, T₀ u ∈ GlobalTheory.Mem.AutSpace.SmFun θ V := hT₀.2.1
  suffices key : ∀ s : Finset D.what₂.Tau, ∀ u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M, (∀ τ ∉ s, u τ = u₀ τ) →
      Good θ V U N (T₀ u) from
    ⟨U, N, hU, fun u => key Finset.univ u (fun τ h => absurd (Finset.mem_univ τ) h)⟩
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro u hu
    have : u = u₀ := funext fun τ => hu τ (Finset.notMem_empty τ)
    subst this
    exact ⟨hUl, hN⟩
  | insert τ s hτ ih =>
    intro u hu
    let Wk : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) :=
      { carrier := {w | Good θ V U N (T₀ (Function.update u τ w))}
        add_mem' := fun {a b} ha hb => by
          show Good θ V U N (T₀ (Function.update u τ (a + b)))
          rw [T₀.map_update_add]
          exact good_add (hsm _) (hsm _) ha hb
        zero_mem' := by
          show Good θ V U N (T₀ (Function.update u τ 0))
          rw [T₀.map_update_zero]
          exact good_zero
        smul_mem' := fun c a ha => by
          show Good θ V U N (T₀ (Function.update u τ (c • a)))
          rw [T₀.map_update_smul]
          exact good_smul c ha }
    let W : Submodule ℂ (M.H τ) := Wk.map (GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ).subtype
    have hmemW : ∀ y : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, y ∈ Wk → (y : M.H τ) ∈ W := fun y hy => ⟨y, hy, rfl⟩
    have hWk : ∀ w ∈ W, ∃ y : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, y ∈ Wk ∧ (y : M.H τ) = w := by
      rintro w ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
    have hle : W ≤ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ := Submodule.map_subtype_le _ _
    have hlie : ∀ X ∈ lieAt V τ, ∀ w ∈ W, dRep (M.rep τ) X w ∈ W := by
      intro X hX w hw
      obtain ⟨y, hy, rfl⟩ := hWk w hw
      let y' : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ := ⟨dRep (M.rep τ) X y, dRep_mem_kFin hHC M τ hX y.2⟩
      refine hmemW y' ?_
      have e := hT₀.2.2.2.2.2.2.2 τ X hX (Function.update u τ y) y' (by simp [y'])
      rw [Function.update_idem] at e
      show Good θ V U N (T₀ (Function.update u τ y'))
      rw [e]
      exact good_Rder hθ (hsm _) hX hy
    have hK : ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt M τ, ∀ w ∈ W, M.rep τ k w ∈ W := by
      intro k hk w hw
      obtain ⟨y, hy, rfl⟩ := hWk w hw
      let y' : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ := ⟨M.rep τ k y, GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.rep_mem_kFin M τ hk y.2⟩
      refine hmemW y' ?_
      have e := hT₀.2.2.2.2.2.2.1 τ k hk (Function.update u τ y) y' (by simp [y'])
      rw [Function.update_idem] at e
      show Good θ V U N (T₀ (Function.update u τ y'))
      rw [e]
      exact good_rTr hθ (hsm _) (GlobalTheory.PointAtPlaceHom.atTau_mem V τ k) hy
    have h0 : u₀ τ ∈ Wk := by
      show Good θ V U N (T₀ (Function.update u τ (u₀ τ)))
      refine ih _ fun τ' h' => ?_
      by_cases e : τ' = τ
      · subst e; simp
      · rw [Function.update_of_ne e]
        exact hu τ' (by simp [e, h'])
    have hWne : W ≠ ⊥ := fun hb => hu₀ τ (Subtype.ext (by
      have := hmemW _ h0
      rw [hb] at this
      simpa using this))
    have hall := GlobalTheory.T.kFinite_le_of_gKStable_discreteSeriesModel hHC D V S M τ W hle hlie hK hWne
    obtain ⟨y, hy, hyu⟩ := hWk _ (hall (u τ).2)
    have : y = u τ := Subtype.ext hyu
    subst this
    have e : Function.update u τ (u τ) = u := Function.update_eq_self τ u
    have hy' : Good θ V U N (T₀ (Function.update u τ (u τ))) := hy
    rwa [e] at hy'

end GlobalTheory.GKUnif

end
