import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open Filter Topology

noncomputable section
namespace GlobalTheory.RootEx

/- English proof (translation)
Take `⟨h1, h2⟩` from `hG`. Prove the components needed by the constructor for the conclusion. Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `x₀`. Establish `hK : IsCompact (Prod.snd '' tsupport G)` using `h2.isCompact.image continuous_snd`.

Establish `h` using `hK.eventually_forall_of_forall_eventually (x₀ := x₀) (P := fun x y => G (x, y) = G (x₀, y)) (by`. Introduce `y _`. Establish `ha` using `h1.eventually_eq (x₀, y)`. Establish `hc : Continuous fun z : X × E => ((x₀, z.2) : X × E)` using `by fun_prop`. Establish `hb` using `(h1.comp_continuous hc).eventually_eq (x₀, y)`.

Use `filter_upwards [ha, hb] with z hz hz'`. Conclude with `hz.trans hz'.symm)`. Use `filter_upwards [h] with x hx`. Use `congr 1`. Use function extensionality and compare the values at `e`.

Distinguish the cases in `he : e ∈ Prod.snd '' tsupport G`. Rewrite using `[hx e he]`. Establish `: ∀ x', G (x', e) = 0` using `fun x' => image_eq_zero_of_notMem_tsupport fun h' => he ⟨_, h', rfl⟩`. Rewrite using `[this, this]`. Use `HasCompactSupport.intro (h2.isCompact.image continuous_fst) fun x hx => ?_` and prove the remaining obligations.

Establish `: ∀ e, G (x, e) = 0` using `fun e => image_eq_zero_of_notMem_tsupport fun h' => hx ⟨_, h', rfl⟩`. Simplify using `[this]`.
-/
theorem integral_mul_mem_SB {X E : Type*} [TopologicalSpace X] [TopologicalSpace E] [R1Space X]
    [MeasurableSpace E] (μ : Measure E) (G : X × E → ℂ) (hG : G ∈ SB (X × E)) (χ : E → ℂ) :
    (fun x => ∫ e, G (x, e) * χ e ∂μ) ∈ SB X := by
  obtain ⟨h1, h2⟩ := hG
  constructor
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x₀
    have hK : IsCompact (Prod.snd '' tsupport G) := h2.isCompact.image continuous_snd
    have h := hK.eventually_forall_of_forall_eventually (x₀ := x₀)
      (P := fun x y => G (x, y) = G (x₀, y)) (by
        intro y _
        have ha := h1.eventually_eq (x₀, y)
        have hc : Continuous fun z : X × E => ((x₀, z.2) : X × E) := by fun_prop
        have hb := (h1.comp_continuous hc).eventually_eq (x₀, y)
        filter_upwards [ha, hb] with z hz hz'
        exact hz.trans hz'.symm)
    filter_upwards [h] with x hx
    congr 1
    funext e
    by_cases he : e ∈ Prod.snd '' tsupport G
    · rw [hx e he]
    · have : ∀ x', G (x', e) = 0 := fun x' =>
        image_eq_zero_of_notMem_tsupport fun h' => he ⟨_, h', rfl⟩
      rw [this, this]
  · refine HasCompactSupport.intro (h2.isCompact.image continuous_fst) fun x hx => ?_
    have : ∀ e, G (x, e) = 0 := fun e =>
      image_eq_zero_of_notMem_tsupport fun h' => hx ⟨_, h', rfl⟩
    simp [this]

section
variable {k : Type*} [Field k] {n n' : Type*} {c : ℕ}

/- English proof (translation)
Take `⟨⟨r, s⟩, h⟩` from `rs`. Simplify using `only [affPt, Matrix.add_apply, Matrix.of_apply, dif_pos h]`. Use `congr 1`. Apply the tactic sequence `rcases r with r | r <;> rcases s with s | s`. Conclude with `h.elim`.

Apply the tactic sequence `all_goals rfl`.
-/
theorem affPt_of_free (p : ℕ) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k)
    (rs : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs}) :
    affPt p x₀ e rs.1.1 rs.1.2 = basePt c (0 : Matrix n n' k) rs.1.1 rs.1.2 + e rs := by
  obtain ⟨⟨r, s⟩, h⟩ := rs
  simp only [affPt, Matrix.add_apply, Matrix.of_apply, dif_pos h]
  congr 1
  rcases r with r | r <;> rcases s with s | s
  · exact h.elim
  all_goals rfl

/- English proof (translation)
Simplify using `[affPt, basePt, Free]`.
-/
theorem affPt_inl_inl (p : ℕ) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) (r : n) (s : n') :
    affPt p x₀ e (Sum.inl r) (Sum.inl s) = x₀ r s := by
  simp [affPt, basePt, Free]

variable [TopologicalSpace k] [IsTopologicalRing k]

/- English proof (translation)
Use `continuous_matrix fun r s => ?_` and prove the remaining obligations. Distinguish the cases in `h : Free p (r, s)`. Use `fun z : Matrix n n' k × ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) => affPt_of_free p z.1 z.2 ⟨(r, s), h⟩` as an intermediate fact. Simplify using `only at this`. Simplify using `only [this]`.

Use `fun_prop`. Simplify using `only [affPt, Matrix.add_apply, Matrix.of_apply, dif_neg h, add_zero]`. Apply the tactic sequence `rcases r with r | r <;> rcases s with s | s`. Conclude with `continuous_fst.matrix_elem r s`. Apply the tactic sequence `all_goals exact continuous_const`.
-/
theorem continuous_affPt_uncurry (p : ℕ) :
    Continuous fun z : Matrix n n' k × ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) =>
      affPt p z.1 z.2 := by
  refine continuous_matrix fun r s => ?_
  by_cases h : Free p (r, s)
  · have := fun z : Matrix n n' k × ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) =>
      affPt_of_free p z.1 z.2 ⟨(r, s), h⟩
    simp only at this
    simp only [this]
    fun_prop
  · simp only [affPt, Matrix.add_apply, Matrix.of_apply, dif_neg h, add_zero]
    rcases r with r | r <;> rcases s with s | s
    · exact continuous_fst.matrix_elem r s
    all_goals exact continuous_const

/- English proof (translation)
Use `Function.LeftInverse.isClosedEmbedding (f := fun M : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k => ((Matrix.of fun r s => M (Sum.inl r) (Sum.inl s) : Matrix n n' k), fun rs : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} => M rs.1.1 rs.1.2 - basePt c (0 : Matrix n n' k) rs.1. …` and prove the remaining obligations. Introduce and unpack `⟨x, e⟩`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use extensionality with `r s`. Simplify using `[affPt_inl_inl]`.

Use function extensionality and compare the values at `rs`. Simplify using `[affPt_of_free]`. Use `Continuous.prodMk (continuous_matrix fun r s => continuous_id.matrix_elem _ _) ?_` and prove the remaining obligations. Conclude with `continuous_pi fun rs => (continuous_id.matrix_elem _ _).sub continuous_const`.
-/
theorem isClosedEmbedding_affPt_uncurry [T2Space k] (p : ℕ) :
    IsClosedEmbedding
      fun z : Matrix n n' k × ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) =>
        affPt p z.1 z.2 := by
  refine Function.LeftInverse.isClosedEmbedding
    (f := fun M : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k =>
      ((Matrix.of fun r s => M (Sum.inl r) (Sum.inl s) : Matrix n n' k),
        fun rs : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} =>
          M rs.1.1 rs.1.2 - basePt c (0 : Matrix n n' k) rs.1.1 rs.1.2)) ?_ ?_
    (continuous_affPt_uncurry p)
  · rintro ⟨x, e⟩
    refine Prod.ext ?_ ?_
    · ext r s
      simp [affPt_inl_inl]
    · funext rs
      simp [affPt_of_free]
  · refine Continuous.prodMk (continuous_matrix fun r s => continuous_id.matrix_elem _ _) ?_
    exact continuous_pi fun rs => (continuous_id.matrix_elem _ _).sub continuous_const

/- English proof (translation)
Assemble the required witnesses or components as `⟨hΦ.1.comp_continuous (continuous_affPt_uncurry p), hΦ.2.comp_isClosedEmbedding (isClosedEmbedding_affPt_uncurry p)⟩`.
-/
theorem comp_affPt_mem_SB [T2Space k] (p : ℕ) {Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ}
    (hΦ : Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) :
    (fun z : Matrix n n' k × ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) =>
        Φ (affPt p z.1 z.2)) ∈ SB _ :=
  ⟨hΦ.1.comp_continuous (continuous_affPt_uncurry p),
    hΦ.2.comp_isClosedEmbedding (isClosedEmbedding_affPt_uncurry p)⟩

end

section
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n n' : Type*} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {c : ℕ}

open Classical in

/- English proof (translation)
Use `haveI := GlobalTheory.SplitWeil.secondCountable k`. Use `haveI := GlobalTheory.SplitWeil.t2Space k`. Establish `hc : Continuous fun e => affPt (c` using `c) p x₀ e := (continuous_affPt_uncurry p).comp (Continuous.prodMk_right x₀)`. Use `Continuous.integrable_of_hasCompactSupport ?_ ?_` and prove the remaining obligations. Use `(hΦ.1.continuous.comp hc).mul (continuous_subtype_val.comp (hψ.comp (Continuous.neg ?_)))` and prove the remaining obligations.

Conclude with `continuous_finset_sum _ fun i _ => hc.matrix_elem _ _`. Use `HasCompactSupport.mul_right ?_` and prove the remaining obligations. Establish `h2` using `(comp_affPt_mem_SB p hΦ).2`. Use `HasCompactSupport.intro (h2.isCompact.image continuous_snd) fun e he => ?_` and prove the remaining obligations. Conclude with `image_eq_zero_of_notMem_tsupport (f := fun z : Matrix n n' k × ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) => Φ (affPt p z.1 z.2)) (x := (x₀, e)) fun h' => he ⟨_, h', rfl⟩`.
-/
theorem integrable_opE_integrand (p : ℕ) {ψ : AddChar k Circle} (hψ : Continuous ψ) (ν : Measure k)
    [ν.IsAddHaarMeasure] {Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ}
    (hΦ : Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (x₀ : Matrix n n' k) :
    Integrable (fun e => Φ (affPt p x₀ e) * (ψ (-ch (affPt p x₀ e)) : ℂ)) (Measure.pi fun _ => ν) := by
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := GlobalTheory.SplitWeil.t2Space k
  have hc : Continuous fun e => affPt (c := c) p x₀ e :=
    (continuous_affPt_uncurry p).comp (Continuous.prodMk_right x₀)
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · refine (hΦ.1.continuous.comp hc).mul (continuous_subtype_val.comp (hψ.comp (Continuous.neg ?_)))
    exact continuous_finset_sum _ fun i _ => hc.matrix_elem _ _
  · refine HasCompactSupport.mul_right ?_
    have h2 := (comp_affPt_mem_SB p hΦ).2
    refine HasCompactSupport.intro (h2.isCompact.image continuous_snd) fun e he => ?_
    exact image_eq_zero_of_notMem_tsupport
      (f := fun z : Matrix n n' k × ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) =>
        Φ (affPt p z.1 z.2)) (x := (x₀, e)) fun h' => he ⟨_, h', rfl⟩

omit [BorelSpace k] [DecidableEq n] [DecidableEq n'] in

/- English proof (translation)
Use `haveI := GlobalTheory.SplitWeil.t2Space k`. Conclude with `integral_mul_mem_SB _ _ (comp_affPt_mem_SB p hΦ) (fun e => (ψ (-ch (affPt p (0 : Matrix n n' k) e)) : ℂ))`.
-/
theorem opE_mem_SB (p : ℕ) (ψ : AddChar k Circle) (ν : Measure k)
    {Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ}
    (hΦ : Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) : opE ψ ν p Φ ∈ SB (Matrix n n' k) := by
  haveI := GlobalTheory.SplitWeil.t2Space k
  exact integral_mul_mem_SB _ _ (comp_affPt_mem_SB p hΦ)
    (fun e => (ψ (-ch (affPt p (0 : Matrix n n' k) e)) : ℂ))

/- English proof (translation)
Use function extensionality and compare the values at `x₀`. Establish `h1` using `(integrable_opE_integrand p hψ ν hΦ x₀).const_mul z`. Establish `h2` using `integrable_opE_integrand p hψ ν hΨ x₀`. Simplify using `only [opE, Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[← integral_const_mul, ← integral_add h1 h2]`.

Use `congr 1`. Use function extensionality and compare the values at `e`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem opE_smul_add (p : ℕ) {ψ : AddChar k Circle} (hψ : Continuous ψ) (ν : Measure k)
    [ν.IsAddHaarMeasure] (z : ℂ) {Φ Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ}
    (hΦ : Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k))
    (hΨ : Ψ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) :
    opE ψ ν p (z • Φ + Ψ) = z • opE ψ ν p Φ + opE ψ ν p Ψ := by
  funext x₀
  have h1 := (integrable_opE_integrand p hψ ν hΦ x₀).const_mul z
  have h2 := integrable_opE_integrand p hψ ν hΨ x₀
  simp only [opE, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul, ← integral_add h1 h2]
  congr 1
  funext e
  ring

end

/- English proof (translation)
Introduce `_ _ _ _ _ _ _ _ _ _ _ _ _ _ p ψ hψ ν _` and use `⟨fun _ hΦ => opE_mem_SB p ψ ν hΦ, fun z _ hΦ _ hΨ => opE_smul_add p hψ ν z hΦ hΨ⟩`.
-/
theorem opE_SB_and_linear : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (ψ : AddChar k Circle) (_ : Continuous ψ) (ν : Measure k) [ν.IsAddHaarMeasure], (∀ Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), opE ψ ν p Φ ∈ SB (Matrix n n' k)) ∧ ∀ (z : ℂ), ∀ Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), ∀ Ψ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), opE ψ ν p (z • Φ + Ψ) = z • opE ψ ν p Φ + opE ψ ν p Ψ :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ p ψ hψ ν _ =>
    ⟨fun _ hΦ => opE_mem_SB p ψ ν hΦ, fun z _ hΦ _ hΨ => opE_smul_add p hψ ν z hΦ hΨ⟩

end GlobalTheory.RootEx
