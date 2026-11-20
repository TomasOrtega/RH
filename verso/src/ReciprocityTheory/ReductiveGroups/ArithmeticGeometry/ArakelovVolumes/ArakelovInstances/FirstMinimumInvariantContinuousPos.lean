import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.PointwiseNormInvarianceHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ModeHalfStatementPfC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KaUnfoldPfA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajorantConjugateTransfer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MinimumGrowthBounds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowMajorantFlags
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlagSpanBounds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ModeHalfStatementPfB

namespace ReciprocityTheory.ChartRestriction.G.AR.Inst

open NumberField ReciprocityTheory.ChartRestriction.G.FD Matrix

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

/- English proof (translation)
Establish `hy` using `ReciprocityTheory.ChartRestriction.G.FD.OrthogonalFrameDomain.rmul_mem_dom X hx hb`. Establish `hf` using `ReciprocityTheory.ChartRestriction.G.FD.FlagSpanBounds.sameFlag_rmul X x hb`. Unfold `Data.firstMinimumSq`. Simplify using `only [ReciprocityTheory.ChartRestriction.G.FD.FlowMajorantFlags.maj_flag X hx hy hf]`.
-/
theorem firstMinimumSq_rightBorel (X : Data E r) {x b : Frame X.Ψ r} (hx : x ∈ X.dom) (hb : b ∈ Bor X.Ψ r) :
    X.firstMinimumSq (rmul x b) = X.firstMinimumSq x := by
  have hy := ReciprocityTheory.ChartRestriction.G.FD.OrthogonalFrameDomain.rmul_mem_dom X hx hb
  have hf := ReciprocityTheory.ChartRestriction.G.FD.FlagSpanBounds.sameFlag_rmul X x hb
  unfold Data.firstMinimumSq
  simp only [ReciprocityTheory.ChartRestriction.G.FD.FlowMajorantFlags.maj_flag X hx hy hf]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[Data.emb, mulVec, dotProduct, map_sum]`.
-/
theorem emb_mulVec (τ : E →+* ℂ) (M : Matrix (Fin r) (Fin r) E) (v : Fin r → E) :
    (M.map τ) *ᵥ Data.emb τ v = Data.emb τ (M *ᵥ v) := by
  funext i
  simp [Data.emb, mulVec, dotProduct, map_sum]

/- English proof (translation)
Establish `hy` using `ReciprocityTheory.ChartRestriction.G.AR.Up.KU.lact_dom X hγ hx`. Use `set g := (γ : Matrix (Fin r) (Fin r) E).map τ.1 with hg`. Use `set g' := ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 with hg'`. Establish `hgg' : ∀ w, g *ᵥ (g' *ᵥ w) = w`. Introduce `w`.

Rewrite using `[mulVec_mulVec, hg, hg', ← Matrix.map_mul, Units.mul_inv, Matrix.map_one τ.1 τ.1.map_zero τ.1.map_one, one_mulVec]`. Establish `hiso : ∀ u w, hermC τ.1 X.Gm (g *ᵥ u) (g *ᵥ w) = hermC τ.1 X.Gm u w` using `fun u w => ReciprocityTheory.ChartRestriction.G.FD.CompactEntryBounds.hermC_stab X (X.Γ_stab γ hγ).1 τ.1 u w`. Establish `hcol : ∀ c, X.colP (lact γ x) τ c = g *ᵥ X.colP x τ c`. Introduce `c`. Use function extensionality and compare the values at `i`.

Both sides reduce to the same expression. Establish `H1 : ∀ c, ∃ K : Fin X.p0 → ℂ, g *ᵥ X.colP x τ c = ∑ a, K a • X.colP (lact γ x) τ a`. Introduce `c`. Use `⟨Pi.single c 1, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single c (fun a _ ha => by rw [Pi.single_eq_of_ne ha, zero_smul]) (fun h => absurd (Finset.mem_univ c) h), Pi.single_eq_same, one_smul, hcol]`.

Establish `H2 : ∀ a, ∃ L : Fin X.p0 → ℂ, X.colP (lact γ x) τ a = ∑ c, L c • (g *ᵥ X.colP x τ c)`. Introduce `a`. Use `⟨Pi.single a 1, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single a (fun c _ hc => by rw [Pi.single_eq_of_ne hc, zero_smul]) (fun h => absurd (Finset.mem_univ a) h), Pi.single_eq_same, one_smul, hcol]`. Rewrite using `[ReciprocityTheory.ChartRestriction.G.FD.MajorantConjugateTransfer.maj_transfer X hx hy τ g g' hgg' hiso H1 H2, hg', emb_mulVec]`.
-/
theorem maj_lact (X : Data E r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (τ : X.Ψ) (v : Fin r → E) :
    X.maj (lact γ x) τ (Data.emb τ.1 v) =
      X.maj x τ (Data.emb τ.1 (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v)) := by
  have hy := ReciprocityTheory.ChartRestriction.G.AR.Up.KU.lact_dom X hγ hx
  set g := (γ : Matrix (Fin r) (Fin r) E).map τ.1 with hg
  set g' := ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 with hg'
  have hgg' : ∀ w, g *ᵥ (g' *ᵥ w) = w := by
    intro w
    rw [mulVec_mulVec, hg, hg', ← Matrix.map_mul, Units.mul_inv, Matrix.map_one τ.1 τ.1.map_zero τ.1.map_one,
      one_mulVec]
  have hiso : ∀ u w, hermC τ.1 X.Gm (g *ᵥ u) (g *ᵥ w) = hermC τ.1 X.Gm u w :=
    fun u w => ReciprocityTheory.ChartRestriction.G.FD.CompactEntryBounds.hermC_stab X (X.Γ_stab γ hγ).1 τ.1 u w
  have hcol : ∀ c, X.colP (lact γ x) τ c = g *ᵥ X.colP x τ c := by
    intro c
    funext i
    rfl
  have H1 : ∀ c, ∃ K : Fin X.p0 → ℂ, g *ᵥ X.colP x τ c = ∑ a, K a • X.colP (lact γ x) τ a := by
    intro c
    classical
    refine ⟨Pi.single c 1, ?_⟩
    rw [Finset.sum_eq_single c (fun a _ ha => by rw [Pi.single_eq_of_ne ha, zero_smul])
      (fun h => absurd (Finset.mem_univ c) h), Pi.single_eq_same, one_smul, hcol]
  have H2 : ∀ a, ∃ L : Fin X.p0 → ℂ, X.colP (lact γ x) τ a = ∑ c, L c • (g *ᵥ X.colP x τ c) := by
    intro a
    classical
    refine ⟨Pi.single a 1, ?_⟩
    rw [Finset.sum_eq_single a (fun c _ hc => by rw [Pi.single_eq_of_ne hc, zero_smul])
      (fun h => absurd (Finset.mem_univ a) h), Pi.single_eq_same, one_smul, hcol]
  rw [ReciprocityTheory.ChartRestriction.G.FD.MajorantConjugateTransfer.maj_transfer X hx hy τ g g' hgg' hiso H1 H2, hg', emb_mulVec]

/- English proof (translation)
Establish `hγi : γ⁻¹ ∈ X.Γ` using `X.Γ.inv_mem hγ`. Establish `hmem : ∀ (δ : GL (Fin r) E), δ ∈ X.Γ → ∀ v, v ∈ X.Λ → ((δ : Matrix (Fin r) (Fin r) E) *ᵥ v) ∈ X.Λ` using `fun δ hδ v hv => ((X.Γ_stab δ hδ).2 v).1 hv`. Establish `hinv1 : ∀ v : Fin r → E, ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) = v` using `fun v => by`. Rewrite using `[mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]`. Establish `hinv2 : ∀ v : Fin r → E, (γ : Matrix (Fin r) (Fin r) E) *ᵥ (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v) = v` using `fun v => by`.

Rewrite using `[mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]`. Establish `hS : {t | ∃ v ∈ X.Λ, v ≠ 0 ∧ t = ∑ τ, X.c τ * X.maj (lact γ x) τ (Data.emb τ.1 v)} = {t | ∃ v ∈ X.Λ, v ≠ 0 ∧ t = ∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 v)}`. Use extensionality with `t`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨v, hv, hv0, rfl⟩`.

Use `⟨((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v, hmem _ hγi v hv, ?_, ?_⟩` and prove the remaining obligations. Introduce `h0`. Apply `hv0` to reduce the goal to its premises. Rewrite using `[← hinv2 v, h0, mulVec_zero]`. Conclude with `Finset.sum_congr rfl fun τ _ => by rw [maj_lact X hγ hx]`.

Introduce and unpack `⟨v, hv, hv0, rfl⟩`. Use `⟨(γ : Matrix (Fin r) (Fin r) E) *ᵥ v, hmem _ hγ v hv, ?_, ?_⟩` and prove the remaining obligations. Introduce `h0`. Apply `hv0` to reduce the goal to its premises. Rewrite using `[← hinv1 v, h0, mulVec_zero]`.

Conclude with `Finset.sum_congr rfl fun τ _ => by rw [maj_lact X hγ hx, hinv1]`. Unfold `Data.firstMinimumSq`. Rewrite using `[hS]`.
-/
theorem firstMinimumSq_leftAction (X : Data E r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    X.firstMinimumSq (lact γ x) = X.firstMinimumSq x := by
  have hγi : γ⁻¹ ∈ X.Γ := X.Γ.inv_mem hγ
  have hmem : ∀ (δ : GL (Fin r) E), δ ∈ X.Γ → ∀ v, v ∈ X.Λ →
      ((δ : Matrix (Fin r) (Fin r) E) *ᵥ v) ∈ X.Λ := fun δ hδ v hv => ((X.Γ_stab δ hδ).2 v).1 hv
  have hinv1 : ∀ v : Fin r → E, ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ
      ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) = v := fun v => by
    rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  have hinv2 : ∀ v : Fin r → E, (γ : Matrix (Fin r) (Fin r) E) *ᵥ
      (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v) = v := fun v => by
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  have hS : {t | ∃ v ∈ X.Λ, v ≠ 0 ∧ t = ∑ τ, X.c τ * X.maj (lact γ x) τ (Data.emb τ.1 v)} =
      {t | ∃ v ∈ X.Λ, v ≠ 0 ∧ t = ∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 v)} := by
    ext t
    constructor
    · rintro ⟨v, hv, hv0, rfl⟩
      refine ⟨((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v, hmem _ hγi v hv, ?_, ?_⟩
      · intro h0
        apply hv0
        rw [← hinv2 v, h0, mulVec_zero]
      · exact Finset.sum_congr rfl fun τ _ => by rw [maj_lact X hγ hx]
    · rintro ⟨v, hv, hv0, rfl⟩
      refine ⟨(γ : Matrix (Fin r) (Fin r) E) *ᵥ v, hmem _ hγ v hv, ?_, ?_⟩
      · intro h0
        apply hv0
        rw [← hinv1 v, h0, mulVec_zero]
      · exact Finset.sum_congr rfl fun τ _ => by rw [maj_lact X hγ hx, hinv1]
  unfold Data.firstMinimumSq
  rw [hS]

/- English proof (translation)
Establish `hy` using `ReciprocityTheory.ChartRestriction.G.FD.OrthogonalFrameDomain.rmul_mem_dom X hx hb`. Unfold `Data.la1`. Rewrite using `[firstMinimumSq_leftAction X hγ hy, firstMinimumSq_rightBorel X hx hb]`.
-/
theorem firstMinimum_biinvariant (X : Data E r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) : X.la1 (lact γ (rmul x b)) = X.la1 x := by
  have hy := ReciprocityTheory.ChartRestriction.G.FD.OrthogonalFrameDomain.rmul_mem_dom X hx hb
  unfold Data.la1
  rw [firstMinimumSq_leftAction X hγ hy, firstMinimumSq_rightBorel X hx hb]

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push Not at h`. Establish `h1 : Submodule.span E (X.Λ : Set (Fin r → E)) = ⊥`. Rewrite using `[Submodule.span_eq_bot]`. Conclude with `h`.

Rewrite `h1` using `[X.Λ_span]`. Establish `: (Pi.single ⟨0, hr⟩ (1 : E) : Fin r → E) ∈ (⊤ : Submodule E (Fin r → E))` using `Submodule.mem_top`. Rewrite `this` using `[h1, Submodule.mem_bot]`. Use `congrFun this ⟨0, hr⟩` as an intermediate fact. Simplify using `at this`.
-/
theorem lam_ne (X : Data E r) (hr : 0 < r) : ∃ v ∈ X.Λ, v ≠ 0 := by
  by_contra h
  push Not at h
  have h1 : Submodule.span E (X.Λ : Set (Fin r → E)) = ⊥ := by
    rw [Submodule.span_eq_bot]
    exact h
  rw [X.Λ_span] at h1
  have : (Pi.single ⟨0, hr⟩ (1 : E) : Fin r → E) ∈ (⊤ : Submodule E (Fin r → E)) := Submodule.mem_top
  rw [h1, Submodule.mem_bot] at this
  have := congrFun this ⟨0, hr⟩
  simp at this

/- English proof (translation)
The claim follows from `ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfC.first_minimum_pos X hx (lam_ne X hr)`.
-/
theorem la1_pos_of_mem_dom (X : Data E r) (hr : 0 < r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) : 0 < X.la1 x :=
  ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfC.first_minimum_pos X hx (lam_ne X hr)

open Topology Filter in
/- English proof (translation)
Take `⟨b0, hb0, hort, hmaj0⟩` from `ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfC.orthonormalize X hx0`. Establish `hτ : ∀ τ : X.Ψ, ∀ᶠ w in 𝓝 x0, w ∈ X.dom → ∀ v, κ⁻¹ * X.maj x0 τ v ≤ X.maj w τ v ∧ X.maj w τ v ≤ κ * X.maj x0 τ v`. Introduce `τ`. Use `set Y := mat (rmul x0 b0) τ with hY`. Establish `hYd : Y.det ≠ 0` using `ReciprocityTheory.ChartRestriction.G.FD.CompactEntryBounds.det_ne_of_gram X (hort τ)`.

Establish `hYu : IsUnit Y.det` using `isUnit_iff_ne_zero.2 hYd`. Use `set Nf : Frame X.Ψ r → (Fin r → Fin r → ℂ) := fun w => (Y⁻¹ * (mat w τ * mat b0 τ) : Matrix (Fin r) (Fin r) ℂ) with hNf`. Establish `hmat : Continuous fun w : Frame X.Ψ r => (mat w τ : Matrix (Fin r) (Fin r) ℂ)` using `continuous_apply τ`. Establish `hcont : Continuous Nf` using `continuous_const.matrix_mul (hmat.matrix_mul continuous_const)`. Establish `hN0 : Nf x0 = ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfB.Nid r` using `by show (Y⁻¹ * (mat x0 τ * mat b0 τ) : Matrix (Fin r) (Fin r) ℂ) = _`.

Rewrite using `[show mat x0 τ * mat b0 τ = Y from rfl, Matrix.nonsing_inv_mul _ hYu]`. Use function extensionality and compare the values at `a b`. Simplify using `[ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfB.Nid, Matrix.one_apply]`. Establish `hU` using `ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfB.Ms_unif X τ hκ`. Rewrite `hU` using `[← hN0]`.

Establish `hev` using `(hcont.tendsto x0).eventually hU`. Use `filter_upwards [hev] with w hw hwd v`. Establish `hwb` using `ReciprocityTheory.ChartRestriction.G.FD.OrthogonalFrameDomain.rmul_mem_dom X hwd hb0`. Establish `e1 : X.maj w τ v = X.maj (rmul w b0) τ v` using `(ReciprocityTheory.ChartRestriction.G.FD.FlowMajorantFlags.maj_flag X hwd hwb (ReciprocityTheory.ChartRestriction.G.FD.FlagSpanBounds.sameFlag_rmul X w hb0) τ v).symm`. Establish `hw' : mat (rmul w b0) τ = Y * Matrix.of (Nf w)` using `by show mat w τ * mat b0 τ = Y * (Y⁻¹ * (mat w τ * mat b0 τ))`.

Rewrite using `[Matrix.mul_nonsing_inv_cancel_left _ _ hYu]`. Establish `e2` using `ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfA.maj_chart X (hort τ) (Nf w) hw' v`. Establish `e3 : X.maj x0 τ v = ∑ a, ‖(Y⁻¹ *ᵥ v) a‖ ^ 2`. Rewrite using `[← hmaj0 τ v, ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfA.maj_orth X hort τ v]`. Take `⟨h1, h2⟩` from `hw (Y⁻¹ *ᵥ v)`.

Rewrite using `[e1, e2, e3]`. Conclude with `⟨h1, h2⟩`. Use `filter_upwards [Filter.eventually_all.2 hτ] with w hw hwd τ v`. Conclude with `hw τ hwd v`.
-/
theorem maj_near (X : Data E r) {x0 : Frame X.Ψ r} (hx0 : x0 ∈ X.dom) {κ : ℝ} (hκ : 1 < κ) :
    ∀ᶠ w in 𝓝 x0, w ∈ X.dom → ∀ τ v, κ⁻¹ * X.maj x0 τ v ≤ X.maj w τ v ∧ X.maj w τ v ≤ κ * X.maj x0 τ v := by
  obtain ⟨b0, hb0, hort, hmaj0⟩ := ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfC.orthonormalize X hx0
  have hτ : ∀ τ : X.Ψ, ∀ᶠ w in 𝓝 x0, w ∈ X.dom → ∀ v,
      κ⁻¹ * X.maj x0 τ v ≤ X.maj w τ v ∧ X.maj w τ v ≤ κ * X.maj x0 τ v := by
    intro τ
    set Y := mat (rmul x0 b0) τ with hY
    have hYd : Y.det ≠ 0 := ReciprocityTheory.ChartRestriction.G.FD.CompactEntryBounds.det_ne_of_gram X (hort τ)
    have hYu : IsUnit Y.det := isUnit_iff_ne_zero.2 hYd
    set Nf : Frame X.Ψ r → (Fin r → Fin r → ℂ) := fun w =>
      (Y⁻¹ * (mat w τ * mat b0 τ) : Matrix (Fin r) (Fin r) ℂ) with hNf
    have hmat : Continuous fun w : Frame X.Ψ r => (mat w τ : Matrix (Fin r) (Fin r) ℂ) := continuous_apply τ
    have hcont : Continuous Nf := continuous_const.matrix_mul (hmat.matrix_mul continuous_const)
    have hN0 : Nf x0 = ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfB.Nid r := by
      show (Y⁻¹ * (mat x0 τ * mat b0 τ) : Matrix (Fin r) (Fin r) ℂ) = _
      rw [show mat x0 τ * mat b0 τ = Y from rfl, Matrix.nonsing_inv_mul _ hYu]
      funext a b
      simp [ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfB.Nid, Matrix.one_apply]
    have hU := ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfB.Ms_unif X τ hκ
    rw [← hN0] at hU
    have hev := (hcont.tendsto x0).eventually hU
    filter_upwards [hev] with w hw hwd v
    have hwb := ReciprocityTheory.ChartRestriction.G.FD.OrthogonalFrameDomain.rmul_mem_dom X hwd hb0
    have e1 : X.maj w τ v = X.maj (rmul w b0) τ v :=
      (ReciprocityTheory.ChartRestriction.G.FD.FlowMajorantFlags.maj_flag X hwd hwb (ReciprocityTheory.ChartRestriction.G.FD.FlagSpanBounds.sameFlag_rmul X w hb0) τ v).symm
    have hw' : mat (rmul w b0) τ = Y * Matrix.of (Nf w) := by
      show mat w τ * mat b0 τ = Y * (Y⁻¹ * (mat w τ * mat b0 τ))
      rw [Matrix.mul_nonsing_inv_cancel_left _ _ hYu]
    have e2 := ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfA.maj_chart X (hort τ) (Nf w) hw' v
    have e3 : X.maj x0 τ v = ∑ a, ‖(Y⁻¹ *ᵥ v) a‖ ^ 2 := by
      rw [← hmaj0 τ v, ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfA.maj_orth X hort τ v]
    obtain ⟨h1, h2⟩ := hw (Y⁻¹ *ᵥ v)
    rw [e1, e2, e3]
    exact ⟨h1, h2⟩
  filter_upwards [Filter.eventually_all.2 hτ] with w hw hwd τ v
  exact hw τ hwd v

set_option maxHeartbeats 400000 in
open Topology Filter in
/- English proof (translation)
Introduce `x0 hx0`. Establish `hsq : ContinuousWithinAt X.firstMinimumSq X.dom x0`. Rewrite using `[Metric.continuousWithinAt_iff]`. Introduce `ε hε`. Take `⟨L, hL⟩ : ∃ L, X.firstMinimumSq x0 = L` from `⟨_, rfl⟩`.

Establish `hL0 : 0 ≤ L` using `hL ▸ ReciprocityTheory.ChartRestriction.G.FD.MinimumGrowthBounds.minimumSq_nonneg X hx0`. Take `⟨q, hqdef⟩ : ∃ q : ℝ, q = ε / (2 * (L + 1))` from `⟨_, rfl⟩`. Establish `hq : 0 < q` using `by rw [hqdef]; positivity`. Establish `hqL : q * L < ε`. Rewrite using `[hqdef, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]`.

Use the polynomial consequences of the given equalities and inequalities. Take `⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = 1 + q` from `⟨_, rfl⟩`. Establish `hκ : 1 < κ` using `by linarith`. Take `⟨δ, hδ, hball⟩` from `Metric.eventually_nhds_iff.1 (maj_near X hx0 hκ)`. Use `⟨δ, hδ, fun w hwd hdist => ?_⟩` and prove the remaining obligations.

Establish `hcmp` using `hball hdist hwd`. Take `⟨b1, b2⟩` from `ReciprocityTheory.ChartRestriction.G.FD.MinimumGrowthBounds.minimumSq_two_sided_bounds X hx0 hwd (inv_nonneg.2 (by linarith)) (by linarith) (fun τ v => (hcmp τ v).1) (fun τ v => (hcmp τ v).2)`. Rewrite `b1`, `b2` using `[hL]`. Establish `hk : (κ - 1) * L < ε` using `by rw [hκdef, add_sub_cancel_left]; exact hqL`. Establish `hk1 : (1 - κ⁻¹) * L ≤ (κ - 1) * L`.

Apply `mul_le_mul_of_nonneg_right _ hL0` to reduce the goal to its premises. Establish `hκ0 : κ ≠ 0` using `by linarith`. Rewrite using `[show 1 - κ⁻¹ = (κ - 1) * κ⁻¹ by field_simp]`. Conclude with `mul_le_of_le_one_right (by linarith) (inv_le_one_of_one_le₀ hκ.le)`. Rewrite using `[hL, Real.dist_eq, abs_lt]`.

Prove the components needed by the constructor for the conclusion. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `(Real.continuous_sqrt.continuousAt).comp_continuousWithinAt hsq`.
-/
theorem firstMinimum_continuousOn (X : Data E r) : ContinuousOn X.la1 X.dom := by
  intro x0 hx0
  have hsq : ContinuousWithinAt X.firstMinimumSq X.dom x0 := by
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    obtain ⟨L, hL⟩ : ∃ L, X.firstMinimumSq x0 = L := ⟨_, rfl⟩
    have hL0 : 0 ≤ L := hL ▸ ReciprocityTheory.ChartRestriction.G.FD.MinimumGrowthBounds.minimumSq_nonneg X hx0
    obtain ⟨q, hqdef⟩ : ∃ q : ℝ, q = ε / (2 * (L + 1)) := ⟨_, rfl⟩
    have hq : 0 < q := by rw [hqdef]; positivity
    have hqL : q * L < ε := by
      rw [hqdef, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = 1 + q := ⟨_, rfl⟩
    have hκ : 1 < κ := by linarith
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (maj_near X hx0 hκ)
    refine ⟨δ, hδ, fun w hwd hdist => ?_⟩
    have hcmp := hball hdist hwd
    obtain ⟨b1, b2⟩ := ReciprocityTheory.ChartRestriction.G.FD.MinimumGrowthBounds.minimumSq_two_sided_bounds X hx0 hwd (inv_nonneg.2 (by linarith))
      (by linarith) (fun τ v => (hcmp τ v).1) (fun τ v => (hcmp τ v).2)
    rw [hL] at b1 b2
    have hk : (κ - 1) * L < ε := by rw [hκdef, add_sub_cancel_left]; exact hqL
    have hk1 : (1 - κ⁻¹) * L ≤ (κ - 1) * L := by
      apply mul_le_mul_of_nonneg_right _ hL0
      have hκ0 : κ ≠ 0 := by linarith
      rw [show 1 - κ⁻¹ = (κ - 1) * κ⁻¹ by field_simp]
      exact mul_le_of_le_one_right (by linarith) (inv_le_one_of_one_le₀ hκ.le)
    rw [hL, Real.dist_eq, abs_lt]
    constructor
    · linarith
    · linarith
  exact (Real.continuous_sqrt.continuousAt).comp_continuousWithinAt hsq

/- English proof (translation)
Introduce `r X hr` and use `⟨fun γ hγ x hx b hb => firstMinimum_biinvariant X hγ hx hb, firstMinimum_continuousOn X, fun x hx => la1_pos_of_mem_dom X hr hx⟩`.
-/
theorem la1GGStatement_firstMinimum : LineBundleFirstBoundGlobalGeneration (E := E) := fun r X hr =>
  ⟨fun γ hγ x hx b hb => firstMinimum_biinvariant X hγ hx hb, firstMinimum_continuousOn X, fun x hx => la1_pos_of_mem_dom X hr hx⟩

end

end ReciprocityTheory.ChartRestriction.G.AR.Inst
