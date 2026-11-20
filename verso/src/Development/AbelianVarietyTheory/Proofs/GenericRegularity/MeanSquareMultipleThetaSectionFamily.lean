import Mathlib
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.RigFrame
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NormalisedPointsSatisfySingleFrame
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif GlobalTheory.FrameNorm
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.FrameNorm

open GlobalTheory.NormFrame in
set_option maxHeartbeats 1600000 in

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo σ' g ty F k m B P fr bas b h τ c₁ c₂ x s κ hbd hper hsympl hdet hsym hpos hn half₁ half₂ ⟨fr_hol, fr_ne, fr_coc, fr_rig⟩ hx hκ0 hs`. Take `⟨Hm, hH1, hH2, hH3⟩` from `hper.2.2.2.2`. Take `⟨hHm, -⟩` from `GlobalTheory.RiemannForm.herm_eq_of_normalised E H _ g _ bas _ h τ Hm hsympl hper hn ⟨hsym, hpos⟩ hH3`. Take `⟨q, hq⟩ : ∃ q : (Fin g → ℂ) → ℂ, ∀ z, q z = Real.pi / 2 * ((h *ᵥ z) ⬝ᵥ (((τ.map Complex.im)⁻¹).map (fun x : ℝ => (x : ℂ)) *ᵥ (h *ᵥ z)))` from `⟨_, fun _ => rfl⟩`. Establish `hlin : Differentiable ℂ (fun z : Fin g → ℂ => h *ᵥ z)` using `(Matrix.mulVecLin h).toContinuousLinearMap.differentiable`.

Establish `hqd : Differentiable ℂ q`. Rewrite using `[funext hq]`. Simplify using `only [dotProduct, Matrix.mulVec]`. Use `fun_prop`. Establish `hq0 : q 0 = 0` using `by simp [hq]`.

Take `⟨hA1, hA2⟩` from `GlobalTheory.ThetaAH.exp_mul_thetaChar_automorphy g τ h Hm c₁ c₂ q hsym hpos half₁ half₂ hHm hq`. Establish `hlat : ∀ lam, lam ∈ (P b).range ↔ ∃ m n : Fin g → ℤ, h *ᵥ lam = (fun i => (m i : ℂ)) + τ *ᵥ (fun i => (n i : ℂ))`. Introduce `lam`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, rfl⟩`.

Take `⟨v, rfl⟩` from `bas.surjective a`. Conclude with `⟨_, _, period_bas bas _ _ _ hn v⟩`. Introduce and unpack `⟨m, n, hmn⟩`. Use `⟨bas (Sum.elim m n), ?_⟩` and prove the remaining obligations. Apply `Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 hdet)` to reduce the goal to its premises.

Rewrite using `[hmn]`. Conclude with `period_bas bas _ _ _ hn _`. Take `⟨Fd, hFd, hint⟩` from `GlobalTheory.ThetaMean.exists_fundamentalDomain_mean_norm_sq_thetaChar g τ h c₁ c₂ _ hsym hpos hdet half₁ half₂ hlat`. Take `⟨hθd, w0, hw0⟩` from `(GlobalTheory.ThetaHalf.thetaChar_holomorphic_ne_zero g c₁ c₂ half₁ half₂).1 _ hsym hpos`. Establish `hχ : ∀ lam : Fin g → ℂ, ∃ χ : ℂ, lam ∈ (P b).range → ‖χ‖ = 1 ∧ ∀ z, Complex.exp (q (z + lam)) * thetaChar τ c₁ c₂ (h *ᵥ (z + lam)) = χ * Complex.exp (Real.pi * hermForm Hm z lam + Real.pi / 2 * hermForm Hm lam lam) * (Complex.exp (q z) * thetaChar τ c₁ c₂ (h *ᵥ z))`.

Introduce `lam`. Distinguish the cases in `hl : lam ∈ (P b).range`. Take `⟨m, n, hmn⟩` from `(hlat lam).1 hl`. Take `⟨χ, hχ⟩` from `hA2 lam m n hmn`. Conclude with `⟨χ, fun _ => hχ⟩`.

Conclude with `⟨1, fun h => absurd h hl⟩`. Use `choose χl hχl using hχ`. Establish `hfrd : ∀ j, DifferentiableOn ℂ (fun z => fr j (b, z) * Complex.exp (-q z)) {z | ⊤ ≤ (F.ex k (P b) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}`. Introduce `j`. Use `DifferentiableOn.mul ?_ (by fun_prop)` and prove the remaining obligations.

Conclude with `(fr_hol j).comp (f := fun z => (b, z)) (by fun_prop) fun z hz => ⟨hbd, hz⟩`. Establish `hval : ∀ j z (pt : Sp ℂ ⟶ Gx x), pt ≫ gxFst x = (F.ex k (P b) z).left → pt ≫ gxSnd x = 𝟙 (Sp ℂ) → ⊤ ≤ (F.ex k (P b) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → valAt' pt ((PPx x).U (fun _ => j)) (s.f (fun _ => j)) = (κ * (Complex.exp (q z) * thetaChar τ c₁ c₂ (h *ᵥ z))) * (fr j (b, z) * Com …`. Introduce `j z pt h1 h2 h3`. Rewrite using `[hs j z pt h1 h2 h3, Complex.exp_neg]`. Use `Complex.exp_ne_zero (q z)` as an intermediate fact.

Clear the denominators using the available nonvanishing facts. Use `⟨Hm, χl, fun j z => fr j (b, z) * Complex.exp (-q z), fun z => κ * (Complex.exp (q z) * thetaChar τ c₁ c₂ (h *ᵥ z)), Fd, hH1, hH2, hH3, hfrd, fun j z hz => mul_ne_zero (fr_ne j b z hbd hz) (Complex.exp_ne_zero _), fun j j' z hz => ?_, fun j hz => ?_, fun a j z => ⟨(hχl _ ⟨a, rfl⟩ …` and prove the remaining obligations. Use `beta_reduce`. Rewrite using `[fr_coc j j' b z hbd hz, mul_assoc]`. Use `beta_reduce`.

Rewrite using `[hq0, neg_zero, Complex.exp_zero, mul_one, fr_rig j b hbd hz, hx]`. Establish `hex : ∀ z, F.ex k (P b) (z + P b a) = F.ex k (P b) z` using `ex_add_period F k _ hper a`. Establish `hO : IsOpen {z | ⊤ ≤ (F.ex k (P b) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}`. Establish `h1` using `((F.hol k 0 Set.univ (fun _ => P b) isOpen_univ ⟨fun _ _ => hper, fun _ => differentiableOn_const _⟩).2 (Xo.univ.t.PP.L.U j) 0).1`. Establish `h2` using `h1.preimage (f := fun z : Fin g → ℂ => ((0 : Fin 0 → ℂ), z)) (by fun_prop)`.

Use `h2 using 1` and compare the differences between its conclusion and the goal. Use extensionality with `z`. Simplify using the standard rewrite rules. Use `cancel_entire (θ := fun z => Complex.exp (q z) * thetaChar τ c₁ c₂ (h *ᵥ z)) (f := fun z => fr j (b, z) * Complex.exp (-q z)) (f' := fun z => χl (P b a) * Complex.exp (Real.pi * hermForm Hm z (P b a) + Real.pi / 2 * hermForm Hm (P b a) (P b a)) * (fr j (b, z + P b a) * Complex.ex …` and prove the remaining obligations. Take `⟨w, hw⟩` from `Matrix.mulVec_surjective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 hdet) w0`.

Conclude with `⟨w, mul_ne_zero (Complex.exp_ne_zero _) (by rw [hw]; exact hw0)⟩`. Use `ContinuousOn.mul (Continuous.continuousOn ?_) ?_` and prove the remaining obligations. Simplify using `only [hermForm, dotProduct] fun_prop`. Use `(hfrd j).continuousOn.comp (f := fun z => z + P b a) (by fun_prop) fun z hz => ?_` and prove the remaining obligations. Rewrite using `[Set.mem_ofPred_eq, hex]`.

Conclude with `hz`. Introduce `z hz`. Establish `hw : 𝟙 _ ≫ x = (F.ex k (P b) z).left ≫ Xo.univ.t.G.hom`. Rewrite using `[Category.id_comp, hx]`. Conclude with `(Over.w (F.ex k (P b) z)).symm`.

Take `⟨pt, e₁, e₂⟩ : ∃ pt : Sp ℂ ⟶ Gx x, pt ≫ gxFst x = (F.ex k (P b) z).left ∧ pt ≫ gxSnd x = 𝟙 _` from `⟨pullback.lift (f := x) (g := Xo.univ.t.G.hom) _ _ hw, pullback.lift_snd _ _ _, pullback.lift_fst _ _ _⟩`. Establish `h1` using `hval j z pt e₁ e₂ hz`. Establish `h2` using `hval j (z + P b a) pt (by rw [hex]; exact e₁) e₂ (by rw [hex]; exact hz)`. Establish `h3` using `h1.symm.trans h2`. Rewrite `h3` using `[(hχl _ ⟨a, rfl⟩).2 z]`.

Apply `mul_left_cancel₀ hκ0` to reduce the goal to its premises. Take the linear combination `h3`. Rewrite using `[← hint, ← mul_div_assoc, ← MeasureTheory.integral_const_mul]`. Use `congr 2`. Use extensionality with `z`.

Rewrite using `[← hA1 z, norm_mul, norm_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ahMean_of_secVal_thetaChar : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (σ' : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ' ty) (k : Fin F.n) (m : ℕ) (B : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → ((F.Di k).La →+ (Fin g → ℂ))) (fr : Xo.univ.t.PP.L.ι → (Fin m → ℂ) × (Fin g → ℂ) → ℂ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (F.Di k).La) (b : Fin m → ℂ) (h τ : Matrix (Fin g) (Fin g) ℂ) (c₁ c₂ : Fin g → ℂ) (x : Sp ℂ ⟶ Xo.X) (s : LB.Sec (PPx x)) (κ : ℂ), b ∈ B → IsPeriod (F.Di k) ty (P b) → (∀ v w, (F.Di k).EF (bas v) (bas w) = -omegaStd v w) → IsUnit h.det → τ.IsSymm → (τ.map Complex.im).PosDef → (∀ i, h *ᵥ P b (bas (Pi.single (Sum.inl i) 1)) = Pi.single i 1 ∧ h *ᵥ P b (bas (Pi.single (Sum.inr i) 1)) = τ *ᵥ Pi.single i 1) → (∀ i, c₁ i = 0 ∨ c₁ i = 1 / 2) → (∀ i, c₂ i = 0 ∨ c₂ i = 1 / 2) → RigFrame F k B P fr → x = F.u k (P b) → κ ≠ 0 → SecVal F k (P b) x s (fun z => κ * thetaChar τ c₁ c₂ (h *ᵥ z)) (fun j z => fr j (b, z)) → AHMean F k (P b) x s (‖κ‖ ^ 2 * (Real.sqrt (2 ^ g * (τ.map Complex.im).det))⁻¹) := by
  intro E _ _ _ H Dw l Xo σ' g ty F k m B P fr bas b h τ c₁ c₂ x s κ hbd hper hsympl hdet hsym hpos hn half₁ half₂
    ⟨fr_hol, fr_ne, fr_coc, fr_rig⟩ hx hκ0 hs
  obtain ⟨Hm, hH1, hH2, hH3⟩ := hper.2.2.2.2
  obtain ⟨hHm, -⟩ := GlobalTheory.RiemannForm.herm_eq_of_normalised E H _ g _ bas _ h τ Hm hsympl hper hn
    ⟨hsym, hpos⟩ hH3
  obtain ⟨q, hq⟩ : ∃ q : (Fin g → ℂ) → ℂ, ∀ z, q z = Real.pi / 2 * ((h *ᵥ z) ⬝ᵥ
      (((τ.map Complex.im)⁻¹).map (fun x : ℝ => (x : ℂ)) *ᵥ (h *ᵥ z))) := ⟨_, fun _ => rfl⟩
  have hlin : Differentiable ℂ (fun z : Fin g → ℂ => h *ᵥ z) :=
    (Matrix.mulVecLin h).toContinuousLinearMap.differentiable
  have hqd : Differentiable ℂ q := by
    rw [funext hq]
    simp only [dotProduct, Matrix.mulVec]
    fun_prop
  have hq0 : q 0 = 0 := by simp [hq]
  obtain ⟨hA1, hA2⟩ := GlobalTheory.ThetaAH.exp_mul_thetaChar_automorphy g τ h Hm c₁ c₂ q hsym hpos
    half₁ half₂ hHm hq
  have hlat : ∀ lam, lam ∈ (P b).range ↔ ∃ m n : Fin g → ℤ,
      h *ᵥ lam = (fun i => (m i : ℂ)) + τ *ᵥ (fun i => (n i : ℂ)) := by
    intro lam
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨v, rfl⟩ := bas.surjective a
      exact ⟨_, _, period_bas bas _ _ _ hn v⟩
    · rintro ⟨m, n, hmn⟩
      refine ⟨bas (Sum.elim m n), ?_⟩
      apply Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 hdet)
      rw [hmn]
      exact period_bas bas _ _ _ hn _
  obtain ⟨Fd, hFd, hint⟩ := GlobalTheory.ThetaMean.exists_fundamentalDomain_mean_norm_sq_thetaChar g τ h
    c₁ c₂ _ hsym hpos hdet half₁ half₂ hlat
  obtain ⟨hθd, w0, hw0⟩ := (GlobalTheory.ThetaHalf.thetaChar_holomorphic_ne_zero g c₁ c₂ half₁ half₂).1 _ hsym hpos
  have hχ : ∀ lam : Fin g → ℂ, ∃ χ : ℂ, lam ∈ (P b).range → ‖χ‖ = 1 ∧ ∀ z,
      Complex.exp (q (z + lam)) * thetaChar τ c₁ c₂ (h *ᵥ (z + lam)) =
        χ * Complex.exp (Real.pi * hermForm Hm z lam + Real.pi / 2 * hermForm Hm lam lam) *
          (Complex.exp (q z) * thetaChar τ c₁ c₂ (h *ᵥ z)) := by
    intro lam
    by_cases hl : lam ∈ (P b).range
    · obtain ⟨m, n, hmn⟩ := (hlat lam).1 hl
      obtain ⟨χ, hχ⟩ := hA2 lam m n hmn
      exact ⟨χ, fun _ => hχ⟩
    · exact ⟨1, fun h => absurd h hl⟩
  choose χl hχl using hχ
  have hfrd : ∀ j, DifferentiableOn ℂ (fun z => fr j (b, z) * Complex.exp (-q z))
      {z | ⊤ ≤ (F.ex k (P b) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j} := by
    intro j
    refine DifferentiableOn.mul ?_ (by fun_prop)
    exact (fr_hol j).comp (f := fun z => (b, z)) (by fun_prop) fun z hz => ⟨hbd, hz⟩
  have hval : ∀ j z (pt : Sp ℂ ⟶ Gx x),
      pt ≫ gxFst x = (F.ex k (P b) z).left → pt ≫ gxSnd x = 𝟙 (Sp ℂ) →
      ⊤ ≤ (F.ex k (P b) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' pt ((PPx x).U (fun _ => j)) (s.f (fun _ => j)) =
        (κ * (Complex.exp (q z) * thetaChar τ c₁ c₂ (h *ᵥ z))) *
          (fr j (b, z) * Complex.exp (-q z)) := by
    intro j z pt h1 h2 h3
    rw [hs j z pt h1 h2 h3, Complex.exp_neg]
    have := Complex.exp_ne_zero (q z)
    field_simp
  refine ⟨Hm, χl, fun j z => fr j (b, z) * Complex.exp (-q z),
    fun z => κ * (Complex.exp (q z) * thetaChar τ c₁ c₂ (h *ᵥ z)), Fd, hH1, hH2, hH3, hfrd,
    fun j z hz => mul_ne_zero (fr_ne j b z hbd hz) (Complex.exp_ne_zero _),
    fun j j' z hz => ?_, fun j hz => ?_, fun a j z => ⟨(hχl _ ⟨a, rfl⟩).1, ?_⟩, hval, hFd, ?_⟩
  · beta_reduce
    rw [fr_coc j j' b z hbd hz, mul_assoc]
  · beta_reduce
    rw [hq0, neg_zero, Complex.exp_zero, mul_one, fr_rig j b hbd hz, hx]
  · have hex : ∀ z, F.ex k (P b) (z + P b a) = F.ex k (P b) z :=
      ex_add_period F k _ hper a
    have hO : IsOpen {z | ⊤ ≤ (F.ex k (P b) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j} := by
      have h1 := ((F.hol k 0 Set.univ (fun _ => P b) isOpen_univ
        ⟨fun _ _ => hper, fun _ => differentiableOn_const _⟩).2 (Xo.univ.t.PP.L.U j) 0).1
      have h2 := h1.preimage (f := fun z : Fin g → ℂ => ((0 : Fin 0 → ℂ), z)) (by fun_prop)
      convert h2 using 1
      ext z
      simp
    refine cancel_entire (θ := fun z => Complex.exp (q z) * thetaChar τ c₁ c₂ (h *ᵥ z))
      (f := fun z => fr j (b, z) * Complex.exp (-q z))
      (f' := fun z => χl (P b a) * Complex.exp (Real.pi * hermForm Hm z (P b a) +
        Real.pi / 2 * hermForm Hm (P b a) (P b a)) *
        (fr j (b, z + P b a) * Complex.exp (-q (z + P b a))))
      ((hqd.cexp).mul (hθd.comp hlin)) ?_ hO (hfrd j).continuousOn ?_ ?_ z
    · obtain ⟨w, hw⟩ := Matrix.mulVec_surjective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 hdet) w0
      exact ⟨w, mul_ne_zero (Complex.exp_ne_zero _) (by rw [hw]; exact hw0)⟩
    · refine ContinuousOn.mul (Continuous.continuousOn ?_) ?_
      · simp only [hermForm, dotProduct]
        fun_prop
      · refine (hfrd j).continuousOn.comp (f := fun z => z + P b a) (by fun_prop) fun z hz => ?_
        rw [Set.mem_ofPred_eq, hex]
        exact hz
    · intro z hz
      have hw : 𝟙 _ ≫ x = (F.ex k (P b) z).left ≫ Xo.univ.t.G.hom := by
        rw [Category.id_comp, hx]
        exact (Over.w (F.ex k (P b) z)).symm
      obtain ⟨pt, e₁, e₂⟩ : ∃ pt : Sp ℂ ⟶ Gx x, pt ≫ gxFst x = (F.ex k (P b) z).left ∧ pt ≫ gxSnd x = 𝟙 _ :=
        ⟨pullback.lift (f := x) (g := Xo.univ.t.G.hom) _ _ hw, pullback.lift_snd _ _ _, pullback.lift_fst _ _ _⟩
      have h1 := hval j z pt e₁ e₂ hz
      have h2 := hval j (z + P b a) pt (by rw [hex]; exact e₁) e₂ (by rw [hex]; exact hz)
      have h3 := h1.symm.trans h2
      rw [(hχl _ ⟨a, rfl⟩).2 z] at h3
      apply mul_left_cancel₀ hκ0
      linear_combination h3
  · rw [← hint, ← mul_div_assoc, ← MeasureTheory.integral_const_mul]
    congr 2
    ext z
    rw [← hA1 z, norm_mul, norm_mul]
    ring

end GlobalTheory.FrameNorm
