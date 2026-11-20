import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegerAddConjEqOneOfFormallyUnramified
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionHermitianLinearFormFgModuleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicDualPartnerSelfDualHermitianLattiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualHermitianLatticeExistsNonzeroPairingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitEmbeddingIntegralAndMaximalIdealStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsScaleFractionalIdealIntegralAvoidMaximalsStatement

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

namespace GlobalTheory.HypPairLat

/- English proof (translation)
Simplify using `[form, smul_dotProduct]`.
-/
theorem form_smul_left {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (c : E) (z w : Fin n → E) : form σ J (c • z) w = c * form σ J z w := by
  simp [form, smul_dotProduct]

/- English proof (translation)
Establish `: (fun i => σ ((c • w) i)) = σ c • fun i => σ (w i)` using `by ext i; simp`. Simplify using `only [form, this, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]`.
-/
theorem form_smul_right {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (c : E) (z w : Fin n → E) : form σ J z (c • w) = σ c * form σ J z w := by
  have : (fun i => σ ((c • w) i)) = σ c • fun i => σ (w i) := by ext i; simp
  simp only [form, this, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

/- English proof (translation)
Simplify using `only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ]`. Simplify using `only [Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hJ]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem form_conj {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (hJ : ∀ i j, σ (J j i) = J i j) (z w : Fin n → E) :
    σ (form σ J z w) = form σ J w z := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]; ring

/- English proof (translation)
The claim follows from `h.map (σ.toRingHom.toIntAlgHom)`.
-/
theorem isIntegral_sigma {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {e : E}
    (h : IsIntegral ℤ e) : IsIntegral ℤ (σ e) :=
  h.map (σ.toRingHom.toIntAlgHom)

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B hB n Y r s hY x hx0 hxx`. Establish `hσ : ∀ e, σ (σ e) = e` using `fun e => by`. Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Apply `τ.injective` to reduce the goal to its premises. Rewrite using `[hB.cm.2.2.2, hB.cm.2.2.2, star_star]`.

Establish `hfu : Algebra.FormallyUnramified (𝓞 F) (𝓞 E)` using `by haveI := hB.unram; infer_instance`. Take `⟨θ, hθ⟩` from `GlobalTheory.exists_integer_add_conj_eq_one_of_formallyUnramified F E σ hB.cm hfu`. Establish `hfg : Y.L.FG` using `hY.lat.fg`. Take `⟨z0, hz0L, hz0⟩` from `GlobalTheory.T.selfDual_hermitianLattice_exists_nonzero_pairing F E σ hσ n Y.J Y.L hfg hY.herm hY.dual x hx0`. Set `f : (Fin n → E) →ₗ[𝓞 E] E` to `{ toFun := fun z => form σ Y.J z x map_add' := fun a b => by simp [form, add_dotProduct] map_smul' := fun c a => by show form σ Y.J ((c : E) • a) x = (c : E) * form σ Y.J a x`.

Conclude with `form_smul_left σ Y.J (c : E) a x }`. Establish `hf : ∀ z, f z = form σ Y.J z x` using `fun z => rfl`. Set `I₀ : Submodule (𝓞 E) E` to `Y.L.map f`. Establish `hI₀fg : I₀.FG` using `hfg.map f`. Establish `hI₀ne : I₀ ≠ ⊥`.

Introduce `h`. Establish `: f z0 ∈ I₀` using `Submodule.mem_map_of_mem hz0L`. Rewrite `this` using `[h, Submodule.mem_bot]`. Conclude with `hz0 this`. Establish `hT4` using `fun (v : B.P) (b : Bool) => GlobalTheory.T.splitEmbedding_integral_and_maximalIdeal F E v.1 (if b then (B.τ v).comp σ else B.τ v)`.

Use `choose hle Q hQmax hQ using hT4`. Take `⟨s, hs0, hsI, hsQ⟩` from `GlobalTheory.T.exists_scale_fractionalIdeal_integral_avoid_maximals E I₀ hI₀fg hI₀ne (B.P × Bool) (fun p => Q p.1 p.2) (fun p => hQmax _ _)`. Use `set x' : Fin n → E := σ s • x with hx'def`. Establish `hfx' : ∀ z, form σ Y.J z x' = s * form σ Y.J z x` using `fun z => by`. Rewrite using `[hx'def, form_smul_right, hσ]`.

Establish `hx'x' : form σ Y.J x' x' = 0`. Rewrite using `[hfx', hx'def, form_smul_left, hxx, mul_zero, mul_zero]`. Take `⟨y₀, hy₀1, hy₀L⟩` from `GlobalTheory.T.exists_section_hermitianLinearForm_fg_module F E σ n Y.J Y.L hfg x' ⟨z0, hz0L, by rw [hfx']; exact mul_ne_zero hs0 hz0⟩`. Take `⟨y, hyy, hx'y, hL⟩` from `GlobalTheory.T.exists_isotropic_dual_partner_selfDual_hermitianLattice F E σ hσ n Y.J Y.L hY.herm hY.dual θ hθ x' y₀ hx'x' hy₀1 hy₀L`. Establish `hint : ∀ z ∈ Y.L, IsIntegral ℤ (form σ Y.J z x')` using `fun z hz => by`.

Rewrite using `[hfx']`. Conclude with `hsI _ (Submodule.mem_map_of_mem hz)`. Establish `hx'L : x' ∈ Y.L` using `(hY.dual x').2 fun w hw => by`. Rewrite using `[← form_conj σ hσ Y.J hY.herm]`. Conclude with `isIntegral_sigma σ (hint w hw)`.

Establish `hyx' : form σ Y.J y x' = 1`. Rewrite using `[← form_conj σ hσ Y.J hY.herm, hx'y, map_one]`. Establish `hval : ∀ (v : B.P) (b : Bool) (e : E), IsIntegral ℤ e → Valued.v ((if b then (B.τ v).comp σ else B.τ v) e) ≤ 1` using `fun v b e he => hle v b ⟨e, he⟩`. Establish `hwit : ∀ (v : B.P) (b : Bool), ∃ z ∈ Y.L, IsIntegral ℤ (form σ Y.J z x') ∧ Valued.v ((if b then (B.τ v).comp σ else B.τ v) (form σ Y.J z x')) = 1`. Introduce `v b`.

Take `⟨a, ha, o, ho, hoQ⟩` from `hsQ (v, b)`. Take `⟨z, hz, rfl⟩` from `Submodule.mem_map.1 ha`. Use `⟨z, hz, hint z hz, ?_⟩` and prove the remaining obligations. Establish `h1` using `hle v b o`. Establish `h2 : ¬ Valued.v ((if b then (B.τ v).comp σ else B.τ v) (o : E)) < 1` using `fun h => hoQ ((hQ v b o).2 h)`.

Rewrite `h1`, `h2` using `[ho, hf, ← hfx']`. Conclude with `le_antisymm h1 (not_lt.1 h2)`. Use `⟨x', y, hx'x', hyy, hx'y, hL, fun v => ⟨⟨fun c hc => ?_, 1, by rw [one_smul]; exact hx'L, by simp⟩, ⟨fun c hc => ?_, ?_⟩⟩⟩` and prove the remaining obligations. Take `⟨z, hz, -, hz1⟩` from `hwit v true`. Establish `hi : IsIntegral ℤ (form σ Y.J (c • x') z)` using `(hY.dual _).1 hc z hz`.

Rewrite `hi` using `[form_smul_left, ← form_conj σ hσ Y.J hY.herm z x']`. Use `hval v false _ hi` as an intermediate fact. Simplify using `only [Bool.false_eq_true, ↓reduceIte, map_mul] at this`. Simplify using `only [↓reduceIte, AlgHom.comp_apply] at hz1`. Rewrite `this` using `[hz1, mul_one]`.

Conclude with `this`. Establish `hi` using `hint _ hc`. Rewrite `hi` using `[form_smul_left, hyx', mul_one]`. Simplify using `using hval v false c hi`. Take `⟨z, hz, -, hz1⟩` from `hwit v false`.

Conclude with `⟨form σ Y.J z x', (hL z hz).2, by simpa using hz1⟩`.
-/
theorem exists_pair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (n : ℕ) (Y : Spc F E n) (r s : ℕ), Y.IsHerm σ B r s →
    ∀ x : Fin n → E, x ≠ 0 → form σ Y.J x x = 0 →
    ∃ x' y : Fin n → E, form σ Y.J x' x' = 0 ∧ form σ Y.J y y = 0 ∧ form σ Y.J x' y = 1 ∧
      (∀ z ∈ Y.L, form σ Y.J z y • x' ∈ Y.L ∧ form σ Y.J z x' • y ∈ Y.L) ∧
      ∀ v : B.P, ((∀ c : E, c • x' ∈ Y.L → Valued.v (B.τ v c) ≤ 1) ∧ ∃ c : E, c • x' ∈ Y.L ∧ Valued.v (B.τ v c) = 1) ∧
        ((∀ c : E, c • y ∈ Y.L → Valued.v (B.τ v c) ≤ 1) ∧ ∃ c : E, c • y ∈ Y.L ∧ Valued.v (B.τ v c) = 1) := by
  intro F E _ _ _ _ _ σ B hB n Y r s hY x hx0 hxx
  have hσ : ∀ e, σ (σ e) = e := fun e => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star]
  have hfu : Algebra.FormallyUnramified (𝓞 F) (𝓞 E) := by haveI := hB.unram; infer_instance
  obtain ⟨θ, hθ⟩ := GlobalTheory.exists_integer_add_conj_eq_one_of_formallyUnramified F E σ hB.cm hfu
  have hfg : Y.L.FG := hY.lat.fg
  obtain ⟨z0, hz0L, hz0⟩ := GlobalTheory.T.selfDual_hermitianLattice_exists_nonzero_pairing F E σ hσ n Y.J Y.L hfg hY.herm hY.dual x hx0
  let f : (Fin n → E) →ₗ[𝓞 E] E :=
    { toFun := fun z => form σ Y.J z x
      map_add' := fun a b => by simp [form, add_dotProduct]
      map_smul' := fun c a => by
        show form σ Y.J ((c : E) • a) x = (c : E) * form σ Y.J a x
        exact form_smul_left σ Y.J (c : E) a x }
  have hf : ∀ z, f z = form σ Y.J z x := fun z => rfl
  let I₀ : Submodule (𝓞 E) E := Y.L.map f
  have hI₀fg : I₀.FG := hfg.map f
  have hI₀ne : I₀ ≠ ⊥ := by
    intro h
    have : f z0 ∈ I₀ := Submodule.mem_map_of_mem hz0L
    rw [h, Submodule.mem_bot] at this
    exact hz0 this
  have hT4 := fun (v : B.P) (b : Bool) => GlobalTheory.T.splitEmbedding_integral_and_maximalIdeal F E v.1 (if b then (B.τ v).comp σ else B.τ v)
  choose hle Q hQmax hQ using hT4
  obtain ⟨s, hs0, hsI, hsQ⟩ := GlobalTheory.T.exists_scale_fractionalIdeal_integral_avoid_maximals E I₀ hI₀fg hI₀ne (B.P × Bool) (fun p => Q p.1 p.2) (fun p => hQmax _ _)
  set x' : Fin n → E := σ s • x with hx'def
  have hfx' : ∀ z, form σ Y.J z x' = s * form σ Y.J z x := fun z => by
    rw [hx'def, form_smul_right, hσ]
  have hx'x' : form σ Y.J x' x' = 0 := by
    rw [hfx', hx'def, form_smul_left, hxx, mul_zero, mul_zero]
  obtain ⟨y₀, hy₀1, hy₀L⟩ := GlobalTheory.T.exists_section_hermitianLinearForm_fg_module F E σ n Y.J Y.L hfg x' ⟨z0, hz0L, by rw [hfx']; exact mul_ne_zero hs0 hz0⟩
  obtain ⟨y, hyy, hx'y, hL⟩ := GlobalTheory.T.exists_isotropic_dual_partner_selfDual_hermitianLattice F E σ hσ n Y.J Y.L hY.herm hY.dual θ hθ x' y₀ hx'x' hy₀1 hy₀L
  have hint : ∀ z ∈ Y.L, IsIntegral ℤ (form σ Y.J z x') := fun z hz => by
    rw [hfx']; exact hsI _ (Submodule.mem_map_of_mem hz)
  have hx'L : x' ∈ Y.L := (hY.dual x').2 fun w hw => by
    rw [← form_conj σ hσ Y.J hY.herm]; exact isIntegral_sigma σ (hint w hw)
  have hyx' : form σ Y.J y x' = 1 := by
    rw [← form_conj σ hσ Y.J hY.herm, hx'y, map_one]

  have hval : ∀ (v : B.P) (b : Bool) (e : E), IsIntegral ℤ e →
      Valued.v ((if b then (B.τ v).comp σ else B.τ v) e) ≤ 1 := fun v b e he =>
    hle v b ⟨e, he⟩
  have hwit : ∀ (v : B.P) (b : Bool), ∃ z ∈ Y.L, IsIntegral ℤ (form σ Y.J z x') ∧
      Valued.v ((if b then (B.τ v).comp σ else B.τ v) (form σ Y.J z x')) = 1 := by
    intro v b
    obtain ⟨a, ha, o, ho, hoQ⟩ := hsQ (v, b)
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 ha
    refine ⟨z, hz, hint z hz, ?_⟩
    have h1 := hle v b o
    have h2 : ¬ Valued.v ((if b then (B.τ v).comp σ else B.τ v) (o : E)) < 1 := fun h => hoQ ((hQ v b o).2 h)
    rw [ho, hf, ← hfx'] at h1 h2
    exact le_antisymm h1 (not_lt.1 h2)
  refine ⟨x', y, hx'x', hyy, hx'y, hL, fun v => ⟨⟨fun c hc => ?_, 1, by rw [one_smul]; exact hx'L, by simp⟩,
    ⟨fun c hc => ?_, ?_⟩⟩⟩
  · obtain ⟨z, hz, -, hz1⟩ := hwit v true
    have hi : IsIntegral ℤ (form σ Y.J (c • x') z) := (hY.dual _).1 hc z hz
    rw [form_smul_left, ← form_conj σ hσ Y.J hY.herm z x'] at hi
    have := hval v false _ hi
    simp only [Bool.false_eq_true, ↓reduceIte, map_mul] at this
    simp only [↓reduceIte, AlgHom.comp_apply] at hz1
    rw [hz1, mul_one] at this
    exact this
  · have hi := hint _ hc
    rw [form_smul_left, hyx', mul_one] at hi
    simpa using hval v false c hi
  · obtain ⟨z, hz, -, hz1⟩ := hwit v false
    exact ⟨form σ Y.J z x', (hL z hz).2, by simpa using hz1⟩

end GlobalTheory.HypPairLat
