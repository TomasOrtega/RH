import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.ConstantTermZeroEq

noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm

namespace PositivityTheory.Rg.Rs.SliceClasses

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

/- English proof (translation)
Introduce `r₁ h0 h1 c₁ hc₁`. Take `⟨F', hF'span, hF'ne, hF'eig⟩` from `(E_exp_iff hD ψ hψ h0 h1 c₁).1 hc₁`. Use `(E_exp_iff hD φ hφ h0 (by omega) c₁).2 ?_` and prove the remaining obligations. Establish `hφc : Continuous φ.1` using `GlobalTheory.CuspRep.ContAut.continuous_of_isOpen_stab E _ φ hφ.level`. Establish `hcr₁ : Continuous (An.ctn r₁ φ.1)` using `E_cont_ctn r₁ hφc hφ.left`.

Establish `hset : (Set.range fun t => E_L E (r + s) r₁ t (An.ctn r₁ φ.1)) = Set.range fun t : ℝ => fun g => An.ctn r₁ φ.1 (aT E (r + s) r₁ t * g)` using `rfl`. Establish `hfd` using `hT E (r + s) φ hφ r₁ h0 (by omega) _ ((hD E (r + s)).2.2.2 φ hφ r₁ h0 (by omega)).1`. Rewrite `hfd` using `[← hset]`. Use `hfd` as an intermediate fact. Establish `key` using `E_key_left h1 φ hφ τs a F hF ψ.1 m₂ h hψF`.

Establish `hP` using `E_cont_join (E := E) (n := r + s) (S := {r₁, r}) r₁`. Use `set B := E_B (fun b : {x : PPos (r + s) {r₁, r} // ¬ IsTop r₁ x} → Ad E => (parGL (joinPos (r := r₁) 0 b) : GA E (r + s))) (fun t (m : GA E r) => aT E (r + s) r t * (lev (Ad E) r s (m, m₂) * h)) ((E_vol E r r₁)⁻¹ * ((E_vol E (r + s) r)⁻¹ * E_vol E (r + s) r₁)) τs a with hBdef`. Establish `hcs : ∀ w ∈ Submodule.span ℂ (Set.range fun t => E_L E (r + s) r₁ t (An.ctn r₁ φ.1)), Continuous w`. Rewrite using `[hset]`. Conclude with `E_cont_span r₁ hcr₁`.

Establish `hadd : ∀ v ∈ Submodule.span ℂ (Set.range fun t => E_L E (r + s) r₁ t (An.ctn r₁ φ.1)), ∀ w ∈ Submodule.span ℂ (Set.range fun t => E_L E (r + s) r₁ t (An.ctn r₁ φ.1)), B (v + w) = B v + B w` using `fun v hv w hw => E_B_add hP _ _ _ _ (hcs v hv) (hcs w hw)`. Establish `hsm : ∀ (c : ℂ), ∀ w ∈ Submodule.span ℂ (Set.range fun t => E_L E (r + s) r₁ t (An.ctn r₁ φ.1)), B (c • w) = c • B w` using `fun c w _ => E_B_smul _ _ _ _ _ c w`. Establish `hBL : ∀ (t : ℝ), ∀ w ∈ Submodule.span ℂ (Set.range fun t => E_L E (r + s) r₁ t (An.ctn r₁ φ.1)), B (E_L E (r + s) r₁ t w) = Complex.exp (0 * t) • E_L E r r₁ t (B w)` using `fun t w _ => by`. Rewrite using `[hBdef, E_hB_left h1, zero_mul, Complex.exp_zero, one_smul]`. Establish `hF'2 : F' ∈ Submodule.span ℂ (Set.range fun t => E_L E r r₁ t (B (An.ctn r₁ φ.1)))`.

Rewrite using `[← key]`. Conclude with `hF'span`. Establish `hF'3 : ∀ t : ℝ, E_L E r r₁ t F' = Complex.exp (c₁ * t) • F'` using `fun t => by`. Use function extensionality and compare the values at `g`. Rewrite using `[E_L_apply, hF'eig t g]`.

Both sides reduce to the same expression. Take `⟨G, hG, hGne, hGeig⟩` from `E_lift (fun t => E_L E (r + s) r₁ t) (fun t => E_L E r r₁ t) constant_term_zero_eq E_LL (An.ctn r₁ φ.1) B hadd hsm c₁ 0 hBL F' hF'2 hF'ne hF'3`. Use `⟨G, hset ▸ hG, hGne, fun t g => ?_⟩` and prove the remaining obligations. Use `congrFun (hGeig t) g` as an intermediate fact. Rewrite `this` using `[E_L_apply, add_zero]`.

Conclude with `this`.
-/
theorem exp_left (hD : Dict) (hT : FinTr) {r s : ℕ} (hr : 0 < r) (hs : 0 < s) (φ : Sm E (r + s)) (hφ : IsAutForm φ)
    (τs : Finset ℝ) (a : ℝ → ℂ) (F : GA E (r + s) → ℂ)
    (hF : ∀ g, F g = ∑ t ∈ τs, a t * An.ctn r φ.1 (aT E (r + s) r t * g))
    (ψ : Sm E r) (hψ : IsAutForm ψ) (m₂ : GA E s) (h : GA E (r + s))
    (hψF : ∀ m₁, ψ.1 m₁ = F (lev (Ad E) r s (m₁, m₂) * h)) :
    ∀ r₁, 0 < r₁ → r₁ < r → ∀ c₁ ∈ Exp r₁ ψ.1, c₁ ∈ Exp r₁ φ.1 := by
  intro r₁ h0 h1 c₁ hc₁
  obtain ⟨F', hF'span, hF'ne, hF'eig⟩ := (E_exp_iff hD ψ hψ h0 h1 c₁).1 hc₁
  refine (E_exp_iff hD φ hφ h0 (by omega) c₁).2 ?_
  have hφc : Continuous φ.1 := GlobalTheory.CuspRep.ContAut.continuous_of_isOpen_stab E _ φ hφ.level
  have hcr₁ : Continuous (An.ctn r₁ φ.1) := E_cont_ctn r₁ hφc hφ.left
  have hset : (Set.range fun t => E_L E (r + s) r₁ t (An.ctn r₁ φ.1)) =
      Set.range fun t : ℝ => fun g => An.ctn r₁ φ.1 (aT E (r + s) r₁ t * g) := rfl
  have hfd := hT E (r + s) φ hφ r₁ h0 (by omega) _ ((hD E (r + s)).2.2.2 φ hφ r₁ h0 (by omega)).1
  rw [← hset] at hfd
  have := hfd
  have key := E_key_left h1 φ hφ τs a F hF ψ.1 m₂ h hψF
  have hP := E_cont_join (E := E) (n := r + s) (S := {r₁, r}) r₁
  set B := E_B (fun b : {x : PPos (r + s) {r₁, r} // ¬ IsTop r₁ x} → Ad E =>
        (parGL (joinPos (r := r₁) 0 b) : GA E (r + s)))
      (fun t (m : GA E r) => aT E (r + s) r t * (lev (Ad E) r s (m, m₂) * h))
      ((E_vol E r r₁)⁻¹ * ((E_vol E (r + s) r)⁻¹ * E_vol E (r + s) r₁)) τs a with hBdef
  have hcs : ∀ w ∈ Submodule.span ℂ (Set.range fun t => E_L E (r + s) r₁ t (An.ctn r₁ φ.1)), Continuous w := by
    rw [hset]; exact E_cont_span r₁ hcr₁
  have hadd : ∀ v ∈ Submodule.span ℂ (Set.range fun t => E_L E (r + s) r₁ t (An.ctn r₁ φ.1)),
      ∀ w ∈ Submodule.span ℂ (Set.range fun t => E_L E (r + s) r₁ t (An.ctn r₁ φ.1)), B (v + w) = B v + B w :=
    fun v hv w hw => E_B_add hP _ _ _ _ (hcs v hv) (hcs w hw)
  have hsm : ∀ (c : ℂ), ∀ w ∈ Submodule.span ℂ (Set.range fun t => E_L E (r + s) r₁ t (An.ctn r₁ φ.1)),
      B (c • w) = c • B w := fun c w _ => E_B_smul _ _ _ _ _ c w
  have hBL : ∀ (t : ℝ), ∀ w ∈ Submodule.span ℂ (Set.range fun t => E_L E (r + s) r₁ t (An.ctn r₁ φ.1)),
      B (E_L E (r + s) r₁ t w) = Complex.exp (0 * t) • E_L E r r₁ t (B w) := fun t w _ => by
    rw [hBdef, E_hB_left h1, zero_mul, Complex.exp_zero, one_smul]
  have hF'2 : F' ∈ Submodule.span ℂ (Set.range fun t => E_L E r r₁ t (B (An.ctn r₁ φ.1))) := by
    rw [← key]; exact hF'span
  have hF'3 : ∀ t : ℝ, E_L E r r₁ t F' = Complex.exp (c₁ * t) • F' := fun t => by
    funext g; rw [E_L_apply, hF'eig t g]; rfl
  obtain ⟨G, hG, hGne, hGeig⟩ := E_lift (fun t => E_L E (r + s) r₁ t) (fun t => E_L E r r₁ t) constant_term_zero_eq E_LL
    (An.ctn r₁ φ.1) B hadd hsm c₁ 0 hBL F' hF'2 hF'ne hF'3
  refine ⟨G, hset ▸ hG, hGne, fun t g => ?_⟩
  have := congrFun (hGeig t) g
  rw [E_L_apply, add_zero] at this
  exact this

variable {r s : ℕ}

/- English proof (translation)
Establish `hpq : r < r + r₂` using `by omega`. Establish `hpos : ∀ x : PPos (r + s) {r, r + r₂}, ¬ IsTop r x → ((x.1.1 : ℕ) < r ↔ (x.1.2 : ℕ) < r)` using `fun x hx => by`. Use `E_pos_bot hpq x hx` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hv : (E_vol E (r + s) r)⁻¹ * E_vol E (r + s) (r + r₂) ≠ 0` using `mul_ne_zero (inv_ne_zero (E_vol_ne _ _)) (E_vol_ne _ _)`.

Establish `key : ∀ z, ∫ b, F (parGL (joinPos (r` using `r) 0 b) * z) ∂(Measure.pi fun _ : {x : PPos (r + s) {r, r + r₂} // ¬ IsTop r x} => boxMeasure E) = ((E_vol E (r + s) r)⁻¹ * E_vol E (r + s) (r + r₂)) * E_B (fun b : {x : PPos (r + s) {r, r + r₂} // ¬ IsTop (r + r₂) x} → Ad E => (parGL (joinPos (r := r + r₂) 0 b) : GA E (r + s))) …`. Introduce `z`. Rewrite using `[E_int_right hr₂ φ hφ τs a F hF z]`. Simplify using `only [E_B]`. Rewrite using `[one_mul, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun u _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `eig : ∫ b, F (parGL (joinPos (r` using `r) 0 b) * (aT E (r + s) r t * z)) ∂(Measure.pi fun _ : {x : PPos (r + s) {r, r + r₂} // ¬ IsTop r x} => boxMeasure E) = Complex.exp (c * t) * ∫ b, F (parGL (joinPos (r := r) 0 b) * z) ∂(Measure.pi fun _ : {x : PPos (r + s) {r, r + r₂} // ¬ IsTop r x} => boxMeasure E) := by`. Rewrite using `[← integral_const_mul]`. Use `congr 1`.

Use function extensionality and compare the values at `b`. Rewrite using `[← mul_assoc, ← aT_comm_parGL _ _ _ _ hpos, mul_assoc, hc]`. Apply `mul_left_cancel₀ hv` to reduce the goal to its premises. Rewrite using `[← key, mul_left_comm, ← key, eig]`.
-/
theorem E_G_base {r₂ : ℕ} (hr₂ : 0 < r₂) (φ : Sm E (r + s)) (hφ : IsAutForm φ) (τs : Finset ℝ) (a : ℝ → ℂ)
    (F : GA E (r + s) → ℂ) (hF : ∀ g, F g = ∑ t ∈ τs, a t * An.ctn r φ.1 (aT E (r + s) r t * g)) (c : ℂ)
    (hc : ∀ (t : ℝ) g, F (aT E (r + s) r t * g) = Complex.exp (c * t) * F g) (t : ℝ) (z : GA E (r + s)) :
    E_B (fun b : {x : PPos (r + s) {r, r + r₂} // ¬ IsTop (r + r₂) x} → Ad E =>
        (parGL (joinPos (r := r + r₂) 0 b) : GA E (r + s)))
      (fun t (z : GA E (r + s)) => aT E (r + s) r t * z) 1 τs a (An.ctn (r + r₂) φ.1) (aT E (r + s) r t * z) =
    Complex.exp (c * t) * E_B (fun b : {x : PPos (r + s) {r, r + r₂} // ¬ IsTop (r + r₂) x} → Ad E =>
        (parGL (joinPos (r := r + r₂) 0 b) : GA E (r + s)))
      (fun t (z : GA E (r + s)) => aT E (r + s) r t * z) 1 τs a (An.ctn (r + r₂) φ.1) z := by
  have hpq : r < r + r₂ := by omega
  have hpos : ∀ x : PPos (r + s) {r, r + r₂}, ¬ IsTop r x → ((x.1.1 : ℕ) < r ↔ (x.1.2 : ℕ) < r) := fun x hx => by
    have := E_pos_bot hpq x hx
    omega
  have hv : (E_vol E (r + s) r)⁻¹ * E_vol E (r + s) (r + r₂) ≠ 0 :=
    mul_ne_zero (inv_ne_zero (E_vol_ne _ _)) (E_vol_ne _ _)
  have key : ∀ z, ∫ b, F (parGL (joinPos (r := r) 0 b) * z)
      ∂(Measure.pi fun _ : {x : PPos (r + s) {r, r + r₂} // ¬ IsTop r x} => boxMeasure E) =
      ((E_vol E (r + s) r)⁻¹ * E_vol E (r + s) (r + r₂)) *
        E_B (fun b : {x : PPos (r + s) {r, r + r₂} // ¬ IsTop (r + r₂) x} → Ad E =>
          (parGL (joinPos (r := r + r₂) 0 b) : GA E (r + s)))
        (fun t (z : GA E (r + s)) => aT E (r + s) r t * z) 1 τs a (An.ctn (r + r₂) φ.1) z := by
    intro z
    rw [E_int_right hr₂ φ hφ τs a F hF z]
    simp only [E_B]
    rw [one_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    ring
  have eig : ∫ b, F (parGL (joinPos (r := r) 0 b) * (aT E (r + s) r t * z))
      ∂(Measure.pi fun _ : {x : PPos (r + s) {r, r + r₂} // ¬ IsTop r x} => boxMeasure E) =
      Complex.exp (c * t) * ∫ b, F (parGL (joinPos (r := r) 0 b) * z)
        ∂(Measure.pi fun _ : {x : PPos (r + s) {r, r + r₂} // ¬ IsTop r x} => boxMeasure E) := by
    rw [← integral_const_mul]
    congr 1
    funext b
    rw [← mul_assoc, ← aT_comm_parGL _ _ _ _ hpos, mul_assoc, hc]
  apply mul_left_cancel₀ hv
  rw [← key, mul_left_comm, ← key, eig]

/- English proof (translation)
Establish `hφc : Continuous φ.1` using `GlobalTheory.CuspRep.ContAut.continuous_of_isOpen_stab E _ φ hφ.level`. Establish `hcr : Continuous (An.ctn (r + r₂) φ.1)` using `E_cont_ctn (r + r₂) hφc hφ.left`. Establish `hset : (Set.range fun u => E_L E (r + s) (r + r₂) u (An.ctn (r + r₂) φ.1)) = Set.range fun u : ℝ => fun g => An.ctn (r + r₂) φ.1 (aT E (r + s) (r + r₂) u * g)` using `rfl`. Establish `hcs : ∀ w ∈ Submodule.span ℂ (Set.range fun u => E_L E (r + s) (r + r₂) u (An.ctn (r + r₂) φ.1)), Continuous w`. Rewrite using `[hset]`.

Conclude with `E_cont_span _ hcr`. Establish `hP` using `E_cont_join (E := E) (n := r + s) (S := {r, r + r₂}) (r + r₂)`. Introduce `w hw`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨u, rfl⟩` from `hx`. Introduce `z`. Rewrite using `[E_G_shift hr₂, E_G_shift hr₂, ← mul_assoc, aT_comm, mul_assoc, E_G_base hr₂ φ hφ τs a F hF c hc]`. Consider the case `zero`. Introduce `z`.

Simplify using `[E_B]`. Consider the case `add x y hx hy ihx ihy`. Introduce `z`. Rewrite using `[E_B_add hP _ _ _ _ (hcs x hx) (hcs y hy)]`. Simplify using `only [Pi.add_apply]`.

Rewrite using `[ihx, ihy, mul_add]`. Consider the case `smul d x _ ih`. Introduce `z`. Rewrite using `[E_B_smul]`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`.

Rewrite using `[ih]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eisenstein_constant_term_span {r₂ : ℕ} (hr₂ : 0 < r₂) (φ : Sm E (r + s)) (hφ : IsAutForm φ) (τs : Finset ℝ) (a : ℝ → ℂ)
    (F : GA E (r + s) → ℂ) (hF : ∀ g, F g = ∑ t ∈ τs, a t * An.ctn r φ.1 (aT E (r + s) r t * g)) (c : ℂ)
    (hc : ∀ (t : ℝ) g, F (aT E (r + s) r t * g) = Complex.exp (c * t) * F g) (t : ℝ) :
    ∀ w ∈ Submodule.span ℂ (Set.range fun u => E_L E (r + s) (r + r₂) u (An.ctn (r + r₂) φ.1)), ∀ z,
      E_B (fun b : {x : PPos (r + s) {r, r + r₂} // ¬ IsTop (r + r₂) x} → Ad E =>
          (parGL (joinPos (r := r + r₂) 0 b) : GA E (r + s)))
        (fun t (z : GA E (r + s)) => aT E (r + s) r t * z) 1 τs a w (aT E (r + s) r t * z) =
      Complex.exp (c * t) * E_B (fun b : {x : PPos (r + s) {r, r + r₂} // ¬ IsTop (r + r₂) x} → Ad E =>
          (parGL (joinPos (r := r + r₂) 0 b) : GA E (r + s)))
        (fun t (z : GA E (r + s)) => aT E (r + s) r t * z) 1 τs a w z := by
  have hφc : Continuous φ.1 := GlobalTheory.CuspRep.ContAut.continuous_of_isOpen_stab E _ φ hφ.level
  have hcr : Continuous (An.ctn (r + r₂) φ.1) := E_cont_ctn (r + r₂) hφc hφ.left
  have hset : (Set.range fun u => E_L E (r + s) (r + r₂) u (An.ctn (r + r₂) φ.1)) =
      Set.range fun u : ℝ => fun g => An.ctn (r + r₂) φ.1 (aT E (r + s) (r + r₂) u * g) := rfl
  have hcs : ∀ w ∈ Submodule.span ℂ (Set.range fun u => E_L E (r + s) (r + r₂) u (An.ctn (r + r₂) φ.1)),
      Continuous w := by
    rw [hset]; exact E_cont_span _ hcr
  have hP := E_cont_join (E := E) (n := r + s) (S := {r, r + r₂}) (r + r₂)
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, rfl⟩ := hx
    intro z
    rw [E_G_shift hr₂, E_G_shift hr₂, ← mul_assoc, aT_comm, mul_assoc, E_G_base hr₂ φ hφ τs a F hF c hc]
  | zero =>
    intro z
    simp [E_B]
  | add x y hx hy ihx ihy =>
    intro z
    rw [E_B_add hP _ _ _ _ (hcs x hx) (hcs y hy)]
    simp only [Pi.add_apply]
    rw [ihx, ihy, mul_add]
  | smul d x _ ih =>
    intro z
    rw [E_B_smul]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [ih]
    ring

/- English proof (translation)
Use function extensionality and compare the values at `m₂`. Use `set y := lev (Ad E) r s (m₁, m₂) * h with hy`. Establish `e2 : ∀ A : UPos s r₂ → Ad E, ψ (unipGL A * m₂) = F (parGL (joinPos (r` using `r) 0 fun q => A ((eR r s r₂ hr₂).symm q)) * y) := by`. Introduce `A`. Rewrite using `[hψF]`.

Use `congr 1`. Establish `e : lev (Ad E) r s (m₁, unipGL A * m₂) = lev (Ad E) r s (1, unipGL A) * lev (Ad E) r s (m₁, m₂)`. Rewrite using `[← map_mul, Prod.mk_mul_mk, one_mul]`. Rewrite using `[e, lev_unipGL_right r s r₂ hr₂, mul_assoc]`. Rewrite using `[E_ctn_eq, constantTerm_eq_integral]`.

Simplify using `only [e2]`. Rewrite using `[← integral_box_reindex (eR r s r₂ hr₂) (fun b => F (parGL (joinPos (r := r) 0 b) * y)), E_int_right hr₂ φ hφ τs a F hF y]`. Simplify using `only [E_B]`. Rewrite using `[Finset.mul_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem E_key_right {r₂ : ℕ} (hr₂ : 0 < r₂) (φ : Sm E (r + s)) (hφ : IsAutForm φ) (τs : Finset ℝ) (a : ℝ → ℂ)
    (F : GA E (r + s) → ℂ) (hF : ∀ g, F g = ∑ t ∈ τs, a t * An.ctn r φ.1 (aT E (r + s) r t * g))
    (ψ : GA E s → ℂ) (m₁ : GA E r) (h : GA E (r + s)) (hψF : ∀ m₂, ψ m₂ = F (lev (Ad E) r s (m₁, m₂) * h)) :
    An.ctn r₂ ψ = E_B (fun b : {x : PPos (r + s) {r, r + r₂} // ¬ IsTop (r + r₂) x} → Ad E =>
        (parGL (joinPos (r := r + r₂) 0 b) : GA E (r + s)))
      (fun t (m : GA E s) => aT E (r + s) r t * (lev (Ad E) r s (m₁, m) * h))
      ((E_vol E s r₂)⁻¹ * ((E_vol E (r + s) r)⁻¹ * E_vol E (r + s) (r + r₂))) τs a (An.ctn (r + r₂) φ.1) := by
  funext m₂
  set y := lev (Ad E) r s (m₁, m₂) * h with hy
  have e2 : ∀ A : UPos s r₂ → Ad E, ψ (unipGL A * m₂) =
      F (parGL (joinPos (r := r) 0 fun q => A ((eR r s r₂ hr₂).symm q)) * y) := by
    intro A
    rw [hψF]
    congr 1
    have e : lev (Ad E) r s (m₁, unipGL A * m₂) = lev (Ad E) r s (1, unipGL A) * lev (Ad E) r s (m₁, m₂) := by
      rw [← map_mul, Prod.mk_mul_mk, one_mul]
    rw [e, lev_unipGL_right r s r₂ hr₂, mul_assoc]
  rw [E_ctn_eq, constantTerm_eq_integral]
  simp only [e2]
  rw [← integral_box_reindex (eR r s r₂ hr₂) (fun b => F (parGL (joinPos (r := r) 0 b) * y)),
    E_int_right hr₂ φ hφ τs a F hF y]
  simp only [E_B]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  ring

/- English proof (translation)
Introduce `r₂ h0 h1 c₂ hc₂`. Take `⟨F', hF'span, hF'ne, hF'eig⟩` from `(E_exp_iff hD ψ hψ h0 h1 c₂).1 hc₂`. Use `(E_exp_iff hD φ hφ (by omega) (by omega) (c + c₂)).2 ?_` and prove the remaining obligations. Establish `hφc : Continuous φ.1` using `GlobalTheory.CuspRep.ContAut.continuous_of_isOpen_stab E _ φ hφ.level`. Establish `hcr : Continuous (An.ctn (r + r₂) φ.1)` using `E_cont_ctn (r + r₂) hφc hφ.left`.

Establish `hset : (Set.range fun t => E_L E (r + s) (r + r₂) t (An.ctn (r + r₂) φ.1)) = Set.range fun t : ℝ => fun g => An.ctn (r + r₂) φ.1 (aT E (r + s) (r + r₂) t * g)` using `rfl`. Establish `hfd` using `hT E (r + s) φ hφ (r + r₂) (by omega) (by omega) _ ((hD E (r + s)).2.2.2 φ hφ (r + r₂) (by omega) (by omega)).1`. Rewrite `hfd` using `[← hset]`. Use `hfd` as an intermediate fact. Establish `key` using `E_key_right h0 φ hφ τs a F hF ψ.1 m₁ h hψF`.

Establish `hP` using `E_cont_join (E := E) (n := r + s) (S := {r, r + r₂}) (r + r₂)`. Use `set B := E_B (fun b : {x : PPos (r + s) {r, r + r₂} // ¬ IsTop (r + r₂) x} → Ad E => (parGL (joinPos (r := r + r₂) 0 b) : GA E (r + s))) (fun t (m : GA E s) => aT E (r + s) r t * (lev (Ad E) r s (m₁, m) * h)) ((E_vol E s r₂)⁻¹ * ((E_vol E (r + s) r)⁻¹ * E_vol E (r + s) (r + r₂))) …`. Establish `hcs : ∀ w ∈ Submodule.span ℂ (Set.range fun t => E_L E (r + s) (r + r₂) t (An.ctn (r + r₂) φ.1)), Continuous w`. Rewrite using `[hset]`. Conclude with `E_cont_span (r + r₂) hcr`.

Establish `hadd : ∀ v ∈ Submodule.span ℂ (Set.range fun t => E_L E (r + s) (r + r₂) t (An.ctn (r + r₂) φ.1)), ∀ w ∈ Submodule.span ℂ (Set.range fun t => E_L E (r + s) (r + r₂) t (An.ctn (r + r₂) φ.1)), B (v + w) = B v + B w` using `fun v hv w hw => E_B_add hP _ _ _ _ (hcs v hv) (hcs w hw)`. Establish `hsm : ∀ (d : ℂ), ∀ w ∈ Submodule.span ℂ (Set.range fun t => E_L E (r + s) (r + r₂) t (An.ctn (r + r₂) φ.1)), B (d • w) = d • B w` using `fun d w _ => E_B_smul _ _ _ _ _ d w`. Establish `hBL : ∀ (t : ℝ), ∀ w ∈ Submodule.span ℂ (Set.range fun t => E_L E (r + s) (r + r₂) t (An.ctn (r + r₂) φ.1)), B (E_L E (r + s) (r + r₂) t w) = Complex.exp (c * t) • E_L E s r₂ t (B w)` using `fun t w hw => by`. Use function extensionality and compare the values at `m₂`. Establish `eB : ∀ (f : GA E (r + s) → ℂ) (m : GA E s), B f m = ((E_vol E s r₂)⁻¹ * ((E_vol E (r + s) r)⁻¹ * E_vol E (r + s) (r + r₂))) * E_B (fun b : {x : PPos (r + s) {r, r + r₂} // ¬ IsTop (r + r₂) x} → Ad E => (parGL (joinPos (r` using `r + r₂) 0 b) : GA E (r + s))) (fun t (z : GA E (r + s)) => aT E (r + s) r t * z) 1 τs a f (lev (Ad E) r s (m₁, m) * h) := by`.

Introduce `f m`. Simplify using `only [hBdef, E_B, one_mul]`. Rewrite using `[Pi.smul_apply, E_L_apply, eB, eB, E_G_shift h0, E_aT_right h1.le, eisenstein_constant_term_span h0 φ hφ τs a F hF c hc t w hw, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hF'2 : F' ∈ Submodule.span ℂ (Set.range fun t => E_L E s r₂ t (B (An.ctn (r + r₂) φ.1)))`.

Rewrite using `[← key]`. Conclude with `hF'span`. Establish `hF'3 : ∀ t : ℝ, E_L E s r₂ t F' = Complex.exp (c₂ * t) • F'` using `fun t => by`. Use function extensionality and compare the values at `g`. Rewrite using `[E_L_apply, hF'eig t g]`.

Both sides reduce to the same expression. Take `⟨G, hG, hGne, hGeig⟩` from `E_lift (fun t => E_L E (r + s) (r + r₂) t) (fun t => E_L E s r₂ t) constant_term_zero_eq E_LL (An.ctn (r + r₂) φ.1) B hadd hsm c₂ c hBL F' hF'2 hF'ne hF'3`. Use `⟨G, hset ▸ hG, hGne, fun t g => ?_⟩` and prove the remaining obligations. Use `congrFun (hGeig t) g` as an intermediate fact. Rewrite `this` using `[E_L_apply, add_comm c₂ c]`.

Conclude with `this`.
-/
theorem exp_right (hD : Dict) (hT : FinTr) {r s : ℕ} (hr : 0 < r) (hs : 0 < s) (φ : Sm E (r + s)) (hφ : IsAutForm φ)
    (τs : Finset ℝ) (a : ℝ → ℂ) (F : GA E (r + s) → ℂ)
    (hF : ∀ g, F g = ∑ t ∈ τs, a t * An.ctn r φ.1 (aT E (r + s) r t * g)) (c : ℂ)
    (hc : ∀ (t : ℝ) g, F (aT E (r + s) r t * g) = Complex.exp (c * t) * F g)
    (ψ : Sm E s) (hψ : IsAutForm ψ) (m₁ : GA E r) (h : GA E (r + s))
    (hψF : ∀ m₂, ψ.1 m₂ = F (lev (Ad E) r s (m₁, m₂) * h)) :
    ∀ r₂, 0 < r₂ → r₂ < s → ∀ c₂ ∈ Exp r₂ ψ.1, c + c₂ ∈ Exp (r + r₂) φ.1 := by
  intro r₂ h0 h1 c₂ hc₂
  obtain ⟨F', hF'span, hF'ne, hF'eig⟩ := (E_exp_iff hD ψ hψ h0 h1 c₂).1 hc₂
  refine (E_exp_iff hD φ hφ (by omega) (by omega) (c + c₂)).2 ?_
  have hφc : Continuous φ.1 := GlobalTheory.CuspRep.ContAut.continuous_of_isOpen_stab E _ φ hφ.level
  have hcr : Continuous (An.ctn (r + r₂) φ.1) := E_cont_ctn (r + r₂) hφc hφ.left
  have hset : (Set.range fun t => E_L E (r + s) (r + r₂) t (An.ctn (r + r₂) φ.1)) =
      Set.range fun t : ℝ => fun g => An.ctn (r + r₂) φ.1 (aT E (r + s) (r + r₂) t * g) := rfl
  have hfd := hT E (r + s) φ hφ (r + r₂) (by omega) (by omega) _
    ((hD E (r + s)).2.2.2 φ hφ (r + r₂) (by omega) (by omega)).1
  rw [← hset] at hfd
  have := hfd
  have key := E_key_right h0 φ hφ τs a F hF ψ.1 m₁ h hψF
  have hP := E_cont_join (E := E) (n := r + s) (S := {r, r + r₂}) (r + r₂)
  set B := E_B (fun b : {x : PPos (r + s) {r, r + r₂} // ¬ IsTop (r + r₂) x} → Ad E =>
        (parGL (joinPos (r := r + r₂) 0 b) : GA E (r + s)))
      (fun t (m : GA E s) => aT E (r + s) r t * (lev (Ad E) r s (m₁, m) * h))
      ((E_vol E s r₂)⁻¹ * ((E_vol E (r + s) r)⁻¹ * E_vol E (r + s) (r + r₂))) τs a with hBdef
  have hcs : ∀ w ∈ Submodule.span ℂ (Set.range fun t => E_L E (r + s) (r + r₂) t (An.ctn (r + r₂) φ.1)),
      Continuous w := by
    rw [hset]; exact E_cont_span (r + r₂) hcr
  have hadd : ∀ v ∈ Submodule.span ℂ (Set.range fun t => E_L E (r + s) (r + r₂) t (An.ctn (r + r₂) φ.1)),
      ∀ w ∈ Submodule.span ℂ (Set.range fun t => E_L E (r + s) (r + r₂) t (An.ctn (r + r₂) φ.1)),
      B (v + w) = B v + B w :=
    fun v hv w hw => E_B_add hP _ _ _ _ (hcs v hv) (hcs w hw)
  have hsm : ∀ (d : ℂ), ∀ w ∈ Submodule.span ℂ (Set.range fun t => E_L E (r + s) (r + r₂) t (An.ctn (r + r₂) φ.1)),
      B (d • w) = d • B w := fun d w _ => E_B_smul _ _ _ _ _ d w
  have hBL : ∀ (t : ℝ), ∀ w ∈ Submodule.span ℂ (Set.range fun t => E_L E (r + s) (r + r₂) t (An.ctn (r + r₂) φ.1)),
      B (E_L E (r + s) (r + r₂) t w) = Complex.exp (c * t) • E_L E s r₂ t (B w) := fun t w hw => by
    funext m₂
    have eB : ∀ (f : GA E (r + s) → ℂ) (m : GA E s), B f m =
        ((E_vol E s r₂)⁻¹ * ((E_vol E (r + s) r)⁻¹ * E_vol E (r + s) (r + r₂))) *
        E_B (fun b : {x : PPos (r + s) {r, r + r₂} // ¬ IsTop (r + r₂) x} → Ad E =>
          (parGL (joinPos (r := r + r₂) 0 b) : GA E (r + s)))
          (fun t (z : GA E (r + s)) => aT E (r + s) r t * z) 1 τs a f (lev (Ad E) r s (m₁, m) * h) := by
      intro f m
      simp only [hBdef, E_B, one_mul]
    rw [Pi.smul_apply, E_L_apply, eB, eB, E_G_shift h0, E_aT_right h1.le, eisenstein_constant_term_span h0 φ hφ τs a F hF c hc t w hw,
      smul_eq_mul]
    ring
  have hF'2 : F' ∈ Submodule.span ℂ (Set.range fun t => E_L E s r₂ t (B (An.ctn (r + r₂) φ.1))) := by
    rw [← key]; exact hF'span
  have hF'3 : ∀ t : ℝ, E_L E s r₂ t F' = Complex.exp (c₂ * t) • F' := fun t => by
    funext g; rw [E_L_apply, hF'eig t g]; rfl
  obtain ⟨G, hG, hGne, hGeig⟩ := E_lift (fun t => E_L E (r + s) (r + r₂) t) (fun t => E_L E s r₂ t) constant_term_zero_eq E_LL
    (An.ctn (r + r₂) φ.1) B hadd hsm c₂ c hBL F' hF'2 hF'ne hF'3
  refine ⟨G, hset ▸ hG, hGne, fun t g => ?_⟩
  have := congrFun (hGeig t) g
  rw [E_L_apply, add_comm c₂ c] at this
  exact this

end PositivityTheory.Rg.Rs.SliceClasses

end
