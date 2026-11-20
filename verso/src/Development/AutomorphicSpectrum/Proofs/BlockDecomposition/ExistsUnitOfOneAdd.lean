import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.FormQuasiInvariantMirabolic

noncomputable section

open MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa
  GroundTheory.Automorphic.Spherical PositivityTheory.JacquetShalikaLocal
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.SatakeBessel

/- English proof (translation)
Use `set S : V := ∑ j ∈ Finset.range T, w j with hS`. Establish `e1 : B v S = ∑ j ∈ Finset.range T, B (w j) (w j)`. Rewrite using `[hS, map_sum]`. Conclude with `Finset.sum_congr rfl fun j _ => h1 j`. Establish `e2 : B S v = ∑ j ∈ Finset.range T, B (w j) (w j)`.

Rewrite using `[hS, map_sum, LinearMap.sum_apply]`. Conclude with `Finset.sum_congr rfl fun j _ => h2 j`. Establish `e3 : B S S = ∑ j ∈ Finset.range T, B (w j) (w j)`. Establish `e5 : ∀ u, B S u = ∑ j ∈ Finset.range T, B (w j) u` using `fun u => by`. Rewrite using `[hS, map_sum, LinearMap.sum_apply]`.

Rewrite using `[e5]`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Rewrite using `[hS, map_sum, Finset.sum_eq_single i (fun j _ hj => h3 i j hj.symm) (fun h => absurd hi h)]`. Establish `h` using `hpsd (v - S)`. Establish `e4 : B (v - S) (v - S) = B v v - ∑ j ∈ Finset.range T, B (w j) (w j)`.

Simplify using `only [map_sub, LinearMap.sub_apply, e1, e2, e3]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h` using `[e4, Complex.sub_re, Complex.re_sum]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem bessel {V : Type} [AddCommGroup V] [Module ℂ V] (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)
    (hpsd : ∀ u, 0 ≤ (B u u).re) (v : V) (w : ℕ → V)
    (h1 : ∀ j, B v (w j) = B (w j) (w j)) (h2 : ∀ j, B (w j) v = B (w j) (w j))
    (h3 : ∀ i j, i ≠ j → B (w i) (w j) = 0) (T : ℕ) :
    ∑ j ∈ Finset.range T, (B (w j) (w j)).re ≤ (B v v).re := by
  set S : V := ∑ j ∈ Finset.range T, w j with hS
  have e1 : B v S = ∑ j ∈ Finset.range T, B (w j) (w j) := by
    rw [hS, map_sum]; exact Finset.sum_congr rfl fun j _ => h1 j
  have e2 : B S v = ∑ j ∈ Finset.range T, B (w j) (w j) := by
    rw [hS, map_sum, LinearMap.sum_apply]; exact Finset.sum_congr rfl fun j _ => h2 j
  have e3 : B S S = ∑ j ∈ Finset.range T, B (w j) (w j) := by
    have e5 : ∀ u, B S u = ∑ j ∈ Finset.range T, B (w j) u := fun u => by
      rw [hS, map_sum, LinearMap.sum_apply]
    rw [e5]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [hS, map_sum, Finset.sum_eq_single i (fun j _ hj => h3 i j hj.symm)
      (fun h => absurd hi h)]
  have h := hpsd (v - S)
  have e4 : B (v - S) (v - S) = B v v - ∑ j ∈ Finset.range T, B (w j) (w j) := by
    simp only [map_sub, LinearMap.sub_apply, e1, e2, e3]; ring
  rw [e4, Complex.sub_re, Complex.re_sum] at h
  linarith

section Diag

variable {F : Type} [Field F] {n : ℕ}

def dg (i₀ : Fin n) (s : Fˣ) : GL (Fin n) F := diagGL F n (Pi.mulSingle i₀ s)

/- English proof (translation)
Rewrite using `[dg, dg, ← map_mul, ← map_mul, mul_comm]`.
-/
theorem dg_comm (i₀ : Fin n) (s t : Fˣ) : dg i₀ s * dg i₀ t = dg i₀ t * dg i₀ s := by
  rw [dg, dg, ← map_mul, ← map_mul, mul_comm]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_dg (i₀ : Fin n) (s : Fˣ) : ((dg i₀ s : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
    diagonal fun i => ((Pi.mulSingle i₀ s : Fin n → Fˣ) i : F) := rfl

/- English proof (translation)
Rewrite using `[coe_dg, det_diagonal, Finset.prod_eq_single i₀ (fun i _ hi => by simp [Pi.mulSingle_eq_of_ne hi]) (fun h => absurd (Finset.mem_univ _) h)]`. Simplify using the standard rewrite rules.
-/
theorem det_dg (i₀ : Fin n) (s : Fˣ) :
    ((dg i₀ s : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = s := by
  rw [coe_dg, det_diagonal, Finset.prod_eq_single i₀ (fun i _ hi => by simp [Pi.mulSingle_eq_of_ne hi])
    (fun h => absurd (Finset.mem_univ _) h)]
  simp

/- English proof (translation)
Establish `key : ∀ i j : Fin n, 1 ≤ (i : ℕ) ∨ 1 < (j : ℕ) → (dg i₀ s : GL (Fin n) F) i j = (1 : Matrix (Fin n) (Fin n) F) i j`. Introduce `i j hij`. Express the relevant statement in the definitionally equal form `((dg i₀ s : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j = _`. Rewrite using `[coe_dg, diagonal_apply, Matrix.one_apply]`. Distinguish the cases in `h : i = j`.

Substitute `h` using the available equality. Establish `: i ≠ i₀` using `fun e => by subst e; omega`. Simplify using `[Pi.mulSingle_eq_of_ne this]`. Simplify using `[h]`. Conclude with `⟨fun i j hi => key i j (Or.inl hi), fun i j hj => key i j (Or.inr hj)⟩`.
-/
theorem inP_dg (i₀ : Fin n) (h₀ : (i₀ : ℕ) = 0) (s : Fˣ) : inP 1 (dg i₀ s : GL (Fin n) F) := by
  have key : ∀ i j : Fin n, 1 ≤ (i : ℕ) ∨ 1 < (j : ℕ) →
      (dg i₀ s : GL (Fin n) F) i j = (1 : Matrix (Fin n) (Fin n) F) i j := by
    intro i j hij
    change ((dg i₀ s : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j = _
    rw [coe_dg, diagonal_apply, Matrix.one_apply]
    by_cases h : i = j
    · subst h
      have : i ≠ i₀ := fun e => by subst e; omega
      simp [Pi.mulSingle_eq_of_ne this]
    · simp [h]
  exact ⟨fun i j hi => key i j (Or.inl hi), fun i j hj => key i j (Or.inr hj)⟩

/- English proof (translation)
Use `Units.ext ?_` and prove the remaining obligations. Rewrite using `[Units.val_mul, Units.val_mul]`. Express the relevant statement in the definitionally equal form `_ * (1 + cM n 0 x) = (1 + cM n 0 _) * _`. Rewrite using `[coe_dg, mul_add, add_mul, mul_one, one_mul]`. Use `congr 1`.

Use extensionality with `i j`. Rewrite using `[Matrix.diagonal_mul, Matrix.mul_diagonal]`. Simplify using `only [cM, Matrix.of_apply]`. Distinguish the cases in `h : (j : ℕ) = 0 + 1 ∧ (i : ℕ) < 0 + 1`. Rewrite using `[dif_pos h, dif_pos h]`.

Establish `e1 : i = i₀` using `Fin.ext (by omega)`. Establish `e2 : j ≠ i₀` using `fun e => by subst e; omega`. Substitute `e1` using the available equality. Simplify using `[Pi.mulSingle_eq_of_ne e2]`. Rewrite using `[dif_neg h, dif_neg h]`.

Simplify using the standard rewrite rules.
-/
theorem dg_mul_col (hn : 1 < n) (i₀ : Fin n) (h₀ : (i₀ : ℕ) = 0) (s : Fˣ) (x : Fin (0 + 1) → F) :
    dg i₀ s * col n 0 x = col n 0 (fun i => (s : F) * x i) * dg i₀ s := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul]
  change _ * (1 + cM n 0 x) = (1 + cM n 0 _) * _
  rw [coe_dg, mul_add, add_mul, mul_one, one_mul]
  congr 1
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  simp only [cM, Matrix.of_apply]
  by_cases h : (j : ℕ) = 0 + 1 ∧ (i : ℕ) < 0 + 1
  · rw [dif_pos h, dif_pos h]
    have e1 : i = i₀ := Fin.ext (by omega)
    have e2 : j ≠ i₀ := fun e => by subst e; omega
    subst e1
    simp [Pi.mulSingle_eq_of_ne e2]
  · rw [dif_neg h, dif_neg h]; simp

end Diag

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

/- English proof (translation)
Rewrite using `[torusPow, dg]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Distinguish the cases in `h : i = i₀`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[Pi.single_eq_of_ne h, Pi.mulSingle_eq_of_ne h]`.
-/
theorem torusPow_eq_dg (i₀ : Fin n) (j : ℕ) :
    torusPow F n (Pi.single i₀ (j : ℤ)) = dg i₀ (uniformizerUnit F ^ j) := by
  rw [torusPow, dg]
  congr 1
  funext i
  by_cases h : i = i₀
  · subst h; simp
  · simp [Pi.single_eq_of_ne h, Pi.mulSingle_eq_of_ne h]

/- English proof (translation)
Establish `h` using `diagGL_map_mem_integralGL F n (Pi.mulSingle i₀ e)`. Establish `e' : (fun i => Units.map (𝒪[F]).subtype.toMonoidHom ((Pi.mulSingle i₀ e : Fin n → (𝒪[F])ˣ) i)) = Pi.mulSingle i₀ (Units.map (𝒪[F]).subtype.toMonoidHom e)`. Use function extensionality and compare the values at `i`. Distinguish the cases in `hi : i = i₀`. Substitute `hi` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[Pi.mulSingle_eq_of_ne hi]`. Rewrite `h` using `[e']`. Conclude with `h`.
-/
theorem dg_mem_integralGL (i₀ : Fin n) (e : (𝒪[F])ˣ) :
    (dg i₀ (Units.map (𝒪[F]).subtype.toMonoidHom e) : GL (Fin n) F) ∈ integralGL F n := by
  have h := diagGL_map_mem_integralGL F n (Pi.mulSingle i₀ e)
  have e' : (fun i => Units.map (𝒪[F]).subtype.toMonoidHom ((Pi.mulSingle i₀ e : Fin n → (𝒪[F])ˣ) i)) =
      Pi.mulSingle i₀ (Units.map (𝒪[F]).subtype.toMonoidHom e) := by
    funext i
    by_cases hi : i = i₀
    · subst hi; simp
    · simp [Pi.mulSingle_eq_of_ne hi]
  rw [e'] at h
  exact h

def sc (s : Fˣ) : GL (Fin (0 + 1)) F := diagGL F (0 + 1) fun _ => s

/- English proof (translation)
Use extensionality with `i`. Simplify using `[sc, mulVec_diagonal]`.
-/
theorem sc_mulVec (s : Fˣ) (x : Fin (0 + 1) → F) :
    ((sc s : GL (Fin (0 + 1)) F) : Matrix (Fin (0 + 1)) (Fin (0 + 1)) F) *ᵥ x = fun i => (s : F) * x i := by
  ext i
  simp [sc, mulVec_diagonal]

/- English proof (translation)
Simplify using `[sc]`.
-/
theorem det_sc (s : Fˣ) :
    ((sc s : GL (Fin (0 + 1)) F) : Matrix (Fin (0 + 1)) (Fin (0 + 1)) F).det = s := by
  simp [sc]

/- English proof (translation)
Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩ i`. Simplify using `only [sc_mulVec]`. Conclude with `(h _).2 (hx i)`.

Introduce `hy`. Use `⟨fun i => ((s⁻¹ : Fˣ) : F) * y i, fun i => (h _).1 ?_, ?_⟩` and prove the remaining obligations. Simplify using `using hy i`. Simplify using `only [sc_mulVec]`. Use function extensionality and compare the values at `i`.

Simplify using the standard rewrite rules.
-/
theorem image_sc (s : Fˣ) (a b : ℕ)
    (h : ∀ x : F, (uniformizer F : F) ^ b * ((s : F) * x) ∈ 𝒪[F] ↔ (uniformizer F : F) ^ a * x ∈ 𝒪[F]) :
    (fun x => ((sc s : GL (Fin (0 + 1)) F) : Matrix (Fin (0 + 1)) (Fin (0 + 1)) F) *ᵥ x) '' lat F (0 + 1) a =
      lat F (0 + 1) b := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩ i
    simp only [sc_mulVec]
    exact (h _).2 (hx i)
  · intro hy
    refine ⟨fun i => ((s⁻¹ : Fˣ) : F) * y i, fun i => (h _).1 ?_, ?_⟩
    · simpa using hy i
    · simp only [sc_mulVec]
      funext i
      simp

/- English proof (translation)
Introduce `i j`. Express the relevant statement in the definitionally equal form `∃ t ∈ 𝒪[F], ((1 + cM n 0 y) - 1 : Matrix (Fin n) (Fin n) F) i j = _`. Rewrite using `[add_sub_cancel_left]`. Simplify using `only [cM, Matrix.of_apply]`. Distinguish the cases in `h : (j : ℕ) = 0 + 1 ∧ (i : ℕ) < 0 + 1`.

Rewrite using `[dif_pos h]`. Conclude with `hy _`. Rewrite using `[dif_neg h]; exact ⟨0, (𝒪[F]).zero_mem, by simp⟩`.
-/
theorem div_col (c : ℕ) (y : Fin (0 + 1) → F)
    (hy : ∀ i, ∃ t ∈ 𝒪[F], y i = (uniformizer F : F) ^ c * t) :
    Div c (((col n 0 y : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) - 1) := by
  intro i j
  change ∃ t ∈ 𝒪[F], ((1 + cM n 0 y) - 1 : Matrix (Fin n) (Fin n) F) i j = _
  rw [add_sub_cancel_left]
  simp only [cM, Matrix.of_apply]
  by_cases h : (j : ℕ) = 0 + 1 ∧ (i : ℕ) < 0 + 1
  · rw [dif_pos h]; exact hy _
  · rw [dif_neg h]; exact ⟨0, (𝒪[F]).zero_mem, by simp⟩

/- English proof (translation)
Establish `hp` using `irreducible_uniformizer F`. Establish `hm : uniformizer F * (⟨y, hy⟩ : 𝒪[F]) ∈ IsLocalRing.maximalIdeal 𝒪[F]` using `Ideal.mul_mem_right _ _ ((IsLocalRing.mem_maximalIdeal _).2 hp.not_isUnit)`. Establish `hu : IsUnit (1 + uniformizer F * (⟨y, hy⟩ : 𝒪[F]))`. Assume the negation of the conclusion as `hne`. Establish `h1 : (1 + uniformizer F * (⟨y, hy⟩ : 𝒪[F])) ∈ IsLocalRing.maximalIdeal 𝒪[F]` using `(IsLocalRing.mem_maximalIdeal _).2 hne`.

Establish `h2` using `(IsLocalRing.maximalIdeal 𝒪[F]).sub_mem h1 hm`. Rewrite `h2` using `[add_sub_cancel_right]`. Conclude with `(Ideal.ne_top_iff_one _).1 (IsLocalRing.maximalIdeal.isMaximal _).ne_top h2`. Take `⟨e, he⟩` from `hu`. Conclude with `⟨e, by rw [he]; rfl⟩`.
-/
theorem exists_unit_of_one_add (y : F) (hy : y ∈ 𝒪[F]) :
    ∃ e : (𝒪[F])ˣ, ((e : 𝒪[F]) : F) = 1 + (uniformizer F : F) * y := by
  have hp := irreducible_uniformizer F
  have hm : uniformizer F * (⟨y, hy⟩ : 𝒪[F]) ∈ IsLocalRing.maximalIdeal 𝒪[F] :=
    Ideal.mul_mem_right _ _ ((IsLocalRing.mem_maximalIdeal _).2 hp.not_isUnit)
  have hu : IsUnit (1 + uniformizer F * (⟨y, hy⟩ : 𝒪[F])) := by
    by_contra hne
    have h1 : (1 + uniformizer F * (⟨y, hy⟩ : 𝒪[F])) ∈ IsLocalRing.maximalIdeal 𝒪[F] :=
      (IsLocalRing.mem_maximalIdeal _).2 hne
    have h2 := (IsLocalRing.maximalIdeal 𝒪[F]).sub_mem h1 hm
    rw [add_sub_cancel_right] at h2
    exact (Ideal.ne_top_iff_one _).1 (IsLocalRing.maximalIdeal.isMaximal _).ne_top h2
  obtain ⟨e, he⟩ := hu
  exact ⟨e, by rw [he]; rfl⟩

end Local

section Meas

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F] {μ : Measure F} [μ.IsAddHaarMeasure] {ψ : AddChar F ℂ} {n : ℕ}
  {V : Type} [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Establish `h` using `((hL0 F μ ψ hψ).2 (0 + 1)).1 M`. Conclude with `⟨h.2.2.1, h.2.2.2⟩`.
-/
theorem lat_facts (hL0 : L0) (hψ : PsiOK ψ) (M : ℕ) :
    MeasurableSet (lat F (0 + 1) M) ∧ 0 < (Measure.pi fun _ : Fin (0 + 1) => μ).real (lat F (0 + 1) M) := by
  have h := ((hL0 F μ ψ hψ).2 (0 + 1)).1 M
  exact ⟨h.2.2.1, h.2.2.2⟩

/- English proof (translation)
Establish `h1` using `((hL0 F μ ψ hψ).2 (0 + 1)).2 (sc s) (lat F (0 + 1) a) f (lat_facts (μ := μ) hL0 hψ a).1`. Rewrite `h1` using `[image_sc s a b h, det_sc]`. Simplify `h1` using `only [sc_mulVec]`.
-/
theorem change_var (hL0 : L0) (hψ : PsiOK ψ) (s : Fˣ) (a b : ℕ)
    (h : ∀ x : F, (uniformizer F : F) ^ b * ((s : F) * x) ∈ 𝒪[F] ↔ (uniformizer F : F) ^ a * x ∈ 𝒪[F])
    (f : (Fin (0 + 1) → F) → ℂ) :
    ∫ x in lat F (0 + 1) b, f x ∂(Measure.pi fun _ => μ) =
      ((Measures.modulus (s : F) : ℝ) : ℂ) *
        ∫ x in lat F (0 + 1) a, f (fun i => (s : F) * x i) ∂(Measure.pi fun _ => μ) := by
  have h1 := ((hL0 F μ ψ hψ).2 (0 + 1)).2 (sc s) (lat F (0 + 1) a) f (lat_facts (μ := μ) hL0 hψ a).1
  rw [image_sc s a b h, det_sc] at h1
  simpa only [sc_mulVec] using h1

/- English proof (translation)
Establish `h1` using `change_var (μ := μ) hL0 hψ s a b h (fun _ => (1 : ℂ))`. Simplify using `only [setIntegral_const, Complex.real_smul, mul_one] at h1`. Conclude with `h1` after adjusting the coercions.
-/
theorem vol_rel (hL0 : L0) (hψ : PsiOK ψ) (s : Fˣ) (a b : ℕ)
    (h : ∀ x : F, (uniformizer F : F) ^ b * ((s : F) * x) ∈ 𝒪[F] ↔ (uniformizer F : F) ^ a * x ∈ 𝒪[F]) :
    (Measure.pi fun _ : Fin (0 + 1) => μ).real (lat F (0 + 1) b) =
      (Measures.modulus (s : F) : ℝ) * (Measure.pi fun _ : Fin (0 + 1) => μ).real (lat F (0 + 1) a) := by
  have h1 := change_var (μ := μ) hL0 hψ s a b h (fun _ => (1 : ℂ))
  simp only [setIntegral_const, Complex.real_smul, mul_one] at h1
  exact_mod_cast h1

/- English proof (translation)
Establish `h` using `vol_rel (μ := μ) hL0 hψ s 0 0 (fun x => by`. Simplify using `only [pow_zero, one_mul]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Use `(𝒪[F]).mul_mem h₂ hx` as an intermediate fact.

Simplify using `using this`. Conclude with `(𝒪[F]).mul_mem h₁)`. Establish `hp` using `(lat_facts (μ := μ) hL0 hψ 0).2`. Establish `h' : (Measures.modulus (s : F) : ℝ) = 1`. Use `mul_right_cancel₀ hp.ne' (by rw [one_mul]; exact h.symm : (Measures.modulus (s : F) : ℝ) * _ = 1 * _)` as an intermediate fact.

Conclude with `this`. Conclude with `h'` after adjusting the coercions.
-/
theorem modulus_unit (μ : Measure F) [μ.IsAddHaarMeasure] (hL0 : L0) (hψ : PsiOK ψ) (s : Fˣ) (h₁ : (s : F) ∈ 𝒪[F])
    (h₂ : ((s⁻¹ : Fˣ) : F) ∈ 𝒪[F]) : Measures.modulus (s : F) = 1 := by
  have h := vol_rel (μ := μ) hL0 hψ s 0 0 (fun x => by
    simp only [pow_zero, one_mul]
    constructor
    · intro hx
      have := (𝒪[F]).mul_mem h₂ hx
      simpa using this
    · exact (𝒪[F]).mul_mem h₁)
  have hp := (lat_facts (μ := μ) hL0 hψ 0).2
  have h' : (Measures.modulus (s : F) : ℝ) = 1 := by
    have := mul_right_cancel₀ hp.ne' (by rw [one_mul]; exact h.symm :
      (Measures.modulus (s : F) : ℝ) * _ = 1 * _)
    exact this
  exact_mod_cast h'

/- English proof (translation)
Establish `hp0 : (uniformizer F : F) ≠ 0` using `(uniformizerUnit F).ne_zero`. Establish `h` using `hL2 F μ ψ hψ 0 0 c' f ht ?_ (sc (uniformizerUnit F ^ M)⁻¹) ?_`. Rewrite `h` using `[image_sc _ 0 M (fun x => ?_)]`. Conclude with `h`. Simplify using `[hp0]`.

Introduce `g hg x`. Take `⟨y, hy, e⟩` from `hg 0 0`. Take `⟨u, hu'⟩` from `exists_unit_of_one_add y (by simpa using hy)`. Establish `hmv : ((g : Matrix (Fin (0 + 1)) (Fin (0 + 1)) F)) *ᵥ x = fun i => ((u : 𝒪[F]) : F) * x i`. Use extensionality with `i`.

Take `rfl : i = 0` from `Fin.fin_one_eq_zero i`. Establish `e' : (g : Matrix (Fin (0 + 1)) (Fin (0 + 1)) F) 0 0 = 1 + (uniformizer F : F) * y`. Use `e` as an intermediate fact. Simplify using `only [Matrix.sub_apply, Matrix.one_apply_eq, zero_add, pow_one] at this`. Rewrite using `[← this]`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `[mulVec, dotProduct, e', hu']`. Rewrite using `[hmv]`. Conclude with `hu u x`. Introduce `i j`.

Take `⟨k, rfl⟩ : ∃ k, M = k + 1` from `⟨M - 1, by omega⟩`. Use `⟨(uniformizer F : F) ^ k, (𝒪[F]).pow_mem (uniformizer F).2 _, ?_⟩` and prove the remaining obligations. Take `rfl : i = j` from `(Fin.fin_one_eq_zero i).trans (Fin.fin_one_eq_zero j).symm`. Establish `: (sc (uniformizerUnit F ^ (k + 1))⁻¹)⁻¹ = diagGL F (0 + 1) fun _ => uniformizerUnit F ^ (k + 1)`. Rewrite using `[sc, ← map_inv]`.

Use `congr 1`. Rewrite using `[this]`. Simplify using `[pow_succ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem stable (hL2 : L2) (hψ : PsiOK ψ) (f : (Fin (0 + 1) → F) → ℂ) (c' : ℕ)
    (ht : ∀ x y, (∀ i, ∃ t ∈ 𝒪[F], y i = (uniformizer F : F) ^ c' * t) → f (x + y) = f x)
    (hu : ∀ e : (𝒪[F])ˣ, ∀ x, f (fun i => ((e : 𝒪[F]) : F) * x i) = f x) (M : ℕ) (hM : 1 ≤ M) :
    ∫ x in lat F (0 + 1) M, ψ (-x (Fin.last 0)) * f x ∂(Measure.pi fun _ => μ) =
      ∫ x in lat F (0 + 1) 1, ψ (-x (Fin.last 0)) * f x ∂(Measure.pi fun _ => μ) := by
  have hp0 : (uniformizer F : F) ≠ 0 := (uniformizerUnit F).ne_zero
  have h := hL2 F μ ψ hψ 0 0 c' f ht ?_ (sc (uniformizerUnit F ^ M)⁻¹) ?_
  · rw [image_sc _ 0 M (fun x => ?_)] at h
    · exact h
    · simp [hp0]
  · intro g hg x
    obtain ⟨y, hy, e⟩ := hg 0 0
    obtain ⟨u, hu'⟩ := exists_unit_of_one_add y (by simpa using hy)
    have hmv : ((g : Matrix (Fin (0 + 1)) (Fin (0 + 1)) F)) *ᵥ x = fun i => ((u : 𝒪[F]) : F) * x i := by
      ext i
      obtain rfl : i = 0 := Fin.fin_one_eq_zero i
      have e' : (g : Matrix (Fin (0 + 1)) (Fin (0 + 1)) F) 0 0 = 1 + (uniformizer F : F) * y := by
        have := e
        simp only [Matrix.sub_apply, Matrix.one_apply_eq, zero_add, pow_one] at this
        rw [← this]; ring
      simp [mulVec, dotProduct, e', hu']
    rw [hmv]
    exact hu u x
  · intro i j
    obtain ⟨k, rfl⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
    refine ⟨(uniformizer F : F) ^ k, (𝒪[F]).pow_mem (uniformizer F).2 _, ?_⟩
    obtain rfl : i = j := (Fin.fin_one_eq_zero i).trans (Fin.fin_one_eq_zero j).symm
    have : (sc (uniformizerUnit F ^ (k + 1))⁻¹)⁻¹ = diagGL F (0 + 1) fun _ => uniformizerUnit F ^ (k + 1) := by
      rw [sc, ← map_inv]
      congr 1
    rw [this]
    simp [pow_succ]
    ring

/- English proof (translation)
Rewrite using `[hl (B W), setIntegral_congr_fun (g := fun _ => B W v) hM ?_, setIntegral_const, Complex.real_smul]`. Introduce `x hx`. Establish `h` using `hU x W v`. Rewrite `h` using `[he x hx]`. Simplify using `only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul] at h`.

Establish `hc : ψ (-(ξ ⬝ᵥ x)) = starRingEnd ℂ (ψ (ξ ⬝ᵥ x))`. Rewrite using `[AddChar.map_neg_eq_inv, Complex.inv_eq_conj (hψ.2.2 _)]`. Simplify using `only [hc]`. Conclude with `h`.
-/
theorem proj (hψ : PsiOK ψ) {ρ : Representation ℂ (GL (Fin n) F) V} (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)
    (hU : ∀ x u u', B (ρ (col n 0 x) u) (ρ (col n 0 x) u') = B u u')
    (M : ℕ) (hM : MeasurableSet (lat F (0 + 1) M)) (ξ : Fin (0 + 1) → F) (v W : V)
    (hl : ∀ l : V →ₗ[ℂ] ℂ, l W = ∫ x in lat F (0 + 1) M, ψ (-(ξ ⬝ᵥ x)) * l (ρ (col n 0 x) v)
      ∂(Measure.pi fun _ => μ))
    (he : ∀ y ∈ lat F (0 + 1) M, ρ (col n 0 y) W = ψ (ξ ⬝ᵥ y) • W) :
    B W W = (((Measure.pi fun _ : Fin (0 + 1) => μ).real (lat F (0 + 1) M) : ℝ) : ℂ) * B W v := by
  rw [hl (B W), setIntegral_congr_fun (g := fun _ => B W v) hM ?_, setIntegral_const,
    Complex.real_smul]
  intro x hx
  have h := hU x W v
  rw [he x hx] at h
  simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul] at h
  have hc : ψ (-(ξ ⬝ᵥ x)) = starRingEnd ℂ (ψ (ξ ⬝ᵥ x)) := by
    rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (hψ.2.2 _)]
  simp only [hc]
  exact h

/- English proof (translation)
Establish `h` using `hU y W W'`. Rewrite `h` using `[h1, h2]`. Simplify using `only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul] at h`. Establish `hc' : starRingEnd ℂ c - 1 ≠ 0` using `fun e => hc (by`. Establish `: starRingEnd ℂ c = 1` using `sub_eq_zero.1 e`.

Simplify using `using congrArg (starRingEnd ℂ) this)`. Establish `: (starRingEnd ℂ c - 1) * B W W' = 0` using `by rw [sub_mul, h]; ring`. Conclude with `(mul_eq_zero.1 this).resolve_left hc'`.
-/
theorem orth (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) {ρ : Representation ℂ (GL (Fin n) F) V}
    (hU : ∀ x u u', B (ρ (col n 0 x) u) (ρ (col n 0 x) u') = B u u')
    (y : Fin (0 + 1) → F) (W W' : V) (c : ℂ) (hc : c ≠ 1) (h1 : ρ (col n 0 y) W = c • W)
    (h2 : ρ (col n 0 y) W' = W') : B W W' = 0 := by
  have h := hU y W W'
  rw [h1, h2] at h
  simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul] at h
  have hc' : starRingEnd ℂ c - 1 ≠ 0 := fun e => hc (by
    have : starRingEnd ℂ c = 1 := sub_eq_zero.1 e
    simpa using congrArg (starRingEnd ℂ) this)
  have : (starRingEnd ℂ c - 1) * B W W' = 0 := by rw [sub_mul, h]; ring
  exact (mul_eq_zero.1 this).resolve_left hc'

end Meas

section Key

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F] {μ : Measure F} [μ.IsAddHaarMeasure] {ψ : AddChar F ℂ} {n : ℕ}
  {V : Type} [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Use `set t : Fˣ := Units.map (𝒪[F]).subtype.toMonoidHom e with ht`. Establish `hcoe : (t : F) = ((e : 𝒪[F]) : F)` using `rfl`. Use `set g : GL (Fin n) F := dg i₀ t with hg`. Use `set u : V := ρ (dg i₀ s) v with hu`. Establish `hgK : g ∈ integralGL F n` using `dg_mem_integralGL i₀ e`.

Establish `hgu : ρ g u = u`. Rewrite using `[hu, ← Module.End.mul_apply, ← map_mul, hg, dg_comm, map_mul, Module.End.mul_apply, hv _ hgK]`. Establish `hm` using `dg_mul_col hn i₀ h₀ t x`. Establish `hmod : Measures.modulus (t : F) = 1` using `modulus_unit μ hL0 hψ t (by rw [hcoe]; exact (e : 𝒪[F]).2) (by`. Establish `: ((t⁻¹ : Fˣ) : F) = (((e⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) : F)`.

Rewrite using `[ht, ← map_inv]`. Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `((e⁻¹ : (𝒪[F])ˣ) : 𝒪[F]).2)`. Establish `hq` using `hB.quasi g (inP_dg i₀ h₀ t) u (ρ (col n 0 x) u)`.

Rewrite `hq` using `[hg, det_dg, hmod, ← hg, hgu]`. Simplify using `only [NNReal.coe_one, Complex.ofReal_one, one_pow, one_mul] at hq`. Establish `h1 : ρ (col n 0 fun i => ((e : 𝒪[F]) : F) * x i) u = ρ g (ρ (col n 0 x) u)`. Establish `hm' : (col n 0 fun i => ((e : 𝒪[F]) : F) * x i) * g = g * col n 0 x` using `hm.symm`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[map_mul, Module.End.mul_apply]`. Use `_ = ρ (g * col n 0 x) u := by rw [hm']`. Use `_ = ρ g (ρ (col n 0 x) u) := by rw [map_mul, Module.End.mul_apply]`. Rewrite using `[h1, hq]`.
-/
theorem coeff_unit (μ : Measure F) [μ.IsAddHaarMeasure] (hL0 : L0) (hψ : PsiOK ψ) (hn : 1 < n) (i₀ : Fin n) (h₀ : (i₀ : ℕ) = 0)
    {ρ : Representation ℂ (GL (Fin n) F) V} {l : V →ₗ[ℂ] ℂ} {B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ}
    (hB : Inv ρ ψ l 1 B) (v : V) (hv : ∀ g ∈ integralGL F n, ρ g v = v) (s : Fˣ)
    (e : (𝒪[F])ˣ) (x : Fin (0 + 1) → F) :
    B (ρ (dg i₀ s) v) (ρ (col n 0 fun i => ((e : 𝒪[F]) : F) * x i) (ρ (dg i₀ s) v)) =
      B (ρ (dg i₀ s) v) (ρ (col n 0 x) (ρ (dg i₀ s) v)) := by
  set t : Fˣ := Units.map (𝒪[F]).subtype.toMonoidHom e with ht
  have hcoe : (t : F) = ((e : 𝒪[F]) : F) := rfl
  set g : GL (Fin n) F := dg i₀ t with hg
  set u : V := ρ (dg i₀ s) v with hu
  have hgK : g ∈ integralGL F n := dg_mem_integralGL i₀ e
  have hgu : ρ g u = u := by
    rw [hu, ← Module.End.mul_apply, ← map_mul, hg, dg_comm, map_mul, Module.End.mul_apply, hv _ hgK]
  have hm := dg_mul_col hn i₀ h₀ t x
  have hmod : Measures.modulus (t : F) = 1 := modulus_unit μ hL0 hψ t
    (by rw [hcoe]; exact (e : 𝒪[F]).2)
    (by
      have : ((t⁻¹ : Fˣ) : F) = (((e⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) : F) := by
        rw [ht, ← map_inv]; rfl
      rw [this]; exact ((e⁻¹ : (𝒪[F])ˣ) : 𝒪[F]).2)
  have hq := hB.quasi g (inP_dg i₀ h₀ t) u (ρ (col n 0 x) u)
  rw [hg, det_dg, hmod, ← hg, hgu] at hq
  simp only [NNReal.coe_one, Complex.ofReal_one, one_pow, one_mul] at hq
  have h1 : ρ (col n 0 fun i => ((e : 𝒪[F]) : F) * x i) u = ρ g (ρ (col n 0 x) u) := by
    have hm' : (col n 0 fun i => ((e : 𝒪[F]) : F) * x i) * g = g * col n 0 x := hm.symm
    calc ρ (col n 0 fun i => ((e : 𝒪[F]) : F) * x i) u
        = ρ (col n 0 fun i => ((e : 𝒪[F]) : F) * x i) (ρ g u) := by rw [hgu]
      _ = ρ ((col n 0 fun i => ((e : 𝒪[F]) : F) * x i) * g) u := by
        rw [map_mul, Module.End.mul_apply]
      _ = ρ (g * col n 0 x) u := by rw [hm']
      _ = ρ g (ρ (col n 0 x) u) := by rw [map_mul, Module.End.mul_apply]
  rw [h1, hq]

/- English proof (translation)
Use `set s : Fˣ := uniformizerUnit F ^ j with hsdef`. Use `set a : GL (Fin n) F := dg i₀ s with ha`. Use `set u : V := ρ a v with hu`. Establish `hlt : 0 + 1 < n` using `by omega`. Take `⟨hadd, -, -, -, -, -⟩` from `hL3c F μ ψ hψ n 0 hlt`.

Take `⟨c, hc⟩` from `hs u`. Take `⟨M₀, hM₀⟩` from `hC u u`. Establish `e1` using `hM₀ (max M₀ 1) (le_max_left _ _)`. Establish `e2` using `stable (μ := μ) hL2 hψ (fun x => B u (ρ (col n 0 x) u)) (c + 1) (fun x y hy => by show B u (ρ (col n 0 (x + y)) u) = B u (ρ (col n 0 x) u)`. Rewrite using `[hadd, map_mul, Module.End.mul_apply, hc _ (div_col (c + 1) y hy)])`.

Use the proof step `(fun e x => coeff_unit μ hL0 hψ hn i₀ h₀ hB v hv s e x) (max M₀ 1) (le_max_right _ _)`. Establish `hpow : ∀ x : F, (uniformizer F : F) ^ 1 * ((s : F) * x) ∈ 𝒪[F] ↔ (uniformizer F : F) ^ (j + 1) * x ∈ 𝒪[F]` using `fun x => by`. Establish `: (uniformizer F : F) ^ 1 * ((s : F) * x) = (uniformizer F : F) ^ (j + 1) * x`. Simplify using `[hsdef, pow_succ]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this]`. Establish `e3` using `change_var (μ := μ) hL0 hψ s (j + 1) 1 hpow (fun x => ψ (-x (Fin.last 0)) * B u (ρ (col n 0 x) u))`. Establish `hdet : ((Measures.modulus (a : Matrix (Fin n) (Fin n) F).det : ℝ) : ℂ) = ((Measures.modulus (s : F) : ℝ) : ℂ)` using `by rw [ha, det_dg]`. Establish `e4 : ∀ x : Fin (0 + 1) → F, ψ (-(fun i => (s : F) * x i) (Fin.last 0)) * B u (ρ (col n 0 fun i => (s : F) * x i) u) = ((Measures.modulus (s : F) : ℝ) : ℂ) ^ (n - 1 - 1) * (ψ (-((fun _ => (s : F)) ⬝ᵥ x)) * B v (ρ (col n 0 x) v))`. Introduce `x`.

Establish `h1 : ρ (col n 0 fun i => (s : F) * x i) u = ρ a (ρ (col n 0 x) v)`. Establish `hm : (col n 0 fun i => (s : F) * x i) * a = a * col n 0 x` using `(dg_mul_col hn i₀ h₀ s x).symm`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[map_mul, Module.End.mul_apply]`. Use `_ = ρ (a * col n 0 x) v := by rw [hm]`.

Use `_ = ρ a (ρ (col n 0 x) v) := by rw [map_mul, Module.End.mul_apply]`. Establish `h2` using `hB.quasi a (inP_dg i₀ h₀ s) v (ρ (col n 0 x) v)`. Rewrite `h2` using `[hdet]`. Establish `h3 : (fun _ : Fin (0 + 1) => (s : F)) ⬝ᵥ x = (s : F) * x (Fin.last 0)`. Simplify using `[dotProduct]`.

Rewrite using `[h1, hu, h2, h3]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, e2, e3]`. Simplify using `only [e4]`. Rewrite using `[integral_const_mul]`.
-/
theorem key (hL0 : L0) (hL2 : L2) (hL3c : ColumnsMirabolic) (hψ : PsiOK ψ) (hn : 1 < n) (i₀ : Fin n)
    (h₀ : (i₀ : ℕ) = 0) {ρ : Representation ℂ (GL (Fin n) F) V} (hs : Smooth ρ)
    {l : V →ₗ[ℂ] ℂ} {B B' : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ} (hB : Inv ρ ψ l 1 B) (hC : Char μ ρ ψ 0 B B')
    (v : V) (hv : ∀ g ∈ integralGL F n, ρ g v = v) (j : ℕ) :
    B' (ρ (dg i₀ (uniformizerUnit F ^ j)) v) (ρ (dg i₀ (uniformizerUnit F ^ j)) v) =
      ((Measures.modulus ((uniformizerUnit F ^ j : Fˣ) : F) : ℝ) : ℂ) *
        (((Measures.modulus ((uniformizerUnit F ^ j : Fˣ) : F) : ℝ) : ℂ) ^ (n - 1 - 1) *
          ∫ x in lat F (0 + 1) (j + 1),
            ψ (-((fun _ => ((uniformizerUnit F ^ j : Fˣ) : F)) ⬝ᵥ x)) * B v (ρ (col n 0 x) v)
              ∂(Measure.pi fun _ => μ)) := by
  set s : Fˣ := uniformizerUnit F ^ j with hsdef
  set a : GL (Fin n) F := dg i₀ s with ha
  set u : V := ρ a v with hu
  have hlt : 0 + 1 < n := by omega
  obtain ⟨hadd, -, -, -, -, -⟩ := hL3c F μ ψ hψ n 0 hlt
  obtain ⟨c, hc⟩ := hs u
  obtain ⟨M₀, hM₀⟩ := hC u u
  have e1 := hM₀ (max M₀ 1) (le_max_left _ _)
  have e2 := stable (μ := μ) hL2 hψ (fun x => B u (ρ (col n 0 x) u)) (c + 1)
    (fun x y hy => by
      show B u (ρ (col n 0 (x + y)) u) = B u (ρ (col n 0 x) u)
      rw [hadd, map_mul, Module.End.mul_apply, hc _ (div_col (c + 1) y hy)])
    (fun e x => coeff_unit μ hL0 hψ hn i₀ h₀ hB v hv s e x) (max M₀ 1) (le_max_right _ _)
  have hpow : ∀ x : F, (uniformizer F : F) ^ 1 * ((s : F) * x) ∈ 𝒪[F] ↔
      (uniformizer F : F) ^ (j + 1) * x ∈ 𝒪[F] := fun x => by
    have : (uniformizer F : F) ^ 1 * ((s : F) * x) = (uniformizer F : F) ^ (j + 1) * x := by
      simp [hsdef, pow_succ]; ring
    rw [this]
  have e3 := change_var (μ := μ) hL0 hψ s (j + 1) 1 hpow
    (fun x => ψ (-x (Fin.last 0)) * B u (ρ (col n 0 x) u))
  have hdet : ((Measures.modulus (a : Matrix (Fin n) (Fin n) F).det : ℝ) : ℂ) =
      ((Measures.modulus (s : F) : ℝ) : ℂ) := by rw [ha, det_dg]
  have e4 : ∀ x : Fin (0 + 1) → F,
      ψ (-(fun i => (s : F) * x i) (Fin.last 0)) *
          B u (ρ (col n 0 fun i => (s : F) * x i) u) =
        ((Measures.modulus (s : F) : ℝ) : ℂ) ^ (n - 1 - 1) *
          (ψ (-((fun _ => (s : F)) ⬝ᵥ x)) * B v (ρ (col n 0 x) v)) := by
    intro x
    have h1 : ρ (col n 0 fun i => (s : F) * x i) u = ρ a (ρ (col n 0 x) v) := by
      have hm : (col n 0 fun i => (s : F) * x i) * a = a * col n 0 x :=
        (dg_mul_col hn i₀ h₀ s x).symm
      calc ρ (col n 0 fun i => (s : F) * x i) u
          = ρ ((col n 0 fun i => (s : F) * x i) * a) v := by
            rw [map_mul, Module.End.mul_apply]
        _ = ρ (a * col n 0 x) v := by rw [hm]
        _ = ρ a (ρ (col n 0 x) v) := by rw [map_mul, Module.End.mul_apply]
    have h2 := hB.quasi a (inP_dg i₀ h₀ s) v (ρ (col n 0 x) v)
    rw [hdet] at h2
    have h3 : (fun _ : Fin (0 + 1) => (s : F)) ⬝ᵥ x = (s : F) * x (Fin.last 0) := by
      simp [dotProduct]
    rw [h1, hu, h2, h3]
    ring
  rw [e1, e2, e3]
  simp only [e4]
  rw [integral_const_mul]

end Key

/- English proof (translation)
Introduce `hL0 _ hL2 hL3 hL3c F _ _ _ _ _ _ μ _ ψ hψ n V _ _ ρ hs l B B' hn hB hC v hv`. Establish `hlt : 0 + 1 < n` using `by omega`. Establish `h₀ : (((⟨0, by omega⟩ : Fin n)) : ℕ) = 0` using `rfl`. Establish `hp0 : (uniformizer F : F) ≠ 0` using `(uniformizerUnit F).ne_zero`. Establish `hO : (uniformizer F : F) ∈ 𝒪[F]` using `(uniformizer F).2`.

Establish `hcoe : ∀ j : ℕ, ((uniformizerUnit F ^ j : Fˣ) : F) = (uniformizer F : F) ^ j` using `fun j => by`. Simplify using the standard rewrite rules. Establish `hU : ∀ (x : Fin (0 + 1) → F) (u u' : V), B (ρ (col n 0 x) u) (ρ (col n 0 x) u') = B u u'`. Introduce `x u u'`. Take `⟨-, -, hx, -⟩` from `hL3c F μ ψ hψ n 0 hlt`.

Take `⟨hP, -, hd, -⟩` from `hx x`. Rewrite using `[hB.quasi _ hP u u', hd]`. Simplify using the standard rewrite rules. Use `choose W hW1 hW2 using fun j : ℕ => hL3 F μ ψ hψ n V ρ hs 0 (j + 1) (fun _ => ((uniformizerUnit F ^ j : Fˣ) : F)) v`. Use `set Vj : ℕ → ℝ := fun j => (Measure.pi fun _ : Fin (0 + 1) => μ).real (lat F (0 + 1) (j + 1)) with hVj`.

Establish `hVpos : ∀ j, 0 < Vj j` using `fun j => (lat_facts (μ := μ) hL0 hψ (j + 1)).2`. Establish `hVne : ∀ j, ((Vj j : ℝ) : ℂ) ≠ 0` using `fun j => by exact_mod_cast (hVpos j).ne'`. Establish `hWW : ∀ j, B (W j) (W j) = ((Vj j : ℝ) : ℂ) * B (W j) v` using `fun j => proj hψ B hU (j + 1) (lat_facts (μ := μ) hL0 hψ (j + 1)).1 _ v (W j) (hW1 j) (hW2 j)`. Establish `hWo : ∀ i j, i < j → B (W i) (W j) = 0`. Introduce `i j hij`.

Take `⟨d, rfl⟩ : ∃ d, j = i + 1 + d` from `⟨j - (i + 1), by omega⟩`. Take `⟨x₀, hx₀, hne⟩` from `hψ.2.1`. Establish `hpi : (uniformizer F : F) ^ i ≠ 0` using `pow_ne_zero _ hp0`. Use `set y : Fin (0 + 1) → F := fun _ => ((uniformizer F : F) ^ i)⁻¹ * x₀ with hy`. Establish `hyi : y ∈ lat F (0 + 1) (i + 1)` using `fun k => by`.

Establish `: (uniformizer F : F) ^ (i + 1) * y k = (uniformizer F : F) * x₀`. Simplify using `only [hy]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`.

Conclude with `hx₀`. Establish `hval : (uniformizer F : F) ^ (i + 1 + d) * (((uniformizer F : F) ^ i)⁻¹ * x₀) = (uniformizer F : F) ^ d * ((uniformizer F : F) * x₀)` using `by field_simp; ring`. Establish `hint : (uniformizer F : F) ^ d * ((uniformizer F : F) * x₀) ∈ 𝒪[F]` using `(𝒪[F]).mul_mem ((𝒪[F]).pow_mem hO _) hx₀`. Establish `hyj : y ∈ lat F (0 + 1) (i + 1 + d + 1)` using `fun k => by`. Establish `: (uniformizer F : F) ^ (i + 1 + d + 1) * y k = (uniformizer F : F) * ((uniformizer F : F) ^ d * ((uniformizer F : F) * x₀))`.

Simplify using `only [hy]`. Rewrite using `[pow_succ, mul_comm _ (uniformizer F : F), mul_assoc, hval]`. Rewrite using `[this]`. Conclude with `(𝒪[F]).mul_mem hO hint`. Establish `d1 : (fun _ : Fin (0 + 1) => ((uniformizerUnit F ^ i : Fˣ) : F)) ⬝ᵥ y = x₀`.

Simplify using `[dotProduct, hy, hpi]`. Establish `d2 : (fun _ : Fin (0 + 1) => ((uniformizerUnit F ^ (i + 1 + d) : Fˣ) : F)) ⬝ᵥ y = (uniformizer F : F) ^ d * ((uniformizer F : F) * x₀)`. Rewrite using `[← hval]`. Simplify using `[dotProduct, hy]`. Establish `h1` using `hW2 i y hyi`.

Establish `h2` using `hW2 (i + 1 + d) y hyj`. Rewrite `h1` using `[d1]`. Rewrite `h2` using `[d2, hψ.1 _ hint, one_smul]`. Conclude with `orth B hU y _ _ _ hne h1 h2`. Use `set w : ℕ → V := fun j => (((Vj j : ℝ) : ℂ)⁻¹) • W j with hw`.

Establish `hconj : ∀ j, starRingEnd ℂ (((Vj j : ℝ) : ℂ)⁻¹) = ((Vj j : ℝ) : ℂ)⁻¹` using `fun j => by`. Rewrite using `[map_inv₀, Complex.conj_ofReal]`. Establish `hwv : ∀ j, B (w j) v = ((Vj j : ℝ) : ℂ)⁻¹ * B (W j) v` using `fun j => by`. Simplify using `only [hw, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hconj]`. Establish `h2 : ∀ j, B (w j) v = B (w j) (w j)` using `fun j => by`.

Establish `: B (w j) (w j) = ((Vj j : ℝ) : ℂ)⁻¹ * (((Vj j : ℝ) : ℂ)⁻¹ * B (W j) (W j))`. Simplify using `only [hw, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hconj, map_smul]`. Rewrite using `[this, hwv, hWW, inv_mul_cancel_left₀ (hVne j)]`. Establish `h1 : ∀ j, B v (w j) = B (w j) (w j)` using `fun j => by`. Rewrite using `[← hB.herm (w j) v, h2, hB.herm]`.

Establish `h3 : ∀ i j, i ≠ j → B (w i) (w j) = 0`. Introduce `i j hij`. Establish `hz : B (W i) (W j) = 0`. Break down `lt_or_gt_of_ne hij with h | h` into its components or cases. Conclude with `hWo i j h`.

Rewrite using `[← hB.herm (W j) (W i), hWo j i h, map_zero]`. Simplify using `only [hw, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, map_smul, hz, mul_zero]`. Establish `hV₀` using `(lat_facts (μ := μ) hL0 hψ 1).2`. Establish `hterm : ∀ j : ℕ, (qF F : ℝ) ^ (j * (n - 2)) * (B' (ρ (torusPow F n (Pi.single ⟨0, by omega⟩ (j : ℤ))) v) (ρ (torusPow F n (Pi.single ⟨0, by omega⟩ (j : ℤ))) v)).re = (Measure.pi fun _ : Fin (0 + 1) => μ).real (lat F (0 + 1) 1) * (B (w j) (w j)).re`. Introduce `j`.

Establish `hk` using `key (μ := μ) hL0 hL2 hL3c hψ hn ⟨0, by omega⟩ h₀ hs hB hC v hv j`. Rewrite `hk` using `[← hW1 j (B v)]`. Rewrite using `[torusPow_eq_dg, hk]`. Establish `hmod : (Measures.modulus ((uniformizerUnit F ^ j : Fˣ) : F) : ℝ) = ((qF F : ℝ)⁻¹) ^ j`. Rewrite using `[hcoe, map_pow, modulus_uniformizer]`.

Simplify using the standard rewrite rules. Establish `hvol` using `vol_rel (μ := μ) hL0 hψ (uniformizerUnit F ^ j) (j + 1) 1 (fun x => by`. Establish `: (uniformizer F : F) ^ 1 * (((uniformizerUnit F ^ j : Fˣ) : F) * x) = (uniformizer F : F) ^ (j + 1) * x`. Rewrite using `[hcoe]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this])`. Establish `hBv : B v (W j) = ((Vj j : ℝ) : ℂ) * B (w j) (w j)`. Rewrite using `[← h1 j]`. Simplify using `only [hw, map_smul, smul_eq_mul]`. Rewrite using `[mul_inv_cancel_left₀ (hVne j)]`.

Establish `hq : ((qF F : ℝ)) ≠ 0` using `by exact_mod_cast (qF_pos (F := F)).ne'`. Establish `hn2 : n - 1 - 1 = n - 2` using `by omega`. Use `set r : ℝ := (Measures.modulus ((uniformizerUnit F ^ j : Fˣ) : F) : ℝ) with hr`. Establish `hrq : (qF F : ℝ) ^ (j * (n - 2)) * r ^ (n - 2) = 1`. Rewrite using `[hmod, pow_mul, ← mul_pow, ← mul_pow, mul_inv_cancel₀ hq, one_pow, one_pow]`.

Rewrite using `[hBv, hvol, hn2]`. Establish `e : ((r : ℝ) : ℂ) * (((r : ℝ) : ℂ) ^ (n - 2) * (((Vj j : ℝ) : ℂ) * B (w j) (w j))) = ((r * r ^ (n - 2) * Vj j : ℝ) : ℂ) * B (w j) (w j)` using `by push_cast; ring`. Rewrite using `[e, Complex.re_ofReal_mul]`. Combine the equalities or inequalities in the displayed calculation. Use `⟨(Measure.pi fun _ : Fin (0 + 1) => μ).real (lat F (0 + 1) 1) * (B v v).re, fun T => ?_⟩` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem bessel_step : L0 → L1 → L2 → L3 → ColumnsMirabolic → L5 := by
  intro hL0 _ hL2 hL3 hL3c F _ _ _ _ _ _ μ _ ψ hψ n V _ _ ρ hs l B B' hn hB hC v hv
  have hlt : 0 + 1 < n := by omega
  have h₀ : (((⟨0, by omega⟩ : Fin n)) : ℕ) = 0 := rfl
  have hp0 : (uniformizer F : F) ≠ 0 := (uniformizerUnit F).ne_zero
  have hO : (uniformizer F : F) ∈ 𝒪[F] := (uniformizer F).2
  have hcoe : ∀ j : ℕ, ((uniformizerUnit F ^ j : Fˣ) : F) = (uniformizer F : F) ^ j := fun j => by
    simp

  have hU : ∀ (x : Fin (0 + 1) → F) (u u' : V),
      B (ρ (col n 0 x) u) (ρ (col n 0 x) u') = B u u' := by
    intro x u u'
    obtain ⟨-, -, hx, -⟩ := hL3c F μ ψ hψ n 0 hlt
    obtain ⟨hP, -, hd, -⟩ := hx x
    rw [hB.quasi _ hP u u', hd]
    simp
  choose W hW1 hW2 using fun j : ℕ => hL3 F μ ψ hψ n V ρ hs 0 (j + 1)
    (fun _ => ((uniformizerUnit F ^ j : Fˣ) : F)) v
  set Vj : ℕ → ℝ := fun j => (Measure.pi fun _ : Fin (0 + 1) => μ).real (lat F (0 + 1) (j + 1)) with hVj
  have hVpos : ∀ j, 0 < Vj j := fun j => (lat_facts (μ := μ) hL0 hψ (j + 1)).2
  have hVne : ∀ j, ((Vj j : ℝ) : ℂ) ≠ 0 := fun j => by exact_mod_cast (hVpos j).ne'
  have hWW : ∀ j, B (W j) (W j) = ((Vj j : ℝ) : ℂ) * B (W j) v := fun j =>
    proj hψ B hU (j + 1) (lat_facts (μ := μ) hL0 hψ (j + 1)).1 _ v (W j) (hW1 j) (hW2 j)

  have hWo : ∀ i j, i < j → B (W i) (W j) = 0 := by
    intro i j hij
    obtain ⟨d, rfl⟩ : ∃ d, j = i + 1 + d := ⟨j - (i + 1), by omega⟩
    obtain ⟨x₀, hx₀, hne⟩ := hψ.2.1
    have hpi : (uniformizer F : F) ^ i ≠ 0 := pow_ne_zero _ hp0
    set y : Fin (0 + 1) → F := fun _ => ((uniformizer F : F) ^ i)⁻¹ * x₀ with hy
    have hyi : y ∈ lat F (0 + 1) (i + 1) := fun k => by
      have : (uniformizer F : F) ^ (i + 1) * y k = (uniformizer F : F) * x₀ := by
        simp only [hy]; field_simp; ring
      rw [this]; exact hx₀
    have hval : (uniformizer F : F) ^ (i + 1 + d) * (((uniformizer F : F) ^ i)⁻¹ * x₀) =
        (uniformizer F : F) ^ d * ((uniformizer F : F) * x₀) := by
      field_simp; ring
    have hint : (uniformizer F : F) ^ d * ((uniformizer F : F) * x₀) ∈ 𝒪[F] :=
      (𝒪[F]).mul_mem ((𝒪[F]).pow_mem hO _) hx₀
    have hyj : y ∈ lat F (0 + 1) (i + 1 + d + 1) := fun k => by
      have : (uniformizer F : F) ^ (i + 1 + d + 1) * y k =
          (uniformizer F : F) * ((uniformizer F : F) ^ d * ((uniformizer F : F) * x₀)) := by
        simp only [hy]; rw [pow_succ, mul_comm _ (uniformizer F : F), mul_assoc, hval]
      rw [this]; exact (𝒪[F]).mul_mem hO hint
    have d1 : (fun _ : Fin (0 + 1) => ((uniformizerUnit F ^ i : Fˣ) : F)) ⬝ᵥ y = x₀ := by
      simp [dotProduct, hy, hpi]
    have d2 : (fun _ : Fin (0 + 1) => ((uniformizerUnit F ^ (i + 1 + d) : Fˣ) : F)) ⬝ᵥ y =
        (uniformizer F : F) ^ d * ((uniformizer F : F) * x₀) := by
      rw [← hval]
      simp [dotProduct, hy]
    have h1 := hW2 i y hyi
    have h2 := hW2 (i + 1 + d) y hyj
    rw [d1] at h1
    rw [d2, hψ.1 _ hint, one_smul] at h2
    exact orth B hU y _ _ _ hne h1 h2
  set w : ℕ → V := fun j => (((Vj j : ℝ) : ℂ)⁻¹) • W j with hw
  have hconj : ∀ j, starRingEnd ℂ (((Vj j : ℝ) : ℂ)⁻¹) = ((Vj j : ℝ) : ℂ)⁻¹ := fun j => by
    rw [map_inv₀, Complex.conj_ofReal]
  have hwv : ∀ j, B (w j) v = ((Vj j : ℝ) : ℂ)⁻¹ * B (W j) v := fun j => by
    simp only [hw, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hconj]
  have h2 : ∀ j, B (w j) v = B (w j) (w j) := fun j => by
    have : B (w j) (w j) = ((Vj j : ℝ) : ℂ)⁻¹ * (((Vj j : ℝ) : ℂ)⁻¹ * B (W j) (W j)) := by
      simp only [hw, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hconj, map_smul]
    rw [this, hwv, hWW, inv_mul_cancel_left₀ (hVne j)]
  have h1 : ∀ j, B v (w j) = B (w j) (w j) := fun j => by
    rw [← hB.herm (w j) v, h2, hB.herm]
  have h3 : ∀ i j, i ≠ j → B (w i) (w j) = 0 := by
    intro i j hij
    have hz : B (W i) (W j) = 0 := by
      rcases lt_or_gt_of_ne hij with h | h
      · exact hWo i j h
      · rw [← hB.herm (W j) (W i), hWo j i h, map_zero]
    simp only [hw, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, map_smul, hz, mul_zero]
  have hV₀ := (lat_facts (μ := μ) hL0 hψ 1).2
  have hterm : ∀ j : ℕ, (qF F : ℝ) ^ (j * (n - 2)) *
      (B' (ρ (torusPow F n (Pi.single ⟨0, by omega⟩ (j : ℤ))) v)
        (ρ (torusPow F n (Pi.single ⟨0, by omega⟩ (j : ℤ))) v)).re =
      (Measure.pi fun _ : Fin (0 + 1) => μ).real (lat F (0 + 1) 1) * (B (w j) (w j)).re := by
    intro j
    have hk := key (μ := μ) hL0 hL2 hL3c hψ hn ⟨0, by omega⟩ h₀ hs hB hC v hv j
    rw [← hW1 j (B v)] at hk
    rw [torusPow_eq_dg, hk]
    have hmod : (Measures.modulus ((uniformizerUnit F ^ j : Fˣ) : F) : ℝ) = ((qF F : ℝ)⁻¹) ^ j := by
      rw [hcoe, map_pow, modulus_uniformizer]
      simp
    have hvol := vol_rel (μ := μ) hL0 hψ (uniformizerUnit F ^ j) (j + 1) 1 (fun x => by
      have : (uniformizer F : F) ^ 1 * (((uniformizerUnit F ^ j : Fˣ) : F) * x) =
          (uniformizer F : F) ^ (j + 1) * x := by
        rw [hcoe]; ring
      rw [this])
    have hBv : B v (W j) = ((Vj j : ℝ) : ℂ) * B (w j) (w j) := by
      rw [← h1 j]
      simp only [hw, map_smul, smul_eq_mul]
      rw [mul_inv_cancel_left₀ (hVne j)]
    have hq : ((qF F : ℝ)) ≠ 0 := by exact_mod_cast (qF_pos (F := F)).ne'
    have hn2 : n - 1 - 1 = n - 2 := by omega
    set r : ℝ := (Measures.modulus ((uniformizerUnit F ^ j : Fˣ) : F) : ℝ) with hr
    have hrq : (qF F : ℝ) ^ (j * (n - 2)) * r ^ (n - 2) = 1 := by
      rw [hmod, pow_mul, ← mul_pow, ← mul_pow, mul_inv_cancel₀ hq, one_pow, one_pow]
    rw [hBv, hvol, hn2]
    have e : ((r : ℝ) : ℂ) * (((r : ℝ) : ℂ) ^ (n - 2) * (((Vj j : ℝ) : ℂ) * B (w j) (w j))) =
        ((r * r ^ (n - 2) * Vj j : ℝ) : ℂ) * B (w j) (w j) := by
      push_cast; ring
    rw [e, Complex.re_ofReal_mul]
    calc (qF F : ℝ) ^ (j * (n - 2)) * (r * r ^ (n - 2) * Vj j * (B (w j) (w j)).re)
        = ((qF F : ℝ) ^ (j * (n - 2)) * r ^ (n - 2)) * (r * Vj j * (B (w j) (w j)).re) := by ring
      _ = _ := by rw [hrq, one_mul]
  refine ⟨(Measure.pi fun _ : Fin (0 + 1) => μ).real (lat F (0 + 1) 1) * (B v v).re, fun T => ?_⟩
  calc _ = ∑ j ∈ Finset.range T,
        (Measure.pi fun _ : Fin (0 + 1) => μ).real (lat F (0 + 1) 1) * (B (w j) (w j)).re :=
        Finset.sum_congr rfl fun j _ => hterm j
    _ = (Measure.pi fun _ : Fin (0 + 1) => μ).real (lat F (0 + 1) 1) *
        ∑ j ∈ Finset.range T, (B (w j) (w j)).re := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (bessel B hB.psd v w h1 h2 h3 T) hV₀.le

end GlobalTheory.CompanionTheory.SatakeBessel

end
