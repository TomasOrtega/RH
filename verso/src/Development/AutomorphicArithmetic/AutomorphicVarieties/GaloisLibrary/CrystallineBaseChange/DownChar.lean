import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.RnStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.MemMirabIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.NslMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.NslMdiffPos

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Nf UpperTheory.V.Sd Matrix CongruenceSubgroup
open UpperHalfPlane hiding I
open scoped MatrixGroups ModularForm

/- English proof (translation)
Distinguish the cases in `hd : IsUnit d`. Conclude with `⟨0, by simpa using hd⟩`. Take `⟨a, b, e⟩` from `h`. Establish `hN : IsUnit N`. Break down `IsLocalRing.isUnit_or_isUnit_of_add_one e with h | h` into its components or cases.

Conclude with `absurd (isUnit_of_mul_isUnit_right h) hd`. Conclude with `isUnit_of_mul_isUnit_right h`. Use `⟨1, ?_⟩` and prove the remaining obligations. Establish `: IsUnit ((d + N * 1) + -d)` using `by simpa using hN`. Break down `IsLocalRing.isUnit_or_isUnit_of_isUnit_add this with h | h` into its components or cases.

Conclude with `h`. Conclude with `absurd h.neg (by simpa using hd)`.
-/
private theorem loc_unit {R : Type} [CommRing R] [IsLocalRing R] {d N : R} (h : IsCoprime d N) : ∃ y, IsUnit (d + N * y) := by
  by_cases hd : IsUnit d
  · exact ⟨0, by simpa using hd⟩
  · obtain ⟨a, b, e⟩ := h
    have hN : IsUnit N := by
      rcases IsLocalRing.isUnit_or_isUnit_of_add_one e with h | h
      · exact absurd (isUnit_of_mul_isUnit_right h) hd
      · exact isUnit_of_mul_isUnit_right h
    refine ⟨1, ?_⟩
    have : IsUnit ((d + N * 1) + -d) := by simpa using hN
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add this with h | h
    · exact h
    · exact absurd h.neg (by simpa using hd)

private noncomputable def jj : (∀ v : HeightOneSpectrum (𝓞 ℚ), v.adicCompletionIntegers ℚ) →+* Af ℚ where
  toFun x := ⟨fun v => (x v : v.adicCompletion ℚ), Filter.Eventually.of_forall fun v => (x v).2⟩
  map_one' := FiniteAdeleRing.ext _ fun _ => rfl
  map_mul' _ _ := FiniteAdeleRing.ext _ fun _ => rfl
  map_zero' := FiniteAdeleRing.ext _ fun _ => rfl
  map_add' _ _ := FiniteAdeleRing.ext _ fun _ => rfl

/- English proof (translation)
Rewrite using `[Ohat, Subring.mem_iInf]`. Conclude with `fun v => (x v).2`.
-/
private theorem jj_mem (x) : jj x ∈ Ohat ℚ := by
  rw [Ohat, Subring.mem_iInf]
  exact fun v => (x v).2

/- English proof (translation)
Use `choose y hy using fun v : HeightOneSpectrum (𝓞 ℚ) => loc_unit (h.map (Int.castRingHom (v.adicCompletionIntegers ℚ)))`. Establish `hu : IsUnit ((d : ∀ v : HeightOneSpectrum (𝓞 ℚ), v.adicCompletionIntegers ℚ) + N * y)` using `Pi.isUnit_iff.2 fun v => by simpa using hy v`. Take `⟨w, hw⟩` from `hu`. Use `⟨Units.map jj.toMonoidHom w, ⟨jj_mem _, jj_mem _⟩, jj y, jj_mem _, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `jj w - d = _`.

Rewrite using `[hw]`. Simplify using the standard rewrite rules.
-/
private theorem ex_unit {d : ℤ} {N : ℕ} (h : IsCoprime d (N : ℤ)) :
    ∃ u, IsZU u ∧ ∃ y ∈ Ohat ℚ, (u : Af ℚ) - d = N * y := by
  choose y hy using fun v : HeightOneSpectrum (𝓞 ℚ) =>
    loc_unit (h.map (Int.castRingHom (v.adicCompletionIntegers ℚ)))
  have hu : IsUnit ((d : ∀ v : HeightOneSpectrum (𝓞 ℚ), v.adicCompletionIntegers ℚ) + N * y) :=
    Pi.isUnit_iff.2 fun v => by simpa using hy v
  obtain ⟨w, hw⟩ := hu
  refine ⟨Units.map jj.toMonoidHom w, ⟨jj_mem _, jj_mem _⟩, jj y, jj_mem _, ?_⟩
  change jj w - d = _
  rw [hw]
  simp

/- English proof (translation)
Use extensionality with `i j`. Express the relevant statement in the definitionally equal form `(1 : Matrix (Fin 2) (Fin 2) S) i j - s ((1 : Matrix (Fin 2) (Fin 2) R) i j) + s (Matrix.scalar (Fin 2) u.val i j) = Matrix.scalar (Fin 2) (1 - s 1 + s u.val) i j`. Apply the tactic sequence `by_cases e : i = j <;> simp [Matrix.one_apply, e]`.
-/
private theorem corner_sc {R S : Type} [CommRing R] [CommRing S] (s : R →ₙ+* S) (u : Rˣ) :
    cornerGL 2 s (GeneralLinearGroup.scalar (Fin 2) u) = GeneralLinearGroup.scalar (Fin 2) (Units.map (corner s) u) := by
  ext i j
  change (1 : Matrix (Fin 2) (Fin 2) S) i j - s ((1 : Matrix (Fin 2) (Fin 2) R) i j) + s (Matrix.scalar (Fin 2) u.val i j) =
    Matrix.scalar (Fin 2) (1 - s 1 + s u.val) i j
  by_cases e : i = j <;> simp [Matrix.one_apply, e]

/- English proof (translation)
Take `⟨c, hc⟩ : (N : ℤ) ∣ δ 1 0` from `(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (Gamma0_mem.1 hδ0)`. Establish `hdet : δ 0 0 * δ 1 1 - δ 0 1 * δ 1 0 = 1`. Use `δ.det_coe` as an intermediate fact. Rewrite `this` using `[Matrix.det_fin_two]`. Then use the resulting hypothesis. Take `⟨u, hu, y, hy, hd⟩` from `ex_unit (d := δ 1 1) (N := N) ⟨δ 0 0, -(δ 0 1 * c), by rw [hc] at hdet; linear_combination hdet⟩`.

Establish `hI : ∀ n : ℤ, (n : Af ℚ) ∈ Ohat ℚ` using `fun n => intCast_mem _ n`. Establish `hδ : ∀ (δ : SL(2, ℤ)) a b, (toF (Matrix.SpecialLinearGroup.mapGL ℚ δ)).val a b = ((δ a b : ℤ) : Af ℚ)`. Introduce `δ a b`. Use `show algebraMap ℚ (Af ℚ) (algebraMap ℤ ℚ (δ a b)) = _`. Simplify using the standard rewrite rules.

Establish `e1 : ∀ a b, ((toF (Matrix.SpecialLinearGroup.mapGL ℚ δ))⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) u).val a b = (((δ⁻¹ : SL(2, ℤ)) a b : ℤ) : Af ℚ) * u`. Introduce `a b`. Rewrite using `[← map_inv, ← map_inv, Units.val_mul, ← hδ]`. Simplify using the standard rewrite rules. Establish `e2 : ∀ a b, (((toF (Matrix.SpecialLinearGroup.mapGL ℚ δ))⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) u)⁻¹).val a b = (u⁻¹ : (Af ℚ)ˣ) * ((δ a b : ℤ) : Af ℚ)`.

Introduce `a b`. Rewrite using `[_root_.mul_inv_rev, inv_inv, ← map_inv, Units.val_mul, ← hδ]`. Generalize the expression as in `u⁻¹ = v`. Simplify using the standard rewrite rules. Establish `i10 : (δ⁻¹ : SL(2, ℤ)) 1 0 = -δ 1 0` using `by rw [Matrix.SpecialLinearGroup.SL2_inv_expl]; rfl`.

Establish `i11 : (δ⁻¹ : SL(2, ℤ)) 1 1 = δ 0 0` using `by rw [Matrix.SpecialLinearGroup.SL2_inv_expl]; rfl`. Establish `hdet' : ((δ 0 0 : ℤ) : Af ℚ) * (δ 1 1 : ℤ) - (δ 0 1 : ℤ) * (N * c) = 1`. Rewrite `hdet` using `[hc]`. Conclude with `congrArg (Int.cast : ℤ → Af ℚ) hdet` after adjusting the coercions. Use `⟨u, hu, (memK N _).2 ⟨fun a b => ?_, fun a b => ?_, ⟨-(c * u), neg_mem (mul_mem (hI _) hu.1), ?_⟩, (δ 0 0 : ℤ) * y + (δ 0 1 : ℤ) * c, add_mem (mul_mem (hI _) hy) (mul_mem (hI _) (hI _)), ?_⟩, y, hy, hd⟩` and prove the remaining obligations.

Rewrite using `[e1]`. Conclude with `mul_mem (hI _) hu.1`. Rewrite using `[e2]`. Conclude with `mul_mem hu.2 (hI _)`. Rewrite using `[e1, i10, hc]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, i11]`. Take the linear combination `((δ 0 0 : ℤ) : Af ℚ) * hd + hdet'`.
-/
private theorem ex_K {N : ℕ} (δ : SL(2, ℤ)) (hδ0 : δ ∈ Gamma0 N) : ∃ u, IsZU u ∧
    (toF (Matrix.SpecialLinearGroup.mapGL ℚ δ))⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) u ∈ K1G N ∧
    ∃ y ∈ Ohat ℚ, (u : Af ℚ) - (δ 1 1 : ℤ) = N * y := by
  obtain ⟨c, hc⟩ : (N : ℤ) ∣ δ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (Gamma0_mem.1 hδ0)
  have hdet : δ 0 0 * δ 1 1 - δ 0 1 * δ 1 0 = 1 := by
    have := δ.det_coe
    rwa [Matrix.det_fin_two] at this
  obtain ⟨u, hu, y, hy, hd⟩ := ex_unit (d := δ 1 1) (N := N) ⟨δ 0 0, -(δ 0 1 * c), by rw [hc] at hdet; linear_combination hdet⟩
  have hI : ∀ n : ℤ, (n : Af ℚ) ∈ Ohat ℚ := fun n => intCast_mem _ n
  have hδ : ∀ (δ : SL(2, ℤ)) a b, (toF (Matrix.SpecialLinearGroup.mapGL ℚ δ)).val a b = ((δ a b : ℤ) : Af ℚ) := by
    intro δ a b
    show algebraMap ℚ (Af ℚ) (algebraMap ℤ ℚ (δ a b)) = _
    simp
  have e1 : ∀ a b, ((toF (Matrix.SpecialLinearGroup.mapGL ℚ δ))⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) u).val a b
      = (((δ⁻¹ : SL(2, ℤ)) a b : ℤ) : Af ℚ) * u := by
    intro a b
    rw [← map_inv, ← map_inv, Units.val_mul, ← hδ]
    simp
  have e2 : ∀ a b, (((toF (Matrix.SpecialLinearGroup.mapGL ℚ δ))⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) u)⁻¹).val a b
      = (u⁻¹ : (Af ℚ)ˣ) * ((δ a b : ℤ) : Af ℚ) := by
    intro a b
    rw [_root_.mul_inv_rev, inv_inv, ← map_inv, Units.val_mul, ← hδ]
    generalize u⁻¹ = v
    simp
  have i10 : (δ⁻¹ : SL(2, ℤ)) 1 0 = -δ 1 0 := by rw [Matrix.SpecialLinearGroup.SL2_inv_expl]; rfl
  have i11 : (δ⁻¹ : SL(2, ℤ)) 1 1 = δ 0 0 := by rw [Matrix.SpecialLinearGroup.SL2_inv_expl]; rfl
  have hdet' : ((δ 0 0 : ℤ) : Af ℚ) * (δ 1 1 : ℤ) - (δ 0 1 : ℤ) * (N * c) = 1 := by
    rw [hc] at hdet
    exact_mod_cast congrArg (Int.cast : ℤ → Af ℚ) hdet
  refine ⟨u, hu, (memK N _).2 ⟨fun a b => ?_, fun a b => ?_, ⟨-(c * u), neg_mem (mul_mem (hI _) hu.1), ?_⟩,
    (δ 0 0 : ℤ) * y + (δ 0 1 : ℤ) * c, add_mem (mul_mem (hI _) hy) (mul_mem (hI _) (hI _)), ?_⟩, y, hy, hd⟩
  · rw [e1]; exact mul_mem (hI _) hu.1
  · rw [e2]; exact mul_mem hu.2 (hI _)
  · rw [e1, i10, hc]; push_cast; ring
  · rw [e1, i11]; linear_combination ((δ 0 0 : ℤ) : Af ℚ) * hd + hdet'

/- English proof (translation)
Establish `e : (aff (Units.mk0 z.im z.im_pos.ne') z.re).val = !![z.im, z.re; 0, 1]` using `rfl`. Establish `hd : (!![z.im, z.re; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ).det = z.im` using `by simp`. Establish `hz : (z.im : ℂ) * Complex.I + z.re = z`. Rewrite using `[add_comm]`. Conclude with `Complex.re_add_im z`.

Rewrite using `[e, nsl, hd, abs_of_pos z.im_pos, sign_pos z.im_pos]`. Simplify using `[hz]`.
-/
private theorem nsl_aff (k : ℕ) (f : ℍ → ℂ) (z : ℍ) :
    nsl k f (aff (Units.mk0 z.im z.im_pos.ne') z.re).val UpperHalfPlane.I = ((z.im ^ ((k : ℝ) / 2) : ℝ) : ℂ) * f z := by
  have e : (aff (Units.mk0 z.im z.im_pos.ne') z.re).val = !![z.im, z.re; 0, 1] := rfl
  have hd : (!![z.im, z.re; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ).det = z.im := by simp
  have hz : (z.im : ℂ) * Complex.I + z.re = z := by
    rw [add_comm]; exact Complex.re_add_im z
  rw [e, nsl, hd, abs_of_pos z.im_pos, sign_pos z.im_pos]
  simp [hz]

/- English proof (translation)
Introduce `k N hN χ ω hω f φ hφ hc δ hδ`. Take `⟨u, hu, hK, hd⟩` from `ex_K δ hδ`. Use `set β := Matrix.SpecialLinearGroup.mapGL ℚ δ with hβ`. Establish `h2` using `hω.unit u hu _ hd`. Establish `s3 : GeneralLinearGroup.scalar (Fin 2) (finId ℚ u) = finGL ℚ 2 (GeneralLinearGroup.scalar (Fin 2) u)` using `(corner_sc _ u).symm`.

Establish `hβ' : (toR β).val = δ.1.map (Int.cast : ℤ → ℝ)`. Use extensionality with `i j`. Express the relevant statement in the definitionally equal form `(Rat.castHom ℝ) (algebraMap ℤ ℚ (δ i j)) = _`. Simplify using the standard rewrite rules. Establish `key : ∀ x : GL (Fin 2) ℝ, nsl k f x.val UpperHalfPlane.I = ((ω.1 (finId ℚ u) : ℂˣ) : ℂ) * nsl k f (toR β * x).val UpperHalfPlane.I`.

Introduce `x`. Establish `e : GeneralLinearGroup.scalar (Fin 2) (finId ℚ u) * (ratGL ℚ 2 1 * (upR (toR β * x) * finGL ℚ 2 1)) = ratGL ℚ 2 β * (upR x * finGL ℚ 2 ((toF β)⁻¹ * GeneralLinearGroup.scalar (Fin 2) u))`. Establish `c : ∀ (x : GL (Fin 2) ℝ) (y : GL (Fin 2) (Af ℚ)) (w : GA ℚ 2), finGL ℚ 2 y * (upR x * w) = upR x * (finGL ℚ 2 y * w)` using `fun x y w => by rw [← mul_assoc, ← upR_comm, mul_assoc]`. Rewrite using `[s3, ratGL_eq β, map_one, one_mul]`. Simplify using `only [mul_assoc, c]`.

Simplify using `only [mul_assoc, map_mul, map_inv, mul_inv_cancel_left, map_one, mul_one]`. Rewrite using `[← hφ β x _ hK, ← e, hc, hφ 1 _ 1 (one_mem _)]`. Use function extensionality and compare the values at `z`. Establish `h` using `key (aff (Units.mk0 z.im z.im_pos.ne') z.re)`. Establish `hdet : 0 < (aff (Units.mk0 z.im z.im_pos.ne') z.re).val.det`.

Establish `e : (aff (Units.mk0 z.im z.im_pos.ne') z.re).val = !![z.im, z.re; 0, 1]` using `rfl`. Rewrite using `[e]`. Simplify using `using z.im_pos`. Rewrite `h` using `[Units.val_mul, ← (nslMul k f).1 _ _ (toR β).det_ne_zero hdet, hβ', (nslSl k f).1, nsl_aff, nsl_aff]`. Establish `hne : ((z.im ^ ((k : ℝ) / 2) : ℝ) : ℂ) ≠ 0`.

Conclude with `(Real.rpow_pos_of_pos z.im_pos _).ne'` after adjusting the coercions. Use `mul_left_cancel₀ hne ?_` and prove the remaining obligations. Rewrite using `[Pi.smul_apply, smul_eq_mul]`. Take the linear combination `(-χ ((δ 1 1 : ℤ) : ZMod N)) * h - (((z.im ^ ((k : ℝ) / 2) : ℝ) : ℂ) * (f ∣[(k : ℤ)] δ) z) * h2`.
-/
theorem UpperTheory.V.Br.downChar :
    UpperTheory.V.Br.DownChar := by
  intro k N hN χ ω hω f φ hφ hc δ hδ
  obtain ⟨u, hu, hK, hd⟩ := ex_K δ hδ
  set β := Matrix.SpecialLinearGroup.mapGL ℚ δ with hβ
  have h2 := hω.unit u hu _ hd
  have s3 : GeneralLinearGroup.scalar (Fin 2) (finId ℚ u) = finGL ℚ 2 (GeneralLinearGroup.scalar (Fin 2) u) :=
    (corner_sc _ u).symm
  have hβ' : (toR β).val = δ.1.map (Int.cast : ℤ → ℝ) := by
    ext i j
    change (Rat.castHom ℝ) (algebraMap ℤ ℚ (δ i j)) = _
    simp
  have key : ∀ x : GL (Fin 2) ℝ, nsl k f x.val UpperHalfPlane.I =
      ((ω.1 (finId ℚ u) : ℂˣ) : ℂ) * nsl k f (toR β * x).val UpperHalfPlane.I := by
    intro x
    have e : GeneralLinearGroup.scalar (Fin 2) (finId ℚ u) * (ratGL ℚ 2 1 * (upR (toR β * x) * finGL ℚ 2 1)) =
        ratGL ℚ 2 β * (upR x * finGL ℚ 2 ((toF β)⁻¹ * GeneralLinearGroup.scalar (Fin 2) u)) := by
      have c : ∀ (x : GL (Fin 2) ℝ) (y : GL (Fin 2) (Af ℚ)) (w : GA ℚ 2), finGL ℚ 2 y * (upR x * w) = upR x * (finGL ℚ 2 y * w) :=
        fun x y w => by rw [← mul_assoc, ← upR_comm, mul_assoc]
      rw [s3, ratGL_eq β, map_one, one_mul]
      simp only [mul_assoc, c]
      simp only [mul_assoc, map_mul, map_inv, mul_inv_cancel_left, map_one, mul_one]
    rw [← hφ β x _ hK, ← e, hc, hφ 1 _ 1 (one_mem _)]
  funext z
  have h := key (aff (Units.mk0 z.im z.im_pos.ne') z.re)
  have hdet : 0 < (aff (Units.mk0 z.im z.im_pos.ne') z.re).val.det := by
    have e : (aff (Units.mk0 z.im z.im_pos.ne') z.re).val = !![z.im, z.re; 0, 1] := rfl
    rw [e]
    simpa using z.im_pos
  rw [Units.val_mul, ← (nslMul k f).1 _ _ (toR β).det_ne_zero hdet, hβ', (nslSl k f).1, nsl_aff, nsl_aff] at h
  have hne : ((z.im ^ ((k : ℝ) / 2) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos z.im_pos _).ne'
  refine mul_left_cancel₀ hne ?_
  rw [Pi.smul_apply, smul_eq_mul]
  linear_combination (-χ ((δ 1 1 : ℤ) : ZMod N)) * h - (((z.im ^ ((k : ℝ) / 2) : ℝ) : ℂ) * (f ∣[(k : ℤ)] δ) z) * h2
