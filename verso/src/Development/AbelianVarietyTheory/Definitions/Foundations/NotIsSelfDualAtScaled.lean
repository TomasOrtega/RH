import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice

noncomputable section

namespace GlobalTheory.AdelicU.Model

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)

variable (E) in

def hyp : Matrix (Fin 2) (Fin 2) E := !![0, 1; 1, 0]

omit [NumberField F] [NumberField E] in
/- English proof (translation)
Assemble the required witnesses or components as `⟨fun i j => by fin_cases i <;> fin_cases j <;> simp [hyp], by simp [hyp, Matrix.det_fin_two]⟩`.
-/
theorem isHermND_hyp : IsHermND σ (hyp E) :=
  ⟨fun i j => by fin_cases i <;> fin_cases j <;> simp [hyp], by simp [hyp, Matrix.det_fin_two]⟩

omit [NumberField E] in
/- English proof (translation)
Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, Units.mul_inv, mul_one]`. Both sides reduce to the same expression.
-/
theorem tmul_mul_inv {v : HeightOneSpectrum (𝓞 F)} (a : (Fv F v)ˣ) :
    ((a : Fv F v) ⊗ₜ[F] (1 : E)) * (((a⁻¹ : (Fv F v)ˣ) : Fv F v) ⊗ₜ[F] (1 : E)) = 1 := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, Units.mul_inv, mul_one]; rfl

omit [NumberField E] in
/- English proof (translation)
Rewrite using `[mul_comm, tmul_mul_inv]`.
-/
theorem inv_mul_tmul {v : HeightOneSpectrum (𝓞 F)} (a : (Fv F v)ˣ) :
    (((a⁻¹ : (Fv F v)ˣ) : Fv F v) ⊗ₜ[F] (1 : E)) * ((a : Fv F v) ⊗ₜ[F] (1 : E)) = 1 := by
  rw [mul_comm, tmul_mul_inv]

variable (E) in

def torMat {v : HeightOneSpectrum (𝓞 F)} (a : (Fv F v)ˣ) : Matrix (Fin 2) (Fin 2) (Fv F v ⊗[F] E) :=
  !![(a : Fv F v) ⊗ₜ[F] (1 : E), 0; 0, ((a⁻¹ : (Fv F v)ˣ) : Fv F v) ⊗ₜ[F] (1 : E)]

omit [NumberField E] in
/- English proof (translation)
Establish `h1` using `tmul_mul_inv (E := E) a`. Establish `h2` using `inv_mul_tmul (E := E) a`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;>`. Apply the tactic sequence `simp only [torMat, Matrix.mul_apply, Fin.sum_univ_two, inv_inv] <;> simp [-Units.val_inv_eq_inv_val, h1, h2, Algebra.TensorProduct.one_def]`.
-/
theorem torMat_mul_inv {v : HeightOneSpectrum (𝓞 F)} (a : (Fv F v)ˣ) : torMat E a * torMat E a⁻¹ = 1 := by
  have h1 := tmul_mul_inv (E := E) a
  have h2 := inv_mul_tmul (E := E) a
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [torMat, Matrix.mul_apply, Fin.sum_univ_two, inv_inv] <;> simp [-Units.val_inv_eq_inv_val, h1, h2, Algebra.TensorProduct.one_def]

def tor {v : HeightOneSpectrum (𝓞 F)} (a : (Fv F v)ˣ) : GLoc σ (hyp E) v :=
  ⟨⟨torMat E a, torMat E a⁻¹, torMat_mul_inv a, by simpa using torMat_mul_inv (E := E) a⁻¹⟩, by
    change cT _ (torMat E a) * JR _ (hyp E) * torMat E a = JR _ (hyp E)
    have h1 := tmul_mul_inv (E := E) a
    have h2 := inv_mul_tmul (E := E) a
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [-Units.val_inv_eq_inv_val, torMat, cT, JR, hyp, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Matrix.mul_apply, Fin.sum_univ_two, h1, h2,
        Algebra.TensorProduct.one_def]⟩

/- English proof (translation)
Use `le_antisymm ((normFin_le_iff F v).2 fun i j => ?_) (max_le ?_ ?_)` and prove the remaining obligations. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [torMat, absFin_tmul_one]`. Simplify `absFin_le_normFin F v (torMat E a) 0 0` using `[torMat, absFin_tmul_one]`. Simplify `absFin_le_normFin F v (torMat E a) 1 1` using `[torMat, absFin_tmul_one]`.
-/
theorem normFin_torMat {v : HeightOneSpectrum (𝓞 F)} (a : (Fv F v)ˣ) :
    normFin F v (torMat E a) = max ‖(a : Fv F v)‖₊ ‖(a : Fv F v)‖₊⁻¹ := by
  refine le_antisymm ((normFin_le_iff F v).2 fun i j => ?_) (max_le ?_ ?_)
  · fin_cases i <;> fin_cases j <;> simp [torMat, absFin_tmul_one]
  · simpa [torMat, absFin_tmul_one] using absFin_le_normFin F v (torMat E a) 0 0
  · simpa [torMat, absFin_tmul_one] using absFin_le_normFin F v (torMat E a) 1 1

/- English proof (translation)
Rewrite using `[height_emb]`. Express the relevant statement in the definitionally equal form `max 1 (max (normFin F v (torMat E a)) (normFin F v (torMat E a⁻¹))) = _`. Rewrite using `[normFin_torMat, normFin_torMat, Units.val_inv_eq_inv_val, nnnorm_inv, inv_inv, max_comm (‖(a : Fv F v)‖₊⁻¹), max_self]`. Use `max_eq_right ?_` and prove the remaining obligations. Establish `h0 : 0 < ‖(a : Fv F v)‖₊` using `by simp`.

Break down `le_total 1 ‖(a : Fv F v)‖₊ with h | h` into its components or cases. Conclude with `le_max_of_le_left h`. Conclude with `le_max_of_le_right ((one_le_inv₀ h0).2 h)`.
-/
theorem height_emb_tor {v : HeightOneSpectrum (𝓞 F)} (a : (Fv F v)ˣ) :
    height σ (hyp E) (emb σ (hyp E) v (tor σ a)) = max ‖(a : Fv F v)‖₊ ‖(a : Fv F v)‖₊⁻¹ := by
  rw [height_emb]
  change max 1 (max (normFin F v (torMat E a)) (normFin F v (torMat E a⁻¹))) = _
  rw [normFin_torMat, normFin_torMat, Units.val_inv_eq_inv_val, nnnorm_inv, inv_inv, max_comm (‖(a : Fv F v)‖₊⁻¹),
    max_self]
  refine max_eq_right ?_
  have h0 : 0 < ‖(a : Fv F v)‖₊ := by simp
  rcases le_total 1 ‖(a : Fv F v)‖₊ with h | h
  · exact le_max_of_le_left h
  · exact le_max_of_le_right ((one_le_inv₀ h0).2 h)

/- English proof (translation)
Establish `key : ∀ b : (Fv F v)ˣ, ‖(b : Fv F v)‖₊ = 1 → ∀ y, y ∈ latLoc F (stdLattice E 2) v → torMat E b *ᵥ y ∈ latLoc F (stdLattice E 2) v` using `fun b hb y hy => by`. Rewrite `hy`, the goal using `[mem_latLoc_stdLattice]`. Establish `hb1 : (b : Fv F v) ∈ v.adicCompletionIntegers F` using `Valued.toNormedField.norm_le_one_iff.1 (show ‖(b : Fv F v)‖ ≤ 1 from by exact_mod_cast hb.le)`. Establish `hb2 : ((b⁻¹ : (Fv F v)ˣ) : Fv F v) ∈ v.adicCompletionIntegers F` using `Valued.toNormedField.norm_le_one_iff.1 (show ‖((b⁻¹ : (Fv F v)ˣ) : Fv F v)‖ ≤ 1 from by`. Establish `: ‖(b : Fv F v)‖ = 1` using `congrArg NNReal.toReal hb`.

Simplify using `[this])`. Introduce `i`. Use `fin_cases i`. Simplify `mul_mem (tmul_mem_intLoc hb1 (1 : 𝓞 E)) (hy 0)` using `[torMat, Matrix.mulVec, dotProduct]`. Simplify `mul_mem (tmul_mem_intLoc hb2 (1 : 𝓞 E)) (hy 1)` using `[torMat, Matrix.mulVec, dotProduct]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h1` using `normFin_conj_le_one (isLatticeFrame_one (F := F)) h`. Rewrite `h1` using `[map_one, inv_one, one_mul, mul_one]`. Express the relevant statement in the definitionally equal form `normFin F v (torMat E a) ≤ 1 at h1`.

Rewrite `h1` using `[normFin_torMat, max_le_iff]`. Establish `h0 : 0 < ‖(a : Fv F v)‖₊` using `by simp`. Conclude with `le_antisymm h1.1 ((inv_le_one₀ h0).1 h1.2)`. Introduce `h y`. Use `⟨key a h y, fun hy => ?_⟩` and prove the remaining obligations.

Use `key a⁻¹ (by simp [h]) _ hy` as an intermediate fact. Express the relevant statement in the definitionally equal form `torMat E a⁻¹ *ᵥ (torMat E a *ᵥ y) ∈ _ at this`. Rewrite `this` using `[Matrix.mulVec_mulVec, show torMat E a⁻¹ * torMat E a = 1 by simpa using torMat_mul_inv (E := E) a⁻¹, Matrix.one_mulVec]`. Then use the resulting hypothesis.
-/
theorem tor_mem_stabLoc {v : HeightOneSpectrum (𝓞 F)} (a : (Fv F v)ˣ) :
    tor σ a ∈ stabLoc σ (hyp E) (stdLattice E 2) v ↔ ‖(a : Fv F v)‖₊ = 1 := by
  have key : ∀ b : (Fv F v)ˣ, ‖(b : Fv F v)‖₊ = 1 → ∀ y, y ∈ latLoc F (stdLattice E 2) v →
      torMat E b *ᵥ y ∈ latLoc F (stdLattice E 2) v := fun b hb y hy => by
    rw [mem_latLoc_stdLattice] at hy ⊢
    have hb1 : (b : Fv F v) ∈ v.adicCompletionIntegers F :=
      Valued.toNormedField.norm_le_one_iff.1 (show ‖(b : Fv F v)‖ ≤ 1 from by exact_mod_cast hb.le)
    have hb2 : ((b⁻¹ : (Fv F v)ˣ) : Fv F v) ∈ v.adicCompletionIntegers F :=
      Valued.toNormedField.norm_le_one_iff.1 (show ‖((b⁻¹ : (Fv F v)ˣ) : Fv F v)‖ ≤ 1 from by
        have : ‖(b : Fv F v)‖ = 1 := congrArg NNReal.toReal hb
        simp [this])
    intro i
    fin_cases i
    · simpa [torMat, Matrix.mulVec, dotProduct] using mul_mem (tmul_mem_intLoc hb1 (1 : 𝓞 E)) (hy 0)
    · simpa [torMat, Matrix.mulVec, dotProduct] using mul_mem (tmul_mem_intLoc hb2 (1 : 𝓞 E)) (hy 1)
  constructor
  · intro h
    have h1 := normFin_conj_le_one (isLatticeFrame_one (F := F)) h
    rw [map_one, inv_one, one_mul, mul_one] at h1
    change normFin F v (torMat E a) ≤ 1 at h1
    rw [normFin_torMat, max_le_iff] at h1
    have h0 : 0 < ‖(a : Fv F v)‖₊ := by simp
    exact le_antisymm h1.1 ((inv_le_one₀ h0).1 h1.2)
  · intro h y
    refine ⟨key a h y, fun hy => ?_⟩
    have := key a⁻¹ (by simp [h]) _ hy
    change torMat E a⁻¹ *ᵥ (torMat E a *ᵥ y) ∈ _ at this
    rwa [Matrix.mulVec_mulVec, show torMat E a⁻¹ * torMat E a = 1 by simpa using torMat_mul_inv (E := E) a⁻¹,
      Matrix.one_mulVec] at this

/- English proof (translation)
Use `letI : NontriviallyNormedField (Fv F v) := Valued.toNontriviallyNormedField (Fv F v) (WithZero (Multiplicative ℤ))`. Take `⟨a, ha⟩` from `NontriviallyNormedField.non_trivial (α := Fv F v)`. Conclude with `⟨Units.mk0 a (by rintro rfl; simp at ha; linarith), ha⟩`.
-/
theorem exists_one_lt (v : HeightOneSpectrum (𝓞 F)) : ∃ a : (Fv F v)ˣ, 1 < ‖(a : Fv F v)‖ := by
  letI : NontriviallyNormedField (Fv F v) := Valued.toNontriviallyNormedField (Fv F v) (WithZero (Multiplicative ℤ))
  obtain ⟨a, ha⟩ := NontriviallyNormedField.non_trivial (α := Fv F v)
  exact ⟨Units.mk0 a (by rintro rfl; simp at ha; linarith), ha⟩

/- English proof (translation)
Introduce `h` and use `by obtain ⟨a, ha⟩ := exists_one_lt v have := (tor_mem_stabLoc σ a).1 (h ▸ Subgroup.mem_top _) exact ha.ne' (congrArg NNReal.toReal this)`.
-/
theorem stabLoc_ne_top (v : HeightOneSpectrum (𝓞 F)) : stabLoc σ (hyp E) (stdLattice E 2) v ≠ ⊤ := fun h => by
  obtain ⟨a, ha⟩ := exists_one_lt v
  have := (tor_mem_stabLoc σ a).1 (h ▸ Subgroup.mem_top _)
  exact ha.ne' (congrArg NNReal.toReal this)

/- English proof (translation)
Take `⟨I, hI⟩` from `Ideal.exists_maximal (𝓞 F)`. Set `v : HeightOneSpectrum (𝓞 F)` to `⟨I, hI.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hI (RingOfIntegers.not_isField F)⟩`. Take `⟨a, ha⟩` from `exists_one_lt v`. Take `⟨k, hk⟩` from `pow_unbounded_of_one_lt c ha`. Use `⟨emb σ _ v (tor σ (a ^ k)), ?_⟩` and prove the remaining obligations.

Rewrite using `[height_emb_tor]`. Use `hk.le.trans ?_` and prove the remaining obligations. Rewrite using `[NNReal.coe_max]`. Conclude with `le_max_of_le_left (by simp)`.
-/
theorem height_unbounded (c : ℝ) : ∃ g : GAd σ (hyp E), c ≤ height σ (hyp E) g := by
  obtain ⟨I, hI⟩ := Ideal.exists_maximal (𝓞 F)
  let v : HeightOneSpectrum (𝓞 F) := ⟨I, hI.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hI (RingOfIntegers.not_isField F)⟩
  obtain ⟨a, ha⟩ := exists_one_lt v
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt c ha
  refine ⟨emb σ _ v (tor σ (a ^ k)), ?_⟩
  rw [height_emb_tor]
  refine hk.le.trans ?_
  rw [NNReal.coe_max]
  exact le_max_of_le_left (by simp)

/- English proof (translation)
Introduce and unpack `⟨C, N, h⟩`. Establish `ht` using `(Real.tendsto_exp_div_pow_atTop N).eventually_gt_atTop C`. Take `⟨c, hc⟩` from `Filter.eventually_atTop.1 ht`. Take `⟨g, hg⟩` from `height_unbounded σ c`. Establish `h1` using `hc _ hg`.

Establish `h2` using `h g`. Establish `h3 : (0 : ℝ) < (height σ (hyp E) g : ℝ) ^ N` using `pow_pos (lt_of_lt_of_le one_pos (by exact_mod_cast one_le_height σ _ g)) N`. Rewrite `h1` using `[lt_div_iff₀ h3]`. Rewrite `h2` using `[Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem not_moderateGrowth_exp : ¬ ModerateGrowth σ (hyp E) fun g => Real.exp (height σ (hyp E) g) := by
  rintro ⟨C, N, h⟩
  have ht := (Real.tendsto_exp_div_pow_atTop N).eventually_gt_atTop C
  obtain ⟨c, hc⟩ := Filter.eventually_atTop.1 ht
  obtain ⟨g, hg⟩ := height_unbounded σ c
  have h1 := hc _ hg
  have h2 := h g
  have h3 : (0 : ℝ) < (height σ (hyp E) g : ℝ) ^ N :=
    pow_pos (lt_of_lt_of_le one_pos (by exact_mod_cast one_le_height σ _ g)) N
  rw [lt_div_iff₀ h3] at h1
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at h2
  linarith

/- English proof (translation)
Establish `e : ∀ y x : Fin 2 → Fv F v ⊗[F] E, hLin σ (hyp E) (Fv F v) y x = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ (x 0) * y 1 + Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ (x 1) * y 0` using `fun y x => by`. Simplify using `[hLin, hR, hform, JR, hyp]`. Use extensionality with `y`. Rewrite using `[mem_latLoc_stdLattice]`. Prove the components needed by the constructor for the conclusion.

Introduce `hy x hx`. Rewrite using `[e]`. Conclude with `add_mem (mul_mem (sigR_mem_intLoc σ (mem_latLoc_stdLattice.1 hx 0)) (hy 1)) (mul_mem (sigR_mem_intLoc σ (mem_latLoc_stdLattice.1 hx 1)) (hy 0))`. Introduce `hy i`. Apply the tactic sequence `have h0 := hy ![1, 0] (mem_latLoc_stdLattice.2 fun j => by fin_cases j <;> simp)`.

Apply the tactic sequence `have h1 := hy ![0, 1] (mem_latLoc_stdLattice.2 fun j => by fin_cases j <;> simp)`. Rewrite `h0`, `h1` using `[e]`. Use `fin_cases i`. Simplify using `using h1`. Simplify using `using h0`.
-/
theorem isSelfDualAt_hyp (v : HeightOneSpectrum (𝓞 F)) : IsSelfDualAt σ (hyp E) (stdLattice E 2) v := by
  have e : ∀ y x : Fin 2 → Fv F v ⊗[F] E, hLin σ (hyp E) (Fv F v) y x =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ (x 0) * y 1 + Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ (x 1) * y 0 := fun y x => by
    simp [hLin, hR, hform, JR, hyp]
  ext y
  rw [mem_latLoc_stdLattice]
  constructor
  · intro hy x hx
    rw [e]
    exact add_mem (mul_mem (sigR_mem_intLoc σ (mem_latLoc_stdLattice.1 hx 0)) (hy 1))
      (mul_mem (sigR_mem_intLoc σ (mem_latLoc_stdLattice.1 hx 1)) (hy 0))
  · intro hy i
    have h0 := hy ![1, 0] (mem_latLoc_stdLattice.2 fun j => by fin_cases j <;> simp)
    have h1 := hy ![0, 1] (mem_latLoc_stdLattice.2 fun j => by fin_cases j <;> simp)
    rw [e] at h0 h1
    fin_cases i
    · simpa using h1
    · simpa using h0

variable {σ} in

/- English proof (translation)
Establish `key : ∀ y : GArch σ (1 : Matrix (Fin n) (Fin n) E) w, matHom _ σ 1 y ∈ UJ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion σ) 1` using `fun y => by`. Establish `: y.1 ∈ UJ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion σ) (JR w.Completion (1 : Matrix (Fin n) (Fin n) E))` using `y.2`. Rewrite `this` using `[show JR w.Completion (1 : Matrix (Fin n) (Fin n) E) = 1 by simp [JR]]`. Then use the resulting hypothesis. Rewrite using `[height_embArch, htInf, htOf_eq_one]`. Conclude with `⟨normInf_le_one_of_unitary h (key x), normInf_le_one_of_unitary h (inv_mem (key x))⟩`.
-/
theorem height_ofInf_definite (h : IsCMExt F E σ) {n : ℕ} (w : InfinitePlace F)
    (x : GArch σ (1 : Matrix (Fin n) (Fin n) E) w) : height σ 1 (embArch σ 1 w x) = 1 := by
  have key : ∀ y : GArch σ (1 : Matrix (Fin n) (Fin n) E) w,
      matHom _ σ 1 y ∈ UJ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion σ) 1 := fun y => by
    have : y.1 ∈ UJ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion σ) (JR w.Completion (1 : Matrix (Fin n) (Fin n) E)) := y.2
    rwa [show JR w.Completion (1 : Matrix (Fin n) (Fin n) E) = 1 by simp [JR]] at this
  rw [height_embArch, htInf, htOf_eq_one]
  exact ⟨normInf_le_one_of_unitary h (key x), normInf_le_one_of_unitary h (inv_mem (key x))⟩

section Supp

omit [NumberField E] in
/- English proof (translation)
Rewrite using `[← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.comp_id]`.
-/
theorem map_map_tens {R R' R'' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] [CommRing R'']
    [Algebra F R''] (φ : R →ₐ[F] R') (ψ : R' →ₐ[F] R'') (y : R ⊗[F] E) :
    Algebra.TensorProduct.map ψ (AlgHom.id F E) (Algebra.TensorProduct.map φ (AlgHom.id F E) y) =
      Algebra.TensorProduct.map (ψ.comp φ) (AlgHom.id F E) y := by
  rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.comp_id]

omit [NumberField E] in
/- English proof (translation)
Use `GlobalTheory.AutFunCounterexample.tens_inj (F := F) (E := E) (A := Ainf F) (B := Af F) (n := 1) (Matrix.of fun _ _ => y) (by` as an intermediate fact. Use extensionality with `i j`. Rewrite using `[Subsingleton.elim i j, Matrix.one_apply_eq]`. Conclude with `GlobalTheory.AutFunCompare.infTens_ext fun w => (map_map_tens _ _ y).trans ((h1 w).trans (map_one _).symm))`. Use the proof step `(by`.

Use extensionality with `i j`. Rewrite using `[Subsingleton.elim i j, Matrix.one_apply_eq]`. Conclude with `GlobalTheory.LatticeLocalGlobal.ext_components _ _ fun v => (map_map_tens _ _ y).trans ((h2 v).trans (map_one _).symm))`. Conclude with `congrFun (congrFun this 0) 0`.
-/
theorem adTens_eq_one {y : AF F ⊗[F] E} (h1 : ∀ w, compInf F E w y = 1) (h2 : ∀ v, compFin F E v y = 1) : y = 1 := by
  have := GlobalTheory.AutFunCounterexample.tens_inj (F := F) (E := E) (A := Ainf F) (B := Af F) (n := 1) (Matrix.of fun _ _ => y)
    (by
      ext i j
      rw [Subsingleton.elim i j, Matrix.one_apply_eq]
      exact GlobalTheory.AutFunCompare.infTens_ext fun w => (map_map_tens _ _ y).trans ((h1 w).trans (map_one _).symm))
    (by
      ext i j
      rw [Subsingleton.elim i j, Matrix.one_apply_eq]
      exact GlobalTheory.LatticeLocalGlobal.ext_components _ _ fun v =>
        (map_map_tens _ _ y).trans ((h2 v).trans (map_one _).symm))
  exact congrFun (congrFun this 0) 0

/- English proof (translation)
Establish `c0 : ∀ w, compInf F E w (algebraMap (AF F) (AF F ⊗[F] E) ε) = 0` using `fun w => by`. Express the relevant statement in the definitionally equal form `evInf F w ε ⊗ₜ[F] (1 : E) = 0`. Rewrite using `[e0, TensorProduct.zero_tmul]`. Establish `c1 : compFin F E v (algebraMap (AF F) (AF F ⊗[F] E) ε) = 1`. Express the relevant statement in the definitionally equal form `evFin F v ε ⊗ₜ[F] (1 : E) = 1`.

Rewrite using `[e1]`. Both sides reduce to the same expression. Establish `c2 : ∀ u, u ≠ v → compFin F E u (algebraMap (AF F) (AF F ⊗[F] E) ε) = 0` using `fun u hu => by`. Express the relevant statement in the definitionally equal form `evFin F u ε ⊗ₜ[F] (1 : E) = 0`. Rewrite using `[e2 u hu, TensorProduct.zero_tmul]`.

Establish `one : ∀ {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (m : Matrix (Fin n) (Fin n) A), m.map φ = 1 ↔ ∀ i j, φ ((m - 1) i j) = 0` using `fun φ m => by`. Rewrite using `[← Matrix.ext_iff]`. Use `forall₂_congr fun i j => ?_` and prove the remaining obligations. Rewrite using `[Matrix.sub_apply, map_sub, sub_eq_zero, Matrix.map_apply]`. Apply the tactic sequence `by_cases h : i = j <;> simp [Matrix.one_apply, h]`.

Establish `pf : ∀ u, proj σ J u g = 1 ↔ ∀ i j, compFin F E u (((matHom _ σ J g).1 - 1) i j) = 0` using `fun u => Iff.trans ⟨fun h => congrArg (fun x => (matHom _ σ J x).1) h, fun h => Subtype.ext (Units.ext h)⟩ (one _ _)`. Establish `pa : ∀ w, projArch σ J w g = 1 ↔ ∀ i j, compInf F E w (((matHom _ σ J g).1 - 1) i j) = 0` using `fun u => Iff.trans ⟨fun h => congrArg (fun x => (matHom _ σ J x).1) h, fun h => Subtype.ext (Units.ext h)⟩ (one _ _)`. Rewrite using `[range_emb, mem_atPts, mem_finPts_iff_forall]`. Simplify using `only [pf, pa, Finset.mem_singleton]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Conclude with `⟨fun w i j => by rw [← h, map_mul, c0, zero_mul], fun u hu i j => by rw [← h, map_mul, c2 u hu, zero_mul]⟩`. Introduce and unpack `⟨h1, h2⟩ i j`. Rewrite using `[← sub_eq_zero, ← add_eq_right (b := 1)]`. Use `adTens_eq_one (fun w => ?_) fun u => ?_` and prove the remaining obligations.

Rewrite using `[map_add, map_sub, map_mul, h1, map_one]`. Simplify using the standard rewrite rules. Rewrite using `[map_add, map_sub, map_mul, map_one]`. Distinguish the cases in `hu : u = v`. Substitute `hu` using the available equality.

Rewrite using `[c1]`. Simplify using the standard rewrite rules. Rewrite using `[h2 u hu]`. Simplify using the standard rewrite rules.
-/
theorem idem_supp_iff {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F)) (ε : AF F)
    (e0 : ∀ w, evInf F w ε = 0) (e1 : evFin F v ε = 1) (e2 : ∀ u, u ≠ v → evFin F u ε = 0) (g : GAd σ J) :
    (∀ i j, algebraMap (AF F) (AF F ⊗[F] E) ε * ((matHom _ σ J g).1 - 1) i j = ((matHom _ σ J g).1 - 1) i j) ↔
      g ∈ (emb σ J v).range := by
  have c0 : ∀ w, compInf F E w (algebraMap (AF F) (AF F ⊗[F] E) ε) = 0 := fun w => by
    change evInf F w ε ⊗ₜ[F] (1 : E) = 0
    rw [e0, TensorProduct.zero_tmul]
  have c1 : compFin F E v (algebraMap (AF F) (AF F ⊗[F] E) ε) = 1 := by
    change evFin F v ε ⊗ₜ[F] (1 : E) = 1
    rw [e1]; rfl
  have c2 : ∀ u, u ≠ v → compFin F E u (algebraMap (AF F) (AF F ⊗[F] E) ε) = 0 := fun u hu => by
    change evFin F u ε ⊗ₜ[F] (1 : E) = 0
    rw [e2 u hu, TensorProduct.zero_tmul]
  have one : ∀ {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (m : Matrix (Fin n) (Fin n) A),
      m.map φ = 1 ↔ ∀ i j, φ ((m - 1) i j) = 0 := fun φ m => by
    rw [← Matrix.ext_iff]
    refine forall₂_congr fun i j => ?_
    rw [Matrix.sub_apply, map_sub, sub_eq_zero, Matrix.map_apply]
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  have pf : ∀ u, proj σ J u g = 1 ↔ ∀ i j, compFin F E u (((matHom _ σ J g).1 - 1) i j) = 0 := fun u =>
    Iff.trans ⟨fun h => congrArg (fun x => (matHom _ σ J x).1) h, fun h => Subtype.ext (Units.ext h)⟩ (one _ _)
  have pa : ∀ w, projArch σ J w g = 1 ↔ ∀ i j, compInf F E w (((matHom _ σ J g).1 - 1) i j) = 0 := fun u =>
    Iff.trans ⟨fun h => congrArg (fun x => (matHom _ σ J x).1) h, fun h => Subtype.ext (Units.ext h)⟩ (one _ _)
  rw [range_emb, mem_atPts, mem_finPts_iff_forall]
  simp only [pf, pa, Finset.mem_singleton]
  constructor
  · intro h
    exact ⟨fun w i j => by rw [← h, map_mul, c0, zero_mul], fun u hu i j => by rw [← h, map_mul, c2 u hu, zero_mul]⟩
  · rintro ⟨h1, h2⟩ i j
    rw [← sub_eq_zero, ← add_eq_right (b := 1)]
    refine adTens_eq_one (fun w => ?_) fun u => ?_
    · rw [map_add, map_sub, map_mul, h1, map_one]; simp
    · rw [map_add, map_sub, map_mul, map_one]
      by_cases hu : u = v
      · subst hu; rw [c1]; simp
      · rw [h2 u hu]; simp

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Take `⟨α, rfl, h1, h2⟩` from `h`. Conclude with `idem_supp_iff _ _ v _ (fun _ => rfl) h1 h2 g`.
-/
theorem suppF_iff {D : D7} (V : HSp D) {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F}
    (h : IsPlaceIdem D v ε) (g : GA D V) :
    Formalism.IndefR.Mult.SuppF V (algebraMap (AF D.host.F) (AE D) ε) g ↔ g ∈ (emb D.sp.cm.sig V.gram v).range := by
  obtain ⟨α, rfl, h1, h2⟩ := h
  exact idem_supp_iff _ _ v _ (fun _ => rfl) h1 h2 g

/- English proof (translation)
Rewrite using `[← suppF_iff V h, ← he]`. Both sides reduce to the same expression.
-/
theorem suppAt_iff {D : D7} (V : HSp D) {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F}
    (h : IsPlaceIdem D v ε) {e : AE D} (he : e + cA D e = algebraMap (AF D.host.F) (AE D) ε) (g : GA D V) :
    SuppAt e V g ↔ g ∈ (emb D.sp.cm.sig V.gram v).range := by
  rw [← suppF_iff V h, ← he]; rfl

/- English proof (translation)
Rewrite using `[KsphC_eq]`. Conclude with `⟨fun h => by simpa using (mem_levelOff.1 h).2.2 v (by simp), emb_mem_levelOff (by simp)⟩`.
-/
theorem emb_mem_KsphC_iff {D : D7} (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F))
    (x : GLoc D.sp.cm.sig V.gram v) :
    emb D.sp.cm.sig V.gram v x ∈ KsphC V ∅ ↔ x ∈ stabLoc D.sp.cm.sig V.gram (frameLat V) v := by
  rw [KsphC_eq]
  exact ⟨fun h => by simpa using (mem_levelOff.1 h).2.2 v (by simp), emb_mem_levelOff (by simp)⟩

end Supp

section More

/- English proof (translation)
Rewrite using `[absFin_tmul_one]`. Conclude with `NNReal.eq (FinitePlace.norm_def (v := v) a)`.
-/
theorem absFin_normalised (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v) :
    absFin F v (a ⊗ₜ[F] (1 : E)) =
      WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero v) (Valued.v a) := by
  rw [absFin_tmul_one]
  exact NNReal.eq (FinitePlace.norm_def (v := v) a)

/- English proof (translation)
Establish `: g = 1` using `matHom_injective _ σ J (Units.ext (Subsingleton.elim _ _))`. Rewrite using `[this, height_one]`.
-/
theorem height_rank_zero (J : Matrix (Fin 0) (Fin 0) E) (g : GAd σ J) : height σ J g = 1 := by
  have : g = 1 := matHom_injective _ σ J (Units.ext (Subsingleton.elim _ _))
  rw [this, height_one]

/- English proof (translation)
Introduce `h`. Establish `h1 : (fun _ => (algebraMap F (Fv F v) c)⁻¹ ⊗ₜ[F] (1 : E)) ∈ dualLoc σ (Matrix.of fun _ _ : Fin 1 => algebraMap F E c) (stdLattice E 1) v` using `fun x hx => by`. Establish `e : (1 : Fv F v) ⊗ₜ[F] (algebraMap F E c) * ((algebraMap F (Fv F v) c)⁻¹ ⊗ₜ[F] (1 : E)) = 1`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, Algebra.algebraMap_eq_smul_one (A := E), ← TensorProduct.smul_tmul, Algebra.smul_def, mul_inv_cancel₀ (by simpa using hc0)]`. Both sides reduce to the same expression.

Establish `e2 : hLin σ (Matrix.of fun _ _ : Fin 1 => algebraMap F E c) (Fv F v) (fun _ => (algebraMap F (Fv F v) c)⁻¹ ⊗ₜ[F] (1 : E)) x = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ (x 0)`. Simplify using `only [hLin, hR, hform, JR, Fin.sum_univ_one, Matrix.map_apply, Matrix.of_apply]`. Rewrite using `[mul_assoc]`. Conclude with `(congrArg _ e).trans (mul_one _)`. Rewrite using `[e2]`.

Conclude with `sigR_mem_intLoc σ (mem_latLoc_stdLattice.1 hx 0)`. Rewrite `h1` using `[← h, mem_latLoc_stdLattice]`. Establish `h2` using `absFin_le_one_of_mem_intLoc (h1 0)`. Rewrite `h2` using `[absFin_tmul_one]`. Establish `h3 : ‖(algebraMap F (Fv F v) c)⁻¹‖ ≤ 1` using `h2`.

Establish `h0 : 0 < ‖algebraMap F (Fv F v) c‖` using `by simpa using hc0`. Rewrite `h3` using `[norm_inv, inv_le_one₀ h0]`. Conclude with `absurd hc (not_lt.2 h3)`.
-/
theorem not_isSelfDualAt_scaled (v : HeightOneSpectrum (𝓞 F)) (c : F) (hc0 : c ≠ 0)
    (hc : ‖algebraMap F (Fv F v) c‖ < 1) :
    ¬ IsSelfDualAt σ (Matrix.of fun _ _ : Fin 1 => algebraMap F E c) (stdLattice E 1) v := by
  intro h
  have h1 : (fun _ => (algebraMap F (Fv F v) c)⁻¹ ⊗ₜ[F] (1 : E)) ∈
      dualLoc σ (Matrix.of fun _ _ : Fin 1 => algebraMap F E c) (stdLattice E 1) v := fun x hx => by
    have e : (1 : Fv F v) ⊗ₜ[F] (algebraMap F E c) * ((algebraMap F (Fv F v) c)⁻¹ ⊗ₜ[F] (1 : E)) = 1 := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, Algebra.algebraMap_eq_smul_one (A := E),
        ← TensorProduct.smul_tmul, Algebra.smul_def, mul_inv_cancel₀ (by simpa using hc0)]
      rfl
    have e2 : hLin σ (Matrix.of fun _ _ : Fin 1 => algebraMap F E c) (Fv F v)
        (fun _ => (algebraMap F (Fv F v) c)⁻¹ ⊗ₜ[F] (1 : E)) x = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ (x 0) := by
      simp only [hLin, hR, hform, JR, Fin.sum_univ_one, Matrix.map_apply, Matrix.of_apply]
      rw [mul_assoc]
      exact (congrArg _ e).trans (mul_one _)
    rw [e2]
    exact sigR_mem_intLoc σ (mem_latLoc_stdLattice.1 hx 0)
  rw [← h, mem_latLoc_stdLattice] at h1
  have h2 := absFin_le_one_of_mem_intLoc (h1 0)
  rw [absFin_tmul_one] at h2
  have h3 : ‖(algebraMap F (Fv F v) c)⁻¹‖ ≤ 1 := h2
  have h0 : 0 < ‖algebraMap F (Fv F v) c‖ := by simpa using hc0
  rw [norm_inv, inv_le_one₀ h0] at h3
  exact absurd hc (not_lt.2 h3)

/- English proof (translation)
Establish `h1` using `(Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) y).le_opNNNorm (EuclideanSpace.single j 1)`. Establish `h2` using `PiLp.nnnorm_apply_le (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) y (EuclideanSpace.single j 1)) i`. Establish `h3 : Matrix.toEuclideanCLM (n` using `Fin n) (𝕜 := ℂ) y (EuclideanSpace.single j 1) i = y i j := by`. Express the relevant statement in the definitionally equal form `∑ k, y i k * (EuclideanSpace.single j (1 : ℂ)) k = _`. Simplify using `[Pi.single_apply]`.

Rewrite `h2` using `[h3]`. Use `h2.trans (h1.trans ?_)` and prove the remaining obligations. Simplify using `[opNorm]`.
-/
theorem entry_le_opNorm {n : ℕ} (y : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) : ‖y i j‖₊ ≤ opNorm y := by
  have h1 := (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) y).le_opNNNorm (EuclideanSpace.single j 1)
  have h2 := PiLp.nnnorm_apply_le (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) y (EuclideanSpace.single j 1)) i
  have h3 : Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) y (EuclideanSpace.single j 1) i = y i j := by
    change ∑ k, y i k * (EuclideanSpace.single j (1 : ℂ)) k = _
    simp [Pi.single_apply]
  rw [h3] at h2
  refine h2.trans (h1.trans ?_)
  simp [opNorm]

def torArch {w : InfinitePlace F} (a : w.Completionˣ) : GArch σ (hyp E) w :=
  have h1 : ((a : w.Completion) ⊗ₜ[F] (1 : E)) * (((a⁻¹ : w.Completionˣ) : w.Completion) ⊗ₜ[F] (1 : E)) = 1 := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, Units.mul_inv, mul_one]; rfl
  have h2 : (((a⁻¹ : w.Completionˣ) : w.Completion) ⊗ₜ[F] (1 : E)) * ((a : w.Completion) ⊗ₜ[F] (1 : E)) = 1 := by
    rw [mul_comm, h1]
  ⟨⟨!![(a : w.Completion) ⊗ₜ[F] (1 : E), 0; 0, ((a⁻¹ : w.Completionˣ) : w.Completion) ⊗ₜ[F] (1 : E)],
    !![((a⁻¹ : w.Completionˣ) : w.Completion) ⊗ₜ[F] (1 : E), 0; 0, (a : w.Completion) ⊗ₜ[F] (1 : E)], by
      rw [Matrix.mul_fin_two, Matrix.one_fin_two, h1, h2]; simp, by
      rw [Matrix.mul_fin_two, Matrix.one_fin_two, h1, h2]; simp⟩, by
    change cT _ _ * JR _ (hyp E) * _ = JR _ (hyp E)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [-Units.val_inv_eq_inv_val, cT, JR, hyp, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Matrix.mul_apply, Fin.sum_univ_two, h1, h2,
        Algebra.TensorProduct.one_def]⟩

/- English proof (translation)
Rewrite using `[height_embArch]`. Take `⟨τ⟩ : Nonempty (EmbOver E w)` from `inferInstance`. Use `le_trans ?_ (le_htOf _ _)` and prove the remaining obligations. Use `le_trans ?_ ((normInf_le_iff F w).1 le_rfl τ)` and prove the remaining obligations. Use `le_trans (le_of_eq ?_) (entry_le_opNorm _ 0 0)` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `_ = ‖infEmb τ ((a : w.Completion) ⊗ₜ[F] (1 : E))‖₊`. Rewrite using `[infEmb_tmul, map_one, mul_one]`. Conclude with `NNReal.eq ((InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) _).symm`.
-/
theorem le_height_torArch {w : InfinitePlace F} (a : w.Completionˣ) :
    ‖(a : w.Completion)‖₊ ≤ height σ (hyp E) (embArch σ (hyp E) w (torArch σ a)) := by
  rw [height_embArch]
  obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
  refine le_trans ?_ (le_htOf _ _)
  refine le_trans ?_ ((normInf_le_iff F w).1 le_rfl τ)
  refine le_trans (le_of_eq ?_) (entry_le_opNorm _ 0 0)
  change _ = ‖infEmb τ ((a : w.Completion) ⊗ₜ[F] (1 : E))‖₊
  rw [infEmb_tmul, map_one, mul_one]
  exact NNReal.eq ((InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) _).symm

end More

end GlobalTheory.AdelicU.Model
