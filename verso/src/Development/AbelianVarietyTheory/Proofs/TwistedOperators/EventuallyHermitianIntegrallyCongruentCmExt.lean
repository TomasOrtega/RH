import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHasCls
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCyclicOfFiniteQuotient
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsOrthogonalBasisDotProductApplyEq
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section

namespace GlobalTheory.HermCongAlmostAll

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Proceed by induction on `y with`. Consider the case `zero => simp`. Consider the case `tmul a b => simp [sigR, hσ]`. Consider the case `add a b ha hb => rw [map_add, map_add, ha, hb]`.
-/
theorem sigR_sigR_of {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) (v : HeightOneSpectrum (𝓞 F))
    (y : Fv F v ⊗[F] E) : sigR (Fv F v) σ (sigR (Fv F v) σ y) = y := by
  induction y with
  | zero => simp
  | tmul a b => simp [sigR, hσ]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

/- English proof (translation)
Set `O` to `intLoc F E v`. Set `_` to `(intLocMap E v).toAlgebra`. Establish `: Module.Finite (v.adicCompletionIntegers F) O` using `finite_intLocMap v`. Use `GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers v` as an intermediate fact. Establish `: Finite (v.adicCompletionIntegers F ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F))` using `Formalism.UG.P.glint_finite_residueField v`.

Use `GlobalTheory.InertNorm.isAdicComplete_map_of_finite (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) O` as an intermediate fact. Use `GlobalTheory.InertNorm.finite_quotient_map_of_finite (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) O` as an intermediate fact. Set `s : O →+* O` to `(sigR (Fv F v) σ).restrict O O fun _ => sigR_mem_intLoc σ`. Establish `hs : ∀ y : O, s (s y) = y` using `fun y => Subtype.ext (sigR_sigR_of hσ v y.1)`. Establish `hk : ∀ c, s (algebraMap (v.adicCompletionIntegers F) O c) = algebraMap (v.adicCompletionIntegers F) O c` using `fun c => Subtype.ext (by`.

Express the relevant statement in the definitionally equal form `sigR (Fv F v) σ ((c : Fv F v) ⊗ₜ[F] (1 : E)) = (c : Fv F v) ⊗ₜ[F] (1 : E)`. Simplify using `[sigR])`. Set `I` to `(IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)).map (algebraMap (v.adicCompletionIntegers F) O)`. Establish `hI : I ≤ I.comap s` using `Ideal.map_le_iff_le_comap.2 fun c hc => by`. Rewrite using `[Ideal.mem_comap, Ideal.mem_comap, hk]`.

Conclude with `Ideal.mem_map_of_mem _ hc`. Establish `hω : IsUnit ((⟨_, hai⟩ : O) - s ⟨_, hai⟩)`. Use `IsUnit.of_mul_eq_one (⟨_, hinv⟩ : O) (Subtype.ext ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(inclR (Fv F v) a - inclR (Fv F v) (σ a)) * inclR (Fv F v) (2 * a)⁻¹ = 1`. Rewrite using `[← map_sub, ← map_mul, ha, sub_neg_eq_add, ← two_mul, mul_inv_cancel₀ (mul_ne_zero two_ne_zero ha0), map_one]`.

Take `⟨c, hc⟩` from `GlobalTheory.HenselianNorm.exists_norm_eq O I s hs (fun y hy => hI hy) ⟨_, hω⟩ x (Subtype.ext hx) hu`. Conclude with `⟨c, congrArg Subtype.val hc⟩`.
-/
theorem exists_norm_eq_at {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) (v : HeightOneSpectrum (𝓞 F)) (a : E)
    (ha : σ a = -a) (ha0 : a ≠ 0) (hai : 1 ⊗ₜ[F] a ∈ intLoc F E v) (hinv : 1 ⊗ₜ[F] (2 * a)⁻¹ ∈ intLoc F E v)
    (x : intLoc F E v) (hx : sigR (Fv F v) σ x = x) (hu : IsUnit x) :
    ∃ c : intLoc F E v, c.1 * sigR (Fv F v) σ c.1 = x.1 := by
  let O := intLoc F E v
  let _ := (intLocMap E v).toAlgebra
  have : Module.Finite (v.adicCompletionIntegers F) O := finite_intLocMap v
  have := GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers v
  have : Finite (v.adicCompletionIntegers F ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) :=
    Formalism.UG.P.glint_finite_residueField v
  have := GlobalTheory.InertNorm.isAdicComplete_map_of_finite (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) O
  have := GlobalTheory.InertNorm.finite_quotient_map_of_finite (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) O
  let s : O →+* O := (sigR (Fv F v) σ).restrict O O fun _ => sigR_mem_intLoc σ
  have hs : ∀ y : O, s (s y) = y := fun y => Subtype.ext (sigR_sigR_of hσ v y.1)
  have hk : ∀ c, s (algebraMap (v.adicCompletionIntegers F) O c) = algebraMap (v.adicCompletionIntegers F) O c :=
    fun c => Subtype.ext (by
      change sigR (Fv F v) σ ((c : Fv F v) ⊗ₜ[F] (1 : E)) = (c : Fv F v) ⊗ₜ[F] (1 : E)
      simp [sigR])
  let I := (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)).map (algebraMap (v.adicCompletionIntegers F) O)
  have hI : I ≤ I.comap s := Ideal.map_le_iff_le_comap.2 fun c hc => by
    rw [Ideal.mem_comap, Ideal.mem_comap, hk]
    exact Ideal.mem_map_of_mem _ hc
  have hω : IsUnit ((⟨_, hai⟩ : O) - s ⟨_, hai⟩) := by
    refine IsUnit.of_mul_eq_one (⟨_, hinv⟩ : O) (Subtype.ext ?_)
    change (inclR (Fv F v) a - inclR (Fv F v) (σ a)) * inclR (Fv F v) (2 * a)⁻¹ = 1
    rw [← map_sub, ← map_mul, ha, sub_neg_eq_add, ← two_mul, mul_inv_cancel₀ (mul_ne_zero two_ne_zero ha0), map_one]
  obtain ⟨c, hc⟩ := GlobalTheory.HenselianNorm.exists_norm_eq O I s hs (fun y hy => hI hy) ⟨_, hω⟩ x (Subtype.ext hx) hu
  exact ⟨c, congrArg Subtype.val hc⟩

end GlobalTheory.HermCongAlmostAll

namespace GlobalTheory.HermCongAlmostAll

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

def IntM (v : HeightOneSpectrum (𝓞 F)) (X : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) : Prop :=
  ∀ i j, X i j ∈ intLoc F E v

/- English proof (translation)
Introduce `i j` and use `by rw [Matrix.mul_apply] exact sum_mem fun k _ => mul_mem (hX i k) (hY k j)`.
-/
theorem intM_mul {v : HeightOneSpectrum (𝓞 F)} {X Y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)}
    (hX : IntM v X) (hY : IntM v Y) : IntM v (X * Y) := fun i j => by
  rw [Matrix.mul_apply]
  exact sum_mem fun k _ => mul_mem (hX i k) (hY k j)

/- English proof (translation)
Introduce `i j` and use `by rw [Matrix.diagonal_apply] split_ifs exacts [hc i, zero_mem _]`.
-/
theorem intM_diagonal {v : HeightOneSpectrum (𝓞 F)} {c : Fin n → Fv F v ⊗[F] E}
    (hc : ∀ i, c i ∈ intLoc F E v) : IntM v (Matrix.diagonal c) := fun i j => by
  rw [Matrix.diagonal_apply]
  split_ifs
  exacts [hc i, zero_mem _]

/- English proof (translation)
Introduce `i` and use `by rw [Matrix.mulVec, dotProduct] exact sum_mem fun k _ => mul_mem (hX i k) (hy k)`.
-/
theorem mulVec_mem {v : HeightOneSpectrum (𝓞 F)} {X : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)} (hX : IntM v X)
    {y : Fin n → Fv F v ⊗[F] E} (hy : ∀ i, y i ∈ intLoc F E v) : ∀ i, (X *ᵥ y) i ∈ intLoc F E v := fun i => by
  rw [Matrix.mulVec, dotProduct]
  exact sum_mem fun k _ => mul_mem (hX i k) (hy k)

/- English proof (translation)
The claim follows from `eventually_all.2 fun i => eventually_all.2 fun j => eventually_one_tmul_mem_intLoc (F := F) (X i j)`.
-/
theorem eventually_intM_JR (X : Matrix (Fin n) (Fin n) E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, IntM v (JR (Fv F v) X) :=
  eventually_all.2 fun i => eventually_all.2 fun j => eventually_one_tmul_mem_intLoc (F := F) (X i j)

/- English proof (translation)
The claim follows from `Matrix.map_mul`.
-/
theorem JR_mul (R : Type) [CommRing R] [Algebra F R] (X Y : Matrix (Fin n) (Fin n) E) :
    JR (F := F) R (X * Y) = JR R X * JR R Y := Matrix.map_mul

/- English proof (translation)
The claim follows from `Matrix.map_one _ (map_zero _) (map_one _)`.
-/
theorem JR_one (R : Type) [CommRing R] [Algebra F R] : JR (F := F) R (1 : Matrix (Fin n) (Fin n) E) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

/- English proof (translation)
The claim follows from `Matrix.diagonal_map (map_zero _)`.
-/
theorem JR_diagonal (R : Type) [CommRing R] [Algebra F R] (d : Fin n → E) :
    JR (F := F) R (Matrix.diagonal d) = Matrix.diagonal fun i => inclR R (d i) :=
  Matrix.diagonal_map (map_zero _)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cT_JR (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R] (X : Matrix (Fin n) (Fin n) E) :
    Formalism.UG.cT (sigR R σ) (JR R X) = JR R (Formalism.UG.cT (σ : E →+* E) X) := rfl

/- English proof (translation)
Unfold `Formalism.UG.cT`. Rewrite using `[Matrix.diagonal_map (map_zero s), Matrix.diagonal_transpose]`.
-/
theorem cT_diagonal {A : Type} [CommRing A] (s : A →+* A) (c : Fin n → A) :
    Formalism.UG.cT s (Matrix.diagonal c) = Matrix.diagonal fun i => s (c i) := by
  unfold Formalism.UG.cT
  rw [Matrix.diagonal_map (map_zero s), Matrix.diagonal_transpose]

end GlobalTheory.HermCongAlmostAll

namespace GlobalTheory.HermCongAlmostAll

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ h n J J' hJ hJ'`. Establish `hσ : ∀ x, σ (σ x) = x` using `fun x => by`. Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Conclude with `τ.injective (by rw [h.2.2.2, h.2.2.2, star_star])`. Establish `diag : ∀ {G : Matrix (Fin n) (Fin n) E}, IsHermND σ G → ∃ (Q Q' : Matrix (Fin n) (Fin n) E) (d : Fin n → E), Q * Q' = 1 ∧ Q' * Q = 1 ∧ Formalism.UG.cT (σ : E →+* E) Q * G * Q = Matrix.diagonal d ∧ (∀ i, σ (d i) = d i) ∧ ∀ i, d i ≠ 0`.

Introduce `G hG`. Take `⟨P, d, hP, hd, hdσ, hd0⟩` from `GlobalTheory.HermDiag.exists_congr_diagonal (c := (σ : E →+* E)) two_ne_zero hσ (G := G) (fun a b => hG.1 b a)`. Establish `hu : IsUnit (P.map (σ : E →+* E)).det`. Rewrite using `[show (P.map (σ : E →+* E)).det = (σ : E →+* E) P.det from (RingHom.map_det _ P).symm]`. Conclude with `((map_ne_zero (σ : E →+* E)).2 hP).isUnit`.

Establish `hc : Formalism.UG.cT (σ : E →+* E) (P.map (σ : E →+* E)) = Pᵀ`. Use extensionality with `i j`. Simplify using `[Formalism.UG.cT, hσ]`. Use `⟨P.map (σ : E →+* E), (P.map (σ : E →+* E))⁻¹, d, Matrix.mul_nonsing_inv _ hu, Matrix.nonsing_inv_mul _ hu, ?_, hdσ, hd0 hG.2⟩` and prove the remaining obligations. Rewrite using `[hc]`.

Conclude with `hd`. Take `⟨Q, Qi, d, hQ1, hQ2, hQd, hdσ, hd0⟩` from `diag hJ`. Take `⟨R, Ri, e, hR1, hR2, hRe, heσ, he0⟩` from `diag hJ'`. Take `⟨a, ha0, ha⟩` from `exists_integer_conj_eq_neg h`. Establish `ha0' : (a : E) ≠ 0` using `RingOfIntegers.coe_ne_zero_iff.2 ha0`.

Use `filter_upwards [eventually_intM_JR (F := F) Q, eventually_intM_JR (F := F) Qi, eventually_intM_JR (F := F) R, eventually_intM_JR (F := F) Ri, eventually_all.2 fun i => eventually_one_tmul_mem_intLoc (F := F) (e i / d i), eventually_all.2 fun i => eventually_one_tmul_mem_intLoc (F …`. Establish `hed : ∀ i, e i / d i * (d i / e i) = 1` using `fun i => by`. Rewrite using `[div_mul_div_comm, mul_comm (e i), div_self (mul_ne_zero (hd0 i) (he0 i))]`. Establish `hc : ∀ i, ∃ c : intLoc F E v, c.1 * sigR (Fv F v) σ c.1 = inclR (Fv F v) (e i / d i)` using `fun i => exists_norm_eq_at hσ v a ha ha0' (tmul_mem_intLoc (one_mem _) a) h7 ⟨_, h5 i⟩ (by`. Express the relevant statement in the definitionally equal form `inclR (Fv F v) (σ (e i / d i)) = inclR (Fv F v) (e i / d i)`.

Rewrite using `[map_div₀, hdσ, heσ])`. Use the proof step `(IsUnit.of_mul_eq_one (⟨_, h6 i⟩ : intLoc F E v) (Subtype.ext (by`. Express the relevant statement in the definitionally equal form `inclR (Fv F v) (e i / d i) * inclR (Fv F v) (d i / e i) = 1`. Rewrite using `[← map_mul, hed, map_one])))`. Use `choose c hc using hc`.

Use `set s := sigR (Fv F v) σ with hs`. Set `C : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)` to `Matrix.diagonal fun i => (c i).1`. Set `C' : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)` to `Matrix.diagonal fun i => s (c i).1 * inclR (Fv F v) (d i / e i)`. Establish `hCC : C * C' = 1`. Rewrite using `[Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`.

Use `congr 1`. Use function extensionality and compare the values at `i`. Rewrite using `[← mul_assoc, hc i, ← map_mul, hed, map_one]`. Establish `hC'C : C' * C = 1`. Rewrite using `[Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`.

Use `congr 1`. Use function extensionality and compare the values at `i`. Rewrite using `[mul_comm, ← mul_assoc, hc i, ← map_mul, hed, map_one]`. Set `u` to `JR (Fv F v) Q * C * JR (Fv F v) Ri`. Set `u'` to `JR (Fv F v) R * C' * JR (Fv F v) Qi`.

Establish `huu : u * u' = 1`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [u, u', JR_mul, Matrix.mul_assoc]`. Use `_ = 1 := by`. Rewrite using `[hR2, JR_one, Matrix.mul_one, Matrix.mul_assoc (JR (Fv F v) Q), hCC, Matrix.mul_one, ← JR_mul, hQ1, JR_one]`.

Establish `huu' : u' * u = 1`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [u, u', JR_mul, Matrix.mul_assoc]`. Use `_ = 1 := by`. Rewrite using `[hQ2, JR_one, Matrix.mul_one, Matrix.mul_assoc (JR (Fv F v) R), hC'C, Matrix.mul_one, ← JR_mul, hR1, JR_one]`.

Establish `hCint : IntM v C` using `intM_diagonal fun i => (c i).2`. Establish `hC'int : IntM v C'` using `intM_diagonal fun i => mul_mem (sigR_mem_intLoc σ (c i).2) (h6 i)`. Establish `hui : IntM v u` using `intM_mul (intM_mul h1 hCint) h4`. Establish `hu'i : IntM v u'` using `intM_mul (intM_mul h3 hC'int) h2`. Establish `eC : Formalism.UG.cT s C * Matrix.diagonal (fun i => inclR (Fv F v) (d i)) * C = Matrix.diagonal fun i => inclR (Fv F v) (e i)`.

Rewrite using `[cT_diagonal, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Rewrite using `[show s (c i).1 * inclR (Fv F v) (d i) * (c i).1 = (c i).1 * s (c i).1 * inclR (Fv F v) (d i) by ring, hc i, ← map_mul, div_mul_cancel₀ _ (hd0 i)]`. Use `⟨⟨u, u', huu, huu'⟩, ?_, fun y => ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `Formalism.UG.cT s u * JR (Fv F v) J * u = JR (Fv F v) J'`. Establish `k1 : Formalism.UG.cT s u * JR (Fv F v) J * u = JR (Fv F v) (Formalism.UG.cT (σ : E →+* E) Ri) * (Formalism.UG.cT s C * JR (Fv F v) (Formalism.UG.cT (σ : E →+* E) Q * J * Q) * C) * JR (Fv F v) Ri`. Simplify using `only [u, Formalism.UG.cT_mul, hs, cT_JR, JR_mul, Matrix.mul_assoc]`. Rewrite using `[k1, hQd, JR_diagonal, eC, ← JR_diagonal, ← hRe, ← JR_mul, ← JR_mul]`. Use `congr 1`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = J' := by rw [← Formalism.UG.cT_mul, hR1, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]`. Express the relevant statement in the definitionally equal form `u *ᵥ y ∈ latLoc F (stdLattice E n) v ↔ y ∈ latLoc F (stdLattice E n) v`. Rewrite using `[mem_latLoc_stdLattice, mem_latLoc_stdLattice]`.

Use `⟨fun hy => ?_, fun hy => mulVec_mem hui hy⟩` and prove the remaining obligations. Use `mulVec_mem hu'i hy` as an intermediate fact. Rewrite `this` using `[Matrix.mulVec_mulVec, huu', Matrix.one_mulVec]`. Then use the resulting hypothesis.
-/
theorem eventually_congr_int : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J J' : Matrix (Fin n) (Fin n) E), IsHermND σ J → IsHermND σ J' →
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∃ u : GL (Fin n) (Fv F v ⊗[F] E),
      Formalism.UG.cT (sigR (Fv F v) σ) u.1 * JR (Fv F v) J * u.1 = JR (Fv F v) J' ∧
      ∀ y, u.1 *ᵥ y ∈ latLoc F (stdLattice E n) v ↔ y ∈ latLoc F (stdLattice E n) v := by
  intro F E _ _ _ _ _ σ h n J J' hJ hJ'
  have hσ : ∀ x, σ (σ x) = x := fun x => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective (by rw [h.2.2.2, h.2.2.2, star_star])
  have diag : ∀ {G : Matrix (Fin n) (Fin n) E}, IsHermND σ G → ∃ (Q Q' : Matrix (Fin n) (Fin n) E) (d : Fin n → E),
      Q * Q' = 1 ∧ Q' * Q = 1 ∧ Formalism.UG.cT (σ : E →+* E) Q * G * Q = Matrix.diagonal d ∧
      (∀ i, σ (d i) = d i) ∧ ∀ i, d i ≠ 0 := by
    intro G hG
    obtain ⟨P, d, hP, hd, hdσ, hd0⟩ :=
      GlobalTheory.HermDiag.exists_congr_diagonal (c := (σ : E →+* E)) two_ne_zero hσ (G := G) (fun a b => hG.1 b a)
    have hu : IsUnit (P.map (σ : E →+* E)).det := by
      rw [show (P.map (σ : E →+* E)).det = (σ : E →+* E) P.det from (RingHom.map_det _ P).symm]
      exact ((map_ne_zero (σ : E →+* E)).2 hP).isUnit
    have hc : Formalism.UG.cT (σ : E →+* E) (P.map (σ : E →+* E)) = Pᵀ := by
      ext i j
      simp [Formalism.UG.cT, hσ]
    refine ⟨P.map (σ : E →+* E), (P.map (σ : E →+* E))⁻¹, d, Matrix.mul_nonsing_inv _ hu,
      Matrix.nonsing_inv_mul _ hu, ?_, hdσ, hd0 hG.2⟩
    rw [hc]
    exact hd
  obtain ⟨Q, Qi, d, hQ1, hQ2, hQd, hdσ, hd0⟩ := diag hJ
  obtain ⟨R, Ri, e, hR1, hR2, hRe, heσ, he0⟩ := diag hJ'
  obtain ⟨a, ha0, ha⟩ := exists_integer_conj_eq_neg h
  have ha0' : (a : E) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.2 ha0
  filter_upwards [eventually_intM_JR (F := F) Q, eventually_intM_JR (F := F) Qi, eventually_intM_JR (F := F) R,
    eventually_intM_JR (F := F) Ri,
    eventually_all.2 fun i => eventually_one_tmul_mem_intLoc (F := F) (e i / d i),
    eventually_all.2 fun i => eventually_one_tmul_mem_intLoc (F := F) (d i / e i),
    eventually_one_tmul_mem_intLoc (F := F) (2 * (a : E))⁻¹] with v h1 h2 h3 h4 h5 h6 h7
  have hed : ∀ i, e i / d i * (d i / e i) = 1 := fun i => by
    rw [div_mul_div_comm, mul_comm (e i), div_self (mul_ne_zero (hd0 i) (he0 i))]
  have hc : ∀ i, ∃ c : intLoc F E v, c.1 * sigR (Fv F v) σ c.1 = inclR (Fv F v) (e i / d i) := fun i =>
    exists_norm_eq_at hσ v a ha ha0' (tmul_mem_intLoc (one_mem _) a) h7 ⟨_, h5 i⟩
      (by
        change inclR (Fv F v) (σ (e i / d i)) = inclR (Fv F v) (e i / d i)
        rw [map_div₀, hdσ, heσ])
      (IsUnit.of_mul_eq_one (⟨_, h6 i⟩ : intLoc F E v) (Subtype.ext (by
        change inclR (Fv F v) (e i / d i) * inclR (Fv F v) (d i / e i) = 1
        rw [← map_mul, hed, map_one])))
  choose c hc using hc
  set s := sigR (Fv F v) σ with hs
  let C : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) := Matrix.diagonal fun i => (c i).1
  let C' : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) :=
    Matrix.diagonal fun i => s (c i).1 * inclR (Fv F v) (d i / e i)
  have hCC : C * C' = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [← mul_assoc, hc i, ← map_mul, hed, map_one]
  have hC'C : C' * C = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [mul_comm, ← mul_assoc, hc i, ← map_mul, hed, map_one]
  let u := JR (Fv F v) Q * C * JR (Fv F v) Ri
  let u' := JR (Fv F v) R * C' * JR (Fv F v) Qi
  have huu : u * u' = 1 := by
    calc u * u' = JR (Fv F v) Q * C * (JR (Fv F v) (Ri * R)) * C' * JR (Fv F v) Qi := by
          simp only [u, u', JR_mul, Matrix.mul_assoc]
      _ = 1 := by
          rw [hR2, JR_one, Matrix.mul_one, Matrix.mul_assoc (JR (Fv F v) Q), hCC, Matrix.mul_one, ← JR_mul, hQ1,
            JR_one]
  have huu' : u' * u = 1 := by
    calc u' * u = JR (Fv F v) R * C' * (JR (Fv F v) (Qi * Q)) * C * JR (Fv F v) Ri := by
          simp only [u, u', JR_mul, Matrix.mul_assoc]
      _ = 1 := by
          rw [hQ2, JR_one, Matrix.mul_one, Matrix.mul_assoc (JR (Fv F v) R), hC'C, Matrix.mul_one, ← JR_mul, hR1,
            JR_one]
  have hCint : IntM v C := intM_diagonal fun i => (c i).2
  have hC'int : IntM v C' := intM_diagonal fun i => mul_mem (sigR_mem_intLoc σ (c i).2) (h6 i)
  have hui : IntM v u := intM_mul (intM_mul h1 hCint) h4
  have hu'i : IntM v u' := intM_mul (intM_mul h3 hC'int) h2
  have eC : Formalism.UG.cT s C * Matrix.diagonal (fun i => inclR (Fv F v) (d i)) * C =
      Matrix.diagonal fun i => inclR (Fv F v) (e i) := by
    rw [cT_diagonal, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rw [show s (c i).1 * inclR (Fv F v) (d i) * (c i).1 = (c i).1 * s (c i).1 * inclR (Fv F v) (d i) by ring, hc i,
      ← map_mul, div_mul_cancel₀ _ (hd0 i)]
  refine ⟨⟨u, u', huu, huu'⟩, ?_, fun y => ?_⟩
  · change Formalism.UG.cT s u * JR (Fv F v) J * u = JR (Fv F v) J'
    have k1 : Formalism.UG.cT s u * JR (Fv F v) J * u = JR (Fv F v) (Formalism.UG.cT (σ : E →+* E) Ri) *
        (Formalism.UG.cT s C * JR (Fv F v) (Formalism.UG.cT (σ : E →+* E) Q * J * Q) * C) * JR (Fv F v) Ri := by
      simp only [u, Formalism.UG.cT_mul, hs, cT_JR, JR_mul, Matrix.mul_assoc]
    rw [k1, hQd, JR_diagonal, eC, ← JR_diagonal, ← hRe, ← JR_mul, ← JR_mul]
    congr 1
    calc Formalism.UG.cT (σ : E →+* E) Ri * (Formalism.UG.cT (σ : E →+* E) R * J' * R) * Ri =
        (Formalism.UG.cT (σ : E →+* E) Ri * Formalism.UG.cT (σ : E →+* E) R) * J' * (R * Ri) := by
          simp only [Matrix.mul_assoc]
      _ = J' := by rw [← Formalism.UG.cT_mul, hR1, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]
  · change u *ᵥ y ∈ latLoc F (stdLattice E n) v ↔ y ∈ latLoc F (stdLattice E n) v
    rw [mem_latLoc_stdLattice, mem_latLoc_stdLattice]
    refine ⟨fun hy => ?_, fun hy => mulVec_mem hui hy⟩
    have := mulVec_mem hu'i hy
    rwa [Matrix.mulVec_mulVec, huu', Matrix.one_mulVec] at this

end GlobalTheory.HermCongAlmostAll
