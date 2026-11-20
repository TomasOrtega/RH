import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.IntegralAlmostAllPlacesStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorIntegerRingAlmostAllPlacesStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianUnitFormDiagonalizesStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianUnitFormRepresentsUnitStatement

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.GoodIso

/- English proof (translation)
Take `⟨g, d, hg, hdd, hgJ⟩` from `GlobalTheory.T.hermitian_unit_form_diagonalizes A σ hσ (fun m J hJ hu => GlobalTheory.T.hermitian_unit_form_represents_unit A σ hσ h2 hδ m J hJ hu) m J hJ hd`. Use `choose a ha using fun i => hN (d i) (hdd i).1 (hdd i).2`. Establish `hau : ∀ i, IsUnit (a i)` using `fun i => isUnit_of_mul_isUnit_left (y := σ (a i)) (by rw [ha i]; exact (hdd i).1)`. Use `choose c hc using fun i => (hau i).exists_right_inv`. Establish `hcu : ∀ i, IsUnit (c i)` using `fun i => IsUnit.of_mul_eq_one (a i) (by rw [mul_comm]; exact hc i)`.

Establish `hdet : IsUnit (g * Matrix.diagonal c).det`. Rewrite using `[Matrix.det_mul, Matrix.det_diagonal]`. Conclude with `hg.mul (IsUnit.prod_univ_iff.2 hcu)`. Use `⟨((Matrix.isUnit_iff_isUnit_det _).2 hdet).unit, ?_⟩` and prove the remaining obligations. Rewrite using `[IsUnit.unit_spec, cT_mul]`.

Establish `hD : cT σ (Matrix.diagonal c) = Matrix.diagonal (fun i => σ (c i))`. Use extensionality with `i j`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using `[cT]`.

Simplify using `[cT, Matrix.diagonal_apply, hij, Ne.symm hij]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = 1 := by`. Rewrite using `[hgJ, hD, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`.

Use `congr 1`. Use function extensionality and compare the values at `i`. Establish `h1 : σ (c i) * σ (a i) = 1` using `by rw [← map_mul, mul_comm, hc i, map_one]`. Rewrite using `[← ha i]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_gl_to_one (A : Type) [CommRing A] [Finite (MaximalSpectrum A)] (σ : A →+* A)
    (hσ : ∀ y, σ (σ y) = y) (h2 : IsUnit (2 : A)) (hδ : ∃ δ : A, IsUnit δ ∧ σ δ = -δ)
    (hN : ∀ β : A, IsUnit β → σ β = β → ∃ a : A, a * σ a = β)
    (m : ℕ) (J : Matrix (Fin m) (Fin m) A) (hJ : ∀ i j, σ (J j i) = J i j) (hd : IsUnit J.det) :
    ∃ h : GL (Fin m) A,
      cT σ (h : Matrix (Fin m) (Fin m) A) * J * (h : Matrix (Fin m) (Fin m) A) = 1 := by
  obtain ⟨g, d, hg, hdd, hgJ⟩ := GlobalTheory.T.hermitian_unit_form_diagonalizes A σ hσ
    (fun m J hJ hu => GlobalTheory.T.hermitian_unit_form_represents_unit A σ hσ h2 hδ m J hJ hu) m J hJ hd
  choose a ha using fun i => hN (d i) (hdd i).1 (hdd i).2
  have hau : ∀ i, IsUnit (a i) := fun i =>
    isUnit_of_mul_isUnit_left (y := σ (a i)) (by rw [ha i]; exact (hdd i).1)
  choose c hc using fun i => (hau i).exists_right_inv
  have hcu : ∀ i, IsUnit (c i) := fun i => IsUnit.of_mul_eq_one (a i) (by rw [mul_comm]; exact hc i)
  have hdet : IsUnit (g * Matrix.diagonal c).det := by
    rw [Matrix.det_mul, Matrix.det_diagonal]
    exact hg.mul (IsUnit.prod_univ_iff.2 hcu)
  refine ⟨((Matrix.isUnit_iff_isUnit_det _).2 hdet).unit, ?_⟩
  rw [IsUnit.unit_spec, cT_mul]
  have hD : cT σ (Matrix.diagonal c) = Matrix.diagonal (fun i => σ (c i)) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [cT]
    · simp [cT, Matrix.diagonal_apply, hij, Ne.symm hij]
  calc cT σ (Matrix.diagonal c) * cT σ g * J * (g * Matrix.diagonal c)
      = cT σ (Matrix.diagonal c) * (cT σ g * J * g) * Matrix.diagonal c := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by
        rw [hgJ, hD, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
        congr 1
        funext i
        have h1 : σ (c i) * σ (a i) = 1 := by rw [← map_mul, mul_comm, hc i, map_one]
        rw [← ha i]
        calc σ (c i) * (a i * σ (a i)) * c i = (σ (c i) * σ (a i)) * (a i * c i) := by ring
          _ = 1 := by rw [h1, hc i, one_mul]

/- English proof (translation)
Take `⟨h, hh⟩` from `exists_gl_to_one A σ hσ h2 hδ hN m J hJ hd`. Take `⟨k, hk⟩` from `exists_gl_to_one A σ hσ h2 hδ hN m J' hJ' hd'`. Use `⟨h * k⁻¹, ?_⟩` and prove the remaining obligations. Establish `hkk : (k : Matrix (Fin m) (Fin m) A) * ((k⁻¹ : GL (Fin m) A) : Matrix (Fin m) (Fin m) A) = 1`. Rewrite using `[← Units.val_mul, mul_inv_cancel, Units.val_one]`.

Establish `hck : cT σ ((k⁻¹ : GL (Fin m) A) : Matrix (Fin m) (Fin m) A) * cT σ (k : Matrix (Fin m) (Fin m) A) = 1`. Rewrite using `[← cT_mul, hkk, cT_one]`. Use `set K : Matrix (Fin m) (Fin m) A := (k : Matrix (Fin m) (Fin m) A)`. Use `set L : Matrix (Fin m) (Fin m) A := ((k⁻¹ : GL (Fin m) A) : Matrix (Fin m) (Fin m) A)`. Use `set H : Matrix (Fin m) (Fin m) A := (h : Matrix (Fin m) (Fin m) A)`.

Establish `e1 : J' = cT σ L * (cT σ K * J' * K) * L`. Combine the equalities or inequalities in the displayed calculation. Establish `e2 : cT σ (H * L) * J * (H * L) = cT σ L * (cT σ H * J * H) * L`. Rewrite using `[cT_mul]`. Simplify using `only [Matrix.mul_assoc]`.

Rewrite using `[Units.val_mul]`. Express the relevant statement in the definitionally equal form `J' = cT σ (H * L) * J * (H * L)`. Rewrite using `[e2, hh, ← hk, ← e1]`.
-/
theorem exists_gl_equiv (A : Type) [CommRing A] [Finite (MaximalSpectrum A)] (σ : A →+* A)
    (hσ : ∀ y, σ (σ y) = y) (h2 : IsUnit (2 : A)) (hδ : ∃ δ : A, IsUnit δ ∧ σ δ = -δ)
    (hN : ∀ β : A, IsUnit β → σ β = β → ∃ a : A, a * σ a = β)
    (m : ℕ) (J J' : Matrix (Fin m) (Fin m) A) (hJ : ∀ i j, σ (J j i) = J i j) (hd : IsUnit J.det)
    (hJ' : ∀ i j, σ (J' j i) = J' i j) (hd' : IsUnit J'.det) :
    ∃ G : GL (Fin m) A,
      J' = cT σ (G : Matrix (Fin m) (Fin m) A) * J * (G : Matrix (Fin m) (Fin m) A) := by
  obtain ⟨h, hh⟩ := exists_gl_to_one A σ hσ h2 hδ hN m J hJ hd
  obtain ⟨k, hk⟩ := exists_gl_to_one A σ hσ h2 hδ hN m J' hJ' hd'
  refine ⟨h * k⁻¹, ?_⟩
  have hkk : (k : Matrix (Fin m) (Fin m) A) * ((k⁻¹ : GL (Fin m) A) : Matrix (Fin m) (Fin m) A) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hck : cT σ ((k⁻¹ : GL (Fin m) A) : Matrix (Fin m) (Fin m) A) * cT σ (k : Matrix (Fin m) (Fin m) A) = 1 := by
    rw [← cT_mul, hkk, cT_one]
  set K : Matrix (Fin m) (Fin m) A := (k : Matrix (Fin m) (Fin m) A)
  set L : Matrix (Fin m) (Fin m) A := ((k⁻¹ : GL (Fin m) A) : Matrix (Fin m) (Fin m) A)
  set H : Matrix (Fin m) (Fin m) A := (h : Matrix (Fin m) (Fin m) A)
  have e1 : J' = cT σ L * (cT σ K * J' * K) * L := by
    calc J' = (cT σ L * cT σ K) * J' * (K * L) := by rw [hck, hkk, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  have e2 : cT σ (H * L) * J * (H * L) = cT σ L * (cT σ H * J * H) * L := by
    rw [cT_mul]; simp only [Matrix.mul_assoc]
  rw [Units.val_mul]
  change J' = cT σ (H * L) * J * (H * L)
  rw [e2, hh, ← hk, ← e1]

/- English proof (translation)
Set `σO : O →+* O` to `(s.comp O.subtype).codRestrict O (fun y => hO y y.2)`. Establish `hσO : ∀ y : O, ((σO y : O) : R) = s (y : R)` using `fun y => rfl`. Establish `lift : ∀ (P : Matrix (Fin m) (Fin m) R) (iP : ∀ i j, P i j ∈ O), (∃ w ∈ O, P.det * w = 1) → ∃ Q : Matrix (Fin m) (Fin m) O, Q.map O.subtype = P ∧ IsUnit Q.det`. Introduce `P iP ⟨w, hw, hPw⟩`. Use `⟨Matrix.of fun i j => ⟨P i j, iP i j⟩, by ext i j; rfl, ?_⟩` and prove the remaining obligations.

Establish `hdet : ((Matrix.of fun i j => (⟨P i j, iP i j⟩ : O)).det : O).1 = P.det`. Use `RingHom.map_det O.subtype (Matrix.of fun i j => (⟨P i j, iP i j⟩ : O))` as an intermediate fact. Conclude with `this`. Use `IsUnit.of_mul_eq_one ⟨w, hw⟩ (Subtype.ext ?_)` and prove the remaining obligations. Simplify `hPw` using `[hdet]`.

Take `⟨Q, rfl, uQ⟩` from `lift K iK wK`. Take `⟨Q', rfl, uQ'⟩` from `lift K' iK' wK'`. Establish `herm : ∀ (Q : Matrix (Fin m) (Fin m) O), (∀ i j, s ((Q.map O.subtype) j i) = (Q.map O.subtype) i j) → ∀ i j, σO (Q j i) = Q i j` using `fun Q h i j => Subtype.ext (h i j)`. Take `⟨G, hG⟩` from `exists_gl_equiv O σO (fun y => Subtype.ext (hs _)) h2 (by obtain ⟨δ, h1, h3⟩ := hδ; exact ⟨δ, h1, Subtype.ext h3⟩) (fun β hβ hβ' => by`. Take `⟨a, ha⟩` from `hN β hβ (congrArg Subtype.val hβ')`.

Conclude with `⟨a, Subtype.ext ha⟩)`. Use `m Q Q' (herm Q hK) uQ (herm Q' hK') uQ'`. Establish `hcT : ∀ P : Matrix (Fin m) (Fin m) O, cT s (P.map O.subtype) = (cT σO P).map O.subtype` using `fun P => by ext i j; rfl`. Use `⟨bc O.subtype G, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `hv : ((bc O.subtype G : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) = (G : Matrix (Fin m) (Fin m) O).map O.subtype` using `rfl`.

Rewrite using `[hv, hcT, hG, Matrix.map_mul, Matrix.map_mul]`. Introduce `i j`. Conclude with `(G.val i j).2`. Introduce `i j`. Rewrite using `[← map_inv]`.

Conclude with `((G⁻¹).val i j).2`.
-/
theorem exists_gl_sub {R : Type} [CommRing R] (s : R →+* R) (hs : ∀ y, s (s y) = y) (O : Subring R)
    (hO : ∀ y ∈ O, s y ∈ O) [Finite (MaximalSpectrum O)] (h2 : IsUnit (2 : O))
    (hδ : ∃ δ : O, IsUnit δ ∧ s (δ : R) = -(δ : R))
    (hN : ∀ β : O, IsUnit β → s (β : R) = β → ∃ a : O, (a : R) * s a = β)
    (m : ℕ) (K K' : Matrix (Fin m) (Fin m) R)
    (hK : ∀ i j, s (K j i) = K i j) (hK' : ∀ i j, s (K' j i) = K' i j)
    (iK : ∀ i j, K i j ∈ O) (iK' : ∀ i j, K' i j ∈ O)
    (wK : ∃ w ∈ O, K.det * w = 1) (wK' : ∃ w ∈ O, K'.det * w = 1) :
    ∃ g : GL (Fin m) R, K' = cT s (g : Matrix (Fin m) (Fin m) R) * K * (g : Matrix (Fin m) (Fin m) R) ∧
      (∀ i j, (g : Matrix (Fin m) (Fin m) R) i j ∈ O) ∧
      ∀ i j, ((g⁻¹ : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) i j ∈ O := by
  let σO : O →+* O := (s.comp O.subtype).codRestrict O (fun y => hO y y.2)
  have hσO : ∀ y : O, ((σO y : O) : R) = s (y : R) := fun y => rfl
  have lift : ∀ (P : Matrix (Fin m) (Fin m) R) (iP : ∀ i j, P i j ∈ O), (∃ w ∈ O, P.det * w = 1) →
      ∃ Q : Matrix (Fin m) (Fin m) O, Q.map O.subtype = P ∧ IsUnit Q.det := by
    intro P iP ⟨w, hw, hPw⟩
    refine ⟨Matrix.of fun i j => ⟨P i j, iP i j⟩, by ext i j; rfl, ?_⟩
    have hdet : ((Matrix.of fun i j => (⟨P i j, iP i j⟩ : O)).det : O).1 = P.det := by
      have := RingHom.map_det O.subtype (Matrix.of fun i j => (⟨P i j, iP i j⟩ : O))
      exact this
    refine IsUnit.of_mul_eq_one ⟨w, hw⟩ (Subtype.ext ?_)
    simpa [hdet] using hPw
  obtain ⟨Q, rfl, uQ⟩ := lift K iK wK
  obtain ⟨Q', rfl, uQ'⟩ := lift K' iK' wK'
  have herm : ∀ (Q : Matrix (Fin m) (Fin m) O), (∀ i j, s ((Q.map O.subtype) j i) = (Q.map O.subtype) i j) →
      ∀ i j, σO (Q j i) = Q i j := fun Q h i j => Subtype.ext (h i j)
  obtain ⟨G, hG⟩ := exists_gl_equiv O σO (fun y => Subtype.ext (hs _)) h2
    (by obtain ⟨δ, h1, h3⟩ := hδ; exact ⟨δ, h1, Subtype.ext h3⟩)
    (fun β hβ hβ' => by
      obtain ⟨a, ha⟩ := hN β hβ (congrArg Subtype.val hβ')
      exact ⟨a, Subtype.ext ha⟩)
    m Q Q' (herm Q hK) uQ (herm Q' hK') uQ'
  have hcT : ∀ P : Matrix (Fin m) (Fin m) O,
      cT s (P.map O.subtype) = (cT σO P).map O.subtype := fun P => by ext i j; rfl
  refine ⟨bc O.subtype G, ?_, ?_, ?_⟩
  · have hv : ((bc O.subtype G : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) =
        (G : Matrix (Fin m) (Fin m) O).map O.subtype := rfl
    rw [hv, hcT, hG, Matrix.map_mul, Matrix.map_mul]
  · intro i j
    exact (G.val i j).2
  · intro i j
    rw [← map_inv]
    exact ((G⁻¹).val i j).2

/- English proof (translation)
Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Apply `τ.injective` to reduce the goal to its premises. Rewrite using `[h.2.2.2, h.2.2.2]`. Simplify using the standard rewrite rules.
-/
theorem sigma_sigma {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2]
  simp

/- English proof (translation)
Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul r e => simp [sigR, h]`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`.
-/
theorem sigR_sigR {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) (h : ∀ x, σ (σ x) = x) (y : R ⊗[F] E) : sigR R σ (sigR R σ y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [sigR, h]
  | add a b ha hb => simp only [map_add, ha, hb]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `∑ j, P i j * x j ∈ O`. Conclude with `O.sum_mem fun j _ => O.mul_mem (hP i j) (hx j)`.
-/
theorem mulVec_mem {R : Type} [CommRing R] (O : Subring R) {m : ℕ} (P : Matrix (Fin m) (Fin m) R)
    (hP : ∀ i j, P i j ∈ O) (x : Fin m → R) (hx : ∀ i, x i ∈ O) (i : Fin m) : P.mulVec x i ∈ O := by
  change ∑ j, P i j * x j ∈ O
  exact O.sum_mem fun j _ => O.mul_mem (hP i j) (hx j)

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM M J hJ J' hJ' d b`. Establish `h1` using `(GlobalTheory.T.integral_almost_all_places F E σ hCM d b).1`. Establish `ent : ∀ P : Matrix (Fin M) (Fin M) E, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ i j k, (Algebra.TensorProduct.basis (Fv F v) b).repr (inclR (F` using `F) (Fv F v) (P i j)) k ∈ v.adicCompletionIntegers F := fun P => Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => h1 (P i j)`. Use `filter_upwards [GlobalTheory.T.tensor_integer_ring_almost_all_places F E σ hCM d b, ent J, ent J', h1 (J.det)⁻¹, h1 (J'.det)⁻¹] with v hv eJ eJ' dJ dJ'`. Take `⟨O, hmem, hst, hfin, h2, hδ, -, hN⟩` from `hv`.

Establish `wit : ∀ P : Matrix (Fin M) (Fin M) E, P.det ≠ 0 → (∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr (inclR (F` using `F) (Fv F v) (P.det)⁻¹) k ∈ v.adicCompletionIntegers F) → ∃ w ∈ O, (JR (Fv F v) P).det * w = 1 := by`. Introduce `P hP hk`. Use `⟨inclR (F := F) (Fv F v) (P.det)⁻¹, (hmem _).2 hk, ?_⟩` and prove the remaining obligations. Establish `: (JR (Fv F v) P).det = inclR (F` using `F) (Fv F v) P.det := (RingHom.map_det (inclR (F := F) (Fv F v)) P).symm`. Rewrite using `[this, ← map_mul, mul_inv_cancel₀ hP, map_one]`.

Take `⟨g, hg, ig, ig'⟩` from `exists_gl_sub (sigR (Fv F v) σ) (sigR_sigR (Fv F v) σ (sigma_sigma σ hCM)) O hst h2 hδ hN M (JR (Fv F v) J) (JR (Fv F v) J') (map_mem_HermR (Fv F v) σ J hJ.1) (map_mem_HermR (Fv F v) σ J' hJ'.1) (fun i j => (hmem _).2 (eJ i j)) (fun i j => (hmem _).2 (eJ' i j)) (wit J hJ.2 dJ) (w …`. Use `⟨g, hg, fun n X => ?_⟩` and prove the remaining obligations. Establish `lat : ∀ Y : Fin n → Fin M → Fv F v ⊗[F] E, Y ∈ latV b v ↔ ∀ a i, Y a i ∈ O` using `fun Y => ⟨fun h a i => (hmem _).2 (h a i), fun h a i => (hmem _).1 (h a i)⟩`. Rewrite using `[lat, lat]`. Prove the components needed by the constructor for the conclusion.

Introduce `h a i`. Establish `e : X a = ((g⁻¹ : GL (Fin M) (Fv F v ⊗[F] E)) : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)).mulVec (actTup (Fv F v) g X a)`. Simplify using `only [actTup, Matrix.mulVec_mulVec]`. Rewrite using `[← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]`. Rewrite using `[e]`.

Conclude with `mulVec_mem O _ ig' _ (h a) i`. Introduce `h a i`. Conclude with `mulVec_mem O _ ig _ (h a) i`.
-/
theorem good_iso : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (J' : Matrix (Fin M) (Fin M) E), IsHermND σ J' → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∃ g : GL (Fin M) (Fv F v ⊗[F] E), JR (Fv F v) J' = cT (sigR (Fv F v) σ) (g : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) * JR (Fv F v) J * (g : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) ∧ ∀ (n : ℕ) (X : Fin n → Fin M → Fv F v ⊗[F] E), actTup (Fv F v) g X ∈ latV b v ↔ X ∈ latV b v := by
  intro F E _ _ _ _ _ σ hCM M J hJ J' hJ' d b
  have h1 := (GlobalTheory.T.integral_almost_all_places F E σ hCM d b).1
  have ent : ∀ P : Matrix (Fin M) (Fin M) E, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∀ i j k, (Algebra.TensorProduct.basis (Fv F v) b).repr (inclR (F := F) (Fv F v) (P i j)) k ∈
        v.adicCompletionIntegers F := fun P =>
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => h1 (P i j)
  filter_upwards [GlobalTheory.T.tensor_integer_ring_almost_all_places F E σ hCM d b, ent J, ent J', h1 (J.det)⁻¹, h1 (J'.det)⁻¹]
    with v hv eJ eJ' dJ dJ'
  obtain ⟨O, hmem, hst, hfin, h2, hδ, -, hN⟩ := hv
  have wit : ∀ P : Matrix (Fin M) (Fin M) E, P.det ≠ 0 →
      (∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr (inclR (F := F) (Fv F v) (P.det)⁻¹) k ∈
        v.adicCompletionIntegers F) → ∃ w ∈ O, (JR (Fv F v) P).det * w = 1 := by
    intro P hP hk
    refine ⟨inclR (F := F) (Fv F v) (P.det)⁻¹, (hmem _).2 hk, ?_⟩
    have : (JR (Fv F v) P).det = inclR (F := F) (Fv F v) P.det := (RingHom.map_det (inclR (F := F) (Fv F v)) P).symm
    rw [this, ← map_mul, mul_inv_cancel₀ hP, map_one]
  obtain ⟨g, hg, ig, ig'⟩ := exists_gl_sub (sigR (Fv F v) σ)
    (sigR_sigR (Fv F v) σ (sigma_sigma σ hCM)) O hst h2 hδ hN M (JR (Fv F v) J) (JR (Fv F v) J')
    (map_mem_HermR (Fv F v) σ J hJ.1) (map_mem_HermR (Fv F v) σ J' hJ'.1)
    (fun i j => (hmem _).2 (eJ i j)) (fun i j => (hmem _).2 (eJ' i j))
    (wit J hJ.2 dJ) (wit J' hJ'.2 dJ')
  refine ⟨g, hg, fun n X => ?_⟩
  have lat : ∀ Y : Fin n → Fin M → Fv F v ⊗[F] E, Y ∈ latV b v ↔ ∀ a i, Y a i ∈ O := fun Y =>
    ⟨fun h a i => (hmem _).2 (h a i), fun h a i => (hmem _).1 (h a i)⟩
  rw [lat, lat]
  constructor
  · intro h a i
    have e : X a = ((g⁻¹ : GL (Fin M) (Fv F v ⊗[F] E)) : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)).mulVec
        (actTup (Fv F v) g X a) := by
      simp only [actTup, Matrix.mulVec_mulVec]
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    rw [e]
    exact mulVec_mem O _ ig' _ (h a) i
  · intro h a i
    exact mulVec_mem O _ ig _ (h a) i

end GlobalTheory.CompanionTheory.SW.GoodIso
