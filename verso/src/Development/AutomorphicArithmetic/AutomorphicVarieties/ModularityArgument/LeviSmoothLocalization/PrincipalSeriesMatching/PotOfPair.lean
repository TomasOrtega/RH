import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PotOfPair
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.PotOfFlag
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.IneConj

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter UpperTheory.V.Af
open scoped Pointwise

section Mat

variable {Γ k : Type} [Group Γ] [Field k] {n : ℕ}

private def revM (k : Type) [Field k] (n : ℕ) : Matrix (Fin n) (Fin n) k := (1 : Matrix (Fin n) (Fin n) k).submatrix Fin.rev id

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.mul_apply]`. Simplify using `only [revM, Matrix.submatrix_apply, id, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]`.
-/
private theorem revM_mul (M : Matrix (Fin n) (Fin n) k) : revM k n * M = M.submatrix Fin.rev id := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [revM, Matrix.submatrix_apply, id, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.mul_apply]`. Simplify using `only [revM, Matrix.submatrix_apply, id, Matrix.one_apply, Fin.rev_eq_iff, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`.
-/
private theorem mul_revM (M : Matrix (Fin n) (Fin n) k) : M * revM k n = M.submatrix id Fin.rev := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [revM, Matrix.submatrix_apply, id, Matrix.one_apply, Fin.rev_eq_iff, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

/- English proof (translation)
Rewrite using `[revM_mul]`. Use extensionality with `i j`. Simplify using `[revM, Matrix.one_apply]`.
-/
private theorem revM_sq : revM k n * revM k n = 1 := by
  rw [revM_mul]
  ext i j
  simp [revM, Matrix.one_apply]

/- English proof (translation)
Take `⟨h, hh⟩` from `hκ`. Set `Dt : GL (Fin n) k` to `⟨((h⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).transpose, (h : Matrix (Fin n) (Fin n) k).transpose, by rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel]; simp, by rw [← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel]; simp⟩`. Set `J : GL (Fin n) k` to `⟨revM k n, revM k n, revM_sq, revM_sq⟩`. Establish `key : ∀ u : ↥H', ((Dt * P * r u * (Dt * P)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = (μ u : k) • ((h * r ((f u)⁻¹ : ↥H) * h⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).transpose`. Introduce `u`.

Establish `hinv : (r ((f u)⁻¹ : ↥H) : Matrix (Fin n) (Fin n) k).transpose * (r (f u) : Matrix (Fin n) (Fin n) k).transpose = 1`. Rewrite using `[← Matrix.transpose_mul, ← Units.val_mul, ← map_mul]`. Simplify using the standard rewrite rules. Establish `e1 : (P : Matrix (Fin n) (Fin n) k) * (r u : Matrix (Fin n) (Fin n) k) = (μ u : k) • ((r ((f u)⁻¹ : ↥H) : Matrix (Fin n) (Fin n) k).transpose * (P : Matrix (Fin n) (Fin n) k))`. Rewrite using `[← Matrix.mul_smul, ← hp u, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hinv, Matrix.one_mul]`.

Establish `e2 : ((Dt * P * r u : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = ((μ u : k) • ((h * r ((f u)⁻¹ : ↥H) * h⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).transpose) * ((Dt * P : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)`. Establish `e3 : (h : Matrix (Fin n) (Fin n) k).transpose * ((h⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).transpose = 1`. Rewrite using `[← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel]`. Simplify using the standard rewrite rules. Simplify using `only [Units.val_mul, Matrix.transpose_mul, Matrix.smul_mul]`.

Express the relevant statement in the definitionally equal form `((h⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).transpose * (P : Matrix (Fin n) (Fin n) k) * (r u : Matrix (Fin n) (Fin n) k) = _`. Rewrite using `[Matrix.mul_assoc, e1, Matrix.mul_smul]`. Use `congr 1`. Express the relevant statement in the definitionally equal form `_ = _ * (((h⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).transpose * (P : Matrix (Fin n) (Fin n) k))`. Simplify using `only [Matrix.mul_assoc]`.

Rewrite using `[← Matrix.mul_assoc (h : Matrix (Fin n) (Fin n) k).transpose, e3, Matrix.one_mul]`. Rewrite using `[Units.val_mul, e2, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel]`. Simplify using the standard rewrite rules. Use `⟨J * (Dt * P), fun u => ?_⟩` and prove the remaining obligations. Establish `e : (J * (Dt * P) * r u * (J * (Dt * P))⁻¹ : GL (Fin n) k) = J * (Dt * P * r u * (Dt * P)⁻¹) * J⁻¹` using `by group`.

Establish `e' : ∀ i j, (J * (Dt * P) * r u * (J * (Dt * P))⁻¹ : GL (Fin n) k) i j = (μ u : k) * (h * r ((f u)⁻¹ : ↥H) * h⁻¹ : GL (Fin n) k) (Fin.rev j) (Fin.rev i)`. Introduce `i j`. Rewrite using `[e]`. Establish `: ((J * (Dt * P * r u * (Dt * P)⁻¹) * J⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = revM k n * ((Dt * P * r u * (Dt * P)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * revM k n` using `rfl`. Rewrite using `[this, revM_mul, mul_revM, key]`.

Simplify using `only [Matrix.submatrix_apply, Matrix.smul_apply, Matrix.transpose_apply, id, smul_eq_mul]`. Use `⟨fun i j hij => ?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[e', (hh ((f u)⁻¹)).1 _ _ (Fin.rev_lt_rev.2 hij), mul_zero]`. Rewrite using `[e', (hh ((f u)⁻¹)).2]`. Simplify using `[div_eq_mul_inv]`.
-/
private theorem flag_rev (r : Γ →* GL (Fin n) k) {H H' : Subgroup Γ} (f : ↥H' →* ↥H) (μ : ↥H' →* kˣ) (P : GL (Fin n) k)
    (hp : ∀ u : ↥H', (r (f u) : Matrix (Fin n) (Fin n) k).transpose * (P : Matrix (Fin n) (Fin n) k) *
      (r u : Matrix (Fin n) (Fin n) k) = (μ u : k) • (P : Matrix (Fin n) (Fin n) k))
    {κ : Fin n → ↥H →* kˣ} (hκ : IsFlagOn r H κ) :
    IsFlagOn r H' fun i => μ * ((κ (Fin.rev i)).comp f)⁻¹ := by
  obtain ⟨h, hh⟩ := hκ
  let Dt : GL (Fin n) k := ⟨((h⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).transpose, (h : Matrix (Fin n) (Fin n) k).transpose,
    by rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel]; simp,
    by rw [← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel]; simp⟩
  let J : GL (Fin n) k := ⟨revM k n, revM k n, revM_sq, revM_sq⟩
  have key : ∀ u : ↥H', ((Dt * P * r u * (Dt * P)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      (μ u : k) • ((h * r ((f u)⁻¹ : ↥H) * h⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).transpose := by
    intro u
    have hinv : (r ((f u)⁻¹ : ↥H) : Matrix (Fin n) (Fin n) k).transpose * (r (f u) : Matrix (Fin n) (Fin n) k).transpose = 1 := by
      rw [← Matrix.transpose_mul, ← Units.val_mul, ← map_mul]
      simp
    have e1 : (P : Matrix (Fin n) (Fin n) k) * (r u : Matrix (Fin n) (Fin n) k) =
        (μ u : k) • ((r ((f u)⁻¹ : ↥H) : Matrix (Fin n) (Fin n) k).transpose * (P : Matrix (Fin n) (Fin n) k)) := by
      rw [← Matrix.mul_smul, ← hp u, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hinv, Matrix.one_mul]
    have e2 : ((Dt * P * r u : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
        ((μ u : k) • ((h * r ((f u)⁻¹ : ↥H) * h⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).transpose) *
          ((Dt * P : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
      have e3 : (h : Matrix (Fin n) (Fin n) k).transpose * ((h⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).transpose = 1 := by
        rw [← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel]
        simp
      simp only [Units.val_mul, Matrix.transpose_mul, Matrix.smul_mul]
      change ((h⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).transpose * (P : Matrix (Fin n) (Fin n) k) * (r u : Matrix (Fin n) (Fin n) k) = _
      rw [Matrix.mul_assoc, e1, Matrix.mul_smul]
      congr 1
      change _ = _ * (((h⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).transpose * (P : Matrix (Fin n) (Fin n) k))
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (h : Matrix (Fin n) (Fin n) k).transpose, e3, Matrix.one_mul]
    rw [Units.val_mul, e2, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel]
    simp
  refine ⟨J * (Dt * P), fun u => ?_⟩
  have e : (J * (Dt * P) * r u * (J * (Dt * P))⁻¹ : GL (Fin n) k) = J * (Dt * P * r u * (Dt * P)⁻¹) * J⁻¹ := by group
  have e' : ∀ i j, (J * (Dt * P) * r u * (J * (Dt * P))⁻¹ : GL (Fin n) k) i j =
      (μ u : k) * (h * r ((f u)⁻¹ : ↥H) * h⁻¹ : GL (Fin n) k) (Fin.rev j) (Fin.rev i) := by
    intro i j
    rw [e]
    have : ((J * (Dt * P * r u * (Dt * P)⁻¹) * J⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
        revM k n * ((Dt * P * r u * (Dt * P)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * revM k n := rfl
    rw [this, revM_mul, mul_revM, key]
    simp only [Matrix.submatrix_apply, Matrix.smul_apply, Matrix.transpose_apply, id, smul_eq_mul]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [e', (hh ((f u)⁻¹)).1 _ _ (Fin.rev_lt_rev.2 hij), mul_zero]
  · rw [e', (hh ((f u)⁻¹)).2]
    simp [div_eq_mul_inv]

end Mat

section Gal

/- English proof (translation)
Rewrite `h` using `[mul_pow, zpow_neg, inv_pow, mul_inv_eq_one]`. Conclude with `h`.
-/
private theorem pow_flag {U : Type} [CommGroup U] (x y : U) (m : ℤ) (k : ℕ) (h : (x * y ^ (-m)) ^ k = 1) :
    x ^ k = (y ^ m) ^ k := by
  rw [mul_pow, zpow_neg, inv_pow, mul_inv_eq_one] at h
  exact h

/- English proof (translation)
Rewrite using `[mul_pow, inv_pow, h, zpow_sub, mul_pow, inv_pow]`.
-/
private theorem pow_dual {U : Type} [CommGroup U] (x y : U) (b m : ℤ) (a : ℕ) (h : x ^ a = (y ^ m) ^ a) :
    (y ^ b * x⁻¹) ^ a = (y ^ (b - m)) ^ a := by
  rw [mul_pow, inv_pow, h, zpow_sub, mul_pow, inv_pow]

/- English proof (translation)
Rewrite using `[map_mul, map_mul, map_inv, mul_comm (χ g)⁻¹, inv_mul_cancel_right]`.
-/
private theorem char_conj {Γ U : Type} [Group Γ] [CommGroup U] (χ : Γ →* U) (g u : Γ) : χ (g⁻¹ * u * g) = χ u := by
  rw [map_mul, map_mul, map_inv, mul_comm (χ g)⁻¹, inv_mul_cancel_right]

/- English proof (translation)
Break down `lt_trichotomy i j with h | h | h` into its components or cases. Use `hm i j h` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Substitute `h` using the available equality. Use linear arithmetic over natural numbers and integers.

Use `hm j i h` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
private theorem gap {n : ℕ} {m : Fin n → ℤ} (hm : ∀ i j, i < j → m j + 2 ≤ m i) (i j : Fin n) : m i ≠ m j + 1 := by
  rcases lt_trichotomy i j with h | h | h
  · have := hm i j h
    omega
  · subst h
    omega
  · have := hm j i h
    omega

variable {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]

/- English proof (translation)
The claim follows from `HeightOneSpectrum.ext (Ideal.ext fun x => (h x).symm.trans (h' x))`.
-/
private theorem place_unique {F : Type} [Field F] [NumberField F] [Algebra F Ω] {A : ValuationSubring Ω}
    {w w' : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A w) (h' : IsPlaceOver A w') : w = w' :=
  HeightOneSpectrum.ext (Ideal.ext fun x => (h x).symm.trans (h' x))

/- English proof (translation)
Introduce `x` and use `by have hA' : ∀ y, g.toRingEquiv y ∈ g • A ↔ y ∈ A := fun y => ValuationSubring.smul_mem_pointwise_smul_iff have e : g.toRingEquiv (algebraMap L Ω (x : L)) = algebraMap L Ω (x : L) := g.commutes _ have h1 := val_lt_one hA' (algebraMap L Ω (x : L)) rw [e] at h1 exact h1.trans (h x …`.
-/
private theorem place_smul (g : G L Ω) {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 L)} (h : IsPlaceOver A w) :
    IsPlaceOver (g • A) w := fun x => by
  have hA' : ∀ y, g.toRingEquiv y ∈ g • A ↔ y ∈ A := fun y => ValuationSubring.smul_mem_pointwise_smul_iff
  have e : g.toRingEquiv (algebraMap L Ω (x : L)) = algebraMap L Ω (x : L) := g.commutes _
  have h1 := val_lt_one hA' (algebraMap L Ω (x : L))
  rw [e] at h1
  exact h1.trans (h x)

/- English proof (translation)
Introduce `x` and use `by rw [IsScalarTower.algebraMap_apply (W.Lp L) L Ω] exact h (algebraMap (𝓞 (W.Lp L)) (𝓞 L) x)`.
-/
private theorem place_under {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 L)} (h : IsPlaceOver A w) :
    IsPlaceOver A (w.under (𝓞 (W.Lp L))) := fun x => by
  rw [IsScalarTower.algebraMap_apply (W.Lp L) L Ω]
  exact h (algebraMap (𝓞 (W.Lp L)) (𝓞 L) x)

private instance normalLp : Normal (W.Lp L) L :=
  (Algebra.IsQuadraticExtension.isGalois (W.Lp L) L).to_normal

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, rfl⟩`. Use `AlgEquiv.ext fun x => (algebraMap L Ω).injective ?_` and prove the remaining obligations. Establish `h` using `AlgEquiv.restrictNormal_commutes (W.resP L Ω u) L x`. Conclude with `h.trans (u.commutes x)`.

Introduce `h`. Use `⟨AlgEquiv.ofRingEquiv (f := γ.toRingEquiv) fun y => ?_, AlgEquiv.ext fun _ => rfl⟩` and prove the remaining obligations. Establish `h1 : γ.restrictNormal L = 1` using `h`. Establish `h2` using `AlgEquiv.restrictNormal_commutes γ L y`. Rewrite `h2` using `[h1]`.

Conclude with `h2.symm`.
-/
private theorem range_iff (γ : G (W.Lp L) Ω) :
    γ ∈ (W.resP L Ω).range ↔ AlgEquiv.restrictNormalHom L γ = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    refine AlgEquiv.ext fun x => (algebraMap L Ω).injective ?_
    have h := AlgEquiv.restrictNormal_commutes (W.resP L Ω u) L x
    exact h.trans (u.commutes x)
  · intro h
    refine ⟨AlgEquiv.ofRingEquiv (f := γ.toRingEquiv) fun y => ?_, AlgEquiv.ext fun _ => rfl⟩
    have h1 : γ.restrictNormal L = 1 := h
    have h2 := AlgEquiv.restrictNormal_commutes γ L y
    rw [h1] at h2
    exact h2.symm

/- English proof (translation)
Establish `h : c⁻¹ * W.resP L Ω u * c ∈ (W.resP L Ω).range`. Rewrite using `[range_iff, map_mul, map_mul, (range_iff (W.resP L Ω u)).1 ⟨u, rfl⟩, map_inv]`. Simplify using the standard rewrite rules. Conclude with `h`.
-/
private theorem norm_res (c : G (W.Lp L) Ω) (u : G L Ω) : ∃ u' : G L Ω, W.resP L Ω u' = c⁻¹ * W.resP L Ω u * c := by
  have h : c⁻¹ * W.resP L Ω u * c ∈ (W.resP L Ω).range := by
    rw [range_iff, map_mul, map_mul, (range_iff (W.resP L Ω u)).1 ⟨u, rfl⟩, map_inv]
    simp
  exact h

/- English proof (translation)
Introduce and unpack `⟨u, rfl⟩`. Take `⟨j, hj⟩` from `hc`. Use `IsCMField.complexConj_ne_one L (AlgEquiv.ext fun x => ?_)` and prove the remaining obligations. Apply `(j.comp (algebraMap L Ω)).injective` to reduce the goal to its premises. Establish `h1` using `IsCMField.complexEmbedding_complexConj L (j.comp (algebraMap L Ω)) x`.

Establish `h2` using `hj (algebraMap L Ω x)`. Establish `h3 : (W.resP L Ω u) (algebraMap L Ω x) = algebraMap L Ω x` using `u.commutes x`. Rewrite `h2` using `[h3]`. Rewrite using `[h1]`. Conclude with `h2.symm`.
-/
private theorem conj_not_mem {c : G (W.Lp L) Ω} (hc : ∃ j : Ω →+* ℂ, ∀ x, j (c x) = starRingEnd ℂ (j x)) :
    c ∉ (W.resP L Ω).range := by
  rintro ⟨u, rfl⟩
  obtain ⟨j, hj⟩ := hc
  refine IsCMField.complexConj_ne_one L (AlgEquiv.ext fun x => ?_)
  apply (j.comp (algebraMap L Ω)).injective
  have h1 := IsCMField.complexEmbedding_complexConj L (j.comp (algebraMap L Ω)) x
  have h2 := hj (algebraMap L Ω x)
  have h3 : (W.resP L Ω u) (algebraMap L Ω x) = algebraMap L Ω x := u.commutes x
  rw [h3] at h2
  rw [h1]
  exact h2.symm

/- English proof (translation)
Establish `hcard : Nat.card (L ≃ₐ[W.Lp L] L) = 2` using `(IsGalois.card_aut_eq_finrank (W.Lp L) L).trans (Algebra.IsQuadraticExtension.finrank_eq_two (W.Lp L) L)`. Take `⟨t, -, hu⟩` from `(Nat.card_eq_two_iff' (1 : L ≃ₐ[W.Lp L] L)).1 hcard`. Establish `h1` using `hu _ (fun e => hc ((range_iff c).2 e))`. Establish `h2` using `hu _ (fun e => hγ ((range_iff γ).2 e))`. Establish `h : γ * c⁻¹ ∈ (W.resP L Ω).range`.

Rewrite using `[range_iff, map_mul, map_inv, h1, h2, mul_inv_cancel]`. Conclude with `h`.
-/
private theorem exists_res_mul {c γ : G (W.Lp L) Ω} (hc : c ∉ (W.resP L Ω).range) (hγ : γ ∉ (W.resP L Ω).range) :
    ∃ g : G L Ω, W.resP L Ω g = γ * c⁻¹ := by
  have hcard : Nat.card (L ≃ₐ[W.Lp L] L) = 2 :=
    (IsGalois.card_aut_eq_finrank (W.Lp L) L).trans (Algebra.IsQuadraticExtension.finrank_eq_two (W.Lp L) L)
  obtain ⟨t, -, hu⟩ := (Nat.card_eq_two_iff' (1 : L ≃ₐ[W.Lp L] L)).1 hcard
  have h1 := hu _ (fun e => hc ((range_iff c).2 e))
  have h2 := hu _ (fun e => hγ ((range_iff γ).2 e))
  have h : γ * c⁻¹ ∈ (W.resP L Ω).range := by
    rw [range_iff, map_mul, map_inv, h1, h2, mul_inv_cancel]
  exact h

variable {l : ℕ} [Fact l.Prime] {n : ℕ}

private def FlagAt (ρ : G L Ω →* GL (Fin n) (Qbar l)) (A : ValuationSubring Ω) (m : Fin n → ℤ) : Prop :=
  ∃ (κ : Fin n → ↥(Dec (F := L) A) →* (Qbar l)ˣ) (a : ℕ), 0 < a ∧ IsFlagOn ρ (Dec (F := L) A) κ ∧
    ∀ i (s : ↥(Dec (F := L) A)), (s : G L Ω) ∈ Ine (F := L) A → κ i s ^ a = (cycBar L Ω l s ^ m i) ^ a

/- English proof (translation)
Take `⟨κ, a, ha, ⟨x, hx⟩, hp⟩` from `h`. Set `f : ↥(Dec (F` to `L) (g • A)) →* ↥(Dec (F := L) A) := { toFun := fun u => ⟨g⁻¹ * u * g, by`. Establish `hu` using `mem_Dec.1 u.2`. Rewrite using `[mem_Dec, mul_smul, mul_smul, hu, inv_smul_smul]⟩`. Use the proof step `map_one' := Subtype.ext (by simp)`.

Use the proof step `map_mul' := fun a b => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }`. Use `⟨fun i => (κ i).comp f, a, ha, ⟨x * (ρ g)⁻¹, fun u => ?_⟩, fun i s hs => ?_⟩` and prove the remaining obligations. Establish `e1 : ((f u : ↥(Dec (F` using `L) A)) : G L Ω) = g⁻¹ * u * g := rfl`. Establish `e : x * (ρ g)⁻¹ * ρ u * (x * (ρ g)⁻¹)⁻¹ = x * ρ (f u : ↥(Dec (F` using `L) A)) * x⁻¹ := by`. Rewrite using `[e1, map_mul, map_mul, map_inv]`.

Use `group`. Rewrite using `[e]`. Conclude with `hx (f u)`. Establish `h1` using `hp i (f s) ((UpperTheory.V.Two.ineConj L Ω g).1 A s hs)`. Establish `e1 : ((f s : ↥(Dec (F` using `L) A)) : G L Ω) = g⁻¹ * s * g := rfl`.

Establish `e : cycBar L Ω l (f s : ↥(Dec (F` using `L) A)) = cycBar L Ω l s := by rw [e1, char_conj]`. Rewrite `h1` using `[e]`. Conclude with `h1`.
-/
private theorem FlagAt.smul {ρ : G L Ω →* GL (Fin n) (Qbar l)} {A : ValuationSubring Ω} {m : Fin n → ℤ} (g : G L Ω)
    (h : FlagAt ρ A m) : FlagAt ρ (g • A) m := by
  obtain ⟨κ, a, ha, ⟨x, hx⟩, hp⟩ := h
  let f : ↥(Dec (F := L) (g • A)) →* ↥(Dec (F := L) A) :=
    { toFun := fun u => ⟨g⁻¹ * u * g, by
        have hu := mem_Dec.1 u.2
        rw [mem_Dec, mul_smul, mul_smul, hu, inv_smul_smul]⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  refine ⟨fun i => (κ i).comp f, a, ha, ⟨x * (ρ g)⁻¹, fun u => ?_⟩, fun i s hs => ?_⟩
  · have e1 : ((f u : ↥(Dec (F := L) A)) : G L Ω) = g⁻¹ * u * g := rfl
    have e : x * (ρ g)⁻¹ * ρ u * (x * (ρ g)⁻¹)⁻¹ = x * ρ (f u : ↥(Dec (F := L) A)) * x⁻¹ := by
      rw [e1, map_mul, map_mul, map_inv]
      group
    rw [e]
    exact hx (f u)
  · have h1 := hp i (f s) ((UpperTheory.V.Two.ineConj L Ω g).1 A s hs)
    have e1 : ((f s : ↥(Dec (F := L) A)) : G L Ω) = g⁻¹ * s * g := rfl
    have e : cycBar L Ω l (f s : ↥(Dec (F := L) A)) = cycBar L Ω l s := by rw [e1, char_conj]
    rw [e] at h1
    exact h1

/- English proof (translation)
Use `choose t ht using norm_res (L := L) (Ω := Ω) c`. Establish `hinj : Function.Injective (W.resP L Ω)` using `fun a b e => AlgEquiv.ext fun x => DFunLike.congr_fun e x`. Set `f : ↥(Dec (F` to `L) (c • A)) →* ↥(Dec (F := L) A) := { toFun := fun u => ⟨t u, by`. Establish `hu : W.resP L Ω u • c • A = c • A` using `mem_Dec.1 u.2`. Use `mem_Dec.2 ?_` and prove the remaining obligations.

Use `show W.resP L Ω (t u) • A = A`. Rewrite using `[ht, mul_smul, mul_smul, hu, inv_smul_smul]⟩`. Use the proof step `map_one' := Subtype.ext (hinj (by`. Establish `e1 : W.resP L Ω (1 : G L Ω) = 1` using `map_one _`. Express the relevant statement in the definitionally equal form `W.resP L Ω (t 1) = W.resP L Ω 1`.

Rewrite using `[ht, e1]`. Use the proof step `group))`. Use the proof step `map_mul' := fun a b => Subtype.ext (hinj (by`. Simplify using `only [Subgroup.coe_mul, map_mul, ht]`. Use the proof step `group)) }`.

Take `⟨κ, a, ha, hf, hp⟩` from `h`. Set `μ : ↥(Dec (F` to `L) (c • A)) →* (Qbar l)ˣ := ((cycBar L Ω l ^ a₀).comp (Dec (F := L) A).subtype).comp f`. Use `⟨fun i => μ * ((κ (Fin.rev i)).comp f)⁻¹, a, ha, flag_rev ρ f μ P (fun u => ?_) hf, fun i s hs => ?_⟩` and prove the remaining obligations. Use `hP (t u) u ?_` and prove the remaining obligations. Establish `e` using `ht u`.

Express the relevant statement in the definitionally equal form `W.resP L Ω u = c * W.resP L Ω (t u) * c⁻¹`. Rewrite using `[e]`. Use `group`. Establish `hs' : ((f s : ↥(Dec (F` using `L) A)) : G L Ω) ∈ Ine (F := L) A := by`. Establish `h1` using `(UpperTheory.V.Two.ineConj (W.Lp L) Ω c).1 A (W.resP L Ω s) hs`.

Rewrite `h1` using `[← ht]`. Conclude with `h1`. Establish `h2` using `hp (Fin.rev i) (f s) hs'`. Establish `e : cycBar L Ω l (f s : ↥(Dec (F` using `L) A)) = cycBar L Ω l s := by`. Express the relevant statement in the definitionally equal form `cycBar (W.Lp L) Ω l (W.resP L Ω (t s)) = cycBar (W.Lp L) Ω l (W.resP L Ω s)`.

Rewrite using `[ht, char_conj]`. Rewrite `h2` using `[e]`. Express the relevant statement in the definitionally equal form `(cycBar L Ω l (f s : ↥(Dec (F := L) A)) ^ a₀ * (κ (Fin.rev i) (f s))⁻¹) ^ a = _`. Rewrite using `[e]`. Conclude with `pow_dual _ _ _ _ _ h2`.
-/
private theorem FlagAt.dual {ρ : G L Ω →* GL (Fin n) (Qbar l)} {A : ValuationSubring Ω} {m : Fin n → ℤ}
    (c : G (W.Lp L) Ω) (a₀ : ℤ) (P : GL (Fin n) (Qbar l)) (hP : IsPairing c ρ (cycBar L Ω l ^ a₀) P)
    (h : FlagAt ρ A m) : FlagAt ρ (c • A) fun i => a₀ - m (Fin.rev i) := by
  choose t ht using norm_res (L := L) (Ω := Ω) c
  have hinj : Function.Injective (W.resP L Ω) := fun a b e => AlgEquiv.ext fun x => DFunLike.congr_fun e x
  let f : ↥(Dec (F := L) (c • A)) →* ↥(Dec (F := L) A) :=
    { toFun := fun u => ⟨t u, by
        have hu : W.resP L Ω u • c • A = c • A := mem_Dec.1 u.2
        refine mem_Dec.2 ?_
        show W.resP L Ω (t u) • A = A
        rw [ht, mul_smul, mul_smul, hu, inv_smul_smul]⟩
      map_one' := Subtype.ext (hinj (by
        have e1 : W.resP L Ω (1 : G L Ω) = 1 := map_one _
        change W.resP L Ω (t 1) = W.resP L Ω 1
        rw [ht, e1]
        group))
      map_mul' := fun a b => Subtype.ext (hinj (by
        simp only [Subgroup.coe_mul, map_mul, ht]
        group)) }
  obtain ⟨κ, a, ha, hf, hp⟩ := h
  let μ : ↥(Dec (F := L) (c • A)) →* (Qbar l)ˣ := ((cycBar L Ω l ^ a₀).comp (Dec (F := L) A).subtype).comp f
  refine ⟨fun i => μ * ((κ (Fin.rev i)).comp f)⁻¹, a, ha, flag_rev ρ f μ P (fun u => ?_) hf, fun i s hs => ?_⟩
  · refine hP (t u) u ?_
    have e := ht u
    change W.resP L Ω u = c * W.resP L Ω (t u) * c⁻¹
    rw [e]
    group
  · have hs' : ((f s : ↥(Dec (F := L) A)) : G L Ω) ∈ Ine (F := L) A := by
      have h1 := (UpperTheory.V.Two.ineConj (W.Lp L) Ω c).1 A (W.resP L Ω s) hs
      rw [← ht] at h1
      exact h1
    have h2 := hp (Fin.rev i) (f s) hs'
    have e : cycBar L Ω l (f s : ↥(Dec (F := L) A)) = cycBar L Ω l s := by
      change cycBar (W.Lp L) Ω l (W.resP L Ω (t s)) = cycBar (W.Lp L) Ω l (W.resP L Ω s)
      rw [ht, char_conj]
    rw [e] at h2
    change (cycBar L Ω l (f s : ↥(Dec (F := L) A)) ^ a₀ * (κ (Fin.rev i) (f s))⁻¹) ^ a = _
    rw [e]
    exact pow_dual _ _ _ _ _ h2

end Gal

/- English proof (translation)
Introduce `l _ L Ω _ _ _ _ _ _ s n ρ a P hP ψ m hm hfl hk w hw`. Take `⟨k, hk0, hk⟩` from `hk`. Take `⟨v, hvw⟩ : ∃ v : W.Vl l L, v.1 = w.under (𝓞 (W.Lp L))` from `⟨⟨w.under (𝓞 (W.Lp L)), Ideal.mem_comap.2 (by simpa using hw)⟩, rfl⟩`. Establish `hf : FlagAt ρ (s.A v.1) (m v)` using `⟨ψ v, k, hk0, hfl v, fun i g hg => pow_flag _ _ _ _ (hk v i g hg)⟩`. Distinguish the cases in `hw' : w = s.w v.1`.

Use `potOfFlag L Ω l n ρ (m v) (gap (hm v)) w hw fun A hA => ?_` and prove the remaining obligations. Take `⟨g, rfl⟩` from `exists_smul_eq_of_isPlaceOver (hw' ▸ s.hw v.1) hA`. Conclude with `hf.smul g`. Use `potOfFlag L Ω l n ρ (fun i => a - m v (Fin.rev i)) (gap fun i j hij => ?_) w hw fun A hA => ?_` and prove the remaining obligations. Use `hm v (Fin.rev j) (Fin.rev i) (Fin.rev_lt_rev.2 hij)` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `h1 : IsPlaceOver A v.1` using `hvw ▸ place_under hA`. Take `⟨γ, hγ⟩` from `exists_smul_eq_of_isPlaceOver (s.hA v.1) h1`. Establish `hγ' : γ ∉ (W.resP L Ω).range`. Introduce and unpack `⟨g, rfl⟩`.

Conclude with `hw' (place_unique hA (hγ ▸ place_smul g (s.hw v.1)))`. Take `⟨g, hg⟩` from `exists_res_mul (conj_not_mem s.hc) hγ'`. Establish `e : A = g • s.c • s.A v.1`. Rewrite using `[← hγ]`. Express the relevant statement in the definitionally equal form `γ • s.A v.1 = W.resP L Ω g • s.c • s.A v.1`.

Rewrite using `[hg, ← mul_smul, inv_mul_cancel_right]`. Rewrite using `[e]`. Conclude with `(hf.dual s.c a P hP).smul g`.
-/
theorem UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.potOfPair :
    UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.PotOfPair := by
  intro l _ L Ω _ _ _ _ _ _ s n ρ a P hP ψ m hm hfl hk w hw
  obtain ⟨k, hk0, hk⟩ := hk
  obtain ⟨v, hvw⟩ : ∃ v : W.Vl l L, v.1 = w.under (𝓞 (W.Lp L)) :=
    ⟨⟨w.under (𝓞 (W.Lp L)), Ideal.mem_comap.2 (by simpa using hw)⟩, rfl⟩
  have hf : FlagAt ρ (s.A v.1) (m v) :=
    ⟨ψ v, k, hk0, hfl v, fun i g hg => pow_flag _ _ _ _ (hk v i g hg)⟩
  by_cases hw' : w = s.w v.1
  · refine potOfFlag L Ω l n ρ (m v) (gap (hm v)) w hw fun A hA => ?_
    obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver (hw' ▸ s.hw v.1) hA
    exact hf.smul g
  · refine potOfFlag L Ω l n ρ (fun i => a - m v (Fin.rev i)) (gap fun i j hij => ?_) w hw fun A hA => ?_
    · have := hm v (Fin.rev j) (Fin.rev i) (Fin.rev_lt_rev.2 hij)
      omega
    have h1 : IsPlaceOver A v.1 := hvw ▸ place_under hA
    obtain ⟨γ, hγ⟩ := exists_smul_eq_of_isPlaceOver (s.hA v.1) h1
    have hγ' : γ ∉ (W.resP L Ω).range := by
      rintro ⟨g, rfl⟩
      exact hw' (place_unique hA (hγ ▸ place_smul g (s.hw v.1)))
    obtain ⟨g, hg⟩ := exists_res_mul (conj_not_mem s.hc) hγ'
    have e : A = g • s.c • s.A v.1 := by
      rw [← hγ]
      change γ • s.A v.1 = W.resP L Ω g • s.c • s.A v.1
      rw [hg, ← mul_smul, inv_mul_cancel_right]
    rw [e]
    exact (hf.dual s.c a P hP).smul g
