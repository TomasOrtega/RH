import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.ApartOfNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdelicUnitaryPointEqOfSectionComponentsEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixExtPLoc
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open GlobalTheory.SplitPts (conjE)
open GroundTheory.Global.AdeleBaseChange (finiteAdeleMap)
open scoped TensorProduct

namespace UpperTheory.Gal.W2.Seed

section Core
variable {R R' : Type} [CommRing R] [CommRing R'] {n : ℕ}

/- English proof (translation)
Establish `h1 : (1 - ε) * (1 - ε) = 1 - ε` using `by linear_combination he`. Establish `h2 : (1 - ε) * ε = 0` using `by linear_combination -he`. Establish `h3 : ε * (1 - ε) = 0` using `by linear_combination -he`. Simplify using `only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_one, Matrix.one_mul, h1, h2, h3, he, zero_smul, add_zero, zero_add]`.
-/
private theorem mulG {ε : R} (he : ε * ε = ε) (A B : Matrix (Fin n) (Fin n) R) :
    ((1 - ε) • A + ε • (1 : Matrix (Fin n) (Fin n) R)) * ((1 - ε) • B + ε • (1 : Matrix (Fin n) (Fin n) R)) =
      (1 - ε) • (A * B) + ε • (1 : Matrix (Fin n) (Fin n) R) := by
  have h1 : (1 - ε) * (1 - ε) = 1 - ε := by linear_combination he
  have h2 : (1 - ε) * ε = 0 := by linear_combination -he
  have h3 : ε * (1 - ε) = 0 := by linear_combination -he
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_one, Matrix.one_mul, h1, h2, h3, he,
    zero_smul, add_zero, zero_add]

/- English proof (translation)
Use extensionality with `i k`. Establish `hik : Φ (M i k - N i k) = 0`. Use `congrFun (congrFun h i) k` as an intermediate fact. Simplify using `only [Matrix.map_apply] at this`. Rewrite using `[map_sub, this, sub_self]`.

Use `hker _ hik` as an intermediate fact. Simplify using `only [Matrix.smul_apply, smul_eq_mul]`. Take the linear combination `this`.
-/
private theorem smul_eq_of_map (Φ : R →+* R') {ε : R} (hker : ∀ z, Φ z = 0 → (1 - ε) * z = 0)
    {M N : Matrix (Fin n) (Fin n) R} (h : M.map Φ = N.map Φ) : (1 - ε) • M = (1 - ε) • N := by
  ext i k
  have hik : Φ (M i k - N i k) = 0 := by
    have := congrFun (congrFun h i) k
    simp only [Matrix.map_apply] at this
    rw [map_sub, this, sub_self]
  have := hker _ hik
  simp only [Matrix.smul_apply, smul_eq_mul]
  linear_combination this

/- English proof (translation)
Rewrite using `[mulG he]`. Establish `h1 : (a' * Y * a * (a' * Y' * a)).map Φ = (1 : Matrix (Fin n) (Fin n) R).map Φ`. Establish `e : a' * Y * a * (a' * Y' * a) = a' * Y * (a * a') * Y' * a` using `by simp only [Matrix.mul_assoc]`. Establish `hA : a'.map Φ * a.map Φ = 1`. Rewrite using `[← Matrix.map_mul, ha', Matrix.map_one _ (map_zero Φ) (map_one Φ)]`.

Rewrite using `[e, haa, Matrix.mul_one, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.mul_assoc (a'.map Φ), hYY, Matrix.mul_one, hA, Matrix.map_one _ (map_zero Φ) (map_one Φ)]`. Rewrite using `[smul_eq_of_map Φ hker h1, ← add_smul, sub_add_cancel, one_smul]`.
-/
private theorem inv_part (Φ : R →+* R') {ε : R} (he : ε * ε = ε) (hker : ∀ z, Φ z = 0 → (1 - ε) * z = 0)
    {a a' Y Y' : Matrix (Fin n) (Fin n) R} (haa : a * a' = 1) (ha' : a' * a = 1)
    (hYY : Y.map Φ * Y'.map Φ = 1) :
    ((1 - ε) • (a' * Y * a) + ε • (1 : Matrix (Fin n) (Fin n) R)) *
      ((1 - ε) • (a' * Y' * a) + ε • (1 : Matrix (Fin n) (Fin n) R)) = 1 := by
  rw [mulG he]
  have h1 : (a' * Y * a * (a' * Y' * a)).map Φ = (1 : Matrix (Fin n) (Fin n) R).map Φ := by
    have e : a' * Y * a * (a' * Y' * a) = a' * Y * (a * a') * Y' * a := by simp only [Matrix.mul_assoc]
    have hA : a'.map Φ * a.map Φ = 1 := by
      rw [← Matrix.map_mul, ha', Matrix.map_one _ (map_zero Φ) (map_one Φ)]
    rw [e, haa, Matrix.mul_one, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.mul_assoc (a'.map Φ), hYY,
      Matrix.mul_one, hA, Matrix.map_one _ (map_zero Φ) (map_one Φ)]
  rw [smul_eq_of_map Φ hker h1, ← add_smul, sub_add_cancel, one_smul]

/- English proof (translation)
Establish `hGs : ((((1 - ε) • (a' * Y * a) + ε • (1 : Matrix (Fin n) (Fin n) R))).map σ)ᵀ = (1 - ε) • ((a' * Y * a).map σ)ᵀ + ε • (1 : Matrix (Fin n) (Fin n) R)`. Use extensionality with `i k`. Simplify using `only [Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul, map_sub, map_one, hσe]`. Break down `eq_or_ne i k with rfl | h` into its components or cases. Simplify using the standard rewrite rules.

Simplify using `[Matrix.one_apply, h, h.symm]`. Rewrite using `[hGs, mulG he]`. Establish `hab : (a'.map σ)ᵀ * (a.map σ)ᵀ = 1`. Rewrite using `[← Matrix.transpose_mul, ← Matrix.map_mul, haa, Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.transpose_one]`. Establish `hDa : D * a = (a'.map σ)ᵀ`.

Establish `: (a'.map σ)ᵀ * ((a.map σ)ᵀ * D * a) = (a'.map σ)ᵀ` using `by rw [hD, Matrix.mul_one]`. Rewrite `this` using `[Matrix.mul_assoc ((a.map σ)ᵀ), ← Matrix.mul_assoc, hab, Matrix.one_mul]`. Then use the resulting hypothesis. Establish `hD2 : (a'.map σ)ᵀ * a' = D` using `by rw [← hDa, Matrix.mul_assoc, haa, Matrix.mul_one]`. Establish `e1 : ((a' * Y * a).map σ)ᵀ * (a' * Y * a) = (a.map σ)ᵀ * ((Y.map σ)ᵀ * D * Y) * a`. Rewrite using `[Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul, ← hD2]`.

Simplify using `only [Matrix.mul_assoc]`. Establish `hS : ∀ M : Matrix (Fin n) (Fin n) R, ((M.map σ)ᵀ).map Φ = ((M.map Φ).map σ')ᵀ`. Introduce `M`. Use extensionality with `i k`. Simplify using `[Matrix.map_apply, Matrix.transpose_apply, hσ]`.

Establish `h1 : (((a' * Y * a).map σ)ᵀ * (a' * Y * a)).map Φ = (t • (1 : Matrix (Fin n) (Fin n) R)).map Φ`. Establish `h2 : ((a.map σ)ᵀ * D * a).map Φ = (1 : Matrix (Fin n) (Fin n) R).map Φ` using `by rw [hD]`. Rewrite `h2` using `[Matrix.map_mul, Matrix.map_mul, Matrix.map_one _ (map_zero Φ) (map_one Φ)]`. Establish `h3 : (t • (1 : Matrix (Fin n) (Fin n) R)).map Φ = Φ t • (1 : Matrix (Fin n) (Fin n) R')`. Use extensionality with `i k`.

Break down `eq_or_ne i k with rfl | h` into its components or cases. Simplify using the standard rewrite rules. Simplify using `[Matrix.one_apply, h]`. Rewrite using `[e1, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, hS Y, hX, h3, Matrix.mul_smul, Matrix.smul_mul, h2]`. Rewrite using `[smul_eq_of_map Φ hker h1, smul_smul, ← add_smul]`.
-/
private theorem star_part (Φ : R →+* R') (σ : R →+* R) (σ' : R' →+* R') {ε t : R}
    (hσ : ∀ x, Φ (σ x) = σ' (Φ x)) (he : ε * ε = ε) (hσe : σ ε = ε)
    (hker : ∀ z, Φ z = 0 → (1 - ε) * z = 0)
    {a a' D Y : Matrix (Fin n) (Fin n) R} (haa : a * a' = 1) (ha' : a' * a = 1)
    (hD : (a.map σ)ᵀ * D * a = 1)
    (hX : ((Y.map Φ).map σ')ᵀ * D.map Φ * Y.map Φ = Φ t • D.map Φ) :
    ((((1 - ε) • (a' * Y * a) + ε • (1 : Matrix (Fin n) (Fin n) R))).map σ)ᵀ *
      ((1 - ε) • (a' * Y * a) + ε • (1 : Matrix (Fin n) (Fin n) R)) =
      ((1 - ε) * t + ε) • (1 : Matrix (Fin n) (Fin n) R) := by
  have hGs : ((((1 - ε) • (a' * Y * a) + ε • (1 : Matrix (Fin n) (Fin n) R))).map σ)ᵀ =
      (1 - ε) • ((a' * Y * a).map σ)ᵀ + ε • (1 : Matrix (Fin n) (Fin n) R) := by
    ext i k
    simp only [Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul,
      map_sub, map_one, hσe]
    rcases eq_or_ne i k with rfl | h
    · simp
    · simp [Matrix.one_apply, h, h.symm]
  rw [hGs, mulG he]
  have hab : (a'.map σ)ᵀ * (a.map σ)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← Matrix.map_mul, haa, Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.transpose_one]
  have hDa : D * a = (a'.map σ)ᵀ := by
    have : (a'.map σ)ᵀ * ((a.map σ)ᵀ * D * a) = (a'.map σ)ᵀ := by rw [hD, Matrix.mul_one]
    rwa [Matrix.mul_assoc ((a.map σ)ᵀ), ← Matrix.mul_assoc, hab, Matrix.one_mul] at this
  have hD2 : (a'.map σ)ᵀ * a' = D := by rw [← hDa, Matrix.mul_assoc, haa, Matrix.mul_one]
  have e1 : ((a' * Y * a).map σ)ᵀ * (a' * Y * a) = (a.map σ)ᵀ * ((Y.map σ)ᵀ * D * Y) * a := by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul, ← hD2]
    simp only [Matrix.mul_assoc]
  have hS : ∀ M : Matrix (Fin n) (Fin n) R, ((M.map σ)ᵀ).map Φ = ((M.map Φ).map σ')ᵀ := by
    intro M
    ext i k
    simp [Matrix.map_apply, Matrix.transpose_apply, hσ]
  have h1 : (((a' * Y * a).map σ)ᵀ * (a' * Y * a)).map Φ = (t • (1 : Matrix (Fin n) (Fin n) R)).map Φ := by
    have h2 : ((a.map σ)ᵀ * D * a).map Φ = (1 : Matrix (Fin n) (Fin n) R).map Φ := by rw [hD]
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_one _ (map_zero Φ) (map_one Φ)] at h2
    have h3 : (t • (1 : Matrix (Fin n) (Fin n) R)).map Φ = Φ t • (1 : Matrix (Fin n) (Fin n) R') := by
      ext i k
      rcases eq_or_ne i k with rfl | h
      · simp
      · simp [Matrix.one_apply, h]
    rw [e1, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, hS Y, hX, h3, Matrix.mul_smul, Matrix.smul_mul, h2]
  rw [smul_eq_of_map Φ hker h1, smul_smul, ← add_smul]

/- English proof (translation)
Establish `e : a * ((1 - ε) • (a' * Y * a) + ε • (1 : Matrix (Fin n) (Fin n) R)) * a' = (1 - ε) • Y + ε • (1 : Matrix (Fin n) (Fin n) R)`. Establish `e1 : a * (a' * Y * a) * a' = Y`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, e1, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, haa]`. Rewrite using `[e]`.

Use extensionality with `i k`. Simplify using `[Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, hΦe]`.
-/
private theorem conj_part (Φ : R →+* R') {ε : R} (hΦe : Φ ε = 0)
    {a a' Y : Matrix (Fin n) (Fin n) R} (haa : a * a' = 1) (ha' : a' * a = 1) :
    (a * ((1 - ε) • (a' * Y * a) + ε • (1 : Matrix (Fin n) (Fin n) R)) * a').map Φ = Y.map Φ := by
  have e : a * ((1 - ε) • (a' * Y * a) + ε • (1 : Matrix (Fin n) (Fin n) R)) * a' = (1 - ε) • Y + ε • (1 : Matrix (Fin n) (Fin n) R) := by
    have e1 : a * (a' * Y * a) * a' = Y := by
      calc a * (a' * Y * a) * a' = (a * a') * Y * (a * a') := by simp only [Matrix.mul_assoc]
        _ = Y := by rw [haa, Matrix.one_mul, Matrix.mul_one]
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, e1, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, haa]
  rw [e]
  ext i k
  simp [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, hΦe]

end Core

section Applications
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {A : Arith E} {n p : ℕ} [Fact p.Prime]

/- English proof (translation)
Establish `key : ∀ u : Plc E, (p : 𝓞 E) ∈ u.asIdeal ↔ (p : 𝓞 (maximalRealSubfield E)) ∈ (u.under (𝓞 (maximalRealSubfield E))).asIdeal`. Introduce `u`. Use `show _ ↔ algebraMap _ (𝓞 E) (p : 𝓞 (maximalRealSubfield E)) ∈ u.asIdeal`. Simplify using the standard rewrite rules. Rewrite using `[key, key, GlobalTheory.LocInj.under_conjSrc]`.
-/
private theorem mem_conj_iff (p : ℕ) (w : Plc E) :
    (p : 𝓞 E) ∈ (conjSrc (conjE E) w).asIdeal ↔ (p : 𝓞 E) ∈ w.asIdeal := by
  have key : ∀ u : Plc E, (p : 𝓞 E) ∈ u.asIdeal ↔
      (p : 𝓞 (maximalRealSubfield E)) ∈ (u.under (𝓞 (maximalRealSubfield E))).asIdeal := by
    intro u
    show _ ↔ algebraMap _ (𝓞 E) (p : 𝓞 (maximalRealSubfield E)) ∈ u.asIdeal
    simp
  rw [key, key, GlobalTheory.LocInj.under_conjSrc]

/- English proof (translation)
The claim follows from `h.2`.
-/
private theorem mx_mem (S : Setup A n p) (h : S.G.GAf) :
    S.mx h * (starT (hermStar (A.H n) (A.det_ne n)) (AfP p) (S.mx h)).unop =
      ((uSimR (AfP p) h : (AfP p)ˣ) : AfP p) ⊗ₜ[ℚ] (1 : Matrix (Fin n) (Fin n) E) := h.2

/- English proof (translation)
The claim follows from `Units.mul_inv (h : (AfP p ⊗[ℚ] S.G.C)ˣ × (AfP p)ˣ).1`.
-/
private theorem mx_inv (S : Setup A n p) (h : S.G.GAf) : S.mx h * S.mx h⁻¹ = 1 :=
  Units.mul_inv (h : (AfP p ⊗[ℚ] S.G.C)ˣ × (AfP p)ˣ).1

/- English proof (translation)
The claim follows from `Units.inv_mul (h : (AfP p ⊗[ℚ] S.G.C)ˣ × (AfP p)ˣ).1`.
-/
private theorem mx_inv' (S : Setup A n p) (h : S.G.GAf) : S.mx h⁻¹ * S.mx h = 1 :=
  Units.inv_mul (h : (AfP p ⊗[ℚ] S.G.C)ˣ × (AfP p)ˣ).1

end Applications

end UpperTheory.Gal.W2.Seed

/- English proof (translation)
Introduce `hI hM E _ _ _ A n p _ S T μ hμ a ha h`. Take `⟨e, heQ, heE⟩` from `hI p E`. Establish `heeQ : e * e = e`. Use `RestrictedProduct.ext _ _ fun v => ?_` and prove the remaining obligations. Use `show e v * e v = e v`.

Distinguish the cases in `hv : (p : 𝓞 ℚ) ∈ v.asIdeal`. Rewrite using `[(heQ v).1 hv, one_mul]`. Rewrite using `[(heQ v).2 hv, zero_mul]`. Establish `hρe : T.ρ e = 0` using `(T.ker e).2 fun v hv => (heQ v).2 hv`. Establish `hkerQ : ∀ z, T.ρ z = 0 → (1 - e) * z = 0`.

Introduce `z hz`. Establish `hz'` using `(T.ker z).1 hz`. Use `RestrictedProduct.ext _ _ fun v => ?_` and prove the remaining obligations. Use `show (1 - e v) * z v = 0`. Distinguish the cases in `hv : (p : 𝓞 ℚ) ∈ v.asIdeal`.

Rewrite using `[(heQ v).1 hv, sub_self, zero_mul]`. Rewrite using `[hz' v hv, mul_zero]`. Take `⟨ε, hε⟩ : ∃ ε : Af E, ε = finiteAdeleMap ℚ E e` from `⟨_, rfl⟩`. Rewrite `heE` using `[← hε]`. Establish `heps : ε * ε = ε` using `by rw [hε, ← map_mul, heeQ]`.

Establish `hΦe : T.Φ ε = 0` using `by rw [hε, T.Φ_Q, hρe, TensorProduct.zero_tmul]`. Establish `hker : ∀ z, T.Φ z = 0 → (1 - ε) * z = 0`. Introduce `z hz`. Establish `hz'` using `(T.Φ_ker z).1 hz`. Use `GlobalTheory.EulerTw.pLoc_ext E fun w => ?_` and prove the remaining obligations.

Rewrite using `[map_mul, map_sub, map_one, map_zero]`. Distinguish the cases in `hw : (p : 𝓞 E) ∈ w.asIdeal`. Rewrite using `[(heE w).1 hw, sub_self, zero_mul]`. Rewrite using `[hz' w hw, mul_zero]`. Establish `hσe : conjFin (conjE E) ε = ε`.

Use `GlobalTheory.EulerTw.pLoc_ext E fun w => ?_` and prove the remaining obligations. Rewrite using `[pLoc_conjFin]`. Distinguish the cases in `hw : (p : 𝓞 E) ∈ w.asIdeal`. Rewrite using `[(heE _).1 ((mem_conj_iff p w).2 hw), (heE w).1 hw, map_one]`. Rewrite using `[(heE _).2 (mt (mem_conj_iff p w).1 hw), (heE w).2 hw, map_zero]`.

Take `⟨c, hc⟩ : ∃ c : (AfP p)ˣ, c = uSimR (AfP p) h` from `⟨_, rfl⟩`. Take `⟨s0, hs0⟩` from `T.surj (c : AfP p)`. Take `⟨s1, hs1⟩` from `T.surj ((c⁻¹ : (AfP p)ˣ) : AfP p)`. Take `⟨X, hXd⟩ : ∃ X, X = μ (S.mx h)` from `⟨_, rfl⟩`. Take `⟨X', hXd'⟩ : ∃ X', X' = μ (S.mx h⁻¹)` from `⟨_, rfl⟩`.

Take `⟨Xs, hXsd⟩ : ∃ Xs, Xs = μ (starT (hermStar (A.H n) (A.det_ne n)) (AfP p) (S.mx h)).unop` from `⟨_, rfl⟩`. Use `choose y hy using fun i k => T.Φ_surj (X i k)`. Use `choose y' hy' using fun i k => T.Φ_surj (X' i k)`. Take `⟨Y, hYd⟩ : ∃ Y : Matrix (Fin n) (Fin n) (Af E), Y = Matrix.of y` from `⟨_, rfl⟩`. Take `⟨Y', hYd'⟩ : ∃ Y' : Matrix (Fin n) (Fin n) (Af E), Y' = Matrix.of y'` from `⟨_, rfl⟩`.

Establish `hY : Y.map T.Φ = X`. Use extensionality with `i k`. Rewrite using `[hYd]`. Conclude with `hy i k`. Establish `hY' : Y'.map T.Φ = X'`.

Use extensionality with `i k`. Rewrite using `[hYd']`. Conclude with `hy' i k`. Establish `hXX : X * X' = 1` using `by rw [hXd, hXd', ← map_mul, mx_inv, map_one]`. Establish `hXX' : X' * X = 1` using `by rw [hXd, hXd', ← map_mul, mx_inv', map_one]`.

Establish `hXXs : X * Xs = ((c : AfP p) ⊗ₜ[ℚ] (1 : E)) • (1 : Matrix (Fin n) (Fin n) (AfP p ⊗[ℚ] E))`. Rewrite using `[hXd, hXsd, ← map_mul, mx_mem, ← hc]`. Use extensionality with `i k`. Rewrite using `[hμ]`. Break down `eq_or_ne i k with rfl | hik` into its components or cases.

Simplify using the standard rewrite rules. Simplify using `[Matrix.one_apply, hik]`. Establish `hXsX : Xs * X = ((c : AfP p) ⊗ₜ[ℚ] (1 : E)) • (1 : Matrix (Fin n) (Fin n) (AfP p ⊗[ℚ] E))`. Establish `h1 : Xs = ((c : AfP p) ⊗ₜ[ℚ] (1 : E)) • X'`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[h1, Matrix.smul_mul, hXX']`. Establish `hMS` using `hM (AfP p) E A n μ hμ (S.mx h)`. Rewrite `hMS` using `[← hXsd, ← hXd]`. Take `⟨D, hDd⟩ : ∃ D : Matrix (Fin n) (Fin n) (Af E), D = Matrix.diagonal (fun i => algebraMap E (Af E) (A.dg n i : E))` from `⟨_, rfl⟩`. Establish `hDT : D.map T.Φ = Matrix.diagonal (fun i => (1 : AfP p) ⊗ₜ[ℚ] (A.dg n i : E))`.

Rewrite using `[hDd, Matrix.diagonal_map (map_zero _)]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Conclude with `T.Φ_E _`. Establish `hΦt : T.Φ (finiteAdeleMap ℚ E s0) = (c : AfP p) ⊗ₜ[ℚ] (1 : E)` using `by rw [T.Φ_Q, hs0]`.

Establish `hX : ((Y.map T.Φ).map (conjT E (AfP p)))ᵀ * D.map T.Φ * Y.map T.Φ = T.Φ (finiteAdeleMap ℚ E s0) • D.map T.Φ`. Rewrite using `[hY, hDT, hΦt, ← hMS, mul_assoc, hXsX, Matrix.mul_smul, mul_one]`. Establish `hD : (a.val.map (conjFin (conjE E)))ᵀ * D * a.val = 1` using `by rw [hDd]; exact ha.1`. Establish `hA : a.val * (a⁻¹).val = 1` using `Units.mul_inv a`. Establish `hA' : (a⁻¹).val * a.val = 1` using `Units.inv_mul a`.

Establish `hGG` using `inv_part T.Φ heps hker hA hA' (Y := Y) (Y' := Y') (by rw [hY, hY', hXX])`. Establish `hGG'` using `inv_part T.Φ heps hker hA hA' (Y := Y') (Y' := Y) (by rw [hY, hY', hXX'])`. Establish `hStar` using `star_part T.Φ (conjFin (conjE E)) (conjT E (AfP p)) (t := finiteAdeleMap ℚ E s0) T.Φ_conj heps hσe hker hA hA' hD hX`. Establish `hConj` using `conj_part T.Φ hΦe hA hA' (Y := Y)`. Establish `h01 : (1 - e) * (s0 * s1 - 1) = 0` using `hkerQ _ (by rw [map_sub, map_mul, hs0, hs1, map_one, Units.mul_inv, sub_self])`.

Establish `hss : ((1 - e) * s0 + e) * ((1 - e) * s1 + e) = 1`. Take the linear combination `h01 + (s0 * s1 - s0 - s1 + 1) * heeQ`. Establish `hss' : ((1 - e) * s1 + e) * ((1 - e) * s0 + e) = 1` using `by rw [mul_comm]; exact hss`. Establish `hmem : (((⟨_, _, hGG, hGG'⟩ : GL (Fin n) (Af E)), (⟨_, _, hss, hss'⟩ : AfQˣ)) : GL (Fin n) (Af E) × AfQˣ) ∈ GUf E n`. Use `UpperTheory.Gal.CertificateRingHomMap.mem_Sim.2 ?_` and prove the remaining obligations.

Use `hStar.trans ?_` and prove the remaining obligations. Use `congr 1`. Simplify using `only [map_add, map_mul, map_sub, map_one, ← hε]`. Use `⟨⟨_, hmem⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hXd, ← hY]`.

Conclude with `hConj.symm`. Introduce `w hw`. Apply `Units.ext` to reduce the goal to its premises. Use `Matrix.ext fun i k => ?_` and prove the remaining obligations. Use `show pLoc E w (((1 - ε) • ((a⁻¹).val * Y * a.val) + ε • (1 : Matrix (Fin n) (Fin n) (Af E))) i k) = (1 : Matrix (Fin n) (Fin n) _) i k`.

Simplify using `only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul, map_sub, map_one, (heE w).1 hw, sub_self, zero_mul, zero_add, one_mul]`. Break down `eq_or_ne i k with rfl | hik` into its components or cases. Simplify using the standard rewrite rules. Simplify using `[Matrix.one_apply, hik]`.
-/
theorem UpperTheory.Gal.W2.Seed.pJSurj :
    IdemP → MuStar → JSurj := by
  intro hI hM E _ _ _ A n p _ S T μ hμ a ha h
  obtain ⟨e, heQ, heE⟩ := hI p E
  have heeQ : e * e = e := by
    refine RestrictedProduct.ext _ _ fun v => ?_
    show e v * e v = e v
    by_cases hv : (p : 𝓞 ℚ) ∈ v.asIdeal
    · rw [(heQ v).1 hv, one_mul]
    · rw [(heQ v).2 hv, zero_mul]
  have hρe : T.ρ e = 0 := (T.ker e).2 fun v hv => (heQ v).2 hv
  have hkerQ : ∀ z, T.ρ z = 0 → (1 - e) * z = 0 := by
    intro z hz
    have hz' := (T.ker z).1 hz
    refine RestrictedProduct.ext _ _ fun v => ?_
    show (1 - e v) * z v = 0
    by_cases hv : (p : 𝓞 ℚ) ∈ v.asIdeal
    · rw [(heQ v).1 hv, sub_self, zero_mul]
    · rw [hz' v hv, mul_zero]
  obtain ⟨ε, hε⟩ : ∃ ε : Af E, ε = finiteAdeleMap ℚ E e := ⟨_, rfl⟩
  rw [← hε] at heE
  have heps : ε * ε = ε := by rw [hε, ← map_mul, heeQ]
  have hΦe : T.Φ ε = 0 := by rw [hε, T.Φ_Q, hρe, TensorProduct.zero_tmul]
  have hker : ∀ z, T.Φ z = 0 → (1 - ε) * z = 0 := by
    intro z hz
    have hz' := (T.Φ_ker z).1 hz
    refine GlobalTheory.EulerTw.pLoc_ext E fun w => ?_
    rw [map_mul, map_sub, map_one, map_zero]
    by_cases hw : (p : 𝓞 E) ∈ w.asIdeal
    · rw [(heE w).1 hw, sub_self, zero_mul]
    · rw [hz' w hw, mul_zero]
  have hσe : conjFin (conjE E) ε = ε := by
    refine GlobalTheory.EulerTw.pLoc_ext E fun w => ?_
    rw [pLoc_conjFin]
    by_cases hw : (p : 𝓞 E) ∈ w.asIdeal
    · rw [(heE _).1 ((mem_conj_iff p w).2 hw), (heE w).1 hw, map_one]
    · rw [(heE _).2 (mt (mem_conj_iff p w).1 hw), (heE w).2 hw, map_zero]
  obtain ⟨c, hc⟩ : ∃ c : (AfP p)ˣ, c = uSimR (AfP p) h := ⟨_, rfl⟩
  obtain ⟨s0, hs0⟩ := T.surj (c : AfP p)
  obtain ⟨s1, hs1⟩ := T.surj ((c⁻¹ : (AfP p)ˣ) : AfP p)
  obtain ⟨X, hXd⟩ : ∃ X, X = μ (S.mx h) := ⟨_, rfl⟩
  obtain ⟨X', hXd'⟩ : ∃ X', X' = μ (S.mx h⁻¹) := ⟨_, rfl⟩
  obtain ⟨Xs, hXsd⟩ : ∃ Xs, Xs = μ (starT (hermStar (A.H n) (A.det_ne n)) (AfP p) (S.mx h)).unop := ⟨_, rfl⟩
  choose y hy using fun i k => T.Φ_surj (X i k)
  choose y' hy' using fun i k => T.Φ_surj (X' i k)
  obtain ⟨Y, hYd⟩ : ∃ Y : Matrix (Fin n) (Fin n) (Af E), Y = Matrix.of y := ⟨_, rfl⟩
  obtain ⟨Y', hYd'⟩ : ∃ Y' : Matrix (Fin n) (Fin n) (Af E), Y' = Matrix.of y' := ⟨_, rfl⟩
  have hY : Y.map T.Φ = X := by
    ext i k
    rw [hYd]
    exact hy i k
  have hY' : Y'.map T.Φ = X' := by
    ext i k
    rw [hYd']
    exact hy' i k
  have hXX : X * X' = 1 := by rw [hXd, hXd', ← map_mul, mx_inv, map_one]
  have hXX' : X' * X = 1 := by rw [hXd, hXd', ← map_mul, mx_inv', map_one]
  have hXXs : X * Xs = ((c : AfP p) ⊗ₜ[ℚ] (1 : E)) • (1 : Matrix (Fin n) (Fin n) (AfP p ⊗[ℚ] E)) := by
    rw [hXd, hXsd, ← map_mul, mx_mem, ← hc]
    ext i k
    rw [hμ]
    rcases eq_or_ne i k with rfl | hik
    · simp
    · simp [Matrix.one_apply, hik]
  have hXsX : Xs * X = ((c : AfP p) ⊗ₜ[ℚ] (1 : E)) • (1 : Matrix (Fin n) (Fin n) (AfP p ⊗[ℚ] E)) := by
    have h1 : Xs = ((c : AfP p) ⊗ₜ[ℚ] (1 : E)) • X' := by
      calc Xs = (X' * X) * Xs := by rw [hXX', one_mul]
        _ = X' * (X * Xs) := mul_assoc _ _ _
        _ = _ := by rw [hXXs, Matrix.mul_smul, mul_one]
    rw [h1, Matrix.smul_mul, hXX']
  have hMS := hM (AfP p) E A n μ hμ (S.mx h)
  rw [← hXsd, ← hXd] at hMS
  obtain ⟨D, hDd⟩ : ∃ D : Matrix (Fin n) (Fin n) (Af E), D = Matrix.diagonal (fun i => algebraMap E (Af E) (A.dg n i : E)) := ⟨_, rfl⟩
  have hDT : D.map T.Φ = Matrix.diagonal (fun i => (1 : AfP p) ⊗ₜ[ℚ] (A.dg n i : E)) := by
    rw [hDd, Matrix.diagonal_map (map_zero _)]
    congr 1
    funext i
    exact T.Φ_E _
  have hΦt : T.Φ (finiteAdeleMap ℚ E s0) = (c : AfP p) ⊗ₜ[ℚ] (1 : E) := by rw [T.Φ_Q, hs0]
  have hX : ((Y.map T.Φ).map (conjT E (AfP p)))ᵀ * D.map T.Φ * Y.map T.Φ =
      T.Φ (finiteAdeleMap ℚ E s0) • D.map T.Φ := by
    rw [hY, hDT, hΦt, ← hMS, mul_assoc, hXsX, Matrix.mul_smul, mul_one]
  have hD : (a.val.map (conjFin (conjE E)))ᵀ * D * a.val = 1 := by rw [hDd]; exact ha.1
  have hA : a.val * (a⁻¹).val = 1 := Units.mul_inv a
  have hA' : (a⁻¹).val * a.val = 1 := Units.inv_mul a
  have hGG := inv_part T.Φ heps hker hA hA' (Y := Y) (Y' := Y') (by rw [hY, hY', hXX])
  have hGG' := inv_part T.Φ heps hker hA hA' (Y := Y') (Y' := Y) (by rw [hY, hY', hXX'])
  have hStar := star_part T.Φ (conjFin (conjE E)) (conjT E (AfP p)) (t := finiteAdeleMap ℚ E s0) T.Φ_conj heps hσe hker hA hA' hD hX
  have hConj := conj_part T.Φ hΦe hA hA' (Y := Y)
  have h01 : (1 - e) * (s0 * s1 - 1) = 0 := hkerQ _ (by rw [map_sub, map_mul, hs0, hs1, map_one, Units.mul_inv, sub_self])
  have hss : ((1 - e) * s0 + e) * ((1 - e) * s1 + e) = 1 := by
    linear_combination h01 + (s0 * s1 - s0 - s1 + 1) * heeQ
  have hss' : ((1 - e) * s1 + e) * ((1 - e) * s0 + e) = 1 := by rw [mul_comm]; exact hss
  have hmem : (((⟨_, _, hGG, hGG'⟩ : GL (Fin n) (Af E)), (⟨_, _, hss, hss'⟩ : AfQˣ)) : GL (Fin n) (Af E) × AfQˣ) ∈ GUf E n := by
    refine UpperTheory.Gal.CertificateRingHomMap.mem_Sim.2 ?_
    refine hStar.trans ?_
    congr 1
    simp only [map_add, map_mul, map_sub, map_one, ← hε]
  refine ⟨⟨_, hmem⟩, ?_, ?_⟩
  · rw [← hXd, ← hY]
    exact hConj.symm
  · intro w hw
    apply Units.ext
    refine Matrix.ext fun i k => ?_
    show pLoc E w (((1 - ε) • ((a⁻¹).val * Y * a.val) + ε • (1 : Matrix (Fin n) (Fin n) (Af E))) i k) = (1 : Matrix (Fin n) (Fin n) _) i k
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul, map_sub, map_one, (heE w).1 hw, sub_self, zero_mul,
      zero_add, one_mul]
    rcases eq_or_ne i k with rfl | hik
    · simp
    · simp [Matrix.one_apply, hik]
