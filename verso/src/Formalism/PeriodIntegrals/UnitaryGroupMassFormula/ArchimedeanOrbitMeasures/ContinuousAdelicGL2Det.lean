import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.CayDensExCayH

noncomputable section

namespace HcInf

open HcS.BasicNotions Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal

section Chart

variable {P Q : ℕ}

local notation "Mat" => Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ

/- English proof (translation)
Establish `h4 : (G + 1) * ((1 + 1) - Y) = (4 : ℂ) • (1 : Mat)`. Rewrite using `[add_mul, h, one_mul, show (4 : ℂ) = 1 + 1 + 1 + 1 by norm_num, add_smul, add_smul, add_smul, one_smul]`. Normalize the expressions using the abelian group laws. Establish `hd` using `congrArg Matrix.det h4`. Rewrite `hd` using `[Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one]`.

Establish `h4ne : IsUnit ((4 : ℂ) ^ Fintype.card (Fin P ⊕ Fin Q))` using `isUnit_iff_ne_zero.2 (pow_ne_zero _ (by norm_num))`. Rewrite `h4ne` using `[← hd]`. Conclude with `⟨h4, isUnit_of_mul_isUnit_left h4ne, isUnit_of_mul_isUnit_right h4ne⟩`.
-/
theorem chart_units (G Y : Mat) (h : G * ((1 + 1) - Y) = (1 + 1) + Y) :
    (G + 1) * ((1 + 1) - Y) = (4 : ℂ) • (1 : Mat) ∧ IsUnit (G + 1).det ∧
      IsUnit ((1 + 1) - Y).det := by
  have h4 : (G + 1) * ((1 + 1) - Y) = (4 : ℂ) • (1 : Mat) := by
    rw [add_mul, h, one_mul, show (4 : ℂ) = 1 + 1 + 1 + 1 by norm_num, add_smul, add_smul, add_smul,
      one_smul]
    abel
  have hd := congrArg Matrix.det h4
  rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one] at hd
  have h4ne : IsUnit ((4 : ℂ) ^ Fintype.card (Fin P ⊕ Fin Q)) :=
    isUnit_iff_ne_zero.2 (pow_ne_zero _ (by norm_num))
  rw [← hd] at h4ne
  exact ⟨h4, isUnit_of_mul_isUnit_left h4ne, isUnit_of_mul_isUnit_right h4ne⟩

/- English proof (translation)
Use `set Y : Mat := ((X : lieU P Q) : Mat) with hY`. Establish `hXm : Yᴴ * HcS.UG.Jpq P Q + HcS.UG.Jpq P Q * Y = 0` using `X.2`. Establish `hB : IsUnit ((1 + 1) - Y).det` using `hX`. Establish `hBH : IsUnit ((1 + 1) - Y)ᴴ.det`. Rewrite using `[Matrix.det_conjTranspose]`.

Conclude with `hB.star`. Establish `hJY : Yᴴ * HcS.UG.Jpq P Q = -(HcS.UG.Jpq P Q * Y)` using `eq_neg_of_add_eq_zero_left hXm`. Establish `h1 : ((1 + 1) + Y)ᴴ * HcS.UG.Jpq P Q = HcS.UG.Jpq P Q * ((1 + 1) - Y)`. Rewrite using `[Matrix.conjTranspose_add, Matrix.conjTranspose_add, Matrix.conjTranspose_one, add_mul, add_mul, hJY, mul_sub, mul_add]`. Use `noncomm_ring`.

Establish `h2 : HcS.UG.Jpq P Q * ((1 + 1) + Y) = ((1 + 1) - Y)ᴴ * HcS.UG.Jpq P Q`. Rewrite using `[Matrix.conjTranspose_sub, Matrix.conjTranspose_add, Matrix.conjTranspose_one, sub_mul, add_mul, hJY, mul_add]`. Use `noncomm_ring`. Establish `hcomm : ((1 + 1) - Y) * ((1 + 1) + Y) = ((1 + 1) + Y) * ((1 + 1) - Y)` using `by noncomm_ring`. Take `⟨G, hG⟩ : ∃ G : Mat, G = ((1 + 1) + Y) * ((1 + 1) - Y)⁻¹` from `⟨_, rfl⟩`.

Establish `hU : Gᴴ * HcS.UG.Jpq P Q * G = HcS.UG.Jpq P Q`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hG, Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = (((1 + 1) - Y)ᴴ)⁻¹ * HcS.UG.Jpq P Q * (((1 + 1) - Y) * ((1 + 1) + Y)) * ((1 + 1) - Y)⁻¹ := by`.

Rewrite using `[h1]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = (((1 + 1) - Y)ᴴ)⁻¹ * (HcS.UG.Jpq P Q * ((1 + 1) + Y)) * (((1 + 1) - Y) * ((1 + 1) - Y)⁻¹) := by`. Rewrite using `[hcomm]`. Simplify using `only [Matrix.mul_assoc]`.

Use `_ = HcS.UG.Jpq P Q := by`. Rewrite using `[h2, Matrix.mul_nonsing_inv _ hB, Matrix.mul_one, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hBH, Matrix.one_mul]`. Establish `hJ : IsUnit (HcS.UG.Jpq P Q).det`. Rewrite using `[HcS.UG.Jpq, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, Matrix.det_neg, Matrix.det_one, one_mul, mul_one]`. Conclude with `IsUnit.pow _ isUnit_neg_one`.

Establish `hGd : IsUnit G.det`. Rewrite using `[isUnit_iff_ne_zero]`. Introduce `h0`. Establish `hd` using `congrArg Matrix.det hU`. Rewrite `hd` using `[Matrix.det_mul, Matrix.det_mul, h0, mul_zero]`.

Conclude with `hJ.ne_zero hd.symm`. Establish `hcT : HcS.UG.cT (starRingEnd ℂ) G = Gᴴ`. Use extensionality with `i j`. Simplify using `[HcS.UG.cT, Matrix.conjTranspose_apply]`. Use `⟨(⟨Matrix.nonsingInvUnit G hGd, ?_⟩ : HcS.UG.Upq P Q), ?_⟩` and prove the remaining obligations.

Use `show HcS.UG.cT (starRingEnd ℂ) G * HcS.UG.Jpq P Q * G = HcS.UG.Jpq P Q`. Rewrite using `[hcT, hU]`. Use `show G * ((1 + 1) - Y) = (1 + 1) + Y`. Rewrite using `[hG, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hB, Matrix.mul_one]`.
-/
theorem cay_exists (X : lieU P Q) (hX : X ∈ D0 P Q) :
    ∃ g : UpqT P Q, UpqT.mat g * ((1 + 1) - ((X : lieU P Q) : Mat)) = (1 + 1) + ((X : lieU P Q) : Mat) := by
  set Y : Mat := ((X : lieU P Q) : Mat) with hY
  have hXm : Yᴴ * HcS.UG.Jpq P Q + HcS.UG.Jpq P Q * Y = 0 := X.2
  have hB : IsUnit ((1 + 1) - Y).det := hX
  have hBH : IsUnit ((1 + 1) - Y)ᴴ.det := by
    rw [Matrix.det_conjTranspose]
    exact hB.star
  have hJY : Yᴴ * HcS.UG.Jpq P Q = -(HcS.UG.Jpq P Q * Y) := eq_neg_of_add_eq_zero_left hXm
  have h1 : ((1 + 1) + Y)ᴴ * HcS.UG.Jpq P Q = HcS.UG.Jpq P Q * ((1 + 1) - Y) := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_add, Matrix.conjTranspose_one, add_mul,
      add_mul, hJY, mul_sub, mul_add]
    noncomm_ring
  have h2 : HcS.UG.Jpq P Q * ((1 + 1) + Y) = ((1 + 1) - Y)ᴴ * HcS.UG.Jpq P Q := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_add, Matrix.conjTranspose_one, sub_mul,
      add_mul, hJY, mul_add]
    noncomm_ring
  have hcomm : ((1 + 1) - Y) * ((1 + 1) + Y) = ((1 + 1) + Y) * ((1 + 1) - Y) := by noncomm_ring
  obtain ⟨G, hG⟩ : ∃ G : Mat, G = ((1 + 1) + Y) * ((1 + 1) - Y)⁻¹ := ⟨_, rfl⟩
  have hU : Gᴴ * HcS.UG.Jpq P Q * G = HcS.UG.Jpq P Q := by
    calc Gᴴ * HcS.UG.Jpq P Q * G
        = (((1 + 1) - Y)ᴴ)⁻¹ * ((((1 + 1) + Y)ᴴ * HcS.UG.Jpq P Q) * ((1 + 1) + Y)) *
            ((1 + 1) - Y)⁻¹ := by
          rw [hG, Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv]
          simp only [Matrix.mul_assoc]
      _ = (((1 + 1) - Y)ᴴ)⁻¹ * HcS.UG.Jpq P Q * (((1 + 1) - Y) * ((1 + 1) + Y)) *
            ((1 + 1) - Y)⁻¹ := by
          rw [h1]
          simp only [Matrix.mul_assoc]
      _ = (((1 + 1) - Y)ᴴ)⁻¹ * (HcS.UG.Jpq P Q * ((1 + 1) + Y)) *
            (((1 + 1) - Y) * ((1 + 1) - Y)⁻¹) := by
          rw [hcomm]
          simp only [Matrix.mul_assoc]
      _ = HcS.UG.Jpq P Q := by
          rw [h2, Matrix.mul_nonsing_inv _ hB, Matrix.mul_one, ← Matrix.mul_assoc,
            Matrix.nonsing_inv_mul _ hBH, Matrix.one_mul]
  have hJ : IsUnit (HcS.UG.Jpq P Q).det := by
    rw [HcS.UG.Jpq, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, Matrix.det_neg, Matrix.det_one,
      one_mul, mul_one]
    exact IsUnit.pow _ isUnit_neg_one
  have hGd : IsUnit G.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    have hd := congrArg Matrix.det hU
    rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at hd
    exact hJ.ne_zero hd.symm
  have hcT : HcS.UG.cT (starRingEnd ℂ) G = Gᴴ := by
    ext i j
    simp [HcS.UG.cT, Matrix.conjTranspose_apply]
  refine ⟨(⟨Matrix.nonsingInvUnit G hGd, ?_⟩ : HcS.UG.Upq P Q), ?_⟩
  · show HcS.UG.cT (starRingEnd ℂ) G * HcS.UG.Jpq P Q * G = HcS.UG.Jpq P Q
    rw [hcT, hU]
  · show G * ((1 + 1) - Y) = (1 + 1) + Y
    rw [hG, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hB, Matrix.mul_one]

/- English proof (translation)
Establish `hex` using `cay_exists X hX`. Unfold `cayF`. Rewrite using `[dif_pos hex]`. Conclude with `Classical.choose_spec hex`.
-/
theorem cayF_spec (X : lieU P Q) (hX : X ∈ D0 P Q) :
    UpqT.mat (cayF P Q X) * ((1 + 1) - ((X : lieU P Q) : Mat)) = (1 + 1) + ((X : lieU P Q) : Mat) := by
  have hex := cay_exists X hX
  unfold cayF
  rw [dif_pos hex]
  exact Classical.choose_spec hex

/- English proof (translation)
Conclude with `(chart_units _ _ h).2.2`.
-/
theorem mem_cayley_domain_of (g : UpqT P Q) (X : lieU P Q)
    (h : UpqT.mat g * ((1 + 1) - ((X : lieU P Q) : Mat)) = (1 + 1) + ((X : lieU P Q) : Mat)) :
    X ∈ D0 P Q := by
  exact (chart_units _ _ h).2.2

/- English proof (translation)
The claim follows from `Subtype.ext (Units.ext e)`.
-/
private theorem upqT_eq_of_mat_eq {g h : UpqT P Q} (e : UpqT.mat g = UpqT.mat h) : g = h :=
  Subtype.ext (Units.ext e)

/- English proof (translation)
Establish `hX` using `mem_cayley_domain_of g X h`. Establish `hB : IsUnit ((1 + 1) - ((X : lieU P Q) : Mat)).det` using `hX`. Establish `he` using `(cayF_spec X hX).trans h.symm`. Apply `upqT_eq_of_mat_eq` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hB, Matrix.mul_one]`. Use `_ = UpqT.mat g * ((1 + 1) - ((X : lieU P Q) : Mat)) * ((1 + 1) - ((X : lieU P Q) : Mat))⁻¹ := by`. Rewrite using `[he]`. Use `_ = UpqT.mat g := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hB, Matrix.mul_one]`.
-/
theorem cayF_eq_of (g : UpqT P Q) (X : lieU P Q)
    (h : UpqT.mat g * ((1 + 1) - ((X : lieU P Q) : Mat)) = (1 + 1) + ((X : lieU P Q) : Mat)) :
    cayF P Q X = g := by
  have hX := mem_cayley_domain_of g X h
  have hB : IsUnit ((1 + 1) - ((X : lieU P Q) : Mat)).det := hX
  have he := (cayF_spec X hX).trans h.symm
  apply upqT_eq_of_mat_eq
  calc UpqT.mat (cayF P Q X)
      = UpqT.mat (cayF P Q X) * ((1 + 1) - ((X : lieU P Q) : Mat)) *
          ((1 + 1) - ((X : lieU P Q) : Mat))⁻¹ := by
        rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hB, Matrix.mul_one]
    _ = UpqT.mat g * ((1 + 1) - ((X : lieU P Q) : Mat)) * ((1 + 1) - ((X : lieU P Q) : Mat))⁻¹ := by
        rw [he]
    _ = UpqT.mat g := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hB, Matrix.mul_one]

/- English proof (translation)
Establish `hB : IsUnit ((1 + 1) - ((X : lieU P Q) : Mat)).det` using `hX`. Rewrite using `[← cayF_spec X hX, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hB, Matrix.mul_one]`.
-/
theorem cayF_mat (X : lieU P Q) (hX : X ∈ D0 P Q) :
    UpqT.mat (cayF P Q X) = ((1 + 1) + ((X : lieU P Q) : Mat)) * ((1 + 1) - ((X : lieU P Q) : Mat))⁻¹ := by
  have hB : IsUnit ((1 + 1) - ((X : lieU P Q) : Mat)).det := hX
  rw [← cayF_spec X hX, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hB, Matrix.mul_one]

/- English proof (translation)
Rewrite using `[cayInv_eq]`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show (1 + 1) * (UpqT.mat (cayF P Q X) + 1)⁻¹ * (UpqT.mat (cayF P Q X) - 1) = ((X : lieU P Q) : Mat)`. Establish `hs` using `cayF_spec X hX`. Use `set Y : Mat := ((X : lieU P Q) : Mat)`.

Use `set G := UpqT.mat (cayF P Q X)`. Take `⟨h4, -, hB⟩` from `chart_units G Y hs`. Establish `hinv : (G + 1)⁻¹ = (4 : ℂ)⁻¹ • ((1 + 1) - Y)`. Apply `Matrix.inv_eq_right_inv` to reduce the goal to its premises. Rewrite using `[Matrix.mul_smul, h4, smul_smul, inv_mul_cancel₀ (by norm_num), one_smul]`.

Establish `hGm : (G - 1) * ((1 + 1) - Y) = Y + Y`. Rewrite using `[sub_mul, hs, one_mul]`. Normalize the expressions using the abelian group laws. Establish `hG1 : G - 1 = (Y + Y) * ((1 + 1) - Y)⁻¹`. Rewrite using `[← hGm, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hB, Matrix.mul_one]`.

Establish `hc : ((1 + 1) - Y) * (Y + Y) = (Y + Y) * ((1 + 1) - Y)` using `by noncomm_ring`. Establish `h4Y : (1 + 1 : Mat) * (Y + Y) = (4 : ℂ) • Y`. Rewrite using `[show (4 : ℂ) = 1 + 1 + 1 + 1 by norm_num, add_smul, add_smul, add_smul, one_smul]`. Use `noncomm_ring`. Rewrite using `[hinv, hG1]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_smul, Matrix.smul_mul]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = (4 : ℂ)⁻¹ • ((1 + 1) * (Y + Y)) := by`. Rewrite using `[hc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hB, Matrix.mul_one]`.

Use `_ = Y := by`. Rewrite using `[h4Y, smul_smul, inv_mul_cancel₀ (by norm_num), one_smul]`.
-/
theorem cayInv_cayF (X : lieU P Q) (hX : X ∈ D0 P Q) : cayInv P Q (cayF P Q X) = X := by
  rw [cayInv_eq]
  apply Subtype.ext
  show (1 + 1) * (UpqT.mat (cayF P Q X) + 1)⁻¹ * (UpqT.mat (cayF P Q X) - 1) =
    ((X : lieU P Q) : Mat)
  have hs := cayF_spec X hX
  set Y : Mat := ((X : lieU P Q) : Mat)
  set G := UpqT.mat (cayF P Q X)
  obtain ⟨h4, -, hB⟩ := chart_units G Y hs
  have hinv : (G + 1)⁻¹ = (4 : ℂ)⁻¹ • ((1 + 1) - Y) := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.mul_smul, h4, smul_smul, inv_mul_cancel₀ (by norm_num), one_smul]
  have hGm : (G - 1) * ((1 + 1) - Y) = Y + Y := by
    rw [sub_mul, hs, one_mul]
    abel
  have hG1 : G - 1 = (Y + Y) * ((1 + 1) - Y)⁻¹ := by
    rw [← hGm, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hB, Matrix.mul_one]
  have hc : ((1 + 1) - Y) * (Y + Y) = (Y + Y) * ((1 + 1) - Y) := by noncomm_ring
  have h4Y : (1 + 1 : Mat) * (Y + Y) = (4 : ℂ) • Y := by
    rw [show (4 : ℂ) = 1 + 1 + 1 + 1 by norm_num, add_smul, add_smul, add_smul, one_smul]
    noncomm_ring
  rw [hinv, hG1]
  calc (1 + 1) * ((4 : ℂ)⁻¹ • ((1 + 1) - Y)) * ((Y + Y) * ((1 + 1) - Y)⁻¹)
      = (4 : ℂ)⁻¹ • ((1 + 1) * ((((1 + 1) - Y) * (Y + Y)) * ((1 + 1) - Y)⁻¹)) := by
        rw [Matrix.mul_smul, Matrix.smul_mul]
        simp only [Matrix.mul_assoc]
    _ = (4 : ℂ)⁻¹ • ((1 + 1) * (Y + Y)) := by
        rw [hc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hB, Matrix.mul_one]
    _ = Y := by
        rw [h4Y, smul_smul, inv_mul_cancel₀ (by norm_num), one_smul]

/- English proof (translation)
Rewrite using `[cayInv_eq]`. Use `show UpqT.mat g * ((1 + 1) - cayCand P Q g) = (1 + 1) + cayCand P Q g`. Unfold `cayCand`. Use `set G := UpqT.mat g`. Use `set A := (G + 1)⁻¹`.

Establish `hAG : A * G = 1 - A`. Establish `h` using `Matrix.nonsing_inv_mul _ hu`. Rewrite `h` using `[mul_add, mul_one]`. Rewrite using `[← h]`. Normalize the expressions using the abelian group laws.

Establish `hGA : G * A = 1 - A`. Establish `h` using `Matrix.mul_nonsing_inv _ hu`. Rewrite `h` using `[add_mul, one_mul]`. Rewrite using `[← h]`. Normalize the expressions using the abelian group laws.

Establish `e1 : (1 + 1) * A * (G - 1) = (1 + 1) - (1 + 1) * A - (1 + 1) * A`. Rewrite using `[Matrix.mul_assoc, mul_sub, hAG]`. Use `noncomm_ring`. Rewrite using `[e1]`. Establish `e2 : G * ((1 + 1) - ((1 + 1) - (1 + 1) * A - (1 + 1) * A)) = G * A + G * A + G * A + G * A` using `by noncomm_ring`.

Rewrite using `[e2, hGA]`. Use `noncomm_ring`.
-/
theorem cayInv_rel (g : UpqT P Q) (hu : IsUnit (UpqT.mat g + 1).det) :
    UpqT.mat g * ((1 + 1) - ((cayInv P Q g : lieU P Q) : Mat)) = (1 + 1) + ((cayInv P Q g : lieU P Q) : Mat) := by
  rw [cayInv_eq]
  show UpqT.mat g * ((1 + 1) - cayCand P Q g) = (1 + 1) + cayCand P Q g
  unfold cayCand
  set G := UpqT.mat g
  set A := (G + 1)⁻¹
  have hAG : A * G = 1 - A := by
    have h := Matrix.nonsing_inv_mul _ hu
    rw [mul_add, mul_one] at h
    rw [← h]
    abel
  have hGA : G * A = 1 - A := by
    have h := Matrix.mul_nonsing_inv _ hu
    rw [add_mul, one_mul] at h
    rw [← h]
    abel
  have e1 : (1 + 1) * A * (G - 1) = (1 + 1) - (1 + 1) * A - (1 + 1) * A := by
    rw [Matrix.mul_assoc, mul_sub, hAG]
    noncomm_ring
  rw [e1]
  have e2 : G * ((1 + 1) - ((1 + 1) - (1 + 1) * A - (1 + 1) * A)) = G * A + G * A + G * A + G * A := by
    noncomm_ring
  rw [e2, hGA]
  noncomm_ring

/- English proof (translation)
Use extensionality with `g`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨X, -, h⟩`. Conclude with `(chart_units _ _ h).2.1`. Introduce `hu`.

Conclude with `⟨cayInv P Q g, mem_cayley_domain_of g _ (cayInv_rel g hu), cayInv_rel g hu⟩`.
-/
theorem cayley_domain_eq : cayS (D0 P Q) = {g : UpqT P Q | IsUnit (UpqT.mat g + 1).det} := by
  ext g
  constructor
  · rintro ⟨X, -, h⟩
    exact (chart_units _ _ h).2.1
  · intro hu
    exact ⟨cayInv P Q g, mem_cayley_domain_of g _ (cayInv_rel g hu), cayInv_rel g hu⟩

/- English proof (translation)
Unfold `UpqT.mat`. Conclude with `Units.continuous_val.comp continuous_subtype_val`.
-/
theorem continuous_mat : Continuous (UpqT.mat (P := P) (Q := Q)) := by
  unfold UpqT.mat
  exact Units.continuous_val.comp continuous_subtype_val

/- English proof (translation)
Rewrite using `[cayley_domain_eq]`. Establish `h : {g : UpqT P Q | IsUnit (UpqT.mat g + 1).det} = (fun g => (UpqT.mat g + 1).det) ⁻¹' {0}ᶜ`. Use extensionality with `g`. Simplify using `[isUnit_iff_ne_zero]`. Rewrite using `[h]`.

Conclude with `isOpen_compl_singleton.preimage ((continuous_mat.add continuous_const).matrix_det)`.
-/
theorem isOpen_cayley_domain : IsOpen (cayS (D0 P Q)) := by
  rw [cayley_domain_eq]
  have h : {g : UpqT P Q | IsUnit (UpqT.mat g + 1).det} =
      (fun g => (UpqT.mat g + 1).det) ⁻¹' {0}ᶜ := by
    ext g
    simp [isUnit_iff_ne_zero]
  rw [h]
  exact isOpen_compl_singleton.preimage ((continuous_mat.add continuous_const).matrix_det)

/- English proof (translation)
Conclude with `(continuous_const.sub continuous_subtype_val).matrix_det`.
-/
theorem continuous_adelicGL2_det : Continuous fun X : lieU P Q => ((1 + 1) - ((X : lieU P Q) : Mat)).det := by
  exact (continuous_const.sub continuous_subtype_val).matrix_det

/- English proof (translation)
Establish `h : D0 P Q = (fun X : lieU P Q => ((1 + 1) - ((X : lieU P Q) : Mat)).det) ⁻¹' {0}ᶜ`. Use extensionality with `X`. Simplify using `[D0, isUnit_iff_ne_zero]`. Rewrite using `[h]`. Conclude with `isOpen_compl_singleton.preimage continuous_adelicGL2_det`.
-/
theorem isOpen_cell_domain : IsOpen (D0 P Q) := by
  have h : D0 P Q = (fun X : lieU P Q => ((1 + 1) - ((X : lieU P Q) : Mat)).det) ⁻¹' {0}ᶜ := by
    ext X
    simp [D0, isUnit_iff_ne_zero]
  rw [h]
  exact isOpen_compl_singleton.preimage continuous_adelicGL2_det

/- English proof (translation)
Use `show IsUnit ((1 + 1) - ((0 : lieU P Q) : Mat)).det`. Rewrite using `[show ((0 : lieU P Q) : Mat) = 0 from rfl, sub_zero, show (1 + 1 : Mat) = (2 : ℂ) • 1 by rw [two_smul], Matrix.det_smul, Matrix.det_one, mul_one]`. Conclude with `isUnit_iff_ne_zero.2 (pow_ne_zero _ two_ne_zero)`.
-/
theorem zero_mem_cayley_domain : (0 : lieU P Q) ∈ D0 P Q := by
  show IsUnit ((1 + 1) - ((0 : lieU P Q) : Mat)).det
  rw [show ((0 : lieU P Q) : Mat) = 0 from rfl, sub_zero,
    show (1 + 1 : Mat) = (2 : ℂ) • 1 by rw [two_smul], Matrix.det_smul, Matrix.det_one, mul_one]
  exact isUnit_iff_ne_zero.2 (pow_ne_zero _ two_ne_zero)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mat_one : UpqT.mat (1 : UpqT P Q) = 1 := rfl

/- English proof (translation)
Conclude with `cayF_eq_of 1 0 (by`. Rewrite using `[mat_one, show ((0 : lieU P Q) : Mat) = 0 from rfl, Matrix.one_mul, sub_zero, add_zero])`.
-/
theorem cayF_zero : cayF P Q 0 = 1 := by
  exact cayF_eq_of 1 0 (by
    rw [mat_one, show ((0 : lieU P Q) : Mat) = 0 from rfl, Matrix.one_mul, sub_zero, add_zero])

/- English proof (translation)
Unfold `cayF`. Rewrite using `[dif_neg]`. Introduce and unpack `⟨g, hg⟩`. Conclude with `hX (mem_cayley_domain_of g X hg)`.
-/
theorem cayF_off (X : lieU P Q) (hX : X ∉ D0 P Q) : cayF P Q X = 1 := by
  unfold cayF
  rw [dif_neg]
  rintro ⟨g, hg⟩
  exact hX (mem_cayley_domain_of g X hg)

/- English proof (translation)
Simplify using `only [Matrix.inv_def, Ring.inverse_eq_inv]`. Conclude with `(hf.matrix_det.inv₀ hd).smul hf.matrix_adjugate`.
-/
private theorem continuous_inv_of_det_ne_zero {α : Type*} [TopologicalSpace α] {f : α → Mat}
    (hf : Continuous f) (hd : ∀ x, (f x).det ≠ 0) : Continuous fun x => (f x)⁻¹ := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv]
  exact (hf.matrix_det.inv₀ hd).smul hf.matrix_adjugate

/- English proof (translation)
Rewrite using `[continuousOn_iff_continuous_restrict]`. Establish `hval : Continuous fun x : D0 P Q => UpqT.mat (cayF P Q x)`. Establish `h : (fun x : D0 P Q => UpqT.mat (cayF P Q x)) = fun x : D0 P Q => ((1 + 1) + ((x.1 : lieU P Q) : Mat)) * ((1 + 1) - ((x.1 : lieU P Q) : Mat))⁻¹`. Use function extensionality and compare the values at `fun x => cayF_mat x.1 x.2`. Rewrite using `[h]`.

Conclude with `(continuous_const.add (continuous_subtype_val.comp continuous_subtype_val)).mul (continuous_inv_of_det_ne_zero (continuous_const.sub (continuous_subtype_val.comp continuous_subtype_val)) fun x => isUnit_iff_ne_zero.1 x.2)`. Establish `hinv : Continuous fun x : D0 P Q => (UpqT.mat (cayF P Q x))⁻¹` using `continuous_inv_of_det_ne_zero hval fun x => (Matrix.isUnits_det_units _).ne_zero`. Use `Continuous.subtype_mk (Units.continuous_iff.2 ⟨hval, ?_⟩) _` and prove the remaining obligations. Use `hinv.congr fun x => ?_` and prove the remaining obligations. Conclude with `(Matrix.coe_units_inv _).symm`.
-/
theorem continuousOn_cayF : ContinuousOn (cayF P Q) (D0 P Q) := by
  rw [continuousOn_iff_continuous_restrict]
  have hval : Continuous fun x : D0 P Q => UpqT.mat (cayF P Q x) := by
    have h : (fun x : D0 P Q => UpqT.mat (cayF P Q x)) = fun x : D0 P Q =>
        ((1 + 1) + ((x.1 : lieU P Q) : Mat)) * ((1 + 1) - ((x.1 : lieU P Q) : Mat))⁻¹ :=
      funext fun x => cayF_mat x.1 x.2
    rw [h]
    exact (continuous_const.add (continuous_subtype_val.comp continuous_subtype_val)).mul
      (continuous_inv_of_det_ne_zero (continuous_const.sub (continuous_subtype_val.comp continuous_subtype_val))
        fun x => isUnit_iff_ne_zero.1 x.2)
  have hinv : Continuous fun x : D0 P Q => (UpqT.mat (cayF P Q x))⁻¹ :=
    continuous_inv_of_det_ne_zero hval fun x => (Matrix.isUnits_det_units _).ne_zero
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨hval, ?_⟩) _
  refine hinv.congr fun x => ?_
  exact (Matrix.coe_units_inv _).symm

/- English proof (translation)
Establish `h : cayF P Q = (D0 P Q).piecewise (cayF P Q) (fun _ => 1)`. Use function extensionality and compare the values at `X`. Distinguish the cases in `hX : X ∈ D0 P Q`. Simplify using `[Set.piecewise, hX]`. Simplify using `[Set.piecewise, hX, cayF_off X hX]`.

Rewrite using `[h]`. Conclude with `continuousOn_cayF.measurable_piecewise continuousOn_const isOpen_cell_domain.measurableSet`.
-/
theorem measurable_cayF : Measurable (cayF P Q) := by
  classical
  have h : cayF P Q = (D0 P Q).piecewise (cayF P Q) (fun _ => 1) := by
    funext X
    by_cases hX : X ∈ D0 P Q
    · simp [Set.piecewise, hX]
    · simp [Set.piecewise, hX, cayF_off X hX]
  rw [h]
  exact continuousOn_cayF.measurable_piecewise continuousOn_const isOpen_cell_domain.measurableSet

/- English proof (translation)
Unfold `rhoH`. Conclude with `((continuous_adelicGL2_det.measurable.norm.inv).pow_const _).ennreal_ofReal`.
-/
theorem measurable_rhoH : Measurable (rhoH P Q) := by
  unfold rhoH
  exact ((continuous_adelicGL2_det.measurable.norm.inv).pow_const _).ennreal_ofReal

/- English proof (translation)
Establish `hne : ‖((1 + 1) - ((X : lieU P Q) : Mat)).det‖ ≠ 0` using `norm_ne_zero_iff.2 (isUnit_iff_ne_zero.1 hX)`. Unfold `rhoH`. Conclude with `ENNReal.continuous_ofReal.continuousAt.comp ((continuous_adelicGL2_det.continuousAt.norm.inv₀ hne).pow _)`.
-/
theorem continuousAt_rhoH (X : lieU P Q) (hX : X ∈ D0 P Q) : ContinuousAt (rhoH P Q) X := by
  have hne : ‖((1 + 1) - ((X : lieU P Q) : Mat)).det‖ ≠ 0 :=
    norm_ne_zero_iff.2 (isUnit_iff_ne_zero.1 hX)
  unfold rhoH
  exact ENNReal.continuous_ofReal.continuousAt.comp
    ((continuous_adelicGL2_det.continuousAt.norm.inv₀ hne).pow _)

/- English proof (translation)
Unfold `rhoH`. Conclude with `(ENNReal.ofReal_pos.2 (pow_pos (inv_pos.2 (norm_pos_iff.2 (isUnit_iff_ne_zero.1 hX))) _)).ne'`.
-/
theorem rhoH_pos (X : lieU P Q) (hX : X ∈ D0 P Q) : rhoH P Q X ≠ 0 := by
  unfold rhoH
  exact (ENNReal.ofReal_pos.2 (pow_pos (inv_pos.2 (norm_pos_iff.2 (isUnit_iff_ne_zero.1 hX))) _)).ne'

end Chart

end HcInf
