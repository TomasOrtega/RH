import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.Unfold

noncomputable section

open MeasureTheory Matrix Formalism.MainNotions.S Formalism.MainNotions.CayleySignature Formalism.L2.SG.SplitPrimeNormLemmas
open scoped InnerProductSpace ENNReal

namespace WlocSk

def WRightInv : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μW : Measure (Formalism.QuantumDeterminants.Mt k r)),
    Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW →
    IsFiniteMeasure μW → ∀ h ∈ Formalism.QuantumDeterminants.UWset k r z,
      μW.map (fun x : Formalism.QuantumDeterminants.Mt k r => fun i j => (Matrix.of x * h) i j) = μW

def NUnimod : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μN : Measure (Formalism.QuantumDeterminants.Mt k r)),
    Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN →
    (∀ K : Set (Formalism.QuantumDeterminants.Mt k r), IsCompact K → μN K < ⊤) →
    ∀ h ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ m₀ ∈ Formalism.QuantumDeterminants.Nset k r,
      μN.map (fun x : Formalism.QuantumDeterminants.Mt k r => fun i j => (h⁻¹ * Matrix.of x * h * m₀) i j) = μN

namespace AE

variable {k r : ℕ}

/- English proof (translation)
Rewrite using `[← Matrix.mul_assoc, hab, Matrix.one_mul]`.
-/
lemma cancel {a b : Mat k r} (hab : a * b = 1) (X : Mat k r) : a * (b * X) = X := by
  rw [← Matrix.mul_assoc, hab, Matrix.one_mul]

def affE (a a' b b' : Mat k r) (h1 : a' * a = 1) (h2 : a * a' = 1) (h3 : b * b' = 1) (h4 : b' * b = 1) :
    Formalism.QuantumDeterminants.Mt k r ≃ᵐ Formalism.QuantumDeterminants.Mt k r where
  toFun x := fun i j => (a * Matrix.of x * b) i j
  invFun y := fun i j => (a' * Matrix.of y * b') i j
  left_inv x := by
    funext i j
    show (a' * (a * Matrix.of x * b) * b') i j = x i j
    rw [show a' * (a * Matrix.of x * b) * b' = Matrix.of x by
      simp only [Matrix.mul_assoc]; rw [cancel h1, h3, Matrix.mul_one]]
    rfl
  right_inv y := by
    funext i j
    show (a * (a' * Matrix.of y * b') * b) i j = y i j
    rw [show a * (a' * Matrix.of y * b') * b = Matrix.of y by
      simp only [Matrix.mul_assoc]; rw [cancel h2, h4, Matrix.mul_one]]
    rfl
  measurable_toFun := by
    have : Continuous (fun x : Formalism.QuantumDeterminants.Mt k r => (fun i j => (a * Matrix.of x * b) i j : Formalism.QuantumDeterminants.Mt k r)) :=
      (continuous_const.matrix_mul Grp.continuous_of).matrix_mul continuous_const
    exact this.measurable
  measurable_invFun := by
    have : Continuous (fun x : Formalism.QuantumDeterminants.Mt k r => (fun i j => (a' * Matrix.of x * b') i j : Formalism.QuantumDeterminants.Mt k r)) :=
      (continuous_const.matrix_mul Grp.continuous_of).matrix_mul continuous_const
    exact this.measurable

/- English proof (translation)
Rewrite using `[ae_iff]`. Establish `e : {p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r | ¬ Matrix.of p.1 ∈ U} = {x | Matrix.of x ∉ U} ×ˢ Set.univ`. Use extensionality with `p`. Simplify using the standard rewrite rules. Rewrite using `[e, Measure.prod_prod, hU, zero_mul]`.
-/
theorem ae_fst {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)} [SFinite μN] {U : Set (Mat k r)}
    (hU : μW {x | Matrix.of x ∉ U} = 0) : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ U := by
  rw [ae_iff]
  have e : {p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r | ¬ Matrix.of p.1 ∈ U} = {x | Matrix.of x ∉ U} ×ˢ Set.univ := by
    ext p
    simp
  rw [e, Measure.prod_prod, hU, zero_mul]

/- English proof (translation)
Rewrite using `[ae_iff]`. Establish `e : {p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r | ¬ Matrix.of p.2 ∈ U} = Set.univ ×ˢ {x | Matrix.of x ∉ U}`. Use extensionality with `p`. Simplify using the standard rewrite rules. Rewrite using `[e, Measure.prod_prod, hU, mul_zero]`.
-/
theorem ae_snd {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)} [SFinite μN] {U : Set (Mat k r)}
    (hU : μN {x | Matrix.of x ∉ U} = 0) : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.2 ∈ U := by
  rw [ae_iff]
  have e : {p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r | ¬ Matrix.of p.2 ∈ U} = Set.univ ×ˢ {x | Matrix.of x ∉ U} := by
    ext p
    simp
  rw [e, Measure.prod_prod, hU, mul_zero]

/- English proof (translation)
Establish `ha0 : a ≠ 0`. Introduce and unpack `rfl`. Simplify using `at ha`. Establish `hb : b = a⁻¹` using `(inv_eq_of_mul_eq_one_right hab).symm`. Establish `hconj : star a = a⁻¹`.

Rewrite using `[Complex.inv_def, Complex.normSq_eq_norm_sq, ha]`. Simplify using `[Complex.star_def]`. Rewrite using `[hb, star_inv₀, hconj, inv_inv]`.
-/
lemma star_of_inv {a b : ℂ} (ha : ‖a‖ = 1) (hab : a * b = 1) : star b = a := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at ha
  have hb : b = a⁻¹ := (inv_eq_of_mul_eq_one_right hab).symm
  have hconj : star a = a⁻¹ := by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, ha]
    simp [Complex.star_def]
  rw [hb, star_inv₀, hconj, inv_inv]

end AE

/- English proof (translation)
Introduce `k r z c u v b H _ _ _ σ Vp _ _ _ π w μG μS ν μW μN hyp hR hCW x₀ hx₀ ξ h hh m hm g hg`. Establish `hAIg` using `hAI k r z c u v b H σ Vp π w μG μS ν μW μN hyp hR hCW x₀ hx₀ ξ g hg`. Take `⟨hset, hDS, hHC, -, -, -, -, hW, hN, hWfin, hNK⟩` from `hyp`. Take `⟨-, -, hz, hT, -⟩` from `hset`. Take `⟨hWG, hNG, hWg, hNg, hconj⟩` from `hSG k r z c hz hT`.

Establish `hσ` using `hSig k r _ _ H σ hDS`. Take `⟨⟨-, hπmul⟩, -⟩` from `hPU k r z u Vp π hz hT hHC`. Establish `hhG` using `hWG hh`. Establish `hmG` using `hNG hm`. Establish `hgG : g ∈ Gr k r` using `hg`.

Establish `hhi : h⁻¹ ∈ Formalism.QuantumDeterminants.UWset k r z` using `(hWg h hh h hh).2.1`. Establish `hih : h⁻¹ * h = 1` using `Grp.inv_mul hhG`. Establish `hhi' : h * h⁻¹ = 1` using `Grp.mul_inv hhG`. Establish `hinv2 : (h⁻¹)⁻¹ = h` using `Matrix.nonsing_inv_nonsing_inv h (Matrix.isUnit_det_of_right_inverse hhi')`. Establish `hmi : m⁻¹ ∈ Formalism.QuantumDeterminants.Nset k r` using `(hNg m hm m hm).2.1`.

Establish `hmim : m⁻¹ * m = 1` using `Grp.inv_mul hmG`. Take `⟨hm₀, -⟩` from `hconj h⁻¹ hhi m⁻¹ hmi`. Rewrite `hm₀` using `[hinv2]`. Take `⟨m₀, hm₀def⟩ : ∃ m₀ : Mat k r, m₀ = h * m⁻¹ * h⁻¹` from `⟨_, rfl⟩`. Rewrite `hm₀` using `[← hm₀def]`.

Establish `hm₀G` using `hNG hm₀`. Establish `hW1` using `hWR k r z μW hz hT hW hWfin h⁻¹ hhi`. Establish `hN1` using `hNU k r z μN hz hT hN hNK h⁻¹ hhi m₀ hm₀`. Rewrite `hN1` using `[hinv2]`. Establish `h3 : h⁻¹ * m₀ * (m₀⁻¹ * h) = 1`.

Rewrite using `[Matrix.mul_assoc, AE.cancel (Grp.mul_inv hm₀G), hih]`. Establish `h4 : m₀⁻¹ * h * (h⁻¹ * m₀) = 1`. Rewrite using `[Matrix.mul_assoc, AE.cancel hhi', Grp.inv_mul hm₀G]`. Set `e₁` to `AE.affE (k := k) (r := r) 1 1 h⁻¹ h (Matrix.one_mul 1) (Matrix.one_mul 1) hih hhi'`. Set `e₂` to `AE.affE (k := k) (r := r) h h⁻¹ (h⁻¹ * m₀) (m₀⁻¹ * h) hih hhi' h3 h4`.

Establish `he₁ : μW.map e₁ = μW`. Establish `: (e₁ : Formalism.QuantumDeterminants.Mt k r → Formalism.QuantumDeterminants.Mt k r) = fun x => fun i j => (Matrix.of x * h⁻¹) i j`. Use function extensionality and compare the values at `x i j`. Use `show ((1 : Mat k r) * Matrix.of x * h⁻¹) i j = _`. Rewrite using `[Matrix.one_mul]`.

Rewrite using `[this, hW1]`. Establish `he₂ : μN.map e₂ = μN`. Establish `: (e₂ : Formalism.QuantumDeterminants.Mt k r → Formalism.QuantumDeterminants.Mt k r) = fun x => fun i j => (h * Matrix.of x * h⁻¹ * m₀) i j`. Use function extensionality and compare the values at `x i j`. Use `show (h * Matrix.of x * (h⁻¹ * m₀)) i j = _`.

Rewrite using `[← Matrix.mul_assoc (h * Matrix.of x)]`. Rewrite using `[this, hN1]`. Establish `hP : (μW.prod μN).map (e₁.prodCongr e₂) = μW.prod μN`. Use `hW.1` as an intermediate fact. Use `hN.1` as an intermediate fact.

Use `show (μW.prod μN).map (Prod.map e₁ e₂) = _`. Rewrite using `[← Measure.map_prod_map μW μN e₁.measurable e₂.measurable, he₁, he₂]`. Use `hN.1` as an intermediate fact. Establish `hWc` using `AE.ae_fst (μN := μN) hW.2.2.1`. Establish `hNc` using `AE.ae_snd (μW := μW) hN.2.2.1`.

Use `show ∫ p, bInt z c σ π (σ x₀ w) ξ (σ (h * m * g) w) p ∂(μW.prod μN) = psiGen k r z c m • π h (∫ p, bInt z c σ π (σ x₀ w) ξ (σ g w) p ∂(μW.prod μN))`. Use `conv_lhs => rw [← hP]`. Rewrite using `[integral_map_equiv, ← ContinuousLinearMap.integral_comp_comm _ hAIg, ← integral_smul]`. Apply `integral_congr_ae` to reduce the goal to its premises. Use `filter_upwards [hWc, hNc] with p h1 h2`.

Establish `h1G` using `hWG h1`. Establish `h2G` using `hNG h2`. Establish `hXG : (1 * Matrix.of p.1 * h⁻¹) * (h * Matrix.of p.2 * (h⁻¹ * m₀)) ∈ Gr k r` using `Grp.mul_mem (Grp.mul_mem (Grp.mul_mem Grp.one_mem h1G) (Grp.inv_mem hhG)) (Grp.mul_mem (Grp.mul_mem hhG h2G) (Grp.mul_mem (Grp.inv_mem hhG) hm₀G))`. Establish `hmgG : h * m * g ∈ Gr k r` using `Grp.mul_mem (Grp.mul_mem hhG hmG) hgG`. Establish `hσ1 : σ ((1 * Matrix.of p.1 * h⁻¹) * (h * Matrix.of p.2 * (h⁻¹ * m₀))) (σ (h * m * g) w) = σ (Matrix.of p.1 * Matrix.of p.2) (σ g w)`.

Establish `e1 : σ ((1 * Matrix.of p.1 * h⁻¹) * (h * Matrix.of p.2 * (h⁻¹ * m₀))) (σ (h * m * g) w) = σ ((1 * Matrix.of p.1 * h⁻¹) * (h * Matrix.of p.2 * (h⁻¹ * m₀)) * (h * m * g)) w`. Rewrite using `[hσ.1.2 _ hXG _ hmgG]`. Both sides reduce to the same expression. Establish `e2 : σ (Matrix.of p.1 * Matrix.of p.2) (σ g w) = σ (Matrix.of p.1 * Matrix.of p.2 * g) w`. Rewrite using `[hσ.1.2 _ (Grp.mul_mem h1G h2G) _ hgG]`.

Both sides reduce to the same expression. Establish `hX : (1 * Matrix.of p.1 * h⁻¹) * (h * Matrix.of p.2 * (h⁻¹ * m₀)) * (h * m * g) = Matrix.of p.1 * Matrix.of p.2 * g`. Rewrite using `[hm₀def]`. Simplify using `only [Matrix.one_mul, Matrix.mul_assoc]`. Rewrite using `[AE.cancel hih, AE.cancel hih, AE.cancel hih, AE.cancel hmim]`.

Rewrite using `[e1, e2, hX]`. Establish `hψ2 : psiGen k r z c (h * Matrix.of p.2 * (h⁻¹ * m₀)) = psiGen k r z c (Matrix.of p.2) * psiGen k r z c m⁻¹`. Establish `hq : h * Matrix.of p.2 * (h⁻¹ * m₀) = (h⁻¹)⁻¹ * (Matrix.of p.2 * m⁻¹) * h⁻¹`. Rewrite using `[hm₀def, hinv2]`. Simplify using `only [Matrix.mul_assoc]`.

Rewrite using `[AE.cancel hih]`. Rewrite using `[hq, (hconj h⁻¹ hhi _ (hNg _ h2 _ hmi).1).2, (hNg _ h2 _ hmi).2.2.2.1]`. Establish `hψm : star (psiGen k r z c m⁻¹) = psiGen k r z c m`. Apply `AE.star_of_inv (hNg m hm m hm).2.2.2.2` to reduce the goal to its premises. Establish `h11 : m * m⁻¹ = 1` using `(hNg m hm m hm).2.2.1`.

Establish `h1N : (1 : Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r`. Use `(hNg m hm m⁻¹ hmi).1` as an intermediate fact. Rewrite `this` using `[h11]`. Then use the resulting hypothesis. Establish `hψ1 : psiGen k r z c 1 = 1`. Establish `hmul` using `(hNg 1 h1N 1 h1N).2.2.2.1`.

Rewrite `hmul` using `[Matrix.mul_one]`. Establish `hn : psiGen k r z c 1 ≠ 0`. Introduce `h0`. Use `(hNg 1 h1N 1 h1N).2.2.2.2` as an intermediate fact. Rewrite `this` using `[h0, norm_zero]`.

Conclude with `zero_ne_one this`. Establish `: psiGen k r z c 1 * (psiGen k r z c 1 - 1) = 0` using `by rw [mul_sub, mul_one, ← hmul, sub_self]`. Break down `mul_eq_zero.mp this with h | h` into its components or cases. Conclude with `absurd h hn`. Conclude with `sub_eq_zero.mp h`.

Rewrite using `[← (hNg m hm m⁻¹ hmi).2.2.2.1, h11, hψ1]`. Establish `hπ2 : π (1 * Matrix.of p.1 * h⁻¹)⁻¹ = (π h).comp (π (Matrix.of p.1)⁻¹)`. Rewrite using `[Matrix.one_mul, Matrix.mul_inv_rev, hinv2]`. Conclude with `hπmul h hh _ (hWg _ h1 _ h1).2.1`. Use `show (⟪σ x₀ w, σ ((1 * Matrix.of p.1 * h⁻¹) * (h * Matrix.of p.2 * (h⁻¹ * m₀))) (σ (h * m * g) w)⟫_ℂ * star (psiGen k r z c (h * Matrix.of p.2 * (h⁻¹ * m₀)))) • π (1 * Matrix.of p.1 * h⁻¹)⁻¹ ξ = psiGen k r z c m • π h ((⟪σ x₀ w, σ (Matrix.of p.1 * Matrix.of p.2) (σ g w)⟫_ℂ * star …`.

Rewrite using `[hσ1, hψ2, hπ2, ContinuousLinearMap.comp_apply, map_smul, smul_smul, star_mul', hψm]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem aEquiv_of (hSG : SGrp) (hPU : PiUnit) (hSig : SigmaG) (hWR : WRightInv) (hNU : NUnimod)
    (hAI : AInt) : AEquiv := by
  intro k r z c u v b H _ _ _ σ Vp _ _ _ π w μG μS ν μW μN hyp hR hCW x₀ hx₀ ξ h hh m hm g hg
  have hAIg := hAI k r z c u v b H σ Vp π w μG μS ν μW μN hyp hR hCW x₀ hx₀ ξ g hg
  obtain ⟨hset, hDS, hHC, -, -, -, -, hW, hN, hWfin, hNK⟩ := hyp
  obtain ⟨-, -, hz, hT, -⟩ := hset
  obtain ⟨hWG, hNG, hWg, hNg, hconj⟩ := hSG k r z c hz hT
  have hσ := hSig k r _ _ H σ hDS
  obtain ⟨⟨-, hπmul⟩, -⟩ := hPU k r z u Vp π hz hT hHC
  have hhG := hWG hh
  have hmG := hNG hm
  have hgG : g ∈ Gr k r := hg
  have hhi : h⁻¹ ∈ Formalism.QuantumDeterminants.UWset k r z := (hWg h hh h hh).2.1
  have hih : h⁻¹ * h = 1 := Grp.inv_mul hhG
  have hhi' : h * h⁻¹ = 1 := Grp.mul_inv hhG
  have hinv2 : (h⁻¹)⁻¹ = h :=
    Matrix.nonsing_inv_nonsing_inv h (Matrix.isUnit_det_of_right_inverse hhi')
  have hmi : m⁻¹ ∈ Formalism.QuantumDeterminants.Nset k r := (hNg m hm m hm).2.1
  have hmim : m⁻¹ * m = 1 := Grp.inv_mul hmG
  obtain ⟨hm₀, -⟩ := hconj h⁻¹ hhi m⁻¹ hmi
  rw [hinv2] at hm₀
  obtain ⟨m₀, hm₀def⟩ : ∃ m₀ : Mat k r, m₀ = h * m⁻¹ * h⁻¹ := ⟨_, rfl⟩
  rw [← hm₀def] at hm₀
  have hm₀G := hNG hm₀

  have hW1 := hWR k r z μW hz hT hW hWfin h⁻¹ hhi
  have hN1 := hNU k r z μN hz hT hN hNK h⁻¹ hhi m₀ hm₀
  rw [hinv2] at hN1
  have h3 : h⁻¹ * m₀ * (m₀⁻¹ * h) = 1 := by
    rw [Matrix.mul_assoc, AE.cancel (Grp.mul_inv hm₀G), hih]
  have h4 : m₀⁻¹ * h * (h⁻¹ * m₀) = 1 := by
    rw [Matrix.mul_assoc, AE.cancel hhi', Grp.inv_mul hm₀G]
  let e₁ := AE.affE (k := k) (r := r) 1 1 h⁻¹ h (Matrix.one_mul 1) (Matrix.one_mul 1) hih hhi'
  let e₂ := AE.affE (k := k) (r := r) h h⁻¹ (h⁻¹ * m₀) (m₀⁻¹ * h) hih hhi' h3 h4
  have he₁ : μW.map e₁ = μW := by
    have : (e₁ : Formalism.QuantumDeterminants.Mt k r → Formalism.QuantumDeterminants.Mt k r) = fun x => fun i j => (Matrix.of x * h⁻¹) i j := by
      funext x i j
      show ((1 : Mat k r) * Matrix.of x * h⁻¹) i j = _
      rw [Matrix.one_mul]
    rw [this, hW1]
  have he₂ : μN.map e₂ = μN := by
    have : (e₂ : Formalism.QuantumDeterminants.Mt k r → Formalism.QuantumDeterminants.Mt k r) =
        fun x => fun i j => (h * Matrix.of x * h⁻¹ * m₀) i j := by
      funext x i j
      show (h * Matrix.of x * (h⁻¹ * m₀)) i j = _
      rw [← Matrix.mul_assoc (h * Matrix.of x)]
    rw [this, hN1]
  have hP : (μW.prod μN).map (e₁.prodCongr e₂) = μW.prod μN := by
    have := hW.1
    have := hN.1
    show (μW.prod μN).map (Prod.map e₁ e₂) = _
    rw [← Measure.map_prod_map μW μN e₁.measurable e₂.measurable, he₁, he₂]
  have := hN.1
  have hWc := AE.ae_fst (μN := μN) hW.2.2.1
  have hNc := AE.ae_snd (μW := μW) hN.2.2.1
  show ∫ p, bInt z c σ π (σ x₀ w) ξ (σ (h * m * g) w) p ∂(μW.prod μN) =
    psiGen k r z c m • π h (∫ p, bInt z c σ π (σ x₀ w) ξ (σ g w) p ∂(μW.prod μN))
  conv_lhs => rw [← hP]
  rw [integral_map_equiv, ← ContinuousLinearMap.integral_comp_comm _ hAIg, ← integral_smul]
  apply integral_congr_ae
  filter_upwards [hWc, hNc] with p h1 h2

  have h1G := hWG h1
  have h2G := hNG h2
  have hXG : (1 * Matrix.of p.1 * h⁻¹) * (h * Matrix.of p.2 * (h⁻¹ * m₀)) ∈ Gr k r :=
    Grp.mul_mem (Grp.mul_mem (Grp.mul_mem Grp.one_mem h1G) (Grp.inv_mem hhG))
      (Grp.mul_mem (Grp.mul_mem hhG h2G) (Grp.mul_mem (Grp.inv_mem hhG) hm₀G))
  have hmgG : h * m * g ∈ Gr k r := Grp.mul_mem (Grp.mul_mem hhG hmG) hgG
  have hσ1 : σ ((1 * Matrix.of p.1 * h⁻¹) * (h * Matrix.of p.2 * (h⁻¹ * m₀)))
      (σ (h * m * g) w) = σ (Matrix.of p.1 * Matrix.of p.2) (σ g w) := by
    have e1 : σ ((1 * Matrix.of p.1 * h⁻¹) * (h * Matrix.of p.2 * (h⁻¹ * m₀)))
        (σ (h * m * g) w) =
        σ ((1 * Matrix.of p.1 * h⁻¹) * (h * Matrix.of p.2 * (h⁻¹ * m₀)) * (h * m * g)) w := by
      rw [hσ.1.2 _ hXG _ hmgG]; rfl
    have e2 : σ (Matrix.of p.1 * Matrix.of p.2) (σ g w) = σ (Matrix.of p.1 * Matrix.of p.2 * g) w := by
      rw [hσ.1.2 _ (Grp.mul_mem h1G h2G) _ hgG]; rfl
    have hX : (1 * Matrix.of p.1 * h⁻¹) * (h * Matrix.of p.2 * (h⁻¹ * m₀)) * (h * m * g) =
        Matrix.of p.1 * Matrix.of p.2 * g := by
      rw [hm₀def]
      simp only [Matrix.one_mul, Matrix.mul_assoc]
      rw [AE.cancel hih, AE.cancel hih, AE.cancel hih, AE.cancel hmim]
    rw [e1, e2, hX]
  have hψ2 : psiGen k r z c (h * Matrix.of p.2 * (h⁻¹ * m₀)) =
      psiGen k r z c (Matrix.of p.2) * psiGen k r z c m⁻¹ := by
    have hq : h * Matrix.of p.2 * (h⁻¹ * m₀) = (h⁻¹)⁻¹ * (Matrix.of p.2 * m⁻¹) * h⁻¹ := by
      rw [hm₀def, hinv2]
      simp only [Matrix.mul_assoc]
      rw [AE.cancel hih]
    rw [hq, (hconj h⁻¹ hhi _ (hNg _ h2 _ hmi).1).2, (hNg _ h2 _ hmi).2.2.2.1]
  have hψm : star (psiGen k r z c m⁻¹) = psiGen k r z c m := by
    apply AE.star_of_inv (hNg m hm m hm).2.2.2.2
    have h11 : m * m⁻¹ = 1 := (hNg m hm m hm).2.2.1
    have h1N : (1 : Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r := by
      have := (hNg m hm m⁻¹ hmi).1; rwa [h11] at this
    have hψ1 : psiGen k r z c 1 = 1 := by
      have hmul := (hNg 1 h1N 1 h1N).2.2.2.1
      rw [Matrix.mul_one] at hmul
      have hn : psiGen k r z c 1 ≠ 0 := by
        intro h0; have := (hNg 1 h1N 1 h1N).2.2.2.2; rw [h0, norm_zero] at this; exact zero_ne_one this
      have : psiGen k r z c 1 * (psiGen k r z c 1 - 1) = 0 := by rw [mul_sub, mul_one, ← hmul, sub_self]
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hn
      · exact sub_eq_zero.mp h
    rw [← (hNg m hm m⁻¹ hmi).2.2.2.1, h11, hψ1]
  have hπ2 : π (1 * Matrix.of p.1 * h⁻¹)⁻¹ = (π h).comp (π (Matrix.of p.1)⁻¹) := by
    rw [Matrix.one_mul, Matrix.mul_inv_rev, hinv2]
    exact hπmul h hh _ (hWg _ h1 _ h1).2.1
  show (⟪σ x₀ w, σ ((1 * Matrix.of p.1 * h⁻¹) * (h * Matrix.of p.2 * (h⁻¹ * m₀)))
      (σ (h * m * g) w)⟫_ℂ * star (psiGen k r z c (h * Matrix.of p.2 * (h⁻¹ * m₀)))) •
      π (1 * Matrix.of p.1 * h⁻¹)⁻¹ ξ =
    psiGen k r z c m • π h ((⟪σ x₀ w, σ (Matrix.of p.1 * Matrix.of p.2) (σ g w)⟫_ℂ *
      star (psiGen k r z c (Matrix.of p.2))) • π (Matrix.of p.1)⁻¹ ξ)
  rw [hσ1, hψ2, hπ2, ContinuousLinearMap.comp_apply, map_smul, smul_smul, star_mul', hψm]
  congr 1
  ring

end WlocSk
