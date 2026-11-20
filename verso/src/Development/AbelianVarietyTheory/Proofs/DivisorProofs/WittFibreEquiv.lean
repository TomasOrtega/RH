import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatStab
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallUnf

noncomputable section

namespace GlobalTheory.WittFibre

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
The claim follows from `Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 F) F)`.
-/
theorem inclR_inj : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
  Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 F) F)

/- English proof (translation)
Introduce `a b h` and use `funext fun i => inclR_inj (congrFun h i)`.
-/
theorem incV_inj {n : ℕ} : Function.Injective (incV F (E := E) (n := n)) := fun a b h =>
  funext fun i => inclR_inj (congrFun h i)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cA_inclR' (σ : E →ₐ[F] E) (e : E) : cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := rfl

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [incV, incM]`. Rewrite using `[RingHom.map_mulVec]`. Both sides reduce to the same expression.
-/
theorem incM_mulVec {n : ℕ} (G : Matrix (Fin n) (Fin n) E) (v : Fin n → E) :
    incM F G *ᵥ incV F v = incV F (G *ᵥ v) := by
  funext i
  simp only [incV, incM]
  rw [RingHom.map_mulVec]
  rfl

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[incV]`.
-/
theorem incV_smul {n : ℕ} (c : E) (v : Fin n → E) :
    incV F (c • v) = inclR (F := F) (AF F) c • incV F v := by
  funext i; simp [incV]

/- English proof (translation)
Simplify using `only [incM, Matrix.map_mul]`.
-/
theorem incM_mul {n : ℕ} (A B : Matrix (Fin n) (Fin n) E) : incM F (A * B) = incM F A * incM F B := by
  simp only [incM, Matrix.map_mul]

/- English proof (translation)
Simplify using `only [incM]`. Conclude with `Matrix.map_one _ (map_zero _) (map_one _)`.
-/
theorem incM_one {n : ℕ} : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := by
  simp only [incM]; exact Matrix.map_one _ (map_zero _) (map_one _)

/- English proof (translation)
The claim follows from `Matrix.map_injective inclR_inj`.
-/
theorem incM_inj {n : ℕ} : Function.Injective (incM F (E := E) (m := Fin n) (n := Fin n)) :=
  Matrix.map_injective inclR_inj

/- English proof (translation)
Take `⟨G, hG⟩` from `Subgroup.mem_subgroupOf.1 hg`. Conclude with `⟨G, by rw [mat, ← hG]; rfl⟩`.
-/
theorem exists_rat {σ : E →ₐ[F] E} {d : ℕ} {J : Matrix (Fin d) (Fin d) E} {g : UA σ J} (hg : g ∈ ratU σ J) :
    ∃ G : Matrix (Fin d) (Fin d) E, mat g = incM F G := by
  obtain ⟨G, hG⟩ := Subgroup.mem_subgroupOf.1 hg
  exact ⟨G, by rw [mat, ← hG]; rfl⟩

/- English proof (translation)
Establish `h' : (incM F G)ᵀ * incM F J * (incM F G).map (cA σ) = incM F J` using `by rw [← hG]; exact g.2`. Establish `h3 : (incM F G).map (cA σ) = incM F (G.map σ)`. Use extensionality with `i j`. Simplify using `[incM, cA_inclR']`. Establish `e : incM F (Gᵀ * J * G.map σ) = incM F J`.

Rewrite using `[← h', h3]`. Simplify using `only [incM, Matrix.map_mul, Matrix.transpose_map]`. Conclude with `Matrix.map_injective inclR_inj e`.
-/
theorem unitary_rat {σ : E →ₐ[F] E} {d : ℕ} {J : Matrix (Fin d) (Fin d) E} (g : UA σ J) (G : Matrix (Fin d) (Fin d) E)
    (hG : mat g = incM F G) : Gᵀ * J * G.map σ = J := by
  have h' : (incM F G)ᵀ * incM F J * (incM F G).map (cA σ) = incM F J := by rw [← hG]; exact g.2
  have h3 : (incM F G).map (cA σ) = incM F (G.map σ) := by
    ext i j; simp [incM, cA_inclR']
  have e : incM F (Gᵀ * J * G.map σ) = incM F J := by
    rw [← h', h3]; simp only [incM, Matrix.map_mul, Matrix.transpose_map]
  exact Matrix.map_injective inclR_inj e

/- English proof (translation)
Unfold `form`. Establish `: (fun i => σ ((G *ᵥ w) i)) = G.map σ *ᵥ fun i => σ (w i)`. Use function extensionality and compare the values at `i`. Simplify using `[Matrix.mulVec, dotProduct, map_sum, map_mul]`. Rewrite using `[this, Matrix.mulVec_mulVec, ← Matrix.vecMul_transpose, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, ← Matrix.dotProduct_mulVec, ← Matrix.mul_assoc, hG]`.
-/
theorem form_mulVec (σ : E →ₐ[F] E) {d : ℕ} (J G : Matrix (Fin d) (Fin d) E) (hG : Gᵀ * J * G.map σ = J)
    (v w : Fin d → E) : form σ J (G *ᵥ v) (G *ᵥ w) = form σ J v w := by
  unfold form
  have : (fun i => σ ((G *ᵥ w) i)) = G.map σ *ᵥ fun i => σ (w i) := by
    funext i; simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  rw [this, Matrix.mulVec_mulVec, ← Matrix.vecMul_transpose, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    ← Matrix.dotProduct_mulVec, ← Matrix.mul_assoc, hG]

/- English proof (translation)
Unfold `form`. Establish `: (fun i => σ ((c • v) i)) = σ c • fun i => σ (v i)`. Use function extensionality and compare the values at `i`. Simplify using `[map_mul]`. Rewrite using `[this, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem form_smul (σ : E →ₐ[F] E) {d : ℕ} (J : Matrix (Fin d) (Fin d) E) (c : E) (v : Fin d → E) :
    form σ J (c • v) (c • v) = c * σ c * form σ J v v := by
  unfold form
  have : (fun i => σ ((c • v) i)) = σ c • fun i => σ (v i) := by
    funext i; simp [map_mul]
  rw [this, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]; ring

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mat_mul {σ : E →ₐ[F] E} {d : ℕ} {J : Matrix (Fin d) (Fin d) E} (g h : UA σ J) : mat (g * h) = mat g * mat h := rfl

/- English proof (translation)
Simplify using `[mat]`.
-/
theorem mat_one {σ : E →ₐ[F] E} {d : ℕ} {J : Matrix (Fin d) (Fin d) E} : mat (1 : UA σ J) = 1 := by simp [mat]

end GlobalTheory.WittFibre

namespace GlobalTheory.WittFibre

open GlobalTheory.WittFibre

/- English proof (translation)
Take `⟨A, hA⟩` from `exists_rat ht`. Take `⟨B, hB⟩` from `exists_rat (inv_mem ht)`. Establish `hAB : A * B = 1`. Apply `incM_inj (F := F)` to reduce the goal to its premises. Rewrite using `[incM_mul, ← hA, ← hB, incM_one, ← mat_mul, mul_inv_cancel, mat_one]`.

Establish `hBA : B * A = 1`. Apply `incM_inj (F := F)` to reduce the goal to its premises. Rewrite using `[incM_mul, ← hA, ← hB, incM_one, ← mat_mul, inv_mul_cancel, mat_one]`. Establish `hBu : Bᵀ * J * B.map σ = J` using `unitary_rat _ B hB`. Use `set u : Fin n → E := B *ᵥ x with hu`.

Establish `hu0 : u ≠ 0`. Introduce `h0`. Apply `hx` to reduce the goal to its premises. Rewrite using `[← Matrix.one_mulVec x, ← hAB, ← Matrix.mulVec_mulVec, ← hu, h0, Matrix.mulVec_zero]`. Establish `huu : form σ J u u = 0` using `by rw [hu, form_mulVec σ J B hBu, hxx]`.

Set `wv : Eˣ → IsoV σ J` to `fun ξ => ⟨((ξ⁻¹ : Eˣ) : E) • u, smul_ne_zero (Units.ne_zero _) hu0, by rw [form_smul, huu, mul_zero]⟩`. Establish `eig : ∀ ξ : Eˣ, mat (γ (wv ξ) * t⁻¹) *ᵥ incV F x = inclR (F` using `F) (AF F) (ξ : E) • incV F x := by`. Introduce `ξ`. Establish `h1 : u = (ξ : E) • (wv ξ).1` using `by show u = (ξ : E) • (((ξ⁻¹ : Eˣ) : E) • u)`. Rewrite using `[smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]`.

Rewrite using `[mat_mul, ← Matrix.mulVec_mulVec, hB, incM_mulVec, ← hu, h1, incV_smul, Matrix.mulVec_smul, (hγ _).2]`. Set `f : Eˣ → {w : IsoV σ J // ∃ l : (AE F E)ˣ, mat (γ w * t⁻¹) *ᵥ incV F x = l.1 • incV F x}` to `fun ξ => ⟨wv ξ, Units.map (inclR (F := F) (AF F)).toMonoidHom ξ, eig ξ⟩`. Establish `finj : Function.Injective f`. Introduce `ξ η h`. Establish `h2 : ((ξ⁻¹ : Eˣ) : E) • u = ((η⁻¹ : Eˣ) : E) • u` using `congrArg (fun z => z.1.1) h`.

Establish `h3 : ((ξ⁻¹ : Eˣ) : E) = ((η⁻¹ : Eˣ) : E)` using `smul_left_injective E hu0 h2`. Conclude with `inv_injective (Units.ext h3)`. Establish `fsurj : Function.Surjective f`. Introduce and unpack `⟨w, l, hl0⟩`. Use `haveI : Nontrivial (AE F E) := (inclR_inj (F := F) (E := E)).nontrivial`.

Take `⟨P, hP⟩` from `exists_rat (mul_mem (hγ w).1 (inv_mem ht))`. Establish `hl` using `hl0`. Rewrite `hl` using `[hP, incM_mulVec]`. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, x i ≠ 0 := by`. Assume the negation of the conclusion as `hc`.

Use `push_neg at hc`. Conclude with `hx (funext hc)`. Establish `ei : inclR (F` using `F) (AF F) ((P *ᵥ x) i) = l.1 * inclR (F := F) (AF F) (x i) := by`. Use `congrFun hl i` as an intermediate fact. Simplify `this` using `[incV]`.

Establish `hPi : (P *ᵥ x) i ≠ 0`. Introduce `h0`. Rewrite `ei` using `[h0, map_zero]`. Establish `hu1 : IsUnit (l.1 * inclR (F` using `F) (AF F) (x i)) := l.isUnit.mul ((isUnit_iff_ne_zero.2 hi).map _)`. Rewrite `hu1` using `[← ei]`.

Conclude with `not_isUnit_zero hu1`. Use `set ξ0 : E := (P *ᵥ x) i * (x i)⁻¹ with hξ0`. Establish `hξ0ne : ξ0 ≠ 0` using `mul_ne_zero hPi (inv_ne_zero hi)`. Establish `hl1 : l.1 = inclR (F` using `F) (AF F) ξ0 := by`. Establish `hxi : IsUnit (inclR (F` using `F) (AF F) (x i)) := (isUnit_iff_ne_zero.2 hi).map _`.

Apply `hxi.mul_left_injective` to reduce the goal to its premises. Simplify using `only`. Rewrite using `[← ei, ← map_mul, hξ0, mul_assoc, inv_mul_cancel₀ hi, mul_one]`. Establish `hPx : incV F (P *ᵥ x) = incV F (ξ0 • x)` using `by rw [hl, hl1, incV_smul]`. Establish `hpw : mat (γ w * t⁻¹) *ᵥ incV F (A *ᵥ w.1) = incV F x`.

Rewrite using `[← incM_mulVec, ← hA, Matrix.mulVec_mulVec, ← mat_mul, mul_assoc, inv_mul_cancel, mul_one]`. Conclude with `(hγ w).2`. Establish `hpx : mat (γ w * t⁻¹) *ᵥ incV F (ξ0⁻¹ • x) = incV F x`. Establish `hPx' : P *ᵥ x = ξ0 • x` using `incV_inj hPx`. Rewrite using `[hP, incM_mulVec, Matrix.mulVec_smul, hPx', smul_smul, inv_mul_cancel₀ hξ0ne, one_smul]`.

Establish `hinvp : mat (γ w * t⁻¹)⁻¹ * mat (γ w * t⁻¹) = 1` using `by rw [← mat_mul, inv_mul_cancel, mat_one]`. Establish `hAw : incV F (A *ᵥ w.1) = incV F (ξ0⁻¹ • x)`. Rewrite using `[← Matrix.one_mulVec (incV F (A *ᵥ w.1)), ← Matrix.one_mulVec (incV F (ξ0⁻¹ • x)), ← hinvp, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hpw, hpx]`. Establish `hw : w.1 = ξ0⁻¹ • u`. Rewrite using `[← Matrix.one_mulVec w.1, ← hBA, ← Matrix.mulVec_mulVec, incV_inj hAw, Matrix.mulVec_smul]`.

Use `⟨Units.mk0 ξ0 hξ0ne, Subtype.ext (Subtype.ext ?_)⟩` and prove the remaining obligations. Use `show ((Units.mk0 ξ0 hξ0ne)⁻¹ : Eˣ).val • u = w.1`. Rewrite using `[Units.val_inv_eq_inv_val, Units.val_mk0, hw]`. Use `⟨(Equiv.ofBijective f ⟨finj, fsurj⟩).symm, fun w => ?_⟩` and prove the remaining obligations. Establish `hw : f ((Equiv.ofBijective f ⟨finj, fsurj⟩).symm w) = w` using `(Equiv.ofBijective f ⟨finj, fsurj⟩).apply_symm_apply w`.

Use `eig ((Equiv.ofBijective f ⟨finj, fsurj⟩).symm w)` as an intermediate fact. Use `conv_lhs => rw [← hw]`. Conclude with `this`.
-/
theorem wittFibre_equiv (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E) (hx : x ≠ 0) (hxx : form σ J x x = 0)
    (γ : IsoV σ J → UA σ J) (hγ : IsWitt (σ := σ) (J := J) x γ) (t : UA σ J) (ht : t ∈ ratU σ J) :
    ∃ κ : {w : IsoV σ J // ∃ l : (AE F E)ˣ, mat (γ w * t⁻¹) *ᵥ incV F x = l.1 • incV F x} ≃ Eˣ,
      ∀ w, mat (γ w.1 * t⁻¹) *ᵥ incV F x = (inclR (F := F) (AF F) (κ w : E)) • incV F x := by
  obtain ⟨A, hA⟩ := exists_rat ht
  obtain ⟨B, hB⟩ := exists_rat (inv_mem ht)
  have hAB : A * B = 1 := by
    apply incM_inj (F := F)
    rw [incM_mul, ← hA, ← hB, incM_one, ← mat_mul, mul_inv_cancel, mat_one]
  have hBA : B * A = 1 := by
    apply incM_inj (F := F)
    rw [incM_mul, ← hA, ← hB, incM_one, ← mat_mul, inv_mul_cancel, mat_one]
  have hBu : Bᵀ * J * B.map σ = J := unitary_rat _ B hB
  set u : Fin n → E := B *ᵥ x with hu
  have hu0 : u ≠ 0 := by
    intro h0; apply hx
    rw [← Matrix.one_mulVec x, ← hAB, ← Matrix.mulVec_mulVec, ← hu, h0, Matrix.mulVec_zero]
  have huu : form σ J u u = 0 := by rw [hu, form_mulVec σ J B hBu, hxx]

  let wv : Eˣ → IsoV σ J := fun ξ => ⟨((ξ⁻¹ : Eˣ) : E) • u, smul_ne_zero (Units.ne_zero _) hu0,
    by rw [form_smul, huu, mul_zero]⟩
  have eig : ∀ ξ : Eˣ, mat (γ (wv ξ) * t⁻¹) *ᵥ incV F x = inclR (F := F) (AF F) (ξ : E) • incV F x := by
    intro ξ
    have h1 : u = (ξ : E) • (wv ξ).1 := by
      show u = (ξ : E) • (((ξ⁻¹ : Eˣ) : E) • u)
      rw [smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]
    rw [mat_mul, ← Matrix.mulVec_mulVec, hB, incM_mulVec, ← hu, h1, incV_smul, Matrix.mulVec_smul, (hγ _).2]
  let f : Eˣ → {w : IsoV σ J // ∃ l : (AE F E)ˣ, mat (γ w * t⁻¹) *ᵥ incV F x = l.1 • incV F x} :=
    fun ξ => ⟨wv ξ, Units.map (inclR (F := F) (AF F)).toMonoidHom ξ, eig ξ⟩
  have finj : Function.Injective f := by
    intro ξ η h
    have h2 : ((ξ⁻¹ : Eˣ) : E) • u = ((η⁻¹ : Eˣ) : E) • u := congrArg (fun z => z.1.1) h
    have h3 : ((ξ⁻¹ : Eˣ) : E) = ((η⁻¹ : Eˣ) : E) := smul_left_injective E hu0 h2
    exact inv_injective (Units.ext h3)
  have fsurj : Function.Surjective f := by
    rintro ⟨w, l, hl0⟩
    haveI : Nontrivial (AE F E) := (inclR_inj (F := F) (E := E)).nontrivial
    obtain ⟨P, hP⟩ := exists_rat (mul_mem (hγ w).1 (inv_mem ht))
    have hl := hl0
    rw [hP, incM_mulVec] at hl
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra hc; push_neg at hc; exact hx (funext hc)
    have ei : inclR (F := F) (AF F) ((P *ᵥ x) i) = l.1 * inclR (F := F) (AF F) (x i) := by
      have := congrFun hl i
      simpa [incV] using this
    have hPi : (P *ᵥ x) i ≠ 0 := by
      intro h0
      rw [h0, map_zero] at ei
      have hu1 : IsUnit (l.1 * inclR (F := F) (AF F) (x i)) :=
        l.isUnit.mul ((isUnit_iff_ne_zero.2 hi).map _)
      rw [← ei] at hu1
      exact not_isUnit_zero hu1
    set ξ0 : E := (P *ᵥ x) i * (x i)⁻¹ with hξ0
    have hξ0ne : ξ0 ≠ 0 := mul_ne_zero hPi (inv_ne_zero hi)
    have hl1 : l.1 = inclR (F := F) (AF F) ξ0 := by
      have hxi : IsUnit (inclR (F := F) (AF F) (x i)) := (isUnit_iff_ne_zero.2 hi).map _
      apply hxi.mul_left_injective
      simp only
      rw [← ei, ← map_mul, hξ0, mul_assoc, inv_mul_cancel₀ hi, mul_one]

    have hPx : incV F (P *ᵥ x) = incV F (ξ0 • x) := by rw [hl, hl1, incV_smul]

    have hpw : mat (γ w * t⁻¹) *ᵥ incV F (A *ᵥ w.1) = incV F x := by
      rw [← incM_mulVec, ← hA, Matrix.mulVec_mulVec, ← mat_mul, mul_assoc, inv_mul_cancel, mul_one]
      exact (hγ w).2
    have hpx : mat (γ w * t⁻¹) *ᵥ incV F (ξ0⁻¹ • x) = incV F x := by
      have hPx' : P *ᵥ x = ξ0 • x := incV_inj hPx
      rw [hP, incM_mulVec, Matrix.mulVec_smul, hPx', smul_smul, inv_mul_cancel₀ hξ0ne, one_smul]
    have hinvp : mat (γ w * t⁻¹)⁻¹ * mat (γ w * t⁻¹) = 1 := by rw [← mat_mul, inv_mul_cancel, mat_one]
    have hAw : incV F (A *ᵥ w.1) = incV F (ξ0⁻¹ • x) := by
      rw [← Matrix.one_mulVec (incV F (A *ᵥ w.1)), ← Matrix.one_mulVec (incV F (ξ0⁻¹ • x)), ← hinvp,
        ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hpw, hpx]
    have hw : w.1 = ξ0⁻¹ • u := by
      rw [← Matrix.one_mulVec w.1, ← hBA, ← Matrix.mulVec_mulVec, incV_inj hAw, Matrix.mulVec_smul]
    refine ⟨Units.mk0 ξ0 hξ0ne, Subtype.ext (Subtype.ext ?_)⟩
    show ((Units.mk0 ξ0 hξ0ne)⁻¹ : Eˣ).val • u = w.1
    rw [Units.val_inv_eq_inv_val, Units.val_mk0, hw]
  refine ⟨(Equiv.ofBijective f ⟨finj, fsurj⟩).symm, fun w => ?_⟩
  have hw : f ((Equiv.ofBijective f ⟨finj, fsurj⟩).symm w) = w := (Equiv.ofBijective f ⟨finj, fsurj⟩).apply_symm_apply w
  have := eig ((Equiv.ofBijective f ⟨finj, fsurj⟩).symm w)
  conv_lhs => rw [← hw]
  exact this

end GlobalTheory.WittFibre

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ _ J x hx hxx γ hγ t ht` and use `GlobalTheory.WittFibre.wittFibre_equiv F E σ J x hx hxx γ hγ t ht`.
-/
example : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E), x ≠ 0 → form σ J x x = 0 →
    ∀ γ : IsoV σ J → UA σ J, IsWitt (σ := σ) (J := J) x γ → ∀ t ∈ ratU σ J,
    ∃ κ : {w : IsoV σ J // ∃ l : (AE F E)ˣ, mat (γ w * t⁻¹) *ᵥ incV F x = l.1 • incV F x} ≃ Eˣ,
      ∀ w, mat (γ w.1 * t⁻¹) *ᵥ incV F x = (inclR (F := F) (AF F) (κ w : E)) • incV F x := fun F E _ _ _ _ _ σ _ J x hx hxx γ hγ t ht => GlobalTheory.WittFibre.wittFibre_equiv F E σ J x hx hxx γ hγ t ht

end
