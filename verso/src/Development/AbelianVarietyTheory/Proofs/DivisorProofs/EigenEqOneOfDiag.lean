import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumHeisenbergEigenDoubledLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledStabilizerWeilOperatorTransportsLatticeEi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceDoubledEigenfunctionsLineVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumEigenInertPlaceLatticeStabiliser
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumEigenvalueEqOneInertPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBoxTensorLeftFixedLinearApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagOneNegOneConjAntidiagonalStabilizerMemStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc GlobalTheory.ThK
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.PairDblVac

open GlobalTheory.DblVacEigen hiding doubled_vac_eigen
open GlobalTheory.DblVacTransport (cols_mem)
open GlobalTheory.VDblEig (boxFun_mem_SB' star_mem_SB')
open GlobalTheory.DblVacSiegel hiding eigen_eq_one_of_diag
open GlobalTheory.DblGenV (KD_mul KD_inv PDiag_inv)

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n d X W M χX χW om r₀ s₀ r₁ s₁ hT v w _ _ d' hd' dd hdd θ _ hvac w₁ hw₁ w₂ hw₂`. Establish `hSB` using `(hT.good.vac v).1`. Establish `hψ : ∀ t, ‖B.ψ t‖ = 1` using `GlobalTheory.StdCharWeilDatum.norm_psi hT.base.std`. Establish `hstar : ∀ t, star (B.ψ t) = B.ψ (-t)`. Introduce `t`.

Rewrite using `[AddChar.map_neg_eq_inv, Complex.inv_def, Complex.normSq_eq_norm_sq, hψ t]`. Simplify using the standard rewrite rules. Establish `hAt : ∀ γ ∈ latAtV X W v, At (evFin F v) γ` using `(GlobalTheory.LatVac.latAtV_at_stable X W v).1`. Establish `hco : ∀ γ ∈ latAtV X W v, At (evFin F v) (M.co.e γ).1 ∧ At (evFin F v) (M.co.e γ).2`. Introduce `γ hγ`.

Establish `e : ∀ u, evFin F v u = 0 → u • M.co.e γ = 0` using `fun u hu => by`. Rewrite using `[← map_smul, hAt γ hγ u hu, map_zero]`. Conclude with `⟨fun u hu => congrArg Prod.fst (e u hu), fun u hu => congrArg Prod.snd (e u hu)⟩`. Establish `h1` using `eigen_pointwise v B.ψ hSB (M.co.e w₁) (hco w₁ hw₁).1 (hco w₁ hw₁).2 _ (hvac w₁ hw₁)`. Establish `h2` using `eigen_pointwise v B.ψ hSB (M.co.e w₂) (hco w₂ hw₂).1 (hco w₂ hw₂).2 _ (hvac w₂ hw₂)`.

Establish `h2' : ∀ z, B.ψ (z ⬝ᵥ (-(M.co.e w₂).2) + ⅟(2 : AF F) * ((M.co.e w₂).1 ⬝ᵥ (-(M.co.e w₂).2))) * (fun x => star (M.vac v x)) (fun i => evFin F v ((z + (M.co.e w₂).1) i)) = star (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F` using `F) (AF F) (θ : E)) (incM F X.J) (incM F W.J) w₂ w₂)) * (fun x => star (M.vac v x)) (fun i => evFin F v (z i)) := by`. Introduce `z`. Establish `e` using `congrArg star (h2 z)`. Simplify using `only [star_mul, hstar] at e`. Rewrite using `[hstar, show z ⬝ᵥ (-(M.co.e w₂).2) + ⅟(2 : AF F) * ((M.co.e w₂).1 ⬝ᵥ (-(M.co.e w₂).2)) = -(z ⬝ᵥ (M.co.e w₂).2 + ⅟(2 : AF F) * ((M.co.e w₂).1 ⬝ᵥ (M.co.e w₂).2)) by`.

Rewrite using `[dotProduct_neg, dotProduct_neg]`. Use the proof step `ring]`. Take the linear combination `e`. Establish `hbox` using `acts_box v B.ψ (φ₁ := M.vac v) (φ₂ := fun x => star (M.vac v x)) (M.co.e w₁).1 (M.co.e w₁).2 (M.co.e w₂).1 (-(M.co.e w₂).2) (hco w₁ hw₁).1 (hco w₂ hw₂).1 _ _ h1 h2'`. Establish `hrho : dd.rho B.ψ (Matrix.fromCols w₁ᵀ w₂ᵀ) = schr B.ψ (Sum.elim (M.co.e w₁).1 (M.co.e w₂).1, Sum.elim (M.co.e w₁).2 (-(M.co.e w₂).2))`.

Rewrite using `[Darboux.rho, hdd, hd', hd']`. Establish `hS : symp (cA σ) (inclR (F` using `F) (AF F) (θ : E)) (incM F W.J) (dbl (incM F X.J)) (Matrix.fromCols w₁ᵀ w₂ᵀ) (Matrix.fromCols w₁ᵀ w₂ᵀ) = symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J) w₁ w₁ - symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J) w₂ w₂ := by`. Unfold `symp`. Rewrite using `[hTens_dbl, hTens_transpose, hTens_transpose, mul_sub, map_sub]`. Establish `hc : B.ψ (⅟(2 : AF F) * (symp (cA σ) (inclR (F` using `F) (AF F) (θ : E)) (incM F X.J) (incM F W.J) w₁ w₁ - symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J) w₂ w₂)) = B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J) w₁ w₁) * star (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := …`.

Rewrite using `[hstar, ← AddChar.map_add_eq_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hrho, hS, hc]`. Conclude with `hbox`.
-/
theorem vac_eigen : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r₀ s₀ r₁ s₁ : ℕ),
    IsPair B M χX χW om r₀ s₀ r₁ s₁ →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → UnrAt χW w →
    ∀ (d' : Darboux (symp (cA σ) (-1 : AE F E) (incM F W.J) (incM F X.J)) (Fin n × Fin d)),
    (∀ x : Matrix (Fin n) (Fin d) (AE F E), d'.e xᵀ = M.co.e x) →
    ∀ (dd : Darboux (symp (cA σ) (-1 : AE F E) (incM F W.J) (dbl (incM F X.J))) ((Fin n × Fin d) ⊕ (Fin n × Fin d))),
    IsDblCoord (cA σ) (-1 : AE F E) (incM F W.J) (incM F X.J) d' dd →
    ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 →
    (∀ γ ∈ latAtV X W v, Acts (evFin F v) (M.co.rho B.ψ γ) (M.vac v)
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J) γ γ) • M.vac v)) →
    (∀ w₁ ∈ latAtV X W v, ∀ w₂ ∈ latAtV X W v,
      Acts (evFin F v) (dd.rho B.ψ (Matrix.fromCols w₁ᵀ w₂ᵀ)) (boxFun (M.vac v) (fun x => star (M.vac v x)))
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F W.J) (dbl (incM F X.J))
          (Matrix.fromCols w₁ᵀ w₂ᵀ) (Matrix.fromCols w₁ᵀ w₂ᵀ)) • (boxFun (M.vac v) (fun x => star (M.vac v x))))) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r₀ s₀ r₁ s₁ hT v w _ _ d' hd' dd hdd θ _ hvac w₁ hw₁ w₂ hw₂
  have hSB := (hT.good.vac v).1
  have hψ : ∀ t, ‖B.ψ t‖ = 1 := GlobalTheory.StdCharWeilDatum.norm_psi hT.base.std
  have hstar : ∀ t, star (B.ψ t) = B.ψ (-t) := by
    intro t
    rw [AddChar.map_neg_eq_inv, Complex.inv_def, Complex.normSq_eq_norm_sq, hψ t]
    simp
  have hAt : ∀ γ ∈ latAtV X W v, At (evFin F v) γ := (GlobalTheory.LatVac.latAtV_at_stable X W v).1
  have hco : ∀ γ ∈ latAtV X W v, At (evFin F v) (M.co.e γ).1 ∧ At (evFin F v) (M.co.e γ).2 := by
    intro γ hγ
    have e : ∀ u, evFin F v u = 0 → u • M.co.e γ = 0 := fun u hu => by
      rw [← map_smul, hAt γ hγ u hu, map_zero]
    exact ⟨fun u hu => congrArg Prod.fst (e u hu), fun u hu => congrArg Prod.snd (e u hu)⟩
  have h1 := eigen_pointwise v B.ψ hSB (M.co.e w₁) (hco w₁ hw₁).1 (hco w₁ hw₁).2 _ (hvac w₁ hw₁)
  have h2 := eigen_pointwise v B.ψ hSB (M.co.e w₂) (hco w₂ hw₂).1 (hco w₂ hw₂).2 _ (hvac w₂ hw₂)
  have h2' : ∀ z, B.ψ (z ⬝ᵥ (-(M.co.e w₂).2) + ⅟(2 : AF F) * ((M.co.e w₂).1 ⬝ᵥ (-(M.co.e w₂).2))) *
      (fun x => star (M.vac v x)) (fun i => evFin F v ((z + (M.co.e w₂).1) i)) =
      star (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J) w₂ w₂)) * (fun x => star (M.vac v x)) (fun i => evFin F v (z i)) := by
    intro z
    have e := congrArg star (h2 z)
    simp only [star_mul, hstar] at e
    rw [hstar, show z ⬝ᵥ (-(M.co.e w₂).2) + ⅟(2 : AF F) * ((M.co.e w₂).1 ⬝ᵥ (-(M.co.e w₂).2)) =
      -(z ⬝ᵥ (M.co.e w₂).2 + ⅟(2 : AF F) * ((M.co.e w₂).1 ⬝ᵥ (M.co.e w₂).2)) by
        rw [dotProduct_neg, dotProduct_neg]; ring]
    linear_combination e
  have hbox := acts_box v B.ψ (φ₁ := M.vac v) (φ₂ := fun x => star (M.vac v x)) (M.co.e w₁).1 (M.co.e w₁).2 (M.co.e w₂).1 (-(M.co.e w₂).2)
    (hco w₁ hw₁).1 (hco w₂ hw₂).1 _ _ h1 h2'
  have hrho : dd.rho B.ψ (Matrix.fromCols w₁ᵀ w₂ᵀ) = schr B.ψ (Sum.elim (M.co.e w₁).1 (M.co.e w₂).1,
      Sum.elim (M.co.e w₁).2 (-(M.co.e w₂).2)) := by
    rw [Darboux.rho, hdd, hd', hd']
  have hS : symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F W.J) (dbl (incM F X.J))
      (Matrix.fromCols w₁ᵀ w₂ᵀ) (Matrix.fromCols w₁ᵀ w₂ᵀ) = symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J) w₁ w₁ - symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J) w₂ w₂ := by
    unfold symp
    rw [hTens_dbl, hTens_transpose, hTens_transpose, mul_sub, map_sub]
  have hc : B.ψ (⅟(2 : AF F) * (symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J) w₁ w₁ - symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J) w₂ w₂)) = B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J) w₁ w₁) * star (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J) w₂ w₂)) := by
    rw [hstar, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  rw [hrho, hS, hc]
  exact hbox

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n d X W M χX χW om r₀ s₀ r₁ s₁ _ v w _ _ d' _ dd _ θ _ _ omd hsp g hg φ hφ φ₁ _ hfix hact w₁ hw₁ w₂ hw₂ r hr`. Distinguish the cases in `h0 : φ₁ = 0`. Substitute `h0` using the available equality. Use function extensionality and compare the values at `x`. Simplify using `[Darboux.rho, schr, tens]`.

Establish `hr' : Rest (evFin F v) φ r` using `GlobalTheory.RestCofactor.rest_of_rest v φ₁ φ r h0 hφ hr`. Take `⟨h1m, h2m⟩` from `cols_mem X W v (GlobalTheory.DblVac.matD g⁻¹) (fun z hz => (hg.2 z hz).2) hw₁ hw₂`. Establish `hsplit : Matrix.fromCols w₁ᵀ w₂ᵀ * (GlobalTheory.DblVac.matD g⁻¹)ᵀ = Matrix.fromCols (((Matrix.fromCols w₁ᵀ w₂ᵀ * (GlobalTheory.DblVac.matD g⁻¹)ᵀ).toCols₁)ᵀ)ᵀ (((Matrix.fromCols w₁ᵀ w₂ᵀ * (GlobalTheory.DblVac.matD g⁻¹)ᵀ).toCols₂)ᵀ)ᵀ`. Rewrite using `[Matrix.transpose_transpose, Matrix.transpose_transpose, Matrix.fromCols_toCols]`. Establish `hback : actB (cA σ) g (Matrix.fromCols w₁ᵀ w₂ᵀ * (GlobalTheory.DblVac.matD g⁻¹)ᵀ) = Matrix.fromCols w₁ᵀ w₂ᵀ`.

Express the relevant statement in the definitionally equal form `Matrix.fromCols w₁ᵀ w₂ᵀ * (GlobalTheory.DblVac.matD g⁻¹)ᵀ * (GlobalTheory.DblVac.matD g)ᵀ = _`. Establish `e : GlobalTheory.DblVac.matD g * GlobalTheory.DblVac.matD g⁻¹ = 1` using `Units.mul_inv g.1`. Rewrite using `[Matrix.mul_assoc, ← Matrix.transpose_mul, e, Matrix.transpose_one, Matrix.mul_one]`. Establish `hsy` using `GlobalTheory.VacTransport.symp_mul_transpose (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F W.J) (dbl (incM F X.J)) (GlobalTheory.DblVac.matD g⁻¹) (g⁻¹).2 (Matrix.fromCols w₁ᵀ w₂ᵀ) (Matrix.fromCols w₁ᵀ w₂ᵀ)`. Establish `hf` using `hfix _ h1m _ h2m r hr'`.

Rewrite `hf` using `[← hsplit, hsy]`. Establish `h1` using `hsp.2.1.impl g (Matrix.fromCols w₁ᵀ w₂ᵀ * (GlobalTheory.DblVac.matD g⁻¹)ᵀ) _ hr'.2`. Rewrite `h1` using `[hback, hf, GlobalTheory.VacTransport.tens_smul, map_smul, hact r hr']`. Rewrite using `[← h1, GlobalTheory.VacTransport.tens_smul]`.
-/
theorem transport : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r₀ s₀ r₁ s₁ : ℕ),
    IsPair B M χX χW om r₀ s₀ r₁ s₁ →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → UnrAt χW w →
    ∀ (d' : Darboux (symp (cA σ) (-1 : AE F E) (incM F W.J) (incM F X.J)) (Fin n × Fin d)),
    (∀ x : Matrix (Fin n) (Fin d) (AE F E), d'.e xᵀ = M.co.e x) →
    ∀ (dd : Darboux (symp (cA σ) (-1 : AE F E) (incM F W.J) (dbl (incM F X.J))) ((Fin n × Fin d) ⊕ (Fin n × Fin d))),
    IsDblCoord (cA σ) (-1 : AE F E) (incM F W.J) (incM F X.J) d' dd →
    ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 →
    (∀ γ ∈ latAtV X W v, Acts (evFin F v) (M.co.rho B.ψ γ) (M.vac v)
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J) γ γ) • M.vac v)) →
    ∀ (omd : GlobalTheory.DblVac.UD σ X →* Module.End ℂ (((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) → ℂ)),
    IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1 : AE F E) (incM F W.J) (dbl (incM F X.J)) dd χW (diagCols (Fin n)) omd →
    ∀ g ∈ GlobalTheory.DblVac.KD σ X v, ∀ φ ∈ SB ((Fin n × Fin d) ⊕ (Fin n × Fin d) → Fv F v), ∀ φ₁ ∈ SB ((Fin n × Fin d) ⊕ (Fin n × Fin d) → Fv F v),
    (∀ w₁ ∈ latAtV X W v, ∀ w₂ ∈ latAtV X W v,
      Acts (evFin F v) (dd.rho B.ψ (Matrix.fromCols w₁ᵀ w₂ᵀ)) φ
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F W.J) (dbl (incM F X.J))
          (Matrix.fromCols w₁ᵀ w₂ᵀ) (Matrix.fromCols w₁ᵀ w₂ᵀ)) • φ)) → Acts (evFin F v) (omd g) φ φ₁ →
    (∀ w₁ ∈ latAtV X W v, ∀ w₂ ∈ latAtV X W v,
      Acts (evFin F v) (dd.rho B.ψ (Matrix.fromCols w₁ᵀ w₂ᵀ)) φ₁
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F W.J) (dbl (incM F X.J))
          (Matrix.fromCols w₁ᵀ w₂ᵀ) (Matrix.fromCols w₁ᵀ w₂ᵀ)) • φ₁)) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r₀ s₀ r₁ s₁ _ v w _ _ d' _ dd _ θ _ _ omd hsp g hg φ hφ φ₁ _ hfix hact w₁ hw₁ w₂ hw₂ r hr
  by_cases h0 : φ₁ = 0
  · subst h0
    funext x
    simp [Darboux.rho, schr, tens]
  have hr' : Rest (evFin F v) φ r := GlobalTheory.RestCofactor.rest_of_rest v φ₁ φ r h0 hφ hr
  obtain ⟨h1m, h2m⟩ := cols_mem X W v (GlobalTheory.DblVac.matD g⁻¹) (fun z hz => (hg.2 z hz).2) hw₁ hw₂
  have hsplit : Matrix.fromCols w₁ᵀ w₂ᵀ * (GlobalTheory.DblVac.matD g⁻¹)ᵀ =
      Matrix.fromCols (((Matrix.fromCols w₁ᵀ w₂ᵀ * (GlobalTheory.DblVac.matD g⁻¹)ᵀ).toCols₁)ᵀ)ᵀ
        (((Matrix.fromCols w₁ᵀ w₂ᵀ * (GlobalTheory.DblVac.matD g⁻¹)ᵀ).toCols₂)ᵀ)ᵀ := by
    rw [Matrix.transpose_transpose, Matrix.transpose_transpose, Matrix.fromCols_toCols]
  have hback : actB (cA σ) g (Matrix.fromCols w₁ᵀ w₂ᵀ * (GlobalTheory.DblVac.matD g⁻¹)ᵀ) = Matrix.fromCols w₁ᵀ w₂ᵀ := by
    change Matrix.fromCols w₁ᵀ w₂ᵀ * (GlobalTheory.DblVac.matD g⁻¹)ᵀ * (GlobalTheory.DblVac.matD g)ᵀ = _
    have e : GlobalTheory.DblVac.matD g * GlobalTheory.DblVac.matD g⁻¹ = 1 := Units.mul_inv g.1
    rw [Matrix.mul_assoc, ← Matrix.transpose_mul, e, Matrix.transpose_one, Matrix.mul_one]
  have hsy := GlobalTheory.VacTransport.symp_mul_transpose (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F W.J)
    (dbl (incM F X.J)) (GlobalTheory.DblVac.matD g⁻¹) (g⁻¹).2 (Matrix.fromCols w₁ᵀ w₂ᵀ) (Matrix.fromCols w₁ᵀ w₂ᵀ)
  have hf := hfix _ h1m _ h2m r hr'
  rw [← hsplit, hsy] at hf
  have h1 := hsp.2.1.impl g (Matrix.fromCols w₁ᵀ w₂ᵀ * (GlobalTheory.DblVac.matD g⁻¹)ᵀ) _ hr'.2
  rw [hback, hf, GlobalTheory.VacTransport.tens_smul, map_smul, hact r hr'] at h1
  rw [← h1, GlobalTheory.VacTransport.tens_smul]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n d X W M χX χW om r₀ s₀ r₁ s₁ hT v w hw hv d' hd' dd hdc θ hθ hvac φ hφSB hφ`. Establish `hψ` using `hT.base.std`. Establish `hn` using `GlobalTheory.StdCharFromIsStd.norm_psi hψ`. Establish `hnv : ∀ t, ‖GlobalTheory.LatVac.psiAt B.ψ v t‖ = 1` using `fun t => hn (GlobalTheory.LatVac.liftV v t)`. Use `set Λ := latAtV X W v with hΛ`.

Establish `hat : ∀ γ ∈ Λ, At (evFin F v) γ` using `(GlobalTheory.LatVac.latAtV_at_stable X W v).1`. Establish `hatT : ∀ γ ∈ Λ, At (evFin F v) γᵀ` using `fun γ h u hu => by`. Rewrite using `[← Matrix.transpose_smul, hat γ h u hu, Matrix.transpose_zero]`. Take `⟨hvSB, hv0, -⟩` from `hT.good.vac v`. Use `set φ₀ := M.vac v with hφ₀`.

Use `set φd := boxFun φ₀ (fun x => star (φ₀ x)) with hφd`. Establish `loc : ∀ {κ : Type} [Fintype κ] {W' : Type} [AddCommGroup W'] [Module (AF F) W'] {Bf : W' → W' → AF F} (d : Darboux Bf κ) (f : (κ → Fv F v) → ℂ), f ∈ SB _ → ∀ γ, At (evFin F v) γ → ∀ c : ℂ, Acts (evFin F v) (d.rho B.ψ γ) f (c • f) → schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTh …`. Introduce `κ _ W' _ _ Bf d f hf γ hγ c h`. Take `⟨r, hr, x₀, hx₀⟩` from `GlobalTheory.RestComplement.exists_rest_ne_zero v f hf`. Use `GlobalTheory.DblVacLine.eq_of_tens v hr.1 hx₀ ?_` and prove the remaining obligations.

Rewrite using `[← GlobalTheory.VacBridge.rho_acts_locCo d B.ψ v γ hγ f r hr]`. Conclude with `h r hr`. Establish `hco : ∀ w₁ w₂ : Matrix (Fin n) (Fin d) (AE F E), GlobalTheory.LatVac.locCo dd v (Matrix.fromCols w₁ᵀ w₂ᵀ) = (Sum.elim (GlobalTheory.LatVac.locCo M.co v w₁).1 (GlobalTheory.LatVac.locCo M.co v w₂).1, Sum.elim (GlobalTheory.LatVac.locCo M.co v w₁).2 (-(GlobalTheory.LatVac.locCo M.c …`. Introduce `w₁ w₂`. Express the relevant statement in the definitionally equal form `((fun k => evFin F v ((dd.e (Matrix.fromCols w₁ᵀ w₂ᵀ)).1 k)), fun k => evFin F v ((dd.e (Matrix.fromCols w₁ᵀ w₂ᵀ)).2 k)) = _`.

Rewrite using `[hdc, hd', hd']`. Use `Prod.ext (funext fun k => ?_) (funext fun k => ?_)` and prove the remaining obligations. Apply the tactic sequence `cases k <;> rfl`. Consider the cases of `k with`. Consider the case `inl k => rfl`.

Consider the case `inr k => exact map_neg (evFin F v) _`. Set `χ : Matrix (Fin n) (Fin d) (AE F E) → ℂ` to `fun γ => B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J) γ γ)`. Set `cf : Matrix (Fin n) (Fin d) (AE F E) → Matrix (Fin n) (Fin d) (AE F E) → ℂ` to `fun w₁ w₂ => B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F W.J) (dbl (incM F X.J)) (Matrix.fromCols w₁ᵀ w₂ᵀ) (Matrix.fromCols w₁ᵀ w₂ᵀ))`. Establish `ht : ∀ w : Matrix (Fin n) (Fin d) (AE F E), symp (R` using `AF F) (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F W.J) (incM F X.J) wᵀ wᵀ = symp (R := AF F) (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J) w w := fun w => by`. Rewrite using `[GlobalTheory.WeilTr.symp_transpose (cA σ) _ (incM F X.J) (incM F W.J) wᵀ wᵀ, Matrix.transpose_transpose]`.

Establish `hcf : ∀ w₁ w₂, cf w₁ w₂ = χ w₁ * star (χ w₂)`. Introduce `w₁ w₂`. Simplify using `only [cf, χ]`. Rewrite using `[GlobalTheory.DblVacLine.symp_dbl, GlobalTheory.DblVacLine.star_eq_neg B.ψ hn, ht, ht, ← AddChar.map_add_eq_mul, mul_sub, sub_eq_add_neg]`. Establish `hvl : ∀ γ ∈ Λ, schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v γ) φ₀ = χ γ • φ₀` using `fun γ h => loc M.co φ₀ hvSB γ (hat γ h) _ (hvac γ h)`.

Establish `hφl : ∀ w₁ ∈ Λ, ∀ w₂ ∈ Λ, schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v (Matrix.fromCols w₁ᵀ w₂ᵀ)) φ = cf w₁ w₂ • φ` using `fun w₁ h₁ w₂ h₂ => loc dd φ hφSB _ (GlobalTheory.DblVacLine.at_fromCols v (hatT w₁ h₁) (hatT w₂ h₂)) _ (hφ w₁ h₁ w₂ h₂)`. Establish `hdl : ∀ w₁ ∈ Λ, ∀ w₂ ∈ Λ, schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v (Matrix.fromCols w₁ᵀ w₂ᵀ)) φd = cf w₁ w₂ • φd`. Introduce `w₁ h₁ w₂ h₂`. Rewrite using `[hco, hφd, GlobalTheory.DblVacLine.schr_box _ hnv, hvl w₁ h₁, hvl w₂ h₂, hcf]`. Use function extensionality and compare the values at `x`.

Simplify using `only [boxFun, Pi.smul_apply, smul_eq_mul, star_mul']`. Expand and normalize the polynomial expressions, which then agree. Take `⟨c, hc0, hcb⟩` from `GlobalTheory.LatBound.locCo_latAtV_bounded X W v M.co hT.herm.lat hT.skew.lat`. Establish `hsd` using `GlobalTheory.LatSelfDualAll.latAtV_selfDual F E σ B _ _ X W _ _ _ _ hT.base hT.herm hT.skew v`. Establish `hfill` using `GlobalTheory.SelfDualFirstProj.exists_pair_of_annihilator v (GlobalTheory.LatVac.psiAt B.ψ v) (Λ.map (GlobalTheory.LatVac.locCo M.co v)) c hc0 (fun x => (hT.base.inert v w hw).2.2 x) (GlobalTheory.LatVac.DualLoc.map_selfDual v M.co B.ψ Λ hat hsd) (fun l hl i => by`.

Take `⟨γ, hγ, rfl⟩` from `AddSubgroup.mem_map.mp hl`. Conclude with `hcb γ hγ i)`. Establish `hφd0 : φd ≠ 0`. Take `⟨t, ht⟩` from `Function.ne_iff.mp hv0`. Use `Function.ne_iff.mpr ⟨Sum.elim t t, ?_⟩` and prove the remaining obligations.

Use `show φ₀ t * star (φ₀ t) ≠ 0`. Conclude with `mul_ne_zero ht (star_ne_zero.mpr ht)`. Take `⟨c', hc'⟩` from `GlobalTheory.VacUniqInert.eq_smul_of_eigen (GlobalTheory.LatVac.psiAt B.ψ v) (fun i : Λ × Λ => GlobalTheory.LatVac.locCo dd v (Matrix.fromCols i.1.1ᵀ i.2.1ᵀ)) (fun i => cf i.1.1 i.2.1) (fun u hu => by`. Establish `eu : u = Sum.elim (u ∘ Sum.inl) (u ∘ Sum.inr)` using `(Sum.elim_comp_inl_inr u).symm`. Take `⟨y₁, γ₁, h₁, e₁⟩` from `hfill (u ∘ Sum.inl) (by`.

Introduce and unpack `b ⟨γ, hγ, he⟩`. Use `hu (⟨γ, hγ⟩, 0) (by` as an intermediate fact. Simplify using `only [hco, he, ZeroMemClass.coe_zero, map_zero]`. Apply the tactic sequence `funext k; cases k <;> rfl)`. Simplify using `only [hco, he, ZeroMemClass.coe_zero, map_zero] at this`.

Rewrite `this` using `[eu, sumElim_dotProduct_sumElim]`. Simplify using `using this)`. Take `⟨y₂, γ₂, h₂, e₂⟩` from `hfill (u ∘ Sum.inr) (by`. Introduce and unpack `b ⟨γ, hγ, he⟩`. Use `hu (0, ⟨-γ, neg_mem hγ⟩) (by` as an intermediate fact.

Simplify using `only [hco, he, ZeroMemClass.coe_zero, map_zero, map_neg]`. Apply the tactic sequence `funext k; cases k <;> simp)`. Simplify using `only [hco, he, ZeroMemClass.coe_zero, map_zero, map_neg] at this`. Rewrite `this` using `[eu, sumElim_dotProduct_sumElim]`. Simplify using `using this)`.

Use `⟨(⟨γ₁, h₁⟩, ⟨γ₂, h₂⟩), ?_⟩` and prove the remaining obligations. Simplify using `only [hco, e₁, e₂]`. Conclude with `eu.symm) φ φd`. Use the proof step `(fun i => hφl _ i.1.2 _ i.2.2) (fun i => hdl _ i.1.2 _ i.2.2) hφd0`. Conclude with `⟨c', hc'⟩`.
-/
theorem vdbl_line : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r₀ s₀ r₁ s₁ : ℕ),
    IsPair B M χX χW om r₀ s₀ r₁ s₁ →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → UnrAt χW w →
    ∀ (d' : Darboux (symp (cA σ) (-1 : AE F E) (incM F W.J) (incM F X.J)) (Fin n × Fin d)),
    (∀ x : Matrix (Fin n) (Fin d) (AE F E), d'.e xᵀ = M.co.e x) →
    ∀ (dd : Darboux (symp (cA σ) (-1 : AE F E) (incM F W.J) (dbl (incM F X.J))) ((Fin n × Fin d) ⊕ (Fin n × Fin d))),
    IsDblCoord (cA σ) (-1 : AE F E) (incM F W.J) (incM F X.J) d' dd →
    ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 →
    (∀ γ ∈ latAtV X W v, Acts (evFin F v) (M.co.rho B.ψ γ) (M.vac v)
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J) γ γ) • M.vac v)) →
    ∀ φ ∈ SB ((Fin n × Fin d) ⊕ (Fin n × Fin d) → Fv F v), (∀ w₁ ∈ latAtV X W v, ∀ w₂ ∈ latAtV X W v,
      Acts (evFin F v) (dd.rho B.ψ (Matrix.fromCols w₁ᵀ w₂ᵀ)) φ
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F W.J) (dbl (incM F X.J))
          (Matrix.fromCols w₁ᵀ w₂ᵀ) (Matrix.fromCols w₁ᵀ w₂ᵀ)) • φ)) → ∃ c : ℂ, φ = c • (boxFun (M.vac v) (fun x => star (M.vac v x))) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r₀ s₀ r₁ s₁ hT v w hw hv d' hd' dd hdc θ hθ hvac φ hφSB hφ
  classical
  have hψ := hT.base.std
  have hn := GlobalTheory.StdCharFromIsStd.norm_psi hψ
  have hnv : ∀ t, ‖GlobalTheory.LatVac.psiAt B.ψ v t‖ = 1 := fun t => hn (GlobalTheory.LatVac.liftV v t)
  set Λ := latAtV X W v with hΛ
  have hat : ∀ γ ∈ Λ, At (evFin F v) γ := (GlobalTheory.LatVac.latAtV_at_stable X W v).1
  have hatT : ∀ γ ∈ Λ, At (evFin F v) γᵀ := fun γ h u hu => by
    rw [← Matrix.transpose_smul, hat γ h u hu, Matrix.transpose_zero]
  obtain ⟨hvSB, hv0, -⟩ := hT.good.vac v
  set φ₀ := M.vac v with hφ₀
  set φd := boxFun φ₀ (fun x => star (φ₀ x)) with hφd

  have loc : ∀ {κ : Type} [Fintype κ] {W' : Type} [AddCommGroup W'] [Module (AF F) W'] {Bf : W' → W' → AF F}
      (d : Darboux Bf κ) (f : (κ → Fv F v) → ℂ), f ∈ SB _ → ∀ γ, At (evFin F v) γ → ∀ c : ℂ,
      Acts (evFin F v) (d.rho B.ψ γ) f (c • f) →
      schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo d v γ) f = c • f := by
    intro κ _ W' _ _ Bf d f hf γ hγ c h
    obtain ⟨r, hr, x₀, hx₀⟩ := GlobalTheory.RestComplement.exists_rest_ne_zero v f hf
    refine GlobalTheory.DblVacLine.eq_of_tens v hr.1 hx₀ ?_
    rw [← GlobalTheory.VacBridge.rho_acts_locCo d B.ψ v γ hγ f r hr]
    exact h r hr
  have hco : ∀ w₁ w₂ : Matrix (Fin n) (Fin d) (AE F E),
      GlobalTheory.LatVac.locCo dd v (Matrix.fromCols w₁ᵀ w₂ᵀ) =
      (Sum.elim (GlobalTheory.LatVac.locCo M.co v w₁).1 (GlobalTheory.LatVac.locCo M.co v w₂).1,
        Sum.elim (GlobalTheory.LatVac.locCo M.co v w₁).2 (-(GlobalTheory.LatVac.locCo M.co v w₂).2)) := by
    intro w₁ w₂
    change ((fun k => evFin F v ((dd.e (Matrix.fromCols w₁ᵀ w₂ᵀ)).1 k)),
      fun k => evFin F v ((dd.e (Matrix.fromCols w₁ᵀ w₂ᵀ)).2 k)) = _
    rw [hdc, hd', hd']
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
    · cases k <;> rfl
    · cases k with
      | inl k => rfl
      | inr k => exact map_neg (evFin F v) _
  let χ : Matrix (Fin n) (Fin d) (AE F E) → ℂ := fun γ =>
    B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J) γ γ)
  let cf : Matrix (Fin n) (Fin d) (AE F E) → Matrix (Fin n) (Fin d) (AE F E) → ℂ := fun w₁ w₂ =>
    B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F W.J) (dbl (incM F X.J))
      (Matrix.fromCols w₁ᵀ w₂ᵀ) (Matrix.fromCols w₁ᵀ w₂ᵀ))
  have ht : ∀ w : Matrix (Fin n) (Fin d) (AE F E),
      symp (R := AF F) (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F W.J) (incM F X.J) wᵀ wᵀ =
        symp (R := AF F) (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J) w w := fun w => by
    rw [GlobalTheory.WeilTr.symp_transpose (cA σ) _ (incM F X.J) (incM F W.J) wᵀ wᵀ, Matrix.transpose_transpose]
  have hcf : ∀ w₁ w₂, cf w₁ w₂ = χ w₁ * star (χ w₂) := by
    intro w₁ w₂
    simp only [cf, χ]
    rw [GlobalTheory.DblVacLine.symp_dbl, GlobalTheory.DblVacLine.star_eq_neg B.ψ hn, ht, ht, ← AddChar.map_add_eq_mul, mul_sub,
      sub_eq_add_neg]
  have hvl : ∀ γ ∈ Λ, schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v γ) φ₀ = χ γ • φ₀ :=
    fun γ h => loc M.co φ₀ hvSB γ (hat γ h) _ (hvac γ h)
  have hφl : ∀ w₁ ∈ Λ, ∀ w₂ ∈ Λ,
      schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v (Matrix.fromCols w₁ᵀ w₂ᵀ)) φ = cf w₁ w₂ • φ :=
    fun w₁ h₁ w₂ h₂ => loc dd φ hφSB _ (GlobalTheory.DblVacLine.at_fromCols v (hatT w₁ h₁) (hatT w₂ h₂)) _ (hφ w₁ h₁ w₂ h₂)
  have hdl : ∀ w₁ ∈ Λ, ∀ w₂ ∈ Λ,
      schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v (Matrix.fromCols w₁ᵀ w₂ᵀ)) φd = cf w₁ w₂ • φd := by
    intro w₁ h₁ w₂ h₂
    rw [hco, hφd, GlobalTheory.DblVacLine.schr_box _ hnv, hvl w₁ h₁, hvl w₂ h₂, hcf]
    funext x
    simp only [boxFun, Pi.smul_apply, smul_eq_mul, star_mul']
    ring

  obtain ⟨c, hc0, hcb⟩ := GlobalTheory.LatBound.locCo_latAtV_bounded X W v M.co hT.herm.lat hT.skew.lat
  have hsd := GlobalTheory.LatSelfDualAll.latAtV_selfDual F E σ B _ _ X W _ _ _ _ hT.base hT.herm hT.skew v
  have hfill := GlobalTheory.SelfDualFirstProj.exists_pair_of_annihilator v (GlobalTheory.LatVac.psiAt B.ψ v)
    (Λ.map (GlobalTheory.LatVac.locCo M.co v)) c hc0 (fun x => (hT.base.inert v w hw).2.2 x)
    (GlobalTheory.LatVac.DualLoc.map_selfDual v M.co B.ψ Λ hat hsd)
    (fun l hl i => by
      obtain ⟨γ, hγ, rfl⟩ := AddSubgroup.mem_map.mp hl
      exact hcb γ hγ i)
  have hφd0 : φd ≠ 0 := by
    obtain ⟨t, ht⟩ := Function.ne_iff.mp hv0
    refine Function.ne_iff.mpr ⟨Sum.elim t t, ?_⟩
    show φ₀ t * star (φ₀ t) ≠ 0
    exact mul_ne_zero ht (star_ne_zero.mpr ht)
  obtain ⟨c', hc'⟩ := GlobalTheory.VacUniqInert.eq_smul_of_eigen (GlobalTheory.LatVac.psiAt B.ψ v)
    (fun i : Λ × Λ => GlobalTheory.LatVac.locCo dd v (Matrix.fromCols i.1.1ᵀ i.2.1ᵀ))
    (fun i => cf i.1.1 i.2.1) (fun u hu => by
      have eu : u = Sum.elim (u ∘ Sum.inl) (u ∘ Sum.inr) := (Sum.elim_comp_inl_inr u).symm
      obtain ⟨y₁, γ₁, h₁, e₁⟩ := hfill (u ∘ Sum.inl) (by
        rintro b ⟨γ, hγ, he⟩
        have := hu (⟨γ, hγ⟩, 0) (by
          simp only [hco, he, ZeroMemClass.coe_zero, map_zero]
          funext k; cases k <;> rfl)
        simp only [hco, he, ZeroMemClass.coe_zero, map_zero] at this
        rw [eu, sumElim_dotProduct_sumElim] at this
        simpa using this)
      obtain ⟨y₂, γ₂, h₂, e₂⟩ := hfill (u ∘ Sum.inr) (by
        rintro b ⟨γ, hγ, he⟩
        have := hu (0, ⟨-γ, neg_mem hγ⟩) (by
          simp only [hco, he, ZeroMemClass.coe_zero, map_zero, map_neg]
          funext k; cases k <;> simp)
        simp only [hco, he, ZeroMemClass.coe_zero, map_zero, map_neg] at this
        rw [eu, sumElim_dotProduct_sumElim] at this
        simpa using this)
      refine ⟨(⟨γ₁, h₁⟩, ⟨γ₂, h₂⟩), ?_⟩
      simp only [hco, e₁, e₂]
      exact eu.symm) φ φd
    (fun i => hφl _ i.1.2 _ i.2.2) (fun i => hdl _ i.1.2 _ i.2.2) hφd0
  exact ⟨c', hc'⟩

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n d X W M χX χW om r₀ s₀ r₁ s₁ hT v w hw hv d' hd' dd omd hdc hsp r hr g hg`. Take `⟨hvSB, -, θ, hθ, hvac⟩` from `hT.good.vac v`. Use `set φ := M.vac v with hφ`. Use `set vD := boxFun φ (fun x => star (φ x)) with hvD`. Use `set RD := boxFun r (fun x => star (r x)) with hRD`.

Establish `hvDSB : vD ∈ SB _` using `boxFun_mem_SB' hvSB (star_mem_SB' hvSB)`. Establish `hS : boxFun (tens (evFin F v) φ r) (fun x => star (tens (evFin F v) φ r x)) = tens (evFin F v) vD RD`. Use function extensionality and compare the values at `x`. Simplify using `only [tens, boxFun, hvD, hRD, Function.comp_def, star_mul']`. Expand and normalize the polynomial expressions, which then agree.

Establish `hRest : Rest (evFin F v) vD RD`. Use `⟨fun x z hz => ?_, ?_⟩` and prove the remaining obligations. Establish `hz1 : At (evFin F v) (z ∘ Sum.inl)` using `fun u hu => by`. Use function extensionality and compare the values at `i`. Conclude with `congrFun (hz u hu) (Sum.inl i)`.

Establish `hz2 : At (evFin F v) (z ∘ Sum.inr)` using `fun u hu => by`. Use function extensionality and compare the values at `i`. Conclude with `congrFun (hz u hu) (Sum.inr i)`. Use `show r ((x + z) ∘ Sum.inl) * star (r ((x + z) ∘ Sum.inr)) = r (x ∘ Sum.inl) * star (r (x ∘ Sum.inr))`. Rewrite using `[show (x + z) ∘ Sum.inl = x ∘ Sum.inl + z ∘ Sum.inl from rfl, show (x + z) ∘ Sum.inr = x ∘ Sum.inr + z ∘ Sum.inr from rfl, hr.1 _ _ hz1, hr.1 _ _ hz2]`.

Rewrite using `[← hS]`. Conclude with `GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ _ hr.2 _ (GlobalTheory.ConjSch.star_mem_schA _ _ hr.2)`. Establish `hU` using `hsp.2.1`. Choose the witnesses or unpack the hypotheses as in `⟨φ₁, hφ₁, hA⟩ : ∃ φ₁ ∈ SB _, Acts (evFin F v) (omd g) vD φ₁ := by`. Use `GlobalTheory.DblActs.acts_of_comm v B.ψ hT.base.std (omd g) (fun Φ hΦ => hU.pres g Φ hΦ) (fun μ hμ Φ hΦ => hU.unit μ hμ g Φ hΦ) ?_ vD hvDSB` and prove the remaining obligations.

Introduce `u hu x y Φ hΦ`. Use `set z := dd.e.symm (x, y) with hz`. Establish `he : dd.e (u • z) = (u • x, u • y)`. Rewrite using `[LinearEquiv.map_smul, hz, LinearEquiv.apply_symm_apply, Prod.smul_mk]`. Establish `h2` using `hg.1 u hu`.

Establish `e2 : actB (cA σ) g (u • z) = u • z`. Simplify using `only [actB]`. Use `set P := GlobalTheory.DblVac.matD g with hP`. Use `set c : AE F E := algebraMap (AF F) (AE F E) u with hc`. Establish `hs1 : u • z = c • z` using `(algebraMap_smul (AE F E) u z).symm`.

Establish `hs2 : u • (P - 1) = c • (P - 1)` using `(algebraMap_smul (AE F E) u (P - 1)).symm`. Establish `h2' : c • (P - 1) = 0` using `hs2 ▸ h2`. Establish `: (c • z) * Pᵀ - c • z = z * (c • (P - 1))ᵀ`. Rewrite using `[Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_sub, Matrix.transpose_one, Matrix.mul_sub, Matrix.mul_one, smul_sub]`. Rewrite `this` using `[h2']`.

Simplify using `only [Matrix.transpose_zero, Matrix.mul_zero, sub_eq_zero] at this`. Rewrite using `[hs1]`. Conclude with `this`. Establish `h3` using `hU.impl g (u • z) Φ hΦ`. Simplify using `only [Darboux.rho, he, e2] at h3`.

Conclude with `h3`. Establish `hE0` using `vac_eigen F E σ B n d X W M χX χW om r₀ s₀ r₁ s₁ hT v w hw hv d' hd' dd hdc θ hθ hvac`. Establish `hE1` using `transport F E σ B n d X W M χX χW om r₀ s₀ r₁ s₁ hT v w hw hv d' hd' dd hdc θ hθ hvac omd hsp g hg vD hvDSB φ₁ hφ₁ hE0 hA`. Take `⟨μ, hμ⟩` from `vdbl_line F E σ B n d X W M χX χW om r₀ s₀ r₁ s₁ hT v w hw hv d' hd' dd hdc θ hθ hvac φ₁ hφ₁ hE1`. Use `⟨μ, ?_⟩` and prove the remaining obligations.

Rewrite using `[hS, hA RD hRest, hμ]`. Use function extensionality and compare the values at `x`. Simplify using `only [tens, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem vdbl_eigen : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r₀ s₀ r₁ s₁ : ℕ),
    IsPair B M χX χW om r₀ s₀ r₁ s₁ →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → UnrAt χW w →
    ∀ (d' : Darboux (symp (cA σ) (-1 : AE F E) (incM F W.J) (incM F X.J)) (Fin n × Fin d)),
    (∀ x : Matrix (Fin n) (Fin d) (AE F E), d'.e xᵀ = M.co.e x) →
    ∀ (dd : Darboux (symp (cA σ) (-1 : AE F E) (incM F W.J) (dbl (incM F X.J))) ((Fin n × Fin d) ⊕ (Fin n × Fin d)))
      (omd : GlobalTheory.DblVac.UD σ X →* Module.End ℂ (((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) → ℂ)),
    IsDblCoord (cA σ) (-1 : AE F E) (incM F W.J) (incM F X.J) d' dd →
    IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1 : AE F E) (incM F W.J) (dbl (incM F X.J)) dd χW (diagCols (Fin n)) omd →
    ∀ r : (Fin n × Fin d → AF F) → ℂ, Rest (evFin F v) (M.vac v) r →
    ∀ g ∈ GlobalTheory.DblVac.KD σ X v, ∃ μ : ℂ,
      omd g (boxFun (tens (evFin F v) (M.vac v) r) (fun x => star (tens (evFin F v) (M.vac v) r x))) =
        μ • boxFun (tens (evFin F v) (M.vac v) r) (fun x => star (tens (evFin F v) (M.vac v) r x)) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r₀ s₀ r₁ s₁ hT v w hw hv d' hd' dd omd hdc hsp r hr g hg
  obtain ⟨hvSB, -, θ, hθ, hvac⟩ := hT.good.vac v
  set φ := M.vac v with hφ
  set vD := boxFun φ (fun x => star (φ x)) with hvD
  set RD := boxFun r (fun x => star (r x)) with hRD
  have hvDSB : vD ∈ SB _ := boxFun_mem_SB' hvSB (star_mem_SB' hvSB)
  have hS : boxFun (tens (evFin F v) φ r) (fun x => star (tens (evFin F v) φ r x)) = tens (evFin F v) vD RD := by
    funext x
    simp only [tens, boxFun, hvD, hRD, Function.comp_def, star_mul']
    ring
  have hRest : Rest (evFin F v) vD RD := by
    refine ⟨fun x z hz => ?_, ?_⟩
    · have hz1 : At (evFin F v) (z ∘ Sum.inl) := fun u hu => by
        funext i; exact congrFun (hz u hu) (Sum.inl i)
      have hz2 : At (evFin F v) (z ∘ Sum.inr) := fun u hu => by
        funext i; exact congrFun (hz u hu) (Sum.inr i)
      show r ((x + z) ∘ Sum.inl) * star (r ((x + z) ∘ Sum.inr)) = r (x ∘ Sum.inl) * star (r (x ∘ Sum.inr))
      rw [show (x + z) ∘ Sum.inl = x ∘ Sum.inl + z ∘ Sum.inl from rfl,
        show (x + z) ∘ Sum.inr = x ∘ Sum.inr + z ∘ Sum.inr from rfl, hr.1 _ _ hz1, hr.1 _ _ hz2]
    · rw [← hS]
      exact GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ _ hr.2 _ (GlobalTheory.ConjSch.star_mem_schA _ _ hr.2)

  have hU := hsp.2.1
  obtain ⟨φ₁, hφ₁, hA⟩ : ∃ φ₁ ∈ SB _, Acts (evFin F v) (omd g) vD φ₁ := by
    refine GlobalTheory.DblActs.acts_of_comm v B.ψ hT.base.std (omd g) (fun Φ hΦ => hU.pres g Φ hΦ)
      (fun μ hμ Φ hΦ => hU.unit μ hμ g Φ hΦ) ?_ vD hvDSB
    intro u hu x y Φ hΦ
    set z := dd.e.symm (x, y) with hz
    have he : dd.e (u • z) = (u • x, u • y) := by
      rw [LinearEquiv.map_smul, hz, LinearEquiv.apply_symm_apply, Prod.smul_mk]
    have h2 := hg.1 u hu
    have e2 : actB (cA σ) g (u • z) = u • z := by
      simp only [actB]
      set P := GlobalTheory.DblVac.matD g with hP
      set c : AE F E := algebraMap (AF F) (AE F E) u with hc
      have hs1 : u • z = c • z := (algebraMap_smul (AE F E) u z).symm
      have hs2 : u • (P - 1) = c • (P - 1) := (algebraMap_smul (AE F E) u (P - 1)).symm
      have h2' : c • (P - 1) = 0 := hs2 ▸ h2
      have : (c • z) * Pᵀ - c • z = z * (c • (P - 1))ᵀ := by
        rw [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_sub, Matrix.transpose_one,
          Matrix.mul_sub, Matrix.mul_one, smul_sub]
      rw [h2'] at this
      simp only [Matrix.transpose_zero, Matrix.mul_zero, sub_eq_zero] at this
      rw [hs1]
      exact this
    have h3 := hU.impl g (u • z) Φ hΦ
    simp only [Darboux.rho, he, e2] at h3
    exact h3
  have hE0 := vac_eigen F E σ B n d X W M χX χW om r₀ s₀ r₁ s₁ hT v w hw hv d' hd' dd hdc θ hθ hvac
  have hE1 := transport F E σ B n d X W M χX χW om r₀ s₀ r₁ s₁ hT v w hw hv d' hd' dd hdc θ hθ hvac omd hsp g hg vD hvDSB φ₁ hφ₁ hE0 hA
  obtain ⟨μ, hμ⟩ := vdbl_line F E σ B n d X W M χX χW om r₀ s₀ r₁ s₁ hT v w hw hv d' hd' dd hdc θ hθ hvac φ₁ hφ₁ hE1
  refine ⟨μ, ?_⟩
  rw [hS, hA RD hRest, hμ]
  funext x
  simp only [tens, Pi.smul_apply, smul_eq_mul]
  ring

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n d X W M χX χW om r₀ s₀ r₁ s₁ hT v w hw hv d' _ dd omd hdd hW r hr h0 p hp hpd μ hμ`. Take `⟨t, ht₀⟩` from `hpd`. Establish `ht : GlobalTheory.DblVac.matD p * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) = (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * (t : Matrix (Fin n) (Fin n) (AE F E))` using `ht₀`. Establish `hF` using `hT.base.cm.1`. Use `set Ψ := tens (evFin F v) (M.vac v) r with hΨ`.

Establish `hS` using `GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ Ψ hr.2 _ (GlobalTheory.SchAConj.star_mem_schA F _ Ψ hr.2)`. Establish `hl` using `lDiag_box_ne_zero hF hr.2 h0`. Establish `hS0 : (boxFun Ψ fun x => star (Ψ x)) ≠ 0` using `fun h => hl (by rw [h, map_zero])`. Establish `hn` using `norm_eq_one_of_eigen hF hW.2.1.unit hS hS0 hμ`. Establish `hrule` using `hW.2.2 _ DiagForm.lDiag_adm (fun z φ hφ => by`.

Establish `e : z * (diagCols (Fin n) : Matrix _ _ (AE F E))ᵀ = Matrix.fromCols z z`. Rewrite using `[diagCols, Matrix.transpose_fromRows, Matrix.mul_fromCols, Matrix.transpose_one, Matrix.mul_one]`. Rewrite using `[e, Darboux.rho, hdd]`. Conclude with `DiagForm.lDiag_schr B.ψ _ _ hφ) p t ht _ hS`. Establish `hvec : ∀ (g : GlobalTheory.DblVac.UD σ X) (s : Matrix (Fin n) (Fin n) (AE F E)), GlobalTheory.DblVac.matD g * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) = (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * s → ∀ z, (GlobalTheory.DblVac.matD g *ᵥ Sum. …` using `fun g s hs z => by`.

Establish `e : ∀ z : Fin n → AE F E, (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) *ᵥ z = Sum.elim z z` using `fun z => by`. Rewrite using `[diagCols, Matrix.fromRows_mulVec, Matrix.one_mulVec]`. Rewrite using `[← e, Matrix.mulVec_mulVec, hs, ← Matrix.mulVec_mulVec, e]`. Both sides reduce to the same expression. Establish `ht' : GlobalTheory.DblVac.matD p⁻¹ * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) = (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * ((t⁻¹ : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E))`.

Establish `e1 : GlobalTheory.DblVac.matD p⁻¹ * GlobalTheory.DblVac.matD p = 1` using `p.1.inv_mul`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc, t.mul_inv, Matrix.mul_one]`. Use `_ = _ := by rw [← ht, ← Matrix.mul_assoc, e1, Matrix.one_mul]`. Establish `hunr : UnrAt χW w` using `hv`.

Establish `hβ : χW (Matrix.GeneralLinearGroup.det t) = 1`. Use `chr_det_eq_one X hT.herm.lat hw hunr t (fun u hu => ?_) fun z hz => ?_` and prove the remaining obligations. Establish `e1 : (GlobalTheory.DblVac.matD p - 1) * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) = (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * ((t : Matrix (Fin n) (Fin n) (AE F E)) - 1)`. Rewrite using `[Matrix.sub_mul, Matrix.mul_sub, ht, Matrix.one_mul, Matrix.mul_one]`. Establish `e2 : (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * (u • ((t : Matrix (Fin n) (Fin n) (AE F E)) - 1)) = 0`.

Rewrite using `[Matrix.mul_smul, ← e1, ← Matrix.smul_mul, hp.1 u hu, Matrix.zero_mul]`. Rewrite `e2` using `[diagCols, Matrix.fromRows_mul, Matrix.one_mul]`. Use extensionality with `i j`. Conclude with `congrFun (congrFun e2 (Sum.inl i)) j`. Establish `hz'` using `hp.2 (Sum.elim z z) ⟨hz, hz⟩`.

Conclude with `⟨hvec p _ ht z ▸ hz'.1.1, hvec p⁻¹ _ ht' z ▸ hz'.2.1⟩`. Rewrite `hrule` using `[hμ, map_smul, smul_eq_mul, hβ, Circle.coe_one, one_mul]`. Establish `hμ'` using `mul_right_cancel₀ hl hrule`. Rewrite `hn` using `[hμ', Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _)]`. Rewrite using `[hμ', hn, Complex.ofReal_one]`.
-/
theorem eigen_eq_one_of_diag : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r₀ s₀ r₁ s₁ : ℕ),
    IsPair B M χX χW om r₀ s₀ r₁ s₁ →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → UnrAt χW w →
    ∀ (d' : Darboux (symp (cA σ) (-1 : AE F E) (incM F W.J) (incM F X.J)) (Fin n × Fin d)),
    (∀ x : Matrix (Fin n) (Fin d) (AE F E), d'.e xᵀ = M.co.e x) →
    ∀ (dd : Darboux (symp (cA σ) (-1 : AE F E) (incM F W.J) (dbl (incM F X.J))) ((Fin n × Fin d) ⊕ (Fin n × Fin d)))
      (omd : GlobalTheory.DblVac.UD σ X →* Module.End ℂ (((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) → ℂ)),
    IsDblCoord (cA σ) (-1 : AE F E) (incM F W.J) (incM F X.J) d' dd →
    IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1 : AE F E) (incM F W.J) (dbl (incM F X.J)) dd χW (diagCols (Fin n)) omd →
    ∀ r : (Fin n × Fin d → AF F) → ℂ, Rest (evFin F v) (M.vac v) r → tens (evFin F v) (M.vac v) r ≠ 0 →
    ∀ p ∈ GlobalTheory.DblVac.KD σ X v, p ∈ GlobalTheory.DblVac.PDiag σ X → ∀ μ : ℂ,
      omd p (boxFun (tens (evFin F v) (M.vac v) r) (fun x => star (tens (evFin F v) (M.vac v) r x))) =
        μ • boxFun (tens (evFin F v) (M.vac v) r) (fun x => star (tens (evFin F v) (M.vac v) r x)) → μ = 1 := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r₀ s₀ r₁ s₁ hT v w hw hv d' _ dd omd hdd hW r hr h0 p hp hpd μ hμ
  obtain ⟨t, ht₀⟩ := hpd
  have ht : GlobalTheory.DblVac.matD p * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) =
      (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * (t : Matrix (Fin n) (Fin n) (AE F E)) := ht₀
  have hF := hT.base.cm.1
  set Ψ := tens (evFin F v) (M.vac v) r with hΨ
  have hS := GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ Ψ hr.2 _ (GlobalTheory.SchAConj.star_mem_schA F _ Ψ hr.2)
  have hl := lDiag_box_ne_zero hF hr.2 h0
  have hS0 : (boxFun Ψ fun x => star (Ψ x)) ≠ 0 := fun h => hl (by rw [h, map_zero])
  have hn := norm_eq_one_of_eigen hF hW.2.1.unit hS hS0 hμ
  have hrule := hW.2.2 _ DiagForm.lDiag_adm (fun z φ hφ => by
    have e : z * (diagCols (Fin n) : Matrix _ _ (AE F E))ᵀ = Matrix.fromCols z z := by
      rw [diagCols, Matrix.transpose_fromRows, Matrix.mul_fromCols, Matrix.transpose_one, Matrix.mul_one]
    rw [e, Darboux.rho, hdd]
    exact DiagForm.lDiag_schr B.ψ _ _ hφ) p t ht _ hS
  have hvec : ∀ (g : GlobalTheory.DblVac.UD σ X) (s : Matrix (Fin n) (Fin n) (AE F E)),
      GlobalTheory.DblVac.matD g * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) = (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * s → ∀ z,
      (GlobalTheory.DblVac.matD g *ᵥ Sum.elim z z) ∘ Sum.inl = s *ᵥ z := fun g s hs z => by
    have e : ∀ z : Fin n → AE F E, (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) *ᵥ z = Sum.elim z z := fun z => by
      rw [diagCols, Matrix.fromRows_mulVec, Matrix.one_mulVec]
    rw [← e, Matrix.mulVec_mulVec, hs, ← Matrix.mulVec_mulVec, e]
    rfl
  have ht' : GlobalTheory.DblVac.matD p⁻¹ * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) =
      (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * ((t⁻¹ : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) := by
    have e1 : GlobalTheory.DblVac.matD p⁻¹ * GlobalTheory.DblVac.matD p = 1 := p.1.inv_mul
    calc _ = GlobalTheory.DblVac.matD p⁻¹ * ((diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * (t : Matrix (Fin n) (Fin n) (AE F E))) *
          ((t⁻¹ : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, t.mul_inv, Matrix.mul_one]
      _ = _ := by rw [← ht, ← Matrix.mul_assoc, e1, Matrix.one_mul]
  have hunr : UnrAt χW w := hv
  have hβ : χW (Matrix.GeneralLinearGroup.det t) = 1 := by
    refine chr_det_eq_one X hT.herm.lat hw hunr t (fun u hu => ?_) fun z hz => ?_
    · have e1 : (GlobalTheory.DblVac.matD p - 1) * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) =
          (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * ((t : Matrix (Fin n) (Fin n) (AE F E)) - 1) := by
        rw [Matrix.sub_mul, Matrix.mul_sub, ht, Matrix.one_mul, Matrix.mul_one]
      have e2 : (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * (u • ((t : Matrix (Fin n) (Fin n) (AE F E)) - 1)) = 0 := by
        rw [Matrix.mul_smul, ← e1, ← Matrix.smul_mul, hp.1 u hu, Matrix.zero_mul]
      rw [diagCols, Matrix.fromRows_mul, Matrix.one_mul] at e2
      ext i j
      exact congrFun (congrFun e2 (Sum.inl i)) j
    · have hz' := hp.2 (Sum.elim z z) ⟨hz, hz⟩
      exact ⟨hvec p _ ht z ▸ hz'.1.1, hvec p⁻¹ _ ht' z ▸ hz'.2.1⟩
  rw [hμ, map_smul, smul_eq_mul, hβ, Circle.coe_one, one_mul] at hrule
  have hμ' := mul_right_cancel₀ hl hrule
  rw [hμ', Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _)] at hn
  rw [hμ', hn, Complex.ofReal_one]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n d X W M χX χW om r₀ s₀ r₁ s₁ hT v w hin _ H hD hA g hg`. Establish `h2 : (2 : 𝓞 F) ∉ v.asIdeal` using `(hT.base.inert v w hin).1`. Take `⟨u, hu, huP, hdet, hlat⟩` from `GlobalTheory.T.exists_unipotent_corner_isUnit_inertPlace F E σ B n r₀ s₀ X hT.base hT.herm v w hin g hg`. Take `⟨p, q, hp, hpP, hq, hqA, hpq⟩` from `GlobalTheory.T.doubledVacuumLatticeStabilizer_bigCell_factorization F E σ n X v h2 (g * u) (KD_mul hg hu) hdet hlat`. Establish `e : g = p * q * u⁻¹` using `by rw [← hpq]; group`.

Rewrite using `[e]`. Conclude with `H.mul_mem (H.mul_mem (hD p hp hpP) (hA q hq hqA)) (hD _ (KD_inv hu) (PDiag_inv huP))`.
-/
theorem mem_of_KD_diag_anti : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r₀ s₀ r₁ s₁ : ℕ),
    IsPair B M χX χW om r₀ s₀ r₁ s₁ →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → UnrAt χW w → ∀ H : Subgroup (GlobalTheory.DblVac.UD σ X),
      (∀ p ∈ GlobalTheory.DblVac.KD σ X v, p ∈ GlobalTheory.DblVac.PDiag σ X → p ∈ H) →
      (∀ p ∈ GlobalTheory.DblVac.KD σ X v, p ∈ GlobalTheory.DblVac.PAnti σ X → p ∈ H) → ∀ g ∈ GlobalTheory.DblVac.KD σ X v, g ∈ H := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r₀ s₀ r₁ s₁ hT v w hin _ H hD hA g hg
  have h2 : (2 : 𝓞 F) ∉ v.asIdeal := (hT.base.inert v w hin).1
  obtain ⟨u, hu, huP, hdet, hlat⟩ := GlobalTheory.T.exists_unipotent_corner_isUnit_inertPlace F E σ B n r₀ s₀ X hT.base hT.herm v w hin g hg
  obtain ⟨p, q, hp, hpP, hq, hqA, hpq⟩ := GlobalTheory.T.doubledVacuumLatticeStabilizer_bigCell_factorization F E σ n X v h2 (g * u) (KD_mul hg hu) hdet hlat
  have e : g = p * q * u⁻¹ := by rw [← hpq]; group
  rw [e]
  exact H.mul_mem (H.mul_mem (hD p hp hpP) (hA q hq hqA)) (hD _ (KD_inv hu) (PDiag_inv huP))

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n d X W M χX χW om r₀ s₀ r₁ s₁ hT v w hw hv d' hd' dd omd hdc hsp r hr hr0 g hg`. Use `set V₀ := tens (evFin F v) (M.vac v) r with hV₀`. Use `set S := boxFun V₀ (fun x => star (V₀ x)) with hS`. Set `H : Subgroup (GlobalTheory.DblVac.UD σ X)` to `{ carrier := {g | omd g S = S} one_mem' := by simp mul_mem' := fun {x y} hx hy => by`. Simplify using `only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *`.

Rewrite using `[hy, hx]`. Use the proof step `inv_mem' := fun {x} hx => by`. Simplify using `only [Set.mem_setOf_eq] at *`. Use `conv_lhs => rw [← hx]`. Rewrite using `[← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }`.

Establish `hD : ∀ p ∈ GlobalTheory.DblVac.KD σ X v, p ∈ GlobalTheory.DblVac.PDiag σ X → p ∈ H` using `fun p hp hpd => by`. Take `⟨μ, hμ⟩` from `vdbl_eigen F E σ B n d X W M χX χW om r₀ s₀ r₁ s₁ hT v w hw hv d' hd' dd omd hdc hsp r hr p hp`. Establish `h1` using `eigen_eq_one_of_diag F E σ B n d X W M χX χW om r₀ s₀ r₁ s₁ hT v w hw hv d' hd' dd omd hdc hsp r hr hr0 p hp hpd μ hμ`. Use `show omd p S = S`. Rewrite using `[hμ, h1, one_smul]`.

Establish `hA : ∀ q ∈ GlobalTheory.DblVac.KD σ X v, q ∈ GlobalTheory.DblVac.PAnti σ X → q ∈ H` using `fun q hq hqa => by`. Take `⟨w₀, hw₀, hW⟩` from `GlobalTheory.T.exists_diagOneNegOne_conj_antidiagonalStabilizer_mem σ X v`. Take `⟨h1, h2⟩` from `hW q hq hqa`. Establish `hq' : omd (w₀ * q * w₀⁻¹) S = S` using `hD _ h1 h2`. Take `⟨μ, hμ⟩` from `vdbl_eigen F E σ B n d X W M χX χW om r₀ s₀ r₁ s₁ hT v w hw hv d' hd' dd omd hdc hsp r hr w₀ hw₀`.

Establish `hinv : μ • omd w₀⁻¹ S = S`. Rewrite using `[← LinearMap.map_smul, ← hμ, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]`. Establish `e : q = w₀⁻¹ * (w₀ * q * w₀⁻¹) * w₀` using `by group`. Use `show omd q S = S`. Rewrite using `[e, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hμ, LinearMap.map_smul, hq', LinearMap.map_smul, hinv]`.

Conclude with `mem_of_KD_diag_anti F E σ B n d X W M χX χW om r₀ s₀ r₁ s₁ hT v w hw hv H hD hA g hg`.
-/
theorem dbl_vac_fixed : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r₀ s₀ r₁ s₁ : ℕ),
    IsPair B M χX χW om r₀ s₀ r₁ s₁ →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → UnrAt χW w →
    ∀ (d' : Darboux (symp (cA σ) (-1 : AE F E) (incM F W.J) (incM F X.J)) (Fin n × Fin d)),
    (∀ x : Matrix (Fin n) (Fin d) (AE F E), d'.e xᵀ = M.co.e x) →
    ∀ (dd : Darboux (symp (cA σ) (-1 : AE F E) (incM F W.J) (dbl (incM F X.J))) ((Fin n × Fin d) ⊕ (Fin n × Fin d)))
      (omd : GlobalTheory.DblVac.UD σ X →* Module.End ℂ (((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) → ℂ)),
    IsDblCoord (cA σ) (-1 : AE F E) (incM F W.J) (incM F X.J) d' dd →
    IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1 : AE F E) (incM F W.J) (dbl (incM F X.J)) dd χW (diagCols (Fin n)) omd →
    ∀ r : (Fin n × Fin d → AF F) → ℂ, Rest (evFin F v) (M.vac v) r → tens (evFin F v) (M.vac v) r ≠ 0 →
    ∀ g ∈ GlobalTheory.DblVac.KD σ X v,
      omd g (boxFun (tens (evFin F v) (M.vac v) r) (fun x => star (tens (evFin F v) (M.vac v) r x))) =
        boxFun (tens (evFin F v) (M.vac v) r) (fun x => star (tens (evFin F v) (M.vac v) r x)) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r₀ s₀ r₁ s₁ hT v w hw hv d' hd' dd omd hdc hsp r hr hr0 g hg
  set V₀ := tens (evFin F v) (M.vac v) r with hV₀
  set S := boxFun V₀ (fun x => star (V₀ x)) with hS
  let H : Subgroup (GlobalTheory.DblVac.UD σ X) :=
    { carrier := {g | omd g S = S}
      one_mem' := by simp
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
        rw [hy, hx]
      inv_mem' := fun {x} hx => by
        simp only [Set.mem_setOf_eq] at *
        conv_lhs => rw [← hx]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hD : ∀ p ∈ GlobalTheory.DblVac.KD σ X v, p ∈ GlobalTheory.DblVac.PDiag σ X → p ∈ H := fun p hp hpd => by
    obtain ⟨μ, hμ⟩ := vdbl_eigen F E σ B n d X W M χX χW om r₀ s₀ r₁ s₁ hT v w hw hv d' hd' dd omd hdc hsp r hr p hp
    have h1 := eigen_eq_one_of_diag F E σ B n d X W M χX χW om r₀ s₀ r₁ s₁ hT v w hw hv d' hd' dd omd hdc hsp r hr hr0 p hp hpd μ hμ
    show omd p S = S
    rw [hμ, h1, one_smul]
  have hA : ∀ q ∈ GlobalTheory.DblVac.KD σ X v, q ∈ GlobalTheory.DblVac.PAnti σ X → q ∈ H := fun q hq hqa => by
    obtain ⟨w₀, hw₀, hW⟩ := GlobalTheory.T.exists_diagOneNegOne_conj_antidiagonalStabilizer_mem σ X v
    obtain ⟨h1, h2⟩ := hW q hq hqa
    have hq' : omd (w₀ * q * w₀⁻¹) S = S := hD _ h1 h2
    obtain ⟨μ, hμ⟩ := vdbl_eigen F E σ B n d X W M χX χW om r₀ s₀ r₁ s₁ hT v w hw hv d' hd' dd omd hdc hsp r hr w₀ hw₀
    have hinv : μ • omd w₀⁻¹ S = S := by
      rw [← LinearMap.map_smul, ← hμ, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply]
    have e : q = w₀⁻¹ * (w₀ * q * w₀⁻¹) * w₀ := by group
    show omd q S = S
    rw [e, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hμ, LinearMap.map_smul, hq',
      LinearMap.map_smul, hinv]
  exact mem_of_KD_diag_anti F E σ B n d X W M χX χW om r₀ s₀ r₁ s₁ hT v w hw hv H hD hA g hg

end GlobalTheory.PairDblVac

end
