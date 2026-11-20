import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNonarchimedeanW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullFrameRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FnEquivApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColMinorEqSupMinors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinorsTriangularChangeInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeftInverseRegularOfRegularStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CramerTriBlockTriangular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularMatricesValueMultiplicative
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionEquivRegularUnitValue
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodReductionExtendsRegular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgebraicPointSpecializing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitAtPointsOverPrimeBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReductionRegularFunctionsGoodPrimesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnMinorNormInequalityStatement
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.WholeFlag GlobalTheory.ConstLat GlobalTheory.WholeFlag.Glue GlobalTheory.ConstLat.CramerFrame
open scoped Classical
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ConstLat.CramerFrame

/- English proof (translation)
Take `⟨A, rfl⟩` from `GlobalTheory.ConstLat.CramerValues.exists_germ_matrix M hM`. Conclude with `⟨A.det, by rw [RingHom.map_det]; rfl⟩`.
-/
theorem regAt_det_of_regAt {Z : Scheme.{0}} [IsIntegral Z] {x : Z} {n : ℕ} (M : Matrix (Fin n) (Fin n) Z.functionField)
    (hM : ∀ a b, RegAt x (M a b)) : RegAt x M.det := by
  obtain ⟨A, rfl⟩ := GlobalTheory.ConstLat.CramerValues.exists_germ_matrix M hM
  exact ⟨A.det, by rw [RingHom.map_det]; rfl⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨(-1) ^ n, by simp⟩`.
-/
theorem regAt_neg_one_pow {Z : Scheme.{0}} [IsIntegral Z] (x : Z) (n : ℕ) : RegAt x ((-1 : Z.functionField) ^ n) :=
  ⟨(-1) ^ n, by simp⟩

/- English proof (translation)
Introduce `F _ _ Y V W p _ _ g U' H d T σ hT hReg _ hU _ v _ e y _ z yt hz hyt hU'`. Establish `hmem : V.j (below z) ∈ U'`. Establish `h1 : V.j (below z) = yt (spMap e.O.subtype (IsLocalRing.closedPoint _))` using `by show below (z ≫ V.j) = _`. Rewrite using `[← hyt]`. Both sides reduce to the same expression.

Rewrite using `[h1]`. Conclude with `hU' (show _ ∈ (⊤ : (Sp e.O).Opens) from trivial)`. Establish `hy : below y.1 = V.π (below z)` using `by rw [← hz]; rfl`. Rewrite using `[hy]`. Establish `hdiag : ∀ k, ((T (V.π (below z))).map V.φ) k k = V.φ (d (V.π (below z)) k : Y.Fn)` using `fun k => by`.

Rewrite using `[Matrix.map_apply, (hT _).2 k]`. Establish `htri : ((T (V.π (below z))).map V.φ).BlockTriangular id` using `fun a b hab => by`. Rewrite using `[Matrix.map_apply, (hT _).1 hab, map_zero]`. Establish `hne : ∀ k, ((T (V.π (below z))).map V.φ) k k ≠ 0` using `fun k => by`. Rewrite using `[hdiag k]`.

Conclude with `(map_ne_zero V.φ).2 (d (V.π (below z)) k).ne_zero`. Establish `hI` using `GlobalTheory.T.minors_triangular_change_invariant H _ htri hne σ`. Establish `hUz` using `hU (below z) hmem`. Establish `hR` using `hReg (below z) hmem`. Establish `hval` using `GlobalTheory.ConstLat.CramerValues.values_regular z`.

Establish `hCR : ∀ a b, RegAt (below z) (cramerTri (H * ((T (V.π (below z))).map V.φ)⁻¹) σ a b)`. Introduce `a b`. Simplify using `only [cramerTri, Matrix.of_apply]`. Use `Finset.sum_induction _ (RegAt (below z)) (fun _ _ => RegAt.add) (regAt_zero _) fun j _ => ?_` and prove the remaining obligations. Use `split_ifs`.

Unfold `cramerCoef`. Conclude with `(hval.2.2 _ _ ((regAt_neg_one_pow _ _).mul (regAt_det_of_regAt _ fun a b => hR _ _)) (hUz _ _)).1`. Conclude with `regAt_zero _`. Establish `hcc : cramerCol H σ = (H * ((T (V.π (below z))).map V.φ)⁻¹) * cramerTri (H * ((T (V.π (below z))).map V.φ)⁻¹) σ` using `hI.2.1.trans (cramerCol_eq_mul _ σ)`. Establish `hP` using `hval.1 _ _ hR hCR`.

Use `⟨(cramerTri (H * ((T (V.π (below z))).map V.φ)⁻¹) σ).map (valAt z), ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `a b hab`. Rewrite using `[Matrix.map_apply, cramerTri_blockTriangular _ σ hab]`. Simplify using `using Base.valAt_stalk z (0 : (V.G).presheaf.stalk (below z))`. Introduce `i`.

Rewrite using `[Matrix.map_apply, cramerTri_diag]`. Use `congr 1`. Rewrite using `[hI.2.2 (fun k hk => (hUz k hk).ne_zero) i, hdiag i]`. Establish `h1` using `(hUz i i.2.le).ne_zero`. Establish `h2` using `(hUz ((i : ℕ) + 1) i.2).ne_zero`.

Establish `h3 : V.φ (d (V.π (below z)) i : Y.Fn) ≠ 0` using `(map_ne_zero V.φ).2 (d (V.π (below z)) i).ne_zero`. Clear the denominators using the available nonvanishing facts. Use extensionality with `r k`. Establish `hrk : RegAt (below z) (cramerCol H σ r k)` using `by rw [hcc]; exact hP.1 r k`. Establish `hreg : RegAt (V.j (below z)) ((fnEquiv V).symm (cramerCol H σ r k))` using `((fnEquiv_transport V).1 (below z) _).1.mp (by rw [RingEquiv.apply_symm_apply]; exact hrk)`.

Simplify using `only [frameUm, Matrix.map_apply]`. Rewrite using `[← (fnEquiv_transport V).2 z _ hreg, RingEquiv.apply_symm_apply, hcc]`. Conclude with `congrFun (congrFun hP.2 r) k`.
-/
theorem frameUm_values_at_test : ∀ {F : Type} [Field F] [NumberField F] {Y : Var F} (V : Cover Y) (W : Y.X.Opens) (p : ℕ), p.Prime → genericPoint Y.X ∈ W → ∀ {g : ℕ} (U' : V.X.Opens) (H : Matrix (Fin (g + g)) (Fin g) V.G.functionField) (d : Y.X → Fin g → Y.Fnˣ) (T : Y.X → Matrix (Fin g) (Fin g) Y.Fn) (σ : ∀ k : ℕ, Fin k → Fin (g + g)), (∀ y, (T y).BlockTriangular id ∧ ∀ i, T y i i = (d y i : Y.Fn)) → ChartReg V U' H T → (∀ (k : ℕ) (hk : k ≤ g), minorAt H k hk (σ k) ≠ 0) → (∀ z : V.G, V.j z ∈ U' → ∀ (k : ℕ) (hk : k ≤ g), UnitAt z (minorAt (H * ((T (V.π z)).map V.φ)⁻¹) k hk (σ k))) → (AtTest V W p fun _ e y z yt => ⊤ ≤ yt ⁻¹ᵁ U' → ∀ (k : ℕ) (hk : k ≤ g) (τ : Fin k → Fin (g + g)), e.w (minorAt (valMat V H (T (below y.1)) z) k hk τ) ≤ e.w (minorAt (valMat V H (T (below y.1)) z) k hk (σ k))) → AtTest V W p fun _ e y z yt => ⊤ ≤ yt ⁻¹ᵁ U' → ∃ B : Matrix (Fin g) (Fin g) (AlgebraicClosure F), B.BlockTriangular id ∧ (∀ i, B i i = valAt z (V.φ (d (below y.1) i : Y.Fn) / (frameC H σ i : V.G.functionField))) ∧ (frameUm V H σ).map (valAt (z ≫ V.j)) = valMat V H (T (below y.1)) z * B := by
  intro F _ _ Y V W p _ _ g U' H d T σ hT hReg _ hU _ v _ e y _ z yt hz hyt hU'
  have hmem : V.j (below z) ∈ U' := by
    have h1 : V.j (below z) = yt (spMap e.O.subtype (IsLocalRing.closedPoint _)) := by
      show below (z ≫ V.j) = _
      rw [← hyt]
      rfl
    rw [h1]
    exact hU' (show _ ∈ (⊤ : (Sp e.O).Opens) from trivial)
  have hy : below y.1 = V.π (below z) := by rw [← hz]; rfl
  rw [hy]
  have hdiag : ∀ k, ((T (V.π (below z))).map V.φ) k k = V.φ (d (V.π (below z)) k : Y.Fn) := fun k => by
    rw [Matrix.map_apply, (hT _).2 k]
  have htri : ((T (V.π (below z))).map V.φ).BlockTriangular id := fun a b hab => by
    rw [Matrix.map_apply, (hT _).1 hab, map_zero]
  have hne : ∀ k, ((T (V.π (below z))).map V.φ) k k ≠ 0 := fun k => by
    rw [hdiag k]
    exact (map_ne_zero V.φ).2 (d (V.π (below z)) k).ne_zero
  have hI := GlobalTheory.T.minors_triangular_change_invariant H _ htri hne σ
  have hUz := hU (below z) hmem
  have hR := hReg (below z) hmem
  have hval := GlobalTheory.ConstLat.CramerValues.values_regular z
  have hCR : ∀ a b, RegAt (below z) (cramerTri (H * ((T (V.π (below z))).map V.φ)⁻¹) σ a b) := by
    intro a b
    simp only [cramerTri, Matrix.of_apply]
    refine Finset.sum_induction _ (RegAt (below z)) (fun _ _ => RegAt.add) (regAt_zero _) fun j _ => ?_
    split_ifs
    · unfold cramerCoef
      exact (hval.2.2 _ _ ((regAt_neg_one_pow _ _).mul (regAt_det_of_regAt _ fun a b => hR _ _)) (hUz _ _)).1
    · exact regAt_zero _
  have hcc : cramerCol H σ = (H * ((T (V.π (below z))).map V.φ)⁻¹) * cramerTri (H * ((T (V.π (below z))).map V.φ)⁻¹) σ :=
    hI.2.1.trans (cramerCol_eq_mul _ σ)
  have hP := hval.1 _ _ hR hCR
  refine ⟨(cramerTri (H * ((T (V.π (below z))).map V.φ)⁻¹) σ).map (valAt z), ?_, ?_, ?_⟩
  · intro a b hab
    rw [Matrix.map_apply, cramerTri_blockTriangular _ σ hab]
    simpa using Base.valAt_stalk z (0 : (V.G).presheaf.stalk (below z))
  · intro i
    rw [Matrix.map_apply, cramerTri_diag]
    congr 1
    rw [hI.2.2 (fun k hk => (hUz k hk).ne_zero) i, hdiag i]
    have h1 := (hUz i i.2.le).ne_zero
    have h2 := (hUz ((i : ℕ) + 1) i.2).ne_zero
    have h3 : V.φ (d (V.π (below z)) i : Y.Fn) ≠ 0 := (map_ne_zero V.φ).2 (d (V.π (below z)) i).ne_zero
    field_simp
  · ext r k
    have hrk : RegAt (below z) (cramerCol H σ r k) := by rw [hcc]; exact hP.1 r k
    have hreg : RegAt (V.j (below z)) ((fnEquiv V).symm (cramerCol H σ r k)) :=
      ((fnEquiv_transport V).1 (below z) _).1.mp (by rw [RingEquiv.apply_symm_apply]; exact hrk)
    simp only [frameUm, Matrix.map_apply]
    rw [← (fnEquiv_transport V).2 z _ hreg, RingEquiv.apply_symm_apply, hcc]
    exact congrFun (congrFun hP.2 r) k

end GlobalTheory.ConstLat.CramerFrame
