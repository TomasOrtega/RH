import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.EllipticityFromProductFormula
import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Action
import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Places
import Development.AutomorphicArithmetic.AdelicQuotients.NormGaloisSmulAdeleComponentAtSmulPlace
open NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped NumberField.AdeleRing

/- English proof (translation)
The claim follows from `le_antisymm (AutomorphicForm.locHeight_le (AutomorphicForm.one_le_locHeight h) (fun i j => (h₁ i j).le.trans (AutomorphicForm.norm_apply_le_locHeight h i j)) (fun i j => (h₂ i j).le.trans (AutomorphicForm.norm_inv_apply_le_locHeight h i j))) (AutomorphicForm.locHeight_le (Automor …`.
-/
private theorem locHeight_congr {A B : Type*} [NormedField A] [NormedField B] {n : ℕ}
    (g : GL (Fin n) A) (h : GL (Fin n) B)
    (h₁ : ∀ i j, ‖(g : Matrix (Fin n) (Fin n) A) i j‖ = ‖(h : Matrix (Fin n) (Fin n) B) i j‖)
    (h₂ : ∀ i j, ‖((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) i j‖ =
      ‖((h⁻¹ : GL (Fin n) B) : Matrix (Fin n) (Fin n) B) i j‖) :
    AutomorphicForm.locHeight g = AutomorphicForm.locHeight h :=
  le_antisymm
    (AutomorphicForm.locHeight_le (AutomorphicForm.one_le_locHeight h)
      (fun i j => (h₁ i j).le.trans (AutomorphicForm.norm_apply_le_locHeight h i j))
      (fun i j => (h₂ i j).le.trans (AutomorphicForm.norm_inv_apply_le_locHeight h i j)))
    (AutomorphicForm.locHeight_le (AutomorphicForm.one_le_locHeight g)
      (fun i j => (h₁ i j).ge.trans (AutomorphicForm.norm_apply_le_locHeight g i j))
      (fun i j => (h₂ i j).ge.trans (AutomorphicForm.norm_inv_apply_le_locHeight g i j)))

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
The claim follows from `(UpperTheory.norm_galois_smul_adele_component_at_smul_place F E σ ((g : Matrix (Fin n) (Fin n) 𝔸[E]) i j)).1 w`.
-/
private theorem fin_norm (σ : E ≃ₐ[F] E) {n : ℕ} (w : HeightOneSpectrum (𝓞 E))
    (g : AdelicGLn.AdelicGL E n) (i j : Fin n) :
    ‖(finAt (σ • w) (mapGL n (galAd σ) g)).val i j‖ = ‖(finAt w g).val i j‖ :=
  (UpperTheory.norm_galois_smul_adele_component_at_smul_place F E σ ((g : Matrix (Fin n) (Fin n) 𝔸[E]) i j)).1 w

/- English proof (translation)
The claim follows from `(UpperTheory.norm_galois_smul_adele_component_at_smul_place F E σ ((g : Matrix (Fin n) (Fin n) 𝔸[E]) i j)).2 w`.
-/
private theorem inf_norm (σ : E ≃ₐ[F] E) {n : ℕ} (w : InfinitePlace E)
    (g : AdelicGLn.AdelicGL E n) (i j : Fin n) :
    ‖(infAt (σ • w) (mapGL n (galAd σ) g)).val i j‖ = ‖(infAt w g).val i j‖ :=
  (UpperTheory.norm_galois_smul_adele_component_at_smul_place F E σ ((g : Matrix (Fin n) (Fin n) 𝔸[E]) i j)).2 w

/- English proof (translation)
Use `locHeight_congr _ _ (fin_norm σ w g) fun i j => ?_` and prove the remaining obligations. Rewrite using `[← finAt_inv, ← finAt_inv, ← map_inv]`. Conclude with `fin_norm σ w g⁻¹ i j`.
-/
private theorem locHeight_fin (σ : E ≃ₐ[F] E) {n : ℕ} (w : HeightOneSpectrum (𝓞 E))
    (g : AdelicGLn.AdelicGL E n) :
    AutomorphicForm.locHeight (finAt (σ • w) (mapGL n (galAd σ) g)) =
      AutomorphicForm.locHeight (finAt w g) := by
  refine locHeight_congr _ _ (fin_norm σ w g) fun i j => ?_
  rw [← finAt_inv, ← finAt_inv, ← map_inv]
  exact fin_norm σ w g⁻¹ i j

/- English proof (translation)
Use `locHeight_congr _ _ (inf_norm σ w g) fun i j => ?_` and prove the remaining obligations. Rewrite using `[← infAt_inv, ← infAt_inv, ← map_inv]`. Conclude with `inf_norm σ w g⁻¹ i j`.
-/
private theorem locHeight_inf (σ : E ≃ₐ[F] E) {n : ℕ} (w : InfinitePlace E)
    (g : AdelicGLn.AdelicGL E n) :
    AutomorphicForm.locHeight (infAt (σ • w) (mapGL n (galAd σ) g)) =
      AutomorphicForm.locHeight (infAt w g) := by
  refine locHeight_congr _ _ (inf_norm σ w g) fun i j => ?_
  rw [← infAt_inv, ← infAt_inv, ← map_inv]
  exact inf_norm σ w g⁻¹ i j

/- English proof (translation)
Establish `h : (σ • w).IsReal ↔ w.IsReal` using `InfinitePlace.isReal_smul_iff`. Unfold `InfinitePlace.mult`. Distinguish the cases in `hw : w.IsReal`. Rewrite using `[if_pos (h.2 hw), if_pos hw]`. Rewrite using `[if_neg (fun h' => hw (h.1 h')), if_neg hw]`.
-/
private theorem mult_smul (σ : E ≃ₐ[F] E) (w : InfinitePlace E) : (σ • w).mult = w.mult := by
  have h : (σ • w).IsReal ↔ w.IsReal := InfinitePlace.isReal_smul_iff
  unfold InfinitePlace.mult
  by_cases hw : w.IsReal
  · rw [if_pos (h.2 hw), if_pos hw]
  · rw [if_neg (fun h' => hw (h.1 h')), if_neg hw]

/- English proof (translation)
Use `(Equiv.prod_comp (MulAction.toPerm σ) (fun w : InfinitePlace E => AutomorphicForm.locHeight (infAt w (mapGL n (galAd σ) g)) ^ w.mult)).symm.trans (Finset.prod_congr rfl fun w _ => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `AutomorphicForm.locHeight (infAt (σ • w) (mapGL n (galAd σ) g)) ^ (σ • w).mult = _`. Rewrite using `[locHeight_inf, mult_smul]`.
-/
private theorem inf_prod (σ : E ≃ₐ[F] E) {n : ℕ} (g : AdelicGLn.AdelicGL E n) :
    (∏ w : InfinitePlace E, AutomorphicForm.locHeight (infAt w (mapGL n (galAd σ) g)) ^ w.mult) =
      ∏ w : InfinitePlace E, AutomorphicForm.locHeight (infAt w g) ^ w.mult := by
  refine (Equiv.prod_comp (MulAction.toPerm σ) (fun w : InfinitePlace E =>
    AutomorphicForm.locHeight (infAt w (mapGL n (galAd σ) g)) ^ w.mult)).symm.trans
    (Finset.prod_congr rfl fun w _ => ?_)
  change AutomorphicForm.locHeight (infAt (σ • w) (mapGL n (galAd σ) g)) ^ (σ • w).mult = _
  rw [locHeight_inf, mult_smul]

/- English proof (translation)
Use `(finprod_comp_equiv (MulAction.toPerm σ : Equiv.Perm (HeightOneSpectrum (𝓞 E))) (f := fun w : HeightOneSpectrum (𝓞 E) => ∏ᶠ (_ : below F w ≠ q), AutomorphicForm.locHeight (finAt w (mapGL n (galAd σ) g)))).symm.trans (finprod_congr fun w => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(∏ᶠ (_ : below F (σ • w) ≠ q), AutomorphicForm.locHeight (finAt (σ • w) (mapGL n (galAd σ) g))) = _`. Establish `hb : below F (σ • w) = below F w` using `HeightOneSpectrum.ext (Ideal.under_smul (𝓞 F) w.asIdeal σ)`. Rewrite using `[locHeight_fin, hb]`.
-/
private theorem fin_prod (σ : E ≃ₐ[F] E) {n : ℕ} (q : HeightOneSpectrum (𝓞 F))
    (g : AdelicGLn.AdelicGL E n) :
    (∏ᶠ (w : HeightOneSpectrum (𝓞 E)) (_ : below F w ≠ q),
      AutomorphicForm.locHeight (finAt w (mapGL n (galAd σ) g))) =
      ∏ᶠ (w : HeightOneSpectrum (𝓞 E)) (_ : below F w ≠ q),
        AutomorphicForm.locHeight (finAt w g) := by
  refine (finprod_comp_equiv (MulAction.toPerm σ : Equiv.Perm (HeightOneSpectrum (𝓞 E)))
    (f := fun w : HeightOneSpectrum (𝓞 E) => ∏ᶠ (_ : below F w ≠ q),
      AutomorphicForm.locHeight (finAt w (mapGL n (galAd σ) g)))).symm.trans
    (finprod_congr fun w => ?_)
  change (∏ᶠ (_ : below F (σ • w) ≠ q),
    AutomorphicForm.locHeight (finAt (σ • w) (mapGL n (galAd σ) g))) = _
  have hb : below F (σ • w) = below F w :=
    HeightOneSpectrum.ext (Ideal.under_smul (𝓞 F) w.asIdeal σ)
  rw [locHeight_fin, hb]

end

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n q g`. Unfold `heightOff`. Rewrite using `[inf_prod, fin_prod]`.
-/
theorem UpperTheory.heightOff_mapGL_galAd :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E ≃ₐ[F] E) (n : ℕ) (q : HeightOneSpectrum (𝓞 F)) (g : AdelicGLn.AdelicGL E n),
        heightOff q (mapGL n (galAd σ) g : AdelicGLn.AdelicGL E n) = heightOff q g := by
  intro F E _ _ _ _ _ σ n q g
  unfold heightOff
  rw [inf_prod, fin_prod]
