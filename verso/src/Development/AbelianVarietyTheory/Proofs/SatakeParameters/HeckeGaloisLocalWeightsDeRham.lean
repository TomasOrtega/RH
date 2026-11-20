import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsobaricDiscreteSelfDualStrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsEmbeddingPadicAlgClPlaceStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteExtAbsIrrSubStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsConjDoubleBlockOfIsoSubspacesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.AbsIrrConstituents

/- English proof (translation)
Use extensionality with `x i j`. Both sides reduce to the same expression.
-/
theorem mapRep_comp {Γ A B C : Type} [Group Γ] [CommRing A] [CommRing B] [CommRing C] {a : ℕ}
    (f : A →+* B) (g : B →+* C) (ρ : Γ →* GL (Fin a) A) :
    mapRep (g.comp f) ρ = mapRep g (mapRep f ρ) := by
  ext x i j
  rfl

/- English proof (translation)
Establish `h1` using `D.naut.locAut_hodgeTateWeightsLevelZero_def i τ`. Rewrite `h1` using `[D.nbc.embAV_inf i P]`. Establish `h2` using `(D.nbc.infW_alg _ (D.nbc.wtAU _ (D.nbc.embAV i P)) ((D.naut.iotaQC i).toRingHom.comp τ)).1`. Establish `h3` using `h2.map (f := fun z : ℂ => -z + ((D.R.nV : ℂ) - 1) / 2) (fun a b hab => by simpa using hab)`. Rewrite `h3` using `[← h1]`.

Conclude with `h3.of_map _`.
-/
theorem fixedJumps_nodup (D : D7) (i : D.nd.Loc) (P : D.naut.AV i) (τ : D.host.E →+* Qbar (D.nd.l i)) :
    (D.naut.locAutHodgeTateWeightsLevelZero i τ).Nodup := by
  have h1 := D.naut.locAut_hodgeTateWeightsLevelZero_def i τ
  rw [D.nbc.embAV_inf i P] at h1
  have h2 := (D.nbc.infW_alg _ (D.nbc.wtAU _ (D.nbc.embAV i P)) ((D.naut.iotaQC i).toRingHom.comp τ)).1
  have h3 := h2.map (f := fun z : ℂ => -z + ((D.R.nV : ℂ) - 1) / 2) (fun a b hab => by simpa using hab)
  rw [← h1] at h3
  exact h3.of_map _

end GlobalTheory.AbsIrrConstituents

namespace GlobalTheory.AbsIrrConstituents

/- English proof (translation)
Apply `(h _).mp` to reduce the goal to its premises. Establish `e : τ (((l : ℕ) : 𝓞 E) : E) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l])`. Simplify using `only [map_natCast]`. Rewrite using `[e, PadicAlgCl.norm_extends]`. Conclude with `Padic.norm_p_lt_one`.
-/
theorem mem_of_induces' (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime]
    (τ : E →+* PadicAlgCl l) (w : HeightOneSpectrum (𝓞 E))
    (h : ∀ x : 𝓞 E, ‖τ (x : E)‖ < 1 ↔ x ∈ w.asIdeal) : ((l : ℕ) : 𝓞 E) ∈ w.asIdeal := by
  apply (h _).mp
  have e : τ (((l : ℕ) : 𝓞 E) : E) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by
    simp only [map_natCast]
  rw [e, PadicAlgCl.norm_extends]
  exact Padic.norm_p_lt_one

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sumRep_coe {k Γ : Type} [CommRing k] [Group Γ] {a b : ℕ} (ρ : Γ →* GL (Fin a) k)
    (ρ' : Γ →* GL (Fin b) k) (g : Γ) :
    ((SumRepresentations.At.sumRep ρ ρ' g : GL (Fin (a + b)) k) : Matrix _ _ k) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (ρ g : Matrix (Fin a) (Fin a) k) 0 0 (ρ' g : Matrix (Fin b) (Fin b) k)) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_mapRep {k L Γ : Type} [CommRing k] [CommRing L] [Group Γ] {a : ℕ} (f : k →+* L)
    (ρ : Γ →* GL (Fin a) k) (g : Γ) :
    ((mapRep f ρ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) = (ρ g : Matrix (Fin a) (Fin a) k).map f := rfl

/- English proof (translation)
Use extensionality with `g i j`. Rewrite using `[coe_mapRep, sumRep_coe, sumRep_coe, coe_mapRep, coe_mapRep]`. Simplify using `only [Matrix.reindex_apply, Matrix.map_apply, Matrix.submatrix_apply]`. Apply the tactic sequence `rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> simp`.
-/
theorem mapRep_sumRep {k L Γ : Type} [CommRing k] [CommRing L] [Group Γ] {a b : ℕ} (f : k →+* L)
    (ρ : Γ →* GL (Fin a) k) (ρ' : Γ →* GL (Fin b) k) :
    mapRep f (SumRepresentations.At.sumRep ρ ρ') = SumRepresentations.At.sumRep (mapRep f ρ) (mapRep f ρ') := by
  ext g i j
  rw [coe_mapRep, sumRep_coe, sumRep_coe, coe_mapRep, coe_mapRep]
  simp only [Matrix.reindex_apply, Matrix.map_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> simp

/- English proof (translation)
Unfold `SumRepresentations.At.ContQ at *`. Simplify using `only [sumRep_coe, Matrix.reindex_apply]`. Conclude with `(Continuous.matrix_fromBlocks h continuous_const continuous_const h').matrix_submatrix _ _`.
-/
theorem contQ_sumRep (D : D7) (i : D.nd.Loc) {a b : ℕ}
    (ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin a) (Qbar (D.nd.l i)))
    (ρ' : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin b) (Qbar (D.nd.l i)))
    (h : SumRepresentations.At.ContQ D.nd i ρ) (h' : SumRepresentations.At.ContQ D.nd i ρ') : SumRepresentations.At.ContQ D.nd i (SumRepresentations.At.sumRep ρ ρ') := by
  unfold SumRepresentations.At.ContQ at *
  simp only [sumRep_coe, Matrix.reindex_apply]
  exact (Continuous.matrix_fromBlocks h continuous_const continuous_const h').matrix_submatrix _ _

end GlobalTheory.AbsIrrConstituents

namespace GlobalTheory.AbsIrrConstituents

/- English proof (translation)
Substitute `h` using the available equality. Introduce `g`. Establish `e1 : (Units.map (f.mapMatrix : Matrix (Fin (d + d + u)) (Fin (d + d + u)) k →+* _).toMonoidHom Pm)⁻¹ * mapRep f ρ g * Units.map (f.mapMatrix : Matrix (Fin (d + d + u)) (Fin (d + d + u)) k →+* _).toMonoidHom Pm = Units.map (f.mapMatrix : Matrix (Fin (d + d + u)) (Fin (d + d + u)) …`. Simplify using `only [map_mul, map_inv]`. Both sides reduce to the same expression.

Rewrite using `[e1]`. Use `show ((Pm⁻¹ * ρ g * Pm : GL (Fin (d + d + u)) k) : Matrix (Fin (d + d + u)) (Fin (d + d + u)) k).map f = _`. Rewrite using `[hrel g]`. Simplify using `only [finCongr_refl, Matrix.reindex_refl_refl]`. Rewrite using `[← mapRep_sumRep, ← mapRep_sumRep, coe_mapRep]`.
-/
theorem rel_map' {k L Γ : Type} [Field k] [Field L] [Group Γ] (f : k →+* L) {a d u : ℕ} (h : d + d + u = a)
    (ρ : Γ →* GL (Fin a) k) (σ : Γ →* GL (Fin d) k) (υ : Γ →* GL (Fin u) k) (Pm : GL (Fin a) k)
    (hrel : ∀ g, ((Pm⁻¹ * ρ g * Pm : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) =
        Matrix.reindex (finCongr h) (finCongr h)
          ((SumRepresentations.At.sumRep (SumRepresentations.At.sumRep σ σ) υ g : GL (Fin (d + d + u)) k) : Matrix _ _ k)) :
    ∀ g, (((Units.map (f.mapMatrix : Matrix (Fin a) (Fin a) k →+* Matrix (Fin a) (Fin a) L).toMonoidHom Pm)⁻¹ *
        mapRep f ρ g * Units.map (f.mapMatrix : Matrix (Fin a) (Fin a) k →+* Matrix (Fin a) (Fin a) L).toMonoidHom Pm :
          GL (Fin a) L) : Matrix (Fin a) (Fin a) L) =
      Matrix.reindex (finCongr h) (finCongr h)
        ((SumRepresentations.At.sumRep (SumRepresentations.At.sumRep (mapRep f σ) (mapRep f σ)) (mapRep f υ) g : GL (Fin (d + d + u)) L) :
          Matrix _ _ L) := by
  subst h
  intro g
  have e1 : (Units.map (f.mapMatrix : Matrix (Fin (d + d + u)) (Fin (d + d + u)) k →+* _).toMonoidHom Pm)⁻¹ *
      mapRep f ρ g * Units.map (f.mapMatrix : Matrix (Fin (d + d + u)) (Fin (d + d + u)) k →+* _).toMonoidHom Pm =
      Units.map (f.mapMatrix : Matrix (Fin (d + d + u)) (Fin (d + d + u)) k →+* Matrix _ _ L).toMonoidHom
        (Pm⁻¹ * ρ g * Pm) := by
    simp only [map_mul, map_inv]; rfl
  rw [e1]
  show ((Pm⁻¹ * ρ g * Pm : GL (Fin (d + d + u)) k) : Matrix (Fin (d + d + u)) (Fin (d + d + u)) k).map f = _
  rw [hrel g]
  simp only [finCongr_refl, Matrix.reindex_refl_refl]
  rw [← mapRep_sumRep, ← mapRep_sumRep, coe_mapRep]

/- English proof (translation)
Introduce `hnd`. Substitute `h` using the available equality. Take `⟨-, -, hJC, hG⟩` from `ht.2.2`. Take `⟨-, hconj, hsum, -⟩` from `hG i`. Establish `hPm : ∀ g, SumRepresentations.At.sumRep (SumRepresentations.At.sumRep σ σ) υ g = Pm⁻¹ * ρ g * Pm`.

Introduce `g`. Use `ext1`. Rewrite using `[hrel g]`. Simplify using `only [finCongr_refl, Matrix.reindex_refl_refl]`. Establish `hcA` using `contQ_sumRep D i σ σ hcσ hcσ`.

Take `⟨hdRc, -, hJc⟩` from `hconj _ ρ _ hc Pm hPm`. Take `⟨hdRs, -, hJs⟩` from `hsum _ _ _ υ hcA hcυ`. Take `⟨hdRσ, -, hJσ⟩` from `hsum _ _ σ σ hcσ hcσ`. Establish `hdR' : ∀ w', InducesW D.nd i τ w' → D.naut.IsdRW i (SumRepresentations.At.sumRep (SumRepresentations.At.sumRep σ σ) υ) w'` using `fun w' hw' => (hdRc w' (hpl w' hw')).2 (hdR w' hw')`. Establish `hdRA : ∀ w', InducesW D.nd i τ w' → D.naut.IsdRW i (SumRepresentations.At.sumRep σ σ) w' ∧ D.naut.IsdRW i υ w'` using `fun w' hw' => (hdRs w' (hpl w' hw')).1 (hdR' w' hw')`.

Establish `hdRσ' : ∀ w', InducesW D.nd i τ w' → D.naut.IsdRW i σ w' ∧ D.naut.IsdRW i σ w'` using `fun w' hw' => (hdRσ w' (hpl w' hw')).1 (hdRA w' hw').1`. Establish `e : D.naut.jumpsW i ρ τ = D.naut.jumpsW i σ τ + D.naut.jumpsW i σ τ + D.naut.jumpsW i υ τ`. Rewrite using `[← hJc τ hdR, hJs τ hdRA, hJσ τ hdRσ']`. Establish `hcard` using `hJC i _ σ w τ hw hτ (hdRσ' w hτ).1`. Rewrite `hnd` using `[e]`.

Establish `h2` using `(Multiset.nodup_add.1 (Multiset.nodup_add.1 hnd).1).2.2`. Take `⟨j, hj⟩` from `Multiset.card_pos_iff_exists_mem.1 (hcard ▸ hd)`. Conclude with `Multiset.disjoint_left.1 h2 hj hj`.
-/
theorem jumps_not_nodup' (D : D7) (ht : SumRepresentations.tie0 D) (i : D.nd.Loc) (τ : D.host.E →+* Qbar (D.nd.l i))
    (w : PlE D.host) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (hτ : InducesW D.nd i τ w)
    (hpl : ∀ w', InducesW D.nd i τ w' → w' ∈ placesOver D.host.E (D.nd.l i))
    {a d u : ℕ} (h : d + d + u = a) (ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin a) (Qbar (D.nd.l i)))
    (σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin d) (Qbar (D.nd.l i)))
    (υ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin u) (Qbar (D.nd.l i))) (Pm : GL (Fin a) (Qbar (D.nd.l i)))
    (hd : 0 < d) (hc : SumRepresentations.At.ContQ D.nd i ρ) (hcσ : SumRepresentations.At.ContQ D.nd i σ) (hcυ : SumRepresentations.At.ContQ D.nd i υ)
    (hrel : ∀ g, ((Pm⁻¹ * ρ g * Pm : GL (Fin a) (Qbar (D.nd.l i))) : Matrix (Fin a) (Fin a) (Qbar (D.nd.l i))) =
        Matrix.reindex (finCongr h) (finCongr h)
          ((SumRepresentations.At.sumRep (SumRepresentations.At.sumRep σ σ) υ g : GL (Fin (d + d + u)) (Qbar (D.nd.l i))) :
            Matrix _ _ (Qbar (D.nd.l i))))
    (hdR : ∀ w', InducesW D.nd i τ w' → D.naut.IsdRW i ρ w') :
    ¬ (D.naut.jumpsW i ρ τ).Nodup := by
  intro hnd
  subst h
  obtain ⟨-, -, hJC, hG⟩ := ht.2.2
  obtain ⟨-, hconj, hsum, -⟩ := hG i
  have hPm : ∀ g, SumRepresentations.At.sumRep (SumRepresentations.At.sumRep σ σ) υ g = Pm⁻¹ * ρ g * Pm := by
    intro g; ext1; rw [hrel g]; simp only [finCongr_refl, Matrix.reindex_refl_refl]
  have hcA := contQ_sumRep D i σ σ hcσ hcσ
  obtain ⟨hdRc, -, hJc⟩ := hconj _ ρ _ hc Pm hPm
  obtain ⟨hdRs, -, hJs⟩ := hsum _ _ _ υ hcA hcυ
  obtain ⟨hdRσ, -, hJσ⟩ := hsum _ _ σ σ hcσ hcσ
  have hdR' : ∀ w', InducesW D.nd i τ w' → D.naut.IsdRW i (SumRepresentations.At.sumRep (SumRepresentations.At.sumRep σ σ) υ) w' :=
    fun w' hw' => (hdRc w' (hpl w' hw')).2 (hdR w' hw')
  have hdRA : ∀ w', InducesW D.nd i τ w' → D.naut.IsdRW i (SumRepresentations.At.sumRep σ σ) w' ∧ D.naut.IsdRW i υ w' :=
    fun w' hw' => (hdRs w' (hpl w' hw')).1 (hdR' w' hw')
  have hdRσ' : ∀ w', InducesW D.nd i τ w' → D.naut.IsdRW i σ w' ∧ D.naut.IsdRW i σ w' :=
    fun w' hw' => (hdRσ w' (hpl w' hw')).1 (hdRA w' hw').1
  have e : D.naut.jumpsW i ρ τ = D.naut.jumpsW i σ τ + D.naut.jumpsW i σ τ + D.naut.jumpsW i υ τ := by
    rw [← hJc τ hdR, hJs τ hdRA, hJσ τ hdRσ']
  have hcard := hJC i _ σ w τ hw hτ (hdRσ' w hτ).1
  rw [e] at hnd
  have h2 := (Multiset.nodup_add.1 (Multiset.nodup_add.1 hnd).1).2.2
  obtain ⟨j, hj⟩ := Multiset.card_pos_iff_exists_mem.1 (hcard ▸ hd)
  exact Multiset.disjoint_left.1 h2 hj hj

end GlobalTheory.AbsIrrConstituents

namespace GlobalTheory.AbsIrrConstituents

/- English proof (translation)
Substitute `h` using the available equality. Establish `hM : Continuous fun g => ((SumRepresentations.At.sumRep ρ₁ ρ₂ g : GL (Fin (b + c)) k) : Matrix (Fin (b + c)) (Fin (b + c)) k)`. Establish `e : (fun g => ((SumRepresentations.At.sumRep ρ₁ ρ₂ g : GL (Fin (b + c)) k) : Matrix (Fin (b + c)) (Fin (b + c)) k)) = fun g => ((Pm⁻¹ : GL (Fin (b + c)) k) : Matrix (Fin (b + c)) (Fin (b + c)) k) * (ρ g : Matrix _ _ k) * (Pm : Matrix _ _ k)`. Use function extensionality and compare the values at `g`. Rewrite using `[← Units.val_mul, ← Units.val_mul, hrel g]`.

Simplify using `only [finCongr_refl, Matrix.reindex_refl_refl]`. Rewrite using `[e]`. Conclude with `(continuous_const.matrix_mul hc).matrix_mul continuous_const`. Prove the components needed by the constructor for the conclusion. Establish `e : (fun g => ((ρ₁ g : GL (Fin b) k) : Matrix (Fin b) (Fin b) k)) = fun g => (((SumRepresentations.At.sumRep ρ₁ ρ₂ g : GL (Fin (b + c)) k) : Matrix (Fin (b + c)) (Fin (b + c)) k)).submatrix (finSumFinEquiv ∘ Sum.inl) (finSumFinEquiv ∘ Sum.inl)`.

Use function extensionality and compare the values at `g`. Use extensionality with `i j`. Simplify using `[sumRep_coe]`. Rewrite using `[e]`. Conclude with `hM.matrix_submatrix _ _`.

Establish `e : (fun g => ((ρ₂ g : GL (Fin c) k) : Matrix (Fin c) (Fin c) k)) = fun g => (((SumRepresentations.At.sumRep ρ₁ ρ₂ g : GL (Fin (b + c)) k) : Matrix (Fin (b + c)) (Fin (b + c)) k)).submatrix (finSumFinEquiv ∘ Sum.inr) (finSumFinEquiv ∘ Sum.inr)`. Use function extensionality and compare the values at `g`. Use extensionality with `i j`. Simplify using `[sumRep_coe]`. Rewrite using `[e]`.

Conclude with `hM.matrix_submatrix _ _`.
-/
theorem continuous_blocks' {k Γ : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] [Group Γ]
    [TopologicalSpace Γ] {a b c : ℕ} (ρ : Γ →* GL (Fin a) k) (ρ₁ : Γ →* GL (Fin b) k)
    (ρ₂ : Γ →* GL (Fin c) k) (h : b + c = a) (Pm : GL (Fin a) k)
    (hrel : ∀ g, ((Pm⁻¹ * ρ g * Pm : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) =
      Matrix.reindex (finCongr h) (finCongr h) ((SumRepresentations.At.sumRep ρ₁ ρ₂ g : GL (Fin (b + c)) k) : Matrix (Fin (b + c)) (Fin (b + c)) k))
    (hc : Continuous fun g => ((ρ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k)) :
    (Continuous fun g => ((ρ₁ g : GL (Fin b) k) : Matrix (Fin b) (Fin b) k)) ∧
      Continuous fun g => ((ρ₂ g : GL (Fin c) k) : Matrix (Fin c) (Fin c) k) := by
  subst h
  have hM : Continuous fun g => ((SumRepresentations.At.sumRep ρ₁ ρ₂ g : GL (Fin (b + c)) k) : Matrix (Fin (b + c)) (Fin (b + c)) k) := by
    have e : (fun g => ((SumRepresentations.At.sumRep ρ₁ ρ₂ g : GL (Fin (b + c)) k) : Matrix (Fin (b + c)) (Fin (b + c)) k)) = fun g =>
        ((Pm⁻¹ : GL (Fin (b + c)) k) : Matrix (Fin (b + c)) (Fin (b + c)) k) * (ρ g : Matrix _ _ k) * (Pm : Matrix _ _ k) := by
      funext g
      rw [← Units.val_mul, ← Units.val_mul, hrel g]
      simp only [finCongr_refl, Matrix.reindex_refl_refl]
    rw [e]
    exact (continuous_const.matrix_mul hc).matrix_mul continuous_const
  constructor
  · have e : (fun g => ((ρ₁ g : GL (Fin b) k) : Matrix (Fin b) (Fin b) k)) = fun g =>
        (((SumRepresentations.At.sumRep ρ₁ ρ₂ g : GL (Fin (b + c)) k) : Matrix (Fin (b + c)) (Fin (b + c)) k)).submatrix
          (finSumFinEquiv ∘ Sum.inl) (finSumFinEquiv ∘ Sum.inl) := by
      funext g; ext i j; simp [sumRep_coe]
    rw [e]; exact hM.matrix_submatrix _ _
  · have e : (fun g => ((ρ₂ g : GL (Fin c) k) : Matrix (Fin c) (Fin c) k)) = fun g =>
        (((SumRepresentations.At.sumRep ρ₁ ρ₂ g : GL (Fin (b + c)) k) : Matrix (Fin (b + c)) (Fin (b + c)) k)).submatrix
          (finSumFinEquiv ∘ Sum.inr) (finSumFinEquiv ∘ Sum.inr) := by
      funext g; ext i j; simp [sumRep_coe]
    rw [e]; exact hM.matrix_submatrix _ _

end GlobalTheory.AbsIrrConstituents

namespace GlobalTheory.AbsIrrConstituents

/- English proof (translation)
Introduce `D ht hadm hH i r hr`. Use `letI alg : Algebra (Kf D.nd i) (Qbar (D.nd.l i)) := (D.naut.iotaQ i).toAlgebra`. Establish `hss : ∀ x, IsSSRep (mapRep (algebraMap (Kf D.nd i) (AlgebraicClosure (Kf D.nd i))) (mapRep (algebraMap (D.nd.O i) (Kf D.nd i)) (r x)))`. Introduce `x`. Set `f : AlgebraicClosure (Kf D.nd i) →ₐ[Kf D.nd i] Qbar (D.nd.l i)` to `IsAlgClosed.lift`.

Use `letI : Algebra (AlgebraicClosure (Kf D.nd i)) (Qbar (D.nd.l i)) := f.toRingHom.toAlgebra`. Apply `SumRepresentations.isSSRep_descent (L := Qbar (D.nd.l i))` to reduce the goal to its premises. Establish `e : ((algebraMap (AlgebraicClosure (Kf D.nd i)) (Qbar (D.nd.l i))).comp (algebraMap (Kf D.nd i) (AlgebraicClosure (Kf D.nd i)))).comp (algebraMap (D.nd.O i) (Kf D.nd i)) = iotaOQ D.nd D.naut i`. Use extensionality with `z`. Use `show f (algebraMap (Kf D.nd i) _ (algebraMap _ (Kf D.nd i) z)) = D.naut.iotaQ i (algebraMap _ _ z)`.

Rewrite using `[f.commutes]`. Both sides reduce to the same expression. Rewrite using `[← mapRep_comp, ← mapRep_comp, e]`. Conclude with `(hr x).2.1`. Take `⟨K', hF, hA, hFD, hsplit⟩` from `GlobalTheory.T.exists_finiteDimensional_ext_irrSub_absIrr (fun x => mapRep (algebraMap (D.nd.O i) (Kf D.nd i)) (r x)) hss`.

Use `⟨K', hF, hA, hFD, fun x => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[mapRep_comp]`. Conclude with `hsplit x`. Introduce `W₁ W₂ h1 h2 hdis hiso`. Set `f' : K' →ₐ[Kf D.nd i] Qbar (D.nd.l i)` to `IsAlgClosed.lift`.

Establish `e' : (f'.toRingHom).comp ((algebraMap (Kf D.nd i) K').comp (algebraMap (D.nd.O i) (Kf D.nd i))) = iotaOQ D.nd D.naut i`. Use extensionality with `z`. Use `show f' (algebraMap (Kf D.nd i) K' (algebraMap _ (Kf D.nd i) z)) = D.naut.iotaQ i (algebraMap _ _ z)`. Rewrite using `[f'.commutes]`. Both sides reduce to the same expression.

Establish `hQ : mapRep f'.toRingHom (mapRep ((algebraMap (Kf D.nd i) K').comp (algebraMap (D.nd.O i) (Kf D.nd i))) (r x)) = mapRep (iotaOQ D.nd D.naut i) (r x)`. Rewrite using `[← mapRep_comp, e']`. Establish `hssK : IsSSRep (mapRep ((algebraMap (Kf D.nd i) K').comp (algebraMap (D.nd.O i) (Kf D.nd i))) (r x))`. Use `letI : Algebra K' (Qbar (D.nd.l i)) := f'.toRingHom.toAlgebra`. Apply `SumRepresentations.isSSRep_descent (L := Qbar (D.nd.l i))` to reduce the goal to its premises.

Use `show IsSSRep (mapRep f'.toRingHom _)`. Rewrite using `[hQ]`. Conclude with `(hr x).2.1`. Take `⟨d, u, σ, υ, h, Pm, hd, hrel⟩` from `GlobalTheory.T.exists_conj_double_block_of_iso_subspaces _ W₁ W₂ hssK h1.2.1 h2.2.1 h1.1 hdis hiso`. Establish `hrelQ` using `rel_map' f'.toRingHom h _ σ υ Pm hrel`.

Rewrite `hrelQ` using `[hQ]`. Establish `hcQ : SumRepresentations.At.ContQ D.nd i (mapRep (iotaOQ D.nd D.naut i) (r x))` using `(hr x).1`. Take `⟨hcA, hcυ⟩` from `continuous_blocks' _ _ _ h _ hrelQ hcQ`. Establish `hcσ : SumRepresentations.At.ContQ D.nd i (mapRep f'.toRingHom σ)` using `(continuous_blocks' (SumRepresentations.At.sumRep (mapRep f'.toRingHom σ) (mapRep f'.toRingHom σ)) (mapRep f'.toRingHom σ) (mapRep f'.toRingHom σ) rfl 1 (fun g => by simp) hcA).1`. Take `⟨P, hP⟩` from `D.naut.pt_surj i x`.

Take `⟨Pa, hPa⟩` from `hadm i P`. Take `⟨-, hon⟩` from `hH i x P Pa hP hPa _ (hr x)`. Take `⟨τ, w, hτw⟩` from `GlobalTheory.T.exists_padicAlgCl_embedding_and_place_norm_lt_one D.host.E (D.nd.l i)`. Establish `hpl : ∀ w', InducesW D.nd i τ w' → w' ∈ placesOver D.host.E (D.nd.l i)` using `fun w' hw' => mem_of_induces' D.host.E (D.nd.l i) τ w' hw'`. Establish `hτ : InducesW D.nd i τ w` using `hτw`.

Establish `hJ` using `(hon w (hpl w hτ)).2.2 τ hτ`. Use `jumps_not_nodup' D ht i τ w (hpl w hτ) hτ hpl h _ _ _ _ hd hcQ hcσ hcυ hrelQ (fun w' hw' => (hon w' (hpl w' hw')).1) ?_` and prove the remaining obligations. Rewrite using `[hJ]`. Conclude with `fixedJumps_nodup D i P τ`.
-/
theorem absIrr_and_distinct_constituents : ∀ D : D7, SumRepresentations.tie0 D → SumRepresentations.adm1 D → (∀ (i : D.nd.Loc) (x : D.nd.X i) (P : D.naut.AV i) (Pa : List (Part D.naut.CG)), D.naut.ptV i P = some x → IsBCV D.nd D.naut i P Pa → ∀ ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (Qbar (D.nd.l i)), SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x ρ → (∀ w, w ∉ placesOver D.host.E (D.nd.l i) → D.naut.wdOf i ρ w = D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2)) ∧ ∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i ρ w ∧ D.naut.wdOf i ρ w = D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2) ∧ ∀ τ, InducesW D.nd i τ w → D.naut.jumpsW i ρ τ = D.naut.locAutHodgeTateWeightsLevelZero i τ) → ∀ (i : D.nd.Loc) (r : D.nd.X i → (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (D.nd.O i))), (∀ x, SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x (mapRep (iotaOQ D.nd D.naut i) (r x))) → SumRepresentations.At.G3a D.nd i r := by
  intro D ht hadm hH i r hr
  classical
  letI alg : Algebra (Kf D.nd i) (Qbar (D.nd.l i)) := (D.naut.iotaQ i).toAlgebra
  have hss : ∀ x, IsSSRep (mapRep (algebraMap (Kf D.nd i) (AlgebraicClosure (Kf D.nd i)))
      (mapRep (algebraMap (D.nd.O i) (Kf D.nd i)) (r x))) := by
    intro x
    let f : AlgebraicClosure (Kf D.nd i) →ₐ[Kf D.nd i] Qbar (D.nd.l i) := IsAlgClosed.lift
    letI : Algebra (AlgebraicClosure (Kf D.nd i)) (Qbar (D.nd.l i)) := f.toRingHom.toAlgebra
    apply SumRepresentations.isSSRep_descent (L := Qbar (D.nd.l i))
    have e : ((algebraMap (AlgebraicClosure (Kf D.nd i)) (Qbar (D.nd.l i))).comp
        (algebraMap (Kf D.nd i) (AlgebraicClosure (Kf D.nd i)))).comp (algebraMap (D.nd.O i) (Kf D.nd i)) =
        iotaOQ D.nd D.naut i := by
      ext z
      show f (algebraMap (Kf D.nd i) _ (algebraMap _ (Kf D.nd i) z)) = D.naut.iotaQ i (algebraMap _ _ z)
      rw [f.commutes]; rfl
    rw [← mapRep_comp, ← mapRep_comp, e]
    exact (hr x).2.1
  obtain ⟨K', hF, hA, hFD, hsplit⟩ :=
    GlobalTheory.T.exists_finiteDimensional_ext_irrSub_absIrr (fun x => mapRep (algebraMap (D.nd.O i) (Kf D.nd i)) (r x)) hss
  refine ⟨K', hF, hA, hFD, fun x => ⟨?_, ?_⟩⟩
  · rw [mapRep_comp]; exact hsplit x
  · intro W₁ W₂ h1 h2 hdis hiso
    let f' : K' →ₐ[Kf D.nd i] Qbar (D.nd.l i) := IsAlgClosed.lift
    have e' : (f'.toRingHom).comp ((algebraMap (Kf D.nd i) K').comp (algebraMap (D.nd.O i) (Kf D.nd i))) =
        iotaOQ D.nd D.naut i := by
      ext z
      show f' (algebraMap (Kf D.nd i) K' (algebraMap _ (Kf D.nd i) z)) = D.naut.iotaQ i (algebraMap _ _ z)
      rw [f'.commutes]; rfl
    have hQ : mapRep f'.toRingHom (mapRep ((algebraMap (Kf D.nd i) K').comp (algebraMap (D.nd.O i) (Kf D.nd i))) (r x)) =
        mapRep (iotaOQ D.nd D.naut i) (r x) := by
      rw [← mapRep_comp, e']
    have hssK : IsSSRep (mapRep ((algebraMap (Kf D.nd i) K').comp (algebraMap (D.nd.O i) (Kf D.nd i))) (r x)) := by
      letI : Algebra K' (Qbar (D.nd.l i)) := f'.toRingHom.toAlgebra
      apply SumRepresentations.isSSRep_descent (L := Qbar (D.nd.l i))
      show IsSSRep (mapRep f'.toRingHom _)
      rw [hQ]; exact (hr x).2.1
    obtain ⟨d, u, σ, υ, h, Pm, hd, hrel⟩ := GlobalTheory.T.exists_conj_double_block_of_iso_subspaces _ W₁ W₂ hssK h1.2.1 h2.2.1 h1.1 hdis hiso
    have hrelQ := rel_map' f'.toRingHom h _ σ υ Pm hrel
    rw [hQ] at hrelQ
    have hcQ : SumRepresentations.At.ContQ D.nd i (mapRep (iotaOQ D.nd D.naut i) (r x)) := (hr x).1
    obtain ⟨hcA, hcυ⟩ := continuous_blocks' _ _ _ h _ hrelQ hcQ
    have hcσ : SumRepresentations.At.ContQ D.nd i (mapRep f'.toRingHom σ) :=
      (continuous_blocks' (SumRepresentations.At.sumRep (mapRep f'.toRingHom σ) (mapRep f'.toRingHom σ))
        (mapRep f'.toRingHom σ) (mapRep f'.toRingHom σ) rfl 1 (fun g => by simp) hcA).1
    obtain ⟨P, hP⟩ := D.naut.pt_surj i x
    obtain ⟨Pa, hPa⟩ := hadm i P
    obtain ⟨-, hon⟩ := hH i x P Pa hP hPa _ (hr x)
    obtain ⟨τ, w, hτw⟩ := GlobalTheory.T.exists_padicAlgCl_embedding_and_place_norm_lt_one D.host.E (D.nd.l i)
    have hpl : ∀ w', InducesW D.nd i τ w' → w' ∈ placesOver D.host.E (D.nd.l i) :=
      fun w' hw' => mem_of_induces' D.host.E (D.nd.l i) τ w' hw'
    have hτ : InducesW D.nd i τ w := hτw
    have hJ := (hon w (hpl w hτ)).2.2 τ hτ
    refine jumps_not_nodup' D ht i τ w (hpl w hτ) hτ hpl h _ _ _ _ hd hcQ hcσ hcυ hrelQ
      (fun w' hw' => (hon w' (hpl w' hw')).1) ?_
    rw [hJ]; exact fixedJumps_nodup D i P τ

end GlobalTheory.AbsIrrConstituents
