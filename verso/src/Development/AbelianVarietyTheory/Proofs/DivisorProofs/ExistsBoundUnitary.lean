import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Development.AbelianVarietyTheory.Definitions.Foundations.ClassMassEqSumOfBijective
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmTypeRestrictRealSubfieldInfinitePlaceBijective
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IntegrableOnFundamentalDomainOfCocompact
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsInfFamFamily

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum NumberField Matrix
open scoped TensorProduct ComplexOrder MatrixOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefiniteQuotient

/- English proof (translation)
Use `open scoped Matrix.Norms.L2Operator in`. Take `⟨B, hB, rfl⟩` from `CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp hG.isStrictlyPositive`. Take `⟨B, rfl⟩` from `hB`. Use `⟨∑ i, ∑ j, ∑ l, ∑ k, ‖(B⁻¹).1 i k‖ * ‖B.1 l j‖, fun g hg i j => ?_⟩` and prove the remaining obligations. Establish `hu : B.1 * g * (B⁻¹).1 ∈ Matrix.unitaryGroup (Fin n) ℂ`.

Rewrite using `[Matrix.mem_unitaryGroup_iff']`. Establish `: star (B.1 * g * (B⁻¹).1) * (B.1 * g * (B⁻¹).1) = star (B⁻¹).1 * (gᴴ * (star B.1 * B.1) * g) * (B⁻¹).1`. Simplify using `only [star_mul, Matrix.star_eq_conjTranspose, Matrix.mul_assoc]`. Rewrite using `[this, hg, ← Matrix.mul_assoc, ← star_mul, Units.mul_inv, star_one, Matrix.one_mul, Units.mul_inv]`. Establish `e : g = (B⁻¹).1 * (B.1 * g * (B⁻¹).1) * B.1`.

Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]`. Establish `h1 : ‖g i j‖ ≤ ∑ l, ∑ k, ‖(B⁻¹).1 i k‖ * ‖B.1 l j‖`. Generalize the expression as in `B.1 * g * (B⁻¹).1 = u at hu e`. Rewrite using `[e, Matrix.mul_apply]`. Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)` and prove the remaining obligations.

Rewrite using `[Matrix.mul_apply, Finset.sum_mul]`. Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)` and prove the remaining obligations. Rewrite using `[norm_mul, norm_mul]`. Conclude with `mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (norm_nonneg _) (entry_norm_bound_of_unitary hu k l)) (norm_nonneg _)`. Use `h1.trans ?_` and prove the remaining obligations.

Use `(Finset.single_le_sum (f := fun j => ∑ l, ∑ k, ‖(B⁻¹).1 i k‖ * ‖B.1 l j‖) (fun _ _ => by positivity) (Finset.mem_univ j)).trans ?_` and prove the remaining obligations. Conclude with `Finset.single_le_sum (f := fun i => ∑ j, ∑ l, ∑ k, ‖(B⁻¹).1 i k‖ * ‖B.1 l j‖) (fun _ _ => by positivity) (Finset.mem_univ i)`.
-/
theorem exists_bound_unitary {n : ℕ} {G : Matrix (Fin n) (Fin n) ℂ} (hG : G.PosDef) :
    ∃ R : ℝ, ∀ g : Matrix (Fin n) (Fin n) ℂ, gᴴ * G * g = G → ∀ i j, ‖g i j‖ ≤ R := by
  open scoped Matrix.Norms.L2Operator in
  obtain ⟨B, hB, rfl⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp hG.isStrictlyPositive
  obtain ⟨B, rfl⟩ := hB
  refine ⟨∑ i, ∑ j, ∑ l, ∑ k, ‖(B⁻¹).1 i k‖ * ‖B.1 l j‖, fun g hg i j => ?_⟩
  have hu : B.1 * g * (B⁻¹).1 ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']
    have : star (B.1 * g * (B⁻¹).1) * (B.1 * g * (B⁻¹).1) =
        star (B⁻¹).1 * (gᴴ * (star B.1 * B.1) * g) * (B⁻¹).1 := by
      simp only [star_mul, Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
    rw [this, hg, ← Matrix.mul_assoc, ← star_mul, Units.mul_inv, star_one, Matrix.one_mul, Units.mul_inv]
  have e : g = (B⁻¹).1 * (B.1 * g * (B⁻¹).1) * B.1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one, ← Matrix.mul_assoc,
      Units.inv_mul, Matrix.one_mul]
  have h1 : ‖g i j‖ ≤ ∑ l, ∑ k, ‖(B⁻¹).1 i k‖ * ‖B.1 l j‖ := by
    generalize B.1 * g * (B⁻¹).1 = u at hu e
    rw [e, Matrix.mul_apply]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (norm_nonneg _)
      (entry_norm_bound_of_unitary hu k l)) (norm_nonneg _)
  refine h1.trans ?_
  refine (Finset.single_le_sum (f := fun j => ∑ l, ∑ k, ‖(B⁻¹).1 i k‖ * ‖B.1 l j‖)
    (fun _ _ => by positivity) (Finset.mem_univ j)).trans ?_
  exact Finset.single_le_sum (f := fun i => ∑ j, ∑ l, ∑ k, ‖(B⁻¹).1 i k‖ * ‖B.1 l j‖)
    (fun _ _ => by positivity) (Finset.mem_univ i)

/- English proof (translation)
Take `⟨e, P, hP⟩` from `h`. Establish `h1 : Formalism.UG.Jpq p 0 = 1`. Use extensionality with `(i | i) (j | j)`. Simplify using `[Formalism.UG.Jpq, Matrix.one_apply]`. Conclude with `j.elim0`.

Conclude with `i.elim0`. Conclude with `i.elim0`. Establish `h2 : (star P.1 * G.reindex e e * P.1).PosDef`. Establish `: star P.1 * G.reindex e e * P.1 = 1` using `hP.trans h1`. Rewrite using `[this]`.

Conclude with `Matrix.PosDef.one`. Establish `h3` using `((Matrix.IsUnit.posDef_star_left_conjugate_iff P.isUnit).1 h2).submatrix e.injective`. Simplify using `using h3`.
-/
theorem posDef_of_signature {n p : ℕ} {G : Matrix (Fin n) (Fin n) ℂ} (h : Formalism.UG.HasSignature G p 0) : G.PosDef := by
  obtain ⟨e, P, hP⟩ := h
  have h1 : Formalism.UG.Jpq p 0 = 1 := by
    ext (i | i) (j | j)
    · simp [Formalism.UG.Jpq, Matrix.one_apply]
    · exact j.elim0
    · exact i.elim0
    · exact i.elim0
  have h2 : (star P.1 * G.reindex e e * P.1).PosDef := by
    have : star P.1 * G.reindex e e * P.1 = 1 := hP.trans h1
    rw [this]; exact Matrix.PosDef.one
  have h3 := ((Matrix.IsUnit.posDef_star_left_conjugate_iff P.isUnit).1 h2).submatrix e.injective
  simpa using h3

variable {D : D7}

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun i j => V.herm.eq (V.frame j) (V.frame i), GlobalTheory.StabCompact.det_gram_ne_zero V⟩`.
-/
theorem gram_hermND (V : HSp D) : IsHermND D.sp.cm.sig V.gram :=
  ⟨fun i j => V.herm.eq (V.frame j) (V.frame i), GlobalTheory.StabCompact.det_gram_ne_zero V⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨D.sp.cm.totReal, D.sp.cm.cmUnram.1, D.sp.cm.deg2, fun τ x => D.sp.cm.cmUnram.2.1 τ x⟩`.
-/
theorem cmExt (D : D7) : IsCMExt D.host.F D.host.E D.sp.cm.sig :=
  ⟨D.sp.cm.totReal, D.sp.cm.cmUnram.1, D.sp.cm.deg2, fun τ x => D.sp.cm.cmUnram.2.1 τ x⟩

/- English proof (translation)
Use `⟨D.sp.cm.totReal, fun ι => Or.inl fun x hx => ?_⟩` and prove the remaining obligations. Establish `hτ` using `(cmExt D).2.2.2`. Take `⟨τ, hι⟩` from `(GlobalTheory.CMTypePlaces.places_bijective D).2 (InfinitePlace.mk (Complex.ofRealHom.comp ι))`. Establish `hι' : (tauE D τ).comp (algebraMap D.host.F D.host.E) = Complex.ofRealHom.comp ι`. Break down `InfinitePlace.mk_eq_iff.1 hι with h1 | h1` into its components or cases.

Conclude with `h1`. Use extensionality with `a`. Use `congrArg (starRingEnd ℂ) (RingHom.congr_fun h1 a)` as an intermediate fact. Simplify using `using this`. Establish `hpos : 0 < tauE D τ (Formalism.UG.hform (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram x x)`.

Establish `hx' : (fun i => tauE D τ (x i)) ≠ 0` using `fun e => hx (funext fun i => (tauE D τ).injective (by`. Simplify using `using congrFun e i))`. Use `(Matrix.posDef_iff_dotProduct_mulVec.1 (h τ)).2 hx'` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Simplify using `only [Formalism.UG.hform, map_sum, map_mul, dotProduct, mulVec, Finset.mul_sum, gramAt, Pi.star_apply, Matrix.map_apply, mul_assoc]`.

Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← hτ]`. Both sides reduce to the same expression. Take `⟨a, ha⟩` from `(D.sp.cm.fixed (Formalism.UG.hform (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram x x)).1 (by`. Apply `(tauE D τ).injective` to reduce the goal to its premises.

Use `(hτ (tauE D τ) _).trans ?_` and prove the remaining obligations. Conclude with `Complex.conj_eq_iff_im.2 (Complex.pos_iff.1 hpos).2.symm)`. Use `⟨a, ha, ?_⟩` and prove the remaining obligations. Rewrite `hpos` using `[← ha]`. Establish `e : tauE D τ (algebraMap D.host.F D.host.E a) = (ι a : ℂ)` using `RingHom.congr_fun hι' a`.

Rewrite `hpos` using `[e]`. Conclude with `hpos` after adjusting the coercions.
-/
theorem isTotDef_of_posDef (V : HSp D) (h : ∀ τ, (gramAt D V τ).PosDef) : Formalism.UG.IsTotDef D.sp.cm.sig V.gram := by
  refine ⟨D.sp.cm.totReal, fun ι => Or.inl fun x hx => ?_⟩
  have hτ := (cmExt D).2.2.2
  obtain ⟨τ, hι⟩ := (GlobalTheory.CMTypePlaces.places_bijective D).2 (InfinitePlace.mk (Complex.ofRealHom.comp ι))
  have hι' : (tauE D τ).comp (algebraMap D.host.F D.host.E) = Complex.ofRealHom.comp ι := by
    rcases InfinitePlace.mk_eq_iff.1 hι with h1 | h1
    · exact h1
    · ext a
      have := congrArg (starRingEnd ℂ) (RingHom.congr_fun h1 a)
      simpa using this
  have hpos : 0 < tauE D τ (Formalism.UG.hform (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram x x) := by
    have hx' : (fun i => tauE D τ (x i)) ≠ 0 := fun e => hx (funext fun i => (tauE D τ).injective (by
      simpa using congrFun e i))
    have := (Matrix.posDef_iff_dotProduct_mulVec.1 (h τ)).2 hx'
    convert this using 1
    simp only [Formalism.UG.hform, map_sum, map_mul, dotProduct, mulVec, Finset.mul_sum, gramAt, Pi.star_apply,
      Matrix.map_apply, mul_assoc]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← hτ]; rfl
  obtain ⟨a, ha⟩ := (D.sp.cm.fixed (Formalism.UG.hform (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram x x)).1 (by
    apply (tauE D τ).injective
    refine (hτ (tauE D τ) _).trans ?_
    exact Complex.conj_eq_iff_im.2 (Complex.pos_iff.1 hpos).2.symm)
  refine ⟨a, ha, ?_⟩
  rw [← ha] at hpos
  have e : tauE D τ (algebraMap D.host.F D.host.E a) = (ι a : ℂ) := RingHom.congr_fun hι' a
  rw [e] at hpos
  exact_mod_cast hpos

/- English proof (translation)
Introduce `D V hV`. Take `⟨θ, hθ⟩` from `GlobalTheory.Member.exists_isInfFam_family D`. Use `haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩`. Use `haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _`. Use `haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _`.

Use `haveI : IsTopologicalGroup (GA D V) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))`. Use `haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField D.host.F`. Take `⟨π, hπ, -⟩` from `GlobalTheory.Mass.existsUnique_isFinProj D.sp.cm.sig V.gram`. Establish `hf : GlobalTheory.Mass.FiniteClasses (GQ V) ((GlobalTheory.Mass.stdLevel D.sp.cm.sig V.gram).comap π)`. Use `(GlobalTheory.Mass.finiteClasses_comap π (GlobalTheory.Mass.ratIn _ _ _) _ hπ.surjective hπ.injOn).2 ?_` and prove the remaining obligations.

Rewrite using `[hπ.map_ratIn]`. Conclude with `GlobalTheory.Mass.finiteClasses_unitary (cmExt D) (gram_hermND V) (isTotDef_of_posDef V hV) (GlobalTheory.Mass.isCompact_stdLevel _ _ (gram_hermND V).2) (GlobalTheory.Mass.isOpen_stdLevel _ _)`. Use `choose R hR using fun τ => exists_bound_unitary (hV τ)`. Take `⟨C, hC, hCe⟩` from `(GlobalTheory.Mass.intTens_open_compact D.host.F D.host.E).2`. Take `⟨C', hC', hCe'⟩` from `GlobalTheory.StabCompact.exists_compact_adele D θ hθ (∑ τ, |R τ|) C hC`.

Take `⟨K, hK, hKe⟩` from `GlobalTheory.StabCompact.exists_compact_of_entries (AF D.host.F) D.sp.cm.sig V.gram (gram_hermND V).2 C' hC'`. Establish `hsub : ∀ k : GA D V, π k ∈ GlobalTheory.Mass.stdLevel D.sp.cm.sig V.gram → k ∈ K`. Introduce `k hk`. Use `hKe k fun i j => hCe' _ (hCe _ ?_) fun τ => ?_` and prove the remaining obligations. Use `((GlobalTheory.Mass.mem_stdLevel _ _ _).1 hk i j).1` as an intermediate fact.

Rewrite `this` using `[hπ k]`. Then use the resulting hypothesis. Establish `hJ : (V.gram.map (incA D)).map ((θ τ).comp (infPart D)) = gramAt D V τ`. Use extensionality with `i j`. Conclude with `GlobalTheory.FockCompare.comp_incA hθ τ _`. Establish `hu : Formalism.UG.cT (cA D) (mt V k) * V.gram.map (incA D) * mt V k = V.gram.map (incA D)` using `k.2`.

Establish `e : (Formalism.UG.cT (cA D) (mt V k)).map ((θ τ).comp (infPart D)) = ((mt V k).map ((θ τ).comp (infPart D)))ᴴ`. Use extensionality with `i j`. Conclude with `GlobalTheory.FockCompare.comp_cA hθ τ _`. Use `congrArg (fun M => M.map ((θ τ).comp (infPart D))) hu` as an intermediate fact. Simplify using `only [Matrix.map_mul, e, hJ] at this`.

Conclude with `((hR τ _ this i j).trans (le_abs_self _)).trans (Finset.single_le_sum (f := fun τ => |R τ|) (fun _ _ => abs_nonneg _) (Finset.mem_univ τ))`. Use `haveI := hf.1`. Use `⟨⋃ c : Formalism.UG.ClassSet (GQ V) ((GlobalTheory.Mass.stdLevel D.sp.cm.sig V.gram).comap π), (fun k => c.out * k) '' K, isCompact_iUnion fun c => hK.image (continuous_const_mul _), fun h => ?_⟩` and prove the remaining obligations. Take `⟨γ, k, hγ, hk, e⟩` from `DoubleCoset.mk_out_eq_mul (GQ V) ((GlobalTheory.Mass.stdLevel D.sp.cm.sig V.gram).comap π) h`. Use `⟨γ⁻¹, inv_mem hγ, _, Set.mem_iUnion.2 ⟨DoubleCoset.mk _ _ h, k⁻¹, hsub _ (inv_mem hk), rfl⟩, ?_⟩` and prove the remaining obligations.

Simplify using `only [e]`. Use `group`.
-/
theorem exists_compact : ∀ {D : D7} (V : HSp D), (∀ τ, (gramAt D V τ).PosDef) →
    ∃ C : Set (GA D V), IsCompact C ∧ ∀ h : GA D V, ∃ γ ∈ GQ V, ∃ c ∈ C, h = γ * c := by
  intro D V hV
  obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  haveI : IsTopologicalGroup (GA D V) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField D.host.F
  obtain ⟨π, hπ, -⟩ := GlobalTheory.Mass.existsUnique_isFinProj D.sp.cm.sig V.gram
  have hf : GlobalTheory.Mass.FiniteClasses (GQ V) ((GlobalTheory.Mass.stdLevel D.sp.cm.sig V.gram).comap π) := by
    refine (GlobalTheory.Mass.finiteClasses_comap π (GlobalTheory.Mass.ratIn _ _ _) _ hπ.surjective hπ.injOn).2 ?_
    rw [hπ.map_ratIn]
    exact GlobalTheory.Mass.finiteClasses_unitary (cmExt D) (gram_hermND V) (isTotDef_of_posDef V hV)
      (GlobalTheory.Mass.isCompact_stdLevel _ _ (gram_hermND V).2) (GlobalTheory.Mass.isOpen_stdLevel _ _)
  choose R hR using fun τ => exists_bound_unitary (hV τ)
  obtain ⟨C, hC, hCe⟩ := (GlobalTheory.Mass.intTens_open_compact D.host.F D.host.E).2
  obtain ⟨C', hC', hCe'⟩ := GlobalTheory.StabCompact.exists_compact_adele D θ hθ (∑ τ, |R τ|) C hC
  obtain ⟨K, hK, hKe⟩ := GlobalTheory.StabCompact.exists_compact_of_entries (AF D.host.F) D.sp.cm.sig V.gram
    (gram_hermND V).2 C' hC'
  have hsub : ∀ k : GA D V, π k ∈ GlobalTheory.Mass.stdLevel D.sp.cm.sig V.gram → k ∈ K := by
    intro k hk
    refine hKe k fun i j => hCe' _ (hCe _ ?_) fun τ => ?_
    · have := ((GlobalTheory.Mass.mem_stdLevel _ _ _).1 hk i j).1
      rwa [hπ k] at this
    · have hJ : (V.gram.map (incA D)).map ((θ τ).comp (infPart D)) = gramAt D V τ := by
        ext i j; exact GlobalTheory.FockCompare.comp_incA hθ τ _
      have hu : Formalism.UG.cT (cA D) (mt V k) * V.gram.map (incA D) * mt V k = V.gram.map (incA D) := k.2
      have e : (Formalism.UG.cT (cA D) (mt V k)).map ((θ τ).comp (infPart D)) =
          ((mt V k).map ((θ τ).comp (infPart D)))ᴴ := by
        ext i j; exact GlobalTheory.FockCompare.comp_cA hθ τ _
      have := congrArg (fun M => M.map ((θ τ).comp (infPart D))) hu
      simp only [Matrix.map_mul, e, hJ] at this
      exact ((hR τ _ this i j).trans (le_abs_self _)).trans
        (Finset.single_le_sum (f := fun τ => |R τ|) (fun _ _ => abs_nonneg _) (Finset.mem_univ τ))
  haveI := hf.1
  refine ⟨⋃ c : Formalism.UG.ClassSet (GQ V) ((GlobalTheory.Mass.stdLevel D.sp.cm.sig V.gram).comap π),
    (fun k => c.out * k) '' K, isCompact_iUnion fun c => hK.image (continuous_const_mul _), fun h => ?_⟩
  obtain ⟨γ, k, hγ, hk, e⟩ := DoubleCoset.mk_out_eq_mul (GQ V) ((GlobalTheory.Mass.stdLevel D.sp.cm.sig V.gram).comap π) h
  refine ⟨γ⁻¹, inv_mem hγ, _, Set.mem_iUnion.2 ⟨DoubleCoset.mk _ _ h, k⁻¹, hsub _ (inv_mem hk), rfl⟩, ?_⟩
  simp only [e]
  group

open MeasureTheory in

/- English proof (translation)
Introduce `D ψ _ S T χS χT om hom hS X _ _ _ L hL F hF hinv μ 𝓕 hμ h𝓕 h`. Use `haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩`. Use `haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _`. Use `haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _`. Use `haveI : IsTopologicalGroup (GA D S) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig S.gram))`.

Use `haveI : BorelSpace (GA D S) := ⟨rfl⟩`. Use `haveI : Countable (GQ S) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma _ _`. Take `⟨C, hC, hcov⟩` from `exists_compact S hS`. Use `GlobalTheory.integrableOn_fundamentalDomain_of_cocompact (GA D S) (GQ S) C hC (fun g => ?_) μ hμ 𝓕 h𝓕 _ ?_ ?_` and prove the remaining obligations. Take `⟨γ, hγ, c, hc, rfl⟩` from `hcov g`.

Conclude with `⟨γ⁻¹, inv_mem hγ, by rwa [inv_mul_cancel_left]⟩`. Set `b` to `Module.finBasis ℂ X`. Establish `e : (fun g => thetaKO om g h (L (F g))) = fun g => ∑ k, b.coord k (F g) * om (g, h) (L (b k)) 0`. Use function extensionality and compare the values at `g`. Use `conv_lhs => rw [← b.sum_repr (F g)]`.

Simplify using `only [thetaKO, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Module.Basis.coord_apply]`. Rewrite using `[e]`. Use `continuous_finset_sum _ fun k _ => Continuous.mul ?_ ?_` and prove the remaining obligations. Conclude with `(b.coord k).continuous_of_finiteDimensional.comp hF`. Conclude with `(hom.om_cont _ (hL (b k)) 0).comp (continuous_id.prodMk continuous_const)`.

Introduce `γ hγ g`. Establish `e : (γ * g, h) = ((γ, 1) : GA D S × GA D T) * (g, h)` using `by rw [Prod.mk_mul_mk, one_mul]`. Simplify using `only [thetaKO]`. Rewrite using `[hinv γ hγ, e, map_mul]`. Conclude with `hom.om_aut γ hγ 1 (one_mem _) _ (hom.om_pres _ _ (hL _))`.
-/
theorem integrableOn_theta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D)
    (χS χT : (AE D)ˣ →* Circle) (om : (GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))),
    IsWeilDatumO ψ S T χS χT om → (∀ τ, (gramAt D S τ).PosDef) →
    ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [FiniteDimensional ℂ X] (L : X →ₗ[ℂ] (WO S T → ℂ)),
    (∀ x, IsThetaFunO ψ S T (L x)) → ∀ F : GA D S → X, Continuous F → (∀ γ ∈ GQ S, ∀ g, F (γ * g) = F g) →
    ∀ (μ : Measure (GA D S)) (𝓕 : Set (GA D S)), μ.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 μ →
    ∀ h, IntegrableOn (fun g => thetaKO om g h (L (F g))) 𝓕 μ := by
  intro D ψ _ S T χS χT om hom hS X _ _ _ L hL F hF hinv μ 𝓕 hμ h𝓕 h
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  haveI : IsTopologicalGroup (GA D S) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig S.gram))
  haveI : BorelSpace (GA D S) := ⟨rfl⟩
  haveI : Countable (GQ S) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma _ _
  obtain ⟨C, hC, hcov⟩ := exists_compact S hS
  refine GlobalTheory.integrableOn_fundamentalDomain_of_cocompact (GA D S) (GQ S) C hC (fun g => ?_) μ hμ 𝓕 h𝓕 _ ?_ ?_
  · obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov g
    exact ⟨γ⁻¹, inv_mem hγ, by rwa [inv_mul_cancel_left]⟩
  · let b := Module.finBasis ℂ X
    have e : (fun g => thetaKO om g h (L (F g))) =
        fun g => ∑ k, b.coord k (F g) * om (g, h) (L (b k)) 0 := by
      funext g
      conv_lhs => rw [← b.sum_repr (F g)]
      simp only [thetaKO, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Module.Basis.coord_apply]
    rw [e]
    refine continuous_finset_sum _ fun k _ => Continuous.mul ?_ ?_
    · exact (b.coord k).continuous_of_finiteDimensional.comp hF
    · exact (hom.om_cont _ (hL (b k)) 0).comp (continuous_id.prodMk continuous_const)
  · intro γ hγ g
    have e : (γ * g, h) = ((γ, 1) : GA D S × GA D T) * (g, h) := by rw [Prod.mk_mul_mk, one_mul]
    simp only [thetaKO]
    rw [hinv γ hγ, e, map_mul]
    exact hom.om_aut γ hγ 1 (one_mem _) _ (hom.om_pres _ _ (hL _))

end GlobalTheory.DefiniteQuotient
