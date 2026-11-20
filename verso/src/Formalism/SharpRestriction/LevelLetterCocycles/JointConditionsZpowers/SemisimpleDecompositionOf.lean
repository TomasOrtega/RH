import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.BaseLin
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.GaloisConditionFiveExtraOf
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CoefficientCompatibilityOf
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ResidualIrreducibleOfTheorem

noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

open NumberField IsDedekindDomain

/- English proof (translation)
Use `isClosed_eq ?_ ?_` and prove the remaining obligations. Conclude with `(continuous_const.sub hM).matrix_det`. Conclude with `(continuous_const.sub hN).matrix_det.mul (continuous_finset_prod _ fun j _ => continuous_const.sub (hχ j))`.
-/
theorem isClosed_det_eq {Γ A : Type} [TopologicalSpace Γ] [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [T2Space A] {n r : ℕ} {ι : Type} (s : Finset ι) (M : Γ → Matrix (Fin n) (Fin n) A)
    (N' : Γ → Matrix (Fin r) (Fin r) A) (χ : ι → Γ → A) (hM : Continuous M) (hN : Continuous N')
    (hχ : ∀ j, Continuous (χ j)) (c : A) :
    IsClosed {g | (Matrix.scalar (Fin n) c - M g).det =
      (Matrix.scalar (Fin r) c - N' g).det * ∏ j ∈ s, (c - χ j g)} := by
  refine isClosed_eq ?_ ?_
  · exact (continuous_const.sub hM).matrix_det
  · exact (continuous_const.sub hN).matrix_det.mul
      (continuous_finset_prod _ fun j _ => continuous_const.sub (hχ j))

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `haveI : Finite (D.nd.O i) := not_infinite_iff_finite.mp h`. Establish `hf : IsField (D.nd.O i)` using `Finite.isField_of_domain (D.nd.O i)`. Conclude with `IsDiscreteValuationRing.not_a_field' ((IsLocalRing.isField_iff_maximalIdeal_eq).mp hf)`.
-/
theorem infinite_O (D : D7) (i : D.nd.Loc) : Infinite (D.nd.O i) := by
  by_contra h
  haveI : Finite (D.nd.O i) := not_infinite_iff_finite.mp h
  have hf : IsField (D.nd.O i) := Finite.isField_of_domain (D.nd.O i)
  exact IsDiscreteValuationRing.not_a_field' ((IsLocalRing.isField_iff_maximalIdeal_eq).mp hf)

/- English proof (translation)
Unfold `Formalism.MainNotions.SumRepresentations.adm5 Formalism.MainNotions.SumRepresentations.At.JacquetShalikaStrongMultOne at hAN`. Establish `hCheb` using `hAN.2.2.1`. Take `⟨hrc, -, hrF⟩` from `hr x`. Take `⟨hρc, -, hρF⟩` from `hρ`. Establish `hP : (placesOver D.host.E (D.nd.l i)).Finite`.

Establish `hne : Ideal.span {((D.nd.l i : ℕ) : 𝓞 D.host.E)} ≠ 0`. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `Nat.cast_ne_zero.mpr (D.nd.lPrime i).out.ne_zero`. Use `(Ideal.finite_factors hne).subset ?_` and prove the remaining obligations. Introduce `v hv`.

Conclude with `Ideal.dvd_span_singleton.mpr hv`. Use `set Sg : Set (PlE D.host) := placesOver D.host.E (D.nd.l i) ∪ (↑(D.nd.S i) : Set (PlE D.host)) ∪ (↑(D.nd.Q i) : Set (PlE D.host)) with hSg_def`. Establish `hSg : Sg.Finite` using `(hP.union (D.nd.S i).finite_toSet).union (D.nd.Q i).finite_toSet`. Use `set Fr : Set (GE D.nd) := {σ | ∃ w ∉ Sg, IsSplitPl D.host w ∧ ∃ B : ValuationSubring D.nd.Om, IsPlaceOver (F := D.host.E) B w ∧ IsFrob (F := D.host.E) B (normV w) σ} with hFr_def`. Establish `hden : closure Fr = Set.univ` using `hCheb Sg hSg`.

Establish `hg : g ∈ closure Fr` using `by rw [hden]; exact Set.mem_univ g`. Use `haveI := infinite_O D i`. Use `Polynomial.eq_of_infinite_eval_eq _ _ ?_` and prove the remaining obligations. Use `Set.Infinite.mono ?_ Set.infinite_univ` and prove the remaining obligations. Introduce `c _`.

Simplify using `only [Set.mem_setOf_eq]`. Use `haveI : T2Space (D.nd.O i) := by`. Establish `hA` using `isAdic_iff.mp (D.nd.O_adic i)`. Use `IsTopologicalAddGroup.t2Space_of_zero_sep ?_` and prove the remaining obligations. Introduce `y hy`.

Choose the witnesses or unpack the hypotheses as in `⟨n, hn⟩ : ∃ n, y ∉ (IsLocalRing.maximalIdeal (D.nd.O i)) ^ n := by`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Apply `hy` to reduce the goal to its premises. Use `(D.nd.O_complete i).toIsHausdorff.haus y fun n => ?_` and prove the remaining obligations.

Rewrite using `[SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top]`. Conclude with `hcon n`. Conclude with `⟨_, (hA.1 n).mem_nhds (Ideal.zero_mem _), hn⟩`. Establish `hcl` using `isClosed_det_eq (Finset.Icc 1 D.R.t) (fun g => ((r x g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i))) (fun g => ((ρ' g : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i))) (fun k g => ((D.nd.chi i k g : (D.nd.O i)ˣ) : D.nd.O i)) hrc hρc (fun k => D.nd.chi_cont i k) …`. Establish `hmain` using `(hcl.closure_subset_iff.mpr ?_) hg`.

Simplify using `only [Set.mem_setOf_eq] at hmain`. Rewrite using `[Polynomial.eval_mul, Polynomial.eval_prod, Matrix.eval_charpoly, Matrix.eval_charpoly]`. Simplify `hmain` using `only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]`. Introduce and unpack `σ ⟨w, hw, hs, B, hB, hFb⟩`. Establish `hso : SplitOut D.nd i w` using `⟨hs, fun h => hw (Or.inl (Or.inl h)), fun h => hw (Or.inl (Or.inr h)), fun h => hw (Or.inr h)⟩`.

Establish `e3` using `congrArg (Polynomial.eval c) ((hrF w hso B σ hB hFb).trans (hρF w hso B σ hB hFb).symm)`. Rewrite `e3` using `[Polynomial.eval_mul, Polynomial.eval_prod, Matrix.eval_charpoly, Matrix.eval_charpoly]`. Simplify using `only [Set.mem_setOf_eq]`. Simplify `e3` using `only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]`.
-/
theorem charpoly_of_isRhoOf (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (x : D.nd.X i) (ρ' : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)) (hAN : Formalism.MainNotions.SumRepresentations.adm5 D) (hr : GoodR D.nd i r)
    (hρ : IsRhoOf D.nd i x ρ') (g : GE D.nd) :
    ((r x g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)).charpoly =
      ((ρ' g : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).charpoly *
        ∏ c ∈ Finset.Icc 1 D.R.t, (X - C ((D.nd.chi i c g : (D.nd.O i)ˣ) : D.nd.O i)) := by
  unfold Formalism.MainNotions.SumRepresentations.adm5 Formalism.MainNotions.SumRepresentations.At.JacquetShalikaStrongMultOne at hAN
  have hCheb := hAN.2.2.1
  obtain ⟨hrc, -, hrF⟩ := hr x
  obtain ⟨hρc, -, hρF⟩ := hρ
  have hP : (placesOver D.host.E (D.nd.l i)).Finite := by
    have hne : Ideal.span {((D.nd.l i : ℕ) : 𝓞 D.host.E)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact Nat.cast_ne_zero.mpr (D.nd.lPrime i).out.ne_zero
    refine (Ideal.finite_factors hne).subset ?_
    intro v hv
    exact Ideal.dvd_span_singleton.mpr hv
  set Sg : Set (PlE D.host) := placesOver D.host.E (D.nd.l i) ∪ (↑(D.nd.S i) : Set (PlE D.host)) ∪
    (↑(D.nd.Q i) : Set (PlE D.host)) with hSg_def
  have hSg : Sg.Finite := (hP.union (D.nd.S i).finite_toSet).union (D.nd.Q i).finite_toSet
  set Fr : Set (GE D.nd) := {σ | ∃ w ∉ Sg, IsSplitPl D.host w ∧ ∃ B : ValuationSubring D.nd.Om,
    IsPlaceOver (F := D.host.E) B w ∧ IsFrob (F := D.host.E) B (normV w) σ} with hFr_def
  have hden : closure Fr = Set.univ := hCheb Sg hSg
  have hg : g ∈ closure Fr := by rw [hden]; exact Set.mem_univ g
  haveI := infinite_O D i
  refine Polynomial.eq_of_infinite_eval_eq _ _ ?_
  refine Set.Infinite.mono ?_ Set.infinite_univ
  intro c _
  simp only [Set.mem_setOf_eq]
  haveI : T2Space (D.nd.O i) := by
    have hA := isAdic_iff.mp (D.nd.O_adic i)
    refine IsTopologicalAddGroup.t2Space_of_zero_sep ?_
    intro y hy
    obtain ⟨n, hn⟩ : ∃ n, y ∉ (IsLocalRing.maximalIdeal (D.nd.O i)) ^ n := by
      by_contra hcon
      push_neg at hcon
      apply hy
      refine (D.nd.O_complete i).toIsHausdorff.haus y fun n => ?_
      rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top]
      exact hcon n
    exact ⟨_, (hA.1 n).mem_nhds (Ideal.zero_mem _), hn⟩
  have hcl := isClosed_det_eq (Finset.Icc 1 D.R.t)
    (fun g => ((r x g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)))
    (fun g => ((ρ' g : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)))
    (fun k g => ((D.nd.chi i k g : (D.nd.O i)ˣ) : D.nd.O i)) hrc hρc (fun k => D.nd.chi_cont i k) c
  have hmain := (hcl.closure_subset_iff.mpr ?_) hg
  · simp only [Set.mem_setOf_eq] at hmain
    rw [Polynomial.eval_mul, Polynomial.eval_prod, Matrix.eval_charpoly, Matrix.eval_charpoly]
    simpa only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] using hmain
  · rintro σ ⟨w, hw, hs, B, hB, hFb⟩
    have hso : SplitOut D.nd i w :=
      ⟨hs, fun h => hw (Or.inl (Or.inl h)), fun h => hw (Or.inl (Or.inr h)), fun h => hw (Or.inr h)⟩
    have e3 := congrArg (Polynomial.eval c) ((hrF w hso B σ hB hFb).trans (hρF w hso B σ hB hFb).symm)
    rw [Polynomial.eval_mul, Polynomial.eval_prod, Matrix.eval_charpoly, Matrix.eval_charpoly] at e3
    simp only [Set.mem_setOf_eq]
    simpa only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] using e3

def rhoChiK (D : D7) (i : D.nd.Loc) (ρ' : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)) :
    GE D.nd →* GL (Fin (D.R.r + D.R.t)) (KK D.nd i) :=
  blockRep (mapRep (algebraMap (D.nd.O i) (KK D.nd i)) ρ')
    (diagGL fun c : Fin D.R.t => (Units.map (algebraMap (D.nd.O i) (KK D.nd i)).toMonoidHom).comp
      (D.nd.chi i ((c : ℕ) + 1)))

/- English proof (translation)
Establish `hcp : ∀ g, ((r π g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)).charpoly = ((ρ π g : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).charpoly * ∏ c ∈ Finset.Icc 1 D.R.t, (X - C ((D.nd.chi i c g : (D.nd.O i)ˣ) : D.nd.O i))` using `fun g => charpoly_of_isRhoOf D i r π (ρ π) hAN hr hρ g`. Unfold `Formalism.MainNotions.SumRepresentations.adm5 Formalism.MainNotions.SumRepresentations.At.JacquetShalikaStrongMultOne at hAN`. Establish `hBN` using `hAN.2.2.2`. Take `⟨-, hSS1, -⟩` from `hr π`. Establish `hblk : ∀ g, ((rhoChiK D i (ρ π) g : GL _ _) : Matrix (Fin (D.R.r + D.R.t)) (Fin (D.R.r + D.R.t)) (KK D.nd i)) = blockHom (KK D.nd i) D.R.r D.R.t ((toK D.nd i).mapMatrix ((ρ π g : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)), Matrix.diagonal fun c : Fin D.R.t => toK D.nd i …` using `fun g => rfl`.

Establish `hdiag : ∀ d : Fin D.R.t → KK D.nd i, (Matrix.diagonal d).charpoly = ∏ c, (X - C (d c))`. Introduce `d`. Use `first`. Consider the case `exact Matrix.charpoly_diagonal d`. Consider the case `(unfold Matrix.charpoly`.

Rewrite using `[show Matrix.charmatrix (Matrix.diagonal d) = Matrix.diagonal fun c => X - C (d c) from by`. Use extensionality with `a b`. Apply the tactic sequence `by_cases h : a = b <;> simp [Matrix.charmatrix_apply, Matrix.diagonal_apply, h]]`. Conclude with `Matrix.det_diagonal)`. Take `⟨Pm, hPm⟩` from `hBN (KK D.nd i) (D.R.r + D.R.t) (mapRep (toK D.nd i) (r π)) (rhoChiK D i (ρ π)) hSS1 hSS (by`.

Introduce `g`. Use `show ((toK D.nd i).mapMatrix ((r π g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i))).charpoly = (blockHom (KK D.nd i) D.R.r D.R.t ((toK D.nd i).mapMatrix ((ρ π g : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)), Matrix.diagonal fun c : Fin D.R.t => toK D.nd i ((D. …`. Rewrite using `[blockHom_charpoly, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.charpoly_map, Matrix.charpoly_map, hcp g, Polynomial.map_mul, Polynomial.map_prod, hdiag]`. Use `congr 1`. Simplify using `only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]`.

Rewrite using `[Fin.prod_univ_eq_prod_range (fun c => X - C (toK D.nd i ((D.nd.chi i (c + 1) g : (D.nd.O i)ˣ) : D.nd.O i))) D.R.t, Finset.range_eq_Ico, Finset.prod_Ico_add' (fun c => X - C (toK D.nd i ((D.nd.chi i c g : (D.nd.O i)ˣ) : D.nd.O i))), zero_add]`. Use `congr 1)`. Set `e0 : (Fin (D.R.r + D.R.t) → KK D.nd i) ≃ₗ[KK D.nd i] (Fin (D.R.r + D.R.t) → KK D.nd i)` to `LinearEquiv.ofLinear (Matrix.toLin' ((Pm⁻¹ : GL (Fin (D.R.r + D.R.t)) (KK D.nd i)) : Matrix (Fin (D.R.r + D.R.t)) (Fin (D.R.r + D.R.t)) (KK D.nd i))) (Matrix.toLin' ((Pm : GL (Fin (D.R.r + D.R.t)) (KK D.nd i)) : Matrix (Fin (D.R.r + D.R.t)) (Fin (D.R.r + D.R.t)) (KK D.nd i))) (by …`. Use `⟨e0.trans (splitRT (KK D.nd i) D.R.r D.R.t), ?_⟩` and prove the remaining obligations. Introduce `g u`.

Establish `hm'` using `congrArg Units.val (hPm g)`. Rewrite `hm'` using `[Units.val_mul, Units.val_mul]`. Establish `hv : ((Pm⁻¹ : GL (Fin (D.R.r + D.R.t)) (KK D.nd i)) : Matrix (Fin (D.R.r + D.R.t)) (Fin (D.R.r + D.R.t)) (KK D.nd i)).mulVec ((mapM (toK D.nd i) (rO D.nd i r π) g : Matrix (Fin (D.R.r + D.R.t)) (Fin (D.R.r + D.R.t)) (KK D.nd i)).mulVec u) = ((rhoChiK D i (ρ π) g : GL (Fin (D.R.r …`. Establish `key : ∀ (A P Q : Matrix (Fin (D.R.r + D.R.t)) (Fin (D.R.r + D.R.t)) (KK D.nd i)) (v : Fin (D.R.r + D.R.t) → KK D.nd i), P * Q = 1 → (Q * A * P).mulVec (Q.mulVec v) = Q.mulVec (A.mulVec v)`. Introduce `A P Q v hPQ`.

Rewrite using `[Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]`. Simplify using `only [mul_assoc, hPQ, mul_one]`. Rewrite using `[hm']`. Conclude with `(key _ _ _ u (Units.mul_inv Pm)).symm`. Use `show splitRT (KK D.nd i) D.R.r D.R.t (((Pm⁻¹ : GL (Fin (D.R.r + D.R.t)) (KK D.nd i)) : Matrix (Fin (D.R.r + D.R.t)) (Fin (D.R.r + D.R.t)) (KK D.nd i)).mulVec ((mapM (toK D.nd i) (rO D.nd i r π) g : Matrix (Fin (D.R.r + D.R.t)) (Fin (D.R.r + D.R.t)) (KK D.nd i)).mulVec u)) = _`.

Rewrite using `[hv, hblk, blockHom_mulVec]`. Use `Prod.ext rfl ?_` and prove the remaining obligations. Use function extensionality and compare the values at `c`. Simplify using `only [Matrix.mulVec_diagonal]`. Both sides reduce to the same expression.
-/
theorem semisimple_decomposition_of (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (hAN : Formalism.MainNotions.SumRepresentations.adm5 D) (hr : GoodR D.nd i r) (hρ : IsRhoOf D.nd i π (ρ π))
    (hSS : IsSSRep (rhoChiK D i (ρ π))) : Formalism.MainNotions.TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π := by
  have hcp : ∀ g, ((r π g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)).charpoly =
      ((ρ π g : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).charpoly *
        ∏ c ∈ Finset.Icc 1 D.R.t, (X - C ((D.nd.chi i c g : (D.nd.O i)ˣ) : D.nd.O i)) :=
    fun g => charpoly_of_isRhoOf D i r π (ρ π) hAN hr hρ g
  unfold Formalism.MainNotions.SumRepresentations.adm5 Formalism.MainNotions.SumRepresentations.At.JacquetShalikaStrongMultOne at hAN
  have hBN := hAN.2.2.2
  obtain ⟨-, hSS1, -⟩ := hr π
  have hblk : ∀ g, ((rhoChiK D i (ρ π) g : GL _ _) : Matrix (Fin (D.R.r + D.R.t)) (Fin (D.R.r + D.R.t)) (KK D.nd i)) =
      blockHom (KK D.nd i) D.R.r D.R.t
        ((toK D.nd i).mapMatrix ((ρ π g : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)),
         Matrix.diagonal fun c : Fin D.R.t =>
           toK D.nd i ((D.nd.chi i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i)) := fun g => rfl
  have hdiag : ∀ d : Fin D.R.t → KK D.nd i, (Matrix.diagonal d).charpoly = ∏ c, (X - C (d c)) := by
    intro d
    first
    | exact Matrix.charpoly_diagonal d
    | (unfold Matrix.charpoly
       rw [show Matrix.charmatrix (Matrix.diagonal d) = Matrix.diagonal fun c => X - C (d c) from by
         ext a b
         by_cases h : a = b <;> simp [Matrix.charmatrix_apply, Matrix.diagonal_apply, h]]
       exact Matrix.det_diagonal)
  obtain ⟨Pm, hPm⟩ := hBN (KK D.nd i) (D.R.r + D.R.t) (mapRep (toK D.nd i) (r π)) (rhoChiK D i (ρ π))
    hSS1 hSS (by
      intro g
      show ((toK D.nd i).mapMatrix ((r π g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i))).charpoly =
        (blockHom (KK D.nd i) D.R.r D.R.t
          ((toK D.nd i).mapMatrix ((ρ π g : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)),
           Matrix.diagonal fun c : Fin D.R.t =>
             toK D.nd i ((D.nd.chi i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i))).charpoly
      rw [blockHom_charpoly, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.charpoly_map,
        Matrix.charpoly_map, hcp g, Polynomial.map_mul, Polynomial.map_prod, hdiag]
      congr 1
      simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
      rw [Fin.prod_univ_eq_prod_range
          (fun c => X - C (toK D.nd i ((D.nd.chi i (c + 1) g : (D.nd.O i)ˣ) : D.nd.O i))) D.R.t,
        Finset.range_eq_Ico,
        Finset.prod_Ico_add' (fun c => X - C (toK D.nd i ((D.nd.chi i c g : (D.nd.O i)ˣ) : D.nd.O i))),
        zero_add]
      congr 1)
  let e0 : (Fin (D.R.r + D.R.t) → KK D.nd i) ≃ₗ[KK D.nd i] (Fin (D.R.r + D.R.t) → KK D.nd i) :=
    LinearEquiv.ofLinear (Matrix.toLin' ((Pm⁻¹ : GL (Fin (D.R.r + D.R.t)) (KK D.nd i)) : Matrix (Fin (D.R.r + D.R.t)) (Fin (D.R.r + D.R.t)) (KK D.nd i)))
      (Matrix.toLin' ((Pm : GL (Fin (D.R.r + D.R.t)) (KK D.nd i)) : Matrix (Fin (D.R.r + D.R.t)) (Fin (D.R.r + D.R.t)) (KK D.nd i)))
      (by rw [← Matrix.toLin'_mul, Units.inv_mul, Matrix.toLin'_one])
      (by rw [← Matrix.toLin'_mul, Units.mul_inv, Matrix.toLin'_one])
  refine ⟨e0.trans (splitRT (KK D.nd i) D.R.r D.R.t), ?_⟩
  intro g u
  have hm' := congrArg Units.val (hPm g)
  rw [Units.val_mul, Units.val_mul] at hm'
  have hv : ((Pm⁻¹ : GL (Fin (D.R.r + D.R.t)) (KK D.nd i)) : Matrix (Fin (D.R.r + D.R.t)) (Fin (D.R.r + D.R.t)) (KK D.nd i)).mulVec ((mapM (toK D.nd i) (rO D.nd i r π) g : Matrix (Fin (D.R.r + D.R.t)) (Fin (D.R.r + D.R.t)) (KK D.nd i)).mulVec u) =
      ((rhoChiK D i (ρ π) g : GL (Fin (D.R.r + D.R.t)) (KK D.nd i)) : Matrix (Fin (D.R.r + D.R.t)) (Fin (D.R.r + D.R.t)) (KK D.nd i)).mulVec (((Pm⁻¹ : GL (Fin (D.R.r + D.R.t)) (KK D.nd i)) : Matrix (Fin (D.R.r + D.R.t)) (Fin (D.R.r + D.R.t)) (KK D.nd i)).mulVec u) := by
    have key : ∀ (A P Q : Matrix (Fin (D.R.r + D.R.t)) (Fin (D.R.r + D.R.t)) (KK D.nd i)) (v : Fin (D.R.r + D.R.t) → KK D.nd i), P * Q = 1 →
        (Q * A * P).mulVec (Q.mulVec v) = Q.mulVec (A.mulVec v) := by
      intro A P Q v hPQ
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      simp only [mul_assoc, hPQ, mul_one]
    rw [hm']
    exact (key _ _ _ u (Units.mul_inv Pm)).symm
  show splitRT (KK D.nd i) D.R.r D.R.t (((Pm⁻¹ : GL (Fin (D.R.r + D.R.t)) (KK D.nd i)) : Matrix (Fin (D.R.r + D.R.t)) (Fin (D.R.r + D.R.t)) (KK D.nd i)).mulVec
      ((mapM (toK D.nd i) (rO D.nd i r π) g : Matrix (Fin (D.R.r + D.R.t)) (Fin (D.R.r + D.R.t)) (KK D.nd i)).mulVec u)) = _
  rw [hv, hblk, blockHom_mulVec]
  refine Prod.ext rfl ?_
  funext c
  simp only [Matrix.mulVec_diagonal]
  rfl

end Formalism.MainNotions.N
