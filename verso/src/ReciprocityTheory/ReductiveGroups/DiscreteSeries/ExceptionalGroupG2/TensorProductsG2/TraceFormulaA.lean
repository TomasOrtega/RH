import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.CoefEmbed
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.ClosGenStable
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.RigidityG2.ClosGenStable
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSchur
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.NormSubOneLeOfHsdA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.AnyDec
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.DataGenSubIrred
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.HasGelfandCharSigLam

noncomputable section

open Finset MeasureTheory Matrix

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

section ClRep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def tfClRep (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H) [S.HasOrthogonalProjection]
    (g : Matrix (Fin n) (Fin n) ℂ) : S →L[ℂ] S :=
  S.orthogonalProjectionOnto ∘L σ g ∘L S.subtypeL

/- English proof (translation)
Use `show ((S.orthogonalProjectionOnto (σ g (x : H)) : S) : H) = _`. Conclude with `congrArg Subtype.val (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (⟨_, hg _ x.2⟩ : S))`.
-/
theorem tfClRep_coe (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H) [S.HasOrthogonalProjection]
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : ∀ x ∈ S, σ g x ∈ S) (x : S) : ((tfClRep σ S g x : S) : H) = σ g x := by
  show ((S.orthogonalProjectionOnto (σ g (x : H)) : S) : H) = _
  exact congrArg Subtype.val (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (⟨_, hg _ x.2⟩ : S))

variable {ε : Fin n → Bool} {lam : Fin n → ℝ} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D} {V : Submodule ℂ D}

instance tfClGen_completeSpace (E : Fin n → Fin n → Module.End ℂ D) (V : Submodule ℂ D) :
    CompleteSpace (closGen E V) := by
  unfold closGen; infer_instance

/- English proof (translation)
Establish `hst` using `closGen_stable hgap hσ hD hV hc hVK`. Establish `h1 : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε` using `by show inUJ ε 1`. Simplify using `[inUJ]`. Use `⟨⟨?_, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Use `ContinuousLinearMap.ext fun x => Subtype.ext ?_` and prove the remaining obligations.

Rewrite using `[tfClRep_coe σ _ (hst 1 h1) x, hσ.1.1]`. Both sides reduce to the same expression. Introduce `a ha b hb`. Use `ContinuousLinearMap.ext fun x => Subtype.ext ?_` and prove the remaining obligations. Rewrite using `[ContinuousLinearMap.comp_apply, tfClRep_coe σ _ (hst _ (mul_mem_unitaryJ ha hb)) x, tfClRep_coe σ _ (hst a ha), tfClRep_coe σ _ (hst b hb), hσ.1.2 a ha b hb, ContinuousLinearMap.comp_apply]`.

Introduce `g hg x`. Establish `h` using `hσ.2.1 g hg (x : H)`. Rewrite `h` using `[← tfClRep_coe σ _ (hst g hg) x]`. Simplify using `using h`. Introduce `v`.

Conclude with `(closGen E V).orthogonalProjectionOnto.continuous.comp_continuousOn (hσ.2.2 (v : H))`.
-/
theorem tfClRep_isURepOn (hgap : StdGap ε lam) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) :
    IsURepOn (UJset ε) (tfClRep σ (closGen E V)) := by
  have hst := closGen_stable hgap hσ hD hV hc hVK
  have h1 : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε := by
    show inUJ ε 1
    simp [inUJ]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · refine ContinuousLinearMap.ext fun x => Subtype.ext ?_
    rw [tfClRep_coe σ _ (hst 1 h1) x, hσ.1.1]
    rfl
  · intro a ha b hb
    refine ContinuousLinearMap.ext fun x => Subtype.ext ?_
    rw [ContinuousLinearMap.comp_apply, tfClRep_coe σ _ (hst _ (mul_mem_unitaryJ ha hb)) x,
      tfClRep_coe σ _ (hst a ha), tfClRep_coe σ _ (hst b hb), hσ.1.2 a ha b hb, ContinuousLinearMap.comp_apply]
  · intro g hg x
    have h := hσ.2.1 g hg (x : H)
    rw [← tfClRep_coe σ _ (hst g hg) x] at h
    simpa using h
  · intro v
    exact (closGen E V).orthogonalProjectionOnto.continuous.comp_continuousOn (hσ.2.2 (v : H))

/- English proof (translation)
Establish `hst` using `closGen_stable hgap hσ hD hV hc hVK`. Introduce `S hSc hSG`. Establish `hinj : Function.Injective (closGen E V).subtype` using `Subtype.val_injective`. Establish `hcl : IsClosed ((S.map (closGen E V).subtype : Submodule ℂ H) : Set H)`. Establish `h` using `(Submodule.isClosed_topologicalClosure _).isClosedEmbedding_subtypeVal.isClosedMap (S : Set (closGen E V)) hSc`.

Rewrite using `[Submodule.map_coe]`. Conclude with `h`. Establish `hle : S.map (closGen E V).subtype ≤ closGen E V`. Introduce and unpack `_ ⟨x, -, rfl⟩`. Conclude with `x.2`.

Establish `hSt : ∀ g ∈ UJset ε, ∀ x ∈ S.map (closGen E V).subtype, σ g x ∈ S.map (closGen E V).subtype`. Introduce and unpack `g hg _ ⟨x, hx, rfl⟩`. Conclude with `⟨tfClRep σ (closGen E V) g x, hSG g (by rw [mir_UJset_eq]; exact hg) x hx, tfClRep_coe σ _ (hst g hg) x⟩`. Break down `rigid_irred hgap hσ hD hV hc hVK _ hle hcl hSt with h | h` into its components or cases. Use `left`.

Conclude with `Submodule.map_injective_of_injective hinj (h.trans (Submodule.map_bot _).symm)`. Use `right`. Apply `Submodule.map_injective_of_injective hinj` to reduce the goal to its premises. Rewrite using `[h, Submodule.map_top, Submodule.range_subtype]`.
-/
theorem tfClRep_irred (hgap : StdGap ε lam) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) :
    Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) (tfClRep σ (closGen E V)) := by
  have hst := closGen_stable hgap hσ hD hV hc hVK
  intro S hSc hSG
  have hinj : Function.Injective (closGen E V).subtype := Subtype.val_injective
  have hcl : IsClosed ((S.map (closGen E V).subtype : Submodule ℂ H) : Set H) := by
    have h := (Submodule.isClosed_topologicalClosure _).isClosedEmbedding_subtypeVal.isClosedMap
      (S : Set (closGen E V)) hSc
    rw [Submodule.map_coe]
    exact h
  have hle : S.map (closGen E V).subtype ≤ closGen E V := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hSt : ∀ g ∈ UJset ε, ∀ x ∈ S.map (closGen E V).subtype, σ g x ∈ S.map (closGen E V).subtype := by
    rintro g hg _ ⟨x, hx, rfl⟩
    exact ⟨tfClRep σ (closGen E V) g x, hSG g (by rw [mir_UJset_eq]; exact hg) x hx, tfClRep_coe σ _ (hst g hg) x⟩
  rcases rigid_irred hgap hσ hD hV hc hVK _ hle hcl hSt with h | h
  · left
    exact Submodule.map_injective_of_injective hinj (h.trans (Submodule.map_bot _).symm)
  · right
    apply Submodule.map_injective_of_injective hinj
    rw [h, Submodule.map_top, Submodule.range_subtype]

/- English proof (translation)
Take `⟨w, hwV, hw0, -⟩` from `hV.2.2.2`. Establish `hw : ((w : D) : H) ∈ closGen E V` using `Submodule.le_topologicalClosure _ ⟨w, rorth_le_genSub hwV, rfl⟩`. Use `⟨⟨⟨_, hw⟩, 0, fun h => hw0 ?_⟩⟩` and prove the remaining obligations. Establish `h2 : ((w : D) : H) = 0` using `congrArg Subtype.val h`. Conclude with `Subtype.ext h2`.
-/
theorem tfClRep_nontrivial (hV : IsKIrrHW ε E (lowK ε lam) V) : Nontrivial (closGen E V) := by
  obtain ⟨w, hwV, hw0, -⟩ := hV.2.2.2
  have hw : ((w : D) : H) ∈ closGen E V :=
    Submodule.le_topologicalClosure _ ⟨w, rorth_le_genSub hwV, rfl⟩
  refine ⟨⟨⟨_, hw⟩, 0, fun h => hw0 ?_⟩⟩
  have h2 : ((w : D) : H) = 0 := congrArg Subtype.val h
  exact Subtype.ext h2

/- English proof (translation)
Establish `hU` using `tfClRep_isURepOn hgap hσ hD hV hc hVK`. Establish `hU' : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) (tfClRep σ (closGen E V))`. Rewrite using `[mir_UJset_eq]`. Conclude with `hU`. Conclude with `Formalism.MainNotions.BridgeCSchur.schur_UJ _ (tfClRep_nontrivial hV) hU' (tfClRep_irred hgap hσ hD hV hc hVK) hSq`.
-/
theorem tfClRep_fdeg (hgap : StdGap ε lam) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (hSq : Formalism.MainNotions.S.IsSqIntOn ε (tfClRep σ (closGen E V))) :
    ∃ d : ℝ, Formalism.MainNotions.S.IsFdeg (Formalism.REAL.muG ε) (tfClRep σ (closGen E V)) d := by
  have hU := tfClRep_isURepOn hgap hσ hD hV hc hVK
  have hU' : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) (tfClRep σ (closGen E V)) := by
    rw [mir_UJset_eq]; exact hU
  exact Formalism.MainNotions.BridgeCSchur.schur_UJ _ (tfClRep_nontrivial hV) hU' (tfClRep_irred hgap hσ hD hV hc hVK) hSq

/- English proof (translation)
Establish `hst` using `closGen_stable hgap hσ hD hV hc hVK`. Take `⟨-, h⟩` from `hd`. Take `⟨h1, h2⟩` from `h ⟨v, hv⟩ ⟨u, hu⟩ ⟨v', hv'⟩ ⟨u', hu'⟩`. Establish `e : ∀ (x y : closGen E V) (g : Formalism.REAL.UJ ε), Formalism.MainNotions.S.coefOn (tfClRep σ (closGen E V)) x y g = inner ℂ (y : H) (σ (Formalism.MainNotions.S.umat g) x)`. Introduce `x y g`.

Simplify using `only [Formalism.MainNotions.S.coefOn]`. Rewrite using `[Submodule.coe_inner, tfClRep_coe σ _ (hst _ (umat_mem_UJset ε g))]`. Simplify using `only [e] at h1 h2`. Use `⟨h1, ?_⟩` and prove the remaining obligations. Rewrite using `[h2, Submodule.coe_inner, Submodule.coe_inner]`.
-/
theorem tfClRep_schur (hgap : StdGap ε lam) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) {d : ℝ}
    (hd : Formalism.MainNotions.S.IsFdeg (Formalism.REAL.muG ε) (tfClRep σ (closGen E V)) d)
    {u v u' v' : H} (hu : u ∈ closGen E V) (hv : v ∈ closGen E V) (hu' : u' ∈ closGen E V) (hv' : v' ∈ closGen E V) :
    Integrable (fun g : Formalism.REAL.UJ ε => inner ℂ u (σ (Formalism.MainNotions.S.umat g) v) * star (inner ℂ u' (σ (Formalism.MainNotions.S.umat g) v')))
      (Formalism.REAL.muG ε) ∧
    ∫ g, inner ℂ u (σ (Formalism.MainNotions.S.umat g) v) * star (inner ℂ u' (σ (Formalism.MainNotions.S.umat g) v')) ∂(Formalism.REAL.muG ε) =
      inner ℂ v' v * inner ℂ u u' / (d : ℂ) := by
  have hst := closGen_stable hgap hσ hD hV hc hVK
  obtain ⟨-, h⟩ := hd
  obtain ⟨h1, h2⟩ := h ⟨v, hv⟩ ⟨u, hu⟩ ⟨v', hv'⟩ ⟨u', hu'⟩
  have e : ∀ (x y : closGen E V) (g : Formalism.REAL.UJ ε),
      Formalism.MainNotions.S.coefOn (tfClRep σ (closGen E V)) x y g = inner ℂ (y : H) (σ (Formalism.MainNotions.S.umat g) x) := by
    intro x y g
    simp only [Formalism.MainNotions.S.coefOn]
    rw [Submodule.coe_inner, tfClRep_coe σ _ (hst _ (umat_mem_UJset ε g))]
  simp only [e] at h1 h2
  refine ⟨h1, ?_⟩
  rw [h2, Submodule.coe_inner, Submodule.coe_inner]

end ClRep

section Form

def tfSgn (ε : Fin n → Bool) (c : Fin n) : ℂ := if ε c then 1 else -1

/- English proof (translation)
Apply the tactic sequence `unfold tfSgn; split_ifs <;> norm_num`.
-/
theorem tfSgn_mul_self (ε : Fin n → Bool) (c : Fin n) : tfSgn ε c * tfSgn ε c = 1 := by
  unfold tfSgn; split_ifs <;> norm_num

/- English proof (translation)
Apply the tactic sequence `unfold tfSgn; split_ifs <;> simp`.
-/
theorem tf_star_sgn (ε : Fin n → Bool) (c : Fin n) : star (tfSgn ε c) = tfSgn ε c := by
  unfold tfSgn; split_ifs <;> simp

/- English proof (translation)
Unfold `Jm tfSgn`. Rewrite using `[Matrix.diagonal_apply]`.
-/
theorem tf_Jm_apply (ε : Fin n → Bool) (a b : Fin n) : Jm ε a b = if a = b then tfSgn ε a else 0 := by
  unfold Jm tfSgn
  rw [Matrix.diagonal_apply]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def tfFormBH (ε : Fin n → Bool) (f g : Fin n → H) : ℂ := ∑ c, tfSgn ε c * inner ℂ (f c) (g c)

/- English proof (translation)
Unfold `tfFormBH`. Rewrite using `[sum_eq_single c]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[hb]`.

Simplify using the standard rewrite rules.
-/
theorem tfFormBH_single_left (ε : Fin n → Bool) (c : Fin n) (y : H) (g : Fin n → H) :
    tfFormBH ε (Pi.single c y) g = tfSgn ε c * inner ℂ y (g c) := by
  unfold tfFormBH
  rw [sum_eq_single c]
  · simp
  · intro b _ hb; simp [hb]
  · simp

def tfCoef (dual : Bool) (g : Matrix (Fin n) (Fin n) ℂ) (c d : Fin n) : ℂ := cond dual ((g⁻¹) d c) (g c d)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem tf_tensGrp_apply (dual : Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (g : Matrix (Fin n) (Fin n) ℂ)
    (f : Fin n → H) (c : Fin n) : tensGrp dual σ g f c = ∑ d, tfCoef dual g c d • σ g (f d) := rfl

/- English proof (translation)
Apply `Matrix.inv_eq_left_inv` to reduce the goal to its premises. Establish `h : gᴴ * Jm ε * g = Jm ε` using `hg`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem tf_inv_Jm {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) :
    g⁻¹ = Jm ε * gᴴ * Jm ε := by
  apply Matrix.inv_eq_left_inv
  have h : gᴴ * Jm ε * g = Jm ε := hg
  calc Jm ε * gᴴ * Jm ε * g = Jm ε * (gᴴ * Jm ε * g) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h, Jm_mul_Jm]

/- English proof (translation)
Establish `h : gᴴ * Jm ε * g = Jm ε` using `hg`. Rewrite using `[tf_inv_Jm hg, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Jm_conjTranspose, Matrix.conjTranspose_conjTranspose]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = Jm ε := by simp only [Jm_mul_Jm, Matrix.mul_one, h, Matrix.one_mul]`.
-/
theorem tf_inv_mul_Jm_mul {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) :
    g⁻¹ * Jm ε * (g⁻¹)ᴴ = Jm ε := by
  have h : gᴴ * Jm ε * g = Jm ε := hg
  rw [tf_inv_Jm hg, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Jm_conjTranspose,
    Matrix.conjTranspose_conjTranspose]
  calc Jm ε * gᴴ * Jm ε * Jm ε * (Jm ε * (g * Jm ε)) = Jm ε * (gᴴ * (Jm ε * Jm ε) * Jm ε * g) * Jm ε := by
        simp only [Matrix.mul_assoc]
    _ = Jm ε := by simp only [Jm_mul_Jm, Matrix.mul_one, h, Matrix.one_mul]

/- English proof (translation)
Consider the cases of `dual`. Establish `h : (gᴴ * Jm ε * g) d d' = Jm ε d d'` using `by rw [show gᴴ * Jm ε * g = Jm ε from hg]`. Rewrite `h` using `[tf_Jm_apply, Matrix.mul_apply]`. Rewrite using `[← h]`. Use `sum_congr rfl fun c _ => ?_` and prove the remaining obligations.

Rewrite using `[Matrix.mul_apply, sum_eq_single c]`. Simplify using `only [tfCoef, cond_false, Matrix.conjTranspose_apply, tf_Jm_apply, if_true]`. Expand and normalize the polynomial expressions, which then agree. Introduce `b _ hb`. Rewrite using `[tf_Jm_apply, if_neg hb, mul_zero]`.

Simplify using the standard rewrite rules. Establish `h : (g⁻¹ * Jm ε * (g⁻¹)ᴴ) d' d = Jm ε d' d` using `by rw [tf_inv_mul_Jm_mul hg]`. Rewrite `h` using `[tf_Jm_apply, Matrix.mul_apply]`. Establish `e : (if d = d' then tfSgn ε d else 0) = if d' = d then tfSgn ε d' else 0`. Distinguish the cases in `hdd : d = d'`.

Substitute `hdd` using the available equality. Both sides reduce to the same expression. Rewrite using `[if_neg hdd, if_neg (Ne.symm hdd)]`. Rewrite using `[e, ← h]`. Use `sum_congr rfl fun c _ => ?_` and prove the remaining obligations.

Rewrite using `[Matrix.mul_apply, sum_eq_single c]`. Simplify using `only [tfCoef, cond_true, Matrix.conjTranspose_apply, tf_Jm_apply, if_true]`. Expand and normalize the polynomial expressions, which then agree. Introduce `b _ hb`. Rewrite using `[tf_Jm_apply, if_neg hb, mul_zero]`.

Simplify using the standard rewrite rules.
-/
theorem tfCoef_orth (dual : Bool) {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε)
    (d d' : Fin n) :
    ∑ c, tfSgn ε c * star (tfCoef dual g c d) * tfCoef dual g c d' = if d = d' then tfSgn ε d else 0 := by
  cases dual
  · have h : (gᴴ * Jm ε * g) d d' = Jm ε d d' := by rw [show gᴴ * Jm ε * g = Jm ε from hg]
    rw [tf_Jm_apply, Matrix.mul_apply] at h
    rw [← h]
    refine sum_congr rfl fun c _ => ?_
    rw [Matrix.mul_apply, sum_eq_single c]
    · simp only [tfCoef, cond_false, Matrix.conjTranspose_apply, tf_Jm_apply, if_true]; ring
    · intro b _ hb; rw [tf_Jm_apply, if_neg hb, mul_zero]
    · simp
  · have h : (g⁻¹ * Jm ε * (g⁻¹)ᴴ) d' d = Jm ε d' d := by rw [tf_inv_mul_Jm_mul hg]
    rw [tf_Jm_apply, Matrix.mul_apply] at h
    have e : (if d = d' then tfSgn ε d else 0) = if d' = d then tfSgn ε d' else 0 := by
      by_cases hdd : d = d'
      · subst hdd; rfl
      · rw [if_neg hdd, if_neg (Ne.symm hdd)]
    rw [e, ← h]
    refine sum_congr rfl fun c _ => ?_
    rw [Matrix.mul_apply, sum_eq_single c]
    · simp only [tfCoef, cond_true, Matrix.conjTranspose_apply, tf_Jm_apply, if_true]; ring
    · intro b _ hb; rw [tf_Jm_apply, if_neg hb, mul_zero]
    · simp

/- English proof (translation)
Establish `h1 : ∀ c, s c * star (∑ d, t c d * u d) * (∑ d, t c d * u' d) = ∑ d, ∑ d', (s c * star (t c d) * t c d') * (star (u d) * u' d')`. Introduce `c`. Rewrite using `[star_sum, mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]`. Use `sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`.

Use `sum_congr rfl fun d' _ => ?_` and prove the remaining obligations. Rewrite using `[star_mul']`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[sum_congr rfl (fun c _ => h1 c), sum_comm]`. Use `sum_congr rfl fun d _ => ?_` and prove the remaining obligations.

Rewrite using `[sum_comm]`. Repeatedly rewrite using `[← Finset.sum_mul, ht]`. Rewrite using `[sum_eq_single d]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.

Introduce `b _ hb`. Simplify using `[Ne.symm hb]`. Simplify using the standard rewrite rules.
-/
theorem tf_jquad (t : Fin n → Fin n → ℂ) (s : Fin n → ℂ)
    (ht : ∀ d d', ∑ c, s c * star (t c d) * t c d' = if d = d' then s d else 0) (u u' : Fin n → ℂ) :
    ∑ c, s c * star (∑ d, t c d * u d) * (∑ d, t c d * u' d) = ∑ d, s d * star (u d) * u' d := by
  have h1 : ∀ c, s c * star (∑ d, t c d * u d) * (∑ d, t c d * u' d) =
      ∑ d, ∑ d', (s c * star (t c d) * t c d') * (star (u d) * u' d') := by
    intro c
    rw [star_sum, mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
    refine sum_congr rfl fun d _ => ?_
    rw [Finset.mul_sum]
    refine sum_congr rfl fun d' _ => ?_
    rw [star_mul']; ring
  rw [sum_congr rfl (fun c _ => h1 c), sum_comm]
  refine sum_congr rfl fun d _ => ?_
  rw [sum_comm]
  simp_rw [← Finset.sum_mul, ht]
  rw [sum_eq_single d]
  · simp; ring
  · intro b _ hb; simp [Ne.symm hb]
  · simp

/- English proof (translation)
Use function extensionality and compare the values at `c`. Simplify using `only [tf_tensGrp_apply, map_sum, map_smul, Finset.smul_sum, smul_smul]`. Rewrite using `[sum_comm]`. Use `sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_smul, hσ.1.2 g hg h hh, ContinuousLinearMap.comp_apply]`.

Use `congr 1`. Consider the cases of `dual`. Simplify using `[tfCoef, Matrix.mul_apply]`. Simplify using `only [tfCoef, cond_true, Matrix.mul_inv_rev, Matrix.mul_apply]`. Conclude with `sum_congr rfl fun e _ => mul_comm _ _`.
-/
theorem tf_tensGrp_mul (dual : Bool) {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsURepOn (UJset ε) σ) {g h : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) (hh : h ∈ UJset ε)
    (f : Fin n → H) : tensGrp dual σ (g * h) f = tensGrp dual σ g (tensGrp dual σ h f) := by
  funext c
  simp only [tf_tensGrp_apply, map_sum, map_smul, Finset.smul_sum, smul_smul]
  rw [sum_comm]
  refine sum_congr rfl fun d _ => ?_
  rw [← Finset.sum_smul, hσ.1.2 g hg h hh, ContinuousLinearMap.comp_apply]
  congr 1
  cases dual
  · simp [tfCoef, Matrix.mul_apply]
  · simp only [tfCoef, cond_true, Matrix.mul_inv_rev, Matrix.mul_apply]
    exact sum_congr rfl fun e _ => mul_comm _ _

end Form

end ReciprocityTheory.ChartRestriction.DS.G2
