import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuationTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupExpTwoSidedInverseUniqueStatement

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.FGDepth

noncomputable section

variable {C : Type} [Field C]

/- English proof (translation)
Establish `hc : ∀ s, constantCoeff (Function.extend j (X : τ → MvPowerSeries τ C) 0 s) = 0`. Introduce `s`. Rewrite using `[Function.extend_def]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `ha` using `hasSubst_of_constantCoeff_zero hc`.

Rewrite using `[coeff_subst ha, finsum_eq_single _ (Finsupp.mapDomain j α)]`. Rewrite using `[Finsupp.prod_mapDomain_index_inj hj]`. Simplify using `only [hj.extend_apply]`. Rewrite using `[← MvPowerSeries.monomial_one_eq, coeff_monomial_same, smul_eq_mul, mul_one]`. Introduce `D hD`.

Distinguish the cases in `hsupp : ↑D.support ⊆ Set.range j`. Take `⟨β, rfl⟩ : ∃ β, Finsupp.mapDomain j β = D` from `⟨_, Finsupp.mapDomain_comapDomain j hj D hsupp⟩`. Rewrite using `[Finsupp.prod_mapDomain_index_inj hj]`. Simplify using `only [hj.extend_apply]`. Rewrite using `[← MvPowerSeries.monomial_one_eq, coeff_monomial_ne, smul_zero]`.

Introduce and unpack `rfl`. Conclude with `hD rfl`. Take `⟨s, hs, hsr⟩` from `Set.not_subset.mp hsupp`. Establish `hz : Function.extend j (X : τ → MvPowerSeries τ C) 0 s = 0` using `Function.extend_apply' _ _ _ (fun h => hsr h)`. Establish `hs' : D s ≠ 0` using `Finsupp.mem_support_iff.mp hs`.

Rewrite using `[Finsupp.prod, Finset.prod_eq_zero hs (by simp [hz, hs']), map_zero, smul_zero]`.
-/
theorem coeff_subst_extend_zero {σ τ : Type} [Finite σ] {j : τ → σ} (hj : Function.Injective j)
    (g : MvPowerSeries σ C) (α : τ →₀ ℕ) :
    coeff α (subst (Function.extend j (X : τ → MvPowerSeries τ C) 0) g) =
      coeff (Finsupp.mapDomain j α) g := by
  classical
  have hc : ∀ s, constantCoeff (Function.extend j (X : τ → MvPowerSeries τ C) 0 s) = 0 := by
    intro s
    rw [Function.extend_def]
    split_ifs <;> simp
  have ha := hasSubst_of_constantCoeff_zero hc
  rw [coeff_subst ha, finsum_eq_single _ (Finsupp.mapDomain j α)]
  · rw [Finsupp.prod_mapDomain_index_inj hj]
    simp only [hj.extend_apply]
    rw [← MvPowerSeries.monomial_one_eq, coeff_monomial_same, smul_eq_mul, mul_one]
  · intro D hD
    by_cases hsupp : ↑D.support ⊆ Set.range j
    · obtain ⟨β, rfl⟩ : ∃ β, Finsupp.mapDomain j β = D :=
        ⟨_, Finsupp.mapDomain_comapDomain j hj D hsupp⟩
      rw [Finsupp.prod_mapDomain_index_inj hj]
      simp only [hj.extend_apply]
      rw [← MvPowerSeries.monomial_one_eq, coeff_monomial_ne, smul_zero]
      rintro rfl
      exact hD rfl
    · obtain ⟨s, hs, hsr⟩ := Set.not_subset.mp hsupp
      have hz : Function.extend j (X : τ → MvPowerSeries τ C) 0 s = 0 :=
        Function.extend_apply' _ _ _ (fun h => hsr h)
      have hs' : D s ≠ 0 := Finsupp.mem_support_iff.mp hs
      rw [Finsupp.prod, Finset.prod_eq_zero hs (by simp [hz, hs']), map_zero, smul_zero]

/- English proof (translation)
Conclude with `subst_zero_of_constantCoeff_zero h0`.
-/
theorem subst_zero_of_constantCoeff {σ τ : Type} [Finite σ] (h : MvPowerSeries σ C)
    (h0 : constantCoeff h = 0) : subst (0 : σ → MvPowerSeries τ C) h = 0 := by
  exact subst_zero_of_constantCoeff_zero h0

/- English proof (translation)
Rewrite using `[← coe_substAlgHom hs, map_sum]`. Simplify using `only [map_smul, substAlgHom_X]`.
-/
theorem subst_sum_smul_X {σ τ ι : Type} [Fintype ι] {s : σ → MvPowerSeries τ C} (hs : HasSubst s)
    (c : ι → C) (k : ι → σ) :
    subst s (∑ a, c a • (X (k a) : MvPowerSeries σ C)) = ∑ a, c a • s (k a) := by
  rw [← coe_substAlgHom hs, map_sum]
  simp only [map_smul, substAlgHom_X]

end

end GlobalTheory.FGDepth

namespace GlobalTheory.FGDepth

noncomputable section

variable {C : Type} [Field C] [CharZero C] {v : AddValuation C (WithTop ℝ)}

/- English proof (translation)
Establish `hE` using `(GlobalTheory.T.formalGroupExp_twoSided_inverse_unique C v (d x.1) (G x.1)).1`. Unfold `IsExp at hE`. Simplify using `only [expAlong]`. Use `constantCoeff_subst_eq_zero ?_ ?_ (hE.1 x.2)` and prove the remaining obligations. Conclude with `hasSubst_of_constantCoeff_zero (fun e => by simp [MvPowerSeries.smul_eq_C_mul])`.

Introduce `e`. Simplify using `[MvPowerSeries.smul_eq_C_mul]`.
-/
theorem constantCoeff_expAlong {κ : Type} {d : κ → ℕ} (G : ∀ b, LogFGL v (d b)) {ι : κ → Type}
    [∀ b, Fintype (ι b)] (u : ∀ b, ι b → Fin (d b) → C) (x : Σ b, Fin (d b)) :
    constantCoeff (expAlong G u x) = 0 := by
  have hE := (GlobalTheory.T.formalGroupExp_twoSided_inverse_unique C v (d x.1) (G x.1)).1
  unfold IsExp at hE
  simp only [expAlong]
  refine constantCoeff_subst_eq_zero ?_ ?_ (hE.1 x.2)
  · exact hasSubst_of_constantCoeff_zero (fun e => by simp [MvPowerSeries.smul_eq_C_mul])
  · intro e
    simp [MvPowerSeries.smul_eq_C_mul]

/- English proof (translation)
Establish `hinj : ∀ (β : κ → Type), Function.Injective (fun x : (Σ b : κ', β (e b)) => (⟨e x.1, x.2⟩ : Σ b, β b))`. Introduce `β`. Introduce and unpack `⟨a, x⟩ ⟨c, y⟩ h`. Simplify using `only [Sigma.mk.inj_iff] at h`. Take `⟨h1, h2⟩` from `h`.

Take `rfl` from `e.injective h1`. Rewrite `h2` using `[heq_eq_eq]`. Rewrite using `[h2]`. Establish `hjt : Function.Injective (fun x : (Σ b : κ', ι (e b)) => (⟨e x.1, x.2⟩ : Σ b, ι b))` using `hinj ι`. Establish `hjv : Function.Injective (fun x : (Σ b : κ', Fin (d (e b))) => (⟨e x.1, x.2⟩ : Σ b, Fin (d b)))` using `hinj (fun b => Fin (d b))`.

Establish `hcc : ∀ {σ τ : Type} (j : τ → σ) (s : σ), constantCoeff (Function.extend j (X : τ → MvPowerSeries τ C) 0 s) = 0`. Introduce `σ τ j s`. Rewrite using `[Function.extend_def]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `hE : ∀ b (k : Fin (d b)), constantCoeff (expOf (G b) k) = 0`.

Introduce `b k`. Establish `h` using `(GlobalTheory.T.formalGroupExp_twoSided_inverse_unique C v (d b) (G b)).1`. Unfold `IsExp at h`. Conclude with `h.1 k`. Establish `hA : HasSubst (expAlong G u)` using `hasSubst_of_constantCoeff_zero (constantCoeff_expAlong G u)`.

Establish `hA' : HasSubst (expAlong (fun b => G (e b)) (fun b => u (e b)))` using `hasSubst_of_constantCoeff_zero (constantCoeff_expAlong _ _)`. Establish `hRt : HasSubst (Function.extend (fun x : (Σ b : κ', ι (e b)) => (⟨e x.1, x.2⟩ : Σ b, ι b)) (X : (Σ b : κ', ι (e b)) → MvPowerSeries (Σ b : κ', ι (e b)) C) 0)` using `hasSubst_of_constantCoeff_zero (hcc _)`. Establish `hRv : HasSubst (Function.extend (fun x : (Σ b : κ', Fin (d (e b))) => (⟨e x.1, x.2⟩ : Σ b, Fin (d b))) (X : (Σ b : κ', Fin (d (e b))) → MvPowerSeries (Σ b : κ', Fin (d (e b))) C) 0)` using `hasSubst_of_constantCoeff_zero (hcc _)`. Establish `hin : ∀ b, HasSubst (fun e' : Fin (d b) => ∑ a, u b a e' • (X ⟨b, a⟩ : MvPowerSeries (Σ b, ι b) C))` using `fun b => hasSubst_of_constantCoeff_zero (fun e' => by simp [MvPowerSeries.smul_eq_C_mul])`. Establish `K1 : ∀ F : MvPowerSeries (Σ b, ι b) C, derivAt0 (MvPolynomial.rename (fun x : (Σ b : κ', ι (e b)) => (⟨e x.1, x.2⟩ : Σ b, ι b)) P) F = derivAt0 P (subst (Function.extend (fun x : (Σ b : κ', ι (e b)) => (⟨e x.1, x.2⟩ : Σ b, ι b)) (X : (Σ b : κ', ι (e b)) → MvPowerSeries (Σ b : κ', …`.

Introduce `F`. Unfold `derivAt0`. Rewrite using `[MvPolynomial.support_rename_of_injective hjt, Finset.sum_image (Finsupp.mapDomain_injective hjt).injOn]`. Use `Finset.sum_congr rfl fun α _ => ?_` and prove the remaining obligations. Establish `hm : (mfact (Finsupp.mapDomain (fun x : (Σ b : κ', ι (e b)) => (⟨e x.1, x.2⟩ : Σ b, ι b)) α) : C) = mfact α`.

Unfold `mfact`. Conclude with `Finsupp.prod_mapDomain_index_inj hjt`. Rewrite using `[MvPolynomial.coeff_rename_mapDomain _ hjt, coeff_subst_extend_zero hjt, hm]`. Establish `K2 : ∀ x : Σ b, Fin (d b),`. Substitute `(Function.extend (fun x : (Σ b : κ', ι (e b)) => (⟨e x.1, x.2⟩ : Σ b, ι b)) (X : (Σ b : κ', ι (e b)) → MvPowerSeries (Σ b : κ', ι (e b)) C) 0) (expAlong G u x) =` using the available equality.

Substitute `(expAlong (fun b => G (e b)) (fun b => u (e b))) (Function.extend (fun x : (Σ b : κ', Fin (d (e b))) => (⟨e x.1, x.2⟩ : Σ b, Fin (d b))) (X : (Σ b : κ', Fin (d (e b))) → MvPowerSeries (Σ b : κ', Fin (d (e b))) C) 0 x) := by` using the available equality. Introduce and unpack `⟨b, k⟩`. Distinguish the cases in `hb : ∃ b', e b' = b`. Take `⟨b', rfl⟩` from `hb`. Establish `h1 : Function.extend (fun x : (Σ b : κ', Fin (d (e b))) => (⟨e x.1, x.2⟩ : Σ b, Fin (d b))) (X : (Σ b : κ', Fin (d (e b))) → MvPowerSeries (Σ b : κ', Fin (d (e b))) C) 0 ⟨e b', k⟩ = X ⟨b', k⟩` using `hjv.extend_apply _ _ ⟨b', k⟩`.

Establish `h2 : ∀ a, Function.extend (fun x : (Σ b : κ', ι (e b)) => (⟨e x.1, x.2⟩ : Σ b, ι b)) (X : (Σ b : κ', ι (e b)) → MvPowerSeries (Σ b : κ', ι (e b)) C) 0 ⟨e b', a⟩ = X ⟨b', a⟩` using `fun a => hjt.extend_apply _ _ ⟨b', a⟩`. Rewrite using `[h1, subst_X hA']`. Simplify using `only [expAlong]`. Rewrite using `[subst_comp_subst_apply (hin (e b')) hRt]`. Use `congr 1`.

Use function extensionality and compare the values at `e'`. Rewrite using `[subst_sum_smul_X hRt]`. Simplify using `only [h2]`. Establish `h1 : Function.extend (fun x : (Σ b : κ', Fin (d (e b))) => (⟨e x.1, x.2⟩ : Σ b, Fin (d b))) (X : (Σ b : κ', Fin (d (e b))) → MvPowerSeries (Σ b : κ', Fin (d (e b))) C) 0 ⟨b, k⟩ = 0` using `Function.extend_apply' _ _ _ (by`. Introduce and unpack `⟨⟨b', k'⟩, h⟩`.

Conclude with `hb ⟨b', congrArg Sigma.fst h⟩)`. Establish `h2 : ∀ a, Function.extend (fun x : (Σ b : κ', ι (e b)) => (⟨e x.1, x.2⟩ : Σ b, ι b)) (X : (Σ b : κ', ι (e b)) → MvPowerSeries (Σ b : κ', ι (e b)) C) 0 ⟨b, a⟩ = 0` using `fun a => Function.extend_apply' _ _ _ (by`. Introduce and unpack `⟨⟨b', a'⟩, h⟩`. Conclude with `hb ⟨b', congrArg Sigma.fst h⟩)`. Rewrite using `[h1, ← coe_substAlgHom hA', map_zero]`.

Simplify using `only [expAlong]`. Rewrite using `[subst_comp_subst_apply (hin b) hRt]`. Establish `h3 : (fun e' : Fin (d b) => subst (Function.extend (fun x : (Σ b : κ', ι (e b)) => (⟨e x.1, x.2⟩ : Σ b, ι b)) (X : (Σ b : κ', ι (e b)) → MvPowerSeries (Σ b : κ', ι (e b)) C) 0) (∑ a, u b a e' • (X ⟨b, a⟩ : MvPowerSeries (Σ b, ι b) C))) = 0`. Use function extensionality and compare the values at `e'`. Rewrite using `[subst_sum_smul_X hRt]`.

Simplify using `[h2]`. Rewrite using `[h3]`. Conclude with `subst_zero_of_constantCoeff _ (hE b k)`. Establish `K : ∀ f : MvPowerSeries (Σ b, Fin (d b)) C, derivAt0 (MvPolynomial.rename (fun x : (Σ b : κ', ι (e b)) => (⟨e x.1, x.2⟩ : Σ b, ι b)) P) (subst (expAlong G u) f) = derivAt0 P (subst (expAlong (fun b => G (e b)) (fun b => u (e b))) (subst (Function.extend (fun x : (Σ b : κ', Fin (d …`. Introduce `f`.

Rewrite using `[K1, subst_comp_subst_apply hA hRt, subst_comp_subst_apply hRv hA']`. Conclude with `congrArg (fun F => derivAt0 P (subst F f)) (funext K2)`. Establish `Rint : ∀ f : MvPowerSeries (Σ b, Fin (d b)) C, MvIsInt v f → MvIsInt v (subst (Function.extend (fun x : (Σ b : κ', Fin (d (e b))) => (⟨e x.1, x.2⟩ : Σ b, Fin (d b))) (X : (Σ b : κ', Fin (d (e b))) → MvPowerSeries (Σ b : κ', Fin (d (e b))) C) 0) f)`. Introduce `f hf α`. Rewrite using `[coeff_subst_extend_zero hjv]`.

Conclude with `hf _`. Establish `Rsec : ∀ g : MvPowerSeries (Σ b : κ', Fin (d (e b))) C, MvIsInt v g → ∃ f, MvIsInt v f ∧ subst (Function.extend (fun x : (Σ b : κ', Fin (d (e b))) => (⟨e x.1, x.2⟩ : Σ b, Fin (d b))) (X : (Σ b : κ', Fin (d (e b))) → MvPowerSeries (Σ b : κ', Fin (d (e b))) C) 0) f = g`. Introduce `g hg`. Use `⟨@id (MvPowerSeries (Σ b, Fin (d b)) C) (Function.extend (Finsupp.mapDomain (fun x : (Σ b : κ', Fin (d (e b))) => (⟨e x.1, x.2⟩ : Σ b, Fin (d b)))) (fun α => coeff α g) 0), ?_, ?_⟩` and prove the remaining obligations. Introduce `β show IsIntV v (Function.extend (Finsupp.mapDomain (fun x : (Σ b : κ', Fin (d (e b))) => (⟨e x.1, x.2⟩ : Σ b, Fin (d b)))) (fun α => coeff α g) 0 β)`.

Rewrite using `[Function.extend_def]`. Use `split_ifs with h`. Conclude with `hg _`. Simplify using `[IsIntV]`. Use extensionality with `α`.

Rewrite using `[coeff_subst_extend_zero hjv]`. Conclude with `(Finsupp.mapDomain_injective hjv).extend_apply _ _ α`. Unfold `depth`. Apply `le_antisymm` to reduce the goal to its premises. Use `le_iInf fun g => ?_` and prove the remaining obligations.

Take `⟨f, hf, hfg⟩` from `Rsec g.1 g.2`. Use `(iInf_le _ ⟨f, hf⟩).trans_eq ?_` and prove the remaining obligations. Simplify using `only`. Rewrite using `[K f, hfg]`. Use `le_iInf fun f => ?_` and prove the remaining obligations.

Use `(iInf_le _ ⟨subst (Function.extend (fun x : (Σ b : κ', Fin (d (e b))) => (⟨e x.1, x.2⟩ : Σ b, Fin (d b))) (X : (Σ b : κ', Fin (d (e b))) → MvPowerSeries (Σ b : κ', Fin (d (e b))) C) 0) f.1, Rint f.1 f.2⟩).trans_eq ?_` and prove the remaining obligations. Simplify using `only`. Rewrite using `[K f.1]`.
-/
theorem depth_rename (κ : Type) [Fintype κ] [DecidableEq κ] (d : κ → ℕ)
    (G : ∀ b, LogFGL v (d b)) (ι : κ → Type) [∀ b, Fintype (ι b)] [∀ b, DecidableEq (ι b)]
    (u : ∀ b, ι b → Fin (d b) → C) (κ' : Type) [Fintype κ'] [DecidableEq κ'] (e : κ' ↪ κ)
    (P : MvPolynomial (Σ b : κ', ι (e b)) C) :
    depth G u (MvPolynomial.rename (fun x => (⟨e x.1, x.2⟩ : Σ b, ι b)) P) =
      depth (fun b => G (e b)) (fun b => u (e b)) P := by
  have hinj : ∀ (β : κ → Type),
      Function.Injective (fun x : (Σ b : κ', β (e b)) => (⟨e x.1, x.2⟩ : Σ b, β b)) := by
    intro β
    rintro ⟨a, x⟩ ⟨c, y⟩ h
    simp only [Sigma.mk.inj_iff] at h
    obtain ⟨h1, h2⟩ := h
    obtain rfl := e.injective h1
    rw [heq_eq_eq] at h2
    rw [h2]
  have hjt : Function.Injective (fun x : (Σ b : κ', ι (e b)) => (⟨e x.1, x.2⟩ : Σ b, ι b)) := hinj ι
  have hjv : Function.Injective (fun x : (Σ b : κ', Fin (d (e b))) => (⟨e x.1, x.2⟩ : Σ b, Fin (d b))) := hinj (fun b => Fin (d b))
  have hcc : ∀ {σ τ : Type} (j : τ → σ) (s : σ),
      constantCoeff (Function.extend j (X : τ → MvPowerSeries τ C) 0 s) = 0 := by
    intro σ τ j s
    classical
    rw [Function.extend_def]
    split_ifs <;> simp
  have hE : ∀ b (k : Fin (d b)), constantCoeff (expOf (G b) k) = 0 := by
    intro b k
    have h := (GlobalTheory.T.formalGroupExp_twoSided_inverse_unique C v (d b) (G b)).1
    unfold IsExp at h
    exact h.1 k
  have hA : HasSubst (expAlong G u) := hasSubst_of_constantCoeff_zero (constantCoeff_expAlong G u)
  have hA' : HasSubst (expAlong (fun b => G (e b)) (fun b => u (e b))) :=
    hasSubst_of_constantCoeff_zero (constantCoeff_expAlong _ _)
  have hRt : HasSubst (Function.extend (fun x : (Σ b : κ', ι (e b)) => (⟨e x.1, x.2⟩ : Σ b, ι b)) (X : (Σ b : κ', ι (e b)) → MvPowerSeries (Σ b : κ', ι (e b)) C) 0) :=
    hasSubst_of_constantCoeff_zero (hcc _)
  have hRv : HasSubst (Function.extend (fun x : (Σ b : κ', Fin (d (e b))) => (⟨e x.1, x.2⟩ : Σ b, Fin (d b))) (X : (Σ b : κ', Fin (d (e b))) → MvPowerSeries (Σ b : κ', Fin (d (e b))) C) 0) :=
    hasSubst_of_constantCoeff_zero (hcc _)
  have hin : ∀ b, HasSubst (fun e' : Fin (d b) =>
      ∑ a, u b a e' • (X ⟨b, a⟩ : MvPowerSeries (Σ b, ι b) C)) := fun b =>
    hasSubst_of_constantCoeff_zero (fun e' => by simp [MvPowerSeries.smul_eq_C_mul])

  have K1 : ∀ F : MvPowerSeries (Σ b, ι b) C,
      derivAt0 (MvPolynomial.rename (fun x : (Σ b : κ', ι (e b)) => (⟨e x.1, x.2⟩ : Σ b, ι b)) P) F =
        derivAt0 P (subst (Function.extend (fun x : (Σ b : κ', ι (e b)) => (⟨e x.1, x.2⟩ : Σ b, ι b)) (X : (Σ b : κ', ι (e b)) → MvPowerSeries (Σ b : κ', ι (e b)) C) 0) F) := by
    intro F
    unfold derivAt0
    rw [MvPolynomial.support_rename_of_injective hjt,
      Finset.sum_image (Finsupp.mapDomain_injective hjt).injOn]
    refine Finset.sum_congr rfl fun α _ => ?_
    have hm : (mfact (Finsupp.mapDomain (fun x : (Σ b : κ', ι (e b)) => (⟨e x.1, x.2⟩ : Σ b, ι b)) α) : C) = mfact α := by
      unfold mfact
      exact Finsupp.prod_mapDomain_index_inj hjt
    rw [MvPolynomial.coeff_rename_mapDomain _ hjt, coeff_subst_extend_zero hjt, hm]

  have K2 : ∀ x : Σ b, Fin (d b),
      subst (Function.extend (fun x : (Σ b : κ', ι (e b)) => (⟨e x.1, x.2⟩ : Σ b, ι b)) (X : (Σ b : κ', ι (e b)) → MvPowerSeries (Σ b : κ', ι (e b)) C) 0) (expAlong G u x) =
        subst (expAlong (fun b => G (e b)) (fun b => u (e b))) (Function.extend (fun x : (Σ b : κ', Fin (d (e b))) => (⟨e x.1, x.2⟩ : Σ b, Fin (d b))) (X : (Σ b : κ', Fin (d (e b))) → MvPowerSeries (Σ b : κ', Fin (d (e b))) C) 0 x) := by
    rintro ⟨b, k⟩
    by_cases hb : ∃ b', e b' = b
    · obtain ⟨b', rfl⟩ := hb
      have h1 : Function.extend (fun x : (Σ b : κ', Fin (d (e b))) => (⟨e x.1, x.2⟩ : Σ b, Fin (d b))) (X : (Σ b : κ', Fin (d (e b))) → MvPowerSeries (Σ b : κ', Fin (d (e b))) C) 0 ⟨e b', k⟩ = X ⟨b', k⟩ := hjv.extend_apply _ _ ⟨b', k⟩
      have h2 : ∀ a, Function.extend (fun x : (Σ b : κ', ι (e b)) => (⟨e x.1, x.2⟩ : Σ b, ι b)) (X : (Σ b : κ', ι (e b)) → MvPowerSeries (Σ b : κ', ι (e b)) C) 0 ⟨e b', a⟩ = X ⟨b', a⟩ :=
        fun a => hjt.extend_apply _ _ ⟨b', a⟩
      rw [h1, subst_X hA']
      simp only [expAlong]
      rw [subst_comp_subst_apply (hin (e b')) hRt]
      congr 1
      funext e'
      rw [subst_sum_smul_X hRt]
      simp only [h2]
    · have h1 : Function.extend (fun x : (Σ b : κ', Fin (d (e b))) => (⟨e x.1, x.2⟩ : Σ b, Fin (d b))) (X : (Σ b : κ', Fin (d (e b))) → MvPowerSeries (Σ b : κ', Fin (d (e b))) C) 0 ⟨b, k⟩ = 0 :=
        Function.extend_apply' _ _ _ (by
          rintro ⟨⟨b', k'⟩, h⟩
          exact hb ⟨b', congrArg Sigma.fst h⟩)
      have h2 : ∀ a, Function.extend (fun x : (Σ b : κ', ι (e b)) => (⟨e x.1, x.2⟩ : Σ b, ι b)) (X : (Σ b : κ', ι (e b)) → MvPowerSeries (Σ b : κ', ι (e b)) C) 0 ⟨b, a⟩ = 0 := fun a =>
        Function.extend_apply' _ _ _ (by
          rintro ⟨⟨b', a'⟩, h⟩
          exact hb ⟨b', congrArg Sigma.fst h⟩)
      rw [h1, ← coe_substAlgHom hA', map_zero]
      simp only [expAlong]
      rw [subst_comp_subst_apply (hin b) hRt]
      have h3 : (fun e' : Fin (d b) => subst (Function.extend (fun x : (Σ b : κ', ι (e b)) => (⟨e x.1, x.2⟩ : Σ b, ι b)) (X : (Σ b : κ', ι (e b)) → MvPowerSeries (Σ b : κ', ι (e b)) C) 0)
          (∑ a, u b a e' • (X ⟨b, a⟩ : MvPowerSeries (Σ b, ι b) C))) = 0 := by
        funext e'
        rw [subst_sum_smul_X hRt]
        simp [h2]
      rw [h3]
      exact subst_zero_of_constantCoeff _ (hE b k)
  have K : ∀ f : MvPowerSeries (Σ b, Fin (d b)) C,
      derivAt0 (MvPolynomial.rename (fun x : (Σ b : κ', ι (e b)) => (⟨e x.1, x.2⟩ : Σ b, ι b)) P) (subst (expAlong G u) f) =
        derivAt0 P (subst (expAlong (fun b => G (e b)) (fun b => u (e b))) (subst (Function.extend (fun x : (Σ b : κ', Fin (d (e b))) => (⟨e x.1, x.2⟩ : Σ b, Fin (d b))) (X : (Σ b : κ', Fin (d (e b))) → MvPowerSeries (Σ b : κ', Fin (d (e b))) C) 0) f)) := by
    intro f
    rw [K1, subst_comp_subst_apply hA hRt, subst_comp_subst_apply hRv hA']
    exact congrArg (fun F => derivAt0 P (subst F f)) (funext K2)

  have Rint : ∀ f : MvPowerSeries (Σ b, Fin (d b)) C, MvIsInt v f →
      MvIsInt v (subst (Function.extend (fun x : (Σ b : κ', Fin (d (e b))) => (⟨e x.1, x.2⟩ : Σ b, Fin (d b))) (X : (Σ b : κ', Fin (d (e b))) → MvPowerSeries (Σ b : κ', Fin (d (e b))) C) 0) f) := by
    intro f hf α
    rw [coeff_subst_extend_zero hjv]
    exact hf _
  have Rsec : ∀ g : MvPowerSeries (Σ b : κ', Fin (d (e b))) C, MvIsInt v g →
      ∃ f, MvIsInt v f ∧ subst (Function.extend (fun x : (Σ b : κ', Fin (d (e b))) => (⟨e x.1, x.2⟩ : Σ b, Fin (d b))) (X : (Σ b : κ', Fin (d (e b))) → MvPowerSeries (Σ b : κ', Fin (d (e b))) C) 0) f = g := by
    intro g hg
    classical
    refine ⟨@id (MvPowerSeries (Σ b, Fin (d b)) C)
      (Function.extend (Finsupp.mapDomain (fun x : (Σ b : κ', Fin (d (e b))) => (⟨e x.1, x.2⟩ : Σ b, Fin (d b)))) (fun α => coeff α g) 0), ?_, ?_⟩
    · intro β
      show IsIntV v (Function.extend (Finsupp.mapDomain (fun x : (Σ b : κ', Fin (d (e b))) => (⟨e x.1, x.2⟩ : Σ b, Fin (d b)))) (fun α => coeff α g) 0 β)
      rw [Function.extend_def]
      split_ifs with h
      · exact hg _
      · simp [IsIntV]
    · ext α
      rw [coeff_subst_extend_zero hjv]
      exact (Finsupp.mapDomain_injective hjv).extend_apply _ _ α
  unfold depth
  apply le_antisymm
  · refine le_iInf fun g => ?_
    obtain ⟨f, hf, hfg⟩ := Rsec g.1 g.2
    refine (iInf_le _ ⟨f, hf⟩).trans_eq ?_
    dsimp only
    rw [K f, hfg]
  · refine le_iInf fun f => ?_
    refine (iInf_le _ ⟨subst (Function.extend (fun x : (Σ b : κ', Fin (d (e b))) => (⟨e x.1, x.2⟩ : Σ b, Fin (d b))) (X : (Σ b : κ', Fin (d (e b))) → MvPowerSeries (Σ b : κ', Fin (d (e b))) C) 0) f.1, Rint f.1 f.2⟩).trans_eq ?_
    dsimp only
    rw [K f.1]

end

end GlobalTheory.FGDepth

namespace GlobalTheory.FGDepth

/- English proof (translation)
Introduce `C _ _ v κ _ _ d G ι _ _ u κ' _ _ e P`. Conclude with `depth_rename κ d G ι u κ' e P`.
-/
theorem depth_restrict : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (κ : Type) [Fintype κ] [DecidableEq κ] (d : κ → ℕ) (G : ∀ b, LogFGL v (d b)) (ι : κ → Type) [∀ b, Fintype (ι b)] [∀ b, DecidableEq (ι b)] (u : ∀ b, ι b → Fin (d b) → C) (κ' : Type) [Fintype κ'] [DecidableEq κ'] (e : κ' ↪ κ) (P : MvPolynomial (Σ b : κ', ι (e b)) C), depth G u (MvPolynomial.rename (fun x => (⟨e x.1, x.2⟩ : Σ b, ι b)) P) = depth (fun b => G (e b)) (fun b => u (e b)) P := by
  intro C _ _ v κ _ _ d G ι _ _ u κ' _ _ e P
  exact depth_rename κ d G ι u κ' e P

end GlobalTheory.FGDepth
