import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RationalSchwartzBruhatAlgebraIntegralLinearStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianWeilActionSiegelParabolicExplicit
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianWeilActionCommPositiveUnitaryGroupStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilActionLevelSupNormUniformInLatticeStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FiniteClsAndStab
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SiegelWeilDifferenceAutomorphyLinearityStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsGoodSplitPrimeCmFieldStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.NeBotOfNorm
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ClassSumNbStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TwistAdmissible
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TwistedSiegelWeilDifferenceBoundedStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HeckeRelationAdmissibleFamilyPointwiseStatement
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.Step

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ}

/- English proof (translation)
Take `⟨R', C, -, H⟩` from `GlobalTheory.T.weil_action_level_supNorm_uniform_in_lattice E Ψ hΨ n N hn 1 R one_pos h.pos.2`. Use `(H M Λ hΛ 1 Base.one_mem_UU (fun i j => ?_) (φ Λ) ⟨h.supp Λ hΛ, h.per Λ hΛ⟩).1` and prove the remaining obligations. Distinguish the cases in `e : i = j`. Substitute `e` using the available equality. Simplify using `using isIntegral_one`.

Simplify `isIntegral_zero` using `[Matrix.one_apply, e]`.
-/
theorem isSB_of_adm (hΨ : IsType Ψ) (hn : Even n) {M R : ℕ} {φ : Fam E n N} (h : admitted M R φ)
    {Λ : Lt E n} (hΛ : Λ ∈ Vset E n M) : IsSB (φ Λ) := by
  obtain ⟨R', C, -, H⟩ := GlobalTheory.T.weil_action_level_supNorm_uniform_in_lattice E Ψ hΨ n N hn 1 R one_pos h.pos.2
  refine (H M Λ hΛ 1 Base.one_mem_UU (fun i j => ?_) (φ Λ) ⟨h.supp Λ hΛ, h.per Λ hΛ⟩).1
  by_cases e : i = j
  · subst e; simpa using isIntegral_one
  · simpa [Matrix.one_apply, e] using isIntegral_zero

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Use `⟨fun _ _ => isSB_zero, ?_⟩` and prove the remaining obligations. Use `(GlobalTheory.T.siegelWeilDifference_automorphy_linearity E Ψ hΨ n N hn hN M 0 hM (fun _ _ => isSB_zero) Z hZ).2.2.2.1 0` as an intermediate fact. Simplify using `using this`.

Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha, ← ih.2]`. Conclude with `⟨fun Λ hΛ => (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear E _ _ _ _ (h a Λ hΛ) (ih.1 Λ hΛ)).1, (GlobalTheory.T.siegelWeilDifference_automorphy_linearity E Ψ hΨ n N hn hN M (ψ a) hM (h a) Z hZ).2.2.1 _ ih.1⟩`.
-/
theorem swd_sum (hΨ : IsType Ψ) (hn : Even n) (hN : 4 * N < n) {M : ℕ} (hM : 0 < M)
    {Z : CM Ψ N N} (hZ : Z ∈ Hn Ψ N) {ι : Type} (s : Finset ι) (ψ : ι → Fam E n N)
    (h : ∀ i, ∀ Λ ∈ Vset E n M, IsSB (ψ i Λ)) :
    (∀ Λ ∈ Vset E n M, IsSB ((∑ i ∈ s, ψ i) Λ)) ∧
      swd Ψ M (∑ i ∈ s, ψ i) Z 0 0 = ∑ i ∈ s, swd Ψ M (ψ i) Z 0 0 := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨fun _ _ => isSB_zero, ?_⟩
    have := (GlobalTheory.T.siegelWeilDifference_automorphy_linearity E Ψ hΨ n N hn hN M 0 hM (fun _ _ => isSB_zero) Z hZ).2.2.2.1 0
    simpa using this
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih.2]
    exact ⟨fun Λ hΛ => (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear E _ _ _ _ (h a Λ hΛ) (ih.1 Λ hΛ)).1,
      (GlobalTheory.T.siegelWeilDifference_automorphy_linearity E Ψ hΨ n N hn hN M (ψ a) hM (h a) Z hZ).2.2.1 _ ih.1⟩

/- English proof (translation)
Use `(finite_cls_and_stab E n M hM).1` as an intermediate fact. Use `Fintype.ofFinite (Cls E n M)` as an intermediate fact. Simplify using `only [classSum, finsum_eq_sum_of_fintype, Finset.mul_sum]`. Conclude with `Finset.sum_comm`.
-/
theorem classSum_sum {M : ℕ} (hM : 0 < M) {ι : Type} (s : Finset ι) (f : ι → Lt E n → ℂ) :
    classSum M (fun Λ => ∑ i ∈ s, f i Λ) = ∑ i ∈ s, classSum M (f i) := by
  have := (finite_cls_and_stab E n M hM).1
  have := Fintype.ofFinite (Cls E n M)
  simp only [classSum, finsum_eq_sum_of_fintype, Finset.mul_sum]
  exact Finset.sum_comm

/- English proof (translation)
Establish `H` using `(neighbours E n M q P hM hP).2.2`. Establish `hq : 0 < q - 1` using `Nat.sub_pos_of_lt hP.1.one_lt`. Establish `key : ∀ Λ : Lt E n, ∃ e : Fin ((q ^ n - 1) / (q - 1)) → Lt E n, Λ ∈ Vset E n M → (∀ j, e j ∈ Vset E n M) ∧ ∀ g : Lt E n → ℂ, ∑ᶠ Λ' ∈ Nb M P Λ, g Λ' = ∑ j, g (e j)`. Introduce `Λ`. Distinguish the cases in `hΛ : Λ ∈ Vset E n M`.

Take `⟨hf, hc, -⟩` from `H Λ hΛ`. Establish `hc' : hf.toFinset.card = (q ^ n - 1) / (q - 1)`. Rewrite using `[← hc, Nat.mul_div_cancel _ hq, Set.ncard_eq_toFinset_card _ hf]`. Set `σ` to `(Finset.equivFinOfCardEq hc').symm`. Use `⟨fun j => (σ j).1, fun _ => ⟨fun j => (hf.mem_toFinset.1 (σ j).2).1, fun g => ?_⟩⟩` and prove the remaining obligations.

Rewrite using `[finsum_mem_eq_finite_toFinset_sum _ hf, ← Finset.sum_coe_sort, ← σ.sum_comp]`. Conclude with `⟨fun _ => Λ, fun h => (hΛ h).elim⟩`. Use `choose e he using key`. Conclude with `⟨_, fun j Λ => e Λ j, he⟩`.
-/
theorem exists_enum {M q : ℕ} {P : Ideal (𝓞 E)} (hM : 0 < M) (hP : GoodPrime M q P) :
    ∃ (B : ℕ) (e : Fin B → Lt E n → Lt E n), ∀ Λ ∈ Vset E n M, (∀ j, e j Λ ∈ Vset E n M) ∧
      ∀ g : Lt E n → ℂ, ∑ᶠ Λ' ∈ Nb M P Λ, g Λ' = ∑ j, g (e j Λ) := by
  have H := (neighbours E n M q P hM hP).2.2
  have hq : 0 < q - 1 := Nat.sub_pos_of_lt hP.1.one_lt
  have key : ∀ Λ : Lt E n, ∃ e : Fin ((q ^ n - 1) / (q - 1)) → Lt E n, Λ ∈ Vset E n M →
      (∀ j, e j ∈ Vset E n M) ∧ ∀ g : Lt E n → ℂ, ∑ᶠ Λ' ∈ Nb M P Λ, g Λ' = ∑ j, g (e j) := by
    intro Λ
    by_cases hΛ : Λ ∈ Vset E n M
    · obtain ⟨hf, hc, -⟩ := H Λ hΛ
      have hc' : hf.toFinset.card = (q ^ n - 1) / (q - 1) := by
        rw [← hc, Nat.mul_div_cancel _ hq, Set.ncard_eq_toFinset_card _ hf]
      let σ := (Finset.equivFinOfCardEq hc').symm
      refine ⟨fun j => (σ j).1, fun _ => ⟨fun j => (hf.mem_toFinset.1 (σ j).2).1, fun g => ?_⟩⟩
      rw [finsum_mem_eq_finite_toFinset_sum _ hf, ← Finset.sum_coe_sort, ← σ.sum_comp]
    · exact ⟨fun _ => Λ, fun h => (hΛ h).elim⟩
  choose e he using key
  exact ⟨_, fun j Λ => e Λ j, he⟩

/- English proof (translation)
Establish `hM` using `h.pos.1`. Take `⟨B, e, he⟩` from `exists_enum (n := n) hM hP`. Take `⟨h1, h2⟩` from `swd_sum hΨ hn hN hM hZ Finset.univ (fun j Λ => ψ (e j Λ)) (fun j Λ hΛ => isSB_of_adm hΨ hn h ((he Λ hΛ).1 j))`. Establish `eq : ∀ Λ ∈ Vset E n M, (fun x => ∑ᶠ Λ' ∈ Nb M P Λ, ψ Λ' x) = (∑ j, fun Λ => ψ (e j Λ)) Λ` using `fun Λ hΛ => by`. Use function extensionality and compare the values at `x`.

Rewrite using `[(he Λ hΛ).2 fun Λ' => ψ Λ' x]`. Simplify using `only [Finset.sum_apply]`. Use `⟨fun Λ hΛ => (eq Λ hΛ) ▸ h1 Λ hΛ, ?_⟩` and prove the remaining obligations. Rewrite using `[(GlobalTheory.T.siegelWeilDifference_automorphy_linearity E Ψ hΨ n N hn hN M _ hM h1 Z hZ).2.2.2.2 _ eq, h2]`. Establish `H` using `GlobalTheory.T.classSum_sum_nb_eq_of_moves_invariant E n M q P hM hP (fun Λ => thH Ψ (ψ Λ) Z 0 0 - eis Ψ (ψ Λ) Z 0 0) (by`.

Introduce `g hg Λ hΛ Λ' hΛ' m`. Establish `e1 : (fun x : Matrix (Fin n) (Fin N) E => ψ Λ' (g * x)) = ψ Λ`. Use function extensionality and compare the values at `(h.equiv g hg Λ hΛ Λ' hΛ' m)`. Use `(GlobalTheory.T.hermitianWeilAction_comm_positiveUnitaryGroup E Ψ hΨ n N hn g hg.1 (ψ Λ') (isSB_of_adm hΨ hn h hΛ')).2.2 Z hZ` as an intermediate fact. Conclude with `congrArg₂ (· - ·) (this.1.symm.trans (congrArg (thH Ψ · Z 0 0) e1)) (this.2.symm.trans (congrArg (eis Ψ · Z 0 0) e1)))`.

Use `Eq.trans ?_ H` and prove the remaining obligations. Use `congr 1`. Unfold `swd`. Rewrite using `[← classSum_sum hM]`. Conclude with `Base.classSum_congr fun Λ hΛ => ((he Λ hΛ).2 fun Λ => thH Ψ (ψ Λ) Z 0 0 - eis Ψ (ψ Λ) Z 0 0).symm`.
-/
theorem swd_nb (hΨ : IsType Ψ) (hn : Even n) (hN : 4 * N < n) {M R q : ℕ} {P : Ideal (𝓞 E)}
    {ψ : Fam E n N} (h : admitted M R ψ) (hP : GoodPrime M q P) {Z : CM Ψ N N} (hZ : Z ∈ Hn Ψ N) :
    (∀ Λ ∈ Vset E n M, IsSB fun x => ∑ᶠ Λ' ∈ Nb M P Λ, ψ Λ' x) ∧
      ((q : ℂ) - 1) * swd Ψ M (fun Λ x => ∑ᶠ Λ' ∈ Nb M P Λ, ψ Λ' x) Z 0 0 =
        ((q : ℂ) ^ n - 1) * swd Ψ M ψ Z 0 0 := by
  have hM := h.pos.1
  obtain ⟨B, e, he⟩ := exists_enum (n := n) hM hP
  obtain ⟨h1, h2⟩ := swd_sum hΨ hn hN hM hZ Finset.univ (fun j Λ => ψ (e j Λ))
    (fun j Λ hΛ => isSB_of_adm hΨ hn h ((he Λ hΛ).1 j))
  have eq : ∀ Λ ∈ Vset E n M, (fun x => ∑ᶠ Λ' ∈ Nb M P Λ, ψ Λ' x) =
      (∑ j, fun Λ => ψ (e j Λ)) Λ := fun Λ hΛ => by
    funext x
    rw [(he Λ hΛ).2 fun Λ' => ψ Λ' x]
    simp only [Finset.sum_apply]
  refine ⟨fun Λ hΛ => (eq Λ hΛ) ▸ h1 Λ hΛ, ?_⟩
  rw [(GlobalTheory.T.siegelWeilDifference_automorphy_linearity E Ψ hΨ n N hn hN M _ hM h1 Z hZ).2.2.2.2 _ eq, h2]
  have H := GlobalTheory.T.classSum_sum_nb_eq_of_moves_invariant E n M q P hM hP (fun Λ => thH Ψ (ψ Λ) Z 0 0 - eis Ψ (ψ Λ) Z 0 0) (by
    intro g hg Λ hΛ Λ' hΛ' m
    have e1 : (fun x : Matrix (Fin n) (Fin N) E => ψ Λ' (g * x)) = ψ Λ :=
      funext (h.equiv g hg Λ hΛ Λ' hΛ' m)
    have := (GlobalTheory.T.hermitianWeilAction_comm_positiveUnitaryGroup E Ψ hΨ n N hn g hg.1 (ψ Λ') (isSB_of_adm hΨ hn h hΛ')).2.2 Z hZ
    exact congrArg₂ (· - ·) (this.1.symm.trans (congrArg (thH Ψ · Z 0 0) e1))
      (this.2.symm.trans (congrArg (eis Ψ · Z 0 0) e1)))
  refine Eq.trans ?_ H
  congr 1
  unfold swd
  rw [← classSum_sum hM]
  exact Base.classSum_congr fun Λ hΛ =>
    ((he Λ hΛ).2 fun Λ => thH Ψ (ψ Λ) Z 0 0 - eis Ψ (ψ Λ) Z 0 0).symm

omit [NumberField E] [IsCMField E] in

/- English proof (translation)
The claim follows from `Finset.prod_pos fun τ _ => (Complex.pos_iff.1 (hZ τ).det_pos).1`.
-/
theorem detIm_pos {Z : CM Ψ N N} (hZ : Z ∈ Hn Ψ N) : 0 < detIm Z :=
  Finset.prod_pos fun τ _ => (Complex.pos_iff.1 (hZ τ).det_pos).1

/- English proof (translation)
Unfold `imH`. Rewrite using `[conjTranspose_add, ← Base.ccT_map, hβ]`. Use `congr 1`. Normalize the expressions using the abelian group laws.
-/
theorem imH_add (Z : CM Ψ N N) {β : Matrix (Fin N) (Fin N) E} (hβ : ccT β = β) (τ : Ψ) :
    imH (Z τ + β.map τ.1) = imH (Z τ) := by
  unfold imH
  rw [conjTranspose_add, ← Base.ccT_map, hβ]
  congr 1
  abel

/- English proof (translation)
Take `⟨A, XA, XB, β, hA, hX, hid⟩` from `GlobalTheory.T.hecke_relation_admissibleFamily_pointwise E Ψ hΨ n N M R q P φ 𝔛 h h1 h2 hP`. Use `⟨A, XA, XB, β, hA, hX, fun Z hZ => ?_⟩` and prove the remaining obligations. Establish `hM` using `h.pos.1`. Establish `hP' : GoodPrime M q P` using `⟨hP.1, Nat.Coprime.coprime_mul_left_right hP.2.1, hP.2.2⟩`. Establish `adm : ∀ Y : Lt E N, Y.FG → Agree (R * M) Y (stdL E N) → ∃ R', admitted M R' (twist R Y φ)` using `fun Y a b => (twist_admissible E n N M R φ Y h a b).2.2.2.2.1`.

Establish `sb : ∀ Y : Lt E N, Y.FG → Agree (R * M) Y (stdL E N) → ∀ Λ ∈ Vset E n M, IsSB (twist R Y φ Λ)` using `fun Y a b Λ hΛ => isSB_of_adm hΨ hn (adm Y a b).choose_spec hΛ`. Establish `aut` using `fun (ψ : Fam E n N) hψ => GlobalTheory.T.siegelWeilDifference_automorphy_linearity E Ψ hΨ n N hn hN M ψ hM hψ Z hZ`. Establish `sbs : ∀ (c : ℂ) (ψ : Fam E n N), (∀ Λ ∈ Vset E n M, IsSB (ψ Λ)) → ∀ Λ ∈ Vset E n M, IsSB ((c • ψ) Λ)` using `fun c ψ hψ Λ hΛ => (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear E _ _ _ _ (hψ Λ hΛ) (hψ Λ hΛ)).2.1 c`. Establish `sba : ∀ (ψ ψ' : Fam E n N), (∀ Λ ∈ Vset E n M, IsSB (ψ Λ)) → (∀ Λ ∈ Vset E n M, IsSB (ψ' Λ)) → ∀ Λ ∈ Vset E n M, IsSB ((ψ + ψ') Λ)` using `fun ψ ψ' hψ hψ' Λ hΛ => (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear E _ _ _ _ (hψ Λ hΛ) (hψ' Λ hΛ)).1`. Take `⟨a1, a2⟩` from `swd_sum hΨ hn hN hM hZ Finset.univ (fun i => twist R (XA i) φ) fun i => sb _ (hX i).1 (hX i).2.1`.

Establish `sbB : ∀ i, ∀ Λ ∈ Vset E n M, IsSB (twist R (XB i) φ Λ)` using `fun i => sb _ (hX i).2.2.2.1 (hX i).2.2.2.2.1`. Establish `b` using `fun i => swd_sum hΨ hn hN hM hZ Finset.univ (fun j Λ x => chiH Ψ (β i j) x * twist R (XB i) φ Λ x) fun j Λ hΛ => by`. Simplify using `using Parab.isSB_chiH hΨ ((hX i).2.2.2.2.2.2 j) 1 (sbB i Λ hΛ)`. Take `⟨b1, b2⟩` from `swd_sum hΨ hn hN hM hZ Finset.univ _ fun i => (b i).1`. Take `⟨R', hR'⟩` from `adm 𝔛 h1 h2`.

Take `⟨c1, c2⟩` from `swd_nb hΨ hn hN hR' hP' hZ`. Establish `d1` using `sb 𝔛 h1 h2`. Establish `hL` using `sba _ _ (sbs ((q : ℂ) ^ n) _ a1) b1`. Establish `e` using `(aut _ (sbs ((q : ℂ) - 1) _ hL)).2.2.2.2 ((((q : ℂ) - 1) * (q : ℂ) ^ N) • (fun Λ x => ∑ᶠ Λ' ∈ Nb M P Λ, twist R 𝔛 φ Λ' x) + ((q : ℂ) ^ (2 * N) - (q : ℂ) ^ n) • twist R 𝔛 φ) (fun Λ hΛ => by`. Use function extensionality and compare the values at `x`.

Simplify using `only [Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]`. Conclude with `(hid Λ hΛ x).symm)`. Rewrite `e` using `[(aut _ (sbs _ _ c1)).2.2.1 _ (sbs _ _ d1), (aut _ c1).2.2.2.1, (aut _ d1).2.2.2.1, (aut _ hL).2.2.2.1, (aut _ (sbs _ _ a1)).2.2.1 _ b1, (aut _ a1).2.2.2.1, a2, b2]`. Establish `f : ∀ i, swd Ψ M (∑ j, fun Λ x => chiH Ψ (β i j) x * twist R (XB i) φ Λ x) Z 0 0 = ∑ j, swd Ψ M (twist R (XB i) φ) (fun τ => Z τ + (β i j).map τ.1) 0 0` using `fun i => by`. Rewrite using `[(b i).2]`.

Conclude with `Finset.sum_congr rfl fun j _ => (aut _ (sbB i)).2.1 _ ((hX i).2.2.2.2.2.2 j)`. Simplify using `only [f] at e`. Rewrite using `[← e]`. Take the linear combination `(-(q : ℂ) ^ N) * c2`.
-/
theorem hecke_swd (hΨ : IsType Ψ) (hn : Even n) (hN : 4 * N < n) {M R q : ℕ} {P : Ideal (𝓞 E)}
    {φ : Fam E n N} (h : admitted M R φ) (hP : GoodPrime (R * M) q P) {𝔛 : Lt E N} (h1 : 𝔛.FG)
    (h2 : Agree (R * M) 𝔛 (stdL E N)) :
    ∃ (A : ℕ) (XA XB : Fin A → Lt E N) (β : Fin A → Fin (q ^ N) → Matrix (Fin N) (Fin N) E),
      A * (q - 1) = q ^ N - 1 ∧
      (∀ i, (XA i).FG ∧ Agree (R * M) (XA i) (stdL E N) ∧ gidx (XA i) = q * gidx 𝔛 ∧
        (XB i).FG ∧ Agree (R * M) (XB i) (stdL E N) ∧ q * gidx (XB i) = gidx 𝔛 ∧
        ∀ j, ccT (β i j) = β i j) ∧
      ∀ Z ∈ Hn Ψ N, ((q : ℂ) ^ N - 1) * ((q : ℂ) ^ n + (q : ℂ) ^ N) *
          swd Ψ M (twist R 𝔛 φ) Z 0 0 =
        ((q : ℂ) - 1) * ((q : ℂ) ^ n * ∑ i, swd Ψ M (twist R (XA i) φ) Z 0 0 +
          ∑ i, ∑ j, swd Ψ M (twist R (XB i) φ) (fun τ => Z τ + (β i j).map τ.1) 0 0) := by
  obtain ⟨A, XA, XB, β, hA, hX, hid⟩ := GlobalTheory.T.hecke_relation_admissibleFamily_pointwise E Ψ hΨ n N M R q P φ 𝔛 h h1 h2 hP
  refine ⟨A, XA, XB, β, hA, hX, fun Z hZ => ?_⟩
  have hM := h.pos.1
  have hP' : GoodPrime M q P := ⟨hP.1, Nat.Coprime.coprime_mul_left_right hP.2.1, hP.2.2⟩
  have adm : ∀ Y : Lt E N, Y.FG → Agree (R * M) Y (stdL E N) → ∃ R', admitted M R' (twist R Y φ) :=
    fun Y a b => (twist_admissible E n N M R φ Y h a b).2.2.2.2.1
  have sb : ∀ Y : Lt E N, Y.FG → Agree (R * M) Y (stdL E N) → ∀ Λ ∈ Vset E n M,
      IsSB (twist R Y φ Λ) := fun Y a b Λ hΛ => isSB_of_adm hΨ hn (adm Y a b).choose_spec hΛ
  have aut := fun (ψ : Fam E n N) hψ => GlobalTheory.T.siegelWeilDifference_automorphy_linearity E Ψ hΨ n N hn hN M ψ hM hψ Z hZ
  have sbs : ∀ (c : ℂ) (ψ : Fam E n N), (∀ Λ ∈ Vset E n M, IsSB (ψ Λ)) →
      ∀ Λ ∈ Vset E n M, IsSB ((c • ψ) Λ) := fun c ψ hψ Λ hΛ =>
    (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear E _ _ _ _ (hψ Λ hΛ) (hψ Λ hΛ)).2.1 c
  have sba : ∀ (ψ ψ' : Fam E n N), (∀ Λ ∈ Vset E n M, IsSB (ψ Λ)) →
      (∀ Λ ∈ Vset E n M, IsSB (ψ' Λ)) → ∀ Λ ∈ Vset E n M, IsSB ((ψ + ψ') Λ) :=
    fun ψ ψ' hψ hψ' Λ hΛ => (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear E _ _ _ _ (hψ Λ hΛ) (hψ' Λ hΛ)).1
  obtain ⟨a1, a2⟩ := swd_sum hΨ hn hN hM hZ Finset.univ (fun i => twist R (XA i) φ)
    fun i => sb _ (hX i).1 (hX i).2.1
  have sbB : ∀ i, ∀ Λ ∈ Vset E n M, IsSB (twist R (XB i) φ Λ) :=
    fun i => sb _ (hX i).2.2.2.1 (hX i).2.2.2.2.1
  have b := fun i => swd_sum hΨ hn hN hM hZ Finset.univ
    (fun j Λ x => chiH Ψ (β i j) x * twist R (XB i) φ Λ x) fun j Λ hΛ => by
      simpa using Parab.isSB_chiH hΨ ((hX i).2.2.2.2.2.2 j) 1 (sbB i Λ hΛ)
  obtain ⟨b1, b2⟩ := swd_sum hΨ hn hN hM hZ Finset.univ _ fun i => (b i).1
  obtain ⟨R', hR'⟩ := adm 𝔛 h1 h2
  obtain ⟨c1, c2⟩ := swd_nb hΨ hn hN hR' hP' hZ
  have d1 := sb 𝔛 h1 h2
  have hL := sba _ _ (sbs ((q : ℂ) ^ n) _ a1) b1
  have e := (aut _ (sbs ((q : ℂ) - 1) _ hL)).2.2.2.2
    ((((q : ℂ) - 1) * (q : ℂ) ^ N) • (fun Λ x => ∑ᶠ Λ' ∈ Nb M P Λ, twist R 𝔛 φ Λ' x) +
      ((q : ℂ) ^ (2 * N) - (q : ℂ) ^ n) • twist R 𝔛 φ) (fun Λ hΛ => by
      funext x
      simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
      exact (hid Λ hΛ x).symm)
  rw [(aut _ (sbs _ _ c1)).2.2.1 _ (sbs _ _ d1), (aut _ c1).2.2.2.1, (aut _ d1).2.2.2.1,
    (aut _ hL).2.2.2.1, (aut _ (sbs _ _ a1)).2.2.1 _ b1, (aut _ a1).2.2.2.1, a2, b2] at e
  have f : ∀ i, swd Ψ M (∑ j, fun Λ x => chiH Ψ (β i j) x * twist R (XB i) φ Λ x) Z 0 0 =
      ∑ j, swd Ψ M (twist R (XB i) φ) (fun τ => Z τ + (β i j).map τ.1) 0 0 := fun i => by
    rw [(b i).2]
    exact Finset.sum_congr rfl fun j _ => (aut _ (sbB i)).2.1 _ ((hX i).2.2.2.2.2.2 j)
  simp only [f] at e
  rw [← e]
  linear_combination (-(q : ℂ) ^ N) * c2

/- English proof (translation)
Take `⟨A, XA, XB, β, hA, hX, hid⟩` from `hecke_swd hΨ ⟨k, rfl⟩ hN h hP h1 h2`. Establish `hq1 : 1 < q` using `hP.1.one_lt`. Establish `hq : (1 : ℝ) < q` using `by exact_mod_cast hq1`. Establish `hqN : (1 : ℝ) < (q : ℝ) ^ N` using `one_lt_pow₀ hq hN0.ne'`. Establish `hA' : (A : ℝ) * ((q : ℝ) - 1) = (q : ℝ) ^ N - 1`.

Use `congrArg (Nat.cast : ℕ → ℝ) hA` as an intermediate fact. Rewrite `this` using `[Nat.cast_mul, Nat.cast_sub hq1.le, Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), Nat.cast_pow, Nat.cast_one]`. Then use the resulting hypothesis. Establish `hg : 0 < gidx 𝔛` using `(twist_admissible E _ N M R φ 𝔛 h h1 h2).2.2.2.1`. Establish `hd` using `detIm_pos hZ`. Use `set w : ℝ := gidx 𝔛 ^ k * detIm Z ^ k with hw`.

Establish `hw0 : 0 < w` using `by positivity`. Establish `hqk : (0 : ℝ) < (q : ℝ) ^ k` using `by positivity`. Establish `hAi : ∀ i, (q : ℝ) ^ k * (w * ‖swd Ψ M (twist R (XA i) φ) Z 0 0‖) ≤ S` using `fun i => by`. Use `hS _ (hX i).1 (hX i).2.1 Z hZ` as an intermediate fact. Rewrite `this` using `[(hX i).2.2.1, mul_pow]`.

Conclude with `le_of_eq_of_le (by rw [hw]; ring) this`. Establish `hBi : ∀ i j, w * ‖swd Ψ M (twist R (XB i) φ) (fun τ => Z τ + (β i j).map τ.1) 0 0‖ ≤ (q : ℝ) ^ k * S` using `fun i j => by`. Establish `hi` using `imH_add Z ((hX i).2.2.2.2.2.2 j)`. Use `hS _ (hX i).2.2.2.1 (hX i).2.2.2.2.1 (fun τ => Z τ + (β i j).map τ.1) (fun τ => by simp only [hi]; exact hZ τ)` as an intermediate fact. Establish `e : detIm (fun τ : Ψ => Z τ + (β i j).map τ.1) = detIm Z` using `by simp only [detIm, hi]`.

Rewrite `this` using `[e]`. Use `le_of_eq_of_le ?_ (mul_le_mul_of_nonneg_left this hqk.le)` and prove the remaining obligations. Rewrite using `[hw, ← (hX i).2.2.2.2.2.1, mul_pow]`. Expand and normalize the polynomial expressions, which then agree. Establish `hn` using `congrArg norm (hid Z hZ)`.

Establish `n1 : ‖((q : ℂ) ^ N - 1) * ((q : ℂ) ^ (k + k) + (q : ℂ) ^ N)‖ = ((q : ℝ) ^ N - 1) * ((q : ℝ) ^ (k + k) + (q : ℝ) ^ N)`. Rewrite using `[← Real.norm_of_nonneg (r := ((q : ℝ) ^ N - 1) * ((q : ℝ) ^ (k + k) + (q : ℝ) ^ N)) (mul_nonneg (by linarith) (by positivity)), ← Complex.norm_real]`. Use `push_cast`. Both sides reduce to the same expression. Establish `n2 : ‖(q : ℂ) - 1‖ = (q : ℝ) - 1`.

Rewrite using `[← Real.norm_of_nonneg (r := (q : ℝ) - 1) (by linarith), ← Complex.norm_real]`. Use `push_cast`. Both sides reduce to the same expression. Rewrite `hn` using `[norm_mul, n1, norm_mul, n2]`. Establish `hle : w * ‖(q : ℂ) ^ (k + k) * ∑ i, swd Ψ M (twist R (XA i) φ) Z 0 0 + ∑ i, ∑ j, swd Ψ M (twist R (XB i) φ) (fun τ => Z τ + (β i j).map τ.1) 0 0‖ ≤ A * ((q : ℝ) ^ k * (1 + (q : ℝ) ^ N) * S)`.

Combine the equalities or inequalities in the displayed calculation. Use `mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add ?_ ?_)) hw0.le` and prove the remaining obligations. Rewrite using `[norm_mul, norm_pow, Complex.norm_natCast]`. Conclude with `mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)`. Conclude with `(norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)`.

Use `_ = (∑ i, (q : ℝ) ^ k * ((q : ℝ) ^ k * (w * ‖swd Ψ M (twist R (XA i) φ) Z 0 0‖))) + ∑ i, ∑ j, w * ‖swd Ψ M (twist R (XB i) φ) (fun τ => Z τ + (β i j).map τ.1) 0 0‖ := by`. Simplify using `only [← Finset.mul_sum]`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ (∑ _i : Fin A, (q : ℝ) ^ k * S) + ∑ _i : Fin A, ∑ _j : Fin (q ^ N), (q : ℝ) ^ k * S := add_le_add (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hAi i) hqk.le) (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hBi i j)`. Use `_ = _ := by`.

Simplify using `only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[div_mul_eq_mul_div, le_div_iff₀ (by positivity)]`. Use `le_of_mul_le_mul_left ?_ (sub_pos.2 hqN)` and prove the remaining obligations.

Use `mul_le_mul_of_nonneg_left hle (sub_pos.2 hq).le` as an intermediate fact. Rewrite `this` using `[mul_left_comm, ← hn, ← mul_assoc ((q : ℝ) - 1), mul_comm ((q : ℝ) - 1), hA']`. Conclude with `le_of_eq_of_le (by rw [hw]; ring) this`.
-/
theorem bound_step (hΨ : IsType Ψ) {k : ℕ} (hN0 : 0 < N) (hN : 4 * N < k + k) {M R q : ℕ}
    {P : Ideal (𝓞 E)} {φ : Fam E (k + k) N} (h : admitted M R φ) (hP : GoodPrime (R * M) q P) {S : ℝ}
    (hS : ∀ 𝔛 : Lt E N, 𝔛.FG → Agree (R * M) 𝔛 (stdL E N) → ∀ Z ∈ Hn Ψ N,
      gidx 𝔛 ^ k * ‖swd Ψ M (twist R 𝔛 φ) Z 0 0‖ * detIm Z ^ k ≤ S)
    (𝔛 : Lt E N) (h1 : 𝔛.FG) (h2 : Agree (R * M) 𝔛 (stdL E N)) (Z : CM Ψ N N)
    (hZ : Z ∈ Hn Ψ N) :
    gidx 𝔛 ^ k * ‖swd Ψ M (twist R 𝔛 φ) Z 0 0‖ * detIm Z ^ k ≤
      (q : ℝ) ^ k * (1 + (q : ℝ) ^ N) / ((q : ℝ) ^ (k + k) + (q : ℝ) ^ N) * S := by
  obtain ⟨A, XA, XB, β, hA, hX, hid⟩ := hecke_swd hΨ ⟨k, rfl⟩ hN h hP h1 h2
  have hq1 : 1 < q := hP.1.one_lt
  have hq : (1 : ℝ) < q := by exact_mod_cast hq1
  have hqN : (1 : ℝ) < (q : ℝ) ^ N := one_lt_pow₀ hq hN0.ne'
  have hA' : (A : ℝ) * ((q : ℝ) - 1) = (q : ℝ) ^ N - 1 := by
    have := congrArg (Nat.cast : ℕ → ℝ) hA
    rwa [Nat.cast_mul, Nat.cast_sub hq1.le, Nat.cast_sub (Nat.one_le_pow _ _ (by omega)),
      Nat.cast_pow, Nat.cast_one] at this
  have hg : 0 < gidx 𝔛 := (twist_admissible E _ N M R φ 𝔛 h h1 h2).2.2.2.1
  have hd := detIm_pos hZ
  set w : ℝ := gidx 𝔛 ^ k * detIm Z ^ k with hw
  have hw0 : 0 < w := by positivity
  have hqk : (0 : ℝ) < (q : ℝ) ^ k := by positivity
  have hAi : ∀ i, (q : ℝ) ^ k * (w * ‖swd Ψ M (twist R (XA i) φ) Z 0 0‖) ≤ S := fun i => by
    have := hS _ (hX i).1 (hX i).2.1 Z hZ
    rw [(hX i).2.2.1, mul_pow] at this
    exact le_of_eq_of_le (by rw [hw]; ring) this
  have hBi : ∀ i j, w * ‖swd Ψ M (twist R (XB i) φ) (fun τ => Z τ + (β i j).map τ.1) 0 0‖ ≤
      (q : ℝ) ^ k * S := fun i j => by
    have hi := imH_add Z ((hX i).2.2.2.2.2.2 j)
    have := hS _ (hX i).2.2.2.1 (hX i).2.2.2.2.1 (fun τ => Z τ + (β i j).map τ.1)
      (fun τ => by simp only [hi]; exact hZ τ)
    have e : detIm (fun τ : Ψ => Z τ + (β i j).map τ.1) = detIm Z := by simp only [detIm, hi]
    rw [e] at this
    refine le_of_eq_of_le ?_ (mul_le_mul_of_nonneg_left this hqk.le)
    rw [hw, ← (hX i).2.2.2.2.2.1, mul_pow]; ring
  have hn := congrArg norm (hid Z hZ)
  have n1 : ‖((q : ℂ) ^ N - 1) * ((q : ℂ) ^ (k + k) + (q : ℂ) ^ N)‖ =
      ((q : ℝ) ^ N - 1) * ((q : ℝ) ^ (k + k) + (q : ℝ) ^ N) := by
    rw [← Real.norm_of_nonneg (r := ((q : ℝ) ^ N - 1) * ((q : ℝ) ^ (k + k) + (q : ℝ) ^ N))
      (mul_nonneg (by linarith) (by positivity)), ← Complex.norm_real]
    push_cast; rfl
  have n2 : ‖(q : ℂ) - 1‖ = (q : ℝ) - 1 := by
    rw [← Real.norm_of_nonneg (r := (q : ℝ) - 1) (by linarith), ← Complex.norm_real]
    push_cast; rfl
  rw [norm_mul, n1, norm_mul, n2] at hn
  have hle : w * ‖(q : ℂ) ^ (k + k) * ∑ i, swd Ψ M (twist R (XA i) φ) Z 0 0 +
      ∑ i, ∑ j, swd Ψ M (twist R (XB i) φ) (fun τ => Z τ + (β i j).map τ.1) 0 0‖ ≤
      A * ((q : ℝ) ^ k * (1 + (q : ℝ) ^ N) * S) := by
    calc _ ≤ w * ((q : ℝ) ^ (k + k) * ∑ i, ‖swd Ψ M (twist R (XA i) φ) Z 0 0‖ +
          ∑ i, ∑ j, ‖swd Ψ M (twist R (XB i) φ) (fun τ => Z τ + (β i j).map τ.1) 0 0‖) := by
          refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add ?_ ?_)) hw0.le
          · rw [norm_mul, norm_pow, Complex.norm_natCast]
            exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
          · exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
      _ = (∑ i, (q : ℝ) ^ k * ((q : ℝ) ^ k * (w * ‖swd Ψ M (twist R (XA i) φ) Z 0 0‖))) +
          ∑ i, ∑ j, w * ‖swd Ψ M (twist R (XB i) φ) (fun τ => Z τ + (β i j).map τ.1) 0 0‖ := by
          simp only [← Finset.mul_sum]; ring
      _ ≤ (∑ _i : Fin A, (q : ℝ) ^ k * S) + ∑ _i : Fin A, ∑ _j : Fin (q ^ N), (q : ℝ) ^ k * S :=
          add_le_add (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hAi i) hqk.le)
            (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hBi i j)
      _ = _ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast; ring
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  refine le_of_mul_le_mul_left ?_ (sub_pos.2 hqN)
  have := mul_le_mul_of_nonneg_left hle (sub_pos.2 hq).le
  rw [mul_left_comm, ← hn, ← mul_assoc ((q : ℝ) - 1), mul_comm ((q : ℝ) - 1), hA'] at this
  exact le_of_eq_of_le (by rw [hw]; ring) this

end GlobalTheory.SW.Step

open GlobalTheory.SW.Step in

/- English proof (translation)
Introduce `E _ _ _ Ψ hΨ n N hn hN hSW M R φ h Z hZ`. Take `⟨C, hC⟩` from `GlobalTheory.T.twisted_siegelWeil_difference_bounded E Ψ hΨ n N hn hN hSW M R φ h`. Take `⟨k, rfl⟩` from `hn`. Establish `ek : ((k + k : ℕ) : ℝ) / 2 = (k : ℝ)` using `by push_cast; ring`. Simplify using `only [ek, Real.rpow_natCast] at hC`.

Take `⟨q, P, hP⟩` from `GlobalTheory.T.exists_good_split_prime_cmField E (R * M) (Nat.mul_pos h.pos.2 h.pos.1)`. Establish `hq : (1 : ℝ) < q` using `by exact_mod_cast hP.1.one_lt`. Use `set θ : ℝ := (q : ℝ) ^ k * (1 + (q : ℝ) ^ (N + 1)) / ((q : ℝ) ^ (k + k) + (q : ℝ) ^ (N + 1)) with hθ`. Establish `θ0 : 0 ≤ θ` using `by positivity`. Establish `θ1 : θ < 1`.

Rewrite using `[hθ, div_lt_one (by positivity), pow_add _ k k]`. Establish `a : (q : ℝ) ^ (N + 1) < (q : ℝ) ^ k` using `pow_lt_pow_right₀ hq (by omega)`. Establish `b : (1 : ℝ) < (q : ℝ) ^ k` using `one_lt_pow₀ hq (by omega)`. Use polynomial arithmetic with `[mul_pos (sub_pos.2 a) (sub_pos.2 b)]`. Establish `key : ∀ m : ℕ, ∀ 𝔛 : Lt E (N + 1), 𝔛.FG → Agree (R * M) 𝔛 (stdL E (N + 1)) → ∀ Z ∈ Hn Ψ (N + 1), gidx 𝔛 ^ k * ‖swd Ψ M (twist R 𝔛 φ) Z 0 0‖ * detIm Z ^ k ≤ θ ^ m * C`.

Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => simpa using hC`. Consider the case `succ m ih`. Introduce `𝔛 h1 h2 Z hZ`.

Rewrite using `[pow_succ', mul_assoc θ]`. Conclude with `bound_step hΨ N.succ_pos hN h hP ih 𝔛 h1 h2 Z hZ`. Establish `s1 : (stdL E (N + 1)).FG` using `Submodule.fg_span (Set.finite_range _)`. Establish `s2 : Agree (R * M) (stdL E (N + 1)) (stdL E (N + 1))` using `⟨1, one_pos, Nat.coprime_one_left _, by simp, by simp⟩`. Establish `lim : Tendsto (fun m : ℕ => θ ^ m * C) atTop (𝓝 0)`.

Simplify using `using (tendsto_pow_atTop_nhds_zero_of_lt_one θ0 θ1).mul_const C`. Establish `le0` using `ge_of_tendsto' lim fun m => key m _ s1 s2 Z hZ`. Rewrite `le0` using `[Base.gidx_stdL, one_pow, one_mul]`. Establish `z : ‖swd Ψ M (twist R (stdL E (N + 1)) φ) Z 0 0‖ ≤ 0` using `nonpos_of_mul_nonpos_left le0 (pow_pos (detIm_pos hZ) k)`. Rewrite using `[← norm_le_zero_iff.1 z]`.

Conclude with `Base.classSum_congr fun Λ hΛ => by`. Rewrite using `[(twist_admissible E _ _ M R φ _ h s1 s2).2.1 Λ hΛ]`.
-/
theorem GlobalTheory.SW.swAt_succ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → 4 * (N + 1) < n → SWAt Ψ n N → SWAt Ψ n (N + 1) := by
  intro E _ _ _ Ψ hΨ n N hn hN hSW M R φ h Z hZ
  obtain ⟨C, hC⟩ := GlobalTheory.T.twisted_siegelWeil_difference_bounded E Ψ hΨ n N hn hN hSW M R φ h
  obtain ⟨k, rfl⟩ := hn
  have ek : ((k + k : ℕ) : ℝ) / 2 = (k : ℝ) := by push_cast; ring
  simp only [ek, Real.rpow_natCast] at hC
  obtain ⟨q, P, hP⟩ := GlobalTheory.T.exists_good_split_prime_cmField E (R * M) (Nat.mul_pos h.pos.2 h.pos.1)
  have hq : (1 : ℝ) < q := by exact_mod_cast hP.1.one_lt
  set θ : ℝ := (q : ℝ) ^ k * (1 + (q : ℝ) ^ (N + 1)) / ((q : ℝ) ^ (k + k) + (q : ℝ) ^ (N + 1))
    with hθ
  have θ0 : 0 ≤ θ := by positivity
  have θ1 : θ < 1 := by
    rw [hθ, div_lt_one (by positivity), pow_add _ k k]
    have a : (q : ℝ) ^ (N + 1) < (q : ℝ) ^ k := pow_lt_pow_right₀ hq (by omega)
    have b : (1 : ℝ) < (q : ℝ) ^ k := one_lt_pow₀ hq (by omega)
    nlinarith [mul_pos (sub_pos.2 a) (sub_pos.2 b)]
  have key : ∀ m : ℕ, ∀ 𝔛 : Lt E (N + 1), 𝔛.FG → Agree (R * M) 𝔛 (stdL E (N + 1)) →
      ∀ Z ∈ Hn Ψ (N + 1),
      gidx 𝔛 ^ k * ‖swd Ψ M (twist R 𝔛 φ) Z 0 0‖ * detIm Z ^ k ≤ θ ^ m * C := by
    intro m
    induction m with
    | zero => simpa using hC
    | succ m ih =>
      intro 𝔛 h1 h2 Z hZ
      rw [pow_succ', mul_assoc θ]
      exact bound_step hΨ N.succ_pos hN h hP ih 𝔛 h1 h2 Z hZ
  have s1 : (stdL E (N + 1)).FG := Submodule.fg_span (Set.finite_range _)
  have s2 : Agree (R * M) (stdL E (N + 1)) (stdL E (N + 1)) :=
    ⟨1, one_pos, Nat.coprime_one_left _, by simp, by simp⟩
  have lim : Tendsto (fun m : ℕ => θ ^ m * C) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one θ0 θ1).mul_const C
  have le0 := ge_of_tendsto' lim fun m => key m _ s1 s2 Z hZ
  rw [Base.gidx_stdL, one_pow, one_mul] at le0
  have z : ‖swd Ψ M (twist R (stdL E (N + 1)) φ) Z 0 0‖ ≤ 0 :=
    nonpos_of_mul_nonpos_left le0 (pow_pos (detIm_pos hZ) k)
  rw [← norm_le_zero_iff.1 z]
  exact Base.classSum_congr fun Λ hΛ => by
    rw [(twist_admissible E _ _ M R φ _ h s1 s2).2.1 Λ hΛ]
