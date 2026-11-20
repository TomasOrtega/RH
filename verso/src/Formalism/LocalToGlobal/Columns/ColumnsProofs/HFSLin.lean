import Mathlib
import Formalism.LocalToGlobal.Columns.HeckeInert
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HfsAevalRestrict

open Module NumberField IsDedekindDomain Polynomial

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV

section HfsSplit

open Polynomial Module.End

variable {L W : Type} [Field L] [AddCommGroup W] [Module L W]

/- English proof (translation)
Apply the tactic sequence `first | exact UpperTheory.Reformulated.B.Qh20.hfs_aeval_restrict .. | (apply UpperTheory.Reformulated.B.Qh20.hfs_aeval_restrict <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qh20.hfs_aeval_restrict <;> assumption) | (apply @UpperTheory.Reformulated.B.Qh20.hfs_aeval_ …`.
-/
theorem hfs_aeval_restrict (f : Module.End L W) {p : Submodule L W} (h : ∀ x ∈ p, f x ∈ p) (q : L[X]) (x : p) :
    ((aeval (f.restrict h) q x : p) : W) = aeval f q x := by
  first | exact UpperTheory.Reformulated.B.Qh20.hfs_aeval_restrict .. | (apply UpperTheory.Reformulated.B.Qh20.hfs_aeval_restrict <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qh20.hfs_aeval_restrict <;> assumption) | (apply @UpperTheory.Reformulated.B.Qh20.hfs_aeval_restrict <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qh20.hfs_aeval_restrict <;> assumption) | (apply @UpperTheory.Reformulated.B.Qh20.hfs_aeval_restrict <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qh20.hfs_aeval_restrict L W ‹_› ‹_› ‹_› f p h q x | exact @UpperTheory.Reformulated.B.Qh20.hfs_aeval_restrict L W ‹_› ‹_› ‹_› f p h q | exact @UpperTheory.Reformulated.B.Qh20.hfs_aeval_restrict L W ‹_› ‹_› ‹_› f p h | exact @UpperTheory.Reformulated.B.Qh20.hfs_aeval_restrict L W ‹_› ‹_› ‹_› f p | exact @UpperTheory.Reformulated.B.Qh20.hfs_aeval_restrict L W ‹_› ‹_› ‹_› f | exact @UpperTheory.Reformulated.B.Qh20.hfs_aeval_restrict L W ‹_› ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qh20.hfs_aeval_restrict L W ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qh20.hfs_aeval_restrict L W ‹_› | exact @UpperTheory.Reformulated.B.Qh20.hfs_aeval_restrict L W | exact @UpperTheory.Reformulated.B.Qh20.hfs_aeval_restrict L

/- English proof (translation)
It suffices to establish `H : ∀ n, ∀ (W : Type) [AddCommGroup W] [Module L W] [FiniteDimensional L W] (f : Module.End L W), (minpoly L f).Splits → finrank L W = n → ⨆ μ, f.maxGenEigenspace μ = ⊤ from H _ W f hs rfl`. Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `h n ih`. Introduce `W _ _ _ f hs h_dim`.

Break down `n with - | n` into its components or cases. Rewrite using `[← top_le_iff]`. Simplify using `only [Submodule.finrank_eq_zero.1 (Eq.trans (finrank_top _ _) h_dim), bot_le]`. Establish `: Nontrivial W` using `finrank_pos_iff.1 (by rw [h_dim]; exact Nat.zero_lt_succ _)`. Establish `hint : IsIntegral L f` using `Algebra.IsIntegral.isIntegral f`.

Choose the witnesses or unpack the hypotheses as in `⟨μ₀, hμ₀⟩ : ∃ μ₀, f.HasEigenvalue μ₀ := by`. Establish `hd : (minpoly L f).degree ≠ 0`. Rewrite using `[degree_eq_natDegree (minpoly.ne_zero hint)]`. Conclude with `(minpoly.natDegree_pos hint).ne'` after adjusting the coercions. Take `⟨μ, hμ⟩` from `hs.exists_eval_eq_zero hd`.

Conclude with `⟨μ, Module.End.hasEigenvalue_of_isRoot hμ⟩`. Set `ES` to `f.genEigenspace μ₀ (finrank L W)`. Set `ER` to `f.genEigenrange μ₀ (finrank L W)`. Establish `h_f_ER : ∀ x : W, x ∈ ER → f x ∈ ER` using `fun x hx => map_genEigenrange_le (Submodule.mem_map_of_mem hx)`. Set `f' : Module.End L ER` to `f.restrict h_f_ER`.

Establish `hs' : (minpoly L f').Splits`. Use `hs.of_dvd (minpoly.ne_zero hint) (minpoly.dvd L f' ?_)` and prove the remaining obligations. Use extensionality with `x`. Rewrite using `[hfs_aeval_restrict f h_f_ER, minpoly.aeval]`. Both sides reduce to the same expression.

Establish `h_dim_ES_pos : 0 < finrank L ES` using `by dsimp +instances only [ES]`. Rewrite using `[h_dim]`. Apply `pos_finrank_genEigenspace_of_hasEigenvalue hμ₀ (Nat.zero_lt_succ n)` to reduce the goal to its premises. Establish `h_dim_add : finrank L ER + finrank L ES = finrank L W` using `by dsimp +instances only [ER, ES]`. Rewrite using `[Module.End.genEigenspace_nat, Module.End.genEigenrange_nat]`.

Apply `LinearMap.finrank_range_add_finrank_ker` to reduce the goal to its premises. Establish `h_dim_ER : finrank L ER < n.succ` using `by omega`. Establish `ih_ER : ⨆ (μ : L), f'.maxGenEigenspace μ = ⊤` using `ih (finrank L ER) h_dim_ER ER f' hs' rfl`. Establish `ih_ER' : ⨆ (μ : L), (f'.maxGenEigenspace μ).map ER.subtype = ER`. Simplify using `only [(Submodule.map_iSup _ _).symm, ih_ER, Submodule.map_subtype_top ER]`.

Establish `hff' : ∀ μ, (f'.maxGenEigenspace μ).map ER.subtype ≤ f.maxGenEigenspace μ`. Use `intros`. Rewrite using `[maxGenEigenspace, genEigenspace_restrict]`. Apply `Submodule.map_comap_le` to reduce the goal to its premises. Establish `hER : ER ≤ ⨆ (μ : L), f.maxGenEigenspace μ`.

Rewrite using `[← ih_ER']`. Conclude with `iSup_mono hff'`. Establish `hES : ES ≤ ⨆ (μ : L), f.maxGenEigenspace μ` using `((f.genEigenspace μ₀).mono le_top).trans (le_iSup f.maxGenEigenspace μ₀)`. Establish `h_disjoint : Disjoint ER ES` using `generalized_eigenvec_disjoint_range_ker f μ₀`. Express the relevant statement in the definitionally equal form `⨆ (μ : L), f.maxGenEigenspace μ = ⊤`.

Rewrite using `[← top_le_iff, ← Submodule.eq_top_of_disjoint ER ES h_dim_add.ge h_disjoint]`. Apply `sup_le hER hES` to reduce the goal to its premises.
-/
theorem hfs_iSup_maxGen_of_splits [FiniteDimensional L W] (f : Module.End L W) (hs : (minpoly L f).Splits) :
    ⨆ μ, f.maxGenEigenspace μ = ⊤ := by
  suffices H : ∀ n, ∀ (W : Type) [AddCommGroup W] [Module L W] [FiniteDimensional L W] (f : Module.End L W),
      (minpoly L f).Splits → finrank L W = n → ⨆ μ, f.maxGenEigenspace μ = ⊤ from H _ W f hs rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
  intro W _ _ _ f hs h_dim
  rcases n with - | n
  · rw [← top_le_iff]
    simp only [Submodule.finrank_eq_zero.1 (Eq.trans (finrank_top _ _) h_dim), bot_le]
  · have : Nontrivial W := finrank_pos_iff.1 (by rw [h_dim]; exact Nat.zero_lt_succ _)
    have hint : IsIntegral L f := Algebra.IsIntegral.isIntegral f
    obtain ⟨μ₀, hμ₀⟩ : ∃ μ₀, f.HasEigenvalue μ₀ := by
      have hd : (minpoly L f).degree ≠ 0 := by
        rw [degree_eq_natDegree (minpoly.ne_zero hint)]
        exact_mod_cast (minpoly.natDegree_pos hint).ne'
      obtain ⟨μ, hμ⟩ := hs.exists_eval_eq_zero hd
      exact ⟨μ, Module.End.hasEigenvalue_of_isRoot hμ⟩
    let ES := f.genEigenspace μ₀ (finrank L W)
    let ER := f.genEigenrange μ₀ (finrank L W)
    have h_f_ER : ∀ x : W, x ∈ ER → f x ∈ ER := fun x hx =>
      map_genEigenrange_le (Submodule.mem_map_of_mem hx)
    let f' : Module.End L ER := f.restrict h_f_ER
    have hs' : (minpoly L f').Splits := by
      refine hs.of_dvd (minpoly.ne_zero hint) (minpoly.dvd L f' ?_)
      ext x
      rw [hfs_aeval_restrict f h_f_ER, minpoly.aeval]
      rfl
    have h_dim_ES_pos : 0 < finrank L ES := by
      dsimp +instances only [ES]
      rw [h_dim]
      apply pos_finrank_genEigenspace_of_hasEigenvalue hμ₀ (Nat.zero_lt_succ n)
    have h_dim_add : finrank L ER + finrank L ES = finrank L W := by
      dsimp +instances only [ER, ES]
      rw [Module.End.genEigenspace_nat, Module.End.genEigenrange_nat]
      apply LinearMap.finrank_range_add_finrank_ker
    have h_dim_ER : finrank L ER < n.succ := by omega
    have ih_ER : ⨆ (μ : L), f'.maxGenEigenspace μ = ⊤ := ih (finrank L ER) h_dim_ER ER f' hs' rfl
    have ih_ER' : ⨆ (μ : L), (f'.maxGenEigenspace μ).map ER.subtype = ER := by
      simp only [(Submodule.map_iSup _ _).symm, ih_ER, Submodule.map_subtype_top ER]
    have hff' : ∀ μ, (f'.maxGenEigenspace μ).map ER.subtype ≤ f.maxGenEigenspace μ := by
      intros
      rw [maxGenEigenspace, genEigenspace_restrict]
      apply Submodule.map_comap_le
    have hER : ER ≤ ⨆ (μ : L), f.maxGenEigenspace μ := by
      rw [← ih_ER']
      exact iSup_mono hff'
    have hES : ES ≤ ⨆ (μ : L), f.maxGenEigenspace μ :=
      ((f.genEigenspace μ₀).mono le_top).trans (le_iSup f.maxGenEigenspace μ₀)
    have h_disjoint : Disjoint ER ES := generalized_eigenvec_disjoint_range_ker f μ₀
    change ⨆ (μ : L), f.maxGenEigenspace μ = ⊤
    rw [← top_le_iff, ← Submodule.eq_top_of_disjoint ER ES h_dim_add.ge h_disjoint]
    apply sup_le hER hES

/- English proof (translation)
Rewrite `hg`, `hh`, the goal using `[Module.End.mem_maxGenEigenspace]`. Take `⟨k, hk⟩` from `hg`. Take `⟨l, hl⟩` from `hh`. Establish `hNM : Commute (g - a • (1 : Module.End L W)) (h - b • (1 : Module.End L W))` using `(hgh.sub_right ((Commute.one_right g).smul_right b)).sub_left (((Commute.one_left _).smul_left a))`. Use `⟨k + l, ?_⟩` and prove the remaining obligations.

Establish `e : g + h - (a + b) • (1 : Module.End L W) = (g - a • (1 : Module.End L W)) + (h - b • (1 : Module.End L W))`. Rewrite using `[add_smul]`. Normalize the expressions using the abelian group laws. Rewrite using `[e, hNM.add_pow, LinearMap.sum_apply]`. Use `Finset.sum_eq_zero fun m _ => ?_` and prove the remaining obligations.

Rewrite using `[Module.End.mul_apply, Module.End.natCast_apply, map_nsmul]`. Use `(congrArg _ ?_).trans (nsmul_zero _)` and prove the remaining obligations. Distinguish the cases in `hmk : k ≤ m`. Establish `h0 : ((g - a • (1 : Module.End L W)) ^ m) v = 0`. Rewrite using `[← Nat.sub_add_cancel hmk, pow_add, Module.End.mul_apply, hk, map_zero]`.

Rewrite using `[(hNM.pow_pow m (k + l - m)).eq, Module.End.mul_apply, h0, map_zero]`. Establish `h0 : ((h - b • (1 : Module.End L W)) ^ (k + l - m)) v = 0`. Rewrite using `[← Nat.sub_add_cancel (show l ≤ k + l - m by omega), pow_add, Module.End.mul_apply, hl, map_zero]`. Rewrite using `[Module.End.mul_apply, h0, map_zero]`.
-/
theorem hfs_mem_maxGen_add {g h : Module.End L W} (hgh : Commute g h) {a b : L} {v : W}
    (hg : v ∈ g.maxGenEigenspace a) (hh : v ∈ h.maxGenEigenspace b) : v ∈ (g + h).maxGenEigenspace (a + b) := by
  rw [Module.End.mem_maxGenEigenspace] at hg hh ⊢
  obtain ⟨k, hk⟩ := hg
  obtain ⟨l, hl⟩ := hh
  have hNM : Commute (g - a • (1 : Module.End L W)) (h - b • (1 : Module.End L W)) :=
    (hgh.sub_right ((Commute.one_right g).smul_right b)).sub_left (((Commute.one_left _).smul_left a))
  refine ⟨k + l, ?_⟩
  have e : g + h - (a + b) • (1 : Module.End L W) = (g - a • (1 : Module.End L W)) + (h - b • (1 : Module.End L W)) := by
    rw [add_smul]; abel
  rw [e, hNM.add_pow, LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun m _ => ?_
  rw [Module.End.mul_apply, Module.End.natCast_apply, map_nsmul]
  refine (congrArg _ ?_).trans (nsmul_zero _)
  by_cases hmk : k ≤ m
  · have h0 : ((g - a • (1 : Module.End L W)) ^ m) v = 0 := by
      rw [← Nat.sub_add_cancel hmk, pow_add, Module.End.mul_apply, hk, map_zero]
    rw [(hNM.pow_pow m (k + l - m)).eq, Module.End.mul_apply, h0, map_zero]
  · have h0 : ((h - b • (1 : Module.End L W)) ^ (k + l - m)) v = 0 := by
      rw [← Nat.sub_add_cancel (show l ≤ k + l - m by omega), pow_add, Module.End.mul_apply, hl, map_zero]
    rw [Module.End.mul_apply, h0, map_zero]

/- English proof (translation)
Rewrite `hg`, the goal using `[Module.End.mem_maxGenEigenspace]`. Take `⟨k, hk⟩` from `hg`. Use `⟨k, ?_⟩` and prove the remaining obligations. Establish `e : c • g - (c * a) • (1 : Module.End L W) = c • (g - a • (1 : Module.End L W))`. Rewrite using `[smul_sub, mul_smul]`.

Rewrite using `[e, _root_.smul_pow, LinearMap.smul_apply, hk, smul_zero]`.
-/
theorem hfs_mem_maxGen_smul {g : Module.End L W} (c a : L) {v : W} (hg : v ∈ g.maxGenEigenspace a) :
    v ∈ (c • g).maxGenEigenspace (c * a) := by
  rw [Module.End.mem_maxGenEigenspace] at hg ⊢
  obtain ⟨k, hk⟩ := hg
  refine ⟨k, ?_⟩
  have e : c • g - (c * a) • (1 : Module.End L W) = c • (g - a • (1 : Module.End L W)) := by
    rw [smul_sub, mul_smul]
  rw [e, _root_.smul_pow, LinearMap.smul_apply, hk, smul_zero]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Rewrite using `[Finset.sum_empty, Finset.sum_empty, Module.End.mem_maxGenEigenspace]`. Conclude with `⟨1, by simp⟩`. Consider the case `insert a s ha ih`.

Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha]`. Establish `hcs : ∀ i ∈ s, ∀ j ∈ s, Commute (F i) (F j)` using `fun i hi j hj => hc i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj)`. Use `hfs_mem_maxGen_add ?_ (hfs_mem_maxGen_smul _ _ (hv a (Finset.mem_insert_self a s))) (ih hcs fun i hi => hv i (Finset.mem_insert_of_mem hi))` and prove the remaining obligations. Conclude with `Commute.smul_left (Commute.sum_right _ _ _ fun j hj => (hc a (Finset.mem_insert_self a s) j (Finset.mem_insert_of_mem hj)).smul_right _) _`.
-/
theorem hfs_mem_maxGen_sum {ι : Type} (s : Finset ι) (F : ι → Module.End L W) (c χ : ι → L)
    (hc : ∀ i ∈ s, ∀ j ∈ s, Commute (F i) (F j)) {v : W} (hv : ∀ i ∈ s, v ∈ (F i).maxGenEigenspace (χ i)) :
    v ∈ (∑ i ∈ s, c i • F i).maxGenEigenspace (∑ i ∈ s, c i * χ i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, Module.End.mem_maxGenEigenspace]
    exact ⟨1, by simp⟩
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hcs : ∀ i ∈ s, ∀ j ∈ s, Commute (F i) (F j) := fun i hi j hj =>
      hc i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj)
    refine hfs_mem_maxGen_add ?_ (hfs_mem_maxGen_smul _ _ (hv a (Finset.mem_insert_self a s)))
      (ih hcs fun i hi => hv i (Finset.mem_insert_of_mem hi))
    exact Commute.smul_left (Commute.sum_right _ _ _ fun j hj =>
      (hc a (Finset.mem_insert_self a s) j (Finset.mem_insert_of_mem hj)).smul_right _) _

/- English proof (translation)
Establish `htop` using `Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute (fun x : s => F x) (fun x y _ => hc x x.2 y y.2) (fun x => hs x x.2)`. Rewrite using `[eq_top_iff, ← htop]`. Use `iSup_le fun χ => le_trans ?_ (le_iSup _ (∑ x : s, c x * χ x))` and prove the remaining obligations. Introduce `v hv`. Establish `hv' : ∀ x : s, v ∈ (F x).maxGenEigenspace (χ x)` using `fun x => (Submodule.mem_iInf _).1 hv x`.

Rewrite using `[← Finset.sum_coe_sort s (fun i => c i • F i)]`. Conclude with `hfs_mem_maxGen_sum Finset.univ (fun x : s => F x) (fun x => c x) χ (fun x _ y _ => hc x x.2 y y.2) (fun x _ => hv' x)`.
-/
theorem hfs_iSup_maxGen_sum [FiniteDimensional L W] {ι : Type} (s : Finset ι) (F : ι → Module.End L W) (c : ι → L)
    (hc : ∀ i ∈ s, ∀ j ∈ s, Commute (F i) (F j)) (hs : ∀ i ∈ s, ⨆ μ, (F i).maxGenEigenspace μ = ⊤) :
    ⨆ μ, (∑ i ∈ s, c i • F i).maxGenEigenspace μ = ⊤ := by
  have htop := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
    (fun x : s => F x) (fun x y _ => hc x x.2 y y.2) (fun x => hs x x.2)
  rw [eq_top_iff, ← htop]
  refine iSup_le fun χ => le_trans ?_ (le_iSup _ (∑ x : s, c x * χ x))
  intro v hv
  have hv' : ∀ x : s, v ∈ (F x).maxGenEigenspace (χ x) := fun x => (Submodule.mem_iInf _).1 hv x
  rw [← Finset.sum_coe_sort s (fun i => c i • F i)]
  exact hfs_mem_maxGen_sum Finset.univ (fun x : s => F x) (fun x => c x) χ (fun x _ y _ => hc x x.2 y y.2)
    (fun x _ => hv' x)

end HfsSplit

section Frame

variable {K L : Type} [Field K] [Field L] (ι : K →+* L)

structure CoefFrame where

  r : ℕ

  e : Fin r → L

  c : L →+ (Fin r → K)

  spec : ∀ y, y = ∑ k, ι (c y k) * e k

  smul : ∀ (a : K) (y : L), c (ι a * y) = a • c y

/- English proof (translation)
Set `_ : Algebra K L` to `ι.toAlgebra`. Use `haveI : IsScalarTower ℚ K L := IsScalarTower.of_algebraMap_eq fun q => by`. Rewrite using `[RingHom.algebraMap_toAlgebra, eq_ratCast (algebraMap ℚ L) q, eq_ratCast (algebraMap ℚ K) q, map_ratCast]`. Use `haveI : Module.Finite K L := Module.Finite.of_restrictScalars_finite ℚ K L`. Set `b` to `Module.finBasis K L`.

Use `⟨⟨Module.finrank K L, b, (b.equivFun.toLinearMap : L →ₗ[K] (Fin _ → K)).toAddMonoidHom, fun y => ?_, fun a y => ?_⟩⟩` and prove the remaining obligations. Use `conv_lhs => rw [← b.sum_equivFun y]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, RingHom.algebraMap_toAlgebra]`. Both sides reduce to the same expression.

Express the relevant statement in the definitionally equal form `b.equivFun (ι a * y) = a • b.equivFun y`. Rewrite using `[← map_smul, Algebra.smul_def, RingHom.algebraMap_toAlgebra]`.
-/
theorem CoefFrame.nonempty [NumberField K] [NumberField L] : Nonempty (CoefFrame ι) := by
  let _ : Algebra K L := ι.toAlgebra
  haveI : IsScalarTower ℚ K L := IsScalarTower.of_algebraMap_eq fun q => by
    rw [RingHom.algebraMap_toAlgebra, eq_ratCast (algebraMap ℚ L) q, eq_ratCast (algebraMap ℚ K) q, map_ratCast]
  haveI : Module.Finite K L := Module.Finite.of_restrictScalars_finite ℚ K L
  let b := Module.finBasis K L
  refine ⟨⟨Module.finrank K L, b, (b.equivFun.toLinearMap : L →ₗ[K] (Fin _ → K)).toAddMonoidHom, fun y => ?_,
    fun a y => ?_⟩⟩
  · conv_lhs => rw [← b.sum_equivFun y]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
    rfl
  · change b.equivFun (ι a * y) = a • b.equivFun y
    rw [← map_smul, Algebra.smul_def, RingHom.algebraMap_toAlgebra]

end Frame

section BC

variable {K L : Type} [Field K] [NumberField K] [StarRing K] [Field L] [NumberField L] [StarRing L] (ι : K →+* L)

structure GSDBC (S : GSD K) (S' : GSD L) where

  eG : S'.G →* S.G
  eG_surj : Function.Surjective eG

  eD : S'.D ≃ S.D
  eD_smul : ∀ (g : S'.G) (d : S'.D), eD (g • d) = eG g • eD d

  j : S.V →+ S'.V
  j_smul : ∀ (a : K) (v : S.V), j (a • v) = ι a • j v

  li : LinearIndependent L fun i => j (S.bV i)

  sp : ⊤ ≤ Submodule.span L (Set.range fun i => j (S.bV i))

  rho : ∀ (g : S'.G) (v : S.V), S'.ρ g (j v) = j (S.ρ (eG g) v)

namespace GSDBC

variable {ι} {S : GSD K} {S' : GSD L} (b : GSDBC ι S S')

/- English proof (translation)
Rewrite using `[map_sum]`. Conclude with `Finset.sum_congr rfl fun x _ => b.j_smul _ _`.
-/
theorem j_sum {α : Type} (s : Finset α) (a : α → K) (v : α → S.V) :
    b.j (∑ x ∈ s, a x • v x) = ∑ x ∈ s, ι (a x) • b.j (v x) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun x _ => b.j_smul _ _

def bas : Basis S.ιV L S'.V := Basis.mk b.li b.sp

/- English proof (translation)
The claim follows from `Basis.mk_apply _ _ _`.
-/
theorem bas_apply (i : S.ιV) : b.bas i = b.j (S.bV i) := Basis.mk_apply _ _ _

/- English proof (translation)
Use `conv_lhs => rw [← S.bV.sum_repr v]`. Rewrite using `[b.j_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [b.bas_apply]`.
-/
theorem j_eq (v : S.V) : b.j v = ∑ i, ι (S.bV.repr v i) • b.bas i := by
  conv_lhs => rw [← S.bV.sum_repr v]
  rw [b.j_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [b.bas_apply]

/- English proof (translation)
Rewrite using `[b.j_eq, ← b.bas.equivFun_symm_apply, ← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]`.
-/
theorem repr_j (v : S.V) (i : S.ιV) : b.bas.repr (b.j v) i = ι (S.bV.repr v i) := by
  rw [b.j_eq, ← b.bas.equivFun_symm_apply, ← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]

def lift (φ : S.EqFun) : S'.EqFun :=
  ⟨fun d' => b.j ((φ : S.D → S.V) (b.eD d')), by
    intro g d
    show b.j ((φ : S.D → S.V) (b.eD (g • d))) = S'.ρ g (b.j ((φ : S.D → S.V) (b.eD d)))
    rw [b.eD_smul, φ.2 (b.eG g), b.rho]⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem lift_apply (φ : S.EqFun) (d' : S'.D) :
    ((b.lift φ : S'.EqFun) : S'.D → S'.V) d' = b.j ((φ : S.D → S.V) (b.eD d')) :=
  rfl

/- English proof (translation)
The claim follows from `Subtype.ext (funext fun d' => by simp only [lift_apply, Submodule.coe_add, Pi.add_apply, map_add])`.
-/
theorem lift_add (φ ψ : S.EqFun) : b.lift (φ + ψ) = b.lift φ + b.lift ψ :=
  Subtype.ext (funext fun d' => by simp only [lift_apply, Submodule.coe_add, Pi.add_apply, map_add])

/- English proof (translation)
The claim follows from `Subtype.ext (funext fun d' => by simp only [lift_apply, Submodule.coe_smul, Pi.smul_apply, b.j_smul])`.
-/
theorem lift_smul (a : K) (φ : S.EqFun) : b.lift (a • φ) = ι a • b.lift φ :=
  Subtype.ext (funext fun d' => by simp only [lift_apply, Submodule.coe_smul, Pi.smul_apply, b.j_smul])

/- English proof (translation)
The claim follows from `Subtype.ext (funext fun d' => by simp only [lift_apply, Submodule.coe_zero, Pi.zero_apply, map_zero])`.
-/
theorem lift_zero : b.lift 0 = 0 :=
  Subtype.ext (funext fun d' => by simp only [lift_apply, Submodule.coe_zero, Pi.zero_apply, map_zero])

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp only [Finset.sum_empty, b.lift_zero]`. Consider the case `insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, b.lift_add, b.lift_smul, ih]`.
-/
theorem lift_sum {α : Type} (s : Finset α) (a : α → K) (φ : α → S.EqFun) :
    b.lift (∑ x ∈ s, a x • φ x) = ∑ x ∈ s, ι (a x) • b.lift (φ x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, b.lift_zero]
  | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, b.lift_add, b.lift_smul, ih]

section Span

variable (F : CoefFrame ι)

def coord (k : Fin F.r) (x : S'.V) : S.V := ∑ i, (F.c (b.bas.repr x i) k) • S.bV i

/- English proof (translation)
Rewrite using `[coord, ← S.bV.equivFun_symm_apply, ← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]`.
-/
theorem repr_coord (k : Fin F.r) (x : S'.V) (l : S.ιV) : S.bV.repr (b.coord F k x) l = F.c (b.bas.repr x l) k := by
  rw [coord, ← S.bV.equivFun_symm_apply, ← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]

/- English proof (translation)
Establish `h1 : ∀ k, b.j (b.coord F k x) = ∑ i, ι (F.c (b.bas.repr x i) k) • b.bas i` using `fun k => by`. Rewrite using `[coord, b.j_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [b.bas_apply]`. Simplify using `only [h1, Finset.smul_sum, smul_smul]`. Rewrite using `[Finset.sum_comm]`.

Use `conv_rhs => rw [← b.bas.sum_repr x]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_smul]`. Use `congr 1`. Use `conv_rhs => rw [F.spec (b.bas.repr x i)]`.

Conclude with `Finset.sum_congr rfl fun k _ => mul_comm _ _`.
-/
theorem sum_coord (x : S'.V) : ∑ k, F.e k • b.j (b.coord F k x) = x := by
  have h1 : ∀ k, b.j (b.coord F k x) = ∑ i, ι (F.c (b.bas.repr x i) k) • b.bas i := fun k => by
    rw [coord, b.j_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [b.bas_apply]
  simp only [h1, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  conv_rhs => rw [← b.bas.sum_repr x]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  conv_rhs => rw [F.spec (b.bas.repr x i)]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/- English proof (translation)
Use `conv_lhs => rw [← b.bas.sum_repr x]`. Rewrite using `[map_sum, map_sum, Finsupp.finset_sum_apply]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, b.bas_apply, b.rho, map_smul, Finsupp.smul_apply, b.repr_j, smul_eq_mul]`.
-/
theorem repr_rho (g : S'.G) (x : S'.V) (l : S.ιV) :
    b.bas.repr (S'.ρ g x) l = ∑ i, b.bas.repr x i * ι (S.bV.repr (S.ρ (b.eG g) (S.bV i)) l) := by
  conv_lhs => rw [← b.bas.sum_repr x]
  rw [map_sum, map_sum, Finsupp.finset_sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, b.bas_apply, b.rho, map_smul, Finsupp.smul_apply, b.repr_j, smul_eq_mul]

/- English proof (translation)
Use `S.bV.ext_elem fun l => ?_` and prove the remaining obligations. Rewrite using `[repr_coord, repr_rho, map_sum]`. Establish `h2 : S.ρ (b.eG g) (b.coord F k x) = ∑ i, (F.c (b.bas.repr x i) k) • S.ρ (b.eG g) (S.bV i)`. Rewrite using `[coord, map_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => map_smul _ _ _`.

Rewrite using `[h2, map_sum, Finsupp.finset_sum_apply]`. Simplify using `only [Finset.sum_apply, map_smul, Finsupp.smul_apply, smul_eq_mul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm, F.smul, Pi.smul_apply, smul_eq_mul, mul_comm]`.
-/
theorem coord_rho (k : Fin F.r) (g : S'.G) (x : S'.V) :
    b.coord F k (S'.ρ g x) = S.ρ (b.eG g) (b.coord F k x) := by
  refine S.bV.ext_elem fun l => ?_
  rw [repr_coord, repr_rho, map_sum]
  have h2 : S.ρ (b.eG g) (b.coord F k x) = ∑ i, (F.c (b.bas.repr x i) k) • S.ρ (b.eG g) (S.bV i) := by
    rw [coord, map_sum]
    exact Finset.sum_congr rfl fun i _ => map_smul _ _ _
  rw [h2, map_sum, Finsupp.finset_sum_apply]
  simp only [Finset.sum_apply, map_smul, Finsupp.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm, F.smul, Pi.smul_apply, smul_eq_mul, mul_comm]

def coordForm (k : Fin F.r) (φ : S'.EqFun) : S.EqFun :=
  ⟨fun d => b.coord F k ((φ : S'.D → S'.V) (b.eD.symm d)), by
    intro g d
    obtain ⟨g', rfl⟩ := b.eG_surj g
    have h : b.eD.symm (b.eG g' • d) = g' • b.eD.symm d := by
      apply b.eD.injective
      rw [Equiv.apply_symm_apply, b.eD_smul, Equiv.apply_symm_apply]
    show b.coord F k ((φ : S'.D → S'.V) (b.eD.symm (b.eG g' • d))) = S.ρ (b.eG g') (b.coord F k ((φ : S'.D → S'.V) (b.eD.symm d)))
    rw [h, φ.2 g', b.coord_rho]⟩

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `d'`. Rewrite using `[Submodule.coe_sum, Finset.sum_apply]`. Simplify using `only [Submodule.coe_smul, Pi.smul_apply, lift_apply]`. Use `show ∑ k, F.e k • b.j (b.coord F k ((φ : S'.D → S'.V) (b.eD.symm (b.eD d')))) = _`.

Rewrite using `[Equiv.symm_apply_apply, b.sum_coord]`.
-/
theorem sum_lift_coordForm (φ : S'.EqFun) : ∑ k, F.e k • b.lift (b.coordForm F k φ) = φ := by
  apply Subtype.ext
  funext d'
  rw [Submodule.coe_sum, Finset.sum_apply]
  simp only [Submodule.coe_smul, Pi.smul_apply, lift_apply]
  show ∑ k, F.e k • b.j (b.coord F k ((φ : S'.D → S'.V) (b.eD.symm (b.eD d')))) = _
  rw [Equiv.symm_apply_apply, b.sum_coord]

include F in

/- English proof (translation)
Rewrite using `[← b.sum_lift_coordForm F φ]`. Conclude with `Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)`.
-/
theorem mem_span_lift (φ : S'.EqFun) : φ ∈ Submodule.span L (Set.range b.lift) := by
  rw [← b.sum_lift_coordForm F φ]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

end Span

end GSDBC

end BC

end Formalism.L2.Col
