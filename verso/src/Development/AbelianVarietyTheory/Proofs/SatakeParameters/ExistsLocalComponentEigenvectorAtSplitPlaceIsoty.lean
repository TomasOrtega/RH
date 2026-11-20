import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsotypicPartSpannedBySplitPlaceLocalComponentStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup

noncomputable section

namespace GlobalTheory.LocVec

open scoped BigOperators

section Algebra

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

def stabSub (π : Representation ℂ G V) (w : V) : Subgroup G where
  carrier := {g | π g w = w}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at *
    rw [map_mul, Module.End.mul_apply, hb, ha]
  one_mem' := by simp
  inv_mem' {a} ha := by
    simp only [Set.mem_setOf_eq] at *
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

/- English proof (translation)
Use `haveI : Fintype (G ⧸ H) := H.fintypeQuotientOfFiniteIndex`. Set `F : V → G → V` to `fun w x => ((θ x : ℂˣ) : ℂ)⁻¹ • π x w`. Establish `hFg : ∀ w g x, π g (F w x) = ((θ g : ℂˣ) : ℂ) • F w (g * x)`. Introduce `w g x`. Simplify using `only [F, map_smul, map_mul, Module.End.mul_apply, Units.val_mul, mul_inv, smul_smul]`.

Use `congr 1`. Establish `: ((θ g : ℂˣ) : ℂ) ≠ 0` using `Units.ne_zero _`. Clear the denominators using the available nonvanishing facts. Establish `hFH : ∀ i ∈ s, ∀ x y : G, (x : G ⧸ H) = y → F (u i) x = F (u i) y`. Introduce `i hi x y hxy`.

Establish `hm : x⁻¹ * y ∈ H` using `QuotientGroup.eq.1 hxy`. Take `⟨h, hh, rfl⟩ : ∃ h ∈ H, y = x * h` from `⟨x⁻¹ * y, hm, by group⟩`. Establish `hθh : θ h = 1` using `hHθ hh`. Simplify using `only [F, map_mul, Module.End.mul_apply, hu i hi h hh, hθh, mul_one]`. Set `e : V → V` to `fun w => ∑ q : G ⧸ H, F w q.out`.

Establish `heig : ∀ i ∈ s, ∀ g, π g (e (u i)) = ((θ g : ℂˣ) : ℂ) • e (u i)`. Introduce `i hi g`. Simplify using `only [e, map_sum, hFg, ← Finset.smul_sum]`. Use `congr 1`. Use `Fintype.sum_equiv (MulAction.toPerm g) _ _ fun q => ?_` and prove the remaining obligations.

Apply `hFH i hi` to reduce the goal to its premises. Rewrite using `[MulAction.toPerm_apply, QuotientGroup.out_eq']`. Use `conv_rhs => rw [← QuotientGroup.out_eq' q]`. Both sides reduce to the same expression. Establish `htot : ∑ i ∈ s, T i (e (u i)) = (Fintype.card (G ⧸ H) : ℂ) • f`.

Simplify using `only [e, map_sum]`. Rewrite using `[Finset.sum_comm]`. Establish `: ∀ q : G ⧸ H, ∑ i ∈ s, T i (F (u i) q.out) = f`. Introduce `q`. Simplify using `only [F, map_smul, ← Finset.smul_sum, hf, smul_smul]`.

Rewrite using `[inv_mul_cancel₀ (Units.ne_zero _), one_smul]`. Simplify using `only [this, Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]`. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Establish `hz : ∀ i ∈ s, e (u i) = 0`.

Introduce `i hi`. Assume the negation of the conclusion as `h0`. Take `⟨g, hg⟩` from `hne _ h0`. Conclude with `hg (heig i hi g)`. Rewrite `htot` using `[Finset.sum_eq_zero (fun i hi => by rw [hz i hi, map_zero])]`.

Establish `hc : (Fintype.card (G ⧸ H) : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 Fintype.card_ne_zero`. Conclude with `hf0 ((smul_eq_zero.1 htot.symm).resolve_left hc)`.
-/
theorem exists_eigen_of_sum {M : Type} [AddCommGroup M] [Module ℂ M]
    (π : Representation ℂ G V) (θ : G →* ℂˣ) (H : Subgroup G) [H.FiniteIndex] (hHθ : H ≤ θ.ker)
    {ι : Type} (s : Finset ι) (u : ι → V) (hu : ∀ i ∈ s, ∀ h ∈ H, π h (u i) = u i)
    (T : ι → V →ₗ[ℂ] M) (f : M) (hf0 : f ≠ 0)
    (hf : ∀ g, ∑ i ∈ s, T i (π g (u i)) = ((θ g : ℂˣ) : ℂ) • f) :
    ∃ w : V, w ≠ 0 ∧ ∀ g, π g w = ((θ g : ℂˣ) : ℂ) • w := by
  classical
  haveI : Fintype (G ⧸ H) := H.fintypeQuotientOfFiniteIndex
  let F : V → G → V := fun w x => ((θ x : ℂˣ) : ℂ)⁻¹ • π x w
  have hFg : ∀ w g x, π g (F w x) = ((θ g : ℂˣ) : ℂ) • F w (g * x) := by
    intro w g x
    simp only [F, map_smul, map_mul, Module.End.mul_apply, Units.val_mul, mul_inv, smul_smul]
    congr 1
    have : ((θ g : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
    field_simp
  have hFH : ∀ i ∈ s, ∀ x y : G, (x : G ⧸ H) = y → F (u i) x = F (u i) y := by
    intro i hi x y hxy
    have hm : x⁻¹ * y ∈ H := QuotientGroup.eq.1 hxy
    obtain ⟨h, hh, rfl⟩ : ∃ h ∈ H, y = x * h := ⟨x⁻¹ * y, hm, by group⟩
    have hθh : θ h = 1 := hHθ hh
    simp only [F, map_mul, Module.End.mul_apply, hu i hi h hh, hθh, mul_one]
  let e : V → V := fun w => ∑ q : G ⧸ H, F w q.out
  have heig : ∀ i ∈ s, ∀ g, π g (e (u i)) = ((θ g : ℂˣ) : ℂ) • e (u i) := by
    intro i hi g
    simp only [e, map_sum, hFg, ← Finset.smul_sum]
    congr 1
    refine Fintype.sum_equiv (MulAction.toPerm g) _ _ fun q => ?_
    apply hFH i hi
    rw [MulAction.toPerm_apply, QuotientGroup.out_eq']
    conv_rhs => rw [← QuotientGroup.out_eq' q]
    rfl
  have htot : ∑ i ∈ s, T i (e (u i)) = (Fintype.card (G ⧸ H) : ℂ) • f := by
    simp only [e, map_sum]
    rw [Finset.sum_comm]
    have : ∀ q : G ⧸ H, ∑ i ∈ s, T i (F (u i) q.out) = f := by
      intro q
      simp only [F, map_smul, ← Finset.smul_sum, hf, smul_smul]
      rw [inv_mul_cancel₀ (Units.ne_zero _), one_smul]
    simp only [this, Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
  by_contra hne
  push_neg at hne
  have hz : ∀ i ∈ s, e (u i) = 0 := by
    intro i hi
    by_contra h0
    obtain ⟨g, hg⟩ := hne _ h0
    exact hg (heig i hi g)
  rw [Finset.sum_eq_zero (fun i hi => by rw [hz i hi, map_zero])] at htot
  have hc : (Fintype.card (G ⧸ H) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  exact hf0 ((smul_eq_zero.1 htot.symm).resolve_left hc)

end Algebra

section Topology

/- English proof (translation)
Take `⟨W, hWo, hWH⟩` from `isOpen_induced_iff.1 hH`. Establish `h1 : (1 : G) ∈ W`. Establish `: (1 : K) ∈ (H : Set K)` using `H.one_mem`. Rewrite `this` using `[← hWH]`. Conclude with `this`.

Take `⟨V, hV, hVW⟩` from `exists_nhds_split_inv (hWo.mem_nhds h1)`. Establish `hV' : V⁻¹ ∈ nhds (1 : G)` using `inv_mem_nhds_one G hV`. Establish `hint : (interior V⁻¹).Nonempty` using `⟨1, mem_interior_iff_mem_nhds.2 hV'⟩`. Take `⟨t, ht⟩` from `compact_covered_by_mul_left_translates hC hint`. Establish `key : ∀ g : G, ((QuotientGroup.mk : K → K ⧸ H) '' {k : K | g * (k : G) ∈ V⁻¹}).Subsingleton`.

Introduce and unpack `g _ ⟨k, hk, rfl⟩ _ ⟨k', hk', rfl⟩`. Apply `QuotientGroup.eq.2` to reduce the goal to its premises. Establish `hk1 : (g * (k : G))⁻¹ ∈ V` using `hk`. Establish `hk2 : (g * (k' : G))⁻¹ ∈ V` using `hk'`. Use `hVW _ hk1 _ hk2` as an intermediate fact.

Establish `hmem : ((k⁻¹ * k' : K) : G) ∈ W`. Use `this using 1` and compare the differences between its conclusion and the goal. Simplify using `only [Subgroup.coe_mul, Subgroup.coe_inv, div_eq_mul_inv, inv_inv, mul_inv_rev]`. Use `group`. Establish `: (k⁻¹ * k' : K) ∈ Subtype.val ⁻¹' W` using `hmem`.

Rewrite `this` using `[hWH]`. Conclude with `this`. Establish `hfin : (Set.univ : Set (K ⧸ H)).Finite`. Use `(t.finite_toSet.biUnion fun g _ => (key g).finite).subset ?_` and prove the remaining obligations. Introduce and unpack `q -`.

Take `⟨k, rfl⟩` from `QuotientGroup.mk_surjective q`. Choose the witnesses or unpack the hypotheses as in `⟨g, hg⟩ : ∃ g ∈ t, (k : G) ∈ (fun h => g * h) ⁻¹' V⁻¹ := by`. Simplify using `using ht (hKC k.2)`. Conclude with `Set.mem_biUnion hg.1 ⟨k, hg.2, rfl⟩`. Use `haveI : Finite (K ⧸ H) := Set.finite_univ_iff.1 hfin`.

Conclude with `Subgroup.finiteIndex_of_finite_quotient`.
-/
theorem finiteIndex_of_isOpen {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (K : Subgroup G) {C : Set G} (hC : IsCompact C) (hKC : (K : Set G) ⊆ C) (H : Subgroup K)
    (hH : IsOpen (H : Set K)) : H.FiniteIndex := by
  classical
  obtain ⟨W, hWo, hWH⟩ := isOpen_induced_iff.1 hH
  have h1 : (1 : G) ∈ W := by
    have : (1 : K) ∈ (H : Set K) := H.one_mem
    rw [← hWH] at this
    exact this
  obtain ⟨V, hV, hVW⟩ := exists_nhds_split_inv (hWo.mem_nhds h1)
  have hV' : V⁻¹ ∈ nhds (1 : G) := inv_mem_nhds_one G hV
  have hint : (interior V⁻¹).Nonempty := ⟨1, mem_interior_iff_mem_nhds.2 hV'⟩
  obtain ⟨t, ht⟩ := compact_covered_by_mul_left_translates hC hint
  have key : ∀ g : G, ((QuotientGroup.mk : K → K ⧸ H) '' {k : K | g * (k : G) ∈ V⁻¹}).Subsingleton := by
    rintro g _ ⟨k, hk, rfl⟩ _ ⟨k', hk', rfl⟩
    apply QuotientGroup.eq.2
    have hk1 : (g * (k : G))⁻¹ ∈ V := hk
    have hk2 : (g * (k' : G))⁻¹ ∈ V := hk'
    have := hVW _ hk1 _ hk2
    have hmem : ((k⁻¹ * k' : K) : G) ∈ W := by
      convert this using 1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, div_eq_mul_inv, inv_inv, mul_inv_rev]
      group
    have : (k⁻¹ * k' : K) ∈ Subtype.val ⁻¹' W := hmem
    rw [hWH] at this
    exact this
  have hfin : (Set.univ : Set (K ⧸ H)).Finite := by
    refine (t.finite_toSet.biUnion fun g _ => (key g).finite).subset ?_
    rintro q -
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨g, hg⟩ : ∃ g ∈ t, (k : G) ∈ (fun h => g * h) ⁻¹' V⁻¹ := by
      simpa using ht (hKC k.2)
    exact Set.mem_biUnion hg.1 ⟨k, hg.2, rfl⟩
  haveI : Finite (K ⧸ H) := Set.finite_univ_iff.1 hfin
  exact Subgroup.finiteIndex_of_finite_quotient

end Topology

end GlobalTheory.LocVec

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocVec

/- English proof (translation)
Introduce `L _ _ _ n a S hS s σ hσ c hc hci K θ hK hθ f hf hf0 hrt`. Establish `hmem` using `GlobalTheory.T.isotypicPart_spanned_by_splitPlace_localComponent L n a S hS s σ hσ c hc hci hf`. Rewrite `hmem` using `[iSup_subtype']`. Take `⟨φ, hφ, hsum⟩` from `(Submodule.mem_iSup_iff_exists_finsupp _ f).1 hmem`. Use `choose u hu using fun i => LinearMap.mem_range.1 (hφ i)`.

Set `m : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)) →* GL (Fin n) (s.w.adicCompletion L)` to `Matrix.GeneralLinearGroup.map c.toRingHom`. Establish `hm : Continuous m` using `Units.continuous_map (continuous_id.matrix_map hc)`. Set `π : Representation ℂ K σ.V` to `σ.ρ.comp (m.comp K.subtype)`. Establish `hπ : ∀ g : K, π g = σ.ρ (m g)` using `fun g => rfl`. Establish `hsumF : ∀ g : K, ∑ i ∈ φ.support, (i.1 : σ.V →ₗ[ℂ] _) (π g (u i)) = ((θ g : ℂˣ) : ℂ) • f`.

Introduce and unpack `⟨g, hg⟩`. Take `⟨κ, hκ, rfl⟩` from `GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s g`. Establish `: ∀ i ∈ φ.support, (i.1 : σ.V →ₗ[ℂ] _) (π ⟨s.loc n κ, hg⟩ (u i)) = NG.rt L n κ (φ i)`. Introduce `i _`. Rewrite using `[hπ, ← hu i]`.

Conclude with `i.2.2 κ hκ (u i)`. Rewrite using `[Finset.sum_congr rfl this, ← map_sum, ← hrt κ hκ hg]`. Rewrite using `[← hsum]`. Both sides reduce to the same expression. Set `H : Subgroup K` to `θ.ker ⊓ ⨅ i ∈ φ.support, stabSub π (u i)`.

Establish `hHo : IsOpen (H : Set K)`. Rewrite using `[Subgroup.coe_inf]`. Use `hθ.inter ?_` and prove the remaining obligations. Simplify using `only [Subgroup.coe_iInf]`. Use `isOpen_biInter_finset fun i _ => ?_` and prove the remaining obligations.

Establish `: (stabSub π (u i) : Set K) = (fun g : K => m g) ⁻¹' {x | σ.ρ x (u i) = u i}` using `rfl`. Rewrite using `[this]`. Conclude with `(σ.smooth (u i)).preimage (hm.comp continuous_subtype_val)`. Establish `hC : IsCompact (Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring : Set (GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))))`. Rewrite using `[(GlobalTheory.AdelicU.GLint_eq_KO_and_princ_eq_KOne s.v n).1]`.

Conclude with `GlobalTheory.SplitFlip.isCompact_KO`. Use `haveI : H.FiniteIndex := finiteIndex_of_isOpen K hC (fun g hg => hK g hg) H hHo`. Take `⟨w, hw0, hw⟩` from `exists_eigen_of_sum π θ H inf_le_left φ.support u (fun i hi h hh => by`. Use `(Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hh).2 i)` as an intermediate fact. Conclude with `(Subgroup.mem_iInf.1 this hi))`.

Use the proof step `(fun i => (i.1 : σ.V →ₗ[ℂ] _)) f hf0 hsumF`. Conclude with `⟨w, hw0, fun g hg => hw ⟨g, hg⟩⟩`.
-/
theorem main : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S : Submodule ℂ (GAf L n → a.W)), NG.IsIrrRep a.ρ S → ∀ (s : SplitPlace L) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))), IsLocS S s σ → ∀ c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L, Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → ∀ (K : Subgroup (GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)))) (θ : K →* ℂˣ), (∀ g ∈ K, g ∈ Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring) → IsOpen (θ.ker : Set K) → ∀ f ∈ NG.isoTyp a.ρ S, f ≠ 0 → (∀ κ, TrivOutside {s.v} κ → ∀ h : s.loc n κ ∈ K, NG.rt L n κ f = ((θ ⟨s.loc n κ, h⟩ : ℂˣ) : ℂ) • f) → ∃ u : σ.V, u ≠ 0 ∧ ∀ g (h : g ∈ K), σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom g) u = ((θ ⟨g, h⟩ : ℂˣ) : ℂ) • u := by
  intro L _ _ _ n a S hS s σ hσ c hc hci K θ hK hθ f hf hf0 hrt
  classical
  have hmem := GlobalTheory.T.isotypicPart_spanned_by_splitPlace_localComponent L n a S hS s σ hσ c hc hci hf
  rw [iSup_subtype'] at hmem
  obtain ⟨φ, hφ, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ f).1 hmem
  choose u hu using fun i => LinearMap.mem_range.1 (hφ i)
  let m : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)) →* GL (Fin n) (s.w.adicCompletion L) :=
    Matrix.GeneralLinearGroup.map c.toRingHom
  have hm : Continuous m := Units.continuous_map (continuous_id.matrix_map hc)
  let π : Representation ℂ K σ.V := σ.ρ.comp (m.comp K.subtype)
  have hπ : ∀ g : K, π g = σ.ρ (m g) := fun g => rfl
  have hsumF : ∀ g : K, ∑ i ∈ φ.support, (i.1 : σ.V →ₗ[ℂ] _) (π g (u i)) = ((θ g : ℂˣ) : ℂ) • f := by
    rintro ⟨g, hg⟩
    obtain ⟨κ, hκ, rfl⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s g
    have : ∀ i ∈ φ.support, (i.1 : σ.V →ₗ[ℂ] _) (π ⟨s.loc n κ, hg⟩ (u i)) = NG.rt L n κ (φ i) := by
      intro i _
      rw [hπ, ← hu i]
      exact i.2.2 κ hκ (u i)
    rw [Finset.sum_congr rfl this, ← map_sum, ← hrt κ hκ hg]
    rw [← hsum]
    rfl
  let H : Subgroup K := θ.ker ⊓ ⨅ i ∈ φ.support, stabSub π (u i)
  have hHo : IsOpen (H : Set K) := by
    rw [Subgroup.coe_inf]
    refine hθ.inter ?_
    simp only [Subgroup.coe_iInf]
    refine isOpen_biInter_finset fun i _ => ?_
    have : (stabSub π (u i) : Set K) = (fun g : K => m g) ⁻¹' {x | σ.ρ x (u i) = u i} := rfl
    rw [this]
    exact (σ.smooth (u i)).preimage (hm.comp continuous_subtype_val)
  have hC : IsCompact (Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring :
      Set (GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)))) := by
    rw [(GlobalTheory.AdelicU.GLint_eq_KO_and_princ_eq_KOne s.v n).1]
    exact GlobalTheory.SplitFlip.isCompact_KO
  haveI : H.FiniteIndex := finiteIndex_of_isOpen K hC (fun g hg => hK g hg) H hHo
  obtain ⟨w, hw0, hw⟩ := exists_eigen_of_sum π θ H inf_le_left φ.support u
    (fun i hi h hh => by
      have := (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hh).2 i)
      exact (Subgroup.mem_iInf.1 this hi))
    (fun i => (i.1 : σ.V →ₗ[ℂ] _)) f hf0 hsumF
  exact ⟨w, hw0, fun g hg => hw ⟨g, hg⟩⟩

end GlobalTheory.LocVec
