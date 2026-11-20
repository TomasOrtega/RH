import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.ExistsCharsAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PotentiallySemistableType
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TTypeVLoc

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi
open GlobalTheory.PRep GlobalTheory.TypeTwo.PowIrrProof
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped commutatorElement
namespace UpperTheory.V.Z.J.D.TypeVAux
/- English proof (translation)
Take `⟨B, hB⟩` from `GlobalTheory.TameInertiaChars.exists_basis_eigen (fun g => ρ g) hs fun g k => hc g k`. Use `choose d hd using hB`. Establish `hne : ∀ j, B j ≠ 0` using `fun j => B.ne_zero j`. Establish `canc : ∀ j {a b : ℂ}, a • B j = b • B j → a = b` using `fun j a b e => smul_left_injective ℂ (hne j) e`. Set `c : Fin n → Γ →* ℂ` to `fun j => { toFun := d j map_one' := canc j (by rw [← hd j 1, map_one, one_smul]; rfl) map_mul' := fun s t => canc j (by`.

Rewrite using `[← hd j (s * t), map_mul, Module.End.mul_apply, hd j t, map_smul, hd j s, smul_smul, mul_comm]) }`. Use `⟨fun j => (c j).toHomUnits, fun g => ?_, fun j g hg => ?_⟩` and prove the remaining obligations. Conclude with `GlobalTheory.TameInertiaChars.charpoly_of_basis _ B _ fun j => hd j g`. Use `Units.ext (canc j ?_) show d j g • B j = (1 : ℂ) • B j` and prove the remaining obligations. Rewrite using `[← hd j g, hg, one_smul]`.

Both sides reduce to the same expression.
-/
private theorem exists_chars {Γ : Type} [Group Γ] {n : ℕ} (ρ : Representation ℂ Γ (Fin n → ℂ))
    (hs : ∀ g, Module.End.IsSemisimple (ρ g)) (hc : ∀ s t, ρ s * ρ t = ρ t * ρ s) :
    ∃ η : Fin n → Γ →* ℂˣ, (∀ g, (ρ g).charpoly = ∏ j, (X - C (η j g : ℂ))) ∧
      ∀ j g, ρ g = 1 → η j g = 1 := by
  obtain ⟨B, hB⟩ := GlobalTheory.TameInertiaChars.exists_basis_eigen (fun g => ρ g) hs fun g k => hc g k
  choose d hd using hB
  have hne : ∀ j, B j ≠ 0 := fun j => B.ne_zero j
  have canc : ∀ j {a b : ℂ}, a • B j = b • B j → a = b := fun j a b e =>
    smul_left_injective ℂ (hne j) e
  let c : Fin n → Γ →* ℂ := fun j =>
    { toFun := d j
      map_one' := canc j (by rw [← hd j 1, map_one, one_smul]; rfl)
      map_mul' := fun s t => canc j (by
        rw [← hd j (s * t), map_mul, Module.End.mul_apply, hd j t, map_smul, hd j s, smul_smul, mul_comm]) }
  refine ⟨fun j => (c j).toHomUnits, fun g => ?_, fun j g hg => ?_⟩
  · exact GlobalTheory.TameInertiaChars.charpoly_of_basis _ B _ fun j => hd j g
  · refine Units.ext (canc j ?_)
    show d j g • B j = (1 : ℂ) • B j
    rw [← hd j g, hg, one_smul]
    rfl
/- English proof (translation)
Establish `key : ∀ ψ : H →* ℂ, Nonempty ({i // c i = ψ} ≃ {j // a j = ψ})` using `fun ψ => ⟨Fintype.equivOfCardEq (by`. Rewrite using `[Fintype.card_subtype, Fintype.card_subtype]`. Conclude with `(GlobalTheory.CommSemisimpleChars.card_eq_of_sum_eq a c h ψ).symm)⟩`. Set `E` to `Equiv.ofFiberEquiv (f := c) (g := a) fun ψ => (key ψ).some`. Conclude with `⟨E, fun i => Equiv.ofFiberEquiv_map _ i⟩`.
-/
private theorem exists_perm {H : Type} [Monoid H] {n : ℕ} (a c : Fin n → H →* ℂ)
    (h : ∀ g, ∑ j, a j g = ∑ i, c i g) : ∃ e : Equiv.Perm (Fin n), ∀ i, a (e i) = c i := by
  classical
  have key : ∀ ψ : H →* ℂ, Nonempty ({i // c i = ψ} ≃ {j // a j = ψ}) := fun ψ =>
    ⟨Fintype.equivOfCardEq (by
      rw [Fintype.card_subtype, Fintype.card_subtype]
      exact (GlobalTheory.CommSemisimpleChars.card_eq_of_sum_eq a c h ψ).symm)⟩
  let E := Equiv.ofFiberEquiv (f := c) (g := a) fun ψ => (key ψ).some
  exact ⟨E, fun i => Equiv.ofFiberEquiv_map _ i⟩
/- English proof (translation)
Establish `key : ∀ u : Fin n → ℂ, (∏ j, (X - C (u j)) : ℂ[X]).roots = Finset.univ.val.map u` using `fun u => by`. Rewrite using `[Finset.prod_eq_multiset_prod]`. Use `roots_multiset_prod_X_sub_C (Finset.univ.val.map u)` as an intermediate fact. Rewrite `this` using `[Multiset.map_map]`. Then use the resulting hypothesis. Conclude with `congrArg Multiset.sum (((key u).symm.trans (congrArg roots h)).trans (key v))`.
-/
private theorem sum_of_prod {n : ℕ} (u v : Fin n → ℂ) (h : ∏ j, (X - C (u j)) = ∏ j, (X - C (v j))) :
    ∑ j, u j = ∑ j, v j := by
  have key : ∀ u : Fin n → ℂ, (∏ j, (X - C (u j)) : ℂ[X]).roots = Finset.univ.val.map u := fun u => by
    rw [Finset.prod_eq_multiset_prod]
    have := roots_multiset_prod_X_sub_C (Finset.univ.val.map u)
    rwa [Multiset.map_map] at this
  exact congrArg Multiset.sum (((key u).symm.trans (congrArg roots h)).trans (key v))
end UpperTheory.V.Z.J.D.TypeVAux
set_option synthInstance.maxHeartbeats 200000 in
open UpperTheory.V.Z.J.D UpperTheory.V.Z.J.D.TypeVAux in
/- English proof (translation)
Introduce `P L Ω _ _ _ _ _ _ n hn π w A h τ hτ χ hχ rc hrc hT`. Take `⟨a, ha, ε, H⟩` from `hrc`. Establish `hart : a = artOf h`. Establish `ha' : IsLocalArtin h (artOf h)` using `Classical.epsilon_spec (p := IsLocalArtin h) ⟨a, ha⟩`. Take `⟨art, hart⟩` from `P.aut.art L Ω`.

Establish `hinj` using `GlobalTheory.ArtinLocalInj.artin_localIdele_injective GlobalTheory.Published.chevalleyUnits' L Ω art hart w`. Conclude with `MonoidHom.ext fun σ => hinj ((ha.glob art hart _).trans (ha'.glob art hart _).symm)`. Take `⟨b, hb, hN, hI⟩` from `hT`. Use `choose ψ hψ using hχ`. Establish `hcomm : ∀ s t, b.ρ s * b.ρ t = b.ρ t * b.ρ s`.

Introduce `s t`. Establish `hd : deg (⁅s, t⁆ : Weil h) = 0`. Establish `h0 : degHom h ⁅s, t⁆ = 1`. Rewrite using `[map_commutatorElement]`. Conclude with `(Commute.all _ _).commutator_eq`.

Rewrite `h0` using `[degHom_apply, ofAdd_eq_one]`. Then use the resulting hypothesis. Set `c : Ine (F` to `L) A := ⟨_, deg_eq_zero_iff.1 hd⟩`. Establish `hcc : ineIncl h c = ⁅s, t⁆` using `Subtype.ext rfl`. Establish `h1 : b.ρ ⁅s, t⁆ = 1`. Establish `h2 : ∀ i, (χ i c : ℂ) = 1` using `fun i => by`.

Rewrite using `[← hψ i c, hcc, map_commutatorElement, (Commute.all _ _).commutator_eq]`. Both sides reduce to the same expression. Rewrite using `[← hcc, hI c]`. Simplify using `[h2]`. Both sides reduce to the same expression.

Establish `e : s * t = ⁅s, t⁆ * (t * s)`. Rewrite using `[commutatorElement_def]`. Use `group`. Rewrite using `[← map_mul, ← map_mul, e, map_mul, h1, one_mul]`. Take `⟨η, hcp, hone⟩` from `exists_chars b.ρ b.semisimple hcomm`.

Establish `hsum : ∀ s : Ine (F` using `L) A, ∑ j, ((Units.coeHom ℂ).comp ((η j).comp (ineIncl h))) s = ∑ i, ((Units.coeHom ℂ).comp (χ i)) s := by`. Introduce `s`. Use `sum_of_prod _ _ ?_` and prove the remaining obligations. Establish `h1` using `hcp (ineIncl h s)`. Rewrite `h1` using `[hI s, ← LinearMap.charpoly_toMatrix _ (Pi.basisFun ℂ (Fin n)), LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin', Matrix.charpoly_diagonal]`.

Conclude with `h1.symm`. Take `⟨e, he⟩` from `exists_perm _ _ hsum`. Establish `hηχ : ∀ i (g : Ine (F` using `L) A), η (e i) (ineIncl h g) = χ i g := fun i g => Units.ext (DFunLike.congr_fun (he i) g)`. Establish `hsm : ∀ j, GlobalTheory.WeilDeligne.IsSmooth (η j)` using `fun j => b.smooth.of_le fun σ hσ => hone j σ hσ`. Use `choose ω hωs hωe using fun i => ha.factor (η (e i)) (hsm _)`.

Use `⟨ω, hωs, ?_, fun i g => ?_⟩` and prove the remaining obligations. Use `_root_.UpperTheory.V.Z.J.D.TypeVAux.nonempty_equiv_principal_series_of_char_poly_of_generic P.loc H _ ω hωs (fun s => ?_) ⟨b, hb, hN⟩ (GlobalTheory.ThK.DetProd.exists_isGeneric_of_isLocComp hτ)` and prove the remaining obligations. Rewrite using `[← hb, WD.charPol_mk, hcp s, ← Equiv.prod_comp e]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hωe i]`.

Both sides reduce to the same expression. Rewrite using `[← hart, ← hηχ i g, hωe i]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.V.Z.J.D.type_v_statement :
    _root_.UpperTheory.V.Z.J.D.TypeVAlt := by
  intro P L Ω _ _ _ _ _ _ n hn π w A h τ hτ χ hχ rc hrc hT
  obtain ⟨a, ha, ε, H⟩ := hrc
  have hart : a = artOf h := by
    have ha' : IsLocalArtin h (artOf h) := Classical.epsilon_spec (p := IsLocalArtin h) ⟨a, ha⟩
    obtain ⟨art, hart⟩ := P.aut.art L Ω
    have hinj := GlobalTheory.ArtinLocalInj.artin_localIdele_injective GlobalTheory.Published.chevalleyUnits' L Ω art hart w
    exact MonoidHom.ext fun σ => hinj ((ha.glob art hart _).trans (ha'.glob art hart _).symm)
  obtain ⟨b, hb, hN, hI⟩ := hT
  choose ψ hψ using hχ
  have hcomm : ∀ s t, b.ρ s * b.ρ t = b.ρ t * b.ρ s := by
    intro s t
    have hd : deg (⁅s, t⁆ : Weil h) = 0 := by
      have h0 : degHom h ⁅s, t⁆ = 1 := by
        rw [map_commutatorElement]
        exact (Commute.all _ _).commutator_eq
      rwa [degHom_apply, ofAdd_eq_one] at h0
    let c : Ine (F := L) A := ⟨_, deg_eq_zero_iff.1 hd⟩
    have hcc : ineIncl h c = ⁅s, t⁆ := Subtype.ext rfl
    have h1 : b.ρ ⁅s, t⁆ = 1 := by
      have h2 : ∀ i, (χ i c : ℂ) = 1 := fun i => by
        rw [← hψ i c, hcc, map_commutatorElement, (Commute.all _ _).commutator_eq]
        rfl
      rw [← hcc, hI c]
      simp [h2]
      rfl
    have e : s * t = ⁅s, t⁆ * (t * s) := by
      rw [commutatorElement_def]
      group
    rw [← map_mul, ← map_mul, e, map_mul, h1, one_mul]
  obtain ⟨η, hcp, hone⟩ := exists_chars b.ρ b.semisimple hcomm
  have hsum : ∀ s : Ine (F := L) A, ∑ j, ((Units.coeHom ℂ).comp ((η j).comp (ineIncl h))) s =
      ∑ i, ((Units.coeHom ℂ).comp (χ i)) s := by
    intro s
    refine sum_of_prod _ _ ?_
    have h1 := hcp (ineIncl h s)
    rw [hI s, ← LinearMap.charpoly_toMatrix _ (Pi.basisFun ℂ (Fin n)), LinearMap.toMatrix_eq_toMatrix',
      LinearMap.toMatrix'_toLin', Matrix.charpoly_diagonal] at h1
    exact h1.symm
  obtain ⟨e, he⟩ := exists_perm _ _ hsum
  have hηχ : ∀ i (g : Ine (F := L) A), η (e i) (ineIncl h g) = χ i g := fun i g =>
    Units.ext (DFunLike.congr_fun (he i) g)
  have hsm : ∀ j, GlobalTheory.WeilDeligne.IsSmooth (η j) := fun j => b.smooth.of_le fun σ hσ => hone j σ hσ
  choose ω hωs hωe using fun i => ha.factor (η (e i)) (hsm _)
  refine ⟨ω, hωs, ?_, fun i g => ?_⟩
  · refine _root_.UpperTheory.V.Z.J.D.TypeVAux.nonempty_equiv_principal_series_of_char_poly_of_generic P.loc H _ ω hωs (fun s => ?_) ⟨b, hb, hN⟩
      (GlobalTheory.ThK.DetProd.exists_isGeneric_of_isLocComp hτ)
    rw [← hb, WD.charPol_mk, hcp s, ← Equiv.prod_comp e]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hωe i]
    rfl
  · rw [← hart, ← hηχ i g, hωe i]
    rfl
end
end
