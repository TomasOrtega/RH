import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.TowerRallisLemma
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.IsSubquotientOfHasSupport
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.MonoOfMemSumList
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JointEigenDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCharsOfTameLpDim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericGlLocalComponentExponentLeOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecOfRecLiteralStatement

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open scoped commutatorElement

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.V.Z.J.D.prime_not_mem_section_base_place

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

end UpperTheory.V.Z.J.D.prime_not_mem_section_base_place

open UpperTheory.V.Z.J.D UpperTheory.V.Z.J.D.prime_not_mem_section_base_place in
/- English proof (translation)
Introduce `P L Ω _ _ _ _ _ _ n hn π w A h τ hτ χ hχ hT`. Establish `Lc` using `P.loc`. Take `⟨rc, hrc0⟩` from `Lc.llc L Ω A w h`. Establish `hrc : IsRec h rc` using `GlobalTheory.T.rec_of_rec_literal Lc.dzc Lc.dzi Lc.exh Lc.multi Lc.cos Lc.zel Lc.geo Lc.bz L Ω A w h rc hrc0`. Establish `ha : IsLocalArtin h (artOf h)`.

Take `⟨a, ha, -⟩` from `hrc`. Conclude with `Classical.epsilon_spec (p := IsLocalArtin h) ⟨a, ha⟩`. Take `⟨b, hb, hN, hI⟩` from `hT rc hrc`. Use `choose ψ hψ using hχ`. Establish `hcomm : ∀ s t, b.ρ s * b.ρ t = b.ρ t * b.ρ s`.

Introduce `s t`. Establish `hd : deg (⁅s, t⁆ : Weil h) = 0`. Establish `h0 : degHom h ⁅s, t⁆ = 1`. Rewrite using `[map_commutatorElement]`. Conclude with `(Commute.all _ _).commutator_eq`.

Rewrite `h0` using `[degHom_apply, ofAdd_eq_one]`. Then use the resulting hypothesis. Set `c : Ine (F` to `L) A := ⟨_, deg_eq_zero_iff.1 hd⟩`. Establish `hcc : ineIncl h c = ⁅s, t⁆` using `Subtype.ext rfl`. Establish `h1 : b.ρ ⁅s, t⁆ = 1`. Establish `h2 : ∀ i, (χ i c : ℂ) = 1` using `fun i => by`.

Rewrite using `[← hψ i c, hcc, map_commutatorElement, (Commute.all _ _).commutator_eq]`. Both sides reduce to the same expression. Rewrite using `[← hcc, hI c]`. Simplify using `[h2]`. Both sides reduce to the same expression.

Establish `e : s * t = ⁅s, t⁆ * (t * s)`. Rewrite using `[commutatorElement_def]`. Use `group`. Rewrite using `[← map_mul, ← map_mul, e, map_mul, h1, one_mul]`. Take `⟨η, hcp, hone⟩` from `exists_chars b.ρ b.semisimple hcomm`.

Establish `hsum : ∀ s : Ine (F` using `L) A, ∑ j, ((Units.coeHom ℂ).comp ((η j).comp (ineIncl h))) s = ∑ i, ((Units.coeHom ℂ).comp (χ i)) s := by`. Introduce `s`. Use `sum_of_prod _ _ ?_` and prove the remaining obligations. Establish `h1` using `hcp (ineIncl h s)`. Rewrite `h1` using `[hI s, ← LinearMap.charpoly_toMatrix _ (Pi.basisFun ℂ (Fin n)), LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin', Matrix.charpoly_diagonal]`.

Conclude with `h1.symm`. Take `⟨e, he⟩` from `exists_perm _ _ hsum`. Establish `hηχ : ∀ i (g : Ine (F` using `L) A), η (e i) (ineIncl h g) = χ i g := fun i g => Units.ext (DFunLike.congr_fun (he i) g)`. Establish `hsm : ∀ j, GlobalTheory.WeilDeligne.IsSmooth (η j)` using `fun j => b.smooth.of_le fun σ hσ => hone j σ hσ`. Use `choose ω hωs hωe using fun i => ha.factor (η (e i)) (hsm _)`.

Use `⟨ω, hωs, ?_, fun i g => ?_⟩` and prove the remaining obligations. Establish `hsq : IsSubquotient τ.ρ (PS ω)` using `(psRec P L Ω n w A h _ ha rc hrc τ ω hωs).2 fun s => by`. Rewrite using `[← hb, WD.charPol_mk, hcp s, ← Equiv.prod_comp e]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hωe i]`.

Both sides reduce to the same expression. Conclude with `psGen P L Ω n w A h _ ha rc hrc τ ω hωs hsq ⟨b, hb, hN⟩ (GlobalTheory.ThK.DetProd.exists_isGeneric_of_isLocComp hτ)`. Rewrite using `[← hηχ i g, hωe i]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.V.Z.J.D.typePS2 :
    TypePS2 := by
  intro P L Ω _ _ _ _ _ _ n hn π w A h τ hτ χ hχ hT
  have Lc := P.loc
  obtain ⟨rc, hrc0⟩ := Lc.llc L Ω A w h
  have hrc : IsRec h rc :=
    GlobalTheory.T.rec_of_rec_literal Lc.dzc Lc.dzi Lc.exh Lc.multi Lc.cos Lc.zel Lc.geo Lc.bz L Ω A w h rc hrc0
  have ha : IsLocalArtin h (artOf h) := by
    obtain ⟨a, ha, -⟩ := hrc
    exact Classical.epsilon_spec (p := IsLocalArtin h) ⟨a, ha⟩
  obtain ⟨b, hb, hN, hI⟩ := hT rc hrc
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
  · have hsq : IsSubquotient τ.ρ (PS ω) := (psRec P L Ω n w A h _ ha rc hrc τ ω hωs).2 fun s => by
      rw [← hb, WD.charPol_mk, hcp s, ← Equiv.prod_comp e]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hωe i]
      rfl
    exact psGen P L Ω n w A h _ ha rc hrc τ ω hωs hsq ⟨b, hb, hN⟩
      (GlobalTheory.ThK.DetProd.exists_isGeneric_of_isLocComp hτ)
  · rw [← hηχ i g, hωe i]
    rfl
