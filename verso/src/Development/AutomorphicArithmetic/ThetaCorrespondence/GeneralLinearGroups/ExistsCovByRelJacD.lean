import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FirstIn
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FPiece
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSubquotientCompMulSingle
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSubquotientJacquetModuleRefineTensor
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleSubquotientTwoBlockConstituents
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacquetWordMultiplicityAdditiveJordanHolder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspProdCharTransport

open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas UpperTheory.Lit.Red

section SlopeTestRemainingChoices

open GlobalTheory.JacStages GlobalTheory.JacStagesExact GlobalTheory.ParIndExact GlobalTheory.CompanionTheory.Hypotheses₂.TD GlobalTheory.SplitRead

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Take `⟨h1, h2⟩` from `(hasFiniteLength_iff_wellFounded ρ).1 hl`. Use `exists_covBy_of_split (fun (S T : Subrepresentation ρ) => IsSubquotient Θ (relJacD e' (subQuot S T))) ?_ ?_ ⊤ ⊥ bot_le ?_` and prove the remaining obligations. Introduce and unpack `S ⟨R, f, hf⟩ haveI := subsingleton_subQuot_self S haveI := Model.nontrivial_of_isIrreducible hΘ`. Take `⟨u, hu⟩` from `exists_ne (0 : U)`. Take `⟨⟨v, hv⟩, rfl⟩` from `hf u`.

Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ v`. Take `rfl : z = 0` from `Subsingleton.elim _ _`. Conclude with `hu (map_zero f)`. Introduce `S M T hTM hMS hQ`. Take `⟨ι, p, hι, hp, hpι, hex⟩` from `subQuot_exact (ρ := ρ) hTM hMS`.

Use `isSubquotient_dichotomy (relJacMap e' ι) (relJacMap e' p) hΘ (fun x hx => ?_) hQ` and prove the remaining obligations. Take `⟨v, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Establish `h1 : p v ∈ twKer (subQuot S M) (relUnipD k e') 1` using `(Submodule.Quotient.mk_eq_zero _).1 hx`. Take `⟨v', hv', h2⟩` from `GlobalTheory.SmGL.Exponents.Additive.exists_mem_twKer p hp _ h1`. Take `⟨u, hu⟩` from `hex (v - v') (by rw [map_sub, h2, sub_self])`.

Use `⟨Submodule.Quotient.mk u, ?_⟩` and prove the remaining obligations. Use `show Submodule.Quotient.mk (ι u) = Submodule.Quotient.mk v`. Rewrite using `[hu]`. Conclude with `(Submodule.Quotient.eq _).2 (by simpa using hv')`. Take `⟨ι, hι⟩` from `subQuot_top_bot ρ`.

Conclude with `h.trans (isSubquotient_relJacD k s d t d' e' _ _ _ _ ((isSubquotient_subQuot _ _).isSmooth hρ) (.of_injective ι hι))`.
-/
private theorem exists_covBy_relJacD {s : ℕ} {d t : Fin s → ℕ} {d' : ∀ a, Fin (t a) → ℕ}
    (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a)) {U V : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V]
    [Module ℂ V] {Θ : Representation ℂ (∀ a, Levi k fun b => Fin (d' a b)) U} (hΘ : Θ.IsIrreducible)
    {ρ : Representation ℂ (Levi k fun a => Fin (d a)) V} (hρ : IsSmooth ρ) (hl : HasFiniteLength ρ)
    (h : IsSubquotient Θ (relJacD e' ρ)) :
    ∃ S T : Subrepresentation ρ, T ⋖ S ∧ IsSubquotient Θ (relJacD e' (subQuot S T)) := by
  obtain ⟨h1, h2⟩ := (hasFiniteLength_iff_wellFounded ρ).1 hl
  refine exists_covBy_of_split (fun (S T : Subrepresentation ρ) => IsSubquotient Θ (relJacD e' (subQuot S T)))
    ?_ ?_ ⊤ ⊥ bot_le ?_
  · rintro S ⟨R, f, hf⟩
    haveI := subsingleton_subQuot_self S
    haveI := Model.nontrivial_of_isIrreducible hΘ
    obtain ⟨u, hu⟩ := exists_ne (0 : U)
    obtain ⟨⟨v, hv⟩, rfl⟩ := hf u
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    obtain rfl : z = 0 := Subsingleton.elim _ _
    exact hu (map_zero f)
  · intro S M T hTM hMS hQ
    obtain ⟨ι, p, hι, hp, hpι, hex⟩ := subQuot_exact (ρ := ρ) hTM hMS
    refine isSubquotient_dichotomy (relJacMap e' ι) (relJacMap e' p) hΘ (fun x hx => ?_) hQ
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have h1 : p v ∈ twKer (subQuot S M) (relUnipD k e') 1 := (Submodule.Quotient.mk_eq_zero _).1 hx
    obtain ⟨v', hv', h2⟩ := GlobalTheory.SmGL.Exponents.Additive.exists_mem_twKer p hp _ h1
    obtain ⟨u, hu⟩ := hex (v - v') (by rw [map_sub, h2, sub_self])
    refine ⟨Submodule.Quotient.mk u, ?_⟩
    show Submodule.Quotient.mk (ι u) = Submodule.Quotient.mk v
    rw [hu]
    exact (Submodule.Quotient.eq _).2 (by simpa using hv')
  · obtain ⟨ι, hι⟩ := subQuot_top_bot ρ
    exact h.trans (isSubquotient_relJacD k s d t d' e' _ _ _ _ ((isSubquotient_subQuot _ _).isSmooth hρ)
      (.of_injective ι hι))

/- English proof (translation)
Set `d : Fin s → ℕ` to `fun a => ∑ b, (x a b).1`. Establish `hd : ∑ a, d a = w.1`. Rewrite using `[← hx, Equiv.sum_comp finSigmaFinEquiv.symm (fun p : (Σ a, Fin (t a)) => (x p.1 p.2).1), Fintype.sum_sigma]`. Set `e` to `stdBlocks d hd`. Set `e' : ∀ a, (Σ b, Fin ((x a b).1)) ≃ Fin (d a)` to `fun a => stdBlocks (fun i => (x a i).1) rfl`.

Take `⟨φR⟩` from `GlobalTheory.T.piExteriorTensor_flattenedIndex_equiv_nested s t (fun a b => GL (Fin ((x a b).1)) k) _ fun a b => (x a b).rep`. Take `⟨φS⟩` from `GlobalTheory.T.jacquetModule_in_stages_refined_blocks k s w.1 d e t (fun a b => (x a b).1) e' _ w.rep`. Take `⟨φP⟩` from `(GlobalTheory.SmGL.Placing.parInd_jac_placing k _ _ _ (stdBlocks _ hx) (refinePlace e e') _).2 w.rep`. Establish `hirr0 : (piTensor fun c : Fin (∑ a, t a) => (x (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2).rep).IsIrreducible` using `GlobalTheory.T.piExteriorTensor_smoothIrreducible_isIrreducible hBZ k _ _ fun c => (x (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2).2.rep`. Establish `hirr1` using `GlobalTheory.FinGL.Transport.isIrreducible_comp _ (flatHom fun a b => GL (Fin ((x a b).1)) k) (flatHom_surjective _) hirr0`.

Establish `hirr : (piTensor fun a => piTensor fun b => (x a b).rep).IsIrreducible` using `GlobalTheory.Parabolic.isIrreducible_of_equiv φR hirr1`. Establish `h1` using `(jhMult_ne_zero_iff.1 h).trans (isSubquotient_of_equiv φP)`. Establish `h2 : IsSubquotient (piTensor fun a => piTensor fun b => (x a b).rep) (relJacD e' (jac e w.rep))` using `(isSubquotient_of_equiv φR.symm).trans ((SupportUnique.isSubquotient_comp h1 (flatHom fun a b => GL (Fin ((x a b).1)) k)).trans (isSubquotient_of_equiv φS))`. Establish `hsm` using `isSmooth_jac e w.2.rep.smooth`. Take `⟨S, T, hST, h3⟩` from `exists_covBy_relJacD e' hirr hsm ((hBZ k).2.1 _ _ _ e _ w.rep w.2.rep.smooth (hasFiniteLength_of_isIrreducible w.2.rep.irr)) h2`.

Establish `hτ` using `isIrreducible_subQuot hST`. Take `⟨σ, hσ⟩` from `GlobalTheory.JacTensor.exists_irr_tensor_of_isSubquotient_jac hG k w.1 (Irr.ofIrrRep w.2.rep) s d e _ (subQuot S T) hτ (isSubquotient_subQuot S T)`. Set `σ' : Fin s → IrrGL k` to `fun a => IrrGL.of (σ a).π (σ a).smooth (σ a).irr`. Establish `hσi : (piTensor fun a => (σ' a).rep).IsIrreducible` using `GlobalTheory.T.piExteriorTensor_smoothIrreducible_isIrreducible hBZ k _ _ fun a => (σ' a).2.rep`. Establish `hσs : IsSmooth (piTensor fun a => (σ' a).rep)` using `isSmooth_piTensor fun a => (σ' a).2.rep.smooth`.

Establish `h4 : IsSubquotient (subQuot S T) (piTensor fun a => (σ' a).rep)` using `hσ.trans (GlobalTheory.piTensor_isSubquotient_of_forall _ _ _ _ _ _ fun a => isSubquotient_of_equiv (IrrGL.equivOf (σ a).π (σ a).smooth (σ a).irr))`. Take `⟨ψ⟩` from `SupportUnique.nonempty_equiv_of_isSubquotient hτ hσi h4`. Use `⟨σ', hd, jhMult_ne_zero_iff.2 ((isSubquotient_of_equiv ψ).trans (isSubquotient_subQuot S T)), fun a => ⟨rfl, jhMult_ne_zero_iff.2 ?_⟩⟩` and prove the remaining obligations. Take `⟨φT⟩` from `GlobalTheory.T.relativeJacquet_piExteriorTensor_equiv_normalized k s d t (fun a b => (x a b).1) e' _ fun a => (σ' a).rep`. Establish `h5` using `h3.trans ((isSubquotient_relJacD k s d t _ e' _ _ _ _ hσs h4).trans (isSubquotient_of_equiv φT))`.

Establish `hi : ∀ a, (piTensor fun b => (x a b).rep).IsIrreducible` using `fun a => GlobalTheory.T.piExteriorTensor_smoothIrreducible_isIrreducible hBZ k _ _ fun b => (x a b).2.rep`. Conclude with `SupportUnique.isSubquotient_factor (fun a => jac (e' a) (σ' a).rep) a (hi a) ((isSubquotient_comp_mulSingle (fun a => piTensor fun b => (x a b).rep) hi a).trans (SupportUnique.isSubquotient_comp h5 _))`.
-/
private theorem coarse (hG : GlobalTheory.Published.GeometricLemma) (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness)
    {s : ℕ} (t : Fin s → ℕ) (x : ∀ a, Fin (t a) → IrrGL k) (w : IrrGL k)
    (hx : ∑ c : Fin (∑ a, t a), (x (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2).1 = w.1)
    (h : jm (fun c : Fin (∑ a, t a) => x (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2) hx w.rep ≠ 0) :
    ∃ (σ : Fin s → IrrGL k) (hσ : ∑ a, (σ a).1 = w.1), jm σ hσ w.rep ≠ 0 ∧
      ∀ a, ∃ ha : ∑ b, (x a b).1 = (σ a).1, jm (x a) ha (σ a).rep ≠ 0 := by
  classical
  let d : Fin s → ℕ := fun a => ∑ b, (x a b).1
  have hd : ∑ a, d a = w.1 := by
    rw [← hx, Equiv.sum_comp finSigmaFinEquiv.symm (fun p : (Σ a, Fin (t a)) => (x p.1 p.2).1), Fintype.sum_sigma]
  let e := stdBlocks d hd
  let e' : ∀ a, (Σ b, Fin ((x a b).1)) ≃ Fin (d a) := fun a => stdBlocks (fun i => (x a i).1) rfl
  obtain ⟨φR⟩ := GlobalTheory.T.piExteriorTensor_flattenedIndex_equiv_nested s t (fun a b => GL (Fin ((x a b).1)) k) _ fun a b => (x a b).rep
  obtain ⟨φS⟩ := GlobalTheory.T.jacquetModule_in_stages_refined_blocks k s w.1 d e t (fun a b => (x a b).1) e' _ w.rep
  obtain ⟨φP⟩ := (GlobalTheory.SmGL.Placing.parInd_jac_placing k _ _ _ (stdBlocks _ hx) (refinePlace e e') _).2 w.rep
  have hirr0 : (piTensor fun c : Fin (∑ a, t a) =>
      (x (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2).rep).IsIrreducible :=
    GlobalTheory.T.piExteriorTensor_smoothIrreducible_isIrreducible hBZ k _ _ fun c => (x (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2).2.rep
  have hirr1 := GlobalTheory.FinGL.Transport.isIrreducible_comp _
    (flatHom fun a b => GL (Fin ((x a b).1)) k) (flatHom_surjective _) hirr0
  have hirr : (piTensor fun a => piTensor fun b => (x a b).rep).IsIrreducible :=
    GlobalTheory.Parabolic.isIrreducible_of_equiv φR hirr1
  have h1 := (jhMult_ne_zero_iff.1 h).trans (isSubquotient_of_equiv φP)
  have h2 : IsSubquotient (piTensor fun a => piTensor fun b => (x a b).rep) (relJacD e' (jac e w.rep)) :=
    (isSubquotient_of_equiv φR.symm).trans ((SupportUnique.isSubquotient_comp h1
      (flatHom fun a b => GL (Fin ((x a b).1)) k)).trans (isSubquotient_of_equiv φS))
  have hsm := isSmooth_jac e w.2.rep.smooth
  obtain ⟨S, T, hST, h3⟩ := exists_covBy_relJacD e' hirr hsm
    ((hBZ k).2.1 _ _ _ e _ w.rep w.2.rep.smooth (hasFiniteLength_of_isIrreducible w.2.rep.irr)) h2
  have hτ := isIrreducible_subQuot hST
  obtain ⟨σ, hσ⟩ := GlobalTheory.JacTensor.exists_irr_tensor_of_isSubquotient_jac hG k w.1 (Irr.ofIrrRep w.2.rep) s d e _
    (subQuot S T) hτ (isSubquotient_subQuot S T)
  let σ' : Fin s → IrrGL k := fun a => IrrGL.of (σ a).π (σ a).smooth (σ a).irr
  have hσi : (piTensor fun a => (σ' a).rep).IsIrreducible := GlobalTheory.T.piExteriorTensor_smoothIrreducible_isIrreducible hBZ k _ _ fun a => (σ' a).2.rep
  have hσs : IsSmooth (piTensor fun a => (σ' a).rep) := isSmooth_piTensor fun a => (σ' a).2.rep.smooth
  have h4 : IsSubquotient (subQuot S T) (piTensor fun a => (σ' a).rep) :=
    hσ.trans (GlobalTheory.piTensor_isSubquotient_of_forall _ _ _ _ _ _ fun a =>
      isSubquotient_of_equiv (IrrGL.equivOf (σ a).π (σ a).smooth (σ a).irr))
  obtain ⟨ψ⟩ := SupportUnique.nonempty_equiv_of_isSubquotient hτ hσi h4
  refine ⟨σ', hd, jhMult_ne_zero_iff.2 ((isSubquotient_of_equiv ψ).trans (isSubquotient_subQuot S T)),
    fun a => ⟨rfl, jhMult_ne_zero_iff.2 ?_⟩⟩
  obtain ⟨φT⟩ := GlobalTheory.T.relativeJacquet_piExteriorTensor_equiv_normalized k s d t (fun a b => (x a b).1) e' _ fun a => (σ' a).rep
  have h5 := h3.trans ((isSubquotient_relJacD k s d t _ e' _ _ _ _ hσs h4).trans (isSubquotient_of_equiv φT))
  have hi : ∀ a, (piTensor fun b => (x a b).rep).IsIrreducible := fun a =>
    GlobalTheory.T.piExteriorTensor_smoothIrreducible_isIrreducible hBZ k _ _ fun b => (x a b).2.rep
  exact SupportUnique.isSubquotient_factor (fun a => jac (e' a) (σ' a).rep) a (hi a)
    ((isSubquotient_comp_mulSingle (fun a => piTensor fun b => (x a b).rep) hi a).trans
      (SupportUnique.isSubquotient_comp h5 _))

/- English proof (translation)
Take `⟨u, hu, rfl⟩` from `exists_sum_of_jac hG hBZ hA (stdBlocks (fun a => (y a).1) hy) (GlobalTheory.T.piExteriorTensor_smoothIrreducible_isIrreducible hBZ k _ _ fun a => (y a).2.rep) (jhMult_ne_zero_iff.1 h) (fun a => (y a).2.rep) (fun a => isSubquotient_comp_mulSingle (fun a => (y a).rep) (fun a => (y …`. Conclude with `Finset.sum_congr rfl fun a _ => hasSupport_unique hG hBZ (hu a) (hT a)`.
-/
private theorem supp_jm (hG : GlobalTheory.Published.GeometricLemma) (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness)
    {s : ℕ} {y : Fin s → IrrGL k} {w : IrrGL k} {hy : ∑ a, (y a).1 = w.1} (h : jm y hy w.rep ≠ 0)
    {A : Multiset (IrrGL k)} (hA : HasSupport w.rep A) {T : Fin s → Multiset (IrrGL k)}
    (hT : ∀ a, HasSupport (y a).rep (T a)) : A = ∑ a, T a := by
  obtain ⟨u, hu, rfl⟩ := exists_sum_of_jac hG hBZ hA (stdBlocks (fun a => (y a).1) hy)
    (GlobalTheory.T.piExteriorTensor_smoothIrreducible_isIrreducible hBZ k _ _ fun a => (y a).2.rep) (jhMult_ne_zero_iff.1 h) (fun a => (y a).2.rep)
    (fun a => isSubquotient_comp_mulSingle (fun a => (y a).rep) (fun a => (y a).2.rep.irr) a)
  exact Finset.sum_congr rfl fun a _ => hasSupport_unique hG hBZ (hu a) (hT a)

/- English proof (translation)
Substitute `hL` using the available equality. Take `rfl : z = y` from `funext hz`. Conclude with `⟨hy, h⟩`.
-/
private theorem jm_cast {L L' : ℕ} (hL : L = L') (y : Fin L' → IrrGL k) (z : Fin L → IrrGL k)
    (hz : ∀ c, z c = y (Fin.cast hL c)) (w : IrrGL k) (hy : ∑ a, (y a).1 = w.1) (h : jm y hy w.rep ≠ 0) :
    ∃ hz : ∑ a, (z a).1 = w.1, jm z hz w.rep ≠ 0 := by
  subst hL
  obtain rfl : z = y := funext hz
  exact ⟨hy, h⟩

/- English proof (translation)
Set `x : ∀ a, Fin (t a) → IrrGL k` to `fun a b => y (Fin.cast hL (finSigmaFinEquiv ⟨a, b⟩))`. Take `⟨hx, h1⟩` from `jm_cast hL y (fun c => x (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2) (fun c => by simp [x]) w hy h`. Take `⟨σ, hσ, h2, h3⟩` from `coarse hG hBZ t x w hx h1`. Use `⟨σ, hσ, h2, fun a => ?_⟩` and prove the remaining obligations. Take `⟨ha, h4⟩` from `h3 a`.

Take `⟨A, hA⟩` from `exists_hasSupport hBZ hG (σ a)`. Rewrite using `[← supp_jm hG hBZ h4 hA fun b => hT _]`. Conclude with `hA`.
-/
private theorem merge (hG : GlobalTheory.Published.GeometricLemma) (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness)
    {s L : ℕ} (t : Fin s → ℕ) (hL : ∑ a, t a = L) {y : Fin L → IrrGL k} {w : IrrGL k} {hy : ∑ a, (y a).1 = w.1}
    (h : jm y hy w.rep ≠ 0) {T : Fin L → Multiset (IrrGL k)} (hT : ∀ a, HasSupport (y a).rep (T a)) :
    ∃ (σ : Fin s → IrrGL k) (hσ : ∑ a, (σ a).1 = w.1), jm σ hσ w.rep ≠ 0 ∧
      ∀ a, HasSupport (σ a).rep (∑ b, T (Fin.cast hL (finSigmaFinEquiv ⟨a, b⟩))) := by
  let x : ∀ a, Fin (t a) → IrrGL k := fun a b => y (Fin.cast hL (finSigmaFinEquiv ⟨a, b⟩))
  obtain ⟨hx, h1⟩ := jm_cast hL y (fun c => x (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2)
    (fun c => by simp [x]) w hy h
  obtain ⟨σ, hσ, h2, h3⟩ := coarse hG hBZ t x w hx h1
  refine ⟨σ, hσ, h2, fun a => ?_⟩
  obtain ⟨ha, h4⟩ := h3 a
  obtain ⟨A, hA⟩ := exists_hasSupport hBZ hG (σ a)
  rw [← supp_jm hG hBZ h4 hA fun b => hT _]
  exact hA

/- English proof (translation)
Establish `h` using `hA.sum_fst`. Rewrite `h` using `[h0]`. Simplify using `using h.symm`.
-/
private theorem deg_eq_zero {y : IrrGL k} {A : Multiset (IrrGL k)} (hA : HasSupport y.rep A) (h0 : A = 0) :
    y.1 = 0 := by
  have h := hA.sum_fst
  rw [h0] at h
  simpa using h.symm

/- English proof (translation)
Use `choose T hT using fun i j => exists_hasSupport hBZ hG (y i j)`. Establish `hC : ∀ j, HasSupport (w j).rep (∑ i, T i j)` using `fun j => hasSupport_of_isSubquotient_prodIrr (fun i => hT i j) (w j).2.rep.irr (jhMult_ne_zero_iff.1 (hcol j))`. Take `⟨A1, hA1, m1⟩` from `h1`. Take `⟨A2, hA2, m2⟩` from `h2`. Take `rfl` from `hasSupport_unique hG hBZ hA1 (hC 1)`.

Take `rfl` from `hasSupport_unique hG hBZ hA2 (hC 2)`. Simplify using `only [Fin.sum_univ_three, Multiset.mem_add] at m1 m2`. Establish `e0 : T 0 1 + T 0 2 = 0`. Take `⟨σ, hσ, j1, j2⟩` from `merge hG hBZ (![1, 2] : Fin 2 → ℕ) (by simp) (hrow 0) (hT 0)`. Establish `j3 : HasSupport (σ 1).rep (T 0 1 + T 0 2)`.

Use `j2 1` as an intermediate fact. Express the relevant statement in the definitionally equal form `HasSupport (σ 1).rep (∑ b : Fin 2, _) at this`. Rewrite `this` using `[Fin.sum_univ_two]`. Conclude with `this`. Break down `Nat.eq_zero_or_pos (σ 1).1 with hz | hp` into its components or cases.

Conclude with `SupportUnique.eq_zero_of_hasSupport hz j3`. Take `⟨A, hA, z, hz, hzJ⟩` from `(UpperTheory.Lit.Full.piece hG hBZ k (w 0) Jᶜ σ hσ j1).2 h0 hp`. Take `rfl` from `hasSupport_unique hG hBZ hA j3`. Break down `Multiset.mem_add.1 hz with hz | hz` into its components or cases. Conclude with `absurd (m1 z (Or.inl (Or.inl hz))).1 hzJ`.

Conclude with `absurd (m2 z (Or.inl (Or.inl hz))) hzJ`. Establish `d01` using `deg_eq_zero (hT 0 1) (add_eq_zero.1 e0).1`. Establish `d02` using `deg_eq_zero (hT 0 2) (add_eq_zero.1 e0).2`. Establish `r0` using `hr 0`. Establish `r1` using `hr 1`.

Establish `r2` using `hr 2`. Establish `c0` using `hc 0`. Establish `c1` using `hc 1`. Establish `c2` using `hc 2`. Simplify using `only [Fin.sum_univ_three] at r0 r1 r2 c0 c1 c2`.

Establish `d10 : (y 1 0).1 = 0` using `by omega`. Establish `d20 : (y 2 0).1 = 0` using `by omega`. Establish `t20 : T 2 0 = 0` using `SupportUnique.eq_zero_of_hasSupport d20 (hT 2 0)`. Establish `e2 : T 2 1 = 0`. Take `⟨σ, hσ, j1, j2⟩` from `merge hG hBZ (![2, 1] : Fin 2 → ℕ) (by simp) (hrow 2) (hT 2)`.

Establish `j3 : HasSupport (σ 0).rep (T 2 0 + T 2 1)`. Use `j2 0` as an intermediate fact. Express the relevant statement in the definitionally equal form `HasSupport (σ 0).rep (∑ b : Fin 2, _) at this`. Rewrite `this` using `[Fin.sum_univ_two]`. Conclude with `this`.

Rewrite `j3` using `[t20, zero_add]`. Break down `Nat.eq_zero_or_pos (σ 0).1 with hz | hp` into its components or cases. Conclude with `SupportUnique.eq_zero_of_hasSupport hz j3`. Take `⟨A, hA, z, hz, hzJ⟩` from `(UpperTheory.Lit.Full.piece hG hBZ k (w 2) {ρ} σ hσ j1).1 h3 hp`. Take `rfl` from `hasSupport_unique hG hBZ hA j3`.

Conclude with `absurd hzJ (m1 z (Or.inr hz)).2`. Establish `d21` using `deg_eq_zero (hT 2 1) e2`. Establish `d12 : (y 1 2).1 = 0` using `by omega`. Introduce `i j hij`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp_all`.
-/
private theorem offdiag (hG : GlobalTheory.Published.GeometricLemma) (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness)
    {J : Set (IrrGL k)} {ρ : IrrGL k} {w : Fin 3 → IrrGL k} (h0 : LastIn (w 0) Jᶜ) (h1 : SuppIn (w 1) (J \ {ρ}))
    (h2 : SuppIn (w 2) J) (h3 : FirstIn (w 2) {ρ}) (y : Fin 3 → Fin 3 → IrrGL k)
    (hr : ∀ i, ∑ j, (y i j).1 = (w i).1) (hc : ∀ j, ∑ i, (y i j).1 = (w j).1)
    (hrow : ∀ i, jm (y i) (hr i) (w i).rep ≠ 0)
    (hcol : ∀ j, jhMult (w j).rep (prodIrr (fun i => y i j) (hc j)) ≠ 0) :
    ∀ i j, j ≠ i → (y i j).1 = 0 := by
  choose T hT using fun i j => exists_hasSupport hBZ hG (y i j)
  have hC : ∀ j, HasSupport (w j).rep (∑ i, T i j) := fun j =>
    hasSupport_of_isSubquotient_prodIrr (fun i => hT i j) (w j).2.rep.irr (jhMult_ne_zero_iff.1 (hcol j))
  obtain ⟨A1, hA1, m1⟩ := h1
  obtain ⟨A2, hA2, m2⟩ := h2
  obtain rfl := hasSupport_unique hG hBZ hA1 (hC 1)
  obtain rfl := hasSupport_unique hG hBZ hA2 (hC 2)
  simp only [Fin.sum_univ_three, Multiset.mem_add] at m1 m2
  have e0 : T 0 1 + T 0 2 = 0 := by
    obtain ⟨σ, hσ, j1, j2⟩ := merge hG hBZ (![1, 2] : Fin 2 → ℕ) (by simp) (hrow 0) (hT 0)
    have j3 : HasSupport (σ 1).rep (T 0 1 + T 0 2) := by
      have := j2 1
      change HasSupport (σ 1).rep (∑ b : Fin 2, _) at this
      rw [Fin.sum_univ_two] at this
      exact this
    rcases Nat.eq_zero_or_pos (σ 1).1 with hz | hp
    · exact SupportUnique.eq_zero_of_hasSupport hz j3
    · obtain ⟨A, hA, z, hz, hzJ⟩ := (UpperTheory.Lit.Full.piece hG hBZ k (w 0) Jᶜ σ hσ j1).2 h0 hp
      obtain rfl := hasSupport_unique hG hBZ hA j3
      rcases Multiset.mem_add.1 hz with hz | hz
      · exact absurd (m1 z (Or.inl (Or.inl hz))).1 hzJ
      · exact absurd (m2 z (Or.inl (Or.inl hz))) hzJ
  have d01 := deg_eq_zero (hT 0 1) (add_eq_zero.1 e0).1
  have d02 := deg_eq_zero (hT 0 2) (add_eq_zero.1 e0).2
  have r0 := hr 0
  have r1 := hr 1
  have r2 := hr 2
  have c0 := hc 0
  have c1 := hc 1
  have c2 := hc 2
  simp only [Fin.sum_univ_three] at r0 r1 r2 c0 c1 c2
  have d10 : (y 1 0).1 = 0 := by omega
  have d20 : (y 2 0).1 = 0 := by omega
  have t20 : T 2 0 = 0 := SupportUnique.eq_zero_of_hasSupport d20 (hT 2 0)
  have e2 : T 2 1 = 0 := by
    obtain ⟨σ, hσ, j1, j2⟩ := merge hG hBZ (![2, 1] : Fin 2 → ℕ) (by simp) (hrow 2) (hT 2)
    have j3 : HasSupport (σ 0).rep (T 2 0 + T 2 1) := by
      have := j2 0
      change HasSupport (σ 0).rep (∑ b : Fin 2, _) at this
      rw [Fin.sum_univ_two] at this
      exact this
    rw [t20, zero_add] at j3
    rcases Nat.eq_zero_or_pos (σ 0).1 with hz | hp
    · exact SupportUnique.eq_zero_of_hasSupport hz j3
    · obtain ⟨A, hA, z, hz, hzJ⟩ := (UpperTheory.Lit.Full.piece hG hBZ k (w 2) {ρ} σ hσ j1).1 h3 hp
      obtain rfl := hasSupport_unique hG hBZ hA j3
      exact absurd hzJ (m1 z (Or.inr hz)).2
  have d21 := deg_eq_zero (hT 2 1) e2
  have d12 : (y 1 2).1 = 0 := by omega
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

/- English proof (translation)
Take `⟨φ⟩` from `(GlobalTheory.SmGL.Placing.parInd_jac_placing k _ _ _ e e' _).1 (piTensor fun i => (s i).ρ)`. Conclude with `isSubquotient_of_equiv φ`.
-/
private theorem multiProd_placing {h N : ℕ} {d : Fin h → ℕ} (e e' : (Σ i, Fin (d i)) ≃ Fin N)
    (s : ∀ i, IrrRep (GL (Fin (d i)) k)) :
    IsSubquotient (multiProd e fun i => (s i).ρ) (multiProd e' fun i => (s i).ρ) := by
  obtain ⟨φ⟩ := (GlobalTheory.SmGL.Placing.parInd_jac_placing k _ _ _ e e' _).1 (piTensor fun i => (s i).ρ)
  exact isSubquotient_of_equiv φ

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Establish `hτ : (piTensor fun j => (w j).rep).IsIrreducible` using `GlobalTheory.T.piExteriorTensor_smoothIrreducible_isIrreducible hBZ k _ _ fun j => (w j).2.rep`. Establish `hρ : IsSmooth (piTensor fun i => (w i).rep)` using `isSmooth_piTensor fun i => (w i).2.rep.smooth`. Take `⟨T, -, hT⟩` from `(hG k).2 (Fin h) (Fin h) (fun i => Fin (w i).1) (fun i => Fin (w i).1) _ f g _ (fun i => (w i).rep) (fun i => (w i).2.rep.smooth) (fun i => hasFiniteLength_of_isIrreducible (w i).2.rep.irr)`. Take `⟨s, -, hs⟩` from `Finset.exists_ne_zero_of_sum_ne_zero (fun e => hne ((hT ⟨_, _, hρ, hτ⟩).trans e))`. Use `⟨s, fun i => ?_, fun j => ?_⟩` and prove the remaining obligations.

Take `⟨φ⟩` from `(GlobalTheory.SmGL.Placing.parInd_jac_placing k _ _ _ (f i) (stdBlocks (fun j => b i j) (hr i)) _).2 (w i).rep`. Establish `k1 : IsSubquotient (piTensor fun j => (s i j).rep.ρ) (jac (f i) (w i).rep)` using `jhMult_ne_zero_iff.1 (Finset.prod_ne_zero_iff.1 (left_ne_zero_of_mul hs) i (Finset.mem_univ i))`. Establish `k2` using `jhMult_ne_zero_iff.2 (k1.trans (isSubquotient_of_equiv φ))`. Conclude with `k2`. Establish `k2 : IsSubquotient (piTensor fun j => (w j).rep) (piTensor fun j => multiProd (g j) fun i => (s i j).rep.ρ)` using `jhMult_ne_zero_iff.1 (right_ne_zero_of_mul hs)`.

Establish `k3` using `(isSubquotient_comp_mulSingle (fun j => (w j).rep) (fun j => (w j).2.rep.irr) j).trans (SupportUnique.isSubquotient_comp k2 (MonoidHom.mulSingle (fun j => GL (Fin (w j).1) k) j))`. Establish `k4 : IsSubquotient (w j).rep (multiProd (g j) fun i => (s i j).rep.ρ)` using `SupportUnique.isSubquotient_factor (fun j => multiProd (g j) fun i => (s i j).rep.ρ) j (w j).2.rep.irr k3`. Establish `k5 : IsSubquotient (multiProd (g j) fun i => (s i j).rep.ρ) (multiProd (stdBlocks (fun i => b i j) (hc j)) fun i => (s i j).rep.ρ)` using `multiProd_placing (g j) _ fun i => (s i j).rep`. Establish `k6` using `jhMult_ne_zero_iff.2 (k4.trans k5)`. Conclude with `k6`.
-/
private theorem cell (hG : GlobalTheory.Published.GeometricLemma) (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness)
    {h : ℕ} (w : Fin h → IrrGL k) {b : Fin h → Fin h → ℕ} (hr : ∀ i, ∑ j, b i j = (w i).1)
    (hc : ∀ j, ∑ i, b i j = (w j).1) (f : ∀ i, (Σ j, Fin (b i j)) ≃ Fin (w i).1)
    (g : ∀ j, (Σ i, Fin (b i j)) ≃ Fin (w j).1)
    (hne : jhMult (piTensor fun j => (w j).rep) (cellFunctor f g (piTensor fun i => (w i).rep)) ≠ 0) :
    ∃ s : ∀ i j, IrrCl (GL (Fin (b i j)) k),
      (∀ i, jm (fun j => (⟨b i j, s i j⟩ : IrrGL k)) (hr i) (w i).rep ≠ 0) ∧
        ∀ j, jhMult (w j).rep (prodIrr (fun i => (⟨b i j, s i j⟩ : IrrGL k)) (hc j)) ≠ 0 := by
  have hτ : (piTensor fun j => (w j).rep).IsIrreducible := GlobalTheory.T.piExteriorTensor_smoothIrreducible_isIrreducible hBZ k _ _ fun j => (w j).2.rep
  have hρ : IsSmooth (piTensor fun i => (w i).rep) := isSmooth_piTensor fun i => (w i).2.rep.smooth
  obtain ⟨T, -, hT⟩ := (hG k).2 (Fin h) (Fin h) (fun i => Fin (w i).1) (fun i => Fin (w i).1) _ f g _
    (fun i => (w i).rep) (fun i => (w i).2.rep.smooth) (fun i => hasFiniteLength_of_isIrreducible (w i).2.rep.irr)
  obtain ⟨s, -, hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    (fun e => hne ((hT ⟨_, _, hρ, hτ⟩).trans e))
  refine ⟨s, fun i => ?_, fun j => ?_⟩
  · obtain ⟨φ⟩ := (GlobalTheory.SmGL.Placing.parInd_jac_placing k _ _ _ (f i)
      (stdBlocks (fun j => b i j) (hr i)) _).2 (w i).rep
    have k1 : IsSubquotient (piTensor fun j => (s i j).rep.ρ) (jac (f i) (w i).rep) := jhMult_ne_zero_iff.1
      (Finset.prod_ne_zero_iff.1 (left_ne_zero_of_mul hs) i (Finset.mem_univ i))
    have k2 := jhMult_ne_zero_iff.2 (k1.trans (isSubquotient_of_equiv φ))
    exact k2
  · have k2 : IsSubquotient (piTensor fun j => (w j).rep)
        (piTensor fun j => multiProd (g j) fun i => (s i j).rep.ρ) :=
      jhMult_ne_zero_iff.1 (right_ne_zero_of_mul hs)
    have k3 := (isSubquotient_comp_mulSingle (fun j => (w j).rep) (fun j => (w j).2.rep.irr) j).trans
      (SupportUnique.isSubquotient_comp k2 (MonoidHom.mulSingle (fun j => GL (Fin (w j).1) k) j))
    have k4 : IsSubquotient (w j).rep (multiProd (g j) fun i => (s i j).rep.ρ) := SupportUnique.isSubquotient_factor
      (fun j => multiProd (g j) fun i => (s i j).rep.ρ) j (w j).2.rep.irr k3
    have k5 : IsSubquotient (multiProd (g j) fun i => (s i j).rep.ρ)
        (multiProd (stdBlocks (fun i => b i j) (hc j)) fun i => (s i j).rep.ρ) :=
      multiProd_placing (g j) _ fun i => (s i j).rep
    have k6 := jhMult_ne_zero_iff.2 (k4.trans k5)
    exact k6

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `hG hBZ k _ _ _ _ J ρ w N hd h0 h1 h2 h3`. Set `M` to `fun i : Fin 3 => Fin (w i).1`. Use `haveI : Fintype (SizeMatrix M M) := Fintype.ofFinite _`. Set `b₀ : SizeMatrix M M` to `⟨fun i j => if i = j then (w i).1 else 0, by`. Use `⟨fun i => ?_, fun j => ?_⟩` and prove the remaining obligations.

Simplify using `[M]`. Simplify using `[M]⟩`. Establish `hτ : (piTensor fun j => (w j).rep).IsIrreducible` using `GlobalTheory.T.piExteriorTensor_smoothIrreducible_isIrreducible hBZ k _ _ fun j => (w j).2.rep`. Establish `hρ : IsSmooth (piTensor fun i => (w i).rep)` using `isSmooth_piTensor fun i => (w i).2.rep.smooth`. Take `⟨f₀, g₀, ⟨E₀⟩⟩` from `GlobalTheory.CompanionTheory.Hypotheses₂.TD.cell_diag b₀ (fun i j hj => by simp [b₀, Ne.symm hj]) _ hρ`.

Set `f : ∀ (b : SizeMatrix M M) i, (Σ j, Fin (b.1 i j)) ≃ M i` to `fun b => if h : b = b₀ then h ▸ f₀ else b.nonempty_rows.some`. Set `g : ∀ (b : SizeMatrix M M) j, (Σ i, Fin (b.1 i j)) ≃ M j` to `fun b => if h : b = b₀ then h ▸ g₀ else b.nonempty_cols.some`. Establish `hf : f b₀ = f₀` using `by simp [f]`. Establish `hg : g b₀ = g₀` using `by simp [g]`. Establish `hsum` using `(hG k).1.jhMult_eq (m := M) (m' := M) (stdBlocks (fun a => (w a).1) hd) (stdBlocks (fun a => (w a).1) hd) hρ f g hτ`.

Use `(show jm w hd (prodIrr w hd) = _ from hsum).trans_le ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single b₀]`. Establish `key : ∀ (f' : ∀ i, (Σ j, Fin (b₀.1 i j)) ≃ M i) (g' : ∀ j, (Σ i, Fin (b₀.1 i j)) ≃ M j), f' = f₀ → g' = g₀ → jhMult (piTensor fun i => (w i).rep) (cellFunctor f' g' (piTensor fun i => (w i).rep)) ≤ 1`. Introduce and unpack `_ _ rfl rfl`. Conclude with `((jhMult_congr_right _ E₀).trans (jhMult_self hτ)).le`.

Conclude with `key _ _ hf hg`. Introduce `b _ hb`. Assume the negation of the conclusion as `hne`. Establish `hr : ∀ i, ∑ j, b.1 i j = (w i).1` using `fun i => (b.2.1 i).trans (Fintype.card_fin _)`. Establish `hc : ∀ j, ∑ i, b.1 i j = (w j).1` using `fun j => (b.2.2 j).trans (Fintype.card_fin _)`.

Take `⟨s, hrow, hcol⟩` from `cell hG hBZ w hr hc (f b) (g b) hne`. Establish `hz : ∀ i j, j ≠ i → b.1 i j = 0` using `offdiag hG hBZ h0 h1 h2 h3 (fun i j => ⟨b.1 i j, s i j⟩) hr hc hrow hcol`. Use `hb (Subtype.ext (funext fun i => funext fun j => ?_))` and prove the remaining obligations. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality.

Establish `r` using `hr i`. Rewrite `r` using `[Finset.sum_eq_single i (fun j _ hj => hz i j hj) (by simp)]`. Conclude with `r.trans (if_pos rfl).symm`. Conclude with `(hz i j (Ne.symm hij)).trans (if_neg hij).symm`. Simplify using the standard rewrite rules.
-/
theorem UpperTheory.Lit.Full.diag3 :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (J : Set (IrrGL k)) (ρ : IrrGL k) (w : Fin 3 → IrrGL k) (N : ℕ) (hd : ∑ a, (w a).1 = N), LastIn (w 0) Jᶜ → SuppIn (w 1) (J \ {ρ}) → SuppIn (w 2) J → FirstIn (w 2) {ρ} → jm w hd (prodIrr w hd) ≤ 1 := by
  intro hG hBZ k _ _ _ _ J ρ w N hd h0 h1 h2 h3
  classical
  let M := fun i : Fin 3 => Fin (w i).1
  haveI : Fintype (SizeMatrix M M) := Fintype.ofFinite _
  let b₀ : SizeMatrix M M := ⟨fun i j => if i = j then (w i).1 else 0, by
    refine ⟨fun i => ?_, fun j => ?_⟩
    · simp [M]
    · simp [M]⟩
  have hτ : (piTensor fun j => (w j).rep).IsIrreducible := GlobalTheory.T.piExteriorTensor_smoothIrreducible_isIrreducible hBZ k _ _ fun j => (w j).2.rep
  have hρ : IsSmooth (piTensor fun i => (w i).rep) := isSmooth_piTensor fun i => (w i).2.rep.smooth
  obtain ⟨f₀, g₀, ⟨E₀⟩⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.TD.cell_diag b₀ (fun i j hj => by simp [b₀, Ne.symm hj]) _ hρ
  let f : ∀ (b : SizeMatrix M M) i, (Σ j, Fin (b.1 i j)) ≃ M i := fun b =>
    if h : b = b₀ then h ▸ f₀ else b.nonempty_rows.some
  let g : ∀ (b : SizeMatrix M M) j, (Σ i, Fin (b.1 i j)) ≃ M j := fun b =>
    if h : b = b₀ then h ▸ g₀ else b.nonempty_cols.some
  have hf : f b₀ = f₀ := by simp [f]
  have hg : g b₀ = g₀ := by simp [g]
  have hsum := (hG k).1.jhMult_eq (m := M) (m' := M) (stdBlocks (fun a => (w a).1) hd)
    (stdBlocks (fun a => (w a).1) hd) hρ f g hτ
  refine (show jm w hd (prodIrr w hd) = _ from hsum).trans_le ?_
  rw [Finset.sum_eq_single b₀]
  · have key : ∀ (f' : ∀ i, (Σ j, Fin (b₀.1 i j)) ≃ M i) (g' : ∀ j, (Σ i, Fin (b₀.1 i j)) ≃ M j), f' = f₀ → g' = g₀ →
        jhMult (piTensor fun i => (w i).rep) (cellFunctor f' g' (piTensor fun i => (w i).rep)) ≤ 1 := by
      rintro _ _ rfl rfl
      exact ((jhMult_congr_right _ E₀).trans (jhMult_self hτ)).le
    exact key _ _ hf hg
  · intro b _ hb
    by_contra hne
    have hr : ∀ i, ∑ j, b.1 i j = (w i).1 := fun i => (b.2.1 i).trans (Fintype.card_fin _)
    have hc : ∀ j, ∑ i, b.1 i j = (w j).1 := fun j => (b.2.2 j).trans (Fintype.card_fin _)
    obtain ⟨s, hrow, hcol⟩ := cell hG hBZ w hr hc (f b) (g b) hne
    have hz : ∀ i j, j ≠ i → b.1 i j = 0 :=
      offdiag hG hBZ h0 h1 h2 h3 (fun i j => ⟨b.1 i j, s i j⟩) hr hc hrow hcol
    refine hb (Subtype.ext (funext fun i => funext fun j => ?_))
    by_cases hij : i = j
    · subst hij
      have r := hr i
      rw [Finset.sum_eq_single i (fun j _ hj => hz i j hj) (by simp)] at r
      exact r.trans (if_pos rfl).symm
    · exact (hz i j (Ne.symm hij)).trans (if_neg hij).symm
  · simp
