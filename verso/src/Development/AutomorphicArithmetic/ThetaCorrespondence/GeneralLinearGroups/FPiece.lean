import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FirstIn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityPos
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FineJacquetLengthOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityConcat
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviIrreducibleTensorDecomposition
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSubquotientCompMulSingle
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LanglandsClassificationCuspidalSupport

open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas UpperTheory.Lit.Red

section SlopeTestRemainingChoices

open GlobalTheory.JacStages GlobalTheory.LocGL.SupportUnique

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Establish `: WellFoundedLT (Subrepresentation ρ)` using `((hasFiniteLength_iff_wellFounded ρ).1 hl).2`. Establish `key : ∀ S : Subrepresentation ρ, jhMult σ (relJacD e' S.toRepresentation) ≠ 0 → ∃ τ : IrrRep (Levi k fun a => Fin (d a)), IsSubquotient τ.ρ ρ ∧ jhMult σ (relJacD e' τ.ρ) ≠ 0`. Introduce `S`. Proceed by induction on `S using WellFoundedLT.induction with`. Consider the case `ind S ih`.

Introduce `hS`. Break down `eq_or_ne S ⊥ with rfl | hne` into its components or cases. Establish `h0 : Subsingleton (⊥ : Subrepresentation ρ).toSubmodule` using `inferInstanceAs (Subsingleton (⊥ : Submodule ℂ V))`. Establish `h1 : Subsingleton (Jacquet (⊥ : Subrepresentation ρ).toRepresentation (relUnipD k e'))` using `(Submodule.Quotient.mk_surjective _).subsingleton`. Conclude with `absurd (jhMult_of_subsingleton hσ _) hS`.

Establish `: WellFoundedGT (Subrepresentation ρ)` using `((hasFiniteLength_iff_wellFounded ρ).1 hl).1`. Take `⟨T, -, hT⟩` from `exists_le_covBy_of_lt (bot_lt_iff_ne_bot.2 hne)`. Set `ι : T.toRepresentation.IntertwiningMap S.toRepresentation` to `⟨Submodule.inclusion hT.le, fun _ => rfl⟩`. Set `p : S.toRepresentation.IntertwiningMap (subQuot S T)` to `⟨Submodule.mkQ _, fun _ => rfl⟩`. Set `j : S.toRepresentation.IntertwiningMap ρ` to `⟨S.toSubmodule.subtype, fun _ => rfl⟩`.

Establish `hp : ∀ v, p v = 0 ↔ v.1 ∈ T.toSubmodule` using `fun v => Submodule.Quotient.mk_eq_zero _`. Establish `hj : IsSubquotient S.toRepresentation ρ` using `.of_injective j Subtype.val_injective`. Establish `hq : IsSubquotient (subQuot S T) ρ` using `(IsSubquotient.of_surjective p (Submodule.Quotient.mk_surjective _)).trans hj`. Rewrite using `[GlobalTheory.CompanionTheory.JmTrans.jhMult_relJacD_exact e' hσ ι p (hj.isSmooth hρ) (Submodule.inclusion_injective hT.le) (Submodule.Quotient.mk_surjective _) (fun v => ⟨fun hv => ⟨⟨v.1, (hp v).1 hv⟩, rfl⟩, by`. Introduce and unpack `⟨u, rfl⟩`.

Conclude with `(hp _).2 u.2⟩)] at hS`. Distinguish the cases in `h1 : jhMult σ (relJacD e' T.toRepresentation) = 0`. Rewrite `hS` using `[h1, zero_add]`. Conclude with `⟨⟨_, subQuot S T, hq.isSmooth hρ, isIrreducible_subQuot hT⟩, hq, hS⟩`. Conclude with `ih T hT.lt h1`.

Use `key ⊤ (jhMult_ne_zero_iff.2 ((jhMult_ne_zero_iff.1 h).trans ?_))` and prove the remaining obligations. Conclude with `GlobalTheory.T.isSubquotient_relativeJacquet_blockLevi k s d t d' e' _ _ ρ _ ((isSubquotient_of_equiv (topEquiv ρ)).isSmooth hρ) (isSubquotient_of_equiv (topEquiv ρ).symm)`.
-/
private theorem piece_irr {s : ℕ} {d : Fin s → ℕ} {t : Fin s → ℕ} {d' : ∀ a, Fin (t a) → ℕ}
    {U V : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a))
    {σ : Representation ℂ (∀ a, Levi k fun b => Fin (d' a b)) U} (hσ : σ.IsIrreducible)
    {ρ : Representation ℂ (Levi k fun a => Fin (d a)) V} (hρ : IsSmooth ρ) (hl : HasFiniteLength ρ)
    (h : jhMult σ (relJacD e' ρ) ≠ 0) :
    ∃ τ : IrrRep (Levi k fun a => Fin (d a)), IsSubquotient τ.ρ ρ ∧ jhMult σ (relJacD e' τ.ρ) ≠ 0 := by
  have : WellFoundedLT (Subrepresentation ρ) := ((hasFiniteLength_iff_wellFounded ρ).1 hl).2
  have key : ∀ S : Subrepresentation ρ, jhMult σ (relJacD e' S.toRepresentation) ≠ 0 →
      ∃ τ : IrrRep (Levi k fun a => Fin (d a)), IsSubquotient τ.ρ ρ ∧ jhMult σ (relJacD e' τ.ρ) ≠ 0 := by
    intro S
    induction S using WellFoundedLT.induction with
    | ind S ih =>
    intro hS
    rcases eq_or_ne S ⊥ with rfl | hne
    · have h0 : Subsingleton (⊥ : Subrepresentation ρ).toSubmodule :=
        inferInstanceAs (Subsingleton (⊥ : Submodule ℂ V))
      have h1 : Subsingleton (Jacquet (⊥ : Subrepresentation ρ).toRepresentation (relUnipD k e')) :=
        (Submodule.Quotient.mk_surjective _).subsingleton
      exact absurd (jhMult_of_subsingleton hσ _) hS
    have : WellFoundedGT (Subrepresentation ρ) := ((hasFiniteLength_iff_wellFounded ρ).1 hl).1
    obtain ⟨T, -, hT⟩ := exists_le_covBy_of_lt (bot_lt_iff_ne_bot.2 hne)
    let ι : T.toRepresentation.IntertwiningMap S.toRepresentation :=
      ⟨Submodule.inclusion hT.le, fun _ => rfl⟩
    let p : S.toRepresentation.IntertwiningMap (subQuot S T) := ⟨Submodule.mkQ _, fun _ => rfl⟩
    let j : S.toRepresentation.IntertwiningMap ρ := ⟨S.toSubmodule.subtype, fun _ => rfl⟩
    have hp : ∀ v, p v = 0 ↔ v.1 ∈ T.toSubmodule := fun v => Submodule.Quotient.mk_eq_zero _
    have hj : IsSubquotient S.toRepresentation ρ := .of_injective j Subtype.val_injective
    have hq : IsSubquotient (subQuot S T) ρ :=
      (IsSubquotient.of_surjective p (Submodule.Quotient.mk_surjective _)).trans hj
    rw [GlobalTheory.CompanionTheory.JmTrans.jhMult_relJacD_exact e' hσ ι p (hj.isSmooth hρ) (Submodule.inclusion_injective hT.le)
      (Submodule.Quotient.mk_surjective _) (fun v => ⟨fun hv => ⟨⟨v.1, (hp v).1 hv⟩, rfl⟩, by
        rintro ⟨u, rfl⟩
        exact (hp _).2 u.2⟩)] at hS
    by_cases h1 : jhMult σ (relJacD e' T.toRepresentation) = 0
    · rw [h1, zero_add] at hS
      exact ⟨⟨_, subQuot S T, hq.isSmooth hρ, isIrreducible_subQuot hT⟩, hq, hS⟩
    · exact ih T hT.lt h1
  refine key ⊤ (jhMult_ne_zero_iff.2 ((jhMult_ne_zero_iff.1 h).trans ?_))
  exact GlobalTheory.T.isSubquotient_relativeJacquet_blockLevi k s d t d' e' _ _ ρ _
    ((isSubquotient_of_equiv (topEquiv ρ)).isSmooth hρ) (isSubquotient_of_equiv (topEquiv ρ).symm)

/- English proof (translation)
Establish `hA : GlobalTheory.Published.IrreducibleAdmissibleGL` using `fun k _ _ _ _ n V _ _ π => (hBZ k).1 (Fin n) V π`. Set `d : Fin s → ℕ` to `fun a => ∑ i, (x a i).1`. Establish `hd : ∑ a, d a = N`. Use `Eq.trans ?_ hcat` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Set `e` to `stdBlocks d hd`. Set `e' : ∀ a, (Σ b, Fin ((x a b).1)) ≃ Fin (d a)` to `fun a => stdBlocks (fun i => (x a i).1) rfl`. Establish `hE : refinePlace e e' = stdBlocks (fun a => (Zc.Seg.concat c x a).1) hcat` using `GlobalTheory.CompanionTheory.JmTrans.refinePlace_stdBlocks (x := fun a i => (x a i).1) hd (fun _ => rfl) hcat`. Take `⟨φR⟩` from `GlobalTheory.T.piExteriorTensor_flattenedIndex_equiv_nested s c (fun a b => GL (Fin ((x a b).1)) k) _ fun a b => (x a b).rep`. Take `⟨φS⟩` from `GlobalTheory.T.jacquetModule_in_stages_refined_blocks k s N d e c (fun a b => (x a b).1) e' V π`.

Establish `hirr0 : (piTensor fun l => (Zc.Seg.concat c x l).rep).IsIrreducible` using `GlobalTheory.CompanionTheory.SocleJm.isIrreducible_piTensor hA (Zc.Seg.concat c x)`. Establish `hirr1` using `GlobalTheory.FinGL.Transport.isIrreducible_comp _ (flatHom fun a b => GL (Fin ((x a b).1)) k) (flatHom_surjective _) hirr0`. Establish `hirr : (piTensor fun a => piTensor fun b => (x a b).rep).IsIrreducible` using `GlobalTheory.Parabolic.isIrreducible_of_equiv φR hirr1`. Establish `h2 : jhMult (piTensor fun a => piTensor fun b => (x a b).rep) (relJacD e' (jac e π)) ≠ 0`. Rewrite using `[← jhMult_congr_right _ φS, ← jhMult_congr_left φR]`.

Rewrite `h1` using `[jm, ← hE]`. Conclude with `(GlobalTheory.SmGL.EmptyBlocks.jhMult_comp_surjective _ (flatHom_surjective _) _ _).trans_ne h1`. Take `⟨τ, hτ, h3⟩` from `piece_irr e' hirr (isSmooth_jac e hs) ((hBZ k).2.1 _ _ _ e V π hs hfl) h2`. Take `⟨σ, ⟨φ⟩⟩` from `GlobalTheory.CompanionTheory.LeviTensor.nonempty_equiv_piTensor hA d τ`. Take `⟨φT⟩` from `GlobalTheory.T.relativeJacquet_piExteriorTensor_equiv_normalized k s d c (fun a b => (x a b).1) e' _ fun a => (σ a).rep.ρ`.

Establish `h4 : IsSubquotient (piTensor fun a => piTensor fun b => (x a b).rep) (piTensor fun a => jac (e' a) (σ a).rep.ρ)` using `((jhMult_ne_zero_iff.1 h3).trans (GlobalTheory.T.isSubquotient_relativeJacquet_blockLevi k s d c _ e' _ _ τ.ρ _ (isSmooth_piTensor fun a => (σ a).rep.smooth) (isSubquotient_of_equiv φ))).trans (isSubquotient_of_equiv φT)`. Use `⟨fun a => ⟨d a, σ a⟩, hd, jhMult_ne_zero_iff.2 ((isSubquotient_of_equiv φ.symm).trans hτ), fun a => ⟨rfl, jhMult_ne_zero_iff.2 ?_⟩⟩` and prove the remaining obligations. Establish `hi : ∀ a, (piTensor fun b => (x a b).rep).IsIrreducible` using `fun a => GlobalTheory.CompanionTheory.SocleJm.isIrreducible_piTensor hA (x a)`. Conclude with `isSubquotient_factor (fun a => jac (e' a) (σ a).rep.ρ) a (hi a) ((GlobalTheory.CompanionTheory.Hypotheses₂.TD.isSubquotient_comp_mulSingle _ hi a).trans (isSubquotient_comp h4 _))`.
-/
private theorem piece_coarse (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) {s N : ℕ} (c : Fin s → ℕ)
    (x : ∀ a, Fin (c a) → IrrGL k) (hcat : ∑ i, (Zc.Seg.concat c x i).1 = N) {V : Type} [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth π) (hfl : HasFiniteLength π)
    (h1 : jm (Zc.Seg.concat c x) hcat π ≠ 0) :
    ∃ (σ : Fin s → IrrGL k) (hσ : ∑ a, (σ a).1 = N), jm σ hσ π ≠ 0 ∧
      ∀ a, ∃ hx : ∑ i, (x a i).1 = (σ a).1, jm (x a) hx (σ a).rep ≠ 0 := by
  classical
  have hA : GlobalTheory.Published.IrreducibleAdmissibleGL := fun k _ _ _ _ n V _ _ π => (hBZ k).1 (Fin n) V π
  let d : Fin s → ℕ := fun a => ∑ i, (x a i).1
  have hd : ∑ a, d a = N := by
    refine Eq.trans ?_ hcat
    calc ∑ a, d a = ∑ p : Σ a, Fin (c a), (x p.1 p.2).1 := (Fintype.sum_sigma fun p : Σ a, Fin (c a) => (x p.1 p.2).1).symm
      _ = _ := (Fintype.sum_equiv finSigmaFinEquiv.symm _ _ fun _ => rfl).symm
  let e := stdBlocks d hd
  let e' : ∀ a, (Σ b, Fin ((x a b).1)) ≃ Fin (d a) := fun a => stdBlocks (fun i => (x a i).1) rfl
  have hE : refinePlace e e' = stdBlocks (fun a => (Zc.Seg.concat c x a).1) hcat :=
    GlobalTheory.CompanionTheory.JmTrans.refinePlace_stdBlocks (x := fun a i => (x a i).1) hd (fun _ => rfl) hcat
  obtain ⟨φR⟩ := GlobalTheory.T.piExteriorTensor_flattenedIndex_equiv_nested s c (fun a b => GL (Fin ((x a b).1)) k) _ fun a b => (x a b).rep
  obtain ⟨φS⟩ := GlobalTheory.T.jacquetModule_in_stages_refined_blocks k s N d e c (fun a b => (x a b).1) e' V π
  have hirr0 : (piTensor fun l => (Zc.Seg.concat c x l).rep).IsIrreducible :=
    GlobalTheory.CompanionTheory.SocleJm.isIrreducible_piTensor hA (Zc.Seg.concat c x)
  have hirr1 := GlobalTheory.FinGL.Transport.isIrreducible_comp _
    (flatHom fun a b => GL (Fin ((x a b).1)) k) (flatHom_surjective _) hirr0
  have hirr : (piTensor fun a => piTensor fun b => (x a b).rep).IsIrreducible :=
    GlobalTheory.Parabolic.isIrreducible_of_equiv φR hirr1
  have h2 : jhMult (piTensor fun a => piTensor fun b => (x a b).rep) (relJacD e' (jac e π)) ≠ 0 := by
    rw [← jhMult_congr_right _ φS, ← jhMult_congr_left φR]
    rw [jm, ← hE] at h1
    exact (GlobalTheory.SmGL.EmptyBlocks.jhMult_comp_surjective _ (flatHom_surjective _) _ _).trans_ne h1
  obtain ⟨τ, hτ, h3⟩ := piece_irr e' hirr (isSmooth_jac e hs) ((hBZ k).2.1 _ _ _ e V π hs hfl) h2
  obtain ⟨σ, ⟨φ⟩⟩ := GlobalTheory.CompanionTheory.LeviTensor.nonempty_equiv_piTensor hA d τ
  obtain ⟨φT⟩ := GlobalTheory.T.relativeJacquet_piExteriorTensor_equiv_normalized k s d c (fun a b => (x a b).1) e' _ fun a => (σ a).rep.ρ
  have h4 : IsSubquotient (piTensor fun a => piTensor fun b => (x a b).rep)
      (piTensor fun a => jac (e' a) (σ a).rep.ρ) :=
    ((jhMult_ne_zero_iff.1 h3).trans (GlobalTheory.T.isSubquotient_relativeJacquet_blockLevi k s d c _ e' _ _ τ.ρ _
      (isSmooth_piTensor fun a => (σ a).rep.smooth) (isSubquotient_of_equiv φ))).trans (isSubquotient_of_equiv φT)
  refine ⟨fun a => ⟨d a, σ a⟩, hd, jhMult_ne_zero_iff.2 ((isSubquotient_of_equiv φ.symm).trans hτ),
    fun a => ⟨rfl, jhMult_ne_zero_iff.2 ?_⟩⟩
  have hi : ∀ a, (piTensor fun b => (x a b).rep).IsIrreducible :=
    fun a => GlobalTheory.CompanionTheory.SocleJm.isIrreducible_piTensor hA (x a)
  exact isSubquotient_factor (fun a => jac (e' a) (σ a).rep.ρ) a (hi a)
    ((GlobalTheory.CompanionTheory.Hypotheses₂.TD.isSubquotient_comp_mulSingle _ hi a).trans (isSubquotient_comp h4 _))

private def Wd (W : ℕ → IrrGL k) (n : ℕ) (x : IrrGL k) : Prop :=
  ∃ hd : ∑ i : Fin n, (W i).1 = x.1, jm (fun i : Fin n => W i) hd x.rep ≠ 0

/- English proof (translation)
Substitute `h` using the available equality. Take `rfl : f = fun i : Fin m => W i` from `funext hf`. Both sides reduce to the same expression.
-/
private theorem wd_iff {W : ℕ → IrrGL k} {n m : ℕ} {x : IrrGL k} (h : m = n) (f : Fin m → IrrGL k)
    (hf : ∀ i, f i = W i) : Wd W n x ↔ ∃ hd : ∑ i, (f i).1 = x.1, jm f hd x.rep ≠ 0 := by
  subst h
  obtain rfl : f = fun i : Fin m => W i := funext hf
  rfl

private def cut (W : ℕ → IrrGL k) (a b : ℕ) (j : Fin 2) (i : Fin (![a, b] j)) : IrrGL k :=
  W (finSigmaFinEquiv (n := ![a, b]) ⟨j, i⟩)

/- English proof (translation)
Simplify using `[Zc.Seg.concat, cut]`.
-/
private theorem concat_cut (W : ℕ → IrrGL k) (a b : ℕ) (i) : Zc.Seg.concat ![a, b] (cut W a b) i = W i := by
  simp [Zc.Seg.concat, cut]

/- English proof (translation)
Simplify using `[cut, finSigmaFinEquiv_apply]`.
-/
private theorem cut_zero (W : ℕ → IrrGL k) (a b : ℕ) (i) : cut W a b 0 i = W i := by
  simp [cut, finSigmaFinEquiv_apply]

/- English proof (translation)
Simplify using `[cut, finSigmaFinEquiv_apply]`.
-/
private theorem cut_one (W : ℕ → IrrGL k) (a b : ℕ) (i) : cut W a b 1 i = W (a + i) := by
  simp [cut, finSigmaFinEquiv_apply]

/- English proof (translation)
Establish `hA : GlobalTheory.Published.IrreducibleAdmissibleGL` using `fun k _ _ _ _ n V _ _ π => (hBZ k).1 (Fin n) V π`. Establish `H : ∀ j, ∃ hd : ∑ i, (cut W a b j i).1 = (y j).1, jm (cut W a b j) hd (y j).rep ≠ 0` using `Fin.forall_fin_two.2 ⟨(wd_iff rfl _ (cut_zero W a b)).1 h0, (wd_iff rfl _ (cut_one W a b)).1 h1⟩`. Use `choose hx hj using H`. Establish `hcat : ∑ i, (Zc.Seg.concat ![a, b] (cut W a b) i).1 = x.1`. Use `Eq.trans ?_ hy` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Use `(wd_iff (by simp) _ (concat_cut W a b)).2 ⟨hcat, ENat.one_le_iff_ne_zero.1 ?_⟩` and prove the remaining obligations. Conclude with `(ENat.one_le_iff_ne_zero.2 h).trans (GlobalTheory.CompanionTheory.JmTrans.jm_le_jm_concat hA y hy _ _ hx hcat (fun j => ENat.one_le_iff_ne_zero.2 (hj j)) x.rep x.2.rep.smooth x.2.rep.hasFiniteLength)`.
-/
private theorem wd_up (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) {x : IrrGL k} (y : Fin 2 → IrrGL k)
    (hy : ∑ a, (y a).1 = x.1) (h : jm y hy x.rep ≠ 0) (W : ℕ → IrrGL k) (a b : ℕ) (h0 : Wd W a (y 0))
    (h1 : Wd (fun i => W (a + i)) b (y 1)) : Wd W (a + b) x := by
  have hA : GlobalTheory.Published.IrreducibleAdmissibleGL := fun k _ _ _ _ n V _ _ π => (hBZ k).1 (Fin n) V π
  have H : ∀ j, ∃ hd : ∑ i, (cut W a b j i).1 = (y j).1, jm (cut W a b j) hd (y j).rep ≠ 0 :=
    Fin.forall_fin_two.2 ⟨(wd_iff rfl _ (cut_zero W a b)).1 h0, (wd_iff rfl _ (cut_one W a b)).1 h1⟩
  choose hx hj using H
  have hcat : ∑ i, (Zc.Seg.concat ![a, b] (cut W a b) i).1 = x.1 := by
    refine Eq.trans ?_ hy
    calc _ = ∑ p : Σ j, Fin (![a, b] j), (cut W a b p.1 p.2).1 :=
          Fintype.sum_equiv finSigmaFinEquiv.symm _ _ fun _ => rfl
      _ = ∑ j, ∑ i, (cut W a b j i).1 := Fintype.sum_sigma _
      _ = _ := Finset.sum_congr rfl fun j _ => hx j
  refine (wd_iff (by simp) _ (concat_cut W a b)).2 ⟨hcat, ENat.one_le_iff_ne_zero.1 ?_⟩
  exact (ENat.one_le_iff_ne_zero.2 h).trans (GlobalTheory.CompanionTheory.JmTrans.jm_le_jm_concat hA y hy _ _ hx hcat
    (fun j => ENat.one_le_iff_ne_zero.2 (hj j)) x.rep x.2.rep.smooth x.2.rep.hasFiniteLength)

/- English proof (translation)
Take `⟨hcat, h⟩` from `(wd_iff (by simp) _ (concat_cut W a b)).1 h`. Take `⟨y, hy, h1, h2⟩` from `piece_coarse hBZ _ _ hcat x.rep x.2.rep.smooth x.2.rep.hasFiniteLength h`. Conclude with `⟨y, hy, h1, (wd_iff rfl _ (cut_zero W a b)).2 (h2 0), (wd_iff rfl _ (cut_one W a b)).2 (h2 1)⟩`.
-/
private theorem wd_down (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) {x : IrrGL k} (W : ℕ → IrrGL k) (a b : ℕ)
    (h : Wd W (a + b) x) : ∃ (y : Fin 2 → IrrGL k) (hy : ∑ a, (y a).1 = x.1), jm y hy x.rep ≠ 0 ∧ Wd W a (y 0) ∧
      Wd (fun i => W (a + i)) b (y 1) := by
  obtain ⟨hcat, h⟩ := (wd_iff (by simp) _ (concat_cut W a b)).1 h
  obtain ⟨y, hy, h1, h2⟩ := piece_coarse hBZ _ _ hcat x.rep x.2.rep.smooth x.2.rep.hasFiniteLength h
  exact ⟨y, hy, h1, (wd_iff rfl _ (cut_zero W a b)).2 (h2 0), (wd_iff rfl _ (cut_one W a b)).2 (h2 1)⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hd, h⟩`. Conclude with `GlobalTheory.CompanionTheory.SegFine.eq_of_one_le_jm x x.rep (.refl _) _ hd (ENat.one_le_iff_ne_zero.2 h)`. Introduce and unpack `rfl`. Establish `hf : (fun i : Fin 1 => W i) = fun _ => W 0` using `funext fun i => by simp`.

Use `⟨by simp, ?_⟩` and prove the remaining obligations. Conclude with `(GlobalTheory.CompanionTheory.SegFine.jm_eq_one (W 0) (W 0).rep (.refl _) _ _ hf).trans_ne one_ne_zero`.
-/
private theorem wd_one {W : ℕ → IrrGL k} {x : IrrGL k} : Wd W 1 x ↔ W 0 = x := by
  constructor
  · rintro ⟨hd, h⟩
    exact GlobalTheory.CompanionTheory.SegFine.eq_of_one_le_jm x x.rep (.refl _) _ hd (ENat.one_le_iff_ne_zero.2 h)
  · rintro rfl
    have hf : (fun i : Fin 1 => W i) = fun _ => W 0 := funext fun i => by simp
    refine ⟨by simp, ?_⟩
    exact (GlobalTheory.CompanionTheory.SegFine.jm_eq_one (W 0) (W 0).rep (.refl _) _ _ hf).trans_ne one_ne_zero

/- English proof (translation)
Establish `hA : GlobalTheory.Published.IrreducibleAdmissibleGL` using `fun k _ _ _ _ n V _ _ π => (hBZ k).1 (Fin n) V π`. Take `⟨s, u, e, hu, φ, hφ⟩` from `GlobalTheory.CompanionTheory.CuspEmbed.main hBZ hG k x.1 (GlobalTheory.SplitRead.Irr.ofIrrRep x.2.rep)`. Establish `hd : ∑ i, (u i).1 = x.1` using `by simpa using Fintype.card_congr e`. Take `⟨ψ⟩` from `(GlobalTheory.SmGL.Placing.parInd_jac_placing k _ _ _ e (stdBlocks (fun i => (u i).1) hd) _).1 (piTensor fun i => (u i).rep)`. Set `f : x.rep.IntertwiningMap (prodIrr u hd)` to `ψ.toIntertwiningMap.comp φ`.

Establish `hf : Function.Injective f` using `ψ.toLinearEquiv.injective.comp hφ`. Use `haveI := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible x.2.rep.irr`. Take `⟨v, hv⟩` from `exists_ne (0 : x.2.rep.V)`. Establish `h1` using `GlobalTheory.CompanionTheory.FrobJm.one_le_jm hA u hd x.rep x.2.rep.smooth f ⟨v, fun e => hv (hf (e.trans (map_zero f).symm))⟩`. Break down `s with _ | s` into its components or cases.

Simplify using `at hd`. Use linear arithmetic over natural numbers and integers. Conclude with `⟨s, u, hd, hu, ENat.one_le_iff_ne_zero.1 h1, hasSupport_of_isSubquotient x.2.rep.irr hu (.of_injective f hf)⟩`.
-/
private theorem wd_exists (hG : GlobalTheory.Published.GeometricLemma) (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness)
    (x : IrrGL k) (hx : 0 < x.1) : ∃ (s : ℕ) (u : Fin (s + 1) → IrrGL k) (hd : ∑ i, (u i).1 = x.1),
      (∀ i, (u i).IsCusp) ∧ jm u hd x.rep ≠ 0 ∧ HasSupport x.rep (Finset.univ.val.map u) := by
  have hA : GlobalTheory.Published.IrreducibleAdmissibleGL := fun k _ _ _ _ n V _ _ π => (hBZ k).1 (Fin n) V π
  obtain ⟨s, u, e, hu, φ, hφ⟩ := GlobalTheory.CompanionTheory.CuspEmbed.main hBZ hG k x.1 (GlobalTheory.SplitRead.Irr.ofIrrRep x.2.rep)
  have hd : ∑ i, (u i).1 = x.1 := by simpa using Fintype.card_congr e
  obtain ⟨ψ⟩ := (GlobalTheory.SmGL.Placing.parInd_jac_placing k _ _ _ e (stdBlocks (fun i => (u i).1) hd) _).1
    (piTensor fun i => (u i).rep)
  let f : x.rep.IntertwiningMap (prodIrr u hd) := ψ.toIntertwiningMap.comp φ
  have hf : Function.Injective f := ψ.toLinearEquiv.injective.comp hφ
  haveI := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible x.2.rep.irr
  obtain ⟨v, hv⟩ := exists_ne (0 : x.2.rep.V)
  have h1 := GlobalTheory.CompanionTheory.FrobJm.one_le_jm hA u hd x.rep x.2.rep.smooth f
    ⟨v, fun e => hv (hf (e.trans (map_zero f).symm))⟩
  rcases s with _ | s
  · simp at hd
    omega
  exact ⟨s, u, hd, hu, ENat.one_le_iff_ne_zero.1 h1,
    hasSupport_of_isSubquotient x.2.rep.irr hu (.of_injective f hf)⟩

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `hG hBZ k _ _ _ _ x P q hq h`. Use `⟨fun hP hpos => ?_, fun hP hpos => ?_⟩` and prove the remaining obligations. Take `⟨s, u, hd, hu, hj, hs⟩` from `wd_exists hG hBZ (q 0) hpos`. Set `W : ℕ → IrrGL k` to `fun i => if hi : i < s + 1 then u ⟨i, hi⟩ else q 1`. Establish `h1 : Wd W (s + 1 + 1) x` using `wd_up hBZ q hq h W (s + 1) 1 ((wd_iff rfl u fun i => by simp only [W, dif_pos i.2]).2 ⟨hd, hj⟩) (wd_one.2 (by simp [W]))`.

Rewrite `h1` using `[add_comm]`. Take `⟨y, hy, h2, h3, -⟩` from `wd_down hBZ W 1 (s + 1) h1`. Establish `h4 : y 0 = u 0` using `(wd_one.1 h3).symm.trans (by simp [W])`. Conclude with `⟨_, hs, u 0, Multiset.mem_map_of_mem _ (Finset.mem_univ_val _), h4 ▸ hP y hy (h4 ▸ hu 0) h2⟩`. Take `⟨s, u, hd, hu, hj, hs⟩` from `wd_exists hG hBZ (q 1) hpos`.

Set `W : ℕ → IrrGL k` to `fun i => if hi : 0 < i ∧ i - 1 < s + 1 then u ⟨i - 1, hi.2⟩ else q 0`. Establish `hW : ∀ i : Fin (s + 1), u i = W (1 + i)` using `fun i => by`. Establish `hi : 0 < 1 + i.1 ∧ 1 + i.1 - 1 < s + 1` using `by omega`. Simplify using `only [W, dif_pos hi]`. Conclude with `congrArg u (Fin.ext (by simp))`.

Establish `h1 : Wd W (1 + (s + 1)) x` using `wd_up hBZ q hq h W 1 (s + 1) (wd_one.2 (by simp [W])) ((wd_iff rfl u hW).2 ⟨hd, hj⟩)`. Rewrite `h1` using `[add_comm]`. Take `⟨y, hy, h2, -, h3⟩` from `wd_down hBZ W (s + 1) 1 h1`. Establish `h4 : y 1 = u (Fin.last s)` using `(wd_one.1 h3).symm.trans (by`. Rewrite using `[hW]`.

Conclude with `congrArg W (by simp [add_comm]))`. Conclude with `⟨_, hs, u (Fin.last s), Multiset.mem_map_of_mem _ (Finset.mem_univ_val _), h4 ▸ hP y hy (h4 ▸ hu _) h2⟩`.
-/
theorem UpperTheory.Lit.Full.piece :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x : IrrGL k) (P : Set (IrrGL k)) (q : Fin 2 → IrrGL k) (hq : ∑ a, (q a).1 = x.1), jm q hq x.rep ≠ 0 → (FirstIn x P → 0 < (q 0).1 → ∃ A, HasSupport (q 0).rep A ∧ ∃ y ∈ A, y ∈ P) ∧ (LastIn x P → 0 < (q 1).1 → ∃ A, HasSupport (q 1).rep A ∧ ∃ y ∈ A, y ∈ P) := by
  intro hG hBZ k _ _ _ _ x P q hq h
  refine ⟨fun hP hpos => ?_, fun hP hpos => ?_⟩
  · obtain ⟨s, u, hd, hu, hj, hs⟩ := wd_exists hG hBZ (q 0) hpos
    let W : ℕ → IrrGL k := fun i => if hi : i < s + 1 then u ⟨i, hi⟩ else q 1
    have h1 : Wd W (s + 1 + 1) x := wd_up hBZ q hq h W (s + 1) 1
      ((wd_iff rfl u fun i => by simp only [W, dif_pos i.2]).2 ⟨hd, hj⟩) (wd_one.2 (by simp [W]))
    rw [add_comm] at h1
    obtain ⟨y, hy, h2, h3, -⟩ := wd_down hBZ W 1 (s + 1) h1
    have h4 : y 0 = u 0 := (wd_one.1 h3).symm.trans (by simp [W])
    exact ⟨_, hs, u 0, Multiset.mem_map_of_mem _ (Finset.mem_univ_val _), h4 ▸ hP y hy (h4 ▸ hu 0) h2⟩
  · obtain ⟨s, u, hd, hu, hj, hs⟩ := wd_exists hG hBZ (q 1) hpos
    let W : ℕ → IrrGL k := fun i => if hi : 0 < i ∧ i - 1 < s + 1 then u ⟨i - 1, hi.2⟩ else q 0
    have hW : ∀ i : Fin (s + 1), u i = W (1 + i) := fun i => by
      have hi : 0 < 1 + i.1 ∧ 1 + i.1 - 1 < s + 1 := by omega
      simp only [W, dif_pos hi]
      exact congrArg u (Fin.ext (by simp))
    have h1 : Wd W (1 + (s + 1)) x := wd_up hBZ q hq h W 1 (s + 1) (wd_one.2 (by simp [W]))
      ((wd_iff rfl u hW).2 ⟨hd, hj⟩)
    rw [add_comm] at h1
    obtain ⟨y, hy, h2, -, h3⟩ := wd_down hBZ W (s + 1) 1 h1
    have h4 : y 1 = u (Fin.last s) := (wd_one.1 h3).symm.trans (by
      rw [hW]
      exact congrArg W (by simp [add_comm]))
    exact ⟨_, hs, u (Fin.last s), Multiset.mem_map_of_mem _ (Finset.mem_univ_val _),
      h4 ▸ hP y hy (h4 ▸ hu _) h2⟩
