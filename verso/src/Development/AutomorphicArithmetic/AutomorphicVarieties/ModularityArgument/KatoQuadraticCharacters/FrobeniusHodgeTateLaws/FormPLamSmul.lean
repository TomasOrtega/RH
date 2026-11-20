import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.ChiQuadAlt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFormCoeffSeqLinearStructureStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsModularFormCoeffSeqHeckeUAndDepletionStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsModularFormCoeffSeqHeckeTOfPrimeNotDvdStatement

open UpperTheory.V.Z.Kato.Joint

/- English proof (translation)
Unfold `GlobalTheory.EisM.lam`. Simplify using `only [Pi.add_apply, mul_add, Finset.sum_add_distrib]`.
-/
private theorem formP_lam_add (B : ℕ) (cc a b : ℕ → ℂ) :
    GlobalTheory.EisM.lam B cc (a + b) = GlobalTheory.EisM.lam B cc a + GlobalTheory.EisM.lam B cc b := by
  unfold GlobalTheory.EisM.lam
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Unfold `GlobalTheory.EisM.lam`. Simplify using `only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun n _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem formP_lam_smul (B : ℕ) (cc a : ℕ → ℂ) (r : ℂ) :
    GlobalTheory.EisM.lam B cc (r • a) = r * GlobalTheory.EisM.lam B cc a := by
  unfold GlobalTheory.EisM.lam
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

/- English proof (translation)
Unfold `UpperTheory.V.Z.Kato.Joint.FormP`. Introduce `l _ ι k N χ t α B cc χE ev hk hE hχE hT hU hD P hP`. Establish `hℓ : Nat.Prime l` using `Fact.out`. It suffices to establish `key : ∀ a : ℕ → Formalism.ConjugateSelfDual.Qbar l, GlobalTheory.EisM.MF k (N * l) (GlobalTheory.EisM.ch χ) (fun i => ι (a i)) → GlobalTheory.EisM.MF k (N * l) (GlobalTheory.EisM.ch χ) (fun i => ι ((FreeAlgebra.lift (Formalism.ConjugateSelfDual.Qbar l) (fop k l χE)) P a i)) ∧ (Gl …`. Unfold `GlobalTheory.KZ.admissibleLettersSubalgebra at hP`.

Proceed by induction on `hP using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Take `⟨x, hx, rfl⟩` from `hx`. Introduce `a ha`. Simplify using `only [FreeAlgebra.lift_ι_apply]`.

Consider the cases of `x with`. Consider the case `T q`. Take `⟨hq, hqn⟩ : Nat.Prime q ∧ ¬q ∣ N * l` from `hx`. Establish `hcop : q.Coprime N` using `Nat.Coprime.coprime_dvd_right (dvd_mul_right N l) ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqn)`. Establish `hχq : ι (χE q) = GlobalTheory.EisM.ch χ (q : ℤ)`.

Rewrite using `[hχE q hcop]`. Simplify using `[GlobalTheory.EisM.ch]`. Establish `hf : (fop k l χE (GlobalTheory.KZ.Letter.T q)) a = GlobalTheory.EisM.To k (χE q) q a` using `rfl`. Establish `hcomm : (fun i => ι (GlobalTheory.EisM.To k (χE q) q a i)) = GlobalTheory.EisM.To k (GlobalTheory.EisM.ch χ (q : ℤ)) q (fun i => ι (a i))`. Use function extensionality and compare the values at `m`.

Simplify using `only [GlobalTheory.EisM.To, GlobalTheory.EisM.Vo, map_add, map_mul, map_pow, map_natCast, hχq]`. Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[hf, hcomm]`. Use `⟨GlobalTheory.T.isModularFormCoeffSeq_heckeT_of_prime_not_dvd k (N * l) N q χ _ hk (dvd_mul_right N l) hq hqn ha, ?_⟩` and prove the remaining obligations. Rewrite using `[hE.T _ ha q hq hqn, hT q hq hqn]`.

Consider the case `U`. Establish `hf : (fop k l χE GlobalTheory.KZ.Letter.U) a = GlobalTheory.EisM.Uo l a` using `rfl`. Establish `hcomm : (fun i => ι (GlobalTheory.EisM.Uo l a i)) = GlobalTheory.EisM.Uo l (fun i => ι (a i))` using `rfl`. Rewrite using `[hf, hcomm]`. Use `⟨(GlobalTheory.T.isModularFormCoeffSeq_heckeU_and_depletion k (N * l) l _ (fun i => ι (a i)) hk hℓ (dvd_mul_left l N) ?_ ha).1, ?_⟩` and prove the remaining obligations.

Introduce `d`. Simplify using `[GlobalTheory.EisM.ch]`. Rewrite using `[hE.U _ ha, hU]`. Consider the case `D d`. Establish `hd : d.Coprime N` using `hx`.

Establish `hf : (fop k l χE (GlobalTheory.KZ.Letter.D d)) a = χE d • a` using `rfl`. Establish `hcomm : (fun i => ι ((χE d • a) i)) = ι (χE d) • fun i => ι (a i)`. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules. Rewrite using `[hf, hcomm, formP_lam_smul, hD d hd]`.

Conclude with `⟨((GlobalTheory.T.modularFormCoeffSeq_linear_structure k (N * l) _).2.2.1 _ _ ha).1, rfl⟩`. Consider the case `algebraMap r`. Introduce `a ha`. Establish `hf : (FreeAlgebra.lift (Formalism.ConjugateSelfDual.Qbar l) (fop k l χE)) (algebraMap (Formalism.ConjugateSelfDual.Qbar l) _ r) a = r • a`. Simplify using `[Algebra.algebraMap_eq_smul_one]`.

Establish `hcomm : (fun i => ι ((r • a) i)) = ι r • fun i => ι (a i)`. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules. Rewrite using `[hf, hcomm, formP_lam_smul, AlgHom.commutes]`. Conclude with `⟨((GlobalTheory.T.modularFormCoeffSeq_linear_structure k (N * l) _).2.2.1 _ _ ha).1, rfl⟩`.

Consider the case `add x y _ _ hx hy`. Introduce `a ha`. Take `⟨h1, h2⟩` from `hx a ha`. Take `⟨h3, h4⟩` from `hy a ha`. Establish `hcomm : (fun i => ι ((FreeAlgebra.lift (Formalism.ConjugateSelfDual.Qbar l) (fop k l χE) (x + y)) a i)) = (fun i => ι (((FreeAlgebra.lift (Formalism.ConjugateSelfDual.Qbar l) (fop k l χE)) x) a i)) + (fun i => ι (((FreeAlgebra.lift (Formalism.ConjugateSelfDual.Qbar l) (fop k l χE …`.

Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules. Rewrite using `[hcomm, formP_lam_add, h2, h4, map_add, map_add, add_mul]`. Conclude with `⟨((GlobalTheory.T.modularFormCoeffSeq_linear_structure k (N * l) _).2.1 _ _ h1 h3).1, rfl⟩`. Consider the case `mul x y _ _ hx hy`.

Introduce `a ha`. Take `⟨h3, h4⟩` from `hy a ha`. Take `⟨h1, h2⟩` from `hx _ h3`. Simplify using `only [map_mul, Module.End.mul_apply]`. Use `⟨h1, ?_⟩` and prove the remaining obligations.

Rewrite using `[h2, h4, mul_assoc]`.
-/
theorem UpperTheory.V.Z.Kato.Joint.LocFacts₂ :
    UpperTheory.V.Z.Kato.Joint.FormP := by
  unfold UpperTheory.V.Z.Kato.Joint.FormP
  intro l _ ι k N χ t α B cc χE ev hk hE hχE hT hU hD P hP
  have hℓ : Nat.Prime l := Fact.out
  suffices key : ∀ a : ℕ → Formalism.ConjugateSelfDual.Qbar l,
      GlobalTheory.EisM.MF k (N * l) (GlobalTheory.EisM.ch χ) (fun i => ι (a i)) →
      GlobalTheory.EisM.MF k (N * l) (GlobalTheory.EisM.ch χ)
                   (fun i => ι ((FreeAlgebra.lift (Formalism.ConjugateSelfDual.Qbar l) (fop k l χE)) P a i)) ∧
        (GlobalTheory.EisM.lam B cc fun i => ι ((FreeAlgebra.lift (Formalism.ConjugateSelfDual.Qbar l) (fop k l χE)) P a i)) =
          ι ((FreeAlgebra.lift (Formalism.ConjugateSelfDual.Qbar l) ev) P) * GlobalTheory.EisM.lam B cc fun i => ι (a i) from
    fun a ha => (key a ha).2
  unfold GlobalTheory.KZ.admissibleLettersSubalgebra at hP
  induction hP using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨x, hx, rfl⟩ := hx
    intro a ha
    simp only [FreeAlgebra.lift_ι_apply]
    cases x with
    | T q =>
      obtain ⟨hq, hqn⟩ : Nat.Prime q ∧ ¬q ∣ N * l := hx
      have hcop : q.Coprime N :=
        Nat.Coprime.coprime_dvd_right (dvd_mul_right N l) ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqn)
      have hχq : ι (χE q) = GlobalTheory.EisM.ch χ (q : ℤ) := by
        rw [hχE q hcop]
        simp [GlobalTheory.EisM.ch]
      have hf : (fop k l χE (GlobalTheory.KZ.Letter.T q)) a = GlobalTheory.EisM.To k (χE q) q a := rfl
      have hcomm : (fun i => ι (GlobalTheory.EisM.To k (χE q) q a i)) =
          GlobalTheory.EisM.To k (GlobalTheory.EisM.ch χ (q : ℤ)) q (fun i => ι (a i)) := by
        funext m
        simp only [GlobalTheory.EisM.To, GlobalTheory.EisM.Vo, map_add, map_mul, map_pow, map_natCast, hχq]
        split_ifs <;> simp
      rw [hf, hcomm]
      refine ⟨GlobalTheory.T.isModularFormCoeffSeq_heckeT_of_prime_not_dvd k (N * l) N q χ _ hk (dvd_mul_right N l) hq hqn ha, ?_⟩
      rw [hE.T _ ha q hq hqn, hT q hq hqn]
    | U =>
      have hf : (fop k l χE GlobalTheory.KZ.Letter.U) a = GlobalTheory.EisM.Uo l a := rfl
      have hcomm : (fun i => ι (GlobalTheory.EisM.Uo l a i)) = GlobalTheory.EisM.Uo l (fun i => ι (a i)) := rfl
      rw [hf, hcomm]
      refine ⟨(GlobalTheory.T.isModularFormCoeffSeq_heckeU_and_depletion k (N * l) l _ (fun i => ι (a i)) hk hℓ (dvd_mul_left l N) ?_ ha).1, ?_⟩
      · intro d
        simp [GlobalTheory.EisM.ch]
      · rw [hE.U _ ha, hU]
    | D d =>
      have hd : d.Coprime N := hx
      have hf : (fop k l χE (GlobalTheory.KZ.Letter.D d)) a = χE d • a := rfl
      have hcomm : (fun i => ι ((χE d • a) i)) = ι (χE d) • fun i => ι (a i) := by
        funext i
        simp
      rw [hf, hcomm, formP_lam_smul, hD d hd]
      exact ⟨((GlobalTheory.T.modularFormCoeffSeq_linear_structure k (N * l) _).2.2.1 _ _ ha).1, rfl⟩
  | algebraMap r =>
    intro a ha
    have hf : (FreeAlgebra.lift (Formalism.ConjugateSelfDual.Qbar l) (fop k l χE)) (algebraMap (Formalism.ConjugateSelfDual.Qbar l) _ r) a = r • a := by
      simp [Algebra.algebraMap_eq_smul_one]
    have hcomm : (fun i => ι ((r • a) i)) = ι r • fun i => ι (a i) := by
      funext i
      simp
    rw [hf, hcomm, formP_lam_smul, AlgHom.commutes]
    exact ⟨((GlobalTheory.T.modularFormCoeffSeq_linear_structure k (N * l) _).2.2.1 _ _ ha).1, rfl⟩
  | add x y _ _ hx hy =>
    intro a ha
    obtain ⟨h1, h2⟩ := hx a ha
    obtain ⟨h3, h4⟩ := hy a ha
    have hcomm : (fun i => ι ((FreeAlgebra.lift (Formalism.ConjugateSelfDual.Qbar l) (fop k l χE) (x + y)) a i)) =
        (fun i => ι (((FreeAlgebra.lift (Formalism.ConjugateSelfDual.Qbar l) (fop k l χE)) x) a i)) +
          (fun i => ι (((FreeAlgebra.lift (Formalism.ConjugateSelfDual.Qbar l) (fop k l χE)) y) a i)) := by
      funext i
      simp
    rw [hcomm, formP_lam_add, h2, h4, map_add, map_add, add_mul]
    exact ⟨((GlobalTheory.T.modularFormCoeffSeq_linear_structure k (N * l) _).2.1 _ _ h1 h3).1, rfl⟩
  | mul x y _ _ hx hy =>
    intro a ha
    obtain ⟨h3, h4⟩ := hy a ha
    obtain ⟨h1, h2⟩ := hx _ h3
    simp only [map_mul, Module.End.mul_apply]
    refine ⟨h1, ?_⟩
    rw [h2, h4, mul_assoc]
