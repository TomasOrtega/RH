import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.SimpleIn
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.ConjMemIwahori
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.BlockFrameConjugationIdentity
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.HopEmb
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.RepsSmul
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.PiHomExt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.LevLaws

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

/- English proof (translation)
Establish `hsing : ∀ {a b : G i}, a⁻¹ * b ∈ U i → (Pi.mulSingle i a : ∀ j, G j)⁻¹ * Pi.mulSingle i b ∈ Subgroup.pi Set.univ U`. Introduce `a b hab j _`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using `using hab`.

Simplify `(U j).one_mem` using `[Pi.mulSingle_eq_of_ne hj]`. Set `f : G i ⧸ U i → (∀ j, G j) ⧸ Subgroup.pi Set.univ U` to `Quotient.lift (fun a => (QuotientGroup.mk (Pi.mulSingle i a) : (∀ j, G j) ⧸ Subgroup.pi Set.univ U)) (by`. Introduce `a b hab`. Conclude with `QuotientGroup.eq.2 (hsing (QuotientGroup.leftRel_apply.1 hab)))`. Establish `hf : ∀ a : G i, f (QuotientGroup.mk a) = QuotientGroup.mk (Pi.mulSingle i a)` using `fun _ => rfl`.

Establish `hinj : Function.Injective f`. Introduce `c c' h`. Proceed by induction on `c using QuotientGroup.induction_on with | _ a => ?_`. Proceed by induction on `c' using QuotientGroup.induction_on with | _ b => ?_`. Rewrite `h` using `[hf, hf, QuotientGroup.eq]`.

Use `h i (Set.mem_univ i)` as an intermediate fact. Simplify `this` using `[QuotientGroup.eq]`. Unfold `hopR`. Use `symm`. Use `finsum_mem_eq_of_bijOn f ⟨?_, hinj.injOn, ?_⟩ ?_` and prove the remaining obligations.

Introduce and unpack `c ⟨u, hu, rfl⟩`. Use `⟨Pi.mulSingle i u, ?_, ?_⟩` and prove the remaining obligations. Introduce `j _`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality.

Simplify using `using hu`. Simplify `(U j).one_mem` using `[Pi.mulSingle_eq_of_ne hj]`. Rewrite using `[hf, Pi.mulSingle_mul]`. Introduce and unpack `c ⟨u, hu, rfl⟩`. Use `⟨QuotientGroup.mk (u i * t), ⟨u i, hu i (Set.mem_univ i), rfl⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[hf, QuotientGroup.eq]`. Introduce `j _`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using the standard rewrite rules.

Simplify `hu j (Set.mem_univ j)` using `[Pi.mulSingle_eq_of_ne hj]`. Introduce `c _`. Establish `hc : (QuotientGroup.mk (f c).out : (∀ j, G j) ⧸ Subgroup.pi Set.univ U) = QuotientGroup.mk (Pi.mulSingle i c.out)`. Rewrite using `[QuotientGroup.out_eq', ← hf, QuotientGroup.out_eq']`. Establish `hu` using `QuotientGroup.eq.1 hc`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_inv_cancel_left]`. Both sides reduce to the same expression. Use `_ = ρ (f c).out (ρ ((f c).out⁻¹ * Pi.mulSingle i c.out) v) := by rw [map_mul]; rfl`. Use `_ = ρ (f c).out v := by rw [hv _ hu]`.
-/
private theorem hopR_single {r : ℕ} {G : Fin r → Type} [∀ i, Group (G i)] {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (∀ i, G i) V) (U : ∀ i, Subgroup (G i)) (i : Fin r) (t : G i) (v : V)
    (hv : ∀ u ∈ Subgroup.pi Set.univ U, ρ u v = v) :
    hopR ρ (Subgroup.pi Set.univ U) (Pi.mulSingle i t) v =
      hopR (ρ.comp (MonoidHom.mulSingle G i)) (U i) t v := by
  have hsing : ∀ {a b : G i}, a⁻¹ * b ∈ U i →
      (Pi.mulSingle i a : ∀ j, G j)⁻¹ * Pi.mulSingle i b ∈ Subgroup.pi Set.univ U := by
    intro a b hab j _
    by_cases hj : j = i
    · subst hj
      simpa using hab
    · simpa [Pi.mulSingle_eq_of_ne hj] using (U j).one_mem
  let f : G i ⧸ U i → (∀ j, G j) ⧸ Subgroup.pi Set.univ U :=
    Quotient.lift (fun a => (QuotientGroup.mk (Pi.mulSingle i a) : (∀ j, G j) ⧸ Subgroup.pi Set.univ U)) (by
      intro a b hab
      exact QuotientGroup.eq.2 (hsing (QuotientGroup.leftRel_apply.1 hab)))
  have hf : ∀ a : G i, f (QuotientGroup.mk a) = QuotientGroup.mk (Pi.mulSingle i a) := fun _ => rfl
  have hinj : Function.Injective f := by
    intro c c' h
    induction c using QuotientGroup.induction_on with | _ a => ?_
    induction c' using QuotientGroup.induction_on with | _ b => ?_
    rw [hf, hf, QuotientGroup.eq] at h
    have := h i (Set.mem_univ i)
    simpa [QuotientGroup.eq] using this
  unfold hopR
  symm
  refine finsum_mem_eq_of_bijOn f ⟨?_, hinj.injOn, ?_⟩ ?_
  · rintro c ⟨u, hu, rfl⟩
    refine ⟨Pi.mulSingle i u, ?_, ?_⟩
    · intro j _
      by_cases hj : j = i
      · subst hj
        simpa using hu
      · simpa [Pi.mulSingle_eq_of_ne hj] using (U j).one_mem
    · rw [hf, Pi.mulSingle_mul]
  · rintro c ⟨u, hu, rfl⟩
    refine ⟨QuotientGroup.mk (u i * t), ⟨u i, hu i (Set.mem_univ i), rfl⟩, ?_⟩
    rw [hf, QuotientGroup.eq]
    intro j _
    by_cases hj : j = i
    · subst hj
      simp
    · simpa [Pi.mulSingle_eq_of_ne hj] using hu j (Set.mem_univ j)
  · intro c _
    have hc : (QuotientGroup.mk (f c).out : (∀ j, G j) ⧸ Subgroup.pi Set.univ U) = QuotientGroup.mk (Pi.mulSingle i c.out) := by
      rw [QuotientGroup.out_eq', ← hf, QuotientGroup.out_eq']
    have hu := QuotientGroup.eq.1 hc
    calc (ρ.comp (MonoidHom.mulSingle G i)) c.out v
        = ρ ((f c).out * ((f c).out⁻¹ * Pi.mulSingle i c.out)) v := by
          rw [mul_inv_cancel_left]; rfl
      _ = ρ (f c).out (ρ ((f c).out⁻¹ * Pi.mulSingle i c.out) v) := by rw [map_mul]; rfl
      _ = ρ (f c).out v := by rw [hv _ hu]

/- English proof (translation)
Introduce `K _ _ _ μ _ μ₂ _ τ₁ τ₂ hP κ e he S U hU D hD d A w hw hUw ν hν M hM`. Choose the witnesses or unpack the hypotheses as in `⟨r, w', hinj, rfl⟩ : ∃ (r : ℕ) (w' : Fin r → Pl K), Function.Injective w' ∧ im w' = S := by`. Use `⟨S.card, fun j => (S.equivFin.symm j : Pl K), ?_, ?_⟩` and prove the remaining obligations. Introduce `a b h`. Conclude with `S.equivFin.symm.injective (Subtype.ext h)`.

Use extensionality with `x`. Simplify using `only [Finset.mem_image, Finset.mem_univ, true_and]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨j, rfl⟩`. Conclude with `(S.equivFin.symm j).2`.

Introduce `hx`. Conclude with `⟨S.equivFin ⟨x, hx⟩, by simp⟩`. Take `⟨i, rfl⟩ : ∃ i, w' i = w` from `by simpa [im] using hw`. Take `⟨⟨ι, hι⟩, hemb⟩` from `embEx (K := K) (2 + 2) w' hinj`. Take `⟨-, -, -, -, -, hmem⟩` from `hemb ι hι`.

Establish `hlev` using `(levLaws (K := K) (2 + 2) (im w')).1 U hU`. Establish `hsec` using `secTr μ₂ τ₁ τ₂ κ e he`. Establish `hz` using `zMem μ₂ τ₁ τ₂ κ e he`. Establish `hZ2` using `hz.2 w' ι hinj hι`. Establish `hflat0 : flat 0 (0 : G1 K (2 + 2) → ℂ) = 0`.

Use function extensionality and compare the values at `x`. Simplify using `[flat]`. Use `(injective_iff_map_eq_zero M).2 fun v hv => ?_` and prove the remaining obligations. Establish `hfS : IsSec τ₁ τ₂ (A.sec v) ∧ D.Fix (A.sec v)` using `(A.onto _).1 ⟨v, rfl⟩`. Establish `hfix` using `(hD.fix _ hfS.1.cont).1 hfS.2`.

Establish `hFφ : FixF (levOn (im w') U) (flat 0 (A.sec v))` using `((hsec.2.1 _ hfS.1.cont).2 _ hlev.2).2 hfix.2`. Establish `hZ : flat 0 (A.sec v) ∈ Zs τ₁ τ₂ κ e (im w')` using `(hz.1 _ _).2 ⟨_, hfS.1, hfix.1, ⟨U, hU, hfix.2⟩, rfl⟩`. Establish `hWfix : ∀ u ∈ Subgroup.pi Set.univ (fun j => U (w' j)), rS ι u (flat 0 (A.sec v)) = flat 0 (A.sec v)`. Introduce `u hu`. Establish `hin : ι u ∈ levOn (im w') U` using `(hmem U _).2 ⟨u, 1, by simp, fun j => hu j (Set.mem_univ j), fun j => by simp [GM.cf], fun x => by simp [GM.cf, one_mem]⟩`.

Use function extensionality and compare the values at `x`. Conclude with `hFφ _ hin x`. Establish `hzero : hopR ((rS ι).comp (MonoidHom.mulSingle (fun j => Gw (2 + 2) (w' j)) i)) (GLnLocal.iwahori ((w' i).adicCompletion K) (2 + 2)) (Cartan.diagPow ((w' i).adicCompletion K) (2 + 2) ν) (flat 0 (A.sec v)) = 0`. Establish `h1` using `hM v`. Rewrite `h1` using `[hv, map_zero, hflat0, ← hι i, hopEmb (2 + 2) w' ι hinj hι U hU _ hFφ, hopR_single (rS ι) (fun j => U (w' j)) i _ _ hWfix, hUw]`.

Conclude with `h1.symm`. Establish `hφ : flat 0 (A.sec v) = 0` using `iwInj (2 + 2) (w' i) ((rS ι).comp (MonoidHom.mulSingle (fun j => Gw (2 + 2) (w' j)) i)) (Zs τ₁ τ₂ κ e (im w')) (fun g φ hφ => (hZ2 φ hφ).2 _) (fun φ hφ => (hZ2 φ hφ).1.preimage (continuous_mulSingle i)) ν hν _ hZ (fun u hu => hWfix _ fun j _ => by`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify `hu` using `[hUw]`.

Simplify `(U (w' j)).one_mem)` using `[Pi.mulSingle_eq_of_ne hj]`. Use `hzero`. Establish `hs0 : A.sec v = 0` using `hsec.2.2.1 _ _ (hφ.trans hflat0.symm)`. Conclude with `A.inj (hs0.trans (map_zero A.sec).symm)`.
-/
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.heckeInj :
    UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.HeckeInj := by
  intro K _ _ _ μ _ μ₂ _ τ₁ τ₂ hP κ e he S U hU D hD d A w hw hUw ν hν M hM
  obtain ⟨r, w', hinj, rfl⟩ : ∃ (r : ℕ) (w' : Fin r → Pl K), Function.Injective w' ∧ im w' = S := by
    refine ⟨S.card, fun j => (S.equivFin.symm j : Pl K), ?_, ?_⟩
    · intro a b h
      exact S.equivFin.symm.injective (Subtype.ext h)
    · ext x
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨j, rfl⟩
        exact (S.equivFin.symm j).2
      · intro hx
        exact ⟨S.equivFin ⟨x, hx⟩, by simp⟩
  obtain ⟨i, rfl⟩ : ∃ i, w' i = w := by simpa [im] using hw
  obtain ⟨⟨ι, hι⟩, hemb⟩ := embEx (K := K) (2 + 2) w' hinj
  obtain ⟨-, -, -, -, -, hmem⟩ := hemb ι hι
  have hlev := (levLaws (K := K) (2 + 2) (im w')).1 U hU
  have hsec := secTr μ₂ τ₁ τ₂ κ e he
  have hz := zMem μ₂ τ₁ τ₂ κ e he
  have hZ2 := hz.2 w' ι hinj hι
  have hflat0 : flat 0 (0 : G1 K (2 + 2) → ℂ) = 0 := by
    funext x
    simp [flat]
  refine (injective_iff_map_eq_zero M).2 fun v hv => ?_
  have hfS : IsSec τ₁ τ₂ (A.sec v) ∧ D.Fix (A.sec v) := (A.onto _).1 ⟨v, rfl⟩
  have hfix := (hD.fix _ hfS.1.cont).1 hfS.2
  have hFφ : FixF (levOn (im w') U) (flat 0 (A.sec v)) := ((hsec.2.1 _ hfS.1.cont).2 _ hlev.2).2 hfix.2
  have hZ : flat 0 (A.sec v) ∈ Zs τ₁ τ₂ κ e (im w') :=
    (hz.1 _ _).2 ⟨_, hfS.1, hfix.1, ⟨U, hU, hfix.2⟩, rfl⟩
  have hWfix : ∀ u ∈ Subgroup.pi Set.univ (fun j => U (w' j)), rS ι u (flat 0 (A.sec v)) = flat 0 (A.sec v) := by
    intro u hu
    have hin : ι u ∈ levOn (im w') U :=
      (hmem U _).2 ⟨u, 1, by simp, fun j => hu j (Set.mem_univ j), fun j => by simp [GM.cf], fun x => by simp [GM.cf, one_mem]⟩
    funext x
    exact hFφ _ hin x
  have hzero : hopR ((rS ι).comp (MonoidHom.mulSingle (fun j => Gw (2 + 2) (w' j)) i))
      (GLnLocal.iwahori ((w' i).adicCompletion K) (2 + 2)) (Cartan.diagPow ((w' i).adicCompletion K) (2 + 2) ν)
      (flat 0 (A.sec v)) = 0 := by
    have h1 := hM v
    rw [hv, map_zero, hflat0, ← hι i, hopEmb (2 + 2) w' ι hinj hι U hU _ hFφ,
      hopR_single (rS ι) (fun j => U (w' j)) i _ _ hWfix, hUw] at h1
    exact h1.symm
  have hφ : flat 0 (A.sec v) = 0 :=
    iwInj (2 + 2) (w' i) ((rS ι).comp (MonoidHom.mulSingle (fun j => Gw (2 + 2) (w' j)) i)) (Zs τ₁ τ₂ κ e (im w'))
      (fun g φ hφ => (hZ2 φ hφ).2 _)
      (fun φ hφ => (hZ2 φ hφ).1.preimage (continuous_mulSingle i))
      ν hν _ hZ
      (fun u hu => hWfix _ fun j _ => by
        by_cases hj : j = i
        · subst hj
          simpa [hUw] using hu
        · simpa [Pi.mulSingle_eq_of_ne hj] using (U (w' j)).one_mem)
      hzero
  have hs0 : A.sec v = 0 := hsec.2.2.1 _ _ (hφ.trans hflat0.symm)
  exact A.inj (hs0.trans (map_zero A.sec).symm)
