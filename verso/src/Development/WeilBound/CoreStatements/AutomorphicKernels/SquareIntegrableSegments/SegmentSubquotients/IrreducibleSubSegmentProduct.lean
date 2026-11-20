import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.JacquetModuleFiniteLength
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityPos
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SupportSubschemeEmbeddingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrobeniusReciprocityNonzeroStatement
import Development.WeilBound.CoreStatements.AutomorphicKernels.SquareIntegrableSegments.SegmentSubquotients.ExistsSocleSegmentProductStatement
import Development.WeilBound.CoreStatements.AutomorphicKernels.SquareIntegrableSegments.SegmentSubquotients.ExistsSegmentRepresentationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FineJacquetLengthOneStatement
import Development.WeilBound.CoreStatements.AutomorphicKernels.SquareIntegrableSegments.SegmentSubquotients.FineJacquetSegmentLengthTwoStatement
import Development.WeilBound.CoreStatements.AutomorphicKernels.SquareIntegrableSegments.SegmentSubquotients.FineJacquetSegmentInductionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityConcatStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviIrreducibleTensorDecompositionStatement

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
open GlobalTheory.Parabolic (Embeds)

namespace GlobalTheory.CompanionTheory.LkSegUniq

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Use `haveI := Model.nontrivial_of_isIrreducible hρ`. Take `⟨v, hv⟩` from `exists_ne (0 : V)`. Conclude with `⟨v, fun e => hv (hφ (e.trans (map_zero φ).symm))⟩`.
-/
theorem exists_ne_zero_of_injective {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (hρ : ρ.IsIrreducible)
    (φ : ρ.IntertwiningMap σ) (hφ : Function.Injective φ) : ∃ v, φ v ≠ 0 := by
  haveI := Model.nontrivial_of_isIrreducible hρ
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  exact ⟨v, fun e => hv (hφ (e.trans (map_zero φ).symm))⟩

/- English proof (translation)
Use `haveI := Model.nontrivial_of_isIrreducible hσ`. Take `⟨u, hu⟩` from `exists_ne (0 : W)`. Take `⟨v, rfl⟩` from `hφ u`. Conclude with `⟨v, hu⟩`.
-/
theorem exists_ne_zero_of_surjective {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (hσ : σ.IsIrreducible)
    (φ : ρ.IntertwiningMap σ) (hφ : Function.Surjective φ) : ∃ v, φ v ≠ 0 := by
  haveI := Model.nontrivial_of_isIrreducible hσ
  obtain ⟨u, hu⟩ := exists_ne (0 : W)
  obtain ⟨v, rfl⟩ := hφ u
  exact ⟨v, hu⟩

/- English proof (translation)
Take `⟨S, f, hf⟩` from `h`. Introduce `hb`. Use `haveI := Model.nontrivial_of_isIrreducible hσ`. Take `⟨u, hu⟩` from `exists_ne (0 : W)`. Take `⟨v, rfl⟩` from `hf u`.

Establish `hv : (v : V) ∈ (⊥ : Subrepresentation ρ)` using `hb ▸ trivial`. Establish `hv0 : v = 0` using `Subtype.ext hv`. Conclude with `hu (by rw [hv0, map_zero])`.
-/
theorem bot_ne_top_of_isSubquotient {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (hσ : σ.IsIrreducible)
    (h : IsSubquotient σ ρ) : (⊥ : Subrepresentation ρ) ≠ ⊤ := by
  obtain ⟨S, f, hf⟩ := h
  intro hb
  haveI := Model.nontrivial_of_isIrreducible hσ
  obtain ⟨u, hu⟩ := exists_ne (0 : W)
  obtain ⟨v, rfl⟩ := hf u
  have hv : (v : V) ∈ (⊥ : Subrepresentation ρ) := hb ▸ trivial
  have hv0 : v = 0 := Subtype.ext hv
  exact hu (by rw [hv0, map_zero])

/- English proof (translation)
Proceed by induction on `h : Δ.len using Nat.strong_induction_on generalizing Δ with`. Consider the case `_ n ih`. Establish `h0` using `Δ.len_pos`. Take `h1 | h2 | h3 : n = 1 ∨ n = 2 ∨ 3 ≤ n` from `by omega`. Conclude with `@GlobalTheory.T.fine_jacquet_length_one k _ _ _ _ hA Δ (h.trans h1)`.

Conclude with `@GlobalTheory.TL.fine_jacquet_segment_length_two k _ _ _ _ hA hZ Δ (h.trans h2)`. Conclude with `@GlobalTheory.TL.fine_jacquet_segment_induction k _ _ _ _ hA Δ (h ▸ h3) fun Δ' hlt => ih _ (h ▸ hlt) Δ' rfl`.
-/
theorem fineJac_all (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hZ : GlobalTheory.Published.SegmentRepresentation)
    (Δ : Segment k) : FineJac Δ := by
  induction h : Δ.len using Nat.strong_induction_on generalizing Δ with
  | _ n ih =>
    have h0 := Δ.len_pos
    obtain h1 | h2 | h3 : n = 1 ∨ n = 2 ∨ 3 ≤ n := by omega
    · exact @GlobalTheory.T.fine_jacquet_length_one k _ _ _ _ hA Δ (h.trans h1)
    · exact @GlobalTheory.TL.fine_jacquet_segment_length_two k _ _ _ _ hA hZ Δ (h.trans h2)
    · exact @GlobalTheory.TL.fine_jacquet_segment_induction k _ _ _ _ hA Δ (h ▸ h3) fun Δ' hlt => ih _ (h ▸ hlt) Δ' rfl

/- English proof (translation)
Substitute `hc` using the available equality. Take `⟨z, rfl⟩ : ∃ z, x = fun _ => z` from `⟨x 0, funext fun a => by rw [Subsingleton.elim a 0]⟩`. Use `⟨0, ?_⟩` and prove the remaining obligations. Take `⟨n, c⟩` from `y`. Take `⟨m, c'⟩` from `z`.

Establish `hnm : m = n` using `by simpa using hd`. Substitute `hnm` using the available equality. Take `⟨ψ⟩` from `nonempty_equiv_prodIrr_one (⟨m, c'⟩ : IrrGL k) hd`. Establish `hS` using `(isSocle_self (⟨m, c'⟩ : IrrGL k).2.rep.irr).of_equiv (.refl _) ψ`. Take `⟨a⟩` from `hS.equiv_of_embeds (⟨m, c⟩ : IrrGL k).2.rep.irr ⟨φ, hφ⟩`.

Conclude with `congrArg (Sigma.mk m) (irrCl_eq_iff.2 ⟨a⟩)`.
-/
theorem exists_eq_of_embeds_one {c : ℕ} (hc : c = 1) (x : Fin c → IrrGL k) (y : IrrGL k)
    (hd : ∑ a, (x a).1 = y.1) (φ : y.rep.IntertwiningMap (prodIrr x hd)) (hφ : Function.Injective φ) :
    ∃ a, y = x a := by
  subst hc
  obtain ⟨z, rfl⟩ : ∃ z, x = fun _ => z := ⟨x 0, funext fun a => by rw [Subsingleton.elim a 0]⟩
  refine ⟨0, ?_⟩
  obtain ⟨n, c⟩ := y
  obtain ⟨m, c'⟩ := z
  have hnm : m = n := by simpa using hd
  subst hnm
  obtain ⟨ψ⟩ := nonempty_equiv_prodIrr_one (⟨m, c'⟩ : IrrGL k) hd
  have hS := (isSocle_self (⟨m, c'⟩ : IrrGL k).2.rep.irr).of_equiv (.refl _) ψ
  obtain ⟨a⟩ := hS.equiv_of_embeds (⟨m, c⟩ : IrrGL k).2.rep.irr ⟨φ, hφ⟩
  exact congrArg (Sigma.mk m) (irrCl_eq_iff.2 ⟨a⟩)

/- English proof (translation)
Establish `h1 : ∑ i, (concat c x i).1 = ∑ p : Σ a, Fin (c a), (x p.1 p.2).1` using `Equiv.sum_comp finSigmaFinEquiv.symm (fun p : Σ a, Fin (c a) => (x p.1 p.2).1)`. Rewrite using `[h1, Fintype.sum_sigma, ← hy]`. Conclude with `Finset.sum_congr rfl fun a _ => hx a`.
-/
theorem sum_concat_fst {s N : ℕ} (y : Fin s → IrrGL k) (hy : ∑ a, (y a).1 = N) (c : Fin s → ℕ)
    (x : ∀ a, Fin (c a) → IrrGL k) (hx : ∀ a, ∑ i, (x a i).1 = (y a).1) :
    ∑ i, (concat c x i).1 = N := by
  have h1 : ∑ i, (concat c x i).1 = ∑ p : Σ a, Fin (c a), (x p.1 p.2).1 :=
    Equiv.sum_comp finSigmaFinEquiv.symm (fun p : Σ a, Fin (c a) => (x p.1 p.2).1)
  rw [h1, Fintype.sum_sigma, ← hy]
  exact Finset.sum_congr rfl fun a _ => hx a

/- English proof (translation)
Establish `hemb` using `fun a => GlobalTheory.T.support_subscheme_embedding k (y a).1 _ (y a).rep (y a).2.rep.smooth (y a).2.rep.irr`. Use `choose c x hx hcusp φ hφ using hemb`. Establish `hne : ∀ a, ∃ v, φ a v ≠ 0` using `fun a => exists_ne_zero_of_injective (y a).2.rep.irr (φ a) (hφ a)`. Establish `hjm : ∀ a, 1 ≤ jm (x a) (hx a) (y a).rep` using `fun a => GlobalTheory.CompanionTheory.FrobJm.one_le_jm hA (x a) (hx a) (y a).rep (y a).2.rep.smooth (φ a) (hne a)`. Establish `hcat` using `sum_concat_fst y hy c x hx`.

Establish `hle` using `GlobalTheory.T.jacquet_multiplicity_concat hA y hy c x hx hcat hjm π hs (hasFiniteLength_of_isIrreducible hi)`. Establish `hcc : ∀ i, (concat c x i).IsCusp` using `fun i => hcusp _ _`. Take `⟨hlen, -⟩` from `(fine π hL).2 _ (concat c x) hcat hcc (h1.trans hle)`. Establish `hc1 : ∀ a, 1 ≤ c a` using `fun a => by`. Assume the negation of the conclusion as `hc`.

Establish `hc0 : c a = 0` using `by omega`. Establish `h2` using `hx a`. Establish `h3` using `hpos a`. Establish `: IsEmpty (Fin (c a))` using `by rw [hc0]; infer_instance`. Rewrite `h2` using `[Fintype.sum_empty]`.

Use linear arithmetic over natural numbers and integers. Establish `hsum : ∑ a : Fin Δ.len, 1 = ∑ a, c a` using `by simpa using hlen.symm`. Establish `hc : ∀ a, c a = 1` using `fun a => ((Finset.sum_eq_sum_iff_of_le fun a _ => hc1 a).1 hsum a (Finset.mem_univ a)).symm`. Establish `hyc : ∀ a, (y a).IsCusp` using `fun a => by`. Take `⟨b, hb⟩` from `exists_eq_of_embeds_one (hc a) (x a) (y a) (hx a) (φ a) (hφ a)`.

Conclude with `hb ▸ hcusp a b`. Take `⟨h, hdec⟩` from `(fine π hL).2 _ y hy hyc h1`. Conclude with `funext fun a => by simpa using hdec a`.
-/
theorem eq_dec_of_one_le_jm (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {Δ : Segment k} (fine : FineJac Δ) {N : ℕ}
    {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (hL : IsLSeg Δ π)
    (hs : IsSmooth π) (hi : π.IsIrreducible) (y : Fin Δ.len → IrrGL k) (hy : ∑ a, (y a).1 = N)
    (hpos : ∀ a, 0 < (y a).1) (h1 : 1 ≤ jm y hy π) : y = dec Δ := by
  have hemb := fun a => GlobalTheory.T.support_subscheme_embedding k (y a).1 _ (y a).rep (y a).2.rep.smooth (y a).2.rep.irr
  choose c x hx hcusp φ hφ using hemb
  have hne : ∀ a, ∃ v, φ a v ≠ 0 := fun a =>
    exists_ne_zero_of_injective (y a).2.rep.irr (φ a) (hφ a)
  have hjm : ∀ a, 1 ≤ jm (x a) (hx a) (y a).rep := fun a =>
    GlobalTheory.CompanionTheory.FrobJm.one_le_jm hA (x a) (hx a) (y a).rep (y a).2.rep.smooth (φ a) (hne a)
  have hcat := sum_concat_fst y hy c x hx
  have hle := GlobalTheory.T.jacquet_multiplicity_concat hA y hy c x hx hcat hjm π hs (hasFiniteLength_of_isIrreducible hi)
  have hcc : ∀ i, (concat c x i).IsCusp := fun i => hcusp _ _
  obtain ⟨hlen, -⟩ := (fine π hL).2 _ (concat c x) hcat hcc (h1.trans hle)
  have hc1 : ∀ a, 1 ≤ c a := fun a => by
    by_contra hc
    have hc0 : c a = 0 := by omega
    have h2 := hx a
    have h3 := hpos a
    have : IsEmpty (Fin (c a)) := by rw [hc0]; infer_instance
    rw [Fintype.sum_empty] at h2
    omega
  have hsum : ∑ a : Fin Δ.len, 1 = ∑ a, c a := by simpa using hlen.symm
  have hc : ∀ a, c a = 1 := fun a =>
    ((Finset.sum_eq_sum_iff_of_le fun a _ => hc1 a).1 hsum a (Finset.mem_univ a)).symm
  have hyc : ∀ a, (y a).IsCusp := fun a => by
    obtain ⟨b, hb⟩ := exists_eq_of_embeds_one (hc a) (x a) (y a) (hx a) (φ a) (hφ a)
    exact hb ▸ hcusp a b
  obtain ⟨h, hdec⟩ := (fine π hL).2 _ y hy hyc h1
  exact funext fun a => by simpa using hdec a

/- English proof (translation)
Introduce `k _ _ _ _ hA hZ Δ N hd V _ _ τ hs hi f hf`. Establish `fine : FineJac Δ` using `@fineJac_all k _ _ _ _ hA hZ Δ`. Take `⟨L, hL⟩` from `GlobalTheory.TL.exists_segment_representation hA Δ`. Establish `hN : Δ.deg = N`. Rewrite using `[← hd]`.

Use `show Δ.deg = ∑ _ : Fin Δ.len, Δ.d`. Simplify using `[Segment.deg]`. Substitute `hN` using the available equality. Establish `hone` using `(fine L.ρ hL).1 hd`. Set `e` to `stdBlocks (fun a => (dec Δ a).1) hd`.

Establish `hfl : HasFiniteLength (jac e L.ρ)` using `GlobalTheory.CompanionTheory.JacquetBridge.jacquetFiniteLength k _ _ _ e _ L.ρ L.smooth (hasFiniteLength_of_isIrreducible L.irr)`. Use `haveI : WellFoundedGT (Subrepresentation (jac e L.ρ)) := ((hasFiniteLength_iff_wellFounded _).1 hfl).1`. Establish `h0 : jm (dec Δ) hd L.ρ ≠ 0` using `by rw [hone]; exact one_ne_zero`. Establish `hne : (⊥ : Subrepresentation (jac e L.ρ)) ≠ ⊤` using `bot_ne_top_of_isSubquotient (GlobalTheory.CompanionTheory.FrobJm.piTensor_rep_isIrreducible hA (dec Δ)) (jhMult_ne_zero_iff.1 h0)`. Take `⟨M, hM, -⟩` from `(eq_top_or_exists_le_coatom (⊥ : Subrepresentation (jac e L.ρ))).resolve_left hne`.

Set `q : (jac e L.ρ).IntertwiningMap (subQuot ⊤ M)` to `⟨(Submodule.mkQ _) ∘ₗ LinearMap.codRestrict (⊤ : Subrepresentation (jac e L.ρ)).toSubmodule LinearMap.id (fun v => trivial), fun g => rfl⟩`. Establish `hq : Function.Surjective q`. Introduce `y`. Take `⟨⟨v, hv⟩, rfl⟩` from `Submodule.Quotient.mk_surjective _ y`. Conclude with `⟨v, rfl⟩`.

Establish `hirr : (subQuot ⊤ M).IsIrreducible` using `isIrreducible_subQuot hM.covBy_top`. Establish `hsq : IsSubquotient (subQuot ⊤ M) (jac e L.ρ)` using `.of_surjective q hq`. Take `⟨σ, ⟨ψ⟩⟩` from `GlobalTheory.T.levi_irreducible_tensor_decomposition hA (fun a => (dec Δ a).1) ⟨_, subQuot ⊤ M, hsq.isSmooth (isSmooth_jac e L.smooth), hirr⟩`. Set `y : Fin Δ.len → IrrGL k` to `fun a => ⟨(dec Δ a).1, σ a⟩`. Establish `hy : ∑ a, (y a).1 = Δ.deg` using `hd`.

Set `g : (jac (stdBlocks (fun a => (y a).1) hy) L.ρ).IntertwiningMap (piTensor fun a => (y a).rep)` to `ψ.toIntertwiningMap.comp q`. Establish `hg : Function.Surjective g` using `ψ.toLinearEquiv.surjective.comp hq`. Establish `h1 : 1 ≤ jm y hy L.ρ` using `ENat.one_le_iff_ne_zero.2 (jhMult_ne_zero_iff.2 (IsSubquotient.of_surjective g hg))`. Establish `hyeq : y = dec Δ` using `eq_dec_of_one_le_jm hA fine L.ρ hL L.smooth L.irr y hy (fun a => Δ.d_pos) h1`. Take `⟨w, hw⟩` from `exists_ne_zero_of_surjective (GlobalTheory.CompanionTheory.FrobJm.piTensor_rep_isIrreducible hA y) g hg`.

Establish `hfrob` using `GlobalTheory.T.frobenius_reciprocity_nonzero y hy L.ρ L.smooth g ⟨w, hw⟩`. Establish `htr : ∀ (y' : Fin Δ.len → IrrGL k) (_ : y = y') (hy' : ∑ a, (y' a).1 = Δ.deg), (∃ g : L.ρ.IntertwiningMap (prodIrr y hy), ∃ v, g v ≠ 0) → ∃ g : L.ρ.IntertwiningMap (prodIrr y' hy'), ∃ v, g v ≠ 0`. Introduce and unpack `_ rfl _ h`. Conclude with `h`. Take `⟨g', v, hv⟩` from `htr _ hyeq hd hfrob`.

Establish `hemb : Embeds L.ρ (prodIrr (dec Δ) hd)` using `(isotypic_ne_bot_iff_embeds L.irr).1 (isotypic_ne_bot_iff.2 ⟨g', fun e' => hv (by rw [e']; rfl)⟩)`. Take `⟨S, hS⟩` from `GlobalTheory.TL.exists_socle_segment_product hA Δ hd`. Take `⟨a⟩` from `hS.equiv_of_embeds hi ⟨f, hf⟩`. Take `⟨b⟩` from `hS.equiv_of_embeds L.irr hemb`. Conclude with `hL.of_equiv (b.trans a.symm)`.
-/
theorem isLSeg_of_dec : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hZ : GlobalTheory.Published.SegmentRepresentation) (Δ : Segment k) {N : ℕ}
    (hd : ∑ a, (dec Δ a).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth τ) (hi : τ.IsIrreducible)
    (f : τ.IntertwiningMap (prodIrr (dec Δ) hd)) (hf : Function.Injective f), IsLSeg Δ τ := by
  intro k _ _ _ _ hA hZ Δ N hd V _ _ τ hs hi f hf
  have fine : FineJac Δ := @fineJac_all k _ _ _ _ hA hZ Δ
  obtain ⟨L, hL⟩ := GlobalTheory.TL.exists_segment_representation hA Δ
  have hN : Δ.deg = N := by
    rw [← hd]
    show Δ.deg = ∑ _ : Fin Δ.len, Δ.d
    simp [Segment.deg]
  subst hN
  have hone := (fine L.ρ hL).1 hd
  let e := stdBlocks (fun a => (dec Δ a).1) hd
  have hfl : HasFiniteLength (jac e L.ρ) :=
    GlobalTheory.CompanionTheory.JacquetBridge.jacquetFiniteLength k _ _ _ e _ L.ρ L.smooth (hasFiniteLength_of_isIrreducible L.irr)
  haveI : WellFoundedGT (Subrepresentation (jac e L.ρ)) := ((hasFiniteLength_iff_wellFounded _).1 hfl).1
  have h0 : jm (dec Δ) hd L.ρ ≠ 0 := by rw [hone]; exact one_ne_zero
  have hne : (⊥ : Subrepresentation (jac e L.ρ)) ≠ ⊤ :=
    bot_ne_top_of_isSubquotient (GlobalTheory.CompanionTheory.FrobJm.piTensor_rep_isIrreducible hA (dec Δ)) (jhMult_ne_zero_iff.1 h0)
  obtain ⟨M, hM, -⟩ := (eq_top_or_exists_le_coatom (⊥ : Subrepresentation (jac e L.ρ))).resolve_left hne
  let q : (jac e L.ρ).IntertwiningMap (subQuot ⊤ M) :=
    ⟨(Submodule.mkQ _) ∘ₗ LinearMap.codRestrict (⊤ : Subrepresentation (jac e L.ρ)).toSubmodule
      LinearMap.id (fun v => trivial), fun g => rfl⟩
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨⟨v, hv⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact ⟨v, rfl⟩
  have hirr : (subQuot ⊤ M).IsIrreducible := isIrreducible_subQuot hM.covBy_top
  have hsq : IsSubquotient (subQuot ⊤ M) (jac e L.ρ) := .of_surjective q hq
  obtain ⟨σ, ⟨ψ⟩⟩ := GlobalTheory.T.levi_irreducible_tensor_decomposition hA (fun a => (dec Δ a).1)
    ⟨_, subQuot ⊤ M, hsq.isSmooth (isSmooth_jac e L.smooth), hirr⟩
  let y : Fin Δ.len → IrrGL k := fun a => ⟨(dec Δ a).1, σ a⟩
  have hy : ∑ a, (y a).1 = Δ.deg := hd
  let g : (jac (stdBlocks (fun a => (y a).1) hy) L.ρ).IntertwiningMap (piTensor fun a => (y a).rep) :=
    ψ.toIntertwiningMap.comp q
  have hg : Function.Surjective g := ψ.toLinearEquiv.surjective.comp hq
  have h1 : 1 ≤ jm y hy L.ρ :=
    ENat.one_le_iff_ne_zero.2 (jhMult_ne_zero_iff.2 (IsSubquotient.of_surjective g hg))
  have hyeq : y = dec Δ := eq_dec_of_one_le_jm hA fine L.ρ hL L.smooth L.irr y hy
    (fun a => Δ.d_pos) h1
  obtain ⟨w, hw⟩ := exists_ne_zero_of_surjective (GlobalTheory.CompanionTheory.FrobJm.piTensor_rep_isIrreducible hA y) g hg
  have hfrob := GlobalTheory.T.frobenius_reciprocity_nonzero y hy L.ρ L.smooth g ⟨w, hw⟩
  have htr : ∀ (y' : Fin Δ.len → IrrGL k) (_ : y = y') (hy' : ∑ a, (y' a).1 = Δ.deg),
      (∃ g : L.ρ.IntertwiningMap (prodIrr y hy), ∃ v, g v ≠ 0) →
        ∃ g : L.ρ.IntertwiningMap (prodIrr y' hy'), ∃ v, g v ≠ 0 := by
    rintro _ rfl _ h
    exact h
  obtain ⟨g', v, hv⟩ := htr _ hyeq hd hfrob
  have hemb : Embeds L.ρ (prodIrr (dec Δ) hd) :=
    (isotypic_ne_bot_iff_embeds L.irr).1 (isotypic_ne_bot_iff.2 ⟨g', fun e' => hv (by rw [e']; rfl)⟩)
  obtain ⟨S, hS⟩ := GlobalTheory.TL.exists_socle_segment_product hA Δ hd
  obtain ⟨a⟩ := hS.equiv_of_embeds hi ⟨f, hf⟩
  obtain ⟨b⟩ := hS.equiv_of_embeds L.irr hemb
  exact hL.of_equiv (b.trans a.symm)

end GlobalTheory.CompanionTheory.LkSegUniq

end
