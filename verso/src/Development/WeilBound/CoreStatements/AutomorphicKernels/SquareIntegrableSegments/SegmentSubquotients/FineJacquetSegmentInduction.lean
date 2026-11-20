import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentTermInjectiveStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityCuspidalProductStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicitySubquotientLeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubquotientCuspidalPermutationStatement
import Development.WeilBound.CoreStatements.AutomorphicKernels.SquareIntegrableSegments.SegmentSubquotients.ExistsSegmentRepresentationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentRepSplitIntertwinerStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StrictAntiOfTwoExceptionsStatement
import Development.WeilBound.CoreStatements.AutomorphicKernels.SquareIntegrableSegments.SegmentSubquotients.DerivativeCuspidalPairLengthStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.JacquetModuleFiniteLengthStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityPos
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubquotientJacquetSegmentStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EquivOfMultiplicityOneUniqueFactorStatement

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

noncomputable section

namespace GlobalTheory.CompanionTheory.LkSegFine

/- English proof (translation)
Set `φ : Fin p ⊕ Fin q → Fin c` to `Sum.elim f g`. Establish `hφ : Function.Injective φ`. Introduce and unpack `(x | x) (z | z) h`. Conclude with `congrArg _ (hf h)`. Conclude with `absurd (show g z ∈ Set.range f from ⟨x, h⟩) (Set.disjoint_left.1 hdis · ⟨z, rfl⟩)`.

Conclude with `absurd (show f z ∈ Set.range g from ⟨x, h⟩) (Set.disjoint_right.1 hdis · ⟨z, rfl⟩)`. Conclude with `congrArg _ (hg h)`. Establish `hS : ∑ x : Fin p ⊕ Fin q, deg (φ x) = (p + q) * d`. Simplify using `[Fintype.sum_sum_type, φ, hfd, hgd, add_mul]`. Establish `hsurj : Function.Surjective φ`.

Introduce `a`. Assume the negation of the conclusion as `hne`. Establish `h2 : ∑ b ∈ Finset.univ.image φ, deg b = (p + q) * d`. Rewrite using `[Finset.sum_image hφ.injOn]`. Conclude with `hS`.

Establish `h3 : a ∉ Finset.univ.image φ`. Simplify using `using fun x h => hne ⟨x, h⟩`. Establish `h4 : deg a + ∑ b ∈ Finset.univ.image φ, deg b ≤ ∑ b, deg b`. Rewrite using `[← Finset.sum_insert h3]`. Conclude with `Finset.sum_le_sum_of_subset (Finset.subset_univ _)`.

Use `hpos a` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `⟨fun a => ?_, ?_⟩` and prove the remaining obligations. Take `⟨x | x, rfl⟩` from `hsurj a`. Conclude with `Or.inl ⟨x, rfl⟩`.

Conclude with `Or.inr ⟨x, rfl⟩`. Use `Fintype.card_of_bijective (⟨hφ, hsurj⟩ : Function.Bijective φ)` as an intermediate fact. Simplify using `using this.symm`.
-/
theorem cover {p q c d : ℕ} (deg : Fin c → ℕ) (hpos : ∀ a, 0 < deg a) (hsum : ∑ a, deg a = (p + q) * d)
    (f : Fin p → Fin c) (g : Fin q → Fin c) (hf : Function.Injective f) (hg : Function.Injective g)
    (hdis : Disjoint (Set.range f) (Set.range g)) (hfd : ∀ i, deg (f i) = d) (hgd : ∀ j, deg (g j) = d) :
    (∀ a, a ∈ Set.range f ∨ a ∈ Set.range g) ∧ c = p + q := by
  let φ : Fin p ⊕ Fin q → Fin c := Sum.elim f g
  have hφ : Function.Injective φ := by
    rintro (x | x) (z | z) h
    · exact congrArg _ (hf h)
    · exact absurd (show g z ∈ Set.range f from ⟨x, h⟩) (Set.disjoint_left.1 hdis · ⟨z, rfl⟩)
    · exact absurd (show f z ∈ Set.range g from ⟨x, h⟩) (Set.disjoint_right.1 hdis · ⟨z, rfl⟩)
    · exact congrArg _ (hg h)
  have hS : ∑ x : Fin p ⊕ Fin q, deg (φ x) = (p + q) * d := by
    simp [Fintype.sum_sum_type, φ, hfd, hgd, add_mul]
  have hsurj : Function.Surjective φ := by
    intro a
    by_contra hne
    have h2 : ∑ b ∈ Finset.univ.image φ, deg b = (p + q) * d := by
      rw [Finset.sum_image hφ.injOn]; exact hS
    have h3 : a ∉ Finset.univ.image φ := by
      simpa using fun x h => hne ⟨x, h⟩
    have h4 : deg a + ∑ b ∈ Finset.univ.image φ, deg b ≤ ∑ b, deg b := by
      rw [← Finset.sum_insert h3]
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    have := hpos a
    omega
  refine ⟨fun a => ?_, ?_⟩
  · obtain ⟨x | x, rfl⟩ := hsurj a
    · exact Or.inl ⟨x, rfl⟩
    · exact Or.inr ⟨x, rfl⟩
  · have := Fintype.card_of_bijective (⟨hφ, hsurj⟩ : Function.Bijective φ)
    simpa using this.symm

/- English proof (translation)
Establish `hex : ∀ a, ∃ n, n < l ∧ y a = t n` using `fun a => by`. Break down `hcov a with rfl | ⟨j, rfl⟩` into its components or cases. Conclude with `⟨0, by omega, hi⟩`. Conclude with `⟨_, by omega, hg j⟩`. Use `choose w hw hyw using hex`.

Establish `hwi : w i = 0` using `hinj _ _ (hw i) (by omega) ((hyw i).symm.trans hi)`. Establish `hwi' : w i' = l - 1` using `hinj _ _ (hw i') (by omega) ((hyw i').symm.trans hi')`. Establish `hwg : ∀ j, w (g j) = l - 1 - j` using `fun j => hinj _ _ (hw _) (by omega) ((hyw _).symm.trans (hg j))`. Establish `hwf : ∀ j, w (f j) = l - 2 - j` using `fun j => hinj _ _ (hw _) (by omega) ((hyw _).symm.trans (hf j))`. Establish `h1 : ∀ a b, a < b → a ≠ i → b ≠ i → w b < w a`.

Introduce `a b hab ha hb`. Take `⟨ja, rfl⟩` from `(hcov a).resolve_left ha`. Take `⟨jb, rfl⟩` from `(hcov b).resolve_left hb`. Establish `h2 : ja < jb` using `g.lt_iff_lt.1 hab`. Establish `h3` using `Fin.lt_def.1 h2`.

Establish `h4` using `jb.2`. Rewrite using `[hwg, hwg]`. Use linear arithmetic over natural numbers and integers. Establish `h2 : ∀ a b, a < b → a ≠ i' → b ≠ i' → w b < w a`. Introduce `a b hab ha hb`.

Take `⟨ja, rfl⟩` from `(hcov' a).resolve_left ha`. Take `⟨jb, rfl⟩` from `(hcov' b).resolve_left hb`. Establish `h2 : ja < jb` using `f.lt_iff_lt.1 hab`. Establish `h3` using `Fin.lt_def.1 h2`. Establish `h4` using `jb.2`.

Rewrite using `[hwf, hwf]`. Use linear arithmetic over natural numbers and integers. Establish `hanti : StrictAnti w` using `GlobalTheory.T.strict_anti_of_two_exceptions l hl w hw i i' hwi hwi' h1 h2`. Set `φ : Fin l → Fin l` to `fun a => Fin.rev ⟨w a, hw a⟩`. Establish `hφ : StrictMono φ` using `fun a b hab => Fin.rev_lt_rev.2 (Fin.lt_def.2 (hanti hab))`.

Establish `h3 : φ a = a` using `le_antisymm hφ.apply_le hφ.le_apply`. Establish `h4 : l - (w a + 1) = a`. Use `congrArg Fin.val h3` as an intermediate fact. Simplify `this` using `[φ, Fin.val_rev]`. Establish `h5` using `hw a`.

Establish `h6 : w a = l - 1 - a` using `by omega`. Rewrite using `[hyw a, h6]`.
-/
theorem word_eq_decreasing {X : Type*} (l : ℕ) (hl : 3 ≤ l) (t : ℕ → X)
    (hinj : ∀ a b, a < l → b < l → t a = t b → a = b) (y : Fin l → X)
    (i : Fin l) (g : Fin (l - 1) ↪o Fin l) (hcov : ∀ a, a = i ∨ a ∈ Set.range g) (hi : y i = t 0)
    (hg : ∀ j : Fin (l - 1), y (g j) = t (l - 1 - j))
    (i' : Fin l) (f : Fin (l - 1) ↪o Fin l) (hcov' : ∀ a, a = i' ∨ a ∈ Set.range f) (hi' : y i' = t (l - 1))
    (hf : ∀ j : Fin (l - 1), y (f j) = t (l - 2 - j)) (a : Fin l) : y a = t (l - 1 - a) := by
  have hex : ∀ a, ∃ n, n < l ∧ y a = t n := fun a => by
    rcases hcov a with rfl | ⟨j, rfl⟩
    · exact ⟨0, by omega, hi⟩
    · exact ⟨_, by omega, hg j⟩
  choose w hw hyw using hex
  have hwi : w i = 0 := hinj _ _ (hw i) (by omega) ((hyw i).symm.trans hi)
  have hwi' : w i' = l - 1 := hinj _ _ (hw i') (by omega) ((hyw i').symm.trans hi')
  have hwg : ∀ j, w (g j) = l - 1 - j := fun j => hinj _ _ (hw _) (by omega) ((hyw _).symm.trans (hg j))
  have hwf : ∀ j, w (f j) = l - 2 - j := fun j =>
    hinj _ _ (hw _) (by omega) ((hyw _).symm.trans (hf j))
  have h1 : ∀ a b, a < b → a ≠ i → b ≠ i → w b < w a := by
    intro a b hab ha hb
    obtain ⟨ja, rfl⟩ := (hcov a).resolve_left ha
    obtain ⟨jb, rfl⟩ := (hcov b).resolve_left hb
    have h2 : ja < jb := g.lt_iff_lt.1 hab
    have h3 := Fin.lt_def.1 h2
    have h4 := jb.2
    rw [hwg, hwg]
    omega
  have h2 : ∀ a b, a < b → a ≠ i' → b ≠ i' → w b < w a := by
    intro a b hab ha hb
    obtain ⟨ja, rfl⟩ := (hcov' a).resolve_left ha
    obtain ⟨jb, rfl⟩ := (hcov' b).resolve_left hb
    have h2 : ja < jb := f.lt_iff_lt.1 hab
    have h3 := Fin.lt_def.1 h2
    have h4 := jb.2
    rw [hwf, hwf]
    omega
  have hanti : StrictAnti w := GlobalTheory.T.strict_anti_of_two_exceptions l hl w hw i i' hwi hwi' h1 h2
  let φ : Fin l → Fin l := fun a => Fin.rev ⟨w a, hw a⟩
  have hφ : StrictMono φ := fun a b hab => Fin.rev_lt_rev.2 (Fin.lt_def.2 (hanti hab))
  have h3 : φ a = a := le_antisymm hφ.apply_le hφ.le_apply
  have h4 : l - (w a + 1) = a := by
    have := congrArg Fin.val h3
    simpa [φ, Fin.val_rev] using this
  have h5 := hw a
  have h6 : w a = l - 1 - a := by omega
  rw [hyw a, h6]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Use `show ∑ _ : Fin Γ.len, Γ.d = _`. Simplify using `[Segment.deg]`.
-/
theorem sum_dec_fst (Γ : Segment k) : ∑ a, (dec Γ a).1 = Γ.deg := by
  show ∑ _ : Fin Γ.len, Γ.d = _
  simp [Segment.deg]

/- English proof (translation)
The claim follows from `Γ.isCusp_term _`.
-/
theorem isCusp_dec (Γ : Segment k) (a : Fin Γ.len) : (dec Γ a).IsCusp := Γ.isCusp_term _

/- English proof (translation)
Substitute `e` using the available equality. Both sides reduce to the same expression.
-/
theorem jm_congr {h N : ℕ} {x x' : Fin h → IrrGL k} (e : x = x') (hd : ∑ a, (x a).1 = N) (hd' : ∑ a, (x' a).1 = N)
    {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) : jm x hd π = jm x' hd' π := by
  subst e
  rfl

/- English proof (translation)
Establish `hi : (i : ℕ) < a` using `i.2`. Establish `e : ((Fin.rev i : Fin (segLow Δ a h0).len) : ℕ) = a - 1 - i`. Rewrite using `[Fin.val_rev]`. Use `show a - ((i : ℕ) + 1) = _`. Use linear arithmetic over natural numbers and integers.

Use `show Δ.first.nu (((Fin.rev i : Fin (segLow Δ a h0).len) : ℕ) : ℂ) = _`. Rewrite using `[e]`.
-/
theorem dec_segLow (Δ : Segment k) (a : ℕ) (h0 : 0 < a) (i : Fin (segLow Δ a h0).len) :
    dec (segLow Δ a h0) i = Δ.first.nu ((a - 1 - (i : ℕ) : ℕ) : ℂ) := by
  have hi : (i : ℕ) < a := i.2
  have e : ((Fin.rev i : Fin (segLow Δ a h0).len) : ℕ) = a - 1 - i := by
    rw [Fin.val_rev]
    show a - ((i : ℕ) + 1) = _
    omega
  show Δ.first.nu (((Fin.rev i : Fin (segLow Δ a h0).len) : ℕ) : ℂ) = _
  rw [e]

/- English proof (translation)
Establish `hj : (j : ℕ) < Δ.len - a` using `j.2`. Establish `e : ((Fin.rev j : Fin (segHigh Δ a h1).len) : ℕ) = Δ.len - a - 1 - j`. Rewrite using `[Fin.val_rev]`. Use `show Δ.len - a - ((j : ℕ) + 1) = _`. Use linear arithmetic over natural numbers and integers.

Use `show (Δ.first.nu ((a : ℕ) : ℂ)).nu (((Fin.rev j : Fin (segHigh Δ a h1).len) : ℕ) : ℂ) = _`. Rewrite using `[e, IrrGL.nu_nu]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem dec_segHigh (Δ : Segment k) (a : ℕ) (h1 : a < Δ.len) (j : Fin (segHigh Δ a h1).len) :
    dec (segHigh Δ a h1) j = Δ.first.nu ((a + (Δ.len - a - 1 - (j : ℕ)) : ℕ) : ℂ) := by
  have hj : (j : ℕ) < Δ.len - a := j.2
  have e : ((Fin.rev j : Fin (segHigh Δ a h1).len) : ℕ) = Δ.len - a - 1 - j := by
    rw [Fin.val_rev]
    show Δ.len - a - ((j : ℕ) + 1) = _
    omega
  show (Δ.first.nu ((a : ℕ) : ℂ)).nu (((Fin.rev j : Fin (segHigh Δ a h1).len) : ℕ) : ℂ) = _
  rw [e, IrrGL.nu_nu]
  push_cast
  rfl

/- English proof (translation)
Take `⟨τ, hd, hc⟩` from `GlobalTheory.TL.exists_segment_representation hA Γ`. Conclude with `⟨IrrGL.of τ.ρ τ.smooth τ.irr, rfl, hd, hc.of_equiv (IrrGL.equivOf _ _ _) (Representation.Equiv.refl _)⟩`.
-/
theorem exists_class (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Γ : Segment k) :
    ∃ u : IrrGL k, u.1 = Γ.deg ∧ IsLSeg Γ u.rep := by
  obtain ⟨τ, hd, hc⟩ := GlobalTheory.TL.exists_segment_representation hA Γ
  exact ⟨IrrGL.of τ.ρ τ.smooth τ.irr, rfl, hd, hc.of_equiv (IrrGL.equivOf _ _ _) (Representation.Equiv.refl _)⟩

/- English proof (translation)
Establish `hJ : HasFiniteLength (jac (stdBlocks (fun i => (dec Γ i).1) hs) u.rep)` using `GlobalTheory.T.jacquet_module_finite_length k _ _ _ _ _ _ u.2.rep.smooth (hasFiniteLength_of_isIrreducible u.2.rep.irr)`. Conclude with `GlobalTheory.T.equiv_of_multiplicity_one_unique_factor _ _ (GlobalTheory.CompanionTheory.FrobJm.piTensor_rep_isIrreducible hA (dec Γ)) hJ ((hF u.rep hu).1 hs) fun X _ _ ρ hi hq => GlobalTheory.T.irreducible_subquotient_jacquet_segment hA Γ hF u hu hs X ρ hi hq`.
-/
theorem fine_tensor (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Γ : Segment k) (hF : FineJac Γ) (u : IrrGL k)
    (hu : IsLSeg Γ u.rep) (hs : ∑ i, (dec Γ i).1 = u.1) :
    Nonempty ((jac (stdBlocks (fun i => (dec Γ i).1) hs) u.rep).Equiv (piTensor fun i => (dec Γ i).rep)) := by
  have hJ : HasFiniteLength (jac (stdBlocks (fun i => (dec Γ i).1) hs) u.rep) :=
    GlobalTheory.T.jacquet_module_finite_length k _ _ _ _ _ _ u.2.rep.smooth (hasFiniteLength_of_isIrreducible u.2.rep.irr)
  exact GlobalTheory.T.equiv_of_multiplicity_one_unique_factor _ _ (GlobalTheory.CompanionTheory.FrobJm.piTensor_rep_isIrreducible hA (dec Γ)) hJ ((hF u.rep hu).1 hs)
    fun X _ _ ρ hi hq => GlobalTheory.T.irreducible_subquotient_jacquet_segment hA Γ hF u hu hs X ρ hi hq

/- English proof (translation)
Take `⟨u, hu1, hu⟩` from `exists_class hA (segLow Δ a h0)`. Take `⟨v, hv1, hv⟩` from `exists_class hA (segHigh Δ a h1)`. Establish `hN : N = Δ.len * Δ.d`. Take `⟨hd, -⟩` from `hπ`. Rewrite using `[← hd, Segment.sum_term_fst]`.

Both sides reduce to the same expression. Establish `hd : ∑ i, (![u, v] i).1 = N`. Establish `e1 : (segLow Δ a h0).deg = a * Δ.d` using `rfl`. Establish `e2 : (segHigh Δ a h1).deg = (Δ.len - a) * Δ.d` using `rfl`. Rewrite using `[Fin.sum_univ_two]`.

Use `show u.1 + v.1 = N`. Rewrite using `[hu1, hv1, e1, e2, ← Nat.add_mul, Nat.add_sub_cancel' h1.le, hN]`. Take `⟨φ, hφ⟩` from `GlobalTheory.T.segment_rep_split_intertwiner hA Δ π hπ a h0 h1 u v hu hv hd`. Establish `hle` using `GlobalTheory.T.jacquet_multiplicity_subquotient_le y hy π _ (isSmooth_prodIrr _ hd) (.of_surjective φ hφ)`. Establish `hs : ∑ i, (dec (segLow Δ a h0) i).1 = u.1` using `by rw [sum_dec_fst, hu1]`.

Establish `ht : ∑ i, (dec (segHigh Δ a h1) i).1 = v.1` using `by rw [sum_dec_fst, hv1]`. Conclude with `GlobalTheory.TL.derivative_cuspidal_pair_length hA u v _ _ hs ht Δ.d (fun _ => rfl) (fun _ => rfl) (isCusp_dec _) (isCusp_dec _) (fine_tensor hA _ hlow u hu hs) (fine_tensor hA _ hhigh v hv ht) hd y hy hyc (h.trans hle)`.
-/
theorem shuffle_step (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) {N : ℕ} {V : Type} [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (hπ : IsLSeg Δ π) (a : ℕ) (h0 : 0 < a) (h1 : a < Δ.len)
    (hlow : FineJac (segLow Δ a h0)) (hhigh : FineJac (segHigh Δ a h1)) {c : ℕ} (y : Fin c → IrrGL k)
    (hy : ∑ i, (y i).1 = N) (hyc : ∀ i, (y i).IsCusp) (h : 1 ≤ jm y hy π) :
    ∃ (f : Fin (segLow Δ a h0).len ↪o Fin c) (g : Fin (segHigh Δ a h1).len ↪o Fin c),
      Disjoint (Set.range f) (Set.range g) ∧ (∀ i, y (f i) = dec (segLow Δ a h0) i) ∧
        ∀ j, y (g j) = dec (segHigh Δ a h1) j := by
  obtain ⟨u, hu1, hu⟩ := exists_class hA (segLow Δ a h0)
  obtain ⟨v, hv1, hv⟩ := exists_class hA (segHigh Δ a h1)
  have hN : N = Δ.len * Δ.d := by
    obtain ⟨hd, -⟩ := hπ
    rw [← hd, Segment.sum_term_fst]
    rfl
  have hd : ∑ i, (![u, v] i).1 = N := by
    have e1 : (segLow Δ a h0).deg = a * Δ.d := rfl
    have e2 : (segHigh Δ a h1).deg = (Δ.len - a) * Δ.d := rfl
    rw [Fin.sum_univ_two]
    show u.1 + v.1 = N
    rw [hu1, hv1, e1, e2, ← Nat.add_mul, Nat.add_sub_cancel' h1.le, hN]
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.segment_rep_split_intertwiner hA Δ π hπ a h0 h1 u v hu hv hd
  have hle := GlobalTheory.T.jacquet_multiplicity_subquotient_le y hy π _ (isSmooth_prodIrr _ hd) (.of_surjective φ hφ)
  have hs : ∑ i, (dec (segLow Δ a h0) i).1 = u.1 := by rw [sum_dec_fst, hu1]
  have ht : ∑ i, (dec (segHigh Δ a h1) i).1 = v.1 := by rw [sum_dec_fst, hv1]
  exact GlobalTheory.TL.derivative_cuspidal_pair_length hA u v _ _ hs ht Δ.d (fun _ => rfl) (fun _ => rfl) (isCusp_dec _) (isCusp_dec _)
    (fine_tensor hA _ hlow u hu hs) (fine_tensor hA _ hhigh v hv ht) hd y hy hyc (h.trans hle)

/- English proof (translation)
Introduce `N V _ _ π hπ`. Take `⟨hd0, hc⟩` from `id hπ`. Establish `hsub` using `hc.isSubquotient`. Establish `hsm : IsSmooth π` using `hsub.isSmooth (isSmooth_prodIrr _ _)`. Establish `hN : N = Δ.len * Δ.d`.

Rewrite using `[← hd0, Segment.sum_term_fst]`. Both sides reduce to the same expression. Establish `shape : ∀ (c : ℕ) (y : Fin c → IrrGL k) (hy : ∑ a, (y a).1 = N), (∀ a, (y a).IsCusp) → 1 ≤ jm y hy π → ∃ h : c = Δ.len, ∀ a, y a = dec Δ (Fin.cast h a)`. Introduce `c y hy hyc h`. Establish `hl1 : 1 < Δ.len` using `by omega`.

Establish `hl2 : Δ.len - 1 < Δ.len` using `by omega`. Establish `hl0 : 0 < Δ.len - 1` using `by omega`. Take `⟨f₁, g₁, dis₁, hf₁, hg₁⟩` from `shuffle_step hA Δ π hπ 1 one_pos hl1 (ih _ (show 1 < Δ.len from hl1)) (ih _ (show Δ.len - 1 < Δ.len from hl2)) y hy hyc h`. Take `⟨f₂, g₂, dis₂, hf₂, hg₂⟩` from `shuffle_step hA Δ π hπ (Δ.len - 1) hl0 hl2 (ih _ (show Δ.len - 1 < Δ.len from hl2)) (ih _ (show Δ.len - (Δ.len - 1) < Δ.len by omega)) y hy hyc h`. Establish `hpos : ∀ a, 0 < (y a).1` using `fun a => (hyc a).1`.

Take `⟨cov₁, hc₁⟩` from `cover (p := 1) (q := Δ.len - 1) (d := Δ.d) (fun a => (y a).1) hpos (by rw [hy, hN, Nat.add_sub_cancel' hl1.le]) f₁ g₁ f₁.injective g₁.injective dis₁ (fun i => congrArg Sigma.fst (hf₁ i)) (fun i => congrArg Sigma.fst (hg₁ i))`. Take `⟨cov₂, -⟩` from `cover (p := Δ.len - 1) (q := Δ.len - (Δ.len - 1)) (d := Δ.d) (fun a => (y a).1) hpos (by rw [hy, hN, Nat.add_sub_cancel' hl2.le]) f₂ g₂ f₂.injective g₂.injective dis₂ (fun i => congrArg Sigma.fst (hf₂ i)) (fun i => congrArg Sigma.fst (hg₂ i))`. Establish `hcl : c = Δ.len` using `by omega`. Substitute `hcl` using the available equality. Establish `e : ∀ {m n : ℕ}, m = n → Δ.first.nu ((m : ℕ) : ℂ) = Δ.first.nu ((n : ℕ) : ℂ)`.

Introduce and unpack `m _ rfl`. Both sides reduce to the same expression. Establish `hinj : ∀ a b, a < Δ.len → b < Δ.len → Δ.first.nu ((a : ℕ) : ℂ) = Δ.first.nu ((b : ℕ) : ℂ) → a = b` using `fun a b ha hb hab => congrArg Fin.val (GlobalTheory.T.segment_term_injective hA Δ (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) hab)`. Establish `z₁ : 0 < (segLow Δ 1 one_pos).len` using `one_pos`. Establish `z₂ : 0 < (segHigh Δ (Δ.len - 1) hl2).len` using `by show 0 < Δ.len - (Δ.len - 1)`.

Use linear arithmetic over natural numbers and integers. Use `⟨rfl, fun a => ?_⟩` and prove the remaining obligations. Use `(word_eq_decreasing Δ.len h3 (fun n => Δ.first.nu ((n : ℕ) : ℂ)) hinj y (f₁ ⟨0, z₁⟩) g₁ (fun a => ?_) ?_ (fun j => ?_) (g₂ ⟨0, z₂⟩) f₂ (fun a => ?_) ?_ (fun j => ?_) a).trans ?_` and prove the remaining obligations. Break down `cov₁ a with ⟨x, rfl⟩ | h` into its components or cases. Establish `hx : (x : ℕ) < 1` using `x.2`.

Conclude with `Or.inl (congrArg f₁ (Fin.ext (by show (x : ℕ) = 0; omega)))`. Conclude with `Or.inr h`. Conclude with `(hf₁ _).trans ((dec_segLow _ _ _ _).trans (e (by simp)))`. Establish `hj` using `j.2`. Conclude with `(hg₁ j).trans ((dec_segHigh _ _ _ _).trans (e (by`.

Establish `: ((j : Fin (segHigh Δ 1 hl1).len) : ℕ) = j` using `rfl`. Use the proof step `omega)))`. Break down `cov₂ a with h | ⟨x, rfl⟩` into its components or cases. Conclude with `Or.inr h`. Establish `hx : (x : ℕ) < Δ.len - (Δ.len - 1)` using `x.2`.

Conclude with `Or.inl (congrArg g₂ (Fin.ext (by show (x : ℕ) = 0; omega)))`. Conclude with `(hg₂ _).trans ((dec_segHigh _ _ _ _).trans (e (by simp; omega)))`. Establish `hj` using `j.2`. Conclude with `(hf₂ j).trans ((dec_segLow _ _ _ _).trans (e (by`. Establish `: ((j : Fin (segLow Δ (Δ.len - 1) hl0).len) : ℕ) = j` using `rfl`.

Use the proof step `omega)))`. Establish `ha` using `a.2`. Establish `e₂ : ((Fin.rev (Fin.cast rfl a) : Fin Δ.len) : ℕ) = Δ.len - 1 - a`. Rewrite using `[Fin.val_rev]`. Simplify using `only [Fin.val_cast]`.

Use linear arithmetic over natural numbers and integers. Use `show _ = Δ.first.nu (((Fin.rev (Fin.cast rfl a) : Fin Δ.len) : ℕ) : ℂ)`. Rewrite using `[e₂]`. Use `⟨fun hd => ?_, shape⟩` and prove the remaining obligations. Establish `hinj` using `GlobalTheory.T.segment_term_injective hA Δ`.

Establish `hset : {e : Fin Δ.len ≃ Fin Δ.len | ∀ a, dec Δ a = Δ.term (e a)} = {Fin.revPerm}`. Use extensionality with `e`. Simplify using `only [Set.mem_setOf_eq, Set.mem_singleton_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Conclude with `Equiv.ext fun a => (hinj (h a)).symm`. Introduce and unpack `rfl a`. Both sides reduce to the same expression. Establish `hup : jm (dec Δ) hd π ≤ 1`. Use `(GlobalTheory.T.jacquet_multiplicity_subquotient_le (dec Δ) hd π _ (isSmooth_prodIrr _ hd0) hsub).trans ?_` and prove the remaining obligations.

Rewrite using `[GlobalTheory.T.jacquet_multiplicity_cuspidal_product hA Δ.term (dec Δ) hd0 hd Δ.isCusp_term (isCusp_dec Δ), hset, Set.ncard_singleton]`. Simplify using the standard rewrite rules. Take `⟨e, he, h1⟩` from `GlobalTheory.T.irreducible_subquotient_cuspidal_permutation hA Δ.term hd0 Δ.isCusp_term π hsm hc.1 hsub`. Take `⟨h, hh⟩` from `shape Δ.len _ he (fun a => Δ.isCusp_term _) h1`. Establish `hfun : (fun a => Δ.term (e a)) = dec Δ` using `funext fun a => hh a`.

Rewrite `h1` using `[jm_congr hfun he hd]`. Conclude with `le_antisymm hup h1`.
-/
theorem fineJac_step (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) (h3 : 3 ≤ Δ.len)
    (ih : ∀ Δ' : Segment k, Δ'.len < Δ.len → FineJac Δ') : FineJac Δ := by
  intro N V _ _ π hπ
  obtain ⟨hd0, hc⟩ := id hπ
  have hsub := hc.isSubquotient
  have hsm : IsSmooth π := hsub.isSmooth (isSmooth_prodIrr _ _)
  have hN : N = Δ.len * Δ.d := by
    rw [← hd0, Segment.sum_term_fst]
    rfl
  have shape : ∀ (c : ℕ) (y : Fin c → IrrGL k) (hy : ∑ a, (y a).1 = N), (∀ a, (y a).IsCusp) → 1 ≤ jm y hy π →
      ∃ h : c = Δ.len, ∀ a, y a = dec Δ (Fin.cast h a) := by
    intro c y hy hyc h
    have hl1 : 1 < Δ.len := by omega
    have hl2 : Δ.len - 1 < Δ.len := by omega
    have hl0 : 0 < Δ.len - 1 := by omega
    obtain ⟨f₁, g₁, dis₁, hf₁, hg₁⟩ := shuffle_step hA Δ π hπ 1 one_pos hl1
      (ih _ (show 1 < Δ.len from hl1)) (ih _ (show Δ.len - 1 < Δ.len from hl2)) y hy hyc h
    obtain ⟨f₂, g₂, dis₂, hf₂, hg₂⟩ := shuffle_step hA Δ π hπ (Δ.len - 1) hl0 hl2
      (ih _ (show Δ.len - 1 < Δ.len from hl2)) (ih _ (show Δ.len - (Δ.len - 1) < Δ.len by omega)) y hy hyc h
    have hpos : ∀ a, 0 < (y a).1 := fun a => (hyc a).1
    obtain ⟨cov₁, hc₁⟩ := cover (p := 1) (q := Δ.len - 1) (d := Δ.d) (fun a => (y a).1) hpos
      (by rw [hy, hN, Nat.add_sub_cancel' hl1.le]) f₁ g₁ f₁.injective g₁.injective dis₁
      (fun i => congrArg Sigma.fst (hf₁ i)) (fun i => congrArg Sigma.fst (hg₁ i))
    obtain ⟨cov₂, -⟩ := cover (p := Δ.len - 1) (q := Δ.len - (Δ.len - 1)) (d := Δ.d) (fun a => (y a).1) hpos
      (by rw [hy, hN, Nat.add_sub_cancel' hl2.le]) f₂ g₂ f₂.injective g₂.injective dis₂
      (fun i => congrArg Sigma.fst (hf₂ i)) (fun i => congrArg Sigma.fst (hg₂ i))
    have hcl : c = Δ.len := by omega
    subst hcl
    have e : ∀ {m n : ℕ}, m = n → Δ.first.nu ((m : ℕ) : ℂ) = Δ.first.nu ((n : ℕ) : ℂ) := by
      rintro m _ rfl
      rfl
    have hinj : ∀ a b, a < Δ.len → b < Δ.len →
        Δ.first.nu ((a : ℕ) : ℂ) = Δ.first.nu ((b : ℕ) : ℂ) → a = b := fun a b ha hb hab =>
      congrArg Fin.val (GlobalTheory.T.segment_term_injective hA Δ (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) hab)
    have z₁ : 0 < (segLow Δ 1 one_pos).len := one_pos
    have z₂ : 0 < (segHigh Δ (Δ.len - 1) hl2).len := by
      show 0 < Δ.len - (Δ.len - 1)
      omega
    refine ⟨rfl, fun a => ?_⟩
    refine (word_eq_decreasing Δ.len h3 (fun n => Δ.first.nu ((n : ℕ) : ℂ)) hinj y
      (f₁ ⟨0, z₁⟩) g₁ (fun a => ?_) ?_ (fun j => ?_) (g₂ ⟨0, z₂⟩) f₂ (fun a => ?_) ?_ (fun j => ?_) a).trans ?_
    · rcases cov₁ a with ⟨x, rfl⟩ | h
      · have hx : (x : ℕ) < 1 := x.2
        exact Or.inl (congrArg f₁ (Fin.ext (by show (x : ℕ) = 0; omega)))
      · exact Or.inr h
    · exact (hf₁ _).trans ((dec_segLow _ _ _ _).trans (e (by simp)))
    · have hj := j.2
      exact (hg₁ j).trans ((dec_segHigh _ _ _ _).trans (e (by
        have : ((j : Fin (segHigh Δ 1 hl1).len) : ℕ) = j := rfl
        omega)))
    · rcases cov₂ a with h | ⟨x, rfl⟩
      · exact Or.inr h
      · have hx : (x : ℕ) < Δ.len - (Δ.len - 1) := x.2
        exact Or.inl (congrArg g₂ (Fin.ext (by show (x : ℕ) = 0; omega)))
    · exact (hg₂ _).trans ((dec_segHigh _ _ _ _).trans (e (by simp; omega)))
    · have hj := j.2
      exact (hf₂ j).trans ((dec_segLow _ _ _ _).trans (e (by
        have : ((j : Fin (segLow Δ (Δ.len - 1) hl0).len) : ℕ) = j := rfl
        omega)))
    · have ha := a.2
      have e₂ : ((Fin.rev (Fin.cast rfl a) : Fin Δ.len) : ℕ) = Δ.len - 1 - a := by
        rw [Fin.val_rev]
        simp only [Fin.val_cast]
        omega
      show _ = Δ.first.nu (((Fin.rev (Fin.cast rfl a) : Fin Δ.len) : ℕ) : ℂ)
      rw [e₂]
  refine ⟨fun hd => ?_, shape⟩
  have hinj := GlobalTheory.T.segment_term_injective hA Δ
  have hset : {e : Fin Δ.len ≃ Fin Δ.len | ∀ a, dec Δ a = Δ.term (e a)} = {Fin.revPerm} := by
    ext e
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro h
      exact Equiv.ext fun a => (hinj (h a)).symm
    · rintro rfl a
      rfl
  have hup : jm (dec Δ) hd π ≤ 1 := by
    refine (GlobalTheory.T.jacquet_multiplicity_subquotient_le (dec Δ) hd π _ (isSmooth_prodIrr _ hd0) hsub).trans ?_
    rw [GlobalTheory.T.jacquet_multiplicity_cuspidal_product hA Δ.term (dec Δ) hd0 hd Δ.isCusp_term (isCusp_dec Δ), hset, Set.ncard_singleton]
    simp
  obtain ⟨e, he, h1⟩ := GlobalTheory.T.irreducible_subquotient_cuspidal_permutation hA Δ.term hd0 Δ.isCusp_term π hsm hc.1 hsub
  obtain ⟨h, hh⟩ := shape Δ.len _ he (fun a => Δ.isCusp_term _) h1
  have hfun : (fun a => Δ.term (e a)) = dec Δ := funext fun a => hh a
  rw [jm_congr hfun he hd] at h1
  exact le_antisymm hup h1

end GlobalTheory.CompanionTheory.LkSegFine

end
