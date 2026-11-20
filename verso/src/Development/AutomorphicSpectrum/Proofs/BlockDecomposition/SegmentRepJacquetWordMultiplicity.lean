import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientProductIrreducibleStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspidalJacquetSubquotientAtMostOneNonemptyBlock

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.FineL

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Simplify using `[decWord]`.
-/
theorem length_decWord (Γ : Segment k) : (decWord Γ).length = Γ.len := by
  simp [decWord]

/- English proof (translation)
Establish `h : (a : ℕ) < (List.ofFn Γ.term).reverse.length` using `a.2`. Use `show (List.ofFn Γ.term).reverse[(a : ℕ)] = _`. Rewrite using `[List.getElem_reverse, List.getElem_ofFn]`. Simplify using `[Segment.term]`.
-/
theorem decWord_get (Γ : Segment k) (a : Fin (decWord Γ).length) :
    (decWord Γ).get a = Γ.first.nu ((Γ.len - 1 - (a : ℕ) : ℕ) : ℂ) := by
  have h : (a : ℕ) < (List.ofFn Γ.term).reverse.length := a.2
  show (List.ofFn Γ.term).reverse[(a : ℕ)] = _
  rw [List.getElem_reverse, List.getElem_ofFn]
  simp [Segment.term]

/- English proof (translation)
Rewrite using `[decWord_get]`. Conclude with `Γ.isCusp_first.nu _`.
-/
theorem isCusp_decWord_get (Γ : Segment k) (a : Fin (decWord Γ).length) : ((decWord Γ).get a).IsCusp := by
  rw [decWord_get]
  exact Γ.isCusp_first.nu _

/- English proof (translation)
Establish `h : ∀ a, ((decWord Γ).get a).1 = Γ.d` using `fun a => by rw [decWord_get]; rfl`. Simplify using `only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, length_decWord]`. Both sides reduce to the same expression.
-/
theorem sum_decWord (Γ : Segment k) : ∑ a, ((decWord Γ).get a).1 = Γ.deg := by
  have h : ∀ a, ((decWord Γ).get a).1 = Γ.d := fun a => by rw [decWord_get]; rfl
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, length_decWord]
  rfl

/- English proof (translation)
Simplify using `only [below, h, Finset.sum_const, smul_eq_mul, mul_one]`. Rewrite using `[Finset.filter_lt_eq_Ioi, Fin.card_Ioi]`.
-/
theorem below_of_len_one {s : ℕ} (Γ : Fin s → Segment k) (h : ∀ a, (Γ a).len = 1) (a : Fin s) :
    below Γ a = s - 1 - (a : ℕ) := by
  simp only [below, h, Finset.sum_const, smul_eq_mul, mul_one]
  rw [Finset.filter_lt_eq_Ioi, Fin.card_Ioi]

/- English proof (translation)
Establish `hd : ∑ a, ((decWord Γ).get a).1 = N` using `(sum_decWord Γ).trans hΓ.deg_eq`. Rewrite using `[jmL, dif_pos hd]`. Use `(hJ Γ π hΓ _ (decWord Γ).get hd fun a => (isCusp_decWord_get Γ a).1).1 ⟨fun a => Segment.single _ (isCusp_decWord_get Γ a), ⟨?_, fun a => ?_⟩, fun a => (single_spec (isCusp_decWord_get Γ a)).2.1⟩` and prove the remaining obligations. Establish `h : ∀ a, (Segment.single _ (isCusp_decWord_get Γ a)).len = 1` using `fun _ => rfl`. Simplify using `only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one, length_decWord]`.

Use `(decWord_get Γ a).trans ?_` and prove the remaining obligations. Establish `e : (decWord Γ).length - 1 - (a : ℕ) = Γ.len - 1 - (a : ℕ)`. Use `length_decWord Γ` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[below_of_len_one _ (fun _ => rfl), e]`.
-/
theorem jmL_decWord (hJ : LSegJacquet k) (Γ : Segment k) {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin N) k) V} (hΓ : IsLSeg Γ π) : jmL (decWord Γ) π = 1 := by
  have hd : ∑ a, ((decWord Γ).get a).1 = N := (sum_decWord Γ).trans hΓ.deg_eq
  rw [jmL, dif_pos hd]
  refine (hJ Γ π hΓ _ (decWord Γ).get hd fun a => (isCusp_decWord_get Γ a).1).1
    ⟨fun a => Segment.single _ (isCusp_decWord_get Γ a), ⟨?_, fun a => ?_⟩,
      fun a => (single_spec (isCusp_decWord_get Γ a)).2.1⟩
  · have h : ∀ a, (Segment.single _ (isCusp_decWord_get Γ a)).len = 1 := fun _ => rfl
    simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one, length_decWord]
  · refine (decWord_get Γ a).trans ?_
    have e : (decWord Γ).length - 1 - (a : ℕ) = Γ.len - 1 - (a : ℕ) := by
      have := length_decWord Γ
      omega
    rw [below_of_len_one _ (fun _ => rfl), e]

/- English proof (translation)
Establish `hd : ∑ a, ((decWord Δ).get a).1 = x.1` using `(sum_decWord Δ).trans h.deg_eq`. Establish `h1` using `jmL_decWord hJ Δ h`. Rewrite `h1` using `[jmL, dif_pos hd, jm]`. Establish `hsub : IsSubquotient (piTensor fun a => ((decWord Δ).get a).rep) (jac (stdBlocks (fun a => ((decWord Δ).get a).1) hd) x.rep)` using `jhMult_ne_zero_iff.1 (by rw [h1]; exact one_ne_zero)`. Establish `hu` using `GlobalTheory.SmGL.CuspRow.block_unique_of_isCuspidal k x.1 _ x.rep _ _ _ _ (fun a => ((decWord Δ).get a).rep) hx.2 (fun a => nontrivial_of_irreducible ((decWord Δ).get a).2.rep.irr) hsub`.

Assume the negation of the conclusion as `hne`. Establish `hl : 2 ≤ (decWord Δ).length`. Use `Δ.len_pos` as an intermediate fact. Rewrite using `[length_decWord]`. Use linear arithmetic over natural numbers and integers.

Use `hu ⟨0, by omega⟩ ⟨1, by omega⟩ (isCusp_decWord_get Δ _).1 (isCusp_decWord_get Δ _).1` as an intermediate fact. Simplify using `at this`.
-/
theorem len_eq_one (hJ : LSegJacquet k) {Δ : Segment k} {x : IrrGL k} (hx : x.IsCusp) (h : IsLSeg Δ x.rep) :
    Δ.len = 1 := by
  have hd : ∑ a, ((decWord Δ).get a).1 = x.1 := (sum_decWord Δ).trans h.deg_eq
  have h1 := jmL_decWord hJ Δ h
  rw [jmL, dif_pos hd, jm] at h1
  have hsub : IsSubquotient (piTensor fun a => ((decWord Δ).get a).rep)
      (jac (stdBlocks (fun a => ((decWord Δ).get a).1) hd) x.rep) :=
    jhMult_ne_zero_iff.1 (by rw [h1]; exact one_ne_zero)
  have hu := GlobalTheory.SmGL.CuspRow.block_unique_of_isCuspidal k x.1 _ x.rep _ _ _ _
    (fun a => ((decWord Δ).get a).rep) hx.2 (fun a => nontrivial_of_irreducible ((decWord Δ).get a).2.rep.irr) hsub
  by_contra hne
  have hl : 2 ≤ (decWord Δ).length := by
    have := Δ.len_pos
    rw [length_decWord]
    omega
  have := hu ⟨0, by omega⟩ ⟨1, by omega⟩ (isCusp_decWord_get Δ _).1 (isCusp_decWord_get Δ _).1
  simp at this

/- English proof (translation)
Establish `hdeg : ρ.1 = x.1`. Use `h.deg_eq` as an intermediate fact. Simplify `this` using `[Segment.deg, Segment.single, Segment.ofFirst]`. Take `⟨n, c⟩` from `x`. Take `⟨m, r⟩` from `ρ`.

Take `rfl : m = n` from `hdeg`. Take `⟨φ⟩` from `(single_spec hρ).2.1.unique h`. Conclude with `(IrrGL.of_rep _).symm.trans ((IrrGL.of_eq_of.2 ⟨φ⟩).trans (IrrGL.of_rep _))`.
-/
theorem eq_of_isLSeg_single {ρ : IrrGL k} (hρ : ρ.IsCusp) {x : IrrGL k} (h : IsLSeg (.single ρ hρ) x.rep) : x = ρ := by
  have hdeg : ρ.1 = x.1 := by
    have := h.deg_eq
    simpa [Segment.deg, Segment.single, Segment.ofFirst] using this
  obtain ⟨n, c⟩ := x
  obtain ⟨m, r⟩ := ρ
  obtain rfl : m = n := hdeg
  obtain ⟨φ⟩ := (single_spec hρ).2.1.unique h
  exact (IrrGL.of_rep _).symm.trans ((IrrGL.of_eq_of.2 ⟨φ⟩).trans (IrrGL.of_rep _))

/- English proof (translation)
Establish `e : Δ = .single Δ.first Δ.isCusp_first` using `Segment.ext_first rfl hl`. Conclude with `eq_of_isLSeg_single Δ.isCusp_first (e ▸ h)`.
-/
theorem eq_first_of_len_one {Δ : Segment k} (hl : Δ.len = 1) {x : IrrGL k} (h : IsLSeg Δ x.rep) : x = Δ.first := by
  have e : Δ = .single Δ.first Δ.isCusp_first := Segment.ext_first rfl hl
  exact eq_of_isLSeg_single Δ.isCusp_first (e ▸ h)

/- English proof (translation)
Introduce `k _ _ _ _ _ hJ Γ N V _ _ π hΓ W hW`. Use `⟨fun e => e ▸ jmL_decWord hJ Γ hΓ, fun hne => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hd : ∑ a, (W.get a).1 = N`. Rewrite using `[jmL, dif_pos hd]`. Use `(hJ Γ π hΓ _ W.get hd fun a => (hW _ (List.get_mem W a)).1).2 ?_` and prove the remaining obligations.

Introduce and unpack `⟨Γ', ⟨hs, hf⟩, hL⟩`. Establish `hl : ∀ a, (Γ' a).len = 1` using `fun a => len_eq_one hJ (hW _ (List.get_mem W a)) (hL a)`. Establish `hlen : W.length = Γ.len`. Simplify `hs` using `only [hl, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]`. Use `hne (List.ext_get (hlen.trans (length_decWord Γ).symm) fun n h1 h2 => ?_)` and prove the remaining obligations.

Establish `h3 : W.get ⟨n, h1⟩ = Γ.first.nu ((W.length - 1 - n : ℕ) : ℂ)`. Establish `h4` using `eq_first_of_len_one (hl ⟨n, h1⟩) (hL ⟨n, h1⟩)`. Rewrite `h4` using `[hf, below_of_len_one Γ' hl]`. Conclude with `h4`. Rewrite using `[h3, decWord_get, hlen]`.

Rewrite using `[jmL, dif_neg hd]`.
-/
theorem jmL_cusp_word : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GlobalTheory.Published.IrreducibleAdmissibleGL → LSegJacquet k → ∀ (Γ : Segment k) {N : ℕ} {V : Type} [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsLSeg Γ π → ∀ W : List (IrrGL k), (∀ w ∈ W, w.IsCusp) →
    (W = decWord Γ → jmL W π = 1) ∧ (W ≠ decWord Γ → jmL W π = 0) := by
  intro k _ _ _ _ _ hJ Γ N V _ _ π hΓ W hW
  refine ⟨fun e => e ▸ jmL_decWord hJ Γ hΓ, fun hne => ?_⟩
  by_cases hd : ∑ a, (W.get a).1 = N
  · rw [jmL, dif_pos hd]
    refine (hJ Γ π hΓ _ W.get hd fun a => (hW _ (List.get_mem W a)).1).2 ?_
    rintro ⟨Γ', ⟨hs, hf⟩, hL⟩
    have hl : ∀ a, (Γ' a).len = 1 := fun a => len_eq_one hJ (hW _ (List.get_mem W a)) (hL a)
    have hlen : W.length = Γ.len := by
      simpa only [hl, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] using hs
    refine hne (List.ext_get (hlen.trans (length_decWord Γ).symm) fun n h1 h2 => ?_)
    have h3 : W.get ⟨n, h1⟩ = Γ.first.nu ((W.length - 1 - n : ℕ) : ℂ) := by
      have h4 := eq_first_of_len_one (hl ⟨n, h1⟩) (hL ⟨n, h1⟩)
      rw [hf, below_of_len_one Γ' hl] at h4
      exact h4
    rw [h3, decWord_get, hlen]
  · rw [jmL, dif_neg hd]

end GlobalTheory.CompanionTheory.FineL

end
