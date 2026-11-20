import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

noncomputable section

namespace GlobalTheory

section SlopeTestRemainingChoices

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
The claim follows from `Segment.ext_first (show (Δ.first.nu a).nu b = Δ.first.nu (a + b) from IrrGL.nu_nu _ _ _) rfl`.
-/
theorem segment_nu_nu (Δ : Segment k) (a b : ℂ) : (Δ.nu a).nu b = Δ.nu (a + b) :=
  Segment.ext_first (show (Δ.first.nu a).nu b = Δ.first.nu (a + b) from IrrGL.nu_nu _ _ _) rfl

/- English proof (translation)
The claim follows from `(h.tw _ _).of_equiv (x.twEquiv _ _)`.
-/
theorem isLSeg_nu {Δ : Segment k} {x : IrrGL k} (h : IsLSeg Δ x.rep) (s : ℂ) : IsLSeg (Δ.nu s) (x.nu s).rep :=
  (h.tw _ _).of_equiv (x.twEquiv _ _)

/- English proof (translation)
Rewrite using `[Fin.univ_val_map]`. Use `congr 1`. Rewrite using `[List.ofFn_mul, List.flatMap_def, ← List.map_coe_finRange_eq_range, List.map_map, ← List.ofFn_eq_map]`. Use `congr 1`. Use `List.ofFn_inj.2 (funext fun i => ?_)` and prove the remaining obligations.

Rewrite using `[Function.comp_apply, List.map_ofFn]`. Use `List.ofFn_inj.2 (funext fun j => ?_)` and prove the remaining obligations. Establish `: ∀ h, finProdFinEquiv.symm (⟨i * m + j, h⟩ : Fin (d * m)) = (i, j)` using `fun h => by`. Rewrite using `[Equiv.symm_apply_eq]`. Use `ext`.

Simplify using `[finProdFinEquiv_apply_val]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [Function.comp, this]`.
-/
theorem univ_map_speh_segments (d m : ℕ) (Δ : Fin m → Segment k) (s : Fin m → ℝ) :
    Finset.univ.val.map (fun p : Fin (d * m) => ((Δ (finProdFinEquiv.symm p).2).nu (s (finProdFinEquiv.symm p).2)).nu
      ((((d : ℝ) - 1) / 2 - ((finProdFinEquiv.symm p).1 : ℕ) : ℝ) : ℂ)) = ↑((List.range d).flatMap fun i : ℕ =>
        (List.ofFn fun j => (Δ j).nu (s j)).map fun Γ => Γ.nu ((((d : ℝ) - 1) / 2 - i : ℝ) : ℂ)) := by
  rw [Fin.univ_val_map]
  congr 1
  rw [List.ofFn_mul, List.flatMap_def, ← List.map_coe_finRange_eq_range, List.map_map, ← List.ofFn_eq_map]
  congr 1
  refine List.ofFn_inj.2 (funext fun i => ?_)
  rw [Function.comp_apply, List.map_ofFn]
  refine List.ofFn_inj.2 (funext fun j => ?_)
  have : ∀ h, finProdFinEquiv.symm (⟨i * m + j, h⟩ : Fin (d * m)) = (i, j) := fun h => by
    rw [Equiv.symm_apply_eq]; ext; simp [finProdFinEquiv_apply_val]; ring
  simp only [Function.comp, this]

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `k _ _ _ _ _ hLM hprec hstage a V _ _ σ m δ Δ s hΔ hδu hs hd hσ d n hdn W _ _ σ' hirr hf`. Take `⟨φ⟩` from `hσ`. Take `⟨f, hfs⟩` from `hf`. Set `y : Fin d → Fin m → IrrGL k` to `fun i j => ((δ j).nu (s j)).nu (((d : ℂ) - 1) / 2 - (i : ℕ))`. Establish `hN : ∀ i, ∑ j, (y i j).1 = a` using `fun _ => hd`.

Set `Y : Fin (d * m) → IrrGL k` to `fun p => y (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2`. Establish `hM' : ∑ p, (Y p).1 = n`. Rewrite using `[← hdn, ← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [Y, Equiv.symm_apply_apply]`.

Conclude with `hN i`. Set `e1 : ∀ i : Fin d, (twist σ (detChar (Fin a) (absPow k (((d : ℂ) - 1) / 2 - (i : ℕ))))).Equiv (prodIrr (y i) (hN i))` to `fun i => (twistEquiv φ _).trans (prodIrrTwistEquiv _ hd _ (isSmoothChar_absPow _))`. Take `⟨e2⟩` from `hstage d m y (fun _ => a) n hN hdn hM'`. Set `E` to `(multiProdEquiv _ e1).trans e2`. Set `Γs : Fin (d * m) → Segment k` to `fun p => ((Δ (finProdFinEquiv.symm p).2).nu (s (finProdFinEquiv.symm p).2)).nu ((((d : ℝ) - 1) / 2 - ((finProdFinEquiv.symm p).1 : ℕ) : ℝ) : ℂ)`.

Establish `hcast : ∀ i : ℕ, (((((d : ℝ) - 1) / 2 - i : ℝ)) : ℂ) = ((d : ℂ) - 1) / 2 - (i : ℕ)` using `fun i => by push_cast; ring`. Establish `hL : ∀ p, IsLSeg (Γs p) (Y p).rep` using `fun p => by`. Simplify using `only [Γs, Y, y, hcast]`. Conclude with `isLSeg_nu (isLSeg_nu (hΔ _) _) _`. Establish `hord : ∀ p p' : Fin (d * m), p < p' → ¬ (Γs p).Precedes (Γs p')`.

Introduce `p p' hpp' hP`. Take `⟨⟨i, j⟩, rfl⟩` from `finProdFinEquiv.surjective p`. Take `⟨⟨i', j'⟩, rfl⟩` from `finProdFinEquiv.surjective p'`. Establish `hii : (i : ℕ) ≤ i'`. Assume the negation of the conclusion as `hlt`.

Establish `h1 : (i' : ℕ) + 1 ≤ i` using `by omega`. Establish `h2` using `Nat.mul_le_mul_left m h1`. Establish `h3` using `Fin.lt_def.1 hpp'`. Simplify using `only [finProdFinEquiv_apply_val] at h3`. Use `j.2` as an intermediate fact.

Use `j'.2` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Simplify using `only [Γs, Equiv.symm_apply_apply, segment_nu_nu] at hP`. Establish `key` using `hprec (δ j) (δ j') (Δ j) (Δ j') (hΔ j) (hδu j) (hΔ j') (hδu j') (s j + (((d : ℝ) - 1) / 2 - (i : ℕ))) (s j' + (((d : ℝ) - 1) / 2 - (i' : ℕ))) (by push_cast at hP ⊢; exact hP)`. Establish `hi : ((i : ℕ) : ℝ) ≤ (i' : ℕ)` using `by exact_mod_cast hii`.

Use `abs_lt.1 (hs j)` as an intermediate fact. Use `abs_lt.1 (hs j')` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hLF : LFactors (↑((List.range d).flatMap fun i : ℕ => (List.ofFn fun j => (Δ j).nu (s j)).map fun Γ => Γ.nu ((((d : ℝ) - 1) / 2 - i : ℝ) : ℂ))) Y` using `⟨Γs, ⟨univ_map_speh_segments d m Δ s, hord⟩, hL⟩`. Take `⟨π, hπ⟩` from `hLM k _ (d * m) n Y hM' hLF`.

Take `⟨ψ⟩` from `hπ.equiv_of_surjective hirr (f.comp E.symm.toIntertwiningMap) (hfs.comp E.symm.toLinearEquiv.surjective)`. Conclude with `⟨d * m, Y, hM', hLF, hπ.of_equiv ψ.symm (.refl _)⟩`.
-/
theorem speh_quotient_isL : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k],
    GlobalTheory.Published.StandardCosocleGL → (∀ (δ δ' : IrrGL k) (Δ Δ' : Segment k), IsLSeg Δ δ.rep → IsUnitarisable δ.rep → IsLSeg Δ' δ'.rep →
    IsUnitarisable δ'.rep → ∀ x y : ℝ, (Δ.nu x).Precedes (Δ'.nu y) → x + 1 ≤ y) → (∀ (d h : ℕ) (y : Fin d → Fin h → IrrGL k) (N : Fin d → ℕ) (M : ℕ) (hN : ∀ i, ∑ j, (y i j).1 = N i)
    (hM : ∑ i, N i = M)
    (hM' : ∑ p : Fin (d * h), (y (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2).1 = M),
    Nonempty ((multiProd (stdBlocks N hM) fun i => prodIrr (y i) (hN i)).Equiv
      (prodIrr (fun p => y (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2) hM'))) →
    ∀ (a : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin a) k) V)
    (m : ℕ) (δ : Fin m → IrrGL k) (Δ : Fin m → Segment k) (s : Fin m → ℝ), (∀ j, IsLSeg (Δ j) (δ j).rep) →
      (∀ j, IsUnitarisable (δ j).rep) → (∀ j, |s j| < 1 / 2) → ∀ hd : ∑ j, ((δ j).nu (s j)).1 = a,
      Nonempty (σ.Equiv (prodIrr (fun j => (δ j).nu (s j)) hd)) →
    ∀ (d n : ℕ) (hdn : ∑ _ : Fin d, a = n) (W : Type) [AddCommGroup W] [Module ℂ W]
      (σ' : Representation ℂ (GL (Fin n) k) W), σ'.IsIrreducible →
      (∃ f : (multiProd (stdBlocks (fun _ : Fin d => a) hdn) fun i : Fin d =>
        twist σ (detChar (Fin a) (absPow k (((d : ℂ) - 1) / 2 - (i : ℕ))))).IntertwiningMap σ',
        Function.Surjective f) →
      IsL ↑((List.range d).flatMap fun i : ℕ =>
        (List.ofFn fun j => (Δ j).nu (s j)).map fun Γ => Γ.nu ((((d : ℝ) - 1) / 2 - i : ℝ) : ℂ)) σ' := by
  intro k _ _ _ _ _ hLM hprec hstage a V _ _ σ m δ Δ s hΔ hδu hs hd hσ d n hdn W _ _ σ' hirr hf
  obtain ⟨φ⟩ := hσ
  obtain ⟨f, hfs⟩ := hf
  let y : Fin d → Fin m → IrrGL k := fun i j => ((δ j).nu (s j)).nu (((d : ℂ) - 1) / 2 - (i : ℕ))
  have hN : ∀ i, ∑ j, (y i j).1 = a := fun _ => hd
  let Y : Fin (d * m) → IrrGL k := fun p => y (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2
  have hM' : ∑ p, (Y p).1 = n := by
    rw [← hdn, ← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Y, Equiv.symm_apply_apply]
    exact hN i
  let e1 : ∀ i : Fin d, (twist σ (detChar (Fin a) (absPow k (((d : ℂ) - 1) / 2 - (i : ℕ))))).Equiv
      (prodIrr (y i) (hN i)) :=
    fun i => (twistEquiv φ _).trans (prodIrrTwistEquiv _ hd _ (isSmoothChar_absPow _))
  obtain ⟨e2⟩ := hstage d m y (fun _ => a) n hN hdn hM'
  let E := (multiProdEquiv _ e1).trans e2
  let Γs : Fin (d * m) → Segment k := fun p =>
    ((Δ (finProdFinEquiv.symm p).2).nu (s (finProdFinEquiv.symm p).2)).nu
      ((((d : ℝ) - 1) / 2 - ((finProdFinEquiv.symm p).1 : ℕ) : ℝ) : ℂ)
  have hcast : ∀ i : ℕ, (((((d : ℝ) - 1) / 2 - i : ℝ)) : ℂ) = ((d : ℂ) - 1) / 2 - (i : ℕ) := fun i => by
    push_cast; ring
  have hL : ∀ p, IsLSeg (Γs p) (Y p).rep := fun p => by
    simp only [Γs, Y, y, hcast]
    exact isLSeg_nu (isLSeg_nu (hΔ _) _) _
  have hord : ∀ p p' : Fin (d * m), p < p' → ¬ (Γs p).Precedes (Γs p') := by
    intro p p' hpp' hP
    obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective p
    obtain ⟨⟨i', j'⟩, rfl⟩ := finProdFinEquiv.surjective p'
    have hii : (i : ℕ) ≤ i' := by
      by_contra hlt
      have h1 : (i' : ℕ) + 1 ≤ i := by omega
      have h2 := Nat.mul_le_mul_left m h1
      have h3 := Fin.lt_def.1 hpp'
      simp only [finProdFinEquiv_apply_val] at h3
      have := j.2
      have := j'.2
      nlinarith
    simp only [Γs, Equiv.symm_apply_apply, segment_nu_nu] at hP
    have key := hprec (δ j) (δ j') (Δ j) (Δ j') (hΔ j) (hδu j) (hΔ j') (hδu j')
      (s j + (((d : ℝ) - 1) / 2 - (i : ℕ))) (s j' + (((d : ℝ) - 1) / 2 - (i' : ℕ))) (by push_cast at hP ⊢; exact hP)
    have hi : ((i : ℕ) : ℝ) ≤ (i' : ℕ) := by exact_mod_cast hii
    have := abs_lt.1 (hs j)
    have := abs_lt.1 (hs j')
    linarith
  have hLF : LFactors (↑((List.range d).flatMap fun i : ℕ =>
      (List.ofFn fun j => (Δ j).nu (s j)).map fun Γ => Γ.nu ((((d : ℝ) - 1) / 2 - i : ℝ) : ℂ))) Y :=
    ⟨Γs, ⟨univ_map_speh_segments d m Δ s, hord⟩, hL⟩
  obtain ⟨π, hπ⟩ := hLM k _ (d * m) n Y hM' hLF
  obtain ⟨ψ⟩ := hπ.equiv_of_surjective hirr (f.comp E.symm.toIntertwiningMap)
    (hfs.comp E.symm.toLinearEquiv.surjective)
  exact ⟨d * m, Y, hM', hLF, hπ.of_equiv ψ.symm (.refl _)⟩

end GlobalTheory
