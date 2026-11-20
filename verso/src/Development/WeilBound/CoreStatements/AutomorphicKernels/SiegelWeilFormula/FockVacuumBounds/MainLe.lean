import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LowerRankDatum

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Atop

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Establish `e : Fin L.n ≃ {i : Fin d.n // ¬ i = L.i₀}` using `Equiv.ofBijective (fun a => ⟨L.em a, (L.rng _).2 ⟨a, rfl⟩⟩) ⟨fun a b h => L.inj (congrArg Subtype.val h), fun i => by`. Take `⟨a, ha⟩` from `(L.rng i.1).1 i.2`. Conclude with `⟨a, Subtype.ext ha⟩⟩`. Establish `h` using `Fintype.card_congr e`. Rewrite `h` using `[Fintype.card_fin, Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_subtype_eq]`.

Use `L.i₀.pos` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem LD.n_succ {d : SD σ} (L : LD d) : L.n + 1 = d.n := by
  have e : Fin L.n ≃ {i : Fin d.n // ¬ i = L.i₀} :=
    Equiv.ofBijective (fun a => ⟨L.em a, (L.rng _).2 ⟨a, rfl⟩⟩)
      ⟨fun a b h => L.inj (congrArg Subtype.val h), fun i => by
        obtain ⟨a, ha⟩ := (L.rng i.1).1 i.2
        exact ⟨a, Subtype.ext ha⟩⟩
  have h := Fintype.card_congr e
  rw [Fintype.card_fin, Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_subtype_eq] at h
  have := L.i₀.pos
  omega

/- English proof (translation)
Establish `hCV : ∀ (d : SD σ) (R : RD d) (c : ℂ), MainC c d → MainV c R`. Introduce `d R c hC Φ hΦ hv x`. Conclude with `hC Φ (hPK F E σ d R Φ hΦ ((hVK F E σ d R).2.1 hv)) x`. Establish `key : ∀ k' : ℕ, ∀ d : SD σ, d.m ≤ d.n → d.n - d.m = k' → ∀ R : RD d, MainV 2 R`. Introduce `k'`.

Proceed by induction on `k' with`. Consider the case `zero`. Introduce `d h1 h2 R`. Conclude with `hCV d R 2 (hEq F E σ d (by omega))`. Consider the case `succ k' ih`.

Introduce `d h1 h2 R`. Establish `hm` using `d.ok.hm`. Take `⟨L⟩` from `hLD F E σ d (by omega)`. Take `⟨R'⟩` from `hRD F E σ L.sd`. Establish `hn` using `LD.n_succ L`.

Use `hStep F E σ d R L R' (by omega) (ih L.sd ?_ ?_ R')` and prove the remaining obligations. Use `show d.m ≤ L.n`. Use linear arithmetic over natural numbers and integers. Use `show L.n - d.m = k'`. Use linear arithmetic over natural numbers and integers.

Introduce `d h1 h2`. Take `⟨R⟩` from `hRD F E σ d`. Conclude with `hVA F E σ d R 2 (key k d h1 h2 R)`.
-/
theorem rank_difference_induction (hRD : RDEx) (hLD : LDEx) (hVK : VacK) (hPK : PolyKFin) (hEq : MainEq) (hStep : Step)
    (hVA : VacAll) (k : ℕ) : ∀ d : SD σ, d.m ≤ d.n → d.n - d.m = k → MainC 2 d := by
  have hCV : ∀ (d : SD σ) (R : RD d) (c : ℂ), MainC c d → MainV c R := by
    intro d R c hC Φ hΦ hv x
    exact hC Φ (hPK F E σ d R Φ hΦ ((hVK F E σ d R).2.1 hv)) x
  have key : ∀ k' : ℕ, ∀ d : SD σ, d.m ≤ d.n → d.n - d.m = k' → ∀ R : RD d, MainV 2 R := by
    intro k'
    induction k' with
    | zero =>
      intro d h1 h2 R
      exact hCV d R 2 (hEq F E σ d (by omega))
    | succ k' ih =>
      intro d h1 h2 R
      have hm := d.ok.hm
      obtain ⟨L⟩ := hLD F E σ d (by omega)
      obtain ⟨R'⟩ := hRD F E σ L.sd
      have hn := LD.n_succ L
      refine hStep F E σ d R L R' (by omega) (ih L.sd ?_ ?_ R')
      · show d.m ≤ L.n
        omega
      · show L.n - d.m = k'
        omega
  intro d h1 h2
  obtain ⟨R⟩ := hRD F E σ d
  exact hVA F E σ d R 2 (key k d h1 h2 R)

end PositivityTheory.SiegelWeilFormula.Atop

namespace PositivityTheory.SiegelWeilFormula

/- English proof (translation)
Introduce `hRD hLD hVK hPK hEq hStep hVA F E _ _ _ _ _ σ d h`. Conclude with `Atop.rank_difference_induction hRD hLD hVK hPK hEq hStep hVA _ d h rfl`.
-/
theorem Atop.mainLeOf : MainLeOf := by
  intro hRD hLD hVK hPK hEq hStep hVA F E _ _ _ _ _ σ d h
  exact Atop.rank_difference_induction hRD hLD hVK hPK hEq hStep hVA _ d h rfl

end PositivityTheory.SiegelWeilFormula

end
