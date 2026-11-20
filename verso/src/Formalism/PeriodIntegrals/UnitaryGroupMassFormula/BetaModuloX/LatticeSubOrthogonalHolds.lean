import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaModuloX.Skeleton

noncomputable section

open scoped Classical

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef IsDedekindDomain

namespace PI.UnitaryGroupMassFormula.BetaModX

section Loc

variable {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module (𝓞 E) V]

/- English proof (translation)
Introduce `x hx`. Use `show ∃ s ∈ p.primeCompl, s • x ∈ L`. Conclude with `⟨1, p.primeCompl.one_mem, by rw [one_smul]; exact hx⟩`.
-/
theorem le_locP (p : Ideal (𝓞 E)) [p.IsPrime] (L : Submodule (𝓞 E) V) : L ≤ Formalism.HermitianLatticesTheory.localization₂ p L := by
  intro x hx
  show ∃ s ∈ p.primeCompl, s • x ∈ L
  exact ⟨1, p.primeCompl.one_mem, by rw [one_smul]; exact hx⟩

/- English proof (translation)
Introduce `x hx`. Take `⟨s, hs, hsx⟩ : ∃ s ∈ p.primeCompl, s • x ∈ L` from `hx`. Use `show ∃ s ∈ p.primeCompl, s • x ∈ L'`. Conclude with `⟨s, hs, h hsx⟩`.
-/
theorem localization_mono (p : Ideal (𝓞 E)) [p.IsPrime] {L L' : Submodule (𝓞 E) V} (h : L ≤ L') :
    Formalism.HermitianLatticesTheory.localization₂ p L ≤ Formalism.HermitianLatticesTheory.localization₂ p L' := by
  intro x hx
  obtain ⟨s, hs, hsx⟩ : ∃ s ∈ p.primeCompl, s • x ∈ L := hx
  show ∃ s ∈ p.primeCompl, s • x ∈ L'
  exact ⟨s, hs, h hsx⟩

/- English proof (translation)
Take `⟨t, ht, htx⟩ : ∃ t ∈ p.primeCompl, t • s • x ∈ L` from `h`. Establish `hs' : s ∈ p.primeCompl` using `hs`. Use `show ∃ s ∈ p.primeCompl, s • x ∈ L`. Conclude with `⟨t * s, p.primeCompl.mul_mem ht hs', by rw [mul_smul]; exact htx⟩`.
-/
theorem mem_localization_of_smul_mem' (p : Ideal (𝓞 E)) [p.IsPrime] (L : Submodule (𝓞 E) V) (x : V) (s : 𝓞 E) (hs : s ∉ p)
    (h : s • x ∈ Formalism.HermitianLatticesTheory.localization₂ p L) : x ∈ Formalism.HermitianLatticesTheory.localization₂ p L := by
  obtain ⟨t, ht, htx⟩ : ∃ t ∈ p.primeCompl, t • s • x ∈ L := h
  have hs' : s ∈ p.primeCompl := hs
  show ∃ s ∈ p.primeCompl, s • x ∈ L
  exact ⟨t * s, p.primeCompl.mul_mem ht hs', by rw [mul_smul]; exact htx⟩

/- English proof (translation)
Set `I : Ideal (𝓞 E)` to `Submodule.comap (LinearMap.toSpanSingleton (𝓞 E) V x) N`. Establish `hmem : ∀ r : 𝓞 E, r ∈ I ↔ r • x ∈ N` using `fun r => by show (LinearMap.toSpanSingleton (𝓞 E) V x) r ∈ N ↔ r • x ∈ N`. Rewrite using `[LinearMap.toSpanSingleton_apply]`. Assume the negation of the conclusion as `hx`. Establish `hIt : I ≠ ⊤`.

Introduce `hI`. Apply `hx` to reduce the goal to its premises. Establish `h1 : (1 : 𝓞 E) ∈ I` using `by rw [hI]; exact Submodule.mem_top`. Establish `h2` using `(hmem 1).1 h1`. Rewrite `h2` using `[one_smul]`. Then use the resulting hypothesis.

Take `⟨M, hM, hIM⟩` from `Ideal.exists_le_maximal I hIt`. Establish `hMb : M ≠ ⊥`. Introduce `hb`. Rewrite `hM` using `[hb]`. Conclude with `NumberField.RingOfIntegers.not_isField E (Ring.isField_iff_maximal_bot.mpr hM)`.

Take `⟨s, hs, hsx⟩ : ∃ s ∈ M.primeCompl, s • x ∈ N` from `h ⟨M, hM.isPrime, hMb⟩`. Conclude with `hs (hIM ((hmem s).2 hsx))`.
-/
theorem mem_of_locP (N : Submodule (𝓞 E) V) (x : V)
    (h : ∀ P : HeightOneSpectrum (𝓞 E), x ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N)) : x ∈ N := by

  let I : Ideal (𝓞 E) := Submodule.comap (LinearMap.toSpanSingleton (𝓞 E) V x) N
  have hmem : ∀ r : 𝓞 E, r ∈ I ↔ r • x ∈ N := fun r => by
    show (LinearMap.toSpanSingleton (𝓞 E) V x) r ∈ N ↔ r • x ∈ N
    rw [LinearMap.toSpanSingleton_apply]
  by_contra hx
  have hIt : I ≠ ⊤ := by
    intro hI
    apply hx
    have h1 : (1 : 𝓞 E) ∈ I := by rw [hI]; exact Submodule.mem_top
    have h2 := (hmem 1).1 h1
    rwa [one_smul] at h2
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hIt
  have hMb : M ≠ ⊥ := by
    intro hb
    rw [hb] at hM
    exact NumberField.RingOfIntegers.not_isField E (Ring.isField_iff_maximal_bot.mpr hM)
  obtain ⟨s, hs, hsx⟩ : ∃ s ∈ M.primeCompl, s • x ∈ N :=
    h ⟨M, hM.isPrime, hMb⟩
  exact hs (hIM ((hmem s).2 hsx))

end Loc

section D7

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Introduce `D u u' F0 Λ hΛ y x hx`. Take `⟨-, ⟨-, -, -, hlc⟩, -⟩` from `hΛ`. Take `⟨-, ⟨ξ, hξl, hξd, hξm⟩, hyc, -⟩` from `y.2`. Establish `hxΛ : x ∈ Λ` using `(Submodule.mem_inf.1 hx).1`. Use `mem_of_locP _ x (fun P => ?_)` and prove the remaining obligations.

Use `haveI := P.isPrime`. Distinguish the cases in `hgP : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal`. Use `swap`. Apply `mem_localization_of_smul_mem' P.asIdeal _ x ((gS D : ℕ) : 𝓞 D.host.E) hgP` to reduce the goal to its premises. Apply `le_locP` to reduce the goal to its premises.

Conclude with `Submodule.mem_sup_left (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hxΛ)`. Establish `hsm : ∀ (o : 𝓞 D.host.E) (v : (VS D).V), v ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ ⊔ XLam Λ y.1) → ((o : D.host.E)) • v ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {((gS D : ℕ) : 𝓞 D.host. …`. Introduce `o v hv`. Establish `h1` using `(Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ ⊔ XLam Λ y.1)).smul_mem o hv`. Rewrite `h1` using `[← algebraMap_smul D.host.E o v]`. Then use the resulting hypothesis.

Establish `hye : ∀ b, y.1.fl.e b ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ ⊔ XLam Λ y.1)`. Introduce `b`. Take `⟨cy, -, hcy1, hcyeq⟩` from `hyc.1 P`. Establish `hmem : cy b • y.1.fl.e b ∈ Submodule.span (𝓞 D.host.E) (Set.range fun a => cy a • y.1.fl.e a)` using `Submodule.subset_span ⟨b, rfl⟩`. Rewrite `hmem` using `[hcy1 hgP b, one_smul]`.

Establish `h1 : y.1.fl.e b ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ y.1)`. Rewrite using `[hcyeq]`. Conclude with `le_locP _ _ hmem`. Conclude with `localization_mono P.asIdeal le_sup_right h1`. Establish `key : ∀ n : ℕ, ∀ b : Fin D.R.rS, (b : ℕ) = n → (lf D F0).fl.e b ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ ⊔ XLam Λ y.1)`.

Introduce `n`. Use `Nat.strong_induction_on n ?_` and prove the remaining obligations. Introduce `n ih b hbn`. Establish `hm` using `hξm (Fin.castSucc b)`. Unfold `ModG frameAct frame at hm`.

Establish `hdiff` using `localization_mono P.asIdeal (le_sup_left : Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ ≤ Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ ⊔ XLam Λ y.1) (hm P hgP)`. Establish `hY : y.1.fl.fvec (Fin.castSucc b) ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ ⊔ XLam Λ y.1)`. Simplify `hye b` using `[Formalism.MainNotions.S.FlagG.fvec]`. Establish `hS : (∑ a, ((ξ a (Fin.castSucc b) : 𝓞 D.host.E) : D.host.E) • (lf D F0).fl.fvec a) ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ ⊔ XLam Λ y.1)`. Establish `h1` using `Submodule.sub_mem _ hY hdiff`.

Rewrite `h1` using `[sub_sub_cancel]`. Then use the resulting hypothesis. Establish `hR : (∑ a ∈ Finset.univ.erase (Fin.castSucc b), ((ξ a (Fin.castSucc b) : 𝓞 D.host.E) : D.host.E) • (lf D F0).fl.fvec a) ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ ⊔ XLam Λ y.1)`. Use `Submodule.sum_mem _ (fun a ha => ?_)` and prove the remaining obligations. Establish `hab : a ≠ Fin.castSucc b` using `Finset.ne_of_mem_erase ha`. Break down `lt_or_gt_of_ne hab with h | h` into its components or cases.

Take `⟨a', rfl⟩ : ∃ a' : Fin D.R.rS, Fin.castSucc a' = a` from `⟨⟨a.val, lt_trans h b.isLt⟩, Fin.ext rfl⟩`. Establish `h' : (a' : ℕ) < (b : ℕ)` using `h`. Simplify using `only [Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc]`. Conclude with `hsm _ _ (ih a' (by omega) a' rfl)`. Rewrite using `[hξl a (Fin.castSucc b) h]`.

Simplify using the standard rewrite rules. Establish `hsum` using `Finset.add_sum_erase Finset.univ (fun a => ((ξ a (Fin.castSucc b) : 𝓞 D.host.E) : D.host.E) • (lf D F0).fl.fvec a) (Finset.mem_univ (Fin.castSucc b))`. Establish `h2 : ((ξ (Fin.castSucc b) (Fin.castSucc b) : 𝓞 D.host.E) : D.host.E) • (lf D F0).fl.fvec (Fin.castSucc b) = (∑ a, ((ξ a (Fin.castSucc b) : 𝓞 D.host.E) : D.host.E) • (lf D F0).fl.fvec a) - ∑ a ∈ Finset.univ.erase (Fin.castSucc b), ((ξ a (Fin.castSucc b) : 𝓞 D.host.E) : D.host.E) • …` using `eq_sub_of_add_eq hsum`. Establish `hfb : ((ξ (Fin.castSucc b) (Fin.castSucc b) : 𝓞 D.host.E) : D.host.E) • (lf D F0).fl.fvec (Fin.castSucc b) = (lf D F0).fl.e b`. Rewrite using `[hξd]`.

Simplify using `[Formalism.MainNotions.S.FlagG.fvec]`. Rewrite using `[← hfb, h2]`. Conclude with `Submodule.sub_mem _ hS hR`. Take `⟨cl, -, hcl1, hcleq⟩` from `hlc.1 P`. Establish `hxl : x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Submodule.span (𝓞 D.host.E) (Set.range fun a => cl a • (lf D F0).fl.e a))`.

Rewrite using `[← hcleq]`. Conclude with `le_locP _ _ hx`. Take `⟨s, hs, hsx⟩ : ∃ s ∈ P.asIdeal.primeCompl, s • x ∈ Submodule.span (𝓞 D.host.E) (Set.range fun a => cl a • (lf D F0).fl.e a)` from `hxl`. Apply `mem_localization_of_smul_mem' P.asIdeal _ x s hs` to reduce the goal to its premises. Use `Submodule.span_le.2 ?_ hsx` and prove the remaining obligations.

Introduce and unpack `_ ⟨a, rfl⟩`. Simplify using `only [hcl1 hgP a, one_smul]`. Conclude with `key _ a rfl`.
-/
theorem lattice_sub_orthogonal_holds : XLamSub := by
  intro D u u' F0 Λ hΛ y x hx
  obtain ⟨-, ⟨-, -, -, hlc⟩, -⟩ := hΛ
  obtain ⟨-, ⟨ξ, hξl, hξd, hξm⟩, hyc, -⟩ := y.2
  have hxΛ : x ∈ Λ := (Submodule.mem_inf.1 hx).1
  refine mem_of_locP _ x (fun P => ?_)
  haveI := P.isPrime
  by_cases hgP : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal
  swap
  · apply mem_localization_of_smul_mem' P.asIdeal _ x ((gS D : ℕ) : 𝓞 D.host.E) hgP
    apply le_locP
    exact Submodule.mem_sup_left (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hxΛ)

  have hsm : ∀ (o : 𝓞 D.host.E) (v : (VS D).V), v ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ ⊔ XLam Λ y.1) → ((o : D.host.E)) • v ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ ⊔ XLam Λ y.1) := by
    intro o v hv
    have h1 := (Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ ⊔ XLam Λ y.1)).smul_mem o hv
    rwa [← algebraMap_smul D.host.E o v] at h1

  have hye : ∀ b, y.1.fl.e b ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ ⊔ XLam Λ y.1) := by
    intro b
    obtain ⟨cy, -, hcy1, hcyeq⟩ := hyc.1 P
    have hmem : cy b • y.1.fl.e b ∈ Submodule.span (𝓞 D.host.E) (Set.range fun a => cy a • y.1.fl.e a) :=
      Submodule.subset_span ⟨b, rfl⟩
    rw [hcy1 hgP b, one_smul] at hmem
    have h1 : y.1.fl.e b ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ y.1) := by
      rw [hcyeq]
      exact le_locP _ _ hmem
    exact localization_mono P.asIdeal le_sup_right h1

  have key : ∀ n : ℕ, ∀ b : Fin D.R.rS, (b : ℕ) = n → (lf D F0).fl.e b ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ ⊔ XLam Λ y.1) := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih b hbn
    have hm := hξm (Fin.castSucc b)
    unfold ModG frameAct frame at hm
    have hdiff := localization_mono P.asIdeal (le_sup_left : Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ ≤ Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ ⊔ XLam Λ y.1) (hm P hgP)
    have hY : y.1.fl.fvec (Fin.castSucc b) ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ ⊔ XLam Λ y.1) := by
      simpa [Formalism.MainNotions.S.FlagG.fvec] using hye b
    have hS : (∑ a, ((ξ a (Fin.castSucc b) : 𝓞 D.host.E) : D.host.E) • (lf D F0).fl.fvec a) ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ ⊔ XLam Λ y.1) := by
      have h1 := Submodule.sub_mem _ hY hdiff
      rwa [sub_sub_cancel] at h1
    have hR : (∑ a ∈ Finset.univ.erase (Fin.castSucc b), ((ξ a (Fin.castSucc b) : 𝓞 D.host.E) : D.host.E) • (lf D F0).fl.fvec a) ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ ⊔ XLam Λ y.1) := by
      refine Submodule.sum_mem _ (fun a ha => ?_)
      have hab : a ≠ Fin.castSucc b := Finset.ne_of_mem_erase ha
      rcases lt_or_gt_of_ne hab with h | h
      · obtain ⟨a', rfl⟩ : ∃ a' : Fin D.R.rS, Fin.castSucc a' = a := ⟨⟨a.val, lt_trans h b.isLt⟩, Fin.ext rfl⟩
        have h' : (a' : ℕ) < (b : ℕ) := h
        simp only [Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc]
        exact hsm _ _ (ih a' (by omega) a' rfl)
      · rw [hξl a (Fin.castSucc b) h]
        simp
    have hsum := Finset.add_sum_erase Finset.univ (fun a => ((ξ a (Fin.castSucc b) : 𝓞 D.host.E) : D.host.E) • (lf D F0).fl.fvec a) (Finset.mem_univ (Fin.castSucc b))
    have h2 : ((ξ (Fin.castSucc b) (Fin.castSucc b) : 𝓞 D.host.E) : D.host.E) • (lf D F0).fl.fvec (Fin.castSucc b) =
        (∑ a, ((ξ a (Fin.castSucc b) : 𝓞 D.host.E) : D.host.E) • (lf D F0).fl.fvec a) -
          ∑ a ∈ Finset.univ.erase (Fin.castSucc b), ((ξ a (Fin.castSucc b) : 𝓞 D.host.E) : D.host.E) • (lf D F0).fl.fvec a :=
      eq_sub_of_add_eq hsum
    have hfb : ((ξ (Fin.castSucc b) (Fin.castSucc b) : 𝓞 D.host.E) : D.host.E) • (lf D F0).fl.fvec (Fin.castSucc b) =
        (lf D F0).fl.e b := by
      rw [hξd]
      simp [Formalism.MainNotions.S.FlagG.fvec]
    rw [← hfb, h2]
    exact Submodule.sub_mem _ hS hR

  obtain ⟨cl, -, hcl1, hcleq⟩ := hlc.1 P
  have hxl : x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Submodule.span (𝓞 D.host.E) (Set.range fun a => cl a • (lf D F0).fl.e a)) := by
    rw [← hcleq]
    exact le_locP _ _ hx
  obtain ⟨s, hs, hsx⟩ : ∃ s ∈ P.asIdeal.primeCompl, s • x ∈ Submodule.span (𝓞 D.host.E) (Set.range fun a => cl a • (lf D F0).fl.e a) := hxl
  apply mem_localization_of_smul_mem' P.asIdeal _ x s hs
  refine Submodule.span_le.2 ?_ hsx
  rintro _ ⟨a, rfl⟩
  simp only [hcl1 hgP a, one_smul]
  exact key _ a rfl

end D7

end PI.UnitaryGroupMassFormula.BetaModX
