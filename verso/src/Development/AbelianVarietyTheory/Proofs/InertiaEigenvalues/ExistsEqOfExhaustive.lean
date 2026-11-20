import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConcretePeriodDeRhamModuleFinrankLe

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

namespace GlobalTheory.Per.FilCount

/- English proof (translation)
Take `⟨s, hs⟩ : D.FG` from `(Submodule.fg_iff_finiteDimensional D).2 inferInstance`. Establish `hsD : ∀ x ∈ s, x ∈ D` using `fun x hx => hs ▸ Submodule.subset_span hx`. Use `choose! f hf using hex`. Take `⟨b, hb⟩` from `(s.image f).bddBelow`. Use `⟨b, fun a ha => le_antisymm (hle a) ?_⟩` and prove the remaining obligations.

Rewrite using `[← hs, Submodule.span_le]`. Introduce `x hx`. Establish `hbx : b ≤ f x` using `hb (Finset.mem_coe.2 (Finset.mem_image_of_mem f hx))`. Conclude with `hF (ha.trans hbx) (hf x (hsD x hx))`.
-/
theorem exists_eq_of_exhaustive {k M : Type*} [Field k] [AddCommGroup M] [Module k M]
    (D : Submodule k M) [FiniteDimensional k D] (F : ℤ → Submodule k M) (hF : Antitone F)
    (hle : ∀ a, F a ≤ D) (hex : ∀ x ∈ D, ∃ a, x ∈ F a) : ∃ b : ℤ, ∀ a ≤ b, F a = D := by
  obtain ⟨s, hs⟩ : D.FG := (Submodule.fg_iff_finiteDimensional D).2 inferInstance
  have hsD : ∀ x ∈ s, x ∈ D := fun x hx => hs ▸ Submodule.subset_span hx
  choose! f hf using hex
  obtain ⟨b, hb⟩ := (s.image f).bddBelow
  refine ⟨b, fun a ha => le_antisymm (hle a) ?_⟩
  rw [← hs, Submodule.span_le]
  intro x hx
  have hbx : b ≤ f x := hb (Finset.mem_coe.2 (Finset.mem_image_of_mem f hx))
  exact hF (ha.trans hbx) (hf x (hsD x hx))

/- English proof (translation)
Establish `tel : ∀ n : ℕ, ∑ a ∈ Finset.Ico (-(n : ℤ)) 0, (d a - d (a + 1)) = d (-n) - d 0`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`.

Establish `e : Finset.Ico (-((n + 1 : ℕ) : ℤ)) 0 = insert (-((n + 1 : ℕ) : ℤ)) (Finset.Ico (-(n : ℤ)) 0)`. Use extensionality with `x`. Simplify using `only [Finset.mem_Ico, Finset.mem_insert]`. Use `push_cast`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[e, Finset.sum_insert (by simp only [Finset.mem_Ico]; push_cast; omega), ih]`. Establish `e2 : -((n + 1 : ℕ) : ℤ) + 1 = -(n : ℤ)` using `by push_cast; ring`. Rewrite using `[e2]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨m, hm⟩` from `J.bddBelow`.

Take `⟨n, hn1, hn2⟩ : ∃ n : ℕ, -(n : ℤ) ≤ m ∧ -(n : ℤ) ≤ b` from `⟨m.natAbs + b.natAbs, by omega, by omega⟩`. Rewrite using `[← hb _ hn2, ← tel n]`. Use `symm`. Use `Finset.sum_subset ?_ ?_` and prove the remaining obligations. Introduce `x hx`.

Rewrite `hx` using `[Finset.mem_filter]`. Conclude with `Finset.mem_Ico.2 ⟨hn1.trans (hm (Finset.mem_coe.2 hx.1)), hx.2⟩`. Introduce `x hx hx'`. Use `hJ x fun h => hx' (Finset.mem_filter.2 ⟨h, (Finset.mem_Ico.1 hx).2⟩)` and prove the remaining obligations.
-/
theorem telescope (d : ℤ → ℤ) (c : ℤ) (b : ℤ) (hb : ∀ a ≤ b, d a = c) (J : Finset ℤ)
    (hJ : ∀ a, a ∉ J → d a - d (a + 1) = 0) :
    c - d 0 = ∑ a ∈ J.filter (· < 0), (d a - d (a + 1)) := by
  have tel : ∀ n : ℕ, ∑ a ∈ Finset.Ico (-(n : ℤ)) 0, (d a - d (a + 1)) = d (-n) - d 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have e : Finset.Ico (-((n + 1 : ℕ) : ℤ)) 0
          = insert (-((n + 1 : ℕ) : ℤ)) (Finset.Ico (-(n : ℤ)) 0) := by
        ext x
        simp only [Finset.mem_Ico, Finset.mem_insert]
        push_cast
        omega
      rw [e, Finset.sum_insert (by simp only [Finset.mem_Ico]; push_cast; omega), ih]
      have e2 : -((n + 1 : ℕ) : ℤ) + 1 = -(n : ℤ) := by push_cast; ring
      rw [e2]; ring
  obtain ⟨m, hm⟩ := J.bddBelow
  obtain ⟨n, hn1, hn2⟩ : ∃ n : ℕ, -(n : ℤ) ≤ m ∧ -(n : ℤ) ≤ b :=
    ⟨m.natAbs + b.natAbs, by omega, by omega⟩
  rw [← hb _ hn2, ← tel n]
  symm
  refine Finset.sum_subset ?_ ?_
  · intro x hx
    rw [Finset.mem_filter] at hx
    exact Finset.mem_Ico.2 ⟨hn1.trans (hm (Finset.mem_coe.2 hx.1)), hx.2⟩
  · intro x hx hx'
    refine hJ x fun h => hx' (Finset.mem_filter.2 ⟨h, (Finset.mem_Ico.1 hx).2⟩)

section

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

/- English proof (translation)
Assemble the required witnesses or components as `⟨v ⊗ₜ[Qp] ⟨b, hb⟩, rfl⟩`.
-/
theorem tmul_mem_filV (a : ℤ) (v : V) (b : BdR) (hb : b ∈ PD.Fil a) :
    v ⊗ₜ[Qp] b ∈ FilV PD (LL := LL) (V := V) a :=
  ⟨v ⊗ₜ[Qp] ⟨b, hb⟩, rfl⟩

/- English proof (translation)
Establish `hA : Antitone PD.Fil` using `antitone_int_of_succ_le PD.Fil_anti`. Introduce and unpack `a b hab _ ⟨y, rfl⟩`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => rw [map_zero]`. Conclude with `Submodule.zero_mem _`.

Consider the case `tmul v c => exact tmul_mem_filV PD a v c.1 (hA hab c.2)`. Consider the case `add x y hx hy => rw [map_add]`. Conclude with `Submodule.add_mem _ hx hy`.
-/
theorem filV_antitone : Antitone (FilV PD (LL := LL) (V := V)) := by
  have hA : Antitone PD.Fil := antitone_int_of_succ_le PD.Fil_anti
  rintro a b hab _ ⟨y, rfl⟩
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | tmul v c => exact tmul_mem_filV PD a v c.1 (hA hab c.2)
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, Submodule.zero_mem _⟩`. Consider the case `tmul v c`. Take `⟨a, ha⟩` from `PD.Fil_exh c`. Conclude with `⟨a, tmul_mem_filV PD a v c ha⟩`.

Consider the case `add x y hx hy`. Take `⟨a, ha⟩` from `hx`. Take `⟨b, hb⟩` from `hy`. Conclude with `⟨min a b, Submodule.add_mem _ (filV_antitone PD (min_le_left a b) ha) (filV_antitone PD (min_le_right a b) hb)⟩`.
-/
theorem filV_exhaustive (x : V ⊗[Qp] BdR) : ∃ a, x ∈ FilV PD (LL := LL) (V := V) a := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, Submodule.zero_mem _⟩
  | tmul v c =>
    obtain ⟨a, ha⟩ := PD.Fil_exh c
    exact ⟨a, tmul_mem_filV PD a v c ha⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨min a b, Submodule.add_mem _ (filV_antitone PD (min_le_left a b) ha)
      (filV_antitone PD (min_le_right a b) hb)⟩

/- English proof (translation)
Establish `: FiniteDimensional LL ↥(DdRE PD ρ τ)` using `Submodule.finiteDimensional_of_le (S₂ := DdR PD ρ) inf_le_left`. Take `⟨b, hb⟩` from `exists_eq_of_exhaustive (DdRE PD ρ τ) (FildR PD ρ τ) (fun a b hab => inf_le_inf_left _ (filV_antitone PD hab)) (fun a => inf_le_left) (fun x hx => (filV_exhaustive PD (LL := LL) x).imp fun a ha => ⟨hx, ha⟩)`. Conclude with `telescope (fun a => (Module.finrank LL ↥(FildR PD ρ τ a) : ℤ)) _ b (fun a ha => by rw [hb a ha]) J hJ`.
-/
theorem codim_fil_zero (ρ : Representation LL G V) [FiniteDimensional LL ↥(DdR PD ρ)]
    (τ : K →ₐ[Qp] LL) (J : Finset ℤ) (hJ : ∀ a, a ∉ J → multV PD ρ τ a = 0) :
    (Module.finrank LL ↥(DdRE PD ρ τ) : ℤ) - Module.finrank LL ↥(FildR PD ρ τ 0)
      = ∑ a ∈ J.filter (· < 0), multV PD ρ τ a := by
  have : FiniteDimensional LL ↥(DdRE PD ρ τ) :=
    Submodule.finiteDimensional_of_le (S₂ := DdR PD ρ) inf_le_left
  obtain ⟨b, hb⟩ := exists_eq_of_exhaustive (DdRE PD ρ τ) (FildR PD ρ τ)
    (fun a b hab => inf_le_inf_left _ (filV_antitone PD hab)) (fun a => inf_le_left)
    (fun x hx => (filV_exhaustive PD (LL := LL) x).imp fun a ha => ⟨hx, ha⟩)
  exact telescope (fun a => (Module.finrank LL ↥(FildR PD ρ τ a) : ℤ)) _ b
    (fun a ha => by rw [hb a ha]) J hJ

end

/- English proof (translation)
Introduce `l _ P AI T K LL V _ _ _ _ _ ρ τ J hJ`. Use `(GlobalTheory.Per.TiedDdR.ddR_finrank_le l P AI T K LL V ρ).1` as an intermediate fact. Conclude with `codim_fil_zero (P.PD K) ρ τ J hJ`.
-/
theorem fil_count : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
    ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V]
      [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V)
      (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (J : Finset ℤ), (∀ a, a ∉ J → multV (P.PD K) ρ τ a = 0) →
      (Module.finrank ↥LL.1 ↥(DdRE (P.PD K) ρ τ) : ℤ) - Module.finrank ↥LL.1 ↥(FildR (P.PD K) ρ τ 0)
        = ∑ a ∈ J.filter (· < 0), multV (P.PD K) ρ τ a := by
  intro l _ P AI T K LL V _ _ _ _ _ ρ τ J hJ
  have := (GlobalTheory.Per.TiedDdR.ddR_finrank_le l P AI T K LL V ρ).1
  exact codim_fil_zero (P.PD K) ρ τ J hJ

end GlobalTheory.Per.FilCount
