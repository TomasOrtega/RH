import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteCohomology
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Formalism.SharpRestriction.LevelLetterCocycles.JsetEmb
import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfJumpsBdd
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain TensorProduct Module GlobalTheory.WeilDeligne GlobalTheory.Pst Polynomial

/- English proof (translation)
Introduce `l _ P ι K LL V _ _ _ _ _ ρ hV hc`. Establish `hk` using `mem_Dst_and_monV_eq_zero_iff l P K LL V ρ`. Use `set S := Submodule.span ℂ {z : WDSpace P ι ρ | ∃ (x : V ⊗[ℚ_[l]] P.R.B) (y : ↥(Dpst P ρ)), x ∈ Dcris (P.PD K) ρ ∧ (y : V ⊗[ℚ_[l]] Bst P) = crisIncl P ↥LL.1 V x ∧ z = wdMk P ι ρ y} with hS`. Establish `key : ∀ (x : V ⊗[ℚ_[l]] Bst P), x ∈ Dpst P ρ → ∃ h : x ∈ Dpst P ρ, wdMk P ι ρ ⟨x, h⟩ ∈ S`. Introduce `x hx`.

Use `AddSubgroup.closure_induction (p := fun y _ => ∃ h : y ∈ Dpst P ρ, wdMk P ι ρ ⟨y, h⟩ ∈ S) ?_ ?_ ?_ ?_ (GlobalTheory.PstLaws.mem_closure_of_isCrys P ρ hV hc x hx)` and prove the remaining obligations. Introduce and unpack `_ ⟨c, s, hs, rfl⟩`. Establish `hsD : s ∈ Dpst P ρ` using `Dst_resTo_le P ρ le_rfl ((hk s).mpr hs).1`. Take `⟨x₀, hx₀, e⟩` from `hs`. Use `⟨mulV_mem_Dpst P ρ c s hsD, ?_⟩` and prove the remaining obligations.

Establish `h1 : wdMk P ι ρ ⟨s, hsD⟩ ∈ S` using `Submodule.subset_span ⟨x₀, ⟨s, hsD⟩, hx₀, e.symm, rfl⟩`. Establish `h2` using `S.smul_mem (ι (c : Om l)) h1`. Rewrite `h2` using `[← wdMk_mul]`. Conclude with `h2`. Use `⟨zero_mem _, ?_⟩` and prove the remaining obligations.

Establish `h1 : wdMk P ι ρ 0 ∈ S` using `by rw [wdMk_zero]; exact zero_mem _`. Conclude with `h1`. Introduce and unpack `y z _ _ ⟨hy, h1⟩ ⟨hz, h2⟩`. Use `⟨add_mem hy hz, ?_⟩` and prove the remaining obligations. Establish `h3` using `S.add_mem h1 h2`.

Rewrite `h3` using `[← wdMk_add]`. Conclude with `h3`. Introduce and unpack `y _ ⟨hy, h1⟩`. Use `⟨neg_mem hy, ?_⟩` and prove the remaining obligations. Establish `h2` using `S.smul_mem (ι (((-1 : ↥LL.1) : ↥LL.1) : Om l)) h1`.

Rewrite `h2` using `[← wdMk_smul, neg_one_smul]`. Conclude with `h2`. Rewrite using `[eq_top_iff, ← span_wdMk P ι ρ, Submodule.span_le]`. Introduce and unpack `_ ⟨x, rfl⟩`. Conclude with `(key x.1 x.2).2`.
-/
theorem UpperTheory.weil_deligne_span_crystalline :
    ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) {K LL : FinExt l} {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), IsPst P ρ → IsCrys (P.PD K) ρ → Submodule.span ℂ {z : WDSpace P ι ρ | ∃ (x : V ⊗[ℚ_[l]] P.R.B) (y : ↥(Dpst P ρ)), x ∈ Dcris (P.PD K) ρ ∧ (y : V ⊗[ℚ_[l]] Bst P) = crisIncl P ↥LL.1 V x ∧ z = wdMk P ι ρ y} = ⊤ := by
  intro l _ P ι K LL V _ _ _ _ _ ρ hV hc
  have hk := mem_Dst_and_monV_eq_zero_iff l P K LL V ρ
  set S := Submodule.span ℂ {z : WDSpace P ι ρ | ∃ (x : V ⊗[ℚ_[l]] P.R.B) (y : ↥(Dpst P ρ)), x ∈ Dcris (P.PD K) ρ ∧ (y : V ⊗[ℚ_[l]] Bst P) = crisIncl P ↥LL.1 V x ∧ z = wdMk P ι ρ y} with hS
  have key : ∀ (x : V ⊗[ℚ_[l]] Bst P), x ∈ Dpst P ρ → ∃ h : x ∈ Dpst P ρ, wdMk P ι ρ ⟨x, h⟩ ∈ S := by
    intro x hx
    refine AddSubgroup.closure_induction
      (p := fun y _ => ∃ h : y ∈ Dpst P ρ, wdMk P ι ρ ⟨y, h⟩ ∈ S) ?_ ?_ ?_ ?_
      (GlobalTheory.PstLaws.mem_closure_of_isCrys P ρ hV hc x hx)
    · rintro _ ⟨c, s, hs, rfl⟩
      have hsD : s ∈ Dpst P ρ := Dst_resTo_le P ρ le_rfl ((hk s).mpr hs).1
      obtain ⟨x₀, hx₀, e⟩ := hs
      refine ⟨mulV_mem_Dpst P ρ c s hsD, ?_⟩
      have h1 : wdMk P ι ρ ⟨s, hsD⟩ ∈ S := Submodule.subset_span ⟨x₀, ⟨s, hsD⟩, hx₀, e.symm, rfl⟩
      have h2 := S.smul_mem (ι (c : Om l)) h1
      rw [← wdMk_mul] at h2
      exact h2
    · refine ⟨zero_mem _, ?_⟩
      have h1 : wdMk P ι ρ 0 ∈ S := by rw [wdMk_zero]; exact zero_mem _
      exact h1
    · rintro y z _ _ ⟨hy, h1⟩ ⟨hz, h2⟩
      refine ⟨add_mem hy hz, ?_⟩
      have h3 := S.add_mem h1 h2
      rw [← wdMk_add] at h3
      exact h3
    · rintro y _ ⟨hy, h1⟩
      refine ⟨neg_mem hy, ?_⟩
      have h2 := S.smul_mem (ι (((-1 : ↥LL.1) : ↥LL.1) : Om l)) h1
      rw [← wdMk_smul, neg_one_smul] at h2
      exact h2
  rw [eq_top_iff, ← span_wdMk P ι ρ, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  exact (key x.1 x.2).2
