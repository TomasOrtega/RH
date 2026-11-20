import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeModelVacuumTranslateClassesIndependent
open Matrix

namespace GlobalTheory.Hk3

/- English proof (translation)
Introduce `L _ _ _ _ ϖ σ q δ n n' JS JT ψ M _ _ ρ ω hP s hvac hspan w hw`. Establish `hind` using `locVac_span_classes_indep L ϖ σ q δ n n' JS JT ψ M ρ ω hP s hvac`. Take `⟨hU, -, hSint, hTint, hS, hT, hδ, -, hpsi_ne, hρ0, hρ, -, -, -⟩` from `hP`. Establish `hσ` using `hU.1`. Establish `hA : ∀ x y : Matrix (Fin n') (Fin n) L, σ (locH σ δ JS JT x y) = - locH σ δ JS JT y x` using `locH_conj σ hσ δ hδ.2 JS JT hS hT`.

Establish `hψinv : ∀ a, ψ a * ψ (-a) = 1` using `fun a => by`. Rewrite using `[← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]`. Establish `hΛ : intMatSub (L` using `L) n n' = HoweDuality.intMat L n' n := AddSubgroup.ext fun _ => Iff.rfl`. Establish `hshift : ∀ x u, u ∈ intMatSub (L` using `L) n n' → ρ (x + u) s = ψ (-((locH σ δ JS JT x u + σ (locH σ δ JS JT x u)) / 2)) • ρ x s := by`. Introduce `x u hu`.

Establish `h1 : ρ x s = ψ ((locH σ δ JS JT x u + σ (locH σ δ JS JT x u)) / 2) • ρ (x + u) s`. Use `congrArg (fun f => f s) (hρ x u)` as an intermediate fact. Simplify using `only [Module.End.mul_apply, LinearMap.smul_apply] at this`. Rewrite `this` using `[hvac u hu]`. Then use the resulting hypothesis. Rewrite using `[h1, smul_smul, mul_comm, hψinv, one_smul]`.

Establish `heig : ∀ x u, u ∈ intMatSub (L` using `L) n n' → ρ u (ρ x s) = ψ (locH σ δ JS JT u x + σ (locH σ δ JS JT u x)) • ρ x s := by`. Introduce `x u hu`. Use `congrArg (fun f => f s) (hρ u x)` as an intermediate fact. Simplify using `only [Module.End.mul_apply, LinearMap.smul_apply] at this`. Rewrite using `[this, add_comm u x, hshift x u hu, smul_smul, ← AddChar.map_add_eq_mul]`.

Use `congr 2`. Rewrite using `[hA u x, hA x u]`. Expand and normalize the polynomial expressions, which then agree. Use `set Λ := HoweDuality.intMat L n' n with hΛdef`. Use `set V : Matrix (Fin n') (Fin n) L ⧸ Λ → Submodule ℂ M := fun c => Submodule.span ℂ {ρ c.out s} with hVdef`.

Establish `hVind : iSupIndep V`. Use `hind.mono fun c => Submodule.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `_ rfl`. Conclude with `Submodule.subset_span ⟨c.out, QuotientAddGroup.out_eq' c, rfl⟩`. Establish `hmemV : ∀ x, ρ x s ∈ V (QuotientAddGroup.mk x)`.

Introduce `x`. Establish `hm : -(QuotientAddGroup.mk x : Matrix (Fin n') (Fin n) L ⧸ Λ).out + x ∈ intMatSub (L` using `L) n n' := by`. Rewrite using `[hΛ]`. Conclude with `QuotientAddGroup.eq.mp (by rw [QuotientAddGroup.out_eq'])`. Use `hshift (QuotientAddGroup.mk x : Matrix (Fin n') (Fin n) L ⧸ Λ).out _ hm` as an intermediate fact.

Rewrite `this` using `[add_neg_cancel_left]`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)`. Establish `hwV : w ∈ ⨆ c, V c`. Establish `hle : Submodule.span ℂ (Set.range fun x => ρ x s) ≤ ⨆ c, V c` using `Submodule.span_le.mpr (by rintro _ ⟨x, rfl⟩; exact Submodule.mem_iSup_of_mem _ (hmemV x))`.

Conclude with `hle (hspan ▸ Submodule.mem_top)`. Take `⟨f, hf, hfw⟩` from `(Submodule.mem_iSup_iff_exists_finsupp V w).mp hwV`. Use `set χ : Matrix (Fin n') (Fin n) L ⧸ Λ → Matrix (Fin n') (Fin n) L → ℂ := fun c u => ψ (locH σ δ JS JT u c.out + σ (locH σ δ JS JT u c.out)) with hχ`. Establish `heigV : ∀ c, ∀ u ∈ intMatSub (L` using `L) n n', ∀ v ∈ V c, ρ u v = χ c u • v := by`. Introduce `c u hu v hv`.

Take `⟨a, rfl⟩` from `Submodule.mem_span_singleton.mp hv`. Rewrite using `[map_smul, heig _ u hu, smul_comm]`. Establish `hzero : ∀ c, c ≠ 0 → f c = 0`. Introduce `c hc`. Take `⟨u, hu, hχu⟩ : ∃ u ∈ intMatSub (L` from `L) n n', χ c u ≠ 1 := by`.

Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Establish `hint` using `intMat_of_psi hU hδ.1 hSint hTint ψ hpsi_ne c.out hcon`. Apply `hc` to reduce the goal to its premises. Rewrite `hint` using `[hΛ]`.

Rewrite using `[← QuotientAddGroup.out_eq' c, QuotientAddGroup.eq_zero_iff]`. Conclude with `hint`. Establish `hsum : (f.support.sum fun d => (χ d u - 1) • f d) = 0`. Establish `e1 : ρ u w = f.support.sum fun d => χ d u • f d`. Rewrite using `[← hfw, Finsupp.sum, map_sum]`.

Conclude with `Finset.sum_congr rfl fun d _ => heigV d u hu _ (hf d)`. Establish `e2 : w = f.support.sum fun d => f d` using `by rw [← hfw, Finsupp.sum]`. Simplify using `only [sub_smul, one_smul, Finset.sum_sub_distrib, ← e1, ← e2, hw u hu, sub_self]`. Distinguish the cases in `hcs : c ∈ f.support`. Rewrite `hsum` using `[← Finset.add_sum_erase _ _ hcs, add_eq_zero_iff_eq_neg]`.

Establish `hmem1 : (χ c u - 1) • f c ∈ V c` using `Submodule.smul_mem _ _ (hf c)`. Establish `hmem2 : (χ c u - 1) • f c ∈ ⨆ (j) (_ : j ≠ c), V j`. Rewrite using `[hsum]`. Use `Submodule.neg_mem _ (Submodule.sum_mem _ fun d hd => ?_)` and prove the remaining obligations. Establish `hdc : d ≠ c` using `Finset.ne_of_mem_erase hd`.

Conclude with `Submodule.mem_iSup_of_mem d (Submodule.mem_iSup_of_mem hdc (Submodule.smul_mem _ _ (hf d)))`. Establish `hz : (χ c u - 1) • f c = 0`. Use `(iSupIndep_def.mp hVind c)` as an intermediate fact. Rewrite `this` using `[Submodule.disjoint_def]`. Conclude with `this _ hmem1 hmem2`.

Conclude with `(smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hχu)`. Conclude with `Finsupp.notMem_support_iff.mp hcs`. Establish `hw0 : w = f 0`. Rewrite using `[← hfw, Finsupp.sum, Finset.sum_eq_single (0 : Matrix (Fin n') (Fin n) L ⧸ Λ)]`. Introduce `d _ hd`.

Conclude with `hzero d hd`. Introduce `h0`. Conclude with `Finsupp.notMem_support_iff.mp h0`. Establish `hout : ρ (0 : Matrix (Fin n') (Fin n) L ⧸ Λ).out s = s`. Apply `hvac` to reduce the goal to its premises.

Establish `: (0 : Matrix (Fin n') (Fin n) L ⧸ Λ).out ∈ Λ`. Rewrite using `[← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.out_eq']`. Conclude with `this`. Use `hf 0` as an intermediate fact. Express the relevant statement in the definitionally equal form `f 0 ∈ Submodule.span ℂ {ρ (0 : Matrix (Fin n') (Fin n) L ⧸ Λ).out s} at this`.

Rewrite `this` using `[hout]`. Rewrite using `[hw0]`. Conclude with `this`.
-/
theorem locVac_mem_span_vac : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M]
    (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M)
    (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M), GlobalTheory.Hk3.LocPair ϖ σ q δ JS JT ψ ρ ω → ∀ s : M, GlobalTheory.Hk3.LocVac ρ s →
    Submodule.span ℂ (Set.range fun x => ρ x s) = ⊤ → ∀ w : M, GlobalTheory.Hk3.LocVac ρ w → w ∈ Submodule.span ℂ {s} := by
  intro L _ _ _ _ ϖ σ q δ n n' JS JT ψ M _ _ ρ ω hP s hvac hspan w hw
  classical
  have hind := locVac_span_classes_indep L ϖ σ q δ n n' JS JT ψ M ρ ω hP s hvac
  obtain ⟨hU, -, hSint, hTint, hS, hT, hδ, -, hpsi_ne, hρ0, hρ, -, -, -⟩ := hP
  have hσ := hU.1
  have hA : ∀ x y : Matrix (Fin n') (Fin n) L, σ (locH σ δ JS JT x y) = - locH σ δ JS JT y x :=
    locH_conj σ hσ δ hδ.2 JS JT hS hT
  have hψinv : ∀ a, ψ a * ψ (-a) = 1 := fun a => by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have hΛ : intMatSub (L := L) n n' = HoweDuality.intMat L n' n := AddSubgroup.ext fun _ => Iff.rfl
  have hshift : ∀ x u, u ∈ intMatSub (L := L) n n' →
      ρ (x + u) s = ψ (-((locH σ δ JS JT x u + σ (locH σ δ JS JT x u)) / 2)) • ρ x s := by
    intro x u hu
    have h1 : ρ x s = ψ ((locH σ δ JS JT x u + σ (locH σ δ JS JT x u)) / 2) • ρ (x + u) s := by
      have := congrArg (fun f => f s) (hρ x u)
      simp only [Module.End.mul_apply, LinearMap.smul_apply] at this
      rwa [hvac u hu] at this
    rw [h1, smul_smul, mul_comm, hψinv, one_smul]
  have heig : ∀ x u, u ∈ intMatSub (L := L) n n' →
      ρ u (ρ x s) = ψ (locH σ δ JS JT u x + σ (locH σ δ JS JT u x)) • ρ x s := by
    intro x u hu
    have := congrArg (fun f => f s) (hρ u x)
    simp only [Module.End.mul_apply, LinearMap.smul_apply] at this
    rw [this, add_comm u x, hshift x u hu, smul_smul, ← AddChar.map_add_eq_mul]
    congr 2
    rw [hA u x, hA x u]; ring
  set Λ := HoweDuality.intMat L n' n with hΛdef
  set V : Matrix (Fin n') (Fin n) L ⧸ Λ → Submodule ℂ M := fun c => Submodule.span ℂ {ρ c.out s} with hVdef
  have hVind : iSupIndep V := by
    refine hind.mono fun c => Submodule.span_le.mpr ?_
    rintro _ rfl
    exact Submodule.subset_span ⟨c.out, QuotientAddGroup.out_eq' c, rfl⟩
  have hmemV : ∀ x, ρ x s ∈ V (QuotientAddGroup.mk x) := by
    intro x
    have hm : -(QuotientAddGroup.mk x : Matrix (Fin n') (Fin n) L ⧸ Λ).out + x ∈ intMatSub (L := L) n n' := by
      rw [hΛ]
      exact QuotientAddGroup.eq.mp (by rw [QuotientAddGroup.out_eq'])
    have := hshift (QuotientAddGroup.mk x : Matrix (Fin n') (Fin n) L ⧸ Λ).out _ hm
    rw [add_neg_cancel_left] at this
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have hwV : w ∈ ⨆ c, V c := by
    have hle : Submodule.span ℂ (Set.range fun x => ρ x s) ≤ ⨆ c, V c :=
      Submodule.span_le.mpr (by rintro _ ⟨x, rfl⟩; exact Submodule.mem_iSup_of_mem _ (hmemV x))
    exact hle (hspan ▸ Submodule.mem_top)
  obtain ⟨f, hf, hfw⟩ := (Submodule.mem_iSup_iff_exists_finsupp V w).mp hwV
  set χ : Matrix (Fin n') (Fin n) L ⧸ Λ → Matrix (Fin n') (Fin n) L → ℂ :=
    fun c u => ψ (locH σ δ JS JT u c.out + σ (locH σ δ JS JT u c.out)) with hχ
  have heigV : ∀ c, ∀ u ∈ intMatSub (L := L) n n', ∀ v ∈ V c, ρ u v = χ c u • v := by
    intro c u hu v hv
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [map_smul, heig _ u hu, smul_comm]
  have hzero : ∀ c, c ≠ 0 → f c = 0 := by
    intro c hc
    obtain ⟨u, hu, hχu⟩ : ∃ u ∈ intMatSub (L := L) n n', χ c u ≠ 1 := by
      by_contra hcon
      push_neg at hcon
      have hint := intMat_of_psi hU hδ.1 hSint hTint ψ hpsi_ne c.out hcon
      apply hc
      rw [hΛ] at hint
      rw [← QuotientAddGroup.out_eq' c, QuotientAddGroup.eq_zero_iff]
      exact hint
    have hsum : (f.support.sum fun d => (χ d u - 1) • f d) = 0 := by
      have e1 : ρ u w = f.support.sum fun d => χ d u • f d := by
        rw [← hfw, Finsupp.sum, map_sum]
        exact Finset.sum_congr rfl fun d _ => heigV d u hu _ (hf d)
      have e2 : w = f.support.sum fun d => f d := by rw [← hfw, Finsupp.sum]
      simp only [sub_smul, one_smul, Finset.sum_sub_distrib, ← e1, ← e2, hw u hu, sub_self]
    by_cases hcs : c ∈ f.support
    · rw [← Finset.add_sum_erase _ _ hcs, add_eq_zero_iff_eq_neg] at hsum
      have hmem1 : (χ c u - 1) • f c ∈ V c := Submodule.smul_mem _ _ (hf c)
      have hmem2 : (χ c u - 1) • f c ∈ ⨆ (j) (_ : j ≠ c), V j := by
        rw [hsum]
        refine Submodule.neg_mem _ (Submodule.sum_mem _ fun d hd => ?_)
        have hdc : d ≠ c := Finset.ne_of_mem_erase hd
        exact Submodule.mem_iSup_of_mem d (Submodule.mem_iSup_of_mem hdc (Submodule.smul_mem _ _ (hf d)))
      have hz : (χ c u - 1) • f c = 0 := by
        have := (iSupIndep_def.mp hVind c)
        rw [Submodule.disjoint_def] at this
        exact this _ hmem1 hmem2
      exact (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hχu)
    · exact Finsupp.notMem_support_iff.mp hcs
  have hw0 : w = f 0 := by
    rw [← hfw, Finsupp.sum, Finset.sum_eq_single (0 : Matrix (Fin n') (Fin n) L ⧸ Λ)]
    · intro d _ hd; exact hzero d hd
    · intro h0; exact Finsupp.notMem_support_iff.mp h0
  have hout : ρ (0 : Matrix (Fin n') (Fin n) L ⧸ Λ).out s = s := by
    apply hvac
    have : (0 : Matrix (Fin n') (Fin n) L ⧸ Λ).out ∈ Λ := by
      rw [← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.out_eq']
    exact this
  have := hf 0
  change f 0 ∈ Submodule.span ℂ {ρ (0 : Matrix (Fin n') (Fin n) L ⧸ Λ).out s} at this
  rw [hout] at this
  rw [hw0]; exact this

end GlobalTheory.Hk3
