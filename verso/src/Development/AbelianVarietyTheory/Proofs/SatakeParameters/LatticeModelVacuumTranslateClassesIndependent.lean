import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemIntMat
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalThetaPairExistence

namespace GlobalTheory.Hk3

/- English proof (translation)
Introduce `L _ _ _ _ ϖ σ q δ n n' JS JT ψ M _ _ ρ ω hP s hvac`. Take `⟨hU, -, hSint, hTint, hS, hT, hδ, -, hpsi_ne, hρ0, hρ, -, -, -⟩` from `hP`. Establish `hσ` using `hU.1`. Establish `hA : ∀ x y : Matrix (Fin n') (Fin n) L, σ (locH σ δ JS JT x y) = - locH σ δ JS JT y x` using `locH_conj σ hσ δ hδ.2 JS JT hS hT`. Establish `hψinv : ∀ a, ψ a * ψ (-a) = 1` using `fun a => by`.

Rewrite using `[← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]`. Establish `hΛ : intMatSub (L` using `L) n n' = HoweDuality.intMat L n' n := AddSubgroup.ext fun _ => Iff.rfl`. Establish `hshift : ∀ t, LocVac ρ t → ∀ x u, u ∈ intMatSub (L` using `L) n n' → ρ (x + u) t = ψ (-((locH σ δ JS JT x u + σ (locH σ δ JS JT x u)) / 2)) • ρ x t := by`. Introduce `t ht x u hu`. Establish `h1 : ρ x t = ψ ((locH σ δ JS JT x u + σ (locH σ δ JS JT x u)) / 2) • ρ (x + u) t`.

Use `congrArg (fun f => f t) (hρ x u)` as an intermediate fact. Simplify using `only [Module.End.mul_apply, LinearMap.smul_apply] at this`. Rewrite `this` using `[ht u hu]`. Then use the resulting hypothesis. Rewrite using `[h1, smul_smul, mul_comm, hψinv, one_smul]`. Establish `heig : ∀ t, LocVac ρ t → ∀ x u, u ∈ intMatSub (L` using `L) n n' → ρ u (ρ x t) = ψ (locH σ δ JS JT u x + σ (locH σ δ JS JT u x)) • ρ x t := by`.

Introduce `t ht x u hu`. Use `congrArg (fun f => f t) (hρ u x)` as an intermediate fact. Simplify using `only [Module.End.mul_apply, LinearMap.smul_apply] at this`. Rewrite using `[this, add_comm u x, hshift t ht x u hu, smul_smul, ← AddChar.map_add_eq_mul]`. Use `congr 2`.

Rewrite using `[hA u x, hA x u]`. Expand and normalize the polynomial expressions, which then agree. Establish `hdist : ∀ x y : Matrix (Fin n') (Fin n) L, (∀ u ∈ intMatSub (L` using `L) n n', ψ (locH σ δ JS JT u x + σ (locH σ δ JS JT u x)) = ψ (locH σ δ JS JT u y + σ (locH σ δ JS JT u y))) → x - y ∈ intMatSub (L := L) n n' := by`. Introduce `x y hxy`. Use `intMat_of_psi hU hδ.1 hSint hTint ψ hpsi_ne (x - y) (fun u hu => ?_)` and prove the remaining obligations.

Establish `e : locH σ δ JS JT u (x - y) + σ (locH σ δ JS JT u (x - y)) = (locH σ δ JS JT u x + σ (locH σ δ JS JT u x)) + -(locH σ δ JS JT u y + σ (locH σ δ JS JT u y))`. Rewrite using `[locH_sub_right, map_sub]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, AddChar.map_add_eq_mul, hxy u hu, hψinv]`. Use `set Λ := HoweDuality.intMat L n' n with hΛdef`.

Establish `hle : (fun c : Matrix (Fin n') (Fin n) L ⧸ Λ => Submodule.span ℂ {w : M | ∃ x : Matrix (Fin n') (Fin n) L, (QuotientAddGroup.mk x : Matrix (Fin n') (Fin n) L ⧸ Λ) = c ∧ w = ρ x s}) ≤ fun c => Submodule.span ℂ {ρ c.out s}`. Introduce `c`. Use `Submodule.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `w ⟨x, hx, rfl⟩`. Establish `hm : -c.out + x ∈ intMatSub (L` using `L) n n' := by`.

Rewrite using `[hΛ]`. Conclude with `QuotientAddGroup.eq.mp (by rw [QuotientAddGroup.out_eq', hx])`. Use `hshift s hvac c.out _ hm` as an intermediate fact. Rewrite `this` using `[add_neg_cancel_left]`. Rewrite using `[SetLike.mem_coe, this]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)`. Use `iSupIndep.mono ?_ hle` and prove the remaining obligations. Distinguish the cases in `hs : s = 0`. Establish `hb : (fun c : Matrix (Fin n') (Fin n) L ⧸ Λ => Submodule.span ℂ {ρ c.out s}) = fun _ => ⊥`. Use function extensionality and compare the values at `c`.

Rewrite using `[hs, map_zero, Submodule.span_singleton_eq_bot]`. Rewrite using `[hb, iSupIndep_def]`. Introduce `i`. Conclude with `disjoint_bot_left`. Establish `hnz : ∀ x, ρ x s ≠ 0`.

Introduce `x h0`. Use `congrArg (fun f => f s) (hρ (-x) x)` as an intermediate fact. Simplify using `only [Module.End.mul_apply, LinearMap.smul_apply, h0, map_zero, neg_add_cancel, hρ0, Module.End.one_apply] at this`. Establish `hne : ψ ((locH σ δ JS JT (-x) x + σ (locH σ δ JS JT (-x) x)) / 2) ≠ 0`. Introduce `h`.

Use `hψinv ((locH σ δ JS JT (-x) x + σ (locH σ δ JS JT (-x) x)) / 2)` as an intermediate fact. Rewrite `this` using `[h, zero_mul]`. Conclude with `zero_ne_one this`. Conclude with `hs ((smul_eq_zero.mp this.symm).resolve_left hne)`. Use `LinearIndependent.iSupIndep_span_singleton ?_` and prove the remaining obligations.

Rewrite using `[linearIndependent_iff']`. Introduce `I C hC y hy`. Establish `hind` using `eig_indep (fun u : intMatSub (L := L) n n' => ρ (u : Matrix (Fin n') (Fin n) L)) (fun (y : Matrix (Fin n') (Fin n) L ⧸ Λ) (u : intMatSub (L := L) n n') => ψ (locH σ δ JS JT (u : Matrix (Fin n') (Fin n) L) y.out + σ (locH σ δ JS JT (u : Matrix (Fin n') (Fin n) L) y.out))) (fun y = …`. Introduce `y _ y' _ hyy`. Assume the negation of the conclusion as `hcon`.

Use `push_neg at hcon`. Apply `hyy` to reduce the goal to its premises. Establish `hm` using `hdist y.out y'.out (fun u hu => hcon ⟨u, hu⟩)`. Rewrite `hm` using `[hΛ]`. Rewrite using `[← QuotientAddGroup.out_eq' y, ← QuotientAddGroup.out_eq' y', QuotientAddGroup.eq_iff_sub_mem]`.

Conclude with `hm)`. Use `C hC`. Conclude with `(smul_eq_zero.mp (hind y hy)).resolve_right (hnz _)`.
-/
theorem locVac_span_classes_indep : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M]
    (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M)
    (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M), GlobalTheory.Hk3.LocPair ϖ σ q δ JS JT ψ ρ ω → ∀ s : M, GlobalTheory.Hk3.LocVac ρ s →
    iSupIndep (fun c : Matrix (Fin n') (Fin n) L ⧸ GlobalTheory.Hk3.HoweDuality.intMat L n' n =>
      Submodule.span ℂ {w : M | ∃ x : Matrix (Fin n') (Fin n) L,
        (QuotientAddGroup.mk x : Matrix (Fin n') (Fin n) L ⧸ GlobalTheory.Hk3.HoweDuality.intMat L n' n) = c ∧ w = ρ x s}) := by
  intro L _ _ _ _ ϖ σ q δ n n' JS JT ψ M _ _ ρ ω hP s hvac
  classical
  obtain ⟨hU, -, hSint, hTint, hS, hT, hδ, -, hpsi_ne, hρ0, hρ, -, -, -⟩ := hP
  have hσ := hU.1
  have hA : ∀ x y : Matrix (Fin n') (Fin n) L, σ (locH σ δ JS JT x y) = - locH σ δ JS JT y x :=
    locH_conj σ hσ δ hδ.2 JS JT hS hT
  have hψinv : ∀ a, ψ a * ψ (-a) = 1 := fun a => by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have hΛ : intMatSub (L := L) n n' = HoweDuality.intMat L n' n := AddSubgroup.ext fun _ => Iff.rfl
  have hshift : ∀ t, LocVac ρ t → ∀ x u, u ∈ intMatSub (L := L) n n' →
      ρ (x + u) t = ψ (-((locH σ δ JS JT x u + σ (locH σ δ JS JT x u)) / 2)) • ρ x t := by
    intro t ht x u hu
    have h1 : ρ x t = ψ ((locH σ δ JS JT x u + σ (locH σ δ JS JT x u)) / 2) • ρ (x + u) t := by
      have := congrArg (fun f => f t) (hρ x u)
      simp only [Module.End.mul_apply, LinearMap.smul_apply] at this
      rwa [ht u hu] at this
    rw [h1, smul_smul, mul_comm, hψinv, one_smul]
  have heig : ∀ t, LocVac ρ t → ∀ x u, u ∈ intMatSub (L := L) n n' →
      ρ u (ρ x t) = ψ (locH σ δ JS JT u x + σ (locH σ δ JS JT u x)) • ρ x t := by
    intro t ht x u hu
    have := congrArg (fun f => f t) (hρ u x)
    simp only [Module.End.mul_apply, LinearMap.smul_apply] at this
    rw [this, add_comm u x, hshift t ht x u hu, smul_smul, ← AddChar.map_add_eq_mul]
    congr 2
    rw [hA u x, hA x u]; ring
  have hdist : ∀ x y : Matrix (Fin n') (Fin n) L, (∀ u ∈ intMatSub (L := L) n n',
      ψ (locH σ δ JS JT u x + σ (locH σ δ JS JT u x)) = ψ (locH σ δ JS JT u y + σ (locH σ δ JS JT u y))) →
      x - y ∈ intMatSub (L := L) n n' := by
    intro x y hxy
    refine intMat_of_psi hU hδ.1 hSint hTint ψ hpsi_ne (x - y) (fun u hu => ?_)
    have e : locH σ δ JS JT u (x - y) + σ (locH σ δ JS JT u (x - y)) =
        (locH σ δ JS JT u x + σ (locH σ δ JS JT u x)) + -(locH σ δ JS JT u y + σ (locH σ δ JS JT u y)) := by
      rw [locH_sub_right, map_sub]; ring
    rw [e, AddChar.map_add_eq_mul, hxy u hu, hψinv]
  set Λ := HoweDuality.intMat L n' n with hΛdef

  have hle : (fun c : Matrix (Fin n') (Fin n) L ⧸ Λ =>
      Submodule.span ℂ {w : M | ∃ x : Matrix (Fin n') (Fin n) L,
        (QuotientAddGroup.mk x : Matrix (Fin n') (Fin n) L ⧸ Λ) = c ∧ w = ρ x s}) ≤
      fun c => Submodule.span ℂ {ρ c.out s} := by
    intro c
    refine Submodule.span_le.mpr ?_
    rintro w ⟨x, hx, rfl⟩
    have hm : -c.out + x ∈ intMatSub (L := L) n n' := by
      rw [hΛ]
      exact QuotientAddGroup.eq.mp (by rw [QuotientAddGroup.out_eq', hx])
    have := hshift s hvac c.out _ hm
    rw [add_neg_cancel_left] at this
    rw [SetLike.mem_coe, this]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  refine iSupIndep.mono ?_ hle
  by_cases hs : s = 0
  · have hb : (fun c : Matrix (Fin n') (Fin n) L ⧸ Λ => Submodule.span ℂ {ρ c.out s}) = fun _ => ⊥ := by
      funext c; rw [hs, map_zero, Submodule.span_singleton_eq_bot]
    rw [hb, iSupIndep_def]
    intro i
    exact disjoint_bot_left
  have hnz : ∀ x, ρ x s ≠ 0 := by
    intro x h0
    have := congrArg (fun f => f s) (hρ (-x) x)
    simp only [Module.End.mul_apply, LinearMap.smul_apply, h0, map_zero, neg_add_cancel, hρ0,
      Module.End.one_apply] at this
    have hne : ψ ((locH σ δ JS JT (-x) x + σ (locH σ δ JS JT (-x) x)) / 2) ≠ 0 := by
      intro h; have := hψinv ((locH σ δ JS JT (-x) x + σ (locH σ δ JS JT (-x) x)) / 2); rw [h, zero_mul] at this
      exact zero_ne_one this
    exact hs ((smul_eq_zero.mp this.symm).resolve_left hne)
  refine LinearIndependent.iSupIndep_span_singleton ?_
  rw [linearIndependent_iff']
  intro I C hC y hy
  have hind := eig_indep (fun u : intMatSub (L := L) n n' => ρ (u : Matrix (Fin n') (Fin n) L))
    (fun (y : Matrix (Fin n') (Fin n) L ⧸ Λ) (u : intMatSub (L := L) n n') =>
      ψ (locH σ δ JS JT (u : Matrix (Fin n') (Fin n) L) y.out + σ (locH σ δ JS JT (u : Matrix (Fin n') (Fin n) L) y.out)))
    (fun y => ρ y.out s) (fun y u => heig s hvac y.out u u.2) I
    (by
      intro y _ y' _ hyy
      by_contra hcon
      push_neg at hcon
      apply hyy
      have hm := hdist y.out y'.out (fun u hu => hcon ⟨u, hu⟩)
      rw [hΛ] at hm
      rw [← QuotientAddGroup.out_eq' y, ← QuotientAddGroup.out_eq' y', QuotientAddGroup.eq_iff_sub_mem]
      exact hm)
    C hC
  exact (smul_eq_zero.mp (hind y hy)).resolve_right (hnz _)

end GlobalTheory.Hk3
