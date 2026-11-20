import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdBetaK
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarOmLocPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarGlob
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.GramNondeg

noncomputable section

open scoped Classical
open NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdBetaS

open OmP

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

/- English proof (translation)
Use `split_ifs with h`. Rewrite using `[h.1, h.2]`. Conclude with `FsLA.gram_fvec_last A`. Conclude with `FsLA.gram_fvec_zero A c a (by tauto)`.
-/
theorem hT_fvec_self {T : E} (A : FlagG S r T) (c a : Fin (r + 1)) :
    S.hT (A.fvec c) (A.fvec a) = if c = Fin.last r ∧ a = Fin.last r then -T else 0 := by
  split_ifs with h
  · rw [h.1, h.2]; exact FsLA.gram_fvec_last A
  · exact FsLA.gram_fvec_zero A c a (by tauto)

/- English proof (translation)
Take `⟨κ, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun E).1 hy`. Rewrite `h`, the goal using `[Fintype.sum_sum_type]`. Simplify using `only [Sum.elim_inl, Sum.elim_inr] at h ⊢`. Use `set yA := ∑ a, κ (Sum.inl a) • A.fvec a with hyA`. Use `set yB := ∑ b, κ (Sum.inr b) • B.fvec b with hyB`.

Establish `hA : ∀ c, S.hT (A.fvec c) yA = if c = Fin.last r then -TA * κ (Sum.inl (Fin.last r)) else 0`. Introduce `c`. Rewrite using `[hyA, map_sum]`. Simplify using `only [map_smul, smul_eq_mul, hT_fvec_self]`. Rewrite using `[Finset.sum_eq_single (Fin.last r)]`.

Apply the tactic sequence `split_ifs with h1 h2 h2 <;> simp_all [mul_comm]`. Introduce `b _ hb`. Simplify using `[hb]`. Simplify using the standard rewrite rules. Establish `hB : ∀ c, S.hT (A.fvec c) yB = - S.hT (A.fvec c) yA`.

Introduce `c`. Use `h c` as an intermediate fact. Rewrite `this` using `[map_add]`. Conclude with `eq_neg_of_add_eq_zero_right this`. Establish `hcB : ∀ i : Fin r, S.hT (A.e i) (∑ b, κ (Sum.inr b) • B.fvec b) = 0`.

Introduce `i`. Rewrite using `[← hyB, ← fvec_cs, hB, hA]`. Simplify using `[Fin.castSucc_ne_last]`. Establish `hyB'` using `comb_eq A B hdet hΩ (fun b => κ (Sum.inr b)) hcB`. Rewrite `hyB'` using `[← hyB]`.

Establish `hzB : S.hT A.z yB = TA * κ (Sum.inl (Fin.last r))`. Rewrite using `[← fvec_last, hB, hA]`. Simplify using the standard rewrite rules. Use `⟨∑ i : Fin r, κ (Sum.inl i.castSucc) • A.e i, ?_, κ (Sum.inl (Fin.last r)), ?_⟩` and prove the remaining obligations. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`.

Rewrite using `[hyB', hzB, hyA, Fin.sum_univ_castSucc]`. Simplify using `only [fvec_cs, fvec_last]`. Rewrite using `[smul_add, smul_smul, mul_comm]`. Normalize the expressions using the abelian group laws.
-/
theorem dec {TA TB : E} (A : FlagG S r TA) (B : FlagG S r TB) (hdet : (Zhat A B).det ≠ 0) {Ω : S.V}
    (hΩ : OmV A B Ω) {y : S.V} (hy : y ∈ Submodule.span E (Set.range (Sum.elim A.fvec B.fvec)))
    (h : ∀ a, S.hT (A.fvec a) y = 0) : ∃ x ∈ A.X, ∃ c : E, y = x + c • (A.z + TA • Ω) := by
  obtain ⟨κ, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hy
  rw [Fintype.sum_sum_type] at h ⊢
  simp only [Sum.elim_inl, Sum.elim_inr] at h ⊢
  set yA := ∑ a, κ (Sum.inl a) • A.fvec a with hyA
  set yB := ∑ b, κ (Sum.inr b) • B.fvec b with hyB
  have hA : ∀ c, S.hT (A.fvec c) yA = if c = Fin.last r then -TA * κ (Sum.inl (Fin.last r)) else 0 := by
    intro c
    rw [hyA, map_sum]
    simp only [map_smul, smul_eq_mul, hT_fvec_self]
    rw [Finset.sum_eq_single (Fin.last r)]
    · split_ifs with h1 h2 h2 <;> simp_all [mul_comm]
    · intro b _ hb; simp [hb]
    · simp
  have hB : ∀ c, S.hT (A.fvec c) yB = - S.hT (A.fvec c) yA := by
    intro c
    have := h c
    rw [map_add] at this
    exact eq_neg_of_add_eq_zero_right this
  have hcB : ∀ i : Fin r, S.hT (A.e i) (∑ b, κ (Sum.inr b) • B.fvec b) = 0 := by
    intro i
    rw [← hyB, ← fvec_cs, hB, hA]
    simp [Fin.castSucc_ne_last]
  have hyB' := comb_eq A B hdet hΩ (fun b => κ (Sum.inr b)) hcB
  rw [← hyB] at hyB'
  have hzB : S.hT A.z yB = TA * κ (Sum.inl (Fin.last r)) := by
    rw [← fvec_last, hB, hA]; simp
  refine ⟨∑ i : Fin r, κ (Sum.inl i.castSucc) • A.e i, ?_, κ (Sum.inl (Fin.last r)), ?_⟩
  · exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [hyB', hzB, hyA, Fin.sum_univ_castSucc]
    simp only [fvec_cs, fvec_last]
    rw [smul_add, smul_smul, mul_comm]
    abel

/- English proof (translation)
Use `set c : Fin (r + 1) → E := (Zhat A B)⁻¹ *ᵥ Pi.single (Fin.last r) 1 with hc`. Establish `hv : OmV A B (∑ b, c b • B.fvec b)`. Use `⟨(Submodule.mem_span_range_iff_exists_fun E).2 ⟨c, rfl⟩, fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[hT_comb, hc, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet), Matrix.one_mulVec]`. Distinguish the cases in `ha : a = Fin.last r`.

Substitute `ha` using the available equality. Simplify using the standard rewrite rules. Simplify using `[ha]`. Rewrite using `[om_unique A B hdet hΩ hv, Fin.sum_univ_castSucc]`. Establish `hcl : c (Fin.last r) = (Zhat A B)⁻¹ (Fin.last r) (Fin.last r)`.

Rewrite using `[hc, Matrix.mulVec_single_one]`. Both sides reduce to the same expression. Simplify using `only [fvec_cs, fvec_last, hcl, add_sub_cancel_right]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`.
-/
theorem om_zcoef {TA TB : E} (A : FlagG S r TA) (B : FlagG S r TB) (hdet : (Zhat A B).det ≠ 0) {Ω : S.V}
    (hΩ : OmV A B Ω) : Ω - (Zhat A B)⁻¹ (Fin.last r) (Fin.last r) • B.z ∈ B.X := by
  set c : Fin (r + 1) → E := (Zhat A B)⁻¹ *ᵥ Pi.single (Fin.last r) 1 with hc
  have hv : OmV A B (∑ b, c b • B.fvec b) := by
    refine ⟨(Submodule.mem_span_range_iff_exists_fun E).2 ⟨c, rfl⟩, fun a => ?_⟩
    rw [hT_comb, hc, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet),
      Matrix.one_mulVec]
    by_cases ha : a = Fin.last r
    · subst ha; simp
    · simp [ha]
  rw [om_unique A B hdet hΩ hv, Fin.sum_univ_castSucc]
  have hcl : c (Fin.last r) = (Zhat A B)⁻¹ (Fin.last r) (Fin.last r) := by
    rw [hc, Matrix.mulVec_single_one]; rfl
  simp only [fvec_cs, fvec_last, hcl, add_sub_cancel_right]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/- English proof (translation)
Take `⟨x, hx, x', hx', hxx⟩` from `Submodule.mem_sup.1 h`. Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun E).1 hx`. Take `⟨d, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun E).1 hx'`. Set `κ : Fin (r + 1) ⊕ Fin (r + 1) → E` to `Sum.elim (Fin.snoc (α := fun _ => E) (fun i => c i) (-l)) (Fin.snoc (α := fun _ => E) (fun i => d i) (-m))`. Establish `h0 : ∑ s, κ s • Sum.elim A.fvec B.fvec s = 0`.

Rewrite using `[Fintype.sum_sum_type, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]`. Simplify using `only [κ, Sum.elim_inl, Sum.elim_inr, Fin.snoc_castSucc, Fin.snoc_last, fvec_cs, fvec_last, neg_smul]`. Rewrite `hxx` using `[← sub_eq_zero]`. Rewrite using `[← hxx]`. Normalize the expressions using the abelian group laws.

Establish `hl` using `Fintype.linearIndependent_iff.1 hli κ h0 (Sum.inl (Fin.last r))`. Establish `hm` using `Fintype.linearIndependent_iff.1 hli κ h0 (Sum.inr (Fin.last r))`. Simplify using `only [κ, Sum.elim_inl, Sum.elim_inr, Fin.snoc_last, neg_eq_zero] at hl hm`. Conclude with `⟨hl, hm⟩`.
-/
theorem indep2 {TA TB : E} (A : FlagG S r TA) (B : FlagG S r TB)
    (hli : LinearIndependent E (Sum.elim A.fvec B.fvec)) {l m : E} (h : l • A.z + m • B.z ∈ A.X ⊔ B.X) :
    l = 0 ∧ m = 0 := by
  obtain ⟨x, hx, x', hx', hxx⟩ := Submodule.mem_sup.1 h
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hx
  obtain ⟨d, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hx'
  let κ : Fin (r + 1) ⊕ Fin (r + 1) → E :=
    Sum.elim (Fin.snoc (α := fun _ => E) (fun i => c i) (-l)) (Fin.snoc (α := fun _ => E) (fun i => d i) (-m))
  have h0 : ∑ s, κ s • Sum.elim A.fvec B.fvec s = 0 := by
    rw [Fintype.sum_sum_type, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    simp only [κ, Sum.elim_inl, Sum.elim_inr, Fin.snoc_castSucc, Fin.snoc_last, fvec_cs, fvec_last, neg_smul]
    rw [← sub_eq_zero] at hxx
    rw [← hxx]
    abel
  have hl := Fintype.linearIndependent_iff.1 hli κ h0 (Sum.inl (Fin.last r))
  have hm := Fintype.linearIndependent_iff.1 hli κ h0 (Sum.inr (Fin.last r))
  simp only [κ, Sum.elim_inl, Sum.elim_inr, Fin.snoc_last, neg_eq_zero] at hl hm
  exact ⟨hl, hm⟩

end Gen

section Gen2

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

/- English proof (translation)
Use `set ω' := Ω - ρ • F'.fl.z with hω'`. Use `set ω := Ω' - σ • F.fl.z with hω`. Establish `eΩ : Ω = ρ • F'.fl.z + ω'` using `by rw [hω']; abel`. Establish `eΩ' : Ω' = σ • F.fl.z + ω` using `by rw [hω]; abel`. Simplify using `only [SgRel, hz, hz', Xsp]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨ξ, hξ, ξ', hξ', he⟩`. Establish `key : (a - a' * T' * σ - α) • F.fl.z + (a * T * ρ - a' - α') • F'.fl.z = (ξ - (x - (a' * T') • ω)) + (ξ' - ((a * T) • ω' - x'))`. Rewrite `he` using `[eΩ, eΩ']`. Take the linear combination `(norm := module) he`.

Establish `hmem : (a - a' * T' * σ - α) • F.fl.z + (a * T * ρ - a' - α') • F'.fl.z ∈ F.fl.X ⊔ F'.fl.X`. Rewrite using `[key]`. Use `Submodule.add_mem_sup (Submodule.sub_mem _ hξ (Submodule.sub_mem _ hx (Submodule.smul_mem _ _ hΩ'))) (Submodule.sub_mem _ hξ' (Submodule.sub_mem _ (Submodule.smul_mem _ _ hΩ) hx'))` and prove the remaining obligations. Take `⟨h1, h2⟩` from `indep2 F.fl F'.fl hli hmem`. Conclude with `⟨by linear_combination -h1, by linear_combination -h2⟩`.

Introduce and unpack `⟨rfl, rfl⟩`. Use `⟨x - (a' * T') • ω, Submodule.sub_mem _ hx (Submodule.smul_mem _ _ hΩ'), (a * T) • ω' - x', Submodule.sub_mem _ (Submodule.smul_mem _ _ hΩ) hx', ?_⟩` and prove the remaining obligations. Rewrite using `[eΩ, eΩ']`. Use `module`.
-/
theorem sgRel_iff {T T' : E} (F : LFlag S r T) (F' : LFlag S r T') (hz : F.zt = F.fl.z) (hz' : F'.zt = F'.fl.z)
    (hli : LinearIndependent E (Sum.elim F.fl.fvec F'.fl.fvec)) {Ω Ω' : S.V} {ρ σ : E}
    (hΩ : Ω - ρ • F'.fl.z ∈ F'.fl.X) (hΩ' : Ω' - σ • F.fl.z ∈ F.fl.X) {x x' : S.V} (hx : x ∈ F.fl.X)
    (hx' : x' ∈ F'.fl.X) (a a' α α' : E) :
    SgRel F F' (x + a • (F.fl.z + T • Ω)) (x' + a' • (F'.fl.z + T' • Ω')) α α' ↔
      α = a - a' * T' * σ ∧ α' = a * T * ρ - a' := by
  set ω' := Ω - ρ • F'.fl.z with hω'
  set ω := Ω' - σ • F.fl.z with hω
  have eΩ : Ω = ρ • F'.fl.z + ω' := by rw [hω']; abel
  have eΩ' : Ω' = σ • F.fl.z + ω := by rw [hω]; abel
  simp only [SgRel, hz, hz', Xsp]
  constructor
  · rintro ⟨ξ, hξ, ξ', hξ', he⟩
    have key : (a - a' * T' * σ - α) • F.fl.z + (a * T * ρ - a' - α') • F'.fl.z =
        (ξ - (x - (a' * T') • ω)) + (ξ' - ((a * T) • ω' - x')) := by
      rw [eΩ, eΩ'] at he
      linear_combination (norm := module) he
    have hmem : (a - a' * T' * σ - α) • F.fl.z + (a * T * ρ - a' - α') • F'.fl.z ∈ F.fl.X ⊔ F'.fl.X := by
      rw [key]
      refine Submodule.add_mem_sup (Submodule.sub_mem _ hξ (Submodule.sub_mem _ hx (Submodule.smul_mem _ _ hΩ')))
        (Submodule.sub_mem _ hξ' (Submodule.sub_mem _ (Submodule.smul_mem _ _ hΩ) hx'))
    obtain ⟨h1, h2⟩ := indep2 F.fl F'.fl hli hmem
    exact ⟨by linear_combination -h1, by linear_combination -h2⟩
  · rintro ⟨rfl, rfl⟩
    refine ⟨x - (a' * T') • ω, Submodule.sub_mem _ hx (Submodule.smul_mem _ _ hΩ'),
      (a * T) • ω' - x', Submodule.sub_mem _ (Submodule.smul_mem _ _ hΩ) hx', ?_⟩
    rw [eΩ, eΩ']
    module

end Gen2

section Gen3

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

/- English proof (translation)
Rewrite using `[Matrix.inv_def, Matrix.smul_apply, PI.UnitaryGroupMassFormula.BetaLUniq.GN.adj_last, smul_eq_mul, Ring.inverse_eq_inv', leadMinorE, dif_pos (Nat.le_succ r)]`. Establish `ecs : (Fin.castLE (Nat.le_succ r) : Fin r → Fin (r + 1)) = Fin.castSucc` using `funext fun i => Fin.ext rfl`. Rewrite using `[ecs, div_eq_inv_mul]`.
-/
theorem inv_last (A : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    A⁻¹ (Fin.last r) (Fin.last r) = leadMinorE A r / A.det := by
  rw [Matrix.inv_def, Matrix.smul_apply, PI.UnitaryGroupMassFormula.BetaLUniq.GN.adj_last, smul_eq_mul, Ring.inverse_eq_inv',
    leadMinorE, dif_pos (Nat.le_succ r)]
  have ecs : (Fin.castLE (Nat.le_succ r) : Fin r → Fin (r + 1)) = Fin.castSucc := funext fun i => Fin.ext rfl
  rw [ecs, div_eq_inv_mul]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Zhat, Matrix.conjTranspose_apply, brS]`. Conclude with `PI.PairCorankPos.W.hT_swap S (A.fvec j) (B.fvec i)`.
-/
theorem Zhat_swap {TA TB : E} (A : FlagG S r TA) (B : FlagG S r TB) : Zhat B A = (Zhat A B)ᴴ := by
  ext i j
  simp only [Zhat, Matrix.conjTranspose_apply, brS]
  exact PI.PairCorankPos.W.hT_swap S (A.fvec j) (B.fvec i)

/- English proof (translation)
Establish `e : Sum.elim B.fvec A.fvec = Sum.elim A.fvec B.fvec ∘ Sum.swap`. Apply the tactic sequence `funext s; rcases s with i | i <;> rfl`. Rewrite using `[e]`. Conclude with `h.comp _ (Function.LeftInverse.injective (f := Sum.swap) (g := Sum.swap) Sum.swap_swap)`.
-/
theorem linIndep_swap {TA TB : E} (A : FlagG S r TA) (B : FlagG S r TB)
    (h : LinearIndependent E (Sum.elim A.fvec B.fvec)) : LinearIndependent E (Sum.elim B.fvec A.fvec) := by
  have e : Sum.elim B.fvec A.fvec = Sum.elim A.fvec B.fvec ∘ Sum.swap := by
    funext s; rcases s with i | i <;> rfl
  rw [e]
  exact h.comp _ (Function.LeftInverse.injective (f := Sum.swap) (g := Sum.swap) Sum.swap_swap)

/- English proof (translation)
Use `congr 1`. Use extensionality with `v`. Simplify using `only [Set.mem_range, Sum.exists, Sum.elim_inl, Sum.elim_inr]`. The claim follows by propositional logic.
-/
theorem span_swap {ι κ : Type*} (a : ι → S.V) (b : κ → S.V) :
    Submodule.span E (Set.range (Sum.elim a b)) = Submodule.span E (Set.range (Sum.elim b a)) := by
  congr 1
  ext v
  simp only [Set.mem_range, Sum.exists, Sum.elim_inl, Sum.elim_inr]
  tauto

/- English proof (translation)
Use `Fin.lastCases ?_ (fun i => ?_) a` and prove the remaining obligations. Rewrite using `[fvec_last]`. Conclude with `Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)`. Rewrite using `[fvec_cs]`. Conclude with `Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩)`.
-/
theorem fvec_mem_Xplus {T : E} (A : FlagG S r T) (a : Fin (r + 1)) : A.fvec a ∈ A.Xplus := by
  refine Fin.lastCases ?_ (fun i => ?_) a
  · rw [fvec_last]; exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  · rw [fvec_cs]; exact Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩)

/- English proof (translation)
Establish `key : (a - b) • A.z + ((a - b) * TA * ρ) • B₂.z = ((x₁ + a • (A.z + TA • Ω₁)) - (x₂ + b • (A.z + TA • Ω₂)) - (x₁ - x₂) + (a * TA) • (Ω₂ - Ω₁)) - ((a - b) * TA) • (Ω₂ - ρ • B₂.z)` using `by module`. Establish `hmem : (a - b) • A.z + ((a - b) * TA * ρ) • B₂.z ∈ A.X ⊔ B₂.X`. Rewrite using `[key]`. Conclude with `Submodule.sub_mem _ (Submodule.mem_sup_left (Submodule.add_mem _ (Submodule.sub_mem _ h12 (Submodule.sub_mem _ hx₁ hx₂)) (Submodule.smul_mem _ _ hloc))) (Submodule.mem_sup_right (Submodule.smul_mem _ _ hω₂))`. Conclude with `sub_eq_zero.1 (indep2 A B₂ hli hmem).1`.
-/
theorem ab_of {TA T' : E} (A : FlagG S r TA) (B₂ : FlagG S r T') {x₁ x₂ Ω₁ Ω₂ : S.V} {a b ρ : E}
    (hx₁ : x₁ ∈ A.X) (hx₂ : x₂ ∈ A.X) (hω₂ : Ω₂ - ρ • B₂.z ∈ B₂.X) (hloc : Ω₂ - Ω₁ ∈ A.X)
    (h12 : (x₁ + a • (A.z + TA • Ω₁)) - (x₂ + b • (A.z + TA • Ω₂)) ∈ A.X)
    (hli : LinearIndependent E (Sum.elim A.fvec B₂.fvec)) : a = b := by
  have key : (a - b) • A.z + ((a - b) * TA * ρ) • B₂.z =
      ((x₁ + a • (A.z + TA • Ω₁)) - (x₂ + b • (A.z + TA • Ω₂)) - (x₁ - x₂) + (a * TA) • (Ω₂ - Ω₁)) -
        ((a - b) * TA) • (Ω₂ - ρ • B₂.z) := by
    module
  have hmem : (a - b) • A.z + ((a - b) * TA * ρ) • B₂.z ∈ A.X ⊔ B₂.X := by
    rw [key]
    exact Submodule.sub_mem _ (Submodule.mem_sup_left (Submodule.add_mem _ (Submodule.sub_mem _ h12
      (Submodule.sub_mem _ hx₁ hx₂)) (Submodule.smul_mem _ _ hloc)))
      (Submodule.mem_sup_right (Submodule.smul_mem _ _ hω₂))
  exact sub_eq_zero.1 (indep2 A B₂ hli hmem).1

/- English proof (translation)
Establish `e : β (x₁' + a' • (B₁.z + T' • Ω'₁)) = β x₁' + a' • (B₂.z + T' • β Ω'₁)`. Rewrite using `[map_add, map_smul, map_add, map_smul, hβz]`. Rewrite `h2` using `[e]`. Establish `key : (b' - a') • B₂.z + ((b' - a') * T' * σ) • A.z = ((x₂'' + b' • (B₂.z + T' • Ω'₂)) - (β x₁' + a' • (B₂.z + T' • β Ω'₁)) - (x₂'' - β x₁') + (a' * T') • (β Ω'₁ - Ω'₂)) - ((b' - a') * T') • (Ω'₂ - σ • A.z)` using `by module`. Establish `hmem : (b' - a') • B₂.z + ((b' - a') * T' * σ) • A.z ∈ B₂.X ⊔ A.X`.

Rewrite using `[key]`. Conclude with `Submodule.sub_mem _ (Submodule.mem_sup_left (Submodule.add_mem _ (Submodule.sub_mem _ h2 (Submodule.sub_mem _ hx₂ hβx)) (Submodule.smul_mem _ _ hβΩ))) (Submodule.mem_sup_right (Submodule.smul_mem _ _ hω))`. Conclude with `(sub_eq_zero.1 (indep2 B₂ A hli hmem).1).symm`.
-/
theorem ab'_of {TA T' : E} (A : FlagG S r TA) (B₁ B₂ : FlagG S r T') (β : S.V ≃ₗ[E] S.V)
    {x₁' x₂'' Ω'₁ Ω'₂ : S.V} {a' b' σ : E} (hβx : β x₁' ∈ B₂.X) (hx₂ : x₂'' ∈ B₂.X) (hβz : β B₁.z = B₂.z)
    (hω : Ω'₂ - σ • A.z ∈ A.X) (hβΩ : β Ω'₁ - Ω'₂ ∈ B₂.X)
    (h2 : (x₂'' + b' • (B₂.z + T' • Ω'₂)) - β (x₁' + a' • (B₁.z + T' • Ω'₁)) ∈ B₂.X)
    (hli : LinearIndependent E (Sum.elim B₂.fvec A.fvec)) : a' = b' := by
  have e : β (x₁' + a' • (B₁.z + T' • Ω'₁)) = β x₁' + a' • (B₂.z + T' • β Ω'₁) := by
    rw [map_add, map_smul, map_add, map_smul, hβz]
  rw [e] at h2
  have key : (b' - a') • B₂.z + ((b' - a') * T' * σ) • A.z =
      ((x₂'' + b' • (B₂.z + T' • Ω'₂)) - (β x₁' + a' • (B₂.z + T' • β Ω'₁)) - (x₂'' - β x₁') +
        (a' * T') • (β Ω'₁ - Ω'₂)) - ((b' - a') * T') • (Ω'₂ - σ • A.z) := by
    module
  have hmem : (b' - a') • B₂.z + ((b' - a') * T' * σ) • A.z ∈ B₂.X ⊔ A.X := by
    rw [key]
    exact Submodule.sub_mem _ (Submodule.mem_sup_left (Submodule.add_mem _ (Submodule.sub_mem _ h2
      (Submodule.sub_mem _ hx₂ hβx)) (Submodule.smul_mem _ _ hβΩ)))
      (Submodule.mem_sup_right (Submodule.smul_mem _ _ hω))
  exact (sub_eq_zero.1 (indep2 B₂ A hli hmem).1).symm

/- English proof (translation)
Establish `hmul : (d₁ * d₂) • (β Ω'₁ - Ω'₂) = d₂ • β G₁ - d₁ • G₂`. Rewrite using `[e1, e2, map_smul, smul_sub, smul_smul, smul_smul]`. Use `congr 2`. Clear the denominators using the available nonvanishing facts. Clear the denominators using the available nonvanishing facts.

Conclude with `(Submodule.smul_mem_iff _ (mul_ne_zero hd₁ hd₂)).1 (hmul ▸ hO)`.
-/
theorem omB_conv (β : S.V ≃ₗ[E] S.V) {X : Submodule E S.V} {G₁ G₂ Ω'₁ Ω'₂ : S.V} {d₁ d₂ : E} (hd₁ : d₁ ≠ 0)
    (hd₂ : d₂ ≠ 0) (e1 : Ω'₁ = d₁⁻¹ • G₁) (e2 : Ω'₂ = d₂⁻¹ • G₂) (hO : d₂ • β G₁ - d₁ • G₂ ∈ X) :
    β Ω'₁ - Ω'₂ ∈ X := by
  have hmul : (d₁ * d₂) • (β Ω'₁ - Ω'₂) = d₂ • β G₁ - d₁ • G₂ := by
    rw [e1, e2, map_smul, smul_sub, smul_smul, smul_smul]
    congr 2
    · field_simp
    · field_simp
  exact (Submodule.smul_mem_iff _ (mul_ne_zero hd₁ hd₂)).1 (hmul ▸ hO)

end Gen3

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdBetaS

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

open BwdCut BwdBetaCut BwdBetaS OmP Formalism.L2.SG.Pf.ScalarFramePf Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.TermDef

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

namespace BwdBetaS

/- English proof (translation)
Use `set W := Submodule.span D.host.E (Set.range (Sum.elim F.fl.fvec F'.fl.fvec))`. Establish `hz1 : F.zt ∈ W`. Rewrite using `[hz]`. Conclude with `span_left_le F F' (Submodule.subset_span ⟨Fin.last _, fvec_last _⟩)`. Establish `hz2 : F'.zt ∈ W`.

Rewrite using `[hz']`. Conclude with `span_right_le F F' (Submodule.subset_span ⟨Fin.last _, fvec_last _⟩)`. Establish `hUU : UU Λ F F' ≤ W.restrictScalars (𝓞 D.host.E)`. Unfold `UU`. Use `sup_le (sup_le (sup_le ?_ ?_) ?_) ?_` and prove the remaining obligations.

Introduce `v hv`. Conclude with `span_left_le F F' (Xsp_le_span F (Submodule.mem_inf.1 hv).2)`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ rfl`. Conclude with `hz1`.

Introduce `v hv`. Conclude with `span_right_le F F' (Xsp_le_span F' (Submodule.mem_inf.1 hv).2)`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ rfl`. Conclude with `hz2`.

Conclude with `Submodule.span_le.2 fun v hv => hUU hv`.
-/
theorem UUE_le_span (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T)
    (F' : LFlag (VS D) D.R.rS T') (hz : F.zt = F.fl.z) (hz' : F'.zt = F'.fl.z) :
    UUE Λ F F' ≤ Submodule.span D.host.E (Set.range (Sum.elim F.fl.fvec F'.fl.fvec)) := by
  set W := Submodule.span D.host.E (Set.range (Sum.elim F.fl.fvec F'.fl.fvec))
  have hz1 : F.zt ∈ W := by
    rw [hz]; exact span_left_le F F' (Submodule.subset_span ⟨Fin.last _, fvec_last _⟩)
  have hz2 : F'.zt ∈ W := by
    rw [hz']; exact span_right_le F F' (Submodule.subset_span ⟨Fin.last _, fvec_last _⟩)
  have hUU : UU Λ F F' ≤ W.restrictScalars (𝓞 D.host.E) := by
    unfold UU
    refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
    · intro v hv; exact span_left_le F F' (Xsp_le_span F (Submodule.mem_inf.1 hv).2)
    · rw [Submodule.span_le]; rintro _ rfl; exact hz1
    · intro v hv; exact span_right_le F F' (Xsp_le_span F' (Submodule.mem_inf.1 hv).2)
    · rw [Submodule.span_le]; rintro _ rfl; exact hz2
  exact Submodule.span_le.2 fun v hv => hUU hv

/- English proof (translation)
Take `⟨hy1, hy2⟩` from `Submodule.mem_inf.1 hy`. Use `dec F.fl F'.fl hdet hΩ (UUE_le_span Λ F F' hz hz' hy1) fun a => ?_` and prove the remaining obligations. Rewrite `hy2` using `[Formalism.L2.SG.Pf.mem_orth_iff_sat 1 (Subgroup.one_mem _)]`. Conclude with `hy2 _ (fvec_mem_Xplus F.fl a)`.
-/
theorem ylift_dec (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T)
    (F' : LFlag (VS D) D.R.rS T') (hz : F.zt = F.fl.z) (hz' : F'.zt = F'.fl.z) (hdet : (Zhat F.fl F'.fl).det ≠ 0)
    {Ω : (VS D).V} (hΩ : OmV F.fl F'.fl Ω) {y : (VS D).V} (hy : y ∈ Ylift Λ F F') :
    ∃ x ∈ F.fl.X, ∃ c : D.host.E, y = x + c • (F.fl.z + T • Ω) := by
  obtain ⟨hy1, hy2⟩ := Submodule.mem_inf.1 hy
  refine dec F.fl F'.fl hdet hΩ (UUE_le_span Λ F F' hz hz' hy1) fun a => ?_
  rw [Formalism.L2.SG.Pf.mem_orth_iff_sat 1 (Subgroup.one_mem _)] at hy2
  exact hy2 _ (fvec_mem_Xplus F.fl a)

/- English proof (translation)
Take `⟨hy1, hy2⟩` from `Submodule.mem_inf.1 hy`. Establish `hs` using `UUE_le_span Λ F F' hz hz' hy1`. Rewrite `hs` using `[span_swap]`. Use `dec F'.fl F.fl hdet hΩ hs fun a => ?_` and prove the remaining obligations. Rewrite `hy2` using `[Formalism.L2.SG.Pf.mem_orth_iff_sat 1 (Subgroup.one_mem _)]`.

Conclude with `hy2 _ (fvec_mem_Xplus F'.fl a)`.
-/
theorem ylift'_dec (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T)
    (F' : LFlag (VS D) D.R.rS T') (hz : F.zt = F.fl.z) (hz' : F'.zt = F'.fl.z) (hdet : (Zhat F'.fl F.fl).det ≠ 0)
    {Ω : (VS D).V} (hΩ : OmV F'.fl F.fl Ω) {y : (VS D).V} (hy : y ∈ Ylift' Λ F F') :
    ∃ x ∈ F'.fl.X, ∃ c : D.host.E, y = x + c • (F'.fl.z + T' • Ω) := by
  obtain ⟨hy1, hy2⟩ := Submodule.mem_inf.1 hy
  have hs := UUE_le_span Λ F F' hz hz' hy1
  rw [span_swap] at hs
  refine dec F'.fl F.fl hdet hΩ hs fun a => ?_
  rw [Formalism.L2.SG.Pf.mem_orth_iff_sat 1 (Subgroup.one_mem _)] at hy2
  exact hy2 _ (fvec_mem_Xplus F'.fl a)

end BwdBetaS

namespace BwdBetaS

/- English proof (translation)
Establish `hD : GDl (frame (lf D F0)) (frame F') (D.R.rS + 1) = (Zhat F0 F'.fl).det`. Rewrite using `[GDl_top']`. Both sides reduce to the same expression. Establish `hD0 : star (GDl (frame (lf D F0)) (frame F') (D.R.rS + 1)) ≠ 0`. Rewrite using `[hD]`.

Conclude with `star_ne_zero.2 hdet`. Establish `hdet' : (Zhat F'.fl F0).det ≠ 0`. Rewrite using `[Zhat_swap, Matrix.det_conjTranspose]`. Conclude with `star_ne_zero.2 hdet`. Use `om_unique F'.fl F0 hdet' hΩ' ⟨Submodule.smul_mem _ _ (Gom_mem _ _), fun b => ?_⟩` and prove the remaining obligations.

Rewrite using `[map_smul, smul_eq_mul, PI.PairCorankPos.W.hT_swap (VS D) (Gom (frame (lf D F0)) (frame F')) (F'.fl.fvec b)]`. Use `om_pair (D := D) (frame (lf D F0)) (frame F') b` as an intermediate fact. Rewrite using `[show F'.fl.fvec b = frame F' b from rfl, this]`. Use `split_ifs with hb`. Conclude with `inv_mul_cancel₀ hD0`.

Simplify using the standard rewrite rules.
-/
theorem om'_eq {T' : D.host.E} (F' : LFlag (VS D) D.R.rS T')
    (hdet : (Zhat F0 F'.fl).det ≠ 0) {Ω' : (VS D).V} (hΩ' : OmV F'.fl F0 Ω') :
    Ω' = (star (GDl (frame (lf D F0)) (frame F') (D.R.rS + 1)))⁻¹ • Gom (frame (lf D F0)) (frame F') := by
  have hD : GDl (frame (lf D F0)) (frame F') (D.R.rS + 1) = (Zhat F0 F'.fl).det := by
    rw [GDl_top']; rfl
  have hD0 : star (GDl (frame (lf D F0)) (frame F') (D.R.rS + 1)) ≠ 0 := by
    rw [hD]; exact star_ne_zero.2 hdet
  have hdet' : (Zhat F'.fl F0).det ≠ 0 := by
    rw [Zhat_swap, Matrix.det_conjTranspose]; exact star_ne_zero.2 hdet
  refine om_unique F'.fl F0 hdet' hΩ' ⟨Submodule.smul_mem _ _ (Gom_mem _ _), fun b => ?_⟩
  rw [map_smul, smul_eq_mul, PI.PairCorankPos.W.hT_swap (VS D) (Gom (frame (lf D F0)) (frame F')) (F'.fl.fvec b)]
  have := om_pair (D := D) (frame (lf D F0)) (frame F') b
  rw [show F'.fl.fvec b = frame F' b from rfl, this]
  split_ifs with hb
  · exact inv_mul_cancel₀ hD0
  · simp

end BwdBetaS

/- English proof (translation)
Introduce `γ Z F'₂ φ φ' Λ₂ hB β hβ hfr hO`. Take `⟨hC, hZ, hS, hΛ₂, -, hT, hPD, hG⟩` from `hB`. Take `⟨hZd, hZ₁d, hx⟩` from `starMinors_holds u u' F0 what₂ γ Z hZ`. Establish `eA₂ : Zhat F0 F'₂.fl = Z` using `hS.1`. Establish `hl1` using `star_frame_lead_minor γ (D.R.rS + 1)`.

Establish `hlr` using `star_frame_lead_minor γ D.R.rS`. Rewrite `hl1` using `[FsLA.leadMinorE_full, FsLA.leadMinorE_full]`. Establish `hdet1 : (Zhat F0 (repF γ).fl).det ≠ 0` using `fun h0 => hZ₁d (hl1.trans h0)`. Establish `hdet2 : (Zhat F0 F'₂.fl).det ≠ 0` using `by rw [eA₂]; exact hZd`. Establish `hρ : (Zhat F0 (repF γ).fl)⁻¹ (Fin.last _) (Fin.last _) = (Zhat F0 F'₂.fl)⁻¹ (Fin.last _) (Fin.last _)`.

Rewrite using `[inv_last, inv_last, div_eq_div_iff hdet1 hdet2, eA₂]`. Establish `e1 : leadMinorE (Zhat F0 (repF γ).fl) D.R.rS = leadMinorE (starZh (frame (lf D F0)) (starFrame γ)) D.R.rS` using `hlr.symm`. Rewrite using `[e1, ← hl1]`. Conclude with `hx`. Establish `hdet1' : (Zhat (repF γ).fl F0).det ≠ 0`.

Rewrite using `[Zhat_swap, Matrix.det_conjTranspose]`. Conclude with `star_ne_zero.2 hdet1`. Establish `hdet2' : (Zhat F'₂.fl F0).det ≠ 0`. Rewrite using `[Zhat_swap, Matrix.det_conjTranspose]`. Conclude with `star_ne_zero.2 hdet2`.

Establish `hσ : (Zhat (repF γ).fl F0)⁻¹ (Fin.last _) (Fin.last _) = (Zhat F'₂.fl F0)⁻¹ (Fin.last _) (Fin.last _)`. Rewrite using `[Zhat_swap F0 (repF γ).fl, Zhat_swap F0 F'₂.fl, ← Matrix.conjTranspose_nonsing_inv, ← Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_apply, Matrix.conjTranspose_apply, hρ]`. Take `⟨Ω₁, hΩ₁⟩` from `exists_om F0 (repF γ).fl hdet1`. Take `⟨Ω₂, hΩ₂⟩` from `exists_om F0 F'₂.fl hdet2`. Take `⟨Ω'₁, hΩ'₁⟩` from `exists_om (repF γ).fl F0 hdet1'`.

Take `⟨Ω'₂, hΩ'₂⟩` from `exists_om F'₂.fl F0 hdet2'`. Establish `hloc : Ω₂ - Ω₁ ∈ Xsp (lf D F0)` using `omega_local_holds Zd u u' F0 what₂ hC.2.1 γ Z hZ F'₂ φ φ' hS hdet1 hZd Ω₂ Ω₁ hΩ₂ hΩ₁`. Establish `hD1 : GDl (frame (lf D F0)) (frame (repF γ)) (D.R.rS + 1) = (Zhat F0 (repF γ).fl).det`. Rewrite using `[GDl_top']`. Both sides reduce to the same expression.

Establish `hD2 : GDl (frame (lf D F0)) (frame (liftF F'₂)) (D.R.rS + 1) = (Zhat F0 F'₂.fl).det`. Rewrite using `[GDl_top']`. Both sides reduce to the same expression. Establish `hβΩ : β Ω'₁ - Ω'₂ ∈ Xsp (liftF F'₂)` using `omB_conv β (by rw [hD1]; exact star_ne_zero.2 hdet1) (by rw [hD2]; exact star_ne_zero.2 hdet2) (BwdBetaS.om'_eq (F0 := F0) (repF γ) hdet1 hΩ'₁) (BwdBetaS.om'_eq (F0 := F0) (liftF F'₂) hdet2 hΩ'₂) hO`. Establish `hli1 : LinearIndependent D.host.E (Sum.elim F0.fvec (repF γ).fl.fvec)` using `PI.PairCorankPos.W.linIndep F0 (repF γ).fl hG`.

Establish `hli2 : LinearIndependent D.host.E (Sum.elim F0.fvec F'₂.fl.fvec)` using `PI.PairCorankPos.W.linIndep F0 F'₂.fl hT.1.2.2`. Establish `hzx : (repF γ).zt = (repF γ).fl.z` using `hPD.1.2`. Establish `hω₂` using `om_zcoef F0 F'₂.fl hdet2 hΩ₂`. Establish `hω'₂` using `om_zcoef F'₂.fl F0 hdet2' hΩ'₂`. Establish `hω₁` using `om_zcoef F0 (repF γ).fl hdet1 hΩ₁`.

Establish `hω'₁` using `om_zcoef (repF γ).fl F0 hdet1' hΩ'₁`. Rewrite `hω₁` using `[hρ]`. Rewrite `hω'₁` using `[hσ]`. Establish `hβz : β (repF γ).fl.z = F'₂.fl.z`. Use `hfr (Fin.last _)` as an intermediate fact.

Rewrite `this` using `[BwdBetaCut.fvec_last', BwdBetaCut.fvec_last']`. Then use the resulting hypothesis. Establish `hXβ` using `BwdBetaCut.Xsp_of_frame β (repF γ) (liftF F'₂) hfr`. Introduce `y1 hy1 y2 hy2 y1' hy1' y2'' hy2'' h12 h2'' α α'`. Take `⟨x₁, hx₁, a, rfl⟩` from `BwdBetaS.ylift_dec γ.lam (lf D F0) (repF γ) rfl hzx hdet1 hΩ₁ hy1`. Take `⟨x₂, hx₂, b, rfl⟩` from `BwdBetaS.ylift_dec Λ₂ (lf D F0) (liftF F'₂) rfl rfl hdet2 hΩ₂ hy2`.

Take `⟨x₁', hx₁', a', rfl⟩` from `BwdBetaS.ylift'_dec γ.lam (lf D F0) (repF γ) rfl hzx hdet1' hΩ'₁ hy1'`. Take `⟨x₂'', hx₂'', b', rfl⟩` from `BwdBetaS.ylift'_dec Λ₂ (lf D F0) (liftF F'₂) rfl rfl hdet2' hΩ'₂ hy2''`. Establish `hab : a = b` using `ab_of F0 F'₂.fl hx₁ hx₂ hω₂ hloc h12 hli2`. Establish `hβx : β x₁' ∈ F'₂.fl.X`. Establish `: β x₁' ∈ (Xsp (repF γ)).map (β : (VS D).V →ₗ[D.host.E] (VS D).V)` using `Submodule.mem_map_of_mem hx₁'`.

Rewrite `this` using `[hXβ]`. Conclude with `this`. Establish `hab' : a' = b'` using `ab'_of F0 (repF γ).fl F'₂.fl β hβx hx₂'' hβz hω'₂ hβΩ h2'' (BwdBetaS.linIndep_swap F0 F'₂.fl hli2)`. Substitute `hab` using the available equality. Substitute `hab'` using the available equality.

Rewrite using `[sgRel_iff (lf D F0) (repF γ) rfl hzx hli1 hω₁ hω'₁ hx₁ hx₁' a a' α α', sgRel_iff (lf D F0) (liftF F'₂) rfl rfl hli2 hω₂ hω'₂ hx₂ hx₂'' a a' α α']`.
-/
theorem scalarOf_holds : ScalarOf Zd u u' F0 what₂ := by
  intro γ Z F'₂ φ φ' Λ₂ hB β hβ hfr hO
  obtain ⟨hC, hZ, hS, hΛ₂, -, hT, hPD, hG⟩ := hB
  obtain ⟨hZd, hZ₁d, hx⟩ := starMinors_holds u u' F0 what₂ γ Z hZ
  have eA₂ : Zhat F0 F'₂.fl = Z := hS.1
  have hl1 := star_frame_lead_minor γ (D.R.rS + 1)
  have hlr := star_frame_lead_minor γ D.R.rS
  rw [FsLA.leadMinorE_full, FsLA.leadMinorE_full] at hl1
  have hdet1 : (Zhat F0 (repF γ).fl).det ≠ 0 := fun h0 => hZ₁d (hl1.trans h0)
  have hdet2 : (Zhat F0 F'₂.fl).det ≠ 0 := by rw [eA₂]; exact hZd
  have hρ : (Zhat F0 (repF γ).fl)⁻¹ (Fin.last _) (Fin.last _) = (Zhat F0 F'₂.fl)⁻¹ (Fin.last _) (Fin.last _) := by
    rw [inv_last, inv_last, div_eq_div_iff hdet1 hdet2, eA₂]
    have e1 : leadMinorE (Zhat F0 (repF γ).fl) D.R.rS = leadMinorE (starZh (frame (lf D F0)) (starFrame γ)) D.R.rS :=
      hlr.symm
    rw [e1, ← hl1]
    exact hx
  have hdet1' : (Zhat (repF γ).fl F0).det ≠ 0 := by
    rw [Zhat_swap, Matrix.det_conjTranspose]; exact star_ne_zero.2 hdet1
  have hdet2' : (Zhat F'₂.fl F0).det ≠ 0 := by
    rw [Zhat_swap, Matrix.det_conjTranspose]; exact star_ne_zero.2 hdet2
  have hσ : (Zhat (repF γ).fl F0)⁻¹ (Fin.last _) (Fin.last _) = (Zhat F'₂.fl F0)⁻¹ (Fin.last _) (Fin.last _) := by
    rw [Zhat_swap F0 (repF γ).fl, Zhat_swap F0 F'₂.fl, ← Matrix.conjTranspose_nonsing_inv,
      ← Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_apply, Matrix.conjTranspose_apply, hρ]
  obtain ⟨Ω₁, hΩ₁⟩ := exists_om F0 (repF γ).fl hdet1
  obtain ⟨Ω₂, hΩ₂⟩ := exists_om F0 F'₂.fl hdet2
  obtain ⟨Ω'₁, hΩ'₁⟩ := exists_om (repF γ).fl F0 hdet1'
  obtain ⟨Ω'₂, hΩ'₂⟩ := exists_om F'₂.fl F0 hdet2'
  have hloc : Ω₂ - Ω₁ ∈ Xsp (lf D F0) :=
    omega_local_holds Zd u u' F0 what₂ hC.2.1 γ Z hZ F'₂ φ φ' hS hdet1 hZd Ω₂ Ω₁ hΩ₂ hΩ₁
  have hD1 : GDl (frame (lf D F0)) (frame (repF γ)) (D.R.rS + 1) = (Zhat F0 (repF γ).fl).det := by
    rw [GDl_top']; rfl
  have hD2 : GDl (frame (lf D F0)) (frame (liftF F'₂)) (D.R.rS + 1) = (Zhat F0 F'₂.fl).det := by
    rw [GDl_top']; rfl
  have hβΩ : β Ω'₁ - Ω'₂ ∈ Xsp (liftF F'₂) :=
    omB_conv β (by rw [hD1]; exact star_ne_zero.2 hdet1) (by rw [hD2]; exact star_ne_zero.2 hdet2)
      (BwdBetaS.om'_eq (F0 := F0) (repF γ) hdet1 hΩ'₁) (BwdBetaS.om'_eq (F0 := F0) (liftF F'₂) hdet2 hΩ'₂) hO
  have hli1 : LinearIndependent D.host.E (Sum.elim F0.fvec (repF γ).fl.fvec) :=
    PI.PairCorankPos.W.linIndep F0 (repF γ).fl hG
  have hli2 : LinearIndependent D.host.E (Sum.elim F0.fvec F'₂.fl.fvec) :=
    PI.PairCorankPos.W.linIndep F0 F'₂.fl hT.1.2.2
  have hzx : (repF γ).zt = (repF γ).fl.z := hPD.1.2
  have hω₂ := om_zcoef F0 F'₂.fl hdet2 hΩ₂
  have hω'₂ := om_zcoef F'₂.fl F0 hdet2' hΩ'₂
  have hω₁ := om_zcoef F0 (repF γ).fl hdet1 hΩ₁
  have hω'₁ := om_zcoef (repF γ).fl F0 hdet1' hΩ'₁
  rw [hρ] at hω₁
  rw [hσ] at hω'₁
  have hβz : β (repF γ).fl.z = F'₂.fl.z := by
    have := hfr (Fin.last _)
    rwa [BwdBetaCut.fvec_last', BwdBetaCut.fvec_last'] at this
  have hXβ := BwdBetaCut.Xsp_of_frame β (repF γ) (liftF F'₂) hfr
  intro y1 hy1 y2 hy2 y1' hy1' y2'' hy2'' h12 h2'' α α'
  obtain ⟨x₁, hx₁, a, rfl⟩ := BwdBetaS.ylift_dec γ.lam (lf D F0) (repF γ) rfl hzx hdet1 hΩ₁ hy1
  obtain ⟨x₂, hx₂, b, rfl⟩ := BwdBetaS.ylift_dec Λ₂ (lf D F0) (liftF F'₂) rfl rfl hdet2 hΩ₂ hy2
  obtain ⟨x₁', hx₁', a', rfl⟩ := BwdBetaS.ylift'_dec γ.lam (lf D F0) (repF γ) rfl hzx hdet1' hΩ'₁ hy1'
  obtain ⟨x₂'', hx₂'', b', rfl⟩ := BwdBetaS.ylift'_dec Λ₂ (lf D F0) (liftF F'₂) rfl rfl hdet2' hΩ'₂ hy2''
  have hab : a = b := ab_of F0 F'₂.fl hx₁ hx₂ hω₂ hloc h12 hli2
  have hβx : β x₁' ∈ F'₂.fl.X := by
    have : β x₁' ∈ (Xsp (repF γ)).map (β : (VS D).V →ₗ[D.host.E] (VS D).V) := Submodule.mem_map_of_mem hx₁'
    rw [hXβ] at this; exact this
  have hab' : a' = b' :=
    ab'_of F0 (repF γ).fl F'₂.fl β hβx hx₂'' hβz hω'₂ hβΩ h2'' (BwdBetaS.linIndep_swap F0 F'₂.fl hli2)
  subst hab
  subst hab'
  rw [sgRel_iff (lf D F0) (repF γ) rfl hzx hli1 hω₁ hω'₁ hx₁ hx₁' a a' α α',
    sgRel_iff (lf D F0) (liftF F'₂) rfl rfl hli2 hω₂ hω'₂ hx₂ hx₂'' a a' α α']

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
