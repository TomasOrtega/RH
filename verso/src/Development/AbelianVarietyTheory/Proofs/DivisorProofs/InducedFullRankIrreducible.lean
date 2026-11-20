import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedScalarIrreducible

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitFlip
open scoped Matrix

namespace GlobalTheory.FullRankCoinv.IndTwist

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single (Fin.natAdd a i)]`. Simplify using `[Y0]`. Introduce `l _ hl`. Establish `: ¬ ((l : ℕ) = a + i)` using `fun h => hl (Fin.ext (by simp; omega))`. Simplify using `[Y0, this]`.

Simplify using the standard rewrite rules.
-/
theorem Y0_mul_apply {a n : ℕ} (M : Matrix (Fin (a + n)) (Fin (a + n)) k) (i : Fin n) (j : Fin (a + n)) :
    (Y0 k n (a + n) * M) i j = M (Fin.natAdd a i) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.natAdd a i)]
  · simp [Y0]
  · intro l _ hl
    have : ¬ ((l : ℕ) = a + i) := fun h => hl (Fin.ext (by simp; omega))
    simp [Y0, this]
  · simp

/- English proof (translation)
Use `split_ifs with h`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single (⟨j - a, by omega⟩ : Fin n)]`. Simplify using `[Y0]`. Use linear arithmetic over natural numbers and integers. Introduce `l _ hl`.

Establish `: ¬ ((j : ℕ) = a + l)` using `fun h' => hl (Fin.ext (by simp; omega))`. Simplify using `[Y0, this]`. Simplify using the standard rewrite rules. Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun l _ => ?_` and prove the remaining obligations.

Establish `: ¬ ((j : ℕ) = a + l)` using `by omega`. Simplify using `[Y0, this]`.
-/
theorem mul_Y0_apply {a n : ℕ} (D : Matrix (Fin n) (Fin n) k) (i : Fin n) (j : Fin (a + n)) :
    (D * Y0 k n (a + n)) i j = if h : a ≤ (j : ℕ) then D i ⟨j - a, by omega⟩ else 0 := by
  split_ifs with h
  · rw [Matrix.mul_apply, Finset.sum_eq_single (⟨j - a, by omega⟩ : Fin n)]
    · simp [Y0]; omega
    · intro l _ hl
      have : ¬ ((j : ℕ) = a + l) := fun h' => hl (Fin.ext (by simp; omega))
      simp [Y0, this]
    · simp
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    have : ¬ ((j : ℕ) = a + l) := by omega
    simp [Y0, this]

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Y0_mul_apply, mul_Y0_apply]`. Establish `hp` using `(mem_parab_two k).1 p.2`. Use `split_ifs with h`. Rewrite using `[leviProj_apply]`.

Establish `e1 : GlobalTheory.RankFibre.blocks a n ⟨true, i⟩ = Fin.natAdd a i` using `Fin.ext (by simp [stdSum])`. Establish `e2 : GlobalTheory.RankFibre.blocks a n ⟨true, (⟨j - a, by omega⟩ : Fin n)⟩ = j` using `Fin.ext (by simp [stdSum]; omega)`. Rewrite using `[e1, e2]`. Use `hp i ⟨j, by omega⟩` as an intermediate fact. Simplify `this` using `[stdSum]`.
-/
theorem Y0_mul_parab {a n : ℕ} (p : parab k (GlobalTheory.RankFibre.blocks a n)) :
    Y0 k n (a + n) * (p : GL (Fin (a + n)) k).1 =
      (leviProj k (GlobalTheory.RankFibre.blocks a n) p true : GL (Fin n) k).1 * Y0 k n (a + n) := by
  ext i j
  rw [Y0_mul_apply, mul_Y0_apply]
  have hp := (mem_parab_two k).1 p.2
  split_ifs with h
  · rw [leviProj_apply]
    have e1 : GlobalTheory.RankFibre.blocks a n ⟨true, i⟩ = Fin.natAdd a i := Fin.ext (by simp [stdSum])
    have e2 : GlobalTheory.RankFibre.blocks a n ⟨true, (⟨j - a, by omega⟩ : Fin n)⟩ = j := Fin.ext (by simp [stdSum]; omega)
    rw [e1, e2]
  · have := hp i ⟨j, by omega⟩
    simpa [stdSum] using this

end GlobalTheory.FullRankCoinv.IndTwist

namespace GlobalTheory.FullRankCoinv.IndTwist

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Use `set A := leviProj k (GlobalTheory.RankFibre.blocks a n) p false`. Use `set D := leviProj k (GlobalTheory.RankFibre.blocks a n) p true`. Establish `hδ : deltaHalf k (Two (Fin a) (Fin n)) (leviProj k (GlobalTheory.RankFibre.blocks a n) p) = absPow k ((n : ℂ) / 2) (gdet A) * absPow k (-(a : ℂ) / 2) (gdet D)`. Rewrite using `[← (leviTwo k (Fin a) (Fin n)).apply_symm_apply (leviProj k (GlobalTheory.RankFibre.blocks a n) p), deltaHalf_two]`. Simplify using `[A, D]`.

Both sides reduce to the same expression. Establish `hdet : gdet (p : GL (Fin (a + n)) k) = gdet A * gdet D`. Rewrite using `[gdet, det_parab, Fintype.prod_bool, mul_comm]`. Simplify using `only [GlobalTheory.RankFibre.parChar, MonoidHom.comp_apply, MonoidHom.mul_apply, Units.val_mul, hδ]`. Rewrite using `[hdet, apow_mul]`.

Establish `e : apow (gdet D) (-(a : ℂ) / 2) = apow (gdet D) ((n : ℂ) / 2) * apow (gdet D) (-((a + n : ℕ) : ℂ) / 2)`. Rewrite using `[← apow_add]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Use `show apow (gdet A) ((n : ℂ) / 2) * apow (gdet D) (-(a : ℂ) / 2) * (((ν * ν⁻¹) (gdet A) : ℂˣ) : ℂ) * ((ν⁻¹ (gdet D) : ℂˣ) : ℂ) = _`. Rewrite using `[e, mul_inv_cancel]`. Simplify using `only [MonoidHom.one_apply, Units.val_one, mul_one, MonoidHom.inv_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem parChar_eq {a n : ℕ} (ν : kˣ →* ℂˣ) (p : parab k (GlobalTheory.RankFibre.blocks a n)) :
    ((GlobalTheory.RankFibre.parChar ν ν⁻¹ a n p : ℂˣ) : ℂ) =
      apow (gdet (p : GL (Fin (a + n)) k)) ((n : ℂ) / 2) *
        ((((ν (gdet (leviProj k (GlobalTheory.RankFibre.blocks a n) p true)))⁻¹ : ℂˣ) : ℂ) *
          apow (gdet (leviProj k (GlobalTheory.RankFibre.blocks a n) p true)) (-((a + n : ℕ) : ℂ) / 2)) := by
  set A := leviProj k (GlobalTheory.RankFibre.blocks a n) p false
  set D := leviProj k (GlobalTheory.RankFibre.blocks a n) p true
  have hδ : deltaHalf k (Two (Fin a) (Fin n)) (leviProj k (GlobalTheory.RankFibre.blocks a n) p) =
      absPow k ((n : ℂ) / 2) (gdet A) * absPow k (-(a : ℂ) / 2) (gdet D) := by
    rw [← (leviTwo k (Fin a) (Fin n)).apply_symm_apply (leviProj k (GlobalTheory.RankFibre.blocks a n) p), deltaHalf_two]
    simp [A, D]
    rfl
  have hdet : gdet (p : GL (Fin (a + n)) k) = gdet A * gdet D := by
    rw [gdet, det_parab, Fintype.prod_bool, mul_comm]
  simp only [GlobalTheory.RankFibre.parChar, MonoidHom.comp_apply, MonoidHom.mul_apply, Units.val_mul, hδ]
  rw [hdet, apow_mul]
  have e : apow (gdet D) (-(a : ℂ) / 2) =
      apow (gdet D) ((n : ℂ) / 2) * apow (gdet D) (-((a + n : ℕ) : ℂ) / 2) := by
    rw [← apow_add]; congr 1; push_cast; ring
  show apow (gdet A) ((n : ℂ) / 2) * apow (gdet D) (-(a : ℂ) / 2) * (((ν * ν⁻¹) (gdet A) : ℂˣ) : ℂ) *
    ((ν⁻¹ (gdet D) : ℂˣ) : ℂ) = _
  rw [e, mul_inv_cancel]
  simp only [MonoidHom.one_apply, Units.val_one, mul_one, MonoidHom.inv_apply]
  ring

end GlobalTheory.FullRankCoinv.IndTwist

namespace GlobalTheory.FullRankCoinv.IndTwist

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def detTw (d : ℕ) (s : ℂ) : (GL (Fin d) k → ℂ) →ₗ[ℂ] (GL (Fin d) k → ℂ) where
  toFun f x := apow (gdet x) s * f x
  map_add' f g := by funext x; simp [mul_add]
  map_smul' c f := by funext x; simp; ring

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem detTw_apply (d : ℕ) (s : ℂ) (f : GL (Fin d) k → ℂ) (x : GL (Fin d) k) :
    detTw d s f x = apow (gdet x) s * f x := rfl

/- English proof (translation)
Use function extensionality and compare the values at `x`. Rewrite using `[detTw_apply, detTw_apply, ← mul_assoc, ← apow_add]`. Simplify using the standard rewrite rules.
-/
theorem detTw_neg_detTw (d : ℕ) (s : ℂ) (f : GL (Fin d) k → ℂ) : detTw d (-s) (detTw d s f) = f := by
  funext x; rw [detTw_apply, detTw_apply, ← mul_assoc, ← apow_add]; simp

/- English proof (translation)
Simplify using `using detTw_neg_detTw d (-s) f`.
-/
theorem detTw_detTw_neg (d : ℕ) (s : ℂ) (f : GL (Fin d) k → ℂ) : detTw d s (detTw d (-s) f) = f := by
  simpa using detTw_neg_detTw d (-s) f

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [detTw_apply, Pi.smul_apply, smul_eq_mul, gdet_mul, apow_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem detTw_translate (d : ℕ) (s : ℂ) (f : GL (Fin d) k → ℂ) (h : GL (Fin d) k) :
    (fun x => detTw d s f (x * h)) = apow (gdet h) s • detTw d s (fun x => f (x * h)) := by
  funext x
  simp only [detTw_apply, Pi.smul_apply, smul_eq_mul, gdet_mul, apow_mul]
  ring

/- English proof (translation)
Take `⟨⟨U, hU, hfU⟩, hfl⟩` from `hf`. Establish `hK : IsSmoothChar (detChar (Fin (a + n)) (absPow k ((n : ℂ) / 2)))` using `(isSmoothChar_of_isUnram (isUnram_absPow k _)).detChar`. Establish `hK1 : ((detChar (Fin (a + n)) (absPow k ((n : ℂ) / 2))).ker : Set (GL (Fin (a + n)) k)) ∈ nhds 1` using `hK.mem_nhds (by simp)`. Use `⟨mem_smoothPart_of_nhds (Filter.mem_of_superset (Filter.inter_mem hU hK1) fun g hg => ?_), ?_⟩` and prove the remaining obligations. Establish `hg2 : apow (gdet g) ((n : ℂ) / 2) = 1`.

Use `congrArg Units.val (MonoidHom.mem_ker.1 hg.2)` as an intermediate fact. Conclude with `this`. Use `show (fun x => detTw (a + n) ((n : ℂ) / 2) f (x * g)) = detTw (a + n) ((n : ℂ) / 2) f`. Use function extensionality and compare the values at `x`. Simplify using `only [detTw_apply, gdet_mul, apow_mul, hg2, mul_one, hfU x g hg.1]`.

Introduce `p x`. Establish `h` using `hfl p x (leviProj k (GlobalTheory.RankFibre.blocks a n) p true) (Y0_mul_parab p)`. Simplify using `only [ofChar_apply, detTw_apply, gdet_mul, apow_mul, h, parChar_eq]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem detTw_mem_indScal {a n : ℕ} (ν : kˣ →* ℂˣ) {f : GL (Fin (a + n)) k → ℂ} (hf : f ∈ indSp k n (a + n) ν) :
    detTw (a + n) ((n : ℂ) / 2) f ∈ GlobalTheory.RankFibre.indScal ν ν⁻¹ a n := by
  obtain ⟨⟨U, hU, hfU⟩, hfl⟩ := hf
  have hK : IsSmoothChar (detChar (Fin (a + n)) (absPow k ((n : ℂ) / 2))) :=
    (isSmoothChar_of_isUnram (isUnram_absPow k _)).detChar
  have hK1 : ((detChar (Fin (a + n)) (absPow k ((n : ℂ) / 2))).ker : Set (GL (Fin (a + n)) k)) ∈ nhds 1 :=
    hK.mem_nhds (by simp)
  refine ⟨mem_smoothPart_of_nhds (Filter.mem_of_superset (Filter.inter_mem hU hK1) fun g hg => ?_), ?_⟩
  · have hg2 : apow (gdet g) ((n : ℂ) / 2) = 1 := by
      have := congrArg Units.val (MonoidHom.mem_ker.1 hg.2)
      exact this
    show (fun x => detTw (a + n) ((n : ℂ) / 2) f (x * g)) = detTw (a + n) ((n : ℂ) / 2) f
    funext x
    simp only [detTw_apply, gdet_mul, apow_mul, hg2, mul_one, hfU x g hg.1]
  · intro p x
    have h := hfl p x (leviProj k (GlobalTheory.RankFibre.blocks a n) p true) (Y0_mul_parab p)
    simp only [ofChar_apply, detTw_apply, gdet_mul, apow_mul, h, parChar_eq]
    ring

end GlobalTheory.FullRankCoinv.IndTwist

namespace GlobalTheory.FullRankCoinv

open IndTwist

/- English proof (translation)
Introduce `P k _ _ _ _ n d ν hn hνs hνu N hN hinv`. Take `⟨a, rfl⟩ : ∃ a, d = a + n` from `⟨d - n, by omega⟩`. Establish `hu : IsUnitaryChar ν⁻¹` using `fun g => by`. Rewrite using `[MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, hνu g, inv_one]`. Use `set s : ℂ := (n : ℂ) / 2`.

Set `M : Submodule ℂ (GL (Fin (a + n)) k → ℂ)` to `N.comap (detTw (a + n) (-s))`. Establish `hMle : M ≤ GlobalTheory.RankFibre.indScal ν ν⁻¹ a n` using `fun g hg => by`. Use `detTw_mem_indScal ν (hN hg)` as an intermediate fact. Rewrite `this` using `[detTw_detTw_neg]`. Then use the resulting hypothesis. Establish `hMinv : ∀ g ∈ M, ∀ h : GL (Fin (a + n)) k, (fun x => g (x * h)) ∈ M` using `fun g hg h => by show detTw (a + n) (-s) (fun x => g (x * h)) ∈ N`.

Establish `e : detTw (a + n) (-s) (fun x => g (x * h)) = apow (gdet h) s • (fun x => detTw (a + n) (-s) g (x * h))`. Rewrite using `[detTw_translate, smul_smul, ← apow_add]`. Simplify using the standard rewrite rules. Rewrite using `[e]`. Conclude with `N.smul_mem _ (hinv _ hg h)`.

Establish `hmemM : ∀ f ∈ N, detTw (a + n) s f ∈ M` using `fun f hf => by show detTw (a + n) (-s) (detTw (a + n) s f) ∈ N`. Rewrite using `[detTw_neg_detTw]` and apply the resulting hypothesis. Break down `GlobalTheory.RankFibre.indScal_irreducible P.bernsteinUnitaryProductIrreducible k a n ν ν⁻¹ hνs hνu hνs.inv hu M hMle hMinv with h | h` into its components or cases. Use `left`. Use `(Submodule.eq_bot_iff N).2 fun f hf => ?_` and prove the remaining obligations.

Establish `h0 : detTw (a + n) s f = 0`. Use `hmemM f hf` as an intermediate fact. Rewrite `this` using `[h]`. Conclude with `(Submodule.mem_bot ℂ).1 this`. Rewrite using `[← detTw_neg_detTw (a + n) s f, h0, map_zero]`.

Use `right`. Use `le_antisymm hN fun f hf => ?_` and prove the remaining obligations. Use `h (detTw_mem_indScal ν hf)` as an intermediate fact. Establish `h' : detTw (a + n) (-s) (detTw (a + n) s f) ∈ N` using `this`. Rewrite `h'` using `[detTw_neg_detTw]`. Then use the resulting hypothesis.
-/
theorem indSp_irreducible : GlobalTheory.FunPr.Hypotheses₂ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n d : ℕ) (ν : kˣ →* ℂˣ), n ≤ d → GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsUnitaryChar ν →
    ∀ N : Submodule ℂ (GL (Fin d) k → ℂ), N ≤ GlobalTheory.FullRankCoinv.indSp k n d ν →
      (∀ f ∈ N, ∀ h₀ : GL (Fin d) k, (fun h => f (h * h₀)) ∈ N) → N = ⊥ ∨ N = GlobalTheory.FullRankCoinv.indSp k n d ν := by
  intro P k _ _ _ _ n d ν hn hνs hνu N hN hinv
  obtain ⟨a, rfl⟩ : ∃ a, d = a + n := ⟨d - n, by omega⟩
  have hu : IsUnitaryChar ν⁻¹ := fun g => by
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, hνu g, inv_one]
  set s : ℂ := (n : ℂ) / 2
  let M : Submodule ℂ (GL (Fin (a + n)) k → ℂ) := N.comap (detTw (a + n) (-s))
  have hMle : M ≤ GlobalTheory.RankFibre.indScal ν ν⁻¹ a n := fun g hg => by
    have := detTw_mem_indScal ν (hN hg)
    rwa [detTw_detTw_neg] at this
  have hMinv : ∀ g ∈ M, ∀ h : GL (Fin (a + n)) k, (fun x => g (x * h)) ∈ M := fun g hg h => by
    show detTw (a + n) (-s) (fun x => g (x * h)) ∈ N
    have e : detTw (a + n) (-s) (fun x => g (x * h)) =
        apow (gdet h) s • (fun x => detTw (a + n) (-s) g (x * h)) := by
      rw [detTw_translate, smul_smul, ← apow_add]; simp
    rw [e]
    exact N.smul_mem _ (hinv _ hg h)
  have hmemM : ∀ f ∈ N, detTw (a + n) s f ∈ M := fun f hf => by
    show detTw (a + n) (-s) (detTw (a + n) s f) ∈ N
    rwa [detTw_neg_detTw]
  rcases GlobalTheory.RankFibre.indScal_irreducible P.bernsteinUnitaryProductIrreducible k a n ν ν⁻¹ hνs hνu hνs.inv hu
    M hMle hMinv with h | h
  · left
    refine (Submodule.eq_bot_iff N).2 fun f hf => ?_
    have h0 : detTw (a + n) s f = 0 := by
      have := hmemM f hf
      rw [h] at this
      exact (Submodule.mem_bot ℂ).1 this
    rw [← detTw_neg_detTw (a + n) s f, h0, map_zero]
  · right
    refine le_antisymm hN fun f hf => ?_
    have := h (detTw_mem_indScal ν hf)
    have h' : detTw (a + n) (-s) (detTw (a + n) s f) ∈ N := this
    rwa [detTw_neg_detTw] at h'

end GlobalTheory.FullRankCoinv
