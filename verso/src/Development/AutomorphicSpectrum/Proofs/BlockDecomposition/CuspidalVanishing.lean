import Mathlib
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll

open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFin.CuspVan

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Conclude with `blk_mul b c p.2.1 q.2.1`.
-/
theorem levi_mul {s : ℕ} (b : ι → Fin s) (c : Fin s) (p q : parab K b) :
    levi K b c (p * q) = levi K b c p * levi K b c q := by
  apply Units.ext
  exact blk_mul b c p.2.1 q.2.1

/- English proof (translation)
Use `⟨mul_mem hx.1 hy.1, fun i j hij => ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single i]`. Rewrite using `[hx.2 i i rfl, if_pos rfl, one_mul]`. Conclude with `hy.2 i j hij`. Introduce `k _ hk`.

Break down `lt_trichotomy (b k) (b i) with h | h | h` into its components or cases. Rewrite using `[hx.1.1 i k h, zero_mul]`. Rewrite using `[hx.2 i k h.symm, if_neg (Ne.symm hk), zero_mul]`. Rewrite using `[hy.1.1 k j (hij ▸ h), mul_zero]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ i) h`.
-/
theorem unip_mul {s : ℕ} (b : ι → Fin s) {x y : GL ι K} (hx : x ∈ unip K b) (hy : y ∈ unip K b) :
    x * y ∈ unip K b := by
  refine ⟨mul_mem hx.1 hy.1, fun i j hij => ?_⟩
  rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [hx.2 i i rfl, if_pos rfl, one_mul]
    exact hy.2 i j hij
  · intro k _ hk
    rcases lt_trichotomy (b k) (b i) with h | h | h
    · rw [hx.1.1 i k h, zero_mul]
    · rw [hx.2 i k h.symm, if_neg (Ne.symm hk), zero_mul]
    · rw [hy.1.1 k j (hij ▸ h), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

/- English proof (translation)
Use `⟨one_mem _, fun i j _ => ?_⟩` and prove the remaining obligations. Simplify using `[Matrix.one_apply]`.
-/
theorem one_mem_unip {s : ℕ} (b : ι → Fin s) : (1 : GL ι K) ∈ unip K b := by
  refine ⟨one_mem _, fun i j _ => ?_⟩
  simp [Matrix.one_apply]

open Classical in

/- English proof (translation)
Use `set Y := Finset.univ.filter (fun v : GL ι K => v ∈ unip K bb) with hY`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `w`. Apply `hτ t bb hs ht` to reduce the goal to its premises. Introduce `y hy`.

Establish `himg : Y.image (fun v => y * v) = Y`. Apply `Finset.eq_of_subset_of_card_le` to reduce the goal to its premises. Introduce `z hz`. Take `⟨v, hv, rfl⟩` from `Finset.mem_image.mp hz`. Simplify using `only [hY, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢`.

Conclude with `unip_mul bb hy hv`. Rewrite using `[Finset.card_image_of_injective _ (mul_right_injective y)]`. Establish `h1 : ∑ v ∈ Y, τ.ρ (y * v) = ∑ v ∈ Y, τ.ρ v` using `by conv_rhs => rw [← himg]`. Rewrite using `[Finset.sum_image (fun a _ b _ h => mul_right_injective y h)]`. Rewrite using `[LinearMap.sum_apply, map_sum, ← LinearMap.sum_apply, ← h1, LinearMap.sum_apply]`.

Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Both sides reduce to the same expression.
-/
theorem sum_unip_rho {t : ℕ} (bb : ι → Fin t) (hs : Function.Surjective bb) (ht : 2 ≤ t)
    (τ : FDRep ℂ (GL ι K)) (hτ : IsCuspidal K τ) :
    ∑ v ∈ Finset.univ.filter (fun v : GL ι K => v ∈ unip K bb), τ.ρ v = 0 := by
  set Y := Finset.univ.filter (fun v : GL ι K => v ∈ unip K bb) with hY
  apply LinearMap.ext
  intro w
  apply hτ t bb hs ht
  intro y hy
  have himg : Y.image (fun v => y * v) = Y := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
      simp only [hY, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      exact unip_mul bb hy hv
    · rw [Finset.card_image_of_injective _ (mul_right_injective y)]
  have h1 : ∑ v ∈ Y, τ.ρ (y * v) = ∑ v ∈ Y, τ.ρ v := by
    conv_rhs => rw [← himg]
    rw [Finset.sum_image (fun a _ b _ h => mul_right_injective y h)]
  rw [LinearMap.sum_apply, map_sum, ← LinearMap.sum_apply, ← h1, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [map_mul]
  rfl

open Classical in

/- English proof (translation)
Establish `h` using `congrArg (fun P => LinearMap.trace ℂ τ (τ.ρ g * P)) (sum_unip_rho bb hs ht τ hτ)`. Simplify using `only [mul_zero, map_zero, Finset.mul_sum, map_sum] at h`. Rewrite using `[← h]`. Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations. Rewrite using `[FDRep.character, map_mul]`.
-/
theorem sum_char {t : ℕ} (bb : ι → Fin t) (hs : Function.Surjective bb) (ht : 2 ≤ t)
    (τ : FDRep ℂ (GL ι K)) (hτ : IsCuspidal K τ) (g : GL ι K) :
    ∑ v ∈ Finset.univ.filter (fun v : GL ι K => v ∈ unip K bb), τ.character (g * v) = 0 := by
  have h := congrArg (fun P => LinearMap.trace ℂ τ (τ.ρ g * P)) (sum_unip_rho bb hs ht τ hτ)
  simp only [mul_zero, map_zero, Finset.mul_sum, map_sum] at h
  rw [← h]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [FDRep.character, map_mul]

def rankMap {κ : Type} [Fintype κ] {s : ℕ} (β : κ → Fin s) :
    κ → Fin (Finset.univ.image β).card := fun i =>
  ((Finset.univ.image β).orderIsoOfFin rfl).symm ⟨β i, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩

/- English proof (translation)
Simplify using `only [rankMap]`. Rewrite using `[OrderIso.lt_iff_lt]`. Conclude with `Iff.rfl`.
-/
theorem rankMap_lt {κ : Type} [Fintype κ] {s : ℕ} (β : κ → Fin s) (i j : κ) :
    rankMap β i < rankMap β j ↔ β i < β j := by
  simp only [rankMap]
  rw [OrderIso.lt_iff_lt]
  exact Iff.rfl

/- English proof (translation)
Simplify using `only [rankMap]`. Rewrite using `[EmbeddingLike.apply_eq_iff_eq, Subtype.mk.injEq]`.
-/
theorem rankMap_eq {κ : Type} [Fintype κ] {s : ℕ} (β : κ → Fin s) (i j : κ) :
    rankMap β i = rankMap β j ↔ β i = β j := by
  simp only [rankMap]
  rw [EmbeddingLike.apply_eq_iff_eq, Subtype.mk.injEq]

/- English proof (translation)
Introduce `x`. Take `⟨i, -, hi⟩` from `Finset.mem_image.mp (((Finset.univ.image β).orderIsoOfFin rfl) x).2`. Use `⟨i, ?_⟩` and prove the remaining obligations. Simplify using `only [rankMap]`. Rewrite using `[OrderIso.symm_apply_eq]`.

Conclude with `Subtype.ext hi`.
-/
theorem rankMap_surj {κ : Type} [Fintype κ] {s : ℕ} (β : κ → Fin s) :
    Function.Surjective (rankMap β) := by
  intro x
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp (((Finset.univ.image β).orderIsoOfFin rfl) x).2
  refine ⟨i, ?_⟩
  simp only [rankMap]
  rw [OrderIso.symm_apply_eq]
  exact Subtype.ext hi

def extHom {s : ℕ} (b : ι → Fin s) (c : Fin s) : GL {i // b i = c} K →* GL ι K :=
  (leviEmb K (fun i => b i = c)).comp (MonoidHom.inl _ _)

/- English proof (translation)
Establish `h0 : (extHom b c v : Matrix ι ι K) = (Matrix.fromBlocks (v : Matrix {i // b i = c} {i // b i = c} K) 0 0 1).submatrix (Equiv.sumCompl (fun i => b i = c)).symm (Equiv.sumCompl (fun i => b i = c)).symm` using `rfl`. Rewrite using `[h0, Matrix.submatrix_apply]`. Apply the tactic sequence `by_cases hi : b i = c <;> by_cases hj : b j = c`. Simplify using `[hi, hj, Equiv.sumCompl_symm_apply_of_pos]`. Establish `: i ≠ j` using `fun h => hj (h ▸ hi)`.

Simplify using `[hi, hj, Equiv.sumCompl_symm_apply_of_pos, Equiv.sumCompl_symm_apply_of_neg, this]`. Establish `: i ≠ j` using `fun h => hi (h ▸ hj)`. Simplify using `[hi, hj, Equiv.sumCompl_symm_apply_of_pos, Equiv.sumCompl_symm_apply_of_neg, this]`. Simplify using `[hi, hj, Equiv.sumCompl_symm_apply_of_neg, Matrix.one_apply, Subtype.ext_iff]`.
-/
theorem extHom_apply {s : ℕ} (b : ι → Fin s) (c : Fin s) (v : GL {i // b i = c} K) (i j : ι) :
    (extHom b c v : Matrix ι ι K) i j =
      if h : b i = c ∧ b j = c then (v : Matrix {i // b i = c} {i // b i = c} K) ⟨i, h.1⟩ ⟨j, h.2⟩ else if i = j then 1 else 0 := by
  have h0 : (extHom b c v : Matrix ι ι K) =
      (Matrix.fromBlocks (v : Matrix {i // b i = c} {i // b i = c} K) 0 0 1).submatrix
        (Equiv.sumCompl (fun i => b i = c)).symm (Equiv.sumCompl (fun i => b i = c)).symm := rfl
  rw [h0, Matrix.submatrix_apply]
  by_cases hi : b i = c <;> by_cases hj : b j = c
  · simp [hi, hj, Equiv.sumCompl_symm_apply_of_pos]
  · have : i ≠ j := fun h => hj (h ▸ hi)
    simp [hi, hj, Equiv.sumCompl_symm_apply_of_pos, Equiv.sumCompl_symm_apply_of_neg, this]
  · have : i ≠ j := fun h => hi (h ▸ hj)
    simp [hi, hj, Equiv.sumCompl_symm_apply_of_pos, Equiv.sumCompl_symm_apply_of_neg, this]
  · simp [hi, hj, Equiv.sumCompl_symm_apply_of_neg, Matrix.one_apply, Subtype.ext_iff]

/- English proof (translation)
Introduce `i j h`. Rewrite using `[extHom_apply]`. Use `split_ifs with h1 h2`. Conclude with `hw _ _ ((rankMap_lt _ _ _).mpr h)`. Conclude with `absurd (h2 ▸ h) (lt_irrefl _)`.

Both sides reduce to the same expression.
-/
theorem extHom_blockUT {s s' : ℕ} (b : ι → Fin s) (c : Fin s) (β : ι → Fin s')
    {w : GL {i // b i = c} K}
    (hw : IsBlockUT K (rankMap fun i : {i // b i = c} => β i.1)
      (w : Matrix {i // b i = c} {i // b i = c} K)) :
    IsBlockUT K β (extHom b c w : Matrix ι ι K) := by
  intro i j h
  rw [extHom_apply]
  split_ifs with h1 h2
  · exact hw _ _ ((rankMap_lt _ _ _).mpr h)
  · exact absurd (h2 ▸ h) (lt_irrefl _)
  · rfl

/- English proof (translation)
Use `⟨⟨extHom_blockUT b c β hv.1.1, ?_⟩, fun i j hij => ?_⟩` and prove the remaining obligations. Rewrite using `[← map_inv]`. Conclude with `extHom_blockUT b c β hv.1.2`. Rewrite using `[extHom_apply]`. Distinguish the cases in `h : b i = c ∧ b j = c`.

Rewrite using `[dif_pos h, hv.2 _ _ ((rankMap_eq _ _ _).mpr hij)]`. Simplify using `[Subtype.ext_iff]`. Rewrite using `[dif_neg h]`.
-/
theorem extHom_mem_unip {s s' : ℕ} (b : ι → Fin s) (c : Fin s) (β : ι → Fin s')
    {v : GL {i // b i = c} K} (hv : v ∈ unip K (rankMap fun i : {i // b i = c} => β i.1)) :
    extHom b c v ∈ unip K β := by
  refine ⟨⟨extHom_blockUT b c β hv.1.1, ?_⟩, fun i j hij => ?_⟩
  · rw [← map_inv]
    exact extHom_blockUT b c β hv.1.2
  · rw [extHom_apply]
    by_cases h : b i = c ∧ b j = c
    · rw [dif_pos h, hv.2 _ _ ((rankMap_eq _ _ _).mpr hij)]
      simp [Subtype.ext_iff]
    · rw [dif_neg h]

/- English proof (translation)
Rewrite using `[extHom_apply, dif_neg (fun h => hij (h.1.trans h.2.symm)), if_neg (fun e => hij (congrArg b e))]`.
-/
theorem extHom_off {s : ℕ} (b : ι → Fin s) (c : Fin s) (v : GL {i // b i = c} K) (i j : ι)
    (hij : b i ≠ b j) : (extHom b c v : Matrix ι ι K) i j = 0 := by
  rw [extHom_apply, dif_neg (fun h => hij (h.1.trans h.2.symm)),
    if_neg (fun e => hij (congrArg b e))]

/- English proof (translation)
Simplify using `only [blkGL]`. Rewrite using `[dif_pos hg, dif_pos he, dif_pos (mul_mem hg he)]`. Conclude with `levi_mul b c ⟨g, hg⟩ ⟨e, he⟩`.
-/
theorem blkGL_mul {s : ℕ} (b : ι → Fin s) (c : Fin s) {g e : GL ι K} (hg : g ∈ parab K b)
    (he : e ∈ parab K b) : blkGL b c (g * e) = blkGL b c g * blkGL b c e := by
  simp only [blkGL]
  rw [dif_pos hg, dif_pos he, dif_pos (mul_mem hg he)]
  exact levi_mul b c ⟨g, hg⟩ ⟨e, he⟩

/- English proof (translation)
Simplify using `only [blkGL]`. Rewrite using `[dif_pos hp]`. Apply `Units.ext` to reduce the goal to its premises. Use `Matrix.ext ?_` and prove the remaining obligations. Introduce and unpack `⟨i, hi⟩ ⟨j, hj⟩`.

Express the relevant statement in the definitionally equal form `(extHom b c v : Matrix ι ι K) i j = _`. Rewrite using `[extHom_apply, dif_pos ⟨hi, hj⟩]`.
-/
theorem blkGL_extHom_self {s : ℕ} (b : ι → Fin s) (c : Fin s) (v : GL {i // b i = c} K)
    (hp : extHom b c v ∈ parab K b) : blkGL b c (extHom b c v) = v := by
  simp only [blkGL]
  rw [dif_pos hp]
  apply Units.ext
  refine Matrix.ext ?_
  rintro ⟨i, hi⟩ ⟨j, hj⟩
  change (extHom b c v : Matrix ι ι K) i j = _
  rw [extHom_apply, dif_pos ⟨hi, hj⟩]

/- English proof (translation)
Simplify using `only [blkGL]`. Rewrite using `[dif_pos hp]`. Apply `Units.ext` to reduce the goal to its premises. Use `Matrix.ext ?_` and prove the remaining obligations. Introduce and unpack `⟨i, hi⟩ ⟨j, hj⟩`.

Express the relevant statement in the definitionally equal form `(extHom b c v : Matrix ι ι K) i j = (1 : Matrix {i // b i = c'} {i // b i = c'} K) ⟨i, hi⟩ ⟨j, hj⟩`. Rewrite using `[extHom_apply, dif_neg (fun h => hc (hi.symm.trans h.1)), Matrix.one_apply]`. Simplify using `[Subtype.ext_iff]`.
-/
theorem blkGL_extHom_ne {s : ℕ} (b : ι → Fin s) {c c' : Fin s} (hc : c' ≠ c)
    (v : GL {i // b i = c} K) (hp : extHom b c v ∈ parab K b) :
    blkGL b c' (extHom b c v) = 1 := by
  simp only [blkGL]
  rw [dif_pos hp]
  apply Units.ext
  refine Matrix.ext ?_
  rintro ⟨i, hi⟩ ⟨j, hj⟩
  change (extHom b c v : Matrix ι ι K) i j = (1 : Matrix {i // b i = c'} {i // b i = c'} K) ⟨i, hi⟩ ⟨j, hj⟩
  rw [extHom_apply, dif_neg (fun h => hc (hi.symm.trans h.1)), Matrix.one_apply]
  simp [Subtype.ext_iff]

/- English proof (translation)
Use `set βc : {i // b i = c} → Fin s' := fun i => β i.1 with hβc`. Establish `ht : 2 ≤ (Finset.univ.image βc).card` using `Finset.one_lt_card.mpr ⟨βc ⟨i₀, hi⟩, Finset.mem_image_of_mem _ (Finset.mem_univ _), βc ⟨j₀, hj⟩, Finset.mem_image_of_mem _ (Finset.mem_univ _), hβ⟩`. Establish `key : ∀ Y : Finset (GL {i // b i = c} K), (∀ v ∈ Y, v ∈ unip K (rankMap βc)) → 1 ∈ Y → (∀ g, ∑ v ∈ Y, (lam c).character (g * v) = 0) → ∑ h, (if h ∈ H then F h * hcFun b (fun c => (lam c).character) h else 0) = 0`. Introduce `Y hY h1 hY0`. Use `set A : GL ι K → ℂ := fun h => ∏ c' ∈ Finset.univ.erase c, (lam c').character (blkGL b c' h) with hA`.

Use `set G : GL ι K → GL {i // b i = c} K → ℂ := fun h v => if h ∈ H then F h * ((lam c).character (blkGL b c h * v) * A h) else 0 with hG`. Use `set T : GL ι K → ℂ := fun h => if h ∈ H then F h * hcFun b (fun c => (lam c).character) h else 0 with hT`. Establish `step : ∀ v ∈ Y, ∑ h, T h = ∑ h, G h v`. Introduce `v hv`. Take `⟨heH, hFe⟩` from `hF (extHom b c v) (extHom_mem_unip b c β (hY v hv)) (extHom_off b c v)`.

Establish `hep : extHom b c v ∈ parab K b` using `hH heH`. Use `(Equiv.sum_comp (Equiv.mulRight (extHom b c v)) T).symm.trans ?_` and prove the remaining obligations. Use `Finset.sum_congr rfl fun h _ => ?_` and prove the remaining obligations. Simplify using `only [Equiv.coe_mulRight, hT, hG]`. Distinguish the cases in `hh : h ∈ H`.

Rewrite using `[if_pos (mul_mem hh heH), if_pos hh, hFe h hh, hcFun, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ c), blkGL_mul b c (hH hh) hep, blkGL_extHom_self b c v hep]`. Use `congr 2`. Use `Finset.prod_congr rfl fun c' hc' => ?_` and prove the remaining obligations. Rewrite using `[blkGL_mul b c' (hH hh) hep, blkGL_extHom_ne b (Finset.ne_of_mem_erase hc') v hep, mul_one]`. Rewrite using `[if_neg hh, if_neg (fun h' => hh (by simpa using mul_mem h' (inv_mem heH)))]`.

Establish `hcard : (Y.card : ℂ) * ∑ h, T h = 0`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_const, nsmul_eq_mul]`. Use `_ = ∑ v ∈ Y, ∑ h, G h v := Finset.sum_congr rfl step`. Use `_ = ∑ h, ∑ v ∈ Y, G h v := Finset.sum_comm`.

Use `_ = 0 := by`. Use `Finset.sum_eq_zero fun h _ => ?_` and prove the remaining obligations. Distinguish the cases in `hh : h ∈ H`. Simplify using `only [hG, if_pos hh]`. Rewrite using `[← Finset.mul_sum, ← Finset.sum_mul, hY0, zero_mul, mul_zero]`.

Simplify using `only [hG, if_neg hh, Finset.sum_const_zero]`. Establish `hne : (Y.card : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr (Finset.card_ne_zero_of_mem h1)`. Conclude with `(mul_eq_zero.mp hcard).resolve_left hne`. Conclude with `key _ (fun v hv => (Finset.mem_filter.mp hv).2) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, one_mem_unip _⟩) (sum_char (rankMap βc) (rankMap_surj βc) ht (lam c) (hcusp c))`.
-/
theorem vanish {s s' : ℕ} (b : ι → Fin s) (β : ι → Fin s')
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)) (hcusp : ∀ c, IsCuspidal K (lam c))
    (c : Fin s) (i₀ j₀ : ι) (hi : b i₀ = c) (hj : b j₀ = c) (hβ : β i₀ ≠ β j₀)
    (H : Subgroup (GL ι K)) [DecidablePred (· ∈ H)] (F : GL ι K → ℂ) (hH : H ≤ parab K b)
    (hF : ∀ u ∈ unip K β, (∀ i j, b i ≠ b j → (u : Matrix ι ι K) i j = 0) →
      u ∈ H ∧ ∀ h ∈ H, F (h * u) = F h) :
    ∑ h, (if h ∈ H then F h * hcFun b (fun c => (lam c).character) h else 0) = 0 := by
  set βc : {i // b i = c} → Fin s' := fun i => β i.1 with hβc
  have ht : 2 ≤ (Finset.univ.image βc).card :=
    Finset.one_lt_card.mpr ⟨βc ⟨i₀, hi⟩, Finset.mem_image_of_mem _ (Finset.mem_univ _),
      βc ⟨j₀, hj⟩, Finset.mem_image_of_mem _ (Finset.mem_univ _), hβ⟩
  have key : ∀ Y : Finset (GL {i // b i = c} K), (∀ v ∈ Y, v ∈ unip K (rankMap βc)) → 1 ∈ Y →
      (∀ g, ∑ v ∈ Y, (lam c).character (g * v) = 0) →
      ∑ h, (if h ∈ H then F h * hcFun b (fun c => (lam c).character) h else 0) = 0 := by
    intro Y hY h1 hY0
    set A : GL ι K → ℂ := fun h => ∏ c' ∈ Finset.univ.erase c, (lam c').character (blkGL b c' h)
      with hA
    set G : GL ι K → GL {i // b i = c} K → ℂ := fun h v =>
      if h ∈ H then F h * ((lam c).character (blkGL b c h * v) * A h) else 0 with hG
    set T : GL ι K → ℂ := fun h =>
      if h ∈ H then F h * hcFun b (fun c => (lam c).character) h else 0 with hT
    have step : ∀ v ∈ Y, ∑ h, T h = ∑ h, G h v := by
      intro v hv
      obtain ⟨heH, hFe⟩ := hF (extHom b c v) (extHom_mem_unip b c β (hY v hv)) (extHom_off b c v)
      have hep : extHom b c v ∈ parab K b := hH heH
      refine (Equiv.sum_comp (Equiv.mulRight (extHom b c v)) T).symm.trans ?_
      refine Finset.sum_congr rfl fun h _ => ?_
      simp only [Equiv.coe_mulRight, hT, hG]
      by_cases hh : h ∈ H
      · rw [if_pos (mul_mem hh heH), if_pos hh, hFe h hh, hcFun,
          ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ c),
          blkGL_mul b c (hH hh) hep, blkGL_extHom_self b c v hep]
        congr 2
        refine Finset.prod_congr rfl fun c' hc' => ?_
        rw [blkGL_mul b c' (hH hh) hep, blkGL_extHom_ne b (Finset.ne_of_mem_erase hc') v hep, mul_one]
      · rw [if_neg hh, if_neg (fun h' => hh (by simpa using mul_mem h' (inv_mem heH)))]
    have hcard : (Y.card : ℂ) * ∑ h, T h = 0 := by
      calc (Y.card : ℂ) * ∑ h, T h = ∑ _v ∈ Y, ∑ h, T h := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ = ∑ v ∈ Y, ∑ h, G h v := Finset.sum_congr rfl step
        _ = ∑ h, ∑ v ∈ Y, G h v := Finset.sum_comm
        _ = 0 := by
            refine Finset.sum_eq_zero fun h _ => ?_
            by_cases hh : h ∈ H
            · simp only [hG, if_pos hh]
              rw [← Finset.mul_sum, ← Finset.sum_mul, hY0, zero_mul, mul_zero]
            · simp only [hG, if_neg hh, Finset.sum_const_zero]
    have hne : (Y.card : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.card_ne_zero_of_mem h1)
    exact (mul_eq_zero.mp hcard).resolve_left hne
  classical
  exact key _ (fun v hv => (Finset.mem_filter.mp hv).2)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, one_mem_unip _⟩)
    (sum_char (rankMap βc) (rankMap_surj βc) ht (lam c) (hcusp c))

/- English proof (translation)
Introduce `K _ _ _ ι _ _ s s' b β lam hcusp ⟨i₀, j₀, hb, hβ⟩ H F hH hF`. Conclude with `vanish b β lam hcusp (b i₀) i₀ j₀ rfl hb.symm hβ H F hH hF`.
-/
theorem cuspVanish : ReciprocityTheory.Ty.Fin.St.CuspVanish := by
  intro K _ _ _ ι _ _ s s' b β lam hcusp ⟨i₀, j₀, hb, hβ⟩ H F hH hF
  classical
  exact vanish b β lam hcusp (b i₀) i₀ j₀ rfl hb.symm hβ H F hH hF

end GlobalTheory.CompanionTheory.TyFin.CuspVan
