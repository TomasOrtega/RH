import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.LiftFactorization
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CubeSignEmb
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.Qh71.cubeSign_emb t h k`.
-/
private theorem cubeSign_emb {κ : Type} [LinearOrder κ] (t : Finset κ) {n : ℕ} (h : t.card = n) (k : Fin n) :
    GlobalTheory.cubeSign t (t.orderEmbOfFin h k) = (-1) ^ (k : ℕ) :=
  _root_.UpperTheory.Reformulated.B.Qh71.cubeSign_emb t h k

/- English proof (translation)
Use `Finset.orderEmbOfFin_unique h' (f := fun a => t.orderEmbOfFin h (k.succAbove a)) (fun x => Finset.mem_erase.2 ⟨fun hx => Fin.succAbove_ne k x ((t.orderEmbOfFin h).injective hx), Finset.orderEmbOfFin_mem _ _ _⟩) ((t.orderEmbOfFin h).strictMono.comp (Fin.strictMono_succAbove k))` as an intermediate fact. Conclude with `(congrFun this a).symm`.
-/
private theorem erase_emb {κ : Type} [LinearOrder κ] (t : Finset κ) {n : ℕ} (h : t.card = n + 1) (k : Fin (n + 1))
    (h' : (t.erase (t.orderEmbOfFin h k)).card = n) (a : Fin n) :
    (t.erase (t.orderEmbOfFin h k)).orderEmbOfFin h' a = t.orderEmbOfFin h (k.succAbove a) := by
  have := Finset.orderEmbOfFin_unique h' (f := fun a => t.orderEmbOfFin h (k.succAbove a))
    (fun x => Finset.mem_erase.2 ⟨fun hx => Fin.succAbove_ne k x ((t.orderEmbOfFin h).injective hx),
      Finset.orderEmbOfFin_mem _ _ _⟩)
    ((t.orderEmbOfFin h).strictMono.comp (Fin.strictMono_succAbove k))
  exact (congrFun this a).symm

/- English proof (translation)
Establish `h' : (t.erase (t.orderEmbOfFin h k)).card = p`. Rewrite using `[Finset.card_erase_of_mem (Finset.orderEmbOfFin_mem _ _ _), h]`. Both sides reduce to the same expression. Unfold `detC`. Rewrite using `[dif_pos h']`.

Use `congr 1`. Use extensionality with `a b`. Simplify using `only [Matrix.of_apply]`. Rewrite using `[erase_emb t h k h' a]`.
-/
private theorem detC_erase {S κ : Type} [CommRing S] [LinearOrder κ] {p : ℕ} (ρ : κ → Fin p → S) (t : Finset κ)
    (h : t.card = p + 1) (k : Fin (p + 1)) :
    detC ρ (t.erase (t.orderEmbOfFin h k)) =
      (Matrix.of fun a b => ρ (t.orderEmbOfFin h (k.succAbove a)) b).det := by
  have h' : (t.erase (t.orderEmbOfFin h k)).card = p := by
    rw [Finset.card_erase_of_mem (Finset.orderEmbOfFin_mem _ _ _), h]; rfl
  unfold detC
  rw [dif_pos h']
  congr 1
  ext a b
  simp only [Matrix.of_apply]
  rw [erase_emb t h k h' a]

/- English proof (translation)
Use `set e := t.orderEmbOfFin h with he`. Set `A : Matrix (Fin (p + 1)) (Fin (p + 1)) S` to `Matrix.of fun a => Fin.cons (∑ b, ρ (e a) b * f b) (ρ (e a))`. Establish `hA : A.det = 0`. Establish `h1` using `Matrix.det_updateCol_sum A 0 (Fin.cons 0 f : Fin (p + 1) → S)`. Establish `h2 : (A.updateCol 0 fun k => ∑ i, (Fin.cons 0 f : Fin (p + 1) → S) i • A k i) = A`.

Use extensionality with `a b`. Use `Fin.cases ?_ (fun b => ?_) b` and prove the remaining obligations. Simplify using `[A, Matrix.updateCol_apply, Fin.sum_univ_succ, mul_comm]`. Simplify using `[A, Matrix.updateCol_apply, Fin.succ_ne_zero]`. Rewrite `h1` using `[h2]`.

Simplify using `using h1`. Establish `ht : t = Finset.univ.map e.toEmbedding`. Rewrite using `[he, Finset.map_orderEmbOfFin_univ]`. Establish `hs : ∑ i ∈ t, ((GlobalTheory.cubeSign t i : ℤ) : S) * ((∑ b, ρ i b * f b) * detC ρ (t.erase i)) = ∑ k : Fin (p + 1), (((-1 : ℤ) ^ (k : ℕ) : ℤ) : S) * ((∑ b, ρ (e k) b * f b) * detC ρ (t.erase (e k)))` using `by conv_lhs => rw [show (∑ i ∈ t, ((GlobalTheory.cubeSign t i : ℤ) : S) * ((∑ b, ρ i b * f b) * detC ρ (t.erase i))) = ∑ i ∈ Finset.univ.map e.toEmbedding, ((GlobalTheory.cubeSign t i : ℤ) : S) * ((∑ b, ρ i b * f b) * detC ρ (t.erase i)) by`. Rewrite using `[← ht]]`.

Rewrite using `[Finset.sum_map]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `only [RelEmbedding.coe_toEmbedding]`. Rewrite using `[he, cubeSign_emb t h k]`. Rewrite using `[hs, ← hA, Matrix.det_succ_column_zero]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[he, detC_erase ρ t h k]`. Establish `: (A.submatrix k.succAbove Fin.succ) = Matrix.of fun a b => ρ (t.orderEmbOfFin h (k.succAbove a)) b`. Use extensionality with `a b`. Simplify using `[A, he]`.

Rewrite using `[this]`. Simplify using `[A, he, mul_assoc]`.
-/
private theorem ring_core {S κ : Type} [CommRing S] [LinearOrder κ] {p : ℕ} (ρ : κ → Fin p → S) (f : Fin p → S)
    (t : Finset κ) (h : t.card = p + 1) :
    ∑ i ∈ t, ((GlobalTheory.cubeSign t i : ℤ) : S) * ((∑ b, ρ i b * f b) * detC ρ (t.erase i)) = 0 := by
  set e := t.orderEmbOfFin h with he
  let A : Matrix (Fin (p + 1)) (Fin (p + 1)) S :=
    Matrix.of fun a => Fin.cons (∑ b, ρ (e a) b * f b) (ρ (e a))
  have hA : A.det = 0 := by
    have h1 := Matrix.det_updateCol_sum A 0 (Fin.cons 0 f : Fin (p + 1) → S)
    have h2 : (A.updateCol 0 fun k => ∑ i, (Fin.cons 0 f : Fin (p + 1) → S) i • A k i) = A := by
      ext a b
      refine Fin.cases ?_ (fun b => ?_) b
      · simp [A, Matrix.updateCol_apply, Fin.sum_univ_succ, mul_comm]
      · simp [A, Matrix.updateCol_apply, Fin.succ_ne_zero]
    rw [h2] at h1
    simpa using h1
  have ht : t = Finset.univ.map e.toEmbedding := by
    rw [he, Finset.map_orderEmbOfFin_univ]
  have hs : ∑ i ∈ t, ((GlobalTheory.cubeSign t i : ℤ) : S) * ((∑ b, ρ i b * f b) * detC ρ (t.erase i)) =
      ∑ k : Fin (p + 1), (((-1 : ℤ) ^ (k : ℕ) : ℤ) : S) * ((∑ b, ρ (e k) b * f b) * detC ρ (t.erase (e k))) := by
    conv_lhs => rw [show (∑ i ∈ t, ((GlobalTheory.cubeSign t i : ℤ) : S) * ((∑ b, ρ i b * f b) * detC ρ (t.erase i))) =
      ∑ i ∈ Finset.univ.map e.toEmbedding, ((GlobalTheory.cubeSign t i : ℤ) : S) * ((∑ b, ρ i b * f b) * detC ρ (t.erase i)) by
        rw [← ht]]
    rw [Finset.sum_map]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [RelEmbedding.coe_toEmbedding]
    rw [he, cubeSign_emb t h k]
  rw [hs, ← hA, Matrix.det_succ_column_zero]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [he, detC_erase ρ t h k]
  have : (A.submatrix k.succAbove Fin.succ) = Matrix.of fun a b => ρ (t.orderEmbOfFin h (k.succAbove a)) b := by
    ext a b
    simp [A, he]
  rw [this]
  simp [A, he, mul_assoc]

/- English proof (translation)
Introduce `S E _ _ _ _ act κ _ p ρ f m`. Use function extensionality and compare the values at `t`. Establish `key : wd (fun l => act (∑ b, ρ l b * f b)) (fun s => act (detC ρ s) m) t = ∑ i ∈ t, (GlobalTheory.cubeSign t i : ℤ) • act (∑ b, ρ i b * f b) (act (detC ρ (t.erase i)) m)`. Simplify using `[wd, LinearMap.pi_apply, LinearMap.sum_apply]`. Rewrite using `[key]`.

Distinguish the cases in `h : t.card = p + 1`. Establish `h0` using `congrArg (fun x => act x m) (ring_core ρ f t h)`. Simplify using `only [map_zero, LinearMap.zero_apply, map_sum, LinearMap.sum_apply] at h0`. Rewrite using `[Pi.zero_apply, ← h0]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[← zsmul_eq_mul, map_zsmul, LinearMap.smul_apply, map_mul, Module.End.mul_apply]`. Rewrite using `[Pi.zero_apply]`. Use `Finset.sum_eq_zero fun i hi => ?_` and prove the remaining obligations. Establish `hc : (t.erase i).card ≠ p`. Rewrite using `[Finset.card_erase_of_mem hi]`.

Use `Finset.card_pos.2 ⟨i, hi⟩` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Simplify using `[detC, hc]`.
-/
theorem UpperTheory.Gal.productCup_of_system.det_of :
    Det := by
  intro S E _ _ _ _ act κ _ p ρ f m
  funext t
  have key : wd (fun l => act (∑ b, ρ l b * f b)) (fun s => act (detC ρ s) m) t =
      ∑ i ∈ t, (GlobalTheory.cubeSign t i : ℤ) • act (∑ b, ρ i b * f b) (act (detC ρ (t.erase i)) m) := by
    simp [wd, LinearMap.pi_apply, LinearMap.sum_apply]
  rw [key]
  by_cases h : t.card = p + 1
  · have h0 := congrArg (fun x => act x m) (ring_core ρ f t h)
    simp only [map_zero, LinearMap.zero_apply, map_sum, LinearMap.sum_apply] at h0
    rw [Pi.zero_apply, ← h0]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← zsmul_eq_mul, map_zsmul, LinearMap.smul_apply, map_mul, Module.End.mul_apply]
  · rw [Pi.zero_apply]
    refine Finset.sum_eq_zero fun i hi => ?_
    have hc : (t.erase i).card ≠ p := by
      rw [Finset.card_erase_of_mem hi]
      have := Finset.card_pos.2 ⟨i, hi⟩
      omega
    simp [detC, hc]
