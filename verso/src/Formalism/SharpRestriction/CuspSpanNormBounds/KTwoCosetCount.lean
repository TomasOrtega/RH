import Formalism.SharpRestriction.CuspSpanNormBounds.KTwoMinorIntegrality

noncomputable section

namespace Formalism.MainNotions.KTwoCosetCount

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section A

variable {D : D7}

/- English proof (translation)
Unfold `KappaEndpoints.k2ends`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem card_ends_le (j : ℕ) (δ : ℕ → D.host.E) : (KappaEndpoints.k2ends D j δ).card ≤ j := by
  classical
  unfold KappaEndpoints.k2ends
  calc _ ≤ (Finset.Icc 1 j).card := Finset.card_filter_le _ _
    _ = j := by simp

/- English proof (translation)
Use `set σ := KappaEndpoints.k2sg D H1 j δ τ with hσ`. Establish `h1 : 1 ≤ σ` using `KappaEndpoints.one_le_minor_sigma H1 j δ τ`. Establish `hle : ∀ l ∈ KappaEndpoints.k2ends D j δ, max 1 (absReal D.host.rdE (embS D τ) D.R.rS l (δ l) / (2 * H1) ^ (2 * D.R.rS)) ≤ σ`. Introduce `l hl`. Use `max_le h1 ?_` and prove the remaining obligations.

Rewrite using `[hσ]`. Unfold `KappaEndpoints.k2sg`. Conclude with `(Finset.le_fold_max _).2 (Or.inr ⟨l, hl, le_rfl⟩)`. Establish `step1 : ∏ l ∈ KappaEndpoints.k2ends D j δ, σ ^ (-(3 : ℝ)) ≤ ∏ l ∈ KappaEndpoints.k2ends D j δ, (max 1 (absReal D.host.rdE (embS D τ) D.R.rS l (δ l) / (2 * H1) ^ (2 * D.R.rS))) ^ (-(3 : ℝ))`. Apply `Finset.prod_le_prod` to reduce the goal to its premises.

Introduce `l _; exact Real.rpow_nonneg (by linarith) _`. Introduce `l hl`. Conclude with `Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le one_pos (le_max_left _ _)) (hle l hl) (by norm_num)`. Establish `hc` using `card_ends_le (D := D) j δ`. Establish `step0 : σ ^ (-(3 * (D.R.rS : ℝ))) ≤ ∏ l ∈ KappaEndpoints.k2ends D j δ, σ ^ (-(3 : ℝ))`.

Rewrite using `[Finset.prod_const, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]`. Apply `Real.rpow_le_rpow_of_exponent_le h1` to reduce the goal to its premises. Establish `: ((KappaEndpoints.k2ends D j δ).card : ℝ) ≤ D.R.rS` using `by exact_mod_cast hc.trans hj`. Use the polynomial consequences of the given equalities and inequalities. Conclude with `step0.trans step1`.
-/
theorem sg_rpow_le (H1 : ℝ) {j : ℕ} (hj : j ≤ D.R.rS) (δ : ℕ → D.host.E) (τ : D.what₂.Tau) :
    KappaEndpoints.k2sg D H1 j δ τ ^ (-(3 * (D.R.rS : ℝ))) ≤
      ∏ l ∈ KappaEndpoints.k2ends D j δ,
        (max 1 (absReal D.host.rdE (embS D τ) D.R.rS l (δ l) / (2 * H1) ^ (2 * D.R.rS))) ^ (-(3 : ℝ)) := by
  set σ := KappaEndpoints.k2sg D H1 j δ τ with hσ
  have h1 : 1 ≤ σ := KappaEndpoints.one_le_minor_sigma H1 j δ τ
  have hle : ∀ l ∈ KappaEndpoints.k2ends D j δ,
      max 1 (absReal D.host.rdE (embS D τ) D.R.rS l (δ l) / (2 * H1) ^ (2 * D.R.rS)) ≤ σ := by
    intro l hl
    refine max_le h1 ?_
    rw [hσ]
    unfold KappaEndpoints.k2sg
    exact (Finset.le_fold_max _).2 (Or.inr ⟨l, hl, le_rfl⟩)
  have step1 : ∏ l ∈ KappaEndpoints.k2ends D j δ, σ ^ (-(3 : ℝ)) ≤
      ∏ l ∈ KappaEndpoints.k2ends D j δ,
        (max 1 (absReal D.host.rdE (embS D τ) D.R.rS l (δ l) / (2 * H1) ^ (2 * D.R.rS))) ^ (-(3 : ℝ)) := by
    apply Finset.prod_le_prod
    · intro l _; exact Real.rpow_nonneg (by linarith) _
    · intro l hl
      exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le one_pos (le_max_left _ _)) (hle l hl) (by norm_num)
  have hc := card_ends_le (D := D) j δ
  have step0 : σ ^ (-(3 * (D.R.rS : ℝ))) ≤ ∏ l ∈ KappaEndpoints.k2ends D j δ, σ ^ (-(3 : ℝ)) := by
    rw [Finset.prod_const, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    apply Real.rpow_le_rpow_of_exponent_le h1
    have : ((KappaEndpoints.k2ends D j δ).card : ℝ) ≤ D.R.rS := by exact_mod_cast hc.trans hj
    nlinarith
  exact step0.trans step1

end A

section B

variable {D : D7}

def wl (H1 : ℝ) (l : ℕ) (x : D.host.E) : ℝ :=
  ∏ τ : D.what₂.Tau, (max 1 (absReal D.host.rdE (embS D τ) D.R.rS l x / (2 * H1) ^ (2 * D.R.rS))) ^ (-(3 : ℝ))

/- English proof (translation)
The claim follows from `Finset.prod_nonneg (fun τ _ => Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _)`.
-/
theorem wl_nonneg (H1 : ℝ) (l : ℕ) (x : D.host.E) : 0 ≤ wl (D := D) H1 l x := Finset.prod_nonneg (fun τ _ => Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _)

/- English proof (translation)
Unfold `KappaEndpoints.k2S wl`. Rewrite using `[← Real.finsetProd_rpow _ _ (fun τ _ => le_trans zero_le_one (KappaEndpoints.one_le_minor_sigma H1 j δ τ)), Finset.prod_comm]`. Conclude with `Finset.prod_le_prod (fun τ _ => Real.rpow_nonneg (le_trans zero_le_one (KappaEndpoints.one_le_minor_sigma H1 j δ τ)) _) (fun τ _ => sg_rpow_le H1 hj δ τ)`.
-/
theorem S_rpow_le (H1 : ℝ) {j : ℕ} (hj : j ≤ D.R.rS) (δ : ℕ → D.host.E) :
    KappaEndpoints.k2S D H1 j δ ^ (-(3 * (D.R.rS : ℝ))) ≤ ∏ l ∈ KappaEndpoints.k2ends D j δ, wl (D := D) H1 l (δ l) := by
  unfold KappaEndpoints.k2S wl
  rw [← Real.finsetProd_rpow _ _ (fun τ _ => le_trans zero_le_one (KappaEndpoints.one_le_minor_sigma H1 j δ τ)), Finset.prod_comm]
  exact Finset.prod_le_prod (fun τ _ => Real.rpow_nonneg (le_trans zero_le_one (KappaEndpoints.one_le_minor_sigma H1 j δ τ)) _)
    (fun τ _ => sg_rpow_le H1 hj δ τ)

def Rl (H1 : ℝ) (l : ℕ) : ℝ := max 1 (D.host.rdE ^ ((2 * frameExp D.R.rS l : ℕ) : ℝ) * (2 * H1) ^ (2 * D.R.rS))

/- English proof (translation)
The claim follows from `le_max_left _ _`.
-/
theorem one_le_Rl (H1 : ℝ) (l : ℕ) : 1 ≤ Rl (D := D) H1 l := le_max_left _ _

/- English proof (translation)
Unfold `wl`. Use `Finset.prod_le_prod (fun τ _ => Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _) (fun τ _ => ?_)` and prove the remaining obligations. Apply `Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le one_pos (le_max_left _ _)) _ (by norm_num)` to reduce the goal to its premises. Apply `max_le_max le_rfl` to reduce the goal to its premises. Establish `hP : 0 < D.host.rdE ^ ((2 * frameExp D.R.rS l : ℕ) : ℝ) * (2 * H1) ^ (2 * D.R.rS)` using `mul_pos (Real.rpow_pos_of_pos hrd _) (pow_pos (by linarith) _)`.

Establish `e : absReal D.host.rdE (embS D τ) D.R.rS l x / (2 * H1) ^ (2 * D.R.rS) = ‖embS D τ x‖ / (D.host.rdE ^ ((2 * frameExp D.R.rS l : ℕ) : ℝ) * (2 * H1) ^ (2 * D.R.rS))`. Unfold `absReal`. Rewrite using `[Real.rpow_neg hrd.le]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[e]`. Conclude with `div_le_div_of_nonneg_left (norm_nonneg _) hP (le_max_right _ _)`.
-/
theorem wl_le (hrd : 0 < D.host.rdE) {H1 : ℝ} (hH : 0 < H1) (l : ℕ) (x : D.host.E) :
    wl (D := D) H1 l x ≤ ∏ τ : D.what₂.Tau, (max 1 (‖embS D τ x‖ / Rl (D := D) H1 l)) ^ (-(3 : ℝ)) := by
  unfold wl
  refine Finset.prod_le_prod (fun τ _ => Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _) (fun τ _ => ?_)
  apply Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le one_pos (le_max_left _ _)) _ (by norm_num)
  apply max_le_max le_rfl
  have hP : 0 < D.host.rdE ^ ((2 * frameExp D.R.rS l : ℕ) : ℝ) * (2 * H1) ^ (2 * D.R.rS) :=
    mul_pos (Real.rpow_pos_of_pos hrd _) (pow_pos (by linarith) _)
  have e : absReal D.host.rdE (embS D τ) D.R.rS l x / (2 * H1) ^ (2 * D.R.rS) =
      ‖embS D τ x‖ / (D.host.rdE ^ ((2 * frameExp D.R.rS l : ℕ) : ℝ) * (2 * H1) ^ (2 * D.R.rS)) := by
    unfold absReal
    rw [Real.rpow_neg hrd.le]
    push_cast
    field_simp
  rw [e]
  exact div_le_div_of_nonneg_left (norm_nonneg _) hP (le_max_right _ _)

/- English proof (translation)
Use `set vec : D.host.E → D.what₂.Tau → ℂ := fun x τ => embS D τ x with hvec`. Establish `hinj : Set.InjOn vec A`. Introduce `x _ y _ hxy`. Take `⟨τ⟩` from `(inferInstance : Nonempty D.what₂.Tau)`. Conclude with `(embS D τ).injective (congrFun hxy τ)`.

Establish `hsum : ∑ x ∈ A, ∏ τ : D.what₂.Tau, (max 1 (‖embS D τ x‖ / R)) ^ (-(3 : ℝ)) = ∑ p ∈ A.image vec, ∏ τ : D.what₂.Tau, (max 1 (‖p τ‖ / R)) ^ (-(3 : ℝ))`. Rewrite using `[Finset.sum_image hinj]`. Rewrite using `[hsum]`. Apply `hLS D.what₂.Tau (A.image vec) R hR` to reduce the goal to its premises. Introduce `p hp q hq hpq`.

Take `⟨x, hx, rfl⟩` from `Finset.mem_image.1 hp`. Take `⟨y, hy, rfl⟩` from `Finset.mem_image.1 hq`. Establish `hxy : x - y ≠ 0` using `sub_ne_zero.2 (fun h => hpq (by rw [h]))`. Establish `h` using `hNT D (x - y) ((hA x hx).sub (hA y hy)) hxy`. Establish `e : ∏ τ : D.what₂.Tau, ‖embS D τ (x - y)‖ ^ 2 = (∏ τ : D.what₂.Tau, ‖vec x τ - vec y τ‖) ^ 2`.

Rewrite using `[← Finset.prod_pow]`. Simplify using `[hvec, map_sub]`. Rewrite `h` using `[e]`. Establish `h0 : 0 ≤ ∏ τ : D.what₂.Tau, ‖vec x τ - vec y τ‖` using `Finset.prod_nonneg fun τ _ => norm_nonneg _`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem sum_one_coord (hNT : KTwoMinorIntegrality.NormLB) (hLS : KTwoMinorIntegrality.LatSum) [Nonempty D.what₂.Tau] (A : Finset D.host.E)
    (hA : ∀ x ∈ A, IsIntegral ℤ x) {R : ℝ} (hR : 1 ≤ R) :
    ∑ x ∈ A, ∏ τ : D.what₂.Tau, (max 1 (‖embS D τ x‖ / R)) ^ (-(3 : ℝ)) ≤ (64 * R) ^ (2 * Fintype.card D.what₂.Tau) := by
  classical
  set vec : D.host.E → D.what₂.Tau → ℂ := fun x τ => embS D τ x with hvec
  have hinj : Set.InjOn vec A := by
    intro x _ y _ hxy
    obtain ⟨τ⟩ := (inferInstance : Nonempty D.what₂.Tau)
    exact (embS D τ).injective (congrFun hxy τ)
  have hsum : ∑ x ∈ A, ∏ τ : D.what₂.Tau, (max 1 (‖embS D τ x‖ / R)) ^ (-(3 : ℝ)) =
      ∑ p ∈ A.image vec, ∏ τ : D.what₂.Tau, (max 1 (‖p τ‖ / R)) ^ (-(3 : ℝ)) := by
    rw [Finset.sum_image hinj]
  rw [hsum]
  apply hLS D.what₂.Tau (A.image vec) R hR
  intro p hp q hq hpq
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hp
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hq
  have hxy : x - y ≠ 0 := sub_ne_zero.2 (fun h => hpq (by rw [h]))
  have h := hNT D (x - y) ((hA x hx).sub (hA y hy)) hxy
  have e : ∏ τ : D.what₂.Tau, ‖embS D τ (x - y)‖ ^ 2 = (∏ τ : D.what₂.Tau, ‖vec x τ - vec y τ‖) ^ 2 := by
    rw [← Finset.prod_pow]
    simp [hvec, map_sub]
  rw [e] at h
  have h0 : 0 ≤ ∏ τ : D.what₂.Tau, ‖vec x τ - vec y τ‖ := Finset.prod_nonneg fun τ _ => norm_nonneg _
  nlinarith

end B

section C

/- English proof (translation)
Rewrite using `[Finset.prod_sum]`. Set `φ : (ι → α) → (∀ i ∈ S, α)` to `fun δ i _ => δ i`. Establish `hφinj : ∀ δ ∈ T, ∀ δ' ∈ T, φ δ = φ δ' → δ = δ'` using `fun δ hδ δ' hδ' h => hinj δ hδ δ' hδ' (fun i hi => congrFun (congrFun h i) hi)`. Establish `hsub : T.image φ ⊆ S.pi (fun i => T.image (fun δ => δ i))`. Introduce `x hx`.

Take `⟨δ, hδ, rfl⟩` from `Finset.mem_image.mp hx`. Conclude with `Finset.mem_pi.mpr (fun i _ => Finset.mem_image_of_mem _ hδ)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_image hφinj]`. Use `Finset.sum_congr rfl (fun δ _ => ?_)` and prove the remaining obligations.

Conclude with `(Finset.prod_attach S (fun i => g i (δ i))).symm`. Use `_ ≤ ∑ x ∈ S.pi (fun i => T.image (fun δ => δ i)), ∏ i ∈ S.attach, g i (x i i.2) := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => Finset.prod_nonneg (fun i _ => hg _ _))`.
-/
theorem sum_prod_le {ι α : Type*} [DecidableEq ι] [DecidableEq α] (S : Finset ι) (T : Finset (ι → α)) (g : ι → α → ℝ)
    (hg : ∀ i a, 0 ≤ g i a) (hinj : ∀ δ ∈ T, ∀ δ' ∈ T, (∀ i ∈ S, δ i = δ' i) → δ = δ') :
    ∑ δ ∈ T, ∏ i ∈ S, g i (δ i) ≤ ∏ i ∈ S, ∑ a ∈ T.image (fun δ => δ i), g i a := by
  classical
  rw [Finset.prod_sum]
  let φ : (ι → α) → (∀ i ∈ S, α) := fun δ i _ => δ i
  have hφinj : ∀ δ ∈ T, ∀ δ' ∈ T, φ δ = φ δ' → δ = δ' := fun δ hδ δ' hδ' h =>
    hinj δ hδ δ' hδ' (fun i hi => congrFun (congrFun h i) hi)
  have hsub : T.image φ ⊆ S.pi (fun i => T.image (fun δ => δ i)) := by
    intro x hx
    obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_pi.mpr (fun i _ => Finset.mem_image_of_mem _ hδ)
  calc ∑ δ ∈ T, ∏ i ∈ S, g i (δ i)
      = ∑ x ∈ T.image φ, ∏ i ∈ S.attach, g i (x i i.2) := by
        rw [Finset.sum_image hφinj]
        refine Finset.sum_congr rfl (fun δ _ => ?_)
        exact (Finset.prod_attach S (fun i => g i (δ i))).symm
    _ ≤ ∑ x ∈ S.pi (fun i => T.image (fun δ => δ i)), ∏ i ∈ S.attach, g i (x i i.2) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun x _ _ => Finset.prod_nonneg (fun i _ => hg _ _))

end C

section Dsum

variable {D : D7}

/- English proof (translation)
Unfold `leadMinorE`. Simplify using the standard rewrite rules.
-/
theorem leadMinorE_zero {N : ℕ} (A : Matrix (Fin N) (Fin N) D.host.E) : leadMinorE A 0 = 1 := by
  unfold leadMinorE
  simp

/- English proof (translation)
Use `⟨fun l => ?_, fun l hl => ?_, ?_⟩` and prove the remaining obligations. Unfold `KappaEndpoints.k2lab split_ifs with h`. Conclude with `hMI D X u t (hT.1 t) l (by omega)`. Conclude with `isIntegral_zero`. Unfold `KappaEndpoints.k2lab`.

Rewrite using `[if_neg (by omega)]`. Unfold `KappaEndpoints.k2lab`. Rewrite using `[if_pos (Nat.zero_le _)]`. Conclude with `leadMinorE_zero _`.
-/
theorem lab_facts (hMI : KTwoMinorIntegrality.MinorInt) (X : TermTie D) {u : D.what₂.Word} (hT : LatticeIndexAndWeightTheory.TieOK X u)
    (t : D.s.Term u u) {j : ℕ} (hj : j ≤ D.R.rS) (htj : LatticeIndexAndWeightTheory.jOf X t = j) :
    (∀ l, IsIntegral ℤ (KappaEndpoints.k2lab X t l)) ∧ (∀ l, j < l → KappaEndpoints.k2lab X t l = 0) ∧
      KappaEndpoints.k2lab X t 0 = 1 := by
  refine ⟨fun l => ?_, fun l hl => ?_, ?_⟩
  · unfold KappaEndpoints.k2lab
    split_ifs with h
    · exact hMI D X u t (hT.1 t) l (by omega)
    · exact isIntegral_zero
  · unfold KappaEndpoints.k2lab
    rw [if_neg (by omega)]
  · unfold KappaEndpoints.k2lab
    rw [if_pos (Nat.zero_le _)]
    exact leadMinorE_zero _

/- English proof (translation)
Establish `hfact : ∀ δ ∈ T, (∀ l, IsIntegral ℤ (δ l)) ∧ (∀ l, j < l → δ l = 0) ∧ δ 0 = 1`. Introduce `δ hδ`. Take `⟨t, -, htj, rfl⟩` from `hTm δ hδ`. Conclude with `lab_facts hMI X hT t hj htj`. Use `set K : ℝ := ∏ l ∈ Finset.Icc 1 j, (64 * Rl (D := D) H1 l) ^ (2 * Fintype.card D.what₂.Tau) with hK`.

Establish `hmaps : ∀ δ ∈ T, KappaEndpoints.k2ends D j δ ∈ (Finset.Icc 1 j).powerset`. Introduce `δ _`. Rewrite using `[Finset.mem_powerset]`. Unfold `KappaEndpoints.k2ends`. Conclude with `Finset.filter_subset _ _`.

Rewrite using `[← Finset.sum_fiberwise_of_maps_to hmaps]`. Establish `hS : ∀ S ∈ (Finset.Icc 1 j).powerset, ∑ δ ∈ T with KappaEndpoints.k2ends D j δ = S, KappaEndpoints.k2S D H1 j δ ^ (-(3 * (D.R.rS : ℝ))) ≤ K`. Introduce `S hSm`. Establish `hSsub` using `Finset.mem_powerset.1 hSm`. Use `set TS := T.filter (fun δ => KappaEndpoints.k2ends D j δ = S) with hTS`.

Establish `step1 : ∑ δ ∈ TS, KappaEndpoints.k2S D H1 j δ ^ (-(3 * (D.R.rS : ℝ))) ≤ ∑ δ ∈ TS, ∏ l ∈ S, wl (D` using `D) H1 l (δ l) := by`. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `δ hδ`. Establish `he` using `(Finset.mem_filter.1 hδ).2`. Use `S_rpow_le (D := D) H1 hj δ` as an intermediate fact.

Rewrite `this` using `[he]`. Then use the resulting hypothesis. Establish `hinj : ∀ δ ∈ TS, ∀ δ' ∈ TS, (∀ l ∈ S, δ l = δ' l) → δ = δ'`. Introduce `δ hδ δ' hδ' h`. Take `⟨hδT, he⟩` from `Finset.mem_filter.1 hδ`. Take `⟨hδT', he'⟩` from `Finset.mem_filter.1 hδ'`.

Take `⟨-, hz, h0⟩` from `hfact δ hδT`. Take `⟨-, hz', h0'⟩` from `hfact δ' hδT'`. Use function extensionality and compare the values at `l`. Distinguish the cases in `hl0 : l = 0`. Rewrite using `[hl0, h0, h0']`.

Distinguish the cases in `hlj : j < l`. Rewrite using `[hz l hlj, hz' l hlj]`. Distinguish the cases in `hlS : l ∈ S`. Conclude with `h l hlS`. Establish `hI : l ∈ Finset.Icc 1 j` using `Finset.mem_Icc.2 ⟨by omega, by omega⟩`.

Establish `a1 : δ l = 0`. Assume the negation of the conclusion as `hne`. Apply `hlS` to reduce the goal to its premises. Rewrite using `[← he]`. Unfold `KappaEndpoints.k2ends`.

Conclude with `Finset.mem_filter.2 ⟨hI, hne⟩`. Establish `a2 : δ' l = 0`. Assume the negation of the conclusion as `hne`. Apply `hlS` to reduce the goal to its premises. Rewrite using `[← he']`.

Unfold `KappaEndpoints.k2ends`. Conclude with `Finset.mem_filter.2 ⟨hI, hne⟩`. Rewrite using `[a1, a2]`. Establish `step2` using `sum_prod_le S TS (fun l x => wl (D := D) H1 l x) (fun l x => wl_nonneg H1 l x) hinj`. Establish `step3 : ∏ l ∈ S, ∑ x ∈ TS.image (fun δ => δ l), wl (D` using `D) H1 l x ≤ ∏ l ∈ S, (64 * Rl (D := D) H1 l) ^ (2 * Fintype.card D.what₂.Tau) := by`.

Apply `Finset.prod_le_prod` to reduce the goal to its premises. Introduce `l _`. Conclude with `Finset.sum_nonneg fun x _ => wl_nonneg H1 l x`. Introduce `l _`. Establish `hint : ∀ x ∈ TS.image (fun δ => δ l), IsIntegral ℤ x`.

Introduce `x hx`. Take `⟨δ, hδ, rfl⟩` from `Finset.mem_image.1 hx`. Conclude with `(hfact δ (Finset.mem_filter.1 hδ).1).1 l`. Combine the equalities or inequalities in the displayed calculation. Establish `step4 : ∏ l ∈ S, (64 * Rl (D` using `D) H1 l) ^ (2 * Fintype.card D.what₂.Tau) ≤ K := by`.

Rewrite using `[hK, ← Finset.prod_sdiff hSsub]`. Establish `hge : ∀ l, 1 ≤ (64 * Rl (D` using `D) H1 l) ^ (2 * Fintype.card D.what₂.Tau) := fun l => one_le_pow₀ (by linarith [one_le_Rl (D := D) H1 l])`. Establish `h1 : 1 ≤ ∏ l ∈ Finset.Icc 1 j \ S, (64 * Rl (D` using `D) H1 l) ^ (2 * Fintype.card D.what₂.Tau) := Finset.prod_induction _ (fun x => 1 ≤ x) (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb) le_rfl (fun l _ => hge l)`. Establish `h0 : 0 ≤ ∏ l ∈ S, (64 * Rl (D` using `D) H1 l) ^ (2 * Fintype.card D.what₂.Tau) := Finset.prod_nonneg fun l _ => le_trans zero_le_one (hge l)`. Use the polynomial consequences of the given equalities and inequalities.

Conclude with `step1.trans (step2.trans (step3.trans step4))`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_const, Finset.card_powerset, nsmul_eq_mul]`. Simplify using the standard rewrite rules.
-/
theorem cosets_sum (hNT : KTwoMinorIntegrality.NormLB) (hLS : KTwoMinorIntegrality.LatSum) (hMI : KTwoMinorIntegrality.MinorInt)
    [Nonempty D.what₂.Tau] (hrd : 0 < D.host.rdE) (X : TermTie D) {u : D.what₂.Word} (hT : LatticeIndexAndWeightTheory.TieOK X u) {H1 : ℝ}
    (hH : 0 < H1) {j : ℕ} (hj : j ≤ D.R.rS) (T : Finset (ℕ → D.host.E))
    (hTm : ∀ δ ∈ T, ∃ t : D.s.Term u u, LatticeIndexAndWeightTheory.IsInertiaCyclotomicGeneratorElement t ∧ LatticeIndexAndWeightTheory.jOf X t = j ∧ KappaEndpoints.k2lab X t = δ) :
    ∑ δ ∈ T, KappaEndpoints.k2S D H1 j δ ^ (-(3 * (D.R.rS : ℝ))) ≤
      2 ^ j * ∏ l ∈ Finset.Icc 1 j, (64 * Rl (D := D) H1 l) ^ (2 * Fintype.card D.what₂.Tau) := by
  classical
  have hfact : ∀ δ ∈ T, (∀ l, IsIntegral ℤ (δ l)) ∧ (∀ l, j < l → δ l = 0) ∧ δ 0 = 1 := by
    intro δ hδ
    obtain ⟨t, -, htj, rfl⟩ := hTm δ hδ
    exact lab_facts hMI X hT t hj htj
  set K : ℝ := ∏ l ∈ Finset.Icc 1 j, (64 * Rl (D := D) H1 l) ^ (2 * Fintype.card D.what₂.Tau) with hK
  have hmaps : ∀ δ ∈ T, KappaEndpoints.k2ends D j δ ∈ (Finset.Icc 1 j).powerset := by
    intro δ _
    rw [Finset.mem_powerset]
    unfold KappaEndpoints.k2ends
    exact Finset.filter_subset _ _
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hS : ∀ S ∈ (Finset.Icc 1 j).powerset,
      ∑ δ ∈ T with KappaEndpoints.k2ends D j δ = S, KappaEndpoints.k2S D H1 j δ ^ (-(3 * (D.R.rS : ℝ))) ≤ K := by
    intro S hSm
    have hSsub := Finset.mem_powerset.1 hSm
    set TS := T.filter (fun δ => KappaEndpoints.k2ends D j δ = S) with hTS
    have step1 : ∑ δ ∈ TS, KappaEndpoints.k2S D H1 j δ ^ (-(3 * (D.R.rS : ℝ))) ≤
        ∑ δ ∈ TS, ∏ l ∈ S, wl (D := D) H1 l (δ l) := by
      apply Finset.sum_le_sum
      intro δ hδ
      have he := (Finset.mem_filter.1 hδ).2
      have := S_rpow_le (D := D) H1 hj δ
      rwa [he] at this
    have hinj : ∀ δ ∈ TS, ∀ δ' ∈ TS, (∀ l ∈ S, δ l = δ' l) → δ = δ' := by
      intro δ hδ δ' hδ' h
      obtain ⟨hδT, he⟩ := Finset.mem_filter.1 hδ
      obtain ⟨hδT', he'⟩ := Finset.mem_filter.1 hδ'
      obtain ⟨-, hz, h0⟩ := hfact δ hδT
      obtain ⟨-, hz', h0'⟩ := hfact δ' hδT'
      funext l
      by_cases hl0 : l = 0
      · rw [hl0, h0, h0']
      by_cases hlj : j < l
      · rw [hz l hlj, hz' l hlj]
      by_cases hlS : l ∈ S
      · exact h l hlS
      have hI : l ∈ Finset.Icc 1 j := Finset.mem_Icc.2 ⟨by omega, by omega⟩
      have a1 : δ l = 0 := by
        by_contra hne
        apply hlS
        rw [← he]
        unfold KappaEndpoints.k2ends
        exact Finset.mem_filter.2 ⟨hI, hne⟩
      have a2 : δ' l = 0 := by
        by_contra hne
        apply hlS
        rw [← he']
        unfold KappaEndpoints.k2ends
        exact Finset.mem_filter.2 ⟨hI, hne⟩
      rw [a1, a2]
    have step2 := sum_prod_le S TS (fun l x => wl (D := D) H1 l x) (fun l x => wl_nonneg H1 l x) hinj
    have step3 : ∏ l ∈ S, ∑ x ∈ TS.image (fun δ => δ l), wl (D := D) H1 l x ≤
        ∏ l ∈ S, (64 * Rl (D := D) H1 l) ^ (2 * Fintype.card D.what₂.Tau) := by
      apply Finset.prod_le_prod
      · intro l _; exact Finset.sum_nonneg fun x _ => wl_nonneg H1 l x
      · intro l _
        have hint : ∀ x ∈ TS.image (fun δ => δ l), IsIntegral ℤ x := by
          intro x hx
          obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.1 hx
          exact (hfact δ (Finset.mem_filter.1 hδ).1).1 l
        calc ∑ x ∈ TS.image (fun δ => δ l), wl (D := D) H1 l x
            ≤ ∑ x ∈ TS.image (fun δ => δ l), ∏ τ : D.what₂.Tau, (max 1 (‖embS D τ x‖ / Rl (D := D) H1 l)) ^ (-(3 : ℝ)) :=
              Finset.sum_le_sum fun x _ => wl_le hrd hH l x
          _ ≤ _ := sum_one_coord hNT hLS _ hint (one_le_Rl H1 l)
    have step4 : ∏ l ∈ S, (64 * Rl (D := D) H1 l) ^ (2 * Fintype.card D.what₂.Tau) ≤ K := by
      rw [hK, ← Finset.prod_sdiff hSsub]
      have hge : ∀ l, 1 ≤ (64 * Rl (D := D) H1 l) ^ (2 * Fintype.card D.what₂.Tau) :=
        fun l => one_le_pow₀ (by linarith [one_le_Rl (D := D) H1 l])
      have h1 : 1 ≤ ∏ l ∈ Finset.Icc 1 j \ S, (64 * Rl (D := D) H1 l) ^ (2 * Fintype.card D.what₂.Tau) :=
        Finset.prod_induction _ (fun x => 1 ≤ x) (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb) le_rfl
          (fun l _ => hge l)
      have h0 : 0 ≤ ∏ l ∈ S, (64 * Rl (D := D) H1 l) ^ (2 * Fintype.card D.what₂.Tau) :=
        Finset.prod_nonneg fun l _ => le_trans zero_le_one (hge l)
      nlinarith
    exact step1.trans (step2.trans (step3.trans step4))
  calc _ ≤ ∑ S ∈ (Finset.Icc 1 j).powerset, K := Finset.sum_le_sum hS
    _ = 2 ^ j * K := by
      rw [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul]
      simp

end Dsum

end Formalism.MainNotions.KTwoCosetCount

end
