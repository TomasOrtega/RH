import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.HarishChandraDescent.Restrict
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary

noncomputable section

open Finset Matrix
open scoped InnerProductSpace

namespace PositivityTheory.RgHe3

open ReciprocityTheory.ChartRestriction.DS PositivityTheory.UnitaryDecomposition PositivityTheory.RgHe

namespace trialData

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Rewrite using `[sum_image (fun a _ b _ h => hι h)]`. Use `sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[sum_image (fun a _ b _ h => hι h)]`. Use `_ ≤ ∑ x ∈ univ.image ι, ∑ y, f x y := sum_le_sum fun x _ => sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun y _ _ => hf x y)`.

Use `_ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun x _ _ => sum_nonneg fun y _ => hf x y)`.
-/
theorem sum_emb_le {m k : ℕ} (ι : Fin m → Fin k) (hι : Function.Injective ι) (f : Fin k → Fin k → ℝ)
    (hf : ∀ a b, 0 ≤ f a b) : ∑ a, ∑ b, f (ι a) (ι b) ≤ ∑ a, ∑ b, f a b := by
  calc ∑ a, ∑ b, f (ι a) (ι b) = ∑ x ∈ univ.image ι, ∑ y ∈ univ.image ι, f x y := by
        rw [sum_image (fun a _ b _ h => hι h)]
        refine sum_congr rfl fun a _ => ?_
        rw [sum_image (fun a _ b _ h => hι h)]
    _ ≤ ∑ x ∈ univ.image ι, ∑ y, f x y :=
        sum_le_sum fun x _ => sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun y _ _ => hf x y)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _)
        (fun x _ _ => sum_nonneg fun y _ => hf x y)

/- English proof (translation)
Establish `h` using `norm_sub_le p q`. Establish `h0` using `norm_nonneg (p - q)`. Use polynomial arithmetic with `[norm_nonneg p, norm_nonneg q, sq_nonneg (‖p‖ - ‖q‖)]`.
-/
theorem norm_sub_sq_le {V : Type} [SeminormedAddCommGroup V] (p q : V) :
    ‖p - q‖ ^ 2 ≤ 2 * ‖p‖ ^ 2 + 2 * ‖q‖ ^ 2 := by
  have h := norm_sub_le p q
  have h0 := norm_nonneg (p - q)
  nlinarith [norm_nonneg p, norm_nonneg q, sq_nonneg (‖p‖ - ‖q‖)]

/- English proof (translation)
Establish `e1 : Q (I (η - w)) - c • I (η - w) = I ((P η - c • η) - (P w - c • w))`. Rewrite using `[← hPQ, ← map_smul, ← map_sub]`. Use `congr 1`. Rewrite using `[map_sub, smul_sub]`. Normalize the expressions using the abelian group laws.

Rewrite using `[e1, hI]`. Establish `h1` using `norm_sub_sq_le (P η - c • η) (P w - c • w)`. Establish `h2` using `norm_sub_sq_le (P w) (c • w)`. Rewrite `h2` using `[norm_smul, mul_pow]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem term_le {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] (I : V →ₗ[ℂ] W) (hI : ∀ z, ‖I z‖ = ‖z‖) (P : V →ₗ[ℂ] V) (Q : W →ₗ[ℂ] W)
    (hPQ : ∀ z, I (P z) = Q (I z)) (c : ℂ) (η w : V) :
    ‖Q (I (η - w)) - c • I (η - w)‖ ^ 2 ≤ 2 * ‖P η - c • η‖ ^ 2 + 4 * ‖P w‖ ^ 2 + 4 * (‖c‖ ^ 2 * ‖w‖ ^ 2) := by
  have e1 : Q (I (η - w)) - c • I (η - w) = I ((P η - c • η) - (P w - c • w)) := by
    rw [← hPQ, ← map_smul, ← map_sub]
    congr 1
    rw [map_sub, smul_sub]
    abel
  rw [e1, hI]
  have h1 := norm_sub_sq_le (P η - c • η) (P w - c • w)
  have h2 := norm_sub_sq_le (P w) (c • w)
  rw [norm_smul, mul_pow] at h2
  linarith

end trialData

open trialData in
/- English proof (translation)
Introduce `hDS hMom hApp hRes`. Unfold `DSData ForRep at hDS`. Unfold `Approx ForAlg at hApp`. Unfold `Mom2 at hMom`. Unfold `Restrict at hRes`.

Unfold `Trial`. Introduce `n ε ε' e lam d d' g hFits hOver`. Take `⟨C0, hC0, hM⟩` from `hMom n ε e lam d d' g hOver`. Use `⟨8 * C0 + 8, by linarith, ?_⟩` and prove the remaining obligations. Introduce `t ht hHC hGap H _ _ _ π hIsDS`.

Establish `hU : IsURepOn (UJset ε) π` using `hIsDS.2.2.1`. Take `⟨hU', I, hIc, hIE⟩` from `hRes n ε ε' e H π hFits hU`. Establish `key : ∀ N : ℝ, 1 ≤ N → N ^ 3 + 2 * N + 1 < 200 * N ^ 3`. Introduce `N h1`. Establish `h2 : 1 ≤ N ^ 2` using `by nlinarith`.

Establish `h3 : N ≤ N ^ 3` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities. Establish `hgap : ((n + 1 : ℕ) : ℝ) ^ 3 + 2 * ((n + 1 : ℕ) : ℝ) + 1 < 200 * ((n : ℝ) + 1) ^ 3`. Use `push_cast`. Conclude with `key _ (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])`.

Take `⟨hcas, ⟨v, hv1, hvK⟩, hdense⟩` from `hDS (n + 1) ε H π hU (lam + t • d) (200 * ((n : ℝ) + 1) ^ 3) hHC hGap hgap hIsDS`. Take `⟨η, hη1, hηb⟩` from `hM t ht H π hU v hv1 hvK (hcas v)`. Establish `hDer` using `isDerivedOn_smE hU`. Establish `hG` using `hDer.glRep`. Establish `hUn` using `isInfUnitary_of_isDerivedOn hU hDer`.

Take `⟨K, hKdef⟩ : ∃ K, ‖(2 : ℂ) • casimirK ε (smE ε π) η - ((casVal (lam + t • d) : ℝ) : ℂ) • η‖ = K` from `⟨_, rfl⟩`. Establish `hK0 : 0 ≤ K` using `hKdef ▸ norm_nonneg _`. Take `⟨S, hSdef⟩ : ∃ S, ∑ a : Fin n, ∑ b : Fin n, ‖(if a = b then ((t * d' a : ℝ) : ℂ) else 0)‖ ^ 2 = S` from `⟨_, rfl⟩`. Establish `hS0 : 0 ≤ S` using `hSdef ▸ sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _`. Establish `ht0 : 0 < t` using `by linarith`.

Take `⟨δ, hδdef⟩ : ∃ δ : ℝ, min (1 / 2 : ℝ) (min (t / (4 * K + 1)) (t / (4 * S + 1))) = δ` from `⟨_, rfl⟩`. Establish `hδpos : 0 < δ` using `hδdef ▸ lt_min (by norm_num) (lt_min (div_pos ht0 (by linarith)) (div_pos ht0 (by linarith)))`. Establish `hδ1 : δ ≤ 1 / 2` using `hδdef ▸ min_le_left _ _`. Establish `hδK : δ ≤ t / (4 * K + 1)` using `hδdef ▸ (min_le_right _ _).trans (min_le_left _ _)`. Establish `hδS : δ ≤ t / (4 * S + 1)` using `hδdef ▸ (min_le_right _ _).trans (min_le_right _ _)`.

Take `⟨f, ⟨F, hFfd, hFst, hfF⟩, hf⟩` from `hdense (η : H) δ hδpos`. Take `⟨η', hη'F, hdist, hsum⟩` from `hApp (n + 1) ε (smD ε π) (smE ε π) hG hUn (casVal (lam + t • d)) hcas F hFfd hFst η f hfF`. Take `⟨w, rfl⟩ : ∃ w, η' = η - w` from `⟨η - η', (sub_sub_cancel η η').symm⟩`. Rewrite `hdist`, `hsum` using `[sub_sub_cancel]`. Use `replace hsum : ∑ a, ∑ b, ‖smE ε π a b w‖ ^ 2 ≤ K * ‖η - f‖ := hsum.trans_eq (by subst hKdef; rfl)`.

Establish `hηf : ‖η - f‖ < δ` using `hf`. Establish `hw : ‖w‖ < δ` using `lt_of_le_of_lt hdist hηf`. Establish `hKb : K * ‖η - f‖ ≤ t / 4`. Establish `h1 : K * ‖η - f‖ ≤ K * (t / (4 * K + 1))` using `mul_le_mul_of_nonneg_left (hηf.le.trans hδK) hK0`. Establish `h2 : K * (t / (4 * K + 1)) ≤ t / 4`.

Rewrite using `[mul_div_assoc', div_le_div_iff₀ (by linarith) (by norm_num)]`. Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hSb : S * ‖w‖ ^ 2 ≤ t / 4`. Establish `h0` using `norm_nonneg w`.

Establish `e1 : ‖w‖ ^ 2 ≤ δ ^ 2` using `pow_le_pow_left₀ h0 hw.le 2`. Establish `e2 : δ ^ 2 ≤ δ` using `by nlinarith`. Establish `h1 : S * ‖w‖ ^ 2 ≤ S * (t / (4 * S + 1))` using `mul_le_mul_of_nonneg_left (by linarith) hS0`. Establish `h2 : S * (t / (4 * S + 1)) ≤ t / 4`. Rewrite using `[mul_div_assoc', div_le_div_iff₀ (by linarith) (by norm_num)]`.

Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hI : ∀ z, ‖I z‖ = ‖z‖` using `fun z => congrArg (‖·‖) (hIc z)`. Establish `hn' : 1 / 2 ≤ ‖η - w‖`. Use `norm_sub_norm_le η (η - w)` as an intermediate fact.

Rewrite `this` using `[sub_sub_cancel]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨hU', ?_, I (η - w), ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Metric.dense_iff]`. Introduce `y r hr`.

Take `⟨f2, -, hf2⟩` from `hdense y r hr`. Use `⟨(I f2 : H), ?_, (I f2).2⟩` and prove the remaining obligations. Rewrite using `[Metric.mem_ball, dist_comm, dist_eq_norm, hIc]`. Conclude with `hf2`. Introduce `h0`.

Use `hI (η - w)` as an intermediate fact. Rewrite `this` using `[h0, norm_zero]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨F.map I, by haveI := hFfd; infer_instance, ?_, Submodule.mem_map_of_mem hη'F⟩` and prove the remaining obligations. Introduce `a b hab y hy`.

Take `⟨z, hz, rfl⟩` from `Submodule.mem_map.mp hy`. Rewrite using `[← hIE a b z]`. Conclude with `Submodule.mem_map_of_mem (hFst _ _ (by rw [hFits.2 a, hFits.2 b]; exact hab) z hz)`. Unfold `qf`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`.

Establish `hB` using `sum_emb_le (fun a => e (Sum.inl a)) (e.injective.comp Sum.inl_injective) (fun a b => ‖smE ε π a b w‖ ^ 2) (fun _ _ => sq_nonneg _)`. Establish `hT : ∑ a : Fin n, ∑ b : Fin n, ‖smE ε' (res e π) a b (I (η - w)) - (if a = b then ((t * d' a : ℝ) : ℂ) else 0) • I (η - w)‖ ^ 2 ≤ ∑ a : Fin n, ∑ b : Fin n, (2 * ‖smE ε π (e (Sum.inl a)) (e (Sum.inl b)) η - (if a = b then ((t * d' a : ℝ) : ℂ) else 0) • η‖ ^ 2 + 4 * ‖smE ε π (e (Su …` using `sum_le_sum fun a _ => sum_le_sum fun b _ => term_le I hI _ _ (hIE a b) _ η w`. Establish `hsplit : ∑ a : Fin n, ∑ b : Fin n, (2 * ‖smE ε π (e (Sum.inl a)) (e (Sum.inl b)) η - (if a = b then ((t * d' a : ℝ) : ℂ) else 0) • η‖ ^ 2 + 4 * ‖smE ε π (e (Sum.inl a)) (e (Sum.inl b)) w‖ ^ 2 + 4 * (‖(if a = b then ((t * d' a : ℝ) : ℂ) else 0)‖ ^ 2 * ‖w‖ ^ 2)) = 2 * ∑ a : Fin n, …`. Simplify using `only [sum_add_distrib, mul_sum, sum_mul]`. Rewrite `hT` using `[hsplit, hSdef]`.

Establish `hx2 : 1 / 4 ≤ ‖I (η - w)‖ ^ 2`. Rewrite using `[hI]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hfin` using `mul_le_mul_of_nonneg_left hx2 (by positivity : (0 : ℝ) ≤ (8 * C0 + 8) * t)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem trial_of_inputs : DSData → Mom2 → Approx → Restrict → Trial := by
  intro hDS hMom hApp hRes
  unfold DSData ForRep at hDS
  unfold Approx ForAlg at hApp
  unfold Mom2 at hMom
  unfold Restrict at hRes
  unfold Trial
  intro n ε ε' e lam d d' g hFits hOver
  obtain ⟨C0, hC0, hM⟩ := hMom n ε e lam d d' g hOver
  refine ⟨8 * C0 + 8, by linarith, ?_⟩
  intro t ht hHC hGap H _ _ _ π hIsDS
  have hU : IsURepOn (UJset ε) π := hIsDS.2.2.1
  obtain ⟨hU', I, hIc, hIE⟩ := hRes n ε ε' e H π hFits hU
  have key : ∀ N : ℝ, 1 ≤ N → N ^ 3 + 2 * N + 1 < 200 * N ^ 3 := by
    intro N h1
    have h2 : 1 ≤ N ^ 2 := by nlinarith
    have h3 : N ≤ N ^ 3 := by nlinarith
    nlinarith
  have hgap : ((n + 1 : ℕ) : ℝ) ^ 3 + 2 * ((n + 1 : ℕ) : ℝ) + 1 < 200 * ((n : ℝ) + 1) ^ 3 := by
    push_cast
    exact key _ (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  obtain ⟨hcas, ⟨v, hv1, hvK⟩, hdense⟩ :=
    hDS (n + 1) ε H π hU (lam + t • d) (200 * ((n : ℝ) + 1) ^ 3) hHC hGap hgap hIsDS
  obtain ⟨η, hη1, hηb⟩ := hM t ht H π hU v hv1 hvK (hcas v)
  have hDer := isDerivedOn_smE hU
  have hG := hDer.glRep
  have hUn := isInfUnitary_of_isDerivedOn hU hDer
  obtain ⟨K, hKdef⟩ : ∃ K, ‖(2 : ℂ) • casimirK ε (smE ε π) η - ((casVal (lam + t • d) : ℝ) : ℂ) • η‖ = K :=
    ⟨_, rfl⟩
  have hK0 : 0 ≤ K := hKdef ▸ norm_nonneg _
  obtain ⟨S, hSdef⟩ : ∃ S, ∑ a : Fin n, ∑ b : Fin n,
      ‖(if a = b then ((t * d' a : ℝ) : ℂ) else 0)‖ ^ 2 = S := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := hSdef ▸ sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _
  have ht0 : 0 < t := by linarith
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, min (1 / 2 : ℝ) (min (t / (4 * K + 1)) (t / (4 * S + 1))) = δ :=
    ⟨_, rfl⟩
  have hδpos : 0 < δ := hδdef ▸ lt_min (by norm_num)
    (lt_min (div_pos ht0 (by linarith)) (div_pos ht0 (by linarith)))
  have hδ1 : δ ≤ 1 / 2 := hδdef ▸ min_le_left _ _
  have hδK : δ ≤ t / (4 * K + 1) := hδdef ▸ (min_le_right _ _).trans (min_le_left _ _)
  have hδS : δ ≤ t / (4 * S + 1) := hδdef ▸ (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨f, ⟨F, hFfd, hFst, hfF⟩, hf⟩ := hdense (η : H) δ hδpos
  obtain ⟨η', hη'F, hdist, hsum⟩ :=
    hApp (n + 1) ε (smD ε π) (smE ε π) hG hUn (casVal (lam + t • d)) hcas F hFfd hFst η f hfF
  obtain ⟨w, rfl⟩ : ∃ w, η' = η - w := ⟨η - η', (sub_sub_cancel η η').symm⟩
  rw [sub_sub_cancel] at hdist hsum
  replace hsum : ∑ a, ∑ b, ‖smE ε π a b w‖ ^ 2 ≤ K * ‖η - f‖ :=
    hsum.trans_eq (by subst hKdef; rfl)
  have hηf : ‖η - f‖ < δ := hf
  have hw : ‖w‖ < δ := lt_of_le_of_lt hdist hηf
  have hKb : K * ‖η - f‖ ≤ t / 4 := by
    have h1 : K * ‖η - f‖ ≤ K * (t / (4 * K + 1)) :=
      mul_le_mul_of_nonneg_left (hηf.le.trans hδK) hK0
    have h2 : K * (t / (4 * K + 1)) ≤ t / 4 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by linarith) (by norm_num)]
      nlinarith
    linarith
  have hSb : S * ‖w‖ ^ 2 ≤ t / 4 := by
    have h0 := norm_nonneg w
    have e1 : ‖w‖ ^ 2 ≤ δ ^ 2 := pow_le_pow_left₀ h0 hw.le 2
    have e2 : δ ^ 2 ≤ δ := by nlinarith
    have h1 : S * ‖w‖ ^ 2 ≤ S * (t / (4 * S + 1)) :=
      mul_le_mul_of_nonneg_left (by linarith) hS0
    have h2 : S * (t / (4 * S + 1)) ≤ t / 4 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by linarith) (by norm_num)]
      nlinarith
    linarith
  have hI : ∀ z, ‖I z‖ = ‖z‖ := fun z => congrArg (‖·‖) (hIc z)
  have hn' : 1 / 2 ≤ ‖η - w‖ := by
    have := norm_sub_norm_le η (η - w)
    rw [sub_sub_cancel] at this
    linarith
  refine ⟨hU', ?_, I (η - w), ?_, ?_, ?_⟩
  · rw [Metric.dense_iff]
    intro y r hr
    obtain ⟨f2, -, hf2⟩ := hdense y r hr
    refine ⟨(I f2 : H), ?_, (I f2).2⟩
    rw [Metric.mem_ball, dist_comm, dist_eq_norm, hIc]
    exact hf2
  · intro h0
    have := hI (η - w)
    rw [h0, norm_zero] at this
    linarith
  · refine ⟨F.map I, by haveI := hFfd; infer_instance, ?_, Submodule.mem_map_of_mem hη'F⟩
    intro a b hab y hy
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hy
    rw [← hIE a b z]
    exact Submodule.mem_map_of_mem (hFst _ _ (by rw [hFits.2 a, hFits.2 b]; exact hab) z hz)
  · unfold qf
    simp only [Pi.smul_apply, smul_eq_mul]
    have hB := sum_emb_le (fun a => e (Sum.inl a)) (e.injective.comp Sum.inl_injective)
      (fun a b => ‖smE ε π a b w‖ ^ 2) (fun _ _ => sq_nonneg _)
    have hT : ∑ a : Fin n, ∑ b : Fin n, ‖smE ε' (res e π) a b (I (η - w)) -
        (if a = b then ((t * d' a : ℝ) : ℂ) else 0) • I (η - w)‖ ^ 2 ≤
        ∑ a : Fin n, ∑ b : Fin n,
          (2 * ‖smE ε π (e (Sum.inl a)) (e (Sum.inl b)) η -
              (if a = b then ((t * d' a : ℝ) : ℂ) else 0) • η‖ ^ 2 +
            4 * ‖smE ε π (e (Sum.inl a)) (e (Sum.inl b)) w‖ ^ 2 +
            4 * (‖(if a = b then ((t * d' a : ℝ) : ℂ) else 0)‖ ^ 2 * ‖w‖ ^ 2)) :=
      sum_le_sum fun a _ => sum_le_sum fun b _ => term_le I hI _ _ (hIE a b) _ η w
    have hsplit : ∑ a : Fin n, ∑ b : Fin n,
          (2 * ‖smE ε π (e (Sum.inl a)) (e (Sum.inl b)) η -
              (if a = b then ((t * d' a : ℝ) : ℂ) else 0) • η‖ ^ 2 +
            4 * ‖smE ε π (e (Sum.inl a)) (e (Sum.inl b)) w‖ ^ 2 +
            4 * (‖(if a = b then ((t * d' a : ℝ) : ℂ) else 0)‖ ^ 2 * ‖w‖ ^ 2)) =
        2 * ∑ a : Fin n, ∑ b : Fin n, ‖smE ε π (e (Sum.inl a)) (e (Sum.inl b)) η -
              (if a = b then ((t * d' a : ℝ) : ℂ) else 0) • η‖ ^ 2 +
          4 * ∑ a : Fin n, ∑ b : Fin n, ‖smE ε π (e (Sum.inl a)) (e (Sum.inl b)) w‖ ^ 2 +
          4 * ((∑ a : Fin n, ∑ b : Fin n,
            ‖(if a = b then ((t * d' a : ℝ) : ℂ) else 0)‖ ^ 2) * ‖w‖ ^ 2) := by
      simp only [sum_add_distrib, mul_sum, sum_mul]
    rw [hsplit, hSdef] at hT
    have hx2 : 1 / 4 ≤ ‖I (η - w)‖ ^ 2 := by
      rw [hI]
      nlinarith
    have hfin := mul_le_mul_of_nonneg_left hx2 (by positivity : (0 : ℝ) ≤ (8 * C0 + 8) * t)
    linarith
