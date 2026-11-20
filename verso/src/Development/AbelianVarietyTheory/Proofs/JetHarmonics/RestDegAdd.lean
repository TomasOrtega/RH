import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.IsSelfOf
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.GapParts

set_option autoImplicit false

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowAt

/- English proof (translation)
Unfold `RF.restDeg`. Rewrite using `[Finset.sum_comm, Finset.sum_comm (f := fun g s => ∑ k ∈ Finset.Icc 1 K, k * ga g s k), ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Establish `e : n * ga (bgr s) s n = ∑ g : Fin 2, ∑ k ∈ Finset.Icc 1 K, if g = bgr s ∧ k = n then k * ga g s k else 0`. Rewrite using `[Finset.sum_eq_single (bgr s), Finset.sum_eq_single n]`.

Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[hb]`. Introduce `h`. Conclude with `absurd (Finset.mem_Icc.2 ⟨h1, hK⟩) h`.

Introduce `b _ hb`. Simplify using `[hb]`. Simplify using the standard rewrite rules. Rewrite using `[e, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations.

Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp`.
-/
private theorem restDeg_add {d : ℕ} [NeZero d] (bgr : ZMod d → Fin 2) (n K : ℕ) (h1 : 1 ≤ n) (hK : n ≤ K)
    (ga : Fin 2 → ZMod d → ℕ → ℕ) :
    RF.restDeg bgr n ga K + ∑ s, n * ga (bgr s) s n =
      ∑ g : Fin 2, ∑ s : ZMod d, ∑ k ∈ Finset.Icc 1 K, k * ga g s k := by
  unfold RF.restDeg
  rw [Finset.sum_comm, Finset.sum_comm (f := fun g s => ∑ k ∈ Finset.Icc 1 K, k * ga g s k),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  have e : n * ga (bgr s) s n =
      ∑ g : Fin 2, ∑ k ∈ Finset.Icc 1 K, if g = bgr s ∧ k = n then k * ga g s k else 0 := by
    rw [Finset.sum_eq_single (bgr s), Finset.sum_eq_single n]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_Icc.2 ⟨h1, hK⟩) h
    · intro b _ hb; simp [hb]
    · simp
  rw [e, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp

/- English proof (translation)
Rewrite using `[← Finset.sum_product']`. Use `Finset.sum_bij (fun p _ => P.pos p.1 p.2.val) (fun _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ => rfl)` and prove the remaining obligations. Introduce `p hp q hq hpq`. Conclude with `(h (P.pos q.1 q.2.val)).unique ⟨(Finset.mem_product.1 hp).1, hpq⟩ ⟨(Finset.mem_product.1 hq).1, rfl⟩`. Introduce `z _`.

Take `⟨p, hp, -⟩` from `h z`. Conclude with `⟨p, Finset.mem_product.2 ⟨hp.1, Finset.mem_univ _⟩, hp.2⟩`.
-/
private theorem sum_reps (P : RF.Par) (Z : Finset P.Pl) (h : RF.IsReps P Z) (W : P.Pl → ℕ) :
    ∑ z ∈ Z, ∑ s : ZMod P.d, W (P.pos z s.val) = ∑ z, W z := by
  rw [← Finset.sum_product']
  refine Finset.sum_bij (fun p _ => P.pos p.1 p.2.val) (fun _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ => rfl)
  · intro p hp q hq hpq
    exact (h (P.pos q.1 q.2.val)).unique ⟨(Finset.mem_product.1 hp).1, hpq⟩ ⟨(Finset.mem_product.1 hq).1, rfl⟩
  · intro z _
    obtain ⟨p, hp, -⟩ := h z
    exact ⟨p, Finset.mem_product.2 ⟨hp.1, Finset.mem_univ _⟩, hp.2⟩

/- English proof (translation)
Introduce `E _ _ _ H Dw N j pl a hj1 hjm hpsi hp hq hdom d _ pos Z bgr tau hZ hbij htau`. Establish `hmk` using `N.R.m_add_three_le_k`. Establish `hp' : Dw.p = N.R.k + j - 1` using `hp`. Establish `hq' : Dw.q = N.R.m - j` using `hq`. Establish `hr : N.R.r = N.R.k + N.R.m - 1` using `rfl`.

Establish `hmul : ∀ τ, Dw.mult τ ≤ N.R.r` using `fun τ => by`. Apply the tactic sequence `unfold Datum.mult; split_ifs <;> omega`. Establish `hgs` using `fun τ => gap_sums (Dw.mult τ) (fun i => a (τ, i)) (fun i i' hi hi' => hdom τ ⟨i, lt_of_le_of_lt hi hi'⟩ ⟨i', hi'⟩ hi)`. Establish `hmain : ∀ z s, gap (Dw.mult (tau z (bgr s) s)) (fun i => a (tau z (bgr s) s, i)) (N.R.k - 1) = gapW N pl a (pos z s.val)`. Introduce `z s`.

Rewrite using `[htau]`. Establish `hm : Dw.mult (pl (pos z s.val)) = Dw.p` using `if_pos (hpsi _)`. Rewrite using `[hm]`. Unfold `gap gapW`. Rewrite using `[if_pos (by omega), if_pos (by omega)]`.

Both sides reduce to the same expression. Use `⟨fun z _ g s k hk => (hgs _).1 k hk, fun z _ s => hmain z s, ?_⟩` and prove the remaining obligations. Establish `hDF : DF Dw a = ∑ z ∈ Z, ∑ g : Fin 2, ∑ s : ZMod d, ∑ i : Fin (Dw.mult (tau z g s)), a (tau z g s, i)`. Unfold `DF`. Rewrite using `[← hbij.sum_comp (fun τ => ∑ i : Fin (Dw.mult τ), a (τ, i)), Fintype.sum_prod_type, ← Finset.sum_coe_sort Z]`.

Use `Finset.sum_congr rfl fun z _ => ?_` and prove the remaining obligations. Rewrite using `[Fintype.sum_prod_type]`. Establish `key : (∑ z ∈ Z, RF.restDeg bgr (N.R.k - 1) (fun g s => gap (Dw.mult (tau z g s)) fun i => a (tau z g s, i)) N.R.r) + (N.R.k - 1) * ∑ z, gapW N pl a z = DF Dw a`. Establish `hs : ∑ z ∈ Z, ∑ s : ZMod d, gapW N pl a (pos z s.val) = ∑ z, gapW N pl a z` using `sum_reps (parAt N j d pos) Z hZ (gapW N pl a)`. Rewrite using `[hDF, ← hs, Finset.mul_sum, ← Finset.sum_add_distrib]`.

Use `Finset.sum_congr rfl fun z _ => ?_` and prove the remaining obligations. Use `restDeg_add bgr (N.R.k - 1) N.R.r (by omega) (by omega) (fun g s => gap (Dw.mult (tau z g s)) fun i => a (tau z g s, i))` as an intermediate fact. Simplify using `only [hmain] at this`. Rewrite using `[Finset.mul_sum, this]`. Conclude with `Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun s _ => ((hgs _).2 _ (hmul _)).2`.

Unfold `restOf`. Rewrite using `[← key]`. Move the coercions through the operations in `[Nat.cast_sub (show 1 ≤ N.R.k by omega)]`. Simplify using the standard rewrite rules.
-/
theorem wtHyp_gap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (N : NumDatum) (j : ℕ) (pl : RPl N.R → (E →+* ℂ)) (a : (E →+* ℂ) × ℕ → ℕ), 1 ≤ j → j ≤ N.R.m → (∀ z, InPsi H (pl z)) → Dw.p = (N.R.sigW j).1 → Dw.q = (N.R.sigW j).2 → DomW Dw a → ∀ (d : ℕ) [NeZero d] (pos : RPl N.R → ℕ → RPl N.R) (Z : Finset (RPl N.R)) (bgr : ZMod d → Fin 2) (tau : RPl N.R → Fin 2 → ZMod d → (E →+* ℂ)), RF.IsReps (parAt N j d pos) Z → Function.Bijective (fun x : Z × Fin 2 × ZMod d => tau x.1.1 x.2.1 x.2.2) → (∀ z s, tau z (bgr s) s = pl (pos z s.val)) → RF.WtHyp N.R.k N.R.r Z bgr (fun z g s => Dw.mult (tau z g s)) (fun z g s => gap (Dw.mult (tau z g s)) fun i => a (tau z g s, i)) (fun z => RF.alongOrb (parAt N j d pos) z (gapW N pl a)) (fun _ _ => 0) (restOf N Dw pl a) := by
  intro E _ _ _ H Dw N j pl a hj1 hjm hpsi hp hq hdom d _ pos Z bgr tau hZ hbij htau
  have hmk := N.R.m_add_three_le_k
  have hp' : Dw.p = N.R.k + j - 1 := hp
  have hq' : Dw.q = N.R.m - j := hq
  have hr : N.R.r = N.R.k + N.R.m - 1 := rfl
  have hmul : ∀ τ, Dw.mult τ ≤ N.R.r := fun τ => by
    unfold Datum.mult; split_ifs <;> omega
  have hgs := fun τ => gap_sums (Dw.mult τ) (fun i => a (τ, i)) (fun i i' hi hi' => hdom τ ⟨i, lt_of_le_of_lt hi hi'⟩ ⟨i', hi'⟩ hi)
  have hmain : ∀ z s, gap (Dw.mult (tau z (bgr s) s)) (fun i => a (tau z (bgr s) s, i)) (N.R.k - 1) =
      gapW N pl a (pos z s.val) := by
    intro z s
    rw [htau]
    have hm : Dw.mult (pl (pos z s.val)) = Dw.p := if_pos (hpsi _)
    rw [hm]
    unfold gap gapW
    rw [if_pos (by omega), if_pos (by omega)]
    rfl
  refine ⟨fun z _ g s k hk => (hgs _).1 k hk, fun z _ s => hmain z s, ?_⟩
  have hDF : DF Dw a = ∑ z ∈ Z, ∑ g : Fin 2, ∑ s : ZMod d, ∑ i : Fin (Dw.mult (tau z g s)), a (tau z g s, i) := by
    unfold DF
    rw [← hbij.sum_comp (fun τ => ∑ i : Fin (Dw.mult τ), a (τ, i)), Fintype.sum_prod_type,
      ← Finset.sum_coe_sort Z]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Fintype.sum_prod_type]
  have key : (∑ z ∈ Z, RF.restDeg bgr (N.R.k - 1)
      (fun g s => gap (Dw.mult (tau z g s)) fun i => a (tau z g s, i)) N.R.r) +
      (N.R.k - 1) * ∑ z, gapW N pl a z = DF Dw a := by
    have hs : ∑ z ∈ Z, ∑ s : ZMod d, gapW N pl a (pos z s.val) = ∑ z, gapW N pl a z :=
      sum_reps (parAt N j d pos) Z hZ (gapW N pl a)
    rw [hDF, ← hs, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun z _ => ?_
    have := restDeg_add bgr (N.R.k - 1) N.R.r (by omega) (by omega)
      (fun g s => gap (Dw.mult (tau z g s)) fun i => a (tau z g s, i))
    simp only [hmain] at this
    rw [Finset.mul_sum, this]
    exact Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun s _ => ((hgs _).2 _ (hmul _)).2
  unfold restOf
  rw [← key]
  push_cast [Nat.cast_sub (show 1 ≤ N.R.k by omega)]
  simp

end GlobalTheory.RowAt
