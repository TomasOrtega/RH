import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFullFlagRestrictFibre
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

noncomputable section

namespace FlagRestrict

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {Ω : Type*} [Field Ω] [Algebra O Ω]
variable {x : (Σ k, ι k) → Ω} {Q : Ideal (MRingOver (kap O) ι)} [Q.IsPrime]
variable {N : ℕ} {V : Type*} [AddCommGroup V] [Module Ω V] {B : ChartBundle O (mseg x) N V}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `_`. Establish `he : e ∈ Submodule.span (FractionRing (MRingOver (kap O) ι ⧸ Q)) (Set.range b)` using `hsp ▸ Submodule.mem_top`. Take `⟨a, ha⟩` from `(Submodule.mem_span_range_iff_exists_fun _).1 he`. Conclude with `⟨a, fun q => ⟨1, by simp⟩, ha.symm⟩`.

Introduce `_`. Conclude with `⟨1, by simp⟩`.
-/
theorem frame_zero {s : ∀ k, ι k} {b : Fin N → resFibre O x Q B}
    (hsp : Submodule.span (FractionRing (MRingOver (kap O) ι ⧸ Q)) (Set.range b) = ⊤) (e : resFibre O x Q B) :
    (∃ n : ℕ, (0 : FractionRing (MRingOver (kap O) ι ⧸ Q)) ^ n • e ∈ resLat O x Q B s) ↔
      ∃ a : Fin N → FractionRing (MRingOver (kap O) ι ⧸ Q),
        (∀ q, ∃ n : ℕ, (0 : FractionRing (MRingOver (kap O) ι ⧸ Q)) ^ n * a q ∈
          chartRing (kap O) (mseg (genPt (kap O) Q)) s) ∧ e = ∑ q, a q • b q := by
  constructor
  · intro _
    have he : e ∈ Submodule.span (FractionRing (MRingOver (kap O) ι ⧸ Q)) (Set.range b) := hsp ▸ Submodule.mem_top
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 he
    exact ⟨a, fun q => ⟨1, by simp⟩, ha.symm⟩
  · intro _
    exact ⟨1, by simp⟩

/- English proof (translation)
Establish `h : rs x Q (∑ l, c l * f l) = ∑ l, rs x Q (c l) * rs x Q (f l)`. Rewrite using `[rs_sum hPQ _ _ fun l _ => mul_mem (chartRing_sub hPQ hs (hc l)).1 (chartRing_sub hPQ hs (hf l)).1]`. Conclude with `Finset.sum_congr rfl fun l _ => rs_mul hPQ (chartRing_sub hPQ hs (hc l)).1 (chartRing_sub hPQ hs (hf l)).1`. Rewrite `h` using `[hsum, rs_one hPQ]`. Use `⟨h.symm, ?_⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Simplify using `[hne] at h`.
-/
theorem cover_rs (hPQ : redIdeal O (mcIdeal O x) ≤ Q) {s : ∀ k, ι k} (hs : mseg (genPt (kap O) Q) s ≠ 0)
    {k : ℕ} {f c : Fin k → Ω} (hf : ∀ l, f l ∈ chartRing O (mseg x) s) (hc : ∀ l, c l ∈ chartRing O (mseg x) s)
    (hsum : ∑ l, c l * f l = 1) : ∑ l, rs x Q (c l) * rs x Q (f l) = 1 ∧ ∃ l, rs x Q (f l) ≠ 0 := by
  have h : rs x Q (∑ l, c l * f l) = ∑ l, rs x Q (c l) * rs x Q (f l) := by
    rw [rs_sum hPQ _ _ fun l _ => mul_mem (chartRing_sub hPQ hs (hc l)).1 (chartRing_sub hPQ hs (hf l)).1]
    exact Finset.sum_congr rfl fun l _ =>
      rs_mul hPQ (chartRing_sub hPQ hs (hc l)).1 (chartRing_sub hPQ hs (hf l)).1
  rw [hsum, rs_one hPQ] at h
  refine ⟨h.symm, ?_⟩
  by_contra hne
  push_neg at hne
  simp [hne] at h

variable (B) in

def resBundle (hPQ : redIdeal O (mcIdeal O x) ≤ Q) :
    ChartBundle (kap O) (mseg (genPt (kap O) Q)) N (resFibre O x Q B) where
  lat := resLat O x Q B
  stable := fun s _ ha _ he => resLat_smul_mem hPQ s ha he
  frame := by
    intro s hs
    obtain ⟨k, f, c, hf, hc, hsum, hl⟩ := B.frame s (mseg_ne_zero hPQ hs)
    obtain ⟨hsum', l₀, hl₀⟩ := cover_rs hPQ hs hf hc hsum
    obtain ⟨b₀, hb₀, hsp₀, hlat₀⟩ := hl l₀
    have h₀ := frame_res_basis hPQ hs (hf l₀) hl₀ hlat₀ hb₀ hsp₀
    refine ⟨k, fun l => rs x Q (f l), fun l => rs x Q (c l), fun l => (chartRing_sub hPQ hs (hf l)).2,
      fun l => (chartRing_sub hPQ hs (hc l)).2, hsum', fun l => ?_⟩
    beta_reduce
    by_cases h0 : rs x Q (f l) = 0
    · refine ⟨_, h₀.1, h₀.2, fun e => ?_⟩
      rw [h0]
      exact frame_zero h₀.2 e
    · obtain ⟨b, hb, hsp, hlat⟩ := hl l
      have h := frame_res_basis hPQ hs (hf l) h0 hlat hb hsp
      exact ⟨_, h.1, h.2, frame_res_lat hPQ hs (hf l) h0 hlat⟩
  overlap := fun _ _ hs ht _ he => resLat_overlap hPQ hs ht he

/- English proof (translation)
Take `⟨hw0, ⟨n, hn⟩, ⟨n', hn'⟩⟩` from `hw`. Establish `h1` using `mem_locAlg_of_pow_mul hPQ hs hf hf0 hn`. Establish `h2` using `mem_locAlg_of_pow_mul hPQ hs hf hf0 hn'`. Establish `h3 : rs x Q w * rs x Q w⁻¹ = 1` using `by rw [← rs_mul hPQ h1 h2, mul_inv_cancel₀ hw0, rs_one hPQ]`. Establish `h4 : rs x Q w ≠ 0` using `left_ne_zero_of_mul_eq_one h3`.

Establish `hfl` using `(chartRing_sub hPQ hs hf).1`. Use `⟨h1, h2, h4, h4, ⟨n, ?_⟩, ⟨n', ?_⟩⟩` and prove the remaining obligations. Rewrite using `[← rs_pow hPQ hfl, ← rs_mul hPQ (pow_mem hfl n) h1]`. Conclude with `(chartRing_sub hPQ hs hn).2`. Rewrite using `[← (inv_mem_of_rs_ne_zero hPQ h1 h4).2, ← rs_pow hPQ hfl, ← rs_mul hPQ (pow_mem hfl n') h2]`.

Conclude with `(chartRing_sub hPQ hs hn').2`.
-/
theorem unit_res (hPQ : redIdeal O (mcIdeal O x) ≤ Q) {s : ∀ k, ι k} (hs : mseg (genPt (kap O) Q) s ≠ 0) {f w : Ω}
    (hf : f ∈ chartRing O (mseg x) s) (hf0 : rs x Q f ≠ 0) (hw : IsUnitOn O (mseg x) s f w) :
    w ∈ locAlg x Q ∧ w⁻¹ ∈ locAlg x Q ∧ rs x Q w ≠ 0 ∧
      IsUnitOn (kap O) (mseg (genPt (kap O) Q)) s (rs x Q f) (rs x Q w) := by
  obtain ⟨hw0, ⟨n, hn⟩, ⟨n', hn'⟩⟩ := hw
  have h1 := mem_locAlg_of_pow_mul hPQ hs hf hf0 hn
  have h2 := mem_locAlg_of_pow_mul hPQ hs hf hf0 hn'
  have h3 : rs x Q w * rs x Q w⁻¹ = 1 := by rw [← rs_mul hPQ h1 h2, mul_inv_cancel₀ hw0, rs_one hPQ]
  have h4 : rs x Q w ≠ 0 := left_ne_zero_of_mul_eq_one h3
  have hfl := (chartRing_sub hPQ hs hf).1
  refine ⟨h1, h2, h4, h4, ⟨n, ?_⟩, ⟨n', ?_⟩⟩
  · rw [← rs_pow hPQ hfl, ← rs_mul hPQ (pow_mem hfl n) h1]
    exact (chartRing_sub hPQ hs hn).2
  · rw [← (inv_mem_of_rs_ne_zero hPQ h1 h4).2, ← rs_pow hPQ hfl, ← rs_mul hPQ (pow_mem hfl n') h2]
    exact (chartRing_sub hPQ hs hn').2

/- English proof (translation)
The claim follows from `Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (Finset.prod_ne_zero_iff.1 hs k (Finset.mem_univ k))`.
-/
theorem chartMon_ne_zero {F : Type*} [Field F] (y : (Σ k, ι k) → F) {s : ∀ k, ι k} (hs : mseg y s ≠ 0)
    (m : K → ℤ) : chartMon y s m ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (Finset.prod_ne_zero_iff.1 hs k (Finset.mem_univ k))

def lowSet (j : Fin (N + 1)) : Set (Fin N) := {q | (q : ℕ) < j}

/- English proof (translation)
Establish `e : b '' lowSet j = Set.range (b ∘ Fin.castLE (Fin.is_le j))`. Use extensionality with `v`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨q, hq, rfl⟩`. Conclude with `⟨⟨q, hq⟩, rfl⟩`.

Introduce and unpack `⟨q, rfl⟩`. Conclude with `⟨_, show ((Fin.castLE (Fin.is_le j) q : Fin N) : ℕ) < j from q.2, rfl⟩`. Rewrite using `[e, finrank_span_eq_card (hb.comp _ (Fin.castLE_injective _)), Fintype.card_fin]`.
-/
theorem finrank_span_low {F E : Type*} [Field F] [AddCommGroup E] [Module F E] {b : Fin N → E}
    (hb : LinearIndependent F b) (j : Fin (N + 1)) :
    Module.finrank F (Submodule.span F (b '' lowSet j)) = j := by
  have e : b '' lowSet j = Set.range (b ∘ Fin.castLE (Fin.is_le j)) := by
    ext v
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨⟨q, hq⟩, rfl⟩
    · rintro ⟨q, rfl⟩
      exact ⟨_, show ((Fin.castLE (Fin.is_le j) q : Fin N) : ℕ) < j from q.2, rfl⟩
  rw [e, finrank_span_eq_card (hb.comp _ (Fin.castLE_injective _)), Fintype.card_fin]

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Use `choose s₀ hs₀' using hrel`. Establish `hs₀ : mseg (genPt (kap O) Q) s₀ ≠ 0` using `Finset.prod_ne_zero_iff.2 fun k _ => by`. Introduce `h`. Apply `hs₀' k` to reduce the goal to its premises. Rewrite using `[← aeval_genPt_eq_zero_iff, aeval_X]`.

Conclude with `h`. Take `⟨k₀, f₀, c₀, hf₀, hc₀, hsum₀, hl₀⟩` from `fl.frame s₀ (mseg_ne_zero hPQ hs₀)`. Take `⟨-, l₀, hl₀0⟩` from `cover_rs hPQ hs₀ hf₀ hc₀ hsum₀`. Take `⟨b₀, hb₀, hsp₀, hlat₀, hw₀⟩` from `hl₀ l₀`. Use `choose w₀ hw₀u hw₀v using hw₀`.

Establish `hbM` using `frame_mem_stalk hPQ hs₀ (hf₀ l₀) hl₀0 hlat₀`. Take `⟨li₀, sp₀⟩` from `frame_res_basis hPQ hs₀ (hf₀ l₀) hl₀0 hlat₀ hb₀ hsp₀`. Take `⟨b₀', hb₀'⟩ : ∃ g : Fin N → resFibre O x Q B, g = fun q => resMap O x Q B ⟨b₀ q, hbM q⟩` from `⟨_, rfl⟩`. Rewrite `li₀`, `sp₀` using `[← hb₀']`. Establish `hw₀r : ∀ i, rs x Q (w₀ i) ≠ 0` using `fun i => (unit_res hPQ hs₀ (hf₀ l₀) hl₀0 (hw₀u i)).2.2.1`.

Establish `hcm₀ : ∀ i, chartMon (genPt (kap O) Q) s₀ (fl.deg i) ≠ 0` using `fun i => chartMon_ne_zero _ hs₀ _`. Take `⟨gen', hgen'⟩ : ∃ g : Fin N → resFibre O x Q B, ∀ i, g i = (rs x Q (w₀ i) * chartMon (genPt (kap O) Q) s₀ (fl.deg i))⁻¹ • b₀' i` from `⟨_, fun i => rfl⟩`. Establish `hb₀V : ∀ (q : Fin N) (j : Fin (N + 1)), (q : ℕ) < j → b₀ q ∈ fl.Vs j`. Introduce `q j hqj`. Establish `hle : q.succ ≤ j`.

Rewrite using `[Fin.le_def, Fin.val_succ]`. Conclude with `hqj`. Establish `h1 : b₀ q = (b₀ q - (w₀ q * chartMon x s₀ (fl.deg q)) • fl.gen q) + (w₀ q * chartMon x s₀ (fl.deg q)) • fl.gen q` using `by abel`. Rewrite using `[h1]`. Conclude with `add_mem (fl.mono (le_trans (show q.castSucc < q.succ from Fin.castSucc_lt_succ).le hle) (hw₀v q)) (Submodule.smul_mem _ _ (fl.mono hle (fl.gen_mem q)))`.

Set `bas : Module.Basis (Fin N) Ω V` to `Module.Basis.mk hb₀ (by rw [hsp₀])`. Establish `hbas : ⇑bas = b₀` using `funext fun q => Module.Basis.mk_apply _ _ q`. Use `haveI : FiniteDimensional Ω V := Module.Finite.of_basis bas`. Establish `hVs : ∀ j, fl.Vs j = Submodule.span Ω (b₀ '' lowSet j)`. Introduce `j`.

Use `symm`. Apply `Submodule.eq_of_le_of_finrank_eq` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨q, hq, rfl⟩`. Conclude with `hb₀V q j hq`.

Rewrite using `[finrank_span_low hb₀ j, fl.dim j]`. Establish `hres : ∀ j, resSub O x Q B (fl.Vs j) = Submodule.span _ (b₀' '' lowSet j)`. Introduce `j`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[resSub, Submodule.span_le]`.

Introduce and unpack `_ ⟨m, hm, rfl⟩`. Take `⟨a, ha, hma⟩` from `stalk_coords hPQ hs₀ (hf₀ l₀) hl₀0 hlat₀ m.2`. Rewrite using `[resMap_sum hPQ hs₀ (hf₀ l₀) hl₀0 hlat₀ ha m hma]`. Establish `hrep : bas.equivFun m = a`. Rewrite using `[hma, show ∑ q, a q • b₀ q = bas.equivFun.symm a by`.

Rewrite using `[Module.Basis.equivFun_symm_apply, hbas], LinearEquiv.apply_symm_apply]`. Establish `hsupp : ∀ q : Fin N, ¬ ((q : ℕ) < j) → a q = 0`. Introduce `q hq`. Establish `hm' : (m : V) ∈ Submodule.span Ω (bas '' lowSet j)`. Rewrite using `[hbas, ← hVs j]`.

Conclude with `hm`. Rewrite `hm'` using `[Module.Basis.mem_span_image]`. Rewrite using `[← hrep, Module.Basis.equivFun_apply]`. Assume the negation of the conclusion as `hne`. Conclude with `hq (hm' (Finsupp.mem_support_iff.2 hne))`.

Use `Submodule.sum_mem _ fun q _ => ?_` and prove the remaining obligations. Distinguish the cases in `hq : (q : ℕ) < j`. Rewrite `*` using `[hb₀']`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, hq, rfl⟩)`. Rewrite using `[hsupp q hq, rs_zero hPQ, zero_smul]`.

Conclude with `zero_mem _`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨q, hq, rfl⟩`. Rewrite using `[hb₀']`. Conclude with `Submodule.subset_span ⟨⟨b₀ q, hbM q⟩, hb₀V q j hq, rfl⟩`.

Use `⟨{ Vs := fun j => resSub O x Q B (fl.Vs j) mono := fun i j h => Submodule.span_mono (Set.image_mono fun m hm => fl.mono h hm) dim := fun j => by rw [hres j, finrank_span_low li₀ j] top := ?_ deg := fl.deg gen := gen' gen_mem := fun i => ?_ frame := ?_ }, rfl, fun _ => rfl⟩` and prove the remaining obligations. Rewrite using `[hres, show lowSet (Fin.last N) = Set.univ from Set.eq_univ_of_forall fun q => q.2, Set.image_univ]`. Conclude with `sp₀`. Rewrite using `[hres, hgen']`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, show (i : ℕ) < i.succ by simp, rfl⟩)`.

Introduce `s hs`. Take `⟨k, f, c, hf, hc, hsum, hl⟩` from `fl.frame s (mseg_ne_zero hPQ hs)`. Take `⟨hsum', -, -⟩` from `cover_rs hPQ hs hf hc hsum`. Use `⟨k, fun l => rs x Q (f l), fun l => rs x Q (c l), fun l => (chartRing_sub hPQ hs (hf l)).2, fun l => (chartRing_sub hPQ hs (hc l)).2, hsum', fun l => ?_⟩` and prove the remaining obligations. Use `beta_reduce`.

Distinguish the cases in `h0 : rs x Q (f l) = 0`. Establish `hu : ∀ i, chartMon (genPt (kap O) Q) s (fl.deg i) * (rs x Q (w₀ i) * chartMon (genPt (kap O) Q) s₀ (fl.deg i))⁻¹ ≠ 0` using `fun i => mul_ne_zero (chartMon_ne_zero _ hs _) (inv_ne_zero (mul_ne_zero (hw₀r i) (hcm₀ i)))`. Establish `hbu : (fun i => chartMon (genPt (kap O) Q) s (fl.deg i) • gen' i) = fun i => (Units.mk0 _ (hu i) : (FractionRing (MRingOver (kap O) ι ⧸ Q))ˣ) • b₀' i`. Use function extensionality and compare the values at `i`. Rewrite using `[hgen', smul_smul, Units.smul_def, Units.val_mk0]`.

Establish `hli : LinearIndependent (FractionRing (MRingOver (kap O) ι ⧸ Q)) (fun i => chartMon (genPt (kap O) Q) s (fl.deg i) • gen' i)`. Rewrite using `[hbu]`. Conclude with `li₀.units_smul fun i => Units.mk0 _ (hu i)`. Establish `hsp : Submodule.span (FractionRing (MRingOver (kap O) ι ⧸ Q)) (Set.range fun i => chartMon (genPt (kap O) Q) s (fl.deg i) • gen' i) = ⊤`. Rewrite using `[eq_top_iff, ← sp₀, Submodule.span_le]`.

Introduce and unpack `_ ⟨i, rfl⟩`. Establish `e : b₀' i = (Units.mk0 _ (hu i))⁻¹ • (chartMon (genPt (kap O) Q) s (fl.deg i) • gen' i)`. Rewrite using `[congrFun hbu i, smul_smul, inv_mul_cancel, one_smul]`. Rewrite using `[e]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`.

Use `⟨_, hli, hsp, fun e => ?_, fun i => ⟨1, ?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[h0]`. Conclude with `frame_zero hsp e`. Rewrite using `[h0]`. Conclude with `⟨one_ne_zero, ⟨1, by simp⟩, ⟨1, by simp⟩⟩`.

Rewrite using `[one_mul, sub_self]`. Conclude with `zero_mem _`. Take `⟨b, hb, hsp, hlat, hw⟩` from `hl l`. Establish `hbM'` using `frame_mem_stalk hPQ hs (hf l) h0 hlat`. Take `⟨li, sp⟩` from `frame_res_basis hPQ hs (hf l) h0 hlat hb hsp`.

Use `⟨_, li, sp, frame_res_lat hPQ hs (hf l) h0 hlat, fun i => ?_⟩` and prove the remaining obligations. Take `⟨w, hwu, hwv⟩` from `hw i`. Take `⟨hw1, -, -, hw4⟩` from `unit_res hPQ hs (hf l) h0 hwu`. Take `⟨hw01, hw02, hw03, -⟩` from `unit_res hPQ hs₀ (hf₀ l₀) hl₀0 (hw₀u i)`. Take `⟨hcm1, hcm2⟩` from `chartMon_ratio (x := x) hPQ hs hs₀ (fl.deg i)`.

Use `⟨rs x Q w, hw4, ?_⟩` and prove the remaining obligations. Establish `hx0 : chartMon x s₀ (fl.deg i) ≠ 0` using `chartMon_ne_zero x (mseg_ne_zero hPQ hs₀) _`. Establish `hw00 : w₀ i ≠ 0` using `(hw₀u i).1`. Take `⟨u, hu_def⟩ : ∃ u : Ω, u = w * (w₀ i)⁻¹ * (chartMon x s (fl.deg i) / chartMon x s₀ (fl.deg i))` from `⟨_, rfl⟩`. Establish `hu : u ∈ locAlg x Q`.

Rewrite using `[hu_def]`. Conclude with `mul_mem (mul_mem hw1 hw02) hcm1`. Establish `hu' : u * (w₀ i * chartMon x s₀ (fl.deg i)) = w * chartMon x s (fl.deg i)`. Rewrite using `[hu_def]`. Clear the denominators using the available nonvanishing facts.

Establish `hmem : b i - u • b₀ i ∈ fl.Vs i.castSucc`. Establish `e : b i - u • b₀ i = (b i - (w * chartMon x s (fl.deg i)) • fl.gen i) - u • (b₀ i - (w₀ i * chartMon x s₀ (fl.deg i)) • fl.gen i)`. Rewrite using `[smul_sub u, smul_smul, hu']`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`.

Conclude with `sub_mem hwv (Submodule.smul_mem _ _ (hw₀v i))`. Establish `hS : b i - u • b₀ i ∈ stalk O x Q B` using `sub_mem (hbM' i) (smul_mem_stalk hPQ hu (hbM i))`. Establish `hres' : resMap O x Q B ⟨b i - u • b₀ i, hS⟩ = resMap O x Q B ⟨b i, hbM' i⟩ - rs x Q u • b₀' i`. Rewrite using `[hb₀', ← resMap_smul hPQ hu ⟨b₀ i, hbM i⟩, ← map_sub]`. Both sides reduce to the same expression.

Establish `hru : rs x Q u • b₀' i = (rs x Q w * chartMon (genPt (kap O) Q) s (fl.deg i)) • gen' i`. Rewrite using `[hgen', smul_smul]`. Use `congr 1`. Rewrite using `[hu_def, rs_mul hPQ (mul_mem hw1 hw02) hcm1, rs_mul hPQ hw1 hw02, (inv_mem_of_rs_ne_zero hPQ hw01 hw03).2, hcm2]`. Use `hw₀r i` as an intermediate fact.

Use `hcm₀ i` as an intermediate fact. Clear the denominators using the available nonvanishing facts. Express the relevant statement in the definitionally equal form `resMap O x Q B ⟨b i, hbM' i⟩ - (rs x Q w * chartMon (genPt (kap O) Q) s (fl.deg i)) • gen' i ∈ resSub O x Q B (fl.Vs i.castSucc)`. Rewrite using `[← hru, ← hres']`. Conclude with `Submodule.subset_span ⟨_, hmem, rfl⟩`.
-/
theorem exists_resFlag (hPQ : redIdeal O (mcIdeal O x) ≤ Q) (hrel : IsRelevant Q) (fl : FullFlag O x B) :
    ∃ fl' : FullFlag (kap O) (genPt (kap O) Q) (resBundle B hPQ),
      fl'.deg = fl.deg ∧ ∀ i, fl'.Vs i = resSub O x Q B (fl.Vs i) := by
  classical

  choose s₀ hs₀' using hrel
  have hs₀ : mseg (genPt (kap O) Q) s₀ ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => by
    intro h
    apply hs₀' k
    rw [← aeval_genPt_eq_zero_iff, aeval_X]
    exact h

  obtain ⟨k₀, f₀, c₀, hf₀, hc₀, hsum₀, hl₀⟩ := fl.frame s₀ (mseg_ne_zero hPQ hs₀)
  obtain ⟨-, l₀, hl₀0⟩ := cover_rs hPQ hs₀ hf₀ hc₀ hsum₀
  obtain ⟨b₀, hb₀, hsp₀, hlat₀, hw₀⟩ := hl₀ l₀
  choose w₀ hw₀u hw₀v using hw₀
  have hbM := frame_mem_stalk hPQ hs₀ (hf₀ l₀) hl₀0 hlat₀
  obtain ⟨li₀, sp₀⟩ := frame_res_basis hPQ hs₀ (hf₀ l₀) hl₀0 hlat₀ hb₀ hsp₀
  obtain ⟨b₀', hb₀'⟩ : ∃ g : Fin N → resFibre O x Q B, g = fun q => resMap O x Q B ⟨b₀ q, hbM q⟩ := ⟨_, rfl⟩
  rw [← hb₀'] at li₀ sp₀
  have hw₀r : ∀ i, rs x Q (w₀ i) ≠ 0 := fun i => (unit_res hPQ hs₀ (hf₀ l₀) hl₀0 (hw₀u i)).2.2.1
  have hcm₀ : ∀ i, chartMon (genPt (kap O) Q) s₀ (fl.deg i) ≠ 0 := fun i => chartMon_ne_zero _ hs₀ _
  obtain ⟨gen', hgen'⟩ : ∃ g : Fin N → resFibre O x Q B,
      ∀ i, g i = (rs x Q (w₀ i) * chartMon (genPt (kap O) Q) s₀ (fl.deg i))⁻¹ • b₀' i := ⟨_, fun i => rfl⟩

  have hb₀V : ∀ (q : Fin N) (j : Fin (N + 1)), (q : ℕ) < j → b₀ q ∈ fl.Vs j := by
    intro q j hqj
    have hle : q.succ ≤ j := by
      rw [Fin.le_def, Fin.val_succ]
      exact hqj
    have h1 : b₀ q = (b₀ q - (w₀ q * chartMon x s₀ (fl.deg q)) • fl.gen q) +
        (w₀ q * chartMon x s₀ (fl.deg q)) • fl.gen q := by abel
    rw [h1]
    exact add_mem (fl.mono (le_trans (show q.castSucc < q.succ from Fin.castSucc_lt_succ).le hle) (hw₀v q))
      (Submodule.smul_mem _ _ (fl.mono hle (fl.gen_mem q)))
  let bas : Module.Basis (Fin N) Ω V := Module.Basis.mk hb₀ (by rw [hsp₀])
  have hbas : ⇑bas = b₀ := funext fun q => Module.Basis.mk_apply _ _ q
  haveI : FiniteDimensional Ω V := Module.Finite.of_basis bas
  have hVs : ∀ j, fl.Vs j = Submodule.span Ω (b₀ '' lowSet j) := by
    intro j
    symm
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]
      rintro _ ⟨q, hq, rfl⟩
      exact hb₀V q j hq
    · rw [finrank_span_low hb₀ j, fl.dim j]

  have hres : ∀ j, resSub O x Q B (fl.Vs j) = Submodule.span _ (b₀' '' lowSet j) := by
    intro j
    apply le_antisymm
    · rw [resSub, Submodule.span_le]
      rintro _ ⟨m, hm, rfl⟩
      obtain ⟨a, ha, hma⟩ := stalk_coords hPQ hs₀ (hf₀ l₀) hl₀0 hlat₀ m.2
      rw [resMap_sum hPQ hs₀ (hf₀ l₀) hl₀0 hlat₀ ha m hma]
      have hrep : bas.equivFun m = a := by
        rw [hma, show ∑ q, a q • b₀ q = bas.equivFun.symm a by
          rw [Module.Basis.equivFun_symm_apply, hbas], LinearEquiv.apply_symm_apply]
      have hsupp : ∀ q : Fin N, ¬ ((q : ℕ) < j) → a q = 0 := by
        intro q hq
        have hm' : (m : V) ∈ Submodule.span Ω (bas '' lowSet j) := by
          rw [hbas, ← hVs j]
          exact hm
        rw [Module.Basis.mem_span_image] at hm'
        rw [← hrep, Module.Basis.equivFun_apply]
        by_contra hne
        exact hq (hm' (Finsupp.mem_support_iff.2 hne))
      refine Submodule.sum_mem _ fun q _ => ?_
      by_cases hq : (q : ℕ) < j
      · rw [hb₀'] at *
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, hq, rfl⟩)
      · rw [hsupp q hq, rs_zero hPQ, zero_smul]
        exact zero_mem _
    · rw [Submodule.span_le]
      rintro _ ⟨q, hq, rfl⟩
      rw [hb₀']
      exact Submodule.subset_span ⟨⟨b₀ q, hbM q⟩, hb₀V q j hq, rfl⟩
  refine ⟨{ Vs := fun j => resSub O x Q B (fl.Vs j)
            mono := fun i j h => Submodule.span_mono (Set.image_mono fun m hm => fl.mono h hm)
            dim := fun j => by rw [hres j, finrank_span_low li₀ j]
            top := ?_
            deg := fl.deg
            gen := gen'
            gen_mem := fun i => ?_
            frame := ?_ }, rfl, fun _ => rfl⟩
  ·
    rw [hres, show lowSet (Fin.last N) = Set.univ from Set.eq_univ_of_forall fun q => q.2, Set.image_univ]
    exact sp₀
  ·
    rw [hres, hgen']
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, show (i : ℕ) < i.succ by simp, rfl⟩)
  ·
    intro s hs
    obtain ⟨k, f, c, hf, hc, hsum, hl⟩ := fl.frame s (mseg_ne_zero hPQ hs)
    obtain ⟨hsum', -, -⟩ := cover_rs hPQ hs hf hc hsum
    refine ⟨k, fun l => rs x Q (f l), fun l => rs x Q (c l), fun l => (chartRing_sub hPQ hs (hf l)).2,
      fun l => (chartRing_sub hPQ hs (hc l)).2, hsum', fun l => ?_⟩
    beta_reduce
    by_cases h0 : rs x Q (f l) = 0
    ·
      have hu : ∀ i, chartMon (genPt (kap O) Q) s (fl.deg i) *
          (rs x Q (w₀ i) * chartMon (genPt (kap O) Q) s₀ (fl.deg i))⁻¹ ≠ 0 := fun i =>
        mul_ne_zero (chartMon_ne_zero _ hs _) (inv_ne_zero (mul_ne_zero (hw₀r i) (hcm₀ i)))
      have hbu : (fun i => chartMon (genPt (kap O) Q) s (fl.deg i) • gen' i) = fun i =>
          (Units.mk0 _ (hu i) : (FractionRing (MRingOver (kap O) ι ⧸ Q))ˣ) • b₀' i := by
        funext i
        rw [hgen', smul_smul, Units.smul_def, Units.val_mk0]
      have hli : LinearIndependent (FractionRing (MRingOver (kap O) ι ⧸ Q))
          (fun i => chartMon (genPt (kap O) Q) s (fl.deg i) • gen' i) := by
        rw [hbu]
        exact li₀.units_smul fun i => Units.mk0 _ (hu i)
      have hsp : Submodule.span (FractionRing (MRingOver (kap O) ι ⧸ Q))
          (Set.range fun i => chartMon (genPt (kap O) Q) s (fl.deg i) • gen' i) = ⊤ := by
        rw [eq_top_iff, ← sp₀, Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        have e : b₀' i = (Units.mk0 _ (hu i))⁻¹ • (chartMon (genPt (kap O) Q) s (fl.deg i) • gen' i) := by
          rw [congrFun hbu i, smul_smul, inv_mul_cancel, one_smul]
        rw [e]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      refine ⟨_, hli, hsp, fun e => ?_, fun i => ⟨1, ?_, ?_⟩⟩
      · rw [h0]
        exact frame_zero hsp e
      · rw [h0]
        exact ⟨one_ne_zero, ⟨1, by simp⟩, ⟨1, by simp⟩⟩
      · rw [one_mul, sub_self]
        exact zero_mem _
    ·
      obtain ⟨b, hb, hsp, hlat, hw⟩ := hl l
      have hbM' := frame_mem_stalk hPQ hs (hf l) h0 hlat
      obtain ⟨li, sp⟩ := frame_res_basis hPQ hs (hf l) h0 hlat hb hsp
      refine ⟨_, li, sp, frame_res_lat hPQ hs (hf l) h0 hlat, fun i => ?_⟩
      obtain ⟨w, hwu, hwv⟩ := hw i
      obtain ⟨hw1, -, -, hw4⟩ := unit_res hPQ hs (hf l) h0 hwu
      obtain ⟨hw01, hw02, hw03, -⟩ := unit_res hPQ hs₀ (hf₀ l₀) hl₀0 (hw₀u i)
      obtain ⟨hcm1, hcm2⟩ := chartMon_ratio (x := x) hPQ hs hs₀ (fl.deg i)
      refine ⟨rs x Q w, hw4, ?_⟩
      have hx0 : chartMon x s₀ (fl.deg i) ≠ 0 := chartMon_ne_zero x (mseg_ne_zero hPQ hs₀) _
      have hw00 : w₀ i ≠ 0 := (hw₀u i).1
      obtain ⟨u, hu_def⟩ : ∃ u : Ω, u = w * (w₀ i)⁻¹ * (chartMon x s (fl.deg i) / chartMon x s₀ (fl.deg i)) :=
        ⟨_, rfl⟩
      have hu : u ∈ locAlg x Q := by
        rw [hu_def]
        exact mul_mem (mul_mem hw1 hw02) hcm1
      have hu' : u * (w₀ i * chartMon x s₀ (fl.deg i)) = w * chartMon x s (fl.deg i) := by
        rw [hu_def]
        field_simp
      have hmem : b i - u • b₀ i ∈ fl.Vs i.castSucc := by
        have e : b i - u • b₀ i = (b i - (w * chartMon x s (fl.deg i)) • fl.gen i) -
            u • (b₀ i - (w₀ i * chartMon x s₀ (fl.deg i)) • fl.gen i) := by
          rw [smul_sub u, smul_smul, hu']
          abel
        rw [e]
        exact sub_mem hwv (Submodule.smul_mem _ _ (hw₀v i))
      have hS : b i - u • b₀ i ∈ stalk O x Q B := sub_mem (hbM' i) (smul_mem_stalk hPQ hu (hbM i))
      have hres' : resMap O x Q B ⟨b i - u • b₀ i, hS⟩ =
          resMap O x Q B ⟨b i, hbM' i⟩ - rs x Q u • b₀' i := by
        rw [hb₀', ← resMap_smul hPQ hu ⟨b₀ i, hbM i⟩, ← map_sub]
        rfl
      have hru : rs x Q u • b₀' i = (rs x Q w * chartMon (genPt (kap O) Q) s (fl.deg i)) • gen' i := by
        rw [hgen', smul_smul]
        congr 1
        rw [hu_def, rs_mul hPQ (mul_mem hw1 hw02) hcm1, rs_mul hPQ hw1 hw02,
          (inv_mem_of_rs_ne_zero hPQ hw01 hw03).2, hcm2]
        have := hw₀r i
        have := hcm₀ i
        field_simp
      change resMap O x Q B ⟨b i, hbM' i⟩ - (rs x Q w * chartMon (genPt (kap O) Q) s (fl.deg i)) • gen' i ∈
        resSub O x Q B (fl.Vs i.castSucc)
      rw [← hru, ← hres']
      exact Submodule.subset_span ⟨_, hmem, rfl⟩

end FlagRestrict

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
