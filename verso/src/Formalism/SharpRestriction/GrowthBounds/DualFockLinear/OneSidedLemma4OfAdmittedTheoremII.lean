import Formalism.SharpRestriction.GrowthBounds.PathWeight
import Formalism.SharpRestriction.GrowthBounds.TableLineDegreeFive

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.MainNotions.SourceCleaning Formalism.MainNotions.G.WittFrameLocaliserOrders Formalism.MainNotions.G.symbolGeneratorData

def OneSidedLemma4 (_D : Formalism.BasicNotions.D7) (CLa CD Csz : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [Fact p.Prime] [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra (WF p n') O] (S : UniformizedDVR p O), OHyp p n' O S →
    CommonHypotheses p n' r (r + K) →
  ∀ (Fr : Frames n' r) (L₁ N₁ G' : ℕ), Fr.Valid L₁ N₁ → TwistBound p Fr (p ^ G') →
  ∀ (deg : Fin n' → ℕ) (a : ℕ) (Y : ℝ) (c0 c'' cStar : ℕ) (Dd : ℝ),
    HypII CLa CD Csz p Fr (r + K) L₁ N₁ G' deg a Y c0 c'' cStar Dd →
  let c' := cPrime n' r Fr.TT.card c0 c'' cStar
  ∀ g : Matrix (Fin (r + K)) (Fin (r + K)) (WF p n'), IsGLW g →
  ∀ (n : ℕ) (obd : ℤ → ℤ → ℝ) (xi : Fin n → ℤ → SegRing O r K) (dd : ℤ → ℤ → ℕ),
    (∀ (i : Fin n) (j : ℕ), j < Fr.J →
      xi i j ∈ XX' O r K Fr j (fun _ => (mStar p Fr (r + K) N₁ (p ^ G') c' : ℤ))
        (fun x => Bo p Fr deg j x / 2 - sl p Fr deg Y (r + K) j x) (obd j) ∧
      xi i j ∈ restrictSupport O {mm | ∀ x ∈ Fr.letters j, ∑ c : Fin (r + K), mm (x, c) = dd j x}) →
    (∀ j : ℕ, j < Fr.J → ∀ x ∈ Fr.letters j, (Fr.IsW j x ∨ x ∈ Fr.LLset j) →
        (dd j x : ℝ) ≤ levDeg p Fr deg j x + levDeg p Fr deg j x / 100) →
  ∀ (mon : Fin n' × Fin (r + K) →₀ ℕ), IsLabel p Fr mon → (∀ v ∈ mon.support, v.1 ∈ Fr.TT) →
  ∀ o : ℕ, (∀ m ∈ (monPh O K p Fr mon xi).support, normDeg r m = o) →
    Realisable p n' S.w n' r g c' o (MvPolynomial.map (algebraMap O (KK O)) (monPh O K p Fr mon xi))

/- English proof (translation)
Introduce `p n' r K _ _ _ _ O _ _ _ _ S hO hH Fr L₁ N₁ G' hV hT deg a Y c0 c'' cStar Dd hII c' g hg n obd xi dd hxi hdd mon hmon hmonT o ho`. Use `h p n' r K O S hO hH Fr L₁ N₁ G' hV hT deg a Y c0 c'' cStar Dd hII g hg n obd xi dd hxi ?_ mon hmon hmonT o ho` and prove the remaining obligations. Introduce `j hj x hx hw`. Use `(abs_le.1 (hdd j hj x hx hw)).2` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem lemma4_of_one_sided (D : Formalism.BasicNotions.D7) (CLa CD Csz : ℝ) (h : OneSidedLemma4 D CLa CD Csz) : Conclusion6 D CLa CD Csz := by
  intro p n' r K _ _ _ _ O _ _ _ _ S hO hH Fr L₁ N₁ G' hV hT deg a Y c0 c'' cStar Dd hII c' g hg n obd xi dd hxi hdd
    mon hmon hmonT o ho
  refine h p n' r K O S hO hH Fr L₁ N₁ G' hV hT deg a Y c0 c'' cStar Dd hII g hg n obd xi dd hxi ?_ mon hmon hmonT o ho
  intro j hj x hx hw
  have := (abs_le.1 (hdd j hj x hx hw)).2
  linarith

def RestGeomU : Prop :=
  ∀ (p n' r : ℕ) [NeZero n'] (F : Frames n' r) (L₁ N₁ : ℕ), 13 ≤ p → 2 ≤ r → Even n' → F.Valid L₁ N₁ →
  ∀ (deg : Fin n' → ℕ) (a : ℕ), (∀ s ∈ F.TT, (a : ℝ) ≤ deg s ∧ (deg s : ℝ) ≤ 2 * a) →
  ∀ (j : ℤ) (dd : ℤ → ℕ),
    (∀ x ∈ F.letters j, (F.IsW j x ∨ x ∈ F.LLset j) →
      (dd x : ℝ) ≤ levDeg p F deg j x + levDeg p F deg j x / 100) →
  ∀ x ∈ nonW F j,
    ((∑ y ∈ (F.letters j).filter (fun y => Even y ∧ y < x ∧ ∀ l < r, y ≠ Arow F x l), dd y : ℕ) : ℝ) ≤
      Bo p F deg j x / 80

def RestDivMU (CLa CD Csz : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [Fact p.Prime] [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra (WF p n') O] (X : Ctx p n' r K O)
    (deg : Fin n' → ℕ) (a : ℕ) (Y : ℝ) (c0 c'' cStar : ℕ) (Dd : ℝ),
    HypII CLa CD Csz p X.Fr (r + K) X.L₁ X.N₁ X.G' deg a Y c0 c'' cStar Dd →
  ∀ (j : ℤ) (dd : ℤ → ℕ),
    (∀ x ∈ X.Fr.letters j, (X.Fr.IsW j x ∨ x ∈ X.Fr.LLset j) →
      (dd x : ℝ) ≤ levDeg p X.Fr deg j x + levDeg p X.Fr deg j x / 100) →
  ∀ P ∈ MGen X.Fr j O K (mStar p X.Fr (r + K) X.N₁ (p ^ X.G') (cPrime n' r X.Fr.TT.card c0 c'' cStar) : ℤ)
      (fun x => Bo p X.Fr deg j x / 2 - sl p X.Fr deg Y (r + K) j x) dd,
    ∃ P' ∈ MGen0 X.Fr j O K,
      P = Dv X.Fr j O K (X.m1 (cPrime n' r X.Fr.TT.card c0 c'' cStar))
        (X.m2 (cPrime n' r X.Fr.TT.card c0 c'' cStar)) * P'

/- English proof (translation)
Introduce `p n' r _ F L₁ N₁ hp hr hn hV deg a hdeg j dd hdd x hx`. Establish `hx1 : x ∈ F.letters j` using `(Finset.mem_filter.1 hx).1`. Establish `hW : ¬ F.IsW j x` using `(Finset.mem_filter.1 hx).2`. Take `⟨⟨ho1, ho2, ho3⟩, _⟩` from `ge_oldest F L₁ N₁ hV (by omega) j x hx1 hW`. Establish `ho1'` using `ho1`.

Unfold `Frames.letters at ho1'`. Rewrite `ho1'` using `[Finset.mem_filter, Finset.mem_Icc]`. Establish `hp0 : (0 : ℝ) < p`. Establish `: (13 : ℝ) ≤ p` using `by exact_mod_cast hp`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hY : ∀ y ∈ (F.letters j).filter (fun y => Even y ∧ y < x ∧ ∀ l < r, y ≠ Arow F x l), y < F.oldest j x ∧ Even y ∧ y ∈ F.letters j ∧ (F.IsW j y ∨ y ∈ F.LLset j)`. Introduce `y hy`. Rewrite `hy` using `[Finset.mem_filter]`. Take `⟨h1, h2, h3, h4⟩` from `hy`. Take `⟨h5, h6⟩` from `ge_older F L₁ N₁ hV hn (by omega) j x hx1 hW y h1 h2 h3 h4`.

Conclude with `⟨h5, h2, h1, h6⟩`. Establish `hlev : ∀ y ∈ F.letters j, levDeg p F deg j y ≤ 2 * ((a : ℝ) / (p : ℝ) ^ (F.dist j y))`. Introduce `y hy`. Unfold `Frames.letters at hy`. Rewrite `hy` using `[Finset.mem_filter]`.

Unfold `levDeg`. Rewrite using `[← mul_div_assoc]`. Conclude with `div_le_div_of_nonneg_right (hdeg _ hy.2).2 (pow_pos hp0 _).le`. Establish `hdd' : ∀ y ∈ (F.letters j).filter (fun y => Even y ∧ y < x ∧ ∀ l < r, y ≠ Arow F x l), (dd y : ℝ) ≤ 2.02 * ((a : ℝ) / (p : ℝ) ^ (F.dist j y))`. Introduce `y hy`.

Take `⟨_, _, h3, h4⟩` from `hY y hy`. Establish `h5` using `hdd y h3 h4`. Establish `h6` using `hlev y h3`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[Nat.cast_sum]`.

Distinguish the cases in `ha : a = 0`. Establish `hz : ∀ y ∈ (F.letters j).filter (fun y => Even y ∧ y < x ∧ ∀ l < r, y ≠ Arow F x l), (dd y : ℝ) = 0`. Introduce `y hy`. Establish `h1` using `hdd' y hy`. Rewrite `h1` using `[ha]`.

Simplify using `only [Nat.cast_zero, zero_div, mul_zero] at h1`. Conclude with `le_antisymm h1 (Nat.cast_nonneg _)`. Rewrite using `[Finset.sum_eq_zero hz]`. Use `level_degree_nonneg p F deg j x` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hf : ∀ y ∈ (F.letters j).filter (fun y => Even y ∧ y < x ∧ ∀ l < r, y ≠ Arow F x l), ((((F.oldest j x - y) / 2).toNat : ℕ) : ℤ) * 2 = F.oldest j x - y ∧ 1 ≤ ((F.oldest j x - y) / 2).toNat`. Introduce `y hy`. Take `⟨h1, h2, _, _⟩` from `hY y hy`. Take `⟨k, hk⟩` from `ho2.sub h2`. Apply the tactic sequence `constructor <;> omega`.

Establish `hsum : ∑ y ∈ (F.letters j).filter (fun y => Even y ∧ y < x ∧ ∀ l < r, y ≠ Arow F x l), (dd y : ℝ) = ∑ m ∈ ((F.letters j).filter (fun y => Even y ∧ y < x ∧ ∀ l < r, y ≠ Arow F x l)).image (fun y => ((F.oldest j x - y) / 2).toNat), (dd (F.oldest j x - 2 * (m : ℤ)) : ℝ)`. Rewrite using `[Finset.sum_image]`. Use `Finset.sum_congr rfl fun y hy => ?_` and prove the remaining obligations. Establish `h1` using `(hf y hy).1`. Establish `h2 : F.oldest j x - 2 * ((((F.oldest j x - y) / 2).toNat : ℕ) : ℤ) = y` using `by omega`.

Rewrite using `[h2]`. Introduce `y1 hy1 y2 hy2 h`. Establish `h1` using `(hf y1 hy1).1`. Establish `h2` using `(hf y2 hy2).1`. Establish `h' : ((F.oldest j x - y1) / 2).toNat = ((F.oldest j x - y2) / 2).toNat` using `h`.

Rewrite `h1` using `[h']`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hsum]`. Establish `hB : (a : ℝ) / (p : ℝ) ^ (F.dist j (F.oldest j x)) ≤ Bo p F deg j x`. Unfold `Bo levDeg`.

Conclude with `div_le_div_of_nonneg_right (hdeg _ ho1'.2).1 (pow_pos hp0 _).le`. Take `⟨g1, g2⟩` from `Formalism.CountingSumsFrames.Top.lemma4Geom (p : ℝ) (a : ℝ) (Bo p F deg j x) (F.dist j (F.oldest j x)) (((F.letters j).filter (fun y => Even y ∧ y < x ∧ ∀ l < r, y ≠ Arow F x l)).image (fun y => ((F.oldest j x - y) / 2).toNat)) (fun m => (dd (F.oldest j x - 2 * (m : ℤ)) : ℝ)) (by …`. Introduce `m hm`. Take `⟨y, hy, rfl⟩` from `Finset.mem_image.1 hm`. Take `⟨h1, h2⟩` from `hf y hy`.

Use `⟨h2, Nat.cast_nonneg _, ?_⟩` and prove the remaining obligations. Establish `h3 : F.oldest j x - 2 * ((((F.oldest j x - y) / 2).toNat : ℕ) : ℤ) = y` using `by omega`. Establish `h4 : F.dist j y = F.dist j (F.oldest j x) + 2 * ((F.oldest j x - y) / 2).toNat`. Use `(hY y hy).1` as an intermediate fact. Unfold `Frames.dist`.

Use linear arithmetic over natural numbers and integers. Use `show (dd (F.oldest j x - 2 * ((((F.oldest j x - y) / 2).toNat : ℕ) : ℤ)) : ℝ) ≤ _`. Rewrite using `[h3, ← h4, mul_div_assoc]`. Conclude with `hdd' y hy)`. Conclude with `le_trans g1 g2`.
-/
theorem restGeomU : RestGeomU := by
  intro p n' r _ F L₁ N₁ hp hr hn hV deg a hdeg j dd hdd x hx
  have hx1 : x ∈ F.letters j := (Finset.mem_filter.1 hx).1
  have hW : ¬ F.IsW j x := (Finset.mem_filter.1 hx).2
  obtain ⟨⟨ho1, ho2, ho3⟩, _⟩ := ge_oldest F L₁ N₁ hV (by omega) j x hx1 hW
  have ho1' := ho1
  unfold Frames.letters at ho1'
  rw [Finset.mem_filter, Finset.mem_Icc] at ho1'
  have hp0 : (0 : ℝ) < p := by
    have : (13 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have hY : ∀ y ∈ (F.letters j).filter (fun y => Even y ∧ y < x ∧ ∀ l < r, y ≠ Arow F x l),
      y < F.oldest j x ∧ Even y ∧ y ∈ F.letters j ∧ (F.IsW j y ∨ y ∈ F.LLset j) := by
    intro y hy
    rw [Finset.mem_filter] at hy
    obtain ⟨h1, h2, h3, h4⟩ := hy
    obtain ⟨h5, h6⟩ := ge_older F L₁ N₁ hV hn (by omega) j x hx1 hW y h1 h2 h3 h4
    exact ⟨h5, h2, h1, h6⟩
  have hlev : ∀ y ∈ F.letters j, levDeg p F deg j y ≤ 2 * ((a : ℝ) / (p : ℝ) ^ (F.dist j y)) := by
    intro y hy
    unfold Frames.letters at hy
    rw [Finset.mem_filter] at hy
    unfold levDeg
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (hdeg _ hy.2).2 (pow_pos hp0 _).le
  have hdd' : ∀ y ∈ (F.letters j).filter (fun y => Even y ∧ y < x ∧ ∀ l < r, y ≠ Arow F x l),
      (dd y : ℝ) ≤ 2.02 * ((a : ℝ) / (p : ℝ) ^ (F.dist j y)) := by
    intro y hy
    obtain ⟨_, _, h3, h4⟩ := hY y hy
    have h5 := hdd y h3 h4
    have h6 := hlev y h3
    linarith
  rw [Nat.cast_sum]
  by_cases ha : a = 0
  · have hz : ∀ y ∈ (F.letters j).filter (fun y => Even y ∧ y < x ∧ ∀ l < r, y ≠ Arow F x l),
        (dd y : ℝ) = 0 := by
      intro y hy
      have h1 := hdd' y hy
      rw [ha] at h1
      simp only [Nat.cast_zero, zero_div, mul_zero] at h1
      exact le_antisymm h1 (Nat.cast_nonneg _)
    rw [Finset.sum_eq_zero hz]
    have := level_degree_nonneg p F deg j x
    linarith
  · have hf : ∀ y ∈ (F.letters j).filter (fun y => Even y ∧ y < x ∧ ∀ l < r, y ≠ Arow F x l),
        ((((F.oldest j x - y) / 2).toNat : ℕ) : ℤ) * 2 = F.oldest j x - y ∧ 1 ≤ ((F.oldest j x - y) / 2).toNat := by
      intro y hy
      obtain ⟨h1, h2, _, _⟩ := hY y hy
      obtain ⟨k, hk⟩ := ho2.sub h2
      constructor <;> omega
    have hsum : ∑ y ∈ (F.letters j).filter (fun y => Even y ∧ y < x ∧ ∀ l < r, y ≠ Arow F x l), (dd y : ℝ) =
        ∑ m ∈ ((F.letters j).filter (fun y => Even y ∧ y < x ∧ ∀ l < r, y ≠ Arow F x l)).image
          (fun y => ((F.oldest j x - y) / 2).toNat), (dd (F.oldest j x - 2 * (m : ℤ)) : ℝ) := by
      rw [Finset.sum_image]
      · refine Finset.sum_congr rfl fun y hy => ?_
        have h1 := (hf y hy).1
        have h2 : F.oldest j x - 2 * ((((F.oldest j x - y) / 2).toNat : ℕ) : ℤ) = y := by omega
        rw [h2]
      · intro y1 hy1 y2 hy2 h
        have h1 := (hf y1 hy1).1
        have h2 := (hf y2 hy2).1
        have h' : ((F.oldest j x - y1) / 2).toNat = ((F.oldest j x - y2) / 2).toNat := h
        rw [h'] at h1
        omega
    rw [hsum]
    have hB : (a : ℝ) / (p : ℝ) ^ (F.dist j (F.oldest j x)) ≤ Bo p F deg j x := by
      unfold Bo levDeg
      exact div_le_div_of_nonneg_right (hdeg _ ho1'.2).1 (pow_pos hp0 _).le
    obtain ⟨g1, g2⟩ := Formalism.CountingSumsFrames.Top.lemma4Geom (p : ℝ) (a : ℝ) (Bo p F deg j x) (F.dist j (F.oldest j x))
      (((F.letters j).filter (fun y => Even y ∧ y < x ∧ ∀ l < r, y ≠ Arow F x l)).image
          (fun y => ((F.oldest j x - y) / 2).toNat)) (fun m => (dd (F.oldest j x - 2 * (m : ℤ)) : ℝ))
      (by exact_mod_cast hp) (by exact_mod_cast Nat.pos_of_ne_zero ha) hB (by
        intro m hm
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hm
        obtain ⟨h1, h2⟩ := hf y hy
        refine ⟨h2, Nat.cast_nonneg _, ?_⟩
        have h3 : F.oldest j x - 2 * ((((F.oldest j x - y) / 2).toNat : ℕ) : ℤ) = y := by omega
        have h4 : F.dist j y = F.dist j (F.oldest j x) + 2 * ((F.oldest j x - y) / 2).toNat := by
          have := (hY y hy).1
          unfold Frames.dist
          omega
        show (dd (F.oldest j x - 2 * ((((F.oldest j x - y) / 2).toNat : ℕ) : ℤ)) : ℝ) ≤ _
        rw [h3, ← h4, mul_div_assoc]
        exact hdd' y hy)
    exact le_trans g1 g2

/- English proof (translation)
Take `⟨C, hC, H⟩` from `numeric_symbol_bound_real`. Use `⟨C, hC, fun hGeom => ?_⟩` and prove the remaining obligations. Introduce `p n' r K _ _ _ _ O _ _ _ _ X deg a Y c0 c'' cStar Dd hII j dd hdd P hP`. Take `⟨d', d'', A, G, Mx, hA, hG, hsum, hW, hCM, hth, rfl⟩` from `hP`. Establish `hp` using `X.hH.1`.

Establish `hr` using `X.hH.2.1`. Establish `hn` using `X.hH.2.2.2.2`. Establish `hdeg : ∀ s ∈ X.Fr.TT, (a : ℝ) ≤ deg s ∧ (deg s : ℝ) ≤ 2 * a`. Establish `hII'` using `hII`. Unfold `Formalism.MainNotions.SourceCleaning.HypII at hII'`.

Take `⟨_, _, g3, _⟩` from `hII'`. Introduce `s hs`. Take `⟨h1, h2⟩` from `g3 s hs`. Establish `h0 : (0 : ℝ) ≤ (c'' : ℝ)` using `Nat.cast_nonneg _`. Conclude with `⟨by linarith, by linarith⟩`.

Establish `hms : (X.Fr.letters j).card * X.m1 (cPrime n' r X.Fr.TT.card c0 c'' cStar) + X.m2 (cPrime n' r X.Fr.TT.card c0 c'' cStar) ≤ mStar p X.Fr (r + K) X.N₁ (p ^ X.G') (cPrime n' r X.Fr.TT.card c0 c'' cStar)`. Unfold `Ctx.m1 Ctx.m2 Ctx.Q`. Conclude with `segment_divisions_le_bound p X.Fr (r + K) X.L₁ X.N₁ (p ^ X.G') _ X.hV j`. Use `dv_segment hE X.hV hn (by omega) j _ _ _ hms dd d' d'' A G Mx hA hG hW hCM (fun b => by have := hsum b; omega) ?_` and prove the remaining obligations. Introduce `i hiW`.

Consider the cases of `hv : valS (LLs X.Fr j).toLetters {y | y < i} A with`. Consider the case `top => exact le_top`. Consider the case `coe z`. Establish `h1` using `hth i hiW z hv`. Establish `hB` using `hGeom p n' r X.Fr X.L₁ X.N₁ hp hr hn X.hV deg a hdeg j dd hdd _ (dv_nonW_of j i hiW)`.

Take `⟨_, h2⟩` from `H n' r p X.Fr (r + K) X.L₁ X.N₁ X.G' deg a Y c0 c'' cStar Dd hp hr X.hV hII X.hT j _ (dv_eL_mem X.Fr j i) hiW`. Take `⟨h3, _⟩` from `h2 _ (z : ℝ) hB h1`. Establish `h0` using `level_degree_nonneg p X.Fr deg j (eL X.Fr j i)`. Establish `h4 : ((∑ y ∈ (X.Fr.letters j).filter (fun y => Even y ∧ y < eL X.Fr j i ∧ ∀ l < r, y ≠ Arow X.Fr (eL X.Fr j i) l), dd y : ℕ) : ℝ) + (mStar p X.Fr (r + K) X.N₁ (p ^ X.G') (cPrime n' r X.Fr.TT.card c0 c'' cStar) : ℝ) ≤ (z : ℝ)`. Combine the linear equalities and inequalities to obtain the conclusion.

Conclude with `WithTop.coe_le_coe.2 (by exact_mod_cast h4)`.
-/
theorem restDivMU (hE : FieldMultidegreeDivisibility) : ∃ C : ℝ, 1 ≤ C ∧ (RestGeomU → RestDivMU C (C + 1) C) := by
  obtain ⟨C, hC, H⟩ := numeric_symbol_bound_real
  refine ⟨C, hC, fun hGeom => ?_⟩
  intro p n' r K _ _ _ _ O _ _ _ _ X deg a Y c0 c'' cStar Dd hII j dd hdd P hP
  obtain ⟨d', d'', A, G, Mx, hA, hG, hsum, hW, hCM, hth, rfl⟩ := hP
  have hp := X.hH.1
  have hr := X.hH.2.1
  have hn := X.hH.2.2.2.2
  have hdeg : ∀ s ∈ X.Fr.TT, (a : ℝ) ≤ deg s ∧ (deg s : ℝ) ≤ 2 * a := by
    have hII' := hII
    unfold Formalism.MainNotions.SourceCleaning.HypII at hII'
    obtain ⟨_, _, g3, _⟩ := hII'
    intro s hs
    obtain ⟨h1, h2⟩ := g3 s hs
    have h0 : (0 : ℝ) ≤ (c'' : ℝ) := Nat.cast_nonneg _
    exact ⟨by linarith, by linarith⟩
  have hms : (X.Fr.letters j).card * X.m1 (cPrime n' r X.Fr.TT.card c0 c'' cStar) +
      X.m2 (cPrime n' r X.Fr.TT.card c0 c'' cStar) ≤
      mStar p X.Fr (r + K) X.N₁ (p ^ X.G') (cPrime n' r X.Fr.TT.card c0 c'' cStar) := by
    unfold Ctx.m1 Ctx.m2 Ctx.Q
    exact segment_divisions_le_bound p X.Fr (r + K) X.L₁ X.N₁ (p ^ X.G') _ X.hV j
  refine dv_segment hE X.hV hn (by omega) j _ _ _ hms dd d' d'' A G Mx hA hG hW hCM
    (fun b => by have := hsum b; omega) ?_
  intro i hiW
  cases hv : valS (LLs X.Fr j).toLetters {y | y < i} A with
  | top => exact le_top
  | coe z =>
    have h1 := hth i hiW z hv
    have hB := hGeom p n' r X.Fr X.L₁ X.N₁ hp hr hn X.hV deg a hdeg j dd hdd _ (dv_nonW_of j i hiW)
    obtain ⟨_, h2⟩ := H n' r p X.Fr (r + K) X.L₁ X.N₁ X.G' deg a Y c0 c'' cStar Dd hp hr X.hV hII X.hT j _
      (dv_eL_mem X.Fr j i) hiW
    obtain ⟨h3, _⟩ := h2 _ (z : ℝ) hB h1
    have h0 := level_degree_nonneg p X.Fr deg j (eL X.Fr j i)
    have h4 : ((∑ y ∈ (X.Fr.letters j).filter
        (fun y => Even y ∧ y < eL X.Fr j i ∧ ∀ l < r, y ≠ Arow X.Fr (eL X.Fr j i) l), dd y : ℕ) : ℝ) +
        (mStar p X.Fr (r + K) X.N₁ (p ^ X.G') (cPrime n' r X.Fr.TT.card c0 c'' cStar) : ℝ) ≤ (z : ℝ) := by
      linarith
    exact WithTop.coe_le_coe.2 (by exact_mod_cast h4)

/- English proof (translation)
Introduce `p n' r K _ _ _ _ O _ _ _ _ S hO hH Fr L₁ N₁ G' hV hT deg a Y c0 c'' cStar Dd hII c' g hg n obd xi dd hxi hdd mon hmon hmonT o ho`. Establish `hII'` using `hII`. Unfold `Formalism.MainNotions.SourceCleaning.HypII at hII'`. Take `⟨g1, _, _, _, _, g6, _⟩` from `hII'`. Set `X : Ctx p n' r K O` to `⟨S, hO, hH, Fr, L₁, N₁, G', hV, hT, g1, by omega, g, hg⟩`.

Establish `hA : ∀ (i : Fin n) (j : ℕ), ∃ ξ' : SegRing O r K, j < Fr.J → (xi i j = Dv Fr (j : ℤ) O K (X.m1 c') (X.m2 c') * ξ' ∧ MvPolynomial.map (algebraMap O (KK O)) (phSeg O K p Fr (j : ℤ) ξ') ∈ X.SyS)`. Introduce `i j`. Distinguish the cases in `hj : j < Fr.J`. Take `⟨ξ', h1, h2⟩` from `good_of_span X hW1 hW2 (j : ℤ) (Dv Fr (j : ℤ) O K (X.m1 c') (X.m2 c')) _ (hDiv p n' r K O X deg a Y c0 c'' cStar Dd hII (j : ℤ) (dd j) (hdd j hj)) (hModel O n' r K Fr (j : ℤ) _ _ _ (dd j) (xi i j) (hxi i j hj).1 (hxi i j hj).2)`. Conclude with `⟨ξ', fun _ => ⟨h1, h2⟩⟩`.

Conclude with `⟨0, fun h => absurd h hj⟩`. Use `choose ξ' hξ' using hA`. Take `⟨H, Y0, hH1, hY0, hPhe⟩` from `hPh p n' r K O X c'`. Take `⟨om, hom⟩` from `hMon p n' r K O X mon hmon hmonT`. Use `set Sg : MvPolynomial (TV n' (r + K)) (KK O) := ∑ i, ∏ j ∈ Finset.range Fr.J, MvPolynomial.map (algebraMap O (KK O)) (phSeg O K p Fr (j : ℤ) (ξ' i j)) with hSg`.

Establish `hSgS : Sg ∈ X.SyS` using `sum_mem fun i _ => SyS_prod _ _ fun j hj => (hξ' i j (Finset.mem_range.1 hj)).2`. Establish `hSg0 : InWj S.w Sg 0`. Use `inWj_sum _ _ fun i _ => inWj_prod0 _ _ fun j _ => inWj_map _` and prove the remaining obligations. Establish `hT : MvPolynomial.map (algebraMap O (KK O)) (monPh O K p Fr mon xi) = (monomial mon 1 * X.DkQ * Sg * H) * X.fixedSymbolFactor c' + C (algebraMap O (KK O) ((p : O) ^ c')) * (monomial mon 1 * Sg * Y0)`. Establish `e1 : monPh O K p Fr mon xi = monomial mon 1 * ((∑ i, ∏ j ∈ Finset.range Fr.J, phSeg O K p Fr (j : ℤ) (ξ' i j)) * ∏ j ∈ Finset.range Fr.J, phSeg O K p Fr (j : ℤ) (Dv Fr (j : ℤ) O K (X.m1 c') (X.m2 c')))`.

Unfold `monPh`. Use `congr 1`. Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.prod_mul_distrib]`.

Use `Finset.prod_congr rfl fun j hj => ?_` and prove the remaining obligations. Rewrite using `[(hξ' i j (Finset.mem_range.1 hj)).1, map_mul, mul_comm]`. Rewrite using `[e1, map_mul, map_mul, hPhe, map_monomial, map_one, map_sum]`. Simplify using `only [map_prod]`. Rewrite using `[← hSg]`.

Expand and normalize the polynomial expressions, which then agree. Use `core X D c' o _ (monomial mon 1 * X.DkQ * Sg * H) (monomial mon 1 * Sg * Y0) ?_ ?_ hT ?_` and prove the remaining obligations. Conclude with `SyS_mul (SyS_mul (SyS_of_Sy hom) hSgS) (SyS_of_Sy (Sy_IT hH1))`. Conclude with `inWPow_zero_mul (inWPow_zero_mul (bc_inWj_monomial S.w mon) hSg0) hY0`. Introduce `m hm`.

Conclude with `ho m (support_map_subset _ _ hm)`.
-/
theorem one_sided_lemma4_of_interfaces (D : Formalism.BasicNotions.D7) (CLa CD Csz : ℝ) (hModel : RestModel) (hDiv : RestDivMU CLa CD Csz)
    (hW1 : GeneratorSpanInclusion) (hW2 : GeneratorImageIsSymbol) (hMon : RestMon) (hPh : RestPh) : OneSidedLemma4 D CLa CD Csz := by
  intro p n' r K _ _ _ _ O _ _ _ _ S hO hH Fr L₁ N₁ G' hV hT deg a Y c0 c'' cStar Dd hII c' g hg n obd xi dd hxi hdd
    mon hmon hmonT o ho
  have hII' := hII
  unfold Formalism.MainNotions.SourceCleaning.HypII at hII'
  obtain ⟨g1, _, _, _, _, g6, _⟩ := hII'
  let X : Ctx p n' r K O := ⟨S, hO, hH, Fr, L₁, N₁, G', hV, hT, g1, by omega, g, hg⟩

  have hA : ∀ (i : Fin n) (j : ℕ), ∃ ξ' : SegRing O r K, j < Fr.J →
      (xi i j = Dv Fr (j : ℤ) O K (X.m1 c') (X.m2 c') * ξ' ∧
        MvPolynomial.map (algebraMap O (KK O)) (phSeg O K p Fr (j : ℤ) ξ') ∈ X.SyS) := by
    intro i j
    by_cases hj : j < Fr.J
    · obtain ⟨ξ', h1, h2⟩ := good_of_span X hW1 hW2 (j : ℤ) (Dv Fr (j : ℤ) O K (X.m1 c') (X.m2 c')) _
        (hDiv p n' r K O X deg a Y c0 c'' cStar Dd hII (j : ℤ) (dd j) (hdd j hj))
        (hModel O n' r K Fr (j : ℤ) _ _ _ (dd j) (xi i j) (hxi i j hj).1 (hxi i j hj).2)
      exact ⟨ξ', fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose ξ' hξ' using hA
  obtain ⟨H, Y0, hH1, hY0, hPhe⟩ := hPh p n' r K O X c'
  obtain ⟨om, hom⟩ := hMon p n' r K O X mon hmon hmonT

  set Sg : MvPolynomial (TV n' (r + K)) (KK O) :=
    ∑ i, ∏ j ∈ Finset.range Fr.J, MvPolynomial.map (algebraMap O (KK O)) (phSeg O K p Fr (j : ℤ) (ξ' i j)) with hSg
  have hSgS : Sg ∈ X.SyS := sum_mem fun i _ => SyS_prod _ _ fun j hj => (hξ' i j (Finset.mem_range.1 hj)).2
  have hSg0 : InWj S.w Sg 0 := by
    refine inWj_sum _ _ fun i _ => inWj_prod0 _ _ fun j _ => inWj_map _
  have hT : MvPolynomial.map (algebraMap O (KK O)) (monPh O K p Fr mon xi) =
      (monomial mon 1 * X.DkQ * Sg * H) * X.fixedSymbolFactor c' +
        C (algebraMap O (KK O) ((p : O) ^ c')) * (monomial mon 1 * Sg * Y0) := by
    have e1 : monPh O K p Fr mon xi = monomial mon 1 *
        ((∑ i, ∏ j ∈ Finset.range Fr.J, phSeg O K p Fr (j : ℤ) (ξ' i j)) *
          ∏ j ∈ Finset.range Fr.J, phSeg O K p Fr (j : ℤ) (Dv Fr (j : ℤ) O K (X.m1 c') (X.m2 c'))) := by
      unfold monPh
      congr 1
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun j hj => ?_
      rw [(hξ' i j (Finset.mem_range.1 hj)).1, map_mul, mul_comm]
    rw [e1, map_mul, map_mul, hPhe, map_monomial, map_one, map_sum]
    simp only [map_prod]
    rw [← hSg]
    ring
  refine core X D c' o _ (monomial mon 1 * X.DkQ * Sg * H) (monomial mon 1 * Sg * Y0) ?_ ?_ hT ?_
  · exact SyS_mul (SyS_mul (SyS_of_Sy hom) hSgS) (SyS_of_Sy (Sy_IT hH1))
  · exact inWPow_zero_mul (inWPow_zero_mul (bc_inWj_monomial S.w mon) hSg0) hY0
  · intro m hm
    exact ho m (support_map_subset _ _ hm)

/- English proof (translation)
Distinguish the cases in `hE : FieldMultidegreeDivisibility`. Take `⟨C, hC, hD⟩` from `restDivMU hE`. Conclude with `⟨C, hC, fun D hA3 hB1 hB2 hB3 hC1 _ => one_sided_lemma4_of_interfaces D C (C + 1) C restModel (hD restGeomU) (generator_pair_conditions_of_admitted D hA3 hB1) (generator_path_homogeneous_holds D hB2 hB3 hC1) (restMon D) restPh⟩`. Conclude with `⟨1, le_rfl, fun D _ _ _ _ _ h => absurd h hE⟩`.
-/
theorem one_sided_lemma4_of_admitted_lemmas : ∃ C : ℝ, 1 ≤ C ∧ ∀ D : Formalism.BasicNotions.D7, StandardMonomialSpanBis D → PathPairCorrespondence D → admB2 D → admB3 D → CoefficientValuationLemma D → LargePrimeLengthVanishing D →
    OneSidedLemma4 D C (C + 1) C := by
  by_cases hE : FieldMultidegreeDivisibility
  · obtain ⟨C, hC, hD⟩ := restDivMU hE
    exact ⟨C, hC, fun D hA3 hB1 hB2 hB3 hC1 _ => one_sided_lemma4_of_interfaces D C (C + 1) C restModel (hD restGeomU)
      (generator_pair_conditions_of_admitted D hA3 hB1) (generator_path_homogeneous_holds D hB2 hB3 hC1) (restMon D) restPh⟩
  · exact ⟨1, le_rfl, fun D _ _ _ _ _ h => absurd h hE⟩

/- English proof (translation)
Take `⟨C, hC, H⟩` from `one_sided_lemma4_of_admitted_lemmas`. Use `⟨C, hC, fun D CLa Ck Crk Cdeg hA => ?_⟩` and prove the remaining obligations. Take `⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h15, h16, h17, h18, _, h20, h21, _⟩` from `hA`. Conclude with `H D h15 h16 h17 h18 h20 h21`.
-/
theorem one_sided_lemma4_of_admitted_theorem_II : ∃ C : ℝ, 1 ≤ C ∧ ∀ (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ), tableLineDegreeFive.admitted D CLa Ck Crk Cdeg →
    OneSidedLemma4 D C (C + 1) C := by
  obtain ⟨C, hC, H⟩ := one_sided_lemma4_of_admitted_lemmas
  refine ⟨C, hC, fun D CLa Ck Crk Cdeg hA => ?_⟩
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h15, h16, h17, h18, _, h20, h21, _⟩ := hA
  exact H D h15 h16 h17 h18 h20 h21

end Formalism.MainNotions.TestSideCounting
