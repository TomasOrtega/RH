import Formalism.HermitianCurvature.HermitianCurvatureProofs.ImageProdLoc

namespace Formalism.FourierDecayAlt.P.PBC

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

/- English proof (translation)
Establish `hk : n * C.Kst = (n - 1) * C.Kst + C.Kst`. Establish `: n = (n - 1) + 1` using `by omega`. Use `conv_lhs => rw [this]`. Rewrite using `[add_mul, one_mul]`. Establish `hg' : (0 : ℝ) < S.g` using `by exact_mod_cast hg`.

Use `set L : Fin S.f → ℝ := fun v => Λ b (n - 1) v with hLdef`. Establish `hL0 : ∀ v, 0 ≤ L v` using `fun v => hΛ0 b (n - 1) hb (by omega) (by omega) v`. Take `⟨θL, hθL, hLV⟩` from `Formalism.FourierDecayAlt.P.lift_bound_below_top_all_places E Wp Wq S Λ hpos hLL ε hε (b + n - 2) (n - 1) (by omega) (by omega) (by omega) w' hw' (by omega)`. Establish `hΛi : b + n - 2 - (n - 1) + 1 = b` using `by omega`. Rewrite `hLV` using `[hΛi]`.

Use `choose! θ'' hθ'' using hP'`. Use `set Wd := S.base.Wb (S.base.cnt w' + n * C.Kst) with hWd`. Use `set pairs := S.base.Wb (S.base.cnt w' + C.Kst) ×ˢ S.base.Wb (S.base.cnt w' + C.Kst) with hpairs`. Establish `hpw : ∀ x ∈ pairs, (x.1 ∈ S.base.Wall ∧ S.base.cnt x.1 + (n - 1) * C.Kst ≤ S.Ntop ∧ S.base.Wb (S.base.cnt x.1 + (n - 1) * C.Kst) ⊆ Wd) ∧ (x.2 ∈ S.base.Wall ∧ S.base.cnt x.2 + (n - 1) * C.Kst ≤ S.Ntop ∧ S.base.Wb (S.base.cnt x.2 + (n - 1) * C.Kst) ⊆ Wd)`. Introduce `x hx`.

Rewrite `hx` using `[hpairs, Finset.mem_product, mem_Wb_iff, mem_Wb_iff]`. Conclude with `⟨⟨hx.1.1, by omega, Wb_mono S (by omega)⟩, ⟨hx.2.1, by omega, Wb_mono S (by omega)⟩⟩`. Establish `hpr : ∀ u, u ∈ S.base.Wall → S.base.cnt u + (n - 1) * C.Kst ≤ S.Ntop → TB.IsProb (S.base.Wb (S.base.cnt u + (n - 1) * C.Kst)) (θ'' u)` using `fun u h1 h2 => (hθ'' u h1 h2).1`. Set `q : crystallineComparison.V S.f → S.W → ℝ` to `fun σ u => ∑ x ∈ pairs, θL (crystallineComparison.pat L ((S.g : ℝ) • σ)) x * ((θ'' x.1 u + θ'' x.2 u) / 2)`. Establish `hq : ∀ σ, TB.IsProb Wd (q σ)`.

Introduce `σ`. Use `set A := crystallineComparison.pat L ((S.g : ℝ) • σ)`. Use `⟨fun u => Finset.sum_nonneg fun x hx => mul_nonneg ((hθL A).1 x) (div_nonneg (add_nonneg ((hpr _ (hpw x hx).1.1 (hpw x hx).1.2.1).1 u) ((hpr _ (hpw x hx).2.1 (hpw x hx).2.2.1).1 u)) (by norm_num)), fun u hu => Finset.sum_eq_zero fun x hx => ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : θ'' x.1 u = 0` using `(hpr _ (hpw x hx).1.1 (hpw x hx).1.2.1).2.1 u fun h => hu ((hpw x hx).1.2.2 h)`. Establish `h2 : θ'' x.2 u = 0` using `(hpr _ (hpw x hx).2.1 (hpw x hx).2.2.1).2.1 u fun h => hu ((hpw x hx).2.2.2 h)`.

Simplify using `[h1, h2]`. Use `show ∑ u ∈ Wd, ∑ x ∈ pairs, θL A x * ((θ'' x.1 u + θ'' x.2 u) / 2) = 1`. Rewrite using `[Finset.sum_comm, ← (hθL A).2.2]`. Use `Finset.sum_congr rfl fun x hx => ?_` and prove the remaining obligations. Rewrite using `[← Finset.mul_sum, ← Finset.sum_div, Finset.sum_add_distrib, prob_sum_sub (hpr _ (hpw x hx).1.1 (hpw x hx).1.2.1) (hpw x hx).1.2.2, prob_sum_sub (hpr _ (hpw x hx).2.1 (hpw x hx).2.2.1) (hpw x hx).2.2.2]`.

Evaluate the numerical expressions. Take `⟨θn, hθn, hmix⟩` from `tsum_mix Wd (fun σ : crystallineComparison.dualSet La => crystallineComparison.mL C.Kst L ((S.g : ℝ) • (σ : crystallineComparison.V S.f))) (fun σ => mL_nonneg _ _ hL0 _) hsm (by linarith [one_le_tsum_mL La C.Kst L hL0 (S.g : ℝ) hsm]) (fun σ => q σ) (fun σ => hq σ)`. Use `⟨θn, hθn, fun Y hY κ hκ z₀ Ss hS hgood => ?_⟩` and prove the remaining obligations. Take `⟨Pq, Qq, hreg, hGD⟩` from `germ_global S hpos hI hg Λ hLL hGL hΛ0 ε hε n hn b hb hbn w' hcnt Y hY`. Take `⟨Lm, j1, j2, hLm⟩` from `GlobalTheory.dual_smul_mem La (S.g : ℝ) hg'.ne'`.

Use `j1` as an intermediate fact. Use `j2` as an intermediate fact. Use `set N' : S.W → ℝ := fun u => P' * S.base.N0 ε (b - 1) u Y κ with hN'`. Set `D : Fin S.f → TB.Pt E → TB.Pt E → ℂ → ℂ` to `fun v h h' c => KB.gN S v ε (b + n - 1) (w'.1 v) (C.loc (S.σ v) h ++ [(n, c)]) (C.loc (S.σ v) h' ++ [(n, c)])`. Establish `hD : ∀ v (z : ℂ), z ≠ 0 → TB.PSDOn Y (fun h h' => D v h h' z)`.

Introduce `v z _`. Use `PBB.gN_psd S hpos v ε hε (b + n - 1) (by omega) w' (Y.image fun h => C.loc (S.σ v) h ++ [(n, z)])` as an intermediate fact. Conclude with `JCx1.decay.psd_pull _ _ this Y (fun h => C.loc (S.σ v) h ++ [(n, z)]) (fun h hh => Finset.mem_image_of_mem _ hh)`. Set `U : Fin S.f → TB.Pt E × ℂ → TB.Pt E × ℂ → ℂ` to `fun v p q => KB.gN S v ε (b + n - 2) (w'.1 v) (C.loc (S.σ v) p.1 ++ [(n - 1, p.2⁻¹)]) (C.loc (S.σ v) q.1 ++ [(n - 1, q.2⁻¹)])`. Establish `hsub : ∀ x' ∈ pairs, ∀ (t : crystallineComparison.V S.f), Good t → (KB.NstV S ε (b + n - 2) (n - 1) x'.1 Y κ t t).re ≤ ∑ u ∈ Wd, θ'' x'.1 u * N' u ∧ (KB.NstV S ε (b + n - 2) (n - 1) x'.2 Y κ t t).re ≤ ∑ u ∈ Wd, θ'' x'.2 u * N' u`.

Introduce `x' hx' t ht`. Establish `e : b + (n - 1) - 1 = b + n - 2` using `by omega`. Establish `h1` using `(hθ'' x'.1 (hpw x' hx').1.1 (hpw x' hx').1.2.1).2 Y hY κ hκ t ht`. Establish `h2` using `(hθ'' x'.2 (hpw x' hx').2.1 (hpw x' hx').2.2.1).2 Y hY κ hκ t ht`. Rewrite `h1`, `h2` using `[e]`.

Establish `s1 : ∑ u ∈ Wd, θ'' x'.1 u * N' u = P' * ∑ u ∈ S.base.Wb (S.base.cnt x'.1 + (n - 1) * C.Kst), θ'' x'.1 u * S.base.N0 ε (b - 1) u Y κ`. Rewrite using `[Finset.mul_sum, ← Finset.sum_subset (hpw x' hx').1.2.2 fun u _ hu => by`. Rewrite using `[(hpr _ (hpw x' hx').1.1 (hpw x' hx').1.2.1).2.1 u hu]`. Use the proof step `ring]`. Conclude with `Finset.sum_congr rfl fun u _ => by simp only [hN']; ring`.

Establish `s2 : ∑ u ∈ Wd, θ'' x'.2 u * N' u = P' * ∑ u ∈ S.base.Wb (S.base.cnt x'.2 + (n - 1) * C.Kst), θ'' x'.2 u * S.base.N0 ε (b - 1) u Y κ`. Rewrite using `[Finset.mul_sum, ← Finset.sum_subset (hpw x' hx').2.2.2 fun u _ hu => by`. Rewrite using `[(hpr _ (hpw x' hx').2.1 (hpw x' hx').2.2.1).2.1 u hu]`. Use the proof step `ring]`. Conclude with `Finset.sum_congr rfl fun u _ => by simp only [hN']; ring`.

Conclude with `⟨s1 ▸ h1, s2 ▸ h2⟩`. Establish `hF : ∀ σ ∈ crystallineComparison.dualSet La, ∀ x : crystallineComparison.V S.f, Good x → Good (x + (S.g : ℝ) • σ) → ‖phi Y κ U x (x + (S.g : ℝ) • σ)‖ ≤ crystallineComparison.mL C.Kst L ((S.g : ℝ) • σ) * ∑ u ∈ Wd, q σ u * N' u`. Introduce `σ _ x hx hx'`. Use `set t : crystallineComparison.V S.f := fun v => (x v)⁻¹ with ht_def`. Use `set t' : crystallineComparison.V S.f := fun v => ((x + (S.g : ℝ) • σ) v)⁻¹ with ht'_def`.

Establish `ht : Good t` using `fun v => inv_ne_zero (hx v)`. Establish `ht' : Good t'` using `fun v => inv_ne_zero (hx' v)`. Establish `ephi : phi Y κ U x (x + (S.g : ℝ) • σ) = KB.NstV S ε (b + n - 2) (n - 1) w' Y κ t t'`. Rewrite using `[nstV_eq]`. Both sides reduce to the same expression.

Establish `hlv` using `hLV Y κ κ κ (fun h hh => by rw [hY h hh]; omega) (blockPSD_same Y κ hκ) t t' ht ht' (crystallineComparison.pat L ((S.g : ℝ) • σ))`. Establish `ediff : ∀ v, (t v)⁻¹ - (t' v)⁻¹ = -(((S.g : ℝ) • σ) v)`. Introduce `v`. Simplify using `only [t, t', inv_inv, Pi.add_apply]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [ediff, norm_neg] at hlv`. Rewrite using `[ephi]`. Use `bound_mL C.Kst L hL0 _ _ _ (hlv.trans ?_)` and prove the remaining obligations. Use `mul_le_mul_of_nonneg_left ?_ (Finset.prod_nonneg fun v _ => pow_nonneg (hL0 v) _)` and prove the remaining obligations. Use `show _ ≤ ∑ u ∈ Wd, (∑ x ∈ pairs, θL (crystallineComparison.pat L ((S.g : ℝ) • σ)) x * ((θ'' x.1 u + θ'' x.2 u) / 2)) * N' u`.

Simplify using `only [Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_le_sum fun x' hx' => ?_` and prove the remaining obligations. Establish `hs` using `hsub x' hx'`. Establish `e2 : ∑ u ∈ Wd, θL (crystallineComparison.pat L ((S.g : ℝ) • σ)) x' * ((θ'' x'.1 u + θ'' x'.2 u) / 2) * N' u = θL (crystallineComparison.pat L ((S.g : ℝ) • σ)) x' * ((∑ u ∈ Wd, θ'' x'.1 u * N' u + ∑ u ∈ Wd, θ'' x'.2 u * N' u) / 2)`.

Rewrite using `[← Finset.sum_add_distrib, Finset.sum_div, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun u _ => by ring`. Rewrite using `[e2]`. Use `mul_le_mul_of_nonneg_left ?_ ((hθL _).1 x')` and prove the remaining obligations. Combine the linear relations using `[(hs t ht).1, (hs t' ht').2]`.

Establish `hH` using `herglotz_germ (H := TB.Pt E) Y κ hκ D hD (fun v h hh h' hh' => (hreg v h hh h' hh').1) (fun v h hh h' hh' => (hreg v h hh h' hh').2) (S.g : ℝ) hg' (fun _ => KB.dlB S b n) (fun _ => dlB_pos S hg b n) U Pq Qq (fun v σ h h' => KB.hatB S v ε b n (w'.1 v) σ (C.loc (S.σ v) h) (C.loc (S …`. Rewrite `hH` using `[(hmix N').2]`. Establish `hN : ∑ z ∈ Ss, Nz Y κ D z = ∑ z ∈ Ss, (KB.NstV S ε (b + n - 1) n w' Y κ z z).re` using `Finset.sum_congr rfl fun z hz => by`. Simplify using `only [Nz, if_pos (hgood z hz)]`. Rewrite using `[nstV_eq]`.

Both sides reduce to the same expression. Rewrite `hH` using `[hN]`. Use `hH.trans (le_of_eq ?_)` and prove the remaining obligations. Establish `e3 : ∑ u ∈ Wd, θn u * N' u = P' * ∑ u ∈ Wd, θn u * S.base.N0 ε (b - 1) u Y κ`. Rewrite using `[Finset.mul_sum]; exact Finset.sum_congr rfl fun u _ => by simp only [hN']; ring`.

Rewrite using `[e3]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem germ_step (S : C.HidaSetting E Wp Wq) (hpos : C.ThmPPos S) (hI : KB.IntAll S) (hg : 0 < S.g)
    (Λ : ℕ → ℕ → Fin S.f → ℝ) (hLL : ∀ v, KB.LiftLoc S v fun b s => Λ b s v) (hGL : ∀ v, KB.GermLoc S v)
    (hΛ0 : ∀ b s, 1 ≤ b → 1 ≤ s → b + s ≤ S.G.r + 1 → ∀ v, 0 ≤ Λ b s v) (ε : ℝ) (hε : 0 < ε) (n : ℕ)
    (hn : 2 ≤ n) (b : ℕ) (hb : 1 ≤ b) (hbn : b + n ≤ S.G.r + 2) (P' : ℝ) (hP' : GSup S ε b (n - 1) P')
    (hP'0 : 0 ≤ P') (w' : S.W) (hw' : w' ∈ S.base.Wall) (hcnt : S.base.cnt w' + n * C.Kst ≤ S.Ntop)
    (La : Submodule ℤ (crystallineComparison.V S.f)) [DiscreteTopology La] [IsZLattice ℝ La]
    (hsm : Summable fun σ : crystallineComparison.dualSet La => crystallineComparison.mL C.Kst (fun v => Λ b (n - 1) v) ((S.g : ℝ) • (σ : crystallineComparison.V S.f))) :
    ∃ θ : S.W → ℝ, TB.IsProb (S.base.Wb (S.base.cnt w' + n * C.Kst)) θ ∧
      ∀ Y : Finset (TB.Pt E), (∀ h ∈ Y, TB.level h = b - 1) → ∀ κ, TB.PSDOn Y κ →
        ∀ (z₀ : crystallineComparison.V S.f) (Ss : Finset (crystallineComparison.V S.f)), (∀ z ∈ Ss, z - z₀ ∈ La) → (∀ z ∈ Ss, Good z) →
          ZLattice.covolume La * ∑ z ∈ Ss, (KB.NstV S ε (b + n - 1) n w' Y κ z z).re ≤
            (∏ _v : Fin S.f, KB.dlB S b n) *
              ((∑' σ : crystallineComparison.dualSet La, crystallineComparison.mL C.Kst (fun v => Λ b (n - 1) v) ((S.g : ℝ) • (σ : crystallineComparison.V S.f))) * P') *
              ∑ u ∈ S.base.Wb (S.base.cnt w' + n * C.Kst), θ u * S.base.N0 ε (b - 1) u Y κ := by
  have hk : n * C.Kst = (n - 1) * C.Kst + C.Kst := by
    have : n = (n - 1) + 1 := by omega
    conv_lhs => rw [this]
    rw [add_mul, one_mul]
  have hg' : (0 : ℝ) < S.g := by exact_mod_cast hg
  set L : Fin S.f → ℝ := fun v => Λ b (n - 1) v with hLdef
  have hL0 : ∀ v, 0 ≤ L v := fun v => hΛ0 b (n - 1) hb (by omega) (by omega) v

  obtain ⟨θL, hθL, hLV⟩ := Formalism.FourierDecayAlt.P.lift_bound_below_top_all_places E Wp Wq S Λ hpos hLL ε hε (b + n - 2) (n - 1) (by omega)
    (by omega) (by omega) w' hw' (by omega)
  have hΛi : b + n - 2 - (n - 1) + 1 = b := by omega
  rw [hΛi] at hLV

  choose! θ'' hθ'' using hP'
  set Wd := S.base.Wb (S.base.cnt w' + n * C.Kst) with hWd
  set pairs := S.base.Wb (S.base.cnt w' + C.Kst) ×ˢ S.base.Wb (S.base.cnt w' + C.Kst) with hpairs
  have hpw : ∀ x ∈ pairs, (x.1 ∈ S.base.Wall ∧ S.base.cnt x.1 + (n - 1) * C.Kst ≤ S.Ntop ∧
      S.base.Wb (S.base.cnt x.1 + (n - 1) * C.Kst) ⊆ Wd) ∧
      (x.2 ∈ S.base.Wall ∧ S.base.cnt x.2 + (n - 1) * C.Kst ≤ S.Ntop ∧
      S.base.Wb (S.base.cnt x.2 + (n - 1) * C.Kst) ⊆ Wd) := by
    intro x hx
    rw [hpairs, Finset.mem_product, mem_Wb_iff, mem_Wb_iff] at hx
    exact ⟨⟨hx.1.1, by omega, Wb_mono S (by omega)⟩, ⟨hx.2.1, by omega, Wb_mono S (by omega)⟩⟩
  have hpr : ∀ u, u ∈ S.base.Wall → S.base.cnt u + (n - 1) * C.Kst ≤ S.Ntop →
      TB.IsProb (S.base.Wb (S.base.cnt u + (n - 1) * C.Kst)) (θ'' u) := fun u h1 h2 => (hθ'' u h1 h2).1
  let q : crystallineComparison.V S.f → S.W → ℝ := fun σ u =>
    ∑ x ∈ pairs, θL (crystallineComparison.pat L ((S.g : ℝ) • σ)) x * ((θ'' x.1 u + θ'' x.2 u) / 2)
  have hq : ∀ σ, TB.IsProb Wd (q σ) := by
    intro σ
    set A := crystallineComparison.pat L ((S.g : ℝ) • σ)
    refine ⟨fun u => Finset.sum_nonneg fun x hx => mul_nonneg ((hθL A).1 x) (div_nonneg (add_nonneg
      ((hpr _ (hpw x hx).1.1 (hpw x hx).1.2.1).1 u) ((hpr _ (hpw x hx).2.1 (hpw x hx).2.2.1).1 u)) (by norm_num)),
      fun u hu => Finset.sum_eq_zero fun x hx => ?_, ?_⟩
    · have h1 : θ'' x.1 u = 0 := (hpr _ (hpw x hx).1.1 (hpw x hx).1.2.1).2.1 u fun h => hu ((hpw x hx).1.2.2 h)
      have h2 : θ'' x.2 u = 0 := (hpr _ (hpw x hx).2.1 (hpw x hx).2.2.1).2.1 u fun h => hu ((hpw x hx).2.2.2 h)
      simp [h1, h2]
    · show ∑ u ∈ Wd, ∑ x ∈ pairs, θL A x * ((θ'' x.1 u + θ'' x.2 u) / 2) = 1
      rw [Finset.sum_comm, ← (hθL A).2.2]
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [← Finset.mul_sum, ← Finset.sum_div, Finset.sum_add_distrib,
        prob_sum_sub (hpr _ (hpw x hx).1.1 (hpw x hx).1.2.1) (hpw x hx).1.2.2,
        prob_sum_sub (hpr _ (hpw x hx).2.1 (hpw x hx).2.2.1) (hpw x hx).2.2.2]
      norm_num
  obtain ⟨θn, hθn, hmix⟩ := tsum_mix Wd (fun σ : crystallineComparison.dualSet La => crystallineComparison.mL C.Kst L ((S.g : ℝ) • (σ : crystallineComparison.V S.f)))
    (fun σ => mL_nonneg _ _ hL0 _) hsm
    (by linarith [one_le_tsum_mL La C.Kst L hL0 (S.g : ℝ) hsm]) (fun σ => q σ) (fun σ => hq σ)
  refine ⟨θn, hθn, fun Y hY κ hκ z₀ Ss hS hgood => ?_⟩
  obtain ⟨Pq, Qq, hreg, hGD⟩ := germ_global S hpos hI hg Λ hLL hGL hΛ0 ε hε n hn b hb hbn w' hcnt Y hY
  obtain ⟨Lm, j1, j2, hLm⟩ := GlobalTheory.dual_smul_mem La (S.g : ℝ) hg'.ne'
  have := j1; have := j2
  set N' : S.W → ℝ := fun u => P' * S.base.N0 ε (b - 1) u Y κ with hN'
  let D : Fin S.f → TB.Pt E → TB.Pt E → ℂ → ℂ := fun v h h' c =>
    KB.gN S v ε (b + n - 1) (w'.1 v) (C.loc (S.σ v) h ++ [(n, c)]) (C.loc (S.σ v) h' ++ [(n, c)])
  have hD : ∀ v (z : ℂ), z ≠ 0 → TB.PSDOn Y (fun h h' => D v h h' z) := by
    intro v z _
    have := PBB.gN_psd S hpos v ε hε (b + n - 1) (by omega) w' (Y.image fun h => C.loc (S.σ v) h ++ [(n, z)])
    exact JCx1.decay.psd_pull _ _ this Y (fun h => C.loc (S.σ v) h ++ [(n, z)])
      (fun h hh => Finset.mem_image_of_mem _ hh)
  let U : Fin S.f → TB.Pt E × ℂ → TB.Pt E × ℂ → ℂ := fun v p q =>
    KB.gN S v ε (b + n - 2) (w'.1 v) (C.loc (S.σ v) p.1 ++ [(n - 1, p.2⁻¹)]) (C.loc (S.σ v) q.1 ++ [(n - 1, q.2⁻¹)])
  have hsub : ∀ x' ∈ pairs, ∀ (t : crystallineComparison.V S.f), Good t →
      (KB.NstV S ε (b + n - 2) (n - 1) x'.1 Y κ t t).re ≤ ∑ u ∈ Wd, θ'' x'.1 u * N' u ∧
      (KB.NstV S ε (b + n - 2) (n - 1) x'.2 Y κ t t).re ≤ ∑ u ∈ Wd, θ'' x'.2 u * N' u := by
    intro x' hx' t ht
    have e : b + (n - 1) - 1 = b + n - 2 := by omega
    have h1 := (hθ'' x'.1 (hpw x' hx').1.1 (hpw x' hx').1.2.1).2 Y hY κ hκ t ht
    have h2 := (hθ'' x'.2 (hpw x' hx').2.1 (hpw x' hx').2.2.1).2 Y hY κ hκ t ht
    rw [e] at h1 h2
    have s1 : ∑ u ∈ Wd, θ'' x'.1 u * N' u =
        P' * ∑ u ∈ S.base.Wb (S.base.cnt x'.1 + (n - 1) * C.Kst), θ'' x'.1 u * S.base.N0 ε (b - 1) u Y κ := by
      rw [Finset.mul_sum, ← Finset.sum_subset (hpw x' hx').1.2.2 fun u _ hu => by
        rw [(hpr _ (hpw x' hx').1.1 (hpw x' hx').1.2.1).2.1 u hu]; ring]
      exact Finset.sum_congr rfl fun u _ => by simp only [hN']; ring
    have s2 : ∑ u ∈ Wd, θ'' x'.2 u * N' u =
        P' * ∑ u ∈ S.base.Wb (S.base.cnt x'.2 + (n - 1) * C.Kst), θ'' x'.2 u * S.base.N0 ε (b - 1) u Y κ := by
      rw [Finset.mul_sum, ← Finset.sum_subset (hpw x' hx').2.2.2 fun u _ hu => by
        rw [(hpr _ (hpw x' hx').2.1 (hpw x' hx').2.2.1).2.1 u hu]; ring]
      exact Finset.sum_congr rfl fun u _ => by simp only [hN']; ring
    exact ⟨s1 ▸ h1, s2 ▸ h2⟩
  have hF : ∀ σ ∈ crystallineComparison.dualSet La, ∀ x : crystallineComparison.V S.f, Good x → Good (x + (S.g : ℝ) • σ) →
      ‖phi Y κ U x (x + (S.g : ℝ) • σ)‖ ≤
        crystallineComparison.mL C.Kst L ((S.g : ℝ) • σ) * ∑ u ∈ Wd, q σ u * N' u := by
    intro σ _ x hx hx'
    set t : crystallineComparison.V S.f := fun v => (x v)⁻¹ with ht_def
    set t' : crystallineComparison.V S.f := fun v => ((x + (S.g : ℝ) • σ) v)⁻¹ with ht'_def
    have ht : Good t := fun v => inv_ne_zero (hx v)
    have ht' : Good t' := fun v => inv_ne_zero (hx' v)
    have ephi : phi Y κ U x (x + (S.g : ℝ) • σ) = KB.NstV S ε (b + n - 2) (n - 1) w' Y κ t t' := by
      rw [nstV_eq]; rfl
    have hlv := hLV Y κ κ κ (fun h hh => by rw [hY h hh]; omega) (blockPSD_same Y κ hκ) t t' ht ht'
      (crystallineComparison.pat L ((S.g : ℝ) • σ))
    have ediff : ∀ v, (t v)⁻¹ - (t' v)⁻¹ = -(((S.g : ℝ) • σ) v) := by
      intro v; simp only [t, t', inv_inv, Pi.add_apply]; ring
    simp only [ediff, norm_neg] at hlv
    rw [ephi]
    refine bound_mL C.Kst L hL0 _ _ _ (hlv.trans ?_)
    refine mul_le_mul_of_nonneg_left ?_ (Finset.prod_nonneg fun v _ => pow_nonneg (hL0 v) _)
    show _ ≤ ∑ u ∈ Wd, (∑ x ∈ pairs, θL (crystallineComparison.pat L ((S.g : ℝ) • σ)) x * ((θ'' x.1 u + θ'' x.2 u) / 2)) * N' u
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun x' hx' => ?_
    have hs := hsub x' hx'
    have e2 : ∑ u ∈ Wd, θL (crystallineComparison.pat L ((S.g : ℝ) • σ)) x' * ((θ'' x'.1 u + θ'' x'.2 u) / 2) * N' u =
        θL (crystallineComparison.pat L ((S.g : ℝ) • σ)) x' * ((∑ u ∈ Wd, θ'' x'.1 u * N' u + ∑ u ∈ Wd, θ'' x'.2 u * N' u) / 2) := by
      rw [← Finset.sum_add_distrib, Finset.sum_div, Finset.mul_sum]
      exact Finset.sum_congr rfl fun u _ => by ring
    rw [e2]
    refine mul_le_mul_of_nonneg_left ?_ ((hθL _).1 x')
    linarith [(hs t ht).1, (hs t' ht').2]
  have hH := herglotz_germ (H := TB.Pt E) Y κ hκ D hD (fun v h hh h' hh' => (hreg v h hh h' hh').1)
    (fun v h hh h' hh' => (hreg v h hh h' hh').2) (S.g : ℝ) hg' (fun _ => KB.dlB S b n)
    (fun _ => dlB_pos S hg b n) U Pq Qq
    (fun v σ h h' => KB.hatB S v ε b n (w'.1 v) σ (C.loc (S.σ v) h) (C.loc (S.σ v) h')) hGD
    (fun _ _ _ _ => rfl) La Lm hLm
    (fun σ : crystallineComparison.V S.f => crystallineComparison.mL C.Kst L ((S.g : ℝ) • σ) * ∑ u ∈ Wd, q σ u * N' u) (hmix N').1 hF z₀ Ss hS
  rw [(hmix N').2] at hH
  have hN : ∑ z ∈ Ss, Nz Y κ D z = ∑ z ∈ Ss, (KB.NstV S ε (b + n - 1) n w' Y κ z z).re :=
    Finset.sum_congr rfl fun z hz => by
      simp only [Nz, if_pos (hgood z hz)]
      rw [nstV_eq]
      rfl
  rw [hN] at hH
  refine hH.trans (le_of_eq ?_)
  have e3 : ∑ u ∈ Wd, θn u * N' u = P' * ∑ u ∈ Wd, θn u * S.base.N0 ε (b - 1) u Y κ := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun u _ => by simp only [hN']; ring
  rw [e3]
  ring

end

end Formalism.FourierDecayAlt.P.PBC
