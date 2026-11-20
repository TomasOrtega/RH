import Formalism.LocalToGlobal.CharacterGerms.RowTiePAllSet
import Formalism.LocalToGlobal.CharacterGerms.RowTiePOActLog
import Formalism.LocalToGlobal.CharacterGerms.RowTieProj
import Formalism.LocalToGlobal.CharacterGerms.CoeffSubstEqSum
import Formalism.LocalToGlobal.CharacterGerms.RowTieCartFB
import Formalism.LocalToGlobal.CharacterGerms.RowTieCartAdd

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ RowTiePE0

namespace AllStart

variable {C : Type} [Field C]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [linAct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => by ring`.
-/
theorem linAct_sum {dd : ℕ} (φ : Pt C 1 dd) {ι : Type} (S : Finset ι) (w : ι → C) (u : ι → Fin dd → C) :
    linAct φ (∑ c ∈ S, w c • u c) = ∑ c ∈ S, w c • linAct φ (u c) := by
  funext i
  simp only [linAct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Establish `hA : MvPowerSeries.HasSubst P` using `MvPowerSeries.hasSubst_of_constantCoeff_zero hP0`. Rewrite using `[MvPowerSeries.coeff_subst hA]`. Use `finsum_eq_zero_of_forall_eq_zero fun μ => ?_` and prove the remaining obligations. Distinguish the cases in `hμ : μ.degree ≤ 1`. Rewrite using `[hf μ hμ, zero_smul]`.

Use `push_neg at hμ`. Establish `hX : ∀ q, (PowerSeries.X : PowerSeries C) ∣ P q` using `fun q => PowerSeries.X_dvd_iff.2 (hP0 q)`. Establish `hdeg : μ.degree = ∑ s ∈ μ.support, μ s` using `rfl`. Establish `h1 : (PowerSeries.X : PowerSeries C) ^ μ.degree ∣ μ.prod fun s e => P s ^ e`. Rewrite using `[hdeg, Finsupp.prod, ← Finset.prod_pow_eq_pow_sum]`.

Conclude with `Finset.prod_dvd_prod_of_dvd _ _ fun s _ => pow_dvd_pow_of_dvd (hX s) _`. Establish `hdvd : (PowerSeries.X : PowerSeries C) ^ 2 ∣ μ.prod fun s e => P s ^ e` using `(pow_dvd_pow _ hμ).trans h1`. Establish `h2` using `(PowerSeries.X_pow_dvd_iff.1 hdvd) 1 (by norm_num)`. Rewrite using `[show MvPowerSeries.coeff (Finsupp.single () 1) (μ.prod fun s e => P s ^ e) = 0 from h2, smul_zero]`.
-/
theorem coeff_one_subst {dd : ℕ} (f : PS C 1 dd)
    (hf : ∀ (μ : Fin 1 × Fin dd →₀ ℕ), μ.degree ≤ 1 → MvPowerSeries.coeff μ f = 0)
    (P : Fin 1 × Fin dd → PowerSeries C) (hP0 : ∀ q, MvPowerSeries.constantCoeff (P q) = 0) :
    MvPowerSeries.coeff (Finsupp.single () 1) (MvPowerSeries.subst P f) = 0 := by
  have hA : MvPowerSeries.HasSubst P := MvPowerSeries.hasSubst_of_constantCoeff_zero hP0
  rw [MvPowerSeries.coeff_subst hA]
  refine finsum_eq_zero_of_forall_eq_zero fun μ => ?_
  by_cases hμ : μ.degree ≤ 1
  · rw [hf μ hμ, zero_smul]
  · push_neg at hμ
    have hX : ∀ q, (PowerSeries.X : PowerSeries C) ∣ P q := fun q => PowerSeries.X_dvd_iff.2 (hP0 q)
    have hdeg : μ.degree = ∑ s ∈ μ.support, μ s := rfl
    have h1 : (PowerSeries.X : PowerSeries C) ^ μ.degree ∣ μ.prod fun s e => P s ^ e := by
      rw [hdeg, Finsupp.prod, ← Finset.prod_pow_eq_pow_sum]
      exact Finset.prod_dvd_prod_of_dvd _ _ fun s _ => pow_dvd_pow_of_dvd (hX s) _
    have hdvd : (PowerSeries.X : PowerSeries C) ^ 2 ∣ μ.prod fun s e => P s ^ e := (pow_dvd_pow _ hμ).trans h1
    have h2 := (PowerSeries.X_pow_dvd_iff.1 hdvd) 1 (by norm_num)
    rw [show MvPowerSeries.coeff (Finsupp.single () 1) (μ.prod fun s e => P s ^ e) = 0 from h2, smul_zero]

end AllStart

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd d : ℕ}
  {I : Fin 2 → Type} [∀ g, Fintype (I g)]

/- English proof (translation)
Take `⟨e, heI, he0, hhom, -, -, hfix, hspan, -⟩` from `hP`. Set `v : Fin dd → C` to `∑ c, w c • p.u g c`. Establish `hvI : ∀ j, V.Ge 0 (v j)` using `fun j => by`. Simplify using `only [v, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`. Conclude with `VF.Ge.sum fun c _ => (hw c).mul_int (p.u_int g c j)`.

Set `P : Fin 1 × Fin dd → PowerSeries C` to `fun q => MvPowerSeries.C (v q.2) * MvPowerSeries.X ()`. Establish `hP0 : ∀ q, MvPowerSeries.constantCoeff (P q) = 0` using `fun q => by`. Simplify using `[P]`. Establish `hPI : ∀ q, IntS V (P q)` using `fun q μ => by`. Simplify using `only [P, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X]`.

Use `split_ifs`. Rewrite using `[mul_one]`. Conclude with `hvI q.2`. Rewrite using `[mul_zero]`. Conclude with `VF.Ge.zero 0`.

Establish `hPS` using `MvPowerSeries.hasSubst_of_constantCoeff_zero hP0`. Set `a : ℕ → Fin dd → C` to `fun n j => PowerSeries.coeff n (MvPowerSeries.subst P (Y.lg j))`. Establish `ha1 : ∀ j, a 1 j = v j` using `fun j => by show MvPowerSeries.coeff (Finsupp.single () 1) (MvPowerSeries.subst P (Y.lg j)) = v j`. Establish `e1 : Y.lg j = MvPowerSeries.X ((0 : Fin 1), j) + (Y.lg j - MvPowerSeries.X ((0 : Fin 1), j))` using `by ring`. Establish `h0` using `AllStart.coeff_one_subst (Y.lg j - MvPowerSeries.X ((0 : Fin 1), j)) (fun μ hμ => by rw [map_sub, Y.lg_lin j μ hμ, sub_self]) P hP0`.

Rewrite using `[e1, MvPowerSeries.subst_add hPS, MvPowerSeries.subst_X hPS, map_add, h0, add_zero]`. Simplify using `[P, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X]`. Establish `hv : linAct (e g) v = v` using `by show linAct (e g) (∑ c, w c • p.u g c) = ∑ c, w c • p.u g c`. Rewrite using `[AllStart.linAct_sum]`. Conclude with `Finset.sum_congr rfl fun c _ => by rw [hfix g c]`.

Set `b : ℕ → I g → C` to `fun n => Classical.choose (hspan g (a n))`. Establish `hb : ∀ n, linAct (e g) (a n) = ∑ c, b n c • p.u g c` using `fun n => Classical.choose_spec (hspan g (a n))`. Set `Linl : ℕ → I g → C` to `fun n c => if n = 1 then w c else b n c`. Establish `hkey : ∀ n i, ∑ j, OActLog.linM (e g) i j * a n j = ∑ c, p.u g c i * Linl n c`. Introduce `n i`.

Establish `hl : ∑ j, OActLog.linM (e g) i j * a n j = linAct (e g) (a n) i` using `rfl`. Rewrite using `[hl]`. Distinguish the cases in `hn : n = 1`. Substitute `hn` using the available equality. Establish `e2 : a 1 = v` using `funext ha1`.

Rewrite using `[e2, hv]`. Simplify using `only [Linl, if_pos rfl, v, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`. Conclude with `Finset.sum_congr rfl fun c _ => mul_comm _ _`. Rewrite using `[hb n]`. Simplify using `only [Linl, if_neg hn, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`.

Conclude with `Finset.sum_congr rfl fun c _ => mul_comm _ _`. Set `γ : Fin dd → PowerSeries C` to `fun i => MvPowerSeries.subst P (e g i)`. Establish `hγ0 : ∀ i, MvPowerSeries.constantCoeff (γ i) = 0` using `fun i => constantCoeff_subst_zero hP0 (he0 g i)`. Establish `hγ : IsCv V γ` using `fun i => ⟨hγ0 i, fun n => IntS.subst hP0 hPI (heI g i) (Finsupp.single () n)⟩`. Establish `heS : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => e g q.2)` using `MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => he0 g q.2`.

Establish `hlog : ∀ i, alongCv γ ((Y.raw p).lg i) = ∑ c, (Y.raw p).u g c i • PowerSeries.mk (fun n => Linl n c)`. Introduce `i`. Establish `h1 : alongCv γ ((Y.raw p).lg i) = MvPowerSeries.subst P (comp1 Y.lg (e g) i)` using `by show MvPowerSeries.subst γ (un1 (Y.lg i)) = _`. Rewrite using `[subst_singlePointUncurry hγ0]`. Use `show MvPowerSeries.subst (fun q : Fin 1 × Fin dd => MvPowerSeries.subst P (e g q.2)) (Y.lg i) = MvPowerSeries.subst P (ev ![e g] (Y.lg i))`.

Rewrite using `[eval_single_eq_subst, MvPowerSeries.subst_comp_subst_apply heS hPS]`. Rewrite using `[h1, OActLog.log_endo Y.B.G Y.lg Y.lg_lin Y.lg_add (e g) (he0 g) (hhom g) i]`. Simplify using `only [← MvPowerSeries.smul_eq_C_mul]`. Rewrite using `[← MvPowerSeries.coe_substAlgHom hPS, map_sum]`. Simplify using `only [map_smul, MvPowerSeries.coe_substAlgHom hPS]`.

Use `PowerSeries.ext fun n => ?_` and prove the remaining obligations. Simplify using `only [map_sum, map_smul, smul_eq_mul, PowerSeries.coeff_mk]`. Conclude with `hkey n i`. Set `RHS : JJ I g → PowerSeries C` to `fun q => (0 : PowerSeries C) - alongCv γ ((Y.raw p).sg ((Y.raw p).u (1 - g) q)) + ∑ c : I g, if (Y.raw p).ty g c = (Y.raw p).ty (1 - g) q then (Y.raw p).sg1 ((Y.raw p).u g c) ((Y.raw p).u (1 - g) q) • PowerSeries.mk (fun n => Linl n c) else 0`. Set `L : ℕ → I g ⊕ JJ I g → C` to `fun n k => Sum.elim (fun c => Linl n c) (fun q => PowerSeries.coeff n (RHS q)) k`.

Use `⟨L, ⟨γ, fun _ => 0, hγ, fun q => ⟨by simp, fun n => by simpa using VF.Ge.zero (V := V) 0⟩, hlog, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `q`. Use `PowerSeries.ext fun n => ?_` and prove the remaining obligations. Rewrite using `[PowerSeries.coeff_mk]`. Both sides reduce to the same expression.

Introduce `c show (if 1 = 1 then w c else b 1 c) = w c`. Rewrite using `[if_pos rfl]`.
-/
theorem allStart_of_proj (Y : FBChart C V O dd) (p : PairData Y d I) (hP : ProjSt Y p) (g : Fin 2) (w : I g → C)
    (hw : ∀ c, V.Ge 0 (w c)) : ∃ L ∈ (Y.raw p).AllSet V g, ∀ c, L 1 (Sum.inl c) = w c := by
  obtain ⟨e, heI, he0, hhom, -, -, hfix, hspan, -⟩ := hP
  let v : Fin dd → C := ∑ c, w c • p.u g c
  have hvI : ∀ j, V.Ge 0 (v j) := fun j => by
    simp only [v, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact VF.Ge.sum fun c _ => (hw c).mul_int (p.u_int g c j)
  let P : Fin 1 × Fin dd → PowerSeries C := fun q =>
    MvPowerSeries.C (v q.2) * MvPowerSeries.X ()
  have hP0 : ∀ q, MvPowerSeries.constantCoeff (P q) = 0 := fun q => by
    simp [P]
  have hPI : ∀ q, IntS V (P q) := fun q μ => by
    simp only [P, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X]
    split_ifs
    · rw [mul_one]; exact hvI q.2
    · rw [mul_zero]; exact VF.Ge.zero 0
  have hPS := MvPowerSeries.hasSubst_of_constantCoeff_zero hP0
  let a : ℕ → Fin dd → C := fun n j => PowerSeries.coeff n (MvPowerSeries.subst P (Y.lg j))
  have ha1 : ∀ j, a 1 j = v j := fun j => by
    show MvPowerSeries.coeff (Finsupp.single () 1) (MvPowerSeries.subst P (Y.lg j)) = v j
    have e1 : Y.lg j = MvPowerSeries.X ((0 : Fin 1), j) + (Y.lg j - MvPowerSeries.X ((0 : Fin 1), j)) := by ring
    have h0 := AllStart.coeff_one_subst (Y.lg j - MvPowerSeries.X ((0 : Fin 1), j))
      (fun μ hμ => by rw [map_sub, Y.lg_lin j μ hμ, sub_self]) P hP0
    rw [e1, MvPowerSeries.subst_add hPS, MvPowerSeries.subst_X hPS, map_add, h0, add_zero]
    simp [P, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X]
  have hv : linAct (e g) v = v := by
    show linAct (e g) (∑ c, w c • p.u g c) = ∑ c, w c • p.u g c
    rw [AllStart.linAct_sum]
    exact Finset.sum_congr rfl fun c _ => by rw [hfix g c]
  let b : ℕ → I g → C := fun n => Classical.choose (hspan g (a n))
  have hb : ∀ n, linAct (e g) (a n) = ∑ c, b n c • p.u g c := fun n => Classical.choose_spec (hspan g (a n))
  let Linl : ℕ → I g → C := fun n c => if n = 1 then w c else b n c
  have hkey : ∀ n i, ∑ j, OActLog.linM (e g) i j * a n j = ∑ c, p.u g c i * Linl n c := by
    intro n i
    have hl : ∑ j, OActLog.linM (e g) i j * a n j = linAct (e g) (a n) i := rfl
    rw [hl]
    by_cases hn : n = 1
    · subst hn
      have e2 : a 1 = v := funext ha1
      rw [e2, hv]
      simp only [Linl, if_pos rfl, v, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun c _ => mul_comm _ _
    · rw [hb n]
      simp only [Linl, if_neg hn, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun c _ => mul_comm _ _
  let γ : Fin dd → PowerSeries C := fun i => MvPowerSeries.subst P (e g i)
  have hγ0 : ∀ i, MvPowerSeries.constantCoeff (γ i) = 0 := fun i => constantCoeff_subst_zero hP0 (he0 g i)
  have hγ : IsCv V γ := fun i => ⟨hγ0 i, fun n => IntS.subst hP0 hPI (heI g i) (Finsupp.single () n)⟩
  have heS : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => e g q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => he0 g q.2
  have hlog : ∀ i, alongCv γ ((Y.raw p).lg i) = ∑ c, (Y.raw p).u g c i • PowerSeries.mk (fun n => Linl n c) := by
    intro i
    have h1 : alongCv γ ((Y.raw p).lg i) = MvPowerSeries.subst P (comp1 Y.lg (e g) i) := by
      show MvPowerSeries.subst γ (un1 (Y.lg i)) = _
      rw [subst_singlePointUncurry hγ0]
      show MvPowerSeries.subst (fun q : Fin 1 × Fin dd => MvPowerSeries.subst P (e g q.2)) (Y.lg i) =
        MvPowerSeries.subst P (ev ![e g] (Y.lg i))
      rw [eval_single_eq_subst, MvPowerSeries.subst_comp_subst_apply heS hPS]
    rw [h1, OActLog.log_endo Y.B.G Y.lg Y.lg_lin Y.lg_add (e g) (he0 g) (hhom g) i]
    simp only [← MvPowerSeries.smul_eq_C_mul]
    rw [← MvPowerSeries.coe_substAlgHom hPS, map_sum]
    simp only [map_smul, MvPowerSeries.coe_substAlgHom hPS]
    refine PowerSeries.ext fun n => ?_
    simp only [map_sum, map_smul, smul_eq_mul, PowerSeries.coeff_mk]
    exact hkey n i
  let RHS : JJ I g → PowerSeries C := fun q =>
    (0 : PowerSeries C) - alongCv γ ((Y.raw p).sg ((Y.raw p).u (1 - g) q)) +
      ∑ c : I g, if (Y.raw p).ty g c = (Y.raw p).ty (1 - g) q then
        (Y.raw p).sg1 ((Y.raw p).u g c) ((Y.raw p).u (1 - g) q) • PowerSeries.mk (fun n => Linl n c) else 0
  let L : ℕ → I g ⊕ JJ I g → C := fun n k => Sum.elim (fun c => Linl n c) (fun q => PowerSeries.coeff n (RHS q)) k
  refine ⟨L, ⟨γ, fun _ => 0, hγ, fun q => ⟨by simp, fun n => by simpa using VF.Ge.zero (V := V) 0⟩, hlog, ?_⟩, ?_⟩
  · intro q
    refine PowerSeries.ext fun n => ?_
    rw [PowerSeries.coeff_mk]
    rfl
  · intro c
    show (if 1 = 1 then w c else b 1 c) = w c
    rw [if_pos rfl]

end Formalism.L2.FormalSeriesBounds
