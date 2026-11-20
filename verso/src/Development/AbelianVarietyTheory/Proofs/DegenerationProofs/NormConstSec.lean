import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsZpowMulIsUnitOfMem
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ValUnitNeZero
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH GlobalTheory.ZH.FrameNorm

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace GlobalTheory.ZH.FrameNorm
open CrdCalc

/- English proof (translation)
Introduce `p _ V _ _ _ K _ _ _ σ jV hj hloc H HK f j q hs hg hK X L M ψ ω hL hM hω nH nK nX hnj hnψ n α hα`. Establish `ej : ∀ x : Sp (PadicAlgCl p) ⟶ HK, (x ≫ nK) ≫ j = (x ≫ j) ≫ nH` using `fun x => by`. Rewrite using `[Category.assoc, hnj, Category.assoc]`. Establish `eψ : ∀ x : Sp (PadicAlgCl p) ⟶ HK, (x ≫ nK) ≫ ψ = (x ≫ ψ) ≫ nX` using `fun x => by`. Rewrite using `[Category.assoc, hnψ, Category.assoc]`.

Establish `w₀ : ∀ m, LB.wchart L ![𝟙 X, nX] m ≤ L.U (m 0)` using `fun m => LB.wchart_le L ![𝟙 X, nX] m 0`. Establish `w₁ : ∀ m, LB.wchart L ![𝟙 X, nX] m ≤ nX ⁻¹ᵁ L.U (m 1)` using `fun m => LB.wchart_le L ![𝟙 X, nX] m 1`. Establish `l₁ : ∀ {x : Sp (PadicAlgCl p) ⟶ HK} {a : M.ι × M.ι}, ⊤ ≤ (x ≫ j) ⁻¹ᵁ (M.U a.1 ⊓ nH ⁻¹ᵁ M.U a.2) → ⊤ ≤ ((x ≫ nK) ≫ j) ⁻¹ᵁ M.U a.2` using `fun h => by`. Rewrite using `[ej]`. Conclude with `fun _ hz => (h hz).2`.

Establish `m₁ : ∀ {x : Sp (PadicAlgCl p) ⟶ HK} {m}, ⊤ ≤ x ⁻¹ᵁ ψ ⁻¹ᵁ LB.wchart L ![𝟙 X, nX] m → ⊤ ≤ ((x ≫ nK) ≫ ψ) ⁻¹ᵁ L.U (m 1)` using `fun h => by`. Rewrite using `[eψ]`. Conclude with `fun _ hz => w₁ _ (h hz)`. Take `⟨κ, hκ, h⟩` from `norm_const p V K σ jV hj hloc H HK f j q hs hg hK (M.ι × M.ι) (Fin 2 → L.ι) (fun a => M.U a.1 ⊓ nH ⁻¹ᵁ M.U a.2) (fun m => ψ ⁻¹ᵁ LB.wchart L ![𝟙 X, nX] m) (fun a m x => valR (x ≫ ψ) (LB.wchart L ![𝟙 X, nX] m) (α.s m).val * ω x a.1 (m 0) ^ n ^ 2 * (ω (x ≫ nK) a.2 (m 1))⁻¹) (fun z = …`. Establish `hm₀ : ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ L.U (m 0)` using `fun _ hz => w₀ _ (hm hz)`.

Establish `hm₀' : ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ L.U (m' 0)` using `fun _ hz => w₀ _ (hm' hz)`. Establish `e` using `(gen_val hα (x := x ≫ ψ) hm hm').trans (congrArg (· * _) (tv_linComb L _ _ (fun k _ hz => LB.wchart_le L ![𝟙 X, nX] m k (hm hz)) fun k _ hz => LB.wchart_le L ![𝟙 X, nX] m' k (hm' hz)))`. Rewrite `e` using `[Fin.prod_univ_two]`. Express the relevant statement in the definitionally equal form `valR (x ≫ ψ) (LB.wchart L ![𝟙 X, nX] m) (α.s m).val = tv L ((x ≫ ψ) ≫ 𝟙 X) (m 0) (m' 0) ^ ((n : ℤ) ^ 2) * tv L ((x ≫ ψ) ≫ nX) (m 1) (m' 1) ^ (-1 : ℤ) * valR (x ≫ ψ) (LB.wchart L ![𝟙 X, nX] m') (α.s m').val at e`. Rewrite `e` using `[Category.comp_id, ← eψ, zpow_neg_one, show ∀ z : PadicAlgCl p, z ^ ((n : ℤ) ^ 2) = z ^ n ^ 2 from fun z => by rw [← zpow_natCast, Nat.cast_pow]]`.

Use `beta_reduce`. Rewrite using `[e, ← hω.right x a.1 (m 0) (m' 0) (fun _ hz => (ha hz).1) hm₀ hm₀', ← hω.right (x ≫ nK) a.2 (m 1) (m' 1) (l₁ ha) (m₁ hm) (m₁ hm'), mul_pow, mul_inv]`. Use the proof step `ring)`. Use the proof step `(fun a a' => by`. Establish `e₁ : M.U a.1 ⊓ nH ⁻¹ᵁ M.U a.2 ⊓ (M.U a'.1 ⊓ nH ⁻¹ᵁ M.U a'.2) ≤ M.U a.1 ⊓ M.U a'.1` using `inf_le_inf inf_le_left inf_le_left`.

Establish `e₂ : M.U a.1 ⊓ nH ⁻¹ᵁ M.U a.2 ⊓ (M.U a'.1 ⊓ nH ⁻¹ᵁ M.U a'.2) ≤ nH ⁻¹ᵁ (M.U a.2 ⊓ M.U a'.2)` using `fun _ hz => ⟨hz.1.2, hz.2.2⟩`. Use `⟨res e₁ (M.g a.1 a'.1) ^ ((n ^ 2 : ℕ) : ℤ) * res e₂ (pullU nH _ (M.g a.2 a'.2)) ^ (-1 : ℤ), fun m x _ ha ha' hm => ?_⟩` and prove the remaining obligations. Establish `hh : ⊤ ≤ (x ≫ j) ⁻¹ᵁ (M.U a.1 ⊓ nH ⁻¹ᵁ M.U a.2 ⊓ (M.U a'.1 ⊓ nH ⁻¹ᵁ M.U a'.2))` using `fun _ hz => ⟨ha hz, ha' hz⟩`. Establish `v₁ : valR (x ≫ j) _ (res e₁ (M.g a.1 a'.1)).val = tv M (x ≫ j) a.1 a'.1` using `valR_res _ e₁ hh _`. Establish `v₂ : valR (x ≫ j) _ (res e₂ (pullU nH _ (M.g a.2 a'.2))).val = tv M ((x ≫ nK) ≫ j) a.2 a'.2`.

Rewrite using `[ej]`. Conclude with `val_res_pull _ nH e₂ hh _`. Use `beta_reduce`. Rewrite using `[Units.val_mul, valR_mul _ _ hh, val_zpow _ hh, val_zpow _ hh, v₁, v₂, zpow_natCast, zpow_neg_one, hω.left x a.1 a'.1 (m 0) (fun _ hz => (ha hz).1) (fun _ hz => (ha' hz).1) fun _ hz => w₀ _ (hm hz), hω.left (x ≫ nK) a.2 a'.2 (m 1) (l₁ ha) (l₁ ha') (m₁ hm), mul_pow, mul_inv]`. Use the proof step `ring)`.

Use `⟨κ, hκ, fun c x l l' m hc hx hq hl hl' hm hm' => h (l, l') m c x hc hx hq (fun _ hz => ⟨hl hz, hl' hz⟩) fun _ hz => Set.mem_iInter.2 fun k => ?_⟩` and prove the remaining obligations. Use `fin_cases k`. Conclude with `hm hz`. Conclude with `hm' hz`.
-/
theorem norm_const_gen : ∀ (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (K : Type) [Field K] [Algebra V K] [IsFractionRing V K] (σ : K →+* PadicAlgCl p) (jV : V →+* OO p), (∀ a, (jV a : PadicAlgCl p) = σ (algebraMap V K a)) → IsLocalHom jV → ∀ (H HK : Scheme.{0}) (f : H ⟶ Sp V) (j : HK ⟶ H) (q : HK ⟶ Sp K), Smooth f → GeometricallyIntegral f → IsPullback j q f (spMap (algebraMap V K)) → ∀ (X : Scheme.{0}) (L : LB X) (M : LB H) (ψ : HK ⟶ X) (ω : (Sp (PadicAlgCl p) ⟶ HK) → M.ι → L.ι → PadicAlgCl p), L.IsLB → M.IsLB → IsoVal q σ L M ψ j ω → ∀ (nH : H ⟶ H) (nK : HK ⟶ HK) (nX : X ⟶ X), nK ≫ j = j ≫ nH → nK ≫ ψ = ψ ≫ nX → ∀ (n : ℕ) (α : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, nX] ![(n : ℤ) ^ 2, -1])), α.IsGen → ∃ κ : ℝ, 0 < κ ∧ ∀ (c : Sp (OO p) ⟶ H) (x : Sp (PadicAlgCl p) ⟶ HK) (l l' : M.ι) (m : Fin 2 → L.ι), c ≫ f = spMap jV → x ≫ j = gPt p ≫ c → x ≫ q = spMap σ → ⊤ ≤ c ⁻¹ᵁ M.U l → ⊤ ≤ (c ≫ nH) ⁻¹ᵁ M.U l' → ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ L.U (m 0) → ⊤ ≤ (x ≫ ψ ≫ nX) ⁻¹ᵁ L.U (m 1) → ‖valR (x ≫ ψ) (LB.wchart L ![𝟙 X, nX] m) (α.s m).val * ω x l (m 0) ^ n ^ 2 * (ω (x ≫ nK) l' (m 1))⁻¹‖ = κ := by
  intro p _ V _ _ _ K _ _ _ σ jV hj hloc H HK f j q hs hg hK X L M ψ ω hL hM hω nH nK nX hnj hnψ n α hα
  have ej : ∀ x : Sp (PadicAlgCl p) ⟶ HK, (x ≫ nK) ≫ j = (x ≫ j) ≫ nH := fun x => by
    rw [Category.assoc, hnj, Category.assoc]
  have eψ : ∀ x : Sp (PadicAlgCl p) ⟶ HK, (x ≫ nK) ≫ ψ = (x ≫ ψ) ≫ nX := fun x => by
    rw [Category.assoc, hnψ, Category.assoc]
  have w₀ : ∀ m, LB.wchart L ![𝟙 X, nX] m ≤ L.U (m 0) := fun m => LB.wchart_le L ![𝟙 X, nX] m 0
  have w₁ : ∀ m, LB.wchart L ![𝟙 X, nX] m ≤ nX ⁻¹ᵁ L.U (m 1) := fun m => LB.wchart_le L ![𝟙 X, nX] m 1
  have l₁ : ∀ {x : Sp (PadicAlgCl p) ⟶ HK} {a : M.ι × M.ι}, ⊤ ≤ (x ≫ j) ⁻¹ᵁ (M.U a.1 ⊓ nH ⁻¹ᵁ M.U a.2) →
      ⊤ ≤ ((x ≫ nK) ≫ j) ⁻¹ᵁ M.U a.2 := fun h => by
    rw [ej]
    exact fun _ hz => (h hz).2
  have m₁ : ∀ {x : Sp (PadicAlgCl p) ⟶ HK} {m}, ⊤ ≤ x ⁻¹ᵁ ψ ⁻¹ᵁ LB.wchart L ![𝟙 X, nX] m →
      ⊤ ≤ ((x ≫ nK) ≫ ψ) ⁻¹ᵁ L.U (m 1) := fun h => by
    rw [eψ]
    exact fun _ hz => w₁ _ (h hz)
  obtain ⟨κ, hκ, h⟩ := norm_const p V K σ jV hj hloc H HK f j q hs hg hK (M.ι × M.ι) (Fin 2 → L.ι)
    (fun a => M.U a.1 ⊓ nH ⁻¹ᵁ M.U a.2) (fun m => ψ ⁻¹ᵁ LB.wchart L ![𝟙 X, nX] m)
    (fun a m x => valR (x ≫ ψ) (LB.wchart L ![𝟙 X, nX] m) (α.s m).val * ω x a.1 (m 0) ^ n ^ 2 *
      (ω (x ≫ nK) a.2 (m 1))⁻¹)
    (fun z => exists_chart (LB.isLB_linComb hL ![𝟙 X, nX] ![(n : ℤ) ^ 2, -1]) (ψ z))
    (fun a m => ((Reg.pull ψ inf_le_right _).mul
      (((hω.reg (𝟙 _) (j ⁻¹ᵁ (M.U a.1 ⊓ nH ⁻¹ᵁ M.U a.2) ⊓ ψ ⁻¹ᵁ LB.wchart L ![𝟙 X, nX] m) a.1 (m 0)
        (fun _ hz => hz.1.1) fun _ hz => w₀ _ hz.2).1).pow _)).mul
      (hω.reg nK _ a.2 (m 1) (by rw [hnj]; exact fun _ hz => hz.1.2) (by rw [hnψ]; exact fun _ hz => w₁ _ hz.2)).2)
    (fun a m x _ ha hm => mul_ne_zero (mul_ne_zero (val_unit_ne_zero (x ≫ ψ) (U := LB.wchart L ![𝟙 X, nX] m) hm _)
      (pow_ne_zero _ (hω.ne _ _ _ (fun _ hz => (ha hz).1) fun _ hz => w₀ _ (hm hz))))
      (inv_ne_zero (hω.ne _ _ _ (l₁ ha) (m₁ hm))))
    (fun a m m' x _ ha hm hm' => by
      have hm₀ : ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ L.U (m 0) := fun _ hz => w₀ _ (hm hz)
      have hm₀' : ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ L.U (m' 0) := fun _ hz => w₀ _ (hm' hz)
      have e := (gen_val hα (x := x ≫ ψ) hm hm').trans (congrArg (· * _) (tv_linComb L _ _
        (fun k _ hz => LB.wchart_le L ![𝟙 X, nX] m k (hm hz)) fun k _ hz => LB.wchart_le L ![𝟙 X, nX] m' k (hm' hz)))
      rw [Fin.prod_univ_two] at e
      change valR (x ≫ ψ) (LB.wchart L ![𝟙 X, nX] m) (α.s m).val =
        tv L ((x ≫ ψ) ≫ 𝟙 X) (m 0) (m' 0) ^ ((n : ℤ) ^ 2) * tv L ((x ≫ ψ) ≫ nX) (m 1) (m' 1) ^ (-1 : ℤ) *
        valR (x ≫ ψ) (LB.wchart L ![𝟙 X, nX] m') (α.s m').val at e
      rw [Category.comp_id, ← eψ, zpow_neg_one,
        show ∀ z : PadicAlgCl p, z ^ ((n : ℤ) ^ 2) = z ^ n ^ 2 from fun z => by rw [← zpow_natCast, Nat.cast_pow]] at e
      beta_reduce
      rw [e, ← hω.right x a.1 (m 0) (m' 0) (fun _ hz => (ha hz).1) hm₀ hm₀',
        ← hω.right (x ≫ nK) a.2 (m 1) (m' 1) (l₁ ha) (m₁ hm) (m₁ hm'), mul_pow, mul_inv]
      ring)
    (fun a a' => by
      have e₁ : M.U a.1 ⊓ nH ⁻¹ᵁ M.U a.2 ⊓ (M.U a'.1 ⊓ nH ⁻¹ᵁ M.U a'.2) ≤ M.U a.1 ⊓ M.U a'.1 :=
        inf_le_inf inf_le_left inf_le_left
      have e₂ : M.U a.1 ⊓ nH ⁻¹ᵁ M.U a.2 ⊓ (M.U a'.1 ⊓ nH ⁻¹ᵁ M.U a'.2) ≤ nH ⁻¹ᵁ (M.U a.2 ⊓ M.U a'.2) :=
        fun _ hz => ⟨hz.1.2, hz.2.2⟩
      refine ⟨res e₁ (M.g a.1 a'.1) ^ ((n ^ 2 : ℕ) : ℤ) * res e₂ (pullU nH _ (M.g a.2 a'.2)) ^ (-1 : ℤ),
        fun m x _ ha ha' hm => ?_⟩
      have hh : ⊤ ≤ (x ≫ j) ⁻¹ᵁ (M.U a.1 ⊓ nH ⁻¹ᵁ M.U a.2 ⊓ (M.U a'.1 ⊓ nH ⁻¹ᵁ M.U a'.2)) :=
        fun _ hz => ⟨ha hz, ha' hz⟩
      have v₁ : valR (x ≫ j) _ (res e₁ (M.g a.1 a'.1)).val = tv M (x ≫ j) a.1 a'.1 := valR_res _ e₁ hh _
      have v₂ : valR (x ≫ j) _ (res e₂ (pullU nH _ (M.g a.2 a'.2))).val = tv M ((x ≫ nK) ≫ j) a.2 a'.2 := by
        rw [ej]
        exact val_res_pull _ nH e₂ hh _
      beta_reduce
      rw [Units.val_mul, valR_mul _ _ hh, val_zpow _ hh, val_zpow _ hh, v₁, v₂, zpow_natCast, zpow_neg_one,
        hω.left x a.1 a'.1 (m 0) (fun _ hz => (ha hz).1) (fun _ hz => (ha' hz).1) fun _ hz => w₀ _ (hm hz),
        hω.left (x ≫ nK) a.2 a'.2 (m 1) (l₁ ha) (l₁ ha') (m₁ hm), mul_pow, mul_inv]
      ring)
  refine ⟨κ, hκ, fun c x l l' m hc hx hq hl hl' hm hm' => h (l, l') m c x hc hx hq (fun _ hz => ⟨hl hz, hl' hz⟩)
    fun _ hz => Set.mem_iInter.2 fun k => ?_⟩
  fin_cases k
  · exact hm hz
  · exact hm' hz

/- English proof (translation)
Introduce `p _ V _ _ _ K _ _ _ σ jV hj hloc H HK f j q hs hg hK X L M ψ ω hL hM hω Y π ψ' hψ N J _ s t b hlink hprim`. Substitute `hψ` using the available equality. Set `v : (Sp (PadicAlgCl p) ⟶ HK) → L.ι → J → PadicAlgCl p` to `fun x m i => valR (x ≫ ψ') (LB.wchart L (fun _ : Fin 1 => π) fun _ => m) ((s i).f fun _ => m)`. Set `w : (Sp (PadicAlgCl p) ⟶ H) → M.ι → J → PadicAlgCl p` to `fun x l i => valR x (LB.wchart M (fun _ : Fin 1 => 𝟙 H) fun _ => l) ((t i).f fun _ => l)`. Establish `wl : ∀ l i, H.basicOpen ((t i).f fun _ => l) ≤ M.U l` using `fun l i => (H.basicOpen_le _).trans (LB.wchart_le M (fun _ : Fin 1 => 𝟙 H) (fun _ => l) 0)`.

Establish `wne : ∀ {x : Sp (PadicAlgCl p) ⟶ H} {l i}, ⊤ ≤ x ⁻¹ᵁ H.basicOpen ((t i).f fun _ => l) → w x l i ≠ 0` using `fun h => ((isUnit_valR_iff _ _ (fun _ hz => H.basicOpen_le _ (h hz)) _).2 h).ne_zero`. Establish `hv : ∀ x m m', ⊤ ≤ (x ≫ ψ' ≫ π) ⁻¹ᵁ L.U m → ⊤ ≤ (x ≫ ψ' ≫ π) ⁻¹ᵁ L.U m' → ∀ i, (b.map σ).mulVec (v x m) i = tv L (x ≫ ψ' ≫ π) m m' ^ N * (b.map σ).mulVec (v x m') i`. Introduce `x m m' hm hm' i`. Simplify using `only [Matrix.mulVec, dotProduct, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Establish `e` using `(sec_val (s k) (x := x ≫ ψ') (i := fun _ => m) (j := fun _ => m') (le_wchart fun _ => hm) (le_wchart fun _ => hm')).trans (congrArg (· * _) (tv_linComb L _ _ (fun _ => hm) fun _ => hm'))`. Rewrite `e` using `[Fin.prod_univ_one, zpow_natCast, Category.assoc]`. Rewrite using `[mul_left_comm]`. Conclude with `congrArg _ e`. Establish `hw : ∀ x l l', ⊤ ≤ x ⁻¹ᵁ M.U l → ⊤ ≤ x ⁻¹ᵁ M.U l' → ∀ i, w x l i = tv M x l l' ^ N * w x l' i`.

Introduce `x l l' hl hl' i`. Establish `e` using `(sec_val (t i) (x := x) (i := fun _ => l) (j := fun _ => l') (le_wchart fun _ => hl) (le_wchart fun _ => hl')).trans (congrArg (· * _) (tv_linComb M _ _ (fun _ => hl) fun _ => hl'))`. Rewrite `e` using `[Fin.prod_univ_one, zpow_natCast, Category.comp_id]`. Conclude with `e`. Establish `key : ∀ x l m, x ≫ q = spMap σ → ⊤ ≤ (x ≫ j) ⁻¹ᵁ M.U l → ⊤ ≤ (x ≫ ψ' ≫ π) ⁻¹ᵁ L.U m → ∃ c : PadicAlgCl p, c ≠ 0 ∧ ∀ i, (b.map σ).mulVec (v x m) i = c * w (x ≫ j) l i`.

Introduce `x l m hx hl hm`. Establish `h₁` using `hlink x (v x m) hx ⟨fun _ => m, 1, le_wchart fun _ => hm, fun i => (_root_.one_mul _).symm⟩`. Take `⟨c, hc⟩` from `crd_unique (s := t) (x := x ≫ j) (v := w (x ≫ j) l) ⟨fun _ => l, 1, fun _ hz => Set.mem_iInter.2 fun _ => hl hz, fun i => (_root_.one_mul _).symm⟩ h₁`. Conclude with `⟨c, c.ne_zero, hc⟩`. Take `⟨κ, hκ, h⟩` from `norm_const p V K σ jV hj hloc H HK f j q hs hg hK (J × M.ι) L.ι (fun a => H.basicOpen ((t a.1).f fun _ => a.2)) (fun m => (ψ' ≫ π) ⁻¹ᵁ L.U m) (fun a m x => (b.map σ).mulVec (v x m) a.1 * ω x a.2 m ^ N * (w (x ≫ j) a.2 a.1)⁻¹) (fun z => exists_chart hL _) (fun a m => ((Reg.sum fun …`.

Take `⟨c, hc, e⟩` from `key x a.2 m hx (fun _ hz => wl _ _ (ha hz)) hm`. Conclude with `mul_ne_zero (mul_ne_zero ((e _).trans_ne (mul_ne_zero hc (wne ha))) (pow_ne_zero _ (hω.ne _ _ _ (fun _ hz => wl _ _ (ha hz)) hm))) (inv_ne_zero (wne ha)))`. Use the proof step `(fun a m m' x _ ha hm hm' => by beta_reduce`. Rewrite using `[hv x m m' hm hm', ← hω.right x a.2 m m' (fun _ hz => wl _ _ (ha hz)) hm hm', mul_pow]`. Use the proof step `ring)`.

Use the proof step `(fun a a' => ⟨1, fun m x hx ha ha' hm => by`. Establish `hl : ⊤ ≤ (x ≫ j) ⁻¹ᵁ M.U a.2` using `fun _ hz => wl _ _ (ha hz)`. Establish `hl' : ⊤ ≤ (x ≫ j) ⁻¹ᵁ M.U a'.2` using `fun _ hz => wl _ _ (ha' hz)`. Take `⟨c, -, e⟩` from `key x a.2 m hx hl hm`. Establish `h₁` using `wne ha`.

Establish `h₂` using `wne ha'`. Use `beta_reduce`. Rewrite using `[valR_eq (x ≫ j) (H.basicOpen ((t a.1).f fun _ => a.2) ⊓ H.basicOpen ((t a'.1).f fun _ => a'.2)) (le_inf ha ha'), Units.val_one, map_one, e, e, hw _ a.2 a'.2 hl hl' a'.1, hω.left x a.2 a'.2 m hl hl' hm, mul_pow]`. Use the proof step `field_simp⟩)`. Use `⟨κ, hκ, fun c x l m hc hx hq hl hm => ?_⟩` and prove the remaining obligations.

Establish `hlw : ⊤ ≤ c ⁻¹ᵁ LB.wchart M (fun _ : Fin 1 => 𝟙 H) fun _ => l` using `fun _ hz => Set.mem_iInter.2 fun _ => hl hz`. Take `⟨i₀, hi₀⟩` from `hprim c _ hc ⟨fun _ => l, 1, hlw, fun i => (_root_.one_mul _).symm⟩`. Establish `hwc : ∀ i, w (x ≫ j) l i = (valR c _ ((t i).f fun _ => l) : OO p)` using `fun i => by`. Rewrite using `[hx]`. Conclude with `(valR_spMap (OO p).subtype c _ hlw).2 _`.

Establish `hle : ∀ i, ‖w (x ≫ j) l i‖ ≤ 1` using `fun i => by`. Rewrite using `[hwc]`. Conclude with `(mem_OO_iff _).1 (Subtype.prop _)`. Establish `h1 : ‖w (x ≫ j) l i₀‖ = 1`. Take `⟨d, hd⟩` from `hi₀.exists_right_inv`.

Establish `e : w (x ≫ j) l i₀ * (d : PadicAlgCl p) = 1`. Rewrite using `[hwc]`. Conclude with `congrArg Subtype.val hd`. Establish `e'` using `congrArg norm e`. Rewrite `e'` using `[norm_mul, norm_one]`.

Conclude with `le_antisymm (hle _) (e'.ge.trans (mul_le_of_le_one_right (norm_nonneg _) ((mem_OO_iff _).1 d.2)))`. Take `⟨d, -, e⟩` from `key x l m hq (by rw [hx]; exact fun _ _ => hl trivial) hm`. Establish `h₀` using `h (i₀, l) m c x hc hx hq ((isUnit_valR_iff _ _ hlw _).1 hi₀) hm`. Establish `hd : ∀ i, ‖(b.map σ).mulVec (v x m) i * ω x l m ^ N‖ = κ * ‖w (x ≫ j) l i‖` using `fun i => by`. Rewrite using `[← h₀]`.

Simplify using `only [e, norm_mul, norm_inv, h1]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨⟨i₀, (hd i₀).trans (by rw [h1, _root_.mul_one])⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `(hd i).trans_le (mul_le_of_le_one_right hκ.le (hle i))`.
-/
theorem norm_const_sec : ∀ (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (K : Type) [Field K] [Algebra V K] [IsFractionRing V K] (σ : K →+* PadicAlgCl p) (jV : V →+* OO p), (∀ a, (jV a : PadicAlgCl p) = σ (algebraMap V K a)) → IsLocalHom jV → ∀ (H HK : Scheme.{0}) (f : H ⟶ Sp V) (j : HK ⟶ H) (q : HK ⟶ Sp K), Smooth f → GeometricallyIntegral f → IsPullback j q f (spMap (algebraMap V K)) → ∀ (X : Scheme.{0}) (L : LB X) (M : LB H) (ψ : HK ⟶ X) (ω : (Sp (PadicAlgCl p) ⟶ HK) → M.ι → L.ι → PadicAlgCl p), L.IsLB → M.IsLB → IsoVal q σ L M ψ j ω → ∀ (Y : Scheme.{0}) (π : Y ⟶ X) (ψ' : HK ⟶ Y), ψ' ≫ π = ψ → ∀ (N : ℕ) (J : Type) [Fintype J] (s : J → (LB.LinComb L (K := Fin 1) (fun _ => π) (fun _ => (N : ℤ))).Sec) (t : J → (LB.LinComb M (K := Fin 1) (fun _ => 𝟙 H) (fun _ => (N : ℤ))).Sec) (b : Matrix J J K), (∀ (x : Sp (PadicAlgCl p) ⟶ HK) v, x ≫ q = spMap σ → Crd _ s (x ≫ ψ') v → Crd _ t (x ≫ j) ((b.map σ).mulVec v)) → (∀ (c : Sp (OO p) ⟶ H) w, c ≫ f = spMap jV → Crd _ t c w → ∃ i, IsUnit (w i)) → ∃ κ : ℝ, 0 < κ ∧ ∀ (c : Sp (OO p) ⟶ H) (x : Sp (PadicAlgCl p) ⟶ HK) (l : M.ι) (m : L.ι), c ≫ f = spMap jV → x ≫ j = gPt p ≫ c → x ≫ q = spMap σ → ⊤ ≤ c ⁻¹ᵁ M.U l → ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ L.U m → IsGreatest (Set.range fun i => ‖(b.map σ).mulVec (fun i => valR (x ≫ ψ') (LB.wchart L (fun _ : Fin 1 => π) (fun _ => m)) ((s i).f fun _ => m)) i * ω x l m ^ N‖) κ := by
  intro p _ V _ _ _ K _ _ _ σ jV hj hloc H HK f j q hs hg hK X L M ψ ω hL hM hω Y π ψ' hψ N J _ s t b hlink hprim
  subst hψ
  let v : (Sp (PadicAlgCl p) ⟶ HK) → L.ι → J → PadicAlgCl p := fun x m i =>
    valR (x ≫ ψ') (LB.wchart L (fun _ : Fin 1 => π) fun _ => m) ((s i).f fun _ => m)
  let w : (Sp (PadicAlgCl p) ⟶ H) → M.ι → J → PadicAlgCl p := fun x l i =>
    valR x (LB.wchart M (fun _ : Fin 1 => 𝟙 H) fun _ => l) ((t i).f fun _ => l)
  have wl : ∀ l i, H.basicOpen ((t i).f fun _ => l) ≤ M.U l := fun l i =>
    (H.basicOpen_le _).trans (LB.wchart_le M (fun _ : Fin 1 => 𝟙 H) (fun _ => l) 0)
  have wne : ∀ {x : Sp (PadicAlgCl p) ⟶ H} {l i}, ⊤ ≤ x ⁻¹ᵁ H.basicOpen ((t i).f fun _ => l) → w x l i ≠ 0 :=
    fun h => ((isUnit_valR_iff _ _ (fun _ hz => H.basicOpen_le _ (h hz)) _).2 h).ne_zero
  have hv : ∀ x m m', ⊤ ≤ (x ≫ ψ' ≫ π) ⁻¹ᵁ L.U m → ⊤ ≤ (x ≫ ψ' ≫ π) ⁻¹ᵁ L.U m' → ∀ i,
      (b.map σ).mulVec (v x m) i = tv L (x ≫ ψ' ≫ π) m m' ^ N * (b.map σ).mulVec (v x m') i := by
    intro x m m' hm hm' i
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have e := (sec_val (s k) (x := x ≫ ψ') (i := fun _ => m) (j := fun _ => m') (le_wchart fun _ => hm)
      (le_wchart fun _ => hm')).trans (congrArg (· * _) (tv_linComb L _ _ (fun _ => hm) fun _ => hm'))
    rw [Fin.prod_univ_one, zpow_natCast, Category.assoc] at e
    rw [mul_left_comm]
    exact congrArg _ e
  have hw : ∀ x l l', ⊤ ≤ x ⁻¹ᵁ M.U l → ⊤ ≤ x ⁻¹ᵁ M.U l' → ∀ i, w x l i = tv M x l l' ^ N * w x l' i := by
    intro x l l' hl hl' i
    have e := (sec_val (t i) (x := x) (i := fun _ => l) (j := fun _ => l') (le_wchart fun _ => hl)
      (le_wchart fun _ => hl')).trans (congrArg (· * _) (tv_linComb M _ _ (fun _ => hl) fun _ => hl'))
    rw [Fin.prod_univ_one, zpow_natCast, Category.comp_id] at e
    exact e
  have key : ∀ x l m, x ≫ q = spMap σ → ⊤ ≤ (x ≫ j) ⁻¹ᵁ M.U l → ⊤ ≤ (x ≫ ψ' ≫ π) ⁻¹ᵁ L.U m →
      ∃ c : PadicAlgCl p, c ≠ 0 ∧ ∀ i, (b.map σ).mulVec (v x m) i = c * w (x ≫ j) l i := by
    intro x l m hx hl hm
    have h₁ := hlink x (v x m) hx ⟨fun _ => m, 1, le_wchart fun _ => hm, fun i => (_root_.one_mul _).symm⟩
    obtain ⟨c, hc⟩ := crd_unique (s := t) (x := x ≫ j) (v := w (x ≫ j) l)
      ⟨fun _ => l, 1, fun _ hz => Set.mem_iInter.2 fun _ => hl hz, fun i => (_root_.one_mul _).symm⟩ h₁
    exact ⟨c, c.ne_zero, hc⟩
  obtain ⟨κ, hκ, h⟩ := norm_const p V K σ jV hj hloc H HK f j q hs hg hK (J × M.ι) L.ι
    (fun a => H.basicOpen ((t a.1).f fun _ => a.2)) (fun m => (ψ' ≫ π) ⁻¹ᵁ L.U m)
    (fun a m x => (b.map σ).mulVec (v x m) a.1 * ω x a.2 m ^ N * (w (x ≫ j) a.2 a.1)⁻¹)
    (fun z => exists_chart hL _)
    (fun a m => ((Reg.sum fun k => (Reg.const (b a.1 k)).mul (Reg.pull ψ' (U := LB.wchart L (fun _ : Fin 1 => π) fun _ => m)
        (W := j ⁻¹ᵁ H.basicOpen ((t a.1).f fun _ => a.2) ⊓ (ψ' ≫ π) ⁻¹ᵁ L.U m)
        (fun _ hz => Set.mem_iInter.2 fun _ => hz.2) ((s k).f fun _ => m))).mul
      (((hω.reg (𝟙 _) (j ⁻¹ᵁ H.basicOpen ((t a.1).f fun _ => a.2) ⊓ (ψ' ≫ π) ⁻¹ᵁ L.U m) a.2 m (fun _ hz => wl _ _ hz.1) fun _ hz => hz.2).1).pow _)).mul
      (Reg.inv_basicOpen j _ inf_le_left))
    (fun a m x hx ha hm => by
      obtain ⟨c, hc, e⟩ := key x a.2 m hx (fun _ hz => wl _ _ (ha hz)) hm
      exact mul_ne_zero (mul_ne_zero ((e _).trans_ne (mul_ne_zero hc (wne ha)))
        (pow_ne_zero _ (hω.ne _ _ _ (fun _ hz => wl _ _ (ha hz)) hm))) (inv_ne_zero (wne ha)))
    (fun a m m' x _ ha hm hm' => by
      beta_reduce
      rw [hv x m m' hm hm', ← hω.right x a.2 m m' (fun _ hz => wl _ _ (ha hz)) hm hm', mul_pow]
      ring)
    (fun a a' => ⟨1, fun m x hx ha ha' hm => by
      have hl : ⊤ ≤ (x ≫ j) ⁻¹ᵁ M.U a.2 := fun _ hz => wl _ _ (ha hz)
      have hl' : ⊤ ≤ (x ≫ j) ⁻¹ᵁ M.U a'.2 := fun _ hz => wl _ _ (ha' hz)
      obtain ⟨c, -, e⟩ := key x a.2 m hx hl hm
      have h₁ := wne ha
      have h₂ := wne ha'
      beta_reduce
      rw [valR_eq (x ≫ j) (H.basicOpen ((t a.1).f fun _ => a.2) ⊓ H.basicOpen ((t a'.1).f fun _ => a'.2))
        (le_inf ha ha'), Units.val_one, map_one, e, e,
        hw _ a.2 a'.2 hl hl' a'.1, hω.left x a.2 a'.2 m hl hl' hm, mul_pow]
      field_simp⟩)
  refine ⟨κ, hκ, fun c x l m hc hx hq hl hm => ?_⟩
  have hlw : ⊤ ≤ c ⁻¹ᵁ LB.wchart M (fun _ : Fin 1 => 𝟙 H) fun _ => l := fun _ hz => Set.mem_iInter.2 fun _ => hl hz
  obtain ⟨i₀, hi₀⟩ := hprim c _ hc ⟨fun _ => l, 1, hlw, fun i => (_root_.one_mul _).symm⟩
  have hwc : ∀ i, w (x ≫ j) l i = (valR c _ ((t i).f fun _ => l) : OO p) := fun i => by
    rw [hx]
    exact (valR_spMap (OO p).subtype c _ hlw).2 _
  have hle : ∀ i, ‖w (x ≫ j) l i‖ ≤ 1 := fun i => by
    rw [hwc]
    exact (mem_OO_iff _).1 (Subtype.prop _)
  have h1 : ‖w (x ≫ j) l i₀‖ = 1 := by
    obtain ⟨d, hd⟩ := hi₀.exists_right_inv
    have e : w (x ≫ j) l i₀ * (d : PadicAlgCl p) = 1 := by
      rw [hwc]
      exact congrArg Subtype.val hd
    have e' := congrArg norm e
    rw [norm_mul, norm_one] at e'
    exact le_antisymm (hle _) (e'.ge.trans (mul_le_of_le_one_right (norm_nonneg _) ((mem_OO_iff _).1 d.2)))
  obtain ⟨d, -, e⟩ := key x l m hq (by rw [hx]; exact fun _ _ => hl trivial) hm
  have h₀ := h (i₀, l) m c x hc hx hq ((isUnit_valR_iff _ _ hlw _).1 hi₀) hm
  have hd : ∀ i, ‖(b.map σ).mulVec (v x m) i * ω x l m ^ N‖ = κ * ‖w (x ≫ j) l i‖ := fun i => by
    rw [← h₀]
    simp only [e, norm_mul, norm_inv, h1]
    ring
  refine ⟨⟨i₀, (hd i₀).trans (by rw [h1, _root_.mul_one])⟩, ?_⟩
  rintro _ ⟨i, rfl⟩
  exact (hd i).trans_le (mul_le_of_le_one_right hκ.le (hle i))

end GlobalTheory.ZH.FrameNorm
end
