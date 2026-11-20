import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.HeckeDoubleCosets.PHeckeFormal

noncomputable section

open UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.AffineStabilizerVanishing

open PositivityTheory.KB

section

variable {G K : Type} [Group G] [Group K]

/- English proof (translation)
Unfold `Gq`. Simplify using `[MulAut.conj_apply]`.
-/
theorem mem_Gq {ρ : G →* K} {q : K} {δ : G} : δ ∈ Gq ρ q ↔ ∃ γ, q⁻¹ * ρ γ * q = ρ δ := by
  unfold Gq
  simp [MulAut.conj_apply]

/- English proof (translation)
Take `⟨γ, hγ⟩` from `mem_Gq.mp h`. Establish `hρ : ρ γ = q * ρ b * (ρ a)⁻¹ * q⁻¹`. Rewrite `hγ` using `[map_mul, map_inv]`. Combine the equalities or inequalities in the displayed calculation. Establish `key : (fun j => q * ρ b * y j) = fun j => ρ γ • (q * ρ a * y j)`.

Use function extensionality and compare the values at `j`. Rewrite using `[smul_eq_mul, hρ]`. Use `group`. Rewrite using `[key]`. Conclude with `hF γ _`.
-/
theorem F_rep {m : ℕ} (ρ : G →* K) (q : K) (F : (Fin (m + 1) → K) → ℝ) (hF : Inv ρ F) (a b : G)
    (h : b * a⁻¹ ∈ Gq ρ q) (y : Fin (m + 1) → K) :
    F (fun j => q * ρ b * y j) = F (fun j => q * ρ a * y j) := by
  obtain ⟨γ, hγ⟩ := mem_Gq.mp h
  have hρ : ρ γ = q * ρ b * (ρ a)⁻¹ * q⁻¹ := by
    rw [map_mul, map_inv] at hγ
    calc ρ γ = q * (q⁻¹ * ρ γ * q) * q⁻¹ := by group
      _ = q * ρ b * (ρ a)⁻¹ * q⁻¹ := by rw [hγ]; group
  have key : (fun j => q * ρ b * y j) = fun j => ρ γ • (q * ρ a * y j) := by
    funext j
    rw [smul_eq_mul, hρ]
    group
  rw [key]
  exact hF γ _

/- English proof (translation)
Establish `hx` using `Quotient.mk_out (s := QuotientGroup.rightRel s) (c.out * g)`. Conclude with `QuotientGroup.rightRel_apply.mp hx`.
-/
theorem rel_out_mul (s : Subgroup G) (c : Quotient (QuotientGroup.rightRel s)) (g : G) :
    (c.out * g) * (Quotient.mk'' (c.out * g) : Quotient (QuotientGroup.rightRel s)).out⁻¹ ∈ s := by
  have hx := Quotient.mk_out (s := QuotientGroup.rightRel s) (c.out * g)
  exact QuotientGroup.rightRel_apply.mp hx

def actQ (s : Subgroup G) (c : Quotient (QuotientGroup.rightRel s)) (g : G) : Quotient (QuotientGroup.rightRel s) :=
  Quotient.mk'' (c.out * g)

/- English proof (translation)
Simplify using `[actQ]`.
-/
theorem actQ_one (s : Subgroup G) (c : Quotient (QuotientGroup.rightRel s)) : actQ s c 1 = c := by
  simp [actQ]

/- English proof (translation)
Unfold `actQ`. Apply `Quotient.sound'` to reduce the goal to its premises. Apply `QuotientGroup.rightRel_apply.mpr` to reduce the goal to its premises. Use `s.inv_mem (rel_out_mul s c g) using 1` and compare the differences between its conclusion and the goal. Use `group`.
-/
theorem actQ_mul (s : Subgroup G) (c : Quotient (QuotientGroup.rightRel s)) (g h : G) :
    actQ s c (g * h) = actQ s (actQ s c g) h := by
  unfold actQ
  apply Quotient.sound'
  apply QuotientGroup.rightRel_apply.mpr
  convert s.inv_mem (rel_out_mul s c g) using 1
  group

/- English proof (translation)
Use `Function.bijective_iff_has_inverse.2 ⟨fun c => actQ s c g⁻¹, fun c => ?_, fun c => ?_⟩` and prove the remaining obligations. Use `show actQ s (actQ s c g) g⁻¹ = c`. Rewrite using `[← actQ_mul, mul_inv_cancel, actQ_one]`. Use `show actQ s (actQ s c g⁻¹) g = c`. Rewrite using `[← actQ_mul, inv_mul_cancel, actQ_one]`.
-/
theorem actQ_bij (s : Subgroup G) (g : G) : Function.Bijective fun c => actQ s c g := by
  refine Function.bijective_iff_has_inverse.2 ⟨fun c => actQ s c g⁻¹, fun c => ?_, fun c => ?_⟩
  · show actQ s (actQ s c g) g⁻¹ = c
    rw [← actQ_mul, mul_inv_cancel, actQ_one]
  · show actQ s (actQ s c g⁻¹) g = c
    rw [← actQ_mul, inv_mul_cancel, actQ_one]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem hecke_apply {m : ℕ} (ρ : G →* K) (q : K) (F : (Fin (m + 1) → K) → ℝ) (y : Fin (m + 1) → K) :
    hecke ρ (MonoidHom.id K) q F y =
      ((Gq ρ q).index : ℝ)⁻¹ * ∑ᶠ c : Quotient (QuotientGroup.rightRel (Gq ρ q)), F (fun j => q * ρ c.out * y j) :=
  rfl

end

/- English proof (translation)
Introduce `G K _ _ ρ q hfin m F F' c hF`. Use `haveI := Fintype.ofFinite (Quotient (QuotientGroup.rightRel (Gq ρ q)))`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `g y`. Rewrite using `[hecke_apply, hecke_apply]`.

Use `congr 1`. Use `Eq.trans ?_ (finsum_comp_equiv (Equiv.ofBijective _ (actQ_bij (Gq ρ q) g)))` and prove the remaining obligations. Apply `finsum_congr` to reduce the goal to its premises. Introduce `c'`. Simplify using `only [Equiv.ofBijective_apply]`.

Rewrite using `[← F_rep ρ q F hF (actQ (Gq ρ q) c' g).out (c'.out * g) (rel_out_mul _ c' g) y]`. Use `congr 1`. Use function extensionality and compare the values at `j`. Rewrite using `[smul_eq_mul, map_mul]`. Use `group`.

Use function extensionality and compare the values at `y`. Rewrite using `[hecke_apply]`. Unfold `dC`. Simplify using `only [hecke_apply, finsum_eq_sum_of_fintype, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun i _ => ?_))` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Use function extensionality and compare the values at `y`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hecke_apply, finsum_eq_sum_of_fintype, Finset.sum_add_distrib, ← Finset.mul_sum]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pHeckeFormal : PHeckeFormal := by
  intro G K _ _ ρ q hfin m F F' c hF
  haveI := Fintype.ofFinite (Quotient (QuotientGroup.rightRel (Gq ρ q)))
  refine ⟨?_, ?_, ?_⟩
  · intro g y
    rw [hecke_apply, hecke_apply]
    congr 1
    refine Eq.trans ?_ (finsum_comp_equiv (Equiv.ofBijective _ (actQ_bij (Gq ρ q) g)))
    apply finsum_congr
    intro c'
    simp only [Equiv.ofBijective_apply]
    rw [← F_rep ρ q F hF (actQ (Gq ρ q) c' g).out (c'.out * g) (rel_out_mul _ c' g) y]
    congr 1
    funext j
    rw [smul_eq_mul, map_mul]
    group
  · funext y
    rw [hecke_apply]
    unfold dC
    simp only [hecke_apply, finsum_eq_sum_of_fintype, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun i _ => ?_))
    ring
  · funext y
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hecke_apply, finsum_eq_sum_of_fintype,
      Finset.sum_add_distrib, ← Finset.mul_sum]
    ring

/- English proof (translation)
Establish `hc : ∀ (j : Fin (m + 1)) (g : Fin (m + 1) → G), (fun i => f (Fin.contractNth j (· * ·) g i)) = Fin.contractNth j (· * ·) (fun i => f (g i))` using `fun j g => Fin.comp_contractNth _ _ (map_mul f) j g`. Establish `key : (bd H m).comp (cmap f (m + 1)) = (cmap f m).comp (bd G m)`. Apply `Finsupp.lhom_ext` to reduce the goal to its premises. Introduce `g r`. Simplify using `[bd, cmap, Finsupp.mapDomain_single, map_sum, Finsupp.mapDomain_add, Finsupp.mapDomain_smul, hc]`.

Rewrite using `[Finsupp.mapDomain_finset_sum]`. Simplify using `only [Finsupp.mapDomain_single, hc]`. Conclude with `LinearMap.congr_fun key z`.
-/
theorem bd_cmap {G H : Type} [Group G] [Group H] (f : G →* H) (m : ℕ) (z : Chn G (m + 1)) :
    bd H m (cmap f (m + 1) z) = cmap f m (bd G m z) := by
  have hc : ∀ (j : Fin (m + 1)) (g : Fin (m + 1) → G),
      (fun i => f (Fin.contractNth j (· * ·) g i)) = Fin.contractNth j (· * ·) (fun i => f (g i)) :=
    fun j g => Fin.comp_contractNth _ _ (map_mul f) j g
  have key : (bd H m).comp (cmap f (m + 1)) = (cmap f m).comp (bd G m) := by
    apply Finsupp.lhom_ext
    intro g r
    simp [bd, cmap, Finsupp.mapDomain_single, map_sum, Finsupp.mapDomain_add, Finsupp.mapDomain_smul, hc]
    rw [Finsupp.mapDomain_finset_sum]
    simp only [Finsupp.mapDomain_single, hc]
  exact LinearMap.congr_fun key z

/- English proof (translation)
Introduce `hSEv G K _ _ ρ hρ q hfin m F hF hdF hcyc z hz`. Use `haveI := Fintype.ofFinite (Quotient (QuotientGroup.rightRel (Gq ρ q)))`. Establish `heq : ∀ (c : Quotient (QuotientGroup.rightRel (Gq ρ q))) (g : G) (y : Fin (m + 2) → G), ((Gq ρ q).index : ℝ)⁻¹ * F (fun j => q * ρ (actQ (Gq ρ q) c g).out * ρ (y j)) = ((Gq ρ q).index : ℝ)⁻¹ * F (fun j => q * ρ c.out * ρ (g * y j))`. Introduce `c g y`. Establish `e` using `F_rep ρ q F hF (actQ (Gq ρ q) c g).out (c.out * g) (rel_out_mul _ c g) (fun j => ρ (y j))`.

Rewrite using `[← e]`. Use `congr 1`. Use `congr 1`. Use function extensionality and compare the values at `j`. Rewrite using `[map_mul, map_mul]`.

Use `group`. Establish `hcoc : ∀ c : Quotient (QuotientGroup.rightRel (Gq ρ q)), dC (fun y : Fin (m + 2) → G => ((Gq ρ q).index : ℝ)⁻¹ * F (fun j => q * ρ c.out * ρ (y j))) = 0`. Introduce `c`. Use function extensionality and compare the values at `y`. Establish `h` using `congrFun hdF (fun j => q * ρ c.out * ρ (y j))`.

Unfold `dC at h ⊢`. Simplify using `only [Pi.zero_apply] at h ⊢`. Rewrite using `[← mul_zero (((Gq ρ q).index : ℝ)⁻¹), ← h, Finset.mul_sum]`. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Establish `hpp : ∀ {S T : Type} [Group S] [Group T] (φ : S →* T) {n : ℕ} (g : Fin n → S) (j : Fin (n + 1)), Fin.partialProd (fun i => φ (g i)) j = φ (Fin.partialProd g j)`. Introduce `S T _ _ φ n g j`. Use `Fin.inductionOn j ?_ ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Introduce `j ih`.

Rewrite using `[Fin.partialProd_succ, Fin.partialProd_succ, ih, map_mul]`. Establish `hstab : ∀ (c : Quotient (QuotientGroup.rightRel (Gq ρ q))) (w : Chn (stabR (actQ (Gq ρ q)) (actQ_one _) (actQ_mul _) c) (m + 1)), IsCyc w → ev (stabR (actQ (Gq ρ q)) (actQ_one _) (actQ_mul _) c).subtype (fun y : Fin (m + 2) → G => ((Gq ρ q).index : ℝ)⁻¹ * F (fun j => q * ρ c.out …`. Introduce `c w hw`. Establish `hmem : ∀ h : stabR (actQ (Gq ρ q)) (actQ_one _) (actQ_mul _) c, q * ρ c.out * ρ h * (q * ρ c.out)⁻¹ ∈ ρ.range`. Introduce `h`.

Establish `h1 : actQ (Gq ρ q) c h = c` using `h.2`. Establish `h3 : (Quotient.mk'' (c.out * (h : G)) : Quotient (QuotientGroup.rightRel (Gq ρ q))) = Quotient.mk'' c.out`. Rewrite using `[Quotient.out_eq']`. Conclude with `h1`. Establish `h2 : c.out * (c.out * (h : G))⁻¹ ∈ Gq ρ q` using `QuotientGroup.rightRel_apply.mp (Quotient.exact' h3)`.

Take `⟨γ, hγ⟩` from `mem_Gq.mp h2`. Use `⟨γ⁻¹, ?_⟩` and prove the remaining obligations. Rewrite using `[map_inv]`. Rewrite `hγ` using `[map_mul, map_inv, map_mul]`. Combine the equalities or inequalities in the displayed calculation.

Set `ψ : (stabR (actQ (Gq ρ q)) (actQ_one _) (actQ_mul _) c) →* K` to `(MulAut.conj (q * ρ c.out)).toMonoidHom.comp (ρ.comp (stabR (actQ (Gq ρ q)) (actQ_one _) (actQ_mul _) c).subtype)`. Establish `hψ : ∀ h, ψ h ∈ ρ.range` using `fun h => by`. Use `hmem h using 1` and compare the differences between its conclusion and the goal. Simplify using `only [ψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_subtype]`. Use `done`.

Set `φ` to `(MonoidHom.ofInjective hρ).symm.toMonoidHom.comp (ψ.codRestrict ρ.range hψ)`. Establish `hφ : ∀ h, ρ (φ h) = q * ρ c.out * ρ h * (q * ρ c.out)⁻¹`. Introduce `h`. Rewrite using `[← MonoidHom.ofInjective_apply hρ (x := φ h)]`. Simplify using `[φ, ψ, MulAut.conj_apply]`.

Use `group`. Establish `hz' : IsCyc (cmap φ (m + 1) w)`. Unfold `IsCyc at hw ⊢`. Rewrite using `[bd_cmap, hw, map_zero]`. Establish `hsev` using `(hSEv G K K ρ m F hF hdF).2 (q * ρ c.out) 1 _ hz'`.

Establish `hcalc : ev (stabR (actQ (Gq ρ q)) (actQ_one _) (actQ_mul _) c).subtype (fun y : Fin (m + 2) → G => ((Gq ρ q).index : ℝ)⁻¹ * F (fun j => q * ρ c.out * ρ (y j))) 1 w = ((Gq ρ q).index : ℝ)⁻¹ * ev ρ F (q * ρ c.out) (cmap φ (m + 1) w)`. Unfold `ev cmap`. Rewrite using `[Finsupp.lmapDomain_apply, Finsupp.sum_mapDomain_index (by intro b; simp) (by intro b r1 r2; ring), Finsupp.mul_sum]`. Apply `Finsupp.sum_congr` to reduce the goal to its premises. Introduce `g _`.

Simplify using `only [hpp, hφ, smul_eq_mul, Subgroup.coe_subtype, mul_one, inv_mul_cancel_right]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hcalc, hsev, hcyc _ hz', mul_zero]`. Establish `hfinal` using `hT G (Quotient (QuotientGroup.rightRel (Gq ρ q))) (actQ (Gq ρ q)) (actQ_one _) (actQ_mul _) m (fun c y => ((Gq ρ q).index : ℝ)⁻¹ * F (fun j => q * ρ c.out * ρ (y j))) heq hcoc hstab z hz`. Use `Eq.trans ?_ hfinal` and prove the remaining obligations.

Unfold `ev`. Apply `Finsupp.sum_congr` to reduce the goal to its premises. Introduce `g _`. Use `congr 1`. Simplify using `only [hecke_apply, finsum_eq_sum_of_fintype, Finset.mul_sum, smul_eq_mul, mul_one, MonoidHom.id_apply]`.
-/
theorem pHeckeKer (hT : PTransfer) (hE : PEvDC) : PHeckeKer := by
  intro hSEv G K _ _ ρ hρ q hfin m F hF hdF hcyc z hz
  haveI := Fintype.ofFinite (Quotient (QuotientGroup.rightRel (Gq ρ q)))
  have heq : ∀ (c : Quotient (QuotientGroup.rightRel (Gq ρ q))) (g : G) (y : Fin (m + 2) → G),
      ((Gq ρ q).index : ℝ)⁻¹ * F (fun j => q * ρ (actQ (Gq ρ q) c g).out * ρ (y j)) =
        ((Gq ρ q).index : ℝ)⁻¹ * F (fun j => q * ρ c.out * ρ (g * y j)) := by
    intro c g y
    have e := F_rep ρ q F hF (actQ (Gq ρ q) c g).out (c.out * g) (rel_out_mul _ c g) (fun j => ρ (y j))
    rw [← e]
    congr 1
    congr 1
    funext j
    rw [map_mul, map_mul]
    group
  have hcoc : ∀ c : Quotient (QuotientGroup.rightRel (Gq ρ q)),
      dC (fun y : Fin (m + 2) → G => ((Gq ρ q).index : ℝ)⁻¹ * F (fun j => q * ρ c.out * ρ (y j))) = 0 := by
    intro c
    funext y
    have h := congrFun hdF (fun j => q * ρ c.out * ρ (y j))
    unfold dC at h ⊢
    simp only [Pi.zero_apply] at h ⊢
    rw [← mul_zero (((Gq ρ q).index : ℝ)⁻¹), ← h, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  have hpp : ∀ {S T : Type} [Group S] [Group T] (φ : S →* T) {n : ℕ} (g : Fin n → S) (j : Fin (n + 1)),
      Fin.partialProd (fun i => φ (g i)) j = φ (Fin.partialProd g j) := by
    intro S T _ _ φ n g j
    refine Fin.inductionOn j ?_ ?_
    · simp
    · intro j ih
      rw [Fin.partialProd_succ, Fin.partialProd_succ, ih, map_mul]
  have hstab : ∀ (c : Quotient (QuotientGroup.rightRel (Gq ρ q)))
      (w : Chn (stabR (actQ (Gq ρ q)) (actQ_one _) (actQ_mul _) c) (m + 1)), IsCyc w →
      ev (stabR (actQ (Gq ρ q)) (actQ_one _) (actQ_mul _) c).subtype
        (fun y : Fin (m + 2) → G => ((Gq ρ q).index : ℝ)⁻¹ * F (fun j => q * ρ c.out * ρ (y j))) 1 w = 0 := by
    intro c w hw
    have hmem : ∀ h : stabR (actQ (Gq ρ q)) (actQ_one _) (actQ_mul _) c,
        q * ρ c.out * ρ h * (q * ρ c.out)⁻¹ ∈ ρ.range := by
      intro h
      have h1 : actQ (Gq ρ q) c h = c := h.2
      have h3 : (Quotient.mk'' (c.out * (h : G)) : Quotient (QuotientGroup.rightRel (Gq ρ q))) =
          Quotient.mk'' c.out := by
        rw [Quotient.out_eq']
        exact h1
      have h2 : c.out * (c.out * (h : G))⁻¹ ∈ Gq ρ q := QuotientGroup.rightRel_apply.mp (Quotient.exact' h3)
      obtain ⟨γ, hγ⟩ := mem_Gq.mp h2
      refine ⟨γ⁻¹, ?_⟩
      rw [map_inv]
      rw [map_mul, map_inv, map_mul] at hγ
      calc (ρ γ)⁻¹ = (q * (q⁻¹ * ρ γ * q) * q⁻¹)⁻¹ := by group
        _ = _ := by rw [hγ]; group
    let ψ : (stabR (actQ (Gq ρ q)) (actQ_one _) (actQ_mul _) c) →* K :=
      (MulAut.conj (q * ρ c.out)).toMonoidHom.comp (ρ.comp (stabR (actQ (Gq ρ q)) (actQ_one _) (actQ_mul _) c).subtype)
    have hψ : ∀ h, ψ h ∈ ρ.range := fun h => by
      convert hmem h using 1
      simp only [ψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_subtype]
      done
    let φ := (MonoidHom.ofInjective hρ).symm.toMonoidHom.comp (ψ.codRestrict ρ.range hψ)
    have hφ : ∀ h, ρ (φ h) = q * ρ c.out * ρ h * (q * ρ c.out)⁻¹ := by
      intro h
      rw [← MonoidHom.ofInjective_apply hρ (x := φ h)]
      simp [φ, ψ, MulAut.conj_apply]
      group
    have hz' : IsCyc (cmap φ (m + 1) w) := by
      unfold IsCyc at hw ⊢
      rw [bd_cmap, hw, map_zero]
    have hsev := (hSEv G K K ρ m F hF hdF).2 (q * ρ c.out) 1 _ hz'
    have hcalc : ev (stabR (actQ (Gq ρ q)) (actQ_one _) (actQ_mul _) c).subtype
        (fun y : Fin (m + 2) → G => ((Gq ρ q).index : ℝ)⁻¹ * F (fun j => q * ρ c.out * ρ (y j))) 1 w =
        ((Gq ρ q).index : ℝ)⁻¹ * ev ρ F (q * ρ c.out) (cmap φ (m + 1) w) := by
      unfold ev cmap
      rw [Finsupp.lmapDomain_apply, Finsupp.sum_mapDomain_index (by intro b; simp) (by intro b r1 r2; ring),
        Finsupp.mul_sum]
      apply Finsupp.sum_congr
      intro g _
      simp only [hpp, hφ, smul_eq_mul, Subgroup.coe_subtype, mul_one, inv_mul_cancel_right]
      ring
    rw [hcalc, hsev, hcyc _ hz', mul_zero]
  have hfinal := hT G (Quotient (QuotientGroup.rightRel (Gq ρ q))) (actQ (Gq ρ q)) (actQ_one _) (actQ_mul _) m
    (fun c y => ((Gq ρ q).index : ℝ)⁻¹ * F (fun j => q * ρ c.out * ρ (y j))) heq hcoc hstab z hz
  refine Eq.trans ?_ hfinal
  unfold ev
  apply Finsupp.sum_congr
  intro g _
  congr 1
  simp only [hecke_apply, finsum_eq_sum_of_fintype, Finset.mul_sum, smul_eq_mul, mul_one, MonoidHom.id_apply]

end PositivityTheory.KB.AffineStabilizerVanishing

end
