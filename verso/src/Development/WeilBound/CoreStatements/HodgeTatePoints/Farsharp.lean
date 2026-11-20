import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeTateCokerSharp
import Development.WeilBound.CoreStatements.HodgeTatePoints.FarsharpA
import Development.WeilBound.CoreStatements.HodgeTatePoints.FarsharpB

noncomputable section

open TensorProduct Coalgebra Bialgebra WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace PositivityTheory.HtPt.Farsharp

variable (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
  (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O)
  (hp : v (p : C) < 1)

include hv hp in

/- English proof (translation)
Establish `: IsDomain O` using `hv.hom_inj.isDomain (algebraMap O C)`. Establish `: ValuationRing O`. Use `@ValuationRing.mk O _ _ ⟨fun a b => ?_⟩` and prove the remaining obligations. Break down `le_total (v (algebraMap O C a)) (v (algebraMap O C b)) with h | h` into its components or cases. Take `⟨c, hc⟩` from `hv.dvd_iff_le.2 h`.

Conclude with `⟨c, Or.inr hc.symm⟩`. Take `⟨c, hc⟩` from `hv.dvd_iff_le.2 h`. Conclude with `⟨c, Or.inl hc.symm⟩`. Set `ε` to `counitAlgHom O A`. Set `π : A →ₗ[O] A` to `LinearMap.id - Algebra.linearMap O A ∘ₗ ε.toLinearMap`.

Establish `hπ : ∀ a, π a = a - algebraMap O A (ε a)` using `fun _ => rfl`. Set `μ : A ⊗[O] A →ₗ[O] A` to `LinearMap.mul' O A ∘ₗ TensorProduct.map π π`. Establish `hμ : ∀ a b, μ (a ⊗ₜ b) = π a * π b` using `fun a b => by simp [μ]`. Set `N : Submodule O A` to `Submodule.span O {u : A | IsGroupLikeElem O u} ⊔ (LinearMap.range μ ⊔ LinearMap.range (q • (LinearMap.id : A →ₗ[O] A)))`. Establish `hN : N.FG` using `(Submodule.fg_span hfin).sup ((Submodule.fg_range _).sup (Submodule.fg_range _))`.

Establish `hNM : N ≤ M.comap (AugCot.d ε)`. Use `sup_le (Submodule.span_le.2 hM) (sup_le ?_ ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨t, rfl⟩`. Proceed by induction on `t with`. Consider the case `zero => simp`.

Consider the case `tmul a b`. Establish `h0 : ∀ a, ε (π a) = 0` using `fun a => by rw [hπ]; simp`. Rewrite using `[Submodule.mem_comap, hμ, AugCot.d_mul, h0, h0, zero_smul, zero_smul, add_zero]`. Conclude with `zero_mem _`. Consider the case `add x y hx hy => rw [map_add]`.

Conclude with `add_mem hx hy`. Introduce and unpack `_ ⟨a, rfl⟩`. Rewrite using `[Submodule.mem_comap, LinearMap.smul_apply, map_smul]`. Conclude with `hqM _`. Take `⟨a, rfl⟩` from `AugCot.d_surjective _ y`.

Rewrite using `[← map_smul]`. Use `hNM (mem_of_forall_dvd N hN hq (fun a => Submodule.mem_sup_right (Submodule.mem_sup_right ⟨a, rfl⟩)) _ fun φ hφ => ?_)` and prove the remaining obligations. Establish `hu : ∀ u : A, IsGroupLikeElem O u → q ∣ φ u` using `fun u hu => hφ u (Submodule.mem_sup_left (Submodule.subset_span hu))`. Rewrite using `[map_smul]`. Use `dvd_mul_of_val p C v O hv hp A q hq φ (fun a b => ?_) hu κ hκ a` and prove the remaining obligations.

Establish `h1` using `hφ _ (Submodule.mem_sup_right (Submodule.mem_sup_left ⟨a ⊗ₜ b, rfl⟩))`. Establish `h2` using `(hu 1 IsGroupLikeElem.one).mul_left (ε a * ε b)`. Establish `h3 : μ (a ⊗ₜ b) = a * b - ε a • b - ε b • a + (ε a * ε b) • (1 : A)`. Rewrite using `[hμ, hπ, hπ]`. Simplify using `only [Algebra.smul_def, map_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite `h1` using `[h3, map_add, map_sub, map_sub, map_smul, map_smul, map_smul]`. Conclude with `(dvd_add_left h2).1 h1`.
-/
theorem smul_dUnit_mem (A : Type) [CommRing A] [Bialgebra O A] [IsCocomm O A] [Module.Finite O A]
    [Module.Projective O A] (hfin : {u : A | IsGroupLikeElem O u}.Finite) (q : O) (hq : q ≠ 0)
    (M : Submodule O (Cot O A)) (hM : ∀ u, IsGroupLikeElem O u → dUnit O u ∈ M)
    (hqM : ∀ y, q • y ∈ M) (κ : O) (hκ : v (algebraMap O C κ) ^ (p - 1) ≤ v (p : C))
    (y : Cot O A) : κ • y ∈ M := by
  have : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  have : ValuationRing O := by
    refine @ValuationRing.mk O _ _ ⟨fun a b => ?_⟩
    rcases le_total (v (algebraMap O C a)) (v (algebraMap O C b)) with h | h
    · obtain ⟨c, hc⟩ := hv.dvd_iff_le.2 h
      exact ⟨c, Or.inr hc.symm⟩
    · obtain ⟨c, hc⟩ := hv.dvd_iff_le.2 h
      exact ⟨c, Or.inl hc.symm⟩
  let ε := counitAlgHom O A
  let π : A →ₗ[O] A := LinearMap.id - Algebra.linearMap O A ∘ₗ ε.toLinearMap
  have hπ : ∀ a, π a = a - algebraMap O A (ε a) := fun _ => rfl
  let μ : A ⊗[O] A →ₗ[O] A := LinearMap.mul' O A ∘ₗ TensorProduct.map π π
  have hμ : ∀ a b, μ (a ⊗ₜ b) = π a * π b := fun a b => by simp [μ]
  let N : Submodule O A := Submodule.span O {u : A | IsGroupLikeElem O u} ⊔
    (LinearMap.range μ ⊔ LinearMap.range (q • (LinearMap.id : A →ₗ[O] A)))
  have hN : N.FG := (Submodule.fg_span hfin).sup ((Submodule.fg_range _).sup (Submodule.fg_range _))
  have hNM : N ≤ M.comap (AugCot.d ε) := by
    refine sup_le (Submodule.span_le.2 hM) (sup_le ?_ ?_)
    · rintro _ ⟨t, rfl⟩
      induction t with
      | zero => simp
      | tmul a b =>
        have h0 : ∀ a, ε (π a) = 0 := fun a => by rw [hπ]; simp
        rw [Submodule.mem_comap, hμ, AugCot.d_mul, h0, h0, zero_smul, zero_smul, add_zero]
        exact zero_mem _
      | add x y hx hy => rw [map_add]; exact add_mem hx hy
    · rintro _ ⟨a, rfl⟩
      rw [Submodule.mem_comap, LinearMap.smul_apply, map_smul]
      exact hqM _
  obtain ⟨a, rfl⟩ := AugCot.d_surjective _ y
  rw [← map_smul]
  refine hNM (mem_of_forall_dvd N hN hq
    (fun a => Submodule.mem_sup_right (Submodule.mem_sup_right ⟨a, rfl⟩)) _ fun φ hφ => ?_)
  have hu : ∀ u : A, IsGroupLikeElem O u → q ∣ φ u := fun u hu =>
    hφ u (Submodule.mem_sup_left (Submodule.subset_span hu))
  rw [map_smul]
  refine dvd_mul_of_val p C v O hv hp A q hq φ (fun a b => ?_) hu κ hκ a
  have h1 := hφ _ (Submodule.mem_sup_right (Submodule.mem_sup_left ⟨a ⊗ₜ b, rfl⟩))
  have h2 := (hu 1 IsGroupLikeElem.one).mul_left (ε a * ε b)
  have h3 : μ (a ⊗ₜ b) = a * b - ε a • b - ε b • a + (ε a * ε b) • (1 : A) := by
    rw [hμ, hπ, hπ]
    simp only [Algebra.smul_def, map_mul]
    ring
  rw [h3, map_add, map_sub, map_sub, map_smul, map_smul, map_smul] at h1
  exact (dvd_add_left h2).1 h1

include hv hp in

/- English proof (translation)
Establish `hpp : p.Prime` using `Fact.out`. Establish `: IsIntegrallyClosedIn O C` using `isIntegrallyClosedIn_iff.2 ⟨hv.hom_inj, fun hx => hv.exists_of_le_one (hv.mem_of_integral hx)⟩`. Use `G.dual.finite_tate C` as an intermediate fact. Establish `hp0 : (p : O) ≠ 0` using `fun h => by`. Establish `h1` using `congrArg (algebraMap O C) h`.

Rewrite `h1` using `[map_natCast, map_zero]`. Conclude with `Nat.cast_ne_zero.2 hpp.ne_zero h1`. Establish `: IsDomain O` using `hv.hom_inj.isDomain (algebraMap O C)`. Establish `key : ∀ κ : O, v (algebraMap O C κ) ^ (p - 1) ≤ v (p : C) → ∀ n (y : Cot O (G.A n)), κ • y ∈ (LinearMap.range (dlogLinear G)).map (lev G n)` using `fun κ hκ n y => by`. Establish `hch : ∀ u (hu : IsGroupLikeElem O u), charFun O (G.A n) (toConv (evalPoint u hu)) = u` using `fun u hu => CartierDual.eq_of_forall_apply (R := O) fun φ => apply_charFun _ φ`.

Establish `: Finite (CartierDual O (G.A n) →ₐ[O] O)` using `Nat.finite_of_card_ne_zero ((G.dual.natCard_pts_eq C n).trans_ne (pow_ne_zero _ hpp.ne_zero))`. Use `smul_dUnit_mem p C v O hv hp (G.A n) ((Set.finite_range fun χ : CartierDual O (G.A n) →ₐ[O] O => charFun O (G.A n) (toConv χ)).subset fun u hu => ⟨_, hch u hu⟩) ((p : O) ^ n) (pow_ne_zero _ hp0) _ (fun u hu => ?_) (fun y => by rw [pow_smul_cot]; exact zero_mem _) κ hκ y` and prove the remaining obligations. Take `⟨χ, hχ⟩` from `G.dual.pt_surjective C n (evalPoint u hu)`. Use `⟨dlog G χ, ⟨1 ⊗ₜ χ, by rw [dlogLinear_tmul, one_smul]⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[lev_apply, dlog_val, ← hch u hu, ← hχ]`.

Both sides reduce to the same expression. Use `smul_mem_of_levels G _ (Submodule.fg_range _) κ (key κ hκ) (key p ?_) w` and prove the remaining obligations. Rewrite using `[map_natCast]`. Conclude with `pow_le_of_le_one zero_le hp.le (Nat.sub_pos_of_lt hpp.one_lt).ne'`.
-/
theorem smul_mem_range_dlogLinear [Algebra ℤ_[p] O] [IsAdicComplete (Ideal.span {(p : O)}) O]
    (G : PDivGroup p O) (κ : O) (hκ : v (algebraMap O C κ) ^ (p - 1) ≤ v (p : C)) (w : G.omega) :
    κ • w ∈ LinearMap.range (dlogLinear G) := by
  have hpp : p.Prime := Fact.out
  have : IsIntegrallyClosedIn O C := isIntegrallyClosedIn_iff.2
    ⟨hv.hom_inj, fun hx => hv.exists_of_le_one (hv.mem_of_integral hx)⟩
  have := G.dual.finite_tate C
  have hp0 : (p : O) ≠ 0 := fun h => by
    have h1 := congrArg (algebraMap O C) h
    rw [map_natCast, map_zero] at h1
    exact Nat.cast_ne_zero.2 hpp.ne_zero h1
  have : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  have key : ∀ κ : O, v (algebraMap O C κ) ^ (p - 1) ≤ v (p : C) → ∀ n (y : Cot O (G.A n)),
      κ • y ∈ (LinearMap.range (dlogLinear G)).map (lev G n) := fun κ hκ n y => by
    have hch : ∀ u (hu : IsGroupLikeElem O u),
        charFun O (G.A n) (toConv (evalPoint u hu)) = u := fun u hu =>
      CartierDual.eq_of_forall_apply (R := O) fun φ => apply_charFun _ φ
    have : Finite (CartierDual O (G.A n) →ₐ[O] O) :=
      Nat.finite_of_card_ne_zero ((G.dual.natCard_pts_eq C n).trans_ne (pow_ne_zero _ hpp.ne_zero))
    refine smul_dUnit_mem p C v O hv hp (G.A n)
      ((Set.finite_range fun χ : CartierDual O (G.A n) →ₐ[O] O =>
        charFun O (G.A n) (toConv χ)).subset fun u hu => ⟨_, hch u hu⟩)
      ((p : O) ^ n) (pow_ne_zero _ hp0) _ (fun u hu => ?_)
      (fun y => by rw [pow_smul_cot]; exact zero_mem _) κ hκ y
    obtain ⟨χ, hχ⟩ := G.dual.pt_surjective C n (evalPoint u hu)
    refine ⟨dlog G χ, ⟨1 ⊗ₜ χ, by rw [dlogLinear_tmul, one_smul]⟩, ?_⟩
    rw [lev_apply, dlog_val, ← hch u hu, ← hχ]
    rfl
  refine smul_mem_of_levels G _ (Submodule.fg_range _) κ (key κ hκ) (key p ?_) w
  rw [map_natCast]
  exact pow_le_of_le_one zero_le hp.le (Nat.sub_pos_of_lt hpp.one_lt).ne'

/- English proof (translation)
Introduce `p _ C _ _ _ v O _ _ _ hv hp hO G κ hκ w`. Take `⟨z, hz⟩` from `smul_mem_range_dlogLinear p C v O hv hp G.dual κ hκ w`. Rewrite using `[← hz]`. Use `clear hz`. Proceed by induction on `z with`.

Consider the case `zero => simp`. Consider the case `tmul c χ`. Take `⟨t, rfl⟩` from `(tateCongr O G.bidual).surjective χ`. Conclude with `⟨c ⊗ₜ t, rfl⟩`. Consider the case `add x y hx hy => rw [map_add]`.

Conclude with `add_mem hx hy`.
-/
theorem hodgeTateCokerSharp : GlobalTheory.CompanionTheory.Ar.HT.HodgeTateCokerSharp := by
  intro p _ C _ _ _ v O _ _ _ hv hp hO G κ hκ w
  obtain ⟨z, hz⟩ := smul_mem_range_dlogLinear p C v O hv hp G.dual κ hκ w
  rw [← hz]
  clear hz
  induction z with
  | zero => simp
  | tmul c χ =>
    obtain ⟨t, rfl⟩ := (tateCongr O G.bidual).surjective χ
    exact ⟨c ⊗ₜ t, rfl⟩
  | add x y hx hy => rw [map_add]; exact add_mem hx hy

end PositivityTheory.HtPt.Farsharp
