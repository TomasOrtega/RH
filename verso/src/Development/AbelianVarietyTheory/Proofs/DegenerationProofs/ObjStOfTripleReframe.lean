import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ReframeSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsOfDouble
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLatticeUniformisationOfPrimTheta
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.AppellHumbertDataOfIsoCube

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch
noncomputable section
namespace GlobalTheory.Ex.Arch

/- English proof (translation)
Establish `hd : ∀ k : ℕ, 0 < k → (k : ℤ) ∣ m - n` using `fun k hk => by`. Take `⟨j, hj⟩` from `Complex.exp_eq_exp_iff_exists_int.1 (h k hk)`. Establish `hk' : (k : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 hk.ne'`. Establish `hp : (2 * Real.pi * Complex.I : ℂ) ≠ 0` using `Complex.two_pi_I_ne_zero`. Use `⟨-j, ?_⟩` and prove the remaining obligations.

Establish `: ((m - n : ℤ) : ℂ) = ((k * -j : ℤ) : ℂ)`. Use `push_cast`. Apply `mul_left_cancel₀ hp` to reduce the goal to its premises. Establish `h2` using `congrArg (· * (k : ℂ)) hj`. Simplify using `only [add_mul, div_mul_cancel₀ _ hk'] at h2`.

Take the linear combination `-h2`. Conclude with `this` after adjusting the coercions. Use `sub_eq_zero.1 (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (hd ((m - n).natAbs + 1) (Nat.succ_pos _)) ?_)` and prove the remaining obligations. Rewrite using `[Int.natAbs_natCast]`. Conclude with `Nat.lt_succ_self _`.
-/
theorem int_eq_of_exp_div_eq {m n : ℤ} (h : ∀ k : ℕ, 0 < k →
    Complex.exp (-(2 * Real.pi * Complex.I) * (m : ℂ) / k) = Complex.exp (-(2 * Real.pi * Complex.I) * (n : ℂ) / k)) :
    m = n := by
  have hd : ∀ k : ℕ, 0 < k → (k : ℤ) ∣ m - n := fun k hk => by
    obtain ⟨j, hj⟩ := Complex.exp_eq_exp_iff_exists_int.1 (h k hk)
    have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
    have hp : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
    refine ⟨-j, ?_⟩
    have : ((m - n : ℤ) : ℂ) = ((k * -j : ℤ) : ℂ) := by
      push_cast
      apply mul_left_cancel₀ hp
      have h2 := congrArg (· * (k : ℂ)) hj
      simp only [add_mul, div_mul_cancel₀ _ hk'] at h2
      linear_combination -h2
    exact_mod_cast this
  refine sub_eq_zero.1 (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (hd ((m - n).natAbs + 1) (Nat.succ_pos _)) ?_)
  rw [Int.natAbs_natCast]
  exact Nat.lt_succ_self _

/- English proof (translation)
Introduce `laws hT hR E _ _ _ H D La _ _ EF g ty P Hm₀ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10`. Take `⟨Q, oa, L₀, u₀, hg, hiso, hdet, ht₁, ht₂, hker, hact, hW⟩` from `hT E H D La EF g ty P Hm₀ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10`. Take `⟨u, Hm, χ, Ef, F, hAH, hE, hF⟩` from `hR Q L₀ g u₀ hg ht₁ ht₂`. Establish `hΛ : ∀ a, F (P a) ∈ u.Λ` using `fun a => (u.ker _).1 ((hF _).trans ((hker _).2 ⟨a, rfl⟩))`. Establish `hsur : ∀ z ∈ u.Λ, ∃ a, z = F (P a)` using `fun z hz => by`.

Take `⟨w, rfl⟩` from `F.surjective z`. Take `⟨a, ha⟩` from `(hker w).1 ((hF w).symm.trans ((u.ker _).2 hz))`. Conclude with `⟨a, by rw [ha]⟩`. Establish `hW' : ∀ (k : ℕ) a b (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k) → WeilIs Q.A Q.L k (u.ex ((k : ℂ)⁻¹ • F (P a))) (u.ex ((k : ℂ)⁻¹ • F (P b))) (unitOn c)` using `fun k a b c hk hc => by`. Rewrite using `[← map_smul F, ← map_smul F, hF, hF]`.

Conclude with `hW k a b c hk hc`. Establish `hEf : ∀ a b, Ef ⟨F (P a), hΛ a⟩ ⟨F (P b), hΛ b⟩ = EF a b` using `fun a b => int_eq_of_exp_div_eq fun k hk => by`. Establish `w₁` using `PeriodPoint.weilIs_of_isAH laws Q rfl u hAH Ef hE k ⟨F (P a), hΛ a⟩ ⟨F (P b), hΛ b⟩ (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl`. Establish `w₂` using `hW' k a b (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl`. Conclude with `congrArg Units.val (PrimUnif.unitOn_inj' (CommutatorPairing.weilIs_unique laws.globalFns Q.isAb Q.isLB w₁ w₂))`.

Establish `hact' : ∀ (a : 𝓞 E) z, u.ex (F fun k => ty k (a : E) * z k) = u.ex (F z) ≫ oa.act a` using `fun a z => by`. Rewrite using `[hF, hF, hact]`. Set `d : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)` to `LinearMap.pi fun k => ty k (H.w0 : E) • LinearMap.proj (R := ℂ) (φ := fun _ => ℂ) k`. Set `G : (Fin Q.g → ℂ) →ₗ[ℂ] (Fin Q.g → ℂ)` to `F.toLinearMap ∘ₗ d ∘ₗ F.symm.toLinearMap`. Establish `hG : ∀ z, G (F z) = F fun k => ty k (H.w0 : E) * z k` using `fun z => by`.

Express the relevant statement in the definitionally equal form `F (d (F.symm (F z))) = _`. Rewrite using `[F.symm_apply_apply]`. Both sides reduce to the same expression. Establish `hGP : ∀ a, G (F (P a)) = F (P (H.w0 • a))` using `fun a => by`. Rewrite using `[hG]`.

Use `congr 1`. Use function extensionality and compare the values at `k`. Conclude with `(h4 _ _ _).symm`. Establish `hGΛ : ∀ l ∈ u.Λ, G l ∈ u.Λ` using `fun l hl => by`. Take `⟨a, rfl⟩` from `hsur l hl`.

Rewrite using `[hGP]`. Conclude with `hΛ _`. Establish `hGex : ∀ z, u.ex (G z) = u.ex z ≫ oa.act H.w0` using `fun z => by`. Take `⟨w, rfl⟩` from `F.surjective z`. Rewrite using `[hG, hact']`.

Establish `hχ` using `(@GlobalTheory.SelfCube.appellHumbert_data_of_iso_cube GlobalTheory.valAt'_rules (GlobalTheory.holFamily_lift GlobalTheory.valAt'_rules) Q Q.isAb.comm u Hm χ Ef ⟨hAH.1, hAH.2.2.1, hE, hAH.2.2.2⟩ (oa.act H.w0) G hGΛ hGex hiso).2`. Use `⟨Q, oa, u, Hm, χ, F, hΛ, hiso, hdet, hAH, hsur, fun a b => ?_, fun a => ?_, hact', hW'⟩` and prove the remaining obligations. Rewrite using `[← hEf]`. Conclude with `(hE ⟨F (P a), hΛ a⟩ ⟨F (P b), hΛ b⟩).symm`. Rewrite using `[hχ, ← hEf]`.

Use `congr 2`. Conclude with `Subtype.ext (hGP a)`.
-/
theorem objSt_of_triple_reframe : Laws → TripleSt → ReframeSt → ObjSt := by
  intro laws hT hR E _ _ _ H D La _ _ EF g ty P Hm₀ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  obtain ⟨Q, oa, L₀, u₀, hg, hiso, hdet, ht₁, ht₂, hker, hact, hW⟩ :=
    hT E H D La EF g ty P Hm₀ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  obtain ⟨u, Hm, χ, Ef, F, hAH, hE, hF⟩ := hR Q L₀ g u₀ hg ht₁ ht₂
  have hΛ : ∀ a, F (P a) ∈ u.Λ := fun a => (u.ker _).1 ((hF _).trans ((hker _).2 ⟨a, rfl⟩))
  have hsur : ∀ z ∈ u.Λ, ∃ a, z = F (P a) := fun z hz => by
    obtain ⟨w, rfl⟩ := F.surjective z
    obtain ⟨a, ha⟩ := (hker w).1 ((hF w).symm.trans ((u.ker _).2 hz))
    exact ⟨a, by rw [ha]⟩
  have hW' : ∀ (k : ℕ) a b (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k) →
      WeilIs Q.A Q.L k (u.ex ((k : ℂ)⁻¹ • F (P a))) (u.ex ((k : ℂ)⁻¹ • F (P b))) (unitOn c) := fun k a b c hk hc => by
    rw [← map_smul F, ← map_smul F, hF, hF]
    exact hW k a b c hk hc
  have hEf : ∀ a b, Ef ⟨F (P a), hΛ a⟩ ⟨F (P b), hΛ b⟩ = EF a b := fun a b => int_eq_of_exp_div_eq fun k hk => by
    have w₁ := PeriodPoint.weilIs_of_isAH laws Q rfl u hAH Ef hE k ⟨F (P a), hΛ a⟩ ⟨F (P b), hΛ b⟩
      (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
    have w₂ := hW' k a b (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
    exact congrArg Units.val
      (PrimUnif.unitOn_inj' (CommutatorPairing.weilIs_unique laws.globalFns Q.isAb Q.isLB w₁ w₂))
  have hact' : ∀ (a : 𝓞 E) z, u.ex (F fun k => ty k (a : E) * z k) = u.ex (F z) ≫ oa.act a := fun a z => by
    rw [hF, hF, hact]
  let d : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) :=
    LinearMap.pi fun k => ty k (H.w0 : E) • LinearMap.proj (R := ℂ) (φ := fun _ => ℂ) k
  let G : (Fin Q.g → ℂ) →ₗ[ℂ] (Fin Q.g → ℂ) := F.toLinearMap ∘ₗ d ∘ₗ F.symm.toLinearMap
  have hG : ∀ z, G (F z) = F fun k => ty k (H.w0 : E) * z k := fun z => by
    change F (d (F.symm (F z))) = _
    rw [F.symm_apply_apply]
    rfl
  have hGP : ∀ a, G (F (P a)) = F (P (H.w0 • a)) := fun a => by
    rw [hG]
    congr 1
    funext k
    exact (h4 _ _ _).symm
  have hGΛ : ∀ l ∈ u.Λ, G l ∈ u.Λ := fun l hl => by
    obtain ⟨a, rfl⟩ := hsur l hl
    rw [hGP]
    exact hΛ _
  have hGex : ∀ z, u.ex (G z) = u.ex z ≫ oa.act H.w0 := fun z => by
    obtain ⟨w, rfl⟩ := F.surjective z
    rw [hG, hact']
  have hχ := (@GlobalTheory.SelfCube.appellHumbert_data_of_iso_cube GlobalTheory.valAt'_rules
    (GlobalTheory.holFamily_lift GlobalTheory.valAt'_rules) Q Q.isAb.comm u Hm χ Ef
    ⟨hAH.1, hAH.2.2.1, hE, hAH.2.2.2⟩ (oa.act H.w0) G hGΛ hGex hiso).2
  refine ⟨Q, oa, u, Hm, χ, F, hΛ, hiso, hdet, hAH, hsur, fun a b => ?_, fun a => ?_, hact', hW'⟩
  · rw [← hEf]
    exact (hE ⟨F (P a), hΛ a⟩ ⟨F (P b), hΛ b⟩).symm
  · rw [hχ, ← hEf]
    congr 2
    exact Subtype.ext (hGP a)

end GlobalTheory.Ex.Arch
end
