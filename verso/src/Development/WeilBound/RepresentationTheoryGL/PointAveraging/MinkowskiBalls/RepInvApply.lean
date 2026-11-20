import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GermIntegrals.StepSt

open MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL ValuativeRel PositivityTheory.Tls2.Ming3

namespace PositivityTheory.Rg.Ming

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/- English proof (translation)
Use extensionality with `i l`. Simplify using `[idem, GlobalTheory.GodementJacquet.eMat]`.
-/
theorem idem_eq_eMat (r t : ℕ) : idem k r (r + t) r = GlobalTheory.GodementJacquet.eMat k r t := by
  ext i l
  simp [idem, GlobalTheory.GodementJacquet.eMat]

/- English proof (translation)
Establish `h1 : x.rank ≤ r`. Simplify using `using Matrix.rank_le_width x`. Establish `h2 : ¬ x.rank < r` using `fun h => hx (hΦ x h)`. Use linear arithmetic over natural numbers and integers.
-/
theorem rank_eq_of_ne {r t : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (Φ : SB (Matrix (Fin (r + t)) (Fin r) k))
    (hΦ : ∀ x : Matrix (Fin (r + t)) (Fin r) k, x.rank < r → Φ.1 x = 0)
    (x : Matrix (Fin (r + t)) (Fin r) k) (hx : Φ.1 x ≠ 0) : x.rank = r := by
  have h1 : x.rank ≤ r := by
    simpa using Matrix.rank_le_width x
  have h2 : ¬ x.rank < r := fun h => hx (hΦ x h)
  omega

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/- English proof (translation)
Rewrite using `[← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]`. Both sides reduce to the same expression.
-/
theorem rep_inv_apply {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (GL (Fin n) k) W) (h : GL (Fin n) k) (w : W) : π h (π h⁻¹ w) = w := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
  rfl

end PositivityTheory.Rg.Ming

namespace PositivityTheory.Rg.Ming

/- English proof (translation)
Introduce `hball hloc hnf k _ _ _ _ _ _ ν hν r t μ V _ _ W _ _ σ π B hEq hG Φ hΦ`. Use extensionality with `w`. Use `show B Φ w = 0`. Use `set e := GlobalTheory.GodementJacquet.eMat k r t with he`. Establish `key` using `hloc k (r + t) r (LinearMap.ker (B.flip w)) Φ`.

Establish `hmem` using `key ?_`. Simplify using `using hmem`. Introduce `x hx`. Establish `hrk` using `rank_eq_of_ne (V := V) (W := W) Φ hΦ x hx`. Take `⟨⟨H, G, hxHG⟩, -⟩` from `hnf k (r + t) r r x hrk`.

Rewrite `hxHG` using `[idem_eq_eMat]`. Take `⟨c, hc⟩` from `hG (π H⁻¹ w)`. Set `f : Matrix (Fin (r + t)) (Fin r) k → Matrix (Fin (r + t)) (Fin r) k` to `fun z => (H⁻¹ : GL (Fin (r + t)) k).val * z * (G⁻¹ : GL (Fin r) k).val`. Establish `hf : Continuous f` using `(continuous_const.matrix_mul continuous_id).matrix_mul continuous_const`. Use `⟨f ⁻¹' ballM c e, ((hball k (r + t) r).1 c e).1.preimage hf, ?_, ?_⟩` and prove the remaining obligations.

Use `show f x ∈ ballM c e`. Establish `: f x = e`. Simplify using `only [f, hxHG, ← Matrix.mul_assoc]`. Rewrite using `[Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]`. Rewrite using `[this]`.

Conclude with `fun i l => by simp`. Introduce `Ψ hΨ`. Take `⟨Ψ', hΨ'def⟩ : ∃ Ψ' : SB (Matrix (Fin (r + t)) (Fin r) k), Ψ'.1 = om μ G H⁻¹ Ψ.1` from `⟨⟨_, om_mem_SB μ _ _ Ψ.2⟩, rfl⟩`. Establish `hΨΨ' : (Ψ : Matrix (Fin (r + t)) (Fin r) k → ℂ) = om μ G⁻¹ H Ψ'.1` using `by show Ψ.1 = _`. Rewrite using `[hΨ'def, ← om_mul, inv_mul_cancel, mul_inv_cancel, om_one]`.

Establish `hsupp : ∀ y, Ψ'.1 y ≠ 0 → y ∈ ballM c e`. Introduce `y hy`. Rewrite `hy` using `[hΨ'def]`. Simplify using `only [om, inv_inv] at hy`. Establish `h2` using `(hΨ _ (right_ne_zero_of_mul hy)).1`.

Establish `h3 : f (H.val * y * G.val) = y`. Simplify using `only [f, ← Matrix.mul_assoc]`. Rewrite using `[Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]`. Simplify `h2` using `[Set.mem_preimage, h3]`. Establish `h1` using `hEq G⁻¹ H Ψ' Ψ hΨΨ' (π H⁻¹ w)`.

Rewrite `h1` using `[rep_inv_apply]`. Use `show B Ψ w = 0`. Rewrite using `[h1, hc Ψ' hsupp, smul_zero, map_zero]`.
-/
theorem nz : BallSt → LocSt → NfSt → NzSt := by
  intro hball hloc hnf k _ _ _ _ _ _ ν hν r t μ V _ _ W _ _ σ π B hEq hG Φ hΦ
  ext w
  show B Φ w = 0
  set e := GlobalTheory.GodementJacquet.eMat k r t with he
  have key := hloc k (r + t) r (LinearMap.ker (B.flip w)) Φ
  have hmem := key ?_
  · simpa using hmem
  intro x hx
  have hrk := rank_eq_of_ne (V := V) (W := W) Φ hΦ x hx
  obtain ⟨⟨H, G, hxHG⟩, -⟩ := hnf k (r + t) r r x hrk
  rw [idem_eq_eMat] at hxHG
  obtain ⟨c, hc⟩ := hG (π H⁻¹ w)
  let f : Matrix (Fin (r + t)) (Fin r) k → Matrix (Fin (r + t)) (Fin r) k :=
    fun z => (H⁻¹ : GL (Fin (r + t)) k).val * z * (G⁻¹ : GL (Fin r) k).val
  have hf : Continuous f := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  refine ⟨f ⁻¹' ballM c e, ((hball k (r + t) r).1 c e).1.preimage hf, ?_, ?_⟩
  · show f x ∈ ballM c e
    have : f x = e := by
      simp only [f, hxHG, ← Matrix.mul_assoc]
      rw [Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    rw [this]
    exact fun i l => by simp
  · intro Ψ hΨ
    obtain ⟨Ψ', hΨ'def⟩ : ∃ Ψ' : SB (Matrix (Fin (r + t)) (Fin r) k),
        Ψ'.1 = om μ G H⁻¹ Ψ.1 :=
      ⟨⟨_, om_mem_SB μ _ _ Ψ.2⟩, rfl⟩
    have hΨΨ' : (Ψ : Matrix (Fin (r + t)) (Fin r) k → ℂ) = om μ G⁻¹ H Ψ'.1 := by
      show Ψ.1 = _
      rw [hΨ'def, ← om_mul, inv_mul_cancel, mul_inv_cancel, om_one]
    have hsupp : ∀ y, Ψ'.1 y ≠ 0 → y ∈ ballM c e := by
      intro y hy
      rw [hΨ'def] at hy
      simp only [om, inv_inv] at hy
      have h2 := (hΨ _ (right_ne_zero_of_mul hy)).1
      have h3 : f (H.val * y * G.val) = y := by
        simp only [f, ← Matrix.mul_assoc]
        rw [Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
      simpa [Set.mem_preimage, h3] using h2
    have h1 := hEq G⁻¹ H Ψ' Ψ hΨΨ' (π H⁻¹ w)
    rw [rep_inv_apply] at h1
    show B Ψ w = 0
    rw [h1, hc Ψ' hsupp, smul_zero, map_zero]

end PositivityTheory.Rg.Ming
