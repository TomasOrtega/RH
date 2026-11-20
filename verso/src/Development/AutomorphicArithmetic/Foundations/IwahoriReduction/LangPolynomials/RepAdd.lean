import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.FixedIntegersIsUnitOfNotMemPrimeSpan
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.KumAlg
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.PresMono
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.WdVal
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.DvdOfNormLe

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

/- English proof (translation)
The claim follows from `IsUltrametricDist.norm_natCast_le_one (PadicAlgCl l) a`.
-/
private theorem nat_le_one' {l : ℕ} [Fact l.Prime] (a : ℕ) : ‖(a : Qbar l)‖ ≤ 1 :=
  IsUltrametricDist.norm_natCast_le_one (PadicAlgCl l) a

/- English proof (translation)
Simplify using `[dd]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem dd_mul_eq_dd_mul_add_mul_dd {R : Type} [CommRing R] (f g : PowerSeries R) :
    dd (f * g) = dd f * g + f * dd g := by
  simp [dd]; ring

/- English proof (translation)
Take `⟨u, rfl⟩` from `hf`. Take `⟨v, rfl⟩` from `hg`. Simplify using `only [dl, ← Units.val_mul, Ring.inverse_unit]`. Simplify using `only [Units.val_mul, mul_inv_rev, dd_mul_eq_dd_mul_add_mul_dd]`. Establish `h1 : (u : PowerSeries R) * ↑u⁻¹ = 1` using `u.mul_inv`.

Establish `h2 : (v : PowerSeries R) * ↑v⁻¹ = 1` using `v.mul_inv`. Take the linear combination `(dd (u : PowerSeries R) * ↑u⁻¹) * h2 + (dd (v : PowerSeries R) * ↑v⁻¹) * h1`.
-/
private theorem dl_mul_eq_add_of_isUnit {R : Type} [CommRing R] {f g : PowerSeries R}
    (hf : IsUnit f) (hg : IsUnit g) : dl (f * g) = dl f + dl g := by
  obtain ⟨u, rfl⟩ := hf
  obtain ⟨v, rfl⟩ := hg
  simp only [dl, ← Units.val_mul, Ring.inverse_unit]
  simp only [Units.val_mul, mul_inv_rev, dd_mul_eq_dd_mul_add_mul_dd]
  have h1 : (u : PowerSeries R) * ↑u⁻¹ = 1 := u.mul_inv
  have h2 : (v : PowerSeries R) * ↑v⁻¹ = 1 := v.mul_inv
  linear_combination (dd (u : PowerSeries R) * ↑u⁻¹) * h2 + (dd (v : PowerSeries R) * ↑v⁻¹) * h1

/- English proof (translation)
Introduce `l _ hl Ω _ _ _ A hA j Φ c β ζ hζ`. Establish `hB` using `(pBasEx l c).2 β`. Establish `hpv : ∀ (P Q : Polynomial (R0 A)) (z : Ω), pv (P * Q) z = pv P z * pv Q z`. Introduce `P Q z`. Simplify using `[pv, Polynomial.eval₂_mul]`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `Z Z' D D' ⟨c₁, m₁, h₁⟩ ⟨c₂, m₂, h₂⟩`. Use `⟨max c₁ c₂, max (max m₁ m₂) 1, fun m hm => ?_⟩` and prove the remaining obligations. Establish `hm₁ : m₁ ≤ m` using `le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hm`. Establish `hm₂ : m₂ ≤ m` using `le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hm`.

Establish `hm0 : 1 ≤ m` using `le_trans (le_max_right _ _) hm`. Establish `hc₁ : m - max c₁ c₂ ≤ m - c₁` using `Nat.sub_le_sub_left (le_max_left _ _) m`. Establish `hc₂ : m - max c₁ c₂ ≤ m - c₂` using `Nat.sub_le_sub_left (le_max_right _ _) m`. Take `⟨P, hP, hPL⟩` from `h₁ m hm₁`. Take `⟨P', hP', hPL'⟩` from `h₂ m hm₂`.

Establish `hQ` using `pPresMono l hl Ω A hA c β ζ hζ Z Z m (m - c₁) (m - max c₁ c₂) P hc₁ (fun s _ => by simp [Cg]) hP`. Establish `hQ'` using `pPresMono l hl Ω A hA c β ζ hζ Z' Z' m (m - c₂) (m - max c₁ c₂) P' hc₂ (fun s _ => by simp [Cg]) hP'`. Unfold `UpperTheory.Kd.C7.BPres GlobalTheory.Col.KumPres at hQ hQ'`. Take `⟨hprim, hnr, hu, ho, hk⟩` from `hQ`. Take `⟨-, -, hu', -, hk'⟩` from `hQ'`.

Use `⟨fun i => P i * P' i, ?_, fun i => ?_⟩` and prove the remaining obligations. Unfold `UpperTheory.Kd.C7.BPres GlobalTheory.Col.KumPres`. Use `⟨hprim, hnr, fun i => ?_, ho, fun s hs hcyc hsζ => ?_⟩` and prove the remaining obligations. Simplify using `only`. Rewrite using `[hpv]`.

Take `⟨a₁, a₂, a₃⟩` from `hu i`. Take `⟨b₁, b₂, b₃⟩` from `hu' i`. Simplify using `only at a₁ a₂ a₃ b₁ b₂ b₃`. Conclude with `⟨mul_mem a₁ b₁, mul_ne_zero a₂ b₂, by rw [mul_inv]; exact mul_mem a₃ b₃⟩`. Take `⟨k, hkv, hkc⟩` from `hk s hs hcyc hsζ`.

Take `⟨k', hkv', hkc'⟩` from `hk' s hs hcyc hsζ`. Establish `hsH : s ∈ Hm l A m` using `Subgroup.mem_inf.mpr ⟨hs, MonoidHom.mem_ker.mpr hcyc⟩`. Establish `halg` using `(pKumAlg l hl Ω A hA ζ hζ m (m - max c₁ c₂) (Nat.sub_le _ _) s hsH).1`. Use `⟨k + k', fun i => ?_, ?_⟩` and prove the remaining obligations. Simplify using `only`.

Rewrite using `[hpv]`. Conclude with `(halg _ _ _ _ (hkv i) (hkv' i)).1`. Establish `hNz : NeZero (l ^ (m - max c₁ c₂))` using `⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩`. Establish `key : ∀ i, (((k + k') i).val : Qbar l) = (k i).val + (k' i).val - (l : Qbar l) ^ (m - max c₁ c₂) * ((((k i).val + (k' i).val) / l ^ (m - max c₁ c₂) : ℕ) : Qbar l)`. Introduce `i`.

Rewrite using `[Pi.add_apply, ZMod.val_add, eq_sub_iff_add_eq]`. Conclude with `Nat.mod_add_div ((k i).val + (k' i).val) (l ^ (m - max c₁ c₂))` after adjusting the coercions. Unfold `Cg at hkc hkc' ⊢`. Simplify using `only`. Establish `hsplit : Z m s 1 + Z' m s 1 - ∑ i, β.val i * (((k + k') i).val : Qbar l) = (Z m s 1 - ∑ i, β.val i * ((k i).val : Qbar l)) + (Z' m s 1 - ∑ i, β.val i * ((k' i).val : Qbar l)) + ∑ i, β.val i * ((l : Qbar l) ^ (m - max c₁ c₂) * ((((k i).val + (k' i).val) / l ^ (m - max c₁ c₂) : ℕ) …`.

Simplify using `only [key, mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hsplit]`. Establish `hN : 0 ≤ ‖(l : Qbar l) ^ (m - max c₁ c₂)‖` using `norm_nonneg _`. Use `le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le (le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le hkc hkc')) ?_)` and prove the remaining obligations.

Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hN (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[norm_mul, norm_mul]`. Establish `h1` using `ho i`. Establish `h2` using `nat_le_one' (l := l) (((k i).val + (k' i).val) / l ^ (m - max c₁ c₂))`. Combine the equalities or inequalities in the displayed calculation.

Establish `hU : IsUnit (Φ.ser (P i))` using `(pWD l hl Ω A hA j Φ ζ hζ m hm0 (P i)).2 (hu i)`. Establish `hU' : IsUnit (Φ.ser (P' i))` using `(pWD l hl Ω A hA j Φ ζ hζ m hm0 (P' i)).2 (hu' i)`. Establish `hs : Φ.ser (P i * P' i) = Φ.ser (P i) * Φ.ser (P' i)`. Simplify using `[Fr.ser, Polynomial.map_mul, Polynomial.eval₂_mul]`. Establish `ht : Φ.tw m ((D + D') i) = Φ.tw m (D i) + Φ.tw m (D' i)`.

Simplify using `[Fr.tw, map_add]`. Establish `e₁` using `hPL i`. Establish `e₂` using `hPL' i`. Unfold `LC at e₁ e₂ ⊢`. Simplify using `only`.

Rewrite using `[ht, hs, dl_mul_eq_add_of_isUnit hU hU', map_add, map_add]`. Establish `f₁` using `Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ hc₁) e₁`. Establish `f₂` using `Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ hc₂) e₂`. Use `Ideal.add_mem _ f₁ f₂ using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.

Introduce `Z hZ`. Use `⟨0, 0, fun m _ => ⟨fun _ => 1, ?_, fun i => ?_⟩⟩` and prove the remaining obligations. Unfold `UpperTheory.Kd.C7.BPres GlobalTheory.Col.KumPres`. Use `⟨by simpa using (hζ m).1, by simp, fun i => by simp [pv], fun i => hB.1 i, fun s hs hcyc hsζ => ⟨0, fun i => ?_, ?_⟩⟩` and prove the remaining obligations. Unfold `KumVal`.

Conclude with `⟨1, by simp [pv], by simp⟩`. Unfold `Cg`. Establish `hz` using `hZ m s (Subgroup.mem_inf.mpr ⟨hs, MonoidHom.mem_ker.mpr hcyc⟩)`. Simplify using `[hz]`. Unfold `LC`.

Simplify using `[Fr.tw, Fr.ser, dl, dd]`.
-/
theorem UpperTheory.Kd.C7.pRepAdd :
    UpperTheory.Kd.C7.SRepAdd := by
  intro l _ hl Ω _ _ _ A hA j Φ c β ζ hζ
  have hB := (pBasEx l c).2 β
  have hpv : ∀ (P Q : Polynomial (R0 A)) (z : Ω), pv (P * Q) z = pv P z * pv Q z := by
    intro P Q z; simp [pv, Polynomial.eval₂_mul]
  refine ⟨?_, ?_⟩
  · rintro Z Z' D D' ⟨c₁, m₁, h₁⟩ ⟨c₂, m₂, h₂⟩
    refine ⟨max c₁ c₂, max (max m₁ m₂) 1, fun m hm => ?_⟩
    have hm₁ : m₁ ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hm
    have hm₂ : m₂ ≤ m := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hm
    have hm0 : 1 ≤ m := le_trans (le_max_right _ _) hm
    have hc₁ : m - max c₁ c₂ ≤ m - c₁ := Nat.sub_le_sub_left (le_max_left _ _) m
    have hc₂ : m - max c₁ c₂ ≤ m - c₂ := Nat.sub_le_sub_left (le_max_right _ _) m
    obtain ⟨P, hP, hPL⟩ := h₁ m hm₁
    obtain ⟨P', hP', hPL'⟩ := h₂ m hm₂
    have hQ := pPresMono l hl Ω A hA c β ζ hζ Z Z m (m - c₁) (m - max c₁ c₂) P hc₁
      (fun s _ => by simp [Cg]) hP
    have hQ' := pPresMono l hl Ω A hA c β ζ hζ Z' Z' m (m - c₂) (m - max c₁ c₂) P' hc₂
      (fun s _ => by simp [Cg]) hP'
    unfold UpperTheory.Kd.C7.BPres GlobalTheory.Col.KumPres at hQ hQ'
    obtain ⟨hprim, hnr, hu, ho, hk⟩ := hQ
    obtain ⟨-, -, hu', -, hk'⟩ := hQ'
    refine ⟨fun i => P i * P' i, ?_, fun i => ?_⟩
    · unfold UpperTheory.Kd.C7.BPres GlobalTheory.Col.KumPres
      refine ⟨hprim, hnr, fun i => ?_, ho, fun s hs hcyc hsζ => ?_⟩
      · dsimp only
        rw [hpv]
        obtain ⟨a₁, a₂, a₃⟩ := hu i
        obtain ⟨b₁, b₂, b₃⟩ := hu' i
        dsimp only at a₁ a₂ a₃ b₁ b₂ b₃
        exact ⟨mul_mem a₁ b₁, mul_ne_zero a₂ b₂, by rw [mul_inv]; exact mul_mem a₃ b₃⟩
      · obtain ⟨k, hkv, hkc⟩ := hk s hs hcyc hsζ
        obtain ⟨k', hkv', hkc'⟩ := hk' s hs hcyc hsζ
        have hsH : s ∈ Hm l A m := Subgroup.mem_inf.mpr ⟨hs, MonoidHom.mem_ker.mpr hcyc⟩
        have halg := (pKumAlg l hl Ω A hA ζ hζ m (m - max c₁ c₂) (Nat.sub_le _ _) s hsH).1
        refine ⟨k + k', fun i => ?_, ?_⟩
        · dsimp only
          rw [hpv]
          exact (halg _ _ _ _ (hkv i) (hkv' i)).1
        · have hNz : NeZero (l ^ (m - max c₁ c₂)) :=
            ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
          have key : ∀ i, (((k + k') i).val : Qbar l) = (k i).val + (k' i).val
              - (l : Qbar l) ^ (m - max c₁ c₂)
                * ((((k i).val + (k' i).val) / l ^ (m - max c₁ c₂) : ℕ) : Qbar l) := by
            intro i
            rw [Pi.add_apply, ZMod.val_add, eq_sub_iff_add_eq]
            exact_mod_cast Nat.mod_add_div ((k i).val + (k' i).val) (l ^ (m - max c₁ c₂))
          unfold Cg at hkc hkc' ⊢
          dsimp only
          have hsplit : Z m s 1 + Z' m s 1 - ∑ i, β.val i * (((k + k') i).val : Qbar l)
              = (Z m s 1 - ∑ i, β.val i * ((k i).val : Qbar l))
                + (Z' m s 1 - ∑ i, β.val i * ((k' i).val : Qbar l))
                + ∑ i, β.val i * ((l : Qbar l) ^ (m - max c₁ c₂)
                  * ((((k i).val + (k' i).val) / l ^ (m - max c₁ c₂) : ℕ) : Qbar l)) := by
            simp only [key, mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
            ring
          rw [hsplit]
          have hN : 0 ≤ ‖(l : Qbar l) ^ (m - max c₁ c₂)‖ := norm_nonneg _
          refine le_trans (IsUltrametricDist.norm_add_le_max _ _)
            (max_le (le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le hkc hkc')) ?_)
          refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hN (fun i _ => ?_)
          rw [norm_mul, norm_mul]
          have h1 := ho i
          have h2 := nat_le_one' (l := l) (((k i).val + (k' i).val) / l ^ (m - max c₁ c₂))
          calc _ ≤ 1 * (‖(l : Qbar l) ^ (m - max c₁ c₂)‖ * 1) :=
                mul_le_mul h1 (mul_le_mul_of_nonneg_left h2 hN) (by positivity) zero_le_one
            _ = _ := by ring
    · have hU : IsUnit (Φ.ser (P i)) := (pWD l hl Ω A hA j Φ ζ hζ m hm0 (P i)).2 (hu i)
      have hU' : IsUnit (Φ.ser (P' i)) := (pWD l hl Ω A hA j Φ ζ hζ m hm0 (P' i)).2 (hu' i)
      have hs : Φ.ser (P i * P' i) = Φ.ser (P i) * Φ.ser (P' i) := by
        simp [Fr.ser, Polynomial.map_mul, Polynomial.eval₂_mul]
      have ht : Φ.tw m ((D + D') i) = Φ.tw m (D i) + Φ.tw m (D' i) := by
        simp [Fr.tw, map_add]
      have e₁ := hPL i
      have e₂ := hPL' i
      unfold LC at e₁ e₂ ⊢
      dsimp only
      rw [ht, hs, dl_mul_eq_add_of_isUnit hU hU', map_add, map_add]
      have f₁ := Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ hc₁) e₁
      have f₂ := Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ hc₂) e₂
      convert Ideal.add_mem _ f₁ f₂ using 1
      ring
  · intro Z hZ
    refine ⟨0, 0, fun m _ => ⟨fun _ => 1, ?_, fun i => ?_⟩⟩
    · unfold UpperTheory.Kd.C7.BPres GlobalTheory.Col.KumPres
      refine ⟨by simpa using (hζ m).1, by simp, fun i => by simp [pv], fun i => hB.1 i,
        fun s hs hcyc hsζ => ⟨0, fun i => ?_, ?_⟩⟩
      · unfold KumVal
        exact ⟨1, by simp [pv], by simp⟩
      · unfold Cg
        have hz := hZ m s (Subgroup.mem_inf.mpr ⟨hs, MonoidHom.mem_ker.mpr hcyc⟩)
        simp [hz]
    · unfold LC
      simp [Fr.tw, Fr.ser, dl, dd]
