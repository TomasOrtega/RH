import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.MemSEOfFin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaCmType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankSmulMemAdelesFiniteMultipleOfTensorCongru
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenIntegralTensorAdeleMultiples
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegerOfAlgebraMapMemAdelesFiniteMultiple

noncomputable section

open scoped TensorProduct Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF Formalism.IndefR.LiftF
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HeckeExtend GlobalTheory.HeckeExtend.AtInf GlobalTheory.SplitDetCharF

namespace PositivityTheory.ThKW.Eta

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def UI (σ : E →ₐ[F] E) : Subgroup (AF F ⊗[F] E)ˣ where
  carrier := {x | x ∈ GF F E ∧ (∀ e, IsSplitIdemF σ e → e * (x : AF F ⊗[F] E) = e) ∧
    (x : AF F ⊗[F] E) ∈ SE F E ∧ ((x⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) ∈ SE F E}
  one_mem' := ⟨one_mem _, fun e _ => mul_one e, one_mem_SE, by rw [inv_one]; exact one_mem_SE⟩
  mul_mem' {x y} hx hy := ⟨mul_mem hx.1 hy.1,
    fun e he => by rw [Units.val_mul, ← mul_assoc, hx.2.1 e he, hy.2.1 e he],
    SE_mul hx.2.2.1 hy.2.2.1, by rw [mul_inv_rev]; exact SE_mul hy.2.2.2 hx.2.2.2⟩
  inv_mem' {x} hx := ⟨inv_mem hx.1, fun e he => by
    conv_lhs => rw [← hx.2.1 e he]
    rw [mul_assoc, Units.mul_inv, mul_one], hx.2.2.2, by rw [inv_inv]; exact hx.2.2.1⟩

/- English proof (translation)
Use `haveI : Algebra.IsQuadraticExtension F E := { finrank_eq_two' := hB.cm.2.2.1 }`. Establish `hint : ∀ t : AF F, algebraMap (AF F) (AF F ⊗[F] E) t ∈ SE F E → ∀ v : HeightOneSpectrum (𝓞 F), 2 * t.2 v ∈ v.adicCompletionIntegers F`. Introduce `t ht v`. Use `GlobalTheory.T.finrank_smul_mem_adelesFiniteMultiple_of_tensorCongruence F E 1 t (CE_one ht)` as an intermediate fact. Rewrite `this` using `[hB.cm.2.2.1]`.

Take `⟨c, hc, e⟩` from `this`. Establish `e2 : evalV F v (2 • t.2) = evalV F v (1 • c)` using `congrArg (evalV F v) e`. Rewrite `e2` using `[one_smul, map_nsmul, nsmul_eq_mul, Nat.cast_ofNat]`. Establish `e3 : 2 * t.2 v = c v` using `e2`. Rewrite using `[e3]`.

Conclude with `hc v`. Establish `hn : finU F (sndU F a) ∈ GlobalTheory.QuadSymbol.normGroup F E (AF F)`. Use `(GlobalTheory.IdeleNormChar.mem_normGroup_iff_everywhereNorm E _).2 ⟨fun v => ?_, fun w => ?_⟩` and prove the remaining obligations. Conclude with `local_norm hB v _ (hint _ h1 v) (hint _ h2 v)`. Establish `: GlobalTheory.IdeleNormChar.infComp (finU F (sndU F a)) w = 1` using `Units.ext rfl`.

Rewrite using `[this]`. Conclude with `one_mem _`. Take `⟨x, hx⟩` from `hn`. Take `⟨⟨η₀, h0⟩, h⟩` from `hη`. Rewrite using `[h η₀ h0, ← hx, h0.2.2.1 x, one_pow]`.
-/
theorem eta_fin {σ : E →ₐ[F] E} {B : Base F E} (hB : B.IsGood σ) {η : (AF F ⊗[F] E)ˣ →* Circle} (hη : ResEtaF η 1)
    (a : (AF F)ˣ) (h1 : (idFF F E a : AF F ⊗[F] E) ∈ SE F E) (h2 : (idFF F E a⁻¹ : AF F ⊗[F] E) ∈ SE F E) :
    η (idFF F E (finU F (sndU F a))) = 1 := by
  haveI : Algebra.IsQuadraticExtension F E := { finrank_eq_two' := hB.cm.2.2.1 }
  have hint : ∀ t : AF F, algebraMap (AF F) (AF F ⊗[F] E) t ∈ SE F E → ∀ v : HeightOneSpectrum (𝓞 F),
      2 * t.2 v ∈ v.adicCompletionIntegers F := by
    intro t ht v
    have := GlobalTheory.T.finrank_smul_mem_adelesFiniteMultiple_of_tensorCongruence F E 1 t (CE_one ht)
    rw [hB.cm.2.2.1] at this
    obtain ⟨c, hc, e⟩ := this
    have e2 : evalV F v (2 • t.2) = evalV F v (1 • c) := congrArg (evalV F v) e
    rw [one_smul, map_nsmul, nsmul_eq_mul, Nat.cast_ofNat] at e2
    have e3 : 2 * t.2 v = c v := e2
    rw [e3]
    exact hc v
  have hn : finU F (sndU F a) ∈ GlobalTheory.QuadSymbol.normGroup F E (AF F) := by
    refine (GlobalTheory.IdeleNormChar.mem_normGroup_iff_everywhereNorm E _).2 ⟨fun v => ?_, fun w => ?_⟩
    · exact local_norm hB v _ (hint _ h1 v) (hint _ h2 v)
    · have : GlobalTheory.IdeleNormChar.infComp (finU F (sndU F a)) w = 1 := Units.ext rfl
      rw [this]
      exact one_mem _
  obtain ⟨x, hx⟩ := hn
  obtain ⟨⟨η₀, h0⟩, h⟩ := hη
  rw [h η₀ h0, ← hx, h0.2.2.1 x, one_pow]

/- English proof (translation)
Take `⟨hσσ, hfix⟩` from `GlobalTheory.T.cmExtension_conjugation_involutive_fixedField F E σ hcm`. Set `cU : (AF F ⊗[F] E)ˣ →* (AF F ⊗[F] E)ˣ` to `Units.map (cA σ).toMonoidHom`. Establish `hcW : cU w ∈ WE F E (M * N)`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `CE_cA σ hw.1` as an intermediate fact.

Rewrite `this` using `[map_sub, map_one]`. Then use the resulting hypothesis. Use `CE_cA σ hw.2` as an intermediate fact. Rewrite `this` using `[map_sub, map_one]`. Rewrite using `[← map_inv]`. Conclude with `this`.

Establish `hfixa : cU (idFF F E a) = idFF F E a` using `Units.ext ((cA σ).commutes (a : AF F))`. Establish `hcinc : cU (Units.map (incAF F E).toMonoidHom k) = Units.map (incAF F E).toMonoidHom (Units.map σ.toMonoidHom k)` using `Units.ext rfl`. Set `ζ : Eˣ` to `Units.map σ.toMonoidHom k * k⁻¹`. Establish `hw' : w * (cU w)⁻¹ ∈ WE F E (M * N)` using `mul_mem hw (inv_mem hcW)`. Establish `hζ : Units.map (incAF F E).toMonoidHom ζ = cU x * x⁻¹ * (w * (cU w)⁻¹)`.

Rewrite using `[← h]`. Simplify using `only [ζ, map_mul, map_inv, hfixa, hcinc]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv]`. Normalize the expressions using the abelian group laws.

Establish `hζ' : incAF F E (ζ : E) = cA σ (x : AF F ⊗[F] E) * ((x⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * ((w * (cU w)⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)` using `congrArg Units.val hζ`. Establish `hζS : incAF F E (ζ : E) ∈ SE F E`. Rewrite using `[hζ']`. Conclude with `SE_mul (SE_mul (cA_mem_SE σ hx.2.2.1) hx.2.2.2) (mem_SE_of_CE hw'.1)`. Establish `hζS' : incAF F E (σ ζ) ∈ SE F E` using `cA_mem_SE σ hζS`.

Take `⟨e, he, he', hcc, hφ⟩` from `exists_idem hcm τ`. Establish `q1 : phi τ ((x⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) = 1`. Use `congrArg (phi τ) ((inv_mem hx).2.1 e he)` as an intermediate fact. Rewrite `this` using `[map_mul, hφ, one_mul]`. Then use the resulting hypothesis. Establish `q2 : phi τ (cA σ (x : AF F ⊗[F] E)) = 1`.

Establish `h1` using `congrArg (cAF σ) (hx.2.1 _ he')`. Rewrite `h1` using `[map_mul, hcc]`. Use `congrArg (phi τ) h1` as an intermediate fact. Rewrite `this` using `[map_mul, hφ, one_mul]`. Then use the resulting hypothesis. Take `⟨s, hs, es⟩` from `mem_CE.1 hw'.1`.

Establish `q3 : τ (ζ : E) - 1 = (M * N) • phi τ s`. Rewrite using `[← phi_inc, hζ', map_mul, map_mul, q1, q2, one_mul, one_mul, ← map_nsmul, es, map_sub, map_one]`. Establish `hζv : (ζ : E) = σ k * (k : E)⁻¹` using `by simp [ζ]`. Take `⟨y, hy⟩` from `hfix (((ζ : E) - 1) * σ ((ζ : E) - 1)) (by rw [map_mul, hσσ, mul_comm])`. Establish `hyS : algebraMap (AF F) (AF F ⊗[F] E) (algebraMap F (AF F) y) ∈ SE F E`.

Rewrite using `[← incAF_algebraMap, hy, map_mul, map_sub σ, map_one, map_sub, map_sub, map_one]`. Conclude with `SE_mul (sub_mem hζS one_mem_SE) (sub_mem hζS' one_mem_SE)`. Establish `hy2` using `GlobalTheory.T.finrank_smul_mem_adelesFiniteMultiple_of_tensorCongruence F E 1 _ (CE_one hyS)`. Rewrite `hy2` using `[hcm.2.2.1, ← map_nsmul]`. Take `⟨r, hr⟩` from `GlobalTheory.T.exists_integer_of_algebraMap_mem_adelesFiniteMultiple F _ 1 one_pos hy2`.

Establish `hy0 : 2 • y = 0`. Use `hN (2 • y) ?_ (fun φ => ?_) (2 * (M • phi τ s) * (phi τ (incAF F E (σ ζ)) - 1)) ?_ ?_` and prove the remaining obligations. Rewrite using `[hr, Nat.cast_one, one_mul]`. Conclude with `r.2`. Take `⟨τ', hτ⟩` from `exists_emb_ext (E := E) φ`.

Establish `hφ : φ y = τ' (algebraMap F E y)` using `by rw [← hτ]; rfl`. Establish `hτσ` using `hcm.2.2.2 τ'`. Establish `hk0 : τ' (k : E) ≠ 0` using `(map_ne_zero τ').2 k.ne_zero`. Establish `hζn : ‖τ' (ζ : E)‖ = 1`. Rewrite using `[hζv, map_mul, map_inv₀, hτσ, norm_mul, norm_inv, norm_star]`.

Conclude with `mul_inv_cancel₀ (norm_ne_zero_iff.2 hk0)`. Establish `hxn : ‖τ' ((ζ : E) - 1)‖ ≤ 2`. Combine the equalities or inequalities in the displayed calculation. Use `_ ≤ ‖τ' (ζ : E)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _`. Use `_ = 2 := by rw [hζn, norm_one]; norm_num`.

Rewrite using `[map_nsmul, nsmul_eq_mul, norm_mul, hφ, hy, map_mul, hτσ, norm_mul, norm_star]`. Establish `: ‖((2 : ℕ) : ℂ)‖ = 2` using `by simp`. Rewrite using `[this]`. Use polynomial arithmetic with `[norm_nonneg (τ' ((ζ : E) - 1))]`. Use `mul_mem (mul_mem ?_ (nsmul_mem (phi_mem τ hs) M)) (sub_mem (phi_mem τ hζS') (one_mem _))` and prove the remaining obligations.

Rewrite using `[← one_add_one_eq_two]`. Conclude with `add_mem (one_mem _) (one_mem _)`. Rewrite using `[map_nsmul, ← τ.commutes, hy, map_mul, map_sub, map_one, q3, map_sub σ, map_one, map_sub, map_one, phi_inc]`. Simplify using `only [nsmul_eq_mul]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hy1 : y = 0` using `by simpa using hy0`. Rewrite `hy` using `[hy1, map_zero]`. Establish `hζ1 : (ζ : E) = 1`. Break down `mul_eq_zero.1 hy.symm with h | h` into its components or cases.

Conclude with `sub_eq_zero.1 h`. Conclude with `sub_eq_zero.1 ((map_eq_zero σ).1 h)`. Rewrite `hζ1` using `[hζv]`. Conclude with `(mul_inv_eq_one₀ k.ne_zero).1 hζ1`.
-/
theorem fixed_of_mem {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) {v : HeightOneSpectrum (𝓞 F)} (τ : E →ₐ[F] Fv F v)
    {M N : ℕ} (hN : ∀ y : F, IsIntegral ℤ y → (∀ φ : F →+* ℂ, ‖φ y‖ ≤ 8) →
      ∀ c ∈ v.adicCompletionIntegers F, algebraMap F (Fv F v) y = N • c → y = 0)
    {x w : (AF F ⊗[F] E)ˣ} (hx : x ∈ UI σ) (hw : w ∈ WE F E (M * N)) (k : Eˣ) (a : (AF F)ˣ)
    (h : Units.map (incAF F E).toMonoidHom k * idFF F E a * w = x) : σ k = (k : E) := by
  obtain ⟨hσσ, hfix⟩ := GlobalTheory.T.cmExtension_conjugation_involutive_fixedField F E σ hcm
  let cU : (AF F ⊗[F] E)ˣ →* (AF F ⊗[F] E)ˣ := Units.map (cA σ).toMonoidHom
  have hcW : cU w ∈ WE F E (M * N) := by
    refine ⟨?_, ?_⟩
    · have := CE_cA σ hw.1
      rwa [map_sub, map_one] at this
    · have := CE_cA σ hw.2
      rw [map_sub, map_one] at this
      rw [← map_inv]
      exact this
  have hfixa : cU (idFF F E a) = idFF F E a := Units.ext ((cA σ).commutes (a : AF F))
  have hcinc : cU (Units.map (incAF F E).toMonoidHom k) =
      Units.map (incAF F E).toMonoidHom (Units.map σ.toMonoidHom k) := Units.ext rfl
  let ζ : Eˣ := Units.map σ.toMonoidHom k * k⁻¹
  have hw' : w * (cU w)⁻¹ ∈ WE F E (M * N) := mul_mem hw (inv_mem hcW)
  have hζ : Units.map (incAF F E).toMonoidHom ζ = cU x * x⁻¹ * (w * (cU w)⁻¹) := by
    rw [← h]
    simp only [ζ, map_mul, map_inv, hfixa, hcinc]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  have hζ' : incAF F E (ζ : E) = cA σ (x : AF F ⊗[F] E) * ((x⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) *
      ((w * (cU w)⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) := congrArg Units.val hζ
  have hζS : incAF F E (ζ : E) ∈ SE F E := by
    rw [hζ']
    exact SE_mul (SE_mul (cA_mem_SE σ hx.2.2.1) hx.2.2.2) (mem_SE_of_CE hw'.1)
  have hζS' : incAF F E (σ ζ) ∈ SE F E := cA_mem_SE σ hζS
  obtain ⟨e, he, he', hcc, hφ⟩ := exists_idem hcm τ
  have q1 : phi τ ((x⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) = 1 := by
    have := congrArg (phi τ) ((inv_mem hx).2.1 e he)
    rwa [map_mul, hφ, one_mul] at this
  have q2 : phi τ (cA σ (x : AF F ⊗[F] E)) = 1 := by
    have h1 := congrArg (cAF σ) (hx.2.1 _ he')
    rw [map_mul, hcc] at h1
    have := congrArg (phi τ) h1
    rwa [map_mul, hφ, one_mul] at this
  obtain ⟨s, hs, es⟩ := mem_CE.1 hw'.1
  have q3 : τ (ζ : E) - 1 = (M * N) • phi τ s := by
    rw [← phi_inc, hζ', map_mul, map_mul, q1, q2, one_mul, one_mul, ← map_nsmul, es, map_sub, map_one]
  have hζv : (ζ : E) = σ k * (k : E)⁻¹ := by simp [ζ]
  obtain ⟨y, hy⟩ := hfix (((ζ : E) - 1) * σ ((ζ : E) - 1)) (by rw [map_mul, hσσ, mul_comm])
  have hyS : algebraMap (AF F) (AF F ⊗[F] E) (algebraMap F (AF F) y) ∈ SE F E := by
    rw [← incAF_algebraMap, hy, map_mul, map_sub σ, map_one, map_sub, map_sub, map_one]
    exact SE_mul (sub_mem hζS one_mem_SE) (sub_mem hζS' one_mem_SE)
  have hy2 := GlobalTheory.T.finrank_smul_mem_adelesFiniteMultiple_of_tensorCongruence F E 1 _ (CE_one hyS)
  rw [hcm.2.2.1, ← map_nsmul] at hy2
  obtain ⟨r, hr⟩ := GlobalTheory.T.exists_integer_of_algebraMap_mem_adelesFiniteMultiple F _ 1 one_pos hy2
  have hy0 : 2 • y = 0 := by
    refine hN (2 • y) ?_ (fun φ => ?_) (2 * (M • phi τ s) * (phi τ (incAF F E (σ ζ)) - 1)) ?_ ?_
    · rw [hr, Nat.cast_one, one_mul]
      exact r.2
    · obtain ⟨τ', hτ⟩ := exists_emb_ext (E := E) φ
      have hφ : φ y = τ' (algebraMap F E y) := by rw [← hτ]; rfl
      have hτσ := hcm.2.2.2 τ'
      have hk0 : τ' (k : E) ≠ 0 := (map_ne_zero τ').2 k.ne_zero
      have hζn : ‖τ' (ζ : E)‖ = 1 := by
        rw [hζv, map_mul, map_inv₀, hτσ, norm_mul, norm_inv, norm_star]
        exact mul_inv_cancel₀ (norm_ne_zero_iff.2 hk0)
      have hxn : ‖τ' ((ζ : E) - 1)‖ ≤ 2 := by
        calc ‖τ' ((ζ : E) - 1)‖ = ‖τ' (ζ : E) - 1‖ := by rw [map_sub, map_one]
        _ ≤ ‖τ' (ζ : E)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [hζn, norm_one]; norm_num
      rw [map_nsmul, nsmul_eq_mul, norm_mul, hφ, hy, map_mul, hτσ, norm_mul, norm_star]
      have : ‖((2 : ℕ) : ℂ)‖ = 2 := by simp
      rw [this]
      nlinarith [norm_nonneg (τ' ((ζ : E) - 1))]
    · refine mul_mem (mul_mem ?_ (nsmul_mem (phi_mem τ hs) M)) (sub_mem (phi_mem τ hζS') (one_mem _))
      rw [← one_add_one_eq_two]
      exact add_mem (one_mem _) (one_mem _)
    · rw [map_nsmul, ← τ.commutes, hy, map_mul, map_sub, map_one, q3, map_sub σ, map_one, map_sub, map_one, phi_inc]
      simp only [nsmul_eq_mul]
      push_cast
      ring
  have hy1 : y = 0 := by simpa using hy0
  rw [hy1, map_zero] at hy
  have hζ1 : (ζ : E) = 1 := by
    rcases mul_eq_zero.1 hy.symm with h | h
    · exact sub_eq_zero.1 h
    · exact sub_eq_zero.1 ((map_eq_zero σ).1 h)
  rw [hζv] at hζ1
  exact (mul_inv_eq_one₀ k.ne_zero).1 hζ1

/- English proof (translation)
Take `⟨M, hM, hMk⟩` from `exists_level η hc`. Take `⟨N, hN, hNk⟩` from `exists_sep B.v₁`. Use `⟨M * N, Nat.mul_pos hM hN, fun x hx hV => ?_⟩` and prove the remaining obligations. Take `⟨y, hy, w, hw, hyw⟩` from `Subgroup.mem_sup.1 hV`. Take `⟨_, ⟨k, rfl⟩, _, ⟨a, rfl⟩, rfl⟩` from `Subgroup.mem_sup.1 hy`.

Establish `hk` using `fixed_of_mem hB.cm B.τ₁ hNk hx hw k a hyw`. Take `⟨f, hf⟩` from `(GlobalTheory.T.cmExtension_conjugation_involutive_fixedField F E σ hB.cm).2 k hk`. Establish `hf0 : f ≠ 0`. Introduce and unpack `rfl`. Rewrite `hf` using `[map_zero]`.

Conclude with `k.ne_zero hf.symm`. Set `fU : (AF F)ˣ` to `Units.map (algebraMap F (AF F)).toMonoidHom (Units.mk0 f hf0)`. Establish `hinc : Units.map (incAF F E).toMonoidHom k = idFF F E fU`. Apply `Units.ext` to reduce the goal to its premises. Use `show incAF F E (k : E) = algebraMap (AF F) (AF F ⊗[F] E) (algebraMap F (AF F) f)`.

Rewrite using `[← hf, incAF_algebraMap]`. Rewrite `hyw` using `[hinc, ← map_mul]`. Generalize the expression as in `fU * a = a' at hyw`. Establish `e1 : idFF F E a' = x * w⁻¹` using `by rw [← hyw, mul_inv_cancel_right]`. Establish `e2 : idFF F E a'⁻¹ = x⁻¹ * w` using `by rw [map_inv, e1, mul_inv, inv_inv]`.

Establish `h1` using `eta_fin hB hη a' (by rw [e1]; exact SE_mul hx.2.2.1 (mem_SE_of_CE hw.2)) (by rw [e2]; exact SE_mul hx.2.2.2 (mem_SE_of_CE hw.1))`. Set `p : (AF F ⊗[F] E)ˣ →* (AF F ⊗[F] E)ˣ` to `Units.map (cut (fI F E) fI_idem)`. Establish `hp : ∀ z : (AF F ⊗[F] E)ˣ, (p z : AF F ⊗[F] E) = (1 - fI F E) + fI F E * z` using `fun _ => rfl`. Establish `px : p x = x` using `Units.ext (by`. Establish `: (1 - fI F E) * (x : AF F ⊗[F] E) = 1 - fI F E` using `hx.1`.

Rewrite using `[hp]`. Take the linear combination `-this)`. Establish `pa : p (idFF F E a') = idFF F E (finU F (sndU F a'))` using `Units.ext (by`. Rewrite using `[hp]`. Use `show 1 - algebraMap (AF F) (AF F ⊗[F] E) (uFin F) + algebraMap (AF F) (AF F ⊗[F] E) (uFin F) * algebraMap (AF F) (AF F ⊗[F] E) (a' : AF F) = algebraMap (AF F) (AF F ⊗[F] E) (pairA F 1 (a' : AF F).2)`.

Rewrite using `[← map_mul, ← map_one (algebraMap (AF F) (AF F ⊗[F] E)), ← map_sub, ← map_add, uFin_mul]`. Use `congr 1`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use `show (1 : Ainf F) - 0 + 0 = 1`. Simplify using the standard rewrite rules.

Use `show (1 : Af F) - 1 + (a' : AF F).2 = (a' : AF F).2 simp)`. Establish `pC : ∀ z : (AF F ⊗[F] E)ˣ, (z : AF F ⊗[F] E) - 1 ∈ CE F E (M * N) → (p z : AF F ⊗[F] E) - 1 ∈ CE F E M`. Introduce `z hz`. Take `⟨s, hs, e⟩` from `mem_CE.1 (CE_mul hz)`. Use `mem_CE.2 ⟨fI F E * s, SE_mul fI_mem hs, ?_⟩` and prove the remaining obligations.

Rewrite using `[← mul_smul_comm, e, hp]`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : η (p w) = 1`. Use `hMk _ ⟨pC w hw.1, by rw [← map_inv]; exact pC _ hw.2⟩ ?_` and prove the remaining obligations. Use `show (1 - fI F E) * (p w : AF F ⊗[F] E) = 1 - fI F E`.

Rewrite using `[hp]`. Take the linear combination `(1 - (w : AF F ⊗[F] E)) * (fI_idem (F := F) (E := E))`. Rewrite using `[← px, ← hyw, map_mul, map_mul, pa, h1, h2, mul_one]`.
-/
theorem key {σ : E →ₐ[F] E} {B : Base F E} (hB : B.IsGood σ) {η : (AF F ⊗[F] E)ˣ →* Circle} (hc : Continuous η)
    (hη : ResEtaF η 1) : ∃ N : ℕ, 0 < N ∧ ∀ x ∈ UI σ,
      x ∈ ((Units.map (incAF F E).toMonoidHom).range ⊔ (idFF F E).range) ⊔ WE F E N → η x = 1 := by
  obtain ⟨M, hM, hMk⟩ := exists_level η hc
  obtain ⟨N, hN, hNk⟩ := exists_sep B.v₁
  refine ⟨M * N, Nat.mul_pos hM hN, fun x hx hV => ?_⟩
  obtain ⟨y, hy, w, hw, hyw⟩ := Subgroup.mem_sup.1 hV
  obtain ⟨_, ⟨k, rfl⟩, _, ⟨a, rfl⟩, rfl⟩ := Subgroup.mem_sup.1 hy
  have hk := fixed_of_mem hB.cm B.τ₁ hNk hx hw k a hyw
  obtain ⟨f, hf⟩ := (GlobalTheory.T.cmExtension_conjugation_involutive_fixedField F E σ hB.cm).2 k hk
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [map_zero] at hf
    exact k.ne_zero hf.symm
  let fU : (AF F)ˣ := Units.map (algebraMap F (AF F)).toMonoidHom (Units.mk0 f hf0)
  have hinc : Units.map (incAF F E).toMonoidHom k = idFF F E fU := by
    apply Units.ext
    show incAF F E (k : E) = algebraMap (AF F) (AF F ⊗[F] E) (algebraMap F (AF F) f)
    rw [← hf, incAF_algebraMap]
  rw [hinc, ← map_mul] at hyw
  generalize fU * a = a' at hyw
  have e1 : idFF F E a' = x * w⁻¹ := by rw [← hyw, mul_inv_cancel_right]
  have e2 : idFF F E a'⁻¹ = x⁻¹ * w := by rw [map_inv, e1, mul_inv, inv_inv]
  have h1 := eta_fin hB hη a' (by rw [e1]; exact SE_mul hx.2.2.1 (mem_SE_of_CE hw.2))
    (by rw [e2]; exact SE_mul hx.2.2.2 (mem_SE_of_CE hw.1))
  let p : (AF F ⊗[F] E)ˣ →* (AF F ⊗[F] E)ˣ := Units.map (cut (fI F E) fI_idem)
  have hp : ∀ z : (AF F ⊗[F] E)ˣ, (p z : AF F ⊗[F] E) = (1 - fI F E) + fI F E * z := fun _ => rfl
  have px : p x = x := Units.ext (by
    have : (1 - fI F E) * (x : AF F ⊗[F] E) = 1 - fI F E := hx.1
    rw [hp]
    linear_combination -this)
  have pa : p (idFF F E a') = idFF F E (finU F (sndU F a')) := Units.ext (by
    rw [hp]
    show 1 - algebraMap (AF F) (AF F ⊗[F] E) (uFin F) + algebraMap (AF F) (AF F ⊗[F] E) (uFin F) *
      algebraMap (AF F) (AF F ⊗[F] E) (a' : AF F) = algebraMap (AF F) (AF F ⊗[F] E) (pairA F 1 (a' : AF F).2)
    rw [← map_mul, ← map_one (algebraMap (AF F) (AF F ⊗[F] E)), ← map_sub, ← map_add, uFin_mul]
    congr 1
    refine Prod.ext ?_ ?_
    · show (1 : Ainf F) - 0 + 0 = 1
      simp
    · show (1 : Af F) - 1 + (a' : AF F).2 = (a' : AF F).2
      simp)
  have pC : ∀ z : (AF F ⊗[F] E)ˣ, (z : AF F ⊗[F] E) - 1 ∈ CE F E (M * N) → (p z : AF F ⊗[F] E) - 1 ∈ CE F E M := by
    intro z hz
    obtain ⟨s, hs, e⟩ := mem_CE.1 (CE_mul hz)
    refine mem_CE.2 ⟨fI F E * s, SE_mul fI_mem hs, ?_⟩
    rw [← mul_smul_comm, e, hp]
    ring
  have h2 : η (p w) = 1 := by
    refine hMk _ ⟨pC w hw.1, by rw [← map_inv]; exact pC _ hw.2⟩ ?_
    show (1 - fI F E) * (p w : AF F ⊗[F] E) = 1 - fI F E
    rw [hp]
    linear_combination (1 - (w : AF F ⊗[F] E)) * (fI_idem (F := F) (E := E))
  rw [← px, ← hyw, map_mul, map_mul, pa, h1, h2, mul_one]

end PositivityTheory.ThKW.Eta

namespace PositivityTheory.ThKW

open Eta

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B hB`. Use `haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _`. Take `⟨η, h1, h2, h3⟩` from `GlobalTheory.EtaCMType.exists_eta_cmType F E σ B hB`. Take `⟨N, hN, hk⟩` from `key hB h1.1 h2`. Take `⟨ν, hV, hU⟩` from `exists_ext _ _ η hk`.

Establish `hW : ∀ z ∈ WE F E N, ν z = 1` using `fun z hz => hV z (Subgroup.mem_sup_right hz)`. Establish `hWo : IsOpen (WE F E N : Set (AF F ⊗[F] E)ˣ)`. Establish `ho` using `CE_isOpen F E N hN`. Establish `hcv : Continuous fun z : (AF F ⊗[F] E)ˣ => (z : AF F ⊗[F] E) - 1` using `Units.continuous_val.sub continuous_const`. Establish `hci : Continuous fun z : (AF F ⊗[F] E)ˣ => ((z⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1` using `Units.continuous_coe_inv.sub continuous_const`.

Conclude with `(ho.preimage hcv).inter (ho.preimage hci)`. Establish `hν : Continuous ν`. Use `continuous_of_continuousAt_one _ ?_` and prove the remaining obligations. Unfold `ContinuousAt`. Rewrite using `[map_one]`.

Use `tendsto_const_nhds.congr' ?_` and prove the remaining obligations. Use `filter_upwards [hWo.mem_nhds (one_mem _)] with z hz`. Conclude with `(hW z hz).symm`. Use `⟨η * ν⁻¹, ⟨h1.1.mul hν.inv, fun x => ?_⟩, ⟨h2.1, fun e he a => ?_⟩, fun z hz => ?_, fun x a b c d => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `η _ * (ν _)⁻¹ = 1`.

Rewrite using `[h1.2, hV _ (Subgroup.mem_sup_left (Subgroup.mem_sup_left ⟨x, rfl⟩)), inv_one, one_mul]`. Express the relevant statement in the definitionally equal form `η _ * (ν _)⁻¹ = _`. Rewrite using `[h2.2 e he, hV _ (Subgroup.mem_sup_left (Subgroup.mem_sup_right ⟨a, rfl⟩)), inv_one, mul_one]`. Express the relevant statement in the definitionally equal form `((η z * (ν z)⁻¹ : Circle) : ℂ) = _`. Establish `: z ∈ WE F E N`.

Use `⟨mem_CE_of_atInf F E _ hN _ hz, mem_CE_of_atInf F E _ hN _ ?_⟩` and prove the remaining obligations. Introduce `u hu`. Establish `e : ((z⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1 = -(((z⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * ((z : AF F ⊗[F] E) - 1))`. Rewrite using `[mul_sub, Units.inv_mul, mul_one, neg_sub]`. Rewrite using `[e, smul_neg, ← mul_smul_comm, hz u hu, mul_zero, neg_zero]`.

Rewrite using `[hW z this, inv_one, mul_one]`. Conclude with `h3 z hz`. Express the relevant statement in the definitionally equal form `η _ * (ν _)⁻¹ = 1`. Establish `hx : x ∈ UI σ`. Use `⟨?_, b, mem_SE_of_fin c, mem_SE_of_fin d⟩` and prove the remaining obligations.

Use `show (1 - fI F E) * (x : AF F ⊗[F] E) = 1 - fI F E`. Rewrite using `[← sub_eq_zero, ← mul_sub_one]`. Use `adele_tensor_ext _ ?_ ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_sub _ (x : AF F ⊗[F] E), a, map_one, sub_self, mul_zero]`. Rewrite using `[map_mul, map_sub, map_one, fin_fI, sub_self, zero_mul]`.

Rewrite using `[hU x hx, mul_inv_cancel]`.
-/
theorem exists_eta : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∃ η : (AF F ⊗[F] E)ˣ →* Circle,
      IsHeckeCharF η ∧ ResEtaF η 1 ∧ HasExp B.emb η (fun _ => 1) ∧ UnramInert σ η := by
  intro F E _ _ _ _ _ σ B hB
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨η, h1, h2, h3⟩ := GlobalTheory.EtaCMType.exists_eta_cmType F E σ B hB
  obtain ⟨N, hN, hk⟩ := key hB h1.1 h2
  obtain ⟨ν, hV, hU⟩ := exists_ext _ _ η hk
  have hW : ∀ z ∈ WE F E N, ν z = 1 := fun z hz => hV z (Subgroup.mem_sup_right hz)
  have hWo : IsOpen (WE F E N : Set (AF F ⊗[F] E)ˣ) := by
    have ho := CE_isOpen F E N hN
    have hcv : Continuous fun z : (AF F ⊗[F] E)ˣ => (z : AF F ⊗[F] E) - 1 :=
      Units.continuous_val.sub continuous_const
    have hci : Continuous fun z : (AF F ⊗[F] E)ˣ => ((z⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1 :=
      Units.continuous_coe_inv.sub continuous_const
    exact (ho.preimage hcv).inter (ho.preimage hci)
  have hν : Continuous ν := by
    refine continuous_of_continuousAt_one _ ?_
    unfold ContinuousAt
    rw [map_one]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hWo.mem_nhds (one_mem _)] with z hz
    exact (hW z hz).symm
  refine ⟨η * ν⁻¹, ⟨h1.1.mul hν.inv, fun x => ?_⟩, ⟨h2.1, fun e he a => ?_⟩, fun z hz => ?_, fun x a b c d => ?_⟩
  · change η _ * (ν _)⁻¹ = 1
    rw [h1.2, hV _ (Subgroup.mem_sup_left (Subgroup.mem_sup_left ⟨x, rfl⟩)), inv_one, one_mul]
  · change η _ * (ν _)⁻¹ = _
    rw [h2.2 e he, hV _ (Subgroup.mem_sup_left (Subgroup.mem_sup_right ⟨a, rfl⟩)), inv_one, mul_one]
  · change ((η z * (ν z)⁻¹ : Circle) : ℂ) = _
    have : z ∈ WE F E N := by
      refine ⟨mem_CE_of_atInf F E _ hN _ hz, mem_CE_of_atInf F E _ hN _ ?_⟩
      intro u hu
      have e : ((z⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1 =
          -(((z⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * ((z : AF F ⊗[F] E) - 1)) := by
        rw [mul_sub, Units.inv_mul, mul_one, neg_sub]
      rw [e, smul_neg, ← mul_smul_comm, hz u hu, mul_zero, neg_zero]
    rw [hW z this, inv_one, mul_one]
    exact h3 z hz
  · change η _ * (ν _)⁻¹ = 1
    have hx : x ∈ UI σ := by
      refine ⟨?_, b, mem_SE_of_fin c, mem_SE_of_fin d⟩
      show (1 - fI F E) * (x : AF F ⊗[F] E) = 1 - fI F E
      rw [← sub_eq_zero, ← mul_sub_one]
      refine adele_tensor_ext _ ?_ ?_
      · rw [map_mul, map_sub _ (x : AF F ⊗[F] E), a, map_one, sub_self, mul_zero]
      · rw [map_mul, map_sub, map_one, fin_fI, sub_self, zero_mul]
    rw [hU x hx, mul_inv_cancel]

end PositivityTheory.ThKW

end
