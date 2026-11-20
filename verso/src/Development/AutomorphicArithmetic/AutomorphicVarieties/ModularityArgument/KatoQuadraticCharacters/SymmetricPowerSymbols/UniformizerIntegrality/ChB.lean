import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.UniformizerIntegrality.PtTopOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.UniformizerIntegrality.FixInv

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Sym.PT

attribute [local instance] algMdl

/- English proof (translation)
Introduce `Ω _ _ _ ε X l n M hl hM hdvd u hu0 huF e he`. Establish `hAC : IsAlgClosed Ω` using `IsAlgClosure.isAlgClosed ℚ`. Establish `hN : l ^ n ≠ 0` using `pow_ne_zero _ hl.ne_zero`. Use `haveI : NeZero (l ^ n) := ⟨hN⟩`. Establish `huL : u ∈ topL X M` using `mdl_le_lev X _ _ huF`.

Establish `hpow` using `topRoot_pow X M hN huL`. Establish `h1 : e (topRoot X M (l ^ n) u) ^ l ^ n = io X u`. Rewrite using `[← map_pow, hpow]`. Conclude with `he ⟨u, huL⟩`. Use `⟨h1, ?_⟩` and prove the remaining obligations.

Introduce `σ hσ`. Take `⟨hc1, -, -, -, hlg⟩` from `cjB Ω ε X M e he`. Establish `hθ0 : topRoot X M (l ^ n) u ≠ 0`. Introduce `h`. Rewrite `hpow` using `[h, zero_pow hN]`.

Apply `hu0` to reduce the goal to its premises. Establish `h2 : (⟨u, huL⟩ : topL X M) = 0` using `(algebraMap (topL X M) (topBar X M)).injective (hpow.symm.trans (map_zero _).symm)`. Conclude with `congrArg Subtype.val h2`. Establish `hfix : cj X M e σ (topRoot X M (l ^ n) u ^ l ^ n) = topRoot X M (l ^ n) u ^ l ^ n`. Rewrite using `[hpow]`.

Establish `h3 : (algebraMap (topL X M) (topBar X M)) ⟨u, huL⟩ = algebraMap (topF X M) (topBar X M) ⟨u, huF⟩`. Rewrite using `[IsScalarTower.algebraMap_apply (topF X M) (topL X M) (topBar X M)]`. Both sides reduce to the same expression. Rewrite using `[h3]`. Conclude with `(cj X M e σ).commutes _`.

Establish `hζ` using `isPrimitiveRoot_topZeta X M hl.ne_zero n`. Establish `hr : (cj X M e σ (topRoot X M (l ^ n) u) * (topRoot X M (l ^ n) u)⁻¹) ^ l ^ n = 1`. Rewrite using `[mul_pow, inv_pow, ← map_pow, hfix]`. Conclude with `mul_inv_cancel₀ (pow_ne_zero _ hθ0)`. Take `⟨k, hk, hkr⟩` from `hζ.eq_pow_of_pow_eq_one hr`.

Establish `hex : ∃ i : ZMod (l ^ n), cj X M e σ (topRoot X M (l ^ n) u) = topZeta X M l n ^ i.val * topRoot X M (l ^ n) u`. Use `⟨(k : ZMod (l ^ n)), ?_⟩` and prove the remaining obligations. Rewrite using `[ZMod.val_natCast_of_lt hk, hkr, inv_mul_cancel_right₀ hθ0]`. Rewrite using `[topChar_apply X hl.ne_zero hdvd huF hu0 (cj X M e σ)]`. Use `show lg X (l ^ n) (σ (e (topRoot X M (l ^ n) u))) (e (topRoot X M (l ^ n) u)) = _`.

Rewrite using `[← hc1 σ hσ]`. Apply `hlg l n hl.ne_zero σ hσ _ _ hθ0` to reduce the goal to its premises. Simplify using `only [GlobalTheory.NeedB.kum, dif_pos hex]`. Conclude with `hex.choose_spec`.
-/
theorem UpperTheory.V.Z.Kato.Sym.PT.chB : UpperTheory.V.Z.Kato.Sym.PT.ChB := by
  intro Ω _ _ _ ε X l n M hl hM hdvd u hu0 huF e he
  have hAC : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hN : l ^ n ≠ 0 := pow_ne_zero _ hl.ne_zero
  haveI : NeZero (l ^ n) := ⟨hN⟩
  have huL : u ∈ topL X M := mdl_le_lev X _ _ huF
  have hpow := topRoot_pow X M hN huL
  have h1 : e (topRoot X M (l ^ n) u) ^ l ^ n = io X u := by
    rw [← map_pow, hpow]
    exact he ⟨u, huL⟩
  refine ⟨h1, ?_⟩
  intro σ hσ
  obtain ⟨hc1, -, -, -, hlg⟩ := cjB Ω ε X M e he
  have hθ0 : topRoot X M (l ^ n) u ≠ 0 := by
    intro h
    rw [h, zero_pow hN] at hpow
    apply hu0
    have h2 : (⟨u, huL⟩ : topL X M) = 0 :=
      (algebraMap (topL X M) (topBar X M)).injective (hpow.symm.trans (map_zero _).symm)
    exact congrArg Subtype.val h2
  have hfix : cj X M e σ (topRoot X M (l ^ n) u ^ l ^ n) = topRoot X M (l ^ n) u ^ l ^ n := by
    rw [hpow]
    have h3 : (algebraMap (topL X M) (topBar X M)) ⟨u, huL⟩
        = algebraMap (topF X M) (topBar X M) ⟨u, huF⟩ := by
      rw [IsScalarTower.algebraMap_apply (topF X M) (topL X M) (topBar X M)]
      rfl
    rw [h3]
    exact (cj X M e σ).commutes _
  have hζ := isPrimitiveRoot_topZeta X M hl.ne_zero n
  have hr : (cj X M e σ (topRoot X M (l ^ n) u) * (topRoot X M (l ^ n) u)⁻¹) ^ l ^ n = 1 := by
    rw [mul_pow, inv_pow, ← map_pow, hfix]
    exact mul_inv_cancel₀ (pow_ne_zero _ hθ0)
  obtain ⟨k, hk, hkr⟩ := hζ.eq_pow_of_pow_eq_one hr
  have hex : ∃ i : ZMod (l ^ n),
      cj X M e σ (topRoot X M (l ^ n) u) = topZeta X M l n ^ i.val * topRoot X M (l ^ n) u := by
    refine ⟨(k : ZMod (l ^ n)), ?_⟩
    rw [ZMod.val_natCast_of_lt hk, hkr, inv_mul_cancel_right₀ hθ0]
  rw [topChar_apply X hl.ne_zero hdvd huF hu0 (cj X M e σ)]
  show lg X (l ^ n) (σ (e (topRoot X M (l ^ n) u))) (e (topRoot X M (l ^ n) u)) = _
  rw [← hc1 σ hσ]
  apply hlg l n hl.ne_zero σ hσ _ _ hθ0
  simp only [GlobalTheory.NeedB.kum, dif_pos hex]
  exact hex.choose_spec
