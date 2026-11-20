import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.AdaptedPlaneBasis

open GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Take `⟨y, hy, rfl⟩` from `hu`. Set `ιR : E →ₐ[F] Fv F v ⊗[F] E` to `Algebra.TensorProduct.includeRight`. Use `⟨M.map ιR *ᵥ y, ?_, ?_⟩` and prove the remaining obligations. Use `latLoc_induction (p := fun y => M.map ιR *ᵥ y ∈ latLoc F L' v) ?_ ?_ ?_ ?_ hy` and prove the remaining obligations. Introduce `a ha x hx`.

Establish `e : M.map ιR *ᵥ (fun i => a ⊗ₜ[F] x i) = fun i => a ⊗ₜ[F] (M *ᵥ x) i`. Use function extensionality and compare the values at `i`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.map_apply, ιR, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, TensorProduct.tmul_sum]`. Rewrite using `[e]`. Conclude with `tmul_mem_latLoc ha (hM x hx)`.

Rewrite using `[Matrix.mulVec_zero]`. Conclude with `zero_mem _`. Introduce `y z hy hz`. Rewrite using `[Matrix.mulVec_add]`. Conclude with `add_mem hy hz`.

Introduce `y hy`. Rewrite using `[Matrix.mulVec_neg]`. Conclude with `neg_mem hy`. Use function extensionality and compare the values at `i`. Simplify using `only [splitVec, Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, ιR, Algebra.TensorProduct.includeRight_apply, splitProj_tmul, one_mul]`.
-/
theorem mulVec_mem_splitLat {v : Pl F} (τ : E →ₐ[F] Fv F v) {m k : ℕ} (M : Matrix (Fin m) (Fin k) E)
    {L : Submodule (𝓞 E) (Fin k → E)} {L' : Submodule (𝓞 E) (Fin m → E)} (hM : ∀ x ∈ L, M *ᵥ x ∈ L')
    {u : Fin k → Fv F v} (hu : u ∈ splitLat τ L) : M.map τ *ᵥ u ∈ splitLat τ L' := by
  obtain ⟨y, hy, rfl⟩ := hu
  let ιR : E →ₐ[F] Fv F v ⊗[F] E := Algebra.TensorProduct.includeRight
  refine ⟨M.map ιR *ᵥ y, ?_, ?_⟩
  · refine latLoc_induction (p := fun y => M.map ιR *ᵥ y ∈ latLoc F L' v) ?_ ?_ ?_ ?_ hy
    · intro a ha x hx
      have e : M.map ιR *ᵥ (fun i => a ⊗ₜ[F] x i) = fun i => a ⊗ₜ[F] (M *ᵥ x) i := by
        funext i
        simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, ιR, Algebra.TensorProduct.includeRight_apply,
          Algebra.TensorProduct.tmul_mul_tmul, one_mul, TensorProduct.tmul_sum]
      rw [e]
      exact tmul_mem_latLoc ha (hM x hx)
    · rw [Matrix.mulVec_zero]; exact zero_mem _
    · intro y z hy hz; rw [Matrix.mulVec_add]; exact add_mem hy hz
    · intro y hy; rw [Matrix.mulVec_neg]; exact neg_mem hy
  · funext i
    simp only [splitVec, Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, ιR,
      Algebra.TensorProduct.includeRight_apply, splitProj_tmul, one_mul]

/- English proof (translation)
Set `c : E →+* ℂ` to `(IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom`. Apply `c.injective` to reduce the goal to its premises. Rewrite using `[h.2.2.2 c, h.2.2.2 c, star_star]`.
-/
theorem sigma_sigma {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  let c : E →+* ℂ := (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom
  apply c.injective
  rw [h.2.2.2 c, h.2.2.2 c, star_star]

/- English proof (translation)
Establish `hJ' : ∀ i j, σ (J i j) = -J j i` using `fun i j => hJ j i`. Simplify using `only [form, Matrix.mulVec, dotProduct, map_sum, map_mul, sigma_sigma h, hJ', Finset.mul_sum, ← Finset.sum_neg_distrib]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem form_swap {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {k : ℕ} {J : Matrix (Fin k) (Fin k) E}
    (hJ : ∀ i j, σ (J j i) = -J i j) (x y : Fin k → E) : form σ J y x = -σ (form σ J x y) := by
  have hJ' : ∀ i j, σ (J i j) = -J j i := fun i j => hJ j i
  simp only [form, Matrix.mulVec, dotProduct, map_sum, map_mul, sigma_sigma h, hJ', Finset.mul_sum,
    ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Apply the tactic sequence `unfold skip; split_ifs <;> omega`.
-/
theorem skip_lt {i₀ i₁ j k : ℕ} (h : j < k) : skip i₀ i₁ j < skip i₀ i₁ k := by
  unfold skip; split_ifs <;> omega

/- English proof (translation)
Apply the tactic sequence `unfold skip; split_ifs <;> omega`.
-/
theorem skip_le (i₀ i₁ j : ℕ) : skip i₀ i₁ j ≤ j + 2 := by
  unfold skip; split_ifs <;> omega

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B hB n n₁ W W₁ H i₀ i₁ r s hW hH v`. Use `set τ := B.τ v`. Establish `hcm` using `hB.cm`. Establish `hsk : ∀ j : Fin n₁, skip i₀ i₁ j < n` using `fun j => by`. Use `skip_le i₀ i₁ j` as an intermediate fact.

Use `hH.rank` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Set `sk : Fin n₁ → Fin n` to `fun j => ⟨skip i₀ i₁ j, hsk j⟩`. Establish `skinj : Function.Injective sk`. Introduce `j k e`.

Establish `e' : skip i₀ i₁ j = skip i₀ i₁ k` using `congrArg Fin.val e`. Break down `lt_trichotomy j.1 k.1 with h | h | h` into its components or cases. Conclude with `absurd e' (skip_lt h).ne`. Conclude with `Fin.ext h`. Conclude with `absurd e' (skip_lt h).ne'`.

Set `S : Matrix (Fin n) (Fin n₁) (Fv F v)` to `fun i j => if i = sk j then 1 else 0`. Establish `hSsk : ∀ (u : Fin n₁ → Fv F v) j, (S *ᵥ u) (sk j) = u j` using `fun u j => by`. Simplify using `only [S, Matrix.mulVec, dotProduct]`. Rewrite using `[Finset.sum_eq_single j]`. Simplify using the standard rewrite rules.

Introduce `k _ hk`. Rewrite using `[if_neg (fun e => hk (skinj e).symm), zero_mul]`. Simplify using the standard rewrite rules. Establish `hSoff : ∀ (u : Fin n₁ → Fv F v) i, (∀ j, i ≠ sk j) → (S *ᵥ u) i = 0` using `fun u i hi => by`. Simplify using `only [S, Matrix.mulVec, dotProduct]`.

Conclude with `Finset.sum_eq_zero fun j _ => by rw [if_neg (hi j), zero_mul]`. Establish `hSint : ∀ u : Fin n₁ → Fv F v, (∀ i, (S *ᵥ u) i ∈ v.1.adicCompletionIntegers F) ↔ ∀ j, u j ∈ v.1.adicCompletionIntegers F` using `fun u => by`. Use `⟨fun h j => hSsk u j ▸ h (sk j), fun h i => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hi : ∃ j, i = sk j`. Take `⟨j, rfl⟩` from `hi`.

Rewrite using `[hSsk]`. Conclude with `h j`. Use `push_neg at hi`. Rewrite using `[hSoff u i hi]`. Conclude with `zero_mem _`.

Establish `hcol : (W.bas v).1 * S = H.ι.map τ * (W₁.bas v).1`. Use `Matrix.ext fun r j => ?_` and prove the remaining obligations. Rewrite using `[← (hH.bas v (sk j)).2.2 j rfl r, Matrix.mul_apply, Finset.sum_eq_single (sk j)]`. Simplify using `[S]`. Introduce `i _ hi`.

Simplify using `[S, hi]`. Simplify using the standard rewrite rules. Establish `hinj : Function.Injective (Matrix.toLin' H.ι)`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `u hu`.

Rewrite `hu` using `[Matrix.toLin'_apply]`. Establish `hu' : H.ι.map τ *ᵥ (fun i => τ (u i)) = 0`. Use function extensionality and compare the values at `i`. Use `RingHom.map_mulVec (τ : E →+* Fv F v) H.ι u i` as an intermediate fact. Rewrite `this` using `[hu, Pi.zero_apply, map_zero]`.

Conclude with `this.symm`. Use `set w := ((W₁.bas v)⁻¹).1 *ᵥ (fun i => τ (u i)) with hw`. Establish `h1 : (W.bas v).1 *ᵥ (S *ᵥ w) = 0`. Rewrite using `[Matrix.mulVec_mulVec, hcol, hw, Matrix.mulVec_mulVec, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, hu']`. Establish `h2 : S *ᵥ w = 0`.

Use `congrArg (((W.bas v)⁻¹).1 *ᵥ ·) h1` as an intermediate fact. Simplify `this` using `[Matrix.mulVec_mulVec]`. Establish `h3 : w = 0` using `funext fun j => by rw [← hSsk w j, h2]; rfl`. Establish `h4 : (fun i => τ (u i)) = 0`. Use `congrArg ((W₁.bas v).1 *ᵥ ·) h3` as an intermediate fact.

Simplify using `only [hw, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec, Matrix.mulVec_zero] at this`. Conclude with `this`. Use function extensionality and compare the values at `i`. Conclude with `τ.toRingHom.injective (by simpa using congrFun h4 i)`. Take `⟨g, hg⟩` from `LinearMap.exists_leftInverse_of_injective (Matrix.toLin' H.ι) (LinearMap.ker_eq_bot.2 hinj)`.

Set `dl : (Fin n → E) → (Fin n → E) →ₗ[E] E` to `fun c => { toFun := fun z => z ⬝ᵥ c map_add' := fun a b => add_dotProduct a b c map_smul' := fun a b => by simp [smul_dotProduct] }`. Set `cy : Fin n → E` to `W.J *ᵥ fun i => σ (H.y i)`. Set `cx : Fin n → E` to `W.J *ᵥ fun i => σ (H.x i)`. Set `Q : (Fin n → E) →ₗ[E] (Fin n → E)` to `LinearMap.id - (dl cy).smulRight H.x + (dl cx).smulRight H.y`. Establish `hQ : ∀ z, Q z = z - form σ W.J z H.y • H.x + form σ W.J z H.x • H.y` using `fun z => rfl`.

Set `f` to `g ∘ₗ Q`. Establish `hf1 : ∀ u, f (H.ι *ᵥ u) = u` using `fun u => by`. Simplify using `only [f, LinearMap.comp_apply, hQ, (hH.orth u).1, (hH.orth u).2, zero_smul, sub_zero, add_zero]`. Use `congrArg (fun φ => φ u) hg` as an intermediate fact. Simplify `this` using `[Matrix.toLin'_apply]`.

Establish `hyx : form σ W.J H.y H.x = -1` using `by rw [form_swap hcm hW.skew, hH.xy, map_one]`. Establish `hf2 : ∀ z ∈ W.L, f z ∈ W₁.L` using `fun z hz => by`. Take `⟨a, b, u, -, -, hu, rfl⟩` from `hH.split z hz`. Establish `fl : ∀ p q c : Fin n → E, form σ W.J (p + q) c = form σ W.J p c + form σ W.J q c` using `fun p q c => add_dotProduct _ _ _`. Establish `fs : ∀ (t : E) (p c : Fin n → E), form σ W.J (t • p) c = t * form σ W.J p c` using `fun t p c => smul_dotProduct _ _ _`.

Establish `e : Q (a • H.x + H.ι *ᵥ u + b • H.y) = H.ι *ᵥ u`. Rewrite using `[hQ, fl, fl, fl, fl, fs, fs, fs, fs, hH.xx, hH.xy, hH.yy, hyx, (hH.orth u).1, (hH.orth u).2]`. Simplify using `only [mul_zero, mul_one, mul_neg, zero_add, add_zero]`. Use `module`. Simplify using `only [f, LinearMap.comp_apply, e]`.

Use `congrArg (fun φ => φ u) hg` as an intermediate fact. Simplify using `only [LinearMap.comp_apply, Matrix.toLin'_apply, LinearMap.id_apply] at this`. Rewrite using `[this]`. Conclude with `hu`. Set `P : Matrix (Fin n₁) (Fin n) E` to `LinearMap.toMatrix' f`.

Establish `hP : ∀ z, P *ᵥ z = f z` using `fun z => LinearMap.toMatrix'_mulVec f z`. Establish `hPι : P * H.ι = 1` using `Matrix.toLin'.injective (LinearMap.ext fun u => by`. Rewrite using `[Matrix.toLin'_apply, Matrix.toLin'_one, LinearMap.id_apply, ← Matrix.mulVec_mulVec, hP, hf1])`. Establish `hK : ∀ z, z ∈ splitLat τ W₁.L ↔ H.ι.map τ *ᵥ z ∈ splitLat τ W.L` using `fun z => by`. Use `⟨fun hz => mulVec_mem_splitLat τ H.ι (fun x hx => (hH.low x).1 hx) hz, fun hz => ?_⟩` and prove the remaining obligations.

Use `mulVec_mem_splitLat τ P (fun x hx => (hP x).symm ▸ hf2 x hx) hz` as an intermediate fact. Establish `e : P.map τ * H.ι.map τ = 1`. Rewrite using `[show P.map τ * H.ι.map τ = (P * H.ι).map (τ : E →+* Fv F v) from (Matrix.map_mul).symm, hPι]`. Conclude with `Matrix.map_one _ (map_zero _) (map_one _)`. Rewrite `this` using `[Matrix.mulVec_mulVec, e, Matrix.one_mulVec]`. Then use the resulting hypothesis.

Introduce `u`. Rewrite using `[hK, Matrix.mulVec_mulVec, ← hcol, ← Matrix.mulVec_mulVec, ← hW.bas v (S *ᵥ u), hSint]`.
-/
theorem isSplitBasis_of_isAdapted : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (n n₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁) (i₀ i₁ r s : ℕ),
    W.IsSkew σ B r s → H.IsAdapted σ B W W₁ i₀ i₁ → ∀ v : B.P, GlobalTheory.AdelicU.IsSplitBasis (B.τ v) W₁.L (W₁.bas v) := by
  intro F E _ _ _ _ _ σ B hB n n₁ W W₁ H i₀ i₁ r s hW hH v
  set τ := B.τ v
  have hcm := hB.cm

  have hsk : ∀ j : Fin n₁, skip i₀ i₁ j < n := fun j => by
    have := skip_le i₀ i₁ j; have := hH.rank; omega
  let sk : Fin n₁ → Fin n := fun j => ⟨skip i₀ i₁ j, hsk j⟩
  have skinj : Function.Injective sk := by
    intro j k e
    have e' : skip i₀ i₁ j = skip i₀ i₁ k := congrArg Fin.val e
    rcases lt_trichotomy j.1 k.1 with h | h | h
    · exact absurd e' (skip_lt h).ne
    · exact Fin.ext h
    · exact absurd e' (skip_lt h).ne'
  let S : Matrix (Fin n) (Fin n₁) (Fv F v) := fun i j => if i = sk j then 1 else 0
  have hSsk : ∀ (u : Fin n₁ → Fv F v) j, (S *ᵥ u) (sk j) = u j := fun u j => by
    simp only [S, Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hk; rw [if_neg (fun e => hk (skinj e).symm), zero_mul]
    · simp
  have hSoff : ∀ (u : Fin n₁ → Fv F v) i, (∀ j, i ≠ sk j) → (S *ᵥ u) i = 0 := fun u i hi => by
    simp only [S, Matrix.mulVec, dotProduct]
    exact Finset.sum_eq_zero fun j _ => by rw [if_neg (hi j), zero_mul]
  have hSint : ∀ u : Fin n₁ → Fv F v, (∀ i, (S *ᵥ u) i ∈ v.1.adicCompletionIntegers F) ↔
      ∀ j, u j ∈ v.1.adicCompletionIntegers F := fun u => by
    refine ⟨fun h j => hSsk u j ▸ h (sk j), fun h i => ?_⟩
    by_cases hi : ∃ j, i = sk j
    · obtain ⟨j, rfl⟩ := hi; rw [hSsk]; exact h j
    · push_neg at hi; rw [hSoff u i hi]; exact zero_mem _
  have hcol : (W.bas v).1 * S = H.ι.map τ * (W₁.bas v).1 := by
    refine Matrix.ext fun r j => ?_
    rw [← (hH.bas v (sk j)).2.2 j rfl r, Matrix.mul_apply, Finset.sum_eq_single (sk j)]
    · simp [S]
    · intro i _ hi; simp [S, hi]
    · simp

  have hinj : Function.Injective (Matrix.toLin' H.ι) := by
    rw [injective_iff_map_eq_zero]
    intro u hu
    rw [Matrix.toLin'_apply] at hu
    have hu' : H.ι.map τ *ᵥ (fun i => τ (u i)) = 0 := by
      funext i
      have := RingHom.map_mulVec (τ : E →+* Fv F v) H.ι u i
      rw [hu, Pi.zero_apply, map_zero] at this
      exact this.symm
    set w := ((W₁.bas v)⁻¹).1 *ᵥ (fun i => τ (u i)) with hw
    have h1 : (W.bas v).1 *ᵥ (S *ᵥ w) = 0 := by
      rw [Matrix.mulVec_mulVec, hcol, hw, Matrix.mulVec_mulVec, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, hu']
    have h2 : S *ᵥ w = 0 := by
      have := congrArg (((W.bas v)⁻¹).1 *ᵥ ·) h1
      simpa [Matrix.mulVec_mulVec] using this
    have h3 : w = 0 := funext fun j => by rw [← hSsk w j, h2]; rfl
    have h4 : (fun i => τ (u i)) = 0 := by
      have := congrArg ((W₁.bas v).1 *ᵥ ·) h3
      simp only [hw, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec, Matrix.mulVec_zero] at this
      exact this
    funext i
    exact τ.toRingHom.injective (by simpa using congrFun h4 i)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' H.ι) (LinearMap.ker_eq_bot.2 hinj)

  let dl : (Fin n → E) → (Fin n → E) →ₗ[E] E := fun c =>
    { toFun := fun z => z ⬝ᵥ c
      map_add' := fun a b => add_dotProduct a b c
      map_smul' := fun a b => by simp [smul_dotProduct] }
  let cy : Fin n → E := W.J *ᵥ fun i => σ (H.y i)
  let cx : Fin n → E := W.J *ᵥ fun i => σ (H.x i)
  let Q : (Fin n → E) →ₗ[E] (Fin n → E) := LinearMap.id - (dl cy).smulRight H.x + (dl cx).smulRight H.y
  have hQ : ∀ z, Q z = z - form σ W.J z H.y • H.x + form σ W.J z H.x • H.y := fun z => rfl
  let f := g ∘ₗ Q
  have hf1 : ∀ u, f (H.ι *ᵥ u) = u := fun u => by
    simp only [f, LinearMap.comp_apply, hQ, (hH.orth u).1, (hH.orth u).2, zero_smul, sub_zero, add_zero]
    have := congrArg (fun φ => φ u) hg
    simpa [Matrix.toLin'_apply] using this
  have hyx : form σ W.J H.y H.x = -1 := by rw [form_swap hcm hW.skew, hH.xy, map_one]
  have hf2 : ∀ z ∈ W.L, f z ∈ W₁.L := fun z hz => by
    obtain ⟨a, b, u, -, -, hu, rfl⟩ := hH.split z hz
    have fl : ∀ p q c : Fin n → E, form σ W.J (p + q) c = form σ W.J p c + form σ W.J q c :=
      fun p q c => add_dotProduct _ _ _
    have fs : ∀ (t : E) (p c : Fin n → E), form σ W.J (t • p) c = t * form σ W.J p c :=
      fun t p c => smul_dotProduct _ _ _
    have e : Q (a • H.x + H.ι *ᵥ u + b • H.y) = H.ι *ᵥ u := by
      rw [hQ, fl, fl, fl, fl, fs, fs, fs, fs, hH.xx, hH.xy, hH.yy, hyx, (hH.orth u).1, (hH.orth u).2]
      simp only [mul_zero, mul_one, mul_neg, zero_add, add_zero]
      module
    simp only [f, LinearMap.comp_apply, e]
    have := congrArg (fun φ => φ u) hg
    simp only [LinearMap.comp_apply, Matrix.toLin'_apply, LinearMap.id_apply] at this
    rw [this]; exact hu
  let P : Matrix (Fin n₁) (Fin n) E := LinearMap.toMatrix' f
  have hP : ∀ z, P *ᵥ z = f z := fun z => LinearMap.toMatrix'_mulVec f z
  have hPι : P * H.ι = 1 := Matrix.toLin'.injective (LinearMap.ext fun u => by
    rw [Matrix.toLin'_apply, Matrix.toLin'_one, LinearMap.id_apply, ← Matrix.mulVec_mulVec, hP, hf1])

  have hK : ∀ z, z ∈ splitLat τ W₁.L ↔ H.ι.map τ *ᵥ z ∈ splitLat τ W.L := fun z => by
    refine ⟨fun hz => mulVec_mem_splitLat τ H.ι (fun x hx => (hH.low x).1 hx) hz, fun hz => ?_⟩
    have := mulVec_mem_splitLat τ P (fun x hx => (hP x).symm ▸ hf2 x hx) hz
    have e : P.map τ * H.ι.map τ = 1 := by
      rw [show P.map τ * H.ι.map τ = (P * H.ι).map (τ : E →+* Fv F v) from (Matrix.map_mul).symm, hPι]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    rwa [Matrix.mulVec_mulVec, e, Matrix.one_mulVec] at this
  intro u
  rw [hK, Matrix.mulVec_mulVec, ← hcol, ← Matrix.mulVec_mulVec, ← hW.bas v (S *ᵥ u), hSint]

end GlobalTheory.AdaptedPlaneBasis
