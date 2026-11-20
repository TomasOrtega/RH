import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsSelfDualFor

noncomputable section

open ValuativeRel Matrix MeasureTheory
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker

namespace GlobalTheory.LocLanglands.GammaModel

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Set `ν : Measure k` to `Measure.addHaar`. Establish `fin : ∀ d : kˣ, ν {x | valuation k x ≤ valuation k (d : k)} ≠ ⊤` using `fun d => (IsNonarchimedeanLocalField.isCompact_closedBall k _).measure_lt_top.ne`. Establish `pos : ∀ d : kˣ, ν {x | valuation k x ≤ valuation k (d : k)} ≠ 0` using `fun d => by`. Establish `ho : IsOpen {x : k | valuation k x ≤ valuation k (d : k)}`. Establish `h1 : IsOpen (𝒪[k] : Set k)` using `Valuation.isOpen_integer`.

Establish `h2 : {x : k | valuation k x ≤ valuation k (d : k)} = (fun x => ((d⁻¹ : kˣ) : k) * x) ⁻¹' (𝒪[k] : Set k)`. Use extensionality with `y`. Use `show _ ↔ valuation k (((d⁻¹ : kˣ) : k) * y) ≤ 1`. Establish `: 0 < valuation k (d : k)` using `by simp [zero_lt_iff]`. Simplify using `[inv_mul_le_iff₀ this]`.

Rewrite using `[h2]; exact h1.preimage (by fun_prop)`. Conclude with `(ho.measure_pos ν ⟨0, by simp⟩).ne'`. Establish `f1` using `fin 1`. Establish `p1` using `pos 1`. Simplify using `only [Units.val_one, map_one] at f1 p1`.

Use `set a := ν {x | valuation k x ≤ 1}`. Use `set b := ν {x | valuation k x ≤ valuation k (c : k)}`. Establish `hab0 : a * b ≠ 0` using `mul_ne_zero p1 (pos c)`. Establish `habt : a * b ≠ ⊤` using `ENNReal.mul_ne_top f1 (fin c)`. Set `t : ENNReal` to `(a * b) ^ (-(1 / 2) : ℝ)`.

Establish `ht0 : t ≠ 0` using `by simp [t, ENNReal.rpow_eq_zero_iff, habt, hab0]`. Establish `htt : t ≠ ⊤` using `by simp [t, ENNReal.rpow_eq_top_iff, habt, hab0]`. Use `⟨t • ν, Measure.IsAddHaarMeasure.smul ν ht0 htt, c, hψ, ?_⟩` and prove the remaining obligations. Simplify using `only [Measure.smul_apply, smul_eq_mul]`. Express the relevant statement in the definitionally equal form `t * a * (t * b) = 1`.

Establish `: t * t = (a * b)⁻¹`. Simplify using `only [t]`. Rewrite using `[← ENNReal.rpow_add _ _ hab0 habt, ← ENNReal.rpow_neg_one]`. Evaluate the numerical expressions. Rewrite using `[mul_mul_mul_comm, this, ENNReal.inv_mul_cancel hab0 habt]`.
-/
theorem exists_isSelfDualFor [MeasurableSpace k] [BorelSpace k] {ψ : AddChar k Circle} {c : kˣ}
    (hψ : HasConductor ψ c) : ∃ μ : Measure k, IsSelfDualFor ψ μ := by
  let ν : Measure k := Measure.addHaar
  have fin : ∀ d : kˣ, ν {x | valuation k x ≤ valuation k (d : k)} ≠ ⊤ := fun d =>
    (IsNonarchimedeanLocalField.isCompact_closedBall k _).measure_lt_top.ne
  have pos : ∀ d : kˣ, ν {x | valuation k x ≤ valuation k (d : k)} ≠ 0 := fun d => by
    have ho : IsOpen {x : k | valuation k x ≤ valuation k (d : k)} := by
      have h1 : IsOpen (𝒪[k] : Set k) := Valuation.isOpen_integer
      have h2 : {x : k | valuation k x ≤ valuation k (d : k)} = (fun x => ((d⁻¹ : kˣ) : k) * x) ⁻¹' (𝒪[k] : Set k) := by
        ext y
        show _ ↔ valuation k (((d⁻¹ : kˣ) : k) * y) ≤ 1
        have : 0 < valuation k (d : k) := by simp [zero_lt_iff]
        simp [inv_mul_le_iff₀ this]
      rw [h2]; exact h1.preimage (by fun_prop)
    exact (ho.measure_pos ν ⟨0, by simp⟩).ne'
  have f1 := fin 1
  have p1 := pos 1
  simp only [Units.val_one, map_one] at f1 p1
  set a := ν {x | valuation k x ≤ 1}
  set b := ν {x | valuation k x ≤ valuation k (c : k)}
  have hab0 : a * b ≠ 0 := mul_ne_zero p1 (pos c)
  have habt : a * b ≠ ⊤ := ENNReal.mul_ne_top f1 (fin c)
  let t : ENNReal := (a * b) ^ (-(1 / 2) : ℝ)
  have ht0 : t ≠ 0 := by simp [t, ENNReal.rpow_eq_zero_iff, habt, hab0]
  have htt : t ≠ ⊤ := by simp [t, ENNReal.rpow_eq_top_iff, habt, hab0]
  refine ⟨t • ν, Measure.IsAddHaarMeasure.smul ν ht0 htt, c, hψ, ?_⟩
  simp only [Measure.smul_apply, smul_eq_mul]
  change t * a * (t * b) = 1
  have : t * t = (a * b)⁻¹ := by
    simp only [t]
    rw [← ENNReal.rpow_add _ _ hab0 habt, ← ENNReal.rpow_neg_one]; norm_num
  rw [mul_mul_mul_comm, this, ENNReal.inv_mul_cancel hab0 habt]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

/- English proof (translation)
Establish `e0 : (stdSum (rfl : 1 + (1 + 1) = 3)).symm 0 = Sum.inl 0` using `by decide`. Establish `e1 : (stdSum (rfl : 1 + (1 + 1) = 3)).symm 1 = Sum.inr 0` using `by decide`. Establish `e2 : (stdSum (rfl : 1 + (1 + 1) = 3)).symm 2 = Sum.inr 1` using `by decide`. Establish `p0 : padRow x 0 0 = x 0 0` using `rfl`. Establish `p1 : padRow x 1 0 = 0` using `rfl`.

Rewrite using `[Units.val_mul, Units.val_mul, val_emb₂, val_emb₂]`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;>`. Simplify using `[Matrix.mul_apply, Fin.sum_univ_three, lowUnip, longElt, e0, e1, e2, p0, p1, Fin.ext_iff]`.
-/
theorem arg_three_one (g : GL (Fin 1) k) (x : Fin 1 → Fin 1 → k) :
    (emb₂ k (stdSum (rfl : 1 + (1 + 1) = 3)) (g, 1) * lowUnip rfl (padRow x) *
        emb₂ k (stdSum (rfl : 1 + (1 + 1) = 3)) (1, longElt (1 + 1) k)).val =
      !![g.val 0 0, 0, 0; x 0 0, 0, 1; 0, 1, 0] := by
  have e0 : (stdSum (rfl : 1 + (1 + 1) = 3)).symm 0 = Sum.inl 0 := by decide
  have e1 : (stdSum (rfl : 1 + (1 + 1) = 3)).symm 1 = Sum.inr 0 := by decide
  have e2 : (stdSum (rfl : 1 + (1 + 1) = 3)).symm 2 = Sum.inr 1 := by decide
  have p0 : padRow x 0 0 = x 0 0 := rfl
  have p1 : padRow x 1 0 = 0 := rfl
  rw [Units.val_mul, Units.val_mul, val_emb₂, val_emb₂]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, lowUnip, longElt, e0, e1, e2, p0, p1, Fin.ext_iff]

variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

/- English proof (translation)
Use `ext1`. Simplify using `[lowUnip]`.
-/
theorem lowUnip_zero {m r n : ℕ} (hn : m + r = n) : lowUnip hn (0 : Matrix (Fin r) (Fin m) k) = 1 := by
  ext1
  simp [lowUnip]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

/- English proof (translation)
Use extensionality with `i j`. Use `fin_cases i`. Use `fin_cases j`. Simplify using `[longElt]`.
-/
theorem longElt_one : longElt (0 + 1) k = 1 := by
  ext i j
  fin_cases i; fin_cases j
  simp [longElt]

/- English proof (translation)
Establish `key : ∀ [MeasurableSpace k] (μ : Measure k) (l : Module.Dual ℂ V) (v : V) (g : GL (Fin m) k), (∫ x : Fin 0 → Fin m → k, l (π (tilde (emb₂ k (stdSum (rfl : m + (0 + 1) = m + 1)) (g, 1) * lowUnip rfl (padRow x) * emb₂ k (stdSum (rfl : m + (0 + 1) = m + 1)) (1, longElt (0 + 1) k))) …`. Introduce `_ μ l v g`. Establish `h0 : ∀ x : Fin 0 → Fin m → k, padRow x = 0` using `fun x => by`. Use extensionality with `i j`. Use `fin_cases i`.

Simplify using `[padRow, Fin.snoc]`. Simplify using `only [h0, lowUnip_zero, longElt_one, mul_one]`. Rewrite using `[show ((1, 1) : GL (Fin m) k × GL (Fin (0 + 1)) k) = 1 from rfl, map_one, mul_one, Measure.pi_of_empty]`. Simplify using `[corner]`. Prove the components needed by the constructor for the conclusion.

Introduce `H ω hω l l' hl hl' I hI v v' borelize k`. Take `⟨μ, hμ⟩` from `exists_isSelfDualFor hψ`. Use `H 0 rfl μ hμ ω hω l l' hl hl' I hI v v'` as an intermediate fact. Simplify using `only [key] at this`. Simplify `this` using `[corner]`.

Introduce `H j hn _ _ μ hμ ω hω l l' hl hl' I hI v v'`. Take `rfl : j = 0` from `by omega`. Use `H ω hω l l' hl hl' I hI v v'` as an intermediate fact. Simplify using `only [key]`. Simplify `this` using `[corner]`.
-/
theorem hasPairGamma_succ_iff {m : ℕ} {ψ : AddChar k Circle} {c : kˣ} (hψ : HasConductor ψ c)
    (π : Representation ℂ (GL (Fin (m + 1)) k) V) (τ : Representation ℂ (GL (Fin m) k) V') (e : ℂ) :
    HasPairGamma ψ π τ e ↔ HasPairEps ψ π τ e := by
  have key : ∀ [MeasurableSpace k] (μ : Measure k) (l : Module.Dual ℂ V) (v : V) (g : GL (Fin m) k),
      (∫ x : Fin 0 → Fin m → k, l (π (tilde (emb₂ k (stdSum (rfl : m + (0 + 1) = m + 1)) (g, 1) *
        lowUnip rfl (padRow x) * emb₂ k (stdSum (rfl : m + (0 + 1) = m + 1)) (1, longElt (0 + 1) k))) v)
          ∂(Measure.pi fun _ => Measure.pi fun _ => μ)) = l (π (tilde (corner g)) v) := by
    intro _ μ l v g
    have h0 : ∀ x : Fin 0 → Fin m → k, padRow x = 0 := fun x => by
      ext i j; fin_cases i; simp [padRow, Fin.snoc]
    simp only [h0, lowUnip_zero, longElt_one, mul_one]
    rw [show ((1, 1) : GL (Fin m) k × GL (Fin (0 + 1)) k) = 1 from rfl, map_one, mul_one, Measure.pi_of_empty]
    simp [corner]
  constructor
  · intro H ω hω l l' hl hl' I hI v v'
    borelize k
    obtain ⟨μ, hμ⟩ := exists_isSelfDualFor hψ
    have := H 0 rfl μ hμ ω hω l l' hl hl' I hI v v'
    simp only [key] at this
    simpa [corner] using this
  · intro H j hn _ _ μ hμ ω hω l l' hl hl' I hI v v'
    obtain rfl : j = 0 := by omega
    have := H ω hω l l' hl hl' I hI v v'
    simp only [key]
    simpa [corner] using this

/- English proof (translation)
Establish `h0 : ∀ g : GL (Fin 0) k, g = 1` using `fun g => Units.ext (Subsingleton.elim _ _)`. Establish `key : ∀ [MeasurableSpace k] (μ : Measure k) (l : Module.Dual ℂ V) (v : V) (g : GL (Fin 0) k), (∫ x : Fin j → Fin 0 → k, l (π (tilde (emb₂ k (stdSum (rfl : 0 + (j + 1) = 0 + (j + 1))) (g, 1) * lowUnip rfl (padRow x) * emb₂ k (stdSum (rfl : 0 + (j + 1) = 0 + (j + 1))) (1, longElt ( …`. Introduce `_ μ l v g`. Establish `h1 : ∀ x : Fin j → Fin 0 → k, padRow x = 0` using `fun x => Subsingleton.elim _ _`. Establish `h2 : emb₂ k (stdSum (rfl : 0 + (j + 1) = 0 + (j + 1))) (1, longElt (j + 1) k) = longElt (0 + (j + 1)) k`.

Use extensionality with `a b`. Take `⟨a, rfl⟩` from `(stdSum (rfl : 0 + (j + 1) = 0 + (j + 1))).surjective a`. Take `⟨b, rfl⟩` from `(stdSum (rfl : 0 + (j + 1) = 0 + (j + 1))).surjective b`. Rewrite using `[val_emb₂]`. Break down `a with a | a` into its components or cases.

Conclude with `a.elim0`. Break down `b with b | b` into its components or cases. Conclude with `b.elim0`. Simplify using `[longElt, Fin.ext_iff]`. Establish `h3 : tilde (longElt (0 + (j + 1)) k) = 1` using `by ext1`.

Establish `: (longElt (0 + (j + 1)) k).val.transpose = (longElt (0 + (j + 1)) k).val`. Use extensionality with `a b`. Simplify using `only [longElt, transpose_apply, of_apply]`. Use `congr 1`. Conclude with `propext ⟨fun h => by simp [h], fun h => by simp [h]⟩`.

Express the relevant statement in the definitionally equal form `(longElt (0 + (j + 1)) k).val * (longElt (0 + (j + 1)) k).val.transpose = 1`. Rewrite using `[this]`. Conclude with `antidiag_mul_self _ _`. Simplify using `only [h1, lowUnip_zero, mul_one, h0 g, h2]`. Rewrite using `[show ((1, 1) : GL (Fin 0) k × GL (Fin (j + 1)) k) = 1 from rfl, map_one, one_mul, h3]`.

Establish `hd : (Measure.pi fun _ : Fin 0 => μ) = Measure.dirac fun a => isEmptyElim a` using `Measure.pi_of_empty _ _`. Rewrite using `[hd]`. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Introduce `H borelize k`.

Take `⟨μ, hμ⟩` from `exists_isSelfDualFor hψ`. Take `⟨l, hl0, hl⟩` from `hπ`. Choose the witnesses or unpack the hypotheses as in `⟨v, hv⟩ : ∃ v, l v ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`.

Conclude with `hl0 (LinearMap.ext h)`. Use `H j rfl μ hμ 1 (fun z v => by simp [detRep]) l LinearMap.id hl (fun u hu v => by simp [detRep, superDiag]) _ isInvIntegral_zero v 1` as an intermediate fact. Simplify using `only [key] at this`. Rewrite `this` using `[LinearMap.proj_apply, LinearMap.proj_apply, show ((1, 1) : GL (Fin 0) k × GL (Fin (j + 1)) k) = 1 from rfl, map_one (emb₂ k _)]`. Simplify using `[detRep] at this`.

Conclude with `(mul_eq_right₀ hv).1 this.symm`. Introduce and unpack `rfl j' hn _ _ μ hμ ω hω l l' hl hl' I hI v v'`. Take `rfl : j = j'` from `by omega`. Establish `hω1 : ω (-1) = 1`. Use `hω (-1) 1` as an intermediate fact.

Simplify using `[detRep] at this`. Conclude with `Units.ext (by simpa using this.symm)`. Simplify using `only [key, hω1]`. Simplify using `only [Units.val_one, one_pow, one_mul]`. Use `congr 1`.

Use function extensionality and compare the values at `g`. Rewrite using `[h0 (tilde g), h0 g, show ((1, 1) : GL (Fin 0) k × GL (Fin (j + 1)) k) = 1 from rfl, map_one]`. Simplify using the standard rewrite rules.
-/
theorem hasPairGamma_zero_iff {j : ℕ} {ψ : AddChar k Circle} {c : kˣ} (hψ : HasConductor ψ c)
    (π : Representation ℂ (GL (Fin (0 + (j + 1))) k) V) (hπ : IsGeneric ψ π) (e : ℂ) :
    HasPairGamma ψ π (detRep (Fin 0) 1) e ↔ e = 1 := by
  have h0 : ∀ g : GL (Fin 0) k, g = 1 := fun g => Units.ext (Subsingleton.elim _ _)
  have key : ∀ [MeasurableSpace k] (μ : Measure k) (l : Module.Dual ℂ V) (v : V) (g : GL (Fin 0) k),
      (∫ x : Fin j → Fin 0 → k, l (π (tilde (emb₂ k (stdSum (rfl : 0 + (j + 1) = 0 + (j + 1))) (g, 1) *
        lowUnip rfl (padRow x) * emb₂ k (stdSum (rfl : 0 + (j + 1) = 0 + (j + 1))) (1, longElt (j + 1) k))) v)
          ∂(Measure.pi fun _ => Measure.pi fun _ => μ)) = l v := by
    intro _ μ l v g
    have h1 : ∀ x : Fin j → Fin 0 → k, padRow x = 0 := fun x => Subsingleton.elim _ _
    have h2 : emb₂ k (stdSum (rfl : 0 + (j + 1) = 0 + (j + 1))) (1, longElt (j + 1) k) = longElt (0 + (j + 1)) k := by
      ext a b
      obtain ⟨a, rfl⟩ := (stdSum (rfl : 0 + (j + 1) = 0 + (j + 1))).surjective a
      obtain ⟨b, rfl⟩ := (stdSum (rfl : 0 + (j + 1) = 0 + (j + 1))).surjective b
      rw [val_emb₂]
      rcases a with a | a
      · exact a.elim0
      rcases b with b | b
      · exact b.elim0
      simp [longElt, Fin.ext_iff]
    have h3 : tilde (longElt (0 + (j + 1)) k) = 1 := by
      ext1
      have : (longElt (0 + (j + 1)) k).val.transpose = (longElt (0 + (j + 1)) k).val := by
        ext a b
        simp only [longElt, transpose_apply, of_apply]
        congr 1
        exact propext ⟨fun h => by simp [h], fun h => by simp [h]⟩
      change (longElt (0 + (j + 1)) k).val * (longElt (0 + (j + 1)) k).val.transpose = 1
      rw [this]; exact antidiag_mul_self _ _
    simp only [h1, lowUnip_zero, mul_one, h0 g, h2]
    rw [show ((1, 1) : GL (Fin 0) k × GL (Fin (j + 1)) k) = 1 from rfl, map_one, one_mul, h3]
    have hd : (Measure.pi fun _ : Fin 0 => μ) = Measure.dirac fun a => isEmptyElim a := Measure.pi_of_empty _ _
    rw [hd]
    simp
  constructor
  · intro H
    borelize k
    obtain ⟨μ, hμ⟩ := exists_isSelfDualFor hψ
    obtain ⟨l, hl0, hl⟩ := hπ
    obtain ⟨v, hv⟩ : ∃ v, l v ≠ 0 := by
      by_contra h; push Not at h; exact hl0 (LinearMap.ext h)
    have := H j rfl μ hμ 1 (fun z v => by simp [detRep]) l LinearMap.id hl
      (fun u hu v => by simp [detRep, superDiag]) _ isInvIntegral_zero v 1
    simp only [key] at this
    rw [LinearMap.proj_apply, LinearMap.proj_apply,
      show ((1, 1) : GL (Fin 0) k × GL (Fin (j + 1)) k) = 1 from rfl, map_one (emb₂ k _)] at this
    simp [detRep] at this
    exact (mul_eq_right₀ hv).1 this.symm
  · rintro rfl j' hn _ _ μ hμ ω hω l l' hl hl' I hI v v'
    obtain rfl : j = j' := by omega
    have hω1 : ω (-1) = 1 := by
      have := hω (-1) 1
      simp [detRep] at this
      exact Units.ext (by simpa using this.symm)
    simp only [key, hω1]
    simp only [Units.val_one, one_pow, one_mul]
    congr 1
    funext g
    rw [h0 (tilde g), h0 g, show ((1, 1) : GL (Fin 0) k × GL (Fin (j + 1)) k) = 1 from rfl, map_one]
    simp

end GlobalTheory.LocLanglands.GammaModel

end
