import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsDiagDiv
import GroundTheory.HeightsAndTheta.Heights.Intersections.PRFormula
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

namespace DiagonalForms

section Local

variable {Ω : Type*} [Field Ω]

/- English proof (translation)
Take `⟨n, hn⟩` from `hy`. Take `⟨m, hm⟩` from `hz`. Use `⟨n + m, ?_⟩` and prove the remaining obligations. Establish `: g ^ (n + m) * (y + z) = g ^ m * (g ^ n * y) + g ^ n * (g ^ m * z)` using `by ring`. Rewrite using `[this]`.

Conclude with `add_mem (mul_mem (pow_mem hg _) hn) (mul_mem (pow_mem hg _) hm)`.
-/
theorem loc_add {R : Subalgebra ℤ Ω} {g y z : Ω} (hg : g ∈ R) (hy : ∃ n : ℕ, g ^ n * y ∈ R)
    (hz : ∃ n : ℕ, g ^ n * z ∈ R) : ∃ n : ℕ, g ^ n * (y + z) ∈ R := by
  obtain ⟨n, hn⟩ := hy
  obtain ⟨m, hm⟩ := hz
  refine ⟨n + m, ?_⟩
  have : g ^ (n + m) * (y + z) = g ^ m * (g ^ n * y) + g ^ n * (g ^ m * z) := by ring
  rw [this]
  exact add_mem (mul_mem (pow_mem hg _) hn) (mul_mem (pow_mem hg _) hm)

/- English proof (translation)
Take `⟨n, hn⟩` from `hy`. Take `⟨m, hm⟩` from `hz`. Use `⟨n + m, ?_⟩` and prove the remaining obligations. Establish `: g ^ (n + m) * (y * z) = (g ^ n * y) * (g ^ m * z)` using `by ring`. Rewrite using `[this]`.

Conclude with `mul_mem hn hm`.
-/
theorem loc_mul {R : Subalgebra ℤ Ω} {g y z : Ω} (hy : ∃ n : ℕ, g ^ n * y ∈ R)
    (hz : ∃ n : ℕ, g ^ n * z ∈ R) : ∃ n : ℕ, g ^ n * (y * z) ∈ R := by
  obtain ⟨n, hn⟩ := hy
  obtain ⟨m, hm⟩ := hz
  refine ⟨n + m, ?_⟩
  have : g ^ (n + m) * (y * z) = (g ^ n * y) * (g ^ m * z) := by ring
  rw [this]
  exact mul_mem hn hm

/- English proof (translation)
Rewrite using `[← Nat.sub_add_cancel hn, pow_add, mul_assoc]`. Conclude with `mul_mem (pow_mem hg _) h`.
-/
theorem pow_mul_mem_of_le {R : Subalgebra ℤ Ω} {g y : Ω} (hg : g ∈ R) {n N : ℕ} (hn : n ≤ N)
    (h : g ^ n * y ∈ R) : g ^ N * y ∈ R := by
  rw [← Nat.sub_add_cancel hn, pow_add, mul_assoc]
  exact mul_mem (pow_mem hg _) h

/- English proof (translation)
Set `I : Ideal R` to `{ carrier := {r | (r : Ω) * y ∈ R} add_mem' := fun {a b} ha hb => by show ((a + b : R) : Ω) * y ∈ R`. Rewrite using `[Subalgebra.coe_add, add_mul]`. Conclude with `add_mem ha hb`. Use the proof step `zero_mem' := by show ((0 : R) : Ω) * y ∈ R`. Simplify using the standard rewrite rules.

Use the proof step `smul_mem' := fun a b hb => by show ((a * b : R) : Ω) * y ∈ R`. Rewrite using `[Subalgebra.coe_mul, mul_assoc]`. Conclude with `mul_mem a.2 hb }`. Establish `hrad : ∀ l, (⟨f l, hf l⟩ : R) ∈ I.radical` using `fun l => by`. Take `⟨n, hn⟩` from `hy l`.

Use `⟨n, ?_⟩` and prove the remaining obligations. Use `show ((⟨f l, hf l⟩ ^ n : R) : Ω) * y ∈ R`. Simplify using `using hn`. Establish `h1 : (1 : R) ∈ I.radical`. Establish `: (1 : R) = ∑ l, (⟨c l, hc l⟩ : R) * ⟨f l, hf l⟩` using `Subtype.ext (by simp [hsum])`.

Rewrite using `[this]`. Conclude with `Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hrad l)`. Establish `hI : I = ⊤` using `Ideal.radical_eq_top.1 ((Ideal.eq_top_iff_one _).2 h1)`. Establish `: (1 : R) ∈ I` using `hI ▸ Submodule.mem_top`. Simplify `this` using `[I]`.
-/
theorem mem_of_forall_pow_mul_mem (R : Subalgebra ℤ Ω) {K : ℕ} (f c : Fin K → Ω) (hf : ∀ l, f l ∈ R)
    (hc : ∀ l, c l ∈ R) (hsum : ∑ l, c l * f l = 1) {y : Ω} (hy : ∀ l, ∃ n : ℕ, f l ^ n * y ∈ R) :
    y ∈ R := by
  let I : Ideal R :=
    { carrier := {r | (r : Ω) * y ∈ R}
      add_mem' := fun {a b} ha hb => by
        show ((a + b : R) : Ω) * y ∈ R
        rw [Subalgebra.coe_add, add_mul]
        exact add_mem ha hb
      zero_mem' := by
        show ((0 : R) : Ω) * y ∈ R
        simp
      smul_mem' := fun a b hb => by
        show ((a * b : R) : Ω) * y ∈ R
        rw [Subalgebra.coe_mul, mul_assoc]
        exact mul_mem a.2 hb }
  have hrad : ∀ l, (⟨f l, hf l⟩ : R) ∈ I.radical := fun l => by
    obtain ⟨n, hn⟩ := hy l
    refine ⟨n, ?_⟩
    show ((⟨f l, hf l⟩ ^ n : R) : Ω) * y ∈ R
    simpa using hn
  have h1 : (1 : R) ∈ I.radical := by
    have : (1 : R) = ∑ l, (⟨c l, hc l⟩ : R) * ⟨f l, hf l⟩ := Subtype.ext (by simp [hsum])
    rw [this]
    exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hrad l)
  have hI : I = ⊤ := Ideal.radical_eq_top.1 ((Ideal.eq_top_iff_one _).2 h1)
  have : (1 : R) ∈ I := hI ▸ Submodule.mem_top
  simpa [I] using this

end Local

section Bundle

variable {Ω : Type*} [Field Ω] {ι : Type*} {E : Type*} [AddCommGroup E] [Module Ω E] {x : ι → Ω}

/- English proof (translation)
Take `⟨K, fs, cs, hf, hc, hsum, hb⟩` from `B.frame i hi`. Use `choose bs hli hsp hiff using hb`. Choose the witnesses or unpack the hypotheses as in `⟨l₀, hl₀⟩ : ∃ l, fs l ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`.

Simplify using `[h] at hsum`. Establish `hgen : ∀ l q, ∃ n : ℕ, fs l ^ n • bs l q ∈ B.lat i`. Introduce `l q`. Use `(hiff l (bs l q)).2 ⟨Pi.single q 1, fun q' => ⟨0, ?_⟩, ?_⟩` and prove the remaining obligations. Break down `eq_or_ne q' q with rfl | h` into its components or cases.

Simplify using the standard rewrite rules. Simplify using `[h]`. Simplify using `[Pi.single_apply]`. Use `choose n hn using hgen`. Set `bB : Module.Basis (Fin 2) Ω E` to `Module.Basis.mk (hli l₀) (hsp l₀).ge`.

Establish `hbB : ⇑bB = bs l₀` using `Module.Basis.coe_mk _ _`. Establish `hcoord : ∀ p : Fin K × Fin 2 × Fin 2, ∃ m : ℕ, fs l₀ ^ m * bB.repr (fs p.1 ^ n p.1 p.2.1 • bs p.1 p.2.1) p.2.2 ∈ chartRing ℤ x i`. Introduce and unpack `⟨l, q, q'⟩`. Take `⟨a, ha, hv⟩` from `(hiff l₀ _).1 ⟨0, by simpa using hn l q⟩`. Establish `: bB.repr (fs l ^ n l q • bs l q) = a`.

Rewrite using `[hv, ← hbB]`. Conclude with `bB.repr_sum_self a`. Rewrite using `[this]`. Conclude with `ha q'`. Use `choose m hm using hcoord`.

Use `⟨fs l₀, bB, Finset.univ.sup m, hf l₀, hl₀, fun q => ⟨n l₀ q, by rw [hbB]; exact hn l₀ q⟩, ?_⟩` and prove the remaining obligations. Introduce `v hv q'`. Use `mem_of_forall_pow_mul_mem _ fs cs hf hc hsum fun l => ?_` and prove the remaining obligations. Take `⟨a, ha, hva⟩` from `(hiff l v).1 ⟨0, by simpa using hv⟩`. Establish `hterm : ∀ q, ∃ t : ℕ, fs l ^ t * (a q * (fs l₀ ^ Finset.univ.sup m * bB.repr (bs l q) q')) ∈ chartRing ℤ x i`.

Introduce `q`. Use `loc_mul (ha q) ⟨n l q, ?_⟩` and prove the remaining obligations. Establish `h1` using `pow_mul_mem_of_le (hf l₀) (Finset.le_sup (f := m) (Finset.mem_univ (l, q, q'))) (hm (l, q, q'))`. Establish `h2 : fs l ^ n l q * (fs l₀ ^ Finset.univ.sup m * bB.repr (bs l q) q') = fs l₀ ^ Finset.univ.sup m * bB.repr (fs l ^ n l q • bs l q) q'`. Rewrite using `[map_smul, Finsupp.smul_apply, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h2]`. Conclude with `h1`. Establish `hsplit : fs l₀ ^ Finset.univ.sup m * bB.repr v q' = a 0 * (fs l₀ ^ Finset.univ.sup m * bB.repr (bs l 0) q') + a 1 * (fs l₀ ^ Finset.univ.sup m * bB.repr (bs l 1) q')`. Rewrite using `[hva, Fin.sum_univ_two, map_add, map_smul, map_smul, Finsupp.add_apply, Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hsplit]`. Conclude with `loc_add (hf l) (hterm 0) (hterm 1)`.
-/
theorem exists_bounded_frame (B : ChartBundle ℤ x 2 E) (i : ι) (hi : x i ≠ 0) :
    ∃ (f : Ω) (b : Module.Basis (Fin 2) Ω E) (N : ℕ), f ∈ chartRing ℤ x i ∧ f ≠ 0 ∧
      (∀ q, ∃ n : ℕ, f ^ n • b q ∈ B.lat i) ∧
      ∀ v ∈ B.lat i, ∀ q, f ^ N * b.repr v q ∈ chartRing ℤ x i := by
  classical
  obtain ⟨K, fs, cs, hf, hc, hsum, hb⟩ := B.frame i hi
  choose bs hli hsp hiff using hb
  obtain ⟨l₀, hl₀⟩ : ∃ l, fs l ≠ 0 := by
    by_contra h
    push Not at h
    simp [h] at hsum
  have hgen : ∀ l q, ∃ n : ℕ, fs l ^ n • bs l q ∈ B.lat i := by
    intro l q
    refine (hiff l (bs l q)).2 ⟨Pi.single q 1, fun q' => ⟨0, ?_⟩, ?_⟩
    · rcases eq_or_ne q' q with rfl | h
      · simp
      · simp [h]
    · simp [Pi.single_apply]
  choose n hn using hgen
  let bB : Module.Basis (Fin 2) Ω E := Module.Basis.mk (hli l₀) (hsp l₀).ge
  have hbB : ⇑bB = bs l₀ := Module.Basis.coe_mk _ _
  have hcoord : ∀ p : Fin K × Fin 2 × Fin 2, ∃ m : ℕ,
      fs l₀ ^ m * bB.repr (fs p.1 ^ n p.1 p.2.1 • bs p.1 p.2.1) p.2.2 ∈ chartRing ℤ x i := by
    rintro ⟨l, q, q'⟩
    obtain ⟨a, ha, hv⟩ := (hiff l₀ _).1 ⟨0, by simpa using hn l q⟩
    have : bB.repr (fs l ^ n l q • bs l q) = a := by
      rw [hv, ← hbB]
      exact bB.repr_sum_self a
    rw [this]
    exact ha q'
  choose m hm using hcoord
  refine ⟨fs l₀, bB, Finset.univ.sup m, hf l₀, hl₀, fun q => ⟨n l₀ q, by rw [hbB]; exact hn l₀ q⟩, ?_⟩
  intro v hv q'
  refine mem_of_forall_pow_mul_mem _ fs cs hf hc hsum fun l => ?_
  obtain ⟨a, ha, hva⟩ := (hiff l v).1 ⟨0, by simpa using hv⟩
  have hterm : ∀ q, ∃ t : ℕ, fs l ^ t * (a q * (fs l₀ ^ Finset.univ.sup m * bB.repr (bs l q) q')) ∈
      chartRing ℤ x i := by
    intro q
    refine loc_mul (ha q) ⟨n l q, ?_⟩
    have h1 := pow_mul_mem_of_le (hf l₀) (Finset.le_sup (f := m) (Finset.mem_univ (l, q, q'))) (hm (l, q, q'))
    have h2 : fs l ^ n l q * (fs l₀ ^ Finset.univ.sup m * bB.repr (bs l q) q') =
        fs l₀ ^ Finset.univ.sup m * bB.repr (fs l ^ n l q • bs l q) q' := by
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
      ring
    rw [h2]
    exact h1
  have hsplit : fs l₀ ^ Finset.univ.sup m * bB.repr v q' =
      a 0 * (fs l₀ ^ Finset.univ.sup m * bB.repr (bs l 0) q') +
        a 1 * (fs l₀ ^ Finset.univ.sup m * bB.repr (bs l 1) q') := by
    rw [hva, Fin.sum_univ_two, map_add, map_smul, map_smul, Finsupp.add_apply, Finsupp.smul_apply,
      Finsupp.smul_apply, smul_eq_mul, smul_eq_mul]
    ring
  rw [hsplit]
  exact loc_add (hf l) (hterm 0) (hterm 1)

/- English proof (translation)
Rewrite using `[Module.Basis.det_apply, Matrix.det_fin_two]`. Simplify using `only [T.detE, Module.Basis.toMatrix_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem detE_eq_det (e b : Module.Basis (Fin 2) Ω E) : T.detE e (b 0) (b 1) = e.det b := by
  rw [Module.Basis.det_apply, Matrix.det_fin_two]
  simp only [T.detE, Module.Basis.toMatrix_apply]
  ring

/- English proof (translation)
Simplify using `only [T.detE, map_smul, Finsupp.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem detE_smul (e : Module.Basis (Fin 2) Ω E) (α β : Ω) (u w : E) :
    T.detE e (α • u) (β • w) = α * β * T.detE e u w := by
  simp only [T.detE, map_smul, Finsupp.smul_apply, smul_eq_mul]
  ring

/- English proof (translation)
Take `⟨f, b, -, -, hf0, hb, -⟩` from `exists_bounded_frame B i hi`. Take `⟨n₀, h₀⟩` from `hb 0`. Take `⟨n₁, h₁⟩` from `hb 1`. Use `⟨_, h₀, _, h₁, ?_⟩` and prove the remaining obligations. Rewrite using `[detE_smul, detE_eq_det]`.

Conclude with `mul_ne_zero (mul_ne_zero (pow_ne_zero _ hf0) (pow_ne_zero _ hf0)) (e.isUnit_det b).ne_zero`.
-/
theorem exists_detE_ne (B : ChartBundle ℤ x 2 E) (i : ι) (hi : x i ≠ 0) (e : Module.Basis (Fin 2) Ω E) :
    ∃ u ∈ B.lat i, ∃ w ∈ B.lat i, T.detE e u w ≠ 0 := by
  obtain ⟨f, b, -, -, hf0, hb, -⟩ := exists_bounded_frame B i hi
  obtain ⟨n₀, h₀⟩ := hb 0
  obtain ⟨n₁, h₁⟩ := hb 1
  refine ⟨_, h₀, _, h₁, ?_⟩
  rw [detE_smul, detE_eq_det]
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hf0) (pow_ne_zero _ hf0)) (e.isUnit_det b).ne_zero

/- English proof (translation)
Take `⟨f, b, N, -, hf0, -, hN⟩` from `exists_bounded_frame B i hi`. Establish `hψ : ∀ q (v : E), (f ^ N • b.coord q) v = f ^ N * b.repr v q` using `fun q v => by`. Simplify using `[Module.Basis.coord_apply]`. Use `⟨f ^ N • b.coord 0, fun v hv => ?_, f ^ N • b.coord 1, fun v hv => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hψ]`.

Conclude with `hN v hv 0`. Rewrite using `[hψ]`. Conclude with `hN v hv 1`. Rewrite using `[hψ, hψ, hψ, hψ]`. Establish `hdet` using `(b.isUnit_det e).ne_zero`.

Rewrite `hdet` using `[Module.Basis.det_apply, Matrix.det_fin_two]`. Simplify using `only [Module.Basis.toMatrix_apply] at hdet`. Establish `: f ^ N * b.repr (e 0) 0 * (f ^ N * b.repr (e 1) 1) - f ^ N * b.repr (e 0) 1 * (f ^ N * b.repr (e 1) 0) = (f ^ N) ^ 2 * (b.repr (e 0) 0 * b.repr (e 1) 1 - b.repr (e 1) 0 * b.repr (e 0) 1)` using `by ring`. Rewrite using `[this]`. Conclude with `mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ hf0)) hdet`.
-/
theorem exists_dual_pair (B : ChartBundle ℤ x 2 E) (i : ι) (hi : x i ≠ 0) (e : Module.Basis (Fin 2) Ω E) :
    ∃ ψ₀ ∈ T.dualLat B i, ∃ ψ₁ ∈ T.dualLat B i, ψ₀ (e 0) * ψ₁ (e 1) - ψ₁ (e 0) * ψ₀ (e 1) ≠ 0 := by
  obtain ⟨f, b, N, -, hf0, -, hN⟩ := exists_bounded_frame B i hi
  have hψ : ∀ q (v : E), (f ^ N • b.coord q) v = f ^ N * b.repr v q := fun q v => by
    simp [Module.Basis.coord_apply]
  refine ⟨f ^ N • b.coord 0, fun v hv => ?_, f ^ N • b.coord 1, fun v hv => ?_, ?_⟩
  · rw [hψ]; exact hN v hv 0
  · rw [hψ]; exact hN v hv 1
  · rw [hψ, hψ, hψ, hψ]
    have hdet := (b.isUnit_det e).ne_zero
    rw [Module.Basis.det_apply, Matrix.det_fin_two] at hdet
    simp only [Module.Basis.toMatrix_apply] at hdet
    have : f ^ N * b.repr (e 0) 0 * (f ^ N * b.repr (e 1) 1) - f ^ N * b.repr (e 0) 1 * (f ^ N * b.repr (e 1) 0) =
        (f ^ N) ^ 2 * (b.repr (e 0) 0 * b.repr (e 1) 1 - b.repr (e 1) 0 * b.repr (e 0) 1) := by ring
    rw [this]
    exact mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ hf0)) hdet

end Bundle

section Forms

variable {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E]

/- English proof (translation)
Establish `hx : ∀ (χ : E →ₗ[Ω] Ω) (v : E), χ v = e.repr v 0 * χ (e 0) + e.repr v 1 * χ (e 1)`. Introduce `χ v`. Establish `h` using `congrArg χ (e.sum_repr v)`. Rewrite `h` using `[map_sum, Fin.sum_univ_two, map_smul, map_smul, smul_eq_mul, smul_eq_mul]`. Conclude with `h.symm`.

Rewrite using `[hx ψ u, hx ψ' w, hx ψ w, hx ψ' u]`. Simplify using `only [T.detE]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dForm_mul_detE (e : Module.Basis (Fin 2) Ω E) (ψ ψ' : E →ₗ[Ω] Ω) (u w : E) :
    (ψ (e 0) * ψ' (e 1) - ψ' (e 0) * ψ (e 1)) * T.detE e u w = ψ u * ψ' w - ψ w * ψ' u := by
  have hx : ∀ (χ : E →ₗ[Ω] Ω) (v : E), χ v = e.repr v 0 * χ (e 0) + e.repr v 1 * χ (e 1) := by
    intro χ v
    have h := congrArg χ (e.sum_repr v)
    rw [map_sum, Fin.sum_univ_two, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h
    exact h.symm
  rw [hx ψ u, hx ψ' w, hx ψ w, hx ψ' u]
  simp only [T.detE]
  ring

/- English proof (translation)
Simplify using `only [T.lineVal, map_sub, map_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lineVal_cross {Φ : Type*} [Field Φ] [Algebra Ω Φ] (e : Module.Basis (Fin 2) Ω E) (ψ ψ' : E →ₗ[Ω] Ω)
    (a₀ a₁ : Φ) :
    T.lineVal e ψ a₀ * T.lineVal e ψ' a₁ - T.lineVal e ψ' a₀ * T.lineVal e ψ a₁ =
      algebraMap Ω Φ (ψ (e 0) * ψ' (e 1) - ψ' (e 0) * ψ (e 1)) * (a₁ - a₀) := by
  simp only [T.lineVal, map_sub, map_mul]
  ring

/- English proof (translation)
Rewrite using `[mul_comm ((∑ k, c' k • s • φ k) (e 0))]`. Simplify using `only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]`. Rewrite using `[Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_sub_distrib]`.

Use `Finset.sum_eq_zero fun k' _ => ?_` and prove the remaining obligations. Take the linear combination `(c k * c' k' * s ^ 2) * hd k k'`.
-/
theorem dForm_sum_eq_zero {κ : Type*} [Fintype κ] (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω)
    (hd : ∀ k k', φ k (e 0) * φ k' (e 1) - φ k' (e 0) * φ k (e 1) = 0) (c c' : κ → Ω) (s : Ω) :
    (∑ k, c k • s • φ k) (e 0) * (∑ k, c' k • s • φ k) (e 1) -
      (∑ k, c' k • s • φ k) (e 0) * (∑ k, c k • s • φ k) (e 1) = 0 := by
  rw [mul_comm ((∑ k, c' k • s • φ k) (e 0))]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun k' _ => ?_
  linear_combination (c k * c' k' * s ^ 2) * hd k k'

end Forms

section Chart

variable {Ω : Type} [Field Ω] {ι κ : Type} {E : Type} [AddCommGroup E] [Module Ω E] {x : ι → Ω}

/- English proof (translation)
Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨u, hu, w, hw, rfl⟩` from `hy`. Take `⟨r₁, hr₁, h₁⟩` from `(mem_lineLat x 1 i _).1 (hsec i hi k u hu)`. Take `⟨r₂, hr₂, h₂⟩` from `(mem_lineLat x 1 i _).1 (hsec i hi k' w hw)`.

Take `⟨r₃, hr₃, h₃⟩` from `(mem_lineLat x 1 i _).1 (hsec i hi k w hw)`. Take `⟨r₄, hr₄, h₄⟩` from `(mem_lineLat x 1 i _).1 (hsec i hi k' u hu)`. Use `⟨r₁ * r₂ - r₃ * r₄, sub_mem (mul_mem hr₁ hr₂) (mul_mem hr₃ hr₄), ?_⟩` and prove the remaining obligations. Rewrite using `[mul_assoc, mul_comm (T.detE e u w), dForm_mul_detE, ← h₁, ← h₂, ← h₃, ← h₄]`. Expand and normalize the polynomial expressions, which then agree.

Consider the case `zero => exact ⟨0, zero_mem _, by simp⟩`. Consider the case `add y z _ _ hy hz`. Take `⟨r, hr, h⟩` from `hy`. Take `⟨s, hs, h'⟩` from `hz`. Conclude with `⟨r + s, add_mem hr hs, by rw [add_mul, h, h']; ring⟩`.

Consider the case `smul c y _ hy`. Take `⟨r, hr, h⟩` from `hy`. Use `⟨c * r, mul_mem c.2 hr, ?_⟩` and prove the remaining obligations. Rewrite using `[Subalgebra.smul_def, smul_eq_mul, mul_assoc, h]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mul_dForm_mem (B : ChartBundle ℤ x 2 E) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω)
    (hsec : T.IsTwistedDualSec B φ) (i : ι) (hi : x i ≠ 0) (k k' : κ) {y : Ω}
    (hy : y ∈ Submodule.span (chartRing ℤ x i) {d | ∃ u ∈ B.lat i, ∃ w ∈ B.lat i, d = x i * T.detE e u w}) :
    ∃ r ∈ chartRing ℤ x i, y * (φ k (e 0) * φ k' (e 1) - φ k' (e 0) * φ k (e 1)) = x i ^ 3 * r := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨u, hu, w, hw, rfl⟩ := hy
    obtain ⟨r₁, hr₁, h₁⟩ := (mem_lineLat x 1 i _).1 (hsec i hi k u hu)
    obtain ⟨r₂, hr₂, h₂⟩ := (mem_lineLat x 1 i _).1 (hsec i hi k' w hw)
    obtain ⟨r₃, hr₃, h₃⟩ := (mem_lineLat x 1 i _).1 (hsec i hi k w hw)
    obtain ⟨r₄, hr₄, h₄⟩ := (mem_lineLat x 1 i _).1 (hsec i hi k' u hu)
    refine ⟨r₁ * r₂ - r₃ * r₄, sub_mem (mul_mem hr₁ hr₂) (mul_mem hr₃ hr₄), ?_⟩
    rw [mul_assoc, mul_comm (T.detE e u w), dForm_mul_detE, ← h₁, ← h₂, ← h₃, ← h₄]
    ring
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨r, hr, h⟩ := hy
    obtain ⟨s, hs, h'⟩ := hz
    exact ⟨r + s, add_mem hr hs, by rw [add_mul, h, h']; ring⟩
  | smul c y _ hy =>
    obtain ⟨r, hr, h⟩ := hy
    refine ⟨c * r, mul_mem c.2 hr, ?_⟩
    rw [Subalgebra.smul_def, smul_eq_mul, mul_assoc, h]
    ring

end Chart

section Homog

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [Fintype K] in
/- English proof (translation)
Introduce `m hm k`. Take `⟨m1, hm1, m2, hm2, rfl⟩` from `Finset.mem_add.mp (MvPolynomial.support_mul f g hm)`. Simplify using `only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf m1 hm1 k, hg m2 hm2 k]`.
-/
theorem isMultiHomog_mul {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) :
    IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf m1 hm1 k, hg m2 hm2 k]

omit [Fintype K] in
/- English proof (translation)
Introduce `m hm k`. Break down `Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h` into its components or cases. Conclude with `hf m h k`. Conclude with `hg m h k`.
-/
theorem isMultiHomog_add {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f + g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
  · exact hf m h k
  · exact hg m h k

omit [Fintype K] in
/- English proof (translation)
Rewrite using `[sub_eq_add_neg]`. Use `isMultiHomog_add hf fun m hm => hg m ?_` and prove the remaining obligations. Rewrite `hm` using `[MvPolynomial.support_neg]`. Then use the resulting hypothesis.
-/
theorem isMultiHomog_sub {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f - g) a := by
  rw [sub_eq_add_neg]
  refine isMultiHomog_add hf fun m hm => hg m ?_
  rwa [MvPolynomial.support_neg] at hm

omit [Fintype K] in
/- English proof (translation)
Introduce `m hm k`. Rewrite `hm` using `[MvPolynomial.mem_support_iff, MvPolynomial.coeff_C]`. Use `split_ifs at hm with h`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Conclude with `absurd rfl hm`.
-/
theorem isMultiHomog_C (r : ℤ) : IsMultiHomog (C r : MRing ι) 0 := by
  classical
  intro m hm k
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C] at hm
  split_ifs at hm with h
  · subst h
    simp
  · exact absurd rfl hm

omit [Fintype K] in
/- English proof (translation)
Introduce `m hm k'`. Rewrite `hm` using `[MvPolynomial.support_X, Finset.mem_singleton]`. Substitute `hm` using the available equality. Distinguish the cases in `h : k' = k`. Substitute `h` using the available equality.

Simplify using `[Finsupp.single_apply]`. Establish `: ∀ j' : ι k', (⟨k, j⟩ : Σ k, ι k) ≠ ⟨k', j'⟩` using `fun j' e => h (congrArg Sigma.fst e).symm`. Simplify using `[h]`.
-/
theorem isMultiHomog_X [DecidableEq K] (k : K) (j : ι k) :
    IsMultiHomog (X ⟨k, j⟩ : MRing ι) (Pi.single k 1) := by
  classical
  intro m hm k'
  rw [MvPolynomial.support_X, Finset.mem_singleton] at hm
  subst hm
  by_cases h : k' = k
  · subst h
    simp [Finsupp.single_apply]
  · have : ∀ j' : ι k', (⟨k, j⟩ : Σ k, ι k) ≠ ⟨k', j'⟩ := fun j' e => h (congrArg Sigma.fst e).symm
    simp [h]

omit [Fintype K] in
/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simpa using isMultiHomog_C (ι := ι) 1`. Consider the case `succ n ih`. Rewrite using `[pow_succ, succ_nsmul]`. Conclude with `isMultiHomog_mul ih hf`.
-/
theorem isMultiHomog_pow {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (n : ℕ) :
    IsMultiHomog (f ^ n) (n • a) := by
  induction n with
  | zero => simpa using isMultiHomog_C (ι := ι) 1
  | succ n ih =>
    rw [pow_succ, succ_nsmul]
    exact isMultiHomog_mul ih hf

omit [Fintype K] in
/- English proof (translation)
The claim follows from `h ▸ hf`.
-/
theorem isMultiHomog_of_eq {f : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a) (h : a = b) :
    IsMultiHomog f b :=
  h ▸ hf

end Homog

section Coord

variable {Ω : Type} [Field Ω] {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ] {E : Type} [AddCommGroup E]
  [Module Ω E] {Φ : Type} [Field Φ] [Algebra Ω Φ]

/- English proof (translation)
Apply the tactic sequence `have hX : ∀ j, IsMultiHomog (X ⟨T.WBlk.base, j⟩ : MRing (T.wwIdx ι ν κ)) (T.wwDeg 1 0) := fun j => isMultiHomog_of_eq (isMultiHomog_X (ι := T.wwIdx ι ν κ) T.WBlk.base j) (by funext b; cases b <;> simp [T.wwDeg])`. Establish `hdeg : ∀ N M, T.wwDeg N 0 + T.wwDeg M 0 = T.wwDeg (N + M) 0` using `fun N M => by`. Apply the tactic sequence `funext b; cases b <;> simp [T.wwDeg]`. Apply the tactic sequence `have hXp : ∀ M, IsMultiHomog ((X ⟨T.WBlk.base, i⟩ : MRing (T.wwIdx ι ν κ)) ^ M) (T.wwDeg M 0) := fun M => isMultiHomog_of_eq (isMultiHomog_pow (hX i) M) (by funext b; cases b <;> simp [T.wwDeg])`. Proceed by induction on `hr using Algebra.adjoin_induction with`.

Consider the case `mem y hy`. Take `⟨j, rfl⟩` from `hy`. Use `⟨1, X ⟨T.WBlk.base, j⟩, hX j, ?_⟩` and prove the remaining obligations. Rewrite using `[aeval_X]`. Use `show algebraMap Ω Φ (x j) = algebraMap Ω Φ (x i ^ 1 * (x j / x i))`.

Use `congr 1`. Clear the denominators using the available nonvanishing facts. Consider the case `algebraMap z`. Apply the tactic sequence `refine ⟨0, C z, isMultiHomog_of_eq (isMultiHomog_C z) (by funext b; cases b <;> rfl), ?_⟩`. Simplify using the standard rewrite rules.

Consider the case `add y z _ _ hy hz`. Take `⟨N, F, hF, hFv⟩` from `hy`. Take `⟨M, G, hG, hGv⟩` from `hz`. Establish `h₁ : IsMultiHomog ((X ⟨T.WBlk.base, i⟩ : MRing (T.wwIdx ι ν κ)) ^ M * F) (T.wwDeg (N + M) 0)`. Use `isMultiHomog_mul (hXp M) hF` as an intermediate fact.

Rewrite `this` using `[hdeg, Nat.add_comm M N]`. Then use the resulting hypothesis. Establish `h₂ : IsMultiHomog ((X ⟨T.WBlk.base, i⟩ : MRing (T.wwIdx ι ν κ)) ^ N * G) (T.wwDeg (N + M) 0)`. Use `isMultiHomog_mul (hXp N) hG` as an intermediate fact. Rewrite `this` using `[hdeg]`. Then use the resulting hypothesis. Use `⟨N + M, _, isMultiHomog_add h₁ h₂, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_add, map_mul, map_mul, map_pow, map_pow, aeval_X, hFv, hGv]`. Use `show algebraMap Ω Φ (x i) ^ M * _ + algebraMap Ω Φ (x i) ^ N * _ = _`. Simplify using `only [map_mul, map_pow, map_add]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `mul y z _ _ hy hz`.

Take `⟨N, F, hF, hFv⟩` from `hy`. Take `⟨M, G, hG, hGv⟩` from `hz`. Establish `h₁ : IsMultiHomog (F * G) (T.wwDeg (N + M) 0)`. Use `isMultiHomog_mul hF hG` as an intermediate fact. Rewrite `this` using `[hdeg]`. Then use the resulting hypothesis.

Use `⟨N + M, F * G, h₁, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, hFv, hGv]`. Simplify using `only [map_mul, map_pow]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_form (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (a₀ a₁ : Φ)
    (i : ι) (hi : x i ≠ 0) {r : Ω} (hr : r ∈ chartRing ℤ x i) :
    ∃ (N : ℕ) (F : MRing (T.wwIdx ι ν κ)), IsMultiHomog F (T.wwDeg N 0) ∧
      aeval (T.wwCoord x δ e φ a₀ a₁) F = algebraMap Ω Φ (x i ^ N * r) := by
  have hX : ∀ j, IsMultiHomog (X ⟨T.WBlk.base, j⟩ : MRing (T.wwIdx ι ν κ)) (T.wwDeg 1 0) := fun j =>
    isMultiHomog_of_eq (isMultiHomog_X (ι := T.wwIdx ι ν κ) T.WBlk.base j)
      (by funext b; cases b <;> simp [T.wwDeg])
  have hdeg : ∀ N M, T.wwDeg N 0 + T.wwDeg M 0 = T.wwDeg (N + M) 0 := fun N M => by
    funext b; cases b <;> simp [T.wwDeg]
  have hXp : ∀ M, IsMultiHomog ((X ⟨T.WBlk.base, i⟩ : MRing (T.wwIdx ι ν κ)) ^ M) (T.wwDeg M 0) := fun M =>
    isMultiHomog_of_eq (isMultiHomog_pow (hX i) M) (by funext b; cases b <;> simp [T.wwDeg])
  induction hr using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    refine ⟨1, X ⟨T.WBlk.base, j⟩, hX j, ?_⟩
    rw [aeval_X]
    show algebraMap Ω Φ (x j) = algebraMap Ω Φ (x i ^ 1 * (x j / x i))
    congr 1
    field_simp
  | algebraMap z =>
    refine ⟨0, C z, isMultiHomog_of_eq (isMultiHomog_C z) (by funext b; cases b <;> rfl), ?_⟩
    simp
  | add y z _ _ hy hz =>
    obtain ⟨N, F, hF, hFv⟩ := hy
    obtain ⟨M, G, hG, hGv⟩ := hz
    have h₁ : IsMultiHomog ((X ⟨T.WBlk.base, i⟩ : MRing (T.wwIdx ι ν κ)) ^ M * F) (T.wwDeg (N + M) 0) := by
      have := isMultiHomog_mul (hXp M) hF
      rwa [hdeg, Nat.add_comm M N] at this
    have h₂ : IsMultiHomog ((X ⟨T.WBlk.base, i⟩ : MRing (T.wwIdx ι ν κ)) ^ N * G) (T.wwDeg (N + M) 0) := by
      have := isMultiHomog_mul (hXp N) hG
      rwa [hdeg] at this
    refine ⟨N + M, _, isMultiHomog_add h₁ h₂, ?_⟩
    rw [map_add, map_mul, map_mul, map_pow, map_pow, aeval_X, hFv, hGv]
    show algebraMap Ω Φ (x i) ^ M * _ + algebraMap Ω Φ (x i) ^ N * _ = _
    simp only [map_mul, map_pow, map_add]
    ring
  | mul y z _ _ hy hz =>
    obtain ⟨N, F, hF, hFv⟩ := hy
    obtain ⟨M, G, hG, hGv⟩ := hz
    have h₁ : IsMultiHomog (F * G) (T.wwDeg (N + M) 0) := by
      have := isMultiHomog_mul hF hG
      rwa [hdeg] at this
    refine ⟨N + M, F * G, h₁, ?_⟩
    rw [map_mul, hFv, hGv]
    simp only [map_mul, map_pow]
    ring

end Coord

end DiagonalForms

open DiagonalForms in

/- English proof (translation)
Introduce `Ω _ ι ν κ _ _ _ E _ _ Φ _ _ x B e φ δ hsec hgen hdet hx a _`. Take `⟨i, hi⟩` from `hx`. Take `⟨u, hu, w, hw, huw⟩` from `exists_detE_ne B i hi e`. Choose the witnesses or unpack the hypotheses as in `⟨l, hl⟩ : ∃ l, δ l ≠ 0 := by`. Assume the negation of the conclusion as `h`.

Use `push Not at h`. Establish `hspan : Submodule.span (chartRing ℤ x i) (Set.range fun l => (x i)⁻¹ * δ l) = ⊥`. Rewrite using `[Submodule.span_eq_bot]`. Introduce and unpack `_ ⟨l, rfl⟩`. Simplify using `[h l]`.

Use `(hdet i hi).2 u hu w hw` as an intermediate fact. Rewrite `this` using `[hspan, Submodule.mem_bot]`. Conclude with `huw this`. Take `⟨ψ₀, h₀, ψ₁, h₁, hψ⟩` from `exists_dual_pair B i hi e`. Choose the witnesses or unpack the hypotheses as in `⟨k, k', hk⟩ : ∃ k k', φ k (e 0) * φ k' (e 1) - φ k' (e 0) * φ k (e 1) ≠ 0 := by`.

Assume the negation of the conclusion as `h`. Use `push Not at h`. Take `⟨c₀, -, rfl⟩` from `hgen i hi ψ₀ h₀`. Take `⟨c₁, -, rfl⟩` from `hgen i hi ψ₁ h₁`. Conclude with `hψ (dForm_sum_eq_zero e φ h c₀ c₁ (x i)⁻¹)`.

Take `⟨r, hr, hrD⟩` from `mul_dForm_mem B e φ hsec i hi k k' ((hdet i hi).1 l)`. Take `⟨N, F, hF, hFv⟩` from `exists_form (ν := ν) (κ := κ) (Φ := Φ) x δ e φ (a 0) (a 1) i hi hr`. Establish `hg : IsMultiHomog ((X ⟨T.WBlk.base, i⟩ : MRing (T.wwIdx ι ν κ)) ^ N * X ⟨T.WBlk.det, l⟩ * (X ⟨T.WBlk.line0, k⟩ * X ⟨T.WBlk.line1, k'⟩ - X ⟨T.WBlk.line0, k'⟩ * X ⟨T.WBlk.line1, k⟩)) (T.wwDeg N 1)`. Use `isMultiHomog_mul (isMultiHomog_mul (isMultiHomog_pow (isMultiHomog_X (ι := T.wwIdx ι ν κ) T.WBlk.base i) N) (isMultiHomog_X (ι := T.wwIdx ι ν κ) T.WBlk.det l)) (isMultiHomog_sub (isMultiHomog_mul (isMultiHomog_X (ι := T.wwIdx ι ν κ) T.WBlk.line0 k) (isMultiHomog_X (ι := T.wwIdx ι …` as an intermediate fact. Use `isMultiHomog_of_eq this ?_` and prove the remaining obligations.

Use function extensionality and compare the values at `b`. Apply the tactic sequence `cases b <;> simp [T.wwDeg]`. Establish `hh : IsMultiHomog ((X ⟨T.WBlk.base, i⟩ : MRing (T.wwIdx ι ν κ)) ^ 3 * F) (T.wwDeg (N + 3) 0)`. Use `isMultiHomog_mul (isMultiHomog_pow (isMultiHomog_X (ι := T.wwIdx ι ν κ) T.WBlk.base i) 3) hF` as an intermediate fact. Use `isMultiHomog_of_eq this ?_` and prove the remaining obligations.

Use function extensionality and compare the values at `b`. Apply the tactic sequence `cases b <;> simp [T.wwDeg]`. Use linear arithmetic over natural numbers and integers. Establish `hkey : x i ^ 3 * (x i ^ N * r) = x i ^ N * δ l * (φ k (e 0) * φ k' (e 1) - φ k' (e 0) * φ k (e 1))`. Rewrite using `[mul_assoc (x i ^ N), hrD]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hhv : aeval (T.wwCoord x δ e φ (a 0) (a 1)) ((X ⟨T.WBlk.base, i⟩ : MRing (T.wwIdx ι ν κ)) ^ 3 * F) = algebraMap Ω Φ (x i ^ N * δ l * (φ k (e 0) * φ k' (e 1) - φ k' (e 0) * φ k (e 1)))`. Rewrite using `[map_mul, map_pow, aeval_X, hFv, ← hkey]`. Use `show algebraMap Ω Φ (x i) ^ 3 * _ = _`. Simplify using `only [map_mul, map_pow]`.

Use `⟨N, _, _, hg, hh, ?_, ?_⟩` and prove the remaining obligations. Use `show _ ∉ RingHom.ker (T.multiConeMap (T.wwCoord x δ e φ (a 0) (a 1)))`. Rewrite using `[DiagRAux.not_mem_ker_iff_aeval_ne _ _ _ hh, hhv]`. Conclude with `(map_ne_zero _).2 (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hi) hl) hk)`. Rewrite using `[hhv]`.

Simplify using `only [map_mul, map_sub, map_pow, aeval_X]`. Use `show algebraMap Ω Φ (x i) ^ N * algebraMap Ω Φ (δ l) * (T.lineVal e (φ k) (a 0) * T.lineVal e (φ k') (a 1) - T.lineVal e (φ k') (a 0) * T.lineVal e (φ k) (a 1)) = T.diagSec a * (algebraMap Ω Φ (x i) ^ N * algebraMap Ω Φ (δ l) * (algebraMap Ω Φ (φ k (e 0)) * algebraMap Ω Φ (φ k' ( …`. Rewrite using `[lineVal_cross, T.diagSec]`. Simplify using `only [map_mul, map_sub]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem DiagForms.proof : DiagForms.Statement := by
  intro Ω _ ι ν κ _ _ _ E _ _ Φ _ _ x B e φ δ hsec hgen hdet hx a _
  classical
  obtain ⟨i, hi⟩ := hx
  obtain ⟨u, hu, w, hw, huw⟩ := exists_detE_ne B i hi e
  obtain ⟨l, hl⟩ : ∃ l, δ l ≠ 0 := by
    by_contra h
    push Not at h
    have hspan : Submodule.span (chartRing ℤ x i) (Set.range fun l => (x i)⁻¹ * δ l) = ⊥ := by
      rw [Submodule.span_eq_bot]
      rintro _ ⟨l, rfl⟩
      simp [h l]
    have := (hdet i hi).2 u hu w hw
    rw [hspan, Submodule.mem_bot] at this
    exact huw this
  obtain ⟨ψ₀, h₀, ψ₁, h₁, hψ⟩ := exists_dual_pair B i hi e
  obtain ⟨k, k', hk⟩ : ∃ k k', φ k (e 0) * φ k' (e 1) - φ k' (e 0) * φ k (e 1) ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨c₀, -, rfl⟩ := hgen i hi ψ₀ h₀
    obtain ⟨c₁, -, rfl⟩ := hgen i hi ψ₁ h₁
    exact hψ (dForm_sum_eq_zero e φ h c₀ c₁ (x i)⁻¹)
  obtain ⟨r, hr, hrD⟩ := mul_dForm_mem B e φ hsec i hi k k' ((hdet i hi).1 l)
  obtain ⟨N, F, hF, hFv⟩ := exists_form (ν := ν) (κ := κ) (Φ := Φ) x δ e φ (a 0) (a 1) i hi hr
  have hg : IsMultiHomog ((X ⟨T.WBlk.base, i⟩ : MRing (T.wwIdx ι ν κ)) ^ N * X ⟨T.WBlk.det, l⟩ *
      (X ⟨T.WBlk.line0, k⟩ * X ⟨T.WBlk.line1, k'⟩ - X ⟨T.WBlk.line0, k'⟩ * X ⟨T.WBlk.line1, k⟩)) (T.wwDeg N 1) := by
    have := isMultiHomog_mul
      (isMultiHomog_mul (isMultiHomog_pow (isMultiHomog_X (ι := T.wwIdx ι ν κ) T.WBlk.base i) N)
        (isMultiHomog_X (ι := T.wwIdx ι ν κ) T.WBlk.det l))
      (isMultiHomog_sub
        (isMultiHomog_mul (isMultiHomog_X (ι := T.wwIdx ι ν κ) T.WBlk.line0 k)
          (isMultiHomog_X (ι := T.wwIdx ι ν κ) T.WBlk.line1 k'))
        (isMultiHomog_mul (isMultiHomog_X (ι := T.wwIdx ι ν κ) T.WBlk.line0 k')
          (isMultiHomog_X (ι := T.wwIdx ι ν κ) T.WBlk.line1 k)))
    refine isMultiHomog_of_eq this ?_
    funext b
    cases b <;> simp [T.wwDeg]
  have hh : IsMultiHomog ((X ⟨T.WBlk.base, i⟩ : MRing (T.wwIdx ι ν κ)) ^ 3 * F) (T.wwDeg (N + 3) 0) := by
    have := isMultiHomog_mul (isMultiHomog_pow (isMultiHomog_X (ι := T.wwIdx ι ν κ) T.WBlk.base i) 3) hF
    refine isMultiHomog_of_eq this ?_
    funext b
    cases b <;> simp [T.wwDeg]
    omega
  have hkey : x i ^ 3 * (x i ^ N * r) =
      x i ^ N * δ l * (φ k (e 0) * φ k' (e 1) - φ k' (e 0) * φ k (e 1)) := by
    rw [mul_assoc (x i ^ N), hrD]
    ring
  have hhv : aeval (T.wwCoord x δ e φ (a 0) (a 1)) ((X ⟨T.WBlk.base, i⟩ : MRing (T.wwIdx ι ν κ)) ^ 3 * F) =
      algebraMap Ω Φ (x i ^ N * δ l * (φ k (e 0) * φ k' (e 1) - φ k' (e 0) * φ k (e 1))) := by
    rw [map_mul, map_pow, aeval_X, hFv, ← hkey]
    show algebraMap Ω Φ (x i) ^ 3 * _ = _
    simp only [map_mul, map_pow]
  refine ⟨N, _, _, hg, hh, ?_, ?_⟩
  · show _ ∉ RingHom.ker (T.multiConeMap (T.wwCoord x δ e φ (a 0) (a 1)))
    rw [DiagRAux.not_mem_ker_iff_aeval_ne _ _ _ hh, hhv]
    exact (map_ne_zero _).2 (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hi) hl) hk)
  · rw [hhv]
    simp only [map_mul, map_sub, map_pow, aeval_X]
    show algebraMap Ω Φ (x i) ^ N * algebraMap Ω Φ (δ l) *
        (T.lineVal e (φ k) (a 0) * T.lineVal e (φ k') (a 1) - T.lineVal e (φ k') (a 0) * T.lineVal e (φ k) (a 1)) =
      T.diagSec a * (algebraMap Ω Φ (x i) ^ N * algebraMap Ω Φ (δ l) *
        (algebraMap Ω Φ (φ k (e 0)) * algebraMap Ω Φ (φ k' (e 1)) -
          algebraMap Ω Φ (φ k' (e 0)) * algebraMap Ω Φ (φ k (e 1))))
    rw [lineVal_cross, T.diagSec]
    simp only [map_mul, map_sub]
    ring

end

end GroundTheory.Heights₂.Heights.Inter
