import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsDiagOffPair
import GroundTheory.HeightsAndTheta.Heights.Intersections.PDiagForms
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

namespace DiagonalOffFrame

section Bundle

variable {Ω : Type*} [Field Ω] {ι : Type*} {E : Type*} [AddCommGroup E] [Module Ω E] {x : ι → Ω}

/- English proof (translation)
Take `⟨K, fs, cs, hf, hc, hsum, hb⟩` from `B.frame i hi`. Use `choose bs hli hsp hiff using hb`. Choose the witnesses or unpack the hypotheses as in `⟨l₀, hl₀⟩ : ∃ l, (⟨fs l, hf l⟩ : chartRing ℤ x i) ∉ q := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`.

Apply `hq.ne_top` to reduce the goal to its premises. Rewrite using `[Ideal.eq_top_iff_one]`. Establish `: (1 : chartRing ℤ x i) = ∑ l, (⟨cs l, hc l⟩ : chartRing ℤ x i) * ⟨fs l, hf l⟩` using `Subtype.ext (by simp [hsum])`. Rewrite using `[this]`. Conclude with `Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (h l)`.

Establish `hgen : ∀ l j, ∃ n : ℕ, fs l ^ n • bs l j ∈ B.lat i`. Introduce `l j`. Use `(hiff l (bs l j)).2 ⟨Pi.single j 1, fun j' => ⟨0, ?_⟩, ?_⟩` and prove the remaining obligations. Break down `eq_or_ne j' j with rfl | h` into its components or cases. Simplify using the standard rewrite rules.

Simplify using `[h]`. Simplify using `[Pi.single_apply]`. Use `choose n hn using hgen`. Set `bB : Module.Basis (Fin 2) Ω E` to `Module.Basis.mk (hli l₀) (hsp l₀).ge`. Establish `hbB : ⇑bB = bs l₀` using `Module.Basis.coe_mk _ _`.

Establish `hcoord : ∀ p : Fin K × Fin 2 × Fin 2, ∃ mm : ℕ, fs l₀ ^ mm * bB.repr (fs p.1 ^ n p.1 p.2.1 • bs p.1 p.2.1) p.2.2 ∈ chartRing ℤ x i`. Introduce and unpack `⟨l, j, j'⟩`. Take `⟨a, ha, hv⟩` from `(hiff l₀ _).1 ⟨0, by simpa using hn l j⟩`. Establish `: bB.repr (fs l ^ n l j • bs l j) = a`. Rewrite using `[hv, ← hbB]`.

Conclude with `bB.repr_sum_self a`. Rewrite using `[this]`. Conclude with `ha j'`. Use `choose mm hmm using hcoord`. Establish `hbound : ∀ v ∈ B.lat i, ∀ j', fs l₀ ^ Finset.univ.sup mm * bB.repr v j' ∈ chartRing ℤ x i`.

Introduce `v hv j'`. Use `DiagonalForms.mem_of_forall_pow_mul_mem _ fs cs hf hc hsum fun l => ?_` and prove the remaining obligations. Take `⟨a, ha, hva⟩` from `(hiff l v).1 ⟨0, by simpa using hv⟩`. Establish `hterm : ∀ j, ∃ t : ℕ, fs l ^ t * (a j * (fs l₀ ^ Finset.univ.sup mm * bB.repr (bs l j) j')) ∈ chartRing ℤ x i`. Introduce `j`.

Use `DiagonalForms.loc_mul (ha j) ⟨n l j, ?_⟩` and prove the remaining obligations. Establish `h1` using `DiagonalForms.pow_mul_mem_of_le (hf l₀) (Finset.le_sup (f := mm) (Finset.mem_univ (l, j, j'))) (hmm (l, j, j'))`. Establish `h2 : fs l ^ n l j * (fs l₀ ^ Finset.univ.sup mm * bB.repr (bs l j) j') = fs l₀ ^ Finset.univ.sup mm * bB.repr (fs l ^ n l j • bs l j) j'`. Rewrite using `[map_smul, Finsupp.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h2]`. Conclude with `h1`. Establish `hsplit : fs l₀ ^ Finset.univ.sup mm * bB.repr v j' = a 0 * (fs l₀ ^ Finset.univ.sup mm * bB.repr (bs l 0) j') + a 1 * (fs l₀ ^ Finset.univ.sup mm * bB.repr (bs l 1) j')`. Rewrite using `[hva, Fin.sum_univ_two, map_add, map_smul, map_smul, Finsupp.add_apply, Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hsplit]`. Conclude with `DiagonalForms.loc_add (hf l) (hterm 0) (hterm 1)`. Establish `hψ : ∀ j (v : E), (fs l₀ ^ Finset.univ.sup mm • bB.coord j) v = fs l₀ ^ Finset.univ.sup mm * bB.repr v j` using `fun j v => by`. Simplify using `[Module.Basis.coord_apply]`. Use `⟨fs l₀ ^ n l₀ 0 • bB 0, by rw [hbB]; exact hn l₀ 0, fs l₀ ^ n l₀ 1 • bB 1, by rw [hbB]; exact hn l₀ 1, fs l₀ ^ Finset.univ.sup mm • bB.coord 0, fun v hv => by rw [hψ]; exact hbound v hv 0, fs l₀ ^ Finset.univ.sup mm • bB.coord 1, fun v hv => by rw [hψ]; exact hbound v hv 1, ⟨fs l …` and prove the remaining obligations.

Rewrite using `[hψ, hψ, hψ, hψ]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_minor_not_mem (B : ChartBundle ℤ x 2 E) (i : ι) (hi : x i ≠ 0)
    (q : Ideal (chartRing ℤ x i)) (hq : q.IsPrime) :
    ∃ u ∈ B.lat i, ∃ w ∈ B.lat i, ∃ ψ ∈ T.dualLat B i, ∃ ψ' ∈ T.dualLat B i,
      ∃ m : chartRing ℤ x i, m ∉ q ∧ (m : Ω) = ψ u * ψ' w - ψ w * ψ' u := by
  classical
  obtain ⟨K, fs, cs, hf, hc, hsum, hb⟩ := B.frame i hi
  choose bs hli hsp hiff using hb
  obtain ⟨l₀, hl₀⟩ : ∃ l, (⟨fs l, hf l⟩ : chartRing ℤ x i) ∉ q := by
    by_contra h
    push Not at h
    apply hq.ne_top
    rw [Ideal.eq_top_iff_one]
    have : (1 : chartRing ℤ x i) = ∑ l, (⟨cs l, hc l⟩ : chartRing ℤ x i) * ⟨fs l, hf l⟩ :=
      Subtype.ext (by simp [hsum])
    rw [this]
    exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (h l)
  have hgen : ∀ l j, ∃ n : ℕ, fs l ^ n • bs l j ∈ B.lat i := by
    intro l j
    refine (hiff l (bs l j)).2 ⟨Pi.single j 1, fun j' => ⟨0, ?_⟩, ?_⟩
    · rcases eq_or_ne j' j with rfl | h
      · simp
      · simp [h]
    · simp [Pi.single_apply]
  choose n hn using hgen
  let bB : Module.Basis (Fin 2) Ω E := Module.Basis.mk (hli l₀) (hsp l₀).ge
  have hbB : ⇑bB = bs l₀ := Module.Basis.coe_mk _ _
  have hcoord : ∀ p : Fin K × Fin 2 × Fin 2, ∃ mm : ℕ,
      fs l₀ ^ mm * bB.repr (fs p.1 ^ n p.1 p.2.1 • bs p.1 p.2.1) p.2.2 ∈ chartRing ℤ x i := by
    rintro ⟨l, j, j'⟩
    obtain ⟨a, ha, hv⟩ := (hiff l₀ _).1 ⟨0, by simpa using hn l j⟩
    have : bB.repr (fs l ^ n l j • bs l j) = a := by
      rw [hv, ← hbB]
      exact bB.repr_sum_self a
    rw [this]
    exact ha j'
  choose mm hmm using hcoord
  have hbound : ∀ v ∈ B.lat i, ∀ j', fs l₀ ^ Finset.univ.sup mm * bB.repr v j' ∈ chartRing ℤ x i := by
    intro v hv j'
    refine DiagonalForms.mem_of_forall_pow_mul_mem _ fs cs hf hc hsum fun l => ?_
    obtain ⟨a, ha, hva⟩ := (hiff l v).1 ⟨0, by simpa using hv⟩
    have hterm : ∀ j, ∃ t : ℕ, fs l ^ t * (a j * (fs l₀ ^ Finset.univ.sup mm * bB.repr (bs l j) j')) ∈
        chartRing ℤ x i := by
      intro j
      refine DiagonalForms.loc_mul (ha j) ⟨n l j, ?_⟩
      have h1 := DiagonalForms.pow_mul_mem_of_le (hf l₀)
        (Finset.le_sup (f := mm) (Finset.mem_univ (l, j, j'))) (hmm (l, j, j'))
      have h2 : fs l ^ n l j * (fs l₀ ^ Finset.univ.sup mm * bB.repr (bs l j) j') =
          fs l₀ ^ Finset.univ.sup mm * bB.repr (fs l ^ n l j • bs l j) j' := by
        rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
        ring
      rw [h2]
      exact h1
    have hsplit : fs l₀ ^ Finset.univ.sup mm * bB.repr v j' =
        a 0 * (fs l₀ ^ Finset.univ.sup mm * bB.repr (bs l 0) j') +
          a 1 * (fs l₀ ^ Finset.univ.sup mm * bB.repr (bs l 1) j') := by
      rw [hva, Fin.sum_univ_two, map_add, map_smul, map_smul, Finsupp.add_apply, Finsupp.smul_apply,
        Finsupp.smul_apply, smul_eq_mul, smul_eq_mul]
      ring
    rw [hsplit]
    exact DiagonalForms.loc_add (hf l) (hterm 0) (hterm 1)
  have hψ : ∀ j (v : E), (fs l₀ ^ Finset.univ.sup mm • bB.coord j) v =
      fs l₀ ^ Finset.univ.sup mm * bB.repr v j := fun j v => by
    simp [Module.Basis.coord_apply]
  refine ⟨fs l₀ ^ n l₀ 0 • bB 0, by rw [hbB]; exact hn l₀ 0, fs l₀ ^ n l₀ 1 • bB 1, by rw [hbB]; exact hn l₀ 1,
    fs l₀ ^ Finset.univ.sup mm • bB.coord 0, fun v hv => by rw [hψ]; exact hbound v hv 0,
    fs l₀ ^ Finset.univ.sup mm • bB.coord 1, fun v hv => by rw [hψ]; exact hbound v hv 1,
    ⟨fs l₀, hf l₀⟩ ^ (2 * Finset.univ.sup mm + n l₀ 0 + n l₀ 1), fun h => hl₀ (hq.mem_of_pow_mem _ h), ?_⟩
  rw [hψ, hψ, hψ, hψ]
  simp
  ring

end Bundle

section Contr

variable {Ω : Type} [Field Ω] {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ] {E : Type} [AddCommGroup E]
  [Module Ω E] {Φ : Type} [Field Φ] [Algebra Ω Φ]

omit [Fintype ι] [Fintype ν] [Fintype κ] in
/- English proof (translation)
Rewrite using `[aeval_X]`. Both sides reduce to the same expression.
-/
theorem aeval_X_base (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (a₀ a₁ : Φ)
    (j : ι) : aeval (T.wwCoord x δ e φ a₀ a₁) (X ⟨T.WBlk.base, j⟩ : MRing (T.wwIdx ι ν κ)) =
      algebraMap Ω Φ (x j) := by
  rw [aeval_X]; rfl

omit [Fintype ι] [Fintype ν] [Fintype κ] in
/- English proof (translation)
Rewrite using `[aeval_X]`. Both sides reduce to the same expression.
-/
theorem aeval_X_det (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (a₀ a₁ : Φ)
    (l : ν) : aeval (T.wwCoord x δ e φ a₀ a₁) (X ⟨T.WBlk.det, l⟩ : MRing (T.wwIdx ι ν κ)) =
      algebraMap Ω Φ (δ l) := by
  rw [aeval_X]; rfl

/- English proof (translation)
The claim follows from `DiagonalForms.isMultiHomog_of_eq (DiagonalForms.isMultiHomog_pow (DiagonalForms.isMultiHomog_X (ι := T.wwIdx ι ν κ) T.WBlk.base j) M) (by funext b; cases b <;> simp [T.wwDeg])`.
-/
theorem isMultiHomog_Xbase_pow (j : ι) (M : ℕ) :
    IsMultiHomog ((X ⟨T.WBlk.base, j⟩ : MRing (T.wwIdx ι ν κ)) ^ M) (T.wwDeg M 0) :=
  DiagonalForms.isMultiHomog_of_eq
    (DiagonalForms.isMultiHomog_pow (DiagonalForms.isMultiHomog_X (ι := T.wwIdx ι ν κ) T.WBlk.base j) M)
    (by funext b; cases b <;> simp [T.wwDeg])

/- English proof (translation)
Apply the tactic sequence `funext b; cases b <;> simp [T.wwDeg]`.
-/
theorem wwDeg_add (N M : ℕ) : T.wwDeg N 0 + T.wwDeg M 0 = T.wwDeg (N + M) 0 := by
  funext b; cases b <;> simp [T.wwDeg]

/- English proof (translation)
Assume the negation of the conclusion as `h'`. Establish `h'' : s ∉ RingHom.ker (T.multiConeMap (T.wwCoord x δ e φ a₀ a₁))` using `h'`. Conclude with `((DiagRAux.not_mem_ker_iff_aeval_ne _ s β hs).1 h'') h`.
-/
theorem mem_wwIdeal_of_aeval_eq_zero (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E)
    (φ : κ → E →ₗ[Ω] Ω) (a₀ a₁ : Φ) {s : MRing (T.wwIdx ι ν κ)} {β : T.WBlk → ℕ} (hs : IsMultiHomog s β)
    (h : aeval (T.wwCoord x δ e φ a₀ a₁) s = 0) : s ∈ T.wwIdeal x δ e φ a₀ a₁ := by
  by_contra h'
  have h'' : s ∉ RingHom.ker (T.multiConeMap (T.wwCoord x δ e φ a₀ a₁)) := h'
  exact ((DiagRAux.not_mem_ker_iff_aeval_ne _ s β hs).1 h'') h

/- English proof (translation)
Establish `hd : (X ⟨T.WBlk.base, i⟩ : MRing (T.wwIdx ι ν κ)) ^ M * F - X ⟨T.WBlk.base, i⟩ ^ N * G ∈ W`. Use `hle (mem_wwIdeal_of_aeval_eq_zero x δ e φ a₀ a₁ (β := T.wwDeg (M + N) 0) ?_ ?_)` and prove the remaining obligations. Use `DiagonalForms.isMultiHomog_sub ?_ ?_` and prove the remaining obligations. Rewrite using `[← wwDeg_add]`. Conclude with `DiagonalForms.isMultiHomog_mul (isMultiHomog_Xbase_pow i M) hF`.

Rewrite using `[Nat.add_comm, ← wwDeg_add]`. Conclude with `DiagonalForms.isMultiHomog_mul (isMultiHomog_Xbase_pow i N) hG`. Simplify using `only [map_sub, map_mul, map_pow, aeval_X_base, hFv, hGv]`. Expand and normalize the polynomial expressions, which then agree. Establish `h2` using `W.sub_mem (W.mul_mem_left ((X ⟨T.WBlk.base, i⟩ : MRing (T.wwIdx ι ν κ)) ^ M) hFW) hd`.

Rewrite `h2` using `[sub_sub_cancel]`. Break down `hW.mem_or_mem h2 with h | h` into its components or cases. Conclude with `absurd (hW.mem_of_pow_mem _ h) hXi`. Conclude with `h`.
-/
theorem form_mem_of_form_mem (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω)
    (a₀ a₁ : Φ) {W : Ideal (MRing (T.wwIdx ι ν κ))} (hW : W.IsPrime) (hle : T.wwIdeal x δ e φ a₀ a₁ ≤ W)
    {i : ι} (hXi : (X ⟨T.WBlk.base, i⟩ : MRing (T.wwIdx ι ν κ)) ∉ W) {r : Ω} {N M : ℕ}
    {F G : MRing (T.wwIdx ι ν κ)} (hF : IsMultiHomog F (T.wwDeg N 0))
    (hFv : aeval (T.wwCoord x δ e φ a₀ a₁) F = algebraMap Ω Φ (x i ^ N * r))
    (hG : IsMultiHomog G (T.wwDeg M 0))
    (hGv : aeval (T.wwCoord x δ e φ a₀ a₁) G = algebraMap Ω Φ (x i ^ M * r)) (hFW : F ∈ W) : G ∈ W := by
  have hd : (X ⟨T.WBlk.base, i⟩ : MRing (T.wwIdx ι ν κ)) ^ M * F - X ⟨T.WBlk.base, i⟩ ^ N * G ∈ W := by
    refine hle (mem_wwIdeal_of_aeval_eq_zero x δ e φ a₀ a₁ (β := T.wwDeg (M + N) 0) ?_ ?_)
    · refine DiagonalForms.isMultiHomog_sub ?_ ?_
      · rw [← wwDeg_add]
        exact DiagonalForms.isMultiHomog_mul (isMultiHomog_Xbase_pow i M) hF
      · rw [Nat.add_comm, ← wwDeg_add]
        exact DiagonalForms.isMultiHomog_mul (isMultiHomog_Xbase_pow i N) hG
    · simp only [map_sub, map_mul, map_pow, aeval_X_base, hFv, hGv]
      ring
  have h2 := W.sub_mem (W.mul_mem_left ((X ⟨T.WBlk.base, i⟩ : MRing (T.wwIdx ι ν κ)) ^ M) hFW) hd
  rw [sub_sub_cancel] at h2
  rcases hW.mem_or_mem h2 with h | h
  · exact absurd (hW.mem_of_pow_mem _ h) hXi
  · exact h

/- English proof (translation)
Establish `form : ∀ r : chartRing ℤ x i, ∃ (N : ℕ) (F : MRing (T.wwIdx ι ν κ)), IsMultiHomog F (T.wwDeg N 0) ∧ aeval (T.wwCoord x δ e φ a₀ a₁) F = algebraMap Ω Φ (x i ^ N * r)` using `fun r => DiagonalForms.exists_form x δ e φ a₀ a₁ i hi r.2`. Set `q : Ideal (chartRing ℤ x i)` to `{ carrier := {r | ∃ (N : ℕ) (F : MRing (T.wwIdx ι ν κ)), IsMultiHomog F (T.wwDeg N 0) ∧ aeval (T.wwCoord x δ e φ a₀ a₁) F = algebraMap Ω Φ (x i ^ N * r) ∧ F ∈ W} add_mem' := by`. Introduce and unpack `r s ⟨N, F, hF, hFv, hFW⟩ ⟨M, G, hG, hGv, hGW⟩`. Use `⟨N + M, X ⟨T.WBlk.base, i⟩ ^ M * F + X ⟨T.WBlk.base, i⟩ ^ N * G, ?_, ?_, W.add_mem (W.mul_mem_left _ hFW) (W.mul_mem_left _ hGW)⟩` and prove the remaining obligations. Use `DiagonalForms.isMultiHomog_add ?_ ?_` and prove the remaining obligations.

Rewrite using `[Nat.add_comm, ← wwDeg_add]`. Conclude with `DiagonalForms.isMultiHomog_mul (isMultiHomog_Xbase_pow i M) hF`. Rewrite using `[← wwDeg_add]`. Conclude with `DiagonalForms.isMultiHomog_mul (isMultiHomog_Xbase_pow i N) hG`. Simplify using `only [map_add, map_mul, map_pow, aeval_X_base, hFv, hGv, Subalgebra.coe_add]`.

Expand and normalize the polynomial expressions, which then agree. Use the proof step `zero_mem' := ⟨0, 0, fun m hm => by simp at hm, by simp, W.zero_mem⟩`. Use the proof step `smul_mem' := by`. Introduce and unpack `c r ⟨N, F, hF, hFv, hFW⟩`. Take `⟨M, G, hG, hGv⟩` from `form c`.

Use `⟨M + N, G * F, ?_, ?_, W.mul_mem_left _ hFW⟩` and prove the remaining obligations. Rewrite using `[← wwDeg_add]`. Conclude with `DiagonalForms.isMultiHomog_mul hG hF`. Simplify using `only [map_mul, map_pow, hGv, hFv, smul_eq_mul, Subalgebra.coe_mul]`. Use `ring }`.

Establish `hprime : q.IsPrime`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Ne, Ideal.eq_top_iff_one]`. Introduce and unpack `⟨N, F, hF, hFv, hFW⟩`. Establish `h1` using `form_mem_of_form_mem x δ e φ a₀ a₁ hW hle hXi (M := 1) (G := (X ⟨T.WBlk.base, i⟩ : MRing (T.wwIdx ι ν κ)) ^ 1) hF hFv (isMultiHomog_Xbase_pow i 1) (by rw [map_pow, aeval_X_base]; simp) hFW`.

Conclude with `hXi (hW.mem_of_pow_mem _ h1)`. Introduce and unpack `r s ⟨N, F, hF, hFv, hFW⟩`. Take `⟨M, G, hG, hGv⟩` from `form r`. Take `⟨M', G', hG', hGv'⟩` from `form s`. Establish `hGG : G * G' ∈ W`.

Use `form_mem_of_form_mem x δ e φ a₀ a₁ hW hle hXi (M := M + M') hF hFv ?_ ?_ hFW` and prove the remaining obligations. Rewrite using `[← wwDeg_add]`. Conclude with `DiagonalForms.isMultiHomog_mul hG hG'`. Simplify using `only [map_mul, map_pow, hGv, hGv', Subalgebra.coe_mul]`. Expand and normalize the polynomial expressions, which then agree.

Break down `hW.mem_or_mem hGG with h | h` into its components or cases. Conclude with `Or.inl ⟨M, G, hG, hGv, h⟩`. Conclude with `Or.inr ⟨M', G', hG', hGv', h⟩`. Conclude with `⟨q, hprime, fun r hr N F hF hFv hFW => hr ⟨N, F, hF, hFv, hFW⟩⟩`.
-/
theorem exists_contr (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (a₀ a₁ : Φ)
    (i : ι) (hi : x i ≠ 0) (W : Ideal (MRing (T.wwIdx ι ν κ))) (hW : W.IsPrime)
    (hle : T.wwIdeal x δ e φ a₀ a₁ ≤ W) (hXi : (X ⟨T.WBlk.base, i⟩ : MRing (T.wwIdx ι ν κ)) ∉ W) :
    ∃ q : Ideal (chartRing ℤ x i), q.IsPrime ∧ ∀ r : chartRing ℤ x i, r ∉ q →
      ∀ (N : ℕ) (F : MRing (T.wwIdx ι ν κ)), IsMultiHomog F (T.wwDeg N 0) →
        aeval (T.wwCoord x δ e φ a₀ a₁) F = algebraMap Ω Φ (x i ^ N * r) → F ∉ W := by
  classical
  have form : ∀ r : chartRing ℤ x i, ∃ (N : ℕ) (F : MRing (T.wwIdx ι ν κ)), IsMultiHomog F (T.wwDeg N 0) ∧
      aeval (T.wwCoord x δ e φ a₀ a₁) F = algebraMap Ω Φ (x i ^ N * r) := fun r =>
    DiagonalForms.exists_form x δ e φ a₀ a₁ i hi r.2
  let q : Ideal (chartRing ℤ x i) :=
    { carrier := {r | ∃ (N : ℕ) (F : MRing (T.wwIdx ι ν κ)), IsMultiHomog F (T.wwDeg N 0) ∧
        aeval (T.wwCoord x δ e φ a₀ a₁) F = algebraMap Ω Φ (x i ^ N * r) ∧ F ∈ W}
      add_mem' := by
        rintro r s ⟨N, F, hF, hFv, hFW⟩ ⟨M, G, hG, hGv, hGW⟩
        refine ⟨N + M, X ⟨T.WBlk.base, i⟩ ^ M * F + X ⟨T.WBlk.base, i⟩ ^ N * G, ?_, ?_,
          W.add_mem (W.mul_mem_left _ hFW) (W.mul_mem_left _ hGW)⟩
        · refine DiagonalForms.isMultiHomog_add ?_ ?_
          · rw [Nat.add_comm, ← wwDeg_add]
            exact DiagonalForms.isMultiHomog_mul (isMultiHomog_Xbase_pow i M) hF
          · rw [← wwDeg_add]
            exact DiagonalForms.isMultiHomog_mul (isMultiHomog_Xbase_pow i N) hG
        · simp only [map_add, map_mul, map_pow, aeval_X_base, hFv, hGv, Subalgebra.coe_add]
          ring
      zero_mem' := ⟨0, 0, fun m hm => by simp at hm, by simp, W.zero_mem⟩
      smul_mem' := by
        rintro c r ⟨N, F, hF, hFv, hFW⟩
        obtain ⟨M, G, hG, hGv⟩ := form c
        refine ⟨M + N, G * F, ?_, ?_, W.mul_mem_left _ hFW⟩
        · rw [← wwDeg_add]
          exact DiagonalForms.isMultiHomog_mul hG hF
        · simp only [map_mul, map_pow, hGv, hFv, smul_eq_mul, Subalgebra.coe_mul]
          ring }
  have hprime : q.IsPrime := by
    refine ⟨?_, ?_⟩
    · rw [Ne, Ideal.eq_top_iff_one]
      rintro ⟨N, F, hF, hFv, hFW⟩
      have h1 := form_mem_of_form_mem x δ e φ a₀ a₁ hW hle hXi (M := 1)
        (G := (X ⟨T.WBlk.base, i⟩ : MRing (T.wwIdx ι ν κ)) ^ 1) hF hFv (isMultiHomog_Xbase_pow i 1)
        (by rw [map_pow, aeval_X_base]; simp) hFW
      exact hXi (hW.mem_of_pow_mem _ h1)
    · rintro r s ⟨N, F, hF, hFv, hFW⟩
      obtain ⟨M, G, hG, hGv⟩ := form r
      obtain ⟨M', G', hG', hGv'⟩ := form s
      have hGG : G * G' ∈ W := by
        refine form_mem_of_form_mem x δ e φ a₀ a₁ hW hle hXi (M := M + M') hF hFv ?_ ?_ hFW
        · rw [← wwDeg_add]
          exact DiagonalForms.isMultiHomog_mul hG hG'
        · simp only [map_mul, map_pow, hGv, hGv', Subalgebra.coe_mul]
          ring
      rcases hW.mem_or_mem hGG with h | h
      · exact Or.inl ⟨M, G, hG, hGv, h⟩
      · exact Or.inr ⟨M', G', hG', hGv', h⟩
  exact ⟨q, hprime, fun r hr N F hF hFv hFW => hr ⟨N, F, hF, hFv, hFW⟩⟩

end Contr

end DiagonalOffFrame

open DiagonalOffFrame in

/- English proof (translation)
Introduce `Ω _ ι ν κ _ _ _ E _ _ Φ _ _ x B e φ δ hsec hgen hdet _ a _ W hW hrel hle`. Establish `hbase : ∃ i : ι, (X ⟨T.WBlk.base, i⟩ : MRing (T.wwIdx ι ν κ)) ∉ W` using `hrel T.WBlk.base`. Take `⟨i, hXi'⟩` from `hbase`. Establish `hi : x i ≠ 0`. Introduce `h0`.

Use `hXi' (hle (mem_wwIdeal_of_aeval_eq_zero x δ e φ (a 0) (a 1) (DiagonalForms.isMultiHomog_X (ι := T.wwIdx ι ν κ) T.WBlk.base i) ?_))` and prove the remaining obligations. Rewrite using `[aeval_X_base, h0, map_zero]`. Take `⟨q, hq, hqW⟩` from `exists_contr x δ e φ (a 0) (a 1) i hi W hW hle hXi'`. Take `⟨u, hu, w, hw, ψ, hψ, ψ', hψ', m, hm, hmv⟩` from `exists_minor_not_mem B i hi q hq`. Establish `hr : ∀ (l : ν) (k k' : κ), ∃ r : chartRing ℤ x i, δ l * dualMinor e φ k k' = x i ^ 3 * r` using `fun l k k' =>`.

Set `⟨r, hr, h⟩` to `DiagonalForms.mul_dForm_mem B e φ hsec i hi k k' ((hdet i hi).1 l)`. Use the proof step `⟨⟨r, hr⟩, h⟩`. Use `choose r hrv using hr`. Choose the witnesses or unpack the hypotheses as in `⟨l, k, k', hlkk⟩ : ∃ l k k', r l k k' ∉ q := by`. Assume the negation of the conclusion as `hall`.

Use `push Not at hall`. Take `⟨c, hc, rfl⟩` from `hgen i hi ψ hψ`. Take `⟨c', hc', rfl⟩` from `hgen i hi ψ' hψ'`. Take `⟨d, hd⟩` from `(Submodule.mem_span_range_iff_exists_fun (chartRing ℤ x i)).1 ((hdet i hi).2 u hu w hw)`. Establish `hD : (∑ k, c k • (x i)⁻¹ • φ k) (e 0) * (∑ k, c' k • (x i)⁻¹ • φ k) (e 1) - (∑ k, c' k • (x i)⁻¹ • φ k) (e 0) * (∑ k, c k • (x i)⁻¹ • φ k) (e 1) = ∑ k, ∑ k', c k * c' k' * ((x i)⁻¹ ^ 2 * dualMinor e φ k k')`.

Rewrite using `[mul_comm ((∑ k, c' k • (x i)⁻¹ • φ k) (e 0))]`. Simplify using `only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]`. Rewrite using `[Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_sub_distrib]`.

Use `Finset.sum_congr rfl fun k' _ => ?_` and prove the remaining obligations. Simplify using `only [dualMinor]`. Expand and normalize the polynomial expressions, which then agree. Establish `hdet' : T.detE e u w = ∑ l, (d l : Ω) * ((x i)⁻¹ * δ l)`. Rewrite using `[← hd]`.

Simplify using `only [Subalgebra.smul_def, smul_eq_mul]`. Establish `hsum : (m : Ω) = ((∑ k, ∑ k', ∑ l, (⟨c k, hc k⟩ : chartRing ℤ x i) * ⟨c' k', hc' k'⟩ * d l * r l k k' : chartRing ℤ x i) : Ω)`. Rewrite using `[hmv, ← DiagonalForms.dForm_mul_detE e, hD, hdet']`. Use `push_cast`. Rewrite using `[Finset.sum_mul]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_congr rfl fun k' _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations.

Establish `hrl : (r l k k' : Ω) = (x i ^ 3)⁻¹ * (δ l * dualMinor e φ k k')`. Rewrite using `[hrv]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hrl]`. Clear the denominators using the available nonvanishing facts.

Apply `hm` to reduce the goal to its premises. Rewrite using `[Subtype.ext hsum]`. Conclude with `Ideal.sum_mem _ fun k _ => Ideal.sum_mem _ fun k' _ => Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hall l k k')`. Establish `hG3 : ∀ {N : ℕ} {F : MRing (T.wwIdx ι ν κ)}, IsMultiHomog F (T.wwDeg N 0) → IsMultiHomog ((X ⟨T.WBlk.base, i⟩ : MRing (T.wwIdx ι ν κ)) ^ 3 * F) (T.wwDeg (N + 3) 0)`. Introduce `N F hF`.

Rewrite using `[Nat.add_comm, ← wwDeg_add]`. Conclude with `DiagonalForms.isMultiHomog_mul (isMultiHomog_Xbase_pow i 3) hF`. Take `⟨N, F, hF, hFv⟩` from `DiagonalForms.exists_form (ν := ν) (κ := κ) (Φ := Φ) x δ e φ (a 0) (a 1) i hi (r l k k').2`. Establish `hFW : F ∉ W` using `hqW _ hlkk N F hF hFv`. Establish `hGW : (X ⟨T.WBlk.base, i⟩ : MRing (T.wwIdx ι ν κ)) ^ 3 * F ∉ W` using `fun h => (hW.mem_or_mem h).elim (fun h3 => hXi' (hW.mem_of_pow_mem _ h3)) hFW`.

Establish `hGv : aeval (T.wwCoord x δ e φ (a 0) (a 1)) ((X ⟨T.WBlk.base, i⟩ : MRing (T.wwIdx ι ν κ)) ^ 3 * F) = algebraMap Ω Φ (x i ^ N * δ l * dualMinor e φ k k')`. Establish `key : x i ^ 3 * (x i ^ N * (r l k k' : Ω)) = x i ^ N * δ l * dualMinor e φ k k'`. Rewrite using `[mul_assoc (x i ^ N), hrv]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[map_mul, map_pow, aeval_X_base, hFv, ← key]`.

Simplify using `only [map_mul, map_pow]`. Establish `hXl : (X ⟨T.WBlk.det, l⟩ : MRing (T.wwIdx ι ν κ)) ∉ W`. Introduce `hl`. Establish `hdet0 : ∃ l' : ν, (X ⟨T.WBlk.det, l'⟩ : MRing (T.wwIdx ι ν κ)) ∉ W` using `hrel T.WBlk.det`. Take `⟨l', hl''⟩` from `hdet0`.

Take `⟨M, F', hF', hFv'⟩` from `DiagonalForms.exists_form (ν := ν) (κ := κ) (Φ := Φ) x δ e φ (a 0) (a 1) i hi (r l' k k').2`. Establish `hdiff : (X ⟨T.WBlk.det, l'⟩ : MRing (T.wwIdx ι ν κ)) * X ⟨T.WBlk.base, i⟩ ^ M * (X ⟨T.WBlk.base, i⟩ ^ 3 * F) - X ⟨T.WBlk.det, l⟩ * X ⟨T.WBlk.base, i⟩ ^ N * (X ⟨T.WBlk.base, i⟩ ^ 3 * F') ∈ W`. Use `hle (mem_wwIdeal_of_aeval_eq_zero x δ e φ (a 0) (a 1) (β := Pi.single T.WBlk.det 1 + T.wwDeg M 0 + T.wwDeg (N + 3) 0) ?_ ?_)` and prove the remaining obligations. Use `DiagonalForms.isMultiHomog_sub (DiagonalForms.isMultiHomog_mul (DiagonalForms.isMultiHomog_mul (DiagonalForms.isMultiHomog_X (ι := T.wwIdx ι ν κ) T.WBlk.det l') (isMultiHomog_Xbase_pow i M)) (hG3 hF)) ?_` and prove the remaining obligations. Use `DiagonalForms.isMultiHomog_of_eq (DiagonalForms.isMultiHomog_mul (DiagonalForms.isMultiHomog_mul (DiagonalForms.isMultiHomog_X (ι := T.wwIdx ι ν κ) T.WBlk.det l) (isMultiHomog_Xbase_pow i N)) (hG3 hF')) ?_` and prove the remaining obligations.

Use function extensionality and compare the values at `b`. Apply the tactic sequence `cases b <;> simp [T.wwDeg, Pi.single_apply] <;> omega`. Establish `h1` using `congrArg (algebraMap Ω Φ) (hrv l k k')`. Establish `h2` using `congrArg (algebraMap Ω Φ) (hrv l' k k')`. Simplify using `only [map_mul, map_pow] at h1 h2`.

Simplify using `only [map_sub, map_mul, map_pow, aeval_X_det, aeval_X_base, hFv, hFv']`. Take the linear combination `(-(algebraMap Ω Φ (δ l') * algebraMap Ω Φ (x i) ^ M * algebraMap Ω Φ (x i) ^ N)) * h1 + (algebraMap Ω Φ (δ l) * algebraMap Ω Φ (x i) ^ N * algebraMap Ω Φ (x i) ^ M) * h2`. Establish `h3` using `W.add_mem hdiff (W.mul_mem_right (X ⟨T.WBlk.base, i⟩ ^ 3 * F') (W.mul_mem_right (X ⟨T.WBlk.base, i⟩ ^ N) hl))`. Rewrite `h3` using `[sub_add_cancel]`. Break down `hW.mem_or_mem h3 with h | h` into its components or cases.

Break down `hW.mem_or_mem h with h | h` into its components or cases. Conclude with `hl'' h`. Conclude with `hXi' (hW.mem_of_pow_mem _ h)`. Conclude with `hGW h`. Conclude with `⟨i, l, k, k', hXi', hXl, N, _, hG3 hF, hGv, hGW⟩`.
-/
theorem DiagOffFrame.proof : DiagOffFrame.Statement := by
  intro Ω _ ι ν κ _ _ _ E _ _ Φ _ _ x B e φ δ hsec hgen hdet _ a _ W hW hrel hle
  classical
  have hbase : ∃ i : ι, (X ⟨T.WBlk.base, i⟩ : MRing (T.wwIdx ι ν κ)) ∉ W := hrel T.WBlk.base
  obtain ⟨i, hXi'⟩ := hbase
  have hi : x i ≠ 0 := by
    intro h0
    refine hXi' (hle (mem_wwIdeal_of_aeval_eq_zero x δ e φ (a 0) (a 1)
      (DiagonalForms.isMultiHomog_X (ι := T.wwIdx ι ν κ) T.WBlk.base i) ?_))
    rw [aeval_X_base, h0, map_zero]
  obtain ⟨q, hq, hqW⟩ := exists_contr x δ e φ (a 0) (a 1) i hi W hW hle hXi'
  obtain ⟨u, hu, w, hw, ψ, hψ, ψ', hψ', m, hm, hmv⟩ := exists_minor_not_mem B i hi q hq
  have hr : ∀ (l : ν) (k k' : κ), ∃ r : chartRing ℤ x i, δ l * dualMinor e φ k k' = x i ^ 3 * r :=
    fun l k k' =>
      let ⟨r, hr, h⟩ := DiagonalForms.mul_dForm_mem B e φ hsec i hi k k' ((hdet i hi).1 l)
      ⟨⟨r, hr⟩, h⟩
  choose r hrv using hr
  obtain ⟨l, k, k', hlkk⟩ : ∃ l k k', r l k k' ∉ q := by
    by_contra hall
    push Not at hall
    obtain ⟨c, hc, rfl⟩ := hgen i hi ψ hψ
    obtain ⟨c', hc', rfl⟩ := hgen i hi ψ' hψ'
    obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun (chartRing ℤ x i)).1 ((hdet i hi).2 u hu w hw)
    have hD : (∑ k, c k • (x i)⁻¹ • φ k) (e 0) * (∑ k, c' k • (x i)⁻¹ • φ k) (e 1) -
        (∑ k, c' k • (x i)⁻¹ • φ k) (e 0) * (∑ k, c k • (x i)⁻¹ • φ k) (e 1) =
        ∑ k, ∑ k', c k * c' k' * ((x i)⁻¹ ^ 2 * dualMinor e φ k k') := by
      rw [mul_comm ((∑ k, c' k • (x i)⁻¹ • φ k) (e 0))]
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k' _ => ?_
      simp only [dualMinor]
      ring
    have hdet' : T.detE e u w = ∑ l, (d l : Ω) * ((x i)⁻¹ * δ l) := by
      rw [← hd]
      simp only [Subalgebra.smul_def, smul_eq_mul]
    have hsum : (m : Ω) = ((∑ k, ∑ k', ∑ l, (⟨c k, hc k⟩ : chartRing ℤ x i) * ⟨c' k', hc' k'⟩ * d l *
        r l k k' : chartRing ℤ x i) : Ω) := by
      rw [hmv, ← DiagonalForms.dForm_mul_detE e, hD, hdet']
      push_cast
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun k' _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      have hrl : (r l k k' : Ω) = (x i ^ 3)⁻¹ * (δ l * dualMinor e φ k k') := by
        rw [hrv]
        field_simp
      rw [hrl]
      field_simp
    apply hm
    rw [Subtype.ext hsum]
    exact Ideal.sum_mem _ fun k _ => Ideal.sum_mem _ fun k' _ => Ideal.sum_mem _ fun l _ =>
      Ideal.mul_mem_left _ _ (hall l k k')
  have hG3 : ∀ {N : ℕ} {F : MRing (T.wwIdx ι ν κ)}, IsMultiHomog F (T.wwDeg N 0) →
      IsMultiHomog ((X ⟨T.WBlk.base, i⟩ : MRing (T.wwIdx ι ν κ)) ^ 3 * F) (T.wwDeg (N + 3) 0) := by
    intro N F hF
    rw [Nat.add_comm, ← wwDeg_add]
    exact DiagonalForms.isMultiHomog_mul (isMultiHomog_Xbase_pow i 3) hF
  obtain ⟨N, F, hF, hFv⟩ := DiagonalForms.exists_form (ν := ν) (κ := κ) (Φ := Φ) x δ e φ (a 0) (a 1) i hi
    (r l k k').2
  have hFW : F ∉ W := hqW _ hlkk N F hF hFv
  have hGW : (X ⟨T.WBlk.base, i⟩ : MRing (T.wwIdx ι ν κ)) ^ 3 * F ∉ W := fun h =>
    (hW.mem_or_mem h).elim (fun h3 => hXi' (hW.mem_of_pow_mem _ h3)) hFW
  have hGv : aeval (T.wwCoord x δ e φ (a 0) (a 1)) ((X ⟨T.WBlk.base, i⟩ : MRing (T.wwIdx ι ν κ)) ^ 3 * F) =
      algebraMap Ω Φ (x i ^ N * δ l * dualMinor e φ k k') := by
    have key : x i ^ 3 * (x i ^ N * (r l k k' : Ω)) = x i ^ N * δ l * dualMinor e φ k k' := by
      rw [mul_assoc (x i ^ N), hrv]
      ring
    rw [map_mul, map_pow, aeval_X_base, hFv, ← key]
    simp only [map_mul, map_pow]
  have hXl : (X ⟨T.WBlk.det, l⟩ : MRing (T.wwIdx ι ν κ)) ∉ W := by
    intro hl
    have hdet0 : ∃ l' : ν, (X ⟨T.WBlk.det, l'⟩ : MRing (T.wwIdx ι ν κ)) ∉ W := hrel T.WBlk.det
    obtain ⟨l', hl''⟩ := hdet0
    obtain ⟨M, F', hF', hFv'⟩ := DiagonalForms.exists_form (ν := ν) (κ := κ) (Φ := Φ) x δ e φ (a 0) (a 1) i hi
      (r l' k k').2
    have hdiff : (X ⟨T.WBlk.det, l'⟩ : MRing (T.wwIdx ι ν κ)) * X ⟨T.WBlk.base, i⟩ ^ M *
        (X ⟨T.WBlk.base, i⟩ ^ 3 * F) -
        X ⟨T.WBlk.det, l⟩ * X ⟨T.WBlk.base, i⟩ ^ N * (X ⟨T.WBlk.base, i⟩ ^ 3 * F') ∈ W := by
      refine hle (mem_wwIdeal_of_aeval_eq_zero x δ e φ (a 0) (a 1)
        (β := Pi.single T.WBlk.det 1 + T.wwDeg M 0 + T.wwDeg (N + 3) 0) ?_ ?_)
      · refine DiagonalForms.isMultiHomog_sub (DiagonalForms.isMultiHomog_mul (DiagonalForms.isMultiHomog_mul
          (DiagonalForms.isMultiHomog_X (ι := T.wwIdx ι ν κ) T.WBlk.det l') (isMultiHomog_Xbase_pow i M))
          (hG3 hF)) ?_
        refine DiagonalForms.isMultiHomog_of_eq (DiagonalForms.isMultiHomog_mul (DiagonalForms.isMultiHomog_mul
          (DiagonalForms.isMultiHomog_X (ι := T.wwIdx ι ν κ) T.WBlk.det l) (isMultiHomog_Xbase_pow i N))
          (hG3 hF')) ?_
        funext b
        cases b <;> simp [T.wwDeg, Pi.single_apply] <;> omega
      · have h1 := congrArg (algebraMap Ω Φ) (hrv l k k')
        have h2 := congrArg (algebraMap Ω Φ) (hrv l' k k')
        simp only [map_mul, map_pow] at h1 h2
        simp only [map_sub, map_mul, map_pow, aeval_X_det, aeval_X_base, hFv, hFv']
        linear_combination
          (-(algebraMap Ω Φ (δ l') * algebraMap Ω Φ (x i) ^ M * algebraMap Ω Φ (x i) ^ N)) * h1 +
            (algebraMap Ω Φ (δ l) * algebraMap Ω Φ (x i) ^ N * algebraMap Ω Φ (x i) ^ M) * h2
    have h3 := W.add_mem hdiff (W.mul_mem_right (X ⟨T.WBlk.base, i⟩ ^ 3 * F')
      (W.mul_mem_right (X ⟨T.WBlk.base, i⟩ ^ N) hl))
    rw [sub_add_cancel] at h3
    rcases hW.mem_or_mem h3 with h | h
    · rcases hW.mem_or_mem h with h | h
      · exact hl'' h
      · exact hXi' (hW.mem_of_pow_mem _ h)
    · exact hGW h
  exact ⟨i, l, k, k', hXi', hXl, N, _, hG3 hF, hGv, hGW⟩

end

end GroundTheory.Heights₂.Heights.Inter
