import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsHeisTrivial
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PerfectPairingQuotients
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumEqZeroAddUnits
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AdjacentSelfDualLatticesIndexSimple
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumOpTransversal

open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil

open Classical in
open scoped BigOperators in
/- English proof (translation)
Use `ext`. Simplify using the standard rewrite rules.
-/
private lemma submodule_toAddSubgroup_inf {R X : Type} [CommRing R] [AddCommGroup X] [Module R X]
    (A B : Submodule R X) : (A ⊓ B).toAddSubgroup = A.toAddSubgroup ⊓ B.toAddSubgroup := by
  ext; simp

open Classical in
open scoped BigOperators in

/- English proof (translation)
Introduce `R X M _ _ _ _ _ σ w γ W hW lam hlam A B C hA hB hC hAdj hAC hinf v hv`. Establish `hA' : ∀ y, y ∈ A ↔ ∀ a ∈ A, γ y a = 1` using `hA`. Establish `hB' : ∀ y, y ∈ B ↔ ∀ b ∈ B, γ y b = 1` using `hB`. Establish `hC' : ∀ y, y ∈ C ↔ ∀ c ∈ C, γ y c = 1` using `hC`. Establish `hv' : ∀ a ∈ A, W a v = v` using `hv`.

Establish `hlam' : (∀ n : ℕ, n ≠ 0 → lam n ≠ 0) ∧ ∀ P : Ideal R, P.IsMaximal → Finite (R ⧸ P) → lam (Nat.card (R ⧸ P)) ^ 2 = (Nat.card (R ⧸ P) : ℂ) ∧ ((∀ r ∈ P, σ r ∈ P) → lam (Nat.card (R ⧸ P)) = -(Real.sqrt (Nat.card (R ⧸ P)) : ℂ) ∧ ∃ r, σ r - r ∉ P)` using `hlam`. Take `⟨x, hx, P, hP, hfin, hxP, hBle⟩ : ∃ x ∈ B, ∃ P : Ideal R, P.IsMaximal ∧ Finite (R ⧸ P) ∧ (∀ r : R, r • x ∈ A ↔ r ∈ P) ∧ B ≤ (A ⊓ B) ⊔ Submodule.span R {x}` from `hAdj`. Take `⟨hAB, -, hrep, -, -⟩` from `_root_.GlobalTheory.FinWeil.adjacent_selfDual_simple hW A B hA hB x hx P hP hfin hxP hBle`. Use `haveI := Fintype.ofFinite (R ⧸ P)`. Establish `hN : Nat.card (R ⧸ P) ≠ 0` using `Nat.card_pos.ne'`.

Establish `hu : _root_.GlobalTheory.FinWeil.sumOp W A B v = ∑ q : R ⧸ P, W (Quotient.out q • x) v` using `(_root_.GlobalTheory.FinWeil.sumOp_eq_sum_transversal hW A B hB v hv (R ⧸ P) (fun q => Quotient.out q • x) (fun q => B.smul_mem _ hx) hrep).1`. Establish `huB : _root_.GlobalTheory.FinWeil.Fixes W B (_root_.GlobalTheory.FinWeil.sumOp W A B v)` using `((_root_.GlobalTheory.FinWeil.sumOp_transversal hW A B hB).2.1 (hAB ▸ hN)).2.1 v hv`. Take `⟨n, f, hfC, hfrep⟩` from `_root_.GlobalTheory.FinWeil.exists_transversal_of_idx_ne_zero A C hAC`. Establish `hfrepB : ∀ c ∈ C, ∃! i, c - f i ∈ B`. Introduce `c hc`.

Establish `key : ∀ i, c - f i ∈ A ↔ c - f i ∈ B` using `fun i => by`. Establish `hm : c - f i ∈ C` using `C.sub_mem hc (hfC i)`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h' : c - f i ∈ A ⊓ C` using `Submodule.mem_inf.2 ⟨h, hm⟩`.

Rewrite `h'` using `[hinf]`. Conclude with `(Submodule.mem_inf.1 h').1`. Introduce `h`. Establish `h' : c - f i ∈ B ⊓ C` using `Submodule.mem_inf.2 ⟨h, hm⟩`. Rewrite `h'` using `[← hinf]`.

Conclude with `(Submodule.mem_inf.1 h').1`. Simplify `hfrep c hc` using `only [key]`. Establish `hBC` using `(_root_.GlobalTheory.FinWeil.sumOp_eq_sum_transversal hW B C hC _ huB (Fin n) f hfC hfrepB).1`. Establish `hACsum` using `(_root_.GlobalTheory.FinWeil.sumOp_eq_sum_transversal hW A C hC v hv (Fin n) f hfC hfrep).1`. Establish `hSfix : ∀ c ∈ C, W c (_root_.GlobalTheory.FinWeil.sumOp W A C v) = _root_.GlobalTheory.FinWeil.sumOp W A C v` using `((_root_.GlobalTheory.FinWeil.sumOp_transversal hW A C hC).2.1 hAC).2.1 v hv`.

Establish `hmemE : ∀ y, y ∈ (A ⊓ C).toAddSubgroup ↔ y ∈ A ∧ y ∈ C` using `fun y => by`. Simplify using `only [Submodule.mem_toAddSubgroup, Submodule.mem_inf]`. Establish `hEC : (A ⊓ C).toAddSubgroup.relIndex C.toAddSubgroup ≠ 0`. Rewrite using `[submodule_toAddSubgroup_inf, AddSubgroup.inf_relIndex_right]`. Conclude with `hAC`.

Establish `hEA` using `(_root_.GlobalTheory.FinWeil.perfect_pairing_quotients hW (A ⊓ C).toAddSubgroup A.toAddSubgroup (A ⊓ C).toAddSubgroup C.toAddSubgroup (fun a ha => by`. Simplify using `only [Submodule.mem_toAddSubgroup] at ha`. Rewrite using `[hmemE, hC' a]`. Conclude with `⟨fun h => h.2, fun h => ⟨ha, h⟩⟩)`. Use the proof step `(fun t ht => by`.

Simplify using `only [Submodule.mem_toAddSubgroup] at ht`. Rewrite using `[hmemE, hA' t]`. Conclude with `⟨fun h a ha => hW.swap_eq_one (h.1 a ha), fun h => ⟨fun a ha => hW.swap_eq_one (h a ha), ht⟩⟩)`. Use the proof step `hEC).1`. Establish `hdual` using `(_root_.GlobalTheory.FinWeil.perfect_pairing_quotients hW (A ⊓ C).toAddSubgroup C.toAddSubgroup (A ⊓ C).toAddSubgroup A.toAddSubgroup (fun c hc => by`.

Simplify using `only [Submodule.mem_toAddSubgroup] at hc`. Rewrite using `[hmemE, hA' c]`. Conclude with `⟨fun h => h.1, fun h => ⟨h, hc⟩⟩)`. Use the proof step `(fun t ht => by`. Simplify using `only [Submodule.mem_toAddSubgroup] at ht`.

Rewrite using `[hmemE, hC' t]`. Conclude with `⟨fun h c hc => hW.swap_eq_one (h.2 c hc), fun h => ⟨ht, fun c hc => hW.swap_eq_one (h c hc)⟩⟩)`. Use the proof step `(hEA ▸ hEC)).2.1`. Take `⟨a, ha, hxa⟩` from `hdual x (fun c _ hcE => by`. Establish `hcBC : c ∈ B ⊓ C`.

Rewrite using `[← hinf]`. Conclude with `Submodule.mem_inf.2 ((hmemE c).1 hcE)`. Conclude with `hW.iso hB (Submodule.mem_inf.1 hcBC).1 hx)`. Simplify using `only [Submodule.mem_toAddSubgroup] at ha`. Establish `hc₀ : x - a ∈ C`.

Rewrite using `[hC']`. Introduce `c hc`. Apply `hW.swap_eq_one` to reduce the goal to its premises. Rewrite using `[sub_eq_add_neg, hW.add_right, hW.neg_right, hxa c hc, mul_inv_cancel₀ (hW.ne_zero c a)]`. Take `⟨c₀, hc₀C, hxac⟩ : ∃ c₀ ∈ C, x = a + c₀` from `⟨x - a, hc₀, by abel⟩`.

Take `⟨χ, hχ⟩ : ∃ χ : R → ℂ, ∀ t, χ t = γ a (t • c₀)` from `⟨fun t => γ a (t • c₀), fun _ => rfl⟩`. Establish `hχne : ∀ t, χ t ≠ 0` using `fun t => by rw [hχ]; exact hW.ne_zero _ _`. Establish `hχadd : ∀ s t, χ (s + t) = χ s * χ t` using `fun s t => by`. Rewrite using `[hχ, hχ, hχ, add_smul, hW.add_right]`. Establish `hχ0 : χ 0 = 1` using `by rw [hχ, zero_smul]; exact hW.zero_right a`.

Establish `hχx : ∀ t, χ t = γ a (t • x)` using `fun t => by`. Rewrite using `[hχ, hxac, smul_add, hW.add_right, hW.iso hA ha (A.smul_mem t ha), one_mul]`. Establish `hχP : ∀ r ∈ P, χ r = 1` using `fun r hr => by`. Rewrite using `[hχx]`. Conclude with `hW.iso hA ha ((hxP r).2 hr)`.

Establish `hχσ : ∀ t, χ (σ t) = χ t` using `fun t => by`. Establish `h1 : γ (t • a) c₀ * γ (t • c₀) a = 1`. Establish `h0` using `hW.iso hB (B.smul_mem t hx) hx`. Rewrite `h0` using `[hxac, smul_add, hW.add_left, hW.add_right, hW.add_right, hW.iso hA (A.smul_mem t ha) ha, hW.iso hC (C.smul_mem t hc₀C) hc₀C]`. Simplify `h0` using `only [one_mul, mul_one]`.

Rewrite `h1` using `[hW.swap a (t • c₀), ← hχ]`. Rewrite using `[hχ, ← hW.adj t a c₀]`. Conclude with `(mul_inv_eq_one₀ (hχne t)).1 h1`. Establish `hχnt : ∃ t, χ t ≠ 1`. Assume the negation of the conclusion as `hcon`.

Use `push_neg at hcon`. Establish `haB : a ∈ B`. Rewrite using `[hB']`. Introduce `b hb`. Take `⟨d, hd, y, hy, rfl⟩` from `Submodule.mem_sup.1 (hBle hb)`.

Take `⟨r, rfl⟩` from `Submodule.mem_span_singleton.1 hy`. Rewrite using `[hW.add_right, hW.iso hA ha (Submodule.mem_inf.1 hd).1, ← hχx, hcon, one_mul]`. Establish `hc₀A : c₀ ∈ A`. Establish `h1 : c₀ ∈ B ⊓ C`. Use `Submodule.mem_inf.2 ⟨?_, hc₀C⟩` and prove the remaining obligations.

Establish `h2` using `B.sub_mem hx haB`. Rewrite `h2` using `[hxac, add_sub_cancel_left]`. Then use the resulting hypothesis. Rewrite `h1` using `[← hinf]`. Conclude with `(Submodule.mem_inf.1 h1).1`. Establish `h3 : (1 : R) • x ∈ A`.

Rewrite using `[one_smul, hxac]`. Conclude with `A.add_mem ha hc₀A`. Conclude with `hP.ne_top ((Ideal.eq_top_iff_one P).2 ((hxP 1).1 h3))`. Establish `hσP : ∀ r ∈ P, σ r ∈ P`. Introduce `r hr`.

Assume the negation of the conclusion as `hσr`. Take `⟨s, i, hi, hsi⟩` from `hP.exists_inv hσr`. Take `⟨t, ht⟩` from `hχnt`. Apply `ht` to reduce the goal to its premises. Establish `h1 : t = t * i + σ (r * σ (t * s))`.

Rewrite using `[map_mul, hW.sg_sg]`. Take the linear combination `(-t) * hsi`. Rewrite using `[h1, hχadd, hχP _ (P.mul_mem_left t hi), hχσ, hχP _ (P.mul_mem_right _ hr), one_mul]`. Establish `hterm : ∀ s : R, W (s • x) v = χ (w * s * σ s) • W (s • c₀) v` using `fun s => by`. Establish `hcomp` using `hW.comp (s • c₀) (s • a) v`.

Rewrite `hcomp` using `[hv' _ (A.smul_mem s ha), ← smul_add, add_comm c₀ a, ← hxac]`. Establish `e : γ (w • s • c₀) (s • a) = (χ (w * s * σ s))⁻¹`. Rewrite using `[hW.swap (s • a) (w • s • c₀), hW.adj s a, smul_smul, smul_smul, hχ, show σ s * w * s = w * s * σ s by ring]`. Rewrite using `[hcomp, e, smul_smul, mul_inv_cancel₀ (hχne _), one_smul]`. Establish `hshift : ∀ c ∈ C, ∑ i, W (f i) (W c v) = _root_.GlobalTheory.FinWeil.sumOp W A C v`.

Introduce `c hc`. Establish `h1 : ∀ i, W (f i) (W c v) = W c (W (f i) v)` using `fun i => by`. Rewrite using `[hW.comm, hW.iso hC (hfC i) hc, one_smul]`. Rewrite using `[Finset.sum_congr rfl (fun i _ => h1 i), ← map_sum, ← hACsum]`. Conclude with `hSfix c hc`.

Establish `hstep : ∀ i, W (f i) (∑ q : R ⧸ P, W (Quotient.out q • x) v) = ∑ q : R ⧸ P, χ (w * Quotient.out q * σ (Quotient.out q)) • W (f i) (W (Quotient.out q • c₀) v)` using `fun i => by`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl (fun q _ => ?_)` and prove the remaining obligations. Rewrite using `[hterm, map_smul]`. Establish `hstep' : ∀ q : R ⧸ P, ∑ i, χ (w * Quotient.out q * σ (Quotient.out q)) • W (f i) (W (Quotient.out q • c₀) v) = χ (w * Quotient.out q * σ (Quotient.out q)) • _root_.GlobalTheory.FinWeil.sumOp W A C v` using `fun q => by rw [← Finset.smul_sum, hshift _ (C.smul_mem _ hc₀C)]`.

Rewrite using `[hBC, hu, Finset.sum_congr rfl (fun i _ => hstep i), Finset.sum_comm, Finset.sum_congr rfl (fun q _ => hstep' q), ← Finset.sum_smul]`. Use `congr 1`. Rewrite using `[← finsum_eq_sum_of_fintype, _root_.GlobalTheory.NormFormGauss.gauss_quotient σ w hW.sg_sg hW.w_add P hP hfin hσP ((hlam'.2 P hP hfin).2 hσP).2 χ hχadd hχ0 hχP hχσ hχnt, hAB, ((hlam'.2 P hP hfin).2 hσP).1]`.
-/
theorem _root_.GlobalTheory.FinWeil.sumOp_comp_of_adj_of_inf_eq : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, _root_.GlobalTheory.FinWeil.IsHeis σ w γ W → ∀ lam : ℕ →* ℂ, _root_.GlobalTheory.FinWeil.GoodNorm σ lam → ∀ (A B C : Submodule R X), _root_.GlobalTheory.FinWeil.SelfDual γ A → _root_.GlobalTheory.FinWeil.SelfDual γ B → _root_.GlobalTheory.FinWeil.SelfDual γ C → _root_.GlobalTheory.FinWeil.Adj A B → _root_.GlobalTheory.FinWeil.idx A C ≠ 0 → A ⊓ C = B ⊓ C → ∀ v, _root_.GlobalTheory.FinWeil.Fixes W A v → _root_.GlobalTheory.FinWeil.sumOp W B C (_root_.GlobalTheory.FinWeil.sumOp W A B v) = lam (_root_.GlobalTheory.FinWeil.idx A B) • _root_.GlobalTheory.FinWeil.sumOp W A C v := by
  intro R X M _ _ _ _ _ σ w γ W hW lam hlam A B C hA hB hC hAdj hAC hinf v hv
  have hA' : ∀ y, y ∈ A ↔ ∀ a ∈ A, γ y a = 1 := hA
  have hB' : ∀ y, y ∈ B ↔ ∀ b ∈ B, γ y b = 1 := hB
  have hC' : ∀ y, y ∈ C ↔ ∀ c ∈ C, γ y c = 1 := hC
  have hv' : ∀ a ∈ A, W a v = v := hv
  have hlam' : (∀ n : ℕ, n ≠ 0 → lam n ≠ 0) ∧ ∀ P : Ideal R, P.IsMaximal → Finite (R ⧸ P) →
      lam (Nat.card (R ⧸ P)) ^ 2 = (Nat.card (R ⧸ P) : ℂ) ∧ ((∀ r ∈ P, σ r ∈ P) →
        lam (Nat.card (R ⧸ P)) = -(Real.sqrt (Nat.card (R ⧸ P)) : ℂ) ∧ ∃ r, σ r - r ∉ P) := hlam
  obtain ⟨x, hx, P, hP, hfin, hxP, hBle⟩ : ∃ x ∈ B, ∃ P : Ideal R, P.IsMaximal ∧ Finite (R ⧸ P) ∧
      (∀ r : R, r • x ∈ A ↔ r ∈ P) ∧ B ≤ (A ⊓ B) ⊔ Submodule.span R {x} := hAdj
  obtain ⟨hAB, -, hrep, -, -⟩ :=
    _root_.GlobalTheory.FinWeil.adjacent_selfDual_simple hW A B hA hB x hx P hP hfin hxP hBle
  haveI := Fintype.ofFinite (R ⧸ P)
  have hN : Nat.card (R ⧸ P) ≠ 0 := Nat.card_pos.ne'
  have hu : _root_.GlobalTheory.FinWeil.sumOp W A B v = ∑ q : R ⧸ P, W (Quotient.out q • x) v :=
    (_root_.GlobalTheory.FinWeil.sumOp_eq_sum_transversal hW A B hB v hv (R ⧸ P) (fun q => Quotient.out q • x)
      (fun q => B.smul_mem _ hx) hrep).1
  have huB : _root_.GlobalTheory.FinWeil.Fixes W B (_root_.GlobalTheory.FinWeil.sumOp W A B v) :=
    ((_root_.GlobalTheory.FinWeil.sumOp_transversal hW A B hB).2.1 (hAB ▸ hN)).2.1 v hv
  obtain ⟨n, f, hfC, hfrep⟩ := _root_.GlobalTheory.FinWeil.exists_transversal_of_idx_ne_zero A C hAC
  have hfrepB : ∀ c ∈ C, ∃! i, c - f i ∈ B := by
    intro c hc
    have key : ∀ i, c - f i ∈ A ↔ c - f i ∈ B := fun i => by
      have hm : c - f i ∈ C := C.sub_mem hc (hfC i)
      constructor
      · intro h
        have h' : c - f i ∈ A ⊓ C := Submodule.mem_inf.2 ⟨h, hm⟩
        rw [hinf] at h'
        exact (Submodule.mem_inf.1 h').1
      · intro h
        have h' : c - f i ∈ B ⊓ C := Submodule.mem_inf.2 ⟨h, hm⟩
        rw [← hinf] at h'
        exact (Submodule.mem_inf.1 h').1
    simpa only [key] using hfrep c hc
  have hBC := (_root_.GlobalTheory.FinWeil.sumOp_eq_sum_transversal hW B C hC _ huB (Fin n) f hfC hfrepB).1
  have hACsum := (_root_.GlobalTheory.FinWeil.sumOp_eq_sum_transversal hW A C hC v hv (Fin n) f hfC hfrep).1
  have hSfix : ∀ c ∈ C, W c (_root_.GlobalTheory.FinWeil.sumOp W A C v) = _root_.GlobalTheory.FinWeil.sumOp W A C v :=
    ((_root_.GlobalTheory.FinWeil.sumOp_transversal hW A C hC).2.1 hAC).2.1 v hv

  have hmemE : ∀ y, y ∈ (A ⊓ C).toAddSubgroup ↔ y ∈ A ∧ y ∈ C := fun y => by
    simp only [Submodule.mem_toAddSubgroup, Submodule.mem_inf]
  have hEC : (A ⊓ C).toAddSubgroup.relIndex C.toAddSubgroup ≠ 0 := by
    rw [submodule_toAddSubgroup_inf, AddSubgroup.inf_relIndex_right]
    exact hAC
  have hEA := (_root_.GlobalTheory.FinWeil.perfect_pairing_quotients hW (A ⊓ C).toAddSubgroup A.toAddSubgroup
    (A ⊓ C).toAddSubgroup C.toAddSubgroup
    (fun a ha => by
      simp only [Submodule.mem_toAddSubgroup] at ha
      rw [hmemE, hC' a]
      exact ⟨fun h => h.2, fun h => ⟨ha, h⟩⟩)
    (fun t ht => by
      simp only [Submodule.mem_toAddSubgroup] at ht
      rw [hmemE, hA' t]
      exact ⟨fun h a ha => hW.swap_eq_one (h.1 a ha),
        fun h => ⟨fun a ha => hW.swap_eq_one (h a ha), ht⟩⟩)
    hEC).1
  have hdual := (_root_.GlobalTheory.FinWeil.perfect_pairing_quotients hW (A ⊓ C).toAddSubgroup C.toAddSubgroup
    (A ⊓ C).toAddSubgroup A.toAddSubgroup
    (fun c hc => by
      simp only [Submodule.mem_toAddSubgroup] at hc
      rw [hmemE, hA' c]
      exact ⟨fun h => h.1, fun h => ⟨h, hc⟩⟩)
    (fun t ht => by
      simp only [Submodule.mem_toAddSubgroup] at ht
      rw [hmemE, hC' t]
      exact ⟨fun h c hc => hW.swap_eq_one (h.2 c hc),
        fun h => ⟨ht, fun c hc => hW.swap_eq_one (h c hc)⟩⟩)
    (hEA ▸ hEC)).2.1

  obtain ⟨a, ha, hxa⟩ := hdual x (fun c _ hcE => by
    have hcBC : c ∈ B ⊓ C := by
      rw [← hinf]
      exact Submodule.mem_inf.2 ((hmemE c).1 hcE)
    exact hW.iso hB (Submodule.mem_inf.1 hcBC).1 hx)
  simp only [Submodule.mem_toAddSubgroup] at ha
  have hc₀ : x - a ∈ C := by
    rw [hC']
    intro c hc
    apply hW.swap_eq_one
    rw [sub_eq_add_neg, hW.add_right, hW.neg_right, hxa c hc,
      mul_inv_cancel₀ (hW.ne_zero c a)]
  obtain ⟨c₀, hc₀C, hxac⟩ : ∃ c₀ ∈ C, x = a + c₀ := ⟨x - a, hc₀, by abel⟩

  obtain ⟨χ, hχ⟩ : ∃ χ : R → ℂ, ∀ t, χ t = γ a (t • c₀) := ⟨fun t => γ a (t • c₀), fun _ => rfl⟩
  have hχne : ∀ t, χ t ≠ 0 := fun t => by rw [hχ]; exact hW.ne_zero _ _
  have hχadd : ∀ s t, χ (s + t) = χ s * χ t := fun s t => by
    rw [hχ, hχ, hχ, add_smul, hW.add_right]
  have hχ0 : χ 0 = 1 := by rw [hχ, zero_smul]; exact hW.zero_right a
  have hχx : ∀ t, χ t = γ a (t • x) := fun t => by
    rw [hχ, hxac, smul_add, hW.add_right,
      hW.iso hA ha (A.smul_mem t ha), one_mul]
  have hχP : ∀ r ∈ P, χ r = 1 := fun r hr => by
    rw [hχx]
    exact hW.iso hA ha ((hxP r).2 hr)
  have hχσ : ∀ t, χ (σ t) = χ t := fun t => by
    have h1 : γ (t • a) c₀ * γ (t • c₀) a = 1 := by
      have h0 := hW.iso hB (B.smul_mem t hx) hx
      rw [hxac, smul_add, hW.add_left, hW.add_right,
        hW.add_right,
        hW.iso hA (A.smul_mem t ha) ha,
        hW.iso hC (C.smul_mem t hc₀C) hc₀C] at h0
      simpa only [one_mul, mul_one] using h0
    rw [hW.swap a (t • c₀), ← hχ] at h1
    rw [hχ, ← hW.adj t a c₀]
    exact (mul_inv_eq_one₀ (hχne t)).1 h1
  have hχnt : ∃ t, χ t ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    have haB : a ∈ B := by
      rw [hB']
      intro b hb
      obtain ⟨d, hd, y, hy, rfl⟩ := Submodule.mem_sup.1 (hBle hb)
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hy
      rw [hW.add_right,
        hW.iso hA ha (Submodule.mem_inf.1 hd).1, ← hχx,
        hcon, one_mul]
    have hc₀A : c₀ ∈ A := by
      have h1 : c₀ ∈ B ⊓ C := by
        refine Submodule.mem_inf.2 ⟨?_, hc₀C⟩
        have h2 := B.sub_mem hx haB
        rwa [hxac, add_sub_cancel_left] at h2
      rw [← hinf] at h1
      exact (Submodule.mem_inf.1 h1).1
    have h3 : (1 : R) • x ∈ A := by
      rw [one_smul, hxac]
      exact A.add_mem ha hc₀A
    exact hP.ne_top ((Ideal.eq_top_iff_one P).2 ((hxP 1).1 h3))
  have hσP : ∀ r ∈ P, σ r ∈ P := by
    intro r hr
    by_contra hσr
    obtain ⟨s, i, hi, hsi⟩ := hP.exists_inv hσr
    obtain ⟨t, ht⟩ := hχnt
    apply ht
    have h1 : t = t * i + σ (r * σ (t * s)) := by
      rw [map_mul, hW.sg_sg]
      linear_combination (-t) * hsi
    rw [h1, hχadd, hχP _ (P.mul_mem_left t hi), hχσ, hχP _ (P.mul_mem_right _ hr), one_mul]

  have hterm : ∀ s : R, W (s • x) v = χ (w * s * σ s) • W (s • c₀) v := fun s => by
    have hcomp := hW.comp (s • c₀) (s • a) v
    rw [hv' _ (A.smul_mem s ha), ← smul_add, add_comm c₀ a, ← hxac] at hcomp
    have e : γ (w • s • c₀) (s • a) = (χ (w * s * σ s))⁻¹ := by
      rw [hW.swap (s • a) (w • s • c₀), hW.adj s a,
        smul_smul, smul_smul, hχ, show σ s * w * s = w * s * σ s by ring]
    rw [hcomp, e, smul_smul, mul_inv_cancel₀ (hχne _), one_smul]

  have hshift : ∀ c ∈ C, ∑ i, W (f i) (W c v) = _root_.GlobalTheory.FinWeil.sumOp W A C v := by
    intro c hc
    have h1 : ∀ i, W (f i) (W c v) = W c (W (f i) v) := fun i => by
      rw [hW.comm,
        hW.iso hC (hfC i) hc, one_smul]
    rw [Finset.sum_congr rfl (fun i _ => h1 i), ← map_sum, ← hACsum]
    exact hSfix c hc
  have hstep : ∀ i, W (f i) (∑ q : R ⧸ P, W (Quotient.out q • x) v) =
      ∑ q : R ⧸ P, χ (w * Quotient.out q * σ (Quotient.out q)) •
        W (f i) (W (Quotient.out q • c₀) v) := fun i => by
    rw [map_sum]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [hterm, map_smul]
  have hstep' : ∀ q : R ⧸ P, ∑ i, χ (w * Quotient.out q * σ (Quotient.out q)) •
      W (f i) (W (Quotient.out q • c₀) v) =
        χ (w * Quotient.out q * σ (Quotient.out q)) • _root_.GlobalTheory.FinWeil.sumOp W A C v :=
    fun q => by rw [← Finset.smul_sum, hshift _ (C.smul_mem _ hc₀C)]
  rw [hBC, hu, Finset.sum_congr rfl (fun i _ => hstep i), Finset.sum_comm,
    Finset.sum_congr rfl (fun q _ => hstep' q), ← Finset.sum_smul]
  congr 1
  rw [← finsum_eq_sum_of_fintype,
    _root_.GlobalTheory.NormFormGauss.gauss_quotient σ w hW.sg_sg hW.w_add P hP hfin hσP
      ((hlam'.2 P hP hfin).2 hσP).2 χ hχadd hχ0 hχP hχσ hχnt,
    hAB, ((hlam'.2 P hP hfin).2 hσP).1]

end GlobalTheory.FinWeil
