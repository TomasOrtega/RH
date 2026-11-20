import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.FlagMinor

namespace GlobalTheory.CompanionTheory.Ar.Num.LocFreeExt

variable {o Ω : Type*} [CommRing o] [Field Ω] [Algebra o Ω]

section One

variable {E : Type*} [AddCommGroup E] [Module Ω E]

def loc (R : Subalgebra o Ω) (f : Ω) (hf : f ∈ R) (L : AddSubgroup E)
    (hL : ∀ a ∈ R, ∀ e ∈ L, a • e ∈ L) : AddSubgroup E where
  carrier := {e | ∃ n : ℕ, f ^ n • e ∈ L}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro x y ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨n + m, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [pow_add, mul_comm, mul_smul]; exact hL _ (R.pow_mem hf _) _ hn
    · rw [pow_add, mul_smul]; exact hL _ (R.pow_mem hf _) _ hm
  neg_mem' := by
    rintro x ⟨n, hn⟩
    exact ⟨n, by rw [smul_neg]; exact L.neg_mem hn⟩

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_loc {R : Subalgebra o Ω} {f : Ω} {hf : f ∈ R} {L : AddSubgroup E}
    {hL : ∀ a ∈ R, ∀ e ∈ L, a • e ∈ L} {e : E} :
    e ∈ loc R f hf L hL ↔ ∃ n : ℕ, f ^ n • e ∈ L := Iff.rfl

/- English proof (translation)
Rewrite using `[← mem_loc (hf := hf) (hL := hL)]`. Use `AddSubgroup.sum_mem _ fun q _ => ?_` and prove the remaining obligations. Take `⟨n, hn⟩` from `ha q`. Take `⟨m, hm⟩` from `hb q`. Use `⟨n + m, ?_⟩` and prove the remaining obligations.

Establish `h` using `hL _ hn _ hm`. Rewrite `h` using `[smul_smul]`. Rewrite using `[smul_smul]`. Use `h using 2` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_mem_loc {R : Subalgebra o Ω} {f : Ω} (hf : f ∈ R) {L : AddSubgroup E}
    (hL : ∀ a ∈ R, ∀ e ∈ L, a • e ∈ L) {r : ℕ} (a : Fin r → Ω) (b : Fin r → E)
    (ha : ∀ q, ∃ n : ℕ, f ^ n * a q ∈ R) (hb : ∀ q, ∃ n : ℕ, f ^ n • b q ∈ L) :
    ∃ n : ℕ, f ^ n • (∑ q, a q • b q) ∈ L := by
  rw [← mem_loc (hf := hf) (hL := hL)]
  refine AddSubgroup.sum_mem _ fun q _ => ?_
  obtain ⟨n, hn⟩ := ha q
  obtain ⟨m, hm⟩ := hb q
  refine ⟨n + m, ?_⟩
  have h := hL _ hn _ hm
  rw [smul_smul] at h
  rw [smul_smul]
  convert h using 2
  ring

def FreeOn (R : Subalgebra o Ω) (f : Ω) (L : AddSubgroup E) {r : ℕ} (b : Fin r → E) : Prop :=
  LinearIndependent Ω b ∧ Submodule.span Ω (Set.range b) = ⊤ ∧
    ∀ e, (∃ n : ℕ, f ^ n • e ∈ L) ↔
      ∃ a : Fin r → Ω, (∀ q, ∃ n : ℕ, f ^ n * a q ∈ R) ∧ e = ∑ q, a q • b q

/- English proof (translation)
Use `(h.2.2 _).2 ⟨Pi.single q 1, fun p => ⟨0, ?_⟩, ?_⟩` and prove the remaining obligations. Distinguish the cases in `hp : p = q`. Substitute `hp` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_eq_of_ne hp]`.

Simplify using `[Pi.single_apply, ite_smul]`.
-/
theorem FreeOn.basis_mem {R : Subalgebra o Ω} {f : Ω} {L : AddSubgroup E} {r : ℕ} {b : Fin r → E}
    (h : FreeOn R f L b) (q : Fin r) : ∃ n : ℕ, f ^ n • b q ∈ L := by
  classical
  refine (h.2.2 _).2 ⟨Pi.single q 1, fun p => ⟨0, ?_⟩, ?_⟩
  · by_cases hp : p = q
    · subst hp; simp
    · simp [Pi.single_eq_of_ne hp]
  · simp [Pi.single_apply, ite_smul]

/- English proof (translation)
Establish `he : e ∈ Submodule.span Ω (Set.range b)` using `h ▸ Submodule.mem_top`. Take `⟨a, ha⟩` from `(Submodule.mem_span_range_iff_exists_fun Ω).1 he`. Conclude with `⟨a, ha.symm⟩`.
-/
theorem exists_coord {r : ℕ} {b : Fin r → E} (h : Submodule.span Ω (Set.range b) = ⊤) (e : E) :
    ∃ a : Fin r → Ω, e = ∑ q, a q • b q := by
  have he : e ∈ Submodule.span Ω (Set.range b) := h ▸ Submodule.mem_top
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun Ω).1 he
  exact ⟨a, ha.symm⟩

/- English proof (translation)
Use `⟨h.1, h.2.1, fun e => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Introduce and unpack `⟨n, hn⟩`. Distinguish the cases in `hg0 : g = 0`. Take `⟨a, ha⟩` from `exists_coord h.2.1 e`. Conclude with `⟨a, fun q => ⟨1, by simp [hg0]⟩, ha⟩`.

Rewrite `hn` using `[mul_pow, mul_smul]`. Take `⟨a, ha, he⟩` from `(h.2.2 _).1 ⟨n, hn⟩`. Use `⟨fun q => (g ^ n)⁻¹ * a q, fun q => ?_, ?_⟩` and prove the remaining obligations. Take `⟨m, hm⟩` from `ha q`. Use `⟨n + m, ?_⟩` and prove the remaining obligations.

Establish `h1` using `R.mul_mem (R.mul_mem (R.pow_mem hf n) (R.pow_mem hg m)) hm`. Use `h1 using 1` and compare the differences between its conclusion and the goal. Establish `: g ^ n ≠ 0` using `pow_ne_zero _ hg0`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [mul_smul]`. Rewrite using `[← Finset.smul_sum, ← he, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hg0), one_smul]`. Introduce and unpack `⟨a, ha, rfl⟩`. Use `sum_mem_loc (R.mul_mem hf hg) hL a b ha fun q => ?_` and prove the remaining obligations. Take `⟨n, hn⟩` from `h.basis_mem q`.

Use `⟨n, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_pow, mul_comm, mul_smul]`. Conclude with `hL _ (R.pow_mem hg _) _ hn`.
-/
theorem FreeOn.mul {R : Subalgebra o Ω} {f g : Ω} (hf : f ∈ R) (hg : g ∈ R) {L : AddSubgroup E}
    (hL : ∀ a ∈ R, ∀ e ∈ L, a • e ∈ L) {r : ℕ} {b : Fin r → E}
    (h : FreeOn R f L b) : FreeOn R (f * g) L b := by
  refine ⟨h.1, h.2.1, fun e => ⟨?_, ?_⟩⟩
  · rintro ⟨n, hn⟩
    by_cases hg0 : g = 0
    · obtain ⟨a, ha⟩ := exists_coord h.2.1 e
      exact ⟨a, fun q => ⟨1, by simp [hg0]⟩, ha⟩
    · rw [mul_pow, mul_smul] at hn
      obtain ⟨a, ha, he⟩ := (h.2.2 _).1 ⟨n, hn⟩
      refine ⟨fun q => (g ^ n)⁻¹ * a q, fun q => ?_, ?_⟩
      · obtain ⟨m, hm⟩ := ha q
        refine ⟨n + m, ?_⟩
        have h1 := R.mul_mem (R.mul_mem (R.pow_mem hf n) (R.pow_mem hg m)) hm
        convert h1 using 1
        have : g ^ n ≠ 0 := pow_ne_zero _ hg0
        field_simp
        ring
      · simp only [mul_smul]
        rw [← Finset.smul_sum, ← he, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hg0), one_smul]
  · rintro ⟨a, ha, rfl⟩
    refine sum_mem_loc (R.mul_mem hf hg) hL a b ha fun q => ?_
    obtain ⟨n, hn⟩ := h.basis_mem q
    refine ⟨n, ?_⟩
    rw [mul_pow, mul_comm, mul_smul]
    exact hL _ (R.pow_mem hg _) _ hn

end One

variable {E E₁ E₂ : Type*} [AddCommGroup E] [Module Ω E] [AddCommGroup E₁] [Module Ω E₁]
  [AddCommGroup E₂] [Module Ω E₂]

/- English proof (translation)
Establish `hlift : ∀ p, ∃ t : E, q t = b₂ p ∧ ∃ n : ℕ, f ^ n • t ∈ L`. Introduce `p`. Distinguish the cases in `hf0 : f = 0`. Take `⟨t, ht⟩` from `hq (b₂ p)`. Conclude with `⟨t, ht, 1, by simp [hf0]⟩`.

Take `⟨n, s, hs, hs'⟩` from `h₂.basis_mem p`. Establish `hs'' : q s = f ^ n • b₂ p` using `hs'`. Use `⟨(f ^ n)⁻¹ • s, ?_, n, ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul, hs'', smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hf0), one_smul]`. Rewrite using `[smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hf0), one_smul]`.

Conclude with `hs`. Use `choose t ht htL using hlift`. Establish `hqi : ∀ x, q (i x) = 0` using `fun x => by`. Establish `: i x ∈ LinearMap.ker q` using `hiq ▸ LinearMap.mem_range_self i x`. Conclude with `this`.

Establish `hsum : ∀ (a₁ : Fin r₁ → Ω) (a₂ : Fin r₂ → Ω), ∑ p, Fin.append a₁ a₂ p • Fin.append (fun p => i (b₁ p)) t p = i (∑ p, a₁ p • b₁ p) + ∑ p, a₂ p • t p`. Introduce `a₁ a₂`. Rewrite using `[Fin.sum_univ_add]`. Simplify using `[map_sum]`. Establish `hker : ∀ (e : E) (a₂ : Fin r₂ → Ω), q e = ∑ p, a₂ p • b₂ p → ∃ x, i x = e - ∑ p, a₂ p • t p`.

Introduce `e a₂ he`. Establish `: e - ∑ p, a₂ p • t p ∈ LinearMap.range i`. Rewrite using `[hiq, LinearMap.mem_ker, map_sub, he]`. Simplify using `[map_sum, ht]`. Conclude with `this`.

Use `⟨Fin.append (fun p => i (b₁ p)) t, ?_, ?_, fun e => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg`. Rewrite `hg` using `[Fin.sum_univ_add]`. Simplify using `only [Fin.append_left, Fin.append_right] at hg`.

Establish `h2 : ∑ p, g (Fin.natAdd r₁ p) • b₂ p = 0`. Use `congrArg q hg` as an intermediate fact. Simplify `this` using `[map_sum, hqi, ht]`. Establish `h2'` using `Fintype.linearIndependent_iff.1 h₂.1 _ h2`. Establish `h1 : ∑ p, g (Fin.castAdd r₂ p) • b₁ p = 0`.

Apply `hi` to reduce the goal to its premises. Simplify `hg` using `[map_sum, h2']`. Establish `h1'` using `Fintype.linearIndependent_iff.1 h₁.1 _ h1`. Introduce `p`. Use `Fin.addCases (fun p => h1' p) (fun p => h2' p) p` and prove the remaining obligations.

Rewrite using `[eq_top_iff]`. Introduce `e _`. Take `⟨a₂, ha₂⟩` from `exists_coord h₂.2.1 (q e)`. Take `⟨x, hx⟩` from `hker e a₂ ha₂`. Take `⟨a₁, ha₁⟩` from `exists_coord h₁.2.1 x`.

Use `(Submodule.mem_span_range_iff_exists_fun Ω).2 ⟨Fin.append a₁ a₂, ?_⟩` and prove the remaining obligations. Rewrite using `[hsum, ← ha₁, hx, sub_add_cancel]`. Introduce and unpack `⟨n, hn⟩`. Take `⟨a₂, ha₂R, ha₂⟩` from `(h₂.2.2 (q e)).1 ⟨n, f ^ n • e, hn, by simp⟩`. Take `⟨x, hx⟩` from `hker e a₂ ha₂`.

Establish `hxL : i x ∈ loc R f hf L hL`. Rewrite using `[hx]`. Conclude with `AddSubgroup.sub_mem _ ⟨n, hn⟩ (sum_mem_loc hf hL a₂ t ha₂R htL)`. Take `⟨m, hm⟩` from `hxL`. Take `⟨a₁, ha₁R, ha₁⟩` from `(h₁.2.2 x).1 ⟨m, by`.

Rewrite using `[AddSubgroup.mem_comap]`. Simplify using `using hm⟩`. Use `⟨Fin.append a₁ a₂, fun p => ?_, ?_⟩` and prove the remaining obligations. Use `Fin.addCases (fun p => ?_) (fun p => ?_) p` and prove the remaining obligations. Simplify using `using ha₁R p`.

Simplify using `using ha₂R p`. Rewrite using `[hsum, ← ha₁, hx, sub_add_cancel]`. Introduce and unpack `⟨a, ha, rfl⟩`. Use `sum_mem_loc hf hL a _ ha fun p => ?_` and prove the remaining obligations. Use `Fin.addCases (fun p => ?_) (fun p => ?_) p` and prove the remaining obligations.

Take `⟨n, hn⟩` from `h₁.basis_mem p`. Rewrite `hn` using `[AddSubgroup.mem_comap]`. Conclude with `⟨n, by simpa using hn⟩`. Simplify using `using htL p`.
-/
theorem freeOn_ext {R : Subalgebra o Ω} {f : Ω} (hf : f ∈ R) (i : E₁ →ₗ[Ω] E) (q : E →ₗ[Ω] E₂)
    (hi : Function.Injective i) (hq : Function.Surjective q)
    (hiq : LinearMap.range i = LinearMap.ker q) {L : AddSubgroup E}
    (hL : ∀ a ∈ R, ∀ e ∈ L, a • e ∈ L) {r₁ r₂ : ℕ} {b₁ : Fin r₁ → E₁} {b₂ : Fin r₂ → E₂}
    (h₁ : FreeOn R f (L.comap i.toAddMonoidHom) b₁) (h₂ : FreeOn R f (L.map q.toAddMonoidHom) b₂) :
    ∃ b : Fin (r₁ + r₂) → E, FreeOn R f L b := by
  have hlift : ∀ p, ∃ t : E, q t = b₂ p ∧ ∃ n : ℕ, f ^ n • t ∈ L := by
    intro p
    by_cases hf0 : f = 0
    · obtain ⟨t, ht⟩ := hq (b₂ p)
      exact ⟨t, ht, 1, by simp [hf0]⟩
    · obtain ⟨n, s, hs, hs'⟩ := h₂.basis_mem p
      have hs'' : q s = f ^ n • b₂ p := hs'
      refine ⟨(f ^ n)⁻¹ • s, ?_, n, ?_⟩
      · rw [map_smul, hs'', smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hf0), one_smul]
      · rw [smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hf0), one_smul]; exact hs
  choose t ht htL using hlift
  have hqi : ∀ x, q (i x) = 0 := fun x => by
    have : i x ∈ LinearMap.ker q := hiq ▸ LinearMap.mem_range_self i x
    exact this
  have hsum : ∀ (a₁ : Fin r₁ → Ω) (a₂ : Fin r₂ → Ω),
      ∑ p, Fin.append a₁ a₂ p • Fin.append (fun p => i (b₁ p)) t p
        = i (∑ p, a₁ p • b₁ p) + ∑ p, a₂ p • t p := by
    intro a₁ a₂
    rw [Fin.sum_univ_add]
    simp [map_sum]
  have hker : ∀ (e : E) (a₂ : Fin r₂ → Ω), q e = ∑ p, a₂ p • b₂ p →
      ∃ x, i x = e - ∑ p, a₂ p • t p := by
    intro e a₂ he
    have : e - ∑ p, a₂ p • t p ∈ LinearMap.range i := by
      rw [hiq, LinearMap.mem_ker, map_sub, he]
      simp [map_sum, ht]
    exact this
  refine ⟨Fin.append (fun p => i (b₁ p)) t, ?_, ?_, fun e => ⟨?_, ?_⟩⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_add] at hg
    simp only [Fin.append_left, Fin.append_right] at hg
    have h2 : ∑ p, g (Fin.natAdd r₁ p) • b₂ p = 0 := by
      have := congrArg q hg
      simpa [map_sum, hqi, ht] using this
    have h2' := Fintype.linearIndependent_iff.1 h₂.1 _ h2
    have h1 : ∑ p, g (Fin.castAdd r₂ p) • b₁ p = 0 := by
      apply hi
      simpa [map_sum, h2'] using hg
    have h1' := Fintype.linearIndependent_iff.1 h₁.1 _ h1
    intro p
    refine Fin.addCases (fun p => h1' p) (fun p => h2' p) p
  · rw [eq_top_iff]
    intro e _
    obtain ⟨a₂, ha₂⟩ := exists_coord h₂.2.1 (q e)
    obtain ⟨x, hx⟩ := hker e a₂ ha₂
    obtain ⟨a₁, ha₁⟩ := exists_coord h₁.2.1 x
    refine (Submodule.mem_span_range_iff_exists_fun Ω).2 ⟨Fin.append a₁ a₂, ?_⟩
    rw [hsum, ← ha₁, hx, sub_add_cancel]
  · rintro ⟨n, hn⟩
    obtain ⟨a₂, ha₂R, ha₂⟩ := (h₂.2.2 (q e)).1 ⟨n, f ^ n • e, hn, by simp⟩
    obtain ⟨x, hx⟩ := hker e a₂ ha₂
    have hxL : i x ∈ loc R f hf L hL := by
      rw [hx]
      exact AddSubgroup.sub_mem _ ⟨n, hn⟩ (sum_mem_loc hf hL a₂ t ha₂R htL)
    obtain ⟨m, hm⟩ := hxL
    obtain ⟨a₁, ha₁R, ha₁⟩ := (h₁.2.2 x).1 ⟨m, by
      rw [AddSubgroup.mem_comap]; simpa using hm⟩
    refine ⟨Fin.append a₁ a₂, fun p => ?_, ?_⟩
    · refine Fin.addCases (fun p => ?_) (fun p => ?_) p
      · simpa using ha₁R p
      · simpa using ha₂R p
    · rw [hsum, ← ha₁, hx, sub_add_cancel]
  · rintro ⟨a, ha, rfl⟩
    refine sum_mem_loc hf hL a _ ha fun p => ?_
    refine Fin.addCases (fun p => ?_) (fun p => ?_) p
    · obtain ⟨n, hn⟩ := h₁.basis_mem p
      rw [AddSubgroup.mem_comap] at hn
      exact ⟨n, by simpa using hn⟩
    · simpa using htL p

/- English proof (translation)
Introduce `o Ω _ _ _ R E E₁ E₂ _ _ _ _ _ _ i q hi hq hiq L r₁ r₂ hL`. Introduce and unpack `⟨hL₁, k₁, f₁, c₁, hf₁, hc₁, hs₁, hb₁⟩ ⟨hL₂, k₂, f₂, c₂, hf₂, hc₂, hs₂, hb₂⟩`. Use `⟨hL, k₁ * k₂, fun l => f₁ (finProdFinEquiv.symm l).1 * f₂ (finProdFinEquiv.symm l).2, fun l => c₁ (finProdFinEquiv.symm l).1 * c₂ (finProdFinEquiv.symm l).2, fun l => R.mul_mem (hf₁ _) (hf₂ _), fun l => R.mul_mem (hc₁ _) (hc₂ _), ?_, fun l => ?_⟩` and prove the remaining obligations. Rewrite using `[Equiv.sum_comp finProdFinEquiv.symm (fun p : Fin k₁ × Fin k₂ => c₁ p.1 * c₂ p.2 * (f₁ p.1 * f₂ p.2)), Fintype.sum_prod_type, ← mul_one (1 : Ω)] conv_rhs => rw [← hs₁]`. Use `enter [2]`.

Rewrite using `[hs₁, ← hs₂]`. Rewrite using `[Finset.sum_mul_sum]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Take `⟨b₁, h₁⟩` from `hb₁ (finProdFinEquiv.symm l).1`.

Take `⟨b₂, h₂⟩` from `hb₂ (finProdFinEquiv.symm l).2`. Establish `h₁'` using `FreeOn.mul (hf₁ _) (hf₂ (finProdFinEquiv.symm l).2) hL₁ h₁`. Establish `h₂'` using `FreeOn.mul (hf₂ _) (hf₁ (finProdFinEquiv.symm l).1) hL₂ h₂`. Rewrite `h₂'` using `[mul_comm]`. Conclude with `freeOn_ext (R.mul_mem (hf₁ _) (hf₂ _)) i q hi hq hiq hL h₁' h₂'`.
-/
theorem main : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) {E E₁ E₂ : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup E₁] [Module Ω E₁] [AddCommGroup E₂] [Module Ω E₂] (i : E₁ →ₗ[Ω] E) (q : E →ₗ[Ω] E₂), Function.Injective i → Function.Surjective q → LinearMap.range i = LinearMap.ker q → ∀ (L : AddSubgroup E) (r₁ r₂ : ℕ), (∀ a ∈ R, ∀ e ∈ L, a • e ∈ L) → LocFree R r₁ (L.comap i.toAddMonoidHom) → LocFree R r₂ (L.map q.toAddMonoidHom) → LocFree R (r₁ + r₂) L := by
  intro o Ω _ _ _ R E E₁ E₂ _ _ _ _ _ _ i q hi hq hiq L r₁ r₂ hL
  rintro ⟨hL₁, k₁, f₁, c₁, hf₁, hc₁, hs₁, hb₁⟩ ⟨hL₂, k₂, f₂, c₂, hf₂, hc₂, hs₂, hb₂⟩
  refine ⟨hL, k₁ * k₂,
    fun l => f₁ (finProdFinEquiv.symm l).1 * f₂ (finProdFinEquiv.symm l).2,
    fun l => c₁ (finProdFinEquiv.symm l).1 * c₂ (finProdFinEquiv.symm l).2,
    fun l => R.mul_mem (hf₁ _) (hf₂ _), fun l => R.mul_mem (hc₁ _) (hc₂ _), ?_, fun l => ?_⟩
  · rw [Equiv.sum_comp finProdFinEquiv.symm
      (fun p : Fin k₁ × Fin k₂ => c₁ p.1 * c₂ p.2 * (f₁ p.1 * f₂ p.2)), Fintype.sum_prod_type,
      ← mul_one (1 : Ω)]
    conv_rhs => rw [← hs₁]; enter [2]; rw [hs₁, ← hs₂]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  · obtain ⟨b₁, h₁⟩ := hb₁ (finProdFinEquiv.symm l).1
    obtain ⟨b₂, h₂⟩ := hb₂ (finProdFinEquiv.symm l).2
    have h₁' := FreeOn.mul (hf₁ _) (hf₂ (finProdFinEquiv.symm l).2) hL₁ h₁
    have h₂' := FreeOn.mul (hf₂ _) (hf₁ (finProdFinEquiv.symm l).1) hL₂ h₂
    rw [mul_comm] at h₂'
    exact freeOn_ext (R.mul_mem (hf₁ _) (hf₂ _)) i q hi hq hiq hL h₁' h₂'

end GlobalTheory.CompanionTheory.Ar.Num.LocFreeExt
