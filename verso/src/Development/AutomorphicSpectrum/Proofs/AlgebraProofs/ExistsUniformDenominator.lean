import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.FlagMinor

namespace GlobalTheory.CompanionTheory.Ar.Num.Reflexive

open GlobalTheory.CompanionTheory.Ar.Num

variable {o Ω : Type*} [CommRing o] [Field Ω] [Algebra o Ω] {E : Type*} [AddCommGroup E] [Module Ω E]

/- English proof (translation)
Set `I : Ideal R` to `{ carrier := {a | (a : Ω) • v ∈ L} add_mem' := fun {a b} ha hb => by`. Simplify using `only [Set.mem_ofPred_eq, AddMemClass.coe_add, add_smul] at *`. Conclude with `L.add_mem ha hb`. Use the proof step `zero_mem' := by simp`. Use the proof step `smul_mem' := fun a b hb => by`.

Simplify using `only [Set.mem_ofPred_eq, smul_eq_mul, MulMemClass.coe_mul, mul_smul] at *`. Conclude with `hL _ a.2 _ hb }`. Establish `hrad : ∀ l, (⟨f l, hf l⟩ : R) ∈ I.radical` using `fun l => by`. Take `⟨n, hn⟩` from `hv l`. Conclude with `⟨n, by simpa [I] using hn⟩`.

Establish `hone : (1 : R) ∈ I.radical`. Establish `: (1 : R) = ∑ l, (⟨c l, hc l⟩ : R) * ⟨f l, hf l⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[h1]`. Rewrite using `[this]`.

Conclude with `Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hrad l)`. Take `⟨n, hn⟩` from `hone`. Simplify `hn` using `[I]`.
-/
theorem mem_of_locally_mem (R : Subalgebra o Ω) (L : AddSubgroup E)
    (hL : ∀ a ∈ R, ∀ e ∈ L, a • e ∈ L) {k : ℕ} (f c : Fin k → Ω) (hf : ∀ l, f l ∈ R)
    (hc : ∀ l, c l ∈ R) (h1 : ∑ l, c l * f l = 1) (v : E) (hv : ∀ l, ∃ n : ℕ, f l ^ n • v ∈ L) :
    v ∈ L := by
  let I : Ideal R :=
    { carrier := {a | (a : Ω) • v ∈ L}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, AddMemClass.coe_add, add_smul] at *
        exact L.add_mem ha hb
      zero_mem' := by simp
      smul_mem' := fun a b hb => by
        simp only [Set.mem_ofPred_eq, smul_eq_mul, MulMemClass.coe_mul, mul_smul] at *
        exact hL _ a.2 _ hb }
  have hrad : ∀ l, (⟨f l, hf l⟩ : R) ∈ I.radical := fun l => by
    obtain ⟨n, hn⟩ := hv l
    exact ⟨n, by simpa [I] using hn⟩
  have hone : (1 : R) ∈ I.radical := by
    have : (1 : R) = ∑ l, (⟨c l, hc l⟩ : R) * ⟨f l, hf l⟩ := by
      apply Subtype.ext
      simp [h1]
    rw [this]
    exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hrad l)
  obtain ⟨n, hn⟩ := hone
  simpa [I] using hn

/- English proof (translation)
Use `Fintype.ofFinite ι` as an intermediate fact. Use `choose n hn using hx`. Use `⟨∑ i, n i, fun i => ?_⟩` and prove the remaining obligations. Take `⟨d, hd⟩` from `Nat.exists_eq_add_of_le' (Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))`. Rewrite using `[hd, pow_add, mul_smul]`.

Conclude with `hL _ (R.pow_mem hg d) _ (hn i)`.
-/
theorem exists_uniform_pow (R : Subalgebra o Ω) (L : AddSubgroup E)
    (hL : ∀ a ∈ R, ∀ e ∈ L, a • e ∈ L) {ι : Type*} [Finite ι] (g : Ω) (hg : g ∈ R) (x : ι → E)
    (hx : ∀ i, ∃ n : ℕ, g ^ n • x i ∈ L) : ∃ n : ℕ, ∀ i, g ^ n • x i ∈ L := by
  classical
  have := Fintype.ofFinite ι
  choose n hn using hx
  refine ⟨∑ i, n i, fun i => ?_⟩
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le'
    (Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
  rw [hd, pow_add, mul_smul]
  exact hL _ (R.pow_mem hg d) _ (hn i)

/- English proof (translation)
Take `⟨hL, k, f, c, hf, hc, h1, hb⟩` from `h`. Use `choose b _ _ hb using hb`. Set `R' : AddSubgroup Ω` to `R.toSubring.toAddSubgroup`. Establish `hR' : ∀ a ∈ R, ∀ e ∈ R', a • e ∈ R'` using `fun a ha e he => R.mul_mem ha he`. Establish `hbL : ∀ j q, ∃ n : ℕ, f j ^ n • b j q ∈ L` using `fun j q => by`.

Use `(hb j (b j q)).2 ⟨Pi.single q 1, fun q' => ⟨0, ?_⟩, ?_⟩` and prove the remaining obligations. Distinguish the cases in `hq : q' = q`. Substitute `hq` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hq]`.

Simplify using `[Pi.single_apply]`. Use `choose N hN using hbL`. Take `⟨m, hm⟩` from `exists_uniform_pow R R' hR' g hg (fun p : Fin k × Fin r => ψ (f p.1 ^ N p.1 p.2 • b p.1 p.2)) (fun p => hψ _ (hN p.1 p.2))`. Use `⟨m, fun e he => ?_⟩` and prove the remaining obligations. Use `mem_of_locally_mem R R' hR' f c hf hc h1 _ fun j => ?_` and prove the remaining obligations.

Take `⟨a, ha, rfl⟩` from `(hb j e).1 ⟨0, by simpa using he⟩`. Establish `key : ∀ q, ∃ n : ℕ, f j ^ n • (g ^ m * (a q * ψ (b j q))) ∈ R'` using `fun q => by`. Take `⟨n, hn⟩` from `ha q`. Use `⟨n + N j q, ?_⟩` and prove the remaining obligations. Establish `h2 : g ^ m * ψ (f j ^ N j q • b j q) ∈ R` using `hm (j, q)`.

Establish `h3` using `R.mul_mem hn h2`. Establish `h4 : f j ^ (n + N j q) • (g ^ m * (a q * ψ (b j q))) = f j ^ n * a q * (g ^ m * ψ (f j ^ N j q • b j q))`. Simplify using `only [map_smul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h4]`.

Conclude with `h3`. Take `⟨n, hn⟩` from `exists_uniform_pow R R' hR' (f j) (hf j) _ key`. Use `⟨n, ?_⟩` and prove the remaining obligations. Establish `h5 : f j ^ n • (g ^ m * ψ (∑ q, a q • b j q)) = ∑ q, f j ^ n • (g ^ m * (a q * ψ (b j q)))`. Simplify using `only [map_sum, map_smul, smul_eq_mul, Finset.mul_sum]`.

Rewrite using `[h5]`. Conclude with `R'.sum_mem fun q _ => hn q`.
-/
theorem exists_uniform_denominator (R : Subalgebra o Ω) (r : ℕ) (L : AddSubgroup E)
    (h : LocFree R r L) (g : Ω) (hg : g ∈ R) (ψ : Module.Dual Ω E)
    (hψ : ∀ e ∈ L, ∃ n : ℕ, g ^ n * ψ e ∈ R) : ∃ m : ℕ, ∀ e ∈ L, g ^ m * ψ e ∈ R := by
  classical
  obtain ⟨hL, k, f, c, hf, hc, h1, hb⟩ := h
  choose b _ _ hb using hb
  let R' : AddSubgroup Ω := R.toSubring.toAddSubgroup
  have hR' : ∀ a ∈ R, ∀ e ∈ R', a • e ∈ R' := fun a ha e he => R.mul_mem ha he
  have hbL : ∀ j q, ∃ n : ℕ, f j ^ n • b j q ∈ L := fun j q => by
    refine (hb j (b j q)).2 ⟨Pi.single q 1, fun q' => ⟨0, ?_⟩, ?_⟩
    · by_cases hq : q' = q
      · subst hq; simp
      · simp [hq]
    · simp [Pi.single_apply]
  choose N hN using hbL
  obtain ⟨m, hm⟩ := exists_uniform_pow R R' hR' g hg
    (fun p : Fin k × Fin r => ψ (f p.1 ^ N p.1 p.2 • b p.1 p.2)) (fun p => hψ _ (hN p.1 p.2))
  refine ⟨m, fun e he => ?_⟩
  refine mem_of_locally_mem R R' hR' f c hf hc h1 _ fun j => ?_
  obtain ⟨a, ha, rfl⟩ := (hb j e).1 ⟨0, by simpa using he⟩
  have key : ∀ q, ∃ n : ℕ, f j ^ n • (g ^ m * (a q * ψ (b j q))) ∈ R' := fun q => by
    obtain ⟨n, hn⟩ := ha q
    refine ⟨n + N j q, ?_⟩
    have h2 : g ^ m * ψ (f j ^ N j q • b j q) ∈ R := hm (j, q)
    have h3 := R.mul_mem hn h2
    have h4 : f j ^ (n + N j q) • (g ^ m * (a q * ψ (b j q)))
        = f j ^ n * a q * (g ^ m * ψ (f j ^ N j q • b j q)) := by
      simp only [map_smul, smul_eq_mul]; ring
    rw [h4]; exact h3
  obtain ⟨n, hn⟩ := exists_uniform_pow R R' hR' (f j) (hf j) _ key
  refine ⟨n, ?_⟩
  have h5 : f j ^ n • (g ^ m * ψ (∑ q, a q • b j q))
      = ∑ q, f j ^ n • (g ^ m * (a q * ψ (b j q))) := by
    simp only [map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
  rw [h5]
  exact R'.sum_mem fun q _ => hn q

/- English proof (translation)
Introduce `o Ω _ _ _ R E _ _ r L h v hv`. Establish `h'` using `h`. Take `⟨hL, k, f, c, hf, hc, h1, hb⟩` from `h'`. Use `mem_of_locally_mem R L hL f c hf hc h1 v fun l => ?_` and prove the remaining obligations. Take `⟨b, hli, hsp, hb⟩` from `hb l`.

Set `B : Module.Basis (Fin r) Ω E` to `Module.Basis.mk hli hsp.ge`. Establish `hB : ∀ q, B q = b q` using `fun q => Module.Basis.mk_apply _ _ q`. Use `(hb v).2 ⟨fun q => B.coord q v, fun q => ?_, ?_⟩` and prove the remaining obligations. Take `⟨m, hm⟩` from `exists_uniform_denominator R r L h (f l) (hf l) (B.coord q) fun e he => by`. Take `⟨a, ha, rfl⟩` from `(hb e).1 ⟨0, by simpa using he⟩`.

Establish `: B.coord q (∑ q, a q • b q) = a q`. Simplify using `only [← hB, Module.Basis.coord_apply]`. Conclude with `congrFun (B.repr_sum_self a) q`. Rewrite using `[this]`. Conclude with `ha q`.

Conclude with `⟨m, by simpa using hv (f l ^ m • B.coord q) (by simpa using hm)⟩`. Simplify using `only [← hB, Module.Basis.coord_apply]`. Conclude with `(B.sum_repr v).symm`.
-/
theorem locFree_reflexive : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) {E : Type} [AddCommGroup E] [Module Ω E] (r : ℕ) (L : AddSubgroup E), LocFree R r L → ∀ v : E, (∀ ψ : Module.Dual Ω E, (∀ e ∈ L, ψ e ∈ R) → ψ v ∈ R) → v ∈ L := by
  intro o Ω _ _ _ R E _ _ r L h v hv
  have h' := h
  obtain ⟨hL, k, f, c, hf, hc, h1, hb⟩ := h'
  refine mem_of_locally_mem R L hL f c hf hc h1 v fun l => ?_
  obtain ⟨b, hli, hsp, hb⟩ := hb l
  let B : Module.Basis (Fin r) Ω E := Module.Basis.mk hli hsp.ge
  have hB : ∀ q, B q = b q := fun q => Module.Basis.mk_apply _ _ q
  refine (hb v).2 ⟨fun q => B.coord q v, fun q => ?_, ?_⟩
  · obtain ⟨m, hm⟩ := exists_uniform_denominator R r L h (f l) (hf l) (B.coord q) fun e he => by
      obtain ⟨a, ha, rfl⟩ := (hb e).1 ⟨0, by simpa using he⟩
      have : B.coord q (∑ q, a q • b q) = a q := by
        simp only [← hB, Module.Basis.coord_apply]
        exact congrFun (B.repr_sum_self a) q
      rw [this]; exact ha q
    exact ⟨m, by simpa using hv (f l ^ m • B.coord q) (by simpa using hm)⟩
  · simp only [← hB, Module.Basis.coord_apply]
    exact (B.sum_repr v).symm

end GlobalTheory.CompanionTheory.Ar.Num.Reflexive
