import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntAtNatCast

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.AdT.CosShape

section Gen

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

/- English proof (translation)
Establish `h : ((r : E) ^ k) • x = (r ^ k) • x`. Rewrite using `[← algebraMap_smul E (r ^ k) x]`. Simplify using the standard rewrite rules. Rewrite using `[h]`. Conclude with `S.smul_mem _ hx`.
-/
theorem pow_smul_mem (S : Submodule (𝓞 E) (Sp E n)) (r : 𝓞 E) (k : ℕ) {x : Sp E n} (hx : x ∈ S) :
    ((r : E) ^ k) • x ∈ S := by

  have h : ((r : E) ^ k) • x = (r ^ k) • x := by
    rw [← algebraMap_smul E (r ^ k) x]
    simp
  rw [h]
  exact S.smul_mem _ hx

/- English proof (translation)
Establish `hYY : ∀ y ∈ Y, ∀ y' ∈ Y, (c ^ e)⁻¹ • (F.symm y - F.symm y') ∈ S₀`. Introduce `y hy y' hy'`. Establish `h1` using `hF _ (hY y hy)`. Establish `h2` using `hF _ (hY y' hy')`. Establish `h3 : (c ^ e)⁻¹ • (F.symm y - F.symm y') = F.symm ((c ^ e)⁻¹ • (y - y₀)) - F.symm ((c ^ e)⁻¹ • (y' - y₀))`.

Simplify using `only [LinearEquiv.map_smul, map_sub]`. Rewrite using `[← smul_sub]`. Use `congr 1`. Normalize the expressions using the abelian group laws. Rewrite using `[h3]`.

Conclude with `S₀.sub_mem h1 h2`. Establish `hself : ∀ y ∈ Y, F.symm y ∈ C`. Introduce `y hy`. Conclude with `(hC _).2 ⟨y, hy, by simp⟩`. Establish `hmem : ∀ z ∈ C, ∀ z', z' ∈ C ↔ (c ^ e)⁻¹ • (z' - z) ∈ S₀`.

Introduce `z hz z'`. Take `⟨y₁, hy₁, hz1⟩` from `(hC z).1 hz`. Prove the components needed by the constructor for the conclusion. Introduce `hz'`. Take `⟨y₂, hy₂, hz2⟩` from `(hC z').1 hz'`.

Establish `key` using `S₀.add_mem (S₀.sub_mem hz2 hz1) (hYY y₂ hy₂ y₁ hy₁)`. Use `key using 1` and compare the differences between its conclusion and the goal. Rewrite using `[← smul_sub, ← smul_add]`. Use `congr 1`. Normalize the expressions using the abelian group laws.

Introduce `h`. Use `(hC z').2 ⟨y₁, hy₁, ?_⟩` and prove the remaining obligations. Establish `key` using `S₀.add_mem h hz1`. Use `key using 1` and compare the differences between its conclusion and the goal. Rewrite using `[← smul_add]`.

Use `congr 1`. Normalize the expressions using the abelian group laws. Use `⟨⟨F.symm y₀, hself y₀ hY0⟩, hself, fun z hz => ⟨hmem z hz, ?_⟩⟩` and prove the remaining obligations. Introduce `g g' D hg' hD hle hgz z'`. Take `⟨y₁, hy₁, hz1⟩` from `(hC z).1 hz`.

Establish `hce : c ^ e ≠ 0` using `pow_ne_zero _ hc`. Establish `hx₀ : c ^ e' • z ∈ S₀`. Establish `a1 : c ^ e' • (c ^ e • ((c ^ e)⁻¹ • (z - F.symm y₁))) ∈ S₀` using `hpow _ _ _ (hpow _ _ _ hz1)`. Establish `a2 : c ^ e' • (c ^ e • ((c ^ e)⁻¹ • (F.symm y₁ - F.symm y₀))) ∈ S₀` using `hpow _ _ _ (hpow _ _ _ (hYY y₁ hy₁ y₀ hY0))`. Establish `a3 : F.symm (c ^ e' • y₀) ∈ S₀` using `hF _ hy₀`.

Rewrite `a1`, `a2` using `[smul_inv_smul₀ hce]`. Rewrite `a3` using `[LinearEquiv.map_smul]`. Establish `a4` using `S₀.add_mem (S₀.add_mem a1 a2) a3`. Use `a4 using 1` and compare the differences between its conclusion and the goal. Rewrite using `[← smul_add, ← smul_add]`.

Use `congr 1`. Normalize the expressions using the abelian group laws. Take `⟨k, rfl⟩` from `Nat.exists_eq_add_of_le hle`. Establish `hdiff : (c ^ e)⁻¹ • (g z - g' z) ∈ S₀`. Establish `b1` using `hpow S₀ k _ (hD _ hx₀)`.

Use `b1 using 1` and compare the differences between its conclusion and the goal. Rewrite using `[LinearEquiv.map_smul, LinearEquiv.map_smul, ← smul_sub, smul_smul, smul_smul]`. Use `congr 1`. Rewrite using `[pow_add, pow_add]`. Clear the denominators using the available nonvanishing facts.

Establish `ht : (c ^ e)⁻¹ • (g' z - z) ∈ S₀`. Establish `b2` using `S₀.sub_mem hgz hdiff`. Use `b2 using 1` and compare the differences between its conclusion and the goal. Rewrite using `[← smul_sub]`. Use `congr 1`.

Normalize the expressions using the abelian group laws. Rewrite using `[hmem z hz (g' z'), hmem z hz z']`. Establish `hsplit : (c ^ e)⁻¹ • (g' z' - z) = g' ((c ^ e)⁻¹ • (z' - z)) + (c ^ e)⁻¹ • (g' z - z)`. Rewrite using `[LinearEquiv.map_smul, ← smul_add, map_sub]`. Use `congr 1`.

Normalize the expressions using the abelian group laws. Rewrite using `[hsplit, add_mem_cancel_right ht]`. Conclude with `hg' _`.
-/
theorem core (S₀ L : Submodule (𝓞 E) (Sp E n)) (F : Sp E n ≃ₗ[E] Sp E n) (hF : ∀ w ∈ L, F.symm w ∈ S₀)
    (c : E) (hc : c ≠ 0) (hpow : ∀ (S : Submodule (𝓞 E) (Sp E n)) (k : ℕ) (x : Sp E n), x ∈ S → c ^ k • x ∈ S)
    (Y : Set (Sp E n)) (y₀ : Sp E n) (e e' : ℕ) (hY0 : y₀ ∈ Y) (hY : ∀ y ∈ Y, (c ^ e)⁻¹ • (y - y₀) ∈ L)
    (hy₀ : c ^ e' • y₀ ∈ L) (C : Set (Sp E n)) (hC : ∀ z, z ∈ C ↔ ∃ y ∈ Y, (c ^ e)⁻¹ • (z - F.symm y) ∈ S₀) :
    C.Nonempty ∧ (∀ y ∈ Y, F.symm y ∈ C) ∧ ∀ z ∈ C, (∀ z', z' ∈ C ↔ (c ^ e)⁻¹ • (z' - z) ∈ S₀) ∧
      ∀ (g g' : Sp E n ≃ₗ[E] Sp E n) (D : ℕ), (∀ x, g' x ∈ S₀ ↔ x ∈ S₀) →
        (∀ x ∈ S₀, (c ^ D)⁻¹ • (g x - g' x) ∈ S₀) → e + e' ≤ D →
        (c ^ e)⁻¹ • (g z - z) ∈ S₀ → ∀ z', g' z' ∈ C ↔ z' ∈ C := by

  have hYY : ∀ y ∈ Y, ∀ y' ∈ Y, (c ^ e)⁻¹ • (F.symm y - F.symm y') ∈ S₀ := by
    intro y hy y' hy'
    have h1 := hF _ (hY y hy)
    have h2 := hF _ (hY y' hy')
    have h3 : (c ^ e)⁻¹ • (F.symm y - F.symm y') =
        F.symm ((c ^ e)⁻¹ • (y - y₀)) - F.symm ((c ^ e)⁻¹ • (y' - y₀)) := by
      simp only [LinearEquiv.map_smul, map_sub]
      rw [← smul_sub]
      congr 1
      abel
    rw [h3]
    exact S₀.sub_mem h1 h2
  have hself : ∀ y ∈ Y, F.symm y ∈ C := by
    intro y hy
    exact (hC _).2 ⟨y, hy, by simp⟩

  have hmem : ∀ z ∈ C, ∀ z', z' ∈ C ↔ (c ^ e)⁻¹ • (z' - z) ∈ S₀ := by
    intro z hz z'
    obtain ⟨y₁, hy₁, hz1⟩ := (hC z).1 hz
    constructor
    · intro hz'
      obtain ⟨y₂, hy₂, hz2⟩ := (hC z').1 hz'
      have key := S₀.add_mem (S₀.sub_mem hz2 hz1) (hYY y₂ hy₂ y₁ hy₁)
      convert key using 1
      rw [← smul_sub, ← smul_add]
      congr 1
      abel
    · intro h
      refine (hC z').2 ⟨y₁, hy₁, ?_⟩
      have key := S₀.add_mem h hz1
      convert key using 1
      rw [← smul_add]
      congr 1
      abel
  refine ⟨⟨F.symm y₀, hself y₀ hY0⟩, hself, fun z hz => ⟨hmem z hz, ?_⟩⟩
  intro g g' D hg' hD hle hgz z'
  obtain ⟨y₁, hy₁, hz1⟩ := (hC z).1 hz
  have hce : c ^ e ≠ 0 := pow_ne_zero _ hc

  have hx₀ : c ^ e' • z ∈ S₀ := by
    have a1 : c ^ e' • (c ^ e • ((c ^ e)⁻¹ • (z - F.symm y₁))) ∈ S₀ := hpow _ _ _ (hpow _ _ _ hz1)
    have a2 : c ^ e' • (c ^ e • ((c ^ e)⁻¹ • (F.symm y₁ - F.symm y₀))) ∈ S₀ :=
      hpow _ _ _ (hpow _ _ _ (hYY y₁ hy₁ y₀ hY0))
    have a3 : F.symm (c ^ e' • y₀) ∈ S₀ := hF _ hy₀
    rw [smul_inv_smul₀ hce] at a1 a2
    rw [LinearEquiv.map_smul] at a3
    have a4 := S₀.add_mem (S₀.add_mem a1 a2) a3
    convert a4 using 1
    rw [← smul_add, ← smul_add]
    congr 1
    abel

  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  have hdiff : (c ^ e)⁻¹ • (g z - g' z) ∈ S₀ := by
    have b1 := hpow S₀ k _ (hD _ hx₀)
    convert b1 using 1
    rw [LinearEquiv.map_smul, LinearEquiv.map_smul, ← smul_sub, smul_smul, smul_smul]
    congr 1
    rw [pow_add, pow_add]
    field_simp
  have ht : (c ^ e)⁻¹ • (g' z - z) ∈ S₀ := by
    have b2 := S₀.sub_mem hgz hdiff
    convert b2 using 1
    rw [← smul_sub]
    congr 1
    abel
  rw [hmem z hz (g' z'), hmem z hz z']
  have hsplit : (c ^ e)⁻¹ • (g' z' - z) = g' ((c ^ e)⁻¹ • (z' - z)) + (c ^ e)⁻¹ • (g' z - z) := by
    rw [LinearEquiv.map_smul, ← smul_add, map_sub]
    congr 1
    abel
  rw [hsplit, add_mem_cancel_right ht]
  exact hg' _

end Gen

end GlobalTheory.Mem.Col2.AdT.CosShape

namespace GlobalTheory.Mem.Col2.AdT.CosShape

set_option maxHeartbeats 1600000 in
open Classical in

/- English proof (translation)
Introduce `B X I hI u a i p P`. Use `⟨fun hi => ?_, fun hi => ?_⟩` and prove the remaining obligations. Establish `h0 : p.1.2 = ∅`. Establish `h` using `p.2`. Rewrite `h` using `[ysAt_ys_of_ne (h := hi)]`.

Conclude with `Set.mem_singleton_iff.mp h`. Use extensionality with `z`. Simplify using `[cosetIn, h0]`. Take `⟨y₀, hy₀, hYeq⟩` from `PtAt.mem_ybSet p hi`. Establish `hfr : ∀ x, (frsF I.sel (I.tup a) p.1.1 P) x ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.1.1.deco.1.N ↔ x ∈ stdAt B.fields.E (B.R.N i) P.1`.

Introduce `x`. Simplify using `only [frsF]`. Use `split_ifs with h`. Conclude with `(GlobalTheory.TopStep.liftFr_spec p.1.1.deco.2 ⟨P.1, h⟩).1 x`. Conclude with `p.1.1.2 ⟨P.1, (Finset.mem_union.mp P.2).resolve_left h⟩ x`.

Establish `hF : ∀ w ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.1.1.deco.1.N, (frsF I.sel (I.tup a) p.1.1 P).symm w ∈ stdAt B.fields.E (B.R.N i) P.1`. Introduce `w hw`. Rewrite using `[← hfr, LinearEquiv.apply_symm_apply]`. Conclude with `hw`. Establish `hc : ((qOf P.1 : ℕ) : B.fields.E) ≠ 0`.

Conclude with `(GlobalTheory.GO.ChRoot.qOf_pos P.1).ne'` after adjusting the coercions. Establish `hpow : ∀ (S : Submodule (𝓞 B.fields.E) (Sp B.fields.E (B.R.N i))) (k : ℕ) (x : Sp B.fields.E (B.R.N i)), x ∈ S → ((qOf P.1 : ℕ) : B.fields.E) ^ k • x ∈ S`. Introduce `S k x hx`. Establish `h` using `pow_smul_mem S ((qOf P.1 : ℕ) : 𝓞 B.fields.E) k hx`. Simplify using `using h`.

Establish `hY0 : y₀ ∈ p.1.2`. Rewrite using `[hYeq, Set.mem_setOf_eq, sub_self]`. Conclude with `zero_mem _`. Establish `hY1` using `(mem_locLat _ _ _ _).1 hy₀ P`. Establish `hGL : ∀ g' : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i), g' ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1 → ∀ x, g' x ∈ stdAt B.fields.E (B.R.N i) P.1 ↔ x ∈ stdAt B.fields.E (B.R.N i) P.1`.

Introduce `g' hg'`. Conclude with `hg'`. Distinguish the cases in `hP : P.1 ∈ (B.primes X).vGs`. Establish `hYl : ∀ y ∈ p.1.2, (((qOf P.1 : ℕ) : B.fields.E) ^ 0)⁻¹ • (y - y₀) ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.1.1.deco.1.N`. Introduce `y hy`.

Rewrite `hy` using `[hYeq, Set.mem_setOf_eq]`. Establish `h` using `(mem_locLat _ _ _ _).1 hy P`. Simplify `h` using `[hP]`. Establish `hy₀' : ((qOf P.1 : ℕ) : B.fields.E) ^ 1 • y₀ ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.1.1.deco.1.N`. Simplify `hY1` using `[hP]`.

Establish `hC : ∀ z, z ∈ cosetIn p P ↔ ∃ y ∈ p.1.2, (((qOf P.1 : ℕ) : B.fields.E) ^ 0)⁻¹ • (z - (frsF I.sel (I.tup a) p.1.1 P).symm y) ∈ stdAt B.fields.E (B.R.N i) P.1`. Introduce `z`. Simplify using `only [cosetIn, Set.mem_setOf_eq, if_pos hP]`. Establish `hSC : ∀ x y : Sp B.fields.E (B.R.N i), GlobalTheory.TwU.SameCoset I.sel (I.tup a) (I.cst a) P x y ↔ (((qOf P.1 : ℕ) : B.fields.E) ^ 0)⁻¹ • (x - y) ∈ stdAt B.fields.E (B.R.N i) P.1`. Introduce `x y`.

Rewrite using `[GlobalTheory.GO.ChRoot.mem_stdAt']`. Simplify using `only [GlobalTheory.TwU.SameCoset, if_pos hP, Pi.smul_apply, smul_eq_mul]`. Take `⟨k1, k2, k3⟩` from `core (stdAt B.fields.E (B.R.N i) P.1) (Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.1.1.deco.1.N) (frsF I.sel (I.tup a) p.1.1 P) hF _ hc hpow p.1.2 y₀ 0 1 hY0 hYl hy₀' (cosetIn p P) hC`. Use `⟨k1, k2, fun z hz => ⟨fun z' => ((k3 z hz).1 z').trans (hSC z' z).symm, ?_⟩⟩` and prove the remaining obligations. Introduce `g g' hg' hcong hgz z'`.

Establish `hD1` using `(hI.idx_ok a).depthG P hP`. Conclude with `(k3 z hz).2 g g' _ (hGL g' hg') hcong (by omega) ((hSC _ _).1 hgz) z'`. Establish `hYl : ∀ y ∈ p.1.2, (((qOf P.1 : ℕ) : B.fields.E) ^ (I.cst a).M)⁻¹ • (y - y₀) ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.1.1.deco.1.N`. Introduce `y hy`. Rewrite `hy` using `[hYeq, Set.mem_setOf_eq]`.

Establish `h` using `(mem_locLat _ _ _ _).1 hy P`. Simplify `h` using `[hP]`. Establish `hy₀' : ((qOf P.1 : ℕ) : B.fields.E) ^ (I.cst a).M • y₀ ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.1.1.deco.1.N`. Simplify `hY1` using `[hP]`. Establish `hC : ∀ z, z ∈ cosetIn p P ↔ ∃ y ∈ p.1.2, (((qOf P.1 : ℕ) : B.fields.E) ^ (I.cst a).M)⁻¹ • (z - (frsF I.sel (I.tup a) p.1.1 P).symm y) ∈ stdAt B.fields.E (B.R.N i) P.1`.

Introduce `z`. Simplify using `only [cosetIn, Set.mem_setOf_eq, if_neg hP]`. Establish `hSC : ∀ x y : Sp B.fields.E (B.R.N i), GlobalTheory.TwU.SameCoset I.sel (I.tup a) (I.cst a) P x y ↔ (((qOf P.1 : ℕ) : B.fields.E) ^ (I.cst a).M)⁻¹ • (x - y) ∈ stdAt B.fields.E (B.R.N i) P.1`. Introduce `x y`. Rewrite using `[GlobalTheory.GO.ChRoot.mem_stdAt']`.

Simplify using `only [GlobalTheory.TwU.SameCoset, if_neg hP, Pi.smul_apply, smul_eq_mul]`. Take `⟨k1, k2, k3⟩` from `core (stdAt B.fields.E (B.R.N i) P.1) (Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.1.1.deco.1.N) (frsF I.sel (I.tup a) p.1.1 P) hF _ hc hpow p.1.2 y₀ (I.cst a).M (I.cst a).M hY0 hYl hy₀' (cosetIn p P) hC`. Use `⟨k1, k2, fun z hz => ⟨fun z' => ((k3 z hz).1 z').trans (hSC z' z).symm, ?_⟩⟩` and prove the remaining obligations. Introduce `g g' hg' hcong hgz z'`. Establish `hD2` using `(hI.idx_ok a).depthQ P hP`.

Conclude with `(k3 z hz).2 g g' _ (hGL g' hg') hcong (by omega) ((hSC _ _).1 hgz) z'`.
-/
theorem cosShape : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ) (p : PtAt B.R I.sel (I.tup a) (I.cst a) u i) (P : SBof I a), (i + 1 ≠ B.R.m → cosetIn p P = ∅) ∧ (i + 1 = B.R.m → (cosetIn p P).Nonempty ∧ (∀ y ∈ p.1.2, (frsF I.sel (I.tup a) p.1.1 P).symm y ∈ cosetIn p P) ∧ ∀ z ∈ cosetIn p P, (∀ z', z' ∈ cosetIn p P ↔ GlobalTheory.TwU.SameCoset I.sel (I.tup a) (I.cst a) P z' z) ∧ ∀ g g' : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i), g' ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1 → CongE P.1 ((I.cst a).D P) g g' → GlobalTheory.TwU.SameCoset I.sel (I.tup a) (I.cst a) P (g z) z → ∀ z', g' z' ∈ cosetIn p P ↔ z' ∈ cosetIn p P) := by
  intro B X I hI u a i p P
  refine ⟨fun hi => ?_, fun hi => ?_⟩
  ·
    have h0 : p.1.2 = ∅ := by
      have h := p.2
      rw [ysAt_ys_of_ne (h := hi)] at h
      exact Set.mem_singleton_iff.mp h
    ext z
    simp [cosetIn, h0]
  · obtain ⟨y₀, hy₀, hYeq⟩ := PtAt.mem_ybSet p hi

    have hfr : ∀ x, (frsF I.sel (I.tup a) p.1.1 P) x ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.1.1.deco.1.N ↔
        x ∈ stdAt B.fields.E (B.R.N i) P.1 := by
      intro x
      simp only [frsF]
      split_ifs with h
      · exact (GlobalTheory.TopStep.liftFr_spec p.1.1.deco.2 ⟨P.1, h⟩).1 x
      · exact p.1.1.2 ⟨P.1, (Finset.mem_union.mp P.2).resolve_left h⟩ x
    have hF : ∀ w ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.1.1.deco.1.N,
        (frsF I.sel (I.tup a) p.1.1 P).symm w ∈ stdAt B.fields.E (B.R.N i) P.1 := by
      intro w hw
      rw [← hfr, LinearEquiv.apply_symm_apply]
      exact hw
    have hc : ((qOf P.1 : ℕ) : B.fields.E) ≠ 0 := by
      exact_mod_cast (GlobalTheory.GO.ChRoot.qOf_pos P.1).ne'
    have hpow : ∀ (S : Submodule (𝓞 B.fields.E) (Sp B.fields.E (B.R.N i))) (k : ℕ) (x : Sp B.fields.E (B.R.N i)),
        x ∈ S → ((qOf P.1 : ℕ) : B.fields.E) ^ k • x ∈ S := by
      intro S k x hx
      have h := pow_smul_mem S ((qOf P.1 : ℕ) : 𝓞 B.fields.E) k hx
      simpa using h
    have hY0 : y₀ ∈ p.1.2 := by
      rw [hYeq, Set.mem_setOf_eq, sub_self]
      exact zero_mem _
    have hY1 := (mem_locLat _ _ _ _).1 hy₀ P
    have hGL : ∀ g' : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i),
        g' ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1 →
          ∀ x, g' x ∈ stdAt B.fields.E (B.R.N i) P.1 ↔ x ∈ stdAt B.fields.E (B.R.N i) P.1 := by
      intro g' hg'
      exact hg'
    by_cases hP : P.1 ∈ (B.primes X).vGs
    ·
      have hYl : ∀ y ∈ p.1.2, (((qOf P.1 : ℕ) : B.fields.E) ^ 0)⁻¹ • (y - y₀) ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.1.1.deco.1.N := by
        intro y hy
        rw [hYeq, Set.mem_setOf_eq] at hy
        have h := (mem_locLat _ _ _ _).1 hy P
        simpa [hP] using h
      have hy₀' : ((qOf P.1 : ℕ) : B.fields.E) ^ 1 • y₀ ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.1.1.deco.1.N := by
        simpa [hP] using hY1
      have hC : ∀ z, z ∈ cosetIn p P ↔ ∃ y ∈ p.1.2,
          (((qOf P.1 : ℕ) : B.fields.E) ^ 0)⁻¹ • (z - (frsF I.sel (I.tup a) p.1.1 P).symm y) ∈
            stdAt B.fields.E (B.R.N i) P.1 := by
        intro z
        simp only [cosetIn, Set.mem_setOf_eq, if_pos hP]
      have hSC : ∀ x y : Sp B.fields.E (B.R.N i), GlobalTheory.TwU.SameCoset I.sel (I.tup a) (I.cst a) P x y ↔
          (((qOf P.1 : ℕ) : B.fields.E) ^ 0)⁻¹ • (x - y) ∈ stdAt B.fields.E (B.R.N i) P.1 := by
        intro x y
        rw [GlobalTheory.GO.ChRoot.mem_stdAt']
        simp only [GlobalTheory.TwU.SameCoset, if_pos hP, Pi.smul_apply, smul_eq_mul]
      obtain ⟨k1, k2, k3⟩ := core (stdAt B.fields.E (B.R.N i) P.1) (Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.1.1.deco.1.N)
        (frsF I.sel (I.tup a) p.1.1 P) hF _ hc hpow p.1.2 y₀ 0 1 hY0 hYl hy₀' (cosetIn p P) hC
      refine ⟨k1, k2, fun z hz => ⟨fun z' => ((k3 z hz).1 z').trans (hSC z' z).symm, ?_⟩⟩
      intro g g' hg' hcong hgz z'
      have hD1 := (hI.idx_ok a).depthG P hP
      exact (k3 z hz).2 g g' _ (hGL g' hg') hcong (by omega) ((hSC _ _).1 hgz) z'
    ·
      have hYl : ∀ y ∈ p.1.2, (((qOf P.1 : ℕ) : B.fields.E) ^ (I.cst a).M)⁻¹ • (y - y₀) ∈
          Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.1.1.deco.1.N := by
        intro y hy
        rw [hYeq, Set.mem_setOf_eq] at hy
        have h := (mem_locLat _ _ _ _).1 hy P
        simpa [hP] using h
      have hy₀' : ((qOf P.1 : ℕ) : B.fields.E) ^ (I.cst a).M • y₀ ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.1.1.deco.1.N := by
        simpa [hP] using hY1
      have hC : ∀ z, z ∈ cosetIn p P ↔ ∃ y ∈ p.1.2,
          (((qOf P.1 : ℕ) : B.fields.E) ^ (I.cst a).M)⁻¹ • (z - (frsF I.sel (I.tup a) p.1.1 P).symm y) ∈
            stdAt B.fields.E (B.R.N i) P.1 := by
        intro z
        simp only [cosetIn, Set.mem_setOf_eq, if_neg hP]
      have hSC : ∀ x y : Sp B.fields.E (B.R.N i), GlobalTheory.TwU.SameCoset I.sel (I.tup a) (I.cst a) P x y ↔
          (((qOf P.1 : ℕ) : B.fields.E) ^ (I.cst a).M)⁻¹ • (x - y) ∈ stdAt B.fields.E (B.R.N i) P.1 := by
        intro x y
        rw [GlobalTheory.GO.ChRoot.mem_stdAt']
        simp only [GlobalTheory.TwU.SameCoset, if_neg hP, Pi.smul_apply, smul_eq_mul]
      obtain ⟨k1, k2, k3⟩ := core (stdAt B.fields.E (B.R.N i) P.1) (Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.1.1.deco.1.N)
        (frsF I.sel (I.tup a) p.1.1 P) hF _ hc hpow p.1.2 y₀ (I.cst a).M (I.cst a).M hY0 hYl hy₀' (cosetIn p P) hC
      refine ⟨k1, k2, fun z hz => ⟨fun z' => ((k3 z hz).1 z').trans (hSC z' z).symm, ?_⟩⟩
      intro g g' hg' hcong hgz z'
      have hD2 := (hI.idx_ok a).depthQ P hP
      exact (k3 z hz).2 g g' _ (hGL g' hg') hcong (by omega) ((hSC _ _).1 hgz) z'

end GlobalTheory.Mem.Col2.AdT.CosShape
