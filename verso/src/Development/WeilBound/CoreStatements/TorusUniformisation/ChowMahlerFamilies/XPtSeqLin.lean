import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LieLatticeData
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.PolarisedFlagStatement

open GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.GR ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up

namespace PositivityTheory.Xgn.A_pt_seq_lin

variable {o C : Type} [CommRing o] [Field C] [Algebra o C]

/- English proof (translation)
Simplify using `[stdLat, AddSubgroup.mem_pi]`.
-/
theorem mem_std (R : Subalgebra o C) {ι : Type} (v : ι → C) : v ∈ stdLat R ι ↔ ∀ i, v i ∈ R := by
  simp [stdLat, AddSubgroup.mem_pi]

/- English proof (translation)
Simplify using `[dotDual, AddSubgroup.mem_iInf]`.
-/
theorem mem_dual (R : Subalgebra o C) {m : ℕ} (L : AddSubgroup (Fin m → C)) (v : Fin m → C) :
    v ∈ dotDual R L ↔ ∀ l ∈ L, l ⬝ᵥ v ∈ R := by
  simp [dotDual, AddSubgroup.mem_iInf]

/- English proof (translation)
Introduce `v hv`. Rewrite using `[mem_dual]`. Introduce `l hl`. Establish `hl'` using `(mem_std R l).1 (h hl)`. Establish `hv'` using `(mem_std R v).1 hv`.

Use `show ∑ i, l i * v i ∈ R`. Conclude with `R.sum_mem fun i _ => R.mul_mem (hl' i) (hv' i)`.
-/
theorem std_le_dual (R : Subalgebra o C) {m : ℕ} (L : AddSubgroup (Fin m → C))
    (h : L ≤ stdLat R _) : stdLat R _ ≤ dotDual R L := by
  intro v hv
  rw [mem_dual]
  intro l hl
  have hl' := (mem_std R l).1 (h hl)
  have hv' := (mem_std R v).1 hv
  show ∑ i, l i * v i ∈ R
  exact R.sum_mem fun i _ => R.mul_mem (hl' i) (hv' i)

/- English proof (translation)
Rewrite using `[mem_std]`. Introduce `i`. Establish `he : (Pi.single i (1 : C) : Fin m → C) ∈ stdLat R (Fin m)`. Rewrite using `[mem_std]`. Introduce `j`.

Rewrite using `[Pi.single_apply]`. Use `split_ifs`. Conclude with `R.one_mem`. Conclude with `R.zero_mem`. Establish `hwe : w • (Pi.single i (1 : C) : Fin m → C) ∈ L` using `h (AddSubgroup.mem_map_of_mem (DistribMulAction.toAddMonoidHom (Fin m → C) w) he)`.

Establish `hd` using `(mem_dual R L v).1 hv _ hwe`. Establish `heq : (w • (Pi.single i (1 : C) : Fin m → C)) ⬝ᵥ v = w * v i`. Rewrite using `[smul_dotProduct, single_dotProduct, one_mul, smul_eq_mul]`. Rewrite `hd` using `[heq]`. Simplify `hd` using `[Pi.smul_apply, smul_eq_mul]`.
-/
theorem smul_mem_std (R : Subalgebra o C) {m : ℕ} (L : AddSubgroup (Fin m → C)) (w : C)
    (h : mulLat w (stdLat R _) ≤ L) (v : Fin m → C) (hv : v ∈ dotDual R L) :
    w • v ∈ stdLat R (Fin m) := by
  rw [mem_std]
  intro i
  have he : (Pi.single i (1 : C) : Fin m → C) ∈ stdLat R (Fin m) := by
    rw [mem_std]
    intro j
    rw [Pi.single_apply]
    split_ifs
    · exact R.one_mem
    · exact R.zero_mem
  have hwe : w • (Pi.single i (1 : C) : Fin m → C) ∈ L :=
    h (AddSubgroup.mem_map_of_mem (DistribMulAction.toAddMonoidHom (Fin m → C) w) he)
  have hd := (mem_dual R L v).1 hv _ hwe
  have heq : (w • (Pi.single i (1 : C) : Fin m → C)) ⬝ᵥ v = w * v i := by
    rw [smul_dotProduct, single_dotProduct, one_mul, smul_eq_mul]
  rw [heq] at hd
  simpa [Pi.smul_apply, smul_eq_mul] using hd

end PositivityTheory.Xgn.A_pt_seq_lin

open PositivityTheory.Xgn.A_pt_seq_lin in
/- English proof (translation)
Introduce `o C _ _ _ RC p F _ _ n Sg r s D w χ τ hw0 h1 h2 ht hb hinj hrng hHT hW hom hlie hDel hGam`. Establish `hS : stdLat RC (Fin n) ≤ D.hh RC p (χ τ)` using `std_le_dual RC _ h2`. Establish `hm : ∀ v ∈ D.hh RC p (χ τ), w • v ∈ stdLat RC (Fin n)` using `fun v hv => smul_mem_std RC _ w h1 v hv`. Prove the components needed by the constructor for the conclusion. Use extensionality with `c`.

Rewrite using `[← hom]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨b, c'⟩, hx, rfl⟩`. Take `⟨hd, hp⟩` from `AddSubgroup.mem_inf.1 hx`. Take `⟨hb1, -⟩` from `AddSubgroup.mem_prod.1 hp`.

Take `⟨-, hc⟩` from `(hDel b c').1 hd`. Rewrite `hc` using `[← hHT]`. Take `⟨y, hy, hy'⟩` from `AddSubgroup.mem_map.1 hc`. Use `AddSubgroup.mem_map.2 ⟨b + y, add_mem hb1 (hS hy), ?_⟩` and prove the remaining obligations. Simplify using `only [LinearMap.toAddMonoidHom_coe] at hy' ⊢`.

Simplify using `[map_add, hy']`. Introduce and unpack `⟨b, hb1, rfl⟩`. Use `AddSubgroup.mem_map.2 ⟨(b, ht b), AddSubgroup.mem_inf.2 ⟨?_, AddSubgroup.mem_prod.2 ⟨hb1, AddSubgroup.mem_top _⟩⟩, rfl⟩` and prove the remaining obligations. Rewrite using `[hDel]`. Use `⟨hm b hb1, ?_⟩` and prove the remaining obligations.

Simplify using `only [sub_self]`. Conclude with `zero_mem _`. Use extensionality with `a`. Rewrite using `[← hlie]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨⟨a', b⟩, hx, rfl⟩`. Take `⟨hg, hp⟩` from `AddSubgroup.mem_inf.1 hx`. Take `⟨-, hb1⟩` from `AddSubgroup.mem_prod.1 hp`. Take `⟨-, h2'⟩` from `(hGam a' b).1 hg`. Rewrite using `[AddSubgroup.mem_comap]`.

Use `sub_mem hb1 (hS h2')` as an intermediate fact. Simplify using `using this`. Introduce `ha`. Rewrite `ha` using `[AddSubgroup.mem_comap]`. Use `AddSubgroup.mem_map.2 ⟨(a, hb a), AddSubgroup.mem_inf.2 ⟨(hGam _ _).2 ⟨?_, ?_⟩, AddSubgroup.mem_prod.2 ⟨AddSubgroup.mem_top _, ha⟩⟩, rfl⟩` and prove the remaining obligations.

Rewrite using `[← hW, AddSubgroup.mem_comap]`. Simplify using `only [LinearMap.toAddMonoidHom_coe, map_smul]`. Conclude with `hm _ ha`. Simplify using `only [sub_self]`. Conclude with `zero_mem _`.
-/
theorem PositivityTheory.Xgn.t_pt_seq_lin : ∀ {o C : Type} [CommRing o] [Field C] [Algebra o C] (RC : Subalgebra o C) (p : ℕ) {F : Type} [Zero F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData C F n Sg r s) (w : C) (χ : Sg → F → C) (τ : Sg), w ≠ 0 → mulLat w (stdLat RC _) ≤ D.af RC p (χ τ) → D.af RC p (χ τ) ≤ stdLat RC _ → ∀ (ht : (Fin n → C) →ₗ[C] (Fin (s τ) → C)) (hb : (Fin (r τ) → C) →ₗ[C] (Fin n → C)), Function.Injective hb → LinearMap.range hb = LinearMap.ker ht → (stdLat RC _).map ht.toAddMonoidHom = D.omHT τ → (stdLat RC _).comap hb.toAddMonoidHom = D.W τ → (D.hh RC p (χ τ)).map ht.toAddMonoidHom = D.om τ → (D.hh RC p (χ τ)).comap hb.toAddMonoidHom = divLat w (D.lie τ) → (∀ b c, (b, c) ∈ D.Del τ ↔ w • b ∈ stdLat RC _ ∧ c - ht b ∈ D.omHT τ) → (∀ a b, (a, b) ∈ D.Gam τ ↔ w • a ∈ D.W τ ∧ b - hb a ∈ stdLat RC _) → D.imH RC p τ (χ τ) = D.om τ ∧ D.kerH RC p τ (χ τ) = divLat w (D.lie τ) := by
  intro o C _ _ _ RC p F _ _ n Sg r s D w χ τ hw0 h1 h2 ht hb hinj hrng hHT hW hom hlie hDel hGam
  have hS : stdLat RC (Fin n) ≤ D.hh RC p (χ τ) := std_le_dual RC _ h2
  have hm : ∀ v ∈ D.hh RC p (χ τ), w • v ∈ stdLat RC (Fin n) :=
    fun v hv => smul_mem_std RC _ w h1 v hv
  constructor
  · ext c
    rw [← hom]
    constructor
    · rintro ⟨⟨b, c'⟩, hx, rfl⟩
      obtain ⟨hd, hp⟩ := AddSubgroup.mem_inf.1 hx
      obtain ⟨hb1, -⟩ := AddSubgroup.mem_prod.1 hp
      obtain ⟨-, hc⟩ := (hDel b c').1 hd
      rw [← hHT] at hc
      obtain ⟨y, hy, hy'⟩ := AddSubgroup.mem_map.1 hc
      refine AddSubgroup.mem_map.2 ⟨b + y, add_mem hb1 (hS hy), ?_⟩
      simp only [LinearMap.toAddMonoidHom_coe] at hy' ⊢
      simp [map_add, hy']
    · rintro ⟨b, hb1, rfl⟩
      refine AddSubgroup.mem_map.2 ⟨(b, ht b), AddSubgroup.mem_inf.2 ⟨?_, AddSubgroup.mem_prod.2 ⟨hb1, AddSubgroup.mem_top _⟩⟩, rfl⟩
      rw [hDel]
      refine ⟨hm b hb1, ?_⟩
      simp only [sub_self]
      exact zero_mem _
  · ext a
    rw [← hlie]
    constructor
    · rintro ⟨⟨a', b⟩, hx, rfl⟩
      obtain ⟨hg, hp⟩ := AddSubgroup.mem_inf.1 hx
      obtain ⟨-, hb1⟩ := AddSubgroup.mem_prod.1 hp
      obtain ⟨-, h2'⟩ := (hGam a' b).1 hg
      rw [AddSubgroup.mem_comap]
      have := sub_mem hb1 (hS h2')
      simpa using this
    · intro ha
      rw [AddSubgroup.mem_comap] at ha
      refine AddSubgroup.mem_map.2 ⟨(a, hb a), AddSubgroup.mem_inf.2 ⟨(hGam _ _).2 ⟨?_, ?_⟩, AddSubgroup.mem_prod.2 ⟨AddSubgroup.mem_top _, ha⟩⟩, rfl⟩
      · rw [← hW, AddSubgroup.mem_comap]
        simp only [LinearMap.toAddMonoidHom_coe, map_smul]
        exact hm _ ha
      · simp only [sub_self]
        exact zero_mem _
