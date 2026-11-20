import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeOperatorExists
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeOperatorJacquetEigenRight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsJLeviMulJPlus

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.KmIwahori

open GlobalTheory.CompanionTheory.HeckeJacquet (mem_Km_iff val_unif_lt_one)
open GlobalTheory.LocGL.IwahoriFactor (one_same one_ne)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Establish `hlt : valuation k (((Zls.unifU k : kˣ) : k) ^ m) < 1`. Rewrite using `[map_pow]`. Conclude with `pow_lt_one₀ zero_le' (val_unif_lt_one k) (by omega)`. Take `⟨g, -, hg⟩` from `GlobalTheory.StepData.exists_mem_KOne (k := k) (n := Fin N) (M := M) fun i j => by`. Rewrite using `[Matrix.sub_apply]`.

Conclude with `(h i j).trans_lt hlt`. Conclude with `⟨g, (mem_Km_iff N hm g).2 (by rw [hg]; exact h), hg⟩`.
-/
theorem exists_mem_Km {N m : ℕ} (hm : 1 ≤ m) {M : Matrix (Fin N) (Fin N) k}
    (h : ∀ i j, valuation k (M i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤
      valuation k (((Zls.unifU k : kˣ) : k) ^ m)) :
    ∃ g ∈ Zls.Km k N m, g.val = M := by
  have hlt : valuation k (((Zls.unifU k : kˣ) : k) ^ m) < 1 := by
    rw [map_pow]
    exact pow_lt_one₀ zero_le' (val_unif_lt_one k) (by omega)
  obtain ⟨g, -, hg⟩ := GlobalTheory.StepData.exists_mem_KOne (k := k) (n := Fin N) (M := M)
    fun i j => by
      rw [Matrix.sub_apply]
      exact (h i j).trans_lt hlt
  exact ⟨g, (mem_Km_iff N hm g).2 (by rw [hg]; exact h), hg⟩

variable {α : Type} {μ : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (μ a)]
  [∀ a, DecidableEq (μ a)]

/- English proof (translation)
Establish `hx'` using `(mem_Km_iff N hm x).1 hx`. Establish `hA : ∀ a : α, ∃ y ∈ Zls.Km k N m, y.val = Matrix.of fun i l => if a < blk e i then x.val i l else (1 : Matrix (Fin N) (Fin N) k) i l` using `fun a => exists_mem_Km hm fun i l => by`. Simplify using `only [Matrix.of_apply]`. Use `split_ifs`. Conclude with `hx' i l`.

Simplify using the standard rewrite rules. Use `choose y hy hyv using hA`. Take `⟨c, hc, hcv⟩` from `exists_mem_Km hm (M := Matrix.of fun i j => (y (blk e j))⁻¹.val i j) fun i j => (mem_Km_iff N hm _).1 (inv_mem (hy (blk e j))) i j`. Establish `key : ∀ i j, ∑ l, (if blk e j < blk e i then x.val i l else (1 : Matrix (Fin N) (Fin N) k) i l) * c.val l j = (1 : Matrix (Fin N) (Fin N) k) i j` using `fun i j => by`. Use `congrFun (congrFun (y (blk e j)).mul_inv i) j` as an intermediate fact.

Rewrite `this` using `[Matrix.mul_apply, hyv]`. Rewrite using `[hcv]`. Conclude with `this`. Establish `h1 : ∀ i j, blk e i ≤ blk e j → c.val i j = (1 : Matrix (Fin N) (Fin N) k) i j` using `fun i j h => by`. Use `key i j` as an intermediate fact.

Simplify using `only [if_neg h.not_gt] at this`. Rewrite `this` using `[← Matrix.mul_apply, Matrix.one_mul]`. Then use the resulting hypothesis. Use `⟨c, ⟨hc, (mem_unipRadLower k).2 ⟨(mem_parabLower_iff k).2 fun a b i j h => ?_, fun a i j => ?_⟩⟩, mem_parab_iff.2 fun a b i j h => ?_⟩` and prove the remaining obligations. Rewrite using `[h1 _ _ (by simpa using h.le), one_ne e h.ne]`. Rewrite using `[h1 _ _ (by simp), one_same]`.

Use `key (e ⟨a, i⟩) (e ⟨b, j⟩)` as an intermediate fact. Simplify using `only [blk_apply, if_pos h] at this`. Rewrite using `[Units.val_mul, Matrix.mul_apply, this, one_ne e h.ne']`.
-/
theorem exists_mul_mem_parab {N m : ℕ} (hm : 1 ≤ m) (e : (Σ a, μ a) ≃ Fin N) {x : GL (Fin N) k}
    (hx : x ∈ Zls.Km k N m) :
    ∃ c ∈ Zls.Km k N m ⊓ unipRadLower k e, x * c ∈ parab k e := by
  have hx' := (mem_Km_iff N hm x).1 hx
  have hA : ∀ a : α, ∃ y ∈ Zls.Km k N m, y.val =
      Matrix.of fun i l => if a < blk e i then x.val i l else (1 : Matrix (Fin N) (Fin N) k) i l := fun a =>
    exists_mem_Km hm fun i l => by
      simp only [Matrix.of_apply]
      split_ifs
      · exact hx' i l
      · simp
  choose y hy hyv using hA
  obtain ⟨c, hc, hcv⟩ := exists_mem_Km hm (M := Matrix.of fun i j => (y (blk e j))⁻¹.val i j)
    fun i j => (mem_Km_iff N hm _).1 (inv_mem (hy (blk e j))) i j
  have key : ∀ i j, ∑ l, (if blk e j < blk e i then x.val i l else (1 : Matrix (Fin N) (Fin N) k) i l) *
      c.val l j = (1 : Matrix (Fin N) (Fin N) k) i j := fun i j => by
    have := congrFun (congrFun (y (blk e j)).mul_inv i) j
    rw [Matrix.mul_apply, hyv] at this
    rw [hcv]
    exact this
  have h1 : ∀ i j, blk e i ≤ blk e j → c.val i j = (1 : Matrix (Fin N) (Fin N) k) i j := fun i j h => by
    have := key i j
    simp only [if_neg h.not_gt] at this
    rwa [← Matrix.mul_apply, Matrix.one_mul] at this
  refine ⟨c, ⟨hc, (mem_unipRadLower k).2 ⟨(mem_parabLower_iff k).2 fun a b i j h => ?_, fun a i j => ?_⟩⟩,
    mem_parab_iff.2 fun a b i j h => ?_⟩
  · rw [h1 _ _ (by simpa using h.le), one_ne e h.ne]
  · rw [h1 _ _ (by simp), one_same]
  · have := key (e ⟨a, i⟩) (e ⟨b, j⟩)
    simp only [blk_apply, if_pos h] at this
    rw [Units.val_mul, Matrix.mul_apply, this, one_ne e h.ne']

/- English proof (translation)
Use `(mem_Km_iff N hm _).2 fun i j => ?_` and prove the remaining obligations. Take `⟨⟨a, i⟩, rfl⟩` from `e.surjective i`. Take `⟨⟨b, j⟩, rfl⟩` from `e.surjective j`. Distinguish the cases in `h : a = b`. Substitute `h` using the available equality.

Use `(mem_Km_iff N hm _).1 hp (e ⟨a, i⟩) (e ⟨a, j⟩)` as an intermediate fact. Rewrite using `[leviEmb_apply_same, leviProj_apply]` and apply the resulting hypothesis. Rewrite using `[leviEmb_apply_ne k e _ h, one_ne e h]`. Simplify using the standard rewrite rules.
-/
theorem leviEmb_leviProj_mem_Km {N m : ℕ} (hm : 1 ≤ m) (e : (Σ a, μ a) ≃ Fin N) (p : parab k e)
    (hp : (p : GL (Fin N) k) ∈ Zls.Km k N m) :
    leviEmb k e (leviProj k e p) ∈ Zls.Km k N m := by
  refine (mem_Km_iff N hm _).2 fun i j => ?_
  obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
  obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective j
  by_cases h : a = b
  · subst h
    have := (mem_Km_iff N hm _).1 hp (e ⟨a, i⟩) (e ⟨a, j⟩)
    rwa [leviEmb_apply_same, leviProj_apply]
  · rw [leviEmb_apply_ne k e _ h, one_ne e h]
    simp

/- English proof (translation)
Take `⟨c, hc, hp⟩` from `exists_mul_mem_parab hm e (inv_mem hx)`. Establish `hq : (x⁻¹ * c)⁻¹ ∈ parab k e` using `inv_mem hp`. Establish `hqK : (x⁻¹ * c)⁻¹ ∈ Zls.Km k N m` using `inv_mem (mul_mem (inv_mem hx) hc.1)`. Take `⟨u, hu, hqu⟩` from `exists_levi_mul_unip k e ⟨_, hq⟩`. Establish `hd` using `leviEmb_leviProj_mem_Km hm e ⟨_, hq⟩ hqK`.

Use `⟨c, hc, _, ⟨hd, ⟨_, rfl⟩⟩, u, ⟨?_, hu⟩, ?_⟩` and prove the remaining obligations. Establish `: u = (leviEmb k e (leviProj k e ⟨_, hq⟩))⁻¹ * (x⁻¹ * c)⁻¹`. Rewrite using `[eq_inv_mul_iff_mul_eq]`. Conclude with `hqu.symm`. Use `show u ∈ Zls.Km k N m`.

Rewrite using `[this]`. Conclude with `mul_mem (inv_mem hd) hqK`. Rewrite using `[mul_assoc, ← hqu] group`.
-/
theorem exists_factor {N m : ℕ} (hm : 1 ≤ m) (e : (Σ a, μ a) ≃ Fin N) {x : GL (Fin N) k}
    (hx : x ∈ Zls.Km k N m) :
    ∃ a ∈ Zls.Km k N m ⊓ unipRadLower k e, ∃ b ∈ Zls.Km k N m ⊓ (leviEmb k e).range,
      ∃ c ∈ Zls.Km k N m ⊓ unipRad k e, x = a * b * c := by
  obtain ⟨c, hc, hp⟩ := exists_mul_mem_parab hm e (inv_mem hx)
  have hq : (x⁻¹ * c)⁻¹ ∈ parab k e := inv_mem hp
  have hqK : (x⁻¹ * c)⁻¹ ∈ Zls.Km k N m := inv_mem (mul_mem (inv_mem hx) hc.1)
  obtain ⟨u, hu, hqu⟩ := exists_levi_mul_unip k e ⟨_, hq⟩
  have hd := leviEmb_leviProj_mem_Km hm e ⟨_, hq⟩ hqK
  refine ⟨c, hc, _, ⟨hd, ⟨_, rfl⟩⟩, u, ⟨?_, hu⟩, ?_⟩
  · have : u = (leviEmb k e (leviProj k e ⟨_, hq⟩))⁻¹ * (x⁻¹ * c)⁻¹ := by
      rw [eq_inv_mul_iff_mul_eq]
      exact hqu.symm
    show u ∈ Zls.Km k N m
    rw [this]
    exact mul_mem (inv_mem hd) hqK
  · rw [mul_assoc, ← hqu]
    group

/- English proof (translation)
Introduce `k _ _ _ _ N m h d hd hm`. Conclude with `⟨GlobalTheory.CompanionTheory.HeckeKm.isOpen_Km N m, GlobalTheory.CompanionTheory.HeckeKm.isCompact_Km N m, fun x hx => exists_factor hm (stdBlocks d hd) hx⟩`.
-/
theorem c0 : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    PositivityTheory.Lbc.C0 k := by
  intro k _ _ _ _ N m h d hd hm
  exact ⟨GlobalTheory.CompanionTheory.HeckeKm.isOpen_Km N m, GlobalTheory.CompanionTheory.HeckeKm.isCompact_Km N m,
    fun x hx => exists_factor hm (stdBlocks d hd) hx⟩

end GlobalTheory.CompanionTheory.KmIwahori

end
