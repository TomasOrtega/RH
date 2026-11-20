import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.MultiplicationKernelIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreEig
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjoinRootProdLinearFactorsStructureStatement
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module

/- English proof (translation)
Introduce `C _ v S _ _ a ha N Fil hFil τ`. Take `⟨hfree, hfin, hlc, hev, hker, ⟨g, hg⟩, hann⟩` from `GlobalTheory.T.adjoinRootProdLinearFactors_structure (Int0 v) S a τ`. Establish `hd : ev a τ (cofac a τ) ≠ 0`. Rewrite using `[hev]`. Conclude with `Finset.prod_ne_zero_iff.mpr fun s hs => sub_ne_zero.mpr fun h => Finset.ne_of_mem_erase hs (ha h).symm`.

Establish `hid : ∀ x : Fin N → RS a, ev a τ (cofac a τ) • x = cofac a τ • x - g • (lin a τ • x)`. Introduce `x`. Establish `: cofac a τ • x = ev a τ (cofac a τ) • x + g • (lin a τ • x)` using `by conv_lhs => rw [hg]`. Rewrite using `[add_smul, algebraMap_smul, mul_comm, mul_smul]`. Rewrite using `[this, add_sub_cancel_right]`.

Establish `htf : ∀ (c : Int0 v) (x : Fin N → RS a), c ≠ 0 → c • x = 0 → x = 0`. Introduce `c x hc hx`. Use `haveI := hfree`. Use `haveI : Module.IsTorsionFree (Int0 v) (Fin N → RS a) := (Module.Free.chooseBasis (Int0 v) (Fin N → RS a)).isTorsionFree`. Conclude with `(smul_eq_zero_iff_right hc).mp hx`.

Establish `hcomp0 : ∀ x : Fin N → RS a, comp a N τ x = 0 ↔ ∀ i, ev a τ (x i) = 0`. Introduce `x`. Prove the components needed by the constructor for the conclusion. Introduce `h i`. Conclude with `congrFun h i`.

Introduce `h`. Use function extensionality and compare the values at `i`. Conclude with `h i`. Establish `h2 : ∀ x : Fin N → RS a, comp a N τ x = 0 ↔ mulR a N (cofac a τ) x = 0`. Introduce `x`.

Rewrite using `[hcomp0]`. Prove the components needed by the constructor for the conclusion. Introduce `h show cofac a τ • x = 0`. Use function extensionality and compare the values at `i`. Take `⟨r', hr'⟩` from `hker _ (h i)`.

Use `show cofac a τ * x i = 0`. Rewrite using `[hr', ← mul_assoc, mul_comm (cofac a τ), hlc, zero_mul]`. Introduce `h i`. Establish `hi : cofac a τ * x i = 0` using `congrFun h i`. Use `congrArg (ev a τ) hi` as an intermediate fact.

Rewrite `this` using `[map_mul, map_zero]`. Conclude with `(mul_eq_zero.mp this).resolve_left hd`. Establish `h3 : LinearMap.ker (comp a N τ) = LinearMap.range (mulR a N (lin a τ))`. Use extensionality with `x`. Rewrite using `[LinearMap.mem_ker, LinearMap.mem_range, hcomp0]`.

Prove the components needed by the constructor for the conclusion. Introduce `h choose r hr using fun i => hker _ (h i)`. Conclude with `⟨r, funext fun i => (hr i).symm⟩`. Introduce and unpack `⟨y, rfl⟩ i show ev a τ (lin a τ * y i) = 0`. Rewrite using `[map_mul, ev_lin, sub_self, zero_mul]`.

Establish `hcz : ∀ x : Fin N → RS a, comp a N τ x = 0 → cofac a τ • x = 0` using `fun x h => (h2 x).mp h`. Use `⟨hd, h2, h3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, htf, ⟨g, hid⟩⟩` and prove the remaining obligations. Introduce and unpack `x ⟨hx1, hx2⟩`. Establish `hx1' : lin a τ • x ∈ Fil` using `hx1`. Establish `hc : cofac a τ • x = 0` using `hcz x hx2`.

Apply `hFil _ x hd` to reduce the goal to its premises. Rewrite using `[hid, hc, zero_sub]`. Conclude with `Fil.neg_mem (Fil.smul_mem g hx1')`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨x, hx, rfl⟩`. Establish `hx' : lin a τ • x ∈ Fil` using `hx`. Use `⟨hx', ?_⟩` and prove the remaining obligations. Use `show cofac a τ • (lin a τ • x) = 0`. Rewrite using `[smul_smul, mul_comm, hlc, zero_smul]`.

Introduce and unpack `⟨hy1, hy2⟩`. Establish `hy2' : mulR a N (cofac a τ) y = 0` using `hy2`. Establish `hk : y ∈ LinearMap.ker (comp a N τ)` using `(h2 y).mpr hy2'`. Rewrite `hk` using `[h3]`. Take `⟨x, rfl⟩` from `hk`.

Conclude with `⟨x, hy1, rfl⟩`. Rewrite using `[eq_bot_iff]`. Introduce and unpack `x ⟨hx1, hx2⟩`. Establish `hx1' : lin a τ • x = 0` using `hx1`. Establish `hc : cofac a τ • x = 0` using `hcz x hx2`.

Establish `: ev a τ (cofac a τ) • x = 0` using `by rw [hid, hc, hx1', smul_zero, sub_zero]`. Conclude with `(Submodule.mem_bot _).mpr (htf _ x hd this)`. Use extensionality with `y`. Simplify using `only [Submodule.mem_map, Submodule.mem_top, true_and, LinearMap.lsmul_apply]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨x, hx, rfl⟩`. Establish `hx' : lin a τ • x = 0` using `hx`. Use `choose c hc using fun i => hann (x i) (congrFun hx' i)`. Use `⟨c, funext fun i => ?_⟩` and prove the remaining obligations. Use `show ev a τ (cofac a τ) * c i = ev a τ (x i)`.

Rewrite using `[hc i, map_mul, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, mul_comm]`. Introduce and unpack `⟨c, rfl⟩`. Use `⟨fun i => algebraMap (Int0 v) (RS a) (c i) * cofac a τ, ?_, ?_⟩` and prove the remaining obligations. Use `show lin a τ • (fun i => algebraMap (Int0 v) (RS a) (c i) * cofac a τ) = 0`. Use function extensionality and compare the values at `i`.

Use `show lin a τ * (algebraMap (Int0 v) (RS a) (c i) * cofac a τ) = 0`. Rewrite using `[mul_left_comm, hlc, mul_zero]`. Use function extensionality and compare the values at `i show ev a τ (algebraMap (Int0 v) (RS a) (c i) * cofac a τ) = ev a τ (cofac a τ) * c i`. Rewrite using `[map_mul, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, mul_comm]`. Use extensionality with `q`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Establish `hx' : lin a τ • x ∈ Fil` using `hx`. Use `show lin a τ • Fil.mkQ x = 0`. Rewrite using `[← LinearMap.map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`.

Conclude with `hx'`. Introduce `hq`. Establish `hq' : lin a τ • q = 0` using `hq`. Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective Fil q`. Use `⟨x, ?_, rfl⟩` and prove the remaining obligations.

Use `show lin a τ • x ∈ Fil`. Rewrite using `[← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]`. Conclude with `hq'`. Introduce `x hx`. Establish `hx' : lin a τ • x = 0` using `hx`.

Use `show lin a τ • x ∈ Fil`. Rewrite using `[hx']`. Conclude with `Fil.zero_mem`. Introduce `x hx show lin a τ • x ∈ Fil`. Conclude with `Fil.smul_mem _ hx`.
-/
theorem GlobalTheory.herbrand_lattice_facts : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (S : Type) [Fintype S] [DecidableEq S] (a : S → Int0 v), Function.Injective a → ∀ (N : ℕ) (Fil : Submodule (RS a) (Fin N → RS a)), (∀ (c : Int0 v) (x : Fin N → RS a), c ≠ 0 → c • x ∈ Fil → x ∈ Fil) → ∀ τ : S, ev a τ (cofac a τ) ≠ 0 ∧ (∀ x : Fin N → RS a, comp a N τ x = 0 ↔ mulR a N (cofac a τ) x = 0) ∧ LinearMap.ker (comp a N τ) = LinearMap.range (mulR a N (lin a τ)) ∧ preEig a Fil τ ⊓ LinearMap.ker (comp a N τ) ≤ Fil.restrictScalars (Int0 v) ∧ (preEig a Fil τ).map (mulR a N (lin a τ)) = filKer a Fil τ ∧ eigSub a τ (Fin N → RS a) ⊓ LinearMap.ker (comp a N τ) = ⊥ ∧ (eigSub a τ (Fin N → RS a)).map (comp a N τ) = (⊤ : Submodule (Int0 v) (Fin N → Int0 v)).map (LinearMap.lsmul (Int0 v) (Fin N → Int0 v) (ev a τ (cofac a τ))) ∧ (preEig a Fil τ).map (proj a Fil) = eigSub a τ ((Fin N → RS a) ⧸ Fil) ∧ eigSub a τ (Fin N → RS a) ≤ preEig a Fil τ ∧ Fil.restrictScalars (Int0 v) ≤ preEig a Fil τ ∧ (∀ (c : Int0 v) (x : Fin N → RS a), c ≠ 0 → c • x = 0 → x = 0) ∧ (∃ g : RS a, ∀ x : Fin N → RS a, ev a τ (cofac a τ) • x = cofac a τ • x - g • (lin a τ • x)) := by
  intro C _ v S _ _ a ha N Fil hFil τ
  obtain ⟨hfree, hfin, hlc, hev, hker, ⟨g, hg⟩, hann⟩ := GlobalTheory.T.adjoinRootProdLinearFactors_structure (Int0 v) S a τ
  have hd : ev a τ (cofac a τ) ≠ 0 := by
    rw [hev]
    exact Finset.prod_ne_zero_iff.mpr fun s hs =>
      sub_ne_zero.mpr fun h => Finset.ne_of_mem_erase hs (ha h).symm
  have hid : ∀ x : Fin N → RS a, ev a τ (cofac a τ) • x = cofac a τ • x - g • (lin a τ • x) := by
    intro x
    have : cofac a τ • x = ev a τ (cofac a τ) • x + g • (lin a τ • x) := by
      conv_lhs => rw [hg]
      rw [add_smul, algebraMap_smul, mul_comm, mul_smul]
    rw [this, add_sub_cancel_right]
  have htf : ∀ (c : Int0 v) (x : Fin N → RS a), c ≠ 0 → c • x = 0 → x = 0 := by
    intro c x hc hx
    haveI := hfree
    haveI : Module.IsTorsionFree (Int0 v) (Fin N → RS a) :=
      (Module.Free.chooseBasis (Int0 v) (Fin N → RS a)).isTorsionFree
    exact (smul_eq_zero_iff_right hc).mp hx
  have hcomp0 : ∀ x : Fin N → RS a, comp a N τ x = 0 ↔ ∀ i, ev a τ (x i) = 0 := by
    intro x
    constructor
    · intro h i; exact congrFun h i
    · intro h; funext i; exact h i
  have h2 : ∀ x : Fin N → RS a, comp a N τ x = 0 ↔ mulR a N (cofac a τ) x = 0 := by
    intro x
    rw [hcomp0]
    constructor
    · intro h
      show cofac a τ • x = 0
      funext i
      obtain ⟨r', hr'⟩ := hker _ (h i)
      show cofac a τ * x i = 0
      rw [hr', ← mul_assoc, mul_comm (cofac a τ), hlc, zero_mul]
    · intro h i
      have hi : cofac a τ * x i = 0 := congrFun h i
      have := congrArg (ev a τ) hi
      rw [map_mul, map_zero] at this
      exact (mul_eq_zero.mp this).resolve_left hd
  have h3 : LinearMap.ker (comp a N τ) = LinearMap.range (mulR a N (lin a τ)) := by
    ext x
    rw [LinearMap.mem_ker, LinearMap.mem_range, hcomp0]
    constructor
    · intro h
      choose r hr using fun i => hker _ (h i)
      exact ⟨r, funext fun i => (hr i).symm⟩
    · rintro ⟨y, rfl⟩ i
      show ev a τ (lin a τ * y i) = 0
      rw [map_mul, ev_lin, sub_self, zero_mul]
  have hcz : ∀ x : Fin N → RS a, comp a N τ x = 0 → cofac a τ • x = 0 := fun x h => (h2 x).mp h
  refine ⟨hd, h2, h3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, htf, ⟨g, hid⟩⟩
  ·
    rintro x ⟨hx1, hx2⟩
    have hx1' : lin a τ • x ∈ Fil := hx1
    have hc : cofac a τ • x = 0 := hcz x hx2
    apply hFil _ x hd
    rw [hid, hc, zero_sub]
    exact Fil.neg_mem (Fil.smul_mem g hx1')
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : lin a τ • x ∈ Fil := hx
      refine ⟨hx', ?_⟩
      show cofac a τ • (lin a τ • x) = 0
      rw [smul_smul, mul_comm, hlc, zero_smul]
    · rintro ⟨hy1, hy2⟩
      have hy2' : mulR a N (cofac a τ) y = 0 := hy2
      have hk : y ∈ LinearMap.ker (comp a N τ) := (h2 y).mpr hy2'
      rw [h3] at hk
      obtain ⟨x, rfl⟩ := hk
      exact ⟨x, hy1, rfl⟩
  · rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    have hx1' : lin a τ • x = 0 := hx1
    have hc : cofac a τ • x = 0 := hcz x hx2
    have : ev a τ (cofac a τ) • x = 0 := by rw [hid, hc, hx1', smul_zero, sub_zero]
    exact (Submodule.mem_bot _).mpr (htf _ x hd this)
  · ext y
    simp only [Submodule.mem_map, Submodule.mem_top, true_and, LinearMap.lsmul_apply]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : lin a τ • x = 0 := hx
      choose c hc using fun i => hann (x i) (congrFun hx' i)
      refine ⟨c, funext fun i => ?_⟩
      show ev a τ (cofac a τ) * c i = ev a τ (x i)
      rw [hc i, map_mul, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, mul_comm]
    · rintro ⟨c, rfl⟩
      refine ⟨fun i => algebraMap (Int0 v) (RS a) (c i) * cofac a τ, ?_, ?_⟩
      · show lin a τ • (fun i => algebraMap (Int0 v) (RS a) (c i) * cofac a τ) = 0
        funext i
        show lin a τ * (algebraMap (Int0 v) (RS a) (c i) * cofac a τ) = 0
        rw [mul_left_comm, hlc, mul_zero]
      · funext i
        show ev a τ (algebraMap (Int0 v) (RS a) (c i) * cofac a τ) = ev a τ (cofac a τ) * c i
        rw [map_mul, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, mul_comm]
  · ext q
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : lin a τ • x ∈ Fil := hx
      show lin a τ • Fil.mkQ x = 0
      rw [← LinearMap.map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hx'
    · intro hq
      have hq' : lin a τ • q = 0 := hq
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective Fil q
      refine ⟨x, ?_, rfl⟩
      show lin a τ • x ∈ Fil
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
      exact hq'
  · intro x hx
    have hx' : lin a τ • x = 0 := hx
    show lin a τ • x ∈ Fil
    rw [hx']; exact Fil.zero_mem
  · intro x hx
    show lin a τ • x ∈ Fil
    exact Fil.smul_mem _ hx
