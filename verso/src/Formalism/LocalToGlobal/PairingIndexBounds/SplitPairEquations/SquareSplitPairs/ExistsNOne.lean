import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SquareSplitPairs.SumThreeComm
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsSmulMemLattice

noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.PairingIndexBounds.Eq.SquareSplitPairs

open Formalism.MainNotions Formalism.L2.PairingIndexBounds.Eq

variable {D : D7}

/- English proof (translation)
Establish `e : ((m * k : 𝓞 D.host.E) : D.host.E) • v = m • ((k : D.host.E) • v)`. Rewrite using `[osmul, smul_smul]`. Use `norm_cast`. Rewrite using `[e]`. Conclude with `L₁.smul_mem m h`.
-/
theorem mul_smul_mem {N : ℕ} {L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {m k : 𝓞 D.host.E}
    {v : Fin N → D.host.E} (h : (k : D.host.E) • v ∈ L₁) : ((m * k : 𝓞 D.host.E) : D.host.E) • v ∈ L₁ := by
  have e : ((m * k : 𝓞 D.host.E) : D.host.E) • v = m • ((k : D.host.E) • v) := by
    rw [osmul, smul_smul]
    norm_cast
  rw [e]
  exact L₁.smul_mem m h

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.ExistsIntegerSmulMemOfSpanEqTop.exists_smul_mem hsp x`.
-/
theorem exists_smul_mem {N : ℕ} {L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    (hsp : Submodule.span D.host.E (L₁ : Set (Fin N → D.host.E)) = ⊤) (x : Fin N → D.host.E) :
    ∃ n : 𝓞 D.host.E, n ≠ 0 ∧ (n : D.host.E) • x ∈ L₁ :=
  _root_.UpperTheory.Reformulated.B.ExistsIntegerSmulMemOfSpanEqTop.exists_smul_mem hsp x

/- English proof (translation)
Take `⟨s, hs⟩` from `hL`. Use `choose f hf0 hf using exists_smul_mem hsp`. Use `⟨∏ g ∈ s, f g, Finset.prod_ne_zero_iff.2 fun g _ => hf0 g, ?_⟩` and prove the remaining obligations. Introduce `u hu`. Rewrite `hu` using `[← hs]`.

Proceed by induction on `hu using Submodule.span_induction with`. Consider the case `mem g hg`. Rewrite using `[← Finset.prod_erase_mul s f hg]`. Conclude with `mul_smul_mem (hf g)`. Consider the case `zero => simp`.

Consider the case `add x y _ _ hx hy => rw [smul_add]`. Conclude with `L₁.add_mem hx hy`. Consider the case `smul c x _ hx`. Rewrite using `[osmul c x, smul_comm, ← osmul]`. Conclude with `L₁.smul_mem c hx`.
-/
theorem exists_n_one {N : ℕ} {L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} (hL : L.FG)
    (hsp : Submodule.span D.host.E (L₁ : Set (Fin N → D.host.E)) = ⊤) :
    ∃ n : 𝓞 D.host.E, n ≠ 0 ∧ ∀ u ∈ L, (n : D.host.E) • u ∈ L₁ := by
  obtain ⟨s, hs⟩ := hL
  choose f hf0 hf using exists_smul_mem hsp
  refine ⟨∏ g ∈ s, f g, Finset.prod_ne_zero_iff.2 fun g _ => hf0 g, ?_⟩
  intro u hu
  rw [← hs] at hu
  induction hu using Submodule.span_induction with
  | mem g hg =>
    rw [← Finset.prod_erase_mul s f hg]
    exact mul_smul_mem (hf g)
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact L₁.add_mem hx hy
  | smul c x _ hx =>
    rw [osmul c x, smul_comm, ← osmul]
    exact L₁.smul_mem c hx

/- English proof (translation)
Take `⟨hfg, hsp, -⟩` from `hL`. Take `⟨hfg1, hsp1, -⟩` from `hL1`. Take `⟨a, ha, h1⟩` from `exists_n_one hfg hsp1`. Take `⟨b, hb, h2⟩` from `exists_n_one hfg1 hsp`. Use `⟨b * a, mul_ne_zero hb ha, fun u hu => mul_smul_mem (h1 u hu), fun u hu => ?_⟩` and prove the remaining obligations.

Rewrite using `[mul_comm]`. Conclude with `mul_smul_mem (h2 u hu)`.
-/
theorem exists_n {N : ℕ} {L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} (hL : SD D L) (hL1 : SD D L₁) :
    ∃ n : 𝓞 D.host.E, n ≠ 0 ∧ (∀ u ∈ L, (n : D.host.E) • u ∈ L₁) ∧ ∀ u ∈ L₁, (n : D.host.E) • u ∈ L := by
  obtain ⟨hfg, hsp, -⟩ := hL
  obtain ⟨hfg1, hsp1, -⟩ := hL1
  obtain ⟨a, ha, h1⟩ := exists_n_one hfg hsp1
  obtain ⟨b, hb, h2⟩ := exists_n_one hfg1 hsp
  refine ⟨b * a, mul_ne_zero hb ha, fun u hu => mul_smul_mem (h1 u hu), fun u hu => ?_⟩
  rw [mul_comm]
  exact mul_smul_mem (h2 u hu)

end Formalism.L2.PairingIndexBounds.Eq.SquareSplitPairs
